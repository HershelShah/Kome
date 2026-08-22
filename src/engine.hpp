/* engine.hpp — internal state model shared by the core (M1) and, later, the
 * persistence layer (M2). Not part of the public ABI. */
#ifndef SYNC_ENGINE_INTERNAL_HPP
#define SYNC_ENGINE_INTERNAL_HPP

#include <array>
#include <cstdint>
#include <map>
#include <memory>
#include <string>

#include "crypto.h"
#include "sync_engine.h"

namespace ke {

using SiteId = std::array<uint8_t, SYNC_SITE_ID_LEN>;
using PubKey = std::array<uint8_t, SYNC_PUBKEY_LEN>;
using Sig    = std::array<uint8_t, SYNC_SIG_LEN>;

/* A 32-byte SHA-256 value: reconciliation-element hashes, combinable
 * fingerprint sums (reconcile.cpp), and the cached per-cell hashes below. */
using Hash256 = std::array<uint8_t, 32>;

/* A public key rendered as raw bytes, for use as a std::map/std::set key. */
inline std::string key_bytes(const PubKey &pk) {
    return std::string(reinterpret_cast<const char *>(pk.data()), pk.size());
}

/* Hybrid Logical Clock. */
struct Hlc {
    uint64_t physical = 0;
    uint32_t logical = 0;

    /* Advance for a local event using wall-clock now_ms; returns the new value. */
    Hlc tick(uint64_t now_ms);
    /* Merge a remote timestamp on receive; keeps the clock monotonic. */
    void receive(const Hlc &remote, uint64_t now_ms);
};

/* Total order on HLC: physical, then logical. <0 / 0 / >0. */
int hlc_cmp(const Hlc &a, const Hlc &b);

/* An LWW register: a field's value plus the timestamp/author that wrote it,
 * and the author's signature over the canonical record. */
struct Register {
    std::string value;
    Hlc         hlc;
    PubKey      author{};
    Sig         sig{};
    /* Cached reconciliation-element hash: SHA-256 of this cell's canonical
     * record bytes (encode_record = encode_signing bytes + raw signature).
     * Invariant — scoped to cells stored in sync_engine::ns only: every point
     * that installs or replaces such a cell computes the hash (hoisted above
     * the first committed byte, so a throw leaves no stale-hashed cell) and
     * stores it with the cell, so build_snapshot copies it instead of
     * re-hashing. Registers that never enter sync_engine::ns (e.g. the
     * throwaway Register Storage::put_field builds only to feed build_field)
     * are out of scope and may leave this zero. RAM-only: never serialized,
     * recomputed at load. */
    Hash256     elem_hash{};
};

/* Total order on registers: (hlc, author, value). Larger wins on merge. */
int register_cmp(const Register &a, const Register &b);

/* An entity: an LWW presence register (present/absent decided by the latest
 * (hlc, author) assertion), the author/signature of that assertion, and the
 * entity's field registers. Replacing the old causal-length counter removes the
 * saturation attack (a peer could pin presence with causal_length = UINT64_MAX)
 * and unifies the whole data model under one LWW-by-HLC rule. */
struct Entity {
    bool                              present_v = false; /* LWW presence value */
    Hlc                               presence_hlc;      /* {0,0} == no assertion */
    PubKey                            ex_author{};
    Sig                               ex_sig{};
    /* Cached hash of the existence element — same contract as
     * Register::elem_hash (see above): maintained at every mutation point for
     * entities stored in sync_engine::ns; meaningful only while asserted()
     * (an unasserted shell emits no element). */
    Hash256                           ex_hash{};
    std::map<std::string, Register>   fields;

    bool present() const { return present_v; }
    /* True once a presence assertion (add or delete) exists; an entity that only
     * holds fields (a register arrived before any existence record) has none. */
    bool asserted() const {
        return presence_hlc.physical != 0 || presence_hlc.logical != 0;
    }
};

using Entities   = std::map<std::string, Entity>;
using Namespaces = std::map<std::string, Entities>;

/* Current wall-clock time in milliseconds since the Unix epoch. */
uint64_t now_ms();

/* Apply one change. The public sync_engine_apply is a thin wrapper with
 * already_verified=false; reconcile's parallel batch verifier calls it with
 * already_verified=true after checking the signature out of band (the cheap
 * "would this change state?" gate still runs either way), passing the element
 * hash it computed alongside that check so the bulk path never re-encodes the
 * record. */
int apply_change(sync_engine *e, const sync_change *c, bool already_verified,
                 const Hash256 *elem_hash = nullptr);

/* The engine's two cache-invalidation counters taken together (see the fields
 * on sync_engine below). Comparable so a cache stamped with a pair can ask
 * "did either counter advance?" with one inequality. */
struct GenPair {
    uint64_t content = 0;
    uint64_t scope = 0;
    friend bool operator==(const GenPair &a, const GenPair &b) {
        return a.content == b.content && a.scope == b.scope;
    }
    friend bool operator!=(const GenPair &a, const GenPair &b) {
        return !(a == b);
    }
};

class Storage;          /* defined in storage.h (M2) */
class CapStore;         /* defined in capability.h (M4) */
struct ReconSnapshot;   /* defined in reconcile.cpp (M3): cached sync snapshot */
struct ReconView;       /* defined in reconcile.cpp (M3): read-scoped range view
                         * over a ReconSnapshot (see scoped_view_cache below) */

} // namespace ke

/* The opaque engine handle from the public header. */
struct sync_engine {
    ke::KeyPair      identity;        /* signing + agreement keypair */
    ke::SiteId       site_id{};       /* BLAKE2b-256(identity.sign_pk) */
    ke::Hlc          clock;
    ke::Namespaces   ns;
    ke::Storage     *store = nullptr; /* null for in-memory engines */
    ke::CapStore    *caps = nullptr;  /* granted capabilities (M4) */
    uint64_t         db_clock = 0;    /* monotonic per-mutation counter */
    sync_log_fn      log_fn = nullptr;
    void            *log_ctx = nullptr;

    /* Cache-invalidation counters (M3 perf). Two independent monotonic gens
     * classify every invalidation — bump exactly one per mutation:
     *   content_gen — the element set changed (a write, delete, accepted
     *                 apply, or tombstone GC): the unscoped snapshot is stale.
     *   scope_gen   — who may read/write changed (a capability grant, revoke,
     *                 or wire ingest): the element set is untouched, so the
     *                 unscoped snapshot stays valid, but every per-peer scoped
     *                 snapshot is suspect.
     * Ordering rule: compute anything that can throw (sign/encode/hash) into
     * locals BEFORE committing state, then commit and bump as non-throwing
     * steps. Phase 2 hoists every sign/element-hash computation accordingly:
     * on the set/delete/apply paths a bad_alloc now leaves the element set —
     * and every cached element hash — untouched (at worst an empty,
     * unasserted entity shell is inserted, which emits no element), and the
     * gen bump immediately follows the commit with nothing throwing between.
     * New code must preserve this: a throw between the first committed byte
     * and the bump would let recon_cache serve a stale snapshot, and a
     * committed cell without its hash would be a permanent, silent
     * fingerprint divergence (Release never re-hashes from bytes). */
    uint64_t         content_gen = 0;
    uint64_t         scope_gen = 0;
    ke::GenPair      gens() const { return {content_gen, scope_gen}; }

    /* Reconciliation snapshot cache: the sorted, hashed element set a session
     * reconciles over — a pure function of ns, so it is keyed on content_gen
     * alone and rebuilt lazily on the next session_begin when that gen is
     * stale. Shared via shared_ptr so an in-flight session keeps the snapshot
     * it began with even as later writes replace the engine's cached one. */
    std::shared_ptr<const ke::ReconSnapshot>  recon_cache;

    /* Per-peer read-scoped snapshot cache (steady-state perf). A scoped session
     * filters the snapshot to what one peer may read, so unlike recon_cache it
     * cannot be shared across peers — but for a converged, idle gossip link it
     * was being rebuilt (encode + hash every record) every cycle. Cache one
     * snapshot per peer, keyed by raw pubkey bytes, valid at scoped_cache_gens;
     * cleared wholesale when either gen advances (a write, apply, or capability
     * change). Initialized to {UINT64_MAX, UINT64_MAX} — never a live gens()
     * value — so the first ensure_scoped_source call clears unconditionally.
     * Holds only peers whose scope is time-INdependent: a fully-open peer (an
     * alias to the shared unscoped snapshot) or a permanently-restricted one (a
     * distinct filtered snapshot). A peer whose scope can change with the clock
     * alone is served from scoped_view_cache below instead, because a GenPair is
     * not enough to invalidate it. */
    ke::GenPair                               scoped_cache_gens{UINT64_MAX,
                                                                UINT64_MAX};
    std::map<std::string,
             std::shared_ptr<const ke::ReconSnapshot>> scoped_cache;

    /* Per-peer read-scoped RANGE VIEWS, for peers whose visible set depends on a
     * capability expiry (§3.5). Such a peer used to be excluded from caching
     * altogether, so every gossip cycle — idle ones included — re-encoded and
     * re-hashed its whole visible set. A ReconView instead holds base-index
     * ranges into the shared unscoped snapshot plus prefix sums over them, so it
     * is built in O(namespaces log N) and serves the identical wire bytes.
     *
     * Two independent invalidations apply, and both are required:
     *   - scoped_cache_gens, exactly as for scoped_cache above: this map is
     *     cleared in the same guarded block whenever either gen advances.
     *   - ReconView::valid_until_ms, the wall-clock deadline the view's scope
     *     decision holds until (inclusive). Capability expiry moves no counter,
     *     so a deadline-passed entry is erased and rebuilt on the spot, with no
     *     dependence on a content_gen or scope_gen bump. */
    std::map<std::string,
             std::shared_ptr<const ke::ReconView>>     scoped_view_cache;
};

#endif /* SYNC_ENGINE_INTERNAL_HPP */
