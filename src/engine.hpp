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
 * "would this change state?" gate still runs either way). */
int apply_change(sync_engine *e, const sync_change *c, bool already_verified);

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
     * Ordering caveat (pre-existing, not introduced by the split): the local
     * mutation paths in sync_engine.cpp allocate (sign/encode) between the
     * first committed byte and the content_gen++ — a bad_alloc in that window
     * leaves state mutated with no bump, so recon_cache can serve a stale
     * snapshot until the next accepted mutation. New code must not widen that
     * window: compute anything that can throw before committing state, then
     * bump (Phase 2 hoists its element hashing accordingly). */
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
     * value — so the first ensure_scoped_cache call clears unconditionally.
     * Snapshots whose scope is time-bound (a finite-expiry cap) are not
     * cached — see reconcile.cpp ensure_scoped_cache. */
    ke::GenPair                               scoped_cache_gens{UINT64_MAX,
                                                                UINT64_MAX};
    std::map<std::string,
             std::shared_ptr<const ke::ReconSnapshot>> scoped_cache;
};

#endif /* SYNC_ENGINE_INTERNAL_HPP */
