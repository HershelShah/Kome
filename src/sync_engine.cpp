/* sync_engine.cpp — convergent core (M1).
 *
 * Implements the public C ABI in include/sync_engine.h: HLC, LWW registers,
 * causal-length sets, local ops, the export/apply full-state baseline, and a
 * deterministic digest. Every extern "C" function wraps its body in
 * try/catch so no C++ exception crosses the boundary. */
#include "sync_engine.h"

#include <chrono>
#include <cstdlib>
#include <cstring>
#include <new>
#include <string>
#include <type_traits>
#include <utility>

#include "byteorder.h"
#include "capability.h"
#include "codec.h"
#include "crypto.h"
#include "engine.hpp"
#include "sha256.h"
#include "storage.h"

namespace ke {

/* std::chrono::milliseconds::rep is a SIGNED integer, so a host whose wall
 * clock reads before 1970 yields a negative count -- and a bare (uint64_t) cast
 * is a modular wrap, not a clamp: 1900-01-01 comes back as 18446741864720751616
 * and one millisecond before the epoch as UINT64_MAX exactly.
 *
 * Every consumer reads this as a BOUNDED wall-clock millisecond count:
 * Hlc::tick's `now > physical` monotonicity gate, Storage::gc_tombstones'
 * `cutoff = now - kTombstoneTtlMs`, capability expiry, and ReconView deadlines.
 * The tick gate is one-way, so a single local write on such a host pins the
 * engine-global clock ~584 million years ahead for the life of the process AND
 * of the database (the value is persisted by stamp_clock_meta and restored),
 * lands the clock in the exhausted-state neighbourhood kMaxAdoptablePhysical
 * exists to keep out of reach, purges every tombstone at the next compaction,
 * and expires every finite capability.
 *
 * Reachable without an attacker: the WASM/browser build follows the host's
 * user-settable date, Windows' SetSystemTime accepts years back to 1601, and a
 * bare-metal RTC with a dead backup cell powers on at 1900. (Linux rejects a
 * negative settimeofday, so there the host lands at 0 instead -- the already
 * documented "stuck at the epoch" case.)
 *
 * Clamping to 0 is safe against the {0,0} reservation: with now == 0, tick
 * takes the else branch into bump_logical, which yields logical >= 1. That is
 * exactly the case ZeroHlcExistence.ClockNeverMintsTheSentinel pins. */
uint64_t ms_since_epoch(int64_t count) {
    return count < 0 ? 0 : (uint64_t)count;
}

uint64_t now_ms() {
    using namespace std::chrono;
    return ms_since_epoch((int64_t)duration_cast<milliseconds>(
                              system_clock::now().time_since_epoch())
                              .count());
}

/* logical = base + 1, carrying a uint32 overflow into `phys`.
 *
 * `logical` is uint32_t and every increment site is a bare +1, so a clock at
 * {p, UINT32_MAX} wraps to {p, 0} -- and at p == 0 (a host whose now_ms() is
 * stuck at the epoch: no RTC) that is exactly {0,0}, the reserved "no
 * assertion" sentinel (Entity::asserted(), engine.hpp). Carrying into physical
 * keeps the result strictly greater than the pre-bump value ({p,MAX} <
 * {p+1,0} under hlc_cmp).
 *
 * The carry MUST be decided from the pre-increment counter, not from
 * "logical == 0" afterwards: receive's fourth branch sets logical = 0
 * deliberately (the wall clock advanced past both sides), and a carry there
 * would push physical past `now` on every ordinary apply.
 *
 * `phys` is remote-influenced -- receive adopts a peer's physical with no
 * clamp on future timestamps -- so the increment needs its own overflow guard.
 * On the one degenerate input where no larger HLC exists at all
 * (phys == UINT64_MAX and base == UINT32_MAX) the clock SATURATES rather than
 * wrapping: a repeated timestamp costs only progress (LWW then ties on author
 * and the later write is dropped), whereas wrapping would land on the sentinel
 * and mint a phantom. */
void Hlc::bump_logical(uint64_t &phys, uint32_t base) {
    if (base != UINT32_MAX) { logical = base + 1; return; }
    if (phys != UINT64_MAX) { phys += 1; logical = 0; return; }
    logical = UINT32_MAX; /* clock exhausted: saturate, never wrap to {0,0} */
}

Hlc Hlc::tick(uint64_t now) {
    if (now > physical) {
        physical = now;
        logical = 0;
    } else {
        bump_logical(physical, logical);
    }
    return *this;
}

/* Merge a remote timestamp, keeping the clock monotonic.
 *
 * The remote physical is ADOPTED only up to kMaxAdoptablePhysical (engine.hpp).
 * Without that ceiling one signed record at the top of the uint64 range drives
 * this clock onto bump_logical's saturating FIXED POINT, after which tick()
 * stops being strictly monotonic and every local write -- to any entity, in any
 * namespace -- lands locally but is dropped by every peer as a tie. The clamp
 * bounds what we adopt, never what we accept: apply_change still compares the
 * record's own (hlc, author), so the merge stays deterministic. A record above
 * the ceiling still wins its own cell; we just do not let it pin the engine. */
void Hlc::receive(const Hlc &remote, uint64_t now) {
    uint64_t old_p = physical;
    uint64_t new_p = old_p;
    if (remote.physical > new_p && remote.physical <= kMaxAdoptablePhysical)
        new_p = remote.physical;
    if (now > new_p) new_p = now;

    if (new_p == old_p && new_p == remote.physical) {
        bump_logical(new_p, logical > remote.logical ? logical : remote.logical);
    } else if (new_p == old_p) {
        bump_logical(new_p, logical);
    } else if (new_p == remote.physical) {
        bump_logical(new_p, remote.logical);
    } else {
        logical = 0; /* wall clock advanced past both: a real reset, not a wrap */
    }
    physical = new_p;
}

int hlc_cmp(const Hlc &a, const Hlc &b) {
    if (a.physical != b.physical) return a.physical < b.physical ? -1 : 1;
    if (a.logical != b.logical) return a.logical < b.logical ? -1 : 1;
    return 0;
}

int register_cmp(const Register &a, const Register &b) {
    if (int c = hlc_cmp(a.hlc, b.hlc)) return c;
    if (int c = std::memcmp(a.author.data(), b.author.data(), SYNC_PUBKEY_LEN))
        return c < 0 ? -1 : 1;
    if (a.value != b.value) return a.value < b.value ? -1 : 1;
    return 0;
}

} // namespace ke

using namespace ke;
using sync_engine_detail::Sha256;

namespace {

std::string to_str(const uint8_t *p, size_t len) {
    if (len == 0) return std::string();
    return std::string(reinterpret_cast<const char *>(p), len);
}

/* The implied author of an absent entity (causal_length 0): all zeros. Used to
 * order an incoming existence record against a not-yet-seen entity. */
const uint8_t kZeroAuthor[SYNC_PUBKEY_LEN] = {0};

/* Fill c->author and c->signature by signing c's canonical content with e.
 * The canonical signing bytes are appended to `signing` and left for the
 * caller, which feeds them to the streaming element_hash overload — the
 * cached element hash costs no re-encode and no extra allocation. */
void author_sign(sync_engine *e, sync_change &c, std::string &signing) {
    std::memcpy(c.author, e->identity.sign_pk.data(), SYNC_PUBKEY_LEN);
    ke::encode_signing(c, signing);
    ke::sign(e->identity.sign_sk.data(), signing.data(), signing.size(),
             c.signature);
}

/* Verify a record's signature against its declared author. The canonical
 * signing bytes are left in `signing` for the caller (streaming element_hash
 * — same reuse as author_sign above). */
bool verify_change(const sync_change *c, std::string &signing) {
    ke::encode_signing(*c, signing);
    return ke::verify(c->author, signing.data(), signing.size(), c->signature);
}

/* A fully built (signed + hashed) presence assertion, held in locals until
 * commit_existence lands it on the map-resident entity. */
struct ExistenceAssertion {
    bool    present = false;
    Hlc     hlc;
    PubKey  author{};
    Sig     sig{};
    Hash256 hash{};
};

/* Build, sign, and hash a presence assertion (present bit + hlc) for (ns, ent)
 * entirely into locals. Every throw point of the presence path lives here —
 * author_sign's signing-buffer allocation (the streaming element_hash is
 * stack-only) — strictly before the first committed byte, per the hoisting
 * rule (§3.2 point 1 / engine.hpp): a std::bad_alloc leaves the entity, and
 * with it the engine's advertised element set, completely untouched. Shared
 * by the add path (set) and the remove path (delete). */
ExistenceAssertion build_existence(sync_engine *e, const std::string &ns,
                                   const std::string &ent, bool present,
                                   const Hlc &hlc) {
    sync_change ec;
    std::memset(&ec, 0, sizeof ec);
    ec.kind = SYNC_CHANGE_EXISTENCE;
    ec.ns = (const uint8_t *)ns.data(); ec.ns_len = ns.size();
    ec.entity = (const uint8_t *)ent.data(); ec.entity_len = ent.size();
    ec.causal_length = present ? 1 : 0; /* present bit */
    ec.hlc.physical = hlc.physical;
    ec.hlc.logical = hlc.logical;
    std::string signing;
    author_sign(e, ec, signing);
    ExistenceAssertion a;
    a.present = present;
    a.hlc = hlc;
    std::memcpy(a.author.data(), ec.author, SYNC_PUBKEY_LEN);
    std::memcpy(a.sig.data(), ec.signature, SYNC_SIG_LEN);
    ke::element_hash(signing, ec.signature, a.hash);
    return a;
}

/* Commit a built assertion into the map-resident entity: present_v,
 * presence_hlc, ex_author, ex_sig, and ex_hash land together as one
 * non-throwing step (POD and std::array assignments only), so the entity can
 * never be observed holding a new presence with the previous assertion's
 * signature or cached hash. */
void commit_existence(Entity &en, const ExistenceAssertion &a) noexcept {
    en.present_v = a.present;
    en.presence_hlc = a.hlc;
    en.ex_author = a.author;
    en.ex_sig = a.sig;
    en.ex_hash = a.hash;
}

/* The register install below relies on move-assignment being a buffer steal,
 * never an allocating copy, so a committed cell can't be left mid-update. */
static_assert(std::is_nothrow_move_assignable<Register>::value &&
                  std::is_nothrow_move_constructible<Register>::value,
              "Register moves must not throw: install-after-hash depends on it");

/* Emit a diagnostic log line (no record values/keys/namespaces/secrets). */
void engine_log(sync_engine *e, int level, const char *msg) {
    if (e->log_fn) e->log_fn(e->log_ctx, level, msg);
}

/* Hash one length-prefixed byte field (LE 64-bit length) into h. */
void feed(Sha256 &h, const void *p, size_t len) {
    uint8_t lb[8];
    store_u64le(lb, (uint64_t)len);
    h.update(lb, 8);
    if (len) h.update(p, len);
}

void feed_u64(Sha256 &h, uint64_t v) {
    uint8_t b[8];
    store_u64le(b, v);
    h.update(b, 8);
}

void feed_u32(Sha256 &h, uint32_t v) {
    uint8_t b[4];
    store_u32le(b, v);
    h.update(b, 4);
}

/* ---- write-through helpers (no-ops for in-memory engines) --------------- */

bool persist_meta_clock(sync_engine *e) {
    return e->store->put_meta_u64("hlc_physical", e->clock.physical) &&
           e->store->put_meta_u64("hlc_logical", e->clock.logical) &&
           e->store->put_meta_u64("db_clock", e->db_clock);
}

/* Persist an entity row (and clock) in one transaction. During a bulk-apply
 * batch the record is only staged — the batch owns the transaction, clock, and
 * compaction (O(1) fsyncs for the whole batch) — followed by the MANDATORY
 * bounded-staging flush hook. Any in-batch failure (a false return OR a
 * throw) poisons the whole engine-global batch (spec §3.3 point 9): a
 * poisoned batch fails every subsequent tx_* immediately and its outermost
 * commit discards the un-flushed tail instead of committing it. */
bool tx_entity(sync_engine *e, const std::string &ns, const std::string &ent,
               const Entity &en) {
    Storage *s = e->store;
    if (s->in_batch()) {
        bool ok = false;
        try {
            ok = s->put_entity(ns, ent, en.present_v, en.presence_hlc,
                               en.ex_author, en.ex_sig, e->db_clock) &&
                 s->batch_maybe_flush(e);
        } catch (...) {
            s->batch_poison();
            throw;
        }
        if (!ok) s->batch_poison();
        return ok;
    }
    if (!s->begin()) return false;
    bool ok = s->put_entity(ns, ent, en.present_v, en.presence_hlc,
                            en.ex_author, en.ex_sig, e->db_clock) &&
              persist_meta_clock(e);
    if (!ok) { s->rollback(); return false; }
    if (!s->commit()) return false;
    s->maybe_compact(e); /* bound log growth (best-effort) */
    return true;
}

/* Persist an entity row + one field register (and clock) in one transaction.
 * In-batch semantics identical to tx_entity above: stage, then the mandatory
 * flush hook; any failure — including a put_* short-circuit — poisons the
 * batch (spec §3.3 point 9). */
bool tx_entity_field(sync_engine *e, const std::string &ns,
                     const std::string &ent, const std::string &field,
                     const Entity &en, const Register &reg) {
    Storage *s = e->store;
    if (s->in_batch()) {
        bool ok = false;
        try {
            ok = s->put_entity(ns, ent, en.present_v, en.presence_hlc,
                               en.ex_author, en.ex_sig, e->db_clock) &&
                 s->put_field(ns, ent, field, reg.value, reg.hlc, reg.author,
                              reg.sig, e->db_clock) &&
                 s->batch_maybe_flush(e);
        } catch (...) {
            s->batch_poison();
            throw;
        }
        if (!ok) s->batch_poison();
        return ok;
    }
    if (!s->begin()) return false;
    bool ok = s->put_entity(ns, ent, en.present_v, en.presence_hlc,
                            en.ex_author, en.ex_sig, e->db_clock) &&
              s->put_field(ns, ent, field, reg.value, reg.hlc, reg.author,
                           reg.sig, e->db_clock) &&
              persist_meta_clock(e);
    if (!ok) { s->rollback(); return false; }
    if (!s->commit()) return false;
    s->maybe_compact(e); /* bound log growth (best-effort) */
    return true;
}

} // namespace

extern "C" {

uint32_t sync_abi_version(void) { return SYNC_ABI_VERSION; }

int sync_engine_set_logger(sync_engine *e, sync_log_fn fn, void *ctx) {
    if (!e) return SYNC_ERR_INVALID;
    e->log_fn = fn;
    e->log_ctx = ctx;
    return SYNC_OK;
}

const char *sync_strerror(int err) {
    switch (err) {
        case SYNC_OK:           return "ok";
        case SYNC_ERR_INVALID:  return "invalid argument";
        case SYNC_ERR_NOMEM:    return "out of memory";
        case SYNC_ERR_NOTFOUND: return "not found";
        case SYNC_ERR_INTERNAL: return "internal error";
        case SYNC_ERR_BADSIG:   return "signature verification failed";
        case SYNC_ERR_UNAUTHORIZED: return "not authorized";
        case SYNC_ERR_CORRUPT:  return "blob content does not match its hash";
        default:                return "unknown error";
    }
}

void sync_free(void *p) { std::free(p); }

sync_engine *sync_engine_create(const uint8_t seed[SYNC_SEED_LEN]) {
    if (!seed) return nullptr;
    try {
        sync_engine *e = new sync_engine();
        e->identity = keypair_from_seed(seed);
        site_id_from_pubkey(e->identity.sign_pk.data(), e->site_id.data());
        return e;
    } catch (...) {
        return nullptr;
    }
}

static sync_engine *open_impl(const char *path, const uint8_t *seed,
                              const uint8_t *key) {
    if (!path || !seed) return nullptr;
    try {
        sync_error err = SYNC_OK;
        Storage *store = Storage::open(path, &err, key);
        if (!store) return nullptr;

        sync_engine *e = new (std::nothrow) sync_engine();
        if (!e) {
            delete store;
            return nullptr;
        }
        if (!store->load(e, seed, &err)) {
            delete e; /* e does not own store yet */
            delete store;
            return nullptr;
        }
        e->store = store;
        return e;
    } catch (...) {
        return nullptr;
    }
}

sync_engine *sync_engine_open(const char *path,
                              const uint8_t seed[SYNC_SEED_LEN]) {
    return open_impl(path, seed, nullptr);
}

sync_engine *sync_engine_open_encrypted(const char *path,
                                        const uint8_t seed[SYNC_SEED_LEN],
                                        const uint8_t key[32]) {
    if (!key) return nullptr;
    return open_impl(path, seed, key);
}

int sync_engine_flush(sync_engine *e) {
    if (!e) return SYNC_ERR_INVALID;
    try {
        /* Write-through keeps disk current outside a batch, so with no batch
         * open there is nothing to force. With an open batch
         * (sync_engine_batch_begin) flush is precisely the "make everything
         * durable now" call an embedder issues before backgrounding, so it
         * COMMITS the batch — every nesting level, engine-global — rather
         * than silently violating its documented no-op-safety-net contract
         * (spec §3.3 point 3). */
        if (e->store && e->store->in_batch()) {
            bool ok = true;
            while (e->store->in_batch())
                if (!e->store->batch_commit(e)) ok = false;
            if (!ok) return SYNC_ERR_INTERNAL;
        }
        return SYNC_OK;
    } catch (const std::bad_alloc &) {
        return SYNC_ERR_NOMEM;
    } catch (...) {
        return SYNC_ERR_INTERNAL;
    }
}

int sync_engine_compact(sync_engine *e) {
    if (!e || !e->store) return SYNC_ERR_INVALID; /* no log to rewrite */
    try {
        /* compact() refuses while a transaction is in flight — including for
         * a batch's WHOLE lifetime (a batch holds the transaction open), so
         * this returns SYNC_ERR_INTERNAL while any sync_engine_batch_begin
         * batch is open (spec §3.3 point 4). The erase-then-compact
         * physical-erasure pairing must run outside a batch. */
        return e->store->compact(e) ? SYNC_OK : SYNC_ERR_INTERNAL;
    } catch (const std::bad_alloc &) {
        return SYNC_ERR_NOMEM;
    } catch (...) {
        return SYNC_ERR_INTERNAL;
    }
}

void sync_engine_destroy(sync_engine *e) {
    if (!e) return;
    if (e->store && e->store->in_batch()) {
        /* Destroy with an open batch is a defined, non-silent path (spec
         * §3.3 point 2): ~Storage() would otherwise drop the staged tail
         * with no commit, no rollback, no diagnostic. Run the outermost
         * commit so staged mutations land durably; on failure (including a
         * poisoned batch, whose tail is discarded by contract) warn via the
         * log callback — never a silent drop. */
        try {
            bool ok = true;
            while (e->store->in_batch())
                if (!e->store->batch_commit(e)) ok = false;
            if (!ok)
                engine_log(e, SYNC_LOG_WARN,
                           "destroy: open batch failed to commit; staged "
                           "mutations were not persisted");
        } catch (...) {
            engine_log(e, SYNC_LOG_WARN,
                       "destroy: open batch failed to commit; staged "
                       "mutations were not persisted");
        }
    }
    delete e->store;
    delete e->caps;
    delete e;
}

int sync_engine_identity(sync_engine *e, uint8_t out[SYNC_PUBKEY_LEN]) {
    if (!e || !out) return SYNC_ERR_INVALID;
    std::memcpy(out, e->identity.sign_pk.data(), SYNC_PUBKEY_LEN);
    return SYNC_OK;
}

int sync_engine_site_id(sync_engine *e, uint8_t out[SYNC_SITE_ID_LEN]) {
    if (!e || !out) return SYNC_ERR_INVALID;
    std::memcpy(out, e->site_id.data(), SYNC_SITE_ID_LEN);
    return SYNC_OK;
}

int sync_engine_set(sync_engine *e,
                    const uint8_t *ns, size_t ns_len,
                    const uint8_t *entity, size_t entity_len,
                    const uint8_t *field, size_t field_len,
                    const uint8_t *value, size_t value_len) {
    if (!e || (!ns && ns_len) || (!entity && entity_len) ||
        (!field && field_len) || (!value && value_len))
        return SYNC_ERR_INVALID;
    try {
        std::string nsk = to_str(ns, ns_len);
        std::string entk = to_str(entity, entity_len);
        std::string fk = to_str(field, field_len);

        /* Probe with find() — nothing is inserted until every throwing step
         * (sign + hash of both cells) below has finished. */
        const Entity *cur = nullptr;
        {
            auto ni = e->ns.find(nsk);
            if (ni != e->ns.end()) {
                auto ei = ni->second.find(entk);
                if (ei != ni->second.end()) cur = &ei->second;
            }
        }
        const bool need_presence = !cur || !cur->present();

        /* Phase 1 — build + sign + hash both cells into locals. Every
         * allocation (and so every throw point except the map-node
         * allocations in phase 2) happens here, before any committed byte. */
        ExistenceAssertion ex;
        if (need_presence)
            /* Assert presence with a fresh LWW timestamp (strictly newer than
             * any prior assertion this engine has seen, so it wins). */
            ex = build_existence(e, nsk, entk, /*present=*/true,
                                 e->clock.tick(now_ms()));

        Register reg;
        reg.value = to_str(value, value_len);
        reg.hlc = e->clock.tick(now_ms());
        {
            sync_change rc;
            std::memset(&rc, 0, sizeof rc);
            rc.kind = SYNC_CHANGE_REGISTER;
            rc.ns = (const uint8_t *)nsk.data(); rc.ns_len = nsk.size();
            rc.entity = (const uint8_t *)entk.data(); rc.entity_len = entk.size();
            rc.field = (const uint8_t *)fk.data(); rc.field_len = fk.size();
            rc.value = (const uint8_t *)reg.value.data();
            rc.value_len = reg.value.size();
            rc.hlc.physical = reg.hlc.physical;
            rc.hlc.logical = reg.hlc.logical;
            std::string signing;
            author_sign(e, rc, signing);
            std::memcpy(reg.author.data(), rc.author, SYNC_PUBKEY_LEN);
            std::memcpy(reg.sig.data(), rc.signature, SYNC_SIG_LEN);
            /* Cache the element hash on the still-local register (streaming,
             * reusing the signing buffer) before it is installed below. */
            ke::element_hash(signing, rc.signature, reg.elem_hash);
        }

        /* Phase 2 — commit. The map lookups can still throw, but only while
         * allocating a node, before anything is linked in (strong guarantee);
         * the worst partial effect is an empty, unasserted entity shell,
         * which emits no element and carries no hash. Past try_emplace,
         * everything is non-throwing (a string buffer steal, array copies,
         * counter bumps — see the static_assert above), so a bad_alloc can
         * never leave a committed cell whose cached hash is not its own. */
        Entity &ent = e->ns[nsk][entk];
        /* A fresh local tick dominates any prior state for this cell. */
        auto ins = ent.fields.try_emplace(fk, std::move(reg));
        if (!ins.second) ins.first->second = std::move(reg);
        if (need_presence) commit_existence(ent, ex);
        e->content_gen++; /* invalidate the reconciliation snapshot cache */

        if (e->store) {
            e->db_clock++;
            if (!tx_entity_field(e, nsk, entk, fk, ent, ins.first->second))
                return SYNC_ERR_INTERNAL;
        }
        return SYNC_OK;
    } catch (const std::bad_alloc &) {
        return SYNC_ERR_NOMEM;
    } catch (...) {
        return SYNC_ERR_INTERNAL;
    }
}

int sync_engine_delete(sync_engine *e,
                       const uint8_t *ns, size_t ns_len,
                       const uint8_t *entity, size_t entity_len) {
    if (!e || (!ns && ns_len) || (!entity && entity_len))
        return SYNC_ERR_INVALID;
    try {
        std::string nsk = to_str(ns, ns_len);
        std::string entk = to_str(entity, entity_len);
        auto ni = e->ns.find(nsk);
        if (ni == e->ns.end()) return SYNC_OK;
        auto ei = ni->second.find(entk);
        if (ei == ni->second.end()) return SYNC_OK;
        if (ei->second.present()) {
            Entity &ent = ei->second;
            /* Assert absence with a fresh LWW timestamp (a tombstone). Built,
             * signed, and hashed into locals first; commit_existence then
             * lands the tombstone as one non-throwing step, so a bad_alloc
             * leaves the entity still present with its previous,
             * self-consistent assertion — never a tombstone carrying the old
             * assertion's cached hash. */
            ExistenceAssertion ex = build_existence(
                e, nsk, entk, /*present=*/false, e->clock.tick(now_ms()));
            commit_existence(ent, ex);
            e->content_gen++; /* invalidate the reconciliation snapshot cache */
            if (e->store) {
                e->db_clock++;
                if (!tx_entity(e, nsk, entk, ent))
                    return SYNC_ERR_INTERNAL;
            }
        }
        return SYNC_OK;
    } catch (const std::bad_alloc &) {
        return SYNC_ERR_NOMEM;
    } catch (...) {
        return SYNC_ERR_INTERNAL;
    }
}

sync_error sync_engine_erase_field(sync_engine *e,
                                   const uint8_t *ns, size_t ns_len,
                                   const uint8_t *entity, size_t entity_len,
                                   const uint8_t *field, size_t field_len) {
    if (!e || (!ns && ns_len) || (!entity && entity_len) ||
        (!field && field_len))
        return SYNC_ERR_INVALID;
    try {
        /* Refuse to write through a tombstone: set() re-asserts presence, so
         * erasing a deleted entity would resurrect it. Likewise refuse a
         * field that does not exist — an erase must never create state. */
        auto ni = e->ns.find(to_str(ns, ns_len));
        if (ni == e->ns.end()) return SYNC_ERR_NOTFOUND;
        auto ei = ni->second.find(to_str(entity, entity_len));
        if (ei == ni->second.end() || !ei->second.present())
            return SYNC_ERR_NOTFOUND;
        if (ei->second.fields.find(to_str(field, field_len)) ==
            ei->second.fields.end())
            return SYNC_ERR_NOTFOUND;
        return (sync_error)sync_engine_set(e, ns, ns_len, entity, entity_len,
                                           field, field_len, nullptr, 0);
    } catch (const std::bad_alloc &) {
        return SYNC_ERR_NOMEM;
    } catch (...) {
        return SYNC_ERR_INTERNAL;
    }
}

/* ---- Write batching (additive ABI; contracts in include/sync_engine.h) ---
 * Thin wrappers over Storage's nesting-safe batch machinery. In-memory
 * engines (no store) have no log to batch, so all three are clean no-ops
 * returning SYNC_OK; on a store-backed engine an unbalanced commit/abort
 * (no batch open) is SYNC_ERR_INVALID. */

int sync_engine_batch_begin(sync_engine *e) {
    if (!e) return SYNC_ERR_INVALID;
    if (!e->store) return SYNC_OK; /* in-memory: no-op */
    try {
        return e->store->batch_begin() ? SYNC_OK : SYNC_ERR_INTERNAL;
    } catch (const std::bad_alloc &) {
        return SYNC_ERR_NOMEM;
    } catch (...) {
        return SYNC_ERR_INTERNAL;
    }
}

int sync_engine_batch_commit(sync_engine *e) {
    if (!e) return SYNC_ERR_INVALID;
    if (!e->store) return SYNC_OK; /* in-memory: no-op */
    try {
        if (!e->store->in_batch()) return SYNC_ERR_INVALID; /* unbalanced */
        /* false = poisoned batch (outermost: staged tail discarded) or a
         * write failure at the outermost commit. */
        return e->store->batch_commit(e) ? SYNC_OK : SYNC_ERR_INTERNAL;
    } catch (const std::bad_alloc &) {
        return SYNC_ERR_NOMEM;
    } catch (...) {
        return SYNC_ERR_INTERNAL;
    }
}

int sync_engine_batch_abort(sync_engine *e) {
    if (!e) return SYNC_ERR_INVALID;
    if (!e->store) return SYNC_OK; /* in-memory: no-op */
    try {
        if (!e->store->in_batch()) return SYNC_ERR_INVALID; /* unbalanced */
        return e->store->batch_abort() ? SYNC_OK : SYNC_ERR_INTERNAL;
    } catch (...) {
        return SYNC_ERR_INTERNAL;
    }
}

int sync_engine_get(sync_engine *e,
                    const uint8_t *ns, size_t ns_len,
                    const uint8_t *entity, size_t entity_len,
                    const uint8_t *field, size_t field_len,
                    uint8_t **out_value, size_t *out_len) {
    if (!e || !out_value || !out_len || (!ns && ns_len) ||
        (!entity && entity_len) || (!field && field_len))
        return SYNC_ERR_INVALID;
    *out_value = nullptr;
    *out_len = 0;
    try {
        auto ni = e->ns.find(to_str(ns, ns_len));
        if (ni == e->ns.end()) return SYNC_ERR_NOTFOUND;
        auto ei = ni->second.find(to_str(entity, entity_len));
        if (ei == ni->second.end() || !ei->second.present())
            return SYNC_ERR_NOTFOUND;
        auto fi = ei->second.fields.find(to_str(field, field_len));
        if (fi == ei->second.fields.end()) return SYNC_ERR_NOTFOUND;

        const std::string &v = fi->second.value;
        /* Non-NULL even when empty, so callers can distinguish from not-found. */
        uint8_t *buf = static_cast<uint8_t *>(std::malloc(v.empty() ? 1 : v.size()));
        if (!buf) return SYNC_ERR_NOMEM;
        if (!v.empty()) std::memcpy(buf, v.data(), v.size());
        *out_value = buf;
        *out_len = v.size();
        return SYNC_OK;
    } catch (const std::bad_alloc &) {
        return SYNC_ERR_NOMEM;
    } catch (...) {
        return SYNC_ERR_INTERNAL;
    }
}

int sync_engine_exists(sync_engine *e,
                       const uint8_t *ns, size_t ns_len,
                       const uint8_t *entity, size_t entity_len,
                       int *out_exists) {
    if (!e || !out_exists || (!ns && ns_len) || (!entity && entity_len))
        return SYNC_ERR_INVALID;
    *out_exists = 0;
    try {
        auto ni = e->ns.find(to_str(ns, ns_len));
        if (ni == e->ns.end()) return SYNC_OK;
        auto ei = ni->second.find(to_str(entity, entity_len));
        if (ei == ni->second.end()) return SYNC_OK;
        *out_exists = ei->second.present() ? 1 : 0;
        return SYNC_OK;
    } catch (...) {
        return SYNC_ERR_INTERNAL;
    }
}

sync_error sync_engine_scan(sync_engine *e,
                            const uint8_t *ns, size_t ns_len,
                            const uint8_t *start_after, size_t start_after_len,
                            size_t limit,
                            sync_scan_entry **out_entries, size_t *out_count) {
    if (!e || !out_entries || !out_count || (!ns && ns_len) ||
        (!start_after && start_after_len))
        return SYNC_ERR_INVALID;
    *out_entries = nullptr;
    *out_count = 0;
    try {
        auto ni = e->ns.find(to_str(ns, ns_len));
        if (ni == e->ns.end()) return SYNC_OK;
        Entities &ents = ni->second;

        /* start_after is exclusive; upper_bound lands on the first key past it
         * (a cursor that doesn't name an entity is still a valid bound). No
         * cursor means the beginning, which is not the same as upper_bound of
         * an empty string (that would skip an entity literally named ""). */
        auto begin = start_after_len == 0
                         ? ents.begin()
                         : ents.upper_bound(to_str(start_after, start_after_len));

        /* Count first (bounded by limit) so the array is allocated exactly. */
        size_t n = 0;
        for (auto it = begin; it != ents.end() && (limit == 0 || n < limit); ++it)
            if (it->second.present()) n++;
        if (n == 0) return SYNC_OK;

        sync_scan_entry *arr = static_cast<sync_scan_entry *>(
            std::calloc(n, sizeof(sync_scan_entry)));
        if (!arr) return SYNC_ERR_NOMEM;

        size_t i = 0;
        bool oom = false;
        for (auto it = begin; it != ents.end() && i < n; ++it) {
            if (!it->second.present()) continue;
            const std::string &entk = it->first;
            if (entk.empty()) {
                /* dup_field() returns NULL for an empty string, but scan's
                 * entity buffer must always be non-NULL: it is documented as
                 * an owned, heap-allocated buffer, and a NULL+0 entry is
                 * indistinguishable from "no cursor" (start-from-beginning),
                 * which would make an entity literally named "" un-passable
                 * as a start_after cursor and hang the documented pagination
                 * loop. Allocate a 1-byte buffer, as sync_engine_get does for
                 * the same reason. */
                arr[i].entity = static_cast<uint8_t *>(std::malloc(1));
                if (!arr[i].entity) { oom = true; goto fail; }
            } else {
                arr[i].entity = dup_field(entk, &oom);
                if (oom) goto fail;
            }
            arr[i].entity_len = entk.size();
            i++;
        }
        *out_entries = arr;
        *out_count = n;
        return SYNC_OK;
    fail:
        sync_scan_free(arr, i);
        return SYNC_ERR_NOMEM;
    } catch (const std::bad_alloc &) {
        return SYNC_ERR_NOMEM;
    } catch (...) {
        return SYNC_ERR_INTERNAL;
    }
}

void sync_scan_free(sync_scan_entry *entries, size_t count) {
    if (!entries) return;
    for (size_t i = 0; i < count; i++) std::free(entries[i].entity);
    std::free(entries);
}

} // extern "C"

/* Internal apply, shared by the public ABI and reconcile's parallel batch
 * verifier. already_verified=true skips only the EdDSA check (the caller
 * verified the signature out of band); the cheap LWW/existence "would this
 * change state?" gate still runs, so verify-on-win and every other invariant
 * hold regardless. elem_hash, when non-null, is the record's element hash
 * precomputed by the caller (the parallel verifier hashes from the signing
 * buffer it already built — no re-encode, no allocation, no throw here). */
int ke::apply_change(sync_engine *e, const sync_change *c,
                     bool already_verified, const Hash256 *elem_hash) {
    if (!e || !c) return SYNC_ERR_INVALID;
    if ((!c->ns && c->ns_len) || (!c->entity && c->entity_len))
        return SYNC_ERR_INVALID;
    if (c->kind != SYNC_CHANGE_EXISTENCE && c->kind != SYNC_CHANGE_REGISTER)
        return SYNC_ERR_INVALID;
    if (c->kind == SYNC_CHANGE_EXISTENCE) {
        /* {0,0} is the "no assertion" SENTINEL, not a timestamp: Entity::
         * asserted() (engine.hpp) *derives* "does this entity carry a presence
         * assertion?" from a non-zero presence_hlc rather than storing a bit.
         * So a record stamped {0,0} is malformed, and accepting one used to
         * commit present_v/ex_author/ex_sig onto a cell that asserted() still
         * reported as unasserted -- exists() said 1, digest moved,
         * build_snapshot advertised no element, and the reload dropped it
         * (storage.cpp re-derives asserted() at load).
         *
         * Refusing it cannot drop an honest peer's record: Hlc::tick cannot
         * return {0,0} (now > physical gives physical >= 1; the else branch
         * goes through bump_logical, which carries a uint32 wrap of logical
         * into physical and saturates rather than wrapping at the top), both
         * local existence producers go through it, and build_snapshot only
         * ever advertises asserted() cells -- so no honest writer can emit
         * {0,0} in the first place. */
        if (c->hlc.physical == 0 && c->hlc.logical == 0) return SYNC_ERR_INVALID;
    }
    if (c->kind == SYNC_CHANGE_REGISTER) {
        if (!c->field && c->field_len) return SYNC_ERR_INVALID;
        if (!c->value && c->value_len) return SYNC_ERR_INVALID;
    }
    try {
        std::string nsk = to_str(c->ns, c->ns_len);
        std::string entk = to_str(c->entity, c->entity_len);

        /* Decide whether this record would change state *before* paying for the
         * signature check — verifying is ~100x everything else (see docs/PERF.md),
         * so a record that loses LWW or that we already hold is dropped for free.
         * This is safe: an unverified record reaches no state and doesn't even
         * perturb the clock (a dominated record's HLC is already <= ours), and a
         * record forged to *win* the comparison still gets verified and rejected
         * below. We look up with find() so a rejected record inserts nothing
         * (no empty-entity growth from spam). */
        auto find_entity = [&](void) -> const Entity * {
            auto ni = e->ns.find(nsk);
            if (ni == e->ns.end()) return nullptr;
            auto ei = ni->second.find(entk);
            return ei == ni->second.end() ? nullptr : &ei->second;
        };

        if (c->kind == SYNC_CHANGE_EXISTENCE) {
            const Entity *cur = find_entity();
            /* LWW on the presence register: the later (hlc, author) wins. An
             * entity with no assertion has hlc {0,0}, which any real assertion
             * beats. No counter to saturate. */
            Hlc inc_hlc = {c->hlc.physical, c->hlc.logical};
            Hlc cur_hlc = cur ? cur->presence_hlc : Hlc{0, 0};
            const uint8_t *cur_author =
                cur ? cur->ex_author.data() : kZeroAuthor;
            int order = hlc_cmp(inc_hlc, cur_hlc);
            if (order == 0)
                order = std::memcmp(c->author, cur_author, SYNC_PUBKEY_LEN);
            if (order <= 0) return SYNC_OK; /* dominated: no verify, no state */

            std::string signing; /* canonical signing bytes (verify_change) */
            if (!already_verified && !verify_change(c, signing)) {
                engine_log(e, SYNC_LOG_WARN, "apply: signature verification failed");
                return SYNC_ERR_BADSIG;
            }
            int authz = cap_authorize_write(e, c->author, nsk);
            if (authz != SYNC_OK) {
                engine_log(e, SYNC_LOG_WARN,
                           "apply: write not authorized for namespace");
                return authz;
            }
            /* Hoisted: the element hash (which can allocate and throw) is
             * computed before the first committed byte — the e->ns[nsk][entk]
             * lookup below itself inserts, so it is already a mutation.
             * Precomputed by the parallel verifier when available; streaming
             * from the verify buffer when one was built here; the one-shot
             * re-encode remains only as the fallback for an already_verified
             * caller that supplies no hash. */
            Hash256 eh;
            if (elem_hash) eh = *elem_hash;
            else if (already_verified) eh = ke::element_hash(*c);
            else ke::element_hash(signing, c->signature, eh);
            Entity &ent = e->ns[nsk][entk];
            ent.present_v = (c->causal_length != 0); /* present bit */
            ent.presence_hlc = inc_hlc;
            std::memcpy(ent.ex_author.data(), c->author, SYNC_PUBKEY_LEN);
            std::memcpy(ent.ex_sig.data(), c->signature, SYNC_SIG_LEN);
            ent.ex_hash = eh;
            /* Adopt the assertion's HLC so later local writes are strictly newer. */
            e->clock.receive(inc_hlc, now_ms());
            e->content_gen++; /* invalidate the reconciliation snapshot cache */
            if (e->store) {
                e->db_clock++;
                if (!tx_entity(e, nsk, entk, ent)) return SYNC_ERR_INTERNAL;
            }
            return SYNC_OK;
        }

        /* REGISTER */
        Register cand;
        cand.value = to_str(c->value, c->value_len);
        cand.hlc = {c->hlc.physical, c->hlc.logical};
        std::memcpy(cand.author.data(), c->author, SYNC_PUBKEY_LEN);
        std::memcpy(cand.sig.data(), c->signature, SYNC_SIG_LEN);
        std::string fkey = to_str(c->field, c->field_len);

        const Entity *cur = find_entity();
        if (cur) {
            auto fi = cur->fields.find(fkey);
            if (fi != cur->fields.end() && register_cmp(cand, fi->second) <= 0)
                return SYNC_OK; /* dominated: no verify, no clock, no state */
        }

        std::string signing; /* canonical signing bytes (verify_change) */
        if (!already_verified && !verify_change(c, signing)) {
            engine_log(e, SYNC_LOG_WARN, "apply: signature verification failed");
            return SYNC_ERR_BADSIG;
        }
        int authz = cap_authorize_write(e, c->author, nsk);
        if (authz != SYNC_OK) {
            engine_log(e, SYNC_LOG_WARN,
                       "apply: write not authorized for namespace");
            return authz;
        }

        /* Hoisted: hash into the still-local candidate before the map
         * lookups below (whose node inserts are the first committed bytes);
         * see the EXISTENCE branch for the overload choice. */
        if (elem_hash) cand.elem_hash = *elem_hash;
        else if (already_verified) cand.elem_hash = ke::element_hash(*c);
        else ke::element_hash(signing, c->signature, cand.elem_hash);
        /* Install by try_emplace + move, not operator[]: operator[] is two
         * mutations — it default-inserts a zero-hashed Register and only then
         * runs an allocating copy-assign, so a bad_alloc in between would
         * commit a default cell whose cached hash is not its own. Here the
         * node allocation fails before anything is linked (strong guarantee)
         * and the move is a non-throwing buffer steal (static_assert above). */
        Entity &ent = e->ns[nsk][entk];
        auto ins = ent.fields.try_emplace(fkey, std::move(cand));
        if (!ins.second) ins.first->second = std::move(cand);
        e->content_gen++; /* invalidate the reconciliation snapshot cache */
        /* Only an accepted record advances the clock; its HLC is now adopted. */
        e->clock.receive({c->hlc.physical, c->hlc.logical}, now_ms());
        if (e->store) {
            e->db_clock++;
            if (!tx_entity_field(e, nsk, entk, fkey, ent, ins.first->second))
                return SYNC_ERR_INTERNAL;
        }
        return SYNC_OK;
    } catch (const std::bad_alloc &) {
        return SYNC_ERR_NOMEM;
    } catch (...) {
        return SYNC_ERR_INTERNAL;
    }
}

extern "C" {

int sync_engine_apply(sync_engine *e, const sync_change *c) {
    return ke::apply_change(e, c, false);
}

int sync_engine_export(sync_engine *e, sync_change **out, size_t *out_count) {
    if (!e || !out || !out_count) return SYNC_ERR_INVALID;
    *out = nullptr;
    *out_count = 0;
    try {
        /* Count first. */
        size_t n = 0;
        for (auto &np : e->ns)
            for (auto &ep : np.second) {
                if (ep.second.asserted()) n++;              /* existence */
                n += ep.second.fields.size();               /* registers */
            }
        if (n == 0) return SYNC_OK;

        sync_change *arr =
            static_cast<sync_change *>(std::calloc(n, sizeof(sync_change)));
        if (!arr) return SYNC_ERR_NOMEM;

        size_t i = 0;
        bool oom = false;
        for (auto &np : e->ns) {
            const std::string &nsk = np.first;
            for (auto &ep : np.second) {
                const std::string &entk = ep.first;
                Entity &ent = ep.second;
                if (ent.asserted()) {
                    sync_change &c = arr[i++];
                    c.kind = SYNC_CHANGE_EXISTENCE;
                    c.ns = dup_field(nsk, &oom); c.ns_len = nsk.size();
                    if (oom) goto fail;
                    c.entity = dup_field(entk, &oom); c.entity_len = entk.size();
                    if (oom) goto fail;
                    c.causal_length = ent.present_v ? 1 : 0; /* present bit */
                    c.hlc.physical = ent.presence_hlc.physical;
                    c.hlc.logical = ent.presence_hlc.logical;
                    std::memcpy(c.author, ent.ex_author.data(), SYNC_PUBKEY_LEN);
                    std::memcpy(c.signature, ent.ex_sig.data(), SYNC_SIG_LEN);
                }
                for (auto &fp : ent.fields) {
                    const std::string &fk = fp.first;
                    Register &r = fp.second;
                    sync_change &c = arr[i++];
                    c.kind = SYNC_CHANGE_REGISTER;
                    c.ns = dup_field(nsk, &oom); c.ns_len = nsk.size();
                    if (oom) goto fail;
                    c.entity = dup_field(entk, &oom); c.entity_len = entk.size();
                    if (oom) goto fail;
                    c.field = dup_field(fk, &oom); c.field_len = fk.size();
                    if (oom) goto fail;
                    c.value = dup_field(r.value, &oom); c.value_len = r.value.size();
                    if (oom) goto fail;
                    c.hlc.physical = r.hlc.physical;
                    c.hlc.logical = r.hlc.logical;
                    std::memcpy(c.author, r.author.data(), SYNC_PUBKEY_LEN);
                    std::memcpy(c.signature, r.sig.data(), SYNC_SIG_LEN);
                }
            }
        }
        *out = arr;
        *out_count = n;
        return SYNC_OK;
    fail:
        sync_changes_free(arr, i);
        return SYNC_ERR_NOMEM;
    } catch (const std::bad_alloc &) {
        return SYNC_ERR_NOMEM;
    } catch (...) {
        return SYNC_ERR_INTERNAL;
    }
}

void sync_changes_free(sync_change *arr, size_t count) {
    if (!arr) return;
    for (size_t i = 0; i < count; i++) free_change_fields(arr[i]);
    std::free(arr);
}

int sync_engine_digest(sync_engine *e, uint8_t out[SYNC_DIGEST_LEN]) {
    if (!e || !out) return SYNC_ERR_INVALID;
    try {
        Sha256 h;
        for (auto &np : e->ns) {
            const std::string &nsk = np.first;
            for (auto &ep : np.second) {
                const std::string &entk = ep.first;
                Entity &ent = ep.second;
                /* Only an ASSERTED presence contributes a presence block --
                 * the same gate build_snapshot/export apply, so the digest
                 * quantifies over exactly the element set reconciliation
                 * replicates. An unasserted shell (an entity that reached the
                 * map via a register whose existence record has not arrived)
                 * has no assertion to hash: its block would be the constant
                 * "no assertion" tuple (present=0, hlc {0,0}, zero author),
                 * whose only information is "this key is in the map" -- which
                 * is precisely what RBSR does not replicate. Hashing it let
                 * two replicas that reconciliation calls fully converged hold
                 * different digests, with no route to repair (an unasserted
                 * shell survives both gc_tombstones and compaction). Its
                 * registers below are still hashed: real state, still
                 * advertised, still replicated. */
                if (ent.asserted()) {
                    const uint8_t tagE = 'E';
                    h.update(&tagE, 1);
                    feed(h, nsk.data(), nsk.size());
                    feed(h, entk.data(), entk.size());
                    const uint8_t present = ent.present_v ? 1 : 0;
                    h.update(&present, 1);
                    feed_u64(h, ent.presence_hlc.physical);
                    feed_u32(h, ent.presence_hlc.logical);
                    h.update(ent.ex_author.data(), SYNC_PUBKEY_LEN);
                }
                for (auto &fp : ent.fields) {
                    const std::string &fk = fp.first;
                    Register &r = fp.second;
                    const uint8_t tagR = 'R';
                    h.update(&tagR, 1);
                    feed(h, nsk.data(), nsk.size());
                    feed(h, entk.data(), entk.size());
                    feed(h, fk.data(), fk.size());
                    feed(h, r.value.data(), r.value.size());
                    feed_u64(h, r.hlc.physical);
                    feed_u32(h, r.hlc.logical);
                    h.update(r.author.data(), SYNC_PUBKEY_LEN);
                }
            }
        }
        h.finish(out);
        return SYNC_OK;
    } catch (...) {
        return SYNC_ERR_INTERNAL;
    }
}

} // extern "C"
