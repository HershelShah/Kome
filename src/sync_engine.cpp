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

#include "byteorder.h"
#include "capability.h"
#include "codec.h"
#include "crypto.h"
#include "engine.hpp"
#include "sha256.h"
#include "storage.h"

namespace ke {

uint64_t now_ms() {
    using namespace std::chrono;
    return (uint64_t)duration_cast<milliseconds>(
               system_clock::now().time_since_epoch())
        .count();
}

Hlc Hlc::tick(uint64_t now) {
    if (now > physical) {
        physical = now;
        logical = 0;
    } else {
        logical += 1;
    }
    return *this;
}

void Hlc::receive(const Hlc &remote, uint64_t now) {
    uint64_t old_p = physical;
    uint64_t new_p = old_p;
    if (remote.physical > new_p) new_p = remote.physical;
    if (now > new_p) new_p = now;

    if (new_p == old_p && new_p == remote.physical) {
        logical = (logical > remote.logical ? logical : remote.logical) + 1;
    } else if (new_p == old_p) {
        logical += 1;
    } else if (new_p == remote.physical) {
        logical = remote.logical + 1;
    } else {
        logical = 0;
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

/* Fill c->author and c->signature by signing c's canonical content with e. */
void author_sign(sync_engine *e, sync_change &c) {
    std::memcpy(c.author, e->identity.sign_pk.data(), SYNC_PUBKEY_LEN);
    std::string signing;
    ke::encode_signing(c, signing);
    ke::sign(e->identity.sign_sk.data(), signing.data(), signing.size(),
             c.signature);
}

/* Verify a record's signature against its declared author. */
bool verify_change(const sync_change *c) {
    std::string signing;
    ke::encode_signing(*c, signing);
    return ke::verify(c->author, signing.data(), signing.size(), c->signature);
}

/* Sign the entity's current existence assertion (the caller has already set
 * en.causal_length) and store the author/signature on the entity. Shared by
 * the add path (set) and the remove path (delete). */
void sign_existence(sync_engine *e, const std::string &ns,
                    const std::string &ent, Entity &en) {
    sync_change ec;
    std::memset(&ec, 0, sizeof ec);
    ec.kind = SYNC_CHANGE_EXISTENCE;
    ec.ns = (const uint8_t *)ns.data(); ec.ns_len = ns.size();
    ec.entity = (const uint8_t *)ent.data(); ec.entity_len = ent.size();
    ec.causal_length = en.causal_length;
    author_sign(e, ec);
    std::memcpy(en.ex_author.data(), ec.author, SYNC_PUBKEY_LEN);
    std::memcpy(en.ex_sig.data(), ec.signature, SYNC_SIG_LEN);
}

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

/* Persist an entity row (and clock) in one transaction. */
bool tx_entity(sync_engine *e, const std::string &ns, const std::string &ent,
               const Entity &en) {
    Storage *s = e->store;
    if (!s->begin()) return false;
    bool ok = s->put_entity(ns, ent, en.causal_length, en.ex_author, en.ex_sig,
                            e->db_clock) &&
              persist_meta_clock(e);
    if (!ok) { s->rollback(); return false; }
    return s->commit();
}

/* Persist an entity row + one field register (and clock) in one transaction. */
bool tx_entity_field(sync_engine *e, const std::string &ns,
                     const std::string &ent, const std::string &field,
                     const Entity &en, const Register &reg) {
    Storage *s = e->store;
    if (!s->begin()) return false;
    bool ok = s->put_entity(ns, ent, en.causal_length, en.ex_author, en.ex_sig,
                            e->db_clock) &&
              s->put_field(ns, ent, field, reg.value, reg.hlc, reg.author,
                           reg.sig, e->db_clock) &&
              persist_meta_clock(e);
    if (!ok) { s->rollback(); return false; }
    return s->commit();
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

sync_engine *sync_engine_open(const char *path,
                              const uint8_t seed[SYNC_SEED_LEN]) {
    if (!path || !seed) return nullptr;
    try {
        sync_error err = SYNC_OK;
        Storage *store = Storage::open(path, &err);
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

int sync_engine_flush(sync_engine *e) {
    if (!e) return SYNC_ERR_INVALID;
    /* Write-through keeps disk current; WAL checkpoints on close. Nothing to
     * force here, but validate the handle for a clean contract. */
    return SYNC_OK;
}

void sync_engine_destroy(sync_engine *e) {
    if (!e) return;
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
        Entity &ent = e->ns[nsk][entk];

        if (!ent.present()) {
            ent.causal_length += 1; /* causal-length add; sign the assertion */
            sign_existence(e, nsk, entk, ent);
        }

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
            author_sign(e, rc);
            std::memcpy(reg.author.data(), rc.author, SYNC_PUBKEY_LEN);
            std::memcpy(reg.sig.data(), rc.signature, SYNC_SIG_LEN);
        }
        /* A fresh local tick dominates any prior state for this cell. */
        ent.fields[fk] = reg;
        e->state_gen++; /* invalidate the reconciliation snapshot cache */

        if (e->store) {
            e->db_clock++;
            if (!tx_entity_field(e, nsk, entk, fk, ent, reg))
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
            ent.causal_length += 1; /* remove; sign the new assertion */
            sign_existence(e, nsk, entk, ent);
            e->state_gen++; /* invalidate the reconciliation snapshot cache */
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

int sync_engine_apply(sync_engine *e, const sync_change *c) {
    if (!e || !c) return SYNC_ERR_INVALID;
    if ((!c->ns && c->ns_len) || (!c->entity && c->entity_len))
        return SYNC_ERR_INVALID;
    if (c->kind != SYNC_CHANGE_EXISTENCE && c->kind != SYNC_CHANGE_REGISTER)
        return SYNC_ERR_INVALID;
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
            uint64_t cur_cl = cur ? cur->causal_length : 0;
            const uint8_t *cur_author =
                cur ? cur->ex_author.data() : kZeroAuthor;
            int order = (c->causal_length > cur_cl) ? 1
                        : (c->causal_length < cur_cl) ? -1
                        : std::memcmp(c->author, cur_author, SYNC_PUBKEY_LEN);
            if (order <= 0) return SYNC_OK; /* dominated: no verify, no state */

            if (!verify_change(c)) {
                engine_log(e, SYNC_LOG_WARN, "apply: signature verification failed");
                return SYNC_ERR_BADSIG;
            }
            int authz = cap_authorize_write(e, c->author, nsk);
            if (authz != SYNC_OK) {
                engine_log(e, SYNC_LOG_WARN,
                           "apply: write not authorized for namespace");
                return authz;
            }
            Entity &ent = e->ns[nsk][entk];
            ent.causal_length = c->causal_length; /* (cl, author) max */
            std::memcpy(ent.ex_author.data(), c->author, SYNC_PUBKEY_LEN);
            std::memcpy(ent.ex_sig.data(), c->signature, SYNC_SIG_LEN);
            e->state_gen++; /* invalidate the reconciliation snapshot cache */
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

        if (!verify_change(c)) {
            engine_log(e, SYNC_LOG_WARN, "apply: signature verification failed");
            return SYNC_ERR_BADSIG;
        }
        int authz = cap_authorize_write(e, c->author, nsk);
        if (authz != SYNC_OK) {
            engine_log(e, SYNC_LOG_WARN,
                       "apply: write not authorized for namespace");
            return authz;
        }

        Entity &ent = e->ns[nsk][entk];
        ent.fields[fkey] = cand;
        e->state_gen++; /* invalidate the reconciliation snapshot cache */
        /* Only an accepted record advances the clock; its HLC is now adopted. */
        e->clock.receive({c->hlc.physical, c->hlc.logical}, now_ms());
        if (e->store) {
            e->db_clock++;
            if (!tx_entity_field(e, nsk, entk, fkey, ent, cand))
                return SYNC_ERR_INTERNAL;
        }
        return SYNC_OK;
    } catch (const std::bad_alloc &) {
        return SYNC_ERR_NOMEM;
    } catch (...) {
        return SYNC_ERR_INTERNAL;
    }
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
                if (ep.second.causal_length > 0) n++;       /* existence */
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
                if (ent.causal_length > 0) {
                    sync_change &c = arr[i++];
                    c.kind = SYNC_CHANGE_EXISTENCE;
                    c.ns = dup_field(nsk, &oom); c.ns_len = nsk.size();
                    if (oom) goto fail;
                    c.entity = dup_field(entk, &oom); c.entity_len = entk.size();
                    if (oom) goto fail;
                    c.causal_length = ent.causal_length;
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
                const uint8_t tagE = 'E';
                h.update(&tagE, 1);
                feed(h, nsk.data(), nsk.size());
                feed(h, entk.data(), entk.size());
                feed_u64(h, ent.causal_length);
                h.update(ent.ex_author.data(), SYNC_PUBKEY_LEN);
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
