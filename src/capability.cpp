/* capability.cpp — capability tokens, chain verification, public ABI (M4). */
#include "capability.h"

#include <cstdlib>
#include <cstring>
#include <map>
#include <new>
#include <set>

#include "byteorder.h"
#include "codec.h" /* put_varint / get_varint */
#include "crypto.h"
#include "storage.h"

namespace ke {

/* Upper bound on capabilities learned over the wire (gossiped delegations). A
 * peer can sign unlimited junk delegations from throwaway keys; without a cap
 * the store — and the per-write authorization scan — grow without bound. Locally
 * granted capabilities (sync_engine_grant) are a trust decision and not subject
 * to this limit. */
constexpr size_t kMaxIngestedCaps = 4096;

void cap_signing_bytes(const Capability &c, std::string &out) {
    out.push_back((char)0x01); /* capability format version */
    out.append((const char *)c.issuer.data(), c.issuer.size());
    out.append((const char *)c.subject.data(), c.subject.size());
    put_varint(out, c.ns.size());
    out.append(c.ns);
    out.push_back((char)c.access);
    put_u64le(out, c.expiry);
}

void cap_encode(const Capability &c, std::string &out) {
    cap_signing_bytes(c, out);
    out.append((const char *)c.sig.data(), c.sig.size());
}

bool cap_decode(const uint8_t *buf, size_t len, Capability &out) {
    const uint8_t *p = buf, *end = buf + len;
    if (p >= end || *p++ != 0x01) return false; /* version */
    if (end - p < (long)(2 * SYNC_PUBKEY_LEN)) return false; /* issuer+subject */
    std::memcpy(out.issuer.data(), p, SYNC_PUBKEY_LEN); p += SYNC_PUBKEY_LEN;
    std::memcpy(out.subject.data(), p, SYNC_PUBKEY_LEN); p += SYNC_PUBKEY_LEN;
    uint64_t nslen = 0;
    if (!get_varint(p, end, nslen) || (uint64_t)(end - p) < nslen) return false;
    out.ns.assign((const char *)p, (size_t)nslen); p += nslen;
    if (p >= end) return false;
    out.access = *p++;
    if (end - p < (long)(8 + SYNC_SIG_LEN)) return false; /* expiry + sig */
    out.expiry = read_u64le(p);
    p += 8;
    std::memcpy(out.sig.data(), p, SYNC_SIG_LEN);
    return true;
}

bool cap_sig_valid(const Capability &c) {
    std::string s;
    cap_signing_bytes(c, s);
    return verify(c.issuer.data(), s.data(), s.size(), c.sig.data());
}

/* ---- revocations ------------------------------------------------------- */

void rev_signing_bytes(const Revocation &r, std::string &out) {
    out.push_back((char)0x01); /* revocation format version */
    out.append((const char *)r.revoker.data(), r.revoker.size());
    out.append((const char *)r.subject.data(), r.subject.size());
    put_varint(out, r.ns.size());
    out.append(r.ns);
    put_u64le(out, r.issued_ms);
}

void rev_encode(const Revocation &r, std::string &out) {
    rev_signing_bytes(r, out);
    out.append((const char *)r.sig.data(), r.sig.size());
}

bool rev_decode(const uint8_t *buf, size_t len, Revocation &out) {
    const uint8_t *p = buf, *end = buf + len;
    if (p >= end || *p++ != 0x01) return false; /* version */
    if (end - p < (long)(2 * SYNC_PUBKEY_LEN)) return false; /* revoker+subject */
    std::memcpy(out.revoker.data(), p, SYNC_PUBKEY_LEN); p += SYNC_PUBKEY_LEN;
    std::memcpy(out.subject.data(), p, SYNC_PUBKEY_LEN); p += SYNC_PUBKEY_LEN;
    uint64_t nslen = 0;
    if (!get_varint(p, end, nslen) || (uint64_t)(end - p) < nslen) return false;
    out.ns.assign((const char *)p, (size_t)nslen); p += nslen;
    if (end - p < (long)(8 + SYNC_SIG_LEN)) return false; /* issued + sig */
    out.issued_ms = read_u64le(p);
    p += 8;
    std::memcpy(out.sig.data(), p, SYNC_SIG_LEN);
    return true;
}

bool rev_sig_valid(const Revocation &r) {
    std::string s;
    rev_signing_bytes(r, s);
    return verify(r.revoker.data(), s.data(), s.size(), r.sig.data());
}

void CapStore::add(const Capability &c) {
    for (const auto &x : caps_)
        if (x.sig == c.sig) return; /* duplicate */
    caps_.push_back(c);
}

void CapStore::add_rev(const Revocation &r) {
    for (const auto &x : revs_)
        if (x.sig == r.sig) return; /* duplicate */
    revs_.push_back(r);
}

void CapStore::export_blobs(std::vector<std::string> &out) const {
    for (const auto &c : caps_) {
        std::string b;
        cap_encode(c, b);
        out.push_back(std::move(b));
    }
}

void CapStore::export_rev_blobs(std::vector<std::string> &out) const {
    for (const auto &r : revs_) {
        std::string b;
        rev_encode(r, b);
        out.push_back(std::move(b));
    }
}

bool CapStore::has(const Sig &sig) const {
    for (const auto &c : caps_)
        if (c.sig == sig) return true;
    return false;
}

bool CapStore::has_rev(const Sig &sig) const {
    for (const auto &r : revs_)
        if (r.sig == sig) return true;
    return false;
}

/* Subjects with an *effective* revocation in `ns` — one whose revoker is known
 * here to hold the namespace root. (A revocation signed by a non-owner, or by an
 * owner we don't recognize, is inert: it stays for relaying but grants nothing.) */
void CapStore::revoked_in(const std::string &ns,
                          std::vector<std::string> &out) const {
    if (revs_.empty()) return;
    std::set<std::string> roots;
    for (const auto &c : caps_)
        if (c.is_root() && c.ns == ns) roots.insert(key_bytes(c.issuer));
    if (roots.empty()) return;
    for (const auto &r : revs_)
        if (r.ns == ns && roots.count(key_bytes(r.revoker)))
            out.push_back(key_bytes(r.subject));
}

bool CapStore::is_revoked(const uint8_t subject[32], const std::string &ns) const {
    std::vector<std::string> revoked;
    revoked_in(ns, revoked);
    std::string sk((const char *)subject, SYNC_PUBKEY_LEN);
    for (const auto &s : revoked)
        if (s == sk) return true;
    return false;
}

bool CapStore::is_root_owner(const uint8_t me[32], const std::string &ns) const {
    std::string mk((const char *)me, SYNC_PUBKEY_LEN);
    for (const auto &c : caps_)
        if (c.is_root() && c.ns == ns && key_bytes(c.issuer) == mk) return true;
    return false;
}

bool CapStore::owned(const std::string &ns) const {
    for (const auto &c : caps_)
        if (c.is_root() && c.ns == ns) return true;
    return false;
}

bool CapStore::authorized(const uint8_t author[32], const std::string &ns,
                          uint8_t need, uint64_t now, bool *time_bound,
                          uint64_t *valid_until_ms) const {
    if (time_bound) *time_bound = false;
    /* Unbounded until proven otherwise. Every path that returns without
     * revisiting this is a path whose answer cannot change with time alone: it
     * changes only via a grant/revoke/ingest, each of which bumps scope_gen and
     * so invalidates any cache keyed on it. */
    if (valid_until_ms) *valid_until_ms = UINT64_MAX;
    /* Capabilities in the store are signature-verified on insertion, so the
     * hot path only checks access/expiry (no EdDSA here). */
    auto usable = [now](const Capability &c) {
        return c.access != 0 && (c.expiry == 0 || now <= c.expiry);
    };

    /* Keys the namespace owner has revoked. A revoked key is given no access and
     * cannot pass access onward, so revoking a (lost/stolen) key also cuts off
     * every capability that key sub-delegated. Computed once for both passes. */
    std::set<std::string> revoked;
    {
        std::vector<std::string> rv;
        revoked_in(ns, rv);
        revoked.insert(rv.begin(), rv.end());
    }

    /* Maximal-access fixpoint for `author` over this namespace's capability graph,
     * optionally restricted to permanent (never-expiring) caps. Returns {open,
     * access}: `open` means the namespace has no usable root (unowned == world-
     * readable); otherwise `access` is the largest mask `author` can prove.
     * best[holder] is the union of access reachable via any chain from the owner,
     * each hop attenuated to what the issuer actually holds (granted = c->access &
     * issuer's best). Indexing usable delegations by issuer once keeps the walk
     * O(N) total (not O(N^2) — a remote DoS once a peer gossips many delegations).
     * Iterating to a fixpoint (rather than returning at the first chain to reach
     * the author) means a subject holding several delegations gets the union, so a
     * role upgrade that adds a second, broader grant is honored. Masks only gain
     * bits (<=2), so it terminates and is cycle-safe. */
    struct Result { bool open; uint8_t access; };
    /* `expiring` (when non-null) collects, over the *usable* caps of this
     * namespace, whether any carries a finite expiry and the earliest such
     * expiry — the instant at which this whole answer may change. Every usable
     * cap counts, not just the ones on the winning chain: a cap expiring
     * elsewhere in the namespace can turn a denial into an allow (losing the
     * last usable root makes the namespace open == world-readable). Expired caps
     * are already filtered out by usable(), and expiry is one-way, so the
     * minimum collected here is always >= now. */
    struct Expiring { bool saw = false; uint64_t min_ms = UINT64_MAX; };
    auto solve = [&](bool permanent_only, Expiring *expiring) -> Result {
        const Capability *root = nullptr;
        std::map<std::string, std::vector<const Capability *>> by_issuer;
        for (const auto &c : caps_) {
            if (!usable(c) || c.ns != ns) continue;
            if (expiring && c.expiry != 0) {
                expiring->saw = true;
                if (c.expiry < expiring->min_ms) expiring->min_ms = c.expiry;
            }
            if (permanent_only && c.expiry != 0) continue;
            if (c.is_root()) {
                if (!root) root = &c;
            } else {
                by_issuer[key_bytes(c.issuer)].push_back(&c);
            }
        }
        if (!root) return {true, 0};

        std::map<std::string, uint8_t> best;
        std::vector<std::string> work;
        std::string rk = key_bytes(root->issuer);
        if (revoked.count(rk)) return {false, 0}; /* owner revoked itself */
        best[rk] = root->access;
        work.push_back(rk);
        while (!work.empty()) {
            std::string h = std::move(work.back());
            work.pop_back();
            if (revoked.count(h)) continue; /* a revoked key passes on nothing */
            uint8_t ha = best[h];
            auto it = by_issuer.find(h);
            if (it == by_issuer.end()) continue;
            for (const Capability *c : it->second) {
                uint8_t granted = (uint8_t)(c->access & ha); /* can't exceed issuer's */
                if (!granted) continue;
                std::string subj = key_bytes(c->subject);
                if (revoked.count(subj)) continue; /* a revoked key gets nothing */
                auto sit = best.find(subj);
                uint8_t cur = sit == best.end() ? 0 : sit->second;
                uint8_t next = (uint8_t)(cur | granted);
                if (next != cur) { best[subj] = next; work.push_back(subj); }
            }
        }
        std::string akey((const char *)author, SYNC_PUBKEY_LEN);
        auto ait = best.find(akey);
        return {false, ait == best.end() ? (uint8_t)0 : ait->second};
    };

    Expiring expiring;
    Result all = solve(/*permanent_only=*/false, &expiring);
    /* No usable root: the namespace is open (world-readable/writable). This is
     * absorbing — caps only ever expire, never revive — so "open" cannot lapse
     * with time, and valid_until_ms stays unbounded. */
    if (all.open) return true;
    /* Owned, and something in this namespace expires: the answer below — allow
     * OR deny — holds only until that instant. Set for the denied case too
     * (§3.5 fix 1): owned() ignores expiry, so a namespace whose only root has a
     * finite expiry silently becomes open once that root lapses, flipping a
     * denial to world-readable with no generation bump anywhere. */
    if (valid_until_ms && expiring.saw) *valid_until_ms = expiring.min_ms;
    bool ok = (all.access & need) == need;
    /* Time-bound only if `need` cannot be proven from permanent caps alone — i.e.
     * the answer genuinely depends on a finite-expiry cap. With no expiring cap in
     * the namespace the permanent-only pass is identical, so skip it. (A permanent
     * member in a namespace that merely also holds some unrelated expiring cap is
     * thus correctly NOT flagged time-bound, keeping its scoped snapshot cacheable.) */
    if (ok && time_bound && expiring.saw) {
        Result perm = solve(/*permanent_only=*/true, nullptr);
        *time_bound = (perm.access & need) != need;
    }
    return ok;
}

void cap_ingest_delegations(sync_engine *e,
                            const std::vector<std::string> &blobs) {
    for (const auto &blob : blobs) {
        if (e->caps && e->caps->size() >= kMaxIngestedCaps)
            break; /* bound growth from a peer flooding signed junk */
        Capability c;
        if (!cap_decode((const uint8_t *)blob.data(), blob.size(), c)) continue;
        if (c.is_root()) continue;          /* never trust a wire root */
        if (e->caps && e->caps->has(c.sig)) continue; /* known: skip re-verify */
        if (!cap_sig_valid(c)) continue;    /* verify once, on first sight */
        if (!e->caps) e->caps = new CapStore();
        e->caps->add(c);
        e->scope_gen++; /* a new delegation can change read-scope: invalidate
                         * cached scoped snapshots (the unscoped content snapshot
                         * stays valid — no element changed). Only genuinely-new
                         * caps reach here (known sigs are skipped above), so a
                         * converged session re-ingesting the same caps does not
                         * bump. */
    }
}

/* Upper bound on revocations learned over the wire (same rationale as caps). */
constexpr size_t kMaxIngestedRevs = 4096;

void rev_ingest(sync_engine *e, const std::vector<std::string> &blobs) {
    for (const auto &blob : blobs) {
        Revocation r;
        if (!rev_decode((const uint8_t *)blob.data(), blob.size(), r)) continue;
        if (e->caps && e->caps->has_rev(r.sig)) continue; /* known: skip re-verify */
        if (!rev_sig_valid(r)) continue;                  /* verify once, on first sight */
        if (!e->caps) e->caps = new CapStore();
        /* An *authoritative* revocation (signed by a key we trust as this
         * namespace's root) is the security payload this gossip exists to carry,
         * and is self-limited (only the real owner can mint it). Bound only the
         * relay-only (not-yet-authoritative) revocations, so a peer flooding
         * signed junk can't fill the store and block a genuine cut-off from
         * propagating through this node. */
        bool authoritative = e->caps->is_root_owner(r.revoker.data(), r.ns);
        if (!authoritative && e->caps->rev_count() >= kMaxIngestedRevs)
            continue;
        e->caps->add_rev(r);
        e->scope_gen++; /* a revocation changes read-scope: invalidate scoped
                         * snapshots (the unscoped content snapshot stays valid) */
        /* Persist authoritative revocations so the cut-off survives a reopen
         * without persisting unrelated/junk ones. Like sync_engine_revoke,
         * put_revocation writes its own immediately-fsync'd frame even inside
         * an open batch (spec §3.3 point 5) — a durable cut-off must not be
         * discardable by a later batch_abort. */
        if (e->store && authoritative) {
            std::string b;
            rev_encode(r, b);
            e->store->put_revocation(b);
        }
    }
}

int cap_authorize_write(sync_engine *e, const uint8_t author[32],
                        const std::string &ns) {
    if (!e->caps) return SYNC_OK; /* no capability system engaged */
    if (!e->caps->owned(ns)) return SYNC_OK; /* open namespace */
    return e->caps->authorized(author, ns, kAccessWrite, now_ms())
               ? SYNC_OK
               : SYNC_ERR_UNAUTHORIZED;
}

bool cap_authorize_read(sync_engine *e, const uint8_t reader[32],
                        const std::string &ns, uint64_t now, bool *time_bound,
                        uint64_t *valid_until_ms) {
    if (time_bound) *time_bound = false;
    /* Both early returns below are time-independent, so the unbounded deadline
     * is not a fail-open default: engaging the capability system at all, and
     * taking ownership of a namespace, both require a local grant, and every
     * grant/revoke/wire-ingest bumps scope_gen (capability.cpp) — which
     * invalidates every per-peer cache keyed on the engine's GenPair. Only
     * expiry moves without a bump, and expiry is what authorized() reports. */
    if (valid_until_ms) *valid_until_ms = UINT64_MAX;
    if (!e->caps) return true;              /* no capability system engaged */
    if (!e->caps->owned(ns)) return true;   /* open (unowned) namespace */
    /* `now` is the caller's, never now_ms() here — see capability.h. */
    return e->caps->authorized(reader, ns, kAccessRead, now, time_bound,
                               valid_until_ms);
}

} // namespace ke

/* ---- public capability ABI --------------------------------------------- */

using namespace ke;

/* The opaque public type is just a Capability. */
struct sync_capability : public ke::Capability {};

extern "C" {

sync_capability *sync_capability_root(sync_engine *owner, const char *ns,
                                      int access) {
    if (!owner || !ns) return nullptr;
    if ((access & ~(int)(kAccessRead | kAccessWrite)) != 0 || access == 0)
        return nullptr;
    try {
        sync_capability *c = new (std::nothrow) sync_capability();
        if (!c) return nullptr;
        c->issuer = owner->identity.sign_pk;
        c->subject = owner->identity.sign_pk; /* self-signed root */
        c->ns = ns;
        c->access = (uint8_t)access;
        c->expiry = 0;
        std::string s;
        cap_signing_bytes(*c, s);
        sign(owner->identity.sign_sk.data(), s.data(), s.size(), c->sig.data());
        return c;
    } catch (...) {
        return nullptr;
    }
}

sync_capability *sync_capability_delegate(sync_engine *delegator,
                                          const sync_capability *parent,
                                          const uint8_t subject_pubkey[32],
                                          int access, uint64_t expiry_ms) {
    if (!delegator || !parent || !subject_pubkey) return nullptr;
    if ((access & ~(int)(kAccessRead | kAccessWrite)) != 0 || access == 0)
        return nullptr;
    /* The delegator must be the parent's subject, and may not widen access. */
    if (std::memcmp(delegator->identity.sign_pk.data(), parent->subject.data(),
                    SYNC_PUBKEY_LEN) != 0)
        return nullptr;
    if (((uint8_t)access & ~parent->access) != 0) return nullptr; /* over-broad */
    try {
        sync_capability *c = new (std::nothrow) sync_capability();
        if (!c) return nullptr;
        c->issuer = delegator->identity.sign_pk;
        std::memcpy(c->subject.data(), subject_pubkey, SYNC_PUBKEY_LEN);
        c->ns = parent->ns;
        c->access = (uint8_t)access;
        c->expiry = expiry_ms;
        std::string s;
        cap_signing_bytes(*c, s);
        sign(delegator->identity.sign_sk.data(), s.data(), s.size(),
             c->sig.data());
        return c;
    } catch (...) {
        return nullptr;
    }
}

int sync_capability_encode(const sync_capability *c, uint8_t *buf,
                           size_t buf_len) {
    if (!c) return 0;
    try {
        std::string s;
        cap_encode(*c, s);
        if (buf && buf_len >= s.size()) std::memcpy(buf, s.data(), s.size());
        return (int)s.size();
    } catch (...) {
        return 0;
    }
}

sync_capability *sync_capability_decode(const uint8_t *buf, size_t len) {
    if (!buf) return nullptr;
    try {
        sync_capability *c = new (std::nothrow) sync_capability();
        if (!c) return nullptr;
        if (!cap_decode(buf, len, *c)) {
            delete c;
            return nullptr;
        }
        return c;
    } catch (...) {
        return nullptr;
    }
}

int sync_engine_grant(sync_engine *e, const sync_capability *c) {
    if (!e || !c) return SYNC_ERR_INVALID;
    try {
        /* grant is the *local* trust API: the application decides which roots and
         * delegations to install (it accepts a root here, unlike the wire path
         * cap_ingest, which never does). Do NOT feed untrusted/network-received
         * capabilities here — that path is cap_ingest, which rejects roots and
         * only ever extends chains anchored at a locally-granted root.
         *
         * A granted capability must carry a valid signature (expiry is checked at
         * authorize time, so an expired-but-signed cap can still be held). */
        if (!cap_sig_valid(*c)) return SYNC_ERR_BADSIG;
        if (!e->caps) e->caps = new ke::CapStore();
        e->caps->add(*c);
        e->scope_gen++; /* read-scope changed: invalidate cached scoped snapshots
                         * (the unscoped content snapshot stays valid) */
        /* Persist so the grant survives a reopen. put_capability bypasses any
         * open write batch and writes its own immediately-fsync'd frame
         * (spec §3.3 point 5): SYNC_OK from grant means durable NOW, never
         * "staged and discardable by a later batch_abort". */
        if (e->store) {
            std::string blob;
            cap_encode(*c, blob);
            if (!e->store->put_capability(blob)) return SYNC_ERR_INTERNAL;
        }
        return SYNC_OK;
    } catch (const std::bad_alloc &) {
        return SYNC_ERR_NOMEM;
    } catch (...) {
        return SYNC_ERR_INTERNAL;
    }
}

int sync_engine_revoke(sync_engine *e, const char *ns,
                       const uint8_t subject_pubkey[32]) {
    if (!e || !ns || !subject_pubkey) return SYNC_ERR_INVALID;
    try {
        /* Only the namespace owner (holder of its root) may revoke. */
        if (!e->caps ||
            !e->caps->is_root_owner(e->identity.sign_pk.data(), ns))
            return SYNC_ERR_UNAUTHORIZED;
        ke::Revocation r;
        r.revoker = e->identity.sign_pk;
        std::memcpy(r.subject.data(), subject_pubkey, SYNC_PUBKEY_LEN);
        r.ns = ns;
        r.issued_ms = now_ms();
        std::string s;
        rev_signing_bytes(r, s);
        sign(e->identity.sign_sk.data(), s.data(), s.size(), r.sig.data());
        e->caps->add_rev(r);
        e->scope_gen++; /* read-scope changed: invalidate cached scoped snapshots
                         * (the unscoped content snapshot stays valid) */
        /* Security: put_revocation bypasses any open write batch and writes
         * its own immediately-fsync'd frame (spec §3.3 point 5). A revocation
         * that could be discarded by a later batch_abort would silently undo
         * a "remove a stolen device" cut-off the caller was told succeeded,
         * so revoke keeps synchronous fsync durability unconditionally. */
        if (e->store) {
            std::string blob;
            rev_encode(r, blob);
            if (!e->store->put_revocation(blob)) return SYNC_ERR_INTERNAL;
        }
        return SYNC_OK;
    } catch (const std::bad_alloc &) {
        return SYNC_ERR_NOMEM;
    } catch (...) {
        return SYNC_ERR_INTERNAL;
    }
}

int sync_engine_is_revoked(sync_engine *e, const char *ns,
                           const uint8_t subject_pubkey[32], int *out_revoked) {
    if (!e || !ns || !subject_pubkey || !out_revoked) return SYNC_ERR_INVALID;
    try {
        *out_revoked = (e->caps && e->caps->is_revoked(subject_pubkey, ns)) ? 1 : 0;
        return SYNC_OK;
    } catch (...) {
        return SYNC_ERR_INTERNAL;
    }
}

void sync_capability_subject(const sync_capability *c, uint8_t out[32]) {
    if (c && out) std::memcpy(out, c->subject.data(), SYNC_PUBKEY_LEN);
}

void sync_capability_free(sync_capability *c) { delete c; }

} // extern "C"
