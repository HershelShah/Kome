/* capability.cpp — capability tokens, chain verification, public ABI (M4). */
#include "capability.h"

#include <cstdlib>
#include <cstring>
#include <new>
#include <set>

#include "byteorder.h"
#include "codec.h" /* put_varint / get_varint */
#include "crypto.h"
#include "storage.h"

namespace ke {

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

void CapStore::add(const Capability &c) {
    for (const auto &x : caps_)
        if (x.sig == c.sig) return; /* duplicate */
    caps_.push_back(c);
}

void CapStore::export_blobs(std::vector<std::string> &out) const {
    for (const auto &c : caps_) {
        std::string b;
        cap_encode(c, b);
        out.push_back(std::move(b));
    }
}

bool CapStore::has(const Sig &sig) const {
    for (const auto &c : caps_)
        if (c.sig == sig) return true;
    return false;
}

bool CapStore::owned(const std::string &ns) const {
    for (const auto &c : caps_)
        if (c.is_root() && c.ns == ns) return true;
    return false;
}

bool CapStore::authorized(const uint8_t author[32], const std::string &ns,
                          uint8_t need, uint64_t now) const {
    /* Capabilities in the store are signature-verified on insertion, so the
     * hot path only checks access/expiry (no EdDSA here). */
    auto usable = [now](const Capability &c) {
        return c.access != 0 && (c.expiry == 0 || now <= c.expiry);
    };

    /* Find a usable root for the namespace. */
    const Capability *root = nullptr;
    for (const auto &c : caps_)
        if (c.is_root() && c.ns == ns && usable(c)) {
            root = &c;
            break;
        }
    if (!root) return true; /* unowned namespace == open */

    /* DFS from the owner, narrowing access at each hop. visited guards cycles. */
    std::set<std::string> visited;
    struct Frame { PubKey holder; uint8_t access; };
    std::vector<Frame> stack;
    Frame start;
    start.holder = root->issuer;
    start.access = root->access;
    stack.push_back(start);
    visited.insert(key_bytes(root->issuer));

    while (!stack.empty()) {
        Frame f = stack.back();
        stack.pop_back();

        if (std::memcmp(f.holder.data(), author, SYNC_PUBKEY_LEN) == 0)
            return (f.access & need) == need;

        for (const auto &c : caps_) {
            if (c.is_root()) continue;
            if (c.ns != ns) continue;
            if (std::memcmp(c.issuer.data(), f.holder.data(), SYNC_PUBKEY_LEN) != 0)
                continue;
            /* A delegation cannot widen the holder's access. */
            if ((c.access & ~f.access) != 0) continue;
            if (!usable(c)) continue;
            std::string subj = key_bytes(c.subject);
            if (visited.count(subj)) continue;
            visited.insert(subj);
            Frame nf;
            nf.holder = c.subject;
            nf.access = c.access;
            stack.push_back(nf);
        }
    }
    return false;
}

void cap_ingest_delegations(sync_engine *e,
                            const std::vector<std::string> &blobs) {
    for (const auto &blob : blobs) {
        Capability c;
        if (!cap_decode((const uint8_t *)blob.data(), blob.size(), c)) continue;
        if (c.is_root()) continue;          /* never trust a wire root */
        if (e->caps && e->caps->has(c.sig)) continue; /* known: skip re-verify */
        if (!cap_sig_valid(c)) continue;    /* verify once, on first sight */
        if (!e->caps) e->caps = new CapStore();
        e->caps->add(c);
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
                        const std::string &ns) {
    if (!e->caps) return true;
    if (!e->caps->owned(ns)) return true;
    return e->caps->authorized(reader, ns, kAccessRead, now_ms());
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
        /* A granted capability must carry a valid signature (expiry is checked
         * at authorize time, so an expired-but-signed cap can still be held). */
        if (!cap_sig_valid(*c)) return SYNC_ERR_BADSIG;
        if (!e->caps) e->caps = new ke::CapStore();
        e->caps->add(*c);
        /* Persist so the grant survives a reopen. */
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

void sync_capability_subject(const sync_capability *c, uint8_t out[32]) {
    if (c && out) std::memcpy(out, c->subject.data(), SYNC_PUBKEY_LEN);
}

void sync_capability_free(sync_capability *c) { delete c; }

} // extern "C"
