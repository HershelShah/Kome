/* codec.cpp — canonical record serialization + public codec ABI (M3/M4). */
#include "codec.h"

#include <cstdlib>
#include <cstring>
#include <new>

#include "byteorder.h"
#include "crypto.h"
#include "sha256.h"

namespace ke {

void put_varint(std::string &out, uint64_t v) {
    do {
        uint8_t b = (uint8_t)(v & 0x7f);
        v >>= 7;
        if (v) b |= 0x80;
        out.push_back((char)b);
    } while (v);
}

bool get_varint(const uint8_t *&p, const uint8_t *end, uint64_t &v) {
    v = 0;
    int shift = 0;
    while (p < end) {
        uint8_t b = *p++;
        if (shift > 63) return false;            /* overflow guard */
        /* On the 10th byte (shift==63) only bit 63 is representable; reject any
         * higher bits rather than silently truncating them (a malleability: two
         * byte strings decoding to the same value). */
        if (shift == 63 && (b & 0x7e)) return false;
        v |= (uint64_t)(b & 0x7f) << shift;
        if (!(b & 0x80)) {
            /* Reject non-minimal encodings: a terminating 0x00 group at a
             * non-zero shift is padding that put_varint never emits. Requiring
             * the unique minimal form keeps the wire record canonical — distinct
             * byte strings can't decode to the same logical record and churn the
             * content fingerprint / evade dedup (see reconcile apply_records). */
            if (b == 0 && shift != 0) return false;
            return true;
        }
        shift += 7;
    }
    return false; /* truncated */
}

namespace {

/* Length-prefixed byte field (varint length + raw bytes). Fixed-width integer
 * (de)serialization lives in byteorder.h. */
void put_bytes(std::string &out, const uint8_t *p, size_t len) {
    put_varint(out, len);
    if (len) out.append(reinterpret_cast<const char *>(p), len);
}

bool get_bytes(const uint8_t *&p, const uint8_t *end, std::string &out) {
    uint64_t len = 0;
    if (!get_varint(p, end, len)) return false;
    if ((uint64_t)(end - p) < len) return false;
    out.assign(reinterpret_cast<const char *>(p), (size_t)len);
    p += len;
    return true;
}

} // namespace

void encode_signing(const sync_change &c, std::string &out) {
    out.push_back((char)kCodecVersion);
    out.push_back((char)c.kind);
    put_bytes(out, c.ns, c.ns_len);
    put_bytes(out, c.entity, c.entity_len);
    if (c.kind == SYNC_CHANGE_EXISTENCE) {
        out.push_back((char)(c.causal_length ? 1 : 0)); /* present bit */
        put_u64le(out, c.hlc.physical);
        put_u32le(out, c.hlc.logical);
    } else { /* REGISTER */
        put_bytes(out, c.field, c.field_len);
        put_bytes(out, c.value, c.value_len);
        put_u64le(out, c.hlc.physical);
        put_u32le(out, c.hlc.logical);
    }
    out.append(reinterpret_cast<const char *>(c.author), SYNC_PUBKEY_LEN);
}

void encode_record(const sync_change &c, std::string &out) {
    /* Reserve once so the field appends below don't repeatedly regrow the
     * buffer (worst case: version+kind, two varints+ns+entity, field+value with
     * varints, hlc, author, signature). */
    out.reserve(out.size() + 4 + c.ns_len + c.entity_len + 5 + c.field_len + 5 +
                c.value_len + 12 + SYNC_PUBKEY_LEN + SYNC_SIG_LEN);
    encode_signing(c, out);
    out.append(reinterpret_cast<const char *>(c.signature), SYNC_SIG_LEN);
}

sync_change change_from_entity(const std::string &ns, const std::string &entity,
                               const Entity &en) {
    sync_change c;
    std::memset(&c, 0, sizeof c);
    c.kind = SYNC_CHANGE_EXISTENCE;
    c.ns = (const uint8_t *)ns.data();         c.ns_len = ns.size();
    c.entity = (const uint8_t *)entity.data(); c.entity_len = entity.size();
    c.causal_length = en.present_v ? 1 : 0; /* present bit */
    c.hlc.physical = en.presence_hlc.physical;
    c.hlc.logical = en.presence_hlc.logical;
    std::memcpy(c.author, en.ex_author.data(), SYNC_PUBKEY_LEN);
    std::memcpy(c.signature, en.ex_sig.data(), SYNC_SIG_LEN);
    return c;
}

sync_change change_from_register(const std::string &ns,
                                 const std::string &entity,
                                 const std::string &field, const Register &r) {
    sync_change c;
    std::memset(&c, 0, sizeof c);
    c.kind = SYNC_CHANGE_REGISTER;
    c.ns = (const uint8_t *)ns.data();         c.ns_len = ns.size();
    c.entity = (const uint8_t *)entity.data(); c.entity_len = entity.size();
    c.field = (const uint8_t *)field.data();   c.field_len = field.size();
    c.value = (const uint8_t *)r.value.data(); c.value_len = r.value.size();
    c.hlc.physical = r.hlc.physical;
    c.hlc.logical = r.hlc.logical;
    std::memcpy(c.author, r.author.data(), SYNC_PUBKEY_LEN);
    std::memcpy(c.signature, r.sig.data(), SYNC_SIG_LEN);
    return c;
}

Hash256 element_hash(const sync_change &c) {
    std::string rec;
    encode_record(c, rec);
    Hash256 out;
    sync_engine_detail::sha256(rec.data(), rec.size(), out.data());
    return out;
}

void element_hash(const std::string &signing_bytes,
                  const uint8_t sig[SYNC_SIG_LEN], Hash256 &out) {
    sync_engine_detail::Sha256 h;
    h.update(signing_bytes.data(), signing_bytes.size());
    h.update(sig, SYNC_SIG_LEN);
    h.finish(out.data());
}

bool decode_record(const uint8_t *buf, size_t len, DecodedChange &out,
                   size_t &consumed) {
    const uint8_t *p = buf;
    const uint8_t *end = buf + len;
    if (end - p < 2) return false;
    uint8_t ver = *p++;
    if (ver != kCodecVersion) return false;
    uint8_t kind = *p++;
    if (kind != SYNC_CHANGE_EXISTENCE && kind != SYNC_CHANGE_REGISTER)
        return false;
    out.kind = kind;
    if (!get_bytes(p, end, out.ns)) return false;
    if (!get_bytes(p, end, out.entity)) return false;
    if (kind == SYNC_CHANGE_EXISTENCE) {
        if (p >= end) return false;
        out.causal_length = (*p++ != 0) ? 1 : 0; /* present bit */
        if (!get_u64le(p, end, out.hlc.physical)) return false;
        if (!get_u32le(p, end, out.hlc.logical)) return false;
    } else {
        if (!get_bytes(p, end, out.field)) return false;
        if (!get_bytes(p, end, out.value)) return false;
        if (!get_u64le(p, end, out.hlc.physical)) return false;
        if (!get_u32le(p, end, out.hlc.logical)) return false;
    }
    if (end - p < (long)SYNC_PUBKEY_LEN) return false;
    std::memcpy(out.author.data(), p, SYNC_PUBKEY_LEN);
    p += SYNC_PUBKEY_LEN;
    if (end - p < (long)SYNC_SIG_LEN) return false;
    std::memcpy(out.signature.data(), p, SYNC_SIG_LEN);
    p += SYNC_SIG_LEN;
    consumed = (size_t)(p - buf);
    return true;
}

uint8_t *dup_field(const std::string &s, bool *oom) {
    if (s.empty()) return nullptr;
    uint8_t *p = static_cast<uint8_t *>(std::malloc(s.size()));
    if (!p) {
        *oom = true;
        return nullptr;
    }
    std::memcpy(p, s.data(), s.size());
    return p;
}

void free_change_fields(sync_change &c) {
    std::free(const_cast<uint8_t *>(c.ns));
    std::free(const_cast<uint8_t *>(c.entity));
    std::free(const_cast<uint8_t *>(c.field));
    std::free(const_cast<uint8_t *>(c.value));
    c.ns = c.entity = c.field = c.value = nullptr;
    c.ns_len = c.entity_len = c.field_len = c.value_len = 0;
}

sync_change DecodedChange::view() const {
    sync_change c;
    std::memset(&c, 0, sizeof c);
    c.kind = kind;
    c.ns = (const uint8_t *)ns.data();         c.ns_len = ns.size();
    c.entity = (const uint8_t *)entity.data();  c.entity_len = entity.size();
    c.field = (const uint8_t *)field.data();     c.field_len = field.size();
    c.value = (const uint8_t *)value.data();     c.value_len = value.size();
    c.causal_length = causal_length;
    c.hlc = hlc;
    std::memcpy(c.author, author.data(), SYNC_PUBKEY_LEN);
    std::memcpy(c.signature, signature.data(), SYNC_SIG_LEN);
    return c;
}

} // namespace ke

/* ---- Public codec ABI --------------------------------------------------- */

using namespace ke;

extern "C" {

size_t sync_change_encode(const sync_change *c, uint8_t *buf, size_t buf_len) {
    if (!c) return 0;
    if (c->kind != SYNC_CHANGE_EXISTENCE && c->kind != SYNC_CHANGE_REGISTER)
        return 0;
    try {
        std::string s;
        encode_record(*c, s);
        if (buf && buf_len >= s.size()) std::memcpy(buf, s.data(), s.size());
        return s.size();
    } catch (...) {
        return 0;
    }
}

int sync_change_decode(const uint8_t *buf, size_t len, sync_change *out,
                       size_t *consumed) {
    if (!buf || !out) return SYNC_ERR_INVALID;
    try {
        DecodedChange d;
        size_t used = 0;
        if (!decode_record(buf, len, d, used)) return SYNC_ERR_INVALID;

        std::memset(out, 0, sizeof *out);
        out->kind = d.kind;
        out->causal_length = d.causal_length;
        out->hlc = d.hlc;
        std::memcpy(out->author, d.author.data(), SYNC_PUBKEY_LEN);
        std::memcpy(out->signature, d.signature.data(), SYNC_SIG_LEN);

        /* Allocate owned copies (NULL for empty, freed by free_decoded). */
        bool oom = false;
        out->ns = dup_field(d.ns, &oom);         out->ns_len = d.ns.size();
        out->entity = dup_field(d.entity, &oom); out->entity_len = d.entity.size();
        out->field = dup_field(d.field, &oom);   out->field_len = d.field.size();
        out->value = dup_field(d.value, &oom);   out->value_len = d.value.size();
        if (oom) {
            sync_change_free_decoded(out);
            return SYNC_ERR_NOMEM;
        }
        if (consumed) *consumed = used;
        return SYNC_OK;
    } catch (...) {
        return SYNC_ERR_INTERNAL;
    }
}

int sync_change_sign(sync_change *c, const uint8_t *seed) {
    if (!c || !seed) return SYNC_ERR_INVALID;
    if (c->kind != SYNC_CHANGE_EXISTENCE && c->kind != SYNC_CHANGE_REGISTER)
        return SYNC_ERR_INVALID;
    try {
        KeyPair kp = keypair_from_seed(seed);
        std::memcpy(c->author, kp.sign_pk.data(), SYNC_PUBKEY_LEN);
        std::string signing;
        encode_signing(*c, signing);
        sign(kp.sign_sk.data(), signing.data(), signing.size(), c->signature);
        return SYNC_OK;
    } catch (...) {
        return SYNC_ERR_INTERNAL;
    }
}

void sync_change_free_decoded(sync_change *c) {
    if (c) free_change_fields(*c);
}

} // extern "C"
