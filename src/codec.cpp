/* codec.cpp — canonical record serialization + public codec ABI (M3/M4). */
#include "codec.h"

#include <cstdlib>
#include <cstring>
#include <new>

#include "crypto.h"

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
        v |= (uint64_t)(b & 0x7f) << shift;
        if (!(b & 0x80)) return true;
        shift += 7;
    }
    return false; /* truncated */
}

namespace {

void put_u64le(std::string &out, uint64_t v) {
    for (int i = 0; i < 8; i++) out.push_back((char)(v >> (i * 8)));
}
void put_u32le(std::string &out, uint32_t v) {
    for (int i = 0; i < 4; i++) out.push_back((char)(v >> (i * 8)));
}
void put_bytes(std::string &out, const uint8_t *p, size_t len) {
    put_varint(out, len);
    if (len) out.append(reinterpret_cast<const char *>(p), len);
}

bool get_u64le(const uint8_t *&p, const uint8_t *end, uint64_t &v) {
    if (end - p < 8) return false;
    v = 0;
    for (int i = 0; i < 8; i++) v |= (uint64_t)p[i] << (i * 8);
    p += 8;
    return true;
}
bool get_u32le(const uint8_t *&p, const uint8_t *end, uint32_t &v) {
    if (end - p < 4) return false;
    v = 0;
    for (int i = 0; i < 4; i++) v |= (uint32_t)p[i] << (i * 8);
    p += 4;
    return true;
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
        put_u64le(out, c.causal_length);
    } else { /* REGISTER */
        put_bytes(out, c.field, c.field_len);
        put_bytes(out, c.value, c.value_len);
        put_u64le(out, c.hlc.physical);
        put_u32le(out, c.hlc.logical);
    }
    out.append(reinterpret_cast<const char *>(c.author), SYNC_PUBKEY_LEN);
}

void encode_record(const sync_change &c, std::string &out) {
    encode_signing(c, out);
    out.append(reinterpret_cast<const char *>(c.signature), SYNC_SIG_LEN);
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
        if (!get_u64le(p, end, out.causal_length)) return false;
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
        auto dup = [](const std::string &s, const uint8_t **dst,
                      size_t *dlen) -> bool {
            *dlen = s.size();
            if (s.empty()) {
                *dst = nullptr;
                return true;
            }
            uint8_t *m = (uint8_t *)std::malloc(s.size());
            if (!m) return false;
            std::memcpy(m, s.data(), s.size());
            *dst = m;
            return true;
        };
        if (!dup(d.ns, &out->ns, &out->ns_len) ||
            !dup(d.entity, &out->entity, &out->entity_len) ||
            !dup(d.field, &out->field, &out->field_len) ||
            !dup(d.value, &out->value, &out->value_len)) {
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
    if (!c) return;
    std::free(const_cast<uint8_t *>(c->ns));
    std::free(const_cast<uint8_t *>(c->entity));
    std::free(const_cast<uint8_t *>(c->field));
    std::free(const_cast<uint8_t *>(c->value));
    c->ns = c->entity = c->field = c->value = nullptr;
    c->ns_len = c->entity_len = c->field_len = c->value_len = 0;
}

} // extern "C"
