/* invite.cpp — invite encode/decode for invite-based discovery (M5).
 *
 * Wire form (versioned, little-endian):
 *   [1] version (1)
 *   [32] peer signing public key
 *   [varint] rendezvous address length, then the address bytes
 *   [1] has_capability flag
 *   if set: [varint] capability length, then the capability blob
 */
#include <cstdint>
#include <cstring>
#include <string>

#include "codec.h" /* ke::put_varint / ke::get_varint */
#include "sync_engine.h"

using namespace ke;

namespace {
constexpr uint8_t kInviteVersion = 1;
}

extern "C" {

size_t sync_invite_encode(const uint8_t peer_pubkey[SYNC_PUBKEY_LEN],
                          const char *rendezvous_addr,
                          const sync_capability *cap, uint8_t *buf,
                          size_t buf_len) {
    if (!peer_pubkey || !rendezvous_addr) return 0;
    try {
        std::string out;
        out.push_back((char)kInviteVersion);
        out.append((const char *)peer_pubkey, SYNC_PUBKEY_LEN);
        std::string addr(rendezvous_addr);
        put_varint(out, addr.size());
        out += addr;

        if (cap) {
            int clen = sync_capability_encode(cap, nullptr, 0);
            if (clen <= 0) return 0;
            std::string cb((size_t)clen, '\0');
            sync_capability_encode(cap, (uint8_t *)cb.data(), cb.size());
            out.push_back(1);
            put_varint(out, cb.size());
            out += cb;
        } else {
            out.push_back(0);
        }

        if (buf && buf_len >= out.size()) std::memcpy(buf, out.data(), out.size());
        return out.size();
    } catch (...) {
        return 0;
    }
}

int sync_invite_decode(const uint8_t *buf, size_t len,
                       uint8_t peer_pubkey[SYNC_PUBKEY_LEN], char *addr_out,
                       size_t addr_cap, sync_capability **cap_out) {
    if (!buf || !peer_pubkey || !addr_out) return SYNC_ERR_INVALID;
    if (cap_out) *cap_out = nullptr;
    try {
        const uint8_t *p = buf, *end = buf + len;
        if (p >= end || *p++ != kInviteVersion) return SYNC_ERR_INVALID;
        if (end - p < (long)SYNC_PUBKEY_LEN) return SYNC_ERR_INVALID;
        std::memcpy(peer_pubkey, p, SYNC_PUBKEY_LEN);
        p += SYNC_PUBKEY_LEN;

        uint64_t alen = 0;
        if (!get_varint(p, end, alen)) return SYNC_ERR_INVALID;
        if ((uint64_t)(end - p) < alen) return SYNC_ERR_INVALID;
        if (alen + 1 > addr_cap) return SYNC_ERR_INVALID; /* +1 for NUL */
        std::memcpy(addr_out, p, (size_t)alen);
        addr_out[alen] = '\0';
        p += alen;

        if (p >= end) return SYNC_ERR_INVALID;
        uint8_t has_cap = *p++;
        if (has_cap) {
            uint64_t clen = 0;
            if (!get_varint(p, end, clen)) return SYNC_ERR_INVALID;
            if ((uint64_t)(end - p) < clen) return SYNC_ERR_INVALID;
            sync_capability *c = sync_capability_decode(p, (size_t)clen);
            p += clen;
            if (!c) return SYNC_ERR_INVALID;
            if (cap_out) *cap_out = c;
            else sync_capability_free(c);
        }
        return SYNC_OK;
    } catch (...) {
        return SYNC_ERR_INTERNAL;
    }
}

} // extern "C"
