/* stun.cpp — minimal STUN Binding client/server helpers (M5). */
#include "transport/stun.h"

#include <arpa/inet.h>

#include <cstring>

#include "crypto.h"

namespace ke {

namespace {
constexpr uint16_t kBindingRequest = 0x0001;
constexpr uint16_t kBindingSuccess = 0x0101;
constexpr uint16_t kXorMappedAddress = 0x0020;

void put16(std::string &s, uint16_t v) {
    s.push_back((char)(v >> 8));
    s.push_back((char)(v & 0xff));
}
uint16_t get16(const uint8_t *p) { return (uint16_t)(p[0] << 8 | p[1]); }

void put_header(std::string &s, uint16_t type, uint16_t attr_len,
                const uint8_t txid[12]) {
    put16(s, type);
    put16(s, attr_len);
    uint32_t c = kStunMagicCookie;
    s.push_back((char)(c >> 24)); s.push_back((char)(c >> 16));
    s.push_back((char)(c >> 8));  s.push_back((char)c);
    s.append((const char *)txid, 12);
}
} // namespace

void stun_build_request(uint8_t txid[12], std::string &out) {
    random_bytes(txid, 12);
    out.clear();
    put_header(out, kBindingRequest, 0, txid);
}

bool stun_parse_request(const std::string &msg, uint8_t txid[12]) {
    if (msg.size() < 20) return false;
    const uint8_t *p = (const uint8_t *)msg.data();
    if (get16(p) != kBindingRequest) return false;
    std::memcpy(txid, p + 8, 12);
    return true;
}

void stun_build_response(const uint8_t txid[12], const Endpoint &mapped,
                         std::string &out) {
    /* XOR-MAPPED-ADDRESS attribute (IPv4): 0x0020, len 8. */
    std::string attr;
    put16(attr, kXorMappedAddress);
    put16(attr, 8);
    attr.push_back(0x00);            /* reserved */
    attr.push_back(0x01);            /* family IPv4 */
    uint16_t xport = (uint16_t)(mapped.port ^ (kStunMagicCookie >> 16));
    put16(attr, xport);
    in_addr a{};
    if (inet_pton(AF_INET, mapped.ip.c_str(), &a) != 1) a.s_addr = 0;
    uint32_t addr = ntohl(a.s_addr);
    uint32_t xaddr = addr ^ kStunMagicCookie;
    attr.push_back((char)(xaddr >> 24)); attr.push_back((char)(xaddr >> 16));
    attr.push_back((char)(xaddr >> 8));  attr.push_back((char)xaddr);

    out.clear();
    put_header(out, kBindingSuccess, (uint16_t)attr.size(), txid);
    out += attr;
}

bool stun_parse_response(const std::string &msg, const uint8_t txid[12],
                         Endpoint &mapped) {
    if (msg.size() < 20) return false;
    const uint8_t *p = (const uint8_t *)msg.data();
    if (get16(p) != kBindingSuccess) return false;
    if (std::memcmp(p + 8, txid, 12) != 0) return false;
    uint16_t attr_len = get16(p + 2);
    const uint8_t *a = p + 20;
    const uint8_t *end = a + attr_len;
    if (end > p + msg.size()) return false;
    while (a + 4 <= end) {
        uint16_t type = get16(a);
        uint16_t len = get16(a + 2);
        const uint8_t *val = a + 4;
        if (val + len > end) return false;
        if (type == kXorMappedAddress && len >= 8 && val[1] == 0x01) {
            uint16_t xport = get16(val + 2);
            uint16_t port = (uint16_t)(xport ^ (kStunMagicCookie >> 16));
            uint32_t xaddr = (uint32_t)val[4] << 24 | (uint32_t)val[5] << 16 |
                             (uint32_t)val[6] << 8 | val[7];
            uint32_t addr = xaddr ^ kStunMagicCookie;
            in_addr ia;
            ia.s_addr = htonl(addr);
            char ip[INET_ADDRSTRLEN];
            inet_ntop(AF_INET, &ia, ip, sizeof ip);
            mapped.ip = ip;
            mapped.port = port;
            return true;
        }
        a = val + len + ((4 - (len & 3)) & 3); /* 4-byte alignment */
    }
    return false;
}

} // namespace ke
