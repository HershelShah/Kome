/* ws.cpp — RFC 6455 WebSocket transport (server + client). */
#include "transport/ws.h"

#include <cstring>

#include "crypto.h" /* random_bytes */

namespace ke {

namespace {

/* Cap the HTTP upgrade handshake so a peer can't grow it without bound. */
constexpr size_t kMaxHandshakeBytes = 1u << 20;

/* Cap a single frame's payload and a reassembled (fragmented) message. A peer
 * controls the 64-bit frame length, so without this the `hdr+masklen+len` size
 * math overflows (passing the buffered-enough check, then allocating ~2^64) and
 * continuation frames grow the reassembly buffer without bound. 64 MiB is well
 * above any real reconcile message (the UDP path is one ~64 KB datagram). */
constexpr size_t kMaxWsMessageBytes = 64u << 20;

/* ---- SHA-1 (for the Sec-WebSocket-Accept handshake only) --------------- */
struct Sha1 {
    uint32_t h[5];
    uint64_t len = 0;
    uint8_t buf[64];
    size_t n = 0;
    Sha1() { h[0]=0x67452301; h[1]=0xEFCDAB89; h[2]=0x98BADCFE; h[3]=0x10325476; h[4]=0xC3D2E1F0; }
    static uint32_t rol(uint32_t x, int c) { return (x << c) | (x >> (32 - c)); }
    void block(const uint8_t *p) {
        uint32_t w[80];
        for (int i = 0; i < 16; i++)
            w[i] = (uint32_t)p[i*4]<<24 | (uint32_t)p[i*4+1]<<16 | (uint32_t)p[i*4+2]<<8 | p[i*4+3];
        for (int i = 16; i < 80; i++) w[i] = rol(w[i-3]^w[i-8]^w[i-14]^w[i-16], 1);
        uint32_t a=h[0],b=h[1],c=h[2],d=h[3],e=h[4];
        for (int i = 0; i < 80; i++) {
            uint32_t f, k;
            if (i<20){f=(b&c)|(~b&d);k=0x5A827999;}
            else if (i<40){f=b^c^d;k=0x6ED9EBA1;}
            else if (i<60){f=(b&c)|(b&d)|(c&d);k=0x8F1BBCDC;}
            else {f=b^c^d;k=0xCA62C1D6;}
            uint32_t t = rol(a,5)+f+e+k+w[i];
            e=d; d=c; c=rol(b,30); b=a; a=t;
        }
        h[0]+=a; h[1]+=b; h[2]+=c; h[3]+=d; h[4]+=e;
    }
    void update(const void *data, size_t l) {
        const uint8_t *p = (const uint8_t *)data;
        len += l;
        while (l) { size_t t = 64 - n; if (t > l) t = l; std::memcpy(buf+n, p, t); n += t; p += t; l -= t; if (n == 64) { block(buf); n = 0; } }
    }
    void finish(uint8_t out[20]) {
        uint64_t bits = len * 8;
        uint8_t pad = 0x80; update(&pad, 1);
        uint8_t z = 0; while (n != 56) update(&z, 1);
        uint8_t lb[8]; for (int i = 0; i < 8; i++) lb[i] = (uint8_t)(bits >> (56 - i*8));
        update(lb, 8);
        for (int i = 0; i < 5; i++) { out[i*4]=h[i]>>24; out[i*4+1]=h[i]>>16; out[i*4+2]=h[i]>>8; out[i*4+3]=h[i]; }
    }
};

std::string base64(const uint8_t *p, size_t n) {
    static const char *t = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    std::string o;
    for (size_t i = 0; i < n; i += 3) {
        uint32_t v = p[i] << 16;
        if (i+1 < n) v |= p[i+1] << 8;
        if (i+2 < n) v |= p[i+2];
        o.push_back(t[(v>>18)&63]);
        o.push_back(t[(v>>12)&63]);
        o.push_back(i+1 < n ? t[(v>>6)&63] : '=');
        o.push_back(i+2 < n ? t[v&63] : '=');
    }
    return o;
}

const char *kGuid = "258EAFA5-E914-47DA-95CA-C5AB0DC85B11";

/* Case-insensitive search for a header value. */
std::string header(const std::string &req, const std::string &name) {
    std::string low = req, ln = name;
    for (auto &c : low) c = (char)tolower(c);
    for (auto &c : ln) c = (char)tolower(c);
    size_t pos = low.find(ln + ":");
    if (pos == std::string::npos) return "";
    pos += ln.size() + 1;
    size_t end = req.find("\r\n", pos);
    std::string v = req.substr(pos, end - pos);
    size_t b = v.find_first_not_of(" \t");
    size_t e = v.find_last_not_of(" \t\r\n");
    return (b == std::string::npos) ? "" : v.substr(b, e - b + 1);
}

bool read_until(TcpStream &tcp, std::string &buf, const char *delim, int timeout_ms) {
    while (buf.find(delim) == std::string::npos) {
        if (!tcp.recv_into(buf, timeout_ms)) return false;
        if (buf.size() > kMaxHandshakeBytes) return false; /* runaway handshake */
    }
    return true;
}

} // namespace

std::string ws_accept_key(const std::string &key) {
    Sha1 s;
    s.update(key.data(), key.size());
    s.update(kGuid, std::strlen(kGuid));
    uint8_t d[20];
    s.finish(d);
    return base64(d, 20);
}

bool WsStream::server_handshake(int timeout_ms) {
    is_client_ = false;
    if (!read_until(tcp, rx_, "\r\n\r\n", timeout_ms)) return false;
    size_t hend = rx_.find("\r\n\r\n");
    std::string req = rx_.substr(0, hend);
    rx_.erase(0, hend + 4); /* keep any frames that followed */

    std::string key = header(req, "Sec-WebSocket-Key");
    if (key.empty()) return false;
    std::string resp =
        "HTTP/1.1 101 Switching Protocols\r\n"
        "Upgrade: websocket\r\nConnection: Upgrade\r\n"
        "Sec-WebSocket-Accept: " + ws_accept_key(key) + "\r\n\r\n";
    return tcp.send_all(resp.data(), resp.size());
}

bool WsStream::client_handshake(const std::string &host, int timeout_ms) {
    is_client_ = true;
    uint8_t k[16];
    random_bytes(k, sizeof k);
    std::string key = base64(k, sizeof k);
    std::string req =
        "GET / HTTP/1.1\r\nHost: " + host + "\r\n"
        "Upgrade: websocket\r\nConnection: Upgrade\r\n"
        "Sec-WebSocket-Key: " + key + "\r\nSec-WebSocket-Version: 13\r\n\r\n";
    if (!tcp.send_all(req.data(), req.size())) return false;

    if (!read_until(tcp, rx_, "\r\n\r\n", timeout_ms)) return false;
    size_t hend = rx_.find("\r\n\r\n");
    std::string resp = rx_.substr(0, hend);
    rx_.erase(0, hend + 4);
    if (resp.find(" 101 ") == std::string::npos) return false;
    return header(resp, "Sec-WebSocket-Accept") == ws_accept_key(key);
}

bool WsStream::send_frame(const std::string &msg) {
    std::string f;
    f.push_back((char)0x82); /* FIN + binary opcode */
    uint64_t n = msg.size();
    uint8_t maskbit = is_client_ ? 0x80 : 0x00;
    if (n < 126) {
        f.push_back((char)(maskbit | n));
    } else if (n < 65536) {
        f.push_back((char)(maskbit | 126));
        f.push_back((char)(n >> 8)); f.push_back((char)(n & 0xff));
    } else {
        f.push_back((char)(maskbit | 127));
        for (int i = 7; i >= 0; i--) f.push_back((char)(n >> (i * 8)));
    }
    if (is_client_) {
        uint8_t mk[4];
        random_bytes(mk, 4);
        f.append((const char *)mk, 4);
        size_t off = f.size();
        f += msg;
        for (size_t i = 0; i < msg.size(); i++) f[off + i] ^= mk[i % 4];
    } else {
        f += msg;
    }
    return tcp.send_all(f.data(), f.size());
}

int ws_parse_frame(const uint8_t *buf, size_t len, bool &fin, uint8_t &op,
                   std::string &payload, size_t &consumed) {
    if (len < 2) return 0;
    fin = buf[0] & 0x80;
    op = buf[0] & 0x0f;
    bool masked = buf[1] & 0x80;
    uint64_t plen = buf[1] & 0x7f;
    size_t hdr = 2;
    if (plen == 126) {
        if (len < 4) return 0;
        plen = ((uint64_t)buf[2] << 8) | buf[3];
        hdr = 4;
    } else if (plen == 127) {
        if (len < 10) return 0;
        plen = 0;
        for (int i = 0; i < 8; i++) plen = (plen << 8) | buf[2 + i];
        hdr = 10;
    }
    /* Reject before the size math (hdr + masklen + plen) can overflow size_t. */
    if (plen > kMaxWsMessageBytes) return -1;
    /* RFC 6455 5.5: a control frame carries at most 125 payload bytes and is
     * never fragmented. Enforced HERE, at the decoder, rather than only at the
     * pong builder, for two reasons.
     *
     * The second header byte is MASK(1) || len(7), in which 126 and 127 are
     * RESERVED escapes ("a 16- or 64-bit length follows") and 0x80 means "a
     * 4-byte mask key follows". recv_frame echoes a ping by writing
     * `(char)(mb | payload.size())` into that byte, so an oversized ping does
     * not merely mis-frame the pong -- it MINTS those markers (a 126-byte ping
     * yields 0x7E, 128..255 sets MASK on a server->client frame, 256 yields
     * 0x00: a declared empty pong trailed by 256 unaccounted bytes) while the
     * body appended is the full payload. The peer's parser desynchronizes on
     * bytes we chose.
     *
     * And without a bound here a 64 MiB ping is buffered and echoed 1:1 through
     * TcpStream::send_all, which loops on EAGAIN with no overall deadline: an
     * unauthenticated peer that sends one and then stops reading stalls the
     * recv thread while we hold ~128 MiB. Rejecting at the decoder fixes both,
     * and puts the rule where fuzz_ws can reach it -- the fuzzer drives only
     * ws_parse_frame and never the pong emitter, which is why this survived. */
    if ((op & 0x8) && (plen > 125 || !fin)) return -1;
    size_t masklen = masked ? 4 : 0;
    if (len < hdr + masklen + plen) return 0;
    const uint8_t *mk = buf + hdr;
    payload.assign((const char *)buf + hdr + masklen, (size_t)plen);
    if (masked)
        for (size_t i = 0; i < payload.size(); i++) payload[i] ^= mk[i % 4];
    consumed = hdr + masklen + (size_t)plen;
    return 1;
}

bool WsStream::recv_frame(std::string &out, int timeout_ms) {
    for (;;) {
        bool fin = false;
        uint8_t op = 0;
        std::string payload;
        size_t consumed = 0;
        int r = ws_parse_frame((const uint8_t *)rx_.data(), rx_.size(), fin, op,
                               payload, consumed);
        if (r < 0) { /* oversized / malformed: drop the connection */
            tcp.close(); rx_.clear(); assembling_.clear();
            return false;
        }
        if (r == 0) { /* need more bytes from the socket */
            if (!tcp.recv_into(rx_, timeout_ms)) return false;
            continue;
        }
        rx_.erase(0, consumed);

        if (op == 0x8) return false; /* close */
        if (op == 0x9) {             /* ping -> pong */
            std::string pong;
            pong.push_back((char)0x8A);
            uint8_t mb = is_client_ ? 0x80 : 0x00;
            /* Belt-and-braces against the length byte above: ws_parse_frame
             * already refuses a control frame over 125 bytes, so `n` is a no-op
             * today. It stays so the declared length and the appended byte
             * count can never disagree -- and so the RESERVED 126/127 escapes
             * and the MASK bit can never be minted here -- even if the decoder
             * rule is later relaxed. */
            const size_t n = payload.size() > 125 ? 125 : payload.size();
            pong.push_back((char)(mb | (uint8_t)n));
            if (is_client_) {
                uint8_t m[4]; random_bytes(m, 4); pong.append((const char *)m, 4);
                for (size_t i = 0; i < n; i++)
                    pong.push_back(payload[i] ^ m[i % 4]);
            } else {
                pong.append(payload, 0, n);
            }
            tcp.send_all(pong.data(), pong.size());
            continue;
        }
        if (op == 0xA) continue; /* pong: ignore */

        /* data: 0x1 text, 0x2 binary, 0x0 continuation */
        if (op == 0x0) {
            if (assembling_.size() + payload.size() > kMaxWsMessageBytes) {
                tcp.close(); rx_.clear(); assembling_.clear();
                return false;
            }
            assembling_ += payload;
        } else {
            assembling_ = payload; assembling_op_ = op; in_message_ = true;
        }
        if (fin && in_message_) {
            out.swap(assembling_);
            assembling_.clear();
            in_message_ = false;
            return true;
        }
    }
}

} // namespace ke
