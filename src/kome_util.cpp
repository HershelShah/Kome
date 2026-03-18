#include "kome_util.hpp"
#include <chrono>
#include <cstring>
#include <vector>

namespace kome {

/* --------------------------------------------------------------------------
 * Standalone SHA-256 — based on FIPS 180-4
 *
 * Processes data incrementally per 64-byte block. No heap allocation for
 * the padding buffer — we handle the final block(s) specially.
 * ----------------------------------------------------------------------- */

static const uint32_t K256[64] = {
    0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
    0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
    0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
    0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
    0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
    0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
    0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
    0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2
};

static inline uint32_t rotr(uint32_t x, int n) { return (x >> n) | (x << (32 - n)); }
static inline uint32_t ch(uint32_t x, uint32_t y, uint32_t z) { return (x & y) ^ (~x & z); }
static inline uint32_t maj(uint32_t x, uint32_t y, uint32_t z) { return (x & y) ^ (x & z) ^ (y & z); }
static inline uint32_t sigma0(uint32_t x) { return rotr(x,2) ^ rotr(x,13) ^ rotr(x,22); }
static inline uint32_t sigma1(uint32_t x) { return rotr(x,6) ^ rotr(x,11) ^ rotr(x,25); }
static inline uint32_t gamma0(uint32_t x) { return rotr(x,7) ^ rotr(x,18) ^ (x >> 3); }
static inline uint32_t gamma1(uint32_t x) { return rotr(x,17) ^ rotr(x,19) ^ (x >> 10); }

static inline uint32_t load32be(const uint8_t *p) {
    return ((uint32_t)p[0] << 24) | ((uint32_t)p[1] << 16) |
           ((uint32_t)p[2] << 8)  | (uint32_t)p[3];
}

static inline void store32be(uint8_t *p, uint32_t v) {
    p[0] = (uint8_t)(v >> 24); p[1] = (uint8_t)(v >> 16);
    p[2] = (uint8_t)(v >> 8);  p[3] = (uint8_t)v;
}

static void sha256_compress(uint32_t h[8], const uint8_t block[64]) {
    uint32_t w[64];
    for (int i = 0; i < 16; i++)
        w[i] = load32be(block + i * 4);
    for (int i = 16; i < 64; i++)
        w[i] = gamma1(w[i-2]) + w[i-7] + gamma0(w[i-15]) + w[i-16];

    uint32_t a = h[0], b = h[1], c = h[2], d = h[3];
    uint32_t e = h[4], f = h[5], g = h[6], hh = h[7];

    for (int i = 0; i < 64; i++) {
        uint32_t t1 = hh + sigma1(e) + ch(e,f,g) + K256[i] + w[i];
        uint32_t t2 = sigma0(a) + maj(a,b,c);
        hh = g; g = f; f = e; e = d + t1;
        d = c; c = b; b = a; a = t1 + t2;
    }
    h[0] += a; h[1] += b; h[2] += c; h[3] += d;
    h[4] += e; h[5] += f; h[6] += g; h[7] += hh;
}

void sha256(const uint8_t *data, size_t len, uint8_t out[32]) {
    uint32_t h[8] = {
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
        0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
    };

    /* Process full 64-byte blocks directly from input — zero copy */
    size_t full_blocks = len / 64;
    for (size_t i = 0; i < full_blocks; i++)
        sha256_compress(h, data + i * 64);

    /* Final block(s): pad into a stack buffer (max 128 bytes) */
    size_t remaining = len - full_blocks * 64;
    uint8_t final_buf[128];
    std::memset(final_buf, 0, sizeof(final_buf));
    std::memcpy(final_buf, data + full_blocks * 64, remaining);
    final_buf[remaining] = 0x80;

    /* If remaining + 1 + 8 > 64, we need two final blocks */
    size_t final_blocks = (remaining + 9 > 64) ? 2 : 1;
    uint64_t bit_len = (uint64_t)len * 8;
    uint8_t *len_ptr = final_buf + final_blocks * 64 - 8;
    for (int i = 7; i >= 0; i--)
        len_ptr[i] = (uint8_t)(bit_len >> ((7 - i) * 8));

    for (size_t i = 0; i < final_blocks; i++)
        sha256_compress(h, final_buf + i * 64);

    for (int i = 0; i < 8; i++)
        store32be(out + i * 4, h[i]);
}

uint64_t timestamp_us() {
    auto now = std::chrono::system_clock::now();
    auto us = std::chrono::duration_cast<std::chrono::microseconds>(
        now.time_since_epoch());
    return static_cast<uint64_t>(us.count());
}

} /* namespace kome */
