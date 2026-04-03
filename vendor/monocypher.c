/*
 * Minimal Monocypher-compatible implementation — vendored for Kome
 *
 * Implements:
 *   - X25519 (RFC 7748) via Montgomery ladder on Curve25519
 *   - ChaCha20 (RFC 7539)
 *   - Poly1305 (RFC 7539)
 *   - ChaCha20-Poly1305 AEAD (RFC 7539)
 *   - crypto_wipe (volatile memset)
 *
 * Public domain (CC0).
 */
#include "monocypher.h"
#include <string.h>

/* =====================================================================
 * Secure wipe
 * ===================================================================== */

void crypto_wipe(void *secret, size_t size)
{
    volatile uint8_t *p = (volatile uint8_t *)secret;
    for (size_t i = 0; i < size; i++)
        p[i] = 0;
}

/* =====================================================================
 * ChaCha20  (RFC 7539)
 * ===================================================================== */

static uint32_t load32_le(const uint8_t *p)
{
    return (uint32_t)p[0]
        | ((uint32_t)p[1] <<  8)
        | ((uint32_t)p[2] << 16)
        | ((uint32_t)p[3] << 24);
}

static void store32_le(uint8_t *p, uint32_t v)
{
    p[0] = (uint8_t)(v      );
    p[1] = (uint8_t)(v >>  8);
    p[2] = (uint8_t)(v >> 16);
    p[3] = (uint8_t)(v >> 24);
}

static uint32_t rotl32(uint32_t x, int n)
{
    return (x << n) | (x >> (32 - n));
}

#define QR(a, b, c, d)           \
    a += b; d ^= a; d = rotl32(d, 16); \
    c += d; b ^= c; b = rotl32(b, 12); \
    a += b; d ^= a; d = rotl32(d,  8); \
    c += d; b ^= c; b = rotl32(b,  7)

static void chacha20_block(uint32_t out[16], const uint32_t in[16])
{
    uint32_t x[16];
    memcpy(x, in, 64);

    for (int i = 0; i < 10; i++) {
        /* Column rounds */
        QR(x[0], x[4], x[ 8], x[12]);
        QR(x[1], x[5], x[ 9], x[13]);
        QR(x[2], x[6], x[10], x[14]);
        QR(x[3], x[7], x[11], x[15]);
        /* Diagonal rounds */
        QR(x[0], x[5], x[10], x[15]);
        QR(x[1], x[6], x[11], x[12]);
        QR(x[2], x[7], x[ 8], x[13]);
        QR(x[3], x[4], x[ 9], x[14]);
    }

    for (int i = 0; i < 16; i++)
        out[i] = x[i] + in[i];
}

/*
 * chacha20_xor: XOR plaintext with ChaCha20 key stream.
 *   key   : 32 bytes
 *   nonce : 12 bytes  (RFC 7539 nonce)
 *   counter: initial block counter
 */
static void chacha20_xor(uint8_t *out, const uint8_t *in, size_t len,
                          const uint8_t key[32], const uint8_t nonce[12],
                          uint32_t counter)
{
    uint32_t state[16];
    /* "expand 32-byte k" */
    state[0]  = 0x61707865;
    state[1]  = 0x3320646e;
    state[2]  = 0x79622d32;
    state[3]  = 0x6b206574;

    for (int i = 0; i < 8; i++)
        state[4 + i] = load32_le(key + 4 * i);

    state[12] = counter;
    state[13] = load32_le(nonce + 0);
    state[14] = load32_le(nonce + 4);
    state[15] = load32_le(nonce + 8);

    while (len > 0) {
        uint32_t block[16];
        chacha20_block(block, state);

        uint8_t keystream[64];
        for (int i = 0; i < 16; i++)
            store32_le(keystream + 4 * i, block[i]);

        size_t chunk = len < 64 ? len : 64;
        for (size_t i = 0; i < chunk; i++)
            out[i] = in[i] ^ keystream[i];

        state[12]++;
        out += chunk;
        in  += chunk;
        len -= chunk;
    }
}

/* =====================================================================
 * Poly1305  (RFC 7539)
 * ===================================================================== */

typedef struct {
    uint32_t r[5];   /* clamped r, split into 26-bit limbs */
    uint32_t h[5];   /* accumulator */
    uint32_t pad[4]; /* one-time pad s */
} poly1305_ctx;

static void poly1305_init(poly1305_ctx *ctx, const uint8_t key[32])
{
    /* r = key[0..15], clamped */
    uint32_t t0 = load32_le(key +  0);
    uint32_t t1 = load32_le(key +  4);
    uint32_t t2 = load32_le(key +  8);
    uint32_t t3 = load32_le(key + 12);

    ctx->r[0] =  t0                        & 0x3ffffff;
    ctx->r[1] = ((t0 >> 26) | (t1 <<  6)) & 0x3ffff03;
    ctx->r[2] = ((t1 >> 20) | (t2 << 12)) & 0x3ffc0ff;
    ctx->r[3] = ((t2 >> 14) | (t3 << 18)) & 0x3f03fff;
    ctx->r[4] =  (t3 >>  8)               & 0x00fffff;

    /* h = 0 */
    ctx->h[0] = 0;
    ctx->h[1] = 0;
    ctx->h[2] = 0;
    ctx->h[3] = 0;
    ctx->h[4] = 0;

    /* s = key[16..31] */
    ctx->pad[0] = load32_le(key + 16);
    ctx->pad[1] = load32_le(key + 20);
    ctx->pad[2] = load32_le(key + 24);
    ctx->pad[3] = load32_le(key + 28);
}

static void poly1305_block(poly1305_ctx *ctx, const uint8_t *msg,
                            size_t len, uint32_t hibit)
{
    while (len > 0) {
        size_t chunk = len < 16 ? len : 16;
        uint8_t block[17];
        memset(block, 0, sizeof(block));
        memcpy(block, msg, chunk);
        block[chunk] = 1; /* hibit */

        /* If this is the final partial block, hibit controls the 2^128 bit */
        uint32_t t0 = load32_le(block + 0);
        uint32_t t1 = load32_le(block + 4);
        uint32_t t2 = load32_le(block + 8);
        uint32_t t3 = load32_le(block + 12);

        ctx->h[0] +=  t0                        & 0x3ffffff;
        ctx->h[1] += ((t0 >> 26) | (t1 <<  6)) & 0x3ffffff;
        ctx->h[2] += ((t1 >> 20) | (t2 << 12)) & 0x3ffffff;
        ctx->h[3] += ((t2 >> 14) | (t3 << 18)) & 0x3ffffff;
        ctx->h[4] +=  (t3 >>  8)               | (hibit << 24);

        /* Multiply h by r */
        uint64_t s1 = ctx->r[1] * 5;
        uint64_t s2 = ctx->r[2] * 5;
        uint64_t s3 = ctx->r[3] * 5;
        uint64_t s4 = ctx->r[4] * 5;

        uint64_t d0 = (uint64_t)ctx->h[0] * ctx->r[0]
                     + (uint64_t)ctx->h[1] * s4
                     + (uint64_t)ctx->h[2] * s3
                     + (uint64_t)ctx->h[3] * s2
                     + (uint64_t)ctx->h[4] * s1;
        uint64_t d1 = (uint64_t)ctx->h[0] * ctx->r[1]
                     + (uint64_t)ctx->h[1] * ctx->r[0]
                     + (uint64_t)ctx->h[2] * s4
                     + (uint64_t)ctx->h[3] * s3
                     + (uint64_t)ctx->h[4] * s2;
        uint64_t d2 = (uint64_t)ctx->h[0] * ctx->r[2]
                     + (uint64_t)ctx->h[1] * ctx->r[1]
                     + (uint64_t)ctx->h[2] * ctx->r[0]
                     + (uint64_t)ctx->h[3] * s4
                     + (uint64_t)ctx->h[4] * s3;
        uint64_t d3 = (uint64_t)ctx->h[0] * ctx->r[3]
                     + (uint64_t)ctx->h[1] * ctx->r[2]
                     + (uint64_t)ctx->h[2] * ctx->r[1]
                     + (uint64_t)ctx->h[3] * ctx->r[0]
                     + (uint64_t)ctx->h[4] * s4;
        uint64_t d4 = (uint64_t)ctx->h[0] * ctx->r[4]
                     + (uint64_t)ctx->h[1] * ctx->r[3]
                     + (uint64_t)ctx->h[2] * ctx->r[2]
                     + (uint64_t)ctx->h[3] * ctx->r[1]
                     + (uint64_t)ctx->h[4] * ctx->r[0];

        /* Partial reduction modulo 2^130 - 5 */
        uint32_t c;
        c = (uint32_t)(d0 >> 26); ctx->h[0] = (uint32_t)d0 & 0x3ffffff; d1 += c;
        c = (uint32_t)(d1 >> 26); ctx->h[1] = (uint32_t)d1 & 0x3ffffff; d2 += c;
        c = (uint32_t)(d2 >> 26); ctx->h[2] = (uint32_t)d2 & 0x3ffffff; d3 += c;
        c = (uint32_t)(d3 >> 26); ctx->h[3] = (uint32_t)d3 & 0x3ffffff; d4 += c;
        c = (uint32_t)(d4 >> 26); ctx->h[4] = (uint32_t)d4 & 0x3ffffff;
        ctx->h[0] += c * 5;
        c = ctx->h[0] >> 26; ctx->h[0] &= 0x3ffffff;
        ctx->h[1] += c;

        msg += chunk;
        len -= chunk;
    }
}

static void poly1305_finish(poly1305_ctx *ctx, uint8_t mac[16])
{
    /* Final reduction */
    uint32_t c;
    c = ctx->h[1] >> 26; ctx->h[1] &= 0x3ffffff; ctx->h[2] += c;
    c = ctx->h[2] >> 26; ctx->h[2] &= 0x3ffffff; ctx->h[3] += c;
    c = ctx->h[3] >> 26; ctx->h[3] &= 0x3ffffff; ctx->h[4] += c;
    c = ctx->h[4] >> 26; ctx->h[4] &= 0x3ffffff; ctx->h[0] += c * 5;
    c = ctx->h[0] >> 26; ctx->h[0] &= 0x3ffffff; ctx->h[1] += c;

    /* Compute h + -(2^130 - 5) = h - p */
    uint32_t g0 = ctx->h[0] + 5; c = g0 >> 26; g0 &= 0x3ffffff;
    uint32_t g1 = ctx->h[1] + c; c = g1 >> 26; g1 &= 0x3ffffff;
    uint32_t g2 = ctx->h[2] + c; c = g2 >> 26; g2 &= 0x3ffffff;
    uint32_t g3 = ctx->h[3] + c; c = g3 >> 26; g3 &= 0x3ffffff;
    uint32_t g4 = ctx->h[4] + c - (1u << 26);

    /* Select h or h-p based on whether h >= p */
    uint32_t mask = (g4 >> 31) - 1; /* 0 if g4 < 0 (h < p), all-1s if h >= p */
    g0 &= mask;
    g1 &= mask;
    g2 &= mask;
    g3 &= mask;
    g4 &= mask;
    mask = ~mask;
    ctx->h[0] = (ctx->h[0] & mask) | g0;
    ctx->h[1] = (ctx->h[1] & mask) | g1;
    ctx->h[2] = (ctx->h[2] & mask) | g2;
    ctx->h[3] = (ctx->h[3] & mask) | g3;
    ctx->h[4] = (ctx->h[4] & mask) | g4;

    /* Assemble h into 4 x 32-bit words */
    uint64_t f;
    f = (uint64_t)ctx->h[0] | ((uint64_t)ctx->h[1] << 26);
    uint32_t h0 = (uint32_t)f;
    f = ((uint64_t)ctx->h[1] >> 6) | ((uint64_t)ctx->h[2] << 20);
    uint32_t h1 = (uint32_t)f;
    f = ((uint64_t)ctx->h[2] >> 12) | ((uint64_t)ctx->h[3] << 14);
    uint32_t h2 = (uint32_t)f;
    f = ((uint64_t)ctx->h[3] >> 18) | ((uint64_t)ctx->h[4] <<  8);
    uint32_t h3 = (uint32_t)f;

    /* h = h + s */
    uint64_t t;
    t = (uint64_t)h0 + ctx->pad[0];             h0 = (uint32_t)t;
    t = (uint64_t)h1 + ctx->pad[1] + (t >> 32); h1 = (uint32_t)t;
    t = (uint64_t)h2 + ctx->pad[2] + (t >> 32); h2 = (uint32_t)t;
    t = (uint64_t)h3 + ctx->pad[3] + (t >> 32); h3 = (uint32_t)t;

    store32_le(mac +  0, h0);
    store32_le(mac +  4, h1);
    store32_le(mac +  8, h2);
    store32_le(mac + 12, h3);
}

/* =====================================================================
 * ChaCha20-Poly1305 AEAD  (RFC 7539 Section 2.8)
 * ===================================================================== */

/*
 * Build a 12-byte RFC-7539 nonce from the 8-byte "Monocypher" nonce:
 *   nonce12 = [0x00, 0x00, 0x00, 0x00, nonce[0..7]]
 */
static void build_nonce12(uint8_t nonce12[12], const uint8_t nonce[8])
{
    memset(nonce12, 0, 4);
    memcpy(nonce12 + 4, nonce, 8);
}

static void pad16(poly1305_ctx *ctx, size_t len)
{
    size_t rem = len & 15;
    if (rem) {
        uint8_t zeros[16];
        memset(zeros, 0, 16);
        poly1305_block(ctx, zeros, 16 - rem, 1);
    }
}

void crypto_aead_lock(uint8_t        mac[16],
                      uint8_t       *cipher_text,
                      const uint8_t  key[32],
                      const uint8_t  nonce[8],
                      const uint8_t *ad,        size_t ad_size,
                      const uint8_t *plain_text, size_t text_size)
{
    uint8_t nonce12[12];
    build_nonce12(nonce12, nonce);

    /* Generate Poly1305 key: first 32 bytes of ChaCha20 block 0 */
    uint8_t poly_key[64];
    memset(poly_key, 0, 64);
    chacha20_xor(poly_key, poly_key, 64, key, nonce12, 0);

    /* Encrypt with counter starting at 1 */
    chacha20_xor(cipher_text, plain_text, text_size, key, nonce12, 1);

    /* Compute MAC over: AD || pad || ciphertext || pad || len(AD) || len(CT) */
    poly1305_ctx pctx;
    poly1305_init(&pctx, poly_key);

    if (ad && ad_size > 0)
        poly1305_block(&pctx, ad, ad_size, 1);
    pad16(&pctx, ad_size);

    if (text_size > 0)
        poly1305_block(&pctx, cipher_text, text_size, 1);
    pad16(&pctx, text_size);

    uint8_t lens[16];
    store32_le(lens + 0, (uint32_t)(ad_size));
    store32_le(lens + 4, (uint32_t)(ad_size >> 32));
    store32_le(lens + 8, (uint32_t)(text_size));
    store32_le(lens + 12, (uint32_t)(text_size >> 32));
    poly1305_block(&pctx, lens, 16, 1);

    poly1305_finish(&pctx, mac);
    crypto_wipe(poly_key, 64);
}

int crypto_aead_unlock(uint8_t       *plain_text,
                       const uint8_t  key[32],
                       const uint8_t  nonce[8],
                       const uint8_t  mac[16],
                       const uint8_t *ad,         size_t ad_size,
                       const uint8_t *cipher_text, size_t text_size)
{
    uint8_t nonce12[12];
    build_nonce12(nonce12, nonce);

    /* Generate Poly1305 key */
    uint8_t poly_key[64];
    memset(poly_key, 0, 64);
    chacha20_xor(poly_key, poly_key, 64, key, nonce12, 0);

    /* Verify MAC first */
    poly1305_ctx pctx;
    poly1305_init(&pctx, poly_key);

    if (ad && ad_size > 0)
        poly1305_block(&pctx, ad, ad_size, 1);
    pad16(&pctx, ad_size);

    if (text_size > 0)
        poly1305_block(&pctx, cipher_text, text_size, 1);
    pad16(&pctx, text_size);

    uint8_t lens[16];
    store32_le(lens + 0, (uint32_t)(ad_size));
    store32_le(lens + 4, (uint32_t)(ad_size >> 32));
    store32_le(lens + 8, (uint32_t)(text_size));
    store32_le(lens + 12, (uint32_t)(text_size >> 32));
    poly1305_block(&pctx, lens, 16, 1);

    uint8_t computed_mac[16];
    poly1305_finish(&pctx, computed_mac);
    crypto_wipe(poly_key, 64);

    /* Constant-time comparison */
    volatile uint8_t diff = 0;
    for (int i = 0; i < 16; i++)
        diff |= computed_mac[i] ^ mac[i];

    if (diff != 0)
        return -1;

    /* Decrypt */
    chacha20_xor(plain_text, cipher_text, text_size, key, nonce12, 1);
    return 0;
}

/* =====================================================================
 * X25519  (RFC 7748 — Curve25519 Diffie-Hellman)
 *
 * Field arithmetic modulo p = 2^255 - 19.
 * Representation: 5 x uint64_t limbs, each up to ~51 bits.
 * Montgomery ladder for scalar multiplication.
 * ===================================================================== */

typedef uint64_t fe[5]; /* field element: 5 limbs of ~51 bits */

/* 2^51 */
#define FE_LIMB_BITS 51
#define FE_LIMB_MASK ((UINT64_C(1) << FE_LIMB_BITS) - 1)

static void fe_0(fe h) { h[0]=h[1]=h[2]=h[3]=h[4]=0; }
static void fe_1(fe h) { h[0]=1; h[1]=h[2]=h[3]=h[4]=0; }

static void fe_copy(fe h, const fe f) {
    h[0]=f[0]; h[1]=f[1]; h[2]=f[2]; h[3]=f[3]; h[4]=f[4];
}

static void fe_add(fe h, const fe f, const fe g) {
    h[0] = f[0] + g[0];
    h[1] = f[1] + g[1];
    h[2] = f[2] + g[2];
    h[3] = f[3] + g[3];
    h[4] = f[4] + g[4];
}

static void fe_sub(fe h, const fe f, const fe g) {
    /* Add 2*p to avoid underflow */
    h[0] = f[0] + UINT64_C(0xFFFFFFFFFFFDA) - g[0];
    h[1] = f[1] + UINT64_C(0xFFFFFFFFFFFFE) - g[1];
    h[2] = f[2] + UINT64_C(0xFFFFFFFFFFFFE) - g[2];
    h[3] = f[3] + UINT64_C(0xFFFFFFFFFFFFE) - g[3];
    h[4] = f[4] + UINT64_C(0xFFFFFFFFFFFFE) - g[4];
}

static void fe_carry(fe h) {
    uint64_t c;
    c = h[0] >> FE_LIMB_BITS; h[1] += c; h[0] &= FE_LIMB_MASK;
    c = h[1] >> FE_LIMB_BITS; h[2] += c; h[1] &= FE_LIMB_MASK;
    c = h[2] >> FE_LIMB_BITS; h[3] += c; h[2] &= FE_LIMB_MASK;
    c = h[3] >> FE_LIMB_BITS; h[4] += c; h[3] &= FE_LIMB_MASK;
    c = h[4] >> FE_LIMB_BITS; h[0] += c * 19; h[4] &= FE_LIMB_MASK;
    /* One more carry from h[0] in case c*19 overflowed */
    c = h[0] >> FE_LIMB_BITS; h[1] += c; h[0] &= FE_LIMB_MASK;
}

/*
 * Multiplication using 128-bit intermediates.
 * GCC / Clang provide __uint128_t on 64-bit targets.
 */
#ifdef __SIZEOF_INT128__
typedef unsigned __int128 uint128_t;
#else
/* Fallback: use two uint64_t. Only needed on 32-bit targets, which we
 * don't officially support, but let's keep it compiling. */
#error "128-bit integer support required for X25519"
#endif

static void fe_mul(fe h, const fe f, const fe g)
{
    const uint64_t m19 = 19;
    uint128_t t0, t1, t2, t3, t4;

    t0 =  (uint128_t)f[0]*g[0]
        + (uint128_t)f[1]*g[4]*m19
        + (uint128_t)f[2]*g[3]*m19
        + (uint128_t)f[3]*g[2]*m19
        + (uint128_t)f[4]*g[1]*m19;

    t1 =  (uint128_t)f[0]*g[1]
        + (uint128_t)f[1]*g[0]
        + (uint128_t)f[2]*g[4]*m19
        + (uint128_t)f[3]*g[3]*m19
        + (uint128_t)f[4]*g[2]*m19;

    t2 =  (uint128_t)f[0]*g[2]
        + (uint128_t)f[1]*g[1]
        + (uint128_t)f[2]*g[0]
        + (uint128_t)f[3]*g[4]*m19
        + (uint128_t)f[4]*g[3]*m19;

    t3 =  (uint128_t)f[0]*g[3]
        + (uint128_t)f[1]*g[2]
        + (uint128_t)f[2]*g[1]
        + (uint128_t)f[3]*g[0]
        + (uint128_t)f[4]*g[4]*m19;

    t4 =  (uint128_t)f[0]*g[4]
        + (uint128_t)f[1]*g[3]
        + (uint128_t)f[2]*g[2]
        + (uint128_t)f[3]*g[1]
        + (uint128_t)f[4]*g[0];

    /* Carry chain */
    uint64_t c;
    h[0] = (uint64_t)t0 & FE_LIMB_MASK; c = (uint64_t)(t0 >> FE_LIMB_BITS);
    t1 += c;
    h[1] = (uint64_t)t1 & FE_LIMB_MASK; c = (uint64_t)(t1 >> FE_LIMB_BITS);
    t2 += c;
    h[2] = (uint64_t)t2 & FE_LIMB_MASK; c = (uint64_t)(t2 >> FE_LIMB_BITS);
    t3 += c;
    h[3] = (uint64_t)t3 & FE_LIMB_MASK; c = (uint64_t)(t3 >> FE_LIMB_BITS);
    t4 += c;
    h[4] = (uint64_t)t4 & FE_LIMB_MASK; c = (uint64_t)(t4 >> FE_LIMB_BITS);
    h[0] += c * 19;
    c = h[0] >> FE_LIMB_BITS; h[1] += c; h[0] &= FE_LIMB_MASK;
}

static void fe_sq(fe h, const fe f)
{
    fe_mul(h, f, f);
}

/* Multiply by small constant 121666 (for the a24 parameter) */
static void fe_mul121666(fe h, const fe f)
{
    uint128_t t;
    uint64_t c;

    t = (uint128_t)f[0] * 121666; h[0] = (uint64_t)t & FE_LIMB_MASK; c = (uint64_t)(t >> FE_LIMB_BITS);
    t = (uint128_t)f[1] * 121666 + c; h[1] = (uint64_t)t & FE_LIMB_MASK; c = (uint64_t)(t >> FE_LIMB_BITS);
    t = (uint128_t)f[2] * 121666 + c; h[2] = (uint64_t)t & FE_LIMB_MASK; c = (uint64_t)(t >> FE_LIMB_BITS);
    t = (uint128_t)f[3] * 121666 + c; h[3] = (uint64_t)t & FE_LIMB_MASK; c = (uint64_t)(t >> FE_LIMB_BITS);
    t = (uint128_t)f[4] * 121666 + c; h[4] = (uint64_t)t & FE_LIMB_MASK; c = (uint64_t)(t >> FE_LIMB_BITS);
    h[0] += c * 19;
    c = h[0] >> FE_LIMB_BITS; h[1] += c; h[0] &= FE_LIMB_MASK;
}

/* Conditional swap: swap f and g if b == 1, no-op if b == 0 */
static void fe_cswap(fe f, fe g, uint64_t b)
{
    uint64_t mask = -(uint64_t)b; /* 0 or 0xFFFFFFFFFFFFFFFF */
    for (int i = 0; i < 5; i++) {
        uint64_t t = mask & (f[i] ^ g[i]);
        f[i] ^= t;
        g[i] ^= t;
    }
}

/* Load 32 bytes (little-endian) into a field element */
static void fe_frombytes(fe h, const uint8_t s[32])
{
    uint64_t lo;
    lo  = (uint64_t)s[0];
    lo |= (uint64_t)s[1]  <<  8;
    lo |= (uint64_t)s[2]  << 16;
    lo |= (uint64_t)s[3]  << 24;
    lo |= (uint64_t)s[4]  << 32;
    lo |= (uint64_t)s[5]  << 40;
    lo |= (uint64_t)s[6]  << 48;
    h[0] = lo & FE_LIMB_MASK;

    lo  = (uint64_t)s[6]  >>  3;
    lo |= (uint64_t)s[7]  <<  5;
    lo |= (uint64_t)s[8]  << 13;
    lo |= (uint64_t)s[9]  << 21;
    lo |= (uint64_t)s[10] << 29;
    lo |= (uint64_t)s[11] << 37;
    lo |= (uint64_t)s[12] << 45;
    h[1] = lo & FE_LIMB_MASK;

    lo  = (uint64_t)s[12] >>  6;
    lo |= (uint64_t)s[13] <<  2;
    lo |= (uint64_t)s[14] << 10;
    lo |= (uint64_t)s[15] << 18;
    lo |= (uint64_t)s[16] << 26;
    lo |= (uint64_t)s[17] << 34;
    lo |= (uint64_t)s[18] << 42;
    lo |= (uint64_t)s[19] << 50;
    h[2] = lo & FE_LIMB_MASK;

    lo  = (uint64_t)s[19] >>  1;
    lo |= (uint64_t)s[20] <<  7;
    lo |= (uint64_t)s[21] << 15;
    lo |= (uint64_t)s[22] << 23;
    lo |= (uint64_t)s[23] << 31;
    lo |= (uint64_t)s[24] << 39;
    lo |= (uint64_t)s[25] << 47;
    h[3] = lo & FE_LIMB_MASK;

    lo  = (uint64_t)s[25] >>  4;
    lo |= (uint64_t)s[26] <<  4;
    lo |= (uint64_t)s[27] << 12;
    lo |= (uint64_t)s[28] << 20;
    lo |= (uint64_t)s[29] << 28;
    lo |= (uint64_t)s[30] << 36;
    lo |= (uint64_t)s[31] << 44;
    h[4] = lo & FE_LIMB_MASK;
}

/* Store a fully-reduced field element to 32 bytes (little-endian) */
static void fe_tobytes(uint8_t s[32], const fe h_in)
{
    fe h;
    fe_copy(h, h_in);
    fe_carry(h);

    /* Full reduction: if h >= p, subtract p */
    /* Compute q = (h + 19) >> 255 */
    uint64_t q = (h[0] + 19) >> FE_LIMB_BITS;
    q = (h[1] + q) >> FE_LIMB_BITS;
    q = (h[2] + q) >> FE_LIMB_BITS;
    q = (h[3] + q) >> FE_LIMB_BITS;
    q = (h[4] + q) >> FE_LIMB_BITS;
    /* q is 0 or 1 */

    h[0] += 19 * q;
    uint64_t c;
    c = h[0] >> FE_LIMB_BITS; h[1] += c; h[0] &= FE_LIMB_MASK;
    c = h[1] >> FE_LIMB_BITS; h[2] += c; h[1] &= FE_LIMB_MASK;
    c = h[2] >> FE_LIMB_BITS; h[3] += c; h[2] &= FE_LIMB_MASK;
    c = h[3] >> FE_LIMB_BITS; h[4] += c; h[3] &= FE_LIMB_MASK;
    h[4] &= FE_LIMB_MASK;

    /* Pack 5 * 51 bits = 255 bits into 32 bytes, little-endian */
    uint64_t bits;

    /* bytes 0..6:  h[0] (51 bits) */
    bits = h[0];
    s[0]  = (uint8_t)(bits);       s[1] = (uint8_t)(bits >>  8);
    s[2]  = (uint8_t)(bits >> 16); s[3] = (uint8_t)(bits >> 24);
    s[4]  = (uint8_t)(bits >> 32); s[5] = (uint8_t)(bits >> 40);

    /* bytes 6..12: h[1] (shifted left by 51 - 48 = 3 within byte 6) */
    bits = (h[0] >> 48) | (h[1] << 3);
    s[6]  = (uint8_t)(bits);       s[7]  = (uint8_t)(bits >>  8);
    s[8]  = (uint8_t)(bits >> 16); s[9]  = (uint8_t)(bits >> 24);
    s[10] = (uint8_t)(bits >> 32); s[11] = (uint8_t)(bits >> 40);

    /* bytes 12..19: h[2] (shifted left by 102 - 96 = 6 within byte 12) */
    bits = (h[1] >> 45) | (h[2] << 6);
    s[12] = (uint8_t)(bits);       s[13] = (uint8_t)(bits >>  8);
    s[14] = (uint8_t)(bits >> 16); s[15] = (uint8_t)(bits >> 24);
    s[16] = (uint8_t)(bits >> 32); s[17] = (uint8_t)(bits >> 40);
    s[18] = (uint8_t)(bits >> 48);

    /* bytes 19..25: h[3] (shifted left by 153 - 152 = 1 within byte 19) */
    bits = (h[2] >> 42) | (h[3] << 1);
    /* Actually: bit 153 starts at byte 19 bit 1. But let's be more precise. */
    /* h[3] contributes bits [153..203]. Byte 19 starts at bit 152. */
    /* So within byte 19, h[3] starts at bit offset 1 */
    /* We already have the high bits of h[2] in byte 19 bit 0 */
    bits = (h[3] << 1) | (h[2] >> 50);
    s[19] = (uint8_t)(bits);       s[20] = (uint8_t)(bits >>  8);
    s[21] = (uint8_t)(bits >> 16); s[22] = (uint8_t)(bits >> 24);
    s[23] = (uint8_t)(bits >> 32); s[24] = (uint8_t)(bits >> 40);

    /* bytes 25..31: h[4] (shifted left by 204 - 200 = 4 within byte 25) */
    bits = (h[3] >> 47) | (h[4] << 4);
    s[25] = (uint8_t)(bits);       s[26] = (uint8_t)(bits >>  8);
    s[27] = (uint8_t)(bits >> 16); s[28] = (uint8_t)(bits >> 24);
    s[29] = (uint8_t)(bits >> 32); s[30] = (uint8_t)(bits >> 40);
    s[31] = (uint8_t)(bits >> 48);
}

/* Modular inversion: h = f^(-1) mod p = f^(p-2) mod p using Fermat.
 * p-2 = 2^255 - 21
 * Uses the addition chain from ref10 (donna) */
static void fe_invert(fe out, const fe z)
{
    fe t0, t1, t2, t3;
    int i;

    fe_sq(t0, z);          /* t0 = z^2 */
    fe_sq(t1, t0);
    fe_sq(t1, t1);         /* t1 = z^8 */
    fe_mul(t1, z, t1);     /* t1 = z^9 */
    fe_mul(t0, t0, t1);    /* t0 = z^11 */
    fe_sq(t2, t0);         /* t2 = z^22 */
    fe_mul(t1, t1, t2);    /* t1 = z^(2^5 - 1) = z^31 */

    fe_sq(t2, t1);
    for (i = 1; i < 5; i++) fe_sq(t2, t2);
    fe_mul(t1, t2, t1);    /* t1 = z^(2^10 - 1) */

    fe_sq(t2, t1);
    for (i = 1; i < 10; i++) fe_sq(t2, t2);
    fe_mul(t2, t2, t1);    /* t2 = z^(2^20 - 1) */

    fe_sq(t3, t2);
    for (i = 1; i < 20; i++) fe_sq(t3, t3);
    fe_mul(t2, t3, t2);    /* t2 = z^(2^40 - 1) */

    fe_sq(t2, t2);
    for (i = 1; i < 10; i++) fe_sq(t2, t2);
    fe_mul(t1, t2, t1);    /* t1 = z^(2^50 - 1) */

    fe_sq(t2, t1);
    for (i = 1; i < 50; i++) fe_sq(t2, t2);
    fe_mul(t2, t2, t1);    /* t2 = z^(2^100 - 1) */

    fe_sq(t3, t2);
    for (i = 1; i < 100; i++) fe_sq(t3, t3);
    fe_mul(t2, t3, t2);    /* t2 = z^(2^200 - 1) */

    fe_sq(t2, t2);
    for (i = 1; i < 50; i++) fe_sq(t2, t2);
    fe_mul(t1, t2, t1);    /* t1 = z^(2^250 - 1) */

    fe_sq(t1, t1);
    fe_sq(t1, t1);
    fe_sq(t1, t1);
    fe_sq(t1, t1);
    fe_sq(t1, t1);         /* t1 = z^(2^255 - 32) */

    fe_mul(out, t1, t0);   /* out = z^(2^255 - 21) = z^(p-2) */
}

/*
 * Montgomery ladder: compute X25519 scalar multiplication.
 * scalar: 32-byte scalar (clamped)
 * point:  32-byte u-coordinate (little-endian)
 * result: 32-byte u-coordinate of result
 */
static void x25519_scalarmult(uint8_t result[32],
                               const uint8_t scalar[32],
                               const uint8_t point[32])
{
    fe x1, x2, z2, x3, z3, tmp0, tmp1;

    fe_frombytes(x1, point);
    fe_1(x2);
    fe_0(z2);
    fe_copy(x3, x1);
    fe_1(z3);

    uint64_t swap = 0;

    for (int pos = 254; pos >= 0; pos--) {
        uint64_t b = (scalar[pos / 8] >> (pos & 7)) & 1;
        swap ^= b;
        fe_cswap(x2, x3, swap);
        fe_cswap(z2, z3, swap);
        swap = b;

        fe_sub(tmp0, x3, z3);   /* A = x2 - z2 (reusing tmp naming from RFC) */
        fe_sub(tmp1, x2, z2);   /* Actually: let's follow the RFC 7748 ladder */
        /* RFC 7748 Section 5 Montgomery ladder step */
        fe a, aa, b2, bb, e, c2, d, da, cb;

        fe_add(a, x2, z2);
        fe_carry(a);
        fe_sq(aa, a);

        fe_sub(b2, x2, z2);
        fe_carry(b2);
        fe_sq(bb, b2);

        fe_sub(e, aa, bb);
        fe_carry(e);

        fe_add(c2, x3, z3);
        fe_carry(c2);

        fe_sub(d, x3, z3);
        fe_carry(d);

        fe_mul(da, d, a);
        fe_mul(cb, c2, b2);

        fe_add(tmp0, da, cb);
        fe_carry(tmp0);
        fe_sq(x3, tmp0);

        fe_sub(tmp1, da, cb);
        fe_carry(tmp1);
        fe_sq(tmp1, tmp1);
        fe_mul(z3, x1, tmp1);

        fe_mul(x2, aa, bb);
        fe_mul121666(tmp0, e);
        fe_add(tmp0, aa, tmp0);
        fe_carry(tmp0);
        fe_mul(z2, e, tmp0);
    }

    fe_cswap(x2, x3, swap);
    fe_cswap(z2, z3, swap);

    fe_invert(z2, z2);
    fe_mul(x2, x2, z2);
    fe_tobytes(result, x2);
}

/* The base point for Curve25519 is u = 9 */
static const uint8_t X25519_BASE_POINT[32] = { 9 };

static void x25519_clamp(uint8_t scalar[32])
{
    scalar[0]  &= 248;   /* clear bits 0,1,2 */
    scalar[31] &= 127;   /* clear bit 255 (bit 7 of byte 31) */
    scalar[31] |= 64;    /* set bit 254 (bit 6 of byte 31) */
}

void crypto_x25519_public_key(uint8_t public_key[32],
                               const uint8_t secret_key[32])
{
    uint8_t clamped[32];
    memcpy(clamped, secret_key, 32);
    x25519_clamp(clamped);
    x25519_scalarmult(public_key, clamped, X25519_BASE_POINT);
    crypto_wipe(clamped, 32);
}

void crypto_x25519(uint8_t shared_key[32],
                   const uint8_t your_secret_key[32],
                   const uint8_t their_public_key[32])
{
    uint8_t clamped[32];
    memcpy(clamped, your_secret_key, 32);
    x25519_clamp(clamped);
    x25519_scalarmult(shared_key, clamped, their_public_key);
    crypto_wipe(clamped, 32);
}
