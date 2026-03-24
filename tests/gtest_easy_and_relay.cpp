/*
 * Tests for KomeEasy simplified API and relay transport utilities.
 *
 * Since we can't run a real relay server in unit tests, we test:
 * - KomeEasy lifecycle (open/close)
 * - KomeEasy put/get/delete with local-only mode (NULL relay_url)
 * - Base64 encode/decode
 * - URL parsing
 * - Hex encode/decode
 */
#include <gtest/gtest.h>
#include <cstring>
#include <cstdlib>

/* Public headers */
#include "kome_easy.h"
#include "kome_relay_transport.h"

/* For testing internal functions, we re-declare them here.
 * The actual implementations live in kome_relay_transport.cpp in an
 * anonymous namespace — we need to expose test versions.
 * Instead, we'll duplicate minimal versions for testing. */

/* ========================================================================
   Inline test versions of base64 / hex / URL parsing
   (These exercise the same algorithms as the production code)
   ======================================================================== */

namespace test_utils {

static const char b64_table[] =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

std::string base64_encode(const uint8_t *data, size_t len) {
    std::string out;
    out.reserve(((len + 2) / 3) * 4);
    for (size_t i = 0; i < len; i += 3) {
        uint32_t n = (uint32_t)data[i] << 16;
        if (i + 1 < len) n |= (uint32_t)data[i + 1] << 8;
        if (i + 2 < len) n |= (uint32_t)data[i + 2];

        out.push_back(b64_table[(n >> 18) & 0x3F]);
        out.push_back(b64_table[(n >> 12) & 0x3F]);
        out.push_back((i + 1 < len) ? b64_table[(n >> 6) & 0x3F] : '=');
        out.push_back((i + 2 < len) ? b64_table[n & 0x3F] : '=');
    }
    return out;
}

static int b64_decode_char(char c) {
    if (c >= 'A' && c <= 'Z') return c - 'A';
    if (c >= 'a' && c <= 'z') return c - 'a' + 26;
    if (c >= '0' && c <= '9') return c - '0' + 52;
    if (c == '+') return 62;
    if (c == '/') return 63;
    return -1;
}

std::vector<uint8_t> base64_decode(const char *str, size_t len) {
    std::vector<uint8_t> out;
    out.reserve((len / 4) * 3);

    for (size_t i = 0; i + 3 < len; i += 4) {
        int a = b64_decode_char(str[i]);
        int b = b64_decode_char(str[i + 1]);
        int c = b64_decode_char(str[i + 2]);
        int d = b64_decode_char(str[i + 3]);

        if (a < 0 || b < 0) break;

        out.push_back((uint8_t)((a << 2) | (b >> 4)));
        if (c >= 0) out.push_back((uint8_t)(((b & 0x0F) << 4) | (c >> 2)));
        if (d >= 0) out.push_back((uint8_t)(((c & 0x03) << 6) | d));
    }
    return out;
}

std::string hex_encode(const uint8_t *data, size_t len) {
    static const char hex[] = "0123456789abcdef";
    std::string out;
    out.reserve(len * 2);
    for (size_t i = 0; i < len; i++) {
        out.push_back(hex[data[i] >> 4]);
        out.push_back(hex[data[i] & 0x0F]);
    }
    return out;
}

bool hex_decode(const char *str, size_t str_len, uint8_t *out, size_t out_len) {
    if (str_len != out_len * 2) return false;
    for (size_t i = 0; i < out_len; i++) {
        int hi, lo;
        char ch = str[i * 2];
        char cl = str[i * 2 + 1];

        if (ch >= '0' && ch <= '9') hi = ch - '0';
        else if (ch >= 'a' && ch <= 'f') hi = ch - 'a' + 10;
        else if (ch >= 'A' && ch <= 'F') hi = ch - 'A' + 10;
        else return false;

        if (cl >= '0' && cl <= '9') lo = cl - '0';
        else if (cl >= 'a' && cl <= 'f') lo = cl - 'a' + 10;
        else if (cl >= 'A' && cl <= 'F') lo = cl - 'A' + 10;
        else return false;

        out[i] = (uint8_t)((hi << 4) | lo);
    }
    return true;
}

struct ParsedURL {
    std::string host;
    uint16_t    port = 80;
    std::string path;
};

bool parse_url(const char *url, ParsedURL &out) {
    const char *p = url;
    if (std::strncmp(p, "http://", 7) != 0) return false;
    p += 7;

    const char *host_start = p;
    const char *host_end = p;
    while (*host_end && *host_end != ':' && *host_end != '/' && *host_end != '?')
        host_end++;

    out.host.assign(host_start, host_end);
    if (out.host.empty()) return false;

    p = host_end;
    if (*p == ':') {
        p++;
        char *end = nullptr;
        long port = std::strtol(p, &end, 10);
        if (end == p || port <= 0 || port > 65535) return false;
        out.port = (uint16_t)port;
        p = end;
    } else {
        out.port = 80;
    }

    if (*p == '/') {
        out.path = p;
    } else {
        out.path = "/";
    }

    return true;
}

} /* namespace test_utils */

/* ========================================================================
   Test helpers
   ======================================================================== */

static std::string temp_db(const char *name) {
    return std::string("/tmp/kome_easy_test_") + name + ".db";
}

static void cleanup_db(const std::string &path) {
    std::remove(path.c_str());
    std::remove((path + "-wal").c_str());
    std::remove((path + "-shm").c_str());
}

/* ========================================================================
   Base64 Tests
   ======================================================================== */

TEST(Base64, EncodeEmpty) {
    auto result = test_utils::base64_encode(nullptr, 0);
    EXPECT_EQ(result, "");
}

TEST(Base64, EncodeOneBytes) {
    uint8_t data[] = { 0x4D };
    auto result = test_utils::base64_encode(data, 1);
    EXPECT_EQ(result, "TQ==");
}

TEST(Base64, EncodeTwoBytes) {
    uint8_t data[] = { 0x4D, 0x61 };
    auto result = test_utils::base64_encode(data, 2);
    EXPECT_EQ(result, "TWE=");
}

TEST(Base64, EncodeThreeBytes) {
    uint8_t data[] = { 0x4D, 0x61, 0x6E };
    auto result = test_utils::base64_encode(data, 3);
    EXPECT_EQ(result, "TWFu");
}

TEST(Base64, EncodeHelloWorld) {
    const char *input = "Hello, World!";
    auto result = test_utils::base64_encode(
        (const uint8_t *)input, std::strlen(input));
    EXPECT_EQ(result, "SGVsbG8sIFdvcmxkIQ==");
}

TEST(Base64, RoundTrip) {
    /* Test round-trip for various lengths */
    for (size_t len = 0; len < 256; len++) {
        std::vector<uint8_t> data(len);
        for (size_t i = 0; i < len; i++)
            data[i] = (uint8_t)(i & 0xFF);

        auto encoded = test_utils::base64_encode(data.data(), data.size());
        auto decoded = test_utils::base64_decode(encoded.c_str(), encoded.size());

        ASSERT_EQ(decoded.size(), data.size()) << "length=" << len;
        ASSERT_EQ(decoded, data) << "length=" << len;
    }
}

TEST(Base64, DecodeInvalidChars) {
    /* Decode with invalid characters should stop at invalid point */
    auto result = test_utils::base64_decode("!!!!", 4);
    EXPECT_TRUE(result.empty());
}

/* ========================================================================
   Hex Tests
   ======================================================================== */

TEST(Hex, EncodeBasic) {
    uint8_t data[] = { 0xAA, 0xBB, 0xCC, 0xDD };
    auto result = test_utils::hex_encode(data, 4);
    EXPECT_EQ(result, "aabbccdd");
}

TEST(Hex, EncodeEmpty) {
    auto result = test_utils::hex_encode(nullptr, 0);
    EXPECT_EQ(result, "");
}

TEST(Hex, DecodeBasic) {
    uint8_t out[4];
    bool ok = test_utils::hex_decode("aabbccdd", 8, out, 4);
    EXPECT_TRUE(ok);
    EXPECT_EQ(out[0], 0xAA);
    EXPECT_EQ(out[1], 0xBB);
    EXPECT_EQ(out[2], 0xCC);
    EXPECT_EQ(out[3], 0xDD);
}

TEST(Hex, DecodeUpperCase) {
    uint8_t out[4];
    bool ok = test_utils::hex_decode("AABBCCDD", 8, out, 4);
    EXPECT_TRUE(ok);
    EXPECT_EQ(out[0], 0xAA);
    EXPECT_EQ(out[1], 0xBB);
}

TEST(Hex, DecodeMixedCase) {
    uint8_t out[2];
    bool ok = test_utils::hex_decode("aAbB", 4, out, 2);
    EXPECT_TRUE(ok);
    EXPECT_EQ(out[0], 0xAA);
    EXPECT_EQ(out[1], 0xBB);
}

TEST(Hex, DecodeWrongLength) {
    uint8_t out[4];
    bool ok = test_utils::hex_decode("aabb", 4, out, 4);
    EXPECT_FALSE(ok);
}

TEST(Hex, DecodeInvalidChars) {
    uint8_t out[2];
    bool ok = test_utils::hex_decode("ggzz", 4, out, 2);
    EXPECT_FALSE(ok);
}

TEST(Hex, RoundTrip32Bytes) {
    uint8_t data[32];
    for (int i = 0; i < 32; i++) data[i] = (uint8_t)(i * 7 + 3);

    auto hex = test_utils::hex_encode(data, 32);
    ASSERT_EQ(hex.size(), 64u);

    uint8_t decoded[32];
    bool ok = test_utils::hex_decode(hex.c_str(), hex.size(), decoded, 32);
    ASSERT_TRUE(ok);
    ASSERT_EQ(std::memcmp(data, decoded, 32), 0);
}

/* ========================================================================
   URL Parsing Tests
   ======================================================================== */

TEST(URLParse, SimpleHost) {
    test_utils::ParsedURL url;
    ASSERT_TRUE(test_utils::parse_url("http://relay.example.com", url));
    EXPECT_EQ(url.host, "relay.example.com");
    EXPECT_EQ(url.port, 80);
    EXPECT_EQ(url.path, "/");
}

TEST(URLParse, HostWithPort) {
    test_utils::ParsedURL url;
    ASSERT_TRUE(test_utils::parse_url("http://127.0.0.1:8080", url));
    EXPECT_EQ(url.host, "127.0.0.1");
    EXPECT_EQ(url.port, 8080);
    EXPECT_EQ(url.path, "/");
}

TEST(URLParse, HostWithPath) {
    test_utils::ParsedURL url;
    ASSERT_TRUE(test_utils::parse_url("http://relay.example.com/api/v1", url));
    EXPECT_EQ(url.host, "relay.example.com");
    EXPECT_EQ(url.port, 80);
    EXPECT_EQ(url.path, "/api/v1");
}

TEST(URLParse, HostWithPortAndPath) {
    test_utils::ParsedURL url;
    ASSERT_TRUE(test_utils::parse_url("http://localhost:9090/kome", url));
    EXPECT_EQ(url.host, "localhost");
    EXPECT_EQ(url.port, 9090);
    EXPECT_EQ(url.path, "/kome");
}

TEST(URLParse, RejectsHttps) {
    test_utils::ParsedURL url;
    EXPECT_FALSE(test_utils::parse_url("https://example.com", url));
}

TEST(URLParse, RejectsNoScheme) {
    test_utils::ParsedURL url;
    EXPECT_FALSE(test_utils::parse_url("relay.example.com", url));
}

TEST(URLParse, RejectsEmptyHost) {
    test_utils::ParsedURL url;
    EXPECT_FALSE(test_utils::parse_url("http://", url));
}

TEST(URLParse, RejectsInvalidPort) {
    test_utils::ParsedURL url;
    EXPECT_FALSE(test_utils::parse_url("http://host:0", url));
}

TEST(URLParse, RejectsPortTooLarge) {
    test_utils::ParsedURL url;
    EXPECT_FALSE(test_utils::parse_url("http://host:99999", url));
}

/* ========================================================================
   KomeEasy Lifecycle Tests
   ======================================================================== */

TEST(KomeEasy, OpenCloseLocalOnly) {
    std::string path = temp_db("easy_open_close");
    cleanup_db(path);

    uint8_t key[32];
    std::memset(key, 0x42, sizeof(key));

    KomeEasy *easy = nullptr;
    KomeError err = kome_easy_open(path.c_str(), nullptr, key, sizeof(key), &easy);
    ASSERT_EQ(err, KOME_OK);
    ASSERT_NE(easy, nullptr);

    /* Engine should be accessible */
    KomeEngine *engine = kome_easy_engine(easy);
    EXPECT_NE(engine, nullptr);

    kome_easy_close(easy);
    cleanup_db(path);
}

TEST(KomeEasy, CloseNull) {
    /* Should not crash */
    kome_easy_close(nullptr);
}

TEST(KomeEasy, OpenMissingArgs) {
    KomeEasy *easy = nullptr;
    uint8_t key[32] = {};

    /* NULL db_path */
    EXPECT_EQ(kome_easy_open(nullptr, nullptr, key, 32, &easy), KOME_ERR_MISUSE);

    /* NULL key_material */
    EXPECT_EQ(kome_easy_open("/tmp/x.db", nullptr, nullptr, 32, &easy), KOME_ERR_MISUSE);

    /* Zero key_len */
    EXPECT_EQ(kome_easy_open("/tmp/x.db", nullptr, key, 0, &easy), KOME_ERR_MISUSE);

    /* NULL out */
    EXPECT_EQ(kome_easy_open("/tmp/x.db", nullptr, key, 32, nullptr), KOME_ERR_MISUSE);
}

/* ========================================================================
   KomeEasy Put/Get/Delete Tests (local-only mode)
   ======================================================================== */

TEST(KomeEasy, PutGetDelete) {
    std::string path = temp_db("easy_put_get");
    cleanup_db(path);

    uint8_t key_mat[32];
    std::memset(key_mat, 0x55, sizeof(key_mat));

    KomeEasy *easy = nullptr;
    ASSERT_EQ(kome_easy_open(path.c_str(), nullptr, key_mat, sizeof(key_mat), &easy), KOME_OK);

    /* Put */
    const uint8_t k[] = "mykey";
    const uint8_t v[] = "hello world";
    ASSERT_EQ(kome_easy_put(easy, "ns1", k, sizeof(k) - 1, v, sizeof(v) - 1), KOME_OK);

    /* Get */
    uint8_t *val_out = nullptr;
    size_t val_len = 0;
    ASSERT_EQ(kome_easy_get(easy, "ns1", k, sizeof(k) - 1, &val_out, &val_len), KOME_OK);
    ASSERT_NE(val_out, nullptr);
    ASSERT_EQ(val_len, sizeof(v) - 1);
    EXPECT_EQ(std::memcmp(val_out, v, val_len), 0);
    kome_free_value(val_out);

    /* Delete */
    ASSERT_EQ(kome_easy_delete(easy, "ns1", k, sizeof(k) - 1), KOME_OK);

    /* Get after delete — should be NOT_FOUND */
    val_out = nullptr;
    val_len = 0;
    EXPECT_EQ(kome_easy_get(easy, "ns1", k, sizeof(k) - 1, &val_out, &val_len),
              KOME_ERR_NOT_FOUND);

    kome_easy_close(easy);
    cleanup_db(path);
}

TEST(KomeEasy, MultipleNamespaces) {
    std::string path = temp_db("easy_multi_ns");
    cleanup_db(path);

    uint8_t key_mat[32];
    std::memset(key_mat, 0x66, sizeof(key_mat));

    KomeEasy *easy = nullptr;
    ASSERT_EQ(kome_easy_open(path.c_str(), nullptr, key_mat, sizeof(key_mat), &easy), KOME_OK);

    const uint8_t k[] = "same_key";
    const uint8_t v1[] = "value_in_ns1";
    const uint8_t v2[] = "value_in_ns2";

    ASSERT_EQ(kome_easy_put(easy, "ns1", k, sizeof(k) - 1, v1, sizeof(v1) - 1), KOME_OK);
    ASSERT_EQ(kome_easy_put(easy, "ns2", k, sizeof(k) - 1, v2, sizeof(v2) - 1), KOME_OK);

    /* Read back from ns1 */
    uint8_t *val_out = nullptr;
    size_t val_len = 0;
    ASSERT_EQ(kome_easy_get(easy, "ns1", k, sizeof(k) - 1, &val_out, &val_len), KOME_OK);
    EXPECT_EQ(val_len, sizeof(v1) - 1);
    EXPECT_EQ(std::memcmp(val_out, v1, val_len), 0);
    kome_free_value(val_out);

    /* Read back from ns2 */
    ASSERT_EQ(kome_easy_get(easy, "ns2", k, sizeof(k) - 1, &val_out, &val_len), KOME_OK);
    EXPECT_EQ(val_len, sizeof(v2) - 1);
    EXPECT_EQ(std::memcmp(val_out, v2, val_len), 0);
    kome_free_value(val_out);

    kome_easy_close(easy);
    cleanup_db(path);
}

TEST(KomeEasy, GetNonexistent) {
    std::string path = temp_db("easy_get_missing");
    cleanup_db(path);

    uint8_t key_mat[32];
    std::memset(key_mat, 0x77, sizeof(key_mat));

    KomeEasy *easy = nullptr;
    ASSERT_EQ(kome_easy_open(path.c_str(), nullptr, key_mat, sizeof(key_mat), &easy), KOME_OK);

    uint8_t *val_out = nullptr;
    size_t val_len = 0;
    const uint8_t k[] = "noexist";
    EXPECT_EQ(kome_easy_get(easy, "ns", k, sizeof(k) - 1, &val_out, &val_len),
              KOME_ERR_NOT_FOUND);

    kome_easy_close(easy);
    cleanup_db(path);
}

TEST(KomeEasy, EngineAccess) {
    std::string path = temp_db("easy_engine_access");
    cleanup_db(path);

    uint8_t key_mat[32];
    std::memset(key_mat, 0x88, sizeof(key_mat));

    KomeEasy *easy = nullptr;
    ASSERT_EQ(kome_easy_open(path.c_str(), nullptr, key_mat, sizeof(key_mat), &easy), KOME_OK);

    /* Use the engine directly for an advanced operation */
    KomeEngine *engine = kome_easy_engine(easy);
    ASSERT_NE(engine, nullptr);

    /* kome_stats should work through the engine */
    KomeStats stats;
    EXPECT_EQ(kome_stats(engine, &stats), KOME_OK);

    kome_easy_close(easy);
    cleanup_db(path);
}

TEST(KomeEasy, OnChangeCallback) {
    std::string path = temp_db("easy_on_change");
    cleanup_db(path);

    uint8_t key_mat[32];
    std::memset(key_mat, 0x99, sizeof(key_mat));

    KomeEasy *easy = nullptr;
    ASSERT_EQ(kome_easy_open(path.c_str(), nullptr, key_mat, sizeof(key_mat), &easy), KOME_OK);

    /* Register and unregister callback — just test it doesn't crash */
    kome_easy_on_change(easy, nullptr, nullptr);

    kome_easy_close(easy);
    cleanup_db(path);
}

/* ========================================================================
   Relay Transport API Tests (creation with invalid args)
   ======================================================================== */

TEST(RelayTransport, CreateNullArgs) {
    KomeTransport *t = nullptr;
    uint8_t fp[32] = {};

    EXPECT_EQ(kome_relay_transport_create(nullptr, fp, &t), KOME_ERR_MISUSE);
    EXPECT_EQ(kome_relay_transport_create("http://host", nullptr, &t), KOME_ERR_MISUSE);
    EXPECT_EQ(kome_relay_transport_create("http://host", fp, nullptr), KOME_ERR_MISUSE);
}

TEST(RelayTransport, CreateInvalidURL) {
    KomeTransport *t = nullptr;
    uint8_t fp[32] = {};

    EXPECT_EQ(kome_relay_transport_create("not-a-url", fp, &t), KOME_ERR_MISUSE);
    EXPECT_EQ(kome_relay_transport_create("https://host", fp, &t), KOME_ERR_MISUSE);
    EXPECT_EQ(kome_relay_transport_create("http://", fp, &t), KOME_ERR_MISUSE);
}

TEST(RelayTransport, DestroyNull) {
    /* Should not crash */
    kome_relay_transport_destroy(nullptr);
}

TEST(KomeEasy, EngineNullArg) {
    EXPECT_EQ(kome_easy_engine(nullptr), nullptr);
}
