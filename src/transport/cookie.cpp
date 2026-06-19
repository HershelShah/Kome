/* cookie.cpp — stateless return-routability cookies (F5). */
#include "transport/cookie.h"

#include <chrono>
#include <cstring>

#include "byteorder.h"
#include "crypto.h"

namespace ke {

namespace {

/* Cookie validity window. A cookie is accepted for the current and previous
 * window, so its real lifetime is between one and two windows (10–20 s) —
 * comfortably longer than the single challenge→auth round-trip it must survive,
 * short enough to keep the replay window small. (The cookie is not single-use,
 * so an on-path attacker who captures a valid auth could replay it until it
 * expires; binding to the observed source means the reply still only ever goes
 * to that source, so this is not a third-party reflector — see cookie.h.) */
constexpr uint64_t kCookieWindowMs = 10000;

uint64_t mono_ms() {
    using namespace std::chrono;
    return (uint64_t)duration_cast<milliseconds>(
               steady_clock::now().time_since_epoch())
        .count();
}

void compute(const uint8_t secret[32], uint64_t window,
             const std::string &context, uint8_t out[16]) {
    /* HMAC input = window (fixed 8 bytes) || context. Putting the fixed-width
     * window first keeps the variable-length context unambiguous (no field
     * boundary can be shifted to forge a collision). */
    std::string m;
    m.reserve(8 + context.size());
    uint8_t wb[8];
    store_u64le(wb, window);
    m.append((const char *)wb, 8);
    m += context;
    uint8_t mac[32];
    hmac_sha256(secret, 32, (const uint8_t *)m.data(), m.size(), mac);
    std::memcpy(out, mac, 16);
}

} // namespace

bool Cookies::ensure_secret() {
    if (have_secret_) return true;
    if (!random_bytes(secret_, 32)) return false;
    have_secret_ = true;
    return true;
}

bool Cookies::issue(const std::string &context, uint8_t out[16]) {
    if (!ensure_secret()) return false;
    compute(secret_, mono_ms() / kCookieWindowMs, context, out);
    return true;
}

bool Cookies::verify(const std::string &context, const uint8_t presented[16]) {
    if (!have_secret_) return false; /* nothing was ever issued */
    uint64_t w = mono_ms() / kCookieWindowMs;
    uint8_t c[16];
    compute(secret_, w, context, c);
    if (ct_eq16(c, presented)) return true;
    if (w == 0) return false;
    compute(secret_, w - 1, context, c); /* accept the previous window too */
    return ct_eq16(c, presented);
}

} // namespace ke
