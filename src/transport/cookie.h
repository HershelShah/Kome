/* cookie.h — stateless return-routability cookies (M5 hardening, F5).
 *
 * SYN-cookie style. Instead of storing a random nonce per outstanding challenge
 * — a table that a spoofed-source flood can exhaust or evict, starving honest
 * peers — the server derives the cookie from a process-local secret:
 *
 *     cookie = HMAC(secret, window || context)[:16]
 *
 * `context` binds the caller's server-observed endpoint (and the request's key),
 * so a cookie sent to a spoofed source is useless to an off-path attacker (only
 * whoever actually receives it at that endpoint can echo it back — exactly the
 * return-routability property). `window` is a coarse time bucket; verification
 * accepts the current and previous window, so a cookie survives one round-trip
 * but expires shortly after, bounding replay. No per-request state is held, so
 * there is nothing for a flood to exhaust.
 *
 * Trade-off vs. the old per-challenge table: a cookie is not single-use, so an
 * on-path attacker who observes a valid auth datagram can replay it until the
 * cookie expires. This grants no new power against the stated adversary: the
 * cookie is bound to the *server-observed* source address, so a reply (relay
 * delivery / rendezvous endpoint) is only ever sent back to that source — never
 * to an attacker-chosen victim — and an off-path spoofer never receives the
 * cookie in the first place. The short window bounds the residual on-path
 * replay (e.g. re-triggering a mailbox drain to the legitimate fetcher). */
#ifndef SYNC_TRANSPORT_COOKIE_H
#define SYNC_TRANSPORT_COOKIE_H

#include <cstdint>
#include <string>

namespace ke {

class Cookies {
public:
    /* Issue the cookie for `context` now. Returns false only if the CSPRNG
     * secret cannot be initialized — the caller then drops the request (as it
     * already did on a per-nonce RNG failure). */
    bool issue(const std::string &context, uint8_t out[16]);

    /* Constant-time check that `presented` is a cookie we issued for `context`
     * within the accepted window. */
    bool verify(const std::string &context, const uint8_t presented[16]);

private:
    bool ensure_secret();
    uint8_t secret_[32] = {0};
    bool    have_secret_ = false;
};

} // namespace ke

#endif /* SYNC_TRANSPORT_COOKIE_H */
