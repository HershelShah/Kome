/* stun.h — minimal STUN (RFC 5389) Binding client + helpers (M5). Internal.
 *
 * Just enough to learn a public reflexive endpoint via XOR-MAPPED-ADDRESS, plus
 * server-side helpers so tests can run a local STUN responder. IPv4 only. */
#ifndef SYNC_STUN_H
#define SYNC_STUN_H

#include <cstdint>
#include <string>

#include "transport/udp.h"

namespace ke {

constexpr uint32_t kStunMagicCookie = 0x2112A442u;

/* Build a Binding Request; fills a fresh 12-byte transaction id. */
void stun_build_request(uint8_t txid[12], std::string &out);

/* Parse a Binding Request, extracting its transaction id (server side). */
bool stun_parse_request(const std::string &msg, uint8_t txid[12]);

/* Build a Binding Success Response echoing `mapped` as XOR-MAPPED-ADDRESS. */
void stun_build_response(const uint8_t txid[12], const Endpoint &mapped,
                         std::string &out);

/* Parse a Binding Success Response, verifying txid and extracting the mapped
 * (reflexive) endpoint. */
bool stun_parse_response(const std::string &msg, const uint8_t txid[12],
                         Endpoint &mapped);

} // namespace ke

#endif /* SYNC_STUN_H */
