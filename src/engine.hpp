/* engine.hpp — internal state model shared by the core (M1) and, later, the
 * persistence layer (M2). Not part of the public ABI. */
#ifndef SYNC_ENGINE_INTERNAL_HPP
#define SYNC_ENGINE_INTERNAL_HPP

#include <array>
#include <cstdint>
#include <map>
#include <string>

#include "crypto.h"
#include "sync_engine.h"

namespace ke {

using SiteId = std::array<uint8_t, SYNC_SITE_ID_LEN>;
using PubKey = std::array<uint8_t, SYNC_PUBKEY_LEN>;
using Sig    = std::array<uint8_t, SYNC_SIG_LEN>;

/* Hybrid Logical Clock. */
struct Hlc {
    uint64_t physical = 0;
    uint32_t logical = 0;

    /* Advance for a local event using wall-clock now_ms; returns the new value. */
    Hlc tick(uint64_t now_ms);
    /* Merge a remote timestamp on receive; keeps the clock monotonic. */
    void receive(const Hlc &remote, uint64_t now_ms);
};

/* Total order on HLC: physical, then logical. <0 / 0 / >0. */
int hlc_cmp(const Hlc &a, const Hlc &b);

/* An LWW register: a field's value plus the timestamp/author that wrote it,
 * and the author's signature over the canonical record. */
struct Register {
    std::string value;
    Hlc         hlc;
    PubKey      author{};
    Sig         sig{};
};

/* Total order on registers: (hlc, author, value). Larger wins on merge. */
int register_cmp(const Register &a, const Register &b);

/* An entity: a causal-length counter (odd == present), the author/signature of
 * the current existence assertion, and its field registers. */
struct Entity {
    uint64_t                          causal_length = 0;
    PubKey                            ex_author{};
    Sig                               ex_sig{};
    std::map<std::string, Register>   fields;

    bool present() const { return (causal_length & 1u) != 0; }
};

using Entities   = std::map<std::string, Entity>;
using Namespaces = std::map<std::string, Entities>;

/* Current wall-clock time in milliseconds since the Unix epoch. */
uint64_t now_ms();

class Storage;    /* defined in storage.h (M2) */
class CapStore;   /* defined in capability.h (M4) */

} // namespace ke

/* The opaque engine handle from the public header. */
struct sync_engine {
    ke::KeyPair      identity;        /* signing + agreement keypair */
    ke::SiteId       site_id{};       /* BLAKE2b-256(identity.sign_pk) */
    ke::Hlc          clock;
    ke::Namespaces   ns;
    ke::Storage     *store = nullptr; /* null for in-memory engines */
    ke::CapStore    *caps = nullptr;  /* granted capabilities (M4) */
    uint64_t         db_clock = 0;    /* monotonic per-mutation counter */
    sync_log_fn      log_fn = nullptr;
    void            *log_ctx = nullptr;
};

#endif /* SYNC_ENGINE_INTERNAL_HPP */
