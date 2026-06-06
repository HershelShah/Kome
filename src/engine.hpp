/* engine.hpp — internal state model shared by the core (M1) and, later, the
 * persistence layer (M2). Not part of the public ABI. */
#ifndef SYNC_ENGINE_INTERNAL_HPP
#define SYNC_ENGINE_INTERNAL_HPP

#include <array>
#include <cstdint>
#include <map>
#include <string>

#include "sync_engine.h"

namespace ke {

using SiteId = std::array<uint8_t, SYNC_SITE_ID_LEN>;

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

/* An LWW register: a field's value plus the timestamp/site that wrote it. */
struct Register {
    std::string value;
    Hlc         hlc;
    SiteId      site{};
};

/* Total order on registers: (hlc, site_id, value). Larger wins on merge. */
int register_cmp(const Register &a, const Register &b);

/* An entity: a causal-length counter (odd == present) and its field registers. */
struct Entity {
    uint64_t                          causal_length = 0;
    std::map<std::string, Register>   fields;

    bool present() const { return (causal_length & 1u) != 0; }
};

using Entities   = std::map<std::string, Entity>;
using Namespaces = std::map<std::string, Entities>;

/* Current wall-clock time in milliseconds since the Unix epoch. */
uint64_t now_ms();

class Storage; /* defined in storage.h (M2) */

} // namespace ke

/* The opaque engine handle from the public header. */
struct sync_engine {
    ke::SiteId       site_id{};
    ke::Hlc          clock;
    ke::Namespaces   ns;
    ke::Storage     *store = nullptr; /* null for in-memory engines */
    uint64_t         db_clock = 0;    /* monotonic per-mutation counter */
};

#endif /* SYNC_ENGINE_INTERNAL_HPP */
