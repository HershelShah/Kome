#ifndef KOME_UTIL_HPP
#define KOME_UTIL_HPP

#include <cstdint>
#include <cstddef>

namespace kome {

/* SHA-256 — standalone, no heap allocation for messages <= 16 MiB */
void sha256(const uint8_t *data, size_t len, uint8_t out[32]);

/* Current time in microseconds */
uint64_t timestamp_us();

} /* namespace kome */

#endif /* KOME_UTIL_HPP */
