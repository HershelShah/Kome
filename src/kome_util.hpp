#ifndef KOME_UTIL_HPP
#define KOME_UTIL_HPP

/**
 * @file kome_util.hpp
 * @brief Cryptographic and time utilities.
 *
 * Contains a standalone SHA-256 implementation (no external dependency),
 * a key derivation function for database encryption, and a microsecond
 * timestamp function.
 */

#include <cstdint>
#include <cstddef>

namespace kome {

/** @brief Compute SHA-256 hash. Standalone — no heap allocation for data <= 16 MiB. */
void sha256(const uint8_t *data, size_t len, uint8_t out[32]);

/** @brief Current wall-clock time in microseconds since epoch. */
uint64_t timestamp_us();

} /* namespace kome */

#endif /* KOME_UTIL_HPP */
