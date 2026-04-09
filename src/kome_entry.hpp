#ifndef KOME_ENTRY_HPP
#define KOME_ENTRY_HPP

/**
 * @file kome_entry.hpp
 * @brief Unified entry type used for both storage and wire protocol.
 *
 * Every piece of data in Kome is an Entry. The same struct is used as the
 * database record (aliased as LogEntry) and the sync message payload
 * (aliased as SyncEntry). This eliminates conversion code between layers.
 *
 * Entries are identified by (namespace, key) and carry:
 *   - value:        opaque binary payload (up to 16 MiB)
 *   - timestamp_us: microsecond wall clock at write time
 *   - author:       32-byte SHA-256 fingerprint of the writing peer
 *   - seq:          per-author monotonic sequence number
 *   - hash:         SHA-256 of the value (for integrity verification)
 *   - tombstone:    1 if this entry represents a delete
 */

#include "kome.h"
#include <cstdint>
#include <cstring>
#include <string>
#include <vector>

namespace kome {

/**
 * @brief The fundamental data unit — a namespaced key-value entry with
 *        causal metadata for replication and conflict resolution.
 */
struct Entry {
    std::string             ns;              ///< Namespace (e.g. "messages")
    std::vector<uint8_t>    key;             ///< Binary key
    std::vector<uint8_t>    value;           ///< Binary value (empty if tombstone)
    uint64_t                timestamp_us = 0;///< Microsecond wall-clock timestamp
    uint8_t                 author[32] = {}; ///< SHA-256 fingerprint of writing peer
    uint64_t                seq = 0;         ///< Per-author monotonic sequence number
    uint8_t                 hash[32] = {};   ///< SHA-256 of value content
    uint8_t                 tombstone = 0;   ///< 1 = deleted entry

    /**
     * @brief Populate a public KomeEntryMeta from this entry's fields.
     *
     * Used when returning metadata to callers through the C API
     * (kome_get, kome_get_meta, kome_get_all, etc.).
     */
    void to_meta(KomeEntryMeta *out) const {
        out->timestamp_us = timestamp_us;
        std::memcpy(out->author, author, 32);
        out->seq = seq;
        std::memcpy(out->hash, hash, 32);
        out->value_len = (uint32_t)value.size();
        out->tombstone = tombstone;
    }

    /**
     * @brief Construct an Entry from a KomeEntryMeta plus raw key/value data.
     *
     * Used after kome_put/kome_delete to build an Entry for the sync layer
     * without manual field-by-field copying.
     */
    static Entry from_meta(const KomeEntryMeta &m, const char *ns_str,
                           const uint8_t *key_data, size_t key_len,
                           const uint8_t *value_data, size_t value_len) {
        Entry e;
        e.ns = ns_str;
        e.key.assign(key_data, key_data + key_len);
        if (value_data && value_len > 0)
            e.value.assign(value_data, value_data + value_len);
        e.timestamp_us = m.timestamp_us;
        std::memcpy(e.author, m.author, 32);
        e.seq = m.seq;
        std::memcpy(e.hash, m.hash, 32);
        e.tombstone = m.tombstone;
        return e;
    }
};

} /* namespace kome */

#endif /* KOME_ENTRY_HPP */
