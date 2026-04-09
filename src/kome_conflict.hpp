#ifndef KOME_CONFLICT_HPP
#define KOME_CONFLICT_HPP

/**
 * @file kome_conflict.hpp
 * @brief Conflict resolution — LWW default with user callback override.
 *
 * When two peers write different values for the same (namespace, key),
 * Kome needs to decide which version wins. The default strategy is
 * Last-Writer-Wins (LWW):
 *
 *   1. Higher timestamp_us wins
 *   2. Tie → higher author fingerprint (memcmp of 32 bytes) wins
 *   3. Tie → higher sequence number wins
 *
 * Apps can override this by registering a conflict callback via
 * kome_on_conflict(). The callback runs OUTSIDE all locks, so it
 * may call kome_put/kome_get. If it returns KOME_MERGE, it must
 * allocate a merged value with malloc().
 */

#include "kome.h"
#include <cstdint>
#include <cstddef>

namespace kome {

/** @brief Pure LWW comparison. Returns true if remote wins over local. */
bool lww_remote_wins(const KomeEntryMeta *local, const KomeEntryMeta *remote);

/**
 * @brief Full conflict resolution: delegates to user callback if set,
 *        otherwise falls back to LWW.
 * @return KOME_KEEP_LOCAL, KOME_KEEP_REMOTE, or KOME_MERGE
 */
KomeConflictChoice resolve_conflict(
    const char *ns, const uint8_t *key, size_t key_len,
    const KomeEntryMeta *local_meta,  const uint8_t *local_value,
    const KomeEntryMeta *remote_meta, const uint8_t *remote_value,
    KomeConflictCallback user_cb, void *user_ud,
    uint8_t **merge_value_out, size_t *merge_value_len_out);

} /* namespace kome */

#endif /* KOME_CONFLICT_HPP */
