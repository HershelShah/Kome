#ifndef KOME_CONFLICT_HPP
#define KOME_CONFLICT_HPP

#include "kome.h"
#include <cstdint>
#include <cstddef>

namespace kome {

/* Pure conflict resolution function.
 * Returns which entry wins: true = remote wins, false = local wins.
 * LWW: higher timestamp > higher author (memcmp) > higher seq.
 */
bool lww_remote_wins(const KomeEntryMeta *local, const KomeEntryMeta *remote);

/* Full conflict resolution including user callback.
 * Returns the choice: KEEP_LOCAL, KEEP_REMOTE, or MERGE.
 * If MERGE is chosen, merge_value and merge_value_len are set.
 */
KomeConflictChoice resolve_conflict(
    const char *ns, const uint8_t *key, size_t key_len,
    const KomeEntryMeta *local_meta,  const uint8_t *local_value,
    const KomeEntryMeta *remote_meta, const uint8_t *remote_value,
    KomeConflictCallback user_cb, void *user_ud,
    uint8_t **merge_value_out, size_t *merge_value_len_out);

} /* namespace kome */

#endif /* KOME_CONFLICT_HPP */
