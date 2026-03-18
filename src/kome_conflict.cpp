#include "kome_conflict.hpp"
#include <cstring>

namespace kome {

bool lww_remote_wins(const KomeEntryMeta *local, const KomeEntryMeta *remote) {
    /* Higher timestamp wins */
    if (remote->timestamp_us != local->timestamp_us)
        return remote->timestamp_us > local->timestamp_us;

    /* Tiebreak: higher author (lexicographic on 32-byte fingerprint) */
    int cmp = std::memcmp(remote->author, local->author, 32);
    if (cmp != 0)
        return cmp > 0;

    /* Final tiebreak: higher sequence number */
    return remote->seq > local->seq;
}

KomeConflictChoice resolve_conflict(
    const char *ns, const uint8_t *key, size_t key_len,
    const KomeEntryMeta *local_meta,  const uint8_t *local_value,
    const KomeEntryMeta *remote_meta, const uint8_t *remote_value,
    KomeConflictCallback user_cb, void *user_ud,
    uint8_t **merge_value_out, size_t *merge_value_len_out)
{
    if (merge_value_out) *merge_value_out = nullptr;
    if (merge_value_len_out) *merge_value_len_out = 0;

    /* If user callback is set, delegate */
    if (user_cb) {
        return user_cb(user_ud, ns, key, key_len,
                       local_meta, local_value,
                       remote_meta, remote_value,
                       merge_value_out, merge_value_len_out);
    }

    /* Default: LWW */
    return lww_remote_wins(local_meta, remote_meta)
        ? KOME_KEEP_REMOTE
        : KOME_KEEP_LOCAL;
}

} /* namespace kome */
