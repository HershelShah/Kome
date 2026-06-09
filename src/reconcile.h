/* reconcile.h — range-based set reconciliation session (M3). Internal.
 *
 * The session and its message format are implemented in reconcile.cpp; the
 * public entry points are sync_session_* in sync_engine.h. This header just
 * documents the tuning constants and the protocol shape. */
#ifndef SYNC_RECONCILE_H
#define SYNC_RECONCILE_H

#include <cstddef>
#include <cstdint>

namespace ke {

/* Branching factor: a differing range is split into up to this many
 * equal-count buckets per round, giving ~log_BUCKETS(n) round-trips. */
constexpr size_t kBuckets = 16;

/* When a range holds at most this many of the local elements, stop splitting
 * and exchange the records directly. */
constexpr size_t kLeafThreshold = 2;

/* A healthy reconcile converges in O(log n) rounds; cap a session's lifetime so
 * a peer that never lets it quiesce can't run it unboundedly even if the caller
 * drives without its own deadline. */
constexpr uint64_t kMaxSessionSteps = 1u << 20;

/* Cap the size of a single reconcile message so it never exceeds the relay's
 * blob limit (S6a kMaxBlobBytes = 64 KiB) or bloats UDP datagrams. A HAVE/LEAF
 * reply that would carry more record bytes than this is split across several
 * descriptors, and a session emits at most this many record-bytes per message,
 * queueing the rest for the next round. The headroom under 64 KiB covers the
 * message envelope, attached capabilities, and channel-encryption overhead. */
constexpr size_t kMaxMessageBytes = 48u * 1024u;

} // namespace ke

#endif /* SYNC_RECONCILE_H */
