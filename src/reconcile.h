/* reconcile.h — range-based set reconciliation session (M3). Internal.
 *
 * The session and its message format are implemented in reconcile.cpp; the
 * public entry points are sync_session_* in sync_engine.h. This header just
 * documents the tuning constants and the protocol shape. */
#ifndef SYNC_RECONCILE_H
#define SYNC_RECONCILE_H

#include <cstddef>

namespace ke {

/* Branching factor: a differing range is split into up to this many
 * equal-count buckets per round, giving ~log_BUCKETS(n) round-trips. */
constexpr size_t kBuckets = 16;

/* When a range holds at most this many of the local elements, stop splitting
 * and exchange the records directly. */
constexpr size_t kLeafThreshold = 2;

} // namespace ke

#endif /* SYNC_RECONCILE_H */
