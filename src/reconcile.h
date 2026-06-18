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

/* Bounds on a *received* reconcile message (F3). A stream transport (TCP/WS)
 * accepts frames up to 64 MiB, and the decoder turns each ~1 input byte into a
 * heap object — a std::string record/cap, or a Desc with several owned strings —
 * so an unbounded message amplifies into GiBs of vector entries. We bound the
 * three growth axes directly (rather than via a tight byte cap that would also
 * reject a legitimately large capabilities blob, which is attached whole to the
 * first message):
 *   - kMaxRecvMessageBytes: coarse early reject, set well above any legitimate
 *     message (descriptors ≤ kMaxMessageBytes + all attached caps).
 *   - kMaxWireElements: total records + caps across the message (each is a
 *     std::string in a growing vector).
 *   - kMaxWireDescriptors: number of descriptors (each a multi-string Desc).
 * Together these cap the decoder's peak allocation to tens of MiB regardless of
 * input size, while leaving >10x headroom for real traffic. */
constexpr size_t kMaxRecvMessageBytes = 8u << 20;  /* 8 MiB */
constexpr uint64_t kMaxWireElements   = 1u << 20;  /* records + caps */
constexpr uint64_t kMaxWireDescriptors = 1u << 16; /* Desc objects */

} // namespace ke

#endif /* SYNC_RECONCILE_H */
