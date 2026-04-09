#ifndef KOME_ENGINE_HPP
#define KOME_ENGINE_HPP

/**
 * @file kome_engine.hpp
 * @brief KomeEngine — the opaque handle behind the C API.
 *
 * A KomeEngine owns:
 *   - A KomeLog (SQLite storage layer)
 *   - A KomeSyncManager (sync state machine, created on transport attach)
 *   - Peer identity (32-byte SHA-256 fingerprint)
 *   - All registered callbacks
 *   - Namespace sync filters and entry TTL cache
 *
 * Thread safety: all fields are guarded by @c mu except @c log_level and
 * @c closed (atomics). The C API functions acquire @c mu on entry.
 */

#include "kome.h"
#include "kome_log.hpp"
#include "kome_sync.hpp"

#include <atomic>
#include <mutex>
#include <string>
#include <unordered_map>
#include <vector>
#include <memory>

struct KomeEngine {
    std::mutex                          mu;   ///< Guards all mutable state below
    std::unique_ptr<kome::KomeLog>      log;  ///< SQLite storage
    std::shared_ptr<kome::KomeSyncManager> sync_mgr; ///< Sync protocol (null until transport attached)

    uint8_t                             identity[32] = {};   ///< SHA-256 of key material
    bool                                identity_set = false;
    uint64_t                            next_seq     = 1;    ///< Next sequence number for local writes
    std::atomic<bool>                   closed{false};

    KomeTransport                      *transport    = nullptr; ///< Raw transport pointer (app-owned)

    /* Callbacks — all guarded by mu */
    KomeRemoteChangeCallback            on_remote_change_cb   = nullptr;
    void                               *on_remote_change_ud   = nullptr;
    std::unordered_map<std::string, std::pair<KomeRemoteChangeCallback, void*>> ns_change_cbs;
    KomeConflictCallback                on_conflict_cb        = nullptr;
    void                               *on_conflict_ud        = nullptr;
    KomeSyncDoneCallback                on_sync_done_cb       = nullptr;
    void                               *on_sync_done_ud       = nullptr;
    KomeSyncProgressCallback            on_sync_progress_cb   = nullptr;
    void                               *on_sync_progress_ud   = nullptr;

    /** Namespace filter for sync. Empty = sync all namespaces (default). */
    std::vector<std::string>            sync_namespaces;

    /** Per-namespace entry TTL in seconds. Cached in-memory to avoid
     *  DB lookups on every incoming entry during sync. */
    std::unordered_map<std::string, uint64_t> entry_ttls;
};

#endif /* KOME_ENGINE_HPP */
