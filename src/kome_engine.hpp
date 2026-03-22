#ifndef KOME_ENGINE_HPP
#define KOME_ENGINE_HPP

#include "kome.h"
#include "kome_log.hpp"
#include "kome_transport.hpp"
#include "kome_sync.hpp"

#include <atomic>
#include <mutex>
#include <string>
#include <unordered_map>
#include <vector>
#include <memory>

struct KomeEngine {
    std::mutex                          mu;
    std::unique_ptr<kome::KomeLog>      log;
    std::unique_ptr<kome::KomeSyncManager> sync_mgr;
    std::unique_ptr<kome::KomeTransportAdapter> transport_adapter;

    uint8_t                             identity[32] = {};
    bool                                identity_set = false;
    uint64_t                            next_seq     = 1;
    uint64_t                            tombstone_ttl_sec = 30 * 24 * 3600;
    std::atomic<KomeLogLevel>           log_level{KOME_LOG_WARN};
    std::atomic<bool>                   closed{false};

    KomeTransport                      *transport    = nullptr;

    /* Callbacks — guarded by mu */
    KomeRemoteChangeCallback            on_remote_change_cb   = nullptr;
    void                               *on_remote_change_ud   = nullptr;
    std::unordered_map<std::string, std::pair<KomeRemoteChangeCallback, void*>> ns_change_cbs;
    KomeConflictCallback                on_conflict_cb        = nullptr;
    void                               *on_conflict_ud        = nullptr;
    KomeSyncDoneCallback                on_sync_done_cb       = nullptr;
    void                               *on_sync_done_ud       = nullptr;
    KomeSyncProgressCallback            on_sync_progress_cb   = nullptr;
    void                               *on_sync_progress_ud   = nullptr;
    KomeReplicationChangeCallback       on_repl_change_cb     = nullptr;
    void                               *on_repl_change_ud     = nullptr;

    uint32_t                            ack_since_gc          = 0;
};

#endif /* KOME_ENGINE_HPP */
