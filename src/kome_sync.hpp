#ifndef KOME_SYNC_HPP
#define KOME_SYNC_HPP

/**
 * @file kome_sync.hpp
 * @brief Sync protocol state machine.
 *
 * KomeSyncManager handles all peer-to-peer synchronization:
 *   - Handshake: exchange version vectors + namespace filters
 *   - Differential sync: send only entries the peer is missing
 *   - Live push: forward local writes to connected peers in real-time
 *   - Gossip relay: forward received entries to other live peers
 *   - Conflict resolution: LWW default with user callback override
 *
 * ## Lock ordering
 *
 * Two locks exist: @c engine_->mu (protects DB + engine state) and
 * @c peers_mu_ (protects the peer connection map). The invariant is:
 *
 *   **Always acquire engine_->mu BEFORE peers_mu_.**
 *
 * This prevents deadlocks between sync operations and the C API.
 * The 5-phase design in process_remote_entries() drops all locks
 * between phases to allow conflict callbacks to call kome_put/kome_get.
 */

#include "kome.h"
#include "kome_log.hpp"
#include "kome_wire.hpp"
#include <cstdint>
#include <map>
#include <string>
#include <mutex>

struct KomeEngine;

namespace kome {

/**
 * @brief Peer sync lifecycle states.
 *
 * ```
 * IDLE → SYNCING → WE_DONE/THEY_DONE → LIVE
 * ```
 *
 * Transitions happen in handle_sync_request() and handle_sync_done().
 * Once LIVE, local writes are pushed automatically via on_local_write().
 * Disconnect removes the peer entirely (no IDLE reset).
 */
enum class PeerSyncState {
    IDLE,        ///< Not syncing — waiting for initiate_sync()
    SYNCING,     ///< Exchange started, neither side has sent SYNC_DONE
    WE_DONE,     ///< We sent SYNC_DONE, waiting for their SYNC_DONE
    THEY_DONE,   ///< They sent SYNC_DONE, waiting for ours
    LIVE         ///< Both done — real-time push mode active
};

/**
 * @brief Per-peer connection state tracked by the sync manager.
 */
struct PeerInfo {
    PeerSyncState state = PeerSyncState::IDLE;
    uint64_t      entries_received = 0;         ///< Count of SYNC_ENTRYs received (for progress callback)
    std::vector<std::string> agreed_namespaces; ///< Intersection of both sides' namespace filters; empty = all
};

/**
 * @brief Manages sync protocol for all connected peers.
 *
 * Created when kome_attach_transport() is called. Destroyed when the
 * transport is detached or the engine is closed.
 */
class KomeSyncManager {
public:
    explicit KomeSyncManager(KomeEngine *engine);

    /** Wire up the transport's send/recv/peer callbacks. */
    void set_transport(KomeTransport *transport);

    /** Called by transport when a peer connects. Starts handshake. */
    void on_peer_connected(const uint8_t *peer_fp);
    void on_peer_disconnected(const uint8_t *peer_fp);

    /** Called by transport when data arrives from a peer. Dispatches by message type. */
    void on_recv(const uint8_t *peer_fp, const uint8_t *data, size_t len);

    /** Called after a local kome_put/kome_delete. Pushes to LIVE peers. */
    void on_local_write(const LogEntry &entry);
    void on_local_write_batch(const std::vector<LogEntry> &entries);

    /** Initiate sync handshake — sends SYNC_REQUEST with version vector + namespace filter. */
    void initiate_sync(const uint8_t *peer_fp);

    /** Returns true if the peer is idle (not currently syncing or live). */
    bool is_peer_idle(const uint8_t *peer_fp);

private:
    KomeEngine            *engine_;
    KomeTransport         *transport_ = nullptr;

    std::mutex             peers_mu_;                        ///< Guards peers_ map
    std::map<std::string, PeerInfo> peers_;                  ///< Key = 32-byte fingerprint as string

    static std::string fp_key(const uint8_t *fp) {
        return std::string((const char*)fp, 32);
    }

    void handle_sync_request(const uint8_t *peer_fp, const uint8_t *data, size_t len);
    void handle_sync_entry(const uint8_t *peer_fp, const uint8_t *data, size_t len);
    void handle_sync_done(const uint8_t *peer_fp);
    void handle_sync_ack(const uint8_t *peer_fp, const uint8_t *data, size_t len);
    void handle_live_entry(const uint8_t *peer_fp, const uint8_t *data, size_t len);
    void handle_batch_entry(const uint8_t *peer_fp, const uint8_t *data, size_t len);

    /**
     * @brief Unified 5-phase pipeline for processing remote entries.
     *
     * Handles single entries, live pushes, and batches through one code path.
     * See docs/ARCHITECTURE.md for the full phase diagram.
     *
     * @param peer_fp  32-byte fingerprint of the sending peer
     * @param entries  Entries to process (modified in-place: invalid entries filtered out)
     */
    void process_remote_entries(const uint8_t *peer_fp, std::vector<SyncEntry> &entries);

    void send_to_peer(const uint8_t *peer_fp, const std::vector<uint8_t> &data);
};

} /* namespace kome */

#endif /* KOME_SYNC_HPP */
