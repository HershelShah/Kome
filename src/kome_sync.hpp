#ifndef KOME_SYNC_HPP
#define KOME_SYNC_HPP

#include "kome.h"
#include "kome_transport.hpp"
#include "kome_log.hpp"
#include "kome_wire.hpp"
#include <cstdint>
#include <cstring>
#include <map>
#include <string>
#include <mutex>

struct KomeEngine;

namespace kome {

enum class PeerSyncState {
    IDLE,
    SYNCING,
    LIVE
};

struct PeerInfo {
    PeerSyncState state = PeerSyncState::IDLE;
    bool          we_sent_done   = false;
    bool          they_sent_done = false;
    uint64_t      entries_expected = 0;
    uint64_t      entries_received = 0;
};

/* Convert LogEntry to SyncEntry (eliminates repeated field-by-field copies) */
inline SyncEntry log_to_sync(const LogEntry &e) {
    SyncEntry se;
    se.ns = e.ns;
    se.key = e.key;
    se.value = e.value;
    se.timestamp_us = e.timestamp_us;
    std::memcpy(se.author, e.author, 32);
    se.seq = e.seq;
    std::memcpy(se.hash, e.hash, 32);
    se.tombstone = e.tombstone;
    return se;
}

class KomeSyncManager {
public:
    explicit KomeSyncManager(KomeEngine *engine);

    void set_transport(KomeTransportAdapter *transport);

    /* Called when a peer connects */
    void on_peer_connected(const uint8_t *peer_fp);
    void on_peer_disconnected(const uint8_t *peer_fp);

    /* Called when data is received from a peer */
    void on_recv(const uint8_t *peer_fp, const uint8_t *data, size_t len);

    /* Called when local data is written (for live mode push) */
    void on_local_write(const LogEntry &entry);
    void on_local_write_batch(const std::vector<LogEntry> &entries);

    /* Initiate sync with a specific peer */
    void initiate_sync(const uint8_t *peer_fp);

private:
    KomeEngine            *engine_;
    KomeTransportAdapter  *transport_ = nullptr;

    std::mutex             peers_mu_;
    std::map<std::string, PeerInfo> peers_; /* key = 32-byte fingerprint */

    static std::string fp_key(const uint8_t *fp) {
        return std::string((const char*)fp, 32);
    }

    void handle_sync_request(const uint8_t *peer_fp, const uint8_t *data, size_t len);
    void handle_sync_entry(const uint8_t *peer_fp, const uint8_t *data, size_t len);
    void handle_sync_done(const uint8_t *peer_fp);
    void handle_sync_ack(const uint8_t *peer_fp, const uint8_t *data, size_t len);
    void handle_live_entry(const uint8_t *peer_fp, const uint8_t *data, size_t len);
    void handle_batch_entry(const uint8_t *peer_fp, const uint8_t *data, size_t len);

    void apply_remote_entry(const uint8_t *peer_fp, const SyncEntry &entry);
    void send_to_peer(const uint8_t *peer_fp, const std::vector<uint8_t> &data);
};

} /* namespace kome */

#endif /* KOME_SYNC_HPP */
