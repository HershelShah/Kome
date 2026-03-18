#include "kome_sync.hpp"
#include "kome_engine.hpp"
#include "kome_conflict.hpp"
#include "kome_util.hpp"
#include <cstring>

/*
 * Lock ordering contract: engine_->mu BEFORE peers_mu_, always.
 * Never acquire engine_->mu while holding peers_mu_.
 */

static const uint32_t GC_ACK_INTERVAL = 100;

namespace kome {

KomeSyncManager::KomeSyncManager(KomeEngine *engine) : engine_(engine) {}

void KomeSyncManager::set_transport(KomeTransportAdapter *transport) {
    transport_ = transport;

    transport_->set_recv_callback(
        [this](const uint8_t *peer_fp, const uint8_t *data, size_t len) {
            on_recv(peer_fp, data, len);
        });

    transport_->set_peer_callback(
        [this](const uint8_t *peer_fp, int connected) {
            if (connected)
                on_peer_connected(peer_fp);
            else
                on_peer_disconnected(peer_fp);
        });
}

void KomeSyncManager::on_peer_connected(const uint8_t *peer_fp) {
    std::string key = fp_key(peer_fp);
    {
        std::lock_guard<std::mutex> lock(peers_mu_);
        auto it = peers_.find(key);
        if (it == peers_.end()) {
            peers_[key] = PeerInfo{PeerSyncState::SYNCING, false, false, 0, 0};
        }
    }
    initiate_sync(peer_fp);
}

void KomeSyncManager::on_peer_disconnected(const uint8_t *peer_fp) {
    std::lock_guard<std::mutex> lock(peers_mu_);
    peers_.erase(fp_key(peer_fp));
}

void KomeSyncManager::on_recv(const uint8_t *peer_fp, const uint8_t *data, size_t len) {
    WireMessageType type;
    if (!decode_message_type(data, len, &type)) return;

    switch (type) {
        case SYNC_REQUEST: handle_sync_request(peer_fp, data, len); break;
        case SYNC_ENTRY:   handle_sync_entry(peer_fp, data, len);   break;
        case SYNC_DONE:    handle_sync_done(peer_fp);                break;
        case SYNC_ACK:     handle_sync_ack(peer_fp, data, len);     break;
        case LIVE_ENTRY:   handle_live_entry(peer_fp, data, len);   break;
    }
}

void KomeSyncManager::on_local_write(const LogEntry &entry) {
    /* Snapshot live peers under lock, then send outside lock.
       This prevents a slow transport::send from blocking all peer operations. */
    std::vector<std::string> live_peers;
    {
        std::lock_guard<std::mutex> lock(peers_mu_);
        for (auto &[key, info] : peers_) {
            if (info.state == PeerSyncState::LIVE)
                live_peers.push_back(key);
        }
    }
    if (live_peers.empty()) return;
    auto msg = encode_live_entry(log_to_sync(entry));
    for (auto &fp : live_peers)
        send_to_peer((const uint8_t*)fp.data(), msg);
}

void KomeSyncManager::initiate_sync(const uint8_t *peer_fp) {
    SyncRequest req;
    req.protocol_version = KOME_PROTOCOL_VERSION;
    {
        std::lock_guard<std::mutex> lock(engine_->mu);
        engine_->log->get_version_vector(req.vv);
    }

    auto msg = encode_sync_request(req);
    send_to_peer(peer_fp, msg);
}

void KomeSyncManager::handle_sync_request(const uint8_t *peer_fp,
                                            const uint8_t *data, size_t len) {
    SyncRequest req;
    if (!decode_sync_request(data, len, &req)) return;

    std::vector<LogEntry> missing;
    {
        std::lock_guard<std::mutex> lock(engine_->mu);
        engine_->log->get_missing_entries(req.vv, missing);
    }

    for (auto &entry : missing) {
        auto msg = encode_sync_entry(log_to_sync(entry));
        send_to_peer(peer_fp, msg);
    }

    send_to_peer(peer_fp, encode_sync_done());

    /* Snapshot callback under engine->mu first, then update peers under peers_mu_.
       This respects the lock ordering: engine->mu before peers_mu_. */
    KomeSyncDoneCallback done_cb = nullptr;
    void *done_ud = nullptr;
    {
        std::lock_guard<std::mutex> elock(engine_->mu);
        done_cb = engine_->on_sync_done_cb;
        done_ud = engine_->on_sync_done_ud;
    }

    bool fire = false;
    {
        std::lock_guard<std::mutex> lock(peers_mu_);
        auto &info = peers_[fp_key(peer_fp)];
        if (info.state == PeerSyncState::IDLE) info.state = PeerSyncState::SYNCING;
        info.we_sent_done = true;
        if (info.we_sent_done && info.they_sent_done) {
            info.state = PeerSyncState::LIVE;
            fire = true;
        }
    }
    if (fire && done_cb) done_cb(done_ud, peer_fp);
}

void KomeSyncManager::handle_sync_entry(const uint8_t *peer_fp,
                                          const uint8_t *data, size_t len) {
    SyncEntry entry;
    if (!decode_sync_entry(data, len, &entry)) return;

    apply_remote_entry(peer_fp, entry);

    /* Track progress — each lock taken independently, never nested */
    uint64_t received = 0, expected = 0;
    {
        std::lock_guard<std::mutex> lock(peers_mu_);
        auto it = peers_.find(fp_key(peer_fp));
        if (it != peers_.end()) {
            it->second.entries_received++;
            received = it->second.entries_received;
            expected = it->second.entries_expected;
        }
    }

    KomeSyncProgressCallback progress_cb = nullptr;
    void *progress_ud = nullptr;
    {
        std::lock_guard<std::mutex> lock(engine_->mu);
        progress_cb = engine_->on_sync_progress_cb;
        progress_ud = engine_->on_sync_progress_ud;
    }
    if (progress_cb) progress_cb(progress_ud, peer_fp, received, expected);
}

void KomeSyncManager::handle_sync_done(const uint8_t *peer_fp) {
    /* Snapshot callback under engine->mu first (lock ordering) */
    KomeSyncDoneCallback done_cb = nullptr;
    void *done_ud = nullptr;
    {
        std::lock_guard<std::mutex> elock(engine_->mu);
        done_cb = engine_->on_sync_done_cb;
        done_ud = engine_->on_sync_done_ud;
    }

    bool fire = false;
    {
        std::lock_guard<std::mutex> lock(peers_mu_);
        auto &info = peers_[fp_key(peer_fp)];
        if (info.state == PeerSyncState::IDLE) info.state = PeerSyncState::SYNCING;
        info.they_sent_done = true;
        info.entries_expected = info.entries_received;
        if (info.we_sent_done && info.they_sent_done) {
            info.state = PeerSyncState::LIVE;
            fire = true;
        }
    }
    if (fire && done_cb) done_cb(done_ud, peer_fp);
}

void KomeSyncManager::handle_sync_ack(const uint8_t *peer_fp,
                                        const uint8_t *data, size_t len) {
    SyncAck ack;
    if (!decode_sync_ack(data, len, &ack)) return;

    KomeReplicationChangeCallback repl_cb = nullptr;
    void *repl_ud = nullptr;
    std::string fire_ns;
    std::vector<uint8_t> fire_key;
    uint32_t fire_confirmed = 0, fire_target = 0;

    {
        std::lock_guard<std::mutex> lock(engine_->mu);
        engine_->log->update_peer_state(peer_fp, ack.author, ack.seq);

        std::vector<LogEntry> entries;
        engine_->log->get_entries_after(ack.author, ack.seq - 1, entries);
        for (auto &e : entries) {
            if (e.seq == ack.seq) {
                engine_->log->increment_replication_peer(
                    e.ns.c_str(), e.key.data(), e.key.size(), peer_fp);
                engine_->log->get_replication_confirmed(
                    e.ns.c_str(), e.key.data(), e.key.size(), &fire_confirmed);
                engine_->log->get_replication_target(e.ns.c_str(), &fire_target);
                fire_ns = e.ns;
                fire_key = e.key;
                repl_cb = engine_->on_repl_change_cb;
                repl_ud = engine_->on_repl_change_ud;
                break;
            }
        }

        if (++engine_->ack_since_gc >= GC_ACK_INTERVAL) {
            engine_->ack_since_gc = 0;
            engine_->log->gc_tombstones(engine_->tombstone_ttl_sec);
            engine_->log->gc_values();
        }
    }
    if (repl_cb && !fire_ns.empty()) {
        repl_cb(repl_ud, fire_ns.c_str(), fire_key.data(), fire_key.size(),
                fire_confirmed, fire_target);
    }
}

void KomeSyncManager::handle_live_entry(const uint8_t *peer_fp,
                                          const uint8_t *data, size_t len) {
    SyncEntry entry;
    if (!decode_live_entry(data, len, &entry)) return;
    apply_remote_entry(peer_fp, entry);
}

void KomeSyncManager::apply_remote_entry(const uint8_t *peer_fp, const SyncEntry &entry) {
    /* Validate received entry sizes — don't trust the peer */
    if (entry.ns.size() > KOME_MAX_NS_LEN || entry.ns.empty()) return;
    if (entry.key.size() > KOME_MAX_KEY_LEN || entry.key.empty()) return;
    if (entry.value.size() > KOME_MAX_VALUE_LEN) return;

    /* Verify hash integrity */
    if (!entry.tombstone) {
        uint8_t computed_hash[32];
        sha256(entry.value.data(), entry.value.size(), computed_hash);
        if (std::memcmp(computed_hash, entry.hash, 32) != 0)
            return;
    }

    KomeEntryMeta remote_meta;
    remote_meta.timestamp_us = entry.timestamp_us;
    std::memcpy(remote_meta.author, entry.author, 32);
    remote_meta.seq = entry.seq;
    std::memcpy(remote_meta.hash, entry.hash, 32);
    remote_meta.value_len = (uint32_t)entry.value.size();
    remote_meta.tombstone = entry.tombstone;

    /* Phase 1: read local + snapshot conflict callback under engine lock */
    bool have_local = false;
    uint64_t local_seq_snapshot = 0;
    KomeEntryMeta local_meta{};
    std::vector<uint8_t> local_value_copy;
    KomeConflictCallback conflict_cb = nullptr;
    void *conflict_ud = nullptr;

    {
        std::lock_guard<std::mutex> lock(engine_->mu);
        conflict_cb = engine_->on_conflict_cb;
        conflict_ud = engine_->on_conflict_ud;

        LogEntry local;
        KomeError err = engine_->log->get_entry(entry.ns.c_str(), entry.key.data(),
                                                 entry.key.size(), &local);
        if (err == KOME_OK) {
            have_local = true;
            local_seq_snapshot = local.seq;
            local_meta.timestamp_us = local.timestamp_us;
            std::memcpy(local_meta.author, local.author, 32);
            local_meta.seq = local.seq;
            std::memcpy(local_meta.hash, local.hash, 32);
            local_meta.value_len = (uint32_t)local.value.size();
            local_meta.tombstone = local.tombstone;
            local_value_copy = std::move(local.value);
        }
    }

    /* Phase 2: conflict resolution outside all locks */
    bool should_store = false;
    uint8_t *merge_value = nullptr;
    size_t merge_value_len = 0;
    const uint8_t *store_value = entry.value.data();
    size_t store_value_len = entry.value.size();

    if (!have_local) {
        should_store = true;
    } else {
        KomeConflictChoice choice = resolve_conflict(
            entry.ns.c_str(), entry.key.data(), entry.key.size(),
            &local_meta, local_value_copy.data(),
            &remote_meta, entry.value.data(),
            conflict_cb, conflict_ud,
            &merge_value, &merge_value_len);

        if (choice == KOME_KEEP_REMOTE) {
            should_store = true;
        } else if (choice == KOME_MERGE) {
            should_store = true;
            store_value = merge_value;
            store_value_len = merge_value_len;
        }
    }

    /* Phase 3: write under engine lock with TOCTOU guard */
    KomeEntryMeta store_meta = remote_meta;
    KomeRemoteChangeCallback change_cb = nullptr;
    void *change_ud = nullptr;
    std::vector<uint8_t> store_value_copy;

    if (should_store) {
        if (merge_value) {
            sha256(store_value, store_value_len, store_meta.hash);
            store_meta.value_len = (uint32_t)store_value_len;
            store_meta.tombstone = 0;
        }

        std::lock_guard<std::mutex> lock(engine_->mu);

        /* TOCTOU guard: if the local entry changed since Phase 1,
           another thread wrote concurrently. Re-read and re-resolve
           using default LWW (fast path — no callback, just compare). */
        if (have_local) {
            LogEntry current;
            KomeError err = engine_->log->get_entry(entry.ns.c_str(), entry.key.data(),
                                                     entry.key.size(), &current);
            if (err == KOME_OK && current.seq != local_seq_snapshot) {
                /* Local entry changed — re-evaluate with LWW only */
                KomeEntryMeta cur_meta;
                cur_meta.timestamp_us = current.timestamp_us;
                std::memcpy(cur_meta.author, current.author, 32);
                cur_meta.seq = current.seq;
                if (!lww_remote_wins(&cur_meta, &store_meta)) {
                    should_store = false; /* local is now newer, skip */
                }
            }
        }

        if (should_store) {
            engine_->log->put_entry(entry.ns.c_str(), entry.key.data(), entry.key.size(),
                                     store_value, store_value_len, &store_meta);
            engine_->log->update_version_vector(store_meta.author, store_meta.seq);
            change_cb = engine_->on_remote_change_cb;
            change_ud = engine_->on_remote_change_ud;

            if (change_cb && store_value_len > 0)
                store_value_copy.assign(store_value, store_value + store_value_len);
        }
    }

    /* Phase 4: fire callback outside all locks */
    if (should_store && change_cb) {
        change_cb(change_ud,
                  entry.ns.c_str(), entry.key.data(), entry.key.size(),
                  store_value_copy.data(), store_value_copy.size(), &store_meta);
    }

    /* Phase 5: gossip relay — forward to other live peers, excluding sender */
    if (should_store) {
        std::string sender_key = fp_key(peer_fp);
        std::vector<std::string> relay_peers;
        {
            std::lock_guard<std::mutex> lock(peers_mu_);
            for (auto &[key, info] : peers_) {
                if (info.state == PeerSyncState::LIVE && key != sender_key)
                    relay_peers.push_back(key);
            }
        }
        if (!relay_peers.empty()) {
            auto msg = encode_live_entry(entry);
            for (auto &fp : relay_peers)
                send_to_peer((const uint8_t*)fp.data(), msg);
        }
    }

    /* ACK */
    SyncAck ack;
    std::memcpy(ack.author, entry.author, 32);
    ack.seq = entry.seq;
    auto ack_msg = encode_sync_ack(ack);
    if (transport_)
        transport_->send(peer_fp, ack_msg.data(), ack_msg.size());

    if (merge_value) std::free(merge_value);
}

void KomeSyncManager::send_to_peer(const uint8_t *peer_fp,
                                     const std::vector<uint8_t> &data) {
    if (transport_)
        transport_->send(peer_fp, data.data(), data.size());
}

} /* namespace kome */
