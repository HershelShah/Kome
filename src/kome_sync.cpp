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

void KomeSyncManager::set_peer_limits(uint64_t max_bytes, uint64_t max_entries) {
    std::lock_guard<std::mutex> lock(peers_mu_);
    max_bytes_per_minute_ = max_bytes;
    max_entries_per_minute_ = max_entries;
}

bool KomeSyncManager::check_rate_limit(const uint8_t *peer_fp, uint64_t entry_bytes,
                                        uint64_t entry_count) {
    /* Must be called under peers_mu_ */
    std::string key(reinterpret_cast<const char*>(peer_fp), 32);
    auto &state = peer_rates_[key];

    uint64_t now = timestamp_us();
    if (now - state.window_start_us > 60000000ULL) {
        /* Reset window */
        state.window_start_us = now;
        state.bytes_in_window = 0;
        state.entries_in_window = 0;
    }

    state.bytes_in_window += entry_bytes;
    state.entries_in_window += entry_count;

    if (state.bytes_in_window > max_bytes_per_minute_ ||
        state.entries_in_window > max_entries_per_minute_) {
        return false;  /* rate limited */
    }

    return true;  /* allowed */
}

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

    /* Build the access map: what namespaces this peer can access on us */
    std::map<std::string, int> access;
    {
        std::lock_guard<std::mutex> lock(engine_->mu);
        engine_->log->get_peer_namespace_access(peer_fp, access);
    }

    /* Send NAMESPACE_ACL_SYNC to the peer */
    NamespaceACLSync acl_msg;
    for (auto &[ns, role] : access)
        acl_msg.entries.push_back({ns, role});
    send_to_peer(peer_fp, encode_namespace_acl_sync(acl_msg));

    {
        std::lock_guard<std::mutex> lock(peers_mu_);
        auto &info = peers_[key];
        if (info.state == PeerSyncState::IDLE)
            info.state = PeerSyncState::SYNCING;
        info.peer_access = std::move(access);
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
        case SYNC_ACK:            handle_sync_ack(peer_fp, data, len);              break;
        case LIVE_ENTRY:          handle_live_entry(peer_fp, data, len);            break;
        case BATCH_ENTRY:         handle_batch_entry(peer_fp, data, len);           break;
        case NAMESPACE_ACL_SYNC:  handle_namespace_acl_sync(peer_fp, data, len);   break;
    }
}

void KomeSyncManager::on_local_write(const LogEntry &entry) {
    /* Snapshot live peers under lock, then send outside lock.
       This prevents a slow transport::send from blocking all peer operations. */
    std::vector<std::string> live_peers;
    {
        std::lock_guard<std::mutex> lock(peers_mu_);
        for (auto &[key, info] : peers_) {
            if (info.state != PeerSyncState::LIVE) continue;
            /* Only push to peers with READ or WRITE access to this namespace */
            auto it = info.peer_access.find(entry.ns);
            if (it == info.peer_access.end() || it->second < KOME_ROLE_READ)
                continue;
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

    /* Snapshot peer access for filtering.
       If the peer hasn't connected yet (synchronous transport), fall back to DB. */
    std::map<std::string, int> peer_access;
    {
        std::lock_guard<std::mutex> lock(peers_mu_);
        auto it = peers_.find(fp_key(peer_fp));
        if (it != peers_.end())
            peer_access = it->second.peer_access;
    }
    if (peer_access.empty()) {
        std::lock_guard<std::mutex> lock(engine_->mu);
        engine_->log->get_peer_namespace_access(peer_fp, peer_access);
    }

    std::vector<LogEntry> missing;
    {
        std::lock_guard<std::mutex> lock(engine_->mu);
        engine_->log->get_missing_entries(req.vv, missing);
    }

    for (auto &entry : missing) {
        /* Only send entries for namespaces the peer has access to */
        auto it = peer_access.find(entry.ns);
        if (it == peer_access.end() || it->second < KOME_ROLE_READ)
            continue;
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

    /* Clock sanity: reject entries with timestamps too far in the future */
    if (entry.timestamp_us > timestamp_us() + KOME_MAX_CLOCK_DRIFT_US) return;

    /* Per-peer rate limiting */
    {
        std::lock_guard<std::mutex> lock(peers_mu_);
        if (!check_rate_limit(peer_fp, entry.value.size())) return;
    }

    /* Write authorization: sender must have WRITE access on this namespace */
    {
        std::lock_guard<std::mutex> lock(engine_->mu);
        int role = engine_->log->get_peer_role(entry.ns.c_str(), peer_fp);
        if (role < KOME_ROLE_WRITE) return;  /* silently drop */
    }

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
    KomeRemoteChangeCallback ns_change_cb = nullptr;
    void *ns_change_ud = nullptr;
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

            auto ns_it = engine_->ns_change_cbs.find(entry.ns);
            if (ns_it != engine_->ns_change_cbs.end()) {
                ns_change_cb = ns_it->second.first;
                ns_change_ud = ns_it->second.second;
            }

            if ((change_cb || ns_change_cb) && store_value_len > 0)
                store_value_copy.assign(store_value, store_value + store_value_len);
        }
    }

    /* Phase 4: fire callbacks outside all locks */
    if (should_store && change_cb) {
        change_cb(change_ud,
                  entry.ns.c_str(), entry.key.data(), entry.key.size(),
                  store_value_copy.data(), store_value_copy.size(), &store_meta);
    }
    if (should_store && ns_change_cb) {
        ns_change_cb(ns_change_ud,
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

void KomeSyncManager::on_local_write_batch(const std::vector<LogEntry> &entries) {
    if (entries.empty()) return;

    /* Per-peer filtering: only send entries for namespaces the peer can access */
    std::vector<std::pair<std::string, std::map<std::string, int>>> live_peers;
    {
        std::lock_guard<std::mutex> lock(peers_mu_);
        for (auto &[key, info] : peers_) {
            if (info.state == PeerSyncState::LIVE)
                live_peers.push_back({key, info.peer_access});
        }
    }
    if (live_peers.empty()) return;

    for (auto &[fp, peer_access] : live_peers) {
        std::vector<SyncEntry> se_vec;
        se_vec.reserve(entries.size());
        for (auto &e : entries) {
            auto it = peer_access.find(e.ns);
            if (it == peer_access.end() || it->second < KOME_ROLE_READ)
                continue;
            se_vec.push_back(log_to_sync(e));
        }
        if (se_vec.empty()) continue;
        auto msg = encode_batch_entry(se_vec);
        send_to_peer((const uint8_t*)fp.data(), msg);
    }
}

void KomeSyncManager::handle_batch_entry(const uint8_t *peer_fp,
                                           const uint8_t *data, size_t len) {
    std::vector<SyncEntry> entries;
    if (!decode_batch_entry(data, len, &entries)) return;
    if (entries.empty() || entries.size() > KOME_MAX_BATCH_COUNT) return;

    /* Write authorization: drop entries where sender lacks WRITE access */
    {
        std::lock_guard<std::mutex> lock(engine_->mu);
        std::vector<SyncEntry> authorized;
        authorized.reserve(entries.size());
        for (auto &entry : entries) {
            int role = engine_->log->get_peer_role(entry.ns.c_str(), peer_fp);
            if (role >= KOME_ROLE_WRITE)
                authorized.push_back(std::move(entry));
        }
        entries = std::move(authorized);
    }
    if (entries.empty()) return;

    /* Validate all entries first — reject the entire batch on any failure */
    uint64_t now_us = timestamp_us();
    for (auto &entry : entries) {
        if (entry.ns.size() > KOME_MAX_NS_LEN || entry.ns.empty()) return;
        if (entry.key.size() > KOME_MAX_KEY_LEN || entry.key.empty()) return;
        if (entry.value.size() > KOME_MAX_VALUE_LEN) return;
        if (entry.timestamp_us > now_us + KOME_MAX_CLOCK_DRIFT_US) return;
        if (!entry.tombstone) {
            uint8_t computed_hash[32];
            sha256(entry.value.data(), entry.value.size(), computed_hash);
            if (std::memcmp(computed_hash, entry.hash, 32) != 0)
                return;
        }
    }

    /* Per-peer rate limiting: check total batch size against limits */
    {
        uint64_t total_bytes = 0;
        for (auto &entry : entries)
            total_bytes += entry.value.size();

        std::lock_guard<std::mutex> lock(peers_mu_);
        if (!check_rate_limit(peer_fp, total_bytes, entries.size())) return;
    }

    /* Phase 1: Read local state + snapshot callbacks under engine lock */
    struct EntryCtx {
        bool have_local = false;
        uint64_t local_seq_snapshot = 0;
        KomeEntryMeta local_meta{};
        std::vector<uint8_t> local_value_copy;
        KomeEntryMeta remote_meta{};
        bool should_store = false;
        std::vector<uint8_t> store_value_buf;
        uint8_t *merge_value = nullptr;
        size_t merge_value_len = 0;
    };
    std::vector<EntryCtx> ctxs(entries.size());

    KomeConflictCallback conflict_cb = nullptr;
    void *conflict_ud = nullptr;

    {
        std::lock_guard<std::mutex> lock(engine_->mu);
        conflict_cb = engine_->on_conflict_cb;
        conflict_ud = engine_->on_conflict_ud;

        for (size_t i = 0; i < entries.size(); i++) {
            auto &entry = entries[i];
            auto &ctx = ctxs[i];

            ctx.remote_meta.timestamp_us = entry.timestamp_us;
            std::memcpy(ctx.remote_meta.author, entry.author, 32);
            ctx.remote_meta.seq = entry.seq;
            std::memcpy(ctx.remote_meta.hash, entry.hash, 32);
            ctx.remote_meta.value_len = (uint32_t)entry.value.size();
            ctx.remote_meta.tombstone = entry.tombstone;

            LogEntry local;
            KomeError err = engine_->log->get_entry(entry.ns.c_str(), entry.key.data(),
                                                     entry.key.size(), &local);
            if (err == KOME_OK) {
                ctx.have_local = true;
                ctx.local_seq_snapshot = local.seq;
                ctx.local_meta.timestamp_us = local.timestamp_us;
                std::memcpy(ctx.local_meta.author, local.author, 32);
                ctx.local_meta.seq = local.seq;
                std::memcpy(ctx.local_meta.hash, local.hash, 32);
                ctx.local_meta.value_len = (uint32_t)local.value.size();
                ctx.local_meta.tombstone = local.tombstone;
                ctx.local_value_copy = std::move(local.value);
            }
        }
    }

    /* Phase 2: Conflict resolution outside all locks */
    for (size_t i = 0; i < entries.size(); i++) {
        auto &entry = entries[i];
        auto &ctx = ctxs[i];

        ctx.store_value_buf = entry.value;

        if (!ctx.have_local) {
            ctx.should_store = true;
        } else {
            KomeConflictChoice choice = resolve_conflict(
                entry.ns.c_str(), entry.key.data(), entry.key.size(),
                &ctx.local_meta, ctx.local_value_copy.data(),
                &ctx.remote_meta, entry.value.data(),
                conflict_cb, conflict_ud,
                &ctx.merge_value, &ctx.merge_value_len);

            if (choice == KOME_KEEP_REMOTE) {
                ctx.should_store = true;
            } else if (choice == KOME_MERGE) {
                ctx.should_store = true;
                ctx.store_value_buf.assign(ctx.merge_value,
                                           ctx.merge_value + ctx.merge_value_len);
            }
        }
    }

    /* Phase 3: Write all entries atomically under engine lock */
    KomeRemoteChangeCallback change_cb = nullptr;
    void *change_ud = nullptr;

    struct StoredEntry {
        std::string ns;
        std::vector<uint8_t> key;
        std::vector<uint8_t> value_copy;
        KomeEntryMeta meta;
        KomeRemoteChangeCallback ns_cb = nullptr;
        void *ns_ud = nullptr;
    };
    std::vector<StoredEntry> stored;
    bool txn_ok = true;

    {
        std::lock_guard<std::mutex> lock(engine_->mu);
        change_cb = engine_->on_remote_change_cb;
        change_ud = engine_->on_remote_change_ud;

        if (engine_->log->begin_transaction() != KOME_OK) {
            txn_ok = false;
        }

        for (size_t i = 0; i < entries.size() && txn_ok; i++) {
            auto &entry = entries[i];
            auto &ctx = ctxs[i];

            if (!ctx.should_store) continue;

            KomeEntryMeta store_meta = ctx.remote_meta;
            if (ctx.merge_value) {
                sha256(ctx.store_value_buf.data(), ctx.store_value_buf.size(),
                       store_meta.hash);
                store_meta.value_len = (uint32_t)ctx.store_value_buf.size();
                store_meta.tombstone = 0;
            }

            /* TOCTOU guard */
            if (ctx.have_local) {
                LogEntry current;
                KomeError err = engine_->log->get_entry(entry.ns.c_str(), entry.key.data(),
                                                         entry.key.size(), &current);
                if (err == KOME_OK && current.seq != ctx.local_seq_snapshot) {
                    KomeEntryMeta cur_meta;
                    cur_meta.timestamp_us = current.timestamp_us;
                    std::memcpy(cur_meta.author, current.author, 32);
                    cur_meta.seq = current.seq;
                    if (!lww_remote_wins(&cur_meta, &store_meta)) {
                        continue;
                    }
                }
            }

            KomeError err = engine_->log->put_entry(entry.ns.c_str(), entry.key.data(),
                                                     entry.key.size(),
                                                     ctx.store_value_buf.data(),
                                                     ctx.store_value_buf.size(),
                                                     &store_meta);
            if (err != KOME_OK) {
                engine_->log->rollback_transaction();
                txn_ok = false;
                break;
            }

            err = engine_->log->update_version_vector(store_meta.author, store_meta.seq);
            if (err != KOME_OK) {
                engine_->log->rollback_transaction();
                txn_ok = false;
                break;
            }

            StoredEntry se;
            se.ns = entry.ns;
            se.key = entry.key;
            se.meta = store_meta;
            se.value_copy = std::move(ctx.store_value_buf);

            auto ns_it = engine_->ns_change_cbs.find(entry.ns);
            if (ns_it != engine_->ns_change_cbs.end()) {
                se.ns_cb = ns_it->second.first;
                se.ns_ud = ns_it->second.second;
            }

            stored.push_back(std::move(se));
        }

        if (txn_ok)
            engine_->log->commit_transaction();
    }

    for (auto &ctx : ctxs) {
        if (ctx.merge_value) std::free(ctx.merge_value);
    }

    if (!txn_ok) return;

    /* Phase 4: Fire callbacks outside all locks — once per entry in order */
    for (auto &se : stored) {
        if (change_cb) {
            change_cb(change_ud,
                      se.ns.c_str(), se.key.data(), se.key.size(),
                      se.value_copy.data(), se.value_copy.size(), &se.meta);
        }
        if (se.ns_cb) {
            se.ns_cb(se.ns_ud,
                     se.ns.c_str(), se.key.data(), se.key.size(),
                     se.value_copy.data(), se.value_copy.size(), &se.meta);
        }
    }

    /* Phase 5: Gossip relay — forward only stored entries to other live peers */
    if (!stored.empty()) {
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
            std::vector<SyncEntry> relay_entries;
            relay_entries.reserve(stored.size());
            for (auto &se : stored) {
                SyncEntry re;
                re.ns = se.ns;
                re.key = se.key;
                re.value = se.value_copy;
                re.timestamp_us = se.meta.timestamp_us;
                std::memcpy(re.author, se.meta.author, 32);
                re.seq = se.meta.seq;
                std::memcpy(re.hash, se.meta.hash, 32);
                re.tombstone = se.meta.tombstone;
                relay_entries.push_back(std::move(re));
            }
            auto msg = encode_batch_entry(relay_entries);
            for (auto &fp : relay_peers)
                send_to_peer((const uint8_t*)fp.data(), msg);
        }
    }

    /* ACK each entry */
    for (auto &entry : entries) {
        SyncAck ack;
        std::memcpy(ack.author, entry.author, 32);
        ack.seq = entry.seq;
        auto ack_msg = encode_sync_ack(ack);
        if (transport_)
            transport_->send(peer_fp, ack_msg.data(), ack_msg.size());
    }
}

void KomeSyncManager::handle_namespace_acl_sync(const uint8_t * /*peer_fp*/,
                                                  const uint8_t *data, size_t len) {
    NamespaceACLSync acl_sync;
    if (!decode_namespace_acl_sync(data, len, &acl_sync)) return;
    /* Informational — the remote peer is telling us what we can access on them.
       Enforcement happens on each side independently using local configs. */
}

void KomeSyncManager::send_to_peer(const uint8_t *peer_fp,
                                     const std::vector<uint8_t> &data) {
    if (transport_)
        transport_->send(peer_fp, data.data(), data.size());
}

} /* namespace kome */
