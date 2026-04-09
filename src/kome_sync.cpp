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
static const uint64_t DEFAULT_TOMBSTONE_TTL_SEC = 30 * 24 * 3600; /* 30 days */

/* Compute namespace intersection: if either side has empty list, result is empty
   (meaning "all namespaces"). Otherwise, return the common namespaces. */
static std::vector<std::string> ns_intersect(
    const std::vector<std::string> &ours,
    const std::vector<std::string> &theirs)
{
    if (ours.empty() || theirs.empty()) return {};  /* empty = all */
    std::vector<std::string> result;
    for (auto &ns : ours) {
        for (auto &tns : theirs) {
            if (ns == tns) { result.push_back(ns); break; }
        }
    }
    return result;
}

static bool ns_allowed(const std::vector<std::string> &agreed, const std::string &ns) {
    if (agreed.empty()) return true;  /* empty = all */
    for (auto &a : agreed)
        if (a == ns) return true;
    return false;
}

namespace kome {

KomeSyncManager::KomeSyncManager(KomeEngine *engine) : engine_(engine) {}

void KomeSyncManager::set_transport(KomeTransport *transport) {
    transport_ = transport;

    transport_->set_recv_callback(transport_,
        [](void *ud, const uint8_t *peer_fp, const uint8_t *data, size_t len) {
            static_cast<KomeSyncManager*>(ud)->on_recv(peer_fp, data, len);
        }, this);

    transport_->set_peer_callback(transport_,
        [](void *ud, const uint8_t *peer_fp, int connected) {
            auto *self = static_cast<KomeSyncManager*>(ud);
            if (connected)
                self->on_peer_connected(peer_fp);
            else
                self->on_peer_disconnected(peer_fp);
        }, this);
}

void KomeSyncManager::on_peer_connected(const uint8_t *peer_fp) {
    {
        std::lock_guard<std::mutex> lock(peers_mu_);
        auto &info = peers_[fp_key(peer_fp)];
        if (info.state == PeerSyncState::IDLE)
            info.state = PeerSyncState::SYNCING;
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
    }
}

void KomeSyncManager::on_local_write(const LogEntry &entry) {
    /* Snapshot live peers under lock, then send outside lock. */
    std::vector<std::string> live_peers;
    {
        std::lock_guard<std::mutex> lock(peers_mu_);
        for (auto &[key, info] : peers_) {
            if (info.state != PeerSyncState::LIVE) continue;
            if (!ns_allowed(info.agreed_namespaces, entry.ns)) continue;
            live_peers.push_back(key);
        }
    }
    if (live_peers.empty()) return;
    auto msg = encode_live_entry(entry);
    for (auto &fp : live_peers)
        send_to_peer((const uint8_t*)fp.data(), msg);
}

bool KomeSyncManager::is_peer_idle(const uint8_t *peer_fp) {
    std::lock_guard<std::mutex> lock(peers_mu_);
    auto it = peers_.find(fp_key(peer_fp));
    if (it == peers_.end()) return true;  /* unknown peer treated as idle */
    return it->second.state == PeerSyncState::IDLE;
}

void KomeSyncManager::initiate_sync(const uint8_t *peer_fp) {
    SyncRequest req;
    req.protocol_version = KOME_PROTOCOL_VERSION;
    {
        std::lock_guard<std::mutex> lock(engine_->mu);
        engine_->log->get_version_vector(req.vv);
        req.namespaces = engine_->sync_namespaces;
    }

    auto msg = encode_sync_request(req);
    send_to_peer(peer_fp, msg);
}

void KomeSyncManager::handle_sync_request(const uint8_t *peer_fp,
                                            const uint8_t *data, size_t len) {
    SyncRequest req;
    if (!decode_sync_request(data, len, &req)) return;

    /* Compute namespace intersection */
    std::vector<std::string> our_ns;
    {
        std::lock_guard<std::mutex> lock(engine_->mu);
        our_ns = engine_->sync_namespaces;
    }
    auto agreed = ns_intersect(our_ns, req.namespaces);

    /* Store agreed namespaces for this peer */
    {
        std::lock_guard<std::mutex> lock(peers_mu_);
        peers_[fp_key(peer_fp)].agreed_namespaces = agreed;
    }

    std::vector<LogEntry> missing;
    {
        std::lock_guard<std::mutex> lock(engine_->mu);
        engine_->log->get_missing_entries(req.vv, missing);
    }

    for (auto &entry : missing) {
        if (!ns_allowed(agreed, entry.ns)) continue;
        auto msg = encode_sync_entry(entry);
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
        if (info.state == PeerSyncState::THEY_DONE) {
            info.state = PeerSyncState::LIVE;
            fire = true;
        } else if (info.state == PeerSyncState::SYNCING || info.state == PeerSyncState::IDLE) {
            info.state = PeerSyncState::WE_DONE;
        }
    }
    if (fire && done_cb) done_cb(done_ud, peer_fp);
}

void KomeSyncManager::handle_sync_entry(const uint8_t *peer_fp,
                                          const uint8_t *data, size_t len) {
    SyncEntry entry;
    if (!decode_sync_entry(data, len, &entry)) return;

    std::vector<SyncEntry> batch{std::move(entry)};
    process_remote_entries(peer_fp, batch);

    /* Track progress */
    uint64_t received = 0;
    {
        std::lock_guard<std::mutex> lock(peers_mu_);
        auto it = peers_.find(fp_key(peer_fp));
        if (it != peers_.end()) {
            it->second.entries_received++;
            received = it->second.entries_received;
        }
    }

    KomeSyncProgressCallback progress_cb = nullptr;
    void *progress_ud = nullptr;
    {
        std::lock_guard<std::mutex> lock(engine_->mu);
        progress_cb = engine_->on_sync_progress_cb;
        progress_ud = engine_->on_sync_progress_ud;
    }
    if (progress_cb) progress_cb(progress_ud, peer_fp, received, 0);
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
        if (info.state == PeerSyncState::WE_DONE) {
            info.state = PeerSyncState::LIVE;
            fire = true;
        } else if (info.state == PeerSyncState::SYNCING || info.state == PeerSyncState::IDLE) {
            info.state = PeerSyncState::THEY_DONE;
        }
    }
    if (fire && done_cb) done_cb(done_ud, peer_fp);
}

void KomeSyncManager::handle_sync_ack(const uint8_t * /*peer_fp*/,
                                        const uint8_t *data, size_t len) {
    SyncAck ack;
    if (!decode_sync_ack(data, len, &ack)) return;

    /* Periodically GC expired tombstones (cheap — just a single DELETE) */
    static thread_local uint32_t ack_count = 0;
    if (++ack_count >= GC_ACK_INTERVAL) {
        ack_count = 0;
        std::lock_guard<std::mutex> lock(engine_->mu);
        engine_->log->gc_tombstones(DEFAULT_TOMBSTONE_TTL_SEC);
    }
}

void KomeSyncManager::handle_live_entry(const uint8_t *peer_fp,
                                          const uint8_t *data, size_t len) {
    SyncEntry entry;
    if (!decode_live_entry(data, len, &entry)) return;

    std::vector<SyncEntry> batch{std::move(entry)};
    process_remote_entries(peer_fp, batch);
}

void KomeSyncManager::on_local_write_batch(const std::vector<LogEntry> &entries) {
    if (entries.empty()) return;

    /* Snapshot live peers and their namespace filters */
    std::vector<std::pair<std::string, std::vector<std::string>>> live_peers;
    {
        std::lock_guard<std::mutex> lock(peers_mu_);
        for (auto &[key, info] : peers_) {
            if (info.state == PeerSyncState::LIVE)
                live_peers.push_back({key, info.agreed_namespaces});
        }
    }
    if (live_peers.empty()) return;

    for (auto &[fp, agreed] : live_peers) {
        std::vector<SyncEntry> filtered;
        for (auto &e : entries) {
            if (ns_allowed(agreed, e.ns))
                filtered.push_back(e);
        }
        if (filtered.empty()) continue;
        auto msg = encode_batch_entry(filtered);
        send_to_peer((const uint8_t*)fp.data(), msg);
    }
}

void KomeSyncManager::handle_batch_entry(const uint8_t *peer_fp,
                                           const uint8_t *data, size_t len) {
    std::vector<SyncEntry> entries;
    if (!decode_batch_entry(data, len, &entries)) return;
    if (entries.empty() || entries.size() > KOME_MAX_BATCH_COUNT) return;
    process_remote_entries(peer_fp, entries);
}

/*
 * Unified remote entry processing — handles both single entries and batches.
 *
 * 5-phase design (lock ordering: engine_->mu before peers_mu_):
 *   Phase 1: Validate, filter by namespace/TTL, snapshot local state (engine lock)
 *   Phase 2: Conflict resolution (no locks — callback may call kome API)
 *   Phase 3: Write entries atomically with TOCTOU guard (engine lock)
 *   Phase 4: Fire change callbacks (no locks)
 *   Phase 5: Gossip relay + ACK (peers lock, then no locks)
 */
void KomeSyncManager::process_remote_entries(const uint8_t *peer_fp,
                                              std::vector<SyncEntry> &entries) {
    uint64_t now_us = timestamp_us();

    /* Filter by namespace scope, TTL, and validate */
    {
        std::lock_guard<std::mutex> lock(engine_->mu);
        std::vector<SyncEntry> accepted;
        accepted.reserve(entries.size());
        for (auto &entry : entries) {
            if (entry.ns.empty() || entry.ns.size() > KOME_MAX_NS_LEN) continue;
            if (entry.key.empty() || entry.key.size() > KOME_MAX_KEY_LEN) continue;
            if (entry.value.size() > KOME_MAX_VALUE_LEN) continue;
            if (!engine_->sync_namespaces.empty() &&
                !ns_allowed(engine_->sync_namespaces, entry.ns))
                continue;
            if (entry.timestamp_us > now_us + KOME_MAX_CLOCK_DRIFT_US) continue;
            if (now_us > KOME_MAX_CLOCK_DRIFT_US &&
                entry.timestamp_us < now_us - KOME_MAX_CLOCK_DRIFT_US)
                continue;
            auto ttl_it = engine_->entry_ttls.find(entry.ns);
            if (ttl_it != engine_->entry_ttls.end() && ttl_it->second > 0) {
                uint64_t max_age_us = ttl_it->second * 1000000ULL;
                if (now_us > entry.timestamp_us &&
                    (now_us - entry.timestamp_us) > max_age_us)
                    continue;
            }
            if (!entry.tombstone) {
                uint8_t computed_hash[32];
                sha256(entry.value.data(), entry.value.size(), computed_hash);
                if (std::memcmp(computed_hash, entry.hash, 32) != 0)
                    continue;
            }
            accepted.push_back(std::move(entry));
        }
        entries = std::move(accepted);
    }
    if (entries.empty()) return;

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

            entry.to_meta(&ctx.remote_meta);

            LogEntry local;
            KomeError err = engine_->log->get_entry(entry.ns.c_str(), entry.key.data(),
                                                     entry.key.size(), &local);
            if (err == KOME_OK) {
                ctx.have_local = true;
                ctx.local_seq_snapshot = local.seq;
                local.to_meta(&ctx.local_meta);
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
    struct StoredEntry {
        std::string ns;
        std::vector<uint8_t> key;
        std::vector<uint8_t> value_copy;
        KomeEntryMeta meta;
        KomeRemoteChangeCallback ns_cb = nullptr;
        void *ns_ud = nullptr;
    };
    std::vector<StoredEntry> stored;
    KomeRemoteChangeCallback change_cb = nullptr;
    void *change_ud = nullptr;
    bool txn_ok = true;

    {
        std::lock_guard<std::mutex> lock(engine_->mu);
        change_cb = engine_->on_remote_change_cb;
        change_ud = engine_->on_remote_change_ud;

        if (engine_->log->begin_transaction() != KOME_OK)
            txn_ok = false;

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
                    current.to_meta(&cur_meta);
                    if (!lww_remote_wins(&cur_meta, &store_meta))
                        continue;
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
            engine_->log->update_version_vector(store_meta.author, store_meta.seq);

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

    for (auto &ctx : ctxs)
        if (ctx.merge_value) std::free(ctx.merge_value);
    if (!txn_ok) return;

    /* Phase 4: Fire callbacks outside all locks */
    for (auto &se : stored) {
        if (change_cb)
            change_cb(change_ud, se.ns.c_str(), se.key.data(), se.key.size(),
                      se.value_copy.data(), se.value_copy.size(), &se.meta);
        if (se.ns_cb)
            se.ns_cb(se.ns_ud, se.ns.c_str(), se.key.data(), se.key.size(),
                     se.value_copy.data(), se.value_copy.size(), &se.meta);
    }

    /* Phase 5: Gossip relay + ACK */
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
            for (auto &se : stored)
                relay_entries.push_back(Entry::from_meta(
                    se.meta, se.ns.c_str(),
                    se.key.data(), se.key.size(),
                    se.value_copy.data(), se.value_copy.size()));
            auto msg = encode_batch_entry(relay_entries);
            for (auto &fp : relay_peers)
                send_to_peer((const uint8_t*)fp.data(), msg);
        }
    }

    for (auto &entry : entries) {
        SyncAck ack;
        std::memcpy(ack.author, entry.author, 32);
        ack.seq = entry.seq;
        auto ack_msg = encode_sync_ack(ack);
        send_to_peer(peer_fp, ack_msg);
    }
}

void KomeSyncManager::send_to_peer(const uint8_t *peer_fp,
                                     const std::vector<uint8_t> &data) {
    if (transport_ && transport_->send)
        transport_->send(transport_, peer_fp, data.data(), data.size());
}

} /* namespace kome */
