#include "kome_engine.hpp"
#include "kome_util.hpp"
#include <cstring>
#include <cstdlib>

static const char *KOME_VERSION_STR = "0.0.1";

extern "C" {

KOME_API KomeError kome_open(const KomeConfig *config, KomeEngine **out) {
    if (!config || !config->path || !out) return KOME_ERR_MISUSE;

    auto *engine = new (std::nothrow) KomeEngine;
    if (!engine) return KOME_ERR_INTERNAL;

    engine->log = std::make_unique<kome::KomeLog>();
    int use_wal = config->disable_wal ? 0 : 1;
    int timeout = config->busy_timeout_ms > 0 ? config->busy_timeout_ms : 5000;

    KomeError err = engine->log->open(config->path, use_wal, timeout,
                                       config->encryption_key,
                                       config->encryption_key_len);
    if (err != KOME_OK) {
        delete engine;
        return err;
    }

    *out = engine;
    return KOME_OK;
}

KOME_API void kome_close(KomeEngine *engine) {
    if (!engine) return;

    /* Mark closed — any thread that wakes up on mu will see this and bail */
    engine->closed.store(true, std::memory_order_release);

    {
        std::lock_guard<std::mutex> lock(engine->mu);
        engine->sync_mgr.reset();
        engine->log->close();
    }
    delete engine;
}

KOME_API KomeError kome_set_identity(KomeEngine *engine, const uint8_t *key_material, size_t len) {
    if (!engine || !key_material || len == 0) return KOME_ERR_MISUSE;

    std::lock_guard<std::mutex> lock(engine->mu);
    if (engine->closed.load(std::memory_order_acquire)) return KOME_ERR_MISUSE;

    kome::sha256(key_material, len, engine->identity);
    engine->identity_set = true;

    std::map<std::string, uint64_t> vv;
    engine->log->get_version_vector(vv);
    std::string id_key((const char*)engine->identity, 32);
    auto it = vv.find(id_key);
    if (it != vv.end())
        engine->next_seq = it->second + 1;

    return KOME_OK;
}

KOME_API KomeError kome_put(KomeEngine *engine,
    const char *ns, const uint8_t *key, size_t key_len,
    const uint8_t *value, size_t value_len,
    KomeEntryMeta *meta_out)
{
    if (!engine || !ns || !key || !value) return KOME_ERR_MISUSE;

    size_t ns_len = std::strlen(ns);
    if (ns_len == 0 || ns_len > KOME_MAX_NS_LEN) return KOME_ERR_TOO_LARGE;
    if (key_len == 0 || key_len > KOME_MAX_KEY_LEN) return KOME_ERR_TOO_LARGE;
    if (value_len > KOME_MAX_VALUE_LEN) return KOME_ERR_TOO_LARGE;

    KomeEntryMeta meta;
    std::shared_ptr<kome::KomeSyncManager> sync;
    {
        std::lock_guard<std::mutex> lock(engine->mu);
        if (engine->closed.load(std::memory_order_acquire)) return KOME_ERR_MISUSE;
        if (!engine->identity_set) return KOME_ERR_MISUSE;

        meta.timestamp_us = kome::timestamp_us();
        std::memcpy(meta.author, engine->identity, 32);
        meta.seq = engine->next_seq++;
        kome::sha256(value, value_len, meta.hash);
        meta.value_len = (uint32_t)value_len;
        meta.tombstone = 0;

        KomeError err = engine->log->put_entry(ns, key, key_len, value, value_len, &meta);
        if (err != KOME_OK) return err;

        err = engine->log->update_version_vector(meta.author, meta.seq);
        if (err != KOME_OK) return err;

        if (meta_out) *meta_out = meta;
        sync = engine->sync_mgr;
    }

    if (sync)
        sync->on_local_write(kome::Entry::from_meta(meta, ns, key, key_len, value, value_len));

    return KOME_OK;
}

KOME_API KomeError kome_put_batch(KomeEngine *engine,
    const KomeBatchEntry *entries, size_t count,
    KomeEntryMeta *metas_out)
{
    if (!engine || !entries || count == 0) return KOME_ERR_MISUSE;
    if (count > KOME_MAX_BATCH_COUNT) return KOME_ERR_TOO_LARGE;

    /* Validate all entries before acquiring the lock */
    for (size_t i = 0; i < count; i++) {
        if (!entries[i].ns || !entries[i].key || !entries[i].value)
            return KOME_ERR_MISUSE;
        size_t ns_len = std::strlen(entries[i].ns);
        if (ns_len == 0 || ns_len > KOME_MAX_NS_LEN) return KOME_ERR_TOO_LARGE;
        if (entries[i].key_len == 0 || entries[i].key_len > KOME_MAX_KEY_LEN)
            return KOME_ERR_TOO_LARGE;
        if (entries[i].value_len > KOME_MAX_VALUE_LEN) return KOME_ERR_TOO_LARGE;
    }

    std::vector<KomeEntryMeta> metas(count);
    std::shared_ptr<kome::KomeSyncManager> sync;
    {
        std::lock_guard<std::mutex> lock(engine->mu);
        if (engine->closed.load(std::memory_order_acquire)) return KOME_ERR_MISUSE;
        if (!engine->identity_set) return KOME_ERR_MISUSE;

        KomeError err = engine->log->begin_transaction();
        if (err != KOME_OK) return err;

        uint64_t base_ts = kome::timestamp_us();
        for (size_t i = 0; i < count; i++) {
            auto &e = entries[i];
            auto &meta = metas[i];

            meta.timestamp_us = base_ts;
            std::memcpy(meta.author, engine->identity, 32);
            meta.seq = engine->next_seq++;
            kome::sha256(e.value, e.value_len, meta.hash);
            meta.value_len = (uint32_t)e.value_len;
            meta.tombstone = 0;

            err = engine->log->put_entry(e.ns, e.key, e.key_len,
                                          e.value, e.value_len, &meta);
            if (err != KOME_OK) {
                engine->log->rollback_transaction();
                engine->next_seq -= (i + 1);
                return err;
            }

            err = engine->log->update_version_vector(meta.author, meta.seq);
            if (err != KOME_OK) {
                engine->log->rollback_transaction();
                engine->next_seq -= (i + 1);
                return err;
            }
        }

        err = engine->log->commit_transaction();
        if (err != KOME_OK) {
            engine->log->rollback_transaction();
            engine->next_seq -= count;
            return err;
        }

        if (metas_out) {
            for (size_t i = 0; i < count; i++)
                metas_out[i] = metas[i];
        }
        sync = engine->sync_mgr;
    }

    if (sync) {
        std::vector<kome::LogEntry> log_entries;
        log_entries.reserve(count);
        for (size_t i = 0; i < count; i++) {
            log_entries.push_back(kome::Entry::from_meta(
                metas[i], entries[i].ns,
                entries[i].key, entries[i].key_len,
                entries[i].value, entries[i].value_len));
        }
        sync->on_local_write_batch(log_entries);
    }

    return KOME_OK;
}

KOME_API KomeError kome_delete(KomeEngine *engine,
    const char *ns, const uint8_t *key, size_t key_len,
    KomeEntryMeta *meta_out)
{
    if (!engine || !ns || !key) return KOME_ERR_MISUSE;

    size_t ns_len = std::strlen(ns);
    if (ns_len == 0 || ns_len > KOME_MAX_NS_LEN) return KOME_ERR_TOO_LARGE;
    if (key_len == 0 || key_len > KOME_MAX_KEY_LEN) return KOME_ERR_TOO_LARGE;

    KomeEntryMeta meta;
    std::shared_ptr<kome::KomeSyncManager> sync;
    {
        std::lock_guard<std::mutex> lock(engine->mu);
        if (engine->closed.load(std::memory_order_acquire)) return KOME_ERR_MISUSE;
        if (!engine->identity_set) return KOME_ERR_MISUSE;

        meta.timestamp_us = kome::timestamp_us();
        std::memcpy(meta.author, engine->identity, 32);
        meta.seq = engine->next_seq++;
        std::memset(meta.hash, 0, 32);
        meta.value_len = 0;
        meta.tombstone = 1;

        KomeError err = engine->log->delete_entry(ns, key, key_len, &meta);
        if (err != KOME_OK) return err;

        err = engine->log->update_version_vector(meta.author, meta.seq);
        if (err != KOME_OK) return err;

        if (meta_out) *meta_out = meta;
        sync = engine->sync_mgr;
    }

    if (sync)
        sync->on_local_write(kome::Entry::from_meta(meta, ns, key, key_len, nullptr, 0));

    return KOME_OK;
}

KOME_API KomeError kome_get(KomeEngine *engine,
    const char *ns, const uint8_t *key, size_t key_len,
    uint8_t **value_out, size_t *value_len_out,
    KomeEntryMeta *meta_out)
{
    if (!engine || !ns || !key || !value_out || !value_len_out) return KOME_ERR_MISUSE;

    std::lock_guard<std::mutex> lock(engine->mu);
    if (engine->closed.load(std::memory_order_acquire)) return KOME_ERR_MISUSE;

    kome::LogEntry entry;
    KomeError err = engine->log->get_entry(ns, key, key_len, &entry);
    if (err != KOME_OK) return err;

    if (entry.tombstone) {
        *value_out = nullptr;
        *value_len_out = 0;
        if (meta_out) entry.to_meta(meta_out);
        return KOME_ERR_NOT_FOUND;
    }

    if (meta_out) entry.to_meta(meta_out);

    if (entry.value.empty()) {
        *value_out = nullptr;
        *value_len_out = 0;
    } else {
        auto *buf = (uint8_t*)std::malloc(entry.value.size());
        if (!buf) return KOME_ERR_INTERNAL;
        std::memcpy(buf, entry.value.data(), entry.value.size());
        *value_out = buf;
        *value_len_out = entry.value.size();
    }

    return KOME_OK;
}

KOME_API void kome_free_value(uint8_t *value) {
    std::free(value);
}

KOME_API KomeError kome_get_meta(KomeEngine *engine,
    const char *ns, const uint8_t *key, size_t key_len,
    KomeEntryMeta *meta_out)
{
    if (!engine || !ns || !key || !meta_out) return KOME_ERR_MISUSE;

    std::lock_guard<std::mutex> lock(engine->mu);
    if (engine->closed.load(std::memory_order_acquire)) return KOME_ERR_MISUSE;

    kome::LogEntry entry;
    KomeError err = engine->log->get_entry(ns, key, key_len, &entry);
    if (err != KOME_OK) return err;

    entry.to_meta(meta_out);

    return KOME_OK;
}

KOME_API KomeError kome_attach_transport(KomeEngine *engine, KomeTransport *transport) {
    if (!engine || !transport) return KOME_ERR_MISUSE;

    std::lock_guard<std::mutex> lock(engine->mu);
    if (engine->closed.load(std::memory_order_acquire)) return KOME_ERR_MISUSE;

    engine->transport = transport;
    engine->sync_mgr.reset();

    engine->sync_mgr = std::make_shared<kome::KomeSyncManager>(engine);
    engine->sync_mgr->set_transport(transport);

    return KOME_OK;
}

KOME_API KomeError kome_sync_with(KomeEngine *engine, const uint8_t *peer_fp) {
    if (!engine || !peer_fp) return KOME_ERR_MISUSE;
    if (engine->closed.load(std::memory_order_acquire)) return KOME_ERR_MISUSE;

    std::shared_ptr<kome::KomeSyncManager> sync;
    {
        std::lock_guard<std::mutex> lock(engine->mu);
        if (engine->closed.load(std::memory_order_acquire)) return KOME_ERR_MISUSE;
        sync = engine->sync_mgr;
    }
    if (!sync) return KOME_ERR_MISUSE;
    /* No-op if peer is already syncing or in live mode */
    if (!sync->is_peer_idle(peer_fp)) return KOME_OK;
    sync->initiate_sync(peer_fp);
    return KOME_OK;
}

KOME_API KomeError kome_set_sync_namespaces(KomeEngine *engine,
    const char **namespaces, size_t count)
{
    if (!engine) return KOME_ERR_MISUSE;
    if (count > 0 && !namespaces) return KOME_ERR_MISUSE;

    std::lock_guard<std::mutex> lock(engine->mu);
    engine->sync_namespaces.clear();
    for (size_t i = 0; i < count; i++) {
        if (!namespaces[i]) return KOME_ERR_MISUSE;
        engine->sync_namespaces.emplace_back(namespaces[i]);
    }
    return KOME_OK;
}

KOME_API KomeError kome_set_entry_ttl(KomeEngine *engine,
    const char *ns, uint64_t ttl_sec)
{
    if (!engine || !ns) return KOME_ERR_MISUSE;

    std::lock_guard<std::mutex> lock(engine->mu);
    KomeError err = engine->log->set_entry_ttl(ns, ttl_sec);
    if (err != KOME_OK) return err;

    if (ttl_sec > 0)
        engine->entry_ttls[ns] = ttl_sec;
    else
        engine->entry_ttls.erase(ns);
    return KOME_OK;
}

KOME_API KomeError kome_version_vector(KomeEngine *engine,
    KomeVersionEntry **entries_out, size_t *count_out)
{
    if (!engine || !entries_out || !count_out) return KOME_ERR_MISUSE;

    std::lock_guard<std::mutex> lock(engine->mu);

    std::map<std::string, uint64_t> vv;
    KomeError err = engine->log->get_version_vector(vv);
    if (err != KOME_OK) return err;

    size_t count = vv.size();
    if (count == 0) {
        *entries_out = nullptr;
        *count_out = 0;
        return KOME_OK;
    }

    if (count > SIZE_MAX / sizeof(KomeVersionEntry)) return KOME_ERR_INTERNAL;
    auto *entries = (KomeVersionEntry*)std::malloc(count * sizeof(KomeVersionEntry));
    if (!entries) return KOME_ERR_INTERNAL;

    size_t i = 0;
    for (auto &[author, seq] : vv) {
        if (author.size() >= 32) {
            std::memcpy(entries[i].author, author.data(), 32);
        } else {
            std::memset(entries[i].author, 0, 32);
            std::memcpy(entries[i].author, author.data(), author.size());
        }
        entries[i].seq = seq;
        i++;
    }

    *entries_out = entries;
    *count_out = count;
    return KOME_OK;
}

KOME_API void kome_free_version_vector(KomeVersionEntry *entries) {
    std::free(entries);
}

KOME_API KomeError kome_list_namespaces(KomeEngine *engine,
    char ***ns_out, size_t *count_out)
{
    if (!engine || !ns_out || !count_out) return KOME_ERR_MISUSE;

    std::lock_guard<std::mutex> lock(engine->mu);

    std::vector<std::string> namespaces;
    KomeError err = engine->log->list_namespaces(namespaces);
    if (err != KOME_OK) return err;

    size_t count = namespaces.size();
    if (count == 0) {
        *ns_out = nullptr;
        *count_out = 0;
        return KOME_OK;
    }

    if (count > SIZE_MAX / sizeof(char*)) return KOME_ERR_INTERNAL;
    auto **list = (char**)std::malloc(count * sizeof(char*));
    if (!list) return KOME_ERR_INTERNAL;

    for (size_t i = 0; i < count; i++) {
        list[i] = (char*)std::malloc(namespaces[i].size() + 1);
        if (!list[i]) {
            for (size_t j = 0; j < i; j++) std::free(list[j]);
            std::free(list);
            return KOME_ERR_INTERNAL;
        }
        std::memcpy(list[i], namespaces[i].c_str(), namespaces[i].size() + 1);
    }

    *ns_out = list;
    *count_out = count;
    return KOME_OK;
}

KOME_API void kome_free_namespaces(char **ns_list, size_t count) {
    if (!ns_list) return;
    for (size_t i = 0; i < count; i++) std::free(ns_list[i]);
    std::free(ns_list);
}

KOME_API KomeError kome_list_keys(KomeEngine *engine, const char *ns,
    uint8_t ***keys_out, size_t **key_lens_out, size_t *count_out)
{
    if (!engine || !ns || !keys_out || !key_lens_out || !count_out)
        return KOME_ERR_MISUSE;

    std::lock_guard<std::mutex> lock(engine->mu);
    if (engine->closed.load(std::memory_order_acquire)) return KOME_ERR_MISUSE;

    std::vector<std::vector<uint8_t>> keys;
    KomeError err = engine->log->list_keys(ns, keys);
    if (err != KOME_OK) return err;

    size_t count = keys.size();
    if (count == 0) {
        *keys_out = nullptr;
        *key_lens_out = nullptr;
        *count_out = 0;
        return KOME_OK;
    }

    if (count > SIZE_MAX / sizeof(uint8_t*)) return KOME_ERR_INTERNAL;
    auto **kptrs = (uint8_t**)std::malloc(count * sizeof(uint8_t*));
    auto *klens  = (size_t*)std::malloc(count * sizeof(size_t));
    if (!kptrs || !klens) {
        std::free(kptrs);
        std::free(klens);
        return KOME_ERR_INTERNAL;
    }

    for (size_t i = 0; i < count; i++) {
        klens[i] = keys[i].size();
        /* Allocate at least 1 byte to avoid implementation-defined malloc(0) */
        kptrs[i] = (uint8_t*)std::malloc(klens[i] > 0 ? klens[i] : 1);
        if (!kptrs[i]) {
            for (size_t j = 0; j < i; j++) std::free(kptrs[j]);
            std::free(kptrs);
            std::free(klens);
            return KOME_ERR_INTERNAL;
        }
        if (klens[i] > 0)
            std::memcpy(kptrs[i], keys[i].data(), klens[i]);
    }

    *keys_out = kptrs;
    *key_lens_out = klens;
    *count_out = count;
    return KOME_OK;
}

KOME_API KomeError kome_get_all(KomeEngine *engine, const char *ns,
    uint8_t ***keys_out, size_t **key_lens_out,
    uint8_t ***values_out, size_t **value_lens_out,
    KomeEntryMeta **metas_out, size_t *count_out)
{
    if (!engine || !ns || !keys_out || !key_lens_out ||
        !values_out || !value_lens_out || !metas_out || !count_out)
        return KOME_ERR_MISUSE;

    std::lock_guard<std::mutex> lock(engine->mu);
    if (engine->closed.load(std::memory_order_acquire)) return KOME_ERR_MISUSE;

    std::vector<kome::LogEntry> entries;
    KomeError err = engine->log->get_all_entries(ns, entries);
    if (err != KOME_OK) return err;

    size_t count = entries.size();
    if (count == 0) {
        *keys_out = nullptr;
        *key_lens_out = nullptr;
        *values_out = nullptr;
        *value_lens_out = nullptr;
        *metas_out = nullptr;
        *count_out = 0;
        return KOME_OK;
    }

    if (count > SIZE_MAX / sizeof(KomeEntryMeta)) return KOME_ERR_INTERNAL;
    auto **kptrs = (uint8_t**)std::malloc(count * sizeof(uint8_t*));
    auto *klens  = (size_t*)std::malloc(count * sizeof(size_t));
    auto **vptrs = (uint8_t**)std::malloc(count * sizeof(uint8_t*));
    auto *vlens  = (size_t*)std::malloc(count * sizeof(size_t));
    auto *metas  = (KomeEntryMeta*)std::malloc(count * sizeof(KomeEntryMeta));
    if (!kptrs || !klens || !vptrs || !vlens || !metas) {
        std::free(kptrs);
        std::free(klens);
        std::free(vptrs);
        std::free(vlens);
        std::free(metas);
        return KOME_ERR_INTERNAL;
    }

    for (size_t i = 0; i < count; i++) {
        auto &e = entries[i];

        klens[i] = e.key.size();
        kptrs[i] = (uint8_t*)std::malloc(klens[i] > 0 ? klens[i] : 1);
        if (!kptrs[i]) {
            for (size_t j = 0; j < i; j++) { std::free(kptrs[j]); std::free(vptrs[j]); }
            std::free(kptrs); std::free(klens);
            std::free(vptrs); std::free(vlens);
            std::free(metas);
            return KOME_ERR_INTERNAL;
        }
        if (klens[i] > 0)
            std::memcpy(kptrs[i], e.key.data(), klens[i]);

        vlens[i] = e.value.size();
        if (vlens[i] > 0) {
            vptrs[i] = (uint8_t*)std::malloc(vlens[i]);
            if (!vptrs[i]) {
                std::free(kptrs[i]);
                for (size_t j = 0; j < i; j++) { std::free(kptrs[j]); std::free(vptrs[j]); }
                std::free(kptrs); std::free(klens);
                std::free(vptrs); std::free(vlens);
                std::free(metas);
                return KOME_ERR_INTERNAL;
            }
            std::memcpy(vptrs[i], e.value.data(), vlens[i]);
        } else {
            vptrs[i] = nullptr;
        }

        e.to_meta(&metas[i]);
    }

    *keys_out = kptrs;
    *key_lens_out = klens;
    *values_out = vptrs;
    *value_lens_out = vlens;
    *metas_out = metas;
    *count_out = count;
    return KOME_OK;
}

KOME_API void kome_free_entries(uint8_t **keys, size_t *key_lens,
    uint8_t **values, size_t *value_lens,
    KomeEntryMeta *metas, size_t count)
{
    if (keys) {
        for (size_t i = 0; i < count; i++) std::free(keys[i]);
        std::free(keys);
    }
    std::free(key_lens);
    if (values) {
        for (size_t i = 0; i < count; i++) std::free(values[i]);
        std::free(values);
    }
    std::free(value_lens);
    std::free(metas);
}

KOME_API void kome_free_keys(uint8_t **keys, size_t *key_lens, size_t count) {
    if (keys) {
        for (size_t i = 0; i < count; i++) std::free(keys[i]);
        std::free(keys);
    }
    std::free(key_lens);
}

KOME_API void kome_on_remote_change(KomeEngine *engine, KomeRemoteChangeCallback cb, void *ud) {
    if (!engine) return;
    std::lock_guard<std::mutex> lock(engine->mu);
    engine->on_remote_change_cb = cb;
    engine->on_remote_change_ud = ud;
}

KOME_API void kome_on_remote_change_ns(KomeEngine *engine, const char *ns,
    KomeRemoteChangeCallback cb, void *ud) {
    if (!engine || !ns) return;
    std::lock_guard<std::mutex> lock(engine->mu);
    if (cb) {
        engine->ns_change_cbs[ns] = {cb, ud};
    } else {
        engine->ns_change_cbs.erase(ns);
    }
}

KOME_API void kome_on_conflict(KomeEngine *engine, KomeConflictCallback cb, void *ud) {
    if (!engine) return;
    std::lock_guard<std::mutex> lock(engine->mu);
    engine->on_conflict_cb = cb;
    engine->on_conflict_ud = ud;
}

KOME_API void kome_on_sync_done(KomeEngine *engine, KomeSyncDoneCallback cb, void *ud) {
    if (!engine) return;
    std::lock_guard<std::mutex> lock(engine->mu);
    engine->on_sync_done_cb = cb;
    engine->on_sync_done_ud = ud;
}

KOME_API void kome_on_sync_progress(KomeEngine *engine, KomeSyncProgressCallback cb, void *ud) {
    if (!engine) return;
    std::lock_guard<std::mutex> lock(engine->mu);
    engine->on_sync_progress_cb = cb;
    engine->on_sync_progress_ud = ud;
}

KOME_API KomeError kome_stats(KomeEngine *engine, KomeStats *out) {
    if (!engine || !out) return KOME_ERR_MISUSE;
    std::lock_guard<std::mutex> lock(engine->mu);
    return engine->log->get_stats(out);
}

KOME_API const char *kome_errstr(KomeError err) {
    switch (err) {
        case KOME_OK:            return "OK";
        case KOME_ERR_MISUSE:    return "misuse of API";
        case KOME_ERR_STORAGE:   return "storage error";
        case KOME_ERR_TRANSPORT: return "transport error";
        case KOME_ERR_NOT_FOUND: return "not found";
        case KOME_ERR_TOO_LARGE: return "too large";
        case KOME_ERR_INTERNAL:  return "internal error";
    }
    return "unknown error";
}

KOME_API const char *kome_version(void) {
    return KOME_VERSION_STR;
}

} /* extern "C" */
