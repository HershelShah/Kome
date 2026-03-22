/*
 * Kome — Peer-to-peer data replication middleware
 * C99 public API
 *
 * Quick start:
 *   KomeConfig cfg = {0};
 *   cfg.path = "my.db";
 *   KomeEngine *e;
 *   kome_open(&cfg, &e);
 *   kome_set_identity(e, key_bytes, 32);
 *   kome_put(e, "contacts", "alice", 5, vcard, vcard_len, NULL);
 *   kome_close(e);
 *
 * Thread safety: All functions are safe to call concurrently on the same
 * KomeEngine. Callbacks are invoked WITHOUT the engine lock held — they
 * MAY call back into the kome API.
 */
#ifndef KOME_H
#define KOME_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* --- Visibility --------------------------------------------------------- */

#if defined(_WIN32) || defined(__CYGWIN__)
  #ifdef KOME_BUILDING
    #define KOME_API __declspec(dllexport)
  #else
    #define KOME_API __declspec(dllimport)
  #endif
#elif defined(__GNUC__) || defined(__clang__)
  #define KOME_API __attribute__((visibility("default")))
#else
  #define KOME_API
#endif

/* --- Constants ---------------------------------------------------------- */

#define KOME_PROTOCOL_VERSION  2
#define KOME_MAX_NS_LEN      255
#define KOME_MAX_KEY_LEN      512
#define KOME_MAX_VALUE_LEN    (16 * 1024 * 1024)  /* 16 MiB */
#define KOME_MAX_BATCH_COUNT  1000
#define KOME_MAX_CLOCK_DRIFT_US (24ULL * 3600 * 1000000)  /* 24 h in microseconds */

/* --- Error codes -------------------------------------------------------- */

typedef enum {
    KOME_OK            = 0,
    KOME_ERR_MISUSE    = 1,  /* NULL arg, wrong call order, no identity set */
    KOME_ERR_STORAGE   = 2,  /* SQLite failure */
    KOME_ERR_TRANSPORT = 3,  /* Transport-level failure */
    KOME_ERR_NOT_FOUND = 4,  /* Key does not exist */
    KOME_ERR_TOO_LARGE = 5,  /* ns/key/value exceeds size limit */
    KOME_ERR_INTERNAL  = 6   /* Allocation failure or unexpected state */
} KomeError;

/* --- Opaque handle ------------------------------------------------------ */

typedef struct KomeEngine KomeEngine;

/* --- Public structs ----------------------------------------------------- */

/* Metadata attached to every entry. Filled by kome_put, returned by kome_get. */
typedef struct {
    uint64_t timestamp_us;    /* Microsecond wall clock at write time      */
    uint8_t  author[32];      /* SHA-256 fingerprint of writing peer       */
    uint64_t seq;             /* Per-author monotonic sequence number      */
    uint8_t  hash[32];        /* SHA-256 of value content                  */
    uint32_t value_len;       /* Length of value in bytes                   */
    uint8_t  tombstone;       /* 1 = deleted                               */
} KomeEntryMeta;

/*
 * Engine configuration. Zero-init gives safe defaults:
 *   KomeConfig cfg = {0};
 *   cfg.path = "state.db";
 */
typedef struct {
    const char *path;           /* SQLite database path (required)            */
    int         disable_wal;    /* 1 = disable WAL (default: 0 = WAL on)     */
    int         busy_timeout_ms;/* SQLite busy timeout (default: 5000, 0=def) */

    /*
     * Optional encryption key for database-at-rest encryption via SQLCipher.
     * Set to a 32-byte key to enable; NULL (or zero length) to disable.
     *
     * With plain SQLite (not SQLCipher), PRAGMA key is silently ignored —
     * no encryption is performed. To get actual encryption, build with
     * -DKOME_USE_SQLCIPHER=ON and ensure libsqlcipher is installed.
     */
    const uint8_t *encryption_key;      /* 32-byte key, or NULL for none     */
    size_t         encryption_key_len;   /* must be 32 if key is provided     */
} KomeConfig;

typedef struct {
    uint8_t  author[32];
    uint64_t seq;
} KomeVersionEntry;

typedef struct {
    uint64_t total_entries;
    uint64_t tombstone_count;
    uint64_t namespace_count;
    uint64_t db_size_bytes;
} KomeStats;

/* --- Batch writes ------------------------------------------------------- */

typedef struct {
    const char    *ns;
    const uint8_t *key;
    size_t         key_len;
    const uint8_t *value;
    size_t         value_len;
} KomeBatchEntry;

/* --- Namespace configuration -------------------------------------------- */

typedef enum {
    KOME_ROLE_NONE  = 0,
    KOME_ROLE_READ  = 1,
    KOME_ROLE_WRITE = 2
} KomeRole;

typedef struct {
    uint8_t  fingerprint[32];
    KomeRole role;
} KomeNamespaceACLEntry;

typedef struct {
    const char            *name;
    uint64_t               tombstone_ttl_sec;  /* 0 = never GC tombstones   */
    KomeNamespaceACLEntry *acl;                /* peer access control list   */
    size_t                 acl_count;          /* 0 = owner-only (no repl)   */
} KomeNamespaceConfig;

/* --- Transport interface ------------------------------------------------ */

typedef struct KomeTransport KomeTransport;

typedef void (*KomeTransportSendFn)(KomeTransport *t, const uint8_t *peer_fp,
                                    const uint8_t *data, size_t len);
typedef void (*KomeTransportSetRecvFn)(KomeTransport *t,
    void (*cb)(void *ud, const uint8_t *peer_fp, const uint8_t *data, size_t len),
    void *ud);
typedef void (*KomeTransportSetPeerFn)(KomeTransport *t,
    void (*cb)(void *ud, const uint8_t *peer_fp, int connected),
    void *ud);

struct KomeTransport {
    KomeTransportSendFn     send;
    KomeTransportSetRecvFn  set_recv_callback;
    KomeTransportSetPeerFn  set_peer_callback;
    void                   *user_data;
};

/* --- Callbacks ---------------------------------------------------------- */

typedef enum {
    KOME_KEEP_LOCAL  = 0,
    KOME_KEEP_REMOTE = 1,
    KOME_MERGE       = 2
} KomeConflictChoice;

/*
 * Conflict callback. Called outside the engine lock — may call kome_* functions.
 * If choice is KOME_MERGE, allocate *merge_value_out with malloc().
 */
typedef KomeConflictChoice (*KomeConflictCallback)(
    void *ud,
    const char *ns, const uint8_t *key, size_t key_len,
    const KomeEntryMeta *local_meta,  const uint8_t *local_value,
    const KomeEntryMeta *remote_meta, const uint8_t *remote_value,
    uint8_t **merge_value_out, size_t *merge_value_len_out);

/* Fired when a remote peer's write is applied locally. */
typedef void (*KomeRemoteChangeCallback)(
    void *ud,
    const char *ns, const uint8_t *key, size_t key_len,
    const uint8_t *value, size_t value_len,
    const KomeEntryMeta *meta);

typedef void (*KomeSyncDoneCallback)(void *ud, const uint8_t *peer_fp);
typedef void (*KomeSyncProgressCallback)(
    void *ud, const uint8_t *peer_fp,
    uint64_t entries_received, uint64_t entries_total);
typedef void (*KomeReplicationChangeCallback)(
    void *ud, const char *ns, const uint8_t *key, size_t key_len,
    uint32_t confirmed_peers, uint32_t target_peers);

/* --- Log levels --------------------------------------------------------- */

typedef enum {
    KOME_LOG_NONE  = 0,
    KOME_LOG_ERROR = 1,
    KOME_LOG_WARN  = 2,
    KOME_LOG_INFO  = 3,
    KOME_LOG_DEBUG = 4
} KomeLogLevel;

/* ========================================================================
   Core API — the 8 functions most apps need
   ======================================================================== */

/* Open / close */
KOME_API KomeError kome_open(const KomeConfig *config, KomeEngine **out);
KOME_API void      kome_close(KomeEngine *engine);

/* Identity — call once after open, before any put/delete */
KOME_API KomeError kome_set_identity(KomeEngine *engine,
                                      const uint8_t *key_material, size_t len);

/* Rotate identity to new key material. Migrates all ACL entries from old
 * fingerprint to new fingerprint. Identity must already be set. */
KOME_API KomeError kome_rotate_identity(KomeEngine *engine,
    const uint8_t *new_key_material, size_t new_key_len);

/* Write a key-value pair. Syncs automatically to connected peers. */
KOME_API KomeError kome_put(KomeEngine *engine,
    const char *ns, const uint8_t *key, size_t key_len,
    const uint8_t *value, size_t value_len,
    KomeEntryMeta *meta_out);

/* Write multiple key-value pairs atomically. Syncs as a single batch.
 * All entries share one timestamp and receive consecutive sequence numbers.
 * count must be <= KOME_MAX_BATCH_COUNT.
 * If any entry fails validation the entire batch is rejected. */
KOME_API KomeError kome_put_batch(KomeEngine *engine,
    const KomeBatchEntry *entries, size_t count,
    KomeEntryMeta *metas_out);

/* Delete a key (writes a tombstone). */
KOME_API KomeError kome_delete(KomeEngine *engine,
    const char *ns, const uint8_t *key, size_t key_len,
    KomeEntryMeta *meta_out);

/* Read a value. Caller must kome_free_value() the returned buffer.
 * Returns KOME_ERR_NOT_FOUND for tombstoned (deleted) entries. */
KOME_API KomeError kome_get(KomeEngine *engine,
    const char *ns, const uint8_t *key, size_t key_len,
    uint8_t **value_out, size_t *value_len_out,
    KomeEntryMeta *meta_out);

/* Like kome_get but returns KOME_OK even for tombstoned entries.
 * Use this when you need to inspect tombstone metadata. */
KOME_API KomeError kome_get_with_tombstones(KomeEngine *engine,
    const char *ns, const uint8_t *key, size_t key_len,
    uint8_t **value_out, size_t *value_len_out,
    KomeEntryMeta *meta_out);

KOME_API void      kome_free_value(uint8_t *value);

/* React to writes from other peers */
KOME_API void kome_on_remote_change(KomeEngine *engine,
    KomeRemoteChangeCallback cb, void *ud);

/* React to writes from other peers in a specific namespace.
 * Pass cb = NULL to unregister. */
KOME_API void kome_on_remote_change_ns(KomeEngine *engine, const char *ns,
    KomeRemoteChangeCallback cb, void *ud);

/* ========================================================================
   Transport — attach a networking layer
   ======================================================================== */

KOME_API KomeError kome_attach_transport(KomeEngine *engine, KomeTransport *transport);

/* Initiate a sync handshake with the given peer.
 *
 * This function is non-blocking — it sends the initial SYNC_REQUEST message
 * and returns immediately.  It does NOT wait for the sync to complete.
 *
 * When both sides have finished exchanging entries the kome_on_sync_done
 * callback fires with the peer's fingerprint.
 *
 * Calling this on a peer that is already syncing or in live mode is a no-op
 * and returns KOME_OK.
 *
 * Requires: kome_attach_transport() must have been called first.
 */
KOME_API KomeError kome_sync_with(KomeEngine *engine, const uint8_t *peer_fp);

/* ========================================================================
   Advanced API — replication, introspection, tuning
   ======================================================================== */

/* Metadata-only read (no value copy) */
KOME_API KomeError kome_get_meta(KomeEngine *engine,
    const char *ns, const uint8_t *key, size_t key_len,
    KomeEntryMeta *meta_out);

/* Version vector */
KOME_API KomeError kome_version_vector(KomeEngine *engine,
    KomeVersionEntry **entries_out, size_t *count_out);
KOME_API void      kome_free_version_vector(KomeVersionEntry *entries);

/* Replication targets */
KOME_API KomeError kome_set_replication(KomeEngine *engine,
    const char *ns, uint32_t target_n);
KOME_API KomeError kome_replication_status(KomeEngine *engine,
    const char *ns, const uint8_t *key, size_t key_len,
    uint32_t *confirmed_out, uint32_t *target_out);

/* Namespace configuration */
KOME_API KomeError kome_configure_namespace(KomeEngine *engine,
    const KomeNamespaceConfig *config);
KOME_API KomeError kome_get_namespace_config(KomeEngine *engine,
    const char *ns, KomeNamespaceConfig *out);
KOME_API KomeError kome_remove_namespace(KomeEngine *engine, const char *ns);
KOME_API void      kome_free_namespace_config(KomeNamespaceConfig *config);

/* Namespace and key listing */
KOME_API KomeError kome_list_namespaces(KomeEngine *engine,
    char ***ns_out, size_t *count_out);
KOME_API void      kome_free_namespaces(char **ns_list, size_t count);

/* List all keys in a namespace. Each key is a (pointer, length) pair.
   Caller must kome_free_keys() the result. */
KOME_API KomeError kome_list_keys(KomeEngine *engine, const char *ns,
    uint8_t ***keys_out, size_t **key_lens_out, size_t *count_out);
KOME_API void      kome_free_keys(uint8_t **keys, size_t *key_lens, size_t count);

/* Read all key-value pairs in a namespace in one call.
   Tombstoned entries are excluded. Caller must kome_free_entries() the result. */
KOME_API KomeError kome_get_all(KomeEngine *engine, const char *ns,
    uint8_t ***keys_out, size_t **key_lens_out,
    uint8_t ***values_out, size_t **value_lens_out,
    KomeEntryMeta **metas_out, size_t *count_out);
KOME_API void      kome_free_entries(uint8_t **keys, size_t *key_lens,
    uint8_t **values, size_t *value_lens,
    KomeEntryMeta *metas, size_t count);

/* Additional callbacks */
KOME_API void kome_on_conflict(KomeEngine *engine,
    KomeConflictCallback cb, void *ud);
KOME_API void kome_on_sync_done(KomeEngine *engine,
    KomeSyncDoneCallback cb, void *ud);
KOME_API void kome_on_sync_progress(KomeEngine *engine,
    KomeSyncProgressCallback cb, void *ud);
KOME_API void kome_on_replication_change(KomeEngine *engine,
    KomeReplicationChangeCallback cb, void *ud);

/* Tuning */
KOME_API void      kome_set_log_level(KomeEngine *engine, KomeLogLevel level);

/* Per-peer write rate limiting.
 * Limits incoming writes from any single peer within a 60-second window.
 * Default: 50 MiB/min bytes, 1000 entries/min.
 * When a peer exceeds either limit, subsequent entries are dropped until
 * the window resets. */
KOME_API KomeError kome_set_peer_limits(KomeEngine *engine,
    uint64_t max_bytes_per_minute,
    uint64_t max_entries_per_minute);

/* Info */
KOME_API KomeError    kome_stats(KomeEngine *engine, KomeStats *out);
KOME_API const char  *kome_errstr(KomeError err);
KOME_API const char  *kome_version(void);

#ifdef __cplusplus
}
#endif

#endif /* KOME_H */
