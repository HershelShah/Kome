/*
 * KomeEasy — Simplified API for the Kome P2P replication library
 *
 * Provides a one-call setup with optional built-in HTTP relay transport.
 * Pure C API (C99 compatible).
 *
 * Quick start:
 *   KomeEasy *easy;
 *   kome_easy_open("my.db", "http://relay.example.com", key, 32, &easy);
 *   kome_easy_put(easy, "contacts", "alice", 5, vcard, vcard_len);
 *   kome_easy_close(easy);
 */
#ifndef KOME_EASY_H
#define KOME_EASY_H

#include "kome.h"

#ifdef __cplusplus
extern "C" {
#endif

/* --- Opaque handle ------------------------------------------------------ */

typedef struct KomeEasy KomeEasy;

/* --- Lifecycle ---------------------------------------------------------- */

/*
 * Open a Kome instance with optional relay transport.
 *
 * db_path:      SQLite database path (required)
 * relay_url:    HTTP relay server URL, e.g. "http://relay.example.com"
 *               Pass NULL for local-only mode (no networking).
 * key_material: Identity key material — SHA-256'd to produce fingerprint
 * key_len:      Length of key_material in bytes (must be > 0)
 * out:          Receives the new KomeEasy handle on success
 *
 * Returns KOME_OK on success, or an error code.
 */
KOME_API KomeError kome_easy_open(const char *db_path, const char *relay_url,
    const uint8_t *key_material, size_t key_len,
    KomeEasy **out);

/*
 * Close and free all resources. Safe to call with NULL.
 */
KOME_API void kome_easy_close(KomeEasy *easy);

/* --- Data operations ---------------------------------------------------- */

/*
 * Write a key-value pair into a namespace.
 */
KOME_API KomeError kome_easy_put(KomeEasy *easy, const char *ns,
    const uint8_t *key, size_t key_len,
    const uint8_t *value, size_t value_len);

/*
 * Read a value. Caller must free *value_out with kome_free_value().
 * Returns KOME_ERR_NOT_FOUND if the key does not exist or is deleted.
 */
KOME_API KomeError kome_easy_get(KomeEasy *easy, const char *ns,
    const uint8_t *key, size_t key_len,
    uint8_t **value_out, size_t *value_len_out);

/*
 * Delete a key (writes a tombstone).
 */
KOME_API KomeError kome_easy_delete(KomeEasy *easy, const char *ns,
    const uint8_t *key, size_t key_len);

/* --- Callbacks ---------------------------------------------------------- */

/*
 * Register a callback for remote changes (from any namespace).
 * Pass cb=NULL to unregister.
 */
KOME_API void kome_easy_on_change(KomeEasy *easy, KomeRemoteChangeCallback cb,
    void *ud);

/* --- Advanced access ---------------------------------------------------- */

/*
 * Get the underlying KomeEngine for advanced operations
 * (namespace config, replication targets, version vectors, etc.).
 * The returned pointer is valid until kome_easy_close().
 */
KOME_API KomeEngine *kome_easy_engine(KomeEasy *easy);

#ifdef __cplusplus
}
#endif

#endif /* KOME_EASY_H */
