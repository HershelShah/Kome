/* sync_engine.h — P2P Replication Engine public C ABI.
 *
 * Milestone M1: convergent core (in memory).
 *   - Hybrid Logical Clock (HLC)
 *   - LWW register (per field)
 *   - Causal-length set (per entity existence/deletion)
 *   - Full-state replication baseline: export / apply
 *   - Deterministic state digest
 *
 * Conventions:
 *   - All multi-byte integers crossing this boundary are passed as host
 *     scalars; the portable, endianness-explicit wire form is the M3 codec.
 *   - Byte strings (namespace / entity / field / value) are length-prefixed
 *     pointer+length pairs and may contain embedded NUL bytes.
 *   - No C++ exception ever crosses this boundary; every function returns a
 *     sync_error code (or NULL for constructors) on failure.
 *   - Memory ownership is documented per function. Buffers handed back to the
 *     caller are released with sync_free; change arrays with sync_changes_free.
 */
#ifndef SYNC_ENGINE_H
#define SYNC_ENGINE_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ABI version. Pre-1.0: breaking changes bump this and update all bindings.
 *   1 — M1 convergent in-memory core
 *   2 — M2 durable storage (sync_engine_open / sync_engine_flush)
 *   3 — M3 codec + range-based reconciliation session */
#define SYNC_ABI_VERSION 3u

/* Identity length. 32 bytes from the start: in M4 a site_id is the
 * BLAKE2b-256 of a signing public key. (The plan widens 16->32 in M2; we
 * adopt the final width immediately — see DECISIONS.md.) */
#define SYNC_SITE_ID_LEN 32u

/* Deterministic state digest length (SHA-256). */
#define SYNC_DIGEST_LEN 32u

/* Error codes. Returned by every fallible extern "C" function. */
typedef enum sync_error {
    SYNC_OK            = 0,
    SYNC_ERR_INVALID   = 1, /* NULL / malformed argument */
    SYNC_ERR_NOMEM     = 2, /* allocation failed */
    SYNC_ERR_NOTFOUND  = 3, /* key/field absent or entity not present */
    SYNC_ERR_INTERNAL  = 4  /* unexpected internal failure */
} sync_error;

/* A hybrid logical clock timestamp. physical is wall-clock milliseconds
 * since the Unix epoch; logical disambiguates events within the same ms. */
typedef struct sync_hlc {
    uint64_t physical;
    uint32_t logical;
} sync_hlc;

/* Kind of a change record. */
typedef enum sync_change_kind {
    SYNC_CHANGE_EXISTENCE = 0, /* causal-length set element (entity presence) */
    SYNC_CHANGE_REGISTER  = 1  /* LWW register element (one field value)      */
} sync_change_kind;

/* A single change record — the unit of replication.
 *
 * For SYNC_CHANGE_EXISTENCE: (ns, entity, causal_length) are meaningful;
 *   field/value/hlc/site_id are unused.
 * For SYNC_CHANGE_REGISTER: (ns, entity, field, value, hlc, site_id) are
 *   meaningful; causal_length is unused.
 *
 * Pointer fields are borrowed for the duration of a call (apply copies what
 * it needs). Records produced by sync_engine_export own their buffers and
 * must be released with sync_changes_free. */
typedef struct sync_change {
    uint8_t        kind; /* sync_change_kind */

    const uint8_t *ns;     size_t ns_len;
    const uint8_t *entity; size_t entity_len;
    const uint8_t *field;  size_t field_len;  /* REGISTER only */

    uint64_t       causal_length;             /* EXISTENCE only */

    const uint8_t *value;  size_t value_len;  /* REGISTER only */
    sync_hlc       hlc;                        /* REGISTER only */
    uint8_t        site_id[SYNC_SITE_ID_LEN]; /* REGISTER only */
} sync_change;

/* Opaque engine handle. All state lives here; no global mutable state. */
typedef struct sync_engine sync_engine;

/* ---- Lifecycle ---------------------------------------------------------- */

/* Create an in-memory engine with the given site identity.
 * Returns NULL on allocation failure or if site_id is NULL. */
sync_engine *sync_engine_create(const uint8_t site_id[SYNC_SITE_ID_LEN]);

/* Open (creating if needed) a durable engine backed by the SQLite file at
 * path. State is loaded on open and written through on every mutation. For a
 * fresh file, site_id becomes the persisted identity; for an existing file the
 * persisted identity is used and site_id is ignored. Returns NULL on failure
 * (including an unknown/newer on-disk schema version). */
sync_engine *sync_engine_open(const char *path,
                              const uint8_t site_id[SYNC_SITE_ID_LEN]);

/* Flush durable state to disk. With write-through this is a no-op safety net;
 * a no-op for in-memory engines. Returns SYNC_OK on success. */
int sync_engine_flush(sync_engine *e);

/* Destroy an engine. For durable engines this also closes the database.
 * Safe to call with NULL. */
void sync_engine_destroy(sync_engine *e);

/* Copy this engine's site identity into out. */
int sync_engine_site_id(sync_engine *e, uint8_t out[SYNC_SITE_ID_LEN]);

/* ---- Local operations --------------------------------------------------- */

/* Set field=value on (ns, entity). Creates/ensures the entity is present
 * (causal-length set add when absent) and updates the field's LWW register
 * with a freshly ticked HLC. value may be empty (value_len == 0). */
int sync_engine_set(sync_engine *e,
                    const uint8_t *ns, size_t ns_len,
                    const uint8_t *entity, size_t entity_len,
                    const uint8_t *field, size_t field_len,
                    const uint8_t *value, size_t value_len);

/* Mark (ns, entity) deleted (causal-length set remove). Field registers are
 * retained but hidden; see sync_engine_get / sync_engine_exists. */
int sync_engine_delete(sync_engine *e,
                       const uint8_t *ns, size_t ns_len,
                       const uint8_t *entity, size_t entity_len);

/* ---- Reads -------------------------------------------------------------- */

/* Read field value of (ns, entity). Returns SYNC_OK and a malloc'd buffer in
 * *out_value (length *out_len) when the entity is present and the field
 * exists; SYNC_ERR_NOTFOUND otherwise. *out_value is set to NULL on not-found.
 * Release the buffer with sync_free. An empty value yields a non-NULL,
 * zero-length buffer. */
int sync_engine_get(sync_engine *e,
                    const uint8_t *ns, size_t ns_len,
                    const uint8_t *entity, size_t entity_len,
                    const uint8_t *field, size_t field_len,
                    uint8_t **out_value, size_t *out_len);

/* Set *out_exists to 1 if (ns, entity) is currently present, else 0. */
int sync_engine_exists(sync_engine *e,
                       const uint8_t *ns, size_t ns_len,
                       const uint8_t *entity, size_t entity_len,
                       int *out_exists);

/* ---- Full-state replication baseline (the oracle) ----------------------- */

/* Export the entire current state as change records. On success *out points
 * to *out_count records (owning their buffers); release with
 * sync_changes_free. *out may be NULL when *out_count == 0. */
int sync_engine_export(sync_engine *e, sync_change **out, size_t *out_count);

/* Release an array returned by sync_engine_export. Safe with NULL. */
void sync_changes_free(sync_change *arr, size_t count);

/* Merge a single change record into the engine (idempotent, commutative,
 * associative). Borrows c for the duration of the call. */
int sync_engine_apply(sync_engine *e, const sync_change *c);

/* ---- Digest ------------------------------------------------------------- */

/* Compute a deterministic digest of the full current state (including hidden
 * registers under tombstones). Two engines that have merged the same set of
 * records produce identical digests regardless of order. */
int sync_engine_digest(sync_engine *e, uint8_t out[SYNC_DIGEST_LEN]);

/* ---- Codec (M3): canonical, little-endian, versioned record bytes -------- */

/* Encode c into buf. Returns the number of bytes the encoding requires; writes
 * into buf only when buf_len is large enough (call with buf==NULL to size).
 * Returns 0 on invalid input. */
size_t sync_change_encode(const sync_change *c, uint8_t *buf, size_t buf_len);

/* Decode one record from buf[0,len). On success fills *out (which owns its
 * buffers) and, if consumed!=NULL, sets *consumed to bytes read. Release the
 * decoded record with sync_change_free_decoded. */
int sync_change_decode(const uint8_t *buf, size_t len, sync_change *out,
                       size_t *consumed);

/* Release buffers owned by a record filled by sync_change_decode. Safe with
 * NULL; does not free the sync_change struct itself. */
void sync_change_free_decoded(sync_change *c);

/* ---- Reconciliation session (M3): sync only the difference --------------- */

/* A transport-agnostic, range-based set-reconciliation session. Drive it by
 * pumping opaque messages between two peers until both report done. */
typedef struct sync_session sync_session;

/* Begin a session against engine e. Exactly one peer passes as_initiator=1;
 * the initiator produces the first message (call step with in_len==0). */
sync_session *sync_session_begin(sync_engine *e, int as_initiator);

/* Process an incoming message (in,in_len) and produce the next outgoing
 * message in *out (length *out_len; malloc'd, release with sync_free; may be
 * NULL when *out_len==0). Sets *done to 1 when this peer has nothing further to
 * send. For the initiator's first call, pass in=NULL,in_len=0. */
int sync_session_step(sync_session *s, const uint8_t *in, size_t in_len,
                      uint8_t **out, size_t *out_len, int *done);

/* End a session and release its resources. Safe with NULL. */
void sync_session_end(sync_session *s);

/* ---- Misc --------------------------------------------------------------- */

/* Release a buffer returned by sync_engine_get. Safe with NULL. */
void sync_free(void *p);

/* Human-readable string for a sync_error code. Never NULL. */
const char *sync_strerror(int err);

/* Return SYNC_ABI_VERSION at runtime. */
uint32_t sync_abi_version(void);

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* SYNC_ENGINE_H */
