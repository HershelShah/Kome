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
 *   3 — M3 codec + range-based reconciliation session
 *   4 — M4 identity + per-record signatures + capabilities */
#define SYNC_ABI_VERSION 4u

/* site_id length (BLAKE2b-256 of the signing public key). */
#define SYNC_SITE_ID_LEN 32u

/* Identity sizes. author = EdDSA signing public key; signature is over the
 * canonical record content (everything but the signature itself). */
#define SYNC_PUBKEY_LEN 32u
#define SYNC_SIG_LEN    64u

/* A 32-byte seed deterministically derives a replica's identity keypair. */
#define SYNC_SEED_LEN 32u

/* Deterministic state digest length (SHA-256). */
#define SYNC_DIGEST_LEN 32u

/* Error codes. Returned by every fallible extern "C" function. */
typedef enum sync_error {
    SYNC_OK              = 0,
    SYNC_ERR_INVALID     = 1, /* NULL / malformed argument */
    SYNC_ERR_NOMEM       = 2, /* allocation failed */
    SYNC_ERR_NOTFOUND    = 3, /* key/field absent or entity not present */
    SYNC_ERR_INTERNAL    = 4, /* unexpected internal failure */
    SYNC_ERR_BADSIG      = 5, /* record signature failed to verify */
    SYNC_ERR_UNAUTHORIZED = 6 /* author lacks a capability for the namespace */
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
 *   field/value/hlc are unused.
 * For SYNC_CHANGE_REGISTER: (ns, entity, field, value, hlc) are meaningful;
 *   causal_length is unused.
 *
 * Every record is authenticated: author is the writer's EdDSA signing public
 * key, and signature is an EdDSA signature over the canonical content. apply
 * rejects a record whose signature does not verify against author.
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

    uint8_t        author[SYNC_PUBKEY_LEN];   /* writer's signing public key */
    uint8_t        signature[SYNC_SIG_LEN];   /* EdDSA over canonical content */
} sync_change;

/* Opaque engine handle. All state lives here; no global mutable state. */
typedef struct sync_engine sync_engine;

/* ---- Lifecycle ---------------------------------------------------------- */

/* Create an in-memory engine whose identity keypair is derived from seed.
 * Returns NULL on allocation failure or if seed is NULL. */
sync_engine *sync_engine_create(const uint8_t seed[SYNC_SEED_LEN]);

/* Open (creating if needed) a durable engine backed by the append-only log at
 * path. State is loaded on open and written through on every mutation. For a
 * fresh file, seed establishes the persisted identity; for an existing file
 * the persisted identity is used and seed is ignored. Returns NULL on failure
 * (including an unknown/newer on-disk schema version). */
sync_engine *sync_engine_open(const char *path,
                              const uint8_t seed[SYNC_SEED_LEN]);

/* Like sync_engine_open, but the log is encrypted at rest: every frame is
 * sealed with XChaCha20-Poly1305 under the caller-supplied 32-byte key (derive
 * it from a passphrase via a KDF, or fetch it from an OS keystore — the engine
 * does not manage key derivation). Opening an existing encrypted log with the
 * wrong key fails cleanly (returns NULL); opening a plaintext log as encrypted
 * (or vice versa) also fails. The key is held in memory for the engine's
 * lifetime and wiped on destroy. */
sync_engine *sync_engine_open_encrypted(const char *path,
                                        const uint8_t seed[SYNC_SEED_LEN],
                                        const uint8_t key[32]);

/* Flush durable state to disk. With write-through this is a no-op safety net;
 * a no-op for in-memory engines. Returns SYNC_OK on success. */
int sync_engine_flush(sync_engine *e);

/* Destroy an engine. For durable engines this also closes the database.
 * Safe to call with NULL. */
void sync_engine_destroy(sync_engine *e);

/* Copy this engine's signing public key (its author identity) into out. */
int sync_engine_identity(sync_engine *e, uint8_t out[SYNC_PUBKEY_LEN]);

/* Copy this engine's site_id (BLAKE2b-256 of the signing public key). */
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

/* Sign an externally-constructed record in place: derives the identity keypair
 * from seed, sets c->author to its signing public key, and fills c->signature
 * with an EdDSA signature over the canonical content. Useful for tests and for
 * constructing records outside an engine. Returns SYNC_OK on success. */
int sync_change_sign(sync_change *c, const uint8_t seed[SYNC_SEED_LEN]);

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

/* Begin a session that is read-scoped to a specific peer: records in
 * namespaces the peer is not authorized to read are excluded from the snapshot
 * before any fingerprint is computed, so their existence never leaks. For
 * unowned (open) namespaces every peer may read. peer_pubkey is the peer's
 * signing public key (as authenticated by the channel). */
sync_session *sync_session_begin_scoped(sync_engine *e, int as_initiator,
                                        const uint8_t peer_pubkey[SYNC_PUBKEY_LEN]);

/* ---- Capabilities (M4): authorization ----------------------------------- */

#define SYNC_ACCESS_READ  1
#define SYNC_ACCESS_WRITE 2

/* An opaque capability token. */
typedef struct sync_capability sync_capability;

/* Create a self-signed root capability: owner becomes the namespace's owner
 * with the given access (bitmask of SYNC_ACCESS_*). Returns NULL on error.
 * Release with sync_capability_free. */
sync_capability *sync_capability_root(sync_engine *owner, const char *ns,
                                      int access);

/* Delegate a (narrower-or-equal) capability to subject_pubkey, signed by
 * delegator (which must be parent's subject). expiry_ms is a Unix-ms deadline
 * (0 = never). Returns NULL if delegator isn't the parent's subject or access
 * would widen the parent's. */
sync_capability *sync_capability_delegate(sync_engine *delegator,
                                          const sync_capability *parent,
                                          const uint8_t subject_pubkey[SYNC_PUBKEY_LEN],
                                          int access, uint64_t expiry_ms);

/* Serialize/deserialize a capability. encode returns the required size (writes
 * if buf fits; 0 on error). decode returns NULL on malformed input. */
int sync_capability_encode(const sync_capability *c, uint8_t *buf, size_t buf_len);
sync_capability *sync_capability_decode(const uint8_t *buf, size_t len);

/* Copy a capability's subject public key into out. */
void sync_capability_subject(const sync_capability *c, uint8_t out[SYNC_PUBKEY_LEN]);

/* Install a capability into the engine (verifying its self-signature). Granting
 * a root for a namespace switches that namespace into enforced mode. */
int sync_engine_grant(sync_engine *e, const sync_capability *c);

/* Release a capability. Safe with NULL. */
void sync_capability_free(sync_capability *c);

/* ---- Invites (M5 discovery) --------------------------------------------- */

/* An invite carries the peer's signing public key, a rendezvous address, and
 * an optional capability granting the holder access. Share the encoded bytes
 * out-of-band (QR, link, message); the recipient learns whom to connect to,
 * where to find them, and what they may do. No public DHT.
 *
 * encode returns the number of bytes required (writes into buf only if buf_len
 * is large enough; call with buf==NULL to size). Returns 0 on invalid input. */
size_t sync_invite_encode(const uint8_t peer_pubkey[SYNC_PUBKEY_LEN],
                          const char *rendezvous_addr,
                          const sync_capability *cap /* nullable */,
                          uint8_t *buf, size_t buf_len);

/* Decode an invite. Fills peer_pubkey and the NUL-terminated address into
 * addr_out (capacity addr_cap). If cap_out is non-NULL it receives a newly
 * allocated capability (or NULL when the invite carries none); release it with
 * sync_capability_free. Returns SYNC_OK or an error. */
int sync_invite_decode(const uint8_t *buf, size_t len,
                       uint8_t peer_pubkey[SYNC_PUBKEY_LEN],
                       char *addr_out, size_t addr_cap,
                       sync_capability **cap_out /* nullable */);

/* ---- Misc --------------------------------------------------------------- */

/* Release a buffer returned by sync_engine_get. Safe with NULL. */
void sync_free(void *p);

/* ---- Logging (optional, off by default) --------------------------------- */

typedef enum sync_log_level {
    SYNC_LOG_ERROR = 0,
    SYNC_LOG_WARN  = 1,
    SYNC_LOG_INFO  = 2
} sync_log_level;

/* Diagnostic log callback. msg is a short, NUL-terminated description that
 * never contains record values, keys, namespaces, or secrets. */
typedef void (*sync_log_fn)(void *ctx, int level, const char *msg);

/* Install (or clear, with fn==NULL) a per-engine log callback. Off by default;
 * the library logs nothing until one is set. */
int sync_engine_set_logger(sync_engine *e, sync_log_fn fn, void *ctx);

/* Human-readable string for a sync_error code. Never NULL. */
const char *sync_strerror(int err);

/* Return SYNC_ABI_VERSION at runtime. */
uint32_t sync_abi_version(void);

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* SYNC_ENGINE_H */
