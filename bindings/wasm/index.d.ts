/* Type declarations for kome-sync (hand-written; checked by tsc in CI against
 * a strict consumer snippet — see .github/workflows/wasm.yml). */

/** Accepted anywhere the engine takes bytes: strings are UTF-8 encoded. */
export type BytesLike = string | Uint8Array | ArrayLike<number>;

/** Opaque engine handle (a pointer into the WASM heap). */
export type EngineHandle = number;
/** Opaque reconciliation-session handle. */
export type SessionHandle = number;
/** Opaque capability handle; free with {@link Binding.capFree}. */
export type CapabilityHandle = number;

/**
 * A capability's requested access, a bitmask of these flags (READ=1, WRITE=2,
 * READ|WRITE=3). Matches SYNC_ACCESS_READ / SYNC_ACCESS_WRITE in
 * include/sync_engine.h.
 */
export type AccessFlags = number;

/** {@link Binding.blobStat} result. size is bytes; complete is whether every
 * chunk the manifest references is present locally. */
export interface BlobStat {
  size: number;
  complete: boolean;
}

/** {@link Binding.inviteDecode} result. cap is null when the invite carries
 * no capability; free a non-null cap with {@link Binding.capFree}. */
export interface DecodedInvite {
  peerPubkey: Uint8Array;
  addr: string;
  cap: CapabilityHandle | null;
}

/**
 * An Error thrown by a sync_error-returning wrapper carries the raw C error
 * code (see SYNC_ERR_* in include/sync_engine.h) on `.code`, so callers can
 * branch on it (e.g. distinguishing SYNC_ERR_CORRUPT=7 from
 * SYNC_ERR_NOTFOUND=3) without parsing the message. Currently attached by the
 * blob* and invite* wrappers.
 */
export interface CodedError extends Error {
  code: number;
}

export declare class Binding {
  /** The raw Emscripten module, for advanced/ABI-level use. */
  M: unknown;

  abiVersion(): number;
  /** Human-readable name for a sync_error code (e.g. from a CodedError). */
  strerror(code: number): string;

  /** In-memory engine from a 32-byte identity seed. */
  create(seed: BytesLike): EngineHandle;
  /**
   * Durable engine backed by an append-only log file. The filesystem is
   * Emscripten's (MEMFS by default); mount IDBFS/OPFS in a browser for
   * persistence across reloads. An existing file's persisted identity wins
   * over the passed seed.
   */
  open(path: string, seed: BytesLike): EngineHandle;
  /**
   * Like open(), but the log is encrypted at rest under a caller-supplied
   * 32-byte key (XChaCha20-Poly1305). Throws if the key is wrong or the log
   * is otherwise unreadable (mismatched plaintext/encrypted framing, etc.) —
   * never hands back a partially-usable engine.
   */
  openEncrypted(path: string, seed: BytesLike, key: BytesLike): EngineHandle;
  destroy(e: EngineHandle): void;
  /** Flush durable state to disk (a no-op safety net; a no-op for in-memory
   * engines). */
  flush(e: EngineHandle): void;

  /** The engine's Ed25519 identity public key (32 bytes). */
  identity(e: EngineHandle): Uint8Array;
  /** BLAKE2b-256 of the signing public key — a stable, non-secret peer id. */
  siteId(e: EngineHandle): Uint8Array;

  /** Root capability for a namespace owned by `owner`. access: READ=1, WRITE=2. */
  capRoot(owner: EngineHandle, ns: BytesLike, access: AccessFlags): CapabilityHandle;
  capDelegate(
    delegator: EngineHandle,
    parent: CapabilityHandle,
    subjectPubkey: BytesLike,
    access: AccessFlags,
    expiryMs?: number,
  ): CapabilityHandle;
  /** Install a capability into an engine; returns 0 (SYNC_OK) on success.
   * Granting a root switches that namespace into enforced mode *for this
   * engine* — read-scoping and write-authorization both key off an engine's
   * own capability store, so the sender of a scoped session needs the root
   * (and any delegations it wants to honor) granted into itself, not just
   * into the recipient. */
  grant(e: EngineHandle, cap: CapabilityHandle): number;
  capFree(c: CapabilityHandle): void;
  /** Serialize a capability to bytes (for storage or out-of-band transfer). */
  capEncode(cap: CapabilityHandle): Uint8Array;
  /** Deserialize a capability; free the returned handle with capFree(). */
  capDecode(buf: BytesLike): CapabilityHandle;
  /** The capability's subject public key (32 bytes). */
  capSubject(cap: CapabilityHandle): Uint8Array;

  /**
   * Permanently revoke subject_pubkey's access (and everything it
   * sub-delegated) in namespace ns. The caller (e) must itself hold ns's
   * root, else the returned code is SYNC_ERR_UNAUTHORIZED (6). Returns the
   * raw sync_error code (0 = SYNC_OK) rather than throwing, matching
   * grant()'s convention.
   */
  revoke(e: EngineHandle, ns: BytesLike, subjectPubkey: BytesLike): number;
  /** Whether subject_pubkey is revoked in ns, as known to this replica. */
  isRevoked(e: EngineHandle, ns: BytesLike, subjectPubkey: BytesLike): boolean;

  set(e: EngineHandle, ns: BytesLike, entity: BytesLike, field: BytesLike, value: BytesLike): void;
  del(e: EngineHandle, ns: BytesLike, entity: BytesLike): void;
  /** Field value, or null if the entity/field is absent (or tombstoned). */
  get(e: EngineHandle, ns: BytesLike, entity: BytesLike, field: BytesLike): Uint8Array | null;
  exists(e: EngineHandle, ns: BytesLike, entity: BytesLike): boolean;
  /**
   * List entities present in namespace ns, in canonical byte-lexicographic
   * order. startAfter is an exclusive resume cursor (pass the last entity
   * from the previous page to continue; null/omit to start from the
   * beginning); limit caps the page size (0 = unlimited, the default).
   * Returns [] for an unknown namespace or a cursor past the end (not an
   * error).
   */
  scan(e: EngineHandle, ns: BytesLike, startAfter?: BytesLike | null, limit?: number): Uint8Array[];
  /** Deterministic 32-byte digest of the full state (the convergence oracle). */
  digest(e: EngineHandle): Uint8Array;

  /**
   * Content-address and store data in namespace ns (chunked automatically
   * above SYNC_BLOB_CHUNK_MAX bytes/chunk). Returns the 32-byte blob id
   * (BLAKE2b-256 of data). Idempotent: re-putting the same content yields
   * the same id.
   */
  blobPut(e: EngineHandle, ns: BytesLike, data: BytesLike): Uint8Array;
  /**
   * Reassemble and verify the blob identified by id. Returns a Uint8Array
   * (possibly zero-length, but never null, on success); null if unknown or
   * still incompletely replicated (SYNC_ERR_NOTFOUND — use blobStat to tell
   * those apart); throws a {@link CodedError} with code 7
   * (SYNC_ERR_CORRUPT) if any chunk or the reassembled whole fails its
   * content-hash check.
   */
  blobGet(e: EngineHandle, ns: BytesLike, id: BytesLike): Uint8Array | null;
  /**
   * Report a blob's size and local replication completeness without
   * reassembling or verifying it. Returns null if no manifest exists
   * (SYNC_ERR_NOTFOUND); throws a {@link CodedError} with code 7
   * (SYNC_ERR_CORRUPT) if the manifest is malformed.
   */
  blobStat(e: EngineHandle, ns: BytesLike, id: BytesLike): BlobStat | null;
  /**
   * Delete the manifest and every chunk entity it references. Throws a
   * {@link CodedError}: code 3 (SYNC_ERR_NOTFOUND) if no manifest exists, or
   * code 7 (SYNC_ERR_CORRUPT) if it is malformed (nothing is deleted in that
   * case).
   */
  blobDelete(e: EngineHandle, ns: BytesLike, id: BytesLike): void;

  sessionBegin(e: EngineHandle, initiator: boolean): SessionHandle;
  /**
   * Like sessionBegin, but read-scoped to peerPubkey: records in namespaces
   * that peer cannot read are excluded before any fingerprint is computed,
   * so their existence never leaks to an unauthorized peer. The scoping
   * check runs against `e`'s own capability store (see grant()'s note), so
   * `e` must itself hold the relevant root/delegations for this to exclude
   * anything — an engine with no capabilities granted into itself treats
   * every namespace as open.
   */
  sessionBeginScoped(e: EngineHandle, initiator: boolean, peerPubkey: BytesLike): SessionHandle;
  sessionEnd(s: SessionHandle): void;
  /**
   * Feed one incoming message (possibly empty) to the reconciliation session;
   * returns the next outgoing message and whether the session is done. This
   * is the transport-agnostic pump a browser drives over its WebSocket.
   */
  sessionStep(s: SessionHandle, input: Uint8Array): { out: Uint8Array; done: boolean };

  /** Converge two local engines via the reconciliation session (in-process). */
  sync(a: EngineHandle, b: EngineHandle): void;

  /**
   * Encode an invite: peer's pubkey + a rendezvous address + an optional
   * capability, for out-of-band sharing (QR, link, message). cap is a
   * CapabilityHandle to embed, or omit/0 for none.
   */
  inviteEncode(peerPubkey: BytesLike, rendezvousAddr: string, cap?: CapabilityHandle): Uint8Array;
  /**
   * Decode an invite. Throws a {@link CodedError} (code = sync_error) on
   * malformed input. A non-null result.cap must be released with capFree().
   */
  inviteDecode(buf: BytesLike): DecodedInvite;

  /**
   * Mount an IndexedDB-backed directory (browser only) so a durable engine's
   * files under `dir` survive a page reload. Call before open()/
   * openEncrypted() at a path under `dir`, then `await syncFs(true)` to pull
   * in persisted state. Throws under Node (no IndexedDB there — use a plain
   * MEMFS path instead).
   */
  mountIdbfs(dir: string): void;
  /**
   * Synchronize Emscripten's in-memory filesystem with the mounted IDBFS
   * backing store. populate=true pulls persisted state into memory (call
   * once after mountIdbfs, before opening); populate=false pushes current
   * writes out to IndexedDB. Throws (rejects) under Node.
   */
  syncFs(populate: boolean): Promise<void>;
}

/** Instantiate the WASM engine and return the API binding. */
export declare function load(): Promise<Binding>;
