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

export declare class Binding {
  /** The raw Emscripten module, for advanced/ABI-level use. */
  M: unknown;

  abiVersion(): number;

  /** In-memory engine from a 32-byte identity seed. */
  create(seed: BytesLike): EngineHandle;
  /**
   * Durable engine backed by an append-only log file. The filesystem is
   * Emscripten's (MEMFS by default); mount IDBFS/OPFS in a browser for
   * persistence across reloads. An existing file's persisted identity wins
   * over the passed seed.
   */
  open(path: string, seed: BytesLike): EngineHandle;
  destroy(e: EngineHandle): void;

  /** The engine's Ed25519 identity public key (32 bytes). */
  identity(e: EngineHandle): Uint8Array;

  /** Root capability for a namespace owned by `owner`. access: READ=1, WRITE=2. */
  capRoot(owner: EngineHandle, ns: BytesLike, access: number): CapabilityHandle;
  capDelegate(
    delegator: EngineHandle,
    parent: CapabilityHandle,
    subjectPubkey: BytesLike,
    access: number,
    expiryMs?: number,
  ): CapabilityHandle;
  /** Install a capability into an engine; returns 0 (SYNC_OK) on success. */
  grant(e: EngineHandle, cap: CapabilityHandle): number;
  capFree(c: CapabilityHandle): void;

  set(e: EngineHandle, ns: BytesLike, entity: BytesLike, field: BytesLike, value: BytesLike): void;
  del(e: EngineHandle, ns: BytesLike, entity: BytesLike): void;
  /** Field value, or null if the entity/field is absent (or tombstoned). */
  get(e: EngineHandle, ns: BytesLike, entity: BytesLike, field: BytesLike): Uint8Array | null;
  exists(e: EngineHandle, ns: BytesLike, entity: BytesLike): boolean;
  /** Deterministic 32-byte digest of the full state (the convergence oracle). */
  digest(e: EngineHandle): Uint8Array;

  sessionBegin(e: EngineHandle, initiator: boolean): SessionHandle;
  sessionEnd(s: SessionHandle): void;
  /**
   * Feed one incoming message (possibly empty) to the reconciliation session;
   * returns the next outgoing message and whether the session is done. This
   * is the transport-agnostic pump a browser drives over its WebSocket.
   */
  sessionStep(s: SessionHandle, input: Uint8Array): { out: Uint8Array; done: boolean };

  /** Converge two local engines via the reconciliation session (in-process). */
  sync(a: EngineHandle, b: EngineHandle): void;
}

/** Instantiate the WASM engine and return the API binding. */
export declare function load(): Promise<Binding>;
