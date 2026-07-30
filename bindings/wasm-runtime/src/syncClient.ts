import type { Binding, EngineHandle } from "kome-sync";
import { BrowserSocket } from "./socket.js";
import { GossipPeer } from "./peer.js";

export type ConnState = "connecting" | "open" | "closed";

export interface SyncClientOptions {
  engine: EngineHandle;
  binding: Binding;
  /** ws:// or wss:// URL of the SyncHub (or any peer speaking this wire protocol). */
  url: string;
  /** The counterpart's pubkey, to scope what this engine reveals to it. */
  peerPubkey?: Uint8Array;
  /** Use sessionBeginScoped (requires peerPubkey) rather than sessionBegin. Default true. */
  scoped?: boolean;
  /** Gossip cycle period, in ms. Default 2000. */
  intervalMs?: number;
  /** Aborts one stuck cycle, cleanly ending its session. Default 30000. */
  cycleTimeoutMs?: number;
  /** Shared bearer token, if the hub requires one; sent as ?token=... on connect. */
  token?: string;
}

/**
 * The dialer: connects to a SyncHub (or another SyncClient-compatible peer),
 * then runs a gossip cycle every `intervalMs` — sessionBegin(initiator) ->
 * exchange sessionStep messages over the socket until both sides report
 * done -> sessionEnd. Reconnects with exponential backoff + jitter on
 * close/error. Works unchanged in a browser or under Node >=22 (both have a
 * global WebSocket client).
 *
 * onChange is intentionally not provided: the underlying engine has no
 * change-notification callback. After onSync fires, poll your own state
 * (e.g. via Binding.scan/get) to pick up what the cycle just merged in.
 */
export class SyncClient {
  private readonly engine: EngineHandle;
  private readonly binding: Binding;
  private readonly url: string;
  private readonly peerPubkey: Uint8Array | undefined;
  private readonly scoped: boolean;
  private readonly intervalMs: number;
  private readonly cycleTimeoutMs: number;
  private readonly token: string | undefined;

  private socket: BrowserSocket | null = null;
  private peer: GossipPeer | null = null;
  private stopped = false;
  private reconnectAttempt = 0;
  private reconnectTimer: ReturnType<typeof setTimeout> | null = null;
  private liveSessionCount = 0;

  private readonly syncListeners = new Set<(info: { durationMs: number }) => void>();
  private readonly errorListeners = new Set<(err: Error) => void>();
  private readonly stateListeners = new Set<(state: ConnState) => void>();

  constructor(opts: SyncClientOptions) {
    this.engine = opts.engine;
    this.binding = opts.binding;
    this.url = opts.url;
    this.peerPubkey = opts.peerPubkey;
    this.scoped = opts.scoped ?? true;
    this.intervalMs = opts.intervalMs ?? 2000;
    this.cycleTimeoutMs = opts.cycleTimeoutMs ?? 30_000;
    this.token = opts.token;
  }

  onSync(cb: (info: { durationMs: number }) => void): void {
    this.syncListeners.add(cb);
  }
  onError(cb: (err: Error) => void): void {
    this.errorListeners.add(cb);
  }
  onStateChange(cb: (state: ConnState) => void): void {
    this.stateListeners.add(cb);
  }

  /** Number of SessionHandles currently open on this connection (0 or 1). For leak checks. */
  get liveSessions(): number {
    return this.liveSessionCount;
  }

  /** Open the socket and begin periodic gossip cycles once it connects. */
  connect(): void {
    if (this.stopped) return;
    this.dial();
  }

  private dial(): void {
    if (this.stopped) return;
    this.emitState("connecting");

    const identityHex = toHex(this.binding.identity(this.engine));
    const dialUrl = new URL(this.url);
    dialUrl.searchParams.set("pubkey", identityHex);
    if (this.token) dialUrl.searchParams.set("token", this.token);

    const socket = new BrowserSocket(dialUrl.toString());
    this.socket = socket;

    // Node's global WebSocket (unlike a browser's) does not always follow a
    // pre-open connection failure with a 'close' event — only 'error'. Guard
    // so either event (or both, as browsers do) triggers reconnect exactly
    // once per dial attempt.
    let settled = false;
    const handleGone = (): void => {
      if (settled) return;
      settled = true;
      this.peer?.stop();
      this.peer = null;
      this.socket = null;
      if (this.stopped) return;
      this.emitState("closed");
      this.scheduleReconnect();
    };

    socket.onOpen(() => {
      if (this.stopped) {
        socket.close();
        return;
      }
      this.reconnectAttempt = 0;
      this.emitState("open");

      const peer = new GossipPeer({
        engine: this.engine,
        binding: this.binding,
        socket,
        scoped: this.scoped,
        peerPubkey: this.peerPubkey,
        cycleTimeoutMs: this.cycleTimeoutMs,
        onSync: (info) => this.syncListeners.forEach((cb) => cb(info)),
        onError: (err) => this.errorListeners.forEach((cb) => cb(err)),
        onSessionHandleDelta: (d) => {
          this.liveSessionCount += d;
        },
      });
      this.peer = peer;
      peer.startInitiator(this.intervalMs);
    });

    socket.onError((err) => {
      this.errorListeners.forEach((cb) => cb(err));
      handleGone();
    });

    socket.onClose(() => handleGone());
  }

  private scheduleReconnect(): void {
    const base = 500;
    const cap = 30_000;
    const exp = Math.min(cap, base * 2 ** this.reconnectAttempt);
    const delay = Math.min(cap, exp / 2 + Math.random() * (exp / 2));
    this.reconnectAttempt++;
    this.reconnectTimer = setTimeout(() => this.dial(), delay);
  }

  private emitState(state: ConnState): void {
    this.stateListeners.forEach((cb) => cb(state));
  }

  /** Cancel timers, close the socket, end any live session. Idempotent. */
  stop(): void {
    if (this.stopped) return;
    this.stopped = true;
    if (this.reconnectTimer !== null) {
      clearTimeout(this.reconnectTimer);
      this.reconnectTimer = null;
    }
    this.peer?.stop();
    this.peer = null;
    this.socket?.close();
    this.socket = null;
  }
}

function toHex(bytes: Uint8Array): string {
  let out = "";
  for (const b of bytes) out += b.toString(16).padStart(2, "0");
  return out;
}
