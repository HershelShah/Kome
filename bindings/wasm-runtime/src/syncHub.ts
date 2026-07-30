import type { IncomingMessage } from "node:http";
import { WebSocketServer, type WebSocket as WsSocket } from "ws";
import type { Binding, EngineHandle } from "kome-sync";
import { NodeSocket } from "./nodeSocket.js";
import { GossipPeer } from "./peer.js";

export interface SyncHubOptions {
  engine: EngineHandle;
  binding: Binding;
  port: number;
  host?: string;
  /** Read-scope replies by the pubkey each client presents. Default true. */
  scoped?: boolean;
  /** Per-connection cycle abort timeout, in ms. Default 30000. */
  cycleTimeoutMs?: number;
  /** Maximum simultaneous connections; excess connections are rejected at the WS upgrade. Default 256. */
  maxConnections?: number;
  /**
   * Optional shared bearer token clients must present as ?token=... on
   * connect. See the module doc comment below for what this is (and is not)
   * a substitute for.
   */
  token?: string;
}

/**
 * ---------------------------------------------------------------------------
 * TRUST MODEL — read this before pointing a hub at anything but your own
 * devices.
 *
 * This WebSocket path authenticates at the TRANSPORT layer only: terminate
 * TLS in front of it (wss://, e.g. behind a reverse proxy) and optionally
 * require a shared bearer `token` checked on the WS upgrade. Read-scoping is
 * keyed off the pubkey each client SELF-REPORTS in its connection URL
 * (?pubkey=...) — there is no signature or challenge proving the client
 * actually owns that key.
 *
 * It does NOT perform the Noise XX handshake + identity-proof mutual auth
 * that the native UDP path (connect_and_sync / komed) does — the WASM
 * binding does not expose a signing primitive over this API surface capable
 * of proving pubkey ownership from JS. A malicious or buggy client can claim
 * any pubkey and thereby attempt to widen the read-scope the hub applies to
 * it (sessionBeginScoped only filters by capabilities *this engine* has
 * granted for that claimed key — it will happily scope generously for a
 * pubkey nobody has actually authenticated).
 *
 * So: this is appropriate for syncing your own devices, or a hub you run and
 * whose clients you also control/deploy (e.g. behind your own token + TLS).
 * It is NOT a substitute for real peer authentication if you don't trust
 * every holder of the token. This is the same class of call komed's cap_file
 * serving makes explicit — don't oversell it as more.
 * ---------------------------------------------------------------------------
 *
 * The listener: accepts many client connections and, per connection, runs
 * the same GossipPeer machinery SyncClient does (responder to client-driven
 * cycles) against the hub's own durable engine — so every connected client
 * converges with the hub, and thus, transitively across cycles, with every
 * other connected client.
 */
export class SyncHub {
  private readonly engine: EngineHandle;
  private readonly binding: Binding;
  private readonly port: number;
  private readonly host: string;
  private readonly scoped: boolean;
  private readonly cycleTimeoutMs: number;
  private readonly maxConnections: number;
  private readonly token: string | undefined;

  private wss: WebSocketServer | null = null;
  private readonly connections = new Map<WsSocket, GossipPeer>();
  private liveSessionCount = 0;

  private readonly errorListeners = new Set<(err: Error) => void>();

  constructor(opts: SyncHubOptions) {
    this.engine = opts.engine;
    this.binding = opts.binding;
    this.port = opts.port;
    this.host = opts.host ?? "127.0.0.1";
    this.scoped = opts.scoped ?? true;
    this.cycleTimeoutMs = opts.cycleTimeoutMs ?? 30_000;
    this.maxConnections = opts.maxConnections ?? 256;
    this.token = opts.token;
  }

  onError(cb: (err: Error) => void): void {
    this.errorListeners.add(cb);
  }

  /** Total SessionHandles currently open across all connections. For leak checks. */
  get liveSessions(): number {
    return this.liveSessionCount;
  }
  get connectionCount(): number {
    return this.connections.size;
  }

  /** Start listening. Resolves once the port is bound. */
  start(): Promise<void> {
    return new Promise((resolve, reject) => {
      const wss = new WebSocketServer({
        port: this.port,
        host: this.host,
        verifyClient: (info: { req: IncomingMessage }, cb: (ok: boolean, code?: number, msg?: string) => void) => {
          if (this.connections.size >= this.maxConnections) {
            cb(false, 503, "kome-sync-runtime: hub at capacity");
            return;
          }
          if (this.token) {
            const url = new URL(info.req.url ?? "/", "http://localhost");
            if (url.searchParams.get("token") !== this.token) {
              cb(false, 401, "kome-sync-runtime: bad token");
              return;
            }
          }
          cb(true);
        },
      });

      const onListenError = (err: Error): void => reject(err);
      wss.once("error", onListenError);
      wss.once("listening", () => {
        wss.off("error", onListenError);
        wss.on("error", (err: Error) => this.errorListeners.forEach((cb) => cb(err)));
        resolve();
      });
      wss.on("connection", (ws: WsSocket, req: IncomingMessage) => this.handleConnection(ws, req));
      this.wss = wss;
    });
  }

  private handleConnection(ws: WsSocket, req: IncomingMessage): void {
    const url = new URL(req.url ?? "/", "http://localhost");
    const pubkeyHex = url.searchParams.get("pubkey");
    const peerPubkey = pubkeyHex ? fromHex(pubkeyHex) : undefined;

    const socket = new NodeSocket(ws);
    const peer = new GossipPeer({
      engine: this.engine,
      binding: this.binding,
      socket,
      scoped: this.scoped,
      peerPubkey,
      cycleTimeoutMs: this.cycleTimeoutMs,
      onError: (err) => this.errorListeners.forEach((cb) => cb(err)),
      onSessionHandleDelta: (d) => {
        this.liveSessionCount += d;
      },
    });
    this.connections.set(ws, peer);
    ws.once("close", () => {
      peer.stop();
      this.connections.delete(ws);
    });
  }

  /** Close all sockets, end all sessions, close the server. Idempotent. */
  stop(): Promise<void> {
    return new Promise((resolve, reject) => {
      for (const [ws, peer] of this.connections) {
        peer.stop();
        ws.terminate();
      }
      this.connections.clear();

      const wss = this.wss;
      this.wss = null;
      if (!wss) {
        resolve();
        return;
      }
      wss.close((err?: Error) => (err ? reject(err) : resolve()));
    });
  }
}

function fromHex(hex: string): Uint8Array {
  const clean = hex.length % 2 === 0 ? hex : "0" + hex;
  const out = new Uint8Array(clean.length / 2);
  for (let i = 0; i < out.length; i++) out[i] = parseInt(clean.slice(i * 2, i * 2 + 2), 16);
  return out;
}
