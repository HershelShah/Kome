import type { Binding, EngineHandle, SessionHandle } from "kome-sync";
import type { Socket } from "./socket.js";
import { EMPTY, TAG_CYCLE_BEGIN, TAG_SESSION, frame, unframe } from "./wire.js";

export interface GossipPeerOptions {
  engine: EngineHandle;
  binding: Binding;
  socket: Socket;
  /** Whether to use sessionBeginScoped (needs peerPubkey) instead of sessionBegin. */
  scoped: boolean;
  /** The counterpart's pubkey, for scoping what THIS engine reveals to it. */
  peerPubkey?: Uint8Array;
  /** Aborts one stuck cycle; the session is still ended cleanly. Default 30s. */
  cycleTimeoutMs?: number;
  onSync?: (info: { durationMs: number }) => void;
  onError?: (err: Error) => void;
  /** Instrumentation: +1 right after sessionBegin*, -1 right after sessionEnd. */
  onSessionHandleDelta?: (delta: 1 | -1) => void;
}

/**
 * Drives one gossip connection's session pump against `socket`: at most one
 * SessionHandle alive at a time, whether started locally (startInitiator /
 * the periodic cycle) or remotely (an inbound cycle-begin frame makes this
 * side the responder). Transport-agnostic and identical on both ends of a
 * connection — this is the "mirror" logic SyncClient and each SyncHub
 * connection both run.
 */
export class GossipPeer {
  private readonly engine: EngineHandle;
  private readonly binding: Binding;
  private readonly socket: Socket;
  private readonly scoped: boolean;
  private readonly peerPubkey: Uint8Array | undefined;
  private readonly cycleTimeoutMs: number;
  private readonly onSync: ((info: { durationMs: number }) => void) | undefined;
  private readonly onErrorCb: ((err: Error) => void) | undefined;
  private readonly onSessionHandleDelta: ((delta: 1 | -1) => void) | undefined;

  private stopped = false;
  private busy = false;
  private frameWaiter: { resolve: (payload: Uint8Array) => void; reject: (err: Error) => void } | null = null;
  private periodicTimer: ReturnType<typeof setTimeout> | null = null;

  constructor(opts: GossipPeerOptions) {
    this.engine = opts.engine;
    this.binding = opts.binding;
    this.socket = opts.socket;
    this.scoped = opts.scoped;
    this.peerPubkey = opts.peerPubkey;
    this.cycleTimeoutMs = opts.cycleTimeoutMs ?? 30_000;
    this.onSync = opts.onSync;
    this.onErrorCb = opts.onError;
    this.onSessionHandleDelta = opts.onSessionHandleDelta;

    this.socket.onMessage((data) => this.handleMessage(data));
    // Abort a stuck cycle immediately rather than waiting out its timeout.
    this.socket.onClose(() => this.abortActiveCycle(new Error("kome-sync-runtime: socket closed mid-cycle")));
    this.socket.onError((err) => this.abortActiveCycle(err));
  }

  /** Start this connection's periodic self-initiated gossip cycles (first one fires immediately). */
  startInitiator(intervalMs: number): void {
    const tick = (): void => {
      if (this.stopped) return;
      this.runCycle(true)
        .catch((err: unknown) => this.reportError(err))
        .finally(() => {
          if (!this.stopped) this.periodicTimer = setTimeout(tick, intervalMs);
        });
    };
    this.periodicTimer = setTimeout(tick, 0);
  }

  /** Cancel periodic initiation and abort any in-flight cycle, ending its session. Idempotent. */
  stop(): void {
    if (this.stopped) return;
    this.stopped = true;
    if (this.periodicTimer !== null) {
      clearTimeout(this.periodicTimer);
      this.periodicTimer = null;
    }
    this.abortActiveCycle(new Error("kome-sync-runtime: peer stopped mid-cycle"));
  }

  private abortActiveCycle(err: Error): void {
    if (this.frameWaiter) {
      const w = this.frameWaiter;
      this.frameWaiter = null;
      w.reject(err);
    }
  }

  private handleMessage(data: Uint8Array): void {
    let tag: number, payload: Uint8Array;
    try {
      ({ tag, payload } = unframe(data));
    } catch (err) {
      this.reportError(err);
      return;
    }

    if (tag === TAG_CYCLE_BEGIN) {
      if (this.busy) return; // one session per connection; the peer's cycle-begin is dropped.
      this.runCycle(false).catch((err: unknown) => this.reportError(err));
      return;
    }
    if (tag === TAG_SESSION) {
      if (this.frameWaiter) {
        const w = this.frameWaiter;
        this.frameWaiter = null;
        w.resolve(payload);
      }
      // else: a stray session frame with nobody waiting on it — drop it.
      return;
    }
  }

  private waitForFrame(): Promise<Uint8Array> {
    return new Promise((resolve, reject) => {
      this.frameWaiter = { resolve, reject };
    });
  }

  private reportError(err: unknown): void {
    this.onErrorCb?.(err instanceof Error ? err : new Error(String(err)));
  }

  /**
   * Feed one genuinely-received input (or EMPTY for the initiator's very
   * first call) to the session, then keep calling with EMPTY input to drain
   * any further chunks already queued for THIS input (a single incoming
   * message can require several size-bounded outbound messages) — mirrors
   * the native transport's pump_() in src/transport/connection.cpp. Sends
   * every non-empty chunk. Returns whether anything was sent at all; a
   * `sessionStep` call's own `done` flag only reflects "nothing else queued
   * for the input I was just given" (it flips true even from a fabricated
   * empty drain call), so — like the native code — we deliberately do not
   * use it to decide whether the OVERALL session has converged.
   */
  private pumpAndSend(session: SessionHandle, initialInput: Uint8Array): boolean {
    let input = initialInput;
    let emittedAnything = false;
    for (;;) {
      const { out } = this.binding.sessionStep(session, input);
      input = EMPTY;
      if (out.length > 0) {
        this.socket.send(frame(TAG_SESSION, out));
        emittedAnything = true;
      }
      if (out.length === 0) break;
    }
    return emittedAnything;
  }

  private beginSession(initiator: boolean): SessionHandle {
    const s =
      this.scoped && this.peerPubkey
        ? this.binding.sessionBeginScoped(this.engine, initiator, this.peerPubkey)
        : this.binding.sessionBegin(this.engine, initiator);
    this.onSessionHandleDelta?.(1);
    return s;
  }

  private endSession(s: SessionHandle): void {
    this.binding.sessionEnd(s);
    this.onSessionHandleDelta?.(-1);
  }

  /** Run exactly one session to completion, as initiator or responder. */
  private async runCycle(initiator: boolean): Promise<void> {
    if (this.stopped || this.busy) return;
    this.busy = true;
    const start = Date.now();
    let session: SessionHandle | null = null;
    let timedOut = false;
    const timer = setTimeout(() => {
      timedOut = true;
      this.abortActiveCycle(new Error("kome-sync-runtime: gossip cycle timed out"));
    }, this.cycleTimeoutMs);

    try {
      session = this.beginSession(initiator);
      if (initiator) this.socket.send(frame(TAG_CYCLE_BEGIN, EMPTY));

      // The initiator supplies empty input to its first sessionStep; the
      // responder's first input is the initiator's first message, which
      // arrives right after the cycle-begin frame we were triggered by.
      let input: Uint8Array = initiator ? EMPTY : await this.waitForFrame();

      for (;;) {
        if (this.stopped) throw new Error("kome-sync-runtime: peer stopped mid-cycle");
        if (timedOut) throw new Error("kome-sync-runtime: gossip cycle timed out");
        const emitted = this.pumpAndSend(session, input);
        if (!emitted) {
          // Nothing left to say. The peer may be blocked waiting on a reply
          // (our own last message could have been non-empty), so say so
          // explicitly with an empty session frame, then conclude our side.
          this.socket.send(frame(TAG_SESSION, EMPTY));
          break;
        }
        input = await this.waitForFrame();
      }
      this.onSync?.({ durationMs: Date.now() - start });
    } finally {
      clearTimeout(timer);
      if (session !== null) this.endSession(session);
      this.busy = false;
    }
  }
}
