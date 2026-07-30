/**
 * Transport abstraction. The gossip pump (peer.ts) and SyncClient talk only
 * to this interface, never to WebSocket/'ws' directly, so the core stays
 * dependency-free — 'ws' is imported solely by nodeSocket.ts, which only
 * SyncHub uses.
 */
export interface Socket {
  /** Send one binary frame. Must not be called after close(). */
  send(data: Uint8Array): void;
  /** Fires once, when the socket becomes ready to send/receive. */
  onOpen(cb: () => void): void;
  /** Fires for every inbound binary frame, as a Uint8Array. */
  onMessage(cb: (data: Uint8Array) => void): void;
  /** Fires once the socket is closed (for any reason, including close()). */
  onClose(cb: (reason?: string) => void): void;
  /** Fires on a transport-level error. A close event normally follows. */
  onError(cb: (err: Error) => void): void;
  /** Tear down the socket. Safe to call more than once. */
  close(): void;
}

/**
 * Adapter over the standard WebSocket API (globalThis.WebSocket): what a
 * browser tab has natively, and what Node >=22 also provides for outbound
 * (client) connections. SyncClient uses this on both sides — Node's global
 * WebSocket is a client only, so this adapter is never used to *accept*
 * connections (that's NodeSocket + SyncHub's 'ws' server).
 */
export class BrowserSocket implements Socket {
  private readonly ws: WebSocket;

  constructor(url: string) {
    const ws = new WebSocket(url);
    ws.binaryType = "arraybuffer";
    this.ws = ws;
  }

  send(data: Uint8Array): void {
    this.ws.send(data);
  }

  onOpen(cb: () => void): void {
    this.ws.addEventListener("open", () => cb());
  }

  onMessage(cb: (data: Uint8Array) => void): void {
    this.ws.addEventListener("message", (ev: MessageEvent) => {
      const raw = ev.data as unknown;
      if (raw instanceof ArrayBuffer) {
        cb(new Uint8Array(raw));
      } else if (ArrayBuffer.isView(raw)) {
        cb(new Uint8Array(raw.buffer, raw.byteOffset, raw.byteLength));
      } else {
        throw new Error(
          "kome-sync-runtime: BrowserSocket received a non-binary message " +
            "(binaryType must stay 'arraybuffer' and peers must only send binary frames)",
        );
      }
    });
  }

  onClose(cb: (reason?: string) => void): void {
    this.ws.addEventListener("close", (ev: CloseEvent) => cb(ev.reason || undefined));
  }

  onError(cb: (err: Error) => void): void {
    this.ws.addEventListener("error", () => cb(new Error("kome-sync-runtime: WebSocket error")));
  }

  close(): void {
    this.ws.close();
  }
}
