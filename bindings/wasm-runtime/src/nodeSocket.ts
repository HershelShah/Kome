import type WebSocket from "ws";
import type { Socket } from "./socket.js";

/** Concatenate ws's fragmented-message form ('fragments' binaryType) into one buffer. */
function concat(chunks: readonly Uint8Array[]): Uint8Array {
  const total = chunks.reduce((n, c) => n + c.length, 0);
  const out = new Uint8Array(total);
  let offset = 0;
  for (const c of chunks) {
    out.set(c, offset);
    offset += c.length;
  }
  return out;
}

function toUint8Array(data: WebSocket.RawData): Uint8Array {
  if (Array.isArray(data)) return concat(data);
  if (data instanceof ArrayBuffer) return new Uint8Array(data);
  // Node Buffer: already a Uint8Array subclass, but re-view defensively in
  // case it is a slice of a larger pooled buffer.
  return new Uint8Array(data.buffer, data.byteOffset, data.byteLength);
}

/**
 * Adapter over a 'ws' library WebSocket. Used only by SyncHub, for
 * connections its WebSocketServer has already accepted (so the socket is
 * already open by the time a NodeSocket wraps it).
 */
export class NodeSocket implements Socket {
  constructor(private readonly ws: WebSocket) {}

  send(data: Uint8Array): void {
    this.ws.send(data);
  }

  onOpen(cb: () => void): void {
    if (this.ws.readyState === this.ws.OPEN) {
      queueMicrotask(cb);
    } else {
      this.ws.once("open", cb);
    }
  }

  onMessage(cb: (data: Uint8Array) => void): void {
    this.ws.on("message", (data: WebSocket.RawData) => cb(toUint8Array(data)));
  }

  onClose(cb: (reason?: string) => void): void {
    this.ws.on("close", (_code: number, reason: Buffer) =>
      cb(reason.length > 0 ? reason.toString("utf8") : undefined),
    );
  }

  onError(cb: (err: Error) => void): void {
    this.ws.on("error", cb);
  }

  close(): void {
    this.ws.close();
  }
}
