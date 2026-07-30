/**
 * Wire framing shared by every peer on the WebSocket transport (browser
 * SyncClient, Node SyncClient, SyncHub connections): each sync-session
 * message is exactly one binary WebSocket frame, a 1-byte tag followed by
 * the payload bytes.
 *
 *   byte 0       tag: 0x00 = cycle-begin (control), 0x01 = session message
 *   byte 1..N    payload (empty for cycle-begin; the reconcile bytes from
 *                Binding.sessionStep for a session message)
 *
 * Both ends run the exact same encode/decode below — there is deliberately
 * no version byte, no length prefix (the WebSocket frame boundary already
 * delimits the message), and no additional metadata. Keep it that way; if a
 * new control message is ever needed, add a new tag value rather than
 * growing this format.
 */

/** Control: initiator announces the start of a new gossip cycle. No payload. */
export const TAG_CYCLE_BEGIN = 0x00;
/** A sessionStep in/out message (the reconciliation bytes). */
export const TAG_SESSION = 0x01;

/** The empty byte string, reused to avoid reallocating for every frame. */
export const EMPTY: Uint8Array = new Uint8Array(0);

/** Prefix `payload` with its 1-byte tag, producing the frame to send. */
export function frame(tag: number, payload: Uint8Array): Uint8Array {
  const out = new Uint8Array(payload.length + 1);
  out[0] = tag;
  out.set(payload, 1);
  return out;
}

/** Split a received frame back into its tag and payload. */
export function unframe(data: Uint8Array): { tag: number; payload: Uint8Array } {
  if (data.length < 1) {
    throw new Error("kome-sync-runtime: received a 0-byte WebSocket frame (missing tag byte)");
  }
  return { tag: data[0] as number, payload: data.subarray(1) };
}
