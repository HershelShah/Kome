export { SyncClient, type SyncClientOptions, type ConnState } from "./syncClient.js";
export { SyncHub, type SyncHubOptions } from "./syncHub.js";
export type { Socket } from "./socket.js";
export { BrowserSocket } from "./socket.js";
export { NodeSocket } from "./nodeSocket.js";
export { TAG_CYCLE_BEGIN, TAG_SESSION, frame, unframe, EMPTY } from "./wire.js";
// Exported for tests/advanced use (e.g. instrumenting session-handle counts
// with a custom transport); not part of the SyncClient/SyncHub happy path.
export { GossipPeer, type GossipPeerOptions } from "./peer.js";
