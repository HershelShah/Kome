"""WebSocket relay transport for cross-network sync."""

import struct
import threading
from .transport import Transport

MSG_JOIN = 0x01
MSG_CREATED = 0x02
MSG_PEER_JOIN = 0x03
MSG_PEER_LEFT = 0x04
MSG_DATA = 0x05
MSG_ERROR = 0x06


class WsRelayTransport(Transport):
    """Transport that connects to a Kome relay server via WebSocket.

    Usage::

        transport = WsRelayTransport()
        room = transport.connect("wss://kome-relay.fly.dev", my_fingerprint)
        # share `room` with peer
        engine.attach_transport(transport)

    Or join an existing room::

        transport = WsRelayTransport()
        transport.connect("wss://kome-relay.fly.dev", my_fingerprint, room="X7KM2Q")
        engine.attach_transport(transport)
    """

    def __init__(self):
        super().__init__()
        self._ws = None
        self._running = False
        self._recv_thread = None
        self._room_code = None
        self._room_event = threading.Event()
        self._error = None

    def connect(self, url: str, fingerprint: bytes, room: str | None = None) -> str:
        """Connect to relay. Returns room code."""
        try:
            from websockets.sync.client import connect as ws_connect
        except ImportError:
            raise ImportError(
                "websockets is required for relay mode. "
                "Install it with: pip install websockets"
            )

        self._ws = ws_connect(url)

        # Send JOIN
        if room:
            self._ws.send(bytes([MSG_JOIN]) + fingerprint[:32] + room.encode())
        else:
            self._ws.send(bytes([MSG_JOIN]) + fingerprint[:32])

        # Wait for CREATED response (may receive PEER_JOINED first if joining)
        self._pending_peers = []
        while True:
            resp = self._ws.recv()
            if not isinstance(resp, bytes) or len(resp) < 1:
                continue
            if resp[0] == MSG_CREATED and len(resp) >= 7:
                self._room_code = resp[1:7].decode()
                break
            elif resp[0] == MSG_PEER_JOIN and len(resp) >= 33:
                self._pending_peers.append(resp[1:33])
            elif resp[0] == MSG_ERROR:
                raise ConnectionError(f"Relay error: {resp[1:].decode()}")
            else:
                raise ConnectionError("Unexpected relay response")

        if not self._room_code:
            raise ConnectionError("Failed to join relay room")

        # Start recv loop
        self._running = True
        self._recv_thread = threading.Thread(target=self._recv_loop, daemon=True)
        self._recv_thread.start()

        # Deliver any peer notifications received during handshake
        # (must happen after attach_transport, so caller should call
        # on_peer manually — we store them for the caller)
        self.pending_peers = self._pending_peers
        del self._pending_peers

        return self._room_code

    def send(self, peer_fp: bytes, data: bytes):
        if self._ws:
            try:
                self._ws.send(bytes([MSG_DATA]) + peer_fp[:32] + data)
            except Exception:
                pass

    def stop(self):
        self._running = False
        if self._ws:
            try:
                self._ws.close()
            except Exception:
                pass
        if self._recv_thread:
            self._recv_thread.join(timeout=2)

    def _recv_loop(self):
        while self._running:
            try:
                msg = self._ws.recv()
            except Exception:
                break

            if not isinstance(msg, bytes) or len(msg) < 1:
                continue

            mtype = msg[0]

            if mtype == MSG_PEER_JOIN and len(msg) >= 33:
                peer_fp = msg[1:33]
                self.on_peer(peer_fp, True)

            elif mtype == MSG_PEER_LEFT and len(msg) >= 33:
                peer_fp = msg[1:33]
                self.on_peer(peer_fp, False)

            elif mtype == MSG_DATA and len(msg) > 33:
                sender_fp = msg[1:33]
                payload = msg[33:]
                self.on_recv(sender_fp, payload)

            elif mtype == MSG_ERROR:
                self._error = msg[1:].decode()
                break
