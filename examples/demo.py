#!/usr/bin/env python3
"""
kome-demo: interactive P2P key-value replication.

TCP mode (same network):
    python demo.py --port 9001
    python demo.py --port 9002 --peer 127.0.0.1:9001

Relay mode (any network):
    python demo.py --relay
    python demo.py --relay --room X7KM2Q

Commands:
    put <ns> <key> <value>    Write a key-value pair
    get <ns> <key>            Read a value
    del <ns> <key>            Delete a key
    list <ns>                 List all keys in a namespace
    namespaces                List all namespaces
    stats                     Show database stats
    help                      Show this help
    quit                      Exit
"""

import argparse
import os
import readline
import socket
import struct
import sys
import threading

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "python"))

from kome import Engine, KomeError, Transport

DEFAULT_RELAY = "wss://kome-relay.fly.dev"


# ── TCP Transport ────────────────────────────────────────────────────

class TcpTransport(Transport):
    """Simple TCP transport with length-prefix framing."""

    def __init__(self):
        super().__init__()
        self._conn = None
        self._peer_fp = b"\x00" * 32
        self._running = False
        self._recv_thread = None
        self._send_lock = threading.Lock()

    def connect_to(self, host, port, my_fp, peer_fp):
        self._peer_fp = peer_fp
        self._conn = socket.create_connection((host, port))
        self._conn.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        self._conn.sendall(my_fp[:32])
        remote_fp = _recv_exact(self._conn, 32)
        if remote_fp:
            self._peer_fp = remote_fp
        self._start_recv()

    def accept_from(self, listen_sock, my_fp):
        self._conn, _ = listen_sock.accept()
        self._conn.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        remote_fp = _recv_exact(self._conn, 32)
        if remote_fp:
            self._peer_fp = remote_fp
        self._conn.sendall(my_fp[:32])
        self._start_recv()

    def send(self, peer_fp, data):
        with self._send_lock:
            if self._conn:
                try:
                    self._conn.sendall(struct.pack("!I", len(data)) + data)
                except OSError:
                    pass

    def stop(self):
        self._running = False
        if self._conn:
            try:
                self._conn.shutdown(socket.SHUT_RDWR)
            except OSError:
                pass
        if self._recv_thread:
            self._recv_thread.join(timeout=2)
        if self._conn:
            self._conn.close()
            self._conn = None

    def _start_recv(self):
        self._running = True
        self._recv_thread = threading.Thread(target=self._recv_loop, daemon=True)
        self._recv_thread.start()

    def _recv_loop(self):
        while self._running:
            hdr = _recv_exact(self._conn, 4)
            if not hdr:
                break
            length = struct.unpack("!I", hdr)[0]
            if length > 16 * 1024 * 1024:
                break
            data = _recv_exact(self._conn, length)
            if not data:
                break
            self.on_recv(self._peer_fp, data)


def _recv_exact(sock, n):
    buf = b""
    while len(buf) < n:
        try:
            chunk = sock.recv(n - len(buf))
        except OSError:
            return None
        if not chunk:
            return None
        buf += chunk
    return buf


# ── Fingerprint helper ───────────────────────────────────────────────

def get_fingerprint(engine):
    """Get engine's identity fingerprint by writing a probe entry."""
    meta = engine.put("__sys", b"__fp__", b"x")
    fp = bytes(meta.author)
    engine.delete("__sys", b"__fp__")
    return fp


# ── Main ─────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description="Kome P2P demo — sync data between two machines")
    parser.add_argument("--port", type=int, help="Listen port (TCP mode)")
    parser.add_argument("--peer", type=str, help="Peer address host:port (TCP mode)")
    parser.add_argument("--relay", nargs="?", const=DEFAULT_RELAY, default=None,
                        metavar="URL", help="Use WebSocket relay (default: %(const)s)")
    parser.add_argument("--room", type=str, help="Join existing relay room")
    parser.add_argument("--db", type=str, help="Database path")
    args = parser.parse_args()

    if not args.relay and not args.port:
        parser.error("specify either --relay or --port")

    # Database path
    if args.db:
        db_path = args.db
    elif args.relay:
        suffix = args.room or "new"
        db_path = f"/tmp/kome_demo_{suffix}.db"
    else:
        db_path = f"/tmp/kome_demo_{args.port}.db"

    # Open engine
    identity = os.urandom(32)
    engine = Engine(db_path)
    engine.set_identity(identity)
    my_fp = get_fingerprint(engine)

    # Remote change callback
    def on_change(ns, key, value, meta):
        if ns.startswith("__"):
            return
        print(f"\n  << remote: {ns}/{key.decode(errors='replace')} = "
              f"{value.decode(errors='replace')}")
        print("> ", end="", flush=True)

    engine.on_remote_change(on_change)

    # Set up transport
    transport = None

    if args.relay:
        # ── Relay mode ──
        from kome.ws_transport import WsRelayTransport

        transport = WsRelayTransport()
        room = transport.connect(args.relay, my_fp, room=args.room)
        engine.attach_transport(transport)

        # Deliver any peer-joined notifications from the handshake
        for peer_fp in transport.pending_peers:
            transport.on_peer(peer_fp, True)

        if args.room:
            print(f"Joined room: {room}")
        else:
            print(f"Room code: {room} -- share this with your peer")
        print(f"Relay: {args.relay}")

    elif args.peer:
        # ── TCP client mode ──
        transport = TcpTransport()
        host, port_str = args.peer.rsplit(":", 1)
        transport.connect_to(host, int(port_str), my_fp, b"\x00" * 32)
        engine.attach_transport(transport)
        transport.on_peer(transport._peer_fp, True)
        print(f"Connected to {args.peer}")

    else:
        # ── TCP server mode ──
        transport = TcpTransport()
        listen_sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        listen_sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        listen_sock.bind(("0.0.0.0", args.port))
        listen_sock.listen(1)
        print(f"Listening on port {args.port}... ", end="", flush=True)

        def accept_thread():
            transport.accept_from(listen_sock, my_fp)
            listen_sock.close()
            engine.attach_transport(transport)
            transport.on_peer(transport._peer_fp, True)
            print("peer connected!")
            print("> ", end="", flush=True)

        threading.Thread(target=accept_thread, daemon=True).start()

    print(f"Database: {db_path}")
    print('Type "help" for commands.\n')

    # REPL
    while True:
        try:
            line = input("> ").strip()
        except (EOFError, KeyboardInterrupt):
            print()
            break

        if not line:
            continue

        parts = line.split(None, 3)
        cmd = parts[0].lower()

        try:
            if cmd == "put" and len(parts) >= 4:
                ns, key, val = parts[1], parts[2], parts[3]
                meta = engine.put(ns, key.encode(), val.encode())
                print(f"  ok (seq={meta.seq})")

            elif cmd == "get" and len(parts) >= 3:
                ns, key = parts[1], parts[2]
                value, meta = engine.get(ns, key.encode())
                if value:
                    print(f"  {value.decode(errors='replace')}")
                else:
                    print("  (empty)")

            elif cmd == "del" and len(parts) >= 3:
                ns, key = parts[1], parts[2]
                engine.delete(ns, key.encode())
                print("  deleted")

            elif cmd == "list" and len(parts) >= 2:
                ns = parts[1]
                keys = engine.list_keys(ns)
                if not keys:
                    print("  (empty)")
                for k in keys:
                    try:
                        value, meta = engine.get(ns, k)
                        print(f"  {k.decode(errors='replace')} = "
                              f"{value.decode(errors='replace') if value else '(empty)'}")
                    except KomeError:
                        pass

            elif cmd == "namespaces":
                nss = engine.list_namespaces()
                for ns in nss:
                    if not ns.startswith("__"):
                        print(f"  {ns}")

            elif cmd == "stats":
                s = engine.stats()
                print(f"  entries: {s.total_entries}, tombstones: {s.tombstone_count}, "
                      f"namespaces: {s.namespace_count}, db: {s.db_size_bytes} bytes")

            elif cmd in ("quit", "exit", "q"):
                break

            elif cmd == "help":
                print("  put <ns> <key> <value>  Write a key-value pair")
                print("  get <ns> <key>          Read a value")
                print("  del <ns> <key>          Delete a key")
                print("  list <ns>               List all keys in a namespace")
                print("  namespaces              List all namespaces")
                print("  stats                   Show database stats")
                print("  quit                    Exit")

            else:
                print(f"  unknown command: {cmd} (type 'help')")

        except KomeError as e:
            print(f"  error: {e.message}")
        except Exception as e:
            print(f"  error: {e}")

    if transport:
        transport.stop()
    engine.close()
    print("Bye!")


if __name__ == "__main__":
    main()
