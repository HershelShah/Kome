#!/usr/bin/env python3
"""
kome-demo: interactive P2P key-value replication over TCP.

Usage:
    python demo.py --port 9001
    python demo.py --port 9002 --peer 127.0.0.1:9001

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

# Add parent directory to path so we can import kome
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "python"))

from kome import Engine, KomeError, Transport


# ── TCP Transport ────────────────────────────────────────────────────────

class TcpTransport(Transport):
    """Simple TCP transport with length-prefix framing."""

    def __init__(self):
        super().__init__()
        self._conn: socket.socket | None = None
        self._peer_fp = b"\x00" * 32
        self._running = False
        self._recv_thread = None
        self._send_lock = threading.Lock()

    def connect_to(self, host: str, port: int, my_fp: bytes, peer_fp: bytes):
        """Connect to a remote peer."""
        self._peer_fp = peer_fp
        self._conn = socket.create_connection((host, port))
        self._conn.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        # Exchange fingerprints: send ours, receive theirs
        self._conn.sendall(my_fp[:32])
        remote_fp = _recv_exact(self._conn, 32)
        if remote_fp:
            self._peer_fp = remote_fp
        self._start_recv()

    def accept_from(self, listen_sock: socket.socket, my_fp: bytes):
        """Accept a connection from a remote peer."""
        self._conn, _ = listen_sock.accept()
        self._conn.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        # Exchange fingerprints: receive theirs, send ours
        remote_fp = _recv_exact(self._conn, 32)
        if remote_fp:
            self._peer_fp = remote_fp
        self._conn.sendall(my_fp[:32])
        self._start_recv()

    def send(self, peer_fp: bytes, data: bytes):
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


def _recv_exact(sock: socket.socket, n: int) -> bytes | None:
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


# ── Demo App ─────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description="Kome P2P demo")
    parser.add_argument("--port", type=int, required=True, help="Listen port")
    parser.add_argument("--peer", type=str, help="Peer address (host:port)")
    parser.add_argument("--db", type=str, help="Database path (default: /tmp/kome_demo_<port>.db)")
    args = parser.parse_args()

    db_path = args.db or f"/tmp/kome_demo_{args.port}.db"
    identity = f"demo_node_{args.port}".encode().ljust(32, b"\x00")[:32]

    # Open engine
    engine = Engine(db_path)
    engine.set_identity(identity)

    # Register remote change callback
    def on_change(ns, key, value, meta):
        if ns.startswith("__"):
            return  # ignore internal probe entries
        print(f"\n  << remote: {ns}/{key.decode(errors='replace')} = "
              f"{value.decode(errors='replace')}")
        print("> ", end="", flush=True)

    engine.on_remote_change(on_change)

    # Set up transport
    transport = TcpTransport()
    my_fp = engine.put("__sys", b"__fp__", b"x").author
    engine.delete("__sys", b"__fp__")

    if args.peer:
        # Client mode: connect to peer
        host, port_str = args.peer.rsplit(":", 1)
        peer_fp = b"\x00" * 32  # Will be replaced by handshake
        transport.connect_to(host, int(port_str), bytes(my_fp), peer_fp)
        engine.attach_transport(transport)
        transport.on_peer(transport._peer_fp, True)
        print(f"Connected to {args.peer}")
    else:
        # Server mode: listen and accept
        listen_sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        listen_sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        listen_sock.bind(("0.0.0.0", args.port))
        listen_sock.listen(1)
        print(f"Listening on port {args.port}... ", end="", flush=True)

        # Accept in background
        def accept_thread():
            transport.accept_from(listen_sock, bytes(my_fp))
            listen_sock.close()
            engine.attach_transport(transport)
            transport.on_peer(transport._peer_fp, True)
            print(f"peer connected!")
            print("> ", end="", flush=True)

        t = threading.Thread(target=accept_thread, daemon=True)
        t.start()

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

    transport.stop()
    engine.close()
    print("Bye!")


if __name__ == "__main__":
    main()
