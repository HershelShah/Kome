"""Kome — Peer-to-peer data replication middleware (Python bindings)"""

from .engine import Engine, KomeError
from .transport import Transport

__all__ = ["Engine", "KomeError", "Transport"]

# Optional: WsRelayTransport (requires `pip install websockets`)
try:
    from .ws_transport import WsRelayTransport
    __all__.append("WsRelayTransport")
except ImportError:
    pass
