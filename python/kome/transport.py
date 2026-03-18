"""Base transport class for Python-side custom transports."""

import ctypes
from ._ffi import KomeTransport, SEND_FN, SET_RECV_FN, SET_PEER_FN, RECV_CB, PEER_CB


class Transport:
    """Base class for Python transports.

    Subclass and implement send() to create a custom transport.
    Call on_recv() and on_peer() to deliver data and peer events to the engine.
    """

    def __init__(self):
        self._recv_cb = None
        self._recv_ud = None
        self._peer_cb = None
        self._peer_ud = None

        # Build C KomeTransport struct
        self._c_transport = KomeTransport()

        # Must keep references to prevent GC
        self._send_fn = SEND_FN(self._c_send)
        self._set_recv_fn = SET_RECV_FN(self._c_set_recv)
        self._set_peer_fn = SET_PEER_FN(self._c_set_peer)

        self._c_transport.send = self._send_fn
        self._c_transport.set_recv_callback = self._set_recv_fn
        self._c_transport.set_peer_callback = self._set_peer_fn
        self._c_transport.user_data = None

    @property
    def c_transport(self):
        return self._c_transport

    def send(self, peer_fp: bytes, data: bytes):
        """Override this to send data to a peer."""
        raise NotImplementedError

    def on_recv(self, peer_fp: bytes, data: bytes):
        """Call this to deliver received data to the engine."""
        if self._recv_cb:
            fp_arr = (ctypes.c_uint8 * 32)(*peer_fp[:32])
            data_arr = (ctypes.c_uint8 * len(data))(*data)
            self._recv_cb(self._recv_ud,
                          ctypes.cast(fp_arr, ctypes.POINTER(ctypes.c_uint8)),
                          ctypes.cast(data_arr, ctypes.POINTER(ctypes.c_uint8)),
                          len(data))

    def on_peer(self, peer_fp: bytes, connected: bool):
        """Call this to notify engine of peer connect/disconnect."""
        if self._peer_cb:
            fp_arr = (ctypes.c_uint8 * 32)(*peer_fp[:32])
            self._peer_cb(self._peer_ud,
                          ctypes.cast(fp_arr, ctypes.POINTER(ctypes.c_uint8)),
                          1 if connected else 0)

    # C callback wrappers
    def _c_send(self, _transport_ptr, peer_fp, data, length):
        fp = bytes(peer_fp[:32])
        d = bytes(data[:length])
        self.send(fp, d)

    def _c_set_recv(self, _transport_ptr, cb, ud):
        self._recv_cb = cb
        self._recv_ud = ud

    def _c_set_peer(self, _transport_ptr, cb, ud):
        self._peer_cb = cb
        self._peer_ud = ud
