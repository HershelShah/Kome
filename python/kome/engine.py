"""Pythonic Engine class wrapping the Kome C API."""

import ctypes
import os
import tempfile
from typing import Optional, Callable, Dict, List, Tuple

from ._ffi import (
    _lib, KomeConfig, KomeEntryMeta, KomeVersionEntry, KomeStats,
    KomeTransport, REMOTE_CHANGE_CB,
)
from .transport import Transport


class KomeError(Exception):
    """Exception raised on Kome errors."""
    def __init__(self, code: int, msg: str = ""):
        self.code = code
        errstr = _lib.kome_errstr(code)
        self.message = errstr.decode() if errstr else msg
        super().__init__(f"KomeError({code}): {self.message}")


def _check(rc: int):
    if rc != 0:
        raise KomeError(rc)


class Engine:
    """Kome replication engine.

    Usage::

        with Engine("state.db") as e:
            e.set_identity(b"my_secret_key")
            meta = e.replicate("contacts", b"user1", b"Alice")
    """

    def __init__(self, path: str, enable_wal: bool = True, busy_timeout_ms: int = 5000):
        cfg = KomeConfig()
        cfg.path = path.encode() if isinstance(path, str) else path
        cfg.disable_wal = 0 if enable_wal else 1
        cfg.busy_timeout_ms = busy_timeout_ms

        self._handle = ctypes.c_void_p()
        _check(_lib.kome_open(ctypes.byref(cfg), ctypes.byref(self._handle)))

        # prevent GC of callbacks
        self._callbacks = []
        self._transport_ref = None

    def __enter__(self):
        return self

    def __exit__(self, *args):
        self.close()

    def close(self):
        if self._handle:
            _lib.kome_close(self._handle)
            self._handle = None

    def set_identity(self, key: bytes):
        arr = (ctypes.c_uint8 * len(key))(*key)
        _check(_lib.kome_set_identity(
            self._handle,
            ctypes.cast(arr, ctypes.POINTER(ctypes.c_uint8)),
            len(key)))

    def put(self, ns: str, key: bytes, value: bytes) -> KomeEntryMeta:
        meta = KomeEntryMeta()
        key_arr = (ctypes.c_uint8 * len(key))(*key)
        val_arr = (ctypes.c_uint8 * len(value))(*value)
        _check(_lib.kome_put(
            self._handle, ns.encode(),
            ctypes.cast(key_arr, ctypes.POINTER(ctypes.c_uint8)), len(key),
            ctypes.cast(val_arr, ctypes.POINTER(ctypes.c_uint8)), len(value),
            ctypes.byref(meta)))
        return meta

    def delete(self, ns: str, key: bytes) -> KomeEntryMeta:
        meta = KomeEntryMeta()
        key_arr = (ctypes.c_uint8 * len(key))(*key)
        _check(_lib.kome_delete(
            self._handle, ns.encode(),
            ctypes.cast(key_arr, ctypes.POINTER(ctypes.c_uint8)), len(key),
            ctypes.byref(meta)))
        return meta

    def get(self, ns: str, key: bytes) -> Tuple[Optional[bytes], KomeEntryMeta]:
        """Read a value and its metadata. Returns (value_bytes, meta).
        Raises KomeError (NOT_FOUND) for deleted/tombstoned entries."""
        meta = KomeEntryMeta()
        key_arr = (ctypes.c_uint8 * len(key))(*key)
        value_ptr = ctypes.POINTER(ctypes.c_uint8)()
        value_len = ctypes.c_size_t(0)
        _check(_lib.kome_get(
            self._handle, ns.encode(),
            ctypes.cast(key_arr, ctypes.POINTER(ctypes.c_uint8)), len(key),
            ctypes.byref(value_ptr), ctypes.byref(value_len),
            ctypes.byref(meta)))
        if value_ptr and value_len.value > 0:
            result = bytes(value_ptr[:value_len.value])
            _lib.kome_free_value(value_ptr)
        else:
            result = None
        return result, meta

    def get_meta(self, ns: str, key: bytes) -> KomeEntryMeta:
        meta = KomeEntryMeta()
        key_arr = (ctypes.c_uint8 * len(key))(*key)
        _check(_lib.kome_get_meta(
            self._handle, ns.encode(),
            ctypes.cast(key_arr, ctypes.POINTER(ctypes.c_uint8)), len(key),
            ctypes.byref(meta)))
        return meta

    def attach_transport(self, transport: Transport):
        self._transport_ref = transport
        _check(_lib.kome_attach_transport(
            self._handle, ctypes.byref(transport.c_transport)))

    def version_vector(self) -> Dict[bytes, int]:
        entries = ctypes.POINTER(KomeVersionEntry)()
        count = ctypes.c_size_t(0)
        _check(_lib.kome_version_vector(
            self._handle, ctypes.byref(entries), ctypes.byref(count)))
        result = {}
        for i in range(count.value):
            author = bytes(entries[i].author)
            result[author] = entries[i].seq
        if entries:
            _lib.kome_free_version_vector(entries)
        return result

    def list_namespaces(self) -> List[str]:
        ns_out = ctypes.POINTER(ctypes.c_char_p)()
        count = ctypes.c_size_t(0)
        _check(_lib.kome_list_namespaces(
            self._handle, ctypes.byref(ns_out), ctypes.byref(count)))
        result = []
        for i in range(count.value):
            result.append(ns_out[i].decode())
        if ns_out:
            _lib.kome_free_namespaces(ns_out, count)
        return result

    def list_keys(self, ns: str) -> List[bytes]:
        keys_ptr = ctypes.POINTER(ctypes.POINTER(ctypes.c_uint8))()
        lens_ptr = ctypes.POINTER(ctypes.c_size_t)()
        count = ctypes.c_size_t(0)
        _check(_lib.kome_list_keys(
            self._handle, ns.encode(),
            ctypes.byref(keys_ptr), ctypes.byref(lens_ptr), ctypes.byref(count)))
        result = []
        for i in range(count.value):
            result.append(bytes(keys_ptr[i][:lens_ptr[i]]))
        if keys_ptr:
            _lib.kome_free_keys(keys_ptr, lens_ptr, count)
        return result

    def on_remote_change(self, callback: Callable):
        """Register a callback for remote changes.

        callback(ns: str, key: bytes, value: bytes, meta: KomeEntryMeta)
        """
        @REMOTE_CHANGE_CB
        def _cb(_ud, ns, key, key_len, value, value_len, meta):
            ns_str = ns.decode() if ns else ""
            key_bytes = bytes(key[:key_len]) if key else b""
            val_bytes = bytes(value[:value_len]) if value else b""
            callback(ns_str, key_bytes, val_bytes, meta.contents if meta else None)

        self._callbacks.append(_cb)
        _lib.kome_on_remote_change(self._handle, _cb, None)

    def set_log_level(self, level: int):
        _lib.kome_set_log_level(self._handle, level)

    def stats(self) -> KomeStats:
        s = KomeStats()
        _check(_lib.kome_stats(self._handle, ctypes.byref(s)))
        return s

    @staticmethod
    def version() -> str:
        return _lib.kome_version().decode()

    @staticmethod
    def errstr(code: int) -> str:
        return _lib.kome_errstr(code).decode()
