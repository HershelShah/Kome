"""Python binding for the P2P replication engine (M6).

A thin ctypes wrapper over libsync_engine. Mirrors the C ABI in
include/sync_engine.h: create an engine from a 32-byte seed, set/get/delete,
export/apply change records, and compare deterministic digests.

Set SYNC_ENGINE_LIB to the shared library path, or place it on the loader
path. Example:
    SYNC_ENGINE_LIB=build/libsync_engine.so python -m pytest bindings/python
"""
import ctypes
import os

SITE_ID_LEN = 32
PUBKEY_LEN = 32
SIG_LEN = 64
SEED_LEN = 32
DIGEST_LEN = 32

SYNC_OK = 0
SYNC_ERR_NOTFOUND = 3

CHANGE_EXISTENCE = 0
CHANGE_REGISTER = 1


class _Hlc(ctypes.Structure):
    _fields_ = [("physical", ctypes.c_uint64), ("logical", ctypes.c_uint32)]


class _Change(ctypes.Structure):
    _fields_ = [
        ("kind", ctypes.c_uint8),
        ("ns", ctypes.c_void_p), ("ns_len", ctypes.c_size_t),
        ("entity", ctypes.c_void_p), ("entity_len", ctypes.c_size_t),
        ("field", ctypes.c_void_p), ("field_len", ctypes.c_size_t),
        ("causal_length", ctypes.c_uint64),
        ("value", ctypes.c_void_p), ("value_len", ctypes.c_size_t),
        ("hlc", _Hlc),
        ("author", ctypes.c_uint8 * PUBKEY_LEN),
        ("signature", ctypes.c_uint8 * SIG_LEN),
    ]


def _find_lib():
    env = os.environ.get("SYNC_ENGINE_LIB")
    candidates = [env] if env else []
    here = os.path.dirname(os.path.abspath(__file__))
    root = os.path.abspath(os.path.join(here, "..", ".."))
    for d in ("build", "build-asan", "."):
        candidates.append(os.path.join(root, d, "libsync_engine.so"))
    candidates.append("libsync_engine.so")
    for c in candidates:
        if c and os.path.exists(c):
            return c
    # last resort: let the loader search
    return "libsync_engine.so"


_lib = ctypes.CDLL(_find_lib())

_lib.sync_engine_create.restype = ctypes.c_void_p
_lib.sync_engine_create.argtypes = [ctypes.c_char_p]
_lib.sync_engine_open.restype = ctypes.c_void_p
_lib.sync_engine_open.argtypes = [ctypes.c_char_p, ctypes.c_char_p]
_lib.sync_engine_destroy.argtypes = [ctypes.c_void_p]
_lib.sync_engine_set.argtypes = [ctypes.c_void_p] + [ctypes.c_char_p, ctypes.c_size_t] * 4
_lib.sync_engine_delete.argtypes = [ctypes.c_void_p] + [ctypes.c_char_p, ctypes.c_size_t] * 2
_lib.sync_engine_get.argtypes = [ctypes.c_void_p] + [ctypes.c_char_p, ctypes.c_size_t] * 3 + [
    ctypes.POINTER(ctypes.POINTER(ctypes.c_uint8)), ctypes.POINTER(ctypes.c_size_t)]
_lib.sync_engine_exists.argtypes = [ctypes.c_void_p] + [ctypes.c_char_p, ctypes.c_size_t] * 2 + [
    ctypes.POINTER(ctypes.c_int)]
_lib.sync_engine_export.argtypes = [ctypes.c_void_p,
                                    ctypes.POINTER(ctypes.POINTER(_Change)),
                                    ctypes.POINTER(ctypes.c_size_t)]
_lib.sync_engine_apply.argtypes = [ctypes.c_void_p, ctypes.POINTER(_Change)]
_lib.sync_changes_free.argtypes = [ctypes.POINTER(_Change), ctypes.c_size_t]
_lib.sync_engine_digest.argtypes = [ctypes.c_void_p, ctypes.c_char_p]
_lib.sync_engine_identity.argtypes = [ctypes.c_void_p, ctypes.c_char_p]
_lib.sync_free.argtypes = [ctypes.c_void_p]
_lib.sync_abi_version.restype = ctypes.c_uint32


def abi_version():
    return _lib.sync_abi_version()


class Engine:
    """A convergent replica. Not thread-safe; one engine per thread or guard it."""

    def __init__(self, seed: bytes, path: str = None):
        if len(seed) != SEED_LEN:
            raise ValueError("seed must be 32 bytes")
        if path is None:
            self._e = _lib.sync_engine_create(seed)
        else:
            self._e = _lib.sync_engine_open(path.encode(), seed)
        if not self._e:
            raise RuntimeError("failed to create engine")

    def close(self):
        if self._e:
            _lib.sync_engine_destroy(self._e)
            self._e = None

    def __enter__(self):
        return self

    def __exit__(self, *a):
        self.close()

    def set(self, ns: bytes, entity: bytes, field: bytes, value: bytes):
        rc = _lib.sync_engine_set(self._e, ns, len(ns), entity, len(entity),
                                  field, len(field), value, len(value))
        if rc != SYNC_OK:
            raise RuntimeError("set failed: %d" % rc)

    def delete(self, ns: bytes, entity: bytes):
        _lib.sync_engine_delete(self._e, ns, len(ns), entity, len(entity))

    def get(self, ns: bytes, entity: bytes, field: bytes):
        out = ctypes.POINTER(ctypes.c_uint8)()
        out_len = ctypes.c_size_t(0)
        rc = _lib.sync_engine_get(self._e, ns, len(ns), entity, len(entity),
                                  field, len(field), ctypes.byref(out),
                                  ctypes.byref(out_len))
        if rc == SYNC_ERR_NOTFOUND:
            return None
        if rc != SYNC_OK:
            raise RuntimeError("get failed: %d" % rc)
        data = ctypes.string_at(out, out_len.value)
        _lib.sync_free(out)
        return data

    def exists(self, ns: bytes, entity: bytes) -> bool:
        p = ctypes.c_int(0)
        _lib.sync_engine_exists(self._e, ns, len(ns), entity, len(entity),
                                ctypes.byref(p))
        return p.value != 0

    def digest(self) -> bytes:
        buf = ctypes.create_string_buffer(DIGEST_LEN)
        _lib.sync_engine_digest(self._e, buf)
        return buf.raw

    def identity(self) -> bytes:
        buf = ctypes.create_string_buffer(PUBKEY_LEN)
        _lib.sync_engine_identity(self._e, buf)
        return buf.raw

    def replicate_into(self, other: "Engine"):
        """Export this engine's full state and apply it into `other`."""
        arr = ctypes.POINTER(_Change)()
        n = ctypes.c_size_t(0)
        rc = _lib.sync_engine_export(self._e, ctypes.byref(arr), ctypes.byref(n))
        if rc != SYNC_OK:
            raise RuntimeError("export failed: %d" % rc)
        try:
            for i in range(n.value):
                if _lib.sync_engine_apply(other._e, ctypes.byref(arr[i])) != SYNC_OK:
                    raise RuntimeError("apply failed")
        finally:
            _lib.sync_changes_free(arr, n)
