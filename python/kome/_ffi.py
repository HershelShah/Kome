"""ctypes FFI bindings for libkome."""

import ctypes
import ctypes.util
import os
import sys
from pathlib import Path


# --- Load shared library ---------------------------------------------------

def _find_libkome():
    """Find libkome shared library."""
    # Check LD_LIBRARY_PATH and common build locations
    search_dirs = []

    # From environment
    ld_path = os.environ.get("LD_LIBRARY_PATH", "")
    if ld_path:
        search_dirs.extend(ld_path.split(":"))

    # Relative to this file (common dev layout)
    here = Path(__file__).resolve().parent
    search_dirs.extend([
        str(here / ".." / ".." / "build"),
        str(here / ".." / ".." / "build" / "lib"),
    ])

    ext = {"linux": "so", "darwin": "dylib", "win32": "dll"}.get(sys.platform, "so")
    name = f"libkome.{ext}"

    for d in search_dirs:
        p = Path(d) / name
        if p.exists():
            return str(p)

    # Try system-wide
    found = ctypes.util.find_library("kome")
    if found:
        return found

    raise OSError(f"Cannot find {name}. Set LD_LIBRARY_PATH to the build directory.")


_lib = ctypes.CDLL(_find_libkome())


# --- C types ---------------------------------------------------------------

class KomeEntryMeta(ctypes.Structure):
    _fields_ = [
        ("timestamp_us", ctypes.c_uint64),
        ("author", ctypes.c_uint8 * 32),
        ("seq", ctypes.c_uint64),
        ("hash", ctypes.c_uint8 * 32),
        ("value_len", ctypes.c_uint32),
        ("tombstone", ctypes.c_uint8),
        ("signature", ctypes.c_uint8 * 64),
    ]


class KomeConfig(ctypes.Structure):
    _fields_ = [
        ("path", ctypes.c_char_p),
        ("disable_wal", ctypes.c_int),
        ("busy_timeout_ms", ctypes.c_int),
        ("encryption_key", ctypes.POINTER(ctypes.c_uint8)),
        ("encryption_key_len", ctypes.c_size_t),
    ]


class KomeVersionEntry(ctypes.Structure):
    _fields_ = [
        ("author", ctypes.c_uint8 * 32),
        ("seq", ctypes.c_uint64),
    ]


class KomeStats(ctypes.Structure):
    _fields_ = [
        ("total_entries", ctypes.c_uint64),
        ("tombstone_count", ctypes.c_uint64),
        ("namespace_count", ctypes.c_uint64),
        ("db_size_bytes", ctypes.c_uint64),
    ]


# Transport callback types
SEND_FN = ctypes.CFUNCTYPE(None, ctypes.c_void_p, ctypes.POINTER(ctypes.c_uint8),
                            ctypes.POINTER(ctypes.c_uint8), ctypes.c_size_t)
RECV_CB = ctypes.CFUNCTYPE(None, ctypes.c_void_p, ctypes.POINTER(ctypes.c_uint8),
                            ctypes.POINTER(ctypes.c_uint8), ctypes.c_size_t)
SET_RECV_FN = ctypes.CFUNCTYPE(None, ctypes.c_void_p, RECV_CB, ctypes.c_void_p)
PEER_CB = ctypes.CFUNCTYPE(None, ctypes.c_void_p, ctypes.POINTER(ctypes.c_uint8), ctypes.c_int)
SET_PEER_FN = ctypes.CFUNCTYPE(None, ctypes.c_void_p, PEER_CB, ctypes.c_void_p)


class KomeTransport(ctypes.Structure):
    _fields_ = [
        ("send", SEND_FN),
        ("set_recv_callback", SET_RECV_FN),
        ("set_peer_callback", SET_PEER_FN),
        ("user_data", ctypes.c_void_p),
    ]


# Remote change callback
REMOTE_CHANGE_CB = ctypes.CFUNCTYPE(
    None, ctypes.c_void_p,
    ctypes.c_char_p, ctypes.POINTER(ctypes.c_uint8), ctypes.c_size_t,
    ctypes.POINTER(ctypes.c_uint8), ctypes.c_size_t,
    ctypes.POINTER(KomeEntryMeta))


# --- Function signatures ---------------------------------------------------

_lib.kome_open.argtypes = [ctypes.POINTER(KomeConfig), ctypes.POINTER(ctypes.c_void_p)]
_lib.kome_open.restype = ctypes.c_int

_lib.kome_close.argtypes = [ctypes.c_void_p]
_lib.kome_close.restype = None

_lib.kome_set_identity.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_uint8), ctypes.c_size_t]
_lib.kome_set_identity.restype = ctypes.c_int

_lib.kome_put.argtypes = [
    ctypes.c_void_p, ctypes.c_char_p,
    ctypes.POINTER(ctypes.c_uint8), ctypes.c_size_t,
    ctypes.POINTER(ctypes.c_uint8), ctypes.c_size_t,
    ctypes.POINTER(KomeEntryMeta)
]
_lib.kome_put.restype = ctypes.c_int

_lib.kome_delete.argtypes = [
    ctypes.c_void_p, ctypes.c_char_p,
    ctypes.POINTER(ctypes.c_uint8), ctypes.c_size_t,
    ctypes.POINTER(KomeEntryMeta)
]
_lib.kome_delete.restype = ctypes.c_int

_lib.kome_get.argtypes = [
    ctypes.c_void_p, ctypes.c_char_p,
    ctypes.POINTER(ctypes.c_uint8), ctypes.c_size_t,
    ctypes.POINTER(ctypes.POINTER(ctypes.c_uint8)), ctypes.POINTER(ctypes.c_size_t),
    ctypes.POINTER(KomeEntryMeta)
]
_lib.kome_get.restype = ctypes.c_int

_lib.kome_free_value.argtypes = [ctypes.POINTER(ctypes.c_uint8)]
_lib.kome_free_value.restype = None

_lib.kome_get_meta.argtypes = [
    ctypes.c_void_p, ctypes.c_char_p,
    ctypes.POINTER(ctypes.c_uint8), ctypes.c_size_t,
    ctypes.POINTER(KomeEntryMeta)
]
_lib.kome_get_meta.restype = ctypes.c_int

_lib.kome_attach_transport.argtypes = [ctypes.c_void_p, ctypes.POINTER(KomeTransport)]
_lib.kome_attach_transport.restype = ctypes.c_int

_lib.kome_sync_with.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_uint8)]
_lib.kome_sync_with.restype = ctypes.c_int

_lib.kome_version_vector.argtypes = [
    ctypes.c_void_p,
    ctypes.POINTER(ctypes.POINTER(KomeVersionEntry)),
    ctypes.POINTER(ctypes.c_size_t)
]
_lib.kome_version_vector.restype = ctypes.c_int

_lib.kome_free_version_vector.argtypes = [ctypes.POINTER(KomeVersionEntry)]
_lib.kome_free_version_vector.restype = None

_lib.kome_list_namespaces.argtypes = [
    ctypes.c_void_p,
    ctypes.POINTER(ctypes.POINTER(ctypes.c_char_p)),
    ctypes.POINTER(ctypes.c_size_t)
]
_lib.kome_list_namespaces.restype = ctypes.c_int

_lib.kome_free_namespaces.argtypes = [ctypes.POINTER(ctypes.c_char_p), ctypes.c_size_t]
_lib.kome_free_namespaces.restype = None

_lib.kome_list_keys.argtypes = [
    ctypes.c_void_p, ctypes.c_char_p,
    ctypes.POINTER(ctypes.POINTER(ctypes.POINTER(ctypes.c_uint8))),
    ctypes.POINTER(ctypes.POINTER(ctypes.c_size_t)),
    ctypes.POINTER(ctypes.c_size_t)
]
_lib.kome_list_keys.restype = ctypes.c_int

_lib.kome_free_keys.argtypes = [
    ctypes.POINTER(ctypes.POINTER(ctypes.c_uint8)),
    ctypes.POINTER(ctypes.c_size_t),
    ctypes.c_size_t
]
_lib.kome_free_keys.restype = None

_lib.kome_on_remote_change.argtypes = [ctypes.c_void_p, REMOTE_CHANGE_CB, ctypes.c_void_p]
_lib.kome_on_remote_change.restype = None

_lib.kome_stats.argtypes = [ctypes.c_void_p, ctypes.POINTER(KomeStats)]
_lib.kome_stats.restype = ctypes.c_int

_lib.kome_errstr.argtypes = [ctypes.c_int]
_lib.kome_errstr.restype = ctypes.c_char_p

_lib.kome_version.argtypes = []
_lib.kome_version.restype = ctypes.c_char_p
