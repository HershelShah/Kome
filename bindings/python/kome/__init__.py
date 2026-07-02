"""Kome — a private, distributed, offline-first sync engine.

Python binding over the C ABI (include/sync_engine.h). SYNC_ENGINE_LIB, when
set, always wins (a loud dev override); otherwise the library bundled in the
wheel (``pip install kome-sync`` -> kome/_lib/) is used, with the CMake build
tree as the source-checkout fallback (see kome._ffi._find_lib).
"""
from kome._ffi import (
    SITE_ID_LEN, PUBKEY_LEN, SIG_LEN, SEED_LEN, DIGEST_LEN,
    SYNC_OK, SYNC_ERR_NOTFOUND, CHANGE_EXISTENCE, CHANGE_REGISTER,
    Engine, abi_version,
)

__all__ = [
    "SITE_ID_LEN", "PUBKEY_LEN", "SIG_LEN", "SEED_LEN", "DIGEST_LEN",
    "SYNC_OK", "SYNC_ERR_NOTFOUND", "CHANGE_EXISTENCE", "CHANGE_REGISTER",
    "Engine", "abi_version",
]

try:
    from importlib.metadata import version as _dist_version
    __version__ = _dist_version("kome-sync")
except Exception:  # source checkout without installed dist metadata
    __version__ = "0.0.0.dev0"
