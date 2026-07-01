"""Deprecated shim — the binding moved to the ``kome`` package (M7).

Kept for one release so ``import sync_engine`` keeps working in existing dev
flows (PYTHONPATH=bindings/python). New code should ``import kome``. Not
shipped in the wheel.
"""
from kome._ffi import *  # noqa: F401,F403
from kome._ffi import __all__  # noqa: F401
