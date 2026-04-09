"""Tests for Kome Python bindings."""

import os
import sys
import tempfile
import pytest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from kome import Engine, KomeError, Transport


@pytest.fixture
def db_path():
    path = os.path.join(tempfile.gettempdir(), "kome_pytest.db")
    yield path
    for suffix in ("", "-wal", "-shm"):
        try:
            os.remove(path + suffix)
        except FileNotFoundError:
            pass


@pytest.fixture
def engine(db_path):
    e = Engine(db_path)
    yield e
    e.close()


class TestLifecycle:
    def test_open_close(self, db_path):
        e = Engine(db_path)
        e.close()

    def test_context_manager(self, db_path):
        with Engine(db_path) as e:
            assert e is not None

    def test_version(self):
        assert Engine.version() == "0.0.1"

    def test_errstr(self):
        assert Engine.errstr(0) == "OK"
        assert Engine.errstr(1) == "misuse of API"


class TestData:
    def test_put(self, engine):
        engine.set_identity(b"test_key_1234567890123456")
        meta = engine.put("contacts", b"user1", b"Alice")
        assert meta.timestamp_us > 0
        assert meta.seq == 1
        assert meta.value_len == 5
        assert meta.tombstone == 0

    def test_put_without_identity(self, engine):
        with pytest.raises(KomeError):
            engine.put("test", b"key", b"value")

    def test_get(self, engine):
        engine.set_identity(b"test_key_1234567890123456")
        engine.put("test", b"mykey", b"myvalue")
        value, meta = engine.get("test", b"mykey")
        assert value == b"myvalue"
        assert meta.value_len == 7
        assert meta.tombstone == 0

    def test_get_deleted_returns_not_found(self, engine):
        engine.set_identity(b"test_key_1234567890123456")
        engine.put("test", b"dkey", b"data")
        engine.delete("test", b"dkey")
        with pytest.raises(KomeError) as exc_info:
            engine.get("test", b"dkey")
        assert exc_info.value.code == 4  # KOME_ERR_NOT_FOUND

    def test_get_with_tombstones(self, engine):
        engine.set_identity(b"test_key_1234567890123456")
        engine.put("test", b"dkey2", b"data")
        engine.delete("test", b"dkey2")
        value, meta = engine.get_with_tombstones("test", b"dkey2")
        assert value is None
        assert meta.tombstone == 1

    def test_get_not_found(self, engine):
        with pytest.raises(KomeError):
            engine.get("test", b"nonexistent")

    def test_get_meta(self, engine):
        engine.set_identity(b"test_key_1234567890123456")
        engine.put("test", b"mykey", b"myvalue")
        meta = engine.get_meta("test", b"mykey")
        assert meta.value_len == 7
        assert meta.tombstone == 0

    def test_delete(self, engine):
        engine.set_identity(b"test_key_1234567890123456")
        engine.put("test", b"delme", b"data")
        meta = engine.delete("test", b"delme")
        assert meta.tombstone == 1

    def test_version_vector(self, engine):
        engine.set_identity(b"test_key_1234567890123456")
        engine.put("test", b"k", b"v")
        vv = engine.version_vector()
        assert len(vv) == 1
        assert list(vv.values())[0] == 1

    def test_stats(self, engine):
        engine.set_identity(b"test_key_1234567890123456")
        engine.put("ns1", b"k", b"v")
        engine.put("ns2", b"k", b"v")
        s = engine.stats()
        assert s.total_entries == 2
        assert s.namespace_count == 2

    def test_list_namespaces(self, engine):
        engine.set_identity(b"test_key_1234567890123456")
        engine.put("beta", b"k", b"v")
        engine.put("alpha", b"k", b"v")
        ns = engine.list_namespaces()
        assert ns == ["alpha", "beta"]

    def test_list_keys(self, engine):
        engine.set_identity(b"test_key_1234567890123456")
        engine.put("contacts", b"alice", b"data1")
        engine.put("contacts", b"bob", b"data2")
        engine.put("other", b"carol", b"data3")
        keys = engine.list_keys("contacts")
        assert len(keys) == 2
        assert b"alice" in keys
        assert b"bob" in keys

    def test_list_keys_empty(self, engine):
        keys = engine.list_keys("empty")
        assert keys == []


class TestSync:
    def test_two_engine_sync(self):
        path_a = os.path.join(tempfile.gettempdir(), "kome_py_a.db")
        path_b = os.path.join(tempfile.gettempdir(), "kome_py_b.db")

        for p in (path_a, path_b):
            for suffix in ("", "-wal", "-shm"):
                try:
                    os.remove(p + suffix)
                except FileNotFoundError:
                    pass

        try:
            transport_a = LoopbackTransport()
            transport_b = LoopbackTransport()
            transport_a.other = transport_b
            transport_b.other = transport_a
            transport_a.my_fp = b"\xAA" * 32
            transport_b.my_fp = b"\xBB" * 32

            with Engine(path_a) as ea, Engine(path_b) as eb:
                ea.set_identity(b"aaaa" * 8)
                eb.set_identity(b"bbbb" * 8)

                ea.put("test", b"key1", b"value1")
                ea.put("test", b"key2", b"value2")

                ea.attach_transport(transport_a)
                eb.attach_transport(transport_b)

                transport_a.on_peer(transport_b.my_fp, True)
                transport_b.on_peer(transport_a.my_fp, True)

                value, meta = eb.get("test", b"key1")
                assert value == b"value1"
                value, meta = eb.get("test", b"key2")
                assert value == b"value2"

        finally:
            for p in (path_a, path_b):
                for suffix in ("", "-wal", "-shm"):
                    try:
                        os.remove(p + suffix)
                    except FileNotFoundError:
                        pass


class LoopbackTransport(Transport):
    def __init__(self):
        super().__init__()
        self.other = None
        self.my_fp = b"\x00" * 32

    def send(self, peer_fp: bytes, data: bytes):
        if self.other:
            self.other.on_recv(self.my_fp, data)
