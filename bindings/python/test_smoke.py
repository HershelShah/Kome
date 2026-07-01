"""T6.6 — Python binding smoke test.

Reproduces examples/example.c through the binding: two replicas write
independently, exchange full state, read across, and converge to an identical
digest.
"""
import kome as se


def test_abi_version():
    assert se.abi_version() == 4


def test_write_export_apply_read_digest():
    a = se.Engine(b"\x01" * 32)
    b = se.Engine(b"\x02" * 32)
    try:
        a.set(b"people", b"alice", b"name", b"Alice")
        b.set(b"people", b"bob", b"name", b"Bob")

        # Full-state replication both ways.
        a.replicate_into(b)
        b.replicate_into(a)

        # Each side now sees the other's record.
        assert a.get(b"people", b"bob", b"name") == b"Bob"
        assert b.get(b"people", b"alice", b"name") == b"Alice"

        # Converged to an identical state digest.
        assert a.digest() == b.digest()
        assert len(a.digest()) == 32
    finally:
        a.close()
        b.close()


def test_delete_hides_value():
    a = se.Engine(b"\x03" * 32)
    try:
        a.set(b"ns", b"x", b"f", b"v")
        assert a.exists(b"ns", b"x")
        a.delete(b"ns", b"x")
        assert not a.exists(b"ns", b"x")
        assert a.get(b"ns", b"x", b"f") is None  # presence-filtered
    finally:
        a.close()


def test_distinct_identities():
    a = se.Engine(b"\x04" * 32)
    b = se.Engine(b"\x05" * 32)
    try:
        assert a.identity() != b.identity()
        assert len(a.identity()) == 32
    finally:
        a.close()
        b.close()


if __name__ == "__main__":
    test_abi_version()
    test_write_export_apply_read_digest()
    test_delete_hides_value()
    test_distinct_identities()
    print("python smoke test: OK")
