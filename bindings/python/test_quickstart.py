"""M7/A5 — the README Python quickstart, run against the installed package.

This is the wheel's exit gate: two durable engines write offline, replicate,
converge to an identical digest, and the synced data survives reopening the
log file. In CI it runs from a directory outside the repo with
SYNC_ENGINE_LIB unset, so the library under test is the one bundled in the
wheel (kome/_lib/), not a build tree.
"""
import kome as se


def test_quickstart_readme(tmp_path):
    phone = se.Engine(b"\x01" * 32, path=str(tmp_path / "phone.db"))
    laptop = se.Engine(b"\x02" * 32, path=str(tmp_path / "laptop.db"))

    phone.set(b"contacts", b"alice", b"phone", b"555-1234")
    laptop.set(b"contacts", b"bob", b"email", b"bob@example.com")

    phone.replicate_into(laptop)
    laptop.replicate_into(phone)

    assert phone.get(b"contacts", b"bob", b"email") == b"bob@example.com"
    assert laptop.get(b"contacts", b"alice", b"phone") == b"555-1234"
    assert phone.digest() == laptop.digest()

    phone.close()
    laptop.close()

    # Durability: reopening the log shows the synced data persisted. The
    # persisted identity wins on reopen, so the seed is irrelevant here.
    with se.Engine(b"\x01" * 32, path=str(tmp_path / "phone.db")) as again:
        assert again.get(b"contacts", b"bob", b"email") == b"bob@example.com"
        assert again.exists(b"contacts", b"alice")


def test_in_memory_engine_has_no_file(tmp_path):
    with se.Engine(b"\x09" * 32) as e:
        e.set(b"ns", b"k", b"f", b"v")
        assert e.get(b"ns", b"k", b"f") == b"v"
    assert list(tmp_path.iterdir()) == []
