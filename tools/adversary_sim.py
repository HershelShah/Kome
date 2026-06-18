#!/usr/bin/env python3
"""adversary_sim.py — multi-process adversarial simulation against the built
binaries (netnode, relayd, rendezvousd) over real localhost UDP.

Spins up honest nodes/services and a malicious actor that injects garbage,
malformed protocol frames, oversized payloads, and spoofed-shaped requests,
then asserts the honest side (a) never crashes (no signal death) and (b) where
applicable still converges / refuses to be used as a reflector.

Run:  python3 tools/adversary_sim.py /path/to/build
Exit: 0 if all scenarios pass, 1 otherwise.
"""
import os, sys, socket, subprocess, time, random, threading, signal

BUILD = sys.argv[1] if len(sys.argv) > 1 else "build"
random.seed(1234)
results = []


def record(name, ok, detail=""):
    results.append((name, ok, detail))
    print(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f" — {detail}" if detail else ""))


def free_port():
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    s.bind(("127.0.0.1", 0))
    p = s.getsockname()[1]
    s.close()
    return p


def launch(args, log):
    f = open(log, "w")
    return subprocess.Popen(args, stdout=f, stderr=subprocess.STDOUT)


CRASH_SIGS = {signal.SIGSEGV, signal.SIGABRT, signal.SIGBUS, signal.SIGFPE,
              signal.SIGILL}

def crashed(proc):
    """True only if the process died from a *fault* signal (segfault/abort/etc.).
    SIGTERM/SIGKILL that we send to stop a daemon are not crashes."""
    rc = proc.returncode
    return rc is not None and rc < 0 and (-rc) in CRASH_SIGS


def flood(target_port, dur_s, rate_hz, mk):
    """Blast attacker-crafted datagrams at 127.0.0.1:target_port."""
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    end = time.time() + dur_s
    gap = 1.0 / rate_hz
    n = 0
    while time.time() < end:
        try:
            s.sendto(mk(), ("127.0.0.1", target_port))
            n += 1
        except OSError:
            pass
        time.sleep(gap)
    s.close()
    return n


# --- malformed-datagram generators -----------------------------------------
def junk_small():
    return bytes(random.getrandbits(8) for _ in range(random.randint(1, 40)))

def junk_handshakeish():
    # 32-byte "ephemeral"-sized blob — looks like a Noise msg1 to confuse the
    # pre-key handshake of an in-progress connect_and_sync.
    return bytes(random.getrandbits(8) for _ in range(random.choice([32, 80, 96])))

def junk_oversized():
    return bytes(random.getrandbits(8) for _ in range(60000))  # near UDP datagram cap


# ===========================================================================
# Scenario 1 — garbage flood at a node mid-handshake: must not crash.
# ===========================================================================
def scenario_node_flood(heavy):
    pa, pb = free_port(), free_port()
    for f in ("/tmp/sim_a.db", "/tmp/sim_b.db"):
        try: os.remove(f)
        except OSError: pass
    b = launch([f"{BUILD}/netnode", "--db", "/tmp/sim_b.db", "--seed", "2",
                "--bind", "127.0.0.1", "--port", str(pb), "--role", "responder",
                "--peer", f"127.0.0.1:{pa}"], "/tmp/sim_nodeB.log")
    time.sleep(0.3)
    rate = 4000 if heavy else 150
    th = threading.Thread(target=flood, args=(pb, 6.0, rate,
                          junk_handshakeish if not heavy else junk_oversized))
    th.start()
    a = launch([f"{BUILD}/netnode", "--db", "/tmp/sim_a.db", "--seed", "1",
                "--bind", "127.0.0.1", "--port", str(pa), "--role", "initiator",
                "--peer", f"127.0.0.1:{pb}"], "/tmp/sim_nodeA.log")
    try:
        a.wait(timeout=30); b.wait(timeout=30)
    except subprocess.TimeoutExpired:
        a.kill(); b.kill()
    th.join()
    tag = "heavy" if heavy else "moderate"
    if crashed(a) or crashed(b):
        record(f"node survives {tag} garbage flood (no crash)", False,
               f"A rc={a.returncode} B rc={b.returncode}")
        return
    conv = False
    try:
        conv = "converged" in open("/tmp/sim_nodeA.log").read()
    except OSError:
        pass
    extra = "still converged" if conv else "no crash (convergence DoS'd, as documented)"
    record(f"node survives {tag} garbage flood (no crash)", True, extra)


# ===========================================================================
# Scenario 2 — rendezvous LOOKUP must NOT reflect (F1).
# ===========================================================================
def scenario_rendezvous_reflection():
    port = free_port()
    d = launch([f"{BUILD}/rendezvousd", "--listen", str(port)], "/tmp/sim_rdv.log")
    time.sleep(0.3)
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.settimeout(1.0)
        target = bytes(32)  # arbitrary (unregistered) key
        # A bare one-shot LOOKUP — what a spoofed-source reflector would send.
        s.sendto(b"L" + target, ("127.0.0.1", port))
        reply = s.recv(4096)
        # Must be a challenge ('C' | 16), never an immediate peer reply ('P').
        ok = len(reply) == 17 and reply[0:1] == b"C"
        reflected = reply[0:1] == b"P"
        record("rendezvous LOOKUP requires return-routability (F1)", ok and not reflected,
               f"reply[0]={reply[0:1]!r} len={len(reply)}"
               + (" REFLECTED!" if reflected else ""))

        # The honest two-phase flow still resolves (found=0 for unregistered).
        nonce = reply[1:17]
        s.sendto(b"M" + target + nonce, ("127.0.0.1", port))
        peer = s.recv(4096)
        ok2 = peer[0:1] == b"P" and len(peer) >= 2 and peer[1] == 0
        record("rendezvous two-phase LOOKUP still works (found=0)", ok2,
               f"reply[0]={peer[0:1]!r} found={peer[1] if len(peer)>1 else '?'}")
        s.close()
    finally:
        d.send_signal(signal.SIGTERM); d.wait()
    record("rendezvousd survived LOOKUP probes (no crash)", not crashed(d),
           f"rc={d.returncode}")


# ===========================================================================
# Scenario 3 — relay garbage flood: stays alive and still serves a valid FETCH.
# ===========================================================================
def scenario_relay_robustness():
    port = free_port()
    d = launch([f"{BUILD}/relayd", "--listen", str(port)], "/tmp/sim_relay.log")
    time.sleep(0.3)
    # Flood malformed datagrams (random, plus opcode-shaped junk).
    def mk():
        if random.random() < 0.5:
            return random.choice([b"S", b"F", b"A", b"C"]) + junk_small()
        return junk_small()
    flood(port, 3.0, 2000, mk)
    # After the flood, a well-formed FETCH must still elicit a challenge.
    served = False
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.settimeout(1.0)
        s.sendto(b"F" + bytes(32), ("127.0.0.1", port))
        reply = s.recv(4096)
        served = len(reply) == 17 and reply[0:1] == b"C"
        s.close()
    except socket.timeout:
        pass
    alive = d.poll() is None
    d.send_signal(signal.SIGTERM); d.wait()
    record("relayd survives garbage flood and still serves FETCH", alive and served
           and not crashed(d), f"alive={alive} served={served} rc={d.returncode}")


# ===========================================================================
# Scenario 4 — oversized/truncated datagrams at the rendezvous parser.
# ===========================================================================
def scenario_parser_fuzz():
    port = free_port()
    d = launch([f"{BUILD}/rendezvousd", "--listen", str(port)], "/tmp/sim_fuzz.log")
    time.sleep(0.3)
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    s.setblocking(False)  # most malformed inputs draw no reply — never block
    payloads = [b"", b"L", b"L" + bytes(5), b"M" + bytes(10), b"U" + bytes(200),
                b"R" + bytes(31), b"\xff" * 65000, b"M" + bytes(32) + bytes(15)]
    for _ in range(5000):
        p = random.choice(payloads) if random.random() < 0.3 else junk_small()
        try: s.sendto(p, ("127.0.0.1", port))
        except OSError: pass
        try:
            while True: s.recv(4096)   # drain any replies, non-blocking
        except OSError:
            pass
    s.close()
    alive = d.poll() is None
    d.send_signal(signal.SIGTERM); d.wait()
    record("rendezvous parser survives malformed/oversized fuzz", alive and not crashed(d),
           f"alive={alive} rc={d.returncode}")


if __name__ == "__main__":
    print(f"== adversarial simulation (build={BUILD}) ==")
    scenario_rendezvous_reflection()
    scenario_relay_robustness()
    scenario_parser_fuzz()
    scenario_node_flood(heavy=False)
    scenario_node_flood(heavy=True)
    print("\n== summary ==")
    bad = [n for n, ok, _ in results if not ok]
    for n, ok, d in results:
        print(f"  {'ok ' if ok else 'XX '} {n}")
    print(f"\n{len(results)-len(bad)}/{len(results)} scenarios passed")
    sys.exit(1 if bad else 0)
