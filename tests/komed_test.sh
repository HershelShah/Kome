#!/usr/bin/env bash
# komed end-to-end test: two standalone komed processes, two durable SQLite
# databases, syncing over real UDP through the production secure path (Noise
# XX + identity proof + capability-scoped reconcile) — driven purely through
# the komed binary and its config file, the way an operator would run it.
#
#   cmake -B build && cmake --build build --target komed sync_engine_shared
#   tests/komed_test.sh
#
# komed A is started with *no* peer= lines at all, to exercise its passive
# responder path: komed B (which lists A as its one static peer) dials in,
# and A must accept and reconcile without having A's own address configured.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BIN="${KOMED_BIN:-$ROOT/build/komed}"
LIB="${SYNC_ENGINE_LIB:-$ROOT/build/libsync_engine.so}"
PYPATH="$ROOT/bindings/python"

if ! command -v python3 >/dev/null 2>&1; then
    echo "komed_test: python3 not available, skipping"
    exit 77
fi
if [ ! -x "$BIN" ]; then
    echo "komed_test: komed binary not found/executable at $BIN"
    exit 1
fi
if [ ! -f "$LIB" ]; then
    echo "komed_test: sync_engine shared lib not found at $LIB"
    exit 1
fi
# This test loads libsync_engine.so a second time via Python ctypes (the
# verification steps below use the Python binding directly). Under an
# ASan/TSan build that second, non-LD_PRELOADed load of the sanitizer-
# instrumented .so reliably fails at the dynamic-linker level ("ASan runtime
# does not come first in initial library list" / "cannot allocate memory in
# static TLS block") — not a real product bug — so skip rather than report a
# false failure. CMake passes the active sanitizer through
# KOMED_TEST_SANITIZER; UBSan has no such requirement and still runs.
case "${KOMED_TEST_SANITIZER:-}" in
    address|thread)
        echo "komed_test: skipping under -DSYNC_SANITIZER=$KOMED_TEST_SANITIZER" \
             "(Python ctypes cannot load an instrumented libsync_engine.so" \
             "without LD_PRELOADing the sanitizer runtime first)"
        exit 77
        ;;
esac

TMP="$(mktemp -d)"
APID=""
BPID=""
CPID=""
DPID=""
P_PID=""
QPID=""
cleanup() {
    [ -n "$APID" ] && kill -9 "$APID" >/dev/null 2>&1
    [ -n "$BPID" ] && kill -9 "$BPID" >/dev/null 2>&1
    [ -n "$CPID" ] && kill -9 "$CPID" >/dev/null 2>&1
    [ -n "$DPID" ] && kill -9 "$DPID" >/dev/null 2>&1
    [ -n "$P_PID" ] && kill -9 "$P_PID" >/dev/null 2>&1
    [ -n "$QPID" ] && kill -9 "$QPID" >/dev/null 2>&1
    wait >/dev/null 2>&1
    rm -rf "$TMP"
}
trap cleanup EXIT

PORT_A=7401
PORT_B=7402
PORT_C=7403
PORT_D=7404
PORT_P=7405
PORT_Q=7406

pyrun() {
    PYTHONPATH="$PYPATH" SYNC_ENGINE_LIB="$LIB" python3 "$@"
}

fail() { echo "komed_test: FAIL: $*" >&2; exit 1; }

# Wait (up to 5s, 0.1s poll) for a pid to exit; fail loudly if it doesn't.
wait_exit_5s() {
    local pid="$1" who="$2"
    for i in $(seq 1 50); do
        kill -0 "$pid" >/dev/null 2>&1 || return 0
        sleep 0.1
    done
    kill -0 "$pid" >/dev/null 2>&1 && fail "$who did not exit within 5s of SIGTERM"
}

# Mutual peer= restart-recovery, one iteration: SIGTERM the side named by the
# $1 pid variable (a nameref onto P_PID or QPID), write `marker` offline into
# its db, restart it, and verify `marker` reaches the *other* (surviving,
# never-restarted) side's db within `budget_s` seconds. Used looped, always
# against the derived-responder side of the edge — see step [9/10].
mutual_restart_and_check() {
    local -n pidref="$1"
    local resp_conf="$2" resp_db="$3" resp_log="$4"
    local other_db="$5" other_log="$6" other_pid="$7" marker="$8" budget_s="$9"

    kill -TERM "$pidref"
    wait_exit_5s "$pidref" "komed $1"
    wait "$pidref" 2>/dev/null

    pyrun - "$resp_db" "$marker" <<'PY'
import sys
import kome as se
db, marker = sys.argv[1], sys.argv[2]
e = se.Engine(b'\x00' * 32, path=db)
e.set(b"t", marker.encode(), b"v", ("val-%s" % marker).encode())
e.close()
PY

    "$BIN" "$resp_conf" >>"$resp_log" 2>&1 &
    pidref=$!

    local recovered=0 i out
    for i in $(seq 1 "$((budget_s * 10))"); do
        sleep 0.1
        kill -0 "$pidref" >/dev/null 2>&1 || fail "komed $1 died during mutual-peer restart loop:\n$(tail -n 40 "$resp_log")"
        kill -0 "$other_pid" >/dev/null 2>&1 || fail "surviving mutual-peer komed died:\n$(tail -n 40 "$other_log")"
        out=$(pyrun - "$other_db" "$marker" <<'PY'
import sys
import kome as se
db, marker = sys.argv[1], sys.argv[2]
e = se.Engine(b'\x00' * 32, path=db)
present = e.exists(b"t", marker.encode())
e.close()
print("YES" if present else "NO")
PY
)
        if [ "$out" = "YES" ]; then recovered=1; break; fi
    done
    [ "$recovered" -eq 1 ] || fail "mutual-peer restart recovery: marker $marker did not reach $other_db within ${budget_s}s\n--- $resp_log (tail) ---\n$(tail -n 40 "$resp_log")\n--- $other_log (tail) ---\n$(tail -n 40 "$other_log")"
}

# Best-effort fallback for ad-hoc sanitizer builds that don't run through the
# CMake-set KOMED_TEST_SANITIZER (e.g. LIB pointed by hand at a local ASan/TSan
# build): if the Python ctypes load of libsync_engine.so itself blows up with
# a sanitizer-runtime-preload error, skip (77) instead of misreporting it as a
# product failure.
SANITIZER_LOAD_ERR='libasan|libtsan|ASan runtime does not come first|cannot allocate memory in static TLS block'

echo "=== [1/10] seeding a.db (3 records, ns=t, A-0..A-2) and b.db (3 different) ==="
SEED_ERR="$TMP/seed.err"
pyrun - "$TMP" <<'PY' 2>"$SEED_ERR"
import sys
import kome as se
tmp = sys.argv[1]
e = se.Engine(b'\x01' * 32, path=tmp + "/a.db")
for i in range(3):
    e.set(b"t", ("A-%d" % i).encode(), b"v", ("val-a-%d" % i).encode())
e.close()
e = se.Engine(b'\x02' * 32, path=tmp + "/b.db")
for i in range(3):
    e.set(b"t", ("B-%d" % i).encode(), b"v", ("val-b-%d" % i).encode())
e.close()
PY
cat "$SEED_ERR" >&2
if grep -qE "$SANITIZER_LOAD_ERR" "$SEED_ERR" 2>/dev/null; then
    echo "komed_test: skipping — Python ctypes could not load an instrumented libsync_engine.so"
    exit 77
fi
[ -f "$TMP/a.db" ] || fail "a.db was not created"
[ -f "$TMP/b.db" ] || fail "b.db was not created"

echo "=== [2/10] malformed config => exit 2; directory as config path => exit 2 (FINDING-4) ==="
cat > "$TMP/bad.conf" <<EOF
db=$TMP/bad.db
this_is_not_a_known_key=oops
EOF
"$BIN" "$TMP/bad.conf" >"$TMP/bad.out" 2>"$TMP/bad.err"
rc=$?
[ "$rc" -eq 2 ] || fail "malformed config exited $rc, expected 2 ($(cat "$TMP/bad.err"))"
[ -s "$TMP/bad.err" ] || fail "malformed config produced no stderr message"
echo "    ok: exit 2, stderr: $(cat "$TMP/bad.err")"

mkdir -p "$TMP/a_directory_config"
"$BIN" "$TMP/a_directory_config" >"$TMP/dir.out" 2>"$TMP/dir.err"
rc=$?
[ "$rc" -eq 2 ] || fail "directory-as-config exited $rc, expected 2 ($(cat "$TMP/dir.err"))"
[ -s "$TMP/dir.err" ] || fail "directory-as-config produced no stderr message"
echo "    ok: exit 2, stderr: $(cat "$TMP/dir.err")"

echo "=== [3/10] --identity for both ==="
cat > "$TMP/a.conf" <<EOF
db=$TMP/a.db
listen=$PORT_A
EOF
A_PUB=$("$BIN" "$TMP/a.conf" --identity)
rc=$?
[ "$rc" -eq 0 ] || fail "komed A --identity exited $rc"
echo "$A_PUB" | grep -Eq '^[0-9a-f]{64}$' || fail "A identity not 64 hex chars: '$A_PUB'"

cat > "$TMP/b.conf" <<EOF
db=$TMP/b.db
listen=$PORT_B
peer=${A_PUB}@127.0.0.1:$PORT_A
interval_ms=300
EOF
B_PUB=$("$BIN" "$TMP/b.conf" --identity)
rc=$?
[ "$rc" -eq 0 ] || fail "komed B --identity exited $rc"
echo "$B_PUB" | grep -Eq '^[0-9a-f]{64}$' || fail "B identity not 64 hex chars: '$B_PUB'"
echo "    A=$A_PUB"
echo "    B=$B_PUB"

echo "=== [4/10] starting komed A (no peers, listen $PORT_A) and komed B (peer=A, listen $PORT_B) ==="
"$BIN" "$TMP/a.conf" >"$TMP/a.log" 2>&1 &
APID=$!
sleep 0.3
"$BIN" "$TMP/b.conf" >"$TMP/b.log" 2>&1 &
BPID=$!

echo "=== [5/10] polling for convergence (<=30s) ==="
CONVERGED=0
for i in $(seq 1 30); do
    sleep 1
    kill -0 "$APID" >/dev/null 2>&1 || fail "komed A died early:\n$(cat "$TMP/a.log")"
    kill -0 "$BPID" >/dev/null 2>&1 || fail "komed B died early:\n$(cat "$TMP/b.log")"
    OUT=$(pyrun - "$TMP" <<'PY'
import sys
import kome as se
tmp = sys.argv[1]
want = ["A-0", "A-1", "A-2", "B-0", "B-1", "B-2"]
digests = set()
ok = True
for name in ("a.db", "b.db"):
    e = se.Engine(b'\x00' * 32, path=tmp + "/" + name)
    present = [k for k in want if e.exists(b"t", k.encode())]
    digests.add(e.digest())
    if len(present) != len(want):
        ok = False
    e.close()
print("CONVERGED" if (ok and len(digests) == 1) else "PENDING")
PY
)
    if [ "$OUT" = "CONVERGED" ]; then
        CONVERGED=1
        echo "    converged after ${i}s"
        break
    fi
done
[ "$CONVERGED" -eq 1 ] || fail "did not converge within 30s\n--- a.log ---\n$(cat "$TMP/a.log")\n--- b.log ---\n$(cat "$TMP/b.log")"

echo "=== [6/10] restart-recovery (FINDING-1): SIGTERM B, write a record into b.db offline, restart B, verify it reaches a.db within 10s ==="
# Before the SESSION-POLICY REDESIGN, A held B's dynamic session as
# authenticated/stale after B restarted and only pruned it after kPruneMs
# (~27-29s observed) before a fresh handshake could even be attempted.
# Restart-detection (3 consecutive no-progress inbound datagrams against an
# established session) must now recover this in about one datagram round.
T0=$(date +%s.%N)
kill -TERM "$BPID"
wait_exit_5s "$BPID" "komed B"
wait "$BPID" 2>/dev/null
BPID=""

pyrun - "$TMP" <<'PY'
import sys
import kome as se
tmp = sys.argv[1]
e = se.Engine(b'\x00' * 32, path=tmp + "/b.db")
e.set(b"t", b"C-0", b"v", b"val-c-0")
e.close()
PY

"$BIN" "$TMP/b.conf" >>"$TMP/b.log" 2>&1 &
BPID=$!

RECOVERED=0
for i in $(seq 1 100); do
    sleep 0.1
    kill -0 "$APID" >/dev/null 2>&1 || fail "komed A died during restart-recovery:\n$(cat "$TMP/a.log")"
    kill -0 "$BPID" >/dev/null 2>&1 || fail "komed B died during restart-recovery:\n$(cat "$TMP/b.log")"
    OUT=$(pyrun - "$TMP" <<'PY'
import sys
import kome as se
tmp = sys.argv[1]
e = se.Engine(b'\x00' * 32, path=tmp + "/a.db")
present = e.exists(b"t", b"C-0")
e.close()
print("YES" if present else "NO")
PY
)
    if [ "$OUT" = "YES" ]; then
        RECOVERED=1
        break
    fi
done
T1=$(date +%s.%N)
ELAPSED=$(awk "BEGIN{printf \"%.2f\", $T1-$T0}")
[ "$RECOVERED" -eq 1 ] || fail "restart-recovery record did not reach a.db within 10s (elapsed ${ELAPSED}s)\n--- a.log (tail) ---\n$(tail -n 40 "$TMP/a.log")\n--- b.log (tail) ---\n$(tail -n 40 "$TMP/b.log")"
echo "    ok: record reached a.db ${ELAPSED}s after restart (was ~27-29s before the fix)"

echo "=== [7/10] restart-recovery mirror (FINDING-1 reopened by an earlier fix attempt): SIGTERM A (the pure listener, zero peer= lines), write a record into a.db offline, restart A, verify it reaches b.db within 30s ==="
# Restart-detection above (step 6) only fires on the side a restarted peer
# actively redials — B, which holds the peer= line. A never dials anyone (it
# has no peer= entries at all), so when A is the one that restarts, B's
# static session for A goes stale with nothing at all arriving to trigger
# restart-detection: an earlier fix attempt that deleted the old idle-reset
# timer outright (to stop FINDING-2's re-handshake thrash) left this direction
# with NO recovery path whatsoever — B stayed wedged on the stale
# "authenticated" session forever while still logging peer ...: ok/direct.
# Recovery here instead depends on the bounded established-session staleness
# backstop (kEstablishedStaleFactor/kEstablishedStaleFloorMs), which is
# deliberately looser than restart-detection's near-instant recovery, hence
# the longer 30s budget.
T0=$(date +%s.%N)
kill -TERM "$APID"
wait_exit_5s "$APID" "komed A"
wait "$APID" 2>/dev/null
APID=""

pyrun - "$TMP" <<'PY'
import sys
import kome as se
tmp = sys.argv[1]
e = se.Engine(b'\x00' * 32, path=tmp + "/a.db")
e.set(b"t", b"E-0", b"v", b"val-e-0")
e.close()
PY

"$BIN" "$TMP/a.conf" >>"$TMP/a.log" 2>&1 &
APID=$!

RECOVERED=0
for i in $(seq 1 300); do
    sleep 0.1
    kill -0 "$APID" >/dev/null 2>&1 || fail "komed A died during restart-recovery mirror:\n$(cat "$TMP/a.log")"
    kill -0 "$BPID" >/dev/null 2>&1 || fail "komed B died during restart-recovery mirror:\n$(cat "$TMP/b.log")"
    OUT=$(pyrun - "$TMP" <<'PY'
import sys
import kome as se
tmp = sys.argv[1]
e = se.Engine(b'\x00' * 32, path=tmp + "/b.db")
present = e.exists(b"t", b"E-0")
e.close()
print("YES" if present else "NO")
PY
)
    if [ "$OUT" = "YES" ]; then
        RECOVERED=1
        break
    fi
done
T1=$(date +%s.%N)
ELAPSED=$(awk "BEGIN{printf \"%.2f\", $T1-$T0}")
[ "$RECOVERED" -eq 1 ] || fail "restart-recovery mirror record did not reach b.db within 30s (elapsed ${ELAPSED}s)\n--- a.log (tail) ---\n$(tail -n 40 "$TMP/a.log")\n--- b.log (tail) ---\n$(tail -n 40 "$TMP/b.log")"
echo "    ok: record reached b.db ${ELAPSED}s after restarting the listener side (this direction hung forever before the established-session staleness backstop)"

echo "=== [8/10] no-rehandshake-thrash (FINDING-2/FINDING-3): fresh pair at interval_ms=2000, 'session established' logs exactly once per side over an 8s idle window ==="
pyrun - "$TMP" <<'PY'
import sys
import kome as se
tmp = sys.argv[1]
e = se.Engine(b'\x03' * 32, path=tmp + "/c.db")
e.set(b"t", b"C-x", b"v", b"val-c-x")
e.close()
e = se.Engine(b'\x04' * 32, path=tmp + "/d.db")
e.set(b"t", b"D-x", b"v", b"val-d-x")
e.close()
PY

cat > "$TMP/c.conf" <<EOF
db=$TMP/c.db
listen=$PORT_C
EOF
C_PUB=$("$BIN" "$TMP/c.conf" --identity)
rc=$?
[ "$rc" -eq 0 ] || fail "komed C --identity exited $rc"

cat > "$TMP/d.conf" <<EOF
db=$TMP/d.db
listen=$PORT_D
peer=${C_PUB}@127.0.0.1:$PORT_C
interval_ms=2000
EOF
D_PUB=$("$BIN" "$TMP/d.conf" --identity)
rc=$?
[ "$rc" -eq 0 ] || fail "komed D --identity exited $rc"

"$BIN" "$TMP/c.conf" >"$TMP/c.log" 2>&1 &
CPID=$!
sleep 0.3
"$BIN" "$TMP/d.conf" >"$TMP/d.log" 2>&1 &
DPID=$!

ESTABLISHED=0
for i in $(seq 1 20); do
    sleep 0.5
    kill -0 "$CPID" >/dev/null 2>&1 || fail "komed C died early:\n$(cat "$TMP/c.log")"
    kill -0 "$DPID" >/dev/null 2>&1 || fail "komed D died early:\n$(cat "$TMP/d.log")"
    if grep -q "session established" "$TMP/c.log" && grep -q "session established" "$TMP/d.log"; then
        ESTABLISHED=1
        break
    fi
done
[ "$ESTABLISHED" -eq 1 ] || fail "C/D pair did not establish within 10s\n--- c.log ---\n$(cat "$TMP/c.log")\n--- d.log ---\n$(cat "$TMP/d.log")"
echo "    established; observing an 8s idle window for re-handshake thrash ..."
sleep 8

C_COUNT=$(grep -c "session established" "$TMP/c.log")
D_COUNT=$(grep -c "session established" "$TMP/d.log")
echo "    session established count over the window: C=$C_COUNT D=$D_COUNT"
[ "$C_COUNT" -eq 1 ] || fail "expected exactly 1 'session established' in c.log (re-handshake thrash), got $C_COUNT\n$(cat "$TMP/c.log")"
[ "$D_COUNT" -eq 1 ] || fail "expected exactly 1 'session established' in d.log (re-handshake thrash), got $D_COUNT\n$(cat "$TMP/d.log")"
echo "    ok: no re-handshake thrash"

kill -TERM "$CPID" "$DPID" >/dev/null 2>&1
wait_exit_5s "$CPID" "komed C"
wait_exit_5s "$DPID" "komed D"
wait "$CPID" 2>/dev/null
wait "$DPID" 2>/dev/null
CPID=""
DPID=""

echo "=== [9/10] mutual peer= restart-recovery (FINDING-3 collision, looped 5x): P and Q each list the other as peer=; restart the derived-responder side repeatedly and verify each restart still converges ==="
# A one-directional restart (steps 6/7) only exercises one side ever dialing.
# When *both* sides list each other, restarting the derived-responder side
# (the one that only ever listens for its permanent role) risks the double-
# initiator collision FINDING-3 fixed the flapping half of: the restarted
# side, hearing nothing decodable from the still-authenticated survivor,
# self-promotes to initiator (sticky) — a real race against the survivor's
# own established-session staleness backstop (step 7) eventually re-dialing
# in its permanent initiator role. An earlier fix attempt got this stuck in a
# permanent double-initiator livelock ~50-60% of the time; the tie-break (a
# failed() handshake step demotes a self-promoted session immediately,
# checked in the recv loop rather than only at the next cycle boundary) is
# what is supposed to break it. Looped 5x since the collision is timing-
# dependent, not every run hits it.
pyrun - "$TMP" <<'PY'
import sys
import kome as se
tmp = sys.argv[1]
e = se.Engine(b'\x05' * 32, path=tmp + "/p.db")
e.set(b"t", b"P-0", b"v", b"val-p-0")
e.close()
e = se.Engine(b'\x06' * 32, path=tmp + "/q.db")
e.set(b"t", b"Q-0", b"v", b"val-q-0")
e.close()
PY

cat > "$TMP/p.conf" <<EOF
db=$TMP/p.db
listen=$PORT_P
EOF
P_PUB=$("$BIN" "$TMP/p.conf" --identity)
rc=$?
[ "$rc" -eq 0 ] || fail "komed P --identity exited $rc"

cat > "$TMP/q.conf" <<EOF
db=$TMP/q.db
listen=$PORT_Q
EOF
Q_PUB=$("$BIN" "$TMP/q.conf" --identity)
rc=$?
[ "$rc" -eq 0 ] || fail "komed Q --identity exited $rc"

cat > "$TMP/p.conf" <<EOF
db=$TMP/p.db
listen=$PORT_P
peer=${Q_PUB}@127.0.0.1:$PORT_Q
interval_ms=300
EOF
cat > "$TMP/q.conf" <<EOF
db=$TMP/q.db
listen=$PORT_Q
peer=${P_PUB}@127.0.0.1:$PORT_P
interval_ms=300
EOF
echo "    P=$P_PUB"
echo "    Q=$Q_PUB"

"$BIN" "$TMP/p.conf" >"$TMP/p.log" 2>&1 &
P_PID=$!
"$BIN" "$TMP/q.conf" >"$TMP/q.log" 2>&1 &
QPID=$!

CONVERGED=0
for i in $(seq 1 30); do
    sleep 1
    kill -0 "$P_PID" >/dev/null 2>&1 || fail "komed P died early:\n$(cat "$TMP/p.log")"
    kill -0 "$QPID" >/dev/null 2>&1 || fail "komed Q died early:\n$(cat "$TMP/q.log")"
    OUT=$(pyrun - "$TMP" <<'PY'
import sys
import kome as se
tmp = sys.argv[1]
want = ["P-0", "Q-0"]
digests = set()
ok = True
for name in ("p.db", "q.db"):
    e = se.Engine(b'\x00' * 32, path=tmp + "/" + name)
    present = [k for k in want if e.exists(b"t", k.encode())]
    digests.add(e.digest())
    if len(present) != len(want):
        ok = False
    e.close()
print("CONVERGED" if (ok and len(digests) == 1) else "PENDING")
PY
)
    if [ "$OUT" = "CONVERGED" ]; then
        CONVERGED=1
        echo "    P/Q converged after ${i}s"
        break
    fi
done
[ "$CONVERGED" -eq 1 ] || fail "P/Q did not converge within 30s\n--- p.log ---\n$(cat "$TMP/p.log")\n--- q.log ---\n$(cat "$TMP/q.log")"

# derive_initiator(my_pk, peer_pk) = memcmp(my_pk, peer_pk) < 0: the side
# whose pubkey compares *smaller* is the derived initiator; the other side is
# the derived responder — restart that one.
if [[ "$P_PUB" < "$Q_PUB" ]]; then
    RESP_NODE=Q
else
    RESP_NODE=P
fi
echo "    derived-responder side (to be restarted 5x): komed $RESP_NODE"

for iter in 1 2 3 4 5; do
    echo "    -- mutual-peer restart iteration $iter/5 (restarting komed $RESP_NODE) --"
    T0=$(date +%s.%N)
    if [ "$RESP_NODE" = Q ]; then
        mutual_restart_and_check QPID "$TMP/q.conf" "$TMP/q.db" "$TMP/q.log" \
            "$TMP/p.db" "$TMP/p.log" "$P_PID" "M-$iter" 45
    else
        mutual_restart_and_check P_PID "$TMP/p.conf" "$TMP/p.db" "$TMP/p.log" \
            "$TMP/q.db" "$TMP/q.log" "$QPID" "M-$iter" 45
    fi
    T1=$(date +%s.%N)
    echo "       ok: marker M-$iter reached the surviving side $(awk "BEGIN{printf \"%.2f\", $T1-$T0}")s after restart"
done
echo "    ok: mutual-peer= derived-responder restart recovered 5/5 times, no permanent double-initiator livelock"

kill -TERM "$P_PID" "$QPID" >/dev/null 2>&1
wait_exit_5s "$P_PID" "komed P"
wait_exit_5s "$QPID" "komed Q"
wait "$P_PID" 2>/dev/null
wait "$QPID" 2>/dev/null
P_PID=""
QPID=""

echo "=== [10/10] SIGTERM A+B, verify clean shutdown within 5s and final state ==="
T0=$(date +%s)
kill -TERM "$APID" "$BPID"
wait_exit_5s "$APID" "komed A"
wait_exit_5s "$BPID" "komed B"
T1=$(date +%s)
echo "    both exited within $((T1 - T0))s of SIGTERM"
wait "$APID" 2>/dev/null; ARC=$?
wait "$BPID" 2>/dev/null; BRC=$?
[ "$ARC" -eq 0 ] || fail "komed A exit code $ARC after SIGTERM, expected 0"
[ "$BRC" -eq 0 ] || fail "komed B exit code $BRC after SIGTERM, expected 0"
APID=""
BPID=""

echo "=== final verification: both dbs hold all 8 records (incl. restart-recovery C-0 and E-0) + identical digests ==="
pyrun - "$TMP" <<'PY'
import sys
import kome as se
tmp = sys.argv[1]
want = ["A-0", "A-1", "A-2", "B-0", "B-1", "B-2", "C-0", "E-0"]
digests = {}
ok = True
for name in ("a.db", "b.db"):
    e = se.Engine(b'\x00' * 32, path=tmp + "/" + name)
    present = [k for k in want if e.exists(b"t", k.encode())]
    digests[name] = e.digest()
    print(name, "records:", len(present), "of", len(want),
          "missing:", [k for k in want if k not in present])
    if len(present) != len(want):
        ok = False
    e.close()
if len(set(digests.values())) != 1:
    print("DIGEST MISMATCH:", {k: v.hex() for k, v in digests.items()})
    ok = False
else:
    print("digest (both):", next(iter(digests.values())).hex())
sys.exit(0 if ok else 1)
PY
[ $? -eq 0 ] || fail "final convergence check failed"

echo "=== komed_test PASSED ==="
exit 0
