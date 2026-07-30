/* komed_main.cpp — komed: a generic, config-driven, always-on peer daemon.
 *
 * No app semantics: given an identity (a seed, only used the first time a
 * fresh database is created) and a durable database, komed periodically syncs
 * with configured peers over the *production* secure path — the same
 * connect_and_sync / SecurePeerSession / ConnectionManager machinery netnode
 * and netmesh drive (Noise XX handshake + transcript-bound identity proof +
 * capability-scoped range reconciliation). It also listens for and accepts
 * inbound connections from peers who dial *it*, even ones not in its own
 * peer= list (subject to whatever capabilities its owner has granted it via
 * cap_file=) — the "always-on member of your circles" any application can
 * deploy standalone and point at a shared database.
 *
 *   komed <config-file> [--key=value ...] [--identity | --once]
 *   komed --config <path> [--key=value ...] [--identity | --once]
 *
 * Config file: simple `key=value` lines (# comments, blank lines ignored).
 * Every key is also settable/overridable on the command line as
 * --key=value (CLI wins over the file for single-valued keys; for the
 * repeatable keys below, CLI entries are appended to the file's).
 *
 *   db=<path>                      durable engine (sync_engine_open). Required.
 *   seed_file=<path>               32 raw bytes or 64 hex chars; used only to
 *                                   derive identity when db is freshly created
 *                                   (an existing db keeps its persisted
 *                                   identity regardless). Should be 0600 —
 *                                   komed warns (does not refuse) if the file
 *                                   is group/other-readable. If omitted, a
 *                                   fresh db gets a random identity.
 *   listen=<udp-port>               local UDP port; 0 or absent = ephemeral.
 *   peer=<pubkey_hex>@<host:port>   repeatable; a static peer to sync with.
 *                                   Role (Noise XX initiator vs. responder) is
 *                                   derived per-edge from a strict identity-key
 *                                   compare (memcmp(my_pk, peer_pk, 32) < 0),
 *                                   the same rule examples/netmesh.cpp uses —
 *                                   so two komeds that each list the other as
 *                                   peer= converge without any operator-set
 *                                   role, and relay= works symmetrically too.
 *   rendezvous=<host:port>          optional; register self + look up peers.
 *   relay=<host:port>               optional; fallback path for peers komed
 *                                   cannot reach directly.
 *   interval_ms=<n>                 gossip cycle period; default 2000.
 *   cap_file=<path>                 repeatable; each file holds one encoded
 *                                   capability blob, decoded and granted into
 *                                   the engine at startup (sync_capability_decode
 *                                   + sync_engine_grant) — how an owner hands
 *                                   komed delegated, read-scoped serving.
 *
 * Modes:
 *   --identity   print this replica's identity pubkey (creating/opening the
 *                db as configured) as 64 hex chars, then exit 0.
 *   --once       run exactly one outbound sync cycle against every configured
 *                peer (direct, falling back to relay if configured), then
 *                exit — 0 if every peer converged, 1 if any failed.
 *   (default)    run forever: dial configured peers on a cadence of
 *                interval_ms (direct, falling back to a blocking relay
 *                attempt for any peer still unauthenticated at a cycle
 *                boundary if relay= is set) *and* passively accept inbound
 *                connections from any peer that dials komed's listen port,
 *                so komed can be a pure responder with zero peer= lines (as
 *                relayd/rendezvousd are pure responders). SIGINT/SIGTERM
 *                triggers a clean shutdown: sync_engine_flush + destroy.
 *
 * Never logs the seed or any record value — only identity, addresses, and
 * per-peer/per-cycle outcomes.
 */
#include "sync_engine.h"

#include <algorithm>
#include <array>
#include <cctype>
#include <cerrno>
#include <chrono>
#include <csignal>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <map>
#include <memory>
#include <string>
#include <vector>

#include <fcntl.h>
#include <signal.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

#include "engine.hpp"
#include "transport/connection.h"
#include "transport/rendezvous.h"
#include "transport/udp.h"

using namespace ke;

namespace {

/* ---------------------------------------------------------------- utility */

uint64_t wall_ms() {
    using namespace std::chrono;
    return (uint64_t)duration_cast<milliseconds>(
               steady_clock::now().time_since_epoch())
        .count();
}

/* Human-readable wall-clock timestamp for log lines. */
std::string ts() {
    time_t t = time(nullptr);
    struct tm tmv;
    localtime_r(&t, &tmv);
    char buf[32];
    strftime(buf, sizeof buf, "%Y-%m-%d %H:%M:%S", &tmv);
    return std::string(buf);
}

std::string hexstr(const uint8_t *p, size_t n) {
    static const char *d = "0123456789abcdef";
    std::string out;
    out.reserve(n * 2);
    for (size_t i = 0; i < n; i++) {
        out.push_back(d[p[i] >> 4]);
        out.push_back(d[p[i] & 0xf]);
    }
    return out;
}

std::string trim(const std::string &s) {
    size_t a = s.find_first_not_of(" \t\r\n");
    if (a == std::string::npos) return "";
    size_t b = s.find_last_not_of(" \t\r\n");
    return s.substr(a, b - a + 1);
}

bool parse_hex32(const std::string &s, uint8_t out[32]) {
    if (s.size() != 64) return false;
    for (int i = 0; i < 32; i++) {
        unsigned v;
        if (sscanf(s.c_str() + i * 2, "%2x", &v) != 1) return false;
        /* sscanf %2x accepts a leading '+'/whitespace inside the 2-char
         * window in some libcs; reject anything not pure hex explicitly. */
        char c0 = s[i * 2], c1 = s[i * 2 + 1];
        if (!isxdigit((unsigned char)c0) || !isxdigit((unsigned char)c1))
            return false;
        out[i] = (uint8_t)v;
    }
    return true;
}

/* Rightmost ':' splits host:port (host is an IPv4 literal — see udp.h). */
bool parse_host_port(const std::string &s, std::string &host, uint16_t &port) {
    auto c = s.rfind(':');
    if (c == std::string::npos || c == 0 || c + 1 >= s.size()) return false;
    host = s.substr(0, c);
    std::string ps = s.substr(c + 1);
    for (char ch : ps)
        if (!isdigit((unsigned char)ch)) return false;
    long v = strtol(ps.c_str(), nullptr, 10);
    if (v <= 0 || v > 65535) return false;
    port = (uint16_t)v;
    return true;
}

bool parse_port_field(const std::string &s, uint16_t &out) {
    if (s.empty()) return false;
    for (char ch : s)
        if (!isdigit((unsigned char)ch)) return false;
    long v = strtol(s.c_str(), nullptr, 10);
    if (v < 0 || v > 65535) return false;
    out = (uint16_t)v;
    return true;
}

bool parse_uint_field(const std::string &s, long &out) {
    if (s.empty()) return false;
    for (char ch : s)
        if (!isdigit((unsigned char)ch)) return false;
    errno = 0;
    char *end = nullptr;
    long v = strtol(s.c_str(), &end, 10);
    /* strtol clamps to LONG_MAX/LONG_MIN and sets ERANGE on overflow rather
     * than failing outright — an all-digit value like
     * "999999999999999999999" silently becomes LONG_MAX. Left unchecked that
     * reaches arithmetic on cfg.interval_ms (e.g. `* 5` for the rendezvous
     * refresh period) and triggers signed-overflow UB, confirmed by UBSan,
     * while the daemon runs forever logging nothing. Reject it here instead. */
    if (errno == ERANGE || end == s.c_str() || *end != '\0') return false;
    out = v;
    return true;
}

/* ------------------------------------------------------------ config type */

struct PeerCfg {
    std::array<uint8_t, 32> pk{};
    std::string             host;
    uint16_t                port = 0;
    std::string             raw; /* original "peer=" value, for logging */
};

struct Config {
    std::string db;
    std::string seed_file;
    uint16_t    listen = 0;
    bool        have_listen = false;
    std::vector<PeerCfg> peers;
    std::string rendezvous_host;
    uint16_t    rendezvous_port = 0;
    bool        have_rendezvous = false;
    std::string relay_host;
    uint16_t    relay_port = 0;
    bool        have_relay = false;
    long        interval_ms = 2000;
    std::vector<std::string> cap_files;
};

/* Apply one key=value pair to cfg. Returns false + fills *err on any
 * malformed value or unknown key. */
bool apply_kv(Config &cfg, const std::string &key, const std::string &val,
             std::string *err) {
    if (key == "db") {
        cfg.db = val;
    } else if (key == "seed_file") {
        cfg.seed_file = val;
    } else if (key == "listen") {
        uint16_t p;
        if (!parse_port_field(val, p)) { *err = "bad listen port: " + val; return false; }
        cfg.listen = p;
        cfg.have_listen = true;
    } else if (key == "peer") {
        auto at = val.find('@');
        if (at == std::string::npos) { *err = "bad peer (missing '@'): " + val; return false; }
        PeerCfg pc;
        std::string keyhex = val.substr(0, at);
        if (!parse_hex32(keyhex, pc.pk.data())) {
            *err = "bad peer pubkey hex: " + keyhex;
            return false;
        }
        if (!parse_host_port(val.substr(at + 1), pc.host, pc.port)) {
            *err = "bad peer host:port: " + val.substr(at + 1);
            return false;
        }
        pc.raw = val;
        cfg.peers.push_back(std::move(pc));
    } else if (key == "rendezvous") {
        if (!parse_host_port(val, cfg.rendezvous_host, cfg.rendezvous_port)) {
            *err = "bad rendezvous host:port: " + val;
            return false;
        }
        cfg.have_rendezvous = true;
    } else if (key == "relay") {
        if (!parse_host_port(val, cfg.relay_host, cfg.relay_port)) {
            *err = "bad relay host:port: " + val;
            return false;
        }
        cfg.have_relay = true;
    } else if (key == "interval_ms") {
        long v;
        if (!parse_uint_field(val, v)) { *err = "bad interval_ms: " + val; return false; }
        /* Sane upper bound: interval_ms feeds `* 5` (rendezvous refresh, see
         * kResetMs-style arithmetic below) and various (uint32_t) casts, so
         * even an in-range-for-long-but-absurd value like a value in years
         * is worth rejecting outright rather than trusting downstream
         * arithmetic to stay safe. 3600000ms = 1 hour is already a very slow
         * gossip cadence for an "always-on" daemon. */
        if (v > 3600000) { *err = "bad interval_ms (must be 0..3600000): " + val; return false; }
        cfg.interval_ms = v;
    } else if (key == "cap_file") {
        cfg.cap_files.push_back(val);
    } else {
        *err = "unknown config key: " + key;
        return false;
    }
    return true;
}

/* Parse "key=value" (already trimmed, non-comment, non-blank). */
bool split_kv(const std::string &line, std::string &key, std::string &val) {
    auto eq = line.find('=');
    if (eq == std::string::npos) return false;
    key = trim(line.substr(0, eq));
    val = trim(line.substr(eq + 1));
    return !key.empty();
}

bool load_config_file(const std::string &path, Config &cfg, std::string *err) {
    FILE *f = fopen(path.c_str(), "r");
    if (!f) { *err = "cannot read config file: " + path; return false; }
    /* Same S_ISREG check as read_file_bytes (FINDING-4): fopen("r") happily
     * opens a directory on most libcs, and the first fgets() on it then just
     * returns NULL (EOF-looking, not an error) — so a directory or other
     * non-regular path (fifo, device, ...) passed as the config silently
     * behaved as an *empty* config instead of failing. Reject it up front
     * with a clear message instead. */
    int fd = fileno(f);
    struct stat st;
    if (fd < 0 || fstat(fd, &st) != 0 || !S_ISREG(st.st_mode)) {
        fclose(f);
        *err = "not a regular file: " + path;
        return false;
    }
    char linebuf[4096];
    int lineno = 0;
    bool ok = true;
    while (fgets(linebuf, sizeof linebuf, f)) {
        lineno++;
        std::string line = trim(linebuf);
        if (line.empty() || line[0] == '#') continue;
        std::string key, val;
        if (!split_kv(line, key, val)) {
            *err = path + ":" + std::to_string(lineno) + ": malformed line (expected key=value): " + line;
            ok = false;
            break;
        }
        if (!apply_kv(cfg, key, val, err)) {
            *err = path + ":" + std::to_string(lineno) + ": " + *err;
            ok = false;
            break;
        }
    }
    fclose(f);
    return ok;
}

/* Read a whole file into bytes. Returns false on open failure, on a path
 * that isn't a regular file (e.g. a directory — ftell() on those returns
 * LONG_MAX on some platforms, which would otherwise drive an unbounded
 * resize()), or on a file bigger than kMaxReadFileBytes (every caller reads
 * small, bounded config artifacts: a 32/64-byte seed or a ~143-byte
 * capability blob). */
bool read_file_bytes(const std::string &path, std::vector<uint8_t> &out) {
    constexpr long kMaxReadFileBytes = 1 << 20; /* 1 MiB, generous headroom */
    FILE *f = fopen(path.c_str(), "rb");
    if (!f) return false;
    int fd = fileno(f);
    struct stat st;
    if (fd < 0 || fstat(fd, &st) != 0 || !S_ISREG(st.st_mode)) {
        fclose(f);
        return false;
    }
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    if (n < 0 || n > kMaxReadFileBytes) { fclose(f); return false; }
    fseek(f, 0, SEEK_SET);
    out.resize((size_t)n);
    size_t rd = n ? fread(out.data(), 1, (size_t)n, f) : 0;
    fclose(f);
    return rd == (size_t)n;
}

/* seed_file: 32 raw bytes, or 64 hex chars (optionally trailing newline). */
bool load_seed_file(const std::string &path, uint8_t seed[32], std::string *err) {
    std::vector<uint8_t> raw;
    if (!read_file_bytes(path, raw)) { *err = "cannot read seed_file: " + path; return false; }
    /* Warn (do not refuse) if group/other-readable. */
    struct stat st;
    if (stat(path.c_str(), &st) == 0 && (st.st_mode & (S_IRWXG | S_IRWXO))) {
        fprintf(stderr, "komed: warning: seed_file %s is group/other-accessible "
                        "(chmod 0600 recommended)\n", path.c_str());
    }
    if (raw.size() == 32) {
        memcpy(seed, raw.data(), 32);
        return true;
    }
    std::string trimmed = trim(std::string((char *)raw.data(), raw.size()));
    if (trimmed.size() == 64 && parse_hex32(trimmed, seed)) return true;
    *err = "seed_file must hold 32 raw bytes or 64 hex chars: " + path;
    return false;
}

/* -------------------------------------------------------- single-writer lock */

std::string g_lock_path;
bool        g_own_lock = false;

bool lock_is_stale(const std::string &path) {
    FILE *f = fopen(path.c_str(), "r");
    if (!f) return true;
    long pid = 0;
    if (fscanf(f, "%ld", &pid) != 1) pid = 0;
    fclose(f);
    if (pid <= 0) return true;
    if (kill((pid_t)pid, 0) == 0) return false;      /* alive */
    return errno == ESRCH;                            /* dead (or lost race) */
}

/* db has no storage-level lock (verified: Storage::open takes no flock/
 * O_EXCL/fcntl) — so komed enforces single-writer itself via <db>.lock:
 * O_CREAT|O_EXCL containing our pid, removed on clean shutdown, stolen if the
 * owning pid is dead. */
bool acquire_db_lock(const std::string &db_path, std::string *err) {
    g_lock_path = db_path + ".lock";
    for (int attempt = 0; attempt < 2; attempt++) {
        int fd = open(g_lock_path.c_str(), O_CREAT | O_EXCL | O_WRONLY, 0600);
        if (fd >= 0) {
            char buf[32];
            int n = snprintf(buf, sizeof buf, "%ld\n", (long)getpid());
            ssize_t wn = write(fd, buf, (size_t)n);
            (void)wn; /* best-effort; a failed pid write still leaves the
                       * O_EXCL lock in place, which is what matters. */
            close(fd);
            g_own_lock = true;
            return true;
        }
        if (errno != EEXIST) {
            *err = "cannot create lock file " + g_lock_path + ": " + strerror(errno);
            return false;
        }
        if (lock_is_stale(g_lock_path)) {
            unlink(g_lock_path.c_str());
            continue; /* retry the O_EXCL create */
        }
        *err = "database is locked by another running komed (" + g_lock_path + ")";
        return false;
    }
    *err = "could not acquire lock: " + g_lock_path;
    return false;
}

void release_db_lock() {
    if (g_own_lock && !g_lock_path.empty()) {
        unlink(g_lock_path.c_str());
        g_own_lock = false;
    }
}

/* ------------------------------------------------------------- shutdown */

volatile sig_atomic_t g_stop = 0;
void on_signal(int) { g_stop = 1; }

void install_signal_handlers() {
    struct sigaction sa;
    memset(&sa, 0, sizeof sa);
    sa.sa_handler = on_signal;
    sigemptyset(&sa.sa_mask);
    sa.sa_flags = 0;
    sigaction(SIGINT, &sa, nullptr);
    sigaction(SIGTERM, &sa, nullptr);
}

/* Clean shutdown: durable flush, destroy, release lock. */
void shutdown_engine(sync_engine *e) {
    if (e) {
        sync_engine_flush(e);
        sync_engine_destroy(e);
    }
    release_db_lock();
}

/* ------------------------------------------------------------ daemon loop */

struct LiveSession {
    Endpoint                           ep;
    bool                                is_static = false;
    PeerCfg                            *peer = nullptr; /* set iff is_static */
    std::unique_ptr<SecurePeerSession>  sps;
    /* Current *effective* role of `sps` — only meaningful while is_static (a
     * dynamic session is always a responder: initiator=false, fixed for its
     * whole life). Tracked here rather than queried from SecurePeerSession
     * because it can change post-construction: see kPassiveFallbackMs below.
     * May diverge from derived_initiator while self-promoted. */
    bool                                is_initiator = false;
    /* The *permanent* role derived once at creation from the identity-key
     * compare (FINDING-3) and never changed thereafter. is_initiator can be
     * temporarily forced away from this by self-promotion below; a
     * self-promoted session (is_initiator != derived_initiator) only ever
     * demotes back via restart-detection or failed() — see
     * reset_live_session(). */
    bool                                derived_initiator = false;
    /* Consecutive inbound datagrams, since the session was last (re)started,
     * that produced no progress while the session was already
     * authenticated/established (SESSION-POLICY REDESIGN point 1 /
     * FINDING-1): last_progress() did not advance and handshake_done() did
     * not change. A peer that restarts and redials sends exactly such
     * datagrams against our still-"authenticated" stale session (its fresh
     * handshake bytes don't decrypt against our live post-handshake channel,
     * so ReliableLink::on_datagram/chan_ report no progress). Reaching 3 is
     * treated as restart detection: reset() immediately rather than waiting
     * out kPruneMs. Zeroed on any progress. Meaningless (left at 0) for a
     * session that has never authenticated. */
    int                                 no_progress_count = 0;
    /* Set once and never cleared (for this LiveSession's lifetime — a fresh
     * config/restart of *this* side gets a fresh LiveSession and starts over)
     * the first time a self-promoted session actually collides with the real
     * derived initiator: a failed() handshake step while is_initiator !=
     * derived_initiator (see the two failed()-triggered reset_live_session()
     * call sites) is direct, positive proof that the peer we listed *does*
     * dial as initiator — self-promotion's whole premise (the peer never
     * dials) is false for this edge. Once witnessed, re-arming self-promotion
     * on the usual silence timer would only manufacture the same collision
     * again: the peer's own initiator-retry loop (which runs unconditionally,
     * forever, every max(3*interval_ms, 10000)ms, for as long as it stays
     * unauthenticated) is what completes the handshake from here — it needs
     * this side to just stay a responder and let it land. Without this,
     * self-promotion re-arms every kPassiveFallbackMs (6s) — *faster* than
     * the peer's own retry cadence (>=10s) — so the self-promoted side always
     * re-collides before the peer's next natural retry, a resonant
     * double-initiator livelock with no bound (FINDING-3's mutual-peer=
     * collision, reopened by the first cut at this tie-break: demoting fast
     * is necessary but not sufficient — it also has to stop re-promoting). */
    bool                                self_promotion_locked = false;
};

const uint64_t kPruneMs = 30000;  /* silence before dropping a dynamic link */
const size_t   kMaxDynamic = 64;  /* bound on unsolicited inbound sessions */
/* Consecutive no-progress inbound datagrams against an established session
 * that indicate the peer has restarted. See LiveSession::no_progress_count. */
const int kRestartNoProgressCount = 3;
/* Bounded time-based backstop for an AUTHENTICATED static session that has
 * gone silent (REJECTED-FIX FOLLOW-UP: restart-detection above only fires on
 * an *inbound* unauthenticated datagram, which only a peer that actively
 * dials produces; a restarted peer that is a pure responder — or the
 * derived-responder side of a mutual peer= edge, which does not dial either —
 * never sends us anything at all, so restart-detection alone can wedge this
 * side on a stale "authenticated" session forever while it keeps reporting
 * ok/direct). If an authenticated session has made no progress at all for
 * this long, treat it as probably talking to a restarted (or otherwise dead)
 * peer and re-handshake — but role-preserving (see reset_live_session's
 * demote_to_derived=false), NOT demoted to the derived role: a self-promoted
 * session got that way because the real peer never dials, and that has not
 * changed just because our side went stale, so demoting here would trade a
 * silent stall for a silent stall in the other role. Large enough relative to
 * interval_ms that a healthy, merely-idle link (whose initiator re-kicks
 * every interval_ms and gets an inbound reply each time, keeping
 * last_progress() fresh) never comes close — verified against the
 * no-rehandshake-thrash window (FINDING-2). */
const long     kEstablishedStaleFactor  = 6;     /* multiple of interval_ms */
const uint64_t kEstablishedStaleFloorMs = 8000;  /* floor for small intervals */
/* A static peer derived (FINDING-3) to be the *responder* side of its edge
 * that has heard nothing at all from that peer for this long evidently isn't
 * being dialed by it — e.g. it's the "pure responder, zero peer= lines" side
 * of a one-directional config, which never initiates for any edge — so
 * self-promote to initiator and dial. Harmless in the true mutual-listing
 * case too: there, the real initiator's first message normally arrives well
 * within this window, so promotion never fires.
 *
 * Promotion is sticky (SESSION-POLICY REDESIGN point 3 / FINDING-3): it is
 * never reversed by an elapsed grace period. It is only ever demoted back to
 * the derived role as a side effect of restart-detection or a failed()
 * session being reset — see reset_live_session(). This is what stops the
 * promote/demote flapping the age-based (promoted_at) demotion used to cause:
 * once a link is doing real work, nothing here second-guesses its role again
 * on a timer. */
const uint64_t kPassiveFallbackMs = 6000;

std::string addr_key(const Endpoint &ep) { return ep.ip + ":" + std::to_string(ep.port); }

/* Re-handshake a live session from scratch, sending whatever it emits.
 * This is the *only* place a session's role is ever changed after creation:
 * a dynamic session always resets as a responder (its role never varies); a
 * static session's target role depends on `demote_to_derived`:
 *
 *   true  — reset to the permanent derived_initiator role, demoting the
 *           session if it was self-promoted. Used by the two events that are
 *           positive evidence the *other* side just dialed us (or tried to)
 *           as initiator, so our own promotion (if any) lost the race and
 *           must yield: restart-detection (the peer's fresh redial arrived)
 *           and a failed() handshake (a structurally-mismatched inbound
 *           message is exactly what a colliding double-initiator produces —
 *           the tie-break for FINDING-3's mutual-peer= collision).
 *   false — preserve the session's current role. Used by the established-
 *           session staleness backstop above (kEstablishedStaleMs): we have
 *           heard *nothing at all*, so there is no evidence about the peer's
 *           behavior one way or the other, and demoting a self-promoted
 *           session here (when the real reason it was promoted — the peer
 *           never dials — has not changed) would just trade a stale
 *           "authenticated initiator" for a stale "waiting responder".
 *
 * When the target role matches the session's current role,
 * SecurePeerSession::reset() is enough (it keeps its fixed initiator_ but
 * rebuilds the Noise channel + reliability state); when the role must
 * change, a fresh SecurePeerSession is constructed instead, since role is
 * fixed for the lifetime of a SecurePeerSession object. */
void reset_live_session(sync_engine *e, UdpSocket &sock, const Config &cfg,
                        LiveSession &ls, uint64_t now, bool demote_to_derived) {
    bool target_initiator = ls.is_static
        ? (demote_to_derived ? ls.derived_initiator : ls.is_initiator)
        : false;
    std::vector<std::string> out;
    if (ls.is_initiator != target_initiator) {
        ls.sps = std::make_unique<SecurePeerSession>(e, target_initiator, (uint32_t)cfg.interval_ms);
        ls.is_initiator = target_initiator;
        ls.sps->start(now, out);
    } else {
        ls.sps->reset(now, out);
    }
    ls.no_progress_count = 0;
    for (auto &dg : out) sock.send_to(ls.ep, dg);
}

/* Exactly one side of a static peer edge must be the Noise XX initiator, or
 * neither side ever completes a handshake (both dial and both wait, or both
 * wait and neither dials). komed has no --role config key, so — same as
 * netmesh's memcmp(my_pk, peer_pk, 32) < 0 — the role is derived from a
 * strict identity-key compare: deterministic on both ends without any
 * operator coordination, and guaranteed to pick exactly one initiator per
 * edge (a < b XOR b < a for distinct keys), including when a peer= is
 * listed on both sides or reached only through relay=. */
bool derive_initiator(const uint8_t my_pk[32], const uint8_t peer_pk[32]) {
    return memcmp(my_pk, peer_pk, 32) < 0;
}

/* One blocking relay-fallback attempt for a single static peer, used both by
 * --once and as the daemon loop's periodic fallback for peers unauthenticated
 * over direct. */
bool try_relay(sync_engine *e, UdpSocket &sock, const Config &cfg,
               const PeerCfg &peer, const uint8_t my_pk[32], int timeout_ms) {
    if (!cfg.have_relay) return false;
    RelayTransport rt;
    rt.sock = &sock;
    rt.relay = Endpoint{cfg.relay_host, cfg.relay_port};
    memcpy(rt.peer_pk.data(), peer.pk.data(), 32);
    memcpy(rt.my_pk.data(), my_pk, 32);
    return connect_and_sync(e, rt, derive_initiator(my_pk, peer.pk.data()), timeout_ms);
}

/* --once: sequential, blocking, one cycle across all configured peers. */
int run_once(sync_engine *e, UdpSocket &sock, Config &cfg, const uint8_t my_pk[32]) {
    fprintf(stdout, "%s cycle 1: peers=%zu (once)\n", ts().c_str(), cfg.peers.size());
    Endpoint rdv_ep;
    if (cfg.have_rendezvous) {
        rdv_ep = Endpoint{cfg.rendezvous_host, cfg.rendezvous_port};
        rendezvous_register(sock, rdv_ep, e->identity, 2000);
    }
    bool all_ok = true;
    for (auto &peer : cfg.peers) {
        Endpoint direct_ep{peer.host, peer.port};
        if (cfg.have_rendezvous) {
            Endpoint looked;
            if (rendezvous_lookup(sock, rdv_ep, peer.pk.data(), looked, 2000))
                direct_ep = looked;
        }
        DirectTransport dt;
        dt.sock = &sock;
        dt.peer = direct_ep;
        /* Role must agree with what the daemon on the other end derives for
         * this same edge (memcmp(my_pk, peer_pk, 32) < 0 — see
         * derive_initiator), same as run_daemon and try_relay above:
         * hardcoding initiator=true unconditionally made --once collide with
         * a live, healthy daemon whose derived role for this edge is also
         * initiator (both sides dial, both reject the other, deterministic
         * "failed" for ~half of all identity-key pairs against a perfectly
         * reachable peer).
         *
         * Try the derived role first — against a real daemon peer (the
         * common case this command is used to probe/monitor) that's the role
         * it expects and converges immediately. But --once must also work
         * against a "pure responder, zero peer= lines" target that never
         * dials anyone (so if our derived role happens to be responder here,
         * waiting would just time out): if the first attempt fails, retry
         * with the opposite role for the rest of the budget rather than
         * pinning one role for the whole window. */
        bool derived_initiator = derive_initiator(my_pk, peer.pk.data());
        bool ok = connect_and_sync(e, dt, derived_initiator, 4000);
        if (!ok) ok = connect_and_sync(e, dt, !derived_initiator, 4000);
        const char *how = "failed";
        if (ok) {
            how = "ok/direct";
        } else if (try_relay(e, sock, cfg, peer, my_pk, 8000)) {
            ok = true;
            how = "ok/relay";
        }
        fprintf(stdout, "%s   peer %s: %s\n", ts().c_str(), hexstr(peer.pk.data(), 32).c_str(), how);
        all_ok = all_ok && ok;
    }
    return all_ok ? 0 : 1;
}

/* default mode: forever, dial configured peers on a cadence and passively
 * accept inbound connections from anyone else who reaches this socket. */
int run_daemon(sync_engine *e, UdpSocket &sock, Config &cfg, const uint8_t my_pk[32]) {
    std::map<std::string, LiveSession> live;
    for (auto &peer : cfg.peers) {
        LiveSession ls;
        ls.ep = Endpoint{peer.host, peer.port};
        ls.is_static = true;
        ls.peer = &peer;
        ls.derived_initiator = derive_initiator(my_pk, peer.pk.data());
        ls.is_initiator = ls.derived_initiator;
        ls.sps = std::make_unique<SecurePeerSession>(e, ls.is_initiator, (uint32_t)cfg.interval_ms);
        std::vector<std::string> out;
        uint64_t now0 = wall_ms();
        ls.sps->start(now0, out);
        for (auto &dg : out) sock.send_to(ls.ep, dg);
        live.emplace(addr_key(ls.ep), std::move(ls));
    }

    std::map<PeerCfg *, std::string> last_result;
    for (auto &peer : cfg.peers) last_result[&peer] = "pending";

    Endpoint rdv_ep;
    if (cfg.have_rendezvous) {
        rdv_ep = Endpoint{cfg.rendezvous_host, cfg.rendezvous_port};
        rendezvous_register(sock, rdv_ep, e->identity, 2000);
    }

    uint64_t cycle_no = 0;
    uint64_t last_cycle = wall_ms();
    uint64_t last_rdv = last_cycle;

    while (!g_stop) {
        uint64_t now = wall_ms();

        for (auto &kv : live) {
            LiveSession &ls = kv.second;
            /* EVENT-DRIVEN session policy (SESSION-POLICY REDESIGN), plus a
             * bounded time-based backstop for established sessions (REJECTED-
             * FIX FOLLOW-UP — see kEstablishedStaleMs above for why deleting
             * the old kResetMs idle reset outright, as FINDING-2's first fix
             * attempt did, reopened FINDING-1 for any restarted peer that
             * doesn't dial). An established, idle-but-healthy link is left
             * alone here: gossip cadence is poll()'s job below (it fires a
             * fresh cycle every gossip_interval_ms on its own, which keeps
             * last_progress() fresh). The timer-driven triggers are:
             *
             *   (c) an AUTHENTICATED session with no progress at all for the
             *       established-staleness threshold — probably talking to a
             *       dead/restarted peer that itself never dials in; re-
             *       handshake role-preserving (not demoted — see
             *       reset_live_session);
             *   (b) an initiator session whose handshake is still incomplete
             *       with no progress for max(3*interval_ms, 10000) ms —
             *       retry the stalled handshake attempt; and
             *   the sticky self-promotion of a derived-responder static
             *       session that has heard nothing at all since creation for
             *       kPassiveFallbackMs — see the const above.
             *
             * Trigger (a) — a failed() session — is checked immediately in
             * the recv loop below (as soon as a datagram makes it fail) and,
             * as a backstop, once more per cycle boundary alongside
             * last_result. Restart-detection (the fix for FINDING-1) also
             * lives in the recv loop, since it is driven by inbound
             * datagrams, not time. (a) and restart-detection both demote a
             * self-promoted session back to its derived role — they are
             * positive evidence the real peer just dialed (or tried to) as
             * initiator, so our own promotion lost the race (FINDING-3's
             * mutual-peer= collision tie-break); (c) does not, since silence
             * alone is not evidence the peer's dialing behavior changed. */
            if (ls.is_static && ls.sps->authenticated()) {
                uint64_t stale_threshold = (uint64_t)std::max<long>(
                    cfg.interval_ms * kEstablishedStaleFactor, (long)kEstablishedStaleFloorMs);
                if (now - ls.sps->last_progress() > stale_threshold)
                    reset_live_session(e, sock, cfg, ls, now, /*demote_to_derived=*/false);
            } else if (ls.is_static && ls.is_initiator) {
                if (!ls.sps->handshake_done()) {
                    uint64_t threshold =
                        (uint64_t)std::max<long>(cfg.interval_ms * 3, 10000);
                    if (now - ls.sps->last_progress() > threshold)
                        reset_live_session(e, sock, cfg, ls, now, /*demote_to_derived=*/true);
                }
            } else if (ls.is_static && !ls.self_promotion_locked &&
                       now - ls.sps->last_progress() > kPassiveFallbackMs) {
                /* Derived responder, never converged, silent since
                 * creation (or since the last reset) past the grace
                 * period: self-promote to initiator so a one-directional
                 * config (the peer we listed doesn't list us back, so it
                 * never dials) still converges. Sticky: nothing here ever
                 * un-does this on a timer again (FINDING-3) — only
                 * restart-detection or a failed() reset demotes it. Gated on
                 * !self_promotion_locked: once a self-promoted attempt has
                 * actually collided with the real derived initiator, that is
                 * proof this peer *does* dial, so re-arming this timer would
                 * only manufacture the same collision again — see
                 * self_promotion_locked's definition on LiveSession. */
                ls.sps = std::make_unique<SecurePeerSession>(e, /*initiator=*/true,
                                                              (uint32_t)cfg.interval_ms);
                ls.is_initiator = true;
                ls.no_progress_count = 0;
                std::vector<std::string> out;
                ls.sps->start(now, out);
                for (auto &dg : out) sock.send_to(ls.ep, dg);
            }
            std::vector<std::string> out;
            ls.sps->poll(now, out);
            for (auto &dg : out) sock.send_to(ls.ep, dg);
        }

        for (auto it = live.begin(); it != live.end();) {
            if (!it->second.is_static && now - it->second.sps->last_progress() > kPruneMs)
                it = live.erase(it);
            else
                ++it;
        }

        std::string dg;
        Endpoint from;
        while (sock.recv(dg, from, 30)) {
            std::string key = addr_key(from);
            auto it = live.find(key);
            if (it == live.end()) {
                size_t dyn_count = 0;
                for (auto &kv : live) if (!kv.second.is_static) dyn_count++;
                if (dyn_count >= kMaxDynamic) {
                    /* Full: evict the stalest *unauthenticated* dynamic
                     * session (oldest last_progress) to make room, rather
                     * than unconditionally dropping the new arrival — that
                     * would let a burst of junk datagrams from distinct
                     * source addresses permanently occupy every dynamic slot
                     * and deny service to any real peer dialing in
                     * afterwards. Never evict an authenticated session (a
                     * real, converged peer) to make room for a fresh,
                     * unproven one. */
                    auto victim = live.end();
                    for (auto lit = live.begin(); lit != live.end(); ++lit) {
                        if (lit->second.is_static || lit->second.sps->authenticated())
                            continue;
                        if (victim == live.end() ||
                            lit->second.sps->last_progress() < victim->second.sps->last_progress())
                            victim = lit;
                    }
                    if (victim == live.end()) continue; /* all slots are real, authenticated peers */
                    live.erase(victim);
                }
                LiveSession ls;
                ls.ep = from;
                ls.is_static = false;
                ls.sps = std::make_unique<SecurePeerSession>(e, /*initiator=*/false,
                                                              (uint32_t)cfg.interval_ms);
                std::vector<std::string> sout;
                ls.sps->start(now, sout);
                for (auto &d : sout) sock.send_to(ls.ep, d);
                it = live.emplace(key, std::move(ls)).first;
            }

            LiveSession &ls = it->second;
            bool was_authenticated = ls.sps->authenticated();
            uint64_t progress_before = ls.sps->last_progress();
            bool handshake_before = ls.sps->handshake_done();

            std::vector<std::string> out;
            ls.sps->on_datagram(dg, now, out);
            for (auto &d : out) sock.send_to(ls.ep, d);

            if (!was_authenticated && ls.sps->authenticated()) {
                /* Countable marker for "this session finished a Noise
                 * handshake + identity proof" — the no-rehandshake-thrash
                 * test greps for it: on a converged, idle pair this must
                 * appear exactly once per side (FINDING-2 verification). */
                fprintf(stdout, "%s session established: %s\n", ts().c_str(),
                        addr_key(ls.ep).c_str());
                fflush(stdout);
            }

            /* RESTART DETECTION (SESSION-POLICY REDESIGN point 1 /
             * FINDING-1): only meaningful once a session has authenticated
             * at least once — an unauthenticated session's normal handshake
             * back-and-forth naturally includes datagrams that don't (yet)
             * move last_progress()/handshake_done() and must not be treated
             * as a restart.
             *
             * A "no progress" inbound datagram alone is not, by itself, safe
             * to treat as restart evidence: transport/reliable.cpp's
             * stop-and-wait retransmits on a kRtoMs=50ms timer, and a busy
             * event loop can easily let that timer fire before it has read
             * the peer's ack — a completely benign duplicate ACK/DATA retransmit
             * from a peer that never restarted at all, and it returns the
             * exact same "no progress" signal (verified empirically: it
             * reproduces on every run of the local two-node test at
             * interval_ms=300, immediately after the handshake settles,
             * long before any real restart). What actually distinguishes a
             * restarted peer's traffic is *authentication*, not progress: a
             * restarted peer's SecurePeerSession builds a brand-new
             * ReliableLink (transport/reliable.h), which sends its very
             * first frame — the fresh Noise handshake — unauthenticated
             * (frame()'s leading auth byte is 0; ReliableLink::send()
             * captures `keyed_`, false before any handshake has ever
             * completed on that new link). A peer that is still the same,
             * long-running, already-authenticated session we spoke to
             * before, by contrast, has nothing left to legitimately
             * (re)transmit that isn't already MAC'd — by the time *we* have
             * ever reached `authenticated()`, that peer's own reliable
             * stream has necessarily delivered its (always-later,
             * authenticated) identity proof in order, so every earlier,
             * pre-mac frame of theirs is already acked and gone. So: only
             * count a no-progress datagram toward restart detection when its
             * raw wire leading byte is 0 (unauthenticated) — the actual
             * restart signature — not merely "no progress", which a benign
             * authenticated retransmit also produces. */
            if (was_authenticated) {
                bool progressed = ls.sps->last_progress() != progress_before ||
                                  ls.sps->handshake_done() != handshake_before;
                bool unauthenticated_frame = !dg.empty() && (unsigned char)dg[0] == 0;
                if (progressed || !unauthenticated_frame) {
                    ls.no_progress_count = 0;
                } else if (++ls.no_progress_count >= kRestartNoProgressCount) {
                    reset_live_session(e, sock, cfg, ls, now, /*demote_to_derived=*/true);
                }
            }

            /* Trigger (a), checked immediately rather than only at the next
             * cycle boundary (FINDING-3 collision tie-break): a structurally
             * mismatched inbound message — which is exactly what a colliding
             * double-initiator produces, since each side's Noise channel is
             * waiting for the *other* role's next message — fails the
             * handshake step synchronously inside on_datagram() above. Acting
             * on it here, in the same recv iteration, rather than waiting up
             * to a full cycle boundary away, is what lets a self-promoted
             * initiator that just collided with the real derived initiator
             * yield (demote) fast enough for the real initiator's very next
             * retry to land on a peer that is actually listening. The cycle-
             * boundary check below still catches any failed() session this
             * misses (e.g. one that failed via something other than an
             * inbound datagram). */
            if (ls.is_static && ls.sps->failed()) {
                if (ls.is_initiator != ls.derived_initiator) ls.self_promotion_locked = true;
                reset_live_session(e, sock, cfg, ls, now, /*demote_to_derived=*/true);
            }
        }

        if (g_stop) break;

        if (now - last_rdv > (uint64_t)std::max<long>(cfg.interval_ms * 5, 10000)) {
            if (cfg.have_rendezvous) {
                rendezvous_register(sock, rdv_ep, e->identity, 1000);
                for (auto &peer : cfg.peers) {
                    auto it = live.find(addr_key(Endpoint{peer.host, peer.port}));
                    if (it != live.end() && it->second.sps->authenticated()) continue;
                    Endpoint looked;
                    if (rendezvous_lookup(sock, rdv_ep, peer.pk.data(), looked, 1000) &&
                        !(looked.ip == peer.host && looked.port == peer.port)) {
                        std::string old_key = addr_key(Endpoint{peer.host, peer.port});
                        auto oit = live.find(old_key);
                        if (oit != live.end()) {
                            LiveSession moved = std::move(oit->second);
                            live.erase(oit);
                            moved.ep = looked;
                            live.emplace(addr_key(looked), std::move(moved));
                        }
                        peer.host = looked.ip;
                        peer.port = looked.port;
                    }
                }
            }
            last_rdv = now;
        }

        if (now - last_cycle >= (uint64_t)std::max<long>(cfg.interval_ms, 200)) {
            cycle_no++;
            for (auto &peer : cfg.peers) {
                auto it = live.find(addr_key(Endpoint{peer.host, peer.port}));
                if (it != live.end() && it->second.sps->failed()) {
                    /* Trigger (a) — SESSION-POLICY REDESIGN point 2: a
                     * session that has failed (bad handshake step or a
                     * rejected identity proof) is dead and never recovers on
                     * its own; reset it here as a backstop for anything the
                     * immediate check in the recv loop above missed. Also
                     * where a self-promoted session demotes back to its
                     * derived role if that promotion turned out to collide
                     * with the real initiator (FINDING-3) — see
                     * reset_live_session() and self_promotion_locked. */
                    if (it->second.is_initiator != it->second.derived_initiator)
                        it->second.self_promotion_locked = true;
                    reset_live_session(e, sock, cfg, it->second, now, /*demote_to_derived=*/true);
                }
                bool authed = it != live.end() && it->second.sps->authenticated();
                if (authed) {
                    last_result[&peer] = "ok/direct";
                } else if (cfg.have_relay) {
                    int budget = (int)std::min<long>(cfg.interval_ms, 3000);
                    if (budget < 200) budget = 200;
                    bool ok = try_relay(e, sock, cfg, peer, my_pk, budget);
                    last_result[&peer] = ok ? "ok/relay" : "failed";
                } else {
                    last_result[&peer] = "failed";
                }
            }
            fprintf(stdout, "%s cycle %llu: peers=%zu\n", ts().c_str(),
                    (unsigned long long)cycle_no, cfg.peers.size());
            for (auto &peer : cfg.peers)
                fprintf(stdout, "%s   peer %s: %s\n", ts().c_str(),
                        hexstr(peer.pk.data(), 32).c_str(), last_result[&peer].c_str());
            fflush(stdout);
            last_cycle = now;
        }
    }

    fprintf(stdout, "%s shutting down\n", ts().c_str());
    fflush(stdout);
    return 0;
}

} // namespace

int main(int argc, char **argv) {
    std::string config_path;
    std::vector<std::pair<std::string, std::string>> cli_overrides;
    bool mode_identity = false, mode_once = false;

    for (int i = 1; i < argc; i++) {
        std::string a = argv[i];
        if (a == "--identity") { mode_identity = true; continue; }
        if (a == "--once") { mode_once = true; continue; }
        if (a == "--config") {
            if (i + 1 >= argc) { fprintf(stderr, "komed: --config needs a value\n"); return 2; }
            config_path = argv[++i];
            continue;
        }
        if (a.rfind("--config=", 0) == 0) { config_path = a.substr(9); continue; }
        if (a.rfind("--", 0) == 0) {
            std::string body = a.substr(2);
            auto eq = body.find('=');
            if (eq == std::string::npos) {
                fprintf(stderr, "komed: unrecognized flag: %s\n", a.c_str());
                return 2;
            }
            cli_overrides.emplace_back(body.substr(0, eq), body.substr(eq + 1));
            continue;
        }
        if (config_path.empty()) { config_path = a; continue; }
        fprintf(stderr, "komed: unexpected argument: %s\n", a.c_str());
        return 2;
    }

    if (config_path.empty()) {
        fprintf(stderr, "usage: komed <config-file> [--key=value ...] [--identity | --once]\n");
        return 2;
    }

    Config cfg;
    std::string err;
    if (!load_config_file(config_path, cfg, &err)) {
        fprintf(stderr, "komed: %s\n", err.c_str());
        return 2;
    }
    for (auto &kv : cli_overrides) {
        if (!apply_kv(cfg, kv.first, kv.second, &err)) {
            fprintf(stderr, "komed: --%s=%s: %s\n", kv.first.c_str(), kv.second.c_str(), err.c_str());
            return 2;
        }
    }

    if (cfg.db.empty()) {
        fprintf(stderr, "komed: db= is required\n");
        return 2;
    }

    uint8_t seed[SYNC_SEED_LEN];
    if (!cfg.seed_file.empty()) {
        if (!load_seed_file(cfg.seed_file, seed, &err)) {
            fprintf(stderr, "komed: %s\n", err.c_str());
            return 2;
        }
    } else {
        FILE *rf = fopen("/dev/urandom", "rb");
        if (rf) {
            size_t n = fread(seed, 1, sizeof seed, rf);
            fclose(rf);
            if (n != sizeof seed) { fprintf(stderr, "komed: failed to read random seed\n"); return 1; }
        } else {
            fprintf(stderr, "komed: no seed_file and /dev/urandom unavailable\n");
            return 1;
        }
    }

    std::string lock_err;
    if (!acquire_db_lock(cfg.db, &lock_err)) {
        fprintf(stderr, "komed: %s\n", lock_err.c_str());
        return 1;
    }

    sync_engine *e = sync_engine_open(cfg.db.c_str(), seed);
    /* Best-effort scrub of the local seed copy now that the engine has derived
     * identity from it — it is never logged either way. */
    memset(seed, 0, sizeof seed);
    if (!e) {
        fprintf(stderr, "komed: failed to open db: %s\n", cfg.db.c_str());
        release_db_lock();
        return 1;
    }

    uint8_t my_pk[SYNC_PUBKEY_LEN];
    sync_engine_identity(e, my_pk);

    if (mode_identity) {
        printf("%s\n", hexstr(my_pk, 32).c_str());
        shutdown_engine(e);
        return 0;
    }

    for (auto &path : cfg.cap_files) {
        std::vector<uint8_t> blob;
        if (!read_file_bytes(path, blob)) {
            fprintf(stderr, "komed: cannot read cap_file: %s\n", path.c_str());
            shutdown_engine(e);
            return 2;
        }
        sync_capability *cap = sync_capability_decode(blob.data(), blob.size());
        if (!cap) {
            fprintf(stderr, "komed: cap_file does not decode as a capability: %s\n", path.c_str());
            shutdown_engine(e);
            return 1;
        }
        int rc = sync_engine_grant(e, cap);
        sync_capability_free(cap);
        if (rc != SYNC_OK) {
            fprintf(stderr, "komed: failed to grant capability from %s (error %d)\n", path.c_str(), rc);
            shutdown_engine(e);
            return 1;
        }
    }

    UdpSocket sock;
    if (!sock.open("0.0.0.0", cfg.listen)) {
        fprintf(stderr, "komed: bind udp/%u failed\n", cfg.listen);
        shutdown_engine(e);
        return 1;
    }

    fprintf(stdout, "%s komed: identity=%s db=%s listen=udp/%u peers=%zu\n",
            ts().c_str(), hexstr(my_pk, 32).c_str(), cfg.db.c_str(),
            sock.local().port, cfg.peers.size());
    fflush(stdout);

    install_signal_handlers();

    int rc;
    if (mode_once) {
        rc = run_once(e, sock, cfg, my_pk);
    } else {
        rc = run_daemon(e, sock, cfg, my_pk);
    }

    shutdown_engine(e);
    return rc;
}
