/* tcp_relay.h — blind store-and-forward relay over persistent TCP (issue #49).
 * Internal.
 *
 * Same privacy invariant as the UDP relay (transport/relay.h): forwards
 * opaque ciphertext blobs and never holds key material or a decryption path.
 * Differs in three ways driven by TCP's shape (see the design plan):
 *
 *   - Mailbox = a dedicated EdDSA keypair's public key (not a peer identity).
 *     A mailbox is a *retained log*, not a drain-on-fetch queue: FETCH takes
 *     a client-held cursor (since_seq) and is non-destructive, because a
 *     shared circle mailbox must let every member read the same post.
 *   - No session state and no one-shot ATTACH: every operation is
 *     individually signed against the connection's HELLO challenge
 *     (mailbox_pk is both the identity and the verification key), so a
 *     forwarded frame is worth exactly one operation to whoever relays it.
 *   - The server owns raw non-blocking I/O itself (TcpStream's blocking
 *     send_all / unbounded recv_frame buffering are wrong for a server
 *     fielding untrusted persistent connections) in a single-threaded poll
 *     loop — no locks, TSan-clean by construction.
 *
 * Blindness is structural, not just documented: this file and its .cpp never
 * call aead_decrypt, x25519, or sign — only random_bytes (the HELLO nonce)
 * and verify (checking a client's claim against its own mailbox_pk). The
 * daemon's static identity keypair (services/tcp_relay/tcp_relay_main.cpp) is
 * the one place a secret key is generated at all, and it never touches a
 * client's blob.
 *
 * On-path note (documented once, here): a byte-proxy MITM is indistinguish-
 * able from the network and is the already-accepted adversary for the whole
 * stack (every envelope is E2EE upstream of this relay). The per-op
 * signature stops such a MITM from *minting* operations of its own; it does
 * not hide connection metadata. Deployments wanting on-path privacy run this
 * behind TLS/Noise. */
#ifndef SYNC_TCP_RELAY_H
#define SYNC_TCP_RELAY_H

#include <cstdint>
#include <deque>
#include <functional>
#include <map>
#include <string>
#include <utility>
#include <vector>

#include "transport/tcp.h"
#include "transport/udp.h" /* Endpoint */

namespace ke {

/* ---- wire constants (shared by server, client helpers, and tests) ------ */

constexpr char kTcpRelayOpHello    = 'H'; /* server -> client, on accept    */
constexpr char kTcpRelayOpOk       = 'O'; /* server -> client               */
constexpr char kTcpRelayOpErr      = 'E'; /* server -> client               */
constexpr char kTcpRelayOpDeliver  = 'D'; /* server -> client, FETCH reply  */
constexpr char kTcpRelayOpPost     = 'P'; /* client -> server               */
constexpr char kTcpRelayOpFetch    = 'F'; /* client -> server               */
constexpr char kTcpRelayOpPushReg  = 'R'; /* client -> server               */

constexpr uint8_t kTcpRelayErrMalformed      = 1;
constexpr uint8_t kTcpRelayErrAuth           = 2;
constexpr uint8_t kTcpRelayErrRateLimited    = 3;
constexpr uint8_t kTcpRelayErrTooLarge       = 4;
constexpr uint8_t kTcpRelayErrCapacity       = 5;
constexpr uint8_t kTcpRelayErrTooManyMailboxes = 6;

constexpr uint8_t kTcpRelayHelloVersion = 1;

/* Domain-separated signing transcript for every client op (decision 2 of the
 * plan): binds the signature to this relay (server_pk), this connection
 * (nonce), and the exact op — so a signature minted for relay A or op X is
 * worthless replayed at relay B or as a different op. */
constexpr char kTcpRelayOpDomain[] = "kome-relay-op-v1";

/* ---- MailboxLog: the blind, retained-log store -------------------------- */

/* An opaque per-mailbox wake target the caller (TcpRelayServer) notifies
 * through PushNotifier after a successful POST. Carries no mailbox id, no
 * sender, no content — see PushNotifier below. */
struct TcpRelayWakeTarget {
    uint8_t     provider = 0;
    std::string handle;
};

/* Retained-log mailbox store: caps/TTL/eviction adapted from transport/
 * relay.cpp's Relay for FETCH-is-non-destructive semantics (see file
 * header). All operations take an explicit `now_ms` (caller-supplied wall
 * time) rather than reading a clock internally, so tests can move time
 * forward without sleeping and the server has one clock read per poll step. */
class MailboxLog {
public:
    explicit MailboxLog(uint64_t retention_hours = kDefaultRetentionHours);
    /* Test/inspection hook: pin the seq-counter seed instead of deriving it
     * from wall_ms() at construction, so the "recreated/restarted mailbox
     * never reuses old seq space" property is assertable deterministically
     * rather than racing the real clock. */
    MailboxLog(uint64_t retention_hours, uint64_t seq_seed);

    /* Append blob (already capacity-checked by the caller: 1..64 KiB) to
     * mailbox_pk's log, creating the mailbox if absent. On success sets
     * *out_seq to the assigned seq (from one counter shared by every
     * mailbox, seeded from wall-clock at first construction — see the plan's
     * "seq identity" rationale) and, if out_wakes is non-null, appends the
     * mailbox's registered push handles that are due (debounced) a wake.
     * Returns false only on a capacity drop (global byte cap still exceeded
     * after evicting every other mailbox this connection may touch) — the
     * caller must reply ERR 5, never a lying OK. */
    bool store(const uint8_t mailbox_pk[32], const std::string &blob,
              uint64_t now_ms, uint64_t *out_seq,
              std::vector<TcpRelayWakeTarget> *out_wakes = nullptr);

    /* Non-destructive: appends records with seq > since_seq (budget-capped
     * at kDeliverBudgetBytes, always at least one record if any qualify, so
     * the fetch-paginate loop always makes progress) to out, in seq order.
     * Sets *evicted_up_to to the mailbox's highest TTL/cap-evicted seq (0 if
     * the mailbox doesn't exist locally — e.g. never posted to, or evicted
     * as a whole; that loss is not relay-detectable, by design). Refreshes
     * the mailbox's LRU position (fetch-driven LRU: FETCH and creation touch
     * it, POST does not — see the plan's eviction-economics rationale). */
    void fetch(const uint8_t mailbox_pk[32], uint64_t since_seq, uint64_t now_ms,
              std::vector<std::pair<uint64_t, std::string>> &out,
              uint64_t *evicted_up_to);

    /* Register a wake handle on mailbox_pk (creating the mailbox if absent).
     * Bounded set per mailbox (kMaxPushHandles, evict-oldest); re-registering
     * an identical (provider, handle) is a no-op. Returns false only if
     * handle exceeds kMaxPushHandleBytes (the caller should have already
     * rejected that as malformed). */
    bool register_push(const uint8_t mailbox_pk[32], uint8_t provider,
                       const std::string &handle, uint64_t now_ms);

    /* Sweep every mailbox for TTL-expired records. Cheap at the bounded
     * mailbox count; called periodically by the server (not every poll
     * step) and by store/fetch lazily for the one mailbox they touch. */
    void sweep_all(uint64_t now_ms);

    bool   exists(const uint8_t mailbox_pk[32]) const;
    size_t mailboxes() const { return mailboxes_.size(); }
    size_t total_bytes() const { return total_bytes_; }

    /* Test-only: override the global byte cap (production always runs at the
     * fixed 64 MiB constant). Structurally, a single mailbox is capped far
     * below the global cap and store() always evicts every other LRU
     * mailbox before giving up (see the plan's eviction-economics
     * rationale), so genuine capacity exhaustion (ERR 5) is not reachable in
     * a test within a reasonable byte budget without shrinking this. */
    void set_total_bytes_cap_for_test(size_t cap) { max_total_bytes_ = cap; }

    static constexpr uint64_t kDefaultRetentionHours = 168; /* 7 days */

private:
    struct Record {
        uint64_t    seq = 0;
        uint64_t    arrival_ms = 0;
        std::string blob;
    };
    struct PushHandle {
        uint8_t     provider = 0;
        std::string handle;
        bool        ever_woken = false;
        uint64_t    last_wake_ms = 0;
    };
    struct MailboxEntry {
        std::deque<Record>      records;
        size_t                  bytes = 0;
        uint64_t                evicted_up_to = 0;
        uint64_t                lru_seq = 0; /* 0 == not registered in lru_ */
        std::vector<PushHandle> push_handles;
    };
    using Map = std::map<std::string, MailboxEntry>;

    static std::string key(const uint8_t pk[32]) {
        return std::string((const char *)pk, 32);
    }
    void touch(Map::iterator it);
    void sweep_mailbox(MailboxEntry &mb, uint64_t now_ms);
    void evict_oldest_record(MailboxEntry &mb);
    /* Evict the globally least-recently-used mailbox whose key != protect
     * (protect="" never matches a real 32-byte key). Returns false if none
     * could be evicted (every mailbox is protected, or the table is empty). */
    bool evict_lru_mailbox(const std::string &protect);

    Map                              mailboxes_;
    std::map<uint64_t, std::string>  lru_; /* access_seq -> mailbox key, asc */
    uint64_t                         access_seq_ = 0;
    uint64_t                         next_seq_;
    size_t                           total_bytes_ = 0;
    size_t                           max_total_bytes_; /* set from the real
                                                          * cap in the .cpp;
                                                          * see set_total_
                                                          * bytes_cap_for_test */
    uint64_t                         retention_ms_;
};

/* ---- push notification --------------------------------------------------
 *
 * The wake carries only the opaque handle ("sync now") — no mailbox id, no
 * sender, no size, no content. Registering a raw APNs/FCM token here would
 * let the relay link every circle that shares a device (tokens are stable,
 * device-global, and outlive mailbox rotation); the interface instead
 * expects a per-mailbox opaque handle whose app-side push gateway maps
 * handle -> token, so the relay learns only mailbox<->handle and the gateway
 * only handle<->token. See DECISIONS.md. */
struct PushNotifier {
    virtual ~PushNotifier();
    virtual void wake(uint8_t provider, const std::string &handle) = 0;
};

/* ---- per-IP rate limiting (persists across reconnects) ------------------ */

/* Token buckets keyed by source IP (not connection — a reconnect must not
 * reset a budget), in a bounded LRU-expired table. Charged by the server
 * before any signature verification, so garbage frames never reach EdDSA. */
class RateLimits {
public:
    bool charge_op(const std::string &ip, uint64_t now_ms);
    bool charge_post_bytes(const std::string &ip, size_t bytes, uint64_t now_ms);
    bool charge_new_mailbox(const std::string &ip, uint64_t now_ms);
    /* Admits one more concurrent connection from ip (false if already at the
     * per-IP cap); pair with release_connection on disconnect. */
    bool admit_connection(const std::string &ip);
    void release_connection(const std::string &ip);

    static constexpr double   kOpsRatePerSec        = 20.0;
    static constexpr double   kOpsBurst             = 60.0;
    static constexpr double   kPostBytesRatePerSec  = 256.0 * 1024.0;
    static constexpr double   kPostBytesBurst       = 1024.0 * 1024.0;
    static constexpr double   kNewMailboxRatePerSec = 4.0 / 60.0;
    static constexpr double   kNewMailboxBurst      = 8.0;
    static constexpr int      kMaxConnsPerIp        = 8;

private:
    struct Bucket {
        double   tokens = 0;
        uint64_t last_ms = 0;
        bool     initialized = false;
    };
    struct IpEntry {
        Bucket ops, post_bytes, new_mailbox;
        int      concurrent = 0;
        uint64_t lru_seq = 0;
    };
    /* Refill `b` for elapsed time up to now_ms, then take `cost` tokens if
     * available. A bucket's first use fills it to `burst` (a fresh IP starts
     * with its full burst allowance, not zero). */
    static bool take(Bucket &b, double rate_per_sec, double burst, double cost,
                     uint64_t now_ms);
    IpEntry &get(const std::string &ip);
    void     touch(std::map<std::string, IpEntry>::iterator it);
    void     evict_lru();

    std::map<std::string, IpEntry>  table_;
    std::map<uint64_t, std::string> lru_;
    uint64_t                        access_seq_ = 0;
};

/* ---- per-op signature verification (decision 2) -------------------------
 *
 * Exposed standalone (no connection/socket needed) so it is unit-testable
 * directly: forged signature, cross-nonce replay (a signature valid under a
 * different HELLO), and ctr replay are each one call. */

/* Build the exact bytes a client signs / the server verifies for one op. */
std::string tcp_relay_op_transcript(const uint8_t server_pk[32],
                                    const uint8_t nonce[16], uint8_t op,
                                    const uint8_t mailbox_pk[32], uint64_t ctr,
                                    const std::string &payload);

/* Verify one op against (server_pk, nonce) and mailbox_pk, requiring ctr to
 * strictly exceed the last accepted ctr for this (connection, mailbox) pair.
 * ctr_initialized/last_ctr are caller-owned state for that pair (a fresh
 * pair starts with *ctr_initialized == false); advanced only on success, so
 * a forged frame can never poison or block a subsequent legitimate one. */
bool tcp_relay_verify_op(const uint8_t server_pk[32], const uint8_t nonce[16],
                         uint8_t op, const uint8_t mailbox_pk[32], uint64_t ctr,
                         const std::string &payload, const uint8_t sig[64],
                         bool *ctr_initialized, uint64_t *last_ctr);

/* ---- wire framing helpers (shared by the server, client helpers, tests) - */

/* A parsed client op-frame header: op(1) || mailbox_pk(32) || ctr(8 LE) ||
 * payload || sig(64). Never throws on truncated/garbage input; returns false
 * if the frame is too short to hold the fixed fields (payload may be empty).
 * Op-specific payload shape (POST's blob, FETCH's varint, PUSH_REG's
 * provider+handle) is validated by the caller, not here. */
struct TcpRelayParsedOp {
    uint8_t     op = 0;
    uint8_t     mailbox_pk[32] = {};
    uint64_t    ctr = 0;
    std::string payload;
    uint8_t     sig[64] = {};
};
bool tcp_relay_parse_client_frame(const std::string &frame, TcpRelayParsedOp &out);

/* Assemble one client op frame (op || mailbox_pk || ctr || payload || sig) —
 * the inverse of tcp_relay_parse_client_frame, for hand-building frames
 * (including deliberately invalid ones) in tests and the client helpers. */
std::string tcp_relay_build_op_frame(uint8_t op, const uint8_t mailbox_pk[32],
                                     uint64_t ctr, const std::string &payload,
                                     const uint8_t sig[64]);

/* ---- server --------------------------------------------------------------
 *
 * Single-threaded poll loop, server-owned raw I/O (see file header for why:
 * TcpStream's blocking send_all / unbounded recv_frame buffering are unsafe
 * for a server fielding untrusted persistent connections). No locks. */
class TcpRelayServer {
public:
    /* server_pk is the relay's static EdDSA public key, generated by the
     * caller (services/tcp_relay/tcp_relay_main.cpp) from an identity seed
     * or ephemerally — this class never generates or holds a secret key.
     * notifier may be null (no push wakes fired). */
    TcpRelayServer(const uint8_t server_pk[32], PushNotifier *notifier,
                  uint64_t retention_hours = MailboxLog::kDefaultRetentionHours);
    ~TcpRelayServer();
    TcpRelayServer(const TcpRelayServer &) = delete;
    TcpRelayServer &operator=(const TcpRelayServer &) = delete;

    bool     listen(const char *ip, uint16_t port);
    Endpoint local() const { return listener_.local(); }
    void     close();

    /* One poll() iteration over the listener + every connection: bounded
     * accept, non-blocking read/parse/reply, TX flush, deadline reaping,
     * periodic TTL sweep. Returns false only if the listener itself is not
     * open (caller stops the loop); otherwise always true, including on a
     * poll() error (EINTR and friends just make this step a no-op). */
    bool   step(int timeout_ms);
    size_t connection_count() const { return conns_.size(); }

    /* Test aid mirrored by the daemon's --dump-frames: invoked with every
     * raw client frame exactly as received, before any parsing, so an
     * end-to-end test can prove-by-grep that only ever-ciphertext bytes (and
     * never key material) reached this process. */
    void set_frame_sink(std::function<void(const std::string &)> sink) {
        frame_sink_ = std::move(sink);
    }

    static constexpr size_t   kMaxClientFrameBytes = 68u * 1024;  /* at prefix */
    static constexpr size_t   kMaxTxBytes          = 2u << 20;    /* per conn */
    static constexpr size_t   kMaxMailboxesPerConn = 16;
    static constexpr int      kMaxAuthFailures     = 3;
    static constexpr int      kMaxProtocolErrors   = 8;
    static constexpr size_t   kMaxAcceptPerStep    = 16;
    static constexpr size_t   kMaxGlobalConns      = 256;
    static constexpr uint64_t kIdleTimeoutMs       = 120000;
    static constexpr uint64_t kFrameProgressMs     = 30000;
    static constexpr uint64_t kTxStallMs           = 30000;
    static constexpr uint64_t kSweepIntervalMs     = 1000;

private:
    struct MailboxCtr {
        bool     initialized = false;
        uint64_t last = 0;
    };
    struct Conn {
        int                             fd = -1;
        std::string                     ip;
        uint8_t                         nonce[16] = {};
        std::string                     rx, tx;
        uint64_t                        last_activity_ms = 0;
        uint64_t                        frame_started_ms = 0; /* 0 == none pending */
        uint64_t                        tx_progress_ms = 0;
        int                             auth_failures = 0;
        int                             protocol_errors = 0;
        bool                            closing = false;
        std::map<std::string, MailboxCtr> mailboxes; /* mailbox key -> ctr state */
    };

    void accept_loop();
    void read_conn(Conn &c);
    void process_frame(Conn &c, const std::string &frame);
    void queue_frame(Conn &c, const std::string &body);
    void flush_tx(Conn &c);
    void send_ok(Conn &c, uint64_t detail);
    void send_err(Conn &c, uint8_t code);
    /* send_err for a client protocol violation (malformed/bad-shape/bad-op
     * frame): also counts toward the per-connection protocol-error budget and
     * drops the connection past kMaxProtocolErrors, so a flood of tiny bad
     * frames can't monopolize the single-threaded loop with ERR replies. */
    void reject(Conn &c, uint8_t code);
    void send_deliver(Conn &c, uint64_t evicted_up_to,
                      const std::vector<std::pair<uint64_t, std::string>> &recs);
    void reap(Conn &c);

    TcpListener                    listener_;
    std::map<int, Conn>            conns_;
    MailboxLog                     log_;
    RateLimits                     limits_;
    uint8_t                        server_pk_[32] = {};
    PushNotifier                  *notifier_ = nullptr;
    uint64_t                        last_sweep_ms_ = 0;
    std::function<void(const std::string &)> frame_sink_;
};

/* ---- client helpers over a blocking TcpStream ---------------------------
 *
 * Thin, synchronous helpers used by tests and any future runtime binding.
 * Each op-sending call signs per decision 2; the caller supplies the
 * mailbox's EdDSA keypair (sk[64]/pk[32], as returned by ke::sign's
 * convention) and a per-(connection, mailbox) counter it is responsible for
 * incrementing strictly between calls. */

bool tcp_relay_client_hello(TcpStream &s, uint8_t out_server_pk[32],
                            uint8_t out_nonce[16], int timeout_ms);

/* On success sets *out_seq to the assigned seq. On a server ERR reply,
 * returns false and, if out_err is non-null, fills it with the ERR code. */
bool tcp_relay_client_post(TcpStream &s, const uint8_t server_pk[32],
                           const uint8_t nonce[16], const uint8_t mailbox_sk[64],
                           const uint8_t mailbox_pk[32], uint64_t ctr,
                           const std::string &blob, uint64_t *out_seq,
                           uint8_t *out_err, int timeout_ms);

bool tcp_relay_client_fetch(TcpStream &s, const uint8_t server_pk[32],
                            const uint8_t nonce[16], const uint8_t mailbox_sk[64],
                            const uint8_t mailbox_pk[32], uint64_t ctr,
                            uint64_t since_seq,
                            std::vector<std::pair<uint64_t, std::string>> &out_records,
                            uint64_t *out_evicted_up_to, uint8_t *out_err,
                            int timeout_ms);

bool tcp_relay_client_register_push(TcpStream &s, const uint8_t server_pk[32],
                                    const uint8_t nonce[16],
                                    const uint8_t mailbox_sk[64],
                                    const uint8_t mailbox_pk[32], uint64_t ctr,
                                    uint8_t provider, const std::string &handle,
                                    uint8_t *out_err, int timeout_ms);

} // namespace ke

#endif /* SYNC_TCP_RELAY_H */
