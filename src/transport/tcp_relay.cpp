/* tcp_relay.cpp — blind store-and-forward relay over persistent TCP
 * (issue #49). See tcp_relay.h for the design rationale. */
#include "transport/tcp_relay.h"

#include <arpa/inet.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <poll.h>
#include <sys/socket.h>
#include <unistd.h>

#include <algorithm>
#include <chrono>
#include <cstring>

#include "byteorder.h"
#include "codec.h" /* ke::put_varint / ke::get_varint */
#include "crypto.h"

namespace ke {

namespace {

/* Same contract as ke::now_ms (sync_engine.cpp), kept local so a transport file
 * does not pull in the engine's internal state model. milliseconds::rep is
 * SIGNED, and a bare (uint64_t) cast is a modular wrap, not a clamp: a
 * pre-epoch wall clock lands within ~2.2e12 of UINT64_MAX, and every deadline
 * below is an unsigned `now - then` that would then read as astronomically
 * overdue and reap every live connection. */
uint64_t wall_ms() {
    using namespace std::chrono;
    const auto c = duration_cast<milliseconds>(
                       system_clock::now().time_since_epoch())
                       .count();
    return c < 0 ? 0 : (uint64_t)c;
}

/* DELIVER budget: below the 1 MiB per-mailbox cap, so a mailbox at the cap
 * genuinely needs more than one FETCH to drain (the fetch-paginate loop is
 * real and gets exercised, not a dead code path). */
constexpr size_t kDeliverBudgetBytes = 256u << 10;

constexpr size_t kTcpRelayMaxBlobBytes      = 1u << 16;  /* 64 KiB, one POST payload */
constexpr size_t kMaxMailboxBytes   = 1u << 20;  /* 1 MiB retained per mailbox */
constexpr size_t kMaxMailboxBlobs   = 256;
constexpr size_t kTcpRelayMaxTotalBytes     = 64u << 20; /* 64 MiB across all mailboxes */
constexpr size_t kMaxMailboxes      = 4096;
constexpr size_t kMaxPushHandles    = 4;
constexpr size_t kMaxPushHandleBytes = 256;
constexpr uint64_t kPushDebounceMs  = 30000;
constexpr size_t kMaxIpEntries      = 4096;

} // namespace

/* ---- MailboxLog ---------------------------------------------------------- */

/* Seeding next_seq_ from wall-clock guarantees a restarted (or evicted-then-
 * recreated) mailbox hands out seqs above any cursor a client saved against
 * the old incarnation — the property that keeps saved cursors valid across
 * restarts (see the plan's "seq identity" rationale). The trade-off is that
 * seq >> 20 discloses the relay's boot time to an authorized poster; this is
 * relay operational metadata (not client content, identity, or key material,
 * so outside the plaintext/key blindness invariant) and is subsumed by the
 * already-accepted seq-delta post-volume leak. A monotonic-across-restarts
 * seed with no clock disclosure would need persistent state we deliberately
 * don't keep. */
MailboxLog::MailboxLog(uint64_t retention_hours)
    : next_seq_(wall_ms() << 20), max_total_bytes_(kTcpRelayMaxTotalBytes),
      retention_ms_(retention_hours * 3600000ull) {}

MailboxLog::MailboxLog(uint64_t retention_hours, uint64_t seq_seed)
    : next_seq_(seq_seed), max_total_bytes_(kTcpRelayMaxTotalBytes),
      retention_ms_(retention_hours * 3600000ull) {}

void MailboxLog::touch(Map::iterator it) {
    if (it->second.lru_seq) lru_.erase(it->second.lru_seq);
    it->second.lru_seq = ++access_seq_;
    lru_[it->second.lru_seq] = it->first;
}

void MailboxLog::evict_oldest_record(MailboxEntry &mb) {
    Record &r = mb.records.front();
    mb.bytes -= r.blob.size();
    total_bytes_ -= r.blob.size();
    mb.evicted_up_to = std::max(mb.evicted_up_to, r.seq);
    mb.records.pop_front();
}

void MailboxLog::sweep_mailbox(MailboxEntry &mb, uint64_t now_ms) {
    while (!mb.records.empty() &&
           mb.records.front().arrival_ms + retention_ms_ < now_ms)
        evict_oldest_record(mb);
}

void MailboxLog::sweep_all(uint64_t now_ms) {
    for (auto &kv : mailboxes_) sweep_mailbox(kv.second, now_ms);
}

bool MailboxLog::evict_lru_mailbox(const std::string &protect) {
    for (auto it = lru_.begin(); it != lru_.end(); ++it) {
        if (it->second == protect) continue;
        auto mit = mailboxes_.find(it->second);
        if (mit != mailboxes_.end()) {
            total_bytes_ -= mit->second.bytes;
            mailboxes_.erase(mit);
        }
        lru_.erase(it);
        return true;
    }
    return false;
}

bool MailboxLog::exists(const uint8_t pk[32]) const {
    return mailboxes_.find(key(pk)) != mailboxes_.end();
}

bool MailboxLog::store(const uint8_t pk[32], const std::string &blob,
                       uint64_t now_ms, uint64_t *out_seq,
                       std::vector<TcpRelayWakeTarget> *out_wakes) {
    std::string k = key(pk);
    auto it = mailboxes_.find(k);
    bool created = false;
    if (it == mailboxes_.end()) {
        if (mailboxes_.size() >= kMaxMailboxes) evict_lru_mailbox("");
        it = mailboxes_.emplace(k, MailboxEntry{}).first;
        touch(it); /* creation touches LRU; POST below does not (fetch-driven) */
        created = true;
    }
    MailboxEntry &mb = it->second;
    sweep_mailbox(mb, now_ms);

    /* Per-mailbox FIFO drop-oldest until this blob fits the retained-log caps. */
    while (!mb.records.empty() &&
           (mb.records.size() >= kMaxMailboxBlobs ||
            mb.bytes + blob.size() > kMaxMailboxBytes))
        evict_oldest_record(mb);

    /* Global byte cap: evict other LRU mailboxes (never this one) until the
     * new blob fits, keeping the relay usable for active circles instead of
     * permanently refusing new posts once full. */
    while (total_bytes_ + blob.size() > max_total_bytes_) {
        if (!evict_lru_mailbox(k)) break;
    }
    if (mb.bytes + blob.size() > kMaxMailboxBytes ||
        total_bytes_ + blob.size() > max_total_bytes_) {
        if (created) {
            if (mb.lru_seq) lru_.erase(mb.lru_seq);
            mailboxes_.erase(it);
        }
        return false;
    }

    uint64_t seq = next_seq_++;
    mb.records.push_back({seq, now_ms, blob});
    mb.bytes += blob.size();
    total_bytes_ += blob.size();
    *out_seq = seq;

    if (out_wakes) {
        for (auto &h : mb.push_handles) {
            if (!h.ever_woken ||
                elapsed_ms(now_ms, h.last_wake_ms) >= kPushDebounceMs) {
                out_wakes->push_back({h.provider, h.handle});
                h.last_wake_ms = now_ms;
                h.ever_woken = true;
            }
        }
    }
    return true;
}

void MailboxLog::fetch(const uint8_t pk[32], uint64_t since_seq, uint64_t now_ms,
                       std::vector<std::pair<uint64_t, std::string>> &out,
                       uint64_t *evicted_up_to) {
    auto it = mailboxes_.find(key(pk));
    if (it == mailboxes_.end()) {
        *evicted_up_to = 0; /* never posted, or evicted whole — not detectable */
        return;
    }
    MailboxEntry &mb = it->second;
    sweep_mailbox(mb, now_ms);
    touch(it); /* fetch-driven LRU refresh */
    *evicted_up_to = mb.evicted_up_to;

    size_t budget = kDeliverBudgetBytes;
    for (auto &rec : mb.records) {
        if (rec.seq <= since_seq) continue;
        if (!out.empty() && rec.blob.size() > budget) break; /* paginate */
        out.push_back({rec.seq, rec.blob});
        budget = (rec.blob.size() < budget) ? budget - rec.blob.size() : 0;
    }
}

bool MailboxLog::register_push(const uint8_t pk[32], uint8_t provider,
                               const std::string &handle, uint64_t now_ms) {
    if (handle.size() > kMaxPushHandleBytes) return false;
    std::string k = key(pk);
    auto it = mailboxes_.find(k);
    if (it == mailboxes_.end()) {
        if (mailboxes_.size() >= kMaxMailboxes) evict_lru_mailbox("");
        it = mailboxes_.emplace(k, MailboxEntry{}).first;
        touch(it);
    }
    (void)now_ms;
    MailboxEntry &mb = it->second;
    for (auto &h : mb.push_handles)
        if (h.provider == provider && h.handle == handle) return true; /* already registered */
    if (mb.push_handles.size() >= kMaxPushHandles)
        mb.push_handles.erase(mb.push_handles.begin()); /* evict-oldest */
    PushHandle ph;
    ph.provider = provider;
    ph.handle = handle;
    mb.push_handles.push_back(std::move(ph));
    return true;
}

/* ---- PushNotifier --------------------------------------------------------- */

PushNotifier::~PushNotifier() {}

/* ---- RateLimits ------------------------------------------------------------ */

bool RateLimits::take(Bucket &b, double rate_per_sec, double burst, double cost,
                      uint64_t now_ms) {
    if (!b.initialized) {
        b.tokens = burst;
        b.last_ms = now_ms;
        b.initialized = true;
    } else if (now_ms > b.last_ms) {
        double elapsed_s = (double)(now_ms - b.last_ms) / 1000.0;
        b.tokens = std::min(burst, b.tokens + elapsed_s * rate_per_sec);
        b.last_ms = now_ms;
    }
    if (b.tokens < cost) return false;
    b.tokens -= cost;
    return true;
}

void RateLimits::touch(std::map<std::string, IpEntry>::iterator it) {
    if (it->second.lru_seq) lru_.erase(it->second.lru_seq);
    it->second.lru_seq = ++access_seq_;
    lru_[it->second.lru_seq] = it->first;
}

void RateLimits::evict_lru() {
    for (auto it = lru_.begin(); it != lru_.end(); ++it) {
        auto eit = table_.find(it->second);
        /* Never evict a source with a live connection — that would silently
         * reset its budget to full while it's still connected. */
        if (eit != table_.end() && eit->second.concurrent > 0) continue;
        if (eit != table_.end()) table_.erase(eit);
        lru_.erase(it);
        return;
    }
}

RateLimits::IpEntry &RateLimits::get(const std::string &ip) {
    auto it = table_.find(ip);
    if (it == table_.end()) {
        if (table_.size() >= kMaxIpEntries) evict_lru();
        it = table_.emplace(ip, IpEntry{}).first;
    }
    touch(it);
    return it->second;
}

bool RateLimits::charge_op(const std::string &ip, uint64_t now_ms) {
    return take(get(ip).ops, kOpsRatePerSec, kOpsBurst, 1.0, now_ms);
}

bool RateLimits::charge_post_bytes(const std::string &ip, size_t bytes,
                                   uint64_t now_ms) {
    return take(get(ip).post_bytes, kPostBytesRatePerSec, kPostBytesBurst,
               (double)bytes, now_ms);
}

bool RateLimits::charge_new_mailbox(const std::string &ip, uint64_t now_ms) {
    return take(get(ip).new_mailbox, kNewMailboxRatePerSec, kNewMailboxBurst,
               1.0, now_ms);
}

bool RateLimits::admit_connection(const std::string &ip) {
    IpEntry &e = get(ip);
    if (e.concurrent >= kMaxConnsPerIp) return false;
    e.concurrent++;
    return true;
}

void RateLimits::release_connection(const std::string &ip) {
    auto it = table_.find(ip);
    if (it != table_.end() && it->second.concurrent > 0) it->second.concurrent--;
}

/* ---- per-op signature verification ---------------------------------------- */

std::string tcp_relay_op_transcript(const uint8_t server_pk[32],
                                    const uint8_t nonce[16], uint8_t op,
                                    const uint8_t mailbox_pk[32], uint64_t ctr,
                                    const std::string &payload) {
    std::string m;
    m.reserve(sizeof(kTcpRelayOpDomain) - 1 + 32 + 16 + 1 + 32 + 8 + payload.size());
    m.append(kTcpRelayOpDomain, sizeof(kTcpRelayOpDomain) - 1); /* no NUL */
    m.append((const char *)server_pk, 32);
    m.append((const char *)nonce, 16);
    m.push_back((char)op);
    m.append((const char *)mailbox_pk, 32);
    put_u64le(m, ctr);
    m += payload;
    return m;
}

bool tcp_relay_verify_op(const uint8_t server_pk[32], const uint8_t nonce[16],
                         uint8_t op, const uint8_t mailbox_pk[32], uint64_t ctr,
                         const std::string &payload, const uint8_t sig[64],
                         bool *ctr_initialized, uint64_t *last_ctr) {
    if (*ctr_initialized && ctr <= *last_ctr) return false; /* replay */
    std::string msg =
        tcp_relay_op_transcript(server_pk, nonce, op, mailbox_pk, ctr, payload);
    if (!verify(mailbox_pk, msg.data(), msg.size(), sig)) return false;
    *last_ctr = ctr;
    *ctr_initialized = true;
    return true;
}

/* ---- wire framing helpers -------------------------------------------------- */

bool tcp_relay_parse_client_frame(const std::string &frame, TcpRelayParsedOp &out) {
    /* op(1) + mailbox_pk(32) + ctr(8) + sig(64) = 105 fixed bytes minimum;
     * payload is whatever remains (may be empty). */
    if (frame.size() < 105) return false;
    const uint8_t *p = (const uint8_t *)frame.data();
    out.op = p[0];
    std::memcpy(out.mailbox_pk, p + 1, 32);
    out.ctr = read_u64le(p + 33);
    size_t payload_len = frame.size() - 105;
    out.payload.assign((const char *)p + 41, payload_len);
    std::memcpy(out.sig, p + 41 + payload_len, 64);
    return true;
}

std::string tcp_relay_build_op_frame(uint8_t op, const uint8_t mailbox_pk[32],
                                     uint64_t ctr, const std::string &payload,
                                     const uint8_t sig[64]) {
    std::string f;
    f.reserve(1 + 32 + 8 + payload.size() + 64);
    f.push_back((char)op);
    f.append((const char *)mailbox_pk, 32);
    put_u64le(f, ctr);
    f += payload;
    f.append((const char *)sig, 64);
    return f;
}

/* ---- TcpRelayServer --------------------------------------------------------- */

TcpRelayServer::TcpRelayServer(const uint8_t server_pk[32], PushNotifier *notifier,
                               uint64_t retention_hours)
    : log_(retention_hours), notifier_(notifier) {
    std::memcpy(server_pk_, server_pk, 32);
}

TcpRelayServer::~TcpRelayServer() { close(); }

bool TcpRelayServer::listen(const char *ip, uint16_t port) {
    return listener_.open(ip, port);
}

void TcpRelayServer::close() {
    for (auto &kv : conns_) ::close(kv.first);
    conns_.clear();
    listener_.close();
}

void TcpRelayServer::reap(Conn &c) {
    limits_.release_connection(c.ip);
    ::close(c.fd);
}

void TcpRelayServer::queue_frame(Conn &c, const std::string &body) {
    if (c.closing) return;
    if (c.tx.size() + 4 + body.size() > kMaxTxBytes) {
        c.closing = true;
        return;
    }
    if (c.tx.empty()) c.tx_progress_ms = wall_ms();
    put_u32le(c.tx, (uint32_t)body.size());
    c.tx += body;
    flush_tx(c);
}

void TcpRelayServer::flush_tx(Conn &c) {
    while (!c.tx.empty()) {
        ssize_t w = ::send(c.fd, c.tx.data(), c.tx.size(), MSG_NOSIGNAL);
        if (w > 0) {
            c.tx.erase(0, (size_t)w);
            c.tx_progress_ms = wall_ms();
            continue;
        }
        if (w < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) break;
        c.closing = true;
        break;
    }
}

void TcpRelayServer::send_ok(Conn &c, uint64_t detail) {
    std::string body(1, kTcpRelayOpOk);
    put_varint(body, detail);
    queue_frame(c, body);
}

void TcpRelayServer::send_err(Conn &c, uint8_t code) {
    std::string body(1, kTcpRelayOpErr);
    body.push_back((char)code);
    queue_frame(c, body);
}

void TcpRelayServer::reject(Conn &c, uint8_t code) {
    send_err(c, code);
    if (++c.protocol_errors > kMaxProtocolErrors) c.closing = true;
}

void TcpRelayServer::send_deliver(
    Conn &c, uint64_t evicted_up_to,
    const std::vector<std::pair<uint64_t, std::string>> &recs) {
    std::string body(1, kTcpRelayOpDeliver);
    put_varint(body, evicted_up_to);
    put_varint(body, recs.size());
    for (auto &r : recs) {
        put_varint(body, r.first);
        put_varint(body, r.second.size());
        body += r.second;
    }
    queue_frame(c, body);
}

void TcpRelayServer::accept_loop() {
    for (size_t i = 0; i < kMaxAcceptPerStep; i++) {
        int fd = ::accept(listener_.fd(), nullptr, nullptr);
        if (fd < 0) break; /* EAGAIN (no more pending) or a real error */

        std::string ip = "0.0.0.0";
        sockaddr_in sa;
        socklen_t slen = sizeof sa;
        if (getpeername(fd, (sockaddr *)&sa, &slen) == 0) {
            char buf[INET_ADDRSTRLEN];
            if (inet_ntop(AF_INET, &sa.sin_addr, buf, sizeof buf)) ip = buf;
        }

        if (conns_.size() >= kMaxGlobalConns) { ::close(fd); continue; }
        if (!limits_.admit_connection(ip)) { ::close(fd); continue; }

        int fl = fcntl(fd, F_GETFL, 0);
        fcntl(fd, F_SETFL, fl | O_NONBLOCK);
        int one = 1;
        setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof one);

        uint8_t nonce[16];
        if (!random_bytes(nonce, 16)) {
            /* No HELLO without real entropy: an all-zero nonce would make one
             * captured client signature a forever-credential (decision 2). */
            limits_.release_connection(ip);
            ::close(fd);
            continue;
        }

        Conn c;
        c.fd = fd;
        c.ip = ip;
        std::memcpy(c.nonce, nonce, 16);
        uint64_t now = wall_ms();
        c.last_activity_ms = now;
        c.tx_progress_ms = now;
        auto &ref = conns_.emplace(fd, std::move(c)).first->second;

        std::string hello(1, kTcpRelayOpHello);
        hello.push_back((char)kTcpRelayHelloVersion);
        hello.append((const char *)server_pk_, 32);
        hello.append((const char *)nonce, 16);
        queue_frame(ref, hello);
    }
}

void TcpRelayServer::read_conn(Conn &c) {
    char buf[65536];
    ssize_t n = ::recv(c.fd, buf, sizeof buf, 0);
    if (n == 0) { c.closing = true; return; } /* EOF */
    if (n < 0) {
        if (errno == EAGAIN || errno == EWOULDBLOCK) return; /* idle */
        c.closing = true;
        return;
    }
    c.last_activity_ms = wall_ms();
    if (c.rx.empty()) c.frame_started_ms = c.last_activity_ms;
    c.rx.append(buf, (size_t)n);

    for (;;) {
        if (c.rx.size() < 4) break;
        uint32_t len = read_u32le((const uint8_t *)c.rx.data());
        if (len > kMaxClientFrameBytes) { c.closing = true; return; } /* at prefix */
        if (c.rx.size() < 4 + (size_t)len) break; /* wait for the rest */
        std::string frame = c.rx.substr(4, len);
        c.rx.erase(0, 4 + len);
        if (frame_sink_) frame_sink_(frame);
        process_frame(c, frame);
        if (c.closing) return;
    }
    c.frame_started_ms = c.rx.empty() ? 0 : c.frame_started_ms;
}

void TcpRelayServer::process_frame(Conn &c, const std::string &frame) {
    uint64_t now = wall_ms();

    /* Charge the per-IP op budget for EVERY inbound frame BEFORE parsing, so a
     * flood of tiny malformed frames is throttled exactly like real ops (a
     * bad frame must not buy free work from the single-threaded loop). Crypto
     * still runs only after this and the shape checks, so garbage costs no
     * EdDSA either. */
    if (!limits_.charge_op(c.ip, now)) { send_err(c, kTcpRelayErrRateLimited); return; }

    TcpRelayParsedOp po;
    if (!tcp_relay_parse_client_frame(frame, po)) {
        reject(c, kTcpRelayErrMalformed);
        return;
    }

    /* Op-specific payload shape, checked before any auth work. */
    uint8_t push_provider = 0;
    std::string push_handle;
    uint64_t fetch_since_seq = 0;
    if (po.op == kTcpRelayOpPost) {
        if (po.payload.empty()) { reject(c, kTcpRelayErrMalformed); return; }
        if (po.payload.size() > kTcpRelayMaxBlobBytes) { reject(c, kTcpRelayErrTooLarge); return; }
    } else if (po.op == kTcpRelayOpFetch) {
        const uint8_t *p = (const uint8_t *)po.payload.data();
        const uint8_t *end = p + po.payload.size();
        if (!get_varint(p, end, fetch_since_seq) || p != end) {
            reject(c, kTcpRelayErrMalformed);
            return;
        }
    } else if (po.op == kTcpRelayOpPushReg) {
        const uint8_t *p = (const uint8_t *)po.payload.data();
        const uint8_t *end = p + po.payload.size();
        if (end - p < 1) { reject(c, kTcpRelayErrMalformed); return; }
        push_provider = *p++;
        uint64_t hlen = 0;
        if (!get_varint(p, end, hlen) || (uint64_t)(end - p) != hlen ||
            hlen > kMaxPushHandleBytes) {
            reject(c, kTcpRelayErrMalformed);
            return;
        }
        push_handle.assign((const char *)p, (size_t)hlen);
    } else {
        reject(c, kTcpRelayErrMalformed);
        return;
    }

    std::string mbkey((const char *)po.mailbox_pk, 32);
    auto mit = c.mailboxes.find(mbkey);
    if (mit == c.mailboxes.end()) {
        if (c.mailboxes.size() >= kMaxMailboxesPerConn) {
            send_err(c, kTcpRelayErrTooManyMailboxes);
            return;
        }
        mit = c.mailboxes.emplace(mbkey, MailboxCtr{}).first;
    }

    if (!tcp_relay_verify_op(server_pk_, c.nonce, po.op, po.mailbox_pk, po.ctr,
                             po.payload, po.sig, &mit->second.initialized,
                             &mit->second.last)) {
        send_err(c, kTcpRelayErrAuth);
        c.auth_failures++;
        if (c.auth_failures > kMaxAuthFailures) c.closing = true;
        return;
    }

    bool is_new_mailbox = !log_.exists(po.mailbox_pk);

    if (po.op == kTcpRelayOpPost) {
        if (is_new_mailbox && !limits_.charge_new_mailbox(c.ip, now)) {
            send_err(c, kTcpRelayErrRateLimited);
            return;
        }
        if (!limits_.charge_post_bytes(c.ip, po.payload.size(), now)) {
            send_err(c, kTcpRelayErrRateLimited);
            return;
        }
        uint64_t seq = 0;
        std::vector<TcpRelayWakeTarget> wakes;
        if (!log_.store(po.mailbox_pk, po.payload, now, &seq, &wakes)) {
            send_err(c, kTcpRelayErrCapacity); /* store returns the truth; never a lying OK */
            return;
        }
        send_ok(c, seq);
        if (notifier_)
            for (auto &w : wakes) notifier_->wake(w.provider, w.handle);
    } else if (po.op == kTcpRelayOpFetch) {
        std::vector<std::pair<uint64_t, std::string>> recs;
        uint64_t evicted_up_to = 0;
        log_.fetch(po.mailbox_pk, fetch_since_seq, now, recs, &evicted_up_to);
        send_deliver(c, evicted_up_to, recs);
    } else { /* PUSH_REG */
        if (is_new_mailbox && !limits_.charge_new_mailbox(c.ip, now)) {
            send_err(c, kTcpRelayErrRateLimited);
            return;
        }
        log_.register_push(po.mailbox_pk, push_provider, push_handle, now);
        send_ok(c, 0);
    }
}

bool TcpRelayServer::step(int timeout_ms) {
    if (listener_.fd() < 0) return false;

    std::vector<pollfd> pfds;
    pfds.reserve(1 + conns_.size());
    pfds.push_back(pollfd{listener_.fd(), POLLIN, 0});
    for (auto &kv : conns_) {
        short ev = POLLIN;
        if (!kv.second.tx.empty()) ev |= POLLOUT;
        pfds.push_back(pollfd{kv.first, ev, 0});
    }

    int nr = ::poll(pfds.data(), pfds.size(), timeout_ms);
    if (nr > 0) {
        if (pfds[0].revents & POLLIN) accept_loop();
        for (size_t i = 1; i < pfds.size(); i++) {
            if (!pfds[i].revents) continue;
            auto it = conns_.find(pfds[i].fd);
            if (it == conns_.end()) continue;
            if (pfds[i].revents & (POLLHUP | POLLERR | POLLNVAL)) {
                it->second.closing = true;
                continue;
            }
            if (pfds[i].revents & POLLOUT) flush_tx(it->second);
            if (!it->second.closing && (pfds[i].revents & POLLIN))
                read_conn(it->second);
        }
    }
    /* nr < 0 (EINTR or similar) and nr == 0 (plain timeout) both fall through
     * to deadline/sweep housekeeping below, same as a quiet poll. */

    uint64_t now = wall_ms();
    for (auto it = conns_.begin(); it != conns_.end();) {
        Conn &c = it->second;
        bool drop = c.closing;
        if (!drop && elapsed_ms(now, c.last_activity_ms) > kIdleTimeoutMs)
            drop = true;
        if (!drop && c.frame_started_ms &&
            elapsed_ms(now, c.frame_started_ms) > kFrameProgressMs)
            drop = true;
        if (!drop && !c.tx.empty() &&
            elapsed_ms(now, c.tx_progress_ms) > kTxStallMs)
            drop = true;
        if (drop) {
            reap(c);
            it = conns_.erase(it);
        } else {
            ++it;
        }
    }

    if (elapsed_ms(now, last_sweep_ms_) >= kSweepIntervalMs) {
        log_.sweep_all(now);
        last_sweep_ms_ = now;
    }
    return true;
}

/* ---- client helpers --------------------------------------------------------- */

namespace {
bool read_reply_err(const std::string &frame, uint8_t *out_err) {
    if (frame.size() == 2 && frame[0] == kTcpRelayOpErr) {
        if (out_err) *out_err = (uint8_t)frame[1];
        return true;
    }
    return false;
}

std::string sign_and_build(const uint8_t server_pk[32], const uint8_t nonce[16],
                           uint8_t op, const uint8_t mailbox_sk[64],
                           const uint8_t mailbox_pk[32], uint64_t ctr,
                           const std::string &payload) {
    std::string msg = tcp_relay_op_transcript(server_pk, nonce, op, mailbox_pk, ctr, payload);
    uint8_t sig[64];
    sign(mailbox_sk, msg.data(), msg.size(), sig);
    return tcp_relay_build_op_frame(op, mailbox_pk, ctr, payload, sig);
}
} // namespace

bool tcp_relay_client_hello(TcpStream &s, uint8_t out_server_pk[32],
                            uint8_t out_nonce[16], int timeout_ms) {
    std::string frame;
    if (!s.recv_frame(frame, timeout_ms)) return false;
    if (frame.size() != 1 + 1 + 32 + 16) return false;
    if (frame[0] != kTcpRelayOpHello) return false;
    if ((uint8_t)frame[1] != kTcpRelayHelloVersion) return false;
    std::memcpy(out_server_pk, frame.data() + 2, 32);
    std::memcpy(out_nonce, frame.data() + 34, 16);
    return true;
}

bool tcp_relay_client_post(TcpStream &s, const uint8_t server_pk[32],
                           const uint8_t nonce[16], const uint8_t mailbox_sk[64],
                           const uint8_t mailbox_pk[32], uint64_t ctr,
                           const std::string &blob, uint64_t *out_seq,
                           uint8_t *out_err, int timeout_ms) {
    std::string frame = sign_and_build(server_pk, nonce, kTcpRelayOpPost, mailbox_sk,
                                       mailbox_pk, ctr, blob);
    if (!s.send_frame(frame)) return false;
    std::string reply;
    if (!s.recv_frame(reply, timeout_ms)) return false;
    if (read_reply_err(reply, out_err)) return false;
    if (reply.size() < 2 || reply[0] != kTcpRelayOpOk) return false;
    const uint8_t *p = (const uint8_t *)reply.data() + 1;
    const uint8_t *end = (const uint8_t *)reply.data() + reply.size();
    uint64_t seq = 0;
    if (!get_varint(p, end, seq) || p != end) return false;
    if (out_seq) *out_seq = seq;
    return true;
}

bool tcp_relay_client_fetch(TcpStream &s, const uint8_t server_pk[32],
                            const uint8_t nonce[16], const uint8_t mailbox_sk[64],
                            const uint8_t mailbox_pk[32], uint64_t ctr,
                            uint64_t since_seq,
                            std::vector<std::pair<uint64_t, std::string>> &out_records,
                            uint64_t *out_evicted_up_to, uint8_t *out_err,
                            int timeout_ms) {
    std::string payload;
    put_varint(payload, since_seq);
    std::string frame = sign_and_build(server_pk, nonce, kTcpRelayOpFetch, mailbox_sk,
                                       mailbox_pk, ctr, payload);
    if (!s.send_frame(frame)) return false;
    std::string reply;
    if (!s.recv_frame(reply, timeout_ms)) return false;
    if (read_reply_err(reply, out_err)) return false;
    if (reply.empty() || reply[0] != kTcpRelayOpDeliver) return false;

    const uint8_t *p = (const uint8_t *)reply.data() + 1;
    const uint8_t *end = (const uint8_t *)reply.data() + reply.size();
    uint64_t evicted_up_to = 0, n = 0;
    if (!get_varint(p, end, evicted_up_to)) return false;
    if (!get_varint(p, end, n)) return false;
    for (uint64_t i = 0; i < n; i++) {
        uint64_t seq = 0, len = 0;
        if (!get_varint(p, end, seq)) return false;
        if (!get_varint(p, end, len)) return false;
        if ((uint64_t)(end - p) < len) return false;
        out_records.emplace_back(seq, std::string((const char *)p, (size_t)len));
        p += len;
    }
    if (out_evicted_up_to) *out_evicted_up_to = evicted_up_to;
    return true;
}

bool tcp_relay_client_register_push(TcpStream &s, const uint8_t server_pk[32],
                                    const uint8_t nonce[16],
                                    const uint8_t mailbox_sk[64],
                                    const uint8_t mailbox_pk[32], uint64_t ctr,
                                    uint8_t provider, const std::string &handle,
                                    uint8_t *out_err, int timeout_ms) {
    std::string payload(1, (char)provider);
    put_varint(payload, handle.size());
    payload += handle;
    std::string frame = sign_and_build(server_pk, nonce, kTcpRelayOpPushReg, mailbox_sk,
                                       mailbox_pk, ctr, payload);
    if (!s.send_frame(frame)) return false;
    std::string reply;
    if (!s.recv_frame(reply, timeout_ms)) return false;
    if (read_reply_err(reply, out_err)) return false;
    return reply.size() >= 1 && reply[0] == kTcpRelayOpOk;
}

} // namespace ke
