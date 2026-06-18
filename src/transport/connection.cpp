/* connection.cpp — connect-and-sync core (M5). */
#include "transport/connection.h"

#include <chrono>

#include "engine.hpp"
#include "noise.h"
#include "transport/reliable.h"

namespace ke {

namespace {
uint64_t now_ms_mono() {
    using namespace std::chrono;
    return (uint64_t)duration_cast<milliseconds>(
               steady_clock::now().time_since_epoch())
        .count();
}
} // namespace

SecurePeerSession::SecurePeerSession(sync_engine *e, bool initiator,
                                     uint32_t gossip_interval_ms)
    : e_(e), initiator_(initiator), interval_(gossip_interval_ms),
      chan_(new NoiseChannel(initiator, e->identity)) {}

SecurePeerSession::~SecurePeerSession() {
    if (sess_) sync_session_end(sess_);
}

/* Step the reconcile session with in[0,in_len), encrypt any reply onto the
 * reliable link, then keep stepping with empty input to drain the session's
 * outbound queue — a large reply is split across several size-bounded messages
 * (P0), and a terminal HAVE elicits no peer reply to pull the rest, so the
 * sender must flush them itself. The reliable link queues them and delivers in
 * order. (sync_free(nullptr) is a no-op.) Returns true if it emitted anything. */
bool SecurePeerSession::pump_(const uint8_t *in, size_t in_len) {
    if (!sess_) return false;
    const uint8_t *p = in;
    size_t pl = in_len;
    bool emitted = false;
    for (;;) {
        uint8_t *o = nullptr; size_t ol = 0; int d = 0;
        sync_session_step(sess_, p, pl, &o, &ol, &d);
        p = nullptr; pl = 0; /* subsequent steps just drain the queue */
        if (ol) {
            std::string ct;
            chan_->encrypt(std::string((char *)o, ol), ct);
            link_.send(ct);
            emitted = true;
        }
        sync_free(o);
        if (!ol) break; /* queue drained, nothing more to send */
    }
    return emitted;
}

/* The Noise XX handshake authenticates only the X25519 static. Bind the channel
 * to our long-term EdDSA identity by signing the unique handshake transcript and
 * sending it as the first post-handshake message (once). */
void SecurePeerSession::send_proof_() {
    if (proof_sent_ || !chan_->done()) return;
    std::string proof, ct;
    if (chan_->make_identity_proof(proof) && chan_->encrypt(proof, ct)) {
        link_.send(ct);
        proof_sent_ = true;
    }
}

/* Handshake just completed: authenticate the reliability layer from here on (the
 * proof and all reconcile traffic), then send our proof. */
void SecurePeerSession::enable_after_handshake_() {
    uint8_t rk[32];
    chan_->reliability_key(rk);
    link_.enable_mac(rk);
    send_proof_();
}

/* (Re)begin a fresh, re-snapshotted reconcile cycle, read-scoped to the
 * authenticated peer. Records the engine state_gen the snapshot was taken at so
 * a later cycle boundary can tell whether our state has since advanced. Does not
 * send — callers pump if they want to emit the first message. */
void SecurePeerSession::begin_cycle_() {
    if (sess_) { sync_session_end(sess_); sess_ = nullptr; }
    sess_ = sync_session_begin_scoped(e_, initiator_ ? 1 : 0, peer_pk_.data());
    sess_gen_ = e_->state_gen;
    sess_done_ = false;
}

/* Initiator: start a fresh cycle and send its first fingerprint. */
void SecurePeerSession::kick_(uint64_t now) {
    begin_cycle_();
    pump_(nullptr, 0);
    last_kick_ = now;
}

void SecurePeerSession::drain_(uint64_t now, std::vector<std::string> &out) {
    std::vector<std::string> dgs;
    link_.poll(dgs, now);
    for (auto &dg : dgs) out.push_back(std::move(dg));
}

void SecurePeerSession::start(uint64_t now_mono, std::vector<std::string> &out) {
    last_progress_ = now_mono;
    if (initiator_) {
        std::string hs;
        bool done = false;
        chan_->step("", hs, done);
        link_.send(hs);
    }
    drain_(now_mono, out);
}

void SecurePeerSession::on_datagram(const std::string &dg, uint64_t now_mono,
                                    std::vector<std::string> &out) {
    if (failed_) return;
    std::vector<std::string> delivered;
    if (link_.on_datagram(dg, delivered)) last_progress_ = now_mono;
    for (auto &msg : delivered) {
        if (!chan_->done()) {
            std::string hs;
            bool done = false;
            if (!chan_->step(msg, hs, done)) { failed_ = true; break; }
            last_progress_ = now_mono;
            if (!hs.empty()) link_.send(hs); /* handshake msg: plain */
            if (chan_->done()) enable_after_handshake_();
        } else {
            std::string pt;
            if (!chan_->decrypt(msg, pt)) continue;
            last_progress_ = now_mono;
            if (!peer_ok_) {
                /* The first post-handshake message MUST be the peer's identity
                 * proof. A bad/absent proof => MITM, forgery, or a peer skipping
                 * authentication => abort. */
                if (!chan_->verify_identity_proof(pt, peer_pk_.data())) {
                    failed_ = true;
                    break;
                }
                peer_ok_ = true;
                /* Reconcile read-scoped to the authenticated peer, so a peer
                 * only receives namespaces it may read. */
                begin_cycle_();
                if (initiator_) { pump_(nullptr, 0); last_kick_ = now_mono; }
            } else {
                /* Gossip mode: the responder re-snapshots at the start of each new
                 * cycle (the previous one drained to empty). Stale-snapshot refresh
                 * when our own state has since advanced is handled at the cycle
                 * boundary in poll() (link idle) — NOT here mid-cycle, which would
                 * rebuild the O(state) snapshot on every datagram that applied a
                 * record (apply_change bumps state_gen) and tear down the in-flight
                 * reconcile. See poll(). */
                if (interval_ > 0 && !initiator_ && (!sess_ || sess_done_))
                    begin_cycle_();
                bool emitted = pump_((const uint8_t *)pt.data(), pt.size());
                if (interval_ > 0 && !emitted) sess_done_ = true;
            }
        }
    }
    drain_(now_mono, out);
}

void SecurePeerSession::poll(uint64_t now_mono, std::vector<std::string> &out) {
    drain_(now_mono, out);
    if (interval_ == 0 || !peer_ok_ || !chan_->done()) return;
    if (initiator_) {
        /* Initiator: start a fresh cycle once the previous settled (link idle)
         * and the interval has elapsed. */
        if (link_.idle() && now_mono - last_kick_ > interval_) {
            kick_(now_mono);
            drain_(now_mono, out);
        }
    } else {
        /* Responder (FINDING-1): refresh a stale snapshot at a cycle boundary —
         * when the link is idle (the previous cycle fully drained) and our state
         * has advanced past the session's snapshot. This is what lets a value
         * written (or learned) faster than the gossip interval eventually ship: a
         * session whose `sess_done_` never flips would otherwise stay frozen on a
         * stale snapshot forever. Gating on link_.idle() keeps it to once per
         * settled cycle rather than rebuilding the O(state) snapshot on every
         * datagram that applied a record. No send — the responder reconciles on
         * the next inbound fingerprint. */
        if (link_.idle() && e_->state_gen != sess_gen_)
            begin_cycle_();
    }
}

void SecurePeerSession::reset(uint64_t now_mono, std::vector<std::string> &out) {
    chan_ = std::unique_ptr<NoiseChannel>(new NoiseChannel(initiator_, e_->identity));
    link_ = ReliableLink();
    if (sess_) { sync_session_end(sess_); sess_ = nullptr; }
    proof_sent_ = false;
    peer_ok_ = false;
    failed_ = false;
    sess_done_ = false;
    sess_gen_ = 0;
    last_kick_ = 0;
    start(now_mono, out);
}

bool SecurePeerSession::handshake_done() const { return chan_->done(); }
bool SecurePeerSession::authenticated() const { return peer_ok_; }
bool SecurePeerSession::idle() const { return link_.idle(); }
bool SecurePeerSession::failed() const { return failed_; }

bool connect_and_sync(sync_engine *e, PeerTransport &t, bool initiator,
                      int total_timeout_ms) {
    SecurePeerSession s(e, initiator, /*gossip_interval_ms=*/0);
    std::vector<std::string> out;
    s.start(now_ms_mono(), out);
    for (auto &dg : out) t.send(dg);

    uint64_t deadline = now_ms_mono() + (uint64_t)total_timeout_ms;
    /* Re-handshake from scratch (fresh Noise channel + reliability state) on a
     * stall, but ONLY while still pre-authentication (handshake + identity proof).
     * There a cross-host stall — a blackholed handshake — can wait out the whole
     * timeout and the reliability-layer retransmit alone does not recover it; a
     * reset does (FINDING-2). Once authenticated, reconcile is driven by retransmit
     * and the overall deadline: a reset there would discard already-transferred
     * state and, against a slow / CPU-starved / high-latency peer, thrash — re-
     * handshaking faster than the peer can answer, so it never converges (observed
     * cross-host under concurrent load). The stall interval also backs off on each
     * successive reset and snaps back to the base on genuine progress, so a slow-
     * but-live handshake (high RTT) is not reset to death. */
    const uint64_t kStallBaseMs = 2000, kStallMaxMs = 30000;
    uint64_t stall_ms = kStallBaseMs;
    uint64_t seen_progress = s.last_progress();
    int quiet = 0;
    bool ok = false;

    while (!s.failed() && now_ms_mono() < deadline) {
        uint64_t now = now_ms_mono();

        if (!s.authenticated()) {
            if (s.last_progress() > seen_progress) { /* link advanced: reset backoff */
                stall_ms = kStallBaseMs;
                seen_progress = s.last_progress();
            }
            if (now - s.last_progress() > stall_ms) {
                out.clear();
                s.reset(now, out);
                for (auto &dg : out) t.send(dg);
                stall_ms = stall_ms * 2 > kStallMaxMs ? kStallMaxMs : stall_ms * 2;
                seen_progress = s.last_progress(); /* reset() bumps progress; ignore it */
            }
        }

        out.clear();
        s.poll(now, out);
        bool work = !out.empty();
        for (auto &dg : out) t.send(dg);

        std::string in;
        if (t.recv(in, 20)) {
            work = true;
            out.clear();
            s.on_datagram(in, now, out);
            for (auto &dg : out) t.send(dg);
        }

        /* Quiesced: peer authenticated, reconcile started, link drained, and no
         * activity for a while. We never settle before the peer's identity is
         * verified (authenticated() stays false until then), so an
         * unauthenticated peer cannot complete a sync. */
        bool settled = s.authenticated() && s.idle();
        if (!work && settled) {
            if (++quiet > 5) { ok = true; break; }
        } else {
            quiet = 0;
        }
    }

    return ok && !s.failed();
}

ConnResult ConnectionManager::sync_with(const uint8_t peer_pk[32],
                                        bool initiator, const Endpoint *direct_ep,
                                        int direct_ms, int relay_ms) {
    if (direct_ep) {
        DirectTransport t;
        t.sock = sock;
        t.peer = *direct_ep;
        if (connect_and_sync(engine, t, initiator, direct_ms))
            return ConnResult::Direct;
    }
    if (have_relay) {
        RelayTransport t;
        t.sock = sock;
        t.relay = relay;
        std::memcpy(t.peer_pk.data(), peer_pk, SYNC_PUBKEY_LEN);
        t.my_pk = my_pk;
        if (connect_and_sync(engine, t, initiator, relay_ms))
            return ConnResult::Relay;
    }
    return ConnResult::Failed;
}

} // namespace ke
