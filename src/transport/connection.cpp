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

/* Begin a fresh, re-snapshotted reconcile cycle (read-scoped to the
 * authenticated peer) and send its first message. */
void SecurePeerSession::kick_(uint64_t now) {
    if (sess_) { sync_session_end(sess_); sess_ = nullptr; }
    sess_ = sync_session_begin_scoped(e_, initiator_ ? 1 : 0, peer_pk_.data());
    sess_done_ = false;
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
                sess_ = sync_session_begin_scoped(e_, initiator_ ? 1 : 0,
                                                  peer_pk_.data());
                sess_done_ = false;
                if (initiator_) { pump_(nullptr, 0); last_kick_ = now_mono; }
            } else {
                /* Gossip mode: the responder re-snapshots at the start of each
                 * new cycle so newly-learned data propagates onward. */
                if (interval_ > 0 && !initiator_ && (!sess_ || sess_done_)) {
                    if (sess_) sync_session_end(sess_);
                    sess_ = sync_session_begin_scoped(e_, 0, peer_pk_.data());
                    sess_done_ = false;
                }
                bool emitted = pump_((const uint8_t *)pt.data(), pt.size());
                if (interval_ > 0 && !emitted) sess_done_ = true;
            }
        }
    }
    drain_(now_mono, out);
}

void SecurePeerSession::poll(uint64_t now_mono, std::vector<std::string> &out) {
    drain_(now_mono, out);
    /* Gossip mode: the initiator starts a fresh cycle once the previous settled
     * and the interval has elapsed. */
    if (interval_ > 0 && initiator_ && peer_ok_ && chan_->done() &&
        link_.idle() && now_mono - last_kick_ > interval_) {
        kick_(now_mono);
        drain_(now_mono, out);
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
    int quiet = 0;
    bool ok = false;

    while (!s.failed() && now_ms_mono() < deadline) {
        uint64_t now = now_ms_mono();

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
