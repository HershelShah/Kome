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

bool connect_and_sync(sync_engine *e, PeerTransport &t, bool initiator,
                      int total_timeout_ms) {
    NoiseChannel chan(initiator, e->identity);
    ReliableLink link;
    sync_session *sess = nullptr;
    bool proof_sent = false;   /* our signed identity proof sent (once) */
    bool peer_ok = false;      /* peer's identity proof verified */
    uint8_t peer_pk[SYNC_PUBKEY_LEN]{};

    /* Step the reconcile session with in[0,in_len) and, if it produced a reply,
     * encrypt it onto the reliable link. (sync_free(nullptr) is a no-op.) */
    auto pump = [&](const uint8_t *in, size_t in_len) {
        if (!sess) return;
        uint8_t *o = nullptr; size_t ol = 0; int d = 0;
        sync_session_step(sess, in, in_len, &o, &ol, &d);
        if (ol) {
            std::string ct;
            chan.encrypt(std::string((char *)o, ol), ct);
            link.send(ct);
        }
        sync_free(o);
    };

    /* The Noise XX handshake authenticates only the X25519 static. Bind the
     * channel to our long-term EdDSA identity by signing the unique handshake
     * transcript and sending it as the first post-handshake message (once). */
    auto send_proof = [&]() {
        if (proof_sent || !chan.done()) return;
        std::string proof, ct;
        if (chan.make_identity_proof(proof) && chan.encrypt(proof, ct)) {
            link.send(ct);
            proof_sent = true;
        }
    };

    if (initiator) {
        std::string out;
        bool done = false;
        chan.step("", out, done);
        link.send(out);
    }

    uint64_t deadline = now_ms_mono() + (uint64_t)total_timeout_ms;
    int quiet = 0;
    bool ok = false, failed = false;

    while (!failed && now_ms_mono() < deadline) {
        uint64_t now = now_ms_mono();

        std::vector<std::string> dgs;
        link.poll(dgs, now);
        bool work = !dgs.empty();
        for (auto &dg : dgs) t.send(dg);

        std::string in;
        if (t.recv(in, 20)) {
            work = true;
            std::vector<std::string> delivered;
            link.on_datagram(in, delivered);
            for (auto &msg : delivered) {
                if (!chan.done()) {
                    std::string out;
                    bool done = false;
                    if (!chan.step(msg, out, done)) { failed = true; break; }
                    if (!out.empty()) link.send(out); /* handshake msg: plain */
                    if (chan.done()) {
                        /* Handshake complete: authenticate the reliability layer
                         * from here on (the proof and all reconcile traffic). */
                        uint8_t rk[32];
                        chan.reliability_key(rk);
                        link.enable_mac(rk);
                        send_proof();
                    }
                } else {
                    std::string pt;
                    if (!chan.decrypt(msg, pt)) continue;
                    if (!peer_ok) {
                        /* The first post-handshake message MUST be the peer's
                         * identity proof. A bad/absent proof => MITM, forgery,
                         * or a peer skipping authentication => abort the sync. */
                        if (!chan.verify_identity_proof(pt, peer_pk)) {
                            failed = true;
                            break;
                        }
                        peer_ok = true;
                        /* Reconcile read-scoped to the authenticated peer, so a
                         * peer only receives namespaces it may read. */
                        sess = sync_session_begin_scoped(e, initiator ? 1 : 0,
                                                         peer_pk);
                        if (initiator) pump(nullptr, 0); /* send first FP */
                    } else {
                        pump((const uint8_t *)pt.data(), pt.size());
                    }
                }
            }
        }

        /* Quiesced: peer authenticated, reconcile started, link drained, and no
         * activity for a while. We never settle before the peer's identity is
         * verified (sess stays null until then), so an unauthenticated peer
         * cannot complete a sync. */
        bool settled = peer_ok && sess != nullptr && link.idle();
        if (!work && settled) {
            if (++quiet > 5) { ok = true; break; }
        } else {
            quiet = 0;
        }
    }

    if (sess) sync_session_end(sess);
    return ok && !failed;
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
