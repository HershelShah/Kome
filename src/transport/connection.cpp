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
    bool kicked = false;

    auto kick = [&]() {
        if (kicked) return;
        kicked = true;
        sess = sync_session_begin(e, 1);
        uint8_t *o = nullptr; size_t ol = 0; int d = 0;
        sync_session_step(sess, nullptr, 0, &o, &ol, &d);
        if (ol) {
            std::string ct;
            chan.encrypt(std::string((char *)o, ol), ct);
            link.send(ct);
        }
        if (o) sync_free(o);
    };

    if (initiator) {
        std::string out;
        bool done = false;
        chan.step("", out, done);
        link.send(out);
    }

    uint64_t deadline = now_ms_mono() + (uint64_t)total_timeout_ms;
    int quiet = 0;
    bool ok = false;

    while (now_ms_mono() < deadline) {
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
                    chan.step(msg, out, done);
                    if (!out.empty()) link.send(out);
                    if (chan.done() && initiator) kick();
                } else {
                    if (!sess) sess = sync_session_begin(e, 0);
                    std::string pt;
                    if (!chan.decrypt(msg, pt)) continue;
                    uint8_t *o = nullptr; size_t ol = 0; int d = 0;
                    sync_session_step(sess, (const uint8_t *)pt.data(),
                                      pt.size(), &o, &ol, &d);
                    if (ol) {
                        std::string ct;
                        chan.encrypt(std::string((char *)o, ol), ct);
                        link.send(ct);
                    }
                    if (o) sync_free(o);
                }
            }
        }

        /* Quiesced: handshake done, reconcile started, link drained, and no
         * activity for a while. (On a reliable localhost link, a lull only
         * happens once the exchange is complete; a lost message keeps the link
         * non-idle, so we won't settle mid-protocol.) */
        bool settled = chan.done() && sess != nullptr && link.idle();
        if (!work && settled) {
            if (++quiet > 5) { ok = true; break; }
        } else {
            quiet = 0;
        }
    }

    if (sess) sync_session_end(sess);
    return ok;
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
        std::memcpy(t.peer_pk.data(), peer_pk, 32);
        t.my_pk = my_pk;
        if (connect_and_sync(engine, t, initiator, relay_ms))
            return ConnResult::Relay;
    }
    return ConnResult::Failed;
}

} // namespace ke
