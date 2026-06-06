/* node.cpp — a real end-to-end node for the two-process demo.
 *
 * Combines the whole stack: a durable SQLite-backed engine, a Noise XX
 * encrypted channel, the reliability layer, and the range-reconciliation
 * session, over real UDP. Two instances (initiator + responder) on localhost
 * create data independently, connect, and converge over the encrypted channel.
 *
 * This is a demo/example; it reaches into internal headers on purpose. */
#include "sync_engine.h"

#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

#include "engine.hpp"               /* engine identity for the Noise channel */
#include "noise.h"
#include "transport/reliable.h"
#include "transport/udp.h"

using namespace ke;

static uint64_t wall_ms() {
    using namespace std::chrono;
    return (uint64_t)duration_cast<milliseconds>(
               steady_clock::now().time_since_epoch())
        .count();
}

static const uint8_t *B(const std::string &s) {
    return (const uint8_t *)s.data();
}

static void hex(const uint8_t *p, size_t n) {
    for (size_t i = 0; i < n; i++) printf("%02x", p[i]);
}

struct Args {
    std::string db, role;
    uint8_t seed = 0;
    uint16_t listen = 0, peer = 0;
};

int main(int argc, char **argv) {
    Args a;
    for (int i = 1; i < argc; i++) {
        std::string k = argv[i];
        auto val = [&]() { return std::string(argv[++i]); };
        if (k == "--db") a.db = val();
        else if (k == "--role") a.role = val();
        else if (k == "--seed") a.seed = (uint8_t)atoi(val().c_str());
        else if (k == "--listen") a.listen = (uint16_t)atoi(val().c_str());
        else if (k == "--peer") a.peer = (uint16_t)atoi(val().c_str());
    }
    bool initiator = (a.role == "initiator");
    const char *tag = initiator ? "A" : "B";

    /* Durable, offline-first engine. */
    uint8_t seed[SYNC_SEED_LEN];
    memset(seed, a.seed, sizeof seed);
    sync_engine *e = sync_engine_open(a.db.c_str(), seed);
    if (!e) { fprintf(stderr, "[%s] open failed\n", tag); return 1; }

    /* Write some local data *before* connecting (offline). */
    std::string ns = "contacts";
    for (int i = 0; i < 3; i++) {
        std::string ent = std::string(tag) + "-" + std::to_string(i);
        std::string val = std::string("owned-by-") + tag + "-" + std::to_string(i);
        sync_engine_set(e, B(ns), ns.size(), B(ent), ent.size(),
                        B(std::string("name")), 4, B(val), val.size());
    }

    uint8_t dig0[SYNC_DIGEST_LEN];
    sync_engine_digest(e, dig0);
    printf("[%s] before sync: digest=", tag);
    hex(dig0, 8);
    printf("...  (wrote 3 local records)\n");
    fflush(stdout);

    /* Network + crypto + reliability. */
    UdpSocket sock;
    if (!sock.open("127.0.0.1", a.listen)) {
        fprintf(stderr, "[%s] bind %u failed\n", tag, a.listen);
        return 1;
    }
    Endpoint peer{"127.0.0.1", a.peer};
    NoiseChannel chan(initiator, e->identity);
    ReliableLink link;

    sync_session *sess = nullptr;
    bool kicked = false;     /* reconcile session started */
    bool last_empty = false; /* last session reply was empty */

    auto kick_session = [&]() {
        if (kicked || !initiator) return;
        sess = sync_session_begin(e, 1);
        uint8_t *o = nullptr; size_t ol = 0; int d = 0;
        sync_session_step(sess, nullptr, 0, &o, &ol, &d);
        if (ol) {
            std::string ct;
            chan.encrypt(std::string((char *)o, ol), ct);
            link.send(ct);
        }
        if (o) sync_free(o);
        kicked = true;
    };

    /* Initiator opens the handshake. */
    if (initiator) {
        std::string out;
        bool done = false;
        chan.step("", out, done);
        link.send(out);
    }

    uint64_t start = wall_ms();
    int quiet = 0;

    while (wall_ms() - start < 15000) {
        uint64_t now = wall_ms();

        std::vector<std::string> dgs;
        link.poll(dgs, now);
        bool work = !dgs.empty();
        for (auto &d : dgs) sock.send_to(peer, d);

        std::string dg;
        Endpoint from;
        while (sock.recv(dg, from, 10)) {
            work = true;
            std::vector<std::string> delivered;
            link.on_datagram(dg, delivered);
            for (auto &msg : delivered) {
                if (!chan.done()) {
                    std::string out;
                    bool done = false;
                    chan.step(msg, out, done);
                    if (!out.empty()) link.send(out);
                    if (chan.done()) {
                        printf("[%s] noise handshake complete (peer key ",
                               tag);
                        hex(chan.remote_static(), 4);
                        printf("...)\n");
                        fflush(stdout);
                        kick_session();
                    }
                } else {
                    if (!sess) sess = sync_session_begin(e, 0);
                    std::string pt;
                    if (!chan.decrypt(msg, pt)) continue;
                    uint8_t *o = nullptr; size_t ol = 0; int d = 0;
                    sync_session_step(sess, (const uint8_t *)pt.data(),
                                      pt.size(), &o, &ol, &d);
                    last_empty = (ol == 0);
                    if (ol) {
                        std::string ct;
                        chan.encrypt(std::string((char *)o, ol), ct);
                        link.send(ct);
                    }
                    if (o) sync_free(o);
                }
            }
        }

        /* Initiator may complete the handshake without inbound work above. */
        if (chan.done() && initiator && !kicked) kick_session();

        /* Settled once the handshake is done, a session exists and last
         * replied empty, and the reliable link has drained (acks flushed). */
        bool settled = chan.done() && sess != nullptr && link.idle() && last_empty;
        if (!work && settled) {
            if (++quiet > 40) break;
        } else {
            quiet = 0;
        }
    }

    uint8_t dig1[SYNC_DIGEST_LEN];
    sync_engine_digest(e, dig1);
    printf("[%s] after sync:  digest=", tag);
    hex(dig1, 8);
    printf("...\n");

    /* Show what this node now knows (including the peer's records). */
    sync_change *recs = nullptr;
    size_t n = 0;
    sync_engine_export(e, &recs, &n);
    int present = 0;
    for (size_t i = 0; i < n; i++) {
        if (recs[i].kind != SYNC_CHANGE_REGISTER) continue;
        std::string ent((const char *)recs[i].entity, recs[i].entity_len);
        std::string val((const char *)recs[i].value, recs[i].value_len);
        printf("[%s]   %s/name = %s\n", tag, ent.c_str(), val.c_str());
        present++;
    }
    printf("[%s] total records known: %d\n", tag, present);

    sync_changes_free(recs, n);
    if (sess) sync_session_end(sess);
    sync_engine_destroy(e);
    return 0;
}
