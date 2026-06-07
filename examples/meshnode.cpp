/* meshnode.cpp — a real multi-peer gossip daemon for the multi-process demo.
 *
 * One UDP socket, multiple peers. For each peer it maintains a Noise XX channel
 * and periodically runs a fresh range-reconciliation session (re-snapshotting
 * each cycle so data propagates multi-hop across a topology). Launch several of
 * these in a ring/mesh and the whole network converges.
 *
 * Demo/example: reaches into internal transport/crypto headers on purpose. */
#include "sync_engine.h"

#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <map>
#include <sstream>
#include <string>
#include <vector>

#include "engine.hpp"
#include "noise.h"
#include "transport/reliable.h"
#include "transport/udp.h"

using namespace ke;

static uint64_t wall_ms() {
    using namespace std::chrono;
    return (uint64_t)duration_cast<milliseconds>(
               steady_clock::now().time_since_epoch()).count();
}
static const uint8_t *B(const std::string &s) { return (const uint8_t *)s.data(); }

struct Peer {
    Endpoint ep;
    uint16_t port = 0;
    bool initiator = false;
    NoiseChannel *chan = nullptr;
    ReliableLink link;
    sync_session *sess = nullptr;
    bool sess_done = false;   /* responder: produced empty, ready for next cycle */
    uint64_t last_kick = 0;   /* initiator: when we last started a cycle */
    uint64_t last_progress = 0; /* last handshake step / successful decrypt */
};

/* If a peer makes no progress for this long, assume it restarted (fresh Noise
 * + reliability state) and reset our side of the connection to re-handshake. */
static const uint64_t kResetMs = 2000;

int main(int argc, char **argv) {
    std::string db, peers_arg;
    int seed_v = 0, listen = 0, seconds = 6;
    for (int i = 1; i < argc; i++) {
        std::string k = argv[i];
        auto v = [&]() { return std::string(argv[++i]); };
        if (k == "--db") db = v();
        else if (k == "--seed") seed_v = atoi(v().c_str());
        else if (k == "--listen") listen = atoi(v().c_str());
        else if (k == "--peers") peers_arg = v();
        else if (k == "--seconds") seconds = atoi(v().c_str());
    }

    uint8_t seed[SYNC_SEED_LEN];
    memset(seed, seed_v, sizeof seed);
    sync_engine *e = sync_engine_open(db.c_str(), seed);
    if (!e) { fprintf(stderr, "open failed\n"); return 1; }

    /* One local record, tagged by this node's port (so we can see it spread).
     * Write it only once: on restart the durable DB already has it, and
     * re-writing would needlessly bump its HLC (churn with no new information). */
    std::string ns = "mesh";
    std::string mine = "node-" + std::to_string(listen);
    int already = 0;
    sync_engine_exists(e, B(ns), ns.size(), B(mine), mine.size(), &already);
    if (!already)
        sync_engine_set(e, B(ns), ns.size(), B(mine), mine.size(),
                        B(std::string("v")), 1, B(mine), mine.size());

    UdpSocket sock;
    if (!sock.open("127.0.0.1", (uint16_t)listen)) { fprintf(stderr, "bind\n"); return 1; }

    std::map<uint16_t, Peer> peers;
    std::stringstream ss(peers_arg);
    std::string tok;
    while (std::getline(ss, tok, ',')) {
        if (tok.empty()) continue;
        uint16_t p = (uint16_t)atoi(tok.c_str());
        Peer pe;
        pe.port = p;
        pe.ep = Endpoint{"127.0.0.1", p};
        pe.initiator = (uint16_t)listen < p; /* lower port initiates */
        pe.chan = new NoiseChannel(pe.initiator, e->identity);
        peers[p] = std::move(pe);
    }

    auto kick = [&](Peer &pr) {
        if (pr.sess) { sync_session_end(pr.sess); pr.sess = nullptr; }
        pr.sess = sync_session_begin(e, 1);
        uint8_t *o = nullptr; size_t ol = 0; int d = 0;
        sync_session_step(pr.sess, nullptr, 0, &o, &ol, &d);
        if (ol) {
            std::string ct;
            pr.chan->encrypt(std::string((char *)o, ol), ct);
            pr.link.send(ct);
        }
        if (o) sync_free(o);
        pr.last_kick = wall_ms();
    };

    /* Reset our side of a peer connection (used when a peer restarts): fresh
     * Noise channel + reliability state, then re-open the handshake. */
    auto reset = [&](Peer &pr) {
        delete pr.chan;
        pr.chan = new NoiseChannel(pr.initiator, e->identity);
        pr.link = ReliableLink();
        if (pr.sess) { sync_session_end(pr.sess); pr.sess = nullptr; }
        pr.sess_done = false;
        pr.last_progress = wall_ms();
        pr.last_kick = 0;
        if (pr.initiator) {
            std::string out; bool done = false;
            pr.chan->step("", out, done);
            pr.link.send(out);
        }
    };

    /* Initiators open handshakes. */
    for (auto &kv : peers)
        if (kv.second.initiator) {
            std::string out; bool done = false;
            kv.second.chan->step("", out, done);
            kv.second.link.send(out);
        }

    uint64_t start = wall_ms();
    for (auto &kv : peers) kv.second.last_progress = start;
    while (wall_ms() - start < (uint64_t)seconds * 1000) {
        uint64_t now = wall_ms();

        for (auto &kv : peers) {
            Peer &pr = kv.second;
            /* No genuine progress (delivered msg or valid ack) for a while ->
             * the peer is silent or restarted; re-handshake. Healthy idle
             * connections still progress: the initiator's periodic FP is acked
             * and the responder decrypts it, so last_progress stays fresh. */
            if (now - pr.last_progress > kResetMs) reset(pr);
            std::vector<std::string> dgs;
            pr.link.poll(dgs, now);
            for (auto &d : dgs) sock.send_to(pr.ep, d);
            /* Initiator: start a fresh gossip cycle periodically once idle. */
            if (pr.initiator && pr.chan->done() && pr.link.idle() &&
                now - pr.last_kick > 300)
                kick(pr);
        }

        std::string dg;
        Endpoint from;
        while (sock.recv(dg, from, 5)) {
            auto it = peers.find(from.port);
            if (it == peers.end()) continue;
            Peer &pr = it->second;
            std::vector<std::string> delivered;
            if (pr.link.on_datagram(dg, delivered)) pr.last_progress = now;
            for (auto &msg : delivered) {
                if (!pr.chan->done()) {
                    std::string out; bool done = false;
                    if (pr.chan->step(msg, out, done)) pr.last_progress = now;
                    if (!out.empty()) pr.link.send(out);
                    if (pr.chan->done() && pr.initiator) kick(pr);
                } else {
                    /* Responder starts a fresh session each cycle to
                     * re-snapshot (so newly-learned data propagates onward). */
                    if (!pr.initiator && (!pr.sess || pr.sess_done)) {
                        if (pr.sess) sync_session_end(pr.sess);
                        pr.sess = sync_session_begin(e, 0);
                        pr.sess_done = false;
                    }
                    if (!pr.sess) pr.sess = sync_session_begin(e, 0);
                    std::string pt;
                    if (!pr.chan->decrypt(msg, pt)) continue;
                    pr.last_progress = now;
                    uint8_t *o = nullptr; size_t ol = 0; int d = 0;
                    sync_session_step(pr.sess, (const uint8_t *)pt.data(),
                                      pt.size(), &o, &ol, &d);
                    if (ol == 0) pr.sess_done = true;
                    if (ol) {
                        std::string ct;
                        pr.chan->encrypt(std::string((char *)o, ol), ct);
                        pr.link.send(ct);
                    }
                    if (o) sync_free(o);
                }
            }
        }
    }

    /* Report: how many of the network's records did this node learn? */
    uint8_t dig[SYNC_DIGEST_LEN];
    sync_engine_digest(e, dig);
    sync_change *recs = nullptr; size_t n = 0;
    sync_engine_export(e, &recs, &n);
    int known = 0;
    for (size_t i = 0; i < n; i++)
        if (recs[i].kind == SYNC_CHANGE_REGISTER) known++;
    sync_changes_free(recs, n);

    printf("[node %d] knows %d records (%d direct peers)  digest=%02x%02x%02x%02x\n",
           listen, known, (int)peers.size(), dig[0], dig[1], dig[2], dig[3]);

    for (auto &kv : peers)
        if (kv.second.sess) sync_session_end(kv.second.sess);
    for (auto &kv : peers) delete kv.second.chan;
    sync_engine_destroy(e);
    return 0;
}
