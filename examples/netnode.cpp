/* netnode.cpp — a real, deployable node for cross-host / real-network testing.
 *
 * Unlike node.cpp / meshnode.cpp (localhost demos that hand-roll the channel),
 * this drives the *production* path: connect_and_sync (Noise XX + transcript-
 * bound identity proof + capability-scoped reconcile + authenticated reliability)
 * and, for NATed peers, ConnectionManager (rendezvous discovery -> direct hole
 * punch -> relay fallback). Use it on two real hosts to validate M5.
 *
 *   # Direct (same LAN / known address); run on both, pointed at each other:
 *   netnode --db a.db --seed 1 --bind 0.0.0.0 --port 7001 \
 *           --role initiator --peer 192.168.1.20:7002
 *
 *   # NAT-traversed (needs a public relayd + rendezvousd):
 *   netnode --db a.db --seed 1 --port 0 --role initiator \
 *           --rendezvous RELAY_HOST:9002 --relay RELAY_HOST:9001 \
 *           --peer-key <64-hex peer signing key>
 *
 * Print this node's own key with --print-key to share it with the peer.
 */
#include "sync_engine.h"

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>

#include "engine.hpp"
#include "transport/connection.h"
#include "transport/rendezvous.h"
#include "transport/udp.h"

using namespace ke;

static const uint8_t *B(const std::string &s) { return (const uint8_t *)s.data(); }

static void hex(const uint8_t *p, size_t n) {
    for (size_t i = 0; i < n; i++) printf("%02x", p[i]);
}

/* Parse "ip:port" (IPv4 or [v6]:port not handled here — IPv4/hostname:port). */
static bool parse_ep(const std::string &s, Endpoint &ep) {
    auto c = s.rfind(':');
    if (c == std::string::npos) return false;
    ep.ip = s.substr(0, c);
    ep.port = (uint16_t)atoi(s.substr(c + 1).c_str());
    return ep.port != 0 && !ep.ip.empty();
}

/* 64 hex chars -> 32 bytes. */
static bool parse_key(const std::string &s, uint8_t out[32]) {
    if (s.size() != 64) return false;
    for (int i = 0; i < 32; i++) {
        unsigned v;
        if (sscanf(s.c_str() + i * 2, "%2x", &v) != 1) return false;
        out[i] = (uint8_t)v;
    }
    return true;
}

int main(int argc, char **argv) {
    std::string db, bind = "0.0.0.0", role, peer_s, rdv_s, relay_s, peer_key_s;
    uint8_t seed_v = 0;
    uint16_t port = 0;
    bool print_key = false;
    for (int i = 1; i < argc; i++) {
        std::string k = argv[i];
        auto v = [&]() { return std::string(argv[++i]); };
        if (k == "--db") db = v();
        else if (k == "--seed") seed_v = (uint8_t)atoi(v().c_str());
        else if (k == "--bind") bind = v();
        else if (k == "--port") port = (uint16_t)atoi(v().c_str());
        else if (k == "--role") role = v();
        else if (k == "--peer") peer_s = v();           /* direct mode */
        else if (k == "--rendezvous") rdv_s = v();        /* managed mode */
        else if (k == "--relay") relay_s = v();
        else if (k == "--peer-key") peer_key_s = v();
        else if (k == "--print-key") print_key = true;
    }
    bool initiator = (role == "initiator");

    uint8_t seed[SYNC_SEED_LEN];
    memset(seed, seed_v, sizeof seed);
    sync_engine *e = db.empty() ? sync_engine_create(seed)
                                : sync_engine_open(db.c_str(), seed);
    if (!e) { fprintf(stderr, "engine open failed\n"); return 1; }

    uint8_t id[SYNC_PUBKEY_LEN];
    sync_engine_identity(e, id);
    if (print_key) { hex(id, 32); printf("\n"); sync_engine_destroy(e); return 0; }
    printf("node key: "); hex(id, 32); printf("\n");

    /* A couple of local records so convergence is observable. */
    std::string ns = "contacts", tag = initiator ? "A" : "B";
    for (int i = 0; i < 3; i++) {
        std::string ent = tag + "-" + std::to_string(i);
        std::string val = "owned-by-" + tag;
        sync_engine_set(e, B(ns), ns.size(), B(ent), ent.size(),
                        B(std::string("name")), 4, B(val), val.size());
    }
    uint8_t d0[SYNC_DIGEST_LEN];
    sync_engine_digest(e, d0);
    printf("before sync: digest="); hex(d0, 8); printf("...\n");
    fflush(stdout);

    UdpSocket sock;
    if (!sock.open(bind.c_str(), port)) {
        fprintf(stderr, "bind %s:%u failed\n", bind.c_str(), port);
        return 1;
    }
    printf("listening on udp/%u\n", sock.local().port);
    fflush(stdout);

    bool ok = false;
    if (!peer_s.empty()) {
        /* Direct: secure reconcile straight to a known endpoint. */
        Endpoint peer;
        if (!parse_ep(peer_s, peer)) { fprintf(stderr, "bad --peer\n"); return 1; }
        DirectTransport t;
        t.sock = &sock;
        t.peer = peer;
        ok = connect_and_sync(e, t, initiator, 20000);
        printf("direct sync: %s\n", ok ? "converged" : "failed/timeout");
    } else if (!relay_s.empty() || !rdv_s.empty()) {
        /* Managed: discover via rendezvous, then direct-punch -> relay fallback. */
        uint8_t peer_pk[32];
        if (!parse_key(peer_key_s, peer_pk)) {
            fprintf(stderr, "managed mode needs --peer-key <64 hex>\n");
            return 1;
        }
        ConnectionManager mgr;
        mgr.engine = e;
        mgr.sock = &sock;
        sync_engine_identity(e, mgr.my_pk.data());
        Endpoint relay_ep;
        if (!relay_s.empty() && parse_ep(relay_s, relay_ep)) {
            mgr.have_relay = true;
            mgr.relay = relay_ep;
        }
        Endpoint peer_ep;
        bool have_direct = false;
        if (!rdv_s.empty()) {
            Endpoint rdv;
            if (parse_ep(rdv_s, rdv)) {
                rendezvous_register(sock, rdv, e->identity, 2000);
                have_direct = rendezvous_lookup(sock, rdv, peer_pk, peer_ep, 3000);
                if (have_direct)
                    printf("rendezvous: peer at %s:%u\n", peer_ep.ip.c_str(),
                           peer_ep.port);
            }
        }
        ConnResult r = mgr.sync_with(peer_pk, initiator,
                                     have_direct ? &peer_ep : nullptr, 8000, 12000);
        const char *how = r == ConnResult::Direct  ? "direct"
                          : r == ConnResult::Relay  ? "relay"
                                                    : "failed";
        ok = (r != ConnResult::Failed);
        printf("managed sync: %s\n", how);
    } else {
        fprintf(stderr, "need --peer (direct) or --relay/--rendezvous (managed)\n");
        return 1;
    }

    uint8_t d1[SYNC_DIGEST_LEN];
    sync_engine_digest(e, d1);
    printf("after sync:  digest="); hex(d1, 8); printf("...\n");

    sync_change *recs = nullptr;
    size_t n = 0;
    sync_engine_export(e, &recs, &n);
    int regs = 0;
    for (size_t i = 0; i < n; i++)
        if (recs[i].kind == SYNC_CHANGE_REGISTER) regs++;
    sync_changes_free(recs, n);
    printf("records known: %d\n", regs);

    sync_engine_destroy(e);
    return ok ? 0 : 2;
}
