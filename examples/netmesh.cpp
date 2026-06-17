/* netmesh.cpp — a secure multi-peer mesh daemon for real-network scale testing.
 *
 * The real-network counterpart to meshnode (which is localhost-only and skips
 * the production security). netmesh drives the *secure* path — a Noise XX
 * handshake, the transcript-bound identity proof, and capability-scoped range
 * reconciliation (SecurePeerSession) — to several peers at once over one UDP
 * socket, gossiping each link periodically so newly-learned data propagates
 * multi-hop. Run several of these across machines on a flat reachable substrate
 * (Tailscale tailnet, cloud VMs, or a LAN) and the whole mesh converges.
 *
 *   # print this node's key to share with peers:
 *   netmesh --seed 1 --print-key
 *
 *   # run a node, listing each neighbour as ip:port=<64-hex-key>:
 *   netmesh --db a.db --seed 1 --port 7001 --seconds 20 \
 *           --peers 10.0.0.2:7002=<keyB>,10.0.0.3:7003=<keyC>
 *
 * Endpoint demux: inbound datagrams are matched to a peer by sender address, so
 * a peer must send from the ip:port it is configured as. That holds on a flat
 * reachable network (no NAT rewriting between peers); NAT traversal (hole-punch
 * /relay) is validated pairwise by netnode, not here. IPv4 literals only (the
 * engine is IPv4-only). */
#include "sync_engine.h"

#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <map>
#include <memory>
#include <sstream>
#include <string>
#include <vector>

#include "engine.hpp"
#include "transport/connection.h"
#include "transport/udp.h"

using namespace ke;

static const uint8_t *B(const std::string &s) { return (const uint8_t *)s.data(); }

static uint64_t wall_ms() {
    using namespace std::chrono;
    return (uint64_t)duration_cast<milliseconds>(
               steady_clock::now().time_since_epoch()).count();
}

static void hex(const uint8_t *p, size_t n) {
    for (size_t i = 0; i < n; i++) printf("%02x", p[i]);
}

/* Parse "ip:port" (IPv4 literal:port; no [v6] or hostname). */
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

/* If a peer makes no progress for this long, assume it is silent or restarted
 * and reset our side to re-handshake (matches meshnode's kResetMs). */
static const uint64_t kResetMs = 2000;

struct Peer {
    Endpoint                           ep;
    std::string                        key; /* "ip:port" for inbound demux */
    std::unique_ptr<SecurePeerSession> sps;
};

int main(int argc, char **argv) {
    std::string db, bind = "0.0.0.0", peers_arg, write_key, key_hex;
    int seed_v = 0, seconds = 8, interval = 300;
    int write_interval = 0, delete_interval = 0; /* test drivers (0 = off) */
    int write_for = 0; /* stop writing after N s (then drain/gossip); 0 = whole run */
    uint16_t port = 0;
    bool print_key = false, daemon = false;
    for (int i = 1; i < argc; i++) {
        std::string k = argv[i];
        auto v = [&]() { return std::string(argv[++i]); };
        if (k == "--db") db = v();
        else if (k == "--seed") seed_v = atoi(v().c_str());
        else if (k == "--bind") bind = v();
        else if (k == "--port") port = (uint16_t)atoi(v().c_str());
        else if (k == "--peers") peers_arg = v();
        else if (k == "--seconds") seconds = atoi(v().c_str());
        else if (k == "--interval") interval = atoi(v().c_str());
        else if (k == "--daemon") daemon = true;
        else if (k == "--print-key") print_key = true;
        /* --- test drivers --- */
        else if (k == "--write-interval") write_interval = atoi(v().c_str());
        else if (k == "--write-key") write_key = v();   /* shared key => LWW conflict */
        else if (k == "--delete-interval") delete_interval = atoi(v().c_str());
        else if (k == "--write-for") write_for = atoi(v().c_str());
        else if (k == "--key") key_hex = v();           /* hex => at-rest encryption */
    }
    if (seconds == 0) daemon = true;

    uint8_t seed[SYNC_SEED_LEN];
    memset(seed, (uint8_t)seed_v, sizeof seed);
    sync_engine *e;
    if (!key_hex.empty()) {
        uint8_t key[32];
        if (db.empty() || !parse_key(key_hex, key)) {
            fprintf(stderr, "--key needs 64 hex chars and a --db path\n");
            return 1;
        }
        e = sync_engine_open_encrypted(db.c_str(), seed, key);
    } else {
        e = db.empty() ? sync_engine_create(seed) : sync_engine_open(db.c_str(), seed);
    }
    if (!e) { fprintf(stderr, "engine open failed (wrong key/mode?)\n"); return 1; }

    uint8_t my_pk[SYNC_PUBKEY_LEN];
    sync_engine_identity(e, my_pk);
    if (print_key) { hex(my_pk, 32); printf("\n"); sync_engine_destroy(e); return 0; }
    printf("node key: "); hex(my_pk, 32); printf("\n");

    /* One local record, tagged by this node, written once (the durable DB keeps
     * it across restarts; re-writing would needlessly bump its HLC). */
    std::string ns = "mesh", mine = "node-" + std::to_string(port);
    int already = 0;
    sync_engine_exists(e, B(ns), ns.size(), B(mine), mine.size(), &already);
    if (!already)
        sync_engine_set(e, B(ns), ns.size(), B(mine), mine.size(),
                        B(std::string("v")), 1, B(mine), mine.size());

    UdpSocket sock;
    if (!sock.open(bind.c_str(), port)) {
        fprintf(stderr, "bind %s:%u failed\n", bind.c_str(), port);
        sync_engine_destroy(e);
        return 1;
    }
    printf("listening on udp/%u\n", sock.local().port);
    fflush(stdout);

    /* Parse peers: "ip:port=hexkey,ip:port=hexkey,...". Initiator is decided by
     * identity-key compare (strict order => exactly one initiator per edge). */
    std::vector<std::unique_ptr<Peer>> peers;
    std::map<std::string, Peer *> by_addr;
    std::stringstream ss(peers_arg);
    std::string tok;
    while (std::getline(ss, tok, ',')) {
        if (tok.empty()) continue;
        auto eq = tok.rfind('=');
        if (eq == std::string::npos) { fprintf(stderr, "bad --peers entry: %s\n", tok.c_str()); return 1; }
        Endpoint ep;
        uint8_t peer_pk[32];
        if (!parse_ep(tok.substr(0, eq), ep) || !parse_key(tok.substr(eq + 1), peer_pk)) {
            fprintf(stderr, "bad --peers entry: %s\n", tok.c_str());
            return 1;
        }
        bool initiator = std::memcmp(my_pk, peer_pk, 32) < 0;
        auto p = std::make_unique<Peer>();
        p->ep = ep;
        p->key = ep.ip + ":" + std::to_string(ep.port);
        p->sps = std::make_unique<SecurePeerSession>(e, initiator, (uint32_t)interval);
        by_addr[p->key] = p.get();
        peers.push_back(std::move(p));
    }

    uint8_t d0[SYNC_DIGEST_LEN];
    sync_engine_digest(e, d0);
    printf("before sync: digest="); hex(d0, 4); printf("...  (%d peers)\n", (int)peers.size());
    fflush(stdout);

    auto send_out = [&](Peer &p, std::vector<std::string> &out) {
        for (auto &dg : out) sock.send_to(p.ep, dg);
        out.clear();
    };

    uint64_t start = wall_ms();
    std::vector<std::string> out;
    for (auto &p : peers) { p->sps->start(start, out); send_out(*p, out); }

    uint64_t last_status = start, last_write = start, last_delete = start;
    int wcounter = 0;
    std::vector<std::string> created;   /* entities we created (for --delete-interval) */
    size_t del_idx = 0;
    std::string lns = "load";
    while (daemon || wall_ms() - start < (uint64_t)seconds * 1000) {
        uint64_t now = wall_ms();

        for (auto &p : peers) {
            if (now - p->sps->last_progress() > kResetMs) {
                p->sps->reset(now, out);
                send_out(*p, out);
            }
            p->sps->poll(now, out);
            send_out(*p, out);
        }

        std::string dg;
        Endpoint from;
        while (sock.recv(dg, from, 5)) {
            auto it = by_addr.find(from.ip + ":" + std::to_string(from.port));
            if (it == by_addr.end()) continue; /* not a configured peer */
            it->second->sps->on_datagram(dg, now, out);
            send_out(*it->second, out);
        }

        /* --- test drivers: synthetic write/delete load --- */
        bool writing = write_for == 0 || now - start < (uint64_t)write_for * 1000;
        if (writing && write_interval > 0 && now - last_write >= (uint64_t)write_interval) {
            std::string ent, val = std::to_string(port) + "-" + std::to_string(wcounter);
            if (!write_key.empty()) {
                ent = write_key; /* both nodes hammer one key => LWW conflict */
            } else {
                ent = "w-" + std::to_string(port) + "-" + std::to_string(wcounter);
                created.push_back(ent);
            }
            sync_engine_set(e, B(lns), lns.size(), B(ent), ent.size(),
                            B(std::string("v")), 1, B(val), val.size());
            wcounter++;
            last_write = now;
        }
        if (writing && delete_interval > 0 &&
            now - last_delete >= (uint64_t)delete_interval && del_idx < created.size()) {
            const std::string &ent = created[del_idx++];
            sync_engine_delete(e, B(lns), lns.size(), B(ent), ent.size());
            last_delete = now;
        }

        if (daemon && now - last_status >= 3000) {
            int authed = 0;
            for (auto &p : peers) if (p->sps->authenticated()) authed++;
            sync_change *recs = nullptr; size_t n = 0;
            sync_engine_export(e, &recs, &n);
            int known = 0;
            for (size_t i = 0; i < n; i++)
                if (recs[i].kind == SYNC_CHANGE_REGISTER) known++;
            sync_changes_free(recs, n);
            uint8_t d[SYNC_DIGEST_LEN];
            sync_engine_digest(e, d);
            printf("[status] knows %d records, %d/%d peers authed, digest=",
                   known, authed, (int)peers.size());
            hex(d, 4); printf("...\n");
            fflush(stdout);
            last_status = now;
        }
    }

    uint8_t d1[SYNC_DIGEST_LEN];
    sync_engine_digest(e, d1);
    sync_change *recs = nullptr; size_t n = 0;
    sync_engine_export(e, &recs, &n);
    int known = 0;
    for (size_t i = 0; i < n; i++)
        if (recs[i].kind == SYNC_CHANGE_REGISTER) known++;
    sync_changes_free(recs, n);

    /* Report line (meshnode-format) for tools/netmesh_verify.sh. */
    printf("[node %u] knows %d records (%d peers)  digest=%02x%02x%02x%02x\n",
           sock.local().port, known, (int)peers.size(), d1[0], d1[1], d1[2], d1[3]);

    peers.clear(); /* free sessions (and their sync_session*) before the engine */
    sync_engine_destroy(e);
    return 0;
}
