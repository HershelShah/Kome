/* tcp_relay_probe.cpp — tiny signed TCP-relay client for the shell e2e
 * (tests/tcp_relayd_test.sh). Not a general-purpose tool: exactly the ops
 * the shell test needs. One process per invocation, so "disjoint client
 * lifetimes" falls out of just running it twice; seed-derived mailbox keys
 * let the shell script reproduce the same mailbox_pk across invocations by
 * re-passing the same --mailbox-seed.
 *
 *   tcp_relay_probe --host H --port P --mailbox-seed <64 hex chars>
 *                    --op hello|post|fetch|register
 *                    [--ctr N] [--blob TEXT] [--since N]
 *                    [--provider N] [--handle TEXT] [--wrong-key]
 *
 * Prints one line to stdout per reply:
 *   hello:       "HELLO <server_pk hex> <nonce hex>"
 *   post ok:     "OK POST seq=<n>"
 *   fetch ok:    "OK FETCH n=<count> evicted_up_to=<n>", then one
 *                "REC seq=<n> blob=<hex>" line per fetched record
 *   register ok: "OK REGISTER"
 *   any ERR reply: "ERR <code>"
 * Exit 0 whenever a server reply was received (OK or ERR — the caller
 * inspects stdout to tell them apart); exit 1 on a transport-level failure
 * (connect/HELLO/timeout/malformed reply); exit 2 on bad arguments.
 *
 * --wrong-key signs with a different keypair than the claimed mailbox_pk (a
 * forged-signature rejection drill) while still presenting the real
 * mailbox_pk, so the server's ERR 2 is against a genuine wrong-secret
 * forgery, not just a different mailbox. */
#include "transport/tcp_relay.h"

#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>

#include "codec.h" /* ke::put_varint / ke::get_varint */
#include "crypto.h"
#include "transport/tcp.h"
#include "transport/udp.h" /* Endpoint */

using namespace ke;

namespace {

bool parse_hex32(const std::string &s, uint8_t out[32]) {
    if (s.size() != 64) return false;
    for (int i = 0; i < 32; i++) {
        char c0 = s[i * 2], c1 = s[i * 2 + 1];
        if (!isxdigit((unsigned char)c0) || !isxdigit((unsigned char)c1)) return false;
        unsigned v;
        if (sscanf(s.c_str() + i * 2, "%2x", &v) != 1) return false;
        out[i] = (uint8_t)v;
    }
    return true;
}

std::string hexstr(const uint8_t *p, size_t n) {
    static const char *d = "0123456789abcdef";
    std::string out;
    out.reserve(n * 2);
    for (size_t i = 0; i < n; i++) {
        out.push_back(d[p[i] >> 4]);
        out.push_back(d[p[i] & 0xf]);
    }
    return out;
}

std::string hexstr(const std::string &s) { return hexstr((const uint8_t *)s.data(), s.size()); }

} // namespace

int main(int argc, char **argv) {
    std::string host = "127.0.0.1", op, blob, handle, mailbox_seed_hex;
    int port = -1;
    uint64_t ctr = 0, since = 0;
    uint8_t provider = 0;
    bool wrong_key = false;

    for (int i = 1; i < argc; i++) {
        std::string a = argv[i];
        auto need = [&](const char *name) -> std::string {
            if (i + 1 >= argc) {
                fprintf(stderr, "tcp_relay_probe: %s needs a value\n", name);
                exit(2);
            }
            return argv[++i];
        };
        if (a == "--host") host = need("--host");
        else if (a == "--port") port = atoi(need("--port").c_str());
        else if (a == "--mailbox-seed") mailbox_seed_hex = need("--mailbox-seed");
        else if (a == "--op") op = need("--op");
        else if (a == "--ctr") ctr = strtoull(need("--ctr").c_str(), nullptr, 10);
        else if (a == "--blob") blob = need("--blob");
        else if (a == "--since") since = strtoull(need("--since").c_str(), nullptr, 10);
        else if (a == "--provider") provider = (uint8_t)atoi(need("--provider").c_str());
        else if (a == "--handle") handle = need("--handle");
        else if (a == "--wrong-key") wrong_key = true;
        else {
            fprintf(stderr, "tcp_relay_probe: unrecognized argument: %s\n", a.c_str());
            return 2;
        }
    }
    if (port < 0 || mailbox_seed_hex.empty() || op.empty()) {
        fprintf(stderr, "tcp_relay_probe: --port, --mailbox-seed, --op are required\n");
        return 2;
    }
    uint8_t mbseed[32];
    if (!parse_hex32(mailbox_seed_hex, mbseed)) {
        fprintf(stderr, "tcp_relay_probe: --mailbox-seed must be 64 hex chars\n");
        return 2;
    }
    KeyPair mailbox = keypair_from_seed(mbseed);
    KeyPair signer = mailbox;
    if (wrong_key) {
        uint8_t wseed[32];
        for (int i = 0; i < 32; i++) wseed[i] = (uint8_t)(mbseed[i] ^ 0xFF);
        signer = keypair_from_seed(wseed);
    }

    TcpStream s;
    Endpoint ep{host, (uint16_t)port};
    if (!s.connect_to(ep)) {
        fprintf(stderr, "tcp_relay_probe: connect to %s:%d failed\n", host.c_str(), port);
        return 1;
    }
    uint8_t server_pk[32], nonce[16];
    if (!tcp_relay_client_hello(s, server_pk, nonce, 2000)) {
        fprintf(stderr, "tcp_relay_probe: HELLO failed\n");
        return 1;
    }
    if (op == "hello") {
        printf("HELLO %s %s\n", hexstr(server_pk, 32).c_str(), hexstr(nonce, 16).c_str());
        return 0;
    }

    std::string payload;
    uint8_t wire_op = 0;
    if (op == "post") {
        wire_op = (uint8_t)kTcpRelayOpPost;
        payload = blob;
    } else if (op == "fetch") {
        wire_op = (uint8_t)kTcpRelayOpFetch;
        put_varint(payload, since);
    } else if (op == "register") {
        wire_op = (uint8_t)kTcpRelayOpPushReg;
        payload.push_back((char)provider);
        put_varint(payload, handle.size());
        payload += handle;
    } else {
        fprintf(stderr, "tcp_relay_probe: unknown --op %s\n", op.c_str());
        return 2;
    }

    std::string msg =
        tcp_relay_op_transcript(server_pk, nonce, wire_op, mailbox.sign_pk.data(), ctr, payload);
    uint8_t sig[64];
    sign(signer.sign_sk.data(), msg.data(), msg.size(), sig);
    std::string frame =
        tcp_relay_build_op_frame(wire_op, mailbox.sign_pk.data(), ctr, payload, sig);
    if (!s.send_frame(frame)) {
        fprintf(stderr, "tcp_relay_probe: send failed\n");
        return 1;
    }
    std::string reply;
    if (!s.recv_frame(reply, 2000)) {
        fprintf(stderr, "tcp_relay_probe: no reply\n");
        return 1;
    }
    if (reply.size() == 2 && reply[0] == kTcpRelayOpErr) {
        printf("ERR %u\n", (unsigned)(uint8_t)reply[1]);
        return 0;
    }

    if (op == "post") {
        if (reply.size() < 2 || reply[0] != kTcpRelayOpOk) {
            fprintf(stderr, "tcp_relay_probe: bad POST reply\n");
            return 1;
        }
        const uint8_t *p = (const uint8_t *)reply.data() + 1;
        const uint8_t *end = (const uint8_t *)reply.data() + reply.size();
        uint64_t seq = 0;
        if (!get_varint(p, end, seq)) { fprintf(stderr, "tcp_relay_probe: bad OK detail\n"); return 1; }
        printf("OK POST seq=%llu\n", (unsigned long long)seq);
    } else if (op == "fetch") {
        if (reply.empty() || reply[0] != kTcpRelayOpDeliver) {
            fprintf(stderr, "tcp_relay_probe: bad FETCH reply\n");
            return 1;
        }
        const uint8_t *p = (const uint8_t *)reply.data() + 1;
        const uint8_t *end = (const uint8_t *)reply.data() + reply.size();
        uint64_t evicted_up_to = 0, n = 0;
        if (!get_varint(p, end, evicted_up_to) || !get_varint(p, end, n)) {
            fprintf(stderr, "tcp_relay_probe: malformed DELIVER header\n");
            return 1;
        }
        printf("OK FETCH n=%llu evicted_up_to=%llu\n", (unsigned long long)n,
               (unsigned long long)evicted_up_to);
        for (uint64_t i = 0; i < n; i++) {
            uint64_t seq = 0, len = 0;
            if (!get_varint(p, end, seq) || !get_varint(p, end, len) ||
                (uint64_t)(end - p) < len) {
                fprintf(stderr, "tcp_relay_probe: malformed DELIVER record %llu\n",
                        (unsigned long long)i);
                return 1;
            }
            std::string rec((const char *)p, (size_t)len);
            p += len;
            printf("REC seq=%llu blob=%s\n", (unsigned long long)seq, hexstr(rec).c_str());
        }
    } else { /* register */
        if (reply.size() < 1 || reply[0] != kTcpRelayOpOk) {
            fprintf(stderr, "tcp_relay_probe: bad REGISTER reply\n");
            return 1;
        }
        printf("OK REGISTER\n");
    }
    return 0;
}
