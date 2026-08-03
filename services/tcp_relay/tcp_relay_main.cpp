/* tcp_relay_main.cpp — standalone blind store-and-forward TCP relay daemon
 * (tcp-relayd, issue #49).
 *
 *   tcp-relayd --listen 9003 [--retention-hours 168]
 *              [--identity-seed-file <path>] [--dump-frames <path>]
 *
 * Forwards opaque ciphertext blobs over persistent TCP connections, addressed
 * by mailbox public key; never decrypts and never signs a client op (see
 * transport/tcp_relay.h for the structural blindness argument).
 *
 *   --listen               TCP port (default 9003).
 *   --retention-hours      mailbox log TTL (default 168 = 7 days).
 *   --identity-seed-file   32 raw bytes or 64 hex chars deriving the relay's
 *                          static EdDSA public key (server_pk), so clients
 *                          that want to pin a relay see the same key across
 *                          restarts. Only the public half is ever used — the
 *                          relay never signs anything — but a keypair is
 *                          derived deterministically so a fresh process
 *                          reproduces the same server_pk. Omit for a fresh
 *                          ephemeral identity each run (logged on startup).
 *   --dump-frames <path>   test aid, not for production use: appends every
 *                          raw client frame exactly as received (length-
 *                          prefixed, same framing as the wire) to path, so an
 *                          end-to-end test can grep-prove blindness — the
 *                          posted ciphertext appears verbatim and no
 *                          plaintext marker or key material ever does.
 *
 * SIGINT/SIGTERM triggers a clean shutdown (komed's g_stop pattern). */
#include "transport/tcp_relay.h"

#include <cctype>
#include <csignal>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <string>

#include "byteorder.h"
#include "crypto.h"

namespace {

std::string ts() {
    time_t t = time(nullptr);
    struct tm tmv;
    localtime_r(&t, &tmv);
    char buf[32];
    strftime(buf, sizeof buf, "%Y-%m-%d %H:%M:%S", &tmv);
    return std::string(buf);
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

std::string hexstr(const std::string &s) {
    return hexstr((const uint8_t *)s.data(), s.size());
}

volatile sig_atomic_t g_stop = 0;
void on_signal(int) { g_stop = 1; }

void install_signal_handlers() {
    struct sigaction sa;
    memset(&sa, 0, sizeof sa);
    sa.sa_handler = on_signal;
    sigemptyset(&sa.sa_mask);
    sa.sa_flags = 0;
    sigaction(SIGINT, &sa, nullptr);
    sigaction(SIGTERM, &sa, nullptr);
}

/* Logging-only push notifier (§3 of the plan): prints the wake exactly as
 * the interface hands it over — provider + opaque handle, hex-encoded since
 * a handle is untrusted bytes, not necessarily printable. A real APNs/FCM/
 * WebPush gateway implements ke::PushNotifier in its place. */
class LoggingPushNotifier : public ke::PushNotifier {
public:
    void wake(uint8_t provider, const std::string &handle) override {
        fprintf(stdout, "%s tcp-relayd: push wake provider=%u handle=%s\n",
                ts().c_str(), (unsigned)provider, hexstr(handle).c_str());
        fflush(stdout);
    }
};

bool read_file_bytes(const std::string &path, std::string &out) {
    FILE *f = fopen(path.c_str(), "rb");
    if (!f) return false;
    char buf[4096];
    out.clear();
    size_t n;
    while ((n = fread(buf, 1, sizeof buf, f)) > 0) out.append(buf, n);
    bool ok = !ferror(f);
    fclose(f);
    return ok;
}

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

std::string trim(const std::string &s) {
    size_t a = s.find_first_not_of(" \t\r\n");
    if (a == std::string::npos) return "";
    size_t b = s.find_last_not_of(" \t\r\n");
    return s.substr(a, b - a + 1);
}

/* seed_file: 32 raw bytes, or 64 hex chars (optionally trailing newline) —
 * same convention komed's seed_file uses. */
bool load_seed_file(const std::string &path, uint8_t seed[32]) {
    std::string raw;
    if (!read_file_bytes(path, raw)) return false;
    if (raw.size() == 32) {
        memcpy(seed, raw.data(), 32);
        return true;
    }
    std::string trimmed = trim(raw);
    if (trimmed.size() == 64 && parse_hex32(trimmed, seed)) return true;
    return false;
}

} // namespace

int main(int argc, char **argv) {
    int port = 9003;
    uint64_t retention_hours = ke::MailboxLog::kDefaultRetentionHours;
    std::string seed_file, dump_path;

    for (int i = 1; i < argc; i++) {
        std::string a = argv[i];
        if (a == "--listen") {
            if (i + 1 >= argc) { fprintf(stderr, "tcp-relayd: --listen needs a value\n"); return 2; }
            port = atoi(argv[++i]);
        } else if (a == "--retention-hours") {
            if (i + 1 >= argc) { fprintf(stderr, "tcp-relayd: --retention-hours needs a value\n"); return 2; }
            retention_hours = (uint64_t)strtoull(argv[++i], nullptr, 10);
        } else if (a == "--identity-seed-file") {
            if (i + 1 >= argc) { fprintf(stderr, "tcp-relayd: --identity-seed-file needs a value\n"); return 2; }
            seed_file = argv[++i];
        } else if (a == "--dump-frames") {
            if (i + 1 >= argc) { fprintf(stderr, "tcp-relayd: --dump-frames needs a value\n"); return 2; }
            dump_path = argv[++i];
        } else {
            fprintf(stderr, "tcp-relayd: unrecognized argument: %s\n", a.c_str());
            return 2;
        }
    }

    uint8_t server_pk[32];
    if (!seed_file.empty()) {
        uint8_t seed[32];
        if (!load_seed_file(seed_file, seed)) {
            fprintf(stderr, "tcp-relayd: identity-seed-file must hold 32 raw bytes "
                            "or 64 hex chars: %s\n", seed_file.c_str());
            return 1;
        }
        ke::KeyPair id = ke::keypair_from_seed(seed);
        memcpy(server_pk, id.sign_pk.data(), 32);
        /* The relay never signs (see tcp_relay.h): only server_pk, the public
         * half, is ever used. Wipe the seed and the rest of the derived
         * keypair now that the pubkey is extracted. */
        ke::secure_wipe(seed, sizeof seed);
        ke::secure_wipe(id.sign_sk.data(), id.sign_sk.size());
        ke::secure_wipe(id.dh_sk.data(), id.dh_sk.size());
    } else if (!ke::random_bytes(server_pk, 32)) {
        fprintf(stderr, "tcp-relayd: no --identity-seed-file and no entropy source\n");
        return 1;
    }

    FILE *dump_f = nullptr;
    if (!dump_path.empty()) {
        dump_f = fopen(dump_path.c_str(), "ab");
        if (!dump_f) {
            fprintf(stderr, "tcp-relayd: cannot open --dump-frames file: %s\n", dump_path.c_str());
            return 1;
        }
    }

    LoggingPushNotifier notifier;
    ke::TcpRelayServer server(server_pk, &notifier, retention_hours);
    if (!server.listen("0.0.0.0", (uint16_t)port)) {
        fprintf(stderr, "tcp-relayd: bind %d failed\n", port);
        if (dump_f) fclose(dump_f);
        return 1;
    }

    if (dump_f) {
        /* Test-aid sink: every raw client frame, length-prefixed exactly as
         * on the wire, verbatim. */
        server.set_frame_sink([dump_f](const std::string &frame) {
            uint8_t lb[4];
            ke::store_u32le(lb, (uint32_t)frame.size());
            fwrite(lb, 1, sizeof lb, dump_f);
            fwrite(frame.data(), 1, frame.size(), dump_f);
            fflush(dump_f);
        });
    }

    fprintf(stdout, "%s tcp-relayd: listening on tcp/%d server_pk=%s retention_hours=%llu"
                    "%s\n", ts().c_str(), server.local().port, hexstr(server_pk, 32).c_str(),
            (unsigned long long)retention_hours, dump_f ? " dump-frames=on" : "");
    fflush(stdout);

    install_signal_handlers();
    while (!g_stop) server.step(1000);

    fprintf(stdout, "%s tcp-relayd: shutting down\n", ts().c_str());
    fflush(stdout);
    if (dump_f) fclose(dump_f);
    return 0;
}
