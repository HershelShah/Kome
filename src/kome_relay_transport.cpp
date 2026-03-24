/*
 * Kome HTTP relay transport — implementation
 *
 * Minimal HTTP client using raw POSIX sockets. Not a general-purpose HTTP
 * library — handles only what the relay protocol needs.
 */
#include "kome_relay_transport.h"

#include <atomic>
#include <cinttypes>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <mutex>
#include <string>
#include <thread>
#include <vector>

/* POSIX networking */
#include <arpa/inet.h>
#include <errno.h>
#include <netdb.h>
#include <sys/socket.h>
#include <unistd.h>

namespace {

/* ========================================================================
   Base64 encode/decode — used for binary data in JSON relay messages
   ======================================================================== */

static const char b64_table[] =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

std::string base64_encode(const uint8_t *data, size_t len) {
    std::string out;
    out.reserve(((len + 2) / 3) * 4);
    for (size_t i = 0; i < len; i += 3) {
        uint32_t n = (uint32_t)data[i] << 16;
        if (i + 1 < len) n |= (uint32_t)data[i + 1] << 8;
        if (i + 2 < len) n |= (uint32_t)data[i + 2];

        out.push_back(b64_table[(n >> 18) & 0x3F]);
        out.push_back(b64_table[(n >> 12) & 0x3F]);
        out.push_back((i + 1 < len) ? b64_table[(n >> 6) & 0x3F] : '=');
        out.push_back((i + 2 < len) ? b64_table[n & 0x3F] : '=');
    }
    return out;
}

static int b64_decode_char(char c) {
    if (c >= 'A' && c <= 'Z') return c - 'A';
    if (c >= 'a' && c <= 'z') return c - 'a' + 26;
    if (c >= '0' && c <= '9') return c - '0' + 52;
    if (c == '+') return 62;
    if (c == '/') return 63;
    return -1;
}

std::vector<uint8_t> base64_decode(const char *str, size_t len) {
    std::vector<uint8_t> out;
    out.reserve((len / 4) * 3);

    for (size_t i = 0; i + 3 < len; i += 4) {
        /* Skip whitespace */
        int a = b64_decode_char(str[i]);
        int b = b64_decode_char(str[i + 1]);
        int c = b64_decode_char(str[i + 2]);
        int d = b64_decode_char(str[i + 3]);

        if (a < 0 || b < 0) break;

        out.push_back((uint8_t)((a << 2) | (b >> 4)));
        if (c >= 0) out.push_back((uint8_t)(((b & 0x0F) << 4) | (c >> 2)));
        if (d >= 0) out.push_back((uint8_t)(((c & 0x03) << 6) | d));
    }
    return out;
}

/* ========================================================================
   Hex encode/decode — fingerprints are hex strings in the relay protocol
   ======================================================================== */

std::string hex_encode(const uint8_t *data, size_t len) {
    static const char hex[] = "0123456789abcdef";
    std::string out;
    out.reserve(len * 2);
    for (size_t i = 0; i < len; i++) {
        out.push_back(hex[data[i] >> 4]);
        out.push_back(hex[data[i] & 0x0F]);
    }
    return out;
}

bool hex_decode(const char *str, size_t str_len, uint8_t *out, size_t out_len) {
    if (str_len != out_len * 2) return false;
    for (size_t i = 0; i < out_len; i++) {
        int hi, lo;
        char ch = str[i * 2];
        char cl = str[i * 2 + 1];

        if (ch >= '0' && ch <= '9') hi = ch - '0';
        else if (ch >= 'a' && ch <= 'f') hi = ch - 'a' + 10;
        else if (ch >= 'A' && ch <= 'F') hi = ch - 'A' + 10;
        else return false;

        if (cl >= '0' && cl <= '9') lo = cl - '0';
        else if (cl >= 'a' && cl <= 'f') lo = cl - 'a' + 10;
        else if (cl >= 'A' && cl <= 'F') lo = cl - 'A' + 10;
        else return false;

        out[i] = (uint8_t)((hi << 4) | lo);
    }
    return true;
}

/* ========================================================================
   Minimal URL parser
   ======================================================================== */

struct ParsedURL {
    std::string host;
    uint16_t    port = 80;
    std::string path;   /* includes leading / */
};

bool parse_url(const char *url, ParsedURL &out) {
    /* Only support http:// */
    const char *p = url;
    if (std::strncmp(p, "http://", 7) != 0) return false;
    p += 7;

    /* Find host end */
    const char *host_start = p;
    const char *host_end = p;
    while (*host_end && *host_end != ':' && *host_end != '/' && *host_end != '?')
        host_end++;

    out.host.assign(host_start, host_end);
    if (out.host.empty()) return false;

    p = host_end;
    if (*p == ':') {
        p++;
        char *end = nullptr;
        long port = std::strtol(p, &end, 10);
        if (end == p || port <= 0 || port > 65535) return false;
        out.port = (uint16_t)port;
        p = end;
    } else {
        out.port = 80;
    }

    if (*p == '/') {
        out.path = p;
    } else {
        out.path = "/";
    }

    return true;
}

/* ========================================================================
   Minimal HTTP client using raw POSIX sockets
   ======================================================================== */

/* Connect to host:port, returns socket fd or -1 on failure */
int tcp_connect(const char *host, uint16_t port) {
    struct addrinfo hints{}, *res = nullptr;
    hints.ai_family = AF_UNSPEC;
    hints.ai_socktype = SOCK_STREAM;

    char port_str[8];
    std::snprintf(port_str, sizeof(port_str), "%u", port);

    if (getaddrinfo(host, port_str, &hints, &res) != 0)
        return -1;

    int fd = -1;
    for (auto *rp = res; rp; rp = rp->ai_next) {
        fd = socket(rp->ai_family, rp->ai_socktype, rp->ai_protocol);
        if (fd < 0) continue;

        /* Set a 10-second connect/send/recv timeout */
        struct timeval tv;
        tv.tv_sec = 10;
        tv.tv_usec = 0;
        setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv));
        setsockopt(fd, SOL_SOCKET, SO_SNDTIMEO, &tv, sizeof(tv));

        if (connect(fd, rp->ai_addr, rp->ai_addrlen) == 0)
            break;
        close(fd);
        fd = -1;
    }
    freeaddrinfo(res);
    return fd;
}

/* Send all bytes, returns true on success */
bool tcp_send_all(int fd, const void *data, size_t len) {
    const uint8_t *p = (const uint8_t *)data;
    size_t sent = 0;
    while (sent < len) {
        ssize_t n = ::send(fd, p + sent, len - sent, MSG_NOSIGNAL);
        if (n <= 0) return false;
        sent += (size_t)n;
    }
    return true;
}

/* Read entire HTTP response. Returns status code and body, or -1 on error. */
struct HttpResponse {
    int         status = -1;
    std::string body;
};

HttpResponse http_read_response(int fd) {
    HttpResponse resp;
    /* Read headers + body in chunks */
    std::string raw;
    char buf[4096];
    bool headers_done = false;
    size_t content_length = 0;
    size_t header_end_pos = 0;

    while (true) {
        ssize_t n = recv(fd, buf, sizeof(buf), 0);
        if (n <= 0) break;
        raw.append(buf, (size_t)n);

        if (!headers_done) {
            auto pos = raw.find("\r\n\r\n");
            if (pos != std::string::npos) {
                headers_done = true;
                header_end_pos = pos + 4;

                /* Parse status line */
                auto first_line_end = raw.find("\r\n");
                if (first_line_end != std::string::npos) {
                    /* "HTTP/1.1 200 OK" — status starts at offset 9 */
                    auto space = raw.find(' ');
                    if (space != std::string::npos)
                        resp.status = std::atoi(raw.c_str() + space + 1);
                }

                /* Parse Content-Length (case-insensitive search) */
                std::string header_block = raw.substr(0, pos);
                const char *cl = "content-length:";
                size_t cl_len = 15;
                /* Simple case-insensitive search */
                for (size_t i = 0; i + cl_len < header_block.size(); i++) {
                    bool match = true;
                    for (size_t j = 0; j < cl_len && match; j++) {
                        char a = header_block[i + j];
                        char b = cl[j];
                        if (a >= 'A' && a <= 'Z') a += 32;
                        if (a != b) match = false;
                    }
                    if (match) {
                        content_length = (size_t)std::atol(
                            header_block.c_str() + i + cl_len);
                        break;
                    }
                }
            }
        }

        if (headers_done) {
            size_t body_received = raw.size() - header_end_pos;
            if (content_length > 0 && body_received >= content_length)
                break;
            /* If no content-length, use chunked/close semantics —
               just keep reading until connection closes */
            if (content_length == 0 && headers_done) {
                /* For relay responses we expect Content-Length; if missing,
                   read a reasonable amount then stop */
                if (body_received > 0) break;
            }
        }
    }

    if (headers_done) {
        resp.body = raw.substr(header_end_pos);
        if (content_length > 0 && resp.body.size() > content_length)
            resp.body.resize(content_length);
    }

    return resp;
}

/* Perform an HTTP GET request */
HttpResponse http_get(const char *host, uint16_t port, const std::string &path) {
    HttpResponse fail;
    int fd = tcp_connect(host, port);
    if (fd < 0) return fail;

    std::string req = "GET " + path + " HTTP/1.1\r\n"
                      "Host: " + host + "\r\n"
                      "Connection: close\r\n"
                      "\r\n";

    if (!tcp_send_all(fd, req.data(), req.size())) {
        close(fd);
        return fail;
    }

    auto resp = http_read_response(fd);
    close(fd);
    return resp;
}

/* Perform an HTTP POST request with JSON body */
HttpResponse http_post(const char *host, uint16_t port,
                        const std::string &path, const std::string &json_body) {
    HttpResponse fail;
    int fd = tcp_connect(host, port);
    if (fd < 0) return fail;

    char len_str[32];
    std::snprintf(len_str, sizeof(len_str), "%zu", json_body.size());

    std::string req = "POST " + path + " HTTP/1.1\r\n"
                      "Host: " + std::string(host) + "\r\n"
                      "Content-Type: application/json\r\n"
                      "Content-Length: " + len_str + "\r\n"
                      "Connection: close\r\n"
                      "\r\n" + json_body;

    if (!tcp_send_all(fd, req.data(), req.size())) {
        close(fd);
        return fail;
    }

    auto resp = http_read_response(fd);
    close(fd);
    return resp;
}

/* ========================================================================
   Minimal JSON helpers — just enough for the relay protocol
   ======================================================================== */

/* Find a string value for a given key in a JSON object.
 * Returns empty string if not found. Very naive — works for simple flat JSON. */
std::string json_get_string(const std::string &json, const char *key) {
    std::string needle = std::string("\"") + key + "\"";
    auto pos = json.find(needle);
    if (pos == std::string::npos) return "";
    pos += needle.size();

    /* Skip whitespace and colon */
    while (pos < json.size() && (json[pos] == ' ' || json[pos] == ':' ||
           json[pos] == '\t' || json[pos] == '\n' || json[pos] == '\r'))
        pos++;

    if (pos >= json.size() || json[pos] != '"') return "";
    pos++; /* skip opening quote */

    std::string result;
    while (pos < json.size() && json[pos] != '"') {
        if (json[pos] == '\\' && pos + 1 < json.size()) {
            pos++;
            result.push_back(json[pos]);
        } else {
            result.push_back(json[pos]);
        }
        pos++;
    }
    return result;
}

/* Get a numeric value for a given key */
int64_t json_get_number(const std::string &json, const char *key) {
    std::string needle = std::string("\"") + key + "\"";
    auto pos = json.find(needle);
    if (pos == std::string::npos) return -1;
    pos += needle.size();

    while (pos < json.size() && (json[pos] == ' ' || json[pos] == ':' ||
           json[pos] == '\t' || json[pos] == '\n' || json[pos] == '\r'))
        pos++;

    return std::atoll(json.c_str() + pos);
}

/* Parse a JSON array of objects like [{"id":N,"from":"...","data":"..."},...]
 * Extracts objects one by one. Very simple — assumes no nested objects. */
struct RecvMessage {
    int64_t     id;
    std::string from;  /* hex fingerprint */
    std::string data;  /* base64 encoded */
};

std::vector<RecvMessage> parse_recv_messages(const std::string &json) {
    std::vector<RecvMessage> result;
    size_t pos = 0;

    while (pos < json.size()) {
        auto obj_start = json.find('{', pos);
        if (obj_start == std::string::npos) break;
        auto obj_end = json.find('}', obj_start);
        if (obj_end == std::string::npos) break;

        std::string obj = json.substr(obj_start, obj_end - obj_start + 1);
        RecvMessage msg;
        msg.id = json_get_number(obj, "id");
        msg.from = json_get_string(obj, "from");
        msg.data = json_get_string(obj, "data");

        if (msg.id >= 0 && !msg.from.empty() && !msg.data.empty())
            result.push_back(std::move(msg));

        pos = obj_end + 1;
    }
    return result;
}

/* Parse a JSON array of strings like ["aabb...","ccdd...",...] */
std::vector<std::string> parse_string_array(const std::string &json) {
    std::vector<std::string> result;
    size_t pos = 0;

    /* Find the opening bracket */
    pos = json.find('[');
    if (pos == std::string::npos) return result;
    pos++;

    while (pos < json.size()) {
        auto quote_start = json.find('"', pos);
        if (quote_start == std::string::npos) break;
        auto quote_end = json.find('"', quote_start + 1);
        if (quote_end == std::string::npos) break;

        result.push_back(json.substr(quote_start + 1, quote_end - quote_start - 1));
        pos = quote_end + 1;
    }
    return result;
}

/* ========================================================================
   Relay transport state
   ======================================================================== */

struct RelayTransport {
    KomeTransport         transport;   /* must be first member */

    /* Configuration */
    std::string           host;
    uint16_t              port;
    std::string           base_path;
    uint8_t               fingerprint[32];
    std::string           fp_hex;

    /* Callbacks (set by the engine via set_recv_callback / set_peer_callback) */
    std::mutex            cb_mu;
    void                (*recv_cb)(void *ud, const uint8_t *peer_fp,
                                   const uint8_t *data, size_t len);
    void                 *recv_ud;
    void                (*peer_cb)(void *ud, const uint8_t *peer_fp, int connected);
    void                 *peer_ud;

    /* Background poller */
    std::atomic<bool>     running{false};
    std::thread           poll_thread;

    /* Known peers — track who we've announced as connected */
    std::mutex            peers_mu;
    std::vector<std::string> known_peers;  /* hex fingerprints */
};

/* ========================================================================
   Transport function implementations
   ======================================================================== */

void relay_send(KomeTransport *t, const uint8_t *peer_fp,
                const uint8_t *data, size_t len) {
    auto *rt = reinterpret_cast<RelayTransport*>(t->user_data);

    std::string to_hex = hex_encode(peer_fp, 32);
    std::string b64 = base64_encode(data, len);

    std::string body = "{\"from\":\"" + rt->fp_hex + "\","
                        "\"to\":\"" + to_hex + "\","
                        "\"data\":\"" + b64 + "\"}";

    http_post(rt->host.c_str(), rt->port, rt->base_path + "/send", body);
    /* Fire-and-forget — relay transport is best-effort */
}

void relay_set_recv(KomeTransport *t,
    void (*cb)(void *ud, const uint8_t *peer_fp, const uint8_t *data, size_t len),
    void *ud) {
    auto *rt = reinterpret_cast<RelayTransport*>(t->user_data);
    std::lock_guard<std::mutex> lock(rt->cb_mu);
    rt->recv_cb = cb;
    rt->recv_ud = ud;
}

void relay_set_peer(KomeTransport *t,
    void (*cb)(void *ud, const uint8_t *peer_fp, int connected),
    void *ud) {
    auto *rt = reinterpret_cast<RelayTransport*>(t->user_data);
    std::lock_guard<std::mutex> lock(rt->cb_mu);
    rt->peer_cb = cb;
    rt->peer_ud = ud;
}

/* ========================================================================
   Background polling thread
   ======================================================================== */

void relay_poll_loop(RelayTransport *rt) {
    uint32_t backoff_ms = 1000;        /* start at 1s */
    const uint32_t max_backoff = 30000; /* cap at 30s */
    const uint32_t normal_interval = 2000; /* poll every 2s when healthy */

    while (rt->running.load(std::memory_order_acquire)) {
        bool success = true;

        /* --- Poll /recv for incoming messages --- */
        {
            std::string path = rt->base_path + "/recv?fp=" + rt->fp_hex;
            auto resp = http_get(rt->host.c_str(), rt->port, path);

            if (resp.status == 200) {
                auto msgs = parse_recv_messages(resp.body);

                if (!msgs.empty()) {
                    /* Deliver messages */
                    std::vector<int64_t> ack_ids;
                    for (auto &msg : msgs) {
                        uint8_t from_fp[32];
                        if (!hex_decode(msg.from.c_str(), msg.from.size(), from_fp, 32))
                            continue;

                        auto decoded = base64_decode(msg.data.c_str(), msg.data.size());
                        if (decoded.empty()) continue;

                        /* Deliver to engine */
                        void (*cb)(void *, const uint8_t *, const uint8_t *, size_t) = nullptr;
                        void *ud = nullptr;
                        {
                            std::lock_guard<std::mutex> lock(rt->cb_mu);
                            cb = rt->recv_cb;
                            ud = rt->recv_ud;
                        }
                        if (cb)
                            cb(ud, from_fp, decoded.data(), decoded.size());

                        ack_ids.push_back(msg.id);
                    }

                    /* ACK received messages */
                    if (!ack_ids.empty()) {
                        std::string ids_str;
                        for (size_t i = 0; i < ack_ids.size(); i++) {
                            if (i > 0) ids_str += ",";
                            char num[32];
                            std::snprintf(num, sizeof(num), "%" PRId64, ack_ids[i]);
                            ids_str += num;
                        }
                        std::string ack_body = "{\"fp\":\"" + rt->fp_hex + "\","
                                                "\"ids\":[" + ids_str + "]}";
                        http_post(rt->host.c_str(), rt->port,
                                  rt->base_path + "/ack", ack_body);
                    }
                }
            } else {
                success = false;
            }
        }

        /* --- Poll /peers for peer discovery --- */
        {
            std::string path = rt->base_path + "/peers";
            auto resp = http_get(rt->host.c_str(), rt->port, path);

            if (resp.status == 200) {
                auto peers = parse_string_array(resp.body);

                /* Diff against known peers */
                void (*pcb)(void *, const uint8_t *, int) = nullptr;
                void *pud = nullptr;
                {
                    std::lock_guard<std::mutex> lock(rt->cb_mu);
                    pcb = rt->peer_cb;
                    pud = rt->peer_ud;
                }

                if (pcb) {
                    std::lock_guard<std::mutex> lock(rt->peers_mu);

                    /* Find new peers */
                    for (auto &p : peers) {
                        if (p == rt->fp_hex) continue; /* skip self */
                        bool found = false;
                        for (auto &kp : rt->known_peers) {
                            if (kp == p) { found = true; break; }
                        }
                        if (!found) {
                            rt->known_peers.push_back(p);
                            uint8_t fp[32];
                            if (hex_decode(p.c_str(), p.size(), fp, 32))
                                pcb(pud, fp, 1);
                        }
                    }

                    /* Find disconnected peers */
                    auto it = rt->known_peers.begin();
                    while (it != rt->known_peers.end()) {
                        bool still_here = false;
                        for (auto &p : peers) {
                            if (p == *it) { still_here = true; break; }
                        }
                        if (!still_here) {
                            uint8_t fp[32];
                            if (hex_decode(it->c_str(), it->size(), fp, 32))
                                pcb(pud, fp, 0);
                            it = rt->known_peers.erase(it);
                        } else {
                            ++it;
                        }
                    }
                }
            } else {
                success = false;
            }
        }

        /* Exponential backoff on failure, reset on success */
        uint32_t sleep_ms;
        if (success) {
            backoff_ms = 1000;
            sleep_ms = normal_interval;
        } else {
            sleep_ms = backoff_ms;
            backoff_ms = std::min(backoff_ms * 2, max_backoff);
        }

        /* Sleep in small increments to allow quick shutdown */
        for (uint32_t elapsed = 0;
             elapsed < sleep_ms && rt->running.load(std::memory_order_acquire);
             elapsed += 100) {
            std::this_thread::sleep_for(std::chrono::milliseconds(100));
        }
    }
}

} /* anonymous namespace */

/* ========================================================================
   Public C API
   ======================================================================== */

extern "C" {

KOME_API KomeError kome_relay_transport_create(const char *relay_url,
    const uint8_t *fingerprint, KomeTransport **out)
{
    if (!relay_url || !fingerprint || !out) return KOME_ERR_MISUSE;

    ParsedURL parsed;
    if (!parse_url(relay_url, parsed)) return KOME_ERR_MISUSE;

    auto *rt = new (std::nothrow) RelayTransport;
    if (!rt) return KOME_ERR_INTERNAL;

    rt->host = parsed.host;
    rt->port = parsed.port;
    /* Remove trailing slash from path to use as base */
    rt->base_path = parsed.path;
    if (!rt->base_path.empty() && rt->base_path.back() == '/')
        rt->base_path.pop_back();
    /* If the path is just empty, leave it empty (endpoints are /register etc.) */

    std::memcpy(rt->fingerprint, fingerprint, 32);
    rt->fp_hex = hex_encode(fingerprint, 32);
    rt->recv_cb = nullptr;
    rt->recv_ud = nullptr;
    rt->peer_cb = nullptr;
    rt->peer_ud = nullptr;

    /* Wire transport function pointers */
    rt->transport.send = relay_send;
    rt->transport.set_recv_callback = relay_set_recv;
    rt->transport.set_peer_callback = relay_set_peer;
    rt->transport.user_data = rt;

    /* Register with the relay */
    {
        std::string body = "{\"fingerprint\":\"" + rt->fp_hex + "\"}";
        auto resp = http_post(rt->host.c_str(), rt->port,
                              rt->base_path + "/register", body);
        /* Non-fatal if registration fails — the poll loop will retry implicitly */
        (void)resp;
    }

    /* Start background polling thread */
    rt->running.store(true, std::memory_order_release);
    rt->poll_thread = std::thread(relay_poll_loop, rt);

    *out = &rt->transport;
    return KOME_OK;
}

KOME_API void kome_relay_transport_destroy(KomeTransport *transport) {
    if (!transport) return;

    auto *rt = reinterpret_cast<RelayTransport*>(transport->user_data);
    if (!rt) return;

    /* Stop polling thread */
    rt->running.store(false, std::memory_order_release);
    if (rt->poll_thread.joinable())
        rt->poll_thread.join();

    delete rt;
}

} /* extern "C" */
