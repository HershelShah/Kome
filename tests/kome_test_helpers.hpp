#ifndef KOME_TEST_HELPERS_HPP
#define KOME_TEST_HELPERS_HPP

#include "kome.h"
#include <cstring>
#include <functional>
#include <vector>
#include <string>

/*
 * Loopback transport: two engines connected via direct function calls.
 * send() on one directly calls recv_callback() on the other.
 */

struct LoopbackSide {
    KomeTransport              transport;
    void                      (*recv_cb)(void *ud, const uint8_t *peer_fp,
                                         const uint8_t *data, size_t len) = nullptr;
    void                       *recv_ud = nullptr;
    void                      (*peer_cb)(void *ud, const uint8_t *peer_fp,
                                         int connected) = nullptr;
    void                       *peer_ud = nullptr;
    LoopbackSide               *other   = nullptr;
    uint8_t                     fingerprint[32] = {};
};

static void loopback_send(KomeTransport *t, const uint8_t * /*peer_fp*/,
                           const uint8_t *data, size_t len) {
    auto *side = reinterpret_cast<LoopbackSide*>(t->user_data);
    if (side->other && side->other->recv_cb) {
        /* Deliver data to the other side, with our fingerprint as the sender */
        side->other->recv_cb(side->other->recv_ud, side->fingerprint, data, len);
    }
}

static void loopback_set_recv(KomeTransport *t,
    void (*cb)(void *ud, const uint8_t *peer_fp, const uint8_t *data, size_t len),
    void *ud) {
    auto *side = reinterpret_cast<LoopbackSide*>(t->user_data);
    side->recv_cb = cb;
    side->recv_ud = ud;
}

static void loopback_set_peer(KomeTransport *t,
    void (*cb)(void *ud, const uint8_t *peer_fp, int connected),
    void *ud) {
    auto *side = reinterpret_cast<LoopbackSide*>(t->user_data);
    side->peer_cb = cb;
    side->peer_ud = ud;
}

struct LoopbackPair {
    LoopbackSide a;
    LoopbackSide b;

    LoopbackPair() {
        /* Set up side A */
        std::memset(a.fingerprint, 0xAA, 32);
        a.transport.send = loopback_send;
        a.transport.set_recv_callback = loopback_set_recv;
        a.transport.set_peer_callback = loopback_set_peer;
        a.transport.user_data = &a;

        /* Set up side B */
        std::memset(b.fingerprint, 0xBB, 32);
        b.transport.send = loopback_send;
        b.transport.set_recv_callback = loopback_set_recv;
        b.transport.set_peer_callback = loopback_set_peer;
        b.transport.user_data = &b;

        /* Wire them together */
        a.other = &b;
        b.other = &a;
    }

    void connect() {
        /* Fire peer callbacks on both sides */
        if (a.peer_cb) a.peer_cb(a.peer_ud, b.fingerprint, 1);
        if (b.peer_cb) b.peer_cb(b.peer_ud, a.fingerprint, 1);
    }

    void disconnect() {
        if (a.peer_cb) a.peer_cb(a.peer_ud, b.fingerprint, 0);
        if (b.peer_cb) b.peer_cb(b.peer_ud, a.fingerprint, 0);
    }
};

/* Helper to create a temp database path */
static std::string temp_db_path(const char *name) {
    return std::string("/tmp/kome_test_") + name + ".db";
}

/* Helper to clean up temp databases */
static void cleanup_db(const std::string &path) {
    std::remove(path.c_str());
    std::remove((path + "-wal").c_str());
    std::remove((path + "-shm").c_str());
}

#endif /* KOME_TEST_HELPERS_HPP */
