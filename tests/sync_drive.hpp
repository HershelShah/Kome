/* sync_drive.hpp — shared test helpers: a datagram medium abstraction and a
 * reconciliation pump over the reliability layer. Used by network_test and
 * relay_test. */
#ifndef SYNC_TEST_DRIVE_HPP
#define SYNC_TEST_DRIVE_HPP

#include "sync_engine.h"

#include <unistd.h>

#include <chrono>
#include <string>
#include <vector>

#include "transport/reliable.h"

namespace synctest {

/* A datagram medium between endpoint 0 (A) and endpoint 1 (B). */
struct Medium {
    virtual ~Medium() = default;
    virtual void send(int from, const std::string &dg) = 0;
    virtual bool recv(int to, std::string &dg) = 0;
};

inline uint64_t now_ms() {
    using namespace std::chrono;
    return (uint64_t)duration_cast<milliseconds>(
               steady_clock::now().time_since_epoch())
        .count();
}

/* Drive two engines to convergence over a datagram medium using the
 * reliability layer. virtual_clock advances time deterministically (for an
 * in-process lossy/sim medium); otherwise it uses the real clock. */
inline bool converge(sync_engine *a, sync_engine *b, Medium &m,
                     bool virtual_clock, int max_iters) {
    sync_session *sa = sync_session_begin(a, 1);
    sync_session *sb = sync_session_begin(b, 0);
    ke::ReliableLink la, lb;

    auto feed = [&](sync_session *s, ke::ReliableLink &l,
                    const std::string &msg) {
        uint8_t *o = nullptr; size_t ol = 0; int d = 0;
        sync_session_step(s, (const uint8_t *)msg.data(), msg.size(), &o, &ol,
                          &d);
        if (ol) l.send(std::string((char *)o, ol));
        if (o) sync_free(o);
    };

    { /* initiator's first message */
        uint8_t *o = nullptr; size_t ol = 0; int d = 0;
        sync_session_step(sa, nullptr, 0, &o, &ol, &d);
        if (ol) la.send(std::string((char *)o, ol));
        if (o) sync_free(o);
    }

    uint64_t now = virtual_clock ? 0 : now_ms();
    int quiet = 0;
    bool ok = false;
    for (int iter = 0; iter < max_iters; iter++) {
        now = virtual_clock ? now + 100 : now_ms();
        bool work = false;

        std::vector<std::string> dgs;
        la.poll(dgs, now);
        for (auto &d : dgs) { m.send(0, d); work = true; }
        dgs.clear();
        lb.poll(dgs, now);
        for (auto &d : dgs) { m.send(1, d); work = true; }

        std::string dg;
        while (m.recv(0, dg)) {
            work = true;
            std::vector<std::string> del;
            la.on_datagram(dg, del);
            for (auto &msg : del) feed(sa, la, msg);
        }
        while (m.recv(1, dg)) {
            work = true;
            std::vector<std::string> del;
            lb.on_datagram(dg, del);
            for (auto &msg : del) feed(sb, lb, msg);
        }

        if (!work && la.idle() && lb.idle()) {
            if (++quiet > 5) { ok = true; break; }
        } else {
            quiet = 0;
        }
        if (!virtual_clock) usleep(500);
    }
    sync_session_end(sa);
    sync_session_end(sb);
    return ok;
}

} // namespace synctest

#endif /* SYNC_TEST_DRIVE_HPP */
