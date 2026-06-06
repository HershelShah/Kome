/* libFuzzer target for the reconciliation message parser, reached through
 * sync_session_step (M6, T6.2). */
#include <cstddef>
#include <cstdint>
#include <cstring>

#include "sync_engine.h"

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    uint8_t seed[SYNC_SEED_LEN];
    std::memset(seed, 0x07, sizeof seed);
    sync_engine *e = sync_engine_create(seed);
    if (!e) return 0;
    /* A little state so the session has a non-empty snapshot to parse against. */
    sync_engine_set(e, (const uint8_t *)"n", 1, (const uint8_t *)"x", 1,
                    (const uint8_t *)"f", 1, (const uint8_t *)"v", 1);
    sync_session *s = sync_session_begin(e, 0); /* responder parses input */
    if (s) {
        uint8_t *out = nullptr;
        size_t ol = 0;
        int done = 0;
        sync_session_step(s, data, size, &out, &ol, &done);
        if (out) sync_free(out);
        sync_session_end(s);
    }
    sync_engine_destroy(e);
    return 0;
}
