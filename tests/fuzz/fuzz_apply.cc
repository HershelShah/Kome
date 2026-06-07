/* libFuzzer target: decode a record then apply it (exercises signature
 * verification + LWW/causal-length merge on arbitrary records). */
#include <cstddef>
#include <cstdint>
#include <cstring>

#include "sync_engine.h"

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    sync_change c;
    size_t used = 0;
    if (sync_change_decode(data, size, &c, &used) != SYNC_OK) return 0;
    uint8_t seed[SYNC_SEED_LEN];
    std::memset(seed, 0x03, sizeof seed);
    sync_engine *e = sync_engine_create(seed);
    if (e) {
        sync_engine_apply(e, &c);
        sync_engine_destroy(e);
    }
    sync_change_free_decoded(&c);
    return 0;
}
