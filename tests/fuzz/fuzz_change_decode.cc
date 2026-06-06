/* libFuzzer target for sync_change_decode (M6, T6.2).
 * Build with -DSYNC_FUZZ=ON using a clang that ships the fuzzer runtime. */
#include <cstddef>
#include <cstdint>

#include "sync_engine.h"

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    sync_change c;
    size_t consumed = 0;
    if (sync_change_decode(data, size, &c, &consumed) == SYNC_OK)
        sync_change_free_decoded(&c);
    return 0;
}
