/* libFuzzer target for sync_capability_decode (M6, T6.2). */
#include <cstddef>
#include <cstdint>

#include "sync_engine.h"

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    sync_capability *c = sync_capability_decode(data, size);
    if (c) sync_capability_free(c);
    return 0;
}
