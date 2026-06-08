/* libFuzzer target for sync_invite_decode (the invite codec parses untrusted
 * bytes — pubkey, address string, and an optional embedded capability).
 * Build with -DSYNC_FUZZ=ON using a clang that ships the fuzzer runtime. */
#include <cstddef>
#include <cstdint>

#include "sync_engine.h"

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    uint8_t pk[SYNC_PUBKEY_LEN];
    char addr[512];
    sync_capability *cap = nullptr;
    if (sync_invite_decode(data, size, pk, addr, sizeof addr, &cap) == SYNC_OK &&
        cap)
        sync_capability_free(cap);
    return 0;
}
