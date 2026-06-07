/* libFuzzer target: open a database from arbitrary bytes (storage load path,
 * schema/meta/row parsing against a corrupt file). */
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <string>
#include <unistd.h>

#include "sync_engine.h"

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    std::string path = "/tmp/sync_fuzz_storage_" + std::to_string(getpid()) + ".db";
    FILE *f = std::fopen(path.c_str(), "wb");
    if (!f) return 0;
    if (size) std::fwrite(data, 1, size, f);
    std::fclose(f);

    uint8_t seed[SYNC_SEED_LEN];
    std::memset(seed, 0x5a, sizeof seed);
    sync_engine *e = sync_engine_open(path.c_str(), seed);
    if (e) {
        uint8_t dig[SYNC_DIGEST_LEN];
        sync_engine_digest(e, dig);
        sync_engine_destroy(e);
    }
    std::remove(path.c_str());
    std::remove((path + "-wal").c_str());
    std::remove((path + "-shm").c_str());
    return 0;
}
