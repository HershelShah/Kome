/* libFuzzer target for the WebSocket frame parser — the place a peer's frame
 * length/mask bytes are parsed (where the CVE-class length overflow lived).
 * Build with -DSYNC_FUZZ=ON using a clang that ships the fuzzer runtime. */
#include <cstddef>
#include <cstdint>
#include <string>

#include "transport/ws.h"

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    bool fin = false;
    uint8_t op = 0;
    std::string payload;
    size_t consumed = 0;
    /* Parse repeatedly, consuming frames, until it needs more bytes or errors. */
    size_t off = 0;
    for (int i = 0; i < 64; i++) {
        int r = ke::ws_parse_frame(data + off, size - off, fin, op, payload,
                                   consumed);
        if (r != 1 || consumed == 0) break;
        off += consumed;
        if (off >= size) break;
    }
    return 0;
}
