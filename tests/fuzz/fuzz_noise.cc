/* libFuzzer target: feed arbitrary bytes to a Noise handshake step
 * (handshake message parsing + AEAD-on-decrypt path). */
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <string>

#include "crypto.h"
#include "noise.h"

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    uint8_t seed[32];
    std::memset(seed, 0x11, sizeof seed);
    ke::KeyPair kp = ke::keypair_from_seed(seed);
    ke::NoiseChannel ch(false, kp); /* responder parses an incoming handshake */
    std::string in((const char *)data, size), out;
    bool done = false;
    ch.step(in, out, done);
    return 0;
}
