/* libFuzzer target: STUN request/response parsing on arbitrary bytes. */
#include <cstddef>
#include <cstdint>
#include <string>

#include "transport/stun.h"

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    std::string m((const char *)data, size);
    uint8_t txid[12];
    ke::Endpoint ep;
    ke::stun_parse_request(m, txid);
    ke::stun_parse_response(m, txid, ep);
    return 0;
}
