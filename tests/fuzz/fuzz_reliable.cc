/* libFuzzer target: reliability-layer datagram framing on arbitrary bytes. */
#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "transport/reliable.h"

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    ke::ReliableLink link;
    std::string dg((const char *)data, size);
    std::vector<std::string> delivered;
    link.on_datagram(dg, delivered);
    return 0;
}
