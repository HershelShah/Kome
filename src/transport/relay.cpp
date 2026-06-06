/* relay.cpp — blind store-and-forward relay (M5). */
#include "transport/relay.h"

namespace ke {

void Relay::send(const uint8_t dst[32], const std::string &blob) {
    mailbox_[key(dst)].push_back(blob);
}

void Relay::fetch(const uint8_t pk[32], std::vector<std::string> &out) {
    auto it = mailbox_.find(key(pk));
    if (it == mailbox_.end()) return;
    while (!it->second.empty()) {
        out.push_back(it->second.front());
        it->second.pop_front();
    }
}

size_t Relay::queued(const uint8_t dst[32]) const {
    auto it = mailbox_.find(key(dst));
    return it == mailbox_.end() ? 0 : it->second.size();
}

} // namespace ke
