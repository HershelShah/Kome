/* sha256.h — minimal SHA-256, used for the deterministic state digest.
 * Public-domain style implementation (see sha256.cpp). Internal header. */
#ifndef SYNC_SHA256_H
#define SYNC_SHA256_H

#include <cstddef>
#include <cstdint>

namespace sync_engine_detail {

class Sha256 {
public:
    Sha256() { reset(); }
    void reset();
    void update(const void *data, size_t len);
    /* Writes 32 bytes to out and finalizes; the object must be reset to reuse. */
    void finish(uint8_t out[32]);

private:
    void block(const uint8_t *p);
    uint32_t state_[8];
    uint64_t bitlen_;
    uint8_t  buf_[64];
    size_t   buflen_;
};

/* One-shot helper. */
void sha256(const void *data, size_t len, uint8_t out[32]);

} // namespace sync_engine_detail

#endif /* SYNC_SHA256_H */
