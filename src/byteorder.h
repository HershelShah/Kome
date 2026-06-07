/* byteorder.h — fixed-width little-endian (de)serialization primitives.
 *
 * One home for the integer-to-bytes loops that were duplicated across the
 * codec, the engine's digest, the reconciliation fingerprint, and the
 * capability codec. All inline, all in namespace ke. (Big-endian wire helpers
 * for the network transports live alongside their own framing code.) */
#ifndef SYNC_BYTEORDER_H
#define SYNC_BYTEORDER_H

#include <cstddef>
#include <cstdint>
#include <string>

namespace ke {

/* ---- store into a fixed-size byte buffer (no bounds: caller owns the size) - */

inline void store_u32le(uint8_t out[4], uint32_t v) {
    for (int i = 0; i < 4; i++) out[i] = (uint8_t)(v >> (i * 8));
}
inline void store_u64le(uint8_t out[8], uint64_t v) {
    for (int i = 0; i < 8; i++) out[i] = (uint8_t)(v >> (i * 8));
}

/* ---- append to a growing string ---------------------------------------- */

inline void put_u32le(std::string &out, uint32_t v) {
    uint8_t b[4];
    store_u32le(b, v);
    out.append(reinterpret_cast<const char *>(b), sizeof b);
}
inline void put_u64le(std::string &out, uint64_t v) {
    uint8_t b[8];
    store_u64le(b, v);
    out.append(reinterpret_cast<const char *>(b), sizeof b);
}

/* ---- read from a buffer (no bounds: caller checked there are N bytes) ---- */

inline uint32_t read_u32le(const uint8_t *p) {
    uint32_t v = 0;
    for (int i = 0; i < 4; i++) v |= (uint32_t)p[i] << (i * 8);
    return v;
}
inline uint64_t read_u64le(const uint8_t *p) {
    uint64_t v = 0;
    for (int i = 0; i < 8; i++) v |= (uint64_t)p[i] << (i * 8);
    return v;
}

/* ---- bounds-checked, cursor-advancing reads ---------------------------- */

inline bool get_u32le(const uint8_t *&p, const uint8_t *end, uint32_t &v) {
    if (end - p < 4) return false;
    v = read_u32le(p);
    p += 4;
    return true;
}
inline bool get_u64le(const uint8_t *&p, const uint8_t *end, uint64_t &v) {
    if (end - p < 8) return false;
    v = read_u64le(p);
    p += 8;
    return true;
}

} // namespace ke

#endif /* SYNC_BYTEORDER_H */
