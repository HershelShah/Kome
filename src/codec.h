/* codec.h — canonical, little-endian, versioned serialization of change
 * records (M3). Internal helpers shared by the public codec ABI and the
 * reconciliation engine. */
#ifndef SYNC_CODEC_H
#define SYNC_CODEC_H

#include <cstddef>
#include <cstdint>
#include <string>

#include "engine.hpp"
#include "sync_engine.h"

namespace ke {

/* 1-byte format version stamped at the head of every record. */
constexpr uint8_t kCodecVersion = 1;

/* Unsigned LEB128 varint. */
void     put_varint(std::string &out, uint64_t v);
bool     get_varint(const uint8_t *&p, const uint8_t *end, uint64_t &v);

/* Append the canonical serialization of c to out. */
void encode_record(const sync_change &c, std::string &out);

/* A decoded record owning its own bytes; yields a borrowing sync_change view. */
struct DecodedChange {
    uint8_t     kind = 0;
    std::string ns, entity, field, value;
    uint64_t    causal_length = 0;
    sync_hlc    hlc{};
    SiteId      site{};

    sync_change view() const;
};

/* Decode one record from buf[0, len). On success returns true, fills out, and
 * sets consumed to the number of bytes read. */
bool decode_record(const uint8_t *buf, size_t len, DecodedChange &out,
                   size_t &consumed);

} // namespace ke

#endif /* SYNC_CODEC_H */
