#ifndef KOME_WIRE_HPP
#define KOME_WIRE_HPP

/**
 * @file kome_wire.hpp
 * @brief Wire protocol types and MessagePack encode/decode functions.
 *
 * All messages are a 1-byte type prefix + MessagePack payload (via cwpack).
 * The protocol is forward-compatible: unknown fields are silently skipped
 * on decode, so older peers can still talk to newer ones.
 *
 * ## Message types
 *
 * | Byte | Name         | Direction  | Purpose                              |
 * |------|------------- |------------|--------------------------------------|
 * | 0x01 | SYNC_REQUEST | both       | Initiate sync (version vector + ns)  |
 * | 0x02 | SYNC_ENTRY   | responder  | Send a single entry during sync      |
 * | 0x03 | SYNC_DONE    | responder  | "I'm done sending entries"           |
 * | 0x04 | SYNC_ACK     | receiver   | Acknowledge receipt of an entry      |
 * | 0x05 | LIVE_ENTRY   | either     | Push a single entry in live mode     |
 * | 0x06 | BATCH_ENTRY  | either     | Push multiple entries atomically     |
 */

#include "kome_entry.hpp"
#include <map>

namespace kome {

enum WireMessageType : uint8_t {
    SYNC_REQUEST       = 0x01,
    SYNC_ENTRY         = 0x02,
    SYNC_DONE          = 0x03,
    SYNC_ACK           = 0x04,
    LIVE_ENTRY         = 0x05,
    BATCH_ENTRY        = 0x06
};

/** @brief SYNC_REQUEST payload: protocol version + version vector + optional namespace filter. */
struct SyncRequest {
    uint8_t                         protocol_version = KOME_PROTOCOL_VERSION;
    std::map<std::string, uint64_t> vv;          ///< author(32 bytes) → highest seq
    std::vector<std::string>        namespaces;  ///< Namespace filter; empty = sync all
};

/// SyncEntry is just an Entry — same struct used for storage and wire
using SyncEntry = Entry;

/** @brief SYNC_ACK payload: identifies which entry was acknowledged. */
struct SyncAck {
    uint8_t  author[32];
    uint64_t seq;
};

/* --- Encode (returns serialized bytes; empty vector on error) --- */
std::vector<uint8_t> encode_sync_request(const SyncRequest &msg);
std::vector<uint8_t> encode_sync_entry(const SyncEntry &entry);
std::vector<uint8_t> encode_sync_done();
std::vector<uint8_t> encode_sync_ack(const SyncAck &ack);
std::vector<uint8_t> encode_live_entry(const SyncEntry &entry);
std::vector<uint8_t> encode_batch_entry(const std::vector<SyncEntry> &entries);

/* --- Decode (returns false on malformed input) --- */
bool decode_message_type(const uint8_t *data, size_t len, WireMessageType *type_out);
bool decode_sync_request(const uint8_t *data, size_t len, SyncRequest *out);
bool decode_sync_entry(const uint8_t *data, size_t len, SyncEntry *out);
bool decode_sync_done(const uint8_t *data, size_t len);
bool decode_sync_ack(const uint8_t *data, size_t len, SyncAck *out);
bool decode_live_entry(const uint8_t *data, size_t len, SyncEntry *out);
bool decode_batch_entry(const uint8_t *data, size_t len, std::vector<SyncEntry> *out);

} /* namespace kome */

#endif /* KOME_WIRE_HPP */
