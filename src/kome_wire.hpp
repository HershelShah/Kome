#ifndef KOME_WIRE_HPP
#define KOME_WIRE_HPP

#include "kome.h"
#include <cstdint>
#include <cstddef>
#include <string>
#include <vector>
#include <map>

namespace kome {

enum WireMessageType : uint8_t {
    SYNC_REQUEST       = 0x01,
    SYNC_ENTRY         = 0x02,
    SYNC_DONE          = 0x03,
    SYNC_ACK           = 0x04,
    LIVE_ENTRY         = 0x05,
    BATCH_ENTRY        = 0x06,
    NAMESPACE_ACL_SYNC = 0x07
};

struct SyncRequest {
    uint8_t                         protocol_version = KOME_PROTOCOL_VERSION;
    std::map<std::string, uint64_t> vv;   /* author(32 bytes) -> seq */
};

struct SyncEntry {
    std::string          ns;
    std::vector<uint8_t> key;
    std::vector<uint8_t> value;
    uint64_t             timestamp_us;
    uint8_t              author[32];
    uint64_t             seq;
    uint8_t              hash[32];
    uint8_t              tombstone;
};

struct SyncAck {
    uint8_t  author[32];
    uint64_t seq;
};

struct NamespaceACLSyncEntry {
    std::string ns;
    int         role;   /* KomeRole value */
};

struct NamespaceACLSync {
    std::vector<NamespaceACLSyncEntry> entries;
};

/* Encode functions — return serialized bytes (type prefix + msgpack payload).
   Returns empty vector on encoding error. */
std::vector<uint8_t> encode_sync_request(const SyncRequest &msg);
std::vector<uint8_t> encode_sync_entry(const SyncEntry &entry);
std::vector<uint8_t> encode_sync_done();
std::vector<uint8_t> encode_sync_ack(const SyncAck &ack);
std::vector<uint8_t> encode_live_entry(const SyncEntry &entry);
std::vector<uint8_t> encode_batch_entry(const std::vector<SyncEntry> &entries);
std::vector<uint8_t> encode_namespace_acl_sync(const NamespaceACLSync &msg);

/* Decode functions — return false on malformed input */
bool decode_message_type(const uint8_t *data, size_t len, WireMessageType *type_out);
bool decode_sync_request(const uint8_t *data, size_t len, SyncRequest *out);
bool decode_sync_entry(const uint8_t *data, size_t len, SyncEntry *out);
bool decode_sync_done(const uint8_t *data, size_t len);
bool decode_sync_ack(const uint8_t *data, size_t len, SyncAck *out);
bool decode_live_entry(const uint8_t *data, size_t len, SyncEntry *out);
bool decode_batch_entry(const uint8_t *data, size_t len, std::vector<SyncEntry> *out);
bool decode_namespace_acl_sync(const uint8_t *data, size_t len, NamespaceACLSync *out);

} /* namespace kome */

#endif /* KOME_WIRE_HPP */
