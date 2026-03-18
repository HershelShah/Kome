#include "kome_wire.hpp"
extern "C" {
#include "cwpack.h"
}
#include <cstring>

namespace kome {

/* --- Encode helpers ------------------------------------------------------ */

static void pack_entry_fields(cw_pack_context *pc, const SyncEntry &e) {
    cw_pack_map_size(pc, 8);

    cw_pack_str(pc, "ns", 2);
    cw_pack_str(pc, e.ns.data(), (unsigned)e.ns.size());

    cw_pack_str(pc, "k", 1);
    cw_pack_bin(pc, e.key.data(), (unsigned)e.key.size());

    cw_pack_str(pc, "v", 1);
    if (e.tombstone) {
        cw_pack_nil(pc);
    } else {
        cw_pack_bin(pc, e.value.data(), (unsigned)e.value.size());
    }

    cw_pack_str(pc, "ts", 2);
    cw_pack_unsigned(pc, e.timestamp_us);

    cw_pack_str(pc, "a", 1);
    cw_pack_bin(pc, e.author, 32);

    cw_pack_str(pc, "seq", 3);
    cw_pack_unsigned(pc, e.seq);

    cw_pack_str(pc, "h", 1);
    cw_pack_bin(pc, e.hash, 32);

    cw_pack_str(pc, "t", 1);
    cw_pack_unsigned(pc, e.tombstone);
}

std::vector<uint8_t> encode_sync_request(const SyncRequest &msg) {
    /* Heap-allocate: 40 bytes per VV entry + ns strings + overhead */
    size_t buf_size = 256 + msg.vv.size() * 48;
    for (auto &ns : msg.ns_filter) buf_size += ns.size() + 8;
    std::vector<uint8_t> buf(buf_size);

    cw_pack_context pc;
    cw_pack_context_init(&pc, buf.data() + 1, buf_size - 1, nullptr);
    buf[0] = SYNC_REQUEST;

    cw_pack_map_size(&pc, 3);

    /* protocol version */
    cw_pack_str(&pc, "pv", 2);
    cw_pack_unsigned(&pc, msg.protocol_version);

    /* vv */
    cw_pack_str(&pc, "vv", 2);
    cw_pack_map_size(&pc, (unsigned)msg.vv.size());
    for (auto &[author, seq] : msg.vv) {
        cw_pack_bin(&pc, author.data(), 32);
        cw_pack_unsigned(&pc, seq);
    }

    /* ns filter */
    cw_pack_str(&pc, "ns", 2);
    cw_pack_array_size(&pc, (unsigned)msg.ns_filter.size());
    for (auto &ns : msg.ns_filter) {
        cw_pack_str(&pc, ns.data(), (unsigned)ns.size());
    }

    if (pc.return_code != CWP_RC_OK) return {};

    size_t total = 1 + (size_t)(pc.current - (buf.data() + 1));
    buf.resize(total);
    return buf;
}

std::vector<uint8_t> encode_sync_entry(const SyncEntry &entry) {
    size_t buf_size = 512 + entry.ns.size() + entry.key.size() + entry.value.size();
    std::vector<uint8_t> buf(buf_size);
    cw_pack_context pc;
    cw_pack_context_init(&pc, buf.data() + 1, buf_size - 1, nullptr);
    buf[0] = SYNC_ENTRY;

    pack_entry_fields(&pc, entry);

    if (pc.return_code != CWP_RC_OK) return {};

    size_t total = 1 + (size_t)(pc.current - (buf.data() + 1));
    buf.resize(total);
    return buf;
}

std::vector<uint8_t> encode_sync_done() {
    return {SYNC_DONE};
}

std::vector<uint8_t> encode_sync_ack(const SyncAck &ack) {
    uint8_t buf[256];
    cw_pack_context pc;
    cw_pack_context_init(&pc, buf + 1, sizeof(buf) - 1, nullptr);
    buf[0] = SYNC_ACK;

    cw_pack_map_size(&pc, 2);
    cw_pack_str(&pc, "a", 1);
    cw_pack_bin(&pc, ack.author, 32);
    cw_pack_str(&pc, "seq", 3);
    cw_pack_unsigned(&pc, ack.seq);

    if (pc.return_code != CWP_RC_OK) return {};

    size_t total = 1 + (size_t)(pc.current - (buf + 1));
    return std::vector<uint8_t>(buf, buf + total);
}

std::vector<uint8_t> encode_live_entry(const SyncEntry &entry) {
    auto buf = encode_sync_entry(entry);
    if (!buf.empty()) buf[0] = LIVE_ENTRY;
    return buf;
}

/* --- Decode helpers ------------------------------------------------------ */

bool decode_message_type(const uint8_t *data, size_t len, WireMessageType *type_out) {
    if (!data || len < 1) return false;
    uint8_t t = data[0];
    if (t < SYNC_REQUEST || t > LIVE_ENTRY) return false;
    *type_out = static_cast<WireMessageType>(t);
    return true;
}

static bool decode_entry_from_map(cw_unpack_context *uc, SyncEntry *out) {
    cw_unpack_next(uc);
    if (uc->return_code != CWP_RC_OK) return false;
    if (uc->item.type != CWP_ITEM_MAP) return false;
    unsigned map_size = uc->item.as.map.size;

    std::memset(out->author, 0, 32);
    std::memset(out->hash, 0, 32);
    out->tombstone = 0;
    out->timestamp_us = 0;
    out->seq = 0;
    out->ns.clear();
    out->key.clear();
    out->value.clear();

    for (unsigned i = 0; i < map_size; i++) {
        cw_unpack_next(uc);
        if (uc->return_code != CWP_RC_OK) return false;
        if (uc->item.type != CWP_ITEM_STR) return false;
        std::string field((const char*)uc->item.as.str.start, uc->item.as.str.length);

        cw_unpack_next(uc);
        if (uc->return_code != CWP_RC_OK) return false;

        if (field == "ns") {
            if (uc->item.type != CWP_ITEM_STR) return false;
            out->ns.assign((const char*)uc->item.as.str.start, uc->item.as.str.length);
        } else if (field == "k") {
            if (uc->item.type != CWP_ITEM_BIN) return false;
            out->key.assign((const uint8_t*)uc->item.as.bin.start,
                           (const uint8_t*)uc->item.as.bin.start + uc->item.as.bin.length);
        } else if (field == "v") {
            if (uc->item.type == CWP_ITEM_NIL) {
                out->value.clear();
            } else if (uc->item.type == CWP_ITEM_BIN) {
                out->value.assign((const uint8_t*)uc->item.as.bin.start,
                                 (const uint8_t*)uc->item.as.bin.start + uc->item.as.bin.length);
            } else {
                return false;
            }
        } else if (field == "ts") {
            if (uc->item.type == CWP_ITEM_POSITIVE_INTEGER) {
                out->timestamp_us = uc->item.as.u64;
            } else {
                return false;
            }
        } else if (field == "a") {
            if (uc->item.type != CWP_ITEM_BIN || uc->item.as.bin.length != 32) return false;
            std::memcpy(out->author, uc->item.as.bin.start, 32);
        } else if (field == "seq") {
            if (uc->item.type == CWP_ITEM_POSITIVE_INTEGER) {
                out->seq = uc->item.as.u64;
            } else {
                return false;
            }
        } else if (field == "h") {
            if (uc->item.type != CWP_ITEM_BIN || uc->item.as.bin.length != 32) return false;
            std::memcpy(out->hash, uc->item.as.bin.start, 32);
        } else if (field == "t") {
            if (uc->item.type == CWP_ITEM_POSITIVE_INTEGER) {
                out->tombstone = (uint8_t)uc->item.as.u64;
            } else {
                return false;
            }
        }
        /* skip unknown fields */
    }
    return true;
}

bool decode_sync_request(const uint8_t *data, size_t len, SyncRequest *out) {
    if (!data || len < 2 || data[0] != SYNC_REQUEST) return false;

    cw_unpack_context uc;
    cw_unpack_context_init(&uc, data + 1, (unsigned long)(len - 1), nullptr);

    cw_unpack_next(&uc);
    if (uc.return_code != CWP_RC_OK || uc.item.type != CWP_ITEM_MAP) return false;
    unsigned map_size = uc.item.as.map.size;

    out->protocol_version = 0;
    out->vv.clear();
    out->ns_filter.clear();

    for (unsigned i = 0; i < map_size; i++) {
        cw_unpack_next(&uc);
        if (uc.return_code != CWP_RC_OK || uc.item.type != CWP_ITEM_STR) return false;
        std::string field((const char*)uc.item.as.str.start, uc.item.as.str.length);

        if (field == "pv") {
            cw_unpack_next(&uc);
            if (uc.return_code != CWP_RC_OK || uc.item.type != CWP_ITEM_POSITIVE_INTEGER)
                return false;
            out->protocol_version = (uint8_t)uc.item.as.u64;
        } else if (field == "vv") {
            cw_unpack_next(&uc);
            if (uc.return_code != CWP_RC_OK || uc.item.type != CWP_ITEM_MAP) return false;
            unsigned vv_size = uc.item.as.map.size;
            for (unsigned j = 0; j < vv_size; j++) {
                cw_unpack_next(&uc);
                if (uc.return_code != CWP_RC_OK || uc.item.type != CWP_ITEM_BIN
                    || uc.item.as.bin.length != 32)
                    return false;
                std::string author((const char*)uc.item.as.bin.start, 32);

                cw_unpack_next(&uc);
                if (uc.return_code != CWP_RC_OK || uc.item.type != CWP_ITEM_POSITIVE_INTEGER)
                    return false;
                out->vv[author] = uc.item.as.u64;
            }
        } else if (field == "ns") {
            cw_unpack_next(&uc);
            if (uc.return_code != CWP_RC_OK || uc.item.type != CWP_ITEM_ARRAY) return false;
            unsigned arr_size = uc.item.as.array.size;
            for (unsigned j = 0; j < arr_size; j++) {
                cw_unpack_next(&uc);
                if (uc.return_code != CWP_RC_OK || uc.item.type != CWP_ITEM_STR) return false;
                out->ns_filter.emplace_back((const char*)uc.item.as.str.start,
                                           uc.item.as.str.length);
            }
        } else {
            /* skip unknown value */
            cw_unpack_next(&uc);
        }
    }
    return true;
}

bool decode_sync_entry(const uint8_t *data, size_t len, SyncEntry *out) {
    if (!data || len < 2 || data[0] != SYNC_ENTRY) return false;

    cw_unpack_context uc;
    cw_unpack_context_init(&uc, data + 1, (unsigned long)(len - 1), nullptr);
    return decode_entry_from_map(&uc, out);
}

bool decode_sync_done(const uint8_t *data, size_t len) {
    return data && len >= 1 && data[0] == SYNC_DONE;
}

bool decode_sync_ack(const uint8_t *data, size_t len, SyncAck *out) {
    if (!data || len < 2 || data[0] != SYNC_ACK) return false;

    cw_unpack_context uc;
    cw_unpack_context_init(&uc, data + 1, (unsigned long)(len - 1), nullptr);

    cw_unpack_next(&uc);
    if (uc.return_code != CWP_RC_OK || uc.item.type != CWP_ITEM_MAP) return false;
    unsigned map_size = uc.item.as.map.size;

    std::memset(out->author, 0, 32);
    out->seq = 0;

    for (unsigned i = 0; i < map_size; i++) {
        cw_unpack_next(&uc);
        if (uc.return_code != CWP_RC_OK || uc.item.type != CWP_ITEM_STR) return false;
        std::string field((const char*)uc.item.as.str.start, uc.item.as.str.length);

        cw_unpack_next(&uc);
        if (uc.return_code != CWP_RC_OK) return false;

        if (field == "a") {
            if (uc.item.type != CWP_ITEM_BIN || uc.item.as.bin.length != 32) return false;
            std::memcpy(out->author, uc.item.as.bin.start, 32);
        } else if (field == "seq") {
            if (uc.item.type != CWP_ITEM_POSITIVE_INTEGER) return false;
            out->seq = uc.item.as.u64;
        }
    }
    return true;
}

bool decode_live_entry(const uint8_t *data, size_t len, SyncEntry *out) {
    if (!data || len < 2 || data[0] != LIVE_ENTRY) return false;

    cw_unpack_context uc;
    cw_unpack_context_init(&uc, data + 1, (unsigned long)(len - 1), nullptr);
    return decode_entry_from_map(&uc, out);
}

} /* namespace kome */
