#include <gtest/gtest.h>
#include "kome_wire.hpp"
#include <cstring>

using namespace kome;

/* --- SyncRequest round-trip ---------------------------------------------- */

TEST(WireTest, SyncRequestRoundTrip) {
    SyncRequest req;
    req.protocol_version = KOME_PROTOCOL_VERSION;
    uint8_t author1[32], author2[32];
    std::memset(author1, 0x11, 32);
    std::memset(author2, 0x22, 32);
    req.vv[std::string((const char*)author1, 32)] = 42;
    req.vv[std::string((const char*)author2, 32)] = 100;
    req.ns_filter.push_back("contacts");
    req.ns_filter.push_back("calendar");

    auto encoded = encode_sync_request(req);
    ASSERT_FALSE(encoded.empty());
    ASSERT_EQ(SYNC_REQUEST, encoded[0]);

    SyncRequest decoded;
    ASSERT_TRUE(decode_sync_request(encoded.data(), encoded.size(), &decoded));
    EXPECT_EQ(KOME_PROTOCOL_VERSION, decoded.protocol_version);
    EXPECT_EQ(2u, decoded.vv.size());
    EXPECT_EQ(42u, decoded.vv[std::string((const char*)author1, 32)]);
    EXPECT_EQ(100u, decoded.vv[std::string((const char*)author2, 32)]);
    EXPECT_EQ(2u, decoded.ns_filter.size());
    EXPECT_EQ("contacts", decoded.ns_filter[0]);
    EXPECT_EQ("calendar", decoded.ns_filter[1]);
}

TEST(WireTest, SyncRequestEmpty) {
    SyncRequest req;
    auto encoded = encode_sync_request(req);
    SyncRequest decoded;
    ASSERT_TRUE(decode_sync_request(encoded.data(), encoded.size(), &decoded));
    EXPECT_TRUE(decoded.vv.empty());
    EXPECT_TRUE(decoded.ns_filter.empty());
}

/* --- SyncEntry round-trip ------------------------------------------------ */

TEST(WireTest, SyncEntryRoundTrip) {
    SyncEntry entry;
    entry.ns = "contacts";
    entry.key = {1, 2, 3, 4};
    entry.value = {10, 20, 30, 40, 50};
    entry.timestamp_us = 1234567890;
    std::memset(entry.author, 0xAA, 32);
    entry.seq = 7;
    std::memset(entry.hash, 0xBB, 32);
    entry.tombstone = 0;

    auto encoded = encode_sync_entry(entry);
    ASSERT_FALSE(encoded.empty());
    ASSERT_EQ(SYNC_ENTRY, encoded[0]);

    SyncEntry decoded;
    ASSERT_TRUE(decode_sync_entry(encoded.data(), encoded.size(), &decoded));
    EXPECT_EQ("contacts", decoded.ns);
    EXPECT_EQ(entry.key, decoded.key);
    EXPECT_EQ(entry.value, decoded.value);
    EXPECT_EQ(1234567890u, decoded.timestamp_us);
    EXPECT_EQ(0, std::memcmp(entry.author, decoded.author, 32));
    EXPECT_EQ(7u, decoded.seq);
    EXPECT_EQ(0, std::memcmp(entry.hash, decoded.hash, 32));
    EXPECT_EQ(0, decoded.tombstone);
}

TEST(WireTest, SyncEntryTombstone) {
    SyncEntry entry;
    entry.ns = "test";
    entry.key = {1};
    entry.value.clear();
    entry.timestamp_us = 999;
    std::memset(entry.author, 0x11, 32);
    entry.seq = 1;
    std::memset(entry.hash, 0, 32);
    entry.tombstone = 1;

    auto encoded = encode_sync_entry(entry);
    SyncEntry decoded;
    ASSERT_TRUE(decode_sync_entry(encoded.data(), encoded.size(), &decoded));
    EXPECT_EQ(1, decoded.tombstone);
    EXPECT_TRUE(decoded.value.empty());
}

/* --- SyncDone ------------------------------------------------------------ */

TEST(WireTest, SyncDoneRoundTrip) {
    auto encoded = encode_sync_done();
    ASSERT_EQ(1u, encoded.size());
    ASSERT_EQ(SYNC_DONE, encoded[0]);
    ASSERT_TRUE(decode_sync_done(encoded.data(), encoded.size()));
}

/* --- SyncAck round-trip -------------------------------------------------- */

TEST(WireTest, SyncAckRoundTrip) {
    SyncAck ack;
    std::memset(ack.author, 0xCC, 32);
    ack.seq = 42;

    auto encoded = encode_sync_ack(ack);
    ASSERT_FALSE(encoded.empty());
    ASSERT_EQ(SYNC_ACK, encoded[0]);

    SyncAck decoded;
    ASSERT_TRUE(decode_sync_ack(encoded.data(), encoded.size(), &decoded));
    EXPECT_EQ(0, std::memcmp(ack.author, decoded.author, 32));
    EXPECT_EQ(42u, decoded.seq);
}

/* --- LiveEntry round-trip ------------------------------------------------ */

TEST(WireTest, LiveEntryRoundTrip) {
    SyncEntry entry;
    entry.ns = "live";
    entry.key = {9, 8, 7};
    entry.value = {1, 2, 3};
    entry.timestamp_us = 55555;
    std::memset(entry.author, 0xDD, 32);
    entry.seq = 3;
    std::memset(entry.hash, 0xEE, 32);
    entry.tombstone = 0;

    auto encoded = encode_live_entry(entry);
    ASSERT_EQ(LIVE_ENTRY, encoded[0]);

    SyncEntry decoded;
    ASSERT_TRUE(decode_live_entry(encoded.data(), encoded.size(), &decoded));
    EXPECT_EQ("live", decoded.ns);
    EXPECT_EQ(entry.key, decoded.key);
    EXPECT_EQ(3u, decoded.seq);
}

/* --- Edge cases ---------------------------------------------------------- */

TEST(WireTest, DecodeNullData) {
    WireMessageType t;
    EXPECT_FALSE(decode_message_type(nullptr, 0, &t));
}

TEST(WireTest, DecodeEmptyData) {
    uint8_t data[1] = {0};
    WireMessageType t;
    EXPECT_FALSE(decode_message_type(data, 0, &t));
}

TEST(WireTest, DecodeInvalidType) {
    uint8_t data[] = {0xFF};
    WireMessageType t;
    EXPECT_FALSE(decode_message_type(data, 1, &t));
}

TEST(WireTest, DecodeTruncatedSyncEntry) {
    uint8_t data[] = {SYNC_ENTRY, 0x00};
    SyncEntry entry;
    EXPECT_FALSE(decode_sync_entry(data, 2, &entry));
}

TEST(WireTest, DecodeTruncatedSyncRequest) {
    uint8_t data[] = {SYNC_REQUEST};
    SyncRequest req;
    EXPECT_FALSE(decode_sync_request(data, 1, &req));
}

/* --- BatchEntry round-trip ----------------------------------------------- */

TEST(WireTest, BatchEntryRoundTrip) {
    std::vector<SyncEntry> entries(3);
    for (int i = 0; i < 3; i++) {
        entries[i].ns = "batch_ns";
        entries[i].key = {(uint8_t)(i + 1)};
        entries[i].value = {(uint8_t)(i + 10), (uint8_t)(i + 20)};
        entries[i].timestamp_us = 1000000 + i;
        std::memset(entries[i].author, 0xAA + i, 32);
        entries[i].seq = i + 1;
        std::memset(entries[i].hash, 0xCC + i, 32);
        entries[i].tombstone = 0;
    }

    auto encoded = encode_batch_entry(entries);
    ASSERT_FALSE(encoded.empty());
    ASSERT_EQ(BATCH_ENTRY, encoded[0]);

    std::vector<SyncEntry> decoded;
    ASSERT_TRUE(decode_batch_entry(encoded.data(), encoded.size(), &decoded));
    ASSERT_EQ(3u, decoded.size());

    for (int i = 0; i < 3; i++) {
        EXPECT_EQ("batch_ns", decoded[i].ns);
        EXPECT_EQ(entries[i].key, decoded[i].key);
        EXPECT_EQ(entries[i].value, decoded[i].value);
        EXPECT_EQ(entries[i].timestamp_us, decoded[i].timestamp_us);
        EXPECT_EQ(0, std::memcmp(entries[i].author, decoded[i].author, 32));
        EXPECT_EQ(entries[i].seq, decoded[i].seq);
        EXPECT_EQ(0, std::memcmp(entries[i].hash, decoded[i].hash, 32));
        EXPECT_EQ(0, decoded[i].tombstone);
    }
}

TEST(WireTest, BatchEntryEmpty) {
    std::vector<SyncEntry> entries;
    auto encoded = encode_batch_entry(entries);
    ASSERT_FALSE(encoded.empty());

    std::vector<SyncEntry> decoded;
    ASSERT_TRUE(decode_batch_entry(encoded.data(), encoded.size(), &decoded));
    EXPECT_TRUE(decoded.empty());
}

TEST(WireTest, BatchEntryWithTombstone) {
    std::vector<SyncEntry> entries(2);
    entries[0].ns = "ns";
    entries[0].key = {1};
    entries[0].value = {10, 20};
    entries[0].timestamp_us = 100;
    std::memset(entries[0].author, 0x11, 32);
    entries[0].seq = 1;
    std::memset(entries[0].hash, 0x22, 32);
    entries[0].tombstone = 0;

    entries[1].ns = "ns";
    entries[1].key = {2};
    entries[1].value.clear();
    entries[1].timestamp_us = 200;
    std::memset(entries[1].author, 0x11, 32);
    entries[1].seq = 2;
    std::memset(entries[1].hash, 0, 32);
    entries[1].tombstone = 1;

    auto encoded = encode_batch_entry(entries);
    std::vector<SyncEntry> decoded;
    ASSERT_TRUE(decode_batch_entry(encoded.data(), encoded.size(), &decoded));
    ASSERT_EQ(2u, decoded.size());
    EXPECT_EQ(0, decoded[0].tombstone);
    EXPECT_EQ(1, decoded[1].tombstone);
    EXPECT_TRUE(decoded[1].value.empty());
}

TEST(WireTest, DecodeBatchEntryInvalid) {
    /* Wrong type byte */
    uint8_t data[] = {LIVE_ENTRY, 0x00};
    std::vector<SyncEntry> out;
    EXPECT_FALSE(decode_batch_entry(data, 2, &out));

    /* Null data */
    EXPECT_FALSE(decode_batch_entry(nullptr, 0, &out));
}

TEST(WireTest, MessageTypeBatchEntry) {
    uint8_t data[] = {BATCH_ENTRY};
    WireMessageType t;
    ASSERT_TRUE(decode_message_type(data, 1, &t));
    EXPECT_EQ(BATCH_ENTRY, t);
}
