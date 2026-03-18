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
