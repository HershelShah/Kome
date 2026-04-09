/**
 * Multi-node simulation tests.
 *
 * These tests spin up 3–5 Kome engines in one process, connected via
 * loopback transports in various topologies (chain, mesh, star), and
 * verify that data converges correctly across all nodes.
 *
 * This simulates the real-world scenario of multiple servers/devices
 * syncing over a network — the same sync protocol runs, just with
 * in-memory transport instead of TCP/WebSocket.
 */
#include <gtest/gtest.h>
#include "kome.h"
#include "kome_test_helpers.hpp"
#include <cstring>
#include <string>
#include <vector>
#include <map>
#include <memory>
#include <thread>
#include <chrono>
#include <set>

/* ── Helpers ─────────────────────────────────────────────────────────── */

struct Node {
    std::string   db_path;
    KomeEngine   *engine = nullptr;
    uint8_t       fp[32] = {};  /* identity fingerprint (filled after set_identity) */

    ~Node() {
        if (engine) kome_close(engine);
        cleanup_db(db_path);
    }
};

struct Link {
    std::unique_ptr<LoopbackPair> loopback;

    Link() : loopback(std::make_unique<LoopbackPair>()) {}

    void disable() {
        if (loopback) {
            loopback->a.other = nullptr;
            loopback->b.other = nullptr;
        }
    }
};

/* Track all links to keep them alive, and active link per engine
   so we can disable the old one when a node reattaches. */
static std::vector<std::shared_ptr<Link>> g_all_links;
static std::map<KomeEngine*, std::shared_ptr<Link>> g_active_link;

static Node make_node(const char *name, uint8_t id_byte) {
    Node n;
    n.db_path = temp_db_path(name);
    cleanup_db(n.db_path);
    KomeConfig cfg = {};
    cfg.path = n.db_path.c_str();
    EXPECT_EQ(KOME_OK, kome_open(&cfg, &n.engine));

    uint8_t key[32];
    std::memset(key, id_byte, 32);
    EXPECT_EQ(KOME_OK, kome_set_identity(n.engine, key, 32));

    /* Read back the fingerprint */
    KomeEntryMeta m;
    uint8_t tmp_key[] = "__fp_probe__";
    uint8_t tmp_val[] = "x";
    kome_put(n.engine, "__sys", tmp_key, 12, tmp_val, 1, &m);
    std::memcpy(n.fp, m.author, 32);
    kome_delete(n.engine, "__sys", tmp_key, 12, nullptr);

    return n;
}

static std::shared_ptr<Link> connect_nodes(Node &a, Node &b) {
    /* Disable any existing links for these nodes */
    if (g_active_link.count(a.engine)) g_active_link[a.engine]->disable();
    if (g_active_link.count(b.engine)) g_active_link[b.engine]->disable();

    auto link = std::make_shared<Link>();
    std::memcpy(link->loopback->a.fingerprint, a.fp, 32);
    std::memcpy(link->loopback->b.fingerprint, b.fp, 32);
    EXPECT_EQ(KOME_OK, kome_attach_transport(a.engine, &link->loopback->a.transport));
    EXPECT_EQ(KOME_OK, kome_attach_transport(b.engine, &link->loopback->b.transport));
    link->loopback->connect();
    g_active_link[a.engine] = link;
    g_active_link[b.engine] = link;
    g_all_links.push_back(link);
    return link;
}

static void put(Node &n, const char *ns, const char *key, const char *val) {
    ASSERT_EQ(KOME_OK, kome_put(n.engine, ns,
        (const uint8_t*)key, std::strlen(key),
        (const uint8_t*)val, std::strlen(val), nullptr));
}

static std::string get_val(Node &n, const char *ns, const char *key) {
    uint8_t *out = nullptr;
    size_t len = 0;
    KomeError err = kome_get(n.engine, ns,
        (const uint8_t*)key, std::strlen(key), &out, &len, nullptr);
    if (err != KOME_OK) return "";
    std::string result((const char*)out, len);
    kome_free_value(out);
    return result;
}

static bool has_key(Node &n, const char *ns, const char *key) {
    KomeEntryMeta meta;
    return kome_get_meta(n.engine, ns,
        (const uint8_t*)key, std::strlen(key), &meta) == KOME_OK;
}

/* ── Test: 3-node chain  A ↔ B ↔ C ─────────────────────────────────── */

TEST(MultiNode, ChainTopologyConverges) {
    /* A writes, syncs to B, B relays to C via gossip.
       All 3 nodes should converge. */
    auto A = make_node("chain_a", 0xA1);
    auto B = make_node("chain_b", 0xB2);
    auto C = make_node("chain_c", 0xC3);

    /* A writes data before any connections */
    put(A, "chat", "msg1", "hello from A");
    put(A, "chat", "msg2", "second from A");

    /* Connect A ↔ B (syncs A's data to B) */
    [[maybe_unused]] auto ab = connect_nodes(A, B);

    EXPECT_EQ("hello from A", get_val(B, "chat", "msg1"));
    EXPECT_EQ("second from A", get_val(B, "chat", "msg2"));

    /* Connect B ↔ C (B relays A's data to C via initial sync) */
    [[maybe_unused]] auto bc = connect_nodes(B, C);

    EXPECT_EQ("hello from A", get_val(C, "chat", "msg1"));
    EXPECT_EQ("second from A", get_val(C, "chat", "msg2"));
}

/* ── Test: Concurrent writes from different nodes ───────────────────── */

TEST(MultiNode, ConcurrentWritesConverge) {
    /* A and B both write, then connect. Each engine supports one
       transport at a time, so we test pairwise convergence. */
    auto A = make_node("conc_a", 0xA1);
    auto B = make_node("conc_b", 0xB2);

    put(A, "shared", "from_a", "value_a");
    put(B, "shared", "from_b", "value_b");

    [[maybe_unused]] auto ab = connect_nodes(A, B);
    EXPECT_EQ("value_a", get_val(B, "shared", "from_a"));
    EXPECT_EQ("value_b", get_val(A, "shared", "from_b"));
}

/* ── Test: Conflict resolution across 2 nodes ──────────────────────── */

TEST(MultiNode, ConflictResolutionAcrossNodes) {
    /* A writes first, B writes later with higher timestamp.
       After sync, both should converge to B's value (LWW). */
    auto A = make_node("cflct_a", 0xA1);
    auto B = make_node("cflct_b", 0xB2);

    put(A, "ns", "contested", "from_a");
    std::this_thread::sleep_for(std::chrono::milliseconds(2));
    put(B, "ns", "contested", "from_b");

    [[maybe_unused]] auto ab = connect_nodes(A, B);

    /* Both should converge to B's value (later timestamp) */
    EXPECT_EQ("from_b", get_val(A, "ns", "contested"));
    EXPECT_EQ("from_b", get_val(B, "ns", "contested"));
}

/* ── Test: Namespace-scoped sync across 3 nodes ─────────────────────── */

TEST(MultiNode, NamespaceScopingAcrossNodes) {
    /* A syncs "chat" + "media", B syncs "chat" + "status", C syncs all.
       Verify each node only gets the namespaces in its intersection. */
    auto A = make_node("nsscope_a", 0xA1);
    auto B = make_node("nsscope_b", 0xB2);
    auto C = make_node("nsscope_c", 0xC3);

    const char *a_ns[] = {"chat", "media"};
    const char *b_ns[] = {"chat", "status"};
    kome_set_sync_namespaces(A.engine, a_ns, 2);
    kome_set_sync_namespaces(B.engine, b_ns, 2);
    /* C has no filter → syncs everything */

    put(A, "chat", "msg", "hello");
    put(A, "media", "photo", "jpeg_data");
    put(B, "status", "mood", "happy");

    /* A ↔ B: intersection is {"chat"} */
    [[maybe_unused]] auto ab = connect_nodes(A, B);
    EXPECT_TRUE(has_key(B, "chat", "msg"));     /* chat is in intersection */
    EXPECT_FALSE(has_key(B, "media", "photo")); /* media not in B's filter */
    EXPECT_FALSE(has_key(A, "status", "mood")); /* status not in A's filter */

    /* B ↔ C: intersection is {"chat", "status"} (C has no filter → all) */
    [[maybe_unused]] auto bc = connect_nodes(B, C);
    EXPECT_TRUE(has_key(C, "chat", "msg"));     /* chat from B */
    EXPECT_TRUE(has_key(C, "status", "mood"));  /* status from B */
    EXPECT_FALSE(has_key(C, "media", "photo")); /* media never left A */
}

/* ── Test: Entry TTL across nodes ───────────────────────────────────── */

TEST(MultiNode, TTLRejectsExpiredAcrossNodes) {
    /* A writes an entry. B has a 1-second TTL. After TTL expires,
       B should reject the entry during sync. */
    auto A = make_node("ttl_a", 0xA1);
    auto B = make_node("ttl_b", 0xB2);

    kome_set_entry_ttl(B.engine, "ephemeral", 1);

    put(A, "ephemeral", "old_msg", "stale");
    put(A, "persistent", "keep", "forever");

    /* Wait for TTL to expire */
    std::this_thread::sleep_for(std::chrono::milliseconds(1100));

    [[maybe_unused]] auto ab = connect_nodes(A, B);

    /* B should reject the expired entry but accept the persistent one */
    EXPECT_FALSE(has_key(B, "ephemeral", "old_msg"));
    EXPECT_TRUE(has_key(B, "persistent", "keep"));
}

/* ── Test: Batch writes propagate through mesh ──────────────────────── */

TEST(MultiNode, BatchWritesSyncToPeer) {
    /* A writes a batch, syncs to B. B should have all 3 entries. */
    auto A = make_node("batch_a", 0xA1);
    auto B = make_node("batch_b", 0xB2);

    KomeBatchEntry entries[3];
    uint8_t k0[] = "k0", k1[] = "k1", k2[] = "k2";
    uint8_t v0[] = "val0", v1[] = "val1", v2[] = "val2";
    entries[0] = {"batch", k0, 2, v0, 4};
    entries[1] = {"batch", k1, 2, v1, 4};
    entries[2] = {"batch", k2, 2, v2, 4};
    ASSERT_EQ(KOME_OK, kome_put_batch(A.engine, entries, 3, nullptr));

    [[maybe_unused]] auto ab = connect_nodes(A, B);

    EXPECT_EQ("val0", get_val(B, "batch", "k0"));
    EXPECT_EQ("val1", get_val(B, "batch", "k1"));
    EXPECT_EQ("val2", get_val(B, "batch", "k2"));
}

/* ── Test: Delete propagates as tombstone ────────────────────────────── */

TEST(MultiNode, DeletePropagatesAcrossNodes) {
    auto A = make_node("del_a", 0xA1);
    auto B = make_node("del_b", 0xB2);

    put(A, "ns", "doomed", "will be deleted");
    [[maybe_unused]] auto ab = connect_nodes(A, B);

    /* B has the entry */
    EXPECT_TRUE(has_key(B, "ns", "doomed"));

    /* A deletes it — should push tombstone to B */
    kome_delete(A.engine, "ns", (const uint8_t*)"doomed", 6, nullptr);

    /* B should no longer find it */
    uint8_t *out = nullptr;
    size_t len = 0;
    EXPECT_EQ(KOME_ERR_NOT_FOUND, kome_get(B.engine, "ns",
        (const uint8_t*)"doomed", 6, &out, &len, nullptr));
}

/* ── Test: Sequential star sync ──────────────────────────────────────── */

TEST(MultiNode, SequentialStarConvergesViaHub) {
    /* Hub syncs with each spoke one at a time. Each engine supports one
       transport at a time, so the hub connects to each spoke sequentially.
       After all rounds, hub has everything and each spoke got whatever
       the hub had at the time they connected. */
    auto H  = make_node("star_h",  0x00);
    auto S1 = make_node("star_s1", 0x11);
    auto S2 = make_node("star_s2", 0x22);
    auto S3 = make_node("star_s3", 0x33);

    /* Each spoke writes before connecting */
    put(S1, "data", "from_s1", "spoke1");
    put(S2, "data", "from_s2", "spoke2");
    put(S3, "data", "from_s3", "spoke3");

    /* Hub ↔ S1: hub gets S1's data */
    { [[maybe_unused]] auto l = connect_nodes(H, S1); }
    EXPECT_EQ("spoke1", get_val(H, "data", "from_s1"));

    /* Hub ↔ S2: hub gets S2's data, S2 gets S1's data via hub */
    { [[maybe_unused]] auto l = connect_nodes(H, S2); }
    EXPECT_EQ("spoke2", get_val(H, "data", "from_s2"));
    EXPECT_EQ("spoke1", get_val(S2, "data", "from_s1"));

    /* Hub ↔ S3: hub gets S3's data, S3 gets S1+S2 data via hub */
    { [[maybe_unused]] auto l = connect_nodes(H, S3); }
    EXPECT_EQ("spoke3", get_val(H, "data", "from_s3"));
    EXPECT_EQ("spoke1", get_val(S3, "data", "from_s1"));
    EXPECT_EQ("spoke2", get_val(S3, "data", "from_s2"));

    /* Hub has all 3 */
    EXPECT_EQ("spoke1", get_val(H, "data", "from_s1"));
    EXPECT_EQ("spoke2", get_val(H, "data", "from_s2"));
    EXPECT_EQ("spoke3", get_val(H, "data", "from_s3"));
}

/* ── Test: Sync-done callback fires for each peer ────────────────────── */

TEST(MultiNode, SyncDoneFiresPerPeer) {
    auto A = make_node("done_a", 0xA1);
    auto B = make_node("done_b", 0xB2);

    int done_count = 0;
    kome_on_sync_done(A.engine,
        [](void *ud, const uint8_t *) { (*static_cast<int*>(ud))++; },
        &done_count);

    put(A, "ns", "k", "v");
    [[maybe_unused]] auto ab = connect_nodes(A, B);

    EXPECT_GE(done_count, 1) << "sync_done should fire at least once";
}

/* ── Test: Remote change callback fires across nodes ─────────────────── */

TEST(MultiNode, RemoteChangeCallbackFires) {
    auto A = make_node("rcb_a", 0xA1);
    auto B = make_node("rcb_b", 0xB2);

    struct Change {
        std::string ns;
        std::string key;
        std::string value;
    };
    std::vector<Change> changes;

    kome_on_remote_change(B.engine,
        [](void *ud, const char *ns, const uint8_t *key, size_t key_len,
           const uint8_t *value, size_t value_len, const KomeEntryMeta *) {
            auto *v = static_cast<std::vector<Change>*>(ud);
            v->push_back({ns, std::string((const char*)key, key_len),
                          std::string((const char*)value, value_len)});
        }, &changes);

    [[maybe_unused]] auto ab = connect_nodes(A, B);

    put(A, "chat", "msg1", "hello");
    put(A, "chat", "msg2", "world");

    ASSERT_EQ(2u, changes.size());
    EXPECT_EQ("chat", changes[0].ns);
    EXPECT_EQ("msg1", changes[0].key);
    EXPECT_EQ("hello", changes[0].value);
    EXPECT_EQ("msg2", changes[1].key);
    EXPECT_EQ("world", changes[1].value);
}
