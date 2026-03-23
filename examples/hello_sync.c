/*
 * hello_sync.c — Minimal Kome usage example
 *
 * Build:
 *   gcc -o hello_sync hello_sync.c -I../include -L../build -lkome
 *
 * Run:
 *   LD_LIBRARY_PATH=../build ./hello_sync
 */

#include "kome.h"
#include <stdio.h>
#include <string.h>

int main(void) {
    printf("Kome version: %s\n", kome_version());

    /* Open engine */
    KomeConfig cfg = {0};
    cfg.path = "hello.db";
    cfg.busy_timeout_ms = 5000;

    KomeEngine *engine = NULL;
    KomeError err = kome_open(&cfg, &engine);
    if (err != KOME_OK) {
        fprintf(stderr, "kome_open failed: %s\n", kome_errstr(err));
        return 1;
    }

    /* Set identity (in production, use a persistent key) */
    uint8_t key[32] = {0};
    memset(key, 0x42, sizeof(key));
    err = kome_set_identity(engine, key, sizeof(key));
    if (err != KOME_OK) {
        fprintf(stderr, "kome_set_identity failed: %s\n", kome_errstr(err));
        kome_close(engine);
        return 1;
    }

    /* Write some data */
    const char *ns = "contacts";
    uint8_t entry_key[] = "alice";
    uint8_t value[] = "{\"name\":\"Alice\",\"email\":\"alice@example.com\"}";

    KomeEntryMeta meta;
    err = kome_put(engine, ns, entry_key, 5, value, (uint32_t)strlen((char*)value), &meta);
    if (err != KOME_OK) {
        fprintf(stderr, "kome_put failed: %s\n", kome_errstr(err));
        kome_close(engine);
        return 1;
    }

    printf("Replicated entry: ns=%s key=alice seq=%lu ts=%lu\n",
           ns, (unsigned long)meta.seq, (unsigned long)meta.timestamp_us);

    /* Read it back */
    KomeEntryMeta read_meta;
    err = kome_get_meta(engine, ns, entry_key, 5, &read_meta);
    if (err == KOME_OK) {
        printf("Read back: seq=%lu value_len=%u tombstone=%d\n",
               (unsigned long)read_meta.seq, read_meta.value_len, read_meta.tombstone);
    }

    /* Stats */
    KomeStats stats;
    kome_stats(engine, &stats);
    printf("Stats: %lu entries, %lu namespaces, %lu bytes\n",
           (unsigned long)stats.total_entries,
           (unsigned long)stats.namespace_count,
           (unsigned long)stats.db_size_bytes);

    /* To sync with a peer, you would:
     * 1. Implement a KomeTransport (TCP, WebSocket, etc.)
     * 2. Call kome_attach_transport(engine, &my_transport)
     * 3. When a peer connects, fire the peer callback
     * 4. Sync happens automatically via the transport callbacks
     */

    kome_close(engine);
    printf("Done.\n");
    return 0;
}
