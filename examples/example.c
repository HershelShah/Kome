/* example.c — minimal end-to-end use of the convergent core (M1).
 *
 * Demonstrates: create two replicas, write independently, exchange full state
 * via export/apply, and observe both converge to an identical digest. */
#include <stdio.h>
#include <string.h>

#include "sync_engine.h"

static void hex(const uint8_t *p, size_t n) {
    for (size_t i = 0; i < n; i++) printf("%02x", p[i]);
}

static int digests_equal(sync_engine *a, sync_engine *b) {
    uint8_t da[SYNC_DIGEST_LEN], db[SYNC_DIGEST_LEN];
    sync_engine_digest(a, da);
    sync_engine_digest(b, db);
    return memcmp(da, db, SYNC_DIGEST_LEN) == 0;
}

/* Export every record of `from` and apply them all into `into`. */
static int replicate(sync_engine *from, sync_engine *into) {
    sync_change *recs = NULL;
    size_t n = 0;
    int rc = sync_engine_export(from, &recs, &n);
    if (rc != SYNC_OK) return rc;
    for (size_t i = 0; i < n; i++) {
        rc = sync_engine_apply(into, &recs[i]);
        if (rc != SYNC_OK) break;
    }
    sync_changes_free(recs, n);
    return rc;
}

int main(void) {
    uint8_t id_a[SYNC_SITE_ID_LEN], id_b[SYNC_SITE_ID_LEN];
    memset(id_a, 0xA1, sizeof id_a);
    memset(id_b, 0xB2, sizeof id_b);

    sync_engine *a = sync_engine_create(id_a);
    sync_engine *b = sync_engine_create(id_b);

    sync_engine_set(a, (const uint8_t *)"people", 6,
                    (const uint8_t *)"alice", 5,
                    (const uint8_t *)"name", 4,
                    (const uint8_t *)"Alice", 5);
    sync_engine_set(b, (const uint8_t *)"people", 6,
                    (const uint8_t *)"bob", 3,
                    (const uint8_t *)"name", 4,
                    (const uint8_t *)"Bob", 3);

    /* Exchange full state both ways. */
    replicate(a, b);
    replicate(b, a);

    uint8_t *val = NULL;
    size_t len = 0;
    if (sync_engine_get(a, (const uint8_t *)"people", 6,
                        (const uint8_t *)"bob", 3,
                        (const uint8_t *)"name", 4, &val, &len) == SYNC_OK) {
        printf("A sees people/bob/name = %.*s\n", (int)len, (char *)val);
        sync_free(val);
    }

    uint8_t dig[SYNC_DIGEST_LEN];
    sync_engine_digest(a, dig);
    printf("digest = ");
    hex(dig, SYNC_DIGEST_LEN);
    printf("\n");

    printf("converged: %s\n", digests_equal(a, b) ? "yes" : "no");

    sync_engine_destroy(a);
    sync_engine_destroy(b);
    return 0;
}
