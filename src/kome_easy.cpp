/*
 * KomeEasy — Simplified API implementation
 *
 * C++ implementation file, but the public API (kome_easy.h) is pure C.
 */
#include "kome_easy.h"
#include "kome_relay_transport.h"
#include "kome_util.hpp"

#include <cstdlib>
#include <cstring>
#include <new>

struct KomeEasy {
    KomeEngine    *engine;
    KomeTransport *transport;   /* NULL if local-only */
};

extern "C" {

KOME_API KomeError kome_easy_open(const char *db_path, const char *relay_url,
    const uint8_t *key_material, size_t key_len,
    KomeEasy **out)
{
    if (!db_path || !key_material || key_len == 0 || !out)
        return KOME_ERR_MISUSE;

    auto *easy = static_cast<KomeEasy*>(std::calloc(1, sizeof(KomeEasy)));
    if (!easy)
        return KOME_ERR_INTERNAL;

    /* Open engine */
    KomeConfig cfg{};
    cfg.path = db_path;

    KomeError err = kome_open(&cfg, &easy->engine);
    if (err != KOME_OK) {
        std::free(easy);
        return err;
    }

    /* Set identity */
    err = kome_set_identity(easy->engine, key_material, key_len);
    if (err != KOME_OK) {
        kome_close(easy->engine);
        std::free(easy);
        return err;
    }

    /* Create relay transport if URL is provided */
    if (relay_url) {
        /* Compute the fingerprint the same way kome_set_identity does:
         * SHA-256(key_material). We can call kome::sha256 directly since
         * this is a C++ translation unit. */
        uint8_t fp[32];
        kome::sha256(key_material, key_len, fp);

        err = kome_relay_transport_create(relay_url, fp, &easy->transport);
        if (err != KOME_OK) {
            /* Non-fatal: degrade to local-only mode */
            easy->transport = nullptr;
        } else {
            err = kome_attach_transport(easy->engine, easy->transport);
            if (err != KOME_OK) {
                kome_relay_transport_destroy(easy->transport);
                easy->transport = nullptr;
                /* Non-fatal: degrade to local-only */
            }
        }
    }

    *out = easy;
    return KOME_OK;
}

KOME_API void kome_easy_close(KomeEasy *easy) {
    if (!easy) return;

    /* Close engine first (detaches transport internally) */
    if (easy->engine) {
        kome_close(easy->engine);
        easy->engine = nullptr;
    }

    /* Destroy relay transport */
    if (easy->transport) {
        kome_relay_transport_destroy(easy->transport);
        easy->transport = nullptr;
    }

    std::free(easy);
}

KOME_API KomeError kome_easy_put(KomeEasy *easy, const char *ns,
    const uint8_t *key, size_t key_len,
    const uint8_t *value, size_t value_len)
{
    if (!easy || !easy->engine) return KOME_ERR_MISUSE;
    return kome_put(easy->engine, ns, key, key_len, value, value_len, nullptr);
}

KOME_API KomeError kome_easy_get(KomeEasy *easy, const char *ns,
    const uint8_t *key, size_t key_len,
    uint8_t **value_out, size_t *value_len_out)
{
    if (!easy || !easy->engine) return KOME_ERR_MISUSE;
    return kome_get(easy->engine, ns, key, key_len, value_out, value_len_out, nullptr);
}

KOME_API KomeError kome_easy_delete(KomeEasy *easy, const char *ns,
    const uint8_t *key, size_t key_len)
{
    if (!easy || !easy->engine) return KOME_ERR_MISUSE;
    return kome_delete(easy->engine, ns, key, key_len, nullptr);
}

KOME_API void kome_easy_on_change(KomeEasy *easy, KomeRemoteChangeCallback cb,
    void *ud)
{
    if (!easy || !easy->engine) return;
    kome_on_remote_change(easy->engine, cb, ud);
}

KOME_API KomeEngine *kome_easy_engine(KomeEasy *easy) {
    if (!easy) return nullptr;
    return easy->engine;
}

} /* extern "C" */
