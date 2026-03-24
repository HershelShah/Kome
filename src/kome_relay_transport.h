/*
 * Kome HTTP relay transport — built-in transport using a central relay server.
 *
 * The relay protocol:
 *   POST /register  { "fingerprint": "aabb..." }
 *   POST /send      { "from": "aabb...", "to": "ccdd...", "data": "<base64>" }
 *   GET  /recv?fp=aabb...  -> [{ "id": N, "from": "...", "data": "..." }]
 *   POST /ack       { "fp": "...", "ids": [1, 2, 3] }
 *   GET  /peers     -> ["aabb...", "ccdd...", ...]
 *
 * Uses raw POSIX sockets — no external HTTP library dependencies.
 */
#ifndef KOME_RELAY_TRANSPORT_H
#define KOME_RELAY_TRANSPORT_H

#include "kome.h"

#ifdef __cplusplus
extern "C" {
#endif

/*
 * Create a relay transport that communicates via an HTTP relay server.
 *
 * relay_url:    e.g. "http://relay.example.com" or "http://127.0.0.1:8080"
 * fingerprint:  32-byte identity fingerprint (SHA-256 of key material)
 * out:          Receives the new KomeTransport on success.
 *               The caller must call kome_relay_transport_destroy() to free it.
 *
 * Returns KOME_OK on success.
 */
KOME_API KomeError kome_relay_transport_create(const char *relay_url,
    const uint8_t *fingerprint, KomeTransport **out);

/*
 * Destroy a relay transport created by kome_relay_transport_create().
 * Stops the background polling thread and frees all resources.
 * Safe to call with NULL.
 */
KOME_API void kome_relay_transport_destroy(KomeTransport *transport);

#ifdef __cplusplus
}
#endif

#endif /* KOME_RELAY_TRANSPORT_H */
