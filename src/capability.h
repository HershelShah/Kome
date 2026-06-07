/* capability.h — capability tokens and verification (M4). Internal.
 *
 * A capability is a signed statement: (issuer, subject, namespace, access,
 * expiry, signature). A root has issuer == subject and declares the issuer the
 * owner of the namespace. Delegation is a signature chain rooted at the owner,
 * each hop narrowing access and re-signed by the previous subject.
 *
 * Enforcement is opt-in per namespace: a namespace is "owned" once a root
 * capability for it is granted. Unowned namespaces are open (any validly
 * signed record is accepted, any peer may read). */
#ifndef SYNC_CAPABILITY_H
#define SYNC_CAPABILITY_H

#include <cstdint>
#include <string>
#include <vector>

#include "engine.hpp"
#include "sync_engine.h"

namespace ke {

/* Access bits (match SYNC_ACCESS_* in the public header). */
constexpr uint8_t kAccessRead  = 1;
constexpr uint8_t kAccessWrite = 2;

struct Capability {
    PubKey      issuer{};
    PubKey      subject{};
    std::string ns;
    uint8_t     access = 0;   /* bitmask of kAccessRead | kAccessWrite */
    uint64_t    expiry = 0;   /* unix ms; 0 == never */
    Sig         sig{};

    bool is_root() const { return issuer == subject; }
};

/* Append the canonical signing bytes (everything but the signature). */
void cap_signing_bytes(const Capability &c, std::string &out);
/* Full wire form: signing bytes + signature. */
void cap_encode(const Capability &c, std::string &out);
/* Decode a full wire-form capability. Returns false on malformed input. */
bool cap_decode(const uint8_t *buf, size_t len, Capability &out);
/* Verify only a capability's signature (ignores expiry / access). */
bool cap_sig_valid(const Capability &c);

/* The set of capabilities an engine has been granted. */
class CapStore {
public:
    /* Add a capability, skipping exact duplicates (by signature). */
    void add(const Capability &c);

    /* Encode every held capability as a wire blob (for sync exchange). */
    void export_blobs(std::vector<std::string> &out) const;

    /* True if a capability with this exact signature is already held. */
    bool has(const Sig &sig) const;

    /* True if the namespace has a known root (i.e. enforcement is active). */
    bool owned(const std::string &ns) const;

    /* True if `author` holds a valid chain granting `need` access to `ns`. */
    bool authorized(const uint8_t author[32], const std::string &ns,
                    uint8_t need, uint64_t now_ms) const;

private:
    std::vector<Capability> caps_;
};

/* Ingest delegation capabilities learned during a sync session. Roots are
 * never accepted over the wire (a namespace owner is established only locally),
 * and signatures are re-verified; valid delegations are added to e->caps in
 * memory (not persisted). Safe because authorization only ever roots chains at
 * a locally-trusted root. */
void cap_ingest_delegations(sync_engine *e,
                            const std::vector<std::string> &blobs);

/* Enforcement hooks used by the engine / reconciliation. Return SYNC_OK when
 * allowed (including the open, unowned-namespace case). */
int cap_authorize_write(sync_engine *e, const uint8_t author[32],
                        const std::string &ns);
bool cap_authorize_read(sync_engine *e, const uint8_t reader[32],
                        const std::string &ns);

} // namespace ke

#endif /* SYNC_CAPABILITY_H */
