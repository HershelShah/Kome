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

/* A revocation: the namespace owner's signed, permanent statement that a subject
 * key's access in `ns` is withdrawn. It is the mirror of a capability — signed,
 * gossiped, and persisted — but it only ever *removes* access, so the set of
 * revocations is grow-only (a CRDT: merge is union, order-independent). A
 * revocation takes effect only where its `revoker` is known to hold the root for
 * `ns`, so a stolen *delegated* key cannot forge one (no root secret) and cannot
 * un-revoke (grow-only). Revoking a key also kills every capability that key
 * sub-delegated, because the chain walk refuses to pass access through it. */
struct Revocation {
    PubKey      revoker{};   /* must hold the namespace root to be effective */
    PubKey      subject{};   /* the key whose access is withdrawn */
    std::string ns;
    uint64_t    issued_ms = 0; /* wall-clock when issued (audit/ordering only) */
    Sig         sig{};
};

/* Append the canonical signing bytes of a revocation (everything but the sig). */
void rev_signing_bytes(const Revocation &r, std::string &out);
/* Full wire form: signing bytes + signature. */
void rev_encode(const Revocation &r, std::string &out);
/* Decode a full wire-form revocation. Returns false on malformed input. */
bool rev_decode(const uint8_t *buf, size_t len, Revocation &out);
/* Verify only a revocation's signature (against its declared revoker). */
bool rev_sig_valid(const Revocation &r);

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

    /* Add a revocation, skipping exact duplicates (by signature). */
    void add_rev(const Revocation &r);

    /* Encode every held capability as a wire blob (for sync exchange). */
    void export_blobs(std::vector<std::string> &out) const;
    /* Encode every held revocation as a wire blob (for sync exchange). */
    void export_rev_blobs(std::vector<std::string> &out) const;

    /* True if a capability with this exact signature is already held. */
    bool has(const Sig &sig) const;
    /* True if a revocation with this exact signature is already held. */
    bool has_rev(const Sig &sig) const;

    /* Number of revocations held (used to bound growth from gossip). */
    size_t rev_count() const { return revs_.size(); }

    /* True if `subject` has an *effective* revocation in `ns` — i.e. one whose
     * revoker is known here to hold the namespace root. */
    bool is_revoked(const uint8_t subject[32], const std::string &ns) const;

    /* True if `me` holds the root for `ns` (so it may issue revocations). */
    bool is_root_owner(const uint8_t me[32], const std::string &ns) const;

    /* True if the namespace has a known root (i.e. enforcement is active). */
    bool owned(const std::string &ns) const;

    /* True if `author` holds a valid chain granting `need` access to `ns`.
     * If `time_bound` is non-null, it is set to true when the granting decision
     * depended on a capability with a finite expiry — i.e. the answer can change
     * with the passage of time alone. (An open/unowned namespace or a chain of
     * permanent caps is not time-bound.) Lets callers cache the result safely. */
    bool authorized(const uint8_t author[32], const std::string &ns,
                    uint8_t need, uint64_t now_ms,
                    bool *time_bound = nullptr) const;

    /* Number of capabilities held (used to bound growth from gossip). */
    size_t size() const { return caps_.size(); }

private:
    /* Subjects revoked in `ns` by a root owner (effective revocations). */
    void revoked_in(const std::string &ns,
                    std::vector<std::string> &out_subject_keys) const;

    std::vector<Capability> caps_;
    std::vector<Revocation> revs_;
};

/* Ingest delegation capabilities learned during a sync session. Roots are
 * never accepted over the wire (a namespace owner is established only locally),
 * and signatures are re-verified; valid delegations are added to e->caps in
 * memory (not persisted). Safe because authorization only ever roots chains at
 * a locally-trusted root. */
void cap_ingest_delegations(sync_engine *e,
                            const std::vector<std::string> &blobs);

/* Ingest revocations learned during a sync session. Signatures are re-verified
 * and the store is bounded; a revocation only takes effect at authorization time
 * (and only where its revoker holds the namespace root), so relaying a not-yet-
 * authoritative one is harmless and helps it reach a node that can act on it.
 * Authoritative revocations (revoker holds a local root) are persisted so the
 * cut-off survives a reopen. */
void rev_ingest(sync_engine *e, const std::vector<std::string> &blobs);

/* Enforcement hooks used by the engine / reconciliation. Return SYNC_OK when
 * allowed (including the open, unowned-namespace case). */
int cap_authorize_write(sync_engine *e, const uint8_t author[32],
                        const std::string &ns);
bool cap_authorize_read(sync_engine *e, const uint8_t reader[32],
                        const std::string &ns, bool *time_bound = nullptr);

} // namespace ke

#endif /* SYNC_CAPABILITY_H */
