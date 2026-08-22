/* codec.h — canonical, little-endian, versioned serialization of change
 * records (M3). Internal helpers shared by the public codec ABI and the
 * reconciliation engine. */
#ifndef SYNC_CODEC_H
#define SYNC_CODEC_H

#include <cstddef>
#include <cstdint>
#include <string>

#include "engine.hpp"
#include "sync_engine.h"

namespace ke {

/* 1-byte format version stamped at the head of every record.
 *   1 — M3 (ns/entity/field/value/hlc/site_id)
 *   2 — M4 (author public key + per-record signature)
 *   3 — LWW existence: an EXISTENCE record carries (present:u8, hlc) instead of
 *       a causal_length counter. Not backward compatible (signatures cover the
 *       new content); pre-1.0, so no migration. */
constexpr uint8_t kCodecVersion = 3;

/* Unsigned LEB128 varint. */
void     put_varint(std::string &out, uint64_t v);
bool     get_varint(const uint8_t *&p, const uint8_t *end, uint64_t &v);

/* Append the canonical signing bytes (everything except the signature) to out.
 * This is exactly what an author signs / a verifier checks. */
void encode_signing(const sync_change &c, std::string &out);

/* Append the full canonical serialization (signing bytes + signature). */
void encode_record(const sync_change &c, std::string &out);

/* Borrowing sync_change views of stored cells — the single canonical
 * construction of "what build_snapshot re-encodes" for a cell, shared by the
 * snapshot builder, the storage load path's degenerate-insert synthesis, and
 * the tests, so the element-hash contract is established once, structurally.
 * The returned change borrows the argument strings/cell bytes, which must
 * outlive it. */
sync_change change_from_entity(const std::string &ns, const std::string &entity,
                               const Entity &en);
sync_change change_from_register(const std::string &ns,
                                 const std::string &entity,
                                 const std::string &field, const Register &r);

/* Reconciliation-element hash: SHA-256 of the cell's full canonical record
 * (the encode_record bytes). One-shot form — encodes, then hashes. */
Hash256 element_hash(const sync_change &c);

/* Streaming form: hash pre-built signing bytes plus the raw 64-byte signature
 * without re-encoding. Byte-equivalent to the one-shot form because
 * encode_record is exactly encode_signing followed by the unprefixed
 * signature append. */
void element_hash(const std::string &signing_bytes,
                  const uint8_t sig[SYNC_SIG_LEN], Hash256 &out);

/* A decoded record owning its own bytes; yields a borrowing sync_change view. */
struct DecodedChange {
    uint8_t     kind = 0;
    std::string ns, entity, field, value;
    uint64_t    causal_length = 0;
    sync_hlc    hlc{};
    PubKey      author{};
    Sig         signature{};

    sync_change view() const;
};

/* Decode one record from buf[0, len). On success returns true, fills out, and
 * sets consumed to the number of bytes read. */
bool decode_record(const uint8_t *buf, size_t len, DecodedChange &out,
                   size_t &consumed);

/* Ownership helpers for a sync_change's four malloc'd byte fields (ns, entity,
 * field, value), shared by export and decode. */

/* malloc a copy of s; NULL for an empty field. Sets *oom (never clears it) on
 * allocation failure, so callers can chain several dups and test once. */
uint8_t *dup_field(const std::string &s, bool *oom);

/* free + null the four byte fields and zero their lengths. Safe on a
 * zero-initialized change and idempotent. */
void free_change_fields(sync_change &c);

} // namespace ke

#endif /* SYNC_CODEC_H */
