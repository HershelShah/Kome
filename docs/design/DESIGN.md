# Kome: the frontier store

**Decision.** Build Kome on a single lattice: the *frontier* of a set of
signed records under one strict total order, with every policy question
(authorization, far-future clocks, revocation) moved out of the merge and into
either a monotone admission rule or a pure view. The decisions are in §1, the
design in §2–§8, the theorems in §9, and what is still open in §10.

## 1. Decisions

**The governing rule.** The frontier lattice is sound iff every kill
predicate is a down-set of the record order on its key. Every proposal is
decided by this rule first; none of the decisions below breaks it, and none
changes the version order.

### 1.1 The core

| # | Decision |
|---|---|
| C1 | The state is the frontier: merge is set union, then drop every record dominated by a newer one on its key (§3). |
| C2 | The ceiling is a *monotone* admission rule, never an arrival gate: a record above `maxceil` is refused, and admission never shrinks (§4). |
| C3 | Tombstones are apply-then-expire, not refuse-on-arrival: a `DEL` is held, dominates, and is removed only by expiry at a horizon (§7). |
| C4 | Cross-author `DEL`s dominate in the store, so deletion is durable and needs no membership knowledge (§3). |
| C5 | No self-tombstone rule and no device-global clock adoption; a writer's clock affects only its own records (§5). |
| C6 | Revocation carries a `from_t` and is a view, not a gate: it voids records in the views and never feeds admission (§3, §6). |
| C7 | Read control uses hash-chained epoch keys (§6). |
| C8 | Reconciliation starts with a one-message IBLT sketch, then the range split (§8). |
| C9 | Several root keys, certified by the founding key, so root loss is recoverable; no per-field writer rules (§6). |
| C10 | Typed fields (counters, sets, multi-value registers per `(cell, author)`) are a specified extension, built only when an application needs them; they require `W`, a saturating fold, and view output read through a cursor (§4). |

### 1.2 Authorization, storage and wire

| # | Decision |
|---|---|
| D1 | Every authorization record carries a *signer block*; the signer is the founding key or a root certified by it (`cert_sig` over `ns ‖ signer ‖ cert_cap`). Only the founding key certifies, so only it adds roots. Admission depends on bytes only (§2, §6). |
| D1′ | Write access lives in a record kind `GRANT(subject)`, keyed by `(ns, issuer, subject)`. `W(F)` is the set of subjects of the `GRANT`s in `F`, and `maxceil(F)` is the largest `ceiling_t` of the rosters in `F`; a roster leaves `F` only under a roster of the same signer with a ceiling at least its own. Both registers are functions of `F` that never shrink (§3, §4). |
| D2 | Only the founding key root-voids, `from_t` is ignored for it, the founding key can never be revoked, and everything a root-voided root issued (rosters, `REVOKE`s, `GRANT`s) stops counting in every view; keys only it granted read `void` through the effective-writer view `W_eff` (§3, §6). |
| D3 | Canonical form is a property of `Header`, produced by decode and required by the lattice. A roster dominates another of its signer iff it is greater in `(gen, h)` *and* not lower in `ceiling_t` (a product order); `ROSTER_eff` is the `(gen, h)`-maximum, with a tie-break on the whole roster tuple (§3). |
| D4 | Signatures are RFC 8032 Ed25519 (SHA-512 internal to the signature), from monocypher's `monocypher-ed25519`, checked against RFC 8032 and Wycheproof vectors. BLAKE2b is the hash for everything Kome derives (§2, A1). |
| D5 | There is no root X25519 key. Each `ROSTER` carries a fresh ephemeral `box_pk` covered by its signature; its secret seals that roster's boxes and is wiped (§2, §6). |
| D6 | `wrap_key` hashes the DH output with `box_pk`, both member keys, `ns` and `epoch`; the box nonce is synthetic, `BLAKE2b(wrap_key ‖ k_e)`, recomputed and checked by the member. Bundle nonces are synthetic too (§6). |
| D7 | The accumulator is little-endian, recorded exactly, with the tags as bytes (§8). |
| D8 | The write path picks `(t, seq)` without `h`, then hashes; the outcome is independent of `h`. `seq_self` is per collection (§5). |
| D9 | Nothing but `F` is persisted. The log is a `HEADER` (`ns`, `root_pk`, `salt`, capacities) and a journal of `APPLY`, `APPLY_EXPIRED` and `EXPIRE` entries; `EXPIRE` is logged only when it removes something or lowers the horizon; compaction writes authorization records first. Replay gives the same frontier as a set (T18, §7). |
| D10 | Expiry is an operation on the lattice state at `horizon = min(now_local, maxceil) − del_ttl_eff`, with `del_ttl_eff` the largest `del_ttl` of the non-root-voided rosters (clamped at decode), so a stolen root can lengthen tombstone life but never shorten it (§7). |
| D11 | Order of checks: admission, duplicate, domination, room. A dominated record never needs room, and nothing changes on any refusal (§7). |
| D12 | `Value_Max` = 40 960, so every frame fits one 48 KiB message (§2, §8). |
| D13 | No register value crosses the wire. A pre-gate `OPEN` carries `ns` and the sender's founding-issued `REVOKE`s of roots, which the receiver applies *before* it evaluates the gate. The post-gate `HELLO` carries counts, the digest and the sender's credential roster (which must list the sender's Noise key), and is sent only to a peer already admitted. The authorization range is reconciled to completion before the data range (§6, §8). |
| D14 | Session phases are `Auth` then `Data`; only the initiator sends root `RANGE`s, exactly two, with fixed bounds; replies are exact windows; items apply in key order (§8). |
| D15 | Prefix sums carry one more entry, the total; any sub-range costs at most 64 additions and one subtraction, by the two-accumulator scheme (§8). |
| E1 | Data records have one capacity; every signer has its own *slice* of authorization capacity, the founding key's reserved. `W`'s capacity is the total of the slices, so it never fills on its own. Neither a data flood nor a stolen root can fill anyone else's space, so the founding key's `REVOKE` always lands (§7). |
| E2 | An authorization record that would exceed its signer's slice is refused with `AUTH_FULL`, changing nothing; no key is ever dropped silently (§7). |
| E3 | One hash chain per collection, in *segments*; only the founding key opens a segment (on root-void, or when a segment's top is reached), and each roster carries links that let a member walk back across segments (§6). |
| E4 | `from_t` protects only against a key lost, not one used by a thief; for a stolen key, revoke from 0 (§6). |
| E5 | Keys are canonical at decode: `box_pk`/`dh_pk` reduced and not low-order, `del_ttl` clamped, the cert block zero exactly for the founding key; one encoding per record (§2). |
| E6 | `root_pk` must equal the store's founding key; the effective certificate cap is the largest ever certified (§6). |
| E7 | A revoked key's records are not refused at admission; instead assumption A7 (a revocation reaches a replica before records its subject signs afterwards) is stated, and the H8 bounds depend on it. Refusing them would give a stolen root a permanent mass-deletion primitive and give up T3 (§6, §9). |
| E8 | No per-author data quota in the engine: a quota refusal is a capacity refusal and would disagree across replicas under a flood; it stays an application policy (§10.5). |
| E9 | The frontier keeps one data array and one authorization row per signer slot, each bounded by its own discriminant (§7). |

## 2. Objects

**Identifiers.** A collection `ns` is 16 bytes, self-certifying:
`ns = BLAKE2b-256(root_pk ‖ salt)[0:16]`; `root_pk` is the collection's
**founding key**. An entity `ent` is 16 bytes. A field name is 1–32 bytes.
A value is 0–40 960 bytes (blob chunks of 32 KiB fit; larger payloads are
chunked above the engine; the bound is what makes every frame fit in one
reconciliation message, §8). An empty value is a value.

**Version.** `v = (t : u48, author : [32]u8, seq : u48, h : [32]u8)`, compared
lexicographically with `author` and `h` as unsigned 256-bit integers. `h` is
the record's own content hash, so distinct records never compare equal and the
order is total by construction. `t = 0` and `seq = 0` are ordinary values.

**Records.** A frame is `tag:u8 ‖ content ‖ sig[64]`; `h = BLAKE2b-256(tag ‖
content)`, and `sig` is an Ed25519 signature (RFC 8032, strict: `S < L`)
over the 32 bytes of `h` by the record's signer. All integers are
big-endian; all tags and labels in this document are ASCII bytes without a
terminator. The five layouts, exactly as `Kome.Records` encodes them:

```
tag 0  ROSTER  ns[16] root_pk[32] salt[16] SIGNER box_pk[32]
               gen:u48 ceiling_t:u48 del_ttl:u48 epoch:u16
               n_links:u8 (≤ 15)   links[n_links]     { from_epoch:u16 nonce[24] box[48] }
               n_members:u8 (≤ 64) members[n_members] { sign_pk[32] dh_pk[32] nonce[24] box[48] }
tag 1  REVOKE  ns[16] root_pk[32] salt[16] SIGNER sign_pk[32] from_t:u48 rev_seq:u48
tag 2  GRANT   ns[16] root_pk[32] salt[16] SIGNER subject[32]
tag 3  DEL     ns[16] ent[16] t:u48 seq:u48 author[32]
tag 4  PUT     ns[16] ent[16] flen:u8 field[flen] t:u48 seq:u48 author[32] vlen:u16 value[vlen]

SIGNER = signer[32] cert_cap:u48 cert_sig[64]
```

| Kind | Content offsets (the tag is byte 0) | Frame bytes |
|---|---|---|
| ROSTER | ns 1, root_pk 17, salt 49, signer 65, cert_cap 97, cert_sig 103, box_pk 167, gen 199, ceiling_t 205, del_ttl 211, epoch 217, n_links 219, links 220, n_members 220 + 74·n_links, members 221 + 74·n_links | 285 + 74·n_links + 136·n_members, at most 10 099 |
| REVOKE | ns 1, root_pk 17, salt 49, signer 65, cert_cap 97, cert_sig 103, sign_pk 167, from_t 199, rev_seq 205 | 275 |
| GRANT | ns 1, root_pk 17, salt 49, signer 65, cert_cap 97, cert_sig 103, subject 167 | 263 |
| DEL | ns 1, ent 17, t 33, seq 39, author 45 | 141 |
| PUT | ns 1, ent 17, flen 33, field 34, t 34 + flen, seq 40 + flen, author 46 + flen, vlen 78 + flen, value 80 + flen | 144 + flen + vlen, at most 41 136 |

The signature follows the content. `PUT` and `DEL` are signed by `author`;
`ROSTER`, `REVOKE` and `GRANT` by `signer`.

**The signer block and root certificates (D1).** An authorization record
names its signer and proves the signer is a root, from its own bytes:

- `signer = root_pk`, `cert_cap = 0`, `cert_sig` = 64 zero bytes: signed by
  the founding key; or
- `signer ≠ root_pk` and `cert_sig` is the founding key's signature over
  `BLAKE2b-256("kome/root" ‖ ns ‖ signer ‖ u48(cert_cap))`: a **certified
  root**, whose rosters may not set `ceiling_t` above `cert_cap`.

Only the founding key can produce a certificate, so only the founding key
adds roots; certification happens out of band (a key ceremony), and the
certificate then travels inside every record the root signs. The founding
key is meant to be kept cold (offline, or in a hardware token): it signs
certificates, root revocations and the occasional roster, nothing else.
The founding key renews a certified root's `cert_cap` by issuing a new
certificate. Certificates cannot be narrowed or withdrawn: every certificate
ever issued stays valid for every record, so a root's **effective cap is the
largest `cert_cap` ever certified for it**, and only root-voiding (§6) ends
what a certificate allows. Caps should therefore be short (weeks ahead of
the wall clock) and renewed regularly; the cap also acts as a dead-man
switch, because if the founding device is lost `maxceil` stops at the
largest cap once wall time passes it (§6).

**Well-formed** is a function of the bytes alone. A frame is well-formed iff:

1. its length is exactly the layout's, `flen` ∈ 1..32, `vlen` ≤ 40 960,
   `n_links` ≤ 15, `n_members` ≤ 64;
2. for `ROSTER`, `REVOKE`, `GRANT`: `ns = BLAKE2b-256(root_pk ‖ salt)[0:16]`,
   the signer block is valid as above, and a `ROSTER` signed by a certified
   root has `ceiling_t ≤ cert_cap`;
3. for `ROSTER`: `del_ttl` ∈ [`Del_TTL_Min`, `Del_TTL_Max`] (7 days and
   3 650 days, in milliseconds), and `box_pk` and every member `dh_pk` is a
   reduced X25519 encoding (`u < 2^255 − 19`, bit 255 clear) and not one
   of the five reduced low-order encodings (0, 1, `p − 1`, and the two
   points of order 8), so every listed member can open its box (E5);
4. for `REVOKE`: `sign_pk ≠ root_pk` (the founding key cannot be revoked);
5. the signature verifies under the signer (authorization kinds) or the
   author (data kinds).

Each well-formed record has exactly one encoding (unused buffer bytes are
zero in every in-memory representation), so `h` is a function of the
record and, under A2, injective on records.

**Why these five kinds.** `PUT` and `DEL` are the data. `ROSTER` carries
read access (the member boxes), the session gate, the epoch key and two
replicated parameters (`ceiling_t`, `del_ttl`). `GRANT` carries write
access: its subject may author `PUT`s and `DEL`s, and the grant counts in
the effective-writer view only while its issuer is not root-voided (§3). It
is separate from
`ROSTER` because write access must be grow-only and a function of the
frontier, and roster membership is neither (a later roster drops members,
and dominated rosters leave the frontier). `REVOKE` is separate from both
because it must be grow-only: a revocation can never be undone by a later
roster (otherwise a root restored from backup could issue a roster that
drops a revocation).

## 3. The lattice

For `H` a set of well-formed records, **domination** is:

```
dom(p, H) for PUT p    := ∃ q ∈ H : PUT, cell(q) = cell(p), q.v > p.v
                        ∨ ∃ d ∈ H : DEL, entity(d) = entity(p), d.v > p.v
dom(d, H) for DEL d    := ∃ d' ∈ H : DEL, entity(d') = entity(d), d'.v > d.v
dom(r, H) for ROSTER r := ∃ r' ∈ H : ROSTER, same ns, same signer,
                            (r'.gen, r'.h) > (r.gen, r.h) ∧ r'.ceiling_t ≥ r.ceiling_t
dom(g, H) for GRANT g  := ∃ g' ∈ H : GRANT, same ns, same issuer, same subject, g'.h > g.h
dom(x, H) for REVOKE   := false
F(H) := { x ∈ H | ¬ dom(x, H) }
```

Every kind carries its identity in one version, and each clause above
implies that the dominator's version is greater on the record's key:

| Kind | `v` | key on which `dom` compares | order on the key |
|---|---|---|---|
| PUT | `(t, author, seq, h)` | cell `(ns, ent, field)`; also a DEL of its entity | `v` |
| DEL | `(t, author, seq, h)` | entity `(ns, ent)` | `v` |
| ROSTER | `(ceiling_t, signer, gen, h)` | `(ns, signer)` | product of `(gen, h)` and `ceiling_t` |
| GRANT | `(0, subject, 0, h)` | `(ns, issuer, subject)` | `h` |
| REVOKE | `(from_t, subject, rev_seq, h)` | none: never dominated | — |

The roster clause is a product order (D3). Ordering
rosters by ceiling first would let a stale roster with an old `gen` and a
current clock (a root restored from backup, or a second device holding the
same root key) evict the newer roster for good and roll back a member
removal and the epoch; under the product order neither dominates and both
stay until the root re-issues one that is above both. The product order is
a strict partial order that the version order extends, and it is monotone,
so T2, T2' and T3 hold exactly as for a total order; the governing rule of
§1 is read accordingly: every kill predicate is a down-set of a strict
partial order on its key that the record order extends.

The fields of the lattice's header that a kind does not use are zero, and
a roster's header also carries its `del_ttl` and its issuer (= signer);
`REVOKE` and `GRANT` headers carry their issuer (the signer). This is the
**canonical** header (D3); decode produces only canonical headers and the
lattice accepts no other. A frontier holds at most one `GRANT` per
`(issuer, subject)`; it holds a per-signer *antichain* of rosters, which an
honest signer keeps at one roster (§10.3) and a misbehaving one can grow
only within its capacity slice (§7). Every dominator stays in the same
capacity row as what it dominates: data dominates only data, and an
authorization record is dominated only by one with the same issuer.

`F(H)` is the **frontier**, and it is the state. `dom` is monotone in `H`
(T2) and *upward-closed*: a dominator of a dominator of `x` dominates `x`
(T2'). It is the lemma the convergence proof needs, and it holds for every
kind above, which is why `REVOKE` is not
allowed to dominate (a revocation dominating a writer's `PUT` would not
dominate what that `PUT` had already dominated; see §6). From T2 and T2':

```
F(H₁ ∪ H₂) = F(F(H₁) ∪ F(H₂))        (T3)
```

so a replica may drop a dominated record the moment it is dominated, on any
subset of replicas, at any time, and no future frontier changes. That one
equation is the whole GC story for values: a deleted entity's values are freed
everywhere a `DEL` arrives, with no membership knowledge and no clock.

**Views** are pure functions of `F` (and of the collection's constant
`root_pk`):

```
deleted_at(ns, ent) := max { d.v | d ∈ F, DEL on (ns, ent) }            -- Option
cell(ns, ent, f)    := the unique PUT in F on (ns, ent, f)               -- Option
exists(ns, ent)     := ∃ f. cell(ns, ent, f) ≠ None
maxceil(F)          := max { r.ceiling_t | r ∈ F, ROSTER }   (0 if none)
W(F)                := { g.subject | g ∈ F, GRANT }                       -- admission
root_void(k)        := k ≠ root_pk ∧ ∃ x ∈ F : REVOKE, x.subject = k, x.issuer = root_pk
W_eff(F)            := { g.subject | g ∈ F, GRANT, ¬ root_void(g.issuer) }  -- views
void(p)             := (∃ x ∈ F : REVOKE, x.subject = p.author, p.t ≥ x.from_t,
                          ¬ root_void(x.issuer))
                       ∨ p.author ∉ W_eff(F)
ROSTER_eff          := the maximal ROSTER r ∈ F with ¬ root_void(r.signer), ordered by
                       (gen, h), ties (impossible under A2) by (signer, ceiling_t, del_ttl)  -- Option
del_ttl_eff         := max { r.del_ttl | r ∈ F, ROSTER, ¬ root_void(r.signer) },
                       or Del_TTL_Default (180 days) if there is none
far(p)              := p.t > now_local + slack      -- advisory flag only
```

`W` decides admission and `W_eff` decides views. They differ only by the
grants of root-voided issuers: admission cannot drop them (it must stay
monotone, §4), so the keys they name stay admissible and their records stay
held, but every such record reads `void` unless an issuer that is not
root-voided also granted its author. `del_ttl_eff` is a maximum so that a
root can lengthen tombstone life but never shorten it below what another
root set: shortening is irreversible (expired tombstones are gone), and
lengthening is undone by root-voiding the root that did it.

There is no presence bit and no sentinel: an entity exists iff it has a live
field; a deleted entity is a `DEL` and nothing else.

`maxceil` and `W` lose nothing to domination: a roster leaves `F` only under
a roster of the same signer with a ceiling at least its own, and a `GRANT`
leaves `F` only under a `GRANT` of the same issuer and subject; with T2'
every dominated record has an undominated dominator. So `maxceil(F(H)) =
maxceil(H)`, `W(F(H)) = W(H)` and `W_eff(F(H)) = W_eff(H)`: the registers of
the frontier are the registers of everything ever applied, and they never
shrink (T4'). Likewise `ROSTER_eff(F(H)) = ROSTER_eff(H)`, because a roster
that dominates another has a greater `(gen, h)` and the same signer.
`ROSTER_eff` is present whenever `F` holds a roster signed by the founding
key, which the collection's first roster is.

## 4. Admission

Every well-formed authorization record (`ROSTER`, `REVOKE`, `GRANT`) is
admitted. A `PUT` or `DEL` is admitted iff `t ≤ maxceil(F)` and `author ∈
W(F)`. Both registers are the derived views of §3: they are functions of the
frontier, not separate state, and they only grow, because admission of
authorization records is unconditional and their domination never lowers
either (§3). `W` bounds who can occupy the store: without it a member could
relay records under unrostered ground keys and make a cell's state unbounded,
and typed fields (below) would have no
per-cell bound at all. Removal from `W` does not exist; removal of a writer
is `REVOKE` (§6), and neither `REVOKE` nor root-voiding ever changes
admission: an admission rule that a later record can withdraw is
non-monotone, and replicas that saw the two records in different orders
would hold different frontiers forever (and the variant that also drops the
withdrawn records is rejected, E7). What keeps a revoked key's later records out is the transport
gate, under assumption A7 (§6, §9).

A gate of the form "inadmissible under the currently maximal roster" would
break with two rosters of equal generation. This rule is instead
**monotone in the held history**: once a record is admissible at a
replica it stays admissible, and a record inadmissible at one replica
becomes admissible there as soon as the authorization record that made it
admissible elsewhere arrives. Inadmissible records are **discarded**, not
held; they are re-offered by whichever peer holds them on the next
reconciliation (T4 is stated in exchange form for exactly this reason). The
ceiling keeps the top of the version order unreachable: no admissible record
can pin a cell beyond `maxceil`, and every roster refresh moves `maxceil` up.

The state of a replica is `F` alone; its join is `F(F₁ ∪ F₂)`, with the data
records re-admitted under the joined authorization records. Every batch of
records received together (a bundle, an import) is applied in element-key order
(§8), which puts authorization records first; that is the authorization-first
pass of T4 (a), so a data record is never discarded for arriving in the same
batch as, but before, the grant that admits it. An
implementation may cache `maxceil` and `W` (`Kome.Registers`), provided the
cache equals the views of §3 on every state (an invariant, not a second
source of truth).

**Registers are derived, not reconciled.** Stored registers would have to
be joined between replicas, and unauthenticated register values on the wire
would let any peer raise `maxceil` or add a writer; a roster dominated on
arrival would raise registers the log never recorded. With `GRANT` and the
ceiling inside the roster's version (D1′) nothing outside `F` needs
reconciling or persisting: reconciling the authorization records reconciles
the registers (§8), and replaying the log replays them (§7). Root authority
is a certificate, checked on bytes (§2).

**Typed fields (extension, C10).** When an application needs
counters, grow-only sets or multi-value registers in the engine, a `PUT`
may carry `ftype : u8 ∈ {LWW, GSET, PNCOUNTER, MVREG, MAXREG}` as part of
the cell key, the author's full state for that field as its value, and the
`PUT`-over-`PUT` clause of `dom` gains the condition `(ftype = LWW ∨ same
author)`. The frontier then holds at most one record per `(cell, author)`,
bounded by `|W|`, and the cell's value is a join over the surviving,
non-void per-author records. LWW cells are unchanged. It requires `W`, a
saturating fold, and view output read through a cursor. It is not on the
critical path: an application can get the same semantics today
with one LWW sub-cell per device.

## 5. Clocks and writing

There is no engine clock, no `tick`, no `receive`, nothing adopted from a
peer, so one collection's far-future record can never carry into another
collection on the device.

```
floor(cell)  := max(cell(ns,ent,f).v, deleted_at(ns,ent))     -- for DEL: max over all fields and deleted_at
t_emit       := max(now_ms, floor.t + 1 if floor exists); if t_emit > maxceil then t_emit := maxceil
seq_emit     := seq_self(ns) + 1, and above every seq of this device's records held in F(ns);
                at 2^48 − 1 the write fails SEQ_EXHAUSTED, no record is produced
v_emit       := (t_emit, self_pk, seq_emit, h)
status       := SHADOWED if floor exists ∧ v_emit < floor   (only when t_emit = maxceil) else OK
```

**The write path has three steps (D8).** `h` hashes content that contains
`t` and `seq`, so `h` cannot be an input to the step that chooses them:

1. *Choose* `(t_emit, seq_emit, status, clone_suspected)` from the frontier,
   the target cell, `now_ms`, the device key and `seq_self(ns)`. No `h`.
2. *Build* the `PUT` or `DEL` content with that `(t, seq)` and hash it.
3. *Sign* and apply; persist `seq_self(ns) := seq_emit` (A5).

The outcome of step 1 does not depend on `h`: because `seq_emit` exceeds
every `seq` of this device's held records, `(t_emit, self_pk, seq_emit)`
differs from the prefix of every held version, and two versions with
different `(t, author, seq)` prefixes compare by the prefix alone. So for
every `h`, the record of step 2 is admitted, `OK` means it is dominated by
nothing held, and `SHADOWED` holds iff some held record of the floor has a
greater prefix (stated as a lemma, `Lemma_Outcome_Independent_Of_H`). An
`OK` write is held by the apply step unless the store is full (`NO_SPACE`,
§7).

A write *chases* the cell's floor, so read-your-writes holds (T8) unless the
cell is pinned at the ceiling. A device with no real-time clock works: all its
writes chase. `seq_self(ns)` is the only persisted clock state. It is **per
collection**: kept per `(device key, ns)` next to that collection's store, so
a thief who forces a jump to `2^48 − 1` in one collection exhausts only that
collection's counter for that key. `SEQ_EXHAUSTED` is a clone alarm: the
device moves to a fresh key in that collection (a new `GRANT` and roster)
and the old key is revoked.

**What a misbehaving writer can do (H8).**

| Case | Effect | Bound |
|---|---|---|
| Clock ahead by δ | Wins concurrent conflicts on cells it writes for δ; those cells then resolve by chase (arrival order) rather than wall time | δ ≤ maxceil − now; only cells it touched; automatic |
| Clock behind | Loses concurrent conflicts; its own cells still chase | its cells only; a fixed clock takes effect at once |
| Backup restore | Re-emits old `seq` values: equivocation, ordered by `h`, flagged; old records re-offered and dominated unless the `DEL` has expired (§7) | self-detected (own held record with `seq ≥ seq_self + 1`); `seq` jumps past it; the write succeeds and reports the flag `CLONE_SUSPECTED` |
| Cloned key | Continuous equivocation; replicas still agree | flagged; owner issues `REVOKE(old, 0)`, a `GRANT` for a fresh key and a roster |
| Malicious | Overwrite or delete any cell (that is what write access means); pin cells to `maxceil`; flood entities; grind a public key that wins ties at the ceiling; force its own `seq` to `2^48 − 1` in collections where it writes | no forging; no exceeding `maxceil`; a flood cannot block the `REVOKE` (§7 capacity classes). Under A7: once a replica holds the `REVOKE` and the roster that removes the key, nothing the key signs reaches that replica, so pins end at the next roster refresh and floods end at `REVOKE` plus owner `DEL`s. Without A7: a stale replica (one without the `REVOKE`) that admits the key to a session, or takes its bundle under the old epoch, relays what it signs to every replica, where it is admitted and flagged `void`; the bytes it overwrites or deletes are gone |
| Root restored from backup | Issues a roster with an old `gen`: dominated on arrival (status `DOMINATED`) if its own held roster is above it in `(gen, h)` with a ceiling at least as high; otherwise (a current clock) neither dominates and both are held, and `ROSTER_eff` is still the newer `(gen, h)`; once synced the root re-issues a roster above both. `maxceil` never decreases and `REVOKE`s are never lost | convergent either way; a stale roster never becomes effective |

`CLONE_SUSPECTED` is a flag reported beside the write's status, not a status:
the write itself happened.

The honest statement of the residual: **LWW cannot un-ring a wall clock**. A
cell whose floor was pushed far ahead resolves by chase until wall time passes
it. The ceiling bounds how far; it does not prevent it. A thief's overwrites
made before the revocation reaches a replica stand, flagged `void`; the bytes
they replaced are gone. This is acceptable because every such act is
signed, attributable, bounded, and ends at revocation plus one refresh. It
ends at each replica when that replica holds the revocation, and it ends everywhere only
if no stale replica accepts the key's later records first, which is
assumption A7 (§9). Offline-first makes stale replicas normal, so A7 is a
deployment duty: revoke promptly, and sync every device after a revocation
before it talks to anything else.

## 6. Authorization, encryption, revocation

**Roots (C9, D1).** A collection has one
founding key (`root_pk`, from which `ns` is derived) and up to 15 certified
roots over its life (`Signers_Max` = 16 signers in all). Any root, founding
or certified, may sign `ROSTER`, `REVOKE` and `GRANT`; only the founding key
certifies a root (§2). Whether a record's signer is a root is decided from
the record's bytes, so admission of authorization records needs no history:
a latecomer can never refuse a `REVOKE` every other replica holds, and a
roster never waits for the roster that introduced its signer. Roster
domination is per signer (§3), and the effective roster is the view
`ROSTER_eff` (§3): the `(gen, h)`-maximum over frontier rosters whose signer
is not `root_void`. Two roots racing equal generations resolve by `h`;
`REVOKE`s are grow-only so nothing a race can do loses one. Per-field
writer sets are not part of the design: enforced at admission they
are non-monotone, and as a view flag
they are a label that cannot stop an unauthorized write from freeing an
authorized value's bytes.

**Root revocation (D2).** Only the founding key root-voids:
`root_void(k)` holds iff `F` holds a `REVOKE` of `k` *issued by the founding
key*; its `from_t` is ignored, because root-issued records carry no
trustworthy time and a thief would backdate. The founding key is never
`root_void` (a `REVOKE` of `root_pk` is malformed). A `REVOKE` issued by a
certified root and naming another root only voids that key's data records.
A root-voided root's certificate stays valid, so it can go on signing
well-formed records, and admission (which must stay monotone) still takes
them; what root-voiding changes is every view. Everything the root issued,
before or after, stops counting: its rosters leave `ROSTER_eff` and
`del_ttl_eff`; its `REVOKE`s stop voiding (members it wrongly revoked are
un-voided); and its `GRANT`s leave `W_eff`, so every record whose author only
it granted reads `void`, including every key it mints afterwards. The price
is that honest revocations and grants issued by a root that is later
root-voided also stop counting; the recovery procedure re-issues the ones to
keep. `void`, `W_eff` and `ROSTER_eff` are views and never feed admission;
`root_void` is monotone in `F`, and for a fixed `root_void` set the
`REVOKE` clause of `void` and `W_eff` are monotone in `F` (T12).

**Recovering from a stolen or lost certified root `R`.** The founding key,
in one sitting: (1) issues a `GRANT` of its own for every key `R` granted
that the owner wants to keep writing (otherwise those keys read `void` after
step 2); (2) issues `REVOKE(R, 0)`; (3) re-signs any of `R`'s member
revocations it wants to keep; (4) issues a founding-signed roster that opens
a new epoch segment (below) and delivers the new top to the remaining roots
out of band. Keys `R` granted that the owner does not recognize need no
action: `W_eff` voids them, including any `R` mints later. The root
revocation reaches captured replicas through `OPEN` (below).

**What a stolen certified root can do, stated.** Until a replica holds its
root revocation, it can do there what a root does: grant writers (who can
overwrite or delete any data), make its roster `ROSTER_eff` (with `gen =
2^48 − 1`, so it decides who passes the session gate and which epoch
bundles use, and can lock honest members out), revoke members (flag them
`void`), raise `maxceil` up to its effective cap, and lengthen `del_ttl_eff`.
After the founding key root-voids it, at every replica that holds the root
revocation all of that stops counting in the views, and under A7 nothing it
or its grantees sign afterwards reaches that replica, because no roster of
its counts for the gate and no epoch of its is accepted for bundles. What
stays, permanently: `maxceil` raised up to the largest cap ever certified for
it; its records in its own capacity slice; if it overflowed its slice, the
replicas' disagreement about its surplus records (§7); and without A7, the
records it or its grantees signed after the revocation that a stale replica
accepted, which every replica then holds, flagged `void`, together with the
loss of the bytes they overwrote or deleted. A stolen founding key violates
A1 and means re-founding the collection.

**Losing the founding device** without the key being stolen is survivable
while a certified root remains (it keeps issuing rosters and grants), but
only until wall time passes the largest `cert_cap` in force: `maxceil` cannot
rise above it, so writes then degrade to ties at the ceiling (A3), and no
root can be added or root-voided until the key is restored from its offline
backup. That is why the founding key is kept cold with an offline backup.

**Membership is key possession.** The `ROSTER` wraps the current epoch key to
each member's `dh_pk`. Epoch keys form a hash chain `k_e = BLAKE2b-256(k_{e+1}
‖ "prev")` within a *segment*: a member holding `k_e`
derives every older key of the segment, so a new member needs one box, and a
removed member holding `k_e` cannot derive `k_{e+1}`. 2^16 epochs suffice for
any collection's life.

**Epoch segments and several roots (E3).** There is one chain per
collection, shared by the roots that are not `root_void`. A segment starts at
epoch `s` with a fresh random top key drawn at an epoch `top_s` above it (for
example `min(s + 4 095, 65 535)`); the roots receive the current segment's
top out of band (at certification, and at each new segment). Within a
segment every epoch key is a function of the top, so two roots that issue
rosters at the same epoch use the same key and never conflict; a root never
issues a roster with an epoch above `top_s`. **Only the founding key opens a
segment**, with a founding-signed roster at epoch `1 +` the largest epoch of
the non-root-voided rosters in `F` (a root-voided root's epochs are ignored,
so a thief cannot use up the epoch space), when it root-voids a root or when
the current segment's top is reached. A root-voided root never sees the new
top, so it cannot derive any later key. Each roster carries `links[]` (at
most 15, cumulative over the collection's life): link `{from_epoch = s,
nonce, box}` seals `k_{s−1}`, the last key of the previous segment, under a
key derived from `k_s`, the first key of the segment that follows it. A
holder of any key of the current segment walks down to its start, opens the
link, and continues downward, so a new member still reads all history.
Because every roster carries the full link list, history survives the
domination of old rosters. A seventeenth segment would need a sixteenth
link, and the epoch space ends at 65 535; at either bound the collection is
re-founded.

**Boxes (D5, D6).** Each roster carries `box_pk`, the X25519 public key of a
fresh ephemeral secret `eph_sk` that the signer draws for that one roster,
seals the roster's member boxes with, and wipes. No root has a long-term
X25519 key, no key is used both to sign and to exchange, and boxes get
forward secrecy once `eph_sk` is wiped. For member `(sign_pk, dh_pk)` of a
roster of collection `ns` at epoch `e`:

```
wrap_key = BLAKE2b-256("kome/wrap" ‖ X25519(eph_sk, dh_pk) ‖ box_pk ‖ dh_pk ‖ sign_pk ‖ ns ‖ u16(e))
nonce    = BLAKE2b-256("kome/nonce" ‖ wrap_key ‖ k_e)[0:24]
box      = XChaCha20-Poly1305(wrap_key, nonce, AD = ns ‖ u16(e), k_e)        -- cipher[32] ‖ tag[16]
```

The member computes `X25519(dh_sk, box_pk)`, opens the box, recomputes the
nonce from the opened key and refuses a mismatch, so there is exactly one
valid box per `(wrap_key, k_e)`. A link is the same construction with
`link_key = BLAKE2b-256("kome/link" ‖ k_s ‖ ns ‖ u16(s))`, `nonce =
BLAKE2b-256("kome/nonce" ‖ link_key ‖ k_{s−1})[0:24]`, `AD = ns ‖ u16(s)`,
sealing `k_{s−1}`. Three layers keep keystreams apart: a fresh `box_pk` makes
every wrap key single-use; binding `ns`, the epoch and both member keys
separates wrap keys even if a `box_pk` were reused (a restored device, a
bug); and the synthetic nonce makes a repeated `(key, nonce)` imply a
repeated plaintext, which reveals only that the same key was re-wrapped. The
only randomness is the caller's `eph_sk` and segment tops; SPARK code reads
no RNG, and the construction is deterministic and testable by known-answer
vectors. Low-order and non-reduced peer keys are refused at decode (§2) and
again at box time.

**Two gates on transport, none on records.** A peer is admitted to a session
for `ns` iff its Noise static key is the `dh_pk` of a member of `ROSTER_eff`.
Before evaluating the gate each side applies what the peer sent before the
gate: the `OPEN` message carries the sender's founding-issued `REVOKE`s of
roots (signed records, admissible everywhere), so one honest contact
un-captures a replica whose `ROSTER_eff` a root-voided thief had taken over
(D13). The credential `HELLO` follows, and a side sends
its own only after it has admitted the peer, so a non-member learns no
membership list: the credential is a roster in the sender's `F` that lists
the sender's Noise key (any other credential is refused), and the receiver
applies it and re-evaluates the gate, so a newly added member can still
reach a replica whose rosters are stale (§8). A sealed bundle (mailbox,
broadcast, BLE) is readable iff the replica holds its epoch key; bundles are
accepted **only under `ROSTER_eff.epoch`** (accepting the previous epoch
would let a removed member write into up-to-date replicas for a whole
epoch). A captured replica therefore takes
no bundle from honest members until an interactive session un-captures it.
Both gates decide who you talk to, never what a record means.

**Revocation** is `REVOKE(X, from_t)`: grow-only, never dominated, root-signed.
Its effect is the view flag `void` on `X`'s records with `t ≥ from_t` (while
its issuer is not `root_void`), plus the roster that follows it (fresh
epoch, `X` removed). It is deliberately *not* a prune, and it does not
change admission, for this reason: if a revocation dropped `X`'s records from `F`, a record
`p'` of `X` that had already dominated (and freed) an honest `p` would vanish
on one replica and leave the cell empty, while a replica that saw the
revocation first would still hold `p`. Same records, different frontiers.
Retroactive removal needs history; a frontier has none. So `void` hides and
flags, and an honest writer's next write chases above the voided record.
The cost: a revoked writer's garbage stays in `F` as void records until the
owner `DEL`s those entities (an app-level "purge revoked writer" routine
issues the `DEL`s; the tombstones then expire). Revocation does not remove
`X` from `W`, and never needs to: `W` only admits, `void` judges. What keeps
`X`'s *later* records out is the gate: a replica holding the revocation and
the roster that removes `X` admits `X` to no session and takes no bundle
from it. A replica that does not yet hold them can, and then relays `X`'s
records everywhere, where they are admitted (flagged `void`); assumption A7
(§9) excludes that, and the H8 bounds (§5) depend on it.

**What `from_t` can and cannot do (E4).** `from_t > 0` keeps a key's
earlier records unflagged, which is right for a key that was *lost* and not
used by anyone. It cannot protect against a thief: a thief chooses `t` and
can backdate below `from_t`, and such records are indistinguishable from
honest ones. For a key known or suspected to be stolen, revoke from 0.
(`from_t` is ignored for root revocation, above.)

## 7. Storage and tombstone expiry

**The log is a journal of operations on `F` (D9).** One collection's store
is an append-only log, sealed at rest under the device key (a later layer),
and an in-memory index `cell → (offset, v)` that holds exactly the records of
`F`. Per cell, version metadata is 6 + 6 + 32 bytes plus a cached 32-byte `h`.
Log entries, all integers big-endian:

```
HEADER         op = 0 ‖ "kome/log" ‖ version:u8 ‖ ns[16] ‖ root_pk[32] ‖ salt[16] ‖ data_cap:u32 ‖ slice:u16
APPLY          op = 1 ‖ len:u32 ‖ frame        a record applied and held
APPLY_EXPIRED  op = 2 ‖ len:u32 ‖ frame        a DEL applied for its effect and not held (below)
EXPIRE         op = 3 ‖ horizon:u48            Frontier.Expire at this horizon, or a lowered horizon
```

The log starts with exactly one `HEADER` (`version = 1`; 80 bytes); its
`ns` must equal `BLAKE2b-256(root_pk ‖ salt)[0:16]`, which fixes the founding
key for everything the store does, and its capacities are those the store
was last opened with (§10 item 10). Nothing else is persisted: the registers are functions of
`F` (§4), and refused or dominated records changed nothing. **Compaction**
rewrites the log as the `HEADER`, then one `APPLY` per record of `F`, every
authorization record first and then every data record (each part in index
order), followed by one `EXPIRE(horizon)` if the store has a horizon.
**Replay** (opening a store) checks the `HEADER`, requires the capacities it
is opened with to be at least the logged ones, starts from the empty state
with the logged founding key, and performs the entries in order; every
operation is a deterministic function of the held set, and after compaction
every authorization record is admitted and so is every data record, because
the authorization part is complete before the first data record and `F` is
an antichain under `dom`. T18 states the result: the same held set and the
same index entries as sets (array order may differ after compaction).

**Order of operations and room (D11, E1, E2).** Applying a decoded,
verified frame runs these steps; all classification happens before anything
changes, and on every refusal nothing changes:

0. Wrong `ns`, or an authorization record whose `root_pk` field is not the
   store's founding key: `MALFORMED`. (Two key pairs can share a 128-bit
   `ns` at about 2^64 work; this check makes the decoder, the capacity rows
   and `root_void` agree on which key is the founding key.)
1. A data record that is not admitted: `INADMISSIBLE`.
2. Already held: `OK`, no change.
3. Dominated by a held record: `DOMINATED`. It needs no room in the
   frontier, the log or the index, and never gets `NO_SPACE`.
4. A `DEL` with `t ≤ horizon` (expired on arrival, below): applied for its
   effect. If it dominates nothing held, nothing changes; otherwise its
   dominated records leave `F` and one `APPLY_EXPIRED` entry is logged (and
   it needs only log room). Status `OK`; it is not held.
5. Room. Data records share one **data capacity** (`data_cap`). Every signer
   has its own **slice** of `slice` authorization records (at most
   `Slice_Max`), in one of `Signers_Max` = 16 slots; slot 1 is reserved for
   the founding key, and a slot is assigned to a certified root when its
   first record is held and never freed (none of a signer's records can
   leave `F` except under another of its own). A record that dominates a
   held record frees that record's slot, which is always in its own row
   (§3). A data record whose capacity is full and that frees nothing:
   `NO_SPACE` (the caller compacts, deletes, or gives up). An authorization
   record whose signer's slice is full and that frees nothing, or whose
   signer is new when all 16 slots are taken: `AUTH_FULL`. Not enough log
   bytes for the entry: `NO_SPACE`. The index always has room for what `F`
   holds, and `W` (at most one subject per held `GRANT`) always has room.
6. Apply: drop what the record dominates, hold it, append `APPLY`, index it.

**What `AUTH_FULL` means.** No key is ever dropped silently, and a refused
record changes nothing; but which of an over-quota signer's records a
replica holds then depends on arrival order, so replicas can disagree
permanently about that signer's surplus records, about data records admitted
only through its surplus `GRANT`s, and about what those data records
dominate. Honest roots never reach their slice (the honest-issuer rules,
§10.3) and the founding key certifies at most 15 roots (A1), so only a stolen
root can cause this, it cannot touch any other signer's slice, and once it is
root-voided everything its surplus admitted reads `void`. Byte-for-byte
agreement then returns only by re-founding. The slice size must be the same
at every replica of a collection (the C ABI fixes it to `Slice_Max`), since
replicas with different slices would disagree honestly.

**Drop rule.** A record leaves `F` iff

```
dom(x, F)                                                  -- deterministic, membership-free (T3)
∨ (x is DEL ∧ x.t ≤ horizon)                               -- tombstone expiry
```

**Expiry is an operation on `F` (D10).** `Expire(now_local)` computes

```
horizon := min(now_local, maxceil(F)) − del_ttl_eff(F)       -- in 64 bits; below 0 means "none"
```

(64 bits so that `x.t + del_ttl` never wraps; at `x.t = 2^48 − 1` a 48-bit
sum would turn an immortal tombstone into an instant one). Clamping the clock
to `maxceil` bounds expiry by the roots' clocks rather than any one device's:
a clock set far ahead (spoofed time, or the user) cannot expire every
tombstone at once and make arriving `DEL`s expire on arrival. If `horizon` is
above the store's horizon, `Expire` removes from `F` exactly the `DEL`s with
`t ≤ horizon` and sets the store's horizon; if it is below (a clock stepped
back, or `del_ttl_eff` raised), it only lowers the store's horizon, so fewer
arriving `DEL`s expire on arrival and A4′ is not narrowed; a `DEL` already
removed stays removed, and one that arrives again is applied and held until
it expires again. `EXPIRE(horizon)` is logged iff the call removed something
or lowered the horizon, so periodic calls do not grow the log; a raise that
removed nothing is kept in memory only, and a reopened store's horizon is
then at most the live one, which only makes it hold more until its next
`Expire`. The registers do not change, and removing records from a frontier
leaves a frontier. `del_ttl_eff` is the largest `del_ttl` of the
non-root-voided rosters (§3), each clamped to [7 days, 3 650 days] at decode:
a stolen root can neither set it to zero to mass-resurrect deleted data nor
shorten it below what an honest root set, and lengthening ends when it is
root-voided. With no horizon yet, nothing is expired.

The second clause is **apply-then-expire**, not refuse-on-arrival: an
arriving `DEL` with `t ≤ horizon` is always applied (it dominates and frees
the entity's values) and only then, being expired, not held. Refusing an
expired `DEL` on arrival would let two
replicas with a two-millisecond skew diverge and then resurrect the entity
on both. With apply-then-expire, a skewed pair converges on the next
exchange (the replica still holding the `DEL` re-sends it; the other
re-applies and re-expires it; the cost is one frame per session until both
expire it) and the only residual is the documented one: a straggler that
never saw the `DEL` and reconnects after `del_ttl` resurrects the entity with
its stale fields, which the user re-deletes. That requires a device offline
for longer than `del_ttl` (default 180 days); it is a liveness assumption
(A4′), stated as such, not hidden in a safety theorem.

**Why A4′ and not a sync-frequency assumption.** "Every member syncs with
some member once per `del_ttl`" is not enough: there is a four-member
schedule satisfying it in which the `DEL` reaches two members, both expire
it, and a third member that never saw it re-seeds the entity everywhere.
The assumption expiry needs is **A4′: every `DEL` reaches every member
within `del_ttl` of `d.t`**, that is, sync-graph diameter times sync period
is below `del_ttl`. Its failure mode is resurrection of deleted data, never
destruction of live data, which is why tombstone expiry is preferred over
root-signed snapshots.

**Chased tombstones (residual).** A `DEL` that
dominates a far-future `PUT` must chase to `t > p.t`, so its tombstone lives
`δ + del_ttl` where `δ` is how far ahead the pinning clock was, bounded by
`maxceil − now`. Ordering on a separate counter would remove it, but a
writer-chosen expiry clock is worse than an inflated one. The residual is storage of one tombstone frame per
pinned entity for at most one horizon beyond `del_ttl`.

**Bounds.** After `Expire`, `|F(ns)| ≤ live cells + DELs younger than
del_ttl_eff + authorization records`, with the data part bounded by
`data_cap` and the authorization part by `Signers_Max × Slice_Max = 16 × 512
= 8 192` records (rosters, `GRANT`s and `REVOKE`s of each signer within its
slice); so `|W| ≤ 8 192`. No vectors, no per-peer state, no shells, no
pending buffers.

## 8. Reconciliation and digest

Elements are the records of `F` for one `ns`, keyed
`kind:u8 ‖ ent[16] ‖ fh[32] ‖ h[32]` (81 bytes, `fh` = BLAKE2b-256 of the
field name, zero where a kind has no entity or field) with `ROSTER = 0,
REVOKE = 1, GRANT = 2, DEL = 3, PUT = 4`, compared bytewise. Authorization
records sort first: the key space splits at `Data_Lo = 03 ‖ 0^16 ‖ 0^32 ‖
0^32` into the **authorization range** `[Min_Key, Data_Lo)` and the **data
range** `[Data_Lo, Max_Key)`, where `Min_Key` is all zeros and `Max_Key` is
`FF ‖ 0^80`.

**Fingerprint = digest (D7).** For a record `e` with content hash `h(e)`
(32 bytes, in the order BLAKE2b produced them):

```
B_i(e)     := BLAKE2b-256("kome/acc" ‖ h(e) ‖ u8(i))           for i = 0..15
acc(e)     := Σ_{i=0..15} LE(B_i(e)) · 2^(256·i)  mod 2^4096,   LE(B) := Σ_j B[j] · 256^j
ACC(R)     := Σ_{e ∈ R} acc(e)  mod 2^4096
fp(R)      := BLAKE2b-256("kome/fp" ‖ u64(|R|) ‖ ACC_le(R))
digest(ns) := fp(F|ns)
```

Equivalently `acc(e)` is the 512-byte string `B_0 ‖ … ‖ B_15` read as a
little-endian integer, and `ACC_le(R)` is the 512-byte little-endian form
(byte `k` is `⌊ACC/256^k⌋ mod 256`). `"kome/acc"` is the bytes `6B 6F 6D 65
2F 61 63 63`, `"kome/fp"` is `6B 6F 6D 65 2F 66 70`, and `u64(|R|)` is
big-endian. The accumulator is the only little-endian quantity in Kome; every
other integer is big-endian. `spark/vectors/digest.txt` holds the normative
known-answer vectors.

`ACC` is homomorphic over disjoint union, so prefix sums answer any sub-range
cheaply: the snapshot stores `P(K) = ACC(L(1 .. 64K))` for every full block
`K = 1 .. ⌊n/64⌋` and one more entry, the total `P_end = ACC(L(1 .. n))`
(D15). Write `Pre(x) = ACC(L(1 .. x))`, so a range is `Pre(b) − Pre(a)`. Each
end `x` starts from the nearest stored point `A(x)` (the block boundary below
or above, or `P_end` for an end in the tail after the last full block), which
is at most 32 element terms away: `Pre(x) = P(A(x)) + fwd(x) − bwd(x)`, with
`fwd` the terms walked forward and `bwd` those walked backward. The range is
computed with two accumulators, `Plus = P(A(b)) + fwd(b) + bwd(a)` and
`Minus = P(A(a)) + bwd(b) + fwd(a)`, and one subtraction `Plus − Minus`: at
most 64 big-integer additions and exactly one subtraction, for every range
including those that end in the tail. That is 8
bytes amortized per element, and a snapshot cache of the prefix sums
stays valid between sessions, where a per-session keyed sum would force
O(n) hashing per session. A k-sum attack on a 4096-bit modulus
costs about 2^128 and needs 2^64 inserted records. A 256-bit sum would be
breakable in about 2^32 by a member, which is why the sum is 4096 bits.

**Messages.** All integers big-endian; `g` is the size of the reply group a
message belongs to (0 only for a root `RANGE`).

```
OPEN      5 ‖ proto:u8 ‖ ns[16] ‖ n_rv:u8 (≤ 15) ‖ n_rv × frame[275]
HELLO     1 ‖ n_auth:u32 ‖ n_data:u32 ‖ digest[32] ‖ cred_len:u16 ‖ cred[cred_len]
RANGE     2 ‖ g:u8 ‖ lo[81] ‖ hi[81] ‖ count:u32 ‖ fp[32]
ELEMENTS  3 ‖ g:u8 ‖ lo[81] ‖ hi[81] ‖ n:u8 ‖ n × (key[81] ‖ flen:u32 ‖ frame)
HAVE      4 ‖ g:u8 ‖ lo[81] ‖ hi[81] ‖ n:u8 ‖ n × (key[81] ‖ flen:u32 ‖ frame)
```

**OPEN (pre-gate, D13).** `proto = 1`; `ns` is the
collection (a mismatch aborts the session, so the digest that follows is
bound to it); the frames are the sender's **root-void set**: every
founding-issued `REVOKE` in its `F` whose subject has signed an
authorization record the sender holds, at most 15 (`Signers_Max − 1`), so an
`OPEN` is at most 4 144 bytes. The receiver checks each frame is a `REVOKE`
signed by the founding key, verifies and applies those whose subject is a
signer it holds and is not yet root-voided (skipping the rest unverified,
which bounds pre-gate work), and only then evaluates the gate (§6). The
frames are signed records that every replica admits anyway; applying them
before authentication is safe, and the transport rate-limits pre-gate
work per peer.

**HELLO (post-gate, D13).** `n_auth` and `n_data` are the sender's element
counts in the two ranges (they size the round-0 sketch and the budgets, and
enter them only as `min(claimed, Held_Max)`, with `Held_Max` the frontier's
bound, the one constant both the frontier and reconciliation use); `digest`
is `digest(ns)` of the sender's snapshot; `cred` is the sender's credential:
the frame of a roster in its `F` whose members include the sender's Noise
static key as a `dh_pk` (normally `ROSTER_eff`), at most 10 099 bytes, so a
HELLO is at most 10 142 bytes. HELLO carries **no register values**. A side
sends its HELLO only once it has admitted the peer, so a non-member learns
no membership list. The receiver refuses a credential that is not such a
roster, otherwise decodes, verifies and applies it like any authorization
record, and re-evaluates the gate; if that admits the peer and its own HELLO
is unsent, it sends it now (this is how a newly added member reaches a stale
replica: the stale side admits the newcomer once it sees the newcomer's
credential). If neither side can admit the other, the session times out.
Nothing a lying peer puts in an `OPEN` or a HELLO is trusted: a false count
or digest only costs rounds within the session budgets, and the frames are
signed records. Equal digests end the session after the HELLO exchange
(under A2 they mean equal frontiers). Each side takes its snapshot when it
encodes its HELLO, after applying the peer's `OPEN` (and the peer's
credential, if it came first).

**Session (D14).** Both sides send `OPEN` after the Noise handshake, then
exchange HELLOs as above. Then:

- **Auth phase.** The initiator sends the root `RANGE(g = 0, [Min_Key,
  Data_Lo))`. When nothing it asked is open (its pending weight is 0), the
  authorization phase is complete on its side.
- **Data phase.** The initiator then sends the root `RANGE(g = 0, [Data_Lo,
  Max_Key))`, and when nothing it asked is open again, it is **done**. The
  responder accepts the data root only once it has received the
  authorization root and nothing it asked is open (on an in-order transport
  the initiator answered everything first), and it is done when it has
  received the data root and nothing it asked is open.
- Only the initiator sends `g = 0` messages, exactly these two, in this
  order, with exactly these bounds. Any other `g = 0` message (an
  `ELEMENTS` or `HAVE` with `g = 0`, a root `RANGE` with other bounds, a
  repeated root, a data root before the authorization root) is refused and
  changes nothing.

After the authorization phase both sides hold the same authorization
records (unless one side refused one with `AUTH_FULL`, §7), hence the same
`maxceil` and `W`, so every data record a peer ships in the data phase is
admissible on arrival: this is what makes the exchange clause of T4 true
without registers in the HELLO. The initiator is the Noise initiator.

**Replies.** Every `RANGE` or `ELEMENTS` obliges exactly one reply group;
`HAVE` obliges nothing. With `window` = our snapshot's elements in
`[lo, hi)`:

- `RANGE` whose `(count, fp)` equal ours over `[lo, hi)`: one empty `HAVE`
  over `[lo, hi)` (the confirm).
- `RANGE` otherwise, `|window| ≤ 4`: `ELEMENTS` over `[lo, hi)` carrying
  exactly `window` (one `ELEMENTS` per element, each over a sub-range that
  holds that element alone, when they do not fit one message).
- `RANGE` otherwise: at most 16 `RANGE`s that tile `[lo, hi)`, each carrying
  our exact count and fingerprint of its sub-range and holding strictly
  fewer of our elements (balanced: `⌊n/16⌋` or `⌈n/16⌉`).
- `ELEMENTS`: deliver exactly the listed items not in our snapshot; then if
  `|window| ≤ 4`, `HAVE` over `[lo, hi)` carrying exactly `window` minus the
  listed items (one empty `HAVE` if none), else the split above.
- `HAVE`: deliver exactly the listed items not in our snapshot; no reply.

A reply never mixes a `HAVE` with other kinds, and every plan in it is
exact (a `RANGE` carries our true count and fingerprint, an `ELEMENTS` all of
our elements of its range). Descriptors are self-contained, and within a
phase duplication and reordering cost rounds, not correctness; but the phase
gate assumes an in-order transport (Noise over a stream): a data root that
overtakes the last authorization-phase reply is refused, and the session
then never completes. **Under loss, or reordering of a root message, a
session never completes**: the caller times out and starts a new session
from the `OPEN`.
A session with no loss takes at most `⌈log₁₆ N⌉ + 2` rounds per phase; under
loss, convergence holds given fairness at the session level (some session
eventually completes), which T7 states explicitly. Per-session budgets
bound what a hostile peer can draw: the messages accepted, the `RANGE`s
emitted and the item bytes emitted, each counted over both phases. A member
that always claims `Held_Max` elements gets the largest budgets in every
session; it is authorized to read `F` anyway, and limiting how often a peer
may open sessions is the transport's job.

**Message size (D12).** Every message is at most `Max_Message_Len` = 48 KiB.
A frame is at most 41 136 bytes (a `PUT` with a 32-byte field and a
40 960-byte value), which is below the 48 902 bytes one `ELEMENTS` item can
carry (`48 KiB − 165 − 85`) and below the sealed-bundle plaintext bound, so
every well-formed record can be shipped in one message on every transport;
the implementation checks both inequalities at compile time.

**Round 0: one-round set difference (C8).**
At the start of each phase each side may send an invertible Bloom lookup
table over the 32-byte element hashes of that phase's range, sized from the
HELLO counts and clamped so one sketch fits in one message (at most 1 000
cells of 44 bytes). Subtracting the two tables and peeling yields the exact
symmetric difference in one round when it is small, which is the common
case; peeling failure and a false decode are both detected (every
recovered hash must verify against a held or received record) before any
state is written, and the phase falls through to the range protocol above.
The sketch is homomorphic, so it is cached per collection and updated per
record. It adds nothing to the trusted core: every element it names is
still delivered and checked as a record.

**Transports.** Noise XX for interactive sync, with the device's `dh_pk` as
the static key (§6 gate). Sealed bundles for store-and-forward:

```
bundle = ns[16] ‖ u16(epoch) ‖ nonce[24] ‖ XChaCha20-Poly1305(k_b, nonce, AD = ns ‖ u16(epoch), plaintext)
k_b    = BLAKE2b-256("kome/bundle" ‖ k_epoch ‖ ns)
nonce  = BLAKE2b-256("kome/bnonce" ‖ k_b ‖ plaintext)[0:24]
```

accepted only under `ROSTER_eff.epoch`. `k_e` is shared by every member, so
the nonce must never come from a per-device counter; it is synthetic, as for
boxes, and identical plaintexts give identical bundles, which reveals only
that. The plaintext is a list of `ELEMENTS` items totalling at most
`Max_Message_Len` bytes, sorted by element key; the receiver applies the
items in element-key order (authorization records first: the
authorization-first pass of T4 (a)). Relays see ciphertext, `ns`, the epoch
and the transport's routing key.

## 9. Proof obligations

Stated so that each is a finite, first-order fact about sets of records.
Core-Lean-provable ones are marked ✓; the two hard ones are marked ✗.

- **T1 ✓ Total order.** On well-formed records with `h` injective, `v` is a
  strict total order.
- **T2 ✓ Monotone domination.** `H ⊆ H' ⇒ dom(x, H) ⇒ dom(x, H')`.
- **T2' ✓ Upward closure.** `y dom x ∧ z dom y ⇒ z dom x`, for every kind.
- **T3 ✓ Frontier homomorphism.** `F(H₁ ∪ H₂) = F(F(H₁) ∪ F(H₂))` and
  `F(F(H)) = F(H)`. Hence dropping dominated records anywhere, at any time,
  changes no future frontier.
- **T4 ✓ Convergence.** With state `F`, admission of data records under
  `(maxceil(F), W(F))`, and inadmissible records discarded: (a) one pass
  that applies a set's authorization records before its data records, from
  any frontier, yields `F` of the admitted records of the union; (b) two
  passes over the same records in any order and with any duplication (the
  second pass re-offering what the first refused) yield the same; so two
  replicas that applied the same records hold the same `F`. (c) After a
  complete two-phase reconciliation (§8) both replicas hold `F(F_A ∪ F_B)`
  of the admitted records, including records that were inadmissible at one
  side before the session. All three hold for runs with no capacity refusal
  (`NO_SPACE`, `AUTH_FULL`); a `NO_SPACE` record is re-offered later, and
  `AUTH_FULL` is the stated residual of §7.
- **T4' ✓ Monotone admission.** If every authorization record of `H` is in
  `H'` then `adm(r, H) ⇒ adm(r, H')`; `maxceil(F(H)) = maxceil(H)` and
  `W(F(H)) = W(H)`, so neither register shrinks along any history,
  including rosters of lower generation or ceiling. Admission never reads
  `REVOKE`, `root_void` or `W_eff`.
- **T5 ✓ View determinism.** `deleted_at`, `cell`, `exists`, `maxceil`, `W`,
  `root_void`, `W_eff`, `void`, `ROSTER_eff` and `del_ttl_eff` are functions
  of `F` as a set (and the constant `root_pk`) alone; `ROSTER_eff` uses the
  whole roster tuple as its tie-break, so it does not depend on list order
  even without A2. Moreover `W_eff`, `root_void` and `ROSTER_eff` of `F(H)`
  equal those of `H`.
- **T6 ✓ Digest.** `digest(ns) = fp(F|ns)`; `ACC(R₁ ⊎ R₂) = ACC(R₁) +
  ACC(R₂)`; under k-sum hardness, `fp(R₁) = fp(R₂) ⇒ R₁ = R₂`.
- **T7 ✗ Reconciliation.** From `F_A, F_B` over `N` elements, a session is
  two sequential range reconciliations over a partition of the key space;
  each terminates in `≤ ⌈log₁₆ N⌉ + 2` rounds without loss, by the measure
  `(μ, k)` with `μ([lo, hi))` the two sides' element counts in the range and
  `k = 1` for a `RANGE`, 0 for an `ELEMENTS`; both sides then hold
  `F(F_A ∪ F_B)`. Under loss no session completes, and convergence follows
  from fairness at the session level. (The substantial Lean project.)
- **T8 ✓ Chase.** If `floor.t < maxceil` then `v_emit > floor`; always
  `v_emit.t ≤ maxceil`, and `v_emit.seq` exceeds every `seq` this device
  emitted in this collection and every own `seq` held; the outcome of the
  emission does not depend on `h` (§5).
- **T9 ✓ Bounded pin.** No admitted data record has `t > maxceil`; once a
  roster with a higher ceiling is applied, every honest write to any cell
  is unshadowed.
- **T10 ✓ Equivocation.** Two distinct records with equal `(author, seq)`
  are ordered identically everywhere; `F` is unaffected by arrival order.
- **T11 (liveness) Tombstone expiry.** (a) After `Expire` at a horizon, `F`
  holds no `DEL` with `t ≤` that horizon, and `|F|` meets the §7 bound;
  expiring a frontier leaves a frontier with the same registers.
  (b) Apply-then-expire: two replicas whose held sets differ only in that
  one holds a `DEL` `d` with `d.t ≤ h` and the other does not agree, after
  the same further records, a re-sent `d` and an `Expire` at `h`, on every
  record. (c) Under A4′, after every replica has expired `d`, no replica
  holds a record `d` dominated.
- **T12 ✓ Revocation locality.** Applying a `ROSTER`, `REVOKE` or `GRANT`
  changes `F` only at that record and the records of its own kind and key
  it dominates; it never adds or removes a `PUT` or `DEL`. `root_void` is
  monotone in `F`; for a fixed `root_void` set, the `REVOKE` clause of
  `void` and `W_eff` are monotone in `F` (so a `GRANT` can only un-void, a
  `REVOKE` only void).
- **T13 ✓ Bounds.** Every emitted record satisfies the §2 layout; `seq`, `t`,
  `gen`, `rev_seq` never wrap; at a bound, emission fails with no side
  effect; every refusal of an apply leaves the state unchanged.
- **T14 ✗ Epoch secrecy.** A key absent from roster `e` and all later rosters
  cannot derive `k_e'` for any `e' ≥ e`; a root-voided root cannot derive any
  key of a segment opened after its revocation. A paper reduction to
  hash-chain one-wayness, X25519 CDH, BLAKE2b as a PRF and
  XChaCha20-Poly1305 with a unique `(key, nonce)` per plaintext; not a Lean
  theorem.
- **T18 ✓ Replay.** For every store the implementation writes, replaying its
  log from the empty state, with the logged founding key and capacities at
  least the logged ones, yields the same held set (hence the same registers
  and digest) and the same index entries, both as sets; the replayed
  horizon is at most the live one; after compaction every replayed `APPLY`
  succeeds. (T15–T17 are reserved for extension F.)

**Assumptions.** A1 Ed25519 (RFC 8032) is unforgeable under strict
verification; the founding key is never stolen, and its holder certifies at
most 15 roots. A certified root may be stolen: until a replica holds its
root revocation it can do there what a root does (§6 lists it); afterwards
everything it issued stops counting in that replica's views, and under A7
nothing it or its grantees sign afterwards reaches that replica. Its
permanent residue is `maxceil` raised up to the largest cap ever certified
for it, its records in its own slice, and, if it overflowed its slice, the
disagreement about its surplus (§7). Honest roots stay within the
authorization bounds (§7: `Signers_Max`, `Slice_Max`, `Links_Max`, and the
epoch space); beyond them a collection is re-founded. A2 BLAKE2b collision-resistant; the
4096-bit sum is k-sum hard. A3 Some root device refreshes the roster within
each horizon (writes degrade to ceiling ties otherwise; convergence
unaffected). A4′ For tombstone expiry only: every `DEL` reaches every member
within `del_ttl` of `d.t`. A5 Writers persist `seq_self` per collection
(violations are detected). No assumption is needed about register values
on the wire: none crosses it. **A7 Revocation arrives first** (E7): every replica receives a `REVOKE` before it receives
any record signed after that `REVOKE` by its subject, and a root revocation
before any record signed afterwards by a key that root granted. Only the H8
bounds (§5) and the post-revocation guarantees of §6 depend on it;
convergence does not. When it fails, a stale replica admits such records
and relays them, every replica then holds them flagged `void`, and the
bytes they overwrote or deleted are lost. **No clock assumption for
convergence.**

## 10. What is open

1. **Lean model of this design.** `lean/Kome/Frontier.lean` proves T1,
   T2, T2', T3, T4 (`auth_first`, `convergence_two_pass`, `convergence`),
   T4', T5, T8, T9, T11, T12, T13 and T18 over finite lists, machine-checked
   (`lean/build.sh`), with no `sorry` and only Lean's standard axioms; T3 is
   derived from a general "sandwich" lemma. The model has the five record
   kinds, per-signer product-order roster domination and per-`(issuer,
   subject)` grant domination, `maxceil` and `W` as functions of the held
   list, the discard model, expiry, and the views `rootVoid`, `wEff`,
   `voided`, `rosterEff` and `delTtlEff`. Certificates, capacity and the
   horizon's clock clamp are outside the model, which assumes well-formed
   records. T7 remains open; T14 is argued on paper.
2. **Toolchain.** Lean comes from nixpkgs (`nix shell nixpkgs#lean4`), since
   `elan` could not be downloaded in the authoring environment; `lean-toolchain`
   names 4.35.0 for anyone using `elan`.
3. **Root ceremonies (`Kome.Roster`, phase 8).** Certification (short
   caps, renewed), the out-of-band delivery of segment tops to roots,
   segment opening (founding key only, §6), the recovery procedure (§6),
   and the honest-issuer rules, written down here but not yet built: a new
   roster has `gen = 1 +` the largest `gen` of the non-root-voided rosters
   in `F`, `ceiling_t` at least the largest ceiling of the signer's own held
   rosters (so it dominates all of them and the signer keeps one), an epoch
   within the current segment and never above its top; a root stays within
   its slice (`Slice_Max` records) and the founding key within 15
   certificates; a member removal bumps the epoch.
4. **Conflict visibility.** This design keeps one value per cell and frees
   losers' bytes. An application that wants visible conflicts gets them
   through the typed-fields extension (C10: the `MVREG` type plus parent
   hashes) rather than a different lattice.
5. **Quotas.** Floods by an authorized writer are bounded only by revocation
   (under A7), owner `DEL`s and the data capacity. A per-author quota at the
   room step is not adopted (E8): it is a capacity refusal, so under a flood replicas disagree about which of
   the flooder's records they hold, as with the data capacity; it protects
   honest room but strengthens no guarantee, and the right bound depends on
   the application. A per-author byte quota in the roster, enforced by the
   application, would not touch the lattice.
6. **The C ABI.** Not designed yet. Its shape follows from the packages:
   `set/get/delete/exists/scan` over records, `GRANT`, `REVOKE` and roster
   operations, `session_*` over Kome.Reconcile, and a digest whose value
   equals the sync fingerprint. Statuses are Kome's `Status`, including
   `AUTH_FULL`; `CLONE_SUSPECTED` is an out flag beside the status.
7. **Typed fields.** The extension (C10) composes with the core; build it
   after T7 is proved, when an application asks for engine-side counters or
   sets. Estimated at about 7.5 person-weeks over the core.
8. **Sketch sizing.** The sketch cap (1 000 cells) is set by the current
   maximum message length; raising the message bound raises the cap. Below
   the cap the common sync is two round trips per phase; above it the range
   protocol runs as before.
9. **Interoperability residue.** A record's frame is never re-encoded, so
   any verifier with RFC 8032 Ed25519 and BLAKE2b can check Kome records;
   the accumulator's byte order (§8) is the one place a second
   implementation must take care.

10. **Two log decisions taken in the SPARK store.** (a) Capacities: the
    `HEADER`'s capacities are always those of `F`, so reopening with larger
    capacities rewrites the six capacity bytes of the `HEADER` (the one write
    that is not an append) and keeps every other byte; reopening with smaller
    ones is refused (`No_Space`). (b) Compaction: if fewer than 7 bytes remain
    after the frames, the trailing `EXPIRE(horizon)` is omitted; the reopened
    replica then has a lower horizon, which T18 allows.

Estimated effort: roughly 24 person-weeks for the Lean theorems plus the
SPARK core, about 3.5 more for the sketch (C8) outside the trusted core,
about 3 for multiple roots (C9), and about 7.5 for typed fields (C10) when
built; T7 is the long pole throughout.
