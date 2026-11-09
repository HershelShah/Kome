# Kome: the frontier store

Kome is built on a single lattice. This lattice is the *frontier* of a set
of signed records under one strict total order. No policy question
(authorization, far-future clocks, revocation) is part of the merge. Each
policy question is either a monotone admission rule or a pure view. §1 gives
the decisions, §2–§8 give the design, §9 gives the theorems, and §10 gives
the open items.

## 1. Decisions

**The governing rule.** The frontier lattice is sound if and only if every
kill predicate is a down-set of the record order on its key. Every kill
predicate in this document is such a down-set, and no decision changes the
version order.

### 1.1 The core

| # | Decision |
|---|---|
| C1 | The state is the frontier. Merge is set union. Then merge drops every record that a newer record on its key dominates (§3). |
| C2 | The ceiling is a *monotone* admission rule, not an arrival gate. The store refuses a record above `maxceil`, and admission never shrinks (§4). |
| C3 | Tombstones use apply-then-expire, not refuse-on-arrival. The store holds a `DEL`, and the `DEL` dominates. Only expiry at a horizon removes it (§7). |
| C4 | Cross-author `DEL`s dominate in the store, so deletion is durable and needs no membership knowledge (§3). |
| C5 | A device adopts no clock from a peer, and a record never changes the device's clock. A writer's clock affects only that writer's records, with one bounded exception: a write *chases* the floor of its cell (§5), so a cell that another writer pinned ahead raises the `t` of later writes on that cell, by at most `maxceil − now`. Adoption is per cell, through chase, never device-global (the H8 "Clock ahead" row in §5 and the chased-tombstone residual in §7). |
| C6 | Revocation carries a `from_t` and is a view, not a gate. It voids records in the views and never feeds admission (§3, §6). |
| C7 | Read control uses hash-chained epoch keys (§6). |
| C8 | Reconciliation starts with a one-message IBLT sketch. Then it uses the range split (§8). |
| C9 | There are several root keys, and the founding key certifies them. So the loss of a root is recoverable. There are no per-field writer rules (§6). |
| C10 | Typed fields (counters, sets, multi-value registers per `(cell, author)`) are a specified extension. Build them only when an application needs them. They need `W`, a saturating fold, and a cursor to read the view output (§4). |

### 1.2 Authorization, storage and wire

| # | Decision |
|---|---|
| D1 | Every authorization record carries a *signer block*. The signer is the founding key or a root that the founding key certified (`cert_sig` over `ns ‖ signer ‖ cert_cap`). Only the founding key certifies, so only the founding key adds roots. Admission depends only on the bytes (§2, §6). |
| D1′ | A record kind `GRANT(subject)` holds write access. Its key is `(ns, issuer, subject)`, and it carries a *write cap*: `2^48 − 1` when the founding key issued it, else the issuer's `cert_cap`. `W(F)` is the set of `GRANT` subjects in `F`, and `wcap(F, k)` is the largest cap of the `GRANT`s of `k` in `F`. `maxceil(F)` is the largest `ceiling_t` of the rosters in `F`. A roster leaves `F` only under a roster of the same signer with a ceiling at least equal to its own; a `GRANT` leaves `F` only under a `GRANT` of the same issuer and subject with a cap at least equal to its own. The three registers are functions of `F`, and they never shrink (§3, §4). |
| D2 | Only the founding key root-voids. The store ignores `from_t` for a root-void. Nobody can revoke the founding key. When a root is root-voided, all that it issued (rosters, `REVOKE`s, `GRANT`s) no longer counts in any view. Keys that only that root granted read `void` through the effective-writer view `W_eff` (§3, §6). |
| D3 | Canonical form is a property of `Header`. Decode produces it, and the lattice requires it. A roster dominates another roster of its signer if and only if its `gen` is *strictly* greater *and* it is not lower in `ceiling_t` or in `epoch` (a product order). `h` never decides between two rosters of one signer: at equal `gen`, both stay, and the view `ROSTER_FORK` reports the pair. `ROSTER_eff` is the `(epoch, gen, h)`-maximum, and the whole roster tuple breaks a tie (§3). |
| D4 | Signatures are RFC 8032 Ed25519 (with SHA-512 inside the signature). They come from the `monocypher-ed25519` part of monocypher. Tests check them against RFC 8032 and Wycheproof vectors. BLAKE2b is the hash for all values that Kome derives (§2, A1). |
| D5 | There is no root X25519 key. Each `ROSTER` carries its own `box_pk`, and the roster signature covers it. `box_pk` is the X25519 public key of `eph_sk = BLAKE2b-256("kome/eph" ‖ k_e ‖ ns ‖ u16(e) ‖ signer ‖ u48(gen))`, which `Kome.Epochs` computes from the epoch key: no caller draws it. `Kome.Roster.Build` seals that roster's boxes with it and wipes it (§2, §6). |
| D6 | `wrap_key` hashes the DH output with `box_pk`, the two member keys, `ns` and `epoch`. The box nonce is synthetic, `BLAKE2b(wrap_key ‖ k_e)`. The member calculates it again and checks it. Bundle nonces are also synthetic. The chain step and the bundle key are keyed BLAKE2b, one PRF under one key (§6, T14). |
| D7 | The accumulator is little-endian and recorded exactly. The tags are bytes (§8). |
| D8 | The write path selects `(t, seq)` without `h`, and then it calculates the hash. The result does not depend on `h`. `seq_self` is per collection (§5). |
| D9 | Kome persists only `F`. The log is a `HEADER` (`ns`, `root_pk`, `salt`, the data capacity, the slice as a check) and a journal of `APPLY`, `APPLY_EXPIRED`, `EXPIRE` and `EXPIRE_NONE` entries. The store logs `EXPIRE` only when it removes a record or lowers the horizon. Compaction writes authorization records first, and the store runs it on its own when the entry count passes `2·|F| + c`. Replay gives the same frontier as a set (T18, §7). The log is plaintext; the host owns its integrity and confidentiality at rest (§7). |
| D10 | Expiry is an operation on the lattice state at `horizon = min(now_local, maxceil) − del_ttl_eff`. `del_ttl_eff` is the largest `del_ttl` of the rosters that are not root-voided (decode refuses a value outside `[Del_TTL_Min, Del_TTL_Max]`, §2 rule 3). A roster leaves `F` only under a roster of its signer with a `del_ttl` at least equal to its own, so `del_ttl_eff` never falls except when a root is root-voided: no root, stolen or honest, can make tombstone life shorter by domination (§3, §7). |
| D11 | The order of checks is admission, duplicate, domination, room. A dominated record never needs room. No refusal changes anything (§7). |
| D12 | `Value_Max` = 40 960, so every frame fits in one 48 KiB message (§2, §8). |
| D13 | No register value goes on the wire, so no assumption about register values on the wire is needed. A pre-gate `OPEN` carries `ns` and the sender's root-void set: one founding-issued `REVOKE` for each root-voided subject in its `F`, at most 15 subjects, whatever else the sender holds. The responder answers an `OPEN` only after the initiator's `OPEN` named its `ns`, and sends the set only to a peer whose Noise key some held roster lists. The receiver applies the set *before* it evaluates the gate. The post-gate `HELLO` carries counts, the digest and the sender's credential roster. That roster must list the sender's Noise key. A side sends `HELLO` only to a peer that it has already admitted. The authorization range is fully reconciled before the data range (§6, §8). |
| D14 | The session phases are `Auth` and then `Data`. Only the initiator sends root `RANGE`s: exactly two, with fixed bounds. Replies are exact windows. Within a batch (a reply group, a bundle, an import), every record with kind < 3 applies before any record with kind ≥ 3 (§8). |
| D15 | Prefix sums carry one more entry, the total. Any sub-range costs at most 64 additions and one subtraction, with the two-accumulator scheme (§8). |
| E1 | Data records have one capacity. Each signer has its own *slice* of authorization capacity, and the founding key's slice is reserved. The capacity of `W` is the total of the slices, so `W` never fills on its own. A data flood cannot fill another party's space, and a stolen root cannot either. Log bytes are a fourth class, shared by every record: the binding keeps `Log_Fits` (§7), so that a compacted log always has room for one more entry. The founding key keeps a *reserve* of 15 entries in its slice for root-voids (§10.3). Under these two duties, the founding key's `REVOKE` always lands (§7). |
| E2 | If an authorization record would exceed its signer's slice, the store refuses it with `AUTH_FULL` and changes nothing. If a record that `F` can hold does not fit the log, the store refuses it with `LOG_FULL`, and the binding compacts and retries. The store never drops a key silently (§7). |
| E3 | There is one hash chain per collection, in *segments*. Only the founding key opens a segment (on root-void, or when the chain reaches the top of a segment). Each roster carries links that let a member walk back across segments (§6). |
| E4 | `from_t` gives protection only against a lost key, not against a key that a thief uses. For a stolen key, revoke from 0 (§6). |
| E5 | Keys are canonical at decode: `box_pk`/`dh_pk` are reduced, not low-order and not the all-zero encoding, every Ed25519 key (`signer`, `subject`, `author`, `root_pk`, member `sign_pk`) is canonical and not small-order, `del_ttl` is in range, and the cert block is zero exactly for the founding key. Each record has one encoding (§2). That every listed member can open its box is not a decode check: `Kome.Roster.Build` makes it true by construction, because it derives `box_pk` from the secret that sealed the boxes (§6). |
| E6 | `root_pk` must be equal to the store's founding key. The effective certificate cap is the largest cap ever certified (§6). |
| E7 | Admission does not refuse the records of a revoked key. Instead, the design bounds a revoked key's reach with the write cap (`t ≤ wcap`, §4), states assumption A7 (no replica receives, from any source, a record that a revoked subject signed after its revocation), and makes the H8 bounds depend on A7. A refusal would give a stolen root a permanent primitive for mass deletion, and it would give up T3 (§6, §9). |
| E8 | The engine has no per-author data quota. A quota refusal is a capacity refusal, and under a flood the replicas would not agree about it. It stays an application policy (§10.5). |
| E9 | The frontier keeps one data array and one authorization row per signer slot. Its own discriminant sets the limit of each one (§7). |

## 2. Objects

**Identifiers.** A collection `ns` is 16 bytes and self-certifying:
`ns = BLAKE2b-256(root_pk ‖ salt)[0:16]`. `root_pk` is the collection's
**founding key**. An entity `ent` is 16 bytes. A field name is 1–32 bytes.
A value is 0–40 960 bytes. Blob chunks of 32 KiB fit, and a layer above the
engine cuts larger payloads into chunks. This bound makes every frame fit in
one reconciliation message (§8). An empty value is a value: it does not
free the cell, and it keeps using data capacity. `DEL` is the only removal,
and it has entity grain: it removes every field of its entity and no single
field. So an item that must be removable on its own (an entry of a shared
list, a chunk of a blob) is its own entity, not a field of a shared one
(§10.6).

**Version.** `v = (t : u48, author : [32]u8, seq : u48, h : [32]u8)`. Kome
compares versions lexicographically, with `author` and `h` as unsigned
256-bit integers. `h` is the record's content hash, so two different
records never compare equal, and the order is total by construction.
`t = 0` and `seq = 0` are ordinary values.

**Records.** A frame is `tag:u8 ‖ content ‖ sig[64]`, and `h = BLAKE2b-256(tag
‖ content)`. `sig` is an Ed25519 signature (RFC 8032) by the record's
signer over the 32 bytes of `h`. The verification predicate is normative
(§10.9): a signature `R ‖ S` under the public key `A` over the message `m`
is valid if and only if `A` and `R` are canonical point encodings (each
decodes to a point, with the `y` coordinate below `p`), `A` is not one of
the eight small-order encodings, `S < L`, and `[8][S]B = [8]R + [8][k]A`
with `k = SHA-512(R ‖ A ‖ m) mod L`. This is the cofactored equation.
`Kome.Crypto.Verify` is this predicate as a SPARK expression (the canonical
checks and the small-order check are byte comparisons; the group equation
is a private `Raw_Ed25519_Check` over monocypher), and nothing else. The
Wycheproof and torsion vectors in `spark/vectors/crypto.txt` are normative:
an implementation that accepts or refuses one of them differently does not
interoperate. A key that a `GRANT` names, a signer, `root_pk` and the
author of a data record are each subject to the same canonical and
small-order checks at decode. (The all-zero key is an order-4 point: a
`GRANT` to it would let anybody who can deliver frames forge data under
it.) Kome signs the bare 32-byte `h`, so a device key serves Kome and
nothing else: the key API generates each key from Kome's own seed, and it
neither imports nor exports a signing key (§10.3, §10.6). A key that an
application must import can only sign with Ed25519ph, a different
signature that Kome does not accept on records. All integers are big-endian. All
tags and labels in this document are ASCII bytes without a terminator. These
are the five layouts, exactly as `Kome.Records` encodes them:

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

The signature follows the content. `author` signs `PUT` and `DEL`. `signer`
signs `ROSTER`, `REVOKE` and `GRANT`.

**The signer block and root certificates (D1).** An authorization record
names its signer. The record's bytes prove that the signer is a root:

- `signer = root_pk`, `cert_cap = 0`, `cert_sig` = 64 zero bytes: the
  founding key signed the record; or
- `signer ≠ root_pk` and `cert_sig` is the founding key's signature over
  `BLAKE2b-256("kome/root" ‖ ns ‖ signer ‖ u48(cert_cap))`: the signer is a
  **certified root**. Its rosters must not set `ceiling_t` above `cert_cap`.

Only the founding key can make a certificate, so only the founding key adds
roots. A `GRANT` carries no cap of its own: its write cap (§3, §4) is its
issuer's `cert_cap`, or `2^48 − 1` when the founding key signed it. So a
key that a certified root granted can never write above that root's cap.
Certification occurs out of band (in a key ceremony). Then the
certificate goes inside every record that the root signs. Keep the founding
key cold (offline, or in a hardware token). The founding key signs
certificates, root revocations and an occasional roster, and nothing else.

To renew a certified root's `cert_cap`, the founding key issues a new
certificate. Nobody can narrow or withdraw a certificate. Every certificate
stays valid for every record, so **a root's effective cap is the largest
`cert_cap` ever certified for it**. Only root-voiding (§6) ends what
a certificate allows. So make caps short (at most `Cap_Lead` = 3 days ahead
of the wall clock, §7 and §10.3, where the ceremony cadence allows) and
renew them regularly. A certificate is not a record and takes no slice
entry, so renewals are unlimited: the bound of A1 is on *distinct*
certified signer keys (at most 15, `Signers_Max − 1`), not on
certificates. The founding device keeps a ceremony log of every
certificate it made (§10.3), because a dominated roster takes its
certificate with it, so "the largest cap ever certified" is not a function
of `F`. The cap is also a dead-man switch: if the founding device is lost,
`maxceil` stops at the largest cap when wall time passes it (§6).

**Well-formed** is a function of the bytes alone. A frame is well-formed if
and only if all these conditions are true:

1. Its length is exactly the layout's length, `flen` ∈ 1..32,
   `vlen` ≤ 40 960, `n_links` ≤ 15, and `n_members` ≤ 64.
2. For `ROSTER`, `REVOKE`, `GRANT`: `ns = BLAKE2b-256(root_pk ‖ salt)[0:16]`,
   the signer block is valid as above, and a `ROSTER` that a certified root
   signs has `ceiling_t ≤ cert_cap`. Every `ROSTER` has `gen ≤ ceiling_t`.
   (`ceiling_t` is a millisecond clock, so an honest `gen` is always far
   below it. The bound is byte-local, and for a certified root it caps
   `gen` at its `cert_cap`, so a stolen root cannot use up the `gen`
   space above 2^47: see §10.3.)
3. For `ROSTER`: `del_ttl` ∈ [`Del_TTL_Min`, `Del_TTL_Max`] (7 days and
   3 650 days, in milliseconds); decode refuses (`MALFORMED`) a value
   outside the range. `box_pk` and every member `dh_pk` are reduced X25519
   encodings (`u < 2^255 − 19`, bit 255 clear). None of them is one of the
   five reduced low-order encodings (0, 1, `p − 1`, and the two points of
   order 8), and `box_pk` is not `X25519_Public(0^32)`, the public key of
   the all-zero secret. (That every listed member can open its box is a
   property of how `Kome.Roster.Build` makes the roster, E5, not a decode
   check: no bytes of the frame can show it.)
4. For `REVOKE`: `sign_pk ≠ root_pk` (nobody can revoke the founding key).
   For `GRANT`, `REVOKE` and `ROSTER`: `subject`, `sign_pk`, `signer` and
   `root_pk` are canonical Ed25519 encodings, not small-order and not
   `Derive_Public(0^32)`, the public key of the all-zero seed.
5. The signature is valid, under the predicate above, under the signer
   (authorization kinds) or the author (data kinds).

Each well-formed record has exactly one encoding (unused buffer bytes are
zero in every in-memory representation). So `h` is a function of the
record, and under A2 it is injective on records.

**Why these five kinds.** `PUT` and `DEL` are the data. `ROSTER` carries
read access (the member boxes), the session gate, the epoch key and two
replicated parameters (`ceiling_t`, `del_ttl`). `GRANT` carries write
access. Its subject can be the author of `PUT`s and `DEL`s. The grant counts
in the effective-writer view only while its issuer is not root-voided (§3).

`GRANT` is separate from `ROSTER` because write access must be grow-only and
a function of the frontier. Roster membership is neither: a later roster
drops members, and dominated rosters leave the frontier. `REVOKE` is
separate from both because it must be grow-only. A later roster must never
undo a revocation. If it could, a root restored from backup could issue a
roster that drops a revocation.

## 3. The lattice

Let `H` be a set of well-formed records. **Domination** is:

```
dom(p, H) for PUT p    := ∃ q ∈ H : PUT, cell(q) = cell(p), q.v > p.v
                        ∨ ∃ d ∈ H : DEL, entity(d) = entity(p), d.v > p.v
dom(d, H) for DEL d    := ∃ d' ∈ H : DEL, entity(d') = entity(d), d'.v > d.v
dom(r, H) for ROSTER r := ∃ r' ∈ H : ROSTER, same ns, same signer,
                            r'.gen > r.gen ∧ r'.ceiling_t ≥ r.ceiling_t ∧ r'.epoch ≥ r.epoch
                            ∧ r'.del_ttl ≥ r.del_ttl
dom(g, H) for GRANT g  := ∃ g' ∈ H : GRANT, same ns, same issuer, same subject,
                            g'.cap ≥ g.cap ∧ g'.h > g.h
dom(x, H) for REVOKE   := false
F(H) := { x ∈ H | ¬ dom(x, H) }
```

Each kind carries its identity in one version. Each clause above implies
that the dominator's version is greater on the record's key:

| Kind | `v` | key on which `dom` compares | order on the key |
|---|---|---|---|
| PUT | `(t, author, seq, h)` | cell `(ns, ent, field)`; also a DEL of its entity | `v` |
| DEL | `(t, author, seq, h)` | entity `(ns, ent)` | `v` |
| ROSTER | `(ceiling_t, signer, gen, h)` | `(ns, signer)` | product of `gen` (strict), `ceiling_t`, `epoch` and `del_ttl` |
| GRANT | `(cap, subject, 0, h)` | `(ns, issuer, subject)` | product of `cap` and `h` |
| REVOKE | `(from_t, subject, rev_seq, h)` | none: never dominated | — |

The roster clause is a product order (D3). Suppose that the order put the
roster ceiling first. Then a stale roster with an old `gen` and a current
clock could evict the newer roster permanently. (A root restored from backup,
or a second device that holds the same root key, can make such a roster.)
This would roll back a member removal and the epoch. Under the product order,
neither roster dominates, and both stay until the root issues a new roster
above both.

The clause is strict in `gen` for the same reason. A restored root issues
`gen = 1 +` the largest `gen` that it holds, which can be the `gen` of the
roster that the live device issued after the backup. If `h` decided
between the two, the stale roster would evict the newer one, at every
replica, with probability one half, and it would roll back a removal and
the epoch. So at equal `gen` neither roster dominates. Both stay, the view
`ROSTER_FORK` reports the pair, and `ROSTER_eff` (which puts `epoch`
first) stays with the roster at the newer epoch. The root resolves the fork
by reconciling and then issuing a roster above both (§10.3).

The clause also never lowers the epoch: the roster that opens a new
segment is not evicted by a roster of the old segment, whatever its `gen`.
And it never lowers `del_ttl`: a roster with a shorter `del_ttl` does not
dominate its signer's roster with the longer one. A root that lowers its
own `del_ttl` therefore leaves two rosters in its slice, an antichain, and
`del_ttl_eff` (a maximum over held rosters) keeps the longer value until
that root is root-voided. So a stolen root cannot shorten tombstone life,
and neither can an honest root by a refresh.

The product order is a strict partial order that the version order extends,
and it is monotone. So T2, T2' and T3 hold exactly as for a total order.
Read the governing rule of §1 like this. Every kill predicate is a down-set
of a strict partial order on its key, and the record order extends that
partial order.

The fields of the lattice header that a kind does not use are zero. A roster
header also carries its `del_ttl` and its issuer (= signer). `REVOKE` and
`GRANT` headers carry their issuer (the signer). This is the **canonical**
header (D3). Decode produces only canonical headers, and the lattice accepts
no other headers.

A frontier holds at most one `GRANT` per `(issuer, subject)`. It holds a
per-signer *antichain* of rosters. An honest signer keeps this antichain at
one roster (§10.3), and a signer that misbehaves can make it larger only within
its capacity slice (§7). Every dominator stays in the same capacity row as
the record that it dominates. Data dominates only data. Only a record with
the same issuer dominates an authorization record.

`F(H)` is the **frontier**, and it is the state. `dom` is monotone in `H`
(T2) and *upward-closed*: a dominator of a dominator of `x` dominates `x`
(T2'). The convergence proof needs this lemma, and it holds for every kind
above. For this reason, `REVOKE` must not dominate. (A revocation that
dominates a writer's `PUT` would not dominate the records that this
`PUT` already dominated; see §6.) From T2 and T2':

```
F(H₁ ∪ H₂) = F(F(H₁) ∪ F(H₂))        (T3)
```

So a replica can drop a record immediately when it is dominated. This is
true on any subset of replicas and at any time, and no future frontier
changes. That one equation is all of the garbage collection (GC) design for
values. The values of a deleted entity are freed at each replica that a
`DEL` reaches, with no membership knowledge and no clock.

**Views** are pure functions of `F` (and of the collection's constant
`root_pk`):

```
deleted_at(ns, ent) := max { d.v | d ∈ F, DEL on (ns, ent) }            -- Option
cell(ns, ent, f)    := the unique PUT in F on (ns, ent, f)               -- Option
exists(ns, ent)     := ∃ f. cell(ns, ent, f) ≠ None
maxceil(F)          := max { r.ceiling_t | r ∈ F, ROSTER }   (0 if none)
W(F)                := { g.subject | g ∈ F, GRANT }                       -- admission
wcap(F, k)          := max { g.cap | g ∈ F, GRANT, g.subject = k }   (0 if none)  -- admission
root_void(k)        := k ≠ root_pk ∧ ∃ x ∈ F : REVOKE, x.subject = k, x.issuer = root_pk
W_eff(F)            := { g.subject | g ∈ F, GRANT, ¬ root_void(g.issuer) }  -- views
void(p)             := (∃ x ∈ F : REVOKE, x.subject = p.author, p.t ≥ x.from_t,
                          ¬ root_void(x.issuer))
                       ∨ p.author ∉ W_eff(F)
ROSTER_eff          := the maximal ROSTER r ∈ F with ¬ root_void(r.signer), ordered by
                       (epoch, gen, h), ties (impossible under A2) by (signer, ceiling_t, del_ttl)
                                                                                   -- Option
revoked(k)          := ∃ x ∈ F : REVOKE, x.subject = k, ¬ root_void(x.issuer)   -- any from_t;
                                                                                   -- the gate reads it
ROSTER_FORK         := ∃ r, r' ∈ F : ROSTER, r ≠ r', same signer, same gen        -- advisory flag
del_ttl_eff         := max { r.del_ttl | r ∈ F, ROSTER, ¬ root_void(r.signer) },
                       or Del_TTL_Default (180 days) if there is none
rivals(F)           := { r ∈ F : ROSTER | ¬ root_void(r.signer), r.gen = ROSTER_eff.gen,
                         r.signer ≠ ROSTER_eff.signer }         -- "membership contested", advisory
```

Two predicates read the local clock, so they are not functions of `F`.
They are per-replica advisory flags, and T5 does not list them:

```
far(p)              := p.t > now_local + slack
ceiling_lead        := maxceil(F) − now_local        -- a status when it passes a bound (§10.3)
```

`W` decides admission and `W_eff` decides views. The only difference between
them is the grants of root-voided issuers. Admission cannot drop these
grants, because admission must stay monotone (§4). So the keys that these
grants name stay admissible, and the store holds their records.
But each such record reads `void`, unless an issuer that is not root-voided
also granted its author.

`del_ttl_eff` is a maximum over rosters that domination never lowers in
`del_ttl`, so a root can make tombstone life longer but never shorter: not
the value that another root set, and not its own earlier value. A shorter
life is irreversible (expired tombstones are gone). The only way to undo a
longer life is to root-void the root that set it, and the recovery roster
then carries at least the previous `del_ttl_eff` (§6, §10.3).

There is no presence bit and no sentinel. An entity exists if and only if it
has a live field. A deleted entity is a `DEL` and nothing else. Because a
`DEL` dominates only the field versions below its own, an entity can be
*partial*: if A deletes entity `E` at `t = 1000` and B, offline, writes only
`E.phone` at `t = 1003`, then after the sync `exists(E)` holds and every
field except `phone` reads `None`. This is the lattice's answer, and it is
the same at every replica. An application that needs whole entities checks
its required fields when it reads, and either deletes the remainder again
or fills it in; or it uses a typed `MVREG` cell (C10) where it needs the
concurrent write to be visible (§10.4).

`maxceil`, `W` and `wcap` lose nothing to domination. A roster leaves `F`
only under a roster of the same signer with a ceiling and a `del_ttl` at
least equal to its own. A `GRANT` leaves `F` only under a `GRANT` of the
same issuer and subject with a cap at least equal to its own. With T2',
each dominated record has a dominator that is not dominated. Thus
`maxceil(F(H)) = maxceil(H)`, `W(F(H)) = W(H)`, `wcap(F(H), k) = wcap(H,
k)`, `W_eff(F(H)) = W_eff(H)` and `del_ttl_eff(F(H)) = del_ttl_eff(H)`. The
frontier's registers are the registers of all records ever applied, and
they never shrink (T4').

Also, `ROSTER_eff(F(H)) = ROSTER_eff(H)`, because a roster that dominates
another roster has the same signer, an epoch at least as high and a
strictly greater `gen`, so it is greater in `(epoch, gen, h)`. `ROSTER_eff` is
present when `F` holds a roster that the founding key signed. The
collection's first roster is such a roster.

## 4. Admission

Kome admits every well-formed authorization record (`ROSTER`, `REVOKE`,
`GRANT`). Kome admits a `PUT` or `DEL` if and only if `t ≤ maxceil(F)`,
`author ∈ W(F)` and `t ≤ wcap(F, author)`. The three registers are the
derived views of §3. They are functions of the frontier, not separate
state. They only grow, because admission of authorization records is
unconditional and their domination never lowers any register (§3).

The write cap bounds what a revoked key can still do. Without it, any
current member (a compromised read-only member, a relay) could carry the
records of a revoked key to every replica for ever, at `t = maxceil`, and
A7 could not be a deployment duty. With it, a key that a certified root
granted writes at most up to that root's cap, which the founding key keeps
short (§2, §10.3); and a key that the founding key granted is capped only by
`maxceil`. A `GRANT` by a root with a longer cap raises the subject's
`wcap`, and nothing lowers it (T4'). The cap is a function of the bytes of
the `GRANT` (its signer block), so admission still depends only on bytes
(D1).

`W` sets a limit on who can occupy the store. Without `W`, a member could
relay records under keys that it generates and that no `GRANT` names. Then
a cell's state would have no bound, and typed fields (below) would have
no per-cell bound. There is no removal from `W`. To remove a writer, use
`REVOKE` (§6). Neither `REVOKE` nor root-voiding ever changes admission.

An admission rule that lets a later record withdraw an admission is not
monotone. Replicas that saw the two records in different orders would then
hold different frontiers forever. (The design also rejects the variant that
drops the withdrawn records, E7.) The transport gate keeps a revoked key's later
records out, under assumption A7 (§6, §9).

A gate of the form "inadmissible under the currently maximal roster" would
fail when two rosters have equal generation. Instead, this rule is
**monotone in the held history**. When a record is admissible at a replica,
it stays admissible. A record that is inadmissible at one replica becomes
admissible there when the authorization record that made it admissible
elsewhere arrives. Kome **discards** inadmissible records and does not hold
them.

A peer that holds a discarded record offers it again on the next
reconciliation. (For exactly this reason, T4 has an exchange form.) The
ceiling keeps the top of the version order unreachable. No admissible record
can pin a cell above `maxceil`, and each roster refresh moves `maxceil` up.

A replica's state is only `F`. Its join is `F(F₁ ∪ F₂)`, and Kome admits
the data records again under the joined authorization records. Within each
batch of records that arrive together (a reply group, a bundle, an import),
Kome applies every record with kind < 3 (`ROSTER`, `REVOKE`, `GRANT`)
before any record with kind ≥ 3 (`DEL`, `PUT`); the order inside each part
is free (D14). That is the authorization-first pass of T4 (a)
(`auth_first`). So Kome never discards a data record that arrives in the
same batch as the grant that admits it. In a session, the phase gate (§8)
gives this order on its own.

An implementation can cache `maxceil` and `W` (`Kome.Registers`). The cache
must be equal to the views of §3 on every state. This is an invariant, not a
second source of truth.

**Registers are derived, not reconciled.** If Kome stored registers, the
replicas would have to join them. Register values on the wire without
authentication would let any peer raise `maxceil` or add a writer. Also, a
roster dominated on arrival would raise registers that the log never
recorded. Write access is in `GRANT` records, and the ceiling is in the
roster's version (D1′). So nothing outside `F` needs reconciliation
or persistence. Reconciliation of the authorization records reconciles the
registers (§8), and replay of the log replays them (§7).

Root authority is a certificate, and Kome checks it on bytes (§2).

**Typed fields (extension, C10).** If an application needs counters,
grow-only sets or multi-value registers in the engine, these changes apply:

- A `PUT` can carry `ftype : u8 ∈ {LWW, GSET, PNCOUNTER, MVREG, MAXREG}` as
  part of the cell key.
- The `PUT`'s value is the author's full state for that field.
- For a typed cell, the `PUT`-over-`PUT` clause of `dom` becomes: `q` kills
  `p` only when `q` and `p` have the same author, `q.v > p.v` and `state(q)
  ⊒ state(p)` in the type's join order. The state comparison is a
  down-set on the cell key, so the governing rule holds. An author whose
  state is not inflationary (a device restored from a backup emits `{a, c}`
  after `{a, b}`) then leaves an *antichain* of its own records in the
  cell, which the view joins; nothing is lost. The antichain counts
  against the data capacity, record by record.
- An honest author emits, as its next state, the join of every record of
  its own that it holds on the cell. Then its antichain has one record.
  This is the obligation behind T15–T17, and the antichain is the checked
  fallback when it fails.
- A `DEL` of the entity dominates every typed cell of the entity exactly as
  it dominates LWW cells: the per-author records with versions below the
  `DEL` leave. A typed cell has no per-author tombstone.

Then the frontier holds, per `(cell, author)`, one record from an honest
author, and `|W|` sets the limit. The cell's value is a join over the
per-author records that survive and are not void. LWW cells do not change.
The extension needs `W`, a saturating fold, and a cursor to read the view
output. It is not on the critical path. Today, an application can get the
same semantics with one LWW sub-cell per device.

## 5. Clocks and writing

There is no engine clock, no `tick` and no `receive`. Kome adopts nothing
from a peer. So a far-future record of one collection can never carry into
another collection on the device.

```
floor(cell)  := max(cell(ns,ent,f).v, deleted_at(ns,ent))     -- for DEL: max over all fields and deleted_at;
                                                              -- the zero version when the cell has no record
ceil         := min(maxceil, wcap(self))                      -- one writer's ceiling (§4)
floor_t      := max(floor.t, mark)                            -- mark is the store's expire mark (§7)
low          := maxceil − Cap_Lead for a DEL (0 if maxceil < Cap_Lead), and 0 for a PUT
u            := max(now_ms, low, floor_t + 1)
t_emit       := min(u, ceil)
clamped      := t_emit < max(now_ms, floor_t + 1)             -- out flag: the ceiling held the write back
born_expired := DEL ∧ t_emit + del_ttl_eff ≤ now_ms           -- out flag
seq_emit     := seq_self(ns) + 1, and above every seq of this device's records held in F(ns);
                at 2^48 − 1 the write fails SEQ_EXHAUSTED, no record is produced
v_emit       := (t_emit, self_pk, seq_emit, h)
status       := SHADOWED if floor exists ∧ v_emit < floor   (only when t_emit = ceil) else OK
```

**The write path has three steps (D8).** `h` hashes content that contains
`t` and `seq`, so `h` cannot be an input to the step that selects them:

1. *Choose* `(t_emit, seq_emit, status)` and the flags `CLONE_SUSPECTED`,
   `CLAMPED` and `BORN_EXPIRED` from the frontier, the target cell,
   `now_ms`, the device key and `seq_self(ns)`. This step does not use `h`.
   The target is built by `Put_Target(ns, ent, field)` or `Del_Target(ns,
   ent)`, which compute the field hash themselves; a caller cannot name a
   cell that the built record does not have, so the cell that *Choose*
   looks at is the cell that *Build* writes.
2. *Build* the `PUT` or `DEL` content with that `(t, seq)`, and hash it.
3. *Sign* and apply. Persist `seq_self(ns) := seq_emit` durably right
   after *Choose* and before the `APPLY` is appended; send the frame only
   after its `APPLY` is durable (A5). `Kome.Write` is this path:
   `Prepare` (*Choose*, *Build*, *Sign*; it changes nothing and returns
   the frame and the `seq_self` to persist), then the binding persists
   `seq_self`, then `Commit` (`Store.Put_Frame`). On open,
   `seq_self(ns) := max(stored, the largest seq of this device's records
   held in F(ns))`. A seq store that cannot be read is reported as
   `SEQ_CORRUPT`, apart from `SEQ_EXHAUSTED`, and the path starts from
   the held records alone. Neither step refuses a large jump of `seq`:
   own records leave `F` when they are dominated.

`CLAMPED` means that the ceiling `min(maxceil, wcap)` held the write
back: `t_emit` is below the clock, or not above the cell's floor (the
expire mark included). The write was back-dated to the ceiling, and it
loses against any concurrent write at the ceiling by a higher key. The
floor term always exists: a cell with no record has the zero version, so
a write with `now_ms = 0` and no floor gets `t_emit = 1`. `BORN_EXPIRED` means that a `DEL` would be
expired already at a replica whose horizon follows a fresh `maxceil` (a
device that was offline for longer than `del_ttl_eff` under a stale
ceiling). Such a `DEL` is applied at those replicas for its effect and not
held, so a stale copy of the entity can come back. The caller syncs first
(so that a fresh roster lifts `maxceil`) and then writes the `DEL`. For the
same reason, the roster refresh of A3 must reach every partition of the
members, not only the partition that holds the root device.

The result of step 1 does not depend on `h`. `seq_emit` is larger than the
`seq` of each held record of this device. So `(t_emit, self_pk, seq_emit)`
is different from the prefix of each held version. Two versions with
different `(t, author, seq)` prefixes compare by the prefix alone.

Thus, for each `h`, Kome admits the record of step 2. `OK` means that no
held record dominates it. `SHADOWED` is true if and only if a held record of
the floor has a greater prefix. (The lemma `Lemma_Outcome_Independent_Of_H`
states this.) The apply step holds an `OK` write unless the store is full
(`NO_SPACE`, §7).

A write *chases* the cell's floor, so read-your-writes holds (T8)
unless the cell is pinned at the ceiling. A device with no real-time clock
works: all its writes chase, and it expires tombstones with `Expire(now :=
maxceil(F))` (§7). `seq_self(ns)` is the only persisted clock state.

`seq_self(ns)` is **per collection**. The device keeps it per
`(device key, ns)` next to that collection's store. So if a thief forces
a jump to `2^48 − 1` in one collection, only that key's counter in that
collection is exhausted. `SEQ_EXHAUSTED` is a clone alarm. The
device moves to a fresh key in that collection (a new `GRANT` and roster),
and a root revokes the old key.

**What a writer that misbehaves can do (H8).**

| Case | Effect | Bound |
|---|---|---|
| Clock ahead by δ | It wins concurrent conflicts on the cells that it writes, for δ. Those cells then resolve by chase (arrival order), not by wall time. Every later write to such a cell, by any writer, chases above the pinned `t` (C5): the adoption is per cell, and a `DEL` of the entity lives δ longer (§7, chased tombstones) | δ ≤ maxceil − now; only cells it touched; automatic |
| Clock behind | It loses concurrent conflicts; its own cells still chase. Under a stale `maxceil` (a long time offline), the clamp back-dates its writes to the ceiling, and a `DEL` can be born expired; `Choose` reports `CLAMPED` and `BORN_EXPIRED`, and the caller syncs before it writes such a `DEL` | its cells only; a corrected clock has an effect immediately |
| Backup restore | It emits old `seq` values again: equivocation, ordered by `h`, flagged. Peers offer the old records again, and they are dominated unless the `DEL` has expired (§7) | The writer detects it (it holds its own record with `seq ≥ seq_self + 1`). `seq` jumps past it. The write succeeds and reports the flag `CLONE_SUSPECTED` |
| Cloned key | Continuous equivocation; replicas still agree | flagged; the owner issues `REVOKE(old, 0)`, a `GRANT` for a fresh key and a roster |
| Malicious | It can overwrite or delete any cell (that is what write access means). It can pin cells to `min(maxceil, wcap)`, flood entities, and grind a public key that wins ties at the ceiling. It can force its own `seq` to `2^48 − 1` in the collections where it writes | It cannot forge, and it cannot go above `maxceil` or above its `wcap`. A flood cannot block the `REVOKE` while the binding keeps `Log_Fits` and the founding key keeps its reserve (§7, E1). Under A7: nothing that the key signs after the `REVOKE` reaches any replica. So pins stop at the first roster whose ceiling exceeds the pinned `t` (not at "the next refresh": a refresh below the pin changes nothing). A flood of `DEL`s on random entities holds data capacity until it expires: the owner's purge `DEL`s are `SHADOWED` or free one record each, and the room comes back only when `min(now, maxceil) ≥ t_flood + del_ttl_eff` (§10.5). The purge is entity-grained (§6): junk fields on an honest entity are overwritten with empty `PUT`s, not deleted with the entity. Without A7: a replica that admits the key to a session, or takes its bundle, or relays what another member carried, spreads the key's later records everywhere. Each replica admits them (within `wcap`) and flags them `void`. The bytes that they overwrite or delete leave `F` at every replica, and Kome keeps no copy |
| Compromised current member (a relay, a read-only member) | It can carry the records of a revoked or root-voided key to every replica, whatever those replicas hold, because admission reads neither `REVOKE` nor `root_void` (E7) and `W` never shrinks | Each such record is admitted only within `wcap(author)` and reads `void`. The transport attributes it: when a record arrives whose author is already void in the receiver's view, it records the delivering peer's `dh_pk` and flags that peer `SUSPECT_RELAY` (§8). The owner removes the relay. This is the A7 duty stated for a member, not for a stale replica |
| Root restored from backup | It issues a roster with an old or an equal `gen`. If its own held roster has a strictly greater `gen`, an epoch at least as high and a ceiling at least as high, the restored roster is dominated on arrival (status `DOMINATED`). If not (an equal `gen`, a current clock, or an older epoch), neither roster dominates, Kome holds both, `ROSTER_FORK` reports the pair, and `ROSTER_eff` is the roster at the newer epoch (then the greater `gen`, then `h`). `h` never evicts a roster of the same signer. After sync, the root issues a new roster above both. `maxceil` never decreases, and no `REVOKE` is lost | It converges in both cases; a stale roster never becomes effective while the newer one is held, and a removal (which raises the epoch) is never undone |

`CLONE_SUSPECTED` is a flag that Kome reports next to the write's
status. It is not a status: the write occurred. It is also raised on the
apply side (H18): a record signed by the device's own key that arrives
from a peer and changes `F` (not a duplicate, not dominated, not an
expired `DEL`) sets it, and so does `F` holding two of the device's own
records with equal `seq` and different `h`. A clone that writes at the
owner's pace is flagged this way. With A5 (a frame leaves only after its
`APPLY` is durable), a crash never makes the device's own lost frame come
back from a peer, so the apply-side flag raises no false alarm.

This is the honest statement of the residual risk: **LWW cannot undo the
effect of a wall clock that was ahead**. If a writer pushed a cell's floor
far ahead, the cell resolves by chase until wall time passes that
floor. The ceiling sets a limit on how far; it does not prevent it. A thief
can overwrite records before the revocation reaches a replica. These
overwrites stay, flagged `void`, and the bytes that they replaced leave
every replica; Kome keeps no copy. This is acceptable, because each such
act is signed and bounded, and it is attributable as long as the record is
held: a back-dated `DEL` that every replica applies and expires on arrival
(§7 step 4) destroys the entity and leaves no held record of the act. It
stops at the revocation and at the first roster whose ceiling exceeds what
the thief pinned.

It stops at each replica when that replica holds the revocation. It stops
everywhere only if no stale replica accepts the key's later records
first. This is assumption A7 (§9). Offline-first operation makes stale
replicas normal, so A7 is a deployment duty. Revoke promptly. After a
revocation, sync each device before it talks to anything else.

## 6. Authorization, encryption, revocation

**Roots (C9, D1).** A collection has one founding key (`root_pk`, from which
Kome derives `ns`). It has at most 15 distinct certified signer keys during
its life (`Signers_Max` = 16 signers in total); renewals of a key's cap are
unlimited and take no slot. Any root, founding or certified, can
sign `ROSTER`, `REVOKE` and `GRANT`. Only the founding key certifies a root
(§2). A record's bytes tell if its signer is a root, so admission of
authorization records needs no history. A replica that joins late can
never refuse a `REVOKE` that every other replica holds. Also, a roster never
waits for the roster that introduced its signer.

Roster domination is per signer (§3). The effective roster is the view
`ROSTER_eff` (§3): the `(epoch, gen, h)`-maximum over the frontier rosters
whose signer is not `root_void`. Epoch comes first, so a removal (which
raises the epoch) is never undone by a concurrent roster that still lists
the member, and the founding roster that opens a segment beats every roster
of the old segment whatever its `gen`. If two roots race at one epoch with
equal generations, `h` resolves the race, and the loser's newcomer is shut
out until a root repairs it: the view `rivals(F)` (§3) reports the losing
rosters as "membership contested", and a root that sees rivals at
`ROSTER_eff.epoch` issues `gen + 1` with the union of the members (§10.3).
Two rosters of *one* signer at equal `gen` are a fork (a backup restore or
a second device): both stay, `ROSTER_FORK` reports them, and the newer
epoch is effective. `REVOKE`s are grow-only, so no race can lose one.

A losing roster still carries boxes. Two rosters at one epoch wrap the same
`k_e`, so a member that only the loser lists holds the key of the epoch,
and it can read every bundle of that epoch although it fails the gate. So
a root **re-keys on divergence**: when it holds a roster `r'` of another
signer that is not root-voided, with `r'.epoch = ROSTER_eff.epoch`, and
`r'` lists a `(sign_pk, dh_pk)` that `ROSTER_eff` does not list, it issues
its next roster at `ROSTER_eff.epoch + 1`. From then on, no key that
`ROSTER_eff` does not list can derive the bundle key in use (T14).
Per-field writer sets are not part of the design. If admission enforces
them, they are not monotone. If they are a view flag, they are only a label.
A label cannot stop an unauthorized write that frees the bytes of an
authorized value.

**Root revocation (D2).** Only the founding key root-voids. `root_void(k)`
is true if and only if `F` holds a `REVOKE` of `k` *that the founding key
issued*. Kome ignores the `from_t` of this `REVOKE`, because records that a
root issues carry no trustworthy time and a thief would backdate them. The
founding key is never `root_void` (a `REVOKE` of `root_pk` is malformed). A
`REVOKE` that a certified root issues and that names another root voids only
that key's data records.

The certificate of a root-voided root stays valid. So the root can continue
to sign well-formed records, and admission (which must stay monotone) still
takes them. Root-voiding changes every view. All that the root issued,
before or after, no longer counts:

- Its rosters leave `ROSTER_eff` and `del_ttl_eff`.
- Its `REVOKE`s void nothing (members that it revoked wrongly are no longer
  void).
- Its `GRANT`s leave `W_eff`. So each record whose author only this root
  granted reads `void`. This includes each key that the root makes
  afterwards.

The cost is this: honest revocations and grants from a root that is root-voided
later also no longer count. The recovery procedure issues again the ones
to keep. `void`, `W_eff` and `ROSTER_eff` are views, and they never feed
admission. `root_void` is monotone in `F`. For a fixed `root_void` set, the
`REVOKE` clause of `void` and `W_eff` are monotone in `F` (T12).

**Recovery from a stolen or lost certified root `R`.** The founding key
reconciles first (so that it holds `R`'s records), and then does these
steps together, in this order. The re-issues come *before* the root-void,
so that a replica which receives the records in issue order never reads
`R`'s honest grants and revocations as gone:

1. It issues its own `GRANT` for each key that `R` granted and that the owner
   wants to keep as a writer. (If not, those keys read `void` after step 4.)
2. It issues `REVOKE(k, 0)` for every member `sign_pk` that the stolen device
   holds (the device's own member entry, and any member that `R` added and
   that the owner does not confirm). With the `REVOKE`-aware gate, these
   devices then pass no gate anywhere, as soon as the `REVOKE` arrives.
3. It signs again each member revocation of `R` that it wants to keep. For
   a lost key, `from_t` is `maxceil(F) + 1` at issue time (below, E4).
4. It issues `REVOKE(R, 0)`.
5. It issues a founding-signed roster that opens a new epoch segment
   (below). The roster leaves out every entry revoked in step 2, and keeps
   only the entries that the owner re-confirms. Its `ceiling_t` is
   `max(intended, maxceil(F) + 1)`: the founding key is uncapped, so it can
   lift `maxceil` above the largest cap that `R` ever used. Then every cell
   that `R`'s grantees pinned at that cap is writable again at once, instead
   of when wall time passes it. Its `del_ttl` is at least the `del_ttl_eff`
   of the state before the ceremony, with `R`'s rosters still counted:
   otherwise the root-void would shorten tombstone life (a value that only
   `R` had set stops counting), and members that sync rarely would bring
   deleted data back. It gives the new top to the other roots out of band.

`Kome.Roster` issues the steps in this order and checks steps 2, 3 and 5:
after recovery, no `ROSTER_eff` member has a `sign_pk` with a counting
`REVOKE`, `ROSTER_eff.ceiling_t > maxceil` of the state before it, and
`del_ttl_eff` did not fall. The founding key's slice holds these records
within its reserve (§10.3), so step 4 always fits. Keys that `R` granted
and that the owner does not recognize need no action. `W_eff` voids them,
and also each key that `R` makes later. The root revocation reaches
captured replicas through `OPEN` (below), and the quarantine flag holds
them until the recovery roster arrives.

The order holds for the founding device's own sessions and bundles. It
does not hold for `OPEN`: an `OPEN` carries root-voids only, from any
member that holds them, to a replica that may hold none of steps 1, 3 and
5. At such a replica there is a **transient**: until the re-issued records
arrive, the keepers that only `R` granted read `void`, and the members
that only `R` revoked read clean and pass the gate again. Each view takes
either its pre-recovery or its post-recovery value, never a third one,
because `root_void` is monotone and the re-issues are founding-signed
records that every replica admits. The transient ends at the replica's
next member session (the authorization range is reconciled first, D13).
A non-member that holds `REVOKE(R, 0)` can start this transient at a
stale replica, and this is the whole of what it can do with the frame
(§8, `OPEN`).

**What a stolen certified root can do.** Until a replica holds its root
revocation, the stolen root can do there all that a root does:

- It can grant writers, who can overwrite or delete any data.
- It can make its roster `ROSTER_eff` (with `gen` up to its cap, §2 rule 2,
  at the epochs of the segment whose top it holds). Then it decides who
  passes the session gate and which epoch bundles use, and it can lock
  honest members out, until a founding roster at a later epoch arrives.
- It can revoke members (flag them `void`).
- It can raise `maxceil` up to its effective cap.
- It can make `del_ttl_eff` longer.

After the founding key root-voids it, none of that counts in the views of a
replica that holds the root revocation. Under A7, nothing that
it or its grantees sign afterwards reaches that replica. The reason is that
no roster of this root counts for the gate, and no epoch of this root is
accepted for bundles. These effects stay permanently:

- `maxceil`, raised up to the largest cap ever certified for it.
- Its records in its own capacity slice.
- If it overflowed its slice, the replicas' disagreement about its surplus
  records (§7).
- Without A7, the records that it or its grantees signed after the
  revocation and that a stale replica accepted. Every replica then holds
  these records, flagged `void`, and the bytes that they overwrote or
  deleted are lost.

A stolen founding key violates A1. The only remedy is to re-found the
collection.

**Loss of the founding device** (without theft of the key) is survivable
while a certified root remains. That root continues to issue rosters and
grants. But this is true only until wall time passes the largest
`cert_cap` in force. `maxceil` cannot go above that cap, so writes then
degrade to ties at the ceiling, and tombstone expiry freezes with them
(A3). Also, nobody can add or root-void a root, and nobody opens a new
segment, until the key is restored from its offline backup: the epoch
can advance only to the top of the current segment, and a member removal
needs an epoch. This is why the founding key stays cold, with an offline
backup.

**Membership is key possession.** The `ROSTER` wraps the current epoch key
to each member's `dh_pk`. Epoch keys make a hash chain within a *segment*:
`k_e = f(k_{e+1}, "kome/prev")`, where `f(k, m)` is keyed BLAKE2b-256
(`crypto_blake2b_keyed`) with key `k` over the message `m`. The bundle key
is the same PRF under the epoch key, `k_b = f(k_e, "kome/bundle" ‖ ns)`
(§8). One PRF assumption on keyed BLAKE2b then gives T14: a removed member
holds `k_e`, which is an *output* of the PRF under `k_{e+1}`, and nothing
about `k_{e+1}` itself. A member that holds `k_e` derives each older key of
the segment. So a new member needs one box, and a removed member that
holds `k_e` cannot derive `k_{e+1}`. 2^16 epochs are sufficient for the
life of any collection.

The member's `dh_sk` is the member's whole capability: it opens the boxes
and it is the Noise static key. There is no key update inside a segment
and no post-compromise security: an attacker who copies a member's
`dh_sk` once opens that member's box in every later roster that lists it,
for as long as it stays listed, and nothing in the chain can show it. A
member therefore rotates its `dh_pk` from time to time (it proposes a
fresh key, and the next roster lists it; a removal of the old key raises
the epoch), and the roots re-key members on a schedule (§10.3). T14 states
the premise.

**Epoch segments and several roots (E3).** There is one chain per
collection. The roots that are not `root_void` share it. Segment boundaries
are fixed: segment `j` covers the epochs `[4 096·j, 4 096·j + 4 095]`, so
a segment starts at `s = 4 096·j` and its top is `top_s = s + 4 095`
(`Kome.Epochs.Segment_Start`, `Segment_Top`; 16 segments cover the 2^16
epochs). The founding key draws a fresh random top key for each segment.
The roots receive the top of the current segment out of band (at
certification, and at each new segment). Within a segment, each epoch key
is a function of the top. So two roots that issue rosters at the same epoch
use the same key and never conflict. A root never issues a roster with an
epoch above `top_s`, and a certified root that holds a founding roster at an
epoch above the segment that it knows refuses to issue until it has the new
top.

**Only the founding key opens a segment.** It opens a segment when it
root-voids a root, or when the chain reaches the top of the current segment.
It uses a founding-signed roster at epoch `s' = top_s + 1`, the start of the
next segment. It knows `top_s`, so it needs no fresh `F` for this: a
founding device that is behind on `F` still opens the right segment. Under
the `(epoch, gen, h)` order, this roster beats every roster of the old
segment whatever their `gen`, including the rosters of the root that it
voids. (Kome ignores the epochs of a root-voided root in every view, and a
thief cannot use up the epoch space: it can only write epochs of the
segment whose top it holds.) A root-voided root never sees the new top, so
it cannot derive any later key.

Every root of a segment holds its top, and the top gives every key of the
segment and, through the links, all history. So a leak of a root's
storage (a backup of a certified root's device) leaks the segment without
any theft of a signing key. The remedy is the **top-leaked procedure**: the
founding key opens a new segment, with a fresh top, and issues no
`REVOKE`. The same procedure serves when the owner wants a fresh top for
any other reason. T14 counts the roots of a segment among the holders of
its keys.

Each roster carries `links[]` (at most 15, cumulative over the collection's
life). Link `{from_epoch = s, nonce, box}` seals `k_{s−1}`, the last
key of the previous segment. The seal uses a key derived from `k_s`, the
first key of the segment that follows it. A holder of any key of the current
segment walks down to the start of the segment, opens the link, and
continues down. So a new member can still read all history. Each roster
carries the full link list, so history survives when old rosters are
dominated.

A seventeenth segment would need a sixteenth link, and the epoch space ends
at 65 535. At either bound, the owner must re-found the collection.

**Boxes (D5, D6).** Each roster carries `box_pk`. This is the X25519 public
key of the roster's box secret

```
eph_sk = BLAKE2b-256("kome/eph" ‖ k_e ‖ ns ‖ u16(e) ‖ signer ‖ u48(gen))
```

which `Kome.Epochs` computes from the epoch key inside the sealing
operation; no caller draws it, so a weak RNG (a VM snapshot, early boot, a
WASM shim) cannot reveal it. Anyone who holds `k_e` can recompute it, and
such a party holds the boxed key already. `Kome.Roster.Build` takes the
epoch key, the signer, `gen` and the members, computes `box_pk` and seals
the boxes from the same secret, and wipes it; `Make_Roster` is private to
it, so a roster's `box_pk` and boxes cannot disagree. No root has a
long-term X25519 key, and no key is used both to sign and to exchange. For
member `(sign_pk, dh_pk)` of a roster of collection `ns` at epoch `e`:

```
wrap_key = BLAKE2b-256("kome/wrap" ‖ X25519(eph_sk, dh_pk) ‖ box_pk ‖ dh_pk ‖ sign_pk ‖ ns ‖ u16(e))
nonce    = BLAKE2b-256("kome/nonce" ‖ wrap_key ‖ k_e)[0:24]
box      = XChaCha20-Poly1305(wrap_key, nonce, AD = ns ‖ u16(e), k_e)        -- cipher[32] ‖ tag[16]
```

The member calculates `X25519(dh_sk, box_pk)` and opens the box. Then it
calculates the nonce again from the opened key and refuses a mismatch. So
there is exactly one valid box per `(wrap_key, k_e)`. A link uses the same
construction with `link_key = BLAKE2b-256("kome/link" ‖ k_s ‖ ns ‖ u16(s))`,
`nonce = BLAKE2b-256("kome/nonce" ‖ link_key ‖ k_{s−1})[0:24]` and
`AD = ns ‖ u16(s)`, and it seals `k_{s−1}`.

Three layers keep keystreams apart:

- A fresh `box_pk` makes each wrap key single-use.
- Each wrap key binds `ns`, the epoch and the two member keys. So wrap
  keys are different, even if a `box_pk` is used again (a restored device,
  a bug).
- With the synthetic nonce, a repeated `(key, nonce)` implies a repeated
  plaintext. This shows only that the same key was wrapped again.

The only randomness is the segment tops, which the founding device draws
in its ceremony (`Kome.Roster`, §10.3). SPARK code reads no RNG. The
construction is deterministic, and known-answer vectors test it. Decode
refuses low-order and non-reduced peer keys (§2), and the box code refuses
them again. An all-zero `eph_sk`, seed or top is refused as an input
(`X25519_Public(0^32)` and `Derive_Public(0^32)` are public knowledge, and
a key derived from them protects nothing).

**Two gates on transport, none on records.** Kome admits a peer to a session
for `ns` if and only if its Noise static key is the `dh_pk` of a member of
`ROSTER_eff` whose `sign_pk` is not `revoked` (§3: a held `REVOKE` of that
key, with any `from_t`, from an issuer that is not `root_void`). So a
revocation closes the gate at once, before the roster that removes the
member arrives and wins `ROSTER_eff`; the removal roster is still needed
for the epoch. The same test applies to a `HELLO` credential (the peer's
member entry) and to the boxes a roster seals (`Kome.Roster` seals no box
for a revoked member). `Kome.Guard.Gate` is this test, and the session
carries it as a contract: `Reconcile.Start` takes the peer's Noise key,
`Receive` of a `HELLO` refuses a credential that does not list that key,
and `Admit` has the gate as its precondition. The gate is not evaluated
once: the store keeps a monotone `Auth_Gen` that goes up with every
applied `ROSTER`, `REVOKE` or `GRANT`, the session records it at `Admit`
as `Gate_Gen`, and `Receive` and `Next_Phase` evaluate the gate again
whenever `Auth_Gen ≠ Gate_Gen` and abort the session when it fails. So a
revocation that the owner issues during a session ends that session at the
next message. At most `Members_Max` = 64 devices pass the gate of a
collection, because the gate is membership of one roster (§7, Bounds).
Before each side evaluates the gate, it applies what the peer sent before
the gate. The `OPEN` message carries the founding-issued `REVOKE`s of the
roots that are root-voided in the sender's `F` (signed records,
admissible everywhere). So one honest contact releases a replica whose
`ROSTER_eff` a root-voided thief took over (D13), whether or not the honest
sender ever held a record of that thief.

**Quarantine after a pre-gate root-void.** An `OPEN` carries only `REVOKE`s,
never the recovery roster that the founding key issues with them. If an
`OPEN` root-voids the signer of the receiver's current `ROSTER_eff`,
`ROSTER_eff` falls back to an older roster, which can list members that the
voided root had removed. So the receiver keeps a store-local flag outside
`F` (`Kome.Guard`): it is set when a pre-gate `OPEN` root-voids the signer
of `ROSTER_eff`, and it clears only when a founding-signed roster is applied
and is `ROSTER_eff`. While it is set, the replica admits a peer only through
a `HELLO` whose credential is such a roster (so the credential itself clears
the flag), takes no sealed bundle and seals none. The flag is not "gen or
epoch non-regression": a thief can set `gen` or the epoch to the largest
value, and no recovery roster could exceed it. A founding roster is
`ROSTER_eff` as soon as it beats every roster of a signer that is not
root-voided, whatever the voided root wrote. The flag depends on the order
of arrival, which `F` does not record, so it lives outside `F`.

The credential `HELLO` follows. A side sends its own `HELLO` only after it
has admitted the peer, so a non-member learns no membership list. The
credential is a roster in the sender's `F` that lists the sender's Noise
key. The receiver refuses any other credential. Before it verifies the
credential, the receiver drops it and aborts the session if its `F` holds a
founding `REVOKE` of the credential's signer (the same lookup that `OPEN`
uses): a root-voided root could otherwise fill its own slice at the
receiver with one fresh roster per session, although it is refused every
time. The receiver applies the credential and evaluates the gate again. So
a newly added member can still reach a replica whose rosters are stale
(§8).

**Joining.** A new device has no `F`, so it has no `ROSTER_eff` and admits
nobody. The join hand-off is `(root_pk, salt, frame of the roster that
lists the newcomer)`, delivered out of band with the device's enrollment
(§10.3). The newcomer opens its store with `root_pk` and `salt` and applies
the roster frame: a founding-signed or root-signed roster applies to an
empty store like any other authorization record. That roster is the
newcomer's freshness anchor. While `F` holds no non-root-voided roster
that lists the device's own `dh_pk`, the device accepts as a credential
only a roster that lists both the peer's Noise key and its own `dh_pk`,
refuses any other credential, and lets no other credential change
`ROSTER_eff`. So a removed member that reaches the newcomer first with an
old roster that lists the removed member and not the newcomer cannot
capture it, and the newcomer's first `ROSTER_eff` is at least as new as
the roster that added it.

A replica can read a sealed bundle (mailbox, broadcast, BLE) if and only if
it holds the bundle's epoch key. Kome accepts bundles **only under
`ROSTER_eff.epoch`**. (If Kome accepted the previous epoch, a removed member
could write into up-to-date replicas for a full epoch.) So a captured
replica takes no bundle from honest members until an interactive session
releases it. The key in use is `bundle_key(F)`: the key that the device's
own member entry of `ROSTER_eff` unboxes, computed again whenever
`ROSTER_eff` changes. An epoch number is not a key identifier: a stolen
root can box any key under any epoch of its segment before it is
root-voided, so a device never caches a key by epoch number, and sealer
and opener both use `bundle_key(F)`. The two gates decide who you talk
to, never what a record means.

A replica that syncs only through store-and-forward must still cross an
epoch change: the roster that raises the epoch travels in bundles under
the new key, which the replica cannot open yet. So there is a **sender
rule**, with no receiver change: for a set period after its
`ROSTER_eff.epoch` rises from `e` to `e'`, a replica also sends an
authorization-only bundle under `k_e`, which carries the new roster and
the `REVOKE`s before it. These records are signed and admitted everywhere,
and they carry no data, so a removed member that still holds `k_e` gets no
write path from them: it learns that it was removed. A replica that holds
`k_e` and gets that bundle reaches `ROSTER_eff.epoch = e'` and opens the
rest.

**Revocation** is `REVOKE(X, from_t)`: grow-only, never dominated,
root-signed. Its effect is the view flag `void` on the records of `X` with
`t ≥ from_t` (while its issuer is not `root_void`). The roster that follows
it adds a fresh epoch and removes `X`. A revocation is intentionally *not* a
prune, and it does not change admission. The reason is as follows. Suppose
that a revocation dropped the records of `X` from `F`, and that a record `p'`
of `X` already dominated (and freed) an honest `p`. Then `p'` would
disappear on one replica and leave the cell empty, but a replica that saw
the revocation first would still hold `p`. The records are the same, but the
frontiers are different.

Retroactive removal needs history, and a frontier has none, so `void`
hides and flags. An honest writer's next write chases above the voided
record. The cost: a revoked writer's garbage stays in `F` as void
records until the owner removes it. The purge is **entity-grained**, like
`DEL` itself: an app-level "purge revoked writer" routine `DEL`s the
entities that the writer created, and the tombstones then expire. For
junk fields that the writer put on an *honest* entity, the routine does
not `DEL` the entity (that would free every honest field of it at every
replica, and the purger could re-`PUT` only what it holds, under its own
authorship); it overwrites each junk cell with an empty `PUT`, which
chases above the void record and costs one cell (§10.5). Revocation does
not remove `X` from `W`, and it never needs to: `W` only admits, and
`void` judges.

A `REVOKE` is never dominated, so each one costs its issuer a slice entry
for the life of the collection. An issuer therefore emits `REVOKE(s,
from_t)` only if `F` holds no `REVOKE` of `s` by that issuer with a
`from_t` at or below the new one (§10.3): a second `REVOKE` of a key that
is already void from an earlier point changes no view.

The gate keeps the *later* records of `X` out. A replica that holds the
revocation and the roster that removes `X` admits `X` to no session and
takes no bundle from it. A replica that does not yet hold them can admit
`X`. It then relays the records of `X` everywhere, where they are admitted
(flagged `void`). Assumption A7 (§9) excludes this, and the H8 bounds (§5)
depend on it.

**What `from_t` can and cannot do (E4).** `from_t` is a point on the `t`
axis of the records, not a wall-clock time: `void` compares it with the
record's `t`, and a record's `t` chases the floor of its cell (§5), so an
honest record written at wall time `w` can carry any `t` between `w` and
`maxceil`. With `from_t > 0`, the key's records with `t < from_t` stay
unflagged. This is correct for a key that was *lost* and that nobody used,
and only if `from_t` is above every `t` that the key honestly wrote before
the loss. So for a lost key, the issuer sets `from_t := maxceil(F) + 1` at
issue time (`Kome.Roster`, the phase-8 revoke API); a `from_t` taken from
the wall clock at the time of the loss would void the honest writes that
chased above it. It cannot give protection against a thief. A thief
selects `t` and can backdate below `from_t`, and nobody can tell such
records from honest ones. If a key is known or suspected to be stolen,
revoke it from 0. (Kome ignores `from_t` for root revocation, above.)

## 7. Storage and tombstone expiry

**The log is a journal of operations on `F` (D9).** The store of one
collection is an append-only log and an in-memory index `cell → (offset, v)`.
The log is plaintext, and it carries no authentication: no key, no
checksum and no hash chain. Integrity and confidentiality at rest belong
to the host (file permissions, disk encryption, a sealed container), not
to Kome. A party that can write the file can do anything to the store; a
log cut at an entry boundary is a stale replica, and nothing more (§8,
the sync point). The index holds exactly the records of `F`. Per cell,
version metadata is 6 + 6 + 32 bytes plus a cached 32-byte `h`. These are
the log entries (all integers are big-endian):

```
HEADER         op = 0 ‖ "kome/log" ‖ version:u8 ‖ ns[16] ‖ root_pk[32] ‖ salt[16] ‖ data_cap:u32 ‖ slice:u16
APPLY          op = 1 ‖ len:u32 ‖ frame        a record applied and held
APPLY_EXPIRED  op = 2 ‖ len:u32 ‖ frame        a DEL applied for its effect and not held (below)
EXPIRE         op = 3 ‖ horizon:u48            Frontier.Expire at this horizon, or a lowered horizon
EXPIRE_NONE    op = 4                          the horizon lowered to "none"
```

The log starts with exactly one `HEADER` (`version = 1`; 80 bytes). Its `ns`
must be equal to `BLAKE2b-256(root_pk ‖ salt)[0:16]`. This fixes the
founding key for all the store's operations. Its `slice` field is a check:
the slice is the constant `Slice_Max` at every replica, and a `HEADER`
with another value is refused. Its `data_cap` is the data capacity that
wrote the log; the capacity in force is a parameter of the open, kept
outside the log or appended as a `CAPS` entry, and a reopen at a smaller
`data_cap` is allowed whenever the replay fits in it (§10.10 (a)). "No
horizon" is an entry of its own (`EXPIRE_NONE`), not a reserved horizon
value (H6). Kome persists nothing else in the log; the one other durable
value is `seq_self(ns)`, which the binding keeps beside the store (§5,
A5). The registers are functions of `F`
(§4), and refused or dominated records changed nothing.

**Deletion is not erasure.** A `DEL` frees the bytes of its entity in `F`,
the index and the next compacted log. It does not erase them: the
dominated `APPLY` entries stay in the log until compaction, the old
file's bytes stay on the device after compaction renames the new file over
it until the file system reuses them, a relay keeps every bundle it
stored, and a member
that joins later walks the chain down and can open those bundles (§6,
links). What Kome guarantees is space and convergence (H7), not that a
deleted value is unrecoverable from a device or a relay. Erasure at rest is
the host's.

**Compaction** writes a new log. The new log has the `HEADER`, then one
`APPLY` per record of `F`, then one `EXPIRE(horizon)` if the store has a
horizon. The `APPLY` entries put all authorization records first and then
all data records (each part in index order). Compaction is a store duty,
not only a caller's: after an append, when the entry count passes
`2·|F| + c` (a small constant `c`), the store runs `Compact` itself. So
the log holds at most `2·|F| + c` entries after every operation, which
bounds the dominated bytes that a deleted value leaves behind and bounds
the cost of the next open.

**Replay** (when a store opens) does these steps:

1. It checks the `HEADER`.
2. It takes the capacities of this open. A larger `data_cap` than the
   logged one is always allowed, and a smaller one is allowed when the
   replayed `F` fits in it (`NO_SPACE` otherwise, and nothing is written).
3. It starts from the empty state with the logged founding key.
4. It does the entries in order. An `EXPIRE(horizon)` is applied at
   `min(horizon, maxceil(F) − del_ttl_eff(F))` for the `F` replayed so far
   (`Horizon_At(F, U48'Last)`): every `EXPIRE` that the store wrote meets
   this bound, because `maxceil` never falls and `del_ttl_eff ≥
   Del_TTL_Min`, so a valid log replays as written, and a torn or corrupt
   horizon (bytes that read as `2^48 − 16`, for example) cannot drop every
   tombstone. T18 allows the lower horizon that the clamp can give.

Replay verifies one signature per logged record, so an open costs
`O(entries)` signature checks: with the compaction trigger above, that is
`O(|F|)`, and never a multiple of it. `Open_From_Log` is strict: the
whole log replays, or the open refuses. The binding owns the two cases
that strictness alone would make permanent (REQUIREMENTS H8: one entry
must not brick the store). A *torn tail* (power lost inside an append) is
cut: `Open_From_Log` reports `Valid_Length`, the offset of the last
complete entry, and the binding truncates the file there and opens again;
the prefix replays, because the log is append-only and every
entry-boundary prefix of a log that the store wrote is a log that the
store wrote (T18-prefix). A *corrupt entry* in the middle (a flipped byte,
a failed signature check) stops the replay at that entry: the binding
opens the prefix before it, reports `DEGRADED`, and syncs again; the
entries after the corrupt one are not skipped, because an `EXPIRE` or a
`DEL` among them could have removed what the prefix still holds, and a
replica that holds more than it should is only stale. A *duplicated*
entry cannot occur: the binding writes each append at the `Log_Length`
from before the call (`pwrite` at that offset), so a retry after a write
error overwrites the same bytes and never appends twice.

Each operation is a deterministic function of the held set. After
compaction, Kome admits each authorization record and each data record. The
reason is that the authorization part is complete before the first data
record, and `F` is an antichain under `dom`. T18 states the result: the same
held set and the same index entries as sets (array order can be different
after compaction).

**Order of operations and room (D11, E1, E2).** When Kome applies a decoded,
verified frame, it does these steps. All classification occurs before any
change, and no refusal changes anything:

0. Wrong `ns`, or an authorization record whose `root_pk` field is not the
   store's founding key: `MALFORMED`. (Two key pairs can share a
   128-bit `ns` at approximately 2^64 work. This check makes the decoder,
   the capacity rows and `root_void` agree on which key is the founding
   key.)
1. A data record that is not admitted: `INADMISSIBLE`.
2. Already held: `OK`, no change.
3. Dominated by a held record: `DOMINATED`. It needs no room in the
   frontier, the log or the index, and it never gets `NO_SPACE`.
4. A `DEL` with `t ≤ horizon` (expired on arrival, below): Kome applies it
   for its effect. If it dominates nothing held, nothing changes. If not,
   its dominated records leave `F`, and Kome logs one `APPLY_EXPIRED` entry
   (the `DEL` needs only log room). The status is `OK`, and Kome does not
   hold the `DEL`.
5. Room. Data records share one **data capacity** (`data_cap`). Each signer
   has its own **slice** of `slice` authorization records (at most
   `Slice_Max`), in one of `Signers_Max` = 16 slots. Slot 1 is reserved for
   the founding key. Kome assigns a slot to a certified root when it holds
   that root's first record, and never frees the slot. (No record of a
   signer can leave `F` except under another record of the same signer.) A
   record that dominates a held record frees the slot of that record, which
   is always in its own row (§3). The refusals are:
   - A data record whose capacity is full and that frees nothing:
     `NO_SPACE` (the caller compacts, deletes, or stops). When the refused
     record came from a peer, the transport reports the refusal as a
     replica status, because the replicas then disagree about that
     record (below, and §10.5).
   - An authorization record whose signer's slice is full and that frees
     nothing, or whose signer is new when all 16 slots are in use:
     `AUTH_FULL`.
   - Not sufficient log bytes for the entry: `LOG_FULL`. The binding
     compacts and retries. Log bytes are a capacity class of their own,
     shared by every record, so a store whose log is too small for its
     rows can refuse the founding `REVOKE` after a flood of large values,
     and compaction would free nothing. The binding therefore keeps
     **`Log_Fits`**: `log_cap ≥ 80 + 7 + (data_cap + 16·slice + 1) ·
     Entry_Max`, with `Entry_Max = 5 + 41 136` (the APPLY prefix plus the
     largest frame). Under `Log_Fits`, a compacted log has room for one more
     entry of any kind, so `LOG_FULL` only ever means "compact first". It is
     a bound on `data_cap` for a given `log_cap`: with a 1 GiB log, at most
     about 17 000 data records beside 16 full slices. `Kome.Store.Log_Fits`
     is the test, and `Open` and `Open_From_Log` do not require it (small
     logs are legitimate for tests and for tiny stores); a binding that
     opens a store without it accepts that `LOG_FULL` can be permanent.

   The index always has room for what `F` holds. `W` (at most one subject
   per held `GRANT`) always has room.
6. Apply: drop what the record dominates, hold the record, append `APPLY`,
   and index the record.

**What `AUTH_FULL` means.** Kome never drops a key silently, and a refused
record changes nothing. But then the set of an over-quota signer's records
that a replica holds depends on arrival order. So replicas can disagree
permanently about these items:

- that signer's surplus records;
- the data records that only its surplus `GRANT`s admitted;
- the records that those data records dominate;
- that signer's contribution to `maxceil` and `del_ttl_eff`, when the
  refused record is a roster. `maxceil` is a maximum over *held* rosters,
  and a refused roster does not count. A stolen root with a long cap can
  fill its slice with `REVOKE`s at one replica and send its roster first
  at another: the second replica then admits data up to that roster's
  ceiling, and the first discards the same data for good. A root-void
  does not lower `maxceil`, so the disagreement is permanent, and it
  ends only when every honest root's ceiling passes the stolen one's.

Honest roots never reach their slice (the honest-issuer rules, §10.3), and
the founding key certifies at most 15 distinct signer keys (A1). The
founding key's slice is a lifetime budget, not a reserve by itself:
`REVOKE`s are never dominated, so about 250 key rotations (a `REVOKE` plus
a `GRANT` each) would fill it, and then `REVOKE(R, 0)` would get
`AUTH_FULL`. So the founding key keeps a reserve of 15 entries for
root-voids (§10.3) and does no routine `GRANT`s or `REVOKE`s. So only a
stolen root can cause this. It cannot touch any other signer's slice. When
it is root-voided, all that its surplus admitted reads `void`. After that,
byte-for-byte agreement comes back only if the owner re-founds the
collection. The slice is the constant `Slice_Max` at every replica, so no
two replicas disagree about where a slice ends.

**Drop rule.** A record leaves `F` if and only if:

```
dom(x, F)                                                  -- deterministic, membership-free (T3)
∨ (x is DEL ∧ x.t ≤ horizon)                               -- tombstone expiry
```

**Expiry is an operation on `F` (D10).** `Expire(now_local)` calculates:

```
horizon := min(now_local, maxceil(F)) − del_ttl_eff(F)       -- in 64 bits; below 0 means "none"
```

(Kome uses 64 bits so that `x.t + del_ttl` never wraps. At `x.t = 2^48 − 1`,
a 48-bit sum would change an immortal tombstone into an instant one.) The
clock is clamped to `maxceil`, so the roots' clocks set the limit on
expiry, not one device's clock. A clock set far ahead (spoofed time, or
the user) cannot expire all tombstones at once and make
`DEL`s that arrive expire on arrival. The same clamp means that A3 gates
expiry as well as writing: once wall time passes `maxceil` (the root
devices stopped refreshing), every new `DEL` is emitted at `t = maxceil`,
which is above the frozen horizon, so no tombstone expires until a fresh
roster arrives. `Ceiling_Stale` (`now > maxceil`) and `Horizon_Frozen`
are statuses that the store computes and the C ABI shows (§10.6). A
device with no real-time clock, or one whose clock it does not trust,
calls `Expire(now := maxceil(F))`: it then expires exactly what the
fastest honest replica has expired, and never more.

The clamp protects tombstones only as far as the ceiling leads the wall
clock. A clock ahead by `δ ≤ maxceil − now` expires `DEL`s `δ` early, and a
spoofed-ahead device with `maxceil − now ≥ del_ttl_eff` would hold no
tombstone at all. So the honest-issuer rules keep `ceiling_t ≤ now +
Cap_Lead` with **`Cap_Lead` = 3 days `< Del_TTL_Min`** (§10.3), and every
expiry statement below counts the window `del_ttl_eff − Cap_Lead`, measured
against the fastest replica's horizon. A `DEL` from a slow or clockless
writer would expire on arrival at every clocked replica and never be
relayed; so a `DEL` is emitted at `t ≥ maxceil − Cap_Lead` (§5), and lives
at least `del_ttl_eff − Cap_Lead` everywhere.

If `horizon` is above the store's horizon, `Expire` removes from `F`
exactly the `DEL`s with `t ≤ horizon` and sets the store's horizon. If
`horizon` is below it (a clock stepped back, or a higher `del_ttl_eff`),
`Expire` only lowers the store's horizon. So fewer `DEL`s that arrive
expire on arrival, and A4 does not become narrower. A `DEL` that `Expire`
already removed stays removed. If it arrives again, Kome applies it and
holds it until it expires again.

Kome logs `EXPIRE(horizon)` if and only if the call removed a record or
lowered the horizon. So periodic calls do not make the log larger. Kome
keeps a raise that removed nothing in memory only. A reopened store's horizon
is then at most the live one, so the store only holds more records
until its next `Expire`. The registers do not change, and when Kome removes
records from a frontier, the result is a frontier.

The store also keeps an **expire mark**: the largest `d.t` of any `DEL`
that `Expire` removed or that an `APPLY_EXPIRED` applied. `Expire` only
raises it, replay rebuilds it from the logged entries, and it is not part
of `F`. The write path reads it: when `mark < maxceil`, `Choose` emits at
`t ≥ mark + 1` (§5). Without the mark, a device whose clock was reset
after it expired `d` would write the entity at a `t` below `d.t`, and
every replica that still holds `d` would drop the user's write.

After a session's authorization phase, and before its data phase, the
transport calls `Expire(now)` if `del_ttl_eff` changed: a roster with a
longer `del_ttl` lowers the horizon, and the data phase must not expire on
arrival a `DEL` that the new value keeps (§8).

`del_ttl_eff` is the largest `del_ttl` of the rosters that are not
root-voided (§3). Decode refuses a roster whose value is outside [7 days,
3 650 days] (§2 rule 3). So a stolen root cannot set it to zero to
resurrect deleted data in bulk. It cannot make it shorter at all: a roster
with a shorter `del_ttl` dominates no roster with a longer one (§3), so
neither a stolen root nor an honest refresh lowers the maximum. If the
stolen root makes it longer, this stops when the stolen root is
root-voided, and the recovery roster carries at least the previous value
(§6). If there is no horizon yet, nothing expires.

The second clause is **apply-then-expire**, not refuse-on-arrival. Kome
always applies a `DEL` that arrives with `t ≤ horizon` (it dominates and frees
the entity's values). Only after this, because the `DEL` is expired,
Kome does not hold it. If Kome refused an expired `DEL` on arrival, two
replicas with a skew of two milliseconds could diverge and then resurrect
the entity on both.

With apply-then-expire, a skewed pair converges on the next exchange. The
replica that still holds the `DEL` sends it again, and the other replica
applies and expires it again. The cost is one frame per session until the
two replicas expire it. The residual is this: expiry is not a
join-endomorphism, `expire(F({d, p})) = {}` but `F(expire({d}) ∪ {p}) =
{p}`. So any copy of a frame that `d` dominated, delivered after every
replica expired `d`, brings the entity back: a straggler that never saw
the `DEL`, a relay that stores an old bundle (bundles carry no freshness,
and a synthetic nonce makes a replayed bundle identical to the original),
a read-only member with a saved frame, or a store restored from a backup
taken before `d`. A4 names every one of these copies. If it fails, the
entity comes back with its stale fields, and the user deletes it again.
A4 is a liveness assumption, and §9 states it as one: the safety
theorems (T3, T4) hold without it.

**Why A4 and not a sync-frequency assumption.** The assumption "every
member syncs with some member once per `del_ttl`" is not sufficient. A
four-member schedule can satisfy it while the `DEL` reaches two members and
both expire it. Then a third member that never saw the `DEL` seeds the
entity again everywhere. Expiry needs **A4 (§9): every `DEL` `d` is
admitted and durable at every member within `del_ttl_eff − Cap_Lead` of
`d.t`, and no frame of a record that `d` dominates is delivered to a
replica after that replica expired `d`**. "Admitted", not "arrived": a
`DEL` discarded as `INADMISSIBLE` and never offered again does not count
(bundles are closed under admission, §8). "Durable", not "applied": a
lost log tail counts as a backup restore (§8, the sync point). The
sync-graph diameter times the sync period is less than the window. If
this assumption fails, deleted data comes back, but live data is never
destroyed. For this reason, the design prefers tombstone expiry to
root-signed snapshots.

**Chased tombstones (residual).** A `DEL` that dominates a far-future `PUT`
must chase to `t > p.t`. So its tombstone lives for `δ + del_ttl`, where
`δ` is how far ahead the clock that pinned the entity was. `maxceil − now`
sets the limit on `δ`. This is the per-cell adoption that C5 allows: the
pinned cell, and only that cell, carries the other writer's lead into the
`DEL`'s `t` and so into its expiry. Order on a separate counter would
remove this residual. But an expiry clock that the writer selects is worse
than an inflated clock. The residual is the storage of one tombstone frame
per pinned entity, for at most one horizon after `del_ttl`.

**Bounds.** After `Expire`, `|F(ns)| ≤ live cells + DELs younger than
del_ttl_eff + authorization records`. `data_cap` sets the limit on the data
part. `Signers_Max × Slice_Max = 16 × 512 = 8 192` records sets the limit on
the authorization part (each signer's rosters, `GRANT`s and `REVOKE`s,
within its slice). Thus `|W| ≤ 8 192`. This bounds *storage*: the keys
that can hold records. The devices that can sync are bounded by the gate,
at most `Members_Max` = 64 per collection, the members of one roster (§6).
The state is `F`, the index, the horizon and the expire mark; every
per-session value lives in the session and is gone when it ends.

## 8. Reconciliation and digest

Elements are the records of `F` for one `ns`. An element's key is
`kind:u8 ‖ ent[16] ‖ fh[32] ‖ h[32]` (81 bytes). `fh` is the BLAKE2b-256 of
the field name, and it is zero where a kind has no entity or field. The kind
values are `ROSTER = 0, REVOKE = 1, GRANT = 2, DEL = 3, PUT = 4`, and keys
compare bytewise. Authorization records sort first. The key space splits at
`Data_Lo = 03 ‖ 0^16 ‖ 0^32 ‖ 0^32` into the **authorization range**
`[Min_Key, Data_Lo)` and the **data range** `[Data_Lo, Max_Key)`. `Min_Key`
is all zeros, and `Max_Key` is `FF ‖ 0^80`.

**Fingerprint = digest (D7).** For a record `e` with content hash `h(e)`
(32 bytes, in the order that BLAKE2b produced them):

```
B_i(e)     := BLAKE2b-256("kome/acc" ‖ h(e) ‖ u8(i))           for i = 0..15
acc(e)     := Σ_{i=0..15} LE(B_i(e)) · 2^(256·i)  mod 2^4096,   LE(B) := Σ_j B[j] · 256^j
ACC(R)     := Σ_{e ∈ R} acc(e)  mod 2^4096
fp(R)      := BLAKE2b-256("kome/fp" ‖ u64(|R|) ‖ ACC_le(R))
digest(ns) := fp(F|ns)
```

An equivalent statement: `acc(e)` is the 512-byte string `B_0 ‖ … ‖ B_15`
read as a little-endian integer. `ACC_le(R)` is the 512-byte little-endian
form (byte `k` is `⌊ACC/256^k⌋ mod 256`).

`"kome/acc"` is the bytes `6B 6F 6D 65 2F 61 63 63`, and `"kome/fp"` is
`6B 6F 6D 65 2F 66 70`. `u64(|R|)` is big-endian. The accumulator is the
only little-endian quantity in Kome; all other integers are big-endian.
`spark/vectors/digest.txt` holds the normative known-answer vectors.

`ACC` is homomorphic over disjoint union, so prefix sums give any sub-range
at low cost. The snapshot stores `P(K) = ACC(L(1 .. 64K))` for each full
block `K = 1 .. ⌊n/64⌋`. It also stores one more entry, the total
`P_end = ACC(L(1 .. n))` (D15). Let `Pre(x) = ACC(L(1 .. x))`, so a range is
`Pre(b) − Pre(a)`. Each end `x` starts from the nearest stored point `A(x)`.
This point is the block boundary below or above, or `P_end` for an end in
the tail after the last full block. It is at most 32 element terms away:
`Pre(x) = P(A(x)) + fwd(x) − bwd(x)`. Here `fwd` is the terms walked
forward, and `bwd` is the terms walked backward.

Kome calculates the range with two accumulators,
`Plus = P(A(b)) + fwd(b) + bwd(a)` and `Minus = P(A(a)) + bwd(b) + fwd(a)`,
and one subtraction `Plus − Minus`. This is at most 64 big-integer additions
and exactly one subtraction for each range, including ranges that end in
the tail. The cost is 8 bytes amortized per element. A snapshot cache of the
prefix sums stays valid between sessions, but a per-session keyed sum would
force O(n) hash operations per session.

A k-sum attack on a 4096-bit modulus costs approximately 2^128 at best:
that is Wagner's minimum over every list count `k`, reached at `k = 2^64`
summands, which is 2^64 inserted records. Kome's own parameters put the
attack far above it. A frontier holds at most `Held_Max` = 2^20 records,
so a colliding pair of record sets has at most 2^21 signed summands, and
with `k ≤ 2^21` Wagner's cost is at least about 2^186. The lattice route
gives the same answer: a collision is a short vector (every coefficient in
`{−1, 0, 1}`, an `l∞` bound of 1) in a knapsack lattice modulo 2^4096 with
at most 2^21 columns, which is an SIS instance with no known solver below
that bound. A member could break a 256-bit sum in approximately 2^32. For
this reason, the sum is 4096 bits.

**Messages.** All integers are big-endian. `g` is the size of a message's
reply group (0 only for a root `RANGE`).

```
OPEN      5 ‖ proto:u8 ‖ ns[16] ‖ n_rv:u8 (≤ 15) ‖ n_rv × frame[275]
HELLO     1 ‖ n_auth:u32 ‖ n_data:u32 ‖ digest[32] ‖ cred_len:u16 ‖ cred[cred_len]
RANGE     2 ‖ g:u8 ‖ lo[81] ‖ hi[81] ‖ count:u32 ‖ fp[32]
ELEMENTS  3 ‖ g:u8 ‖ lo[81] ‖ hi[81] ‖ n:u8 ‖ n × (key[81] ‖ flen:u32 ‖ frame)
HAVE      4 ‖ g:u8 ‖ lo[81] ‖ hi[81] ‖ n:u8 ‖ n × (key[81] ‖ flen:u32 ‖ frame)
```

**OPEN (pre-gate, D13).** `proto = 1`. `ns` is the collection. The
initiator sends its `OPEN` first. The responder waits for it, and answers
with its own `OPEN` only when the `ns` matches; on a mismatch the session
stops with nothing sent, so a stranger that guesses a Noise key learns no
`ns`, `root_pk` or revoked root from a Kome endpoint. The matching `ns`
binds the digest that follows to the collection.

The frames are the sender's **root-void set**: for each subject `s` that is
`root_void` in the sender's `F`, the founding-issued `REVOKE` of `s` with
`from_t = 0` and the least `h` (one frame per subject, independent of
whether the sender holds any record that `s` signed). A subject can have
several founding `REVOKE`s, because `REVOKE`s are never dominated; one is
enough, since `root_void` ignores `from_t`. The set has at most 15
subjects (`Signers_Max − 1`), so an `OPEN` is at most 4 144 bytes. The
sender includes the set only when the peer's Noise static key is a member
`dh_pk` in some roster that the sender holds, and sends `n_rv = 0`
otherwise: a stranger gets no list of the collection's revoked roots. The
D13 release still works, because the replica that a thief captured holds
the thief's roster, and the honest sender holds the thief's `REVOKE`
whether or not it ever held a record of the thief.

The receiver checks that each frame is a `REVOKE` that the founding key
signed. It verifies and applies the frames whose subject is a signer that it
holds and that is not yet root-voided. It skips the other frames without
verification, and this sets a limit on pre-gate work. (A captured replica
holds the thief's roster, so the thief is a held signer there, and its
`REVOKE` is verified.) Only then does it evaluate the gate (§6). The
frames are signed records that every replica admits in any case. So it is
safe to apply them before authentication, and the transport sets a rate
limit on pre-gate work per peer. What an `OPEN` from a non-member can do
at a stale replica is the recovery transient of §6: it starts it, and the
replica's next member session ends it.

**HELLO (post-gate, D13).** `n_auth` and `n_data` are the sender's element
counts in the two ranges. They set the size of the round-0 sketch and the
budgets. They go into these only as `min(claimed, Held_Max)`. `Held_Max` is
the frontier's bound, the one constant that the frontier and
reconciliation both use. `digest` is `digest(ns)` of the sender's
snapshot.

`cred` is the sender's credential. It is the frame of a roster in the
sender's `F`. The members of this roster include the sender's Noise static
key as a `dh_pk` (usually this roster is `ROSTER_eff`). It is at
most 10 099 bytes, so a HELLO is at most 10 142 bytes. HELLO carries
**no register values**.

A side sends its HELLO only when it has admitted the peer, so a non-member
learns no membership list. The receiver refuses a credential that is not
such a roster. If the credential is such a roster, the receiver decodes,
verifies and applies it like any authorization record, and evaluates the
gate again. If the gate then admits the peer and the receiver has not sent
its own HELLO, it sends it now. (This is how a newly added member reaches a
stale replica. The stale side admits the newcomer when it sees the
newcomer's credential.) If no side can admit the other, the session
times out.

A peer can lie, so Kome trusts nothing in an `OPEN` or a HELLO. A false
count or digest only costs rounds within the session budgets, and the frames
are signed records. Equal digests end the session after the HELLO exchange
(under A2 they mean equal frontiers). Each side takes its snapshot when it
encodes its HELLO. This occurs after it applies the peer's `OPEN` (and the
peer's credential, if it came first). The snapshot is `Snapshot_Of(F)`,
built in SPARK from the store: its keys are `Key_Of(H)` for each held
header, in key order, and its frames come from the log, so the digest of
the snapshot is the digest of `F` by construction, and no caller can
present a snapshot that `F` does not have.

**Session (D14).** The two sides send `OPEN` after the Noise handshake. Then
they exchange HELLOs as above. Then:

- **Auth phase.** The initiator sends the root `RANGE(g = 0, [Min_Key,
  Data_Lo))`. When nothing that it asked is open (its pending weight is 0),
  the authorization phase is complete on its side.
- **Data phase.** The initiator then sends the root `RANGE(g = 0, [Data_Lo,
  Max_Key))`. When nothing that it asked is open again, it is **done**. The
  responder accepts the data root only after it has received the
  authorization root and nothing that it asked is open. (On an in-order
  transport, the initiator answered all of it first.) The responder is done
  when it has received the data root and nothing that it asked is open.
- Only the initiator sends `g = 0` messages: exactly these two, in this
  order, with exactly these bounds. The receiver refuses any other `g = 0`
  message, and the refusal changes nothing. Examples are an `ELEMENTS` or
  `HAVE` with `g = 0`, a root `RANGE` with other bounds, a repeated root,
  and a data root before the authorization root.

After the authorization phase, the two sides hold the same authorization
records, unless one side refused one with `AUTH_FULL` (§7). In that case
they can differ in `maxceil` and `del_ttl_eff` as well as in the refused
record, because a refused roster does not count: the §7 "What `AUTH_FULL`
means" list names this case, and it needs a stolen root. In every other
case they have the same `maxceil` and `W`, and each data record that a
peer sends in the data phase is admissible on arrival. This makes the
exchange clause of T4 true without registers in the HELLO. Between the two
phases, each side calls `Expire(now)` if the authorization phase changed
its `del_ttl_eff` (§7), so that the data phase expires on arrival only
what the new value expires. The initiator is the Noise initiator.

**Replies.** Each `RANGE` or `ELEMENTS` requires exactly one reply group.
`HAVE` requires nothing. Let `window` be the elements of our snapshot in
`[lo, hi)`:

- `RANGE` whose `(count, fp)` are equal to ours over `[lo, hi)`: one empty
  `HAVE` over `[lo, hi)` (the confirm).
- `RANGE` otherwise, `|window| ≤ 4`: `ELEMENTS` over `[lo, hi)` that carries
  exactly `window`. (If the elements do not fit in one message, send one
  `ELEMENTS` per element, each over a sub-range that holds only that
  element.)
- `RANGE` otherwise: at most 16 `RANGE`s that tile `[lo, hi)`. Each carries
  our exact count and fingerprint of its sub-range, and each holds strictly
  fewer of our elements (balanced: `⌊n/16⌋` or `⌈n/16⌉`).
- `ELEMENTS`: deliver exactly the listed items that are not in our snapshot.
  Then, if `|window| ≤ 4`, send `HAVE` over `[lo, hi)` that carries exactly
  `window` minus the listed items (one empty `HAVE` if there are none). If
  not, use the split above.
- `HAVE`: deliver exactly the listed items that are not in our snapshot. Do
  not reply.

A reply never mixes a `HAVE` with other kinds. Each plan in a reply is
exact: a `RANGE` carries our true count and fingerprint, and an `ELEMENTS`
carries all our elements of its range. Descriptors are self-contained.

**Replies are bound to obligations.** Each side keeps a FIFO of the
obligations it opened (the `[lo, hi)` of each `RANGE` and `ELEMENTS` it
sent), bounded by the range budget. Each direction of the session is in
order, so reply groups arrive in request order, and a side accepts a
reply only when it matches the head obligation; any other reply is
refused and changes nothing. So a duplicated or forged reply cannot close
another obligation, and `Complete` means that every obligation got exactly
one full reply group. A fingerprint over a sub-range costs at most 64
additions and one hash through the D15 prefix sums, never a pass over the
slice, so the work of a session is `O(n log n)` for `n` held elements,
whatever a peer asks.

The session layer requires exactly-once, in-order delivery: Noise's nonce
counter rejects a replayed or reordered message, and a rejected message
counts as loss. If a data root overtakes the last reply of the
authorization phase, the receiver refuses it, and the session then never
completes. **If a message is lost, or a root message is reordered, the
session never completes.** The caller times out and starts a new session
from the `OPEN`.

A session with no loss takes at most `⌈log₁₆ N⌉ + 2` rounds per phase. If
loss occurs, convergence holds given fairness at the session level (some
session completes eventually), and T7 states this explicitly. Per-session
budgets set a limit on what a hostile peer can get. The budgets count the
messages accepted, the `RANGE`s emitted and the item bytes emitted, over the
two phases. A member that always claims `Held_Max` elements gets the largest
budgets in every session. That member is authorized to read `F` in any case.
The transport must set a limit on how frequently a peer can open sessions.

**Message size (D12).** Each message is at most `Max_Message_Len` = 48 KiB.
A frame is at most 41 136 bytes (a `PUT` with a 32-byte field and a
40 960-byte value). This is less than the 48 902 bytes that one `ELEMENTS`
item can carry (`48 KiB − 165 − 85`). It is also less than the sealed-bundle
plaintext bound. So each well-formed record fits in one message on each
transport. The implementation checks the two inequalities at compile time.

**Round 0: one-round set difference (C8).** At the start of each phase, each
side can send an invertible Bloom lookup table. The table is over the 32-byte
element hashes of that phase's range. The HELLO counts set the size of
the table. A clamp makes one sketch fit in one message (at most 1 000 cells
of 44 bytes). A side subtracts the two tables and peels the result.
This gives the exact symmetric difference in one round if the difference is
small, which is the usual case.

Kome detects a peel failure and a false decode before it writes any state.
Each recovered hash must verify against a held or received record.
If either occurs, the phase continues with the range protocol above. The
sketch is homomorphic, so Kome caches it per collection and updates it per
record. It adds nothing to the trusted core: Kome still delivers and checks
as a record each element that the sketch names.

**Transports.** Kome uses Noise XK for interactive sync. The responder's
static key is a member `dh_pk` that the initiator takes from its
`ROSTER_eff` (or from the credential it was handed at enrollment), and
the prologue binds `ns`. In XK the responder's static key never crosses
the wire, and the initiator sends its own static key encrypted under the
responder's; so a stranger that scans for Kome endpoints (a BLE or LAN
scanner) learns that an endpoint answers and nothing else: no `dh_pk`,
no `ns`, no membership, and no way to link the endpoint across places,
network changes or collections. (Noise XX would hand the device's
long-term `dh_pk` to any party that completes a handshake.) The static
key is **per collection**: `dh_sk_ns = KDF(device secret, ns)`, so the
same device has unrelated `dh_pk`s in two collections, and two
memberships cannot be linked by key. This per-collection `dh_pk` is the
member entry that rosters list and that opens the boxes: `dh_sk_ns` is
the member's whole capability in that collection (§6, T14). The
transport refuses a low-order Noise static key from a peer and uses a
constant-time X25519. It uses sealed bundles for store-and-forward:

```
bundle = ns[16] ‖ nonce[24] ‖ XChaCha20-Poly1305(k_b, nonce, AD = ns ‖ u16(epoch), pad(plaintext))
k_b    = f(k_epoch, "kome/bundle" ‖ ns)           -- keyed BLAKE2b-256 under the epoch key (§6)
nonce  = BLAKE2b-256("kome/bnonce" ‖ k_b ‖ pad(plaintext))[0:24]
```

The epoch is in the associated data only, never in the clear: the sealer
fills it from its `ROSTER_eff.epoch`, and the opener from its own, which
is the only epoch it accepts anyway. `pad` is deterministic: it extends
the plaintext to the next of a fixed set of bucket sizes, so a bundle's
length shows its bucket and not its content, and a membership change (a
roster with one member more or less) does not show as a length change.
Kome accepts a bundle only under `ROSTER_eff.epoch`, with `bundle_key(F)`
(§6). All members share `k_e`, so the nonce must never come from a
per-device counter. The nonce is synthetic, as for boxes. Identical
plaintexts give identical bundles, and this shows only that the
plaintexts are identical. The plaintext is a list of `ELEMENTS` items,
sorted by element key, with a total of at most `Max_Message_Len` bytes
before padding. The receiver applies every item with kind < 3 before any
item with kind ≥ 3 (D14: the authorization-first pass of T4 (a)). Relays
see ciphertext, `ns`, the bucket size, timing and the transport's routing
key.

**Bundles are closed under admission.** A bundle carries, ahead of its
data records, every `GRANT` of each data author that the sender holds and
the sender's roster with the largest ceiling (or an authorization-only
bundle goes first). So a `DEL` in a bundle is admitted wherever the bundle
is opened, and never discarded for a stale `maxceil` or a missing `GRANT`
and then forgotten (`auth_first_closed` in Lean). A `DEL` that a session
discards as `INADMISSIBLE` is offered again by the next session (§4), but
a bundle has no next session. The quarantine flag (§6) suspends bundles.

**Suspect-relay attribution.** When a record arrives, by session or
bundle, whose author is already `void` in the receiver's view (a counting
`REVOKE`, or a root-voided issuer), the transport records the delivering
peer's `dh_pk` (the Noise static key, or the bundle's mailbox owner) and
reports the flag `SUSPECT_RELAY` for that peer. Admission does not change.
The owner decides whether to remove the relay. This is how a failure of A7
(§9) becomes attributable instead of silent.

**Durability before acknowledgement.** The log is an append-only buffer;
the store binding writes it to its device. The binding makes the log
durable up to its current `Log_Length` (the sync point) before the
transport counts a session as `Complete`, before it acknowledges a bundle
or deletes it from a mailbox, before it relays an applied record to
another peer, and before it continues after applying an authorization
record. Otherwise a crash can undo an applied `DEL` while every other
replica expires it (A4, §7), or drop a `REVOKE` that this replica already
told a peer it holds. A log cut at an entry boundary by a crash before
the sync point is a stale replica, which the next session repairs; the
log needs no hash chain for this.

## 9. Proof obligations

Each obligation is a finite, first-order fact about sets of records. ✓ marks
the obligations that core Lean proves (§10.1 gives the exact scope of each
one); ✗ marks the ones that are open or argued on paper: T4 (c), T7 and
T14.

- **T1 ✓ Total order.** On well-formed records with `h` injective, `v` is a
  strict total order.
- **T2 ✓ Monotone domination.** `H ⊆ H' ⇒ dom(x, H) ⇒ dom(x, H')`.
- **T2' ✓ Upward closure.** `y dom x ∧ z dom y ⇒ z dom x`, for every kind.
- **T3 ✓ Frontier homomorphism.** `F(H₁ ∪ H₂) = F(F(H₁) ∪ F(H₂))` and
  `F(F(H)) = F(H)`. Thus, if a replica drops dominated records anywhere and
  at any time, no future frontier changes.
- **T4 ✓ Convergence.** Assume the state `F`, admission of data records
  under `(maxceil(F), W(F))`, and discard of inadmissible records. Then:
  - (a) One pass that applies the authorization records of a set before its
    data records, from any frontier, gives `F` of the admitted records of
    the union.
  - (b) Two passes over the same records, in any order and with any
    duplication, give the same result. (The second pass offers again what
    the first pass refused.) So two replicas that applied the same records
    *and expired at the same horizon* hold the same `F`: the horizon is
    per replica (§7), so "same records" alone gives the same `F` only
    before any expiry. This is stated for `applyD` (apply, no horizon).
    The store expires a `DEL` on arrival at its horizon `h` (`applyH`), and
    then the order matters when a record that an expired `DEL` dominates
    arrives after that `DEL` (`[d, p, d, p]` gives `{p}`, `[p, d, p, d]`
    gives `{}`). Under `NoLateDom(h, l)` (no such late arrival), the two
    agree after an expiry at `h` (`expire_applyAllH`); A4 excludes the
    late arrival.
  - (c) ✗ After a complete two-phase session (§8) with no capacity
    refusal and no expiry crossing, each side holds at least the join of
    the two snapshots: `F_A ⊒ F(snap_A ∪ snap_B)`, and the same for `B`.
    The snapshots are frozen at the HELLO while other sessions, writes and
    bundles keep changing `F`, so "both hold `F(F_A ∪ F_B)`" is not the
    statement; the join-inclusion is, and it follows from T3 and T4 (a)
    once the session delivered the snapshot difference. That delivery,
    authorization part first and then data part, is the content of T7,
    which is open. So (c) is T7 delivery plus T4 (a), and it is not
    proved.

  (a) and (b) hold for runs with no capacity refusal (`NO_SPACE`,
  `AUTH_FULL`). Kome offers a `NO_SPACE` record again later, and `AUTH_FULL`
  is the stated residual of §7.
- **T4' ✓ Monotone admission.** If each authorization record of `H` is in
  `H'`, then `adm(r, H) ⇒ adm(r, H')`. Also, `maxceil(F(H)) = maxceil(H)`,
  `W(F(H)) = W(H)` and `wcap(F(H), k) = wcap(H, k)`. So no register shrinks
  along any history, and this includes rosters of lower generation or
  ceiling and grants of lower cap. Admission never reads `REVOKE`,
  `root_void` or `W_eff`.
- **T5 ✓ View determinism.** `deleted_at`, `cell`, `exists`, `maxceil`, `W`,
  `root_void`, `W_eff`, `void`, `ROSTER_eff` and `del_ttl_eff` are functions
  of `F` as a set alone (and of the constant `root_pk`). `ROSTER_eff` uses
  the whole roster tuple to break a tie, so it does not depend on list
  order, even without A2. Also, `W_eff`, `root_void`, `ROSTER_eff` and
  `del_ttl_eff` of `F(H)` are equal to those of `H`. `far` and
  `ceiling_lead` read the local clock and are not in this list.
- **T6 ✓ Digest** (SPARK: `Kome.Accumulator`, `Kome.Digest`; there is no
  Lean statement). `digest(ns) = fp(F|ns)`; `ACC(R₁ ⊎ R₂) = ACC(R₁) +
  ACC(R₂)`; under k-sum hardness, `fp(R₁) = fp(R₂) ⇒ R₁ = R₂`.
- **T7 ✗ Reconciliation.** Start from `F_A, F_B` over `N` elements. A
  session is two sequential range reconciliations over a partition of the
  key space. Each one terminates in `≤ ⌈log₁₆ N⌉ + 2` rounds without loss.
  The measure is `(μ, k)`. Here `μ([lo, hi))` is the two sides' element
  counts in the range, and `k = 1` for a `RANGE` and 0 for an `ELEMENTS`.
  The two sides then hold `F(F_A ∪ F_B)`. If loss occurs, no session
  completes, and convergence follows from fairness at the session level.
  (This is the large Lean project.)
- **T8 ✓ Chase.** If `floor.t < maxceil`, then `v_emit > floor`. Always,
  `v_emit.t ≤ maxceil`, and `v_emit.seq` is larger than each `seq` that this
  device emitted in this collection and each own `seq` held. The result of
  the emission does not depend on `h` (§5).
- **T9 ✓ Bounded pin.** No admitted data record has `t > maxceil` or `t >
  wcap(author)` (Lean: `adm_put_le`, `adm_put_le_wcap`). After Kome
  applies a roster with a higher ceiling, no honest write to any cell is
  shadowed (this second clause follows from T8 and is not a separate Lean
  statement).
- **T10 ✓ Equivocation.** All replicas put two different records with equal
  `(author, seq)` in the same order, because `v` is a strict total order
  (`StrictTotal Version`, T1). Arrival order has no effect on `F`
  (`convergence`, `convergence_empty`; for `applyD`; with a horizon, under
  `NoLateDom`, as in T4 (b)).
- **T11 Tombstone expiry.** (a) and (b) are proved; (c) is a liveness
  argument under A4, not a theorem.
  - (a) ✓ After `Expire` at a horizon, `F` holds no `DEL` with `t ≤` that
    horizon, and `|F|` meets the §7 bound. Expiry of a frontier gives a
    frontier with the same registers.
  - (b) ✓ Apply-then-expire: take two replicas whose held sets are
    different only because one holds a `DEL` `d` with `d.t ≤ h` and the
    other does not. After the same further records, a re-sent `d` and an
    `Expire` at `h`, they agree on each record. (For `applyD`; the store's
    `applyH` agrees with it under `NoLateDom`, T4 (b).)
  - (c) Under A4 (every copy of `d` admitted and durable within
    `del_ttl_eff − Cap_Lead`, no late copy of what `d` dominates, and a
    lead of at most `Cap_Lead` at every honest root), after each replica
    has expired `d`, no replica holds a record that `d` dominated. The
    window that it tolerates is the lead that A4 names.
- **T12 ✓ Revocation locality.** When Kome applies a `ROSTER`, `REVOKE` or
  `GRANT`, `F` changes only at that record and at the records of its own
  kind and key that it dominates. It never adds or removes a `PUT` or `DEL`.
  `root_void` is monotone in `F`. For a fixed `root_void` set, the `REVOKE`
  clause of `void` and `W_eff` are monotone in `F`. (So a `GRANT` can only
  un-void, and a `REVOKE` can only void.)
- **T13 ✓ Bounds.** Each emitted record agrees with the §2 layout. `seq`,
  `t`, `gen` and `rev_seq` never wrap. At a bound, emission fails with no
  side effect. No refused apply changes the state. Every held roster has
  `gen ≤ ceiling_t` (§2 rule 2), so a certified root's `gen` is at most
  its cap, and an honest root never emits `gen > 2^47` (§10.3).
- **T14 ✗ Epoch secrecy.** Let `e` be an epoch of segment `S`. For a party
  that holds no `dh_sk` of a member listed in the roster of `e` or of any
  later roster of `S`, holds no top of `S`, and is not a root of `S` that
  is not root-voided, the bundle key `k_b` of `e` and of every later epoch
  of `S` is indistinguishable from random. A root-voided root cannot
  derive any key of a segment opened after its revocation; nor can the
  devices it held, whose `sign_pk`s recovery step 2 revokes, so no later
  roster boxes a key for them. The premises: keyed BLAKE2b-256 is a PRF
  (the chain step `k_e = f(k_{e+1}, "kome/prev")` and the bundle key `k_b
  = f(k_e, "kome/bundle" ‖ ns)` are two outputs of one PRF under one key,
  so key regression gives nothing: holding `k_e` says nothing about
  `k_{e+1}`); BLAKE2b-256 over the domain-separated inputs `"kome/eph"`,
  `"kome/wrap"` and `"kome/nonce"` is a random oracle; X25519 is Gap-CDH
  (or CDH in the random-oracle model with separate oracles, since each
  member's `dh_sk` serves both the boxes and the Noise static key:
  `dh_sk` is the member's whole capability); and
  XChaCha20-Poly1305 is an AEAD with a unique `(key, nonce)` per
  plaintext. The theorem excludes what it must: every member's `dh_sk`
  stays secret (there is no post-compromise security, §6), every root of
  the segment holds its top and so every key of the segment (the
  top-leaked procedure opens a new segment, §6), and a stranger learns
  nothing from the transport (Noise XK, §8). It is a paper argument, not
  a Lean theorem.
- **T18 ✓ Replay.** Take each store that the implementation writes. Replay
  its log from the empty state, with the logged founding key and with a
  data capacity that the replayed `F` fits in. The result has the same held set
  (and so the same registers and digest) and the same index entries, both as
  sets. The replayed horizon is at most the live one. After compaction, each
  replayed `APPLY` succeeds. The replayed horizon can also be lower than
  a logged `EXPIRE` by the replay clamp of §7. (T15–T17 are reserved for
  typed fields, C10, and are not stated.)

**Assumptions.** The assumption IDs are fixed: a restated assumption keeps
its ID, and a new one takes the next free number.

- **A1** Ed25519 (RFC 8032) is unforgeable under the strict verification
  predicate of §2. Nobody ever steals the founding key, and its holder
  certifies at most 15 distinct signer keys (renewals of a key's cap are
  unlimited). While the founding device is lost, no root is added or
  root-voided and no segment opens (§6). A certified root can be stolen.
  Until a replica holds its root
  revocation, the stolen root can do there all that a root does (§6 gives
  the list). After that, all that it issued no longer counts in that
  replica's views. Under A7, nothing that it or its grantees sign
  afterwards reaches that replica. Its permanent residue is as follows:
  `maxceil` raised up to the largest cap ever certified for it; its records
  in its own slice; and, if it overflowed its slice, the disagreement about
  its surplus (§7). Honest roots stay within the authorization bounds
  (§7: `Signers_Max`, `Slice_Max`, `Links_Max`, and the epoch space).
  Beyond these bounds, the owner must re-found the collection.
- **A2** BLAKE2b is collision-resistant. The 4096-bit sum is k-sum hard.
- **A3** A root device refreshes the roster within each horizon, and the
  refresh reaches every partition of the members, not only the one that
  holds the root device. (If not, writes degrade to ties at the ceiling,
  a `DEL` can be born expired, and tombstone expiry freezes with the
  ceiling, §7. Convergence is not affected.)
- **A4** For tombstone expiry only: every `DEL` `d` is admitted and
  durably held (or durably applied, `APPLY` or `APPLY_EXPIRED`) at every
  member within `del_ttl_eff − Cap_Lead` of `d.t`, measured against the
  fastest replica's horizon; and no frame of a record that `d` dominates
  (a stale replica's, a relay's stored bundle, a saved frame, a backup) is
  delivered to a replica after that replica expired `d`. A lost log tail
  counts as a backup restore.
- **A5** Writers persist `seq_self` per collection, durably, after
  *Choose* and before the `APPLY` is appended, and send a frame only after
  its `APPLY` is durable (Kome detects violations: `CLONE_SUSPECTED`).
- **A7 No record after revocation** (E7). No replica receives, from any
  source, a record that the subject of a `REVOKE` signed after that
  `REVOKE`, nor a record that a key granted by a root-voided root signed
  after the root-void. This is a duty of every current member, not only of
  stale replicas: a stale replica is the usual source, and a compromised
  relay or read-only member is the other (H8). The gate (§6) and the
  `SUSPECT_RELAY` attribution (§8) are the mechanisms; the write cap bounds
  the damage when the duty fails (`t ≤ wcap`). Only the H8 bounds (§5) and
  the post-revocation guarantees of §6 depend on this assumption;
  convergence does not. If it fails, every replica holds the records,
  flagged `void`, and the bytes that they overwrote or deleted leave `F`
  at every replica. Kome keeps no copy.

**There is no clock assumption for convergence.** Two replicas that
applied the same records hold the same `F` before any expiry, and two
that also expired at the same horizon hold the same `F` after it. The
horizon is per replica (§7), so expiry, and only expiry, depends on a
clock, and A3 and A4 are the assumptions that bound it.

## 10. What is open

1. **Lean model of this design.** `lean/Kome/Frontier.lean` proves the
   theorems below over finite lists. `lean/build.sh` checks the proofs by
   machine. There is no `sorry`, and the proofs use only Lean's standard
   axioms. The proof of T3 uses a general "sandwich" lemma. The exact
   scope of each check mark in §9 is this (`lean/README.md` names the
   theorems):
   - T1 (`StrictTotal Version`), T2, T2', T3: whole.
   - T4 (a) and (b): `auth_first`, `convergence_two_pass`, `convergence`,
     for `applyD`; `expire_applyAllH` relates the store's `applyH` to it
     under `NoLateDom`. T4 (c) is not proved (it is T7 delivery plus
     T4 (a)). `auth_first_closed` is the bundle rule of §8.
   - T4': whole (`adm_mono`, `maxCeil_F`, `isWriter_F`, `wcap_F`,
     `adm_F`).
   - T5: `cell`, `maxceil`, `W`, `root_void`, `W_eff`, `void`,
     `ROSTER_eff` and `del_ttl_eff` (`cell_unique`, `rootVoid_F`,
     `wEff_F`, `voided_F`, `rosterEff_F`, `delTtlEff_F`). `deleted_at`
     and `exists` have no Lean statement; they are functions of `F` by
     their definition in §3.
   - T6: SPARK only (`Kome.Accumulator`, `Kome.Digest`); no Lean
     statement.
   - T8: the `t` clause (`chase`) and D8 (`lt_iff_prefix`). The `seq`
     clause is proved in SPARK (`Kome.Emit`), not in Lean.
   - T9: the first clause (`adm_put_le`, `adm_put_le_wcap`).
   - T10: by `StrictTotal Version`, `convergence` and
     `convergence_empty`.
   - T11 (a) and (b): `expire_none`, `expire_only_del`, `expire_frontier`,
     `expire_adm`, `expire_admitted`, `expire_reapply`. T11 (c) is argued
     under A4, not proved.
   - T12, T13 (`emitT_le`), T18 (`auth_first`, over sets): whole.
   - T7 is open. T14 has a paper argument only. T15–T17 are reserved for
     typed fields (C10) and are not stated.

   The model has the five record kinds, per-signer product-order roster
   domination (strict in `gen`, with the epoch and `del_ttl`) and
   per-`(issuer, subject)` grant domination (with the cap). It also has
   `maxceil`, `W` and `wcap` as functions of the held list, the discard
   model (`applyD`), the store's apply with expiry on arrival (`applyH`),
   expiry, and the views `rootVoid`, `wEff`, `voided`, `rosterEff` and
   `delTtlEff`.

   This list is the **only divergence register**: what the implementation
   has and the model does not. Where a SPARK contract is intentionally
   different from the model, its comment says so and the difference is
   listed here (`spark/CONVENTIONS.md`).
   - No signer certificates and no well-formedness: the model assumes
     well-formed records.
   - No `ns`: the model is one collection.
   - No capacity: no `NO_SPACE`, `AUTH_FULL` or `LOG_FULL`.
   - No clock clamp: the model takes the horizon as a number, with no
     `min(now, maxceil)` and no `Cap_Lead`.
   - `Nat` for `u48`: the model has no bound on `t`, `seq` or `gen`.
   - No journal: the model has no log, no index and no replay; T18 is the
     set-level `auth_first`.
   - Expire-on-arrival: the store expires a `DEL` on arrival at its
     horizon (`applyH`), and the model's `applyD` holds it; they agree
     under `NoLateDom` (T4 (b)).
   - Outside both: the quarantine flag, the expire mark, the gate and
     assumption A7.
2. **Toolchain.** `lean/build.sh` and `spark/check.sh` get Lean and the
   GNAT, gprbuild, gnatprove, cvc5 and z3 tools from the nixpkgs revision
   that `nixpkgs.pin` names when they are not on the path.
   `lean-toolchain` gives the Lean version for users of `elan`.
3. **Root ceremonies (`Kome.Roster`, phase 8).** This document specifies
   these items, but they are not built yet:
   - certification (short caps, renewed), with the **ceremony log**: the
     founding device records every `Make_Cert` it performs, and "the
     largest cap ever certified for a root" is read from that log, not
     from `F` (a dominated roster takes its certificate with it, so no
     view of `F` can give it); there is no `CERT` record kind;
   - the out-of-band delivery of segment tops to roots, and the ceremony
     **self-check**: before a root's first roster in a segment, it derives
     `k_s` from the top it received and opens the founding opener's link
     `{from_epoch = s}` with `Open_Link`; a top that opens no link is
     refused, so a wrong top fails at the ceremony and not as a silent
     member split;
   - the rule for new segments (only the founding key opens one, §6), and
     the top-leaked procedure (a new segment with no `REVOKE`, §6);
   - the recovery procedure (§6), in its order: re-issues first, the
     root-void fourth, the roster last;
   - **enrollment**: a member's `(sign_pk, dh_pk)` reaches the root out of
     band, and Kome cannot authenticate it (a substituted `dh_pk` gets read
     and gate access). The two parties compare a short authentication
     string, or a QR code, over `BLAKE2b-256("kome/member" ‖ ns ‖ sign_pk
     ‖ dh_pk)` before the root lists the entry. The join hand-off to the
     new device is `(root_pk, salt, the frame of the roster that lists
     it)` (§6, Joining);
   - **key rotation**: a member proposes a fresh `dh_pk` (the same check),
     the next roster lists it and drops the old one, and the roots re-key
     every member on a schedule, because there is no post-compromise
     security inside the chain (§6, T14);
   - the **key API**: a signing key or `dh_sk_ns` is generated from Kome's
     own seed and is neither imported nor exported; an application that
     must bring its own key can sign only with Ed25519ph, which Kome does
     not accept on records (§2);
   - the honest-issuer rules, as follows.

   The honest-issuer rules are:
   - A root reconciles before it issues. A new roster has `gen = 1 +` the
     largest `gen` of the rosters in `F` that are not root-voided, counting
     only `gen ≤ G_honest = 2^47`. A root never emits `gen > G_honest`; if
     `1 + max` would exceed it, the root refuses with
     `STOLEN_ROOT_SUSPECTED` and waits for the founding root-void. (A
     stolen root can issue `gen = 2^48 − 2`; the founding opener wins by
     epoch, not by `gen`.) A restored root that holds its own roster with
     `gen ≥` its next `gen` issues at `1 + max`, which resolves the fork
     that `ROSTER_FORK` reports.
   - Its `ceiling_t` is at least the largest ceiling of the signer's held
     rosters, and at least its `gen` (§2 rule 2). So it dominates all of
     them, and the signer keeps one roster.
   - Its epoch is at least the largest epoch of the rosters in `F` that are
     not root-voided, within the current segment, and never above the top
     of the segment. A certified root that holds a founding roster at an
     epoch above its known segment refuses to issue until it has the new
     top.
   - Re-key on divergence (§6): if `F` holds a roster of another signer,
     not root-voided, at `ROSTER_eff.epoch`, that lists a `(sign_pk,
     dh_pk)` which `ROSTER_eff` does not list, the next roster is at
     `ROSTER_eff.epoch + 1`.
   - Rivals (§6): if `rivals(F)` is not empty and every rival is at
     `ROSTER_eff.epoch`, the next roster has `gen + 1` and the union of
     the rivals' members and `ROSTER_eff`'s.
   - A roster at epoch `e` lists a superset of `ROSTER_eff`'s members at
     `e` (a removal takes a new epoch), and a sixty-fifth member is
     refused: `Members_Max` = 64 is the number of devices that can pass
     the gate of a collection, and the issuer tells the owner rather than
     silently drop an entry.
   - A root stays within its slice (`Slice_Max` records), and the founding
     key certifies at most 15 distinct signer keys (`Signers_Max − 1`,
     A1). Renewals of a certified key's cap are unlimited and take no
     slot; a renewal is a certificate, not a record.
   - The founding key keeps a *reserve* for root-voids: it signs an
     authorization record other than a root-void only if
     `slot_count(1) + 1 ≤ slice − (15 − roots_already_voided)`. It does no
     routine `GRANT`s or `REVOKE`s (E1).
   - An issuer emits `REVOKE(s, from_t)` only if `F` holds no `REVOKE` of
     `s` by that issuer with a `from_t` at or below the new one (§6): a
     `REVOKE` is never dominated, so every one costs a slice entry for
     the life of the collection.
   - `from_t` is a point on the `t` axis (§6, E4). For a lost key it is
     `maxceil(F) + 1` at issue time; for a stolen key it is 0.
   - A certified root's `ceiling_t` and `cert_cap` are at most
     `now + Cap_Lead` (§7: `Cap_Lead` is 3 days, below `Del_TTL_Min`), so
     that `maxceil − now ≤ Cap_Lead` whenever every root is honest. A
     longer `cert_cap` is a trade: fewer ceremonies against a wider window
     for a stolen root. No receiver-side rule can bound the founding key's
     own ceiling (a relative-climb rule would make a late joiner with
     `maxceil = 0` discard the only surviving roster for good), so the
     bound is an issuer rule for the founding key too: never a
     `ceiling_t` or `cert_cap` within `2^47` of `2^48 − 1`. The view
     `ceiling_lead = maxceil − now_local` (§3) reports a status when it
     passes a bound, so that a device can see a ceiling that runs ahead.
   - A recovery roster (§6 step 5), and any founding roster issued while
     `maxceil(F) > now`, has `ceiling_t = max(intended, maxceil(F) + 1)`.
   - A founding roster issued in a recovery carries `del_ttl ≥` the
     `del_ttl_eff` computed before the ceremony's `REVOKE`s, with the
     voided root still counted (§6 step 5).
   - A member removal increases the epoch.
   - After an epoch change from `e` to `e'`, a replica sends, for a set
     period, an authorization-only bundle under `k_e` with the new roster
     and the `REVOKE`s before it (§6), so that store-and-forward replicas
     can cross the change.
4. **Conflict visibility.** This design keeps one value per cell and frees
   the losers' bytes. If an application wants visible conflicts, it
   gets them through the typed-fields extension (C10: the `MVREG` type plus
   parent hashes). It does not need a different lattice. The one
   cross-cell case that the core shows the application is the partial
   entity (§3): a `DEL` of an entity concurrent with a `PUT` of one of
   its fields leaves that field live and the others `None`, at every
   replica alike. An application that treats entities as wholes checks
   its required fields on read and completes or deletes the remainder;
   one that wants the concurrent write kept uses an `MVREG` cell.
5. **Quotas.** Only revocation (under A7), owner `DEL`s and the data
   capacity set a limit on floods by an authorized writer. The design does
   not adopt a per-author quota at the room step (E8). Such a quota is a
   capacity refusal. So under a flood, replicas disagree about which
   data records on new cells they hold, the flooder's and the honest ones
   alike: with equal capacities, one replica holds an honest `PUT` and
   refuses a flood record, while another refuses the honest `PUT`. The
   transport reports a `NO_SPACE` refusal of a peer-offered record as a
   replica status, so that the disagreement is visible (§7). A flood of
   `DEL`s is not freed by the `REVOKE` and the owner's `DEL`s: a `DEL` is
   dominated only by a higher `DEL`, so the flooded entities hold capacity
   until `min(now, maxceil) ≥ t_flood + del_ttl_eff`. The purge of a
   revoked writer is entity-grained (§6): its own entities are deleted,
   and its junk fields on honest entities are overwritten with empty
   `PUT`s. The quota protects honest room but makes no guarantee stronger,
   and the correct bound depends on the application. A per-author byte
   quota in the roster, enforced by the application, would not touch the
   lattice.
6. **The C ABI.** It is not designed yet. The packages give its shape:
   `set/get/exists/scan` over records, `delete(ns, ent)` (the only
   removal, entity-grained, §2), `GRANT`, `REVOKE` and roster operations,
   `session_*` over Kome.Reconcile, and a digest whose value is equal to
   the sync fingerprint. There is no field-level delete; an item that must
   be removable on its own is its own entity. Statuses are Kome's
   `Status`, including `AUTH_FULL`, `LOG_FULL`, `SEQ_CORRUPT` (§5) and,
   from the storage binding, `DEGRADED` (§7). `CLONE_SUSPECTED`, `CLAMPED` and
   `BORN_EXPIRED` are out flags next to a write's status (§5).
   `Ceiling_Stale` and `Horizon_Frozen` are replica statuses (§7), as is
   a `NO_SPACE` refusal of a peer-offered record. The key API generates
   keys and never imports or exports one (§10.3).
7. **Typed fields.** The extension (C10) composes with the core. Build it
   when an application asks for counters or sets in the engine. Its
   lattice rule is in §4: a typed record kills another only with the
   same author, a greater version and a state that contains the other's;
   an author's non-inflationary states leave an antichain that the view
   joins and that counts against the data capacity; a `DEL` of the
   entity dominates typed cells as it dominates LWW cells. T15–T17 state
   the per-author inflation obligation and are not written yet.
8. **Sketch size.** The current maximum message length sets the sketch cap
   (1 000 cells). A larger message bound gives a larger cap. Below the cap,
   the usual sync is two round trips per phase. Above the cap, the range
   protocol runs as before.
9. **Interoperability residue.** Kome never encodes a record's frame again,
   so a second implementation can check Kome records with BLAKE2b and an
   Ed25519 verifier that computes exactly the **cofactored verification
   equation** of §2: canonical `A` and `R`, `A` not small-order, `S < L`,
   and `[8][S]B = [8]R + [8][k]A`. "RFC 8032" alone is not enough: the RFC
   permits both the cofactored and the cofactorless equation, and the two
   disagree on signatures that a malicious author can make (an `R` with a
   torsion component), so two replicas with different verifiers would
   never converge on such a record. The Wycheproof and torsion vectors in
   `spark/vectors/crypto.txt` are the normative test of a verifier. The
   accumulator's byte order (§8) is the other place where a second
   implementation must be careful.

10. **Two log decisions made in the SPARK store.**
    - (a) Capacities: the slice is the constant `Slice_Max` at every
      replica, and the `HEADER`'s `slice` field is a check, not a
      parameter. The data capacity in force is a parameter of the open,
      kept outside the log or appended as a `CAPS` entry, so nothing in
      the log is ever rewritten in place, and a reopen with a smaller
      `data_cap` is allowed whenever the replayed `F` fits in it
      (`No_Space` otherwise, with nothing written). The slice therefore
      never appears in T4's scope: no two replicas can disagree about
      it.
    - (b) Compaction: `Compact` omits the trailing `EXPIRE(horizon)` only
      when the old log is exactly the `HEADER` plus one held `APPLY` per
      record of `F`, with no other entry and fewer than 7 bytes to spare.
      Every other entry is at least 7 bytes long, so in every other case
      the room for the `EXPIRE` is there. That one case is the full-log state of §7: a log whose
      `Log_Cap` is below `Log_Fits`, with every record held, where
      compaction frees nothing. The reopened replica then has a lower
      horizon, and T18 allows this.
