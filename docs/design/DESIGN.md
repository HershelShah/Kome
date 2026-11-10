# Kome: the frontier store

Kome is built on a single lattice. This lattice is the *frontier* of a set
of signed records under one strict total order. No policy question
(authorization, far-future clocks, revocation) is part of the merge. Each
policy question is either a monotone admission rule or a pure view. §1 gives
the decisions, §2–§8 give the design, §9 gives the theorems, and §10 gives
the open items. `SIMPLIFY.md` records the simplification (S1 to S24) that
brought the design to its present form; this document describes the design
as the SPARK code builds it.

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
| C3 | Tombstones use apply-then-expire, not refuse-on-arrival. The store holds a `DEL`, and the `DEL` dominates. Only expiry at the horizon `hz(F)` removes it (§7). |
| C4 | Cross-author `DEL`s dominate in the store, so deletion is durable and needs no membership knowledge (§3). |
| C5 | A device adopts no clock from a peer, and a record never changes the device's clock. A writer's clock affects only that writer's records, with one bounded exception: a write *chases* the floor of its cell (§5), so a cell that another writer pinned ahead raises the `t` of later writes on that cell, by at most `maxceil − now`. Adoption is per cell, through chase, never device-global (the H8 "Clock ahead" row in §5 and the chased-tombstone residual in §7). |
| C6 | Revocation carries a `from_t` and is a view, not a gate. It voids records in the views and never feeds admission (§3, §6). |
| C7 | Read control uses one fresh collection key per roster generation, boxed to each member of that roster (§6). |
| C8 | Reconciliation is a range split over the element keys (§8). A one-message IBLT sketch before it is an optional extension (§10.8). |
| C9 | There are several root keys, and the founding key certifies them. So the loss of a root is recoverable. There are no per-field writer rules (§6). |
| C10 | Typed fields (counters, sets, multi-value registers per `(cell, author)`) are a specified extension. Build them only when an application needs them. They need `W`, a saturating fold, and a cursor to read the view output (§4). |

### 1.2 Authorization, storage and wire

| # | Decision |
|---|---|
| D1 | Every authorization record carries a *signer block*. The signer is a root: the founding key or a key that the founding key certified, with `cert_sig` over `BLAKE2b-256("kome/root" ‖ cid ‖ signer ‖ u48(cert_cap))`. The founding key certifies itself once, with `cert_cap = 2^48 − 1`, so every signer is checked the same way. Only the founding key certifies, so only the founding key adds roots. Admission depends only on the bytes and the collection's `cid` (§2, §6). |
| D1′ | A record kind `GRANT(subject)` holds write access. Its key is `(issuer, subject)`, and it carries a *write cap*: its issuer's `cert_cap` (`2^48 − 1` for the founding key). `W(F)` is the set of `GRANT` subjects in `F`, and `wcap(F, k)` is the largest cap of the `GRANT`s of `k` in `F`. `maxceil(F)` is the largest `ceiling_t` of the rosters in `F`. A roster leaves `F` only under a roster of the same signer with a ceiling at least equal to its own; a `GRANT` leaves `F` only under a `GRANT` of the same issuer and subject with a cap at least equal to its own. The three are views of `F` (`Kome.Frontier.Max_Ceil`, `In_W`, `W_Cap`), not stored registers, and they never shrink (§3, §4). |
| D2 | Only the founding key root-voids. The store ignores `from_t` for a root-void. Nobody can revoke the founding key. When a root is root-voided, all that it issued (rosters, `REVOKE`s, `GRANT`s) no longer counts in any view. Keys that only that root granted read `void` through the effective-writer view `W_eff` (§3, §6). |
| D3 | Canonical form is a property of `Header`. Decode produces it, and the lattice requires it. A roster dominates another roster of its signer if and only if its `gen` is *strictly* greater *and* its `ceiling_t` is not lower (a product order). `h` never decides between two rosters of one signer: at equal `gen`, both stay, and the view `contested` reports them. `ROSTER_eff` is the maximum of the roster key `(gen, h, signer, ceiling_t)` over the rosters whose signer is not root-voided (§3). |
| D4 | Signatures are RFC 8032 Ed25519 (with SHA-512 inside the signature). They come from the `monocypher-ed25519` part of monocypher. Tests check them against RFC 8032 and Wycheproof vectors. BLAKE2b is the hash for all values that Kome derives (§2, A1). |
| D5 | There is no root X25519 key and no epoch. Each `ROSTER` carries a fresh collection key `k_g` for its `gen`, `k_g = Hedge(issuer_sk, "kome/key", cid ‖ u48(gen), rnd)`, boxed to each member, and its own `box_pk`, which the roster signature covers. `box_pk` is the X25519 public key of `eph_sk = f(k_g, "kome/eph" ‖ cid ‖ u48(gen) ‖ signer)`, which `Kome.Epochs` computes from `k_g`: no caller draws it. `Kome.Roster.Build` (phase 8) seals the roster's boxes with it and wipes it (§2, §6). |
| D6 | Every key derivation is keyed BLAKE2b-256 in one style, `f(key, label ‖ context)`. `wrap_key = f(X25519(eph_sk, dh_pk), "kome/wrap" ‖ box_pk ‖ dh_pk ‖ sign_pk ‖ cid ‖ u48(gen))`. The box nonce is synthetic, `f(k_g, "kome/box" ‖ dh_pk)[0:24]`; the member calculates it again from the opened key and checks it. The bundle key is `f(k_g, "kome/bundle")`, and bundle nonces are also synthetic (§6, T14). |
| D7 | The accumulator is little-endian and recorded exactly: `acc(e)` is eight BLAKE2b-512 outputs, a 4096-bit integer. The tags are bytes (§8). |
| D8 | The write path selects `(t, seq)` without `h`, and then it calculates the hash. The result does not depend on `h`. `seq_self` is per collection (§5). |
| D9 | Kome persists `F` and `seq_self`, both in the log, and nothing else (§5, §7). The log is a `HEADER` (`"KOME"`, the version, `root_pk`, `salt`, `del_ttl`) and a journal of `APPLY` and `SEQ` entries. There is no expiry entry: the horizon is a function of `F`, and replay reruns `Put_Frame`. Compaction writes one `APPLY` per held record in row order (the authorization rows first) and one `SEQ(seq_self)`; the binding runs it whenever `Compact_Due` holds (more than `2·|F| + 64` entries) and no session pins the log. Replay gives the same frontier as a set (T18, §7). The log is plaintext; the host owns its integrity and confidentiality at rest (§7). |
| D10 | Expiry is a function of `F`: the horizon is `hz(F) = maxceil(F) − del_ttl` when `maxceil(F) ≥ del_ttl`, and there is none otherwise. `del_ttl` is fixed at founding: a u48 in the log `HEADER` and in the `cid`, in `[Del_TTL_Min, Del_TTL_Max]`. No record carries it, so no root, stolen or honest, can make tombstone life shorter or longer. `Put_Frame` expires in the same call when a record raises `maxceil`; no local clock is read (§7). |
| D11 | The order of checks is admission, duplicate, domination, expiry on arrival, room. A dominated record never needs room. No refusal changes anything (§7). |
| D12 | `Value_Max` = 40 960, so every frame fits in one 48 KiB message (§2, §8). |
| D13 | No register value goes on the wire, so no assumption about register values on the wire is needed. There is no pre-gate message: the Noise XK prologue `"kome/1" ‖ ns ‖ 01` binds the collection and the protocol version. The post-gate `HELLO` carries counts, the digest and the sender's credential roster. That roster must list the sender's Noise key, and its signer must not be root-voided at the receiver. The credential is also how a recovery roster reaches a captured replica (§6). A side sends `HELLO` only to a peer that it has already admitted. The authorization range is fully reconciled before the data range (§6, §8). |
| D14 | The session phases are `Gate`, `Auth`, `Data` and `Done`. Only the initiator sends `ROOT` messages: exactly two, whose bounds the phase fixes. A reply tiles the range that it answers. One ordering rule serves every batch (a reply, a bundle, an import, a compacted log): apply in element-key order, which puts the authorization records (tags 0, 1, 2) before the data records, and the `ROSTER`s before the `REVOKE`s (§8). |
| D15 | Prefix sums carry one more entry, the total. Any sub-range costs at most 64 additions and one subtraction, with the two-accumulator scheme (§8). |
| E1 | Data records have one capacity. Each signer has its own *slice* of authorization capacity, and the founding key's slice is reserved. The capacity of `W` is the total of the slices, so `W` never fills on its own. A data flood cannot fill another party's space, and a stolen root cannot either. Log bytes are a fourth class, shared by every record: the binding keeps `Log_Fits` (§7), so that a compacted log always has room for one more entry. The founding key keeps a *reserve* of 15 entries in its slice for root-voids (§10.3). Under these two duties, the founding key's `REVOKE` always lands (§7). |
| E2 | If an authorization record would exceed its signer's slice, the store refuses it with `AUTH_FULL` and changes nothing. If a record that `F` can hold does not fit the log, the store refuses it with `LOG_FULL`, and the binding compacts and retries. The store never drops a key silently (§7). |
| E3 | There is no hash chain and no segment. Every roster generation has its own key, drawn by its issuer, so a key never derives another, and a member that a roster leaves out gets no box of that roster's key (§6; this resolves AUDIT.md A7 differently, `SIMPLIFY.md` S4). |
| E4 | `from_t` gives protection only against a lost key, not against a key that a thief uses. For a stolen key, revoke from 0 (§6). |
| E5 | Keys are checked at decode: `box_pk`/`dh_pk` are reduced, not low-order and not the all-zero encoding, and `box_pk` is not `X25519_Public(0^32)`; `root_pk`, `signer`, a `GRANT`'s `subject`, a `REVOKE`'s `sign_pk` and every roster member's `sign_pk` are canonical, not small-order and not the key of the all-zero seed (`Sign_Key_OK`); the signature check makes a data record's `author` canonical and not small-order; every signer's certificate verifies under `root_pk`, the founding key's own included. Each record has one encoding (§2). That every listed member can open its box is not a decode check: `Kome.Roster.Build` makes it true by construction, because it derives `box_pk` from the secret that sealed the boxes (§6). |
| E6 | No frame carries `root_pk`, `salt` or `ns`. The verifier supplies the collection's `cid` and `root_pk` (from the store, the session or the bundle), and a record of another collection does not verify, because its `h` binds another `cid`. The effective certificate cap is the largest cap ever certified (§6). |
| E7 | Admission does not refuse the records of a revoked key. Instead, the design bounds a revoked key's reach with the write cap (`t ≤ wcap`, §4), states assumption A7 (no replica receives, from any source, a record that a revoked subject signed after its revocation), and makes the H8 bounds depend on A7. A refusal would give a stolen root a permanent primitive for mass deletion, and it would give up T3 (§6, §9). |
| E8 | The engine has no per-author data quota. A quota refusal is a capacity refusal, and under a flood the replicas would not agree about it. It stays an application policy (§10.5). |
| E9 | The frontier keeps one data row and one authorization row per signer slot. Its discriminant sets the data capacity, and the slice is the constant `Slice_Max`. Each held record carries an opaque 64-bit tag that the lattice ignores and the store uses to find its frame in the log (§7). |

## 2. Objects

**Identifiers.** A collection is fixed at founding by three values: its
**founding key** `root_pk`, a 16-byte `salt` and the tombstone lifetime
`del_ttl` (a u48 in milliseconds, in [`Del_TTL_Min`, `Del_TTL_Max`] = [7
days, 3 650 days], §7). Its **context** is the 32-byte hash `cid =
BLAKE2b-256(root_pk ‖ salt ‖ u48(del_ttl))` (`Kome.Records.Cid_Of`), and
`ns = cid[0:16]` (`NS_Of`) is its routing identifier: the Noise prologue,
the bundle header and file names carry `ns`, and nothing else does. The
`h` of every record binds the `cid` (Records below). So a different
`del_ttl` is a different collection. An entity `ent` is 16 bytes. A field name is 1–32 bytes.
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

**Records.** A frame is `tag:u8 ‖ content ‖ sig[64]`. For every kind,
`h = BLAKE2b-256(tag ‖ cid ‖ content)`. The `cid` is *implicit context*:
no frame carries `ns`, `root_pk` or `salt`, and the verifier supplies the
`cid` (and, for an authorization record, `root_pk`) from the store, the
session or the bundle. So every function that reads `h` takes the `cid`
as its first parameter: `Kome.Records.Hash`, `To_Header`, `Well_Formed`,
`Decode_Verified`, `Sign` and the `Make_*` constructors; `Parse`,
`Decode` and `Encode` do not. A record of another collection does not
verify under this collection's `cid`, even when the two `ns` collide
(about 2^64 work), because its `h` binds the other `cid`. `Kome.Store`
computes its `cid` once and passes it (§7). `sig` is an Ed25519 signature
(RFC 8032) by the record's signer over the 32 bytes of `h`, so every
signature binds the `cid`. The verification predicate is normative
(§10.9): a signature `R ‖ S` under the public key `A` over the message `m`
is valid if and only if `A` and `R` are canonical point encodings (each
decodes to a point, with the `y` coordinate below `p`), `A` is not one of
the eight small-order encodings, `S < L`, and `[8][S]B = [8]R + [8][k]A`
with `k = SHA-512(R ‖ A ‖ m) mod L`. This is the cofactored equation.
`Kome.Crypto.Verify` is this predicate as a SPARK expression, and nothing
else: `S_Below_L(sig) ∧ Is_Canonical_Point(R) ∧ Is_Canonical_Point(A) ∧
¬Is_Small_Order_Point(A) ∧ Raw_Ed25519_Check(sig, A, m)`. The first four
are byte comparisons that gnatprove proves. The group equation is the
private `Raw_Ed25519_Check` over monocypher, which has no Post. It is
assumed (A1), and so are two binding axioms of the same kind,
`Kome.Crypto.Lemma_Blake2b_Congruent` and
`Kome.Crypto.Lemma_X25519_Congruent` (BLAKE2b and X25519 read only the
bytes of their input); a test under `-gnata` checks each one. The
Wycheproof and torsion vectors in `spark/vectors/crypto.txt` are normative:
an implementation that accepts or refuses one of them differently does not
interoperate. At decode, `root_pk` (as the verifier supplies it), the
signer of an authorization record, the subject of a `GRANT` or a `REVOKE`
(`sign_pk`) and every member `sign_pk` of a `ROSTER` must pass
`Kome.Records.Sign_Key_OK`: a canonical point encoding
(`Is_Canonical_Point`), not one of the eight small-order encodings
(`Is_Small_Order_Point`) and not `Derive_Public(0^32)`, the public key of
the all-zero seed. The author of a data record is also canonical and not
small-order, because a signature verifies under it. (The all-zero key is
an order-4 point: a `GRANT` to it would let anybody who can deliver
frames forge data under it.) The constructors require the same of their
inputs: `Make_Roster` requires `Sign_Key_OK` of the signer, `Make_Revoke`
and `Make_Grant` also of the subject, `Make_Cert` of the signer, `Cert_OK`
of `root_pk` and the signer, `Key_Pair` refuses the all-zero seed, and
`Kome.Store.Open` requires `Sign_Key_OK` of the founding key. Kome signs
the bare 32-byte `h`, so a device key serves Kome and nothing else: the
key API generates each key from Kome's own seed, and it neither imports
nor exports a signing key (§10.3, §10.6). A key that an application must
import can only sign with Ed25519ph, a different signature that Kome does
not accept on records. All integers are big-endian. All tags and labels in
this document are ASCII bytes without a terminator. These are the five
layouts, exactly as `Kome.Records` encodes them:

```
tag 0  ROSTER  SIGNER box_pk[32] gen:u48 ceiling_t:u48
               n_members:u8 (≤ 64) members[n_members] { sign_pk[32] dh_pk[32] nonce[24] box[48] }
tag 1  REVOKE  SIGNER sign_pk[32] from_t:u48
tag 2  GRANT   SIGNER subject[32]
tag 3  DEL     ent[16] t:u48 seq:u48 author[32]
tag 4  PUT     ent[16] flen:u8 field[flen] t:u48 seq:u48 author[32] vlen:u16 value[vlen]

SIGNER = signer[32] cert_cap:u48 cert_sig[64]
h      = BLAKE2b-256(tag ‖ cid ‖ content)          for every kind
cid    = BLAKE2b-256(root_pk ‖ salt ‖ u48(del_ttl)),   ns = cid[0:16]
```

A member's `box` holds the roster's collection key `k_g` (§6).

| Kind | Content offsets (the tag is byte 0) | Frame bytes |
|---|---|---|
| ROSTER | signer 1, cert_cap 33, cert_sig 39, box_pk 103, gen 135, ceiling_t 141, n_members 147, members 148 | 212 + 136·n_members, at most 8 916 |
| REVOKE | signer 1, cert_cap 33, cert_sig 39, sign_pk 103, from_t 135 | 205 |
| GRANT | signer 1, cert_cap 33, cert_sig 39, subject 103 | 199 |
| DEL | ent 1, t 17, seq 23, author 29 | 125 |
| PUT | ent 1, flen 17, field 18, t 18 + flen, seq 24 + flen, author 30 + flen, vlen 62 + flen, value 64 + flen | 128 + flen + vlen, from 129 to 41 120 |

The largest frame, `Frame_Max`, is 41 120 bytes (a `PUT` with a 32-byte
field and a 40 960-byte value). The signature follows the content.
`author` signs `PUT` and `DEL`. `signer` signs `ROSTER`, `REVOKE` and
`GRANT`.

**The signer block and root certificates (D1).** An authorization record
names its signer, and its bytes prove that the signer is a root. Every
signer block carries `cert_sig`, the founding key's signature over
`BLAKE2b-256("kome/root" ‖ cid ‖ signer ‖ u48(cert_cap))`
(`Kome.Records.Cert_Hash`; the signature covers the 32-byte hash, as a
record signature covers `h`). The founding key certifies itself once,
with `cert_cap = 2^48 − 1` (`Founding_Cap`), and every record that it
signs carries that certificate; any other signer is a **certified root**.
There is no zero-certificate case and no sentinel: `Cert_OK (cid,
root_pk, signer, cert_cap, cert_sig)` checks every signer the same way. A
roster's `ceiling_t` is at most its `cert_cap`.

Only the founding key can make a certificate, so only the founding key adds
roots. A `GRANT` carries no cap of its own: its write cap (§3, §4) is its
issuer's `cert_cap` (`2^48 − 1` for the founding key). So a
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

**Well-formed** is a function of the bytes and of the `(cid, root_pk)`
that the verifier supplies. A frame is well-formed if and only if all
these conditions are true:

1. Its length is exactly the layout's length, `flen` ∈ 1..32,
   `vlen` ≤ 40 960, and `n_members` ≤ 64.
2. For `ROSTER`, `REVOKE`, `GRANT`: the signer block is valid as above
   (`Cert_OK`), and a `ROSTER` has `ceiling_t ≤ cert_cap` and `gen ≤
   ceiling_t`. (`ceiling_t` is a millisecond clock, so an honest `gen` is
   always far below it. The bound is byte-local, and for a certified root
   it caps `gen` at its `cert_cap`, so a stolen root cannot use up the
   `gen` space above 2^47: see §10.3.)
3. For `ROSTER`: `box_pk` and every member `dh_pk` are reduced X25519
   encodings (`u < 2^255 − 19`, bit 255 clear). None of them is one of the
   five reduced low-order encodings (0, 1, `p − 1`, and the two points of
   order 8), and `box_pk` is not `X25519_Public(0^32)`, the public key of
   the all-zero secret. (That every listed member can open its box is a
   property of how `Kome.Roster.Build` makes the roster, E5, not a decode
   check: no bytes of the frame can show it.)
4. For `REVOKE`: `sign_pk ≠ root_pk` (nobody can revoke the founding key).
   For `GRANT`, `REVOKE` and `ROSTER`: `signer` and `root_pk`, the
   `subject` of a `GRANT`, the `sign_pk` of a `REVOKE` and every member
   `sign_pk` of a `ROSTER` are canonical point encodings, not
   small-order and not `Derive_Public(0^32)`, the public key of the
   all-zero seed (`Sign_Key_OK`). So each subject and member key has one
   encoding, and a `REVOKE` or a member entry never names a key that
   could not sign a record that verifies.
5. The signature over `h` (with the supplied `cid`) is valid, under the
   predicate above, under the signer (authorization kinds) or the author
   (data kinds).

Decode does not check `del_ttl`: it is inside the `cid`, and
`Kome.Store` checks the `HEADER`'s value against its range (§7).

Each well-formed record has exactly one encoding (unused buffer bytes are
zero in every in-memory representation). So `h` is a function of the
record and of the `cid`, and under A2 it is injective on records.

**Why these five kinds.** `PUT` and `DEL` are the data. `ROSTER` carries
read access (the member boxes of its key `k_g`), the session gate and one
replicated parameter, `ceiling_t`. `GRANT` carries write
access. Its subject can be the author of `PUT`s and `DEL`s. The grant counts
in the effective-writer view only while its issuer is not root-voided (§3).

`GRANT` is separate from `ROSTER` because write access must be grow-only and
a function of the frontier. Roster membership is neither: a later roster
drops members, and dominated rosters leave the frontier. `REVOKE` is
separate from both because its effect must be grow-only: a `REVOKE` leaves
`F` only under a `REVOKE` of the same issuer and subject that voids at
least as much (§3). A later roster must never undo a revocation. If it
could, a root restored from backup could issue a roster that drops a
revocation.

## 3. The lattice

Let `H` be a set of well-formed records of one collection. **Domination**
is:

```
dom(p, H) for PUT p    := ∃ q ∈ H : PUT, cell(q) = cell(p), q.v > p.v
                        ∨ ∃ d ∈ H : DEL, entity(d) = entity(p), d.v > p.v
dom(d, H) for DEL d    := ∃ d' ∈ H : DEL, entity(d') = entity(d), d'.v > d.v
dom(r, H) for ROSTER r := ∃ r' ∈ H : ROSTER, same signer,
                            r'.gen > r.gen ∧ r'.ceiling_t ≥ r.ceiling_t
dom(g, H) for GRANT g  := ∃ g' ∈ H : GRANT, same issuer, same subject,
                            g'.cap ≥ g.cap ∧ g'.h > g.h
dom(x, H) for REVOKE x := ∃ x' ∈ H : REVOKE, same issuer, same subject,
                            x'.from_t < x.from_t ∨ (x'.from_t = x.from_t ∧ x'.h > x.h)
F(H) := { x ∈ H | ¬ dom(x, H) }
```

There is no cross-kind clause other than `DEL` over `PUT`: no
authorization record dominates a data record, no data record dominates an
authorization record, and a `REVOKE` dominates only `REVOKE`s of its own
`(issuer, subject)` (T2′). Each kind carries its identity in one version,
and each clause compares records on one key:

| Kind | `v` | key on which `dom` compares | order on the key |
|---|---|---|---|
| PUT | `(t, author, seq, h)` | cell `(ent, field)`; also a DEL of its entity | `v` |
| DEL | `(t, author, seq, h)` | entity `ent` | `v` |
| ROSTER | `(ceiling_t, signer, gen, h)` | signer | product of `gen` (strict) and `ceiling_t` |
| GRANT | `(cap, subject, 0, h)` | `(issuer, subject)` | product of `cap` and `h` |
| REVOKE | `(from_t, subject, 0, h)` | `(issuer, subject)` | lower `from_t` first, then greater `h` |

The data, roster and grant clauses imply that the dominator's version is
greater (`Kome.Headers.Lemma_Roster_Dom`, `Lemma_Grant_Dom`). The `REVOKE`
clause runs the other way on `from_t`: of the `REVOKE`s of one key, the
frontier keeps the one with the least `from_t` (and, at equal `from_t`,
the greatest `h`; `Kome.Headers.Revoke_Lt`). Every authorization clause
implies the same issuer, so a dominator is in the same capacity row as
the record that it dominates.

The roster clause is a product order (D3). Suppose that the order put the
roster ceiling first. Then a stale roster with an old `gen` and a current
clock could evict the newer roster permanently. (A root restored from backup,
or a second device that holds the same root key, can make such a roster.)
This would roll back a member removal. Under the product order,
neither roster dominates, and both stay until the root issues a new roster
above both.

The clause is strict in `gen` for the same reason. A restored root issues
`gen = 1 +` the largest `gen` that it holds, which can be the `gen` of the
roster that the live device issued after the backup. If `h` decided
domination between the two, the stale roster would evict the newer one, at
every replica, with probability one half, and the removal would be lost
for good. So at equal `gen` neither roster dominates. Both stay, and the
view `contested` reports them. `ROSTER_eff` takes the one with the
greater `h`, which can be the stale one: until the root reconciles and
issues a roster above both (§10.3), a removal that only the newer roster
made can be undone at the gate. That window is the residue of a backup
restore, and `contested` makes it visible.

The `REVOKE` clause (`SIMPLIFY.md` S5) never loses what a view reads.
Every view of a revocation reads "some counting `REVOKE` of `k` with
`from_t ≤ t`" (`revoked_at` below), and the least `from_t` of each
`(issuer, subject)` decides that; so domination changes no view (Lean
`isMinFrom_F`). It also bounds the slice: a frontier holds at most one
`REVOKE` per `(issuer, subject)`, so a repeated revocation costs no
entry. A `REVOKE` with a higher `from_t` than the held one is dominated on
arrival, and one with a lower `from_t` replaces it.

The product orders and the `REVOKE` order are strict partial orders, and
they are monotone. So T2, T2′ and T3 hold exactly as for a total order.
Read the governing rule of §1 like this. Every kill predicate is a down-set
of a strict partial order on its key: for data and rosters and grants the
version order extends that partial order, and for `REVOKE` it is the
order `Revoke_Lt` of its own key.

The fields of the lattice header that a kind does not use are zero. The
header is `(Kind, Ent, FH, V, Issuer)` (`Kome.Headers.Header`): no `ns`, no
epoch and no `del_ttl`. A roster header carries its issuer (= signer).
`REVOKE` and `GRANT` headers carry their issuer (the signer). This is the
**canonical** header (D3). Decode produces only canonical headers, and the
lattice accepts no other headers.

A frontier holds at most one `REVOKE` per `(issuer, subject)`, and one
`GRANT` per `(issuer, subject)` while the issuer's cap does not change
(a renewed, larger cap can leave an antichain of two). It holds a
per-signer *antichain* of rosters. An honest signer keeps this antichain at
one roster (§10.3), and a signer that misbehaves can make it larger only within
its capacity slice (§7). Every dominator stays in the same capacity row as
the record that it dominates. Data dominates only data. Only a record with
the same issuer dominates an authorization record.

`F(H)` is the **frontier**, and it is the state. `dom` is monotone in `H`
(T2) and *upward-closed*: a dominator of a dominator of `x` dominates `x`
(T2'). The convergence proof needs this lemma, and it holds for every kind
above. For this reason, a `REVOKE` must not dominate records of another
kind. (A revocation that dominated a writer's `PUT` would not dominate the
records that this `PUT` already dominated; see §6.) From T2 and T2':

```
F(H₁ ∪ H₂) = F(F(H₁) ∪ F(H₂))        (T3)
```

So a replica can drop a record immediately when it is dominated. This is
true on any subset of replicas and at any time, and no future frontier
changes. That one equation is all of the garbage collection (GC) design for
values. The values of a deleted entity are freed at each replica that a
`DEL` reaches, with no membership knowledge and no clock.

**Views** are pure functions of `F` (and of the collection's constant
`root_pk`; `Kome.Views`, and `Kome.Frontier` for the three admission
views):

```
deleted_at(ent)     := max { d.v | d ∈ F, DEL on ent }                     -- Option
cell(ent, f)        := the unique PUT in F on (ent, f)                      -- Option
exists(ent)         := ∃ f. cell(ent, f) ≠ None
maxceil(F)          := max { r.ceiling_t | r ∈ F, ROSTER }   (0 if none)    -- admission
W(F)                := { g.subject | g ∈ F, GRANT }                         -- admission
wcap(F, k)          := max { g.cap | g ∈ F, GRANT, g.subject = k }  (0 if none)  -- admission
root_void(k)        := k ≠ root_pk ∧ ∃ x ∈ F : REVOKE, x.subject = k, x.issuer = root_pk
W_eff(F)            := { g.subject | g ∈ F, GRANT, ¬ root_void(g.issuer) }  -- views
revoked_at(k, t)    := ∃ x ∈ F : REVOKE, x.subject = k, x.from_t ≤ t, ¬ root_void(x.issuer)
void(p)             := p is a PUT or a DEL ∧ (revoked_at(p.author, p.t) ∨ p.author ∉ W_eff(F))
revoked(k)          := revoked_at(k, 2^48 − 1)          -- any from_t; the gate reads it
ROSTER_eff          := the maximal ROSTER r ∈ F with ¬ root_void(r.signer), ordered by the
                       roster key (gen, h, signer, ceiling_t)                -- Option
Roster_Max          := the maximal ROSTER r ∈ F in the same order, root-voided ones included
                                                                             -- Option
contested           := ∃ r ∈ F : ROSTER, ¬ root_void(r.signer), r ≠ ROSTER_eff,
                         r.gen = ROSTER_eff.gen                              -- advisory
quarantined         := Roster_Max ≠ None ∧ root_void(Roster_Max.signer)     -- the gate reads it
```

`maxceil`, `W` and `wcap` are `Kome.Frontier.Max_Ceil`, `In_W` and
`W_Cap`; `revoked_at` is the one revocation view, and `void` and `revoked`
are two readings of it (`SIMPLIFY.md` S13, Lean `revokeVoids`). The order
of `ROSTER_eff` is Lean's `rkey`: `(gen, h)` decides, and `signer` and
`ceiling_t` only make the order total (they decide only between rosters
equal in `(gen, h)`, which A2 excludes), so `ROSTER_eff` does not depend on
the order of the held array, even without A2.

Two predicates read the local clock, so they are not functions of `F`.
They are per-replica advisory flags, and T5 does not list them:

```
far(p)              := p.t > now_local + slack
skew(now)           := now_local − maxceil(F)     -- signed (Kome.Views.Skew); a status past a bound (§10.3)
```

`W` decides admission and `W_eff` decides views. The only difference between
them is the grants of root-voided issuers. Admission cannot drop these
grants, because admission must stay monotone (§4). So the keys that these
grants name stay admissible, and the store holds their records.
But each such record reads `void`, unless an issuer that is not root-voided
also granted its author.

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
only under a roster of the same signer with a ceiling at least equal to
its own. A `GRANT` leaves `F` only under a `GRANT` of the same issuer and
subject with a cap at least equal to its own. With T2', each dominated
record has a dominator that is not dominated. Thus `maxceil(F(H)) =
maxceil(H)`, `W(F(H)) = W(H)`, `wcap(F(H), k) = wcap(H, k)` and
`W_eff(F(H)) = W_eff(H)`. The admission views of the frontier are those of
all records ever applied, and they never shrink (T4′; in SPARK,
`Kome.Frontier.Lemma_Views_Step` gives their new values after each
`Apply`).

Also, `ROSTER_eff(F(H)) = ROSTER_eff(H)`, because a roster that dominates
another roster has the same signer and a strictly greater `gen`, so it is
greater in `(gen, h)`. The same argument holds for `Roster_Max` (a paper
argument; `Kome.Views` states the uniqueness of both maxima on a
frontier, `Lemma_Roster_Eff_Unique` and `Lemma_Roster_Max_Unique`). `ROSTER_eff` is
present when `F` holds a roster that the founding key signed. The
collection's first roster is such a roster.

## 4. Admission

Kome admits every well-formed authorization record (`ROSTER`, `REVOKE`,
`GRANT`). Kome admits a `PUT` or `DEL` if and only if `t ≤ maxceil(F)`,
`author ∈ W(F)` and `t ≤ wcap(F, author)`. The three admission views are
the views of §3 (`Kome.Frontier.Max_Ceil`, `In_W`, `W_Cap`). They are
functions of the frontier, not separate state. They only grow, because
admission of authorization records is unconditional and their domination
never lowers any of them (§3).

The write cap bounds what a revoked key can still do. Without it, any
current member (a compromised read-only member, a relay) could carry the
records of a revoked key to every replica for ever, at `t = maxceil`, and
A7 could not be a deployment duty. With it, a key that a certified root
granted writes at most up to that root's cap, which the founding key keeps
short (§2, §10.3); and a key that the founding key granted is capped only by
`maxceil` (the founding key's own `cert_cap` is `2^48 − 1`). A `GRANT` by a root with a longer cap raises the subject's
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
the data records again under the joined authorization records. Every
batch of records that arrive together (a reply, a bundle, an import, a
compacted log) applies in element-key order (D14, §8). The authorization
keys (tags 0, 1, 2: `ROSTER`, `REVOKE`, `GRANT`) are below every data key
(tag 3), so this is the authorization-first pass of T4 (a)
(`auth_first`), and Kome never discards a data record that arrives in the
same batch as the grant that admits it. In a session, the phase gate (§8)
gives this order on its own.

`maxceil`, `W` and `wcap` are opaque functions over the authorization rows
of `Kome.Frontier.State`, each with a `_Def` lemma, like the other views
(`SIMPLIFY.md` S6). There is no register file and no cache in the proved
state. A binding may cache them outside the proof, as long as the cache is
equal to the views on every state. `W` holds at most one subject per held
`GRANT`, so it never fills on its own, and there is no "`W` full" refusal.

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
floor(cell)  := max(cell(ent,f).v, deleted_at(ent))           -- for DEL: max over all fields and deleted_at;
                                                              -- the zero version when the cell has no record
ceil         := min(maxceil, wcap(self))                      -- one writer's ceiling (§4)
floor_t      := floor.t                                       -- 0 for an absent floor
low          := maxceil − Cap_Lead (0 if maxceil < Cap_Lead), for PUT and DEL alike
u            := max(now_ms, low, floor_t + 1)
t_emit       := min(u, ceil)
clamped      := t_emit < max(now_ms, floor_t + 1)             -- the one advisory flag: the ceiling held the write back
seq_emit     := seq_self + 1, and above every seq of this device's records held in F;
                at 2^48 − 1 the write fails SEQ_EXHAUSTED, no record is produced
v_emit       := (t_emit, self_pk, seq_emit, h)
status       := SHADOWED if floor exists ∧ v_emit < floor   (only when t_emit = ceil) else OK
```

**The write path has three steps (D8).** `h` hashes content that contains
`t` and `seq`, so `h` cannot be an input to the step that selects them:

1. *Choose* `(t_emit, seq_emit, status)` and the flag `CLAMPED` from the
   frontier, the target cell, `now_ms`, the device key and `seq_self`
   (`Kome.Emit.Choose`). This step does not use `h`.
   The target is built by `Put_Target(ent, field)` or `Del_Target(ent)`,
   which compute the field hash themselves; a caller cannot name a
   cell that the built record does not have, so the cell that *Choose*
   looks at is the cell that *Build* writes.
2. *Build* the `PUT` or `DEL` content with that `(t, seq)`, and hash it
   under the store's `cid` (`Kome.Records.Make_Put`, `Make_Del`).
3. *Sign* and apply (`Store.Put_Frame`).

`Kome.Write.Write (S, F, Op, Ent, Field, Value, Now, SK, Rec, Result,
Clamped)` is this path in one call (`SIMPLIFY.md` S16, S17). Its outcomes:

- `OK`: the record was applied; `Rec` is its header.
- `SHADOWED`: a refusal decided in step 1, before anything is built or
  signed (`t_emit = ceil` and the floor beats the prefix of `v_emit`). No
  seq is consumed.
- `INADMISSIBLE` (the device key is not in `W`) and `SEQ_EXHAUSTED`
  (`seq_self = 2^48 − 1`, a clone alarm): the refusals of step 1.
- `NO_SPACE` and `LOG_FULL`: the refusals of `Put_Frame` for the data row
  and the log (§7). (`AUTH_FULL` is only for authorization records, and
  `DOMINATED` cannot occur: an `OK` choice is above every record that can
  dominate it, `Kome.Emit.Lemma_OK_Undominated`.)
- `MALFORMED`: the signed frame failed `Write`'s own check. `Write`
  verifies its own frame and compares the decoded header with the choice,
  because `Kome.Crypto` does not state `Verify (Sign (M))` (A1). The check
  fails only for a signing key whose signatures do not verify; with a key
  from `Key_Pair` it does not fail (tested, not proved).

Every outcome except `OK` changes nothing. `CLAMPED` is the one advisory
flag next to the status; `CLONE_SUSPECTED` is read from `Clone_View`
(below), not from the write.

`seq_self` lives in the log (§7): `Kome.Store.Seq_Self (S)` is the largest
own seq over the logged `APPLY` entries and the `SEQ` entries that
`Compact` writes, replay rebuilds it, and `Put_Frame` of an own record
raises it to the record's seq. There is no second durable file and no
persist-before-append duty. The crash case: the binding flushes the log to
`Log_Length` before it sends a frame (§8, AUDIT.md A21), so a frame lost
before its `APPLY` is durable was never sent, no peer can hold it, and the
next write may reuse its seq. Neither step refuses a large jump of `seq`:
own records leave `F` when they are dominated.

`CLAMPED` means that the ceiling `min(maxceil, wcap)` held the write
back: `t_emit` is below the clock, or not above the cell's floor:
`Is_Clamped` is `t_emit < now_ms ∨ t_emit ≤ floor_t`. The write was
back-dated to the ceiling, and it loses against any concurrent write at
the ceiling by a higher key. The floor term always exists: a cell with no
record has the zero version, so a write with `now_ms = 0` and no floor
gets `t_emit = 1`. There is no born-expired flag: every write of a
writer whose `wcap` is not below `low` lands at `t ≥ maxceil − Cap_Lead`,
and `Cap_Lead < Del_TTL_Min`, so it is above `hz(F) = maxceil − del_ttl`
(§7). (Only a writer whose cap is below the horizon can write a `DEL`
that its own store sees as expired; `Write` then reports `OK`, and the
`DEL` is applied for its effect and not held, §7 step 4.) The same bound puts every
write above each `DEL` that the device expired (`d.t ≤ hz(F) <
t_emit`), so a device whose clock was reset after an expiry never writes
the entity below the expired `DEL` (this is why there is no expire mark).
A `DEL` from a writer whose `maxceil` is stale can still arrive expired
at a replica with a fresher `maxceil` (more than `del_ttl − Cap_Lead`
ahead), which applies it for its effect and does not hold it (§7), so a
stale copy of the entity can come back. Under `CLAMPED` the caller syncs
first (so that a fresh roster lifts `maxceil`) and then writes the `DEL`.
For the same reason, the roster refresh of A3 must reach every partition
of the members, not only the partition that holds the root device.

The result of step 1 does not depend on `h`. `seq_emit` is larger than the
`seq` of each held record of this device. So `(t_emit, self_pk, seq_emit)`
is different from the prefix of each held version. Two versions with
different `(t, author, seq)` prefixes compare by the prefix alone.

Thus, for each `h`, Kome admits the record of step 2. `OK` means that no
held record dominates it. `SHADOWED` is true if and only if a held record of
the floor has a greater prefix. (The lemma `Lemma_Outcome_Independent_Of_H`
states this.) The apply step holds an `OK` write unless the store is full
(`NO_SPACE` or `LOG_FULL`, §7).

A write *chases* the cell's floor, so read-your-writes holds (T8)
unless the cell is pinned at the ceiling. A device with no real-time clock
works: all its writes chase, and expiry reads no clock (§7). `seq_self` is
the only persisted clock state, and it is in the log.

`seq_self` is **per collection**: it is the counter of `(device key,
collection)`, and the collection's log keeps it. So if a thief forces
a jump to `2^48 − 1` in one collection, only that key's counter in that
collection is exhausted. `SEQ_EXHAUSTED` is a clone alarm. The
device moves to a fresh key in that collection (a new `GRANT` and roster),
and a root revokes the old key.

**What a writer that misbehaves can do (H8).**

| Case | Effect | Bound |
|---|---|---|
| Clock ahead by δ | It wins concurrent conflicts on the cells that it writes, for δ. Those cells then resolve by chase (arrival order), not by wall time. Every later write to such a cell, by any writer, chases above the pinned `t` (C5): the adoption is per cell, and a `DEL` of the entity lives δ longer (§7, chased tombstones) | δ ≤ maxceil − now; only cells it touched; automatic |
| Clock behind | It loses concurrent conflicts; its own cells still chase. Under a stale `maxceil` (a long time offline), the clamp back-dates its writes to the ceiling, and a replica with a fresher `maxceil` can see its `DEL` as expired on arrival; `Choose` reports `CLAMPED`, and the caller syncs before it writes such a `DEL` | its cells only; a corrected clock has an effect immediately |
| Backup restore | Its restored log has an old `seq_self`, so it emits old `seq` values again: equivocation, ordered by `h`, flagged. Peers offer its later records again, and they are dominated unless the `DEL` has expired (§7) | The writer detects it: a peer's copy of its own record that changes `F` sets `CLONE_SUSPECTED` (`Kome.Write.Receive`), and `seq` jumps past every held own record |
| Cloned key | Continuous equivocation; replicas still agree | flagged; the owner issues `REVOKE(old, 0)`, a `GRANT` for a fresh key and a roster |
| Malicious | It can overwrite or delete any cell (that is what write access means). It can pin cells to `min(maxceil, wcap)`, flood entities, and grind a public key that wins ties at the ceiling. It can force its own `seq` to `2^48 − 1` in the collections where it writes | It cannot forge, and it cannot go above `maxceil` or above its `wcap`. A flood cannot block the `REVOKE` while the binding keeps `Log_Fits` and the founding key keeps its reserve (§7, E1). Under A7: nothing that the key signs after the `REVOKE` reaches any replica. So pins stop at the first roster whose ceiling exceeds the pinned `t` (not at "the next refresh": a refresh below the pin changes nothing). A flood of `DEL`s on random entities holds data capacity until it expires: the owner's purge `DEL`s are `SHADOWED` or free one record each, and the room comes back only when `maxceil ≥ t_flood + del_ttl` (§10.5). The purge is entity-grained (§6): junk fields on an honest entity are overwritten with empty `PUT`s, not deleted with the entity. Without A7: a replica that admits the key to a session, or takes its bundle, or relays what another member carried, spreads the key's later records everywhere. Each replica admits them (within `wcap`) and flags them `void`. The bytes that they overwrite or delete leave `F` at every replica, and Kome keeps no copy |
| Compromised current member (a relay, a read-only member) | It can carry the records of a revoked or root-voided key to every replica, whatever those replicas hold, because admission reads neither `REVOKE` nor `root_void` (E7) and `W` never shrinks | Each such record is admitted only within `wcap(author)` and reads `void`. The transport attributes it: when a record arrives whose author is already void in the receiver's view, it records the delivering peer's `dh_pk` and flags that peer `SUSPECT_RELAY` (§8). The owner removes the relay. This is the A7 duty stated for a member, not for a stale replica |
| Root restored from backup | It issues a roster with an old or an equal `gen`. If its own held roster has a strictly greater `gen` and a ceiling at least as high, the restored roster is dominated on arrival (status `DOMINATED`). If not (an equal `gen`, or a higher ceiling from a current clock), neither roster dominates, Kome holds both, and `ROSTER_eff` is the `(gen, h)`-maximum; at equal `gen`, `contested` reports the pair. `h` never evicts a roster of the same signer. After sync, the root issues a new roster above both. `maxceil` never decreases, and no `REVOKE` is lost | It converges in both cases; a roster with a lower `gen` never becomes effective while the newer one is held. At equal `gen`, `h` decides `ROSTER_eff` until the root issues above both, so a removal can be undone at the gate for that window, and `contested` shows it |

`CLONE_SUSPECTED` is a flag that Kome reports next to a status. It is not
a status: the write occurred. `Kome.Write.Clone_View (F, self, seq_self)`
raises it when a held record of this device has a `seq` above `seq_self`
(under `Store.Valid` this does not hold, since every own `APPLY` raises
`seq_self`), or when `F` holds two records of this device with equal
`seq` and different `h` (`Kome.Emit.Clone_Pair`): the trace of a clone that
writes at the owner's pace. It is also raised on the apply side (H18): a
record signed by the device's own key that arrives from a peer and
changes `F` (not a duplicate, not dominated, not an expired `DEL` that
drops nothing) sets it (`Kome.Write.Receive`). The caller shows
`CLONE_SUSPECTED` for either. With A5 (a frame leaves only after its
`APPLY` is durable), a crash never makes the device's own lost frame
come back from a peer, so the apply-side flag raises no false alarm.

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

**Roots (C9, D1).** A collection has one founding key (`root_pk`, which,
with `salt` and `del_ttl`, gives the `cid` and `ns`). It has at most 15
distinct certified signer keys during its life (`Signers_Max` = 16
signers in total); renewals of a key's cap are unlimited and take no
slot. Any root, founding or certified, can sign `ROSTER`, `REVOKE` and
`GRANT`. Only the founding key certifies a root (§2). A record's bytes
tell if its signer is a root, so admission of authorization records needs
no history. A replica that joins late can never refuse a `REVOKE` that
every other replica holds. Also, a roster never waits for the roster that
introduced its signer.

Roster domination is per signer (§3). The effective roster is the view
`ROSTER_eff` (§3): the `(gen, h)`-maximum over the frontier rosters whose
signer is not `root_void`. If two roots race with equal generations, `h`
resolves the race, and the loser's newcomer is shut out until a root
repairs it. Two rosters of *one* signer at equal `gen` (a backup restore,
or a second device) are the same case. The view `contested` (§3) reports
both: some roster that is not root-voided and is not `ROSTER_eff` has
`ROSTER_eff.gen`. The one response is an issuer rule: a root that sees
`contested` issues its next roster at a `gen` above every held roster,
with the confirmed union of the members (§10.3). `REVOKE`s are grow-only
in effect (§3), so no race can lose one.

A losing roster carries its own key: each roster boxes its own `k_g`
(below), so a member that only the loser lists holds a key that no
up-to-date sender uses, since every sender seals under the key of its
`ROSTER_eff` (`bundle_key(F)`, below). There is no re-key rule. Per-field
writer sets are not part of the design. If admission enforces them, they
are not monotone. If they are a view flag, they are only a label. A label
cannot stop an unauthorized write that frees the bytes of an authorized
value.

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

- Its rosters leave `ROSTER_eff` (and they still count in `Roster_Max`,
  which sets the quarantine, below).
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
5. It issues the **recovery roster**: a founding-signed roster at a `gen`
   above every held roster, root-voided ones included, with a fresh `k_g`.
   The roster leaves out every entry revoked in step 2, and keeps only the
   entries that the owner re-confirms. Its `ceiling_t` is `max(intended,
   maxceil(F) + 1)`: the founding key is uncapped, so it can lift
   `maxceil` above the largest cap that `R` ever used. Then every cell
   that `R`'s grantees pinned at that cap is writable again at once,
   instead of when wall time passes it. Every held `gen` is at most its
   roster's `ceiling_t ≤ maxceil(F)` (§2 rule 2), so `gen = maxceil(F) +
   1 ≤ ceiling_t` always beats `R`'s rosters, whatever `gen` `R` wrote.

`Kome.Roster` (phase 8) issues the steps in this order and checks steps 2,
3 and 5: after recovery, no `ROSTER_eff` member has a `sign_pk` with a
counting `REVOKE`, `ROSTER_eff.ceiling_t > maxceil` of the state before it,
and the recovery roster is `Roster_Max` and `ROSTER_eff`
(`Kome.Guard.Lemma_Quarantine_Cleared`). The founding key's slice holds
these records within its reserve (§10.3), so step 4 always fits. Keys that
`R` granted and that the owner does not recognize need no action. `W_eff`
voids them, and also each key that `R` makes later. A captured replica
learns of the recovery from any member that holds the recovery roster:
that roster reaches it as the member's `HELLO` credential, and the
`REVOKE`s follow in the authorization range (below, §8).

Within one batch the records apply in element-key order (D14), so the
recovery roster (tag 0) applies before the `REVOKE`s (tag 1) and the
`GRANT`s (tag 2), and the views and the gate are evaluated after the
batch. A session can still deliver the recovery over several batches of
its authorization range. Between two batches there is a **transient**:
the keepers that only `R` granted can read `void` until their re-issued
`GRANT`s arrive, and the members that only `R` revoked can read clean
until the re-signed revocations arrive. Each view takes either its
pre-recovery or its post-recovery value, never a third one, because
`root_void` is monotone and the re-issues are founding-signed records that
every replica admits. The transient ends when the authorization range is
complete, before the data range starts (D13).

**What a stolen certified root can do.** Until a replica holds its root
revocation, the stolen root can do there all that a root does:

- It can grant writers, who can overwrite or delete any data.
- It can make its roster `ROSTER_eff` (with `gen` up to its cap, §2 rule
  2). Then it decides who passes the session gate and which key bundles
  use, and it can lock honest members out, until a roster of a root that is
  not voided arrives at a higher `gen`.
- It can revoke members (flag them `void`).
- It can raise `maxceil` up to its effective cap.

After the founding key root-voids it, none of that counts in the views of a
replica that holds the root revocation. Under A7, nothing that
it or its grantees sign afterwards reaches that replica. The reason is that
no roster of this root counts for the gate, and no key of its rosters is
the bundle key. These effects stay permanently:

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
(A3). Also, nobody can add or root-void a root until the key is restored
from its offline backup. This is why the founding key stays cold, with an
offline backup.

**Membership is key possession (`SIMPLIFY.md` S4).** Each `ROSTER` carries
a fresh **collection key** `k_g` for its `gen` and boxes it to each
member's `dh_pk`. The issuer derives it with a hedge:

```
k_g = Hedge(issuer_sk, "kome/key", cid ‖ u48(gen), rnd)
    = f(seed(issuer_sk), "kome/key" ‖ cid ‖ u48(gen) ‖ rnd)          -- Kome.Epochs.Key_For_Gen
```

where `f(k, m)` is keyed BLAKE2b-256 (`crypto_blake2b_keyed`) with key `k`
over the message `m`, and `rnd` is 32 bytes that the caller draws. A weak
RNG alone does not reveal `k_g`, because the issuer's signing seed keys
it (AUDIT.md A6), and a repeated `rnd` at one `(cid, gen)` only repeats
`k_g`. A refresh (the same members, a new ceiling) is a new `gen` with a
new key, and so is a removal. Every key of a roster derives from its
`k_g` in the same style, `f(k_g, label ‖ context)`. The bundle key is
`bundle_key = f(k_g, "kome/bundle")` (`Kome.Epochs.Bundle_Key_Of`). Keys
of different rosters are independent: no key derives another, so a
member that a roster leaves out learns nothing about that roster's key
from the keys that it held (T14). A new member holds only the keys of
the rosters that list it; it reads the collection's history through
sessions, which carry records, not through old bundles (senders seal
under the current key, below).

The member's `dh_sk` is the member's whole capability: it opens the boxes
and it is the Noise static key. There is no post-compromise security: an
attacker who copies a member's `dh_sk` once opens that member's box in
every later roster that lists it, for as long as it stays listed, and
nothing in the rosters can show it. A member therefore rotates its
`dh_pk` from time to time (it proposes a fresh key, and the next roster
lists it and drops the old one), and the roots re-key members on a
schedule (§10.3). T14 states the premise.

**Boxes (D5, D6).** Each roster carries `box_pk`. For member `(sign_pk,
dh_pk)` of a roster of signer `signer` at `gen` in the collection `cid`
(`Kome.Epochs`):

```
eph_sk   = f(k_g, "kome/eph" ‖ cid ‖ u48(gen) ‖ signer)                       -- Eph_SK_Of
box_pk   = X25519_Public(eph_sk)                                               -- Box_PK_Of
wrap_key = f(X25519(eph_sk, dh_pk), "kome/wrap" ‖ box_pk ‖ dh_pk ‖ sign_pk ‖ cid ‖ u48(gen))
nonce    = f(k_g, "kome/box" ‖ dh_pk)[0:24]                                    -- Box_Nonce
box      = XChaCha20-Poly1305(wrap_key, nonce, AD = cid ‖ u48(gen), k_g)      -- cipher[32] ‖ tag[16]
```

`Kome.Epochs` computes `eph_sk` from `k_g` inside the sealing operation; no
caller draws it, so a weak RNG cannot reveal it. Anyone who holds `k_g`
can recompute it, and such a party holds the boxed key already.
`Kome.Roster.Build` (phase 8) takes `k_g`, the `cid`, the signer, `gen`
and the members, computes `box_pk` and seals the boxes from the same
secret, and wipes it; `Make_Roster` is private to it, so a roster's
`box_pk` and boxes cannot disagree. No root has a long-term X25519 key,
and no key is used both to sign and to exchange.

The member calculates `X25519(dh_sk, box_pk)` and opens the box. Then it
calculates the nonce again from the opened key and refuses a mismatch, and
it refuses an opened `k_g` that is all zeros (`Kome.Epochs.Unbox_Key`). So
there is exactly one valid box per `(wrap_key, k_g)`.

Three layers keep keystreams apart:

- A fresh `k_g` per roster gives a fresh `eph_sk`, `box_pk` and wrap key
  per roster.
- Each wrap key binds the `cid`, `gen` and the two member keys. So wrap
  keys are different, even if a `box_pk` is used again (a restored device,
  a bug).
- With the synthetic nonce, a repeated `(key, nonce)` implies a repeated
  plaintext. This shows only that the same key was wrapped again.

The only randomness is `rnd`, which the issuer draws for each roster
(`Kome.Roster`, §10.3). SPARK code reads no RNG: the caller gives `rnd`.
Every derivation is deterministic, and known-answer vectors test it
(`spark/vectors/epochs.txt`). Decode refuses low-order and non-reduced peer
keys (§2), and the box code refuses them again. All-zero inputs are refused
(`X25519_Public(0^32)` and `Derive_Public(0^32)` are public knowledge, and
a key derived from them protects nothing): `Key_Pair` requires a seed
that is not all zeros, `Box_Key` a `k_g` that is not `Zero_Key`, and
`Unbox_Key` refuses an opened zero key; a roster builder that draws the
zero key (probability 2^-256) draws again; `eph_sk` is derived, not an
input.

**Two gates on transport, none on records.** Kome admits a peer to a session
if and only if its Noise static key is the `dh_pk` of a member of
`ROSTER_eff` whose `sign_pk` is not `revoked` (§3: a held `REVOKE` of that
key, with any `from_t`, from an issuer that is not `root_void`), and the
replica is not `quarantined` (below). So a revocation closes the gate at
once, before the roster that removes the member arrives and wins
`ROSTER_eff`. The same test applies to a `HELLO` credential (the peer's
member entry) and to the boxes a roster seals (`Kome.Roster` seals no box
for a revoked member). `Kome.Guard.Admits (cid, F, eff, dh) = Gate ∧ ¬
quarantined` is this test, with `eff` the record of `ROSTER_eff`, and the
session carries it as a contract: `Reconcile.Start` takes the `cid` and
the peer's Noise key; `Receive` of a `HELLO` refuses a credential that does
not list that key; `Admit` has the gate (`Gate_Open`) as its
precondition; and `Receive` (in `Auth` and `Data`) and `Next_Phase`
evaluate the gate again on every call, with `F` after the previous batch,
and abort the session when it fails (`SIMPLIFY.md` S9). So a revocation
that the owner issues during a session ends that session at the next
message. There is no generation counter. At most `Members_Max` = 64
devices pass the gate of a collection, because the gate is membership of
one roster (§7, Bounds). No message goes before the gate: the Noise XK
prologue binds `ns` and the protocol version, and a stranger cannot
finish XK without the responder's static key (§8).

**The quarantine (`SIMPLIFY.md` S10; AUDIT.md H2).** If a founding
`REVOKE` root-voids the signer of the newest roster, `ROSTER_eff` falls
back to an older roster, which can list members that the voided root had
removed. So the replica is **quarantined** while `Roster_Max`, the
roster-key maximum over every held roster, root-voided ones included, has
a root-voided signer (`Kome.Views.Quarantined`). While it holds, the
replica admits no peer (`Kome.Guard.Lemma_Quarantine_Refuses`), takes no
sealed bundle and seals none. The quarantine is set by the root-void
(`Lemma_Quarantine_Set`) and cleared by a roster of a root that is not
voided at a `gen` above every other held roster: the recovery roster,
which is then `Roster_Max` and `ROSTER_eff` (`Lemma_Quarantine_Cleared`).
It is a function of `F`, so it needs no durable flag and no arrival order.
A thief can set `gen` as high as its cap, but its rosters stay in the
maximum only until a recovery roster at a higher `gen` arrives, and the
founding key is uncapped (step 5 above).

A quarantined replica is released through the credential `HELLO`
(`SIMPLIFY.md` S11). `Receive` accepts the peer's `HELLO` in the `Gate`
phase, before `Admit`; when the credential is the recovery roster, the
caller decodes, verifies and applies it, the quarantine clears, and only
then does the replica evaluate the gate for `Admit`. The authorization
range brings the `REVOKE`s. What this gives up: a peer that holds
`REVOKE(R)` but not the recovery roster cannot release a captured replica
(it can only quarantine it, when the `REVOKE` arrives in a session that
the replica admitted); the release needs a member that holds the recovery
roster (§10.11).

The credential `HELLO` follows. A side sends its own `HELLO` only after it
has admitted the peer, so a non-member learns no membership list. The
credential is a roster in the sender's `F` that lists the sender's Noise
key. The receiver refuses any other credential. Before it verifies the
credential, the receiver drops it and aborts the session if its `F` holds a
founding `REVOKE` of the credential's signer (AUDIT.md G12): a root-voided
root could otherwise fill its own slice at the receiver with one fresh
roster per session, although it is refused every time. The receiver
applies the credential and evaluates the gate again. So a newly added
member can still reach a replica whose rosters are stale (§8).

**Joining.** A new device has no `F`, so it has no `ROSTER_eff` and admits
nobody. The join hand-off is `(root_pk, salt, del_ttl, frame of the
roster that lists the newcomer)`, delivered out of band with the device's
enrollment (§10.3). The newcomer opens its store with `root_pk`, `salt`
and `del_ttl` and applies the roster frame: a founding-signed or
root-signed roster applies to an empty store like any other authorization
record. That roster is the newcomer's freshness anchor. While `F` holds no
non-root-voided roster that lists the device's own `dh_pk`, the device
accepts as a credential only a roster that lists both the peer's Noise key
and its own `dh_pk`, refuses any other credential, and lets no other
credential change `ROSTER_eff`. So a removed member that reaches the
newcomer first with an old roster that lists the removed member and not
the newcomer cannot capture it, and the newcomer's first `ROSTER_eff` is
at least as new as the roster that added it.

A replica can read a sealed bundle (mailbox, broadcast, BLE) if and only if
it holds the bundle's key. Kome accepts a bundle **only under
`bundle_key(F)`**: `f(k_g, "kome/bundle")` for the `k_g` that the
device's own member entry of `ROSTER_eff` unboxes, computed again whenever
`ROSTER_eff` changes. (If Kome accepted the previous key, a removed member
could write into up-to-date replicas until the next roster.) So a captured
replica takes no bundle from honest members until an interactive session
releases it. A `gen` is not a key identifier: two rosters at one `gen`
have different keys, and a stolen root can box any key under any `gen` up
to its cap before it is root-voided, so a device never caches a key by
`gen`, and sealer and opener both use `bundle_key(F)`. The two gates
decide who you talk to, never what a record means.

A replica that syncs only through store-and-forward must still cross a
change of `ROSTER_eff`: the new roster travels in bundles under the new
key, which the replica cannot open yet. So there is a **sender rule**,
with no receiver change: for a set period after its `ROSTER_eff` changes,
a replica keeps the previous key and also sends an authorization-only
bundle under it, which carries the new roster and the `REVOKE`s before it
(AUDIT.md H17). These records are signed and admitted everywhere, and they
carry no data, so a removed member that still holds the previous key gets
no write path from them: it learns that it was removed. A replica that
holds the previous key and gets that bundle applies the new roster and
opens the rest.

**Revocation** is `REVOKE(X, from_t)`: root-signed and grow-only in effect.
Its effect is the view flag `void` on the records of `X` with `t ≥
from_t` (while its issuer is not `root_void`). Of the `REVOKE`s of `X` by
one issuer, `F` keeps the one with the least `from_t` (§3, `SIMPLIFY.md`
S5), so no view ever loses a revocation, and a repeated `REVOKE` costs no
slice entry: one with a higher `from_t` is dominated on arrival, and one
with a lower `from_t` replaces the held one. The roster that follows it
removes `X`, under a fresh `k_g`. A revocation is intentionally *not* a
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

**The log is a journal of operations on `F` (D9).** The replica of one
collection has two parts (`Kome.Store`): the frontier `F`
(`Kome.Frontier.State`), in which each held record carries a 64-bit
**tag**, and a `Store`: an append-only log, the identity of the
collection, the device's `seq_self`, two digest states and a pin counter.
There is no index (`SIMPLIFY.md` S14): the tag of a held record packs the
place of its frame in the log, the offset of its `APPLY` entry (40 bits)
and the frame's length (24 bits) (`Make_Tag`, `Tag_Off`, `Tag_Len`), and
the store reads frames by tag (`Read_Frame`). The lattice ignores the tag:
`Is_Frontier`, admission, domination and the views do not read it, and
`Apply` moves it with the header. The log is plaintext, and it carries no
authentication: no key, no checksum and no hash chain. Integrity and
confidentiality at rest belong to the host (file permissions, disk
encryption, a sealed container), not to Kome. A party that can write the
file can do anything to the store; a log cut at an entry boundary is a
stale replica, and nothing more (§8, the sync point). These are the log
entries (all integers are big-endian):

```
HEADER   "KOME" ‖ version:u8 (= 1) ‖ root_pk[32] ‖ salt[16] ‖ del_ttl:u48     (59 bytes)
APPLY    01 ‖ len:u24 ‖ frame          a frame that Put_Frame applied          (4 + len bytes)
SEQ      02 ‖ seq:u48                  seq_self, written by Compact              (7 bytes)
```

The log is `HEADER ‖ (APPLY | SEQ)*`. The `HEADER` fixes the collection:
the founding key `root_pk` (D1), the `salt`, and the tombstone lifetime
`del_ttl` in [`Del_TTL_Min`, `Del_TTL_Max`] (D10). `Store.Open (Root_PK,
Salt, Del_TTL, Self_PK, F, S)` writes it, and `Store.Open` and
`Open_From_Log` compute the collection context `cid = BLAKE2b-256(root_pk
‖ salt ‖ u48(del_ttl))` once and keep it (`Kome.Store.Cid`). Every frame is
verified under it: `Put_Frame` requires `Verified (Cid (S), Root_Key (S),
frame)`, and `Kome.Write` signs under it (§2). There is no `slice` or
`data_cap` field (`SIMPLIFY.md` S15): the slice is the compile-time
constant `Slice_Max` at every replica, and the data capacity is the
discriminant `Cap` of `F`, a parameter of each open. A reopen at a larger
or a smaller capacity than the one that wrote the log is allowed whenever
the replay fits in it. No byte of the log is rewritten in place: the only
writes are appends at `Log_Length` and the rename of `Compact`. Kome
persists nothing else: `seq_self` is in the log (§5), the views are
functions of `F` (§3, §4), and refused or dominated records changed
nothing. `Log_Max` is 2^30 bytes, so every offset fits in a tag.

**Deletion is not erasure.** A `DEL` frees the bytes of its entity in `F`
and in the next compacted log. It does not erase them: the dominated
`APPLY` entries stay in the log until compaction, the old file's bytes
stay on the device after compaction renames the new file over it until
the file system reuses them, a relay keeps every bundle it stored, and a
member of the roster whose key sealed a bundle can open it (§6). What Kome
guarantees is space and convergence (H7), not that a deleted value is
unrecoverable from a device or a relay. Erasure at rest is the host's.

**Compaction** writes a new log: the `HEADER`, then one `APPLY` per held
record in row order (the authorization rows slot by slot, then the data
row, entity-major), then one `SEQ(seq_self)`. It gives each record the tag
of its new place (`Frontier.Set_Tag`); nothing else of `F` changes. Row
order puts the authorization records first, so a replay of a compacted log
admits every data record (D14). Compaction builds the new log in a buffer
of `Log_Cap + 1` bytes that the binding supplies (the image of the new
file), reads the old log in place, copies each frame once and copies only
the new length back into the store, so it holds no second copy of the log
(§10.10 (c)). It is refused with `BUSY` while a reconciliation session
holds a snapshot of the log (`Pinned (S) > 0`; `Pin` and `Unpin`, §8,
`SIMPLIFY.md` S21), and it keeps the digests and `seq_self`. Compaction is
a store duty of the binding: `Put_Frame` never compacts on its own, and
the binding calls `Compact` whenever `Compact_Due (S, F)` holds, that is,
when the log has more than `2·|F| + Compact_Slack` entries after the
`HEADER` (`Compact_Slack = 64`), and no session pins the log. A compacted
log is never due (the Post of `Compact`). So, under this duty, the log
holds at most `2·|F| + 64` entries before every operation (apart from the
entries a pinned session lets accumulate), which bounds the dominated
bytes that a deleted value leaves behind and bounds the cost of the next
open. The Post of `Compact` (`Retagged`, `Compact_Layout`) states that
`F` changed only in its tags, that the `HEADER` bytes are kept, that
every record's `APPLY` ends before the final `SEQ`, which carries
`seq_self`, and that the log has `|F| + 1` entries; that the `APPLY`s are
contiguous and in row order is tested, not stated (§10.10 (b)).

**Replay** (when a store opens, `Open_From_Log (Input, Self_PK, F, S,
Valid_Length, Result)`) does these steps:

1. It checks the `HEADER`: its magic and version, a usable founding key
   (`Sign_Key_OK`) and a `del_ttl` in range (`MALFORMED` otherwise); a log
   that does not fit the store is `NO_SPACE`. It computes the `cid` from
   the `HEADER`.
2. It starts from the empty state with the logged founding key, at the
   data capacity of this open.
3. It does the entries in order. An `APPLY` reruns `Put_Frame` in
   **trusted mode** (`SIMPLIFY.md` S15): it decodes the frame once
   (`Header_Of`: one parse and one BLAKE2b) and does not verify the
   signature (`Trusted_Frame`: the frames of a store's own log are trusted,
   because the host owns the log's integrity; the proof does not use this
   assumption, and the test main checks it on each log that it reopens).
   The automatic expiry of `Put_Frame` (below) happens again, so replay
   needs no expiry entry. An `APPLY` that `Put_Frame` accepts without a
   change (a duplicate, an expired `DEL` that drops nothing) replays as
   `OK` and stays in the log. A frame that does not parse, is not a record
   frame or has a header that is not canonical, and an `APPLY` that
   `Put_Frame` would refuse (`INADMISSIBLE`, `DOMINATED`, `AUTH_FULL`),
   give `MALFORMED`; an `APPLY` that does not fit the data row of this
   open gives `NO_SPACE`. A `SEQ` raises `seq_self`.

Replay costs one parse and one BLAKE2b per entry and no signature check,
so an open costs `O(entries)` hashes: under the compaction duty above, at
most `2·|F| + 64`. `Open_From_Log` is strict: an entry that does not parse
or does not replay stops the open. It also reports `Valid_Length`, the
length of the longest prefix of the input at an entry boundary that
replays: on `OK` the whole input (`Valid_Length − 1 = Input'Last`); on
`MALFORMED`, or on a `NO_SPACE` from an entry, the start of the refused
entry; 0 when the `HEADER` is refused or the log does not fit. When
`Valid_Length > 0`, the returned `(S, F)` is the replay of exactly that
prefix, with that prefix as its log (`Replayed_Prefix`, proved:
T18-prefix). The binding owns the two cases that strictness alone would
make permanent (REQUIREMENTS H8: one entry must not brick the store). A
*torn tail* (power lost inside an append) is a cut last entry, which
replays as `MALFORMED`: the binding truncates the file to `Valid_Length`
and opens again, or uses the returned prefix state as it is. A *corrupt
entry* in the middle (a byte that no longer parses) stops the replay at
that entry: the binding opens the prefix before it, reports `DEGRADED`,
and syncs again; the entries after the corrupt one are not skipped,
because a `DEL` among them could have removed what the prefix still
holds, and a replica that holds more than it should is only stale.
Trusted replay does not detect a flipped byte that leaves a frame well
shaped (it would read as a different, unsigned record): that is the
integrity that the host owns. A *duplicated* `APPLY` replays as `OK` with
no change (step 3), and the binding still writes each append at the
`Log_Length` from before the call (`pwrite` at that offset; `Put_Frame`
returns that offset as `Off` whether or not it appended), so a retry
after a write error overwrites the same bytes and never appends twice.

Each operation is a deterministic function of the held set. After
compaction, Kome admits each authorization record and each data record. The
reason is that the authorization part is complete before the first data
record, and `F` is an antichain under `dom`. T18 states the result: the
same held set and the same `seq_self` (array order and tags can be
different after compaction).

**Order of operations and room (D11, E1, E2).** Before the store sees a
frame, the caller decodes and verifies it under the store's `cid` and
`root_pk` (`Verified`): a record of another collection does not verify,
because its `h` binds another `cid` (§2). When Kome applies a decoded,
verified frame whose header is `H` (`Store.Put_Frame`), it does these
steps. All classification occurs before any change, and no refusal changes
anything (the Post `Put_Done` states each outcome as an iff):

1. A data record that is not admitted: `INADMISSIBLE`.
2. Already held: `OK`, no change.
3. Dominated by a held record: `DOMINATED`. It needs no room in the
   frontier or the log, and it never gets `NO_SPACE`.
4. A `DEL` with `t ≤ hz(F)` (expired on arrival, below): Kome applies it
   for its effect. If it dominates nothing held, nothing changes and
   nothing is logged. If not, its dominated records leave `F`, Kome logs
   its `APPLY` (the `DEL` needs log room, and no frontier room), and Kome
   does not hold it. The status is `OK`.
5. Room. The refusals are:
   - Not sufficient log bytes for the `APPLY`: `LOG_FULL`. The binding
     compacts and retries. Log bytes are a capacity class of their own,
     shared by every record, so a store whose log is too small for its
     rows can refuse the founding `REVOKE` after a flood of large values,
     and compaction would free nothing. The binding therefore keeps
     **`Log_Fits`**: `log_cap ≥ 59 + 7 + (data_cap + Signers_Max ·
     Slice_Max + 1) · Entry_Max`, with `Entry_Max = 4 + 41 120 = 41 124`
     (the `APPLY` prefix plus the largest frame). Under `Log_Fits`, a
     compacted log has room for one more entry of any kind, so `LOG_FULL`
     only ever means "compact first". It is a bound on `data_cap` for a
     given `log_cap`: with a 1 GiB log, at most about 17 900 data records
     beside 16 full slices. `Kome.Store.Log_Fits` is the test, and `Open`
     and `Open_From_Log` do not require it (small logs are legitimate for
     tests and for tiny stores); a binding that opens a store without it
     accepts that `LOG_FULL` can be permanent.
   - Data records share one **data capacity** (`data_cap`, the
     discriminant of `F`). A data record whose capacity is full and that
     frees nothing: `NO_SPACE` (the caller compacts, deletes, or stops).
     When the refused record came from a peer, the transport reports the
     refusal as a replica status, because the replicas then disagree
     about that record (below, and §10.5).
   - Each signer has its own **slice** of `Slice_Max` = 512 authorization
     records, in one of `Signers_Max` = 16 slots. Slot 1 is reserved for
     the founding key. Kome assigns a slot to a certified root when it
     holds that root's first record, and never frees the slot. (No record
     of a signer can leave `F` except under another record of the same
     signer.) A record that dominates a held record frees the slot of that
     record, which is always in its own row (§3). An authorization record
     whose signer's slice is full and that frees nothing, or whose signer
     is new when all 16 slots are in use: `AUTH_FULL`.

   The tags live in the frontier's slots, so nothing else needs room. `W`
   (at most one subject per held `GRANT`) always has room.
6. Apply: drop what the record dominates, hold the record with the tag of
   its new `APPLY` entry, append the `APPLY`, update the two digest states
   and `seq_self`, and then expire: if the record raised `maxceil` or
   arrived expired, `Frontier.Expire (F, hz(F))` removes the `DEL`s at or
   below the horizon. This is Lean's `applyH delTtl S r = expireHz delTtl
   (applyD S r)` (`Kome.Store.Applied_H`).

**What `AUTH_FULL` means.** Kome never drops a key silently, and a refused
record changes nothing. But then the set of an over-quota signer's records
that a replica holds depends on arrival order. So replicas can disagree
permanently about these items:

- that signer's surplus records;
- the data records that only its surplus `GRANT`s admitted;
- the records that those data records dominate;
- that signer's contribution to `maxceil`, when the refused record is a
  roster. `maxceil` is a maximum over *held* rosters, and a refused roster
  does not count. A stolen root with a long cap can fill its slice with
  `REVOKE`s at one replica and send its roster first at another: the
  second replica then admits data up to that roster's ceiling, and the
  first discards the same data for good. A root-void does not lower
  `maxceil`, so the disagreement is permanent, and it ends only when every
  honest root's ceiling passes the stolen one's. (A reserved ceiling cell
  per slot would close this, AUDIT.md H12; it is deferred.)

Honest roots never reach their slice (the honest-issuer rules, §10.3), and
the founding key certifies at most 15 distinct signer keys (A1). The
founding key's slice is a lifetime budget, not a reserve by itself: every
`REVOKE` of a distinct key stays held, so about 250 key rotations (a
`REVOKE` plus a `GRANT` each) would fill it, and then `REVOKE(R, 0)` would
get `AUTH_FULL`. So the founding key keeps a reserve of 15 entries for
root-voids (§10.3) and does no routine `GRANT`s or `REVOKE`s. So only a
stolen root can cause this. It cannot touch any other signer's slice. When
it is root-voided, all that its surplus admitted reads `void`. After that,
byte-for-byte agreement comes back only if the owner re-founds the
collection. The slice is the constant `Slice_Max` at every replica, so no
two replicas disagree about where a slice ends.

**Drop rule.** A record leaves `F` if and only if:

```
dom(x, F)                                                  -- deterministic, membership-free (T3)
∨ (x is DEL ∧ x.t ≤ hz(F))                                 -- tombstone expiry
```

**Expiry is a function of `F` (D10, `SIMPLIFY.md` S7).** The horizon is

```
hz(F) := maxceil(F) − del_ttl     if maxceil(F) ≥ del_ttl, and none otherwise   (Kome.Store.Hz, Lean hz)
```

and a `DEL` `d` is expired when `d.t ≤ hz(F)` (Lean `isExpiredAt`: `d.t +
del_ttl ≤ maxceil(F)`). The subtraction is taken only when `maxceil(F) ≥
del_ttl`, so it never wraps, and there is no reserved "no horizon" code.
No local clock is read: the roots' ceilings set the limit on expiry, not
one device's clock, so a clock set far ahead (spoofed time, or the user)
cannot expire any tombstone. Expiry is automatic: `Put_Frame` of a record
that raises `maxceil` (a roster with a higher ceiling) expires in the same
call, and so does the apply of a `DEL` that arrives expired (step 6).
`maxceil` never falls, so the horizon never goes back (Lean `hz_mono`).
A `DEL` that expiry removed stays removed; if it arrives again, it is
expired on arrival (step 4). Replay reruns `Put_Frame`, so a reopened store
reaches the same `F`, with no expiry entry, no replay clamp and no
in-memory-only raise. A3 gates expiry as well as writing: once the root
devices stop refreshing, `maxceil` stops, and so does the horizon, so no
tombstone expires until a fresh roster arrives. `skew = now − maxceil`
(`Kome.Views.Skew`) is the advisory status that the C ABI shows for this
(§10.6). A device with no real-time clock expires exactly what every
replica with its `maxceil` expires.

The horizon protects tombstones only as far as the ceiling leads the wall
clock. A ceiling issued `δ` ahead of the wall clock expires `DEL`s `δ`
early in wall time, and a ceiling `del_ttl` ahead would hold no
tombstone at all. So the honest-issuer rules keep `ceiling_t ≤ now +
Cap_Lead` with **`Cap_Lead` = 3 days `< Del_TTL_Min`** (§10.3), and every
expiry statement below counts the window `del_ttl − Cap_Lead`. A write
is emitted at `t ≥ maxceil − Cap_Lead` (§5), above `hz(F)`, so a `DEL` is
never expired at the writer's own `maxceil`, and a replica expires it only
once its `maxceil` passes `d.t + del_ttl`, at least `del_ttl − Cap_Lead`
above the writer's.

`del_ttl` is fixed at founding (`SIMPLIFY.md` S2): it is in the `HEADER`
and in the `cid`, in [7 days, 3 650 days], and no record carries it. So a
stolen root cannot set it to zero to resurrect deleted data in bulk, and
no root, stolen or honest, can make it shorter or longer. A collection that
needs another value is a new collection. If there is no horizon yet,
nothing expires.

The second clause is **apply-then-expire**, not refuse-on-arrival. Kome
always applies a `DEL` that arrives with `t ≤ hz(F)` (it dominates and
frees the entity's values). Only after this, because the `DEL` is expired,
Kome does not hold it. If Kome refused an expired `DEL` on arrival, two
replicas with a small skew of `maxceil` could diverge and then resurrect
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
admitted and durable at every member within `del_ttl − Cap_Lead` of
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

**Digests (`SIMPLIFY.md` S21).** The store keeps two
`Kome.Digest.Digest_State` values, one over the authorization rows
(`Digest_Auth`) and one over the data row (`Digest_Data`); `Valid` states
that they are the states of the held hashes (`Lemma_Digests`;
`Lemma_Digest_Split` relates them to `Kome.Digest.State_Of (F)`).
`Put_Frame` keeps them by diffing: a data apply changes one entity run
(`Frontier.Run`, `Outside_Run`) and an authorization apply one signer slot
(`Frontier.Slot`, `Outside_Slot`), so the store subtracts the sum of the
run or slot before the apply and adds its sum after, and never scans `F`
for an apply. An expiry can remove `DEL`s of many runs, so after an expiry
that removes a record the data digest is summed again over the data row.
The session's `HELLO` is sent from these two states (§8).

**Bounds.** After each `Put_Frame`, `|F| ≤ live cells + DELs above hz(F)
+ authorization records`. `data_cap` sets the limit on the data part.
`Signers_Max × Slice_Max = 16 × 512 = 8 192` records sets the limit on the
authorization part (each signer's rosters, `GRANT`s and `REVOKE`s, within
its slice). Thus `|W| ≤ 8 192`. This bounds *storage*: the keys that can
hold records. The devices that can sync are bounded by the gate, at most
`Members_Max` = 64 per collection, the members of one roster (§6). The
state is `F` with its tags, the log (with `seq_self` in it), the two
digest states and the pin counter; every per-session value lives in the
session and is gone when it ends.

## 8. Reconciliation and digest

Elements are the records of `F`. An element's key is 82 bytes, compared
bytewise (`SIMPLIFY.md` S18; `Kome.Reconcile.Key_Of`):

```
data           03 ‖ ent[16] ‖ sub:u8 ‖ fh[32] ‖ h[32]        sub = 0 for DEL, 1 for PUT
authorization  tag ‖ 0^17 ‖ signer[32] ‖ h[32]              tag = 0 ROSTER, 1 REVOKE, 2 GRANT
```

`fh` is the BLAKE2b-256 of the field name (zero for a `DEL`), and `signer`
is the issuer. The 17 zero bytes of an authorization key come before the
signer, so that both layouts keep their fields at the same places. The
data keys are entity-major, which is the order of the frontier's data row
(sorted by `(ent, kind, fh)`, `DEL` before `PUT`), so the data part of a
snapshot is already in key order. Authorization records sort first. The
key space splits at `Data_Lo = 03 ‖ 0^81` into the **authorization range**
`[Min_Key, Data_Lo)` and the **data range** `[Data_Lo, Max_Key)`.
`Min_Key` is all zeros, and `Max_Key` is `FF ‖ 0^81`. "Apply in
element-key order" is the one ordering rule of every batch (D14): it puts
the authorization records before the data records and the `ROSTER`s
before the `REVOKE`s before the `GRANT`s.

**Fingerprint = digest (D7).** For a record `e` with content hash `h(e)`
(32 bytes, in the order that BLAKE2b produced them; `SIMPLIFY.md` S20):

```
B_i(e)     := BLAKE2b-512("kome/acc" ‖ h(e) ‖ u8(i))           for i = 0..7
acc(e)     := Σ_{i=0..7} LE(B_i(e)) · 2^(512·i)  mod 2^4096,    LE(B) := Σ_j B[j] · 256^j
ACC(R)     := Σ_{e ∈ R} acc(e)  mod 2^4096
fp(R)      := BLAKE2b-256("kome/fp" ‖ u64(|R|) ‖ ACC_le(R))
digest     := fp(F)
```

An equivalent statement: `acc(e)` is the 512-byte string `B_0 ‖ … ‖ B_7`
read as a little-endian integer (chunk `i` at bytes `64·i .. 64·i + 63`).
`ACC_le(R)` is the 512-byte little-endian form (byte `k` is `⌊ACC/256^k⌋
mod 256`).

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
the tail. The cost is 8 bytes amortized per element. When this side
splits a window of at least 1 024 elements, it puts the interior cuts on
multiples of 64 (`SIMPLIFY.md` S20), so only the two ends of a range walk
elements, and each walked element costs eight BLAKE2b-512 calls.

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

**Messages** (`SIMPLIFY.md` S11, S19). All integers are big-endian.

```
HELLO     01 ‖ n_auth:u32 ‖ n_data:u32 ‖ digest[32] ‖ cred_len:u16 ‖ cred[cred_len]     43 + cred_len, at most 8 959
RANGE     02 ‖ k:u8 (1..16) ‖ bounds[k + 1] × key[82] ‖ k × (count:u48 ‖ fp[32])       2 + 82·(k + 1) + 38·k, 2 004 at k = 16
ELEMENTS  03 ‖ lo[82] ‖ hi[82] ‖ n:u16 (≤ 4) ‖ n × (flen:u16 ‖ frame)                  167 + items
HAVE      04 ‖ lo[82] ‖ hi[82] ‖ n:u16 (≤ 4) ‖ n × (flen:u16 ‖ frame)                  167 + items
ROOT      05 ‖ count:u48 ‖ fp[32]                                                        39
```

There is no pre-gate message (no `OPEN`): the Noise XK prologue is
`"kome/1" ‖ ns ‖ 01` (23 bytes, `Kome.Reconcile.Prologue`), which binds
the collection and the protocol version, and a stranger cannot finish XK
without the responder's static key (Transports, below). A `RANGE` carries
`k` sub-ranges `[b(j−1), b(j))` with their counts and fingerprints, so a
16-way split is one message. An `ELEMENTS` or `HAVE` item is its frame
only: the receiver derives the key from the decoded frame. `ELEMENTS` and
`HAVE` keep their `lo` and `hi`, which make the replies tile. A `ROOT`
carries the count and fingerprint of a whole range; its bounds are fixed
by the phase: `[Min_Key, Data_Lo)` for the first, `[Data_Lo, Max_Key)`
for the second. Each field has one width and the order of the parts is
fixed, so a message has one encoding. A range is half-open, `[lo, hi)`,
with `lo < hi`.

**HELLO (post-gate, D13).** `n_auth` and `n_data` are the sender's element
counts in the two ranges. They set the budgets, and they go into them only
as `min(claimed, Elem_Max)`. `digest` is the digest of the sender's `F`.
The sender builds the `HELLO` from the store's two incremental digest
states (`Kome.Store.Digest_Auth`, `Digest_Data`, §7), which `Admit` takes:
no snapshot is built for it.

`cred` is the sender's credential. It is the frame of a roster in the
sender's `F`. The members of this roster include the sender's Noise static
key as a `dh_pk` (usually this roster is `ROSTER_eff`). It is at most
8 916 bytes, so a `HELLO` is at most 8 959 bytes. `HELLO` carries
**no register values**.

A side sends its `HELLO` only when it has admitted the peer, so a
non-member learns no membership list. The receiver refuses a credential
that is not a roster frame, that does not list the peer's Noise key, or
whose signer is root-voided in its `F` (§6), and it aborts the session
(`S_Aborted`). If the credential passes, the caller decodes, verifies and
applies it like any authorization record, and evaluates the gate again. If
the gate then admits the peer and the receiver has not sent its own
`HELLO`, it sends it now. (This is how a newly added member reaches a
stale replica, and how a recovery roster reaches a quarantined one, §6.
The stale side admits the newcomer when it sees the newcomer's
credential.) If no side can admit the other, the session times out.

A peer can lie, so Kome trusts nothing in a `HELLO`. A false count or
digest only costs rounds within the session budgets, and the frames are
signed records. Equal digests end the session after the `HELLO` exchange
(under A2 they mean equal frontiers). Only when the digests differ does a
side build its **snapshot** (`SIMPLIFY.md` S21): on entering `Auth`, it
pins the store (`Kome.Store.Pin`, so that `Compact` is refused while the
session runs), builds the snapshot with `Snapshot_Of (F, T, S, Result)`,
seals it, passes it to every later `Receive` and `Next_Phase` (a
precondition checks that its count and digest are those of our `HELLO`),
and unpins at the end. The snapshot does not copy frames: its keys are
`Key_Of (H)` for each held header, in key order, and each element records
its source index in `F`; the frames come from a frame table `T` that the
binding fills from the log with `Kome.Store.Read_Frame` in the flat order
of `F` (entry `I` is the frame of `Held (F, I)`, a binding duty), and
`Encode` copies the item frames from it. The Post of `Snapshot_Of` states
that each element is a held record of `F`, that the elements are in
strictly ascending key order and are distinct records, that `|S| = |F|`,
and that the digest of the snapshot is `Kome.Digest.Frontier_Digest (F)`:
no caller can present a snapshot whose keys `F` does not have. The data
row is already in key order, so each data element appends in one
comparison; the authorization rows are kept by slot in arrival order,
which is local to a replica, so `Snapshot_Of` inserts the at most 8 192
authorization records into key order (§10.11).

**Session (D14).** The phases are `Gate`, `Auth`, `Data` and `Done`.

- `Start` takes the role, the `cid` and the peer's Noise static key. The
  phase is `Gate`, and nothing goes out.
- `Admit`, called when the gate admits the peer (its precondition), emits
  our `HELLO` from the two digest states. `Receive` of the peer's `HELLO`
  (in `Gate`, before or after `Admit`) runs the credential check above.
- When the two `HELLO`s have passed, equal digests end the session
  (`Done`, no more messages). Otherwise the phase is `Auth`, and the
  initiator sends the authorization `ROOT`.
- **Auth phase.** When nothing that the initiator asked is open, the
  authorization phase is complete on its side, and it calls `Next_Phase`,
  which sends the data `ROOT` and moves to `Data`.
- **Data phase.** When nothing that it asked is open again, the initiator
  is **done**. The responder accepts a `ROOT` only in `Auth`: the first is
  the authorization `ROOT`; the second, accepted only with nothing that
  the responder asked open, is the data `ROOT` and moves it to `Data`. (On
  an in-order transport, the initiator answered all of the authorization
  phase first.) The responder is done when nothing is open after a
  `Receive` in `Data`.
- Every other message is `S_Unexpected` and changes nothing: a `ROOT` at
  the initiator or at the wrong time, any `RANGE`, `ELEMENTS`, `HAVE` or
  `ROOT` before `Auth`, any reply that does not continue the head
  obligation (below), and any message in `Done`.

`Receive` (in `Auth` and `Data`) and `Next_Phase` evaluate the gate
(`Gate_Open`: `Kome.Guard.Admits` with `ROSTER_eff` of `F`) on every call,
with `F` the state after the caller applied the previous batch; when it
fails, the session ends with `S_Aborted` (`SIMPLIFY.md` S9). Within a
batch the caller applies in key order, so `ROSTER`s before `REVOKE`s
(S10).

After the authorization phase, the two sides hold the same authorization
records, unless one side refused one with `AUTH_FULL` (§7). In that case
they can differ in `maxceil` as well as in the refused record, because a
refused roster does not count: the §7 "What `AUTH_FULL` means" list names
this case, and it needs a stolen root. In every other case they have the
same `maxceil` and `W`, and each data record that a peer sends in the data
phase is admissible on arrival. This makes the exchange clause of T4 true
without registers in the `HELLO`. Expiry needs no step between the
phases: a roster of the authorization phase that raises `maxceil` expires
in its own `Put_Frame` (§7). The initiator is the Noise initiator.

**Replies tile (`SIMPLIFY.md` S19).** A `ROOT`, a `RANGE` part or an
`ELEMENTS` obliges its receiver to answer; a `HAVE` obliges nothing. Let
`window` be the elements of our snapshot in `[lo, hi)`:

- `ROOT` or `RANGE` part whose `(count, fp)` are equal to ours over `[lo,
  hi)`: one empty `HAVE` over `[lo, hi)` (the confirm).
- `ROOT` or `RANGE` part otherwise, `|window| ≤ 4`: `ELEMENTS` over `[lo,
  hi)` that carries exactly `window`. (If the elements do not fit in one
  message, send one `ELEMENTS` per element, each over a sub-range that
  holds only that element; the sub-ranges tile `[lo, hi)`.)
- `ROOT` or `RANGE` part otherwise: one `RANGE` message of at most 16
  parts that tile `[lo, hi)`. Each part carries our exact count and
  fingerprint of its sub-range, and each holds strictly fewer of our
  elements (balanced: `⌊n/16⌋` or `⌈n/16⌉`, or blocks on multiples of 64
  for a window of at least 1 024; the balance is tested, not proved).
- `ELEMENTS`: deliver exactly the listed items that are not in our snapshot.
  Then, if `|window| ≤ 4`, send `HAVE` over `[lo, hi)` that carries exactly
  `window` minus the listed items (one empty `HAVE` if there are none;
  one element per message, tiling the range, if they do not fit). If not,
  use the split above.
- `HAVE`: deliver exactly the listed items that are not in our snapshot. Do
  not reply.

`Receive` takes one logical message: a `ROOT`, an `ELEMENTS`, a `HAVE`,
or one part `j` of a `RANGE` (the caller calls `Receive` for `j = 1 .. k`
on the same input). The caller decodes and verifies each item frame with
`Kome.Records` and passes its element key; `Receive` checks that the keys
ascend strictly within `[lo, hi)`. Each plan in a reply is exact: a
`RANGE` part carries our true count and fingerprint, and an `ELEMENTS`
carries all our elements of its range.

**Replies are bound to obligations.** Each side keeps a FIFO of the
obligations it opened (the `[lo, hi)` of each `ROOT`, `RANGE` part and
`ELEMENTS` it sent), bounded by `Oblig_Cap`. Each direction of the session
is in order, so the answers arrive in request order. The answer to an
obligation is a run of messages that tiles `[lo, hi)`: the first starts at
`lo`, each next one starts where the last one ended, and the answer is
complete when a message's `hi` reaches the head's `hi`. Any kind may
tile; there is no group-size byte and no repeat rule. A side accepts a
reply only when it continues the head obligation; any other reply, also a
duplicate delivery, is refused and changes nothing. So a duplicated or
forged reply cannot close another obligation, and `Complete` (nothing
open, no abort) means that every obligation got exactly one tiling answer.
(That implication is an induction over the per-call Posts of `Admit`,
`Receive` and `Next_Phase`; it is tested, not proved.) A fingerprint over a
sub-range costs at most 64 additions and one hash through the D15 prefix
sums, never a hash over the whole range. Each accepted message costs one
scan of the window (`O(n)`) and at most 17 such fingerprints, so a session
of `m` accepted messages costs `O(m·n)` scans, and the budgets bound `m`.
With balanced splits, `m` is `O(log n)` for each difference, and the
fingerprint work is `O(n log n)` for `n` held elements; this bound rests on
the balance and is tested, not proved.

The session layer requires exactly-once, in-order delivery: Noise's nonce
counter rejects a replayed or reordered message, and a rejected message
counts as loss. If a data `ROOT` overtakes the last reply of the
authorization phase, the receiver refuses it, and the session then never
completes. **If a message is lost, or a `ROOT` is reordered, the session
never completes.** The caller times out and starts a new session.

A session with no loss takes at most `⌈log₁₆ N⌉ + 2` rounds per phase. If
loss occurs, convergence holds given fairness at the session level (some
session completes eventually), and T7 states this explicitly. Per-session
budgets set a limit on what a hostile peer can get. The budgets count the
logical messages accepted, the `RANGE` parts emitted in replies and the
item bytes emitted, over the two phases (a 16-way split counts as 16
parts). A member that always claims `Elem_Max` elements gets the largest
budgets in every session. That member is authorized to read `F` in any
case. The transport must set a limit on how frequently a peer can open
sessions.

**Message size (D12).** Each message is at most `Max_Message_Len` = 48 KiB.
A frame is at most 41 120 bytes (a `PUT` with a 32-byte field and a
40 960-byte value). This is less than the 48 983 bytes that one `ELEMENTS`
item can carry (`Frame_Ship_Max = 48 KiB − 167 − 2`). It is also less than
the sealed-bundle plaintext bound. So each well-formed record fits in one
message on each transport. The implementation checks the two inequalities
at compile time.

**Transports.** Kome uses Noise XK for interactive sync. The responder's
static key is a member `dh_pk` that the initiator takes from its
`ROSTER_eff` (or from the credential it was handed at enrollment), and
the prologue `"kome/1" ‖ ns ‖ 01` binds `ns` and the protocol version. In
XK the responder's static key never crosses the wire, and the initiator
sends its own static key encrypted under the responder's; so a stranger
that scans for Kome endpoints (a BLE or LAN scanner) learns that an
endpoint answers and nothing else: no `dh_pk`, no `ns`, no membership, and
no way to link the endpoint across places, network changes or
collections. (Noise XX would hand the device's long-term `dh_pk` to any
party that completes a handshake.) The static key is **per collection**:
`dh_sk_ns = KDF(device secret, ns)`, so the same device has unrelated
`dh_pk`s in two collections, and two memberships cannot be linked by key.
This per-collection `dh_pk` is the member entry that rosters list and that
opens the boxes: `dh_sk_ns` is the member's whole capability in that
collection (§6, T14). The transport refuses a low-order Noise static key
from a peer and uses a constant-time X25519. It uses sealed bundles for
store-and-forward:

```
bundle      = ns[16] ‖ nonce[24] ‖ XChaCha20-Poly1305(bundle_key, nonce, AD = cid ‖ u48(gen), pad(plaintext))
bundle_key  = f(k_g, "kome/bundle")                -- Kome.Epochs.Bundle_Key_Of, k_g of ROSTER_eff (§6)
nonce       = f(bundle_key, "kome/bnonce" ‖ pad(plaintext))[0:24]
```

`Kome.Epochs.Bundle_Key_Of` derives the bundle key. The padding, the
nonce and the seal belong to the bundle layer of the transport (phase 9),
which is not built.

The `gen` is in the associated data only, never in the clear: the sealer
fills it from its `ROSTER_eff`, and the opener from its own, whose key is
the only one it accepts anyway. `pad` is deterministic: it extends the
plaintext to the next of a fixed set of bucket sizes, so a bundle's length
shows its bucket and not its content, and a membership change (a roster
with one member more or less) does not show as a length change. Kome
accepts a bundle only with `bundle_key(F)` (§6). All members share `k_g`,
so the nonce must never come from a per-device counter. The nonce is
synthetic, as for boxes. Identical plaintexts give identical bundles, and
this shows only that the plaintexts are identical. The plaintext is a
list of `ELEMENTS` items (`flen:u16 ‖ frame`), in element-key order, with
a total of at most `Max_Message_Len` bytes before padding. The receiver
applies the items in element-key order (D14: the authorization-first pass
of T4 (a)). Relays see ciphertext, `ns`, the bucket size, timing and the
transport's routing key.

**Bundles are closed under admission.** A bundle carries, ahead of its
data records, every `GRANT` of each data author that the sender holds and
the sender's roster with the largest ceiling (or an authorization-only
bundle goes first). So a `DEL` in a bundle is admitted wherever the bundle
is opened, and never discarded for a stale `maxceil` or a missing `GRANT`
and then forgotten (`auth_first_closed` in Lean). A `DEL` that a session
discards as `INADMISSIBLE` is offered again by the next session (§4), but
a bundle has no next session. The quarantine (§6) suspends bundles.

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
transport counts a session as `Complete`, before it sends a frame that
this device wrote, before it acknowledges a bundle or deletes it from a
mailbox, before it relays an applied record to another peer, and before it
continues after applying an authorization record. Otherwise a crash can
undo an applied `DEL` while every other replica expires it (A4, §7), drop
a `REVOKE` that this replica already told a peer it holds, or lose an own
frame that a peer already holds (§5). A log cut at an entry boundary by a
crash before the sync point is a stale replica, which the next session
repairs; the log needs no hash chain for this.

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
    The store expires at its horizon `hz(F)` (`applyH delTtl`, which
    `Kome.Store.Put_Frame` refines: its Post `Put_Done` states
    `Applied_H`), and then the order matters when a record that an expired `DEL` dominates
    arrives after that `DEL` (`[d, p, d, p]` gives `{p}`, `[p, d, p, d]`
    gives `{}`). Under `NoLateDom(h, l)` (no such late arrival), the two
    agree after an expiry at `h` (`expire_applyAllH`, and
    `expire_applyAllH_hz` at the store's horizon); A4 excludes the late
    arrival.
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
  `W(F(H)) = W(H)` and `wcap(F(H), k) = wcap(H, k)`. So no admission view
  shrinks along any history, and this includes rosters of lower generation
  or ceiling and grants of lower cap. Admission never reads `REVOKE`,
  `root_void` or `W_eff`. In SPARK the three views are opaque functions of
  `F` (`Kome.Frontier.Max_Ceil`, `In_W`, `W_Cap`, each with a `_Def`
  lemma), and `Lemma_Views_Step` gives their values after each `Apply`:
  `maxceil` becomes `max(old, ceiling of R)`, and `W` and `wcap` grow
  exactly by `R` (`Lemma_Same_Auth_Views` for an `Apply` that keeps the
  authorization rows). In Lean `maxceil` and `wcap` are instances of one
  family `maxP` (`maxP_cover`, `maxP_mono_auth`).
- **T5 ✓ View determinism.** `deleted_at`, `cell`, `exists`, `maxceil`, `W`,
  `wcap`, `root_void`, `W_eff`, `revoked_at`, `void`, `ROSTER_eff`,
  `Roster_Max`, `contested` and `quarantined` are functions of `F` as a set
  alone (and of the constant `root_pk`). `ROSTER_eff` and `Roster_Max` use
  the whole roster key `(gen, h, signer, ceiling_t)` to break a tie, so they
  do not depend on list order, even without A2. Also, `W_eff`, `root_void`,
  the least `from_t` of each revoked key (`isMinFrom_F`) and `ROSTER_eff`
  of `F(H)` are equal to those of `H`. `far` and `skew` read the local
  clock and are not in this list.
- **T6 ✓ Digest** (SPARK: `Kome.Accumulator`, `Kome.Digest`; there is no
  Lean statement). `digest = fp(F)`; `ACC(R₁ ⊎ R₂) = ACC(R₁) +
  ACC(R₂)`; under k-sum hardness, `fp(R₁) = fp(R₂) ⇒ R₁ = R₂`.
- **T7 ✗ Reconciliation.** Start from `F_A, F_B` over `N` elements. A
  session is two sequential range reconciliations over a partition of the
  key space. Each one terminates in `≤ ⌈log₁₆ N⌉ + 2` rounds without loss.
  The measure is `(μ, k)`. Here `μ([lo, hi))` is the two sides' element
  counts in the range, and `k = 1` for a `RANGE` and 0 for an `ELEMENTS`.
  The two sides then hold `F(F_A ∪ F_B)`. If loss occurs, no session
  completes, and convergence follows from fairness at the session level.
  (This is the large Lean project.) `Kome.Reconcile` proves the per-call
  facts: each reply strictly decreases the measure, the reply kinds, the
  tiling and the exact plans, the obligation FIFO, the message size
  bounds, the budget checks, the gate check on every `Receive` and
  `Next_Phase`, and the snapshot (sorted, distinct, held records of `F`,
  with the digest of `F`). Its "Tested, not proved" list holds the rest: T7
  itself; that `Decode` accepts every `RANGE` and every `ELEMENTS`/`HAVE`
  that carries items, and the bytes of an encoded `RANGE` after its `k`
  and of the items of an encoded `ELEMENTS`/`HAVE`; balanced splits, the
  64-multiple cuts and the `log₁₆` round bound; the honest-session
  derivations of the budget numbers and of the sufficient obligation
  capacity; the session-wide statements that every accepted message was
  accepted while the gate held and that `Complete` gives one tiling answer
  per obligation; and the `O(n log n)` work bound (§8).
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
  - (a) ✓ After every `Put_Frame`, `F` holds no `DEL` with `t ≤ hz(F)`
    (`Kome.Store.Lemma_No_Expired`; Lean `expireHz_none`), and `|F|` meets
    the §7 bound. Expiry of a frontier gives a frontier with the same
    admission views (`Frontier.Expire` keeps `Max_Ceil` and the
    authorization rows; Lean `maxCeil_expireHz`, `expireHz_frontier`).
  - (b) ✓ Apply-then-expire: take two replicas whose held sets are
    different only because one holds a `DEL` `d` with `d.t ≤ h` and the
    other does not. After the same further records, a re-sent `d` and an
    expiry at `h`, they agree on each record (`expire_reapply`,
    `expireHz_reapply`). (For `applyD`; the store's
    `applyH` agrees with it under `NoLateDom`, T4 (b).)
  - (c) Under A4 (every copy of `d` admitted and durable within
    `del_ttl − Cap_Lead`, no late copy of what `d` dominates, and a
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
  `t` and `gen` never wrap. At a bound, emission fails with no
  side effect. No refused apply changes the state. Every held roster has
  `gen ≤ ceiling_t` (§2 rule 2), so a certified root's `gen` is at most
  its cap, and an honest root never emits `gen > 2^47` (§10.3).
- **T14 ✗ Key secrecy.** Let `r` be a roster of gen `g` with key `k_g`.
  For a party that is not `r`'s issuer and holds no `dh_sk` of a member
  that `r` lists, `k_g` and `bundle_key = f(k_g, "kome/bundle")` are
  indistinguishable from random. Keys of different rosters are
  independent: a member that `r` leaves out learns nothing about `k_g`
  from the keys of the rosters that listed it, and a root-voided root,
  and the devices it held (whose `sign_pk`s recovery step 2 revokes), get
  no box of any later roster. The premises: keyed BLAKE2b-256 is a PRF
  (`k_g` is its output under the issuer's seed over `"kome/key" ‖ cid ‖
  u48(gen) ‖ rnd`, the A6 hedge, so a weak `rnd` alone does not reveal
  it; `eph_sk`, the box nonce and the bundle key are its outputs under
  `k_g`, and the wrap key its output under the X25519 secret, each with
  its own label); X25519 is Gap-CDH (or CDH in the random-oracle model
  with separate oracles, since each member's `dh_sk` serves both the boxes
  and the Noise static key: `dh_sk` is the member's whole capability); and
  XChaCha20-Poly1305 is an AEAD with a unique `(key, nonce)` per
  plaintext. The theorem excludes what it must: every member's `dh_sk`
  stays secret (there is no post-compromise security, §6), the issuer's
  signing seed stays secret, and a stranger learns nothing from the
  transport (Noise XK, §8). It is a paper argument, not a Lean theorem.
- **T18 ✓ Replay.** Take each store that the implementation writes. Replay
  its log from the empty state, with the logged founding key and
  `del_ttl` and with a data capacity that the replayed `F` fits in. The
  result has the same held set (and so the same views, the same horizon
  `hz(F)` and the same digests) and the same `seq_self`. Replay reruns
  `Put_Frame`, so its expiry is the live expiry. After compaction, each
  replayed `APPLY` succeeds. In SPARK, `Open_From_Log` proves T18-prefix
  (when `Valid_Length > 0`, the result is the `Valid` replay of exactly
  that prefix, `Replayed_Prefix`); that replay accepts every log that a
  store writes and gives back its frontier is tested there, not proved,
  and so is the claim that a compacted log never gets `LOG_FULL`.
  `Compact`'s Post (`Retagged`, `Compact_Layout`) states the layout up to
  the order and contiguity of the copied `APPLY`s, which are tested.
  (T15–T17 are reserved for typed fields, C10, and are not stated.)

**Assumptions.** The assumption IDs are fixed: a restated assumption keeps
its ID, and a new one takes the next free number.

- **A1** Ed25519 (RFC 8032) is unforgeable under the strict verification
  predicate of §2. Nobody ever steals the founding key, and its holder
  certifies at most 15 distinct signer keys (renewals of a key's cap are
  unlimited). While the founding device is lost, no root is added or
  root-voided (§6). A certified root can be stolen.
  Until a replica holds its root
  revocation, the stolen root can do there all that a root does (§6 gives
  the list). After that, all that it issued no longer counts in that
  replica's views. Under A7, nothing that it or its grantees sign
  afterwards reaches that replica. Its permanent residue is as follows:
  `maxceil` raised up to the largest cap ever certified for it; its records
  in its own slice; and, if it overflowed its slice, the disagreement about
  its surplus (§7). Honest roots stay within the authorization bounds
  (§7: `Signers_Max`, `Slice_Max`).
  Beyond these bounds, the owner must re-found the collection.
- **A2** BLAKE2b is collision-resistant. The 4096-bit sum is k-sum hard.
- **A3** A root device refreshes the roster within each horizon, and the
  refresh reaches every partition of the members, not only the one that
  holds the root device. (If not, writes degrade to ties at the ceiling,
  a stale writer's `DEL` can arrive expired at a fresher replica, and
  tombstone expiry freezes with the ceiling, §7. Convergence is not
  affected.)
- **A4** For tombstone expiry only: every `DEL` `d` is admitted and
  durably held (or durably applied for its effect: its `APPLY` is in the
  log) at every member within `del_ttl − Cap_Lead` of `d.t`, measured against the
  fastest replica's horizon; and no frame of a record that `d` dominates
  (a stale replica's, a relay's stored bundle, a saved frame, a backup) is
  delivered to a replica after that replica expired `d`. A lost log tail
  counts as a backup restore.
- **A5** Writers send a frame only after its `APPLY` is durable (the sync
  point, §8; AUDIT.md A21). `seq_self` lives in the log (§5), so nothing
  else needs to be persisted, and a frame lost in a crash was never sent
  (Kome detects violations: `CLONE_SUSPECTED`).
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
horizon `hz(F)` reads no clock: it is a function of each replica's `F`
(§7), so expiry, and only expiry, depends on the roots' ceilings, which
follow their clocks, and A3 and A4 are the assumptions that bound it.

## 10. What is open

1. **Lean model of this design.** `lean/Kome/Frontier.lean` proves the
   theorems below over finite lists. `lean/build.sh` checks the proofs by
   machine. There is no `sorry`, and the proofs use only Lean's standard
   axioms. The proof of T3 uses a general "sandwich" lemma. The exact
   scope of each check mark in §9 is this (`lean/README.md` names the
   theorems):
   - T1 (`StrictTotal Version`), T2, T2', T3: whole.
   - T4 (a) and (b): `auth_first`, `convergence_two_pass`, `convergence`,
     for `applyD`; `expire_applyAllH` and `expire_applyAllH_hz` relate the
     store's `applyH` to it under `NoLateDom`. T4 (c) is not proved (it is
     T7 delivery plus T4 (a)). `auth_first_closed` (and
     `auth_first_closed_H` under `applyH`) is the bundle rule of §8.
   - T4': whole (`adm_mono`, `maxCeil_F`, `isWriter_F`, `wcap_F`,
     `adm_F`; `maxceil` and `wcap` are instances of the family `maxP`,
     `maxP_cover`, `maxP_mono_auth`).
   - T5: `cell`, `deleted_at`, `exists`, `maxceil`, `W`, `root_void`,
     `W_eff`, `void` and `ROSTER_eff` (`cell_unique`, `deletedAt_congr`,
     `deletedAt_F`, `existsEnt_congr`, `rootVoid_F`, `wEff_F`, `voided_F`,
     `isMinFrom_F`, `rosterEff_congr`, `rosterEff_F`, `rosterEff_present`).
     `Roster_Max`, `contested` and `quarantined` have no Lean statement;
     they are SPARK views (`Kome.Views`), functions of `F` by their
     definition in §3.
   - T6: SPARK only (`Kome.Accumulator`, `Kome.Digest`); no Lean
     statement.
   - T8: the `t` clause (`chase`) and D8 (`lt_iff_prefix`); the `seq`
     clause (`seq_emit_gt`, `seq_emit_gt_self`), also proved in SPARK
     (`Kome.Emit`).
   - T9: the first clause (`adm_put_le`, `adm_put_le_wcap`), and after a
     raise `chase_after_raise`.
   - T10: by `StrictTotal Version`, `equivocation_ordered`, `convergence`
     and `convergence_empty`.
   - T11 (a) and (b): at the store's horizon `hz` (`hz_F`, `hz_mono`,
     `isExpiredAt_hz`, `expireHz_eq`, `expireHz_none`, `expireHz_only_del`,
     `expireHz_frontier`, `expireHz_adm`, `expireHz_admitted`,
     `expireHz_reapply`, `maxCeil_expireHz`), and at a general horizon
     (`expire_none`, `expire_only_del`, `expire_frontier`, `expire_adm`,
     `expire_admitted`, `expire_reapply`). T11 (c) is argued under A4, not
     proved.
   - T12, T13 (`emitT_le`), T18 (`auth_first`, over sets): whole.
   - T7 is open. T14 has a paper argument only. T15–T17 are reserved for
     typed fields (C10) and are not stated.

   The model has the five record kinds, per-signer product-order roster
   domination (strict in `gen`, ceiling not lower; no epoch and no
   `del_ttl` field), per-`(issuer, subject)` grant domination (with the
   cap) and per-`(issuer, subject)` revocation domination (a lower
   `from_t`, or an equal one and a greater `h`). It also has `maxceil`,
   `W` and `wcap` as functions of the held list, the discard model
   (`applyD`), the store's apply with expiry at the horizon of the state
   it reaches (`applyH delTtl = expireHz delTtl ∘ applyD`), with `delTtl`
   a constant of the model and `hz` its horizon, expiry, the roster key
   `rkey = (gen, h, signer, ceiling)`, and the views `rootVoid`, `wEff`,
   `revokeVoids`, `voided` and `rosterEff`.

   This list is the **only divergence register**: what the implementation
   has and the model does not. Where a SPARK contract is intentionally
   different from the model, its comment says so and the difference is
   listed here (`spark/CONVENTIONS.md`).
   - No signer certificates and no well-formedness: the model assumes
     well-formed records.
   - No `cid`: the model is one collection.
   - No capacity: no `NO_SPACE`, `AUTH_FULL` or `LOG_FULL`.
   - No `Cap_Lead`: the model's horizon is `hz delTtl`, the same function
     as the store's `Hz`, and the model has no write lower bound.
   - `Nat` for `u48`: the model has no bound on `t`, `seq` or `gen`.
   - No journal: the model has no log, no tags, no `seq_self` in the log
     and no replay; T18 is the set-level `auth_first`.
   - Expire-on-arrival: the store and Lean's `applyH` expire at `hz(F)`,
     and the model's `applyD` holds the `DEL`; they agree under
     `NoLateDom` (T4 (b)).
   - Outside the model: `Roster_Max`, `contested`, `quarantined`, the
     gate, the digests and assumption A7.
2. **Toolchain.** `lean/build.sh` and `spark/check.sh` get Lean and the
   GNAT, gprbuild, gnatprove, cvc5 and z3 tools from the nixpkgs revision
   that `nixpkgs.pin` names when they are not on the path.
   `lean-toolchain` gives the Lean version for users of `elan`.
   `spark/kome_spark.gpr` has a `Mode` scenario: `check` (the default,
   with `-gnata`, every contract executed) and `release`
   (`-XMode=release`, no run-time contract checks), and CI builds both.
3. **Root ceremonies (`Kome.Roster`, phase 8).** This document specifies
   these items, but they are not built yet:
   - certification (short caps, renewed), with the **ceremony log**: the
     founding device records every `Make_Cert` it performs, and "the
     largest cap ever certified for a root" is read from that log, not
     from `F` (a dominated roster takes its certificate with it, so no
     view of `F` can give it); there is no `CERT` record kind; the
     founding ceremony makes the founding key's self-certificate,
     `Make_Cert (root_sk, cid, root_pk, 2^48 − 1)`;
   - the roster key: draw `rnd` for each roster, derive `k_g` with
     `Kome.Epochs.Key_For_Gen` (draw again if it is `Zero_Key`), and keep
     the previous key for the store-and-forward sender rule (§6);
   - the recovery procedure (§6), in its order: re-issues first, the
     root-void fourth, the recovery roster last;
   - **enrollment**: a member's `(sign_pk, dh_pk)` reaches the root out of
     band, and Kome cannot authenticate it (a substituted `dh_pk` gets read
     and gate access). The two parties compare a short authentication
     string, or a QR code, over `BLAKE2b-256("kome/member" ‖ ns ‖ sign_pk
     ‖ dh_pk)` before the root lists the entry. The join hand-off to the
     new device is `(root_pk, salt, del_ttl, the frame of the roster that
     lists it)` (§6, Joining);
   - **key rotation**: a member proposes a fresh `dh_pk` (the same check),
     the next roster lists it and drops the old one, and the roots re-key
     every member on a schedule, because there is no post-compromise
     security (§6, T14);
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
     stolen root can issue `gen` up to its cap; the founding recovery
     roster wins by `gen`, because the founding key is uncapped, §6 step
     5.) A restored root that holds its own roster with `gen ≥` its next
     `gen` issues at `1 + max`, which resolves the pair that `contested`
     reports.
   - Its `ceiling_t` is at least the largest ceiling of the signer's held
     rosters, and at least its `gen` (§2 rule 2). So it dominates all of
     them, and the signer keeps one roster.
   - Contested (§6): if `contested(F)` holds, the next roster has a `gen`
     above every held roster and the confirmed union of the members of
     `ROSTER_eff` and of the contesting rosters.
   - A member removal is a new roster without the member, under a fresh
     `k_g`. A sixty-fifth member is refused: `Members_Max` = 64 is the
     number of devices that can pass the gate of a collection, and the
     issuer tells the owner rather than silently drop an entry.
   - A root stays within its slice (`Slice_Max` records), and the founding
     key certifies at most 15 distinct signer keys (`Signers_Max − 1`,
     A1). Renewals of a certified key's cap are unlimited and take no
     slot; a renewal is a certificate, not a record.
   - The founding key keeps a *reserve* for root-voids: it signs an
     authorization record other than a root-void only if
     `slot_count(1) + 1 ≤ Slice_Max − (15 − roots_already_voided)`. It
     does no routine `GRANT`s or `REVOKE`s (E1).
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
     `skew = now_local − maxceil` (§3) reports a status when it passes a
     bound, so that a device can see a ceiling that runs ahead.
   - A recovery roster (§6 step 5), and any founding roster issued while
     `maxceil(F) > now`, has `ceiling_t = max(intended, maxceil(F) + 1)`.
   - After `ROSTER_eff` changes, a replica sends, for a set period, an
     authorization-only bundle under the previous key with the new roster
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
   until `maxceil ≥ t_flood + del_ttl`. The purge of a
   revoked writer is entity-grained (§6): its own entities are deleted,
   and its junk fields on honest entities are overwritten with empty
   `PUT`s. The quota protects honest room but makes no guarantee stronger,
   and the correct bound depends on the application. A per-author byte
   quota in the roster, enforced by the application, would not touch the
   lattice.
6. **The C ABI.** It is not designed yet. The packages give its shape:
   `set/get/exists/scan` over records, `delete(ent)` (the only
   removal, entity-grained, §2), `GRANT`, `REVOKE` and roster operations,
   `session_*` over Kome.Reconcile, and a digest whose value is equal to
   the sync fingerprint. There is no field-level delete; an item that must
   be removable on its own is its own entity. Statuses are Kome's
   `Status`, including `AUTH_FULL`, `LOG_FULL`, `BUSY` (`Compact` while a
   session pins the log, §7) and, from the storage binding, `DEGRADED`
   (§7). `CLAMPED` is the out flag next to a write's status, and
   `CLONE_SUSPECTED` comes from `Clone_View` and from `Receive` (§5).
   `skew` past a bound, `contested` and `quarantined` are replica
   statuses (§3, §6), as is a `NO_SPACE` refusal of a peer-offered record.
   The key API generates keys and never imports or exports one (§10.3).
7. **Typed fields.** The extension (C10) composes with the core. Build it
   when an application asks for counters or sets in the engine. Its
   lattice rule is in §4: a typed record kills another only with the
   same author, a greater version and a state that contains the other's;
   an author's non-inflationary states leave an antichain that the view
   joins and that counts against the data capacity; a `DEL` of the
   entity dominates typed cells as it dominates LWW cells. T15–T17 state
   the per-author inflation obligation and are not written yet.
8. **Round 0: one-round set difference (C8, an optional extension;
   `SIMPLIFY.md` S23).** It is not built, and no phase owns it:
   `Kome.Reconcile` has no wire tag, no fetch-by-hash message and no
   pending-weight rule for it. At the start of each phase, each side
   could send an invertible Bloom lookup table over the 32-byte element
   hashes of that phase's range. The `HELLO` counts would set the size of
   the table, and a clamp would make one sketch fit in one message (at
   most 1 000 cells of 44 bytes at the current `Max_Message_Len`; a larger
   message bound gives a larger cap). A side subtracts the two tables and
   peels the result. This gives the exact symmetric difference in one
   round if the difference is small. Kome would detect a peel failure and
   a false decode before it writes any state: each recovered hash must
   verify against a held or received record, and if either occurs, the
   phase continues with the range protocol of §8. The sketch is
   homomorphic, so a store could keep it per collection and update it per
   record, like the digests. It adds nothing to the trusted core: Kome
   still delivers and checks as a record each element that the sketch
   names. H4 is met without it, by the range split.
9. **Interoperability residue.** Kome never encodes a record's frame again,
   so a second implementation can check Kome records with BLAKE2b and an
   Ed25519 verifier. It needs the collection's `(root_pk, salt, del_ttl)`,
   not only `ns`: every record's `h` is `BLAKE2b-256(tag ‖ cid ‖ content)`
   with `cid = BLAKE2b-256(root_pk ‖ salt ‖ u48(del_ttl))`, which the frame
   does not carry, and every certificate signs a hash over the `cid` (§2;
   `spark/vectors/records.txt` has the `cid1`, `cert1`, `put`, `del`,
   `roster`, `revoke` and `grant` known answers). The verifier must compute exactly the **cofactored
   verification equation** of §2: canonical `A` and `R`, `A` not small-order, `S < L`,
   and `[8][S]B = [8]R + [8][k]A`. "RFC 8032" alone is not enough: the RFC
   permits both the cofactored and the cofactorless equation, and the two
   disagree on signatures that a malicious author can make (an `R` with a
   torsion component), so two replicas with different verifiers would
   never converge on such a record. The Wycheproof and torsion vectors in
   `spark/vectors/crypto.txt` are the normative test of a verifier. The
   accumulator's byte order (§8) is the other place where a second
   implementation must be careful.
10. **Log decisions made in the SPARK store.**
    - (a) Capacities: the slice is the compile-time constant `Slice_Max`
      at every replica, and the `HEADER` has no `slice` or `data_cap`
      field. The data capacity in force is the discriminant `Cap` of `F`,
      chosen by the binding at each open. A reopen with a larger or a
      smaller capacity is allowed whenever the log replays at it
      (`NO_SPACE` otherwise, with nothing written, and `Valid_Length`
      names the prefix that replayed). Nothing in the log is ever
      rewritten in place: the only writes are appends and the rename of
      `Compact`.
    - (b) Compaction: the Post of `Compact` states the layout up to order
      (`Compact_Layout`: the `HEADER` bytes, every record's `APPLY` before
      the final `SEQ(seq_self)`, `|F| + 1` entries; `Retagged`: `F`
      changed only in its tags), and `Valid` states that every tag points
      at an `APPLY` whose frame has that record as its header. That the
      copied `APPLY`s are contiguous and in row order (`Ord`), and that a
      compacted log never gets `LOG_FULL` (the held frames are disjoint
      parts of the old log), are tested, not proved; the check makes the
      second a refusal.
    - (c) Memory: a store holds its log (`log_cap` bytes) and the two
      digest states; the tags live in the frontier's slots, so there is
      no index and no table of entry boundaries. `Compact` writes the new
      log into a buffer of `log_cap + 1` bytes that the binding supplies
      (the image of the new file) and copies only the new length back.
      `Open_From_Log` replays against its input in place, so the input
      (the file, which a binding can map) and the store's log are both
      resident while a store opens.
11. **Not done, on purpose (`SIMPLIFY.md`).** These were weighed in the
    simplification and left as they are:
    - A structural founding reserve (a dedicated row for root-voids): the
      E1 reserve rule works.
    - Sizing the authorization matrix by the slots in use (memory only),
      and a data-only header type (`Header` without `Issuer` for data).
    - `HELLO` sending `h(cred)` before the credential: one more round trip
      for a few KB.
    - A per-entry BLAKE2b check in replay: trusted replay relies on the
      host's integrity of the log (§7).
    - A linear snapshot: the frontier keeps the authorization rows by
      slot in arrival order, which is local to a replica, so
      `Snapshot_Of` insertion-sorts the at most 8 192 authorization
      records (`O(n_auth²)` in the worst case, proved; its run-time checks
      are off, `IMPLEMENTATION_PLAN.md`). A linear merge needs the
      frontier to keep its slots ordered by signer.
    - Release of a captured replica by a peer that holds `REVOKE(R)` but
      not the recovery roster: with no pre-gate message (`SIMPLIFY.md`
      S11), only a member that holds the recovery roster releases it, as
      its `HELLO` credential (§6).
    - A reserved ceiling cell per slot for the `AUTH_FULL` arrival-order
      case of `maxceil` (AUDIT.md H12): deferred (§7).
