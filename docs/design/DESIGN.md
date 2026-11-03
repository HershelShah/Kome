# Kome: the frontier store

**Decision.** Build Kome on a single lattice. This lattice is the *frontier*
of a set of signed records under one strict total order. No policy question
(authorization, far-future clocks, revocation) is part of the merge. Each
policy question is either a monotone admission rule or a pure view. §1 gives
the decisions, §2–§8 give the design, §9 gives the theorems, and §10 gives
the open items.

## 1. Decisions

**The governing rule.** The frontier lattice is sound if and only if every
kill predicate is a down-set of the record order on its key. Apply this rule
first to every proposal. No decision below breaks the rule, and no decision
changes the version order.

### 1.1 The core

| # | Decision |
|---|---|
| C1 | The state is the frontier. Merge is set union. Then merge drops every record that a newer record on its key dominates (§3). |
| C2 | The ceiling is a *monotone* admission rule, not an arrival gate. The store refuses a record above `maxceil`, and admission never shrinks (§4). |
| C3 | Tombstones use apply-then-expire, not refuse-on-arrival. The store holds a `DEL`, and the `DEL` dominates. Only expiry at a horizon removes it (§7). |
| C4 | Cross-author `DEL`s dominate in the store, so deletion is durable and needs no membership knowledge (§3). |
| C5 | There is no self-tombstone rule and no device-global clock adoption. A writer's clock affects only that writer's records (§5). |
| C6 | Revocation carries a `from_t` and is a view, not a gate. It voids records in the views and never feeds admission (§3, §6). |
| C7 | Read control uses hash-chained epoch keys (§6). |
| C8 | Reconciliation starts with a one-message IBLT sketch. Then it uses the range split (§8). |
| C9 | There are several root keys, and the founding key certifies them. So the loss of a root is recoverable. There are no per-field writer rules (§6). |
| C10 | Typed fields (counters, sets, multi-value registers per `(cell, author)`) are a specified extension. Build them only when an application needs them. They need `W`, a saturating fold, and a cursor to read the view output (§4). |

### 1.2 Authorization, storage and wire

| # | Decision |
|---|---|
| D1 | Every authorization record carries a *signer block*. The signer is the founding key or a root that the founding key certified (`cert_sig` over `ns ‖ signer ‖ cert_cap`). Only the founding key certifies, so only the founding key adds roots. Admission depends only on the bytes (§2, §6). |
| D1′ | A record kind `GRANT(subject)` holds write access. Its key is `(ns, issuer, subject)`. `W(F)` is the set of `GRANT` subjects in `F`. `maxceil(F)` is the largest `ceiling_t` of the rosters in `F`. A roster leaves `F` only under a roster of the same signer with a ceiling at least equal to its own. The two registers are functions of `F`, and they never shrink (§3, §4). |
| D2 | Only the founding key root-voids. The store ignores `from_t` for a root-void. Nobody can revoke the founding key. When a root is root-voided, all that it issued (rosters, `REVOKE`s, `GRANT`s) no longer counts in any view. Keys that only that root granted read `void` through the effective-writer view `W_eff` (§3, §6). |
| D3 | Canonical form is a property of `Header`. Decode produces it, and the lattice requires it. A roster dominates another roster of its signer if and only if it is greater in `(gen, h)` *and* not lower in `ceiling_t` (a product order). `ROSTER_eff` is the `(gen, h)`-maximum, and the whole roster tuple breaks a tie (§3). |
| D4 | Signatures are RFC 8032 Ed25519 (with SHA-512 inside the signature). They come from the `monocypher-ed25519` part of monocypher. Tests check them against RFC 8032 and Wycheproof vectors. BLAKE2b is the hash for all values that Kome derives (§2, A1). |
| D5 | There is no root X25519 key. Each `ROSTER` carries a fresh ephemeral `box_pk`, and the roster signature covers it. The secret of `box_pk` seals that roster's boxes, and then the signer wipes the secret (§2, §6). |
| D6 | `wrap_key` hashes the DH output with `box_pk`, the two member keys, `ns` and `epoch`. The box nonce is synthetic, `BLAKE2b(wrap_key ‖ k_e)`. The member calculates it again and checks it. Bundle nonces are also synthetic (§6). |
| D7 | The accumulator is little-endian and recorded exactly. The tags are bytes (§8). |
| D8 | The write path selects `(t, seq)` without `h`, and then it calculates the hash. The result does not depend on `h`. `seq_self` is per collection (§5). |
| D9 | Kome persists only `F`. The log is a `HEADER` (`ns`, `root_pk`, `salt`, capacities) and a journal of `APPLY`, `APPLY_EXPIRED` and `EXPIRE` entries. The store logs `EXPIRE` only when it removes a record or lowers the horizon. Compaction writes authorization records first. Replay gives the same frontier as a set (T18, §7). |
| D10 | Expiry is an operation on the lattice state at `horizon = min(now_local, maxceil) − del_ttl_eff`. `del_ttl_eff` is the largest `del_ttl` of the rosters that are not root-voided (decode clamps each value). So a stolen root can make tombstone life longer but never shorter (§7). |
| D11 | The order of checks is admission, duplicate, domination, room. A dominated record never needs room. No refusal changes anything (§7). |
| D12 | `Value_Max` = 40 960, so every frame fits in one 48 KiB message (§2, §8). |
| D13 | No register value goes on the wire. A pre-gate `OPEN` carries `ns` and the founding-issued `REVOKE`s of roots that the sender holds. The receiver applies them *before* it evaluates the gate. The post-gate `HELLO` carries counts, the digest and the sender's credential roster. That roster must list the sender's Noise key. A side sends `HELLO` only to a peer that it has already admitted. The authorization range is fully reconciled before the data range (§6, §8). |
| D14 | The session phases are `Auth` and then `Data`. Only the initiator sends root `RANGE`s: exactly two, with fixed bounds. Replies are exact windows. Items apply in key order (§8). |
| D15 | Prefix sums carry one more entry, the total. Any sub-range costs at most 64 additions and one subtraction, with the two-accumulator scheme (§8). |
| E1 | Data records have one capacity. Each signer has its own *slice* of authorization capacity, and the founding key's slice is reserved. The capacity of `W` is the total of the slices, so `W` never fills on its own. A data flood cannot fill another party's space, and a stolen root cannot either. So the founding key's `REVOKE` always lands (§7). |
| E2 | If an authorization record would exceed its signer's slice, the store refuses it with `AUTH_FULL` and changes nothing. The store never drops a key silently (§7). |
| E3 | There is one hash chain per collection, in *segments*. Only the founding key opens a segment (on root-void, or when the chain reaches the top of a segment). Each roster carries links that let a member walk back across segments (§6). |
| E4 | `from_t` gives protection only against a lost key, not against a key that a thief uses. For a stolen key, revoke from 0 (§6). |
| E5 | Keys are canonical at decode: `box_pk`/`dh_pk` are reduced and not low-order, `del_ttl` is clamped, and the cert block is zero exactly for the founding key. Each record has one encoding (§2). |
| E6 | `root_pk` must be equal to the store's founding key. The effective certificate cap is the largest cap ever certified (§6). |
| E7 | Admission does not refuse the records of a revoked key. Instead, the design states assumption A7 (a revocation reaches a replica before the records that its subject signs after it), and the H8 bounds depend on it. A refusal would give a stolen root a permanent primitive for mass deletion, and it would give up T3 (§6, §9). |
| E8 | The engine has no per-author data quota. A quota refusal is a capacity refusal, and under a flood the replicas would not agree about it. It stays an application policy (§10.5). |
| E9 | The frontier keeps one data array and one authorization row per signer slot. Its own discriminant sets the limit of each one (§7). |

## 2. Objects

**Identifiers.** A collection `ns` is 16 bytes and self-certifying:
`ns = BLAKE2b-256(root_pk ‖ salt)[0:16]`. `root_pk` is the collection's
**founding key**. An entity `ent` is 16 bytes. A field name is 1–32 bytes.
A value is 0–40 960 bytes. Blob chunks of 32 KiB fit, and a layer above the
engine cuts larger payloads into chunks. This bound makes every frame fit in
one reconciliation message (§8). An empty value is a value.

**Version.** `v = (t : u48, author : [32]u8, seq : u48, h : [32]u8)`. Kome
compares versions lexicographically, with `author` and `h` as unsigned
256-bit integers. `h` is the record's content hash, so two different
records never compare equal, and the order is total by construction.
`t = 0` and `seq = 0` are ordinary values.

**Records.** A frame is `tag:u8 ‖ content ‖ sig[64]`, and `h = BLAKE2b-256(tag
‖ content)`. `sig` is an Ed25519 signature (RFC 8032, strict: `S < L`) by the
record's signer over the 32 bytes of `h`. All integers are big-endian. All
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
roots. Certification occurs out of band (in a key ceremony). Then the
certificate goes inside every record that the root signs. Keep the founding
key cold (offline, or in a hardware token). The founding key signs
certificates, root revocations and an occasional roster, and nothing else.

To renew a certified root's `cert_cap`, the founding key issues a new
certificate. Nobody can narrow or withdraw a certificate. Every certificate
stays valid for every record, so **a root's effective cap is the largest
`cert_cap` ever certified for it**. Only root-voiding (§6) ends what
a certificate allows. So make caps short (some weeks ahead of the wall
clock) and renew them regularly. The cap is also a dead-man switch: if the
founding device is lost, `maxceil` stops at the largest cap when wall time
passes it (§6).

**Well-formed** is a function of the bytes alone. A frame is well-formed if
and only if all these conditions are true:

1. Its length is exactly the layout's length, `flen` ∈ 1..32,
   `vlen` ≤ 40 960, `n_links` ≤ 15, and `n_members` ≤ 64.
2. For `ROSTER`, `REVOKE`, `GRANT`: `ns = BLAKE2b-256(root_pk ‖ salt)[0:16]`,
   the signer block is valid as above, and a `ROSTER` that a certified root
   signs has `ceiling_t ≤ cert_cap`.
3. For `ROSTER`: `del_ttl` ∈ [`Del_TTL_Min`, `Del_TTL_Max`] (7 days and
   3 650 days, in milliseconds). `box_pk` and every member `dh_pk` are
   reduced X25519 encodings (`u < 2^255 − 19`, bit 255 clear). None of them
   is one of the five reduced low-order encodings (0, 1, `p − 1`, and the
   two points of order 8). So every listed member can open its box (E5).
4. For `REVOKE`: `sign_pk ≠ root_pk` (nobody can revoke the founding key).
5. The signature is valid under the signer (authorization kinds) or the
   author (data kinds).

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
                            (r'.gen, r'.h) > (r.gen, r.h) ∧ r'.ceiling_t ≥ r.ceiling_t
dom(g, H) for GRANT g  := ∃ g' ∈ H : GRANT, same ns, same issuer, same subject, g'.h > g.h
dom(x, H) for REVOKE   := false
F(H) := { x ∈ H | ¬ dom(x, H) }
```

Each kind carries its identity in one version. Each clause above implies
that the dominator's version is greater on the record's key:

| Kind | `v` | key on which `dom` compares | order on the key |
|---|---|---|---|
| PUT | `(t, author, seq, h)` | cell `(ns, ent, field)`; also a DEL of its entity | `v` |
| DEL | `(t, author, seq, h)` | entity `(ns, ent)` | `v` |
| ROSTER | `(ceiling_t, signer, gen, h)` | `(ns, signer)` | product of `(gen, h)` and `ceiling_t` |
| GRANT | `(0, subject, 0, h)` | `(ns, issuer, subject)` | `h` |
| REVOKE | `(from_t, subject, rev_seq, h)` | none: never dominated | — |

The roster clause is a product order (D3). Suppose that the order put the
roster ceiling first. Then a stale roster with an old `gen` and a current
clock could evict the newer roster permanently. (A root restored from backup,
or a second device that holds the same root key, can make such a roster.)
This would roll back a member removal and the epoch. Under the product order,
neither roster dominates, and both stay until the root issues a new roster
above both.

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

`W` decides admission and `W_eff` decides views. The only difference between
them is the grants of root-voided issuers. Admission cannot drop these
grants, because admission must stay monotone (§4). So the keys that these
grants name stay admissible, and the store holds their records.
But each such record reads `void`, unless an issuer that is not root-voided
also granted its author.

`del_ttl_eff` is a maximum, so a root can make tombstone life longer but
never shorter than the value that another root set. A shorter life is
irreversible (expired tombstones are gone). To undo a longer life, root-void
the root that set it.

There is no presence bit and no sentinel. An entity exists if and only if it
has a live field. A deleted entity is a `DEL` and nothing else.

`maxceil` and `W` lose nothing to domination. A roster leaves `F` only under
a roster of the same signer with a ceiling at least equal to its own. A
`GRANT` leaves `F` only under a `GRANT` of the same issuer and subject. With
T2', each dominated record has a dominator that is not dominated. Thus
`maxceil(F(H)) = maxceil(H)`, `W(F(H)) = W(H)` and `W_eff(F(H)) = W_eff(H)`.
The frontier's registers are the registers of all records ever applied,
and they never shrink (T4').

Also, `ROSTER_eff(F(H)) = ROSTER_eff(H)`, because a roster that dominates
another roster has a greater `(gen, h)` and the same signer. `ROSTER_eff` is
present when `F` holds a roster that the founding key signed. The
collection's first roster is such a roster.

## 4. Admission

Kome admits every well-formed authorization record (`ROSTER`, `REVOKE`,
`GRANT`). Kome admits a `PUT` or `DEL` if and only if `t ≤ maxceil(F)` and
`author ∈ W(F)`. The two registers are the derived views of §3. They are
functions of the frontier, not separate state. They only grow, because
admission of authorization records is unconditional and their domination
never lowers either register (§3).

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
the data records again under the joined authorization records. Kome applies
each batch of records that arrive together (a bundle, an import) in
element-key order (§8). This order puts authorization records first. That is
the authorization-first pass of T4 (a). So Kome never discards a data
record that arrives in the same batch as the grant that admits it, but
before that grant.

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
- The `PUT`-over-`PUT` clause of `dom` gets the condition `(ftype = LWW ∨
  same author)`.

Then the frontier holds at most one record per `(cell, author)`, and `|W|`
sets the limit. The cell's value is a join over the per-author records
that survive and are not void. LWW cells do not change. The extension needs
`W`, a saturating fold, and a cursor to read the view output. It is not on
the critical path. Today, an application can get the same semantics with one
LWW sub-cell per device.

## 5. Clocks and writing

There is no engine clock, no `tick` and no `receive`. Kome adopts nothing
from a peer. So a far-future record of one collection can never carry into
another collection on the device.

```
floor(cell)  := max(cell(ns,ent,f).v, deleted_at(ns,ent))     -- for DEL: max over all fields and deleted_at
t_emit       := max(now_ms, floor.t + 1 if floor exists); if t_emit > maxceil then t_emit := maxceil
seq_emit     := seq_self(ns) + 1, and above every seq of this device's records held in F(ns);
                at 2^48 − 1 the write fails SEQ_EXHAUSTED, no record is produced
v_emit       := (t_emit, self_pk, seq_emit, h)
status       := SHADOWED if floor exists ∧ v_emit < floor   (only when t_emit = maxceil) else OK
```

**The write path has three steps (D8).** `h` hashes content that contains
`t` and `seq`, so `h` cannot be an input to the step that selects them:

1. *Choose* `(t_emit, seq_emit, status, clone_suspected)` from the frontier,
   the target cell, `now_ms`, the device key and `seq_self(ns)`. This step
   does not use `h`.
2. *Build* the `PUT` or `DEL` content with that `(t, seq)`, and hash it.
3. *Sign* and apply. Persist `seq_self(ns) := seq_emit` (A5).

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
works: all its writes chase. `seq_self(ns)` is the only persisted clock
state.

`seq_self(ns)` is **per collection**. The device keeps it per
`(device key, ns)` next to that collection's store. So if a thief forces
a jump to `2^48 − 1` in one collection, only that key's counter in that
collection is exhausted. `SEQ_EXHAUSTED` is a clone alarm. The
device moves to a fresh key in that collection (a new `GRANT` and roster),
and a root revokes the old key.

**What a writer that misbehaves can do (H8).**

| Case | Effect | Bound |
|---|---|---|
| Clock ahead by δ | It wins concurrent conflicts on the cells that it writes, for δ. Those cells then resolve by chase (arrival order), not by wall time | δ ≤ maxceil − now; only cells it touched; automatic |
| Clock behind | It loses concurrent conflicts; its own cells still chase | its cells only; a corrected clock has an effect immediately |
| Backup restore | It emits old `seq` values again: equivocation, ordered by `h`, flagged. Peers offer the old records again, and they are dominated unless the `DEL` has expired (§7) | The writer detects it (it holds its own record with `seq ≥ seq_self + 1`). `seq` jumps past it. The write succeeds and reports the flag `CLONE_SUSPECTED` |
| Cloned key | Continuous equivocation; replicas still agree | flagged; the owner issues `REVOKE(old, 0)`, a `GRANT` for a fresh key and a roster |
| Malicious | It can overwrite or delete any cell (that is what write access means). It can pin cells to `maxceil`, flood entities, and grind a public key that wins ties at the ceiling. It can force its own `seq` to `2^48 − 1` in the collections where it writes | It cannot forge, and it cannot go above `maxceil`. A flood cannot block the `REVOKE` (§7 capacity classes). Under A7: when a replica holds the `REVOKE` and the roster that removes the key, nothing that the key signs reaches that replica. So pins stop at the next roster refresh, and floods stop at the `REVOKE` plus owner `DEL`s. Without A7: a stale replica (one without the `REVOKE`) can admit the key to a session, or take its bundle under the old epoch. That replica then relays what the key signs to every replica. Each replica admits it and flags it `void`. The bytes that it overwrites or deletes are gone |
| Root restored from backup | It issues a roster with an old `gen`. If its own held roster is above that roster in `(gen, h)` with a ceiling at least as high, the old roster is dominated on arrival (status `DOMINATED`). If not (a current clock), neither roster dominates, Kome holds both, and `ROSTER_eff` is still the newer `(gen, h)`. After sync, the root issues a new roster above both. `maxceil` never decreases, and no `REVOKE` is lost | It converges in both cases; a stale roster never becomes effective |

`CLONE_SUSPECTED` is a flag that Kome reports next to the write's
status. It is not a status: the write occurred.

This is the honest statement of the residual risk: **LWW cannot undo the
effect of a wall clock that was ahead**. If a writer pushed a cell's floor
far ahead, the cell resolves by chase until wall time passes that
floor. The ceiling sets a limit on how far; it does not prevent it. A thief
can overwrite records before the revocation reaches a replica. These
overwrites stay, flagged `void`, and the bytes that they replaced are gone.
This is acceptable, because each such act is signed, attributable and
bounded, and it stops at the revocation plus one refresh.

It stops at each replica when that replica holds the revocation. It stops
everywhere only if no stale replica accepts the key's later records
first. This is assumption A7 (§9). Offline-first operation makes stale
replicas normal, so A7 is a deployment duty. Revoke promptly. After a
revocation, sync each device before it talks to anything else.

## 6. Authorization, encryption, revocation

**Roots (C9, D1).** A collection has one founding key (`root_pk`, from which
Kome derives `ns`). It has up to 15 certified roots during its life
(`Signers_Max` = 16 signers in total). Any root, founding or certified, can
sign `ROSTER`, `REVOKE` and `GRANT`. Only the founding key certifies a root
(§2). A record's bytes tell if its signer is a root, so admission of
authorization records needs no history. A replica that joins late can
never refuse a `REVOKE` that every other replica holds. Also, a roster never
waits for the roster that introduced its signer.

Roster domination is per signer (§3). The effective roster is the view
`ROSTER_eff` (§3): the `(gen, h)`-maximum over the frontier rosters whose
signer is not `root_void`. If two roots race with equal generations, `h`
resolves the race. `REVOKE`s are grow-only, so no race can lose one.
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

**Recovery from a stolen or lost certified root `R`.** The founding key does
these steps together:

1. It issues its own `GRANT` for each key that `R` granted and that the owner
   wants to keep as a writer. (If not, those keys read `void` after step 2.)
2. It issues `REVOKE(R, 0)`.
3. It signs again each member revocation of `R` that it wants to keep.
4. It issues a founding-signed roster that opens a new epoch segment
   (below). It gives the new top to the other roots out of band.

Keys that `R` granted and that the owner does not recognize need no action.
`W_eff` voids them, and also each key that `R` makes later. The root
revocation reaches captured replicas through `OPEN` (below).

**What a stolen certified root can do.** Until a replica holds its root
revocation, the stolen root can do there all that a root does:

- It can grant writers, who can overwrite or delete any data.
- It can make its roster `ROSTER_eff` (with `gen = 2^48 − 1`). Then it
  decides who passes the session gate and which epoch bundles use, and it
  can lock honest members out.
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
degrade to ties at the ceiling (A3). Also, nobody can add or root-void a
root until the key is restored from its offline backup. This is why the
founding key stays cold, with an offline backup.

**Membership is key possession.** The `ROSTER` wraps the current epoch key
to each member's `dh_pk`. Epoch keys make a hash chain
`k_e = BLAKE2b-256(k_{e+1} ‖ "prev")` within a *segment*. A member that holds
`k_e` derives each older key of the segment. So a new member needs one
box, and a removed member that holds `k_e` cannot derive `k_{e+1}`. 2^16
epochs are sufficient for the life of any collection.

**Epoch segments and several roots (E3).** There is one chain per
collection. The roots that are not `root_void` share it. A segment starts at
epoch `s` with a fresh random top key. The top key is at an epoch `top_s`
above `s` (for example `min(s + 4 095, 65 535)`). The roots receive the top
of the current segment out of band (at certification, and at each new
segment). Within a segment, each epoch key is a function of the top. So
two roots that issue rosters at the same epoch use the same key and never
conflict. A root never issues a roster with an epoch above `top_s`.

**Only the founding key opens a segment.** It opens a segment when it
root-voids a root, or when the chain reaches the top of the current segment.
It uses a founding-signed roster at epoch `1 +` the largest epoch of the
rosters in `F` that are not root-voided. (Kome ignores the epochs of a
root-voided root, so a thief cannot use up the epoch space.) A root-voided
root never sees the new top, so it cannot derive any later key.

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
key of a fresh ephemeral secret `eph_sk`. The signer draws `eph_sk` for that
one roster, uses it to seal the roster's member boxes, and then wipes
it. No root has a long-term X25519 key, and no key is used both to sign and
to exchange. Boxes get forward secrecy when `eph_sk` is wiped. For member
`(sign_pk, dh_pk)` of a roster of collection `ns` at epoch `e`:

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

The only randomness is the caller's `eph_sk` and the segment tops.
SPARK code reads no RNG. The construction is deterministic, and known-answer
vectors can test it. Decode refuses low-order and non-reduced peer keys
(§2), and the box code refuses them again.

**Two gates on transport, none on records.** Kome admits a peer to a session
for `ns` if and only if its Noise static key is the `dh_pk` of a member of
`ROSTER_eff`. Before each side evaluates the gate, it applies what the peer
sent before the gate. The `OPEN` message carries the founding-issued
`REVOKE`s of roots that the sender holds (signed records, admissible
everywhere). So one honest contact releases a replica whose `ROSTER_eff` a
root-voided thief took over (D13).

The credential `HELLO` follows. A side sends its own `HELLO` only after it
has admitted the peer, so a non-member learns no membership list. The
credential is a roster in the sender's `F` that lists the sender's Noise
key. The receiver refuses any other credential. The receiver applies
the credential and evaluates the gate again. So a newly added member can
still reach a replica whose rosters are stale (§8).

A replica can read a sealed bundle (mailbox, broadcast, BLE) if and only if
it holds the bundle's epoch key. Kome accepts bundles **only under
`ROSTER_eff.epoch`**. (If Kome accepted the previous epoch, a removed member
could write into up-to-date replicas for a full epoch.) So a captured
replica takes no bundle from honest members until an interactive session
releases it. The two gates decide who you talk to, never what a record
means.

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
records until the owner `DEL`s those entities. (An app-level "purge revoked
writer" routine issues the `DEL`s, and the tombstones then expire.)
Revocation does not remove `X` from `W`, and it never needs to: `W` only
admits, and `void` judges.

The gate keeps the *later* records of `X` out. A replica that holds the
revocation and the roster that removes `X` admits `X` to no session and
takes no bundle from it. A replica that does not yet hold them can admit
`X`. It then relays the records of `X` everywhere, where they are admitted
(flagged `void`). Assumption A7 (§9) excludes this, and the H8 bounds (§5)
depend on it.

**What `from_t` can and cannot do (E4).** With `from_t > 0`, a key's earlier
records stay unflagged. This is correct for a key that was *lost*
and that nobody used. It cannot give protection against a thief. A thief
selects `t` and can backdate below `from_t`, and nobody can tell such
records from honest ones. If a key is known or suspected to be stolen,
revoke it from 0. (Kome ignores `from_t` for root revocation, above.)

## 7. Storage and tombstone expiry

**The log is a journal of operations on `F` (D9).** The store of one
collection is an append-only log and an in-memory index `cell → (offset, v)`.
The log is sealed at rest under the device key (a later layer). The index
holds exactly the records of `F`. Per cell, version metadata is 6 + 6 + 32
bytes plus a cached 32-byte `h`. These are the log entries (all integers are
big-endian):

```
HEADER         op = 0 ‖ "kome/log" ‖ version:u8 ‖ ns[16] ‖ root_pk[32] ‖ salt[16] ‖ data_cap:u32 ‖ slice:u16
APPLY          op = 1 ‖ len:u32 ‖ frame        a record applied and held
APPLY_EXPIRED  op = 2 ‖ len:u32 ‖ frame        a DEL applied for its effect and not held (below)
EXPIRE         op = 3 ‖ horizon:u48            Frontier.Expire at this horizon, or a lowered horizon
```

The log starts with exactly one `HEADER` (`version = 1`; 80 bytes). Its `ns`
must be equal to `BLAKE2b-256(root_pk ‖ salt)[0:16]`. This fixes the
founding key for all the store's operations. Its capacities are the ones
that the store last opened with (§10 item 10). Kome persists nothing else.
The registers are functions of `F` (§4), and refused or dominated records
changed nothing.

**Compaction** writes a new log. The new log has the `HEADER`, then one
`APPLY` per record of `F`, then one `EXPIRE(horizon)` if the store has a
horizon. The `APPLY` entries put all authorization records first and then
all data records (each part in index order).

**Replay** (when a store opens) does these steps:

1. It checks the `HEADER`.
2. It requires that the capacities for this open are at least the logged
   ones.
3. It starts from the empty state with the logged founding key.
4. It does the entries in order.

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
     `NO_SPACE` (the caller compacts, deletes, or stops).
   - An authorization record whose signer's slice is full and that frees
     nothing, or whose signer is new when all 16 slots are in use:
     `AUTH_FULL`.
   - Not sufficient log bytes for the entry: `NO_SPACE`.

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
- the records that those data records dominate.

Honest roots never reach their slice (the honest-issuer rules, §10.3), and
the founding key certifies at most 15 roots (A1). So only a stolen root
can cause this. It cannot touch any other signer's slice. When it is
root-voided, all that its surplus admitted reads `void`. After that,
byte-for-byte agreement comes back only if the owner re-founds the
collection. The slice size must be the same at each replica of a collection
(the C ABI sets it to `Slice_Max`). Replicas with different slices would
disagree honestly.

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
`DEL`s that arrive expire on arrival.

If `horizon` is above the store's horizon, `Expire` removes from `F`
exactly the `DEL`s with `t ≤ horizon` and sets the store's horizon. If
`horizon` is below it (a clock stepped back, or a higher `del_ttl_eff`),
`Expire` only lowers the store's horizon. So fewer `DEL`s that arrive
expire on arrival, and A4′ does not become narrower. A `DEL` that `Expire`
already removed stays removed. If it arrives again, Kome applies it and
holds it until it expires again.

Kome logs `EXPIRE(horizon)` if and only if the call removed a record or
lowered the horizon. So periodic calls do not make the log larger. Kome
keeps a raise that removed nothing in memory only. A reopened store's horizon
is then at most the live one, so the store only holds more records
until its next `Expire`. The registers do not change, and when Kome removes
records from a frontier, the result is a frontier.

`del_ttl_eff` is the largest `del_ttl` of the rosters that are not
root-voided (§3). Decode clamps each value to [7 days, 3 650 days]. So a
stolen root cannot set it to zero to resurrect deleted data in bulk. It also
cannot make it shorter than the value that an honest root set. If the stolen
root makes it longer, this stops when the stolen root is root-voided. If
there is no horizon yet, nothing expires.

The second clause is **apply-then-expire**, not refuse-on-arrival. Kome
always applies a `DEL` that arrives with `t ≤ horizon` (it dominates and frees
the entity's values). Only after this, because the `DEL` is expired,
Kome does not hold it. If Kome refused an expired `DEL` on arrival, two
replicas with a skew of two milliseconds could diverge and then resurrect
the entity on both.

With apply-then-expire, a skewed pair converges on the next exchange. The
replica that still holds the `DEL` sends it again, and the other replica
applies and expires it again. The cost is one frame per session until the
two replicas expire it. The only residual is the documented one. A
straggler that never saw the `DEL` can connect again after `del_ttl`. It
then resurrects the entity with its stale fields, and the user deletes it
again.
That needs a device that is offline for longer than `del_ttl` (default 180
days). It is a liveness assumption (A4′), and the design states it as such
and does not hide it in a safety theorem.

**Why A4′ and not a sync-frequency assumption.** The assumption "every
member syncs with some member once per `del_ttl`" is not sufficient. A
four-member schedule can satisfy it while the `DEL` reaches two members and
both expire it. Then a third member that never saw the `DEL` seeds the
entity again everywhere. Expiry needs **A4′: every `DEL` reaches every
member within `del_ttl` of `d.t`**. That is, the sync-graph diameter times
the sync period is less than `del_ttl`. If this assumption fails, deleted
data comes back, but live data is never destroyed. For this reason, the
design prefers tombstone expiry to root-signed snapshots.

**Chased tombstones (residual).** A `DEL` that dominates a far-future `PUT`
must chase to `t > p.t`. So its tombstone lives for `δ + del_ttl`, where
`δ` is how far ahead the clock that pinned the entity was. `maxceil − now`
sets the limit on `δ`. Order on a separate counter would remove this
residual. But an expiry clock that the writer selects is worse than an
inflated clock. The residual is the storage of one tombstone frame per
pinned entity, for at most one horizon after `del_ttl`.

**Bounds.** After `Expire`, `|F(ns)| ≤ live cells + DELs younger than
del_ttl_eff + authorization records`. `data_cap` sets the limit on the data
part. `Signers_Max × Slice_Max = 16 × 512 = 8 192` records sets the limit on
the authorization part (each signer's rosters, `GRANT`s and `REVOKE`s,
within its slice). Thus `|W| ≤ 8 192`. There are no vectors, no per-peer
state, no shells and no pending buffers.

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

A k-sum attack on a 4096-bit modulus costs approximately 2^128 and needs
2^64 inserted records. A member could break a 256-bit sum in approximately
2^32. For this reason, the sum is 4096 bits.

**Messages.** All integers are big-endian. `g` is the size of a message's
reply group (0 only for a root `RANGE`).

```
OPEN      5 ‖ proto:u8 ‖ ns[16] ‖ n_rv:u8 (≤ 15) ‖ n_rv × frame[275]
HELLO     1 ‖ n_auth:u32 ‖ n_data:u32 ‖ digest[32] ‖ cred_len:u16 ‖ cred[cred_len]
RANGE     2 ‖ g:u8 ‖ lo[81] ‖ hi[81] ‖ count:u32 ‖ fp[32]
ELEMENTS  3 ‖ g:u8 ‖ lo[81] ‖ hi[81] ‖ n:u8 ‖ n × (key[81] ‖ flen:u32 ‖ frame)
HAVE      4 ‖ g:u8 ‖ lo[81] ‖ hi[81] ‖ n:u8 ‖ n × (key[81] ‖ flen:u32 ‖ frame)
```

**OPEN (pre-gate, D13).** `proto = 1`. `ns` is the collection. If `ns` does
not match, the session stops, so the digest that follows is bound to the
collection. The frames are the sender's **root-void set**. This set is
each founding-issued `REVOKE` in the sender's `F` whose subject signed an
authorization record that the sender holds. The set has at most 15
frames (`Signers_Max − 1`), so an `OPEN` is at most 4 144 bytes.

The receiver checks that each frame is a `REVOKE` that the founding key
signed. It verifies and applies the frames whose subject is a signer that it
holds and that is not yet root-voided. It skips the other frames without
verification, and this sets a limit on pre-gate work. Only then does it
evaluate the gate (§6). The frames are signed records that every replica
admits in any case. So it is safe to apply them before authentication, and
the transport sets a rate limit on pre-gate work per peer.

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
peer's credential, if it came first).

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
records (unless one side refused one with `AUTH_FULL`, §7). So they have
the same `maxceil` and `W`, and each data record that a peer sends in the
data phase is admissible on arrival. This makes the exchange clause of T4
true without registers in the HELLO. The initiator is the Noise initiator.

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
Within a phase, duplicate or reordered messages cost rounds, not
correctness.

But the phase gate assumes an in-order transport (Noise over a stream). If a
data root overtakes the last reply of the authorization phase, the receiver
refuses it, and the session then never completes. **If a message is lost, or
a root message is reordered, the session never completes.** The caller times
out and starts a new session from the `OPEN`.

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

**Transports.** Kome uses Noise XX for interactive sync, with the device's
`dh_pk` as the static key (§6 gate). It uses sealed bundles for
store-and-forward:

```
bundle = ns[16] ‖ u16(epoch) ‖ nonce[24] ‖ XChaCha20-Poly1305(k_b, nonce, AD = ns ‖ u16(epoch), plaintext)
k_b    = BLAKE2b-256("kome/bundle" ‖ k_epoch ‖ ns)
nonce  = BLAKE2b-256("kome/bnonce" ‖ k_b ‖ plaintext)[0:24]
```

Kome accepts a bundle only under `ROSTER_eff.epoch`. All members share
`k_e`, so the nonce must never come from a per-device counter. The nonce is
synthetic, as for boxes. Identical plaintexts give identical bundles, and
this shows only that the plaintexts are identical. The plaintext is a list
of `ELEMENTS` items, sorted by element key, with a total of at most
`Max_Message_Len` bytes. The receiver applies the items in element-key order
(authorization records first: the authorization-first pass of T4 (a)).
Relays see ciphertext, `ns`, the epoch and the transport's routing key.

## 9. Proof obligations

Each obligation is a finite, first-order fact about sets of records. ✓ marks
the obligations that core Lean can prove; ✗ marks the two hard ones.

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
    hold the same `F`.
  - (c) After a complete two-phase reconciliation (§8), the two replicas
    hold `F(F_A ∪ F_B)` of the admitted records. This includes records that
    were inadmissible at one side before the session.

  All three hold for runs with no capacity refusal (`NO_SPACE`,
  `AUTH_FULL`). Kome offers a `NO_SPACE` record again later, and `AUTH_FULL`
  is the stated residual of §7.
- **T4' ✓ Monotone admission.** If each authorization record of `H` is in
  `H'`, then `adm(r, H) ⇒ adm(r, H')`. Also, `maxceil(F(H)) = maxceil(H)` and
  `W(F(H)) = W(H)`. So no register shrinks along any history, and this
  includes rosters of lower generation or ceiling. Admission never reads
  `REVOKE`, `root_void` or `W_eff`.
- **T5 ✓ View determinism.** `deleted_at`, `cell`, `exists`, `maxceil`, `W`,
  `root_void`, `W_eff`, `void`, `ROSTER_eff` and `del_ttl_eff` are functions
  of `F` as a set alone (and of the constant `root_pk`). `ROSTER_eff` uses
  the whole roster tuple to break a tie, so it does not depend on list
  order, even without A2. Also, `W_eff`, `root_void` and `ROSTER_eff` of
  `F(H)` are equal to those of `H`.
- **T6 ✓ Digest.** `digest(ns) = fp(F|ns)`; `ACC(R₁ ⊎ R₂) = ACC(R₁) +
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
- **T9 ✓ Bounded pin.** No admitted data record has `t > maxceil`. After
  Kome applies a roster with a higher ceiling, no honest write to any cell
  is shadowed.
- **T10 ✓ Equivocation.** All replicas put two different records with equal
  `(author, seq)` in the same order. Arrival order has no effect on `F`.
- **T11 (liveness) Tombstone expiry.**
  - (a) After `Expire` at a horizon, `F` holds no `DEL` with `t ≤` that
    horizon, and `|F|` meets the §7 bound. Expiry of a frontier gives a
    frontier with the same registers.
  - (b) Apply-then-expire: take two replicas whose held sets are different
    only because one holds a `DEL` `d` with `d.t ≤ h` and the other does
    not. After the same further records, a re-sent `d` and an `Expire` at
    `h`, they agree on each record.
  - (c) Under A4′, after each replica has expired `d`, no replica holds a
    record that `d` dominated.
- **T12 ✓ Revocation locality.** When Kome applies a `ROSTER`, `REVOKE` or
  `GRANT`, `F` changes only at that record and at the records of its own
  kind and key that it dominates. It never adds or removes a `PUT` or `DEL`.
  `root_void` is monotone in `F`. For a fixed `root_void` set, the `REVOKE`
  clause of `void` and `W_eff` are monotone in `F`. (So a `GRANT` can only
  un-void, and a `REVOKE` can only void.)
- **T13 ✓ Bounds.** Each emitted record agrees with the §2 layout. `seq`,
  `t`, `gen` and `rev_seq` never wrap. At a bound, emission fails with no
  side effect. No refused apply changes the state.
- **T14 ✗ Epoch secrecy.** A key that is not in roster `e` and not in any
  later roster cannot derive `k_e'` for any `e' ≥ e`. A root-voided root
  cannot derive any key of a segment opened after its revocation. This is a
  paper reduction to hash-chain one-wayness, X25519 CDH, BLAKE2b as a PRF
  and XChaCha20-Poly1305 with a unique `(key, nonce)` per plaintext. It is
  not a Lean theorem.
- **T18 ✓ Replay.** Take each store that the implementation writes. Replay
  its log from the empty state, with the logged founding key and with
  capacities at least the logged ones. The result has the same held set
  (and so the same registers and digest) and the same index entries, both as
  sets. The replayed horizon is at most the live one. After compaction, each
  replayed `APPLY` succeeds. (T15–T17 are reserved for extension F.)

**Assumptions.**

- **A1** Ed25519 (RFC 8032) is unforgeable under strict verification.
  Nobody ever steals the founding key, and its holder certifies at most 15
  roots. A certified root can be stolen. Until a replica holds its root
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
- **A3** A root device refreshes the roster within each horizon. (If not,
  writes degrade to ties at the ceiling. Convergence is not affected.)
- **A4′** For tombstone expiry only: every `DEL` reaches every member within
  `del_ttl` of `d.t`.
- **A5** Writers persist `seq_self` per collection (Kome detects
  violations).
- No assumption about register values on the wire is necessary, because no
  register value goes on the wire.
- **A7 Revocation arrives first** (E7). Each replica receives a `REVOKE`
  before it receives any record that the subject of that `REVOKE` signed
  after it. Each replica also receives a root revocation before any record
  that a key granted by that root signed afterwards. Only the H8 bounds (§5)
  and the post-revocation guarantees of §6 depend on this assumption;
  convergence does not. If it fails, a stale replica admits such records and
  relays them. Every replica then holds them, flagged `void`, and the bytes
  that they overwrote or deleted are lost.

**There is no clock assumption for convergence.**

## 10. What is open

1. **Lean model of this design.** `lean/Kome/Frontier.lean` proves T1,
   T2, T2', T3, T4 (`auth_first`, `convergence_two_pass`, `convergence`),
   T4', T5, T8, T9, T11, T12, T13 and T18 over finite lists. `lean/build.sh`
   checks the proofs by machine. There is no `sorry`, and the proofs use
   only Lean's standard axioms. The proof of T3 uses a general
   "sandwich" lemma.

   The model has the five record kinds, per-signer product-order roster
   domination and per-`(issuer, subject)` grant domination. It also has
   `maxceil` and `W` as functions of the held list, the discard model,
   expiry, and the views `rootVoid`, `wEff`, `voided`, `rosterEff` and
   `delTtlEff`. Certificates, capacity and the horizon's clock clamp are
   outside the model, which assumes well-formed records. T7 is still
   open; T14 has a paper argument only.
2. **Toolchain.** Lean comes from nixpkgs (`nix shell nixpkgs#lean4`),
   because the authors could not download `elan` in their
   environment. `lean-toolchain` gives 4.35.0 for users of `elan`.
3. **Root ceremonies (`Kome.Roster`, phase 8).** This document specifies
   these items, but they are not built yet:
   - certification (short caps, renewed);
   - the out-of-band delivery of segment tops to roots;
   - the rule for new segments (only the founding key opens one, §6);
   - the recovery procedure (§6);
   - the honest-issuer rules, as follows.

   The honest-issuer rules are:
   - A new roster has `gen = 1 +` the largest `gen` of the rosters in `F`
     that are not root-voided.
   - Its `ceiling_t` is at least the largest ceiling of the signer's held
     rosters. So it dominates all of them, and the signer keeps one
     roster.
   - Its epoch is within the current segment and never above the top of the
     segment.
   - A root stays within its slice (`Slice_Max` records), and the founding
     key stays within 15 certificates.
   - A member removal increases the epoch.
4. **Conflict visibility.** This design keeps one value per cell and frees
   the losers' bytes. If an application wants visible conflicts, it
   gets them through the typed-fields extension (C10: the `MVREG` type plus
   parent hashes). It does not need a different lattice.
5. **Quotas.** Only revocation (under A7), owner `DEL`s and the data
   capacity set a limit on floods by an authorized writer. The design does
   not adopt a per-author quota at the room step (E8). Such a quota is a
   capacity refusal. So under a flood, replicas disagree about which of
   the flooder's records they hold, as with the data capacity. The quota
   protects honest room but makes no guarantee stronger, and the correct
   bound depends on the application. A per-author byte quota in the roster,
   enforced by the application, would not touch the lattice.
6. **The C ABI.** It is not designed yet. The packages give its shape:
   `set/get/delete/exists/scan` over records, `GRANT`, `REVOKE` and roster
   operations, `session_*` over Kome.Reconcile, and a digest whose value is
   equal to the sync fingerprint. Statuses are Kome's `Status`,
   including `AUTH_FULL`. `CLONE_SUSPECTED` is an out flag next to the
   status.
7. **Typed fields.** The extension (C10) composes with the core. Build it
   after T7 is proved, when an application asks for counters or sets in the
   engine. The estimate is approximately 7.5 person-weeks in addition to the
   core.
8. **Sketch size.** The current maximum message length sets the sketch cap
   (1 000 cells). A larger message bound gives a larger cap. Below the cap,
   the usual sync is two round trips per phase. Above the cap, the range
   protocol runs as before.
9. **Interoperability residue.** Kome never encodes a record's frame again,
   so any verifier with RFC 8032 Ed25519 and BLAKE2b can check Kome
   records. The accumulator's byte order (§8) is the one place where a
   second implementation must be careful.

10. **Two log decisions made in the SPARK store.**
    - (a) Capacities: the `HEADER`'s capacities are always those of `F`.
      So if a store opens again with larger capacities, Kome writes the
      `HEADER`'s six capacity bytes again and keeps all other
      bytes. (This is the one write that is not an append.) Kome refuses a
      reopen with smaller capacities (`No_Space`).
    - (b) Compaction: if fewer than 7 bytes remain after the frames, Kome
      omits the last `EXPIRE(horizon)`. The reopened replica then has a
      lower horizon, and T18 allows this.

The estimated effort is approximately 24 person-weeks for the Lean theorems
plus the SPARK core. The sketch (C8), which is outside the trusted core,
needs approximately 3.5 more. Multiple roots (C9) need approximately 3 more,
and typed fields (C10) need approximately 7.5 more when they are built. T7
is the longest task in all phases.
