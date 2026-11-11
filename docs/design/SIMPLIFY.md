# Kome simplification plan (branch ccr-f1194bfd-dei9h4, after 2355b6f)

Four reviews of the design after the audit fixes (reuse, complexity, wasted
work, altitude) found the mechanisms below that can go or merge. This file
is the single reference for the change: what each item decides, the new
layouts, the new package shapes, and the order of work. DESIGN.md is
rewritten to match at the end (S24); until then, where the two disagree,
this file wins. Tags: **wire** = frame, key or message bytes; **log** = the
on-disk log only; **lean** = `lean/Kome/Frontier.lean`; **spark** = proved
contracts; **docs** = text. The rules that do not change: every view is a
function of F, every kill predicate is a down-set, T1 to T3 as proved, 0
unproved checks, no `pragma Assume` or `pragma Annotate`.

## 1. Decisions

| # | Decision | Removes | Tags |
|---|---|---|---|
| S1 | Every record kind hashes as `h = BLAKE2b-256(tag ‖ cid ‖ content)`, with `cid = BLAKE2b-256(root_pk ‖ salt ‖ u48(del_ttl))`. No frame carries `ns`, `root_pk` or `salt`. The verifier supplies the cid from the store, the session or the bundle. `ns = cid[0..15]` stays the routing identifier (Noise prologue, bundle header, file names). | well-formed rule 2's `ns` check, replay step 0, `Foreign_Root`, `With_Cid`, the two decode/sign APIs; 16 B per data frame, 64 B per authorization frame | wire, spark, docs |
| S2 | `del_ttl` is fixed at founding: a u48 in the HEADER and in the cid, in `[Del_TTL_Min, Del_TTL_Max]`. It is no longer a ROSTER field, not a component of roster domination, and there is no `del_ttl_eff` view. `Kome.Store.Del_TTL (S)` returns it. | roster field, 4th product component, `del_ttl_eff` and its lemmas (SPARK and Lean), the recovery rule "del_ttl ≥ previous", `Choose`'s `Del_TTL` input | wire, lean, spark, docs |
| S3 | The founding key self-certifies: every signer block is `signer[32] cert_cap:u48 cert_sig[64]` with `cert_sig = Sign(root_sk, BLAKE2b-256("kome/root" ‖ cid ‖ signer ‖ u48(cert_cap)))` (the signature covers the 32-byte hash, as `h` does). For the founding key `cert_cap = 2^48 − 1` and the cert is signed by itself. `wcap(k) = cert_cap` for every signer, no sentinel case. | the zero-cert founding exception, the `U48'Last` branch in `wcap`, two decode paths | wire, spark, docs |
| S4 | No epoch. Every ROSTER carries a fresh collection key `k_g` for its gen, boxed to each member: `k_g = Hedge(issuer_sk, "kome/key", cid ‖ u48(gen), rnd)` (the A6 hedge: a weak RNG alone does not reveal it). `ROSTER_eff` is the `(gen, h)`-maximum of the non-root-voided rosters; domination stays strict in gen. A refresh (same members, new ceiling) is a new gen with a new key. `bundle_key(F)` is the key my entry in `ROSTER_eff` unboxes; a sender keeps the previous key for the H17 store-and-forward bundle. `eph_sk`, box nonces and the bundle key all derive from `k_g` in one style, `f(k_g, label ‖ context)` with `f` = keyed BLAKE2b-256. The stolen-root bound is H7's: `gen ≤ ceiling_t`. | the hash chain, 4 096-epoch segments, segment tops and their delivery, `links[]` (15 × 74 B per roster), `Seal_Link`/`Open_Link`, the ceremony self-check (A15), the re-key-on-divergence rule, the 16-segment end-of-life bound, the `epoch` header field, the unkeyed derivation style | wire, lean, spark, docs |
| S5 | A REVOKE is dominated by a REVOKE of the same `(issuer, subject)` with a lower `from_t`, or an equal `from_t` and a greater `h`. `void`, `revoked` and `root_void` read the minimum `from_t`, which is unchanged. No REVOKE dominates a data record (T2′ as before). | the honest-issuer rule "emit only if no lower from_t is held", the least-`h` choice, one slice entry per repeated REVOKE | lean, spark, docs |
| S6 | Registers are views. `Max_Ceil (F)`, `In_W (F, k)` and `W_Cap (F, k)` are opaque functions over the authorization rows of `Frontier.State`, each with a `_Def` lemma, like the other views. `Kome.Registers` is deleted. The binding may cache them outside the proof. | `Kome.Registers`, the `Regs` component, `Coherent` and its step lemmas, `Extends`/`Added` clauses, the "W full" `Auth_Full` case (unreachable today), `Writers_Max` as a state bound | spark, docs |
| S7 | The horizon is a function of F: `hz(F) = Max_Ceil (F) − del_ttl` when `Max_Ceil (F) ≥ del_ttl`, else none. A DEL `d` is expired when `d.t ≤ hz(F)`. Expiry is automatic: `Put_Frame` of a ROSTER that raises `Max_Ceil` expires in the same call, and no local clock is read. Replay reproduces it by rerunning `Put_Frame`. | `Expire` as a separate call and the post-auth-phase duty, `EXPIRE` and `APPLY_EXPIRED` log entries, the replay clamp (H24), the reserved code `2^48 − 1` (the H6 exception), `No_Horizon : Time64`, the in-memory-only raise, `Compact_Layout` (b), `Horizon_Frozen`, `Ceiling_Stale`, `Ceiling_Lead`, `Is_Born_Expired` (a DEL lands at `t ≥ Max_Ceil − Cap_Lead > hz`) | log, lean (optional: state T11 with `hz`), spark, docs |
| S8 | One lower bound for every write: `low = Max_Ceil (F) − Cap_Lead` (0 below `Cap_Lead`) for PUT and DEL alike. `floor_t = floor.t`. The expire mark is gone. | `Expire_Mark` and its five Posts, `Floor_Time`, the PUT/DEL split in `Now_Eff`, H28 | spark, docs |
| S9 | No `Auth_Gen`. The session gate `Guard.Admits (F, Cred, DH)` is evaluated on every `Receive` and `Next_Phase`. | `Auth_Counter`, `Gen_Full` and the `AUTH_FULL`-at-`2^62` cause, `Gate_Gen`, `Gate_Holds`, the conditional Pres in Reconcile | spark, docs |
| S10 | The quarantine is a view: `Quarantined (F)` holds when the `(gen, h)`-maximum over all held rosters, root-voided ones included, has a root-voided signer. It is cleared by the recovery roster, which wins by gen. Within a session the gate is evaluated after each batch, and a batch applies its ROSTERs before its REVOKEs (key order already does this: tag 0 < tag 1). | `Guard_State`, `Note_Open`, `Note_Credential`, the third durable value | spark, docs |
| S11 | No OPEN message and no pre-gate root-void set. The Noise XK prologue is `"kome/1" ‖ ns ‖ proto`, which binds the collection and the protocol version; a stranger cannot finish XK without the responder's static key. The recovery roster reaches a captured replica as a HELLO credential (it is `ROSTER_eff` by gen), and the auth range brings the REVOKE. HELLO stays as today (credential roster, counts, digest). | OPEN (4 054 B), `Select_Voids`, `Voids_OK`, `Lemma_Voids_Cover`, `Lists_Peer`, `Is_Founding_Revoke`, the pre-gate rate limit, `Our_Open`. Gives up: release by a peer that holds `REVOKE(R)` but not the recovery roster | wire, spark, docs |
| S12 | Roster contention is one view and one rule. `Contested (F)` := some held, non-root-voided roster `r ≠ ROSTER_eff` has `r.gen = ROSTER_eff.gen`. Response: issue at a gen above every held roster with the confirmed union of members. | `ROSTER_FORK`, `Rivals`/`Contested` as two views, three issuer responses | spark, docs |
| S13 | `Revoked_At (F, K, T)` is the one revocation view: `Revoke_Void (P) = Is_Data (P) and Revoked_At (F, P.author, P.t)`, `Revoked (F, K) = Revoked_At (F, K, U48'Last)`. Matches Lean's `revokeVoids`. | duplicated `_Def`, `_Local`, monotonicity lemmas and the bridge lemma | spark |
| S14 | The store index is gone. Each frontier slot carries an opaque payload `Tag : U64` that the lattice ignores (`Is_Frontier` does not read it, `Apply` moves it with the header). The store packs `(Off : 40 bits, Len : 24 bits)` into it and reads frames from the log. `Compact` walks the frontier rows in key order and copies each frame; `Compact` copies only the new length. `Frontier.Apply` finds the dominated records of a data apply inside one entity run and of an authorization apply inside one signer slot; `Frontier.Run (F, Ent)` and `Frontier.Slot (F, Signer)` expose those index ranges, so the store updates its accumulators by diffing the run before and after an apply, never by scanning F. | `Index_Entry`, `Idx`, `Filter`, the `Valid` set-equality between index and F, `Bnd`, `Bnd_Cap`, `Bnd_Cap_For`, the whole-capacity copy in `Compact`, the random-position replay of a compacted log | spark, docs |
| S15 | The log is `HEADER ‖ (APPLY ‖ SEQ)*`. `HEADER = magic[4] version:u8 root_pk[32] salt[16] del_ttl:u48` (59 B; as built). `APPLY = 01 len:u24 frame`. `SEQ = 02 seq:u48`, written by `Compact` and holding the largest own seq ever used (`Compact` takes the device key). No `slice` or `data_cap` field: `Slice_Max` is a compile-time constant and the `Slice` discriminant of `Frontier.State` is gone. Replay reruns `Put_Frame` on each APPLY from a trusted log: it decodes once, computes `h` once and does not verify the signature (`Trusted_Frame`, a ghost predicate the log file carries; DESIGN §7 already places log integrity with the host). `Put_Frame` from a peer verifies as today. `Valid_Length`, `Replayed_Prefix` and `Compact_Due` stay. | `Logged_Cap`, `Logged_Slice`, `Header_Cap`, `Header_Slice`, the `NO_SPACE` case of open, the duty "open every store with `Slice_Max`", one Ed25519 verification per replayed entry, two of the three parses per entry | log, spark, docs |
| S16 | `seq_self` lives in the log: at open it is `max(own seq over APPLY entries, the SEQ entries)`. `Kome.Write` has one call, `Write (S, F, Op, Ent, Field, Value, Now, SK, Rec, Result, Clamped)` (as built) = Choose, Make, Sign, `Put_Frame`; `Receive` stays (`Put_Frame` plus the clone flag). The crash case: a frame lost before its APPLY is durable was never sent (A21), so its seq is reusable. | `Prepare`/`Commit`, `Seq_Persist`, the persist-before-append duty, the second durable file, `SEQ_CORRUPT`, `Seq_Torn`, `Open_Seq`, `Seq_Self_At_Open` | log, spark, docs |
| S17 | Write outcomes (as built): `OK`, `SHADOWED` (a refusal: nothing is built or signed and no seq is consumed, since `t_emit = ceil` and `v_emit < floor` is decidable before signing), `SEQ_EXHAUSTED`, `INADMISSIBLE`, `MALFORMED` (the self check), `NO_SPACE`, `LOG_FULL`; `DOMINATED` and `AUTH_FULL` cannot occur for an own data write. One advisory flag, `CLAMPED` (`t_emit < max(now, floor_t + 1)`). `CLONE_SUSPECTED` is read from `Clone_View`, not an out parameter of the write. | `BORN_EXPIRED`, the separate `Clone_Suspected` out, `SEQ_CORRUPT`, the `AUTH_FULL` counter cause, two formula lemmas | spark, docs |
| S18 | The data element key is entity-major: `03 ‖ ent[16] ‖ sub:u8 ‖ fh[32] ‖ h[32]` (82 B), `sub = 0` for DEL and `1` for PUT. Authorization keys are `tag ‖ 0^17 ‖ signer[32] ‖ h[32]` (82 B; as built, the zero bytes come before the signer so that both layouts keep their fields at the same places; the order is the same). `Data_Lo = 03 ‖ 0^81`. The key order equals the frontier's row order, so the data part of a snapshot needs no sort (as built, `Snapshot_Of` still insertion-sorts the authorization slots, which the frontier keeps in arrival order). "Apply in element-key order" is the one ordering rule (authorization first follows from tag 0, 1, 2 < 3); `Compact` writes in key order. | the heap sort in `Snapshot_Of` (tested, not proved), `Perm`/`Inv`, the two frame copies, D14's separate batch rule, the bundle sort rule and `Compact_Index`'s separate clause | wire (RANGE bounds), spark, docs |
| S19 | Reply groups tile. `RANGE`, `ELEMENTS` and `HAVE` groups all tile the head obligation's `[lo, hi)`, so the group ends when a message's `hi` reaches the head's `hi` and `g` is not sent. A `ROOT` message (`count:u48 fp[32]`) replaces the `g = 0` roots; its bounds are fixed by phase. A split is one message with `k + 1` bounds (`k ≤ 16`), not `k` ranges. Items carry `flen:u16 frame` only: the receiver derives the key from the frame. | the `g` byte, `Group_Size`, `Matches_Head`, the illegal-`g` refusals, HAVE's repeat rule, 81 B per item, 1.3 KB per 16-way split | wire, spark, docs |
| S20 | `acc(e)` is 8 BLAKE2b-512 outputs (4 096 bits) instead of 16 BLAKE2b-256. When this side splits a window of at least 1 024 elements it puts the interior cuts on multiples of 64, so only the two ends of a range walk elements. | half of every `Elem_Acc`; most of the ~1 000 BLAKE2b calls per fingerprint | wire (digest vectors), spark |
| S21 | The store keeps `(n_auth, n_data, acc_auth, acc_data)` incrementally (S14's run diff, 8 hashes per change) and `Store.Digest_Auth (S)` and `Digest_Data (S)` return them (as built). `Reconcile.Admit` takes these two digest states and the HELLO is sent from them (as built: not `Start`, because the gate may need the peer's HELLO credential first); the snapshot (frame references into the log, S14) is built only after the HELLO digests differ. `Compact` is refused while a session holds a snapshot (`Pinned`). | the snapshot build, sort and copies in every session; the unimplemented C8 "snapshot cache" duty | spark, docs |
| S22 | `Header` is `Kind, Ent, FH, V, Issuer` (no `NS`, `Epoch`, `Del_TTL`). | ~22 B per held header and the constant `NS` in every one | spark |
| S23 | The C8 IBLT round 0 moves from the normative design to §10 as an optional extension. | a specified, unbuilt, unowned mechanism | docs |
| S24 | Build: `kome_spark.gpr` gains a `Mode` scenario (`check`, the default, with `-gnata`; `release` with `Assertion_Policy (Ignore)` for Pre, Post, Ghost and invariants). CI builds both. DESIGN.md §1 (decisions), §2, §3, §5, §6, §7, §8, §9, §10 are rewritten to this file; REQUIREMENTS.md loses the H6 exception; IMPLEMENTATION_PLAN.md and README.md follow; AUDIT.md §0 gains a paragraph that points here for the items it supersedes (A7 reopened by S4, H24 by S7, H26 by S15, A10/A5 by S16, H28 by S8, H11 by S9; H12 was still deferred then, and §6 records its fix). | — | build, docs |

Not done, on purpose: a structural founding reserve (the E1 rule works); sizing the authorization matrix by slots in use (memory only); a data-only header type (S22 is enough for now); `HELLO` sending `h(cred)` first (one more round trip for a few KB); the per-entry BLAKE2b in replay (S15 trusts the host's file, as §7 already does).

## 2. Layouts

Frames (`tag:u8 ‖ content ‖ sig[64]`; `SIGNER = signer[32] cert_cap:u48 cert_sig[64]`, S3):

```
0 ROSTER  SIGNER box_pk[32] gen:u48 ceiling_t:u48 n_members:u8
          members[n_members] { sign_pk[32] dh_pk[32] nonce[24] box[48] }   (box holds k_g, S4)
1 REVOKE  SIGNER sign_pk[32] from_t:u48                                     (205 B)
2 GRANT   SIGNER subject[32]
3 DEL     ent[16] t:u48 seq:u48 author[32]                                  (125 B)
4 PUT     ent[16] flen:u8 field[flen] t:u48 seq:u48 author[32] vlen:u16 value[vlen]
h = BLAKE2b-256(tag ‖ cid ‖ content) for every kind.
cid = BLAKE2b-256(root_pk ‖ salt ‖ u48(del_ttl)); ns = cid[0..15].
cert_sig = Sign(root_sk, BLAKE2b-256("kome/root" ‖ cid ‖ signer ‖ u48(cert_cap))).
Offsets: ROSTER signer 1, cert_cap 33, cert_sig 39, box_pk 103, gen 135, ceiling_t 141, n_members 147,
members 148 (212 + 136·n, at most 8 916); REVOKE sign_pk 103, from_t 135; GRANT subject 103;
DEL ent 1, t 17, seq 23, author 29; PUT ent 1, flen 17, field 18. Frame_Max = 41 120.
```

Keys (S4): `k_g = Hedge(issuer_sk, "kome/key", cid ‖ u48(gen), rnd)`; `f(k, m) = keyed BLAKE2b-256(key = k, msg = m)`; `eph_sk = f(k_g, "kome/eph" ‖ cid ‖ u48(gen) ‖ signer)`; member box nonce = `f(k_g, "kome/box" ‖ dh_pk)[0..23]`; `wrap_key = f(X25519(eph_sk, dh_pk), "kome/wrap" ‖ box_pk ‖ dh_pk ‖ sign_pk ‖ cid ‖ u48(gen))`; the box is XChaCha20-Poly1305(wrap_key, nonce, AD = cid ‖ u48(gen), k_g) and the opener refuses an all-zero `k_g`; `bundle_key = f(k_g, "kome/bundle")` and a bundle's AD is `cid ‖ u48(gen)`. `Kome.Epochs` keeps its name but holds only these derivations and the boxes.

Log (S15): `HEADER = "KOME" 01 root_pk[32] salt[16] del_ttl:u48`; `APPLY = 01 len:u24 frame`; `SEQ = 02 seq:u48`.

Element key (S18): data `03 ‖ ent[16] ‖ sub:u8 ‖ fh[32] ‖ h[32]`; authorization `tag ‖ 0^17 ‖ signer[32] ‖ h[32]` (as built); 82 bytes; `Data_Lo = 03 ‖ 0^81`.

Messages (S11, S19): `HELLO` as today without OPEN before it; `ROOT count:u48 fp[32]`; `RANGE k:u8 bounds[k+1] { count:u48 fp[32] }[k]`; `ELEMENTS lo[82] hi[82] n:u16 items[n] { flen:u16 frame }`; `HAVE lo[82] hi[82] n:u16 items[n] { flen:u16 frame }` (as built: they keep their bounds, which make the replies tile), all tiling `[lo, hi)` of the head obligation.

## 3. Package shapes

- `Kome.Headers`: `Header (Kind, Ent, FH, V, Issuer)`; `Dominates` gains the REVOKE clause (S5) and loses the `del_ttl` and epoch terms.
- `Kome.Frontier`: `State` without `Slice` discriminant and without `Regs`; slots carry `Tag : U64`; `Run (F, Ent)` and `Slot (F, Signer)` return index ranges; `Max_Ceil`, `In_W`, `W_Cap` as opaque views with `_Def` lemmas; `Expire (F, Hz)` stays as the kill of `t ≤ Hz` scoped to data (G1); `Set_Tag` lets `Compact` retag a record; `Apply_Expired` is removed (Store does not use it).
- `Kome.Views`: `Revoked_At`, `Contested`, `Quarantined`, `Skew (F, Now) = Now − Max_Ceil (F)` as a signed advisory; `Roster_Eff` by `(gen, h)`; no `Del_TTL_Eff`, `Roster_Fork`, `Rivals`, `Ceiling_Stale`, `Ceiling_Lead`.
- `Kome.Guard`: `Admits (Cid, F, Cred, DH) = Gate (Cid, F, Cred, DH) and not Quarantined (F)` (the cid first, as built); no state.
- `Kome.Records`: `Cid_Of (Root_PK, Salt, Del_TTL)`; every `Hash`, `To_Header`, `Well_Formed`, `Decode_Verified`, `Sign`, `Make_*` takes `Cid` first; `Cert_OK (Cid, Root_PK, Signer, Cap, Sig)`.
- `Kome.Store` (as built): `Store (Log_Cap)`; `Open (Root_PK, Salt, Del_TTL, Self_PK, F, S)`; `Put_Frame (S, F, Frame, H, Off, Result)` with automatic expiry (Post `Put_Done`); `Compact (S, F, Buf, Result)` with `Busy` while pinned; `Open_From_Log (Input, Self_PK, F, S, Valid_Length, Result)`; `Cid (S)`, `Del_TTL (S)`, `Seq_Self (S)`, `Digest_Auth (S)`, `Digest_Data (S)`, `Pinned (S)`, `Pin`, `Unpin`; `Valid (S, F)` relates log, payload tags and F.
- `Kome.Frames` (new, as built): the opaque predicate `Frame_Is (Frame, Cid, X)`, completed in its body, so that the store's tag lemmas do not unfold the record parsers.
- `Kome.Write`: `Write`, `Receive`, `Receive_Ceil` (AUDIT.md H12), `Clone_View`.
- `Kome.Reconcile` (as built): `Start (Sess, As, Cid, Peer_DH)`, `Admit (Sess, F, Eff, Auth, Data, Cred, Buf, Len, Root)` with the two digest states, `Receive`, `Next_Phase`; snapshot by source index over one frame table; no `Select_Voids`, `Gate_Holds`, `Group_Size`.
- `Kome.Epochs`: `Key_For_Gen` (hedged), `Box_Key`, `Unbox_Key`, `Eph_SK_Of`, `Bundle_Key_Of`.
- `Kome.Registers`: deleted.

## 4. Order of work

Wave 1 (parallel, separate worktrees): Lean (S2, S4, S5, S7); Records + Crypto + Epochs (S1 to S5, S22's `To_Header`); Headers + Frontier + Views + Guard (S5, S6, S10, S12, S13, S14's slots and runs, S22). The Header type text in §3 is written identically by both SPARK agents.
Wave 2 (parallel): Store + Emit + Write (S7, S8, S9, S14 to S17, S21's `Digest_Of`); Reconcile + Digest (S9, S11, S18 to S21).
Wave 3: DESIGN, REQUIREMENTS, PLAN, README, AUDIT addendum (S23, S24); build modes (S24); vectors regenerated; full proof run; counts; artifacts.

## 5. As built

Where the code deviates from the plan above, the code wins; the entries
marked "as built" above carry the correction, and this list collects them.

- The log `HEADER` is 59 bytes (4 + 1 + 32 + 16 + 6), not 61.
- The authorization element key is `tag ‖ 0^17 ‖ signer ‖ h`: the zero
  bytes come before the signer. The order of the keys is the same as with
  `tag ‖ signer ‖ 0^17 ‖ h`, but the bytes of a range bound differ.
- `ELEMENTS` and `HAVE` keep `lo` and `hi`, so that the replies tile.
- `Kome.Store` is `Store (Log_Cap)` and exposes `Digest_Auth (S)` and
  `Digest_Data (S)` (two `Kome.Digest.Digest_State` values), not
  `Digest_Of`. `Compact` takes a `Result` (`OK`, `Busy`, `Log_Full`), and
  `Pin`/`Unpin` count the sessions that hold a snapshot.
- `Reconcile.Admit` takes the two digest states and sends the `HELLO`;
  `Start (Sess, As, Cid, Peer_DH)` does not, because the gate may need the
  peer's `HELLO` credential first (S11).
- `Kome.Write.Write (S, F, Op, Ent, Field, Value, Now, SK, Rec, Result,
  Clamped)`, with the outcomes `OK`, `SHADOWED`, `SEQ_EXHAUSTED`,
  `INADMISSIBLE`, `MALFORMED`, `NO_SPACE` and `LOG_FULL`.
- `Kome.Frames` is a new package: the opaque `Frame_Is (Frame, Cid, X)`,
  because the store's tag invariant timed out with `Header_Of` unfolded.
- `Snapshot_Of` insertion-sorts the authorization slots (at most 8 192
  records, `O(n_auth²)`), which the frontier keeps in arrival order; the
  data row is already in key order. It is proved, and its run-time checks
  are off (an `Assertion_Policy` region).
- `Compact_Layout` is weaker than the plan's byte-for-byte clause: it
  states the `HEADER` bytes, that every record's `APPLY` ends before the
  final `SEQ (seq_self)`, and `Count + 1` entries; the copy order and
  contiguity are tested.
- `Kome.Guard.Admits`, `Gate` and their lemmas take the `cid` first.
- `Frontier.Apply_Expired` is removed by the build stream: `Put_Frame`
  holds an expired `DEL` with `Apply` and expires it in the same call.
- The REVOKE frame is 205 bytes, and `cert_sig` signs the 32-byte
  `Cert_Hash`, as §2 already states.

## 6. After the simplification: the ceiling cell (AUDIT.md H12)

AUDIT.md H12 was applied on top of the state that this file describes.
It changes the statements below. DESIGN.md (E10, §3, §7, §8, T19)
describes the result, and where this file and DESIGN.md disagree,
DESIGN.md and the code win.

- "Every view is a function of F" (the rules that do not change, above)
  and S6: `Max_Ceil` is the larger of `Held_Ceil`, the function over the
  authorization rows that S6 describes, and the ceiling of the roster in
  the ceiling cell. The cell is state beside the rows, and no other view
  reads it.
- S7: `hz(F)` reads that `Max_Ceil`. A roster that the store records in
  the cell expires in the same call, as a held roster does; `Put_Ceil`
  expires too.
- S15 and §2 (Log): the log is `HEADER ‖ (APPLY | SEQ | CEIL)*`, with
  `CEIL = 03 len:u24 frame`. Compaction writes the cell's `CEIL` first,
  and `Compact_Layout` states `Count + 1` entries, or one more with a
  cell. `Log_Fits` counts one more entry.
- S11, S21 and §2 (Messages): the `HELLO` is `01 n_auth:u32 n_data:u32
  digest[32] cred_len:u16 ceil_len:u16 cred ceil`, at most 17 877 bytes.
  `ceil` is the frame of the sender's cell roster while the cell is
  live, and `Reconcile.Admit` takes it (its precondition
  `Ceil_Frame_OK`).
- S17 and §5: `Put_Frame` and `Kome.Write.Receive` can also return
  `CEIL_ONLY`. The outcomes of `Kome.Write.Write` are as listed.
- §3 (package shapes): `Kome.Frontier` gains `Held_Ceil`, `Has_Ceil`,
  `Ceil_Held`, `Ceil_Tag`, `Ceil_Live`, `Raise_Ceil` and `Set_Ceil_Tag`;
  `Kome.Store` gains `Put_Ceil`; `Kome.Write` gains `Receive_Ceil`;
  `Kome.Status` gains `Ceil_Only`.
