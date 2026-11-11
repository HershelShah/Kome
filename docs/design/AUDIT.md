# Kome design audit (master, 2be1260)

Scope: docs/design (REQUIREMENTS.md, DESIGN.md, IMPLEMENTATION_PLAN.md), lean/Kome/Frontier.lean, spark/src/kome-*.ads/.adb, spark/CONVENTIONS.md, spark/tests, spark/vectors, CI and build files. The previous C++ engine is out of scope. Line numbers are at 2be1260. "F<n>" is the confirmed finding ID; merged items list every ID.

## 0. Status

Applied on branch `ccr-f1194bfd-dei9h4` after the audit. Items 1 to 3 are
the fix groups that §1 recommends first; item 4 is everything else in §2
to §5; item 5 is H12, which was applied after the simplification. Each
item names what changed. On the final state, gnatprove at
`--level=3` proves all 18,301 checks of the 17 packages and the root package
with 0 unproved, 1,329 tests pass, `lake build --wfail` checks the 183 Lean
theorems with no `sorry`, and `lean/Kome/Axioms.lean` confirms that every
declaration of `Kome.Frontier` uses only `propext`, `Classical.choice`
and `Quot.sound`.

**Simplification (SIMPLIFY.md), 2026-11-10.** The simplification of
`SIMPLIFY.md` (S1 to S24) was applied on top of the state that this
section describes (commit 2355b6f), and `DESIGN.md` now describes the
design as built. The text below stays as the record of the audit-fix
state; where it and `SIMPLIFY.md` disagree, `SIMPLIFY.md` and the code
win. It supersedes these items: A7 is reopened and resolved differently
by S4 (a fresh hedged key `k_g` per roster generation; the hash chain,
segments, links, segment tops and the A15 self-check are gone, and with
them H6's fixed segment boundaries); A2 is moot, since there is no epoch
and `ROSTER_eff` is the `(gen, h)`-maximum; H15 is moot, since `del_ttl`
left the roster and is fixed at founding (S2); H24 is superseded by S7
(the horizon is a function of `F`, the log has no `EXPIRE` entry, there
is no replay clamp, and the reserved code `2^48 − 1`, the stated
exception to REQUIREMENTS H6, is gone); H26 by S15 (the log is `HEADER ‖
(APPLY | SEQ)*`; `Compact_Due` stays); A10 and A5 by S16 (`seq_self`
lives in the log, `Kome.Write.Write` is one call, and `Prepare`/`Commit`,
`Seq_Persist` and `SEQ_CORRUPT` are gone); H28 by S8 (one write lower
bound `maxceil − Cap_Lead`; no expire mark); H11 by S9 (no `Auth_Gen`;
the gate is evaluated on every `Receive` and `Next_Phase`); H2's
quarantine is now a view of `F` (S10, `Kome.Views.Quarantined`; no
`Guard_State`); and A14 and H5 go with the `OPEN` message (S11). H12
was still deferred in the simplified state; it was applied after it
(item 5 below). G15's index and boundary table are replaced by the tags
of S14, and A11's slice and `data_cap` fields by S15. `SIMPLIFY.md` gives
the decisions, and its "As built" note the places where the code
deviated from the plan. On the simplified state, gnatprove at
`--level=3` proves all 16,709 checks of the 17 packages and the root
package with 0 unproved, 1,033 tests pass, and `lake build --wfail`
checks the 202 Lean theorems and 2 instances with no `sorry`.
Final counts: see IMPLEMENTATION_PLAN.md.

1. Roster and gate integrity: H1 (domination strict in gen, `ROSTER_FORK`
   view, `Lemma_Equal_Gen_No_Dom`), A2 (epoch in `Header`, `ROSTER_eff` by
   `(epoch, gen, h)`), H6 (fixed segment boundaries, `Kome.Epochs`), H7
   (`gen ≤ ceiling_t` in Well_Formed and Canonical, issuer rules), A3 (the
   `revoked` view and `Kome.Guard.Gate`), H2 (`Kome.Guard` quarantine
   flag). Lean: `roster` carries its epoch, `dominates` is strict in gen,
   `rkey` puts the epoch first.
2. Revocation and recovery: A1 (write cap: GRANT `V = (cap, subject, 0, h)`,
   product order `(cap, h)`, `wcap` register in `Kome.Registers`, admission
   `t ≤ wcap`, `Eff_Ceil` in `Kome.Emit`; A7 restated; `SUSPECT_RELAY`
   duty), H3 (`Kome.Store.Log_Fits`, the `LOG_FULL` status; the
   compact-room obligation is stated in §7 and tested, not proved), A4 (the
   founding reserve rule), H8 (recovery membership step), H16 (recovery
   ceiling step). Lean: `grant` carries its cap, `wcap`, `adm` reads it.
3. Expiry: H14 and A5 (`Cap_Lead` = 3 days `< Del_TTL_Min`; a DEL is
   emitted at `t ≥ maxceil − Cap_Lead`, `Kome.Emit.Del_Low`), H4, H35 and
   A16 (A4 restated over every frame copy, admitted and durable, bundles
   closed under admission, the sync point), G1 (T4(b), T10, T11(b) scoped
   to `applyD`; Lean `applyH`, `NoLateDom`, `expire_applyAllH`,
   `auth_first_closed`).
4. The rest of §2 to §5, by package.
   - Headers, Views, Guard: H15 (roster domination also requires
     `del_ttl ≤`; `Lemma_Dominates_Del_TTL`, `Lemma_Del_TTL_Eff_Apply`),
     G8 (`Is_Void` and `Revoke_Void` hold only on data records), A22
     (`Contested`, the `rivals` view), N3 and N4 (`Ceiling_Lead`,
     `Ceiling_Stale`; `Horizon_Frozen` in Store).
   - Lean: H15 (`dominates_ttl`, `delTtlEff_F`), N1 (`expire_expire`), G3
     (`deletedAt`, `existsEnt`, `emitSeq` and the T5, T8, T9, T10
     statements that §9 cited), A18 (`--wfail`, `Kome/Axioms.lean`).
   - Crypto, Records, Epochs: H13 and A27 (`Is_Small_Order_Point`;
     `Verify` refuses small-order keys; `Sign_Key_OK` = canonical, not
     small-order, not the zero-seed key, required of root_pk, signer, the
     GRANT subject, the REVOKE sign_pk and every ROSTER member sign_pk
     (`Member_Keys_OK`), by `Make_*`, `Cert_OK`, Well_Formed and
     `Store.Open`; box_pk is not `X25519_Public(0^32)`; `Key_Pair` and
     `Seal_Link` refuse all-zero keys), A25 (`Verify` is a SPARK
     expression over a private `Raw_Ed25519_Check` with no Post; the
     assumed surface is that function plus the two binding axioms
     `Lemma_Blake2b_Congruent` and `Lemma_X25519_Congruent`, each with a
     `-gnata` test), A6 and G7 (`eph_sk` = BLAKE2b-256(`"kome/eph"` ‖ k_e
     ‖ ns ‖ u16(e) ‖ signer ‖ u48(gen)), `Box_PK_Of`, `Box_Key` with the
     derived secret; no caller randomness), G5 (the chain step is keyed
     BLAKE2b-256 under k_{e+1} with message `"kome/prev"`; the bundle key
     k_b is stated in §6 and §8 but not derived in SPARK yet), G16 (the
     verification equation and the del_ttl refusal are normative; the
     torsion and Wycheproof vectors are normative), E15 (REVOKE has no
     `rev_seq`: a REVOKE frame is 269 bytes, its header seq is 0, an
     OPEN is at most 4 054 bytes; the Lean `revoke` constructor has four
     fields; records.txt, reconcile.txt and one root_pk of store.txt
     regenerated), A26 (a data record's `h` is BLAKE2b-256(tag ‖ cid ‖
     content) with `cid` = BLAKE2b-256(root_pk ‖ salt), `Cid_Of`; the cid
     is implicit context, not on the wire, so frame bytes are unchanged;
     `Store.Open` and `Open_From_Log` compute it once (`Store.Cid`) and
     pass it to `Well_Formed`, `Decode_Verified`, `To_Header`, `Sign`,
     `Make_Put` and `Make_Del`; `Put_Frame` requires `Verified (Cid (S),
     Frame)`; `Write.Ready (P, Cid)`; authorization records are unchanged
     since their content carries root_pk and salt; records.txt
     regenerated; §10.9 interop needs `(root_pk, salt)`, not only `ns`).
   - Emit: H22 (`CLAMPED` and `BORN_EXPIRED` out flags with `Is_Clamped`
     and `Is_Born_Expired`), G21 (`Put_Target`, `Del_Target`,
     `Lemma_Put_Target_Matches`, `Lemma_Del_Target_Matches`), H28 (the
     expire mark is a floor term, `Floor_Time`), H18 (`Clone_Pair`).
   - Store: G22 (`Off = Log_Length (S'Old)`), H24 (replay clamps each
     EXPIRE to `Horizon_At (F, U48'Last)`; the `EXPIRE_NONE` entry was
     declined: the code `2^48 − 1` decodes to "no horizon", which lies
     below every clamp bound, so it can only lower the horizon; this is a
     stated exception to REQUIREMENTS H6), H23 (`Valid_Length`,
     `Replayed_Prefix`, T18-prefix proved; a duplicated APPLY replays as
     OK; the binding truncates to `Valid_Length`), G17 and A28
     (`Compact_Index` and `Compact_Layout` replace `In_Old_Order`), H11
     (`Auth_Gen`, `AUTH_FULL` at 2^62), H28 (`Expire_Mark`: the largest
     horizon applied), H26 (`Compact_Due` = more than `2·|F| + 64`
     entries; the binding calls `Compact` when it holds, so replay checks
     at most `2·|F| + 64` signatures), A11 (the HEADER slice is a check;
     `data_cap` is chosen at each open, smaller allowed when replay fits;
     no in-place rewrite; the constant `Slice_Max` is a binding duty, not
     a Pre of `Open`), G23 (§10.10(b) cites `Compact_Layout`), N4
     (`Horizon_Frozen`), G15 (`Store (Cap, Log_Cap, Bnd_Cap)` with
     `Bnd_Cap ≥ Log_Cap / Min_Entry`; `Compact (S, F, Buf)` writes into the
     binding's buffer and keeps no copy of the log; no whole-store
     temporary in `Init` or `Open_From_Log`; about 1.7 × `Log_Cap` beside
     the index; `Open_From_Log` still holds its input and the log, since a
     streaming replay would change its contract).
   - Write (new package `Kome.Write`): A10 (`Prepare` = Choose, Make,
     Sign, with `Seq_Persist` that the binding persists before `Commit` =
     `Store.Put_Frame`; `Seq_Self_At_Open` = max(stored, `Max_Own_Seq`);
     `Open_Seq` with `SEQ_CORRUPT`; large seq jumps are not refused; the
     Post of `Prepare` is T8 from `Choose`, and `Commit` keeps `Valid`; the
     persist-before-append and send-after-durable duties are stated in
     the package header as A5 restated), H18 (`Receive` = `Put_Frame`
     plus the flag: an own record that is OK, not held before and not an
     expired DEL sets `CLONE_SUSPECTED`; `Clone_View` = `Clone_Detected`
     or `Clone_Pair`).
   - Frontier: G25 (the data row is sorted entity-major `(ent, kind,
     fh)`, `Data_Sorted` in `Is_Frontier`; `Apply` finds the entity run by
     binary search and makes Dominates calls only inside it;
     `Lemma_Dominator_In_Run`, `Lemma_Outside_Run`, `Lemma_No_Drop_Below`;
     public contracts unchanged).
   - Reconcile: G12 and A13 (the credential gate inside `Admit`, with
     `Kome.Guard.Admits`), H11 (`Auth_Gen` re-check in `Receive` and
     `Next_Phase`), H5 (`Select_Voids` with `Voids_OK` and
     `Lemma_Voids_Cover`: one founding REVOKE per root-voided subject, at
     most 15 subjects), G4 and H19 (a `g` byte binds every reply group to
     the obligation FIFO; `Range_Fp` over the D15 prefix sums, at most 64
     additions and one hash), A12 (`Snapshot_Of` with the Post
     `Range_Fp = Frontier_Digest`), A14 (the responder sends OPEN only
     after a matching OPEN; root-void frames go only to a peer that a held
     roster lists), A8 (kind < 3 before kind ≥ 3 inside a batch).
   - Build: E4 (the gpr is the single source of the proof switches), E5
     (`PROOF_WIP` is gone; any unproved check fails), E12 (section
     garbage collection and the `nm` check against `crypto_argon2` and
     `crypto_eddsa_*`), E18, E19 (the module list from the source and
     test files, `check.sh --list`, used by `all` and by the CI matrix),
     E23 (module `kome`), A17 (the CI pull-request gate: `lean/build.sh`
     and `PROVE=0 spark/check.sh all`), A18 (no `pragma Assume` or
     `pragma Annotate`, enforced by `check.sh` and CONVENTIONS).
   - Text only (DESIGN, REQUIREMENTS, IMPLEMENTATION_PLAN, README,
     CONVENTIONS, header comments): H9, H10, H17, H20, H21, H25, H27, H29,
     H30, H31, H32 (the transient is documented; no hash commitment), H33,
     H34, H36; G2, G6, G9, G10 (already gone), G11, G13, G14, G18, G19,
     G20, G24; A9, A15, A19, A20, A21, A23, A29, A30; N1 to N7; E1, E6,
     E7, E8, E9, E10, E13, E14, E16, E17, E20, E21, E22, E24.
   - Residue applied before item 4: E2, E3, E11.
5. H12, the ceiling cell, applied after the simplification (DESIGN.md
   E10, §3, §7, §8, T19). `maxceil` is the same for every arrival order
   of one record set, `AUTH_FULL` included.
   - Frontier: the state has one ceiling cell beside the rows (a matrix
     position of `Auth_Rows` and the flag `Has_Cell`). `Max_Ceil` is the
     larger of `Held_Ceil` (the function that `Max_Ceil` was) and the
     cell's ceiling. New: `Held_Ceil`, `Has_Ceil`, `Ceil_Held`,
     `Ceil_Tag`, `Ceil_Value`, `Ceil_Live`, `Ceil_Same`, `Raises_Ceil`,
     `Same_Held`, `Raise_Ceil`, `Set_Ceil_Tag`, `Lemma_Held_Ceil_Def`,
     `Lemma_Frontier_Ceil`, `Lemma_Ceil_Bound`, `Lemma_Same_Held`.
     `Apply`, `Expire` and `Set_Tag` keep the cell (`Ceil_Same`), and
     `Apply` keeps its five statuses and its contract.
   - Kome: the status `Ceil_Only`.
   - Store: the log entry `CEIL` (`Op_Ceil` = 03). `Put_Frame` records a
     ROSTER that the rows refuse for room and whose ceiling is above
     `maxceil` in the cell and returns `Ceil_Only` (`Ceil_Rule`,
     `Captured`, `Ceiled`, `Ceil_Appended`); `Auth_Full` is left for a
     refused record that does not raise the ceiling. New entry point
     `Put_Ceil` (`Ceil_Done`) for the ceiling frame of a HELLO: it writes
     the cell and never a row. `Ceil_Step`, in `Put_Done` and
     `Ceil_Done`, is the step of T19. `Valid` gains the cell's tag
     (`Lemma_Ceil_Tag`); `Lemma_Tag` states `Op_Apply`; `Has_Frame`
     accepts both entry kinds; `Log_Fits` counts one more entry; replay
     has the `CEIL` rules and refuses an `APPLY` that `Put_Frame` would
     capture; `Compact` writes the cell's `CEIL` first (`Retagged`,
     `Compact_Layout`).
   - Write: `Receive` can return `Ceil_Only`. `Receive_Ceil` is the
     receiver side of the ceiling frame: it checks that the frame is a
     verified ROSTER (`Malformed` if not), applies it with `Put_Ceil`
     only, and gives the `SUSPECT_RELAY` flag of the frame.
   - Reconcile: the HELLO carries a second roster frame, `ceil`
     (`Hello_O_KLen`, `Hello_Fixed` = 45, `Hello_Max_Len` = 17 877,
     `Hello.Ceil`, `Hello_Ceil_Of`, `Lemma_Ceil_Zero`; `Encode_Hello` and
     `Admit` take it). The sender duty is the precondition
     `Ceil_Frame_OK` of `Admit`: with a live cell, `Ceil` is a roster
     frame whose header is the cell's record, and with no live cell it is
     empty. What the receiver does with the frame is the Post of
     `Kome.Write.Receive_Ceil`. That the receiver calls it for every
     accepted HELLO with a ceiling frame, and its order against the
     snapshot, are caller duties: they are in the package header and are
     not proved.
   - Lean: the section "The ceiling cell" (`CState`, `maxCeilC`, `admC`,
     `applyC`, `ceilC`, `expireC`, `applyHC`, `stepHC`), with
     `maxCeil_stepAllHC`, `maxCeil_order_indep_H` (T19) and
     `applyHC_no_refusal`: 12 theorems, 214 theorems and 2 instances in
     all.
   - Tests: `test_frontier` (j), `test_views` (l), `test_store`
     (`Ceiling_Cell`, `Ceil_With_Room`: both arrival orders, reopen,
     compact, re-offers, the replay refusals), `test_write` (g),
     `test_reconcile` (R1 on the wire; (i) `Store_Sessions`, sessions
     between real stores); `vectors/store.txt` and
     `vectors/reconcile.txt` gain the `CEIL` prefix and the HELLO with a
     ceiling frame.
   - The fix differs from the one that H12 proposes. There is one cell
     for the state, not one per slot; it is ordered by the ceiling alone,
     not by `(ceiling_t, gen, h)`; and it is written only for a roster
     that does not enter a row, so it is never the home of a held roster.
     A per-slot cell that held the signer's maximal roster would have to
     evict a roster that the new one does not dominate (a higher ceiling
     with a `gen` that is not higher), which is what H12 itself forbids.
     Here the replaced occupant was never a held record, so T3 is as
     before, and only `maxceil` reads the cell. The roster of a cell is
     not an element, which is why the HELLO frame is part of the fix.
   - Tested, not proved: replay and `Compact` with a cell give back the
     state (T18); SPARK proves the step of T19 and Lean the fold over a
     model; the receiver's caller duties above. Under `-gnata` the store and session
     tests run the scenario with a full slot table; the full-slice form
     (512 REVOKEs) runs in the release mode only
     (IMPLEMENTATION_PLAN.md, Missing tests).

Declined or deferred, with the reason:
- A7 (drop the chain and segments): declined. The chain, the fixed
  segments and the links stay; A6 removes the randomness instead.
- A24 (frames by reference to the store with a generation counter):
  deferred. The session pool stays at `Pool_Max` = 2^30; the change is to
  the `Snapshot` type and every contract over it.
- H24, `EXPIRE_NONE`: declined, as above.
- A11, a `Slice_Max` Pre on `Store.Open`: declined; the tests use smaller
  slices, so it stays a binding duty.
- G15, a streaming `Open_From_Log`: declined, as above.
- G5, the bundle key `k_b` in SPARK: not yet (phase 9 bundle layer).
- A26, the cid in authorization records and a `Reconcile.Start` cid
  parameter: not needed; Reconcile never decodes a data frame (received
  frames go through `Write.Receive` and `Store.Put_Frame`).
- Follow-ups not taken: `Kome.Headers.Canonical` could require `V.Seq = 0`
  of a REVOKE, as it does of a GRANT; the store could check that an
  authorization record's salt equals its own (step 0 checks root_pk, so
  only the founding key could exploit the gap).

Tested, not proved (each stated in the package header that owns it):
the compact-room obligation of H3; the heap sort in `Snapshot_Of` (a
final scan guards its Post); balanced splits, T7 termination and the
session budgets; the session-wide claims "every applied data frame was
applied while the gate held" and "`Complete` implies one full reply
group per obligation" (each call's Post is proved, the induction is
not written); the O(n log n) bound per session; `Prepare`'s self check
(`Kome.Crypto` does not state that `Verify (Sign (M))` holds); the
Crypto Posts (`Raw_Ed25519_Check` and the two congruence axioms).

Inventory items of the audit that this closes (see §4): A5-persist-order
(A10), E1-founding-slice (A4), IA-03 (H14), IA-05 (H16), IA-11 (A22),
IA-12 (A2), IA-13 (G16, E8), IA-14 (H13), IA-16 (A12), IA-17 (A23),
IA-20 (A16, H17), IA-22 (A21), IA-23 (H18), IA-27 (A6), IA-33 (H24,
clamp only).

## 1. Summary

The lattice core is sound. T1-T3, the view functions and the store replay (T18) are proved, and Byteorder, Versions, Keys and Registers have no confirmed defect. The weak parts are the authorization layer around ROSTER_eff and the session gate, the tombstone-expiry rules, and the store's capacity and crash behaviour. Several normative claims are false as written: the D3 rationale and the H8 "Root restored from backup" row (equal-gen domination), E1 "the founding key's REVOKE always lands", D10 "never shorter", "pins stop at the next roster refresh", T4(b)/T10/T11(b) under a store horizon, and the check mark on T4(c). The unbuilt layers (Kome.Roster, transports, storage binding) carry many duties that no phase owns.

Do these three things first:
1. Roster and gate integrity. Make same-signer roster domination strict in gen (H1). Order ROSTER_eff by epoch first and fix segment starts (A2, H6). Make the gate REVOKE-aware, and quarantine a replica after a pre-gate root-void (A3, H2).
2. Make revocation and recovery hold. Bound a revoked writer's reach with a write cap and suspect-relay attribution (A1). Make the founding REVOKE always land with a derived log bound and a founding-slice reserve (H3, A4). Add the missing recovery steps for membership, gen space and ceilings (H8, H7, H16).
3. Restate expiry so that T11(c) is true. State A4′ over every frame copy, as admitted and durable, against the fastest horizon, with a Cap_Lead < Del_TTL_Min issuer rule and a lower bound on DEL t (H4, A16, H35, H14, A5). Scope T4(b)/T10/T11(b) to horizon-free runs and add applyH to Lean (G1).

## 2. Holes

Severity order: high, medium, low. Section 2.4 holds the spec-impl-gap and missing-proof items (all low).

### 2.1 High

#### H1. A same-signer roster at equal gen evicts the newer roster (F87, F91, F94, F98)
- What: DESIGN.md:173-174 kills roster r when a same-signer r′ has (gen, h) greater and ceiling_t ≥. Frontier.lean:150-151, kome-headers.ads:54-59 (Gen_Lt) and :80-83 (K_Roster) match. The honest-issuer rule (DESIGN.md:1206-1209) gives a restored or second-device root gen = 1 + the largest gen it holds. That is the gen of the roster it issued after the backup. Then h decides, and the stale roster wins with probability 1/2. T3 removes the newer roster from F at every replica, and no view brings it back. The H8 row (DESIGN.md:413) and D3 (l.191-196) cover only a strictly lower gen. §6 l.446 ("h resolves the race") hides the same-signer case.
- Scenario: R's backup holds r5 (gen 5, lists X, epoch e). R issues r6 (gen 6, removes X, epoch e+1) and everyone syncs it. R is restored and issues r6′ (gen 6, ceiling ≥ r6's, lists X, epoch e). If h(r6′) > h(r6), r6 is dominated everywhere. ROSTER_eff lists X at epoch e. X passes the gate and reads new bundles. The restored root no longer knows of the removal, so the H8 recovery "issue a new roster above both" re-lists X.
- Fix: (a) Domination strict in gen. kome-headers.ads:82 uses `P.V.Seq < Q.V.Seq` in place of Gen_Lt. Frontier.lean:151 becomes `s = s' ∧ c ≤ c' ∧ g < g'`. (b) A fork must not lower the effective epoch. Order ROSTER_eff (DESIGN.md:249-250, kome-views.ads:134-150) by epoch first (see A2). (c) Add a ROSTER_FORK view: two held rosters of one signer at equal gen. It plays the role that CLONE_SUSPECTED plays for data. (d) Honest-issuer rule: a restored root reconciles before it issues. A root that holds its own roster with gen ≥ its next gen issues at 1 + max. (e) Restate H8 l.413, D3 l.191-196 and §6 l.446.
- Obligation: re-prove T2, T2′ and T3 for the roster branch. The version (ceiling_t, signer, gen, h) still extends the order. Re-prove rosterEff_F for the new ROSTER_eff order. Add a lemma that equal-gen same-signer rosters form a held antichain bounded by the slice. Re-run the SPARK Views and Frontier proofs that use Gen_Lt.

#### H2. A root-void delivered alone through OPEN makes ROSTER_eff fall back to a stale roster (F5)
- What: OPEN carries only founding REVOKE frames, and the receiver applies them before the gate (DESIGN.md:903-916, :948, §6 l.599-605). ROSTER_eff is the (gen, h)-maximum over non-root-voided signers (l.249-250). Recovery issues its steps "together" (l.479-491), but OPEN delivers step 2 alone.
- Scenario: Founding roster r0 (gen 5) lists X. Certified root R issues r1 (gen 9), which removes X, and REVOKE_R(X). Replica C holds r0, r1 and REVOKE_R(X). R is stolen. The founding key issues REVOKE(R, 0), recovery roster rF and REVOKE_F(X). X, now a non-member, replays the public REVOKE(R, 0) to C in an OPEN before C holds rF. R is root-voided at C, so r1 and REVOKE_R(X) stop counting. ROSTER_eff falls back to r0, and X passes the gate.
- Fix: a store-local quarantine flag outside F. Set it when a pre-gate OPEN root-voids the signer of the current ROSTER_eff. While it is set, admit a peer only through a HELLO credential that is a founding-signed roster and that becomes ROSTER_eff when applied. Take no bundles and seal none while the flag is set. In Kome.Roster, rF omits removed members, and the founding key issues REVOKE_F(X) before REVOKE(R). Do not use gen or epoch non-regression as the test (G_rv = largest gen of a root-voided roster): the thief sets gen = 2^48 − 1, and then no recovery roster can exceed it.
- Obligation: while the flag is set, every admitted peer is listed in a newly admitted founding roster. The flag clears only when such a roster is ROSTER_eff.

#### H3. Log bytes are a shared capacity class that nothing accounts for (F37)
- What: E1 (DESIGN.md:52) and H8 l.412 say that a flood cannot block the founding REVOKE. data_cap counts records, not bytes. kome-store.ads:469-475 (At_Bound) applies Log_Short to every class, also to records that free room.
- Scenario: data_cap = 30 000 and Log_Cap = Log_Max = 2^30. An authorized writer makes 26 200 new cells with 40 960-byte values. Each write is OK. The log holds about 1.078e9 bytes, which is more than 2^30. The founding REVOKE(W, 0) (275 B) gets NO_SPACE. Compact frees nothing, because every record is held. The store is stuck for good.
- Fix: a derived precondition on Open and on Open_From_Log (Log_Cap is not logged and can change at reopen): Log_Cap ≥ Header_Len + Expire_Len + (data_cap + Signers_Max·slice)·Entry_Max + Entry_Max, where Entry_Max = Apply_Prefix + the largest frame of any kind, rosters included. State it as a bound on data_cap for a given Log_Cap. Add a LOG_FULL status and a compact-and-retry duty for the binding.
- Obligation: Valid(S, F) and Count(F) ≤ Cap + Signers_Max·Slice imply that after Compact, Body_End + Entry_Max ≤ Log_Cap. The proof uses Compact's existing layout Post. Then the log row never refuses on a compacted store.

### 2.2 Medium

#### H4. Re-delivery of a retained frame after its DEL has expired brings the entity back (F1)
- What: Expiry is not a join-endomorphism. expire_h(F({d, p})) = {}, but F(expire_h({d}) ∪ {p}) = {p}. A4′ (DESIGN.md:1161-1162) only asks that d reach every member. Bundles carry no freshness (§8 l.1037-1052). The synthetic nonce makes a replayed bundle identical to the original. §7 l.796-822 calls the residual "the documented one".
- Scenario: Day 0: a relay stores bundle B0 with PUT p (author Alice ∈ W) on entity E. Day 1: Alice DELs E, and every member gets d. Day 182: every replica expires d (del_ttl_eff = 180 d). Day 200: the relay delivers B0 again to Y at the same epoch. Y holds p and spreads it. A read-only member with a saved frame does the same, and so does a store restored from backup that did receive d.
- Fix: restate A4′ as "no frame of a record that d dominates is delivered to a replica after that replica expires d". Name relays, non-writer members and store restores in H7, H8 and the DESIGN.md:410 row. Treat a restored store as a straggler. Containment: bind t_seal in the bundle AD and drop data items with t ≤ horizon when a bundle is opened (sessions still carry them). Do not advance the epoch at each refresh: that uses up the u16 epoch space and refuses honest store-and-forward bundles.
- Obligation: T11(c) under the restated A4′. With the filter, a lemma that opening a bundle at horizon h applies no data record with t ≤ h.

#### H5. The OPEN root-void set misses roots whose records the sender does not hold (F6, F14, F139)
- What: The set is "each founding-issued REVOKE in the sender's F whose subject signed an authorization record that the sender holds" (DESIGN.md:905-908). The D13 release claim ("one honest contact releases a replica", §6 l.489-491, l.602-605) needs the REVOKE of the root that captured the replica. kome-reconcile.ads:1420-1422 takes a caller-selected Voids array. "At most 15 frames" is also false: REVOKEs are never dominated, so one subject can have several founding REVOKEs (F139).
- Scenario: The founding key certifies R. R is stolen before it signs anything that honest replicas hold. The thief captures C with HELLO credential rT (gen 2^48 − 1). The founding key issues REVOKE(R, 0). Honest A never held an R record, so A's OPEN to C leaves out REVOKE(R, 0). C stays captured.
- Fix: one founding REVOKE per root-voided subject (the from_t = 0 one with the least h), independent of what the sender holds. Fill the remaining frames with other founding from_t = 0 REVOKEs. Or make root revocations recognizable from the bytes: a founding REVOKE of a root embeds the subject's certificate (cert_cap and cert_sig, +70 B). State the bound as "at most 15 subjects". The receiver filter (verify only frames whose subject is a held signer) keeps pre-gate work bounded. C holds rT, so R is a held signer.
- Obligation: for every root-voided subject in the sender's F, the OPEN carries one REVOKE of it, up to 15 subjects.

#### H6. A stale founding device opens a segment from its stale F (F19, F30)
- What: A segment opens at 1 + the largest epoch of the non-voided rosters in F (DESIGN.md:546-551), with gen = 1 + the largest gen (l.1205-1207). The founding key is kept cold (l.117-120). ROSTER_eff is the (gen, h)-maximum over all signers (l.249-250). F30 (necessary-assumption, medium) states the freshness need that this fix removes.
- Scenario: The founding device last synced at gen 20, epoch 7. R1 has since issued gen 30 at epoch 9 (segment 0, top 4095). R2 is stolen. The founding key issues REVOKE(R2, 0) and an opener at gen 21, epoch 8, with a new top. ROSTER_eff stays R1's gen-30 roster at epoch 9 of the old chain. Bundles stay under keys that the voided thief derives from its old top.
- Fix: fixed segment boundaries. Segment j covers epochs [4096·j, 4096·j + 4095], so top = s + 4095. The founding key opens segment j + 1 at s = top_old + 1. It knows top_old, so it needs no fresh F. With the epoch-first ROSTER_eff of A2, every new-segment roster beats every old-segment roster whatever its gen. A certified root that holds a founding roster at an epoch above its known segment refuses to issue until it has the new top.
- Obligation: after a replica holds a founding segment-opening roster at s, ROSTER_eff.epoch ≥ s. This also discharges IA-12.

#### H7. A stolen root sets how much gen space remains (F133, F141, F152)
- What: gen = 1 + the largest non-root-voided gen (DESIGN.md:1205-1207). Roster Well_Formed has no bound on gen (kome-records.ads:987-994). A stolen root sets gen = 2^48 − 2 (§6 l.495-498). Honest roots copy it, and the copy stays after the root-void. At gen 2^48 − 1, ROSTER_eff (l.249-250) changes only by grinding h, and the cost doubles at each change. T13 (l.1127-1130) only says that emission fails at the bound.
- Scenario: Thief R issues r_T at gen 2^48 − 2. Honest R2 does not yet hold REVOKE(R, 0) and refreshes at gen 2^48 − 1. The founding key root-voids R. R2's roster is ROSTER_eff at the maximum gen. Each later change needs h above the current h: about 2, 4, 8 ... tries. After about 40 membership changes or refreshes, no root can issue a winning roster.
- Fix: add "gen ≤ ceiling_t" to Roster Well_Formed. It is byte-local, and with ceiling_t ≤ cert_cap it caps a certified root's gen at its cap. Honest-issuer rules: never emit gen > G_honest = 2^47. When 1 + max > G_honest, refuse with STOLEN_ROOT_SUSPECTED and wait for the founding root-void. Count only gens ≤ G_follow in "1 + max". The founding opener wins by epoch (A2), not by gen.
- Obligation: the decode predicate in the Records proofs. The issuer bound in Kome.Roster. A T13 clause that states the bound.

#### H8. The recovery procedure has no membership step (F145)
- What: Recovery steps 1-4 (DESIGN.md:479-491) re-grant keepers, root-void R, re-sign revocations and open a segment. No step removes the stolen root's own device entries or the members it added. The gate is ROSTER_eff membership (l.599-600). l.504-508 and l.551 claim that a root-voided root sees no later key.
- Scenario: A laptop holds root key R and is listed as member (sign_pk_L, dh_pk_L). It is stolen. The founding opener lists the current ROSTER_eff members, so L gets a box with k_s. The thief passes the gate and reads every new bundle.
- Fix: in step 2, the founding key also issues REVOKE(k, 0) for every member sign_pk held by the stolen device. The step-4 roster leaves out those entries, and the owner re-confirms the entries that R added. Kome.Roster checks this. With the REVOKE-aware gate (A3), the gate also refuses them.
- Obligation: after recovery, no ROSTER_eff member has a sign_pk with a counting REVOKE. Restate T14 so that it covers the devices of a root-voided root.

#### H9. Two roots at the same epoch share k_e, so a removal fails when a rival roster lists the removed member (F26)
- What: k_e = Iter(top, top − e) depends only on top and e (kome-epochs.ads:5-11; DESIGN.md:537-544). A losing roster of another signer stays in F.
- Scenario: R1 issues r1 (gen g, epoch e+1, removes X). At the same time, R2 issues r2 (gen g, epoch e+1, lists X, removes Z). h(r1) > h(r2), so r1 is ROSTER_eff and X fails the gate. r2 stays in F, and its box gives X k_{e+1}. X reads every bundle at e+1.
- Fix: a re-key-on-divergence rule in §10.3 and Kome.Roster. A root that holds a non-root-voided roster r′ with r′.epoch = ROSTER_eff.epoch that lists a (sign_pk, dh_pk) that ROSTER_eff does not list issues its next roster at ROSTER_eff.epoch + 1. Stronger alternative: a fresh per-roster bundle secret b_e in each box (+32 B), with k_b = BLAKE2b("kome/bundle" ‖ b_e ‖ ns) (see H31).
- Obligation: T14′. A key not listed in ROSTER_eff cannot derive the bundle key in use once the re-keyed roster is ROSTER_eff.

#### H10. A joining device has no freshness anchor, and an empty store cannot join through a stale replica (F62, F142)
- What: A joiner opens with (root_pk, salt) only (kome-store.ads:626-634). The HELLO credential is applied before admission, and then the gate is evaluated again (DESIGN.md:607-612, §8 l.925-939). An empty F has no roster, so the joiner admits nobody. It reaches only a replica that already holds its adding roster, which contradicts §6 l.607-612 (F142).
- Scenario: X is removed (REVOKE(X, 0), roster gen g+1). Weeks later phone P (listed in gen g+2) opens with (root_pk, salt). X reaches P first and sends cred = roster g, which lists dh_X. P applies it, ROSTER_eff(P) = g, and P admits X.
- Fix: define the join hand-off as (root_pk, salt, frame of the roster that lists the newcomer). Put_Frame can already apply a signed root roster to an empty store. Join gate rule: while F holds no non-root-voided roster that lists my own dh_pk, accept only a credential that lists both the peer's Noise key and my dh_pk. Refuse any other credential, and do not let it change ROSTER_eff. Add the hand-off to the unbuilt-duty list.
- Obligation: a joiner's first ROSTER_eff is at least as new as the roster that added it.

#### H11. The gate is evaluated once, at Admit (F8)
- What: kome-reconcile.ads:69-75 and :1453-1490 check the gate at Admit. Receive (l.1575-1577) has no gate condition. Session_Msgs_Max = 2^29 (l.1283). DESIGN.md:641-643 says that a replica that holds the revocation admits X to no session.
- Scenario: X is in a session with root phone P. On P, the owner issues REVOKE(X, 0) and a removal roster. The session continues. X ships newly signed PUTs and DELs. P applies them (X ∈ W) and keeps sending data.
- Fix: Kome.Store keeps a monotone Auth_Gen that goes up with every applied ROSTER, REVOKE or GRANT. The session records Gate_Gen at Admit. Receive and Next_Phase check the gate again when Auth_Gen ≠ Gate_Gen, and abort if it fails. No wall-time bound is needed.
- Obligation: every data frame applied from session S was applied while Gate(F, peer) held, with Gate_Gen = Auth_Gen.

#### H12. A stolen root uses AUTH_FULL arrival order to make maxceil differ between honest replicas (F135)
- What: §7 "What AUTH_FULL means" (DESIGN.md:736-752) lists only surplus records and what they admit. §8 l.966-969 says that after the auth phase both sides have the same maxceil and W. maxceil is a maximum over held rosters (l.242), and a refused roster does not count.
- Scenario: Stolen R has cert_cap now + 60 d. It sends group A 512 REVOKEs on random subjects, which fill A's R-slice for good. It sends group B roster r2 (ceiling now + 60 d) first and the REVOKEs after. B holds r2. A refuses r2 with AUTH_FULL. maxceil(A) ≈ now + 14 d and maxceil(B) = now + 60 d. B admits writes up to now + 60 d, and A discards them permanently. A root-void does not lower maxceil.
- Fix: give each slot a reserved CEIL(s) cell outside the slice. It holds the signer's roster that is maximal in (ceiling_t, gen, h), as a total-order max-register. A slice refusal can never block it. Do not evict the previous roster without a domination relation, because that breaks T3. Until this lands, add the case to §7 and correct §8 l.966-969.
- Obligation: maxceil(F) is the same for every arrival order of one record set, AUTH_FULL included.

#### H13. The all-zero key is a small-order point, and a GRANT to it allows universal forgery (F13, F35)
- What: 32 zero bytes encode an order-4 Ed25519 point (spark/vectors/crypto.txt:154). Verify is cofactored and accepts canonical small-order keys (kome-crypto.ads:35-51). Make_Grant has no Pre on Subject (kome-records.ads:1285-1301). GRANT Well_Formed checks no subject (l.1357-1362). Cert_OK checks no signer (l.231-236). The question is an open decision (IMPLEMENTATION_PLAN.md:117-119).
- Scenario: An application calls Make_Grant with Subject at the Zero_Key default. The root signs it, and it reconciles. Any party that can deliver frames makes PUT/DEL with author 00..00, t = maxceil and sig = 01 00..00 ‖ 00..00. Verify accepts them. REVOKE(00..00) makes them void, but W never shrinks, so they still dominate and free honest values. Nobody is attributable.
- Fix: decide the open item as "refuse". Add `not Is_Small_Order_Point (PK)` inside Kome.Crypto.Verify. It is a byte comparison against the 8 canonical torsion encodings. Add the same Pre to Make_Grant, Make_Cert and Store.Open (root_pk). Add Wycheproof small-order public keys as invalid vectors.
- Obligation: Verify(·, A, ·) = True implies that A is not small-order (a Post today, a SPARK expression after A25).

#### H14. The ceiling clamp lets a clock that is ahead expire DELs early, and the design's own parameters permit it (F15, F49)
- What: horizon = min(now_local, maxceil) − del_ttl_eff (DESIGN.md:764-772; kome-store.ads:519-524). A clock ahead by δ ≤ maxceil − now expires DELs δ early. A4′ uses the window del_ttl (l.818-822, l.1161). Caps run "some weeks ahead" (§2 l.126), and Del_TTL_Min = 7 d (kome.ads:100), so the lead can exceed del_ttl (F49). No §10.3 rule bounds the lead.
- Scenario: lead 21 d, del_ttl_eff 180 d. B's clock is 20 d ahead. At t0 + 160 d, B expires d. At t0 + 170 d, stale C syncs with B. B admits C's p and later spreads it. With del_ttl = 7 d and lead 21 d, a spoofed-ahead device holds no tombstones at all.
- Fix: an honest-issuer rule in §10.3 and Kome.Roster: ceiling_t ≤ issuer_now + Cap_Lead and cert_cap ≤ now + Cap_Lead, with Cap_Lead < Del_TTL_Min (for example ≤ del_ttl_eff / 2). Restate A4′ with the window del_ttl_eff − Cap_Lead, measured against the fastest replica's horizon. Optional code change: horizon := min(now_local, maxceil − del_ttl_eff) − del_ttl_eff.
- Obligation: T11(c) names the lead that it tolerates. Kome.Roster refuses a ceiling beyond Cap_Lead.

#### H15. A stolen root, or a root's own refresh, lowers del_ttl_eff (F3, F23)
- What: Roster domination ignores del_ttl (DESIGN.md:173-174; kome-headers.ads:80-83; Frontier.lean:150). del_ttl_eff is a maximum over held non-voided rosters (l.251-252). D10 (l.46), §7 l.789-794 and §6 l.498 say a stolen root can only lengthen tombstone life.
- Scenario: R's roster r1 sets del_ttl 3 650 d, the only long value. A thief signs r2 (gen + 1, ceiling ≥, del_ttl 7 d). r2 dominates r1 everywhere, and a root-void of R does not bring r1 back. del_ttl_eff falls to the founding value. Members that sync once a year now bring back deleted data. An honest refresh of R with a lower del_ttl does the same.
- Fix: add `∧ r′.del_ttl ≥ r.del_ttl` to the roster clause. It is still a product order that the version extends. A root that lowers its own del_ttl then leaves an antichain of two rosters in its slice. Otherwise, correct D10, §6 and §7: a root can lower its own contribution, and only the other non-voided signers set a floor.
- Obligation (with the conjunct): a Lean theorem delTtlEff_F (del_ttl_eff(F(H)) = del_ttl_eff(H)), proved like maxCeil_F. Re-prove Lemma_Roster_Dom.

#### H16. Pins at a stolen root's cap outlive every honest refresh (F101, F114)
- What: H8 l.412 says "pins stop at the next roster refresh". A certified root's ceiling_t ≤ cert_cap (kome-records.ads:991). maxceil keeps the largest cap that a stolen root used (DESIGN.md:509-511). Recovery steps 1-4 (l.479-487) have no step that lifts maxceil above it.
- Scenario: Honest R2 has cap now + 7 d. Stolen R has cap X = now + 60 d. R grants G and raises maxceil to X. G pins 1 000 cells at t = X. The root-void makes G void. R2's weekly refresh stays below X, so honest writes to those cells are SHADOWED until wall time passes X. The owner's DELs at t = X lose the author tie.
- Fix: in recovery step 4, and in any founding roster issued while maxceil(F) > now, set ceiling_t := max(intended, maxceil(F) + 1). The founding key is uncapped, so it can. Restate H8: pins stop at the first roster whose ceiling exceeds the pinned t.
- Obligation: none in Lean (T9 already states the chase). Kome.Roster checks that the recovery roster's ceiling > maxceil(F).

#### H17. Store-and-forward replicas cannot cross an epoch change (F96, F115)
- What: Kome accepts bundles only under ROSTER_eff.epoch (DESIGN.md:614-619). The roster that raises the epoch travels only in bundles under the new key. The chain runs only backward (l.531-536), so a replica at e cannot open e+1.
- Scenario: A, B and D sync only through a mailbox. R removes X at e+1. A moves to e+1 and seals under k_{e+1}. D (at e) cannot open A's bundles. B's bundles at e do not carry r_{e+1}. D never moves forward.
- Fix: a sender rule only, with no receiver change. For a set period after its ROSTER_eff.epoch rises from e to e′, a replica also sends an auth-only bundle under k_e. The bundle carries the new roster and the REVOKEs before it. These records are signed and admitted everywhere anyway.
- Obligation: a replica that holds k_e and gets the auth-only bundle reaches ROSTER_eff.epoch = e′. State in §8 that this gives a removed member no write path.

#### H18. CLONE_SUSPECTED misses clones that write at the same pace (F95)
- What: Clone_Detected = O.Present and O.Seq > Seq_Self (kome-emit.ads:214-219). The H8 "Cloned key" row (DESIGN.md:411) says "flagged".
- Scenario: D1 and D2 hold key K with seq_self = n and are partitioned. Each writes at seq n+1. After sync, Max_Own_Seq = n+1 = seq_self on both, so neither flags. F holds pairs of own records with equal seq. A thief who writes at the owner's pace is never flagged.
- Fix: detect at Apply. An incoming record signed by the device's own key that changes F (not a duplicate, not dominated, not an expired DEL) sets CLONE_SUSPECTED. Also flag two held own records with equal seq and different h. Adopt this together with A10 (a frame leaves only after its APPLY is durable). Otherwise a lost log tail raises a false alarm (see refuted item 65).
- Obligation: a Store/Emit Post. An admitted own-key record that was not held before sets the flag.

#### H19. Replies are not bound to obligations: quadratic fingerprint work per session (F10)
- What: Root_Or_Owed accepts g ≥ 1 if the total Pending ≥ Unit/g (kome-reconcile.ads:1511-1512). Range_Fp hashes the whole slice (l.1719-1722). Range_Budget = 4|S| + 4 (l.1320-1328). l.130 claims "a peer can only answer what it was asked". The 16x egress half of F10 is refuted: it is a budget-bounded amplification by design.
- Scenario: Member B and replica A, where A holds n = 2^20 elements. B sends RANGE(g = 1, [Data_Lo, Max_Key), random fp) many times. Each passes Root_Or_Owed. Each costs about 32·2^20 BLAKE2b. About 2^18 repeats give about 8.8e12 hashes per session.
- Fix: wire D15 prefix sums into Range_Fp (at most 64 adds and one hash for each fingerprint). Bind replies to a FIFO of open obligations (lo, hi), bounded by Range_Budget. Each direction is in order, so reply groups arrive in request order. Accept a reply only when it matches the head obligation.
- Obligation: Complete implies that each obligation got exactly one full reply group. Work per session is O(n log n).

#### H20. Noise XX gives any stranger the device's long-term dh_pk (F105)
- What: Noise XX uses the device's dh_pk as its static key (DESIGN.md:1035-1036), and OPEN follows the handshake (l.948). One device key serves all collections (§5 l.397-400). REQUIREMENTS H3 (l.35-36) allows only sizes, timing and routing keys.
- Scenario: A BLE or LAN scanner runs XX with each device that advertises Kome. It records dh_pk and then ns from OPEN. It tracks the device across places and IP changes. The same dh_pk with two ns values links two memberships.
- Fix: use Noise XK. The initiator takes the responder's static key from its ROSTER_eff (or its credential) and binds ns in the prologue, so the responder's static key never crosses to a stranger. Per-collection static keys (dh_sk_ns = KDF(device secret, ns)) remove the cross-collection link.
- Obligation: none in Lean. State in §8 what a stranger learns, and update H3.

### 2.3 Low

#### H21. DEL floods hold data capacity for del_ttl_eff, and the NO_SPACE disagreement also covers honest records (F12, F93)
- What: A DEL is dominated only by a higher DEL (DESIGN.md:172). H8 l.412 ("floods stop at the REVOKE plus owner DELs") and §10.5 l.1220-1226 are false. kome-frontier.ads:242-246 gives No_Space when the data row is full and the record frees nothing. §7 l.736-752 analyses disagreement only for AUTH_FULL.
- Scenario: K emits about data_cap DELs on random entities at t = maxceil (2^20 × 141 B ≈ 148 MB). The owner revokes K and issues purge DELs, which are SHADOWED or free one record each. Honest new PUTs get NO_SPACE until expiry. With equal caps, A holds honest P and refuses a flood record, while B refuses P.
- Fix: restate H8 and §10.5: room returns only when min(now, maxceil) ≥ t_flood + del_ttl_eff. §10.5 l.1223: the disagreement covers any new-cell data record, honest ones included. Report NO_SPACE refusals of peer-offered records as a replica status. A per-author quota (E8) is optional.
- Obligation: with a quota, an honest author under quota never gets NO_SPACE.

#### H22. Under a stale maxceil the clamp back-dates writes, so a DEL can be born expired (F16)
- What: t_emit is clamped to maxceil (DESIGN.md:365). l.392-395 says a device with no RTC works. The H8 "Clock behind" row says "its cells only". Emit statuses are OK or SHADOWED only (kome-emit.ads:6-13).
- Scenario: lead 21 d, del_ttl_eff 180 d. Laptop D goes offline on day 0 with maxceil = day 21. On day 300 it deletes E, so t_emit = day 21. It reconnects on day 305. Peer B has horizon day 125, so B applies d, drops E's fields and does not hold d. Stale copies come back.
- Fix: Choose exposes clamped := u > maxceil (u = max(now_ms, floor.t + 1)) and born_expired for a DEL whose t_emit + del_ttl_eff ≤ now, as out flags next to CLONE_SUSPECTED. The caller syncs before it writes such a DEL. A3 states that the refresh must reach every partition.
- Obligation: Choose reports CLAMPED iff t_emit < now_ms.

#### H23. One torn, corrupt or duplicated log entry makes the store unopenable (F38, F53, F64, F107)
- What: Open_From_Log is all-or-nothing (kome-store.ads:836-851; kome-store.adb:4031-4060, :4318-4325). test_store.adb:919-920 asserts Malformed for a cut last entry. Replay re-verifies every signature (adb:3644-3690), so one flipped byte refuses the whole log. Replay refuses a duplicated APPLY (adb:3883-3887) that the live Put_Frame treats as OK (adb:2239-2249; test_store.adb:923-924). REQUIREMENTS H8 says "must not permanently brick".
- Scenario: power fails 20 000 bytes into a 41 141-byte APPLY. Or a binding retries an append after EIO, although the bytes reached the disk. Either way, the next open returns Malformed and the device cannot open the collection.
- Fix: keep Open_From_Log strict. Add a proved Torn_Tail_Length(Input), or a Valid_Length out parameter that the loop invariant at adb:4317-4320 already supports, so that the binding truncates to the last complete entry. Binding duty: write each append at the Log_Length(S) offset from before the call (pwrite), so a retry overwrites and does not duplicate. For corruption, use prefix replay up to the first entry whose check fails, report DEGRADED and sync again. Do not skip entries in the middle.
- Obligation: T18-prefix. Every entry-boundary prefix of a log that the store wrote replays OK. The log is append-only, so the existing invariant gives this.

#### H24. EXPIRE entries and HEADER capacity bytes have no integrity, and replay applies any horizon it parses (F39, F52)
- What: kome-store.ads:111-118 says "Replay trusts the logged horizons". The EXPIRE branch (adb:4087-4115) calls Do_Expire for any code. "No horizon" is the sentinel 2^48 − 1 (kome-store.ads:35-39), which H6 forbids.
- Scenario: on FAT or ext4 data=writeback, a torn EXPIRE gets horizon bytes 0xFFFF_FFFF_FFF0. Replay drops every DEL, and stale PUTs come back.
- Fix: in Replay_Entry, clamp the EXPIRE horizon down to Horizon_At(F, U48'Last) = maxceil(F) − del_ttl_eff(F) at that point. T18 already allows a lower reopened horizon (§10.10(b)), so a valid compacted log is never refused. Give "no horizon" its own op (EXPIRE_NONE). A party that can write the file can do more harm than this, and that threat belongs to the host (G14).
- Obligation: every EXPIRE that the store writes meets the bound. This follows from Ceil never decreasing and del_ttl_eff ≥ Del_TTL_Min.

#### H25. No post-compromise security for members (F63)
- What: Every key of a segment is a function of its top (DESIGN.md:530-544). Links give all history (l.556-558). Members have no key-update path, and §10.3 (l.1205-1215) has no rotation rule.
- Scenario: Malware copies member M's dh_sk once and is then removed. Nobody knows, so M is never revoked. The attacker opens M's box in every later roster and reads every bundle that relays carry, for the life of the collection.
- Fix: do not mix per-roster randomness into k_e: that breaks E3 same-epoch agreement and the walk down the chain. Add a §9 assumption or T14 clause: member dh_sk stays secret, and there is no post-compromise security. Add a rotation duty: a member proposes a fresh dh_pk, the next roster lists it, and roots re-key members periodically.
- Obligation: T14 restated with the dh_sk premise.

#### H26. Every open re-verifies one signature for each logged record (F65)
- What: Replay runs Decode_Frame with signature checks (kome-store.adb:3644-3690). The log can reach Log_Max = 2^30 (kome-store.ads:200-203). Dominated APPLYs stay until a caller compacts (:79-89).
- Scenario: a phone holds a 600 MB log with about 4 million entries. At about 150 µs per verify, an open takes about 10 minutes, and again after every crash.
- Fix: make compaction a store duty. After an append, when the entry count passes k·|F| + c (for example k = 2), the store runs Compact. Compact is already proved with T18. State the replay cost bound in §7.
- Obligation: after each operation, log entries ≤ k·|F| + c.

#### H27. An entity DEL concurrent with a field PUT leaves a partial entity (F67)
- What: exists holds iff some field is live (DESIGN.md:268-269). A DEL removes field versions below d.v only (l.170-172). §10.4 does not mention the anomaly.
- Scenario: A deletes contact E at t = 1000. B, offline, edits only E.phone at t = 1003. After sync, exists(E) is true, and every other field is None.
- Fix: document the semantics after DESIGN.md:269 and in §10.4. Give the application rule: a required-field check with a follow-up DEL, or C10 MVREG.
- Obligation: none.

#### H28. The write floor ignores DELs that the device has already expired (F86)
- What: The floor is max(cell.v, deleted_at) over held records (DESIGN.md:364-369; kome-emit.ads:138-143). After a clock reset, the caller passes Now = 0 (kome-emit.ads:81).
- Scenario: P expires d (d.t = 200 d) at horizon 220 d. The RTC resets with no network. The user writes field a of E, and the write gets t far below 200 d. Replicas that still hold d drop the user's write.
- Fix: a monotone per-store mark, the largest d.t of any DEL that Expire removed or APPLY_EXPIRED applied. Expire only raises it. Replay rebuilds it from the logged entries. Choose requires T_Emit ≥ mark + 1 when mark < maxceil.
- Obligation: a Choose Post, T_Emit > mark when mark < maxceil.

#### H29. A back-dated DEL destroys cold data and leaves no held record (F92)
- What: Step 4 applies an expired-on-arrival DEL for its effect and does not hold it (DESIGN.md:709-713; kome-store.ads:67-70). H8 l.421-425 says each act is "signed, attributable and bounded".
- Scenario: Entity E has been idle 200 d, and del_ttl_eff = 180 d. Writer X, revoked from 0 everywhere, has a member relay DEL(E, t = t0 + 1). Each replica applies and expires it. No record of X's act remains.
- Fix: restate H8 l.421-425 so that "attributable" covers held records only. Optional: keep APPLY_EXPIRED frames that removed records in an audit set outside F and the digest for del_ttl_eff.
- Obligation: none for the text fix. With the audit set, T3 and T6 do not change, because the set is outside F.

#### H30. Recovery from a lost honest root shortens tombstone life (F100)
- What: del_ttl_eff counts only non-root-voided rosters (DESIGN.md:251-252, l.263-266). Recovery steps 1-4 (l.479-487) and §10.3 set no del_ttl for the founding roster.
- Scenario: The founding value is 180 d, and R set 3 650 d for devices that sync once a year. R is lost, and recovery root-voids it. The new founding roster carries 180 d, so yearly devices bring back deleted data.
- Fix: an honest-issuer rule in §10.3 and recovery step 4. A founding roster carries del_ttl ≥ the del_ttl_eff computed before the ceremony's REVOKEs, with the voided root still counted. Kome.Roster checks it.
- Obligation: the Kome.Roster check.

#### H31. Deletion is not erasure (F109, F123)
- What: Dominated APPLY frames stay until a caller compacts (kome-store.ads:79-89). The old file remains after the rename (:134-138). Relays keep bundles, and every later member derives the old bundle keys (DESIGN.md:552-559: "a new member can still read all history").
- Scenario: A user deletes a note. The log, the old file after Compact, and a relay's stored bundle still hold it. A member added three months later walks the chain down and opens the old bundle.
- Fix: state in §7 and §10 that a DEL frees space and does not erase. Use the store-owned Compact trigger (H26). Put a fresh per-roster bundle secret b_e in each member box (+32 B), with k_b = BLAKE2b("kome/bundle" ‖ b_e ‖ ns), so that later members cannot open older bundles. Add at-rest sealing as an unbuilt duty (G14).
- Obligation: if a bound is stated, a bound on the dominated bytes in the log.

#### H32. OPEN delivers the root-void without recovery steps 1 and 3, and a stranger inverts the void view (F136)
- What: The founding key does steps 1-4 "together" (DESIGN.md:479-491), but OPEN carries only founding REVOKEs, to any Noise peer, before the gate (§8 l.903-916). A root_void issuer's REVOKEs stop counting (kome-views.ads Revoke_Void).
- Scenario: R1 revoked writer X. Later R1 is lost, and recovery re-signs REVOKE(X). X, now a non-member, sends REVOKE(R1) through OPEN to a replica P that has not synced since the recovery. At P, X's records read clean and the keepers that R1 granted read void until P's next member session.
- Fix: Kome.Roster issues steps 1 and 3 before step 2. With the reserve of A4, step 2 always fits. The founding REVOKE(R) commits by hash to the list of re-issued records. An OPEN-delivered root-void changes only the gate inputs until every listed record is held. At minimum, document the transient in §6 and §10.
- Obligation: every subset of the recovery records gives, for each p, void(p) equal to the pre-recovery value or the post-recovery value.

#### H33. Chase decouples t from real time: from_t > 0 and C5 fail (F137, F140)
- What: t_emit = max(now, floor.t + 1) (DESIGN.md:365), and no-RTC writes chase (l.392-394). E4 and §6 l.648-653 say from_t > 0 keeps a lost key's earlier records unflagged. C5 (l.25) says "A writer's clock affects only that writer's records".
- Scenario: M pins cell c and entity E at now + 30 d. Honest D writes on day 1, so its t = now + 30 d + 1. D is lost on day 3, and REVOKE(D, from_t = day 3) voids D's day-1 writes. Also: honest A's DEL of E chases to now + 30 d + k and expires 30 days later than A's clock implies.
- Fix: in §6, E4 and the phase-8 revoke API, define from_t as a point on the t axis. For a lost key, from_t := maxceil(F) + 1 (or the largest certified cap + 1) at issue time. Restate C5: there is no device-global adoption, and adoption is per cell through chase, bounded by maxceil − now. Link C5 to the H8 "Clock ahead" row and the chased-tombstone residual (l.823-830). Alternative: REVOKE(X, from_seq). It keeps T12, because the clause is still a REVOKE-indexed down-set.
- Obligation: none for the rule. A T12 re-check for the from_seq variant.

#### H34. No per-cell tombstone: purging a revoked writer's junk destroys honest fields (F138)
- What: DEL has entity grain (DESIGN.md §2). §6 l.633-637 tells the owner to DEL the entities that hold a revoked writer's garbage.
- Scenario: Revoked X writes 1-byte junk fields on 10 000 honest entities that have 5 honest fields each. The purge DELs the entities. 50 000 honest fields are freed everywhere. The purger re-PUTs only what it holds, under its own authorship.
- Fix: state in §6 l.635-637, the H8 row and §10.5 that the purge is entity-grained. For junk on an honest entity, overwrite the junk cell with an empty PUT. Alternative: a cell tombstone DELF(ns, ent, field, t, seq, author), a down-set on the cell key.
- Obligation (DELF only): extend T2′ and T3 to the new clause, and include cell-level deleted_at in the §5 floor.

#### H35. A4′ counts a DEL as delivered before it is durable (F148)
- What: A4′ (DESIGN.md:1161-1162) and T11(c) (l.1120-1121) count arrival. The log is an in-memory buffer with no durability rule (kome-store.ads:41-47). Reconcile has no ack.
- Scenario: At t + 179 d, B applies d (dropping p) in memory and loses power. Replay restores p, and B does not hold d. At t + 180 d every other replica expires d. B spreads p.
- Fix: restate A4′: every DEL is durably held, or durably applied (APPLY or APPLY_EXPIRED), by every member within del_ttl of d.t. A lost log tail counts as a backup restore. Storage and transport duty: flush the log to its length before a session counts as Complete and before a bundle is acknowledged or deleted from a mailbox (a Store Durable_Length or Sync_Point).
- Obligation: T11(c) under the restated A4′.

#### H36. There is no field-level delete (F154)
- What: "An empty value is a value" (DESIGN.md:69). DEL is per entity (l.90-91). exists holds iff some field is live (l.268-269). REQUIREMENTS H7 says that deletion frees space.
- Scenario: A shared list uses one entity with one field per item. After 5 000 items are checked off with empty values, all 5 000 cells stay live and use data_cap forever.
- Fix: document in §2 and §10.6 that DEL is the only removal and is entity-grained, so a removable item must be its own entity. The C ABI delete takes (ns, ent). The alternative is the cell tombstone of H34.
- Obligation: none for the text fix.

### 2.4 Spec-implementation gaps and missing proofs (low)

#### G1. With a store horizon, Put_Frame is not applyD, so T4(b), T10 and T11(b) are false for the implementation (F2, F21, F22)
- What: Put_Frame expires a DEL on arrival (kome-store.ads:67-70, :688-702; kome-frontier.ads:313-345). Lean applyD (Frontier.lean:616) holds and then expires. expire_reapply (Frontier.lean:1001-1018) uses one common h. Counterexample: with one horizon h, p < d and d.t ≤ h, the order [p, d, p, d] gives {} and [d, p, d, p] gives {p}. This contradicts DESIGN.md:1072-1074 (T4(b)), l.1110-1111 (T10), l.1113-1119 (T11(b)), §7 l.691 and §9 l.1176.
- Fix: scope T4(b), T10 and §7 l.691 to runs in which no DEL arrives at or below the local horizon. Add Lean applyH h S r := if isExpiredDel h r then expire h (applyD S r) else applyD S r. List the divergence in §10.1.
- Obligation: expire h (applyAllH h S l) = expire h (applyAllD S l), on the side condition that no record of l dominated by a DEL with t ≤ h arrives after that DEL.

#### G2. T4(c) has a check mark but states the conclusion of T7, which is open (F134)
- What: T4(c) (DESIGN.md:1075-1077) and T7 (l.1095-1102) have the same conclusion. Lean has only auth_first, convergence_two_pass and convergence. README.md:15 and §10.1 l.1180-1182 list T4 as proved.
- Fix: mark T4(c) as "✗ (= T7 delivery + T4(a))". Remove T4(c) from the proved lists. See A23 for the join-inclusion restatement.
- Obligation: the delivery lemma under T7. A complete session gives, in order, the auth part and then the data part of the snapshot difference.

#### G3. Check marks and §10.1 claim Lean statements that do not exist (F4, F76)
- What: §10.1 (DESIGN.md:1180-1182) says that Lean proves T5, T8, T9 and T11. Only parts exist (Frontier.lean:1523-1545: chase, emitT_le). T6 and T10 have check marks and no theorem. T11 has no check mark but is listed as proved. T15-T17 are never stated (l.1142).
- Fix: in §10.1, list the exact README scope: T5 except deleted_at and exists; T8 t-clause and D8, with the seq clause in SPARK Emit; T9 first clause. Add a lean/README row for T10 (StrictTotal Version, convergence, convergence_empty) and an alias theorem. Mark T6 "SPARK (Accumulator, Digest)". Split T11 into (a), (b) proved and (c) argued. Mark T15-T17 "reserved for typed fields (C10), not stated".
- Obligation: optional Lean corollaries deletedAt_congr, exists_congr, seq_emit_gt and chase_after_raise.

#### G4. A duplicated or forged reply closes another obligation, and Complete holds with a range unanswered (F11, F17)
- What: Pending is one aggregate weight (kome-reconcile.ads:1509-1512). Done when Pending = 0 (:1649-1670). DESIGN.md:995-997 says that duplicates cost rounds, not correctness. REQUIREMENTS H4 lists UDP and BLE.
- Scenario: A has open RANGEs X and Y. A datagram layer delivers B's reply to X twice. Pending = 0, so A is Done. B's reply to Y gets S_Unexpected.
- Fix: replace l.995-996 with "the session layer requires exactly-once, in-order delivery; Noise's nonce counter rejects a replayed message, and a rejected message counts as loss". Or use the obligation FIFO of H19.
- Obligation: Complete implies that each obligation got exactly one full reply group.

#### G5. T14's premises do not support bundle secrecy (F153)
- What: T14 (DESIGN.md:1131-1136) reduces to chain one-wayness plus "BLAKE2b as a PRF" keyed by k_{e+1}. A removed member holds k_e = BLAKE2b(k_{e+1} ‖ "prev") (l.530-536), so the PRF reduction fails (the key-regression pitfall).
- Fix: restate T14 as indistinguishability. Model BLAKE2b-256 as a random oracle over domain-separated inputs. Or use keyed BLAKE2b (crypto_blake2b_keyed) as one PRF: k_e = f_{k_{e+1}}("kome/prev") and k_b = f_{k_e}("kome/bundle" ‖ ns). That gives key-regression security from one PRF assumption.
- Obligation: the paper proof under the stated premise.

#### G6. The accumulator width argument has no bound in Kome's own parameters (F125)
- What: DESIGN.md:888-890 cites about 2^128 work with 2^64 records. Held_Max = 2^20 (kome-frontier.ads:77). No lattice (SIS) estimate is given (A2 l.1158, T6).
- Fix: state that 2^128 is Wagner's minimum over all k. Under Held_Max, a colliding pair has at most 2^21 signed summands, so the cost is at least about 2^186. Add one line for the SIS route mod 2^4096 with an l∞ bound of 1.
- Obligation: the parameter claim in A2.

#### G7. Nothing ties a roster's box_pk and boxes to the Box_Key inputs (F33)
- What: Make_Roster takes Box_PK and Members as independent bytes (kome-records.ads:849-880). Box_Key computes box_pk internally. E5 (DESIGN.md:139-143) says that every listed member can open its box, but decode does not check this.
- Scenario: a builder retries with a new eph_sk2 and keeps the first box_pk. The roster decodes and wins. Every Unbox_Key returns Not_Authentic, and nothing reports it.
- Fix: one Kome.Roster.Build that takes (Eph_Secret or k_e, Root_PK, Salt, E, members) and builds box_pk and the boxes by construction. It wipes the secret. Make_Roster is private to it. Reword E5. Box_Key has no Post on the cipher bytes (kome-epochs.ads:385-387), so bind by construction. A6 also closes this.
- Obligation: Build Post C.Box_PK = X25519_Public(Eph_Secret).

#### G8. Views.Is_Void is total and answers True off data (F25)
- What: Is_Void has no Pre (kome-views.ads:254-255), and Lemma_Is_Void_Def (:350-363) has no Is_Data. It returns True for the founding roster (root_pk is not in W_eff) and for No_Header. Lean voided is False off data (Frontier.lean:1039-1042).
- Fix: Is_Void(S, P) := Is_Data(P) and then (...). Use the same guard in Revoke_Void and add the conjunct to the lemma.
- Obligation: agreement with Lean voided.

#### G9. D5 forward secrecy and T14 ignore roots (F27)
- What: Every root holds top_s (DESIGN.md:537-544). D5 (l.40) and l.565-569 claim forward secrecy, and T14 (l.1131-1136) leaves roots out.
- Scenario: a backup of certified root C's storage leaks. The attacker derives up to 4 095 future epochs and all history through the links.
- Fix: restate T14 to exclude the non-root-voided roots of the segment. Add a "top leaked" procedure: the founding key opens a new segment without a root-void.
- Obligation: the restated T14.

#### G10. top_s is unspecified and carried in no record (F28)
- What: DESIGN.md:539-540 says "for example min(s + 4 095, 65 535)". k_e depends on top − e (kome-epochs.ads, Lemma_Derive_Shift).
- Scenario: R1 uses top_s = 65 535, and R2 uses s + 4 095. For one epoch, both boxes open with Box_OK, but the keys differ. Members split silently.
- Fix: make top_s a function of s, and choose one rule. Use H6's fixed boundaries (top = s + 4 095), or 65 535 for every segment (at most Max_Steps = 2^16 − 1 hashes per derivation). Delete the "for example" clause.
- Obligation: none beyond Derive's existing bound.

#### G11. An epoch number is not a key identifier (F29, F66)
- What: A new segment starts at 1 + the largest epoch, inside the old segment's range (DESIGN.md:546-551). The keyring is unspecified. The bundle header shows ns and the epoch to relays (§8 l.1040-1052).
- Scenario: before its root-void, stolen R boxes a key K* at epoch 4 000, and member M caches it. Later honest rosters reach epoch 4 000. M seals under K*.
- Fix: define bundle_key(F) = Unbox(own member entry of ROSTER_eff). Compute it again whenever ROSTER_eff changes, and never cache keys by epoch number. H6's fixed boundaries remove the overlap.
- Obligation: sealer and opener both use bundle_key(F).

#### G12. The pre-gate HELLO credential lets a root-voided signer inject rosters (F31)
- What: The caller applies the credential in Gate, before or after Admit (kome-reconcile.ads:50-54, :76-78; DESIGN.md:925-939). §6 l.505-508 and A1 l.1151-1152 say that nothing a root-voided root signs afterwards reaches the replica.
- Scenario: Y holds REVOKE(R, 0). R opens sessions again and again, each with a fresh roster as its credential. Y applies each one and fills R's slice. R is still refused.
- Fix: before it verifies a credential, the receiver drops it and aborts if F holds a founding REVOKE of the credential's signer. This is the same lookup that OPEN uses.
- Obligation: a credential from a root-voided signer never changes F.

#### G13. No phase owns the storage binding (F41)
- What: Crash atomicity, write failure after apply, preallocation, a single-writer lock and durability before send exist only as comments (kome-store.ads:18-20, :41-47, :129-138). IMPLEMENTATION_PLAN.md l.89-113 lists only Transport and Kome.Roster.
- Scenario: Put_Frame returns OK for a REVOKE. Then write() fails with ENOSPC. The binding keeps serving the REVOKE, and after a restart it is gone.
- Fix: add a "Storage binding" entry: a prefix-preserving append; on any write error, discard the in-memory (S, F) and run Open_From_Log; preallocate Log_Cap; take an exclusive lock; fsync before a record is visible to Reconcile or Emit; Compact = write new, fsync, rename, fsync dir.
- Obligation: none new. State the duties against T18.

#### G14. At-rest sealing exists only as one sentence (F42)
- What: DESIGN.md:659 says "sealed at rest under the device key (a later layer)". It has no requirement, phase, key or format. It conflicts with key separation (l.567-569), because the device key is the signing key. kome-store.ads:111-118 trusts logged horizons because of it.
- Fix: delete l.659. State that the log is plaintext and has no authentication, and that integrity and confidentiality at rest belong to the host. A truncated log is equivalent to a stale replica. EXPIRE horizons get the H24 clamp.
- Obligation: none.

#### G15. Store memory is about 5×Log_Cap resident, plus full copies (F43)
- What: Bnd is an Offset_Array(1 .. Log_Cap) of 4-byte entries (kome-store.ads:1035-1058). Compact copies the log (kome-store.adb:3539), and Open holds Input and Image (:4272).
- Fix: add a discriminant Bnd_Cap with Bnd_Cap ≥ Log_Cap / Min_Entry in Valid (RM 3.8(12) allows it). Patch the HEADER caps in place and do not copy. Let Compact write into a binding buffer.
- Obligation: Chain already proves NB ≤ LL / Min_Entry.

#### G16. The verification equation and the del_ttl rule are not normative (F48)
- What: D10 (l.46), E5 (l.56) and §7 l.790 say "clamps", but §2 rule 3 and kome-records.ads:984-992 refuse. §10.9 (l.1242-1245) accepts "any verifier with RFC 8032". kome-crypto.ads:49-51 is cofactored.
- Scenario: a clamping implementation holds a roster with del_ttl = 0, and Kome discards it. A PUT with R′ = R + T8 passes the cofactored check and fails a cofactorless one. The replicas never converge.
- Fix: change the wording (E8). State the full predicate in §2 l.78: canonical A and R, S < L, and [8][S]B = [8]R + [8][k]A. Name this equation in §10.9. Make the Wycheproof and torsion vectors normative.
- Obligation: none (spec only).

#### G17. The Compact Post breaks the project's proof-hygiene rule (F85)
- What: CONVENTIONS.md l.141-145 requires both cvc5 and z3 and a split above about 10 s. The Compact Post proves with z3 alone in about 12.6 s (IMPLEMENTATION_PLAN.md l.130-135).
- Fix: split the Post into ghost lemmas (Lemma_Compact_Index, Lemma_Compact_Layout) and call them at the end of the body. Drop In_Old_Order (A28). Then delete the Proof margin item.
- Obligation: the split lemmas.

#### G18. Put_Frame keeps a stale horizon after del_ttl_eff rises (F99)
- What: The Put_Frame Post has Horizon(S) = Horizon(S'Old) (kome-store.ads:671). DESIGN.md:774-778 says that a higher del_ttl_eff makes fewer DELs expire on arrival.
- Scenario: the auth phase applies a roster with del_ttl 3 650 d. In the data phase, a DEL with t = now − 200 d expires on arrival under the old 180 d horizon.
- Fix: add a phase-9 transport duty. After the auth phase and before data, if del_ttl_eff changed, call Expire(Now). It lowers the horizon and logs EXPIRE.
- Obligation: none new.

#### G19. README says "far" is a function of F (F102)
- What: README.md:94 lists far among the functions of F. Is_Far(P, Now, Slack) reads the local clock (kome-views.ads). DESIGN §3 and T5 (l.1086-1091) do not list it.
- Fix: make README.md:94 match T5's list, and describe far as a per-replica advisory predicate.
- Obligation: none.

#### G20. "The founding key stays within 15 certificates" contradicts cap renewal (F106, F111)
- What: §10.3 l.1213-1214 conflicts with §2 l.122-127 (short caps, renewed regularly). A1 l.1147-1148 says "certifies at most 15 roots".
- Scenario: two roots with 4-week caps are renewed monthly. A Kome.Roster that counts certificates refuses the 16th renewal. The caps lapse, writes clamp, and expiry stops (A3).
- Fix: "at most 15 distinct certified signer keys (Signers_Max − 1, A1). Renewals for a certified key are unlimited and take no slot." Add a test that a renewal uses no slot.
- Obligation: none.

#### G21. Emit's guarantee is about To_Header(Tgt, Stamp), and nothing ties Tgt to the built record (F143)
- What: Target fields are free caller values (kome-emit.ads:124-154). Lemma_OK_Undominated is at :365-386. Make_Put computes FH itself (kome-records.ads:340-356).
- Scenario: a binding hashes a normalized field name into Tgt.FH. Choose looks at an empty phantom cell and returns OK with T = 900. The real cell holds t = 1 000, so the PUT is born dominated.
- Fix: constructors Put_Target(NS, Ent, Field) and Del_Target(NS, Ent) as expression functions that compute FH = To_Key256(Blake2b_256(Field)). Require them.
- Obligation: To_Header(Make_Put(...)) = To_Header(Put_Target(...), Stamp(...)).

#### G22. Put_Frame's Off is unspecified when nothing is appended (F144)
- What: kome-store.ads:43 says that Off names the appended entry. The Post constrains Off only on append (:651-702). The body sets Off := S.LL (kome-store.adb:2181, :2233, :2288). The Pre of Read_Frame (Has_Frame) then fails.
- Fix: add the unconditional Post "Off = Log_Length (S'Old)". Every branch already sets it.
- Obligation: one Post conjunct.

#### G23. §10.10(b) describes a case that Compact never creates (F149)
- What: Compact omits EXPIRE only when the old log is exactly the HEADER plus held APPLYs. Every other entry is at least 7 bytes (kome-store.ads:92-98, Post l.774-781). That is the full-log dead state of H3.
- Fix: reword §10.10(b) and kome-store.ads:96-98 to state this lemma, and name the full-log state.
- Obligation: the stated lemma.

#### G24. The planned "largest certified cap" view cannot be a function of F (F89)
- What: IMPLEMENTATION_PLAN.md l.107-108 plans the view. Certificates live in signer blocks of records that domination removes (DESIGN.md:122-129, l.172-175).
- Scenario: R is certified with cap 2^40 and later with a short cap C. r2 dominates r1, so the view reports C. The thief holds the 2^40 certificate.
- Fix: define the view in Kome.Roster as a ceremony log on the founding device that records every Make_Cert. Do not add a CERT record kind.
- Obligation: none in the lattice.

#### G25. The frontier and the index use linear scans (F122)
- What: kome-frontier.adb:1085-1125, kome-store.adb:1624-1628 and kome-emit.adb:91-94 scan linearly. Apply and write are O(|F|), and replay is O(entries × |F|).
- Scenario: N = 10^6 records and L = 7·10^6 entries give about 10^13 Dominates calls at open.
- Fix: sort Data_H entity-major (ns, ent, kind, fh). One binary search finds a PUT's cell and its entity's DEL. Inside the run, the work is O(fields of the entity).
- Obligation: every dominator of R lies in R's entity run.

## 3. Assumptions that can be removed

#### A1. [high] Any current member relays records of revoked or void writers, so A7 cannot be a deployment duty (F7)
- Today: DESIGN.md:412, l.424-431, §6 l.504-508, l.638-646 and A7 (l.1167-1174) assume that a revoked key's records never reach a replica that holds the REVOKE. W never shrinks. A compromised read-only member relays K_i records at t = maxceil, and every replica admits them.
- Replace with: (1) Restate A7 as "no replica receives, from any source, a record signed by a revoked subject after the revocation". Add an H8 row "compromised current member". (2) Suspect-relay attribution: when a record arrives whose author is already void in the receiver's view, the transport records the delivering peer's dh_pk and flags it. Admission does not change. (3) A per-writer write cap: admit data only if t ≤ wcap(author) := the maximum, over held GRANTs of that subject, of ∞ (issuer root_pk) or the issuer's cert_cap. GRANT domination becomes the product order on (h, cap), so wcap never shrinks.
- Changes: T4′ restated with wcap. The GRANT clause in Lean dominates and in Headers.Dominates. A7 text. A wcap derived from roster ceilings breaks T4′ (refuted item 59). The GRANT-based maximum does not.

#### A2. [high] ROSTER_eff is ordered by (gen, h), so a concurrent or stale roster undoes a removal (F46)
- Today: DESIGN.md:249-250 and kome-views.ads:134-150 (Roster_Lt). The roster header has no epoch (kome-headers.ads:38-46). R2 adds Y at (gen g, epoch e, still lists X) and beats R1's removal at (gen g, epoch e+1) on h. A stale certified root issues gen g0 + 1 at an old-segment epoch after a segment opener.
- Replace with: put Epoch in Kome.Headers.Header. Order ROSTER_eff by (epoch, gen, h, signer, ceiling_t, del_ttl). Add epoch′ ≥ epoch to the roster domination clause. Honest-issuer rule: epoch ≥ the largest held non-root-voided epoch.
- Changes: T2, T2′ and T3 for the extended product order. rosterEff_F for the new order. IA-12 goes away. The same-epoch residual stays (H9).

#### A3. [medium] The gate ignores REVOKE (F9, F47)
- Today: the gate is "Noise static key is the dh_pk of a ROSTER_eff member" (DESIGN.md:597-601). H8 l.412 and l.641-643 need the removal roster to arrive and to win. Roster_Lists_DH checks dh_pk only (kome-records.ads:1438-1446). The cold founding key revokes X, the removal roster comes days later, and meanwhile X passes the gate and its records are relayed.
- Replace with: a SPARK view Gate(F, k). Admit k iff k is the dh_pk of a ROSTER_eff member whose sign_pk has no REVOKE in F from a non-root-voided issuer, whatever its from_t. Apply the same rule to the credential's member entry and to the box rule. Combine it with A2 so that the bundle path is closed too.
- Changes: a new Views function. It reads REVOKE, so it is not monotone in F. That is acceptable for a transport decision, and T3 and T4 do not change. Lemma: a held REVOKE(X) from a non-root-voided issuer makes Gate refuse X's dh_pk.

#### A4. [medium] The founding root-void can be refused AUTH_FULL (F45)
- Today: E1 (DESIGN.md:52) assumes that the founding slice never fills. REVOKEs are never dominated, and Slice_Max = 512 (kome.ads:85-94; kome-frontier.ads:242-256). About 250 key rotations (REVOKE + GRANT) fill it, and then REVOKE(R, 0) gets Auth_Full.
- Replace with: an issuer-side reserve in §10.3 and Kome.Roster. The founding key signs an authorization record other than a root-void only if Slot_Count(1) + 1 ≤ Slice − (15 − roots_already_voided). Recommend that the founding key does no routine GRANTs or REVOKEs. With the reserve in place, the order of H32 is safe. Fallback: a REVOKE scope byte with a dedicated 15-entry row.
- Changes: E1 and §7 l.745 become "lands while the founding key keeps the 15-entry reserve". A1 names the lifetime budget. No Lean or Frontier change for the reserve.

#### A5. [medium] A DEL from a slow or clockless writer expires on arrival and is never relayed (F50, F18)
- Today: t_emit = max(now, floor.t + 1) (DESIGN.md:365). l.393 says that a no-RTC device works. kome-emit.ads:81 uses Now = 0. A clocked replica applies and expires such a DEL and holds nothing, so a peer that syncs only with it re-seeds the fields. F18 (hole, low): with a replica that never expires, the three-replica cycle churns APPLY and APPLY_EXPIRED forever (DESIGN.md:803-806; kome-store.ads:79-89).
- Replace with: a lower bound for DELs only: t_emit := min(max(now_ms, floor.t + 1, maxceil(F) − Cap_Lead), maxceil(F)). Cap_Lead is the issuer lead bound of H14. Each DEL then lives at least del_ttl − Cap_Lead everywhere. The bound maxceil − del_ttl_eff + 1 only stops expiry on arrival, which is not enough.
- Changes: an Emit Post (an emitted DEL has t ≥ maxceil − Cap_Lead). A4′ and T11(c) are stated as "not expired at R for at least del_ttl_eff − Cap_Lead after arrival".

#### A6. [medium] Caller randomness for eph_sk and segment tops (F104, F118)
- Today: the caller draws eph_sk and wipes it (DESIGN.md:565-569, l.594-595; kome-epochs.ads:376-407; IMPLEMENTATION_PLAN.md l.106). A weak RNG (VM snapshot, early boot, WASM shim) reveals eph_sk, and a removed member opens k_{e+1}.
- Replace with: eph_sk = BLAKE2b-256("kome/eph" ‖ k_e ‖ ns ‖ u16(e) ‖ signer ‖ u48(gen)), computed inside Kome.Epochs. Box_Key takes the epoch key, and Make_Roster uses Box_PK_Of, which also closes G7. Hedge the segment tops with Kome.Crypto.Hedge(SK, label, ctx, rnd) = BLAKE2b keyed by Seed_Of(SK).
- Changes: drop D5's "forward secrecy when wiped" and the l.106 duty. The T14 premise for kome/eph and kome/nonce becomes a random oracle. Do not combine this with A7, because A7 needs fresh entropy in eph_sk.

#### A7. [medium] The epoch hash chain, segments, links and tops are unused (F121)
- Today: bundles open only under ROSTER_eff's key (DESIGN.md:614-619, §8 l.1045), so k_e for older epochs is never needed. The chain causes H6, H9, G9, G10, G11, A15 and G5.
- Replace with: a key id per key, key_id = BLAKE2b("kome/kid" ‖ ns ‖ box_pk of the drawing roster)[0:8], carried in each roster in place of the epoch. Draw a fresh key only when a roster removes a member or the founding key root-voids a root. Otherwise, box the current key again. Bundles name key_id. Do not key by roster h, because every refresh would then change the key.
- Changes: removes the chain, links[], Links_Max, top_s, out-of-band tops, the founding-only segment rule and the A1 epoch bound. T14 becomes box secrecy plus a PRF. Residual: a root that is not in the current key's roster must draw a new key.

#### A8. [low] D14 "items apply in key order" (F20)
- Today: D14 (l.50), §4 l.318-324, §8 l.1049-1051 and kome-reconcile.ads:55-58.
- Replace with: "within a batch, apply every record with kind < 3 before any record with kind ≥ 3". In sessions, the phase gate already meets this rule.
- Changes: drops the per-item order duty (IA-25). auth_first already covers it.

#### A9. [low] Bundle sizes and the clear epoch leak membership and removals (F34)
- Today: §8 l.1039-1052 has no padding and a clear u16(epoch). Frame sizes are in §2 l.96-102. H3 calls sizes "unavoidable".
- Replace with: bundle = ns ‖ nonce ‖ AEAD, with the epoch only in the AD, filled in from ROSTER_eff.epoch. Pad the plaintext deterministically to fixed buckets.
- Changes: the §8 format and the H3 list.

#### A10. [low] seq_self lives outside the log, and the write path goes through Frontier.Apply (F40, F58, F110)
- Today: "Sign and apply. Persist seq_self" (DESIGN.md:379; kome-emit.ads:25 names Frontier.Apply). D9 and §7 l.674 say Kome persists nothing else. A crash causes a false CLONE_SUSPECTED, which spends root slices through rotations, or silent seq reuse. A torn seq_self file gives SEQ_EXHAUSTED.
- Replace with: persist seq_self := seq_emit durably right after Choose. Then append APPLY through Store.Put_Frame. Send a frame only after its APPLY is durable. On open, use max(stored, Max_Own_Seq). Report "seq store corrupt" apart from SEQ_EXHAUSTED. Add one SPARK Kome.Write (Choose, Make, Sign, Put_Frame). Do not refuse large seq jumps, because own records leave F when they are dominated.
- Changes: A5 restated. Kome.Write Post = T8 + Valid.

#### A11. [low] Slice is a per-open parameter, and capacities only ratchet (F44)
- Today: DESIGN.md:750-752 requires the same slice at every replica. kome-store.ads:120-132 rewrites HEADER bytes on a larger open.
- Replace with: slice = Slice_Max, a constant. Keep the HEADER slice field only as a check. Record data_cap outside the log, or append a CAPS entry. Allow a reopen at a smaller data_cap when replay fits.
- Changes: removes the slice-equality premise from T4's scope and the in-place rewrite (§10.10(a)).

#### A12. [low] The snapshot and item keys are built by the caller (F54)
- Today: kome-reconcile.ads:55-58, :69-75 and :435-514. Nothing connects the snapshot to F.
- Replace with: Snapshot_Of(S, F) in SPARK, with keys = {Key_Of(H) | H held} in order and frames from Read_Frame. Keep the 81-byte item key on the wire.
- Changes: lemma Range_Fp(Snapshot_Of(S, F), 1, n) = Frontier_Digest(F). Removes IA-16.

#### A13. [low] The gate and the credential check are caller duties (F55)
- Today: kome-reconcile.ads:44-54. Admit has no gate Pre (:1453-1463). A binding that calls Admit early sends a stranger HELLO with the full roster.
- Replace with: Start takes Peer_DH. Receive(HELLO) aborts unless Is_Roster_Frame(cred) and Roster_Lists_DH(cred, Peer_DH). Admit has Pre Gate(F, Peer_DH) (A3).
- Changes: the Admit and Receive contracts. Reduces IA-25.

#### A14. [low] Pre-gate OPEN gives strangers root_pk, salt and the revoked roots (F56)
- Today: DESIGN.md:896, l.903-916 and l.948.
- Replace with: the responder waits for the initiator's OPEN and answers only when ns matches. Send root-void frames only to a peer whose static key is a member dh_pk in some held roster, and n_rv = 0 otherwise. D13 release still works.
- Changes: the §8 OPEN rule and Reconcile.Start.

#### A15. [low] Out-of-band segment tops fail silently (F57)
- Today: E3 and §6 l.537-551. Box_OK checks only the nonce (kome-epochs.ads:358-437).
- Replace with: a Kome.Roster ceremony self-check. Before a root's first roster in a segment, it derives k_s from its top and opens the founding opener's link {from_epoch = s} with Open_Link.
- Changes: a phase-8 duty. No format change.

#### A16. [low] Bundles need a later session to re-offer discarded data, and A4′ counts a DEL that the receiver discarded (F59, F97)
- Today: DESIGN.md:313-324 ("offers it again on the next reconciliation"). A4′ (l.1161) counts arrival, not admission.
- Scenario: a DEL with t in (c1, c2] reaches B, whose maxceil is c1. B discards it, nobody offers it again, and B keeps the fields after the others expire d.
- Replace with: a sender rule. Each bundle is closed under admission. It carries each author's GRANT and the sender's maximum-ceiling roster ahead of the data, or an auth-only bundle goes first. Restate A4′: every DEL is admitted at every member within del_ttl_eff. Do not add a pending side table (§7 Bounds).
- Changes: lemma auth_first_closed, a corollary of auth_first. The A4′ text.

#### A17. [low] No check gates a merge (F82)
- Today: ci.yml l.6-9 runs on schedule and dispatch only. master has no rules. CONTRIBUTING.md l.3-5 and README l.108-109 say that CI rejects.
- Replace with: a pull_request job that runs ./lean/build.sh and PROVE=0 ./spark/check.sh all, and a ruleset that requires signoff and these jobs.
- Changes: CI only.

#### A18. [low] "No sorry" and "only standard axioms" are not enforced (F83)
- Today: lean/build.sh l.8-12 runs a plain lake build. The claims are in README l.15, lean/README l.48-50 and §10.1 l.1184-1185.
- Replace with: lake build --wfail. Add a Lean check file that requires only propext, Classical.choice and Quot.sound for the named theorems. Make check.sh grep for pragma Assume and Annotate.
- Changes: the build scripts.

#### A19. [low] Typed fields assume inflationary author states (F88)
- Today: §4 l.340-356 replaces an author's full state by version. A backup restore turns GSET {a, b} into {a, c}, and b is lost.
- Replace with: q kills p only when q.v > p.v and state(q) ⊒ state(p). Count the per-(cell, author) antichain against data capacity. Honest authors emit the join of their own records next. Specify the DEL semantics for typed cells.
- Changes: per-author inflation becomes an obligation in T15-T17, with the antichain as the checked fallback.

#### A20. [low] "REVOKE is never dominated" costs lifetime slice space (F90)
- Today: DESIGN.md:176 and kome-headers.ads:83. Reissued revocations stay forever.
- Replace with: an issuer rule. Emit REVOKE(s) only if F holds no REVOKE of s by that issuer with from_t ≤ the new from_t. The lattice alternative is a domination clause per (issuer, subject) on lower from_t.
- Changes: a Kome.Roster rule. With the lattice clause, re-prove revokeVoids_F and rootVoid_F.

#### A21. [low] A log cut at an entry boundary opens silently (F108)
- Today: Open_From_Log returns OK for any well-formed prefix (kome-store.ads:836-851). A crash can drop an applied REVOKE.
- Replace with: a durability duty. The binding makes the log durable up to Log_Length before the transport sends Complete, relays an applied record, or continues after applying an authorization record. No hash chain.
- Changes: IMPLEMENTATION_PLAN duties. No theorem change, because a truncated replica is equivalent to a stale one.

#### A22. [low] Concurrent additions by two roots shut out the h-loser's newcomer (F112)
- Today: "h resolves the race" (DESIGN.md:444-447). Two newcomers never send HELLO to each other (§8 l.931-939).
- Replace with: a view rivals(F) := non-root-voided rosters with gen = ROSTER_eff.gen and another signer, reported as "membership contested". A root that sees rivals issues gen + 1 with the union of members when every rival is at ROSTER_eff.epoch.
- Changes: a new T5 view. Removes IA-11.

#### A23. [low] T4(c) needs a frozen, serialized session (F116)
- Today: T4(c) (l.1075-1077). The snapshot is frozen (kome-reconcile.ads:182-186), while other sessions, writes and bundles change F.
- Replace with: after a complete session with no capacity refusal and no expiry crossing, F_A ⊒ F(snap_A ∪ snap_B), and the same for B.
- Changes: the T4(c) statement. It follows from T3 and T4(a). IA-17 then matters only for C ABI threading.

#### A24. [low] Each session copies all frames into a pool of up to 1 GiB (F117)
- Today: Pool_Max = 2^30 (kome-reconcile.ads:439, :1674-1686).
- Replace with: the snapshot holds (key, offset, length) plus a store generation counter. Frame(S, I) is a Store accessor with Pre Generation = Snap.Gen. Compact waits while a snapshot is live.
- Changes: the Snapshot type and contracts (with A12).

#### A25. [low] Verify's strictness Post is assumed because its body is SPARK_Mode Off (F119)
- Today: kome-crypto.ads:452-459 and kome-crypto.adb:210-215.
- Replace with: a private Raw_Ed25519_Check with no Post, completed in the Off body. Verify becomes a SPARK expression: S_Below_L and Is_Canonical_Point(R) and Is_Canonical_Point(PK) and Raw_Ed25519_Check.
- Changes: the assumed surface shrinks to the C group equation (IA-28).

#### A26. [low] Data records bind only the 128-bit ns (F120, F124)
- Today: ns = BLAKE2b(root_pk ‖ salt)[0:16] (DESIGN.md:64-66), and h = BLAKE2b(tag ‖ content) (l.77-79). About 2^64 work gives two collections that exchange records (§7 l.702-706).
- Replace with: cid = BLAKE2b-256(root_pk ‖ salt), computed once at Open, and h = BLAKE2b-256(tag ‖ cid ‖ content) as implicit context.
- Changes: Records.Well_Formed and Decode take the collection context. Vectors change. §10.9 interop needs (root_pk, salt).

#### A27. [low] An all-zero eph_sk or seed gives a publicly known key (F147)
- Today: Box_Key has no Pre on Eph_Secret (kome-epochs.ads:386-412). DH_Keys_OK checks only for reduced and low-order keys.
- Replace with: Pre "not all-zero" on Box_Key.Eph_Secret, the Key_Pair seed and the top input. Refuse X25519_Public(0^32) as box_pk and Derive_Public(0^32) as a GRANT subject, signer or root_pk.
- Changes: two byte comparisons in Well_Formed. A6 makes the eph_sk part moot.

#### A28. [low] Compact's In_Old_Order is used by nothing (F150)
- Today: kome-store.ads:599-610 and :763-767, in the slowest Post.
- Replace with: drop it from the Post and Lemma_Compact_Post. DESIGN §7 l.681 says "authorization records first, then data".
- Changes: a weaker Post. T18 is unchanged.

#### A29. [low] dh_sk serves as both the Noise static key and the box key (F155)
- Today: DESIGN.md:565-579, l.599-600 and l.1035-1036.
- Replace with: state that dh_sk is the member's whole capability. The T14 premise becomes Gap-CDH, or CDH in the ROM with separate oracles. Phase 9 refuses low-order Noise keys and uses constant-time X25519. The full fix is a second X25519 key per member (+32 B).
- Changes: the T14 premise.

#### A30. [low] Record signatures carry no Kome label (F156)
- Today: sig over a bare 32-byte h (DESIGN.md:77-79). One device key serves all collections.
- Replace with: a generate-only key API (Key_Pair from Kome's own seed, never imported or exported), stated as a duty in §10.3 and §10.6. For imported keys, Ed25519ph (crypto_ed25519_ph_sign). A label inside h does not help.
- Changes: §2 signature rule and vectors (Ed25519ph only).

## 4. Assumptions that must stay

#### N1. [medium] The horizon is per replica, so "same records ⇒ same state" fails (F51)
- Why: the horizon reads the local clock (DESIGN.md:764). No shared clock exists. A device with no RTC never frees DELs.
- Containment: restate H1 and T4(b) as "same applied set and same horizon ⇒ same F". Qualify §9 l.1176. Lean lemma: h1 ≤ h2 ⇒ expire h2 (expire h1 S) = expire h2 S. A no-RTC device calls Expire(Now := maxceil(F)).

#### N2. [low] A7 is irreducible, but its stated damage is wrong (F151)
- Why: bounded state cannot filter a revoked key's records at a replica that lacks the REVOKE.
- Containment: in l.412, l.423, l.516-517 and A7, say that the bytes leave F at every replica and that Kome keeps no copy. Optional: at a replica that holds the REVOKE, quarantine the honest records that a void record removes, in an advisory view outside T5.

#### N3. [low] No receiver-side rule can bound the founding key's ceiling (F60)
- Why: a relative-climb rule breaks late joiners. A new device with maxceil = 0 discards the only surviving roster forever.
- Containment: an issuer rule: ceiling_t and cert_cap ≤ now + Ceiling_Lead_Max, and nothing within 2^47 of 2^48 − 1. A view ceiling_lead = maxceil − now_local, with a status when it passes a bound.

#### N4. [low] A3 also gates tombstone expiry (F113)
- Why: after wall time passes maxceil, every DEL gets t = maxceil, above the frozen horizon.
- Containment: say so in A3 (l.1159) and §6 l.526. Ceiling_Stale = Now > Ceil(Regs(F)) is computable today. The C ABI shows it and Horizon_Frozen.

#### N5. [low] Losing the founding device also freezes epoch advance (F36)
- Why: only the founding key opens a segment (DESIGN.md:546-548).
- Containment: add the limit to the loss paragraph (l.522-528) and A1. Keep a cold backup of the founding key.

#### N6. [low] Member enrollment is out of band (F32)
- Why: Kome cannot authenticate (sign_pk, dh_pk) without a human channel. A substituted dh_pk gets read and gate access.
- Containment: specify in §10.3 a SAS or QR check over BLAKE2b-256("kome/member" ‖ ns ‖ sign_pk ‖ dh_pk), and a dh key rotation step in the Kome.Roster duties.

#### N7. [low] At most 64 devices pass the gate per collection (F146)
- Why: the gate is membership of one roster (Members_Max = 64, kome.ads:83).
- Containment: state the bound in §6 and §10. In §7 l.836, say that |W| ≤ 8 192 bounds storage, not syncing devices. Issuer rule: a roster at epoch e is a superset of ROSTER_eff's members at e, and a 65th member is refused.

Other inventory items that stay, with their containment: A1-unforgeable (strict verification, H13, G16); A2-hash and A2-ksum (G6); A1-founding-never-stolen (cold backup, re-founding, refuted items 24 and 33); A4′ (restated by H4, H14, A16, H35); in-order transport (G4); Noise binding (A13); Crypto Posts assumed (A25); collection identity out of band (A26); short caps (N3, G20); founding key kept cold. These inventory items are removed by section 3: A5-persist-order (A10), E1-founding-slice (A4), IA-03 (H14), IA-05 (H16), IA-11 (A22), IA-12 (A2), IA-13 (G16, E8), IA-14 (H13), IA-16 (A12), IA-17 (A23), IA-20 (A16, H17), IA-22 (A21), IA-23 (H18), IA-27 (A6), IA-33 (H24).

## 5. Legacy residue

- E1 (F24, F61, F78). kome-frontier.ads:2, :52, :270, kome-frontier.adb:428 and kome-store.ads:477-478 cite applyA, keep and State. These names come from this redesign's earlier Frontier.lean (9504e73), which 0fae9d9 and c07686c replaced. Edit: Apply refines applyD (OK = the adm branch; Inadmissible = applyD_neg). Apply_Expired refines expire h (applyD S d). spark/CONVENTIONS.md:22-25 says that the model holds inadmissible records, but Frontier.lean:34 discards them. Replace l.23-25 with a pointer to DESIGN §10.1 as the only divergence register. List there: no certificates, no ns, no capacity, no clock clamp, Nat for u48, no journal, and expire-on-arrival (G1).
- E2 (F68, F131). Delete the b2eddsa_old and b2eddsa_old_pk vectors (spark/vectors/crypto.txt l.55-67, l.94-95, l.172-183), and B2_Pub, B2_Sig, Do_Old and Do_Old_Pk with their checks (spark/tests/test_crypto.adb l.8-9, l.162-179, l.230-236, l.494-512, l.545-560, l.735-738). Rewrite kome-crypto.ads l.22 (drop "DECIDED") and l.31-33, and third_party/monocypher/README l.47-55, in present tense. Update the Crypto counts (README l.16, l.78, l.90; IMPLEMENTATION_PLAN l.25).
- E3 (F69). .gitignore l.12-13: delete the comment and build/. If it is needed again, add it anchored as /build/.
- E4 (F70). spark/kome_spark.gpr Prove package uses --level=2, and check.sh l.73-75 uses --level=3. Make the gpr the single source, with Proof_Switches ("--level=3", "--mode=all", "-j0"). Keep -j0, which CI uses. Remove the level and mode from check.sh:75.
- E5 (F71). Delete PROOF_WIP from spark/check.sh l.46-49 and l.78-87, and fail on any unproved check. Delete README l.59-63.
- E6 (F72). REQUIREMENTS.md: delete §4 l.74-84 (scoring C1-C9). The l.1 title becomes "the problem and the constraints". Move l.86-88 into §2 as one sentence.
- E7 (F73). DESIGN.md: rewrite l.3 ("Decision.") as a plain statement. l.13-14 says "every change". Replace §10.2 l.1194-1196 (unpinned nix shell) with a pointer to lean/build.sh, spark/check.sh and nixpkgs.pin. Delete §10.7 l.1235-1237 and l.1257-1261.
- E8 (F74). "Decode clamps del_ttl" in D10 l.46, E5 l.56, §7 l.789-790 and kome.ads l.95-98 becomes "decode refuses (MALFORMED) a ROSTER whose del_ttl is outside [Del_TTL_Min, Del_TTL_Max] (§2 rule 3)". In kome-records.ads l.984 and l.1031, "in the clamp" becomes "in range".
- E9 (F75). IMPLEMENTATION_PLAN.md l.30: remove "C8 sketch" from phase 7 (kome-reconcile.ads l.117-119: not built). Add an unbuilt-duty item: "Round 0 (C8 IBLT) is not built and no phase owns it".
- E10 (F77). "Extension F" in IMPLEMENTATION_PLAN.md l.33, README.md l.102 and DESIGN.md l.1142 becomes "typed fields (C10)".
- E11 (F79, F130). spark/tests/test_records.adb:339-341 is byte-identical to :336-338 (Tag_Del = 3). Change l.339 to Tag_Put + 1 (the count stays 172), or delete it and update the counts. Rename test_records.adb:561, test_store.adb:1113, test_reconcile.adb:1120 and test_epochs.adb:686, and fix spark/vectors/epochs.txt:26, so that each name describes the property.
- E12 (F80). kome_spark.gpr: add -ffunction-sections -fdata-sections and a Linker package with -Wl,--gc-sections. Keep the monocypher files byte-identical (SHA-256 pins). Add a check.sh nm step that fails if crypto_argon2 or crypto_eddsa_* is linked. List the bound symbols in the monocypher README.
- E13 (F81). REQUIREMENTS.md §5 l.92-94 and README.md l.90: "X25519, RFC 8032 Ed25519 (SHA-512 only inside the signature), BLAKE2b, XChaCha20-Poly1305 (24-byte nonce)".
- E14 (F84). Keep per-package counts only in IMPLEMENTATION_PLAN Phases. Remove the count columns from README l.82-98, and point l.16 and l.77-79 to the plan. README l.103-104 becomes "the order of IMPLEMENTATION_PLAN.md Phases".
- E15 (F103). REVOKE.rev_seq has no reader. Drop it (frame 269 B): DESIGN §2 offsets and l.88, §3 l.189, T13 l.1129, kome-records, kome-headers.ads l.18, vectors/records.txt, kome-emit.ads l.181-182, and the Frontier.lean revoke constructor (l.128-134). Or give it the meaning of A20.
- E16 (F126). DESIGN.md C5 l.25 ("self-tombstone rule") and §7 l.836-837 ("pending buffers"): replace the undefined terms with positive statements. Keep C9's per-field clause, D5's "no root X25519 key" and "no vectors", because each has a reason.
- E17 (F127). spark/CONVENTIONS.md:105-106: replace "so flow analysis can prove open never writes" with: "code that touches a file or a clock declares it in Global/Depends; Open_From_Log is Global => null; the only non-append write is the §10.10(a) HEADER rewrite, owned by the binding".
- E18 (F128). kome_spark.gpr l.1: "Kome SPARK implementation". l.17-18: drop -fPIC until a phase-9 library project exists. kome.ads l.3-6: use the CONVENTIONS.md:29 wording.
- E19 (F129). spark/check.sh l.5 documents tests/test_*.adb, but l.96 loops over src/kome-*.adb, and l.53-59 is a dead branch. Build the module list once as the union of the two sets (check.sh --list, also used by ci.yml:38), and fail when a module is on one side only.
- E20 (F132). README.md l.71 and l.15 and kome.ads l.3: name the eight packages that refine Frontier.lean (Versions, Headers, Registers, Frontier, Records, Store, Emit, Views). The others implement encodings, cryptography and protocols.
- E21 (F157). DESIGN.md §9 l.1159-1174: rename A4′ to A4 at l.778, 811, 814, 818, 1120 and 1161, and in spark/tests/test_store.adb:768. Keep A7, and add "assumption IDs are fixed". Move the unnamed register-values bullet into the D13 rationale. Rewrite §7 l.811-822 as a positive statement.
- E22 (F158). IMPLEMENTATION_PLAN.md l.9: "Its contracts name the Lean theorem that they refine, where one exists; the Lean column records the status otherwise (—, paper, open)."
- E23 (F159). Phase 0 marks root package Kome done, but no check runs on it. In check.sh, map module kome to kome.ads, fail when the unit is missing, and add it to the CI list. Or state in the plan that Kome is proved only as context.
- E24 (F160). kome.ads l.13-18 says U64 is "the only modular type", but Byte (l.10) is modular. Reword: "Byte and U64 are the only modular types. Byte is the wire unit; U64 is for accumulator limbs and C storage in Kome.Crypto." Align CONVENTIONS l.65-67.

## 6. Not covered

- Packages read and found clean: Kome.Byteorder, Kome.Versions and Kome.Keys (big-endian order matches §2, so IA-15 holds). Kome.Registers is correct. Its only cost is a linear In_W scan over 8 192 keys and a 256 KiB Register_File that is copied by value (kome.ads:94).
- wipe-compiler: no verdict. It holds only in part. kome-epochs.adb Step wipes Buf and Digest but returns the derived key in an unwiped local R. The Derive loop variable is not wiped. Wipe relies on GNAT passing by reference (RM 6.2(11)).
- record-identity-excludes-sig: harmless under A1. It affects only relay dedup.
- w-full-unreachable: holds (Writers_Max = Signers_Max × Slice_Max, kome.ads:94).
- Not examined: gnata-ignored-regions (nobody checked that each Ignore region is proved), lean-hinj, d15-call-bound, and IA-17 (single-threaded store access from the embedding application).
- C8 round 0 exists as prose only. It has no wire tag, no fetch-by-hash message and no pending-weight rule. This audit did not review it.
- Re-founding and collection retirement are the stated remedy at DESIGN.md l.519-520, 562-563, 748-749 and in A1, but no section specifies them.
- Bundle-path duties: neither the plan's transport duties nor kome-reconcile.ads:55-58 list an ns = Collection check for ELEMENTS/HAVE items or bundle-imported frames.
- Re-shipping of AUTH_FULL surplus in every session: the bandwidth bound is not stated.
- Interactions between hardenings were examined only as refuted items 59-66. Conflicts noted in this report: A7 conflicts with A6 (fresh entropy in eph_sk). H6 and G10 each fix the top_s rule, so choose one. H32's issue order needs A4's reserve.

## 7. Refuted findings

1. Element-key order applies a DEL before the PUTs it dominates: no defined source yields such a batch. ELEMENTS come from one frozen snapshot of an antichain, and bundles are ELEMENTS lists. Only wording is missing.
2. A pre-admission HELLO credential lets a stolen or voided root capture a joiner: the design already names and accepts this window (§6 l.493-499, l.607-612, A1).
3. Apply-then-expire depends on arrival order: each order needs p to arrive after d expired. That is the A4′ violation that §7 documents. The statement gap is G1.
4. T5 uniqueness "without A2" holds only for headers: h hashes the whole content, so the case needs a BLAKE2b collision (A2).
5. Snapshot.Append does not preserve earlier frames: it needs a future maintainer bug and no adversary capability. A key/frame mismatch from a peer is already handled.
6. T13 and T10 are marked proved without a theorem: the check mark means "core Lean can prove". T10 follows from T1 (StrictTotal Version) and convergence.
7. Read revocation is gate-only: the leak to a stale replica is a lower bound for every key-based scheme, so the fix adds nothing.
8. D6 omits the "kome/nonce" label: §1 rows are summaries that point to §6, and the row leaves out other labels too.
9. Replay refuses a log over an unproved invariant: unreachable under the §7 l.781 logging rule. Replay completeness is already declared as tested, not proved (kome-store.ads:150-154).
10. Expire refuses removal when 7 log bytes are missing: the argument fails at its key step, and the wedge is overstated (the full-log state is H3 and G23).
11. Put_Frame trusts caller H and Verified: these are proof obligations on every SPARK caller. The C ABI's run-time check is duty IA-24.
12. A7 needs a membership lease: this is already the design's position (E7 l.58, §6 l.627-634).
13. Small-order keys give universal forgery for that key: the algebra holds but gives nothing beyond what the design handles. The reachable path is H13 (Zero_Key GRANT).
14. The byte order of author and h is unspecified: §8 l.866-867 and §2 l.79 make them big-endian, and the SPARK code and tests match.
15. Sessions need an in-order lossless stream: an aborted session keeps what it applied, and later sessions converge.
16. Per-replica data capacity makes T4 conditional: already stated in T4's scope and exposed to the caller.
17. GRANT never expires, so A7 failures are unbounded: already documented, and the claimed damage and gain fail. A1 covers the real residual.
18. Root-voiding is all-or-nothing and fills the founding slice: a fresh certified root takes the re-issues in its own slice.
19. Synthetic nonces are a hand-made SIV: no attacker in the threat model can use this. Each sub-claim fails against §6 and §8.
20. IBLT poisoning by unsalted hashes: peeling runs on T_A − T_B, so an element both sides hold cancels.
21. A SHADOWED DEL is misreported: the statuses match §5 l.386-388.
22. "Kome ignores from_t" holds only for root_void: the design covers the root's own data records (l.244-247).
23. A lapsed cert_cap does not retire a root: already stated (§2 l.122-129, §6 l.522-528).
24. The founding key has no rotation: this is the A1 violation that the design names (§6 l.519-520).
25. The wrap-key layer fails across overlapping segments: this contradicts the segment-opening rule (l.548-549), and the nonce layer covers the residual.
26. A hardware-token founding key signs blind: a token without a display is blind under any scheme.
27. Replay re-runs the current well-formedness predicate: this needs a hypothetical build. T18 covers stores that this build writes.
28. Re-founding cannot carry data: any member in the new W can re-PUT readable values under ns′.
29. Log offsets are not stable across Compact: a stale offset is a host bug, and no remote capability causes one.
30. Periodic Expire grows the log under a clock that is not monotone: a call lowers the horizon only when its Now is below the Now that set Hz.
31. Re-issued REVOKEs use up slices: the scenario does not hold. A20 covers the slice cost.
32. Choose never reports a void write: the check would run on the writer's own F, which lacks the REVOKE, so it never fires.
33. KERI-style pre-rotation of the founding key: admission would depend on F or on unbounded proofs, which breaks D1.
34. Re-founding is unspecified (as a defect): the facts are true but the scenario fails. It is listed in section 6.
35. Wipe on Byte_Array subtypes depends on by-reference passing: the RM and Wipe's Post cover out-mode arrays, and the eph_sk premises are wrong.
36. W cache Auth_Full case (c) is reachable: not under the definitions. The bound is a declared gap (IMPLEMENTATION_PLAN l.60-64).
37. Element identity excludes sig: identity is content (§2 l.71-79), and two frames of one h are one record.
38. cert_cap is no expiry: the design never presents the cap as an expiry (§2 l.122-126).
39. The founding key must be online more often than del_ttl_eff: the duty and its effect are stated (§2 l.122-127, A3).
40. REVOKE(key, 0) after a clone hides honest records: H8 does not tell the owner to revoke after a backup restore (l.410).
41. DESIGN defines Kome by negations of the C++ engine: each negation has a positive statement next to it.
42. Five null-body ghost lemmas are uncalled: no convention is broken (CONVENTIONS.md:38-41).
43. Provenance and toolchain claims rest on uncommitted files: check.sh:17-24 ties the toolchain to nixpkgs.pin, and committed checks catch the rest.
44. The §1 governing rule is neither sufficient nor necessary: the §3 table puts PUTs on the entity key too, so the counterexample fails.
45. A roster at epoch 65 535 blocks segment opening: this needs a stolen certified root, which can already do worse.
46. A roster and a large PUT do not fit in one bundle: the design re-offers discarded records, and a split delivery equals a dropped message.
47. D13 delivers recovery out of order: the transient is documented (§6 l.468-473, l.482) and clears itself. H32 keeps the stranger case.
48. No Verify(Sign(m)) contract: harm needs a caller that breaks Put_Frame's Pre, and no proved caller can.
49. Nothing says where the founding key keeps segment tops: the link needs k_{s−1}, which every current member holds.
50. Unbox_Key returns Zero_Key on refusal: no caller exists yet. Kome.Roster is not started.
51. Bundles carry no sender identity: each variant breaks a stated rule ("a member removal increases the epoch").
52. A4′ needs a ledger of expired DELs: the scenario reproduces only the documented residual.
53. Lean hinj makes h free: this is a declared model-scope gap, and two supporting claims are false.
54. Leaf ELEMENTS ship whole frames: C8 round 0 (§8 l.1019-1025) handles that case in the design.
55. The digest and D15 sums cannot be kept incrementally: hashing adds a constant factor, not a complexity class.
56. The root .gitignore repeats spark/ and lean/ entries: at 2be1260 it has 13 lines and no such entries.
57. The ns check is only a precondition: the one build uses -gnata, so the Pre runs at run time.
58. Re-founding is never specified (as a hole): it arises only after a named assumption violation, and the proposed fix breaks a proved theorem.
59. F7 v2 (writer ceiling from roster ceilings) breaks T4′: no such rule is in the tree. A1 uses a GRANT-based maximum.
60. The F1 bundle filter traps t = 0 writes: no t-based bundle filter exists in the tree.
61. The F104 derived eph_sk defeats the F26 salt and the F57 in-band top: no derived eph_sk exists in the tree.
62. F6/F14 reserve from_t = 0 for root voids: root_void depends on the issuer, not on from_t (l.244).
63. F37 with F44 forces an 83 MB minimum log: no reservation is in the tree.
64. F47 v3 bans dh_pk reuse: no such rule exists, and §2 does not require dh_pk uniqueness.
65. The F95 detector raises false alarms after a crash: F95 is not in the tree. Pair it with A10 (H18).
66. The F49/F60 lead bound piles rosters into the slice: worked by hand, weekly re-issues dominate and no pile-up occurs.
67. C8 has no wire tag or pending rule (as a bundle defect): C8 is not a bundle path. The area is listed in section 6.
