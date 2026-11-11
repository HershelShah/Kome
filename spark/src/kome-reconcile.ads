--  Kome.Reconcile: the reconciliation session for the frontier of one
--  collection (DESIGN.md §8, D12, D13, D14 and D15, with SIMPLIFY.md S9,
--  S11, S18, S19, S20 and S21). The session has the HELLO exchange and
--  two range reconciliations: first the authorization range, then the
--  data range.
--
--  Element keys (S18). The elements are the records of F. The key of an
--  element is 82 bytes, compared bytewise:
--
--    data           03 ‖ ent[16] ‖ sub:u8 ‖ fh[32] ‖ h[32]   (sub = 0 DEL, 1 PUT)
--    authorization  tag ‖ 0^17 ‖ signer[32] ‖ h[32]          (tag = 0, 1, 2)
--
--  with ROSTER = 0, REVOKE = 1, GRANT = 2. SIMPLIFY.md §2 writes the
--  authorization key as tag ‖ signer[32] ‖ 0^17 ‖ h[32], "as the
--  Reconcile agent lays out": this package puts the 17 zero bytes before
--  the signer, so that both layouts have the same fields at the same
--  places (Elem_Key below). The order of the authorization keys is the
--  same in the two layouts (the zero bytes are constant), so this is a
--  placement, not a different order. In the package, a key is Elem_Key, a
--  record of scalars and word records (CONVENTIONS.md rule 1): K (byte
--  0), Ent (bytes 1 .. 16), Sub (byte 17), FH (bytes 18 .. 49), H (bytes
--  50 .. 81). The bytewise order is Key_Lt, a quantifier-free chain of
--  word comparisons; Lemma_Key_Eq_Is_Bytewise and
--  Lemma_Key_Lt_First_Difference prove that it is exactly the
--  byte-lexicographic order on the wire key. Authorization records sort
--  first (tag 0, 1, 2 < 3). Data_Lo = 03 ‖ 0^81 divides the key space
--  into the authorization range [Min_Key, Data_Lo) and the data range
--  [Data_Lo, Max_Key). "Apply in element-key order" is the one ordering
--  rule of a batch: ROSTERs before REVOKEs before GRANTs before data
--  (S10, S18).
--
--  The key order and the frontier's row order. The data row of
--  Kome.Frontier is sorted entity-major by (ent, kind, fh), DEL before
--  PUT (AUDIT.md G25), which is exactly the order of the data keys. The
--  authorization rows are kept by slot (the order in which each signer
--  first reached this replica) and, in a slot, in arrival order, so
--  their order is local to a replica and is not the key order. Snapshot_Of
--  therefore inserts the authorization records (at most Signers_Max ×
--  Slice_Max = 8 192) into key order and then appends the data row; each
--  data insertion lands at the end in one comparison, because the data
--  row is already in key order (that is how it runs; the proof does not
--  rely on it, since Insert is correct at any position).
--
--  Messages (all integers big-endian):
--
--    HELLO     01 ‖ n_auth:u32 ‖ n_data:u32 ‖ digest[32] ‖ cred_len:u16 ‖ ceil_len:u16
--                 ‖ cred[cred_len] ‖ ceil[ceil_len]
--    RANGE     02 ‖ k:u8 (1 .. 16) ‖ bounds[k + 1] × key[82] ‖ k × (count:u48 ‖ fp[32])
--    ELEMENTS  03 ‖ lo[82] ‖ hi[82] ‖ n:u16 (<= 4) ‖ n × (flen:u16 ‖ frame)
--    HAVE      04 ‖ lo[82] ‖ hi[82] ‖ n:u16 (<= 4) ‖ n × (flen:u16 ‖ frame)
--    ROOT      05 ‖ count:u48 ‖ fp[32]
--
--  There is no OPEN (S11). The Noise XK prologue is "kome/1" ‖ ns ‖ proto
--  (Prologue below): it binds the collection and the protocol version, and
--  a stranger cannot finish XK without the responder's static key. The
--  HELLO carries the two counts, the digest, the credential roster and
--  the ceiling frame (below; AUDIT.md H12). A RANGE carries k sub-ranges
--  [b(j-1), b(j)) with their counts
--  and fingerprints: a 16-way split is one message (S19). An ELEMENTS or a
--  HAVE item is its frame only: the receiver derives the key from the
--  frame (the caller decodes the frame and passes its key, see Keys
--  below). ELEMENTS and HAVE keep their lo and hi (SIMPLIFY.md §2 lists
--  only their items; the bounds are what makes the reply groups tile).
--  A ROOT carries the count and fingerprint of a whole range; its bounds
--  are fixed by the phase: [Min_Key, Data_Lo) for the first ROOT,
--  [Data_Lo, Max_Key) for the second.
--
--  Each field has one width and the order of the parts is fixed, so a
--  message has one encoding. A range is half-open, [lo, hi), with lo < hi.
--  The messages say:
--    * RANGE part j / ROOT: "over my elements in [lo, hi), the count and
--      fingerprint are these";
--    * ELEMENTS: "these (n <= Ship_Threshold) are ALL my elements in
--      [lo, hi)";
--    * HAVE: "these are elements in [lo, hi) that you did not have". An
--      empty HAVE over the whole range is the explicit confirm.
--
--  Parts. Receive takes one logical message: a ROOT, an ELEMENTS, a HAVE,
--  or one part j of a RANGE (the caller calls Receive for j = 1 .. k on
--  the same input, in order). A RANGE part is exactly a single-range
--  message of the protocol before S19, so the responder, the budgets and
--  the obligations are stated per part, and a 16-way split counts as 16
--  messages in the budget (as 16 RANGE messages did).
--
--  Item keys. Decode reads the frame places of an ELEMENTS / HAVE
--  (Item_Places). The caller decodes and verifies each frame with
--  Kome.Records and passes the element key of its header,
--  Key_Of (To_Header (Cid, R)), in Keys (T); a frame that does not decode
--  is a protocol violation, and the caller ends the session. Receive
--  checks that the keys are strictly ascending and in [lo, hi) (else
--  Malformed), and delivers exactly the items whose key we do not hold.
--  The caller applies the delivered frames in item order, which is key
--  order. If the frame's author is already void in the caller's view
--  (Kome.Views.Is_Void before the apply), the caller reports
--  SUSPECT_RELAY for the peer's static key (DESIGN.md §8; AUDIT.md A1).
--
--  The snapshot (A12, S21). The HELLO is built from the two incremental
--  digest states of the store (Kome.Store.Digest_Auth / Digest_Data; Admit
--  takes them), not from a snapshot. The snapshot is built only when the
--  HELLO digests differ: the caller calls Snapshot_Of when the session
--  enters Auth (After_Hellos), Seals it, holds it for the session (it pins
--  the store while it does, S21), and passes it to every later Receive
--  and Next_Phase (Same_Snapshot, a precondition: its count and digest are
--  those of our HELLO). Snapshot_Of (F, T, S) reads the keys from the
--  headers of F and the frame lengths from the frame table T, which the
--  caller fills from Kome.Store.Read_Frame in the flat order of F (entry I
--  is the frame of Held (F, I)). The snapshot does not copy frames: each
--  element records its source index in F, and Encode copies the item
--  frames from T (Linked). This package does not depend on Kome.Store.
--  Snapshot_Of proves that each element is a held record of F (Source),
--  that the elements are in strictly ascending key order and are distinct
--  records, that |S| = |F|, and that the digest of S is
--  Kome.Digest.Frontier_Digest (F) (T6, Lemma_Sum_Perm). Its only refusals
--  are Snap_No_Space (|F| above the capacity) and Snap_Unsorted (two held
--  records with one key: equal h, excluded by A2).
--
--  Fingerprints with prefix sums (D15, AUDIT.md H19). Seal (S, P) builds
--  the prefix-sum table P once (Kome.Digest.Build_Prefix, O(n)); P is a
--  separate object of Prefix_Slots (|S|) accumulators. With the table,
--  Fingerprint_Of gives the fingerprint of any range with at most 64
--  accumulator additions and one hash (Kome.Digest.Range_Sum), and its
--  result is Range_Fp, the fingerprint that the contracts name. When this
--  side splits a window of at least 1 024 elements, the interior cuts are
--  on multiples of 64 (S20), so only the two ends of a range walk
--  elements.
--
--  The gate (S9, Kome.Guard). The caller decodes the record of ROSTER_eff
--  of F (Eff). Gate_Open (Cid, F, Eff, DH) holds when Eff is ROSTER_eff of
--  F and Kome.Guard.Admits (the REVOKE-aware gate and not quarantined).
--  Admit requires it, so a binding cannot admit a stranger (A13). Receive
--  (in Auth and Data) and Next_Phase evaluate it on every call, with F the
--  state after the caller applied the previous batch; when it fails, the
--  session ends with S_Aborted. There is no generation counter. Within a
--  batch the caller applies in key order, so ROSTERs before REVOKEs
--  (S10). While Kome.Views.Quarantined holds, the caller takes no sealed
--  bundle and seals none.
--
--  The HELLO (post-handshake, D13): Receive refuses the HELLO and aborts
--  the session (S_Aborted) unless the credential is a ROSTER frame
--  (Kome.Records.Is_Roster_Frame) that lists the Noise static key of the
--  peer (Kome.Records.Roster_Lists_DH, AUDIT.md A13) and whose signer is
--  not root-voided in F (Kome.Views.Root_Void, AUDIT.md G12). The
--  credential of an aborted HELLO is not returned, so it is never applied.
--  If Receive accepts the HELLO, the caller decodes, verifies and applies
--  the credential. This is how the recovery roster reaches a captured
--  (quarantined) replica (S11): the replica Starts, receives the HELLO,
--  applies its credential, and only then evaluates the gate for Admit.
--
--  The ceiling frame (AUDIT.md H12; DESIGN.md §8). The HELLO carries a
--  second roster frame, `ceil`. It is the frame of the sender's
--  ceiling-cell roster when the cell is the only reason for the sender's
--  maxceil (Kome.Frontier.Ceil_Live), and empty otherwise. The cell's
--  record is not an element: it is not in the snapshot, the digests or the
--  fingerprints. Without the frame, two replicas with equal rows and
--  different cells would end the session at the HELLOs with different
--  maxceil. It is a signed record, not a register value (D13 stands).
--  On receipt this package checks only the two lengths (Hello_Wire_OK);
--  the content of a received `ceil` is checked by the caller, like an
--  item frame. The sender duty is the precondition Ceil_Frame_OK of
--  Admit. The receiver duties are duties of the caller; the reference
--  caller is the store session of the test main. One of them has a proved
--  operation, Kome.Write.Receive_Ceil; when and in which order the caller
--  calls it is not proved.
--    * Sender (a contract: Ceil_Frame_OK, the Pre of Admit). At Admit,
--      Ceil is Kome.Store.Read_Frame (S, Tag_Off (Ceil_Tag (F))) if
--      Ceil_Live (F), else an empty array (Kome.Store.Lemma_Ceil_Tag: it
--      is the cell's ROSTER frame, at most Cred_Max bytes, and its header
--      is Ceil_Held (F)). A caller that leaves out a live cell, or sends
--      another roster in its place, does not meet the Pre.
--    * Receiver, which operation takes which frame. The credential is
--      applied as an authorization record (Kome.Write.Receive, that is,
--      Put_Frame): it can enter a row, and it can return Ceil_Only. The
--      ceiling frame Peer.Ceil (0 .. Peer.Ceil_Len - 1), if Ceil_Len > 0,
--      goes to Kome.Write.Receive_Ceil and to nothing else. Receive_Ceil
--      checks that the frame is a verified ROSTER (Malformed if not: a
--      protocol violation, end the session) and applies it with
--      Kome.Store.Put_Ceil only. It never enters a row,
--      so a roster that a peer keeps only in its cell cannot become
--      ROSTER_eff or a quarantine here.
--    * Receiver, the order. Same_Snapshot requires the snapshot that our
--      HELLO described, and both applies can change the digests. If our
--      HELLO was out when the peer's HELLO was accepted: (1) if the
--      session is now in Auth, pin, fill the frame table, Snapshot_Of,
--      Seal; (2) apply the credential; (3) apply the ceiling frame. If our
--      HELLO was not out: (1) apply the credential; (2) evaluate the gate,
--      and if it is closed apply nothing more (the ceiling frame is
--      dropped if the session ends without Admit); (3) Admit, with the
--      digest states and Ceil_Live (F) as they are now; (4) if the session
--      is now in Auth, the snapshot as above; (5) apply the ceiling frame.
--      In both orders nothing else is applied between Admit and the seal,
--      and the ceiling frame is applied before the next Receive or
--      Next_Phase. Admit requires Gate_Open, so the ceiling frame of a
--      peer is applied only when our gate admitted that peer at our
--      HELLO. In the first order the credential can close the gate
--      before the ceiling frame is applied; the next Receive then
--      aborts, and the peer gains nothing that its credential, a
--      certified roster, could not carry itself.
--    * Ceil_Only (from the credential or from the ceiling frame) counts
--      as an applied authorization record for the sync point.
--    * SUSPECT_RELAY for the ceiling frame: the caller reports the peer's
--      static key exactly when Put_Ceil returned Ceil_Only (the frame
--      raised our maxceil) and the frame's signer was root-voided in our
--      view before the call (Kome.Views.Root_Void). This is the flag
--      Suspect_Relay of Kome.Write.Receive_Ceil (its Post). A frame that
--      changes nothing flags nobody: an honest replica sends its live
--      cell in every HELLO, also after the cell's signer is root-voided.
--
--  Durability: a session counts as Complete only after the log is flushed
--  to Kome.Store.Log_Length (the sync point, DESIGN.md §8; AUDIT.md H35).
--  This package trusts nothing that a lying peer puts in a HELLO. The
--  counts go into the budgets only as min (claimed, Elem_Max). The digest
--  only decides if the session ends early.
--
--  Session (D14, D13). The phases are Gate, Auth, Data, Done.
--    * Start takes the role, the cid (the gate needs it) and the Noise
--      static key of the peer (Peer_DH). P = Gate. Nothing goes out.
--    * Admit: the caller calls Admit when the gate admits the peer (the
--      precondition). Admit emits our HELLO from the two digest states
--      (the counts of the two ranges, the digest of their union, our
--      credential) and records the counts and the authorization-range
--      fingerprint for the ROOT.
--    * Receive of the HELLO of the peer (in Gate, before or after Admit):
--      the credential check above. If it passes, Receive keeps its counts
--      and digest, and the decoded HELLO goes back to the caller.
--    * When the two HELLOs have passed (in Admit or in Receive): if the
--      digests are equal, the session ends (Done, no more messages; under
--      A2, equal digests mean equal frontiers). If not, P = Auth, and the
--      initiator emits the authorization ROOT (from its digest state).
--    * In Auth, when no obligation of the initiator is open, the initiator
--      calls Next_Phase. Next_Phase emits the data ROOT and moves to Data.
--      In Data, the initiator is Done when nothing is open.
--    * The responder accepts a ROOT only in Auth: the first is the
--      authorization ROOT; the second, accepted only with nothing that it
--      asked open, is the data ROOT and moves it to Data. In Data, the
--      responder is Done when nothing is open after a Receive.
--    * Every other message is S_Unexpected and changes nothing: a ROOT at
--      the initiator or at the wrong time, any RANGE, ELEMENTS, HAVE or
--      ROOT before Auth, any reply that does not continue the head
--      obligation (below), and any message in Done.
--  The status of Receive is exactly Status_Of (session, snapshot, F, Eff,
--  input, part, keys). So each refusal has a characterisation in the two
--  directions:
--    * S_Malformed iff the decoder refuses;
--    * S_Aborted iff a well-formed HELLO in Gate carries an inadmissible
--      credential, or the gate is closed in Auth or Data;
--    * S_Limit iff the message would go above a budget;
--    * a well-formed, expected message within the budgets is accepted.
--  Complete (Sess) holds when the session ended without abort.
--
--  Transport. The phase gate assumes an in-order transport (Noise over a
--  stream, DESIGN.md §8). Two conditions stop the session before Complete:
--  loss, and a reordered ROOT (Receive refuses a data ROOT that arrives
--  before the last reply of the authorization phase). Then the caller
--  times out and starts again. DESIGN.md §8 states this.
--
--  Obligations and tiling replies (AUDIT.md G4, H19, S19). A RANGE part,
--  a ROOT or an ELEMENTS obliges its receiver to answer. A HAVE obliges
--  nothing. Each side keeps a FIFO of its open obligations (Open (Sess,
--  K), K = 1 .. Open_Count (Sess)), each a range [lo, hi) that it asked
--  about, in the order that it sent them. The transport is in order in
--  each direction, so the answers arrive in request order. The answer to
--  an obligation is a run of messages that tiles [lo, hi): the first
--  starts at lo, each next one starts where the last one ended (Next),
--  and the answer is complete when a message's hi reaches the head's hi
--  (Group_Done). Any kind may tile (each tile is itself a valid answer
--  for its sub-range); there is no group-size byte and no repeat rule.
--  Receive accepts a non-ROOT message only when it continues the head
--  obligation (Matches_Head); any other reply, also a duplicate delivery,
--  is S_Unexpected and changes nothing. So Complete (nothing open, no
--  abort) implies that each obligation got exactly one tiling answer. The
--  FIFO has Oblig_Cap entries (a discriminant of Session): a reply whose
--  obligations would not fit is S_Limit. An honest session needs at most
--  Range_Budget (S) + 8 × Peer_Claim + 6 (tested).
--
--  The responder (Respond) does these steps, for one range [lo, hi):
--    * On a RANGE part or a ROOT (lo, hi, fp, count): it finds our
--      elements in [lo, hi) (Window). If their count and fingerprint are
--      equal to those of the message, it confirms the range with an empty
--      HAVE. If not, and there are at most Ship_Threshold of them, it
--      ships them as ELEMENTS. If not, it splits [lo, hi) 16 ways
--      (Split_Fanout) over our elements; the children go out as one RANGE
--      message (Encode_Ranges).
--    * On ELEMENTS: it gives the caller every element that we do not have
--      (exactly those). Then, if we hold at most Ship_Threshold in the
--      range, it sends back as HAVE exactly the elements that the peer did
--      not have (an empty HAVE if none), tiling the range. If not, it
--      splits the range as above.
--    * On HAVE: it gives the caller every element that we do not have.
--  The Post of Respond pins: the kind of every reply (All_Kind); a reply
--  tiles the range (Tiles, also the HAVE reply, Have_Exact); every plan
--  is exact (Exact_Plans).
--
--  Message size (D12). No emitted message is longer than Max_Message_Len
--  bytes (Kome, §8). This is proved (Plan_OK, Plan_Len, Range_Msg_Len). A
--  RANGE of 16 parts is 2 004 bytes and a HELLO at most Hello_Max_Len =
--  17 877. If the frames of an ELEMENTS or a HAVE do not fit, the sender
--  sends one message for each element, over a sub-range that holds only
--  that element (the sub-ranges tile the range). One element always fits:
--  a frame is at most Kome.Records.Frame_Max = 41 120 bytes, less than
--  Frame_Ship_Max = Max_Message_Len - 167 - 2 = 48 983 (a compile-time
--  check, Lemma_Frame_Ships).
--
--  Well-founded split (the measure of T7). Each RANGE part that a
--  responder emits is a sub-range of the range that it answers, with
--  strictly fewer of the responder's elements (Shrinks, measured by
--  My_Count). So the measure of T7 is lexicographic: (μ (r), k) with
--  μ ([lo, hi)) = |F_A ∩ [lo, hi)| + |F_B ∩ [lo, hi)|, and k = 1 for a
--  RANGE, 0 for an ELEMENTS. The implementation makes balanced splits
--  (child counts ⌊n/16⌋ or ⌈n/16⌉, or blocks of 64 for n >= 1 024;
--  tested, not proved). With balanced splits, a chain of replies in one
--  phase holds at most s = ⌈log₁₆ N_A⌉ + ⌈log₁₆ N_B⌉ splits, so at most
--  2s + 3 one-way messages for each phase (part of T7, not proved).
--
--  Duplicate deliveries. The snapshot is frozen for the session. So, when
--  we split a range after we receive ELEMENTS, the peer ships the same
--  elements again on the children, and they are delivered again. Record
--  application is idempotent, so this costs bandwidth, not correctness.
--
--  Budgets (a hostile peer cannot cause unlimited traffic). Each budget
--  counts over the two phases:
--    * The accepted logical messages are at most Msg_Budget (our |S|, the
--      claimed count of the peer).
--    * The RANGE parts that we emit in replies are at most Range_Budget
--      (S) = 2 × (2 |S| + 2).
--    * The item bytes that we emit are at most Ship_Budget (S) = 2 × 8 ×
--      (frame bytes + 2 |S|).
--    * The open obligations are at most Oblig_Cap.
--  The two ROOTs are not replies, and Ranges does not count them. Receive
--  refuses a message that would go above a budget, with S_Limit. The
--  counts have exact definitions (Ranges_Upto, Obligations_Upto,
--  Items_Upto), so the Post of Receive states every budget check over the
--  true counts of the reply.
--
--  Tested, not proved (stated limitations):
--    * T7 (termination and convergence). The two-phase session test
--      converges two replicas.
--    * That Decode accepts every RANGE and every ELEMENTS / HAVE with
--      items (a proof shows that it accepts every ROOT and every confirm),
--      and the bytes of an encoded RANGE after its k and of the items of an
--      encoded ELEMENTS / HAVE (the Posts state the head; a test checks
--      the round trip).
--    * That splits are balanced and that the cuts of a large window are
--      on multiples of 64.
--    * The honest-session derivations for Msg_Budget, Range_Budget,
--      Ship_Budget and the sufficient Oblig_Cap.
--    * The session-level statements "every accepted message was accepted
--      while the gate held" and "Complete implies one tiling answer for
--      each obligation" are inductions over the per-call Posts.
pragma Ada_2022;
with Kome.Accumulator;
with Kome.Headers;   use Kome.Headers;
with Kome.Digest;
with Kome.Frontier;
with Kome.Guard;
with Kome.Keys;
with Kome.Records;
with Kome.Views;
package Kome.Reconcile with SPARK_Mode is

   use type Kome.Views.Header_View;

   ----------------------------------------------------------------------
   --  Element keys and their order (DESIGN.md §8, SIMPLIFY.md S18).
   ----------------------------------------------------------------------

   --  A byte of the key (the tag at byte 0, sub at byte 17). Elements use
   --  tags 0 .. 3. Range bounds can use any byte, so Max_Key (tag 255) is
   --  above every element.
   type Kind_Code is range 0 .. 255 with Size => 8;

   type Elem_Key is record
      K   : Kind_Code := 0;
      Ent : Id128;
      Sub : Kind_Code := 0;
      FH  : Key256;
      H   : Key256;
   end record;

   Key_Wire_Len : constant := 1 + 16 + 1 + 32 + 32;   --  82

   --  tag ‖ ent ‖ sub ‖ fh ‖ h compared bytewise.
   function Key_Lt (A, B : Elem_Key) return Boolean is
     (A.K < B.K or else (A.K = B.K and then
      (Kome.Keys.Id_Lt (A.Ent, B.Ent) or else (A.Ent = B.Ent and then
      (A.Sub < B.Sub or else (A.Sub = B.Sub and then
      (Lt (A.FH, B.FH) or else (A.FH = B.FH and then
       Lt (A.H, B.H)))))))));

   function Key_Le (A, B : Elem_Key) return Boolean is (not Key_Lt (B, A));

   --  The data tag (S18): every data key starts with 03.
   Data_Key_Tag : constant Kind_Code := 3;

   --  The full key space: every element key k has Min_Key <= k < Max_Key.
   --  Data_Lo divides it. Authorization records (tags 0 .. 2) are in
   --  [Min_Key, Data_Lo). Data records (tag 3) are in [Data_Lo, Max_Key).
   Min_Key : constant Elem_Key :=
     (K => 0, Ent => (others => 0), Sub => 0, FH => (others => 0), H => (others => 0));
   Data_Lo : constant Elem_Key :=
     (K => Data_Key_Tag, Ent => (others => 0), Sub => 0, FH => (others => 0),
      H => (others => 0));
   Max_Key : constant Elem_Key :=
     (K => 255, Ent => (others => 0), Sub => 0, FH => (others => 0), H => (others => 0));

   --  The element key of the header of a record (S18). Data:
   --  03 ‖ ent ‖ sub ‖ fh ‖ h, sub = 0 for a DEL and 1 for a PUT.
   --  Authorization: tag ‖ 0^17 ‖ signer ‖ h, the tag is the code of the
   --  kind (Kome.Headers) and the signer is the issuer.
   function Key_Of (R : Header) return Elem_Key is
     (if Is_Data (R) then
        (K => Data_Key_Tag, Ent => R.Ent, Sub => (if R.K = K_Del then 0 else 1),
         FH => R.FH, H => R.V.H)
      else
        (K => Kind_Code (Kind'Pos (R.K)), Ent => (others => 0), Sub => 0,
         FH => R.Issuer, H => R.V.H));

   --  The order is a strict total order (as T1 for versions).
   procedure Lemma_Key_Lt_Irrefl (A : Elem_Key) with
     Ghost, Global => null,
     Post => not Key_Lt (A, A);

   procedure Lemma_Key_Lt_Asym (A, B : Elem_Key) with
     Ghost, Global => null,
     Pre  => Key_Lt (A, B),
     Post => not Key_Lt (B, A);

   procedure Lemma_Key_Lt_Trans (A, B, C : Elem_Key) with
     Ghost, Global => null,
     Pre  => Key_Lt (A, B) and then Key_Lt (B, C),
     Post => Key_Lt (A, C);

   procedure Lemma_Key_Trichotomy (A, B : Elem_Key) with
     Ghost, Global => null,
     Post => Key_Lt (A, B) or else A = B or else Key_Lt (B, A);

   --  A <= B < C  ⇒  A < C.
   procedure Lemma_Key_Le_Lt_Trans (A, B, C : Elem_Key) with
     Ghost, Global => null,
     Pre  => Key_Le (A, B) and then Key_Lt (B, C),
     Post => Key_Lt (A, C);

   --  The key order of the data row (S18): entity-major, DEL before PUT,
   --  then the field hash, is the order of the data keys.
   procedure Lemma_Data_Key_Order (A, B : Header) with
     Ghost, Global => null,
     Pre  => Is_Data (A) and then Is_Data (B)
             and then (Kome.Keys.Id_Lt (A.Ent, B.Ent)
                       or else (A.Ent = B.Ent
                                and then (A.K < B.K
                                          or else (A.K = B.K and then Lt (A.FH, B.FH))))),
     Post => Key_Lt (Key_Of (A), Key_Of (B));

   --  Authorization keys are below Data_Lo, data keys in [Data_Lo, Max_Key).
   procedure Lemma_Key_Ranges (R : Header) with
     Ghost, Global => null,
     Post => (if Is_Data (R) then Key_Le (Data_Lo, Key_Of (R))
                                  and then Key_Lt (Key_Of (R), Max_Key)
              else Key_Lt (Key_Of (R), Data_Lo) and then Key_Le (Min_Key, Key_Of (R)));

   ----------------------------------------------------------------------
   --  Sizes and wire layout (DESIGN.md §8; Kome.Max_Message_Len,
   --  Split_Fanout, Ship_Threshold).
   ----------------------------------------------------------------------

   Tag_Hello    : constant Byte := 1;
   Tag_Range    : constant Byte := 2;
   Tag_Elements : constant Byte := 3;
   Tag_Have     : constant Byte := 4;
   Tag_Root     : constant Byte := 5;

   --  The protocol version, in the Noise prologue (S11).
   Proto_Version : constant Byte := 1;

   --  RANGE: 02 ‖ k ‖ bounds[k + 1] ‖ k × (count:u48 ‖ fp[32]).
   Range_O_K      : constant := 1;
   Range_O_Bounds : constant := 2;
   Part_Len       : constant := 6 + 32;                              --  38
   Count_Len      : constant := 6;

   subtype Part_Count is Natural range 0 .. Split_Fanout;
   subtype Part_Index is Positive range 1 .. Split_Fanout;

   --  The place of bound I (0 .. k) and of part J (1 .. k) of a RANGE with
   --  k parts, relative to the message.
   function Bound_At (I : Natural) return Natural is
     (Range_O_Bounds + Key_Wire_Len * I)
   with Pre => I <= Split_Fanout;

   function Part_At (K : Part_Index; J : Part_Index) return Natural is
     (Range_O_Bounds + Key_Wire_Len * (K + 1) + Part_Len * (J - 1))
   with Pre => J <= K;

   function Range_Msg_Len (K : Part_Count) return Natural is
     (Range_O_Bounds + Key_Wire_Len * (K + 1) + Part_Len * K);

   pragma Compile_Time_Error
     (Range_O_Bounds + Key_Wire_Len * (Split_Fanout + 1) + Part_Len * Split_Fanout /= 2_004,
      "S19: a 16-part RANGE is 2 004 bytes");

   --  ELEMENTS / HAVE: tag ‖ lo ‖ hi ‖ n:u16 ‖ n × (flen:u16 ‖ frame).
   O_Lo           : constant := 1;
   O_Hi           : constant := O_Lo + Key_Wire_Len;                 --  83
   Elems_O_N      : constant := O_Hi + Key_Wire_Len;                 --  165
   Elems_Fixed    : constant := Elems_O_N + 2;                       --  167
   Item_Overhead  : constant := 2;
   Frame_Ship_Max : constant := Max_Message_Len - Elems_Fixed - Item_Overhead;

   pragma Compile_Time_Error
     (Frame_Ship_Max /= 48_983, "DESIGN.md §8: one ELEMENTS item carries 48 983 frame bytes");
   --  D12: every well-formed frame (at most 41 120 bytes) fits one item.
   pragma Compile_Time_Error
     (Kome.Records.Frame_Max > Frame_Ship_Max,
      "DESIGN.md §8 (D12): Kome.Records.Frame_Max must not exceed Frame_Ship_Max");

   --  ROOT: 05 ‖ count:u48 ‖ fp[32].
   Root_O_Count : constant := 1;
   Root_O_Fp    : constant := 7;
   Root_Len     : constant := 39;

   --  HELLO (D13; AUDIT.md H12): 01 ‖ n_auth ‖ n_data ‖ digest[32] ‖
   --  cred_len ‖ ceil_len ‖ cred ‖ ceil.
   Hello_O_NAuth  : constant := 1;
   Hello_O_NData  : constant := 5;
   Hello_O_Digest : constant := 9;
   Hello_O_CLen   : constant := 41;
   Hello_O_KLen   : constant := 43;                                --  ceil_len:u16
   Hello_Fixed    : constant := 45;
   Cred_Max       : constant := Kome.Records.Roster_Frame_Max;     --  8 916
   Hello_Max_Len  : constant := Hello_Fixed + 2 * Cred_Max;        --  17 877
   pragma Compile_Time_Error
     (Cred_Max /= 8_916 or else Hello_Max_Len /= 17_877,
      "DESIGN.md §8: a HELLO is at most 17 877 bytes");

   subtype Frame_Size is Positive range 1 .. Frame_Ship_Max;
   subtype Msg_Length is Natural range 0 .. Max_Message_Len;
   subtype Msg_Buffer is Byte_Array (0 .. Max_Message_Len - 1);

   subtype Item_Count is Natural range 0 .. Ship_Threshold;
   subtype Item_Index is Positive range 1 .. Ship_Threshold;

   --  Element counts and indices: the records that one replica holds for
   --  one collection. Kome.Digest.Elem_Max is Kome.Frontier.Held_Max.
   Elem_Max : constant := Kome.Digest.Elem_Max;
   pragma Compile_Time_Error
     (Elem_Max /= Kome.Frontier.Held_Max,
      "DESIGN.md §8: Elem_Max must be Kome.Frontier.Held_Max");
   subtype Elem_Count is Kome.Digest.Elem_Count;
   subtype Elem_Index is Kome.Digest.Elem_Index;
   subtype Lo_Bound   is Kome.Digest.Lo_Bound;

   --  Byte counts of frames and of shipped items.
   type Byte_Total is range 0 .. 2 ** 40;
   subtype Snap_Bytes is Byte_Total range 0 .. Elem_Max * Frame_Ship_Max;

   ----------------------------------------------------------------------
   --  The Noise XK prologue (S11): "kome/1" ‖ ns ‖ proto.
   ----------------------------------------------------------------------

   Prologue_Tag_Len : constant := 6;
   Prologue_Tag : constant Byte_Array (0 .. Prologue_Tag_Len - 1) :=
     [16#6B#, 16#6F#, 16#6D#, 16#65#, 16#2F#, 16#31#];   --  "kome/1"
   Prologue_Len : constant := Prologue_Tag_Len + NS_Len + 1;   --  23
   subtype Prologue_Bytes is Byte_Array (0 .. Prologue_Len - 1);

   function Prologue (Cid : Hash256) return Prologue_Bytes with
     Global => null,
     Post   => Prologue'Result (0 .. Prologue_Tag_Len - 1) = Prologue_Tag
               and then Prologue'Result (Prologue_Tag_Len .. Prologue_Tag_Len + NS_Len - 1)
                          = Kome.Records.NS_Of (Cid)
               and then Prologue'Result (Prologue_Len - 1) = Proto_Version;

   ----------------------------------------------------------------------
   --  Functions that read the wire. They are quantifier-free, so they are
   --  public (rule 2).
   ----------------------------------------------------------------------

   function Wire_U16 (B : Byte_Array; P : Natural) return Natural is
     (Natural (B (P)) * 256 + Natural (B (P + 1)))
   with Pre => P >= B'First and then P < B'Last;

   function Wire_U32 (B : Byte_Array; P : Natural) return Word is
     (Kome.Keys.Word_Of (B (P), B (P + 1), B (P + 2), B (P + 3)))
   with Pre => P >= B'First and then P <= B'Last and then B'Last - P >= 3;

   function Wire_U48 (B : Byte_Array; P : Natural) return U48 is
     (U48 (Wire_U16 (B, P)) * 2 ** 32 + U48 (Wire_U32 (B, P + 2)))
   with Pre => P >= B'First and then P <= B'Last and then B'Last - P >= 5;

   function Wire_Id128 (B : Byte_Array; P : Natural) return Id128 is
     ((W0 => Wire_U32 (B, P),     W1 => Wire_U32 (B, P + 4),
       W2 => Wire_U32 (B, P + 8), W3 => Wire_U32 (B, P + 12)))
   with Pre => P >= B'First and then P <= B'Last and then B'Last - P >= 15;

   function Wire_Key256 (B : Byte_Array; P : Natural) return Key256 is
     ((W0 => Wire_U32 (B, P),      W1 => Wire_U32 (B, P + 4),
       W2 => Wire_U32 (B, P + 8),  W3 => Wire_U32 (B, P + 12),
       W4 => Wire_U32 (B, P + 16), W5 => Wire_U32 (B, P + 20),
       W6 => Wire_U32 (B, P + 24), W7 => Wire_U32 (B, P + 28)))
   with Pre => P >= B'First and then P <= B'Last and then B'Last - P >= 31;

   function Wire_Key (B : Byte_Array; P : Natural) return Elem_Key is
     ((K   => Kind_Code (B (P)),
       Ent => Wire_Id128 (B, P + 1),
       Sub => Kind_Code (B (P + 17)),
       FH  => Wire_Key256 (B, P + 18),
       H   => Wire_Key256 (B, P + 50)))
   with Pre => P >= B'First and then P <= B'Last
               and then B'Last - P >= Key_Wire_Len - 1;

   ----------------------------------------------------------------------
   --  Key_Lt is bytewise order on the 82-byte wire key: equal keys iff
   --  equal bytes, and the first byte that is different decides.
   ----------------------------------------------------------------------

   subtype Key_Wire is Byte_Array (0 .. Key_Wire_Len - 1);

   procedure Lemma_Key_Eq_Is_Bytewise (A, B : Key_Wire) with
     Ghost, Global => null,
     Post => (Wire_Key (A, 0) = Wire_Key (B, 0)) = (A = B);

   procedure Lemma_Key_Lt_First_Difference (A, B : Key_Wire; I : Natural) with
     Ghost, Global => null,
     Pre  => I < Key_Wire_Len
             and then (for all J in 0 .. I - 1 => A (J) = B (J))
             and then A (I) /= B (I),
     Post => Key_Lt (Wire_Key (A, 0), Wire_Key (B, 0)) = (A (I) < B (I));

   ----------------------------------------------------------------------
   --  The frame table: the frames of the records of F in the flat order of
   --  F (entry I: the frame of Held (F, I)). The caller fills it from
   --  Kome.Store.Read_Frame. Cap entries, Pool_Cap bytes of frames.
   ----------------------------------------------------------------------

   Pool_Max : constant := 2 ** 30;
   subtype Pool_Size is Natural range 0 .. Pool_Max;

   type Frame_Table (Cap : Elem_Count; Pool_Cap : Pool_Size) is private;

   function Table_Count (T : Frame_Table) return Elem_Count with
     Global => null,
     Post   => Table_Count'Result <= T.Cap;

   function Table_Bytes (T : Frame_Table) return Pool_Size with Global => null;

   function Table_Len (T : Frame_Table; I : Elem_Index) return Frame_Size with
     Global => null,
     Pre    => I <= Table_Count (T);

   --  Every entry is in the pool. This function has a quantifier, so its
   --  completion is in the private part (rule 2).
   function Table_Valid (T : Frame_Table) return Boolean with Global => null;

   function Table_Frame (T : Frame_Table; I : Elem_Index) return Byte_Array with
     Global => null,
     Pre    => Table_Valid (T) and then I <= Table_Count (T),
     Post   => Table_Frame'Result'Length = Table_Len (T, I);

   procedure Clear_Table (T : out Frame_Table) with
     Global => null,
     Post   => Table_Count (T) = 0 and then Table_Bytes (T) = 0 and then Table_Valid (T);

   type Snap_Status is
     (Snap_OK,
      Snap_Unsorted,    --  Append: the key is not above the last one;
                        --  Snapshot_Of: two held records with one key (A2)
      Snap_Too_Large,   --  Add_Frame: frame empty or longer than Frame_Ship_Max
                        --  (never for a well-formed frame, Lemma_Frame_Ships)
      Snap_No_Space);   --  Cap elements (or Pool_Cap bytes of a table) reached

   --  Append the next frame. On refusal, nothing changes (T13).
   procedure Add_Frame
     (T      : in out Frame_Table;
      F      : Byte_Array;
      Result : out Snap_Status)
   with
     Global => null,
     Pre    => Table_Valid (T),
     Post   => Table_Valid (T)
       and then Result in Snap_OK | Snap_Too_Large | Snap_No_Space
       and then (if Result = Snap_OK then
                   Table_Count (T) = Table_Count (T'Old) + 1
                   and then Table_Bytes (T) = Table_Bytes (T'Old) + F'Length
                   and then Table_Len (T, Table_Count (T)) = F'Length
                   and then Table_Frame (T, Table_Count (T)) = F
                   and then (for all I in 1 .. Table_Count (T'Old) =>
                               Table_Len (T, I) = Table_Len (T'Old, I)
                               and then Table_Frame (T, I) = Table_Frame (T'Old, I))
                 else T = T'Old)
       and then (Result = Snap_Too_Large) = (F'Length not in Frame_Size)
       and then (Result = Snap_OK) =
                (F'Length in Frame_Size
                 and then Table_Count (T'Old) < T.Cap
                 and then F'Length <= T.Pool_Cap - Table_Bytes (T'Old));

   ----------------------------------------------------------------------
   --  Snapshot: our elements for one session, in strictly ascending
   --  order, each with its frame length and its source index in F (and so
   --  in the frame table). Cap elements.
   ----------------------------------------------------------------------

   type Snapshot (Cap : Elem_Count) is private;

   function Count (S : Snapshot) return Elem_Count with
     Global => null,
     Post   => Count'Result <= S.Cap;

   --  Bytes of the frames of the elements.
   function Frame_Bytes (S : Snapshot) return Snap_Bytes with Global => null;

   function Key (S : Snapshot; I : Elem_Index) return Elem_Key with
     Global => null,
     Pre    => I <= Count (S);

   function Frame_Len (S : Snapshot; I : Elem_Index) return Frame_Size with
     Global => null,
     Pre    => I <= Count (S);

   --  The index in F (and in the frame table) of element I.
   function Source (S : Snapshot; I : Elem_Index) return Elem_Index with
     Global => null,
     Pre    => I <= Count (S);

   --  Strictly ascending order (pairwise) and the byte total. This
   --  function has a quantifier, so its completion is in the private part
   --  (rule 2).
   function Valid (S : Snapshot) return Boolean with Global => null;

   --  The frame table T holds the frame of every element of S: the source
   --  of element I is an entry of T of its length. This function has a
   --  quantifier, so its completion is in the private part.
   function Linked (S : Snapshot; T : Frame_Table) return Boolean with
     Global => null;

   --  The frame of element I, from the table.
   function Elem_Frame (S : Snapshot; T : Frame_Table; I : Elem_Index) return Byte_Array
   with
     Global => null,
     Pre    => Table_Valid (T) and then Linked (S, T) and then I <= Count (S),
     Post   => Elem_Frame'Result'Length = Frame_Len (S, I);

   --  The prefix-sum table of a snapshot (D15): Slots = Prefix_Slots (|S|)
   --  accumulators, one for each full block of 64 elements and the total.
   function Prefix_Slots (N : Elem_Count) return Kome.Digest.Block_Index is
     (N / Kome.Digest.Block_Elems + 1);

   type Prefix (Slots : Kome.Digest.Block_Index) is private;

   --  P is the prefix-sum table of the current elements of S
   --  (Kome.Digest.Prefix_Valid). Seal makes it so. Ghost.
   function Sealed (S : Snapshot; P : Prefix) return Boolean with
     Ghost, Global => null;

   procedure Clear (S : out Snapshot) with
     Global => null,
     Post   => Count (S) = 0 and then Frame_Bytes (S) = 0 and then Valid (S);

   --  Append the next element: key K, frame length L, source Src (for a
   --  snapshot that a caller builds element by element; Snapshot_Of builds
   --  the snapshot of a frontier). Keys must come in strictly ascending
   --  order. On refusal, nothing changes (T13).
   procedure Append
     (S      : in out Snapshot;
      K      : Elem_Key;
      L      : Frame_Size;
      Src    : Elem_Index;
      Result : out Snap_Status)
   with
     Global => null,
     Pre    => Valid (S),
     Post   => Valid (S)
       and then Result in Snap_OK | Snap_Unsorted | Snap_No_Space
       and then (if Result = Snap_OK then
                   Count (S) = Count (S'Old) + 1
                   and then Frame_Bytes (S) = Frame_Bytes (S'Old) + Byte_Total (L)
                   and then Key (S, Count (S)) = K
                   and then Frame_Len (S, Count (S)) = L
                   and then Source (S, Count (S)) = Src
                   and then (for all I in 1 .. Count (S'Old) =>
                               Key (S, I) = Key (S'Old, I)
                               and then Frame_Len (S, I) = Frame_Len (S'Old, I)
                               and then Source (S, I) = Source (S'Old, I))
                 else S = S'Old)
       and then (Result = Snap_OK) =
                ((Count (S'Old) = 0 or else Key_Lt (Key (S'Old, Count (S'Old)), K))
                 and then Count (S'Old) < S.Cap);

   --  Build the prefix-sum table (D15) of the elements of S: O(n)
   --  additions, once per snapshot. P must have Prefix_Slots (|S|) slots.
   procedure Seal (S : Snapshot; P : out Prefix) with
     Global => null,
     Pre    => Valid (S) and then P.Slots = Prefix_Slots (Count (S)),
     Post   => Sealed (S, P);

   --  D12: a frame of a well-formed record (1 .. Kome.Records.Frame_Max
   --  bytes) is never Snap_Too_Large.
   procedure Lemma_Frame_Ships (L : Natural) with
     Ghost, Global => null,
     Pre  => L >= 1 and then L <= Kome.Records.Frame_Max,
     Post => L in Frame_Size;

   ----------------------------------------------------------------------
   --  Windows: our elements in [Lo, Hi).
   ----------------------------------------------------------------------

   function In_Window (K, Lo, Hi : Elem_Key) return Boolean is
     (Key_Le (Lo, K) and then Key_Lt (K, Hi));

   --  First .. Last are exactly the indices of our elements in [Lo, Hi).
   function Covers
     (S : Snapshot; Lo, Hi : Elem_Key; First : Lo_Bound; Last : Elem_Count)
      return Boolean
   with Global => null;

   type Span is record
      First : Lo_Bound   := 1;
      Last  : Elem_Count := 0;
   end record;

   function Window (S : Snapshot; Lo, Hi : Elem_Key) return Span with
     Global => null,
     Pre    => Valid (S) and then Key_Lt (Lo, Hi),
     Post   => Window'Result.First <= Window'Result.Last + 1
               and then Window'Result.Last <= Count (S)
               and then Covers (S, Lo, Hi, Window'Result.First, Window'Result.Last);

   --  The ghost measure of T7: the number of our elements in [Lo, Hi).
   function My_Count (S : Snapshot; Lo, Hi : Elem_Key) return Elem_Count is
     (Window (S, Lo, Hi).Last + 1 - Window (S, Lo, Hi).First)
   with Ghost, Global => null,
        Pre => Valid (S) and then Key_Lt (Lo, Hi);

   --  A window has one size: any two covers of [Lo, Hi) have equal spans.
   procedure Lemma_Covers_Unique
     (S : Snapshot; Lo, Hi : Elem_Key;
      F1 : Lo_Bound; L1 : Elem_Count; F2 : Lo_Bound; L2 : Elem_Count)
   with
     Ghost, Global => null,
     Pre  => F1 <= L1 + 1 and then L1 <= Count (S)
             and then F2 <= L2 + 1 and then L2 <= Count (S)
             and then Covers (S, Lo, Hi, F1, L1)
             and then Covers (S, Lo, Hi, F2, L2),
     Post => L1 + 1 - F1 = L2 + 1 - F2
             and then (if F1 <= L1 then F1 = F2 and then L1 = L2);

   procedure Lemma_My_Count
     (S : Snapshot; Lo, Hi : Elem_Key; F : Lo_Bound; L : Elem_Count)
   with
     Ghost, Global => null,
     Pre  => Valid (S) and then Key_Lt (Lo, Hi)
             and then F <= L + 1 and then L <= Count (S)
             and then Covers (S, Lo, Hi, F, L),
     Post => My_Count (S, Lo, Hi) = L + 1 - F;

   --  Take a sub-run B .. E of a covered window, with the ends of the
   --  parent or the adjacent elements as its bounds. Exactly those bounds
   --  cover the sub-run, and it is a non-empty sub-range of the parent.
   function Child_Lo (S : Snapshot; Lo : Elem_Key; I, B : Elem_Index)
     return Elem_Key
   is (if B = I then Lo else Key (S, B))
   with Pre => B <= Count (S);

   function Child_Hi (S : Snapshot; Hi : Elem_Key; J, E : Elem_Index)
     return Elem_Key
   is (if E = J then Hi else Key (S, E + 1))
   with Pre => E <= J and then J <= Count (S);

   procedure Lemma_Child
     (S : Snapshot; Lo, Hi : Elem_Key; I, J, B, E : Elem_Index)
   with
     Ghost, Global => null,
     Pre  => Valid (S) and then Key_Lt (Lo, Hi)
             and then J <= Count (S)
             and then Covers (S, Lo, Hi, I, J)
             and then I <= B and then B <= E and then E <= J,
     Post => Key_Lt (Child_Lo (S, Lo, I, B), Child_Hi (S, Hi, J, E))
             and then Key_Le (Lo, Child_Lo (S, Lo, I, B))
             and then Key_Le (Child_Hi (S, Hi, J, E), Hi)
             and then Covers (S, Child_Lo (S, Lo, I, B), Child_Hi (S, Hi, J, E), B, E);

   --  The interior cut T (1 .. 15) of a split of the window First ..
   --  First + N - 1 when N >= Big_Window (S20): the last element of child
   --  T is at the multiple of 64 at or below First - 1 + T (N / 16). The
   --  ends of the children are then block boundaries of the prefix sums,
   --  so only the two ends of the parent range walk elements. For N >=
   --  1 024 the cuts are strictly increasing and inside the window
   --  (N / 16 >= 64); the responder checks that before it uses one.
   Big_Window : constant := 1_024;

   function Cut_At (First : Elem_Index; N : Elem_Count; T : Positive) return Natural is
     (Kome.Digest.Block_Elems
        * ((First - 1 + T * (N / Split_Fanout)) / Kome.Digest.Block_Elems))
   with Pre => T <= Split_Fanout;

   ----------------------------------------------------------------------
   --  Fingerprints (DESIGN.md §8 "fingerprint = digest", T6): fp over the
   --  h of our elements First .. Last, with Kome.Digest. Range_Fp is the
   --  definition; Fingerprint_Of computes it from the prefix sums (D15).
   ----------------------------------------------------------------------

   function Range_Fp (S : Snapshot; First : Lo_Bound; Last : Elem_Count)
     return Hash256
   with Global => null,
        Pre    => First <= Last + 1 and then Last <= Count (S);

   --  At most 64 accumulator additions and one hash (Kome.Digest.Range_Sum).
   procedure Fingerprint_Of
     (S     : Snapshot;
      P     : Prefix;
      First : Lo_Bound;
      Last  : Elem_Count;
      FP    : out Hash256)
   with
     Global => null,
     Pre    => Valid (S) and then Sealed (S, P)
               and then First <= Last + 1 and then Last <= Count (S),
     Post   => FP = Range_Fp (S, First, Last);

   ----------------------------------------------------------------------
   --  The snapshot of a frontier (A12, S18, S21).
   ----------------------------------------------------------------------

   --  The snapshot of F: the keys of the held records of F in key order,
   --  each with the length of its frame in T. On Snap_OK:
   --    * |S| = |F|, element I of S is the held record Source (S, I) of F
   --      with its key, the sources are distinct (so S holds exactly the
   --      records of F), and T holds every frame (Linked);
   --    * the digest of S is the digest of F (T6, Lemma_Sum_Perm).
   --  The caller then builds the prefix-sum table with Seal.
   --  Snap_No_Space when |F| > S.Cap. Snap_Unsorted when two held records
   --  have one key (equal h: A2 excludes it; never for two data records).
   --  On a refusal, S is empty.
   procedure Snapshot_Of
     (F      : Kome.Frontier.State;
      T      : Frame_Table;
      S      : out Snapshot;
      Result : out Snap_Status)
   with
     Global => null,
     Pre    => Table_Valid (T)
               and then Table_Count (T) = Kome.Frontier.Count (F),
     Post   => Valid (S)
       and then Result in Snap_OK | Snap_Unsorted | Snap_No_Space
       and then (Result = Snap_No_Space) = (Kome.Frontier.Count (F) > S.Cap)
       and then (if Result = Snap_OK then
                   Count (S) = Kome.Frontier.Count (F)
                   and then Linked (S, T)
                   and then (for all I in 1 .. Count (S) =>
                               Source (S, I) <= Kome.Frontier.Count (F)
                               and then Key (S, I)
                                          = Key_Of (Kome.Frontier.Held (F, Source (S, I)))
                               and then Frame_Len (S, I) = Table_Len (T, Source (S, I)))
                   and then (for all I in 1 .. Count (S) =>
                               (for all J in 1 .. Count (S) =>
                                  (if I /= J then Source (S, I) /= Source (S, J))))
                   and then Range_Fp (S, 1, Count (S)) = Kome.Digest.Frontier_Digest (F)
                 else Count (S) = 0);

   ----------------------------------------------------------------------
   --  Plans: messages to send, as references into the snapshot. Encode
   --  and Encode_Ranges change plans into bytes.
   ----------------------------------------------------------------------

   type Out_Kind is (P_Range, P_Elements, P_Have);

   type Index_List is array (Item_Index) of Elem_Index;

   --  A RANGE plan is one part of a RANGE message (an outbox of RANGE
   --  plans that tile a range is one message, Encode_Ranges). An ELEMENTS
   --  or HAVE plan is one message (Encode).
   type Plan is record
      Kind  : Out_Kind   := P_Range;
      Lo    : Elem_Key   := Min_Key;
      Hi    : Elem_Key   := Max_Key;
      First : Lo_Bound   := 1;     --  RANGE, ELEMENTS: our elements First .. Last
      Last  : Elem_Count := 0;
      N     : Item_Count := 0;     --  HAVE: our elements Items (1 .. N)
      Items : Index_List := [others => 1];
   end record;

   --  The wire size of one item, and of a plan's item parts.
   function Item_Size (S : Snapshot; I : Elem_Index) return Positive is
     (Item_Overhead + Frame_Len (S, I))
   with Pre => I <= Count (S);

   function Run_Size (S : Snapshot; First : Lo_Bound; Last : Elem_Count)
     return Natural
   is ((if Last >= First then Item_Size (S, First) else 0)
       + (if Last >= First + 1 then Item_Size (S, First + 1) else 0)
       + (if Last >= First + 2 then Item_Size (S, First + 2) else 0)
       + (if Last >= First + 3 then Item_Size (S, First + 3) else 0))
   with Pre => First <= Last + 1 and then Last <= Count (S)
               and then Last + 1 - First <= Ship_Threshold;

   function List_Size (S : Snapshot; Items : Index_List; N : Item_Count)
     return Natural
   is ((if N >= 1 then Item_Size (S, Items (1)) else 0)
       + (if N >= 2 then Item_Size (S, Items (2)) else 0)
       + (if N >= 3 then Item_Size (S, Items (3)) else 0)
       + (if N = 4 then Item_Size (S, Items (4)) else 0))
   with Pre => (N < 1 or else Items (1) <= Count (S))
               and then (N < 2 or else Items (2) <= Count (S))
               and then (N < 3 or else Items (3) <= Count (S))
               and then (N < 4 or else Items (4) <= Count (S));

   --  A plan refers to real elements and has a proper range, and an
   --  ELEMENTS lists at most Ship_Threshold. This function has a
   --  quantifier (HAVE), so its completion is in the private part.
   function Plan_Shape (S : Snapshot; P : Plan) return Boolean with
     Global => null,
     Post   => (if Plan_Shape'Result then
                  Key_Lt (P.Lo, P.Hi)
                  and then (case P.Kind is
                              when P_Range =>
                                P.First <= P.Last + 1 and then P.Last <= Count (S),
                              when P_Elements =>
                                P.First <= P.Last + 1 and then P.Last <= Count (S)
                                and then P.Last + 1 - P.First <= Ship_Threshold,
                              when P_Have =>
                                (P.N < 1 or else P.Items (1) <= Count (S))
                                and then (P.N < 2 or else P.Items (2) <= Count (S))
                                and then (P.N < 3 or else P.Items (3) <= Count (S))
                                and then (P.N < 4 or else P.Items (4) <= Count (S))));

   --  The number of bytes that P takes: an ELEMENTS or a HAVE message, or
   --  (for a RANGE) a one-part RANGE message, an upper bound on its share.
   function Plan_Len (S : Snapshot; P : Plan) return Positive is
     (case P.Kind is
        when P_Range    => Range_Msg_Len (1),
        when P_Elements => Elems_Fixed + Run_Size (S, P.First, P.Last),
        when P_Have     => Elems_Fixed + List_Size (S, P.Items, P.N))
   with Pre => Plan_Shape (S, P);

   --  All the checks of a receiver, and the size bound.
   function Plan_OK (S : Snapshot; P : Plan) return Boolean with
     Global => null,
     Post   => (if Plan_OK'Result then
                  Plan_Shape (S, P) and then Plan_Len (S, P) <= Max_Message_Len);

   subtype Out_Count is Natural range 0 .. Split_Fanout;
   type Plan_Array is array (1 .. Split_Fanout) of Plan;

   --  What to send for one range: the plans P (1 .. N).
   type Outbox is record
      N : Out_Count := 0;
      P : Plan_Array;
   end record;

   --  Every plan is Plan_OK. This function has a quantifier, so its
   --  completion is in the private part.
   function Outbox_OK (S : Snapshot; O : Outbox) return Boolean with
     Global => null;

   procedure Lemma_Outbox_OK (S : Snapshot; O : Outbox; T : Positive) with
     Ghost, Global => null,
     Pre  => Outbox_OK (S, O) and then T <= O.N,
     Post => Plan_OK (S, O.P (T));

   --  The plans of O tile [Lo, Hi): the first starts at Lo, the last ends
   --  at Hi, and each ends where the next starts (S19).
   function Tiles (O : Outbox; Lo, Hi : Elem_Key) return Boolean with
     Global => null;

   --  Every plan of O is of kind K. This function has a quantifier, so its
   --  completion is in the private part.
   function All_Kind (O : Outbox; K : Out_Kind) return Boolean with
     Global => null;

   procedure Lemma_All_Kind (O : Outbox; K : Out_Kind; T : Positive) with
     Ghost, Global => null,
     Pre  => All_Kind (O, K) and then T <= O.N,
     Post => O.P (T).Kind = K;

   --  Every RANGE and ELEMENTS plan of O is exact: its run First .. Last is
   --  our window of its range. This function has a quantifier, so its
   --  completion is in the private part. Lemma_Exact_Plan gives its
   --  meaning.
   function Exact_Plans (S : Snapshot; O : Outbox) return Boolean with
     Global => null,
     Pre    => Valid (S);

   procedure Lemma_Exact_Plan (S : Snapshot; O : Outbox; T : Positive) with
     Ghost, Global => null,
     Pre  => Valid (S) and then Exact_Plans (S, O) and then T <= O.N
             and then O.P (T).Kind /= P_Have,
     Post => Key_Lt (O.P (T).Lo, O.P (T).Hi)
             and then O.P (T).First = Window (S, O.P (T).Lo, O.P (T).Hi).First
             and then O.P (T).Last = Window (S, O.P (T).Lo, O.P (T).Hi).Last
             and then O.P (T).Last + 1 - O.P (T).First
                        = My_Count (S, O.P (T).Lo, O.P (T).Hi);

   --  The explicit confirm: one empty HAVE over [Lo, Hi).
   function Is_Confirm (O : Outbox; Lo, Hi : Elem_Key) return Boolean is
     (O.N = 1 and then O.P (1).Kind = P_Have and then O.P (1).N = 0
      and then O.P (1).Lo = Lo and then O.P (1).Hi = Hi);

   --  The item bytes of one plan: the encoded items of an ELEMENTS or
   --  HAVE (Plan_Len minus the fixed part). A RANGE has none.
   function Plan_Items (S : Snapshot; P : Plan) return Natural is
     (case P.Kind is
        when P_Range    => 0,
        when P_Elements => Run_Size (S, P.First, P.Last),
        when P_Have     => List_Size (S, P.Items, P.N))
   with Pre => Plan_Shape (S, P);

   --  The defining sums over the plans P (1 .. T), with bounded recursion
   --  (T <= Split_Fanout). They are ghost, and their completion is in the
   --  private part.
   function Ranges_Upto (O : Outbox; T : Out_Count) return Out_Count with
     Ghost, Global => null,
     Subprogram_Variant => (Decreases => T),
     Post => Ranges_Upto'Result <= T;

   function Obligations_Upto (O : Outbox; T : Out_Count) return Out_Count with
     Ghost, Global => null,
     Subprogram_Variant => (Decreases => T),
     Post => Obligations_Upto'Result <= T;

   function Items_Upto (S : Snapshot; O : Outbox; T : Out_Count)
     return Byte_Total
   with
     Ghost, Global => null,
     Subprogram_Variant => (Decreases => T),
     Pre  => Outbox_OK (S, O) and then T <= O.N,
     Post => Items_Upto'Result <= Byte_Total (T) * Max_Message_Len;

   --  The number of RANGE plans of O.
   function Num_Ranges (O : Outbox) return Out_Count with
     Global => null,
     Post   => Num_Ranges'Result = Ranges_Upto (O, O.N)
               and then Num_Ranges'Result <= O.N
               and then (if All_Kind (O, P_Range) then Num_Ranges'Result = O.N)
               and then (if All_Kind (O, P_Elements) or else All_Kind (O, P_Have)
                         then Num_Ranges'Result = 0);

   --  The number of obligations (RANGE and ELEMENTS plans) of O.
   function Obligations (O : Outbox) return Out_Count with
     Global => null,
     Post   => Obligations'Result = Obligations_Upto (O, O.N)
               and then Obligations'Result <= O.N
               and then (if All_Kind (O, P_Range) or else All_Kind (O, P_Elements)
                         then Obligations'Result = O.N)
               and then (if All_Kind (O, P_Have) then Obligations'Result = 0);

   --  The item bytes of O: the sum of Plan_Items over its plans.
   function Item_Bytes (S : Snapshot; O : Outbox) return Byte_Total with
     Global => null,
     Pre    => Outbox_OK (S, O),
     Post   => Item_Bytes'Result = Items_Upto (S, O, O.N)
               and then Item_Bytes'Result
                          <= Byte_Total (Split_Fanout * Max_Message_Len)
               and then (if All_Kind (O, P_Range) then Item_Bytes'Result = 0);

   ----------------------------------------------------------------------
   --  Received RANGE part / ROOT / ELEMENTS / HAVE, decoded. Frames stay
   --  in the input buffer. An item records the key that the caller derived
   --  from its frame, the position (Off, absolute index) and the length.
   ----------------------------------------------------------------------

   type Msg_Kind is (M_Hello, M_Range, M_Elements, M_Have);

   type In_Item is record
      Key : Elem_Key;
      Off : Natural    := 0;
      Len : Frame_Size := 1;
   end record;

   type In_Items is array (Item_Index) of In_Item;

   --  The keys of the items of an ELEMENTS / HAVE, as the caller derived
   --  them from the frames: Keys (T) = Key_Of (To_Header (Cid, R)) for the
   --  record R of frame T (Item_Places).
   type Key_List is array (Item_Index) of Elem_Key;

   --  A ROOT is a range message (Kind = M_Range, Root): its bounds are set
   --  by the phase (Bind).
   type Message is record
      Kind   : Msg_Kind   := M_Range;
      Root   : Boolean    := False;
      Lo     : Elem_Key   := Min_Key;
      Hi     : Elem_Key   := Max_Key;
      Count  : Elem_Count := 0;                 --  RANGE part, ROOT
      Fp     : Hash256    := [others => 0];     --  RANGE part, ROOT
      N      : Item_Count := 0;                 --  ELEMENTS, HAVE
      Items  : In_Items;
   end record;

   --  The properties of a decoded message: a proper range, items strictly
   --  ascending in it. This function has a quantifier (the items), so its
   --  completion is in the private part.
   function Msg_OK (M : Message) return Boolean with
     Global => null,
     Post   => (if Msg_OK'Result then
                  M.Kind in M_Range | M_Elements | M_Have
                  and then Key_Lt (M.Lo, M.Hi)
                  and then (if M.Kind = M_Range then M.N = 0)
                  and then (if M.Root then M.Kind = M_Range));

   --  Every frame of M is in Input. This function has a quantifier, so its
   --  completion is in the private part.
   function Msg_In (M : Message; Input : Byte_Array) return Boolean with
     Global => null;

   --  The item keys of M are the caller's Keys. Quantified, private part.
   function Keys_Given (M : Message; Keys : Key_List) return Boolean with
     Global => null;

   --  The head of a RANGE with a part J: its k, its length, J <= k.
   function Range_Head_OK (B : Byte_Array; J : Positive) return Boolean is
     (B'Last >= B'First and then B'Last - B'First >= 1
      and then B (B'First) = Tag_Range
      and then B (B'First + Range_O_K) in 1 .. Split_Fanout
      and then B'Last - B'First = Range_Msg_Len (Natural (B (B'First + Range_O_K))) - 1
      and then J <= Natural (B (B'First + Range_O_K)));

   --  The lo, hi, count and fingerprint of M are those of part J of B.
   function Range_Fields (B : Byte_Array; J : Positive; M : Message) return Boolean is
     (declare
        K : constant Part_Index := Natural (B (B'First + Range_O_K));
      begin
        M.Lo = Wire_Key (B, B'First + Bound_At (J - 1))
        and then M.Hi = Wire_Key (B, B'First + Bound_At (J))
        and then U48 (M.Count) = Wire_U48 (B, B'First + Part_At (K, J))
        and then M.Fp = B (B'First + Part_At (K, J) + Count_Len
                           .. B'First + Part_At (K, J) + Count_Len + 31))
   with Pre => Range_Head_OK (B, J);

   --  A well-formed ROOT (quantifier-free).
   function Root_Wire_OK (B : Byte_Array) return Boolean is
     (B'Last >= B'First and then B'Last - B'First = Root_Len - 1
      and then B (B'First) = Tag_Root
      and then Wire_U48 (B, B'First + Root_O_Count) <= Elem_Max);

   function Root_Fields (B : Byte_Array; M : Message) return Boolean is
     (U48 (M.Count) = Wire_U48 (B, B'First + Root_O_Count)
      and then M.Fp = B (B'First + Root_O_Fp .. B'First + Root_O_Fp + 31))
   with Pre => Root_Wire_OK (B);

   --  A well-formed empty ELEMENTS or HAVE (the confirm; quantifier-free).
   function Empty_Wire_OK (B : Byte_Array) return Boolean is
     (B'Last >= B'First and then B'Last - B'First = Elems_Fixed - 1
      and then (B (B'First) = Tag_Elements or else B (B'First) = Tag_Have)
      and then Key_Lt (Wire_Key (B, B'First + O_Lo), Wire_Key (B, B'First + O_Hi))
      and then Wire_U16 (B, B'First + Elems_O_N) = 0);

   --  What Decode states about its result (M, OK) for part Part of Input,
   --  with the item keys Keys. When Decode accepts:
   --    * M is well-formed and its frames are in Input;
   --    * a RANGE part: the head is well-formed and the fields of M are
   --      those of the part;
   --    * a ROOT: its count and fingerprint, bounds Min_Key .. Max_Key
   --      until Bind sets them by phase;
   --    * an ELEMENTS / HAVE: its kind, lo, hi and n from the wire, its
   --      item keys from Keys.
   --  Completeness: Decode accepts every well-formed ROOT and confirm.
   function Decode_Facts
     (Input : Byte_Array; Part : Positive; Keys : Key_List; M : Message; OK : Boolean)
      return Boolean
   is
     ((if OK then
         Msg_OK (M) and then Msg_In (M, Input)
         and then Input'Last >= Input'First
         and then (if Input (Input'First) = Tag_Range then
                     Range_Head_OK (Input, Part)
                     and then M.Kind = M_Range and then not M.Root
                     and then Range_Fields (Input, Part, M)
                   elsif Input (Input'First) = Tag_Root then
                     Root_Wire_OK (Input) and then Part = 1
                     and then M.Kind = M_Range and then M.Root
                     and then M.Lo = Min_Key and then M.Hi = Max_Key
                     and then Root_Fields (Input, M)
                   else
                     (Input (Input'First) = Tag_Elements
                      or else Input (Input'First) = Tag_Have)
                     and then Part = 1
                     and then Input'Last - Input'First >= Elems_Fixed - 1
                     and then not M.Root
                     and then M.Kind = (if Input (Input'First) = Tag_Elements
                                        then M_Elements else M_Have)
                     and then M.Lo = Wire_Key (Input, Input'First + O_Lo)
                     and then M.Hi = Wire_Key (Input, Input'First + O_Hi)
                     and then M.N = Wire_U16 (Input, Input'First + Elems_O_N)
                     and then Keys_Given (M, Keys)))
      and then (if Root_Wire_OK (Input) and then Part = 1 then
                  OK and then M.Root and then Root_Fields (Input, M))
      and then (if Empty_Wire_OK (Input) and then Part = 1 then
                  OK and then M.N = 0 and then not M.Root
                  and then M.Kind = (if Input (Input'First) = Tag_Elements
                                     then M_Elements else M_Have)));

   --  Decode, as a function of the input (so a contract can name the one
   --  message that an input decodes to).
   type Decoding is record
      M  : Message;
      OK : Boolean := False;
   end record;

   function Decode_Of (Input : Byte_Array; Part : Positive; Keys : Key_List)
     return Decoding
   with
     Global => null,
     Post   => Decode_Facts (Input, Part, Keys, Decode_Of'Result.M, Decode_Of'Result.OK);

   --  The frame places of an ELEMENTS / HAVE (for the caller, which
   --  decodes each frame to its key before Receive): N items, item T at
   --  Input (Off (T) .. Off (T) + Len (T) - 1). OK when the item lengths
   --  add up to the message length and n <= Ship_Threshold.
   type Off_List is array (Item_Index) of Natural;
   type Len_List is array (Item_Index) of Frame_Size;
   type Places is record
      OK  : Boolean    := False;
      N   : Item_Count := 0;
      Off : Off_List   := [others => 0];
      Len : Len_List   := [others => 1];
   end record;

   function Item_Places (Input : Byte_Array) return Places with
     Global => null,
     Post   => (if Item_Places'Result.OK then
                  Input'Last >= Input'First
                  and then Input'Last - Input'First >= Elems_Fixed - 1
                  and then Item_Places'Result.N = Wire_U16 (Input, Input'First + Elems_O_N)
                  and then
                  (for all T in 1 .. Item_Places'Result.N =>
                     Item_Places'Result.Off (T) >= Input'First
                     and then Item_Places'Result.Off (T) <= Input'Last
                     and then Input'Last - Item_Places'Result.Off (T)
                                >= Item_Places'Result.Len (T) - 1))
               and then (if Input'Last >= Input'First
                           and then Input'Last - Input'First = Elems_Fixed - 1
                           and then Wire_U16 (Input, Input'First + Elems_O_N) = 0
                         then Item_Places'Result.OK and then Item_Places'Result.N = 0);

   ----------------------------------------------------------------------
   --  HELLO (post-handshake, D13). Canonical: the cred bytes after Cred_Len
   --  and the ceil bytes after Ceil_Len are zero.
   ----------------------------------------------------------------------

   subtype Cred_Count is Natural range 0 .. Cred_Max;
   subtype Cred_Bytes is Byte_Array (0 .. Cred_Max - 1);

   --  Ceil is the ceiling frame (AUDIT.md H12): the frame of the sender's
   --  ceiling-cell roster, or empty. The caller applies it with
   --  Kome.Write.Receive_Ceil (Kome.Store.Put_Ceil) only (see the package
   --  comment).
   type Hello is record
      N_Auth   : Word       := 0;
      N_Data   : Word       := 0;
      Digest   : Hash256    := [others => 0];
      Cred_Len : Cred_Count := 0;
      Cred     : Cred_Bytes := [others => 0];
      Ceil_Len : Cred_Count := 0;
      Ceil     : Cred_Bytes := [others => 0];
   end record;

   Empty_Hello : constant Hello := (others => <>);

   --  B is a well-formed HELLO: tag, cred_len <= Cred_Max, ceil_len <=
   --  Cred_Max and the length that the two give. Quantifier-free.
   function Hello_Wire_OK (B : Byte_Array) return Boolean is
     (B'Last >= B'First
      and then B'Last - B'First >= Hello_Fixed - 1
      and then B (B'First) = Tag_Hello
      and then Wire_U16 (B, B'First + Hello_O_CLen) <= Cred_Max
      and then Wire_U16 (B, B'First + Hello_O_KLen) <= Cred_Max
      and then B'Last - B'First
               = Hello_Fixed - 1 + Wire_U16 (B, B'First + Hello_O_CLen)
                 + Wire_U16 (B, B'First + Hello_O_KLen));

   procedure Encode_Hello
     (N_Auth, N_Data : Word;
      Digest         : Hash256;
      Cred           : Byte_Array;
      Ceil           : Byte_Array;
      Buf            : out Msg_Buffer;
      Len            : out Msg_Length)
   with
     Global => null,
     Pre    => Cred'Length <= Cred_Max and then Ceil'Length <= Cred_Max,
     Post   => Len = Hello_Fixed + Cred'Length + Ceil'Length and then Len <= Hello_Max_Len
               and then Hello_Wire_OK (Buf (0 .. Len - 1))
               and then Wire_U32 (Buf, Hello_O_NAuth) = N_Auth
               and then Wire_U32 (Buf, Hello_O_NData) = N_Data
               and then Buf (Hello_O_Digest .. Hello_O_Digest + 31) = Digest
               and then Wire_U16 (Buf, Hello_O_CLen) = Cred'Length
               and then Wire_U16 (Buf, Hello_O_KLen) = Ceil'Length
               and then Buf (Hello_Fixed .. Hello_Fixed + Cred'Length - 1) = Cred
               and then Buf (Hello_Fixed + Cred'Length .. Len - 1) = Ceil;

   --  The cred bytes of H after Cred_Len and the ceil bytes after Ceil_Len
   --  are zero. This function has a quantifier, so its completion is in the
   --  private part (rule 2).
   function Cred_Canonical (H : Hello) return Boolean with
     Global => null;

   procedure Lemma_Cred_Zero (H : Hello; I : Natural) with
     Ghost, Global => null,
     Pre  => Cred_Canonical (H) and then I >= H.Cred_Len and then I <= Cred_Max - 1,
     Post => H.Cred (I) = 0;

   procedure Lemma_Ceil_Zero (H : Hello; I : Natural) with
     Ghost, Global => null,
     Pre  => Cred_Canonical (H) and then I >= H.Ceil_Len and then I <= Cred_Max - 1,
     Post => H.Ceil (I) = 0;

   --  The cred bytes of the well-formed HELLO B (an empty slice when
   --  cred_len = 0, written so that no bound overflows: with cred_len > 0
   --  both bounds are at most B'Last).
   function Cred_Of (B : Byte_Array) return Byte_Array is
     (if Wire_U16 (B, B'First + Hello_O_CLen) = 0 then B (B'First .. B'First - 1)
      else B (B'First + Hello_Fixed
              .. B'First + (Hello_Fixed - 1) + Wire_U16 (B, B'First + Hello_O_CLen)))
   with Pre => Hello_Wire_OK (B);

   --  The ceil bytes of the well-formed HELLO B: its last ceil_len bytes (an
   --  empty slice when ceil_len = 0; the bounds are counted from B'Last, so
   --  none overflows). (The name avoids Kome.Headers.Ceil_Of.)
   function Hello_Ceil_Of (B : Byte_Array) return Byte_Array is
     (if Wire_U16 (B, B'First + Hello_O_KLen) = 0 then B (B'First .. B'First - 1)
      else B (B'Last - (Wire_U16 (B, B'First + Hello_O_KLen) - 1) .. B'Last))
   with Pre => Hello_Wire_OK (B);

   --  H is the HELLO that the well-formed B carries, canonically.
   function Hello_Decoded (B : Byte_Array; H : Hello) return Boolean is
     (H.N_Auth = Wire_U32 (B, B'First + Hello_O_NAuth)
      and then H.N_Data = Wire_U32 (B, B'First + Hello_O_NData)
      and then H.Digest = B (B'First + Hello_O_Digest .. B'First + Hello_O_Digest + 31)
      and then H.Cred_Len = Wire_U16 (B, B'First + Hello_O_CLen)
      and then (if H.Cred_Len > 0 then H.Cred (0 .. H.Cred_Len - 1) = Cred_Of (B))
      and then H.Ceil_Len = Wire_U16 (B, B'First + Hello_O_KLen)
      and then (if H.Ceil_Len > 0 then H.Ceil (0 .. H.Ceil_Len - 1) = Hello_Ceil_Of (B))
      and then Cred_Canonical (H))
   with Pre => Hello_Wire_OK (B);

   --  Decode_Hello accepts exactly the well-formed HELLOs.
   procedure Decode_Hello
     (Input : Byte_Array;
      H     : out Hello;
      OK    : out Boolean)
   with
     Global => null,
     Post   => OK = Hello_Wire_OK (Input)
               and then (if OK then Hello_Decoded (Input, H));

   --  The signer of a ROSTER frame (its signer field, as the lattice sees
   --  it: Kome.Records.Signer_Key of the parsed roster).
   function Cred_Signer (Cred : Byte_Array) return Key256 is
     (Kome.Keys.To_Key256
        (Cred (Cred'First + Kome.Records.Roster_O_Signer
               .. Cred'First + Kome.Records.Roster_O_Signer + Pubkey_Len - 1)))
   with Pre => Kome.Records.Is_Roster_Frame (Cred);

   --  The credential check of Receive (AUDIT.md A13, G12): a ROSTER frame
   --  that lists DH, the Noise static key of the peer, and whose signer
   --  is not root-voided in F.
   function Cred_Admissible
     (F : Kome.Frontier.State; DH : Pubkey; Cred : Byte_Array) return Boolean
   is (Kome.Records.Is_Roster_Frame (Cred)
       and then Kome.Records.Roster_Lists_DH (Cred, DH)
       and then not Kome.Views.Root_Void (F, Cred_Signer (Cred)));

   --  A claimed count, as it goes into the budgets: min (claimed,
   --  Elem_Max).
   function Claim (W : Word) return Elem_Count is
     (if W > Elem_Max then Elem_Max else Natural (W));

   ----------------------------------------------------------------------
   --  ROOT (S19).
   ----------------------------------------------------------------------

   --  A ROOT to send: the count and fingerprint of the range of the phase.
   type Root_Out is record
      Send  : Boolean    := False;
      Count : Elem_Count := 0;
      Fp    : Hash256    := [others => 0];
   end record;

   No_Root : constant Root_Out := (others => <>);

   procedure Encode_Root
     (R   : Root_Out;
      Buf : out Msg_Buffer;
      Len : out Msg_Length)
   with
     Global => null,
     Post   => Len = Root_Len
               and then Root_Wire_OK (Buf (0 .. Len - 1))
               and then Wire_U48 (Buf, Root_O_Count) = U48 (R.Count)
               and then Buf (Root_O_Fp .. Root_O_Fp + 31) = R.Fp;

   --  The fingerprint of the union of two digest states (the HELLO
   --  digest: the authorization and data states of the store, S21).
   function Total_Fp (A, D : Kome.Digest.Digest_State) return Hash256 is
     (Kome.Digest.Fp (Kome.Digest.Count (A) + Kome.Digest.Count (D),
                      Kome.Accumulator.Add (Kome.Digest.Sum (A), Kome.Digest.Sum (D))))
   with Pre => Kome.Digest.Count (A) + Kome.Digest.Count (D) <= Elem_Max;

   ----------------------------------------------------------------------
   --  Encode ELEMENTS / HAVE and RANGE. No message is longer than
   --  Max_Message_Len bytes (T13, the bounds obligation, for messages).
   ----------------------------------------------------------------------

   --  One ELEMENTS or HAVE plan. T holds the frames (Linked).
   procedure Encode
     (S   : Snapshot;
      T   : Frame_Table;
      P   : Plan;
      Buf : out Msg_Buffer;
      Len : out Msg_Length)
   with
     Global => null,
     Pre    => Valid (S) and then Table_Valid (T) and then Linked (S, T)
               and then Plan_OK (S, P) and then P.Kind /= P_Range,
     Post   => Len = Plan_Len (S, P)
               and then Buf (0) = (if P.Kind = P_Elements then Tag_Elements else Tag_Have)
               and then Wire_Key (Buf, O_Lo) = P.Lo
               and then Wire_Key (Buf, O_Hi) = P.Hi
               and then Wire_U16 (Buf, Elems_O_N)
                          = (if P.Kind = P_Elements then P.Last + 1 - P.First else P.N);

   --  The RANGE plans of O, which tile a range, as one RANGE message with
   --  O.N parts. PS is the prefix-sum table of S (the parts carry
   --  fingerprints).
   procedure Encode_Ranges
     (S   : Snapshot;
      PS  : Prefix;
      O   : Outbox;
      Buf : out Msg_Buffer;
      Len : out Msg_Length)
   with
     Global => null,
     Pre    => Valid (S) and then Sealed (S, PS) and then Outbox_OK (S, O)
               and then O.N >= 1 and then All_Kind (O, P_Range)
               and then Tiles (O, O.P (1).Lo, O.P (O.N).Hi),
     Post   => Len = Range_Msg_Len (O.N)
               and then Buf (0) = Tag_Range
               and then Natural (Buf (Range_O_K)) = O.N;

   --  The round trip for the confirm: Decode accepts what Encode emits.
   procedure Lemma_Confirm_Accepted (S : Snapshot; P : Plan; Buf : Msg_Buffer) with
     Ghost, Global => null,
     Pre  => Valid (S) and then Plan_OK (S, P) and then P.Kind = P_Have
             and then P.N = 0
             and then Buf (0) = Tag_Have
             and then Wire_Key (Buf, O_Lo) = P.Lo
             and then Wire_Key (Buf, O_Hi) = P.Hi
             and then Wire_U16 (Buf, Elems_O_N) = 0,
     Post => Empty_Wire_OK (Buf (0 .. Elems_Fixed - 1));

   ----------------------------------------------------------------------
   --  The responder.
   ----------------------------------------------------------------------

   --  The items of a message that go to the caller.
   type Delivery is array (Item_Index) of Boolean;
   No_Delivery : constant Delivery := [others => False];

   --  K is one of our elements. This function has a quantifier, so its
   --  completion is in the private part.
   function Held (S : Snapshot; K : Elem_Key) return Boolean with
     Global => null;

   --  D delivers exactly the items of M that we do not hold. This function
   --  has a quantifier, so its completion is in the private part.
   function Delivers (S : Snapshot; M : Message; D : Delivery) return Boolean with
     Global => null;

   --  Our count and fingerprint over [M.Lo, M.Hi) are those of M.
   function Confirms (S : Snapshot; M : Message) return Boolean is
     (Window (S, M.Lo, M.Hi).Last + 1 - Window (S, M.Lo, M.Hi).First = M.Count
      and then Range_Fp (S, Window (S, M.Lo, M.Hi).First,
                            Window (S, M.Lo, M.Hi).Last) = M.Fp)
   with Pre => Valid (S) and then Key_Lt (M.Lo, M.Hi);

   --  O is the exact HAVE answer to M: HAVEs that tile [M.Lo, M.Hi), that
   --  offer only our elements that M does not list, and that offer each
   --  such element of ours in the range. This function has a quantifier,
   --  so its completion is in the private part.
   function Have_Exact (S : Snapshot; M : Message; O : Outbox) return Boolean with
     Global => null;

   --  Every RANGE in O is a sub-range of M's range, with strictly
   --  fewer of our elements (the measure of T7). Ghost, private part.
   function Shrinks (S : Snapshot; M : Message; O : Outbox) return Boolean with
     Ghost, Global => null,
     Pre => Valid (S) and then Key_Lt (M.Lo, M.Hi);

   --  The reply contract (DESIGN.md §8 "Replies"):
   --    RANGE part or ROOT, equal count and fingerprint: the confirm.
   --    RANGE part or ROOT, in other cases: plans that tile the range,
   --      every plan exact; all ELEMENTS if we hold at most Ship_Threshold
   --      in the range, else all RANGE children (each strictly smaller).
   --    ELEMENTS: the exact HAVE if we hold at most Ship_Threshold. If
   --      not, the exact split above.
   --    HAVE: no reply.
   function Answers (S : Snapshot; M : Message; O : Outbox) return Boolean is
     ((if M.Kind = M_Have then O.N = 0 else O.N >= 1)
      and then (if M.Kind = M_Range then
                  (if Confirms (S, M) then Is_Confirm (O, M.Lo, M.Hi)
                   else Tiles (O, M.Lo, M.Hi) and then Exact_Plans (S, O)
                        and then (if My_Count (S, M.Lo, M.Hi) <= Ship_Threshold
                                  then All_Kind (O, P_Elements)
                                  else All_Kind (O, P_Range))))
      and then (if M.Kind = M_Elements then
                  (if My_Count (S, M.Lo, M.Hi) <= Ship_Threshold
                   then Have_Exact (S, M, O)
                   else Tiles (O, M.Lo, M.Hi) and then Exact_Plans (S, O)
                        and then All_Kind (O, P_Range))))
   with Ghost, Pre => Valid (S) and then Msg_OK (M);

   --  Respond, as a function of the snapshot and the message.
   type Reply is record
      Box : Outbox;
      Got : Delivery := No_Delivery;
   end record;

   --  The reply, given the fingerprint of our window of M as a key (a
   --  record of words, so that equal fingerprints give equal replies in
   --  the logic; CONVENTIONS.md rule 1). FPK must be that fingerprint.
   function Reply_Core (S : Snapshot; M : Message; FPK : Key256) return Reply with
     Global => null,
     Pre    => Valid (S) and then Msg_OK (M)
               and then FPK = Kome.Keys.To_Key256
                                (Range_Fp (S, Window (S, M.Lo, M.Hi).First,
                                              Window (S, M.Lo, M.Hi).Last)),
     Post   => Outbox_OK (S, Reply_Core'Result.Box)
       and then Delivers (S, M, Reply_Core'Result.Got)
       and then Answers (S, M, Reply_Core'Result.Box)
       and then Shrinks (S, M, Reply_Core'Result.Box);

   function Reply_Of (S : Snapshot; M : Message) return Reply with
     Global => null,
     Pre    => Valid (S) and then Msg_OK (M),
     Post   => Reply_Of'Result
                 = Reply_Core (S, M, Kome.Keys.To_Key256
                                       (Range_Fp (S, Window (S, M.Lo, M.Hi).First,
                                                     Window (S, M.Lo, M.Hi).Last)))
       and then Outbox_OK (S, Reply_Of'Result.Box)
       and then Delivers (S, M, Reply_Of'Result.Got)
       and then Answers (S, M, Reply_Of'Result.Box)
       and then Shrinks (S, M, Reply_Of'Result.Box);

   --  Respond computes the fingerprint from the prefix sums (D15), so it
   --  takes the table P of S. Its reply is Reply_Of.
   procedure Respond
     (S       : Snapshot;
      P       : Prefix;
      M       : Message;
      Out_Box : out Outbox;
      Got     : out Delivery)
   with
     Global => null,
     Pre    => Valid (S) and then Sealed (S, P) and then Msg_OK (M),
     Post   => Out_Box = Reply_Of (S, M).Box and then Got = Reply_Of (S, M).Got
       and then Outbox_OK (S, Out_Box)
       and then Delivers (S, M, Got)
       and then Answers (S, M, Out_Box)
       and then Shrinks (S, M, Out_Box);

   ----------------------------------------------------------------------
   --  The session state machine.
   ----------------------------------------------------------------------

   type Role  is (Initiator, Responder);
   type Phase is (Gate, Auth, Data, Done);

   Session_Msgs_Max : constant := 2 ** 29;
   subtype Msg_Counter is Natural range 0 .. Session_Msgs_Max;

   --  In a session, an honest peer sends at most these logical messages
   --  (a RANGE part counts as one):
   --    * its HELLO;
   --    * in each phase, its ROOT and one answer (<= 16 messages or parts)
   --      for each obligation that we send in that phase.
   --  Our obligations in a phase are our RANGE parts and our ELEMENTS.
   --  Our RANGE parts are <= 2 N_ours + 1: a laminar family of ranges with
   --  distinct non-empty sets of our elements, plus the root. Our ELEMENTS
   --  are <= 4 for each RANGE part of the peer, so <= 4 (2 N_peer + 1). So
   --  one phase costs at most
   --  1 + 16 (2 N_ours + 1 + 4 (2 N_peer + 1)) = 128 N_peer + 32 N_ours + 81.
   --  The session costs at most 2 × (128 N_peer + 32 N_ours + 81) + 1.
   function Msg_Budget (Ours, Theirs : Elem_Count) return Msg_Counter is
     (256 * Theirs + 64 * Ours + 163);

   --  Before the HELLO exchange: the HELLO of the peer.
   Pre_Gate_Budget : constant := 1;

   --  The RANGE parts that we emit in replies, over the two phases (the
   --  count does not include the ROOTs). Each phase has at most 2 |S| + 2.
   Range_Max : constant := 2 * (2 * Elem_Max + 2);
   subtype Range_Counter is Natural range 0 .. Range_Max;

   function Range_Budget (S : Snapshot) return Range_Counter is
     (2 * (2 * Count (S) + 2));

   --  The item bytes that we emit, over the two phases. Each phase has at
   --  most 8 × (frame bytes + 2 |S|).
   Ship_Factor : constant := 2 * 8;

   function Ship_Budget (S : Snapshot) return Byte_Total is
     (Ship_Factor * (Frame_Bytes (S) + Item_Overhead * Byte_Total (Count (S))));

   --  An open obligation: a range [Lo, Hi) that we asked about (a RANGE
   --  part or an ELEMENTS that we sent, or a ROOT). Next is where the next
   --  message of its tiling answer starts (S19).
   type Oblig is record
      Lo   : Elem_Key := Min_Key;
      Hi   : Elem_Key := Max_Key;
      Next : Elem_Key := Min_Key;
   end record;

   function Fresh (Lo, Hi : Elem_Key) return Oblig is
     ((Lo => Lo, Hi => Hi, Next => Lo));

   --  The head after the message M of its answer (not the last one).
   function Advanced (H : Oblig; M : Message) return Oblig is
     ((Lo => H.Lo, Hi => H.Hi, Next => M.Hi));

   Oblig_Max : constant := Range_Max;
   subtype Oblig_Count is Natural range 0 .. Oblig_Max;
   subtype Oblig_Cap_Range is Positive range 1 .. Oblig_Max;
   type Oblig_Array is array (Positive range <>) of Oblig;

   --  The FIFO is a ring of Oblig_Cap entries: Q_Head is the slot of the
   --  head, and Q_Len the number of open obligations.
   type Session (Oblig_Cap : Oblig_Cap_Range) is record
      R               : Role          := Responder;
      P               : Phase         := Gate;
      Cid             : Hash256       := [others => 0];  --  our collection
      Peer_DH         : Pubkey        := [others => 0];  --  the peer's Noise static key
      Aborted         : Boolean       := False; --  ended by a bad credential
                                                --  or a closed gate
      Hello_Sent      : Boolean       := False; --  Admit emitted our HELLO
      Peer_Hello_Seen : Boolean       := False; --  peer HELLO arrived
      Auth_Root_Seen  : Boolean       := False; --  the authorization ROOT went
                                                --  out (initiator) / came in
                                                --  (responder)
      Our_N           : Elem_Count    := 0;     --  n_auth + n_data of our HELLO
      Our_Digest      : Key256;                 --  digest of our HELLO
      Our_Auth_N      : Elem_Count    := 0;     --  n_auth of our HELLO
      Our_Auth_Fp     : Hash256       := [others => 0];  --  fp of our auth range
      Peer_Auth       : Elem_Count    := 0;     --  min (n_auth, Elem_Max)
      Peer_Data       : Elem_Count    := 0;     --  min (n_data, Elem_Max)
      Peer_Digest     : Key256;                 --  digest of the peer HELLO
      Msgs            : Msg_Counter   := 0;     --  messages accepted
      Budget          : Msg_Counter   := Pre_Gate_Budget;
      Ranges          : Range_Counter := 0;     --  RANGE parts we emitted in replies
      Shipped         : Byte_Total    := 0;     --  item bytes we emitted
      Q               : Oblig_Array (1 .. Oblig_Cap);
      Q_Head          : Positive      := 1;
      Q_Len           : Oblig_Count   := 0;
   end record;

   --  The slot of open obligation K (1 = the head).
   function Slot (Sess : Session; K : Positive) return Positive is
     (if Sess.Q_Head + (K - 1) <= Sess.Oblig_Cap then Sess.Q_Head + (K - 1)
      else Sess.Q_Head + (K - 1) - Sess.Oblig_Cap)
   with Pre  => Sess.Q_Head <= Sess.Oblig_Cap and then K <= Sess.Oblig_Cap,
        Post => Slot'Result in 1 .. Sess.Oblig_Cap;

   function Open_Count (Sess : Session) return Oblig_Count is (Sess.Q_Len);

   function Open (Sess : Session; K : Positive) return Oblig is
     (Sess.Q (Slot (Sess, K)))
   with Pre => Sess.Q_Head <= Sess.Oblig_Cap and then Sess.Q_Len <= Sess.Oblig_Cap
               and then K <= Sess.Q_Len;

   function Session_OK (Sess : Session) return Boolean is
     (Sess.Msgs <= Sess.Budget
      and then Sess.Q_Head <= Sess.Oblig_Cap
      and then Sess.Q_Len <= Sess.Oblig_Cap
      and then (if Sess.Aborted then Sess.P = Done)
      and then (if Sess.P = Gate then Sess.Budget = Pre_Gate_Budget)
      and then (case Sess.P is
                  when Gate =>
                    not (Sess.Hello_Sent and then Sess.Peer_Hello_Seen)
                    and then not Sess.Auth_Root_Seen and then Sess.Q_Len = 0,
                  when Auth =>
                    Sess.Hello_Sent and then Sess.Peer_Hello_Seen
                    and then (if Sess.R = Initiator then Sess.Auth_Root_Seen),
                  when Data =>
                    Sess.Hello_Sent and then Sess.Peer_Hello_Seen
                    and then Sess.Auth_Root_Seen,
                  when Done => True));

   --  The session ended without abort. Nothing is open then.
   function Complete (Sess : Session) return Boolean is
     (Sess.P = Done and then not Sess.Aborted);

   --  The claimed element count of the peer, as it goes into the budgets:
   --  min (min (n_auth, Elem_Max) + min (n_data, Elem_Max), Elem_Max).
   function Peer_Claim (Sess : Session) return Elem_Count is
     (if Sess.Peer_Auth + Sess.Peer_Data > Elem_Max then Elem_Max
      else Sess.Peer_Auth + Sess.Peer_Data);

   --  S is the snapshot that our HELLO described: its size and digest are
   --  the values that Admit sent (from the store's digest states). The
   --  caller builds S when the session enters Auth and gives it to every
   --  later Receive and Next_Phase.
   function Same_Snapshot (Sess : Session; S : Snapshot) return Boolean is
     (Count (S) = Sess.Our_N
      and then Sess.Our_Digest = Kome.Keys.To_Key256 (Range_Fp (S, 1, Count (S))))
   with Pre => Valid (S);

   --  The gate (S9): Eff is ROSTER_eff of F in the collection Cid, and
   --  Kome.Guard admits the peer DH (the REVOKE-aware gate, not
   --  quarantined).
   function Gate_Open
     (Cid : Hash256; F : Kome.Frontier.State; Eff : Kome.Records.Roster_Record;
      DH : Pubkey) return Boolean
   is (Kome.Views.Roster_Eff (F) = (Present => True, Hdr => Kome.Records.To_Header (Cid, Eff))
       and then Kome.Guard.Admits (Cid, F, Eff, DH));

   --  The bounds of a ROOT, by phase: the authorization range for the
   --  first, the data range for the second.
   function Root_Lo (Sess : Session) return Elem_Key is
     (if Sess.Auth_Root_Seen then Data_Lo else Min_Key);

   function Root_Hi (Sess : Session) return Elem_Key is
     (if Sess.Auth_Root_Seen then Max_Key else Data_Lo);

   --  A decoded message with the bounds of a ROOT set by the phase.
   function Bind (Sess : Session; M : Message) return Message is
     (if M.Root then (M with delta Lo => Root_Lo (Sess), Hi => Root_Hi (Sess)) else M);

   --  The ROOTs that the responder accepts (D14): the authorization ROOT
   --  before it has one, or the data ROOT after it, with nothing that it
   --  asked open.
   function Root_OK (Sess : Session; M : Message) return Boolean is
     (M.Root and then Sess.R = Responder and then Sess.P = Auth
      and then (not Sess.Auth_Root_Seen or else Sess.Q_Len = 0));

   --  M continues the tiling answer of the head obligation (S19): it
   --  starts where the answer stands (Next) and ends at or before the
   --  head's hi.
   function Matches_Head (Sess : Session; M : Message) return Boolean is
     (Sess.Q_Len >= 1
      and then M.Lo = Open (Sess, 1).Next
      and then Key_Le (M.Hi, Open (Sess, 1).Hi))
   with Pre => Sess.Q_Head <= Sess.Oblig_Cap and then Sess.Q_Len <= Sess.Oblig_Cap;

   --  M is the last message of the head's answer: the head leaves the
   --  FIFO.
   function Group_Done (Sess : Session; M : Message) return Boolean is
     (not M.Root and then Matches_Head (Sess, M) and then M.Hi = Open (Sess, 1).Hi)
   with Pre => Sess.Q_Head <= Sess.Oblig_Cap and then Sess.Q_Len <= Sess.Oblig_Cap;

   --  The FIFO after the accepted message M with the reply O: the head
   --  leaves if its answer is done, or advances by M if it goes on (not
   --  for a ROOT); the rest keep their order; the obligations of O (its
   --  RANGE and ELEMENTS plans, in plan order) are appended. This function
   --  has quantifiers, so its completion is in the body.
   --  Lemma_Queue_Step_Def gives its meaning.
   function Queue_Step (Old, Upd : Session; M : Message; O : Outbox) return Boolean with
     Ghost, Global => null,
     Pre => Old.Q_Head <= Old.Oblig_Cap and then Old.Q_Len <= Old.Oblig_Cap
            and then Upd.Q_Head <= Upd.Oblig_Cap and then Upd.Q_Len <= Upd.Oblig_Cap
            and then Upd.Oblig_Cap = Old.Oblig_Cap
            and then (if not M.Root then Matches_Head (Old, M));

   procedure Lemma_Queue_Step_Def (Old, Upd : Session; M : Message; O : Outbox) with
     Ghost, Global => null,
     Pre  => Old.Q_Head <= Old.Oblig_Cap and then Old.Q_Len <= Old.Oblig_Cap
             and then Upd.Q_Head <= Upd.Oblig_Cap and then Upd.Q_Len <= Upd.Oblig_Cap
             and then Upd.Oblig_Cap = Old.Oblig_Cap
             and then (if not M.Root then Matches_Head (Old, M)),
     Post => Queue_Step (Old, Upd, M, O) =
       (declare
          Pop  : constant Natural := (if Group_Done (Old, M) then 1 else 0);
          Base : constant Natural := Old.Q_Len - Pop;
        begin
          Upd.Q_Len = Base + Obligations (O)
          and then (for all K in 1 .. Base =>
                      Open (Upd, K) = (if Pop = 1 then Open (Old, K + 1)
                                       elsif K = 1 and then not M.Root
                                       then Advanced (Open (Old, 1), M)
                                       else Open (Old, K)))
          and then (for all T in 1 .. O.N =>
                      (if O.P (T).Kind /= P_Have
                         and then Base + Obligations_Upto (O, T) in 1 .. Upd.Q_Len
                       then Open (Upd, Base + Obligations_Upto (O, T))
                              = Fresh (O.P (T).Lo, O.P (T).Hi))));

   --  The state when the two HELLOs have passed. If the digests are equal,
   --  the session ends. If not, the phase is Auth, and the initiator's
   --  authorization ROOT goes out (R) and is open.
   function After_Hellos (Sess : Session; R : Root_Out) return Boolean is
     (Sess.Hello_Sent and then Sess.Peer_Hello_Seen
      and then Sess.Budget = Msg_Budget (Sess.Our_N, Peer_Claim (Sess))
      and then Sess.Q_Head <= Sess.Oblig_Cap and then Sess.Q_Len <= Sess.Oblig_Cap
      and then (if Sess.Our_Digest = Sess.Peer_Digest then
                  Sess.P = Done and then not Sess.Aborted and then not R.Send
                  and then Sess.Q_Len = 0
                elsif Sess.R = Initiator then
                  Sess.P = Auth and then Sess.Auth_Root_Seen
                  and then Sess.Q_Len = 1
                  and then Open (Sess, 1) = Fresh (Min_Key, Data_Lo)
                  and then R.Send and then R.Count = Sess.Our_Auth_N
                  and then R.Fp = Sess.Our_Auth_Fp
                else
                  Sess.P = Auth and then not Sess.Auth_Root_Seen
                  and then Sess.Q_Len = 0 and then not R.Send));

   --  Start a session with the peer whose Noise static key is Peer_DH, in
   --  the collection Cid (after the Noise XK handshake with Prologue
   --  (Cid)). Nothing goes out: Admit sends our HELLO once the gate admits
   --  the peer (the peer's HELLO credential may have to come first, S11).
   procedure Start
     (Sess    : out Session;
      As      : Role;
      Cid     : Hash256;
      Peer_DH : Pubkey)
   with
     Global => null,
     Post   => Session_OK (Sess) and then Sess.R = As and then Sess.Cid = Cid
               and then Sess.Peer_DH = Peer_DH
               and then Sess.P = Gate and then not Sess.Aborted
               and then not Sess.Hello_Sent and then not Sess.Peer_Hello_Seen
               and then Sess.Msgs = 0 and then Sess.Q_Len = 0
               and then Sess.Budget = Pre_Gate_Budget
               and then Sess.Ranges = 0 and then Sess.Shipped = 0;

   --  The sender duty for the ceiling frame (AUDIT.md H12; the package
   --  comment): Ceil is the frame of the roster in the ceiling cell of F
   --  when the cell is live (Kome.Frontier.Ceil_Live), and empty
   --  otherwise. "The frame of" is: a ROSTER frame whose lattice header in
   --  the collection of Cid is the cell's record. Admit has it as a
   --  precondition, so a caller cannot leave out a live cell (then two
   --  replicas with equal rows would end the session at the HELLOs with
   --  different maxceil), and cannot send another roster in its place. The
   --  store gives the frame and the facts: Kome.Store.Read_Frame at
   --  Tag_Off (Ceil_Tag (F)), with Lemma_Ceil_Tag and Lemma_Header_Of.
   function Ceil_Frame_OK
     (Cid : Hash256; F : Kome.Frontier.State; Ceil : Byte_Array) return Boolean
   is (if Kome.Frontier.Ceil_Live (F)
       then Kome.Records.Is_Roster_Frame (Ceil)
            and then Kome.Records.To_Header (Cid, Kome.Records.Parse_Roster (Ceil))
                     = Kome.Frontier.Ceil_Held (F)
       else Ceil'Length = 0);

   --  Our HELLO, when the gate admits the peer (the precondition, A13,
   --  S9). The HELLO carries the counts of the two digest states, the
   --  fingerprint of their union, our credential (S21: no snapshot) and
   --  Ceil, the frame of our ceiling-cell roster when the cell is live
   --  (Kome.Frontier.Ceil_Live), else empty (the precondition
   --  Ceil_Frame_OK; AUDIT.md H12).
   --  Admit writes it to Buf (0 .. Len - 1). Send it before Root. If the
   --  HELLO of the peer is already here, the HELLO exchange is over
   --  (After_Hellos; the initiator's ROOT is in Root).
   procedure Admit
     (Sess     : in out Session;
      F        : Kome.Frontier.State;
      Eff      : Kome.Records.Roster_Record;
      Auth     : Kome.Digest.Digest_State;
      Data     : Kome.Digest.Digest_State;
      Cred     : Byte_Array;
      Ceil     : Byte_Array;
      Buf      : out Msg_Buffer;
      Len      : out Msg_Length;
      Root     : out Root_Out)
   with
     Global => null,
     Pre    => Session_OK (Sess)
               and then Sess.P = Gate and then not Sess.Hello_Sent
               and then Cred'Length <= Cred_Max
               and then Ceil'Length <= Cred_Max
               and then Ceil_Frame_OK (Sess.Cid, F, Ceil)
               and then Kome.Digest.Count (Auth) + Kome.Digest.Count (Data) <= Elem_Max
               and then Gate_Open (Sess.Cid, F, Eff, Sess.Peer_DH),
     Post   => Session_OK (Sess)
               and then Sess = (Sess'Old with delta
                                  Hello_Sent     => True,
                                  Our_N          => Sess.Our_N,
                                  Our_Digest     => Sess.Our_Digest,
                                  Our_Auth_N     => Sess.Our_Auth_N,
                                  Our_Auth_Fp    => Sess.Our_Auth_Fp,
                                  P              => Sess.P,
                                  Budget         => Sess.Budget,
                                  Q              => Sess.Q,
                                  Q_Len          => Sess.Q_Len,
                                  Auth_Root_Seen => Sess.Auth_Root_Seen)
               and then Sess.Our_N = Kome.Digest.Count (Auth) + Kome.Digest.Count (Data)
               and then Sess.Our_Digest = Kome.Keys.To_Key256 (Total_Fp (Auth, Data))
               and then Sess.Our_Auth_N = Kome.Digest.Count (Auth)
               and then Sess.Our_Auth_Fp = Kome.Digest.Fingerprint (Auth)
               and then Len = Hello_Fixed + Cred'Length + Ceil'Length
               and then Len <= Hello_Max_Len
               and then Hello_Wire_OK (Buf (0 .. Len - 1))
               and then Wire_U32 (Buf, Hello_O_NAuth) = Word (Kome.Digest.Count (Auth))
               and then Wire_U32 (Buf, Hello_O_NData) = Word (Kome.Digest.Count (Data))
               and then Buf (Hello_O_Digest .. Hello_O_Digest + 31) = Total_Fp (Auth, Data)
               and then Wire_U16 (Buf, Hello_O_KLen) = Ceil'Length
               and then Buf (Hello_Fixed .. Hello_Fixed + Cred'Length - 1) = Cred
               and then Buf (Hello_Fixed + Cred'Length .. Len - 1) = Ceil
               and then (if Sess.Peer_Hello_Seen then After_Hellos (Sess, Root)
                         else Sess.P = Gate and then not Root.Send
                              and then Sess.Budget = Sess'Old.Budget
                              and then Sess.Q_Len = 0);

   type Session_Status is
     (S_OK,
      S_Malformed,     --  the bytes are not a message
      S_Unexpected,    --  a message this phase or our open obligations do not accept
      S_Limit,         --  a session budget would be exceeded
      S_Aborted);      --  the session is over (Done, Aborted): a HELLO with an
                       --  inadmissible credential, or the gate is closed

   --  The initiator, with nothing open in Auth: the data ROOT, after the
   --  gate check (S9). If the gate is closed, the session aborts
   --  (S_Aborted) and nothing goes out.
   procedure Next_Phase
     (Sess     : in out Session;
      S        : Snapshot;
      P        : Prefix;
      F        : Kome.Frontier.State;
      Eff      : Kome.Records.Roster_Record;
      Root     : out Root_Out;
      Result   : out Session_Status)
   with
     Global => null,
     Pre    => Valid (S) and then Sealed (S, P) and then Session_OK (Sess)
               and then Sess.R = Initiator and then Sess.P = Auth
               and then Sess.Q_Len = 0 and then Same_Snapshot (Sess, S),
     Post   => Session_OK (Sess)
               and then Result in S_OK | S_Aborted
               and then (Result = S_OK) = Gate_Open (Sess'Old.Cid, F, Eff, Sess'Old.Peer_DH)
               and then (if Result = S_OK then
                           Root.Send
                           and then Root.Count = My_Count (S, Data_Lo, Max_Key)
                           and then Root.Fp = Range_Fp (S, Window (S, Data_Lo, Max_Key).First,
                                                           Window (S, Data_Lo, Max_Key).Last)
                           and then Sess = (Sess'Old with delta
                                              P => Data, Q => Sess.Q, Q_Len => 1)
                           and then Open (Sess, 1) = Fresh (Data_Lo, Max_Key)
                         else
                           not Root.Send
                           and then Sess = (Sess'Old with delta P => Done, Aborted => True));

   --  Receive can accept M: a ROOT only as the expected one (Root_OK),
   --  any other message only as the next tile of the answer to our head
   --  obligation (Matches_Head).
   function Root_Or_Owed (Sess : Session; M : Message) return Boolean is
     (if M.Root then Root_OK (Sess, M) else Matches_Head (Sess, M))
   with Pre => Sess.Q_Head <= Sess.Oblig_Cap and then Sess.Q_Len <= Sess.Oblig_Cap;

   --  The answer O to M stays within the budgets of the session, and its
   --  obligations fit the FIFO.
   function Within_Budgets
     (Sess : Session; S : Snapshot; M : Message; O : Outbox) return Boolean
   is
     (Sess.Ranges + Num_Ranges (O) <= Range_Budget (S)
      and then Sess.Shipped + Item_Bytes (S, O) <= Ship_Budget (S)
      and then Sess.Q_Len - (if Group_Done (Sess, M) then 1 else 0)
                 + Obligations (O) <= Sess.Oblig_Cap)
   with Pre => Valid (S) and then Outbox_OK (S, O)
               and then Sess.Q_Head <= Sess.Oblig_Cap and then Sess.Q_Len <= Sess.Oblig_Cap
               and then Root_Or_Owed (Sess, M);

   --  The exact status that Receive returns, as a function of the session,
   --  the snapshot, the frontier, Eff and the input (with its part and
   --  item keys).
   function Status_Of
     (Sess     : Session;
      S        : Snapshot;
      F        : Kome.Frontier.State;
      Eff      : Kome.Records.Roster_Record;
      Input    : Byte_Array;
      Part     : Positive;
      Keys     : Key_List) return Session_Status
   is
     (if Sess.P = Done then S_Unexpected
      elsif Input'Last < Input'First then S_Malformed
      elsif Input (Input'First) = Tag_Hello then
        (if Sess.P /= Gate or else Sess.Peer_Hello_Seen then S_Unexpected
         elsif Sess.Msgs = Sess.Budget then S_Limit
         elsif not Hello_Wire_OK (Input) then S_Malformed
         elsif not Cred_Admissible (F, Sess.Peer_DH, Cred_Of (Input)) then S_Aborted
         else S_OK)
      elsif Sess.P not in Auth | Data then S_Unexpected
      elsif not Gate_Open (Sess.Cid, F, Eff, Sess.Peer_DH) then S_Aborted
      elsif Sess.Msgs = Sess.Budget then S_Limit
      elsif not Decode_Of (Input, Part, Keys).OK then S_Malformed
      elsif not Root_Or_Owed (Sess, Bind (Sess, Decode_Of (Input, Part, Keys).M))
      then S_Unexpected
      elsif not Within_Budgets
                  (Sess, S, Bind (Sess, Decode_Of (Input, Part, Keys).M),
                   Reply_Of (S, Bind (Sess, Decode_Of (Input, Part, Keys).M)).Box)
      then S_Limit
      else S_OK)
   with Pre => Valid (S)
               and then Sess.Q_Head <= Sess.Oblig_Cap and then Sess.Q_Len <= Sess.Oblig_Cap;

   --  Receive one logical message: Input with its part (for a RANGE, the
   --  part 1 .. k; else 1) and the item keys that the caller derived from
   --  the frames (Item_Places). The status is exactly Status_Of. On
   --  S_Malformed, S_Unexpected and S_Limit, nothing changes. Receive
   --  delivers and offers elements only in Auth and Data, and only the
   --  HELLO exchange gets to these phases. M is the decoded message with
   --  the bounds of a ROOT set by the phase (Bind), and the reply is
   --  Reply_Of (S, M). Peer is the decoded HELLO, from the wire; it is
   --  Empty_Hello when the HELLO is refused (its credential and its ceiling
   --  frame are not returned). Root is the initiator's authorization ROOT
   --  when this HELLO completes the exchange.
   procedure Receive
     (Sess       : in out Session;
      S          : Snapshot;
      P          : Prefix;
      F          : Kome.Frontier.State;
      Eff        : Kome.Records.Roster_Record;
      Input      : Byte_Array;
      Part       : Positive;
      Keys       : Key_List;
      M          : out Message;
      Peer       : out Hello;
      Out_Box    : out Outbox;
      Got        : out Delivery;
      Root       : out Root_Out;
      Result     : out Session_Status)
   with
     Global => null,
     Pre    => Valid (S) and then Session_OK (Sess)
               and then (if Sess.P in Auth | Data then Same_Snapshot (Sess, S)
                                                       and then Sealed (S, P)),
     Post   => Session_OK (Sess)
       and then Result = Status_Of (Sess'Old, S, F, Eff, Input, Part, Keys)
       and then Sess.R = Sess'Old.R and then Sess.Cid = Sess'Old.Cid
       and then Sess.Peer_DH = Sess'Old.Peer_DH
       and then Sess.Our_N = Sess'Old.Our_N
       and then Sess.Our_Digest = Sess'Old.Our_Digest
       and then Outbox_OK (S, Out_Box)
       and then (if Result in S_Malformed | S_Unexpected | S_Limit then
                   Sess = Sess'Old and then Out_Box.N = 0 and then Got = No_Delivery
                   and then not Root.Send)
       and then (if Sess'Old.P = Done then Result = S_Unexpected)
       and then (if Result = S_OK then
                   Sess.Msgs = Sess'Old.Msgs + 1 and then not Sess.Aborted)
       --  Elements only in Auth and Data.
       and then (if Result = S_OK and then M.Kind in M_Range | M_Elements | M_Have
                 then Sess'Old.P in Auth | Data)
       --  The HELLO, once, in the gate: an inadmissible credential aborts
       --  (A13, G12), and the credential is not returned.
       and then (if Result = S_Aborted and then Sess'Old.P = Gate then
                   M.Kind = M_Hello and then not Sess'Old.Peer_Hello_Seen
                   and then Hello_Wire_OK (Input)
                   and then not Cred_Admissible (F, Sess'Old.Peer_DH, Cred_Of (Input))
                   and then Peer = Empty_Hello
                   and then Sess = (Sess'Old with delta P => Done, Aborted => True)
                   and then Out_Box.N = 0 and then Got = No_Delivery
                   and then not Root.Send)
       and then (if Result = S_OK and then Sess'Old.P = Gate then
                   M.Kind = M_Hello and then not Sess'Old.Peer_Hello_Seen
                   and then Hello_Wire_OK (Input) and then Hello_Decoded (Input, Peer)
                   and then Cred_Admissible (F, Sess'Old.Peer_DH, Cred_Of (Input))
                   and then Sess = (Sess'Old with delta
                                      Peer_Hello_Seen => True,
                                      Peer_Auth       => Sess.Peer_Auth,
                                      Peer_Data       => Sess.Peer_Data,
                                      Peer_Digest     => Sess.Peer_Digest,
                                      Msgs            => Sess'Old.Msgs + 1,
                                      P               => Sess.P,
                                      Budget          => Sess.Budget,
                                      Q               => Sess.Q,
                                      Q_Len           => Sess.Q_Len,
                                      Auth_Root_Seen  => Sess.Auth_Root_Seen)
                   and then Sess.Peer_Digest = Kome.Keys.To_Key256 (Peer.Digest)
                   and then Sess.Peer_Auth = Claim (Peer.N_Auth)
                   and then Sess.Peer_Data = Claim (Peer.N_Data)
                   and then Got = No_Delivery and then Out_Box.N = 0
                   and then (if Sess.Hello_Sent then After_Hellos (Sess, Root)
                             else Sess.P = Gate and then not Root.Send
                                  and then Sess.Budget = Sess'Old.Budget
                                  and then Sess.Q_Len = 0))
       --  The gate (S9): a closed gate in Auth or Data aborts.
       and then (if Result = S_Aborted and then Sess'Old.P in Auth | Data then
                   not Gate_Open (Sess'Old.Cid, F, Eff, Sess'Old.Peer_DH)
                   and then Sess = (Sess'Old with delta P => Done, Aborted => True)
                   and then Out_Box.N = 0 and then Got = No_Delivery
                   and then not Root.Send)
       --  RANGE part / ROOT / ELEMENTS / HAVE in Auth or Data: the answer
       --  is the answer of Respond, within the budgets. A ROOT only as the
       --  expected one, any other message only as the head's next tile;
       --  the gate was open.
       and then (if Result = S_OK and then Sess'Old.P in Auth | Data then
                   M.Kind in M_Range | M_Elements | M_Have
                   and then not Root.Send
                   and then M = Bind (Sess'Old, Decode_Of (Input, Part, Keys).M)
                   and then Decode_Facts (Input, Part, Keys, Decode_Of (Input, Part, Keys).M, True)
                   and then Msg_OK (M)
                   and then Root_Or_Owed (Sess'Old, M)
                   and then Gate_Open (Sess'Old.Cid, F, Eff, Sess'Old.Peer_DH)
                   and then Out_Box = Reply_Of (S, M).Box
                   and then Got = Reply_Of (S, M).Got
                   and then Delivers (S, M, Got)
                   and then Answers (S, M, Out_Box)
                   and then Shrinks (S, M, Out_Box)
                   and then Sess.Ranges = Sess'Old.Ranges + Num_Ranges (Out_Box)
                   and then Sess.Ranges <= Range_Budget (S)
                   and then Sess.Shipped = Sess'Old.Shipped + Item_Bytes (S, Out_Box)
                   and then Sess.Shipped <= Ship_Budget (S)
                   and then Sess.Q_Len =
                              Sess'Old.Q_Len
                              - (if Group_Done (Sess'Old, M) then 1 else 0)
                              + Obligations (Out_Box)
                   and then Queue_Step (Sess'Old, Sess, M, Out_Box)
                   and then Sess.Auth_Root_Seen = (Sess'Old.Auth_Root_Seen or else M.Root)
                   and then Sess.P =
                              (if Sess'Old.P = Data
                                 or else (M.Root and then Sess'Old.Auth_Root_Seen)
                               then (if Sess.Q_Len = 0 then Done else Data)
                               else Auth)
                   and then Sess = (Sess'Old with delta
                                      Msgs           => Sess'Old.Msgs + 1,
                                      P              => Sess.P,
                                      Q              => Sess.Q,
                                      Q_Head         => Sess.Q_Head,
                                      Q_Len          => Sess.Q_Len,
                                      Ranges         => Sess.Ranges,
                                      Shipped        => Sess.Shipped,
                                      Auth_Root_Seen => Sess.Auth_Root_Seen));

private

   --  The key fields other than h, the frame length and the source of one
   --  element (a record of scalars and word records: logical equality).
   type Meta is record
      K   : Kind_Code  := 0;
      Ent : Id128;
      Sub : Kind_Code  := 0;
      FH  : Key256;
      Len : Frame_Size := 1;
      Src : Elem_Index := 1;
   end record;

   type Meta_Array is array (Elem_Index range <>) of Meta;
   type Pos_Array  is array (Elem_Index range <>) of Positive;
   type Len_Array  is array (Elem_Index range <>) of Frame_Size;

   type Frame_Table (Cap : Elem_Count; Pool_Cap : Pool_Size) is record
      N    : Elem_Count := 0;
      Used : Pool_Size  := 0;
      Offs : Pos_Array (1 .. Cap)  := [others => 1];
      Lens : Len_Array (1 .. Cap)  := [others => 1];
      Pool : Byte_Array (1 .. Pool_Cap) := [others => 0];
   end record
   with Dynamic_Predicate => Frame_Table.N <= Frame_Table.Cap
                             and then Frame_Table.Used <= Frame_Table.Pool_Cap;

   function Table_Count (T : Frame_Table) return Elem_Count is (T.N);

   function Table_Bytes (T : Frame_Table) return Pool_Size is (T.Used);

   function Table_Len (T : Frame_Table; I : Elem_Index) return Frame_Size is
     (T.Lens (I));

   function Entry_In_Pool (T : Frame_Table; I : Elem_Index) return Boolean is
     (T.Offs (I) <= T.Used and then T.Lens (I) - 1 <= T.Used - T.Offs (I))
   with Pre => I <= T.Cap;

   function Table_Valid (T : Frame_Table) return Boolean is
     (for all I in 1 .. T.N => Entry_In_Pool (T, I));

   function Table_Frame (T : Frame_Table; I : Elem_Index) return Byte_Array is
     (T.Pool (T.Offs (I) .. T.Offs (I) + T.Lens (I) - 1));

   type Snapshot (Cap : Elem_Count) is record
      N    : Elem_Count := 0;
      Used : Snap_Bytes := 0;
      E    : Meta_Array (1 .. Cap) := [others => (others => <>)];
      Hs   : Kome.Digest.Hash_Array (1 .. Cap) := [others => (others => 0)];
   end record
   with Dynamic_Predicate => Snapshot.N <= Snapshot.Cap;

   type Prefix (Slots : Kome.Digest.Block_Index) is record
      A : Kome.Digest.Acc_Array (1 .. Slots) := [others => Kome.Accumulator.Zero];
   end record;

   function Count (S : Snapshot) return Elem_Count is (S.N);

   function Frame_Bytes (S : Snapshot) return Snap_Bytes is (S.Used);

   function Key (S : Snapshot; I : Elem_Index) return Elem_Key is
     ((K => S.E (I).K, Ent => S.E (I).Ent, Sub => S.E (I).Sub, FH => S.E (I).FH,
       H => S.Hs (I)));

   function Frame_Len (S : Snapshot; I : Elem_Index) return Frame_Size is
     (S.E (I).Len);

   function Source (S : Snapshot; I : Elem_Index) return Elem_Index is
     (S.E (I).Src);

   function Valid (S : Snapshot) return Boolean is
     (S.Used <= Byte_Total (S.N) * Frame_Ship_Max
      and then (for all I in 1 .. S.N =>
                  (for all J in I + 1 .. S.N => Key_Lt (Key (S, I), Key (S, J)))));

   function Linked (S : Snapshot; T : Frame_Table) return Boolean is
     (for all I in 1 .. S.N =>
        S.E (I).Src <= T.N and then T.Lens (S.E (I).Src) = S.E (I).Len);

   function Elem_Frame (S : Snapshot; T : Frame_Table; I : Elem_Index) return Byte_Array is
     (Table_Frame (T, S.E (I).Src));

   function Sealed (S : Snapshot; P : Prefix) return Boolean is
     (P.Slots = Prefix_Slots (S.N)
      and then Kome.Digest.Prefix_Valid (S.Hs (1 .. S.N), P.A));

   function Covers
     (S : Snapshot; Lo, Hi : Elem_Key; First : Lo_Bound; Last : Elem_Count)
      return Boolean
   is (for all K in 1 .. S.N =>
         In_Window (Key (S, K), Lo, Hi) = (K >= First and then K <= Last));

   function Range_Fp (S : Snapshot; First : Lo_Bound; Last : Elem_Count)
     return Hash256
   is (if Last < First then Kome.Digest.Fingerprint (Kome.Digest.Empty)
       else Kome.Digest.Fingerprint (Kome.Digest.Digest_Of (S.Hs (First .. Last))));

   function Plan_Shape (S : Snapshot; P : Plan) return Boolean is
     (Key_Lt (P.Lo, P.Hi)
      and then
      (case P.Kind is
         when P_Range    =>
           P.First <= P.Last + 1 and then P.Last <= Count (S),
         when P_Elements =>
           P.First <= P.Last + 1 and then P.Last <= Count (S)
           and then P.Last + 1 - P.First <= Ship_Threshold,
         when P_Have     =>
           (for all T in 1 .. P.N => P.Items (T) <= Count (S))));

   function Plan_OK (S : Snapshot; P : Plan) return Boolean is
     (Plan_Shape (S, P)
      and then Plan_Len (S, P) <= Max_Message_Len
      and then
      (case P.Kind is
         when P_Range | P_Elements =>
           Covers (S, P.Lo, P.Hi, P.First, P.Last),
         when P_Have     =>
           (for all T in 1 .. P.N =>
              In_Window (Key (S, P.Items (T)), P.Lo, P.Hi))
           and then (for all T in 2 .. P.N => P.Items (T - 1) < P.Items (T))));

   function Outbox_OK (S : Snapshot; O : Outbox) return Boolean is
     (for all T in 1 .. O.N => Plan_OK (S, O.P (T)));

   function Tiles (O : Outbox; Lo, Hi : Elem_Key) return Boolean is
     (O.N >= 1
      and then O.P (1).Lo = Lo
      and then O.P (O.N).Hi = Hi
      and then (for all T in 2 .. O.N => O.P (T - 1).Hi = O.P (T).Lo));

   function Cred_Canonical (H : Hello) return Boolean is
     ((for all I in H.Cred_Len .. Cred_Max - 1 => H.Cred (I) = 0)
      and then (for all I in H.Ceil_Len .. Cred_Max - 1 => H.Ceil (I) = 0));

   function All_Kind (O : Outbox; K : Out_Kind) return Boolean is
     (for all T in 1 .. O.N => O.P (T).Kind = K);

   function Ranges_Upto (O : Outbox; T : Out_Count) return Out_Count is
     (if T = 0 then 0
      else Ranges_Upto (O, T - 1) + (if O.P (T).Kind = P_Range then 1 else 0));

   function Obligations_Upto (O : Outbox; T : Out_Count) return Out_Count is
     (if T = 0 then 0
      else Obligations_Upto (O, T - 1) + (if O.P (T).Kind /= P_Have then 1 else 0));

   function Items_Upto (S : Snapshot; O : Outbox; T : Out_Count)
     return Byte_Total
   is (if T = 0 then 0
       else Items_Upto (S, O, T - 1) + Byte_Total (Plan_Items (S, O.P (T))));

   function Exact_Plans (S : Snapshot; O : Outbox) return Boolean is
     (for all T in 1 .. O.N =>
        (if O.P (T).Kind /= P_Have then
           Key_Lt (O.P (T).Lo, O.P (T).Hi)
           and then O.P (T).First = Window (S, O.P (T).Lo, O.P (T).Hi).First
           and then O.P (T).Last = Window (S, O.P (T).Lo, O.P (T).Hi).Last));

   function Msg_OK (M : Message) return Boolean is
     (M.Kind in M_Range | M_Elements | M_Have
      and then Key_Lt (M.Lo, M.Hi)
      and then (if M.Kind = M_Range then M.N = 0)
      and then (if M.Root then M.Kind = M_Range)
      and then (for all T in 1 .. M.N => In_Window (M.Items (T).Key, M.Lo, M.Hi))
      and then (for all T in 2 .. M.N =>
                  Key_Lt (M.Items (T - 1).Key, M.Items (T).Key)));

   function Msg_In (M : Message; Input : Byte_Array) return Boolean is
     (for all T in 1 .. M.N =>
        M.Items (T).Off >= Input'First
        and then M.Items (T).Off <= Input'Last
        and then Input'Last - M.Items (T).Off >= M.Items (T).Len - 1);

   function Keys_Given (M : Message; Keys : Key_List) return Boolean is
     (for all T in 1 .. M.N => M.Items (T).Key = Keys (T));

   function Held (S : Snapshot; K : Elem_Key) return Boolean is
     (for some I in 1 .. S.N => Key (S, I) = K);

   function Delivers (S : Snapshot; M : Message; D : Delivery) return Boolean is
     (for all T in Item_Index =>
        D (T) = (T <= M.N and then not Held (S, M.Items (T).Key)));

   --  K is one of the item keys of M.
   function In_Msg (M : Message; K : Elem_Key) return Boolean is
     (for some T in 1 .. M.N => M.Items (T).Key = K);

   --  One of the HAVEs of O offers our element K.
   function Offered (O : Outbox; K : Elem_Index) return Boolean is
     (for some T in 1 .. O.N =>
        (for some U in 1 .. O.P (T).N => O.P (T).Items (U) = K));

   function Have_Exact (S : Snapshot; M : Message; O : Outbox) return Boolean is
     (Tiles (O, M.Lo, M.Hi)
      and then (for all T in 1 .. O.N =>
                  O.P (T).Kind = P_Have
                  and then (for all U in 1 .. O.P (T).N =>
                              O.P (T).Items (U) <= S.N
                              and then not In_Msg (M, Key (S, O.P (T).Items (U)))))
      and then (for all K in 1 .. S.N =>
                  (if In_Window (Key (S, K), M.Lo, M.Hi)
                     and then not In_Msg (M, Key (S, K))
                   then Offered (O, K))));

   function Shrinks (S : Snapshot; M : Message; O : Outbox) return Boolean is
     (for all T in 1 .. O.N =>
        (if O.P (T).Kind = P_Range then
           Key_Lt (O.P (T).Lo, O.P (T).Hi)
           and then Key_Le (M.Lo, O.P (T).Lo)
           and then Key_Le (O.P (T).Hi, M.Hi)
           and then My_Count (S, O.P (T).Lo, O.P (T).Hi) < My_Count (S, M.Lo, M.Hi)));

end Kome.Reconcile;
