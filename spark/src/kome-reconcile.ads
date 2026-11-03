--  Kome.Reconcile: the reconciliation session for the frontier of one
--  collection (DESIGN.md §8, D12, D13 and D14). The session has the
--  pre-gate OPEN, the post-gate HELLO and two range reconciliations: first
--  the authorization range, then the data range.
--
--  The elements are the records of F for one ns. The key of an element is
--
--    kind:u8 ‖ ent[16] ‖ fh[32] ‖ h[32]          (81 bytes, §8)
--
--  with ROSTER = 0, REVOKE = 1, GRANT = 2, DEL = 3, PUT = 4. The order of
--  keys is bytewise. In the package, a key is Elem_Key, a record of scalars
--  and word records (CONVENTIONS.md rule 1). The bytewise order is Key_Lt,
--  a quantifier-free chain of word comparisons. Two lemmas prove that
--  Key_Lt is exactly the byte-lexicographic order on the 81-byte wire key
--  (Lemma_Key_Eq_Is_Bytewise, Lemma_Key_Lt_First_Difference, from the
--  Kome.Keys Id128 and Key256 laws). Authorization records sort first.
--  Data_Lo = 03 ‖ 0^80 divides the key space into the authorization range
--  [Min_Key, Data_Lo) and the data range [Data_Lo, Max_Key).
--
--  Messages (all integers big-endian):
--
--    OPEN      5 ‖ proto:u8 ‖ ns[16] ‖ n_rv:u8 (<= 15) ‖ n_rv × frame[275]
--    HELLO     1 ‖ n_auth:u32 ‖ n_data:u32 ‖ digest[32] ‖ cred_len:u16 ‖ cred[cred_len]
--    RANGE     2 ‖ g:u8 ‖ lo[81] ‖ hi[81] ‖ count:u32 ‖ fp[32]
--    ELEMENTS  3 ‖ g:u8 ‖ lo[81] ‖ hi[81] ‖ n:u8 ‖ n × (key[81] ‖ flen:u32 ‖ frame)
--    HAVE      4 ‖ g:u8 ‖ lo[81] ‖ hi[81] ‖ n:u8 ‖ n × (key[81] ‖ flen:u32 ‖ frame)
--
--  OPEN and HELLO have a fixed layout. Open_Wire_OK and Hello_Wire_OK are
--  quantifier-free, and Decode_Open / Decode_Hello accept exactly them.
--  A range is half-open, [lo, hi), with lo < hi. The messages say:
--    * RANGE: "over my elements in [lo, hi), the count and fingerprint are
--      these".
--    * ELEMENTS: "these (n <= Ship_Threshold) are ALL my elements in
--      [lo, hi)".
--    * HAVE: "these are elements in [lo, hi) that you did not have". An
--      empty HAVE is the explicit confirm.
--  Keys in ELEMENTS and HAVE are strictly ascending, are in [lo, hi), and
--  have kind <= 4. If not, the message is Malformed. Each field has one
--  width and the order of keys is fixed, so a message has one encoding.
--
--  The caller (the transport, phase 9) does the content checks with
--  Kome.Records. This package never does them, because it sees frames as
--  opaque bytes:
--    * OPEN (pre-gate, D13): each frame must satisfy
--      Kome.Records.Is_Founding_Revoke for this collection. The caller
--      verifies and applies only the frames whose subject is a signer that
--      it holds and that is not yet root-voided. It skips the other frames
--      without verification (this limits the pre-gate work). Only after
--      this does it evaluate its gate.
--    * HELLO (post-gate, D13): the cred must be a ROSTER frame for which
--      Kome.Records.Roster_Lists_DH (cred, Noise static key of the peer)
--      holds. If not, the caller aborts the session. If it holds, the
--      caller decodes, verifies and applies it, and evaluates its gate
--      again.
--    * ELEMENTS / HAVE items: the caller decodes and verifies each frame.
--      It checks that the key of the frame is the key that the item gives
--      (Key_Of (To_Header (R))), and it applies the frame.
--    Kome.Store.Put_Frame applies every accepted frame.
--  This package trusts nothing that a lying peer puts in an OPEN or a
--  HELLO. The counts go into the budgets only as min (claimed, Elem_Max).
--  The digest only decides if the session ends early. The frames are
--  signed records. The transport limits the rate of pre-gate work.
--
--  Session (D14, D13). The phases are Await_Open, Gate, Auth, Data, Done.
--    * Start emits our OPEN (ns and our root revocations). P = Await_Open.
--    * Receive of the OPEN of the peer: a foreign ns aborts the session
--      (S_Aborted, P = Done, Aborted). If not, P = Gate, and the decoded
--      OPEN goes back to the caller. The caller applies its frames (above).
--    * Admit: the caller calls Admit when its gate admits the peer. Admit
--      emits our HELLO (the counts of the two ranges, the digest of the
--      full snapshot, our credential). Caller duty: the caller must take
--      the snapshot for Admit after it applies the OPEN of the peer (and
--      the credential of the peer, if the HELLO of the peer came first).
--      The caller must give the same snapshot to every later Receive and
--      Next_Phase of the session.
--    * Receive of the HELLO of the peer (in Gate, before or after Admit):
--      Receive keeps its counts and digest, and the decoded HELLO goes back
--      to the caller (for the credential).
--    * When the two HELLOs have passed (in Admit or in Receive): if the
--      digests are equal, the session ends (Done, no more messages; under
--      A2, equal digests mean equal frontiers). If not, P = Auth. If this
--      transition occurs in Admit, the initiator emits the root RANGE
--      (g = 0, [Min_Key, Data_Lo)) together with its HELLO, after it.
--    * In Auth, when no range that the initiator asked is open, the
--      initiator calls Next_Phase. Next_Phase emits the data root RANGE
--      (g = 0, [Data_Lo, Max_Key)) and moves to Data. In Data, the
--      initiator is Done when nothing is open. It never accepts g = 0.
--    * The responder accepts g = 0 only in two cases:
--        (a) RANGE [Min_Key, Data_Lo) in Auth before the authorization
--            root;
--        (b) RANGE [Data_Lo, Max_Key) in Auth after the authorization root,
--            with nothing that it asked open. This moves it to Data.
--      In Data, the responder is Done when nothing is open after a Receive.
--    * These messages are S_Unexpected and change nothing (Root_OK, the
--      Post of Receive): every other g = 0 message (an ELEMENTS or HAVE
--      with g = 0, other bounds, a repeated root, the data root first or
--      while something is open), any RANGE, ELEMENTS or HAVE before Auth,
--      and any message in Done.
--  The status of Receive is exactly Status_Of (session, snapshot, input).
--  So each refusal has a characterisation in the two directions:
--    * S_Malformed iff the decoder for the tag refuses;
--    * S_Aborted iff a well-formed OPEN in Await_Open names a different ns;
--    * S_Limit iff the message would go above a budget;
--    * a well-formed, expected message within the budgets is accepted.
--  What Receive returns comes from the wire. M is Decode_Of (Input) (its
--  head, kind, count, fingerprint and n read from the input, Decode_Facts).
--  The reply is Reply_Of (S, M), and Open / Peer satisfy Open_Decoded /
--  Hello_Decoded. After Admit, the caller must give the snapshot of Admit
--  to every Receive and Next_Phase (Same_Snapshot, a precondition).
--  Complete (Sess) holds when the session ended without abort.
--
--  Transport. The phase gate assumes an in-order transport (Noise over a
--  stream, DESIGN.md §8). Two conditions stop the session before Complete:
--  loss, and a reordered root message (Receive refuses a data root that
--  arrives before the last reply of the authorization phase). Then the
--  caller times out and starts again from OPEN. DESIGN.md §8 states this,
--  so it is not a deviation. Round 0 (C8, the invertible Bloom lookup
--  table) runs once in each phase, at the start of Auth and at
--  Next_Phase, when it is built. This package does not build it.
--
--  Obligations and replies. A RANGE or an ELEMENTS obliges its receiver to
--  answer. A HAVE obliges nothing. Each answer is a reply group of g >= 1
--  messages (the Out_Box of Respond), and each message of the group
--  carries g. The only messages with g = 0 are the two root RANGEs of the
--  initiator. Each side keeps the weight of its open obligations
--  (Session.Pending). When a side sends a RANGE or an ELEMENTS, it adds
--  Unit. When it receives a message of a group of g, it removes Unit / g.
--  (Unit = lcm (1 .. 16), so a full group removes exactly Unit, in any
--  order.) Receive refuses a message that would remove more than is open.
--  So a peer can only answer what it was asked.
--
--  The responder (Respond) does these steps:
--    * On RANGE (lo, hi, fp, count): it finds our elements in [lo, hi)
--      (Window). If their count and fingerprint (Kome.Digest, fp over the
--      h of each element) are equal to those of the message, it confirms
--      the range with an empty HAVE. If not, and there are at most
--      Ship_Threshold of them, it ships them as ELEMENTS. If not, it splits
--      [lo, hi) 16 ways (Split_Fanout) over our elements and sends each
--      child as a RANGE with our count and fingerprint.
--    * On ELEMENTS: it gives the caller every element that we do not have
--      (exactly those). Then, if we hold at most Ship_Threshold in the
--      range, it sends back as HAVE exactly the elements that the peer did
--      not have (an empty HAVE if none). If not, it splits the range as
--      above.
--    * On HAVE: it gives the caller every element that we do not have.
--  The Post of Respond pins these properties:
--    * the kind of every reply (All_Kind);
--    * a reply that is not a confirm tiles the range and never contains a
--      HAVE;
--    * every plan is exact (Exact_Plans: a RANGE carries our true count
--      and fingerprint, and an ELEMENTS carries all of our elements of its
--      range).
--
--  Message size (D12). No emitted message is longer than Max_Message_Len
--  bytes (Kome, §8). This is proved (Plan_OK, Plan_Len). A RANGE is 200
--  bytes, an OPEN is at most Open_Max_Len = 4 144 and a HELLO is at most
--  Hello_Max_Len = 10 142. If the frames of an ELEMENTS do not fit, the
--  sender splits it more: one ELEMENTS for each element, over a sub-range
--  that holds only that element. If a HAVE does not fit, it goes as one
--  HAVE for each element. One element always fits: a frame is at most
--  Kome.Records.Frame_Max = 41 136 bytes, which is less than
--  Frame_Ship_Max = Max_Message_Len - 165 - 85 = 48 902 (a compile-time
--  check). So a snapshot never refuses a well-formed frame as
--  Snap_Too_Large (Lemma_Frame_Ships). The check stays as a defence.
--
--  Well-founded split (the measure of T7). Each RANGE that a responder
--  emits is a sub-range of the range that it answers, with strictly fewer
--  of the responder's elements (the Post of Respond, Shrinks, measured
--  by My_Count). An ELEMENTS reply covers the same range with the same
--  counts. The only answers to it are a HAVE (which gets no answer) or a
--  split whose children have strictly fewer of the answerer's elements.
--  So the measure of T7 is lexicographic: (μ (r), k) with
--  μ ([lo, hi)) = |F_A ∩ [lo, hi)| + |F_B ∩ [lo, hi)|, and k = 1 for a
--  RANGE, 0 for an ELEMENTS. Every reply decreases it. The implementation
--  makes balanced splits (child counts ⌊n/16⌋ or ⌈n/16⌉; tested, not
--  proved, see the limitations below). With balanced splits, a chain of
--  replies in one phase holds at most s = ⌈log₁₆ N_A⌉ + ⌈log₁₆ N_B⌉
--  splits. A split can cost two one-way messages (ELEMENTS, then the
--  split), so the chain holds at most 2s + 3 one-way messages for each
--  phase. That bound is part of T7, and it is not proved.
--
--  Duplicate deliveries. The snapshot is frozen for the session. So, when
--  we split a range after we receive ELEMENTS, the peer ships the same
--  elements again on the children, and they are delivered again. Record
--  application is idempotent, so this costs bandwidth, not correctness.
--  "delivered" means "not in our snapshot". The ship budget limits it.
--
--  Budgets (a hostile peer cannot cause unlimited traffic). Each budget
--  counts over the two phases:
--    * The accepted messages are at most Msg_Budget (our |S|, the claimed
--      count of the peer). This is an upper bound on what an honest peer
--      sends (the derivation is at Msg_Budget).
--    * The RANGEs that we emit in replies are at most Range_Budget (S) =
--      2 × (2 |S| + 2). (In each phase, the ranges of an honest session
--      make a laminar family, in which our ranges have distinct, non-empty
--      sets of our elements.)
--    * The item bytes that we emit are at most Ship_Budget (S) = 2 × 8 ×
--      (frame bytes + 85 |S|). (An honest phase ships each of our elements
--      at most ⌈log₁₆ N_peer⌉ + 1 <= 6 times.)
--  The two root RANGEs are not replies, and Ranges does not count them.
--  Receive refuses a message that would go above a budget, with S_Limit.
--  The counts have exact definitions, not only bounds: Num_Ranges,
--  Obligations and Item_Bytes are equal to the sums Ranges_Upto,
--  Obligations_Upto and Items_Upto over the plans of the reply. So the
--  Post of Receive states Pending, Ranges, Shipped, the Done transitions
--  and every budget check over the true counts of the reply.
--
--  Tested, not proved (stated limitations):
--    * T7 (termination and convergence). The two-phase session test
--      converges two replicas.
--    * That Decode accepts every ELEMENTS / HAVE that carries items. (A
--      proof shows that it accepts every RANGE and every confirm.)
--    * The item and frame bytes in an encoded ELEMENTS / HAVE. The Post of
--      Encode states the head and the item count, and a test checks the
--      round trip. Decode_Facts states that the head, the kind, the count
--      and fingerprint of a RANGE, and the n of an ELEMENTS / HAVE come
--      from the wire. It does not state the item keys and frame places;
--      tests check these.
--    * That splits are balanced (child counts ⌊n/16⌋ or ⌈n/16⌉). Answers
--      and Shrinks state only that each child is strictly smaller, so the
--      log₁₆ round bound above is part of T7.
--    * The honest-session derivations for Msg_Budget, Range_Budget and
--      Ship_Budget. They are arithmetic over the executions of the
--      protocol, an argument at the level of T7.
pragma Ada_2022;
with Kome.Headers;   use Kome.Headers;
with Kome.Digest;
with Kome.Frontier;
with Kome.Keys;
with Kome.Records;
package Kome.Reconcile with SPARK_Mode is

   ----------------------------------------------------------------------
   --  Element keys and their order (DESIGN.md §8).
   ----------------------------------------------------------------------

   --  The kind byte. Elements use 0 .. 4 (the codes of Kome.Headers.Kind:
   --  ROSTER 0, REVOKE 1, GRANT 2, DEL 3, PUT 4). Range bounds can use any
   --  byte, so Max_Key (kind 255) is above every element.
   type Kind_Code is range 0 .. 255 with Size => 8;

   type Elem_Key is record
      K   : Kind_Code := 0;
      Ent : Id128;
      FH  : Key256;
      H   : Key256;
   end record;

   Key_Wire_Len : constant := 1 + 16 + 32 + 32;   --  81


   --  kind ‖ ent ‖ fh ‖ h compared bytewise.
   function Key_Lt (A, B : Elem_Key) return Boolean is
     (A.K < B.K or else (A.K = B.K and then
      (Kome.Keys.Id_Lt (A.Ent, B.Ent) or else (A.Ent = B.Ent and then
      (Lt (A.FH, B.FH) or else (A.FH = B.FH and then
       Lt (A.H, B.H)))))));

   function Key_Le (A, B : Elem_Key) return Boolean is (not Key_Lt (B, A));

   --  The full key space: every element key k has Min_Key <= k < Max_Key.
   --  Data_Lo divides it. Authorization records (kinds 0 .. 2) are in
   --  [Min_Key, Data_Lo). Data records (kinds 3, 4) are in
   --  [Data_Lo, Max_Key).
   Min_Key : constant Elem_Key :=
     (K => 0, Ent => (others => 0), FH => (others => 0), H => (others => 0));
   Data_Lo : constant Elem_Key :=
     (K => 3, Ent => (others => 0), FH => (others => 0), H => (others => 0));
   Max_Key : constant Elem_Key :=
     (K => 255, Ent => (others => 0), FH => (others => 0), H => (others => 0));

   --  The element key of the header of a record (§8: kind ‖ ent ‖ field
   --  hash ‖ h). Kind'Pos is the code of the kind (Kome.Headers).
   function Key_Of (R : Header) return Elem_Key is
     (K => Kind_Code (Kind'Pos (R.K)), Ent => R.Ent, FH => R.FH, H => R.V.H);

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

   ----------------------------------------------------------------------
   --  Sizes and wire layout (DESIGN.md §8; Kome.Max_Message_Len,
   --  Split_Fanout, Ship_Threshold).
   ----------------------------------------------------------------------

   Tag_Hello    : constant Byte := 1;
   Tag_Range    : constant Byte := 2;
   Tag_Elements : constant Byte := 3;
   Tag_Have     : constant Byte := 4;
   Tag_Open     : constant Byte := 5;

   --  RANGE / ELEMENTS / HAVE.
   O_G           : constant := 1;                                   --  group size
   O_Lo          : constant := 2;
   O_Hi          : constant := O_Lo + Key_Wire_Len;                 --  83
   Range_O_Count : constant := O_Hi + Key_Wire_Len;                 --  164
   Range_O_Fp    : constant := Range_O_Count + 4;                   --  168
   Range_Len     : constant := Range_O_Fp + 32;                     --  200
   Elems_O_N     : constant := O_Hi + Key_Wire_Len;                 --  164
   Elems_Fixed   : constant := Elems_O_N + 1;                       --  165
   Item_Overhead : constant := Key_Wire_Len + 4;                    --  85
   Frame_Ship_Max : constant := Max_Message_Len - Elems_Fixed - Item_Overhead;

   pragma Compile_Time_Error
     (Frame_Ship_Max /= 48_902, "DESIGN.md §8: one ELEMENTS item carries 48 902 frame bytes");
   --  D12: every well-formed frame (at most 41 136 bytes) fits one item.
   pragma Compile_Time_Error
     (Kome.Records.Frame_Max > Frame_Ship_Max,
      "DESIGN.md §8 (D12): Kome.Records.Frame_Max must not exceed Frame_Ship_Max");

   --  OPEN (pre-gate, D13): 5 ‖ proto ‖ ns[16] ‖ n_rv ‖ n_rv × frame[275].
   Proto_Version : constant Byte := 1;
   Rv_Frame_Len  : constant := Kome.Records.Revoke_Frame_Len;        --  275
   Rv_Max        : constant := Signers_Max - 1;                     --  15
   Open_O_Proto  : constant := 1;
   Open_O_NS     : constant := 2;
   Open_O_NRV    : constant := 18;
   Open_Fixed    : constant := 19;
   Open_Max_Len  : constant := Open_Fixed + Rv_Max * Rv_Frame_Len;   --  4 144
   pragma Compile_Time_Error
     (Rv_Frame_Len /= 275 or else Open_Max_Len /= 4_144,
      "DESIGN.md §8: an OPEN is at most 4 144 bytes");

   --  HELLO (post-gate, D13): 1 ‖ n_auth ‖ n_data ‖ digest[32] ‖ cred_len ‖
   --  cred. No register value goes on the wire. HELLO has no proto (OPEN
   --  has it).
   Hello_O_NAuth  : constant := 1;
   Hello_O_NData  : constant := 5;
   Hello_O_Digest : constant := 9;
   Hello_O_CLen   : constant := 41;
   Hello_Fixed    : constant := 43;
   Cred_Max       : constant := Kome.Records.Roster_Frame_Max;     --  10 099
   Hello_Max_Len  : constant := Hello_Fixed + Cred_Max;            --  10 142
   pragma Compile_Time_Error
     (Cred_Max /= 10_099 or else Hello_Max_Len /= 10_142,
      "DESIGN.md §8: a HELLO is at most 10 142 bytes");

   subtype Frame_Size is Positive range 1 .. Frame_Ship_Max;
   subtype Msg_Length is Natural range 0 .. Max_Message_Len;
   subtype Msg_Buffer is Byte_Array (0 .. Max_Message_Len - 1);

   subtype Item_Count is Natural range 0 .. Ship_Threshold;
   subtype Item_Index is Positive range 1 .. Ship_Threshold;

   --  The size of a reply group. 0 marks a root RANGE (not a reply).
   subtype Group_Size is Natural range 0 .. Split_Fanout;

   --  Element counts and indices: the records that one replica holds for
   --  one collection. Kome.Digest.Elem_Max is Kome.Frontier.Held_Max. The
   --  frontier and reconciliation use this one constant (§8 HELLO).
   Elem_Max : constant := Kome.Digest.Elem_Max;
   pragma Compile_Time_Error
     (Elem_Max /= Kome.Frontier.Held_Max,
      "DESIGN.md §8: Elem_Max must be Kome.Frontier.Held_Max");
   subtype Elem_Count is Kome.Digest.Elem_Count;
   subtype Elem_Index is Kome.Digest.Elem_Index;
   subtype Lo_Bound   is Kome.Digest.Lo_Bound;

   ----------------------------------------------------------------------
   --  Functions that read the wire. They are quantifier-free, so they are
   --  public (rule 2). The Posts of Decode and Encode use them.
   ----------------------------------------------------------------------

   function Wire_U16 (B : Byte_Array; P : Natural) return Natural is
     (Natural (B (P)) * 256 + Natural (B (P + 1)))
   with Pre => P >= B'First and then P < B'Last;

   function Wire_U32 (B : Byte_Array; P : Natural) return Word is
     (Kome.Keys.Word_Of (B (P), B (P + 1), B (P + 2), B (P + 3)))
   with Pre => P >= B'First and then P <= B'Last and then B'Last - P >= 3;

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
       FH  => Wire_Key256 (B, P + 17),
       H   => Wire_Key256 (B, P + 49)))
   with Pre => P >= B'First and then P <= B'Last
               and then B'Last - P >= Key_Wire_Len - 1;

   ----------------------------------------------------------------------
   --  Key_Lt is bytewise order on the 81-byte wire key (§8 "compared
   --  bytewise"): equal keys iff equal bytes, and the first byte that is
   --  different decides. Together, these lemmas show that Key_Lt is
   --  exactly the byte-lexicographic order of the encodings (Put_Key
   --  writes Wire_Key).
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
   --  Snapshot: our elements for one session, in strictly ascending
   --  order, each with its frame. Cap elements, Pool_Cap bytes of frames.
   ----------------------------------------------------------------------

   Pool_Max : constant := 2 ** 30;
   subtype Pool_Size is Natural range 0 .. Pool_Max;

   type Snapshot (Cap : Elem_Count; Pool_Cap : Pool_Size) is private;

   function Count (S : Snapshot) return Elem_Count with
     Global => null,
     Post   => Count'Result <= S.Cap;

   --  Bytes of frames held.
   function Frame_Bytes (S : Snapshot) return Pool_Size with Global => null;

   function Key (S : Snapshot; I : Elem_Index) return Elem_Key with
     Global => null,
     Pre    => I <= Count (S);

   function Frame_Len (S : Snapshot; I : Elem_Index) return Frame_Size with
     Global => null,
     Pre    => I <= Count (S);

   --  Strictly ascending order (pairwise), kinds <= 4, frames in the pool.
   --  This function has a quantifier, so its completion is in the private
   --  part (rule 2).
   function Valid (S : Snapshot) return Boolean with Global => null;

   function Frame (S : Snapshot; I : Elem_Index) return Byte_Array with
     Global => null,
     Pre    => Valid (S) and then I <= Count (S),
     Post   => Frame'Result'Length = Frame_Len (S, I);

   --  L more frame bytes fit in the pool.
   function Has_Room (S : Snapshot; L : Natural) return Boolean with
     Global => null;

   procedure Clear (S : out Snapshot) with
     Global => null,
     Post   => Count (S) = 0 and then Frame_Bytes (S) = 0 and then Valid (S);

   type Snap_Status is
     (Snap_OK,
      Snap_Unsorted,    --  key not above the last one appended
      Snap_Bad_Kind,    --  kind > 4
      Snap_Too_Large,   --  frame empty or longer than Frame_Ship_Max (defensive:
                        --  never for a well-formed frame, Lemma_Frame_Ships)
      Snap_No_Space);   --  Cap elements or Pool_Cap bytes reached

   --  Append the next element. Keys must come in strictly ascending order.
   --  On refusal, nothing changes (T13).
   procedure Append
     (S      : in out Snapshot;
      K      : Elem_Key;
      F      : Byte_Array;
      Result : out Snap_Status)
   with
     Global => null,
     Pre    => Valid (S),
     Post   => Valid (S)
       and then (if Result = Snap_OK then
                   Count (S) = Count (S'Old) + 1
                   and then Frame_Bytes (S) = Frame_Bytes (S'Old) + F'Length
                   and then Key (S, Count (S)) = K
                   and then Frame_Len (S, Count (S)) = F'Length
                   and then Frame (S, Count (S)) = F
                   and then (for all I in 1 .. Count (S'Old) =>
                               Key (S, I) = Key (S'Old, I)
                               and then Frame_Len (S, I) = Frame_Len (S'Old, I))
                 else S = S'Old)
       and then (Result = Snap_Too_Large) =
                (K.K <= 4 and then F'Length not in Frame_Size)
       and then (Result = Snap_OK) =
                (K.K <= 4
                 and then F'Length in Frame_Size
                 and then (Count (S'Old) = 0
                           or else Key_Lt (Key (S'Old, Count (S'Old)), K))
                 and then Count (S'Old) < S.Cap
                 and then Has_Room (S'Old, F'Length));

   --  D12: a frame of a well-formed record (1 .. Kome.Records.Frame_Max
   --  bytes) is never Snap_Too_Large (with the Post of Append).
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

   --  Take a sub-run S .. E of a covered window, with the ends of the
   --  parent or the adjacent elements as its bounds. Exactly those bounds
   --  cover the sub-run, and it is a non-empty sub-range of the parent.
   --  This makes every split child a well-formed, strictly smaller range.
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

   ----------------------------------------------------------------------
   --  Fingerprints (DESIGN.md §8 "fingerprint = digest", T6): fp over the
   --  h of our elements First .. Last, with Kome.Digest.
   ----------------------------------------------------------------------

   function Range_Fp (S : Snapshot; First : Lo_Bound; Last : Elem_Count)
     return Hash256
   with Global => null,
        Pre    => First <= Last + 1 and then Last <= Count (S);

   ----------------------------------------------------------------------
   --  Plans: messages to send, as references into the snapshot. Encode
   --  changes a plan into bytes. (OPEN and HELLO are not plans: Start and
   --  Admit write them into a buffer.)
   ----------------------------------------------------------------------

   type Out_Kind is (P_Range, P_Elements, P_Have);

   function Tag_Of (K : Out_Kind) return Byte is
     (case K is
        when P_Range    => Tag_Range,
        when P_Elements => Tag_Elements,
        when P_Have     => Tag_Have);

   type Index_List is array (Item_Index) of Elem_Index;

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

   --  The number of bytes that Encode makes for P.
   function Plan_Len (S : Snapshot; P : Plan) return Positive is
     (case P.Kind is
        when P_Range    => Range_Len,
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

   --  What to send: the plans P (1 .. N). If Reply, the plans are one
   --  reply group (each carries g = N). If not, g = 0 (a root RANGE).
   type Outbox is record
      Reply : Boolean   := False;
      N     : Out_Count := 0;
      P     : Plan_Array;
   end record;

   function Group (O : Outbox) return Group_Size is
     (if O.Reply then O.N else 0);

   --  Every plan is Plan_OK. This function has a quantifier, so its
   --  completion is in the private part.
   function Outbox_OK (S : Snapshot; O : Outbox) return Boolean with
     Global => null;

   procedure Lemma_Outbox_OK (S : Snapshot; O : Outbox; T : Positive) with
     Ghost, Global => null,
     Pre  => Outbox_OK (S, O) and then T <= O.N,
     Post => Plan_OK (S, O.P (T));

   --  The plans of O tile [Lo, Hi): the first starts at Lo, the last ends
   --  at Hi, and each ends where the next starts. With each plan's cover,
   --  each of our elements in [Lo, Hi) is in exactly one reply.
   function Tiles (O : Outbox; Lo, Hi : Elem_Key) return Boolean with
     Global => null;

   --  Every plan of O is of kind K (so a reply of one kind never includes
   --  a HAVE). This function has a quantifier, so its completion is in the
   --  private part.
   function All_Kind (O : Outbox; K : Out_Kind) return Boolean with
     Global => null;

   procedure Lemma_All_Kind (O : Outbox; K : Out_Kind; T : Positive) with
     Ghost, Global => null,
     Pre  => All_Kind (O, K) and then T <= O.N,
     Post => O.P (T).Kind = K;

   --  Every RANGE and ELEMENTS plan of O is exact: its run First .. Last is
   --  our window of its range. So a RANGE carries our true count and
   --  fingerprint, and an ELEMENTS carries all of our elements in its
   --  range. This function has a quantifier, so its completion is in the
   --  private part. Lemma_Exact_Plan gives its meaning.
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

   --  A root RANGE over [Lo, Hi): one RANGE, not a reply (g = 0), that
   --  carries our full window of the range.
   function Is_Root (S : Snapshot; O : Outbox; Lo, Hi : Elem_Key) return Boolean is
     (O.N = 1 and then not O.Reply and then O.P (1).Kind = P_Range
      and then O.P (1).Lo = Lo and then O.P (1).Hi = Hi
      and then O.P (1).First = Window (S, Lo, Hi).First
      and then O.P (1).Last = Window (S, Lo, Hi).Last)
   with Pre => Valid (S) and then Key_Lt (Lo, Hi);

   --  The number of RANGE plans, the number of obligations (RANGE or
   --  ELEMENTS), and the number of item bytes in the ELEMENTS and HAVE
   --  plans.
   type Byte_Total is range 0 .. 2 ** 40;

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
   --  private part. The accounting functions below are equal to them at
   --  T = O.N. So the Post of Receive states Pending, Ranges, Shipped and
   --  every budget check over the true counts of the reply.
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
   --  Received RANGE / ELEMENTS / HAVE, decoded. Frames stay in the input
   --  buffer. An item records the position (Off, absolute index) and the
   --  length of its frame.
   ----------------------------------------------------------------------

   type Msg_Kind is (M_Open, M_Hello, M_Range, M_Elements, M_Have);

   type In_Item is record
      Key : Elem_Key;
      Off : Natural    := 0;
      Len : Frame_Size := 1;
   end record;

   type In_Items is array (Item_Index) of In_Item;

   type Message is record
      Kind   : Msg_Kind   := M_Range;
      G      : Group_Size := 0;                 --  RANGE, ELEMENTS, HAVE
      Lo     : Elem_Key   := Min_Key;
      Hi     : Elem_Key   := Max_Key;
      Count  : Elem_Count := 0;                 --  RANGE
      Fp     : Hash256    := [others => 0];     --  RANGE
      N      : Item_Count := 0;                 --  ELEMENTS, HAVE
      Items  : In_Items;
   end record;

   --  The properties of a decoded RANGE / ELEMENTS / HAVE. This function
   --  has a quantifier (the items), so its completion is in the private
   --  part.
   function Msg_OK (M : Message) return Boolean with
     Global => null,
     Post   => (if Msg_OK'Result then
                  M.Kind in M_Range | M_Elements | M_Have
                  and then Key_Lt (M.Lo, M.Hi)
                  and then (if M.Kind = M_Range then M.N = 0));

   --  Every frame of M is in Input. This function has a quantifier, so its
   --  completion is in the private part.
   function Msg_In (M : Message; Input : Byte_Array) return Boolean with
     Global => null;

   --  The two shapes that Decode is proved to accept: a RANGE, and an
   --  ELEMENTS or HAVE with no items (the confirm). Msg_OK states the other
   --  shapes that it accepts, and tests check them. Quantifier-free.
   function Range_Wire_OK (B : Byte_Array) return Boolean is
     (B'Length = Range_Len
      and then B (B'First) = Tag_Range
      and then B (B'First + O_G) <= Split_Fanout
      and then Key_Lt (Wire_Key (B, B'First + O_Lo), Wire_Key (B, B'First + O_Hi))
      and then Wire_U32 (B, B'First + Range_O_Count) <= Elem_Max);

   function Empty_Wire_OK (B : Byte_Array) return Boolean is
     (B'Length = Elems_Fixed
      and then (B (B'First) = Tag_Elements or else B (B'First) = Tag_Have)
      and then B (B'First + O_G) <= Split_Fanout
      and then Key_Lt (Wire_Key (B, B'First + O_Lo), Wire_Key (B, B'First + O_Hi))
      and then B (B'First + Elems_O_N) = 0);

   --  The count and fingerprint of M are those that the well-formed
   --  RANGE B carries.
   function Range_Fields (B : Byte_Array; M : Message) return Boolean is
     (M.Count = Natural (Wire_U32 (B, B'First + Range_O_Count))
      and then M.Fp = B (B'First + Range_O_Fp .. B'First + Range_O_Fp + 31))
   with Pre => Range_Wire_OK (B);

   --  What Decode states about its result (M, OK) for Input. When Decode
   --  accepts:
   --    * M is well-formed, and its head is the (g, lo, hi) of the wire;
   --    * its kind is the kind of the tag;
   --    * a RANGE is a well-formed RANGE, and its count and fingerprint
   --      come from the wire;
   --    * an ELEMENTS / HAVE has the n of the wire.
   --  Completeness: Decode accepts every well-formed RANGE and confirm.
   function Decode_Facts (Input : Byte_Array; M : Message; OK : Boolean)
     return Boolean
   is
     ((if OK then
         Msg_OK (M) and then Msg_In (M, Input)
         and then Input'Length >= Elems_Fixed
         and then M.G = Natural (Input (Input'First + O_G))
         and then M.Lo = Wire_Key (Input, Input'First + O_Lo)
         and then M.Hi = Wire_Key (Input, Input'First + O_Hi)
         and then M.Kind = (if Input (Input'First) = Tag_Range then M_Range
                            elsif Input (Input'First) = Tag_Elements then M_Elements
                            else M_Have)
         and then (if M.Kind = M_Range then
                     Range_Wire_OK (Input) and then Range_Fields (Input, M)
                   else
                     (Input (Input'First) = Tag_Have
                      or else Input (Input'First) = Tag_Elements)
                     and then M.N = Natural (Input (Input'First + Elems_O_N))))
      and then (if Range_Wire_OK (Input) then
                  OK and then M.Kind = M_Range and then Range_Fields (Input, M))
      and then (if Empty_Wire_OK (Input) then
                  OK and then M.N = 0
                  and then M.Kind = (if Input (Input'First) = Tag_Elements
                                     then M_Elements else M_Have)));

   --  Decode, as a function of the input (so a contract can name the one
   --  message that an input decodes to).
   type Decoding is record
      M  : Message;
      OK : Boolean := False;
   end record;

   function Decode_Of (Input : Byte_Array) return Decoding with
     Global => null,
     Post   => Decode_Facts (Input, Decode_Of'Result.M, Decode_Of'Result.OK);

   procedure Decode
     (Input  : Byte_Array;
      M      : out Message;
      OK     : out Boolean)
   with
     Global => null,
     Post   => M = Decode_Of (Input).M and then OK = Decode_Of (Input).OK
               and then Decode_Facts (Input, M, OK);

   ----------------------------------------------------------------------
   --  OPEN (pre-gate, D13). Canonical: frames after N_RV are zero.
   ----------------------------------------------------------------------

   subtype Rv_Count is Natural range 0 .. Rv_Max;
   subtype Rv_Index is Positive range 1 .. Rv_Max;
   subtype Rv_Frame is Byte_Array (0 .. Rv_Frame_Len - 1);
   type Rv_Array is array (Rv_Index) of Rv_Frame;

   Zero_Rv : constant Rv_Frame := [others => 0];

   type Open_Msg is record
      Proto : Byte     := Proto_Version;
      NS    : Id128;
      N_RV  : Rv_Count := 0;
      RV    : Rv_Array := [others => [others => 0]];
   end record;

   function Open_Len (N : Rv_Count) return Positive is
     (Open_Fixed + Rv_Frame_Len * N);

   --  The start of frame I, relative to the message.
   function Rv_At (I : Rv_Index) return Natural is
     (Open_Fixed + Rv_Frame_Len * (I - 1));

   --  B is a well-formed OPEN: tag, proto, n_rv <= Rv_Max and the length
   --  that n_rv gives. Quantifier-free.
   function Open_Wire_OK (B : Byte_Array) return Boolean is
     (B'Last >= B'First
      and then B'Last - B'First >= Open_Fixed - 1
      and then B (B'First) = Tag_Open
      and then B (B'First + Open_O_Proto) = Proto_Version
      and then B (B'First + Open_O_NRV) <= Rv_Max
      and then B'Last - B'First
                 = Open_Fixed - 1 + Rv_Frame_Len * Natural (B (B'First + Open_O_NRV)));

   procedure Encode_Open
     (O   : Open_Msg;
      Buf : out Msg_Buffer;
      Len : out Msg_Length)
   with
     Global => null,
     Pre    => O.Proto = Proto_Version,
     Post   => Len = Open_Len (O.N_RV) and then Len <= Open_Max_Len
               and then Open_Wire_OK (Buf (0 .. Len - 1))
               and then Wire_Id128 (Buf, Open_O_NS) = O.NS
               and then Natural (Buf (Open_O_NRV)) = O.N_RV
               and then (for all I in 1 .. O.N_RV =>
                           Buf (Rv_At (I) .. Rv_At (I) + Rv_Frame_Len - 1) = O.RV (I));

   --  Frame I of the well-formed OPEN B.
   function Open_Frame (B : Byte_Array; I : Rv_Index) return Rv_Frame is
     (B (B'First + Rv_At (I) .. B'First + (Rv_At (I) + (Rv_Frame_Len - 1))))
   with Pre => Open_Wire_OK (B) and then I <= Natural (B (B'First + Open_O_NRV));

   --  The frames of O are the frames of B, and the unused frames are zero.
   --  This function has a quantifier, so its completion is in the private
   --  part (rule 2). Lemma_Open_Frames gives its meaning.
   function Open_Frames (B : Byte_Array; O : Open_Msg) return Boolean with
     Global => null,
     Pre    => Open_Wire_OK (B) and then O.N_RV = Natural (B (B'First + Open_O_NRV));

   procedure Lemma_Open_Frames (B : Byte_Array; O : Open_Msg; I : Rv_Index) with
     Ghost, Global => null,
     Pre  => Open_Wire_OK (B) and then O.N_RV = Natural (B (B'First + Open_O_NRV))
             and then Open_Frames (B, O),
     Post => (if I <= O.N_RV then O.RV (I) = Open_Frame (B, I)
              else O.RV (I) = Zero_Rv);

   --  O is the OPEN that the well-formed B carries, canonically.
   --  Quantifier-free (the frames are behind Open_Frames).
   function Open_Decoded (B : Byte_Array; O : Open_Msg) return Boolean is
     (O.Proto = Proto_Version
      and then O.NS = Wire_Id128 (B, B'First + Open_O_NS)
      and then O.N_RV = Natural (B (B'First + Open_O_NRV))
      and then Open_Frames (B, O))
   with Pre => Open_Wire_OK (B);

   --  Decode_Open accepts exactly the well-formed OPENs (a wrong proto,
   --  n_rv > Rv_Max or a length mismatch is Malformed). The fields that it
   --  returns come from the wire, in canonical form.
   procedure Decode_Open
     (Input : Byte_Array;
      O     : out Open_Msg;
      OK    : out Boolean)
   with
     Global => null,
     Post   => OK = Open_Wire_OK (Input)
               and then (if OK then Open_Decoded (Input, O));

   ----------------------------------------------------------------------
   --  HELLO (post-gate, D13). Canonical: cred bytes after Cred_Len are zero.
   ----------------------------------------------------------------------

   subtype Cred_Count is Natural range 0 .. Cred_Max;
   subtype Cred_Bytes is Byte_Array (0 .. Cred_Max - 1);

   type Hello is record
      N_Auth   : Word       := 0;
      N_Data   : Word       := 0;
      Digest   : Hash256    := [others => 0];
      Cred_Len : Cred_Count := 0;
      Cred     : Cred_Bytes := [others => 0];
   end record;

   --  B is a well-formed HELLO: tag, cred_len <= Cred_Max and the length
   --  that cred_len gives. Quantifier-free.
   function Hello_Wire_OK (B : Byte_Array) return Boolean is
     (B'Last >= B'First
      and then B'Last - B'First >= Hello_Fixed - 1
      and then B (B'First) = Tag_Hello
      and then Wire_U16 (B, B'First + Hello_O_CLen) <= Cred_Max
      and then B'Last - B'First = Hello_Fixed - 1 + Wire_U16 (B, B'First + Hello_O_CLen));

   procedure Encode_Hello
     (N_Auth, N_Data : Word;
      Digest         : Hash256;
      Cred           : Byte_Array;
      Buf            : out Msg_Buffer;
      Len            : out Msg_Length)
   with
     Global => null,
     Pre    => Cred'Length <= Cred_Max,
     Post   => Len = Hello_Fixed + Cred'Length and then Len <= Hello_Max_Len
               and then Hello_Wire_OK (Buf (0 .. Len - 1))
               and then Wire_U32 (Buf, Hello_O_NAuth) = N_Auth
               and then Wire_U32 (Buf, Hello_O_NData) = N_Data
               and then Buf (Hello_O_Digest .. Hello_O_Digest + 31) = Digest
               and then Wire_U16 (Buf, Hello_O_CLen) = Cred'Length
               and then Buf (Hello_Fixed .. Len - 1) = Cred;

   --  The cred bytes of H after Cred_Len are zero. This function has a
   --  quantifier, so its completion is in the private part (rule 2).
   --  Lemma_Cred_Zero gives its meaning.
   function Cred_Canonical (H : Hello) return Boolean with
     Global => null;

   procedure Lemma_Cred_Zero (H : Hello; I : Natural) with
     Ghost, Global => null,
     Pre  => Cred_Canonical (H) and then I >= H.Cred_Len and then I <= Cred_Max - 1,
     Post => H.Cred (I) = 0;

   --  H is the HELLO that the well-formed B carries, canonically.
   --  Quantifier-free (the zero tail is behind Cred_Canonical).
   function Hello_Decoded (B : Byte_Array; H : Hello) return Boolean is
     (H.N_Auth = Wire_U32 (B, B'First + Hello_O_NAuth)
      and then H.N_Data = Wire_U32 (B, B'First + Hello_O_NData)
      and then H.Digest = B (B'First + Hello_O_Digest .. B'First + Hello_O_Digest + 31)
      and then H.Cred_Len = Wire_U16 (B, B'First + Hello_O_CLen)
      and then (if H.Cred_Len > 0 then
                  H.Cred (0 .. H.Cred_Len - 1) = B (B'First + Hello_Fixed .. B'Last))
      and then Cred_Canonical (H))
   with Pre => Hello_Wire_OK (B);

   --  Decode_Hello accepts exactly the well-formed HELLOs (cred_len >
   --  Cred_Max or a length mismatch is Malformed). The fields that it
   --  returns come from the wire, in canonical form.
   procedure Decode_Hello
     (Input : Byte_Array;
      H     : out Hello;
      OK    : out Boolean)
   with
     Global => null,
     Post   => OK = Hello_Wire_OK (Input)
               and then (if OK then Hello_Decoded (Input, H));

   --  A claimed count, as it goes into the budgets: min (claimed,
   --  Elem_Max).
   function Claim (W : Word) return Elem_Count is
     (if W > Elem_Max then Elem_Max else Natural (W));

   ----------------------------------------------------------------------
   --  Encode RANGE / ELEMENTS / HAVE. No message is longer than
   --  Max_Message_Len bytes (T13, the bounds obligation, for messages):
   --  Plan_OK bounds Plan_Len, and the length from Encode is Plan_Len.
   ----------------------------------------------------------------------

   --  G is the group size that goes with the plan (Group (Out_Box)).
   procedure Encode
     (S   : Snapshot;
      P   : Plan;
      G   : Group_Size;
      Buf : out Msg_Buffer;
      Len : out Msg_Length)
   with
     Global => null,
     Pre    => Valid (S) and then Plan_OK (S, P),
     Post   => Len = Plan_Len (S, P)
               and then Buf (0) = Tag_Of (P.Kind)
               and then Natural (Buf (O_G)) = G
               and then Wire_Key (Buf, O_Lo) = P.Lo
               and then Wire_Key (Buf, O_Hi) = P.Hi
               and then (case P.Kind is
                           when P_Range =>
                             Wire_U32 (Buf, Range_O_Count) = Word (P.Last + 1 - P.First)
                             and then Buf (Range_O_Fp .. Range_O_Fp + 31)
                                        = Range_Fp (S, P.First, P.Last),
                           when P_Elements =>
                             Natural (Buf (Elems_O_N)) = P.Last + 1 - P.First,
                           when P_Have =>
                             Natural (Buf (Elems_O_N)) = P.N);

   --  The round trip, for the shapes that Decode is proved to accept:
   --  Decode accepts what Encode emits for a RANGE and for a confirm.
   procedure Lemma_Range_Accepted
     (S : Snapshot; P : Plan; G : Group_Size; Buf : Msg_Buffer)
   with
     Ghost, Global => null,
     Pre  => Valid (S) and then Plan_OK (S, P) and then P.Kind = P_Range
             and then Buf (0) = Tag_Range and then Natural (Buf (O_G)) = G
             and then Wire_Key (Buf, O_Lo) = P.Lo
             and then Wire_Key (Buf, O_Hi) = P.Hi
             and then Wire_U32 (Buf, Range_O_Count) = Word (P.Last + 1 - P.First),
     Post => Range_Wire_OK (Buf (0 .. Range_Len - 1));

   procedure Lemma_Confirm_Accepted
     (S : Snapshot; P : Plan; G : Group_Size; Buf : Msg_Buffer)
   with
     Ghost, Global => null,
     Pre  => Valid (S) and then Plan_OK (S, P) and then P.Kind = P_Have
             and then P.N = 0
             and then Buf (0) = Tag_Have and then Natural (Buf (O_G)) = G
             and then Wire_Key (Buf, O_Lo) = P.Lo
             and then Wire_Key (Buf, O_Hi) = P.Hi
             and then Natural (Buf (Elems_O_N)) = 0,
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

   --  O is the exact HAVE answer to M: HAVEs over [M.Lo, M.Hi) that offer
   --  only our elements that M does not list, and that offer each such
   --  element of ours in the range. This function has a quantifier, so its
   --  completion is in the private part.
   function Have_Exact (S : Snapshot; M : Message; O : Outbox) return Boolean with
     Global => null;

   --  Every RANGE in O is a sub-range of M's range, with strictly
   --  fewer of our elements (the measure of T7). This function is ghost
   --  and has a quantifier, so its completion is in the private part.
   function Shrinks (S : Snapshot; M : Message; O : Outbox) return Boolean with
     Ghost, Global => null,
     Pre => Valid (S) and then Key_Lt (M.Lo, M.Hi);

   --  The reply contract (DESIGN.md §8 "Replies"). It is quantifier-free,
   --  and it uses the quantified functions above:
   --    RANGE, equal count and fingerprint: the confirm.
   --    RANGE, in other cases: a reply group that tiles the range, with
   --      every plan exact. If we hold at most Ship_Threshold in the range,
   --      all plans are ELEMENTS. If not, all plans are RANGE children
   --      (each strictly smaller, Shrinks).
   --    ELEMENTS: the exact HAVE if we hold at most Ship_Threshold. If
   --      not, the exact split above.
   --    HAVE: no reply.
   function Answers (S : Snapshot; M : Message; O : Outbox) return Boolean is
     ((if M.Kind = M_Have then O.N = 0 else O.N >= 1 and then O.Reply)
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

   --  Respond, as a function of the snapshot and the message (so a
   --  contract can name the one reply that a message gets).
   type Reply is record
      Box : Outbox;
      Got : Delivery := No_Delivery;
   end record;

   function Reply_Of (S : Snapshot; M : Message) return Reply with
     Global => null,
     Pre    => Valid (S) and then Msg_OK (M),
     Post   => Outbox_OK (S, Reply_Of'Result.Box)
       and then Delivers (S, M, Reply_Of'Result.Got)
       and then Answers (S, M, Reply_Of'Result.Box)
       --  Well-founded split (the measure of T7).
       and then Shrinks (S, M, Reply_Of'Result.Box);

   procedure Respond
     (S       : Snapshot;
      M       : Message;
      Out_Box : out Outbox;
      Got     : out Delivery)
   with
     Global => null,
     Pre    => Valid (S) and then Msg_OK (M),
     Post   => Out_Box = Reply_Of (S, M).Box and then Got = Reply_Of (S, M).Got
       and then Outbox_OK (S, Out_Box)
       and then Delivers (S, M, Got)
       and then Answers (S, M, Out_Box)
       --  Well-founded split (the measure of T7).
       and then Shrinks (S, M, Out_Box);

   ----------------------------------------------------------------------
   --  The session state machine.
   ----------------------------------------------------------------------

   type Role  is (Initiator, Responder);
   type Phase is (Await_Open, Gate, Auth, Data, Done);

   Session_Msgs_Max : constant := 2 ** 29;
   subtype Msg_Counter is Natural range 0 .. Session_Msgs_Max;

   --  In a session, an honest peer sends at most these messages:
   --    * its OPEN and HELLO;
   --    * in each phase, its root RANGE and one reply group (<= 16
   --      messages) for each obligation that we send in that phase. (Each
   --      phase holds at most N_ours of our elements and N_peer of its
   --      elements.)
   --  Our obligations in a phase are our RANGEs and our ELEMENTS. Our
   --  RANGEs are <= 2 N_ours + 1: a laminar family of ranges with
   --  distinct non-empty sets of our elements, plus the root. Our ELEMENTS
   --  are <= 4 for each RANGE of the peer, so <= 4 (2 N_peer + 1). So one
   --  phase costs at most
   --  1 + 16 (2 N_ours + 1 + 4 (2 N_peer + 1)) = 128 N_peer + 32 N_ours + 81.
   --  The session, over the two phases and OPEN and HELLO, costs at most
   --  2 × (128 N_peer + 32 N_ours + 81) + 2.
   function Msg_Budget (Ours, Theirs : Elem_Count) return Msg_Counter is
     (256 * Theirs + 64 * Ours + 164);

   --  Before the HELLO exchange: the OPEN and HELLO of the peer.
   Pre_Gate_Budget : constant := 2;

   --  Weights of open obligations. Unit = lcm (1 .. 16).
   Unit        : constant := 720_720;
   Pending_Max : constant := 2 ** 52;
   type Pending_Units is range 0 .. Pending_Max;

   function Weight (G : Group_Size) return Pending_Units is
     (Pending_Units (Unit / G))
   with Pre => G >= 1;

   --  The RANGEs that we emit in replies, over the two phases (the count
   --  does not include the roots). Each phase has at most 2 |S| + 2.
   Range_Max : constant := 2 * (2 * Elem_Max + 2);
   subtype Range_Counter is Natural range 0 .. Range_Max;

   function Range_Budget (S : Snapshot) return Range_Counter is
     (2 * (2 * Count (S) + 2));

   --  The item bytes that we emit, over the two phases. Each phase has at
   --  most 8 × (frame bytes + 85 |S|).
   Ship_Factor : constant := 2 * 8;

   function Ship_Budget (S : Snapshot) return Byte_Total is
     (Ship_Factor * (Byte_Total (Frame_Bytes (S))
                     + Item_Overhead * Byte_Total (Count (S))));

   type Session is record
      R               : Role          := Responder;
      P               : Phase         := Await_Open;
      NS              : Id128;                  --  our collection
      Aborted         : Boolean       := False; --  ended by a foreign ns
      Hello_Sent      : Boolean       := False; --  Admit emitted our HELLO
      Peer_Hello_Seen : Boolean       := False; --  peer HELLO arrived
      Auth_Root_Seen  : Boolean       := False; --  the authorization root went
                                                --  out (initiator) / came in
                                                --  (responder)
      Our_N           : Elem_Count    := 0;     --  |S| at Admit
      Our_Digest      : Key256;                 --  digest of S at Admit
      Peer_Auth       : Elem_Count    := 0;     --  min (n_auth, Elem_Max)
      Peer_Data       : Elem_Count    := 0;     --  min (n_data, Elem_Max)
      Peer_Digest     : Key256;                 --  digest of the peer HELLO
      Msgs            : Msg_Counter   := 0;     --  messages accepted
      Budget          : Msg_Counter   := Pre_Gate_Budget;
      Pending         : Pending_Units := 0;     --  weight of our open obligations
      Ranges          : Range_Counter := 0;     --  RANGEs we emitted in replies
      Shipped         : Byte_Total    := 0;     --  item bytes we emitted
   end record;

   function Session_OK (Sess : Session) return Boolean is
     (Sess.Msgs <= Sess.Budget
      and then (if Sess.Aborted then Sess.P = Done)
      and then (if Sess.P in Await_Open | Gate then Sess.Budget = Pre_Gate_Budget)
      and then (case Sess.P is
                  when Await_Open =>
                    Sess.Msgs = 0 and then not Sess.Hello_Sent
                    and then not Sess.Peer_Hello_Seen
                    and then not Sess.Auth_Root_Seen and then Sess.Pending = 0,
                  when Gate =>
                    not (Sess.Hello_Sent and then Sess.Peer_Hello_Seen)
                    and then not Sess.Auth_Root_Seen and then Sess.Pending = 0,
                  when Auth =>
                    Sess.Hello_Sent and then Sess.Peer_Hello_Seen
                    and then (if Sess.R = Initiator then Sess.Auth_Root_Seen),
                  when Data =>
                    Sess.Hello_Sent and then Sess.Peer_Hello_Seen
                    and then Sess.Auth_Root_Seen,
                  when Done => True));

   --  The session ended without abort (on an in-order transport, this is
   --  exactly when it is over).
   function Complete (Sess : Session) return Boolean is
     (Sess.P = Done and then not Sess.Aborted);

   --  The claimed element count of the peer, as it goes into the budgets:
   --  min (min (n_auth, Elem_Max) + min (n_data, Elem_Max), Elem_Max).
   function Peer_Claim (Sess : Session) return Elem_Count is
     (if Sess.Peer_Auth + Sess.Peer_Data > Elem_Max then Elem_Max
      else Sess.Peer_Auth + Sess.Peer_Data);

   --  S is the snapshot that our HELLO described (its size and digest are
   --  the values that Admit recorded). The caller gives the snapshot of
   --  Admit to every later Receive and Next_Phase of the session.
   function Same_Snapshot (Sess : Session; S : Snapshot) return Boolean is
     (Count (S) = Sess.Our_N
      and then Sess.Our_Digest = Kome.Keys.To_Key256 (Range_Fp (S, 1, Count (S))))
   with Pre => Valid (S);

   --  The g = 0 messages that the responder accepts (D14): (a) the
   --  authorization root before it has one, or (b) the data root after the
   --  authorization root, with nothing that it asked open. Exact bounds,
   --  and RANGE only.
   function Root_OK (Sess : Session; M : Message) return Boolean is
     (Sess.R = Responder and then Sess.P = Auth and then M.Kind = M_Range
      and then ((not Sess.Auth_Root_Seen
                 and then M.Lo = Min_Key and then M.Hi = Data_Lo)
                or else (Sess.Auth_Root_Seen and then Sess.Pending = 0
                         and then M.Lo = Data_Lo and then M.Hi = Max_Key)));

   --  The state when the two HELLOs have passed. If the digests are equal,
   --  the session ends. If not, the phase is Auth, and the root RANGE of
   --  the initiator over the authorization range is open.
   function After_Hellos (S : Snapshot; Sess : Session; O : Outbox) return Boolean is
     (Sess.Hello_Sent and then Sess.Peer_Hello_Seen
      and then Sess.Budget = Msg_Budget (Sess.Our_N, Peer_Claim (Sess))
      and then (if Sess.Our_Digest = Sess.Peer_Digest then
                  Sess.P = Done and then not Sess.Aborted and then O.N = 0
                elsif Sess.R = Initiator then
                  Sess.P = Auth and then Sess.Auth_Root_Seen
                  and then Sess.Pending = Unit
                  and then Is_Root (S, O, Min_Key, Data_Lo)
                else
                  Sess.P = Auth and then not Sess.Auth_Root_Seen
                  and then Sess.Pending = 0 and then O.N = 0))
   with Pre => Valid (S);

   --  Our OPEN: ns and our root revocations (Voids (1 .. N_Voids)). Each
   --  is a 275-byte REVOKE frame that the founding key issued and that the
   --  caller selected (§8).
   procedure Start
     (Sess    : out Session;
      As      : Role;
      NS      : Id128;
      Voids   : Rv_Array;
      N_Voids : Rv_Count;
      Buf     : out Msg_Buffer;
      Len     : out Msg_Length)
   with
     Global => null,
     Post   => Session_OK (Sess) and then Sess.R = As and then Sess.NS = NS
               and then Sess.P = Await_Open and then not Sess.Aborted
               and then Sess.Msgs = 0 and then Sess.Pending = 0
               and then Sess.Budget = Pre_Gate_Budget
               and then Sess.Ranges = 0 and then Sess.Shipped = 0
               and then Len = Open_Len (N_Voids)
               and then Open_Wire_OK (Buf (0 .. Len - 1))
               and then Wire_Id128 (Buf, Open_O_NS) = NS
               and then Natural (Buf (Open_O_NRV)) = N_Voids
               and then (for all I in 1 .. N_Voids =>
                           Buf (Rv_At (I) .. Rv_At (I) + Rv_Frame_Len - 1) = Voids (I));

   --  Our HELLO, when the gate of the caller admits the peer: the counts
   --  of the two ranges, the digest of the full snapshot and our
   --  credential. Admit writes it to Buf (0 .. Len - 1). Send it before
   --  Out_Box. If the HELLO of the peer is already here, the HELLO
   --  exchange is over (After_Hellos; the root RANGE of the initiator is
   --  in Out_Box). Caller duty: the caller must take S after it applies
   --  the OPEN of the peer (and its credential, if it came first). S is
   --  the snapshot of the session.
   procedure Admit
     (Sess    : in out Session;
      S       : Snapshot;
      Cred    : Byte_Array;
      Buf     : out Msg_Buffer;
      Len     : out Msg_Length;
      Out_Box : out Outbox)
   with
     Global => null,
     Pre    => Valid (S) and then Session_OK (Sess)
               and then Sess.P = Gate and then not Sess.Hello_Sent
               and then Cred'Length <= Cred_Max,
     Post   => Session_OK (Sess) and then Outbox_OK (S, Out_Box)
               and then Sess = (Sess'Old with delta
                                  Hello_Sent     => True,
                                  Our_N          => Sess.Our_N,
                                  Our_Digest     => Sess.Our_Digest,
                                  P              => Sess.P,
                                  Budget         => Sess.Budget,
                                  Pending        => Sess.Pending,
                                  Auth_Root_Seen => Sess.Auth_Root_Seen)
               and then Same_Snapshot (Sess, S)
               and then Sess.Our_N = Count (S)
               and then Sess.Our_Digest = Kome.Keys.To_Key256 (Range_Fp (S, 1, Count (S)))
               and then Len = Hello_Fixed + Cred'Length and then Len <= Hello_Max_Len
               and then Hello_Wire_OK (Buf (0 .. Len - 1))
               and then Wire_U32 (Buf, Hello_O_NAuth) = Word (My_Count (S, Min_Key, Data_Lo))
               and then Wire_U32 (Buf, Hello_O_NData) = Word (My_Count (S, Data_Lo, Max_Key))
               and then Buf (Hello_O_Digest .. Hello_O_Digest + 31) = Range_Fp (S, 1, Count (S))
               and then Buf (Hello_Fixed .. Len - 1) = Cred
               and then (if Sess.Peer_Hello_Seen then After_Hellos (S, Sess, Out_Box)
                         else Sess.P = Gate and then Out_Box.N = 0
                              and then Sess.Budget = Sess'Old.Budget);

   --  The initiator, with nothing open in Auth: the data root RANGE.
   procedure Next_Phase
     (Sess    : in out Session;
      S       : Snapshot;
      Out_Box : out Outbox)
   with
     Global => null,
     Pre    => Valid (S) and then Session_OK (Sess)
               and then Sess.R = Initiator and then Sess.P = Auth
               and then Sess.Pending = 0 and then Same_Snapshot (Sess, S),
     Post   => Session_OK (Sess) and then Outbox_OK (S, Out_Box)
               and then Is_Root (S, Out_Box, Data_Lo, Max_Key)
               and then Sess = (Sess'Old with delta P => Data, Pending => Unit);

   type Session_Status is
     (S_OK,
      S_Malformed,     --  the bytes are not a message
      S_Unexpected,    --  a message this phase or our open obligations do not accept
      S_Limit,         --  a session budget would be exceeded
      S_Aborted);      --  an OPEN for another collection: the session is over (Done, Aborted)

   --  Receive can accept M: g = 0 only as the expected root (Root_OK). Any
   --  other g only as an answer to an obligation of ours that is still
   --  open.
   function Root_Or_Owed (Sess : Session; M : Message) return Boolean is
     (if M.G = 0 then Root_OK (Sess, M) else Sess.Pending >= Weight (M.G));

   --  The answer O to M stays within the budgets of the session.
   function Within_Budgets
     (Sess : Session; S : Snapshot; M : Message; O : Outbox) return Boolean
   is
     (Sess.Ranges + Num_Ranges (O) <= Range_Budget (S)
      and then Sess.Shipped + Item_Bytes (S, O) <= Ship_Budget (S)
      and then Sess.Pending - (if M.G = 0 then 0 else Weight (M.G))
                 + Unit * Pending_Units (Obligations (O)) <= Pending_Max)
   with Pre => Valid (S) and then Outbox_OK (S, O) and then Root_Or_Owed (Sess, M);

   --  The exact status that Receive returns, as a function of the session,
   --  the snapshot and the input. Every refusal has a characterisation, so
   --  a well-formed, expected message within the budgets is accepted.
   function Status_Of
     (Sess : Session; S : Snapshot; Input : Byte_Array) return Session_Status
   is
     (if Sess.P = Done then S_Unexpected
      elsif Input'Last < Input'First then S_Malformed
      elsif Input (Input'First) = Tag_Open then
        (if Sess.P /= Await_Open then S_Unexpected
         elsif Sess.Msgs = Sess.Budget then S_Limit
         elsif not Open_Wire_OK (Input) then S_Malformed
         elsif Wire_Id128 (Input, Input'First + Open_O_NS) /= Sess.NS then S_Aborted
         else S_OK)
      elsif Input (Input'First) = Tag_Hello then
        (if Sess.P /= Gate or else Sess.Peer_Hello_Seen then S_Unexpected
         elsif Sess.Msgs = Sess.Budget then S_Limit
         elsif not Hello_Wire_OK (Input) then S_Malformed
         else S_OK)
      elsif Sess.P not in Auth | Data then S_Unexpected
      elsif Sess.Msgs = Sess.Budget then S_Limit
      elsif not Decode_Of (Input).OK then S_Malformed
      elsif not Root_Or_Owed (Sess, Decode_Of (Input).M) then S_Unexpected
      elsif not Within_Budgets (Sess, S, Decode_Of (Input).M,
                                Reply_Of (S, Decode_Of (Input).M).Box)
      then S_Limit
      else S_OK)
   with Pre => Valid (S);

   --  Receive one message. The status is exactly Status_Of (the two halves
   --  of every "iff": a foreign ns aborts, and a well-formed expected
   --  message within the budgets is accepted). On S_Malformed, S_Unexpected
   --  and S_Limit, nothing changes. Receive delivers and offers elements
   --  only in Auth and Data, and only the HELLO exchange gets to these
   --  phases. Receive accepts g = 0 only as the expected root with exact
   --  bounds (Root_OK). M is the decoded message (Decode_Of (Input)), and
   --  the reply is Reply_Of (S, M). Open is the decoded OPEN and Peer is
   --  the decoded HELLO, each from the wire (for the content checks of the
   --  caller, see the header).
   procedure Receive
     (Sess    : in out Session;
      S       : Snapshot;
      Input   : Byte_Array;
      M       : out Message;
      Open    : out Open_Msg;
      Peer    : out Hello;
      Out_Box : out Outbox;
      Got     : out Delivery;
      Result  : out Session_Status)
   with
     Global => null,
     Pre    => Valid (S) and then Session_OK (Sess)
               and then (if Sess.Hello_Sent then Same_Snapshot (Sess, S)),
     Post   => Session_OK (Sess)
       and then Result = Status_Of (Sess'Old, S, Input)
       and then Sess.R = Sess'Old.R and then Sess.NS = Sess'Old.NS
       and then Sess.Our_N = Sess'Old.Our_N
       and then Sess.Our_Digest = Sess'Old.Our_Digest
       and then Outbox_OK (S, Out_Box)
       and then (if Result in S_Malformed | S_Unexpected | S_Limit then
                   Sess = Sess'Old and then Out_Box.N = 0 and then Got = No_Delivery)
       and then (if Sess'Old.P = Done then Result = S_Unexpected)
       and then (if Result = S_OK then
                   Sess.Msgs = Sess'Old.Msgs + 1 and then not Sess.Aborted)
       --  g = 0 iff the expected root. Receive never refuses a decoded
       --  g = 0 RANGE that Root_OK admits as unexpected (only a budget can
       --  refuse it). An accepted g = 0 is Root_OK (below).
       and then (if Result = S_Unexpected and then Sess'Old.P in Auth | Data
                   and then M.Kind = M_Range and then M.G = 0
                 then not Root_OK (Sess'Old, M))
       --  Elements only in Auth and Data.
       and then (if Result = S_OK and then M.Kind in M_Range | M_Elements | M_Have
                 then Sess'Old.P in Auth | Data)
       --  The OPEN: a foreign ns aborts. If not, the phase is Gate.
       and then (if Result = S_Aborted then
                   Sess'Old.P = Await_Open and then M.Kind = M_Open
                   and then Open_Wire_OK (Input) and then Open_Decoded (Input, Open)
                   and then Open.NS /= Sess'Old.NS
                   and then Sess = (Sess'Old with delta P => Done, Aborted => True)
                   and then Out_Box.N = 0 and then Got = No_Delivery)
       and then (if Result = S_OK and then Sess'Old.P = Await_Open then
                   M.Kind = M_Open and then Open.NS = Sess.NS
                   and then Open_Wire_OK (Input) and then Open_Decoded (Input, Open)
                   and then Sess = (Sess'Old with delta P => Gate,
                                                        Msgs => Sess'Old.Msgs + 1)
                   and then Out_Box.N = 0 and then Got = No_Delivery)
       --  The HELLO, once, in the gate.
       and then (if Result = S_OK and then Sess'Old.P = Gate then
                   M.Kind = M_Hello and then not Sess'Old.Peer_Hello_Seen
                   and then Hello_Wire_OK (Input) and then Hello_Decoded (Input, Peer)
                   and then Sess = (Sess'Old with delta
                                      Peer_Hello_Seen => True,
                                      Peer_Auth       => Sess.Peer_Auth,
                                      Peer_Data       => Sess.Peer_Data,
                                      Peer_Digest     => Sess.Peer_Digest,
                                      Msgs            => Sess'Old.Msgs + 1,
                                      P               => Sess.P,
                                      Budget          => Sess.Budget,
                                      Pending         => Sess.Pending,
                                      Auth_Root_Seen  => Sess.Auth_Root_Seen)
                   and then Sess.Peer_Digest = Kome.Keys.To_Key256 (Peer.Digest)
                   and then Sess.Peer_Auth = Claim (Peer.N_Auth)
                   and then Sess.Peer_Data = Claim (Peer.N_Data)
                   and then Got = No_Delivery
                   and then (if Sess.Hello_Sent then After_Hellos (S, Sess, Out_Box)
                             else Sess.P = Gate and then Out_Box.N = 0
                                  and then Sess.Budget = Sess'Old.Budget))
       --  RANGE / ELEMENTS / HAVE in Auth or Data: the answer is the
       --  answer of Respond, within the budgets. g = 0 only as the
       --  expected root.
       and then (if Result = S_OK and then Sess'Old.P in Auth | Data then
                   M.Kind in M_Range | M_Elements | M_Have
                   and then M = Decode_Of (Input).M
                   and then Decode_Facts (Input, M, True)
                   and then Msg_OK (M) and then Msg_In (M, Input)
                   and then (if M.G = 0 then Root_OK (Sess'Old, M))
                   and then Out_Box = Reply_Of (S, M).Box
                   and then Got = Reply_Of (S, M).Got
                   and then Delivers (S, M, Got)
                   and then Answers (S, M, Out_Box)
                   and then Shrinks (S, M, Out_Box)
                   and then Sess.Ranges = Sess'Old.Ranges + Num_Ranges (Out_Box)
                   and then Sess.Ranges <= Range_Budget (S)
                   and then Sess.Shipped = Sess'Old.Shipped + Item_Bytes (S, Out_Box)
                   and then Sess.Shipped <= Ship_Budget (S)
                   and then Sess.Pending =
                              Sess'Old.Pending
                              - (if M.G = 0 then 0 else Weight (M.G))
                              + Unit * Pending_Units (Obligations (Out_Box))
                   and then Sess.Auth_Root_Seen = (Sess'Old.Auth_Root_Seen or else M.G = 0)
                   and then Sess.P =
                              (if Sess'Old.P = Data
                                 or else (M.G = 0 and then Sess'Old.Auth_Root_Seen)
                               then (if Sess.Pending = 0 then Done else Data)
                               else Auth)
                   and then Sess = (Sess'Old with delta
                                      Msgs           => Sess'Old.Msgs + 1,
                                      P              => Sess.P,
                                      Pending        => Sess.Pending,
                                      Ranges         => Sess.Ranges,
                                      Shipped        => Sess.Shipped,
                                      Auth_Root_Seen => Sess.Auth_Root_Seen));

private

   type Kind_Array is array (Elem_Index range <>) of Kind_Code;
   type Id_Array   is array (Elem_Index range <>) of Id128;
   type Pos_Array  is array (Elem_Index range <>) of Positive;
   type Len_Array  is array (Elem_Index range <>) of Frame_Size;

   type Snapshot (Cap : Elem_Count; Pool_Cap : Pool_Size) is record
      N     : Elem_Count := 0;
      Used  : Pool_Size  := 0;
      Kinds : Kind_Array (1 .. Cap) := [others => 0];
      Ents  : Id_Array (1 .. Cap)   := [others => (others => 0)];
      FHs   : Kome.Digest.Hash_Array (1 .. Cap) := [others => (others => 0)];
      Hs    : Kome.Digest.Hash_Array (1 .. Cap) := [others => (others => 0)];
      Offs  : Pos_Array (1 .. Cap)  := [others => 1];
      Lens  : Len_Array (1 .. Cap)  := [others => 1];
      Pool  : Byte_Array (1 .. Pool_Cap) := [others => 0];
   end record
   with Dynamic_Predicate => Snapshot.N <= Snapshot.Cap
                             and then Snapshot.Used <= Snapshot.Pool_Cap;

   function Count (S : Snapshot) return Elem_Count is (S.N);

   function Frame_Bytes (S : Snapshot) return Pool_Size is (S.Used);

   function Key (S : Snapshot; I : Elem_Index) return Elem_Key is
     ((K => S.Kinds (I), Ent => S.Ents (I), FH => S.FHs (I), H => S.Hs (I)));

   function Frame_Len (S : Snapshot; I : Elem_Index) return Frame_Size is
     (S.Lens (I));

   function Frame (S : Snapshot; I : Elem_Index) return Byte_Array is
     (S.Pool (S.Offs (I) .. S.Offs (I) + S.Lens (I) - 1));

   function Frame_In_Pool (S : Snapshot; I : Elem_Index) return Boolean is
     (S.Offs (I) <= S.Used and then S.Lens (I) - 1 <= S.Used - S.Offs (I))
   with Pre => I <= S.Cap;

   function Valid (S : Snapshot) return Boolean is
     ((for all I in 1 .. S.N => S.Kinds (I) <= 4 and then Frame_In_Pool (S, I))
      and then (for all I in 1 .. S.N =>
                  (for all J in I + 1 .. S.N => Key_Lt (Key (S, I), Key (S, J)))));

   function Has_Room (S : Snapshot; L : Natural) return Boolean is
     (L <= S.Pool_Cap - S.Used);

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

   function Open_Frames (B : Byte_Array; O : Open_Msg) return Boolean is
     ((for all I in 1 .. O.N_RV => O.RV (I) = Open_Frame (B, I))
      and then (for all I in O.N_RV + 1 .. Rv_Max => O.RV (I) = Zero_Rv));

   function Cred_Canonical (H : Hello) return Boolean is
     (for all I in H.Cred_Len .. Cred_Max - 1 => H.Cred (I) = 0);

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
      and then (for all T in 1 .. M.N =>
                  M.Items (T).Key.K <= 4
                  and then In_Window (M.Items (T).Key, M.Lo, M.Hi))
      and then (for all T in 2 .. M.N =>
                  Key_Lt (M.Items (T - 1).Key, M.Items (T).Key)));

   function Msg_In (M : Message; Input : Byte_Array) return Boolean is
     (for all T in 1 .. M.N =>
        M.Items (T).Off >= Input'First
        and then M.Items (T).Off <= Input'Last
        and then Input'Last - M.Items (T).Off >= M.Items (T).Len - 1);

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
     ((for all T in 1 .. O.N =>
         O.P (T).Kind = P_Have
         and then O.P (T).Lo = M.Lo and then O.P (T).Hi = M.Hi
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
