--  Kome.Reconcile: the reconciliation session of one collection's frontier
--  (DESIGN.md §8, round three D12, D13, D14 and R2): the pre-gate OPEN,
--  the post-gate HELLO, and two range reconciliations, the authorization
--  range first and the data range second.
--
--  Elements are the records of F for one ns, keyed
--
--    kind:u8 ‖ ent[16] ‖ fh[32] ‖ h[32]          (81 bytes, §8)
--
--  with ROSTER = 0, REVOKE = 1, GRANT = 2, DEL = 3, PUT = 4, and ordered
--  bytewise. Inside the package a key is Elem_Key, a record of scalars and
--  word records (CONVENTIONS.md rule 1), and the bytewise order is Key_Lt,
--  a quantifier-free chain of word comparisons. That Key_Lt is exactly
--  byte-lexicographic order on the 81-byte wire key is proved
--  (Lemma_Key_Eq_Is_Bytewise, Lemma_Key_Lt_First_Difference, from the
--  Kome.Keys Id128 and Key256 laws). Authorization records sort first: the
--  key space splits at Data_Lo = 03 ‖ 0^80 into the authorization range
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
--  OPEN and HELLO are fixed-layout: Open_Wire_OK and Hello_Wire_OK are
--  quantifier-free, and Decode_Open / Decode_Hello accept exactly them.
--  A range is half-open, [lo, hi), with lo < hi. RANGE says "over my
--  elements in [lo, hi) the count and fingerprint are these". ELEMENTS says
--  "these (n <= Ship_Threshold) are ALL my elements in [lo, hi)". HAVE says
--  "these are elements in [lo, hi) you lacked"; an empty HAVE is the
--  explicit confirm. Keys in ELEMENTS and HAVE are strictly ascending, lie
--  in [lo, hi), and have kind <= 4; anything else is Malformed. Every field
--  has one width and the order of keys is fixed, so one message has one
--  encoding.
--
--  Content checks belong to the caller (the transport, phase 9), with
--  Kome.Records, never to this package, which sees frames as opaque bytes:
--    * OPEN (pre-gate, R2): each frame must satisfy
--      Kome.Records.Is_Founding_Revoke for this collection. The caller
--      verifies and applies only those whose subject is a signer it holds
--      and is not yet root-voided, skipping the rest unverified (which
--      bounds pre-gate work), and only then evaluates its gate.
--    * HELLO (post-gate, D13): the cred must be a ROSTER frame for which
--      Kome.Records.Roster_Lists_DH (cred, peer's Noise static key) holds;
--      otherwise the caller aborts the session. If it holds, the caller
--      decodes, verifies and applies it and re-evaluates its gate.
--    * ELEMENTS / HAVE items: the caller decodes and verifies each frame,
--      checks that its key is the one it was shipped under
--      (Key_Of (To_Header (R))), and applies it.
--    Every accepted frame is applied through Kome.Store.Put_Frame.
--  Nothing a lying peer puts in an OPEN or a HELLO is trusted here: the
--  counts enter the budgets only as min (claimed, Elem_Max), the digest
--  only decides whether the session ends early, and the frames are signed
--  records. Pre-gate work is rate-limited by the transport.
--
--  Session (D14, R2). Phases Await_Open, Gate, Auth, Data, Done.
--    * Start emits our OPEN (ns and our root revocations); P = Await_Open.
--    * Receive of the peer's OPEN: a foreign ns aborts the session
--      (S_Aborted, P = Done, Aborted); otherwise P = Gate and the decoded
--      OPEN goes back to the caller, who applies its frames (above).
--    * Admit: the caller calls it once its gate admits the peer; it emits
--      our HELLO (counts of the two ranges, the digest of the whole
--      snapshot, our credential). Caller duty: the snapshot passed to
--      Admit is taken after applying the peer's OPEN (and the peer's
--      credential, if its HELLO came first), and the same snapshot is
--      passed to every later Receive and Next_Phase of the session.
--    * Receive of the peer's HELLO (in Gate, before or after Admit): its
--      counts and digest are stored and the decoded HELLO goes back to
--      the caller (for the credential).
--    * When both HELLOs have passed (in Admit or in Receive): equal
--      digests end the session (Done, no further message; under A2 they
--      mean equal frontiers); otherwise P = Auth, and the initiator emits
--      the root RANGE (g = 0, [Min_Key, Data_Lo)) together with, and after,
--      its HELLO when the transition happens in Admit.
--    * The initiator, when nothing it asked is open in Auth, calls
--      Next_Phase, which emits the data root RANGE (g = 0, [Data_Lo,
--      Max_Key)) and moves to Data; in Data it is Done when nothing is
--      open. It never accepts g = 0.
--    * The responder accepts g = 0 only as (a) RANGE [Min_Key, Data_Lo) in
--      Auth before the authorization root, or (b) RANGE [Data_Lo, Max_Key)
--      in Auth after it with nothing it asked open, which moves it to
--      Data; in Data it is Done when nothing is open after a Receive.
--    * Every other g = 0 message (an ELEMENTS or HAVE with g = 0, other
--      bounds, a repeated root, the data root first or while something is
--      open), any RANGE, ELEMENTS or HAVE before Auth, and any message in
--      Done, is S_Unexpected and changes nothing (Root_OK, Receive's Post).
--  Receive's status is exactly Status_Of (session, snapshot, input), so
--  every refusal is characterised both ways: S_Malformed iff the decoder
--  for the tag refuses, S_Aborted iff a well-formed OPEN in Await_Open
--  names another ns, S_Limit iff a budget would be exceeded, and a
--  well-formed, expected message within the budgets is accepted. What
--  Receive returns is the wire's: M is Decode_Of (Input) (its head, kind,
--  count, fingerprint and n read from the input, Decode_Facts), the
--  reply is Reply_Of (S, M), and Open / Peer satisfy Open_Decoded /
--  Hello_Decoded. After Admit, every Receive and Next_Phase must be given
--  the snapshot of Admit (Same_Snapshot, a precondition).
--  Complete (Sess) holds when the session ended without abort.
--
--  Transport. The phase gate assumes an in-order transport (Noise over a
--  stream, DESIGN.md §8). Under loss, or if a root message is reordered
--  (a data root that overtakes the last authorization-phase reply is
--  refused), Complete is never reached and the caller times out and
--  restarts from OPEN; DESIGN.md §8 states this, so it is not a deviation.
--  Round 0 (module I, the invertible Bloom lookup table) runs once per
--  phase, at the start of Auth and at Next_Phase, when it is built; it is
--  not built here.
--
--  Obligations and replies. A RANGE or an ELEMENTS obliges its receiver to
--  answer; a HAVE obliges nothing. Every answer is a reply group of g >= 1
--  messages (Respond's Out_Box), and each message of the group carries g.
--  The only messages with g = 0 are the initiator's two root RANGEs. Each
--  side keeps the weight of its open obligations (Session.Pending): sending
--  a RANGE or an ELEMENTS adds Unit; receiving a message of a group of g
--  removes Unit / g (Unit = lcm (1 .. 16), so a whole group removes exactly
--  Unit, in any order). A message that would remove more than is open is
--  refused, so a peer can only answer what it was asked.
--
--  The responder (Respond), on RANGE (lo, hi, fp, count): our elements in
--  [lo, hi) are located (Window). If their count and fingerprint
--  (Kome.Digest, fp over the h of each element) equal the message's, the
--  range is confirmed with an empty HAVE; else if there are at most
--  Ship_Threshold of them they are shipped as ELEMENTS; else [lo, hi) is
--  split 16-way (Split_Fanout) over our elements, and each child goes out
--  as a RANGE with our count and fingerprint. On ELEMENTS: every element we
--  lack is delivered to the caller (exactly those); then if we hold at most
--  Ship_Threshold in the range, exactly the ones the peer lacked go back as
--  HAVE (an empty HAVE if none), else the range is split as above. On
--  HAVE: every element we lack is delivered. Respond's Post pins the kind
--  of every reply (All_Kind), that a non-confirm reply tiles the range and
--  never contains a HAVE, and that every plan is exact (Exact_Plans: a
--  RANGE carries our true count and fingerprint, an ELEMENTS all of our
--  elements of its range).
--
--  Message size (D12). Every emitted message is at most Max_Message_Len
--  bytes (Kome, §8), proved (Plan_OK, Plan_Len): a RANGE is 200 bytes, an
--  OPEN at most Open_Max_Len = 4 144 and a HELLO at most Hello_Max_Len =
--  10 142. An ELEMENTS whose frames do not fit is split further, into one
--  ELEMENTS per element over a sub-range that holds that element alone, and
--  a HAVE that does not fit is sent as one HAVE per element. One element
--  always fits: a frame is at most Kome.Records.Frame_Max = 41 136 bytes,
--  below Frame_Ship_Max = Max_Message_Len - 165 - 85 = 48 902 (checked at
--  compile time), so a snapshot never refuses a well-formed frame as
--  Snap_Too_Large (Lemma_Frame_Ships); the check stays as a defence.
--
--  Well-founded split (the measure of T7). Each RANGE a responder emits is
--  a sub-range of the range it answers with strictly fewer of the
--  responder's elements (Respond's Post, Shrinks, measured by My_Count).
--  An ELEMENTS reply covers the same range with the same counts; it is
--  answered only by HAVE (never answered) or by a split whose children
--  have strictly fewer of the answerer's elements. So T7's measure is
--  lexicographic: (μ (r), k) with μ ([lo, hi)) = |F_A ∩ [lo, hi)| +
--  |F_B ∩ [lo, hi)| and k = 1 for a RANGE, 0 for an ELEMENTS; every reply
--  decreases it. The implementation splits balanced (child counts ⌊n/16⌋
--  or ⌈n/16⌉; tested, not proved, see the limitations below). Given that,
--  a chain of replies in one phase holds at most s = ⌈log₁₆ N_A⌉ +
--  ⌈log₁₆ N_B⌉ splits and, as a split can cost two one-way messages
--  (ELEMENTS, then the split), at most 2s + 3 one-way messages per phase;
--  that bound is part of T7, not proved.
--
--  Duplicate deliveries. The snapshot is frozen for the session, so when
--  we split a range after receiving ELEMENTS, the peer ships the same
--  elements again on the children and they are delivered again. Applying a
--  record is idempotent, so this costs bandwidth, not correctness;
--  "delivered" means "not in our snapshot". The ship budget bounds it.
--
--  Budgets (a hostile peer cannot draw unbounded traffic), each counted
--  over both phases. The messages accepted are at most Msg_Budget (our
--  |S|, the peer's claimed count), an upper bound on what an honest peer
--  sends (derivation at Msg_Budget); the RANGEs we emit in replies are at
--  most Range_Budget (S) = 2 × (2 |S| + 2) (per phase, the ranges of an
--  honest session form a laminar family in which ours have distinct,
--  non-empty sets of our elements); the item bytes we emit are at most
--  Ship_Budget (S) = 2 × 8 × (frame bytes + 85 |S|) (an honest phase ships
--  each of our elements at most ⌈log₁₆ N_peer⌉ + 1 <= 6 times). The two
--  root RANGEs are not replies and are not counted in Ranges. A message
--  that would exceed a budget is refused with S_Limit. The counts are
--  defined, not just bounded: Num_Ranges, Obligations and Item_Bytes equal
--  the sums Ranges_Upto, Obligations_Upto and Items_Upto over the reply's
--  plans, so Pending, Ranges, Shipped, the Done transitions and every
--  budget check in Receive's Post are stated over the reply's true counts.
--
--  Tested, not proved (stated limitations): T7 (termination and
--  convergence; the two-phase session test converges two replicas); that
--  Decode accepts every ELEMENTS / HAVE carrying items (it is proved to
--  accept every RANGE and every confirm); the item and frame bytes inside
--  an encoded ELEMENTS / HAVE (Encode's Post states the head and the item
--  count, the round trip is tested; Decode_Facts states the head, the
--  kind, a RANGE's count and fingerprint and an ELEMENTS / HAVE's n as the
--  wire's, not the item keys and frame places, which are tested); that
--  splits are balanced (child counts ⌊n/16⌋ or
--  ⌈n/16⌉: Answers and Shrinks state only that each child is strictly
--  smaller, so the log₁₆ round bound above is part of T7); the
--  honest-session derivations behind Msg_Budget, Range_Budget and
--  Ship_Budget (they are arithmetic over the protocol's executions, a
--  T7-level argument).
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

   --  The kind byte. Elements use 0 .. 4 (Kome.Headers.Kind's codes,
   --  ROSTER 0, REVOKE 1, GRANT 2, DEL 3, PUT 4); range bounds may use any
   --  byte, so Max_Key (kind 255) is above every element.
   type Kind_Code is range 0 .. 255 with Size => 8;
   subtype Elem_Kind is Kind_Code range 0 .. 4;

   type Elem_Key is record
      K   : Kind_Code := 0;
      Ent : Id128;
      FH  : Key256;
      H   : Key256;
   end record;

   Key_Wire_Len : constant := 1 + 16 + 32 + 32;   --  81

   --  Unsigned big-endian order on an Id128 (Kome.Keys owns it).
   function Id_Lt (A, B : Id128) return Boolean renames Kome.Keys.Id_Lt;

   --  kind ‖ ent ‖ fh ‖ h compared bytewise.
   function Key_Lt (A, B : Elem_Key) return Boolean is
     (A.K < B.K or else (A.K = B.K and then
      (Kome.Keys.Id_Lt (A.Ent, B.Ent) or else (A.Ent = B.Ent and then
      (Lt (A.FH, B.FH) or else (A.FH = B.FH and then
       Lt (A.H, B.H)))))));

   function Key_Le (A, B : Elem_Key) return Boolean is (not Key_Lt (B, A));

   --  The whole key space: every element key k has Min_Key <= k < Max_Key.
   --  Data_Lo splits it: authorization records (kinds 0 .. 2) lie in
   --  [Min_Key, Data_Lo), data records (kinds 3, 4) in [Data_Lo, Max_Key).
   Min_Key : constant Elem_Key :=
     (K => 0, Ent => (others => 0), FH => (others => 0), H => (others => 0));
   Data_Lo : constant Elem_Key :=
     (K => 3, Ent => (others => 0), FH => (others => 0), H => (others => 0));
   Max_Key : constant Elem_Key :=
     (K => 255, Ent => (others => 0), FH => (others => 0), H => (others => 0));

   --  The element key of a record's header (§8: kind ‖ ent ‖ field hash ‖
   --  h). Kind'Pos is the kind's code (Kome.Headers).
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

   --  OPEN (pre-gate, R2): 5 ‖ proto ‖ ns[16] ‖ n_rv ‖ n_rv × frame[275].
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
   --  cred. No register value crosses the wire, and no proto (OPEN has it).
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

   --  The size of a reply group; 0 marks a root RANGE (not a reply).
   subtype Group_Size is Natural range 0 .. Split_Fanout;

   --  Element counts and indices: the records one replica holds for one
   --  collection. Kome.Digest.Elem_Max is Kome.Frontier.Held_Max, the one
   --  constant both the frontier and reconciliation use (§8 HELLO).
   Elem_Max : constant := Kome.Digest.Elem_Max;
   pragma Compile_Time_Error
     (Elem_Max /= Kome.Frontier.Held_Max,
      "DESIGN.md §8: Elem_Max must be Kome.Frontier.Held_Max");
   subtype Elem_Count is Kome.Digest.Elem_Count;
   subtype Elem_Index is Kome.Digest.Elem_Index;
   subtype Lo_Bound   is Kome.Digest.Lo_Bound;

   ----------------------------------------------------------------------
   --  Reading the wire. Quantifier-free, so public (rule 2): Decode's
   --  and Encode's Posts are stated with them.
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
   --  bytewise"): equal keys iff equal bytes, and the first differing
   --  byte decides. Together these say Key_Lt is exactly the
   --  byte-lexicographic order of the encodings (Put_Key writes Wire_Key).
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
   --  Snapshot: our elements for one session, sorted strictly ascending,
   --  each with its frame. Cap elements, Pool_Cap bytes of frames.
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

   --  Sorted strictly ascending (pairwise), kinds <= 4, frames in the
   --  pool. Quantified, so completed in the private part (rule 2).
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

   --  Append the next element; keys must come in strictly ascending order.
   --  On refusal nothing changes (T13).
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
   --  bytes) is never Snap_Too_Large (with Append's Post).
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

   --  The ghost measure of T7: how many of our elements lie in [Lo, Hi).
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

   --  A sub-run S .. E of a covered window, bounded by the parent's ends
   --  or by the neighbouring elements, is covered by exactly those
   --  bounds, and is a non-empty sub-range of the parent. This is what
   --  makes every split child a well-formed, strictly smaller range.
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
   --  h of our elements First .. Last, by Kome.Digest.
   ----------------------------------------------------------------------

   function Range_Fp (S : Snapshot; First : Lo_Bound; Last : Elem_Count)
     return Hash256
   with Global => null,
        Pre    => First <= Last + 1 and then Last <= Count (S);

   ----------------------------------------------------------------------
   --  Plans: messages to send, by reference into the snapshot. Encode
   --  turns one into bytes. (OPEN and HELLO are not plans: Start and Admit
   --  write them into a buffer.)
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

   --  The wire size of one item and of the item parts of a plan.
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

   --  A plan refers to real elements, has a proper range, and ELEMENTS
   --  lists at most Ship_Threshold. Quantified (HAVE), so opaque.
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

   --  Bytes Encode will produce for P.
   function Plan_Len (S : Snapshot; P : Plan) return Positive is
     (case P.Kind is
        when P_Range    => Range_Len,
        when P_Elements => Elems_Fixed + Run_Size (S, P.First, P.Last),
        when P_Have     => Elems_Fixed + List_Size (S, P.Items, P.N))
   with Pre => Plan_Shape (S, P);

   --  Everything a receiver checks, and the size bound.
   function Plan_OK (S : Snapshot; P : Plan) return Boolean with
     Global => null,
     Post   => (if Plan_OK'Result then
                  Plan_Shape (S, P) and then Plan_Len (S, P) <= Max_Message_Len);

   subtype Out_Count is Natural range 0 .. Split_Fanout;
   type Plan_Array is array (1 .. Split_Fanout) of Plan;

   --  What to send: the plans P (1 .. N). If Reply, the plans are one
   --  reply group (each carries g = N); else g = 0 (a root RANGE).
   type Outbox is record
      Reply : Boolean   := False;
      N     : Out_Count := 0;
      P     : Plan_Array;
   end record;

   function Group (O : Outbox) return Group_Size is
     (if O.Reply then O.N else 0);

   --  Every plan is Plan_OK. Opaque (quantified).
   function Outbox_OK (S : Snapshot; O : Outbox) return Boolean with
     Global => null;

   procedure Lemma_Outbox_OK (S : Snapshot; O : Outbox; T : Positive) with
     Ghost, Global => null,
     Pre  => Outbox_OK (S, O) and then T <= O.N,
     Post => Plan_OK (S, O.P (T));

   --  The plans of O tile [Lo, Hi): the first starts at Lo, the last ends
   --  at Hi, each ends where the next begins. With each plan's cover,
   --  every one of our elements in [Lo, Hi) is in exactly one reply.
   function Tiles (O : Outbox; Lo, Hi : Elem_Key) return Boolean with
     Global => null;

   --  Every plan of O is of kind K (so a reply of one kind never mixes in
   --  a HAVE). Opaque (quantified).
   function All_Kind (O : Outbox; K : Out_Kind) return Boolean with
     Global => null;

   procedure Lemma_All_Kind (O : Outbox; K : Out_Kind; T : Positive) with
     Ghost, Global => null,
     Pre  => All_Kind (O, K) and then T <= O.N,
     Post => O.P (T).Kind = K;

   --  Every RANGE and ELEMENTS plan of O is exact: its run First .. Last is
   --  our window of its range, so a RANGE carries our true count and
   --  fingerprint and an ELEMENTS carries all of our elements in its
   --  range. Opaque (quantified); its meaning is Lemma_Exact_Plan.
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

   --  A root RANGE over [Lo, Hi): one RANGE, not a reply (g = 0), carrying
   --  our whole window of the range.
   function Is_Root (S : Snapshot; O : Outbox; Lo, Hi : Elem_Key) return Boolean is
     (O.N = 1 and then not O.Reply and then O.P (1).Kind = P_Range
      and then O.P (1).Lo = Lo and then O.P (1).Hi = Hi
      and then O.P (1).First = Window (S, Lo, Hi).First
      and then O.P (1).Last = Window (S, Lo, Hi).Last)
   with Pre => Valid (S) and then Key_Lt (Lo, Hi);

   --  How many plans are RANGE, are obligations (RANGE or ELEMENTS), and
   --  how many item bytes the ELEMENTS and HAVE plans carry.
   type Byte_Total is range 0 .. 2 ** 40;

   --  The item bytes of one plan: the encoded items of an ELEMENTS or
   --  HAVE (Plan_Len less the fixed part), none for a RANGE.
   function Plan_Items (S : Snapshot; P : Plan) return Natural is
     (case P.Kind is
        when P_Range    => 0,
        when P_Elements => Run_Size (S, P.First, P.Last),
        when P_Have     => List_Size (S, P.Items, P.N))
   with Pre => Plan_Shape (S, P);

   --  The defining sums over the plans P (1 .. T), bounded recursion
   --  (T <= Split_Fanout). Ghost; completed in the private part. The
   --  accounting functions below equal them at T = O.N, so Pending,
   --  Ranges, Shipped and every budget check in Receive's Post are stated
   --  over the true counts of the reply.
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
   --  buffer; an item records where (Off, absolute index) and how long.
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

   --  What a decoded RANGE / ELEMENTS / HAVE satisfies. Opaque.
   function Msg_OK (M : Message) return Boolean with
     Global => null,
     Post   => (if Msg_OK'Result then
                  M.Kind in M_Range | M_Elements | M_Have
                  and then Key_Lt (M.Lo, M.Hi)
                  and then (if M.Kind = M_Range then M.N = 0));

   --  Every frame of M lies inside Input. Opaque.
   function Msg_In (M : Message; Input : Byte_Array) return Boolean with
     Global => null;

   --  The two shapes Decode is proved to accept (the others it accepts are
   --  stated by Msg_OK and tested): a RANGE, and an ELEMENTS or HAVE with
   --  no items (the confirm). Quantifier-free.
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

   --  M's count and fingerprint are the ones the well-formed RANGE B
   --  carries.
   function Range_Fields (B : Byte_Array; M : Message) return Boolean is
     (M.Count = Natural (Wire_U32 (B, B'First + Range_O_Count))
      and then M.Fp = B (B'First + Range_O_Fp .. B'First + Range_O_Fp + 31))
   with Pre => Range_Wire_OK (B);

   --  What Decode states about its result (M, OK) for Input. When it
   --  accepts: M is well-formed, its head is the wire's (g, lo, hi), its
   --  kind is the tag's, a RANGE is a well-formed RANGE whose count and
   --  fingerprint are the wire's, and an ELEMENTS / HAVE has the wire's n.
   --  Completeness: every well-formed RANGE and confirm is accepted.
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
   --  message an input decodes to).
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
   --  OPEN (pre-gate, R2). Canonical: frames past N_RV are zero.
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

   --  Where frame I starts, relative to the message.
   function Rv_At (I : Rv_Index) return Natural is
     (Open_Fixed + Rv_Frame_Len * (I - 1));

   --  B is a well-formed OPEN: tag, proto, n_rv <= Rv_Max and the length
   --  it gives. Quantifier-free.
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

   --  The frames of O are B's, and the unused ones are zero. Quantified,
   --  so opaque (rule 2): completed in the private part, its meaning is
   --  Lemma_Open_Frames.
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
   --  n_rv > Rv_Max or a length mismatch is Malformed), and the fields it
   --  returns are the wire's, canonically.
   procedure Decode_Open
     (Input : Byte_Array;
      O     : out Open_Msg;
      OK    : out Boolean)
   with
     Global => null,
     Post   => OK = Open_Wire_OK (Input)
               and then (if OK then Open_Decoded (Input, O));

   ----------------------------------------------------------------------
   --  HELLO (post-gate, D13). Canonical: cred bytes past Cred_Len are zero.
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
   --  it gives. Quantifier-free.
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

   --  The cred bytes of H past Cred_Len are zero. Quantified, so opaque
   --  (rule 2): completed in the private part, its meaning is
   --  Lemma_Cred_Zero.
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
   --  Cred_Max or a length mismatch is Malformed), and the fields it
   --  returns are the wire's, canonically.
   procedure Decode_Hello
     (Input : Byte_Array;
      H     : out Hello;
      OK    : out Boolean)
   with
     Global => null,
     Post   => OK = Hello_Wire_OK (Input)
               and then (if OK then Hello_Decoded (Input, H));

   --  A claimed count, as it enters the budgets: min (claimed, Elem_Max).
   function Claim (W : Word) return Elem_Count is
     (if W > Elem_Max then Elem_Max else Natural (W));

   ----------------------------------------------------------------------
   --  Encoding RANGE / ELEMENTS / HAVE. Every message is at most
   --  Max_Message_Len bytes (T13, the bounds obligation, for messages):
   --  Plan_OK bounds Plan_Len, and Encode's length is Plan_Len.
   ----------------------------------------------------------------------

   --  G is the group size the plan is sent with (Group (Out_Box)).
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

   --  The round trip, for the shapes Decode is proved to accept: what
   --  Encode emits for a RANGE, and for a confirm, is accepted.
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

   --  Which items of a message are delivered to the caller.
   type Delivery is array (Item_Index) of Boolean;
   No_Delivery : constant Delivery := [others => False];

   --  K is one of our elements. Opaque.
   function Held (S : Snapshot; K : Elem_Key) return Boolean with
     Global => null;

   --  D delivers exactly the items of M we do not hold. Opaque.
   function Delivers (S : Snapshot; M : Message; D : Delivery) return Boolean with
     Global => null;

   --  Our count and fingerprint over [M.Lo, M.Hi) are M's.
   function Confirms (S : Snapshot; M : Message) return Boolean is
     (Window (S, M.Lo, M.Hi).Last + 1 - Window (S, M.Lo, M.Hi).First = M.Count
      and then Range_Fp (S, Window (S, M.Lo, M.Hi).First,
                            Window (S, M.Lo, M.Hi).Last) = M.Fp)
   with Pre => Valid (S) and then Key_Lt (M.Lo, M.Hi);

   --  O is the exact HAVE answer to M: HAVEs over [M.Lo, M.Hi) offering
   --  only our elements M does not list, and every such element of ours in
   --  the range. Opaque.
   function Have_Exact (S : Snapshot; M : Message; O : Outbox) return Boolean with
     Global => null;

   --  Every RANGE in O is a sub-range of M's with strictly fewer of our
   --  elements (T7's measure). Ghost, opaque.
   function Shrinks (S : Snapshot; M : Message; O : Outbox) return Boolean with
     Ghost, Global => null,
     Pre => Valid (S) and then Key_Lt (M.Lo, M.Hi);

   --  The reply contract (DESIGN.md §8 "Replies"), quantifier-free over
   --  the opaque views above:
   --    RANGE, equal count and fingerprint: the confirm.
   --    RANGE otherwise: a reply group that tiles the range, every plan
   --      exact, all ELEMENTS if we hold at most Ship_Threshold in the
   --      range, else all RANGE children (each strictly smaller, Shrinks).
   --    ELEMENTS: the exact HAVE if we hold at most Ship_Threshold, else
   --      the exact split above.
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
   --  contract can name the one reply a message gets).
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
       --  Well-founded split (T7's measure).
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
       --  Well-founded split (T7's measure).
       and then Shrinks (S, M, Out_Box);

   ----------------------------------------------------------------------
   --  The session state machine.
   ----------------------------------------------------------------------

   type Role  is (Initiator, Responder);
   type Phase is (Await_Open, Gate, Auth, Data, Done);

   Session_Msgs_Max : constant := 2 ** 29;
   subtype Msg_Counter is Natural range 0 .. Session_Msgs_Max;

   --  The messages an honest peer sends in a session are at most its
   --  OPEN and HELLO, and per phase (each phase holds at most N_ours of
   --  our elements and N_peer of its) its root RANGE plus one reply group
   --  (<= 16 messages) per obligation we send in that phase. Our
   --  obligations in a phase are our RANGEs (<= 2 N_ours + 1: a laminar
   --  family of ranges with distinct non-empty sets of our elements, plus
   --  the root) and our ELEMENTS (<= 4 per RANGE of the peer, <= 4 (2 N_peer
   --  + 1)). So one phase costs at most
   --  1 + 16 (2 N_ours + 1 + 4 (2 N_peer + 1)) = 128 N_peer + 32 N_ours + 81,
   --  and the session, counted over both phases plus OPEN and HELLO, at most
   --  2 × (128 N_peer + 32 N_ours + 81) + 2.
   function Msg_Budget (Ours, Theirs : Elem_Count) return Msg_Counter is
     (256 * Theirs + 64 * Ours + 164);

   --  Before the HELLO exchange: the peer's OPEN and HELLO.
   Pre_Gate_Budget : constant := 2;

   --  Weights of open obligations. Unit = lcm (1 .. 16).
   Unit        : constant := 720_720;
   Pending_Max : constant := 2 ** 52;
   type Pending_Units is range 0 .. Pending_Max;

   function Weight (G : Group_Size) return Pending_Units is
     (Pending_Units (Unit / G))
   with Pre => G >= 1;

   --  RANGEs we emit in replies, over both phases (the roots are not
   --  counted): per phase at most 2 |S| + 2.
   Range_Max : constant := 2 * (2 * Elem_Max + 2);
   subtype Range_Counter is Natural range 0 .. Range_Max;

   function Range_Budget (S : Snapshot) return Range_Counter is
     (2 * (2 * Count (S) + 2));

   --  Item bytes we emit, over both phases: per phase at most 8 × (frame
   --  bytes + 85 |S|).
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
      Peer_Hello_Seen : Boolean       := False; --  the peer's HELLO arrived
      Auth_Root_Seen  : Boolean       := False; --  the authorization root went
                                                --  out (initiator) / came in
                                                --  (responder)
      Our_N           : Elem_Count    := 0;     --  |S| at Admit
      Our_Digest      : Key256;                 --  digest of S at Admit
      Peer_Auth       : Elem_Count    := 0;     --  min (n_auth, Elem_Max)
      Peer_Data       : Elem_Count    := 0;     --  min (n_data, Elem_Max)
      Peer_Digest     : Key256;                 --  the peer's HELLO digest
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

   --  The session ended without abort (on an in-order transport, exactly
   --  when it is over).
   function Complete (Sess : Session) return Boolean is
     (Sess.P = Done and then not Sess.Aborted);

   --  The peer's claimed element count as it enters the budgets:
   --  min (min (n_auth, Elem_Max) + min (n_data, Elem_Max), Elem_Max).
   function Peer_Claim (Sess : Session) return Elem_Count is
     (if Sess.Peer_Auth + Sess.Peer_Data > Elem_Max then Elem_Max
      else Sess.Peer_Auth + Sess.Peer_Data);

   --  S is the snapshot our HELLO described (its size and digest are the
   --  ones Admit recorded). The caller passes the snapshot of Admit to
   --  every later Receive and Next_Phase of the session.
   function Same_Snapshot (Sess : Session; S : Snapshot) return Boolean is
     (Count (S) = Sess.Our_N
      and then Sess.Our_Digest = Kome.Keys.To_Key256 (Range_Fp (S, 1, Count (S))))
   with Pre => Valid (S);

   --  The g = 0 messages the responder accepts (D14): (a) the
   --  authorization root before it has one, or (b) the data root after it,
   --  with nothing it asked open. Exact bounds; RANGE only.
   function Root_OK (Sess : Session; M : Message) return Boolean is
     (Sess.R = Responder and then Sess.P = Auth and then M.Kind = M_Range
      and then ((not Sess.Auth_Root_Seen
                 and then M.Lo = Min_Key and then M.Hi = Data_Lo)
                or else (Sess.Auth_Root_Seen and then Sess.Pending = 0
                         and then M.Lo = Data_Lo and then M.Hi = Max_Key)));

   --  The state once both HELLOs have passed: equal digests end the
   --  session; otherwise Auth, and the initiator's root RANGE over the
   --  authorization range is open.
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

   --  Our OPEN: ns and our root revocations (Voids (1 .. N_Voids), each a
   --  275-byte founding-issued REVOKE frame the caller selected, §8).
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

   --  Our HELLO, once the caller's gate admits the peer: the counts of the
   --  two ranges, the digest of the whole snapshot and our credential
   --  (written to Buf (0 .. Len - 1); send it before Out_Box). If the
   --  peer's HELLO has already arrived, the HELLO exchange is over
   --  (After_Hellos; the initiator's root RANGE is in Out_Box).
   --  Caller duty: S is taken after applying the peer's OPEN (and its
   --  credential, if it came first), and is the snapshot of the session.
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

   --  The initiator, nothing open in Auth: the data root RANGE.
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

   --  M may be taken in: g = 0 only as the expected root (Root_OK), any
   --  other g only as an answer to an obligation of ours still open.
   function Root_Or_Owed (Sess : Session; M : Message) return Boolean is
     (if M.G = 0 then Root_OK (Sess, M) else Sess.Pending >= Weight (M.G));

   --  Answering M with O stays within the session's budgets.
   function Within_Budgets
     (Sess : Session; S : Snapshot; M : Message; O : Outbox) return Boolean
   is
     (Sess.Ranges + Num_Ranges (O) <= Range_Budget (S)
      and then Sess.Shipped + Item_Bytes (S, O) <= Ship_Budget (S)
      and then Sess.Pending - (if M.G = 0 then 0 else Weight (M.G))
                 + Unit * Pending_Units (Obligations (O)) <= Pending_Max)
   with Pre => Valid (S) and then Outbox_OK (S, O) and then Root_Or_Owed (Sess, M);

   --  The status Receive returns, exactly, as a function of the session,
   --  the snapshot and the input: every refusal is characterised, so a
   --  well-formed, expected message within the budgets is accepted.
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

   --  Receive one message. The status is exactly Status_Of (both halves
   --  of every "iff": a foreign ns aborts, a well-formed expected message
   --  within the budgets is accepted). On S_Malformed, S_Unexpected and
   --  S_Limit nothing changes. Elements are delivered and offered only in
   --  Auth and Data, which only the HELLO exchange reaches; g = 0 is
   --  accepted only as the expected root with exact bounds (Root_OK).
   --  M is the decoded message (Decode_Of (Input)) and the reply is
   --  Reply_Of (S, M); Open is the decoded OPEN and Peer the decoded HELLO,
   --  each the wire's (for the caller's content checks, see the header).
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
       --  g = 0 iff the expected root: a decoded g = 0 RANGE that Root_OK
       --  admits is never refused as unexpected (only a budget can refuse
       --  it), and an accepted g = 0 is Root_OK (below).
       and then (if Result = S_Unexpected and then Sess'Old.P in Auth | Data
                   and then M.Kind = M_Range and then M.G = 0
                 then not Root_OK (Sess'Old, M))
       --  Elements only in Auth and Data.
       and then (if Result = S_OK and then M.Kind in M_Range | M_Elements | M_Have
                 then Sess'Old.P in Auth | Data)
       --  The OPEN: a foreign ns aborts; otherwise on to the gate.
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
       --  RANGE / ELEMENTS / HAVE in Auth or Data: answered as Respond
       --  answers, within the budgets; g = 0 only as the expected root.
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

   --  K is one of M's item keys.
   function In_Msg (M : Message; K : Elem_Key) return Boolean is
     (for some T in 1 .. M.N => M.Items (T).Key = K);

   --  Our element K is offered by one of O's HAVEs.
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
