--  Kome.Reconcile: range-based set reconciliation of one collection's
--  frontier (DESIGN.md §8) and the session HELLO that joins the grow-only
--  registers before any element is offered (DESIGN.md §4, A6).
--
--  Elements are the records of F for one ns, keyed
--
--    kind:u8 ‖ ent[16] ‖ fh[32] ‖ h[32]          (81 bytes, §8)
--
--  and ordered bytewise. Inside the package a key is Elem_Key, a record of
--  scalars and word records (CONVENTIONS.md rule 1), and the bytewise
--  order is Key_Lt, a quantifier-free chain of word comparisons (each word
--  compared as an unsigned big-endian integer is its four bytes compared
--  lexicographically: Kome.Keys.Lemma_Lt_Is_Lexicographic).
--
--  Messages (all integers big-endian):
--
--    HELLO     1 ‖ maxceil:u48 ‖ |F|:u32 ‖ n:u16 ‖ r:u16 ‖ W[n][32] ‖ roots_ever[r][32]
--    RANGE     2 ‖ g:u8 ‖ lo[81] ‖ hi[81] ‖ count:u32 ‖ fp[32]
--    ELEMENTS  3 ‖ g:u8 ‖ lo[81] ‖ hi[81] ‖ n:u8 ‖ n × (key[81] ‖ flen:u32 ‖ frame)
--    HAVE      4 ‖ g:u8 ‖ lo[81] ‖ hi[81] ‖ n:u8 ‖ n × (key[81] ‖ flen:u32 ‖ frame)
--
--  A range is half-open, [lo, hi), with lo < hi. RANGE says "over my
--  elements in [lo, hi) the count and fingerprint are these". ELEMENTS says
--  "these (n <= Ship_Threshold) are ALL my elements in [lo, hi)". HAVE says
--  "these are elements in [lo, hi) you lacked"; an empty HAVE is the
--  explicit confirm. Keys in ELEMENTS and HAVE are strictly ascending, lie
--  in [lo, hi), and have kind <= 3; HELLO's two key lists are strictly
--  ascending; anything else is Malformed. Every field has one width and
--  the order of keys is fixed, so one message has one encoding.
--
--  Obligations and replies. A RANGE or an ELEMENTS obliges its receiver to
--  answer; a HAVE obliges nothing. Every answer is a reply group of g >= 1
--  messages (Respond's Out_Box), and each message of the group carries g.
--  The only message with g = 0 is the initiator's root RANGE. Each side
--  keeps the weight of its open obligations (Session.Pending): sending a
--  RANGE or an ELEMENTS adds Unit; receiving a message of a group of g
--  removes Unit / g (Unit = lcm (1 .. 16), so a whole group removes exactly
--  Unit, in any order). A message that would remove more than is open is
--  refused, so a peer can only answer what it was asked. Complete (Sess)
--  holds when nothing is open: on a transport without loss or duplication
--  (Noise XX over a stream, §8) it is reached exactly when the session is
--  over. Under loss it is never reached: the caller times out and starts a
--  new session from the root (the recovery DESIGN.md §8 "loss costs rounds"
--  relies on; recorded as a deviation to be written into §10).
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
--  HAVE: every element we lack is delivered.
--
--  Message size. Every emitted message is at most Max_Message_Len bytes
--  (Kome, §8), proved (Plan_OK, Plan_Len). A RANGE is 200 bytes and a
--  HELLO at most 43 023. An ELEMENTS whose frames do not fit is split
--  further, into one ELEMENTS per element over a sub-range that holds that
--  element alone, and a HAVE that does not fit is sent as one HAVE per
--  element. One element always fits, because a snapshot refuses a frame
--  longer than Frame_Ship_Max = Max_Message_Len - 165 - 85 = 48 902 bytes.
--  NOTE (reported, DESIGN decision needed): DESIGN.md §2 allows a
--  65 535-byte value, whose frame (Kome.Records.Frame_Max = 65 712) does
--  not fit in one 48 KiB message; §8 has no chunking. Such a record is
--  refused by Append (Snap_Too_Large) and cannot be reconciled.
--
--  Well-founded split (the measure of T7). Each RANGE a responder emits is
--  a sub-range of the range it answers with strictly fewer of the
--  responder's elements (Respond's Post, Shrinks, measured by My_Count).
--  An ELEMENTS reply covers the same range with the same counts; it is
--  answered only by HAVE (never answered) or by a split whose children
--  have strictly fewer of the answerer's elements. So T7's measure is
--  lexicographic: (μ (r), k) with μ ([lo, hi)) = |F_A ∩ [lo, hi)| +
--  |F_B ∩ [lo, hi)| and k = 1 for a RANGE, 0 for an ELEMENTS; every reply
--  decreases it. Splits are balanced (child counts ⌊n/16⌋ or ⌈n/16⌉), so a
--  chain of replies holds at most s = ⌈log₁₆ N_A⌉ + ⌈log₁₆ N_B⌉ splits and,
--  as a split can cost two one-way messages (ELEMENTS, then the split),
--  at most 2s + 3 one-way messages after the HELLOs. T7 (termination, and
--  convergence to F(F_A ∪ F_B)) is NOT proved here.
--
--  Duplicate deliveries. The snapshot is frozen for the session, so when
--  we split a range after receiving ELEMENTS, the peer ships the same
--  elements again on the children and they are delivered again. Applying a
--  record is idempotent, so this costs bandwidth, not correctness;
--  "delivered" means "not in our snapshot". The ship budget below bounds it.
--
--  Session (DESIGN.md §4 "every session's HELLO carries (maxceil, W,
--  roots_ever) and each side joins them componentwise (max, ∪, ∪) before
--  any element is offered"). The initiator sends HELLO and waits
--  (Hello_Sent); on the responder's HELLO it joins the registers and sends
--  the root RANGE over [Min_Key, Max_Key). The responder waits
--  (Await_Hello); on the initiator's HELLO it joins and answers HELLO. Only
--  then (Ready) are RANGE, ELEMENTS and HAVE accepted, so no element is
--  delivered or offered before the join (Receive's Post). Anything else is
--  refused with a Session_Status and changes nothing. There is no per-peer
--  state beyond the session.
--
--  Budgets (a hostile peer cannot draw unbounded traffic). Per session:
--  the messages accepted are at most Msg_Budget (our |F|, the peer's |F|),
--  an upper bound on what an honest peer sends (derivation at Msg_Budget);
--  the RANGEs we emit are at most Range_Budget (S) = 2 |S| + 2 (in an
--  honest session the ranges form a laminar family in which ours have
--  distinct, non-empty sets of our elements); the item bytes we emit are
--  at most Ship_Budget (S) = 8 × (frame bytes + 85 |S|) (an honest session
--  ships each of our elements at most ⌈log₁₆ N_peer⌉ + 1 <= 6 times). A
--  message that would exceed a budget is refused with S_Limit.
--
--  Registers. Kome.Registers exports no Join, no way to enumerate W, no
--  roots_ever, and Add_Writer's Post does not bound what it adds. So:
--  (a) Join applies the peer's HELLO with Raise_Ceiling and one Add_Writer
--  per key, and checks at run time the bound Add_Writer does not state
--  (at most one new writer, none if the key was already there), refusing
--  with J_Fault and restoring the registers if it ever fails; that makes
--  the upper bound Count (R) <= Count (R'Old) + Fresh (R'Old, H) provable.
--  Since Count is the number of distinct writers (Kome.Registers' body),
--  that bound, Extends (R'Old, R) and Has_All (R, H) say W' = W ∪ H.W
--  exactly. (b) Encode_Hello takes our writer list from the caller, with
--  the Pre that it lists Count (R) distinct (ascending) keys all in W, i.e.
--  exactly W under the same reading of Count. (c) roots_ever is carried
--  in HELLO (Roots_Ever_Max, a bound DESIGN.md does not set) and handed to
--  the caller in Receive's Peer; it is not joined here. (Reported.)
--
--  Trust. A HELLO's register values are not authenticated (DESIGN.md §4
--  derives maxceil and W from signed ROSTERs; reported for a DESIGN
--  decision). Receive joins them only when the caller passes Join_Regs
--  (e.g. a peer authenticated as a root device); otherwise the session
--  proceeds with the registers unchanged.
--
--  Elements and records. A frame is opaque here: the caller decodes and
--  verifies it (Kome.Records), checks that its key is the one it was
--  shipped under (Key_Of (To_Header (R))), and applies it (Kome.Frontier).
pragma Ada_2022;
with Kome.Headers;   use Kome.Headers;
with Kome.Registers; use Kome.Registers;
with Kome.Digest;
with Kome.Keys;
package Kome.Reconcile with SPARK_Mode is

   ----------------------------------------------------------------------
   --  Element keys and their order (DESIGN.md §8).
   ----------------------------------------------------------------------

   --  The kind byte. Elements use 0 .. 3 (Kome.Headers.Kind's codes);
   --  range bounds may use any byte, so Max_Key (kind 255) is above every
   --  element.
   type Kind_Code is range 0 .. 255 with Size => 8;
   subtype Elem_Kind is Kind_Code range 0 .. 3;

   type Elem_Key is record
      K   : Kind_Code := 0;
      Ent : Id128;
      FH  : Key256;
      H   : Key256;
   end record;

   Key_Wire_Len : constant := 1 + 16 + 32 + 32;   --  81

   --  Unsigned big-endian order on an Id128.
   function Id_Lt (A, B : Id128) return Boolean is
     (A.W0 < B.W0 or else (A.W0 = B.W0 and then
      (A.W1 < B.W1 or else (A.W1 = B.W1 and then
      (A.W2 < B.W2 or else (A.W2 = B.W2 and then
       A.W3 < B.W3))))));

   --  kind ‖ ent ‖ fh ‖ h compared bytewise.
   function Key_Lt (A, B : Elem_Key) return Boolean is
     (A.K < B.K or else (A.K = B.K and then
      (Id_Lt (A.Ent, B.Ent) or else (A.Ent = B.Ent and then
      (Lt (A.FH, B.FH) or else (A.FH = B.FH and then
       Lt (A.H, B.H)))))));

   function Key_Le (A, B : Elem_Key) return Boolean is (not Key_Lt (B, A));

   --  The whole key space: every element key k has Min_Key <= k < Max_Key.
   Min_Key : constant Elem_Key :=
     (K => 0, Ent => (others => 0), FH => (others => 0), H => (others => 0));
   Max_Key : constant Elem_Key :=
     (K => 255, Ent => (others => 0), FH => (others => 0), H => (others => 0));

   --  The element key of a record's header (§8: kind ‖ ent ‖ field hash ‖ h).
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

   --  HELLO. roots_ever (DESIGN.md §6) has no bound in DESIGN.md; 256
   --  keeps a HELLO with Writers_Max writers within Max_Message_Len.
   Roots_Ever_Max : constant := 256;
   subtype Root_Count is Natural range 0 .. Roots_Ever_Max;

   Hello_O_Ceil  : constant := 1;
   Hello_O_FCnt  : constant := 7;
   Hello_O_N     : constant := 11;
   Hello_O_R     : constant := 13;
   Hello_Fixed   : constant := 15;
   Hello_Max_Len : constant := Hello_Fixed + 32 * (Writers_Max + Roots_Ever_Max);  --  43 023

   function Hello_Len (N : Writer_Count; R : Root_Count) return Positive is
     (Hello_Fixed + 32 * (Natural (N) + R));

   subtype Frame_Size is Positive range 1 .. Frame_Ship_Max;
   subtype Msg_Length is Natural range 0 .. Max_Message_Len;
   subtype Msg_Buffer is Byte_Array (0 .. Max_Message_Len - 1);

   subtype Item_Count is Natural range 0 .. Ship_Threshold;
   subtype Item_Index is Positive range 1 .. Ship_Threshold;

   --  The size of a reply group; 0 marks the root RANGE (not a reply).
   subtype Group_Size is Natural range 0 .. Split_Fanout;

   --  Element counts and indices: the records one replica holds for one
   --  collection (Kome.Frontier.Held_Max, as Kome.Digest).
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

   function Wire_U48 (B : Byte_Array; P : Natural) return U48 is
     ((U48 (B (P)) * 256 + U48 (B (P + 1))) * 2 ** 32 + U48 (Wire_U32 (B, P + 2)))
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
       FH  => Wire_Key256 (B, P + 17),
       H   => Wire_Key256 (B, P + 49)))
   with Pre => P >= B'First and then P <= B'Last
               and then B'Last - P >= Key_Wire_Len - 1;

   --  The I-th 32-byte key of a list at B (B'First + Rel ..). Indexed by
   --  I, so that quantified facts about a key list trigger on I.
   function Wire_Key_At (B : Byte_Array; Rel : Natural; I : Positive) return Key256 is
     (Wire_Key256 (B, B'First + Rel + 32 * (I - 1)))
   with Pre => Rel <= Max_Message_Len and then I <= Writers_Max + Roots_Ever_Max
               and then B'Last >= B'First
               and then B'Last - B'First >= Rel + 32 * I - 1;

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

   --  Sorted strictly ascending (pairwise), kinds <= 3, frames in the
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
      Snap_Bad_Kind,    --  kind > 3
      Snap_Too_Large,   --  frame empty or longer than Frame_Ship_Max
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
       and then (Result = Snap_OK) =
                (K.K <= 3
                 and then F'Length in Frame_Size
                 and then (Count (S'Old) = 0
                           or else Key_Lt (Key (S'Old, Count (S'Old)), K))
                 and then Count (S'Old) < S.Cap
                 and then Has_Room (S'Old, F'Length));

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
   --  turns one into bytes. (Our HELLO is not a plan: Outbox.Hello asks
   --  the caller to send it with Encode_Hello.)
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

   --  What to send: our HELLO (Hello), then the plans P (1 .. N). If Reply,
   --  the plans are one reply group (each carries g = N); else g = 0.
   type Outbox is record
      Hello : Boolean   := False;
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

   --  The explicit confirm: one empty HAVE over [Lo, Hi).
   function Is_Confirm (O : Outbox; Lo, Hi : Elem_Key) return Boolean is
     (O.N = 1 and then O.P (1).Kind = P_Have and then O.P (1).N = 0
      and then O.P (1).Lo = Lo and then O.P (1).Hi = Hi);

   --  How many plans are RANGE, are obligations (RANGE or ELEMENTS), and
   --  how many item bytes the ELEMENTS and HAVE plans carry.
   type Byte_Total is range 0 .. 2 ** 40;

   function Num_Ranges (O : Outbox) return Out_Count with
     Global => null,
     Post   => Num_Ranges'Result <= O.N;

   function Obligations (O : Outbox) return Out_Count with
     Global => null,
     Post   => Obligations'Result <= O.N;

   function Item_Bytes (S : Snapshot; O : Outbox) return Byte_Total with
     Global => null,
     Pre    => Outbox_OK (S, O),
     Post   => Item_Bytes'Result <= Byte_Total (Split_Fanout * Max_Message_Len);

   ----------------------------------------------------------------------
   --  Received messages, decoded. Frames stay in the input buffer; an
   --  item records where (Off, absolute index) and how long.
   ----------------------------------------------------------------------

   type Msg_Kind is (M_Hello, M_Range, M_Elements, M_Have);

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
      W_Full : Boolean    := False;             --  HELLO: peer writers dropped at Writers_Max
   end record;

   --  What a decoded RANGE / ELEMENTS / HAVE satisfies. Opaque.
   function Msg_OK (M : Message) return Boolean with
     Global => null,
     Post   => (if Msg_OK'Result then
                  M.Kind /= M_Hello and then Key_Lt (M.Lo, M.Hi)
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
      and then Wire_U32 (B, B'First + Range_O_Count) <= Kome.Digest.Elem_Max);

   function Empty_Wire_OK (B : Byte_Array) return Boolean is
     (B'Length = Elems_Fixed
      and then (B (B'First) = Tag_Elements or else B (B'First) = Tag_Have)
      and then B (B'First + O_G) <= Split_Fanout
      and then Key_Lt (Wire_Key (B, B'First + O_Lo), Wire_Key (B, B'First + O_Hi))
      and then B (B'First + Elems_O_N) = 0);

   procedure Decode
     (Input  : Byte_Array;
      M      : out Message;
      OK     : out Boolean)
   with
     Global => null,
     Post   =>
       (if OK then
          Msg_OK (M) and then Msg_In (M, Input)
          and then Input'Length >= Elems_Fixed
          and then M.G = Natural (Input (Input'First + O_G))
          and then M.Lo = Wire_Key (Input, Input'First + O_Lo)
          and then M.Hi = Wire_Key (Input, Input'First + O_Hi))
       --  Completeness: every well-formed RANGE and confirm is accepted.
       and then (if Range_Wire_OK (Input) then
                   OK and then M.Kind = M_Range
                   and then M.Count = Natural (Wire_U32 (Input, Input'First + Range_O_Count))
                   and then M.Fp = Input (Input'First + Range_O_Fp .. Input'First + Range_O_Fp + 31))
       and then (if Empty_Wire_OK (Input) then
                   OK and then M.N = 0
                   and then M.Kind = (if Input (Input'First) = Tag_Elements
                                      then M_Elements else M_Have));

   type Writer_List is array (Positive range <>) of Key256;

   --  Strictly ascending. Opaque.
   function Ascending (W : Writer_List) return Boolean with Global => null;

   type Hello is record
      Ceil  : U48          := 0;
      F_Cnt : Elem_Count   := 0;
      N     : Writer_Count := 0;
      W     : Writer_List (1 .. Writers_Max) := [others => (others => 0)];
      R     : Root_Count   := 0;
      Roots : Writer_List (1 .. Roots_Ever_Max) := [others => (others => 0)];
   end record;

   --  B is a well-formed HELLO: the header's bounds, the length the
   --  counts give, and both key lists strictly ascending. Opaque.
   function Hello_Wire_OK (B : Byte_Array) return Boolean with Global => null;

   --  Decode_Hello accepts exactly the well-formed HELLOs, and the fields
   --  it returns are the wire's.
   procedure Decode_Hello
     (Input : Byte_Array;
      H     : out Hello;
      OK    : out Boolean)
   with
     Global => null,
     Post   => OK = Hello_Wire_OK (Input)
       and then (if OK then
                   Input'Length >= Hello_Fixed
                   and then H.Ceil = Wire_U48 (Input, Input'First + Hello_O_Ceil)
                   and then H.F_Cnt = Natural (Wire_U32 (Input, Input'First + Hello_O_FCnt))
                   and then Natural (H.N) = Wire_U16 (Input, Input'First + Hello_O_N)
                   and then H.R = Wire_U16 (Input, Input'First + Hello_O_R)
                   and then Input'Length = Hello_Len (H.N, H.R)
                   and then (for all I in 1 .. Natural (H.N) =>
                               H.W (I) = Wire_Key_At (Input, Hello_Fixed, I))
                   and then Ascending (H.W (1 .. Natural (H.N)))
                   and then Ascending (H.Roots (1 .. H.R)));

   ----------------------------------------------------------------------
   --  Encoding. Every message is at most Max_Message_Len bytes (T13, the
   --  bounds obligation, for messages): Plan_OK bounds Plan_Len, and
   --  Encode's length is Plan_Len.
   ----------------------------------------------------------------------

   --  Every key of W is in the register's W. Opaque.
   function All_In_W (R : Register_File; W : Writer_List) return Boolean with
     Global => null;

   --  Our HELLO. The ceiling is the register's; the writer list must be
   --  Count (R) distinct (ascending) keys of W, i.e. exactly W since Count
   --  counts distinct writers (Kome.Registers cannot enumerate W).
   procedure Encode_Hello
     (R     : Register_File;
      F_Cnt : Elem_Count;
      W     : Writer_List;
      Roots : Writer_List;
      Buf   : out Msg_Buffer;
      Len   : out Msg_Length)
   with
     Global => null,
     Pre    => W'Length = Natural (Kome.Registers.Count (R))
               and then Ascending (W) and then All_In_W (R, W)
               and then Roots'Length <= Roots_Ever_Max and then Ascending (Roots),
     Post   => Len = Hello_Len (Kome.Registers.Count (R), Roots'Length)
               and then Len <= Hello_Max_Len
               and then Buf (0) = Tag_Hello
               and then Wire_U48 (Buf, Hello_O_Ceil) = Ceil (R)
               and then Wire_U32 (Buf, Hello_O_FCnt) = Word (F_Cnt)
               and then Wire_U16 (Buf, Hello_O_N) = W'Length
               and then Wire_U16 (Buf, Hello_O_R) = Roots'Length
               and then (for all I in 1 .. W'Length =>
                           Wire_Key_At (Buf, Hello_Fixed, I) = W (W'First + (I - 1)));

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
   --  The HELLO join (DESIGN.md §4; T4 exchange clause, T4' monotone):
   --  maxceil := max (ours, theirs); W := W ∪ theirs.
   ----------------------------------------------------------------------

   --  Every peer writer is in R's W. Opaque.
   function Has_All (R : Register_File; H : Hello) return Boolean with
     Global => null;

   --  How many of H's writers R lacks (ghost; a recursive count).
   function Fresh (R : Register_File; H : Hello) return Natural with
     Ghost, Global => null,
     Post => Fresh'Result <= Natural (H.N);

   type Join_Status is
     (J_OK,         --  joined: every peer writer is in W
      J_W_Full,     --  joined, but W reached Writers_Max and dropped peer keys (§7)
      J_Fault);     --  Kome.Registers.Add_Writer broke the bound checked here; R unchanged

   --  The join. Upper bound: at most Fresh more writers than before, so
   --  (Count counting distinct writers) nothing outside W ∪ H.W enters.
   procedure Join (R : in out Register_File; H : Hello; Result : out Join_Status) with
     Global => null,
     Post   =>
       (if Result = J_Fault then R = R'Old
        else Ceil (R) = U48'Max (Ceil (R'Old), H.Ceil)
             and then Extends (R'Old, R)
             and then Kome.Registers.Count (R) >= Kome.Registers.Count (R'Old)
             and then Natural (Kome.Registers.Count (R))
                        <= Natural (Kome.Registers.Count (R'Old)) + Fresh (R'Old, H)
             and then (if Result = J_OK then Has_All (R, H)
                       else Kome.Registers.Count (R) = Writers_Max));

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

   procedure Respond
     (S       : Snapshot;
      M       : Message;
      Out_Box : out Outbox;
      Got     : out Delivery)
   with
     Global => null,
     Pre    => Valid (S) and then Msg_OK (M),
     Post   => Outbox_OK (S, Out_Box)
       and then not Out_Box.Hello
       and then Delivers (S, M, Got)
       --  RANGE and ELEMENTS are always answered, by one reply group;
       --  HAVE never is.
       and then (if M.Kind = M_Have then Out_Box.N = 0
                 else Out_Box.N >= 1 and then Out_Box.Reply)
       --  RANGE: confirm iff equal count and fingerprint; else the reply
       --  (ELEMENTS, or a split) tiles the range.
       and then (if M.Kind = M_Range then
                   (if Confirms (S, M) then Is_Confirm (Out_Box, M.Lo, M.Hi)
                    else Tiles (Out_Box, M.Lo, M.Hi)))
       --  ELEMENTS: the exact HAVE if we hold at most Ship_Threshold in
       --  the range, else a split that tiles it.
       and then (if M.Kind = M_Elements then
                   (if My_Count (S, M.Lo, M.Hi) <= Ship_Threshold
                    then Have_Exact (S, M, Out_Box)
                    else Tiles (Out_Box, M.Lo, M.Hi)))
       --  Well-founded split (T7's measure).
       and then Shrinks (S, M, Out_Box);

   ----------------------------------------------------------------------
   --  The session state machine.
   ----------------------------------------------------------------------

   type Role  is (Initiator, Responder);
   type Phase is (Await_Hello, Hello_Sent, Ready);

   Session_Msgs_Max : constant := 2 ** 28;
   subtype Msg_Counter is Natural range 0 .. Session_Msgs_Max;

   --  The messages an honest peer sends in a session, HELLO included, are
   --  at most 1 + its root RANGE + one reply group (<= 16 messages) per
   --  obligation we send. Our obligations are our RANGEs (<= 2 N_ours + 1:
   --  a laminar family of ranges with distinct non-empty sets of our
   --  elements, plus the root) and our ELEMENTS (<= 4 per RANGE of the
   --  peer, <= 4 (2 N_peer + 1)). So at most
   --  2 + 16 (2 N_ours + 1 + 4 (2 N_peer + 1)) = 128 N_peer + 32 N_ours + 82.
   function Msg_Budget (Ours, Theirs : Elem_Count) return Msg_Counter is
     (128 * Theirs + 32 * Ours + 83);

   --  Weights of open obligations. Unit = lcm (1 .. 16).
   Unit        : constant := 720_720;
   Pending_Max : constant := 2 ** 52;
   type Pending_Units is range 0 .. Pending_Max;

   function Weight (G : Group_Size) return Pending_Units is
     (Pending_Units (Unit / G))
   with Pre => G >= 1;

   Range_Max : constant := 2 * Kome.Digest.Elem_Max + 2;
   subtype Range_Counter is Natural range 0 .. Range_Max;

   function Range_Budget (S : Snapshot) return Range_Counter is
     (2 * Count (S) + 2);

   Ship_Factor : constant := 8;

   function Ship_Budget (S : Snapshot) return Byte_Total is
     (Ship_Factor * (Byte_Total (Frame_Bytes (S))
                     + Item_Overhead * Byte_Total (Count (S))));

   type Session is record
      R       : Role          := Responder;
      P       : Phase         := Await_Hello;
      Msgs    : Msg_Counter   := 0;    --  messages accepted
      Budget  : Msg_Counter   := 1;    --  messages this session may accept
      Pending : Pending_Units := 0;    --  weight of our open obligations
      Ranges  : Range_Counter := 0;    --  RANGEs we emitted
      Shipped : Byte_Total    := 0;    --  item bytes we emitted
   end record;

   function Session_OK (Sess : Session) return Boolean is
     (Sess.Msgs <= Sess.Budget
      and then (case Sess.P is
                  when Await_Hello => Sess.R = Responder and then Sess.Msgs = 0,
                  when Hello_Sent  => Sess.R = Initiator and then Sess.Msgs = 0,
                  when Ready       => Sess.Msgs >= 1));

   --  Nothing we asked is unanswered: the session is over (on a transport
   --  without loss or duplication).
   function Complete (Sess : Session) return Boolean is
     (Sess.P = Ready and then Sess.Pending = 0 and then Sess.Msgs >= 2);

   --  The initiator's first act is its HELLO (Out_Box.Hello).
   procedure Start (Sess : out Session; As : Role; Out_Box : out Outbox) with
     Global => null,
     Post   => Session_OK (Sess) and then Sess.R = As and then Sess.Msgs = 0
               and then Sess.Pending = 0
               and then Out_Box.N = 0 and then Out_Box.Hello = (As = Initiator)
               and then Sess.P = (if As = Initiator then Hello_Sent else Await_Hello);

   type Session_Status is
     (S_OK,
      S_Malformed,     --  the bytes are not a message
      S_Unexpected,    --  a message this phase or our open obligations do not accept
      S_Limit,         --  a session budget would be exceeded
      S_Fault);        --  the register join failed its run-time check (Join)

   --  Receive one message. On any refusal nothing changes. The registers
   --  change only on the HELLO, by the join (when Join_Regs); elements are
   --  delivered and offered only in Ready, which only the HELLO reaches.
   --  Peer is the decoded HELLO (for roots_ever, which is not joined here).
   procedure Receive
     (Sess      : in out Session;
      S         : Snapshot;
      R         : in out Register_File;
      Join_Regs : Boolean;
      Input     : Byte_Array;
      M         : out Message;
      Peer      : out Hello;
      Out_Box   : out Outbox;
      Got       : out Delivery;
      Result    : out Session_Status)
   with
     Global => null,
     Pre    => Valid (S) and then Session_OK (Sess),
     Post   => Session_OK (Sess)
       and then Sess.R = Sess'Old.R
       and then Outbox_OK (S, Out_Box)
       and then (if Result /= S_OK then
                   Sess = Sess'Old and then R = R'Old
                   and then Out_Box.N = 0 and then not Out_Box.Hello
                   and then Got = No_Delivery)
       and then (if Result = S_OK then Sess.Msgs = Sess'Old.Msgs + 1)
       --  The HELLO: the registers are joined (W exactly W ∪ peer W, up
       --  to Writers_Max) or, untrusted, left alone; nothing is delivered.
       and then (if Sess'Old.P /= Ready and then Result = S_OK then
                   M.Kind = M_Hello and then Sess.P = Ready
                   and then Got = No_Delivery
                   and then (if Join_Regs then
                               Ceil (R) = U48'Max (Ceil (R'Old), Peer.Ceil)
                               and then Extends (R'Old, R)
                               and then Natural (Kome.Registers.Count (R))
                                          <= Natural (Kome.Registers.Count (R'Old))
                                             + Fresh (R'Old, Peer)
                               and then (if M.W_Full
                                         then Kome.Registers.Count (R) = Writers_Max
                                         else Has_All (R, Peer))
                             else R = R'Old)
                   and then (if Sess'Old.P = Await_Hello then
                               Out_Box.Hello and then Out_Box.N = 0
                               and then Sess.Pending = 0
                             else not Out_Box.Hello and then not Out_Box.Reply
                                  and then Out_Box.N = 1
                                  and then Out_Box.P (1).Kind = P_Range
                                  and then Out_Box.P (1).Lo = Min_Key
                                  and then Out_Box.P (1).Hi = Max_Key
                                  and then Sess.Pending = Unit))
       --  After the HELLO: the registers are untouched and every message
       --  is answered as Respond answers it, within the budgets.
       and then (if Sess'Old.P = Ready then
                   Sess.P = Ready and then R = R'Old
                   and then (if Result = S_OK then
                               M.Kind /= M_Hello
                               and then Msg_OK (M) and then Msg_In (M, Input)
                               and then not Out_Box.Hello
                               and then Delivers (S, M, Got)
                               and then (if M.Kind = M_Have then Out_Box.N = 0
                                         else Out_Box.N >= 1 and then Out_Box.Reply)
                               and then (if M.Kind = M_Range then
                                           (if Confirms (S, M)
                                            then Is_Confirm (Out_Box, M.Lo, M.Hi)
                                            else Tiles (Out_Box, M.Lo, M.Hi)))
                               and then (if M.Kind = M_Elements then
                                           (if My_Count (S, M.Lo, M.Hi) <= Ship_Threshold
                                            then Have_Exact (S, M, Out_Box)
                                            else Tiles (Out_Box, M.Lo, M.Hi)))
                               and then Shrinks (S, M, Out_Box)
                               and then Sess.Ranges = Sess'Old.Ranges + Num_Ranges (Out_Box)
                               and then Sess.Ranges <= Range_Budget (S)
                               and then Sess.Shipped = Sess'Old.Shipped + Item_Bytes (S, Out_Box)
                               and then Sess.Shipped <= Ship_Budget (S)
                               and then Sess.Pending =
                                          Sess'Old.Pending
                                          - (if M.G = 0 then 0 else Weight (M.G))
                                          + Unit * Pending_Units (Obligations (Out_Box))));

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
     ((for all I in 1 .. S.N => S.Kinds (I) <= 3 and then Frame_In_Pool (S, I))
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

   function Msg_OK (M : Message) return Boolean is
     (M.Kind /= M_Hello
      and then Key_Lt (M.Lo, M.Hi)
      and then (if M.Kind = M_Range then M.N = 0)
      and then (for all T in 1 .. M.N =>
                  M.Items (T).Key.K <= 3
                  and then In_Window (M.Items (T).Key, M.Lo, M.Hi))
      and then (for all T in 2 .. M.N =>
                  Key_Lt (M.Items (T - 1).Key, M.Items (T).Key)));

   function Msg_In (M : Message; Input : Byte_Array) return Boolean is
     (for all T in 1 .. M.N =>
        M.Items (T).Off >= Input'First
        and then M.Items (T).Off <= Input'Last
        and then Input'Last - M.Items (T).Off >= M.Items (T).Len - 1);

   function Ascending (W : Writer_List) return Boolean is
     (for all I in W'Range =>
        (if I > W'First then Lt (W (I - 1), W (I))));

   --  The header of a HELLO: its bounds, and the length its counts give.
   function Hello_Ok_Header (B : Byte_Array) return Boolean is
     (B'Last >= B'First
      and then B'Last - B'First >= Hello_Fixed - 1
      and then B (B'First) = Tag_Hello
      and then Wire_U32 (B, B'First + Hello_O_FCnt) <= Kome.Digest.Elem_Max
      and then Wire_U16 (B, B'First + Hello_O_N) <= Writers_Max
      and then Wire_U16 (B, B'First + Hello_O_R) <= Roots_Ever_Max
      and then B'Last - B'First
                 = Hello_Fixed - 1 + 32 * (Wire_U16 (B, B'First + Hello_O_N)
                                           + Wire_U16 (B, B'First + Hello_O_R)));

   --  The N 32-byte keys at B (B'First + Rel ..) are strictly ascending.
   function Wire_Ascending (B : Byte_Array; Rel, N : Natural) return Boolean is
     (for all I in 2 .. N => Lt (Wire_Key_At (B, Rel, I - 1), Wire_Key_At (B, Rel, I)))
   with Pre => N <= Writers_Max + Roots_Ever_Max and then Rel <= Max_Message_Len
               and then (N = 0 or else (B'Last >= B'First
                                        and then B'Last - B'First >= Rel + 32 * N - 1));

   function Hello_Wire_OK (B : Byte_Array) return Boolean is
     (Hello_Ok_Header (B)
      and then Wire_Ascending (B, Hello_Fixed, Wire_U16 (B, B'First + Hello_O_N))
      and then Wire_Ascending
                 (B, Hello_Fixed + 32 * Wire_U16 (B, B'First + Hello_O_N),
                  Wire_U16 (B, B'First + Hello_O_R)));

   function All_In_W (R : Register_File; W : Writer_List) return Boolean is
     (for all I in W'Range => In_W (R, W (I)));

   function Has_All (R : Register_File; H : Hello) return Boolean is
     (for all I in 1 .. Natural (H.N) => In_W (R, H.W (I)));

   function Fresh_Upto (R : Register_File; H : Hello; I : Natural) return Natural
   with Ghost, Global => null,
        Pre  => I <= Natural (H.N),
        Post => Fresh_Upto'Result <= I,
        Subprogram_Variant => (Decreases => I);

   function Fresh_Upto (R : Register_File; H : Hello; I : Natural) return Natural is
     (if I = 0 then 0
      else Fresh_Upto (R, H, I - 1) + (if In_W (R, H.W (I)) then 0 else 1));

   function Fresh (R : Register_File; H : Hello) return Natural is
     (Fresh_Upto (R, H, Natural (H.N)));

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
