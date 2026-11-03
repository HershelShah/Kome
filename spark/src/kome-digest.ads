--  Kome.Digest: the fingerprint of a set of records, which is also the
--  collection digest (DESIGN.md §8 "Fingerprint = digest (D7)", T6).
--
--  Definitions, exactly as DESIGN.md §8 (decision D7 of §1.2) records them:
--
--    B_i(e)     := BLAKE2b-256 ("kome/acc" ‖ h(e) ‖ u8(i))     i = 0 .. 15
--    acc(e)     := Σ_i LE(B_i(e)) · 2^(256·i)  mod 2^4096,
--                  LE(B) := Σ_j B[j] · 256^j
--    ACC(R)     := Σ_{e ∈ R} acc(e)  mod 2^4096
--    fp(R)      := BLAKE2b-256 ("kome/fp" ‖ u64(|R|) ‖ ACC_le(R))
--    digest(ns) := fp(F|ns)                  (Frontier_Digest below)
--
--  Bytes (§8, D7): "kome/acc" is 6B 6F 6D 65 2F 61 63 63 and "kome/fp" is
--  6B 6F 6D 65 2F 66 70 (Acc_Tag, Fp_Tag); h(e) is the record's content
--  hash (Kome.Headers.Header.V.H) as its 32 bytes in the order BLAKE2b
--  produced them (Kome.Keys.To_Bytes); u8(i) is one byte; u64(|R|) is
--  big-endian. acc(e) is the 512-byte string B_0 ‖ … ‖ B_15 read as a
--  LITTLE-ENDIAN integer (byte 0 least significant, chunk i at bytes
--  32·i .. 32·i + 31), and ACC_le(R) is the 512-byte little-endian form
--  (Kome.Accumulator.To_Bytes); the accumulator is the only little-endian
--  quantity in Kome. vectors/digest.txt holds the normative known-answer
--  vectors (computed with Python's hashlib).
--
--  The arithmetic (the integer mod 2^4096 and its "+" and "-") is
--  Kome.Accumulator; this package hashes an element to its acc(e), keeps
--  the running (|R|, ACC(R)) of a set of records, and hashes that pair to
--  fp(R). The hashing is opaque (Kome.Crypto binds monocypher; A2): its
--  contracts give the exact bytes that are hashed, and the known-answer
--  vectors check the digests themselves. Everything about the arithmetic
--  is proved.
--
--  Equality and the prover (CONVENTIONS.md, rule 1). An Acc is an array,
--  so Ada "=" on two of them is element-wise and not logical equality:
--  the prover cannot conclude Fp (N, A1) = Fp (N, A2) from A1 = A2 by
--  congruence. Lemma_Fp_Congruent and Lemma_Fingerprint_Congruent prove
--  it (the body hashes a record-of-words image of the accumulator, whose
--  equality is logical). The congruences of Add and Sub are
--  Kome.Accumulator's Lemma_Add_Congruent and Lemma_Sub_Congruent.
--
--  Order independence. The state is a commutative-monoid fold: adding
--  records in any order gives the same state (Lemma_Add_Commute for two,
--  Lemma_Sum_Perm for any permutation of a list, given as an injective
--  index map), removing what was added restores it (Lemma_Remove_Add),
--  and the sum over a list splits over any partition into two consecutive
--  ranges (Lemma_Sum_Split, the T6 homomorphism ACC(R₁ ⊎ R₂) = ACC(R₁) +
--  ACC(R₂)). Equal states have equal fingerprints
--  (Lemma_Fingerprint_Congruent). Two frontiers that hold the same
--  records in different array orders have the same digest
--  (Lemma_Frontier_Digest_Perm). The converse (fp(R₁) = fp(R₂) ⇒ R₁ = R₂)
--  is the k-sum hardness assumption A2, not a proof obligation.
--
--  The documented contract of the incremental state. Digest_State is only
--  (|R|, ACC(R)); it does not store R, so it cannot know what R holds.
--  Remove_Record of a record that is not in R, and Add_Record of a record
--  that already is, both return D_OK and apply the arithmetic: the result
--  is the state of no SET (barring a k-sum collision, A2), and nothing in
--  this package detects it. This is inherent in keeping just (|R|, ACC)
--  and is the intended contract, not a defect: T6 is a statement about
--  sets, and the guard is the caller's Models discipline. Models (S, L, N)
--  is the ghost relation "S is the state of the multiset L (1 .. N)", and
--  Lemma_Models_Empty / _Add / _Remove / _Perm carry it across every
--  update; Lemma_Models_Remove asks for the index J at which L holds the
--  removed record, so a client that proves Models proves every removal is
--  of a member. Kome.Frontier holds no record twice (Is_Frontier), and a
--  client that adds exactly what the frontier admits and removes exactly
--  what it drops keeps a state that is the digest recomputed from scratch
--  (Digest_Of, State_Of, Lemma_Digest_Of_Models, Lemma_State_Of_Models).
--  The refusals Add_Record and Remove_Record do report (D_No_Space at
--  |R| = Elem_Max, D_Empty at |R| = 0) are the ones the state can see.
--
--  Prefix sums (§8, D15). Build_Prefix stores P (K) = ACC (L (1 .. 64·K))
--  for every full block K = 1 .. ⌊n/64⌋ and one more entry, the total
--  P_end = ACC (L (1 .. n)), as P (⌊n/64⌋ + 1). Range_Sum answers ACC of
--  any sub-range L (a + 1 .. b), proved equal to the sum over the range.
--  Each end x starts from its nearest stored point Start_Pos (x) (the
--  block boundary below or above, or n for an end in the tail after the
--  last full block, whose stored value is P_end), at most 32 element
--  terms away, and the two-accumulator scheme of §8 adds the terms:
--    Plus  = P(A(b)) + fwd(b) + bwd(a)
--    Minus = P(A(a)) + bwd(b) + fwd(a)
--    ACC (L (a + 1 .. b)) = Plus - Minus
--  so every range, including one that ends in the tail, costs at most 64
--  Add calls and exactly one Sub.
--
--  What the proof gives about that cost, and what it does not. The Post
--  of Range_Sum proves the formula: Range_Cost (a, b, n) <= 64, each end
--  walking at most 32 terms, Adds = Range_Cost and Subs = 1. Adds and
--  Subs are out values; they equal the Add and Sub calls actually made
--  only because the body routes every Add through one local procedure
--  (Add_Term, Pre C < 64, Post C = C'Old + 1) and the Sub through
--  another (Sub_Term). That routing is checked by review of the body, not
--  by the proof: no contract over out values can count calls, so a body
--  that ignored P, added every element of the range and then set Adds :=
--  Range_Cost (...) and Subs := 1 would still prove, and would pass the
--  tests (Prefix_Valid in the Pre forces P to be right, so the Result is
--  the same either way). The proved part is that the RESULT is right for
--  every range and that the bound is a theorem about the scheme; the
--  bound on the calls this body makes rests on the body's discipline.
--
--  Run-time cost under -gnata: every Post that mentions Sum_Of or
--  Frontier_Sum recomputes the sum from scratch (one Add, about 1.5 ms with
--  Kome.Accumulator's checks on, plus 16 hashes per element). The loop
--  invariants and per-step ghost lemmas of Build_Prefix, Range_Sum,
--  Digest_Of and State_Of would make that quadratic, so those bodies set
--  Loop_Invariant, Assert and Ghost to Ignore at run time and call their
--  per-step lemma through a local ghost procedure declared under that
--  policy (a ghost call follows the policy at the called subprogram's
--  declaration). They are proved; their own Pre and Post still run. The
--  ghost lemmas themselves run in full when the test main calls them.
pragma Ada_2022;
with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;
with Kome.Accumulator; use Kome.Accumulator;
with Kome.Byteorder;   use Kome.Byteorder;
with Kome.Keys;
with Kome.Crypto;
with Kome.Frontier;
package Kome.Digest with SPARK_Mode is

   ----------------------------------------------------------------------
   --  Constants (DESIGN.md §8)
   ----------------------------------------------------------------------

   --  "kome/acc" and "kome/fp", ASCII.
   Acc_Tag_Len : constant := 8;
   Fp_Tag_Len  : constant := 7;
   Acc_Tag : constant Byte_Array (0 .. Acc_Tag_Len - 1) :=
     [16#6B#, 16#6F#, 16#6D#, 16#65#, 16#2F#, 16#61#, 16#63#, 16#63#];
   Fp_Tag  : constant Byte_Array (0 .. Fp_Tag_Len - 1) :=
     [16#6B#, 16#6F#, 16#6D#, 16#65#, 16#2F#, 16#66#, 16#70#];

   --  acc(e) is sixteen BLAKE2b-256 outputs: 16 · 32 = 512 bytes = 4096 bits.
   Chunks : constant := Acc_Bytes / Hash_Len;
   subtype Chunk_Index is Natural range 0 .. Chunks - 1;

   --  "kome/acc" ‖ h(e) ‖ i
   Acc_Input_Len : constant := Acc_Tag_Len + Hash_Len + 1;
   subtype Acc_Input_Bytes is Byte_Array (0 .. Acc_Input_Len - 1);

   --  "kome/fp" ‖ |R| (u64 big-endian) ‖ ACC(R) (512 bytes little-endian)
   Count_Pos    : constant := Fp_Tag_Len;
   Acc_Pos      : constant := Fp_Tag_Len + 8;
   Fp_Input_Len : constant := Acc_Pos + Acc_Bytes;
   subtype Fp_Input_Bytes is Byte_Array (0 .. Fp_Input_Len - 1);

   --  |R| is at most the records one replica holds for one collection
   --  (DESIGN.md §7; Kome.Frontier.Held_Max).
   Elem_Max : constant := Kome.Frontier.Held_Max;
   subtype Elem_Count is Natural range 0 .. Elem_Max;
   subtype Elem_Index is Positive range 1 .. Elem_Max;
   --  The low end of a possibly empty range Lo .. Hi (Hi = Lo - 1).
   subtype Lo_Bound is Positive range 1 .. Elem_Max + 1;

   --  §8: one 512-byte prefix sum per 64 elements.
   Block_Elems : constant := 64;

   ----------------------------------------------------------------------
   --  acc(e) (T6). h(e) is a Key256 (the lattice form of the content
   --  hash); it becomes bytes only here, at the hash boundary.
   ----------------------------------------------------------------------

   function Acc_Input (H : Key256; I : Chunk_Index) return Acc_Input_Bytes
     with Global => null,
          Post => Acc_Input'Result (0 .. Acc_Tag_Len - 1) = Acc_Tag
            and then (for all J in Kome.Keys.Key_Index =>
                        Acc_Input'Result (Acc_Tag_Len + J)
                          = Kome.Keys.Byte_At (H, J))
            and then Acc_Input'Result (Acc_Input_Len - 1) = Byte (I);

   --  The 512 bytes of acc(e): chunk I is BLAKE2b-256 of Acc_Input (H, I).
   function Acc_Bytes_Of (H : Key256) return Acc_Byte_Array
     with Global => null,
          Post => (for all I in Chunk_Index =>
                     Acc_Bytes_Of'Result (Hash_Len * I .. Hash_Len * I + Hash_Len - 1)
                       = Kome.Crypto.Blake2b_256 (Acc_Input (H, I)));

   --  acc(e) as an accumulator. An expression function, so that the
   --  element term is logical in H (a record of words).
   function Elem_Acc (H : Key256) return Acc is
     (From_Bytes (Acc_Bytes_Of (H)))
     with Global => null;

   --  "as an integer": acc(e) is the 512 bytes read little-endian.
   procedure Lemma_Elem_Acc_Value (H : Key256)
     with Ghost, Global => null,
          Post => Value (Elem_Acc (H)) = Bytes_Value (Acc_Bytes_Of (H));

   ----------------------------------------------------------------------
   --  fp (T6).
   ----------------------------------------------------------------------

   --  The bytes fp hashes: tag, |R| big-endian, ACC(R) in wire order (the
   --  third conjunct is exactly Kome.Accumulator.To_Bytes (A)).
   function Fp_Input (N : Elem_Count; A : Acc) return Fp_Input_Bytes
     with Global => null,
          Post => Fp_Input'Result (0 .. Fp_Tag_Len - 1) = Fp_Tag
            and then (for all K in U64_Index =>
                        Fp_Input'Result (Count_Pos + K)
                          = Byte_Of_U64 (U64 (N), U64_Len - 1 - K))
            and then (for all I in Acc_Byte_Array'Range =>
                        Fp_Input'Result (Acc_Pos + I)
                          = Byte_Of_U64 (A (I / 8), I mod 8));

   --  fp(R) for |R| = N and ACC(R) = A.
   function Fp (N : Elem_Count; A : Acc) return Hash256 is
     (Kome.Crypto.Blake2b_256 (Fp_Input (N, A)))
     with Global => null;

   --  fp depends on ACC(R) only through its value: element-wise equal
   --  accumulators give the same fingerprint.
   procedure Lemma_Fp_Congruent (N : Elem_Count; A1, A2 : Acc)
     with Ghost, Global => null,
          Pre  => A1 = A2,
          Post => Fp (N, A1) = Fp (N, A2);

   --  The ACC part of the fp input is exactly ACC(R)'s wire form.
   procedure Lemma_Fp_Input_Acc (N : Elem_Count; A : Acc)
     with Ghost, Global => null,
          Post => Fp_Input (N, A) (Acc_Pos .. Fp_Input_Len - 1) = To_Bytes (A);

   ----------------------------------------------------------------------
   --  Incremental state: (|R|, ACC(R)) of a multiset R of records. A
   --  record is added when it is held and removed when it is dropped
   --  (dominated, expired), so the state follows the frontier.
   ----------------------------------------------------------------------

   type Digest_State is private;

   function Count (S : Digest_State) return Elem_Count with Global => null;
   function Sum (S : Digest_State) return Acc with Global => null;

   --  The state of ∅.
   function Empty return Digest_State
     with Global => null,
          Post => Count (Empty'Result) = 0 and then Sum (Empty'Result) = Zero;

   --  The state whose |R| is N and whose ACC(R) is A: for a client that
   --  stored a state's Count and Sum (a §8 snapshot) and restores it. A
   --  restored state carries no Models fact: nothing ties (N, A) to a
   --  set, and it is the state of one only if the client proves Models
   --  for it again (see the header's documented contract).
   function Restore (N : Elem_Count; A : Acc) return Digest_State
     with Global => null,
          Post => Count (Restore'Result) = N and then Sum (Restore'Result) = A;

   --  R ⊎ {e}.
   function With_Record (S : Digest_State; H : Key256) return Digest_State
     with Global => null,
          Pre  => Count (S) < Elem_Max,
          Post => Count (With_Record'Result) = Count (S) + 1
            and then Sum (With_Record'Result) = Add (Sum (S), Elem_Acc (H));

   --  R ∖ {e}, for an e in R. Nothing here can check that e is in R: the
   --  arithmetic is applied regardless (see the header's documented
   --  contract); Lemma_Models_Remove is how a client proves the removal is
   --  of a member.
   function Without_Record (S : Digest_State; H : Key256) return Digest_State
     with Global => null,
          Pre  => Count (S) > 0,
          Post => Count (Without_Record'Result) = Count (S) - 1
            and then Sum (Without_Record'Result) = Sub (Sum (S), Elem_Acc (H));

   --  fp(R).
   function Fingerprint (S : Digest_State) return Hash256 is
     (Fp (Count (S), Sum (S)))
     with Global => null;

   --  Why an update was refused. The state is unchanged on refusal (T13).
   type Digest_Status is
     (D_OK,          --  applied
      D_No_Space,    --  |R| = Elem_Max: no record can be added
      D_Empty);      --  |R| = 0: no record can be removed

   --  Adds H. D_OK whenever |R| < Elem_Max, even if H is already in R (a
   --  multiset add; see the header's documented contract).
   procedure Add_Record
     (S : in out Digest_State; H : Key256; Result : out Digest_Status)
     with Global => null,
          Post => (case Result is
                     when D_OK       =>
                       Count (S'Old) < Elem_Max
                       and then Count (S) = Count (S'Old) + 1
                       and then Sum (S) = Add (Sum (S'Old), Elem_Acc (H)),
                     when D_No_Space =>
                       Count (S'Old) = Elem_Max
                       and then Count (S) = Count (S'Old)
                       and then Sum (S) = Sum (S'Old),
                     when D_Empty    => False);

   --  Removes H, which the caller must hold in R. D_OK whenever |R| > 0,
   --  whether or not H is in R (see the header's documented contract:
   --  T6 is about sets, and the caller's Models discipline is the guard).
   procedure Remove_Record
     (S : in out Digest_State; H : Key256; Result : out Digest_Status)
     with Global => null,
          Post => (case Result is
                     when D_OK       =>
                       Count (S'Old) > 0
                       and then Count (S) = Count (S'Old) - 1
                       and then Sum (S) = Sub (Sum (S'Old), Elem_Acc (H)),
                     when D_Empty    =>
                       Count (S'Old) = 0
                       and then Count (S) = Count (S'Old)
                       and then Sum (S) = Sum (S'Old),
                     when D_No_Space => False);

   ----------------------------------------------------------------------
   --  Laws of the state (T6).
   ----------------------------------------------------------------------

   --  Removing a record that was just added restores the state
   --  (Kome.Accumulator.Lemma_Sub_Add).
   procedure Lemma_Remove_Add (S : Digest_State; H : Key256)
     with Ghost, Global => null,
          Pre  => Count (S) < Elem_Max,
          Post => Count (Without_Record (With_Record (S, H), H)) = Count (S)
            and then Sum (Without_Record (With_Record (S, H), H)) = Sum (S);

   --  Adding back a removed record restores the state (Lemma_Add_Sub).
   procedure Lemma_Add_Remove (S : Digest_State; H : Key256)
     with Ghost, Global => null,
          Pre  => Count (S) > 0,
          Post => Count (With_Record (Without_Record (S, H), H)) = Count (S)
            and then Sum (With_Record (Without_Record (S, H), H)) = Sum (S);

   --  The order of two adds does not matter.
   procedure Lemma_Add_Commute (S : Digest_State; H1, H2 : Key256)
     with Ghost, Global => null,
          Pre  => Count (S) <= Elem_Max - 2,
          Post => Count (With_Record (With_Record (S, H1), H2))
                    = Count (With_Record (With_Record (S, H2), H1))
            and then Sum (With_Record (With_Record (S, H1), H2))
                    = Sum (With_Record (With_Record (S, H2), H1));

   --  Two states with the same count and sum (e.g. the same records, added
   --  in different orders) have the same fingerprint.
   procedure Lemma_Fingerprint_Congruent (S1, S2 : Digest_State)
     with Ghost, Global => null,
          Pre  => Count (S1) = Count (S2) and then Sum (S1) = Sum (S2),
          Post => Fingerprint (S1) = Fingerprint (S2);

   ----------------------------------------------------------------------
   --  Lists of element hashes and their sums (T6 over a multiset).
   ----------------------------------------------------------------------

   type Hash_Array is array (Elem_Index range <>) of Key256;

   --  Σ acc (L (I)) for I in Lo .. Hi, added left to right; Zero when the
   --  range is empty. Ghost model, opaque to clients (completed in the
   --  body); use Lemma_Sum_Of_Empty / Lemma_Sum_Of_Step to unfold it.
   function Sum_Of (L : Hash_Array; Lo : Lo_Bound; Hi : Elem_Count) return Acc
     with Ghost, Global => null,
          Pre => (if Lo <= Hi then Lo >= L'First and then Hi <= L'Last),
          Subprogram_Variant => (Decreases => Hi);

   procedure Lemma_Sum_Of_Empty (L : Hash_Array; Lo : Lo_Bound; Hi : Elem_Count)
     with Ghost, Global => null,
          Pre  => Hi < Lo,
          Post => Sum_Of (L, Lo, Hi) = Zero;

   procedure Lemma_Sum_Of_Step (L : Hash_Array; Lo : Lo_Bound; Hi : Elem_Count)
     with Ghost, Global => null,
          Pre  => Lo <= Hi and then Lo >= L'First and then Hi <= L'Last,
          Post => Sum_Of (L, Lo, Hi) = Add (Sum_Of (L, Lo, Hi - 1), Elem_Acc (L (Hi)));

   --  T6: ACC(R₁ ⊎ R₂) = ACC(R₁) + ACC(R₂), for R₁ = L (Lo .. Mid) and
   --  R₂ = L (Mid + 1 .. Hi), either possibly empty.
   procedure Lemma_Sum_Split
     (L : Hash_Array; Lo : Lo_Bound; Mid : Elem_Count; Hi : Elem_Count)
     with Ghost, Global => null,
          Pre  => Lo - 1 <= Mid and then Mid <= Hi
                  and then (if Lo <= Hi then Lo >= L'First and then Hi <= L'Last),
          Post => Sum_Of (L, Lo, Hi)
                    = Add (Sum_Of (L, Lo, Mid), Sum_Of (L, Mid + 1, Hi));

   --  Two lists that agree on Lo .. Hi have the same sum there.
   procedure Lemma_Sum_Ext
     (L1, L2 : Hash_Array; Lo : Lo_Bound; Hi : Elem_Count)
     with Ghost, Global => null,
          Pre  => (if Lo <= Hi then
                     Lo >= L1'First and then Hi <= L1'Last
                     and then Lo >= L2'First and then Hi <= L2'Last
                     and then (for all I in Lo .. Hi => L1 (I) = L2 (I))),
          Post => Sum_Of (L1, Lo, Hi) = Sum_Of (L2, Lo, Hi);

   --  Order independence: swapping two adjacent elements does not change
   --  the sum (a special case of Lemma_Sum_Perm, kept for its simplicity).
   procedure Lemma_Sum_Swap (L1, L2 : Hash_Array; I : Elem_Index)
     with Ghost, Global => null,
          Pre  => L1'First = L2'First and then L1'Last = L2'Last
                  and then I >= L1'First and then I < L1'Last
                  and then L2 (I) = L1 (I + 1) and then L2 (I + 1) = L1 (I)
                  and then (for all J in L1'Range =>
                              (if J /= I and then J /= I + 1
                               then L2 (J) = L1 (J))),
          Post => Sum_Of (L1, L1'First, L1'Last)
                    = Sum_Of (L2, L2'First, L2'Last);

   --  Deleting the element at J (and shifting the rest down) removes its
   --  acc from the sum: Σ L1 (1 .. N) = Σ L2 (1 .. N - 1) + acc (L1 (J)).
   procedure Lemma_Sum_Delete
     (L1, L2 : Hash_Array; N : Elem_Count; J : Elem_Index)
     with Ghost, Global => null,
          Pre  => L1'First = 1 and then L2'First = 1
                  and then J <= N and then N <= L1'Last
                  and then N - 1 <= L2'Last
                  and then (for all I in 1 .. J - 1 => L2 (I) = L1 (I))
                  and then (for all I in J .. N - 1 => L2 (I) = L1 (I + 1)),
          Post => Sum_Of (L1, 1, N)
                    = Add (Sum_Of (L2, 1, N - 1), Elem_Acc (L1 (J)));

   --  A permutation witness: M (I) is where L2 holds L1 (I). An injective
   --  map of 1 .. N into 1 .. N is a bijection, so it is all a caller
   --  supplies (CONVENTIONS.md: explicit witnesses, not existentials).
   type Index_Map is array (Elem_Index range <>) of Elem_Index;

   --  Is_Perm (L1, L2, M, N): M is such a witness for L1 (1 .. N) and
   --  L2 (1 .. N). Quantified, so opaque (CONVENTIONS.md, rule 2; completed
   --  in the body, which Kome.Accumulator's probe found is what hides a
   --  definition from clients). Lemma_Is_Perm_Intro establishes it and
   --  Lemma_Is_Perm_Elim takes it apart; its Pre and Post are its
   --  definition.
   function Is_Perm
     (L1, L2 : Hash_Array; M : Index_Map; N : Elem_Count) return Boolean
     with Ghost, Global => null;

   procedure Lemma_Is_Perm_Intro
     (L1, L2 : Hash_Array; M : Index_Map; N : Elem_Count)
     with Ghost, Global => null,
          Pre  => L1'First = 1 and then L2'First = 1 and then M'First = 1
                  and then N <= L1'Last and then N <= L2'Last
                  and then N <= M'Last
                  and then (for all I in 1 .. N =>
                              M (I) <= N and then L2 (M (I)) = L1 (I))
                  and then (for all I in 1 .. N =>
                              (for all K in 1 .. N =>
                                 (if I /= K then M (I) /= M (K)))),
          Post => Is_Perm (L1, L2, M, N);

   procedure Lemma_Is_Perm_Elim
     (L1, L2 : Hash_Array; M : Index_Map; N : Elem_Count)
     with Ghost, Global => null,
          Pre  => Is_Perm (L1, L2, M, N),
          Post => L1'First = 1 and then L2'First = 1 and then M'First = 1
                  and then N <= L1'Last and then N <= L2'Last
                  and then N <= M'Last
                  and then (for all I in 1 .. N =>
                              M (I) <= N and then L2 (M (I)) = L1 (I))
                  and then (for all I in 1 .. N =>
                              (for all K in 1 .. N =>
                                 (if I /= K then M (I) /= M (K))));

   --  T6 over a multiset: the sum of a list depends only on the multiset
   --  of its elements, not on their order.
   procedure Lemma_Sum_Perm
     (L1, L2 : Hash_Array; M : Index_Map; N : Elem_Count)
     with Ghost, Global => null,
          Pre  => Is_Perm (L1, L2, M, N),
          Post => Sum_Of (L1, 1, N) = Sum_Of (L2, 1, N),
          Subprogram_Variant => (Decreases => N);

   --  The state of the records whose hashes L lists. (A null array's
   --  bounds need not lie in Elem_Index, hence the case split.)
   function Digest_Of (L : Hash_Array) return Digest_State
     with Global => null,
          Pre  => L'Length <= Elem_Max,
          Post => Count (Digest_Of'Result) = L'Length
            and then (if L'Length = 0 then Sum (Digest_Of'Result) = Zero
                      else Sum (Digest_Of'Result) = Sum_Of (L, L'First, L'Last));

   ----------------------------------------------------------------------
   --  The meaning of an incremental state: S is the state of the multiset
   --  L (1 .. N). A client keeps L as a ghost list beside S and carries
   --  Models across each update with the lemmas below; its running state
   --  is then the digest recomputed from scratch (Lemma_Digest_Of_Models,
   --  Lemma_State_Of_Models), and two running states that model
   --  permutations of one multiset have the same fingerprint.
   ----------------------------------------------------------------------

   function Models
     (S : Digest_State; L : Hash_Array; N : Elem_Count) return Boolean
   is (L'First = 1 and then N <= L'Last
       and then Count (S) = N and then Sum (S) = Sum_Of (L, 1, N))
     with Ghost, Global => null;

   procedure Lemma_Models_Empty (L : Hash_Array)
     with Ghost, Global => null,
          Pre  => L'First = 1 and then L'Last >= 0,
          Post => Models (Empty, L, 0);

   --  Adding H appends it: L2 (1 .. N + 1) = L1 (1 .. N) ‖ H. (L2 may be
   --  L1 updated in place.)
   procedure Lemma_Models_Add
     (S : Digest_State; L1, L2 : Hash_Array; N : Elem_Count; H : Key256)
     with Ghost, Global => null,
          Pre  => Models (S, L1, N) and then N < Elem_Max
                  and then L2'First = 1 and then N + 1 <= L2'Last
                  and then (for all I in 1 .. N => L2 (I) = L1 (I))
                  and then L2 (N + 1) = H,
          Post => Models (With_Record (S, H), L2, N + 1);

   --  Removing the member at index J deletes it: L2 (1 .. N - 1) is
   --  L1 (1 .. N) without L1 (J). J is the membership witness.
   procedure Lemma_Models_Remove
     (S : Digest_State; L1, L2 : Hash_Array; N : Elem_Count; J : Elem_Index)
     with Ghost, Global => null,
          Pre  => Models (S, L1, N) and then J <= N
                  and then L2'First = 1 and then N - 1 <= L2'Last
                  and then (for all I in 1 .. J - 1 => L2 (I) = L1 (I))
                  and then (for all I in J .. N - 1 => L2 (I) = L1 (I + 1)),
          Post => Models (Without_Record (S, L1 (J)), L2, N - 1);

   --  A state models every permutation of its multiset.
   procedure Lemma_Models_Perm
     (S : Digest_State; L1, L2 : Hash_Array; M : Index_Map; N : Elem_Count)
     with Ghost, Global => null,
          Pre  => Models (S, L1, N) and then Is_Perm (L1, L2, M, N),
          Post => Models (S, L2, N);

   --  Two states of the same multiset, in any order, give the same
   --  fingerprint (T6: fp is a function of R).
   procedure Lemma_Models_Fingerprint
     (S1, S2 : Digest_State; L1, L2 : Hash_Array; M : Index_Map;
      N : Elem_Count)
     with Ghost, Global => null,
          Pre  => Models (S1, L1, N) and then Models (S2, L2, N)
                  and then Is_Perm (L1, L2, M, N),
          Post => Fingerprint (S1) = Fingerprint (S2);

   procedure Lemma_Digest_Of_Models (L : Hash_Array)
     with Ghost, Global => null,
          Pre  => L'First = 1 and then L'Last >= 0,
          Post => Models (Digest_Of (L), L, L'Length);

   ----------------------------------------------------------------------
   --  digest(ns) = fp(F|ns) (T6): the fingerprint of one collection's
   --  frontier (Kome.Frontier.State holds one collection).
   ----------------------------------------------------------------------

   --  Σ acc (Held (F, I).V.H) for I in 1 .. K. Ghost model, opaque.
   function Frontier_Sum (F : Kome.Frontier.State; K : Elem_Count) return Acc
     with Ghost, Global => null,
          Pre => K <= Kome.Frontier.Count (F),
          Subprogram_Variant => (Decreases => K);

   procedure Lemma_Frontier_Sum_Step (F : Kome.Frontier.State; K : Elem_Count)
     with Ghost, Global => null,
          Pre  => K <= Kome.Frontier.Count (F),
          Post => (if K = 0 then Frontier_Sum (F, K) = Zero
                   else Frontier_Sum (F, K)
                          = Add (Frontier_Sum (F, K - 1),
                                 Elem_Acc (Kome.Frontier.Held (F, K).V.H)));

   function State_Of (F : Kome.Frontier.State) return Digest_State
     with Global => null,
          Post => Count (State_Of'Result) = Kome.Frontier.Count (F)
            and then Sum (State_Of'Result)
                       = Frontier_Sum (F, Kome.Frontier.Count (F));

   function Frontier_Digest (F : Kome.Frontier.State) return Hash256
     with Global => null,
          Post => Frontier_Digest'Result
                    = Fp (Kome.Frontier.Count (F),
                          Frontier_Sum (F, Kome.Frontier.Count (F)));

   --  The frontier sum is the list sum of the held hashes.
   procedure Lemma_Frontier_Sum_List
     (F : Kome.Frontier.State; L : Hash_Array; K : Elem_Count)
     with Ghost, Global => null,
          Pre  => L'First = 1 and then K <= Kome.Frontier.Count (F)
                  and then K <= L'Last
                  and then (for all I in 1 .. K =>
                              L (I) = Kome.Frontier.Held (F, I).V.H),
          Post => Frontier_Sum (F, K) = Sum_Of (L, 1, K);

   --  State_Of (F) is the state of the list of F's held hashes.
   procedure Lemma_State_Of_Models (F : Kome.Frontier.State; L : Hash_Array)
     with Ghost, Global => null,
          Pre  => L'First = 1 and then Kome.Frontier.Count (F) <= L'Last
                  and then (for all I in 1 .. Kome.Frontier.Count (F) =>
                              L (I) = Kome.Frontier.Held (F, I).V.H),
          Post => Models (State_Of (F), L, Kome.Frontier.Count (F));

   --  T6, digest(ns) = fp(F|ns) is a function of the SET F: two replicas
   --  that hold the same records (T4) in different array orders have the
   --  same digest. M (I) is where F2 holds F1's I-th record's hash.
   procedure Lemma_Frontier_Digest_Perm
     (F1, F2 : Kome.Frontier.State; M : Index_Map)
     with Ghost, Global => null,
          Pre  => Kome.Frontier.Count (F1) = Kome.Frontier.Count (F2)
                  and then M'First = 1
                  and then Kome.Frontier.Count (F1) <= M'Last
                  and then (for all I in 1 .. Kome.Frontier.Count (F1) =>
                              M (I) <= Kome.Frontier.Count (F2)
                              and then Kome.Frontier.Held (F2, M (I)).V.H
                                         = Kome.Frontier.Held (F1, I).V.H)
                  and then (for all I in 1 .. Kome.Frontier.Count (F1) =>
                              (for all K in 1 .. Kome.Frontier.Count (F1) =>
                                 (if I /= K then M (I) /= M (K)))),
          Post => Frontier_Digest (F1) = Frontier_Digest (F2);

   ----------------------------------------------------------------------
   --  Prefix sums for ranges (§8, D15): P (K) = ACC of L (1 .. 64·K) for
   --  K = 1 .. ⌊n/64⌋, and P (⌊n/64⌋ + 1) = P_end = ACC of L (1 .. n).
   ----------------------------------------------------------------------

   --  One stored prefix per full block of Elem_Max elements, plus the
   --  total.
   subtype Block_Index is Positive range 1 .. Elem_Max / Block_Elems + 1;
   type Acc_Array is array (Block_Index range <>) of Acc;

   --  The stored points around a prefix end X of an N-element list (Pre
   --  (X) = ACC (L (1 .. X))): the block boundary at or below X, and the
   --  next one above it, or N (where P_end is stored) when X is in the
   --  tail after the last full block. Quantifier-free, so public.
   function Below (X : Elem_Count) return Elem_Count is
     (Block_Elems * (X / Block_Elems))
     with Global => null;

   function Above (X, N : Elem_Count) return Elem_Count is
     (if Block_Elems * (X / Block_Elems + 1) <= N
      then Block_Elems * (X / Block_Elems + 1) else N)
     with Global => null, Pre => X <= N;

   --  X starts from the nearer one (below on a tie).
   function Walks_Back (X, N : Elem_Count) return Boolean is
     (Above (X, N) - X < X - Below (X))
     with Global => null, Pre => X <= N;

   function Start_Pos (X, N : Elem_Count) return Elem_Count is
     (if Walks_Back (X, N) then Above (X, N) else Below (X))
     with Global => null, Pre => X <= N;

   --  The element terms end X walks: |X - Start_Pos (X, N)|.
   function Walk_Len (X, N : Elem_Count) return Natural is
     (if Walks_Back (X, N) then Above (X, N) - X else X - Below (X))
     with Global => null, Pre => X <= N;

   --  The Add calls of Range_Sum for L (A + 1 .. B) of an N-element list:
   --  one per element term walked, at either end.
   function Range_Cost (A, B, N : Elem_Count) return Natural is
     (Walk_Len (A, N) + Walk_Len (B, N))
     with Global => null, Pre => A <= B and then B <= N;

   --  Ghost, opaque (quantified; CONVENTIONS.md rule 2): P is the prefix
   --  array of L, every full block's prefix then the total.
   function Prefix_Valid (L : Hash_Array; P : Acc_Array) return Boolean
     with Ghost, Global => null;

   procedure Build_Prefix (L : Hash_Array; P : out Acc_Array)
     with Global => null,
          Pre  => L'First = 1 and then P'First = 1
                  and then P'Length = L'Length / Block_Elems + 1,
          Post => Prefix_Valid (L, P);

   --  The last entry is the total (P_end).
   procedure Lemma_Prefix_Total (L : Hash_Array; P : Acc_Array)
     with Ghost, Global => null,
          Pre  => Prefix_Valid (L, P),
          Post => P'First = 1 and then P'Length = L'Length / Block_Elems + 1
                  and then P (P'Last) = Sum_Of (L, 1, L'Length);

   --  The Add calls one Range_Sum makes: at most one block's worth.
   subtype Add_Count is Natural range 0 .. Block_Elems;

   --  Result = ACC of L (Lo .. Hi) (empty when Hi = Lo - 1), by the
   --  two-accumulator scheme of §8 (see the header). The Post proves the
   --  formula Range_Cost (Lo - 1, Hi, n) <= 64 with each end at most 32
   --  terms, and Adds = Range_Cost, Subs = 1. Adds and Subs are the Add
   --  and Sub calls the body counts: it routes every Add through one local
   --  procedure (Add_Term) and the Sub through another (Sub_Term), which
   --  increment the counts. That they are the calls actually made is a
   --  property of this body, checked by review and not by the proof: a
   --  body that set Adds and Subs without counting (and, say, ignored P
   --  and summed the range directly) would also prove this Post and pass
   --  the tests (see the header).
   procedure Range_Sum
     (L      : Hash_Array;
      P      : Acc_Array;
      Lo     : Lo_Bound;
      Hi     : Elem_Count;
      Result : out Acc;
      Adds   : out Add_Count;
      Subs   : out Natural)
     with Global => null,
          Pre  => L'First = 1 and then P'First = 1
                  and then P'Length = L'Length / Block_Elems + 1
                  and then Prefix_Valid (L, P)
                  and then Lo <= Hi + 1 and then Hi <= L'Last,
          Post => Result = Sum_Of (L, Lo, Hi)
                  and then Adds = Range_Cost (Lo - 1, Hi, L'Length)
                  and then Subs = 1
                  and then Walk_Len (Lo - 1, L'Length) <= Block_Elems / 2
                  and then Walk_Len (Hi, L'Length) <= Block_Elems / 2
                  and then Range_Cost (Lo - 1, Hi, L'Length) <= Block_Elems;

private

   type Digest_State is record
      N : Elem_Count := 0;
      A : Acc        := Zero;
   end record;

   function Count (S : Digest_State) return Elem_Count is (S.N);
   function Sum (S : Digest_State) return Acc is (S.A);

   function Empty return Digest_State is ((N => 0, A => Zero));

   function Restore (N : Elem_Count; A : Acc) return Digest_State is
     ((N => N, A => A));

   function With_Record (S : Digest_State; H : Key256) return Digest_State is
     ((N => S.N + 1, A => Add (S.A, Elem_Acc (H))));

   function Without_Record (S : Digest_State; H : Key256) return Digest_State is
     ((N => S.N - 1, A => Sub (S.A, Elem_Acc (H))));

end Kome.Digest;
