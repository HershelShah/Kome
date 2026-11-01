pragma Ada_2022;
package body Kome.Digest with SPARK_Mode is

   ----------------------------------------------------------------------
   --  Congruence of Add and Sub, and transitivity of "=" on Acc. Ada "="
   --  on Acc is element-wise, so the prover neither substitutes equal
   --  accumulators inside Add or Sub nor chains two equalities by itself;
   --  these go through the integer model (Value is a function of the
   --  limbs, and equal Values mean equal accumulators).
   ----------------------------------------------------------------------

   procedure Lemma_Add_Congruent (X1, X2, Y1, Y2 : Acc) is
   begin
      Lemma_Value_Congruent (X1, X2);
      Lemma_Value_Congruent (Y1, Y2);
      Lemma_Value_Injective (Add (X1, Y1), Add (X2, Y2));
   end Lemma_Add_Congruent;

   procedure Lemma_Sub_Congruent (X1, X2, Y1, Y2 : Acc) is
   begin
      Lemma_Value_Congruent (X1, X2);
      Lemma_Value_Congruent (Y1, Y2);
      Lemma_Value_Injective (Sub (X1, Y1), Sub (X2, Y2));
   end Lemma_Sub_Congruent;

   procedure Lemma_Eq_Trans (A, B, C : Acc)
     with Ghost, Global => null,
          Pre  => A = B and then B = C,
          Post => A = C;

   procedure Lemma_Eq_Trans (A, B, C : Acc) is
   begin
      Lemma_Value_Congruent (A, B);
      Lemma_Value_Congruent (B, C);
      Lemma_Value_Injective (A, C);
   end Lemma_Eq_Trans;

   --  (X + A) + B = (X + B) + A: the two-element exchange every order
   --  independence law reduces to.
   procedure Lemma_Add_Exchange (X, A, B : Acc)
     with Ghost, Global => null,
          Post => Add (Add (X, A), B) = Add (Add (X, B), A);

   procedure Lemma_Add_Exchange (X, A, B : Acc) is
   begin
      Lemma_Add_Assoc (X, A, B);
      Lemma_Add_Comm (A, B);
      Lemma_Add_Congruent (X, X, Add (A, B), Add (B, A));
      Lemma_Add_Assoc (X, B, A);
   end Lemma_Add_Exchange;

   ----------------------------------------------------------------------
   --  The accumulator as a record of 64 words. Its equality is logical
   --  (CONVENTIONS.md, rule 1), so a hash of a function of the image is
   --  the same term for element-wise equal accumulators.
   ----------------------------------------------------------------------

   type Acc_Image is record
      L00, L01, L02, L03, L04, L05, L06, L07 : U64;
      L08, L09, L10, L11, L12, L13, L14, L15 : U64;
      L16, L17, L18, L19, L20, L21, L22, L23 : U64;
      L24, L25, L26, L27, L28, L29, L30, L31 : U64;
      L32, L33, L34, L35, L36, L37, L38, L39 : U64;
      L40, L41, L42, L43, L44, L45, L46, L47 : U64;
      L48, L49, L50, L51, L52, L53, L54, L55 : U64;
      L56, L57, L58, L59, L60, L61, L62, L63 : U64;
   end record;

   function Limb (W : Acc_Image; L : Limb_Index) return U64 is
     (case L is
         when  0 => W.L00,
         when  1 => W.L01,
         when  2 => W.L02,
         when  3 => W.L03,
         when  4 => W.L04,
         when  5 => W.L05,
         when  6 => W.L06,
         when  7 => W.L07,
         when  8 => W.L08,
         when  9 => W.L09,
         when 10 => W.L10,
         when 11 => W.L11,
         when 12 => W.L12,
         when 13 => W.L13,
         when 14 => W.L14,
         when 15 => W.L15,
         when 16 => W.L16,
         when 17 => W.L17,
         when 18 => W.L18,
         when 19 => W.L19,
         when 20 => W.L20,
         when 21 => W.L21,
         when 22 => W.L22,
         when 23 => W.L23,
         when 24 => W.L24,
         when 25 => W.L25,
         when 26 => W.L26,
         when 27 => W.L27,
         when 28 => W.L28,
         when 29 => W.L29,
         when 30 => W.L30,
         when 31 => W.L31,
         when 32 => W.L32,
         when 33 => W.L33,
         when 34 => W.L34,
         when 35 => W.L35,
         when 36 => W.L36,
         when 37 => W.L37,
         when 38 => W.L38,
         when 39 => W.L39,
         when 40 => W.L40,
         when 41 => W.L41,
         when 42 => W.L42,
         when 43 => W.L43,
         when 44 => W.L44,
         when 45 => W.L45,
         when 46 => W.L46,
         when 47 => W.L47,
         when 48 => W.L48,
         when 49 => W.L49,
         when 50 => W.L50,
         when 51 => W.L51,
         when 52 => W.L52,
         when 53 => W.L53,
         when 54 => W.L54,
         when 55 => W.L55,
         when 56 => W.L56,
         when 57 => W.L57,
         when 58 => W.L58,
         when 59 => W.L59,
         when 60 => W.L60,
         when 61 => W.L61,
         when 62 => W.L62,
         when 63 => W.L63)
     with Global => null;

   function Image (A : Acc) return Acc_Image is
     ((
       L00 => A (0), L01 => A (1), L02 => A (2), L03 => A (3),
       L04 => A (4), L05 => A (5), L06 => A (6), L07 => A (7),
       L08 => A (8), L09 => A (9), L10 => A (10), L11 => A (11),
       L12 => A (12), L13 => A (13), L14 => A (14), L15 => A (15),
       L16 => A (16), L17 => A (17), L18 => A (18), L19 => A (19),
       L20 => A (20), L21 => A (21), L22 => A (22), L23 => A (23),
       L24 => A (24), L25 => A (25), L26 => A (26), L27 => A (27),
       L28 => A (28), L29 => A (29), L30 => A (30), L31 => A (31),
       L32 => A (32), L33 => A (33), L34 => A (34), L35 => A (35),
       L36 => A (36), L37 => A (37), L38 => A (38), L39 => A (39),
       L40 => A (40), L41 => A (41), L42 => A (42), L43 => A (43),
       L44 => A (44), L45 => A (45), L46 => A (46), L47 => A (47),
       L48 => A (48), L49 => A (49), L50 => A (50), L51 => A (51),
       L52 => A (52), L53 => A (53), L54 => A (54), L55 => A (55),
       L56 => A (56), L57 => A (57), L58 => A (58), L59 => A (59),
       L60 => A (60), L61 => A (61), L62 => A (62), L63 => A (63)))
     with Global => null,
          Post => (for all L in Limb_Index => Limb (Image'Result, L) = A (L));

   --  The fp input built from the image.
   function Fp_Input_W (N : Elem_Count; W : Acc_Image) return Fp_Input_Bytes
     with Global => null,
          Post => Fp_Input_W'Result (0 .. Fp_Tag_Len - 1) = Fp_Tag
            and then (for all K in U64_Index =>
                        Fp_Input_W'Result (Count_Pos + K)
                          = Byte_Of_U64 (U64 (N), U64_Len - 1 - K))
            and then (for all I in Acc_Byte_Array'Range =>
                        Fp_Input_W'Result (Acc_Pos + I)
                          = Byte_Of_U64 (Limb (W, I / 8), I mod 8));

   function Fp_Input_W (N : Elem_Count; W : Acc_Image) return Fp_Input_Bytes is
      R : Fp_Input_Bytes := [others => 0];
   begin
      R (0 .. Fp_Tag_Len - 1) := Fp_Tag;
      for K in U64_Index loop
         R (Count_Pos + K) := Byte_Of_U64 (U64 (N), U64_Len - 1 - K);
         pragma Loop_Invariant (R (0 .. Fp_Tag_Len - 1) = Fp_Tag);
         pragma Loop_Invariant
           (for all J in 0 .. K =>
              R (Count_Pos + J) = Byte_Of_U64 (U64 (N), U64_Len - 1 - J));
      end loop;
      for I in Acc_Byte_Array'Range loop
         R (Acc_Pos + I) := Byte_Of_U64 (Limb (W, I / 8), I mod 8);
         pragma Loop_Invariant (R (0 .. Fp_Tag_Len - 1) = Fp_Tag);
         pragma Loop_Invariant
           (for all J in U64_Index =>
              R (Count_Pos + J) = Byte_Of_U64 (U64 (N), U64_Len - 1 - J));
         pragma Loop_Invariant
           (for all J in 0 .. I =>
              R (Acc_Pos + J) = Byte_Of_U64 (Limb (W, J / 8), J mod 8));
      end loop;
      return R;
   end Fp_Input_W;

   ----------------------------------------------------------------------
   --  acc(e)
   ----------------------------------------------------------------------

   function Acc_Input (H : Key256; I : Chunk_Index) return Acc_Input_Bytes is
      HB : constant Kome.Keys.Key_Bytes := Kome.Keys.To_Bytes (H);
      R  : Acc_Input_Bytes := [others => 0];
   begin
      R (0 .. Acc_Tag_Len - 1) := Acc_Tag;
      R (Acc_Tag_Len .. Acc_Tag_Len + Hash_Len - 1) := HB;
      R (Acc_Input_Len - 1) := Byte (I);
      return R;
   end Acc_Input;

   function Acc_Bytes_Of (H : Key256) return Acc_Byte_Array is
      R : Acc_Byte_Array := [others => 0];
   begin
      for I in Chunk_Index loop
         R (Hash_Len * I .. Hash_Len * I + Hash_Len - 1) :=
           Kome.Crypto.Blake2b_256 (Acc_Input (H, I));
         pragma Loop_Invariant
           (for all J in 0 .. I =>
              R (Hash_Len * J .. Hash_Len * J + Hash_Len - 1)
                = Kome.Crypto.Blake2b_256 (Acc_Input (H, J)));
      end loop;
      return R;
   end Acc_Bytes_Of;

   procedure Lemma_Elem_Acc_Value (H : Key256) is
   begin
      Lemma_Value_From_Bytes (Acc_Bytes_Of (H));
   end Lemma_Elem_Acc_Value;

   ----------------------------------------------------------------------
   --  fp
   ----------------------------------------------------------------------

   function Fp_Input (N : Elem_Count; A : Acc) return Fp_Input_Bytes is
     (Fp_Input_W (N, Image (A)));

   procedure Lemma_Fp_Input_Acc (N : Elem_Count; A : Acc) is
      B : constant Fp_Input_Bytes := Fp_Input (N, A);
      T : constant Acc_Byte_Array := To_Bytes (A);
   begin
      pragma Assert
        (for all I in Acc_Byte_Array'Range => B (Acc_Pos + I) = T (I));
   end Lemma_Fp_Input_Acc;

   procedure Lemma_Fp_Congruent (N : Elem_Count; A1, A2 : Acc) is
   begin
      pragma Assert (Image (A1) = Image (A2));
   end Lemma_Fp_Congruent;

   ----------------------------------------------------------------------
   --  Incremental state
   ----------------------------------------------------------------------

   procedure Add_Record
     (S : in out Digest_State; H : Key256; Result : out Digest_Status) is
   begin
      if Count (S) = Elem_Max then
         Result := D_No_Space;
      else
         S := With_Record (S, H);
         Result := D_OK;
      end if;
   end Add_Record;

   procedure Remove_Record
     (S : in out Digest_State; H : Key256; Result : out Digest_Status) is
   begin
      if Count (S) = 0 then
         Result := D_Empty;
      else
         S := Without_Record (S, H);
         Result := D_OK;
      end if;
   end Remove_Record;

   procedure Lemma_Remove_Add (S : Digest_State; H : Key256) is
   begin
      Lemma_Sub_Add (Sum (S), Elem_Acc (H));
   end Lemma_Remove_Add;

   procedure Lemma_Add_Remove (S : Digest_State; H : Key256) is
   begin
      Lemma_Add_Sub (Sum (S), Elem_Acc (H));
   end Lemma_Add_Remove;

   procedure Lemma_Add_Commute (S : Digest_State; H1, H2 : Key256) is
   begin
      Lemma_Add_Exchange (Sum (S), Elem_Acc (H1), Elem_Acc (H2));
   end Lemma_Add_Commute;

   procedure Lemma_Fingerprint_Congruent (S1, S2 : Digest_State) is
   begin
      Lemma_Fp_Congruent (Count (S1), Sum (S1), Sum (S2));
   end Lemma_Fingerprint_Congruent;

   ----------------------------------------------------------------------
   --  Lists
   ----------------------------------------------------------------------

   function Sum_Of (L : Hash_Array; Lo : Lo_Bound; Hi : Elem_Count) return Acc is
     (if Hi < Lo then Zero
      else Add (Sum_Of (L, Lo, Hi - 1), Elem_Acc (L (Hi))));

   procedure Lemma_Sum_Of_Empty (L : Hash_Array; Lo : Lo_Bound; Hi : Elem_Count)
   is null;

   procedure Lemma_Sum_Of_Step (L : Hash_Array; Lo : Lo_Bound; Hi : Elem_Count)
   is null;

   procedure Lemma_Sum_Split
     (L : Hash_Array; Lo : Lo_Bound; Mid : Elem_Count; Hi : Elem_Count)
   is
      P : constant Acc := Sum_Of (L, Lo, Mid);
   begin
      Lemma_Add_Zero (P);
      pragma Assert (Sum_Of (L, Lo, Mid) = Add (P, Sum_Of (L, Mid + 1, Mid)));
      for K in Mid .. Hi - 1 loop
         Lemma_Add_Congruent (Sum_Of (L, Lo, K), Add (P, Sum_Of (L, Mid + 1, K)),
                         Elem_Acc (L (K + 1)), Elem_Acc (L (K + 1)));
         Lemma_Add_Assoc (P, Sum_Of (L, Mid + 1, K), Elem_Acc (L (K + 1)));
         pragma Loop_Invariant
           (Sum_Of (L, Lo, K + 1) = Add (P, Sum_Of (L, Mid + 1, K + 1)));
      end loop;
   end Lemma_Sum_Split;

   procedure Lemma_Sum_Ext
     (L1, L2 : Hash_Array; Lo : Lo_Bound; Hi : Elem_Count) is
   begin
      for K in Lo .. Hi loop
         Lemma_Add_Congruent (Sum_Of (L1, Lo, K - 1), Sum_Of (L2, Lo, K - 1),
                         Elem_Acc (L1 (K)), Elem_Acc (L2 (K)));
         pragma Loop_Invariant (Sum_Of (L1, Lo, K) = Sum_Of (L2, Lo, K));
      end loop;
   end Lemma_Sum_Ext;

   procedure Lemma_Sum_Swap (L1, L2 : Hash_Array; I : Elem_Index) is
      F  : constant Elem_Index := L1'First;
      La : constant Elem_Count := L1'Last;
      X1 : constant Acc := Sum_Of (L1, F, I - 1);
      X2 : constant Acc := Sum_Of (L2, F, I - 1);
      A  : constant Acc := Elem_Acc (L1 (I));
      B  : constant Acc := Elem_Acc (L1 (I + 1));
   begin
      --  Head: L1 and L2 agree before I.
      Lemma_Sum_Ext (L1, L2, F, I - 1);
      --  The swapped pair.
      pragma Assert (Sum_Of (L1, F, I + 1) = Add (Add (X1, A), B));
      pragma Assert (Sum_Of (L2, F, I + 1) = Add (Add (X2, B), A));
      Lemma_Add_Exchange (X1, A, B);
      Lemma_Add_Congruent (X1, X2, B, B);
      Lemma_Add_Congruent (Add (X1, B), Add (X2, B), A, A);
      pragma Assert (Sum_Of (L1, F, I + 1) = Sum_Of (L2, F, I + 1));
      --  Tail: L1 and L2 agree after I + 1.
      Lemma_Sum_Ext (L1, L2, I + 2, La);
      Lemma_Sum_Split (L1, F, I + 1, La);
      Lemma_Sum_Split (L2, F, I + 1, La);
      Lemma_Add_Congruent (Sum_Of (L1, F, I + 1), Sum_Of (L2, F, I + 1),
                      Sum_Of (L1, I + 2, La), Sum_Of (L2, I + 2, La));
   end Lemma_Sum_Swap;

   --  Σ L2 (Lo .. Hi) = Σ L1 (Lo + 1 .. Hi + 1) where L2 is L1 shifted
   --  down by one.
   procedure Lemma_Sum_Shift
     (L1, L2 : Hash_Array; Lo : Lo_Bound; Hi : Elem_Count)
     with Ghost, Global => null,
          Pre  => Lo <= Elem_Max and then Hi < Elem_Max and then Lo <= Hi + 1
                  and then (if Lo <= Hi then
                              Lo >= L2'First and then Hi <= L2'Last
                              and then Lo + 1 >= L1'First
                              and then Hi + 1 <= L1'Last
                              and then (for all K in Lo .. Hi =>
                                          L2 (K) = L1 (K + 1))),
          Post => Sum_Of (L2, Lo, Hi) = Sum_Of (L1, Lo + 1, Hi + 1);

   procedure Lemma_Sum_Shift
     (L1, L2 : Hash_Array; Lo : Lo_Bound; Hi : Elem_Count) is
   begin
      for K in Lo .. Hi loop
         Lemma_Add_Congruent (Sum_Of (L2, Lo, K - 1), Sum_Of (L1, Lo + 1, K),
                              Elem_Acc (L2 (K)), Elem_Acc (L1 (K + 1)));
         pragma Loop_Invariant
           (Sum_Of (L2, Lo, K) = Sum_Of (L1, Lo + 1, K + 1));
      end loop;
   end Lemma_Sum_Shift;

   procedure Lemma_Sum_Delete
     (L1, L2 : Hash_Array; N : Elem_Count; J : Elem_Index)
   is
      X  : constant Acc := Sum_Of (L1, 1, J - 1);
      A  : constant Acc := Elem_Acc (L1 (J));
      T  : constant Acc := Sum_Of (L1, J + 1, N);
      X2 : constant Acc := Sum_Of (L2, 1, J - 1);
      T2 : constant Acc := Sum_Of (L2, J, N - 1);
   begin
      --  Σ L1 (1 .. N) = (X + A) + T.
      Lemma_Sum_Split (L1, 1, J, N);
      pragma Assert (Sum_Of (L1, 1, J) = Add (X, A));
      Lemma_Add_Congruent (Sum_Of (L1, 1, J), Add (X, A), T, T);
      Lemma_Eq_Trans (Sum_Of (L1, 1, N), Add (Sum_Of (L1, 1, J), T),
                      Add (Add (X, A), T));
      --  Σ L2 (1 .. N - 1) = X + T: the head is unchanged, the tail is
      --  shifted down by one.
      Lemma_Sum_Split (L2, 1, J - 1, N - 1);
      Lemma_Sum_Ext (L1, L2, 1, J - 1);
      Lemma_Sum_Shift (L1, L2, J, N - 1);
      Lemma_Add_Congruent (X2, X, T2, T);
      Lemma_Eq_Trans (Sum_Of (L2, 1, N - 1), Add (X2, T2), Add (X, T));
      --  (X + A) + T = (X + T) + A.
      Lemma_Add_Exchange (X, A, T);
      Lemma_Add_Congruent (Add (X, T), Sum_Of (L2, 1, N - 1), A, A);
      Lemma_Eq_Trans (Sum_Of (L1, 1, N), Add (Add (X, A), T),
                      Add (Add (X, T), A));
      Lemma_Eq_Trans (Sum_Of (L1, 1, N), Add (Add (X, T), A),
                      Add (Sum_Of (L2, 1, N - 1), A));
   end Lemma_Sum_Delete;

   --  Induction on N: L1 (N) sits at J = M (N) in L2. Deleting it from L2
   --  (L3) and renumbering M past J (M3) leaves a permutation of
   --  L1 (1 .. N - 1); the recursive call sums that, Lemma_Sum_Delete puts
   --  acc (L2 (J)) = acc (L1 (N)) back.
   procedure Lemma_Sum_Perm
     (L1, L2 : Hash_Array; M : Index_Map; N : Elem_Count)
   is
      J  : constant Elem_Index := (if N > 0 then M (N) else 1);
      L3 : constant Hash_Array (L2'Range) :=
        [for K in L2'Range =>
           (if K >= J and then K < N then L2 (K + 1) else L2 (K))];
      M3 : constant Index_Map (M'Range) :=
        [for I in M'Range =>
           (if I < N and then M (I) > J then M (I) - 1 else M (I))];
   begin
      if N > 0 then
         pragma Assert (for all I in 1 .. N - 1 => M (I) /= J);
         pragma Assert
           (for all I in 1 .. N - 1 =>
              M3 (I) <= N - 1 and then L3 (M3 (I)) = L1 (I));
         pragma Assert
           (for all I in 1 .. N - 1 =>
              (for all K in 1 .. N - 1 =>
                 (if I /= K then M3 (I) /= M3 (K))));
         Lemma_Sum_Perm (L1, L3, M3, N - 1);
         Lemma_Sum_Delete (L2, L3, N, J);
         Lemma_Add_Congruent
           (Sum_Of (L1, 1, N - 1), Sum_Of (L3, 1, N - 1),
            Elem_Acc (L1 (N)), Elem_Acc (L2 (J)));
         Lemma_Value_Congruent
           (Add (Sum_Of (L1, 1, N - 1), Elem_Acc (L1 (N))),
            Add (Sum_Of (L3, 1, N - 1), Elem_Acc (L2 (J))));
         Lemma_Value_Congruent
           (Sum_Of (L2, 1, N),
            Add (Sum_Of (L3, 1, N - 1), Elem_Acc (L2 (J))));
         Lemma_Value_Injective (Sum_Of (L1, 1, N), Sum_Of (L2, 1, N));
      end if;
   end Lemma_Sum_Perm;

   function Digest_Of (L : Hash_Array) return Digest_State is
      --  Proved; at run time only the Pre and Post are evaluated (each
      --  invariant would recompute Sum_Of: quadratic).
      pragma Assertion_Policy
        (Loop_Invariant => Ignore, Assert => Ignore, Ghost => Ignore);

      --  The congruence step, declared here so that the Ignore policy
      --  above applies to it and its calls are not executed (the policy
      --  of a ghost call is that of the called subprogram).
      procedure Step (X1, X2, Y : Acc)
        with Ghost, Global => null,
             Pre  => X1 = X2,
             Post => Add (X1, Y) = Add (X2, Y);

      procedure Step (X1, X2, Y : Acc) is
      begin
         Lemma_Add_Congruent (X1, X2, Y, Y);
      end Step;

      S : Digest_State := Empty;
   begin
      for I in L'Range loop
         Step (Sum (S), Sum_Of (L, L'First, I - 1), Elem_Acc (L (I)));
         S := With_Record (S, L (I));
         pragma Loop_Invariant
           (Count (S) = I - L'First + 1
            and then Sum (S) = Sum_Of (L, L'First, I));
      end loop;
      return S;
   end Digest_Of;

   ----------------------------------------------------------------------
   --  Models
   ----------------------------------------------------------------------

   procedure Lemma_Models_Empty (L : Hash_Array) is null;

   procedure Lemma_Models_Add
     (S : Digest_State; L1, L2 : Hash_Array; N : Elem_Count; H : Key256) is
   begin
      Lemma_Sum_Ext (L1, L2, 1, N);
      Lemma_Eq_Trans (Sum (S), Sum_Of (L1, 1, N), Sum_Of (L2, 1, N));
      Lemma_Add_Congruent (Sum (S), Sum_Of (L2, 1, N),
                           Elem_Acc (H), Elem_Acc (L2 (N + 1)));
   end Lemma_Models_Add;

   procedure Lemma_Models_Remove
     (S : Digest_State; L1, L2 : Hash_Array; N : Elem_Count; J : Elem_Index)
   is
      A : constant Acc := Elem_Acc (L1 (J));
      R : constant Acc := Sum_Of (L2, 1, N - 1);
   begin
      Lemma_Sum_Delete (L1, L2, N, J);
      Lemma_Eq_Trans (Sum (S), Sum_Of (L1, 1, N), Add (R, A));
      Lemma_Sub_Congruent (Sum (S), Add (R, A), A, A);
      Lemma_Sub_Add (R, A);
      Lemma_Eq_Trans (Sub (Sum (S), A), Sub (Add (R, A), A), R);
   end Lemma_Models_Remove;

   procedure Lemma_Models_Perm
     (S : Digest_State; L1, L2 : Hash_Array; M : Index_Map; N : Elem_Count)
   is
   begin
      Lemma_Sum_Perm (L1, L2, M, N);
      Lemma_Eq_Trans (Sum (S), Sum_Of (L1, 1, N), Sum_Of (L2, 1, N));
   end Lemma_Models_Perm;

   procedure Lemma_Models_Fingerprint
     (S1, S2 : Digest_State; L1, L2 : Hash_Array; M : Index_Map;
      N : Elem_Count)
   is
   begin
      Lemma_Models_Perm (S1, L1, L2, M, N);
      Lemma_Value_Congruent (Sum (S1), Sum_Of (L2, 1, N));
      Lemma_Value_Congruent (Sum (S2), Sum_Of (L2, 1, N));
      Lemma_Value_Injective (Sum (S1), Sum (S2));
      Lemma_Fingerprint_Congruent (S1, S2);
   end Lemma_Models_Fingerprint;

   procedure Lemma_Digest_Of_Models (L : Hash_Array) is
      D : constant Digest_State := Digest_Of (L);
   begin
      pragma Assert (Count (D) = L'Length);
   end Lemma_Digest_Of_Models;

   ----------------------------------------------------------------------
   --  Frontier
   ----------------------------------------------------------------------

   function Frontier_Sum (F : Kome.Frontier.State; K : Elem_Count) return Acc is
     (if K = 0 then Zero
      else Add (Frontier_Sum (F, K - 1),
                Elem_Acc (Kome.Frontier.Held (F, K).V.H)));

   procedure Lemma_Frontier_Sum_Step (F : Kome.Frontier.State; K : Elem_Count)
   is null;

   function State_Of (F : Kome.Frontier.State) return Digest_State is
      --  Proved; at run time only the Post is evaluated (see Digest_Of).
      pragma Assertion_Policy
        (Loop_Invariant => Ignore, Assert => Ignore, Ghost => Ignore);

      --  The congruence step, declared here so that the Ignore policy
      --  above applies to it and its calls are not executed (the policy
      --  of a ghost call is that of the called subprogram).
      procedure Step (X1, X2, Y : Acc)
        with Ghost, Global => null,
             Pre  => X1 = X2,
             Post => Add (X1, Y) = Add (X2, Y);

      procedure Step (X1, X2, Y : Acc) is
      begin
         Lemma_Add_Congruent (X1, X2, Y, Y);
      end Step;

      S : Digest_State := Empty;
   begin
      for I in 1 .. Kome.Frontier.Count (F) loop
         Step (Sum (S), Frontier_Sum (F, I - 1),
               Elem_Acc (Kome.Frontier.Held (F, I).V.H));
         S := With_Record (S, Kome.Frontier.Held (F, I).V.H);
         pragma Loop_Invariant
           (Count (S) = I and then Sum (S) = Frontier_Sum (F, I));
      end loop;
      return S;
   end State_Of;

   function Frontier_Digest (F : Kome.Frontier.State) return Hash256 is
      S : constant Digest_State := State_Of (F);
   begin
      Lemma_Fp_Congruent
        (Count (S), Sum (S), Frontier_Sum (F, Kome.Frontier.Count (F)));
      return Fingerprint (S);
   end Frontier_Digest;

   procedure Lemma_Frontier_Sum_List
     (F : Kome.Frontier.State; L : Hash_Array; K : Elem_Count) is
   begin
      for I in 1 .. K loop
         Lemma_Add_Congruent
           (Frontier_Sum (F, I - 1), Sum_Of (L, 1, I - 1),
            Elem_Acc (Kome.Frontier.Held (F, I).V.H), Elem_Acc (L (I)));
         pragma Loop_Invariant (Frontier_Sum (F, I) = Sum_Of (L, 1, I));
      end loop;
   end Lemma_Frontier_Sum_List;

   procedure Lemma_State_Of_Models (F : Kome.Frontier.State; L : Hash_Array)
   is
      N : constant Elem_Count := Kome.Frontier.Count (F);
      S : constant Digest_State := State_Of (F);
   begin
      Lemma_Frontier_Sum_List (F, L, N);
      Lemma_Eq_Trans (Sum (S), Frontier_Sum (F, N), Sum_Of (L, 1, N));
   end Lemma_State_Of_Models;

   procedure Lemma_Frontier_Digest_Perm
     (F1, F2 : Kome.Frontier.State; M : Index_Map)
   is
      N  : constant Elem_Count := Kome.Frontier.Count (F1);
      L1 : constant Hash_Array (1 .. N) :=
        [for I in 1 .. N => Kome.Frontier.Held (F1, I).V.H];
      L2 : constant Hash_Array (1 .. N) :=
        [for I in 1 .. N => Kome.Frontier.Held (F2, I).V.H];
   begin
      Lemma_Frontier_Sum_List (F1, L1, N);
      Lemma_Frontier_Sum_List (F2, L2, N);
      Lemma_Sum_Perm (L1, L2, M, N);
      Lemma_Value_Congruent (Frontier_Sum (F1, N), Sum_Of (L1, 1, N));
      Lemma_Value_Congruent (Sum_Of (L1, 1, N), Sum_Of (L2, 1, N));
      Lemma_Value_Congruent (Frontier_Sum (F2, N), Sum_Of (L2, 1, N));
      Lemma_Value_Injective (Frontier_Sum (F1, N), Frontier_Sum (F2, N));
      Lemma_Fp_Congruent (N, Frontier_Sum (F1, N), Frontier_Sum (F2, N));
   end Lemma_Frontier_Digest_Perm;

   ----------------------------------------------------------------------
   --  Prefix sums
   ----------------------------------------------------------------------

   --  ACC of the first K blocks. A function of its own so that the
   --  prover substitutes K by congruence: an argument written 64·K is an
   --  arithmetic term, and two of them (64·K, 64·B) are not merged from
   --  K = B the way two calls Block_Prefix (L, K), Block_Prefix (L, B) are.
   function Block_Prefix (L : Hash_Array; K : Natural) return Acc is
     (Sum_Of (L, 1, Block_Elems * K))
     with Ghost, Global => null,
          Pre => L'First = 1 and then K <= L'Length / Block_Elems;

   function Prefix_Valid (L : Hash_Array; P : Acc_Array) return Boolean is
     (L'First = 1 and then P'First = 1
      and then P'Length = L'Length / Block_Elems
      and then (for all K in P'Range => P (K) = Block_Prefix (L, K)));

   procedure Build_Prefix (L : Hash_Array; P : out Acc_Array) is
      --  Proved; at run time only the Pre and Post are evaluated.
      pragma Assertion_Policy
        (Loop_Invariant => Ignore, Assert => Ignore, Ghost => Ignore);

      --  The congruence step, declared here so that the Ignore policy
      --  above applies to it and its calls are not executed (the policy
      --  of a ghost call is that of the called subprogram).
      procedure Step (X1, X2, Y : Acc)
        with Ghost, Global => null,
             Pre  => X1 = X2,
             Post => Add (X1, Y) = Add (X2, Y);

      procedure Step (X1, X2, Y : Acc) is
      begin
         Lemma_Add_Congruent (X1, X2, Y, Y);
      end Step;

      R : Acc := Zero;
   begin
      P := [others => Zero];
      --  Block B covers L (64·(B - 1) + 1 .. 64·B). The elements after the
      --  last full block have no stored prefix (Range_Sum adds them).
      for B in 1 .. L'Length / Block_Elems loop
         pragma Assert (R = Block_Prefix (L, B - 1));
         for J in Block_Elems * (B - 1) + 1 .. Block_Elems * B loop
            Step (R, Sum_Of (L, 1, J - 1), Elem_Acc (L (J)));
            R := Add (R, Elem_Acc (L (J)));
            pragma Loop_Invariant (R = Sum_Of (L, 1, J));
            pragma Loop_Invariant
              (for all K in 1 .. B - 1 => P (K) = Block_Prefix (L, K));
         end loop;
         pragma Assert (R = Block_Prefix (L, B));
         P (B) := R;
         pragma Loop_Invariant (R = Block_Prefix (L, B));
         pragma Loop_Invariant
           (for all K in 1 .. B => P (K) = Block_Prefix (L, K));
      end loop;
   end Build_Prefix;

   function Range_Sum
     (L : Hash_Array; P : Acc_Array; Lo : Lo_Bound; Hi : Elem_Count) return Acc
   is
      --  Proved; at run time only Range_Sum's own Pre and Post (in the
      --  spec) are evaluated: the ghost steps below, and Prefix_Upto's
      --  contract, would each recompute sums over the whole list.
      pragma Assertion_Policy
        (Loop_Invariant => Ignore, Assert => Ignore, Ghost => Ignore,
         Pre => Ignore, Post => Ignore);

      --  The congruence step, declared here so that the Ignore policy
      --  above applies to it and its calls are not executed (the policy
      --  of a ghost call is that of the called subprogram).
      procedure Step (X1, X2, Y : Acc)
        with Ghost, Global => null,
             Pre  => X1 = X2,
             Post => Add (X1, Y) = Add (X2, Y);

      procedure Step (X1, X2, Y : Acc) is
      begin
         Lemma_Add_Congruent (X1, X2, Y, Y);
      end Step;

      --  Upper = X + Y, Lower = X, with X = Σ L (1 .. Lo - 1) and
      --  Y = Σ L (Lo .. Hi); so Upper - Lower = (Y + X) - X = Y.
      procedure Prove_Difference (Upper, Lower : Acc)
        with Ghost,
             Pre  => Lo <= Hi + 1 and then Hi <= L'Last and then L'First = 1
                     and then Upper = Sum_Of (L, 1, Hi)
                     and then Lower = Sum_Of (L, 1, Lo - 1),
             Post => Sub (Upper, Lower) = Sum_Of (L, Lo, Hi);

      procedure Prove_Difference (Upper, Lower : Acc) is
      begin
         Lemma_Sum_Split (L, 1, Lo - 1, Hi);
         Lemma_Add_Comm (Sum_Of (L, 1, Lo - 1), Sum_Of (L, Lo, Hi));
         Lemma_Sub_Add (Sum_Of (L, Lo, Hi), Sum_Of (L, 1, Lo - 1));
         Lemma_Sub_Congruent
           (Upper, Add (Sum_Of (L, Lo, Hi), Sum_Of (L, 1, Lo - 1)),
            Lower, Sum_Of (L, 1, Lo - 1));
      end Prove_Difference;

      --  Undo one step of the sum: R = X + Y gives R - Y = X.
      procedure Back_Step (R, X, Y : Acc)
        with Ghost, Global => null,
             Pre  => R = Add (X, Y),
             Post => Sub (R, Y) = X;

      procedure Back_Step (R, X, Y : Acc) is
      begin
         Lemma_Sub_Add (X, Y);
         Lemma_Sub_Congruent (R, Add (X, Y), Y, Y);
         Lemma_Eq_Trans (Sub (R, Y), Sub (Add (X, Y), Y), X);
      end Back_Step;

      --  ACC of L (1 .. X), from the nearest stored block boundary: X =
      --  64·q + r; when r > 32 and block q + 1 is stored, subtract the
      --  64 - r < 32 elements above X from P (q + 1); otherwise add the
      --  r <= 32 elements above 64·q to P (q) (r <= 63 in the tail after
      --  the last full block, which has no stored prefix above it).
      function Prefix_Upto (X : Elem_Count) return Acc
        with Global => (Input => (L, P)),
             Pre  => L'First = 1 and then P'First = 1
                     and then P'Length = L'Length / Block_Elems
                     and then Prefix_Valid (L, P)
                     and then X <= L'Last,
             Post => Prefix_Upto'Result = Sum_Of (L, 1, X);

      function Prefix_Upto (X : Elem_Count) return Acc is
         Q : constant Natural := X / Block_Elems;
         R : Acc := Zero;
      begin
         if X mod Block_Elems > Block_Elems / 2 and then Q < P'Length then
            R := P (Q + 1);
            pragma Assert (R = Block_Prefix (L, Q + 1));
            pragma Assert (R = Sum_Of (L, 1, Block_Elems * (Q + 1)));
            for J in reverse X + 1 .. Block_Elems * (Q + 1) loop
               Back_Step (R, Sum_Of (L, 1, J - 1), Elem_Acc (L (J)));
               R := Sub (R, Elem_Acc (L (J)));
               pragma Loop_Invariant (R = Sum_Of (L, 1, J - 1));
            end loop;
         else
            if Q > 0 then
               R := P (Q);
            end if;
            pragma Assert (R = Block_Prefix (L, Q));
            pragma Assert (R = Sum_Of (L, 1, Block_Elems * Q));
            for J in Block_Elems * Q + 1 .. X loop
               Step (R, Sum_Of (L, 1, J - 1), Elem_Acc (L (J)));
               R := Add (R, Elem_Acc (L (J)));
               pragma Loop_Invariant (R = Sum_Of (L, 1, J));
            end loop;
         end if;
         return R;
      end Prefix_Upto;

      Upper : constant Acc := Prefix_Upto (Hi);
      Lower : constant Acc := Prefix_Upto (Lo - 1);
   begin
      Prove_Difference (Upper, Lower);
      return Sub (Upper, Lower);
   end Range_Sum;

end Kome.Digest;
