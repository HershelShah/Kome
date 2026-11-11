pragma Ada_2022;
with Kome.Accumulator; use Kome.Accumulator;
package body Kome.Reconcile with SPARK_Mode is

   --  Proof style (CONVENTIONS.md): assertions use the public view (Count,
   --  Key, Frame_Len). The body asserts each quantified fact at the point
   --  where the provers need it. Where an ordering lemma is necessary, it
   --  asserts the fact one instance at a time.

   ----------------------------------------------------------------------
   --  Order lemmas. Key_Lt is a quantifier-free chain. The proof of each
   --  law unfolds the chain.
   ----------------------------------------------------------------------

   procedure Lemma_Key_Lt_Irrefl (A : Elem_Key) is null;

   procedure Lemma_Key_Lt_Asym (A, B : Elem_Key) is null;

   procedure Lemma_Key_Lt_Trans (A, B, C : Elem_Key) is null;

   procedure Lemma_Key_Trichotomy (A, B : Elem_Key) is null;

   procedure Lemma_Key_Le_Lt_Trans (A, B, C : Elem_Key) is
   begin
      Lemma_Key_Trichotomy (A, B);
      if Key_Lt (A, B) then
         Lemma_Key_Lt_Trans (A, B, C);
      end if;
   end Lemma_Key_Le_Lt_Trans;

   procedure Lemma_Data_Key_Order (A, B : Header) is null;

   procedure Lemma_Key_Ranges (R : Header) is null;

   --  Transitivity of "=" on Acc (as in the body of Kome.Digest): Ada "="
   --  on Acc is element-wise, so the prover does not always chain two
   --  equalities by itself.
   procedure Lemma_Acc_Eq_Trans (A, B, C : Acc) with
     Ghost, Global => null,
     Pre  => A = B and then B = C,
     Post => A = C
   is
   begin
      Lemma_Value_Congruent (A, B);
      Lemma_Value_Congruent (B, C);
      Lemma_Value_Injective (A, C);
   end Lemma_Acc_Eq_Trans;

   ----------------------------------------------------------------------
   --  Key_Lt is bytewise order on the wire key. The 82 bytes are tag ‖
   --  ent[16] ‖ sub ‖ fh[32] ‖ h[32]. Kome.Keys decodes each word field
   --  (Wire_Id128 / Wire_Key256 are To_Id128 / To_Key256 of the slice).
   --  The Id128 and Key256 laws of Kome.Keys give the field orders.
   --  Key_Lt is their lexicographic composition with the two bytes.
   ----------------------------------------------------------------------

   --  The three word fields of a wire key, as the Kome.Keys byte views.
   procedure Lemma_Fields (A : Key_Wire) with
     Ghost, Global => null,
     Post => Wire_Id128 (A, 1) = Kome.Keys.To_Id128 (Kome.Keys.Id_Bytes (A (1 .. 16)))
             and then Wire_Key256 (A, 18)
                        = Kome.Keys.To_Key256 (Kome.Keys.Key_Bytes (A (18 .. 49)))
             and then Wire_Key256 (A, 50)
                        = Kome.Keys.To_Key256 (Kome.Keys.Key_Bytes (A (50 .. 81)))
             and then (for all J in Kome.Keys.Id_Index =>
                         Kome.Keys.Id_Bytes (A (1 .. 16)) (J) = A (1 + J))
             and then (for all J in Kome.Keys.Key_Index =>
                         Kome.Keys.Key_Bytes (A (18 .. 49)) (J) = A (18 + J))
             and then (for all J in Kome.Keys.Key_Index =>
                         Kome.Keys.Key_Bytes (A (50 .. 81)) (J) = A (50 + J))
   is
   begin
      Kome.Keys.Lemma_Id_Slide (A (1 .. 16));
      Kome.Keys.Lemma_Key_Slide (A (18 .. 49));
      Kome.Keys.Lemma_Key_Slide (A (50 .. 81));
      pragma Assert (Wire_Id128 (A, 1) = Kome.Keys.To_Id128 (A (1 .. 16)));
      pragma Assert (Wire_Key256 (A, 18) = Kome.Keys.To_Key256 (A (18 .. 49)));
      pragma Assert (Wire_Key256 (A, 50) = Kome.Keys.To_Key256 (A (50 .. 81)));
   end Lemma_Fields;

   procedure Lemma_Key_Eq_Is_Bytewise (A, B : Key_Wire) is
   begin
      Lemma_Fields (A);
      Lemma_Fields (B);
      Kome.Keys.Lemma_Id_Eq_Is_Bytewise
        (Kome.Keys.Id_Bytes (A (1 .. 16)), Kome.Keys.Id_Bytes (B (1 .. 16)));
      Kome.Keys.Lemma_Key_Eq_Is_Bytewise
        (Kome.Keys.Key_Bytes (A (18 .. 49)), Kome.Keys.Key_Bytes (B (18 .. 49)));
      Kome.Keys.Lemma_Key_Eq_Is_Bytewise
        (Kome.Keys.Key_Bytes (A (50 .. 81)), Kome.Keys.Key_Bytes (B (50 .. 81)));
      if Wire_Key (A, 0) = Wire_Key (B, 0) then
         pragma Assert (A (0) = B (0));
         pragma Assert (A (17) = B (17));
         pragma Assert (Kome.Keys.Id_Bytes (A (1 .. 16)) = Kome.Keys.Id_Bytes (B (1 .. 16)));
         pragma Assert (Kome.Keys.Key_Bytes (A (18 .. 49)) = Kome.Keys.Key_Bytes (B (18 .. 49)));
         pragma Assert (Kome.Keys.Key_Bytes (A (50 .. 81)) = Kome.Keys.Key_Bytes (B (50 .. 81)));
         pragma Assert (for all J in 1 .. 16 => A (J) = B (J));
         pragma Assert (for all J in 18 .. 49 => A (J) = B (J));
         pragma Assert (for all J in 50 .. 81 => A (J) = B (J));
         pragma Assert (for all J in A'Range => A (J) = B (J));
         pragma Assert (A = B);
      end if;
   end Lemma_Key_Eq_Is_Bytewise;

   procedure Lemma_Key_Lt_First_Difference (A, B : Key_Wire; I : Natural) is
   begin
      Lemma_Fields (A);
      Lemma_Fields (B);
      if I = 0 then
         pragma Assert (Wire_Key (A, 0).K /= Wire_Key (B, 0).K);
      elsif I <= 16 then
         pragma Assert (Wire_Key (A, 0).K = Wire_Key (B, 0).K);
         Kome.Keys.Lemma_Id_Lt_First_Difference
           (Kome.Keys.Id_Bytes (A (1 .. 16)), Kome.Keys.Id_Bytes (B (1 .. 16)), I - 1);
         Kome.Keys.Lemma_Id_Lt_First_Difference
           (Kome.Keys.Id_Bytes (B (1 .. 16)), Kome.Keys.Id_Bytes (A (1 .. 16)), I - 1);
         pragma Assert (Wire_Id128 (A, 1) /= Wire_Id128 (B, 1));
      elsif I = 17 then
         pragma Assert (Wire_Key (A, 0).K = Wire_Key (B, 0).K);
         pragma Assert (for all J in 1 .. 16 => A (J) = B (J));
         pragma Assert (Wire_Id128 (A, 1) = Wire_Id128 (B, 1));
         pragma Assert (Wire_Key (A, 0).Sub /= Wire_Key (B, 0).Sub);
      elsif I <= 49 then
         pragma Assert (Wire_Key (A, 0).K = Wire_Key (B, 0).K);
         pragma Assert (for all J in 1 .. 16 => A (J) = B (J));
         pragma Assert (Wire_Id128 (A, 1) = Wire_Id128 (B, 1));
         pragma Assert (Wire_Key (A, 0).Sub = Wire_Key (B, 0).Sub);
         Kome.Keys.Lemma_Lt_First_Difference
           (Kome.Keys.Key_Bytes (A (18 .. 49)), Kome.Keys.Key_Bytes (B (18 .. 49)), I - 18);
         Kome.Keys.Lemma_Lt_First_Difference
           (Kome.Keys.Key_Bytes (B (18 .. 49)), Kome.Keys.Key_Bytes (A (18 .. 49)), I - 18);
         pragma Assert (Wire_Key256 (A, 18) /= Wire_Key256 (B, 18));
      else
         pragma Assert (Wire_Key (A, 0).K = Wire_Key (B, 0).K);
         pragma Assert (for all J in 1 .. 16 => A (J) = B (J));
         pragma Assert (Wire_Id128 (A, 1) = Wire_Id128 (B, 1));
         pragma Assert (Wire_Key (A, 0).Sub = Wire_Key (B, 0).Sub);
         pragma Assert (for all J in 18 .. 49 => A (J) = B (J));
         pragma Assert (Wire_Key256 (A, 18) = Wire_Key256 (B, 18));
         Kome.Keys.Lemma_Lt_First_Difference
           (Kome.Keys.Key_Bytes (A (50 .. 81)), Kome.Keys.Key_Bytes (B (50 .. 81)), I - 50);
      end if;
   end Lemma_Key_Lt_First_Difference;

   ----------------------------------------------------------------------
   --  The Noise prologue (S11)
   ----------------------------------------------------------------------

   function Prologue (Cid : Hash256) return Prologue_Bytes is
      R : Prologue_Bytes := [others => 0];
   begin
      R (0 .. Prologue_Tag_Len - 1) := Prologue_Tag;
      R (Prologue_Tag_Len .. Prologue_Tag_Len + NS_Len - 1) := Kome.Records.NS_Of (Cid);
      R (Prologue_Len - 1) := Proto_Version;
      return R;
   end Prologue;

   ----------------------------------------------------------------------
   --  Frame tables
   ----------------------------------------------------------------------

   procedure Clear_Table (T : out Frame_Table) is
   begin
      T.N    := 0;
      T.Used := 0;
      T.Offs := [others => 1];
      T.Lens := [others => 1];
      T.Pool := [others => 0];
   end Clear_Table;

   procedure Add_Frame
     (T      : in out Frame_Table;
      F      : Byte_Array;
      Result : out Snap_Status)
   is
   begin
      if F'Length not in Frame_Size then
         Result := Snap_Too_Large;
         return;
      end if;
      if T.N = T.Cap or else F'Length > T.Pool_Cap - T.Used then
         Result := Snap_No_Space;
         return;
      end if;
      declare
         Old : constant Frame_Table := T with Ghost;
         N   : constant Elem_Index := T.N + 1;
         Off : constant Positive := T.Used + 1;
         L   : constant Frame_Size := F'Length;
      begin
         T.Offs (N) := Off;
         T.Lens (N) := L;
         T.Pool (Off .. Off + L - 1) := F;
         T.Used := T.Used + L;
         T.N := N;
         --  Bridge.
         pragma Assert (for all J in 1 .. N - 1 =>
                          T.Offs (J) = Old.Offs (J) and then T.Lens (J) = Old.Lens (J));
         pragma Assert (for all X in 1 .. Old.Used => T.Pool (X) = Old.Pool (X));
         pragma Assert (for all J in 1 .. N - 1 => Entry_In_Pool (T, J));
         pragma Assert (Entry_In_Pool (T, N));
         pragma Assert (Table_Valid (T));
         pragma Assert (Table_Frame (T, N) = F);
         pragma Assert (for all J in 1 .. N - 1 =>
                          Table_Len (T, J) = Table_Len (Old, J)
                          and then Table_Frame (T, J) = Table_Frame (Old, J));
      end;
      Result := Snap_OK;
   end Add_Frame;

   ----------------------------------------------------------------------
   --  Snapshot
   ----------------------------------------------------------------------

   procedure Clear (S : out Snapshot) is
   begin
      S.N    := 0;
      S.Used := 0;
      S.E    := [others => (others => <>)];
      S.Hs   := [others => (others => 0)];
   end Clear;

   procedure Append
     (S      : in out Snapshot;
      K      : Elem_Key;
      L      : Frame_Size;
      Src    : Elem_Index;
      Result : out Snap_Status)
   is
   begin
      if S.N > 0 and then not Key_Lt (Key (S, S.N), K) then
         Result := Snap_Unsorted;
         return;
      end if;
      if S.N = S.Cap then
         Result := Snap_No_Space;
         return;
      end if;

      declare
         Old : constant Snapshot := S with Ghost;
         N   : constant Elem_Index := S.N + 1;
      begin
         --  Every held key is below K: the last key is below K, and the
         --  other keys are below the last key (pairwise order).
         for I in 1 .. S.N loop
            if I < S.N then
               pragma Assert (Key_Lt (Key (S, I), Key (S, S.N)));
               Lemma_Key_Lt_Trans (Key (S, I), Key (S, S.N), K);
            end if;
            pragma Loop_Invariant (for all J in 1 .. I => Key_Lt (Key (S, J), K));
         end loop;
         pragma Assert (for all J in 1 .. S.N => Key_Lt (Key (Old, J), K));

         S.E (N)  := (K => K.K, Ent => K.Ent, Sub => K.Sub, FH => K.FH,
                      Len => L, Src => Src);
         S.Hs (N) := K.H;
         S.Used := S.Used + Byte_Total (L);
         S.N := N;

         --  Bridge.
         pragma Assert (for all J in 1 .. N - 1 => Key (S, J) = Key (Old, J));
         pragma Assert (for all J in 1 .. N - 1 => S.E (J) = Old.E (J));
         pragma Assert (Key (S, N) = K);
         pragma Assert (for all J in 1 .. N - 1 => Key_Lt (Key (S, J), Key (S, N)));
         pragma Assert
           (for all I in 1 .. N =>
              (for all J in I + 1 .. N => Key_Lt (Key (S, I), Key (S, J))));
         pragma Assert (Valid (S));
      end;
      Result := Snap_OK;
   end Append;

   procedure Seal (S : Snapshot; P : out Prefix) is
   begin
      Kome.Digest.Build_Prefix (S.Hs (1 .. S.N), P.A);
   end Seal;

   procedure Lemma_Frame_Ships (L : Natural) is null;

   ----------------------------------------------------------------------
   --  Fingerprints from the prefix sums (D15).
   ----------------------------------------------------------------------

   procedure Fingerprint_Of
     (S     : Snapshot;
      P     : Prefix;
      First : Lo_Bound;
      Last  : Elem_Count;
      FP    : out Hash256)
   is
      A    : Acc;
      Adds : Kome.Digest.Add_Count;
      Subs : Natural;
   begin
      if Last < First then
         FP := Kome.Digest.Fingerprint (Kome.Digest.Empty);
         return;
      end if;
      Kome.Digest.Range_Sum (S.Hs (1 .. S.N), P.A, First, Last, A, Adds, Subs);
      pragma Assert (A = Kome.Digest.Sum_Of (S.Hs (1 .. S.N), First, Last));
      --  The sum over the slice First .. Last is the same sum.
      Kome.Digest.Lemma_Sum_Ext (S.Hs (First .. Last), S.Hs (1 .. S.N), First, Last);
      pragma Assert (Kome.Digest.Sum_Of (S.Hs (First .. Last), First, Last)
                     = Kome.Digest.Sum_Of (S.Hs (1 .. S.N), First, Last));
      Lemma_Acc_Eq_Trans (Kome.Digest.Sum (Kome.Digest.Digest_Of (S.Hs (First .. Last))),
                          Kome.Digest.Sum_Of (S.Hs (First .. Last), First, Last),
                          A);
      Kome.Digest.Lemma_Fp_Congruent
        (Last + 1 - First,
         Kome.Digest.Sum (Kome.Digest.Digest_Of (S.Hs (First .. Last))), A);
      FP := Kome.Digest.Fp (Last + 1 - First, A);
   end Fingerprint_Of;

   ----------------------------------------------------------------------
   --  The snapshot of a frontier (A12, S18): the authorization records are
   --  inserted into key order (their slot order is local to the replica),
   --  then the data row (already in key order) is appended. Each element
   --  records its source index in F.
   ----------------------------------------------------------------------

   --  T6 for the snapshot: the hashes of S are a permutation of the
   --  hashes of F (Src is the witness), so the digests are equal.
   procedure Lemma_Snapshot_Digest (F : Kome.Frontier.State; S : Snapshot; N : Elem_Count)
   with
     Ghost, Global => null,
     Pre  => N = Kome.Frontier.Count (F) and then N = S.N and then N >= 1
             and then (for all J in 1 .. N =>
                         S.E (J).Src <= N
                         and then S.Hs (J) = Kome.Frontier.Held (F, S.E (J).Src).V.H)
             and then (for all I in 1 .. N =>
                         (for all J in 1 .. N =>
                            (if I /= J then S.E (I).Src /= S.E (J).Src))),
     Post => Range_Fp (S, 1, N) = Kome.Digest.Frontier_Digest (F)
   is
      L1 : Kome.Digest.Hash_Array (1 .. N) := [others => (others => 0)];
      M  : constant Kome.Digest.Index_Map (1 .. N) := [for J in 1 .. N => S.E (J).Src];
      L2 : constant Kome.Digest.Hash_Array (1 .. N) := S.Hs (1 .. N);
   begin
      for I in 1 .. N loop
         pragma Loop_Invariant
           (for all I2 in 1 .. I - 1 => L1 (I2) = Kome.Frontier.Held (F, I2).V.H);
         L1 (I) := Kome.Frontier.Held (F, I).V.H;
      end loop;
      pragma Assert (for all J in 1 .. N => M (J) <= N and then L1 (M (J)) = L2 (J));
      pragma Assert
        (for all I in 1 .. N =>
           (for all K in 1 .. N => (if I /= K then M (I) /= M (K))));
      Kome.Digest.Lemma_Is_Perm_Intro (L2, L1, M, N);
      Kome.Digest.Lemma_Sum_Perm (L2, L1, M, N);
      Kome.Digest.Lemma_Frontier_Sum_List (F, L1, N);
      Kome.Digest.Lemma_Sum_Ext (L2, S.Hs (1 .. N), 1, N);
      pragma Assert (Kome.Digest.Sum_Of (L2, 1, N) = Kome.Digest.Sum_Of (S.Hs (1 .. N), 1, N));
      Lemma_Acc_Eq_Trans (Kome.Digest.Sum_Of (S.Hs (1 .. N), 1, N),
                          Kome.Digest.Sum_Of (L2, 1, N),
                          Kome.Digest.Sum_Of (L1, 1, N));
      Lemma_Acc_Eq_Trans (Kome.Digest.Sum_Of (S.Hs (1 .. N), 1, N),
                          Kome.Digest.Sum_Of (L1, 1, N),
                          Kome.Digest.Frontier_Sum (F, N));
      Lemma_Acc_Eq_Trans (Kome.Digest.Sum (Kome.Digest.Digest_Of (S.Hs (1 .. N))),
                          Kome.Digest.Sum_Of (S.Hs (1 .. N), 1, N),
                          Kome.Digest.Frontier_Sum (F, N));
      Kome.Digest.Lemma_Fp_Congruent
        (N, Kome.Digest.Sum (Kome.Digest.Digest_Of (S.Hs (1 .. N))),
         Kome.Digest.Frontier_Sum (F, N));
   end Lemma_Snapshot_Digest;

   --  T6 for the empty snapshot.
   procedure Lemma_Digest_Of_Empty (F : Kome.Frontier.State; S : Snapshot) with
     Ghost, Global => null,
     Pre  => Kome.Frontier.Count (F) = 0 and then S.N = 0,
     Post => Range_Fp (S, 1, 0) = Kome.Digest.Frontier_Digest (F)
   is
      L : constant Kome.Digest.Hash_Array (1 .. 0) := [];
   begin
      Kome.Digest.Lemma_Frontier_Sum_List (F, L, 0);
      Kome.Digest.Lemma_Sum_Of_Empty (L, 1, 0);
      Lemma_Acc_Eq_Trans (Kome.Digest.Frontier_Sum (F, 0), Kome.Digest.Sum_Of (L, 1, 0), Zero);
      Kome.Digest.Lemma_Fp_Congruent (0, Zero, Kome.Digest.Frontier_Sum (F, 0));
   end Lemma_Digest_Of_Empty;

   --  Element J of S is the held record Src of F, with its frame length
   --  in T. A function with a body, not an expression function: its
   --  meaning is the Post, so a goal Good (F, T, S, I) keeps the term
   --  Good (F, T, S, I), which instantiates a hypothesis "for all J =>
   --  Good (F, T, S, J)" (an inlined body would not).
   function Good
     (F : Kome.Frontier.State; T : Frame_Table; S : Snapshot; J : Elem_Index)
      return Boolean
   with Ghost, Global => null,
     Post => Good'Result =
               (J <= S.N and then J <= S.Cap
                and then S.E (J).Src <= Kome.Frontier.Count (F)
                and then S.E (J).Src <= T.N and then T.N <= T.Cap
                and then Key (S, J) = Key_Of (Kome.Frontier.Held (F, S.E (J).Src))
                and then T.Lens (S.E (J).Src) = S.E (J).Len);

   function Good
     (F : Kome.Frontier.State; T : Frame_Table; S : Snapshot; J : Elem_Index)
      return Boolean
   is
   begin
      return (J <= S.N and then J <= S.Cap
                and then S.E (J).Src <= Kome.Frontier.Count (F)
                and then S.E (J).Src <= T.N and then T.N <= T.Cap
                and then Key (S, J) = Key_Of (Kome.Frontier.Held (F, S.E (J).Src))
                and then T.Lens (S.E (J).Src) = S.E (J).Len);
   end Good;

   --  The sources of a sorted snapshot of held records are distinct:
   --  two elements with one source would have one key.
   procedure Lemma_Sources_Distinct
     (F : Kome.Frontier.State; T : Frame_Table; S : Snapshot)
   with
     Ghost, Global => null,
     Pre  => Valid (S) and then (for all J in 1 .. S.N => Good (F, T, S, J)),
     Post => (for all I in 1 .. S.N =>
                (for all J in 1 .. S.N => (if I /= J then S.E (I).Src /= S.E (J).Src)))
   is
   begin
      for I in 1 .. S.N loop
         for J in 1 .. S.N loop
            pragma Assert (Good (F, T, S, I));
            pragma Assert (Good (F, T, S, J));
            if I < J then
               pragma Assert (Key_Lt (Key (S, I), Key (S, J)));
               Lemma_Key_Lt_Irrefl (Key (S, I));
               if S.E (I).Src = S.E (J).Src then
                  pragma Assert (Key (S, I) = Key (S, J));
                  Lemma_Key_Lt_Irrefl (Key (S, I));
               end if;
               pragma Assert (S.E (I).Src /= S.E (J).Src);
            elsif J < I then
               pragma Assert (Key_Lt (Key (S, J), Key (S, I)));
               Lemma_Key_Lt_Irrefl (Key (S, J));
               if S.E (I).Src = S.E (J).Src then
                  pragma Assert (Key (S, J) = Key (S, I));
                  Lemma_Key_Lt_Irrefl (Key (S, J));
               end if;
               pragma Assert (S.E (I).Src /= S.E (J).Src);
            end if;
            pragma Loop_Invariant
              (for all J2 in 1 .. J => (if I /= J2 then S.E (I).Src /= S.E (J2).Src));
         end loop;
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              (for all J2 in 1 .. S.N => (if I2 /= J2 then S.E (I2).Src /= S.E (J2).Src)));
      end loop;
   end Lemma_Sources_Distinct;

   procedure Snapshot_Of
     (F      : Kome.Frontier.State;
      T      : Frame_Table;
      S      : out Snapshot;
      Result : out Snap_Status)
   is
      --  The insertions and their per-step proofs are proved; their
      --  run-time checks would be cubic in |F| (Valid is pairwise), so
      --  they do not execute (CONVENTIONS.md; listed in the report for
      --  IMPLEMENTATION_PLAN.md). The Post of Snapshot_Of executes.
      pragma Assertion_Policy
        (Loop_Invariant => Ignore, Assert => Ignore, Ghost => Ignore,
         Pre => Ignore, Post => Ignore);

      N   : constant Elem_Count := Kome.Frontier.Count (F);
      DC  : constant Elem_Count := Kome.Frontier.Data_Count (F);
      Pos : Elem_Index;
      St  : Snap_Status;

      --  Insert the element (K, L, Src) at its place in key order. Pos is
      --  its index: the elements before it stay, those after it move up
      --  by one. Snap_Unsorted (nothing is inserted) when K is already
      --  held. Declared here so that the Ignore policy above applies to
      --  its contract and to its ghost steps.
      procedure Insert
        (S      : in out Snapshot;
         K      : Elem_Key;
         L      : Frame_Size;
         Src    : Elem_Index;
         Pos    : out Elem_Index;
         Result : out Snap_Status)
      with
        Global => null,
        Pre    => Valid (S) and then S.N < S.Cap,
        Post   => Valid (S) and then Result in Snap_OK | Snap_Unsorted
          and then (if Result = Snap_OK then
                      S.N = S.N'Old + 1 and then Pos <= S.N
                      and then Key (S, Pos) = K
                      and then S.E (Pos).Len = L and then S.E (Pos).Src = Src
                      and then (for all J in 1 .. Pos - 1 =>
                                  S.E (J) = S'Old.E (J) and then S.Hs (J) = S'Old.Hs (J))
                      and then (for all J in Pos + 1 .. S.N =>
                                  S.E (J) = S'Old.E (J - 1)
                                  and then S.Hs (J) = S'Old.Hs (J - 1))
                    else S.N = S.N'Old)
      is
         N   : constant Elem_Count := S.N;
         P   : Lo_Bound := N + 1;
         Old : constant Snapshot := S with Ghost;

         procedure Tri (A, B : Elem_Key) with
           Ghost, Global => null,
           Post => Key_Lt (A, B) or else A = B or else Key_Lt (B, A)
         is
         begin
            Lemma_Key_Trichotomy (A, B);
         end Tri;

         --  Every key before the place is below K.
         procedure Below with
           Ghost, Global => (Input => (S, K, P)),
           Pre  => Valid (S) and then P >= 2 and then P <= S.N + 1
                   and then Key_Lt (Key (S, P - 1), K),
           Post => (for all J in 1 .. P - 1 => Key_Lt (Key (S, J), K))
         is
         begin
            for J in 1 .. P - 1 loop
               if J < P - 1 then
                  pragma Assert (Key_Lt (Key (S, J), Key (S, P - 1)));
                  Lemma_Key_Lt_Trans (Key (S, J), Key (S, P - 1), K);
               end if;
               pragma Loop_Invariant (for all J2 in 1 .. J => Key_Lt (Key (S, J2), K));
            end loop;
         end Below;

         --  The pairwise order after the insertion, one row at a time.
         procedure Order with
           Ghost, Global => (Input => (S, K, P), Proof_In => Old),
           Pre  => Valid (Old) and then S.N = Old.N + 1 and then P <= S.N
                   and then Key (S, P) = K
                   and then (for all X in 1 .. P - 1 =>
                               Key (S, X) = Key (Old, X) and then Key_Lt (Key (S, X), K))
                   and then (for all X in P + 1 .. S.N =>
                               Key (S, X) = Key (Old, X - 1)
                               and then Key_Lt (K, Key (S, X))),
           Post => (for all I in 1 .. S.N =>
                      (for all J in I + 1 .. S.N => Key_Lt (Key (S, I), Key (S, J))))
         is
         begin
            for I in 1 .. S.N loop
               for J in I + 1 .. S.N loop
                  if I < P and then J > P then
                     Lemma_Key_Lt_Trans (Key (S, I), K, Key (S, J));
                  elsif I > P then
                     pragma Assert (Key_Lt (Key (Old, I - 1), Key (Old, J - 1)));
                  elsif J < P then
                     pragma Assert (Key_Lt (Key (Old, I), Key (Old, J)));
                  end if;
                  pragma Loop_Invariant
                    (for all J2 in I + 1 .. J => Key_Lt (Key (S, I), Key (S, J2)));
               end loop;
               pragma Loop_Invariant
                 (for all I2 in 1 .. I =>
                    (for all J2 in I2 + 1 .. S.N => Key_Lt (Key (S, I2), Key (S, J2))));
            end loop;
         end Order;

      begin
         Pos := 1;
         --  The place: the first index whose key is above K.
         loop
            pragma Loop_Invariant (P in 1 .. N + 1);
            pragma Loop_Invariant (for all J in P .. N => Key_Lt (K, Key (S, J)));
            pragma Loop_Variant (Decreases => P);
            exit when P = 1 or else not Key_Lt (K, Key (S, P - 1));
            P := P - 1;
         end loop;
         if P > 1 then
            Tri (K, Key (S, P - 1));
            if Key (S, P - 1) = K then
               Result := Snap_Unsorted;
               return;
            end if;
            pragma Assert (Key_Lt (Key (S, P - 1), K));
            Below;
         end if;
         pragma Assert (for all J in 1 .. P - 1 => Key_Lt (Key (Old, J), K));
         pragma Assert (for all J in P .. N => Key_Lt (K, Key (Old, J)));

         --  Move the elements P .. N up by one.
         for J in reverse P .. N loop
            S.E (J + 1) := S.E (J);
            S.Hs (J + 1) := S.Hs (J);
            pragma Loop_Invariant (S.N = Old.N and then S.Used = Old.Used);
            pragma Loop_Invariant
              (for all X in 1 .. J => S.E (X) = Old.E (X) and then S.Hs (X) = Old.Hs (X));
            pragma Loop_Invariant
              (for all X in J + 1 .. N + 1 =>
                 S.E (X) = Old.E (X - 1) and then S.Hs (X) = Old.Hs (X - 1));
         end loop;
         pragma Assert
           (for all X in 1 .. P - 1 => S.E (X) = Old.E (X) and then S.Hs (X) = Old.Hs (X));
         pragma Assert
           (for all X in P + 1 .. N + 1 =>
              S.E (X) = Old.E (X - 1) and then S.Hs (X) = Old.Hs (X - 1));

         S.E (P)  := (K => K.K, Ent => K.Ent, Sub => K.Sub, FH => K.FH,
                      Len => L, Src => Src);
         S.Hs (P) := K.H;
         S.Used := S.Used + Byte_Total (L);
         S.N := N + 1;
         Pos := P;

         pragma Assert (Key (S, P) = K);
         pragma Assert (for all X in 1 .. P - 1 => Key (S, X) = Key (Old, X));
         pragma Assert (for all X in P + 1 .. N + 1 => Key (S, X) = Key (Old, X - 1));
         Order;
         pragma Assert (Valid (S));
         Result := Snap_OK;
      end Insert;

      --  After an insertion at Pos, every element is still Good: those
      --  before Pos are the old ones, those after it the old ones moved
      --  up by one, and Pos is the new one.
      procedure Shift (Old, S : Snapshot; Pos : Elem_Index) with
        Ghost, Global => (Proof_In => (F, T)),
        Pre  => S.N = Old.N + 1 and then Pos <= S.N
                and then (for all J in 1 .. Old.N => Good (F, T, Old, J))
                and then Good (F, T, S, Pos)
                and then (for all J in 1 .. Pos - 1 =>
                            S.E (J) = Old.E (J) and then S.Hs (J) = Old.Hs (J))
                and then (for all J in Pos + 1 .. S.N =>
                            S.E (J) = Old.E (J - 1) and then S.Hs (J) = Old.Hs (J - 1)),
        Post => (for all J in 1 .. S.N => Good (F, T, S, J))
      is
      begin
         for J in 1 .. S.N loop
            if J < Pos then
               pragma Assert (Good (F, T, Old, J));
               pragma Assert (S.E (J) = Old.E (J) and then S.Hs (J) = Old.Hs (J));
            elsif J > Pos then
               pragma Assert (Good (F, T, Old, J - 1));
               pragma Assert (S.E (J) = Old.E (J - 1) and then S.Hs (J) = Old.Hs (J - 1));
            end if;
            pragma Assert (Good (F, T, S, J));
            pragma Loop_Invariant (for all J2 in 1 .. J => Good (F, T, S, J2));
         end loop;
      end Shift;

      --  The facts of Good, element by element (each goal names Good
      --  (F, T, S, J), so the hypothesis instantiates).
      procedure Unpack with
        Ghost, Global => (Input => S, Proof_In => (F, T)),
        Pre  => T.N <= T.Cap and then (for all J in 1 .. S.N => Good (F, T, S, J)),
        Post => Linked (S, T)
                and then (for all I in 1 .. S.N =>
                   (S.E (I).Src <= Kome.Frontier.Count (F)
                       and then S.E (I).Src <= T.N
                       and then Key (S, I) = Key_Of (Kome.Frontier.Held (F, S.E (I).Src))
                       and then T.Lens (S.E (I).Src) = S.E (I).Len
                       and then S.Hs (I) = Kome.Frontier.Held (F, S.E (I).Src).V.H))
      is
      begin
         for J in 1 .. S.N loop
            pragma Assert (Good (F, T, S, J));
            pragma Assert (Key (S, J).H = S.Hs (J));
            pragma Loop_Invariant
              (for all I in 1 .. J =>
                 (S.E (I).Src <= Kome.Frontier.Count (F)
                       and then S.E (I).Src <= T.N
                       and then Key (S, I) = Key_Of (Kome.Frontier.Held (F, S.E (I).Src))
                       and then T.Lens (S.E (I).Src) = S.E (I).Len
                       and then S.Hs (I) = Kome.Frontier.Held (F, S.E (I).Src).V.H));
         end loop;
      end Unpack;

      procedure Empty_Digest with
        Ghost, Global => (Input => (F, S)),
        Pre  => Kome.Frontier.Count (F) = 0 and then S.N = 0,
        Post => Range_Fp (S, 1, 0) = Kome.Digest.Frontier_Digest (F)
      is
      begin
         Lemma_Digest_Of_Empty (F, S);
      end Empty_Digest;

      procedure Distinct with
        Ghost, Global => (Input => (F, T, S)),
        Pre  => Valid (S) and then (for all J in 1 .. S.N => Good (F, T, S, J)),
        Post => (for all I in 1 .. S.N =>
                   (for all J in 1 .. S.N => (if I /= J then S.E (I).Src /= S.E (J).Src)))
      is
      begin
         Lemma_Sources_Distinct (F, T, S);
      end Distinct;

      procedure Digest with
        Ghost, Global => (Input => (F, S, N)),
        Pre  => N = Kome.Frontier.Count (F) and then N = S.N and then N >= 1
                and then (for all J in 1 .. N =>
                            S.E (J).Src <= N
                            and then S.Hs (J) = Kome.Frontier.Held (F, S.E (J).Src).V.H)
                and then (for all I in 1 .. N =>
                            (for all J in 1 .. N =>
                               (if I /= J then S.E (I).Src /= S.E (J).Src))),
        Post => Range_Fp (S, 1, N) = Kome.Digest.Frontier_Digest (F)
      is
      begin
         Lemma_Snapshot_Digest (F, S, N);
      end Digest;

   begin
      Clear (S);
      if N > S.Cap then
         Result := Snap_No_Space;
         return;
      end if;
      if N = 0 then
         Empty_Digest;
         pragma Assert (Linked (S, T));
         Result := Snap_OK;
         return;
      end if;

      --  The authorization records (flat indices DC + 1 .. N), into key
      --  order.
      for I in DC + 1 .. N loop
         pragma Loop_Invariant (Valid (S) and then S.N = I - 1 - DC);
         pragma Loop_Invariant (for all J in 1 .. S.N => Good (F, T, S, J));
         declare
            Old : constant Snapshot := S with Ghost;
            R   : constant Header := Kome.Frontier.Held (F, I);
         begin
            pragma Assert (for all J in 1 .. Old.N => Good (F, T, Old, J));
            Insert (S, Key_Of (R), T.Lens (I), I, Pos, St);
            if St /= Snap_OK then
               Clear (S);
               Result := Snap_Unsorted;
               return;
            end if;
            pragma Assert (Good (F, T, S, Pos));
            Shift (Old, S, Pos);
         end;
      end loop;

      --  The data row (flat indices 1 .. DC). It is in key order, so
      --  each insertion lands at the end.
      for I in 1 .. DC loop
         pragma Loop_Invariant (Valid (S) and then S.N = N - DC + I - 1);
         pragma Loop_Invariant (for all J in 1 .. S.N => Good (F, T, S, J));
         declare
            Old : constant Snapshot := S with Ghost;
            R   : constant Header := Kome.Frontier.Held (F, I);
         begin
            pragma Assert (for all J in 1 .. Old.N => Good (F, T, Old, J));
            Insert (S, Key_Of (R), T.Lens (I), I, Pos, St);
            if St /= Snap_OK then
               Clear (S);
               Result := Snap_Unsorted;
               return;
            end if;
            pragma Assert (Good (F, T, S, Pos));
            Shift (Old, S, Pos);
         end;
      end loop;

      pragma Assert (S.N = N);
      pragma Assert (for all J in 1 .. N => Good (F, T, S, J));
      Unpack;
      pragma Assert (Linked (S, T));
      Distinct;
      pragma Assert
        (for all J in 1 .. N =>
           S.E (J).Src <= N
           and then S.Hs (J) = Kome.Frontier.Held (F, S.E (J).Src).V.H);
      Digest;
      Result := Snap_OK;
   end Snapshot_Of;

   ----------------------------------------------------------------------
   --  Windows
   ----------------------------------------------------------------------

   ----------------------------------------------------------------------
   --  Windows
   ----------------------------------------------------------------------

   function Window (S : Snapshot; Lo, Hi : Elem_Key) return Span is
      N : constant Elem_Count := S.N;
      F : Lo_Bound := N + 1;
      L : Elem_Count;

      --  All keys from F to the end are at or above Lo.
      procedure Above_Lo with
        Ghost, Global => (Input => (S, Lo, F, N)),
        Pre  => Valid (S) and then N = Count (S) and then F <= N
                and then not Key_Lt (Key (S, F), Lo),
        Post => (for all K in F .. N => not Key_Lt (Key (S, K), Lo))
      is
      begin
         for K in F .. N loop
            if K > F then
               pragma Assert (Key_Lt (Key (S, F), Key (S, K)));
               Lemma_Key_Le_Lt_Trans (Lo, Key (S, F), Key (S, K));
               Lemma_Key_Lt_Asym (Lo, Key (S, K));
            end if;
            pragma Loop_Invariant (for all J in F .. K => not Key_Lt (Key (S, J), Lo));
         end loop;
      end Above_Lo;

      --  All keys after L are at or above Hi.
      procedure Above_Hi with
        Ghost, Global => (Input => (S, Hi, L, N)),
        Pre  => Valid (S) and then N = Count (S) and then L < N
                and then not Key_Lt (Key (S, L + 1), Hi),
        Post => (for all K in L + 1 .. N => not Key_Lt (Key (S, K), Hi))
      is
      begin
         for K in L + 1 .. N loop
            if K > L + 1 then
               pragma Assert (Key_Lt (Key (S, L + 1), Key (S, K)));
               Lemma_Key_Le_Lt_Trans (Hi, Key (S, L + 1), Key (S, K));
               Lemma_Key_Lt_Asym (Hi, Key (S, K));
            end if;
            pragma Loop_Invariant (for all J in L + 1 .. K => not Key_Lt (Key (S, J), Hi));
         end loop;
      end Above_Hi;

   begin
      for I in 1 .. N loop
         if not Key_Lt (Key (S, I), Lo) then
            F := I;
            exit;
         end if;
         pragma Loop_Invariant (F = N + 1);
         pragma Loop_Invariant (for all K in 1 .. I => Key_Lt (Key (S, K), Lo));
      end loop;
      pragma Assert (for all K in 1 .. F - 1 => Key_Lt (Key (S, K), Lo));
      if F <= N then
         Above_Lo;
      end if;
      pragma Assert (for all K in F .. N => not Key_Lt (Key (S, K), Lo));

      L := F - 1;
      for I in F .. N loop
         exit when not Key_Lt (Key (S, I), Hi);
         L := I;
         pragma Loop_Invariant (L = I);
         pragma Loop_Invariant (for all K in F .. I => Key_Lt (Key (S, K), Hi));
      end loop;
      pragma Assert (F - 1 <= L and then L <= N);
      pragma Assert (for all K in F .. L => Key_Lt (Key (S, K), Hi));
      if L < N then
         pragma Assert (not Key_Lt (Key (S, L + 1), Hi));
         Above_Hi;
      end if;
      pragma Assert (for all K in L + 1 .. N => not Key_Lt (Key (S, K), Hi));

      pragma Assert
        (for all K in 1 .. N =>
           In_Window (Key (S, K), Lo, Hi) = (K >= F and then K <= L));
      return (First => F, Last => L);
   end Window;

   procedure Lemma_Covers_Unique
     (S : Snapshot; Lo, Hi : Elem_Key;
      F1 : Lo_Bound; L1 : Elem_Count; F2 : Lo_Bound; L2 : Elem_Count)
   is
   begin
      if F1 <= L1 then
         pragma Assert (In_Window (Key (S, F1), Lo, Hi));
         pragma Assert (In_Window (Key (S, L1), Lo, Hi));
         pragma Assert (F2 <= F1 and then L1 <= L2);
         pragma Assert (In_Window (Key (S, F2), Lo, Hi));
         pragma Assert (In_Window (Key (S, L2), Lo, Hi));
         pragma Assert (F1 = F2 and then L1 = L2);
      elsif F2 <= L2 then
         pragma Assert (In_Window (Key (S, F2), Lo, Hi));
         pragma Assert (False);
      end if;
   end Lemma_Covers_Unique;

   procedure Lemma_My_Count
     (S : Snapshot; Lo, Hi : Elem_Key; F : Lo_Bound; L : Elem_Count)
   is
   begin
      Lemma_Covers_Unique
        (S, Lo, Hi, Window (S, Lo, Hi).First, Window (S, Lo, Hi).Last, F, L);
   end Lemma_My_Count;

   procedure Lemma_Child
     (S : Snapshot; Lo, Hi : Elem_Key; I, J, B, E : Elem_Index)
   is
      N  : constant Elem_Count := Count (S);
      CL : constant Elem_Key := Child_Lo (S, Lo, I, B);
      CH : constant Elem_Key := Child_Hi (S, Hi, J, E);
   begin
      pragma Assert (In_Window (Key (S, I), Lo, Hi));
      pragma Assert (In_Window (Key (S, J), Lo, Hi));

      --  The bounds are in [Lo, Hi].
      if B = I then
         Lemma_Key_Lt_Irrefl (Lo);
      else
         pragma Assert (In_Window (Key (S, B), Lo, Hi));
      end if;
      pragma Assert (Key_Le (Lo, CL));
      if E = J then
         Lemma_Key_Lt_Irrefl (Hi);
      else
         pragma Assert (In_Window (Key (S, E + 1), Lo, Hi));
         Lemma_Key_Lt_Asym (Key (S, E + 1), Hi);
      end if;
      pragma Assert (Key_Le (CH, Hi));

      --  CL < CH.
      if B = I and then E /= J then
         pragma Assert (Key_Lt (Key (S, I), Key (S, E + 1)));
         Lemma_Key_Le_Lt_Trans (Lo, Key (S, I), Key (S, E + 1));
      elsif B /= I and then E /= J then
         pragma Assert (Key_Lt (Key (S, B), Key (S, E + 1)));
      elsif B /= I then
         pragma Assert (In_Window (Key (S, B), Lo, Hi));
      end if;
      pragma Assert (Key_Lt (CL, CH));

      --  The cover, element by element.
      for K in 1 .. N loop
         if K < B then
            if B = I then
               pragma Assert (not In_Window (Key (S, K), Lo, Hi));
               pragma Assert (Key_Lt (Key (S, K), Key (S, I)));
               Lemma_Key_Lt_Trans (Key (S, K), Key (S, I), Hi);
               pragma Assert (Key_Lt (Key (S, K), Lo));
            else
               pragma Assert (Key_Lt (Key (S, K), Key (S, B)));
            end if;
            pragma Assert (Key_Lt (Key (S, K), CL));
            pragma Assert (not In_Window (Key (S, K), CL, CH));
         elsif K <= E then
            if B /= I then
               if K > B then
                  pragma Assert (Key_Lt (Key (S, B), Key (S, K)));
                  Lemma_Key_Lt_Asym (Key (S, B), Key (S, K));
               else
                  Lemma_Key_Lt_Irrefl (Key (S, K));
               end if;
            else
               pragma Assert (In_Window (Key (S, K), Lo, Hi));
            end if;
            pragma Assert (Key_Le (CL, Key (S, K)));
            if E /= J then
               pragma Assert (Key_Lt (Key (S, K), Key (S, E + 1)));
            else
               pragma Assert (In_Window (Key (S, K), Lo, Hi));
            end if;
            pragma Assert (Key_Lt (Key (S, K), CH));
            pragma Assert (In_Window (Key (S, K), CL, CH));
         else
            if E = J then
               pragma Assert (not In_Window (Key (S, K), Lo, Hi));
               pragma Assert (Key_Lt (Key (S, I), Key (S, K)));
               Lemma_Key_Le_Lt_Trans (Lo, Key (S, I), Key (S, K));
               Lemma_Key_Lt_Asym (Lo, Key (S, K));
               pragma Assert (not Key_Lt (Key (S, K), Hi));
            elsif K = E + 1 then
               Lemma_Key_Lt_Irrefl (Key (S, K));
            else
               pragma Assert (Key_Lt (Key (S, E + 1), Key (S, K)));
               Lemma_Key_Lt_Asym (Key (S, E + 1), Key (S, K));
            end if;
            pragma Assert (not Key_Lt (Key (S, K), CH));
            pragma Assert (not In_Window (Key (S, K), CL, CH));
         end if;
         pragma Loop_Invariant
           (for all K2 in 1 .. K =>
              In_Window (Key (S, K2), CL, CH) = (K2 >= B and then K2 <= E));
      end loop;
      pragma Assert (Covers (S, CL, CH, B, E));
   end Lemma_Child;

   --  A non-empty cover is the window.
   procedure Lemma_Window_Of_Cover
     (S : Snapshot; Lo, Hi : Elem_Key; F : Lo_Bound; L : Elem_Count)
   with
     Ghost, Global => null,
     Pre  => Valid (S) and then Key_Lt (Lo, Hi)
             and then F <= L and then L <= Count (S)
             and then Covers (S, Lo, Hi, F, L),
     Post => Window (S, Lo, Hi).First = F and then Window (S, Lo, Hi).Last = L
   is
   begin
      Lemma_Covers_Unique
        (S, Lo, Hi, F, L, Window (S, Lo, Hi).First, Window (S, Lo, Hi).Last);
   end Lemma_Window_Of_Cover;

   ----------------------------------------------------------------------
   --  Plans and outboxes
   ----------------------------------------------------------------------

   procedure Lemma_Outbox_OK (S : Snapshot; O : Outbox; T : Positive) is null;

   procedure Lemma_All_Kind (O : Outbox; K : Out_Kind; T : Positive) is null;

   procedure Lemma_Cred_Zero (H : Hello; I : Natural) is null;

   procedure Lemma_Ceil_Zero (H : Hello; I : Natural) is null;

   procedure Lemma_Exact_Plan (S : Snapshot; O : Outbox; T : Positive) is null;

   --  Each RANGE / ELEMENTS plan that is well formed and non-empty is
   --  exact (its cover is the window).
   procedure Prove_Exact (S : Snapshot; O : Outbox) with
     Ghost, Global => null,
     Pre  => Valid (S) and then Outbox_OK (S, O)
             and then (for all T in 1 .. O.N =>
                         (if O.P (T).Kind /= P_Have then O.P (T).First <= O.P (T).Last)),
     Post => Exact_Plans (S, O)
   is
   begin
      for T in 1 .. O.N loop
         if O.P (T).Kind /= P_Have then
            pragma Assert (Plan_OK (S, O.P (T)));
            Lemma_Window_Of_Cover
              (S, O.P (T).Lo, O.P (T).Hi, O.P (T).First, O.P (T).Last);
         end if;
         pragma Loop_Invariant
           (for all T2 in 1 .. T =>
              (if O.P (T2).Kind /= P_Have then
                 Key_Lt (O.P (T2).Lo, O.P (T2).Hi)
                 and then O.P (T2).First = Window (S, O.P (T2).Lo, O.P (T2).Hi).First
                 and then O.P (T2).Last = Window (S, O.P (T2).Lo, O.P (T2).Hi).Last));
      end loop;
   end Prove_Exact;

   Empty_Plan : constant Plan := (others => <>);
   Empty_Box  : constant Outbox := (N => 0, P => [others => Empty_Plan]);

   function Num_Ranges (O : Outbox) return Out_Count is
      C : Out_Count := 0;
   begin
      for T in 1 .. O.N loop
         if O.P (T).Kind = P_Range then
            C := C + 1;
         end if;
         pragma Loop_Invariant (C = Ranges_Upto (O, T));
         pragma Loop_Invariant (C <= T);
         pragma Loop_Invariant
           (if (for all T2 in 1 .. O.N => O.P (T2).Kind = P_Range) then C = T);
         pragma Loop_Invariant
           (if (for all T2 in 1 .. O.N => O.P (T2).Kind /= P_Range) then C = 0);
      end loop;
      return C;
   end Num_Ranges;

   function Obligations (O : Outbox) return Out_Count is
      C : Out_Count := 0;
   begin
      for T in 1 .. O.N loop
         if O.P (T).Kind /= P_Have then
            C := C + 1;
         end if;
         pragma Loop_Invariant (C = Obligations_Upto (O, T));
         pragma Loop_Invariant (C <= T);
         pragma Loop_Invariant
           (if (for all T2 in 1 .. O.N => O.P (T2).Kind /= P_Have) then C = T);
         pragma Loop_Invariant
           (if (for all T2 in 1 .. O.N => O.P (T2).Kind = P_Have) then C = 0);
      end loop;
      return C;
   end Obligations;

   --  Obligations_Upto grows with T, by one for each obligation.
   procedure Lemma_Obligations_Upto_Mono (O : Outbox; T : Out_Count) with
     Ghost, Global => null,
     Pre  => T <= O.N,
     Post => Obligations_Upto (O, T) <= Obligations_Upto (O, O.N)
             and then (if T >= 1 and then O.P (T).Kind /= P_Have
                       then Obligations_Upto (O, T) = Obligations_Upto (O, T - 1) + 1)
             and then (if T >= 1 and then O.P (T).Kind = P_Have
                       then Obligations_Upto (O, T) = Obligations_Upto (O, T - 1))
   is
   begin
      for T2 in T .. O.N loop
         pragma Loop_Invariant (Obligations_Upto (O, T) <= Obligations_Upto (O, T2));
      end loop;
   end Lemma_Obligations_Upto_Mono;

   function Item_Bytes (S : Snapshot; O : Outbox) return Byte_Total is
      Sum : Byte_Total := 0;
   begin
      for T in 1 .. O.N loop
         pragma Assert (Plan_OK (S, O.P (T)));
         if O.P (T).Kind /= P_Range then
            Sum := Sum + Byte_Total (Plan_Len (S, O.P (T)) - Elems_Fixed);
         end if;
         pragma Loop_Invariant (Sum = Items_Upto (S, O, T));
         pragma Loop_Invariant (Sum <= Byte_Total (T) * Max_Message_Len);
         pragma Loop_Invariant
           (if (for all T2 in 1 .. O.N => O.P (T2).Kind = P_Range) then Sum = 0);
      end loop;
      return Sum;
   end Item_Bytes;

   --  Split [Lo, Hi) into min (Split_Fanout, n) children of n / 16 or
   --  n / 16 + 1 elements (for n >= Big_Window, the cuts are Cut_At). [Lo, Hi) holds our elements I .. J (more than
   --  Ship_Threshold of them). Each child is [Child_Lo, Child_Hi) over a
   --  run B .. E. The runs partition I .. J, so the children tile
   --  [Lo, Hi). The first run stops before J, and each later run starts
   --  after I. So each child holds strictly fewer of our elements than
   --  the parent. (The last child takes the remaining elements. With these
   --  sizes, this is exactly its share. The balance is tested, not proved:
   procedure Split
     (S : Snapshot; Lo, Hi : Elem_Key; I, J : Elem_Index; O : out Outbox)
   with
     Global => null,
     Pre  => Valid (S) and then Key_Lt (Lo, Hi)
             and then I <= J and then J <= Count (S)
             and then Covers (S, Lo, Hi, I, J)
             and then J + 1 - I > Ship_Threshold,
     Post => Outbox_OK (S, O)
       and then Tiles (O, Lo, Hi)
       and then All_Kind (O, P_Range)
       and then (for all T in 1 .. O.N =>
                   O.P (T).Kind = P_Range
                   and then Key_Le (Lo, O.P (T).Lo)
                   and then Key_Le (O.P (T).Hi, Hi)
                   and then O.P (T).First >= I
                   and then O.P (T).First <= O.P (T).Last
                   and then O.P (T).Last <= J
                   and then O.P (T).Last + 1 - O.P (T).First < J + 1 - I)
   is
      N    : constant Positive := J + 1 - I;
      Base : constant Natural := N / Split_Fanout;
      Rest : constant Natural := N mod Split_Fanout;
      B    : Elem_Index := I;
      E    : Elem_Index;
      Sz   : Positive;
   begin
      pragma Assert (Base + 1 < N);
      O := Empty_Box;
      for T in 1 .. Split_Fanout loop
         pragma Loop_Invariant (O.N = T - 1);
         pragma Loop_Invariant (I <= B and then B <= J);
         pragma Loop_Invariant (if T > 1 then B > I else B = I);
         pragma Loop_Invariant
           (for all T2 in 1 .. T - 1 =>
              Plan_OK (S, O.P (T2))
              and then O.P (T2).Kind = P_Range
              and then Key_Le (Lo, O.P (T2).Lo)
              and then Key_Le (O.P (T2).Hi, Hi)
              and then O.P (T2).First >= I
              and then O.P (T2).First <= O.P (T2).Last
              and then O.P (T2).Last <= J
              and then O.P (T2).Last + 1 - O.P (T2).First < N);
         pragma Loop_Invariant
           (if T > 1 then O.P (1).Lo = Lo and then O.P (T - 1).Hi = Key (S, B));
         pragma Loop_Invariant
           (for all T2 in 2 .. T - 1 => O.P (T2 - 1).Hi = O.P (T2).Lo);
         Sz := Natural'Max (1, Base + (if T <= Rest then 1 else 0));
         pragma Assert (Sz < N);
         if T = Split_Fanout or else J - B < Sz then
            E := J;
         else
            E := B + Sz - 1;
         end if;
         --  S20: the interior cuts of a large window on multiples of 64.
         if N >= Big_Window and then T < Split_Fanout
           and then Cut_At (I, N, T) >= B and then Cut_At (I, N, T) < J
         then
            E := Cut_At (I, N, T);
         end if;
         pragma Assert (B <= E and then E <= J);
         pragma Assert (E + 1 - B < N);
         Lemma_Child (S, Lo, Hi, I, J, B, E);
         O.P (T) := (Kind  => P_Range,
                     Lo    => Child_Lo (S, Lo, I, B),
                     Hi    => Child_Hi (S, Hi, J, E),
                     First => B,
                     Last  => E,
                     N     => 0,
                     Items => [others => 1]);
         O.N := T;
         pragma Assert (Plan_OK (S, O.P (T)));
         pragma Assert (if T > 1 then O.P (T - 1).Hi = O.P (T).Lo);
         exit when E = J;
         B := E + 1;
         pragma Assert (O.P (T).Hi = Key (S, B));
      end loop;
      pragma Assert (All_Kind (O, P_Range));
   end Split;

   --  Ship our elements I .. J (the window of [Lo, Hi), at most
   --  Ship_Threshold) as ELEMENTS. If they fit, use one message. If not,
   --  use one message for each element, over a sub-range that holds only
   --  that element (each fits: Frame_Ship_Max). Every plan is exact.
   procedure Ship
     (S : Snapshot; Lo, Hi : Elem_Key; I : Lo_Bound; J : Elem_Count; O : out Outbox)
   with
     Global => null,
     Pre  => Valid (S) and then Key_Lt (Lo, Hi)
             and then I <= J + 1 and then J <= Count (S)
             and then I = Window (S, Lo, Hi).First
             and then J = Window (S, Lo, Hi).Last
             and then J + 1 - I <= Ship_Threshold,
     Post => Outbox_OK (S, O)
       and then O.N >= 1
       and then Tiles (O, Lo, Hi)
       and then All_Kind (O, P_Elements)
       and then Exact_Plans (S, O)
   is
   begin
      O := Empty_Box;
      if Elems_Fixed + Run_Size (S, I, J) <= Max_Message_Len then
         O.N := 1;
         O.P (1) := (Kind  => P_Elements,
                     Lo    => Lo,
                     Hi    => Hi,
                     First => I,
                     Last  => J,
                     N     => 0,
                     Items => [others => 1]);
         pragma Assert (Plan_OK (S, O.P (1)));
         pragma Assert (Exact_Plans (S, O));
      else
         pragma Assert (I <= J);
         for K in I .. J loop
            pragma Loop_Invariant (O.N = K - I);
            pragma Loop_Invariant
              (for all T2 in 1 .. O.N =>
                 Plan_OK (S, O.P (T2)) and then O.P (T2).Kind = P_Elements
                 and then O.P (T2).First <= O.P (T2).Last);
            pragma Loop_Invariant
              (if K > I then O.P (1).Lo = Lo and then O.P (K - I).Hi = Key (S, K));
            pragma Loop_Invariant
              (for all T2 in 2 .. O.N => O.P (T2 - 1).Hi = O.P (T2).Lo);
            Lemma_Child (S, Lo, Hi, I, J, K, K);
            pragma Assert (Run_Size (S, K, K) = Item_Size (S, K));
            O.P (K - I + 1) := (Kind  => P_Elements,
                                Lo    => Child_Lo (S, Lo, I, K),
                                Hi    => Child_Hi (S, Hi, J, K),
                                First => K,
                                Last  => K,
                                N     => 0,
                                Items => [others => 1]);
            O.N := K - I + 1;
            pragma Assert (Plan_OK (S, O.P (O.N)));
         end loop;
         Prove_Exact (S, O);
      end if;
      pragma Assert (All_Kind (O, P_Elements));
   end Ship;

   --  Send back as HAVE our elements I .. J (at most Ship_Threshold) that
   --  M does not list. If they fit, use one message (an empty HAVE if
   --  there are none). If not, use one message for each element. Send
   --  Send back as HAVE our elements I .. J (at most Ship_Threshold) that
   --  M does not list. If they fit, use one message over [M.Lo, M.Hi) (an
   --  empty HAVE if there are none). If not, use one message for each
   --  element, over sub-ranges that tile [M.Lo, M.Hi) (S19): message T
   --  runs from the key of its element (M.Lo for the first) to the key of
   --  the next one (M.Hi for the last). Send exactly those elements
   --  (Have_Exact).
   procedure Have_Back
     (S : Snapshot; M : Message; I : Lo_Bound; J : Elem_Count; O : out Outbox)
   with
     Global => null,
     Pre  => Valid (S) and then Msg_OK (M)
             and then I <= J + 1 and then J <= Count (S)
             and then Covers (S, M.Lo, M.Hi, I, J)
             and then J + 1 - I <= Ship_Threshold,
     Post => Outbox_OK (S, O)
       and then O.N >= 1
       and then Have_Exact (S, M, O)
   is
      L   : Index_List := [others => 1];
      C   : Item_Count := 0;
      --  Pos (K - I + 1): the position of our element K in L, if L has
      --  it.
      Pos : Index_List := [others => 1] with Ghost;
   begin
      O := Empty_Box;
      for K in I .. J loop
         pragma Loop_Invariant (C <= K - I);
         pragma Loop_Invariant (for all T in 1 .. C => L (T) >= I and then L (T) < K);
         pragma Loop_Invariant (for all T in 2 .. C => L (T - 1) < L (T));
         pragma Loop_Invariant (for all T in 1 .. C => not In_Msg (M, Key (S, L (T))));
         pragma Loop_Invariant
           (for all K2 in I .. K - 1 =>
              In_Msg (M, Key (S, K2))
              or else (Pos (K2 - I + 1) <= C and then L (Pos (K2 - I + 1)) = K2));
         if not In_Msg (M, Key (S, K)) then
            C := C + 1;
            L (C) := K;
            Pos (K - I + 1) := C;
         end if;
      end loop;
      pragma Assert (for all T in 1 .. C => L (T) >= I and then L (T) <= J);
      pragma Assert (for all T in 1 .. C => In_Window (Key (S, L (T)), M.Lo, M.Hi));
      pragma Assert
        (for all K2 in I .. J =>
           In_Msg (M, Key (S, K2))
           or else (Pos (K2 - I + 1) <= C and then L (Pos (K2 - I + 1)) = K2));
      --  Outside I .. J, none of our elements is in the range.
      pragma Assert
        (for all K in 1 .. Count (S) =>
           (if In_Window (Key (S, K), M.Lo, M.Hi) then K >= I and then K <= J));

      if Elems_Fixed + List_Size (S, L, C) <= Max_Message_Len then
         O.N := 1;
         O.P (1) := (Kind  => P_Have,
                     Lo    => M.Lo,
                     Hi    => M.Hi,
                     First => 1,
                     Last  => 0,
                     N     => C,
                     Items => L);
         pragma Assert (Plan_OK (S, O.P (1)));
         for K in 1 .. Count (S) loop
            if In_Window (Key (S, K), M.Lo, M.Hi) and then not In_Msg (M, Key (S, K)) then
               pragma Assert (K >= I and then K <= J);
               pragma Assert (Pos (K - I + 1) <= C);
               pragma Assert (O.P (1).Items (Pos (K - I + 1)) = K);
               pragma Assert (Offered (O, K));
            end if;
            pragma Loop_Invariant
              (for all K2 in 1 .. K =>
                 (if In_Window (Key (S, K2), M.Lo, M.Hi)
                    and then not In_Msg (M, Key (S, K2))
                  then Offered (O, K2)));
         end loop;
         pragma Assert (Tiles (O, M.Lo, M.Hi));
         pragma Assert (Have_Exact (S, M, O));
      else
         pragma Assert (C >= 1);
         for T in 1 .. C loop
            pragma Loop_Invariant (O.N = T - 1);
            pragma Loop_Invariant
              (for all T2 in 1 .. O.N =>
                 Plan_OK (S, O.P (T2)) and then O.P (T2).Kind = P_Have
                 and then O.P (T2).N = 1 and then O.P (T2).Items (1) = L (T2)
                 and then O.P (T2).Items (1) <= Count (S)
                 and then not In_Msg (M, Key (S, O.P (T2).Items (1))));
            pragma Loop_Invariant (if T > 1 then O.P (1).Lo = M.Lo);
            pragma Loop_Invariant (if T > 1 then O.P (T - 1).Hi = Key (S, L (T)));
            pragma Loop_Invariant
              (for all T2 in 2 .. O.N => O.P (T2 - 1).Hi = O.P (T2).Lo);
            declare
               X    : constant Elem_Index := L (T);
               Lo_T : constant Elem_Key := (if T = 1 then M.Lo else Key (S, X));
               Hi_T : constant Elem_Key := (if T = C then M.Hi else Key (S, L (T + 1)));
            begin
               pragma Assert (In_Window (Key (S, X), M.Lo, M.Hi));
               if T > 1 then
                  Lemma_Key_Lt_Irrefl (Key (S, X));
               end if;
               pragma Assert (Key_Le (Lo_T, Key (S, X)));
               if T < C then
                  pragma Assert (X < L (T + 1));
                  pragma Assert (Key_Lt (Key (S, X), Key (S, L (T + 1))));
               end if;
               pragma Assert (Key_Lt (Key (S, X), Hi_T));
               Lemma_Key_Le_Lt_Trans (Lo_T, Key (S, X), Hi_T);
               O.P (T) := (Kind  => P_Have,
                           Lo    => Lo_T,
                           Hi    => Hi_T,
                           First => 1,
                           Last  => 0,
                           N     => 1,
                           Items => [others => X]);
               O.N := T;
               pragma Assert (List_Size (S, O.P (T).Items, 1) = Item_Size (S, X));
               pragma Assert (In_Window (Key (S, O.P (T).Items (1)), Lo_T, Hi_T));
               pragma Assert (Plan_OK (S, O.P (T)));
               pragma Assert (not In_Msg (M, Key (S, L (T))));
               pragma Assert (not In_Msg (M, Key (S, O.P (T).Items (1))));
            end;
         end loop;
         pragma Assert
           (for all T2 in 1 .. O.N =>
              (for all U in 1 .. O.P (T2).N =>
                 U = 1 and then O.P (T2).Items (U) <= Count (S)
                 and then not In_Msg (M, Key (S, O.P (T2).Items (U)))));
         pragma Assert (O.N = C);
         pragma Assert (O.P (O.N).Hi = M.Hi);
         pragma Assert (Tiles (O, M.Lo, M.Hi));
         for K in 1 .. Count (S) loop
            if In_Window (Key (S, K), M.Lo, M.Hi) and then not In_Msg (M, Key (S, K)) then
               pragma Assert (K >= I and then K <= J);
               pragma Assert (Pos (K - I + 1) <= C);
               pragma Assert (O.P (Pos (K - I + 1)).Items (1) = K);
               pragma Assert (Offered (O, K));
            end if;
            pragma Loop_Invariant
              (for all K2 in 1 .. K =>
                 (if In_Window (Key (S, K2), M.Lo, M.Hi)
                    and then not In_Msg (M, Key (S, K2))
                  then Offered (O, K2)));
         end loop;
         pragma Assert (Have_Exact (S, M, O));
      end if;
   end Have_Back;

   procedure Deliver
     (S : Snapshot; M : Message; I : Lo_Bound; J : Elem_Count; D : out Delivery)
   with
     Global => null,
     Pre  => Valid (S) and then Msg_OK (M)
             and then I <= J + 1 and then J <= Count (S)
             and then Covers (S, M.Lo, M.Hi, I, J),
     Post => Delivers (S, M, D)
   is
      Found : Boolean;
   begin
      D := No_Delivery;
      for T in 1 .. M.N loop
         pragma Loop_Invariant
           (for all T2 in 1 .. T - 1 => D (T2) = not Held (S, M.Items (T2).Key));
         pragma Loop_Invariant (for all T2 in T .. Ship_Threshold => not D (T2));
         Found := False;
         for K in I .. J loop
            if Key (S, K) = M.Items (T).Key then
               pragma Assert (Held (S, M.Items (T).Key));
               Found := True;
               exit;
            end if;
            pragma Loop_Invariant (not Found);
            pragma Loop_Invariant
              (for all K2 in I .. K => Key (S, K2) /= M.Items (T).Key);
         end loop;
         if not Found then
            pragma Assert (for all K in I .. J => Key (S, K) /= M.Items (T).Key);
            pragma Assert (In_Window (M.Items (T).Key, M.Lo, M.Hi));
            pragma Assert
              (for all K in 1 .. Count (S) =>
                 (if K < I or else K > J then
                    not In_Window (Key (S, K), M.Lo, M.Hi)));
            pragma Assert
              (for all K in 1 .. Count (S) => Key (S, K) /= M.Items (T).Key);
            pragma Assert (not Held (S, M.Items (T).Key));
            D (T) := True;
         end if;
      end loop;
      pragma Assert (Delivers (S, M, D));
   end Deliver;

   --  The reply, given FPK = the fingerprint of our window of M as a key
   --  (Reply_Core). The comparison with M.Fp goes through To_Key256, so
   --  that the confirm decision is the same for a fingerprint computed
   --  from the prefix sums (Fingerprint_Of) and for Range_Fp
   --  (Lemma_Key_Eq_Is_Bytewise of Kome.Keys).
   procedure Respond_Core
     (S       : Snapshot;
      M       : Message;
      FPK     : Key256;
      Out_Box : out Outbox;
      Got     : out Delivery)
   with
     Global => null,
     Pre    => Valid (S) and then Msg_OK (M)
               and then FPK = Kome.Keys.To_Key256
                                (Range_Fp (S, Window (S, M.Lo, M.Hi).First,
                                              Window (S, M.Lo, M.Hi).Last)),
     Post   => Outbox_OK (S, Out_Box)
       and then Delivers (S, M, Got)
       and then Answers (S, M, Out_Box)
       and then Shrinks (S, M, Out_Box);

   procedure Respond_Core
     (S       : Snapshot;
      M       : Message;
      FPK     : Key256;
      Out_Box : out Outbox;
      Got     : out Delivery)
   is
      W : constant Span := Window (S, M.Lo, M.Hi);
      I : constant Lo_Bound := W.First;
      J : constant Elem_Count := W.Last;
      N : constant Elem_Count := J + 1 - I;

      --  The measure of each child, from its cover.
      procedure Measure with
        Ghost, Global => (Input => (S, Out_Box), Proof_In => (M, N)),
        Pre  => Valid (S) and then Msg_OK (M)
                and then N = My_Count (S, M.Lo, M.Hi)
                and then (for all T in 1 .. Out_Box.N =>
                            Plan_OK (S, Out_Box.P (T))
                            and then Out_Box.P (T).Kind = P_Range
                            and then Key_Le (M.Lo, Out_Box.P (T).Lo)
                            and then Key_Le (Out_Box.P (T).Hi, M.Hi)
                            and then Out_Box.P (T).Last + 1 - Out_Box.P (T).First < N),
        Post => Shrinks (S, M, Out_Box)
      is
      begin
         for T in 1 .. Out_Box.N loop
            Lemma_My_Count (S, Out_Box.P (T).Lo, Out_Box.P (T).Hi,
                            Out_Box.P (T).First, Out_Box.P (T).Last);
            pragma Loop_Invariant
              (for all T2 in 1 .. T =>
                 Key_Lt (Out_Box.P (T2).Lo, Out_Box.P (T2).Hi)
                 and then My_Count (S, Out_Box.P (T2).Lo, Out_Box.P (T2).Hi)
                          < My_Count (S, M.Lo, M.Hi));
         end loop;
      end Measure;

      --  O has no RANGE, so Shrinks holds vacuously.
      procedure No_Ranges with
        Ghost, Global => (Proof_In => (S, Out_Box, M)),
        Pre  => Valid (S) and then Msg_OK (M)
                and then (for all T in 1 .. Out_Box.N => Out_Box.P (T).Kind /= P_Range),
        Post => Shrinks (S, M, Out_Box)
      is
      begin
         null;
      end No_Ranges;

   begin
      Out_Box := Empty_Box;
      Got := No_Delivery;
      pragma Assert (N = My_Count (S, M.Lo, M.Hi));

      case M.Kind is
         when M_Hello =>
            pragma Assert (False);

         when M_Range =>
            pragma Assert (Delivers (S, M, Got));
            Kome.Keys.Lemma_Key_Eq_Is_Bytewise (M.Fp, Range_Fp (S, I, J));
            if N = M.Count and then Kome.Keys.To_Key256 (M.Fp) = FPK then
               pragma Assert (Range_Fp (S, I, J) = M.Fp);
               pragma Assert (Confirms (S, M));
               Out_Box := Empty_Box;
               Out_Box.N := 1;
               Out_Box.P (1) := (Kind  => P_Have,
                                 Lo    => M.Lo,
                                 Hi    => M.Hi,
                                 First => 1,
                                 Last  => 0,
                                 N     => 0,
                                 Items => [others => 1]);
               pragma Assert (Plan_OK (S, Out_Box.P (1)));
               pragma Assert (Is_Confirm (Out_Box, M.Lo, M.Hi));
               No_Ranges;
            elsif N <= Ship_Threshold then
               pragma Assert (not Confirms (S, M));
               Ship (S, M.Lo, M.Hi, I, J, Out_Box);
               pragma Assert (for all T in 1 .. Out_Box.N => Out_Box.P (T).Kind = P_Elements);
               No_Ranges;
            else
               pragma Assert (not Confirms (S, M));
               Split (S, M.Lo, M.Hi, I, J, Out_Box);
               Measure;
               Prove_Exact (S, Out_Box);
            end if;

         when M_Elements =>
            Deliver (S, M, I, J, Got);
            if N <= Ship_Threshold then
               Have_Back (S, M, I, J, Out_Box);
               pragma Assert (for all T in 1 .. Out_Box.N => Out_Box.P (T).Kind = P_Have);
               No_Ranges;
            else
               Split (S, M.Lo, M.Hi, I, J, Out_Box);
               Measure;
               Prove_Exact (S, Out_Box);
            end if;

         when M_Have =>
            Deliver (S, M, I, J, Got);
      end case;
   end Respond_Core;

   function Reply_Core (S : Snapshot; M : Message; FPK : Key256) return Reply is
      R : Reply;
   begin
      Respond_Core (S, M, FPK, R.Box, R.Got);
      return R;
   end Reply_Core;

   function Reply_Of (S : Snapshot; M : Message) return Reply is
     (Reply_Core (S, M, Kome.Keys.To_Key256
                          (Range_Fp (S, Window (S, M.Lo, M.Hi).First,
                                        Window (S, M.Lo, M.Hi).Last))));

   --  The reply of Respond and Receive: the fingerprint of our window of
   --  M comes from the prefix sums, and the result is Reply_Of (S, M)
   --  (the same Reply_Core on the same key).
   procedure Fast_Reply
     (S   : Snapshot;
      P   : Prefix;
      M   : Message;
      Box : out Outbox;
      Got : out Delivery)
   with
     Global => null,
     Pre    => Valid (S) and then Sealed (S, P) and then Msg_OK (M),
     Post   => Box = Reply_Of (S, M).Box and then Got = Reply_Of (S, M).Got
               and then Outbox_OK (S, Box)
               and then Delivers (S, M, Got)
               and then Answers (S, M, Box)
               and then Shrinks (S, M, Box)
   is
      W  : constant Span := Window (S, M.Lo, M.Hi);
      FP : Hash256;
   begin
      Fingerprint_Of (S, P, W.First, W.Last, FP);
      Kome.Keys.Lemma_Key_Eq_Is_Bytewise (FP, Range_Fp (S, W.First, W.Last));
      pragma Assert (Kome.Keys.To_Key256 (FP)
                     = Kome.Keys.To_Key256 (Range_Fp (S, W.First, W.Last)));
      declare
         R : constant Reply := Reply_Core (S, M, Kome.Keys.To_Key256 (FP));
      begin
         pragma Assert (Outbox_OK (S, R.Box) and then Delivers (S, M, R.Got)
                        and then Answers (S, M, R.Box) and then Shrinks (S, M, R.Box));
         pragma Assert (R = Reply_Of (S, M));
         Box := R.Box;
         Got := R.Got;
         pragma Assert (Box = Reply_Of (S, M).Box);
         pragma Assert (Got = Reply_Of (S, M).Got);
      end;
   end Fast_Reply;

   procedure Respond
     (S       : Snapshot;
      P       : Prefix;
      M       : Message;
      Out_Box : out Outbox;
      Got     : out Delivery)
   is
   begin
      Fast_Reply (S, P, M, Out_Box, Got);
   end Respond;
   ----------------------------------------------------------------------
   --  Wire congruence: equal bytes read back as equal values.
   ----------------------------------------------------------------------

   procedure Lemma_Same_Key256 (A, B : Byte_Array; P : Natural) with
     Ghost, Global => null,
     Pre  => P >= A'First and then P <= A'Last and then A'Last - P >= 31
             and then P >= B'First and then P <= B'Last and then B'Last - P >= 31
             and then (for all Y in P .. P + 31 => A (Y) = B (Y)),
     Post => Wire_Key256 (A, P) = Wire_Key256 (B, P)
   is
   begin
      pragma Assert (Wire_U32 (A, P) = Wire_U32 (B, P));
      pragma Assert (Wire_U32 (A, P + 4) = Wire_U32 (B, P + 4));
      pragma Assert (Wire_U32 (A, P + 8) = Wire_U32 (B, P + 8));
      pragma Assert (Wire_U32 (A, P + 12) = Wire_U32 (B, P + 12));
      pragma Assert (Wire_U32 (A, P + 16) = Wire_U32 (B, P + 16));
      pragma Assert (Wire_U32 (A, P + 20) = Wire_U32 (B, P + 20));
      pragma Assert (Wire_U32 (A, P + 24) = Wire_U32 (B, P + 24));
      pragma Assert (Wire_U32 (A, P + 28) = Wire_U32 (B, P + 28));
   end Lemma_Same_Key256;

   procedure Lemma_Same_Key (A, B : Msg_Buffer; P : Natural) with
     Ghost, Global => null,
     Pre  => P <= Max_Message_Len - Key_Wire_Len
             and then (for all Y in P .. P + Key_Wire_Len - 1 => A (Y) = B (Y)),
     Post => Wire_Key (A, P) = Wire_Key (B, P)
   is
   begin
      pragma Assert (A (P) = B (P));
      pragma Assert (Wire_U32 (A, P + 1) = Wire_U32 (B, P + 1));
      pragma Assert (Wire_U32 (A, P + 5) = Wire_U32 (B, P + 5));
      pragma Assert (Wire_U32 (A, P + 9) = Wire_U32 (B, P + 9));
      pragma Assert (Wire_U32 (A, P + 13) = Wire_U32 (B, P + 13));
      pragma Assert (Wire_Id128 (A, P + 1) = Wire_Id128 (B, P + 1));
      pragma Assert (A (P + 17) = B (P + 17));
      Lemma_Same_Key256 (A, B, P + 18);
      Lemma_Same_Key256 (A, B, P + 50);
   end Lemma_Same_Key;

   ----------------------------------------------------------------------
   --  Wire helpers. Big-endian, through the word lanes of Kome.Keys. Each
   --  writer states what it wrote (as the Wire_ functions read it back)
   --  and that nothing else changed.
   ----------------------------------------------------------------------

   procedure Put_Word (Buf : in out Msg_Buffer; P : Natural; V : Word) with
     Global => null,
     Pre  => P <= Max_Message_Len - 4,
     Post => Wire_U32 (Buf, P) = V
             and then (for all X in Buf'Range =>
                         (if X < P or else X >= P + 4 then Buf (X) = Buf'Old (X)))
   is
   begin
      Buf (P)     := Kome.Keys.Byte_Of_Word (V, 0);
      Buf (P + 1) := Kome.Keys.Byte_Of_Word (V, 1);
      Buf (P + 2) := Kome.Keys.Byte_Of_Word (V, 2);
      Buf (P + 3) := Kome.Keys.Byte_Of_Word (V, 3);
      Kome.Keys.Lemma_Word_Round_Trip (V);
   end Put_Word;

   procedure Put_Id (Buf : in out Msg_Buffer; P : Natural; X : Id128) with
     Global => null,
     Pre  => P <= Max_Message_Len - 16,
     Post => Wire_Id128 (Buf, P) = X
             and then (for all Y in Buf'Range =>
                         (if Y < P or else Y >= P + 16 then Buf (Y) = Buf'Old (Y)))
   is
   begin
      Put_Word (Buf, P, X.W0);
      Put_Word (Buf, P + 4, X.W1);
      pragma Assert (Wire_U32 (Buf, P) = X.W0);
      Put_Word (Buf, P + 8, X.W2);
      pragma Assert (Wire_U32 (Buf, P) = X.W0);
      pragma Assert (Wire_U32 (Buf, P + 4) = X.W1);
      Put_Word (Buf, P + 12, X.W3);
      pragma Assert (Wire_U32 (Buf, P) = X.W0);
      pragma Assert (Wire_U32 (Buf, P + 4) = X.W1);
      pragma Assert (Wire_U32 (Buf, P + 8) = X.W2);
   end Put_Id;

   procedure Put_Key256 (Buf : in out Msg_Buffer; P : Natural; X : Key256) with
     Global => null,
     Pre  => P <= Max_Message_Len - 32,
     Post => Wire_Key256 (Buf, P) = X
             and then (for all Y in Buf'Range =>
                         (if Y < P or else Y >= P + 32 then Buf (Y) = Buf'Old (Y)))
   is
   begin
      Put_Id (Buf, P, (W0 => X.W0, W1 => X.W1, W2 => X.W2, W3 => X.W3));
      pragma Assert (Wire_U32 (Buf, P) = X.W0);
      pragma Assert (Wire_U32 (Buf, P + 4) = X.W1);
      pragma Assert (Wire_U32 (Buf, P + 8) = X.W2);
      pragma Assert (Wire_U32 (Buf, P + 12) = X.W3);
      Put_Id (Buf, P + 16, (W0 => X.W4, W1 => X.W5, W2 => X.W6, W3 => X.W7));
      pragma Assert (Wire_U32 (Buf, P) = X.W0);
      pragma Assert (Wire_U32 (Buf, P + 4) = X.W1);
      pragma Assert (Wire_U32 (Buf, P + 8) = X.W2);
      pragma Assert (Wire_U32 (Buf, P + 12) = X.W3);
      pragma Assert (Wire_U32 (Buf, P + 16) = X.W4);
      pragma Assert (Wire_U32 (Buf, P + 20) = X.W5);
      pragma Assert (Wire_U32 (Buf, P + 24) = X.W6);
      pragma Assert (Wire_U32 (Buf, P + 28) = X.W7);
   end Put_Key256;


   procedure Put_Key (Buf : in out Msg_Buffer; P : Natural; K : Elem_Key) with
     Global => null,
     Pre  => P <= Max_Message_Len - Key_Wire_Len,
     Post => Wire_Key (Buf, P) = K
             and then (for all Y in Buf'Range =>
                         (if Y < P or else Y >= P + Key_Wire_Len then Buf (Y) = Buf'Old (Y)))
   is
   begin
      Buf (P) := Byte (K.K);
      Put_Id (Buf, P + 1, K.Ent);
      pragma Assert (Buf (P) = Byte (K.K));
      Buf (P + 17) := Byte (K.Sub);
      pragma Assert (Wire_Id128 (Buf, P + 1) = K.Ent);
      Put_Key256 (Buf, P + 18, K.FH);
      pragma Assert (Buf (P) = Byte (K.K));
      pragma Assert (Buf (P + 17) = Byte (K.Sub));
      pragma Assert (Wire_Id128 (Buf, P + 1) = K.Ent);
      Put_Key256 (Buf, P + 50, K.H);
      pragma Assert (Buf (P) = Byte (K.K));
      pragma Assert (Buf (P + 17) = Byte (K.Sub));
      pragma Assert (Wire_Id128 (Buf, P + 1) = K.Ent);
      pragma Assert (Wire_Key256 (Buf, P + 18) = K.FH);
      pragma Assert (Wire_Key256 (Buf, P + 50) = K.H);
   end Put_Key;

   procedure Put_U16 (Buf : in out Msg_Buffer; P : Natural; V : Natural) with
     Global => null,
     Pre  => P <= Max_Message_Len - 2 and then V <= 65_535,
     Post => Wire_U16 (Buf, P) = V
             and then (for all Y in Buf'Range =>
                         (if Y < P or else Y >= P + 2 then Buf (Y) = Buf'Old (Y)))
   is
   begin
      pragma Assert (V = (V / 256) * 256 + V mod 256);
      Buf (P)     := Byte (V / 256);
      Buf (P + 1) := Byte (V mod 256);
      pragma Assert (Natural (Buf (P)) = V / 256);
      pragma Assert (Natural (Buf (P + 1)) = V mod 256);
   end Put_U16;

   procedure Put_U48 (Buf : in out Msg_Buffer; P : Natural; V : U48) with
     Global => null,
     Pre  => P <= Max_Message_Len - 6,
     Post => Wire_U48 (Buf, P) = V
             and then (for all Y in Buf'Range =>
                         (if Y < P or else Y >= P + 6 then Buf (Y) = Buf'Old (Y)))
   is
      Hi : constant Natural := Natural (V / 2 ** 32);
      Lo : constant Word := Word (V mod 2 ** 32);
   begin
      pragma Assert (V = U48 (Hi) * 2 ** 32 + U48 (Lo));
      Put_U16 (Buf, P, Hi);
      Put_Word (Buf, P + 2, Lo);
      pragma Assert (Wire_U16 (Buf, P) = Hi);
      pragma Assert (Wire_U32 (Buf, P + 2) = Lo);
   end Put_U48;

   --  Tag and range of an ELEMENTS / HAVE. The body (from Elems_O_N to the
   --  end) does not change.
   procedure Write_Head
     (Buf : in out Msg_Buffer; Tag : Byte; Lo, Hi : Elem_Key)
   with
     Global => null,
     Post => Buf (0) = Tag
             and then Wire_Key (Buf, O_Lo) = Lo
             and then Wire_Key (Buf, O_Hi) = Hi
             and then (for all Y in Buf'Range =>
                         (if Y >= Elems_O_N then Buf (Y) = Buf'Old (Y)))
   is
   begin
      Put_Key (Buf, O_Lo, Lo);
      declare
         Mid : constant Msg_Buffer := Buf with Ghost;
      begin
         Put_Key (Buf, O_Hi, Hi);
         pragma Assert (for all Y in O_Lo .. O_Lo + Key_Wire_Len - 1 => Buf (Y) = Mid (Y));
         Lemma_Same_Key (Buf, Mid, O_Lo);
      end;
      pragma Assert (Wire_Key (Buf, O_Lo) = Lo);
      Buf (0) := Tag;
      pragma Assert (Wire_Key (Buf, O_Lo) = Lo);
      pragma Assert (Wire_Key (Buf, O_Hi) = Hi);
   end Write_Head;

   --  One item (flen ‖ frame) of element X at Buf (P ..), its frame from T.
   procedure Put_Item
     (S   : Snapshot;
      T   : Frame_Table;
      X   : Elem_Index;
      Buf : in out Msg_Buffer;
      P   : in out Natural)
   with
     Global => null,
     Pre  => Valid (S) and then Table_Valid (T) and then Linked (S, T)
             and then X <= Count (S)
             and then P >= Elems_Fixed
             and then P <= Max_Message_Len - Item_Size (S, X),
     Post => P = P'Old + Item_Size (S, X)
             and then (for all Y in Buf'Range =>
                         (if Y < P'Old then Buf (Y) = Buf'Old (Y)))
   is
      L : constant Frame_Size := Frame_Len (S, X);
   begin
      Put_U16 (Buf, P, L);
      Buf (P + Item_Overhead .. P + Item_Overhead + L - 1) := Elem_Frame (S, T, X);
      P := P + Item_Overhead + L;
   end Put_Item;

   procedure Encode
     (S   : Snapshot;
      T   : Frame_Table;
      P   : Plan;
      Buf : out Msg_Buffer;
      Len : out Msg_Length)
   is
      Pos : Natural := Elems_Fixed;
      N   : constant Item_Count :=
        (if P.Kind = P_Elements then P.Last + 1 - P.First else P.N);
   begin
      Buf := [others => 0];
      --  First the body, then the head. The head does not change the
      --  body.
      if P.Kind = P_Elements then
         if P.Last >= P.First then
            Put_Item (S, T, P.First, Buf, Pos);
         end if;
         if P.Last >= P.First + 1 then
            Put_Item (S, T, P.First + 1, Buf, Pos);
         end if;
         if P.Last >= P.First + 2 then
            Put_Item (S, T, P.First + 2, Buf, Pos);
         end if;
         if P.Last >= P.First + 3 then
            Put_Item (S, T, P.First + 3, Buf, Pos);
         end if;
      else
         if P.N >= 1 then
            Put_Item (S, T, P.Items (1), Buf, Pos);
         end if;
         if P.N >= 2 then
            Put_Item (S, T, P.Items (2), Buf, Pos);
         end if;
         if P.N >= 3 then
            Put_Item (S, T, P.Items (3), Buf, Pos);
         end if;
         if P.N = 4 then
            Put_Item (S, T, P.Items (4), Buf, Pos);
         end if;
      end if;
      pragma Assert (Pos = Plan_Len (S, P));
      Len := Pos;
      Put_U16 (Buf, Elems_O_N, N);

      declare
         Body_Buf : constant Msg_Buffer := Buf with Ghost;
      begin
         Write_Head (Buf, (if P.Kind = P_Elements then Tag_Elements else Tag_Have),
                     P.Lo, P.Hi);
         pragma Assert (Buf (Elems_O_N) = Body_Buf (Elems_O_N));
         pragma Assert (Buf (Elems_O_N + 1) = Body_Buf (Elems_O_N + 1));
         pragma Assert (Wire_U16 (Buf, Elems_O_N) = Wire_U16 (Body_Buf, Elems_O_N));
      end;
   end Encode;

   procedure Encode_Ranges
     (S   : Snapshot;
      PS  : Prefix;
      O   : Outbox;
      Buf : out Msg_Buffer;
      Len : out Msg_Length)
   is
      K  : constant Part_Index := O.N;
      FP : Hash256;
   begin
      Buf := [others => 0];
      Buf (0) := Tag_Range;
      Buf (Range_O_K) := Byte (K);
      Put_Key (Buf, Bound_At (0), O.P (1).Lo);
      for T in 1 .. K loop
         pragma Loop_Invariant (Buf (0) = Tag_Range and then Natural (Buf (Range_O_K)) = K);
         Lemma_Outbox_OK (S, O, T);
         Put_Key (Buf, Bound_At (T), O.P (T).Hi);
         Put_U48 (Buf, Part_At (K, T), U48 (O.P (T).Last + 1 - O.P (T).First));
         Fingerprint_Of (S, PS, O.P (T).First, O.P (T).Last, FP);
         Buf (Part_At (K, T) + Count_Len .. Part_At (K, T) + Count_Len + 31) := FP;
      end loop;
      Len := Range_Msg_Len (K);
   end Encode_Ranges;

   procedure Lemma_Confirm_Accepted (S : Snapshot; P : Plan; Buf : Msg_Buffer) is
      B : constant Byte_Array := Buf (0 .. Elems_Fixed - 1);
   begin
      pragma Assert (B'First = 0 and then B'Last = Elems_Fixed - 1);
      pragma Assert (for all Y in B'Range => B (Y) = Buf (Y));
      pragma Assert (Wire_Key (B, O_Lo) = Wire_Key (Buf, O_Lo));
      pragma Assert (Wire_Key (B, O_Hi) = Wire_Key (Buf, O_Hi));
      pragma Assert (Wire_U16 (B, Elems_O_N) = Wire_U16 (Buf, Elems_O_N));
      pragma Assert (Key_Lt (P.Lo, P.Hi));
      pragma Assert (Empty_Wire_OK (B));
   end Lemma_Confirm_Accepted;

   procedure Encode_Root
     (R   : Root_Out;
      Buf : out Msg_Buffer;
      Len : out Msg_Length)
   is
   begin
      Buf := [others => 0];
      Put_U48 (Buf, Root_O_Count, U48 (R.Count));
      Buf (Root_O_Fp .. Root_O_Fp + 31) := R.Fp;
      pragma Assert (Wire_U48 (Buf, Root_O_Count) = U48 (R.Count));
      Buf (0) := Tag_Root;
      pragma Assert (Wire_U48 (Buf, Root_O_Count) = U48 (R.Count));
      pragma Assert (Buf (Root_O_Fp .. Root_O_Fp + 31) = R.Fp);
      Len := Root_Len;
      declare
         B : constant Byte_Array := Buf (0 .. Root_Len - 1);
      begin
         pragma Assert (for all Y in B'Range => B (Y) = Buf (Y));
         pragma Assert (Wire_U48 (B, Root_O_Count) = Wire_U48 (Buf, Root_O_Count));
         pragma Assert (Root_Wire_OK (B));
      end;
   end Encode_Root;

   ----------------------------------------------------------------------
   --  HELLO
   ----------------------------------------------------------------------

   procedure Encode_Hello
     (N_Auth, N_Data : Word;
      Digest         : Hash256;
      Cred           : Byte_Array;
      Ceil           : Byte_Array;
      Buf            : out Msg_Buffer;
      Len            : out Msg_Length)
   is
      L : constant Cred_Count := Cred'Length;
      K : constant Cred_Count := Ceil'Length;
   begin
      Buf := [others => 0];
      Buf (0) := Tag_Hello;
      pragma Assert (L = (L / 256) * 256 + L mod 256);
      pragma Assert (L / 256 < 256);
      Buf (Hello_O_CLen)     := Byte (L / 256);
      Buf (Hello_O_CLen + 1) := Byte (L mod 256);
      pragma Assert (Natural (Buf (Hello_O_CLen)) = L / 256);
      pragma Assert (Natural (Buf (Hello_O_CLen + 1)) = L mod 256);
      pragma Assert (Wire_U16 (Buf, Hello_O_CLen) = L);
      pragma Assert (K = (K / 256) * 256 + K mod 256);
      pragma Assert (K / 256 < 256);
      Buf (Hello_O_KLen)     := Byte (K / 256);
      Buf (Hello_O_KLen + 1) := Byte (K mod 256);
      pragma Assert (Natural (Buf (Hello_O_KLen)) = K / 256);
      pragma Assert (Natural (Buf (Hello_O_KLen + 1)) = K mod 256);
      pragma Assert (Wire_U16 (Buf, Hello_O_KLen) = K);
      pragma Assert (Wire_U16 (Buf, Hello_O_CLen) = L);
      Buf (Hello_O_Digest .. Hello_O_Digest + 31) := Digest;
      Buf (Hello_Fixed .. Hello_Fixed + L - 1) := Cred;
      pragma Assert (Buf (Hello_Fixed .. Hello_Fixed + L - 1) = Cred);
      Buf (Hello_Fixed + L .. Hello_Fixed + L + K - 1) := Ceil;
      pragma Assert (Buf (Hello_Fixed + L .. Hello_Fixed + L + K - 1) = Ceil);
      pragma Assert (Buf (Hello_Fixed .. Hello_Fixed + L - 1) = Cred);
      pragma Assert (Wire_U16 (Buf, Hello_O_CLen) = L);
      pragma Assert (Wire_U16 (Buf, Hello_O_KLen) = K);
      pragma Assert (Buf (0) = Tag_Hello);
      Put_Word (Buf, Hello_O_NAuth, N_Auth);
      Put_Word (Buf, Hello_O_NData, N_Data);
      pragma Assert (Wire_U32 (Buf, Hello_O_NAuth) = N_Auth);
      pragma Assert (Wire_U16 (Buf, Hello_O_CLen) = L);
      pragma Assert (Wire_U16 (Buf, Hello_O_KLen) = K);
      pragma Assert (Buf (Hello_O_Digest .. Hello_O_Digest + 31) = Digest);
      pragma Assert (Buf (Hello_Fixed .. Hello_Fixed + L - 1) = Cred);
      pragma Assert (Buf (Hello_Fixed + L .. Hello_Fixed + L + K - 1) = Ceil);
      Len := Hello_Fixed + L + K;
      declare
         B : constant Byte_Array := Buf (0 .. Len - 1);
      begin
         pragma Assert (for all Y in B'Range => B (Y) = Buf (Y));
         pragma Assert (B (B'First) = Tag_Hello);
         pragma Assert (Wire_U16 (B, Hello_O_CLen) = Wire_U16 (Buf, Hello_O_CLen));
         pragma Assert (Wire_U16 (B, Hello_O_KLen) = Wire_U16 (Buf, Hello_O_KLen));
         pragma Assert (Wire_U16 (B, B'First + Hello_O_CLen) = L);
         pragma Assert (Wire_U16 (B, B'First + Hello_O_KLen) = K);
         pragma Assert (B'Last - B'First = Hello_Fixed - 1 + L + K);
         pragma Assert (Hello_Wire_OK (B));
      end;
      pragma Assert (Hello_Wire_OK (Buf (0 .. Len - 1)));
   end Encode_Hello;

   procedure Decode_Hello
     (Input : Byte_Array;
      H     : out Hello;
      OK    : out Boolean)
   is
   begin
      H := Empty_Hello;
      OK := False;
      if Input'Last < Input'First or else Input'Last - Input'First < Hello_Fixed - 1 then
         return;
      end if;
      declare
         F  : constant Natural := Input'First;
         CL : constant Natural := Wire_U16 (Input, F + Hello_O_CLen);
         KL : constant Natural := Wire_U16 (Input, F + Hello_O_KLen);
      begin
         if Input (F) /= Tag_Hello
           or else CL > Cred_Max
           or else KL > Cred_Max
           or else Input'Last - F /= Hello_Fixed - 1 + CL + KL
         then
            return;
         end if;
         pragma Assert (Hello_Wire_OK (Input));
         H.N_Auth := Wire_U32 (Input, F + Hello_O_NAuth);
         H.N_Data := Wire_U32 (Input, F + Hello_O_NData);
         H.Digest := Input (F + Hello_O_Digest .. F + Hello_O_Digest + 31);
         H.Cred_Len := CL;
         if CL > 0 then
            H.Cred (0 .. CL - 1) := Input (F + Hello_Fixed .. F + (Hello_Fixed - 1) + CL);
            pragma Assert (H.Cred (0 .. CL - 1) = Cred_Of (Input));
         end if;
         pragma Assert (for all I in CL .. Cred_Max - 1 => H.Cred (I) = 0);
         H.Ceil_Len := KL;
         if KL > 0 then
            H.Ceil (0 .. KL - 1) := Input (Input'Last - (KL - 1) .. Input'Last);
            pragma Assert (H.Ceil (0 .. KL - 1) = Hello_Ceil_Of (Input));
         end if;
         pragma Assert (for all I in KL .. Cred_Max - 1 => H.Ceil (I) = 0);
         pragma Assert (for all I in CL .. Cred_Max - 1 => H.Cred (I) = 0);
         pragma Assert (if CL > 0 then H.Cred (0 .. CL - 1) = Cred_Of (Input));
         pragma Assert (Cred_Canonical (H));
         OK := True;
      end;
   end Decode_Hello;


   ----------------------------------------------------------------------
   --  RANGE part / ROOT / ELEMENTS / HAVE decode
   ----------------------------------------------------------------------

   function Item_Places (Input : Byte_Array) return Places is
      R   : Places;
      Bad : constant Places := (others => <>);
   begin
      if Input'Last < Input'First
        or else Input'Last - Input'First >= Max_Message_Len
        or else Input'Last - Input'First < Elems_Fixed - 1
      then
         return Bad;
      end if;
      declare
         Len : constant Natural := Input'Last - Input'First + 1;
         F   : constant Natural := Input'First;
         NN  : constant Natural := Wire_U16 (Input, F + Elems_O_N);
         Pos : Natural := Elems_Fixed;   --  relative to F
      begin
         if NN > Ship_Threshold then
            return Bad;
         end if;
         for T in 1 .. NN loop
            pragma Loop_Invariant (Pos >= Elems_Fixed and then Pos <= Len);
            pragma Loop_Invariant (not R.OK);
            pragma Loop_Invariant
              (for all T2 in 1 .. T - 1 =>
                 R.Off (T2) >= Input'First
                 and then R.Off (T2) <= Input'Last
                 and then Input'Last - R.Off (T2) >= R.Len (T2) - 1);
            if Len - Pos < Item_Overhead + 1 then
               return Bad;
            end if;
            declare
               FL : constant Natural := Wire_U16 (Input, F + Pos);
            begin
               if FL < 1 or else FL > Frame_Ship_Max
                 or else Len - Pos - Item_Overhead < FL
               then
                  return Bad;
               end if;
               R.Off (T) := F + Pos + Item_Overhead;
               R.Len (T) := FL;
               Pos := Pos + Item_Overhead + FL;
            end;
         end loop;
         if Pos /= Len then
            return Bad;
         end if;
         R.N := NN;
         R.OK := True;
         return R;
      end;
   end Item_Places;

   --  An ELEMENTS / HAVE that is built from checked items is well-formed,
   --  in a small context.
   procedure Lemma_Items_OK
     (K : Msg_Kind; Lo, Hi : Elem_Key; N : Item_Count; Items : In_Items)
   with
     Ghost, Global => null,
     Pre  => K in M_Elements | M_Have and then Key_Lt (Lo, Hi)
             and then (for all T in 1 .. N => In_Window (Items (T).Key, Lo, Hi))
             and then (for all T in 2 .. N => Key_Lt (Items (T - 1).Key, Items (T).Key)),
     Post => Msg_OK ((Kind => K, Root => False, Lo => Lo, Hi => Hi, Count => 0,
                      Fp => [others => 0], N => N, Items => Items));

   procedure Lemma_Items_OK
     (K : Msg_Kind; Lo, Hi : Elem_Key; N : Item_Count; Items : In_Items) is null;

   --  A 32-byte string equal byte by byte to B (O .. O + 31) is that
   --  slice (array equality across the slide, in a small context).
   procedure Lemma_Fp_Slice (B : Byte_Array; O : Natural; X : Hash256) with
     Ghost, Global => null,
     Pre  => O >= B'First and then O <= B'Last and then B'Last - O >= 31
             and then (for all I in 0 .. 31 => X (I) = B (O + I)),
     Post => X = B (O .. O + 31);

   procedure Lemma_Fp_Slice (B : Byte_Array; O : Natural; X : Hash256) is null;

   --  Range_Fields from its four fields with the k of the head spelled
   --  out (the declare expression of Range_Fields, in a small context).
   procedure Lemma_Range_Fields (B : Byte_Array; J : Positive; M : Message) with
     Ghost, Global => null,
     Pre  => Range_Head_OK (B, J)
             and then M.Lo = Wire_Key (B, B'First + Bound_At (J - 1))
             and then M.Hi = Wire_Key (B, B'First + Bound_At (J))
             and then U48 (M.Count)
                        = Wire_U48 (B, B'First + Part_At (Natural (B (B'First + Range_O_K)), J))
             and then M.Fp = B (B'First + Part_At (Natural (B (B'First + Range_O_K)), J)
                                + Count_Len
                                .. B'First + Part_At (Natural (B (B'First + Range_O_K)), J)
                                   + Count_Len + 31),
     Post => Range_Fields (B, J, M);

   procedure Lemma_Range_Fields (B : Byte_Array; J : Positive; M : Message) is
      K : constant Part_Index := Natural (B (B'First + Range_O_K));
   begin
      pragma Assert (M.Fp = B (B'First + Part_At (K, J) + Count_Len
                               .. B'First + Part_At (K, J) + Count_Len + 31));
   end Lemma_Range_Fields;

   --  Decode_Raw refuses only an input that is neither a ROOT nor a
   --  confirm for part 1 (the completeness half of Decode_Facts).
   function Refused (Input : Byte_Array; Part : Positive) return Boolean is
     (not (Root_Wire_OK (Input) and then Part = 1)
      and then not (Empty_Wire_OK (Input) and then Part = 1))
   with Ghost;

   procedure Decode_Raw
     (Input  : Byte_Array;
      Part   : Positive;
      Keys   : Key_List;
      M      : out Message;
      OK     : out Boolean)
   with
     Global => null,
     Post   => Decode_Facts (Input, Part, Keys, M, OK);

   procedure Decode_Raw
     (Input  : Byte_Array;
      Part   : Positive;
      Keys   : Key_List;
      M      : out Message;
      OK     : out Boolean)
   is
      No_Items : constant In_Items := [others => (Key => Min_Key, Off => 0, Len => 1)];
   begin
      M := (others => <>);
      OK := False;
      --  Total over every input: Decode_Raw calculates no length before it
      --  knows that the length is at most Max_Message_Len.
      if Input'Last < Input'First
        or else Input'Last - Input'First >= Max_Message_Len
      then
         pragma Assert (Refused (Input, Part));
         return;
      end if;

      declare
         F   : constant Natural := Input'First;
         Tag : constant Byte := Input (F);
      begin
         if Tag = Tag_Root then
            if Input'Last - F /= Root_Len - 1 or else Part /= 1 then
               pragma Assert (Refused (Input, Part));
               return;
            end if;
            declare
               C : constant U48 := Wire_U48 (Input, F + Root_O_Count);
            begin
               if C > Elem_Max then
                  pragma Assert (Refused (Input, Part));
                  return;
               end if;
               M := (Kind   => M_Range,
                     Root   => True,
                     Lo     => Min_Key,
                     Hi     => Max_Key,
                     Count  => Elem_Count (C),
                     Fp     => Input (F + Root_O_Fp .. F + Root_O_Fp + 31),
                     N      => 0,
                     Items  => No_Items);
               pragma Assert (Msg_OK (M));
               pragma Assert (Root_Wire_OK (Input));
               pragma Assert (Root_Fields (Input, M));
               OK := True;
            end;

         elsif Tag = Tag_Range then
            if Input'Last - F < 1 then
               pragma Assert (Refused (Input, Part));
               return;
            end if;
            declare
               KB : constant Natural := Natural (Input (F + Range_O_K));
            begin
               if KB < 1 or else KB > Split_Fanout
                 or else Input'Last - F /= Range_Msg_Len (KB) - 1
                 or else Part > KB
               then
                  pragma Assert (Refused (Input, Part));
                  return;
               end if;
               --  The whole message: strictly ascending bounds and counts
               --  within Elem_Max.
               for I in 1 .. KB loop
                  if not Key_Lt (Wire_Key (Input, F + Bound_At (I - 1)),
                                 Wire_Key (Input, F + Bound_At (I)))
                    or else Wire_U48 (Input, F + Part_At (KB, I)) > Elem_Max
                  then
                     pragma Assert (Refused (Input, Part));
                     return;
                  end if;
               end loop;
               declare
                  Lo : constant Elem_Key := Wire_Key (Input, F + Bound_At (Part - 1));
                  Hi : constant Elem_Key := Wire_Key (Input, F + Bound_At (Part));
                  C  : constant U48 := Wire_U48 (Input, F + Part_At (KB, Part));
                  KP : constant Part_Index := Natural (Input (Input'First + Range_O_K));
                  FO : constant Natural := Input'First + Part_At (KP, Part) + Count_Len;
                  FP : Hash256 := [others => 0];
               begin
                  if not Key_Lt (Lo, Hi) or else C > Elem_Max then
                     pragma Assert (Refused (Input, Part));
                     return;
                  end if;
                  --  The fingerprint of the part, byte by byte (the
                  --  slice equality then follows in a small context).
                  for I in 0 .. 31 loop
                     FP (I) := Input (FO + I);
                     pragma Loop_Invariant (for all I2 in 0 .. I => FP (I2) = Input (FO + I2));
                  end loop;
                  M := (Kind   => M_Range,
                        Root   => False,
                        Lo     => Lo,
                        Hi     => Hi,
                        Count  => Elem_Count (C),
                        Fp     => FP,
                        N      => 0,
                        Items  => No_Items);
                  pragma Assert (M.Fp = FP);
                  pragma Assert (for all I in 0 .. 31 => M.Fp (I) = Input (FO + I));
                  Lemma_Fp_Slice (Input, FO, M.Fp);
                  pragma Assert
                    (M.Fp = Input (Input'First + Part_At (KP, Part) + Count_Len
                                   .. Input'First + Part_At (KP, Part) + Count_Len + 31));
                  pragma Assert (Msg_OK (M));
                  pragma Assert (Range_Head_OK (Input, Part));
                  Lemma_Range_Fields (Input, Part, M);
                  pragma Assert (Range_Fields (Input, Part, M));
                  OK := True;
               end;
            end;

         elsif Tag = Tag_Elements or else Tag = Tag_Have then
            if Part /= 1 or else Input'Last - F < Elems_Fixed - 1 then
               pragma Assert (Refused (Input, Part));
               return;
            end if;
            declare
               Lo : constant Elem_Key := Wire_Key (Input, F + O_Lo);
               Hi : constant Elem_Key := Wire_Key (Input, F + O_Hi);
               PL : constant Places := Item_Places (Input);
               Items : In_Items := No_Items;
            begin
               if not Key_Lt (Lo, Hi) or else not PL.OK then
                  pragma Assert (Refused (Input, Part));
                  return;
               end if;
               for T in 1 .. PL.N loop
                  pragma Loop_Invariant
                    (for all T2 in 1 .. T - 1 =>
                       In_Window (Keys (T2), Lo, Hi)
                       and then Items (T2) = (Key => Keys (T2), Off => PL.Off (T2),
                                              Len => PL.Len (T2)));
                  pragma Loop_Invariant
                    (for all T2 in 2 .. T - 1 => Key_Lt (Keys (T2 - 1), Keys (T2)));
                  if not In_Window (Keys (T), Lo, Hi)
                    or else (T > 1 and then not Key_Lt (Keys (T - 1), Keys (T)))
                  then
                     pragma Assert (Refused (Input, Part));
                     return;
                  end if;
                  Items (T) := (Key => Keys (T), Off => PL.Off (T), Len => PL.Len (T));
               end loop;
               Lemma_Items_OK ((if Tag = Tag_Elements then M_Elements else M_Have),
                               Lo, Hi, PL.N, Items);
               M := (Kind   => (if Tag = Tag_Elements then M_Elements else M_Have),
                     Root   => False,
                     Lo     => Lo,
                     Hi     => Hi,
                     Count  => 0,
                     Fp     => [others => 0],
                     N      => PL.N,
                     Items  => Items);
               pragma Assert (Msg_OK (M));
               pragma Assert (Msg_In (M, Input));
               pragma Assert (Keys_Given (M, Keys));
               OK := True;
            end;
         end if;
      end;
   end Decode_Raw;

   function Decode_Of (Input : Byte_Array; Part : Positive; Keys : Key_List)
     return Decoding
   is
      D : Decoding;
   begin
      Decode_Raw (Input, Part, Keys, D.M, D.OK);
      return D;
   end Decode_Of;

   ----------------------------------------------------------------------
   --  The FIFO of open obligations: a ring of Oblig_Cap slots.
   ----------------------------------------------------------------------

   --  The slots of two different open obligations are different.
   procedure Lemma_Slots_Distinct (Sess : Session; K1, K2 : Positive) with
     Ghost, Global => null,
     Pre  => Sess.Q_Head <= Sess.Oblig_Cap
             and then K1 <= Sess.Oblig_Cap and then K2 <= Sess.Oblig_Cap
             and then K1 /= K2,
     Post => Slot (Sess, K1) /= Slot (Sess, K2);

   procedure Lemma_Slots_Distinct (Sess : Session; K1, K2 : Positive) is null;

   procedure Push (Sess : in out Session; Lo, Hi : Elem_Key) with
     Global => null,
     Pre  => Sess.Q_Head <= Sess.Oblig_Cap and then Sess.Q_Len < Sess.Oblig_Cap,
     Post => Sess = (Sess'Old with delta Q => Sess.Q, Q_Len => Sess'Old.Q_Len + 1)
             and then Open (Sess, Sess.Q_Len) = Fresh (Lo, Hi)
             and then (for all K in 1 .. Sess'Old.Q_Len => Open (Sess, K) = Open (Sess'Old, K))
   is
      Sl : constant Positive := Slot (Sess, Sess.Q_Len + 1);
   begin
      Sess.Q (Sl) := Fresh (Lo, Hi);
      Sess.Q_Len := Sess.Q_Len + 1;
      for K in 1 .. Sess.Q_Len - 1 loop
         Lemma_Slots_Distinct (Sess, K, Sess.Q_Len);
         pragma Loop_Invariant
           (for all K2 in 1 .. K => Slot (Sess, K2) /= Sl);
      end loop;
   end Push;

   procedure Pop_Head (Sess : in out Session) with
     Global => null,
     Pre  => Sess.Q_Head <= Sess.Oblig_Cap and then Sess.Q_Len >= 1
             and then Sess.Q_Len <= Sess.Oblig_Cap,
     Post => Sess = (Sess'Old with delta Q_Head => Sess.Q_Head,
                                         Q_Len => Sess'Old.Q_Len - 1)
             and then Sess.Q_Head <= Sess.Oblig_Cap
             and then (for all K in 1 .. Sess.Q_Len => Open (Sess, K) = Open (Sess'Old, K + 1))
   is
      Old : constant Session := Sess with Ghost;
   begin
      Sess.Q_Head := (if Sess.Q_Head = Sess.Oblig_Cap then 1 else Sess.Q_Head + 1);
      Sess.Q_Len := Sess.Q_Len - 1;
      pragma Assert (for all K in 1 .. Sess.Q_Len => Slot (Sess, K) = Slot (Old, K + 1));
   end Pop_Head;

   procedure Advance_Head (Sess : in out Session; M : Message) with
     Global => null,
     Pre  => Sess.Q_Head <= Sess.Oblig_Cap and then Sess.Q_Len >= 1
             and then Sess.Q_Len <= Sess.Oblig_Cap,
     Post => Sess = (Sess'Old with delta Q => Sess.Q)
             and then Open (Sess, 1) = Advanced (Open (Sess'Old, 1), M)
             and then (for all K in 2 .. Sess.Q_Len => Open (Sess, K) = Open (Sess'Old, K))
   is
      Sl : constant Positive := Slot (Sess, 1);
   begin
      Sess.Q (Sl) := Advanced (Sess.Q (Sl), M);
      for K in 2 .. Sess.Q_Len loop
         Lemma_Slots_Distinct (Sess, 1, K);
         pragma Loop_Invariant
           (for all K2 in 2 .. K => Slot (Sess, K2) /= Sl);
      end loop;
   end Advance_Head;

   --  The definition of Queue_Step, as the Post of a function with a
   --  body: a goal Queue_Step (A, B, M, O) keeps its term, so the Post of
   --  a callee that names Queue_Step of an equal session proves it by
   --  congruence, with no instantiation of the quantifiers.
   function Queue_Step_Impl (Old, Upd : Session; M : Message; O : Outbox) return Boolean
   with
     Ghost, Global => null,
     Pre  => Old.Q_Head <= Old.Oblig_Cap and then Old.Q_Len <= Old.Oblig_Cap
            and then Upd.Q_Head <= Upd.Oblig_Cap and then Upd.Q_Len <= Upd.Oblig_Cap
            and then Upd.Oblig_Cap = Old.Oblig_Cap
            and then (if not M.Root then Matches_Head (Old, M)),
     Post => Queue_Step_Impl'Result =
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

   function Queue_Step_Impl (Old, Upd : Session; M : Message; O : Outbox) return Boolean is
   begin
      return (declare
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
   end Queue_Step_Impl;

   function Queue_Step (Old, Upd : Session; M : Message; O : Outbox) return Boolean is
     (Queue_Step_Impl (Old, Upd, M, O));

   procedure Lemma_Queue_Step_Def (Old, Upd : Session; M : Message; O : Outbox) is null;

   --  Append the obligations of O (its RANGE and ELEMENTS plans, in plan
   --  order) to the FIFO.
   procedure Push_All (Sess : in out Session; O : Outbox) with
     Global => null,
     Pre  => Sess.Q_Head <= Sess.Oblig_Cap
             and then Sess.Q_Len + Obligations (O) <= Sess.Oblig_Cap,
     Post => Sess = (Sess'Old with delta Q => Sess.Q,
                                         Q_Len => Sess'Old.Q_Len + Obligations (O))
             and then (for all K in 1 .. Sess'Old.Q_Len => Open (Sess, K) = Open (Sess'Old, K))
             and then (for all T in 1 .. O.N =>
                         (if O.P (T).Kind /= P_Have then
                            Open (Sess, Sess'Old.Q_Len + Obligations_Upto (O, T))
                              = Fresh (O.P (T).Lo, O.P (T).Hi)))
   is
      Base : constant Oblig_Count := Sess.Q_Len;
      Mid  : constant Session := Sess with Ghost;
   begin
      for T in 1 .. O.N loop
         pragma Loop_Invariant (Sess.Q_Len = Base + Obligations_Upto (O, T - 1));
         pragma Loop_Invariant (Sess = (Mid with delta Q => Sess.Q, Q_Len => Sess.Q_Len));
         pragma Loop_Invariant (for all K in 1 .. Base => Open (Sess, K) = Open (Mid, K));
         pragma Loop_Invariant
           (for all T2 in 1 .. T - 1 =>
              (if O.P (T2).Kind /= P_Have then
                 Base + Obligations_Upto (O, T2) <= Sess.Q_Len
                 and then Open (Sess, Base + Obligations_Upto (O, T2))
                            = Fresh (O.P (T2).Lo, O.P (T2).Hi)));
         Lemma_Obligations_Upto_Mono (O, T);
         if O.P (T).Kind /= P_Have then
            Push (Sess, O.P (T).Lo, O.P (T).Hi);
            pragma Assert (Sess.Q_Len = Base + Obligations_Upto (O, T));
         end if;
      end loop;
      pragma Assert (Sess.Q_Len = Base + Obligations_Upto (O, O.N));
   end Push_All;

   --  The FIFO step of an accepted message M with the reply O: the head
   --  leaves (its group is done) or advances (M continues it), then the

   --  The FIFO step of an accepted message M with the reply O: the head
   --  leaves (its answer is done) or advances (M continues it), then the
   --  obligations of O are appended (Queue_Step).
   procedure Step_Queue (Sess : in out Session; M : Message; O : Outbox) with
     Global => null,
     Pre  => Sess.Q_Head <= Sess.Oblig_Cap and then Sess.Q_Len <= Sess.Oblig_Cap
             and then (if not M.Root then Matches_Head (Sess, M))
             and then Sess.Q_Len - (if Group_Done (Sess, M) then 1 else 0)
                        + Obligations (O) <= Sess.Oblig_Cap,
     Post => Sess = (Sess'Old with delta Q      => Sess.Q,
                                         Q_Head => Sess.Q_Head,
                                         Q_Len  => Sess.Q_Len)
             and then Sess.Q_Head <= Sess.Oblig_Cap and then Sess.Q_Len <= Sess.Oblig_Cap
             and then Sess.Q_Len = Sess'Old.Q_Len
                                   - (if Group_Done (Sess'Old, M) then 1 else 0)
                                   + Obligations (O)
             and then Queue_Step (Sess'Old, Sess, M, O)
   is
      Old      : constant Session := Sess with Ghost;
      Done_Grp : constant Boolean := Group_Done (Sess, M);
   begin
      if Done_Grp then
         Pop_Head (Sess);
      elsif not M.Root then
         Advance_Head (Sess, M);
      end if;
      pragma Assert (Sess.Q_Len = Old.Q_Len - (if Done_Grp then 1 else 0));
      pragma Assert
        (for all K in 1 .. Sess.Q_Len =>
           Open (Sess, K) = (if Done_Grp then Open (Old, K + 1)
                             elsif K = 1 and then not M.Root
                             then Advanced (Open (Old, 1), M)
                             else Open (Old, K)));
      declare
         Mid : constant Session := Sess with Ghost;
      begin
         Push_All (Sess, O);
         pragma Assert (Sess.Q_Len = Mid.Q_Len + Obligations (O));
         pragma Assert (for all K in 1 .. Mid.Q_Len => Open (Sess, K) = Open (Mid, K));
         pragma Assert
           (for all K in 1 .. Mid.Q_Len =>
              Open (Sess, K) = (if Done_Grp then Open (Old, K + 1)
                                elsif K = 1 and then not M.Root
                                then Advanced (Open (Old, 1), M)
                                else Open (Old, K)));
         pragma Assert
           (for all T in 1 .. O.N =>
              (if O.P (T).Kind /= P_Have
                 and then Mid.Q_Len + Obligations_Upto (O, T) in 1 .. Sess.Q_Len
               then
                 Open (Sess, Mid.Q_Len + Obligations_Upto (O, T))
                   = Fresh (O.P (T).Lo, O.P (T).Hi)));
      end;
      pragma Assert (Queue_Step (Old, Sess, M, O));
   end Step_Queue;

   --  Accept the RANGE part, ROOT, ELEMENTS or HAVE M in Auth or Data with
   --  the reply O (within the budgets): the counters, the FIFO step and
   --  the phase.
   procedure Accept_Data
     (Sess     : in out Session;
      S        : Snapshot;
      M        : Message;
      O        : Outbox)
   with
     Global => null,
     Pre  => Valid (S) and then Outbox_OK (S, O) and then Session_OK (Sess)
             and then Sess.P in Auth | Data and then Sess.Msgs < Sess.Budget
             and then Root_Or_Owed (Sess, M)
             and then Within_Budgets (Sess, S, M, O),
     Post => Session_OK (Sess) and then not Sess.Aborted
             and then Sess.Ranges = Sess'Old.Ranges + Num_Ranges (O)
             and then Sess.Ranges <= Range_Budget (S)
             and then Sess.Shipped = Sess'Old.Shipped + Item_Bytes (S, O)
             and then Sess.Shipped <= Ship_Budget (S)
             and then Sess.Q_Len =
                        Sess'Old.Q_Len
                        - (if Group_Done (Sess'Old, M) then 1 else 0)
                        + Obligations (O)
             and then Queue_Step (Sess'Old, Sess, M, O)
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
                                Auth_Root_Seen => Sess.Auth_Root_Seen)
   is
      Old : constant Session := Sess with Ghost;
   begin
      Step_Queue (Sess, M, O);
      declare
         Mid : constant Session := Sess with Ghost;
      begin
         Sess.Ranges := Sess.Ranges + Num_Ranges (O);
         Sess.Shipped := Sess.Shipped + Item_Bytes (S, O);
         Sess.Msgs := Sess.Msgs + 1;
         if M.Root then
            if Sess.Auth_Root_Seen then
               Sess.P := Data;          --  the data ROOT
            end if;
            Sess.Auth_Root_Seen := True;
         end if;
         if Sess.P = Data and then Sess.Q_Len = 0 then
            Sess.P := Done;
         end if;
         pragma Assert (Sess.Q_Len = Mid.Q_Len and then Sess.Q_Head = Mid.Q_Head);
         pragma Assert (for all K in 1 .. Sess.Q_Len => Open (Sess, K) = Open (Mid, K));
         pragma Assert (Queue_Step (Old, Sess, M, O));
      end;
   end Accept_Data;

   ----------------------------------------------------------------------
   --  Session
   ----------------------------------------------------------------------

   procedure Start
     (Sess    : out Session;
      As      : Role;
      Cid     : Hash256;
      Peer_DH : Pubkey)
   is
   begin
      Sess := (Oblig_Cap       => Sess.Oblig_Cap,
               R               => As,
               P               => Gate,
               Cid             => Cid,
               Peer_DH         => Peer_DH,
               Aborted         => False,
               Hello_Sent      => False,
               Peer_Hello_Seen => False,
               Auth_Root_Seen  => False,
               Our_N           => 0,
               Our_Digest      => (others => 0),
               Our_Auth_N      => 0,
               Our_Auth_Fp     => [others => 0],
               Peer_Auth       => 0,
               Peer_Data       => 0,
               Peer_Digest     => (others => 0),
               Msgs            => 0,
               Budget          => Pre_Gate_Budget,
               Ranges          => 0,
               Shipped         => 0,
               Q               => [others => Fresh (Min_Key, Max_Key)],
               Q_Head          => 1,
               Q_Len           => 0);
   end Start;

   --  The two HELLOs have passed. If the digests are equal, the session
   --  ends. If not, the phase is Auth, and the initiator opens the
   --  authorization ROOT.
   procedure Exchange_Done (Sess : in out Session; R : out Root_Out) with
     Global => null,
     Pre  => Sess.P = Gate and then Sess.Hello_Sent
             and then Sess.Peer_Hello_Seen and then Sess.Msgs <= Pre_Gate_Budget
             and then not Sess.Aborted and then not Sess.Auth_Root_Seen
             and then Sess.Q_Head <= Sess.Oblig_Cap and then Sess.Q_Len = 0,
     Post => After_Hellos (Sess, R) and then Session_OK (Sess)
             and then Sess.R = Sess'Old.R and then Sess.Cid = Sess'Old.Cid
             and then Sess.Peer_DH = Sess'Old.Peer_DH and then Sess.Our_N = Sess'Old.Our_N
             and then Sess.Our_Digest = Sess'Old.Our_Digest
             and then Sess.Msgs = Sess'Old.Msgs and then not Sess.Aborted
             and then Sess = (Sess'Old with delta
                                P              => Sess.P,
                                Budget         => Sess.Budget,
                                Q              => Sess.Q,
                                Q_Len          => Sess.Q_Len,
                                Auth_Root_Seen => Sess.Auth_Root_Seen)
   is
   begin
      R := No_Root;
      Sess.Budget := Msg_Budget (Sess.Our_N, Peer_Claim (Sess));
      if Sess.Our_Digest = Sess.Peer_Digest then
         Sess.P := Done;
      elsif Sess.R = Initiator then
         R := (Send => True, Count => Sess.Our_Auth_N, Fp => Sess.Our_Auth_Fp);
         Push (Sess, Min_Key, Data_Lo);
         Sess.Auth_Root_Seen := True;
         Sess.P := Auth;
      else
         Sess.P := Auth;
      end if;
   end Exchange_Done;

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
   is
      TF : constant Hash256 := Total_Fp (Auth, Data);
   begin
      Root := No_Root;
      Encode_Hello (Word (Kome.Digest.Count (Auth)), Word (Kome.Digest.Count (Data)),
                    TF, Cred, Ceil, Buf, Len);
      Sess.Hello_Sent := True;
      Sess.Our_N := Kome.Digest.Count (Auth) + Kome.Digest.Count (Data);
      Sess.Our_Digest := Kome.Keys.To_Key256 (TF);
      Sess.Our_Auth_N := Kome.Digest.Count (Auth);
      Sess.Our_Auth_Fp := Kome.Digest.Fingerprint (Auth);
      if Sess.Peer_Hello_Seen then
         Exchange_Done (Sess, Root);
      end if;
   end Admit;

   procedure Next_Phase
     (Sess     : in out Session;
      S        : Snapshot;
      P        : Prefix;
      F        : Kome.Frontier.State;
      Eff      : Kome.Records.Roster_Record;
      Root     : out Root_Out;
      Result   : out Session_Status)
   is
      W  : constant Span := Window (S, Data_Lo, Max_Key);
      FP : Hash256;
   begin
      Root := No_Root;
      if not Gate_Open (Sess.Cid, F, Eff, Sess.Peer_DH) then
         Sess.P := Done;
         Sess.Aborted := True;
         Result := S_Aborted;
         return;
      end if;
      Fingerprint_Of (S, P, W.First, W.Last, FP);
      Root := (Send => True, Count => W.Last + 1 - W.First, Fp => FP);
      Push (Sess, Data_Lo, Max_Key);
      Sess.P := Data;
      Result := S_OK;
   end Next_Phase;

   --  The parts below take every argument of the Post, and each body
   --  reads only its own.
   pragma Warnings (Off, "formal parameter * is not referenced");
   pragma Warnings (GNATprove, Off, "unused variable",
                    Reason => "each part of the Post of Receive reads only its own arguments");

   --  The Post of Receive with the entry state named Old, in seven parts.
   --  Each part is a function with a body whose meaning is its Post, so a
   --  goal that names a part keeps its term. Each exit path of
   --  Receive_Impl asserts the parts for its own path (small VCs), and the
   --  Post of Receive is one unfolding step from Receive_Post.
   --  Receive's Post: the session invariant, the unchanged fields and the outbox.
   function Recv_Fields
     (Old, Sess : Session;
      S         : Snapshot;
      F         : Kome.Frontier.State;
      Eff       : Kome.Records.Roster_Record;
      Input     : Byte_Array;
      Part      : Positive;
      Keys      : Key_List;
      M         : Message;
      Peer      : Hello;
      Out_Box   : Outbox;
      Got       : Delivery;
      Root      : Root_Out;
      Result    : Session_Status) return Boolean
   with
     Ghost, Global => null,
     Pre  => Valid (S) and then Session_OK (Old) and then Sess.Oblig_Cap = Old.Oblig_Cap,
     Post => Recv_Fields'Result =
       (Session_OK (Sess)
       and then Sess.R = Old.R and then Sess.Cid = Old.Cid
       and then Sess.Peer_DH = Old.Peer_DH
       and then Sess.Our_N = Old.Our_N
       and then Sess.Our_Digest = Old.Our_Digest
       and then Outbox_OK (S, Out_Box));

   function Recv_Fields
     (Old, Sess : Session;
      S         : Snapshot;
      F         : Kome.Frontier.State;
      Eff       : Kome.Records.Roster_Record;
      Input     : Byte_Array;
      Part      : Positive;
      Keys      : Key_List;
      M         : Message;
      Peer      : Hello;
      Out_Box   : Outbox;
      Got       : Delivery;
      Root      : Root_Out;
      Result    : Session_Status) return Boolean
   is
   begin
      return
       (Session_OK (Sess)
       and then Sess.R = Old.R and then Sess.Cid = Old.Cid
       and then Sess.Peer_DH = Old.Peer_DH
       and then Sess.Our_N = Old.Our_N
       and then Sess.Our_Digest = Old.Our_Digest
       and then Outbox_OK (S, Out_Box));
   end Recv_Fields;

   --  Receive's Post: the status is Status_Of.
   function Recv_Status
     (Old, Sess : Session;
      S         : Snapshot;
      F         : Kome.Frontier.State;
      Eff       : Kome.Records.Roster_Record;
      Input     : Byte_Array;
      Part      : Positive;
      Keys      : Key_List;
      M         : Message;
      Peer      : Hello;
      Out_Box   : Outbox;
      Got       : Delivery;
      Root      : Root_Out;
      Result    : Session_Status) return Boolean
   with
     Ghost, Global => null,
     Pre  => Valid (S) and then Session_OK (Old) and then Sess.Oblig_Cap = Old.Oblig_Cap and then Session_OK (Sess)
             and then Outbox_OK (S, Out_Box),
     Post => Recv_Status'Result =
       (Result = Status_Of (Old, S, F, Eff, Input, Part, Keys));

   function Recv_Status
     (Old, Sess : Session;
      S         : Snapshot;
      F         : Kome.Frontier.State;
      Eff       : Kome.Records.Roster_Record;
      Input     : Byte_Array;
      Part      : Positive;
      Keys      : Key_List;
      M         : Message;
      Peer      : Hello;
      Out_Box   : Outbox;
      Got       : Delivery;
      Root      : Root_Out;
      Result    : Session_Status) return Boolean
   is
   begin
      return
       (Result = Status_Of (Old, S, F, Eff, Input, Part, Keys));
   end Recv_Status;

   --  Receive's Post: refusals change nothing; Done; the counter; elements only in Auth and Data.
   function Recv_Kinds
     (Old, Sess : Session;
      S         : Snapshot;
      F         : Kome.Frontier.State;
      Eff       : Kome.Records.Roster_Record;
      Input     : Byte_Array;
      Part      : Positive;
      Keys      : Key_List;
      M         : Message;
      Peer      : Hello;
      Out_Box   : Outbox;
      Got       : Delivery;
      Root      : Root_Out;
      Result    : Session_Status) return Boolean
   with
     Ghost, Global => null,
     Pre  => Valid (S) and then Session_OK (Old) and then Sess.Oblig_Cap = Old.Oblig_Cap and then Session_OK (Sess)
             and then Outbox_OK (S, Out_Box),
     Post => Recv_Kinds'Result =
       ((if Result in S_Malformed | S_Unexpected | S_Limit then
                   Sess = Old and then Out_Box.N = 0 and then Got = No_Delivery
                   and then not Root.Send)
       and then (if Old.P = Done then Result = S_Unexpected)
       and then (if Result = S_OK then
                   Sess.Msgs = Old.Msgs + 1 and then not Sess.Aborted)
       and then (if Result = S_OK and then M.Kind in M_Range | M_Elements | M_Have
                 then Old.P in Auth | Data));

   function Recv_Kinds
     (Old, Sess : Session;
      S         : Snapshot;
      F         : Kome.Frontier.State;
      Eff       : Kome.Records.Roster_Record;
      Input     : Byte_Array;
      Part      : Positive;
      Keys      : Key_List;
      M         : Message;
      Peer      : Hello;
      Out_Box   : Outbox;
      Got       : Delivery;
      Root      : Root_Out;
      Result    : Session_Status) return Boolean
   is
   begin
      return
       ((if Result in S_Malformed | S_Unexpected | S_Limit then
                   Sess = Old and then Out_Box.N = 0 and then Got = No_Delivery
                   and then not Root.Send)
       and then (if Old.P = Done then Result = S_Unexpected)
       and then (if Result = S_OK then
                   Sess.Msgs = Old.Msgs + 1 and then not Sess.Aborted)
       and then (if Result = S_OK and then M.Kind in M_Range | M_Elements | M_Have
                 then Old.P in Auth | Data));
   end Recv_Kinds;

   --  Receive's Post: an inadmissible HELLO credential aborts.
   function Recv_Hello_Abort
     (Old, Sess : Session;
      S         : Snapshot;
      F         : Kome.Frontier.State;
      Eff       : Kome.Records.Roster_Record;
      Input     : Byte_Array;
      Part      : Positive;
      Keys      : Key_List;
      M         : Message;
      Peer      : Hello;
      Out_Box   : Outbox;
      Got       : Delivery;
      Root      : Root_Out;
      Result    : Session_Status) return Boolean
   with
     Ghost, Global => null,
     Pre  => Valid (S) and then Session_OK (Old) and then Sess.Oblig_Cap = Old.Oblig_Cap and then Session_OK (Sess)
             and then Outbox_OK (S, Out_Box),
     Post => Recv_Hello_Abort'Result =
       ((if Result = S_Aborted and then Old.P = Gate then
                   M.Kind = M_Hello and then not Old.Peer_Hello_Seen
                   and then Hello_Wire_OK (Input)
                   and then not Cred_Admissible (F, Old.Peer_DH, Cred_Of (Input))
                   and then Peer = Empty_Hello
                   and then Sess = (Old with delta P => Done, Aborted => True)
                   and then Out_Box.N = 0 and then Got = No_Delivery
                   and then not Root.Send));

   function Recv_Hello_Abort
     (Old, Sess : Session;
      S         : Snapshot;
      F         : Kome.Frontier.State;
      Eff       : Kome.Records.Roster_Record;
      Input     : Byte_Array;
      Part      : Positive;
      Keys      : Key_List;
      M         : Message;
      Peer      : Hello;
      Out_Box   : Outbox;
      Got       : Delivery;
      Root      : Root_Out;
      Result    : Session_Status) return Boolean
   is
   begin
      return
       ((if Result = S_Aborted and then Old.P = Gate then
                   M.Kind = M_Hello and then not Old.Peer_Hello_Seen
                   and then Hello_Wire_OK (Input)
                   and then not Cred_Admissible (F, Old.Peer_DH, Cred_Of (Input))
                   and then Peer = Empty_Hello
                   and then Sess = (Old with delta P => Done, Aborted => True)
                   and then Out_Box.N = 0 and then Got = No_Delivery
                   and then not Root.Send));
   end Recv_Hello_Abort;

   --  Receive's Post: an accepted HELLO.
   function Recv_Hello_OK
     (Old, Sess : Session;
      S         : Snapshot;
      F         : Kome.Frontier.State;
      Eff       : Kome.Records.Roster_Record;
      Input     : Byte_Array;
      Part      : Positive;
      Keys      : Key_List;
      M         : Message;
      Peer      : Hello;
      Out_Box   : Outbox;
      Got       : Delivery;
      Root      : Root_Out;
      Result    : Session_Status) return Boolean
   with
     Ghost, Global => null,
     Pre  => Valid (S) and then Session_OK (Old) and then Sess.Oblig_Cap = Old.Oblig_Cap and then Session_OK (Sess)
             and then Outbox_OK (S, Out_Box),
     Post => Recv_Hello_OK'Result =
       ((if Result = S_OK and then Old.P = Gate then
                   M.Kind = M_Hello and then not Old.Peer_Hello_Seen
                   and then Hello_Wire_OK (Input) and then Hello_Decoded (Input, Peer)
                   and then Cred_Admissible (F, Old.Peer_DH, Cred_Of (Input))
                   and then Sess = (Old with delta
                                      Peer_Hello_Seen => True,
                                      Peer_Auth       => Sess.Peer_Auth,
                                      Peer_Data       => Sess.Peer_Data,
                                      Peer_Digest     => Sess.Peer_Digest,
                                      Msgs            => Old.Msgs + 1,
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
                                  and then Sess.Budget = Old.Budget
                                  and then Sess.Q_Len = 0)));

   function Recv_Hello_OK
     (Old, Sess : Session;
      S         : Snapshot;
      F         : Kome.Frontier.State;
      Eff       : Kome.Records.Roster_Record;
      Input     : Byte_Array;
      Part      : Positive;
      Keys      : Key_List;
      M         : Message;
      Peer      : Hello;
      Out_Box   : Outbox;
      Got       : Delivery;
      Root      : Root_Out;
      Result    : Session_Status) return Boolean
   is
   begin
      return
       ((if Result = S_OK and then Old.P = Gate then
                   M.Kind = M_Hello and then not Old.Peer_Hello_Seen
                   and then Hello_Wire_OK (Input) and then Hello_Decoded (Input, Peer)
                   and then Cred_Admissible (F, Old.Peer_DH, Cred_Of (Input))
                   and then Sess = (Old with delta
                                      Peer_Hello_Seen => True,
                                      Peer_Auth       => Sess.Peer_Auth,
                                      Peer_Data       => Sess.Peer_Data,
                                      Peer_Digest     => Sess.Peer_Digest,
                                      Msgs            => Old.Msgs + 1,
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
                                  and then Sess.Budget = Old.Budget
                                  and then Sess.Q_Len = 0)));
   end Recv_Hello_OK;

   --  Receive's Post: a closed gate in Auth or Data aborts.
   function Recv_Gate_Abort
     (Old, Sess : Session;
      S         : Snapshot;
      F         : Kome.Frontier.State;
      Eff       : Kome.Records.Roster_Record;
      Input     : Byte_Array;
      Part      : Positive;
      Keys      : Key_List;
      M         : Message;
      Peer      : Hello;
      Out_Box   : Outbox;
      Got       : Delivery;
      Root      : Root_Out;
      Result    : Session_Status) return Boolean
   with
     Ghost, Global => null,
     Pre  => Valid (S) and then Session_OK (Old) and then Sess.Oblig_Cap = Old.Oblig_Cap and then Session_OK (Sess)
             and then Outbox_OK (S, Out_Box),
     Post => Recv_Gate_Abort'Result =
       ((if Result = S_Aborted and then Old.P in Auth | Data then
                   not Gate_Open (Old.Cid, F, Eff, Old.Peer_DH)
                   and then Sess = (Old with delta P => Done, Aborted => True)
                   and then Out_Box.N = 0 and then Got = No_Delivery
                   and then not Root.Send));

   function Recv_Gate_Abort
     (Old, Sess : Session;
      S         : Snapshot;
      F         : Kome.Frontier.State;
      Eff       : Kome.Records.Roster_Record;
      Input     : Byte_Array;
      Part      : Positive;
      Keys      : Key_List;
      M         : Message;
      Peer      : Hello;
      Out_Box   : Outbox;
      Got       : Delivery;
      Root      : Root_Out;
      Result    : Session_Status) return Boolean
   is
   begin
      return
       ((if Result = S_Aborted and then Old.P in Auth | Data then
                   not Gate_Open (Old.Cid, F, Eff, Old.Peer_DH)
                   and then Sess = (Old with delta P => Done, Aborted => True)
                   and then Out_Box.N = 0 and then Got = No_Delivery
                   and then not Root.Send));
   end Recv_Gate_Abort;

   --  Receive's Post: an accepted RANGE part, ROOT, ELEMENTS or HAVE.
   function Recv_Data_OK
     (Old, Sess : Session;
      S         : Snapshot;
      F         : Kome.Frontier.State;
      Eff       : Kome.Records.Roster_Record;
      Input     : Byte_Array;
      Part      : Positive;
      Keys      : Key_List;
      M         : Message;
      Peer      : Hello;
      Out_Box   : Outbox;
      Got       : Delivery;
      Root      : Root_Out;
      Result    : Session_Status) return Boolean
   with
     Ghost, Global => null,
     Pre  => Valid (S) and then Session_OK (Old) and then Sess.Oblig_Cap = Old.Oblig_Cap and then Session_OK (Sess)
             and then Outbox_OK (S, Out_Box)
             and then (if Result = S_OK then Sess.Msgs = Old.Msgs + 1),
     Post => Recv_Data_OK'Result =
       ((if Result = S_OK and then Old.P in Auth | Data then
                   M.Kind in M_Range | M_Elements | M_Have
                   and then not Root.Send
                   and then M = Bind (Old, Decode_Of (Input, Part, Keys).M)
                   and then Decode_Facts (Input, Part, Keys, Decode_Of (Input, Part, Keys).M, True)
                   and then Msg_OK (M)
                   and then Root_Or_Owed (Old, M)
                   and then Gate_Open (Old.Cid, F, Eff, Old.Peer_DH)
                   and then Out_Box = Reply_Of (S, M).Box
                   and then Got = Reply_Of (S, M).Got
                   and then Delivers (S, M, Got)
                   and then Answers (S, M, Out_Box)
                   and then Shrinks (S, M, Out_Box)
                   and then Sess.Ranges = Old.Ranges + Num_Ranges (Out_Box)
                   and then Sess.Ranges <= Range_Budget (S)
                   and then Sess.Shipped = Old.Shipped + Item_Bytes (S, Out_Box)
                   and then Sess.Shipped <= Ship_Budget (S)
                   and then Sess.Q_Len =
                              Old.Q_Len
                              - (if Group_Done (Old, M) then 1 else 0)
                              + Obligations (Out_Box)
                   and then Queue_Step (Old, Sess, M, Out_Box)
                   and then Sess.Auth_Root_Seen = (Old.Auth_Root_Seen or else M.Root)
                   and then Sess.P =
                              (if Old.P = Data
                                 or else (M.Root and then Old.Auth_Root_Seen)
                               then (if Sess.Q_Len = 0 then Done else Data)
                               else Auth)
                   and then Sess = (Old with delta
                                      Msgs           => Old.Msgs + 1,
                                      P              => Sess.P,
                                      Q              => Sess.Q,
                                      Q_Head         => Sess.Q_Head,
                                      Q_Len          => Sess.Q_Len,
                                      Ranges         => Sess.Ranges,
                                      Shipped        => Sess.Shipped,
                                      Auth_Root_Seen => Sess.Auth_Root_Seen)));

   function Recv_Data_OK
     (Old, Sess : Session;
      S         : Snapshot;
      F         : Kome.Frontier.State;
      Eff       : Kome.Records.Roster_Record;
      Input     : Byte_Array;
      Part      : Positive;
      Keys      : Key_List;
      M         : Message;
      Peer      : Hello;
      Out_Box   : Outbox;
      Got       : Delivery;
      Root      : Root_Out;
      Result    : Session_Status) return Boolean
   is
   begin
      return
       ((if Result = S_OK and then Old.P in Auth | Data then
                   M.Kind in M_Range | M_Elements | M_Have
                   and then not Root.Send
                   and then M = Bind (Old, Decode_Of (Input, Part, Keys).M)
                   and then Decode_Facts (Input, Part, Keys, Decode_Of (Input, Part, Keys).M, True)
                   and then Msg_OK (M)
                   and then Root_Or_Owed (Old, M)
                   and then Gate_Open (Old.Cid, F, Eff, Old.Peer_DH)
                   and then Out_Box = Reply_Of (S, M).Box
                   and then Got = Reply_Of (S, M).Got
                   and then Delivers (S, M, Got)
                   and then Answers (S, M, Out_Box)
                   and then Shrinks (S, M, Out_Box)
                   and then Sess.Ranges = Old.Ranges + Num_Ranges (Out_Box)
                   and then Sess.Ranges <= Range_Budget (S)
                   and then Sess.Shipped = Old.Shipped + Item_Bytes (S, Out_Box)
                   and then Sess.Shipped <= Ship_Budget (S)
                   and then Sess.Q_Len =
                              Old.Q_Len
                              - (if Group_Done (Old, M) then 1 else 0)
                              + Obligations (Out_Box)
                   and then Queue_Step (Old, Sess, M, Out_Box)
                   and then Sess.Auth_Root_Seen = (Old.Auth_Root_Seen or else M.Root)
                   and then Sess.P =
                              (if Old.P = Data
                                 or else (M.Root and then Old.Auth_Root_Seen)
                               then (if Sess.Q_Len = 0 then Done else Data)
                               else Auth)
                   and then Sess = (Old with delta
                                      Msgs           => Old.Msgs + 1,
                                      P              => Sess.P,
                                      Q              => Sess.Q,
                                      Q_Head         => Sess.Q_Head,
                                      Q_Len          => Sess.Q_Len,
                                      Ranges         => Sess.Ranges,
                                      Shipped        => Sess.Shipped,
                                      Auth_Root_Seen => Sess.Auth_Root_Seen)));
   end Recv_Data_OK;

   --  Recv_Status from the status, in a small context (the exit paths
   --  of Receive_Impl carry the whole reply in theirs).
   procedure Lemma_Recv_Status
     (Old, Sess : Session;
      S         : Snapshot;
      F         : Kome.Frontier.State;
      Eff       : Kome.Records.Roster_Record;
      Input     : Byte_Array;
      Part      : Positive;
      Keys      : Key_List;
      M         : Message;
      Peer      : Hello;
      Out_Box   : Outbox;
      Got       : Delivery;
      Root      : Root_Out;
      Result    : Session_Status)
   with
     Ghost, Global => null,
     Pre  => Valid (S) and then Session_OK (Old) and then Sess.Oblig_Cap = Old.Oblig_Cap and then Session_OK (Sess)
             and then Outbox_OK (S, Out_Box)
             and then Result = Status_Of (Old, S, F, Eff, Input, Part, Keys),
     Post => Recv_Status (Old, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got,
                          Root, Result);

   procedure Lemma_Recv_Status
     (Old, Sess : Session;
      S         : Snapshot;
      F         : Kome.Frontier.State;
      Eff       : Kome.Records.Roster_Record;
      Input     : Byte_Array;
      Part      : Positive;
      Keys      : Key_List;
      M         : Message;
      Peer      : Hello;
      Out_Box   : Outbox;
      Got       : Delivery;
      Root      : Root_Out;
      Result    : Session_Status)
   is null;

   --  Recv_Kinds on a refusal, from its facts in a small context.
   procedure Lemma_Recv_Kinds_Refused
     (Old, Sess : Session;
      S         : Snapshot;
      F         : Kome.Frontier.State;
      Eff       : Kome.Records.Roster_Record;
      Input     : Byte_Array;
      Part      : Positive;
      Keys      : Key_List;
      M         : Message;
      Peer      : Hello;
      Out_Box   : Outbox;
      Got       : Delivery;
      Root      : Root_Out;
      Result    : Session_Status)
   with
     Ghost, Global => null,
     Pre  => Valid (S) and then Session_OK (Old) and then Sess.Oblig_Cap = Old.Oblig_Cap
             and then Session_OK (Sess) and then Outbox_OK (S, Out_Box)
             and then Result in S_Malformed | S_Unexpected | S_Limit
             and then Old.P /= Done
             and then Sess = Old and then Out_Box.N = 0 and then Got = No_Delivery
             and then not Root.Send,
     Post => Recv_Kinds (Old, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result);

   procedure Lemma_Recv_Kinds_Refused
     (Old, Sess : Session;
      S         : Snapshot;
      F         : Kome.Frontier.State;
      Eff       : Kome.Records.Roster_Record;
      Input     : Byte_Array;
      Part      : Positive;
      Keys      : Key_List;
      M         : Message;
      Peer      : Hello;
      Out_Box   : Outbox;
      Got       : Delivery;
      Root      : Root_Out;
      Result    : Session_Status)
   is null;

   --  Recv_Hello_Abort on a refused HELLO credential, from its facts in a
   --  small context.
   procedure Lemma_Recv_Hello_Abort
     (Old, Sess : Session;
      S         : Snapshot;
      F         : Kome.Frontier.State;
      Eff       : Kome.Records.Roster_Record;
      Input     : Byte_Array;
      Part      : Positive;
      Keys      : Key_List;
      M         : Message;
      Peer      : Hello;
      Out_Box   : Outbox;
      Got       : Delivery;
      Root      : Root_Out;
      Result    : Session_Status)
   with
     Ghost, Global => null,
     Pre  => Valid (S) and then Session_OK (Old) and then Sess.Oblig_Cap = Old.Oblig_Cap
             and then Session_OK (Sess) and then Outbox_OK (S, Out_Box)
             and then Result = S_Aborted and then Old.P = Gate
             and then M.Kind = M_Hello and then not Old.Peer_Hello_Seen
             and then Hello_Wire_OK (Input)
             and then not Cred_Admissible (F, Old.Peer_DH, Cred_Of (Input))
             and then Peer = Empty_Hello
             and then Sess = (Old with delta P => Done, Aborted => True)
             and then Out_Box.N = 0 and then Got = No_Delivery and then not Root.Send,
     Post => Recv_Hello_Abort (Old, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result);

   procedure Lemma_Recv_Hello_Abort
     (Old, Sess : Session;
      S         : Snapshot;
      F         : Kome.Frontier.State;
      Eff       : Kome.Records.Roster_Record;
      Input     : Byte_Array;
      Part      : Positive;
      Keys      : Key_List;
      M         : Message;
      Peer      : Hello;
      Out_Box   : Outbox;
      Got       : Delivery;
      Root      : Root_Out;
      Result    : Session_Status)
   is null;

   function Receive_Post
     (Old, Sess : Session;
      S         : Snapshot;
      F         : Kome.Frontier.State;
      Eff       : Kome.Records.Roster_Record;
      Input     : Byte_Array;
      Part      : Positive;
      Keys      : Key_List;
      M         : Message;
      Peer      : Hello;
      Out_Box   : Outbox;
      Got       : Delivery;
      Root      : Root_Out;
      Result    : Session_Status) return Boolean
   with
     Ghost, Global => null,
     Pre  => Valid (S) and then Session_OK (Old) and then Sess.Oblig_Cap = Old.Oblig_Cap,
     Post => Receive_Post'Result =
       (Recv_Fields (Old, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result)
         and then Recv_Status (Old, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result)
         and then Recv_Kinds (Old, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result)
         and then Recv_Hello_Abort (Old, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result)
         and then Recv_Hello_OK (Old, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result)
         and then Recv_Gate_Abort (Old, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result)
         and then Recv_Data_OK (Old, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));

   function Receive_Post
     (Old, Sess : Session;
      S         : Snapshot;
      F         : Kome.Frontier.State;
      Eff       : Kome.Records.Roster_Record;
      Input     : Byte_Array;
      Part      : Positive;
      Keys      : Key_List;
      M         : Message;
      Peer      : Hello;
      Out_Box   : Outbox;
      Got       : Delivery;
      Root      : Root_Out;
      Result    : Session_Status) return Boolean
   is
   begin
      return
       (Recv_Fields (Old, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result)
         and then Recv_Status (Old, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result)
         and then Recv_Kinds (Old, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result)
         and then Recv_Hello_Abort (Old, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result)
         and then Recv_Hello_OK (Old, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result)
         and then Recv_Gate_Abort (Old, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result)
         and then Recv_Data_OK (Old, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
   end Receive_Post;

   pragma Warnings (GNATprove, On, "unused variable");
   pragma Warnings (On, "formal parameter * is not referenced");

   --  The body of Receive. Its Post is Receive_Post of the entry state, so
   --  Receive's own Post is one step from it (Receive_Post).
   procedure Receive_Impl
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
     Post   => Receive_Post (Sess'Old, Sess, S, F, Eff, Input, Part, Keys, M, Peer,
                             Out_Box, Got, Root, Result);

   procedure Receive_Impl
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
   is
      OK    : Boolean;
      Sess0 : constant Session := Sess with Ghost;
   begin
      M := (others => <>);
      Peer := Empty_Hello;
      Out_Box := Empty_Box;
      Got := No_Delivery;
      Root := No_Root;

      if Sess.P = Done then
         Result := S_Unexpected;
         pragma Assert (Result = Status_Of (Sess0, S, F, Eff, Input, Part, Keys));
         pragma Assert (Recv_Fields
           (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
         Lemma_Recv_Status
           (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result);
         pragma Assert (Recv_Kinds
           (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
         pragma Assert (Recv_Hello_Abort
           (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
         pragma Assert (Recv_Hello_OK
           (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
         pragma Assert (Recv_Gate_Abort
           (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
         pragma Assert (Recv_Data_OK
           (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
         pragma Assert (Receive_Post (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
         return;
      end if;
      if Input'Last < Input'First then
         Result := S_Malformed;
         pragma Assert (Result = Status_Of (Sess0, S, F, Eff, Input, Part, Keys));
         pragma Assert (Recv_Fields
           (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
         Lemma_Recv_Status
           (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result);
         pragma Assert (Recv_Kinds
           (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
         pragma Assert (Recv_Hello_Abort
           (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
         pragma Assert (Recv_Hello_OK
           (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
         pragma Assert (Recv_Gate_Abort
           (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
         pragma Assert (Recv_Data_OK
           (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
         pragma Assert (Receive_Post (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
         return;
      end if;

      if Input (Input'First) = Tag_Hello then
         --  The HELLO, once, in the gate.
         M.Kind := M_Hello;
         if Sess.P /= Gate or else Sess.Peer_Hello_Seen then
            Result := S_Unexpected;
            pragma Assert (Result = Status_Of (Sess0, S, F, Eff, Input, Part, Keys));
            pragma Assert (Recv_Fields
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            Lemma_Recv_Status
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result);
            pragma Assert (Recv_Kinds
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            pragma Assert (Recv_Hello_Abort
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            pragma Assert (Recv_Hello_OK
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            pragma Assert (Recv_Gate_Abort
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            pragma Assert (Recv_Data_OK
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            pragma Assert (Receive_Post (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            return;
         end if;
         if Sess.Msgs = Sess.Budget then
            Result := S_Limit;
            pragma Assert (Result = Status_Of (Sess0, S, F, Eff, Input, Part, Keys));
            pragma Assert (Recv_Fields
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            Lemma_Recv_Status
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result);
            pragma Assert (Recv_Kinds
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            pragma Assert (Recv_Hello_Abort
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            pragma Assert (Recv_Hello_OK
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            pragma Assert (Recv_Gate_Abort
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            pragma Assert (Recv_Data_OK
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            pragma Assert (Receive_Post (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            return;
         end if;
         if not Hello_Wire_OK (Input) then
            Result := S_Malformed;
            pragma Assert (Result = Status_Of (Sess0, S, F, Eff, Input, Part, Keys));
            pragma Assert (Recv_Fields
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            Lemma_Recv_Status
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result);
            pragma Assert (Recv_Kinds
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            pragma Assert (Recv_Hello_Abort
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            pragma Assert (Recv_Hello_OK
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            pragma Assert (Recv_Gate_Abort
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            pragma Assert (Recv_Data_OK
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            pragma Assert (Receive_Post (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            return;
         end if;
         --  The credential check (A13, G12), before the decode: a refused
         --  credential is not returned.
         if not Cred_Admissible (F, Sess.Peer_DH, Cred_Of (Input)) then
            Sess.P := Done;
            Sess.Aborted := True;
            Result := S_Aborted;
            pragma Assert (Result = Status_Of (Sess0, S, F, Eff, Input, Part, Keys));
            pragma Assert (Session_OK (Sess));
            pragma Assert (Sess.R = Sess0.R and then Sess.Cid = Sess0.Cid
                           and then Sess.Peer_DH = Sess0.Peer_DH
                           and then Sess.Our_N = Sess0.Our_N
                           and then Sess.Our_Digest = Sess0.Our_Digest);
            pragma Assert (Sess = (Sess0 with delta P => Done, Aborted => True));
            pragma Assert (not Cred_Admissible (F, Sess0.Peer_DH, Cred_Of (Input)));
            pragma Assert (M.Kind = M_Hello and then not Sess0.Peer_Hello_Seen
                           and then Hello_Wire_OK (Input) and then Peer = Empty_Hello
                           and then Out_Box.N = 0 and then Got = No_Delivery
                           and then not Root.Send);
            pragma Assert (Recv_Fields
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            Lemma_Recv_Status
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result);
            pragma Assert (Recv_Kinds
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            Lemma_Recv_Hello_Abort
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result);
            pragma Assert (Recv_Hello_OK
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            pragma Assert (Recv_Gate_Abort
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            pragma Assert (Recv_Data_OK
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            pragma Assert (Receive_Post (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            return;
         end if;
         Decode_Hello (Input, Peer, OK);
         pragma Assert (OK);
         Sess.Peer_Hello_Seen := True;
         Sess.Peer_Auth := Claim (Peer.N_Auth);
         Sess.Peer_Data := Claim (Peer.N_Data);
         Sess.Peer_Digest := Kome.Keys.To_Key256 (Peer.Digest);
         Sess.Msgs := Sess.Msgs + 1;
         if Sess.Hello_Sent then
            Exchange_Done (Sess, Root);
         end if;
         Result := S_OK;
         pragma Assert (Result = Status_Of (Sess0, S, F, Eff, Input, Part, Keys));
         pragma Assert (Hello_Wire_OK (Input) and then Hello_Decoded (Input, Peer));
         pragma Assert (Session_OK (Sess));
         pragma Assert (if Sess.Hello_Sent then After_Hellos (Sess, Root)
                        else Sess.P = Gate and then not Root.Send
                             and then Sess.Budget = Sess0.Budget
                             and then Sess.Q_Len = 0);
         pragma Assert (Sess = (Sess0 with delta
                                  Peer_Hello_Seen => True,
                                  Peer_Auth       => Sess.Peer_Auth,
                                  Peer_Data       => Sess.Peer_Data,
                                  Peer_Digest     => Sess.Peer_Digest,
                                  Msgs            => Sess0.Msgs + 1,
                                  P               => Sess.P,
                                  Budget          => Sess.Budget,
                                  Q               => Sess.Q,
                                  Q_Len           => Sess.Q_Len,
                                  Auth_Root_Seen  => Sess.Auth_Root_Seen));
         pragma Assert (Sess.R = Sess0.R and then Sess.Cid = Sess0.Cid
                        and then Sess.Peer_DH = Sess0.Peer_DH
                        and then Sess.Our_N = Sess0.Our_N
                        and then Sess.Our_Digest = Sess0.Our_Digest);
         pragma Assert (Out_Box = Empty_Box and then Outbox_OK (S, Out_Box));
         pragma Assert (Sess.Msgs = Sess0.Msgs + 1 and then not Sess.Aborted);
         pragma Assert (Recv_Fields
           (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
         Lemma_Recv_Status
           (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result);
         pragma Assert (Recv_Kinds
           (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
         pragma Assert (Recv_Hello_Abort
           (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
         pragma Assert (Recv_Hello_OK
           (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
         pragma Assert (Recv_Gate_Abort
           (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
         pragma Assert (Recv_Data_OK
           (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
         pragma Assert (Receive_Post (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));

      else
         --  RANGE part, ROOT, ELEMENTS, HAVE: only in Auth and Data.
         if Sess.P not in Auth | Data then
            Result := S_Unexpected;
            pragma Assert (Result = Status_Of (Sess0, S, F, Eff, Input, Part, Keys));
            pragma Assert (Recv_Fields
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            Lemma_Recv_Status
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result);
            pragma Assert (Recv_Kinds
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            pragma Assert (Recv_Hello_Abort
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            pragma Assert (Recv_Hello_OK
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            pragma Assert (Recv_Gate_Abort
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            pragma Assert (Recv_Data_OK
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            pragma Assert (Receive_Post (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            return;
         end if;
         --  The gate, after the last batch (S9).
         if not Gate_Open (Sess.Cid, F, Eff, Sess.Peer_DH) then
            Sess.P := Done;
            Sess.Aborted := True;
            Result := S_Aborted;
            pragma Assert (Result = Status_Of (Sess0, S, F, Eff, Input, Part, Keys));
            pragma Assert (Session_OK (Sess));
            pragma Assert (Recv_Fields
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            Lemma_Recv_Status
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result);
            pragma Assert (Recv_Kinds
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            pragma Assert (Recv_Hello_Abort
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            pragma Assert (Recv_Hello_OK
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            pragma Assert (Recv_Gate_Abort
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            pragma Assert (Recv_Data_OK
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            pragma Assert (Receive_Post (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            return;
         end if;
         if Sess.Msgs = Sess.Budget then
            Result := S_Limit;
            pragma Assert (Result = Status_Of (Sess0, S, F, Eff, Input, Part, Keys));
            pragma Assert (Recv_Fields
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            Lemma_Recv_Status
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result);
            pragma Assert (Recv_Kinds
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            pragma Assert (Recv_Hello_Abort
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            pragma Assert (Recv_Hello_OK
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            pragma Assert (Recv_Gate_Abort
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            pragma Assert (Recv_Data_OK
              (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            pragma Assert (Receive_Post (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            return;
         end if;
         declare
            D : constant Decoding := Decode_Of (Input, Part, Keys);
         begin
            if not D.OK then
               Result := S_Malformed;
               pragma Assert (Result = Status_Of (Sess0, S, F, Eff, Input, Part, Keys));
               pragma Assert (Recv_Fields
                 (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
               Lemma_Recv_Status
                 (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result);
               pragma Assert (Recv_Kinds
                 (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
               pragma Assert (Recv_Hello_Abort
                 (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
               pragma Assert (Recv_Hello_OK
                 (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
               pragma Assert (Recv_Gate_Abort
                 (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
               pragma Assert (Recv_Data_OK
                 (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
               pragma Assert (Receive_Post (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
               return;
            end if;
            M := Bind (Sess, D.M);
            pragma Assert (Msg_OK (M));
            --  A ROOT only as the expected one (D14); every other message
            --  continues the tiling answer of our head obligation (S19).
            if not Root_Or_Owed (Sess, M) then
               Result := S_Unexpected;
               pragma Assert (Result = Status_Of (Sess0, S, F, Eff, Input, Part, Keys));
               pragma Assert (Recv_Fields
                 (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
               Lemma_Recv_Status
                 (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result);
               pragma Assert (Recv_Kinds
                 (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
               pragma Assert (Recv_Hello_Abort
                 (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
               pragma Assert (Recv_Hello_OK
                 (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
               pragma Assert (Recv_Gate_Abort
                 (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
               pragma Assert (Recv_Data_OK
                 (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
               pragma Assert (Receive_Post (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
               return;
            end if;
            declare
               W  : constant Span := Window (S, M.Lo, M.Hi);
               FP : Hash256;
            begin
               --  The reply from the prefix sums: the same Reply_Core on
               --  the same key as Reply_Of (S, M), so it is that reply.
               Fingerprint_Of (S, P, W.First, W.Last, FP);
               Kome.Keys.Lemma_Key_Eq_Is_Bytewise (FP, Range_Fp (S, W.First, W.Last));
               pragma Assert (Kome.Keys.To_Key256 (FP)
                              = Kome.Keys.To_Key256 (Range_Fp (S, W.First, W.Last)));
            declare
               R : constant Reply := Reply_Core (S, M, Kome.Keys.To_Key256 (FP));
            begin
               pragma Assert (Outbox_OK (S, R.Box) and then Delivers (S, M, R.Got)
                              and then Answers (S, M, R.Box)
                              and then Shrinks (S, M, R.Box));
               pragma Assert (R = Reply_Of (S, M));
               pragma Assert (R.Box = Reply_Of (S, M).Box and then R.Got = Reply_Of (S, M).Got);
               if not Within_Budgets (Sess, S, M, R.Box) then
                  Result := S_Limit;
                  pragma Assert (Result = Status_Of (Sess0, S, F, Eff, Input, Part, Keys));
                  pragma Assert (Sess = Sess0);
                  pragma Assert (Out_Box.N = 0 and then Got = No_Delivery
                                 and then not Root.Send);
                  pragma Assert (Recv_Fields
                    (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
                  Lemma_Recv_Status
                    (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result);
                  pragma Assert (Sess0.P in Auth | Data);
                  Lemma_Recv_Kinds_Refused
                    (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result);
                  pragma Assert (Recv_Hello_Abort
                    (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
                  pragma Assert (Recv_Hello_OK
                    (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
                  pragma Assert (Recv_Gate_Abort
                    (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
                  pragma Assert (Recv_Data_OK
                    (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
                  pragma Assert (Receive_Post (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
                  return;
               end if;
               pragma Assert (Status_Of (Sess0, S, F, Eff, Input, Part, Keys) = S_OK);
               pragma Assert (Sess = Sess0);
               pragma Assert (Root_Or_Owed (Sess0, M));
               pragma Assert (Gate_Open (Sess0.Cid, F, Eff, Sess0.Peer_DH));
               Out_Box := R.Box;
               Got := R.Got;
               Accept_Data (Sess, S, M, Out_Box);
               Result := S_OK;
               pragma Assert (Out_Box = Reply_Of (S, M).Box);
               pragma Assert (Got = Reply_Of (S, M).Got);
               pragma Assert (Decode_Facts (Input, Part, Keys, D.M, True));
               pragma Assert (M = Bind (Sess0, Decode_Of (Input, Part, Keys).M));
               pragma Assert (Msg_OK (M));
               pragma Assert (Delivers (S, M, Got) and then Answers (S, M, Out_Box)
                              and then Shrinks (S, M, Out_Box));
               --  The Post of this path, conjunct by conjunct.
               pragma Assert (Session_OK (Sess) and then not Sess.Aborted);
               pragma Assert (Sess.R = Sess0.R and then Sess.Cid = Sess0.Cid
                              and then Sess.Peer_DH = Sess0.Peer_DH
                              and then Sess.Our_N = Sess0.Our_N
                              and then Sess.Our_Digest = Sess0.Our_Digest);
               pragma Assert (Outbox_OK (S, Out_Box));
               pragma Assert (Sess.Msgs = Sess0.Msgs + 1);
               pragma Assert (M.Kind in M_Range | M_Elements | M_Have
                              and then not Root.Send);
               pragma Assert (M = Bind (Sess0, Decode_Of (Input, Part, Keys).M));
               pragma Assert
                 (Decode_Facts (Input, Part, Keys, Decode_Of (Input, Part, Keys).M, True));
               pragma Assert (Root_Or_Owed (Sess0, M));
               pragma Assert (Out_Box = Reply_Of (S, M).Box and then Got = Reply_Of (S, M).Got);
               pragma Assert (Sess.Ranges = Sess0.Ranges + Num_Ranges (Out_Box)
                              and then Sess.Ranges <= Range_Budget (S));
               pragma Assert (Sess.Shipped = Sess0.Shipped + Item_Bytes (S, Out_Box)
                              and then Sess.Shipped <= Ship_Budget (S));
               pragma Assert (Sess.Q_Len =
                                Sess0.Q_Len
                                - (if Group_Done (Sess0, M) then 1 else 0)
                                + Obligations (Out_Box));
               pragma Assert (Queue_Step (Sess0, Sess, M, Out_Box));
               pragma Assert (Sess.Auth_Root_Seen = (Sess0.Auth_Root_Seen or else M.Root));
               pragma Assert (Sess.P =
                                (if Sess0.P = Data
                                   or else (M.Root and then Sess0.Auth_Root_Seen)
                                 then (if Sess.Q_Len = 0 then Done else Data)
                                 else Auth));
               pragma Assert (Sess = (Sess0 with delta
                                        Msgs           => Sess0.Msgs + 1,
                                        P              => Sess.P,
                                        Q              => Sess.Q,
                                        Q_Head         => Sess.Q_Head,
                                        Q_Len          => Sess.Q_Len,
                                        Ranges         => Sess.Ranges,
                                        Shipped        => Sess.Shipped,
                                        Auth_Root_Seen => Sess.Auth_Root_Seen));
               pragma Assert (Recv_Fields
                 (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
               Lemma_Recv_Status
                 (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result);
               pragma Assert (Recv_Kinds
                 (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
               pragma Assert (Recv_Hello_Abort
                 (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
               pragma Assert (Recv_Hello_OK
                 (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
               pragma Assert (Recv_Gate_Abort
                 (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
               pragma Assert (Recv_Data_OK
                 (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
               pragma Assert (Receive_Post (Sess0, Sess, S, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result));
            end;
            end;
         end;
      end if;
   end Receive_Impl;

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
   is
   begin
      Receive_Impl (Sess, S, P, F, Eff, Input, Part, Keys, M, Peer, Out_Box, Got, Root, Result);
   end Receive;

end Kome.Reconcile;
