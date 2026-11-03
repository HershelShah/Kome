pragma Ada_2022;
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

   ----------------------------------------------------------------------
   --  Key_Lt is bytewise order on the wire key. The 81 bytes are kind ‖
   --  ent[16] ‖ fh[32] ‖ h[32]. Kome.Keys decodes each field (Wire_Id128 /
   --  Wire_Key256 are To_Id128 / To_Key256 of the slice). The Id128 and
   --  Key256 laws of Kome.Keys give the field orders. Key_Lt is their
   --  lexicographic composition.
   ----------------------------------------------------------------------

   --  The three fields of a wire key, as the Kome.Keys byte views.
   procedure Lemma_Fields (A : Key_Wire) with
     Ghost, Global => null,
     Post => Wire_Id128 (A, 1) = Kome.Keys.To_Id128 (Kome.Keys.Id_Bytes (A (1 .. 16)))
             and then Wire_Key256 (A, 17)
                        = Kome.Keys.To_Key256 (Kome.Keys.Key_Bytes (A (17 .. 48)))
             and then Wire_Key256 (A, 49)
                        = Kome.Keys.To_Key256 (Kome.Keys.Key_Bytes (A (49 .. 80)))
             and then (for all J in Kome.Keys.Id_Index =>
                         Kome.Keys.Id_Bytes (A (1 .. 16)) (J) = A (1 + J))
             and then (for all J in Kome.Keys.Key_Index =>
                         Kome.Keys.Key_Bytes (A (17 .. 48)) (J) = A (17 + J))
             and then (for all J in Kome.Keys.Key_Index =>
                         Kome.Keys.Key_Bytes (A (49 .. 80)) (J) = A (49 + J))
   is
   begin
      Kome.Keys.Lemma_Id_Slide (A (1 .. 16));
      Kome.Keys.Lemma_Key_Slide (A (17 .. 48));
      Kome.Keys.Lemma_Key_Slide (A (49 .. 80));
      pragma Assert (Wire_Id128 (A, 1) = Kome.Keys.To_Id128 (A (1 .. 16)));
      pragma Assert (Wire_Key256 (A, 17) = Kome.Keys.To_Key256 (A (17 .. 48)));
      pragma Assert (Wire_Key256 (A, 49) = Kome.Keys.To_Key256 (A (49 .. 80)));
   end Lemma_Fields;

   procedure Lemma_Key_Eq_Is_Bytewise (A, B : Key_Wire) is
   begin
      Lemma_Fields (A);
      Lemma_Fields (B);
      Kome.Keys.Lemma_Id_Eq_Is_Bytewise
        (Kome.Keys.Id_Bytes (A (1 .. 16)), Kome.Keys.Id_Bytes (B (1 .. 16)));
      Kome.Keys.Lemma_Key_Eq_Is_Bytewise
        (Kome.Keys.Key_Bytes (A (17 .. 48)), Kome.Keys.Key_Bytes (B (17 .. 48)));
      Kome.Keys.Lemma_Key_Eq_Is_Bytewise
        (Kome.Keys.Key_Bytes (A (49 .. 80)), Kome.Keys.Key_Bytes (B (49 .. 80)));
      if Wire_Key (A, 0) = Wire_Key (B, 0) then
         pragma Assert (A (0) = B (0));
         pragma Assert (Kome.Keys.Id_Bytes (A (1 .. 16)) = Kome.Keys.Id_Bytes (B (1 .. 16)));
         pragma Assert (Kome.Keys.Key_Bytes (A (17 .. 48)) = Kome.Keys.Key_Bytes (B (17 .. 48)));
         pragma Assert (Kome.Keys.Key_Bytes (A (49 .. 80)) = Kome.Keys.Key_Bytes (B (49 .. 80)));
         pragma Assert (for all J in 1 .. 16 => A (J) = B (J));
         pragma Assert (for all J in 17 .. 48 => A (J) = B (J));
         pragma Assert (for all J in 49 .. 80 => A (J) = B (J));
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
      elsif I <= 48 then
         pragma Assert (Wire_Key (A, 0).K = Wire_Key (B, 0).K);
         pragma Assert (for all J in 1 .. 16 => A (J) = B (J));
         pragma Assert (Wire_Id128 (A, 1) = Wire_Id128 (B, 1));
         Kome.Keys.Lemma_Lt_First_Difference
           (Kome.Keys.Key_Bytes (A (17 .. 48)), Kome.Keys.Key_Bytes (B (17 .. 48)), I - 17);
         Kome.Keys.Lemma_Lt_First_Difference
           (Kome.Keys.Key_Bytes (B (17 .. 48)), Kome.Keys.Key_Bytes (A (17 .. 48)), I - 17);
         pragma Assert (Wire_Key256 (A, 17) /= Wire_Key256 (B, 17));
      else
         pragma Assert (Wire_Key (A, 0).K = Wire_Key (B, 0).K);
         pragma Assert (for all J in 1 .. 16 => A (J) = B (J));
         pragma Assert (Wire_Id128 (A, 1) = Wire_Id128 (B, 1));
         pragma Assert (for all J in 17 .. 48 => A (J) = B (J));
         pragma Assert (Wire_Key256 (A, 17) = Wire_Key256 (B, 17));
         Kome.Keys.Lemma_Lt_First_Difference
           (Kome.Keys.Key_Bytes (A (49 .. 80)), Kome.Keys.Key_Bytes (B (49 .. 80)), I - 49);
      end if;
   end Lemma_Key_Lt_First_Difference;

   ----------------------------------------------------------------------
   --  Snapshot
   ----------------------------------------------------------------------

   procedure Clear (S : out Snapshot) is
   begin
      S.N     := 0;
      S.Used  := 0;
      S.Kinds := [others => 0];
      S.Ents  := [others => (others => 0)];
      S.FHs   := [others => (others => 0)];
      S.Hs    := [others => (others => 0)];
      S.Offs  := [others => 1];
      S.Lens  := [others => 1];
      S.Pool  := [others => 0];
   end Clear;

   procedure Append
     (S      : in out Snapshot;
      K      : Elem_Key;
      F      : Byte_Array;
      Result : out Snap_Status)
   is
   begin
      if K.K > 4 then
         Result := Snap_Bad_Kind;
         return;
      end if;
      if F'Length not in Frame_Size then
         Result := Snap_Too_Large;
         return;
      end if;
      if S.N > 0 and then not Key_Lt (Key (S, S.N), K) then
         Result := Snap_Unsorted;
         return;
      end if;
      if S.N = S.Cap or else not Has_Room (S, F'Length) then
         Result := Snap_No_Space;
         return;
      end if;

      declare
         Old : constant Snapshot := S with Ghost;
         N   : constant Elem_Index := S.N + 1;
         Off : constant Positive := S.Used + 1;
         L   : constant Frame_Size := F'Length;
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

         S.Kinds (N) := K.K;
         S.Ents (N)  := K.Ent;
         S.FHs (N)   := K.FH;
         S.Hs (N)    := K.H;
         S.Offs (N)  := Off;
         S.Lens (N)  := L;
         S.Pool (Off .. Off + L - 1) := F;
         S.Used := S.Used + L;
         S.N := N;

         --  Bridge.
         pragma Assert (for all J in 1 .. N - 1 => Key (S, J) = Key (Old, J));
         pragma Assert (for all J in 1 .. N - 1 => Frame_Len (S, J) = Frame_Len (Old, J));
         pragma Assert (for all J in 1 .. N - 1 =>
                          S.Offs (J) = Old.Offs (J) and then S.Lens (J) = Old.Lens (J));
         pragma Assert (for all J in 1 .. N - 1 => Frame_In_Pool (S, J));
         pragma Assert (Frame_In_Pool (S, N));
         pragma Assert (for all J in 1 .. N => S.Kinds (J) <= 4);
         pragma Assert (Key (S, N) = K);
         pragma Assert (for all J in 1 .. N - 1 => Key_Lt (Key (S, J), Key (S, N)));
         pragma Assert
           (for all I in 1 .. N =>
              (for all J in I + 1 .. N => Key_Lt (Key (S, I), Key (S, J))));
         pragma Assert (Valid (S));
      end;
      Result := Snap_OK;
   end Append;

   procedure Lemma_Frame_Ships (L : Natural) is null;

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

   procedure Lemma_Open_Frames (B : Byte_Array; O : Open_Msg; I : Rv_Index) is null;

   procedure Lemma_Cred_Zero (H : Hello; I : Natural) is null;

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
   Empty_Box  : constant Outbox :=
     (Reply => False, N => 0, P => [others => Empty_Plan]);
   Reply_Box  : constant Outbox :=
     (Reply => True, N => 0, P => [others => Empty_Plan]);

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
   --  n / 16 + 1 elements. [Lo, Hi) holds our elements I .. J (more than
   --  Ship_Threshold of them). Each child is [Child_Lo, Child_Hi) over a
   --  run B .. E. The runs partition I .. J, so the children tile
   --  [Lo, Hi). The first run stops before J, and each later run starts
   --  after I. So each child holds strictly fewer of our elements than
   --  the parent. (The last child takes the remaining elements. With these
   --  sizes, this is exactly its share. The balance is tested, not proved:
   --  the Post states only that each child is strictly smaller.)
   procedure Split
     (S : Snapshot; Lo, Hi : Elem_Key; I, J : Elem_Index; O : out Outbox)
   with
     Global => null,
     Pre  => Valid (S) and then Key_Lt (Lo, Hi)
             and then I <= J and then J <= Count (S)
             and then Covers (S, Lo, Hi, I, J)
             and then J + 1 - I > Ship_Threshold,
     Post => Outbox_OK (S, O)
       and then O.Reply
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
      O := Reply_Box;
      for T in 1 .. Split_Fanout loop
         pragma Loop_Invariant (O.N = T - 1 and then O.Reply);
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
       and then O.N >= 1 and then O.Reply
       and then Tiles (O, Lo, Hi)
       and then All_Kind (O, P_Elements)
       and then Exact_Plans (S, O)
   is
   begin
      O := Reply_Box;
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
            pragma Loop_Invariant (O.N = K - I and then O.Reply);
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
   --  exactly those elements (Have_Exact).
   procedure Have_Back
     (S : Snapshot; M : Message; I : Lo_Bound; J : Elem_Count; O : out Outbox)
   with
     Global => null,
     Pre  => Valid (S) and then Msg_OK (M)
             and then I <= J + 1 and then J <= Count (S)
             and then Covers (S, M.Lo, M.Hi, I, J)
             and then J + 1 - I <= Ship_Threshold,
     Post => Outbox_OK (S, O)
       and then O.N >= 1 and then O.Reply
       and then Have_Exact (S, M, O)
   is
      L   : Index_List := [others => 1];
      C   : Item_Count := 0;
      --  Pos (K - I + 1): the position of our element K in L, if L has
      --  it.
      Pos : Index_List := [others => 1] with Ghost;
   begin
      O := Reply_Box;
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
         pragma Assert (Have_Exact (S, M, O));
      else
         pragma Assert (C >= 1);
         for T in 1 .. C loop
            pragma Loop_Invariant (O.N = T - 1 and then O.Reply);
            pragma Loop_Invariant
              (for all T2 in 1 .. O.N =>
                 Plan_OK (S, O.P (T2)) and then O.P (T2).Kind = P_Have
                 and then O.P (T2).Lo = M.Lo and then O.P (T2).Hi = M.Hi
                 and then O.P (T2).N = 1 and then O.P (T2).Items (1) = L (T2));
            O.P (T) := (Kind  => P_Have,
                        Lo    => M.Lo,
                        Hi    => M.Hi,
                        First => 1,
                        Last  => 0,
                        N     => 1,
                        Items => [others => L (T)]);
            O.N := T;
            pragma Assert (List_Size (S, O.P (T).Items, 1) = Item_Size (S, L (T)));
            pragma Assert (Plan_OK (S, O.P (T)));
         end loop;
         pragma Assert (O.N = C);
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

   --  Exactly the items of M that we do not hold. Our elements in
   --  [M.Lo, M.Hi) are I .. J, and every item is in that range. So a scan
   --  of I .. J decides it.
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

   procedure Respond_Raw
     (S       : Snapshot;
      M       : Message;
      Out_Box : out Outbox;
      Got     : out Delivery)
   with
     Global => null,
     Pre    => Valid (S) and then Msg_OK (M),
     Post   => Outbox_OK (S, Out_Box)
       and then Delivers (S, M, Got)
       and then Answers (S, M, Out_Box)
       and then Shrinks (S, M, Out_Box);

   procedure Respond_Raw
     (S       : Snapshot;
      M       : Message;
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
         when M_Open | M_Hello =>
            pragma Assert (False);

         when M_Range =>
            pragma Assert (Delivers (S, M, Got));
            if N = M.Count and then Range_Fp (S, I, J) = M.Fp then
               pragma Assert (Confirms (S, M));
               Out_Box := Reply_Box;
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
   end Respond_Raw;

   function Reply_Of (S : Snapshot; M : Message) return Reply is
      R : Reply;
   begin
      Respond_Raw (S, M, R.Box, R.Got);
      return R;
   end Reply_Of;

   procedure Respond
     (S       : Snapshot;
      M       : Message;
      Out_Box : out Outbox;
      Got     : out Delivery)
   is
      R : constant Reply := Reply_Of (S, M);
   begin
      Out_Box := R.Box;
      Got := R.Got;
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
      Lemma_Same_Key256 (A, B, P + 17);
      Lemma_Same_Key256 (A, B, P + 49);
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
      Put_Key256 (Buf, P + 17, K.FH);
      pragma Assert (Buf (P) = Byte (K.K));
      pragma Assert (Wire_Id128 (Buf, P + 1) = K.Ent);
      Put_Key256 (Buf, P + 49, K.H);
      pragma Assert (Buf (P) = Byte (K.K));
      pragma Assert (Wire_Id128 (Buf, P + 1) = K.Ent);
      pragma Assert (Wire_Key256 (Buf, P + 17) = K.FH);
      pragma Assert (Wire_Key256 (Buf, P + 49) = K.H);
   end Put_Key;

   --  Tag, group size and range of a RANGE / ELEMENTS / HAVE. The body
   --  (from Elems_O_N to the end) does not change.
   procedure Write_Head
     (Buf : in out Msg_Buffer; Tag : Byte; G : Group_Size; Lo, Hi : Elem_Key)
   with
     Global => null,
     Post => Buf (0) = Tag and then Natural (Buf (O_G)) = G
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
      Buf (O_G) := Byte (G);
      pragma Assert (Wire_Key (Buf, O_Lo) = Lo);
      pragma Assert (Wire_Key (Buf, O_Hi) = Hi);
   end Write_Head;

   --  One item (key ‖ flen ‖ frame) of element X at Buf (P ..).
   procedure Put_Item
     (S : Snapshot; X : Elem_Index; Buf : in out Msg_Buffer; P : in out Natural)
   with
     Global => null,
     Pre  => Valid (S) and then X <= Count (S)
             and then P <= Max_Message_Len - Item_Size (S, X),
     Post => P = P'Old + Item_Size (S, X)
   is
      L   : constant Frame_Size := S.Lens (X);
      Off : constant Positive := S.Offs (X);
   begin
      pragma Assert (Frame_In_Pool (S, X));
      Put_Key (Buf, P, Key (S, X));
      Put_Word (Buf, P + Key_Wire_Len, Word (L));
      Buf (P + Item_Overhead .. P + Item_Overhead + L - 1) :=
        S.Pool (Off .. Off + L - 1);
      P := P + Item_Overhead + L;
   end Put_Item;

   procedure Encode
     (S   : Snapshot;
      P   : Plan;
      G   : Group_Size;
      Buf : out Msg_Buffer;
      Len : out Msg_Length)
   is
   begin
      Buf := [others => 0];
      --  First the body, then the head. The head does not change the
      --  body.
      case P.Kind is
         when P_Range =>
            Put_Word (Buf, Range_O_Count, Word (P.Last + 1 - P.First));
            Buf (Range_O_Fp .. Range_O_Fp + 31) := Range_Fp (S, P.First, P.Last);
            pragma Assert (Wire_U32 (Buf, Range_O_Count) = Word (P.Last + 1 - P.First));
            Len := Range_Len;

         when P_Elements =>
            declare
               Pos : Natural := Elems_Fixed;
            begin
               if P.Last >= P.First then
                  Put_Item (S, P.First, Buf, Pos);
               end if;
               if P.Last >= P.First + 1 then
                  Put_Item (S, P.First + 1, Buf, Pos);
               end if;
               if P.Last >= P.First + 2 then
                  Put_Item (S, P.First + 2, Buf, Pos);
               end if;
               if P.Last >= P.First + 3 then
                  Put_Item (S, P.First + 3, Buf, Pos);
               end if;
               pragma Assert (Pos = Plan_Len (S, P));
               Len := Pos;
            end;
            Buf (Elems_O_N) := Byte (P.Last + 1 - P.First);

         when P_Have =>
            declare
               Pos : Natural := Elems_Fixed;
            begin
               if P.N >= 1 then
                  Put_Item (S, P.Items (1), Buf, Pos);
               end if;
               if P.N >= 2 then
                  Put_Item (S, P.Items (2), Buf, Pos);
               end if;
               if P.N >= 3 then
                  Put_Item (S, P.Items (3), Buf, Pos);
               end if;
               if P.N = 4 then
                  Put_Item (S, P.Items (4), Buf, Pos);
               end if;
               pragma Assert (Pos = Plan_Len (S, P));
               Len := Pos;
            end;
            Buf (Elems_O_N) := Byte (P.N);
      end case;

      declare
         Body_Buf : constant Msg_Buffer := Buf with Ghost;
      begin
         Write_Head (Buf, Tag_Of (P.Kind), G, P.Lo, P.Hi);
         pragma Assert (Buf (Elems_O_N) = Body_Buf (Elems_O_N));
         if P.Kind = P_Range then
            pragma Assert (Buf (Range_O_Count) = Body_Buf (Range_O_Count));
            pragma Assert (Buf (Range_O_Count + 1) = Body_Buf (Range_O_Count + 1));
            pragma Assert (Buf (Range_O_Count + 2) = Body_Buf (Range_O_Count + 2));
            pragma Assert (Buf (Range_O_Count + 3) = Body_Buf (Range_O_Count + 3));
            pragma Assert (Wire_U32 (Buf, Range_O_Count) = Wire_U32 (Body_Buf, Range_O_Count));
            pragma Assert (for all Y in Range_O_Fp .. Range_O_Fp + 31 => Buf (Y) = Body_Buf (Y));
            pragma Assert (Buf (Range_O_Fp .. Range_O_Fp + 31)
                           = Body_Buf (Range_O_Fp .. Range_O_Fp + 31));
         end if;
      end;
   end Encode;

   procedure Lemma_Range_Accepted
     (S : Snapshot; P : Plan; G : Group_Size; Buf : Msg_Buffer)
   is
      B : constant Byte_Array := Buf (0 .. Range_Len - 1);
   begin
      pragma Assert (Natural (B (O_G)) = G);
      pragma Assert (B'First = 0 and then B'Last = Range_Len - 1);
      pragma Assert (for all Y in B'Range => B (Y) = Buf (Y));
      pragma Assert (Wire_Key (B, O_Lo) = Wire_Key (Buf, O_Lo));
      pragma Assert (Wire_Key (B, O_Hi) = Wire_Key (Buf, O_Hi));
      pragma Assert (Wire_U32 (B, Range_O_Count) = Wire_U32 (Buf, Range_O_Count));
      pragma Assert (Key_Lt (P.Lo, P.Hi));
      pragma Assert (P.Last + 1 - P.First <= Kome.Digest.Elem_Max);
      pragma Assert (Range_Wire_OK (B));
   end Lemma_Range_Accepted;

   procedure Lemma_Confirm_Accepted
     (S : Snapshot; P : Plan; G : Group_Size; Buf : Msg_Buffer)
   is
      B : constant Byte_Array := Buf (0 .. Elems_Fixed - 1);
   begin
      pragma Assert (Natural (B (O_G)) = G);
      pragma Assert (B'First = 0 and then B'Last = Elems_Fixed - 1);
      pragma Assert (for all Y in B'Range => B (Y) = Buf (Y));
      pragma Assert (Wire_Key (B, O_Lo) = Wire_Key (Buf, O_Lo));
      pragma Assert (Wire_Key (B, O_Hi) = Wire_Key (Buf, O_Hi));
      pragma Assert (Key_Lt (P.Lo, P.Hi));
      pragma Assert (Empty_Wire_OK (B));
   end Lemma_Confirm_Accepted;

   ----------------------------------------------------------------------
   --  OPEN and HELLO. Fixed layout: first the header, then the frames or
   --  the credential. Each part is written once.
   ----------------------------------------------------------------------

   procedure Encode_Open
     (O   : Open_Msg;
      Buf : out Msg_Buffer;
      Len : out Msg_Length)
   is
      N : constant Rv_Count := O.N_RV;
   begin
      Buf := [others => 0];
      Buf (0) := Tag_Open;
      Buf (Open_O_Proto) := O.Proto;
      Buf (Open_O_NRV) := Byte (N);
      Put_Id (Buf, Open_O_NS, O.NS);
      pragma Assert (Buf (0) = Tag_Open and then Buf (Open_O_Proto) = Proto_Version
                     and then Buf (Open_O_NRV) = Byte (N));
      declare
         Head : constant Msg_Buffer := Buf with Ghost;
      begin
         for I in 1 .. N loop
            pragma Loop_Invariant
              (for all Y in 0 .. Open_Fixed - 1 => Buf (Y) = Head (Y));
            pragma Loop_Invariant
              (for all J in 1 .. I - 1 =>
                 Buf (Rv_At (J) .. Rv_At (J) + Rv_Frame_Len - 1) = O.RV (J));
            Buf (Rv_At (I) .. Rv_At (I) + Rv_Frame_Len - 1) := O.RV (I);
            pragma Assert
              (for all J in 1 .. I - 1 => Rv_At (J) + Rv_Frame_Len - 1 < Rv_At (I));
         end loop;
         pragma Assert (for all Y in 0 .. Open_Fixed - 1 => Buf (Y) = Head (Y));
         pragma Assert (for all Y in Open_O_NS .. Open_O_NS + 15 => Buf (Y) = Head (Y));
         pragma Assert (Wire_U32 (Buf, Open_O_NS) = Wire_U32 (Head, Open_O_NS));
         pragma Assert (Wire_U32 (Buf, Open_O_NS + 4) = Wire_U32 (Head, Open_O_NS + 4));
         pragma Assert (Wire_U32 (Buf, Open_O_NS + 8) = Wire_U32 (Head, Open_O_NS + 8));
         pragma Assert (Wire_U32 (Buf, Open_O_NS + 12) = Wire_U32 (Head, Open_O_NS + 12));
         pragma Assert (Wire_Id128 (Buf, Open_O_NS) = O.NS);
      end;
      Len := Open_Len (N);
      pragma Assert (Open_Wire_OK (Buf (0 .. Len - 1)));
   end Encode_Open;

   procedure Decode_Open
     (Input : Byte_Array;
      O     : out Open_Msg;
      OK    : out Boolean)
   is
   begin
      O := (Proto => Proto_Version,
            NS    => (others => 0),
            N_RV  => 0,
            RV    => [others => Zero_Rv]);
      OK := False;
      if Input'Last < Input'First or else Input'Last - Input'First < Open_Fixed - 1 then
         return;
      end if;
      declare
         F  : constant Natural := Input'First;
         NB : constant Byte := Input (F + Open_O_NRV);
      begin
         if Input (F) /= Tag_Open
           or else Input (F + Open_O_Proto) /= Proto_Version
           or else NB > Rv_Max
           or else Input'Last - F /= Open_Fixed - 1 + Rv_Frame_Len * Natural (NB)
         then
            return;
         end if;
         pragma Assert (Open_Wire_OK (Input));
         O.NS := Wire_Id128 (Input, F + Open_O_NS);
         O.N_RV := Natural (NB);
         for I in 1 .. Natural (NB) loop
            pragma Loop_Invariant
              (for all J in 1 .. I - 1 =>
                 O.RV (J) = Open_Frame (Input, J));
            pragma Loop_Invariant
              (for all J in I .. Rv_Max => O.RV (J) = Zero_Rv);
            pragma Loop_Invariant
              (O.Proto = Proto_Version
               and then O.NS = Wire_Id128 (Input, F + Open_O_NS)
               and then O.N_RV = Natural (NB));
            O.RV (I) := Open_Frame (Input, I);
         end loop;
         pragma Assert (Open_Frames (Input, O));
         OK := True;
      end;
   end Decode_Open;

   procedure Encode_Hello
     (N_Auth, N_Data : Word;
      Digest         : Hash256;
      Cred           : Byte_Array;
      Buf            : out Msg_Buffer;
      Len            : out Msg_Length)
   is
      L : constant Cred_Count := Cred'Length;
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
      Buf (Hello_O_Digest .. Hello_O_Digest + 31) := Digest;
      Buf (Hello_Fixed .. Hello_Fixed + L - 1) := Cred;
      pragma Assert (Wire_U16 (Buf, Hello_O_CLen) = L);
      pragma Assert (Buf (0) = Tag_Hello);
      Put_Word (Buf, Hello_O_NAuth, N_Auth);
      Put_Word (Buf, Hello_O_NData, N_Data);
      pragma Assert (Wire_U32 (Buf, Hello_O_NAuth) = N_Auth);
      pragma Assert (Wire_U16 (Buf, Hello_O_CLen) = L);
      pragma Assert (Buf (Hello_O_Digest .. Hello_O_Digest + 31) = Digest);
      pragma Assert (Buf (Hello_Fixed .. Hello_Fixed + L - 1) = Cred);
      Len := Hello_Fixed + L;
      pragma Assert (Hello_Wire_OK (Buf (0 .. Len - 1)));
   end Encode_Hello;

   procedure Decode_Hello
     (Input : Byte_Array;
      H     : out Hello;
      OK    : out Boolean)
   is
   begin
      H := (N_Auth   => 0,
            N_Data   => 0,
            Digest   => [others => 0],
            Cred_Len => 0,
            Cred     => [others => 0]);
      OK := False;
      if Input'Last < Input'First or else Input'Last - Input'First < Hello_Fixed - 1 then
         return;
      end if;
      declare
         F  : constant Natural := Input'First;
         CL : constant Natural := Wire_U16 (Input, F + Hello_O_CLen);
      begin
         if Input (F) /= Tag_Hello
           or else CL > Cred_Max
           or else Input'Last - F /= Hello_Fixed - 1 + CL
         then
            return;
         end if;
         pragma Assert (Hello_Wire_OK (Input));
         H.N_Auth := Wire_U32 (Input, F + Hello_O_NAuth);
         H.N_Data := Wire_U32 (Input, F + Hello_O_NData);
         H.Digest := Input (F + Hello_O_Digest .. F + Hello_O_Digest + 31);
         H.Cred_Len := CL;
         if CL > 0 then
            H.Cred (0 .. CL - 1) := Input (F + Hello_Fixed .. Input'Last);
         end if;
         OK := True;
      end;
   end Decode_Hello;

   --  The RANGE fields, in a small context.
   procedure Lemma_Range_Fields (Input : Byte_Array; M : Message) with
     Ghost, Global => null,
     Pre  => Range_Wire_OK (Input)
             and then M.Count = Natural (Wire_U32 (Input, Input'First + Range_O_Count))
             and then M.Fp = Input (Input'First + Range_O_Fp
                                    .. Input'First + Range_O_Fp + 31),
     Post => Range_Fields (Input, M);

   procedure Lemma_Range_Fields (Input : Byte_Array; M : Message) is null;

   --  An ELEMENTS / HAVE that is built from checked items is well-formed,
   --  in a small context.
   procedure Lemma_Items_OK
     (K : Msg_Kind; G : Group_Size; Lo, Hi : Elem_Key; N : Item_Count;
      Items : In_Items)
   with
     Ghost, Global => null,
     Pre  => K in M_Elements | M_Have and then Key_Lt (Lo, Hi)
             and then (for all T in 1 .. N =>
                         Items (T).Key.K <= 4 and then In_Window (Items (T).Key, Lo, Hi))
             and then (for all T in 2 .. N => Key_Lt (Items (T - 1).Key, Items (T).Key)),
     Post => Msg_OK ((Kind => K, G => G, Lo => Lo, Hi => Hi, Count => 0,
                      Fp => [others => 0], N => N, Items => Items));

   procedure Lemma_Items_OK
     (K : Msg_Kind; G : Group_Size; Lo, Hi : Elem_Key; N : Item_Count;
      Items : In_Items) is null;

   procedure Decode_Raw
     (Input  : Byte_Array;
      M      : out Message;
      OK     : out Boolean)
   with
     Global => null,
     Post   => Decode_Facts (Input, M, OK);

   procedure Decode_Raw
     (Input  : Byte_Array;
      M      : out Message;
      OK     : out Boolean)
   is
   begin
      M := (others => <>);
      OK := False;
      --  Total over every input: Decode_Raw calculates no length before it
      --  knows that the length is at most Max_Message_Len.
      if Input'Last < Input'First
        or else Input'Last - Input'First >= Max_Message_Len
        or else Input'Last - Input'First < Elems_Fixed - 1
      then
         return;
      end if;

      declare
         Len : constant Natural := Input'Last - Input'First + 1;
         F   : constant Natural := Input'First;
         Tag : constant Byte := Input (F);
         G   : constant Byte := Input (F + O_G);
         Lo  : constant Elem_Key := Wire_Key (Input, F + O_Lo);
         Hi  : constant Elem_Key := Wire_Key (Input, F + O_Hi);
      begin
         if G > Split_Fanout or else not Key_Lt (Lo, Hi) then
            return;
         end if;

         if Tag = Tag_Range then
            if Len /= Range_Len then
               return;
            end if;
            declare
               C : constant Word := Wire_U32 (Input, F + Range_O_Count);
            begin
               if C > Kome.Digest.Elem_Max then
                  return;
               end if;
               M := (Kind   => M_Range,
                     G      => Natural (G),
                     Lo     => Lo,
                     Hi     => Hi,
                     Count  => Elem_Count (C),
                     Fp     => Input (F + Range_O_Fp .. F + Range_O_Fp + 31),
                     N      => 0,
                     Items  => [others => (Key => Min_Key, Off => 0, Len => 1)]);
               pragma Assert (Msg_OK (M));
               pragma Assert (Range_Wire_OK (Input));
               Lemma_Range_Fields (Input, M);
               OK := True;
            end;

         elsif Tag = Tag_Elements or else Tag = Tag_Have then
            declare
               NB    : constant Byte := Input (F + Elems_O_N);
               Items : In_Items := [others => (Key => Min_Key, Off => 0, Len => 1)];
               Pos   : Natural := Elems_Fixed;   --  relative to F
            begin
               if NB > Ship_Threshold then
                  return;
               end if;
               for T in 1 .. Item_Count (NB) loop
                  pragma Loop_Invariant (Pos >= Elems_Fixed and then Pos <= Len);
                  pragma Loop_Invariant
                    (for all T2 in 1 .. T - 1 =>
                       Items (T2).Key.K <= 4
                       and then In_Window (Items (T2).Key, Lo, Hi)
                       and then Items (T2).Off >= Input'First
                       and then Items (T2).Off <= Input'Last
                       and then Input'Last - Items (T2).Off >= Items (T2).Len - 1);
                  pragma Loop_Invariant
                    (for all T2 in 2 .. T - 1 =>
                       Key_Lt (Items (T2 - 1).Key, Items (T2).Key));
                  if Len - Pos < Item_Overhead + 1 then
                     return;
                  end if;
                  declare
                     K  : constant Elem_Key := Wire_Key (Input, F + Pos);
                     FL : constant Word := Wire_U32 (Input, F + Pos + Key_Wire_Len);
                  begin
                     if FL < 1 or else FL > Frame_Ship_Max
                       or else Word (Len - Pos - Item_Overhead) < FL
                       or else K.K > 4
                       or else not In_Window (K, Lo, Hi)
                       or else (T > 1 and then not Key_Lt (Items (T - 1).Key, K))
                     then
                        return;
                     end if;
                     Items (T) := (Key => K,
                                   Off => F + Pos + Item_Overhead,
                                   Len => Frame_Size (FL));
                     Pos := Pos + Item_Overhead + Natural (FL);
                  end;
               end loop;
               if Pos /= Len then
                  return;
               end if;
               pragma Assert
                 (for all T2 in 1 .. Item_Count (NB) =>
                    Items (T2).Key.K <= 4
                    and then In_Window (Items (T2).Key, Lo, Hi));
               pragma Assert
                 (for all T2 in 2 .. Item_Count (NB) =>
                    Key_Lt (Items (T2 - 1).Key, Items (T2).Key));
               Lemma_Items_OK ((if Tag = Tag_Elements then M_Elements else M_Have),
                               Natural (G), Lo, Hi, Item_Count (NB), Items);
               M := (Kind   => (if Tag = Tag_Elements then M_Elements else M_Have),
                     G      => Natural (G),
                     Lo     => Lo,
                     Hi     => Hi,
                     Count  => 0,
                     Fp     => [others => 0],
                     N      => Item_Count (NB),
                     Items  => Items);
               pragma Assert (Msg_OK (M));
               OK := True;
            end;
         end if;
      end;
   end Decode_Raw;

   function Decode_Of (Input : Byte_Array) return Decoding is
      D : Decoding;
   begin
      Decode_Raw (Input, D.M, D.OK);
      return D;
   end Decode_Of;

   procedure Decode
     (Input  : Byte_Array;
      M      : out Message;
      OK     : out Boolean)
   is
      D : constant Decoding := Decode_Of (Input);
   begin
      M := D.M;
      OK := D.OK;
   end Decode;

   ----------------------------------------------------------------------
   --  Session
   ----------------------------------------------------------------------

   procedure Start
     (Sess    : out Session;
      As      : Role;
      NS      : Id128;
      Voids   : Rv_Array;
      N_Voids : Rv_Count;
      Buf     : out Msg_Buffer;
      Len     : out Msg_Length)
   is
   begin
      Sess := (R               => As,
               P               => Await_Open,
               NS              => NS,
               Aborted         => False,
               Hello_Sent      => False,
               Peer_Hello_Seen => False,
               Auth_Root_Seen  => False,
               Our_N           => 0,
               Our_Digest      => (others => 0),
               Peer_Auth       => 0,
               Peer_Data       => 0,
               Peer_Digest     => (others => 0),
               Msgs            => 0,
               Budget          => Pre_Gate_Budget,
               Pending         => 0,
               Ranges          => 0,
               Shipped         => 0);
      Encode_Open ((Proto => Proto_Version, NS => NS, N_RV => N_Voids, RV => Voids),
                   Buf, Len);
   end Start;

   --  The two HELLOs have passed. If the digests are equal, the session
   --  ends. If not, the phase is Auth, and the initiator opens the
   --  authorization root.
   procedure Exchange_Done (Sess : in out Session; S : Snapshot; O : out Outbox) with
     Global => null,
     Pre  => Valid (S)
             and then Sess.P = Gate and then Sess.Hello_Sent
             and then Sess.Peer_Hello_Seen and then Sess.Msgs <= Pre_Gate_Budget
             and then not Sess.Aborted and then not Sess.Auth_Root_Seen
             and then Sess.Pending = 0,
     Post => After_Hellos (S, Sess, O) and then Session_OK (Sess)
             and then Outbox_OK (S, O)
             and then Sess = (Sess'Old with delta
                                P              => Sess.P,
                                Budget         => Sess.Budget,
                                Pending        => Sess.Pending,
                                Auth_Root_Seen => Sess.Auth_Root_Seen)
   is
   begin
      O := Empty_Box;
      Sess.Budget := Msg_Budget (Sess.Our_N, Peer_Claim (Sess));
      if Sess.Our_Digest = Sess.Peer_Digest then
         Sess.P := Done;
      elsif Sess.R = Initiator then
         declare
            W : constant Span := Window (S, Min_Key, Data_Lo);
         begin
            O.N := 1;
            O.P (1) := (Kind  => P_Range,
                        Lo    => Min_Key,
                        Hi    => Data_Lo,
                        First => W.First,
                        Last  => W.Last,
                        N     => 0,
                        Items => [others => 1]);
            pragma Assert (Plan_OK (S, O.P (1)));
         end;
         Sess.Pending := Unit;
         Sess.Auth_Root_Seen := True;
         Sess.P := Auth;
      else
         Sess.P := Auth;
      end if;
   end Exchange_Done;

   procedure Admit
     (Sess    : in out Session;
      S       : Snapshot;
      Cred    : Byte_Array;
      Buf     : out Msg_Buffer;
      Len     : out Msg_Length;
      Out_Box : out Outbox)
   is
      WA : constant Span := Window (S, Min_Key, Data_Lo);
      WD : constant Span := Window (S, Data_Lo, Max_Key);
      Fp : constant Hash256 := Range_Fp (S, 1, Count (S));
   begin
      Out_Box := Empty_Box;
      Encode_Hello (Word (WA.Last + 1 - WA.First), Word (WD.Last + 1 - WD.First),
                    Fp, Cred, Buf, Len);
      Sess.Hello_Sent := True;
      Sess.Our_N := Count (S);
      Sess.Our_Digest := Kome.Keys.To_Key256 (Fp);
      if Sess.Peer_Hello_Seen then
         Exchange_Done (Sess, S, Out_Box);
      end if;
   end Admit;

   procedure Next_Phase
     (Sess    : in out Session;
      S       : Snapshot;
      Out_Box : out Outbox)
   is
      W : constant Span := Window (S, Data_Lo, Max_Key);
   begin
      Out_Box := Empty_Box;
      Out_Box.N := 1;
      Out_Box.P (1) := (Kind  => P_Range,
                        Lo    => Data_Lo,
                        Hi    => Max_Key,
                        First => W.First,
                        Last  => W.Last,
                        N     => 0,
                        Items => [others => 1]);
      pragma Assert (Plan_OK (S, Out_Box.P (1)));
      Sess.P := Data;
      Sess.Pending := Unit;
   end Next_Phase;

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
   is
      OK   : Boolean;
      Sess0 : constant Session := Sess with Ghost;
   begin
      M := (others => <>);
      Open := (Proto => Proto_Version,
               NS    => (others => 0),
               N_RV  => 0,
               RV    => [others => Zero_Rv]);
      Peer := (N_Auth   => 0,
               N_Data   => 0,
               Digest   => [others => 0],
               Cred_Len => 0,
               Cred     => [others => 0]);
      Out_Box := Empty_Box;
      Got := No_Delivery;

      if Sess.P = Done then
         Result := S_Unexpected;
         pragma Assert (Result = Status_Of (Sess0, S, Input));
         return;
      end if;
      if Input'Last < Input'First then
         Result := S_Malformed;
         pragma Assert (Result = Status_Of (Sess0, S, Input));
         return;
      end if;

      if Input (Input'First) = Tag_Open then
         --  The OPEN, once, first.
         M.Kind := M_Open;
         if Sess.P /= Await_Open then
            Result := S_Unexpected;
            pragma Assert (Result = Status_Of (Sess0, S, Input));
            return;
         end if;
         if Sess.Msgs = Sess.Budget then
            Result := S_Limit;
            pragma Assert (Result = Status_Of (Sess0, S, Input));
            return;
         end if;
         Decode_Open (Input, Open, OK);
         if not OK then
            Result := S_Malformed;
            pragma Assert (Result = Status_Of (Sess0, S, Input));
            return;
         end if;
         if Open.NS /= Sess.NS then
            Sess.P := Done;
            Sess.Aborted := True;
            Result := S_Aborted;
            pragma Assert (Result = Status_Of (Sess0, S, Input));
            pragma Assert (Open_Wire_OK (Input) and then Open_Decoded (Input, Open));
            pragma Assert (Session_OK (Sess));
            return;
         end if;
         Sess.P := Gate;
         Sess.Msgs := Sess.Msgs + 1;
         Result := S_OK;
         pragma Assert (Result = Status_Of (Sess0, S, Input));
         pragma Assert (Open_Wire_OK (Input) and then Open_Decoded (Input, Open));
         pragma Assert (Session_OK (Sess));

      elsif Input (Input'First) = Tag_Hello then
         --  The HELLO, once, in the gate.
         M.Kind := M_Hello;
         if Sess.P /= Gate or else Sess.Peer_Hello_Seen then
            Result := S_Unexpected;
            pragma Assert (Result = Status_Of (Sess0, S, Input));
            return;
         end if;
         if Sess.Msgs = Sess.Budget then
            Result := S_Limit;
            pragma Assert (Result = Status_Of (Sess0, S, Input));
            return;
         end if;
         Decode_Hello (Input, Peer, OK);
         if not OK then
            Result := S_Malformed;
            pragma Assert (Result = Status_Of (Sess0, S, Input));
            return;
         end if;
         Sess.Peer_Hello_Seen := True;
         Sess.Peer_Auth := Claim (Peer.N_Auth);
         Sess.Peer_Data := Claim (Peer.N_Data);
         Sess.Peer_Digest := Kome.Keys.To_Key256 (Peer.Digest);
         Sess.Msgs := Sess.Msgs + 1;
         if Sess.Hello_Sent then
            Exchange_Done (Sess, S, Out_Box);
         end if;
         Result := S_OK;
         pragma Assert (Result = Status_Of (Sess0, S, Input));
         pragma Assert (Hello_Wire_OK (Input) and then Hello_Decoded (Input, Peer));
         pragma Assert (Session_OK (Sess));
         pragma Assert (Outbox_OK (S, Out_Box));
         pragma Assert (if Sess.Hello_Sent then After_Hellos (S, Sess, Out_Box)
                        else Sess.P = Gate and then Out_Box.N = 0
                             and then Sess.Budget = Sess0.Budget);
         pragma Assert (Sess = (Sess0 with delta
                                  Peer_Hello_Seen => True,
                                  Peer_Auth       => Sess.Peer_Auth,
                                  Peer_Data       => Sess.Peer_Data,
                                  Peer_Digest     => Sess.Peer_Digest,
                                  Msgs            => Sess0.Msgs + 1,
                                  P               => Sess.P,
                                  Budget          => Sess.Budget,
                                  Pending         => Sess.Pending,
                                  Auth_Root_Seen  => Sess.Auth_Root_Seen));

      else
         --  RANGE, ELEMENTS, HAVE: only in Auth and Data.
         if Sess.P not in Auth | Data then
            Result := S_Unexpected;
            pragma Assert (Result = Status_Of (Sess0, S, Input));
            return;
         end if;
         if Sess.Msgs = Sess.Budget then
            Result := S_Limit;
            pragma Assert (Result = Status_Of (Sess0, S, Input));
            return;
         end if;
         declare
            D  : constant Decoding := Decode_Of (Input);
            Wt : Pending_Units := 0;
         begin
            if not D.OK then
               Result := S_Malformed;
               pragma Assert (Result = Status_Of (Sess0, S, Input));
               return;
            end if;
            M := D.M;
            --  g = 0 is a root RANGE: only the expected root, with exact
            --  bounds (D14). Every other message answers an open
            --  obligation of ours.
            if not Root_Or_Owed (Sess, M) then
               Result := S_Unexpected;
               pragma Assert (Result = Status_Of (Sess0, S, Input));
               return;
            end if;
            if M.G /= 0 then
               Wt := Weight (M.G);
            end if;
            declare
               R  : constant Reply := Reply_Of (S, M);
            begin
               if not Within_Budgets (Sess, S, M, R.Box) then
                  Result := S_Limit;
                  pragma Assert (Result = Status_Of (Sess0, S, Input));
                  return;
               end if;
               Out_Box := R.Box;
               Got := R.Got;
               Sess.Ranges := Sess.Ranges + Num_Ranges (Out_Box);
               Sess.Shipped := Sess.Shipped + Item_Bytes (S, Out_Box);
               Sess.Pending := Sess.Pending - Wt
                               + Unit * Pending_Units (Obligations (Out_Box));
               Sess.Msgs := Sess.Msgs + 1;
               if M.G = 0 then
                  if Sess.Auth_Root_Seen then
                     Sess.P := Data;          --  (b) the data root
                  end if;
                  Sess.Auth_Root_Seen := True;
               end if;
               if Sess.P = Data and then Sess.Pending = 0 then
                  Sess.P := Done;
               end if;
               Result := S_OK;
               pragma Assert (Status_Of (Sess0, S, Input) = S_OK);
               pragma Assert (Session_OK (Sess));
               pragma Assert (Out_Box = Reply_Of (S, M).Box);
               pragma Assert (Decode_Facts (Input, M, True));
               pragma Assert (Sess.Ranges = Sess0.Ranges + Num_Ranges (Out_Box));
               pragma Assert (Sess.Shipped = Sess0.Shipped + Item_Bytes (S, Out_Box));
               pragma Assert (Sess.Pending =
                                Sess0.Pending
                                - (if M.G = 0 then 0 else Weight (M.G))
                                + Unit * Pending_Units (Obligations (Out_Box)));
               pragma Assert (Sess.Ranges <= Range_Budget (S)
                              and then Sess.Shipped <= Ship_Budget (S));
               pragma Assert (Outbox_OK (S, Out_Box));
               pragma Assert (M = Decode_Of (Input).M);
               pragma Assert (Msg_OK (M) and then Msg_In (M, Input));
               pragma Assert (if M.G = 0 then Root_OK (Sess0, M));
               pragma Assert (Got = Reply_Of (S, M).Got);
               pragma Assert (Delivers (S, M, Got) and then Answers (S, M, Out_Box)
                              and then Shrinks (S, M, Out_Box));
               pragma Assert (Sess.Auth_Root_Seen = (Sess0.Auth_Root_Seen or else M.G = 0));
               pragma Assert (Sess.P =
                                (if Sess0.P = Data
                                   or else (M.G = 0 and then Sess0.Auth_Root_Seen)
                                 then (if Sess.Pending = 0 then Done else Data)
                                 else Auth));
               pragma Assert (Sess = (Sess0 with delta
                                        Msgs           => Sess0.Msgs + 1,
                                        P              => Sess.P,
                                        Pending        => Sess.Pending,
                                        Ranges         => Sess.Ranges,
                                        Shipped        => Sess.Shipped,
                                        Auth_Root_Seen => Sess.Auth_Root_Seen));
            end;
         end;
      end if;
   end Receive;

end Kome.Reconcile;
