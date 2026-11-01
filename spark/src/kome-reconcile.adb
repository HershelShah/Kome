pragma Ada_2022;
package body Kome.Reconcile with SPARK_Mode is

   --  Proof style (CONVENTIONS.md): assertions go through the public view
   --  (Count, Key, Frame_Len) and every quantified fact the provers need
   --  at a point is asserted there, instance by instance where an
   --  ordering lemma is involved.

   ----------------------------------------------------------------------
   --  Order lemmas. Key_Lt is a quantifier-free chain; each law is proved
   --  by unfolding it.
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
      if K.K > 3 then
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
         --  Every key held is below K: the last one is, and the others
         --  are below the last one (pairwise sorted).
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
         pragma Assert (for all J in 1 .. N => S.Kinds (J) <= 3);
         pragma Assert (Key (S, N) = K);
         pragma Assert (for all J in 1 .. N - 1 => Key_Lt (Key (S, J), Key (S, N)));
         pragma Assert
           (for all I in 1 .. N =>
              (for all J in I + 1 .. N => Key_Lt (Key (S, I), Key (S, J))));
         pragma Assert (Valid (S));
      end;
      Result := Snap_OK;
   end Append;

   ----------------------------------------------------------------------
   --  Windows
   ----------------------------------------------------------------------

   function Window (S : Snapshot; Lo, Hi : Elem_Key) return Span is
      N : constant Elem_Count := S.N;
      F : Lo_Bound := N + 1;
      L : Elem_Count;

      --  Everything from F on is at or above Lo.
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

      --  Everything after L is at or above Hi.
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

      --  The bounds lie inside [Lo, Hi].
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

   --  The root range [Min_Key, Max_Key) holds every element.
   procedure Lemma_Root (S : Snapshot) with
     Ghost, Global => null,
     Pre  => Valid (S),
     Post => Covers (S, Min_Key, Max_Key, 1, Count (S))
   is
   begin
      for K in 1 .. Count (S) loop
         pragma Assert (Key (S, K).K <= 3);
         pragma Assert (In_Window (Key (S, K), Min_Key, Max_Key));
         pragma Loop_Invariant
           (for all K2 in 1 .. K => In_Window (Key (S, K2), Min_Key, Max_Key));
      end loop;
   end Lemma_Root;

   ----------------------------------------------------------------------
   --  Plans and outboxes
   ----------------------------------------------------------------------

   procedure Lemma_Outbox_OK (S : Snapshot; O : Outbox; T : Positive) is null;

   Empty_Plan : constant Plan := (others => <>);
   Empty_Box  : constant Outbox :=
     (Hello => False, Reply => False, N => 0, P => [others => Empty_Plan]);
   Reply_Box  : constant Outbox :=
     (Hello => False, Reply => True, N => 0, P => [others => Empty_Plan]);

   function Num_Ranges (O : Outbox) return Out_Count is
      C : Out_Count := 0;
   begin
      for T in 1 .. O.N loop
         pragma Loop_Invariant (C <= T - 1);
         if O.P (T).Kind = P_Range then
            C := C + 1;
         end if;
      end loop;
      return C;
   end Num_Ranges;

   function Obligations (O : Outbox) return Out_Count is
      C : Out_Count := 0;
   begin
      for T in 1 .. O.N loop
         pragma Loop_Invariant (C <= T - 1);
         if O.P (T).Kind /= P_Have then
            C := C + 1;
         end if;
      end loop;
      return C;
   end Obligations;

   function Item_Bytes (S : Snapshot; O : Outbox) return Byte_Total is
      Sum : Byte_Total := 0;
   begin
      for T in 1 .. O.N loop
         pragma Loop_Invariant (Sum <= Byte_Total (T - 1) * Max_Message_Len);
         if O.P (T).Kind /= P_Range then
            pragma Assert (Plan_OK (S, O.P (T)));
            Sum := Sum + Byte_Total (Plan_Len (S, O.P (T)) - Elems_Fixed);
         end if;
      end loop;
      return Sum;
   end Item_Bytes;

   --  Split [Lo, Hi), holding our elements I .. J (more than
   --  Ship_Threshold of them), into min (Split_Fanout, n) children of
   --  n / 16 or n / 16 + 1 elements. Each child is [Child_Lo, Child_Hi)
   --  over a run B .. E; the runs partition I .. J, so the children tile
   --  [Lo, Hi). The first run is short of J and every later one starts
   --  after I, so each child holds strictly fewer of our elements than
   --  the parent. (The last child takes whatever is left, which with
   --  these sizes is exactly its share; the proof does not need that.)
   procedure Split
     (S : Snapshot; Lo, Hi : Elem_Key; I, J : Elem_Index; O : out Outbox)
   with
     Global => null,
     Pre  => Valid (S) and then Key_Lt (Lo, Hi)
             and then I <= J and then J <= Count (S)
             and then Covers (S, Lo, Hi, I, J)
             and then J + 1 - I > Ship_Threshold,
     Post => Outbox_OK (S, O)
       and then O.Reply and then not O.Hello
       and then Tiles (O, Lo, Hi)
       and then (for all T in 1 .. O.N =>
                   O.P (T).Kind = P_Range
                   and then Key_Le (Lo, O.P (T).Lo)
                   and then Key_Le (O.P (T).Hi, Hi)
                   and then O.P (T).First >= I
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
         pragma Loop_Invariant (O.N = T - 1 and then O.Reply and then not O.Hello);
         pragma Loop_Invariant (I <= B and then B <= J);
         pragma Loop_Invariant (if T > 1 then B > I else B = I);
         pragma Loop_Invariant
           (for all T2 in 1 .. T - 1 =>
              Plan_OK (S, O.P (T2))
              and then O.P (T2).Kind = P_Range
              and then Key_Le (Lo, O.P (T2).Lo)
              and then Key_Le (O.P (T2).Hi, Hi)
              and then O.P (T2).First >= I
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
   end Split;

   --  Ship our elements I .. J (at most Ship_Threshold) as ELEMENTS: one
   --  message if they fit, else one per element over a sub-range holding
   --  it alone (each fits: Frame_Ship_Max).
   procedure Ship
     (S : Snapshot; Lo, Hi : Elem_Key; I : Lo_Bound; J : Elem_Count; O : out Outbox)
   with
     Global => null,
     Pre  => Valid (S) and then Key_Lt (Lo, Hi)
             and then I <= J + 1 and then J <= Count (S)
             and then Covers (S, Lo, Hi, I, J)
             and then J + 1 - I <= Ship_Threshold,
     Post => Outbox_OK (S, O)
       and then O.Reply and then not O.Hello
       and then Tiles (O, Lo, Hi)
       and then (for all T in 1 .. O.N => O.P (T).Kind = P_Elements)
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
      else
         pragma Assert (I <= J);
         for K in I .. J loop
            pragma Loop_Invariant (O.N = K - I and then O.Reply and then not O.Hello);
            pragma Loop_Invariant
              (for all T2 in 1 .. O.N =>
                 Plan_OK (S, O.P (T2)) and then O.P (T2).Kind = P_Elements);
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
      end if;
   end Ship;

   --  Our elements I .. J (at most Ship_Threshold) that M does not list
   --  go back as HAVE: one message if they fit (an empty HAVE if there
   --  are none), else one per element. Exactly those (Have_Exact).
   procedure Have_Back
     (S : Snapshot; M : Message; I : Lo_Bound; J : Elem_Count; O : out Outbox)
   with
     Global => null,
     Pre  => Valid (S) and then Msg_OK (M)
             and then I <= J + 1 and then J <= Count (S)
             and then Covers (S, M.Lo, M.Hi, I, J)
             and then J + 1 - I <= Ship_Threshold,
     Post => Outbox_OK (S, O)
       and then O.N >= 1 and then O.Reply and then not O.Hello
       and then Have_Exact (S, M, O)
   is
      L   : Index_List := [others => 1];
      C   : Item_Count := 0;
      --  Pos (K - I + 1): where our element K went in L, if it did.
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
      --  Outside I .. J nothing of ours is in the range.
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
            pragma Loop_Invariant (O.N = T - 1 and then O.Reply and then not O.Hello);
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

   --  The items of M we do not hold, exactly. Ours in [M.Lo, M.Hi) are
   --  I .. J, and every item lies in that range, so a scan of I .. J
   --  decides it.
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

   procedure Respond
     (S       : Snapshot;
      M       : Message;
      Out_Box : out Outbox;
      Got     : out Delivery)
   is
      W : constant Span := Window (S, M.Lo, M.Hi);
      I : constant Lo_Bound := W.First;
      J : constant Elem_Count := W.Last;
      N : constant Elem_Count := J + 1 - I;

      --  The measure of each child, by its cover.
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

   begin
      Out_Box := Empty_Box;
      Got := No_Delivery;
      pragma Assert (N = My_Count (S, M.Lo, M.Hi));

      case M.Kind is
         when M_Hello =>
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
            elsif N <= Ship_Threshold then
               pragma Assert (not Confirms (S, M));
               Ship (S, M.Lo, M.Hi, I, J, Out_Box);
            else
               pragma Assert (not Confirms (S, M));
               Split (S, M.Lo, M.Hi, I, J, Out_Box);
               Measure;
            end if;

         when M_Elements =>
            Deliver (S, M, I, J, Got);
            if N <= Ship_Threshold then
               Have_Back (S, M, I, J, Out_Box);
            else
               Split (S, M.Lo, M.Hi, I, J, Out_Box);
               Measure;
            end if;

         when M_Have =>
            Deliver (S, M, I, J, Got);
      end case;
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

   --  N keys written at Rel survive a change that leaves their bytes.
   procedure Lemma_Keys_Kept
     (A, B : Msg_Buffer; Rel : Natural; W : Writer_List; N : Natural)
   with
     Ghost, Global => null,
     Pre  => N <= W'Length and then N <= Writers_Max + Roots_Ever_Max
             and then Rel <= Max_Message_Len and then 32 * N <= Max_Message_Len - Rel
             and then (for all Y in Rel .. Rel + 32 * N - 1 => A (Y) = B (Y))
             and then (for all J in 1 .. N => Wire_Key_At (B, Rel, J) = W (W'First + (J - 1))),
     Post => (for all J in 1 .. N => Wire_Key_At (A, Rel, J) = W (W'First + (J - 1)))
   is
   begin
      for J in 1 .. N loop
         Lemma_Same_Key256 (A, B, Rel + 32 * (J - 1));
         pragma Assert (Wire_Key_At (A, Rel, J) = Wire_Key_At (B, Rel, J));
         pragma Assert (Wire_Key_At (B, Rel, J) = W (W'First + (J - 1)));
         pragma Loop_Invariant
           (for all J2 in 1 .. J => Wire_Key_At (A, Rel, J2) = W (W'First + (J2 - 1)));
      end loop;
   end Lemma_Keys_Kept;

   --  The 48-bit ceiling as Encode_Hello writes it.
   procedure Lemma_U48 (B : Byte_Array; P : Natural; C : U48) with
     Ghost, Global => null,
     Pre  => P >= B'First and then P <= B'Last and then B'Last - P >= 5
             and then U48 (B (P)) = C / 2 ** 32 / 256
             and then U48 (B (P + 1)) = C / 2 ** 32 mod 256
             and then U48 (Wire_U32 (B, P + 2)) = C mod 2 ** 32,
     Post => Wire_U48 (B, P) = C
   is
      Hi : constant U48 := C / 2 ** 32;
   begin
      pragma Assert (Hi <= 65_535);
      pragma Assert (Hi / 256 * 256 + Hi mod 256 = Hi);
      pragma Assert (U48 (B (P)) * 256 + U48 (B (P + 1)) = Hi);
      pragma Assert (Hi * 2 ** 32 + C mod 2 ** 32 = C);
   end Lemma_U48;

   ----------------------------------------------------------------------
   --  Wire helpers. Big-endian, through Kome.Keys' word lanes. Each
   --  writer states what it wrote (read back with the Wire_ functions)
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

   --  Tag, group size and range of a RANGE / ELEMENTS / HAVE; the body
   --  (from Elems_O_N on) is untouched.
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
      --  The body first, then the head, which leaves the body alone.
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

   --  Keys W at Buf (Rel ..), 32 bytes each; nothing else changes.
   procedure Write_Keys (Buf : in out Msg_Buffer; Rel : Natural; W : Writer_List) with
     Global => null,
     Pre  => W'Length <= Writers_Max + Roots_Ever_Max
             and then Rel <= Max_Message_Len - 32 * W'Length,
     Post => (for all I in 1 .. W'Length => Wire_Key_At (Buf, Rel, I) = W (W'First + (I - 1)))
             and then (for all Y in Buf'Range =>
                         (if Y < Rel or else Y >= Rel + 32 * W'Length
                          then Buf (Y) = Buf'Old (Y)))
   is
      N : constant Natural := W'Length;
   begin
      for I in 1 .. N loop
         pragma Loop_Invariant
           (for all J in 1 .. I - 1 => Wire_Key_At (Buf, Rel, J) = W (W'First + (J - 1)));
         pragma Loop_Invariant
           (for all Y in Buf'Range =>
              (if Y < Rel or else Y >= Rel + 32 * (I - 1)
               then Buf (Y) = Buf'Loop_Entry (Y)));
         declare
            Before : constant Msg_Buffer := Buf with Ghost;
         begin
            Put_Key256 (Buf, Rel + 32 * (I - 1), W (W'First + (I - 1)));
            pragma Assert (Wire_Key_At (Buf, Rel, I) = W (W'First + (I - 1)));
            pragma Assert
              (for all Y in Rel .. Rel + 32 * (I - 1) - 1 => Buf (Y) = Before (Y));
            Lemma_Keys_Kept (Buf, Before, Rel, W, I - 1);
         end;
      end loop;
   end Write_Keys;

   procedure Encode_Hello
     (R     : Register_File;
      F_Cnt : Elem_Count;
      W     : Writer_List;
      Roots : Writer_List;
      Buf   : out Msg_Buffer;
      Len   : out Msg_Length)
   is
      C  : constant U48 := Ceil (R);
      Hi : constant U48 := C / 2 ** 32;
      NW : constant Natural := W'Length;
      NR : constant Natural := Roots'Length;
   begin
      Buf := [others => 0];
      --  The header first; the key lists after it leave it alone.
      Buf (0) := Tag_Hello;
      Buf (1) := Byte (Hi / 256);
      Buf (2) := Byte (Hi mod 256);
      Put_Word (Buf, 3, Word (C mod 2 ** 32));
      Put_Word (Buf, Hello_O_FCnt, Word (F_Cnt));
      Buf (Hello_O_N)     := Byte (NW / 256);
      Buf (Hello_O_N + 1) := Byte (NW mod 256);
      Buf (Hello_O_R)     := Byte (NR / 256);
      Buf (Hello_O_R + 1) := Byte (NR mod 256);
      pragma Assert (Wire_U32 (Buf, 3) = Word (C mod 2 ** 32));
      pragma Assert (Wire_U32 (Buf, Hello_O_FCnt) = Word (F_Cnt));
      pragma Assert (Wire_U16 (Buf, Hello_O_N) = NW);
      pragma Assert (Wire_U16 (Buf, Hello_O_R) = NR);
      pragma Assert (U48 (Buf (1)) = C / 2 ** 32 / 256);
      pragma Assert (U48 (Buf (2)) = C / 2 ** 32 mod 256);

      declare
         Head : constant Msg_Buffer := Buf with Ghost;
      begin
         Write_Keys (Buf, Hello_Fixed, W);
         declare
            Mid : constant Msg_Buffer := Buf with Ghost;
         begin
            Write_Keys (Buf, Hello_Fixed + 32 * NW, Roots);
            pragma Assert
              (for all Y in Hello_Fixed .. Hello_Fixed + 32 * NW - 1 => Buf (Y) = Mid (Y));
            Lemma_Keys_Kept (Buf, Mid, Hello_Fixed, W, NW);
         end;
         pragma Assert (for all Y in 0 .. Hello_Fixed - 1 => Buf (Y) = Head (Y));
         pragma Assert (Buf (0) = Tag_Hello);
         pragma Assert (Wire_U32 (Buf, 3) = Wire_U32 (Head, 3));
         pragma Assert (Wire_U32 (Buf, Hello_O_FCnt) = Wire_U32 (Head, Hello_O_FCnt));
         pragma Assert (Wire_U16 (Buf, Hello_O_N) = Wire_U16 (Head, Hello_O_N));
         pragma Assert (Wire_U16 (Buf, Hello_O_R) = Wire_U16 (Head, Hello_O_R));
         pragma Assert (Buf (1) = Head (1) and then Buf (2) = Head (2));
      end;
      Lemma_U48 (Buf, Hello_O_Ceil, C);
      Len := Hello_Fixed + 32 * (NW + NR);
   end Encode_Hello;

   ----------------------------------------------------------------------
   --  Decoding. Total over all byte strings; never reads out of bounds.
   ----------------------------------------------------------------------

   procedure Decode
     (Input  : Byte_Array;
      M      : out Message;
      OK     : out Boolean)
   is
   begin
      M := (others => <>);
      OK := False;
      --  Total over every input: no length is computed before it is
      --  known to be at most Max_Message_Len.
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
                     Items  => [others => (Key => Min_Key, Off => 0, Len => 1)],
                     W_Full => False);
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
                       Items (T2).Key.K <= 3
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
                       or else K.K > 3
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
               M := (Kind   => (if Tag = Tag_Elements then M_Elements else M_Have),
                     G      => Natural (G),
                     Lo     => Lo,
                     Hi     => Hi,
                     Count  => 0,
                     Fp     => [others => 0],
                     N      => Item_Count (NB),
                     Items  => Items,
                     W_Full => False);
               OK := True;
            end;
         end if;
      end;
   end Decode;

   --  One descent at I is enough to fail Wire_Ascending.
   procedure Lemma_Not_Ascending (B : Byte_Array; Rel, N, I : Natural) with
     Ghost, Global => null,
     Pre  => N <= Writers_Max + Roots_Ever_Max and then Rel <= Max_Message_Len
             and then B'Last >= B'First and then B'Last - B'First >= Rel + 32 * N - 1
             and then I >= 2 and then I <= N
             and then not Lt (Wire_Key_At (B, Rel, I - 1), Wire_Key_At (B, Rel, I)),
     Post => not Wire_Ascending (B, Rel, N)
   is
   begin
      null;
   end Lemma_Not_Ascending;

   --  Read N keys at Input (Input'First + Rel ..) into L (1 .. N); OK iff
   --  they are strictly ascending.
   procedure Read_Keys
     (Input : Byte_Array; Rel, N : Natural; L : in out Writer_List; OK : out Boolean)
   with
     Global => null,
     Pre  => L'First = 1 and then N <= L'Length
             and then N <= Writers_Max + Roots_Ever_Max and then Rel <= Max_Message_Len
             and then (N = 0 or else (Input'Last >= Input'First
                                      and then Input'Last - Input'First >= Rel + 32 * N - 1)),
     Post => OK = Wire_Ascending (Input, Rel, N)
             and then (if OK then
                         (for all I in 1 .. N => L (I) = Wire_Key_At (Input, Rel, I))
                         and then Ascending (L (1 .. N)))
   is
   begin
      OK := True;
      for I in 1 .. N loop
         L (I) := Wire_Key_At (Input, Rel, I);
         if I > 1 and then not Lt (L (I - 1), L (I)) then
            pragma Assert (L (I - 1) = Wire_Key_At (Input, Rel, I - 1));
            Lemma_Not_Ascending (Input, Rel, N, I);
            OK := False;
            return;
         end if;
         pragma Loop_Invariant
           (for all J in 1 .. I => L (J) = Wire_Key_At (Input, Rel, J));
         pragma Loop_Invariant
           (for all J in 2 .. I => Lt (Wire_Key_At (Input, Rel, J - 1), Wire_Key_At (Input, Rel, J)));
      end loop;
      pragma Assert (Wire_Ascending (Input, Rel, N));
      pragma Assert (for all J in 2 .. N => Lt (L (J - 1), L (J)));
      pragma Assert (Ascending (L (1 .. N)));
   end Read_Keys;

   procedure Decode_Hello
     (Input : Byte_Array;
      H     : out Hello;
      OK    : out Boolean)
   is
   begin
      H := (others => <>);
      OK := False;
      if Input'Last < Input'First
        or else Input'Last - Input'First < Hello_Fixed - 1
        or else Input'Last - Input'First >= Max_Message_Len
      then
         pragma Assert (not Hello_Ok_Header (Input));
         return;
      end if;
      declare
         F   : constant Natural := Input'First;
         FC  : constant Word := Wire_U32 (Input, F + Hello_O_FCnt);
         NW  : constant Natural := Wire_U16 (Input, F + Hello_O_N);
         NR  : constant Natural := Wire_U16 (Input, F + Hello_O_R);
         Ws  : Writer_List (1 .. Writers_Max) := [others => (others => 0)];
         Rs  : Writer_List (1 .. Roots_Ever_Max) := [others => (others => 0)];
         OK1 : Boolean;
         OK2 : Boolean;
      begin
         if Input (F) /= Tag_Hello
           or else FC > Kome.Digest.Elem_Max
           or else NW > Writers_Max
           or else NR > Roots_Ever_Max
           or else Input'Last - F /= Hello_Fixed - 1 + 32 * (NW + NR)
         then
            pragma Assert (not Hello_Ok_Header (Input));
            return;
         end if;
         pragma Assert (Hello_Ok_Header (Input));

         Read_Keys (Input, Hello_Fixed, NW, Ws, OK1);
         if not OK1 then
            return;
         end if;
         Read_Keys (Input, Hello_Fixed + 32 * NW, NR, Rs, OK2);
         if not OK2 then
            return;
         end if;
         pragma Assert (Hello_Wire_OK (Input));

         H := (Ceil  => Wire_U48 (Input, F + Hello_O_Ceil),
               F_Cnt => Elem_Count (FC),
               N     => Writer_Count (NW),
               W     => Ws,
               R     => NR,
               Roots => Rs);
         pragma Assert (for all I in 1 .. NW => H.W (I) = Ws (I));
         pragma Assert
           (for all I in 1 .. NW => H.W (I) = Wire_Key_At (Input, Hello_Fixed, I));
         pragma Assert (H.W (1 .. NW) = Ws (1 .. NW));
         pragma Assert (H.Roots (1 .. NR) = Rs (1 .. NR));
         OK := True;
      end;
   end Decode_Hello;

   ----------------------------------------------------------------------
   --  The HELLO join (DESIGN.md §4).
   ----------------------------------------------------------------------

   procedure Join (R : in out Register_File; H : Hello; Result : out Join_Status) is
      Old     : constant Register_File := R;
      Dropped : Boolean := False;

      --  Keys joined before step I survive step I (Add_Writer extends W).
      procedure Carry (Before, After : Register_File; I : Natural) with
        Ghost, Global => (Input => H),
        Pre  => Extends (Before, After)
                and then I >= 1 and then I <= Natural (H.N)
                and then (for all J in 1 .. I - 1 => In_W (Before, H.W (J))),
        Post => (for all J in 1 .. I - 1 => In_W (After, H.W (J)))
      is
      begin
         for J in 1 .. I - 1 loop
            Lemma_Extends_In_W (Before, After, H.W (J));
            pragma Loop_Invariant (for all J2 in 1 .. J => In_W (After, H.W (J2)));
         end loop;
      end Carry;

      --  A key Before lacks, Old lacks too (Old's W is inside Before's).
      procedure Not_In_Old (Before : Register_File; X : Key256) with
        Ghost, Global => (Input => Old),
        Pre  => Extends (Old, Before) and then not In_W (Before, X),
        Post => not In_W (Old, X)
      is
      begin
         if In_W (Old, X) then
            Lemma_Extends_In_W (Old, Before, X);
         end if;
      end Not_In_Old;

   begin
      Raise_Ceiling (R, H.Ceil);
      pragma Assert (Extends (Old, R));
      for I in 1 .. Natural (H.N) loop
         pragma Loop_Invariant (Ceil (R) = U48'Max (Ceil (Old), H.Ceil));
         pragma Loop_Invariant (Extends (Old, R));
         pragma Loop_Invariant
           (Kome.Registers.Count (R) >= Kome.Registers.Count (Old));
         pragma Loop_Invariant
           (Natural (Kome.Registers.Count (R))
              <= Natural (Kome.Registers.Count (Old)) + Fresh_Upto (Old, H, I - 1));
         pragma Loop_Invariant
           (if Dropped then Kome.Registers.Count (R) = Writers_Max
            else (for all J in 1 .. I - 1 => In_W (R, H.W (J))));
         declare
            Before : constant Register_File := R with Ghost;
            Was    : constant Boolean := In_W (R, H.W (I));
            Full   : constant Boolean := Kome.Registers.Count (R) = Writers_Max;
            Cnt    : constant Writer_Count := Kome.Registers.Count (R);
         begin
            Add_Writer (R, H.W (I));
            --  The bound Kome.Registers.Add_Writer does not state: at most
            --  one new writer, none if the key was already there. With its
            --  current body this never fails; if it did, nothing changes.
            if Natural (Kome.Registers.Count (R)) > Natural (Cnt) + (if Was then 0 else 1) then
               R := Old;
               Result := J_Fault;
               return;
            end if;
            Lemma_Extends_Trans (Old, Before, R);
            if not Was then
               Not_In_Old (Before, H.W (I));
            end if;
            pragma Assert
              (Fresh_Upto (Old, H, I)
                 = Fresh_Upto (Old, H, I - 1) + (if In_W (Old, H.W (I)) then 0 else 1));
            if not Dropped then
               Carry (Before, R, I);
               if Was then
                  Lemma_Extends_In_W (Before, R, H.W (I));
               elsif Full then
                  Dropped := True;
               end if;
            end if;
         end;
      end loop;
      Result := (if Dropped then J_W_Full else J_OK);
   end Join;

   ----------------------------------------------------------------------
   --  Session
   ----------------------------------------------------------------------

   procedure Start (Sess : out Session; As : Role; Out_Box : out Outbox) is
   begin
      Out_Box := Empty_Box;
      Sess := (R       => As,
               P       => (if As = Initiator then Hello_Sent else Await_Hello),
               Msgs    => 0,
               Budget  => 1,
               Pending => 0,
               Ranges  => 0,
               Shipped => 0);
      Out_Box.Hello := As = Initiator;
   end Start;

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
   is
   begin
      M := (others => <>);
      Peer := (others => <>);
      Out_Box := Empty_Box;
      Got := No_Delivery;

      if Sess.Msgs = Sess.Budget then
         Result := S_Limit;
         return;
      end if;
      if Input'Last < Input'First then
         Result := S_Malformed;
         return;
      end if;

      if Input (Input'First) = Tag_Hello then
         if Sess.P = Ready then
            Result := S_Unexpected;
            return;
         end if;
         declare
            OK : Boolean;
            JR : Join_Status := J_OK;
         begin
            Decode_Hello (Input, Peer, OK);
            if not OK then
               Result := S_Malformed;
               return;
            end if;
            if Join_Regs then
               Join (R, Peer, JR);
               if JR = J_Fault then
                  Result := S_Fault;
                  return;
               end if;
            end if;
            M.Kind := M_Hello;
            M.W_Full := JR = J_W_Full;
            if Sess.P = Await_Hello then
               Out_Box.Hello := True;
               Sess.Pending := 0;
               Sess.Ranges := 0;
            else
               Lemma_Root (S);
               Out_Box.N := 1;
               Out_Box.P (1) := (Kind  => P_Range,
                                 Lo    => Min_Key,
                                 Hi    => Max_Key,
                                 First => 1,
                                 Last  => Count (S),
                                 N     => 0,
                                 Items => [others => 1]);
               pragma Assert (Plan_OK (S, Out_Box.P (1)));
               Sess.Pending := Unit;
               Sess.Ranges := 1;
            end if;
            Sess.Shipped := 0;
            Sess.Budget := Msg_Budget (Count (S), Peer.F_Cnt);
            Sess.P := Ready;
            Sess.Msgs := Sess.Msgs + 1;
            Result := S_OK;
         end;
      else
         if Sess.P /= Ready then
            Result := S_Unexpected;
            return;
         end if;
         declare
            OK : Boolean;
            Wt : Pending_Units := 0;
         begin
            Decode (Input, M, OK);
            if not OK then
               Result := S_Malformed;
               return;
            end if;
            --  g = 0 is the root RANGE, the responder's first message
            --  after the HELLO; every other message answers an open
            --  obligation of ours.
            if M.G = 0 then
               if Sess.R /= Responder or else Sess.Msgs /= 1 then
                  Result := S_Unexpected;
                  return;
               end if;
            else
               Wt := Weight (M.G);
               if Sess.Pending < Wt then
                  Result := S_Unexpected;
                  return;
               end if;
            end if;
            Respond (S, M, Out_Box, Got);
            declare
               NR : constant Out_Count := Num_Ranges (Out_Box);
               IB : constant Byte_Total := Item_Bytes (S, Out_Box);
               OB : constant Out_Count := Obligations (Out_Box);
            begin
               if Sess.Ranges + NR > Range_Budget (S)
                 or else Sess.Shipped + IB > Ship_Budget (S)
                 or else Sess.Pending - Wt + Unit * Pending_Units (OB) > Pending_Max
               then
                  Out_Box := Empty_Box;
                  Got := No_Delivery;
                  Result := S_Limit;
                  return;
               end if;
               Sess.Ranges := Sess.Ranges + NR;
               Sess.Shipped := Sess.Shipped + IB;
               Sess.Pending := Sess.Pending - Wt + Unit * Pending_Units (OB);
               Sess.Msgs := Sess.Msgs + 1;
               Result := S_OK;
            end;
         end;
      end if;
   end Receive;

end Kome.Reconcile;
