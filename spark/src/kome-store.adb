pragma Ada_2022;
package body Kome.Store with SPARK_Mode is

   --  Proof style (CONVENTIONS.md): the invariant is split into parts over
   --  explicit components (Live, Framed, Sorted, Covered), each step of an
   --  operation re-establishes one part through a small ghost lemma, and
   --  every "some record" is turned into a named index by a ghost witness
   --  function before it is used.

   ---------------------------------------------------------------------------
   --  The invariant's parts (defined by their Posts in the spec).
   ---------------------------------------------------------------------------

   function Live (F : Frontier.State; Hz : Time64; Idx : Entry_Array; N : Held_Count)
     return Boolean is
   begin
      return (for all I in 1 .. N =>
                Holds (F, Idx (I).H) and then not Expired (Idx (I).H, Hz));
   end Live;

   function Framed (Log : Byte_Array; LL : Log_Size; Idx : Entry_Array; N : Held_Count)
     return Boolean is
   begin
      return (for all I in 1 .. N => Frame_OK (Log, LL, Idx (I)));
   end Framed;

   function Sorted (Idx : Entry_Array; N : Held_Count) return Boolean is
   begin
      return (for all I in 1 .. N =>
                (for all J in I + 1 .. N =>
                   End_Of (Idx (I)) <= Idx (J).Off and then Idx (I).H /= Idx (J).H));
   end Sorted;

   function Covered (F : Frontier.State; Hz : Time64; Idx : Entry_Array; N : Held_Count)
     return Boolean is
   begin
      return (for all K in 1 .. Count (F) =>
                Expired (Held (F, K), Hz) or else Has_Entry (Idx, N, Held (F, K)));
   end Covered;

   ---------------------------------------------------------------------------
   --  Ghost witnesses.
   ---------------------------------------------------------------------------

   function Witness (F : Frontier.State; X : Header) return Held_Index with
     Ghost, Global => null,
     Pre  => Holds (F, X),
     Post => Witness'Result <= Count (F) and then Held (F, Witness'Result) = X;

   function Witness (F : Frontier.State; X : Header) return Held_Index is
   begin
      for I in 1 .. Count (F) loop
         if Held (F, I) = X then
            return I;
         end if;
         pragma Loop_Invariant (for all J in 1 .. I => Held (F, J) /= X);
      end loop;
      pragma Assert (False);
      return 1;
   end Witness;

   function Dom_Witness (F : Frontier.State; X : Header) return Held_Index with
     Ghost, Global => null,
     Pre  => Dom (F, X),
     Post => Dom_Witness'Result <= Count (F)
             and then Admitted (F, Held (F, Dom_Witness'Result))
             and then Dominates (Held (F, Dom_Witness'Result), X);

   function Dom_Witness (F : Frontier.State; X : Header) return Held_Index is
   begin
      for I in 1 .. Count (F) loop
         if Admitted (F, Held (F, I)) and then Dominates (Held (F, I), X) then
            return I;
         end if;
         pragma Loop_Invariant
           (for all J in 1 .. I =>
              not (Admitted (F, Held (F, J)) and then Dominates (Held (F, J), X)));
      end loop;
      pragma Assert (False);
      return 1;
   end Dom_Witness;

   function Entry_Witness
     (Idx : Entry_Array; N : Held_Count; X : Header) return Held_Index
   with
     Ghost, Global => null,
     Pre  => Idx'First = 1 and then N <= Idx'Last and then Has_Entry (Idx, N, X),
     Post => Entry_Witness'Result <= N and then Idx (Entry_Witness'Result).H = X;

   function Entry_Witness
     (Idx : Entry_Array; N : Held_Count; X : Header) return Held_Index is
   begin
      for I in 1 .. N loop
         if Idx (I).H = X then
            return I;
         end if;
         pragma Loop_Invariant (for all J in 1 .. I => Idx (J).H /= X);
      end loop;
      pragma Assert (False);
      return 1;
   end Entry_Witness;

   function Same_Witness
     (Idx : Entry_Array; N : Held_Count; Old : Entry_Array; N0 : Held_Count;
      J   : Held_Index) return Held_Index
   with
     Ghost, Global => null,
     Pre  => Idx'First = 1 and then N <= Idx'Last
             and then Old'First = 1 and then N0 <= Old'Last
             and then J <= N
             and then (for some I in 1 .. N0 => Idx (J) = Old (I)),
     Post => Same_Witness'Result <= N0 and then Idx (J) = Old (Same_Witness'Result);

   function Same_Witness
     (Idx : Entry_Array; N : Held_Count; Old : Entry_Array; N0 : Held_Count;
      J   : Held_Index) return Held_Index is
   begin
      for I in 1 .. N0 loop
         if Idx (J) = Old (I) then
            return I;
         end if;
         pragma Loop_Invariant (for all K in 1 .. I => Idx (J) /= Old (K));
      end loop;
      pragma Assert (False);
      return 1;
   end Same_Witness;

   function Bound_Witness
     (Idx : Entry_Array; N : Held_Count; Bnd : Offset_Array; NB : Natural;
      J   : Held_Index) return Positive
   with
     Ghost, Global => null,
     Pre  => Idx'First = 1 and then N <= Idx'Last
             and then Bnd'First = 1 and then NB <= Bnd'Last
             and then J <= N
             and then (for some K in 1 .. NB => Bnd (K) = Idx (J).Off),
     Post => Bound_Witness'Result <= NB and then Bnd (Bound_Witness'Result) = Idx (J).Off;

   function Bound_Witness
     (Idx : Entry_Array; N : Held_Count; Bnd : Offset_Array; NB : Natural;
      J   : Held_Index) return Positive is
   begin
      for K in 1 .. NB loop
         if Bnd (K) = Idx (J).Off then
            return K;
         end if;
         pragma Loop_Invariant (for all K2 in 1 .. K => Bnd (K2) /= Idx (J).Off);
      end loop;
      pragma Assert (False);
      return 1;
   end Bound_Witness;

   ---------------------------------------------------------------------------
   --  Lattice lemmas: what Frontier.Apply's Post implies for one record.
   ---------------------------------------------------------------------------

   --  T4': admission is monotone in the registers.
   procedure Lemma_Admitted_Mono (Old_F, New_F : Frontier.State; R : Header) with
     Ghost, Global => null,
     Pre  => Ceil (Regs (New_F)) >= Ceil (Regs (Old_F))
             and then Extends (Regs (Old_F), Regs (New_F)),
     Post => (if Admitted (Old_F, R) then Admitted (New_F, R));

   procedure Lemma_Admitted_Mono (Old_F, New_F : Frontier.State; R : Header) is
   begin
      if Is_Data (R) and then In_W (Regs (Old_F), Data_Author (R)) then
         Lemma_Extends_In_W (Regs (Old_F), Regs (New_F), Data_Author (R));
      end if;
   end Lemma_Admitted_Mono;

   --  A record held before Apply (R) and not dominated by R is held after:
   --  Apply drops only what R dominates. (If R is not held after, nothing
   --  is dropped at all.)
   procedure Lemma_Survivor (Old_F, New_F : Frontier.State; R, X : Header) with
     Ghost, Global => null,
     Pre  => Is_Frontier (Old_F)
       and then (for all I in 1 .. Count (New_F) =>
                   Holds (Old_F, Held (New_F, I)) or else Held (New_F, I) = R)
       and then (for all I in 1 .. Count (Old_F) =>
                   Holds (New_F, Held (Old_F, I)) or else Dom (New_F, Held (Old_F, I)))
       and then Holds (Old_F, X)
       and then (not Dominates (R, X) or else not Holds (New_F, R)),
     Post => Holds (New_F, X);

   procedure Lemma_Survivor (Old_F, New_F : Frontier.State; R, X : Header) is
      K : constant Held_Index := Witness (Old_F, X);
   begin
      if not Holds (New_F, X) then
         pragma Assert (Holds (New_F, Held (Old_F, K)) or else Dom (New_F, Held (Old_F, K)));
         pragma Assert (Dom (New_F, X));
         declare
            J : constant Held_Index := Dom_Witness (New_F, X);
            Q : constant Header := Held (New_F, J);
         begin
            pragma Assert (Dominates (Q, X));
            if Q = R then
               pragma Assert (Holds (New_F, R));
               pragma Assert (False);
            else
               pragma Assert (Holds (Old_F, Q));
               declare
                  K2 : constant Held_Index := Witness (Old_F, Q);
               begin
                  pragma Assert (Admitted (Old_F, Held (Old_F, K2)));
                  pragma Assert (Dominates (Held (Old_F, K2), Held (Old_F, K)));
                  pragma Assert (Dom (Old_F, Held (Old_F, K)));
                  pragma Assert (False);
               end;
            end if;
         end;
      end if;
   end Lemma_Survivor;

   --  In a frontier, a record that is held or dominated there dominates
   --  nothing held there (T2').
   procedure Lemma_Not_Beaten (F : Frontier.State; R, Y : Header) with
     Ghost, Global => null,
     Pre  => Is_Frontier (F)
             and then Holds (F, Y)
             and then (Holds (F, R) or else Dom (F, R)),
     Post => not Dominates (R, Y);

   procedure Lemma_Not_Beaten (F : Frontier.State; R, Y : Header) is
      KY : constant Held_Index := Witness (F, Y);
   begin
      if Dominates (R, Y) then
         if Holds (F, R) then
            declare
               KR : constant Held_Index := Witness (F, R);
            begin
               pragma Assert (Admitted (F, Held (F, KR)));
               pragma Assert (Dominates (Held (F, KR), Held (F, KY)));
               pragma Assert (Dom (F, Held (F, KY)));
               pragma Assert (False);
            end;
         else
            declare
               J : constant Held_Index := Dom_Witness (F, R);
               Q : constant Header := Held (F, J);
            begin
               Lemma_Dominates_Trans (Y, R, Q);
               pragma Assert (Admitted (F, Held (F, J)));
               pragma Assert (Dominates (Held (F, J), Held (F, KY)));
               pragma Assert (Dom (F, Held (F, KY)));
               pragma Assert (False);
            end;
         end if;
      end if;
   end Lemma_Not_Beaten;

   --  Apply holds nothing new but R, so canonical form is kept.
   procedure Lemma_Canon (Old_F, New_F : Frontier.State; R : Header) with
     Ghost, Global => null,
     Pre  => Canon (Old_F)
       and then Kome.Views.Canonical (R)
       and then (for all I in 1 .. Count (New_F) =>
                   Holds (Old_F, Held (New_F, I)) or else Held (New_F, I) = R),
     Post => Canon (New_F);

   procedure Lemma_Canon (Old_F, New_F : Frontier.State; R : Header) is
   begin
      for K in 1 .. Count (New_F) loop
         if Held (New_F, K) /= R then
            declare
               K2 : constant Held_Index := Witness (Old_F, Held (New_F, K));
            begin
               pragma Assert (Kome.Views.Canonical (Held (Old_F, K2)));
            end;
         end if;
         pragma Loop_Invariant
           (for all K3 in 1 .. K => Kome.Views.Canonical (Held (New_F, K3)));
      end loop;
   end Lemma_Canon;

   ---------------------------------------------------------------------------
   --  Index lemmas.
   ---------------------------------------------------------------------------

   --  Every entry of Idx (1 .. N) is an entry of Old (1 .. N0). Defined by
   --  its Post so that it stays one atom in goals that carry it along.
   function Sub (Idx : Entry_Array; N : Held_Count; Old : Entry_Array; N0 : Held_Count)
     return Boolean
   with Ghost, Global => null,
        Pre  => Idx'First = 1 and then N <= Idx'Last
                and then Old'First = 1 and then N0 <= Old'Last,
        Post => Sub'Result =
                  (for all J in 1 .. N => (for some I in 1 .. N0 => Idx (J) = Old (I)));

   function Sub (Idx : Entry_Array; N : Held_Count; Old : Entry_Array; N0 : Held_Count)
     return Boolean is
   begin
      return (for all J in 1 .. N => (for some I in 1 .. N0 => Idx (J) = Old (I)));
   end Sub;

   procedure Lemma_Framed_Sub
     (Log : Byte_Array; LL : Log_Size;
      Old : Entry_Array; N0 : Held_Count; Idx : Entry_Array; N : Held_Count)
   with
     Ghost, Global => null,
     Pre  => Log'First = 0 and then LL <= Log'Last
             and then Idx'First = 1 and then N <= Idx'Last
             and then Old'First = 1 and then N0 <= Old'Last
             and then Framed (Log, LL, Old, N0)
             and then Sub (Idx, N, Old, N0),
     Post => Framed (Log, LL, Idx, N)
             and then (for all J in 1 .. N => End_Of (Idx (J)) <= LL);

   procedure Lemma_Framed_Sub
     (Log : Byte_Array; LL : Log_Size;
      Old : Entry_Array; N0 : Held_Count; Idx : Entry_Array; N : Held_Count) is
   begin
      pragma Assert (for all J in 1 .. N => (for some I in 1 .. N0 => Idx (J) = Old (I)));
      for J in 1 .. N loop
         declare
            I : constant Held_Index := Same_Witness (Idx, N, Old, N0, J);
         begin
            pragma Assert (Frame_OK (Log, LL, Old (I)));
         end;
         pragma Loop_Invariant
           (for all J2 in 1 .. J =>
              Frame_OK (Log, LL, Idx (J2)) and then End_Of (Idx (J2)) <= LL);
      end loop;
   end Lemma_Framed_Sub;

   --  Appending to the log keeps every entry's frame.
   procedure Lemma_Framed_Grow
     (Log1 : Byte_Array; LL1 : Log_Size; Log2 : Byte_Array; LL2 : Log_Size;
      Idx  : Entry_Array; N : Held_Count)
   with
     Ghost, Global => null,
     Pre  => Log1'First = 0 and then LL1 <= Log1'Last
             and then Log2'First = 0 and then LL2 <= Log2'Last
             and then LL1 <= LL2
             and then (for all P in 0 .. LL1 - 1 => Log2 (P) = Log1 (P))
             and then Idx'First = 1 and then N <= Idx'Last
             and then Framed (Log1, LL1, Idx, N),
     Post => Framed (Log2, LL2, Idx, N);

   procedure Lemma_Framed_Grow
     (Log1 : Byte_Array; LL1 : Log_Size; Log2 : Byte_Array; LL2 : Log_Size;
      Idx  : Entry_Array; N : Held_Count) is
   begin
      for J in 1 .. N loop
         pragma Assert (Frame_OK (Log1, LL1, Idx (J)));
         pragma Assert (Idx (J).Off + Prefix_Len < LL1);
         pragma Assert (Log2 (Idx (J).Off) = Log1 (Idx (J).Off));
         pragma Assert (Log2 (Idx (J).Off + 1) = Log1 (Idx (J).Off + 1));
         pragma Assert (Log2 (Idx (J).Off + 2) = Log1 (Idx (J).Off + 2));
         pragma Assert (Log2 (Idx (J).Off + 3) = Log1 (Idx (J).Off + 3));
         pragma Assert (Log2 (Idx (J).Off + 4) = Log1 (Idx (J).Off + 4));
         pragma Assert (Frame_OK (Log2, LL2, Idx (J)));
         pragma Loop_Invariant (for all J2 in 1 .. J => Frame_OK (Log2, LL2, Idx (J2)));
      end loop;
   end Lemma_Framed_Grow;

   ---------------------------------------------------------------------------
   --  The chain of frames.
   ---------------------------------------------------------------------------

   function Chain (Log : Byte_Array; LL : Log_Size; Bnd : Offset_Array; NB : Natural)
     return Boolean is
   begin
      return (NB = 0) = (LL = 0)
        and then (if NB > 0 then Bnd (1) = 0)
        and then NB <= LL / Min_Frame
        and then (for all K in 1 .. NB =>
                    Frame_At (Log, LL, Bnd (K))
                    and then Bnd (K) + Prefix_Len + Natural (Len_Word (Log, Bnd (K))) =
                               (if K < NB then Bnd (K + 1) else LL));
   end Chain;

   function At_Bounds (Idx : Entry_Array; N : Held_Count; Bnd : Offset_Array; NB : Natural)
     return Boolean is
   begin
      return (for all I in 1 .. N => (for some K in 1 .. NB => Bnd (K) = Idx (I).Off));
   end At_Bounds;

   --  The K-th frame of a chain.
   procedure Lemma_Chain_At
     (Log : Byte_Array; LL : Log_Size; Bnd : Offset_Array; NB : Natural; K : Positive)
   with
     Ghost, Global => null,
     Pre  => Log'First = 0 and then LL <= Log'Last
             and then Bnd'First = 1 and then NB <= Bnd'Last and then K <= NB
             and then Chain (Log, LL, Bnd, NB),
     Post => Frame_At (Log, LL, Bnd (K))
       and then Bnd (K) + Prefix_Len + Natural (Len_Word (Log, Bnd (K))) =
                  (if K < NB then Bnd (K + 1) else LL)
       and then Bnd (K) + Prefix_Len < LL
       and then Len_Word (Log, Bnd (K)) =
                  Kome.Keys.Word_Of (Log (Bnd (K)), Log (Bnd (K) + 1),
                                     Log (Bnd (K) + 2), Log (Bnd (K) + 3));

   procedure Lemma_Chain_At
     (Log : Byte_Array; LL : Log_Size; Bnd : Offset_Array; NB : Natural; K : Positive) is null;

   --  Appending one frame at LL1 extends the chain by it.
   procedure Lemma_Chain_Grow
     (Log1 : Byte_Array; LL1 : Log_Size; Log2 : Byte_Array; LL2 : Log_Size;
      Bnd1 : Offset_Array; NB1 : Natural; Bnd2 : Offset_Array; Len : Frame_Size)
   with
     Ghost, Global => null,
     Pre  => Log1'First = 0 and then LL1 <= Log1'Last
       and then Log2'First = 0 and then LL2 <= Log2'Last
       and then Bnd1'First = 1 and then NB1 <= Bnd1'Last
       and then Bnd2'First = 1 and then NB1 < Bnd2'Last
       and then LL1 <= Log_Max and then LL2 = LL1 + Prefix_Len + Len
       and then (for all P in 0 .. LL1 - 1 => Log2 (P) = Log1 (P))
       and then Len_Word (Log2, LL1) = Word (Len)
       and then Chain (Log1, LL1, Bnd1, NB1)
       and then (for all K in 1 .. NB1 => Bnd2 (K) = Bnd1 (K))
       and then Bnd2 (NB1 + 1) = LL1,
     Post => Chain (Log2, LL2, Bnd2, NB1 + 1);

   procedure Lemma_Chain_Grow
     (Log1 : Byte_Array; LL1 : Log_Size; Log2 : Byte_Array; LL2 : Log_Size;
      Bnd1 : Offset_Array; NB1 : Natural; Bnd2 : Offset_Array; Len : Frame_Size) is
   begin
      for K in 1 .. NB1 loop
         Lemma_Chain_At (Log1, LL1, Bnd1, NB1, K);
         pragma Assert (Bnd1 (K) + 3 < LL1);
         pragma Assert (Log2 (Bnd1 (K)) = Log1 (Bnd1 (K)));
         pragma Assert (Log2 (Bnd1 (K) + 1) = Log1 (Bnd1 (K) + 1));
         pragma Assert (Log2 (Bnd1 (K) + 2) = Log1 (Bnd1 (K) + 2));
         pragma Assert (Log2 (Bnd1 (K) + 3) = Log1 (Bnd1 (K) + 3));
         pragma Assert (Len_Word (Log2, Bnd2 (K)) = Len_Word (Log1, Bnd1 (K)));
         pragma Assert (Frame_At (Log2, LL2, Bnd2 (K)));
         pragma Assert (Bnd2 (K) + Prefix_Len + Natural (Len_Word (Log2, Bnd2 (K))) =
                          Bnd2 (K + 1));
         pragma Loop_Invariant
           (for all J in 1 .. K =>
              Frame_At (Log2, LL2, Bnd2 (J))
              and then Bnd2 (J) + Prefix_Len + Natural (Len_Word (Log2, Bnd2 (J))) =
                         Bnd2 (J + 1));
      end loop;
      pragma Assert (Frame_At (Log2, LL2, Bnd2 (NB1 + 1)));
      pragma Assert
        (Bnd2 (NB1 + 1) + Prefix_Len + Natural (Len_Word (Log2, Bnd2 (NB1 + 1))) = LL2);
      pragma Assert (Bnd2 (1) = 0);
      pragma Assert (NB1 <= LL1 / Min_Frame);
      pragma Assert (NB1 + 1 <= LL2 / Min_Frame);
   end Lemma_Chain_Grow;

   --  Entries keep their frames when the chain grows.
   procedure Lemma_Bounds_Grow
     (Idx : Entry_Array; N : Held_Count;
      Bnd1 : Offset_Array; NB1 : Natural; Bnd2 : Offset_Array; NB2 : Natural)
   with
     Ghost, Global => null,
     Pre  => Idx'First = 1 and then N <= Idx'Last
       and then Bnd1'First = 1 and then NB1 <= Bnd1'Last
       and then Bnd2'First = 1 and then NB2 <= Bnd2'Last
       and then NB1 <= NB2
       and then (for all K in 1 .. NB1 => Bnd2 (K) = Bnd1 (K))
       and then At_Bounds (Idx, N, Bnd1, NB1),
     Post => At_Bounds (Idx, N, Bnd2, NB2);

   procedure Lemma_Bounds_Grow
     (Idx : Entry_Array; N : Held_Count;
      Bnd1 : Offset_Array; NB1 : Natural; Bnd2 : Offset_Array; NB2 : Natural) is
   begin
      pragma Assert
        (for all J in 1 .. N => (for some K in 1 .. NB1 => Bnd1 (K) = Idx (J).Off));
      for J in 1 .. N loop
         declare
            K : constant Positive := Bound_Witness (Idx, N, Bnd1, NB1, J);
         begin
            pragma Assert (Bnd2 (K) = Idx (J).Off);
         end;
         pragma Loop_Invariant
           (for all J2 in 1 .. J => (for some K in 1 .. NB2 => Bnd2 (K) = Idx (J2).Off));
      end loop;
      pragma Assert
        (for all J in 1 .. N => (for some K in 1 .. NB2 => Bnd2 (K) = Idx (J).Off));
   end Lemma_Bounds_Grow;

   --  A new last entry at the last frame.
   procedure Lemma_Bounds_Push
     (Old : Entry_Array; N0 : Held_Count; Idx : Entry_Array; N : Held_Count;
      Bnd : Offset_Array; NB : Natural)
   with
     Ghost, Global => null,
     Pre  => Old'First = 1 and then N0 <= Old'Last
       and then Idx'First = 1 and then N <= Idx'Last
       and then Bnd'First = 1 and then NB <= Bnd'Last
       and then N = N0 + 1 and then NB >= 1
       and then (for all J in 1 .. N0 => Idx (J) = Old (J))
       and then Idx (N).Off = Bnd (NB)
       and then At_Bounds (Old, N0, Bnd, NB),
     Post => At_Bounds (Idx, N, Bnd, NB);

   procedure Lemma_Bounds_Push
     (Old : Entry_Array; N0 : Held_Count; Idx : Entry_Array; N : Held_Count;
      Bnd : Offset_Array; NB : Natural) is
   begin
      pragma Assert
        (for all J in 1 .. N0 => (for some K in 1 .. NB => Bnd (K) = Old (J).Off));
      for J in 1 .. N0 loop
         declare
            K : constant Positive := Bound_Witness (Old, N0, Bnd, NB, J);
         begin
            pragma Assert (Bnd (K) = Idx (J).Off);
         end;
         pragma Loop_Invariant
           (for all J2 in 1 .. J => (for some K in 1 .. NB => Bnd (K) = Idx (J2).Off));
      end loop;
      pragma Assert (Bnd (NB) = Idx (N).Off);
      pragma Assert
        (for all J in 1 .. N => (for some K in 1 .. NB => Bnd (K) = Idx (J).Off));
   end Lemma_Bounds_Push;

   --  Entries picked from an index whose frames are on the chain are too.
   procedure Lemma_Bounds_Sub
     (Idx : Entry_Array; N : Held_Count; Old : Entry_Array; N0 : Held_Count;
      Bnd : Offset_Array; NB : Natural)
   with
     Ghost, Global => null,
     Pre  => Idx'First = 1 and then N <= Idx'Last
       and then Old'First = 1 and then N0 <= Old'Last
       and then Bnd'First = 1 and then NB <= Bnd'Last
       and then Sub (Idx, N, Old, N0)
       and then At_Bounds (Old, N0, Bnd, NB),
     Post => At_Bounds (Idx, N, Bnd, NB);

   procedure Lemma_Bounds_Sub
     (Idx : Entry_Array; N : Held_Count; Old : Entry_Array; N0 : Held_Count;
      Bnd : Offset_Array; NB : Natural) is
   begin
      pragma Assert (for all J in 1 .. N => (for some I in 1 .. N0 => Idx (J) = Old (I)));
      pragma Assert
        (for all J in 1 .. N0 => (for some K in 1 .. NB => Bnd (K) = Old (J).Off));
      for J in 1 .. N loop
         declare
            I : constant Held_Index := Same_Witness (Idx, N, Old, N0, J);
            K : constant Positive := Bound_Witness (Old, N0, Bnd, NB, I);
         begin
            pragma Assert (Bnd (K) = Idx (J).Off);
         end;
         pragma Loop_Invariant
           (for all J2 in 1 .. J => (for some K in 1 .. NB => Bnd (K) = Idx (J2).Off));
      end loop;
      pragma Assert
        (for all J in 1 .. N => (for some K in 1 .. NB => Bnd (K) = Idx (J).Off));
   end Lemma_Bounds_Sub;

   --  A log that is exactly the entries' frames, contiguous from 0, is the
   --  chain of their offsets.
   procedure Lemma_Chain_Packed
     (Log : Byte_Array; W : Log_Size; Idx : Entry_Array; N : Held_Count; Bnd : Offset_Array)
   with
     Ghost, Global => null,
     Pre  => Log'First = 0 and then W <= Log'Last
       and then Idx'First = 1 and then N <= Idx'Last
       and then Bnd'First = 1 and then N <= Bnd'Last
       and then Framed (Log, W, Idx, N)
       and then (if N = 0 then W = 0
                 else Idx (1).Off = 0 and then W = End_Of (Idx (N)))
       and then (for all J in 1 .. N - 1 => Idx (J + 1).Off = End_Of (Idx (J)))
       and then Min_Frame * N <= W
       and then (for all J in 1 .. N => Bnd (J) = Idx (J).Off),
     Post => Chain (Log, W, Bnd, N) and then At_Bounds (Idx, N, Bnd, N);

   procedure Lemma_Chain_Packed
     (Log : Byte_Array; W : Log_Size; Idx : Entry_Array; N : Held_Count; Bnd : Offset_Array) is
   begin
      for J in 1 .. N loop
         pragma Assert (Frame_OK (Log, W, Idx (J)));
         pragma Assert (Len_Word (Log, Bnd (J)) = Word (Idx (J).Len));
         pragma Assert (Frame_At (Log, W, Bnd (J)));
         pragma Assert (Bnd (J) + Prefix_Len + Natural (Len_Word (Log, Bnd (J))) =
                          End_Of (Idx (J)));
         pragma Assert (End_Of (Idx (J)) = (if J < N then Bnd (J + 1) else W));
         pragma Assert (for some K in 1 .. N => Bnd (K) = Idx (J).Off);
         pragma Loop_Invariant
           (for all J2 in 1 .. J =>
              Frame_At (Log, W, Bnd (J2))
              and then Bnd (J2) + Prefix_Len + Natural (Len_Word (Log, Bnd (J2))) =
                         (if J2 < N then Bnd (J2 + 1) else W)
              and then (for some K in 1 .. N => Bnd (K) = Idx (J2).Off));
      end loop;
      pragma Assert ((N = 0) = (W = 0));
      pragma Assert (N <= W / Min_Frame);
      pragma Assert (for all J in 1 .. N => (for some K in 1 .. N => Bnd (K) = Idx (J).Off));
   end Lemma_Chain_Packed;

   ---------------------------------------------------------------------------
   --  Filtering the index.
   ---------------------------------------------------------------------------

   --  Which entries a filter drops: those R dominates (after applying R),
   --  or the DELs expired under Hz.
   type Drop_Rule is record
      By_Dom : Boolean := True;
      R      : Header;
      Hz     : Time64  := No_Horizon;
   end record;

   No_Header : constant Header :=
     (K => K_Put, NS => (others => 0), Ent => (others => 0), FH => (others => 0),
      V => (T => 0, Author => (others => 0), Seq => 0, H => (others => 0)),
      Ceiling => 0);

   function Drops (D : Drop_Rule; E : Index_Entry) return Boolean is
     (if D.By_Dom then Dominates (D.R, E.H) else Expired (E.H, D.Hz));

   type Index_Map is array (Held_Index range <>) of Held_Count;

   --  A subsequence of a sorted index, picked by increasing positions, is
   --  sorted.
   procedure Lemma_Sorted_Sub
     (Old : Entry_Array; N0 : Held_Count; Idx : Entry_Array; N : Held_Count;
      Src : Index_Map)
   with
     Ghost, Global => null,
     Pre  => Old'First = 1 and then N0 <= Old'Last
       and then Idx'First = 1 and then N <= Idx'Last
       and then Src'First = 1 and then N <= Src'Last
       and then (for all J in 1 .. N => Src (J) in 1 .. N0 and then Idx (J) = Old (Src (J)))
       and then (for all J in 1 .. N => (for all J2 in J + 1 .. N => Src (J) < Src (J2))),
     Post => (if Sorted (Old, N0) then Sorted (Idx, N));

   procedure Lemma_Sorted_Sub
     (Old : Entry_Array; N0 : Held_Count; Idx : Entry_Array; N : Held_Count;
      Src : Index_Map) is
   begin
      if not Sorted (Old, N0) then
         return;
      end if;
      for J in 1 .. N loop
         for J2 in J + 1 .. N loop
            pragma Assert (Src (J) < Src (J2));
            pragma Assert (End_Of (Old (Src (J))) <= Old (Src (J2)).Off
                           and then Old (Src (J)).H /= Old (Src (J2)).H);
            pragma Loop_Invariant
              (for all J3 in J + 1 .. J2 =>
                 End_Of (Idx (J)) <= Idx (J3).Off and then Idx (J).H /= Idx (J3).H);
         end loop;
         pragma Loop_Invariant
           (for all J1 in 1 .. J =>
              (for all J3 in J1 + 1 .. N =>
                 End_Of (Idx (J1)) <= Idx (J3).Off and then Idx (J1).H /= Idx (J3).H));
      end loop;
   end Lemma_Sorted_Sub;

   --  Remove the entries D drops, keeping the others in order.
   procedure Filter (Idx : in out Entry_Array; N : in out Held_Count; D : Drop_Rule) with
     Global => null,
     Pre  => Idx'First = 1 and then N <= Idx'Last,
     Post => N <= N'Old
       and then (if (for some I in 1 .. N'Old => Drops (D, Idx'Old (I))) then N < N'Old)
       and then (for all J in 1 .. N => not Drops (D, Idx (J)))
       and then Sub (Idx, N, Idx'Old, N'Old)
       and then (for all I in 1 .. N'Old =>
                   (if not Drops (D, Idx'Old (I))
                    then (for some J in 1 .. N => Idx (J) = Idx'Old (I))))
       and then (if Sorted (Idx'Old, N'Old) then Sorted (Idx, N));

   procedure Filter (Idx : in out Entry_Array; N : in out Held_Count; D : Drop_Rule) is
      Old  : constant Entry_Array := Idx with Ghost;
      N0   : constant Held_Count := N;
      Kept : Held_Count := 0;
      --  Src (J): the old position of kept entry J. Dst (I): where old
      --  entry I went (0 if dropped).
      Src  : Index_Map (1 .. N0) := [others => 0] with Ghost;
      Dst  : Index_Map (1 .. N0) := [others => 0] with Ghost;
   begin
      for I in 1 .. N0 loop
         pragma Assert (Idx (I) = Old (I));
         if not Drops (D, Idx (I)) then
            Kept := Kept + 1;
            Idx (Kept) := Idx (I);
            Src (Kept) := I;
            Dst (I) := Kept;
         end if;
         pragma Loop_Invariant (Kept <= I);
         pragma Loop_Invariant (for all K in I + 1 .. N0 => Idx (K) = Old (K));
         pragma Loop_Invariant
           (for all J in 1 .. Kept =>
              Src (J) in 1 .. I
              and then Idx (J) = Old (Src (J))
              and then not Drops (D, Old (Src (J))));
         pragma Loop_Invariant
           (for all J in 1 .. Kept =>
              (for all J2 in J + 1 .. Kept => Src (J) < Src (J2)));
         pragma Loop_Invariant
           (for all K in 1 .. I =>
              (if not Drops (D, Old (K))
               then Dst (K) in 1 .. Kept and then Idx (Dst (K)) = Old (K)));
         pragma Loop_Invariant
           ((Kept = I) = (for all K in 1 .. I => not Drops (D, Old (K))));
      end loop;
      Lemma_Sorted_Sub (Old, N0, Idx, Kept, Src);
      pragma Assert
        (for all J in 1 .. Kept => (for some I in 1 .. N0 => Idx (J) = Old (I)));
      pragma Assert (Sub (Idx, Kept, Old, N0));
      N := Kept;
   end Filter;

   ---------------------------------------------------------------------------
   --  Appending a frame.
   ---------------------------------------------------------------------------

   --  Log (P .. P + Frame'Length - 1) holds Frame. Defined by its Post.
   function Bytes_At (Log : Byte_Array; P : Natural; Frame : Byte_Array) return Boolean
   with Ghost, Global => null,
        Pre  => Log'First = 0 and then Log'Last <= Log_Max
                and then Frame'Length in Frame_Size
                and then P <= Log'Last and then Frame'Length - 1 <= Log'Last - P,
        Post => Bytes_At'Result =
                  (for all K in 0 .. Frame'Length - 1 => Log (P + K) = Frame (Frame'First + K));

   function Bytes_At (Log : Byte_Array; P : Natural; Frame : Byte_Array) return Boolean is
   begin
      return (for all K in 0 .. Frame'Length - 1 => Log (P + K) = Frame (Frame'First + K));
   end Bytes_At;

   procedure Append (Log : in out Byte_Array; LL : in out Log_Size; Frame : Byte_Array) with
     Global => null,
     Pre  => Log'First = 0 and then LL <= Log'Last and then Log'Last <= Log_Max
             and then Frame'Length in Frame_Size
             and then Prefix_Len + Frame'Length <= Log'Last - LL,
     Post => LL = LL'Old + Prefix_Len + Frame'Length
       and then (for all P in 0 .. LL'Old - 1 => Log (P) = Log'Old (P))
       and then Kome.Keys.Word_Of (Log (LL'Old), Log (LL'Old + 1),
                                   Log (LL'Old + 2), Log (LL'Old + 3)) = Word (Frame'Length)
       and then Log (LL'Old + Prefix_Len) = Frame (Frame'First)
       and then (for all K in 0 .. Frame'Length - 1 =>
                   Log (LL'Old + Prefix_Len + K) = Frame (Frame'First + K));

   procedure Append (Log : in out Byte_Array; LL : in out Log_Size; Frame : Byte_Array) is
      Old_Log : constant Byte_Array := Log with Ghost;
      W       : constant Word := Word (Frame'Length);
      P       : constant Log_Size := LL;
      B0      : constant Byte := Kome.Keys.Byte_Of_Word (W, 0);
      B1      : constant Byte := Kome.Keys.Byte_Of_Word (W, 1);
      B2      : constant Byte := Kome.Keys.Byte_Of_Word (W, 2);
      B3      : constant Byte := Kome.Keys.Byte_Of_Word (W, 3);
   begin
      Kome.Keys.Lemma_Word_Round_Trip (W);
      pragma Assert (Kome.Keys.Word_Of (B0, B1, B2, B3) = W);
      Log (P)     := B0;
      Log (P + 1) := B1;
      Log (P + 2) := B2;
      Log (P + 3) := B3;
      for K in 0 .. Frame'Length - 1 loop
         Log (P + Prefix_Len + K) := Frame (Frame'First + K);
         pragma Loop_Invariant (for all Q in 0 .. P - 1 => Log (Q) = Old_Log (Q));
         pragma Loop_Invariant
           (Log (P) = B0 and then Log (P + 1) = B1
            and then Log (P + 2) = B2 and then Log (P + 3) = B3);
         pragma Loop_Invariant (Log (P + Prefix_Len) = Frame (Frame'First));
         pragma Loop_Invariant
           (for all K2 in 0 .. K => Log (P + Prefix_Len + K2) = Frame (Frame'First + K2));
      end loop;
      LL := P + Prefix_Len + Frame'Length;
   end Append;

   --  Dst (W .. W + Size - 1) := Src (From .. From + Size - 1); everything
   --  below W is untouched. The first five bytes (length prefix and tag)
   --  are stated one by one, so that callers need no instantiation at +0.
   procedure Copy_Bytes
     (Dst : in out Byte_Array; W : Natural; Src : Byte_Array; From : Natural;
      Size : Positive)
   with
     Global => null,
     Pre  => Dst'First = 0 and then Src'First = 0
             and then Dst'Last <= Log_Max and then Src'Last <= Log_Max
             and then Size >= Prefix_Len + 1
             and then W <= Dst'Last and then Size - 1 <= Dst'Last - W
             and then From <= Src'Last and then Size - 1 <= Src'Last - From,
     Post => (for all P in 0 .. W - 1 => Dst (P) = Dst'Old (P))
       and then (for all K in 0 .. Size - 1 => Dst (W + K) = Src (From + K))
       and then Dst (W) = Src (From)
       and then Dst (W + 1) = Src (From + 1)
       and then Dst (W + 2) = Src (From + 2)
       and then Dst (W + 3) = Src (From + 3)
       and then Dst (W + 4) = Src (From + 4);

   procedure Copy_Bytes
     (Dst : in out Byte_Array; W : Natural; Src : Byte_Array; From : Natural;
      Size : Positive)
   is
   begin
      for K in 0 .. Size - 1 loop
         Dst (W + K) := Src (From + K);
         pragma Loop_Invariant (for all P in 0 .. W - 1 => Dst (P) = Dst'Loop_Entry (P));
         pragma Loop_Invariant (Dst (W) = Src (From));
         pragma Loop_Invariant (for all K2 in 0 .. K => Dst (W + K2) = Src (From + K2));
      end loop;
   end Copy_Bytes;

   --  Bnd (NB + 1) := P; NB := NB + 1.
   procedure Push_Bound (Bnd : in out Offset_Array; NB : in out Log_Size; P : Log_Size) with
     Global => null,
     Pre  => Bnd'First = 1 and then NB < Bnd'Last and then Bnd'Last <= Log_Max,
     Post => NB = NB'Old + 1
       and then Bnd (NB) = P
       and then (for all K in 1 .. NB'Old => Bnd (K) = Bnd'Old (K));

   procedure Push_Bound (Bnd : in out Offset_Array; NB : in out Log_Size; P : Log_Size) is
   begin
      NB := NB + 1;
      Bnd (NB) := P;
   end Push_Bound;

   --  Bnd (J) := Idx (J).Off for J in 1 .. N.
   procedure Set_Bounds (Bnd : in out Offset_Array; Idx : Entry_Array; N : Held_Count) with
     Global => null,
     Pre  => Bnd'First = 1 and then N <= Bnd'Last
             and then Idx'First = 1 and then N <= Idx'Last,
     Post => (for all J in 1 .. N => Bnd (J) = Idx (J).Off);

   procedure Set_Bounds (Bnd : in out Offset_Array; Idx : Entry_Array; N : Held_Count) is
   begin
      for J in 1 .. N loop
         Bnd (J) := Idx (J).Off;
         pragma Loop_Invariant (for all J2 in 1 .. J => Bnd (J2) = Idx (J2).Off);
      end loop;
   end Set_Bounds;

   --  Append Frame to the log and its offset to the chain.
   procedure Log_Frame
     (Log : in out Byte_Array; LL : in out Log_Size;
      Bnd : in out Offset_Array; NB : in out Log_Size;
      Frame : Byte_Array)
   with
     Global => null,
     Pre  => Log'First = 0 and then LL <= Log'Last and then Log'Last <= Log_Max
             and then Bnd'First = 1 and then Bnd'Last = Log'Last and then NB <= Bnd'Last
             and then Frame'Length in Frame_Size
             and then Prefix_Len + Frame'Length <= Log'Last - LL
             and then Chain (Log, LL, Bnd, NB),
     Post => LL = LL'Old + Prefix_Len + Frame'Length
       and then (for all P in 0 .. LL'Old - 1 => Log (P) = Log'Old (P))
       and then Kome.Keys.Word_Of (Log (LL'Old), Log (LL'Old + 1),
                                   Log (LL'Old + 2), Log (LL'Old + 3)) = Word (Frame'Length)
       and then Log (LL'Old + Prefix_Len) = Frame (Frame'First)
       and then Bytes_At (Log, LL'Old + Prefix_Len, Frame)
       and then NB = NB'Old + 1
       and then Bnd (NB) = LL'Old
       and then (for all K in 1 .. NB'Old => Bnd (K) = Bnd'Old (K))
       and then Chain (Log, LL, Bnd, NB);

   procedure Log_Frame
     (Log : in out Byte_Array; LL : in out Log_Size;
      Bnd : in out Offset_Array; NB : in out Log_Size;
      Frame : Byte_Array)
   is
      Old_Log : constant Byte_Array := Log with Ghost;
      Old_Bnd : constant Offset_Array := Bnd with Ghost;
      Old_LL  : constant Log_Size := LL;
      Old_NB  : constant Log_Size := NB;
      Len     : constant Frame_Size := Frame'Length;
   begin
      pragma Assert (Old_NB <= Old_LL / Min_Frame);
      pragma Assert (Old_NB < Bnd'Last);
      Append (Log, LL, Frame);
      pragma Assert (Len_Word (Log, Old_LL) = Word (Len));
      pragma Assert (Bytes_At (Log, Old_LL + Prefix_Len, Frame));
      Push_Bound (Bnd, NB, Old_LL);
      Lemma_Chain_Grow (Old_Log, Old_LL, Log, LL, Old_Bnd, Old_NB, Bnd, Len);
   end Log_Frame;

   --  Append Frame to the log and, if Index_It, index it as H's entry.
   procedure Store_Frame
     (S : in out Store; Frame : Byte_Array; H : Header; Index_It : Boolean)
   with
     Global => null,
     Pre  => Frame'Length in Frame_Size
       and then Frame (Frame'First) = Kome.Records.Tag_Of (H.K)
       and then S.Log_Cap - S.LL >= Prefix_Len + Frame'Length
       and then Framed (S.Log, S.LL, S.Idx, S.NI)
       and then Sorted (S.Idx, S.NI)
       and then Chain (S.Log, S.LL, S.Bnd, S.NB)
       and then At_Bounds (S.Idx, S.NI, S.Bnd, S.NB)
       and then (if Index_It
                 then S.NI < S.Cap
                      and then (for all J in 1 .. S.NI => S.Idx (J).H /= H)),
     Post => S.NS = S.NS'Old and then S.Hz = S.Hz'Old
       and then S.LL = S.LL'Old + Prefix_Len + Frame'Length
       and then (for all P in 0 .. S.LL'Old - 1 => S.Log (P) = S.Log'Old (P))
       and then Kome.Keys.Word_Of (S.Log (S.LL'Old), S.Log (S.LL'Old + 1),
                                   S.Log (S.LL'Old + 2), S.Log (S.LL'Old + 3))
                  = Word (Frame'Length)
       and then Bytes_At (S.Log, S.LL'Old + Prefix_Len, Frame)
       and then Framed (S.Log, S.LL, S.Idx, S.NI)
       and then Sorted (S.Idx, S.NI)
       and then S.NB = S.NB'Old + 1
       and then S.Bnd (S.NB) = S.LL'Old
       and then (for all K in 1 .. S.NB'Old => S.Bnd (K) = S.Bnd'Old (K))
       and then Chain (S.Log, S.LL, S.Bnd, S.NB)
       and then At_Bounds (S.Idx, S.NI, S.Bnd, S.NB)
       and then (if Index_It
                 then S.NI = S.NI'Old + 1
                      and then S.Idx (S.NI) = (H => H, Off => S.LL'Old, Len => Frame'Length)
                      and then (for all J in 1 .. S.NI'Old => S.Idx (J) = S.Idx'Old (J))
                 else S.NI = S.NI'Old and then S.Idx = S.Idx'Old);

   procedure Store_Frame
     (S : in out Store; Frame : Byte_Array; H : Header; Index_It : Boolean)
   is
      Old_Log : constant Byte_Array := S.Log with Ghost;
      Old_LL  : constant Log_Size := S.LL;
      Old_Idx : constant Entry_Array := S.Idx with Ghost;
      Old_NI  : constant Held_Count := S.NI with Ghost;
      Old_Bnd : constant Offset_Array := S.Bnd with Ghost;
      Old_NB  : constant Log_Size := S.NB with Ghost;
      Len     : constant Frame_Size := Frame'Length;
   begin
      pragma Assert (for all J in 1 .. S.NI => End_Of (S.Idx (J)) <= S.LL);
      Log_Frame (S.Log, S.LL, S.Bnd, S.NB, Frame);
      Lemma_Framed_Grow (Old_Log, Old_LL, S.Log, S.LL, S.Idx, S.NI);
      pragma Assert (S.Log (Old_LL + Prefix_Len) = Kome.Records.Tag_Of (H.K));
      Lemma_Bounds_Grow (S.Idx, S.NI, Old_Bnd, Old_NB, S.Bnd, S.NB);

      if Index_It then
         S.NI := S.NI + 1;
         S.Idx (S.NI) := (H => H, Off => Old_LL, Len => Len);
         pragma Assert (for all J in 1 .. Old_NI => S.Idx (J) = Old_Idx (J));
         pragma Assert (for all J in 1 .. Old_NI => End_Of (S.Idx (J)) <= Old_LL);
         pragma Assert (Frame_OK (S.Log, S.LL, S.Idx (S.NI)));
         pragma Assert (Framed (S.Log, S.LL, S.Idx, S.NI));
         pragma Assert (Sorted (S.Idx, S.NI));
         Lemma_Bounds_Push (Old_Idx, Old_NI, S.Idx, S.NI, S.Bnd, S.NB);
      end if;
   end Store_Frame;

   ---------------------------------------------------------------------------
   --  Re-establishing the invariant after Put_Frame.
   ---------------------------------------------------------------------------

   --  A record not held is not an entry of a live index, nor of any part of
   --  one.
   procedure Lemma_Not_Indexed
     (F   : Frontier.State; Hz : Time64;
      Old : Entry_Array; N0 : Held_Count; Idx : Entry_Array; N : Held_Count;
      R   : Header)
   with
     Ghost, Global => null,
     Pre  => Idx'First = 1 and then N <= Idx'Last
       and then Old'First = 1 and then N0 <= Old'Last
       and then Live (F, Hz, Old, N0)
       and then Sub (Idx, N, Old, N0)
       and then not Holds (F, R),
     Post => (for all J in 1 .. N => Idx (J).H /= R);

   procedure Lemma_Not_Indexed
     (F   : Frontier.State; Hz : Time64;
      Old : Entry_Array; N0 : Held_Count; Idx : Entry_Array; N : Held_Count;
      R   : Header) is
   begin
      pragma Assert (for all J in 1 .. N => (for some I in 1 .. N0 => Idx (J) = Old (I)));
      pragma Assert (for all I in 1 .. N0 => Holds (F, Old (I).H));
      for J in 1 .. N loop
         declare
            I : constant Held_Index := Same_Witness (Idx, N, Old, N0, J);
         begin
            pragma Assert (Holds (F, Old (I).H));
            pragma Assert (Idx (J).H /= R);
         end;
         pragma Loop_Invariant (for all J2 in 1 .. J => Idx (J2).H /= R);
      end loop;
   end Lemma_Not_Indexed;

   --  Entries picked from a live index, unexpired under Hz, are live
   --  under Hz.
   procedure Lemma_Live_Sub
     (F   : Frontier.State; Hz0, Hz : Time64;
      Old : Entry_Array; N0 : Held_Count; Idx : Entry_Array; N : Held_Count)
   with
     Ghost, Global => null,
     Pre  => Idx'First = 1 and then N <= Idx'Last
       and then Old'First = 1 and then N0 <= Old'Last
       and then Live (F, Hz0, Old, N0)
       and then Sub (Idx, N, Old, N0)
       and then (for all J in 1 .. N => not Expired (Idx (J).H, Hz)),
     Post => Live (F, Hz, Idx, N);

   procedure Lemma_Live_Sub
     (F   : Frontier.State; Hz0, Hz : Time64;
      Old : Entry_Array; N0 : Held_Count; Idx : Entry_Array; N : Held_Count) is
   begin
      pragma Assert (for all J in 1 .. N => (for some I in 1 .. N0 => Idx (J) = Old (I)));
      pragma Assert (for all I in 1 .. N0 => Holds (F, Old (I).H));
      for J in 1 .. N loop
         declare
            I : constant Held_Index := Same_Witness (Idx, N, Old, N0, J);
         begin
            pragma Assert (Idx (J) = Old (I));
            pragma Assert (Holds (F, Idx (J).H));
         end;
         pragma Loop_Invariant
           (for all J2 in 1 .. J =>
              Holds (F, Idx (J2).H) and then not Expired (Idx (J2).H, Hz));
      end loop;
   end Lemma_Live_Sub;

   --  Live: kept entries were held and not dominated by R, so are held.
   procedure Lemma_Live_Put
     (Old_F, New_F : Frontier.State; Hz : Time64;
      Old : Entry_Array; N0 : Held_Count; Idx : Entry_Array; N : Held_Count;
      R   : Header)
   with
     Ghost, Global => null,
     Pre  => Idx'First = 1 and then N <= Idx'Last
       and then Old'First = 1 and then N0 <= Old'Last
       and then Is_Frontier (Old_F)
       and then (for all I in 1 .. Count (New_F) =>
                   Holds (Old_F, Held (New_F, I)) or else Held (New_F, I) = R)
       and then (for all I in 1 .. Count (Old_F) =>
                   Holds (New_F, Held (Old_F, I)) or else Dom (New_F, Held (Old_F, I)))
       and then Live (Old_F, Hz, Old, N0)
       and then Sub (Idx, N, Old, N0)
       and then (for all J in 1 .. N => not Dominates (R, Idx (J).H)),
     Post => Live (New_F, Hz, Idx, N);

   procedure Lemma_Live_Put
     (Old_F, New_F : Frontier.State; Hz : Time64;
      Old : Entry_Array; N0 : Held_Count; Idx : Entry_Array; N : Held_Count;
      R   : Header) is
   begin
      pragma Assert (for all J in 1 .. N => (for some I in 1 .. N0 => Idx (J) = Old (I)));
      for J in 1 .. N loop
         declare
            I : constant Held_Index := Same_Witness (Idx, N, Old, N0, J);
         begin
            pragma Assert (Holds (Old_F, Old (I).H) and then not Expired (Old (I).H, Hz));
            Lemma_Survivor (Old_F, New_F, R, Idx (J).H);
         end;
         pragma Loop_Invariant
           (for all J2 in 1 .. J =>
              Holds (New_F, Idx (J2).H) and then not Expired (Idx (J2).H, Hz));
      end loop;
   end Lemma_Live_Put;

   --  Covered: a held unexpired record is the applied record R, which is
   --  indexed, or was held and indexed before and R does not dominate it.
   procedure Lemma_Covered_Put
     (Old_F, New_F : Frontier.State; Hz : Time64;
      Old : Entry_Array; N0 : Held_Count; Idx : Entry_Array; N : Held_Count;
      R   : Header)
   with
     Ghost, Global => null,
     Pre  => Idx'First = 1 and then N <= Idx'Last
       and then Old'First = 1 and then N0 <= Old'Last
       and then Is_Frontier (New_F)
       and then Covered (Old_F, Hz, Old, N0)
       and then (for all I in 1 .. Count (New_F) =>
                   Holds (Old_F, Held (New_F, I)) or else Held (New_F, I) = R)
       and then (Holds (New_F, R) or else Dom (New_F, R))
       and then (for all I in 1 .. N0 =>
                   (if not Dominates (R, Old (I).H) then Has_Entry (Idx, N, Old (I).H)))
       and then (if Holds (New_F, R) and then not Expired (R, Hz)
                 then Has_Entry (Idx, N, R)),
     Post => Covered (New_F, Hz, Idx, N);

   --  One held record of the new state, for Lemma_Covered_Put.
   procedure Lemma_Covered_One
     (Old_F, New_F : Frontier.State; Hz : Time64;
      Old : Entry_Array; N0 : Held_Count; Idx : Entry_Array; N : Held_Count;
      R   : Header; K : Held_Index)
   with
     Ghost, Global => null,
     Pre  => Idx'First = 1 and then N <= Idx'Last
       and then Old'First = 1 and then N0 <= Old'Last
       and then K <= Count (New_F)
       and then Is_Frontier (New_F)
       and then Covered (Old_F, Hz, Old, N0)
       and then (Holds (Old_F, Held (New_F, K)) or else Held (New_F, K) = R)
       and then (Holds (New_F, R) or else Dom (New_F, R))
       and then (for all I in 1 .. N0 =>
                   (if not Dominates (R, Old (I).H) then Has_Entry (Idx, N, Old (I).H)))
       and then (if Holds (New_F, R) and then not Expired (R, Hz)
                 then Has_Entry (Idx, N, R)),
     Post => Expired (Held (New_F, K), Hz) or else Has_Entry (Idx, N, Held (New_F, K));

   procedure Lemma_Covered_One
     (Old_F, New_F : Frontier.State; Hz : Time64;
      Old : Entry_Array; N0 : Held_Count; Idx : Entry_Array; N : Held_Count;
      R   : Header; K : Held_Index)
   is
      Y : constant Header := Held (New_F, K);
   begin
      pragma Assert (Holds (New_F, Y));
      if not Expired (Y, Hz) then
         if Y = R then
            pragma Assert (Holds (New_F, R));
            pragma Assert (Has_Entry (Idx, N, R));
         else
            pragma Assert (Holds (Old_F, Y));
            declare
               K2 : constant Held_Index := Witness (Old_F, Y);
            begin
               pragma Assert (not Expired (Held (Old_F, K2), Hz));
               pragma Assert (Has_Entry (Old, N0, Held (Old_F, K2)));
               Lemma_Not_Beaten (New_F, R, Y);
               declare
                  I : constant Held_Index := Entry_Witness (Old, N0, Y);
               begin
                  pragma Assert (not Dominates (R, Old (I).H));
                  pragma Assert (Has_Entry (Idx, N, Y));
               end;
            end;
         end if;
      end if;
   end Lemma_Covered_One;

   procedure Lemma_Covered_Put
     (Old_F, New_F : Frontier.State; Hz : Time64;
      Old : Entry_Array; N0 : Held_Count; Idx : Entry_Array; N : Held_Count;
      R   : Header) is
   begin
      for K in 1 .. Count (New_F) loop
         Lemma_Covered_One (Old_F, New_F, Hz, Old, N0, Idx, N, R, K);
         pragma Loop_Invariant
           (for all K3 in 1 .. K =>
              Expired (Held (New_F, K3), Hz) or else Has_Entry (Idx, N, Held (New_F, K3)));
      end loop;
   end Lemma_Covered_Put;

   --  Appending one entry for R (or none) keeps every entry and every
   --  fact about which records are indexed.
   procedure Lemma_Index_Grow
     (F   : Frontier.State; Hz : Time64;
      Old : Entry_Array; N0 : Held_Count;
      A   : Entry_Array; NA : Held_Count; B : Entry_Array; NB : Held_Count;
      R   : Header; Grew : Boolean)
   with
     Ghost, Global => null,
     Pre  => Old'First = 1 and then N0 <= Old'Last
       and then A'First = 1 and then NA <= A'Last
       and then B'First = 1 and then NB <= B'Last
       and then NA <= NB
       and then (if Grew then NB = NA + 1 else NB = NA)
       and then (if Grew
                 then NB >= 1 and then B (NB).H = R
                      and then Holds (F, R) and then not Expired (R, Hz))
       and then Live (F, Hz, A, NA)
       and then (for all I in 1 .. N0 =>
                   (if not Dominates (R, Old (I).H) then Has_Entry (A, NA, Old (I).H)))
       and then (for all J in 1 .. NA => B (J) = A (J)),
     Post => Live (F, Hz, B, NB)
       and then (for all I in 1 .. N0 =>
                   (if not Dominates (R, Old (I).H) then Has_Entry (B, NB, Old (I).H)))
       and then (if Grew then Has_Entry (B, NB, R));

   procedure Lemma_Index_Grow
     (F   : Frontier.State; Hz : Time64;
      Old : Entry_Array; N0 : Held_Count;
      A   : Entry_Array; NA : Held_Count; B : Entry_Array; NB : Held_Count;
      R   : Header; Grew : Boolean) is
   begin
      for I in 1 .. N0 loop
         if not Dominates (R, Old (I).H) then
            declare
               J : constant Held_Index := Entry_Witness (A, NA, Old (I).H);
            begin
               pragma Assert (B (J).H = Old (I).H);
            end;
         end if;
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              (if not Dominates (R, Old (I2).H) then Has_Entry (B, NB, Old (I2).H)));
      end loop;
   end Lemma_Index_Grow;

   ---------------------------------------------------------------------------
   --  Operations.
   ---------------------------------------------------------------------------

   procedure Open (NS : Id128; F : Frontier.State; S : out Store) is
   begin
      S := (Cap     => S.Cap,
            Log_Cap => S.Log_Cap,
            NS      => NS,
            Hz      => No_Horizon,
            NI      => 0,
            Idx     => [others => (H => <>, Off => 0, Len => 1)],
            LL      => 0,
            Log     => [others => 0],
            NB      => 0,
            Bnd     => [others => 0]);
   end Open;

   function Read_Frame (S : Store; Off : Natural) return Byte_Array is
      L : constant Natural := Natural (Len_At (S, Off));
      R : Byte_Array (0 .. L - 1) := [others => 0];
   begin
      for K in 0 .. L - 1 loop
         R (K) := S.Log (Off + Prefix_Len + K);
         pragma Loop_Invariant
           (for all K2 in 0 .. K => R (K2) = Log_Byte (S, Off + Prefix_Len + K2));
      end loop;
      return R;
   end Read_Frame;

   procedure Put_Frame
     (S       : in out Store;
      F       : in out Frontier.State;
      Frame   : in     Byte_Array;
      H       : in     Header;
      Members : in     Member_Keys;
      Off     :    out Log_Size;
      Result  :    out Status)
   is
      Saved_F  : constant Frontier.State := F with Ghost;
      Saved_S  : constant Store := S with Ghost;
      Was_Held : constant Boolean := Holds (F, H);
      D        : constant Drop_Rule := (By_Dom => True, R => H, Hz => S.Hz);
      St      : Status;
      Fresh   : Boolean;
      Need    : Boolean;
   begin
      Off := S.LL;

      --  Every refusal is decided before Frontier.Apply runs, so that a
      --  refused record changes nothing at all (Apply would already have
      --  raised a roster's registers, and the store cannot copy a
      --  Frontier.State back: see the package comment).
      --  1. Admission (DESIGN.md §4).
      pragma Assert (Log_Extends (Saved_S, S));
      if not Admitted (F, H) then
         Result := Inadmissible;
         return;
      end if;
      --  2. Room, for a record that may be newly held: in the frontier
      --  (exactly Frontier.Apply's rule: full and R frees nothing), in the
      --  log, and in the index (unless R is already expired, or frees an
      --  entry). A dominated record on a full log or index is refused too.
      if not Was_Held
        and then ((not Dom (F, H)
                   and then Count (F) = F.Cap
                   and then not Frees (F, H))
                  or else S.Log_Cap - S.LL < Prefix_Len + Frame'Length
                  or else (not Expired (H, S.Hz)
                           and then S.NI = S.Cap
                           and then not Index_Frees (S, H)))
      then
         Result := No_Space;
         pragma Assert (At_Bound (Saved_S, Saved_F, H, Frame'Length));
         return;
      end if;

      Apply (F, H, Members, St);

      --  Inadmissible is impossible: R was admitted and admission is
      --  monotone (T4'). No_Space is impossible because step 2 refused
      --  exactly the case Frontier.Apply's body refuses; Frontier.Apply's
      --  contract does not state that rule, so this half is not provable
      --  here (reported; checked at run time).
      Lemma_Admitted_Mono (Saved_F, F, H);
      pragma Assert (St /= Inadmissible);
      pragma Assert (St in OK | Dominated);

      --  What Apply established.
      pragma Assert (Is_Frontier (F));
      pragma Assert (Holds (F, H) or else Dom (F, H));
      pragma Assert (if St = Dominated then not Holds (F, H));
      Lemma_Canon (Saved_F, F, H);

      --  Append the frame iff R is newly held; index it iff also not
      --  expired (apply-then-expire).
      Fresh := St = OK and then not Was_Held;
      Need  := Fresh and then not Expired (H, S.Hz);
      pragma Assert
        (Index_Frees (S, H) = (for some I in 1 .. S.NI => Drops (D, S.Idx (I))));
      pragma Assert (if Fresh then S.Log_Cap - S.LL >= Prefix_Len + Frame'Length);
      pragma Assert
        (if Need then S.NI < S.Cap or else (for some I in 1 .. S.NI => Drops (D, S.Idx (I))));

      declare
         Old_Idx : constant Entry_Array := S.Idx with Ghost;
         Old_NI  : constant Held_Count := S.NI with Ghost;
      begin
         --  Bridge: the invariant of the store as it was, in the names used
         --  below.
         pragma Assert (Live (Saved_F, S.Hz, Old_Idx, Old_NI));
         pragma Assert (Covered (Saved_F, S.Hz, Old_Idx, Old_NI));
         pragma Assert (Framed (S.Log, S.LL, Old_Idx, Old_NI));
         pragma Assert (Sorted (Old_Idx, Old_NI));
         pragma Assert (Chain (S.Log, S.LL, S.Bnd, S.NB));
         pragma Assert (At_Bounds (Old_Idx, Old_NI, S.Bnd, S.NB));
         pragma Assert (Off = S.LL);

         --  dom (x, F): drop the entries R dominates.
         Filter (S.Idx, S.NI, D);
         pragma Assert (for all J in 1 .. S.NI => not Dominates (H, S.Idx (J).H));
         Lemma_Bounds_Sub (S.Idx, S.NI, Old_Idx, Old_NI, S.Bnd, S.NB);
         pragma Assert (Chain (S.Log, S.LL, S.Bnd, S.NB));
         Lemma_Live_Put (Saved_F, F, S.Hz, Old_Idx, Old_NI, S.Idx, S.NI, H);
         Lemma_Framed_Sub (S.Log, S.LL, Old_Idx, Old_NI, S.Idx, S.NI);
         pragma Assert (Sorted (S.Idx, S.NI));
         Lemma_Dominates_Irrefl (H);
         pragma Assert
           (for all I in 1 .. Old_NI =>
              (if not Dominates (H, Old_Idx (I).H)
               then Has_Entry (S.Idx, S.NI, Old_Idx (I).H)));
         if Fresh then
            Lemma_Not_Indexed (Saved_F, S.Hz, Old_Idx, Old_NI, S.Idx, S.NI, H);
         end if;
         pragma Assert (if Fresh then (for all J in 1 .. S.NI => S.Idx (J).H /= H));
         pragma Assert (if Need then S.NI < S.Cap);

         if Fresh then
            declare
               Kept_Idx : constant Entry_Array := S.Idx with Ghost;
               Kept_NI  : constant Held_Count := S.NI with Ghost;
            begin
               pragma Assert (Frame (Frame'First) = Kome.Records.Tag_Of (H.K));
               Store_Frame (S, Frame, H, Need);
               pragma Assert
                 (for all K in 0 .. Frame'Length - 1 =>
                    S.Log (Off + Prefix_Len + K) = Frame (Frame'First + K));
               pragma Assert (Live (F, S.Hz, Kept_Idx, Kept_NI));
               pragma Assert
                 (for all I in 1 .. Old_NI =>
                    (if not Dominates (H, Old_Idx (I).H)
                     then Has_Entry (Kept_Idx, Kept_NI, Old_Idx (I).H)));
               pragma Assert (for all J in 1 .. Kept_NI => S.Idx (J) = Kept_Idx (J));
               pragma Assert
                 (if Need then S.NI = Kept_NI + 1 and then S.Idx (S.NI).H = H
                  else S.NI = Kept_NI);
               pragma Assert (if Need then Holds (F, H) and then not Expired (H, S.Hz));
               Lemma_Index_Grow
                 (F, S.Hz, Old_Idx, Old_NI, Kept_Idx, Kept_NI, S.Idx, S.NI, H, Need);
               pragma Assert (if Need then Has_Entry (S.Idx, S.NI, H));
               pragma Assert (Live (F, S.Hz, S.Idx, S.NI));
               pragma Assert
                 (for all I in 1 .. Old_NI =>
                    (if not Dominates (H, Old_Idx (I).H)
                     then Has_Entry (S.Idx, S.NI, Old_Idx (I).H)));
            end;
         else
            if St = OK and then not Expired (H, S.Hz) then
               declare
                  K : constant Held_Index := Witness (Saved_F, H) with Ghost;
               begin
                  pragma Assert (Held (Saved_F, K) = H);
                  pragma Assert (Has_Entry (Old_Idx, Old_NI, Held (Saved_F, K)));
               end;
               declare
                  I : constant Held_Index := Entry_Witness (Old_Idx, Old_NI, H) with Ghost;
               begin
                  pragma Assert (Old_Idx (I).H = H);
                  pragma Assert (not Dominates (H, Old_Idx (I).H));
                  pragma Assert (Has_Entry (S.Idx, S.NI, Old_Idx (I).H));
                  pragma Assert (Has_Entry (S.Idx, S.NI, H));
               end;
            end if;
         end if;
         pragma Assert
           (if Holds (F, H) and then not Expired (H, S.Hz)
            then Has_Entry (S.Idx, S.NI, H));

         Lemma_Covered_Put (Saved_F, F, S.Hz, Old_Idx, Old_NI, S.Idx, S.NI, H);
         pragma Assert (Live (F, S.Hz, S.Idx, S.NI));
         pragma Assert (Framed (S.Log, S.LL, S.Idx, S.NI));
         pragma Assert (Sorted (S.Idx, S.NI));
         pragma Assert (Chain (S.Log, S.LL, S.Bnd, S.NB));
         pragma Assert (At_Bounds (S.Idx, S.NI, S.Bnd, S.NB));
         pragma Assert (Valid (S, F));
      end;

      --  The contract's parts, over the saved state.
      pragma Assert (Log_Length (S) >= Log_Length (Saved_S));
      pragma Assert
        (for all J in 0 .. Log_Length (Saved_S) - 1 => Log_Byte (S, J) = Log_Byte (Saved_S, J));
      pragma Assert (Frames (S) >= Frames (Saved_S));
      pragma Assert
        (for all K in 1 .. Frames (Saved_S) => Frame_Start (S, K) = Frame_Start (Saved_S, K));
      pragma Assert (Log_Extends (Saved_S, S));
      pragma Assert
        (if Fresh
         then Off = Log_Length (Saved_S)
              and then Log_Length (S) = Off + Prefix_Len + Frame'Length
              and then Frames (S) = Frames (Saved_S) + 1
              and then Frame_Start (S, Frames (S)) = Off
         else Log_Length (S) = Log_Length (Saved_S)
              and then Frames (S) = Frames (Saved_S));
      pragma Assert
        (if Fresh
         then Has_Frame (S, Off)
              and then Natural (Len_At (S, Off)) = Frame'Length
              and then (for all K in 0 .. Frame'Length - 1 =>
                          Log_Byte (S, Off + Prefix_Len + K) = Frame (Frame'First + K)));
      pragma Assert
        (if Fresh and then not Expired (H, S.Hz)
         then Entries (S) >= 1
              and then Entry_At (S, Entries (S)) = (H => H, Off => Off, Len => Frame'Length));
      pragma Assert (if Fresh then Appended (Saved_S, S, Frame, H, Off));
      pragma Assert (Applied (Saved_F, F, H));
      pragma Assert
        (if St = OK
         then Holds (F, H) and then (if not Expired (H, Horizon (S)) then Indexed (S, H)));
      pragma Assert (if St = Dominated then Dom (F, H) and then not Holds (F, H));
      pragma Assert (Fresh = (St = OK and then not Holds (Saved_F, H)));
      pragma Assert (Admitted (Saved_F, H));
      pragma Assert (Collection (S) = Collection (Saved_S));
      pragma Assert (Horizon (S) = Horizon (Saved_S));
      pragma Assert (Valid (S, F));
      Result := St;
   end Put_Frame;

   procedure Expire (S : in out Store; F : Frontier.State; Now, Del_TTL : U48) is
      Old_S : constant Store := S with Ghost;
      Hz    : constant Time64 := Time64'Max (S.Hz, Time64 (Now) - Time64 (Del_TTL));
      D     : constant Drop_Rule := (By_Dom => False, R => No_Header, Hz => Hz);
   begin
      Filter (S.Idx, S.NI, D);
      S.Hz := Hz;

      pragma Assert (for all J in 1 .. S.NI => not Expired (S.Idx (J).H, Hz));
      Lemma_Framed_Sub (S.Log, S.LL, Old_S.Idx, Old_S.NI, S.Idx, S.NI);
      Lemma_Bounds_Sub (S.Idx, S.NI, Old_S.Idx, Old_S.NI, S.Bnd, S.NB);
      pragma Assert
        (for all J in 1 .. S.NI =>
           (for some I in 1 .. Old_S.NI => S.Idx (J) = Old_S.Idx (I)));
      Lemma_Live_Sub (F, Old_S.Hz, S.Hz, Old_S.Idx, Old_S.NI, S.Idx, S.NI);
      pragma Assert (Live (F, S.Hz, S.Idx, S.NI));
      pragma Assert (Sorted (S.Idx, S.NI));

      --  Every old entry is kept or an expired DEL at (Now, Del_TTL).
      pragma Assert
        (for all I in 1 .. Old_S.NI =>
           not Expired (Old_S.Idx (I).H, Old_S.Hz));
      pragma Assert
        (for all I in 1 .. Old_S.NI =>
           Expired_At (Old_S.Idx (I).H, Now, Del_TTL)
           or else not Drops (D, Old_S.Idx (I)));

      --  Covered: a held record unexpired now was unexpired before, hence
      --  indexed, and its entry was not dropped.
      for K in 1 .. Count (F) loop
         if not Expired (Held (F, K), Hz) then
            pragma Assert (not Expired (Held (F, K), Old_S.Hz));
            pragma Assert (Has_Entry (Old_S.Idx, Old_S.NI, Held (F, K)));
            declare
               I : constant Held_Index :=
                 Entry_Witness (Old_S.Idx, Old_S.NI, Held (F, K)) with Ghost;
            begin
               pragma Assert (not Drops (D, Old_S.Idx (I)));
               pragma Assert (Has_Entry (S.Idx, S.NI, Held (F, K)));
            end;
         end if;
         pragma Loop_Invariant
           (for all K3 in 1 .. K =>
              Expired (Held (F, K3), Hz) or else Has_Entry (S.Idx, S.NI, Held (F, K3)));
      end loop;
      pragma Assert (Covered (F, S.Hz, S.Idx, S.NI));
      pragma Assert (Valid (S, F));
   end Expire;

   --  A (PA .. PA + Len - 1) = B (PB .. PB + Len - 1), element by element.
   --  Defined by its Post, so that one frame's copy is one atom.
   function Same_Frame
     (A : Byte_Array; PA : Natural; B : Byte_Array; PB : Natural; Len : Natural) return Boolean
   with Ghost, Global => null,
        Pre  => A'First = 0 and then B'First = 0
                and then A'Last <= Log_Max and then B'Last <= Log_Max
                and then PA <= A'Last + 1 and then Len <= A'Last + 1 - PA
                and then PB <= B'Last + 1 and then Len <= B'Last + 1 - PB,
        Post => Same_Frame'Result = (for all K in 0 .. Len - 1 => A (PA + K) = B (PB + K));

   function Same_Frame
     (A : Byte_Array; PA : Natural; B : Byte_Array; PB : Natural; Len : Natural) return Boolean is
   begin
      return (for all K in 0 .. Len - 1 => A (PA + K) = B (PB + K));
   end Same_Frame;

   --  Entry E moved to offset Off.
   function Moved (E : Index_Entry; Off : Log_Size) return Index_Entry is
     (H => E.H, Off => Off, Len => E.Len);

   type Offset_Map is array (Held_Index range <>) of Log_Size;

   --  A frame whose prefix and tag bytes were copied is in place.
   procedure Lemma_Frame_Copied
     (New_Log : Byte_Array; W : Log_Size; Log : Byte_Array; LL : Log_Size;
      A, B : Index_Entry)
   with
     Ghost, Global => null,
     Pre  => New_Log'First = 0 and then W <= New_Log'Last
       and then Log'First = 0 and then LL <= Log'Last
       and then Frame_OK (Log, LL, B)
       and then A.H = B.H and then A.Len = B.Len
       and then End_Of (A) <= W
       and then New_Log (A.Off) = Log (B.Off)
       and then New_Log (A.Off + 1) = Log (B.Off + 1)
       and then New_Log (A.Off + 2) = Log (B.Off + 2)
       and then New_Log (A.Off + 3) = Log (B.Off + 3)
       and then New_Log (A.Off + 4) = Log (B.Off + 4),
     Post => Frame_OK (New_Log, W, A);

   procedure Lemma_Frame_Copied
     (New_Log : Byte_Array; W : Log_Size; Log : Byte_Array; LL : Log_Size;
      A, B : Index_Entry) is null;

   --  The copies, restated from the offsets map to the entries.
   procedure Lemma_Offs_Content
     (New_Log, Log : Byte_Array; LL : Log_Size; Idx, Old : Entry_Array;
      Offs : Offset_Map; N : Held_Count; W : Log_Size)
   with
     Ghost, Global => null,
     Pre  => New_Log'First = 0 and then Log'First = 0
       and then W <= New_Log'Last and then LL <= Log'Last
       and then Idx'First = 1 and then N <= Idx'Last
       and then Old'First = 1 and then N <= Old'Last
       and then Offs'First = 1 and then N <= Offs'Last
       and then (for all J in 1 .. N =>
                   Idx (J).Off = Offs (J) and then Idx (J).Len = Old (J).Len
                   and then Offs (J) + Prefix_Len + Old (J).Len <= W
                   and then End_Of (Old (J)) <= LL)
       and then (for all J in 1 .. N =>
                   (for all K in 0 .. Prefix_Len + Old (J).Len - 1 =>
                      New_Log (Offs (J) + K) = Log (Old (J).Off + K))),
     Post => (for all J in 1 .. N =>
                (for all K in 0 .. Prefix_Len + Idx (J).Len - 1 =>
                   New_Log (Idx (J).Off + K) = Log (Old (J).Off + K)));

   procedure Lemma_Offs_Content
     (New_Log, Log : Byte_Array; LL : Log_Size; Idx, Old : Entry_Array;
      Offs : Offset_Map; N : Held_Count; W : Log_Size) is
   begin
      for J in 1 .. N loop
         pragma Assert (Idx (J).Off = Offs (J));
         pragma Assert
           (for all K in 0 .. Prefix_Len + Old (J).Len - 1 =>
              New_Log (Offs (J) + K) = Log (Old (J).Off + K));
         pragma Assert
           (for all K in 0 .. Prefix_Len + Idx (J).Len - 1 =>
              New_Log (Idx (J).Off + K) = Log (Old (J).Off + K));
         pragma Loop_Invariant
           (for all J2 in 1 .. J =>
              (for all K in 0 .. Prefix_Len + Idx (J2).Len - 1 =>
                 New_Log (Idx (J2).Off + K) = Log (Old (J2).Off + K)));
      end loop;
   end Lemma_Offs_Content;

   --  Every entry's prefix and tag were copied, so the new log is framed.
   procedure Lemma_Framed_All
     (New_Log, Log : Byte_Array; LL : Log_Size; Idx, Old : Entry_Array;
      N : Held_Count; W : Log_Size)
   with
     Ghost, Global => null,
     Pre  => New_Log'First = 0 and then Log'First = 0
       and then W <= New_Log'Last and then LL <= Log'Last
       and then Idx'First = 1 and then N <= Idx'Last
       and then Old'First = 1 and then N <= Old'Last
       and then Framed (Log, LL, Old, N)
       and then (for all J in 1 .. N =>
                   Idx (J).H = Old (J).H and then Idx (J).Len = Old (J).Len
                   and then End_Of (Idx (J)) <= W
                   and then New_Log (Idx (J).Off) = Log (Old (J).Off)
                   and then New_Log (Idx (J).Off + 1) = Log (Old (J).Off + 1)
                   and then New_Log (Idx (J).Off + 2) = Log (Old (J).Off + 2)
                   and then New_Log (Idx (J).Off + 3) = Log (Old (J).Off + 3)
                   and then New_Log (Idx (J).Off + 4) = Log (Old (J).Off + 4)),
     Post => Framed (New_Log, W, Idx, N);

   procedure Lemma_Framed_All
     (New_Log, Log : Byte_Array; LL : Log_Size; Idx, Old : Entry_Array;
      N : Held_Count; W : Log_Size) is
   begin
      for J in 1 .. N loop
         pragma Assert (Frame_OK (Log, LL, Old (J)));
         Lemma_Frame_Copied (New_Log, W, Log, LL, Idx (J), Old (J));
         pragma Loop_Invariant (for all J2 in 1 .. J => Frame_OK (New_Log, W, Idx (J2)));
      end loop;
   end Lemma_Framed_All;

   --  Copy the frames of Idx (1 .. N) from Log into New_Log, contiguously
   --  from offset 0 in index order, and point the entries at the copies.
   procedure Rewrite
     (Log     : Byte_Array;
      LL      : Log_Size;
      Idx     : in out Entry_Array;
      N       : Held_Count;
      New_Log : in out Byte_Array;
      W       : out Log_Size)
   with
     Global => null,
     Pre  => Log'First = 0 and then Log'Last <= Log_Max and then LL <= Log'Last
       and then New_Log'First = 0 and then New_Log'Last = Log'Last
       and then Idx'First = 1 and then N <= Idx'Last
       and then Framed (Log, LL, Idx, N)
       and then Sorted (Idx, N),
     Post => W <= LL
       and then Min_Frame * N <= W
       and then (for all J in 1 .. N =>
                   Idx (J).H = Idx'Old (J).H and then Idx (J).Len = Idx'Old (J).Len)
       and then (if N = 0 then W = 0
                 else Idx (1).Off = 0 and then W = End_Of (Idx (N)))
       and then (for all J in 1 .. N - 1 => Idx (J + 1).Off = End_Of (Idx (J)))
       and then Framed (New_Log, W, Idx, N)
       and then Sorted (Idx, N)
       and then (for all J in 1 .. N => End_Of (Idx'Old (J)) <= LL)
       and then (for all J in 1 .. N => End_Of (Idx (J)) <= W)
       and then (for all J in 1 .. N =>
                   Same_Frame (New_Log, Idx (J).Off, Log, Idx'Old (J).Off,
                               Prefix_Len + Idx (J).Len));

   procedure Rewrite
     (Log     : Byte_Array;
      LL      : Log_Size;
      Idx     : in out Entry_Array;
      N       : Held_Count;
      New_Log : in out Byte_Array;
      W       : out Log_Size)
   is
      Old  : constant Entry_Array := Idx with Ghost;
      Offs : Offset_Map (1 .. N) := [others => 0];
   begin
      W := 0;
      pragma Assert (Framed (Log, LL, Old, N));
      pragma Assert (for all J in 1 .. N => End_Of (Old (J)) <= LL);

      --  1. Copy every frame, recording where it went. Idx is not touched.
      for I in 1 .. N loop
         declare
            From : constant Log_Size := Idx (I).Off;
            Size : constant Positive := Prefix_Len + Idx (I).Len;
            W0   : constant Log_Size := W;
         begin
            pragma Assert (Idx (I) = Old (I));
            pragma Assert (From + Size <= LL);
            pragma Assert (W0 + Size <= LL);
            Offs (I) := W0;
            pragma Assert
              (for all J in 1 .. I - 1 =>
                 (for all K in 0 .. Prefix_Len + Old (J).Len - 1 =>
                    New_Log (Offs (J) + K) = Log (Old (J).Off + K)));
            pragma Assert
              (for all J in 1 .. I - 1 => Offs (J) + Prefix_Len + Old (J).Len <= W0);
            Copy_Bytes (New_Log, W0, Log, From, Size);
            pragma Assert
              (for all J in 1 .. I - 1 =>
                 (for all K in 0 .. Prefix_Len + Old (J).Len - 1 =>
                    New_Log (Offs (J) + K) = Log (Old (J).Off + K)));
            pragma Assert
              (for all K in 0 .. Prefix_Len + Old (I).Len - 1 =>
                 New_Log (Offs (I) + K) = Log (Old (I).Off + K));
            W := W0 + Size;
         end;
         pragma Loop_Invariant (W <= LL);
         pragma Loop_Invariant (Min_Frame * I <= W);
         pragma Loop_Invariant (for all J in I + 1 .. N => W <= Old (J).Off);
         pragma Loop_Invariant
           (Offs (1) = 0 and then W = Offs (I) + Prefix_Len + Old (I).Len);
         pragma Loop_Invariant
           (for all J in 1 .. I - 1 =>
              Offs (J + 1) = Offs (J) + Prefix_Len + Old (J).Len);
         pragma Loop_Invariant
           (for all J in 1 .. I => Offs (J) + Prefix_Len + Old (J).Len <= W);
         pragma Loop_Invariant
           (for all J in 1 .. I =>
              (for all J2 in J + 1 .. I =>
                 Offs (J) + Prefix_Len + Old (J).Len <= Offs (J2)));
         pragma Loop_Invariant
           (for all J in 1 .. I =>
              New_Log (Offs (J)) = Log (Old (J).Off)
              and then New_Log (Offs (J) + 1) = Log (Old (J).Off + 1)
              and then New_Log (Offs (J) + 2) = Log (Old (J).Off + 2)
              and then New_Log (Offs (J) + 3) = Log (Old (J).Off + 3)
              and then New_Log (Offs (J) + 4) = Log (Old (J).Off + 4));
         pragma Loop_Invariant
           (for all J in 1 .. I =>
              (for all K in 0 .. Prefix_Len + Old (J).Len - 1 =>
                 New_Log (Offs (J) + K) = Log (Old (J).Off + K)));
      end loop;
      pragma Assert (W <= LL);

      --  2. Point the entries at the copies.
      for I in 1 .. N loop
         Idx (I).Off := Offs (I);
         pragma Loop_Invariant (for all J in 1 .. I => Idx (J) = Moved (Old (J), Offs (J)));
         pragma Loop_Invariant (for all J in I + 1 .. N => Idx (J) = Old (J));
      end loop;

      pragma Assert (for all J in 1 .. N => Idx (J).Off = Offs (J));
      pragma Assert (for all J in 1 .. N => End_Of (Idx (J)) <= W);
      Lemma_Offs_Content (New_Log, Log, LL, Idx, Old, Offs, N, W);
      pragma Assert
        (for all J in 1 .. N =>
           New_Log (Idx (J).Off) = Log (Old (J).Off)
           and then New_Log (Idx (J).Off + 1) = Log (Old (J).Off + 1)
           and then New_Log (Idx (J).Off + 2) = Log (Old (J).Off + 2)
           and then New_Log (Idx (J).Off + 3) = Log (Old (J).Off + 3)
           and then New_Log (Idx (J).Off + 4) = Log (Old (J).Off + 4));
      Lemma_Framed_All (New_Log, Log, LL, Idx, Old, N, W);
      pragma Assert
        (for all J in 1 .. N =>
           (for all J2 in J + 1 .. N =>
              End_Of (Idx (J)) <= Idx (J2).Off and then Idx (J).H /= Idx (J2).H));
      pragma Assert (Sorted (Idx, N));
      pragma Assert (for all J in 1 .. N => End_Of (Old (J)) <= LL);
      pragma Assert
        (for all J in 1 .. N =>
           (for all K in 0 .. Prefix_Len + Idx (J).Len - 1 =>
              New_Log (Idx (J).Off + K) = Log (Old (J).Off + K)));
      for J in 1 .. N loop
         pragma Assert
           (for all K in 0 .. Prefix_Len + Idx (J).Len - 1 =>
              New_Log (Idx (J).Off + K) = Log (Old (J).Off + K));
         pragma Assert
           (Same_Frame (New_Log, Idx (J).Off, Log, Old (J).Off, Prefix_Len + Idx (J).Len));
         pragma Loop_Invariant
           (for all J2 in 1 .. J =>
              Same_Frame (New_Log, Idx (J2).Off, Log, Old (J2).Off, Prefix_Len + Idx (J2).Len));
      end loop;
   end Rewrite;

   --  An index with the same records (only the offsets moved) is live and
   --  covering when the old one was.
   procedure Lemma_Same_Records
     (F : Frontier.State; Hz : Time64; Old, Idx : Entry_Array; N : Held_Count)
   with
     Ghost, Global => null,
     Pre  => Old'First = 1 and then N <= Old'Last
       and then Idx'First = 1 and then N <= Idx'Last
       and then (for all J in 1 .. N => Idx (J).H = Old (J).H)
       and then Live (F, Hz, Old, N)
       and then Covered (F, Hz, Old, N)
       and then Sorted (Old, N),
     Post => Live (F, Hz, Idx, N) and then Covered (F, Hz, Idx, N);

   procedure Lemma_Same_Records
     (F : Frontier.State; Hz : Time64; Old, Idx : Entry_Array; N : Held_Count) is
   begin
      for J in 1 .. N loop
         pragma Assert (Holds (F, Old (J).H) and then not Expired (Old (J).H, Hz));
         pragma Loop_Invariant
           (for all J2 in 1 .. J =>
              Holds (F, Idx (J2).H) and then not Expired (Idx (J2).H, Hz));
      end loop;
      for K in 1 .. Count (F) loop
         if not Expired (Held (F, K), Hz) then
            declare
               I : constant Held_Index := Entry_Witness (Old, N, Held (F, K));
            begin
               pragma Assert (Idx (I).H = Held (F, K));
            end;
         end if;
         pragma Loop_Invariant
           (for all K2 in 1 .. K =>
              Expired (Held (F, K2), Hz) or else Has_Entry (Idx, N, Held (F, K2)));
      end loop;
   end Lemma_Same_Records;

   --  The frames of S are those of Old_S, entry by entry, byte for byte:
   --  Compact's contract, from one Same_Frame atom per entry.
   procedure Lemma_Same_Frames (S, Old_S : Store) with
     Ghost, Global => null,
     Pre  => Entries (S) = Entries (Old_S)
       and then (for all J in 1 .. S.NI =>
                   End_Of (S.Idx (J)) <= S.LL
                   and then End_Of (Old_S.Idx (J)) <= Old_S.LL
                   and then S.Idx (J).Len = Old_S.Idx (J).Len)
       and then (for all J in 1 .. S.NI =>
                   Same_Frame (S.Log, S.Idx (J).Off, Old_S.Log, Old_S.Idx (J).Off,
                               Prefix_Len + S.Idx (J).Len)),
     Post => (for all I in 1 .. Entries (S) =>
                I <= Entries (Old_S)
                and then End_Of (Entry_At (S, I)) <= Log_Length (S)
                and then End_Of (Entry_At (Old_S, I)) <= Log_Length (Old_S)
                and then (for all K in 0 .. Prefix_Len + Entry_At (S, I).Len - 1 =>
                            Log_Byte (S, Entry_At (S, I).Off + K) =
                              Log_Byte (Old_S, Entry_At (Old_S, I).Off + K)));

   procedure Lemma_Same_Frames (S, Old_S : Store) is
   begin
      for J in 1 .. S.NI loop
         pragma Assert
           (Same_Frame (S.Log, S.Idx (J).Off, Old_S.Log, Old_S.Idx (J).Off,
                        Prefix_Len + S.Idx (J).Len));
         pragma Assert
           (for all K in 0 .. Prefix_Len + S.Idx (J).Len - 1 =>
              S.Log (S.Idx (J).Off + K) = Old_S.Log (Old_S.Idx (J).Off + K));
         pragma Loop_Invariant
           (for all J2 in 1 .. J =>
              (for all K in 0 .. Prefix_Len + S.Idx (J2).Len - 1 =>
                 S.Log (S.Idx (J2).Off + K) = Old_S.Log (Old_S.Idx (J2).Off + K)));
      end loop;
   end Lemma_Same_Frames;

   procedure Compact (S : in out Store; F : Frontier.State) is
      Old_S   : constant Store := S with Ghost;
      New_Log : Byte_Array := S.Log;   --  the rewritten file; its tail is unused
      W       : Log_Size;
   begin
      Rewrite (S.Log, S.LL, S.Idx, S.NI, New_Log, W);
      S.Log := New_Log;
      S.LL := W;

      --  The frames, byte for byte, first, while the context is small.
      pragma Assert
        (for all J in 1 .. S.NI =>
           End_Of (S.Idx (J)) <= S.LL
           and then End_Of (Old_S.Idx (J)) <= Old_S.LL
           and then S.Idx (J).Len = Old_S.Idx (J).Len);
      pragma Assert
        (for all J in 1 .. S.NI =>
           Same_Frame (S.Log, S.Idx (J).Off, Old_S.Log, Old_S.Idx (J).Off,
                       Prefix_Len + S.Idx (J).Len));
      Lemma_Same_Frames (S, Old_S);

      --  The same records, so still live and covering.
      Lemma_Same_Records (F, S.Hz, Old_S.Idx, S.Idx, S.NI);

      --  The new log is exactly the entries' frames, so its chain is their
      --  offsets.
      pragma Assert (Min_Frame * S.NI <= W);
      pragma Assert (S.NI <= S.Log_Cap);
      Set_Bounds (S.Bnd, S.Idx, S.NI);
      S.NB := S.NI;
      Lemma_Chain_Packed (S.Log, S.LL, S.Idx, S.NI, S.Bnd);
      pragma Assert (for all J in 1 .. S.NI => Frame_Start (S, J) = Entry_At (S, J).Off);
      pragma Assert (Valid (S, F));
   end Compact;

   --  Two entries of a sorted index are distinct records.
   procedure Lemma_Sorted_Distinct (Idx : Entry_Array; N : Held_Count; I, J : Held_Index) with
     Ghost, Global => null,
     Pre  => Idx'First = 1 and then N <= Idx'Last
             and then I <= N and then J <= N and then I /= J
             and then Sorted (Idx, N),
     Post => Idx (I).H /= Idx (J).H;

   procedure Lemma_Sorted_Distinct (Idx : Entry_Array; N : Held_Count; I, J : Held_Index) is
   begin
      pragma Assert
        (for all I2 in 1 .. N =>
           (for all J2 in I2 + 1 .. N =>
              End_Of (Idx (I2)) <= Idx (J2).Off and then Idx (I2).H /= Idx (J2).H));
      if I < J then
         pragma Assert (Idx (I).H /= Idx (J).H);
      else
         pragma Assert (Idx (J).H /= Idx (I).H);
      end if;
   end Lemma_Sorted_Distinct;

   --  The entry of a cell's PUT is the only entry on that cell.
   procedure Lemma_Only_Entry (S : Store; F : Frontier.State; J : Held_Index) with
     Ghost, Global => null,
     Pre  => Valid (S, F) and then J <= Entries (S) and then Entry_At (S, J).H.K = K_Put,
     Post => (for all J2 in 1 .. Entries (S) =>
                (if Kome.Views.Put_On (Entry_At (S, J2).H, Entry_At (S, J).H.NS,
                                       Entry_At (S, J).H.Ent, Entry_At (S, J).H.FH)
                 then J2 = J));

   procedure Lemma_Only_Entry (S : Store; F : Frontier.State; J : Held_Index) is
   begin
      for J2 in 1 .. S.NI loop
         if Kome.Views.Put_On (S.Idx (J2).H, S.Idx (J).H.NS, S.Idx (J).H.Ent, S.Idx (J).H.FH) then
            Lemma_Cell_Unique (S, F, J, J2);
         end if;
         pragma Loop_Invariant
           (for all J3 in 1 .. J2 =>
              (if Kome.Views.Put_On (S.Idx (J3).H, S.Idx (J).H.NS, S.Idx (J).H.Ent,
                                     S.Idx (J).H.FH)
               then J3 = J));
      end loop;
   end Lemma_Only_Entry;

   procedure Find_Cell
     (S     : in     Store;
      F     : in     Frontier.State;
      NS    : in     Id128;
      Ent   : in     Id128;
      FH    : in     Key256;
      Found :    out Boolean;
      I     :    out Held_Count) is
   begin
      for J in 1 .. S.NI loop
         if Kome.Views.Put_On (S.Idx (J).H, NS, Ent, FH) then
            Lemma_Only_Entry (S, F, J);
            Found := True;
            I := J;
            return;
         end if;
         pragma Loop_Invariant
           (for all J2 in 1 .. J => not Kome.Views.Put_On (S.Idx (J2).H, NS, Ent, FH));
      end loop;
      Found := False;
      I := 0;
   end Find_Cell;

   ---------------------------------------------------------------------------
   --  The invariant, unpacked.
   ---------------------------------------------------------------------------

   procedure Lemma_Entry_Held (S : Store; F : Frontier.State; I : Held_Index) is
   begin
      pragma Assert (Frame_OK (S.Log, S.LL, S.Idx (I)));
      pragma Assert (At_Bounds (S.Idx, S.NI, S.Bnd, S.NB));
      pragma Assert
        (for all J in 1 .. S.NI => (for some K in 1 .. S.NB => S.Bnd (K) = S.Idx (J).Off));
      pragma Assert (for some K in 1 .. S.NB => S.Bnd (K) = S.Idx (I).Off);
   end Lemma_Entry_Held;

   procedure Lemma_Scan (S : Store; F : Frontier.State) is
   begin
      pragma Assert (Chain (S.Log, S.LL, S.Bnd, S.NB));
      for K in 1 .. S.NB loop
         Lemma_Chain_At (S.Log, S.LL, S.Bnd, S.NB, K);
         pragma Assert (Len_At (S, S.Bnd (K)) = Len_Word (S.Log, S.Bnd (K)));
         pragma Assert (Has_Frame (S, Frame_Start (S, K)));
         pragma Assert
           (if K < S.NB then Next_Offset (S, Frame_Start (S, K)) = Frame_Start (S, K + 1)
            else Next_Offset (S, Frame_Start (S, K)) = Log_Length (S));
         pragma Loop_Invariant (for all K2 in 1 .. K => Has_Frame (S, Frame_Start (S, K2)));
         pragma Loop_Invariant
           (for all K2 in 1 .. K =>
              (for all K3 in 1 .. Frames (S) =>
                 (if K3 = K2 + 1
                  then Next_Offset (S, Frame_Start (S, K2)) = Frame_Start (S, K3))));
         pragma Loop_Invariant
           (if K = Frames (S)
            then Next_Offset (S, Frame_Start (S, K)) = Log_Length (S));
      end loop;
   end Lemma_Scan;

   procedure Lemma_Header_Of (Frame : Byte_Array) is null;

   procedure Lemma_Members_Agree (Frame : Byte_Array; Members : Member_Keys) is null;

   procedure Lemma_Held_Indexed (S : Store; F : Frontier.State; K : Held_Index) is null;

   procedure Lemma_Indexed (S : Store; X : Header) is null;

   procedure Lemma_Cell_Unique (S : Store; F : Frontier.State; I, J : Held_Index) is
      K1 : constant Held_Index := Witness (F, S.Idx (I).H);
      K2 : constant Held_Index := Witness (F, S.Idx (J).H);
   begin
      pragma Assert (Kome.Views.Canonical (Held (F, K1)));
      pragma Assert (Kome.Views.Canonical (Held (F, K2)));
      Kome.Views.Lemma_Cell_Unique (F, K1, K2);
      pragma Assert (S.Idx (I).H = S.Idx (J).H);
      pragma Assert (Sorted (S.Idx, S.NI));
      if I /= J then
         Lemma_Sorted_Distinct (S.Idx, S.NI, I, J);
      end if;
   end Lemma_Cell_Unique;

end Kome.Store;
