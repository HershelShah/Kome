pragma Ada_2022;
package body Kome.Store with SPARK_Mode is

   --  Proof style (CONVENTIONS.md):
   --    * The invariant has parts over explicit components (Live, Covered,
   --      Fresh, Framed, Sorted, Chain, At_Bounds, Head_OK).
   --    * Each step of an operation makes one part true again through a small
   --      ghost lemma.
   --    * Before the proof uses a "some record", a ghost witness function
   --      changes it into a named index.

   ---------------------------------------------------------------------------
   --  The parts of the invariant (their Posts in the spec define them).
   ---------------------------------------------------------------------------

   function Has_Entry (Idx : Entry_Array; N : Held_Count; X : Header) return Boolean is
   begin
      return (for some I in 1 .. N => Idx (I).H = X);
   end Has_Entry;

   function Live (F : Frontier.State; Idx : Entry_Array; N : Held_Count) return Boolean is
   begin
      return (for all I in 1 .. N => Holds (F, Idx (I).H));
   end Live;

   function Covered (F : Frontier.State; Idx : Entry_Array; N : Held_Count) return Boolean is
   begin
      return (for all K in 1 .. Count (F) => Has_Entry (Idx, N, Held (F, K)));
   end Covered;

   function Fresh (F : Frontier.State; Hz : Time64) return Boolean is
   begin
      return (for all K in 1 .. Count (F) => not Expired (Held (F, K), Hz));
   end Fresh;

   function Same_Bytes (A : Store; PA : Natural; B : Store; PB : Natural; Len : Natural)
     return Boolean is
   begin
      return (for all K in 0 .. Len - 1 => Log_Byte (A, PA + K) = Log_Byte (B, PB + K));
   end Same_Bytes;

   function Compact_Index (Old_S, S : Store) return Boolean is
   begin
      return
        ((for all J in 1 .. Entries (Old_S) => Indexed (S, Entry_At (Old_S, J).H))
         and then (for all I in 1 .. Entries (S) =>
                     Indexed (Old_S, Entry_At (S, I).H)
                     and then Entry_At (Old_S, Position (Old_S, Entry_At (S, I).H)).Len
                              = Entry_At (S, I).Len
                     and then End_Of (Entry_At (S, I)) <= Log_Length (S)
                     and then End_Of (Entry_At (Old_S, Position (Old_S, Entry_At (S, I).H)))
                              <= Log_Length (Old_S)
                     and then Same_Bytes (S, Entry_At (S, I).Off,
                                          Old_S,
                                          Entry_At (Old_S, Position (Old_S, Entry_At (S, I).H)).Off,
                                          Apply_Prefix + Entry_At (S, I).Len))
         and then (for all I in 1 .. Entries (S) =>
                     (for all J in I + 1 .. Entries (S) =>
                        (if Is_Data (Entry_At (S, I).H) then Is_Data (Entry_At (S, J).H)))));
   end Compact_Index;

   function Replayed_Prefix
     (Input : Byte_Array; F : Frontier.State; S : Store; VL : Log_Size) return Boolean
   is
   begin
      return
        (Valid (S, F)
         and then VL >= Header_Len
         and then Input'Last < S.Log_Cap
         and then Header_Well_Formed (Input)
         and then Header_Slice (Input) = F.Slice
         and then Log_Length (S) = VL
         and then VL - 1 <= Input'Last
         and then (for all J in 0 .. VL - 1 => Log_Byte (S, J) = Input (J))
         and then Word (Logged_Cap (S)) = Header_Cap (Input)
         and then Logged_Slice (S) = F.Slice
         and then Horizon_Logged (S));
   end Replayed_Prefix;

   function Compact_Layout (Old_S, S : Store) return Boolean is
   begin
      return
        (Log_Length (S) >= Header_Len
         and then Log_Length (Old_S) >= Header_Len
         and then Body_End (S) <= Log_Length (Old_S)
         and then (for all K in 0 .. Header_Len - 1 => Log_Byte (S, K) = Log_Byte (Old_S, K))
         and then (if Entries (S) > 0 then Entry_At (S, 1).Off = Header_Len)
         and then (for all I in 1 .. Entries (S) - 1 =>
                     Entry_At (S, I + 1).Off = End_Of (Entry_At (S, I)))
         and then (for all I in 1 .. Entries (S) =>
                     I + 1 <= Log_Entries (S)
                     and then Entry_Start (S, I + 1) = Entry_At (S, I).Off)
         and then (if Horizon (S) >= 0 and then S.Log_Cap - Body_End (S) >= Expire_Len
                   then Log_Length (S) >= Body_End (S)
                        and then Log_Length (S) - Body_End (S) = Expire_Len
                        and then Log_Entries (S) = Entries (S) + 2
                        and then Op_At (S, Body_End (S)) = Op_Expire
                        and then Code_At (S, Body_End (S) + 1) = Horizon_Code (Horizon (S))
                   else Log_Length (S) = Body_End (S)
                        and then Log_Entries (S) = Entries (S) + 1)
         and then (if Horizon (S) >= 0 and then Log_Length (S) = Body_End (S)
                   then Log_Length (Old_S) - Body_End (S) < Expire_Len));
   end Compact_Layout;

   function Frame_OK (Log : Byte_Array; LL : Log_Size; E : Index_Entry) return Boolean is
   begin
      return E.Off >= Header_Len
        and then E.Off <= LL
        and then LL - E.Off >= Apply_Prefix + E.Len
        and then Log (E.Off) = Op_Apply
        and then Len_Word (Log, E.Off) = Word (E.Len)
        and then Log (E.Off + Apply_Prefix) = Kome.Records.Tag_Of (E.H.K);
   end Frame_OK;

   function Entry_OK (Log : Byte_Array; LL : Log_Size; P : Natural) return Boolean is
   begin
      return LL <= Log'Last
        and then P < LL
        and then (if Log (P) = Op_Header then LL - P >= Header_Len
                  elsif Log (P) = Op_Expire then LL - P >= Expire_Len
                  elsif Log (P) = Op_Apply or else Log (P) = Op_Apply_Expired
                  then LL - P >= Apply_Prefix
                       and then Len_Word (Log, P) in 1 .. Kome.Records.Frame_Max
                       and then Natural (Len_Word (Log, P)) <= LL - P - Apply_Prefix
                  else False);
   end Entry_OK;

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

   function Chain (Log : Byte_Array; LL : Log_Size; Bnd : Offset_Array; NB : Natural)
     return Boolean is
   begin
      return NB >= 1
        and then NB <= LL / Min_Entry
        and then Bnd (1) = 0
        and then (for all K in 1 .. NB =>
                    Entry_OK (Log, LL, Bnd (K))
                    and then (Log (Bnd (K)) = Op_Header) = (K = 1)
                    and then Bnd (K) + Size_At (Log, Bnd (K)) =
                               (if K < NB then Bnd (K + 1) else LL));
   end Chain;

   function At_Bounds (Idx : Entry_Array; N : Held_Count; Bnd : Offset_Array; NB : Natural)
     return Boolean is
   begin
      return (for all I in 1 .. N => (for some K in 1 .. NB => Bnd (K) = Idx (I).Off));
   end At_Bounds;

   function Head_OK
     (Log : Byte_Array; LL : Log_Size; NSb : NS_Id; Root : Pubkey; Slt : Salt;
      DCap : Data_Size; Slc : Slice_Count) return Boolean is
   begin
      return LL >= Header_Len
        and then Log (0) = Op_Header
        and then (for all J in 0 .. Magic_Len - 1 => Log (HO_Magic + J) = Magic (J))
        and then Log (HO_Version) = Log_Version
        and then (for all J in 0 .. NS_Len - 1 => Log (HO_NS + J) = NSb (J))
        and then (for all J in 0 .. Pubkey_Len - 1 => Log (HO_Root + J) = Root (J))
        and then (for all J in 0 .. Salt_Len - 1 => Log (HO_Salt + J) = Slt (J))
        and then Kome.Keys.Word_Of (Log (HO_Cap), Log (HO_Cap + 1),
                                    Log (HO_Cap + 2), Log (HO_Cap + 3)) = Word (DCap)
        and then Kome.Records.U16_Of (Log (HO_Slice), Log (HO_Slice + 1)) = Slc;
   end Head_OK;

   ---------------------------------------------------------------------------
   --  Ghost witnesses.
   ---------------------------------------------------------------------------

   --  A map from positions to positions (witnesses, sources, targets).
   type Index_Map is array (Held_Index range <>) of Held_Count;

   --  A map from index positions to chain positions.
   type Pos_Map is array (Held_Index range <>) of Natural;

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

   function Position (S : Store; X : Header) return Held_Index is
   begin
      for I in 1 .. Entries (S) loop
         if S.Idx (I).H = X then
            return I;
         end if;
         pragma Loop_Invariant (for all J in 1 .. I => S.Idx (J).H /= X);
      end loop;
      pragma Assert (False);
      return 1;
   end Position;

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

   ---------------------------------------------------------------------------
   --  The HEADER and the chain of entries.
   ---------------------------------------------------------------------------

   --  The HEADER reads only bytes below Header_Len. An append keeps these
   --  bytes.
   procedure Lemma_Head_Grow
     (Log1 : Byte_Array; LL1 : Log_Size; Log2 : Byte_Array; LL2 : Log_Size;
      NSb  : NS_Id; Root : Pubkey; Slt : Salt; DCap : Data_Size; Slc : Slice_Count)
   with
     Ghost, Global => null,
     Pre  => Log1'First = 0 and then LL1 <= Log1'Last
             and then Log2'First = 0 and then LL2 <= Log2'Last
             and then LL2 >= Header_Len
             and then Head_OK (Log1, LL1, NSb, Root, Slt, DCap, Slc)
             and then (for all P in 0 .. Header_Len - 1 => Log2 (P) = Log1 (P)),
     Post => Head_OK (Log2, LL2, NSb, Root, Slt, DCap, Slc);

   procedure Lemma_Head_Grow
     (Log1 : Byte_Array; LL1 : Log_Size; Log2 : Byte_Array; LL2 : Log_Size;
      NSb  : NS_Id; Root : Pubkey; Slt : Salt; DCap : Data_Size; Slc : Slice_Count) is
   begin
      pragma Assert (Log2 (0) = Log1 (0));
      pragma Assert (for all J in 0 .. Magic_Len - 1 => Log2 (HO_Magic + J) = Magic (J));
      pragma Assert (Log2 (HO_Version) = Log_Version);
      pragma Assert (for all J in 0 .. NS_Len - 1 => Log2 (HO_NS + J) = NSb (J));
      pragma Assert (for all J in 0 .. Pubkey_Len - 1 => Log2 (HO_Root + J) = Root (J));
      pragma Assert (for all J in 0 .. Salt_Len - 1 => Log2 (HO_Salt + J) = Slt (J));
      pragma Assert (Log2 (HO_Cap) = Log1 (HO_Cap));
      pragma Assert (Log2 (HO_Cap + 1) = Log1 (HO_Cap + 1));
      pragma Assert (Log2 (HO_Cap + 2) = Log1 (HO_Cap + 2));
      pragma Assert (Log2 (HO_Cap + 3) = Log1 (HO_Cap + 3));
      pragma Assert (Log2 (HO_Slice) = Log1 (HO_Slice));
      pragma Assert (Log2 (HO_Slice + 1) = Log1 (HO_Slice + 1));
   end Lemma_Head_Grow;

   --  The K-th entry of a chain.
   procedure Lemma_Chain_At
     (Log : Byte_Array; LL : Log_Size; Bnd : Offset_Array; NB : Natural; K : Positive)
   with
     Ghost, Global => null,
     Pre  => Log'First = 0 and then LL <= Log'Last
             and then Bnd'First = 1 and then NB <= Bnd'Last and then K <= NB
             and then Chain (Log, LL, Bnd, NB),
     Post => Entry_OK (Log, LL, Bnd (K))
       and then (Log (Bnd (K)) = Op_Header) = (K = 1)
       and then Bnd (K) + Size_At (Log, Bnd (K)) = (if K < NB then Bnd (K + 1) else LL)
       and then Bnd (1) = 0;

   procedure Lemma_Chain_At
     (Log : Byte_Array; LL : Log_Size; Bnd : Offset_Array; NB : Natural; K : Positive) is null;

   --  An entry of a log stays an entry of the same size when the log grows
   --  after it.
   procedure Lemma_Entry_Same
     (Log1 : Byte_Array; LL1 : Log_Size; Log2 : Byte_Array; LL2 : Log_Size; P : Natural)
   with
     Ghost, Global => null,
     Pre  => Log1'First = 0 and then LL1 <= Log1'Last
             and then Log2'First = 0 and then LL2 <= Log2'Last
             and then LL1 <= LL2
             and then (for all Q in 0 .. LL1 - 1 => Log2 (Q) = Log1 (Q))
             and then Entry_OK (Log1, LL1, P)
             and then P + Size_At (Log1, P) <= LL1,
     Post => Entry_OK (Log2, LL2, P)
             and then Size_At (Log2, P) = Size_At (Log1, P)
             and then Log2 (P) = Log1 (P);

   procedure Lemma_Entry_Same
     (Log1 : Byte_Array; LL1 : Log_Size; Log2 : Byte_Array; LL2 : Log_Size; P : Natural) is
   begin
      pragma Assert (Log2 (P) = Log1 (P));
      if Log1 (P) = Op_Apply or else Log1 (P) = Op_Apply_Expired then
         pragma Assert (P + 4 < LL1);
         pragma Assert (Log2 (P + 1) = Log1 (P + 1));
         pragma Assert (Log2 (P + 2) = Log1 (P + 2));
         pragma Assert (Log2 (P + 3) = Log1 (P + 3));
         pragma Assert (Log2 (P + 4) = Log1 (P + 4));
         pragma Assert (Len_Word (Log2, P) = Len_Word (Log1, P));
      end if;
   end Lemma_Entry_Same;

   --  An append of one entry at LL1 adds that entry to the chain.
   procedure Lemma_Chain_Grow
     (Log1 : Byte_Array; LL1 : Log_Size; Log2 : Byte_Array; LL2 : Log_Size;
      Bnd1 : Offset_Array; NB1 : Natural; Bnd2 : Offset_Array)
   with
     Ghost, Global => null,
     Pre  => Log1'First = 0 and then LL1 <= Log1'Last
       and then Log2'First = 0 and then LL2 <= Log2'Last
       and then Bnd1'First = 1 and then NB1 <= Bnd1'Last
       and then Bnd2'First = 1 and then NB1 < Bnd2'Last
       and then LL1 < LL2
       and then (for all P in 0 .. LL1 - 1 => Log2 (P) = Log1 (P))
       and then Entry_OK (Log2, LL2, LL1)
       and then Log2 (LL1) /= Op_Header
       and then LL1 + Size_At (Log2, LL1) = LL2
       and then Size_At (Log2, LL1) >= Min_Entry
       and then Chain (Log1, LL1, Bnd1, NB1)
       and then (for all K in 1 .. NB1 => Bnd2 (K) = Bnd1 (K))
       and then Bnd2 (NB1 + 1) = LL1,
     Post => Chain (Log2, LL2, Bnd2, NB1 + 1);

   procedure Lemma_Chain_Grow
     (Log1 : Byte_Array; LL1 : Log_Size; Log2 : Byte_Array; LL2 : Log_Size;
      Bnd1 : Offset_Array; NB1 : Natural; Bnd2 : Offset_Array) is
   begin
      for K in 1 .. NB1 loop
         Lemma_Chain_At (Log1, LL1, Bnd1, NB1, K);
         Lemma_Entry_Same (Log1, LL1, Log2, LL2, Bnd1 (K));
         pragma Assert (Entry_OK (Log2, LL2, Bnd2 (K)));
         pragma Assert ((Log2 (Bnd2 (K)) = Op_Header) = (K = 1));
         pragma Assert (Bnd2 (K) + Size_At (Log2, Bnd2 (K)) = Bnd2 (K + 1));
         pragma Loop_Invariant
           (for all J in 1 .. K =>
              Entry_OK (Log2, LL2, Bnd2 (J))
              and then (Log2 (Bnd2 (J)) = Op_Header) = (J = 1)
              and then Bnd2 (J) + Size_At (Log2, Bnd2 (J)) = Bnd2 (J + 1));
      end loop;
      pragma Assert (Entry_OK (Log2, LL2, Bnd2 (NB1 + 1)));
      pragma Assert (Bnd2 (NB1 + 1) + Size_At (Log2, Bnd2 (NB1 + 1)) = LL2);
      pragma Assert (Bnd2 (1) = 0);
      pragma Assert (NB1 <= LL1 / Min_Entry);
      pragma Assert (NB1 + 1 <= LL2 / Min_Entry);
   end Lemma_Chain_Grow;

   ---------------------------------------------------------------------------
   --  Append entries.
   ---------------------------------------------------------------------------

   --  Log (P .. P + Frame'Length - 1) contains Frame. Its Post defines it.
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

   --  Log (P .. P + Frame'Length - 1) := Frame; nothing else changes.
   procedure Write_Frame (Log : in out Byte_Array; P : Natural; Frame : Byte_Array) with
     Global => null,
     Pre  => Log'First = 0 and then Log'Last <= Log_Max
             and then Frame'Length in Frame_Size
             and then P <= Log'Last and then Frame'Length - 1 <= Log'Last - P,
     Post => (for all Q in Log'Range =>
                (if Q < P or else Q > P + Frame'Length - 1 then Log (Q) = Log'Old (Q)))
       and then Log (P) = Frame (Frame'First)
       and then Bytes_At (Log, P, Frame);

   procedure Write_Frame (Log : in out Byte_Array; P : Natural; Frame : Byte_Array) is
   begin
      for K in 0 .. Frame'Length - 1 loop
         Log (P + K) := Frame (Frame'First + K);
         pragma Loop_Invariant
           (for all Q in Log'Range =>
              (if Q < P or else Q > P + Frame'Length - 1 then Log (Q) = Log'Loop_Entry (Q)));
         pragma Loop_Invariant
           (for all K2 in 0 .. K => Log (P + K2) = Frame (Frame'First + K2));
      end loop;
      pragma Assert (Bytes_At (Log, P, Frame));
   end Write_Frame;

   --  Append  Op ‖ len:u32 ‖ Frame  to the log and its offset to the chain.
   procedure Append_Apply
     (Log   : in out Byte_Array; LL : in out Log_Size;
      Bnd   : in out Offset_Array; NB : in out Log_Size;
      Op    : Byte;
      Frame : Byte_Array)
   with
     Global => null,
     Pre  => Log'First = 0 and then LL <= Log'Last and then Log'Last <= Log_Max
             and then Bnd'First = 1 and then Bnd'Last >= Log'Last / Min_Entry and then NB <= Bnd'Last
             and then (Op = Op_Apply or else Op = Op_Apply_Expired)
             and then Frame'Length in Frame_Size
             and then Apply_Prefix + Frame'Length <= Log'Last - LL
             and then Chain (Log, LL, Bnd, NB),
     Post => LL = LL'Old + Apply_Prefix + Frame'Length
       and then (for all P in 0 .. LL'Old - 1 => Log (P) = Log'Old (P))
       and then Log (LL'Old) = Op
       and then Len_Word (Log, LL'Old) = Word (Frame'Length)
       and then Kome.Keys.Word_Of (Log (LL'Old + 1), Log (LL'Old + 2),
                                   Log (LL'Old + 3), Log (LL'Old + 4)) = Word (Frame'Length)
       and then Log (LL'Old + Apply_Prefix) = Frame (Frame'First)
       and then (for all K in 0 .. Frame'Length - 1 =>
                   Log (LL'Old + Apply_Prefix + K) = Frame (Frame'First + K))
       and then NB = NB'Old + 1
       and then NB <= Bnd'Last
       and then Bnd (NB) = LL'Old
       and then (for all K in 1 .. NB'Old => Bnd (K) = Bnd'Old (K))
       and then Chain (Log, LL, Bnd, NB);

   procedure Append_Apply
     (Log   : in out Byte_Array; LL : in out Log_Size;
      Bnd   : in out Offset_Array; NB : in out Log_Size;
      Op    : Byte;
      Frame : Byte_Array)
   is
      Old_Log : constant Byte_Array := Log with Ghost;
      Old_Bnd : constant Offset_Array := Bnd with Ghost;
      Old_NB  : constant Log_Size := NB;
      P       : constant Log_Size := LL;
      W       : constant Word := Word (Frame'Length);
      B0      : constant Byte := Kome.Keys.Byte_Of_Word (W, 0);
      B1      : constant Byte := Kome.Keys.Byte_Of_Word (W, 1);
      B2      : constant Byte := Kome.Keys.Byte_Of_Word (W, 2);
      B3      : constant Byte := Kome.Keys.Byte_Of_Word (W, 3);
   begin
      pragma Assert (Old_NB <= P / Min_Entry);
      --  AUDIT.md G15: the new entry has at least Min_Entry bytes, so the
      --  chain has a slot for it.
      pragma Assert (P + Min_Entry <= Log'Last);
      pragma Assert (P / Min_Entry + 1 <= Log'Last / Min_Entry);
      pragma Assert (Old_NB < Bnd'Last);
      Kome.Keys.Lemma_Word_Round_Trip (W);
      pragma Assert (Kome.Keys.Word_Of (B0, B1, B2, B3) = W);
      Log (P)     := Op;
      Log (P + 1) := B0;
      Log (P + 2) := B1;
      Log (P + 3) := B2;
      Log (P + 4) := B3;
      pragma Assert (for all Q in 0 .. P - 1 => Log (Q) = Old_Log (Q));
      Write_Frame (Log, P + Apply_Prefix, Frame);
      pragma Assert (for all Q in 0 .. P - 1 => Log (Q) = Old_Log (Q));
      pragma Assert (Log (P) = Op and then Log (P + 1) = B0 and then Log (P + 2) = B1
                     and then Log (P + 3) = B2 and then Log (P + 4) = B3);
      LL := P + Apply_Prefix + Frame'Length;
      pragma Assert (Len_Word (Log, P) = W);
      pragma Assert
        (for all K in 0 .. Frame'Length - 1 =>
           Log (P + Apply_Prefix + K) = Frame (Frame'First + K));
      pragma Assert (Entry_OK (Log, LL, P));
      pragma Assert (Size_At (Log, P) = Apply_Prefix + Frame'Length);
      NB := NB + 1;
      Bnd (NB) := P;
      Lemma_Chain_Grow (Old_Log, P, Log, LL, Old_Bnd, Old_NB, Bnd);
   end Append_Apply;

   --  Append  op 3 ‖ Code:u48  to the log and its offset to the chain.
   procedure Append_Expire
     (Log  : in out Byte_Array; LL : in out Log_Size;
      Bnd  : in out Offset_Array; NB : in out Log_Size;
      Code : U48)
   with
     Global => null,
     Pre  => Log'First = 0 and then LL <= Log'Last and then Log'Last <= Log_Max
             and then Bnd'First = 1 and then Bnd'Last >= Log'Last / Min_Entry and then NB <= Bnd'Last
             and then Expire_Len <= Log'Last - LL
             and then Chain (Log, LL, Bnd, NB),
     Post => LL = LL'Old + Expire_Len
       and then (for all P in 0 .. LL'Old - 1 => Log (P) = Log'Old (P))
       and then Log (LL'Old) = Op_Expire
       and then Kome.Records.U48_Of (Log (LL'Old + 1), Log (LL'Old + 2), Log (LL'Old + 3),
                                     Log (LL'Old + 4), Log (LL'Old + 5), Log (LL'Old + 6))
                = Code
       and then NB = NB'Old + 1
       and then NB <= Bnd'Last
       and then Bnd (NB) = LL'Old
       and then (for all K in 1 .. NB'Old => Bnd (K) = Bnd'Old (K))
       and then Chain (Log, LL, Bnd, NB);

   procedure Append_Expire
     (Log  : in out Byte_Array; LL : in out Log_Size;
      Bnd  : in out Offset_Array; NB : in out Log_Size;
      Code : U48)
   is
      Old_Log : constant Byte_Array := Log with Ghost;
      Old_Bnd : constant Offset_Array := Bnd with Ghost;
      Old_NB  : constant Log_Size := NB;
      P       : constant Log_Size := LL;
   begin
      pragma Assert (Old_NB <= P / Min_Entry);
      pragma Assert (P + Min_Entry <= Log'Last);
      pragma Assert (P / Min_Entry + 1 <= Log'Last / Min_Entry);
      pragma Assert (Old_NB < Bnd'Last);
      Kome.Records.Lemma_U48_Round_Trip (Code);
      Log (P)     := Op_Expire;
      Log (P + 1) := Kome.Records.Byte_Of_U48 (Code, 0);
      Log (P + 2) := Kome.Records.Byte_Of_U48 (Code, 1);
      Log (P + 3) := Kome.Records.Byte_Of_U48 (Code, 2);
      Log (P + 4) := Kome.Records.Byte_Of_U48 (Code, 3);
      Log (P + 5) := Kome.Records.Byte_Of_U48 (Code, 4);
      Log (P + 6) := Kome.Records.Byte_Of_U48 (Code, 5);
      LL := P + Expire_Len;
      pragma Assert (for all Q in 0 .. P - 1 => Log (Q) = Old_Log (Q));
      pragma Assert (Entry_OK (Log, LL, P));
      pragma Assert (Size_At (Log, P) = Expire_Len);
      NB := NB + 1;
      Bnd (NB) := P;
      Lemma_Chain_Grow (Old_Log, P, Log, LL, Old_Bnd, Old_NB, Bnd);
   end Append_Expire;

   ---------------------------------------------------------------------------
   --  Index lemmas.
   ---------------------------------------------------------------------------

   --  Each entry of Idx (1 .. N) is an entry of Old (1 .. N0). Its Post
   --  defines it, so it stays one atom in goals that carry it along.
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

   --  An append to the log keeps the APPLY of each entry.
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
         pragma Assert (Idx (J).Off + Apply_Prefix < LL1);
         pragma Assert (Log2 (Idx (J).Off) = Log1 (Idx (J).Off));
         pragma Assert (Log2 (Idx (J).Off + 1) = Log1 (Idx (J).Off + 1));
         pragma Assert (Log2 (Idx (J).Off + 2) = Log1 (Idx (J).Off + 2));
         pragma Assert (Log2 (Idx (J).Off + 3) = Log1 (Idx (J).Off + 3));
         pragma Assert (Log2 (Idx (J).Off + 4) = Log1 (Idx (J).Off + 4));
         pragma Assert (Log2 (Idx (J).Off + 5) = Log1 (Idx (J).Off + 5));
         pragma Assert (Len_Word (Log2, Idx (J).Off) = Len_Word (Log1, Idx (J).Off));
         pragma Assert (Frame_OK (Log2, LL2, Idx (J)));
         pragma Loop_Invariant (for all J2 in 1 .. J => Frame_OK (Log2, LL2, Idx (J2)));
      end loop;
   end Lemma_Framed_Grow;

   --  At_Bounds from an explicit witness: the APPLY of entry J is the
   --  Wit (J)-th entry of the chain.
   procedure Lemma_At_Bounds_Of
     (Idx : Entry_Array; N : Held_Count; Bnd : Offset_Array; NB : Natural; Wit : Pos_Map)
   with
     Ghost, Global => null,
     Pre  => Idx'First = 1 and then N <= Idx'Last
       and then Bnd'First = 1 and then NB <= Bnd'Last
       and then Wit'First = 1 and then N <= Wit'Last
       and then (for all J in 1 .. N => Wit (J) in 1 .. NB and then Bnd (Wit (J)) = Idx (J).Off),
     Post => At_Bounds (Idx, N, Bnd, NB);

   procedure Lemma_At_Bounds_Of
     (Idx : Entry_Array; N : Held_Count; Bnd : Offset_Array; NB : Natural; Wit : Pos_Map) is
   begin
      for J in 1 .. N loop
         pragma Assert (Bnd (Wit (J)) = Idx (J).Off);
         pragma Assert (for some K in 1 .. NB => Bnd (K) = Idx (J).Off);
         pragma Loop_Invariant
           (for all J2 in 1 .. J => (for some K in 1 .. NB => Bnd (K) = Idx (J2).Off));
      end loop;
   end Lemma_At_Bounds_Of;

   --  Entries keep their place on the chain when the chain grows.
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
      Bnd1 : Offset_Array; NB1 : Natural; Bnd2 : Offset_Array; NB2 : Natural)
   is
      Wit : Pos_Map (1 .. N) := [others => 0];
   begin
      pragma Assert
        (for all J in 1 .. N => (for some K in 1 .. NB1 => Bnd1 (K) = Idx (J).Off));
      for J in 1 .. N loop
         Wit (J) := Bound_Witness (Idx, N, Bnd1, NB1, J);
         pragma Loop_Invariant
           (for all J2 in 1 .. J => Wit (J2) in 1 .. NB1 and then Bnd1 (Wit (J2)) = Idx (J2).Off);
      end loop;
      pragma Assert
        (for all J in 1 .. N => Wit (J) in 1 .. NB2 and then Bnd2 (Wit (J)) = Idx (J).Off);
      Lemma_At_Bounds_Of (Idx, N, Bnd2, NB2, Wit);
   end Lemma_Bounds_Grow;

   --  A new last entry at the last entry of the chain.
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
      Bnd : Offset_Array; NB : Natural)
   is
      Wit : Pos_Map (1 .. N) := [others => 0];
   begin
      pragma Assert
        (for all J in 1 .. N0 => (for some K in 1 .. NB => Bnd (K) = Old (J).Off));
      for J in 1 .. N0 loop
         Wit (J) := Bound_Witness (Old, N0, Bnd, NB, J);
         pragma Loop_Invariant
           (for all J2 in 1 .. J => Wit (J2) in 1 .. NB and then Bnd (Wit (J2)) = Idx (J2).Off);
      end loop;
      Wit (N) := NB;
      pragma Assert
        (for all J in 1 .. N => Wit (J) in 1 .. NB and then Bnd (Wit (J)) = Idx (J).Off);
      Lemma_At_Bounds_Of (Idx, N, Bnd, NB, Wit);
   end Lemma_Bounds_Push;

   --  If the APPLYs of an index are on the chain, then the APPLYs of the
   --  entries picked from that index are also on the chain.
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
      Bnd : Offset_Array; NB : Natural)
   is
      Wit : Pos_Map (1 .. N) := [others => 0];
   begin
      pragma Assert (for all J in 1 .. N => (for some I in 1 .. N0 => Idx (J) = Old (I)));
      pragma Assert
        (for all J in 1 .. N0 => (for some K in 1 .. NB => Bnd (K) = Old (J).Off));
      for J in 1 .. N loop
         Wit (J) := Bound_Witness (Old, N0, Bnd, NB, Same_Witness (Idx, N, Old, N0, J));
         pragma Loop_Invariant
           (for all J2 in 1 .. J => Wit (J2) in 1 .. NB and then Bnd (Wit (J2)) = Idx (J2).Off);
      end loop;
      Lemma_At_Bounds_Of (Idx, N, Bnd, NB, Wit);
   end Lemma_Bounds_Sub;

   ---------------------------------------------------------------------------
   --  Filter the index.
   ---------------------------------------------------------------------------

   --  The entries that a filter drops: the entries that R dominates, or the
   --  DELs that are expired at Hz.
   type Drop_Rule is record
      By_Dom : Boolean := True;
      R      : Header;
      Hz     : Time64  := No_Horizon;
   end record;

   function Drops_H (D : Drop_Rule; X : Header) return Boolean is
     (if D.By_Dom then Dominates (D.R, X) else Expired (X, D.Hz));

   function Drops (D : Drop_Rule; E : Index_Entry) return Boolean is (Drops_H (D, E.H));

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

   --  Remove the entries that D drops, and keep the other entries in
   --  order.
   procedure Filter (Idx : in out Entry_Array; N : in out Held_Count; D : Drop_Rule) with
     Global => null,
     Pre  => Idx'First = 1 and then N <= Idx'Last,
     Post => N <= N'Old
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
      --  Src (J): the old position of kept entry J. Dst (I): the new position
      --  of old entry I (0 if it was dropped).
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
      end loop;
      Lemma_Sorted_Sub (Old, N0, Idx, Kept, Src);
      pragma Assert
        (for all J in 1 .. Kept => (for some I in 1 .. N0 => Idx (J) = Old (I)));
      pragma Assert (Sub (Idx, Kept, Old, N0));
      N := Kept;
   end Filter;

   --  A new last entry after the APPLY of each entry, with a new record,
   --  keeps the index sorted.
   procedure Lemma_Sorted_Push
     (Old : Entry_Array; N0 : Held_Count; Idx : Entry_Array; N : Held_Count)
   with
     Ghost, Global => null,
     Pre  => Old'First = 1 and then N0 <= Old'Last
       and then Idx'First = 1 and then N <= Idx'Last
       and then N = N0 + 1
       and then Sorted (Old, N0)
       and then (for all J in 1 .. N0 => Idx (J) = Old (J))
       and then (for all J in 1 .. N0 =>
                   End_Of (Old (J)) <= Idx (N).Off and then Old (J).H /= Idx (N).H),
     Post => Sorted (Idx, N);

   procedure Lemma_Sorted_Push
     (Old : Entry_Array; N0 : Held_Count; Idx : Entry_Array; N : Held_Count) is
   begin
      pragma Assert
        (for all I in 1 .. N0 =>
           (for all J in I + 1 .. N0 =>
              End_Of (Old (I)) <= Old (J).Off and then Old (I).H /= Old (J).H));
      pragma Assert
        (for all I in 1 .. N =>
           (for all J in I + 1 .. N =>
              End_Of (Idx (I)) <= Idx (J).Off and then Idx (I).H /= Idx (J).H));
   end Lemma_Sorted_Push;

   ---------------------------------------------------------------------------
   --  The lattice side of a step: what the Posts of Frontier give the
   --  index.
   ---------------------------------------------------------------------------

   --  Kept entries were held and were not dropped, so they are held
   --  after a step that keeps each record that it does not drop.
   procedure Lemma_Live_Kept
     (Old_F, New_F : Frontier.State; D : Drop_Rule;
      Old : Entry_Array; N0 : Held_Count; Idx : Entry_Array; N : Held_Count)
   with
     Ghost, Global => null,
     Pre  => Idx'First = 1 and then N <= Idx'Last
       and then Old'First = 1 and then N0 <= Old'Last
       and then Live (Old_F, Old, N0)
       and then Sub (Idx, N, Old, N0)
       and then (for all J in 1 .. N => not Drops (D, Idx (J)))
       and then (for all I in 1 .. Count (Old_F) =>
                   Holds (New_F, Held (Old_F, I)) or else Drops_H (D, Held (Old_F, I))),
     Post => Live (New_F, Idx, N);

   procedure Lemma_Live_Kept
     (Old_F, New_F : Frontier.State; D : Drop_Rule;
      Old : Entry_Array; N0 : Held_Count; Idx : Entry_Array; N : Held_Count) is
   begin
      pragma Assert (for all J in 1 .. N => (for some I in 1 .. N0 => Idx (J) = Old (I)));
      pragma Assert (for all I in 1 .. N0 => Holds (Old_F, Old (I).H));
      for J in 1 .. N loop
         declare
            I : constant Held_Index := Same_Witness (Idx, N, Old, N0, J);
            K : constant Held_Index := Witness (Old_F, Old (I).H);
         begin
            pragma Assert (Held (Old_F, K) = Idx (J).H);
            pragma Assert (not Drops_H (D, Held (Old_F, K)));
            pragma Assert (Holds (New_F, Held (Old_F, K)));
         end;
         pragma Loop_Invariant (for all J2 in 1 .. J => Holds (New_F, Idx (J2).H));
      end loop;
   end Lemma_Live_Kept;

   --  A record that is not held is not an entry of a live index, or of a
   --  part of a live index.
   procedure Lemma_Not_Indexed
     (F   : Frontier.State;
      Old : Entry_Array; N0 : Held_Count; Idx : Entry_Array; N : Held_Count;
      R   : Header)
   with
     Ghost, Global => null,
     Pre  => Idx'First = 1 and then N <= Idx'Last
       and then Old'First = 1 and then N0 <= Old'Last
       and then Live (F, Old, N0)
       and then Sub (Idx, N, Old, N0)
       and then not Holds (F, R),
     Post => (for all J in 1 .. N => Idx (J).H /= R);

   procedure Lemma_Not_Indexed
     (F   : Frontier.State;
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

   --  In a frontier that holds R, R dominates no held record (T2': the
   --  held set is its own frontier).
   procedure Lemma_Apply_Kept (Old_F, New_F : Frontier.State; R : Header) with
     Ghost, Global => null,
     Pre  => Is_Frontier (New_F)
       and then Holds (New_F, R)
       and then (for all I in 1 .. Count (New_F) =>
                   Holds (Old_F, Held (New_F, I)) or else Held (New_F, I) = R),
     Post => (for all K in 1 .. Count (New_F) =>
                Held (New_F, K) = R
                or else (Holds (Old_F, Held (New_F, K))
                         and then not Dominates (R, Held (New_F, K))));

   procedure Lemma_Apply_Kept (Old_F, New_F : Frontier.State; R : Header) is
      KR : constant Held_Index := Witness (New_F, R);
   begin
      for K in 1 .. Count (New_F) loop
         Lemma_Frontier_Held (New_F, K);
         pragma Assert (not Dominates (Held (New_F, KR), Held (New_F, K)));
         pragma Loop_Invariant
           (for all K2 in 1 .. K =>
              Held (New_F, K2) = R
              or else (Holds (Old_F, Held (New_F, K2))
                       and then not Dominates (R, Held (New_F, K2))));
      end loop;
   end Lemma_Apply_Kept;

   --  Covered after a step: each record that is held after the step is the
   --  applied record R (indexed), or it was held before and is not dropped.
   --  In the second case, its entry was kept.
   procedure Lemma_Covered_Kept
     (Old_F, New_F : Frontier.State; D : Drop_Rule;
      Old : Entry_Array; N0 : Held_Count; Idx : Entry_Array; N : Held_Count)
   with
     Ghost, Global => null,
     Pre  => Idx'First = 1 and then N <= Idx'Last
       and then Old'First = 1 and then N0 <= Old'Last
       and then Covered (Old_F, Old, N0)
       and then (for all I in 1 .. N0 =>
                   (if not Drops (D, Old (I)) then Has_Entry (Idx, N, Old (I).H)))
       and then (for all K in 1 .. Count (New_F) =>
                   (D.By_Dom and then Held (New_F, K) = D.R)
                   or else (Holds (Old_F, Held (New_F, K))
                            and then not Drops_H (D, Held (New_F, K))))
       and then (if D.By_Dom and then Holds (New_F, D.R) then Has_Entry (Idx, N, D.R)),
     Post => Covered (New_F, Idx, N);

   procedure Lemma_Covered_Kept
     (Old_F, New_F : Frontier.State; D : Drop_Rule;
      Old : Entry_Array; N0 : Held_Count; Idx : Entry_Array; N : Held_Count) is
   begin
      for K in 1 .. Count (New_F) loop
         if D.By_Dom and then Held (New_F, K) = D.R then
            pragma Assert (Holds (New_F, D.R));
            pragma Assert (Has_Entry (Idx, N, Held (New_F, K)));
         else
            pragma Assert (Holds (Old_F, Held (New_F, K))
                           and then not Drops_H (D, Held (New_F, K)));
            declare
               K2 : constant Held_Index := Witness (Old_F, Held (New_F, K));
            begin
               pragma Assert (Has_Entry (Old, N0, Held (Old_F, K2)));
               declare
                  I : constant Held_Index := Entry_Witness (Old, N0, Held (New_F, K));
               begin
                  pragma Assert (not Drops (D, Old (I)));
                  pragma Assert (Has_Entry (Idx, N, Old (I).H));
                  pragma Assert (Has_Entry (Idx, N, Held (New_F, K)));
               end;
            end;
         end if;
         pragma Loop_Invariant
           (for all K3 in 1 .. K => Has_Entry (Idx, N, Held (New_F, K3)));
      end loop;
   end Lemma_Covered_Kept;

   --  Fresh after a step that holds no new record other than R.
   procedure Lemma_Fresh_Kept
     (Old_F, New_F : Frontier.State; R : Header; Hz : Time64)
   with
     Ghost, Global => null,
     Pre  => Fresh (Old_F, Hz)
       and then not Expired (R, Hz)
       and then (for all K in 1 .. Count (New_F) =>
                   Held (New_F, K) = R or else Holds (Old_F, Held (New_F, K))),
     Post => Fresh (New_F, Hz);

   procedure Lemma_Fresh_Kept
     (Old_F, New_F : Frontier.State; R : Header; Hz : Time64) is
   begin
      for K in 1 .. Count (New_F) loop
         if Held (New_F, K) /= R then
            declare
               K2 : constant Held_Index := Witness (Old_F, Held (New_F, K));
            begin
               pragma Assert (not Expired (Held (Old_F, K2), Hz));
            end;
         end if;
         pragma Loop_Invariant
           (for all K3 in 1 .. K => not Expired (Held (New_F, K3), Hz));
      end loop;
   end Lemma_Fresh_Kept;

   --  Fresh after a step that holds no new record.
   procedure Lemma_Fresh_Sub (Old_F, New_F : Frontier.State; Hz : Time64) with
     Ghost, Global => null,
     Pre  => Fresh (Old_F, Hz)
       and then (for all K in 1 .. Count (New_F) => Holds (Old_F, Held (New_F, K))),
     Post => Fresh (New_F, Hz);

   procedure Lemma_Fresh_Sub (Old_F, New_F : Frontier.State; Hz : Time64) is
   begin
      for K in 1 .. Count (New_F) loop
         declare
            K2 : constant Held_Index := Witness (Old_F, Held (New_F, K));
         begin
            pragma Assert (not Expired (Held (Old_F, K2), Hz));
         end;
         pragma Loop_Invariant
           (for all K3 in 1 .. K => not Expired (Held (New_F, K3), Hz));
      end loop;
   end Lemma_Fresh_Sub;

   --  An append of one entry for R (or of no entry) keeps each entry and
   --  each fact about which records are indexed.
   procedure Lemma_Index_Grow
     (F   : Frontier.State; D : Drop_Rule;
      Old : Entry_Array; N0 : Held_Count;
      A   : Entry_Array; NA : Held_Count; B : Entry_Array; NB : Held_Count;
      R   : Header)
   with
     Ghost, Global => null,
     Pre  => Old'First = 1 and then N0 <= Old'Last
       and then A'First = 1 and then NA <= A'Last
       and then B'First = 1 and then NB <= B'Last
       and then NB = NA + 1
       and then B (NB).H = R
       and then Holds (F, R)
       and then Live (F, A, NA)
       and then (for all I in 1 .. N0 =>
                   (if not Drops (D, Old (I)) then Has_Entry (A, NA, Old (I).H)))
       and then (for all J in 1 .. NA => B (J) = A (J)),
     Post => Live (F, B, NB)
       and then (for all I in 1 .. N0 =>
                   (if not Drops (D, Old (I)) then Has_Entry (B, NB, Old (I).H)))
       and then Has_Entry (B, NB, R);

   procedure Lemma_Index_Grow
     (F   : Frontier.State; D : Drop_Rule;
      Old : Entry_Array; N0 : Held_Count;
      A   : Entry_Array; NA : Held_Count; B : Entry_Array; NB : Held_Count;
      R   : Header) is
   begin
      for I in 1 .. N0 loop
         if not Drops (D, Old (I)) then
            declare
               J : constant Held_Index := Entry_Witness (A, NA, Old (I).H);
            begin
               pragma Assert (B (J).H = Old (I).H);
            end;
         end if;
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              (if not Drops (D, Old (I2)) then Has_Entry (B, NB, Old (I2).H)));
      end loop;
      pragma Assert (for all J in 1 .. NA => Holds (F, A (J).H));
      pragma Assert (for all J in 1 .. NB => Holds (F, B (J).H));
   end Lemma_Index_Grow;

   ---------------------------------------------------------------------------
   --  The index has room: a pigeonhole argument.
   ---------------------------------------------------------------------------

   type Flag_Array is array (Positive range <>) of Boolean;

   --  The number of flags set in B (1 .. K).
   function Num (B : Flag_Array; K : Natural) return Natural is
     (if K = 0 then 0 else Num (B, K - 1) + (if B (K) then 1 else 0))
   with Ghost,
        Pre  => B'First = 1 and then K <= B'Last,
        Post => Num'Result <= K,
        Subprogram_Variant => (Decreases => K);

   --  If one clear flag is set, each count that includes it increases by
   --  one.
   procedure Lemma_Num_Set (B1, B2 : Flag_Array; P : Positive; K : Natural) with
     Ghost, Global => null,
     Pre  => B1'First = 1 and then B2'First = 1 and then B1'Last = B2'Last
             and then K <= B1'Last and then P <= B1'Last
             and then not B1 (P) and then B2 (P)
             and then (for all I in 1 .. B1'Last => (if I /= P then B2 (I) = B1 (I))),
     Post => Num (B2, K) = Num (B1, K) + (if P <= K then 1 else 0);

   procedure Lemma_Num_Set (B1, B2 : Flag_Array; P : Positive; K : Natural) is
   begin
      for I in 1 .. K loop
         pragma Loop_Invariant (Num (B2, I) = Num (B1, I) + (if P <= I then 1 else 0));
      end loop;
   end Lemma_Num_Set;

   --  Set flag P, which was clear: the count goes up by one.
   procedure Mark (B : in out Flag_Array; P : Positive; C : Natural) with
     Ghost, Global => null,
     Pre  => B'First = 1 and then B'Last = C and then P <= C and then not B (P),
     Post => B (P)
             and then (for all I in 1 .. C => (if I /= P then B (I) = B'Old (I)))
             and then Num (B, C) = Num (B'Old, C) + 1;

   procedure Mark (B : in out Flag_Array; P : Positive; C : Natural) is
      Prev : constant Flag_Array := B;
   begin
      B (P) := True;
      Lemma_Num_Set (Prev, B, P, C);
   end Mark;

   --  N distinct values in 1 .. C: N <= C.
   procedure Lemma_Pigeon (M : Index_Map; N : Held_Count; C : Held_Count) with
     Ghost, Global => null,
     Pre  => M'First = 1 and then N <= M'Last
             and then (for all J in 1 .. N => M (J) in 1 .. C)
             and then (for all J1 in 1 .. N =>
                         (for all J2 in 1 .. N => (if J1 /= J2 then M (J1) /= M (J2)))),
     Post => N <= C;

   procedure Lemma_Pigeon (M : Index_Map; N : Held_Count; C : Held_Count) is
   begin
      if C = 0 then
         if N > 0 then
            pragma Assert (M (1) in 1 .. C);
         end if;
         return;
      end if;
      declare
         Seen : Flag_Array (1 .. C) := [others => False];
      begin
         pragma Assert (Num (Seen, 0) = 0);
         for K in 1 .. C loop
            pragma Loop_Invariant (Num (Seen, K) = 0);
         end loop;
         for J in 1 .. N loop
            pragma Assert (for all J2 in 1 .. J - 1 => M (J2) /= M (J));
            pragma Assert (not Seen (M (J)));
            Mark (Seen, M (J), C);
            pragma Loop_Invariant (Num (Seen, C) = J);
            pragma Loop_Invariant
              (for all P in 1 .. C => Seen (P) = (for some J2 in 1 .. J => M (J2) = P));
         end loop;
      end;
   end Lemma_Pigeon;

   --  N distinct values in 1 .. C, none of them K0: N < C.
   procedure Lemma_Pigeon_Minus
     (M : Index_Map; N : Held_Count; C : Held_Count; K0 : Held_Index)
   with
     Ghost, Global => null,
     Pre  => M'First = 1 and then N <= M'Last and then K0 <= C
             and then (for all J in 1 .. N => M (J) in 1 .. C and then M (J) /= K0)
             and then (for all J1 in 1 .. N =>
                         (for all J2 in 1 .. N => (if J1 /= J2 then M (J1) /= M (J2)))),
     Post => N < C;

   procedure Lemma_Pigeon_Minus
     (M : Index_Map; N : Held_Count; C : Held_Count; K0 : Held_Index)
   is
      M2 : Index_Map (1 .. N) := [others => 0];
   begin
      for J in 1 .. N loop
         M2 (J) := (if M (J) > K0 then M (J) - 1 else M (J));
         pragma Loop_Invariant
           (for all J2 in 1 .. J => M2 (J2) = (if M (J2) > K0 then M (J2) - 1 else M (J2)));
      end loop;
      pragma Assert (for all J in 1 .. N => M2 (J) in 1 .. C - 1);
      Lemma_Pigeon (M2, N, C - 1);
   end Lemma_Pigeon_Minus;

   --  Let R be held, and let a sorted, live index not hold R. Then the
   --  index has fewer entries than there are held records.
   procedure Lemma_Index_Room
     (Idx : Entry_Array; N : Held_Count; F : Frontier.State; R : Header)
   with
     Ghost, Global => null,
     Pre  => Idx'First = 1 and then N <= Idx'Last
             and then Sorted (Idx, N)
             and then Live (F, Idx, N)
             and then Holds (F, R)
             and then (for all J in 1 .. N => Idx (J).H /= R),
     Post => N < Count (F);

   procedure Lemma_Index_Room
     (Idx : Entry_Array; N : Held_Count; F : Frontier.State; R : Header)
   is
      M  : Index_Map (1 .. N) := [others => 0];
      K0 : constant Held_Index := Witness (F, R);
   begin
      for J in 1 .. N loop
         M (J) := Witness (F, Idx (J).H);
         pragma Loop_Invariant
           (for all J2 in 1 .. J =>
              M (J2) in 1 .. Count (F) and then Held (F, M (J2)) = Idx (J2).H);
      end loop;
      for J1 in 1 .. N loop
         for J2 in 1 .. N loop
            if J1 /= J2 then
               Lemma_Sorted_Distinct (Idx, N, J1, J2);
            end if;
            pragma Loop_Invariant
              (for all J3 in 1 .. J2 => (if J1 /= J3 then M (J1) /= M (J3)));
         end loop;
         pragma Loop_Invariant
           (for all J4 in 1 .. J1 =>
              (for all J3 in 1 .. N => (if J4 /= J3 then M (J4) /= M (J3))));
      end loop;
      pragma Assert (for all J in 1 .. N => M (J) /= K0);
      Lemma_Pigeon_Minus (M, N, Count (F), K0);
   end Lemma_Index_Room;

   ---------------------------------------------------------------------------
   --  Nothing changes: the frontier through the Post of Frontier.Apply
   --  itself.
   ---------------------------------------------------------------------------

   --  Two frontiers with the same held records, position by position,
   --  keep the frontier parts of the invariant.
   procedure Lemma_Same_Held (S : Store; Old_F, New_F : Frontier.State) with
     Ghost, Global => null,
     Pre  => Valid (S, Old_F) and then Is_Frontier (New_F)
       and then New_F.Cap = Old_F.Cap and then New_F.Slice = Old_F.Slice
       and then Collection (New_F) = Collection (Old_F)
       and then Frontier.Founding (New_F) = Frontier.Founding (Old_F)
       and then Count (New_F) = Count (Old_F)
       and then (for all I in 1 .. Count (Old_F) => Held (New_F, I) = Held (Old_F, I)),
     Post => Valid (S, New_F);

   procedure Lemma_Same_Held (S : Store; Old_F, New_F : Frontier.State) is
   begin
      for J in 1 .. S.NI loop
         declare
            K : constant Held_Index := Witness (Old_F, S.Idx (J).H);
         begin
            pragma Assert (Held (New_F, K) = S.Idx (J).H);
         end;
         pragma Loop_Invariant (for all J2 in 1 .. J => Holds (New_F, S.Idx (J2).H));
      end loop;
      pragma Assert (Live (New_F, S.Idx, S.NI));
      pragma Assert
        (for all K in 1 .. Count (Old_F) => Has_Entry (S.Idx, S.NI, Held (Old_F, K)));
      for K in 1 .. Count (New_F) loop
         pragma Assert (Has_Entry (S.Idx, S.NI, Held (Old_F, K)));
         pragma Loop_Invariant
           (for all K2 in 1 .. K => Has_Entry (S.Idx, S.NI, Held (New_F, K2)));
      end loop;
      pragma Assert (Covered (New_F, S.Idx, S.NI));
      pragma Assert (for all K in 1 .. Count (Old_F) => not Expired (Held (Old_F, K), S.Hz));
      pragma Assert (Fresh (New_F, S.Hz));
   end Lemma_Same_Held;

   --  An unchanged frontier keeps the invariant. The tests execute it
   --  under -gnata, as all other lemmas (Kome.Frontier.Lemma_Unchanged has
   --  bounded quantifiers).
   procedure Lemma_Valid_Unchanged (S : Store; Old_F, New_F : Frontier.State) with
     Ghost, Global => null,
     Pre  => Valid (S, Old_F) and then Unchanged (Old_F, New_F) and then Is_Frontier (New_F),
     Post => Valid (S, New_F);

   procedure Lemma_Valid_Unchanged (S : Store; Old_F, New_F : Frontier.State) is
   begin
      Lemma_Unchanged (Old_F, New_F);
      Lemma_Same_Held (S, Old_F, New_F);
   end Lemma_Valid_Unchanged;

   ---------------------------------------------------------------------------
   --  Append an entry, and carry the log parts of the invariant along (in
   --  a context that knows nothing about the frontier).
   ---------------------------------------------------------------------------

   --  Frame is at Off as the payload of an APPLY: its length word and its
   --  bytes. Its Post defines it, so it is one atom on the log.
   function Stored_At (Log : Byte_Array; Off : Natural; Frame : Byte_Array) return Boolean
   with
     Ghost, Global => null,
     Pre  => Log'First = 0 and then Frame'Length in Frame_Size,
     Post => Stored_At'Result =
       (Off <= Log'Last and then Apply_Prefix + Frame'Length - 1 <= Log'Last - Off
        and then Len_Word (Log, Off) = Word (Frame'Length)
        and then (for all K in 0 .. Frame'Length - 1 =>
                    Log (Off + Apply_Prefix + K) = Frame (Frame'First + K)));

   function Stored_At (Log : Byte_Array; Off : Natural; Frame : Byte_Array) return Boolean is
     (Off <= Log'Last and then Apply_Prefix + Frame'Length - 1 <= Log'Last - Off
      and then Len_Word (Log, Off) = Word (Frame'Length)
      and then (for all K in 0 .. Frame'Length - 1 =>
                  Log (Off + Apply_Prefix + K) = Frame (Frame'First + K)));

   --  Each framed entry ends in the log. This is a fact about the state
   --  before an append; Put_Fresh needs it for the old end.
   procedure Lemma_Ends_Below
     (Log : Byte_Array; LL : Log_Size; Idx : Entry_Array; NI : Held_Count)
   with
     Ghost, Global => null,
     Pre  => Log'First = 0 and then LL <= Log'Last
       and then Idx'First = 1 and then NI <= Idx'Last
       and then Framed (Log, LL, Idx, NI),
     Post => (for all J in 1 .. NI => End_Of (Idx (J)) <= LL);

   procedure Lemma_Ends_Below
     (Log : Byte_Array; LL : Log_Size; Idx : Entry_Array; NI : Held_Count) is
   begin
      for J in 1 .. NI loop
         pragma Assert (Frame_OK (Log, LL, Idx (J)));
         pragma Loop_Invariant (for all J2 in 1 .. J => End_Of (Idx (J2)) <= LL);
      end loop;
   end Lemma_Ends_Below;

   procedure Log_Entry_Apply
     (Log  : in out Byte_Array; LL : in out Log_Size;
      Bnd  : in out Offset_Array; NB : in out Log_Size;
      Idx  : Entry_Array; NI : Held_Count;
      NSb  : NS_Id; Root : Pubkey; Slt : Salt; DCap : Data_Size; Slc : Slice_Count;
      Op   : Byte; Frame : Byte_Array)
   with
     Global => null,
     Pre  => Log'First = 0 and then LL <= Log'Last and then Log'Last <= Log_Max
       and then Bnd'First = 1 and then Bnd'Last >= Log'Last / Min_Entry and then NB <= Bnd'Last
       and then Idx'First = 1 and then NI <= Idx'Last
       and then (Op = Op_Apply or else Op = Op_Apply_Expired)
       and then Frame'Length in Frame_Size
       and then Apply_Prefix + Frame'Length <= Log'Last - LL
       and then Head_OK (Log, LL, NSb, Root, Slt, DCap, Slc)
       and then Framed (Log, LL, Idx, NI)
       and then Chain (Log, LL, Bnd, NB)
       and then At_Bounds (Idx, NI, Bnd, NB),
     Post => LL = LL'Old + Apply_Prefix + Frame'Length
       and then (for all P in 0 .. LL'Old - 1 => Log (P) = Log'Old (P))
       and then Log (LL'Old) = Op
       and then Len_Word (Log, LL'Old) = Word (Frame'Length)
       and then Kome.Keys.Word_Of (Log (LL'Old + 1), Log (LL'Old + 2),
                                   Log (LL'Old + 3), Log (LL'Old + 4)) = Word (Frame'Length)
       and then Log (LL'Old + Apply_Prefix) = Frame (Frame'First)
       and then (for all K in 0 .. Frame'Length - 1 =>
                   Log (LL'Old + Apply_Prefix + K) = Frame (Frame'First + K))
       and then Stored_At (Log, LL'Old, Frame)
       and then NB = NB'Old + 1
       and then NB <= Bnd'Last
       and then Bnd (NB) = LL'Old
       and then (for all K in 1 .. NB'Old => Bnd (K) = Bnd'Old (K))
       and then Head_OK (Log, LL, NSb, Root, Slt, DCap, Slc)
       and then Framed (Log, LL, Idx, NI)
       and then Chain (Log, LL, Bnd, NB)
       and then At_Bounds (Idx, NI, Bnd, NB);

   procedure Log_Entry_Apply
     (Log  : in out Byte_Array; LL : in out Log_Size;
      Bnd  : in out Offset_Array; NB : in out Log_Size;
      Idx  : Entry_Array; NI : Held_Count;
      NSb  : NS_Id; Root : Pubkey; Slt : Salt; DCap : Data_Size; Slc : Slice_Count;
      Op   : Byte; Frame : Byte_Array)
   is
      Old_Log : constant Byte_Array := Log with Ghost;
      Old_LL  : constant Log_Size := LL;
      Old_Bnd : constant Offset_Array := Bnd with Ghost;
      Old_NB  : constant Log_Size := NB with Ghost;
   begin
      Lemma_Framed_Sub (Log, LL, Idx, NI, Idx, NI);
      pragma Assert (for all J in 1 .. NI => End_Of (Idx (J)) <= Old_LL);
      Append_Apply (Log, LL, Bnd, NB, Op, Frame);
      Lemma_Framed_Grow (Old_Log, Old_LL, Log, LL, Idx, NI);
      Lemma_Bounds_Grow (Idx, NI, Old_Bnd, Old_NB, Bnd, NB);
      Lemma_Head_Grow (Old_Log, Old_LL, Log, LL, NSb, Root, Slt, DCap, Slc);
   end Log_Entry_Apply;

   procedure Log_Entry_Expire
     (Log  : in out Byte_Array; LL : in out Log_Size;
      Bnd  : in out Offset_Array; NB : in out Log_Size;
      Idx  : Entry_Array; NI : Held_Count;
      NSb  : NS_Id; Root : Pubkey; Slt : Salt; DCap : Data_Size; Slc : Slice_Count;
      Code : U48)
   with
     Global => null,
     Pre  => Log'First = 0 and then LL <= Log'Last and then Log'Last <= Log_Max
       and then Bnd'First = 1 and then Bnd'Last >= Log'Last / Min_Entry and then NB <= Bnd'Last
       and then Idx'First = 1 and then NI <= Idx'Last
       and then Expire_Len <= Log'Last - LL
       and then Head_OK (Log, LL, NSb, Root, Slt, DCap, Slc)
       and then Framed (Log, LL, Idx, NI)
       and then Chain (Log, LL, Bnd, NB)
       and then At_Bounds (Idx, NI, Bnd, NB),
     Post => LL = LL'Old + Expire_Len
       and then (for all P in 0 .. LL'Old - 1 => Log (P) = Log'Old (P))
       and then Log (LL'Old) = Op_Expire
       and then Kome.Records.U48_Of (Log (LL'Old + 1), Log (LL'Old + 2), Log (LL'Old + 3),
                                     Log (LL'Old + 4), Log (LL'Old + 5), Log (LL'Old + 6))
                = Code
       and then NB = NB'Old + 1
       and then NB <= Bnd'Last
       and then Bnd (NB) = LL'Old
       and then (for all K in 1 .. NB'Old => Bnd (K) = Bnd'Old (K))
       and then Head_OK (Log, LL, NSb, Root, Slt, DCap, Slc)
       and then Framed (Log, LL, Idx, NI)
       and then Chain (Log, LL, Bnd, NB)
       and then At_Bounds (Idx, NI, Bnd, NB);

   procedure Log_Entry_Expire
     (Log  : in out Byte_Array; LL : in out Log_Size;
      Bnd  : in out Offset_Array; NB : in out Log_Size;
      Idx  : Entry_Array; NI : Held_Count;
      NSb  : NS_Id; Root : Pubkey; Slt : Salt; DCap : Data_Size; Slc : Slice_Count;
      Code : U48)
   is
      Old_Log : constant Byte_Array := Log with Ghost;
      Old_LL  : constant Log_Size := LL with Ghost;
      Old_Bnd : constant Offset_Array := Bnd with Ghost;
      Old_NB  : constant Log_Size := NB with Ghost;
   begin
      Append_Expire (Log, LL, Bnd, NB, Code);
      Lemma_Framed_Grow (Old_Log, Old_LL, Log, LL, Idx, NI);
      Lemma_Bounds_Grow (Idx, NI, Old_Bnd, Old_NB, Bnd, NB);
      Lemma_Head_Grow (Old_Log, Old_LL, Log, LL, NSb, Root, Slt, DCap, Slc);
   end Log_Entry_Expire;

   --  A push of one entry whose APPLY is in place keeps the index
   --  framed.
   procedure Lemma_Framed_Push
     (Log : Byte_Array; LL : Log_Size; Old : Entry_Array; N0 : Held_Count;
      Idx : Entry_Array; N : Held_Count)
   with
     Ghost, Global => null,
     Pre  => Log'First = 0 and then LL <= Log'Last
       and then Old'First = 1 and then N0 <= Old'Last
       and then Idx'First = 1 and then N <= Idx'Last
       and then N = N0 + 1
       and then Framed (Log, LL, Old, N0)
       and then (for all J in 1 .. N0 => Idx (J) = Old (J))
       and then Idx (N).Off >= Header_Len
       and then Idx (N).Off <= LL
       and then LL - Idx (N).Off >= Apply_Prefix + Idx (N).Len
       and then Log (Idx (N).Off) = Op_Apply
       and then Len_Word (Log, Idx (N).Off) = Word (Idx (N).Len)
       and then Log (Idx (N).Off + Apply_Prefix) = Kome.Records.Tag_Of (Idx (N).H.K),
     Post => Framed (Log, LL, Idx, N);

   procedure Lemma_Framed_Push
     (Log : Byte_Array; LL : Log_Size; Old : Entry_Array; N0 : Held_Count;
      Idx : Entry_Array; N : Held_Count) is
   begin
      pragma Assert (Frame_OK (Log, LL, Idx (N)));
      pragma Assert (for all J in 1 .. N0 => Frame_OK (Log, LL, Old (J)));
      pragma Assert (for all J in 1 .. N => Frame_OK (Log, LL, Idx (J)));
   end Lemma_Framed_Push;

   --  The frame bytes of the entry at Off, read through Log_Byte.
   procedure Lemma_Log_Byte_Frame (S : Store; Off : Natural; Frame : Byte_Array) with
     Ghost, Global => null,
     Pre  => S.LL <= S.Log_Cap
       and then Frame'Length in Frame_Size
       and then Off <= S.LL and then Apply_Prefix + Frame'Length <= S.LL - Off
       and then (for all K in 0 .. Frame'Length - 1 =>
                   S.Log (Off + Apply_Prefix + K) = Frame (Frame'First + K)),
     Post => (for all K in 0 .. Frame'Length - 1 =>
                Log_Byte (S, Off + Apply_Prefix + K) = Frame (Frame'First + K));

   procedure Lemma_Log_Byte_Frame (S : Store; Off : Natural; Frame : Byte_Array) is
   begin
      pragma Assert (Log_Length (S) = S.LL);
      for K in 0 .. Frame'Length - 1 loop
         pragma Assert (Log_Byte (S, Off + Apply_Prefix + K) = S.Log (Off + Apply_Prefix + K));
         pragma Loop_Invariant
           (for all K2 in 0 .. K =>
              Log_Byte (S, Off + Apply_Prefix + K2) = Frame (Frame'First + K2));
      end loop;
   end Lemma_Log_Byte_Frame;

   --  Frame_Stored, read in the log array.
   procedure Lemma_Frame_Stored_Log (S : Store; Off : Natural; Frame : Byte_Array) with
     Ghost, Global => null,
     Pre  => S.LL <= S.Log_Cap
       and then Frame'Length in Frame_Size
       and then Frame_Stored (S, Off, Frame),
     Post => Off + Apply_Prefix + Frame'Length <= S.LL
       and then Len_Word (S.Log, Off) = Word (Frame'Length)
       and then (for all K in 0 .. Frame'Length - 1 =>
                   S.Log (Off + Apply_Prefix + K) = Frame (Frame'First + K));

   procedure Lemma_Frame_Stored_Log (S : Store; Off : Natural; Frame : Byte_Array) is
   begin
      pragma Assert (Log_Length (S) = S.LL);
      pragma Assert (Len_At (S, Off) = Word (Frame'Length));
      pragma Assert
        (for all K in 0 .. Frame'Length - 1 =>
           Log_Byte (S, Off + Apply_Prefix + K) = Frame (Frame'First + K));
      for K in 0 .. Frame'Length - 1 loop
         pragma Assert (Log_Byte (S, Off + Apply_Prefix + K) = Frame (Frame'First + K));
         pragma Loop_Invariant
           (for all K2 in 0 .. K => S.Log (Off + Apply_Prefix + K2) = Frame (Frame'First + K2));
      end loop;
   end Lemma_Frame_Stored_Log;

   --  Frame_Stored, from Stored_At on the log array.
   procedure Lemma_Stored_From (S : Store; Off : Natural; Frame : Byte_Array)
   with
     Ghost, Global => null,
     Pre  => S.LL <= S.Log_Cap
       and then Frame'Length in Frame_Size
       and then Off <= S.LL and then Apply_Prefix + Frame'Length <= S.LL - Off
       and then Stored_At (S.Log, Off, Frame),
     Post => Frame_Stored (S, Off, Frame);

   procedure Lemma_Stored_From (S : Store; Off : Natural; Frame : Byte_Array) is
   begin
      pragma Assert (Log_Length (S) = S.LL);
      pragma Assert (Len_Word (S.Log, Off) = Word (Frame'Length));
      pragma Assert (Len_At (S, Off) = Word (Frame'Length));
      pragma Assert
        (for all K in 0 .. Frame'Length - 1 =>
           S.Log (Off + Apply_Prefix + K) = Frame (Frame'First + K));
      Lemma_Log_Byte_Frame (S, Off, Frame);
   end Lemma_Stored_From;

   ---------------------------------------------------------------------------
   --  The two paths of Put_Frame that commit a change.
   ---------------------------------------------------------------------------

   --  Step 6: Frontier.Apply held R. Drop the entries that R dominated,
   --  append APPLY and index R.
   procedure Put_Fresh
     (S     : in out Store;
      F     : in out Frontier.State;
      Frame : Byte_Array;
      H     : Header)
   with
     Global => null,
     Pre  => Valid (S, F)
       and then Canonical (H)
       and then H.NS = S.NS
       and then Frame'Length in Frame_Size
       and then Frame (Frame'First) = Kome.Records.Tag_Of (H.K)
       and then S.Log_Cap - S.LL >= Apply_Prefix + Frame'Length
       and then not Expired (H, S.Hz)
       and then Admitted (F, H)
       and then not Holds (F, H)
       and then not Dom (F, H)
       and then not Data_Full (F, H)
       and then not Auth_Rule (F, H)
       and then not Gen_Full (S, H),
     Post => Valid (S, F)
       and then S.NS = S.NS'Old and then S.Fnd = S.Fnd'Old
       and then S.Root = S.Root'Old and then S.Slt = S.Slt'Old
       and then S.Cid = S.Cid'Old
       and then S.DCap = S.DCap'Old and then S.Slc = S.Slc'Old
       and then S.Hz = S.Hz'Old
       and then S.AG = (if Is_Auth (H) then S.AG'Old + 1 else S.AG'Old)
       and then S.EM = S.EM'Old
       and then Holds (F, H)
       and then Applied (F'Old, F, H)
       and then Log_Extends (S'Old, S)
       and then Appended (S'Old, S, Frame, H, S.LL'Old)
       and then Indexed (S, H);

   procedure Put_Fresh
     (S     : in out Store;
      F     : in out Frontier.State;
      Frame : Byte_Array;
      H     : Header)
   is
      Saved   : constant Store := S with Ghost;
      Old_F   : constant Frontier.State := F with Ghost;
      Old_Idx : constant Entry_Array := S.Idx with Ghost;
      Old_NI  : constant Held_Count := S.NI with Ghost;
      Old_LL  : constant Log_Size := S.LL;
      Len     : constant Frame_Size := Frame'Length;
      D       : constant Drop_Rule := (By_Dom => True, R => H, Hz => No_Horizon);
      St      : Status;
   begin
      Apply (F, H, St);
      pragma Assert (St = OK);
      pragma Assert (Applied (Old_F, F, H));

      --  AUDIT.md H11: one more authorization record applied.
      if Is_Auth (H) then
         S.AG := S.AG + 1;
      end if;

      --  dom (x, F): drop the entries that H dominates.
      Filter (S.Idx, S.NI, D);
      pragma Assert (for all J in 1 .. S.NI => not Dominates (H, S.Idx (J).H));
      Lemma_Live_Kept (Old_F, F, D, Old_Idx, Old_NI, S.Idx, S.NI);
      Lemma_Not_Indexed (Old_F, Old_Idx, Old_NI, S.Idx, S.NI, H);
      Lemma_Framed_Sub (S.Log, S.LL, Old_Idx, Old_NI, S.Idx, S.NI);
      Lemma_Bounds_Sub (S.Idx, S.NI, Old_Idx, Old_NI, S.Bnd, S.NB);
      pragma Assert
        (for all I in 1 .. Old_NI =>
           (if not Drops (D, Old_Idx (I)) then Has_Entry (S.Idx, S.NI, Old_Idx (I).H)));

      --  The index has room: the kept entries are distinct held records
      --  other than H, so there are fewer than Count (F) <= S.Cap of them.
      Lemma_Index_Room (S.Idx, S.NI, F, H);
      Lemma_Frontier_Shape (F);
      pragma Assert (S.NI < S.Cap);

      declare
         Kept_Idx : constant Entry_Array := S.Idx with Ghost;
         Kept_NI  : constant Held_Count := S.NI with Ghost;
      begin
         pragma Assert (Sorted (S.Idx, S.NI));
         pragma Assert (for all J in 1 .. S.NI => S.Idx (J).H /= H);
         Lemma_Ends_Below (S.Log, S.LL, S.Idx, S.NI);
         Log_Entry_Apply (S.Log, S.LL, S.Bnd, S.NB, S.Idx, S.NI,
                          S.NSb, S.Root, S.Slt, S.DCap, S.Slc, Op_Apply, Frame);
         pragma Assert (Stored_At (S.Log, Old_LL, Frame));
         S.NI := S.NI + 1;
         S.Idx (S.NI) := (H => H, Off => Old_LL, Len => Len);
         pragma Assert (for all J in 1 .. Kept_NI => S.Idx (J) = Kept_Idx (J));
         Lemma_Framed_Push (S.Log, S.LL, Kept_Idx, Kept_NI, S.Idx, S.NI);
         Lemma_Sorted_Push (Kept_Idx, Kept_NI, S.Idx, S.NI);
         Lemma_Bounds_Push (Kept_Idx, Kept_NI, S.Idx, S.NI, S.Bnd, S.NB);
         Lemma_Index_Grow (F, D, Old_Idx, Old_NI, Kept_Idx, Kept_NI, S.Idx, S.NI, H);
      end;

      Lemma_Apply_Kept (Old_F, F, H);
      Lemma_Covered_Kept (Old_F, F, D, Old_Idx, Old_NI, S.Idx, S.NI);
      Lemma_Fresh_Kept (Old_F, F, H, S.Hz);
      pragma Assert (Valid (S, F));

      --  The contract, over the saved store.
      pragma Assert (for all J in 0 .. Old_LL - 1 => S.Log (J) = Saved.Log (J));
      pragma Assert (Log_Extends (Saved, S));
      pragma Assert (S.LL = Old_LL + Apply_Prefix + Len);
      Lemma_Stored_From (S, Old_LL, Frame);
      pragma Assert (Appended (Saved, S, Frame, H, Old_LL));
      pragma Assert (Has_Entry (S.Idx, S.NI, H));
   end Put_Fresh;

   --  Step 4: an expired DEL that drops a record. Do
   --  Frontier.Apply_Expired, drop the entries that the DEL dominated, and
   --  append APPLY_EXPIRED (not indexed).
   procedure Do_Apply_Expired
     (S     : in out Store;
      F     : in out Frontier.State;
      Frame : Byte_Array;
      H     : Header)
   with
     Global => null,
     Pre  => Valid (S, F)
       and then H.K = K_Del
       and then Canonical (H)
       and then H.NS = S.NS
       and then Admitted (F, H)
       and then not Dom (F, H)
       and then not Holds (F, H)
       and then Frame'Length in Frame_Size
       and then S.Log_Cap - S.LL >= Apply_Prefix + Frame'Length,
     Post => Valid (S, F)
       and then S.NS = S.NS'Old and then S.Fnd = S.Fnd'Old
       and then S.Root = S.Root'Old and then S.Slt = S.Slt'Old
       and then S.Cid = S.Cid'Old
       and then S.DCap = S.DCap'Old and then S.Slc = S.Slc'Old
       and then S.Hz = S.Hz'Old
       and then S.AG = S.AG'Old
       and then S.EM = U48'Max (S.EM'Old, H.V.T)
       and then Expired_Applied (F'Old, F, H)
       and then Log_Extends (S'Old, S)
       and then Appended_Expired (S'Old, S, Frame, S.LL'Old);

   procedure Do_Apply_Expired
     (S     : in out Store;
      F     : in out Frontier.State;
      Frame : Byte_Array;
      H     : Header)
   is
      Saved   : constant Store := S with Ghost;
      Old_F   : constant Frontier.State := F with Ghost;
      Old_Idx : constant Entry_Array := S.Idx with Ghost;
      Old_NI  : constant Held_Count := S.NI with Ghost;
      Old_LL  : constant Log_Size := S.LL;
      D       : constant Drop_Rule := (By_Dom => True, R => H, Hz => No_Horizon);
      St      : Status;
   begin
      Apply_Expired (F, H, St);
      pragma Assert (St = OK);
      pragma Assert (Expired_Applied (Old_F, F, H));

      --  AUDIT.md H28: the mark rises to the t of the applied DEL.
      S.EM := U48'Max (S.EM, H.V.T);

      Filter (S.Idx, S.NI, D);
      Lemma_Live_Kept (Old_F, F, D, Old_Idx, Old_NI, S.Idx, S.NI);
      Lemma_Framed_Sub (S.Log, S.LL, Old_Idx, Old_NI, S.Idx, S.NI);
      Lemma_Bounds_Sub (S.Idx, S.NI, Old_Idx, Old_NI, S.Bnd, S.NB);
      pragma Assert
        (for all I in 1 .. Old_NI =>
           (if not Drops (D, Old_Idx (I)) then Has_Entry (S.Idx, S.NI, Old_Idx (I).H)));
      pragma Assert
        (for all K in 1 .. Count (F) =>
           Holds (Old_F, Held (F, K)) and then not Drops_H (D, Held (F, K)));
      Lemma_Covered_Kept (Old_F, F, D, Old_Idx, Old_NI, S.Idx, S.NI);
      Lemma_Fresh_Sub (Old_F, F, S.Hz);
      Lemma_Ends_Below (S.Log, S.LL, S.Idx, S.NI);

      Log_Entry_Apply (S.Log, S.LL, S.Bnd, S.NB, S.Idx, S.NI,
                       S.NSb, S.Root, S.Slt, S.DCap, S.Slc, Op_Apply_Expired, Frame);
      pragma Assert (S.LL = Old_LL + Apply_Prefix + Frame'Length);
      Lemma_Stored_From (S, Old_LL, Frame);
      pragma Assert (Frame_Stored (S, Old_LL, Frame));
      pragma Assert (Valid (S, F));

      pragma Assert (for all J in 0 .. Old_LL - 1 => S.Log (J) = Saved.Log (J));
      pragma Assert (Log_Extends (Saved, S));
      pragma Assert (Appended_Expired (Saved, S, Frame, Old_LL));
   end Do_Apply_Expired;


   ---------------------------------------------------------------------------
   --  Expiry.
   ---------------------------------------------------------------------------

   --  The Post of Frontier.Expire, read in the flat view.
   procedure Lemma_Expire_Flat (Old_F, New_F : Frontier.State; Hz : Time64) with
     Ghost, Global => null,
     Pre  => Is_Frontier (Old_F) and then Is_Frontier (New_F)
       and then Slots_Used (New_F) = Slots_Used (Old_F)
       and then (for all K in Slot_Index =>
                   Slot_Count (New_F, K) = Slot_Count (Old_F, K)
                   and then Off (New_F, K) = Off (Old_F, K))
       and then (for all K in 1 .. Slots_Used (New_F) =>
                   Slot_Key (New_F, K) = Slot_Key (Old_F, K)
                   and then (for all J in 1 .. Slot_Count (New_F, K) =>
                               Auth_Held (New_F, K, J) = Auth_Held (Old_F, K, J)))
       and then (for all I in 1 .. Data_Count (New_F) =>
                   Holds (Old_F, Data_Held (New_F, I))
                   and then not Expired (Data_Held (New_F, I), Hz))
       and then (for all I in 1 .. Data_Count (Old_F) =>
                   Expired (Data_Held (Old_F, I), Hz)
                   or else Holds (New_F, Data_Held (Old_F, I))),
     Post => (for all I in 1 .. Count (New_F) =>
                Holds (Old_F, Held (New_F, I)) and then not Expired (Held (New_F, I), Hz))
       and then (for all I in 1 .. Count (Old_F) =>
                   Holds (New_F, Held (Old_F, I)) or else Expired (Held (Old_F, I), Hz));

   procedure Lemma_Expire_Flat (Old_F, New_F : Frontier.State; Hz : Time64) is
   begin
      for I in 1 .. Count (New_F) loop
         Lemma_Held_Cases (New_F, I);
         if I <= Data_Count (New_F) then
            pragma Assert (Held (New_F, I) = Data_Held (New_F, I));
         else
            declare
               K : constant Slot_Index := Slot_At (New_F, I);
               J : constant Held_Index := I - Data_Count (New_F) - Off (New_F, K);
            begin
               pragma Assert (Held (New_F, I) = Auth_Held (New_F, K, J));
               pragma Assert (Auth_Held (New_F, K, J) = Auth_Held (Old_F, K, J));
               Lemma_Held_Auth (Old_F, K, J);
               Lemma_Frontier_Auth (Old_F, K, J);
               pragma Assert
                 (Held (Old_F, Data_Count (Old_F) + Off (Old_F, K) + J) = Held (New_F, I));
               pragma Assert (Holds (Old_F, Held (New_F, I)));
               pragma Assert (not Expired (Held (New_F, I), Hz));
            end;
         end if;
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              Holds (Old_F, Held (New_F, I2)) and then not Expired (Held (New_F, I2), Hz));
      end loop;
      for I in 1 .. Count (Old_F) loop
         Lemma_Held_Cases (Old_F, I);
         if I <= Data_Count (Old_F) then
            pragma Assert (Held (Old_F, I) = Data_Held (Old_F, I));
         else
            declare
               K : constant Slot_Index := Slot_At (Old_F, I);
               J : constant Held_Index := I - Data_Count (Old_F) - Off (Old_F, K);
            begin
               pragma Assert (Held (Old_F, I) = Auth_Held (Old_F, K, J));
               Lemma_Held_Auth (New_F, K, J);
               pragma Assert
                 (Held (New_F, Data_Count (New_F) + Off (New_F, K) + J) = Held (Old_F, I));
               pragma Assert (Holds (New_F, Held (Old_F, I)));
            end;
         end if;
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              Holds (New_F, Held (Old_F, I2)) or else Expired (Held (Old_F, I2), Hz));
      end loop;
   end Lemma_Expire_Flat;

   --  A frontier with no record expired at Hz is its own expiry at a
   --  horizon Hn <= Hz.
   procedure Lemma_Out_Refl (F : Frontier.State; Hz, Hn : Time64) with
     Ghost, Global => null,
     Pre  => Fresh (F, Hz) and then Hn <= Hz,
     Post => Expired_Out (F, F, Hn) and then Fresh (F, Hn);

   procedure Lemma_Out_Refl (F : Frontier.State; Hz, Hn : Time64) is
   begin
      Lemma_Extends_Refl (Regs (F));
      for I in 1 .. Count (F) loop
         pragma Assert (not Expired (Held (F, I), Hz));
         pragma Assert (Holds (F, Held (F, I)));
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              Holds (F, Held (F, I2)) and then not Expired (Held (F, I2), Hn));
      end loop;
      pragma Assert (Fresh (F, Hn));
   end Lemma_Out_Refl;

   --  The log of S is the log of Old_S with EXPIRE (Code) appended. This
   --  is a bridge lemma: it reads the facts in the Post of
   --  Log_Entry_Expire through the store's accessors, in a small context.
   procedure Lemma_Expire_Appended (Old_S, S : Store; Code : U48) with
     Ghost, Global => null,
     Pre  => Old_S.LL <= Old_S.Log_Cap and then S.LL <= S.Log_Cap
       and then Old_S.NB <= Old_S.Log_Cap and then S.NB <= S.Log_Cap
       and then Old_S.NB <= Old_S.Bnd_Cap and then S.NB <= S.Bnd_Cap
       and then Old_S.LL <= S.Log_Cap and then Old_S.NB <= S.Log_Cap
       and then S.LL = Old_S.LL + Expire_Len
       and then (for all P in 0 .. Old_S.LL - 1 => S.Log (P) = Old_S.Log (P))
       and then S.Log (Old_S.LL) = Op_Expire
       and then Kome.Records.U48_Of (S.Log (Old_S.LL + 1), S.Log (Old_S.LL + 2),
                                     S.Log (Old_S.LL + 3), S.Log (Old_S.LL + 4),
                                     S.Log (Old_S.LL + 5), S.Log (Old_S.LL + 6))
                = Code
       and then S.NB = Old_S.NB + 1
       and then S.Bnd (S.NB) = Old_S.LL
       and then (for all K in 1 .. Old_S.NB => S.Bnd (K) = Old_S.Bnd (K)),
     Post => Log_Extends (Old_S, S)
       and then Grew_By (Old_S, S, Old_S.LL, Expire_Len)
       and then Op_At (S, Old_S.LL) = Op_Expire
       and then Code_At (S, Old_S.LL + 1) = Code;

   procedure Lemma_Expire_Appended (Old_S, S : Store; Code : U48) is
   begin
      pragma Assert (Log_Length (S) = S.LL and then Log_Length (Old_S) = Old_S.LL);
      pragma Assert (Log_Entries (S) = S.NB and then Log_Entries (Old_S) = Old_S.NB);
      pragma Assert
        (for all J in 0 .. Log_Length (Old_S) - 1 => Log_Byte (S, J) = Log_Byte (Old_S, J));
      pragma Assert
        (for all K in 1 .. Log_Entries (Old_S) => Entry_Start (S, K) = Entry_Start (Old_S, K));
      pragma Assert (Log_Extends (Old_S, S));
      pragma Assert (Grew_By (Old_S, S, Old_S.LL, Expire_Len));
      pragma Assert (Op_At (S, Old_S.LL) = Op_Expire);
      pragma Assert (Code_At (S, Old_S.LL + 1) = Code);
   end Lemma_Expire_Appended;

   --  Perform EXPIRE at the horizon Hn, logged with the code Code (Expire
   --  logs Horizon_Code (Hn); replay logs the code it read, and applies
   --  the clamped horizon, AUDIT.md H24):
   --    1. If Hn is above the horizon, do Frontier.Expire and drop the
   --       expired entries. If that removed a record, raise the mark to
   --       Hn (AUDIT.md H28).
   --    2. Append EXPIRE (Code).
   --    3. Set the horizon.
   procedure Do_Expire
     (S : in out Store; F : in out Frontier.State; Hn : Horizon_Value; Code : U48)
   with
     Global => null,
     Pre  => Valid (S, F) and then S.Log_Cap - S.LL >= Expire_Len,
     Post => Valid (S, F)
       and then S.NS = S.NS'Old and then S.Fnd = S.Fnd'Old
       and then S.Root = S.Root'Old and then S.Slt = S.Slt'Old
       and then S.Cid = S.Cid'Old
       and then S.DCap = S.DCap'Old and then S.Slc = S.Slc'Old
       and then S.Hz = Hn
       and then S.AG = S.AG'Old
       and then S.EM = (if Hn > S.Hz'Old then U48'Max (S.EM'Old, U48 (Hn)) else S.EM'Old)
       and then Expired_Out (F'Old, F, Hn)
       and then Log_Extends (S'Old, S)
       and then Grew_By (S'Old, S, S.LL'Old, Expire_Len)
       and then Op_At (S, S.LL'Old) = Op_Expire
       and then Code_At (S, S.LL'Old + 1) = Code;

   procedure Do_Expire
     (S : in out Store; F : in out Frontier.State; Hn : Horizon_Value; Code : U48)
   is
      Saved  : constant Store := S with Ghost;
      Old_F  : constant Frontier.State := F with Ghost;
      No_H   : Header;
   begin
      if Hn > S.Hz then
         --  AUDIT.md H28: the mark follows every raise of the horizon.
         S.EM := U48'Max (S.EM, U48 (Hn));
         pragma Assert (Valid (S, F));
         Frontier.Expire (F, Hn);
         Lemma_Expire_Flat (Old_F, F, Hn);
         pragma Assert (Expired_Out (Old_F, F, Hn));
         declare
            Old_Idx : constant Entry_Array := S.Idx with Ghost;
            Old_NI  : constant Held_Count := S.NI with Ghost;
            D       : constant Drop_Rule := (By_Dom => False, R => No_H, Hz => Hn);
         begin
            Filter (S.Idx, S.NI, D);
            Lemma_Live_Kept (Old_F, F, D, Old_Idx, Old_NI, S.Idx, S.NI);
            Lemma_Framed_Sub (S.Log, S.LL, Old_Idx, Old_NI, S.Idx, S.NI);
            Lemma_Bounds_Sub (S.Idx, S.NI, Old_Idx, Old_NI, S.Bnd, S.NB);
            pragma Assert
              (for all I in 1 .. Old_NI =>
                 (if not Drops (D, Old_Idx (I)) then Has_Entry (S.Idx, S.NI, Old_Idx (I).H)));
            Lemma_Covered_Kept (Old_F, F, D, Old_Idx, Old_NI, S.Idx, S.NI);
         end;
         pragma Assert (Fresh (F, Hn));
      else
         Lemma_Out_Refl (F, S.Hz, Hn);
      end if;

      pragma Assert (Live (F, S.Idx, S.NI) and then Covered (F, S.Idx, S.NI));
      pragma Assert (Sorted (S.Idx, S.NI));
      pragma Assert (Is_Frontier (F) and then F.Slice = S.Slc);
      Log_Entry_Expire (S.Log, S.LL, S.Bnd, S.NB, S.Idx, S.NI,
                        S.NSb, S.Root, S.Slt, S.DCap, S.Slc, Code);
      S.Hz := Hn;
      pragma Assert (Valid (S, F));
      Lemma_Expire_Appended (Saved, S, Code);
   end Do_Expire;

   ---------------------------------------------------------------------------
   --  Store creation.
   ---------------------------------------------------------------------------

   --  Byte J of the HEADER.
   function Header_Byte
     (Root : Pubkey; Slt : Salt; NSb : NS_Id; DCap : Data_Size; Slc : Slice_Count;
      J    : Natural) return Byte
   is
     (if J = 0 then Op_Header
      elsif J < HO_Version then Magic (J - HO_Magic)
      elsif J = HO_Version then Log_Version
      elsif J < HO_Root then NSb (J - HO_NS)
      elsif J < HO_Salt then Root (J - HO_Root)
      elsif J < HO_Cap then Slt (J - HO_Salt)
      elsif J < HO_Slice then Kome.Keys.Byte_Of_Word (Word (DCap), J - HO_Cap)
      else Kome.Records.Byte_Of_U16 (Slc, J - HO_Slice))
   with Pre => J < Header_Len;

   --  A store that holds only the HEADER of (Root, Slt) with the
   --  capacities DCap and Slc.
   procedure Init (S : out Store; Root : Pubkey; Slt : Salt; DCap : Data_Size; Slc : Slice_Count)
   with
     Global => null,
     Pre  => S.Log_Cap >= Header_Len and then S.Bnd_Cap >= Bnd_Cap_For (S.Log_Cap),
     Post => S.NS = Kome.Keys.To_Id128 (Kome.Records.Collection_Id (Root, Slt))
       and then S.NS = Kome.Keys.To_Id128 (S.NSb)
       and then S.NSb = Kome.Records.Collection_Id (S.Root, S.Slt)
       and then S.Cid = Kome.Records.Cid_Of (S.Root, S.Slt)
       and then S.Cid = Kome.Records.Cid_Of (Root, Slt)
       and then S.Fnd = Kome.Keys.To_Key256 (Root)
       and then S.Fnd = Kome.Keys.To_Key256 (S.Root)
       and then S.Root = Root and then S.Slt = Slt
       and then S.DCap = DCap and then S.Slc = Slc
       and then S.Hz = No_Horizon
       and then S.AG = 0 and then S.EM = 0
       and then S.NI = 0
       and then S.LL = Header_Len
       and then S.NB = 1
       and then Head_OK (S.Log, S.LL, S.NSb, S.Root, S.Slt, DCap, Slc)
       and then Chain (S.Log, S.LL, S.Bnd, S.NB)
       and then (for all J in 0 .. Header_Len - 1 =>
                   S.Log (J) = Header_Byte (Root, Slt, Kome.Records.Collection_Id (Root, Slt),
                                            DCap, Slc, J));

   procedure Init (S : out Store; Root : Pubkey; Slt : Salt; DCap : Data_Size; Slc : Slice_Count)
   is
      NSb : constant NS_Id := Kome.Records.Collection_Id (Root, Slt);
      Hdr : constant Byte_Array (0 .. Header_Len - 1) :=
        [for J in 0 .. Header_Len - 1 => Header_Byte (Root, Slt, NSb, DCap, Slc, J)];
   begin
      --  Component by component: an aggregate for the whole store would
      --  be built in a temporary and copied (AUDIT.md G15).
      S.NS   := Kome.Keys.To_Id128 (NSb);
      S.NSb  := NSb;
      S.Fnd  := Kome.Keys.To_Key256 (Root);
      S.Root := Root;
      S.Slt  := Slt;
      S.Cid  := Kome.Records.Cid_Of (Root, Slt);   --  once, at open (A26)
      S.DCap := DCap;
      S.Slc  := Slc;
      S.Hz   := No_Horizon;
      S.AG   := 0;
      S.EM   := 0;
      S.NI   := 0;
      S.Idx  := [others => (H => <>, Off => 0, Len => 1)];
      S.LL   := Header_Len;
      S.Log  := [others => 0];
      S.NB   := 1;
      S.Bnd  := [others => 0];
      S.Log (0 .. Header_Len - 1) := Hdr;
      Kome.Keys.Lemma_Word_Round_Trip (Word (DCap));
      Kome.Records.Lemma_U16_Round_Trip (Slc);
      pragma Assert (for all J in 0 .. Header_Len - 1 => S.Log (J) = Hdr (J));
      pragma Assert (S.Log (HO_Cap) = Kome.Keys.Byte_Of_Word (Word (DCap), 0));
      pragma Assert (S.Log (HO_Cap + 1) = Kome.Keys.Byte_Of_Word (Word (DCap), 1));
      pragma Assert (S.Log (HO_Cap + 2) = Kome.Keys.Byte_Of_Word (Word (DCap), 2));
      pragma Assert (S.Log (HO_Cap + 3) = Kome.Keys.Byte_Of_Word (Word (DCap), 3));
      pragma Assert (S.Log (HO_Slice) = Kome.Records.Byte_Of_U16 (Slc, 0));
      pragma Assert (S.Log (HO_Slice + 1) = Kome.Records.Byte_Of_U16 (Slc, 1));
      --  Head_OK, one conjunct at a time (prover time).
      pragma Assert (S.Log (0) = Op_Header);
      pragma Assert (for all J in 0 .. Magic_Len - 1 => S.Log (HO_Magic + J) = Magic (J));
      pragma Assert (S.Log (HO_Version) = Log_Version);
      pragma Assert (for all J in 0 .. NS_Len - 1 => S.Log (HO_NS + J) = S.NSb (J));
      pragma Assert (for all J in 0 .. Pubkey_Len - 1 => S.Log (HO_Root + J) = S.Root (J));
      pragma Assert (for all J in 0 .. Salt_Len - 1 => S.Log (HO_Salt + J) = S.Slt (J));
      pragma Assert
        (Kome.Keys.Word_Of (S.Log (HO_Cap), S.Log (HO_Cap + 1),
                            S.Log (HO_Cap + 2), S.Log (HO_Cap + 3)) = Word (DCap));
      pragma Assert (Kome.Records.U16_Of (S.Log (HO_Slice), S.Log (HO_Slice + 1)) = Slc);
      pragma Assert (Head_OK (S.Log, S.LL, S.NSb, S.Root, S.Slt, DCap, Slc));
      pragma Assert (Entry_OK (S.Log, S.LL, 0));
      pragma Assert (Size_At (S.Log, 0) = Header_Len);
      pragma Assert (Chain (S.Log, S.LL, S.Bnd, S.NB));
   end Init;

   --  A store that holds only its HEADER beside an empty frontier of its
   --  collection and founding key is valid.
   procedure Lemma_Valid_Start (S : Store; F : Frontier.State) with
     Ghost, Global => null,
     Pre  => Is_Frontier (F) and then Count (F) = 0
       and then S.NI = 0 and then S.Log_Cap >= Header_Len
       and then S.Bnd_Cap >= Bnd_Cap_For (S.Log_Cap)
       and then S.LL = Header_Len and then S.NB = 1
       and then Collection (F) = S.NS
       and then Frontier.Founding (F) = S.Fnd
       and then S.Fnd = Kome.Keys.To_Key256 (S.Root)
       and then S.NS = Kome.Keys.To_Id128 (S.NSb)
       and then S.NSb = Kome.Records.Collection_Id (S.Root, S.Slt)
       and then S.Cid = Kome.Records.Cid_Of (S.Root, S.Slt)
       and then S.Slc = F.Slice
       and then S.Cap >= F.Cap + Signers_Max * F.Slice
       and then Head_OK (S.Log, S.LL, S.NSb, S.Root, S.Slt, S.DCap, S.Slc)
       and then Chain (S.Log, S.LL, S.Bnd, S.NB),
     Post => Valid (S, F);

   procedure Lemma_Valid_Start (S : Store; F : Frontier.State) is
   begin
      pragma Assert (Live (F, S.Idx, S.NI));
      pragma Assert (Covered (F, S.Idx, S.NI));
      pragma Assert (Fresh (F, S.Hz));
      pragma Assert (Framed (S.Log, S.LL, S.Idx, S.NI));
      pragma Assert (Sorted (S.Idx, S.NI));
      pragma Assert (At_Bounds (S.Idx, S.NI, S.Bnd, S.NB));
   end Lemma_Valid_Start;

   procedure Open (Root_PK : Pubkey; Salt : Kome.Salt; F : Frontier.State; S : out Store) is
   begin
      Init (S, Root_PK, Salt, F.Cap, F.Slice);
      Lemma_Valid_Start (S, F);
   end Open;

   ---------------------------------------------------------------------------
   --  Read the log.
   ---------------------------------------------------------------------------

   function Read_Frame (S : Store; Off : Natural) return Byte_Array is
      L : constant Natural := Natural (Len_At (S, Off));
      R : Byte_Array (0 .. L - 1) := [others => 0];
   begin
      for K in 0 .. L - 1 loop
         R (K) := Log_Byte (S, Off + Apply_Prefix + K);
         pragma Loop_Invariant
           (for all K2 in 0 .. K => R (K2) = Log_Byte (S, Off + Apply_Prefix + K2));
      end loop;
      return R;
   end Read_Frame;

   function Log_Bytes (S : Store) return Byte_Array is
      L : constant Log_Size := Log_Length (S);
      R : Byte_Array (0 .. L - 1) := [others => 0];
   begin
      for J in 0 .. L - 1 loop
         R (J) := Log_Byte (S, J);
         pragma Loop_Invariant (for all J2 in 0 .. J => R (J2) = Log_Byte (S, J2));
      end loop;
      return R;
   end Log_Bytes;

   ---------------------------------------------------------------------------
   --  Put_Frame and Expire.
   ---------------------------------------------------------------------------

   --  An expired DEL is never held (Fresh).
   procedure Lemma_Expired_Not_Held (S : Store; F : Frontier.State; H : Header) with
     Ghost, Global => null,
     Pre  => Valid (S, F) and then Expired (H, S.Hz),
     Post => not Holds (F, H);

   procedure Lemma_Expired_Not_Held (S : Store; F : Frontier.State; H : Header) is
   begin
      if Holds (F, H) then
         declare
            K : constant Held_Index := Witness (F, H);
         begin
            pragma Assert (not Expired (Held (F, K), S.Hz));
         end;
      end if;
   end Lemma_Expired_Not_Held;

   --  The postcondition of Put_Frame, over explicit old values. The two
   --  branches below prove it separately, each in a smaller context.
   function Put_Post
     (Old_S, S : Store; Old_F, F : Frontier.State; Frame : Byte_Array; H : Header;
      Off : Log_Size; Result : Status) return Boolean
   is
     (Valid (S, F)
      and Same_Identity (Old_S, S)
      and Horizon (S) = Horizon (Old_S)
      and Off = Log_Length (Old_S)
      and Result in OK | Dominated | Inadmissible | Malformed | No_Space | Auth_Full | Log_Full
      --  The order of DESIGN.md §7, each outcome as an iff.
      and (Result = Malformed) = Foreign_Root (Old_S, Frame)
      and (Result = Inadmissible)
            = (not Foreign_Root (Old_S, Frame) and then not Admitted (Old_F, H))
      and (Result = Dominated)
            = (not Foreign_Root (Old_S, Frame) and then Admitted (Old_F, H)
               and then not Holds (Old_F, H) and then Dom (Old_F, H))
      and (Result = Auth_Full)
            = (not Foreign_Root (Old_S, Frame) and then not Holds (Old_F, H)
               and then not Dom (Old_F, H)
               and then (Auth_Rule (Old_F, H) or else Gen_Full (Old_S, H)))
      and (Result = No_Space)
            = (not Foreign_Root (Old_S, Frame) and then Admitted (Old_F, H)
               and then At_Bound (Old_S, Old_F, H, Frame'Length))
      and (Result = Log_Full)
            = (not Foreign_Root (Old_S, Frame) and then Admitted (Old_F, H)
               and then At_Log_Bound (Old_S, Old_F, H, Frame'Length))
      --  Nothing changes on a refusal, on a duplicate, or for an expired
      --  DEL that drops nothing (T13).
      and (if Result /= OK or else Holds (Old_F, H)
              or else (Expired (H, Horizon (Old_S)) and then not Drops_Any (Old_F, H))
           then Unchanged (Old_F, F) and then S = Old_S)
      --  Append-only.
      and Log_Extends (Old_S, S)
      --  The counters (AUDIT.md H11, H28).
      and (if Result = OK and then not Holds (Old_F, H) and then Is_Auth (H)
           then Auth_Gen (Old_S) < Auth_Gen_Max and then Auth_Gen (S) = Auth_Gen (Old_S) + 1
           else Auth_Gen (S) = Auth_Gen (Old_S))
      and (if Result = OK and then not Holds (Old_F, H)
              and then Expired (H, Horizon (Old_S)) and then Drops_Any (Old_F, H)
           then Expire_Mark (S) = U48'Max (Expire_Mark (Old_S), H.V.T)
           else Expire_Mark (S) = Expire_Mark (Old_S))
      --  OK: held and indexed, or an expired DEL applied for its effect.
      and (if Result = OK and then not Holds (Old_F, H) then
             (if Expired (H, Horizon (Old_S))
              then (if Drops_Any (Old_F, H)
                    then Expired_Applied (Old_F, F, H)
                         and then Appended_Expired (Old_S, S, Frame, Off))
              else Holds (F, H)
                   and then Indexed (S, H)
                   and then Applied (Old_F, F, H)
                   and then Appended (Old_S, S, Frame, H, Off))))
   with Ghost, Pre => Frame'Length in Frame_Size and then Is_Record_Frame (Frame);

   --  Put_Frame for a DEL expired on arrival (step 4, after 1-3).
   procedure Put_Expired
     (S      : in out Store;
      F      : in out Frontier.State;
      Frame  : in     Byte_Array;
      H      : in     Header;
      Off    :    out Log_Size;
      Result :    out Status)
   with
     Global => null,
     Pre  => Valid (S, F)
       and then Frame'Length in Frame_Size
       and then Verified (S.Cid, Frame)
       and then Header_Of (S.Cid, Frame) = H
       and then Canonical (H)
       and then H.NS = S.NS
       and then not Foreign_Root (S, Frame)
       and then Expired (H, S.Hz),
     Post => Put_Post (S'Old, S, F'Old, F, Frame, H, Off, Result);

   procedure Put_Expired
     (S      : in out Store;
      F      : in out Frontier.State;
      Frame  : in     Byte_Array;
      H      : in     Header;
      Off    :    out Log_Size;
      Result :    out Status)
   is
      Saved_F : constant Frontier.State := F with Ghost;
      Short   : constant Boolean := S.Log_Cap - S.LL < Apply_Prefix + Frame'Length;
      St      : Status;
   begin
      Off := S.LL;
      pragma Assert (Log_Length (S) = S.LL);
      pragma Assert (not Auth_Rule (F, H));
      pragma Assert (not Gen_Full (S, H));
      Lemma_Expired_Not_Held (S, F, H);
      if not Admitted (F, H) or else Dom (F, H) then
         Apply_Expired (F, H, St);
         Lemma_Valid_Unchanged (S, Saved_F, F);
         Result := St;
      elsif not Drops_Any (F, H) then
         Lemma_Unchanged_Refl (F);   --  drops nothing: OK, F does not change
         Result := OK;
      elsif Short then
         Lemma_Unchanged_Refl (F);   --  a refusal: F does not change
         Result := Log_Full;
      else
         Do_Apply_Expired (S, F, Frame, H);
         Result := OK;
      end if;
   end Put_Expired;

   --  Put_Frame for all other records (steps 1-3, 5, 6).
   procedure Put_Live
     (S      : in out Store;
      F      : in out Frontier.State;
      Frame  : in     Byte_Array;
      H      : in     Header;
      Off    :    out Log_Size;
      Result :    out Status)
   with
     Global => null,
     Pre  => Valid (S, F)
       and then Frame'Length in Frame_Size
       and then Verified (S.Cid, Frame)
       and then Header_Of (S.Cid, Frame) = H
       and then Kome.Records.Kind_Of (Frame) = H.K
       and then Canonical (H)
       and then H.NS = S.NS
       and then not Foreign_Root (S, Frame)
       and then not Expired (H, S.Hz),
     Post => Put_Post (S'Old, S, F'Old, F, Frame, H, Off, Result);

   procedure Put_Live
     (S      : in out Store;
      F      : in out Frontier.State;
      Frame  : in     Byte_Array;
      H      : in     Header;
      Off    :    out Log_Size;
      Result :    out Status)
   is
      Saved_F : constant Frontier.State := F with Ghost;
      St      : Status;
   begin
      Off := S.LL;
      pragma Assert (Log_Length (S) = S.LL);
      pragma Assert (Frame (Frame'First) = Kome.Records.Tag_Of (H.K));

      --  (1), (2), (3) and the room rules of Frontier (5): Frontier.Apply
      --  gives the result and changes nothing.
      if not Admitted (F, H)
        or else Holds (F, H)
        or else Dom (F, H)
        or else Data_Full (F, H)
        or else Auth_Rule (F, H)
      then
         Apply (F, H, St);
         Lemma_Valid_Unchanged (S, Saved_F, F);
         Result := St;
         return;
      end if;

      --  (5) The authorization generation counter is at its bound
      --  (AUDIT.md H11; unreachable in practice).
      if Gen_Full (S, H) then
         Lemma_Unchanged_Refl (F);   --  a refusal: F does not change
         Result := Auth_Full;
         return;
      end if;

      --  (5) Frontier can hold it, but the log has no room for its APPLY.
      if S.Log_Cap - S.LL < Apply_Prefix + Frame'Length then
         Lemma_Unchanged_Refl (F);   --  a refusal: F does not change
         Result := Log_Full;
         return;
      end if;

      --  (6).
      Put_Fresh (S, F, Frame, H);
      Result := OK;
   end Put_Live;

   --  Put_Frame for an authorization record of a foreign founding key (0).
   procedure Put_Foreign
     (S      : in out Store;
      F      : in out Frontier.State;
      Frame  : in     Byte_Array;
      H      : in     Header;
      Off    :    out Log_Size;
      Result :    out Status)
   with
     Global => null,
     Pre  => Valid (S, F)
       and then Frame'Length in Frame_Size
       and then Verified (S.Cid, Frame)
       and then Foreign_Root (S, Frame),
     Post => Put_Post (S'Old, S, F'Old, F, Frame, H, Off, Result);

   procedure Put_Foreign
     (S      : in out Store;
      F      : in out Frontier.State;
      Frame  : in     Byte_Array;
      H      : in     Header;
      Off    :    out Log_Size;
      Result :    out Status)
   is
   begin
      Off := S.LL;
      pragma Assert (Log_Length (S) = S.LL);
      Lemma_Unchanged_Refl (F);   --  a refusal: F does not change
      Result := Malformed;
   end Put_Foreign;

   procedure Put_Frame
     (S      : in out Store;
      F      : in out Frontier.State;
      Frame  : in     Byte_Array;
      H      : in     Header;
      Off    :    out Log_Size;
      Result :    out Status)
   is
   begin
      if Kome.Records.Is_Auth_Frame (Frame)
        and then Kome.Records.Root_Key_Of (Frame) /= S.Fnd
      then
         Put_Foreign (S, F, Frame, H, Off, Result);
      elsif Expired (H, S.Hz) then
         Put_Expired (S, F, Frame, H, Off, Result);
      else
         Put_Live (S, F, Frame, H, Off, Result);
      end if;
   end Put_Frame;

   --  The postcondition of Expire, over explicit old values.
   function Expire_Post
     (Old_S, S : Store; Old_F, F : Frontier.State; Now : U48; Result : Status)
      return Boolean
   is
     (Valid (S, F)
      and Same_Identity (Old_S, S)
      and Auth_Gen (S) = Auth_Gen (Old_S)
      and Result in OK | Log_Full
      and (Result = Log_Full)
            = (Logs_Expire (Old_S, Old_F, Now) and then Log_Short (Old_S, Expire_Len))
      and (if Result = Log_Full then Unchanged (Old_F, F) and then S = Old_S)
      and Log_Extends (Old_S, S)
      and (if Result = OK then
             Horizon (S) = Horizon_At (Old_F, Now)
             and then Horizon (S) <= Horizon_At (Old_F, U48'Last)
             --  The held set is the old set minus exactly the DELs at or
             --  below the new horizon (none if the horizon did not rise).
             and then Expired_Out (Old_F, F, Horizon (S))
             and then (if Logs_Expire (Old_S, Old_F, Now)
                       then Appended_Expire (Old_S, S, Log_Length (Old_S), Horizon (S))
                       else Log_Length (S) = Log_Length (Old_S)
                            and then Log_Entries (S) = Log_Entries (Old_S))
             and then (if Horizon (S) > Horizon (Old_S)
                       then Expire_Mark (S) = U48'Max (Expire_Mark (Old_S), U48 (Horizon (S)))
                       else Expire_Mark (S) = Expire_Mark (Old_S)))
      and Expire_Mark (S) >= Expire_Mark (Old_S)
      --  T11 (a): no held DEL is at or below the horizon.
      and (for all I in 1 .. Count (F) => not Expired (Held (F, I), Horizon (S))))
   with Ghost, Pre => Is_Frontier (Old_F);

   --  Expire when the horizon rises.
   procedure Expire_Raise
     (S : in out Store; F : in out Frontier.State; Now : U48; Result : out Status)
   with
     Global => null,
     Pre  => Valid (S, F) and then Horizon_At (F, Now) > S.Hz,
     Post => Expire_Post (S'Old, S, F'Old, F, Now, Result);

   procedure Expire_Raise
     (S : in out Store; F : in out Frontier.State; Now : U48; Result : out Status)
   is
      Hn : constant Horizon_Value := Horizon_At (F, Now);
   begin
      pragma Assert (Hn <= Horizon_At (F, U48'Last));
      if Expires_Any (F, Hn) then
         if S.Log_Cap - S.LL < Expire_Len then
            Lemma_Unchanged_Refl (F);   --  a refusal: F does not change
            Result := Log_Full;
            return;
         end if;
         Do_Expire (S, F, Hn, Horizon_Code (Hn));
      else
         pragma Assert (for all K in 1 .. Count (F) => not Expired (Held (F, K), Hn));
         Lemma_Out_Refl (F, Hn, Hn);
         S.Hz := Hn;
         S.EM := U48'Max (S.EM, U48 (Hn));   --  AUDIT.md H28
         pragma Assert (Valid (S, F));
      end if;
      Result := OK;
   end Expire_Raise;

   --  Expire when the horizon goes down or stays the same.
   procedure Expire_Other
     (S : in out Store; F : in out Frontier.State; Now : U48; Result : out Status)
   with
     Global => null,
     Pre  => Valid (S, F) and then Horizon_At (F, Now) <= S.Hz,
     Post => Expire_Post (S'Old, S, F'Old, F, Now, Result);

   procedure Expire_Other
     (S : in out Store; F : in out Frontier.State; Now : U48; Result : out Status)
   is
      Hn : constant Horizon_Value := Horizon_At (F, Now);
   begin
      pragma Assert (Hn <= Horizon_At (F, U48'Last));
      if Hn < S.Hz then
         if S.Log_Cap - S.LL < Expire_Len then
            Lemma_Unchanged_Refl (F);   --  a refusal: F does not change
            Result := Log_Full;
            return;
         end if;
         Do_Expire (S, F, Hn, Horizon_Code (Hn));
      else
         Lemma_Out_Refl (F, S.Hz, Hn);
      end if;
      Result := OK;
   end Expire_Other;

   procedure Expire
     (S      : in out Store;
      F      : in out Frontier.State;
      Now    : in     U48;
      Result :    out Status)
   is
   begin
      if Horizon_At (F, Now) > S.Hz then
         Expire_Raise (S, F, Now, Result);
      else
         Expire_Other (S, F, Now, Result);
      end if;
   end Expire;

   ---------------------------------------------------------------------------
   --  Compaction.
   ---------------------------------------------------------------------------

   --  Dst (W .. W + Size - 1) := Src (From .. From + Size - 1); no byte
   --  below W changes. The Post states the first six bytes (op, length, tag)
   --  one by one, so callers need no instantiation at +0.
   procedure Copy_Bytes
     (Dst : in out Byte_Array; W : Natural; Src : Byte_Array; From : Natural;
      Size : Positive)
   with
     Global => null,
     Pre  => Dst'First = 0 and then Src'First = 0
             and then Dst'Last <= Log_Max and then Src'Last <= Log_Max
             and then Size >= Min_Entry
             and then W <= Dst'Last and then Size - 1 <= Dst'Last - W
             and then From <= Src'Last and then Size - 1 <= Src'Last - From,
     Post => (for all P in 0 .. W - 1 => Dst (P) = Dst'Old (P))
       and then (for all K in 0 .. Size - 1 => Dst (W + K) = Src (From + K))
       and then Dst (W) = Src (From)
       and then Dst (W + 1) = Src (From + 1)
       and then Dst (W + 2) = Src (From + 2)
       and then Dst (W + 3) = Src (From + 3)
       and then Dst (W + 4) = Src (From + 4)
       and then Dst (W + 5) = Src (From + 5);

   procedure Copy_Bytes
     (Dst : in out Byte_Array; W : Natural; Src : Byte_Array; From : Natural;
      Size : Positive)
   is
   begin
      for K in 0 .. Size - 1 loop
         Dst (W + K) := Src (From + K);
         pragma Loop_Invariant (for all P in 0 .. W - 1 => Dst (P) = Dst'Loop_Entry (P));
         pragma Loop_Invariant (for all K2 in 0 .. K => Dst (W + K2) = Src (From + K2));
      end loop;
   end Copy_Bytes;

   type Size_Map is array (Natural range <>) of Natural;

   --  Prefix sums over Idx (1 .. N), ghost: the bytes and the number of
   --  authorization (A) and data (D) entries among the first I.
   type Prefix (N : Held_Count) is record
      SA, SD : Size_Map (0 .. N);
      CA, CD : Size_Map (0 .. N);
   end record;

   function Part_Of (X : Header; Data : Boolean) return Boolean is (Is_Data (X) = Data);

   --  The prefix sums are those of Idx, and they fit before LL.
   function Prefix_OK (P : Prefix; Idx : Entry_Array; LL : Natural) return Boolean is
     (P.SA (0) = 0 and then P.SD (0) = 0 and then P.CA (0) = 0 and then P.CD (0) = 0
      and then (for all I in 1 .. P.N =>
                  P.SA (I) - P.SA (I - 1)
                    = (if Is_Auth (Idx (I).H) then Apply_Prefix + Idx (I).Len else 0)
                  and then P.SD (I) - P.SD (I - 1)
                    = (if Is_Data (Idx (I).H) then Apply_Prefix + Idx (I).Len else 0)
                  and then P.CA (I) - P.CA (I - 1) = (if Is_Auth (Idx (I).H) then 1 else 0)
                  and then P.CD (I) - P.CD (I - 1) = (if Is_Data (Idx (I).H) then 1 else 0))
      and then (for all I in 0 .. P.N => P.CA (I) = I - P.CD (I))
      and then (for all I in 0 .. P.N => P.SA (I) >= Min_Entry * I - P.SD (I))
      and then (for all I in 0 .. P.N =>
                  P.SD (I) <= LL - Header_Len and then P.SA (I) <= LL - Header_Len - P.SD (I))
      and then (for all I in 0 .. P.N =>
                  P.SA (I) <= P.SA (P.N) and then P.SD (I) <= P.SD (P.N)
                  and then P.CA (I) <= P.CA (P.N) and then P.CD (I) <= P.CD (P.N)))
     with Ghost, Pre => Idx'First = 1 and then P.N <= Idx'Last;

   function Prefix_Of (Idx : Entry_Array; N : Held_Count; LL : Log_Size) return Prefix with
     Global => null,
     Pre  => Idx'First = 1 and then N <= Idx'Last
             and then LL >= Header_Len
             and then Sorted (Idx, N)
             and then (for all I in 1 .. N => Idx (I).Off >= Header_Len and then End_Of (Idx (I)) <= LL),
     Post => Prefix_Of'Result.N = N and then Prefix_OK (Prefix_Of'Result, Idx, LL);

   function Prefix_Of (Idx : Entry_Array; N : Held_Count; LL : Log_Size) return Prefix is
      P : Prefix (N) := (N => N, SA => [others => 0], SD => [others => 0],
                         CA => [others => 0], CD => [others => 0]);
   begin
      for I in 1 .. N loop
         pragma Assert (P.SD (I - 1) <= Idx (I).Off - Header_Len);
         pragma Assert (P.SA (I - 1) <= Idx (I).Off - Header_Len - P.SD (I - 1));
         if Is_Auth (Idx (I).H) then
            P.SA (I) := P.SA (I - 1) + Apply_Prefix + Idx (I).Len;
            P.SD (I) := P.SD (I - 1);
            P.CA (I) := P.CA (I - 1) + 1;
            P.CD (I) := P.CD (I - 1);
         else
            P.SA (I) := P.SA (I - 1);
            P.SD (I) := P.SD (I - 1) + Apply_Prefix + Idx (I).Len;
            P.CA (I) := P.CA (I - 1);
            P.CD (I) := P.CD (I - 1) + 1;
         end if;
         pragma Loop_Invariant (P.SA (0) = 0 and then P.SD (0) = 0
                                and then P.CA (0) = 0 and then P.CD (0) = 0);
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              P.SA (I2) - P.SA (I2 - 1)
                = (if Is_Auth (Idx (I2).H) then Apply_Prefix + Idx (I2).Len else 0)
              and then P.SD (I2) - P.SD (I2 - 1)
                = (if Is_Data (Idx (I2).H) then Apply_Prefix + Idx (I2).Len else 0)
              and then P.CA (I2) - P.CA (I2 - 1) = (if Is_Auth (Idx (I2).H) then 1 else 0)
              and then P.CD (I2) - P.CD (I2 - 1) = (if Is_Data (Idx (I2).H) then 1 else 0));
         pragma Loop_Invariant (for all I2 in 0 .. I => P.CA (I2) = I2 - P.CD (I2));
         pragma Loop_Invariant
           (for all I2 in 0 .. I => P.SA (I2) >= Min_Entry * I2 - P.SD (I2));
         pragma Loop_Invariant
           (P.SD (I) <= End_Of (Idx (I)) - Header_Len
            and then P.SA (I) <= End_Of (Idx (I)) - Header_Len - P.SD (I));
         pragma Loop_Invariant
           (for all I2 in 0 .. I =>
              P.SD (I2) <= LL - Header_Len and then P.SA (I2) <= LL - Header_Len - P.SD (I2));
         pragma Loop_Invariant
           (for all I2 in 0 .. I =>
              P.SA (I2) <= P.SA (I) and then P.SD (I2) <= P.SD (I)
              and then P.CA (I2) <= P.CA (I) and then P.CD (I2) <= P.CD (I));
      end loop;
      return P;
   end Prefix_Of;

   --  A (PA .. PA + Len - 1) = B (PB .. PB + Len - 1), both in range.
   --  Its Post defines it, so a range of byte equalities is one atom.
   function Bytes_Eq
     (A : Byte_Array; PA : Natural; B : Byte_Array; PB : Natural; Len : Natural)
      return Boolean
   with
     Ghost, Global => null,
     Pre  => A'First = 0 and then B'First = 0,
     Post => Bytes_Eq'Result =
       ((Len = 0
         or else (PA <= A'Last and then Len - 1 <= A'Last - PA
                  and then PB <= B'Last and then Len - 1 <= B'Last - PB))
        and then (for all M in 0 .. Len - 1 => A (PA + M) = B (PB + M)));

   function Bytes_Eq
     (A : Byte_Array; PA : Natural; B : Byte_Array; PB : Natural; Len : Natural)
      return Boolean
   is
     ((Len = 0
       or else (PA <= A'Last and then Len - 1 <= A'Last - PA
                and then PB <= B'Last and then Len - 1 <= B'Last - PB))
      and then (for all M in 0 .. Len - 1 => A (PA + M) = B (PB + M)));

   --  The first K entries of New_Idx are copies of Idx entries:
   --    * their records, lengths and APPLY bytes are copied, with no gaps,
   --      from Header_Len to W;
   --    * the authorization records are first (the first CA entries), and
   --      each part is in index order;
   --    * Src (J) is the old position of new entry J.
   --  Its Post defines it, so it is one atom in goals that only carry it
   --  along.
   function Copied
     (Log : Byte_Array; Idx : Entry_Array; N : Held_Count; CA : Natural;
      New_Log : Byte_Array; W : Log_Size; New_Idx : Entry_Array; K : Held_Count;
      Src : Index_Map) return Boolean
   with
     Ghost, Global => null,
     Pre  => Log'First = 0 and then New_Log'First = 0
             and then Log'Last <= Log_Max and then New_Log'Last <= Log_Max
             and then W <= New_Log'Last
             and then Idx'First = 1 and then N <= Idx'Last
             and then New_Idx'First = 1 and then K <= New_Idx'Last
             and then Src'First = 1 and then K <= Src'Last,
     Post => Copied'Result =
       ((for all J in 1 .. K =>
           Src (J) in 1 .. N
           and then New_Idx (J).H = Idx (Src (J)).H
           and then New_Idx (J).Len = Idx (Src (J)).Len
           and then New_Idx (J).Off >= Header_Len
           and then End_Of (New_Idx (J)) <= W
           and then Idx (Src (J)).Off <= Log'Last
           and then Apply_Prefix + Idx (Src (J)).Len - 1 <= Log'Last - Idx (Src (J)).Off
           and then Is_Data (Idx (Src (J)).H) = (J > CA))
        and then (for all J in 1 .. K =>
                    Bytes_Eq (New_Log, New_Idx (J).Off,
                       Log, Idx (Src (J)).Off,
                       Apply_Prefix + New_Idx (J).Len))
        and then (if K > 0 then New_Idx (1).Off = Header_Len and then W = End_Of (New_Idx (K))
                  else W = Header_Len)
        and then (for all J in 1 .. K - 1 => New_Idx (J + 1).Off = End_Of (New_Idx (J)))
        and then (for all J in 1 .. K =>
                    (for all J2 in J + 1 .. K =>
                       (if J2 <= CA or else J > CA then Src (J) < Src (J2)))));

   function Copied
     (Log : Byte_Array; Idx : Entry_Array; N : Held_Count; CA : Natural;
      New_Log : Byte_Array; W : Log_Size; New_Idx : Entry_Array; K : Held_Count;
      Src : Index_Map) return Boolean
   is
     ((for all J in 1 .. K =>
         Src (J) in 1 .. N
         and then New_Idx (J).H = Idx (Src (J)).H
         and then New_Idx (J).Len = Idx (Src (J)).Len
         and then New_Idx (J).Off >= Header_Len
         and then End_Of (New_Idx (J)) <= W
         and then Idx (Src (J)).Off <= Log'Last
         and then Apply_Prefix + Idx (Src (J)).Len - 1 <= Log'Last - Idx (Src (J)).Off
         and then Is_Data (Idx (Src (J)).H) = (J > CA))
      and then (for all J in 1 .. K =>
                  Bytes_Eq (New_Log, New_Idx (J).Off,
                     Log, Idx (Src (J)).Off,
                     Apply_Prefix + New_Idx (J).Len))
      and then (if K > 0 then New_Idx (1).Off = Header_Len and then W = End_Of (New_Idx (K))
                else W = Header_Len)
      and then (for all J in 1 .. K - 1 => New_Idx (J + 1).Off = End_Of (New_Idx (J)))
      and then (for all J in 1 .. K =>
                  (for all J2 in J + 1 .. K =>
                     (if J2 <= CA or else J > CA then Src (J) < Src (J2)))));

   --  The full definition of Bytes_Eq.
   procedure Lemma_Bytes_Unfold
     (A : Byte_Array; PA : Natural; B : Byte_Array; PB : Natural; Len : Natural)
   with
     Ghost, Global => null,
     Pre  => A'First = 0 and then B'First = 0 and then Bytes_Eq (A, PA, B, PB, Len),
     Post => (Len = 0
              or else (PA <= A'Last and then Len - 1 <= A'Last - PA
                       and then PB <= B'Last and then Len - 1 <= B'Last - PB))
       and then (for all M in 0 .. Len - 1 => A (PA + M) = B (PB + M))
       and then (if Len > 0 then A (PA) = B (PB));

   procedure Lemma_Bytes_Unfold
     (A : Byte_Array; PA : Natural; B : Byte_Array; PB : Natural; Len : Natural) is
   begin
      pragma Assert (for all M in 0 .. Len - 1 => A (PA + M) = B (PB + M));
      if Len > 0 then
         pragma Assert (for all M in 0 .. 0 => A (PA + M) = B (PB + M));
         pragma Assert (A (PA) = B (PB));
      end if;
   end Lemma_Bytes_Unfold;

   --  Bytes below W0 do not change, so a copy below W0 does not
   --  change.
   procedure Lemma_Bytes_Kept
     (Old_Log, New_Log : Byte_Array; W0 : Natural; Log : Byte_Array;
      Off, From, Len : Natural)
   with
     Ghost, Global => null,
     Pre  => Old_Log'First = 0 and then New_Log'First = 0 and then Log'First = 0
       and then Old_Log'Last = New_Log'Last
       and then New_Log'Last <= Log_Max and then Log'Last <= Log_Max
       and then W0 <= New_Log'Last + 1
       and then Off <= W0 and then Len <= W0 - Off
       and then (for all Q in 0 .. W0 - 1 => New_Log (Q) = Old_Log (Q))
       and then Bytes_Eq (Old_Log, Off, Log, From, Len),
     Post => Bytes_Eq (New_Log, Off, Log, From, Len);

   procedure Lemma_Bytes_Kept
     (Old_Log, New_Log : Byte_Array; W0 : Natural; Log : Byte_Array;
      Off, From, Len : Natural) is
   begin
      Lemma_Bytes_Unfold (Old_Log, Off, Log, From, Len);
      for M in 0 .. Len - 1 loop
         pragma Assert (Off + M < W0);
         pragma Assert (New_Log (Off + M) = Old_Log (Off + M));
         pragma Assert (Old_Log (Off + M) = Log (From + M));
         pragma Assert (New_Log (Off + M) = Log (From + M));
         pragma Loop_Invariant
           (for all M2 in 0 .. M => New_Log (Off + M2) = Log (From + M2));
      end loop;
   end Lemma_Bytes_Kept;

   --  The full definition of Copied (so a caller gets its parts as
   --  hypotheses).
   procedure Lemma_Copied_Unfold
     (Log : Byte_Array; Idx : Entry_Array; N : Held_Count; CA : Natural;
      New_Log : Byte_Array; W : Log_Size; New_Idx : Entry_Array; K : Held_Count;
      Src : Index_Map)
   with
     Ghost, Global => null,
     Pre  => Log'First = 0 and then New_Log'First = 0
             and then Log'Last <= Log_Max and then New_Log'Last <= Log_Max
             and then W <= New_Log'Last
             and then Idx'First = 1 and then N <= Idx'Last
             and then New_Idx'First = 1 and then K <= New_Idx'Last
             and then Src'First = 1 and then K <= Src'Last
             and then Copied (Log, Idx, N, CA, New_Log, W, New_Idx, K, Src),
     Post => (for all J in 1 .. K =>
                Src (J) in 1 .. N
                and then New_Idx (J).H = Idx (Src (J)).H
                and then New_Idx (J).Len = Idx (Src (J)).Len
                and then New_Idx (J).Off >= Header_Len
                and then End_Of (New_Idx (J)) <= W
                and then Is_Data (Idx (Src (J)).H) = (J > CA))
       and then (for all J in 1 .. K =>
                   Bytes_Eq (New_Log, New_Idx (J).Off,
                      Log, Idx (Src (J)).Off,
                      Apply_Prefix + New_Idx (J).Len))
       and then (if K > 0 then New_Idx (1).Off = Header_Len and then W = End_Of (New_Idx (K))
                 else W = Header_Len)
       and then (for all J in 1 .. K - 1 => New_Idx (J + 1).Off = End_Of (New_Idx (J)))
       and then (for all J in 1 .. K =>
                   (for all J2 in J + 1 .. K =>
                      (if J2 <= CA or else J > CA then Src (J) < Src (J2))));

   procedure Lemma_Copied_Unfold
     (Log : Byte_Array; Idx : Entry_Array; N : Held_Count; CA : Natural;
      New_Log : Byte_Array; W : Log_Size; New_Idx : Entry_Array; K : Held_Count;
      Src : Index_Map) is null;

   --  Copy entry I of Idx as new entry K + 1 at W, and keep Copied.
   procedure Copy_One
     (Log     : Byte_Array;
      LL      : Log_Size;
      Idx     : Entry_Array;
      N       : Held_Count;
      CA      : Natural;
      I       : Held_Index;
      New_Log : in out Byte_Array;
      W       : in out Log_Size;
      New_Idx : in out Entry_Array;
      K       : in out Held_Count;
      Src     : in out Index_Map)
   with
     Global => null,
     Pre  => Log'First = 0 and then Log'Last <= Log_Max and then LL <= Log'Last
       and then New_Log'First = 0 and then New_Log'Last = Log'Last
       and then Idx'First = 1 and then N <= Idx'Last
       and then New_Idx'First = 1 and then New_Idx'Last = Idx'Last
       and then Src'First = 1 and then Src'Last = N
       and then I <= N
       and then K < N
       and then W >= Header_Len
       and then Frame_OK (Log, LL, Idx (I))
       and then W + Apply_Prefix + Idx (I).Len <= LL
       and then Is_Data (Idx (I).H) = (K + 1 > CA)
       and then (for all J in 1 .. K => (if K + 1 <= CA or else J > CA then Src (J) < I))
       and then Copied (Log, Idx, N, CA, New_Log, W, New_Idx, K, Src),
     Post => K = K'Old + 1
       and then W = W'Old + Apply_Prefix + Idx (I).Len
       and then Src (K) = I
       and then (for all J in 1 .. K'Old => Src (J) = Src'Old (J))
       and then (for all J in 1 .. K'Old => New_Idx (J) = New_Idx'Old (J))
       and then (for all Q in 0 .. Header_Len - 1 => New_Log (Q) = New_Log'Old (Q))
       and then Copied (Log, Idx, N, CA, New_Log, W, New_Idx, K, Src);

   procedure Copy_One
     (Log     : Byte_Array;
      LL      : Log_Size;
      Idx     : Entry_Array;
      N       : Held_Count;
      CA      : Natural;
      I       : Held_Index;
      New_Log : in out Byte_Array;
      W       : in out Log_Size;
      New_Idx : in out Entry_Array;
      K       : in out Held_Count;
      Src     : in out Index_Map)
   is
      Old_Log : constant Byte_Array := New_Log with Ghost;
      Old_Idx : constant Entry_Array := New_Idx with Ghost;
      Old_Src : constant Index_Map := Src with Ghost;
      W0      : constant Log_Size := W;
      K0      : constant Held_Count := K;
      Size    : constant Positive := Apply_Prefix + Idx (I).Len;
   begin
      pragma Assert (Copied (Log, Idx, N, CA, Old_Log, W0, Old_Idx, K0, Old_Src));
      pragma Assert
        (for all J in 1 .. K0 =>
           Bytes_Eq (Old_Log, Old_Idx (J).Off,
              Log, Idx (Old_Src (J)).Off,
              Apply_Prefix + Old_Idx (J).Len));
      pragma Assert
        (for all J in 1 .. K0 =>
           End_Of (Old_Idx (J)) <= W0
           and then Old_Src (J) in 1 .. N
           and then Idx (Old_Src (J)).Off <= Log'Last
           and then Apply_Prefix + Old_Idx (J).Len - 1 <= Log'Last - Idx (Old_Src (J)).Off);
      pragma Assert
        (for all J in 1 .. K0 =>
           (for all J2 in J + 1 .. K0 =>
              (if J2 <= CA or else J > CA then Old_Src (J) < Old_Src (J2))));
      Copy_Bytes (New_Log, W0, Log, Idx (I).Off, Size);
      pragma Assert (Bytes_Eq (New_Log, W0, Log, Idx (I).Off, Size));
      K := K0 + 1;
      New_Idx (K) := (H => Idx (I).H, Off => W0, Len => Idx (I).Len);
      Src (K) := I;
      W := W0 + Size;
      pragma Assert (for all J in 1 .. K0 => New_Idx (J) = Old_Idx (J));
      pragma Assert (for all J in 1 .. K0 => Src (J) = Old_Src (J));
      pragma Assert (for all Q in 0 .. W0 - 1 => New_Log (Q) = Old_Log (Q));
      pragma Assert
        (for all J in 1 .. K0 =>
           End_Of (New_Idx (J)) <= W0
           and then Src (J) in 1 .. N
           and then Idx (Src (J)).Off <= Log'Last
           and then Apply_Prefix + New_Idx (J).Len - 1 <= Log'Last - Idx (Src (J)).Off);
      pragma Assert
        (for all J in 1 .. K0 =>
           Bytes_Eq (Old_Log, New_Idx (J).Off,
              Log, Idx (Src (J)).Off,
              Apply_Prefix + New_Idx (J).Len));
      --  The entries copied before keep their bytes: they are below W0.
      for J in 1 .. K0 loop
         pragma Assert (End_Of (New_Idx (J)) <= W0);
         pragma Assert
           (Bytes_Eq (Old_Log, New_Idx (J).Off,
              Log, Idx (Src (J)).Off,
              Apply_Prefix + New_Idx (J).Len));
         Lemma_Bytes_Kept (Old_Log, New_Log, W0, Log, New_Idx (J).Off,
                           Idx (Src (J)).Off, Apply_Prefix + New_Idx (J).Len);
         pragma Assert
           (Bytes_Eq (New_Log, New_Idx (J).Off,
              Log, Idx (Src (J)).Off,
              Apply_Prefix + New_Idx (J).Len));
         pragma Loop_Invariant
           (for all J2 in 1 .. J =>
              Bytes_Eq (New_Log, New_Idx (J2).Off,
                 Log, Idx (Src (J2)).Off,
                 Apply_Prefix + New_Idx (J2).Len));
      end loop;
      pragma Assert
        (Bytes_Eq (New_Log, New_Idx (K).Off,
           Log, Idx (Src (K)).Off,
           Apply_Prefix + New_Idx (K).Len));
      pragma Assert
        (for all J in 1 .. K =>
           Bytes_Eq (New_Log, New_Idx (J).Off,
              Log, Idx (Src (J)).Off,
              Apply_Prefix + New_Idx (J).Len));
      pragma Assert (if K0 > 0 then New_Idx (K).Off = End_Of (New_Idx (K0)));
      pragma Assert (for all J in 1 .. K - 1 => New_Idx (J + 1).Off = End_Of (New_Idx (J)));
      pragma Assert
        (for all J in 1 .. K0 =>
           (for all J2 in J + 1 .. K0 =>
              (if J2 <= CA or else J > CA then Src (J) < Src (J2))));
      pragma Assert
        (for all J in 1 .. K0 => (if K <= CA or else J > CA then Src (J) < Src (K)));
      pragma Assert
        (for all J in 1 .. K =>
           (for all J2 in J + 1 .. K =>
              (if J2 <= CA or else J > CA then Src (J) < Src (J2))));
      pragma Assert
        (for all J in 1 .. K0 =>
           Old_Src (J) in 1 .. N
           and then Old_Idx (J).H = Idx (Old_Src (J)).H
           and then Old_Idx (J).Len = Idx (Old_Src (J)).Len
           and then Old_Idx (J).Off >= Header_Len
           and then End_Of (Old_Idx (J)) <= W0
           and then Is_Data (Idx (Old_Src (J)).H) = (J > CA));
      pragma Assert
        (for all J in 1 .. K0 =>
           Src (J) in 1 .. N
           and then New_Idx (J).H = Idx (Src (J)).H
           and then New_Idx (J).Len = Idx (Src (J)).Len
           and then New_Idx (J).Off >= Header_Len
           and then End_Of (New_Idx (J)) <= W
           and then Idx (Src (J)).Off <= Log'Last
           and then Apply_Prefix + Idx (Src (J)).Len - 1 <= Log'Last - Idx (Src (J)).Off
           and then Is_Data (Idx (Src (J)).H) = (J > CA));
      pragma Assert
        (Src (K) in 1 .. N
         and then New_Idx (K).H = Idx (Src (K)).H
         and then New_Idx (K).Len = Idx (Src (K)).Len
         and then New_Idx (K).Off >= Header_Len
         and then End_Of (New_Idx (K)) <= W
         and then Idx (Src (K)).Off <= Log'Last
         and then Apply_Prefix + Idx (Src (K)).Len - 1 <= Log'Last - Idx (Src (K)).Off
         and then Is_Data (Idx (Src (K)).H) = (K > CA));
      pragma Assert
        (for all J in 1 .. K =>
           Src (J) in 1 .. N
           and then New_Idx (J).H = Idx (Src (J)).H
           and then New_Idx (J).Len = Idx (Src (J)).Len
           and then New_Idx (J).Off >= Header_Len
           and then End_Of (New_Idx (J)) <= W
           and then Idx (Src (J)).Off <= Log'Last
           and then Apply_Prefix + Idx (Src (J)).Len - 1 <= Log'Last - Idx (Src (J)).Off
           and then Is_Data (Idx (Src (J)).H) = (J > CA));
      pragma Assert (if K > 0 then New_Idx (1).Off = Header_Len and then W = End_Of (New_Idx (K)));
      pragma Assert (Copied (Log, Idx, N, CA, New_Log, W, New_Idx, K, Src));
   end Copy_One;

   --  Copy the frames of one part (the data records iff Data) of
   --  Idx (1 .. N) in index order. Copy them from Log into New_Log, with no
   --  gaps, from W. Append their entries to New_Idx from K + 1, and keep
   --  Copied. Dst (J) is the new position of old entry J.
   procedure Copy_Part
     (Log     : Byte_Array;
      LL      : Log_Size;
      Idx     : Entry_Array;
      N       : Held_Count;
      P       : Prefix;
      Data    : Boolean;
      New_Log : in out Byte_Array;
      W       : in out Log_Size;
      New_Idx : in out Entry_Array;
      K       : in out Held_Count;
      Src     : in out Index_Map;
      Dst     : in out Index_Map)
   with
     Global => null,
     Pre  => Log'First = 0 and then Log'Last <= Log_Max and then LL <= Log'Last
       and then New_Log'First = 0 and then New_Log'Last = Log'Last
       and then Idx'First = 1 and then N <= Idx'Last
       and then New_Idx'First = 1 and then New_Idx'Last = Idx'Last
       and then Src'First = 1 and then Src'Last = N
       and then Dst'First = 1 and then Dst'Last = N
       and then P.N = N
       and then Prefix_OK (P, Idx, LL)
       and then Framed (Log, LL, Idx, N)
       and then W = Header_Len + (if Data then P.SA (N) else 0)
       and then K = (if Data then P.CA (N) else 0)
       and then Copied (Log, Idx, N, P.CA (N), New_Log, W, New_Idx, K, Src)
       and then (if Data then
                   (for all J in 1 .. N =>
                      (if not Is_Data (Idx (J).H)
                       then Dst (J) in 1 .. K and then Src (Dst (J)) = J))),
     Post => W = W'Old + (if Data then P.SD (N) else P.SA (N))
       and then K = K'Old + (if Data then P.CD (N) else P.CA (N))
       and then Copied (Log, Idx, N, P.CA (N), New_Log, W, New_Idx, K, Src)
       and then (for all Q in 0 .. Header_Len - 1 => New_Log (Q) = New_Log'Old (Q))
       and then (for all J in 1 .. N =>
                   (if Data or else not Is_Data (Idx (J).H)
                    then Dst (J) in 1 .. K and then Src (Dst (J)) = J));

   procedure Copy_Part
     (Log     : Byte_Array;
      LL      : Log_Size;
      Idx     : Entry_Array;
      N       : Held_Count;
      P       : Prefix;
      Data    : Boolean;
      New_Log : in out Byte_Array;
      W       : in out Log_Size;
      New_Idx : in out Entry_Array;
      K       : in out Held_Count;
      Src     : in out Index_Map;
      Dst     : in out Index_Map)
   is
      W0 : constant Log_Size := W;
      K0 : constant Held_Count := K;
      CA : constant Natural := P.CA (N);
   begin
      pragma Assert (W0 >= Header_Len);
      for I in 1 .. N loop
         pragma Assert (Frame_OK (Log, LL, Idx (I)));
         if Part_Of (Idx (I).H, Data) then
            pragma Assert
              (W = W0 + (if Data then P.SD (I - 1) else P.SA (I - 1)));
            pragma Assert
              (W + Apply_Prefix + Idx (I).Len = W0 + (if Data then P.SD (I) else P.SA (I)));
            pragma Assert (W + Apply_Prefix + Idx (I).Len <= LL);
            pragma Assert (K < N);
            pragma Assert (Is_Data (Idx (I).H) = (K + 1 > CA));
            Copy_One (Log, LL, Idx, N, CA, I, New_Log, W, New_Idx, K, Src);
            Dst (I) := K;
            pragma Assert (for all J in 1 .. K => (if J > K0 then Src (J) <= I));
         end if;
         pragma Loop_Invariant (W = W0 + (if Data then P.SD (I) else P.SA (I)));
         pragma Loop_Invariant (K = K0 + (if Data then P.CD (I) else P.CA (I)));
         pragma Loop_Invariant (Copied (Log, Idx, N, CA, New_Log, W, New_Idx, K, Src));
         pragma Loop_Invariant
           (for all Q in 0 .. Header_Len - 1 => New_Log (Q) = New_Log'Loop_Entry (Q));
         pragma Loop_Invariant (for all J in 1 .. K0 => Src (J) = Src'Loop_Entry (J));
         pragma Loop_Invariant
           (for all J in 1 .. N =>
              (if not Part_Of (Idx (J).H, Data) then Dst (J) = Dst'Loop_Entry (J)));
         pragma Loop_Invariant
           (for all J in 1 .. K => (if J > K0 then Src (J) <= I));
         --  The witnesses Dst, in two parts (prover time): the entries of
         --  the earlier pass, then the entries of this pass up to now.
         pragma Loop_Invariant
           (for all J in 1 .. N =>
              (if Data and then not Is_Data (Idx (J).H)
               then Dst (J) in 1 .. K and then Src (Dst (J)) = J));
         pragma Loop_Invariant
           (for all J in 1 .. I =>
              (if Part_Of (Idx (J).H, Data)
               then Dst (J) in 1 .. K and then Src (Dst (J)) = J));
      end loop;
      pragma Assert (Copied (Log, Idx, N, CA, New_Log, W, New_Idx, K, Src));
   end Copy_Part;

   --  One APPLY of a compacted log is an entry of its chain.
   procedure Lemma_Compacted_Entry (Log : Byte_Array; LL, W : Log_Size; E : Index_Entry) with
     Ghost, Global => null,
     Pre  => Log'First = 0 and then LL <= Log'Last and then W <= LL
             and then Frame_OK (Log, W, E),
     Post => Frame_OK (Log, LL, E)
             and then E.Off < LL
             and then Entry_OK (Log, LL, E.Off)
             and then Log (E.Off) /= Op_Header
             and then E.Off + Size_At (Log, E.Off) = End_Of (E);

   procedure Lemma_Compacted_Entry (Log : Byte_Array; LL, W : Log_Size; E : Index_Entry) is
   begin
      pragma Assert (Log (E.Off) = Op_Apply);
      pragma Assert (Len_Word (Log, E.Off) = Word (E.Len));
      pragma Assert (Size_At (Log, E.Off) = Apply_Prefix + E.Len);
   end Lemma_Compacted_Entry;

   --  The compacted log is a chain: the HEADER, the entries with no gaps
   --  from Header_Len to W, then EXPIRE iff Ex.
   procedure Lemma_Chain_Compacted
     (Log : Byte_Array; LL : Log_Size; W : Log_Size; Idx : Entry_Array; N : Held_Count;
      Bnd : Offset_Array; NB : Natural; Ex : Boolean)
   with
     Ghost, Global => null,
     Pre  => Log'First = 0 and then LL <= Log'Last
       and then Idx'First = 1 and then N <= Idx'Last
       and then Bnd'First = 1 and then NB <= Bnd'Last
       and then (if Ex then NB = N + 2 else NB = N + 1)
       and then Log (0) = Op_Header
       and then W >= Header_Len + Min_Entry * N
       and then W <= LL
       and then Framed (Log, W, Idx, N)
       and then (if N > 0 then Idx (1).Off = Header_Len and then W = End_Of (Idx (N))
                 else W = Header_Len)
       and then (for all J in 1 .. N - 1 => Idx (J + 1).Off = End_Of (Idx (J)))
       and then Bnd (1) = 0
       and then (for all J in 1 .. N => Bnd (J + 1) = Idx (J).Off)
       and then (if Ex then LL = W + Expire_Len and then Log (W) = Op_Expire
                            and then Bnd (N + 2) = W
                 else LL = W),
     Post => Chain (Log, LL, Bnd, NB)
       and then Framed (Log, LL, Idx, N)
       and then At_Bounds (Idx, N, Bnd, NB);

   procedure Lemma_Chain_Compacted
     (Log : Byte_Array; LL : Log_Size; W : Log_Size; Idx : Entry_Array; N : Held_Count;
      Bnd : Offset_Array; NB : Natural; Ex : Boolean)
   is
   begin
      pragma Assert (Entry_OK (Log, LL, 0));
      pragma Assert (Size_At (Log, 0) = Header_Len);
      pragma Assert (Bnd (1) + Size_At (Log, Bnd (1)) = (if 1 < NB then Bnd (2) else LL));
      for J in 1 .. N loop
         pragma Assert (Frame_OK (Log, W, Idx (J)));
         Lemma_Compacted_Entry (Log, LL, W, Idx (J));
         pragma Loop_Invariant
           (for all J2 in 1 .. J =>
              Frame_OK (Log, LL, Idx (J2))
              and then Entry_OK (Log, LL, Idx (J2).Off)
              and then Log (Idx (J2).Off) /= Op_Header
              and then Idx (J2).Off + Size_At (Log, Idx (J2).Off) = End_Of (Idx (J2)));
      end loop;
      for J in 1 .. N loop
         pragma Assert (Bnd (J + 1) = Idx (J).Off);
         pragma Assert (Entry_OK (Log, LL, Idx (J).Off));
         pragma Assert (Entry_OK (Log, LL, Bnd (J + 1)));
         pragma Assert (End_Of (Idx (J)) = (if J < N then Idx (J + 1).Off else W));
         pragma Assert
           (Bnd (J + 1) + Size_At (Log, Bnd (J + 1)) =
              (if J + 1 < NB then Bnd (J + 2) else LL));
         pragma Loop_Invariant
           (for all K in 2 .. J + 1 =>
              Entry_OK (Log, LL, Bnd (K))
              and then Log (Bnd (K)) /= Op_Header
              and then Bnd (K) + Size_At (Log, Bnd (K)) =
                         (if K < NB then Bnd (K + 1) else LL));
      end loop;
      pragma Assert
        (for all K in 2 .. N + 1 =>
           Entry_OK (Log, LL, Bnd (K))
           and then Log (Bnd (K)) /= Op_Header
           and then Bnd (K) + Size_At (Log, Bnd (K)) = (if K < NB then Bnd (K + 1) else LL));
      if Ex then
         pragma Assert (Entry_OK (Log, LL, Bnd (N + 2)));
         pragma Assert (Bnd (N + 2) + Size_At (Log, Bnd (N + 2)) = LL);
      end if;
      pragma Assert (NB <= LL / Min_Entry);
      pragma Assert
        (for all K in 1 .. NB =>
           Entry_OK (Log, LL, Bnd (K))
           and then (Log (Bnd (K)) = Op_Header) = (K = 1)
           and then Bnd (K) + Size_At (Log, Bnd (K)) = (if K < NB then Bnd (K + 1) else LL));
      pragma Assert (Chain (Log, LL, Bnd, NB));
      pragma Assert
        (for all J in 1 .. N => (for some K in 1 .. NB => Bnd (K) = Idx (J).Off));
   end Lemma_Chain_Compacted;

   --  The APPLYs of the copied entries are in place in the new log.
   procedure Lemma_Copied_Frames
     (New_Log : Byte_Array; W : Log_Size; Log : Byte_Array; LL : Log_Size;
      Old : Entry_Array; N : Held_Count; New_Idx : Entry_Array; Src : Index_Map)
   with
     Ghost, Global => null,
     Pre  => New_Log'First = 0 and then W <= New_Log'Last
       and then Log'First = 0 and then LL <= Log'Last
       and then Old'First = 1 and then N <= Old'Last
       and then New_Idx'First = 1 and then N <= New_Idx'Last
       and then Src'First = 1 and then N <= Src'Last
       and then Framed (Log, LL, Old, N)
       and then (for all J in 1 .. N =>
                   Src (J) in 1 .. N
                   and then New_Idx (J).H = Old (Src (J)).H
                   and then New_Idx (J).Len = Old (Src (J)).Len
                   and then New_Idx (J).Off >= Header_Len
                   and then End_Of (New_Idx (J)) <= W)
       and then (for all J in 1 .. N =>
                   Bytes_Eq (New_Log, New_Idx (J).Off,
                      Log, Old (Src (J)).Off,
                      Apply_Prefix + New_Idx (J).Len)),
     Post => Framed (New_Log, W, New_Idx, N);

   procedure Lemma_Copied_Frames
     (New_Log : Byte_Array; W : Log_Size; Log : Byte_Array; LL : Log_Size;
      Old : Entry_Array; N : Held_Count; New_Idx : Entry_Array; Src : Index_Map) is
   begin
      for J in 1 .. N loop
         pragma Assert (Frame_OK (Log, LL, Old (Src (J))));
         Lemma_Bytes_Unfold (New_Log, New_Idx (J).Off, Log, Old (Src (J)).Off,
                             Apply_Prefix + New_Idx (J).Len);
         pragma Assert (New_Log (New_Idx (J).Off) = Log (Old (Src (J)).Off));
         pragma Assert (New_Log (New_Idx (J).Off + 1) = Log (Old (Src (J)).Off + 1));
         pragma Assert (New_Log (New_Idx (J).Off + 2) = Log (Old (Src (J)).Off + 2));
         pragma Assert (New_Log (New_Idx (J).Off + 3) = Log (Old (Src (J)).Off + 3));
         pragma Assert (New_Log (New_Idx (J).Off + 4) = Log (Old (Src (J)).Off + 4));
         pragma Assert (New_Log (New_Idx (J).Off + 5) = Log (Old (Src (J)).Off + 5));
         pragma Assert
           (Len_Word (New_Log, New_Idx (J).Off) = Len_Word (Log, Old (Src (J)).Off));
         pragma Assert (Frame_OK (New_Log, W, New_Idx (J)));
         pragma Loop_Invariant (for all J2 in 1 .. J => Frame_OK (New_Log, W, New_Idx (J2)));
      end loop;
   end Lemma_Copied_Frames;

   --  Entries with no gaps between them are in increasing order of
   --  offset.
   procedure Lemma_Contiguous (Idx : Entry_Array; N : Held_Count) with
     Ghost, Global => null,
     Pre  => Idx'First = 1 and then N <= Idx'Last
       and then (for all J in 1 .. N - 1 => Idx (J + 1).Off = End_Of (Idx (J))),
     Post => (for all J in 1 .. N =>
                (for all J2 in J + 1 .. N => End_Of (Idx (J)) <= Idx (J2).Off));

   procedure Lemma_Contiguous (Idx : Entry_Array; N : Held_Count) is
   begin
      for J2 in 2 .. N loop
         pragma Assert (Idx (J2).Off = End_Of (Idx (J2 - 1)));
         pragma Loop_Invariant
           (for all J3 in 2 .. J2 =>
              (for all J in 1 .. J3 - 1 => End_Of (Idx (J)) <= Idx (J3).Off));
      end loop;
   end Lemma_Contiguous;

   --  Entries with no gaps and with distinct sources are sorted.
   procedure Lemma_Copied_Sorted
     (Old : Entry_Array; N : Held_Count; New_Idx : Entry_Array; Src : Index_Map;
      KA  : Held_Count)
   with
     Ghost, Global => null,
     Pre  => Old'First = 1 and then N <= Old'Last
       and then New_Idx'First = 1 and then N <= New_Idx'Last
       and then Src'First = 1 and then N <= Src'Last
       and then KA <= N
       and then Sorted (Old, N)
       and then (for all J in 1 .. N =>
                   Src (J) in 1 .. N and then New_Idx (J).H = Old (Src (J)).H)
       and then (for all J in 1 .. N => Is_Data (New_Idx (J).H) = (J > KA))
       and then (for all J in 1 .. N =>
                   (for all J2 in J + 1 .. N =>
                      (if (J2 <= KA or else J > KA) then Src (J) < Src (J2))))
       and then (for all J in 1 .. N - 1 => New_Idx (J + 1).Off = End_Of (New_Idx (J))),
     Post => Sorted (New_Idx, N);

   procedure Lemma_Copied_Sorted
     (Old : Entry_Array; N : Held_Count; New_Idx : Entry_Array; Src : Index_Map;
      KA  : Held_Count) is
   begin
      Lemma_Contiguous (New_Idx, N);
      for J in 1 .. N loop
         for J2 in J + 1 .. N loop
            if J2 <= KA or else J > KA then
               pragma Assert (Src (J) /= Src (J2));
               Lemma_Sorted_Distinct (Old, N, Src (J), Src (J2));
            else
               pragma Assert (Is_Data (New_Idx (J).H) /= Is_Data (New_Idx (J2).H));
            end if;
            pragma Assert (New_Idx (J).H /= New_Idx (J2).H);
            pragma Assert (End_Of (New_Idx (J)) <= New_Idx (J2).Off);
            pragma Loop_Invariant
              (for all J3 in J + 1 .. J2 =>
                 End_Of (New_Idx (J)) <= New_Idx (J3).Off
                 and then New_Idx (J).H /= New_Idx (J3).H);
         end loop;
         pragma Loop_Invariant
           (for all J1 in 1 .. J =>
              (for all J3 in J1 + 1 .. N =>
                 End_Of (New_Idx (J1)) <= New_Idx (J3).Off
                 and then New_Idx (J1).H /= New_Idx (J3).H));
      end loop;
   end Lemma_Copied_Sorted;

   --  The new index has the records of the old index: it is still live
   --  and covering.
   procedure Lemma_Copied_Records
     (F : Frontier.State; Old : Entry_Array; N : Held_Count; New_Idx : Entry_Array;
      Src, Dst : Index_Map)
   with
     Ghost, Global => null,
     Pre  => Old'First = 1 and then N <= Old'Last
       and then New_Idx'First = 1 and then N <= New_Idx'Last
       and then Src'First = 1 and then N <= Src'Last
       and then Dst'First = 1 and then N <= Dst'Last
       and then Live (F, Old, N)
       and then Covered (F, Old, N)
       and then (for all J in 1 .. N =>
                   Src (J) in 1 .. N and then New_Idx (J).H = Old (Src (J)).H)
       and then (for all J in 1 .. N => Dst (J) in 1 .. N and then Src (Dst (J)) = J),
     Post => Live (F, New_Idx, N) and then Covered (F, New_Idx, N)
       and then (for all J in 1 .. N => Has_Entry (New_Idx, N, Old (J).H));

   procedure Lemma_Copied_Records
     (F : Frontier.State; Old : Entry_Array; N : Held_Count; New_Idx : Entry_Array;
      Src, Dst : Index_Map) is
   begin
      for J in 1 .. N loop
         pragma Assert (Holds (F, Old (Src (J)).H));
         pragma Loop_Invariant (for all J2 in 1 .. J => Holds (F, New_Idx (J2).H));
      end loop;
      for J in 1 .. N loop
         pragma Assert (New_Idx (Dst (J)).H = Old (J).H);
         pragma Loop_Invariant (for all J2 in 1 .. J => Has_Entry (New_Idx, N, Old (J2).H));
      end loop;
      for K in 1 .. Count (F) loop
         declare
            I : constant Held_Index := Entry_Witness (Old, N, Held (F, K));
         begin
            pragma Assert (Has_Entry (New_Idx, N, Old (I).H));
         end;
         pragma Loop_Invariant
           (for all K2 in 1 .. K => Has_Entry (New_Idx, N, Held (F, K2)));
      end loop;
   end Lemma_Copied_Records;

   --  The chain of a compacted log: 0, the offsets of the entries, then W
   --  if Ex.
   procedure Set_Chain
     (Bnd : in out Offset_Array; Idx : Entry_Array; N : Held_Count; Ex : Boolean;
      W   : Log_Size)
   with
     Global => null,
     Pre  => Bnd'First = 1 and then N + 2 <= Bnd'Last
             and then Idx'First = 1 and then N <= Idx'Last,
     Post => Bnd (1) = 0
             and then (for all J in 1 .. N => Bnd (J + 1) = Idx (J).Off)
             and then (if Ex then Bnd (N + 2) = W);

   procedure Set_Chain
     (Bnd : in out Offset_Array; Idx : Entry_Array; N : Held_Count; Ex : Boolean;
      W   : Log_Size) is
   begin
      Bnd (1) := 0;
      for J in 1 .. N loop
         Bnd (J + 1) := Idx (J).Off;
         pragma Loop_Invariant (Bnd (1) = 0);
         pragma Loop_Invariant (for all J2 in 1 .. J => Bnd (J2 + 1) = Idx (J2).Off);
      end loop;
      if Ex then
         Bnd (N + 2) := W;
      end if;
   end Set_Chain;

   --  One element of a copied range (a small context for the instance).
   procedure Lemma_Range_At
     (A : Byte_Array; PA : Natural; B : Byte_Array; PB : Natural; Len, K : Natural)
   with
     Ghost, Global => null,
     Pre  => A'First = 0 and then B'First = 0
       and then A'Last <= Log_Max and then B'Last <= Log_Max
       and then K < Len
       and then PA <= A'Last and then Len - 1 <= A'Last - PA
       and then PB <= B'Last and then Len - 1 <= B'Last - PB
       and then (for all M in 0 .. Len - 1 => A (PA + M) = B (PB + M)),
     Post => A (PA + K) = B (PB + K);

   procedure Lemma_Range_At
     (A : Byte_Array; PA : Natural; B : Byte_Array; PB : Natural; Len, K : Natural) is null;

   --  One copied range, from the log arrays to the stores.
   procedure Lemma_Same_From
     (S, Old_S : Store; New_Log, Old_Log : Byte_Array; PA, PB, Len : Natural)
   with
     Ghost, Global => null,
     Pre  => S.LL <= S.Log_Cap and then Old_S.LL <= Old_S.Log_Cap
       and then PA <= S.LL and then Len <= S.LL - PA
       and then PB <= Old_S.LL and then Len <= Old_S.LL - PB
       and then New_Log'First = 0 and then New_Log'Last = S.Log_Cap
       and then (for all Q in 0 .. S.Log_Cap => S.Log (Q) = New_Log (Q))
       and then Old_Log'First = 0 and then Old_Log'Last = Old_S.Log_Cap
       and then (for all Q in 0 .. Old_S.Log_Cap => Old_S.Log (Q) = Old_Log (Q))
       and then (for all M in 0 .. Len - 1 => New_Log (PA + M) = Old_Log (PB + M)),
     Post => PA <= Log_Length (S) and then Len <= Log_Length (S) - PA
       and then PB <= Log_Length (Old_S) and then Len <= Log_Length (Old_S) - PB
       and then Same_Bytes (S, PA, Old_S, PB, Len);

   procedure Lemma_Same_From
     (S, Old_S : Store; New_Log, Old_Log : Byte_Array; PA, PB, Len : Natural) is
   begin
      pragma Assert (Log_Length (S) = S.LL and then Log_Length (Old_S) = Old_S.LL);
      for K in 0 .. Len - 1 loop
         Lemma_Range_At (New_Log, PA, Old_Log, PB, Len, K);
         pragma Assert (New_Log (PA + K) = Old_Log (PB + K));
         pragma Assert (S.Log (PA + K) = New_Log (PA + K));
         pragma Assert (Old_S.Log (PB + K) = Old_Log (PB + K));
         pragma Assert (Log_Byte (S, PA + K) = Log_Byte (Old_S, PB + K));
         pragma Loop_Invariant
           (for all K2 in 0 .. K => Log_Byte (S, PA + K2) = Log_Byte (Old_S, PB + K2));
      end loop;
      pragma Assert
        (for all K in 0 .. Len - 1 => Log_Byte (S, PA + K) = Log_Byte (Old_S, PB + K));
   end Lemma_Same_From;

   --  The byte-for-byte clause of Compact, from the copies (no
   --  frontier).
   procedure Lemma_Compact_Bytes
     (Old_S, S : Store; New_Log, Old_Log : Byte_Array; Old_Idx : Entry_Array;
      Src : Index_Map)
   with
     Ghost, Global => null,
     Pre  => S.NI <= S.Cap and then S.LL <= S.Log_Cap
       and then Old_S.NI <= Old_S.Cap and then Old_S.LL <= Old_S.Log_Cap
       and then S.NI = Old_S.NI
       and then New_Log'First = 0 and then New_Log'Last = S.Log_Cap
       and then (for all Q in 0 .. S.Log_Cap => S.Log (Q) = New_Log (Q))
       and then Old_Log'First = 0 and then Old_Log'Last = Old_S.Log_Cap
       and then (for all Q in 0 .. Old_S.Log_Cap => Old_S.Log (Q) = Old_Log (Q))
       and then Old_Idx'First = 1 and then Old_Idx'Last = Old_S.Cap
       and then (for all I in 1 .. Old_S.Cap => Old_S.Idx (I) = Old_Idx (I))
       and then Src'First = 1 and then Src'Last = S.NI
       and then (for all J in 1 .. S.NI =>
                   Src (J) in 1 .. S.NI
                   and then S.Idx (J).Len = Old_Idx (Src (J)).Len
                   and then End_Of (S.Idx (J)) <= S.LL
                   and then End_Of (Old_Idx (Src (J))) <= Old_S.LL
                   and then Bytes_Eq (New_Log, S.Idx (J).Off,
                                      Old_Log, Old_Idx (Src (J)).Off,
                                      Apply_Prefix + S.Idx (J).Len)),
     Post => (for all J in 1 .. S.NI =>
                End_Of (Entry_At (S, J)) <= Log_Length (S)
                and then End_Of (Entry_At (Old_S, Src (J))) <= Log_Length (Old_S)
                and then Same_Bytes (S, Entry_At (S, J).Off,
                                     Old_S, Entry_At (Old_S, Src (J)).Off,
                                     Apply_Prefix + Entry_At (S, J).Len));

   procedure Lemma_Compact_Bytes
     (Old_S, S : Store; New_Log, Old_Log : Byte_Array; Old_Idx : Entry_Array;
      Src : Index_Map) is
   begin
      pragma Assert (Log_Length (S) = S.LL and then Log_Length (Old_S) = Old_S.LL);
      pragma Assert (Entries (S) = S.NI and then Entries (Old_S) = Old_S.NI);
      for J in 1 .. S.NI loop
         pragma Assert (Old_S.Idx (Src (J)) = Old_Idx (Src (J)));
         pragma Assert (Entry_At (S, J) = S.Idx (J));
         pragma Assert (Entry_At (Old_S, Src (J)) = Old_Idx (Src (J)));
         Lemma_Bytes_Unfold (New_Log, S.Idx (J).Off, Old_Log, Old_Idx (Src (J)).Off,
                             Apply_Prefix + S.Idx (J).Len);
         Lemma_Same_From (S, Old_S, New_Log, Old_Log, S.Idx (J).Off, Old_Idx (Src (J)).Off,
                          Apply_Prefix + S.Idx (J).Len);
         pragma Assert
           (Same_Bytes (S, Entry_At (S, J).Off, Old_S, Entry_At (Old_S, Src (J)).Off,
                        Apply_Prefix + Entry_At (S, J).Len));
         pragma Loop_Invariant
           (for all J2 in 1 .. J =>
              End_Of (Entry_At (S, J2)) <= Log_Length (S)
              and then End_Of (Entry_At (Old_S, Src (J2))) <= Log_Length (Old_S)
              and then Same_Bytes (S, Entry_At (S, J2).Off,
                                   Old_S, Entry_At (Old_S, Src (J2)).Off,
                                   Apply_Prefix + Entry_At (S, J2).Len));
      end loop;
   end Lemma_Compact_Bytes;

   --  The tail of a compacted log: EXPIRE (horizon) at W, if there is a
   --  horizon and it fits. The bytes below W do not change.
   procedure Write_Tail
     (Log     : in out Byte_Array;
      LL      : out Log_Size;
      Ex      : out Boolean;
      W       : Log_Size;
      Hz      : Horizon_Value;
      Idx     : Entry_Array;
      N       : Held_Count;
      Old_Log : Byte_Array;
      Old_Idx : Entry_Array;
      Src     : Index_Map)
   with
     Global => null,
     Pre  => Log'First = 0 and then Log'Last <= Log_Max
       and then Header_Len <= W and then W <= Log'Last
       and then Old_Log'First = 0 and then Old_Log'Last <= Log_Max
       and then Idx'First = 1 and then N <= Idx'Last
       and then Old_Idx'First = 1 and then N <= Old_Idx'Last
       and then Src'First = 1 and then Src'Last = N
       and then Framed (Log, W, Idx, N)
       and then (for all J in 1 .. N =>
                   Src (J) in 1 .. N
                   and then End_Of (Idx (J)) <= W
                   and then Bytes_Eq (Log, Idx (J).Off, Old_Log, Old_Idx (Src (J)).Off,
                                      Apply_Prefix + Idx (J).Len)),
     Post => Ex = (Hz >= 0 and then Log'Last - W >= Expire_Len)
       and then LL = (if Ex then W + Expire_Len else W)
       and then LL <= Log'Last
       and then (for all Q in 0 .. W - 1 => Log (Q) = Log'Old (Q))
       and then (if Ex then
                   Log (W) = Op_Expire
                   and then Kome.Records.U48_Of (Log (W + 1), Log (W + 2), Log (W + 3),
                                                 Log (W + 4), Log (W + 5), Log (W + 6))
                            = Horizon_Code (Hz))
       and then Framed (Log, W, Idx, N)
       and then (for all J in 1 .. N =>
                   Bytes_Eq (Log, Idx (J).Off, Old_Log, Old_Idx (Src (J)).Off,
                             Apply_Prefix + Idx (J).Len));

   procedure Write_Tail
     (Log     : in out Byte_Array;
      LL      : out Log_Size;
      Ex      : out Boolean;
      W       : Log_Size;
      Hz      : Horizon_Value;
      Idx     : Entry_Array;
      N       : Held_Count;
      Old_Log : Byte_Array;
      Old_Idx : Entry_Array;
      Src     : Index_Map)
   is
      Pre_Log : constant Byte_Array := Log with Ghost;
      Code    : constant U48 := Horizon_Code (Hz);
   begin
      Ex := Hz >= 0 and then Log'Last - W >= Expire_Len;
      if Ex then
         Kome.Records.Lemma_U48_Round_Trip (Code);
         Log (W)     := Op_Expire;
         Log (W + 1) := Kome.Records.Byte_Of_U48 (Code, 0);
         Log (W + 2) := Kome.Records.Byte_Of_U48 (Code, 1);
         Log (W + 3) := Kome.Records.Byte_Of_U48 (Code, 2);
         Log (W + 4) := Kome.Records.Byte_Of_U48 (Code, 3);
         Log (W + 5) := Kome.Records.Byte_Of_U48 (Code, 4);
         Log (W + 6) := Kome.Records.Byte_Of_U48 (Code, 5);
         LL := W + Expire_Len;
      else
         LL := W;
      end if;
      pragma Assert (for all Q in 0 .. W - 1 => Log (Q) = Pre_Log (Q));
      Lemma_Framed_Grow (Pre_Log, W, Log, W, Idx, N);
      for J in 1 .. N loop
         Lemma_Bytes_Kept (Pre_Log, Log, W, Old_Log, Idx (J).Off,
                           Old_Idx (Src (J)).Off, Apply_Prefix + Idx (J).Len);
         pragma Loop_Invariant
           (for all J2 in 1 .. J =>
              Bytes_Eq (Log, Idx (J2).Off, Old_Log, Old_Idx (Src (J2)).Off,
                        Apply_Prefix + Idx (J2).Len));
      end loop;
   end Write_Tail;

   --  The index clause of Compact (Compact_Index), from the explicit
   --  copies: Src (J) is the old position of new entry J, and the two
   --  parts are the authorization records (J <= CA) and the data records.
   --  (AUDIT.md G17: one small lemma for each clause of the Post.)
   procedure Lemma_Compact_Index
     (Old_S, S : Store; F : Frontier.State; Src : Index_Map; CA : Natural)
   with
     Ghost, Global => null,
     Pre  => Valid (Old_S, F)
       and then Entries (S) = Entries (Old_S)
       and then Src'First = 1 and then Src'Last = Entries (S)
       and then CA <= Entries (S)
       and then (for all J in 1 .. Entries (S) =>
                   Src (J) in 1 .. Entries (S)
                   and then Entry_At (S, J).H = Entry_At (Old_S, Src (J)).H
                   and then Entry_At (S, J).Len = Entry_At (Old_S, Src (J)).Len
                   and then Is_Data (Entry_At (S, J).H) = (J > CA))
       and then (for all J in 1 .. Entries (S) =>
                   End_Of (Entry_At (S, J)) <= Log_Length (S)
                   and then End_Of (Entry_At (Old_S, Src (J))) <= Log_Length (Old_S)
                   and then Same_Bytes (S, Entry_At (S, J).Off,
                                        Old_S, Entry_At (Old_S, Src (J)).Off,
                                        Apply_Prefix + Entry_At (S, J).Len))
       and then (for all J in 1 .. Entries (Old_S) => Indexed (S, Entry_At (Old_S, J).H)),
     Post => Compact_Index (Old_S, S);

   procedure Lemma_Compact_Index
     (Old_S, S : Store; F : Frontier.State; Src : Index_Map; CA : Natural)
   is
      N : constant Held_Count := Entries (S);
   begin
      pragma Assert (for all J in 1 .. N => Is_Data (Entry_At (S, J).H) = (J > CA));
      for J in 1 .. N loop
         Lemma_Position (Old_S, F, Src (J));
         pragma Assert (Position (Old_S, Entry_At (S, J).H) = Src (J));
         pragma Assert
           (Entry_At (Old_S, Position (Old_S, Entry_At (S, J).H)) = Entry_At (Old_S, Src (J)));
         pragma Assert
           (Same_Bytes (S, Entry_At (S, J).Off,
                        Old_S, Entry_At (Old_S, Src (J)).Off,
                        Apply_Prefix + Entry_At (S, J).Len));
         pragma Assert
           (Indexed (Old_S, Entry_At (S, J).H)
            and then Entry_At (Old_S, Position (Old_S, Entry_At (S, J).H)).Len
                     = Entry_At (S, J).Len
            and then End_Of (Entry_At (S, J)) <= Log_Length (S)
            and then End_Of (Entry_At (Old_S, Position (Old_S, Entry_At (S, J).H)))
                     <= Log_Length (Old_S)
            and then Same_Bytes (S, Entry_At (S, J).Off,
                                 Old_S, Entry_At (Old_S, Position (Old_S, Entry_At (S, J).H)).Off,
                                 Apply_Prefix + Entry_At (S, J).Len));
         pragma Loop_Invariant
           (for all J2 in 1 .. J =>
              Indexed (Old_S, Entry_At (S, J2).H)
              and then Position (Old_S, Entry_At (S, J2).H) = Src (J2));
         pragma Loop_Invariant
           (for all J2 in 1 .. J =>
              Indexed (Old_S, Entry_At (S, J2).H)
              and then Entry_At (Old_S, Position (Old_S, Entry_At (S, J2).H)).Len
                       = Entry_At (S, J2).Len
              and then End_Of (Entry_At (S, J2)) <= Log_Length (S)
              and then End_Of (Entry_At (Old_S, Position (Old_S, Entry_At (S, J2).H)))
                       <= Log_Length (Old_S)
              and then Same_Bytes (S, Entry_At (S, J2).Off,
                                   Old_S, Entry_At (Old_S, Position (Old_S, Entry_At (S, J2).H)).Off,
                                   Apply_Prefix + Entry_At (S, J2).Len));
      end loop;
      pragma Assert
        (for all I in 1 .. N =>
           Indexed (Old_S, Entry_At (S, I).H)
           and then Entry_At (Old_S, Position (Old_S, Entry_At (S, I).H)).Len
                    = Entry_At (S, I).Len
           and then End_Of (Entry_At (S, I)) <= Log_Length (S)
           and then End_Of (Entry_At (Old_S, Position (Old_S, Entry_At (S, I).H)))
                    <= Log_Length (Old_S)
           and then Same_Bytes (S, Entry_At (S, I).Off,
                                Old_S, Entry_At (Old_S, Position (Old_S, Entry_At (S, I).H)).Off,
                                Apply_Prefix + Entry_At (S, I).Len));
      pragma Assert
        (for all I in 1 .. N =>
           (for all J in I + 1 .. N =>
              (if Is_Data (Entry_At (S, I).H) then Is_Data (Entry_At (S, J).H))));
      pragma Assert (for all J in 1 .. Entries (Old_S) => Indexed (S, Entry_At (Old_S, J).H));
      pragma Assert (Compact_Index (Old_S, S));
   end Lemma_Compact_Index;

   --  The layout clause of Compact (Compact_Layout), from the explicit
   --  fields of the compacted store: N entries from Header_Len to W with
   --  no gaps, the chain 0, their offsets, then W iff Ex, and EXPIRE at
   --  W iff Ex.
   procedure Lemma_Compact_Layout
     (Old_S, S : Store; N : Held_Count; W : Log_Size; Ex : Boolean)
   with
     Ghost, Global => null,
     Pre  => S.NI = N and then N <= S.Cap
       and then S.LL <= S.Log_Cap and then S.NB <= S.Log_Cap and then S.NB <= S.Bnd_Cap
       and then Old_S.Log_Cap = S.Log_Cap
       and then Old_S.LL <= Old_S.Log_Cap
       and then Old_S.LL >= Header_Len
       and then W >= Header_Len and then W <= Old_S.LL
       and then Ex = (S.Hz >= 0 and then S.Log_Cap - W >= Expire_Len)
       and then S.LL = (if Ex then W + Expire_Len else W)
       and then S.NB = (if Ex then N + 2 else N + 1)
       and then (for all Q in 0 .. Header_Len - 1 => S.Log (Q) = Old_S.Log (Q))
       and then (if N > 0 then S.Idx (1).Off = Header_Len and then W = End_Of (S.Idx (N))
                 else W = Header_Len)
       and then (for all J in 1 .. N - 1 => S.Idx (J + 1).Off = End_Of (S.Idx (J)))
       and then S.Bnd (1) = 0
       and then (for all J in 1 .. N => S.Bnd (J + 1) = S.Idx (J).Off)
       and then (if Ex then
                   S.Log (W) = Op_Expire
                   and then Kome.Records.U48_Of (S.Log (W + 1), S.Log (W + 2), S.Log (W + 3),
                                                 S.Log (W + 4), S.Log (W + 5), S.Log (W + 6))
                            = Horizon_Code (S.Hz)),
     Post => Compact_Layout (Old_S, S);

   procedure Lemma_Compact_Layout
     (Old_S, S : Store; N : Held_Count; W : Log_Size; Ex : Boolean)
   is
   begin
      pragma Assert (Log_Length (S) = S.LL);
      pragma Assert (Log_Length (Old_S) = Old_S.LL);
      pragma Assert (Entries (S) = N);
      pragma Assert (Log_Entries (S) = S.NB);
      pragma Assert (Body_End (S) = W);
      pragma Assert (Body_End (S) <= Log_Length (Old_S));
      pragma Assert (for all K in 0 .. Header_Len - 1 => Log_Byte (S, K) = Log_Byte (Old_S, K));
      pragma Assert (if Entries (S) > 0 then Entry_At (S, 1).Off = Header_Len);
      pragma Assert
        (for all I in 1 .. Entries (S) - 1 => Entry_At (S, I + 1).Off = End_Of (Entry_At (S, I)));
      pragma Assert
        (for all I in 1 .. Entries (S) =>
           I + 1 <= Log_Entries (S) and then Entry_Start (S, I + 1) = Entry_At (S, I).Off);
      if Ex then
         pragma Assert (Op_At (S, W) = Op_Expire);
         pragma Assert (Code_At (S, W + 1) = Horizon_Code (S.Hz));
         pragma Assert (Log_Length (S) - Body_End (S) = Expire_Len);
         pragma Assert (Log_Entries (S) = Entries (S) + 2);
      else
         pragma Assert (Log_Length (S) = Body_End (S));
         pragma Assert (Log_Entries (S) = Entries (S) + 1);
         pragma Assert (if Horizon (S) >= 0 then S.Log_Cap - W < Expire_Len);
         pragma Assert (if Horizon (S) >= 0 then Log_Length (Old_S) - Body_End (S) < Expire_Len);
      end if;
      pragma Assert (Compact_Layout (Old_S, S));
   end Lemma_Compact_Layout;

   procedure Compact (S : in out Store; F : Frontier.State; Buf : in out Byte_Array) is
      Old_S   : constant Store := S with Ghost;
      N       : constant Held_Count := S.NI;
      Old_LL  : constant Log_Size := S.LL;
      --  The old file. Only the proof names it: the code reads S.Log,
      --  which does not change until the new log replaces it (AUDIT.md
      --  G15: no copy of the log).
      Old_Log : constant Byte_Array := S.Log with Ghost;
      Old_Idx : constant Entry_Array := S.Idx;
      P       : constant Prefix := Prefix_Of (Old_Idx, N, Old_LL);
      Src     : Index_Map (1 .. N) := [others => 0];
      Dst     : Index_Map (1 .. N) := [others => 0];
      W       : Log_Size := Header_Len;
      K       : Held_Count := 0;
      Ex      : Boolean;
      New_LL  : Log_Size;
   begin
      pragma Assert (Valid (Old_S, F));
      pragma Assert (Entries (Old_S) = N);
      pragma Assert (Horizon (Old_S) = S.Hz);
      pragma Assert (Log_Length (Old_S) = Old_LL);
      pragma Assert (for all I in 1 .. N => Frame_OK (Old_Log, Old_LL, Old_Idx (I)));
      pragma Assert (for all I in 1 .. N => End_Of (Old_Idx (I)) <= Old_LL);
      --  The HEADER (the same bytes), into the binding's buffer.
      Buf (0 .. Header_Len - 1) := S.Log (0 .. Header_Len - 1);
      pragma Assert (for all Q in 0 .. Header_Len - 1 => Buf (Q) = Old_Log (Q));
      pragma Assert (Copied (Old_Log, Old_Idx, N, P.CA (N), Buf, W, S.Idx, K, Src));
      --  Pass 1 copies the authorization records, in index order. Pass 2
      --  copies the data records, in index order. Both passes read S.Log
      --  and write Buf from Header_Len.
      Copy_Part (S.Log, Old_LL, Old_Idx, N, P, False, Buf, W, S.Idx, K, Src, Dst);
      pragma Assert (S.Log = Old_Log);
      Copy_Part (S.Log, Old_LL, Old_Idx, N, P, True, Buf, W, S.Idx, K, Src, Dst);
      pragma Assert (S.Log = Old_Log);
      pragma Assert (K = N);
      pragma Assert (W = Header_Len + P.SA (N) + P.SD (N));
      pragma Assert (W <= Old_LL);
      pragma Assert (W >= Header_Len + Min_Entry * N);
      Lemma_Copied_Unfold (Old_Log, Old_Idx, N, P.CA (N), Buf, W, S.Idx, N, Src);
      pragma Assert (for all J in 1 .. N => Is_Data (S.Idx (J).H) = (J > P.CA (N)));
      pragma Assert (for all J in 1 .. N => Dst (J) in 1 .. N and then Src (Dst (J)) = J);
      Lemma_Copied_Frames (Buf, W, Old_Log, Old_LL, Old_Idx, N, S.Idx, Src);
      Lemma_Copied_Sorted (Old_Idx, N, S.Idx, Src, P.CA (N));
      Lemma_Copied_Records (F, Old_Idx, N, S.Idx, Src, Dst);

      --  EXPIRE (horizon), if there is one and it fits.
      Write_Tail (Buf, New_LL, Ex, W, S.Hz, S.Idx, N, S.Log, Old_Idx, Src);
      pragma Assert (Ex = (S.Hz >= 0 and then S.Log_Cap - W >= Expire_Len));
      pragma Assert (for all Q in 0 .. Header_Len - 1 => Buf (Q) = Old_Log (Q));

      --  The new log replaces the old one.
      S.Log := Buf;
      S.LL := New_LL;
      pragma Assert (for all Q in 0 .. S.Log_Cap => S.Log (Q) = Buf (Q));
      pragma Assert (Framed (S.Log, W, S.Idx, N));
      pragma Assert
        (for all J in 1 .. N =>
           Bytes_Eq (S.Log, S.Idx (J).Off, Old_Log, Old_Idx (Src (J)).Off,
                     Apply_Prefix + S.Idx (J).Len));
      pragma Assert (for all Q in 0 .. Header_Len - 1 => S.Log (Q) = Old_Log (Q));

      --  The chain of the new log (AUDIT.md G15: N + 2 entries of at
      --  least Min_Entry bytes fit Log_Cap, so they fit Bnd).
      pragma Assert (N + 2 <= S.Log_Cap);
      pragma Assert (Header_Len + Min_Entry * N <= S.Log_Cap);
      pragma Assert ((Header_Len + Min_Entry * N) / Min_Entry = Header_Len / Min_Entry + N);
      pragma Assert (N + 2 <= S.Log_Cap / Min_Entry);
      pragma Assert (N + 2 <= S.Bnd_Cap);
      Set_Chain (S.Bnd, S.Idx, N, Ex, W);
      S.NB := (if Ex then N + 2 else N + 1);
      pragma Assert (S.Log (0) = Op_Header);
      pragma Assert (if N > 0 then S.Idx (1).Off = Header_Len and then W = End_Of (S.Idx (N))
                     else W = Header_Len);
      pragma Assert (for all J in 1 .. N - 1 => S.Idx (J + 1).Off = End_Of (S.Idx (J)));
      Lemma_Chain_Compacted (S.Log, S.LL, W, S.Idx, N, S.Bnd, S.NB, Ex);
      Lemma_Head_Grow (Old_Log, Old_LL, S.Log, S.LL, S.NSb, S.Root, S.Slt, S.DCap, S.Slc);
      pragma Assert (Valid (S, F));

      --  The contract, over the saved store.
      declare
         Fin_Log : constant Byte_Array := S.Log with Ghost;
      begin
         pragma Assert (for all Q in 0 .. S.Log_Cap => S.Log (Q) = Fin_Log (Q));
         pragma Assert
           (for all J in 1 .. N =>
              Bytes_Eq (Fin_Log, S.Idx (J).Off, Old_Log, Old_Idx (Src (J)).Off,
                        Apply_Prefix + S.Idx (J).Len));
         pragma Assert (Body_End (S) = W);
         pragma Assert (Entries (S) = Entries (Old_S));
         pragma Assert (Old_S.LL = Old_LL);
         pragma Assert (for all Q in 0 .. Old_S.Log_Cap => Old_S.Log (Q) = Old_Log (Q));
         pragma Assert (for all I in 1 .. Old_S.Cap => Old_S.Idx (I) = Old_Idx (I));
         pragma Assert
           (for all J in 1 .. N =>
              Src (J) in 1 .. N
              and then S.Idx (J).Len = Old_Idx (Src (J)).Len
              and then End_Of (S.Idx (J)) <= S.LL
              and then End_Of (Old_Idx (Src (J))) <= Old_S.LL
              and then Bytes_Eq (Fin_Log, S.Idx (J).Off,
                                 Old_Log, Old_Idx (Src (J)).Off,
                                 Apply_Prefix + S.Idx (J).Len));
         Lemma_Compact_Bytes (Old_S, S, Fin_Log, Old_Log, Old_Idx, Src);
      end;
      pragma Assert
        (for all J in 1 .. N =>
           Src (J) in 1 .. N
           and then Entry_At (S, J).H = Entry_At (Old_S, Src (J)).H
           and then Entry_At (S, J).Len = Entry_At (Old_S, Src (J)).Len
           and then Is_Data (Entry_At (S, J).H) = (J > P.CA (N)));
      pragma Assert (Entries (S) = Entries (Old_S));
      pragma Assert (Valid (Old_S, F));
      --  Each old record is a new entry (the copy was onto).
      pragma Assert (for all J in 1 .. N => Has_Entry (S.Idx, N, Old_Idx (J).H));
      pragma Assert (for all J in 1 .. N => Indexed (S, Entry_At (Old_S, J).H));
      Lemma_Compact_Index (Old_S, S, F, Src, P.CA (N));
      --  The layout, from the fields set above.
      pragma Assert (Old_S.LL >= Header_Len);
      pragma Assert (for all Q in 0 .. Header_Len - 1 => S.Log (Q) = Old_S.Log (Q));
      pragma Assert (S.LL = (if Ex then W + Expire_Len else W));
      pragma Assert (S.NB = (if Ex then N + 2 else N + 1));
      Lemma_Compact_Layout (Old_S, S, N, W, Ex);
      --  The simple conjuncts of the Post, one at a time (prover time).
      pragma Assert (Same_Identity (Old_S, S));
      pragma Assert (Horizon (S) = Horizon (Old_S));
      pragma Assert (Auth_Gen (S) = Auth_Gen (Old_S) and then Expire_Mark (S) = Expire_Mark (Old_S));
      pragma Assert (Log_Entries (S) <= Entries (S) + 2);
      pragma Assert (not Compact_Due (S));
      --  Valid, stated again at the end, part by part (prover time: the
      --  Valid conjunct of the Post then closes from these atoms).
      pragma Assert (Framed (S.Log, S.LL, S.Idx, S.NI));
      pragma Assert (Chain (S.Log, S.LL, S.Bnd, S.NB));
      pragma Assert (At_Bounds (S.Idx, S.NI, S.Bnd, S.NB));
      pragma Assert (Sorted (S.Idx, S.NI));
      pragma Assert (Head_OK (S.Log, S.LL, S.NSb, S.Root, S.Slt, S.DCap, S.Slc));
      pragma Assert (Live (F, S.Idx, S.NI) and then Covered (F, S.Idx, S.NI)
                     and then Fresh (F, S.Hz));
      pragma Assert (Valid (S, F));
      --  The new file image is the binding's buffer.
      pragma Assert (Log_Length (S) = S.LL);
      pragma Assert (for all J in 0 .. Log_Length (S) - 1 => Buf (J) = Log_Byte (S, J));
   end Compact;

   ---------------------------------------------------------------------------
   --  Replay.
   ---------------------------------------------------------------------------

   --  Decode_Verified for the frame's kind: OK iff the frame is a
   --  well-formed record.
   procedure Decode_Frame (Cid : Hash256; Frame : Byte_Array; Accepted : out Boolean) with
     Global => null,
     Post => Accepted = Verified (Cid, Frame);

   procedure Decode_Frame (Cid : Hash256; Frame : Byte_Array; Accepted : out Boolean) is
      St : Status;
   begin
      if not Kome.Records.Has_Kind (Frame) then
         Accepted := False;
         return;
      end if;
      case Kome.Records.Kind_Of (Frame) is
         when K_Put =>
            declare
               R : Kome.Records.Put_Record;
            begin
               Kome.Records.Decode_Verified (Cid, Frame, R, St);
            end;
         when K_Del =>
            declare
               R : Kome.Records.Del_Record;
            begin
               Kome.Records.Decode_Verified (Cid, Frame, R, St);
            end;
         when K_Roster =>
            declare
               R : Kome.Records.Roster_Record;
            begin
               Kome.Records.Decode_Verified (Frame, R, St);
            end;
         when K_Revoke =>
            declare
               R : Kome.Records.Revoke_Record;
            begin
               Kome.Records.Decode_Verified (Frame, R, St);
            end;
         when K_Grant =>
            declare
               R : Kome.Records.Grant_Record;
            begin
               Kome.Records.Decode_Verified (Frame, R, St);
            end;
      end case;
      Accepted := St = OK;
   end Decode_Frame;

   --  Four bytes with the same word are the same bytes.
   procedure Lemma_Word_Bytes (A0, A1, A2, A3, B0, B1, B2, B3 : Byte) with
     Ghost, Global => null,
     Pre  => Kome.Keys.Word_Of (A0, A1, A2, A3) = Kome.Keys.Word_Of (B0, B1, B2, B3),
     Post => A0 = B0 and then A1 = B1 and then A2 = B2 and then A3 = B3;

   procedure Lemma_Word_Bytes (A0, A1, A2, A3, B0, B1, B2, B3 : Byte) is
   begin
      Kome.Keys.Lemma_Lanes_Round_Trip (A0, A1, A2, A3);
      Kome.Keys.Lemma_Lanes_Round_Trip (B0, B1, B2, B3);
   end Lemma_Word_Bytes;

   --  Six bytes with the same u48 are the same bytes.
   procedure Lemma_U48_Bytes (A0, A1, A2, A3, A4, A5, B0, B1, B2, B3, B4, B5 : Byte) with
     Ghost, Global => null,
     Pre  => Kome.Records.U48_Of (A0, A1, A2, A3, A4, A5)
             = Kome.Records.U48_Of (B0, B1, B2, B3, B4, B5),
     Post => A0 = B0 and then A1 = B1 and then A2 = B2
             and then A3 = B3 and then A4 = B4 and then A5 = B5;

   procedure Lemma_U48_Bytes (A0, A1, A2, A3, A4, A5, B0, B1, B2, B3, B4, B5 : Byte) is
   begin
      Kome.Records.Lemma_U48_Bytes_Round_Trip (A0, A1, A2, A3, A4, A5);
      Kome.Records.Lemma_U48_Bytes_Round_Trip (B0, B1, B2, B3, B4, B5);
   end Lemma_U48_Bytes;

   --  An append of an entry that is not an EXPIRE keeps the logged
   --  horizon.
   procedure Lemma_Horizon_Append (Old_S, S : Store) with
     Ghost, Global => null,
     Pre  => Horizon_Logged (Old_S)
       and then Log_Extends (Old_S, S)
       and then Log_Entries (S) = Log_Entries (Old_S) + 1
       and then Horizon (S) = Horizon (Old_S)
       and then not Is_Expire (S, Log_Entries (S))
       and then (for all K in 1 .. Log_Entries (Old_S) =>
                   Has_Log_Entry (Old_S, Entry_Start (Old_S, K))),
     Post => Horizon_Logged (S);

   procedure Lemma_Horizon_Append (Old_S, S : Store) is
      N : constant Natural := Log_Entries (Old_S);
      W : Natural := 0;
   begin
      for K in 1 .. N loop
         pragma Assert (Entry_Start (S, K) = Entry_Start (Old_S, K));
         pragma Assert (Has_Log_Entry (Old_S, Entry_Start (Old_S, K)));
         pragma Assert (Entry_Start (Old_S, K) < Log_Length (Old_S));
         pragma Assert (Op_At (S, Entry_Start (S, K)) = Op_At (Old_S, Entry_Start (Old_S, K)));
         if Op_At (Old_S, Entry_Start (Old_S, K)) = Op_Expire then
            pragma Assert (Log_Length (Old_S) - Entry_Start (Old_S, K) >= Expire_Len);
            pragma Assert (Is_Expire (Old_S, K));
            pragma Assert (Is_Expire (S, K));
            pragma Assert
              (Code_At (S, Entry_Start (S, K) + 1) = Code_At (Old_S, Entry_Start (Old_S, K) + 1));
            W := K;
         else
            pragma Assert (not Is_Expire (Old_S, K));
            pragma Assert (not Is_Expire (S, K));
         end if;
         pragma Loop_Invariant (W <= K);
         pragma Loop_Invariant (if W > 0 then Is_Expire (Old_S, W));
         pragma Loop_Invariant (for all K2 in W + 1 .. K => not Is_Expire (Old_S, K2));
         pragma Loop_Invariant
           (for all K2 in 1 .. K =>
              Is_Expire (S, K2) = Is_Expire (Old_S, K2)
              and then (if Is_Expire (Old_S, K2)
                        then Expire_Horizon (S, K2) = Expire_Horizon (Old_S, K2)));
      end loop;
      if W > 0 then
         pragma Assert (Horizon (Old_S) <= Expire_Horizon (Old_S, W));
         pragma Assert
           (Is_Expire (S, W) and then Horizon (S) <= Expire_Horizon (S, W)
            and then (for all K2 in W + 1 .. N + 1 => not Is_Expire (S, K2)));
      else
         pragma Assert (for all K2 in 1 .. N => not Is_Expire (Old_S, K2));
         pragma Assert (Horizon (Old_S) = No_Horizon);
         pragma Assert (for all K2 in 1 .. N + 1 => not Is_Expire (S, K2));
      end if;
   end Lemma_Horizon_Append;

   --  A store whose last entry is an EXPIRE at or above its horizon logs
   --  it.
   procedure Lemma_Horizon_Expire (S : Store) with
     Ghost, Global => null,
     Pre  => Log_Entries (S) >= 1
       and then Is_Expire (S, Log_Entries (S))
       and then Horizon (S) <= Expire_Horizon (S, Log_Entries (S)),
     Post => Horizon_Logged (S);

   procedure Lemma_Horizon_Expire (S : Store) is
      N : constant Positive := Log_Entries (S);
   begin
      pragma Assert
        (Is_Expire (S, N) and then Horizon (S) <= Expire_Horizon (S, N)
         and then (for all K2 in N + 1 .. Log_Entries (S) => not Is_Expire (S, K2)));
   end Lemma_Horizon_Expire;

   --  Replay of an APPLY of a record that is already held (AUDIT.md H23):
   --  as Put_Frame (OK, no change), but the entry stays in the log, so the
   --  log is still the input. Nothing else changes.
   procedure Keep_Apply
     (S : in out Store; F : Frontier.State; Frame : Byte_Array; Off : out Log_Size)
   with
     Global => null,
     Pre  => Valid (S, F)
       and then Frame'Length in Frame_Size
       and then S.Log_Cap - S.LL >= Apply_Prefix + Frame'Length,
     Post => Valid (S, F)
       and then Off = S.LL'Old
       and then S.NS = S.NS'Old and then S.Fnd = S.Fnd'Old
       and then S.Root = S.Root'Old and then S.Slt = S.Slt'Old
       and then S.Cid = S.Cid'Old
       and then S.DCap = S.DCap'Old and then S.Slc = S.Slc'Old
       and then S.Hz = S.Hz'Old
       and then S.AG = S.AG'Old and then S.EM = S.EM'Old
       and then Log_Extends (S'Old, S)
       and then Grew_By (S'Old, S, Off, Apply_Prefix + Frame'Length)
       and then Op_At (S, Off) = Op_Apply
       and then Frame_Stored (S, Off, Frame);

   procedure Keep_Apply
     (S : in out Store; F : Frontier.State; Frame : Byte_Array; Off : out Log_Size)
   is
      Saved : constant Store := S with Ghost;
   begin
      Off := S.LL;
      Lemma_Ends_Below (S.Log, S.LL, S.Idx, S.NI);
      Log_Entry_Apply (S.Log, S.LL, S.Bnd, S.NB, S.Idx, S.NI,
                       S.NSb, S.Root, S.Slt, S.DCap, S.Slc, Op_Apply, Frame);
      pragma Assert (S.LL = Off + Apply_Prefix + Frame'Length);
      Lemma_Stored_From (S, Off, Frame);
      pragma Assert (Frame_Stored (S, Off, Frame));
      pragma Assert (Valid (S, F));
      pragma Assert (for all J in 0 .. Off - 1 => S.Log (J) = Saved.Log (J));
      pragma Assert (Log_Extends (Saved, S));
      pragma Assert (Grew_By (Saved, S, Off, Apply_Prefix + Frame'Length));
      pragma Assert (Op_At (S, Off) = Op_Apply);
   end Keep_Apply;

   --  The OK facts of Replay_Frame, read in the log array. This is a
   --  bridge lemma, so each branch of Replay_Frame proves them in a small
   --  context.
   --  The appended entry is named by Off (= Old_S.LL), the term that the
   --  callers' facts carry, so that the Pre matches them as written.
   procedure Lemma_Replayed
     (Old_S, S : Store; Op : Byte; Frame : Byte_Array; Off : Log_Size)
   with
     Ghost, Global => null,
     Pre  => Frame'Length in Frame_Size
       and then Old_S.LL <= Old_S.Log_Cap and then S.LL <= S.Log_Cap
       and then Off = Old_S.LL
       and then Log_Extends (Old_S, S)
       and then Grew_By (Old_S, S, Off, Apply_Prefix + Frame'Length)
       and then Op_At (S, Off) = Op
       and then Frame_Stored (S, Off, Frame),
     Post => S.LL = Old_S.LL + Apply_Prefix + Frame'Length
       and then (for all J in 0 .. Old_S.LL - 1 => S.Log (J) = Old_S.Log (J))
       and then S.Log (Old_S.LL) = Op
       and then Len_Word (S.Log, Old_S.LL) = Word (Frame'Length)
       and then (for all K in 0 .. Frame'Length - 1 =>
                   S.Log (Old_S.LL + Apply_Prefix + K) = Frame (Frame'First + K));

   procedure Lemma_Replayed
     (Old_S, S : Store; Op : Byte; Frame : Byte_Array; Off : Log_Size)
   is
   begin
      pragma Assert (Log_Length (S) = S.LL and then Log_Length (Old_S) = Old_S.LL);
      pragma Assert (S.LL = Off + Apply_Prefix + Frame'Length);
      pragma Assert (for all J in 0 .. Old_S.LL - 1 => S.Log (J) = Old_S.Log (J));
      pragma Assert (S.Log (Off) = Op);
      pragma Assert (Frame_Stored (S, Old_S.LL, Frame));
      Lemma_Frame_Stored_Log (S, Old_S.LL, Frame);
   end Lemma_Replayed;

   --  Replay accepts the APPLY (Op_Apply) or APPLY_EXPIRED entry Frame:
   --  the frame verifies and is of the collection, and Put_Frame would
   --  hold and index it as a new record, or holds it already (AUDIT.md
   --  H23); or it is an admitted, undominated DEL that is not held.
   function Replay_Accepts
     (S : Store; F : Frontier.State; Op : Byte; Frame : Byte_Array) return Boolean
   is
     (Verified (S.Cid, Frame)
      and then Canonical (Header_Of (S.Cid, Frame))
      and then Header_Of (S.Cid, Frame).K = Kome.Records.Kind_Of (Frame)
      and then Header_Of (S.Cid, Frame).NS = S.NS
      and then not (Kome.Records.Is_Auth_Frame (Frame)
                    and then Kome.Records.Root_Key_Of (Frame) /= S.Fnd)
      and then Admitted (F, Header_Of (S.Cid, Frame))
      and then
        (if Op = Op_Apply then
           Holds (F, Header_Of (S.Cid, Frame))
           or else (not Dom (F, Header_Of (S.Cid, Frame))
                    and then not Expired (Header_Of (S.Cid, Frame), S.Hz)
                    and then not Data_Full (F, Header_Of (S.Cid, Frame))
                    and then not Auth_Rule (F, Header_Of (S.Cid, Frame))
                    and then not Gen_Full (S, Header_Of (S.Cid, Frame)))
         else Header_Of (S.Cid, Frame).K = K_Del
              and then not Holds (F, Header_Of (S.Cid, Frame))
              and then not Dom (F, Header_Of (S.Cid, Frame))))
   with Pre => Is_Frontier (F);

   --  The checks of replay for one APPLY or APPLY_EXPIRED entry. S and F
   --  are only read, so a refusal changes nothing (AUDIT.md H23: the store
   --  stays at the entry boundary). No_Space: the data row of this open is
   --  full (AUDIT.md A11); Malformed: a store with these capacities did
   --  not write this entry.
   procedure Replay_Check
     (S      : Store;
      F      : Frontier.State;
      Op     : Byte;
      Frame  : Byte_Array;
      Result : out Status)
   with
     Global => null,
     Pre  => Valid (S, F) and then Frame'Length in Frame_Size,
     Post => Result in OK | Malformed | No_Space
       and then (Result = OK) = Replay_Accepts (S, F, Op, Frame);

   procedure Replay_Check
     (S      : Store;
      F      : Frontier.State;
      Op     : Byte;
      Frame  : Byte_Array;
      Result : out Status)
   is
      Accepted : Boolean;
      H        : Header;
   begin
      Result := Malformed;
      Decode_Frame (S.Cid, Frame, Accepted);
      if not Accepted then
         return;
      end if;
      H := Header_Of (S.Cid, Frame);
      Lemma_Header_Of (S.Cid, Frame);
      Lemma_Verified_Canonical (S.Cid, Frame);
      if H.NS /= S.NS
        or else (Kome.Records.Is_Auth_Frame (Frame)
                 and then Kome.Records.Root_Key_Of (Frame) /= S.Fnd)
        or else not Admitted (F, H)
      then
         return;
      end if;
      if Op = Op_Apply then
         if not Holds (F, H) then
            if Dom (F, H) or else Expired (H, S.Hz) then
               return;
            end if;
            if Data_Full (F, H) then
               --  The data row of this open is full: the log does not
               --  replay at this capacity (AUDIT.md A11).
               Result := No_Space;
               return;
            end if;
            if Auth_Rule (F, H) or else Gen_Full (S, H) then
               return;
            end if;
         end if;
      elsif H.K /= K_Del or else Holds (F, H) or else Dom (F, H) then
         return;
      end if;
      Result := OK;
   end Replay_Check;

   --  The OK facts of Replay_Frame for an appended APPLY_EXPIRED, in a
   --  small context (no Valid): a bridge from Appended_Expired.
   procedure Lemma_Expired_Replayed (Old_S, S : Store; Frame : Byte_Array) with
     Ghost, Global => null,
     Pre  => Frame'Length in Frame_Size
       and then Old_S.LL <= Old_S.Log_Cap and then S.LL <= S.Log_Cap
       and then Log_Extends (Old_S, S)
       and then Appended_Expired (Old_S, S, Frame, Old_S.LL),
     Post => Log_Extends (Old_S, S)
       and then Grew_By (Old_S, S, Old_S.LL, Apply_Prefix + Frame'Length)
       and then Op_At (S, Old_S.LL) = Op_Apply_Expired
       and then S.LL = Old_S.LL + Apply_Prefix + Frame'Length
       and then (for all J in 0 .. Old_S.LL - 1 => S.Log (J) = Old_S.Log (J))
       and then S.Log (Old_S.LL) = Op_Apply_Expired
       and then Len_Word (S.Log, Old_S.LL) = Word (Frame'Length)
       and then (for all K in 0 .. Frame'Length - 1 =>
                   S.Log (Old_S.LL + Apply_Prefix + K) = Frame (Frame'First + K));

   procedure Lemma_Expired_Replayed (Old_S, S : Store; Frame : Byte_Array) is
   begin
      pragma Assert (Grew_By (Old_S, S, Old_S.LL, Apply_Prefix + Frame'Length));
      pragma Assert (Op_At (S, Old_S.LL) = Op_Apply_Expired);
      pragma Assert (Frame_Stored (S, Old_S.LL, Frame));
      Lemma_Replayed (Old_S, S, Op_Apply_Expired, Frame, Old_S.LL);
   end Lemma_Expired_Replayed;

   --  Replay an APPLY_EXPIRED entry: the admitted, undominated DEL Frame,
   --  applied for its effect (a small context for the branch of
   --  Replay_Frame).
   procedure Replay_Expired
     (S     : in out Store;
      F     : in out Frontier.State;
      Frame : Byte_Array;
      H     : Header)
   with
     Global => null,
     Pre  => Valid (S, F)
       and then H.K = K_Del
       and then Canonical (H)
       and then H.NS = S.NS
       and then Admitted (F, H)
       and then not Dom (F, H)
       and then not Holds (F, H)
       and then Frame'Length in Frame_Size
       and then S.Log_Cap - S.LL >= Apply_Prefix + Frame'Length,
     Post => Valid (S, F)
       and then Logged_Cap (S) = Logged_Cap (S'Old)
       and then Log_Extends (S'Old, S)
       and then Grew_By (S'Old, S, S.LL'Old, Apply_Prefix + Frame'Length)
       and then Op_At (S, S.LL'Old) = Op_Apply_Expired
       and then Horizon (S) = Horizon (S'Old)
       and then S.LL = S.LL'Old + Apply_Prefix + Frame'Length
       and then (for all J in 0 .. S.LL'Old - 1 => S.Log (J) = S'Old.Log (J))
       and then S.Log (S.LL'Old) = Op_Apply_Expired
       and then Len_Word (S.Log, S.LL'Old) = Word (Frame'Length)
       and then (for all K in 0 .. Frame'Length - 1 =>
                   S.Log (S.LL'Old + Apply_Prefix + K) = Frame (Frame'First + K));

   procedure Replay_Expired
     (S     : in out Store;
      F     : in out Frontier.State;
      Frame : Byte_Array;
      H     : Header)
   is
      Saved : constant Store := S with Ghost;
   begin
      Do_Apply_Expired (S, F, Frame, H);
      pragma Assert (Horizon (S) = Horizon (Saved));
      pragma Assert (S.DCap = Saved.DCap);
      Lemma_Expired_Replayed (Saved, S, Frame);
   end Replay_Expired;

   --  Replay one APPLY or APPLY_EXPIRED entry that Replay_Check accepts:
   --  Frame, at the end of the log.
   procedure Replay_Frame
     (S      : in out Store;
      F      : in out Frontier.State;
      Op     : Byte;
      Frame  : Byte_Array)
   with
     Global => null,
     Pre  => Valid (S, F)
       and then (Op = Op_Apply or else Op = Op_Apply_Expired)
       and then Frame'Length in Frame_Size
       and then S.Log_Cap - S.LL >= Apply_Prefix + Frame'Length
       and then Replay_Accepts (S, F, Op, Frame),
     Post => Valid (S, F)
       and then Logged_Cap (S) = Logged_Cap (S'Old)
       and then Log_Extends (S'Old, S)
       and then Grew_By (S'Old, S, S.LL'Old, Apply_Prefix + Frame'Length)
       and then Op_At (S, S.LL'Old) = Op
       and then Horizon (S) = Horizon (S'Old)
       and then S.LL = S.LL'Old + Apply_Prefix + Frame'Length
       and then (for all J in 0 .. S.LL'Old - 1 => S.Log (J) = S'Old.Log (J))
       and then S.Log (S.LL'Old) = Op
       and then Len_Word (S.Log, S.LL'Old) = Word (Frame'Length)
       and then (for all K in 0 .. Frame'Length - 1 =>
                   S.Log (S.LL'Old + Apply_Prefix + K) = Frame (Frame'First + K));

   procedure Replay_Frame
     (S      : in out Store;
      F      : in out Frontier.State;
      Op     : Byte;
      Frame  : Byte_Array)
   is
      Saved : constant Store := S with Ghost;
      H     : constant Header := Header_Of (S.Cid, Frame);
      Off   : Log_Size;
      St    : Status;
   begin
      Lemma_Header_Of (S.Cid, Frame);
      Lemma_Verified_Canonical (S.Cid, Frame);
      pragma Assert (H.NS = Collection (S));
      if Op = Op_Apply then
         if Holds (F, H) then
            --  AUDIT.md H23: already held. Put_Frame answers OK and changes
            --  nothing; replay keeps the entry in the log.
            Keep_Apply (S, F, Frame, Off);
            Lemma_Replayed (Saved, S, Op, Frame, Off);
         else
            --  Put_Frame holds and indexes it as a new record: Replay_Check
            --  decided its refusals, and the log has room, so Log_Full
            --  cannot occur.
            pragma Assert (not Foreign_Root (S, Frame));
            pragma Assert (not Dom (F, H) and then not Expired (H, Horizon (S)));
            pragma Assert (not Data_Full (F, H) and then not Auth_Rule (F, H)
                           and then not Gen_Full (S, H));
            Put_Frame (S, F, Frame, H, Off, St);
            pragma Assert (St = OK);
            pragma Assert (Appended (Saved, S, Frame, H, Off));
            pragma Assert (Off = Saved.LL);
            pragma Assert (Horizon (S) = Horizon (Saved));
            pragma Assert (Log_Extends (Saved, S));
            Lemma_Replayed (Saved, S, Op, Frame, Off);
         end if;
      else
         --  An admitted, undominated DEL, applied for its effect.
         pragma Assert (H.K = K_Del and then Canonical (H) and then H.NS = S.NS);
         pragma Assert (Admitted (F, H) and then not Dom (F, H) and then not Holds (F, H));
         Replay_Expired (S, F, Frame, H);
      end if;
   end Replay_Frame;

   --  A (PA ..) = B (0 ..) and B (0 ..) = C (PC ..) over Len bytes.
   procedure Lemma_Bytes_Trans
     (A : Byte_Array; PA : Natural; B : Byte_Array; C : Byte_Array; PC : Natural;
      Len : Natural)
   with
     Ghost, Global => null,
     Pre  => A'First = 0 and then B'First = 0 and then C'First = 0
       and then A'Last <= Log_Max and then B'Last <= Log_Max and then C'Last <= Log_Max
       and then Len - 1 <= B'Last
       and then PA <= A'Last + 1 and then Len <= A'Last + 1 - PA
       and then PC <= C'Last + 1 and then Len <= C'Last + 1 - PC
       and then (for all K in 0 .. Len - 1 => A (PA + K) = B (K))
       and then (for all K in 0 .. Len - 1 => B (K) = C (PC + K)),
     Post => (for all K in 0 .. Len - 1 => A (PA + K) = C (PC + K));

   procedure Lemma_Bytes_Trans
     (A : Byte_Array; PA : Natural; B : Byte_Array; C : Byte_Array; PC : Natural;
      Len : Natural) is
   begin
      for K in 0 .. Len - 1 loop
         pragma Assert (A (PA + K) = B (K));
         pragma Assert (B (K) = C (PC + K));
         pragma Loop_Invariant (for all K2 in 0 .. K => A (PA + K2) = C (PC + K2));
      end loop;
   end Lemma_Bytes_Trans;

   --  Log and Input agree below P and on P .. P + Len - 1: they agree
   --  below P + Len.
   procedure Lemma_Agree_Grow (Log, Input : Byte_Array; P, Len : Natural) with
     Ghost, Global => null,
     Pre  => Log'First = 0 and then Input'First = 0
       and then Log'Last <= Log_Max and then Input'Last <= Log_Max
       and then P <= Log'Last and then Len <= Log'Last - P + 1
       and then P <= Input'Last and then Len <= Input'Last - P + 1
       and then (for all J in 0 .. P - 1 => Log (J) = Input (J))
       and then (for all K in 0 .. Len - 1 => Log (P + K) = Input (P + K)),
     Post => (for all J in 0 .. P + Len - 1 => Log (J) = Input (J));

   procedure Lemma_Agree_Grow (Log, Input : Byte_Array; P, Len : Natural) is
   begin
      for J in 0 .. P + Len - 1 loop
         if J >= P then
            declare
               K : constant Natural := J - P;
            begin
               pragma Assert (K < Len);
               pragma Assert (Log (P + K) = Input (P + K));
               pragma Assert (P + K = J);
            end;
         end if;
         pragma Loop_Invariant (for all J2 in 0 .. J => Log (J2) = Input (J2));
      end loop;
   end Lemma_Agree_Grow;

   --  The bytes of an APPLY entry: op, len, frame.
   procedure Lemma_Apply_Agree (Log, Input : Byte_Array; P : Natural; FL : Frame_Size) with
     Ghost, Global => null,
     Pre  => Log'First = 0 and then Input'First = 0
       and then Log'Last <= Log_Max and then Input'Last <= Log_Max
       and then P <= Log'Last and then Apply_Prefix + FL <= Log'Last - P + 1
       and then P <= Input'Last and then Apply_Prefix + FL <= Input'Last - P + 1
       and then Log (P) = Input (P)
       and then Log (P + 1) = Input (P + 1) and then Log (P + 2) = Input (P + 2)
       and then Log (P + 3) = Input (P + 3) and then Log (P + 4) = Input (P + 4)
       and then (for all K in 0 .. FL - 1 =>
                   Log (P + Apply_Prefix + K) = Input (P + Apply_Prefix + K)),
     Post => (for all K in 0 .. Apply_Prefix + FL - 1 => Log (P + K) = Input (P + K));

   procedure Lemma_Apply_Agree (Log, Input : Byte_Array; P : Natural; FL : Frame_Size) is
   begin
      for K in 0 .. Apply_Prefix + FL - 1 loop
         if K >= Apply_Prefix then
            declare
               K1 : constant Natural := K - Apply_Prefix;
            begin
               pragma Assert (K1 < FL);
               pragma Assert (Log (P + Apply_Prefix + K1) = Input (P + Apply_Prefix + K1));
               pragma Assert (P + Apply_Prefix + K1 = P + K);
            end;
         end if;
         pragma Loop_Invariant (for all K2 in 0 .. K => Log (P + K2) = Input (P + K2));
      end loop;
   end Lemma_Apply_Agree;

   --  Replay the entry of Input at the end of the log.
   procedure Replay_Entry
     (S      : in out Store;
      F      : in out Frontier.State;
      Input  : Byte_Array;
      Result : out Status)
   with
     Global => null,
     Pre  => Valid (S, F)
       and then Input'First = 0
       and then Input'Last < S.Log_Cap
       and then S.LL <= Input'Last
       and then (for all J in 0 .. S.LL - 1 => S.Log (J) = Input (J))
       and then Horizon_Logged (S),
     Post => Valid (S, F)
       and then Result in OK | Malformed | No_Space
       and then Logged_Cap (S) = Logged_Cap (S'Old)
       --  A refusal leaves the store at the entry boundary (AUDIT.md H23).
       and then (if Result /= OK then
                   S.LL = S.LL'Old
                   and then (for all J in 0 .. S.LL - 1 => S.Log (J) = S'Old.Log (J))
                   and then Horizon_Logged (S))
       and then (if Result = OK then
                   S.LL > S.LL'Old
                   and then S.LL <= Input'Last + 1
                   and then (for all J in 0 .. S.LL - 1 => S.Log (J) = Input (J))
                   and then Horizon_Logged (S));

   procedure Replay_Entry
     (S      : in out Store;
      F      : in out Frontier.State;
      Input  : Byte_Array;
      Result : out Status)
   is
      Len   : constant Natural := Input'Last + 1;
      P     : constant Log_Size := S.LL;
      Op    : constant Byte := Input (P);
      Saved : constant Store := S with Ghost;
   begin
      pragma Assert (Horizon_Logged (Saved));
      Lemma_Scan (Saved, F);
      Lemma_Valid_Facts (S, F);
      Result := Malformed;
      if Op = Op_Apply or else Op = Op_Apply_Expired then
         if Len - P < Apply_Prefix then
            return;
         end if;
         declare
            LW : constant Word :=
              Kome.Keys.Word_Of (Input (P + 1), Input (P + 2), Input (P + 3), Input (P + 4));
         begin
            if LW < 1 or else LW > Kome.Records.Frame_Max
              or else Natural (LW) > Len - P - Apply_Prefix
            then
               return;
            end if;
            declare
               FL    : constant Frame_Size := Natural (LW);
               Frame : constant Byte_Array (0 .. FL - 1) :=
                 Input (P + Apply_Prefix .. P + Apply_Prefix + FL - 1);
               St    : Status;
            begin
               pragma Assert (for all K in 0 .. FL - 1 => Frame (K) = Input (P + Apply_Prefix + K));
               Replay_Check (S, F, Op, Frame, St);
               if St /= OK then
                  Result := St;
                  return;
               end if;
               Replay_Frame (S, F, Op, Frame);
               Lemma_Word_Bytes
                 (S.Log (P + 1), S.Log (P + 2), S.Log (P + 3), S.Log (P + 4),
                  Input (P + 1), Input (P + 2), Input (P + 3), Input (P + 4));
               pragma Assert
                 (for all K in 0 .. FL - 1 => S.Log (P + Apply_Prefix + K) = Frame (K));
               Lemma_Bytes_Trans (S.Log, P + Apply_Prefix, Frame, Input, P + Apply_Prefix, FL);
               pragma Assert
                 (for all K in 0 .. FL - 1 =>
                    S.Log (P + Apply_Prefix + K) = Input (P + Apply_Prefix + K));
               pragma Assert (S.Log (P) = Input (P));
               pragma Assert (for all J in 0 .. P - 1 => S.Log (J) = Input (J));
               Lemma_Apply_Agree (S.Log, Input, P, FL);
               Lemma_Agree_Grow (S.Log, Input, P, Apply_Prefix + FL);
               pragma Assert (S.LL = P + Apply_Prefix + FL);
               pragma Assert (for all J in 0 .. S.LL - 1 => S.Log (J) = Input (J));
               pragma Assert (Entry_Start (S, Log_Entries (S)) = P);
               pragma Assert (Op_At (S, P) /= Op_Expire);
               pragma Assert (not Is_Expire (S, Log_Entries (S)));
               Lemma_Horizon_Append (Saved, S);
            end;
         end;
      elsif Op = Op_Expire then
         if Len - P < Expire_Len then
            return;
         end if;
         declare
            Code  : constant U48 :=
              Kome.Records.U48_Of (Input (P + 1), Input (P + 2), Input (P + 3),
                                   Input (P + 4), Input (P + 5), Input (P + 6));
            --  AUDIT.md H24: the horizon that replay applies is at most
            --  maxceil - del_ttl_eff of the frontier at this point. The
            --  logged bytes stay as they are.
            Bound : constant Horizon_Value := Horizon_At (F, U48'Last);
            Hn    : constant Horizon_Value := Time64'Min (Horizon_Of_Code (Code), Bound);
         begin
            Do_Expire (S, F, Hn, Code);
            Lemma_U48_Bytes
              (S.Log (P + 1), S.Log (P + 2), S.Log (P + 3),
               S.Log (P + 4), S.Log (P + 5), S.Log (P + 6),
               Input (P + 1), Input (P + 2), Input (P + 3),
               Input (P + 4), Input (P + 5), Input (P + 6));
            pragma Assert (S.Log (P) = Input (P));
            pragma Assert (for all J in 0 .. P - 1 => S.Log (J) = Input (J));
            pragma Assert (for all K in 0 .. Expire_Len - 1 => S.Log (P + K) = Input (P + K));
            Lemma_Agree_Grow (S.Log, Input, P, Expire_Len);
            pragma Assert (S.LL = P + Expire_Len);
            pragma Assert (for all J in 0 .. S.LL - 1 => S.Log (J) = Input (J));
            pragma Assert (Entry_Start (S, Log_Entries (S)) = P);
            pragma Assert (Is_Expire (S, Log_Entries (S)));
            pragma Assert (Code_At (S, P + 1) = Code);
            pragma Assert (Expire_Horizon (S, Log_Entries (S)) = Horizon_Of_Code (Code));
            pragma Assert (Horizon (S) <= Expire_Horizon (S, Log_Entries (S)));
            Lemma_Horizon_Expire (S);
         end;
      else
         --  A second HEADER, or an unknown op.
         return;
      end if;
      Result := OK;
   end Replay_Entry;

   --  The HEADER that Init writes for the fields read from Input is the
   --  HEADER of Input.
   procedure Lemma_Header_Agree
     (Log, Input : Byte_Array; Root : Pubkey; Slt : Salt; Cap_W : Word;
      Slc_V : Kome.Records.U16_Value)
   with
     Ghost, Global => null,
     Pre  => Log'First = 0 and then Input'First = 0
       and then Log'Last >= Header_Len - 1 and then Input'Last >= Header_Len - 1
       and then Cap_W <= Word (Held_Max) and then Slc_V <= Slice_Max
       and then (for all J in 0 .. Header_Len - 1 =>
                   Log (J) = Header_Byte (Root, Slt, Kome.Records.Collection_Id (Root, Slt),
                                          Data_Size (Cap_W), Slc_V, J))
       and then Input (0) = Op_Header
       and then (for all J in 0 .. Magic_Len - 1 => Input (HO_Magic + J) = Magic (J))
       and then Input (HO_Version) = Log_Version
       and then (for all J in 0 .. NS_Len - 1 =>
                   Input (HO_NS + J) = Kome.Records.Collection_Id (Root, Slt) (J))
       and then (for all J in 0 .. Pubkey_Len - 1 => Root (J) = Input (HO_Root + J))
       and then (for all J in 0 .. Salt_Len - 1 => Slt (J) = Input (HO_Salt + J))
       and then Cap_W = Kome.Keys.Word_Of (Input (HO_Cap), Input (HO_Cap + 1),
                                           Input (HO_Cap + 2), Input (HO_Cap + 3))
       and then Slc_V = Kome.Records.U16_Of (Input (HO_Slice), Input (HO_Slice + 1)),
     Post => (for all J in 0 .. Header_Len - 1 => Log (J) = Input (J));

   procedure Lemma_Header_Agree
     (Log, Input : Byte_Array; Root : Pubkey; Slt : Salt; Cap_W : Word;
      Slc_V : Kome.Records.U16_Value)
   is
   begin
      Kome.Keys.Lemma_Lanes_Round_Trip
        (Input (HO_Cap), Input (HO_Cap + 1), Input (HO_Cap + 2), Input (HO_Cap + 3));
      Kome.Records.Lemma_U16_Bytes_Round_Trip (Input (HO_Slice), Input (HO_Slice + 1));
      pragma Assert (Word (Data_Size (Cap_W)) = Cap_W);
      for J in 0 .. Header_Len - 1 loop
         if J = 0 then
            pragma Assert (Log (J) = Input (J));
         elsif J < HO_Version then
            pragma Assert (Log (J) = Magic (J - HO_Magic));
            pragma Assert (Input (HO_Magic + (J - HO_Magic)) = Magic (J - HO_Magic));
         elsif J = HO_Version then
            pragma Assert (Log (J) = Input (J));
         elsif J < HO_Root then
            pragma Assert (Input (HO_NS + (J - HO_NS)) =
                             Kome.Records.Collection_Id (Root, Slt) (J - HO_NS));
         elsif J < HO_Salt then
            pragma Assert (Root (J - HO_Root) = Input (HO_Root + (J - HO_Root)));
         elsif J < HO_Cap then
            pragma Assert (Slt (J - HO_Salt) = Input (HO_Salt + (J - HO_Salt)));
         elsif J < HO_Slice then
            pragma Assert (Log (J) = Kome.Keys.Byte_Of_Word (Cap_W, J - HO_Cap));
         else
            pragma Assert (Log (J) = Kome.Records.Byte_Of_U16 (Slc_V, J - HO_Slice));
         end if;
         pragma Assert (Log (J) = Input (J));
         pragma Loop_Invariant (for all J2 in 0 .. J => Log (J2) = Input (J2));
      end loop;
   end Lemma_Header_Agree;

   --  The log of S, read through Log_Byte, is Image (a bridge lemma).
   procedure Lemma_Log_Agrees (S : Store; Image : Byte_Array) with
     Ghost, Global => null,
     Pre  => Image'First = 0 and then Image'Last < S.Log_Cap
       and then S.LL <= S.Log_Cap and then S.LL = Image'Last + 1
       and then (for all J in 0 .. S.LL - 1 => S.Log (J) = Image (J)),
     Post => Log_Length (S) = Image'Last + 1
       and then (for all J in 0 .. Image'Last => Log_Byte (S, J) = Image (J));

   procedure Lemma_Log_Agrees (S : Store; Image : Byte_Array) is
   begin
      pragma Assert (Log_Length (S) = S.LL and then S.LL = Image'Last + 1);
   end Lemma_Log_Agrees;

   --  The T18-prefix clause of the Post of Open_From_Log, from the facts
   --  that its replay loop keeps (prover time: one small goal, AUDIT.md
   --  H23).
   procedure Open_Post_Parts
     (Input : Byte_Array; F : Frontier.State; S : Store; VL : Log_Size; Cap_W : Word)
   with
     Ghost, Global => null,
     Pre  => Input'First = 0
       and then Valid (S, F)
       and then Horizon_Logged (S)
       and then Input'Last < S.Log_Cap
       and then Header_Well_Formed (Input)
       and then Header_Slice (Input) = F.Slice
       and then Header_Cap (Input) = Cap_W
       and then Word (S.DCap) = Cap_W
       and then S.Slc = F.Slice
       and then VL >= Header_Len
       and then VL - 1 <= Input'Last
       and then Log_Length (S) = VL
       and then (for all J in 0 .. VL - 1 => Log_Byte (S, J) = Input (J)),
     Post => Replayed_Prefix (Input, F, S, VL);

   procedure Open_Post_Parts
     (Input : Byte_Array; F : Frontier.State; S : Store; VL : Log_Size; Cap_W : Word)
   is
   begin
      pragma Assert (Logged_Cap (S) = S.DCap and then Word (S.DCap) = Cap_W);
      pragma Assert (Logged_Slice (S) = S.Slc and then Log_Length (S) = VL);
      pragma Assert (Word (Logged_Cap (S)) = Header_Cap (Input));
      pragma Assert (Logged_Slice (S) = F.Slice);
      pragma Assert (Replayed_Prefix (Input, F, S, VL));
   end Open_Post_Parts;

   procedure Open_From_Log
     (Input        : in     Byte_Array;
      F            :    out Frontier.State;
      S            :    out Store;
      Valid_Length :    out Log_Size;
      Result       :    out Status)
   is
   begin
      Valid_Length := 0;
      F := Frontier.Empty (Zero_Id, Zero_Key, F.Cap, F.Slice);
      --  Component by component, as in Init (no temporary store).
      S.NS   := Zero_Id;
      S.NSb  := [others => 0];
      S.Fnd  := Zero_Key;
      S.Root := [others => 0];
      S.Slt  := [others => 0];
      S.Cid  := [others => 0];
      S.DCap := 0;
      S.Slc  := 0;
      S.Hz   := No_Horizon;
      S.AG   := 0;
      S.EM   := 0;
      S.NI   := 0;
      S.Idx  := [others => (H => <>, Off => 0, Len => 1)];
      S.LL   := 0;
      S.Log  := [others => 0];
      S.NB   := 0;
      S.Bnd  := [others => 0];
      if Input'Last >= S.Log_Cap then
         Result := No_Space;
         return;
      end if;
      if Input'Last < Header_Len - 1
        or else Input (0) /= Op_Header
        or else Input (HO_Magic .. HO_Magic + Magic_Len - 1) /= Magic
        or else Input (HO_Version) /= Log_Version
      then
         Result := Malformed;
         return;
      end if;

      declare
         Len   : constant Natural := Input'Last + 1;
         Root  : constant Pubkey := Input (HO_Root .. HO_Root + Pubkey_Len - 1);
         Slt   : constant Salt := Input (HO_Salt .. HO_Salt + Salt_Len - 1);
         NSb   : constant NS_Id := Kome.Records.Collection_Id (Root, Slt);
         Cap_W : constant Word :=
           Kome.Keys.Word_Of (Input (HO_Cap), Input (HO_Cap + 1),
                              Input (HO_Cap + 2), Input (HO_Cap + 3));
         Slc_V : constant Kome.Records.U16_Value :=
           Kome.Records.U16_Of (Input (HO_Slice), Input (HO_Slice + 1));
      begin
         pragma Assert
           (NSb = Kome.Records.Collection_Id (Input (HO_Root .. HO_Root + Pubkey_Len - 1),
                                              Input (HO_Salt .. HO_Salt + Salt_Len - 1)));
         if Input (HO_NS .. HO_NS + NS_Len - 1) /= NSb
           or else Cap_W > Word (Data_Size'Last)
         then
            pragma Assert (not Header_Well_Formed (Input));
            Result := Malformed;
            return;
         end if;
         pragma Assert (Header_Well_Formed (Input));
         pragma Assert (Header_Cap (Input) = Cap_W and then Header_Slice (Input) = Slc_V);
         --  The slice is fixed for the collection (AUDIT.md A11).
         if Slc_V /= F.Slice then
            Result := No_Space;
            return;
         end if;

         F := Frontier.Empty (Kome.Keys.To_Id128 (NSb), Kome.Keys.To_Key256 (Root),
                              F.Cap, F.Slice);
         --  The HEADER keeps the logged data_cap; the slice is the slice
         --  of this open (see the comment at the top of the spec).
         Init (S, Root, Slt, Data_Size (Cap_W), F.Slice);
         Lemma_Valid_Start (S, F);
         pragma Assert (not Is_Expire (S, 1));
         pragma Assert (Horizon_Logged (S));

         --  The written HEADER is the HEADER of the input (prover time:
         --  the fields of Input first).
         pragma Assert (for all J in 0 .. Magic_Len - 1 => Input (HO_Magic + J) = Magic (J));
         pragma Assert (for all J in 0 .. NS_Len - 1 => Input (HO_NS + J) = NSb (J));
         pragma Assert (for all J in 0 .. Pubkey_Len - 1 => Root (J) = Input (HO_Root + J));
         pragma Assert (for all J in 0 .. Salt_Len - 1 => Slt (J) = Input (HO_Salt + J));
         pragma Assert (Word (Data_Size (Cap_W)) = Cap_W);
         Lemma_Header_Agree (S.Log, Input, Root, Slt, Cap_W, Slc_V);
         pragma Assert (for all J in 0 .. S.LL - 1 => S.Log (J) = Input (J));
         Valid_Length := Header_Len;

         --  Replay the journal. Valid_Length is the start of the entry
         --  under replay; a refused entry leaves the store at that
         --  boundary (AUDIT.md H23).
         loop
            pragma Loop_Invariant (Valid (S, F));
            pragma Loop_Invariant (Horizon_Logged (S));
            pragma Loop_Invariant (S.LL >= Header_Len and then S.LL <= Len);
            pragma Loop_Invariant (for all J in 0 .. S.LL - 1 => S.Log (J) = Input (J));
            pragma Loop_Invariant (S.DCap = Data_Size (Cap_W));
            pragma Loop_Invariant (Valid_Length = S.LL);
            pragma Loop_Invariant (S.Slc = F.Slice);
            pragma Loop_Variant (Increases => S.LL);
            exit when S.LL = Len;
            pragma Assert (Input'Last >= Header_Len);
            pragma Assert (S.LL <= Input'Last and then Input'Last < S.Log_Cap);
            declare
               St : Status;
            begin
               Replay_Entry (S, F, Input, St);
               if St /= OK then
                  pragma Assert (S.LL = Valid_Length);
                  pragma Assert (for all J in 0 .. S.LL - 1 => S.Log (J) = Input (J));
                  pragma Assert (Log_Length (S) = Valid_Length);
                  pragma Assert
                    (for all J in 0 .. Valid_Length - 1 => Log_Byte (S, J) = Input (J));
                  Open_Post_Parts (Input, F, S, Valid_Length, Cap_W);
                  pragma Assert (Valid_Length - 1 <= Input'Last);
                  Result := St;
                  return;
               end if;
               Valid_Length := S.LL;
            end;
         end loop;
         pragma Assert (S.LL = Len and then Log_Length (S) = Len);
         Lemma_Log_Agrees (S, Input);
         pragma Assert (for all J in 0 .. Input'Last => Log_Byte (S, J) = Input (J));
         pragma Assert (Header_Cap (Input) = Cap_W);
         pragma Assert (Valid_Length = Len);
         pragma Assert (for all J in 0 .. Valid_Length - 1 => Log_Byte (S, J) = Input (J));
         Open_Post_Parts (Input, F, S, Valid_Length, Cap_W);
         pragma Assert (Valid_Length - 1 = Input'Last);
         Result := OK;
      end;
   end Open_From_Log;

   ---------------------------------------------------------------------------
   --  The cell index.
   ---------------------------------------------------------------------------

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

   procedure Lemma_Header_Of (Cid : Hash256; Frame : Byte_Array) is
   begin
      --  One kind per branch (the data kinds' h is under Cid, A26).
      case Kome.Records.Kind_Of (Frame) is
         when K_Put    =>
            pragma Assert
              (Header_Of (Cid, Frame) = Kome.Records.To_Header (Cid, Kome.Records.Parse_Put (Frame)));
            pragma Assert (Header_Of (Cid, Frame).K = K_Put);
         when K_Del    =>
            pragma Assert
              (Header_Of (Cid, Frame) = Kome.Records.To_Header (Cid, Kome.Records.Parse_Del (Frame)));
            pragma Assert (Header_Of (Cid, Frame).K = K_Del);
         when K_Roster =>
            pragma Assert
              (Header_Of (Cid, Frame) = Kome.Records.To_Header (Kome.Records.Parse_Roster (Frame)));
         when K_Revoke =>
            pragma Assert
              (Header_Of (Cid, Frame) = Kome.Records.To_Header (Kome.Records.Parse_Revoke (Frame)));
         when K_Grant  =>
            pragma Assert
              (Header_Of (Cid, Frame) = Kome.Records.To_Header (Kome.Records.Parse_Grant (Frame)));
      end case;
   end Lemma_Header_Of;

   procedure Lemma_Verified_Canonical (Cid : Hash256; Frame : Byte_Array) is
   begin
      case Kome.Records.Kind_Of (Frame) is
         when K_Put    =>
            Kome.Records.Lemma_Header_Canonical (Cid, Kome.Records.Parse_Put (Frame));
         when K_Del    =>
            Kome.Records.Lemma_Header_Canonical (Cid, Kome.Records.Parse_Del (Frame));
         when K_Roster => Kome.Records.Lemma_Header_Canonical (Kome.Records.Parse_Roster (Frame));
         when K_Revoke => Kome.Records.Lemma_Header_Canonical (Kome.Records.Parse_Revoke (Frame));
         when K_Grant  => Kome.Records.Lemma_Header_Canonical (Kome.Records.Parse_Grant (Frame));
      end case;
   end Lemma_Verified_Canonical;

   procedure Lemma_Valid_Facts (S : Store; F : Frontier.State) is
   begin
      pragma Assert (Head_OK (S.Log, S.LL, S.NSb, S.Root, S.Slt, S.DCap, S.Slc));
   end Lemma_Valid_Facts;

   procedure Lemma_Log_Header (S : Store; F : Frontier.State) is
   begin
      --  One fact per conjunct of the Post (prover time).
      pragma Assert (Head_OK (S.Log, S.LL, S.NSb, S.Root, S.Slt, S.DCap, S.Slc));
      pragma Assert (S.LL <= S.Log_Cap and then Log_Length (S) = S.LL);
      pragma Assert (S.NSb = Kome.Records.Collection_Id (S.Root, S.Slt));
      pragma Assert (Log_Length (S) >= Header_Len);
      pragma Assert (Op_At (S, 0) = Op_Header);
      pragma Assert (for all J in 0 .. Magic_Len - 1 => Log_Byte (S, HO_Magic + J) = Magic (J));
      pragma Assert (Log_Byte (S, HO_Version) = Log_Version);
      pragma Assert (for all J in 0 .. NS_Len - 1 => Log_Byte (S, HO_NS + J) = S.NSb (J));
      pragma Assert
        (for all J in 0 .. NS_Len - 1 =>
           Log_Byte (S, HO_NS + J) = Kome.Records.Collection_Id (Root_Key (S), Salt_Of (S)) (J));
      pragma Assert (for all J in 0 .. Pubkey_Len - 1 => Log_Byte (S, HO_Root + J) = Root_Key (S) (J));
      pragma Assert (for all J in 0 .. Salt_Len - 1 => Log_Byte (S, HO_Salt + J) = Salt_Of (S) (J));
   end Lemma_Log_Header;

   procedure Lemma_Entry_Held (S : Store; F : Frontier.State; I : Held_Index) is
   begin
      pragma Assert (Frame_OK (S.Log, S.LL, S.Idx (I)));
      pragma Assert (Len_At (S, S.Idx (I).Off) = Len_Word (S.Log, S.Idx (I).Off));
      pragma Assert (At_Bounds (S.Idx, S.NI, S.Bnd, S.NB));
      pragma Assert
        (for all J in 1 .. S.NI => (for some K in 1 .. S.NB => S.Bnd (K) = S.Idx (J).Off));
      pragma Assert (for some K in 1 .. S.NB => S.Bnd (K) = S.Idx (I).Off);
   end Lemma_Entry_Held;

   procedure Lemma_Held_Indexed (S : Store; F : Frontier.State; K : Held_Index) is
   begin
      pragma Assert (Covered (F, S.Idx, S.NI));
   end Lemma_Held_Indexed;

   procedure Lemma_No_Expired (S : Store; F : Frontier.State; K : Held_Index) is
   begin
      pragma Assert (Fresh (F, S.Hz));
   end Lemma_No_Expired;

   procedure Lemma_Indexed (S : Store; X : Header) is null;

   procedure Lemma_Position (S : Store; F : Frontier.State; I : Held_Index) is
      J : constant Held_Index := Position (S, S.Idx (I).H);
   begin
      if J /= I then
         Lemma_Sorted_Distinct (S.Idx, S.NI, I, J);
      end if;
   end Lemma_Position;

   procedure Lemma_Scan (S : Store; F : Frontier.State) is
   begin
      pragma Assert (Chain (S.Log, S.LL, S.Bnd, S.NB));
      pragma Assert (Log_Entries (S) = S.NB and then Log_Length (S) = S.LL);
      for K in 1 .. S.NB loop
         Lemma_Chain_At (S.Log, S.LL, S.Bnd, S.NB, K);
         pragma Assert (S.Bnd (K) < S.LL);
         pragma Assert (Op_At (S, S.Bnd (K)) = S.Log (S.Bnd (K)));
         pragma Assert
           (if S.Log (S.Bnd (K)) = Op_Apply or else S.Log (S.Bnd (K)) = Op_Apply_Expired
            then Len_At (S, S.Bnd (K)) = Len_Word (S.Log, S.Bnd (K)));
         pragma Assert (Has_Log_Entry (S, S.Bnd (K)));
         pragma Assert (Entry_Size (S, S.Bnd (K)) = Size_At (S.Log, S.Bnd (K)));
         --  The facts for this K, in the terms of the invariant (prover
         --  time).
         pragma Assert ((Op_At (S, S.Bnd (K)) = Op_Header) = (K = 1));
         pragma Assert
           (Next_Offset (S, S.Bnd (K)) = (if K < S.NB then S.Bnd (K + 1) else S.LL));
         pragma Assert
           (Has_Log_Entry (S, Entry_Start (S, K))
            and then (Op_At (S, Entry_Start (S, K)) = Op_Header) = (K = 1)
            and then Next_Offset (S, Entry_Start (S, K)) =
                       (if K < Log_Entries (S) then Entry_Start (S, K + 1)
                        else Log_Length (S)));
         pragma Loop_Invariant
           (for all K2 in 1 .. K =>
              Has_Log_Entry (S, Entry_Start (S, K2))
              and then (Op_At (S, Entry_Start (S, K2)) = Op_Header) = (K2 = 1)
              and then Next_Offset (S, Entry_Start (S, K2)) =
                         (if K2 < Log_Entries (S) then Entry_Start (S, K2 + 1)
                          else Log_Length (S)));
      end loop;
   end Lemma_Scan;

   procedure Lemma_Cell_Unique (S : Store; F : Frontier.State; I, J : Held_Index) is
      K1 : constant Held_Index := Witness (F, S.Idx (I).H);
      K2 : constant Held_Index := Witness (F, S.Idx (J).H);
   begin
      Kome.Views.Lemma_Cell_Unique (F, K1, K2);
      pragma Assert (S.Idx (I).H = S.Idx (J).H);
      if I /= J then
         Lemma_Sorted_Distinct (S.Idx, S.NI, I, J);
      end if;
   end Lemma_Cell_Unique;

end Kome.Store;
