--  Test main for Kome.Byteorder: (a) contract corner cases, (b) the ghost
--  lemmas evaluated at run time (-gnata) on corner values and on every
--  vector, (c) byte-for-byte comparison against vectors/byteorder.txt,
--  produced from the C++ helpers by vectors/gen/byteorder_gen.cpp.
--  Every GET/RD/ST vector is also replayed on a copy with a non-zero
--  'First so that cursor and offset arithmetic is pinned relative to
--  the buffer origin, as the C++ pointer arithmetic is.
--  (d) Regressions: the shift-based functional views (Byte_Of_*, Read_*)
--  agree with the arithmetic (divide / sum) formulation they replaced,
--  With_LE_* agrees with Store_*, and the get(put(x)) = x law is checked
--  in its stated form on every vector, not only via the lemma's Post.
pragma Ada_2022;
with Ada.Text_IO;         use Ada.Text_IO;
with Ada.Command_Line;    use Ada.Command_Line;
with Kome;                use Kome;
with Kome.Byteorder;      use Kome.Byteorder;

procedure Test_Byteorder with SPARK_Mode => Off is

   Failed : Boolean := False;

   procedure Check (Name : String; Cond : Boolean) is
   begin
      Put_Line ((if Cond then "PASS " else "FAIL ") & Name);
      if not Cond then
         Failed := True;
      end if;
   end Check;

   ----------------------------------------------------------------------
   --  Arithmetic references for the shift-based views in the spec: the
   --  C++ (uint8_t)(v >> (i*8)) is v / 2**(8i) mod 256, and the OR of
   --  shifted lanes is their sum because the lanes are disjoint.
   ----------------------------------------------------------------------

   function Ref_Byte_U32 (V : U32; I : U32_Index) return Byte is
     (Byte ((V / (2 ** (8 * I))) mod 256));
   function Ref_Byte_U64 (V : U64; I : U64_Index) return Byte is
     (Byte ((V / (2 ** (8 * I))) mod 256));

   function Ref_Read_U32 (B : Byte_Array; Pos : Natural) return U32 is
     (U32 (B (Pos)) + U32 (B (Pos + 1)) * 2 ** 8
      + U32 (B (Pos + 2)) * 2 ** 16 + U32 (B (Pos + 3)) * 2 ** 24);
   function Ref_Read_U64 (B : Byte_Array; Pos : Natural) return U64 is
     (U64 (B (Pos)) + U64 (B (Pos + 1)) * 2 ** 8
      + U64 (B (Pos + 2)) * 2 ** 16 + U64 (B (Pos + 3)) * 2 ** 24
      + U64 (B (Pos + 4)) * 2 ** 32 + U64 (B (Pos + 5)) * 2 ** 40
      + U64 (B (Pos + 6)) * 2 ** 48 + U64 (B (Pos + 7)) * 2 ** 56);

   function Views_Agree_U32 (V : U32) return Boolean is
     ((for all I in U32_Index => Byte_Of_U32 (V, I) = Ref_Byte_U32 (V, I))
      and then Read_U32LE (To_LE_U32 (V), 0) = Ref_Read_U32 (To_LE_U32 (V), 0));
   function Views_Agree_U64 (V : U64) return Boolean is
     ((for all I in U64_Index => Byte_Of_U64 (V, I) = Ref_Byte_U64 (V, I))
      and then Read_U64LE (To_LE_U64 (V), 0) = Ref_Read_U64 (To_LE_U64 (V), 0));

   --  get(put(x)) = x as the spec states it, re-evaluated here with the
   --  real Put and Get rather than trusting the lemma's Post alone.
   function Get_Put_Law_U32 (Buf : Byte_Array; Len : Natural; V : U32)
                             return Boolean
   is
      B   : Byte_Array := Buf;
      L   : Natural    := Len;
      Cur : constant Natural := Buf'First + Len;
      Pos : Natural := Cur;
      Got : U32;
      OK  : Boolean;
   begin
      Put_U32LE (B, L, V);
      Get_U32LE (B (Buf'First .. Buf'First + L - 1), Pos, Got, OK);
      return B = With_LE_U32 (Buf, Cur, V)
        and then Has_Bytes (With_LE_U32 (Buf, Cur, V), Cur, U32_Len)
        and then Read_U32LE (With_LE_U32 (Buf, Cur, V), Cur) = V
        and then OK and then Got = V and then Pos = Cur + U32_Len
        and then L = Len + U32_Len;
   end Get_Put_Law_U32;

   function Get_Put_Law_U64 (Buf : Byte_Array; Len : Natural; V : U64)
                             return Boolean
   is
      B   : Byte_Array := Buf;
      L   : Natural    := Len;
      Cur : constant Natural := Buf'First + Len;
      Pos : Natural := Cur;
      Got : U64;
      OK  : Boolean;
   begin
      Put_U64LE (B, L, V);
      Get_U64LE (B (Buf'First .. Buf'First + L - 1), Pos, Got, OK);
      return B = With_LE_U64 (Buf, Cur, V)
        and then Has_Bytes (With_LE_U64 (Buf, Cur, V), Cur, U64_Len)
        and then Read_U64LE (With_LE_U64 (Buf, Cur, V), Cur) = V
        and then OK and then Got = V and then Pos = Cur + U64_Len
        and then L = Len + U64_Len;
   end Get_Put_Law_U64;

   ----------------------------------------------------------------------
   --  Tiny line tokenizer and hex decoders for the vector file.
   ----------------------------------------------------------------------

   Max_Fields : constant := 8;
   type Field_Array is array (1 .. Max_Fields) of Natural;  --  start, end

   procedure Split
     (Line : String; Starts, Ends : out Field_Array; Count : out Natural)
   is
      I : Natural := Line'First;
   begin
      Count  := 0;
      Starts := [others => 0];
      Ends   := [others => 0];
      while I <= Line'Last loop
         if Line (I) = ' ' then
            I := I + 1;
         else
            declare
               J : Natural := I;
            begin
               while J <= Line'Last and then Line (J) /= ' ' loop
                  J := J + 1;
               end loop;
               Count := Count + 1;
               Starts (Count) := I;
               Ends (Count)   := J - 1;
               I := J;
            end;
         end if;
      end loop;
   end Split;

   function Nibble (C : Character) return Byte is
     (case C is
        when '0' .. '9' => Character'Pos (C) - Character'Pos ('0'),
        when 'a' .. 'f' => Character'Pos (C) - Character'Pos ('a') + 10,
        when 'A' .. 'F' => Character'Pos (C) - Character'Pos ('A') + 10,
        when others     => raise Constraint_Error with "bad hex digit");

   function Hex_U64 (S : String) return U64 is
      V : U64 := 0;
   begin
      for C of S loop
         V := V * 16 + U64 (Nibble (C));
      end loop;
      return V;
   end Hex_U64;

   function Hex_U32 (S : String) return U32 is (U32 (Hex_U64 (S)));

   function Dec_Nat (S : String) return Natural is
      V : Natural := 0;
   begin
      for C of S loop
         V := V * 10 + (Character'Pos (C) - Character'Pos ('0'));
      end loop;
      return V;
   end Dec_Nat;

   --  "-" encodes the empty byte string.
   function Hex_Bytes (S : String) return Byte_Array is
   begin
      if S = "-" then
         return Byte_Array'(1 .. 0 => 0);
      end if;
      return R : Byte_Array (0 .. S'Length / 2 - 1) do
         for I in R'Range loop
            R (I) := Nibble (S (S'First + 2 * I)) * 16
                     + Nibble (S (S'First + 2 * I + 1));
         end loop;
      end return;
   end Hex_Bytes;

   ----------------------------------------------------------------------
   --  (a) Contract corner cases.
   ----------------------------------------------------------------------

   procedure Corner_Cases is
   begin
      --  Functional views on a value whose bytes are all distinct.
      Check ("to_le_u32 byte order",
             To_LE_U32 (16#01020304#) = U32_Bytes'[4, 3, 2, 1]);
      Check ("to_le_u64 byte order",
             To_LE_U64 (16#0102030405060708#) =
               U64_Bytes'[8, 7, 6, 5, 4, 3, 2, 1]);
      Check ("byte_of_u32 lanes",
             Byte_Of_U32 (16#DEADBEEF#, 0) = 16#EF#
             and Byte_Of_U32 (16#DEADBEEF#, 1) = 16#BE#
             and Byte_Of_U32 (16#DEADBEEF#, 2) = 16#AD#
             and Byte_Of_U32 (16#DEADBEEF#, 3) = 16#DE#);
      Check ("byte_of_u32 shift view = divide view",
             Views_Agree_U32 (0) and Views_Agree_U32 (U32'Last)
             and Views_Agree_U32 (16#DEADBEEF#) and Views_Agree_U32 (16#8000_0000#)
             and Views_Agree_U32 (16#0000_0100#) and Views_Agree_U32 (16#00FF_0000#));
      Check ("byte_of_u64 shift view = divide view",
             Views_Agree_U64 (0) and Views_Agree_U64 (U64'Last)
             and Views_Agree_U64 (16#0102030405060708#)
             and Views_Agree_U64 (16#8000_0000_0000_0000#)
             and Views_Agree_U64 (16#0000_0100_0000_0000#)
             and Views_Agree_U64 (16#00FF_0000_0000_0000#));
      Check ("byte_of_u32 top lane is bits 24..31",
             Byte_Of_U32 (16#8000_0000#, 3) = 16#80#
             and Byte_Of_U32 (16#8000_0000#, 0) = 0
             and Byte_Of_U32 (16#7FFF_FFFF#, 3) = 16#7F#);
      Check ("byte_of_u64 top lane is bits 56..63",
             Byte_Of_U64 (16#8000_0000_0000_0000#, 7) = 16#80#
             and Byte_Of_U64 (16#8000_0000_0000_0000#, 0) = 0
             and Byte_Of_U64 (16#7FFF_FFFF_FFFF_FFFF#, 7) = 16#7F#);
      Check ("read_u32 all-ff", Read_U32LE ([16#FF#, 16#FF#, 16#FF#, 16#FF#], 0) = U32'Last);
      Check ("read_u64 all-ff", Read_U64LE (U64_Bytes'[others => 16#FF#], 0) = U64'Last);
      Check ("read_u32 top lane only", Read_U32LE ([0, 0, 0, 16#80#], 0) = 16#8000_0000#);
      Check ("read_u64 top lane only",
             Read_U64LE ([0, 0, 0, 0, 0, 0, 0, 16#80#], 0) = 16#8000_0000_0000_0000#);

      --  Store into the middle of a larger buffer with a non-zero 'First:
      --  the Post (checked by -gnata) says neighbours are untouched; we
      --  re-check it here explicitly.
      declare
         Buf : Byte_Array (10 .. 29) := [others => 16#AA#];
      begin
         Store_U32LE (Buf, 12, 16#11223344#);
         Check ("store_u32 in place",
                Buf (10 .. 11) = Byte_Array'[16#AA#, 16#AA#]
                and Buf (12 .. 15) = Byte_Array'[16#44#, 16#33#, 16#22#, 16#11#]
                and (for all J in 16 .. 29 => Buf (J) = 16#AA#));
         Store_U64LE (Buf, 22, 16#0102030405060708#);
         Check ("store_u64 at last slot",
                Buf (22 .. 29) = Byte_Array'[8, 7, 6, 5, 4, 3, 2, 1]
                and (for all J in 16 .. 21 => Buf (J) = 16#AA#));
         Check ("read_u32 at offset", Read_U32LE (Buf, 12) = 16#11223344#);
         Check ("read_u64 at offset", Read_U64LE (Buf, 22) = 16#0102030405060708#);
         Store_U32LE (Buf, 26, 16#FFFFFFF0#);
         Check ("store_u32 at very last slot", Buf (26 .. 29) = Byte_Array'[16#F0#, 16#FF#, 16#FF#, 16#FF#]);
      end;

      --  With_LE_*: the functional view of Store has the buffer's bounds,
      --  the encoding at Pos and the original bytes elsewhere, and is
      --  exactly what Store_* produces (its Post, re-checked here).
      declare
         Init : constant Byte_Array (10 .. 29) := [others => 16#AA#];
         W32  : constant Byte_Array := With_LE_U32 (Init, 12, 16#11223344#);
         W64  : constant Byte_Array := With_LE_U64 (W32, 22, 16#0102030405060708#);
         Buf  : Byte_Array := Init;
      begin
         Check ("with_le_u32 bounds", W32'First = 10 and W32'Last = 29);
         Check ("with_le_u32 bytes",
                W32 (10 .. 11) = Byte_Array'[16#AA#, 16#AA#]
                and W32 (12 .. 15) = Byte_Array'[16#44#, 16#33#, 16#22#, 16#11#]
                and (for all J in 16 .. 29 => W32 (J) = 16#AA#));
         Check ("with_le_u64 bounds", W64'First = 10 and W64'Last = 29);
         Check ("with_le_u64 bytes",
                W64 (10 .. 21) = W32 (10 .. 21)
                and W64 (22 .. 29) = Byte_Array'[8, 7, 6, 5, 4, 3, 2, 1]);
         Store_U32LE (Buf, 12, 16#11223344#);
         Check ("store_u32 = with_le_u32", Buf = W32);
         Store_U64LE (Buf, 22, 16#0102030405060708#);
         Check ("store_u64 = with_le_u64", Buf = W64);
         Check ("with_le_u32 at first slot",
                With_LE_U32 (Init, 10, 16#DEADBEEF#) (10 .. 13)
                  = Byte_Array'[16#EF#, 16#BE#, 16#AD#, 16#DE#]
                and With_LE_U32 (Init, 10, 16#DEADBEEF#) (14 .. 29) = Init (14 .. 29));
         Check ("with_le_u64 at last slot",
                With_LE_U64 (Init, 22, 16#DEADBEEF#) (22 .. 29)
                  = Byte_Array'[16#EF#, 16#BE#, 16#AD#, 16#DE#, 0, 0, 0, 0]
                and With_LE_U64 (Init, 22, 16#DEADBEEF#) (10 .. 21) = Init (10 .. 21));
         Check ("read of with_le_u32 is the value",
                Read_U32LE (With_LE_U32 (Init, 17, 16#CAFEBABE#), 17) = 16#CAFEBABE#);
         Check ("read of with_le_u64 is the value",
                Read_U64LE (With_LE_U64 (Init, 17, 16#CAFEBABE_DEADBEEF#), 17)
                  = 16#CAFEBABE_DEADBEEF#);
      end;

      --  Put: append semantics on a bounded buffer with a non-zero 'First.
      declare
         Buf : Byte_Array (3 .. 20) := [others => 0];
         Len : Natural := 0;
      begin
         Put_U64LE (Buf, Len, 500);
         Check ("put_u64 len", Len = 8);
         Put_U32LE (Buf, Len, 1);
         Check ("put_u32 len", Len = 12);
         Check ("put manifest header bytes",
                Buf (3 .. 14) = Byte_Array'[16#F4#, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
                and (for all J in 15 .. 20 => Buf (J) = 0));
         Put_U32LE (Buf, Len, 16#DEADBEEF#);
         Check ("put_u32 appends after prefix",
                Len = 16
                and Buf (3 .. 14) = Byte_Array'[16#F4#, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
                and Buf (15 .. 18) = Byte_Array'[16#EF#, 16#BE#, 16#AD#, 16#DE#]);
         --  Exactly fills the buffer: Len = Buf'Length is allowed.
         declare
            Full : Byte_Array (0 .. 3) := [others => 0];
            L    : Natural := 0;
         begin
            Put_U32LE (Full, L, 16#01020304#);
            Check ("put fills buffer exactly", L = 4 and Full = U32_Bytes'[4, 3, 2, 1]);
         end;
         Check ("get(put(x)) = x law u32 (stated form)",
                Get_Put_Law_U32 (Buf, 0, 16#01020304#)
                and Get_Put_Law_U32 (Buf, 7, U32'Last)
                and Get_Put_Law_U32 (Buf, 14, 16#80000000#));
         Check ("get(put(x)) = x law u64 (stated form)",
                Get_Put_Law_U64 (Buf, 0, 16#0102030405060708#)
                and Get_Put_Law_U64 (Buf, 5, U64'Last)
                and Get_Put_Law_U64 (Buf, 10, 16#8000000000000000#));
      end;

      --  Get: cursor semantics, short reads, exhausted cursor.
      declare
         Buf : constant Byte_Array (5 .. 15) :=
           [16#F4#, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0];   --  11 bytes: u64 + 3
         Pos : Natural := 5;
         V64 : U64;
         V32 : U32;
         OK  : Boolean;
      begin
         Get_U64LE (Buf, Pos, V64, OK);
         Check ("get_u64 ok", OK and V64 = 500 and Pos = 13);
         Get_U32LE (Buf, Pos, V32, OK);
         Check ("get_u32 short by one rejects", not OK and Pos = 13 and V32 = 0);
         Get_U64LE (Buf, Pos, V64, OK);
         Check ("get_u64 short rejects", not OK and Pos = 13 and V64 = 0);
         Pos := 12;
         Get_U32LE (Buf, Pos, V32, OK);
         --  Buf (12 .. 15) = 00 01 00 00 = 16#100#.
         Check ("get_u32 exactly four left", OK and V32 = 16#100# and Pos = 16);
         --  Pos = Buf'Last + 1 is p == end.
         Get_U32LE (Buf, Pos, V32, OK);
         Check ("get_u32 exhausted cursor", not OK and Pos = 16 and V32 = 0);
         Get_U64LE (Buf, Pos, V64, OK);
         Check ("get_u64 exhausted cursor", not OK and Pos = 16 and V64 = 0);
         --  Slices stand in for a smaller "end".
         Pos := 5;
         Get_U64LE (Buf (5 .. 11), Pos, V64, OK);
         Check ("get_u64 via slice end", not OK and Pos = 5);
         Get_U32LE (Buf (5 .. 8), Pos, V32, OK);
         Check ("get_u32 via slice end", OK and V32 = 16#1F4# and Pos = 9);
      end;

      --  Empty buffer.
      declare
         Empty : constant Byte_Array (1 .. 0) := [];
         Pos   : Natural := 1;
         V32   : U32;
         V64   : U64;
         OK    : Boolean;
      begin
         Get_U32LE (Empty, Pos, V32, OK);
         Check ("get_u32 empty", not OK and Pos = 1 and V32 = 0);
         Get_U64LE (Empty, Pos, V64, OK);
         Check ("get_u64 empty", not OK and Pos = 1 and V64 = 0);
      end;

      --  Has_Bytes boundary.
      declare
         B : constant Byte_Array (0 .. 7) := [others => 0];
      begin
         Check ("has_bytes 8 at 0", Has_Bytes (B, 0, 8));
         Check ("has_bytes 8 at 1 fails", not Has_Bytes (B, 1, 8));
         Check ("has_bytes 4 at 4", Has_Bytes (B, 4, 4));
         Check ("has_bytes 4 at 5 fails", not Has_Bytes (B, 5, 4));
         Check ("has_bytes 1 at end fails", not Has_Bytes (B, 8, 1));
      end;

      --  Index arithmetic at the top of Natural. The C++ puts no bound on
      --  where a 4/8-byte store or read may sit; a Byte_Array may end at
      --  Natural'Last, and a store or read whose last byte is that index
      --  must still work (an earlier contract wrote Pos + N - 1, which
      --  overflowed Integer here). A Get that succeeds at the very end
      --  leaves Pos = Buf'Last + 1, so Get requires Buf'Last < Natural'Last
      --  and is exercised one slot below the top.
      declare
         Top  : Byte_Array (Natural'Last - 7 .. Natural'Last) := [others => 16#EE#];
         Near : constant Byte_Array (Natural'Last - 12 .. Natural'Last - 1) :=
           [16#F4#, 1, 0, 0, 0, 0, 0, 0, 16#EF#, 16#BE#, 16#AD#, 16#DE#];
         Pos  : Natural := Near'First;
         V32  : U32;
         V64  : U64;
         OK   : Boolean;
      begin
         Store_U32LE (Top, Natural'Last - 3, 16#01020304#);
         Check ("store_u32 ending at Natural'Last",
                Top (Natural'Last - 7 .. Natural'Last - 4) = Byte_Array'[16#EE#, 16#EE#, 16#EE#, 16#EE#]
                and Top (Natural'Last - 3 .. Natural'Last) = Byte_Array'[4, 3, 2, 1]);
         Check ("read_u32 ending at Natural'Last",
                Read_U32LE (Top, Natural'Last - 3) = 16#01020304#);
         Store_U64LE (Top, Natural'Last - 7, 16#0102030405060708#);
         Check ("store_u64 ending at Natural'Last",
                Top = Byte_Array'[8, 7, 6, 5, 4, 3, 2, 1]);
         Check ("read_u64 ending at Natural'Last",
                Read_U64LE (Top, Natural'Last - 7) = 16#0102030405060708#);
         Check ("has_bytes at Natural'Last",
                Has_Bytes (Top, Natural'Last - 3, 4)
                and not Has_Bytes (Top, Natural'Last - 2, 4)
                and Has_Bytes (Top, Natural'Last, 1));
         Get_U64LE (Near, Pos, V64, OK);
         Check ("get_u64 near Natural'Last", OK and V64 = 500 and Pos = Natural'Last - 4);
         Get_U32LE (Near, Pos, V32, OK);
         Check ("get_u32 ending one below Natural'Last",
                OK and V32 = 16#DEADBEEF# and Pos = Natural'Last);
         Get_U32LE (Near, Pos, V32, OK);
         Check ("get_u32 exhausted at Natural'Last", not OK and Pos = Natural'Last and V32 = 0);
         --  Put that exactly fills a buffer ending one below the top.
         declare
            B : Byte_Array (Natural'Last - 4 .. Natural'Last - 1) := [others => 0];
            L : Natural := 0;
         begin
            Put_U32LE (B, L, 16#04030201#);
            Check ("put_u32 fills buffer near Natural'Last",
                   L = 4 and B = Byte_Array'[1, 2, 3, 4]);
            Lemma_Get_Put_U32 (B, 0, 16#DEADBEEF#);
            Check ("get(put(x)) = x law near Natural'Last",
                   Get_Put_Law_U32 (B, 0, 16#DEADBEEF#));
         end;
      end;

      --  Overlapping stores: the later store wins byte for byte, as in C++.
      declare
         Buf : Byte_Array (0 .. 11) := [others => 16#EE#];
      begin
         Store_U32LE (Buf, 2, 16#01020304#);
         Store_U64LE (Buf, 4, 16#0102030405060708#);
         Check ("store_u64 overwrites u32 tail",
                Buf = Byte_Array'[16#EE#, 16#EE#, 4, 3, 8, 7, 6, 5, 4, 3, 2, 1]);
         Store_U32LE (Buf, 6, 16#DEADBEEF#);
         Check ("store_u32 overwrites u64 middle",
                Buf = Byte_Array'[16#EE#, 16#EE#, 4, 3, 8, 7, 16#EF#, 16#BE#, 16#AD#, 16#DE#, 2, 1]);
      end;

      --  Get must not depend on the bytes beyond the requested width and
      --  must read the same value a raw Read at the cursor returns.
      declare
         Buf : constant Byte_Array (0 .. 15) :=
           [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
         Pos : Natural := 3;
         V32 : U32;
         V64 : U64;
         OK  : Boolean;
      begin
         Get_U32LE (Buf, Pos, V32, OK);
         Check ("get_u32 unaligned equals read", OK and V32 = Read_U32LE (Buf, 3) and V32 = 16#07060504# and Pos = 7);
         Get_U64LE (Buf, Pos, V64, OK);
         Check ("get_u64 unaligned equals read", OK and V64 = Read_U64LE (Buf, 7) and V64 = 16#0F0E0D0C0B0A0908# and Pos = 15);
         Get_U32LE (Buf, Pos, V32, OK);
         Check ("get_u32 one byte left rejects", not OK and Pos = 15 and V32 = 0);
      end;
   end Corner_Cases;

   ----------------------------------------------------------------------
   --  (b) Lemmas on corner values. Each call evaluates the lemma's Post.
   ----------------------------------------------------------------------

   procedure Lemmas_On_Corners is
      Scratch : constant Byte_Array (0 .. 31) := [others => 16#5A#];
      Shifted : constant Byte_Array (7 .. 30) := [others => 16#C3#];
   begin
      for K in 0 .. 31 loop
         Lemma_Read_Store_U32 (2 ** K);
         Lemma_Read_Store_U32 (2 ** K - 1);
         Lemma_Read_Store_U32 (not (2 ** K));
      end loop;
      Lemma_Read_Store_U32 (U32'Last);
      Lemma_Read_Store_U32 (16#DEADBEEF#);
      for K in 0 .. 63 loop
         Lemma_Read_Store_U64 (2 ** K);
         Lemma_Read_Store_U64 (2 ** K - 1);
         Lemma_Read_Store_U64 (not (2 ** K));
      end loop;
      Lemma_Read_Store_U64 (U64'Last);
      Lemma_Read_Store_U64 (16#0102030405060708#);
      Check ("lemma read(store) corners", True);

      Lemma_Store_Read_U32 ([0, 0, 0, 0]);
      Lemma_Store_Read_U32 ([16#FF#, 16#FF#, 16#FF#, 16#FF#]);
      Lemma_Store_Read_U32 ([1, 2, 3, 4]);
      Lemma_Store_Read_U32 ([16#80#, 0, 0, 16#80#]);
      Lemma_Store_Read_U64 ([others => 0]);
      Lemma_Store_Read_U64 ([others => 16#FF#]);
      Lemma_Store_Read_U64 ([1, 2, 3, 4, 5, 6, 7, 8]);
      Lemma_Store_Read_U64 ([16#80#, 0, 0, 0, 0, 0, 0, 16#80#]);
      Check ("lemma store(read) corners", True);

      --  -gnata evaluates each lemma's Post (and the assertions in its
      --  body) on every call; Law_OK re-checks the stated law directly.
      declare
         Law_OK : Boolean := True;
      begin
         for Len in 0 .. 28 loop
            Lemma_Get_Put_U32 (Scratch, Len, 16#01020304#);
            Lemma_Get_Put_U32 (Scratch, Len, U32'Last);
            Law_OK := Law_OK and then Get_Put_Law_U32 (Scratch, Len, 16#01020304#)
              and then Get_Put_Law_U32 (Scratch, Len, U32'Last);
         end loop;
         for Len in 0 .. 24 loop
            Lemma_Get_Put_U64 (Scratch, Len, 16#0102030405060708#);
            Lemma_Get_Put_U64 (Scratch, Len, U64'Last);
            Law_OK := Law_OK and then Get_Put_Law_U64 (Scratch, Len, 16#0102030405060708#)
              and then Get_Put_Law_U64 (Scratch, Len, U64'Last);
         end loop;
         for Len in 0 .. 20 loop
            Lemma_Get_Put_U32 (Shifted, Len, 16#A5A5A5A5#);
            Law_OK := Law_OK and then Get_Put_Law_U32 (Shifted, Len, 16#A5A5A5A5#);
         end loop;
         for Len in 0 .. 16 loop
            Lemma_Get_Put_U64 (Shifted, Len, 16#A5A5A5A5A5A5A5A5#);
            Law_OK := Law_OK and then Get_Put_Law_U64 (Shifted, Len, 16#A5A5A5A5A5A5A5A5#);
         end loop;
         Check ("lemma get(put) corners", Law_OK);
      end;

      --  Shift view = divide view on every power of two and its neighbours.
      declare
         Agree : Boolean := True;
      begin
         for K in 0 .. 31 loop
            Agree := Agree and then Views_Agree_U32 (2 ** K)
              and then Views_Agree_U32 (2 ** K - 1)
              and then Views_Agree_U32 (not (2 ** K));
         end loop;
         for K in 0 .. 63 loop
            Agree := Agree and then Views_Agree_U64 (2 ** K)
              and then Views_Agree_U64 (2 ** K - 1)
              and then Views_Agree_U64 (not (2 ** K));
         end loop;
         Check ("shift views = arithmetic views on corners", Agree);
      end;
   end Lemmas_On_Corners;

   ----------------------------------------------------------------------
   --  (c) Vectors from the C++ engine.
   ----------------------------------------------------------------------

   procedure Vectors is
      F        : File_Type;
      N_U32    : Natural := 0;
      N_U64    : Natural := 0;
      N_Put    : Natural := 0;
      N_Get    : Natural := 0;
      N_Rd     : Natural := 0;
      N_St     : Natural := 0;
      Bad      : Natural := 0;
      Line_No  : Natural := 0;
      Scratch  : Byte_Array (0 .. 63) := [others => 0];
   begin
      Open (F, In_File, "vectors/byteorder.txt");
      while not End_Of_File (F) loop
         declare
            Line   : constant String := Get_Line (F);
            Starts : Field_Array;
            Ends   : Field_Array;
            Count  : Natural;
            Good   : Boolean := True;

            function Fld (K : Positive) return String is
              (Line (Starts (K) .. Ends (K)));
         begin
            Line_No := Line_No + 1;
            if Line'Length > 0 and then Line (Line'First) /= '#' then
               Split (Line, Starts, Ends, Count);
               if Count > 0 then
                  if Fld (1) = "U32" and Count = 4 then
                     declare
                        V     : constant U32        := Hex_U32 (Fld (2));
                        Bytes : constant Byte_Array := Hex_Bytes (Fld (3));
                        Back  : constant U32        := Hex_U32 (Fld (4));
                        Len   : Natural := 3;
                        Pos   : Natural;
                        Got   : U32;
                        OK    : Boolean;
                     begin
                        Good := Bytes'Length = 4
                          and then To_LE_U32 (V) = Bytes
                          and then Read_U32LE (Bytes, 0) = V
                          and then Back = V
                          and then Views_Agree_U32 (V)
                          and then Ref_Read_U32 (Bytes, 0) = V;
                        Store_U32LE (Scratch, 7, V);
                        Good := Good and then Scratch (7 .. 10) = Bytes;
                        Put_U32LE (Scratch, Len, V);
                        Good := Good and then Len = 7 and then Scratch (3 .. 6) = Bytes;
                        Pos := 3;
                        Get_U32LE (Scratch, Pos, Got, OK);
                        Good := Good and then OK and then Got = V and then Pos = 7;
                        Lemma_Read_Store_U32 (V);
                        Lemma_Store_Read_U32 (Bytes);
                        Lemma_Get_Put_U32 (Scratch, 20, V);
                        Good := Good and then Get_Put_Law_U32 (Scratch, 20, V)
                          and then With_LE_U32 (Scratch, 7, V) (7 .. 10) = Bytes;
                        N_U32 := N_U32 + 1;
                     end;
                  elsif Fld (1) = "U64" and Count = 4 then
                     declare
                        V     : constant U64        := Hex_U64 (Fld (2));
                        Bytes : constant Byte_Array := Hex_Bytes (Fld (3));
                        Back  : constant U64        := Hex_U64 (Fld (4));
                        Len   : Natural := 3;
                        Pos   : Natural;
                        Got   : U64;
                        OK    : Boolean;
                     begin
                        Good := Bytes'Length = 8
                          and then To_LE_U64 (V) = Bytes
                          and then Read_U64LE (Bytes, 0) = V
                          and then Back = V
                          and then Views_Agree_U64 (V)
                          and then Ref_Read_U64 (Bytes, 0) = V;
                        Store_U64LE (Scratch, 11, V);
                        Good := Good and then Scratch (11 .. 18) = Bytes;
                        Put_U64LE (Scratch, Len, V);
                        Good := Good and then Len = 11 and then Scratch (3 .. 10) = Bytes;
                        Pos := 3;
                        Get_U64LE (Scratch, Pos, Got, OK);
                        Good := Good and then OK and then Got = V and then Pos = 11;
                        Lemma_Read_Store_U64 (V);
                        Lemma_Store_Read_U64 (Bytes);
                        Lemma_Get_Put_U64 (Scratch, 20, V);
                        Good := Good and then Get_Put_Law_U64 (Scratch, 20, V)
                          and then With_LE_U64 (Scratch, 11, V) (11 .. 18) = Bytes;
                        N_U64 := N_U64 + 1;
                     end;
                  elsif Fld (1) = "PUT" and Count = 4 then
                     declare
                        A     : constant U64        := Hex_U64 (Fld (2));
                        B     : constant U32        := Hex_U32 (Fld (3));
                        Bytes : constant Byte_Array := Hex_Bytes (Fld (4));
                        Buf   : Byte_Array (0 .. 11) := [others => 16#EE#];
                        Len   : Natural := 0;
                        Pos   : Natural := 0;
                        G64   : U64;
                        G32   : U32;
                        OK1   : Boolean;
                        OK2   : Boolean;
                     begin
                        Put_U64LE (Buf, Len, A);
                        Put_U32LE (Buf, Len, B);
                        Good := Len = 12 and then Bytes'Length = 12 and then Buf = Bytes;
                        Get_U64LE (Buf, Pos, G64, OK1);
                        Get_U32LE (Buf, Pos, G32, OK2);
                        Good := Good and then OK1 and then OK2
                          and then G64 = A and then G32 = B and then Pos = 12;
                        N_Put := N_Put + 1;
                     end;
                  elsif Fld (1) = "GET" and Count = 8 then
                     declare
                        Buf   : constant Byte_Array := Hex_Bytes (Fld (2));
                        E_OK1 : constant Boolean := Fld (3) = "1";
                        E_V64 : constant U64     := Hex_U64 (Fld (4));
                        E_P1  : constant Natural := Dec_Nat (Fld (5));
                        E_OK2 : constant Boolean := Fld (6) = "1";
                        E_V32 : constant U32     := Hex_U32 (Fld (7));
                        E_P2  : constant Natural := Dec_Nat (Fld (8));
                        Pos   : Natural := Buf'First;
                        G64   : U64;
                        G32   : U32;
                        OK1   : Boolean;
                        OK2   : Boolean;
                     begin
                        Get_U64LE (Buf, Pos, G64, OK1);
                        Good := OK1 = E_OK1 and then G64 = E_V64
                          and then Pos - Buf'First = E_P1;
                        Get_U32LE (Buf, Pos, G32, OK2);
                        Good := Good and then OK2 = E_OK2 and then G32 = E_V32
                          and then Pos - Buf'First = E_P2;
                        --  Same stream with a non-zero 'First: positions
                        --  are relative to the cursor origin, not to 0.
                        declare
                           Sh : constant Byte_Array (1000 .. 1000 + Buf'Length - 1) := Buf;
                           SP : Natural := 1000;
                        begin
                           Get_U64LE (Sh, SP, G64, OK1);
                           Good := Good and then OK1 = E_OK1 and then G64 = E_V64
                             and then SP - 1000 = E_P1;
                           Get_U32LE (Sh, SP, G32, OK2);
                           Good := Good and then OK2 = E_OK2 and then G32 = E_V32
                             and then SP - 1000 = E_P2;
                        end;
                        N_Get := N_Get + 1;
                     end;
                  elsif Fld (1) = "RD" and Count = 5 then
                     declare
                        Buf   : constant Byte_Array := Hex_Bytes (Fld (2));
                        P     : constant Natural    := Dec_Nat (Fld (3));
                        E_V32 : constant U32        := Hex_U32 (Fld (4));
                        Has64 : constant Boolean    := Fld (5) /= "-";
                        Sh    : constant Byte_Array (77 .. 77 + Buf'Length - 1) := Buf;
                        Pos   : Natural := Buf'First + P;
                        G32   : U32;
                        G64   : U64;
                        OK    : Boolean;
                     begin
                        Good := Read_U32LE (Buf, P) = E_V32
                          and then Read_U32LE (Sh, 77 + P) = E_V32
                          and then Ref_Read_U32 (Buf, P) = E_V32
                          and then Has_Bytes (Buf, P, 8) = Has64;
                        Get_U32LE (Buf, Pos, G32, OK);
                        Good := Good and then OK and then G32 = E_V32 and then Pos = P + 4;
                        Pos := P;
                        Get_U64LE (Buf, Pos, G64, OK);
                        Good := Good and then OK = Has64;
                        if Has64 then
                           declare
                              E_V64 : constant U64 := Hex_U64 (Fld (5));
                           begin
                              Good := Good and then Read_U64LE (Buf, P) = E_V64
                                and then Read_U64LE (Sh, 77 + P) = E_V64
                                and then Ref_Read_U64 (Buf, P) = E_V64
                                and then G64 = E_V64 and then Pos = P + 8;
                           end;
                        else
                           Good := Good and then G64 = 0 and then Pos = P;
                        end if;
                        N_Rd := N_Rd + 1;
                     end;
                  elsif Fld (1) = "ST" and Count = 7 then
                     declare
                        L     : constant Natural    := Dec_Nat (Fld (2));
                        P32   : constant Natural    := Dec_Nat (Fld (3));
                        V32   : constant U32        := Hex_U32 (Fld (4));
                        P64   : constant Natural    := Dec_Nat (Fld (5));
                        V64   : constant U64        := Hex_U64 (Fld (6));
                        Bytes : constant Byte_Array := Hex_Bytes (Fld (7));
                        Buf   : Byte_Array (0 .. L - 1) := [others => 16#EE#];
                        Sh    : Byte_Array (33 .. 33 + L - 1) := [others => 16#EE#];
                     begin
                        Store_U32LE (Buf, P32, V32);
                        Store_U64LE (Buf, P64, V64);
                        Store_U32LE (Sh, 33 + P32, V32);
                        Store_U64LE (Sh, 33 + P64, V64);
                        Good := Bytes'Length = L and then Buf = Bytes and then Sh = Bytes;
                        --  The functional view composes the same way the
                        --  stores do: later store wins byte for byte.
                        declare
                           Init : constant Byte_Array (0 .. L - 1) := [others => 16#EE#];
                        begin
                           Good := Good
                             and then With_LE_U64 (With_LE_U32 (Init, P32, V32), P64, V64) = Bytes;
                        end;
                        N_St := N_St + 1;
                     end;
                  else
                     Good := False;
                  end if;
                  if not Good then
                     Bad := Bad + 1;
                     Put_Line ("FAIL vector line" & Line_No'Image & ": " & Line);
                  end if;
               end if;
            end if;
         end;
      end loop;
      Close (F);
      Check ("vectors u32 count >= 200 (" & N_U32'Image & ")", N_U32 >= 200);
      Check ("vectors u64 count >= 200 (" & N_U64'Image & ")", N_U64 >= 200);
      Check ("vectors put count >= 30 (" & N_Put'Image & ")", N_Put >= 30);
      Check ("vectors get count >= 30 (" & N_Get'Image & ")", N_Get >= 30);
      Check ("vectors rd count >= 100 (" & N_Rd'Image & ")", N_Rd >= 100);
      Check ("vectors st count >= 30 (" & N_St'Image & ")", N_St >= 30);
      Check ("vectors all match", Bad = 0);
   exception
      when Name_Error =>
         Check ("vectors/byteorder.txt present", False);
   end Vectors;

begin
   Corner_Cases;
   Lemmas_On_Corners;
   Vectors;
   if Failed then
      Set_Exit_Status (Failure);
   end if;
end Test_Byteorder;
