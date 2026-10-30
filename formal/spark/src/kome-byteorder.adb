--  Body of Kome.Byteorder. The store/put loops are the C++ loops verbatim
--  (out[i] = (uint8_t)(v >> (i*8))); the reads are the expression functions
--  in the spec; the gets are the C++ bounds check followed by read. The
--  lemma bodies spell out the per-lane facts behind each law.
pragma Ada_2022;
package body Kome.Byteorder with SPARK_Mode is

   -----------------
   -- Store_U32LE --
   -----------------

   procedure Store_U32LE (Buf : in out Byte_Array; Pos : Natural; V : U32) is
      Before : constant Byte_Array := Buf with Ghost;
   begin
      for I in U32_Index loop
         Buf (Pos + I) := Byte_Of_U32 (V, I);
         pragma Loop_Invariant
           (for all K in 0 .. I => Buf (Pos + K) = Byte_Of_U32 (V, K));
         pragma Loop_Invariant
           (for all J in Buf'Range =>
              (if J < Pos or else J > Pos + I
               then Buf (J) = Buf'Loop_Entry (J)));
      end loop;
      pragma Assert
        (for all J in Buf'Range =>
           Buf (J) = (if J >= Pos and then J <= Pos + (U32_Len - 1)
                      then Byte_Of_U32 (V, J - Pos)
                      else Before (J)));
      pragma Assert (Buf = With_LE_U32 (Before, Pos, V));
   end Store_U32LE;

   -----------------
   -- Store_U64LE --
   -----------------

   procedure Store_U64LE (Buf : in out Byte_Array; Pos : Natural; V : U64) is
      Before : constant Byte_Array := Buf with Ghost;
   begin
      for I in U64_Index loop
         Buf (Pos + I) := Byte_Of_U64 (V, I);
         pragma Loop_Invariant
           (for all K in 0 .. I => Buf (Pos + K) = Byte_Of_U64 (V, K));
         pragma Loop_Invariant
           (for all J in Buf'Range =>
              (if J < Pos or else J > Pos + I
               then Buf (J) = Buf'Loop_Entry (J)));
      end loop;
      pragma Assert
        (for all J in Buf'Range =>
           Buf (J) = (if J >= Pos and then J <= Pos + (U64_Len - 1)
                      then Byte_Of_U64 (V, J - Pos)
                      else Before (J)));
      pragma Assert (Buf = With_LE_U64 (Before, Pos, V));
   end Store_U64LE;

   ---------------
   -- Put_U32LE --
   ---------------

   procedure Put_U32LE (Buf : in out Byte_Array; Len : in out Natural; V : U32)
   is
   begin
      Store_U32LE (Buf, Buf'First + Len, V);
      Len := Len + U32_Len;
   end Put_U32LE;

   ---------------
   -- Put_U64LE --
   ---------------

   procedure Put_U64LE (Buf : in out Byte_Array; Len : in out Natural; V : U64)
   is
   begin
      Store_U64LE (Buf, Buf'First + Len, V);
      Len := Len + U64_Len;
   end Put_U64LE;

   ---------------
   -- Get_U32LE --
   ---------------

   procedure Get_U32LE
     (Buf : Byte_Array; Pos : in out Natural; V : out U32; OK : out Boolean)
   is
   begin
      --  C++: if (end - p < 4) return false;
      if not Has_Bytes (Buf, Pos, U32_Len) then
         V  := 0;
         OK := False;
         return;
      end if;
      V   := Read_U32LE (Buf, Pos);
      Pos := Pos + U32_Len;
      OK  := True;
   end Get_U32LE;

   ---------------
   -- Get_U64LE --
   ---------------

   procedure Get_U64LE
     (Buf : Byte_Array; Pos : in out Natural; V : out U64; OK : out Boolean)
   is
   begin
      --  C++: if (end - p < 8) return false;
      if not Has_Bytes (Buf, Pos, U64_Len) then
         V  := 0;
         OK := False;
         return;
      end if;
      V   := Read_U64LE (Buf, Pos);
      Pos := Pos + U64_Len;
      OK  := True;
   end Get_U64LE;

   ------------
   -- Lemmas --
   ------------

   --  read(store(x)) = x. Lane I of the store is (V >> 8I) & FF; shifting
   --  it back left by 8I recovers bits 8I .. 8I+7 of V and nothing else,
   --  so the OR of the four (eight) lanes is V.

   procedure Lemma_Read_Store_U32 (V : U32) is
      B : constant U32_Bytes := To_LE_U32 (V);
   begin
      pragma Assert (B (0) = Byte (V and 16#FF#));
      pragma Assert (B (1) = Byte (Shift_Right (V, 8) and 16#FF#));
      pragma Assert (B (2) = Byte (Shift_Right (V, 16) and 16#FF#));
      pragma Assert (B (3) = Byte (Shift_Right (V, 24) and 16#FF#));
      pragma Assert (U32 (B (0)) = (V and 16#0000_00FF#));
      pragma Assert (Shift_Left (U32 (B (1)), 8) = (V and 16#0000_FF00#));
      pragma Assert (Shift_Left (U32 (B (2)), 16) = (V and 16#00FF_0000#));
      pragma Assert (Shift_Left (U32 (B (3)), 24) = (V and 16#FF00_0000#));
      pragma Assert (Read_U32LE (B, 0) = V);
   end Lemma_Read_Store_U32;

   procedure Lemma_Read_Store_U64 (V : U64) is
      B : constant U64_Bytes := To_LE_U64 (V);
   begin
      pragma Assert (for all I in U64_Index =>
                       B (I) = Byte (Shift_Right (V, 8 * I) and 16#FF#));
      pragma Assert (U64 (B (0)) = (V and 16#0000_0000_0000_00FF#));
      pragma Assert (Shift_Left (U64 (B (1)), 8) = (V and 16#0000_0000_0000_FF00#));
      pragma Assert (Shift_Left (U64 (B (2)), 16) = (V and 16#0000_0000_00FF_0000#));
      pragma Assert (Shift_Left (U64 (B (3)), 24) = (V and 16#0000_0000_FF00_0000#));
      pragma Assert (Shift_Left (U64 (B (4)), 32) = (V and 16#0000_00FF_0000_0000#));
      pragma Assert (Shift_Left (U64 (B (5)), 40) = (V and 16#0000_FF00_0000_0000#));
      pragma Assert (Shift_Left (U64 (B (6)), 48) = (V and 16#00FF_0000_0000_0000#));
      pragma Assert (Shift_Left (U64 (B (7)), 56) = (V and 16#FF00_0000_0000_0000#));
      pragma Assert (Read_U64LE (B, 0) = V);
   end Lemma_Read_Store_U64;

   --  store(read(b)) = b. Lane I of the read is B (I) << 8I; the lanes
   --  occupy disjoint bit ranges, so (X >> 8I) & FF picks lane I back out.

   procedure Lemma_Store_Read_U32 (B : U32_Bytes) is
      X : constant U32 := Read_U32LE (B, 0);
   begin
      pragma Assert (Byte_Of_U32 (X, 0) = B (0));
      pragma Assert (Byte_Of_U32 (X, 1) = B (1));
      pragma Assert (Byte_Of_U32 (X, 2) = B (2));
      pragma Assert (Byte_Of_U32 (X, 3) = B (3));
      pragma Assert (for all I in U32_Index => To_LE_U32 (X) (I) = B (I));
      pragma Assert (To_LE_U32 (X) = B);
   end Lemma_Store_Read_U32;

   procedure Lemma_Store_Read_U64 (B : U64_Bytes) is
      X : constant U64 := Read_U64LE (B, 0);
   begin
      pragma Assert (for all I in U64_Index => Byte_Of_U64 (X, I) = B (I));
      pragma Assert (for all I in U64_Index => To_LE_U64 (X) (I) = B (I));
      pragma Assert (To_LE_U64 (X) = B);
   end Lemma_Store_Read_U64;

   --  get(put(x)) = x. Put then Get on a copy; the Get is made on the
   --  slice that is exactly the Len + N bytes in use, so the law does not
   --  rely on bytes past the end of the "string".

   procedure Lemma_Get_Put_U32 (Buf : Byte_Array; Len : Natural; V : U32) is
      B   : Byte_Array := Buf;
      L   : Natural    := Len;
      Cur : constant Natural := Buf'First + Len;
      Pos : Natural := Cur;
      Got : U32;
      OK  : Boolean;
   begin
      Put_U32LE (B, L, V);
      pragma Assert (L = Len + U32_Len);
      pragma Assert (B = With_LE_U32 (Buf, Cur, V));
      pragma Assert (for all I in U32_Index => B (Cur + I) = Byte_Of_U32 (V, I));
      Get_U32LE (B (Buf'First .. Buf'First + L - 1), Pos, Got, OK);
      pragma Assert (OK);
      pragma Assert (Pos = Buf'First + L);
      Lemma_Read_Store_U32 (V);
      pragma Assert (Read_U32LE (B, Cur) = Read_U32LE (To_LE_U32 (V), 0));
      pragma Assert (Got = Read_U32LE (B, Cur));
      pragma Assert (Got = V);
   end Lemma_Get_Put_U32;

   procedure Lemma_Get_Put_U64 (Buf : Byte_Array; Len : Natural; V : U64) is
      B   : Byte_Array := Buf;
      L   : Natural    := Len;
      Cur : constant Natural := Buf'First + Len;
      Pos : Natural := Cur;
      Got : U64;
      OK  : Boolean;
   begin
      Put_U64LE (B, L, V);
      pragma Assert (L = Len + U64_Len);
      pragma Assert (B = With_LE_U64 (Buf, Cur, V));
      pragma Assert (for all I in U64_Index => B (Cur + I) = Byte_Of_U64 (V, I));
      Get_U64LE (B (Buf'First .. Buf'First + L - 1), Pos, Got, OK);
      pragma Assert (OK);
      pragma Assert (Pos = Buf'First + L);
      Lemma_Read_Store_U64 (V);
      pragma Assert (Read_U64LE (B, Cur) = Read_U64LE (To_LE_U64 (V), 0));
      pragma Assert (Got = Read_U64LE (B, Cur));
      pragma Assert (Got = V);
   end Lemma_Get_Put_U64;

end Kome.Byteorder;
