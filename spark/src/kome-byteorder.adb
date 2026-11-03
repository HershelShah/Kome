pragma Ada_2022;
package body Kome.Byteorder with SPARK_Mode is

   --  read (encode (V)) = V. Lane I of the encoding, shifted back into
   --  place, is V masked to bits 8I .. 8I + 7. The OR of the lanes is V.
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

   --  encode (read (B)) = B. Lane I of the read is B (I) << 8I. The lanes
   --  occupy disjoint bit ranges, so (X >> 8I) & FF extracts lane I.
   procedure Lemma_Store_Read_U64 (B : U64_Bytes) is
      X : constant U64 := Read_U64LE (B, 0);
   begin
      pragma Assert (for all I in U64_Index => Byte_Of_U64 (X, I) = B (I));
      pragma Assert (for all I in U64_Index => To_LE_U64 (X) (I) = B (I));
      pragma Assert (To_LE_U64 (X) = B);
   end Lemma_Store_Read_U64;

end Kome.Byteorder;
