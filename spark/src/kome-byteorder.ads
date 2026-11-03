--  Kome.Byteorder: the little-endian encoding of a 64-bit word. This is the
--  only little-endian quantity in Kome (the accumulator limbs, DESIGN.md
--  §8, D7).
--
--  All bit-level code uses the Shift_Left/Shift_Right intrinsics and
--  "and"/"or". Thus gnatprove maps the contracts to bit-vector operations
--  (bvlshr/bvshl/bvand/bvor). A `V / 2 ** (8 * I)` view would give an
--  axiomatized power function with a non-literal exponent instead.
--
--  Nothing here touches a file, a clock or global state. Thus each
--  subprogram has Global => null (implied by Pure).
pragma Ada_2022;
package Kome.Byteorder with SPARK_Mode, Pure is

   U64_Len : constant := 8;

   subtype U64_Index is Natural range 0 .. U64_Len - 1;
   subtype U64_Bytes is Byte_Array (U64_Index);

   --  Shift intrinsics on U64, with the same profile as those in Interfaces
   --  (SPARK models them as bit-vector shifts).
   function Shift_Right (Value : U64; Amount : Natural) return U64
     with Import, Convention => Intrinsic, Global => null;
   function Shift_Left (Value : U64; Amount : Natural) return U64
     with Import, Convention => Intrinsic, Global => null;

   --  Byte I of the little-endian encoding of V.
   function Byte_Of_U64 (V : U64; I : U64_Index) return Byte is
     (Byte (Shift_Right (V, 8 * I) and 16#FF#));

   --  The eight-byte encoding of V.
   function To_LE_U64 (V : U64) return U64_Bytes is
     ([for I in U64_Index => Byte_Of_U64 (V, I)]);

   --  The word whose encoding is Buf (Pos .. Pos + 7).
   function Read_U64LE (Buf : Byte_Array; Pos : Natural) return U64 is
     (U64 (Buf (Pos))
      or Shift_Left (U64 (Buf (Pos + 1)), 8)
      or Shift_Left (U64 (Buf (Pos + 2)), 16)
      or Shift_Left (U64 (Buf (Pos + 3)), 24)
      or Shift_Left (U64 (Buf (Pos + 4)), 32)
      or Shift_Left (U64 (Buf (Pos + 5)), 40)
      or Shift_Left (U64 (Buf (Pos + 6)), 48)
      or Shift_Left (U64 (Buf (Pos + 7)), 56))
     with
       Global => null,
       Pre    => Pos in Buf'Range and then Buf'Last - Pos >= U64_Len - 1,
       Post   => (for all I in U64_Index =>
                    Byte_Of_U64 (Read_U64LE'Result, I) = Buf (Pos + I));

   --  The two round-trip laws. The bodies assert the per-byte equalities
   --  that lead to each law. Thus gnatprove works from bit-vector facts one
   --  byte at a time, and -gnata evaluates the assertions on the values that
   --  the tests supply.

   --  read (encode (V)) = V: the encoding is injective.
   procedure Lemma_Read_Store_U64 (V : U64)
     with Ghost, Global => null,
          Post => Read_U64LE (To_LE_U64 (V), 0) = V;

   --  encode (read (B)) = B: each group of eight bytes decodes to exactly
   --  one word.
   procedure Lemma_Store_Read_U64 (B : U64_Bytes)
     with Ghost, Global => null,
          Post => To_LE_U64 (Read_U64LE (B, 0)) = B;

end Kome.Byteorder;
