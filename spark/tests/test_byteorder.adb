--  Test main for Kome.Byteorder: every vector in vectors/byteorder.txt is
--  checked byte for byte against To_LE_U64 and Read_U64LE (also at a
--  non-zero offset inside a larger buffer), against an arithmetic reference
--  (divide and sum instead of shift and or), and through both round-trip
--  lemmas, whose assertions and Posts run under -gnata.
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

   --  Arithmetic references: byte I is V / 2**(8I) mod 256, and the read
   --  is the sum of the shifted bytes (the lanes are disjoint).
   function Ref_Byte (V : U64; I : U64_Index) return Byte is
     (Byte ((V / (2 ** (8 * I))) mod 256));

   function Ref_Read (B : Byte_Array; Pos : Natural) return U64 is
     (U64 (B (Pos)) + U64 (B (Pos + 1)) * 2 ** 8
      + U64 (B (Pos + 2)) * 2 ** 16 + U64 (B (Pos + 3)) * 2 ** 24
      + U64 (B (Pos + 4)) * 2 ** 32 + U64 (B (Pos + 5)) * 2 ** 40
      + U64 (B (Pos + 6)) * 2 ** 48 + U64 (B (Pos + 7)) * 2 ** 56);

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

   function Hex_Bytes (S : String) return U64_Bytes is
   begin
      return R : U64_Bytes do
         for I in R'Range loop
            R (I) := Nibble (S (S'First + 2 * I)) * 16
                     + Nibble (S (S'First + 2 * I + 1));
         end loop;
      end return;
   end Hex_Bytes;

   F       : File_Type;
   N       : Natural := 0;
   Enc_OK  : Boolean := True;
   Read_OK : Boolean := True;
   Off_OK  : Boolean := True;
   Ref_OK  : Boolean := True;
begin
   Open (F, In_File, "vectors/byteorder.txt");
   while not End_Of_File (F) loop
      declare
         Line : constant String := Get_Line (F);
      begin
         if Line'Length > 0 and then Line (Line'First) /= '#' then
            declare
               V   : constant U64 :=
                 Hex_U64 (Line (Line'First .. Line'First + 15));
               B   : constant U64_Bytes :=
                 Hex_Bytes (Line (Line'First + 17 .. Line'First + 32));
               --  The encoding placed at offset 5 of a buffer starting at 3.
               Buf : Byte_Array (3 .. 20) := [others => 16#A5#];
            begin
               N := N + 1;
               Buf (8 .. 15) := B;
               Enc_OK  := Enc_OK and then To_LE_U64 (V) = B;
               Read_OK := Read_OK and then Read_U64LE (B, 0) = V;
               Off_OK  := Off_OK and then Read_U64LE (Buf, 8) = V;
               Ref_OK  := Ref_OK
                 and then (for all I in U64_Index =>
                             Byte_Of_U64 (V, I) = Ref_Byte (V, I))
                 and then Ref_Read (B, 0) = V;
               Lemma_Read_Store_U64 (V);
               Lemma_Store_Read_U64 (B);
            end;
         end if;
      end;
   end loop;
   Close (F);

   Check ("vectors read (" & N'Image & ")", N >= 270);
   Check ("To_LE_U64 equals every vector's encoding", Enc_OK);
   Check ("Read_U64LE decodes every vector", Read_OK);
   Check ("Read_U64LE at a non-zero offset of a buffer not starting at 0",
          Off_OK);
   Check ("shift views agree with divide/sum arithmetic", Ref_OK);
   Check ("both round-trip lemmas held on every vector (-gnata)", True);

   if Failed then
      Set_Exit_Status (Failure);
   end if;
end Test_Byteorder;
