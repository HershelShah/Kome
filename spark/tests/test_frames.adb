--  Test main for Kome.Frames. Frame_Is is the opaque form of "Frame is
--  the record X of the collection Cid" that Kome.Store's invariant uses.
--  The test checks, on a signed DEL and a signed PUT:
--    (a) Frame_Is holds for the frame's own header and fails for another
--        header and for another collection (Lemma_Frame_Is_Def is
--        evaluated with each call);
--    (b) a copy of the frame at other bounds holds the same record
--        (Lemma_Frame_Is_Congruent), and a copy with one byte changed
--        does not;
--    (c) bytes that are not a record frame hold no record.
pragma Ada_2022;
with Ada.Text_IO;      use Ada.Text_IO;
with Ada.Command_Line; use Ada.Command_Line;
with Kome;             use Kome;
with Kome.Headers;     use Kome.Headers;
with Kome.Crypto;
with Kome.Records;     use Kome.Records;
with Kome.Store;
with Kome.Frames;      use Kome.Frames;

procedure Test_Frames with SPARK_Mode => Off is

   Failed : Boolean := False;

   procedure Check (Name : String; Cond : Boolean) is
   begin
      Put_Line ((if Cond then "PASS " else "FAIL ") & Name);
      if not Cond then
         Failed := True;
      end if;
   end Check;

   function Fill (Len : Natural; Seed : Natural) return Byte_Array is
     ([for I in 0 .. Len - 1 => Byte ((Seed + 7 * I) mod 256)]);

   --  Frame_Is, with its definition evaluated beside it.
   function Holds (Frame : Byte_Array; Cid : Hash256; X : Header) return Boolean is
   begin
      Lemma_Frame_Is_Def (Frame, Cid, X);
      return Frame_Is (Frame, Cid, X);
   end Holds;

   --  A copy of Frame at bounds starting at First.
   function Moved (Frame : Byte_Array; First : Natural) return Byte_Array is
      C : Byte_Array (First .. First + Frame'Length - 1);
   begin
      for J in Frame'Range loop
         C (J - Frame'First + First) := Frame (J);
      end loop;
      return C;
   end Moved;

   SK     : Kome.Crypto.Secret_Key;
   PK     : Pubkey;
   Root_PK : constant Pubkey := Pubkey (Fill (Pubkey_Len, 3));
   Cid_A  : Hash256;
   Cid_B  : Hash256;

begin
   Kome.Crypto.Key_Pair (Kome.Crypto.Seed (Fill (Kome.Crypto.Seed_Len, 1)), SK, PK);
   Cid_A := Cid_Of (Root_PK, Salt (Fill (Salt_Len, 90)), Del_TTL_Min);
   Cid_B := Cid_Of (Root_PK, Salt (Fill (Salt_Len, 91)), Del_TTL_Min);

   declare
      D : Del_Record := Make_Del (Cid_A, Ent_Id (Fill (Ent_Len, 5)), 1_000, 1, PK);
   begin
      Sign (Cid_A, D, SK);
      declare
         F  : constant Byte_Array := Encode (D);
         H  : constant Header := Kome.Store.Header_Of (Cid_A, F);
         H2 : Header := H;
         M  : constant Byte_Array := Moved (F, 1_000);
         X  : Byte_Array := M;
      begin
         H2.V.Seq := 2;
         Check ("(a) a DEL holds its own header", Holds (F, Cid_A, H));
         Check ("(a) a DEL does not hold another header", not Holds (F, Cid_A, H2));
         Check ("(a) under another cid the header differs",
                not Holds (F, Cid_B, H));
         Lemma_Frame_Is_Congruent (Cid_A, H, F, M);
         Check ("(b) a moved DEL holds the same record", Holds (M, Cid_A, H));
         X (X'First + 20) := X (X'First + 20) xor 1;
         Check ("(b) a changed byte (t) changes the record", not Holds (X, Cid_A, H));
         Check ("(c) the empty string holds no record",
                not Holds (Byte_Array'(1 .. 0 => 0), Cid_A, H));
         Check ("(c) a truncated frame holds no record",
                not Holds (F (F'First .. F'Last - 1), Cid_A, H));
      end;
   end;

   declare
      P : Put_Record :=
        Make_Put (Cid_A, Ent_Id (Fill (Ent_Len, 6)), [16#61#, 16#62#], 2_000, 3, PK,
                  Fill (40, 9));
   begin
      Sign (Cid_A, P, SK);
      declare
         F : constant Byte_Array := Encode (P);
         H : constant Header := Kome.Store.Header_Of (Cid_A, F);
         M : constant Byte_Array := Moved (F, 7);
      begin
         Check ("(a) a PUT holds its own header", Holds (F, Cid_A, H));
         Lemma_Frame_Is_Congruent (Cid_A, H, F, M);
         Check ("(b) a moved PUT holds the same record", Holds (M, Cid_A, H));
      end;
   end;

   if Failed then
      Set_Exit_Status (Failure);
   end if;
end Test_Frames;
