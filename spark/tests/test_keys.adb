--  Test main for Kome.Keys. The test has these parts:
--    (a) hand vectors for the big-endian packing (bytes 00..1F, all-FF,
--        DEADBEEF lanes), with a source slice that has a non-zero 'First;
--    (b) the two round trips on a grid of words and a grid of byte
--        strings;
--    (c) Kome.Lt against a reference byte-lexicographic loop, on pairs
--        that differ at each position and on equal pairs;
--    (d) the same for Id_Lt, and Id128 injectivity;
--    (e) slice sliding to Key_Bytes / Id_Bytes;
--    (f) on a wrong length, the length precondition of To_Key256 /
--        To_Id128 fails (Assertion_Error under -gnata).
--  Each call also evaluates the Pre/Post of the conversions and of the
--  ghost lemmas at run time (-gnata).
pragma Ada_2022;
with Ada.Text_IO;      use Ada.Text_IO;
with Ada.Command_Line; use Ada.Command_Line;
with Ada.Assertions;
with Kome;             use Kome;
with Kome.Keys;        use Kome.Keys;

procedure Test_Keys with SPARK_Mode => Off is

   Failed : Boolean := False;

   procedure Check (Name : String; Cond : Boolean) is
   begin
      Put_Line ((if Cond then "PASS " else "FAIL ") & Name);
      if not Cond then
         Failed := True;
      end if;
   end Check;

   --  Reference: unsigned byte-lexicographic order by a plain loop.
   function Ref_Lex (A, B : Key_Bytes) return Boolean is
   begin
      for I in Key_Index loop
         if A (I) /= B (I) then
            return A (I) < B (I);
         end if;
      end loop;
      return False;
   end Ref_Lex;

   function Iota return Key_Bytes is
     ([for I in Key_Index => Byte (I)]);

   function Pattern (S : Natural) return Key_Bytes is
     ([for I in Key_Index => Byte ((S * 37 + I * 11 + I * I) mod 256)]);

   --  Reference for identifiers.
   function Ref_Id_Lex (A, B : Id_Bytes) return Boolean is
   begin
      for I in Id_Index loop
         if A (I) /= B (I) then
            return A (I) < B (I);
         end if;
      end loop;
      return False;
   end Ref_Id_Lex;

   function Id_Pattern (S : Natural) return Id_Bytes is
     ([for I in Id_Index => Byte ((S * 53 + I * 13 + I * I * 3) mod 256)]);

   --  (f): call the decoder on an N-byte array (N /= the required length),
   --  and expect the precondition to fail. If the call returns, the test
   --  prints the result, so the compiler cannot optimise the call away.
   procedure Expect_Key_Pre_Failure (N : Natural) is
      B : constant Byte_Array (7 .. 7 + N - 1) := [others => 16#5A#];
      K : Key256;
   begin
      K := To_Key256 (B);
      Put_Line ("  unexpected: To_Key256 returned W0 =" & K.W0'Image);
      Check ("To_Key256 on" & N'Image & " bytes fails its Pre", False);
   exception
      when Ada.Assertions.Assertion_Error =>
         Check ("To_Key256 on" & N'Image & " bytes fails its Pre", True);
      when others =>
         Check ("To_Key256 on" & N'Image & " bytes fails its Pre", False);
   end Expect_Key_Pre_Failure;

   procedure Expect_Id_Pre_Failure (N : Natural) is
      B : constant Byte_Array (3 .. 3 + N - 1) := [others => 16#A5#];
      K : Id128;
   begin
      K := To_Id128 (B);
      Put_Line ("  unexpected: To_Id128 returned W0 =" & K.W0'Image);
      Check ("To_Id128 on" & N'Image & " bytes fails its Pre", False);
   exception
      when Ada.Assertions.Assertion_Error =>
         Check ("To_Id128 on" & N'Image & " bytes fails its Pre", True);
      when others =>
         Check ("To_Id128 on" & N'Image & " bytes fails its Pre", False);
   end Expect_Id_Pre_Failure;

   Bad_Key_Lens : constant array (Positive range <>) of Natural :=
     [0, 1, 16, 31, 33, 64];
   Bad_Id_Lens  : constant array (Positive range <>) of Natural :=
     [0, 1, 15, 17, 32];

   Grid : constant array (Positive range <>) of Word :=
     [0, 1, 16#FF#, 16#100#, 16#FFFF#, 16#1_0000#, 16#FF_FFFF#, 16#100_0000#,
      16#7FFF_FFFF#, 16#8000_0000#, 16#DEAD_BEEF#, 16#0102_0304#,
      16#FFFF_FFFF#];

   Ok : Boolean;

begin
   ----------------------------------------------------------------------
   --  (a) Hand vectors.
   ----------------------------------------------------------------------
   Check ("word_of DE AD BE EF",
          Word_Of (16#DE#, 16#AD#, 16#BE#, 16#EF#) = 16#DEAD_BEEF#);
   Check ("byte_of_word lanes",
          Byte_Of_Word (16#DEAD_BEEF#, 0) = 16#DE#
          and then Byte_Of_Word (16#DEAD_BEEF#, 1) = 16#AD#
          and then Byte_Of_Word (16#DEAD_BEEF#, 2) = 16#BE#
          and then Byte_Of_Word (16#DEAD_BEEF#, 3) = 16#EF#);

   declare
      K : constant Key256 := To_Key256 (Iota);
   begin
      Check ("key 00..1F decodes big-endian",
             K = (16#0001_0203#, 16#0405_0607#, 16#0809_0A0B#, 16#0C0D_0E0F#,
                  16#1011_1213#, 16#1415_1617#, 16#1819_1A1B#, 16#1C1D_1E1F#));
      Check ("key 00..1F encodes back", To_Bytes (K) = Iota);
   end;

   Check ("key all-FF",
          To_Key256 (Key_Bytes'(others => 16#FF#)) = (others => Word'Last)
          and then To_Bytes (Key256'(others => Word'Last)) =
                   Key_Bytes'(others => 16#FF#));
   Check ("key all-00",
          To_Key256 (Key_Bytes'(others => 0)) = (others => 0)
          and then To_Bytes (Key256'(others => 0)) = Key_Bytes'(others => 0));
   Check ("key one in the last byte",
          To_Key256 (Key_Bytes'(31 => 1, others => 0)) =
            (W7 => 1, others => 0));
   Check ("key top bit is byte 0",
          To_Key256 (Key_Bytes'(0 => 16#80#, others => 0)) =
            (W0 => 16#8000_0000#, others => 0));

   declare
      Buf : Byte_Array (100 .. 140) := [others => 16#AA#];
      I16 : constant Id_Bytes := [for I in Id_Index => Byte (16#F0# - I)];
   begin
      for I in Key_Index loop
         Buf (105 + I) := Byte (I);
      end loop;
      Check ("key from slice with 'First = 105",
             To_Key256 (Buf (105 .. 136)) = To_Key256 (Iota));
      Check ("id 00..0F decodes big-endian",
             To_Id128 (Buf (105 .. 120)) =
               (16#0001_0203#, 16#0405_0607#, 16#0809_0A0B#, 16#0C0D_0E0F#));
      Check ("id F0..E1 decodes big-endian",
             To_Id128 (I16) =
               (16#F0EF_EEED#, 16#ECEB_EAE9#, 16#E8E7_E6E5#, 16#E4E3_E2E1#));
      Check ("id encodes back", To_Bytes (To_Id128 (I16)) = I16);
      Lemma_Key_Bytes_Round_Trip (Buf (105 .. 136));
      Lemma_Id_Bytes_Round_Trip (Buf (107 .. 122));
   end;

   ----------------------------------------------------------------------
   --  (b) Round trips on a grid.
   ----------------------------------------------------------------------
   Ok := True;
   for A of Grid loop
      Lemma_Word_Round_Trip (A);
      for B of Grid loop
         declare
            K : constant Key256 := (A, B, B, A, A, A, B, B);
            D : constant Id128  := (B, A, A, B);
         begin
            Lemma_Key_Round_Trip (K);
            Lemma_Id_Round_Trip (D);
            Ok := Ok and then To_Key256 (To_Bytes (K)) = K
              and then To_Id128 (To_Bytes (D)) = D
              and then To_Bytes (K) (0) = Byte_Of_Word (A, 0)
              and then To_Bytes (K) (7) = Byte_Of_Word (B, 3);
         end;
      end loop;
   end loop;
   Check ("words -> bytes -> words on the grid", Ok);

   Ok := True;
   for S in 0 .. 255 loop
      declare
         P : constant Key_Bytes := Pattern (S);
      begin
         Lemma_Key_Bytes_Round_Trip (P);
         Lemma_Id_Bytes_Round_Trip (P (8 .. 23));
         Lemma_Lanes_Round_Trip (P (0), P (1), P (2), P (3));
         Ok := Ok and then To_Bytes (To_Key256 (P)) = P
           and then To_Bytes (To_Id128 (P (8 .. 23))) = P (8 .. 23);
      end;
   end loop;
   Check ("bytes -> words -> bytes on the grid", Ok);

   ----------------------------------------------------------------------
   --  (c) Lt is byte-lexicographic.
   ----------------------------------------------------------------------
   declare
      type Pair is record X, Y : Byte; end record;
      Pairs : constant array (1 .. 6) of Pair :=
        [(0, 1), (1, 0), (16#7F#, 16#80#), (16#80#, 16#7F#), (16#FF#, 0),
         (0, 16#FF#)];
   begin
      Ok := True;
      for S in 0 .. 7 loop
         for P in Key_Index loop
            for Q of Pairs loop
               declare
                  A : Key_Bytes := Pattern (S);
                  B : Key_Bytes := Pattern (S);
               begin
                  A (P) := Q.X;
                  B (P) := Q.Y;
                  --  Bytes after P also differ: they must have no effect.
                  if P < Key_Index'Last then
                     A (P + 1) := 16#FF#;
                     B (P + 1) := 0;
                  end if;
                  Lemma_Lt_Is_Lexicographic (A, B);
                  Lemma_Lt_First_Difference (A, B, P);
                  Lemma_Key_Eq_Is_Bytewise (A, B);
                  Lemma_Lex_Of_Encoding (To_Key256 (A), To_Key256 (B));
                  Ok := Ok
                    and then Lt (To_Key256 (A), To_Key256 (B)) = Ref_Lex (A, B)
                    and then Lt (To_Key256 (A), To_Key256 (B)) = (Q.X < Q.Y)
                    and then Lt (To_Key256 (B), To_Key256 (A)) = (Q.Y < Q.X)
                    and then Lex_Lt (A, B) = Ref_Lex (A, B);
               end;
            end loop;
         end loop;
      end loop;
      Check ("Lt = byte-lexicographic at every position", Ok);
   end;

   Ok := True;
   for S in 0 .. 255 loop
      declare
         A : constant Key_Bytes := Pattern (S);
         B : constant Key_Bytes := Pattern ((S * 7 + 3) mod 256);
      begin
         Lemma_Lt_Is_Lexicographic (A, B);
         Lemma_Lt_Is_Lexicographic (A, A);
         Lemma_Key_Eq_Is_Bytewise (A, A);
         Lemma_Word_Lt_Is_Lexicographic
           (A (4), A (5), A (6), A (7), B (4), B (5), B (6), B (7));
         Ok := Ok
           and then Lt (To_Key256 (A), To_Key256 (B)) = Ref_Lex (A, B)
           and then not Lt (To_Key256 (A), To_Key256 (A))
           and then (Word_Of (A (4), A (5), A (6), A (7))
                       < Word_Of (B (4), B (5), B (6), B (7)))
                    = Ref_Lex ([A (4), A (5), A (6), A (7), others => 0],
                               [B (4), B (5), B (6), B (7), others => 0]);
      end;
   end loop;
   Check ("Lt = byte-lexicographic on pattern pairs; irreflexive", Ok);

   ----------------------------------------------------------------------
   --  (d) Id_Lt is byte-lexicographic, and the Id128 decoder is injective.
   ----------------------------------------------------------------------
   declare
      type Pair is record X, Y : Byte; end record;
      Pairs : constant array (1 .. 6) of Pair :=
        [(0, 1), (1, 0), (16#7F#, 16#80#), (16#80#, 16#7F#), (16#FF#, 0),
         (0, 16#FF#)];
   begin
      Ok := True;
      for S in 0 .. 7 loop
         for P in Id_Index loop
            for Q of Pairs loop
               declare
                  A : Id_Bytes := Id_Pattern (S);
                  B : Id_Bytes := Id_Pattern (S);
               begin
                  A (P) := Q.X;
                  B (P) := Q.Y;
                  if P < Id_Index'Last then
                     A (P + 1) := 16#FF#;
                     B (P + 1) := 0;
                  end if;
                  Lemma_Id_Lt_Is_Lexicographic (A, B);
                  Lemma_Id_Lt_First_Difference (A, B, P);
                  Lemma_Id_Eq_Is_Bytewise (A, B);
                  Lemma_Id_Lex_Of_Encoding (To_Id128 (A), To_Id128 (B));
                  Ok := Ok
                    and then Id_Lt (To_Id128 (A), To_Id128 (B)) = Ref_Id_Lex (A, B)
                    and then Id_Lt (To_Id128 (A), To_Id128 (B)) = (Q.X < Q.Y)
                    and then Id_Lt (To_Id128 (B), To_Id128 (A)) = (Q.Y < Q.X)
                    and then Id_Lex_Lt (A, B) = Ref_Id_Lex (A, B)
                    and then To_Id128 (A) /= To_Id128 (B);
               end;
            end loop;
         end loop;
      end loop;
      Check ("Id_Lt = byte-lexicographic at every position", Ok);
   end;

   Ok := True;
   for S in 0 .. 255 loop
      declare
         A : constant Id_Bytes := Id_Pattern (S);
         B : constant Id_Bytes := Id_Pattern ((S * 11 + 5) mod 256);
      begin
         Lemma_Id_Lt_Is_Lexicographic (A, B);
         Lemma_Id_Lt_Is_Lexicographic (A, A);
         Lemma_Id_Eq_Is_Bytewise (A, A);
         Lemma_Id_Eq_Is_Bytewise (A, B);
         Ok := Ok
           and then Id_Lt (To_Id128 (A), To_Id128 (B)) = Ref_Id_Lex (A, B)
           and then not Id_Lt (To_Id128 (A), To_Id128 (A))
           and then (To_Id128 (A) = To_Id128 (B)) = (A = B)
           and then (Id_Lt (To_Id128 (A), To_Id128 (B))
                     or else Id_Lt (To_Id128 (B), To_Id128 (A))
                     or else A = B);
      end;
   end loop;
   Check ("Id_Lt = byte-lexicographic on pattern pairs; irreflexive; total",
          Ok);

   Ok := True;
   for A of Grid loop
      for B of Grid loop
         declare
            D1 : constant Id128 := (A, B, A, B);
            D2 : constant Id128 := (A, B, B, A);
         begin
            Lemma_Id_Lex_Of_Encoding (D1, D2);
            Ok := Ok
              and then Id_Lt (D1, D2) = Ref_Id_Lex (To_Bytes (D1), To_Bytes (D2))
              and then Id_Lt (D1, D2) = (D1 /= D2 and then A < B);
         end;
      end loop;
   end loop;
   Check ("Id_Lt = byte-lexicographic on encodings of word grid", Ok);

   Check ("Id_Lt hand vectors",
          Id_Lt ((0, 0, 0, 0), (0, 0, 0, 1))
          and then not Id_Lt ((0, 0, 0, 1), (0, 0, 0, 1))
          and then Id_Lt ((0, Word'Last, Word'Last, Word'Last), (1, 0, 0, 0))
          and then not Id_Lt ((16#8000_0000#, 0, 0, 0),
                              (16#7FFF_FFFF#, Word'Last, Word'Last, Word'Last)));

   ----------------------------------------------------------------------
   --  (e) Slice sliding.
   ----------------------------------------------------------------------
   declare
      Buf : Byte_Array (200 .. 299);
   begin
      for I in Buf'Range loop
         Buf (I) := Byte ((I * 29 + 7) mod 256);
      end loop;
      Ok := True;
      for F in 200 .. 268 loop
         Lemma_Key_Slide (Buf (F .. F + 31));
         Ok := Ok
           and then To_Key256 (Key_Bytes (Buf (F .. F + 31)))
                    = To_Key256 (Buf (F .. F + 31))
           and then Key_Bytes (Buf (F .. F + 31)) (0) = Buf (F)
           and then Key_Bytes (Buf (F .. F + 31)) (31) = Buf (F + 31);
      end loop;
      for F in 200 .. 284 loop
         Lemma_Id_Slide (Buf (F .. F + 15));
         Ok := Ok
           and then To_Id128 (Id_Bytes (Buf (F .. F + 15)))
                    = To_Id128 (Buf (F .. F + 15))
           and then Id_Bytes (Buf (F .. F + 15)) (0) = Buf (F)
           and then Id_Bytes (Buf (F .. F + 15)) (15) = Buf (F + 15);
      end loop;
      Check ("slice slides to Key_Bytes / Id_Bytes, same key", Ok);
   end;

   ----------------------------------------------------------------------
   --  (f) Wrong length: the precondition fails (Assertion_Error).
   ----------------------------------------------------------------------
   for N of Bad_Key_Lens loop
      Expect_Key_Pre_Failure (N);
   end loop;
   for N of Bad_Id_Lens loop
      Expect_Id_Pre_Failure (N);
   end loop;

   if Failed then
      Set_Exit_Status (Failure);
   end if;
end Test_Keys;
