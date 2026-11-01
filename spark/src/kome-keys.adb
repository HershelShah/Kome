--  Body of Kome.Keys. The conversions are their definitions plus the
--  per-word lemma calls that discharge the round-trip conjuncts of their
--  Posts; the lemma bodies give the prover the quotient / remainder
--  decomposition one division by 256 at a time.
pragma Ada_2022;
package body Kome.Keys with SPARK_Mode is

   -------------
   -- Word_Of --
   -------------

   function Word_Of (B0, B1, B2, B3 : Byte) return Word is
     (Word (B0) * 2 ** 24 + Word (B1) * 2 ** 16
      + Word (B2) * 2 ** 8 + Word (B3));

   ------------------
   -- Byte_Of_Word --
   ------------------

   function Byte_Of_Word (W : Word; J : Lane) return Byte is
     (case J is
         when 0 => Byte (W / 256 / 256 / 256),
         when 1 => Byte (W / 256 / 256 mod 256),
         when 2 => Byte (W / 256 mod 256),
         when 3 => Byte (W mod 256));

   ---------------------------
   -- Lemma_Word_Round_Trip --
   ---------------------------

   procedure Lemma_Word_Round_Trip (W : Word) is
      Q1 : constant Word := W / 256;
      Q2 : constant Word := Q1 / 256;
      Q3 : constant Word := Q2 / 256;
   begin
      pragma Assert (W = Q1 * 256 + W mod 256);
      pragma Assert (Q1 = Q2 * 256 + Q1 mod 256);
      pragma Assert (Q2 = Q3 * 256 + Q2 mod 256);
      pragma Assert (Q3 <= 255);
      pragma Assert (Word (Byte_Of_Word (W, 0)) = Q3);
      pragma Assert (Word (Byte_Of_Word (W, 1)) = Q2 mod 256);
      pragma Assert (Word (Byte_Of_Word (W, 2)) = Q1 mod 256);
      pragma Assert (Word (Byte_Of_Word (W, 3)) = W mod 256);
   end Lemma_Word_Round_Trip;

   ----------------------------
   -- Lemma_Lanes_Round_Trip --
   ----------------------------

   procedure Lemma_Lanes_Round_Trip (B0, B1, B2, B3 : Byte) is
      W : constant Word := Word_Of (B0, B1, B2, B3);
   begin
      pragma Assert (W mod 256 = Word (B3));
      pragma Assert (W / 256 = Word (B0) * 2 ** 16 + Word (B1) * 2 ** 8 + Word (B2));
      pragma Assert (W / 256 mod 256 = Word (B2));
      pragma Assert (W / 256 / 256 = Word (B0) * 2 ** 8 + Word (B1));
      pragma Assert (W / 256 / 256 mod 256 = Word (B1));
      pragma Assert (W / 256 / 256 / 256 = Word (B0));
   end Lemma_Lanes_Round_Trip;

   ------------------------------------
   -- Lemma_Word_Lt_Is_Lexicographic --
   ------------------------------------

   procedure Lemma_Word_Lt_Is_Lexicographic (A0, A1, A2, A3, B0, B1, B2, B3 : Byte) is
      --  Low parts: WA = A0 * 2**24 + LA1, LA1 = A1 * 2**16 + LA2, ...
      LA2 : constant Word := Word (A2) * 2 ** 8 + Word (A3);
      LB2 : constant Word := Word (B2) * 2 ** 8 + Word (B3);
      LA1 : constant Word := Word (A1) * 2 ** 16 + LA2;
      LB1 : constant Word := Word (B1) * 2 ** 16 + LB2;
      WA  : constant Word := Word_Of (A0, A1, A2, A3);
      WB  : constant Word := Word_Of (B0, B1, B2, B3);
   begin
      --  Byte order (bit-vector) is integer order on the values.
      pragma Assert ((A0 < B0) = (Word (A0) < Word (B0)));
      pragma Assert ((A1 < B1) = (Word (A1) < Word (B1)));
      pragma Assert ((A2 < B2) = (Word (A2) < Word (B2)));
      pragma Assert ((A3 < B3) = (Word (A3) < Word (B3)));
      pragma Assert ((A0 = B0) = (Word (A0) = Word (B0)));
      pragma Assert ((A1 = B1) = (Word (A1) = Word (B1)));
      pragma Assert ((A2 = B2) = (Word (A2) = Word (B2)));
      pragma Assert ((A3 = B3) = (Word (A3) = Word (B3)));
      --  Place-value decomposition, one lane at a time.
      pragma Assert (LA2 < 2 ** 16 and then LB2 < 2 ** 16);
      pragma Assert (LA1 < 2 ** 24 and then LB1 < 2 ** 24);
      pragma Assert (WA = Word (A0) * 2 ** 24 + LA1);
      pragma Assert (WB = Word (B0) * 2 ** 24 + LB1);
      pragma Assert ((LA2 < LB2) =
        (Word (A2) < Word (B2)
         or else (Word (A2) = Word (B2) and then Word (A3) < Word (B3))));
      pragma Assert ((LA2 = LB2) =
        (Word (A2) = Word (B2) and then Word (A3) = Word (B3)));
      pragma Assert ((LA1 < LB1) =
        (Word (A1) < Word (B1)
         or else (Word (A1) = Word (B1) and then LA2 < LB2)));
      pragma Assert ((LA1 = LB1) =
        (Word (A1) = Word (B1) and then LA2 = LB2));
      pragma Assert ((WA < WB) =
        (Word (A0) < Word (B0)
         or else (Word (A0) = Word (B0) and then LA1 < LB1)));
      pragma Assert ((WA = WB) =
        (Word (A0) = Word (B0) and then LA1 = LB1));
   end Lemma_Word_Lt_Is_Lexicographic;

   ---------------
   -- To_Key256 --
   ---------------

   function To_Key256 (B : Byte_Array) return Key256 is
      R : constant Key256 :=
        (
        W0 => Word_Of (B (B'First), B (B'First + 1), B (B'First + 2), B (B'First + 3)),
        W1 => Word_Of (B (B'First + 4), B (B'First + 5), B (B'First + 6), B (B'First + 7)),
        W2 => Word_Of (B (B'First + 8), B (B'First + 9), B (B'First + 10), B (B'First + 11)),
        W3 => Word_Of (B (B'First + 12), B (B'First + 13), B (B'First + 14), B (B'First + 15)),
        W4 => Word_Of (B (B'First + 16), B (B'First + 17), B (B'First + 18), B (B'First + 19)),
        W5 => Word_Of (B (B'First + 20), B (B'First + 21), B (B'First + 22), B (B'First + 23)),
        W6 => Word_Of (B (B'First + 24), B (B'First + 25), B (B'First + 26), B (B'First + 27)),
        W7 => Word_Of (B (B'First + 28), B (B'First + 29), B (B'First + 30), B (B'First + 31)));
   begin
      Lemma_Lanes_Round_Trip (B (B'First), B (B'First + 1), B (B'First + 2), B (B'First + 3));
      Lemma_Lanes_Round_Trip (B (B'First + 4), B (B'First + 5), B (B'First + 6), B (B'First + 7));
      Lemma_Lanes_Round_Trip (B (B'First + 8), B (B'First + 9), B (B'First + 10), B (B'First + 11));
      Lemma_Lanes_Round_Trip (B (B'First + 12), B (B'First + 13), B (B'First + 14), B (B'First + 15));
      Lemma_Lanes_Round_Trip (B (B'First + 16), B (B'First + 17), B (B'First + 18), B (B'First + 19));
      Lemma_Lanes_Round_Trip (B (B'First + 20), B (B'First + 21), B (B'First + 22), B (B'First + 23));
      Lemma_Lanes_Round_Trip (B (B'First + 24), B (B'First + 25), B (B'First + 26), B (B'First + 27));
      Lemma_Lanes_Round_Trip (B (B'First + 28), B (B'First + 29), B (B'First + 30), B (B'First + 31));
      pragma Assert (Byte_At (R, 0) = B (B'First + 0));
      pragma Assert (Byte_At (R, 1) = B (B'First + 1));
      pragma Assert (Byte_At (R, 2) = B (B'First + 2));
      pragma Assert (Byte_At (R, 3) = B (B'First + 3));
      pragma Assert (Byte_At (R, 4) = B (B'First + 4));
      pragma Assert (Byte_At (R, 5) = B (B'First + 5));
      pragma Assert (Byte_At (R, 6) = B (B'First + 6));
      pragma Assert (Byte_At (R, 7) = B (B'First + 7));
      pragma Assert (Byte_At (R, 8) = B (B'First + 8));
      pragma Assert (Byte_At (R, 9) = B (B'First + 9));
      pragma Assert (Byte_At (R, 10) = B (B'First + 10));
      pragma Assert (Byte_At (R, 11) = B (B'First + 11));
      pragma Assert (Byte_At (R, 12) = B (B'First + 12));
      pragma Assert (Byte_At (R, 13) = B (B'First + 13));
      pragma Assert (Byte_At (R, 14) = B (B'First + 14));
      pragma Assert (Byte_At (R, 15) = B (B'First + 15));
      pragma Assert (Byte_At (R, 16) = B (B'First + 16));
      pragma Assert (Byte_At (R, 17) = B (B'First + 17));
      pragma Assert (Byte_At (R, 18) = B (B'First + 18));
      pragma Assert (Byte_At (R, 19) = B (B'First + 19));
      pragma Assert (Byte_At (R, 20) = B (B'First + 20));
      pragma Assert (Byte_At (R, 21) = B (B'First + 21));
      pragma Assert (Byte_At (R, 22) = B (B'First + 22));
      pragma Assert (Byte_At (R, 23) = B (B'First + 23));
      pragma Assert (Byte_At (R, 24) = B (B'First + 24));
      pragma Assert (Byte_At (R, 25) = B (B'First + 25));
      pragma Assert (Byte_At (R, 26) = B (B'First + 26));
      pragma Assert (Byte_At (R, 27) = B (B'First + 27));
      pragma Assert (Byte_At (R, 28) = B (B'First + 28));
      pragma Assert (Byte_At (R, 29) = B (B'First + 29));
      pragma Assert (Byte_At (R, 30) = B (B'First + 30));
      pragma Assert (Byte_At (R, 31) = B (B'First + 31));
      return R;
   end To_Key256;

   --------------
   -- To_Bytes --
   --------------

   function To_Bytes (K : Key256) return Key_Bytes is
      R : constant Key_Bytes :=
      [
       Byte_Of_Word (K.W0, 0), Byte_Of_Word (K.W0, 1), Byte_Of_Word (K.W0, 2), Byte_Of_Word (K.W0, 3),
       Byte_Of_Word (K.W1, 0), Byte_Of_Word (K.W1, 1), Byte_Of_Word (K.W1, 2), Byte_Of_Word (K.W1, 3),
       Byte_Of_Word (K.W2, 0), Byte_Of_Word (K.W2, 1), Byte_Of_Word (K.W2, 2), Byte_Of_Word (K.W2, 3),
       Byte_Of_Word (K.W3, 0), Byte_Of_Word (K.W3, 1), Byte_Of_Word (K.W3, 2), Byte_Of_Word (K.W3, 3),
       Byte_Of_Word (K.W4, 0), Byte_Of_Word (K.W4, 1), Byte_Of_Word (K.W4, 2), Byte_Of_Word (K.W4, 3),
       Byte_Of_Word (K.W5, 0), Byte_Of_Word (K.W5, 1), Byte_Of_Word (K.W5, 2), Byte_Of_Word (K.W5, 3),
       Byte_Of_Word (K.W6, 0), Byte_Of_Word (K.W6, 1), Byte_Of_Word (K.W6, 2), Byte_Of_Word (K.W6, 3),
       Byte_Of_Word (K.W7, 0), Byte_Of_Word (K.W7, 1), Byte_Of_Word (K.W7, 2), Byte_Of_Word (K.W7, 3)];
   begin
      Lemma_Word_Round_Trip (K.W0);
      Lemma_Word_Round_Trip (K.W1);
      Lemma_Word_Round_Trip (K.W2);
      Lemma_Word_Round_Trip (K.W3);
      Lemma_Word_Round_Trip (K.W4);
      Lemma_Word_Round_Trip (K.W5);
      Lemma_Word_Round_Trip (K.W6);
      Lemma_Word_Round_Trip (K.W7);
      declare
         D : constant Key256 := To_Key256 (R) with Ghost;
      begin
         pragma Assert (D = To_Key256 (R));
         pragma Assert (D.W0 = Word_Of (R (0), R (1), R (2), R (3)));
         pragma Assert (D.W0 = K.W0);
         pragma Assert (D.W1 = Word_Of (R (4), R (5), R (6), R (7)));
         pragma Assert (D.W1 = K.W1);
         pragma Assert (D.W2 = Word_Of (R (8), R (9), R (10), R (11)));
         pragma Assert (D.W2 = K.W2);
         pragma Assert (D.W3 = Word_Of (R (12), R (13), R (14), R (15)));
         pragma Assert (D.W3 = K.W3);
         pragma Assert (D.W4 = Word_Of (R (16), R (17), R (18), R (19)));
         pragma Assert (D.W4 = K.W4);
         pragma Assert (D.W5 = Word_Of (R (20), R (21), R (22), R (23)));
         pragma Assert (D.W5 = K.W5);
         pragma Assert (D.W6 = Word_Of (R (24), R (25), R (26), R (27)));
         pragma Assert (D.W6 = K.W6);
         pragma Assert (D.W7 = Word_Of (R (28), R (29), R (30), R (31)));
         pragma Assert (D.W7 = K.W7);
      end;
      return R;
   end To_Bytes;

   --------------
   -- To_Id128 --
   --------------

   function To_Id128 (B : Byte_Array) return Id128 is
      R : constant Id128 :=
        (
        W0 => Word_Of (B (B'First), B (B'First + 1), B (B'First + 2), B (B'First + 3)),
        W1 => Word_Of (B (B'First + 4), B (B'First + 5), B (B'First + 6), B (B'First + 7)),
        W2 => Word_Of (B (B'First + 8), B (B'First + 9), B (B'First + 10), B (B'First + 11)),
        W3 => Word_Of (B (B'First + 12), B (B'First + 13), B (B'First + 14), B (B'First + 15)));
   begin
      Lemma_Lanes_Round_Trip (B (B'First), B (B'First + 1), B (B'First + 2), B (B'First + 3));
      Lemma_Lanes_Round_Trip (B (B'First + 4), B (B'First + 5), B (B'First + 6), B (B'First + 7));
      Lemma_Lanes_Round_Trip (B (B'First + 8), B (B'First + 9), B (B'First + 10), B (B'First + 11));
      Lemma_Lanes_Round_Trip (B (B'First + 12), B (B'First + 13), B (B'First + 14), B (B'First + 15));
      pragma Assert (Byte_At (R, 0) = B (B'First + 0));
      pragma Assert (Byte_At (R, 1) = B (B'First + 1));
      pragma Assert (Byte_At (R, 2) = B (B'First + 2));
      pragma Assert (Byte_At (R, 3) = B (B'First + 3));
      pragma Assert (Byte_At (R, 4) = B (B'First + 4));
      pragma Assert (Byte_At (R, 5) = B (B'First + 5));
      pragma Assert (Byte_At (R, 6) = B (B'First + 6));
      pragma Assert (Byte_At (R, 7) = B (B'First + 7));
      pragma Assert (Byte_At (R, 8) = B (B'First + 8));
      pragma Assert (Byte_At (R, 9) = B (B'First + 9));
      pragma Assert (Byte_At (R, 10) = B (B'First + 10));
      pragma Assert (Byte_At (R, 11) = B (B'First + 11));
      pragma Assert (Byte_At (R, 12) = B (B'First + 12));
      pragma Assert (Byte_At (R, 13) = B (B'First + 13));
      pragma Assert (Byte_At (R, 14) = B (B'First + 14));
      pragma Assert (Byte_At (R, 15) = B (B'First + 15));
      return R;
   end To_Id128;

   --------------
   -- To_Bytes --
   --------------

   function To_Bytes (K : Id128) return Id_Bytes is
      R : constant Id_Bytes :=
      [
       Byte_Of_Word (K.W0, 0), Byte_Of_Word (K.W0, 1), Byte_Of_Word (K.W0, 2), Byte_Of_Word (K.W0, 3),
       Byte_Of_Word (K.W1, 0), Byte_Of_Word (K.W1, 1), Byte_Of_Word (K.W1, 2), Byte_Of_Word (K.W1, 3),
       Byte_Of_Word (K.W2, 0), Byte_Of_Word (K.W2, 1), Byte_Of_Word (K.W2, 2), Byte_Of_Word (K.W2, 3),
       Byte_Of_Word (K.W3, 0), Byte_Of_Word (K.W3, 1), Byte_Of_Word (K.W3, 2), Byte_Of_Word (K.W3, 3)];
   begin
      Lemma_Word_Round_Trip (K.W0);
      Lemma_Word_Round_Trip (K.W1);
      Lemma_Word_Round_Trip (K.W2);
      Lemma_Word_Round_Trip (K.W3);
      declare
         D : constant Id128 := To_Id128 (R) with Ghost;
      begin
         pragma Assert (D = To_Id128 (R));
         pragma Assert (D.W0 = Word_Of (R (0), R (1), R (2), R (3)));
         pragma Assert (D.W0 = K.W0);
         pragma Assert (D.W1 = Word_Of (R (4), R (5), R (6), R (7)));
         pragma Assert (D.W1 = K.W1);
         pragma Assert (D.W2 = Word_Of (R (8), R (9), R (10), R (11)));
         pragma Assert (D.W2 = K.W2);
         pragma Assert (D.W3 = Word_Of (R (12), R (13), R (14), R (15)));
         pragma Assert (D.W3 = K.W3);
      end;
      return R;
   end To_Bytes;

   ------------------------------
   -- Round-trip lemmas (laws) --
   ------------------------------

   procedure Lemma_Key_Round_Trip (K : Key256) is null;
   procedure Lemma_Key_Bytes_Round_Trip (B : Byte_Array) is null;
   procedure Lemma_Id_Round_Trip (K : Id128) is null;
   procedure Lemma_Id_Bytes_Round_Trip (B : Byte_Array) is null;

   ------------------------------
   -- Lemma_Key_Eq_Is_Bytewise --
   ------------------------------

   procedure Lemma_Key_Eq_Is_Bytewise (A, B : Key_Bytes) is
   begin
      if To_Key256 (A) = To_Key256 (B) then
         pragma Assert
           (for all I in Key_Index =>
              A (I) = Byte_At (To_Key256 (A), I)
              and then B (I) = Byte_At (To_Key256 (B), I));
         pragma Assert (for all I in Key_Index => A (I) = B (I));
         pragma Assert (A = B);
      end if;
      if A = B then
         pragma Assert (for all I in Key_Index => A (I) = B (I));
         pragma Assert (To_Key256 (A).W0 = To_Key256 (B).W0);
         pragma Assert (To_Key256 (A).W1 = To_Key256 (B).W1);
         pragma Assert (To_Key256 (A).W2 = To_Key256 (B).W2);
         pragma Assert (To_Key256 (A).W3 = To_Key256 (B).W3);
         pragma Assert (To_Key256 (A).W4 = To_Key256 (B).W4);
         pragma Assert (To_Key256 (A).W5 = To_Key256 (B).W5);
         pragma Assert (To_Key256 (A).W6 = To_Key256 (B).W6);
         pragma Assert (To_Key256 (A).W7 = To_Key256 (B).W7);
      end if;
   end Lemma_Key_Eq_Is_Bytewise;

   -------------------------------
   -- Lemma_Lt_Is_Lexicographic --
   -------------------------------

   --  Suffix_K (A, B): the tail of Lex_Lt that starts at byte 4K. Lex_Lt
   --  is Suffix_0 by unfolding, and each Suffix_K is one word's four-byte
   --  chain wrapped around Suffix_K+1, which the word lemma turns into
   --  one word comparison. Ghost and local to this body.
   function Suffix_7 (A, B : Key_Bytes) return Boolean is
      (A (28) < B (28) or else (A (28) = B (28) and then
       (A (29) < B (29) or else (A (29) = B (29) and then
       (A (30) < B (30) or else (A (30) = B (30) and then
       (A (31) < B (31))))))))
     with Ghost;

   function Suffix_6 (A, B : Key_Bytes) return Boolean is
      (A (24) < B (24) or else (A (24) = B (24) and then
       (A (25) < B (25) or else (A (25) = B (25) and then
       (A (26) < B (26) or else (A (26) = B (26) and then
       (A (27) < B (27) or else (A (27) = B (27) and then
       Suffix_7 (A, B)))))))))
     with Ghost;

   function Suffix_5 (A, B : Key_Bytes) return Boolean is
      (A (20) < B (20) or else (A (20) = B (20) and then
       (A (21) < B (21) or else (A (21) = B (21) and then
       (A (22) < B (22) or else (A (22) = B (22) and then
       (A (23) < B (23) or else (A (23) = B (23) and then
       Suffix_6 (A, B)))))))))
     with Ghost;

   function Suffix_4 (A, B : Key_Bytes) return Boolean is
      (A (16) < B (16) or else (A (16) = B (16) and then
       (A (17) < B (17) or else (A (17) = B (17) and then
       (A (18) < B (18) or else (A (18) = B (18) and then
       (A (19) < B (19) or else (A (19) = B (19) and then
       Suffix_5 (A, B)))))))))
     with Ghost;

   function Suffix_3 (A, B : Key_Bytes) return Boolean is
      (A (12) < B (12) or else (A (12) = B (12) and then
       (A (13) < B (13) or else (A (13) = B (13) and then
       (A (14) < B (14) or else (A (14) = B (14) and then
       (A (15) < B (15) or else (A (15) = B (15) and then
       Suffix_4 (A, B)))))))))
     with Ghost;

   function Suffix_2 (A, B : Key_Bytes) return Boolean is
      (A (8) < B (8) or else (A (8) = B (8) and then
       (A (9) < B (9) or else (A (9) = B (9) and then
       (A (10) < B (10) or else (A (10) = B (10) and then
       (A (11) < B (11) or else (A (11) = B (11) and then
       Suffix_3 (A, B)))))))))
     with Ghost;

   function Suffix_1 (A, B : Key_Bytes) return Boolean is
      (A (4) < B (4) or else (A (4) = B (4) and then
       (A (5) < B (5) or else (A (5) = B (5) and then
       (A (6) < B (6) or else (A (6) = B (6) and then
       (A (7) < B (7) or else (A (7) = B (7) and then
       Suffix_2 (A, B)))))))))
     with Ghost;

   function Suffix_0 (A, B : Key_Bytes) return Boolean is
      (A (0) < B (0) or else (A (0) = B (0) and then
       (A (1) < B (1) or else (A (1) = B (1) and then
       (A (2) < B (2) or else (A (2) = B (2) and then
       (A (3) < B (3) or else (A (3) = B (3) and then
       Suffix_1 (A, B)))))))))
     with Ghost;

   procedure Lemma_Lt_Is_Lexicographic (A, B : Key_Bytes) is
      KA : constant Key256 := To_Key256 (A);
      KB : constant Key256 := To_Key256 (B);
   begin
      Lemma_Word_Lt_Is_Lexicographic
        (A (0), A (1), A (2), A (3),
         B (0), B (1), B (2), B (3));
      pragma Assert (KA.W0 = Word_Of (A (0), A (1), A (2), A (3)));
      pragma Assert (KB.W0 = Word_Of (B (0), B (1), B (2), B (3)));
      Lemma_Word_Lt_Is_Lexicographic
        (A (4), A (5), A (6), A (7),
         B (4), B (5), B (6), B (7));
      pragma Assert (KA.W1 = Word_Of (A (4), A (5), A (6), A (7)));
      pragma Assert (KB.W1 = Word_Of (B (4), B (5), B (6), B (7)));
      Lemma_Word_Lt_Is_Lexicographic
        (A (8), A (9), A (10), A (11),
         B (8), B (9), B (10), B (11));
      pragma Assert (KA.W2 = Word_Of (A (8), A (9), A (10), A (11)));
      pragma Assert (KB.W2 = Word_Of (B (8), B (9), B (10), B (11)));
      Lemma_Word_Lt_Is_Lexicographic
        (A (12), A (13), A (14), A (15),
         B (12), B (13), B (14), B (15));
      pragma Assert (KA.W3 = Word_Of (A (12), A (13), A (14), A (15)));
      pragma Assert (KB.W3 = Word_Of (B (12), B (13), B (14), B (15)));
      Lemma_Word_Lt_Is_Lexicographic
        (A (16), A (17), A (18), A (19),
         B (16), B (17), B (18), B (19));
      pragma Assert (KA.W4 = Word_Of (A (16), A (17), A (18), A (19)));
      pragma Assert (KB.W4 = Word_Of (B (16), B (17), B (18), B (19)));
      Lemma_Word_Lt_Is_Lexicographic
        (A (20), A (21), A (22), A (23),
         B (20), B (21), B (22), B (23));
      pragma Assert (KA.W5 = Word_Of (A (20), A (21), A (22), A (23)));
      pragma Assert (KB.W5 = Word_Of (B (20), B (21), B (22), B (23)));
      Lemma_Word_Lt_Is_Lexicographic
        (A (24), A (25), A (26), A (27),
         B (24), B (25), B (26), B (27));
      pragma Assert (KA.W6 = Word_Of (A (24), A (25), A (26), A (27)));
      pragma Assert (KB.W6 = Word_Of (B (24), B (25), B (26), B (27)));
      Lemma_Word_Lt_Is_Lexicographic
        (A (28), A (29), A (30), A (31),
         B (28), B (29), B (30), B (31));
      pragma Assert (KA.W7 = Word_Of (A (28), A (29), A (30), A (31)));
      pragma Assert (KB.W7 = Word_Of (B (28), B (29), B (30), B (31)));
      pragma Assert (Suffix_7 (A, B) = (KA.W7 < KB.W7));
      pragma Assert (Suffix_6 (A, B) =
        (KA.W6 < KB.W6 or else (KA.W6 = KB.W6 and then Suffix_7 (A, B))));
      pragma Assert (Suffix_5 (A, B) =
        (KA.W5 < KB.W5 or else (KA.W5 = KB.W5 and then Suffix_6 (A, B))));
      pragma Assert (Suffix_4 (A, B) =
        (KA.W4 < KB.W4 or else (KA.W4 = KB.W4 and then Suffix_5 (A, B))));
      pragma Assert (Suffix_3 (A, B) =
        (KA.W3 < KB.W3 or else (KA.W3 = KB.W3 and then Suffix_4 (A, B))));
      pragma Assert (Suffix_2 (A, B) =
        (KA.W2 < KB.W2 or else (KA.W2 = KB.W2 and then Suffix_3 (A, B))));
      pragma Assert (Suffix_1 (A, B) =
        (KA.W1 < KB.W1 or else (KA.W1 = KB.W1 and then Suffix_2 (A, B))));
      pragma Assert (Suffix_0 (A, B) =
        (KA.W0 < KB.W0 or else (KA.W0 = KB.W0 and then Suffix_1 (A, B))));
      pragma Assert (Lex_Lt (A, B) = Suffix_0 (A, B));
      pragma Assert (Lt (KA, KB) = Suffix_0 (A, B));
   end Lemma_Lt_Is_Lexicographic;

   ---------------------------
   -- Lemma_Lex_Of_Encoding --
   ---------------------------

   procedure Lemma_Lex_Of_Encoding (K1, K2 : Key256) is
   begin
      Lemma_Lt_Is_Lexicographic (To_Bytes (K1), To_Bytes (K2));
   end Lemma_Lex_Of_Encoding;

   -------------------------------
   -- Lemma_Lt_First_Difference --
   -------------------------------

   procedure Lemma_Lt_First_Difference (A, B : Key_Bytes; I : Key_Index) is
   begin
      Lemma_Lt_Is_Lexicographic (A, B);
      pragma Assert (Lex_Lt (A, B) = (A (I) < B (I)));
   end Lemma_Lt_First_Difference;

end Kome.Keys;
