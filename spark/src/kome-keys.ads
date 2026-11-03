--  Kome.Keys: the boundary between wire bytes and the word records of the
--  lattice (DESIGN.md §2, CONVENTIONS.md "keys are records of words").
--
--  A 32-byte key or hash (author, h, field hash) and a 16-byte identifier
--  (ns, ent) come in as bytes. In the lattice, they are Key256 / Id128:
--  records of 32-bit words, big-endian. Byte 0 is the most significant
--  byte of W0, and byte 31 is the least significant byte of W7. This
--  package is the only place where the two views meet. Its contracts say
--  that the two views are the same value:
--
--    * To_Key256 / To_Id128 decode, and To_Bytes encodes. The Post of each
--      direction states the round trip (bytes -> words -> bytes is the
--      identity elementwise, words -> bytes -> words is the identity).
--    * Lemma_Lt_Is_Lexicographic: Kome.Lt on Key256 is exactly the
--      unsigned big-endian byte-lexicographic order on the 32 bytes.
--      DESIGN.md §2 gives this order for `author` and `h` ("compared ... as
--      unsigned 256-bit integers"). Thus gnatprove can prove T1 (Version.lt
--      is a strict total order, Frontier.lean) on words, while the design
--      states it on bytes. Lemma_Lt_First_Difference states the same fact
--      as "the first differing byte decides".
--    * Id_Lt is the same order on Id128. Lemma_Id_Eq_Is_Bytewise /
--      Lemma_Id_Lt_Is_Lexicographic / Lemma_Id_Lt_First_Difference are the
--      Id128 versions of the Key256 laws. Lemma_Key_Slide / Lemma_Id_Slide
--      let a caller apply the laws to a field that is a slice of a larger
--      buffer.
--
--  All code is integer arithmetic on the range type Word (multiply and
--  divide by the constant 256), never shifts on modular words. Thus the
--  proofs stay in linear integer arithmetic. Each view in a contract has
--  no quantifier (CONVENTIONS.md, rule 2). Byte_At and Lex_Lt are
--  expression functions. Word_Of and Byte_Of_Word are functions whose Post
--  is their definition (refer to the note at their declaration).
--  There is no state: all subprograms are Global => null.
pragma Ada_2022;
package Kome.Keys with SPARK_Mode, Pure is

   --  Wire widths. DESIGN.md §2: author / sign_pk / h have 32 bytes
   --  (Pubkey_Len = Hash_Len in Kome), and ns / ent have 16 bytes
   --  (NS_Len = Ent_Len in Kome).
   Key_Len : constant := 32;
   Id_Len  : constant := 16;

   subtype Key_Index is Natural range 0 .. Key_Len - 1;
   subtype Id_Index  is Natural range 0 .. Id_Len - 1;

   subtype Key_Bytes is Byte_Array (Key_Index);
   subtype Id_Bytes  is Byte_Array (Id_Index);

   --  Byte position in one big-endian word: 0 is the most significant.
   subtype Lane is Natural range 0 .. 3;

   ----------------------------------------------------------------------
   --  One word. Word_Of packs four bytes big-endian. Byte_Of_Word extracts
   --  lane J. The divisions are written as repeated division by 256
   --  (W / 256 / 256 is (W / 256) / 256). Thus each step is a division by
   --  the same constant, and the round-trip proofs need no fact about
   --  nested quotients.
   --
   --  These two are intentionally ordinary functions whose Post is their
   --  definition, not expression functions. The prover inlines an
   --  expression function this small into each VC that mentions it. This
   --  put 32 byte <-> integer conversions (int2bv / bv2nat) of nested
   --  quotients into the ground problem of the VC of each conversion. The
   --  provers then timed out on what is pure congruence. As functions with
   --  a Post, the definition is a quantified axiom. The prover uses it only
   --  where the arithmetic is necessary (the lane lemmas below).
   ----------------------------------------------------------------------

   function Word_Of (B0, B1, B2, B3 : Byte) return Word
     with Global => null,
          Post => Word_Of'Result =
                    Word (B0) * 2 ** 24 + Word (B1) * 2 ** 16
                    + Word (B2) * 2 ** 8 + Word (B3);

   function Byte_Of_Word (W : Word; J : Lane) return Byte
     with Global => null,
          Post => Byte_Of_Word'Result =
                    (case J is
                        when 0 => Byte (W / 256 / 256 / 256),
                        when 1 => Byte (W / 256 / 256 mod 256),
                        when 2 => Byte (W / 256 mod 256),
                        when 3 => Byte (W mod 256));

   ----------------------------------------------------------------------
   --  Byte I of the big-endian encoding of a key / identifier: lane I mod 4
   --  of word I / 4. It is written as a case, so that it has no quantifier
   --  and no division on the index.
   ----------------------------------------------------------------------

   function Byte_At (K : Key256; I : Key_Index) return Byte is
     (case I is
         when  0 => Byte_Of_Word (K.W0, 0),
         when  1 => Byte_Of_Word (K.W0, 1),
         when  2 => Byte_Of_Word (K.W0, 2),
         when  3 => Byte_Of_Word (K.W0, 3),
         when  4 => Byte_Of_Word (K.W1, 0),
         when  5 => Byte_Of_Word (K.W1, 1),
         when  6 => Byte_Of_Word (K.W1, 2),
         when  7 => Byte_Of_Word (K.W1, 3),
         when  8 => Byte_Of_Word (K.W2, 0),
         when  9 => Byte_Of_Word (K.W2, 1),
         when 10 => Byte_Of_Word (K.W2, 2),
         when 11 => Byte_Of_Word (K.W2, 3),
         when 12 => Byte_Of_Word (K.W3, 0),
         when 13 => Byte_Of_Word (K.W3, 1),
         when 14 => Byte_Of_Word (K.W3, 2),
         when 15 => Byte_Of_Word (K.W3, 3),
         when 16 => Byte_Of_Word (K.W4, 0),
         when 17 => Byte_Of_Word (K.W4, 1),
         when 18 => Byte_Of_Word (K.W4, 2),
         when 19 => Byte_Of_Word (K.W4, 3),
         when 20 => Byte_Of_Word (K.W5, 0),
         when 21 => Byte_Of_Word (K.W5, 1),
         when 22 => Byte_Of_Word (K.W5, 2),
         when 23 => Byte_Of_Word (K.W5, 3),
         when 24 => Byte_Of_Word (K.W6, 0),
         when 25 => Byte_Of_Word (K.W6, 1),
         when 26 => Byte_Of_Word (K.W6, 2),
         when 27 => Byte_Of_Word (K.W6, 3),
         when 28 => Byte_Of_Word (K.W7, 0),
         when 29 => Byte_Of_Word (K.W7, 1),
         when 30 => Byte_Of_Word (K.W7, 2),
         when 31 => Byte_Of_Word (K.W7, 3))
     with Global => null;

   function Byte_At (K : Id128; I : Id_Index) return Byte is
     (case I is
         when  0 => Byte_Of_Word (K.W0, 0),
         when  1 => Byte_Of_Word (K.W0, 1),
         when  2 => Byte_Of_Word (K.W0, 2),
         when  3 => Byte_Of_Word (K.W0, 3),
         when  4 => Byte_Of_Word (K.W1, 0),
         when  5 => Byte_Of_Word (K.W1, 1),
         when  6 => Byte_Of_Word (K.W1, 2),
         when  7 => Byte_Of_Word (K.W1, 3),
         when  8 => Byte_Of_Word (K.W2, 0),
         when  9 => Byte_Of_Word (K.W2, 1),
         when 10 => Byte_Of_Word (K.W2, 2),
         when 11 => Byte_Of_Word (K.W2, 3),
         when 12 => Byte_Of_Word (K.W3, 0),
         when 13 => Byte_Of_Word (K.W3, 1),
         when 14 => Byte_Of_Word (K.W3, 2),
         when 15 => Byte_Of_Word (K.W3, 3))
     with Global => null;

   ----------------------------------------------------------------------
   --  Conversions. B can have any 'First (a slice of a record buffer).
   --  B (B'First) is the most significant byte of W0.
   --  The first conjunct of the Post of each decoder is its definition, so
   --  a caller can compute with it. The second conjunct is the round trip
   --  bytes -> words -> bytes. The Post of the encoder gives each byte and
   --  the round trip words -> bytes -> words.
   ----------------------------------------------------------------------

   function To_Key256 (B : Byte_Array) return Key256
     with Global => null,
          Pre  => B'Length = Key_Len,
          Post => To_Key256'Result =
                    Key256'(
        W0 => Word_Of (B (B'First), B (B'First + 1), B (B'First + 2), B (B'First + 3)),
        W1 => Word_Of (B (B'First + 4), B (B'First + 5), B (B'First + 6), B (B'First + 7)),
        W2 => Word_Of (B (B'First + 8), B (B'First + 9), B (B'First + 10), B (B'First + 11)),
        W3 => Word_Of (B (B'First + 12), B (B'First + 13), B (B'First + 14), B (B'First + 15)),
        W4 => Word_Of (B (B'First + 16), B (B'First + 17), B (B'First + 18), B (B'First + 19)),
        W5 => Word_Of (B (B'First + 20), B (B'First + 21), B (B'First + 22), B (B'First + 23)),
        W6 => Word_Of (B (B'First + 24), B (B'First + 25), B (B'First + 26), B (B'First + 27)),
        W7 => Word_Of (B (B'First + 28), B (B'First + 29), B (B'First + 30), B (B'First + 31)))
                  and then (for all I in Key_Index =>
                              Byte_At (To_Key256'Result, I) = B (B'First + I));

   function To_Bytes (K : Key256) return Key_Bytes
     with Global => null,
          Post => (for all I in Key_Index => To_Bytes'Result (I) = Byte_At (K, I))
                  and then To_Key256 (To_Bytes'Result) = K;

   function To_Id128 (B : Byte_Array) return Id128
     with Global => null,
          Pre  => B'Length = Id_Len,
          Post => To_Id128'Result =
                    Id128'(
        W0 => Word_Of (B (B'First), B (B'First + 1), B (B'First + 2), B (B'First + 3)),
        W1 => Word_Of (B (B'First + 4), B (B'First + 5), B (B'First + 6), B (B'First + 7)),
        W2 => Word_Of (B (B'First + 8), B (B'First + 9), B (B'First + 10), B (B'First + 11)),
        W3 => Word_Of (B (B'First + 12), B (B'First + 13), B (B'First + 14), B (B'First + 15)))
                  and then (for all I in Id_Index =>
                              Byte_At (To_Id128'Result, I) = B (B'First + I));

   function To_Bytes (K : Id128) return Id_Bytes
     with Global => null,
          Post => (for all I in Id_Index => To_Bytes'Result (I) = Byte_At (K, I))
                  and then To_Id128 (To_Bytes'Result) = K;

   ----------------------------------------------------------------------
   --  Unsigned big-endian byte-lexicographic "A < B" on 32 bytes, written
   --  out byte by byte. The first byte where A and B differ decides, and
   --  equal arrays are not less. The function intentionally has no
   --  quantifier.
   ----------------------------------------------------------------------

   function Lex_Lt (A, B : Key_Bytes) return Boolean is
     (A (0) < B (0) or else (A (0) = B (0) and then
     (A (1) < B (1) or else (A (1) = B (1) and then
     (A (2) < B (2) or else (A (2) = B (2) and then
     (A (3) < B (3) or else (A (3) = B (3) and then
     (A (4) < B (4) or else (A (4) = B (4) and then
     (A (5) < B (5) or else (A (5) = B (5) and then
     (A (6) < B (6) or else (A (6) = B (6) and then
     (A (7) < B (7) or else (A (7) = B (7) and then
     (A (8) < B (8) or else (A (8) = B (8) and then
     (A (9) < B (9) or else (A (9) = B (9) and then
     (A (10) < B (10) or else (A (10) = B (10) and then
     (A (11) < B (11) or else (A (11) = B (11) and then
     (A (12) < B (12) or else (A (12) = B (12) and then
     (A (13) < B (13) or else (A (13) = B (13) and then
     (A (14) < B (14) or else (A (14) = B (14) and then
     (A (15) < B (15) or else (A (15) = B (15) and then
     (A (16) < B (16) or else (A (16) = B (16) and then
     (A (17) < B (17) or else (A (17) = B (17) and then
     (A (18) < B (18) or else (A (18) = B (18) and then
     (A (19) < B (19) or else (A (19) = B (19) and then
     (A (20) < B (20) or else (A (20) = B (20) and then
     (A (21) < B (21) or else (A (21) = B (21) and then
     (A (22) < B (22) or else (A (22) = B (22) and then
     (A (23) < B (23) or else (A (23) = B (23) and then
     (A (24) < B (24) or else (A (24) = B (24) and then
     (A (25) < B (25) or else (A (25) = B (25) and then
     (A (26) < B (26) or else (A (26) = B (26) and then
     (A (27) < B (27) or else (A (27) = B (27) and then
     (A (28) < B (28) or else (A (28) = B (28) and then
     (A (29) < B (29) or else (A (29) = B (29) and then
     (A (30) < B (30) or else (A (30) = B (30) and then
     (A (31) < B (31))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     with Global => null;

   ----------------------------------------------------------------------
   --  The same two views for 16-byte identifiers (ns, ent).
   --
   --  Id_Lt is the unsigned big-endian order on Id128: the chain of word
   --  comparisons (W0 most significant), exactly as Kome.Lt is on Key256.
   --  DESIGN.md §8 orders element keys kind ‖ ent ‖ fh ‖ h bytewise.
   --  Kome.Reconcile compares the ent part with this function.
   --
   --  Id_Lex_Lt is the byte-lexicographic order on the 16 bytes, written
   --  out byte by byte. It has a different name from Lex_Lt because
   --  Id_Bytes and Key_Bytes are subtypes of one type. The two functions
   --  have no quantifier.
   ----------------------------------------------------------------------

   function Id_Lt (A, B : Id128) return Boolean is
     (A.W0 < B.W0 or else (A.W0 = B.W0 and then
      (A.W1 < B.W1 or else (A.W1 = B.W1 and then
      (A.W2 < B.W2 or else (A.W2 = B.W2 and then
       A.W3 < B.W3))))))
     with Global => null;

   function Id_Lex_Lt (A, B : Id_Bytes) return Boolean is
     (A (0) < B (0) or else (A (0) = B (0) and then
     (A (1) < B (1) or else (A (1) = B (1) and then
     (A (2) < B (2) or else (A (2) = B (2) and then
     (A (3) < B (3) or else (A (3) = B (3) and then
     (A (4) < B (4) or else (A (4) = B (4) and then
     (A (5) < B (5) or else (A (5) = B (5) and then
     (A (6) < B (6) or else (A (6) = B (6) and then
     (A (7) < B (7) or else (A (7) = B (7) and then
     (A (8) < B (8) or else (A (8) = B (8) and then
     (A (9) < B (9) or else (A (9) = B (9) and then
     (A (10) < B (10) or else (A (10) = B (10) and then
     (A (11) < B (11) or else (A (11) = B (11) and then
     (A (12) < B (12) or else (A (12) = B (12) and then
     (A (13) < B (13) or else (A (13) = B (13) and then
     (A (14) < B (14) or else (A (14) = B (14) and then
     (A (15) < B (15))))))))))))))))))))))))))))))))
     with Global => null;

   ----------------------------------------------------------------------
   --  Laws (ghost). Each lemma states its law as its Post.
   ----------------------------------------------------------------------

   --  One word: decode (encode W) = W and encode (decode B) = B.
   procedure Lemma_Word_Round_Trip (W : Word)
     with Ghost, Global => null,
          Post => Word_Of (Byte_Of_Word (W, 0), Byte_Of_Word (W, 1),
                           Byte_Of_Word (W, 2), Byte_Of_Word (W, 3)) = W;

   procedure Lemma_Lanes_Round_Trip (B0, B1, B2, B3 : Byte)
     with Ghost, Global => null,
          Post => Byte_Of_Word (Word_Of (B0, B1, B2, B3), 0) = B0
            and then Byte_Of_Word (Word_Of (B0, B1, B2, B3), 1) = B1
            and then Byte_Of_Word (Word_Of (B0, B1, B2, B3), 2) = B2
            and then Byte_Of_Word (Word_Of (B0, B1, B2, B3), 3) = B3;

   --  One word: integer order on Word_Of is lexicographic order on the
   --  four bytes, and integer equality is bytewise equality.
   procedure Lemma_Word_Lt_Is_Lexicographic (A0, A1, A2, A3, B0, B1, B2, B3 : Byte)
     with Ghost, Global => null,
          Post => (Word_Of (A0, A1, A2, A3) < Word_Of (B0, B1, B2, B3)) =
                    (A0 < B0 or else (A0 = B0 and then
                    (A1 < B1 or else (A1 = B1 and then
                    (A2 < B2 or else (A2 = B2 and then A3 < B3))))))
            and then (Word_Of (A0, A1, A2, A3) = Word_Of (B0, B1, B2, B3)) =
                    (A0 = B0 and then A1 = B1 and then A2 = B2 and then A3 = B3);

   --  The round trips through the public conversions, stated literally.
   procedure Lemma_Key_Round_Trip (K : Key256)
     with Ghost, Global => null,
          Post => To_Key256 (To_Bytes (K)) = K;

   procedure Lemma_Key_Bytes_Round_Trip (B : Byte_Array)
     with Ghost, Global => null,
          Pre  => B'Length = Key_Len,
          Post => (for all I in Key_Index =>
                     To_Bytes (To_Key256 (B)) (I) = B (B'First + I));

   procedure Lemma_Id_Round_Trip (K : Id128)
     with Ghost, Global => null,
          Post => To_Id128 (To_Bytes (K)) = K;

   procedure Lemma_Id_Bytes_Round_Trip (B : Byte_Array)
     with Ghost, Global => null,
          Pre  => B'Length = Id_Len,
          Post => (for all I in Id_Index =>
                     To_Bytes (To_Id128 (B)) (I) = B (B'First + I));

   --  The decoder is injective: equal keys iff equal bytes.
   procedure Lemma_Key_Eq_Is_Bytewise (A, B : Key_Bytes)
     with Ghost, Global => null,
          Post => (To_Key256 (A) = To_Key256 (B)) = (A = B);

   --  Kome.Lt on keys is the unsigned big-endian byte-lexicographic order
   --  on their bytes (DESIGN.md §2 "as unsigned 256-bit integers"; this is
   --  the order of T1, Frontier.lean Version.lt). This is the form without
   --  quantifiers.
   procedure Lemma_Lt_Is_Lexicographic (A, B : Key_Bytes)
     with Ghost, Global => null,
          Post => Lt (To_Key256 (A), To_Key256 (B)) = Lex_Lt (A, B);

   --  The same law, read from the key side: a comparison of two keys is a
   --  comparison of their encodings.
   procedure Lemma_Lex_Of_Encoding (K1, K2 : Key256)
     with Ghost, Global => null,
          Post => Lt (K1, K2) = Lex_Lt (To_Bytes (K1), To_Bytes (K2));

   --  The first differing byte decides (the usual statement of
   --  lexicographic order). If A and B agree before I and differ at I, then
   --  To_Key256 (A) < To_Key256 (B) exactly when A (I) < B (I).
   procedure Lemma_Lt_First_Difference (A, B : Key_Bytes; I : Key_Index)
     with Ghost, Global => null,
          Pre  => (for all J in 0 .. I - 1 => A (J) = B (J))
                  and then A (I) /= B (I),
          Post => Lt (To_Key256 (A), To_Key256 (B)) = (A (I) < B (I));

   --  Identifiers: the same three laws. The decoder is injective, Id_Lt is
   --  the byte-lexicographic order on the 16 bytes (read from either side),
   --  and the first differing byte decides. Kome.Reconcile combines these
   --  with the Key256 laws above. Thus it proves that its element-key order
   --  is the bytewise order on the wire key (§8).
   procedure Lemma_Id_Eq_Is_Bytewise (A, B : Id_Bytes)
     with Ghost, Global => null,
          Post => (To_Id128 (A) = To_Id128 (B)) = (A = B);

   procedure Lemma_Id_Lt_Is_Lexicographic (A, B : Id_Bytes)
     with Ghost, Global => null,
          Post => Id_Lt (To_Id128 (A), To_Id128 (B)) = Id_Lex_Lt (A, B);

   procedure Lemma_Id_Lex_Of_Encoding (K1, K2 : Id128)
     with Ghost, Global => null,
          Post => Id_Lt (K1, K2) = Id_Lex_Lt (To_Bytes (K1), To_Bytes (K2));

   procedure Lemma_Id_Lt_First_Difference (A, B : Id_Bytes; I : Id_Index)
     with Ghost, Global => null,
          Pre  => (for all J in 0 .. I - 1 => A (J) = B (J))
                  and then A (I) /= B (I),
          Post => Id_Lt (To_Id128 (A), To_Id128 (B)) = (A (I) < B (I));

   --  Slice sliding. A field of a record buffer is a slice B with an
   --  arbitrary 'First. A conversion of B to Key_Bytes / Id_Bytes slides it
   --  to 'First = 0, does not change a byte, and decodes to the same key.
   --  With this, a caller can apply the laws above (stated on Key_Bytes /
   --  Id_Bytes) to To_Key256 / To_Id128 of a slice.
   procedure Lemma_Key_Slide (B : Byte_Array)
     with Ghost, Global => null,
          Pre  => B'Length = Key_Len,
          Post => (for all I in Key_Index => Key_Bytes (B) (I) = B (B'First + I))
                  and then To_Key256 (Key_Bytes (B)) = To_Key256 (B);

   procedure Lemma_Id_Slide (B : Byte_Array)
     with Ghost, Global => null,
          Pre  => B'Length = Id_Len,
          Post => (for all I in Id_Index => Id_Bytes (B) (I) = B (B'First + I))
                  and then To_Id128 (Id_Bytes (B)) = To_Id128 (B);

end Kome.Keys;
