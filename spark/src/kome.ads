--  Root of Kome: the byte types, the integer ranges and the size bounds that
--  every package shares. The design is docs/design/DESIGN.md; the proved
--  model it refines is lean/Kome/Frontier.lean. Each DESIGN.md section is a
--  child package (Kome.Version, Kome.Headers, Kome.Frontier, ...); see
--  CONVENTIONS.md for the rules every child follows.
pragma Ada_2022;
package Kome with SPARK_Mode, Pure is

   type Byte is mod 2**8 with Size => 8;
   type Byte_Array is array (Natural range <>) of Byte;

   --  Modular types for wire encoding and hashing only (Kome.Byteorder,
   --  Kome.SHA256). Semantic quantities use the range types below, so that
   --  every overflow is a proof obligation and no value is reserved (H6).
   type U16 is mod 2**16 with Size => 16;
   type U32 is mod 2**32 with Size => 32;
   type U64 is mod 2**64 with Size => 64;

   --  DESIGN.md §2: t, seq, gen, ceiling_t, del_ttl, from_t, rev_seq are
   --  48-bit. 0 is an ordinary value; 2**48 - 1 is an ordinary value; an
   --  emission that would exceed the range fails with no side effect (T13).
   type U48 is range 0 .. 2**48 - 1 with Size => 64;
   type Epoch is range 0 .. 2**16 - 1 with Size => 16;

   --  Fixed-size identifiers and cryptographic values (DESIGN.md §2).
   NS_Len     : constant := 16;   --  ns = BLAKE2b-256(root_pk ‖ salt)[0:16]
   Ent_Len    : constant := 16;
   Salt_Len   : constant := 16;
   Pubkey_Len : constant := 32;   --  Ed25519 / X25519
   Hash_Len   : constant := 32;   --  BLAKE2b-256, SHA-256
   Sig_Len    : constant := 64;   --  Ed25519
   Nonce_Len  : constant := 24;   --  XChaCha20-Poly1305
   Box_Len    : constant := 48;   --  32-byte epoch key + 16-byte tag

   --  In the lattice, identifiers and keys are records of fixed-width words
   --  (big-endian: W0 is the most significant), not byte arrays, so that
   --  equality on them is logical equality for the prover and the byte-
   --  lexicographic order is a chain of word comparisons. Kome.Records
   --  converts from the wire bytes.
   type Word is range 0 .. 2**32 - 1 with Size => 32;

   type Id128 is record
      W0, W1, W2, W3 : Word := 0;
   end record;

   type Key256 is record
      W0, W1, W2, W3, W4, W5, W6, W7 : Word := 0;
   end record;

   --  Unsigned big-endian "A < B".
   function Lt (A, B : Key256) return Boolean is
     (A.W0 < B.W0 or else (A.W0 = B.W0 and then
      (A.W1 < B.W1 or else (A.W1 = B.W1 and then
      (A.W2 < B.W2 or else (A.W2 = B.W2 and then
      (A.W3 < B.W3 or else (A.W3 = B.W3 and then
      (A.W4 < B.W4 or else (A.W4 = B.W4 and then
      (A.W5 < B.W5 or else (A.W5 = B.W5 and then
      (A.W6 < B.W6 or else (A.W6 = B.W6 and then
       A.W7 < B.W7))))))))))))));

   subtype NS_Id   is Byte_Array (0 .. NS_Len - 1);
   subtype Ent_Id  is Byte_Array (0 .. Ent_Len - 1);
   subtype Salt    is Byte_Array (0 .. Salt_Len - 1);
   subtype Pubkey  is Byte_Array (0 .. Pubkey_Len - 1);
   subtype Hash256 is Byte_Array (0 .. Hash_Len - 1);
   subtype Sig     is Byte_Array (0 .. Sig_Len - 1);
   subtype Nonce   is Byte_Array (0 .. Nonce_Len - 1);
   subtype Box     is Byte_Array (0 .. Box_Len - 1);

   --  Variable-length bounds (DESIGN.md §2). A field name is 1..32 bytes; a
   --  value is 0..65_535 bytes, and the empty value is a value.
   Field_Max  : constant := 32;
   Value_Max  : constant := 65_535;
   subtype Field_Len is Natural range 1 .. Field_Max;
   subtype Value_Len is Natural range 0 .. Value_Max;

   --  Membership bounds (DESIGN.md §2, §6, §7).
   Members_Max     : constant := 64;      --  n_members per ROSTER
   Roots_Max       : constant := 4;       --  n_roots per ROSTER (module J)
   Revocations_Max : constant := 1024;    --  after which a collection is re-founded
   --  Every key any roster has ever listed (the grow-only register W) is
   --  bounded by members over the collection's life: Members_Max live plus
   --  Revocations_Max revoked.
   Writers_Max     : constant := Members_Max + Revocations_Max;

   --  Reconciliation (DESIGN.md §8).
   Split_Fanout    : constant := 16;
   Ship_Threshold  : constant := 4;
   Max_Message_Len : constant := 48 * 1024;

   --  Result codes returned across the C ABI. Every operation that can fail
   --  returns one of these and leaves the store unchanged on failure.
   type Status is
     (OK,
      Dominated,        --  record applied: already beaten by a held record
      Inadmissible,     --  record refused: above the ceiling or author not in W
      Malformed,        --  bounds or signature failed; a function of the bytes
      Shadowed,         --  write emitted at the ceiling and loses to the floor
      Seq_Exhausted,    --  seq would exceed 2**48 - 1; nothing emitted
      No_Space);        --  bounded store is full; nothing changed

end Kome;
