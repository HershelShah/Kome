--  Root of Kome. This package holds the byte types, the integer ranges and
--  the size bounds that all packages share. docs/design/DESIGN.md gives the
--  design. Seven child packages refine the proved model in
--  lean/Kome/Frontier.lean: Kome.Versions, Kome.Headers, Kome.Frontier,
--  Kome.Records, Kome.Store, Kome.Emit and Kome.Views.
--  Kome.Write joins Emit, Records and Store into the write path (DESIGN.md
--  §5 steps 1-3, AUDIT.md A10) and gives the apply-side clone flag (H18).
--  The others implement encodings, cryptography and protocols. Each DESIGN.md
--  concept is one child package Kome.<Name>, in kome-<name>.ads and
--  kome-<name>.adb. spark/CONVENTIONS.md gives the rules that each child
--  follows.
pragma Ada_2022;
package Kome with SPARK_Mode, Pure is

   type Byte is mod 2**8 with Size => 8;
   type Byte_Array is array (Natural range <>) of Byte;

   --  Byte and U64 are the only modular types. Byte is the wire unit. U64
   --  is for the limbs of the accumulator and their byte encoding
   --  (Kome.Byteorder, Kome.Accumulator, Kome.Digest) and for C storage in
   --  Kome.Crypto. Semantic quantities use the range types below, so that
   --  each overflow is a proof obligation and no value is reserved (H6).
   type U64 is mod 2**64 with Size => 64;

   --  DESIGN.md §2: t, seq, gen, ceiling_t, del_ttl and from_t are
   --  48-bit values. 0 is an ordinary value, and 2**48 - 1 is an ordinary
   --  value. If an emission would go above the range, it fails and has no
   --  side effect (T13).
   type U48 is range 0 .. 2**48 - 1 with Size => 64;
   type Epoch is range 0 .. 2**16 - 1 with Size => 16;

   --  Fixed-size identifiers and cryptographic values (DESIGN.md §2).
   NS_Len     : constant := 16;   --  ns = BLAKE2b-256(root_pk ‖ salt)[0:16]
   Ent_Len    : constant := 16;
   Salt_Len   : constant := 16;
   Pubkey_Len : constant := 32;   --  Ed25519 / X25519
   Hash_Len   : constant := 32;   --  BLAKE2b-256
   Sig_Len    : constant := 64;   --  Ed25519
   Nonce_Len  : constant := 24;   --  XChaCha20-Poly1305
   Box_Len    : constant := 48;   --  32-byte epoch key + 16-byte tag

   --  In the lattice, identifiers and keys are records of fixed-width words,
   --  not byte arrays. The words are big-endian: W0 is the most significant.
   --  For the prover, equality on these records is logical equality,
   --  and the byte-lexicographic order is a chain of word comparisons.
   --  Kome.Keys converts the wire bytes to these records (To_Key256 /
   --  To_Id128), and Kome.Records calls Kome.Keys.
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

   --  Variable-length bounds (DESIGN.md §2). A field name has 1..32 bytes. A
   --  value has 0..40_960 bytes, and the empty value is a value. A frame has
   --  at most 41_136 bytes. The value bound (D12) makes each frame fit in
   --  one 48 KiB reconciliation message (§8).
   Field_Max  : constant := 32;
   Value_Max  : constant := 40_960;
   subtype Field_Len is Natural range 1 .. Field_Max;
   subtype Value_Len is Natural range 0 .. Value_Max;

   --  Authorization bounds (DESIGN.md §2, §6, §7).
   Members_Max : constant := 64;     --  n_members per ROSTER
   Links_Max   : constant := 15;     --  n_links per ROSTER (epoch segments, E3)
   --  Signers: the founding key plus at most 15 certified roots (A1). Each
   --  signer has its own slice in the frontier (E1). A slice holds at most
   --  Slice_Max authorization records (the rosters, REVOKEs and GRANTs that
   --  the signer signed).
   --  Slice_Max is a compile-time constant of every state (SIMPLIFY.md
   --  S15): the frontier holds at most Signers_Max * Slice_Max = 8_192
   --  authorization records.
   Signers_Max : constant := 16;
   Slice_Max   : constant := 512;

   --  Tombstone lifetime del_ttl, in milliseconds (DESIGN.md §2 rule 3,
   --  §3 del_ttl_eff, §7). Decode refuses (Malformed) a ROSTER whose
   --  del_ttl is outside [Del_TTL_Min, Del_TTL_Max]. If there is no
   --  roster, the default applies.
   Del_TTL_Min     : constant := 604_800_000;        --  7 days
   Del_TTL_Default : constant := 15_552_000_000;     --  180 days
   Del_TTL_Max     : constant := 315_360_000_000;    --  3 650 days

   --  The ceiling lead (DESIGN.md §7, §10.3; AUDIT.md H14, A5): an honest
   --  root sets ceiling_t at most Cap_Lead ahead of its clock, so that
   --  maxceil - now <= Cap_Lead while every root is honest. The expiry
   --  clamp then protects a tombstone for at least del_ttl_eff - Cap_Lead
   --  at every replica, and a DEL is emitted at t >= maxceil - Cap_Lead
   --  (Kome.Emit), so it never expires on arrival at a clocked replica.
   --  Cap_Lead must stay below Del_TTL_Min.
   Cap_Lead : constant := 259_200_000;               --  3 days
   pragma Compile_Time_Error (Cap_Lead >= Del_TTL_Min,
                              "DESIGN.md §7: Cap_Lead must be below Del_TTL_Min");

   --  Signed 64-bit time for the expiry horizon (DESIGN.md §7). The code
   --  computes horizon := min (now_local, maxceil) - del_ttl_eff in 64 bits,
   --  so it never wraps. A value below 0 means "no horizon".
   type Time64 is range -(2**62) .. 2**62 with Size => 64;
   No_Horizon : constant Time64 := -1;

   --  Reconciliation (DESIGN.md §8).
   Split_Fanout    : constant := 16;
   Ship_Threshold  : constant := 4;
   Max_Message_Len : constant := 48 * 1024;

   --  Result codes of decode and of the store operations (Kome.Records,
   --  Kome.Frontier, Kome.Store, Kome.Emit). They are also the result codes
   --  of the C ABI, when it exists (DESIGN.md §10.6). Each operation that can
   --  fail returns one of these codes. On failure, it does not change the
   --  store.
   type Status is
     (OK,
      Dominated,        --  record applied: a held record already beats it
      Inadmissible,     --  record refused: above the ceiling or author not in W
      Malformed,        --  bounds or signature failed; depends on bytes only
      Shadowed,         --  write emitted at the ceiling; the floor beats it
      Seq_Exhausted,    --  seq would go above 2**48 - 1; nothing emitted
      No_Space,         --  bounded store is full; nothing changed
      Auth_Full,        --  the signer's authorization slice, or the slot
                        --  table, is full; nothing changed (DESIGN.md §7)
      Log_Full,         --  the record fits F but not the log; nothing
                        --  changed: compact and retry (DESIGN.md §7, E2)
      Seq_Corrupt);     --  the binding cannot read the persisted seq_self
                        --  (torn, bad checksum); a report, apart from
                        --  Seq_Exhausted: the write path starts from
                        --  Max_Own_Seq (Kome.Write.Open_Seq, AUDIT.md A10)

end Kome;
