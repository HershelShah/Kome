--  Kome.Crypto: the thin binding to monocypher 4.0.2 (third_party/monocypher,
--  its README gives the provenance). monocypher is the only cryptographic
--  dependency of the design (DESIGN.md §2, §6, §8; CONVENTIONS.md
--  "Cryptography": bind it, do not implement it again).
--
--    BLAKE2b-256      crypto_blake2b, crypto_blake2b_init/update/final with
--                     hash_size = 32. DESIGN.md §2 `ns`, `h`, the root
--                     certificate; §6 the box keys; §8 the accumulator
--                     and the bundle nonce. Assumption A2.
--    keyed BLAKE2b    crypto_blake2b_keyed with hash_size = key_size = 32:
--                     the PRF f of DESIGN.md §6 (the epoch chain step) and
--                     §8 (the bundle key). AUDIT.md G5.
--    Ed25519          crypto_ed25519_key_pair / _sign / _check, from the
--                     optional monocypher-ed25519.c. DESIGN.md §2 `sig`,
--                     `cert_sig`. Assumption A1.
--    X25519           crypto_x25519_public_key, crypto_x25519. DESIGN.md §6
--                     (the epoch key wrapped to each member's `dh_pk`).
--    XChaCha20-       crypto_aead_lock / _unlock: 32-byte key, 24-byte nonce,
--    Poly1305         16-byte tag. DESIGN.md §2 `nonce[24] box[48]`, §8
--                     sealed bundles. T14 (paper) depends on it.
--    Erasure          crypto_wipe, on byte buffers, signing keys and hash
--                     contexts.
--
--  SIGNATURE SCHEME (DESIGN.md §1 D4, §2, A1). Signatures are
--  RFC 8032 Ed25519 (PureEd25519), from the optional monocypher-ed25519.c
--  of monocypher (crypto_ed25519_*). Only the signature uses SHA-512. It
--  uses SHA-512 to expand the seed into the secret scalar and the nonce
--  prefix, and to hash R ‖ A ‖ M into the challenge (RFC 8032
--  §5.1.5-5.1.7). No value that Kome derives uses SHA-512. BLAKE2b-256
--  stays the hash for h, ns, certificates, the accumulator and each key
--  derivation.
--
--  This package does not bind monocypher's core crypto_eddsa_* (EdDSA
--  with BLAKE2b-512, the scheme of Nano). That scheme is not RFC 8032,
--  and its signatures do not verify here.
--
--  STRICT VERIFICATION (DESIGN.md §2 "strict: S < L"; AUDIT.md H13, A25,
--  G16). Verify accepts a signature exactly when these conditions are all
--  true:
--    (a) S < L;
--    (b) R is the canonical RFC 8032 §5.1.2 encoding of a point;
--    (c) PK is also such a canonical encoding;
--    (d) PK is not one of the 8 canonical encodings of a point of small
--        order (the torsion subgroup: orders 1, 2, 4 and 8);
--    (e) crypto_ed25519_check accepts (sig, pk, msg): the cofactored group
--        equation [8][S]B = [8]R + [8][k]A, which RFC 8032 §5.1.7 permits.
--  This predicate is normative (G16): a record is well-formed iff its
--  signature satisfies it, and every Kome verifier must agree on it. The
--  Wycheproof subset, the ed25519-speccheck ("Taming the many EdDSAs")
--  cases and the torsion vectors of vectors/crypto.txt pin it.
--
--  crypto_ed25519_check itself enforces (a), and it refuses encodings that
--  are not on the curve. But by design it allows the non-canonical
--  encodings y >= p and "x = 0 with the sign bit set" (monocypher.c
--  crypto_eddsa_check_equation: "*Allow* non-cannonical encoding for A and
--  R"). Wycheproof ed25519_test.json tcId 151 is such a signature, and
--  crypto_ed25519_check accepts it. It also accepts every small-order
--  public key: for such an A, [8][k]A is the identity for every k, so the
--  signature (R = identity, S = 0) verifies for every message (universal
--  forgery; H13). The all-zero key is one of these points (order 4).
--
--  The binding checks (b), (c) and (d) itself (Is_Canonical_Point,
--  Is_Small_Order_Point). The strictness of (b) and (c) is the decoding
--  rule of RFC 8032 §5.1.3. Verify is a SPARK expression function
--  (completed in the private part, A25): the conjunction of (a) to (d),
--  which gnatprove proves like any other code, and of Raw_Ed25519_Check,
--  the C call with no Post. So the Posts of Verify are proved, not
--  assumed; only the group equation itself is assumed (A1).
--
--  SPARK boundary (CONVENTIONS.md, the one allowed exception): this spec is
--  SPARK_Mode On with full contracts. The body is SPARK_Mode Off, and it
--  calls C through Interfaces.C, so gnatprove ASSUMES the Posts of the
--  subprograms that the body completes, and does not prove them. Only
--  execution (-gnata) checks them, against the known-answer vectors and
--  the properties of tests/test_crypto.adb. This is inherent to a binding
--  to C. The contracts state these facts:
--    * input bounds, output lengths and layouts;
--    * the state machine and the byte count of the incremental context;
--    * that only Key_Pair makes a valid signing key, from a seed that is
--      not all zeros (A27), and that the public half of a valid key is the
--      one derived from its seed. Is_Valid is an expression function, so
--      gnatprove proves its Post and the facts about the default key;
--    * strict verification: True implies S < L, canonical R and PK, and a
--      PK that is not small-order (proved from the expression of Verify);
--    * that X25519 reports a non-contributory exchange, and which X25519
--      keys Kome accepts at decode (Is_Good_DH_Key, E5);
--    * the public keys of the all-zero seed and of the all-zero X25519
--      secret, as named constants (Zero_Seed_Public, Zero_Secret_DH_Public;
--      A27). Kome.Records refuses them at decode;
--    * that a refused Unlock and each Wipe leave zeros;
--    * that BLAKE2b-256 depends only on the bytes of its input
--      (Lemma_Blake2b_Congruent, an axiom for the prover, run by the test
--      main), and that X25519 computes X25519_Shared (a ghost function, so
--      that contracts can name keys derived from an exchange).
--  They do not state Verify (Sign (M)) or the hashing algebra. Those are A1
--  and A2, plus the known-answer vectors. The expression functions here
--  (S_Below_L, Is_Canonical_Point, Is_Reduced_U, Is_Low_Order_U, ...) are
--  SPARK, and gnatprove proves them like any other code.
--
--  Each function here is a mathematical function of its arguments, so it is
--  a SPARK function with Global => null. Ed25519 signatures are
--  deterministic, and no code reads a clock or an RNG.
--
--  PREELABORATE, NOT PURE. RM 10.2.1(18) lets an implementation omit a
--  call to a library-level subprogram of a declared-pure unit, when the
--  results of the call are not necessary after it. A Wipe just before a
--  secret goes out of scope is exactly such a call. The package is
--  Preelaborate, so that this permission never applies and each Wipe is an
--  ordinary call to C that must execute. A unit that withs Kome.Crypto can
--  be Preelaborate but not Pure.
--
--  BY-REFERENCE SECRETS. Secret_Key and Blake2b_Context are limited
--  private types whose full types are explicitly limited records. By RM
--  6.2(4) and 6.2(7), such a record is a by-reference type. By RM 6.2(9), a
--  private type with such a full type is also a by-reference type. RM
--  6.2(10) then requires the compiler to pass each parameter of these types
--  by reference. As a result, a Wipe or a Final erases the caller's object
--  itself, not a copy of it. Because these types are limited, assignment
--  cannot copy them either.
--
--  That is all that the RM promises. It does not stop the C code, or
--  register allocation, from leaving copies in other locations; crypto_wipe
--  in monocypher is for this. Byte_Array (an array of an elementary type)
--  is not a by-reference type, and RM 6.2(11) leaves its parameter
--  mechanism unspecified. See Wipe (B) for the property that the code
--  depends on there.
pragma Ada_2022;
package Kome.Crypto with SPARK_Mode, Preelaborate is

   ---------------------------------------------------------------------------
   --  Sizes (monocypher.h and monocypher-ed25519.h prototypes; DESIGN.md §2
   --  gives the Kome names)
   ---------------------------------------------------------------------------

   Seed_Len       : constant := 32;   --  crypto_ed25519_key_pair seed[32]
   Secret_Key_Len : constant := 64;   --  crypto_ed25519 secret_key[64] = seed ‖ pk
   DH_Key_Len     : constant := 32;   --  crypto_x25519 keys and raw secret
   AEAD_Key_Len   : constant := 32;   --  crypto_aead_lock key[32]
   Tag_Len        : constant := 16;   --  crypto_aead_lock mac[16]

   subtype Seed          is Byte_Array (0 .. Seed_Len - 1);
   subtype DH_Secret     is Byte_Array (0 .. DH_Key_Len - 1);
   subtype Shared_Secret is Byte_Array (0 .. DH_Key_Len - 1);
   subtype AEAD_Key      is Byte_Array (0 .. AEAD_Key_Len - 1);
   subtype Tag           is Byte_Array (0 .. Tag_Len - 1);
   --  Pubkey (32), Hash256 (32), Sig (64) and Nonce (24) come from Kome.
   --  A DESIGN.md §2 Box (48 bytes) is an AEAD_Key sealed under Lock,
   --  followed by its Tag.

   --  All 32 bytes are zero. The function has no quantifier (CONVENTIONS.md
   --  rule 2), so it costs a caller's prover nothing. Seed, DH_Secret and
   --  Shared_Secret have the same bounds, so it applies to each of them.
   function Is_Zero (K : Shared_Secret) return Boolean is
     (K (0) = 0 and then K (1) = 0 and then K (2) = 0 and then K (3) = 0
      and then K (4) = 0 and then K (5) = 0 and then K (6) = 0
      and then K (7) = 0 and then K (8) = 0 and then K (9) = 0
      and then K (10) = 0 and then K (11) = 0 and then K (12) = 0
      and then K (13) = 0 and then K (14) = 0 and then K (15) = 0
      and then K (16) = 0 and then K (17) = 0 and then K (18) = 0
      and then K (19) = 0 and then K (20) = 0 and then K (21) = 0
      and then K (22) = 0 and then K (23) = 0 and then K (24) = 0
      and then K (25) = 0 and then K (26) = 0 and then K (27) = 0
      and then K (28) = 0 and then K (29) = 0 and then K (30) = 0
      and then K (31) = 0)
     with Global => null;

   --  Bytes 0 .. 30 of P and Q are equal (byte by byte, no quantifier). The
   --  small-order test below compares a key against a constant in its low
   --  31 bytes and then decides on byte 31 (the sign bit may be set).
   function Same_Low_31 (P, Q : Pubkey) return Boolean is
     (P (0) = Q (0) and then P (1) = Q (1) and then P (2) = Q (2)
      and then P (3) = Q (3) and then P (4) = Q (4) and then P (5) = Q (5)
      and then P (6) = Q (6) and then P (7) = Q (7) and then P (8) = Q (8)
      and then P (9) = Q (9) and then P (10) = Q (10) and then P (11) = Q (11)
      and then P (12) = Q (12) and then P (13) = Q (13) and then P (14) = Q (14)
      and then P (15) = Q (15) and then P (16) = Q (16) and then P (17) = Q (17)
      and then P (18) = Q (18) and then P (19) = Q (19) and then P (20) = Q (20)
      and then P (21) = Q (21) and then P (22) = Q (22) and then P (23) = Q (23)
      and then P (24) = Q (24) and then P (25) = Q (25) and then P (26) = Q (26)
      and then P (27) = Q (27) and then P (28) = Q (28) and then P (29) = Q (29)
      and then P (30) = Q (30))
     with Global => null;

   --  All 32 bytes of P and Q are equal (byte by byte, no quantifier).
   function Same_Bytes (P, Q : Pubkey) return Boolean is
     (Same_Low_31 (P, Q) and then P (31) = Q (31))
     with Global => null;

   --  The largest single buffer that this package gives to monocypher,
   --  1 MiB. It is declared here, not in Kome (root), because this package
   --  owns only its own files. It is not derived from Value_Max. The design
   --  gives this package these inputs:
   --    * DESIGN.md §2: the largest hashed or signed input is a frame, at
   --      most 41_136 bytes (a PUT with a 32-byte field and a 40_960-byte
   --      value). A signature covers only the 32 bytes of h;
   --    * §8: a sealed-bundle plaintext is a list of ELEMENTS items with a
   --      total of at most Max_Message_Len = 48 KiB. It is the AEAD
   --      plaintext. Its synthetic nonce hashes "kome/bnonce" ‖ k_b ‖
   --      plaintext, which is 43 bytes more (checked below, with 64 bytes
   --      of room);
   --    * §2, §6, §8: each hashed input for certificates, key derivations,
   --      box nonces and the accumulator is less than 1 KiB (the largest is
   --      fp(R) = "kome/fp" ‖ u64 ‖ ACC_le(R), 7 + 8 + 512 bytes).
   --  2**20 covers all of these with room (about 21 times the bundle
   --  plaintext). Larger payloads are chunked above the engine (§2), so no
   --  larger input gets to this package. The bound exists so that each
   --  length converts to size_t and to Stream_Len without overflow.
   Max_Data_Len : constant := 2**20;

   pragma Compile_Time_Error
     (Max_Data_Len < Max_Message_Len + 64,
      "Max_Data_Len must hold a sealed-bundle plaintext plus its hash prefix");
   pragma Compile_Time_Error
     (Max_Data_Len < 144 + Field_Max + Value_Max,
      "Max_Data_Len must hold the largest frame (DESIGN.md §2)");

   ---------------------------------------------------------------------------
   --  BLAKE2b-256 (RFC 7693, 32-byte digest)
   ---------------------------------------------------------------------------

   --  crypto_blake2b (hash, 32, data, len). DESIGN.md §2: h = BLAKE2b-256
   --  (tag ‖ content), and ns = BLAKE2b-256 (root_pk ‖ salt)[0:16]. A2.
   --  There is no Post. The result subtype Hash256 fixes the output length.
   --  This is a static fact, and GNAT flags it as a vacuous Post. This spec
   --  cannot check other properties of a hash: collision resistance is A2.
   --  The vectors of the test main cover the agreement with the incremental
   --  form and with RFC 7693.
   function Blake2b_256 (Data : Byte_Array) return Hash256
     with Global => null,
          Pre    => Data'Length <= Max_Data_Len;

   --  Congruence: BLAKE2b-256 reads only the bytes of its input, in order,
   --  so two inputs with the same bytes have the same digest, whatever
   --  their bounds. This is true of each function of a byte string, but the
   --  prover cannot see it. The prover has no array extensionality, and two
   --  arrays with equal elements but different bounds or different
   --  construction are different terms.
   --
   --  The body is SPARK_Mode Off like each other body here, so the Post is
   --  an AXIOM (assumed, like the other Posts of the binding). The test main
   --  checks it under -gnata on slices with different bounds. Clients use it
   --  to carry a hash across a copy or a re-slice (the wrap key of
   --  Kome.Epochs).
   procedure Lemma_Blake2b_Congruent (A, B : Byte_Array)
     with Ghost, Global => null, Always_Terminates,
          Pre  => A'Length = B'Length
                  and then A'Length <= Max_Data_Len
                  and then (for all K in 0 .. A'Length - 1 =>
                              A (A'First + K) = B (B'First + K)),
          Post => Blake2b_256 (A) = Blake2b_256 (B);

   --  The same hash, written directly into the caller's buffer. Use
   --  this form when the digest is itself a secret, so that no
   --  function-result temporary holds a copy. An example is the wrap key
   --  of a member box (DESIGN.md §6). The caller wipes Digest. The
   --  procedure is Always_Terminates (one C call), so a function can hash
   --  into a buffer that it then wipes.
   procedure Blake2b_256 (Data : Byte_Array; Digest : out Hash256)
     with Global => null, Always_Terminates,
          Pre    => Data'Length <= Max_Data_Len,
          Post   => Digest = Blake2b_256 (Data);

   --  Keyed BLAKE2b-256 (RFC 7693 §2.10 and §3.3: the key is padded to one
   --  128-byte block and hashed first, with the key length in the
   --  parameter block), crypto_blake2b_keyed (hash, 32, key, 32, data, len).
   --  It is the PRF f (key, msg) of DESIGN.md §6 and §8 (AUDIT.md G5): the
   --  epoch chain step k_e = f (k_{e+1}, "kome/prev") and the bundle key
   --  k_b = f (k_e, "kome/bundle" ‖ ns) are both instances of one keyed
   --  BLAKE2b assumption, not of an unkeyed hash of key ‖ label. The key is
   --  32 bytes (Mac_Key). There is no Post, as for Blake2b_256; the test
   --  main checks hashlib's keyed answers.
   subtype Mac_Key is Byte_Array (0 .. Hash_Len - 1);

   function Blake2b_256_Keyed (Key : Mac_Key; Data : Byte_Array) return Hash256
     with Global => null,
          Pre    => Data'Length <= Max_Data_Len;

   --  The same, written into the caller's buffer, for a secret digest (the
   --  next epoch key). The caller wipes Digest. Always_Terminates, so that
   --  Kome.Epochs.Step (a function) can call it.
   procedure Blake2b_256_Keyed (Key : Mac_Key; Data : Byte_Array; Digest : out Hash256)
     with Global => null, Always_Terminates,
          Pre    => Data'Length <= Max_Data_Len,
          Post   => Digest = Blake2b_256_Keyed (Key, Data);

   --  Incremental BLAKE2b-256: Init, any number of Update calls, then Final.
   --  The context is a bounded byte stream: at most Max_Stream_Len bytes in
   --  total, and at most Max_Data_Len for each Update. monocypher counts in
   --  128 bits, so the bound comes from Kome. Kome chooses it so that the
   --  count is a range type that cannot overflow (CONVENTIONS.md: semantic
   --  integers are range types).
   --
   --  The same bytes, given in any chunks, give Blake2b_256 of their
   --  concatenation. monocypher guarantees this. The test main runs
   --  it at each split point across the 128-byte block boundary. It is not a
   --  proof obligation, because it would need a ghost copy of an unbounded
   --  stream.
   Max_Stream_Len : constant := 2**62;
   type Stream_Len is range 0 .. Max_Stream_Len with Size => 64;

   --  A default-initialized context is inactive and empty (proved from the
   --  defaults of the full type and the two expression functions below).
   type Blake2b_Context is limited private
     with Default_Initial_Condition =>
            not Is_Active (Blake2b_Context)
            and then Absorbed (Blake2b_Context) = 0;

   --  True between Init and Final (or Wipe). A context that is
   --  default-initialized, finished or wiped is not active. You must pass it
   --  to Init again. crypto_blake2b_final wipes the C context, so a second
   --  use is undefined in C. Here, the precondition refuses it.
   function Is_Active (Ctx : Blake2b_Context) return Boolean
     with Global => null;

   --  Bytes absorbed since Init (0 when not active).
   function Absorbed (Ctx : Blake2b_Context) return Stream_Len
     with Global => null;

   --  crypto_blake2b_init (ctx, 32).
   procedure Init (Ctx : out Blake2b_Context)
     with Global => null,
          Post   => Is_Active (Ctx) and then Absorbed (Ctx) = 0;

   --  crypto_blake2b_update (ctx, data, len). Bounded: the precondition
   --  refuses a chunk that would take the stream past Max_Stream_Len (T13
   --  style: bounds are preconditions, never a silent wrap).
   procedure Update (Ctx : in out Blake2b_Context; Data : Byte_Array)
     with Global => null,
          Pre    => Is_Active (Ctx)
                    and then Data'Length <= Max_Data_Len
                    and then Stream_Len (Data'Length)
                             <= Max_Stream_Len - Absorbed (Ctx),
          Post   => Absorbed (Ctx)
                      = Absorbed (Ctx)'Old + Stream_Len (Data'Length)
                    and then Is_Active (Ctx);

   --  crypto_blake2b_final (ctx, hash): the digest of each byte absorbed
   --  since Init. This wipes the C context, and the Ada context becomes
   --  inactive.
   procedure Final (Ctx : in out Blake2b_Context; Digest : out Hash256)
     with Global => null,
          Pre    => Is_Active (Ctx),
          Post   => not Is_Active (Ctx) and then Absorbed (Ctx) = 0;

   --  Discard a context and make no digest. This does crypto_wipe over the
   --  C state. The state holds the chaining value and up to one block of
   --  absorbed input, which is a secret when the input is an epoch key. Wipe
   --  is allowed in any state. If a caller hashes secrets incrementally and
   --  can stop early, it calls Wipe.
   procedure Wipe (Ctx : in out Blake2b_Context)
     with Global => null,
          Post   => not Is_Active (Ctx) and then Absorbed (Ctx) = 0;

   ---------------------------------------------------------------------------
   --  Ed25519 (RFC 8032, monocypher-ed25519 crypto_ed25519_*)
   ---------------------------------------------------------------------------

   --  P is the canonical RFC 8032 §5.1.2 encoding of an Edwards point, to
   --  the extent that the bytes alone decide it (§5.1.3 decoding steps 1
   --  and 4). The y-coordinate (bits 0 .. 254, little-endian) is below
   --  p = 2**255 - 19, and the sign bit (bit 255) is clear when x = 0. The
   --  only points with x = 0 are y = 1 (the identity) and y = p - 1 (the
   --  point of order 2), so the second condition is also a byte
   --  comparison.
   --
   --  The check that y is on the curve (step 3) needs a square root.
   --  crypto_ed25519_check does that check, and it refuses such encodings.
   --  ge_tobytes is canonical, so each public key and each R that monocypher
   --  makes is canonical. The function has no quantifier, so it is public
   --  (CONVENTIONS.md rule 2).
   function Is_Canonical_Point (P : Pubkey) return Boolean is
     (--  y < p: not (the top byte of y is 16#7F#, bytes 30 .. 1 are all
      --  16#FF#, and byte 0 >= 16#ED#)
      ((P (31) and 16#7F#) /= 16#7F#
       or else P (30) /= 16#FF# or else P (29) /= 16#FF# or else P (28) /= 16#FF#
       or else P (27) /= 16#FF# or else P (26) /= 16#FF# or else P (25) /= 16#FF#
       or else P (24) /= 16#FF# or else P (23) /= 16#FF# or else P (22) /= 16#FF#
       or else P (21) /= 16#FF# or else P (20) /= 16#FF# or else P (19) /= 16#FF#
       or else P (18) /= 16#FF# or else P (17) /= 16#FF# or else P (16) /= 16#FF#
       or else P (15) /= 16#FF# or else P (14) /= 16#FF# or else P (13) /= 16#FF#
       or else P (12) /= 16#FF# or else P (11) /= 16#FF# or else P (10) /= 16#FF#
       or else P (9) /= 16#FF# or else P (8) /= 16#FF# or else P (7) /= 16#FF#
       or else P (6) /= 16#FF# or else P (5) /= 16#FF# or else P (4) /= 16#FF#
       or else P (3) /= 16#FF# or else P (2) /= 16#FF# or else P (1) /= 16#FF#
       or else P (0) < 16#ED#)
      and then
      --  not (sign bit set and (y = 1 or y = p - 1))
      (P (31) < 16#80#
       or else not
         ((P (0) = 16#01# and then P (31) = 16#80#
           and then P (1) = 0 and then P (2) = 0 and then P (3) = 0
           and then P (4) = 0 and then P (5) = 0 and then P (6) = 0
           and then P (7) = 0 and then P (8) = 0 and then P (9) = 0
           and then P (10) = 0 and then P (11) = 0 and then P (12) = 0
           and then P (13) = 0 and then P (14) = 0 and then P (15) = 0
           and then P (16) = 0 and then P (17) = 0 and then P (18) = 0
           and then P (19) = 0 and then P (20) = 0 and then P (21) = 0
           and then P (22) = 0 and then P (23) = 0 and then P (24) = 0
           and then P (25) = 0 and then P (26) = 0 and then P (27) = 0
           and then P (28) = 0 and then P (29) = 0 and then P (30) = 0)
          or else
          (P (0) = 16#EC# and then P (31) = 16#FF#
           and then P (1) = 16#FF# and then P (2) = 16#FF# and then P (3) = 16#FF#
           and then P (4) = 16#FF# and then P (5) = 16#FF# and then P (6) = 16#FF#
           and then P (7) = 16#FF# and then P (8) = 16#FF# and then P (9) = 16#FF#
           and then P (10) = 16#FF# and then P (11) = 16#FF# and then P (12) = 16#FF#
           and then P (13) = 16#FF# and then P (14) = 16#FF# and then P (15) = 16#FF#
           and then P (16) = 16#FF# and then P (17) = 16#FF# and then P (18) = 16#FF#
           and then P (19) = 16#FF# and then P (20) = 16#FF# and then P (21) = 16#FF#
           and then P (22) = 16#FF# and then P (23) = 16#FF# and then P (24) = 16#FF#
           and then P (25) = 16#FF# and then P (26) = 16#FF# and then P (27) = 16#FF#
           and then P (28) = 16#FF# and then P (29) = 16#FF# and then P (30) = 16#FF#))))
     with Global => null;

   --  The 8-torsion subgroup of the Ed25519 curve (AUDIT.md H13). The
   --  curve group has order 8 L. Its points of order 1, 2, 4 and 8 form a
   --  cyclic subgroup of order 8, and these are their canonical RFC 8032
   --  §5.1.2 encodings (y little-endian, the sign of x in bit 255):
   --    order 1   y = 1,     x = 0           0100..00
   --    order 2   y = p - 1, x = 0           ecff..ff7f
   --    order 4   y = 0,     x = ±sqrt(-1)   0000..00 and 0000..0080
   --    order 8   y = y8,    x = ±x8         26e8958f..fc05 and ..fc85
   --    order 8   y = p - y8, x = ±x8'       c7176a70..037a and ..03fa
   --  with y8 = 0x05fc536d880238b13933c6d305acdfd5f098eff289f4c345b027b2c28f
   --  95e826 (the order-8 points satisfy x^2 = -y^2, so d y^4 + 2 y^2 - 1 =
   --  0). The encodings 0100..0080 and ecff..ffff (x = 0 with the sign bit
   --  set) are not canonical, and Is_Canonical_Point refuses them. These
   --  are the eight "SmallOrderPublicKey" keys of Wycheproof ed25519_test.json
   --  (tcIds 152-159) and the small-order list of "Taming the many EdDSAs"
   --  (ed25519-speccheck) and of libsodium (ge25519_has_small_order, which
   --  also lists the non-canonical forms). The derivation is repeated in
   --  tests/test_crypto.adb's vectors (vectors/crypto.txt, ed25519_small_order).
   Torsion_8_A : constant Pubkey :=
     [16#26#, 16#E8#, 16#95#, 16#8F#, 16#C2#, 16#B2#, 16#27#, 16#B0#,
      16#45#, 16#C3#, 16#F4#, 16#89#, 16#F2#, 16#EF#, 16#98#, 16#F0#,
      16#D5#, 16#DF#, 16#AC#, 16#05#, 16#D3#, 16#C6#, 16#33#, 16#39#,
      16#B1#, 16#38#, 16#02#, 16#88#, 16#6D#, 16#53#, 16#FC#, 16#05#];
   Torsion_8_B : constant Pubkey :=
     [16#C7#, 16#17#, 16#6A#, 16#70#, 16#3D#, 16#4D#, 16#D8#, 16#4F#,
      16#BA#, 16#3C#, 16#0B#, 16#76#, 16#0D#, 16#10#, 16#67#, 16#0F#,
      16#2A#, 16#20#, 16#53#, 16#FA#, 16#2C#, 16#39#, 16#CC#, 16#C6#,
      16#4E#, 16#C7#, 16#FD#, 16#77#, 16#92#, 16#AC#, 16#03#, 16#7A#];
   Identity_Point : constant Pubkey := [0 => 1, others => 0];
   Order_2_Point  : constant Pubkey := [0 => 16#EC#, 31 => 16#7F#, others => 16#FF#];
   Order_4_Point  : constant Pubkey := [others => 0];   --  the all-zero key

   --  P is one of the 8 canonical small-order encodings above. A signature
   --  under such a public key is a universal forgery (see the header), so
   --  Verify refuses it, and Kome.Records refuses such a key as a root, a
   --  signer or a GRANT subject (H13). The function has no quantifier, so
   --  it is public. It reads bytes only, so decode stays total.
   function Is_Small_Order_Point (P : Pubkey) return Boolean is
     ((Same_Low_31 (P, Order_4_Point)
       and then (P (31) = 0 or else P (31) = 16#80#))
      or else Same_Bytes (P, Identity_Point)
      or else Same_Bytes (P, Order_2_Point)
      or else (Same_Low_31 (P, Torsion_8_A)
               and then (P (31) = 16#05# or else P (31) = 16#85#))
      or else (Same_Low_31 (P, Torsion_8_B)
               and then (P (31) = 16#7A# or else P (31) = 16#FA#)))
     with Global => null;

   --  The public key that crypto_ed25519_key_pair derives from a seed
   --  (RFC 8032 §5.1.5). It runs crypto_ed25519_key_pair on a copy of S,
   --  and it wipes the copy and the 64-byte secret that it made. It is
   --  total: it is a pure function of its argument, and Is_Valid names it
   --  on the (zero) seed of a wiped key.
   function Derive_Public (S : Seed) return Pubkey
     with Global => null,
          Post   => Is_Canonical_Point (Derive_Public'Result);

   --  Derive_Public of the all-zero seed (AUDIT.md A27): the public key of a
   --  secret that everybody knows. Computed once, independently of
   --  monocypher, with RFC 8032 §5.1.5 in plain Python integers (SHA-512 of
   --  32 zero bytes, clamped, times the base point) and cross-checked with
   --  pyca/cryptography Ed25519PrivateKey.from_private_bytes (bytes (32)).
   --  The test main checks it against the live Derive_Public. Kome.Records
   --  refuses it as a root, a signer or a GRANT subject.
   Zero_Seed_Public : constant Pubkey :=
     [16#3B#, 16#6A#, 16#27#, 16#BC#, 16#CE#, 16#B6#, 16#A4#, 16#2D#,
      16#62#, 16#A3#, 16#A8#, 16#D0#, 16#2A#, 16#6F#, 16#0D#, 16#73#,
      16#65#, 16#32#, 16#15#, 16#77#, 16#1D#, 16#E2#, 16#43#, 16#A6#,
      16#3A#, 16#C0#, 16#48#, 16#A1#, 16#8B#, 16#59#, 16#DA#, 16#29#];

   function Is_Zero_Seed_Public (P : Pubkey) return Boolean is
     (Same_Bytes (P, Zero_Seed_Public))
     with Global => null;

   --  A signing key: monocypher's 64-byte secret key (seed ‖ public key)
   --  plus a validity flag. The type is private and limited, so only
   --  Key_Pair can make a valid key. Key_Pair derives the public half from
   --  the seed. crypto_ed25519_sign hashes the public half into the
   --  challenge and does not check it, but its nonce depends only on the
   --  seed. If the halves of a key disagree, two signatures of one
   --  message leak the private scalar (the "double public key" oracle).
   --
   --  The type prevents this, and Is_Valid states it. A default-initialized
   --  key is not valid (the DIC, proved from the defaults of the full type
   --  and from the expression of Is_Valid).
   type Secret_Key is limited private
     with Default_Initial_Condition => not Is_Valid (Secret_Key);

   --  The seed half (the first 32 bytes of monocypher's secret key).
   --  Ghost: it exists for the contracts. No executable code can read the
   --  secret seed back from a key, so no function result or temporary ever
   --  holds a copy. If a device stores its signing key persistently, it
   --  stores the seed that it gave to Key_Pair (and then wipes its own
   --  copy).
   function Seed_Of (SK : Secret_Key) return Seed
     with Ghost, Global => null;

   --  The public half (the last 32 bytes of monocypher's secret key).
   function Public_Of (SK : Secret_Key) return Pubkey
     with Global => null;

   --  True for a key that Key_Pair made and that no Wipe cleared after
   --  that. Ghost: only contracts use it (the Pre of Sign, the Sign Pres of
   --  Kome.Records). Its completion is an expression function in the
   --  private part (the flag, and the public half derived from the seed
   --  half), so gnatprove proves its Post and the DIC above. At run time
   --  (-gnata), each evaluation of it derives the public key once.
   function Is_Valid (SK : Secret_Key) return Boolean
     with Ghost, Global => null,
          Post   => (if Is_Valid'Result
                     then Public_Of (SK) = Derive_Public (Seed_Of (SK)));

   --  crypto_ed25519_key_pair (sk, pk, seed). The C call wipes its seed
   --  argument, so the binding gives it a copy, and S does not change (it
   --  is an `in` parameter). Pre: the seed is not all zeros (AUDIT.md A27:
   --  an all-zero seed is a publicly known key, Zero_Seed_Public). Post:
   --  the key is valid and holds S, and PK is its public half and the key
   --  derived from S.
   procedure Key_Pair (S : Seed; SK : out Secret_Key; PK : out Pubkey)
     with Global => null,
          Pre    => not Is_Zero (S),
          Post   => Is_Valid (SK)
                    and then Seed_Of (SK) = S
                    and then Public_Of (SK) = PK
                    and then PK = Derive_Public (S)
                    and then Is_Canonical_Point (PK);

   --  crypto_wipe over the 64-byte secret key. After the call, the key is
   --  invalid and both halves are zero.
   procedure Wipe (SK : in out Secret_Key)
     with Global => null,
          Post   => not Is_Valid (SK)
                    and then (for all B of Seed_Of (SK) => B = 0)
                    and then (for all B of Public_Of (SK) => B = 0);

   --  S < L for the scalar half of a signature. L = 2**252 +
   --  27742317777372353535851937790883648493 is the group order, and S is
   --  little-endian in bytes 32 .. 63. crypto_ed25519_check refuses S >= L
   --  ("prevents malleability"), so for a given public key, message and
   --  R, at most one signature encoding verifies. The function has no
   --  quantifier: it is a chain of byte comparisons from the most
   --  significant byte down, as Kome.Lt is for words, so a caller's prover
   --  can unfold it.
   function S_Below_L (S : Sig) return Boolean is
     (S (63) < 16#10# or else
      (S (63) = 16#10#
       and then S (62) = 0 and then S (61) = 0 and then S (60) = 0
       and then S (59) = 0 and then S (58) = 0 and then S (57) = 0
       and then S (56) = 0 and then S (55) = 0 and then S (54) = 0
       and then S (53) = 0 and then S (52) = 0 and then S (51) = 0
       and then S (50) = 0 and then S (49) = 0 and then S (48) = 0
       and then
      (S (47) < 16#14# or else (S (47) = 16#14# and then
      (S (46) < 16#DE# or else (S (46) = 16#DE# and then
      (S (45) < 16#F9# or else (S (45) = 16#F9# and then
      (S (44) < 16#DE# or else (S (44) = 16#DE# and then
      (S (43) < 16#A2# or else (S (43) = 16#A2# and then
      (S (42) < 16#F7# or else (S (42) = 16#F7# and then
      (S (41) < 16#9C# or else (S (41) = 16#9C# and then
      (S (40) < 16#D6# or else (S (40) = 16#D6# and then
      (S (39) < 16#58# or else (S (39) = 16#58# and then
      (S (38) < 16#12# or else (S (38) = 16#12# and then
      (S (37) < 16#63# or else (S (37) = 16#63# and then
      (S (36) < 16#1A# or else (S (36) = 16#1A# and then
      (S (35) < 16#5C# or else (S (35) = 16#5C# and then
      (S (34) < 16#F5# or else (S (34) = 16#F5# and then
      (S (33) < 16#D3# or else (S (33) = 16#D3# and then
       S (32) < 16#ED#))))))))))))))))))))))))))))))))
     with Global => null;

   --  crypto_ed25519_sign (sig, sk, msg, len). It is deterministic (RFC 8032
   --  §5.1.6), so it is a function. DESIGN.md §2: sig = Ed25519 (h) over the
   --  32-byte content hash. Pre: a key that Key_Pair made (Secret_Key tells
   --  why this is important). Post: the scalar is reduced mod L and R is
   --  canonical. Verify requires both.
   function Sign (SK : Secret_Key; Msg : Byte_Array) return Sig
     with Global => null,
          Pre    => Is_Valid (SK) and then Msg'Length <= Max_Data_Len,
          Post   => S_Below_L (Sign'Result)
                    and then Is_Canonical_Point (Sign'Result (0 .. 31));

   --  Strict RFC 8032 verification (see the header): S < L, canonical
   --  R and PK, PK not small-order, then crypto_ed25519_check (sig, pk,
   --  msg, len) = 0. DESIGN.md §2: a record is well-formed iff its bounds
   --  hold and its signature verifies. This is a function of its bytes
   --  alone, so Verify is a function with Global => null. A1 is the
   --  assumption that True means that the holder of PK's secret key signed
   --  Msg. Verify is an expression function (its completion is in the
   --  private part, after Raw_Ed25519_Check), so gnatprove proves the Post
   --  from the definition (AUDIT.md A25). Clients can see the definition
   --  (CONVENTIONS.md "Proof hygiene": a private-part completion is
   --  visible); it has no quantifier, so that costs them nothing.
   function Verify (Signature : Sig; PK : Pubkey; Msg : Byte_Array) return Boolean
     with Global => null,
          Pre    => Msg'Length <= Max_Data_Len,
          Post   => (if Verify'Result
                     then S_Below_L (Signature)
                          and then Is_Canonical_Point (Signature (0 .. 31))
                          and then Is_Canonical_Point (PK)
                          and then not Is_Small_Order_Point (PK));

   ---------------------------------------------------------------------------
   --  X25519 (RFC 7748)
   ---------------------------------------------------------------------------

   --  An X25519 output is a u-coordinate reduced mod 2**255 - 19 and
   --  encoded little-endian (RFC 7748 §5, encodeUCoordinate), so its top
   --  bit is clear. monocypher's fe_tobytes emits the canonical encoding.
   function Is_Canonical_U (U : Pubkey) return Boolean is (U (31) < 16#80#)
     with Global => null;

   --  U is the reduced little-endian encoding of a field element: bit 255
   --  is clear (Is_Canonical_U) and u < p = 2**255 - 19. That is, U is not
   --  one of the 19 encodings 16#7FFF...FFED# .. 16#7FFF...FFFF#. These are
   --  exactly the outputs of X25519_Public (monocypher fully reduces), so an
   --  honest dh_pk or box_pk always passes. The function has no quantifier,
   --  so it is public. DESIGN.md §2 rule 3, E5.
   function Is_Reduced_U (U : Pubkey) return Boolean is
     (U (31) < 16#7F#
      or else (U (31) = 16#7F#
               and then (U (30) /= 16#FF# or else U (29) /= 16#FF# or else U (28) /= 16#FF#
                         or else U (27) /= 16#FF# or else U (26) /= 16#FF# or else U (25) /= 16#FF#
                         or else U (24) /= 16#FF# or else U (23) /= 16#FF# or else U (22) /= 16#FF#
                         or else U (21) /= 16#FF# or else U (20) /= 16#FF# or else U (19) /= 16#FF#
                         or else U (18) /= 16#FF# or else U (17) /= 16#FF# or else U (16) /= 16#FF#
                         or else U (15) /= 16#FF# or else U (14) /= 16#FF# or else U (13) /= 16#FF#
                         or else U (12) /= 16#FF# or else U (11) /= 16#FF# or else U (10) /= 16#FF#
                         or else U (9) /= 16#FF# or else U (8) /= 16#FF# or else U (7) /= 16#FF#
                         or else U (6) /= 16#FF# or else U (5) /= 16#FF# or else U (4) /= 16#FF#
                         or else U (3) /= 16#FF# or else U (2) /= 16#FF# or else U (1) /= 16#FF#
                         or else U (0) < 16#ED#)))
     with Global => null;

   --  U is one of the five reduced encodings of a low-order X25519 point
   --  (DESIGN.md §2 rule 3, E5). The comparison is bytewise:
   --    u = 0        0000000000000000000000000000000000000000000000000000000000000000
   --    u = 1        0100000000000000000000000000000000000000000000000000000000000000
   --    order 8      e0eb7a7c3b41b8ae1656e3faf19fc46ada098deb9c32b1fd866205165f49b800
   --    order 8      5f9c95bca3508c24b1d0b1559c83ef5b04445cc4581c8e86d8224eddd09f1157
   --    u = p - 1    ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f
   --  (This is libsodium's blocklist without its non-reduced entries,
   --  which Is_Reduced_U already refuses.) For each of these points, each
   --  secret gives an all-zero shared secret (X25519 reports Contributory =
   --  False). The function has no quantifier, so it is public.
   function Is_Low_Order_U (U : Pubkey) return Boolean is
     (Is_Zero (U)
      or else
      (U (0) = 16#01# and then U (1) = 0 and then U (2) = 0 and then U (3) = 0
       and then U (4) = 0 and then U (5) = 0 and then U (6) = 0 and then U (7) = 0
       and then U (8) = 0 and then U (9) = 0 and then U (10) = 0 and then U (11) = 0
       and then U (12) = 0 and then U (13) = 0 and then U (14) = 0 and then U (15) = 0
       and then U (16) = 0 and then U (17) = 0 and then U (18) = 0 and then U (19) = 0
       and then U (20) = 0 and then U (21) = 0 and then U (22) = 0 and then U (23) = 0
       and then U (24) = 0 and then U (25) = 0 and then U (26) = 0 and then U (27) = 0
       and then U (28) = 0 and then U (29) = 0 and then U (30) = 0 and then U (31) = 0)
      or else
      (U (0) = 16#E0# and then U (1) = 16#EB# and then U (2) = 16#7A# and then U (3) = 16#7C#
       and then U (4) = 16#3B# and then U (5) = 16#41# and then U (6) = 16#B8# and then U (7) = 16#AE#
       and then U (8) = 16#16# and then U (9) = 16#56# and then U (10) = 16#E3# and then U (11) = 16#FA#
       and then U (12) = 16#F1# and then U (13) = 16#9F# and then U (14) = 16#C4# and then U (15) = 16#6A#
       and then U (16) = 16#DA# and then U (17) = 16#09# and then U (18) = 16#8D# and then U (19) = 16#EB#
       and then U (20) = 16#9C# and then U (21) = 16#32# and then U (22) = 16#B1# and then U (23) = 16#FD#
       and then U (24) = 16#86# and then U (25) = 16#62# and then U (26) = 16#05# and then U (27) = 16#16#
       and then U (28) = 16#5F# and then U (29) = 16#49# and then U (30) = 16#B8# and then U (31) = 16#00#)
      or else
      (U (0) = 16#5F# and then U (1) = 16#9C# and then U (2) = 16#95# and then U (3) = 16#BC#
       and then U (4) = 16#A3# and then U (5) = 16#50# and then U (6) = 16#8C# and then U (7) = 16#24#
       and then U (8) = 16#B1# and then U (9) = 16#D0# and then U (10) = 16#B1# and then U (11) = 16#55#
       and then U (12) = 16#9C# and then U (13) = 16#83# and then U (14) = 16#EF# and then U (15) = 16#5B#
       and then U (16) = 16#04# and then U (17) = 16#44# and then U (18) = 16#5C# and then U (19) = 16#C4#
       and then U (20) = 16#58# and then U (21) = 16#1C# and then U (22) = 16#8E# and then U (23) = 16#86#
       and then U (24) = 16#D8# and then U (25) = 16#22# and then U (26) = 16#4E# and then U (27) = 16#DD#
       and then U (28) = 16#D0# and then U (29) = 16#9F# and then U (30) = 16#11# and then U (31) = 16#57#)
      or else
      (U (0) = 16#EC# and then U (1) = 16#FF# and then U (2) = 16#FF# and then U (3) = 16#FF#
       and then U (4) = 16#FF# and then U (5) = 16#FF# and then U (6) = 16#FF# and then U (7) = 16#FF#
       and then U (8) = 16#FF# and then U (9) = 16#FF# and then U (10) = 16#FF# and then U (11) = 16#FF#
       and then U (12) = 16#FF# and then U (13) = 16#FF# and then U (14) = 16#FF# and then U (15) = 16#FF#
       and then U (16) = 16#FF# and then U (17) = 16#FF# and then U (18) = 16#FF# and then U (19) = 16#FF#
       and then U (20) = 16#FF# and then U (21) = 16#FF# and then U (22) = 16#FF# and then U (23) = 16#FF#
       and then U (24) = 16#FF# and then U (25) = 16#FF# and then U (26) = 16#FF# and then U (27) = 16#FF#
       and then U (28) = 16#FF# and then U (29) = 16#FF# and then U (30) = 16#FF# and then U (31) = 16#7F#))
     with Global => null;

   --  The X25519 keys that Kome accepts at decode (DESIGN.md §2 rule 3, E5).
   --  The box_pk of a ROSTER and each member dh_pk are reduced and not low
   --  order, so each listed member can open its box. Kome.Records checks
   --  this at decode. Kome.Epochs checks the two conjuncts (Is_Reduced_U,
   --  then Is_Low_Order_U) before each box and unbox operation.
   function Is_Good_DH_Key (U : Pubkey) return Boolean is
     (Is_Reduced_U (U) and then not Is_Low_Order_U (U))
     with Global => null;

   --  crypto_x25519_public_key (pk, sk): the member's `dh_pk`
   --  (DESIGN.md §2 ROSTER members[] { sign_pk dh_pk ... }).
   function X25519_Public (Secret : DH_Secret) return Pubkey
     with Global => null,
          Post   => Is_Canonical_U (X25519_Public'Result);

   --  X25519_Public of the all-zero secret (AUDIT.md A27): the public key of
   --  a secret that everybody knows. RFC 7748 clamps the scalar, so it is
   --  [2**254] of the base point u = 9, a good DH key by Is_Good_DH_Key.
   --  Computed once, independently of monocypher, with the RFC 7748 §5
   --  ladder in plain Python integers and cross-checked with
   --  pyca/cryptography X25519PrivateKey.from_private_bytes (bytes (32)).
   --  The test main checks it against the live X25519_Public. Kome.Records
   --  refuses it as a box_pk.
   Zero_Secret_DH_Public : constant Pubkey :=
     [16#2F#, 16#E5#, 16#7D#, 16#A3#, 16#47#, 16#CD#, 16#62#, 16#43#,
      16#15#, 16#28#, 16#DA#, 16#AC#, 16#5F#, 16#BB#, 16#29#, 16#07#,
      16#30#, 16#FF#, 16#F6#, 16#84#, 16#AF#, 16#C4#, 16#CF#, 16#C2#,
      16#ED#, 16#90#, 16#99#, 16#5F#, 16#58#, 16#CB#, 16#3B#, 16#74#];

   function Is_Zero_Secret_DH_Public (U : Pubkey) return Boolean is
     (Same_Bytes (U, Zero_Secret_DH_Public))
     with Global => null;

   --  crypto_x25519 (shared, your_sk, their_pk): the raw shared secret,
   --  written into the caller's buffer. It is a secret, so the caller wipes
   --  it. monocypher's note applies: the secret is not uniformly random, so
   --  hash it before you use it as a key. If Their_Public has
   --  low order (u = 0, u = 1, the order-8 points, or their non-canonical
   --  encodings), each secret gives all zeros.
   --
   --  The exchange is then not contributory: the peer alone has fixed the
   --  "shared" key. Contributory reports this. If a caller wraps or unwraps
   --  a ROSTER box (DESIGN.md §6), it must refuse when Contributory is
   --  False, and it can prove that it did. Decode refuses such keys earlier
   --  (Is_Good_DH_Key).
   procedure X25519
     (Secret       : DH_Secret;
      Their_Public : Pubkey;
      Shared       : out Shared_Secret;
      Contributory : out Boolean)
     with Global => null,
          Post   => Is_Canonical_U (Shared)
                    and then Contributory = not Is_Zero (Shared)
                    and then Shared = X25519_Shared (Secret, Their_Public);

   --  The same shared secret as a function, for contracts only (Ghost).
   --  It lets a client's Post name a key derived from the exchange
   --  (Kome.Epochs: the wrap key and the synthetic nonce of a member box,
   --  DESIGN.md §6 D6). Because it is Ghost, executable code never holds the
   --  secret in a function-result temporary. Under -gnata it runs the same
   --  C call as X25519, and the Post above checks that both agree.
   function X25519_Shared (Secret : DH_Secret; Their_Public : Pubkey) return Shared_Secret
     with Ghost, Global => null;

   --  Congruence of the two X25519 functions: they read only the bytes of
   --  the secret, so two secrets with the same bytes give the same public
   --  key and the same shared secret. This is true of each function of a
   --  byte string, but the prover has no array extensionality (see
   --  Lemma_Blake2b_Congruent): a secret computed into a buffer and the
   --  ghost term that models it are different terms with equal elements.
   --  Kome.Epochs uses it to carry the derived eph_sk (a wiped buffer) to
   --  its ghost model Eph_Secret_Of (AUDIT.md A6, G7).
   --
   --  The body is SPARK_Mode Off like each other body here, so the Post is
   --  an AXIOM of the same kind as Lemma_Blake2b_Congruent. The test main
   --  checks it under -gnata.
   procedure Lemma_X25519_Congruent (A, B : DH_Secret; Their_Public : Pubkey)
     with Ghost, Global => null, Always_Terminates,
          Pre  => A = B,
          Post => X25519_Public (A) = X25519_Public (B)
                  and then X25519_Shared (A, Their_Public)
                           = X25519_Shared (B, Their_Public);

   ---------------------------------------------------------------------------
   --  XChaCha20-Poly1305 AEAD (crypto_aead_lock / crypto_aead_unlock)
   ---------------------------------------------------------------------------

   --  crypto_aead_lock (cipher, mac, key, nonce, ad, ad_len, plain, len).
   --  Cipher has exactly the length of Plain (a stream cipher), and Mac
   --  authenticates AD and Cipher. SPARK's anti-aliasing rule forbids
   --  one buffer as both Plain and Cipher, so the binding never uses the C
   --  in-place mode. There is no Post: the only output facts are the
   --  lengths, and the Pre fixes them (the bounds of an out parameter cannot
   --  change), so a Post would be vacuous. monocypher guarantees that Unlock
   --  inverts Lock, and the test main runs it.
   procedure Lock
     (Key    : AEAD_Key;
      N      : Nonce;
      AD     : Byte_Array;
      Plain  : Byte_Array;
      Cipher : out Byte_Array;
      Mac    : out Tag)
     with Global => null,
          Pre    => AD'Length <= Max_Data_Len
                    and then Plain'Length <= Max_Data_Len
                    and then Cipher'Length = Plain'Length;

   --  crypto_aead_unlock (...) = 0. If the message is forged or corrupted
   --  (Authentic = False), monocypher writes nothing, and the binding then
   --  sets Plain to zeros, so a refused message never leaves plaintext or
   --  stale bytes behind (the Post). On success, Plain is the decryption of
   --  Cipher.
   procedure Unlock
     (Key       : AEAD_Key;
      N         : Nonce;
      AD        : Byte_Array;
      Cipher    : Byte_Array;
      Mac       : Tag;
      Plain     : out Byte_Array;
      Authentic : out Boolean)
     with Global => null,
          Pre    => AD'Length <= Max_Data_Len
                    and then Cipher'Length <= Max_Data_Len
                    and then Plain'Length = Cipher'Length,
          Post   => (if not Authentic
                     then (for all I in Plain'Range => Plain (I) = 0));

   ---------------------------------------------------------------------------
   --  Erasure
   ---------------------------------------------------------------------------

   --  crypto_wipe (buf, len): set a secret (a seed, a shared secret, an
   --  epoch key, a plaintext) to zero in a way that the C compiler does not
   --  elide. The Ada compiler cannot elide the call either, because the
   --  package is not Pure (see the header).
   --
   --  The object that the call erases: Byte_Array is not a by-reference
   --  type, and RM 6.2(11) leaves the mechanism of B unspecified. GNAT
   --  passes an unconstrained array formal such as B by reference (a
   --  pointer to the actual's data, plus its bounds), so B'Address is the
   --  caller's buffer. The check wipe_zeroes in test_crypto examines the
   --  caller's object after the call. If you port the
   --  code to another compiler, you must check this again (or give B an
   --  explicitly aliased mode).
   --
   --  For callers: gnatprove's flow analysis reports a Wipe of a local
   --  that is never read again as "statement has no effect" / "set by Wipe
   --  but not used after the call". That is the purpose of the call.
   --  Silence the warning locally with pragma Warnings (Off, "statement has
   --  no effect") and a Reason. Do not remove the call. Data and flow
   --  dependencies stay as Global => null states them, because the erasure
   --  of memory is not an effect that the SPARK model can observe.
   procedure Wipe (B : out Byte_Array)
     with Global => null, Always_Terminates,
          Pre    => B'Length <= Max_Data_Len,
          Post   => (for all I in B'Range => B (I) = 0);

private

   --  Storage for monocypher's crypto_blake2b_ctx. The monocypher
   --  header says not to depend on its layout. On LP64 it is 8 + 2 + 16
   --  words of uint64_t plus two size_t, 28 words. 32 words of U64 hold it
   --  with room and give it uint64_t alignment. The body checks the size at
   --  compile time against a Convention C mirror of the struct in the
   --  header.
   Ctx_Words : constant := 32;
   type Ctx_Storage is array (0 .. Ctx_Words - 1) of U64;

   --  Explicitly limited, thus by-reference (RM 6.2(4), 6.2(7)): see the
   --  header.
   type Blake2b_Context is limited record
      Raw    : Ctx_Storage := [others => 0];
      Active : Boolean     := False;
      Count  : Stream_Len  := 0;
   end record;

   function Is_Active (Ctx : Blake2b_Context) return Boolean is (Ctx.Active);
   function Absorbed (Ctx : Blake2b_Context) return Stream_Len is (Ctx.Count);

   --  monocypher's secret_key[64] = seed ‖ public key. Explicitly
   --  limited, thus by-reference (RM 6.2(4), 6.2(7)).
   type Secret_Key is limited record
      Raw   : Byte_Array (0 .. Secret_Key_Len - 1) := [others => 0];
      Valid : Boolean := False;
   end record;

   function Seed_Of (SK : Secret_Key) return Seed is
     (SK.Raw (0 .. Seed_Len - 1));
   function Public_Of (SK : Secret_Key) return Pubkey is
     (SK.Raw (Seed_Len .. Secret_Key_Len - 1));

   --  Valid means: Key_Pair made the key and no Wipe cleared it (the flag),
   --  and the public half is the one derived from the seed half. Key_Pair
   --  establishes both, and Wipe clears the flag (their Posts, assumed: the
   --  bodies are C). The second conjunct makes the Post above a consequence
   --  of the definition. The default flag makes the DIC a consequence too.
   function Is_Valid (SK : Secret_Key) return Boolean is
     (SK.Valid and then Public_Of (SK) = Derive_Public (Seed_Of (SK)));

   --  crypto_ed25519_check (sig, pk, msg, len) = 0, and nothing else: the
   --  cofactored group equation over whatever encodings monocypher
   --  accepts. It has no Post (AUDIT.md A25): its result is the C
   --  assumption A1, and Verify adds the SPARK encoding checks around it.
   --  It is private, so no client can call it without those checks.
   function Raw_Ed25519_Check
     (Signature : Sig; PK : Pubkey; Msg : Byte_Array) return Boolean
     with Global => null,
          Pre    => Msg'Length <= Max_Data_Len;

   --  Strict verification as a SPARK expression (the header, A25): the
   --  Post of Verify follows from this definition.
   function Verify (Signature : Sig; PK : Pubkey; Msg : Byte_Array) return Boolean is
     (S_Below_L (Signature)
      and then Is_Canonical_Point (Signature (0 .. 31))
      and then Is_Canonical_Point (PK)
      and then not Is_Small_Order_Point (PK)
      and then Raw_Ed25519_Check (Signature, PK, Msg));

end Kome.Crypto;
