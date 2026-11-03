--  Kome.Crypto: the thin binding to monocypher 4.0.2 (third_party/monocypher,
--  provenance in its README), the design's only cryptographic dependency
--  (DESIGN.md §2, §6, §8; CONVENTIONS.md "Cryptography": do not
--  reimplement, bind).
--
--    BLAKE2b-256      crypto_blake2b, crypto_blake2b_init/update/final with
--                     hash_size = 32. DESIGN.md §2 `ns`, `h`, the root
--                     certificate; §6 the epoch key chain and box keys; §8
--                     the accumulator and the bundle key and nonce.
--                     Assumption A2.
--    Ed25519          crypto_ed25519_key_pair / _sign / _check, from the
--                     optional monocypher-ed25519.c. DESIGN.md §2 `sig`,
--                     `cert_sig`. Assumption A1.
--    X25519           crypto_x25519_public_key, crypto_x25519. DESIGN.md §6
--                     (epoch key wrapped to each member's `dh_pk`).
--    XChaCha20-       crypto_aead_lock / _unlock: 32-byte key, 24-byte nonce,
--    Poly1305         16-byte tag. DESIGN.md §2 `nonce[24] box[48]`, §8
--                     sealed bundles. T14 (paper) rests on it.
--    Erasure          crypto_wipe, on byte buffers, signing keys and hash
--                     contexts.
--
--  SIGNATURE SCHEME (DECIDED: DESIGN.md §1.2 D4, §2, A1). Signatures are
--  RFC 8032 Ed25519 (PureEd25519), from monocypher's optional
--  monocypher-ed25519.c (crypto_ed25519_*). SHA-512 is used only inside the
--  signature: to expand the seed into the secret scalar and nonce prefix,
--  and to hash R ‖ A ‖ M into the challenge (RFC 8032 §5.1.5-5.1.7).
--  Nothing Kome derives uses SHA-512: BLAKE2b-256 stays the hash for h, ns,
--  certificates, the accumulator and every key derivation. monocypher's
--  core crypto_eddsa_* (EdDSA with BLAKE2b-512, the scheme of the previous
--  C++ engine and of Nano) is no longer bound; its signatures do not verify
--  here, and the test main checks that (regression vectors).
--
--  STRICT VERIFICATION (DESIGN.md §2 "strict: S < L"). Verify accepts a
--  signature only if (a) S < L, (b) R is the canonical RFC 8032 §5.1.2
--  encoding of a point and (c) so is PK, and then crypto_ed25519_check
--  accepts it. crypto_ed25519_check itself enforces (a), and refuses
--  encodings that are not on the curve, but by design allows the
--  non-canonical encodings y >= p and "x = 0 with the sign bit set"
--  (monocypher.c crypto_eddsa_check_equation: "*Allow* non-cannonical
--  encoding for A and R"). Wycheproof ed25519_test.json tcId 151 is such a
--  signature and crypto_ed25519_check accepts it, so the binding checks (b)
--  and (c) itself (Is_Canonical_Point), and the strictness is RFC 8032
--  §5.1.3's decoding rule. The group equation is monocypher's cofactored
--  one ([8][S]B = [8]R + [8][k]A, which RFC 8032 §5.1.7 permits).
--
--  SPARK boundary (CONVENTIONS.md, the one allowed exception): this spec is
--  SPARK_Mode On with full contracts, and the body is SPARK_Mode Off and
--  calls C through Interfaces.C. The Posts of the subprograms completed in
--  the body are therefore ASSUMED by gnatprove, not proved: they are
--  checked only by executing them (-gnata) against the known-answer vectors
--  and properties of tests/test_crypto.adb. That is inherent to binding C
--  and is the residual of the review finding "bodies are SPARK_Mode Off".
--  What the contracts state:
--    * input bounds, output lengths and layouts;
--    * the incremental context's state machine and byte count;
--    * that only Key_Pair makes a valid signing key, and that a valid key's
--      public half is the one derived from its seed (Is_Valid, an
--      expression function, so its Post and the default-key facts are
--      proved);
--    * strict verification: True implies S < L and canonical R and PK;
--    * that a non-contributory X25519 is reported, and which X25519 keys
--      Kome accepts at decode (Is_Good_DH_Key, E5);
--    * that a refused Unlock and every Wipe leave zeros;
--    * that BLAKE2b-256 depends only on the bytes of its input
--      (Lemma_Blake2b_Congruent, an axiom for the prover, run by the test
--      main), and that X25519 computes X25519_Shared (a ghost function, so
--      contracts can name keys derived from an exchange).
--  They do not state Verify (Sign (M)) or the hashing algebra. Those are A1
--  and A2, plus the known-answer vectors. The expression functions here
--  (S_Below_L, Is_Canonical_Point, Is_Reduced_U, Is_Low_Order_U, ...) are
--  SPARK and proved like any other code.
--
--  Every function here is a mathematical function of its arguments
--  (Ed25519 signing is deterministic, and nothing reads a clock or an RNG),
--  so the functions are SPARK functions with Global => null.
--
--  PREELABORATE, NOT PURE. RM 10.2.1(18) lets an implementation omit a
--  call to a library-level subprogram of a declared-pure unit when the
--  call's results are not needed afterwards. A Wipe just before a secret
--  goes out of scope is exactly such a call. The package is therefore
--  Preelaborate, so that permission never applies and a Wipe is an
--  ordinary call to C that must be executed. A unit that withs Kome.Crypto
--  can be Preelaborate but not Pure.
--
--  BY-REFERENCE SECRETS. Secret_Key and Blake2b_Context are limited
--  private types whose full types are explicitly limited records. By RM
--  6.2(4) and 6.2(7) such a record is a by-reference type, and by RM 6.2(9)
--  so is the private type whose full type it is. RM 6.2(10) then requires
--  every parameter of these types to be passed by reference, so a Wipe or
--  Final erases the caller's object itself and not a copy of it. Being
--  limited, they cannot be copied by assignment either. That is all the RM
--  promises: it does not stop the C code, or register allocation, from
--  leaving copies elsewhere, which is what crypto_wipe inside monocypher
--  is for. Byte_Array (an array of an elementary type) is not a
--  by-reference type, and RM 6.2(11) leaves its parameter mechanism
--  unspecified; see Wipe (B) for what is relied on there.
pragma Ada_2022;
package Kome.Crypto with SPARK_Mode, Preelaborate is

   ---------------------------------------------------------------------------
   --  Sizes (monocypher.h and monocypher-ed25519.h prototypes; DESIGN.md §2
   --  for those Kome names)
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

   --  The largest single buffer handed to monocypher, 1 MiB. It is declared
   --  here rather than in Kome (root), because this package owns only its
   --  own files. It is no longer tied to Value_Max (40_960 since D12). What
   --  the design feeds this package:
   --    * DESIGN.md §2: the largest hashed or signed input is a frame, at
   --      most 41_136 bytes (a PUT with a 32-byte field and a 40_960-byte
   --      value); a signature covers only the 32 bytes of h;
   --    * §8: a sealed-bundle plaintext is a list of ELEMENTS items
   --      totalling at most Max_Message_Len = 48 KiB; it is the AEAD
   --      plaintext, and its synthetic nonce hashes "kome/bnonce" ‖ k_b ‖
   --      plaintext, 43 bytes more (checked below, with 64 bytes of room);
   --    * §2, §6, §8: certificates, key derivations, box nonces and the
   --      accumulator hash under 1 KiB each (the largest is
   --      fp(R) = "kome/fp" ‖ u64 ‖ ACC_le(R), 7 + 8 + 512 bytes).
   --  2**20 covers all of these with room (about 21 times the bundle
   --  plaintext), and larger payloads are chunked above the engine (§2), so
   --  nothing larger reaches this package. The bound exists so that every
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
   --  No Post. The output length is fixed by the result subtype Hash256, a
   --  static fact that GNAT flags as a vacuous Post. Nothing else about a
   --  hash can be checked here: collision resistance is A2, and agreement
   --  with the incremental form and with RFC 7693 is covered by the test
   --  main's vectors.
   function Blake2b_256 (Data : Byte_Array) return Hash256
     with Global => null,
          Pre    => Data'Length <= Max_Data_Len;

   --  Congruence: BLAKE2b-256 reads only the bytes of its input, in order,
   --  so two inputs with the same bytes have the same digest, whatever
   --  their bounds. This is true of every function of a byte string, but
   --  the prover cannot see it: it has no array extensionality, and two
   --  arrays with equal elements and different bounds or different
   --  construction are different terms. The body is SPARK_Mode Off like
   --  every other one here, so the Post is an AXIOM (assumed, like the
   --  binding's other Posts); the test main checks it under -gnata on
   --  slices with different bounds. Clients use it to carry a hash across
   --  a copy or a re-slice (Kome.Records.Lemma_Header_Congruent,
   --  Kome.Epochs's wrap key).
   procedure Lemma_Blake2b_Congruent (A, B : Byte_Array)
     with Ghost, Global => null, Always_Terminates,
          Pre  => A'Length = B'Length
                  and then A'Length <= Max_Data_Len
                  and then (for all K in 0 .. A'Length - 1 =>
                              A (A'First + K) = B (B'First + K)),
          Post => Blake2b_256 (A) = Blake2b_256 (B);

   --  The same hash, written straight into the caller's buffer. Use this
   --  form when the digest is itself a secret, such as the epoch key chain
   --  k_e = BLAKE2b-256 (k_{e+1} ‖ "prev") of DESIGN.md §6, so that no
   --  function-result temporary holds a copy. The caller wipes Digest.
   --  Always_Terminates (one C call), so a function such as
   --  Kome.Epochs.Step can hash into a buffer it then wipes.
   procedure Blake2b_256 (Data : Byte_Array; Digest : out Hash256)
     with Global => null, Always_Terminates,
          Pre    => Data'Length <= Max_Data_Len,
          Post   => Digest = Blake2b_256 (Data);

   --  Incremental BLAKE2b-256: Init, any number of Update calls, then Final.
   --  The context is a bounded byte stream: at most Max_Stream_Len bytes in
   --  all, and each Update at most Max_Data_Len. monocypher counts in 128
   --  bits, so the bound is Kome's. It is chosen so that the count is a
   --  range type that cannot overflow (CONVENTIONS.md: semantic integers
   --  are range types). Feeding the same bytes in any chunking gives
   --  Blake2b_256 of their concatenation. That is monocypher's guarantee,
   --  and the test main runs it at every split point across the 128-byte
   --  block boundary. It is not a proof obligation, because it would need a
   --  ghost copy of an unbounded stream.
   Max_Stream_Len : constant := 2**62;
   type Stream_Len is range 0 .. Max_Stream_Len with Size => 64;

   --  A default-initialized context is inactive and empty (proved: the
   --  full type's defaults and the two expression functions below).
   type Blake2b_Context is limited private
     with Default_Initial_Condition =>
            not Is_Active (Blake2b_Context)
            and then Absorbed (Blake2b_Context) = 0;

   --  True between Init and Final (or Wipe). A default-initialized,
   --  finished or wiped context is not active and must be passed to Init
   --  again. crypto_blake2b_final wipes the C context, so using it again is
   --  undefined in C; here it is refused by precondition.
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
   --  refuses a chunk that would carry the stream past Max_Stream_Len (T13
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

   --  crypto_blake2b_final (ctx, hash): the digest of every byte absorbed
   --  since Init. The C context is wiped, and the Ada one becomes inactive.
   procedure Final (Ctx : in out Blake2b_Context; Digest : out Hash256)
     with Global => null,
          Pre    => Is_Active (Ctx),
          Post   => not Is_Active (Ctx) and then Absorbed (Ctx) = 0;

   --  Abandon a context without producing a digest: crypto_wipe over the C
   --  state, which holds the chaining value and up to one block of absorbed
   --  input (a secret, when hashing an epoch key). Allowed in any state.
   --  Callers that hash secrets incrementally and may stop early call this.
   procedure Wipe (Ctx : in out Blake2b_Context)
     with Global => null,
          Post   => not Is_Active (Ctx) and then Absorbed (Ctx) = 0;

   ---------------------------------------------------------------------------
   --  Ed25519 (RFC 8032, monocypher-ed25519 crypto_ed25519_*)
   ---------------------------------------------------------------------------

   --  P is the canonical RFC 8032 §5.1.2 encoding of an Edwards point, as
   --  far as the bytes alone decide it (§5.1.3 decoding steps 1 and 4):
   --  the y-coordinate (bits 0 .. 254, little-endian) is below
   --  p = 2**255 - 19, and the sign bit (bit 255) is clear when x = 0. The
   --  only points with x = 0 are y = 1 (the identity) and y = p - 1 (the
   --  point of order 2), so the second condition is a byte comparison too.
   --  Whether y is on the curve at all (step 3) needs a square root and is
   --  left to crypto_ed25519_check, which refuses such encodings.
   --  ge_tobytes, hence every public key and R that monocypher produces, is
   --  canonical. Quantifier-free, so public (CONVENTIONS.md rule 2).
   function Is_Canonical_Point (P : Pubkey) return Boolean is
     (--  y < p: not (y's top byte 16#7F#, bytes 30 .. 1 all 16#FF#, and
      --  byte 0 >= 16#ED#)
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

   --  The public key that crypto_ed25519_key_pair derives from a seed
   --  (RFC 8032 §5.1.5). It runs crypto_ed25519_key_pair on a copy of S and
   --  wipes the copy and the 64-byte secret it produced.
   function Derive_Public (S : Seed) return Pubkey
     with Global => null,
          Post   => Is_Canonical_Point (Derive_Public'Result);

   --  A signing key: monocypher's 64-byte secret key (seed ‖ public key)
   --  plus a validity flag. It is private and limited, so the only way to
   --  make a valid one is Key_Pair, which derives the public half from the
   --  seed. crypto_ed25519_sign hashes the public half into the challenge
   --  without checking it, while its nonce depends only on the seed. A key
   --  whose halves disagree would therefore leak the private scalar after
   --  two signatures of one message (the "double public key" oracle). The
   --  type rules that out, and Is_Valid states it. A default-initialized
   --  key is not valid (the DIC, proved from the full type's defaults and
   --  Is_Valid's expression).
   type Secret_Key is limited private
     with Default_Initial_Condition => not Is_Valid (Secret_Key);

   --  The seed half (the first 32 bytes of monocypher's secret key). Ghost:
   --  it exists for the contracts, and no executable code can read the
   --  secret seed back out of a key, so no function result or temporary
   --  ever holds a copy. A device that persists its signing key persists
   --  the seed it passed to Key_Pair (and wipes its own copy after).
   function Seed_Of (SK : Secret_Key) return Seed
     with Ghost, Global => null;

   --  The public half (the last 32 bytes of monocypher's secret key).
   function Public_Of (SK : Secret_Key) return Pubkey
     with Global => null;

   --  True for a key made by Key_Pair and not wiped since. Ghost: only
   --  contracts use it (Sign's Pre, Kome.Records' Sign Pres). Its
   --  completion is an expression function in the private part (the flag,
   --  and the public half derived from the seed half), so its Post and the
   --  DIC above are proved. At run time (-gnata) evaluating it derives the
   --  public key once.
   function Is_Valid (SK : Secret_Key) return Boolean
     with Ghost, Global => null,
          Post   => (if Is_Valid'Result
                     then Public_Of (SK) = Derive_Public (Seed_Of (SK)));

   --  crypto_ed25519_key_pair (sk, pk, seed). The C call wipes its seed
   --  argument, so the binding passes it a copy and S is untouched (it is an
   --  `in` parameter). Post: the key is valid, holds S, and PK is its
   --  public half and the key derived from S.
   procedure Key_Pair (S : Seed; SK : out Secret_Key; PK : out Pubkey)
     with Global => null,
          Post   => Is_Valid (SK)
                    and then Seed_Of (SK) = S
                    and then Public_Of (SK) = PK
                    and then PK = Derive_Public (S)
                    and then Is_Canonical_Point (PK);

   --  crypto_wipe over the 64-byte secret key. Afterwards the key is invalid
   --  and both halves are zero.
   procedure Wipe (SK : in out Secret_Key)
     with Global => null,
          Post   => not Is_Valid (SK)
                    and then (for all B of Seed_Of (SK) => B = 0)
                    and then (for all B of Public_Of (SK) => B = 0);

   --  S < L for the scalar half of a signature, where L = 2**252 +
   --  27742317777372353535851937790883648493 is the group order and S is
   --  little-endian in bytes 32 .. 63. crypto_ed25519_check refuses S >= L
   --  ("prevents malleability"), so for a given public key, message and R
   --  at most one signature encoding verifies. Quantifier-free (a chain of
   --  byte comparisons from the most significant byte down, as Kome.Lt is
   --  for words), so callers' provers can unfold it.
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

   --  crypto_ed25519_sign (sig, sk, msg, len). Deterministic (RFC 8032
   --  §5.1.6), hence a function. DESIGN.md §2: sig = Ed25519 (h) over the
   --  32-byte content hash. Pre: a key made by Key_Pair (see Secret_Key for
   --  why that matters). Post: the scalar is reduced mod L and R is
   --  canonical, both of which Verify requires.
   function Sign (SK : Secret_Key; Msg : Byte_Array) return Sig
     with Global => null,
          Pre    => Is_Valid (SK) and then Msg'Length <= Max_Data_Len,
          Post   => S_Below_L (Sign'Result)
                    and then Is_Canonical_Point (Sign'Result (0 .. 31));

   --  Strict RFC 8032 verification (see the header): S < L, canonical R and
   --  PK, then crypto_ed25519_check (sig, pk, msg, len) = 0. DESIGN.md §2: a
   --  record is well-formed iff its bounds hold and its signature verifies,
   --  which is a function of its bytes alone (hence a function, Global =>
   --  null). A1 is the assumption that True means the holder of PK's secret
   --  key signed Msg. The checkable part is the encoding: True implies a
   --  canonical scalar (non-malleability) and canonical point encodings.
   function Verify (Signature : Sig; PK : Pubkey; Msg : Byte_Array) return Boolean
     with Global => null,
          Pre    => Msg'Length <= Max_Data_Len,
          Post   => (if Verify'Result
                     then S_Below_L (Signature)
                          and then Is_Canonical_Point (Signature (0 .. 31))
                          and then Is_Canonical_Point (PK));

   ---------------------------------------------------------------------------
   --  X25519 (RFC 7748)
   ---------------------------------------------------------------------------

   --  An X25519 output is a u-coordinate reduced mod 2**255 - 19 and
   --  encoded little-endian (RFC 7748 §5, encodeUCoordinate), so its top
   --  bit is clear. monocypher's fe_tobytes emits the canonical encoding.
   function Is_Canonical_U (U : Pubkey) return Boolean is (U (31) < 16#80#)
     with Global => null;

   --  All 32 bytes are zero. Quantifier-free (CONVENTIONS.md rule 2), so it
   --  costs callers' provers nothing.
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

   --  U is the reduced little-endian encoding of a field element: bit 255
   --  clear (Is_Canonical_U) and u < p = 2**255 - 19, i.e. not one of the
   --  19 encodings 16#7FFF...FFED# .. 16#7FFF...FFFF#. These are exactly
   --  the outputs of X25519_Public (monocypher fully reduces), so an honest
   --  dh_pk or box_pk always passes. Quantifier-free, so public. (Moved
   --  here from Kome.Epochs, same body: DESIGN.md §2 rule 3, E5.)
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
   --  (DESIGN.md §2 rule 3, E5), compared bytewise:
   --    u = 0        0000000000000000000000000000000000000000000000000000000000000000
   --    u = 1        0100000000000000000000000000000000000000000000000000000000000000
   --    order 8      e0eb7a7c3b41b8ae1656e3faf19fc46ada098deb9c32b1fd866205165f49b800
   --    order 8      5f9c95bca3508c24b1d0b1559c83ef5b04445cc4581c8e86d8224eddd09f1157
   --    u = p - 1    ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f
   --  (libsodium's blocklist without its non-reduced entries, which
   --  Is_Reduced_U already refuses). For each of them every secret gives an
   --  all-zero shared secret (X25519 reports Contributory = False).
   --  Quantifier-free, so public.
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

   --  The X25519 keys Kome accepts at decode (DESIGN.md §2 rule 3, E5): a
   --  ROSTER's box_pk and every member dh_pk is reduced and not low order,
   --  so every listed member can open its box. Kome.Records (decode) and
   --  Kome.Epochs (box and unbox) are both to use this one definition.
   function Is_Good_DH_Key (U : Pubkey) return Boolean is
     (Is_Reduced_U (U) and then not Is_Low_Order_U (U))
     with Global => null;

   --  crypto_x25519_public_key (pk, sk): the member's `dh_pk` (DESIGN.md §2
   --  ROSTER members[] { sign_pk dh_pk ... }).
   function X25519_Public (Secret : DH_Secret) return Pubkey
     with Global => null,
          Post   => Is_Canonical_U (X25519_Public'Result);

   --  crypto_x25519 (shared, your_sk, their_pk): the raw shared secret,
   --  written into the caller's buffer (a secret: the caller wipes it).
   --  monocypher's note applies: it is not uniformly random, so hash it
   --  before using it as a key. If Their_Public has low order (u = 0, u = 1,
   --  the order-8 points, or their non-canonical encodings), every secret
   --  gives all zeros. The exchange is then not contributory: the peer has
   --  fixed the "shared" key alone. Contributory reports this. A caller
   --  wrapping or unwrapping a ROSTER box (DESIGN.md §6) must refuse when
   --  it is False, and can prove that it did. Decode refuses such keys
   --  earlier (Is_Good_DH_Key).
   procedure X25519
     (Secret       : DH_Secret;
      Their_Public : Pubkey;
      Shared       : out Shared_Secret;
      Contributory : out Boolean)
     with Global => null,
          Post   => Is_Canonical_U (Shared)
                    and then Contributory = not Is_Zero (Shared)
                    and then Shared = X25519_Shared (Secret, Their_Public);

   --  The same shared secret as a function, for contracts only (Ghost): a
   --  client's Post can then name a key derived from the exchange
   --  (Kome.Epochs: the wrap key and the synthetic nonce of a member box,
   --  DESIGN.md §6 D6). Ghost, so executable code never holds the secret
   --  in a function-result temporary; under -gnata it runs the same C call
   --  as X25519 and the Post above checks that both agree.
   function X25519_Shared (Secret : DH_Secret; Their_Public : Pubkey) return Shared_Secret
     with Ghost, Global => null;

   ---------------------------------------------------------------------------
   --  XChaCha20-Poly1305 AEAD (crypto_aead_lock / crypto_aead_unlock)
   ---------------------------------------------------------------------------

   --  crypto_aead_lock (cipher, mac, key, nonce, ad, ad_len, plain, len).
   --  Cipher has exactly Plain's length (a stream cipher), and Mac
   --  authenticates AD and Cipher. SPARK's anti-aliasing rule forbids
   --  passing one buffer as both Plain and Cipher, so the C in-place mode is
   --  never used. No Post: the only output facts are the lengths, which the
   --  Pre fixes (an out parameter's bounds cannot change), so a Post would
   --  be vacuous. That Unlock inverts Lock is monocypher's guarantee and is
   --  run in the test main.
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

   --  crypto_aead_unlock (...) = 0. On a forged or corrupted message
   --  (Authentic = False) monocypher writes nothing; the binding then zeros
   --  Plain, so a refused message never leaves plaintext or stale bytes
   --  behind (the Post). On success Plain is the decryption of Cipher.
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

   --  crypto_wipe (buf, len): zero a secret (a seed, a shared secret, an
   --  epoch key, a plaintext) in a way the C compiler does not elide. The
   --  Ada compiler cannot elide the call either, because the package is not
   --  Pure (see the header). Which object is erased: Byte_Array is not a
   --  by-reference type, and RM 6.2(11) leaves the mechanism of B
   --  unspecified. GNAT passes an unconstrained array formal such as B by
   --  reference (a pointer to the actual's data plus its bounds), so
   --  B'Address is the caller's buffer; test_crypto's wipe_zeroes checks
   --  the caller's object after the call. A port to another compiler must
   --  re-check this (or give B an explicitly aliased mode).
   --  For callers: gnatprove's flow analysis reports a Wipe of a local
   --  that is never read again as "statement has no effect" / "set by Wipe
   --  but not used after the call". That is the point of the call. Silence
   --  it locally with pragma Warnings (Off, "statement has no effect") and a
   --  Reason. Do not remove the call. Data and flow dependencies stay as
   --  Global => null states them, because erasing memory is not an effect
   --  the SPARK model can observe.
   procedure Wipe (B : out Byte_Array)
     with Global => null, Always_Terminates,
          Pre    => B'Length <= Max_Data_Len,
          Post   => (for all I in B'Range => B (I) = 0);

private

   --  Storage for monocypher's crypto_blake2b_ctx, whose layout the header
   --  says not to depend on. On LP64 it is 8 + 2 + 16 words of uint64_t plus
   --  two size_t, 28 words. 32 words of U64 hold it with room and give it
   --  uint64_t alignment. The body checks the size at compile time against
   --  a Convention C mirror of the header's struct.
   Ctx_Words : constant := 32;
   type Ctx_Storage is array (0 .. Ctx_Words - 1) of U64;

   --  Explicitly limited, hence by-reference (RM 6.2(4), 6.2(7)): see the
   --  header.
   type Blake2b_Context is limited record
      Raw    : Ctx_Storage := [others => 0];
      Active : Boolean     := False;
      Count  : Stream_Len  := 0;
   end record;

   function Is_Active (Ctx : Blake2b_Context) return Boolean is (Ctx.Active);
   function Absorbed (Ctx : Blake2b_Context) return Stream_Len is (Ctx.Count);

   --  monocypher's secret_key[64] = seed ‖ public key. Explicitly limited,
   --  hence by-reference (RM 6.2(4), 6.2(7)).
   type Secret_Key is limited record
      Raw   : Byte_Array (0 .. Secret_Key_Len - 1) := [others => 0];
      Valid : Boolean := False;
   end record;

   function Seed_Of (SK : Secret_Key) return Seed is
     (SK.Raw (0 .. Seed_Len - 1));
   function Public_Of (SK : Secret_Key) return Pubkey is
     (SK.Raw (Seed_Len .. Secret_Key_Len - 1));

   --  Valid means: made by Key_Pair and not wiped (the flag), and the
   --  public half is the one derived from the seed half. Key_Pair
   --  establishes both and Wipe clears the flag (their Posts, assumed: the
   --  bodies are C). The second conjunct makes the Post above a
   --  consequence of the definition, and the default flag makes the DIC
   --  one.
   function Is_Valid (SK : Secret_Key) return Boolean is
     (SK.Valid and then Public_Of (SK) = Derive_Public (Seed_Of (SK)));

end Kome.Crypto;
