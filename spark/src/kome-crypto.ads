--  Kome.Crypto: the thin binding to monocypher 4 (third_party/monocypher),
--  the design's only cryptographic dependency (DESIGN.md §2, §6;
--  CONVENTIONS.md "Cryptography": do not reimplement, bind).
--
--    BLAKE2b-256      crypto_blake2b, crypto_blake2b_init/update/final with
--                     hash_size = 32. DESIGN.md §2 `ns`, `h`; §6 the epoch
--                     key chain; §8 the accumulator. Assumption A2.
--    EdDSA            crypto_eddsa_key_pair / _sign / _check. DESIGN.md §2
--                     `sig`. Assumption A1.
--    X25519           crypto_x25519_public_key, crypto_x25519. DESIGN.md §6
--                     (epoch key wrapped to each member's `dh_pk`).
--    XChaCha20-       crypto_aead_lock / _unlock: 32-byte key, 24-byte nonce,
--    Poly1305         16-byte tag. DESIGN.md §2 `nonce[24] box[48]`, §6
--                     sealed bundles. T14 (paper) rests on it.
--    Erasure          crypto_wipe, on byte buffers, signing keys and hash
--                     contexts.
--
--  WHICH EdDSA (OPEN DESIGN DECISION, see DESIGN.md §2 and A1).
--  monocypher 4's crypto_eddsa_* is RFC 8032 Ed25519 with BLAKE2b-512 in
--  place of SHA-512 (monocypher.c crypto_eddsa_sign). The SHA-512 variant
--  is in the optional monocypher-ed25519.c, which is not vendored. This is
--  the scheme the previous C++ engine used (src/crypto.cpp before commit
--  5ebfad0) and the one Nano calls "ED25519 with Blake2b-512". Its
--  signatures are NOT interoperable with RFC 8032 Ed25519. The test main
--  checks the RFC 8032 TEST 1 seed against BLAKE2b-EdDSA answers, checks
--  published Ed25519-BLAKE2b key pairs (nano-docs), and checks that the
--  RFC's SHA-512 signature is rejected. DESIGN.md §2 and A1 say "Ed25519".
--  Real RFC 8032 Ed25519 needs SHA-512, which monocypher's core lacks. The
--  options are to amend the design text, or to vendor
--  monocypher-ed25519.{c,h} and bind crypto_ed25519_*. Neither changes the
--  contracts in this spec.
--
--  SPARK boundary (CONVENTIONS.md, the one allowed exception): this spec is
--  SPARK_Mode On with full contracts, and the body is SPARK_Mode Off and
--  calls C through Interfaces.C. The contracts state what can be checked
--  at the boundary:
--    * input bounds, output lengths and layouts;
--    * the incremental context's state machine and byte count;
--    * that only Key_Pair makes a signing key, so a key's public half is
--      always the one derived from its seed (Is_Valid);
--    * non-malleability of signatures (S < L, which crypto_eddsa_check
--      enforces);
--    * that a non-contributory X25519 is reported;
--    * that a refused Unlock and every Wipe leave zeros.
--  They do not state Verify (Sign (M)) or the hashing algebra. Those are A1
--  and A2, plus the known-answer vectors. Under -gnata the test main runs
--  every Post below against monocypher's real output.
--
--  Every function here is a mathematical function of its arguments
--  (monocypher's signing is deterministic, and nothing reads a clock or an
--  RNG), so the functions are SPARK functions with Global => null.
--
--  PREELABORATE, NOT PURE. RM 10.2.1(18) lets an implementation omit a
--  call to a library-level subprogram of a declared-pure unit when the
--  call's results are not needed afterwards. A Wipe just before a secret
--  goes out of scope is exactly such a call. The package is therefore
--  Preelaborate, so that permission never applies and a Wipe is an
--  ordinary call to C that must be executed. A unit that withs Kome.Crypto
--  can be Preelaborate but not Pure.
--
--  BY-REFERENCE SECRETS. Secret_Key and Blake2b_Context are explicitly
--  limited records. RM 6.2(7) makes them by-reference types, so they are
--  never silently copied into temporaries, and a Wipe erases the caller's
--  object itself and not a copy of it. Being limited, they cannot be copied
--  by assignment either.
pragma Ada_2022;
package Kome.Crypto with SPARK_Mode, Preelaborate is

   ---------------------------------------------------------------------------
   --  Sizes (monocypher.h prototypes; DESIGN.md §2 for those Kome names)
   ---------------------------------------------------------------------------

   Seed_Len       : constant := 32;   --  crypto_eddsa_key_pair seed[32]
   Secret_Key_Len : constant := 64;   --  crypto_eddsa secret_key[64] = seed ‖ pk
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

   --  The largest single buffer handed to monocypher. It is declared here
   --  rather than in Kome (root), because this package owns only its own
   --  files; it is reported for adoption there. Sizes from the design:
   --    * DESIGN.md §2: the largest record is a PUT with a 65_535-byte value
   --      (Kome.Value_Max) plus a header of under 1 KiB, so under 66 KiB;
   --    * §8: a reconciliation message is at most 48 KiB
   --      (Kome.Max_Message_Len), and a range ships at most
   --      Ship_Threshold = 4 elements, so a sealed bundle
   --      (`ns ‖ epoch ‖ nonce ‖ AEAD(elements)`) of one range holds at most
   --      4 records, under 264 KiB;
   --    * §7: a log frame `content ‖ sig` is one record.
   --  16 × 64 KiB = 1 MiB covers every one of these, with 4× headroom over
   --  the largest bundle. Larger payloads are chunked above the engine
   --  (§2), so nothing larger reaches this package.
   Max_Data_Len : constant := 16 * (Value_Max + 1);   --  2**20 = 1 MiB

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

   --  The same hash, written straight into the caller's buffer. Use this
   --  form when the digest is itself a secret, such as the epoch key chain
   --  k_e = BLAKE2b-256 (k_{e+1} ‖ "prev") of DESIGN.md §6, so that no
   --  function-result temporary holds a copy. The caller wipes Digest.
   procedure Blake2b_256 (Data : Byte_Array; Digest : out Hash256)
     with Global => null,
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

   type Blake2b_Context is limited private;

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
   --  EdDSA over Curve25519 with BLAKE2b-512 (monocypher crypto_eddsa_*)
   ---------------------------------------------------------------------------

   --  The public key that crypto_eddsa_key_pair derives from a seed. It
   --  runs crypto_eddsa_key_pair on a copy of S and wipes the copy and the
   --  64-byte secret it produced.
   function Derive_Public (S : Seed) return Pubkey
     with Global => null;

   --  A signing key: monocypher's 64-byte secret key (seed ‖ public key)
   --  plus a validity flag. It is private and limited, so the only way to
   --  make a valid one is Key_Pair, which derives the public half from the
   --  seed. crypto_eddsa_sign hashes the public half into the challenge
   --  without checking it, while its nonce depends only on the seed. A key
   --  whose halves disagree would therefore leak the private scalar after
   --  two signatures of one message (the "double public key" oracle). The
   --  type rules that out, and Is_Valid's Post states it.
   type Secret_Key is limited private;

   --  The seed half (the first 32 bytes of monocypher's secret key). This is
   --  what a device persists, since Key_Pair rebuilds the key from it.
   function Seed_Of (SK : Secret_Key) return Seed
     with Global => null;

   --  The public half (the last 32 bytes of monocypher's secret key).
   function Public_Of (SK : Secret_Key) return Pubkey
     with Global => null;

   --  True for a key made by Key_Pair and not wiped since. Opaque: callers
   --  learn it only from Key_Pair's and Wipe's postconditions. A
   --  default-initialized key is not valid.
   function Is_Valid (SK : Secret_Key) return Boolean
     with Global => null,
          Post   => (if Is_Valid'Result
                     then Public_Of (SK) = Derive_Public (Seed_Of (SK)));

   --  crypto_eddsa_key_pair (sk, pk, seed). The C call wipes its seed
   --  argument, so the binding passes it a copy and S is untouched (it is an
   --  `in` parameter). Post: the key is valid, holds S, and PK is its
   --  public half and the key derived from S.
   procedure Key_Pair (S : Seed; SK : out Secret_Key; PK : out Pubkey)
     with Global => null,
          Post   => Is_Valid (SK)
                    and then Seed_Of (SK) = S
                    and then Public_Of (SK) = PK
                    and then PK = Derive_Public (S);

   --  crypto_wipe over the 64-byte secret key. Afterwards the key is invalid
   --  and both halves are zero.
   procedure Wipe (SK : in out Secret_Key)
     with Global => null,
          Post   => not Is_Valid (SK)
                    and then (for all B of Seed_Of (SK) => B = 0)
                    and then (for all B of Public_Of (SK) => B = 0);

   --  S < L for the scalar half of a signature, where L = 2**252 +
   --  27742317777372353535851937790883648493 is the group order and S is
   --  little-endian in bytes 32 .. 63. crypto_eddsa_check refuses S >= L
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

   --  crypto_eddsa_sign (sig, sk, msg, len). Deterministic (RFC 8032 §5.1.6
   --  nonce derivation, with BLAKE2b-512), hence a function. DESIGN.md §2:
   --  sig = Ed25519 (h) over the 32-byte content hash. Pre: a key made by
   --  Key_Pair (see Secret_Key for why that matters). Post: the scalar is
   --  reduced mod L, which Verify requires.
   function Sign (SK : Secret_Key; Msg : Byte_Array) return Sig
     with Global => null,
          Pre    => Is_Valid (SK) and then Msg'Length <= Max_Data_Len,
          Post   => S_Below_L (Sign'Result);

   --  crypto_eddsa_check (sig, pk, msg, len) = 0. DESIGN.md §2: a record is
   --  well-formed iff its bounds hold and its signature verifies, which is a
   --  function of its bytes alone (hence a function, Global => null). A1 is
   --  the assumption that True means the holder of PK's secret key signed
   --  Msg. The checkable part is non-malleability: True implies a canonical
   --  scalar.
   function Verify (Signature : Sig; PK : Pubkey; Msg : Byte_Array) return Boolean
     with Global => null,
          Pre    => Msg'Length <= Max_Data_Len,
          Post   => (if Verify'Result then S_Below_L (Signature));

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
   --  it is False, and can prove that it did.
   procedure X25519
     (Secret       : DH_Secret;
      Their_Public : Pubkey;
      Shared       : out Shared_Secret;
      Contributory : out Boolean)
     with Global => null,
          Post   => Is_Canonical_U (Shared)
                    and then Contributory = not Is_Zero (Shared);

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
   --  Pure (see the header). Byte_Array is passed by reference, so this
   --  erases the caller's buffer.
   --  For callers: gnatprove's flow analysis reports a Wipe of a local
   --  that is never read again as "statement has no effect" / "set by Wipe
   --  but not used after the call". That is the point of the call. Silence
   --  it locally with pragma Warnings (Off, "statement has no effect") and a
   --  Reason. Do not remove the call. Data and flow dependencies stay as
   --  Global => null states them, because erasing memory is not an effect
   --  the SPARK model can observe.
   procedure Wipe (B : out Byte_Array)
     with Global => null,
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

   --  Explicitly limited, hence by-reference (RM 6.2(7)): see the header.
   type Blake2b_Context is limited record
      Raw    : Ctx_Storage := [others => 0];
      Active : Boolean     := False;
      Count  : Stream_Len  := 0;
   end record;

   function Is_Active (Ctx : Blake2b_Context) return Boolean is (Ctx.Active);
   function Absorbed (Ctx : Blake2b_Context) return Stream_Len is (Ctx.Count);

   --  monocypher's secret_key[64] = seed ‖ public key.
   type Secret_Key is limited record
      Raw   : Byte_Array (0 .. Secret_Key_Len - 1) := [others => 0];
      Valid : Boolean := False;
   end record;

   function Seed_Of (SK : Secret_Key) return Seed is
     (SK.Raw (0 .. Seed_Len - 1));
   function Public_Of (SK : Secret_Key) return Pubkey is
     (SK.Raw (Seed_Len .. Secret_Key_Len - 1));

end Kome.Crypto;
