--  Kome.Epochs: the hash-chained epoch keys and the member boxes of
--  DESIGN.md §6 ("Membership is key possession").
--
--  THE CHAIN. k_e = BLAKE2b-256 (k_{e+1} ‖ "prev"). The root draws a random
--  top key k_Top at an epoch Top <= 2**16 - 1 ("2^16 epochs suffice for any
--  collection's life", §6; the range is Kome.Epoch) and derives downward.
--  The randomness is the caller's: nothing in this package reads an RNG or
--  a clock. Step is one link of the chain (one BLAKE2b-256 call through
--  Kome.Crypto); Derive (K, From, To) walks From - To links down.
--
--  WHAT IS PROVED, AND WHAT IS NOT. T14 (epoch secrecy: a key absent from
--  roster e and every later roster cannot derive k_e' for e' >= e) is a
--  paper reduction to the one-wayness of BLAKE2b (A2) and the AEAD, not a
--  machine theorem (DESIGN.md §9). What this package proves is that the code
--  computes the chain it is meant to:
--
--    * Step is opaque: the prover knows nothing about BLAKE2b and treats it
--      as an uninterpreted function. Iter (K, N) is the ghost model "Step
--      applied N times", and Derive's Post says Derive is exactly
--      Iter (K, From - To). The loop that computes it runs at most
--      Max_Steps = 2**16 - 1 times, a bound that is the type of its index.
--    * The chain algebra, as ghost lemmas over the opaque Step:
--      Lemma_Derive_Identity (Derive (K, e, e) = K),
--      Lemma_Derive_Compose  (Derive (Derive (K, a, b), b, c) = Derive (K, a, c)),
--      Lemma_Derive_Step     (one epoch down is one Step),
--      Lemma_Derive_Shift    (only the distance From - To matters),
--      and the underlying Lemma_Iter_Add on the model.
--    * The API only goes down (Pre: To <= From). There is no operation that
--      maps k_e to k_{e+1}; that is the code shape of T14, whose content
--      (that no other operation can either) is A2.
--    * Box_Key / Unbox_Key: the byte layout of a §2 box (ciphertext ‖ tag,
--      32 + 16 = Box_Len = 48 bytes) is checked by the prover on every
--      slice and concatenation; a peer key that is not the canonical
--      encoding of a field element (Is_Reduced_U) is refused, and so is a
--      low-order peer (the exchange is not contributory, Kome.Crypto.X25519);
--      a refused box or key is all zeros, and the Posts say so. Unbox_Key
--      (Box_Key (k)) = k is monocypher's AEAD guarantee, not a proof
--      obligation (a crypto oracle): the test main runs it.
--
--  BOX CONSTRUCTION. DESIGN.md §2/§6 fix the primitives (X25519 to the
--  member's dh_pk, XChaCha20-Poly1305, nonce[24] box[48]) but not the key
--  derivation or the associated data. This package uses, and the report
--  proposes recording in DESIGN.md §6:
--    wrap_key = BLAKE2b-256 (X25519 (root_dh_sk, member_dh_pk)
--                            ‖ root_dh_pk ‖ member_dh_pk)
--      (the raw X25519 output is not uniform and must be hashed; the two
--       public keys bind the key to the pair, as libsodium's crypto_kx does);
--    AD = ns[16] ‖ epoch[2] (the roster's collection id, then its epoch
--      big-endian: a box for (ns, e) does not open as a box for any other
--      collection or epoch, even when a root reuses its X25519 key);
--    box = XChaCha20-Poly1305 (wrap_key, nonce, AD, k_e) = cipher[32] ‖ tag[16].
--  The nonce is the caller's (fresh per box; no randomness in SPARK code).
--
--  CANONICAL PEER KEYS. X25519 reads a u-coordinate modulo p = 2**255 - 19
--  and ignores bit 255, so one point has several 32-byte encodings with the
--  same shared secret; but the wrap key hashes the encoding. A member opens
--  its box with its own X25519_Public, which is always the reduced encoding
--  (u < p, bit 255 clear). A box sealed to any other encoding of the same
--  point would be reported Box_OK and still never open for its member. So
--  both sides accept only reduced encodings (Is_Reduced_U) and refuse the
--  rest with Non_Canonical_Peer; the ROSTER parser should do the same, and
--  DESIGN.md §2 should say that dh_pk is canonical (reported).
--  OPEN (reported): the ROSTER layout of §2 carries the root's Ed25519
--  root_pk but no root X25519 key, so a member has no root dh_pk to open a
--  box with. Unbox_Key takes it as a parameter until the design says where
--  it lives (and, with several roots, module J, whose).
--
--  SECRETS. In Box_Key and Unbox_Key, byte buffers that hold a secret (the
--  shared secret, the wrap key, the plaintext epoch key) are erased with
--  Kome.Crypto.Wipe before every return. Step cannot do the same: it is a
--  function, SPARK functions must terminate, and Kome.Crypto's procedures
--  (Blake2b_256 into a buffer, Wipe) carry no Always_Terminates aspect, so
--  Step uses the function form of BLAKE2b-256 and its temporaries are not
--  wiped (reported for Kome.Crypto). Key256 values themselves are ordinary
--  records (the lattice convention for keys) and are not wiped here.
pragma Ada_2022;
with Kome.Crypto;
package Kome.Epochs with SPARK_Mode, Preelaborate is

   ---------------------------------------------------------------------------
   --  The chain
   ---------------------------------------------------------------------------

   --  DESIGN.md §6: 2^16 epochs, so a walk from the top epoch to epoch 0 is
   --  at most 2**16 - 1 links (Kome.Epoch is 0 .. 2**16 - 1).
   Max_Steps : constant := 2**16 - 1;
   subtype Steps is Natural range 0 .. Max_Steps;

   --  The label hashed after the key: ASCII "prev" (DESIGN.md §6).
   Prev_Label_Len : constant := 4;

   --  One link: Step (k_{e+1}) = k_e = BLAKE2b-256 (k_{e+1} ‖ "prev"), with
   --  the key's 32 bytes in the big-endian order of Kome.Keys. Opaque on
   --  purpose (no Post): the chain algebra below holds for any function,
   --  and what this one computes is checked against hashlib in the test.
   function Step (K : Key256) return Key256
     with Global => null;

   --  Ghost model: Step applied N times. Recursion bounded by the variant
   --  (CONVENTIONS.md: no recursion unless bounded by a Subprogram_Variant).
   --  Quantifier-free, so public.
   function Iter (K : Key256; N : Steps) return Key256 is
     (if N = 0 then K else Step (Iter (K, N - 1)))
     with Ghost, Global => null,
          Subprogram_Variant => (Decreases => N);

   --  The key at epoch To, from the key K at epoch From >= To: From - To
   --  links down the chain. DESIGN.md §6; refines the chain on which the
   --  T14 paper argument rests (only downward derivation exists).
   function Derive (K : Key256; From, To : Epoch) return Key256
     with Global => null,
          Pre    => To <= From,
          Post   => Derive'Result = Iter (K, Natural (From) - Natural (To));

   ---------------------------------------------------------------------------
   --  Chain algebra (ghost lemmas; the law is the Post). DESIGN.md §6.
   ---------------------------------------------------------------------------

   --  Iterating M then N times is iterating M + N times.
   procedure Lemma_Iter_Add (K : Key256; M, N : Steps)
     with Ghost, Global => null,
          Pre  => M + N <= Max_Steps,
          Post => Iter (Iter (K, M), N) = Iter (K, M + N);

   --  Derive (K, e, e) = K.
   procedure Lemma_Derive_Identity (K : Key256; E : Epoch)
     with Ghost, Global => null,
          Post => Derive (K, E, E) = K;

   --  One epoch down is one Step: Derive (k_{e+1}, e + 1, e) = k_e.
   procedure Lemma_Derive_Step (K : Key256; E : Epoch)
     with Ghost, Global => null,
          Pre  => E < Epoch'Last,
          Post => Derive (K, E + 1, E) = Step (K);

   --  Derivation composes: walking a -> b then b -> c is walking a -> c.
   --  This is what makes "a member holding k_e derives every older key"
   --  (§6) independent of the route taken.
   procedure Lemma_Derive_Compose (K : Key256; A, B, C : Epoch)
     with Ghost, Global => null,
          Pre  => C <= B and then B <= A,
          Post => Derive (Derive (K, A, B), B, C) = Derive (K, A, C);

   --  Only the distance matters: Derive (K, a, b) = Derive (K, a', b') when
   --  a - b = a' - b'.
   procedure Lemma_Derive_Shift (K : Key256; A, B, A2, B2 : Epoch)
     with Ghost, Global => null,
          Pre  => B <= A and then B2 <= A2
                  and then Natural (A) - Natural (B) = Natural (A2) - Natural (B2),
          Post => Derive (K, A, B) = Derive (K, A2, B2);

   ---------------------------------------------------------------------------
   --  Boxes (DESIGN.md §2 ROSTER members[] { sign_pk dh_pk nonce[24] box[48] })
   ---------------------------------------------------------------------------

   --  The layout of a box: the AEAD ciphertext of the 32-byte epoch key,
   --  then the 16-byte Poly1305 tag. Kome.Box_Len = 48 is the sum.
   Cipher_Len : constant := Kome.Crypto.AEAD_Key_Len;
   Tag_Len    : constant := Kome.Crypto.Tag_Len;
   pragma Compile_Time_Error
     (Box_Len /= Cipher_Len + Tag_Len, "DESIGN.md §2: box[48] = cipher[32] ‖ tag[16]");
   pragma Compile_Time_Error
     (Cipher_Len /= Hash_Len, "an epoch key is a BLAKE2b-256 digest");

   --  AD bound into every box: ns[16] ‖ epoch (big-endian, 2 bytes); see
   --  the header.
   AD_Len : constant := NS_Len + 2;

   function Cipher_Of (B : Kome.Box) return Kome.Crypto.AEAD_Key is
     (B (0 .. Cipher_Len - 1))
     with Global => null;

   function Tag_Of (B : Kome.Box) return Kome.Crypto.Tag is
     (B (Cipher_Len .. Box_Len - 1))
     with Global => null;

   --  The all-zero key and the all-zero box: what a refusal leaves behind.
   Zero_Key : constant Key256 := (others => 0);

   --  Spelt out byte by byte, not quantified: a public quantified
   --  expression function is an axiom in every client (CONVENTIONS.md
   --  rule 2), as Kome.Crypto.Is_Zero is written for the same reason.
   function Is_Zero_Box (B : Kome.Box) return Boolean is
     (B (0) = 0 and then B (1) = 0 and then B (2) = 0 and then B (3) = 0
      and then B (4) = 0 and then B (5) = 0 and then B (6) = 0 and then B (7) = 0
      and then B (8) = 0 and then B (9) = 0 and then B (10) = 0 and then B (11) = 0
      and then B (12) = 0 and then B (13) = 0 and then B (14) = 0 and then B (15) = 0
      and then B (16) = 0 and then B (17) = 0 and then B (18) = 0 and then B (19) = 0
      and then B (20) = 0 and then B (21) = 0 and then B (22) = 0 and then B (23) = 0
      and then B (24) = 0 and then B (25) = 0 and then B (26) = 0 and then B (27) = 0
      and then B (28) = 0 and then B (29) = 0 and then B (30) = 0 and then B (31) = 0
      and then B (32) = 0 and then B (33) = 0 and then B (34) = 0 and then B (35) = 0
      and then B (36) = 0 and then B (37) = 0 and then B (38) = 0 and then B (39) = 0
      and then B (40) = 0 and then B (41) = 0 and then B (42) = 0 and then B (43) = 0
      and then B (44) = 0 and then B (45) = 0 and then B (46) = 0 and then B (47) = 0)
     with Global => null;

   --  U is the reduced little-endian encoding of a field element: bit 255
   --  clear (Kome.Crypto.Is_Canonical_U) and u < p = 2**255 - 19, i.e. not
   --  one of the 19 encodings 16#7FFF...FFED# .. 16#7FFF...FFFF#. These
   --  are exactly the outputs of X25519_Public (monocypher fully reduces),
   --  so an honest dh_pk always passes. Quantifier-free, so public.
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

   --  Package-local result: Kome.Status has no code for either refusal.
   type Box_Status is
     (Box_OK,
      Non_Canonical_Peer, --  the peer's X25519 key is not reduced
                          --  (Is_Reduced_U): bit 255 set or u >= p. Refused
                          --  before any exchange (see the header).
      Low_Order_Peer,   --  X25519 not contributory: the peer key has low
                        --  order (or is an encoding of such a point), so
                        --  the "shared" secret is all zeros. Refused.
      Not_Authentic);   --  Unbox only: the tag did not verify (wrong key,
                        --  wrong nonce, wrong epoch, or a tampered box).

   --  Seal epoch key Epoch_Key (the key of epoch E of collection Ns) to the
   --  member whose X25519 public key is Member_Public, under the root's
   --  X25519 secret Root_Secret and the caller's fresh nonce N. On Box_OK,
   --  Sealed is cipher[32] ‖ tag[16] and Member_Public was reduced; a
   --  non-reduced key is refused with Non_Canonical_Peer, a low-order one
   --  with Low_Order_Peer, and on refusal Sealed is all zeros. Box_Key never
   --  reports Not_Authentic. Box contents are monocypher's (no Post on the
   --  cipher; the test main checks the round trip).
   procedure Box_Key
     (Root_Secret   : Kome.Crypto.DH_Secret;
      Member_Public : Pubkey;
      Ns            : Id128;
      E             : Epoch;
      Epoch_Key     : Key256;
      N             : Nonce;
      Sealed        : out Kome.Box;
      Status        : out Box_Status)
     with Global => null,
          Post   => Status /= Not_Authentic
                    and then (Status = Non_Canonical_Peer)
                               = not Is_Reduced_U (Member_Public)
                    and then (if Status /= Box_OK then Is_Zero_Box (Sealed));

   --  Open a box with the member's X25519 secret, the root's X25519 public
   --  key, the collection and epoch it claims and its nonce. Box_OK means
   --  the tag verified and Epoch_Key is the sealed key; otherwise
   --  Epoch_Key = Zero_Key. A non-reduced Root_Public is refused with
   --  Non_Canonical_Peer (it could only ever fail to authenticate).
   --  Root_Public is a parameter until DESIGN.md says where the root's
   --  dh_pk lives (see the header).
   procedure Unbox_Key
     (Member_Secret : Kome.Crypto.DH_Secret;
      Root_Public   : Pubkey;
      Ns            : Id128;
      E             : Epoch;
      N             : Nonce;
      Sealed        : Kome.Box;
      Epoch_Key     : out Key256;
      Status        : out Box_Status)
     with Global => null,
          Post   => (Status = Non_Canonical_Peer) = not Is_Reduced_U (Root_Public)
                    and then (if Status /= Box_OK then Epoch_Key = Zero_Key);

end Kome.Epochs;
