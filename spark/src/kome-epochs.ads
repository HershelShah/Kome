--  Kome.Epochs: the collection key of a roster, the member boxes and the
--  keys derived from it (SIMPLIFY.md S4; DESIGN.md §6 "Membership is key
--  possession", "Boxes (D5, D6)"). The package keeps its name; there is no
--  epoch, no hash chain, no segment and no link any more.
--
--  THE KEYS. Every ROSTER carries a fresh collection key k_g for its gen,
--  boxed to each member (S4). f (k, m) is keyed BLAKE2b-256 (key = k, msg =
--  m; Kome.Crypto.Blake2b_256_Keyed, one PRF assumption, AUDIT.md G5).
--  Every derivation is in that one style, f (key, label ‖ context):
--    k_g      = Hedge (issuer_sk, "kome/key", cid ‖ u48 (gen), rnd)
--             = f (Seed_Of (issuer_sk), "kome/key" ‖ cid ‖ u48 (gen) ‖ rnd)
--                                                       (Key_For_Gen; A6)
--    eph_sk   = f (k_g, "kome/eph" ‖ cid ‖ u48 (gen) ‖ signer)  (Eph_SK_Of)
--    box_pk   = X25519_Public (eph_sk)                          (Box_PK_Of)
--    nonce    = f (k_g, "kome/box" ‖ dh_pk)[0:24]               (Box_Nonce)
--    wrap_key = f (X25519 (eph_sk, dh_pk), "kome/wrap" ‖ box_pk ‖ dh_pk
--                  ‖ sign_pk ‖ cid ‖ u48 (gen))
--    box      = XChaCha20-Poly1305 (wrap_key, nonce, AD = cid ‖ u48 (gen),
--                                   k_g)  = cipher[32] ‖ tag[16]
--    bundle_key = f (k_g, "kome/bundle")                    (Bundle_Key_Of)
--  Labels are ASCII with no terminator, u48 is big-endian, cid is the 32
--  bytes of Kome.Records.Cid_Of, and k_g is the 32 bytes of
--  Kome.Keys.To_Bytes. The hedge (Kome.Crypto.Hedge) keys the derivation
--  of k_g with the issuer's signing seed, so a weak RNG alone does not
--  reveal k_g (A6); a repeated rnd at one (cid, gen) only repeats k_g. The
--  caller gives rnd: no part of this package reads an RNG or a clock.
--  eph_sk is not drawn either: whoever holds k_g can recompute it, and
--  that is exactly the set of members that can open the boxes anyway.
--
--  WHAT IS PROVED, AND WHAT IS NOT. Secrecy of k_g (T14: a key that is not
--  in the roster of gen g cannot learn k_g) is a paper reduction to the
--  PRF (A2, G5), to Gap-CDH for X25519 and to the AEAD. It is not a machine
--  theorem (DESIGN.md §9). This package proves:
--    * the byte layout of each input (the Compile_Time_Error pins below)
--      and of a box (cipher ‖ tag, 32 + 16 = Box_Len = 48 bytes);
--    * that Key_For_Gen is exactly the hedge of the issuer's seed over
--      "kome/key" ‖ cid ‖ u48 (gen) ‖ rnd (the ghost Gen_Key_Of);
--    * that Box_PK_Of is X25519_Public of the ghost Eph_SK_Of, and that
--      Box_Key returns that box_pk (G7: the field and the boxes of a roster
--      agree by construction);
--    * that a peer key that is not reduced (Kome.Crypto.Is_Reduced_U) gets
--      Non_Canonical_Peer, a low-order one (Kome.Crypto.Is_Low_Order_U, or
--      a non-contributory exchange) gets Low_Order_Peer, and that a box is
--      Box_OK only for a peer key that passes Kome.Crypto.Is_Good_DH_Key;
--    * that a refused box, nonce or key is all zeros;
--    * the synthetic nonce: the nonce of a sealed box is Box_Nonce (k_g,
--      dh_pk), and a box that Unbox_Key opens has exactly that nonce for
--      the key that it returns, which is never the all-zero key.
--  Open (Seal (k)) = k is monocypher's AEAD guarantee. It is not a proof
--  obligation (a crypto oracle). The test main runs it and checks known
--  answers from an independent Python reference (vectors/epochs.txt).
--
--  KEYSTREAMS. A member opens its box with X25519 (dh_sk, box_pk), computes
--  the nonce again from the opened key and refuses a mismatch, so exactly
--  one box opens for each (wrap_key, k_g). A fresh k_g per gen gives a
--  fresh eph_sk, box_pk and wrap key per roster; the wrap key also binds
--  cid, gen and both member keys, so two boxes for one member in two
--  rosters never share a key even if a box_pk repeated.
--
--  CANONICAL PEER KEYS. X25519 reads a u-coordinate modulo p = 2**255 - 19
--  and ignores bit 255, so one point has several 32-byte encodings with
--  the same shared secret. But the wrap key and the nonce hash the
--  encoding. A member opens its box with its own X25519_Public, which is
--  always the reduced encoding. The two sides accept only reduced
--  encodings (Is_Reduced_U, defined in Kome.Crypto and renamed here). They
--  refuse all other encodings with Non_Canonical_Peer. Decode refuses
--  them before this (DESIGN.md §2 rule 3, E5).
--
--  SECRETS. Key_For_Gen, Box_PK_Of, Box_Key, Unbox_Key and Bundle_Key_Of
--  erase each named byte buffer that holds a secret with Kome.Crypto.Wipe
--  before each return: the key bytes of k_g, the derived eph_sk, the
--  X25519 output, the wrap key, the digests and the plaintext key.
--  (A function can call the procedure forms of keyed BLAKE2b and Wipe
--  because they are Always_Terminates.) The ghost models Gen_Key_Of and
--  Eph_SK_Of run only under -gnata. Key256 values are ordinary records
--  (the lattice convention for keys); this package does not wipe them.
pragma Ada_2022;
with Kome.Crypto;
with Kome.Keys;
package Kome.Epochs with SPARK_Mode, Preelaborate is

   ---------------------------------------------------------------------------
   --  Labels and inputs (SIMPLIFY.md §2 "Keys"; ASCII, no terminator)
   ---------------------------------------------------------------------------

   Key_Label_Len    : constant := 8;    --  "kome/key"
   Eph_Label_Len    : constant := 8;    --  "kome/eph"
   Box_Label_Len    : constant := 8;    --  "kome/box"
   Wrap_Label_Len   : constant := 9;    --  "kome/wrap"
   Bundle_Label_Len : constant := 11;   --  "kome/bundle"

   Key_Label    : constant Byte_Array (0 .. Key_Label_Len - 1) :=
     [16#6B#, 16#6F#, 16#6D#, 16#65#, 16#2F#, 16#6B#, 16#65#, 16#79#];
   Eph_Label    : constant Byte_Array (0 .. Eph_Label_Len - 1) :=
     [16#6B#, 16#6F#, 16#6D#, 16#65#, 16#2F#, 16#65#, 16#70#, 16#68#];
   Box_Label    : constant Byte_Array (0 .. Box_Label_Len - 1) :=
     [16#6B#, 16#6F#, 16#6D#, 16#65#, 16#2F#, 16#62#, 16#6F#, 16#78#];
   Wrap_Label   : constant Byte_Array (0 .. Wrap_Label_Len - 1) :=
     [16#6B#, 16#6F#, 16#6D#, 16#65#, 16#2F#, 16#77#, 16#72#, 16#61#, 16#70#];
   Bundle_Label : constant Byte_Array (0 .. Bundle_Label_Len - 1) :=
     [16#6B#, 16#6F#, 16#6D#, 16#65#, 16#2F#, 16#62#, 16#75#, 16#6E#, 16#64#,
      16#6C#, 16#65#];

   --  cid ‖ u48 (gen): the context of k_g and the AD of every box.
   Gen_Ctx_Len : constant := Hash_Len + 6;
   --  "kome/eph" ‖ cid ‖ u48 (gen) ‖ signer
   Eph_Input_Len : constant := Eph_Label_Len + Gen_Ctx_Len + Pubkey_Len;
   --  "kome/box" ‖ dh_pk
   Box_Nonce_Input_Len : constant := Box_Label_Len + Pubkey_Len;
   --  "kome/wrap" ‖ box_pk ‖ dh_pk ‖ sign_pk ‖ cid ‖ u48 (gen)
   Wrap_Input_Len : constant := Wrap_Label_Len + 3 * Pubkey_Len + Gen_Ctx_Len;
   pragma Compile_Time_Error
     (Gen_Ctx_Len /= 38 or else Eph_Input_Len /= 78
      or else Box_Nonce_Input_Len /= 40 or else Wrap_Input_Len /= 143,
      "SIMPLIFY.md S4: inputs ctx 38, eph 78, box nonce 40, wrap 143 bytes");

   subtype Gen_Ctx_Bytes        is Byte_Array (0 .. Gen_Ctx_Len - 1);
   subtype Eph_Input_Bytes      is Byte_Array (0 .. Eph_Input_Len - 1);
   subtype Box_Nonce_Input_Bytes is Byte_Array (0 .. Box_Nonce_Input_Len - 1);
   subtype Wrap_Input_Bytes     is Byte_Array (0 .. Wrap_Input_Len - 1);

   --  The layout of a box: the AEAD ciphertext of the 32-byte key, then the
   --  16-byte Poly1305 tag. Kome.Box_Len = 48 is the sum.
   Cipher_Len : constant := Kome.Crypto.AEAD_Key_Len;
   Tag_Len    : constant := Kome.Crypto.Tag_Len;
   pragma Compile_Time_Error
     (Box_Len /= Cipher_Len + Tag_Len, "DESIGN.md §2: box[48] = cipher[32] ‖ tag[16]");
   pragma Compile_Time_Error
     (Cipher_Len /= Hash_Len, "a collection key is a BLAKE2b-256 digest");

   --  u48 (Gen), big-endian, byte by byte (lane 0 is the most significant).
   function U48_Byte (Gen : U48; Lane : Natural) return Byte is
     (case Lane is
         when 0 => Byte (Gen / 2**40),
         when 1 => Byte ((Gen / 2**32) mod 256),
         when 2 => Byte ((Gen / 2**24) mod 256),
         when 3 => Byte ((Gen / 2**16) mod 256),
         when 4 => Byte ((Gen / 2**8) mod 256),
         when others => Byte (Gen mod 256))
     with Global => null, Pre => Lane <= 5;

   --  cid ‖ u48 (gen).
   function Gen_Ctx (Cid : Hash256; Gen : U48) return Gen_Ctx_Bytes is
     (Cid & U48_Byte (Gen, 0) & U48_Byte (Gen, 1) & U48_Byte (Gen, 2)
      & U48_Byte (Gen, 3) & U48_Byte (Gen, 4) & U48_Byte (Gen, 5))
     with Global => null;

   --  "kome/eph" ‖ cid ‖ u48 (gen) ‖ signer.
   function Eph_Input (Cid : Hash256; Gen : U48; Signer : Pubkey) return Eph_Input_Bytes is
     (Eph_Label & Gen_Ctx (Cid, Gen) & Signer)
     with Global => null;

   --  "kome/wrap" ‖ box_pk ‖ dh_pk ‖ sign_pk ‖ cid ‖ u48 (gen).
   function Wrap_Input
     (Box_PK, DH_PK, Sign_PK : Pubkey; Cid : Hash256; Gen : U48) return Wrap_Input_Bytes is
     (Wrap_Label & Box_PK & DH_PK & Sign_PK & Gen_Ctx (Cid, Gen))
     with Global => null;

   --  The all-zero key: a refusal gives this key.
   Zero_Key : constant Key256 := (others => 0);

   ---------------------------------------------------------------------------
   --  k_g (hedged; AUDIT.md A6, SIMPLIFY.md S4)
   ---------------------------------------------------------------------------

   --  Ghost model of k_g: f (Seed_Of (issuer), "kome/key" ‖ cid ‖ u48 (gen)
   --  ‖ rnd). Ghost, because it reads the issuer's seed.
   function Gen_Key_Of
     (Issuer : Kome.Crypto.Secret_Key;
      Cid    : Hash256;
      Gen    : U48;
      Rnd    : Kome.Crypto.Random_Bytes) return Key256
   is (Kome.Keys.To_Key256
         (Kome.Crypto.Blake2b_256_Keyed
            (Kome.Crypto.Seed_Of (Issuer), Key_Label & Gen_Ctx (Cid, Gen) & Rnd)))
     with Ghost, Global => null;

   --  The collection key of the issuer's roster at gen (S4): a fresh key
   --  for every gen, a refresh included. The issuer is the roster's signer
   --  (any certified root). The result is the all-zero key with
   --  probability 2^-256; Box_Key refuses that key (Pre), so a builder
   --  checks K /= Zero_Key and draws again.
   procedure Key_For_Gen
     (Issuer : Kome.Crypto.Secret_Key;
      Cid    : Hash256;
      Gen    : U48;
      Rnd    : Kome.Crypto.Random_Bytes;
      K      : out Key256)
     with Global => null,
          Pre    => Kome.Crypto.Is_Valid (Issuer),
          Post   => K = Gen_Key_Of (Issuer, Cid, Gen, Rnd);

   ---------------------------------------------------------------------------
   --  The roster's ephemeral secret and box_pk (AUDIT.md A6, G7)
   ---------------------------------------------------------------------------

   --  eph_sk = f (k_g, "kome/eph" ‖ cid ‖ u48 (gen) ‖ signer). Ghost: it is
   --  a secret, so only contracts name it, and no executable function
   --  result holds it (Box_PK_Of and Box_Key compute it into a buffer that
   --  they wipe).
   function Eph_SK_Of
     (K : Key256; Cid : Hash256; Gen : U48; Signer : Pubkey) return Kome.Crypto.DH_Secret
   is (Kome.Crypto.Blake2b_256_Keyed (Kome.Keys.To_Bytes (K), Eph_Input (Cid, Gen, Signer)))
     with Ghost, Global => null;

   --  box_pk = X25519_Public (eph_sk) for the roster (cid, gen, signer)
   --  that carries k_g. A roster builder puts this in the box_pk field,
   --  and Box_Key seals every member box of that roster under the same
   --  eph_sk (its Post names Box_PK_Of with the same inputs), so the field
   --  and the boxes agree by construction (G7). It is reduced
   --  (Kome.Crypto.Is_Canonical_U), as every X25519_Public is.
   function Box_PK_Of
     (K : Key256; Cid : Hash256; Gen : U48; Signer : Pubkey) return Pubkey
     with Global => null,
          Post   => Box_PK_Of'Result
                      = Kome.Crypto.X25519_Public (Eph_SK_Of (K, Cid, Gen, Signer))
                    and then Kome.Crypto.Is_Canonical_U (Box_PK_Of'Result);

   ---------------------------------------------------------------------------
   --  Member boxes (SIMPLIFY.md §2 ROSTER members[] { sign_pk[32] dh_pk[32]
   --  nonce[24] box[48] })
   ---------------------------------------------------------------------------

   --  The synthetic nonce of the box of member dh_pk that seals K:
   --  f (K, "kome/box" ‖ dh_pk)[0:24]. Its completion is in the private part.
   function Box_Nonce (K : Key256; DH_PK : Pubkey) return Nonce
     with Global => null;

   function Cipher_Of (B : Kome.Box) return Kome.Crypto.AEAD_Key is
     (B (0 .. Cipher_Len - 1))
     with Global => null;

   function Tag_Of (B : Kome.Box) return Kome.Crypto.Tag is
     (B (Cipher_Len .. Box_Len - 1))
     with Global => null;

   --  Written byte by byte, without a quantifier: a public quantified
   --  expression function is an axiom in each client (CONVENTIONS.md
   --  rule 2). Kome.Crypto.Is_Zero has this form for the same reason.
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

   function Is_Zero_Nonce (N : Nonce) return Boolean is
     (N (0) = 0 and then N (1) = 0 and then N (2) = 0 and then N (3) = 0
      and then N (4) = 0 and then N (5) = 0 and then N (6) = 0 and then N (7) = 0
      and then N (8) = 0 and then N (9) = 0 and then N (10) = 0 and then N (11) = 0
      and then N (12) = 0 and then N (13) = 0 and then N (14) = 0 and then N (15) = 0
      and then N (16) = 0 and then N (17) = 0 and then N (18) = 0 and then N (19) = 0
      and then N (20) = 0 and then N (21) = 0 and then N (22) = 0 and then N (23) = 0)
     with Global => null;

   --  The reduced-encoding test comes from Kome.Crypto (DESIGN.md §2
   --  rule 3, E5: decode and box share one definition).
   function Is_Reduced_U (U : Pubkey) return Boolean
     renames Kome.Crypto.Is_Reduced_U;

   --  Package-local result: Kome.Status has no code for these refusals.
   type Box_Status is
     (Box_OK,
      Non_Canonical_Peer, --  the peer's X25519 key is not reduced
                          --  (Is_Reduced_U): bit 255 is set or u >= p.
                          --  Refused before an exchange (see the header).
      Low_Order_Peer,     --  the peer key is one of the reduced low-order
                          --  encodings (Kome.Crypto.Is_Low_Order_U), or the
                          --  exchange is not contributory for a different
                          --  reason (the "shared" secret is all zeros).
                          --  Refused.
      Not_Authentic);     --  Unbox only. The tag did not verify (wrong key,
                          --  nonce, gen, collection, member, box_pk, or a
                          --  tampered box). Or the tag verified, but the
                          --  nonce is not the synthetic nonce of the opened
                          --  key, or the opened key is all zeros.

   --  Seal K, the collection key of the roster (Cid, Gen, Signer), to the
   --  member (Member_DH_PK, Member_Sign_PK). The roster's ephemeral secret
   --  is derived here (A6): eph_sk = Eph_SK_Of (K, Cid, Gen, Signer), wiped
   --  before the return, and Box_PK = Box_PK_Of of the same inputs is the
   --  roster's box_pk. N is the synthetic nonce. Sealed is cipher[32] ‖
   --  tag[16] (see the header).
   --    * Pre: K is not the all-zero key (A27).
   --    * Box_PK is Box_PK_Of (...) in every case (G7).
   --    * If Member_DH_PK is not reduced, the status is Non_Canonical_Peer.
   --    * If Member_DH_PK is low-order, the status is Low_Order_Peer.
   --    * On a refusal, N and Sealed are all zeros.
   --    * The status is Box_OK only for a good key (Is_Good_DH_Key). Then N
   --      is Box_Nonce (K, Member_DH_PK).
   --  Box_Key never gives Not_Authentic. Monocypher makes the cipher bytes
   --  (no Post on them; the test main checks known answers and the round
   --  trip).
   procedure Box_Key
     (K              : Key256;
      Cid            : Hash256;
      Gen            : U48;
      Signer         : Pubkey;
      Member_DH_PK   : Pubkey;
      Member_Sign_PK : Pubkey;
      Box_PK         : out Pubkey;
      N              : out Nonce;
      Sealed         : out Kome.Box;
      Status         : out Box_Status)
     with Global => null,
          Pre    => K /= Zero_Key,
          Post   => Status /= Not_Authentic
                    and then Box_PK = Box_PK_Of (K, Cid, Gen, Signer)
                    and then (Status = Non_Canonical_Peer)
                               = not Kome.Crypto.Is_Reduced_U (Member_DH_PK)
                    and then (if Status = Box_OK
                              then Kome.Crypto.Is_Good_DH_Key (Member_DH_PK)
                                   and then N = Box_Nonce (K, Member_DH_PK))
                    and then (if Status /= Box_OK
                              then Is_Zero_Box (Sealed) and then Is_Zero_Nonce (N));

   --  Open a member box. The inputs are the member's X25519 secret (its
   --  dh_pk = X25519_Public (Member_Secret), computed here), its sign_pk,
   --  the roster's box_pk, the collection and gen that the box claims, and
   --  the box's nonce. Box_OK means three things: the tag verified under
   --  the wrap key computed again here, N is the synthetic nonce of the
   --  opened key for this member, and that key is not all zeros. K is then
   --  the sealed key. If not, K = Zero_Key. If Box_PK is not reduced, the
   --  status is Non_Canonical_Peer. If Box_PK is low-order, the status is
   --  Low_Order_Peer.
   procedure Unbox_Key
     (Member_Secret  : Kome.Crypto.DH_Secret;
      Member_Sign_PK : Pubkey;
      Box_PK         : Pubkey;
      Cid            : Hash256;
      Gen            : U48;
      N              : Nonce;
      Sealed         : Kome.Box;
      K              : out Key256;
      Status         : out Box_Status)
     with Global => null,
          Post   => (Status = Non_Canonical_Peer)
                      = not Kome.Crypto.Is_Reduced_U (Box_PK)
                    and then (if Status = Box_OK
                              then Kome.Crypto.Is_Good_DH_Key (Box_PK)
                                   and then K /= Zero_Key
                                   and then N = Box_Nonce
                                     (K, Kome.Crypto.X25519_Public (Member_Secret)))
                    and then (if Status /= Box_OK then K = Zero_Key);

   ---------------------------------------------------------------------------
   --  The bundle key (DESIGN.md §8 sealed bundles; S4)
   ---------------------------------------------------------------------------

   --  bundle_key = f (k_g, "kome/bundle"). bundle_key (F) is the key that
   --  my entry in ROSTER_eff unboxes; a sender keeps the previous k_g for
   --  the H17 store-and-forward bundle (S4).
   function Bundle_Key_Of (K : Key256) return Key256
     with Global => null,
          Post   => Bundle_Key_Of'Result
                      = Kome.Keys.To_Key256
                          (Kome.Crypto.Blake2b_256_Keyed (Kome.Keys.To_Bytes (K), Bundle_Label));

private

   function Box_Nonce (K : Key256; DH_PK : Pubkey) return Nonce is
     (Kome.Crypto.Blake2b_256_Keyed (Kome.Keys.To_Bytes (K), Box_Label & DH_PK)
        (0 .. Nonce_Len - 1));

end Kome.Epochs;
