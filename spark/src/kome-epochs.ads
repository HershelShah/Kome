--  Kome.Epochs: the hash-chained epoch keys, the member boxes and the
--  segment links of DESIGN.md §6 ("Membership is key possession", "Epoch
--  segments and several roots", "Boxes (D5, D6)"; decisions D5, D6, E3).
--
--  THE CHAIN. Within a segment, k_e = BLAKE2b-256 (k_{e+1} ‖ "prev"). The
--  founding key draws a random top key k_Top at an epoch Top <= 2**16 - 1
--  ("2^16 epochs are sufficient for the life of any collection", §6; the
--  range is Kome.Epoch). The chain is derived downward from k_Top.
--  The caller gives the randomness: no part of this package reads an RNG
--  or a clock. Step is one link of the chain (one BLAKE2b-256 call through
--  Kome.Crypto). Derive (K, From, To) walks From - To links down.
--
--  WHAT IS PROVED, AND WHAT IS NOT. T14 is epoch secrecy: a key that is
--  not in roster e or in any later roster cannot derive k_e' for e' >= e.
--  T14 is a paper reduction to BLAKE2b's one-wayness (A2) and to the
--  AEAD. It is not a machine theorem (DESIGN.md §9). This package proves
--  that the code computes the correct chain:
--
--    * Step is opaque. The prover knows nothing about BLAKE2b and uses it
--      as an uninterpreted function. Iter (K, N) is the ghost model "Step
--      applied N times". The Post of Derive says that Derive is exactly
--      Iter (K, From - To). The loop that computes it runs at most
--      Max_Steps = 2**16 - 1 times. The type of its index sets this bound.
--    * The chain algebra, as ghost lemmas over the opaque Step:
--      Lemma_Derive_Identity (Derive (K, e, e) = K),
--      Lemma_Derive_Compose  (Derive (Derive (K, a, b), b, c)
--                             = Derive (K, a, c)),
--      Lemma_Derive_Step     (one epoch down is one Step),
--      Lemma_Derive_Shift    (only the distance From - To is important),
--      and the underlying Lemma_Iter_Add on the model.
--    * The API goes only down (Pre: To <= From). No operation maps k_e to
--      k_{e+1}. This is the code shape of T14. The content of T14 (that
--      no other operation can do this) is A2.
--    * Boxes and links (DESIGN.md §6 "Boxes (D5, D6)"):
--      - The prover checks the byte layout of a box (ciphertext ‖ tag,
--        32 + 16 = Box_Len = 48 bytes) and of each hash input (155, 74
--        and 59 bytes) on each slice and concatenation.
--      - A peer key that is not reduced (Kome.Crypto.Is_Reduced_U) gets
--        the refusal Non_Canonical_Peer.
--      - A low-order peer key gets the refusal Low_Order_Peer. The test
--        is Kome.Crypto.Is_Low_Order_U, and again the non-contributory
--        check of the exchange.
--      - The status of a box is Box_OK only for a peer key that passes
--        Kome.Crypto.Is_Good_DH_Key.
--      - A refused box, nonce or key is all zeros. The Posts say this.
--      - The Post of Seal_Link gives the synthetic nonce exactly
--        (N = Synthetic_Nonce (Link_Key (K_S, Ns, S), K_Prev)). The Post
--        of Open_Link says that a link that it accepts has exactly that
--        nonce for the key that it returns.
--      - The same is true for member boxes. The Post of Box_Key gives
--        N = Synthetic_Nonce (wrap_key, k_e) for a box that it seals.
--        The Post of Unbox_Key says that a box that it opens has exactly
--        that nonce for the key that it returns. Here wrap_key =
--        Wrap_Key_Of (the ghost model, over the ghost
--        Kome.Crypto.X25519_Shared).
--      - The body builds a buffer field by field, hashes it and wipes it.
--        Lemma_Blake2b_Congruent of Kome.Crypto (an axiom: a hash depends
--        only on the bytes of its input) ties that buffer's digest to the
--        model.
--      - Open (Seal (k)) = k is monocypher's AEAD guarantee. It is
--        not a proof obligation (a crypto oracle). The test main runs it
--        and checks known answers from an independent Python reference
--        (vectors/epochs.txt).
--
--  BOX CONSTRUCTION (DESIGN.md §6, decisions D5 and D6 of §1). There is
--  no root X25519 key. Each ROSTER has box_pk = X25519_Public (eph_sk).
--  The signer draws the fresh ephemeral secret eph_sk for that one roster
--  (the caller gives the randomness: no RNG here). The signer seals that
--  roster's boxes with eph_sk and then wipes it. Labels are ASCII with no
--  terminator, u16 is big-endian, and ns is the 16 bytes of
--  Kome.Keys.To_Bytes (Ns). For member (sign_pk, dh_pk) of a roster at
--  epoch e in collection ns:
--    wrap_key = BLAKE2b-256 ("kome/wrap" ‖ X25519 (eph_sk, dh_pk) ‖ box_pk
--                            ‖ dh_pk ‖ sign_pk ‖ ns ‖ u16 (e))   (155 bytes)
--    nonce    = BLAKE2b-256 ("kome/nonce" ‖ wrap_key ‖ k_e)[0:24]
--    box      = XChaCha20-Poly1305 (wrap_key, nonce, AD = ns ‖ u16 (e), k_e)
--             = cipher[32] ‖ tag[16].
--  The member computes X25519 (dh_sk, box_pk) and opens the box. Then it
--  computes the nonce again from the opened key and refuses a mismatch
--  (Not_Authentic), so exactly one box opens for each (wrap_key, k_e).
--  A segment that starts at epoch s (DESIGN.md §6 "Epoch segments", E3)
--  has a link that seals k_{s-1}:
--    link_key = BLAKE2b-256 ("kome/link" ‖ k_s ‖ ns ‖ u16 (s))   (59 bytes)
--    nonce    = BLAKE2b-256 ("kome/nonce" ‖ link_key ‖ k_{s-1})[0:24]
--    link box = XChaCha20-Poly1305 (link_key, nonce, AD = ns ‖ u16 (s),
--                                   k_{s-1}).
--  Within a segment, the chain step k_e = BLAKE2b-256 (k_{e+1} ‖ "prev")
--  does not change. Segment boundaries are fixed (AUDIT.md H6): segment j
--  covers the epochs [Segment_Len * j, Segment_Len * j + Segment_Len - 1],
--  so its top is Segment_Top (j), and the founding key opens segment j + 1
--  at Segment_Top (j) + 1 without a fresh F. Kome.Roster (phase 8) opens
--  segments (founding key only), draws the top keys and delivers them.
--  This package gives only the arithmetic of the boundaries.
--  The wrap key contains ns, the epoch and the two member keys, so two
--  boxes for one member at epochs 5 and 6 never share a key, also under a
--  reused eph_sk. A removed member that holds k5 learns nothing about k6
--  when it XORs the two boxes (the test main has a regression test).
--
--  CANONICAL PEER KEYS. X25519 reads a u-coordinate modulo p = 2**255 - 19
--  and ignores bit 255, so one point has several 32-byte encodings with
--  the same shared secret. But the wrap key hashes the encoding. A member
--  opens its box with its own X25519_Public, which is always the reduced
--  encoding (u < p, bit 255 clear). A box sealed to a different encoding
--  of the same point gets Box_OK, but its member can never open it. The
--  two sides accept only reduced encodings (Is_Reduced_U, defined in
--  Kome.Crypto and renamed here). They refuse all other encodings with
--  Non_Canonical_Peer. Decode refuses them before this (DESIGN.md §2
--  rule 3, E5).
--
--  SECRETS. Step, Box_Key, Unbox_Key, Seal_Link and Open_Link erase each
--  named byte buffer that holds a secret with Kome.Crypto.Wipe before each
--  return. These buffers are the X25519 output, the wrap or link key, the
--  hash inputs that contain them, the nonce digest, the plaintext epoch
--  key, and the input and digest of Step. (Step can call the procedure
--  form of BLAKE2b-256 and Wipe because the two are Always_Terminates.)
--  Some data cannot be erased:
--    * the temporaries of the expression functions Nonce_Input and
--      Link_Input. They hold copies of keys while their result goes into a
--      named buffer (that buffer is wiped);
--    * the compiler temporary for Step's input expression.
--  The ghost models Wrap_Input and Wrap_Key_Of run only under -gnata.
--  Key256 values are ordinary records (the lattice convention for keys).
--  This package does not wipe them.
pragma Ada_2022;
with Kome.Crypto;
with Kome.Keys;
package Kome.Epochs with SPARK_Mode, Preelaborate is

   ---------------------------------------------------------------------------
   --  The chain
   ---------------------------------------------------------------------------

   --  DESIGN.md §6: 2^16 epochs, so a walk from the top epoch to epoch 0
   --  is at most 2**16 - 1 links (Kome.Epoch is 0 .. 2**16 - 1).
   Max_Steps : constant := 2**16 - 1;
   subtype Steps is Natural range 0 .. Max_Steps;

   --  The label hashed after the key: ASCII "prev" (DESIGN.md §6).
   Prev_Label_Len : constant := 4;

   --  Fixed segment boundaries (DESIGN.md §6 "Epoch segments", AUDIT.md
   --  H6). Segment j covers [Segment_Start (j), Segment_Top (j)], and the
   --  last segment ends at the last epoch. The founding key opens segment
   --  j + 1 at Segment_Top (j) + 1 = Segment_Start (j + 1). So a founding
   --  device that is behind on F still knows where the next segment
   --  starts: it needs only the top of the segment that it is in.
   Segment_Len  : constant := 4096;
   Segments_Max : constant := (Epoch'Last + 1) / Segment_Len;   --  16
   subtype Segment_Index is Natural range 0 .. Segments_Max - 1;

   function Segment_Of (E : Epoch) return Segment_Index is
     (Natural (E) / Segment_Len);

   function Segment_Start (J : Segment_Index) return Epoch is
     (Epoch (J * Segment_Len));

   function Segment_Top (J : Segment_Index) return Epoch is
     (Epoch (J * Segment_Len + Segment_Len - 1));

   --  The epoch of a roster is in the segment of the newest segment start
   --  that it knows (a link's from_epoch), and the roster that opens
   --  segment j + 1 carries a link with from_epoch = Segment_Start (j + 1).
   procedure Lemma_Segment_Bounds (E : Epoch) with
     Ghost, Global => null,
     Post => Segment_Start (Segment_Of (E)) <= E
             and then E <= Segment_Top (Segment_Of (E))
             and then (if Segment_Of (E) < Segments_Max - 1
                       then Segment_Top (Segment_Of (E)) + 1
                            = Segment_Start (Segment_Of (E) + 1));

   --  One link: Step (k_{e+1}) = k_e = BLAKE2b-256 (k_{e+1} ‖ "prev"). The
   --  32 bytes of the key are in the big-endian order of Kome.Keys. Step is
   --  opaque on purpose (no Post): the chain algebra below is true for any
   --  function. The test checks the result of Step against hashlib.
   function Step (K : Key256) return Key256
     with Global => null;

   --  Ghost model: Step applied N times. The variant bounds the recursion
   --  (CONVENTIONS.md: no recursion unless a Subprogram_Variant bounds it).
   --  It has no quantifier, so it is public.
   function Iter (K : Key256; N : Steps) return Key256 is
     (if N = 0 then K else Step (Iter (K, N - 1)))
     with Ghost, Global => null,
          Subprogram_Variant => (Decreases => N);

   --  The key at epoch To, from the key K at epoch From >= To: From - To
   --  links down the chain. DESIGN.md §6. This refines the chain that the
   --  T14 paper argument uses (only downward derivation exists).
   function Derive (K : Key256; From, To : Epoch) return Key256
     with Global => null,
          Pre    => To <= From,
          Post   => Derive'Result = Iter (K, Natural (From) - Natural (To));

   ---------------------------------------------------------------------------
   --  Chain algebra (ghost lemmas; the law is the Post). DESIGN.md §6.
   ---------------------------------------------------------------------------

   --  To iterate M times and then N times is to iterate M + N times.
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

   --  Derivation composes: a walk a -> b and then b -> c is a walk a -> c.
   --  As a result, "a member that holds k_e derives each older key" (§6)
   --  does not depend on the route.
   procedure Lemma_Derive_Compose (K : Key256; A, B, C : Epoch)
     with Ghost, Global => null,
          Pre  => C <= B and then B <= A,
          Post => Derive (Derive (K, A, B), B, C) = Derive (K, A, C);

   --  Only the distance is important: Derive (K, a, b) = Derive (K, a', b')
   --  if a - b = a' - b'.
   procedure Lemma_Derive_Shift (K : Key256; A, B, A2, B2 : Epoch)
     with Ghost, Global => null,
          Pre  => B <= A and then B2 <= A2
                  and then Natural (A) - Natural (B) = Natural (A2) - Natural (B2),
          Post => Derive (K, A, B) = Derive (K, A2, B2);

   ---------------------------------------------------------------------------
   --  Boxes and links (DESIGN.md §2 ROSTER box_pk[32],
   --  links[] { from_epoch:u16 nonce[24] box[48] },
   --  members[] { sign_pk[32] dh_pk[32] nonce[24] box[48] }; §6 "Boxes")
   ---------------------------------------------------------------------------

   --  The layout of a box: the AEAD ciphertext of the 32-byte key, then the
   --  16-byte Poly1305 tag. Kome.Box_Len = 48 is the sum.
   Cipher_Len : constant := Kome.Crypto.AEAD_Key_Len;
   Tag_Len    : constant := Kome.Crypto.Tag_Len;
   pragma Compile_Time_Error
     (Box_Len /= Cipher_Len + Tag_Len, "DESIGN.md §2: box[48] = cipher[32] ‖ tag[16]");
   pragma Compile_Time_Error
     (Cipher_Len /= Hash_Len, "an epoch key is a BLAKE2b-256 digest");

   --  The AD bound into each box and link: ns[16] ‖ u16 (epoch),
   --  big-endian.
   AD_Len : constant := NS_Len + 2;

   --  The labels (ASCII, no terminator; DESIGN.md §2 "all tags and labels").
   Wrap_Label_Len  : constant := 9;    --  "kome/wrap"
   Nonce_Label_Len : constant := 10;   --  "kome/nonce"
   Link_Label_Len  : constant := 9;    --  "kome/link"
   Wrap_Label  : constant Byte_Array (0 .. Wrap_Label_Len - 1) :=
     [16#6B#, 16#6F#, 16#6D#, 16#65#, 16#2F#, 16#77#, 16#72#, 16#61#, 16#70#];
   Nonce_Label : constant Byte_Array (0 .. Nonce_Label_Len - 1) :=
     [16#6B#, 16#6F#, 16#6D#, 16#65#, 16#2F#, 16#6E#, 16#6F#, 16#6E#, 16#63#, 16#65#];
   Link_Label  : constant Byte_Array (0 .. Link_Label_Len - 1) :=
     [16#6B#, 16#6F#, 16#6D#, 16#65#, 16#2F#, 16#6C#, 16#69#, 16#6E#, 16#6B#];

   --  The three hash inputs and their lengths (DESIGN.md §6 "Boxes").
   --  wrap: label ‖ X25519 output ‖ box_pk ‖ dh_pk ‖ sign_pk ‖ ns ‖ u16 (e)
   Wrap_Input_Len  : constant :=
     Wrap_Label_Len + Kome.Crypto.DH_Key_Len + 3 * Pubkey_Len + NS_Len + 2;
   --  nonce: label ‖ key ‖ sealed key
   Nonce_Input_Len : constant := Nonce_Label_Len + 2 * Hash_Len;
   --  link: label ‖ k_s ‖ ns ‖ u16 (s)
   Link_Input_Len  : constant := Link_Label_Len + Hash_Len + NS_Len + 2;
   pragma Compile_Time_Error
     (Wrap_Input_Len /= 155, "DESIGN.md §6: the wrap-key input is 155 bytes");
   pragma Compile_Time_Error
     (Nonce_Input_Len /= 74 or else Link_Input_Len /= 59,
      "DESIGN.md §6: nonce input 74 bytes, link input 59 bytes");

   subtype Wrap_Input_Bytes  is Byte_Array (0 .. Wrap_Input_Len - 1);
   subtype Nonce_Input_Bytes is Byte_Array (0 .. Nonce_Input_Len - 1);
   subtype Link_Input_Bytes  is Byte_Array (0 .. Link_Input_Len - 1);

   --  Offsets of the wrap-key input's fields.
   Wrap_O_Shared : constant := Wrap_Label_Len;                      --    9
   Wrap_O_Box    : constant := Wrap_O_Shared + Kome.Crypto.DH_Key_Len; --   41
   Wrap_O_DH     : constant := Wrap_O_Box + Pubkey_Len;              --   73
   Wrap_O_Sign   : constant := Wrap_O_DH + Pubkey_Len;               --  105
   Wrap_O_Ns     : constant := Wrap_O_Sign + Pubkey_Len;             --  137
   Wrap_O_E      : constant := Wrap_O_Ns + NS_Len;                   --  153
   pragma Compile_Time_Error
     (Wrap_O_E + 2 /= Wrap_Input_Len, "wrap-key input layout");

   --  Byte J of "kome/wrap" ‖ shared ‖ box_pk ‖ dh_pk ‖ sign_pk ‖ ns ‖
   --  u16 (e), position by position. This is the wrap-key input of a member
   --  box (DESIGN.md §6 D6). It is ghost because it reads the shared
   --  secret, so only contracts use it (the body builds the same bytes in
   --  a buffer that it wipes).
   function Wrap_Byte
     (Shared  : Kome.Crypto.Shared_Secret;
      Box_PK  : Pubkey;
      DH_PK   : Pubkey;
      Sign_PK : Pubkey;
      Ns      : Id128;
      E       : Epoch;
      J       : Natural) return Byte
     with Ghost, Global => null, Pre => J < Wrap_Input_Len;

   --  The full wrap-key input. It is ghost for the same reason.
   function Wrap_Input
     (Shared  : Kome.Crypto.Shared_Secret;
      Box_PK  : Pubkey;
      DH_PK   : Pubkey;
      Sign_PK : Pubkey;
      Ns      : Id128;
      E       : Epoch) return Wrap_Input_Bytes
     with Ghost, Global => null,
          Post => (for all J in 0 .. Wrap_Input_Len - 1 =>
                     Wrap_Input'Result (J) = Wrap_Byte (Shared, Box_PK, DH_PK, Sign_PK, Ns, E, J));

   --  wrap_key = BLAKE2b-256 (Wrap_Input (...)), as a key. It is ghost.
   --  Like Link_Key, it is opaque to clients.
   function Wrap_Key_Of
     (Shared  : Kome.Crypto.Shared_Secret;
      Box_PK  : Pubkey;
      DH_PK   : Pubkey;
      Sign_PK : Pubkey;
      Ns      : Id128;
      E       : Epoch) return Key256
     with Ghost, Global => null;

   --  "kome/nonce" ‖ Key ‖ K, with the keys in the byte order of Kome.Keys.
   --  The keys are records (CONVENTIONS.md rule 1), so equal keys give
   --  the same term, and the nonce below is a congruence of its arguments.
   function Nonce_Input (Key, K : Key256) return Nonce_Input_Bytes
     with Global => null;

   --  The synthetic nonce of a box or link that seals K under the AEAD key
   --  Key: BLAKE2b-256 ("kome/nonce" ‖ Key ‖ K)[0:24]. It is opaque to
   --  clients (its definition is in the private part).
   function Synthetic_Nonce (Key, K : Key256) return Nonce
     with Global => null;

   --  "kome/link" ‖ k_s ‖ ns ‖ u16 (s).
   function Link_Input (K_S : Key256; Ns : Id128; S : Epoch) return Link_Input_Bytes
     with Global => null;

   --  link_key = BLAKE2b-256 ("kome/link" ‖ k_s ‖ ns ‖ u16 (s)), as a key.
   --  It is opaque to clients.
   function Link_Key (K_S : Key256; Ns : Id128; S : Epoch) return Key256
     with Global => null;

   function Cipher_Of (B : Kome.Box) return Kome.Crypto.AEAD_Key is
     (B (0 .. Cipher_Len - 1))
     with Global => null;

   function Tag_Of (B : Kome.Box) return Kome.Crypto.Tag is
     (B (Cipher_Len .. Box_Len - 1))
     with Global => null;

   --  The all-zero key: a refusal gives this key.
   Zero_Key : constant Key256 := (others => 0);

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
      Not_Authentic);     --  Unbox and Open only. The tag did not verify
                          --  (wrong key, nonce, epoch, collection, member,
                          --  box_pk, or a tampered box). Or the tag
                          --  verified, but the nonce is not the synthetic
                          --  nonce of the opened key.

   --  Seal Epoch_Key, the epoch-E key of collection Ns, to the member
   --  (Member_DH_PK, Member_Sign_PK) of a roster. The roster's ephemeral
   --  secret is Eph_Secret (box_pk = X25519_Public (Eph_Secret),
   --  computed here). N is the synthetic nonce. Sealed is
   --  cipher[32] ‖ tag[16] (see the header).
   --    * If Member_DH_PK is not reduced, the status is Non_Canonical_Peer.
   --    * If Member_DH_PK is low-order, the status is Low_Order_Peer.
   --    * On a refusal, N and Sealed are all zeros.
   --    * The status is Box_OK only for a good key (Is_Good_DH_Key). Then N
   --      is the synthetic nonce of Epoch_Key under the wrap key of this
   --      member, epoch and collection (D6).
   --  Box_Key never gives Not_Authentic. Monocypher makes the cipher bytes
   --  (no Post on them; the test main checks known answers and the round
   --  trip).
   procedure Box_Key
     (Eph_Secret     : Kome.Crypto.DH_Secret;
      Member_DH_PK   : Pubkey;
      Member_Sign_PK : Pubkey;
      Ns             : Id128;
      E              : Epoch;
      Epoch_Key      : Key256;
      N              : out Nonce;
      Sealed         : out Kome.Box;
      Status         : out Box_Status)
     with Global => null,
          Post   => Status /= Not_Authentic
                    and then (Status = Non_Canonical_Peer)
                               = not Kome.Crypto.Is_Reduced_U (Member_DH_PK)
                    and then (if Status = Box_OK
                              then Kome.Crypto.Is_Good_DH_Key (Member_DH_PK)
                                   and then N = Synthetic_Nonce
                                     (Wrap_Key_Of
                                        (Kome.Crypto.X25519_Shared (Eph_Secret, Member_DH_PK),
                                         Kome.Crypto.X25519_Public (Eph_Secret),
                                         Member_DH_PK, Member_Sign_PK, Ns, E),
                                      Epoch_Key))
                    and then (if Status /= Box_OK
                              then Is_Zero_Box (Sealed) and then Is_Zero_Nonce (N));

   --  Open a member box. The inputs are the member's X25519 secret
   --  (its dh_pk = X25519_Public (Member_Secret), computed here), its
   --  sign_pk, the roster's box_pk, the collection and epoch that the box
   --  claims, and the box's nonce. Box_OK means two things: the
   --  tag verified under the wrap key computed again here, AND N is the
   --  synthetic nonce of the opened key. Epoch_Key is then the sealed key.
   --  If not, Epoch_Key = Zero_Key. If Box_PK is not reduced, the status
   --  is Non_Canonical_Peer. If Box_PK is low-order, the status is
   --  Low_Order_Peer. The Post gives the nonce check: on Box_OK, N is the
   --  synthetic nonce of the returned key under this member's wrap key
   --  (D6).
   procedure Unbox_Key
     (Member_Secret  : Kome.Crypto.DH_Secret;
      Member_Sign_PK : Pubkey;
      Box_PK         : Pubkey;
      Ns             : Id128;
      E              : Epoch;
      N              : Nonce;
      Sealed         : Kome.Box;
      Epoch_Key      : out Key256;
      Status         : out Box_Status)
     with Global => null,
          Post   => (Status = Non_Canonical_Peer)
                      = not Kome.Crypto.Is_Reduced_U (Box_PK)
                    and then (if Status = Box_OK
                              then Kome.Crypto.Is_Good_DH_Key (Box_PK)
                                   and then N = Synthetic_Nonce
                                     (Wrap_Key_Of
                                        (Kome.Crypto.X25519_Shared (Member_Secret, Box_PK),
                                         Box_PK,
                                         Kome.Crypto.X25519_Public (Member_Secret),
                                         Member_Sign_PK, Ns, E),
                                      Epoch_Key))
                    and then (if Status /= Box_OK then Epoch_Key = Zero_Key);

   --  Seal K_Prev = k_{s-1}, the last key of the previous segment, under
   --  link_key = Link_Key (K_S, Ns, S). K_S = k_s is the first key of the
   --  segment that starts at epoch S >= 1 (DESIGN.md §6, E3). N is the
   --  synthetic nonce. The Post gives N exactly.
   procedure Seal_Link
     (K_S    : Key256;
      Ns     : Id128;
      S      : Epoch;
      K_Prev : Key256;
      N      : out Nonce;
      Sealed : out Kome.Box)
     with Global => null,
          Pre    => S >= 1,
          Post   => N = Synthetic_Nonce (Link_Key (K_S, Ns, S), K_Prev);

   --  Open a link {from_epoch = S, nonce N, box Sealed} with k_s. Box_OK
   --  means that the tag verified and N is the synthetic nonce of the
   --  opened key. That key is K_Prev. If not, K_Prev = Zero_Key and the
   --  status is Not_Authentic (a link has no peer key to refuse).
   procedure Open_Link
     (K_S    : Key256;
      Ns     : Id128;
      S      : Epoch;
      N      : Nonce;
      Sealed : Kome.Box;
      K_Prev : out Key256;
      Status : out Box_Status)
     with Global => null,
          Post   => (Status = Box_OK or else Status = Not_Authentic)
                    and then (if Status = Box_OK
                              then N = Synthetic_Nonce (Link_Key (K_S, Ns, S), K_Prev)
                              else K_Prev = Zero_Key);

private

   function Wrap_Byte
     (Shared  : Kome.Crypto.Shared_Secret;
      Box_PK  : Pubkey;
      DH_PK   : Pubkey;
      Sign_PK : Pubkey;
      Ns      : Id128;
      E       : Epoch;
      J       : Natural) return Byte
   is (if    J < Wrap_O_Shared then Wrap_Label (J)
       elsif J < Wrap_O_Box    then Shared (J - Wrap_O_Shared)
       elsif J < Wrap_O_DH     then Box_PK (J - Wrap_O_Box)
       elsif J < Wrap_O_Sign   then DH_PK (J - Wrap_O_DH)
       elsif J < Wrap_O_Ns     then Sign_PK (J - Wrap_O_Sign)
       elsif J < Wrap_O_E      then Kome.Keys.Byte_At (Ns, J - Wrap_O_Ns)
       elsif J = Wrap_O_E      then Byte (Natural (E) / 256)
       else Byte (Natural (E) mod 256));

   function Wrap_Key_Of
     (Shared  : Kome.Crypto.Shared_Secret;
      Box_PK  : Pubkey;
      DH_PK   : Pubkey;
      Sign_PK : Pubkey;
      Ns      : Id128;
      E       : Epoch) return Key256
   is (Kome.Keys.To_Key256
         (Kome.Crypto.Blake2b_256 (Wrap_Input (Shared, Box_PK, DH_PK, Sign_PK, Ns, E))));

   function Nonce_Input (Key, K : Key256) return Nonce_Input_Bytes is
     (Nonce_Label & Kome.Keys.To_Bytes (Key) & Kome.Keys.To_Bytes (K));

   function Synthetic_Nonce (Key, K : Key256) return Nonce is
     (Kome.Crypto.Blake2b_256 (Nonce_Input (Key, K)) (0 .. Nonce_Len - 1));

   function Link_Input (K_S : Key256; Ns : Id128; S : Epoch) return Link_Input_Bytes is
     (Link_Label & Kome.Keys.To_Bytes (K_S) & Kome.Keys.To_Bytes (Ns)
      & Byte (Natural (S) / 256) & Byte (Natural (S) mod 256));

   function Link_Key (K_S : Key256; Ns : Id128; S : Epoch) return Key256 is
     (Kome.Keys.To_Key256 (Kome.Crypto.Blake2b_256 (Link_Input (K_S, Ns, S))));

end Kome.Epochs;
