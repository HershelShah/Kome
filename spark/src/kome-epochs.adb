--  Kome.Epochs body. The spec tells what is proved and what is a crypto
--  oracle. Key_For_Gen, Box_PK_Of, Box_Key, Unbox_Key and Bundle_Key_Of
--  wipe each named secret byte buffer before they return. gnatprove's flow
--  analysis reports that these final Wipes have no effect on the SPARK
--  model. This is their purpose (Kome.Crypto.Wipe).
pragma Ada_2022;

package body Kome.Epochs with SPARK_Mode is

   package C renames Kome.Crypto;

   --  Erase secret buffers. gnatprove's flow analysis reports that a
   --  final Wipe has no effect. This is its purpose (Kome.Crypto.Wipe).
   pragma Warnings (GNATprove, Off, "statement has no effect",
                    Reason => "erasing secrets is not a SPARK effect");
   pragma Warnings (GNATprove, Off, "*is set by ""Wipe"" but not used*",
                    Reason => "erasing secrets is not a SPARK effect");

   ---------------------------------------------------------------------------
   --  k_g
   ---------------------------------------------------------------------------

   procedure Key_For_Gen
     (Issuer : Kome.Crypto.Secret_Key;
      Cid    : Hash256;
      Gen    : U48;
      Rnd    : Kome.Crypto.Random_Bytes;
      K      : out Key256)
   is
      D : Hash256;
   begin
      C.Hedge (Issuer, Key_Label, Gen_Ctx (Cid, Gen), Rnd, D);
      K := Kome.Keys.To_Key256 (D);
      C.Wipe (D);
   end Key_For_Gen;

   ---------------------------------------------------------------------------
   --  eph_sk and box_pk
   ---------------------------------------------------------------------------

   --  eph_sk = f (k_g, "kome/eph" ‖ cid ‖ u48 (gen) ‖ signer), into Eph (a
   --  secret: the caller wipes it). The key bytes of k_g are in a wiped
   --  buffer. Post: it is the ghost model Eph_SK_Of.
   procedure Eph_Secret
     (K      : Key256;
      Cid    : Hash256;
      Gen    : U48;
      Signer : Pubkey;
      Eph    : out C.DH_Secret)
     with Global => null,
          Post   => Eph = Eph_SK_Of (K, Cid, Gen, Signer)
   is
      KB : C.Mac_Key := Kome.Keys.To_Bytes (K);
   begin
      C.Blake2b_256_Keyed (KB, Eph_Input (Cid, Gen, Signer), Eph);
      C.Wipe (KB);
   end Eph_Secret;

   function Box_PK_Of
     (K : Key256; Cid : Hash256; Gen : U48; Signer : Pubkey) return Pubkey
   is
      Eph : C.DH_Secret;
      PK  : Pubkey;
   begin
      Eph_Secret (K, Cid, Gen, Signer, Eph);
      --  Eph has the bytes of the ghost model, so X25519_Public gives the
      --  same key on both (no array extensionality in the prover).
      C.Lemma_X25519_Congruent (Eph, Eph_SK_Of (K, Cid, Gen, Signer), Signer);
      PK := C.X25519_Public (Eph);
      C.Wipe (Eph);
      return PK;
   end Box_PK_Of;

   ---------------------------------------------------------------------------
   --  Member boxes
   ---------------------------------------------------------------------------

   --  The synthetic nonce of K for the member DH_PK, computed through
   --  wiped buffers. Post: it is Box_Nonce.
   procedure Nonce_Of (K : Key256; DH_PK : Pubkey; N : out Nonce)
     with Global => null,
          Post   => N = Box_Nonce (K, DH_PK)
   is
      KB     : C.Mac_Key := Kome.Keys.To_Bytes (K);
      Digest : Hash256;
   begin
      C.Blake2b_256_Keyed (KB, Box_Label & DH_PK, Digest);
      N := Digest (0 .. Nonce_Len - 1);
      C.Wipe (KB);
      C.Wipe (Digest);
   end Nonce_Of;

   --  wrap_key = f (shared, "kome/wrap" ‖ box_pk ‖ dh_pk ‖ sign_pk ‖ cid ‖
   --  u48 (gen)), into Key (a secret: the caller wipes it). The input holds
   --  no secret; the key of the keyed hash is the X25519 output.
   procedure Wrap_Key
     (Shared  : C.Shared_Secret;
      Box_PK  : Pubkey;
      DH_PK   : Pubkey;
      Sign_PK : Pubkey;
      Cid     : Hash256;
      Gen     : U48;
      Key     : out Hash256)
     with Global => null
   is
   begin
      C.Blake2b_256_Keyed (Shared, Wrap_Input (Box_PK, DH_PK, Sign_PK, Cid, Gen), Key);
   end Wrap_Key;

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
   is
      Eph          : C.DH_Secret;
      Shared       : C.Shared_Secret;
      Contributory : Boolean;
      WK           : Hash256;
      Plain        : C.AEAD_Key;
      Cipher       : C.AEAD_Key;
      Mac          : C.Tag;
   begin
      --  The derived ephemeral secret (A6) and the roster's box_pk (G7),
      --  the same for every member of the roster.
      Eph_Secret (K, Cid, Gen, Signer, Eph);
      C.Lemma_X25519_Congruent (Eph, Eph_SK_Of (K, Cid, Gen, Signer), Member_DH_PK);
      Box_PK := C.X25519_Public (Eph);
      pragma Assert (Box_PK = Box_PK_Of (K, Cid, Gen, Signer));

      --  Refuse an encoding that is not reduced before an exchange. It would
      --  seal a box that its member's reduced key can never open (see
      --  the spec header).
      if not Is_Reduced_U (Member_DH_PK) then
         N := [others => 0];
         Sealed := [others => 0];
         Status := Non_Canonical_Peer;
         C.Wipe (Eph);
         return;
      end if;
      if C.Is_Low_Order_U (Member_DH_PK) then
         N := [others => 0];
         Sealed := [others => 0];
         Status := Low_Order_Peer;
         C.Wipe (Eph);
         return;
      end if;

      C.X25519 (Eph, Member_DH_PK, Shared, Contributory);
      if not Contributory then
         N := [others => 0];
         Sealed := [others => 0];
         Status := Low_Order_Peer;
         C.Wipe (Eph);
         return;   --  Shared is all zeros already (Kome.Crypto.X25519 Post)
      end if;

      Wrap_Key (Shared, Box_PK, Member_DH_PK, Member_Sign_PK, Cid, Gen, WK);
      Nonce_Of (K, Member_DH_PK, N);
      Plain := Kome.Keys.To_Bytes (K);
      C.Lock (WK, N, Gen_Ctx (Cid, Gen), Plain, Cipher, Mac);
      Sealed := Cipher & Mac;
      Status := Box_OK;

      C.Wipe (Eph);
      C.Wipe (Shared);
      C.Wipe (WK);
      C.Wipe (Plain);
   end Box_Key;

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
   is
      Shared       : C.Shared_Secret;
      Contributory : Boolean;
      WK           : Hash256;
      Plain        : C.AEAD_Key;
      Authentic    : Boolean;
      Expected     : Nonce;
      Opened       : Key256;
   begin
      if not Is_Reduced_U (Box_PK) then
         K := Zero_Key;
         Status := Non_Canonical_Peer;
         return;
      end if;
      if C.Is_Low_Order_U (Box_PK) then
         K := Zero_Key;
         Status := Low_Order_Peer;
         return;
      end if;

      C.X25519 (Member_Secret, Box_PK, Shared, Contributory);
      if not Contributory then
         K := Zero_Key;
         Status := Low_Order_Peer;
         return;   --  Shared is all zeros already (Kome.Crypto.X25519 Post)
      end if;

      Wrap_Key (Shared, Box_PK, C.X25519_Public (Member_Secret),
                Member_Sign_PK, Cid, Gen, WK);
      C.Unlock (WK, N, Gen_Ctx (Cid, Gen), Cipher_Of (Sealed), Tag_Of (Sealed),
                Plain, Authentic);
      K := Zero_Key;
      Status := Not_Authentic;
      if Authentic then
         --  Compute the synthetic nonce again from the opened key. Refuse a
         --  mismatch: exactly one box opens for each (wrap_key, k_g). Refuse
         --  the all-zero key, which no builder seals (Box_Key's Pre).
         Opened := Kome.Keys.To_Key256 (Plain);
         Nonce_Of (Opened, C.X25519_Public (Member_Secret), Expected);
         if Expected = N and then Opened /= Zero_Key then
            K := Opened;
            Status := Box_OK;
         end if;
      end if;

      C.Wipe (Shared);
      C.Wipe (WK);
      C.Wipe (Plain);
   end Unbox_Key;

   ---------------------------------------------------------------------------
   --  The bundle key
   ---------------------------------------------------------------------------

   function Bundle_Key_Of (K : Key256) return Key256 is
      KB     : C.Mac_Key := Kome.Keys.To_Bytes (K);
      Digest : Hash256;
      R      : Key256;
   begin
      C.Blake2b_256_Keyed (KB, Bundle_Label, Digest);
      R := Kome.Keys.To_Key256 (Digest);
      C.Wipe (KB);
      C.Wipe (Digest);
      return R;
   end Bundle_Key_Of;

   pragma Warnings (GNATprove, On, "*is set by ""Wipe"" but not used*");
   pragma Warnings (GNATprove, On, "statement has no effect");

end Kome.Epochs;
