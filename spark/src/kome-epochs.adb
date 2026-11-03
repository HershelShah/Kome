--  Kome.Epochs body. The spec tells what is proved and what is a crypto
--  oracle. Step, Box_Key, Unbox_Key, Seal_Link and Open_Link wipe each named
--  secret byte buffer before they return. gnatprove's flow analysis
--  reports that these final Wipes have no effect on the SPARK model. This
--  is their purpose (Kome.Crypto.Wipe).
pragma Ada_2022;

package body Kome.Epochs with SPARK_Mode is

   package C renames Kome.Crypto;

   --  ASCII "prev".
   Prev_Label : constant Byte_Array (0 .. Prev_Label_Len - 1) :=
     [16#70#, 16#72#, 16#65#, 16#76#];

   ---------------------------------------------------------------------------
   --  Chain
   ---------------------------------------------------------------------------

   --  Erase secret buffers. gnatprove's flow analysis reports that a
   --  final Wipe has no effect. This is its purpose (Kome.Crypto.Wipe).
   pragma Warnings (GNATprove, Off, "statement has no effect",
                    Reason => "erasing secrets is not a SPARK effect");
   pragma Warnings (GNATprove, Off, "*is set by ""Wipe"" but not used*",
                    Reason => "erasing secrets is not a SPARK effect");

   --  The procedure form of BLAKE2b-256 writes into a buffer, so Step
   --  can wipe the input (which holds k_{e+1}) and the digest before it
   --  returns. A function can call the two procedures because they are
   --  Always_Terminates.
   function Step (K : Key256) return Key256 is
      Buf    : Byte_Array (0 .. Hash_Len + Prev_Label_Len - 1) :=
        Kome.Keys.To_Bytes (K) & Prev_Label;
      Digest : Hash256;
      R      : Key256;
   begin
      C.Blake2b_256 (Buf, Digest);
      R := Kome.Keys.To_Key256 (Digest);
      C.Wipe (Buf);
      C.Wipe (Digest);
      return R;
   end Step;

   function Derive (K : Key256; From, To : Epoch) return Key256 is
      --  The invariant states the ghost model Iter again. To evaluate Iter
      --  costs I Steps. If the test ran it on each iteration, the test
      --  would be quadratic (2**31 hashes for a full chain), so it is
      --  proved, not run. The test checks Derive against an independent
      --  reference instead.
      pragma Assertion_Policy (Loop_Invariant => Ignore);
      N : constant Steps := Natural (From) - Natural (To);
      R : Key256 := K;
   begin
      --  At most Max_Steps = 2**16 - 1 iterations: the range of the index
      --  (subtype Steps) is the bound.
      for I in 1 .. N loop
         R := Step (R);
         pragma Loop_Invariant (R = Iter (K, I));
      end loop;
      return R;
   end Derive;

   ---------------------------------------------------------------------------
   --  Chain algebra
   ---------------------------------------------------------------------------

   procedure Lemma_Iter_Add (K : Key256; M, N : Steps) is
   begin
      --  Induction on N, as a loop: Iter (Iter (K, M), I) = Iter (K, M + I)
      --  is true for I = 0 by definition. One more Step on the two sides
      --  keeps it true.
      for I in 0 .. N loop
         pragma Loop_Invariant (Iter (Iter (K, M), I) = Iter (K, M + I));
      end loop;
   end Lemma_Iter_Add;

   procedure Lemma_Derive_Identity (K : Key256; E : Epoch) is
   begin
      pragma Assert (Iter (K, 0) = K);
   end Lemma_Derive_Identity;

   procedure Lemma_Derive_Step (K : Key256; E : Epoch) is
   begin
      pragma Assert (Iter (K, 1) = Step (Iter (K, 0)));
   end Lemma_Derive_Step;

   procedure Lemma_Derive_Compose (K : Key256; A, B, C : Epoch) is
   begin
      Lemma_Iter_Add (K, Natural (A) - Natural (B), Natural (B) - Natural (C));
   end Lemma_Derive_Compose;

   procedure Lemma_Derive_Shift (K : Key256; A, B, A2, B2 : Epoch) is
   begin
      null;
   end Lemma_Derive_Shift;

   ---------------------------------------------------------------------------
   --  Boxes and links
   ---------------------------------------------------------------------------

   --  The AD: ns[16] ‖ u16 (epoch), big-endian.
   function Box_AD (Ns : Id128; E : Epoch) return Byte_Array is
     (Kome.Keys.To_Bytes (Ns)
      & Byte (Natural (E) / 256) & Byte (Natural (E) mod 256))
     with Global => null,
          Post => Box_AD'Result'Length = AD_Len;

   --  The layout of Wrap_Byte, written into Buf field by field.
   procedure Fill_Wrap
     (Shared  : C.Shared_Secret;
      Box_PK  : Pubkey;
      DH_PK   : Pubkey;
      Sign_PK : Pubkey;
      Ns      : Id128;
      E       : Epoch;
      Buf     : out Wrap_Input_Bytes)
     with Global => null,
          Post   => (for all J in 0 .. Wrap_Input_Len - 1 =>
                       Buf (J) = Wrap_Byte (Shared, Box_PK, DH_PK, Sign_PK, Ns, E, J))
   is
      NB : constant Kome.Keys.Id_Bytes := Kome.Keys.To_Bytes (Ns);
   begin
      Buf := [others => 0];
      Buf (0 .. Wrap_O_Shared - 1)           := Wrap_Label;
      Buf (Wrap_O_Shared .. Wrap_O_Box - 1)  := Shared;
      Buf (Wrap_O_Box .. Wrap_O_DH - 1)      := Box_PK;
      Buf (Wrap_O_DH .. Wrap_O_Sign - 1)     := DH_PK;
      Buf (Wrap_O_Sign .. Wrap_O_Ns - 1)     := Sign_PK;
      Buf (Wrap_O_Ns .. Wrap_O_E - 1)        := NB;
      Buf (Wrap_O_E)                         := Byte (Natural (E) / 256);
      Buf (Wrap_O_E + 1)                     := Byte (Natural (E) mod 256);
      pragma Assert (for all J in 0 .. Wrap_O_Shared - 1 => Buf (J) = Wrap_Label (J));
      pragma Assert (for all J in Wrap_O_Shared .. Wrap_O_Box - 1 =>
                       Buf (J) = Shared (J - Wrap_O_Shared));
      pragma Assert (for all J in Wrap_O_Box .. Wrap_O_DH - 1 =>
                       Buf (J) = Box_PK (J - Wrap_O_Box));
      pragma Assert (for all J in Wrap_O_DH .. Wrap_O_Sign - 1 =>
                       Buf (J) = DH_PK (J - Wrap_O_DH));
      pragma Assert (for all J in Wrap_O_Sign .. Wrap_O_Ns - 1 =>
                       Buf (J) = Sign_PK (J - Wrap_O_Sign));
      pragma Assert (for all J in Wrap_O_Ns .. Wrap_O_E - 1 =>
                       Buf (J) = Kome.Keys.Byte_At (Ns, J - Wrap_O_Ns));
   end Fill_Wrap;

   function Wrap_Input
     (Shared  : Kome.Crypto.Shared_Secret;
      Box_PK  : Pubkey;
      DH_PK   : Pubkey;
      Sign_PK : Pubkey;
      Ns      : Id128;
      E       : Epoch) return Wrap_Input_Bytes
   is
      Buf : Wrap_Input_Bytes;
   begin
      Fill_Wrap (Shared, Box_PK, DH_PK, Sign_PK, Ns, E, Buf);
      return Buf;
   end Wrap_Input;

   --  wrap_key = BLAKE2b-256 ("kome/wrap" ‖ shared ‖ box_pk ‖ dh_pk ‖ sign_pk
   --  ‖ ns ‖ u16 (e)), into Key (a secret: the caller wipes it). The input
   --  holds the shared secret. This procedure wipes it. Buf has the bytes of
   --  the ghost model Wrap_Input, so it has the same digest (the congruence
   --  axiom of Kome.Crypto).
   procedure Wrap_Key
     (Shared  : C.Shared_Secret;
      Box_PK  : Pubkey;
      DH_PK   : Pubkey;
      Sign_PK : Pubkey;
      Ns      : Id128;
      E       : Epoch;
      Key     : out Hash256)
     with Global => null,
          Post   => Kome.Keys.To_Key256 (Key) = Wrap_Key_Of (Shared, Box_PK, DH_PK, Sign_PK, Ns, E)
   is
      Buf : Wrap_Input_Bytes;
   begin
      Fill_Wrap (Shared, Box_PK, DH_PK, Sign_PK, Ns, E, Buf);
      C.Lemma_Blake2b_Congruent (Buf, Wrap_Input (Shared, Box_PK, DH_PK, Sign_PK, Ns, E));
      C.Blake2b_256 (Buf, Key);
      C.Wipe (Buf);
   end Wrap_Key;

   --  The wrap key depends only on the bytes of the shared secret. Box_Key
   --  and Unbox_Key hold the secret that X25519 wrote. That secret is equal
   --  (Ada "=", not the same term) to the ghost X25519_Shared that their
   --  Posts name.
   procedure Lemma_Wrap_Shared
     (S1, S2  : C.Shared_Secret;
      Box_PK  : Pubkey;
      DH_PK   : Pubkey;
      Sign_PK : Pubkey;
      Ns      : Id128;
      E       : Epoch)
     with Ghost, Global => null,
          Pre  => S1 = S2,
          Post => Wrap_Key_Of (S1, Box_PK, DH_PK, Sign_PK, Ns, E)
                  = Wrap_Key_Of (S2, Box_PK, DH_PK, Sign_PK, Ns, E)
   is
   begin
      pragma Assert
        (for all K in 0 .. Wrap_Input_Len - 1 =>
           Wrap_Byte (S1, Box_PK, DH_PK, Sign_PK, Ns, E, K)
           = Wrap_Byte (S2, Box_PK, DH_PK, Sign_PK, Ns, E, K));
      C.Lemma_Blake2b_Congruent (Wrap_Input (S1, Box_PK, DH_PK, Sign_PK, Ns, E),
                                 Wrap_Input (S2, Box_PK, DH_PK, Sign_PK, Ns, E));
   end Lemma_Wrap_Shared;

   --  The synthetic nonce of K under the key with the bytes Key_Bytes,
   --  computed through wiped buffers. Post: it is Synthetic_Nonce.
   procedure Nonce_Of (Key_Bytes : Hash256; K : Key256; N : out Nonce)
     with Global => null,
          Post   => N = Synthetic_Nonce (Kome.Keys.To_Key256 (Key_Bytes), K)
   is
      Buf    : Nonce_Input_Bytes := Nonce_Input (Kome.Keys.To_Key256 (Key_Bytes), K);
      Digest : Hash256;
   begin
      C.Blake2b_256 (Buf, Digest);
      N := Digest (0 .. Nonce_Len - 1);
      C.Wipe (Buf);
      C.Wipe (Digest);
   end Nonce_Of;

   --  The bytes of the link key, through a wiped input buffer. Post: as a
   --  key, it is Link_Key.
   procedure Link_Key_Of (K_S : Key256; Ns : Id128; S : Epoch; Key : out Hash256)
     with Global => null,
          Post   => Kome.Keys.To_Key256 (Key) = Link_Key (K_S, Ns, S)
   is
      Buf : Link_Input_Bytes := Link_Input (K_S, Ns, S);
   begin
      C.Blake2b_256 (Buf, Key);
      C.Wipe (Buf);
   end Link_Key_Of;

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
   is
      Shared       : C.Shared_Secret;
      Contributory : Boolean;
      WK           : Hash256;
      Plain        : C.AEAD_Key;
      Cipher       : C.AEAD_Key;
      Mac          : C.Tag;
   begin
      --  Refuse an encoding that is not reduced before an exchange. It would
      --  seal a box that its member's reduced key can never open (see
      --  the spec header).
      if not Is_Reduced_U (Member_DH_PK) then
         N := [others => 0];
         Sealed := [others => 0];
         Status := Non_Canonical_Peer;
         return;
      end if;
      if C.Is_Low_Order_U (Member_DH_PK) then
         N := [others => 0];
         Sealed := [others => 0];
         Status := Low_Order_Peer;
         return;
      end if;

      C.X25519 (Eph_Secret, Member_DH_PK, Shared, Contributory);
      if not Contributory then
         N := [others => 0];
         Sealed := [others => 0];
         Status := Low_Order_Peer;
         return;   --  Shared is all zeros already (Kome.Crypto.X25519 Post)
      end if;

      Wrap_Key (Shared, C.X25519_Public (Eph_Secret), Member_DH_PK,
                Member_Sign_PK, Ns, E, WK);
      Lemma_Wrap_Shared (Shared, C.X25519_Shared (Eph_Secret, Member_DH_PK),
                         C.X25519_Public (Eph_Secret), Member_DH_PK,
                         Member_Sign_PK, Ns, E);
      Nonce_Of (WK, Epoch_Key, N);
      Plain := Kome.Keys.To_Bytes (Epoch_Key);
      C.Lock (WK, N, Box_AD (Ns, E), Plain, Cipher, Mac);
      Sealed := Cipher & Mac;
      Status := Box_OK;

      C.Wipe (Shared);
      C.Wipe (WK);
      C.Wipe (Plain);
   end Box_Key;

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
   is
      Shared       : C.Shared_Secret;
      Contributory : Boolean;
      WK           : Hash256;
      Plain        : C.AEAD_Key;
      Authentic    : Boolean;
      Expected     : Nonce;
   begin
      if not Is_Reduced_U (Box_PK) then
         Epoch_Key := Zero_Key;
         Status := Non_Canonical_Peer;
         return;
      end if;
      if C.Is_Low_Order_U (Box_PK) then
         Epoch_Key := Zero_Key;
         Status := Low_Order_Peer;
         return;
      end if;

      C.X25519 (Member_Secret, Box_PK, Shared, Contributory);
      if not Contributory then
         Epoch_Key := Zero_Key;
         Status := Low_Order_Peer;
         return;   --  Shared is all zeros already (Kome.Crypto.X25519 Post)
      end if;

      Wrap_Key (Shared, Box_PK, C.X25519_Public (Member_Secret),
                Member_Sign_PK, Ns, E, WK);
      Lemma_Wrap_Shared (Shared, C.X25519_Shared (Member_Secret, Box_PK),
                         Box_PK, C.X25519_Public (Member_Secret),
                         Member_Sign_PK, Ns, E);
      C.Unlock (WK, N, Box_AD (Ns, E), Cipher_Of (Sealed), Tag_Of (Sealed),
                Plain, Authentic);
      Epoch_Key := Zero_Key;
      Status := Not_Authentic;
      if Authentic then
         --  Compute the synthetic nonce again from the opened key. Refuse a
         --  mismatch: exactly one box opens for each (wrap_key, k_e) (§6).
         Nonce_Of (WK, Kome.Keys.To_Key256 (Plain), Expected);
         if Expected = N then
            Epoch_Key := Kome.Keys.To_Key256 (Plain);
            Status := Box_OK;
         end if;
      end if;

      C.Wipe (Shared);
      C.Wipe (WK);
      C.Wipe (Plain);
   end Unbox_Key;

   procedure Seal_Link
     (K_S    : Key256;
      Ns     : Id128;
      S      : Epoch;
      K_Prev : Key256;
      N      : out Nonce;
      Sealed : out Kome.Box)
   is
      LK     : Hash256;
      Plain  : C.AEAD_Key;
      Cipher : C.AEAD_Key;
      Mac    : C.Tag;
   begin
      Link_Key_Of (K_S, Ns, S, LK);
      Nonce_Of (LK, K_Prev, N);
      Plain := Kome.Keys.To_Bytes (K_Prev);
      C.Lock (LK, N, Box_AD (Ns, S), Plain, Cipher, Mac);
      Sealed := Cipher & Mac;

      C.Wipe (LK);
      C.Wipe (Plain);
   end Seal_Link;

   procedure Open_Link
     (K_S    : Key256;
      Ns     : Id128;
      S      : Epoch;
      N      : Nonce;
      Sealed : Kome.Box;
      K_Prev : out Key256;
      Status : out Box_Status)
   is
      LK        : Hash256;
      Plain     : C.AEAD_Key;
      Authentic : Boolean;
      Expected  : Nonce;
   begin
      Link_Key_Of (K_S, Ns, S, LK);
      C.Unlock (LK, N, Box_AD (Ns, S), Cipher_Of (Sealed), Tag_Of (Sealed),
                Plain, Authentic);
      K_Prev := Zero_Key;
      Status := Not_Authentic;
      if Authentic then
         Nonce_Of (LK, Kome.Keys.To_Key256 (Plain), Expected);
         if Expected = N then
            K_Prev := Kome.Keys.To_Key256 (Plain);
            Status := Box_OK;
         end if;
      end if;

      C.Wipe (LK);
      C.Wipe (Plain);
   end Open_Link;

   pragma Warnings (GNATprove, On, "*is set by ""Wipe"" but not used*");
   pragma Warnings (GNATprove, On, "statement has no effect");

end Kome.Epochs;
