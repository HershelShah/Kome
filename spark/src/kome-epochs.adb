--  Kome.Epochs body. See the spec for what is proved and what is a crypto
--  oracle. In Box_Key and Unbox_Key every secret byte buffer is wiped before
--  the subprogram returns (Step cannot: see there);
--  gnatprove's flow analysis reports those final Wipes as having no effect
--  on the SPARK model, which is the point of them (Kome.Crypto.Wipe).
pragma Ada_2022;
with Kome.Keys;

package body Kome.Epochs with SPARK_Mode is

   package C renames Kome.Crypto;

   --  ASCII "prev".
   Prev_Label : constant Byte_Array (0 .. Prev_Label_Len - 1) :=
     [16#70#, 16#72#, 16#65#, 16#76#];

   ---------------------------------------------------------------------------
   --  Chain
   ---------------------------------------------------------------------------

   --  The function form of BLAKE2b-256, not the procedure form that writes
   --  into a buffer the caller then wipes: Step is a function (it has to
   --  be, to appear in Iter and in the contracts), SPARK functions must
   --  terminate, and Kome.Crypto's procedures (Blake2b_256 into a buffer,
   --  Wipe) carry no Always_Terminates aspect, so calling them here would
   --  leave the termination check open. The input buffer and the digest
   --  are therefore not wiped in Step (reported for Kome.Crypto).
   function Step (K : Key256) return Key256 is
   begin
      return Kome.Keys.To_Key256
        (C.Blake2b_256 (Kome.Keys.To_Bytes (K) & Prev_Label));
   end Step;

   function Derive (K : Key256; From, To : Epoch) return Key256 is
      --  The invariant restates the ghost model Iter, which costs I Steps
      --  to evaluate; executing it on every iteration would make the test
      --  quadratic (2**31 hashes for a full chain). It is proved, not run;
      --  the test checks Derive against an independent reference instead.
      pragma Assertion_Policy (Loop_Invariant => Ignore);
      N : constant Steps := Natural (From) - Natural (To);
      R : Key256 := K;
   begin
      --  At most Max_Steps = 2**16 - 1 iterations: the bound is the range
      --  of the index (subtype Steps).
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
      --  holds for I = 0 by definition, and one more Step on both sides
      --  keeps it.
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
   --  Boxes
   ---------------------------------------------------------------------------

   --  The AD: ns[16] ‖ epoch (2 bytes big-endian).
   function Box_AD (Ns : Id128; E : Epoch) return Byte_Array is
     (Kome.Keys.To_Bytes (Ns)
      & Byte (Natural (E) / 256) & Byte (Natural (E) mod 256))
     with Global => null,
          Post => Box_AD'Result'Length = AD_Len;

   --  wrap_key = BLAKE2b-256 (shared ‖ root_dh_pk ‖ member_dh_pk).
   procedure Wrap_Key
     (Shared        : C.Shared_Secret;
      Root_Public   : Pubkey;
      Member_Public : Pubkey;
      Key           : out C.AEAD_Key)
     with Global => null
   is
      Buf : Byte_Array (0 .. C.DH_Key_Len + 2 * Pubkey_Len - 1) :=
        [others => 0];
   begin
      Buf (0 .. C.DH_Key_Len - 1) := Shared;
      Buf (C.DH_Key_Len .. C.DH_Key_Len + Pubkey_Len - 1) := Root_Public;
      Buf (C.DH_Key_Len + Pubkey_Len .. Buf'Last) := Member_Public;
      C.Blake2b_256 (Buf, Key);
      pragma Warnings (GNATprove, Off, "statement has no effect",
                       Reason => "erasing secrets is not a SPARK effect");
      pragma Warnings (GNATprove, Off, "*is set by ""Wipe"" but not used*",
                       Reason => "erasing secrets is not a SPARK effect");
      C.Wipe (Buf);
      pragma Warnings (GNATprove, On, "*is set by ""Wipe"" but not used*");
      pragma Warnings (GNATprove, On, "statement has no effect");
   end Wrap_Key;

   procedure Box_Key
     (Root_Secret   : Kome.Crypto.DH_Secret;
      Member_Public : Pubkey;
      Ns            : Id128;
      E             : Epoch;
      Epoch_Key     : Key256;
      N             : Nonce;
      Sealed        : out Kome.Box;
      Status        : out Box_Status)
   is
      Shared       : C.Shared_Secret;
      Contributory : Boolean;
      WK           : C.AEAD_Key;
      Plain        : C.AEAD_Key;
      Cipher       : C.AEAD_Key;
      Mac          : C.Tag;
      Root_Public  : constant Pubkey := C.X25519_Public (Root_Secret);
   begin
      --  Refuse a non-reduced encoding before any exchange: it would seal a
      --  box its member's reduced key can never open (see the spec header).
      if not Is_Reduced_U (Member_Public) then
         Sealed := [others => 0];
         Status := Non_Canonical_Peer;
         return;
      end if;

      C.X25519 (Root_Secret, Member_Public, Shared, Contributory);
      if not Contributory then
         Sealed := [others => 0];
         Status := Low_Order_Peer;
         return;   --  Shared is all zeros already (Kome.Crypto.X25519 Post)
      end if;

      Wrap_Key (Shared, Root_Public, Member_Public, WK);
      Plain := Kome.Keys.To_Bytes (Epoch_Key);
      C.Lock (WK, N, Box_AD (Ns, E), Plain, Cipher, Mac);
      Sealed := Cipher & Mac;
      Status := Box_OK;

      pragma Warnings (GNATprove, Off, "statement has no effect",
                       Reason => "erasing secrets is not a SPARK effect");
      pragma Warnings (GNATprove, Off, "*is set by ""Wipe"" but not used*",
                       Reason => "erasing secrets is not a SPARK effect");
      C.Wipe (Shared);
      C.Wipe (WK);
      C.Wipe (Plain);
      pragma Warnings (GNATprove, On, "*is set by ""Wipe"" but not used*");
      pragma Warnings (GNATprove, On, "statement has no effect");
   end Box_Key;

   procedure Unbox_Key
     (Member_Secret : Kome.Crypto.DH_Secret;
      Root_Public   : Pubkey;
      Ns            : Id128;
      E             : Epoch;
      N             : Nonce;
      Sealed        : Kome.Box;
      Epoch_Key     : out Key256;
      Status        : out Box_Status)
   is
      Shared        : C.Shared_Secret;
      Contributory  : Boolean;
      WK            : C.AEAD_Key;
      Plain         : C.AEAD_Key;
      Authentic     : Boolean;
      Member_Public : constant Pubkey := C.X25519_Public (Member_Secret);
   begin
      if not Is_Reduced_U (Root_Public) then
         Epoch_Key := Zero_Key;
         Status := Non_Canonical_Peer;
         return;
      end if;

      C.X25519 (Member_Secret, Root_Public, Shared, Contributory);
      if not Contributory then
         Epoch_Key := Zero_Key;
         Status := Low_Order_Peer;
         return;   --  Shared is all zeros already (Kome.Crypto.X25519 Post)
      end if;

      Wrap_Key (Shared, Root_Public, Member_Public, WK);
      C.Unlock (WK, N, Box_AD (Ns, E), Cipher_Of (Sealed), Tag_Of (Sealed),
                Plain, Authentic);
      if Authentic then
         Epoch_Key := Kome.Keys.To_Key256 (Plain);
         Status := Box_OK;
      else
         Epoch_Key := Zero_Key;
         Status := Not_Authentic;
      end if;

      pragma Warnings (GNATprove, Off, "statement has no effect",
                       Reason => "erasing secrets is not a SPARK effect");
      pragma Warnings (GNATprove, Off, "*is set by ""Wipe"" but not used*",
                       Reason => "erasing secrets is not a SPARK effect");
      C.Wipe (Shared);
      C.Wipe (WK);
      C.Wipe (Plain);
      pragma Warnings (GNATprove, On, "*is set by ""Wipe"" but not used*");
      pragma Warnings (GNATprove, On, "statement has no effect");
   end Unbox_Key;

end Kome.Epochs;
