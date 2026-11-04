--  Test main for Kome.Epochs (DESIGN.md §6).
--  (a) Known answers from vectors/epochs.txt:
--      - the chain (Python hashlib, with the full 2**16 - 1 step walk);
--      - the box and link constructions (an independent Python reference
--        over libsodium, pyca/cryptography and hashlib; no monocypher).
--      The test checks each answer through Box_Key, Unbox_Key, Seal_Link,
--      Open_Link, Synthetic_Nonce and Link_Key. It computes the wrap key
--      again here from Kome.Crypto primitives and literal labels.
--  (b) The chain algebra: the ghost lemmas run under -gnata on real keys.
--  (c) Boxes:
--      - round trip;
--      - the member derives older keys;
--      - the nonce is synthetic and open checks it (a box that passes the
--        AEAD under a nonce that is not synthetic is refused);
--      - each refusal gives zeros (wrong member secret, sign_pk, box_pk,
--        nonce, epoch, collection, tampered bytes, low-order and
--        non-reduced peers).
--  (d) Regressions:
--      - the k5-to-k6 keystream reuse. The test shows it on a construction
--        with a caller nonce and no ns or epoch in the wrap key. The test
--        shows that it does not occur with the current construction;
--      - a reused ephemeral secret.
--  (e) Links: a walk back across a segment boundary, refusals.
pragma Ada_2022;
with Ada.Text_IO;      use Ada.Text_IO;
with Ada.Command_Line; use Ada.Command_Line;
with Ada.Directories;
with Kome;             use Kome;
with Kome.Keys;
with Kome.Crypto;
with Kome.Epochs;      use Kome.Epochs;

procedure Test_Epochs with SPARK_Mode => Off is

   Failed : Boolean := False;

   procedure Check (Name : String; Ok : Boolean) is
   begin
      Put_Line ((if Ok then "PASS " else "FAIL ") & Name);
      if not Ok then
         Failed := True;
      end if;
   end Check;

   function Nibble (C : Character) return Byte is
     (case C is
         when '0' .. '9' => Character'Pos (C) - Character'Pos ('0'),
         when 'a' .. 'f' => Character'Pos (C) - Character'Pos ('a') + 10,
         when 'A' .. 'F' => Character'Pos (C) - Character'Pos ('A') + 10,
         when others     => raise Constraint_Error with "bad hex");

   function From_Hex (S : String) return Byte_Array is
   begin
      if S'Length mod 2 /= 0 then
         raise Constraint_Error with "odd hex";
      end if;
      return R : Byte_Array (0 .. S'Length / 2 - 1) do
         for I in R'Range loop
            R (I) := Nibble (S (S'First + 2 * I)) * 16
                     + Nibble (S (S'First + 2 * I + 1));
         end loop;
      end return;
   end From_Hex;

   function Pattern (N : Natural; Mul, Add : Natural) return Byte_Array is
      R : Byte_Array (0 .. N - 1);
   begin
      for I in R'Range loop
         R (I) := Byte ((I * Mul + Add) mod 256);
      end loop;
      return R;
   end Pattern;

   function Key_Of (S : String) return Key256 is
     (Kome.Keys.To_Key256 (From_Hex (S)));

   function Find (Rel : String) return String is
   begin
      if Ada.Directories.Exists (Rel) then
         return Rel;
      elsif Ada.Directories.Exists ("../" & Rel) then
         return "../" & Rel;
      elsif Ada.Directories.Exists ("../../" & Rel) then
         return "../../" & Rel;
      else
         return Rel;
      end if;
   end Find;

   ---------------------------------------------------------------------------
   --  Independent computations from Kome.Crypto primitives and literal
   --  labels (not the package's constants). The tests use them to
   --  check the intermediate values of the vectors and to forge boxes for
   --  the refusal tests.
   ---------------------------------------------------------------------------

   function Ascii (S : String) return Byte_Array is
   begin
      return R : Byte_Array (0 .. S'Length - 1) do
         for I in R'Range loop
            R (I) := Character'Pos (S (S'First + I));
         end loop;
      end return;
   end Ascii;

   function U16 (E : Epoch) return Byte_Array is
     ([Byte (Natural (E) / 256), Byte (Natural (E) mod 256)]);

   --  BLAKE2b-256 ("kome/wrap" ‖ X25519 (Secret, Peer) ‖ box_pk ‖ dh_pk ‖
   --  sign_pk ‖ ns ‖ u16 (e)).
   function Wrap_Ref
     (Secret : Kome.Crypto.DH_Secret; Peer, Box_PK, DH_PK, Sign_PK : Pubkey;
      Ns : Id128; E : Epoch) return Hash256
   is
      Shared : Kome.Crypto.Shared_Secret;
      Contr  : Boolean;
   begin
      Kome.Crypto.X25519 (Secret, Peer, Shared, Contr);
      return Kome.Crypto.Blake2b_256
        (Ascii ("kome/wrap") & Shared & Box_PK & DH_PK & Sign_PK
         & Kome.Keys.To_Bytes (Ns) & U16 (E));
   end Wrap_Ref;

   function Nonce_Ref (Key : Byte_Array; K : Key256) return Nonce is
     (Kome.Crypto.Blake2b_256
        (Ascii ("kome/nonce") & Key & Kome.Keys.To_Bytes (K)) (0 .. Nonce_Len - 1));

   --  An AEAD box of K under Key, nonce N and AD ns ‖ u16 (e). Box_Key or
   --  Seal_Link makes this box if N is the synthetic nonce.
   function Lock_Ref
     (Key : Byte_Array; N : Nonce; Ns : Id128; E : Epoch; K : Key256)
      return Kome.Box
   is
      Cipher : Kome.Crypto.AEAD_Key;
      Mac    : Kome.Crypto.Tag;
   begin
      Kome.Crypto.Lock (Key, N, Kome.Keys.To_Bytes (Ns) & U16 (E),
                        Kome.Keys.To_Bytes (K), Cipher, Mac);
      return Cipher & Mac;
   end Lock_Ref;

   ---------------------------------------------------------------------------
   --  (a) Known answers: chain (hashlib), box and link (Python reference)
   ---------------------------------------------------------------------------

   procedure Vectors is
      Path : constant String := Find ("vectors/epochs.txt");
      F    : File_Type;
      Line : String (1 .. 1024);
      Last : Natural;

      type Bounds is record
         First, Last : Natural;
      end record;
      Fields   : array (1 .. 12) of Bounds;
      N_Fields : Natural;
      N_Chain, N_Box, N_Link : Natural := 0;
      Ok, Ok_Box, Ok_Link : Boolean := True;
      Full     : Boolean := False;

      procedure Tokenize (S : String) is
         I : Natural := S'First;
      begin
         N_Fields := 0;
         while I <= S'Last and then N_Fields < Fields'Last loop
            while I <= S'Last and then S (I) = ' ' loop
               I := I + 1;
            end loop;
            exit when I > S'Last;
            N_Fields := N_Fields + 1;
            Fields (N_Fields).First := I;
            while I <= S'Last and then S (I) /= ' ' loop
               I := I + 1;
            end loop;
            Fields (N_Fields).Last := I - 1;
         end loop;
      end Tokenize;

      function Field (K : Positive) return String is
        (Line (Fields (K).First .. Fields (K).Last));

      procedure Bad (What : String) is
      begin
         Put_Line ("  mismatch: " & What & " (" & Field (1) & " line, field 6 = "
                   & Field (6) & ")");
      end Bad;
   begin
      if not Ada.Directories.Exists (Path) then
         Check ("vectors_present (" & Path & ")", False);
         return;
      end if;
      Open (F, In_File, Path);
      while not End_Of_File (F) loop
         Get_Line (F, Line, Last);
         if Last > 0 and then Line (1) /= '#' then
            Tokenize (Line (1 .. Last));
            if Field (1) = "chain" and then N_Fields = 5 then
               declare
                  K    : constant Key256 := Key_Of (Field (2));
                  From : constant Epoch := Epoch'Value (Field (3));
                  To   : constant Epoch := Epoch'Value (Field (4));
                  Want : constant Key256 := Key_Of (Field (5));
               begin
                  N_Chain := N_Chain + 1;
                  if Derive (K, From, To) /= Want then
                     Ok := False;
                     Put_Line ("  mismatch: chain " & Field (3) & " -> "
                               & Field (4));
                  end if;
                  if From = To + 1 and then Step (K) /= Want then
                     Ok := False;
                     Put_Line ("  mismatch: step " & Field (3));
                  end if;
                  if From = Epoch'Last and then To = 0 then
                     Full := True;
                  end if;
               end;
            elsif Field (1) = "box" and then N_Fields = 12 then
               declare
                  Eph     : constant Kome.Crypto.DH_Secret := From_Hex (Field (2));
                  DH_SK   : constant Kome.Crypto.DH_Secret := From_Hex (Field (3));
                  Sign_PK : constant Pubkey := From_Hex (Field (4));
                  Ns      : constant Id128 := Kome.Keys.To_Id128 (From_Hex (Field (5)));
                  E       : constant Epoch := Epoch'Value (Field (6));
                  K_E     : constant Key256 := Key_Of (Field (7));
                  Box_PK  : constant Pubkey := From_Hex (Field (8));
                  DH_PK   : constant Pubkey := From_Hex (Field (9));
                  Wrap    : constant Hash256 := From_Hex (Field (10));
                  Want_N  : constant Nonce := From_Hex (Field (11));
                  Want_B  : constant Kome.Box := From_Hex (Field (12));
                  N       : Nonce;
                  Sealed  : Kome.Box;
                  St      : Box_Status;
                  Got     : Key256;
               begin
                  N_Box := N_Box + 1;
                  if Kome.Crypto.X25519_Public (Eph) /= Box_PK
                    or else Kome.Crypto.X25519_Public (DH_SK) /= DH_PK
                  then
                     Ok_Box := False;
                     Bad ("box_pk/dh_pk");
                  end if;
                  if Wrap_Ref (Eph, DH_PK, Box_PK, DH_PK, Sign_PK, Ns, E) /= Wrap
                    or else Wrap_Ref (DH_SK, Box_PK, Box_PK, DH_PK, Sign_PK, Ns, E)
                              /= Wrap
                  then
                     Ok_Box := False;
                     Bad ("wrap_key");
                  end if;
                  if Synthetic_Nonce (Kome.Keys.To_Key256 (Wrap), K_E) /= Want_N
                    or else Nonce_Ref (Wrap, K_E) /= Want_N
                  then
                     Ok_Box := False;
                     Bad ("synthetic nonce");
                  end if;
                  Box_Key (Eph, DH_PK, Sign_PK, Ns, E, K_E, N, Sealed, St);
                  if St /= Box_OK or else N /= Want_N or else Sealed /= Want_B then
                     Ok_Box := False;
                     Bad ("Box_Key");
                  end if;
                  Unbox_Key (DH_SK, Sign_PK, Box_PK, Ns, E, Want_N, Want_B, Got, St);
                  if St /= Box_OK or else Got /= K_E then
                     Ok_Box := False;
                     Bad ("Unbox_Key");
                  end if;
               end;
            elsif Field (1) = "link" and then N_Fields = 8 then
               declare
                  K_S    : constant Key256 := Key_Of (Field (2));
                  Ns     : constant Id128 := Kome.Keys.To_Id128 (From_Hex (Field (3)));
                  S      : constant Epoch := Epoch'Value (Field (4));
                  K_Prev : constant Key256 := Key_Of (Field (5));
                  LK     : constant Key256 := Key_Of (Field (6));
                  Want_N : constant Nonce := From_Hex (Field (7));
                  Want_B : constant Kome.Box := From_Hex (Field (8));
                  N      : Nonce;
                  Sealed : Kome.Box;
                  St     : Box_Status;
                  Got    : Key256;
               begin
                  N_Link := N_Link + 1;
                  if Link_Key (K_S, Ns, S) /= LK
                    or else Kome.Crypto.Blake2b_256
                              (Ascii ("kome/link") & Kome.Keys.To_Bytes (K_S)
                               & Kome.Keys.To_Bytes (Ns) & U16 (S))
                            /= Kome.Keys.To_Bytes (LK)
                  then
                     Ok_Link := False;
                     Bad ("link_key");
                  end if;
                  if Synthetic_Nonce (LK, K_Prev) /= Want_N then
                     Ok_Link := False;
                     Bad ("link nonce");
                  end if;
                  Seal_Link (K_S, Ns, S, K_Prev, N, Sealed);
                  if N /= Want_N or else Sealed /= Want_B then
                     Ok_Link := False;
                     Bad ("Seal_Link");
                  end if;
                  Open_Link (K_S, Ns, S, Want_N, Want_B, Got, St);
                  if St /= Box_OK or else Got /= K_Prev then
                     Ok_Link := False;
                     Bad ("Open_Link");
                  end if;
               end;
            else
               Check ("vector_line_parses (" & Field (1) & ")", False);
            end if;
         end if;
      end loop;
      Close (F);
      Check ("chain_matches_hashlib (" & N_Chain'Image & " vectors)",
             Ok and then N_Chain >= 10);
      Check ("chain_full_walk_65535_to_0_present", Full);
      Check ("box_matches_python_reference (" & N_Box'Image & " vectors)",
             Ok_Box and then N_Box >= 6);
      Check ("link_matches_python_reference (" & N_Link'Image & " vectors)",
             Ok_Link and then N_Link >= 4);
   end Vectors;

   Top_Key : constant Key256 :=
     Key_Of ("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f");
   Other_Key : constant Key256 :=
     Key_Of ("ba7fa1f528a3ae574e52dbbc4c8fd147b24842609ea89437adca6c7541f9c24c");

   ---------------------------------------------------------------------------
   --  (b) Chain algebra on real keys
   ---------------------------------------------------------------------------

   procedure Algebra is
      Ok : Boolean := True;
   begin
      --  The lemmas run under -gnata: each Post is evaluated with real
      --  BLAKE2b. A false law raises Assertion_Error.
      Lemma_Derive_Identity (Top_Key, 0);
      Lemma_Derive_Identity (Top_Key, 777);
      Lemma_Derive_Identity (Other_Key, Epoch'Last);
      Check ("lemma_derive_identity (run)", True);

      Lemma_Derive_Step (Top_Key, 0);
      Lemma_Derive_Step (Other_Key, Epoch'Last - 1);
      Check ("lemma_derive_step (run)", True);

      Lemma_Derive_Compose (Top_Key, 9, 5, 2);
      Lemma_Derive_Compose (Top_Key, 9, 9, 2);
      Lemma_Derive_Compose (Top_Key, 9, 2, 2);
      Lemma_Derive_Compose (Other_Key, Epoch'Last, Epoch'Last - 3, Epoch'Last - 7);
      Check ("lemma_derive_compose (run)", True);

      Lemma_Derive_Shift (Top_Key, 10, 4, 60_006, 60_000);
      Check ("lemma_derive_shift (run)", True);

      Lemma_Iter_Add (Top_Key, 0, 0);
      Lemma_Iter_Add (Top_Key, 3, 4);
      Lemma_Iter_Add (Other_Key, 5, 0);
      Check ("lemma_iter_add (run)", True);

      --  The same laws, checked directly over longer walks. For these
      --  walks, the ghost model is too slow to run.
      Ok := Derive (Derive (Other_Key, Epoch'Last, 30_000), 30_000, 0)
              = Derive (Other_Key, Epoch'Last, 0)
            and then Derive (Derive (Top_Key, 5_000, 4_999), 4_999, 0)
              = Derive (Top_Key, 5_000, 0)
            and then Derive (Top_Key, 4_000, 4_000) = Top_Key
            and then Derive (Top_Key, 1, 0) = Step (Top_Key)
            and then Derive (Top_Key, 3, 0) = Step (Step (Step (Top_Key)))
            and then Derive (Top_Key, 1_003, 1_000)
                       = Derive (Top_Key, 3, 0);
      Check ("chain_composes_over_long_walks", Ok);

      Check ("chain_step_changes_key",
             Step (Top_Key) /= Top_Key
             and then Step (Top_Key) /= Step (Other_Key));
   end Algebra;

   ---------------------------------------------------------------------------
   --  (c) Boxes
   ---------------------------------------------------------------------------

   function Flip (B : Byte_Array; I : Natural) return Byte_Array is
      R : Byte_Array := B;
   begin
      R (I) := R (I) xor 16#01#;
      return R;
   end Flip;

   procedure Boxes is
      use Kome.Crypto;
      Eph_SK     : constant DH_Secret := Pattern (DH_Key_Len, 7, 3);
      Eph2_SK    : constant DH_Secret := Pattern (DH_Key_Len, 11, 77);
      Member_SK  : constant DH_Secret := Pattern (DH_Key_Len, 13, 101);
      Other_SK   : constant DH_Secret := Pattern (DH_Key_Len, 31, 9);
      Member_Sig : constant Pubkey := Pattern (Pubkey_Len, 17, 5);
      Other_Sig  : constant Pubkey := Pattern (Pubkey_Len, 3, 200);
      Box_PK     : constant Pubkey := X25519_Public (Eph_SK);
      Box2_PK    : constant Pubkey := X25519_Public (Eph2_SK);
      Member_PK  : constant Pubkey := X25519_Public (Member_SK);
      Other_PK   : constant Pubkey := X25519_Public (Other_SK);
      NS1        : constant Id128 := (16#6B6F6D65#, 1, 2, 3);
      NS2        : constant Id128 := (16#6B6F6D65#, 1, 2, 4);

      Top   : constant Epoch := 50_000;
      E     : constant Epoch := 1_234;
      K_Top : constant Key256 := Other_Key;
      K_E   : constant Key256 := Derive (K_Top, Top, E);

      N, N2         : Nonce;
      Sealed, Sealed2, Bad : Kome.Box;
      St, St2       : Box_Status;
      Got           : Key256;
   begin
      Box_Key (Eph_SK, Member_PK, Member_Sig, NS1, E, K_E, N, Sealed, St);
      Check ("box_ok", St = Box_OK and then not Is_Zero_Box (Sealed)
                       and then not Is_Zero_Nonce (N));
      Check ("box_layout_cipher_tag",
             Cipher_Of (Sealed) = Sealed (0 .. 31)
             and then Tag_Of (Sealed) = Sealed (32 .. 47)
             and then Cipher_Of (Sealed) & Tag_Of (Sealed) = Sealed);
      Check ("box_hides_key",
             Cipher_Of (Sealed) /= Kome.Keys.To_Bytes (K_E));

      --  The nonce is the synthetic nonce, computed again independently.
      --  The box is the AEAD under it (the construction of DESIGN.md §6).
      declare
         WK : constant Hash256 :=
           Wrap_Ref (Eph_SK, Member_PK, Box_PK, Member_PK, Member_Sig, NS1, E);
      begin
         Check ("box_nonce_is_synthetic",
                N = Nonce_Ref (WK, K_E)
                and then N = Synthetic_Nonce (Kome.Keys.To_Key256 (WK), K_E));
         --  The Posts of Box_Key and Unbox_Key name a ghost model
         --  (Wrap_Key_Of over X25519_Shared). It is equal to the independent
         --  reference's wrap key, from each side of the exchange. It
         --  is ghost, so the test uses an assertion.
         pragma Assert
           (Kome.Keys.To_Key256 (WK)
            = Wrap_Key_Of (Kome.Crypto.X25519_Shared (Eph_SK, Member_PK),
                           Box_PK, Member_PK, Member_Sig, NS1, E));
         pragma Assert
           (Kome.Keys.To_Key256 (WK)
            = Wrap_Key_Of (Kome.Crypto.X25519_Shared (Member_SK, Box_PK),
                           Box_PK, Member_PK, Member_Sig, NS1, E));
         pragma Assert
           (N = Synthetic_Nonce
                  (Wrap_Key_Of (Kome.Crypto.X25519_Shared (Eph_SK, Member_PK),
                                Box_PK, Member_PK, Member_Sig, NS1, E), K_E));
         Check ("wrap_key_model_is_reference_wrap_key", St = Box_OK);
         Check ("box_is_aead_under_wrap_key",
                Sealed = Lock_Ref (WK, N, NS1, E, K_E));
         Check ("wrap_key_agrees_both_sides",
                WK = Wrap_Ref (Member_SK, Box_PK, Box_PK, Member_PK, Member_Sig,
                               NS1, E));

         --  This box passes the AEAD under the correct wrap key, but its
         --  nonce is not the synthetic nonce. The member's nonce check
         --  refuses it (D6). Without the check, the box opens.
         declare
            Forged_N : constant Nonce := Pattern (Nonce_Len, 5, 1);
            Forged   : constant Kome.Box := Lock_Ref (WK, Forged_N, NS1, E, K_E);
         begin
            Unbox_Key (Member_SK, Member_Sig, Box_PK, NS1, E, Forged_N, Forged,
                       Got, St);
            Check ("unbox_non_synthetic_nonce_refused",
                   Forged_N /= N and then St = Not_Authentic
                   and then Got = Zero_Key);
         end;
      end;

      Unbox_Key (Member_SK, Member_Sig, Box_PK, NS1, E, N, Sealed, Got, St);
      Check ("unbox_round_trip", St = Box_OK and then Got = K_E);

      --  The member derives each older key from its one box (§6).
      Check ("member_derives_history",
             Derive (Got, E, 0) = Derive (K_Top, Top, 0)
             and then Derive (Got, E, 17) = Derive (K_Top, Top, 17));

      --  Deterministic (no RNG in SPARK code). A fresh ephemeral secret
      --  gives a fresh box_pk, nonce and box.
      Box_Key (Eph_SK, Member_PK, Member_Sig, NS1, E, K_E, N2, Sealed2, St2);
      Check ("box_deterministic",
             St2 = Box_OK and then N2 = N and then Sealed2 = Sealed);
      Box_Key (Eph2_SK, Member_PK, Member_Sig, NS1, E, K_E, N2, Sealed2, St2);
      Check ("box_fresh_eph_differs",
             St2 = Box_OK and then Box2_PK /= Box_PK
             and then N2 /= N and then Sealed2 /= Sealed);
      Unbox_Key (Member_SK, Member_Sig, Box2_PK, NS1, E, N2, Sealed2, Got, St);
      Check ("unbox_round_trip_fresh_eph", St = Box_OK and then Got = K_E);
      Unbox_Key (Member_SK, Member_Sig, Box_PK, NS1, E, N2, Sealed2, Got, St);
      Check ("unbox_wrong_box_pk_fails",
             St = Not_Authentic and then Got = Zero_Key);

      --  A box to a different member is different. It opens only for
      --  that member.
      Box_Key (Eph_SK, Other_PK, Other_Sig, NS1, E, K_E, N2, Sealed2, St2);
      Check ("box_per_member",
             St2 = Box_OK and then Sealed2 /= Sealed and then N2 /= N);
      Unbox_Key (Other_SK, Other_Sig, Box_PK, NS1, E, N2, Sealed2, Got, St);
      Check ("unbox_other_member", St = Box_OK and then Got = K_E);

      --  The wrap key binds sign_pk: the same dh_pk with a different
      --  sign_pk gets a different box.
      Box_Key (Eph_SK, Member_PK, Other_Sig, NS1, E, K_E, N2, Sealed2, St2);
      Check ("box_binds_sign_pk",
             St2 = Box_OK and then Sealed2 /= Sealed and then N2 /= N);

      --  Wrong inputs fail and give the zero key.
      Unbox_Key (Other_SK, Member_Sig, Box_PK, NS1, E, N, Sealed, Got, St);
      Check ("unbox_wrong_member_fails",
             St = Not_Authentic and then Got = Zero_Key);
      Unbox_Key (Member_SK, Other_Sig, Box_PK, NS1, E, N, Sealed, Got, St);
      Check ("unbox_wrong_sign_pk_fails",
             St = Not_Authentic and then Got = Zero_Key);
      Unbox_Key (Member_SK, Member_Sig, Other_PK, NS1, E, N, Sealed, Got, St);
      Check ("unbox_wrong_box_pk_other_key_fails",
             St = Not_Authentic and then Got = Zero_Key);
      Unbox_Key (Member_SK, Member_Sig, Box_PK, NS1, E, Flip (N, 7), Sealed,
                 Got, St);
      Check ("unbox_wrong_nonce_fails",
             St = Not_Authentic and then Got = Zero_Key);
      Unbox_Key (Member_SK, Member_Sig, Box_PK, NS1, E + 1, N, Sealed, Got, St);
      Check ("unbox_wrong_epoch_fails",
             St = Not_Authentic and then Got = Zero_Key);
      Unbox_Key (Member_SK, Member_Sig, Box_PK, NS2, E, N, Sealed, Got, St);
      Check ("unbox_wrong_ns_fails",
             St = Not_Authentic and then Got = Zero_Key);

      declare
         Ok : Boolean := True;
      begin
         for I in Sealed'Range loop
            Bad := Flip (Sealed, I);
            Unbox_Key (Member_SK, Member_Sig, Box_PK, NS1, E, N, Bad, Got, St);
            if St /= Not_Authentic or else Got /= Zero_Key then
               Ok := False;
            end if;
         end loop;
         Check ("unbox_tamper_every_byte_fails", Ok);
      end;

      --  Low-order peers, all with reduced encodings (so the refusal is
      --  for the low order, not for the encoding): u = 0, u = 1, the two
      --  points of order 8 and u = p - 1 (order 2).
      declare
         type Pk_List is array (Positive range <>) of Pubkey;
         Low : constant Pk_List :=
           [[others => 0],
            [0 => 1, others => 0],
            From_Hex ("e0eb7a7c3b41b8ae1656e3faf19fc46ada098deb9c32b1fd866205165f49b800"),
            From_Hex ("5f9c95bca3508c24b1d0b1559c83ef5b04445cc4581c8e86d8224eddd09f1157"),
            From_Hex ("ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f")];
         Ok_Box, Ok_Unbox, Ok_Red : Boolean := True;
      begin
         for U of Low loop
            Ok_Red := Ok_Red and then Kome.Epochs.Is_Reduced_U (U)
                      and then not Is_Good_DH_Key (U);
            Box_Key (Eph_SK, U, Member_Sig, NS1, E, K_E, N2, Bad, St);
            if St /= Low_Order_Peer or else not Is_Zero_Box (Bad)
              or else not Is_Zero_Nonce (N2)
            then
               Ok_Box := False;
            end if;
            Unbox_Key (Member_SK, Member_Sig, U, NS1, E, N, Sealed, Got, St);
            if St /= Low_Order_Peer or else Got /= Zero_Key then
               Ok_Unbox := False;
            end if;
         end loop;
         Check ("low_order_points_are_reduced_and_not_good", Ok_Red);
         Check ("box_low_order_refused (u=0, u=1, order 8 x2, p-1)", Ok_Box);
         Check ("unbox_low_order_box_pk_refused (u=0, u=1, order 8 x2, p-1)",
                Ok_Unbox);
      end;

      --  Non-reduced encodings. Member_PK with bit 255 set is the same
      --  point (X25519 ignores the bit) and gives the same shared secret.
      --  But the wrap key hashes the bytes, so a box sealed to it never
      --  opens for the member. It is refused. Each u >= p is also refused.
      declare
         Hi_Member : Pubkey := Member_PK;
         Hi_Box    : Pubkey := Box_PK;
         P_Enc     : constant Pubkey := From_Hex
           ("edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f");
         P2_Enc    : constant Pubkey := From_Hex
           ("efffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f");
         Max_Enc   : constant Pubkey := [others => 16#FF#];
         P1_Enc    : constant Pubkey := From_Hex
           ("ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f");
         Mid_Enc   : constant Pubkey := From_Hex
           ("fffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffff7f");
      begin
         Hi_Member (31) := Hi_Member (31) or 16#80#;
         Hi_Box (31) := Hi_Box (31) or 16#80#;
         Check ("is_reduced_u_boundaries",
                Kome.Epochs.Is_Reduced_U (Member_PK) and then Kome.Epochs.Is_Reduced_U (Box_PK)
                and then Kome.Epochs.Is_Reduced_U (P1_Enc) and then Kome.Epochs.Is_Reduced_U (Mid_Enc)
                and then not Kome.Epochs.Is_Reduced_U (P_Enc)
                and then not Kome.Epochs.Is_Reduced_U (P2_Enc)
                and then not Kome.Epochs.Is_Reduced_U (Max_Enc)
                and then not Kome.Epochs.Is_Reduced_U (Hi_Member));

         Box_Key (Eph_SK, Hi_Member, Member_Sig, NS1, E, K_E, N2, Bad, St);
         Check ("box_member_bit255_refused",
                St = Non_Canonical_Peer and then Is_Zero_Box (Bad)
                and then Is_Zero_Nonce (N2));
         Box_Key (Eph_SK, P2_Enc, Member_Sig, NS1, E, K_E, N2, Bad, St);
         Check ("box_member_u_ge_p_refused",
                St = Non_Canonical_Peer and then Is_Zero_Box (Bad)
                and then Is_Zero_Nonce (N2));
         Box_Key (Eph_SK, P_Enc, Member_Sig, NS1, E, K_E, N2, Bad, St);
         Check ("box_member_u_eq_p_refused_as_non_canonical",
                St = Non_Canonical_Peer and then Is_Zero_Box (Bad));
         Unbox_Key (Member_SK, Member_Sig, Hi_Box, NS1, E, N, Sealed, Got, St);
         Check ("unbox_box_pk_bit255_refused",
                St = Non_Canonical_Peer and then Got = Zero_Key);
         Unbox_Key (Member_SK, Member_Sig, P2_Enc, NS1, E, N, Sealed, Got, St);
         Check ("unbox_box_pk_u_ge_p_refused",
                St = Non_Canonical_Peer and then Got = Zero_Key);
         --  Box_Key accepts what Unbox_Key hashes: the member's public key
         --  and box_pk are reduced encodings.
         Check ("x25519_public_is_reduced",
                Kome.Epochs.Is_Reduced_U (X25519_Public (Member_SK))
                and then Kome.Epochs.Is_Reduced_U (X25519_Public (Other_SK))
                and then Kome.Epochs.Is_Reduced_U (X25519_Public (Eph_SK)));
      end;

      --  Edge epochs.
      Box_Key (Eph_SK, Member_PK, Member_Sig, NS1, Epoch'Last, K_Top, N2,
               Sealed2, St2);
      Unbox_Key (Member_SK, Member_Sig, Box_PK, NS1, Epoch'Last, N2, Sealed2,
                 Got, St);
      Check ("box_round_trip_top_epoch",
             St2 = Box_OK and then St = Box_OK and then Got = K_Top);
      Box_Key (Eph_SK, Member_PK, Member_Sig, NS1, 0, Zero_Key, N2, Sealed2, St2);
      Unbox_Key (Member_SK, Member_Sig, Box_PK, NS1, 0, N2, Sealed2, Got, St);
      Check ("box_round_trip_zero_key_epoch_0",
             St2 = Box_OK and then St = Box_OK and then Got = Zero_Key);
   end Boxes;

   ---------------------------------------------------------------------------
   --  (d) Regressions: keystream reuse across epochs, reused ephemeral
   --  secret
   ---------------------------------------------------------------------------

   function Xor_Bytes (A, B : Byte_Array) return Byte_Array is
      R : Byte_Array (0 .. A'Length - 1);
   begin
      for I in R'Range loop
         R (I) := A (A'First + I) xor B (B'First + I);
      end loop;
      return R;
   end Xor_Bytes;

   procedure Regressions is
      use Kome.Crypto;
      Eph_SK     : constant DH_Secret := Pattern (DH_Key_Len, 7, 3);
      Eph2_SK    : constant DH_Secret := Pattern (DH_Key_Len, 11, 77);
      Member_SK  : constant DH_Secret := Pattern (DH_Key_Len, 13, 101);
      Member_Sig : constant Pubkey := Pattern (Pubkey_Len, 17, 5);
      Member_PK  : constant Pubkey := X25519_Public (Member_SK);
      Box_PK     : constant Pubkey := X25519_Public (Eph_SK);
      NS1        : constant Id128 := (16#6B6F6D65#, 1, 2, 3);
      K6         : constant Key256 := Other_Key;
      K5         : constant Key256 := Derive (K6, 6, 5);
      N5, N6, N6b : Nonce;
      B5, B6, B6b : Kome.Box;
      St5, St6, St6b : Box_Status;
      Got        : Key256;
      St         : Box_Status;
   begin
      --  The attack, on a construction with a wrap key that does not bind
      --  ns or the epoch
      --  (wrap_key = BLAKE2b (X25519 (root_sk, dh_pk) ‖ root_pk ‖ dh_pk),
      --  one caller nonce reused for the member across epochs). A removed
      --  member that holds k5 XORs the two ciphertexts with k5 and gets k6.
      --  This shows that the test below finds the leak if it exists.
      declare
         Shared : Shared_Secret;
         Contr  : Boolean;
         Old_WK : Hash256;
         Reused : constant Nonce := Pattern (Nonce_Len, 5, 1);
         O5, O6 : Kome.Box;
      begin
         X25519 (Eph_SK, Member_PK, Shared, Contr);
         Old_WK := Blake2b_256 (Shared & Box_PK & Member_PK);
         O5 := Lock_Ref (Old_WK, Reused, NS1, 5, K5);
         O6 := Lock_Ref (Old_WK, Reused, NS1, 6, K6);
         Check ("old_construction_k5_recovers_k6 (reproduction)",
                Xor_Bytes (Xor_Bytes (Cipher_Of (O5), Cipher_Of (O6)),
                           Kome.Keys.To_Bytes (K5))
                  = Kome.Keys.To_Bytes (K6));
      end;

      --  The same two rosters under the current construction, also with a
      --  reused ephemeral secret (the worst case). The wrap keys and nonces
      --  are different, and the XOR with k5 is not k6.
      Box_Key (Eph_SK, Member_PK, Member_Sig, NS1, 5, K5, N5, B5, St5);
      Box_Key (Eph_SK, Member_PK, Member_Sig, NS1, 6, K6, N6, B6, St6);
      Box_Key (Eph2_SK, Member_PK, Member_Sig, NS1, 6, K6, N6b, B6b, St6b);
      Check ("k5_does_not_recover_k6_reused_eph",
             St5 = Box_OK and then St6 = Box_OK
             and then N5 /= N6
             and then Xor_Bytes (Xor_Bytes (Cipher_Of (B5), Cipher_Of (B6)),
                                 Kome.Keys.To_Bytes (K5))
                        /= Kome.Keys.To_Bytes (K6));
      Check ("k5_does_not_recover_k6_fresh_eph",
             St6b = Box_OK and then N5 /= N6b
             and then Xor_Bytes (Xor_Bytes (Cipher_Of (B5), Cipher_Of (B6b)),
                                 Kome.Keys.To_Bytes (K5))
                        /= Kome.Keys.To_Bytes (K6));
      --  The wrap keys of the two epochs are different (ns and epoch are
      --  hashed).
      Check ("wrap_key_covers_epoch",
             Wrap_Ref (Eph_SK, Member_PK, Box_PK, Member_PK, Member_Sig, NS1, 5)
             /= Wrap_Ref (Eph_SK, Member_PK, Box_PK, Member_PK, Member_Sig, NS1, 6));
      Check ("wrap_key_covers_ns",
             Wrap_Ref (Eph_SK, Member_PK, Box_PK, Member_PK, Member_Sig, NS1, 5)
             /= Wrap_Ref (Eph_SK, Member_PK, Box_PK, Member_PK, Member_Sig,
                          (16#6B6F6D65#, 1, 2, 4), 5));
      --  The epoch-5 box does not open as an epoch-6 box. The epoch-6 box
      --  does not open as an epoch-5 box.
      Unbox_Key (Member_SK, Member_Sig, Box_PK, NS1, 6, N5, B5, Got, St);
      Check ("box_epoch5_not_open_at_6", St = Not_Authentic and then Got = Zero_Key);
      Unbox_Key (Member_SK, Member_Sig, Box_PK, NS1, 6, N6, B6, Got, St);
      Check ("box_epoch6_opens", St = Box_OK and then Got = K6);

      --  A reused ephemeral secret (same box_pk) with the same epoch key
      --  gives identical boxes. (With the synthetic nonce, a repeated
      --  (key, nonce) means a repeated plaintext.) With a different epoch
      --  key, it gives different nonces.
      declare
         Na, Nb, Nc : Nonce;
         Ba, Bb, Bc : Kome.Box;
         Sa, Sb, Sc : Box_Status;
      begin
         Box_Key (Eph_SK, Member_PK, Member_Sig, NS1, 6, K6, Na, Ba, Sa);
         Box_Key (Eph_SK, Member_PK, Member_Sig, NS1, 6, K6, Nb, Bb, Sb);
         Box_Key (Eph_SK, Member_PK, Member_Sig, NS1, 6, Top_Key, Nc, Bc, Sc);
         Check ("reused_box_pk_same_key_identical_boxes",
                Sa = Box_OK and then Sb = Box_OK and then Na = Nb and then Ba = Bb);
         Check ("reused_box_pk_different_key_different_nonces",
                Sc = Box_OK and then Nc /= Na and then Bc /= Ba);
      end;
   end Regressions;

   ---------------------------------------------------------------------------
   --  (e) Links across segments (DESIGN.md §6 "Epoch segments", E3)
   ---------------------------------------------------------------------------

   procedure Links is
      NS1   : constant Id128 := (16#6B6F6D65#, 1, 2, 3);
      NS2   : constant Id128 := (16#6B6F6D65#, 1, 2, 4);
      --  Segment A: epochs 0 .. 9, top key Top_Key at 9. Segment B starts
      --  at s = 10 with an unrelated top Other_Key at 20.
      Top_A : constant Epoch := 9;
      S     : constant Epoch := 10;
      Top_B : constant Epoch := 20;
      K_S   : constant Key256 := Derive (Other_Key, Top_B, S);
      K_Last_A : constant Key256 := Derive (Top_Key, Top_A, S - 1);
      N     : Nonce;
      Sealed, Bad : Kome.Box;
      Got   : Key256;
      St    : Box_Status;
   begin
      Seal_Link (K_S, NS1, S, K_Last_A, N, Sealed);
      --  The Post (N = Synthetic_Nonce (Link_Key (...), K_Prev)) ran under
      --  -gnata. Check it again against the independent computation.
      Check ("link_nonce_is_synthetic",
             N = Synthetic_Nonce (Link_Key (K_S, NS1, S), K_Last_A)
             and then N = Nonce_Ref (Kome.Keys.To_Bytes (Link_Key (K_S, NS1, S)),
                                     K_Last_A));
      Check ("link_is_aead_under_link_key",
             Sealed = Lock_Ref (Kome.Keys.To_Bytes (Link_Key (K_S, NS1, S)), N,
                                NS1, S, K_Last_A));

      --  A member that holds only k_15 (segment B) reads all history. It
      --  walks down to k_s, opens the link and continues in segment A.
      declare
         K15 : constant Key256 := Derive (Other_Key, Top_B, 15);
      begin
         Open_Link (Derive (K15, 15, S), NS1, S, N, Sealed, Got, St);
         Check ("link_walk_back_across_segment",
                St = Box_OK and then Got = K_Last_A
                and then Derive (Got, S - 1, 0) = Derive (Top_Key, Top_A, 0));
      end;

      Open_Link (Derive (K_S, S, S - 1), NS1, S, N, Sealed, Got, St);
      Check ("open_link_wrong_k_s_fails",
             St = Not_Authentic and then Got = Zero_Key);
      Open_Link (K_S, NS2, S, N, Sealed, Got, St);
      Check ("open_link_wrong_ns_fails",
             St = Not_Authentic and then Got = Zero_Key);
      Open_Link (K_S, NS1, S + 1, N, Sealed, Got, St);
      Check ("open_link_wrong_s_fails",
             St = Not_Authentic and then Got = Zero_Key);
      Open_Link (K_S, NS1, S, Flip (N, 0), Sealed, Got, St);
      Check ("open_link_wrong_nonce_fails",
             St = Not_Authentic and then Got = Zero_Key);
      declare
         Ok : Boolean := True;
      begin
         for I in Sealed'Range loop
            Bad := Flip (Sealed, I);
            Open_Link (K_S, NS1, S, N, Bad, Got, St);
            if St /= Not_Authentic or else Got /= Zero_Key then
               Ok := False;
            end if;
         end loop;
         Check ("open_link_tamper_every_byte_fails", Ok);
      end;

      --  This link passes the AEAD under the correct link key, but its
      --  nonce is not synthetic. It is refused.
      declare
         Forged_N : constant Nonce := Pattern (Nonce_Len, 9, 4);
         Forged   : constant Kome.Box :=
           Lock_Ref (Kome.Keys.To_Bytes (Link_Key (K_S, NS1, S)), Forged_N,
                     NS1, S, K_Last_A);
      begin
         Open_Link (K_S, NS1, S, Forged_N, Forged, Got, St);
         Check ("open_link_non_synthetic_nonce_refused",
                Forged_N /= N and then St = Not_Authentic
                and then Got = Zero_Key);
      end;

      --  Edge: the last possible segment start.
      Seal_Link (Other_Key, NS1, Epoch'Last, Top_Key, N, Sealed);
      Open_Link (Other_Key, NS1, Epoch'Last, N, Sealed, Got, St);
      Check ("link_round_trip_s_65535", St = Box_OK and then Got = Top_Key);
      Seal_Link (Other_Key, NS1, 1, Zero_Key, N, Sealed);
      Open_Link (Other_Key, NS1, 1, N, Sealed, Got, St);
      Check ("link_round_trip_s_1_zero_key", St = Box_OK and then Got = Zero_Key);
      --  Deterministic. Each segment start has a different link key.
      declare
         N2 : Nonce;
         S2 : Kome.Box;
      begin
         Seal_Link (Other_Key, NS1, 1, Zero_Key, N2, S2);
         Check ("link_deterministic", N2 = N and then S2 = Sealed);
         Check ("link_key_covers_s_and_ns",
                Link_Key (K_S, NS1, S) /= Link_Key (K_S, NS1, S + 1)
                and then Link_Key (K_S, NS1, S) /= Link_Key (K_S, NS2, S));
      end;
   end Links;

   --  H6: fixed segment boundaries.
   procedure Segments is
   begin
      Check ("segments: 16 segments of 4096 epochs cover 0 .. 65535",
             Segments_Max = 16 and then Segment_Len = 4096
             and then Segment_Start (0) = 0 and then Segment_Top (0) = 4095
             and then Segment_Start (15) = 61_440 and then Segment_Top (15) = Epoch'Last);
      Check ("segments: the next segment starts at top + 1",
             (for all J in Segment_Index range 0 .. Segments_Max - 2 =>
                Segment_Top (J) + 1 = Segment_Start (J + 1)));
      Check ("segments: every epoch is in exactly its segment",
             Segment_Of (0) = 0 and then Segment_Of (4095) = 0 and then Segment_Of (4096) = 1
             and then Segment_Of (Epoch'Last) = 15
             and then (for all E in Epoch range 0 .. 9000 =>
                         Segment_Start (Segment_Of (E)) <= E
                         and then E <= Segment_Top (Segment_Of (E))));
      for E in Epoch range 0 .. 9000 loop
         Lemma_Segment_Bounds (E);
      end loop;
      Lemma_Segment_Bounds (Epoch'Last);
   end Segments;

begin
   Vectors;
   Algebra;
   Boxes;
   Regressions;
   Links;
   Segments;
   if Failed then
      Set_Exit_Status (Failure);
   end if;
end Test_Epochs;
