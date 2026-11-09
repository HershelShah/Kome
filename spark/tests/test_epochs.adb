--  Test main for Kome.Epochs (SIMPLIFY.md S4; DESIGN.md §6).
--  (a) Known answers from vectors/epochs.txt (an independent Python
--      reference over pyca/cryptography, hashlib and in-script RFC 7748 /
--      RFC 8439 references; no monocypher): k_g (the hedge), eph_sk,
--      box_pk, the wrap key, the box nonce, the box and the bundle key.
--      The test checks each answer through Key_For_Gen, Box_PK_Of,
--      Box_Key, Unbox_Key, Box_Nonce and Bundle_Key_Of, and computes eph_sk,
--      the wrap key and the nonce again here from Kome.Crypto primitives
--      and literal labels.
--  (b) k_g: the hedge of the issuer's seed (A6), fresh for every gen,
--      cid, rnd and issuer; a weak (all-zero) rnd still gives a key that
--      depends on the seed.
--  (c) Boxes:
--      - round trip;
--      - the nonce is synthetic and open checks it (a box that passes the
--        AEAD under a nonce that is not synthetic is refused, and so is a
--        box of the all-zero key);
--      - each refusal gives zeros (wrong member secret, sign_pk, box_pk,
--        nonce, gen, collection, tampered bytes, low-order and
--        non-reduced peers);
--      - the derived eph_sk (A6, G7): Box_PK_Of is X25519_Public of the
--        keyed derivation, every member box of a roster carries that
--        box_pk, and each derivation input changes it;
--      - the all-zero key is refused by Pre (A27).
--  (d) Regressions: a refresh (same members, next gen) has a fresh key, so
--      the old member cannot read the new key from the two boxes.
pragma Ada_2022;
with Ada.Text_IO;      use Ada.Text_IO;
with Ada.Command_Line; use Ada.Command_Line;
with Ada.Directories;
with Ada.Exceptions;
with Ada.Assertions;
with Ada.Strings.Fixed;
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

   --  Expect a refusal by a precondition of Kome.Epochs (under -gnata, a
   --  failed Pre raises Assertion_Error with the message "failed
   --  precondition from kome-epochs.ads:<line>").
   Pre_Tag : constant String := "failed precondition from kome-epochs.ads";

   generic
      with procedure Run;
   function Refused return Boolean;
   function Refused return Boolean is
   begin
      Run;
      return False;
   exception
      when E : Ada.Assertions.Assertion_Error =>
         declare
            Msg : constant String := Ada.Exceptions.Exception_Message (E);
         begin
            if Ada.Strings.Fixed.Index (Msg, Pre_Tag) = 0 then
               Put_Line ("  unexpected assertion: " & Msg);
               return False;
            end if;
            return True;
         end;
   end Refused;

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
   --  labels (not the package's constants). The tests use them to check
   --  the intermediate values of the vectors and to forge boxes for the
   --  refusal tests.
   ---------------------------------------------------------------------------

   function Ascii (S : String) return Byte_Array is
   begin
      return R : Byte_Array (0 .. S'Length - 1) do
         for I in R'Range loop
            R (I) := Character'Pos (S (S'First + I));
         end loop;
      end return;
   end Ascii;

   function U48_BE (G : U48) return Byte_Array is
     ([Byte (G / 2**40), Byte ((G / 2**32) mod 256), Byte ((G / 2**24) mod 256),
       Byte ((G / 2**16) mod 256), Byte ((G / 2**8) mod 256), Byte (G mod 256)]);

   --  f (k, m): keyed BLAKE2b-256.
   function F (K : Byte_Array; M : Byte_Array) return Hash256 is
     (Kome.Crypto.Blake2b_256_Keyed (K, M));

   --  eph_sk = f (k_g, "kome/eph" ‖ cid ‖ u48 (gen) ‖ signer).
   function Eph_Ref
     (K : Key256; Cid : Hash256; Gen : U48; Signer : Pubkey) return Kome.Crypto.DH_Secret
   is (F (Kome.Keys.To_Bytes (K), Ascii ("kome/eph") & Cid & U48_BE (Gen) & Signer));

   --  f (X25519 (Secret, Peer), "kome/wrap" ‖ box_pk ‖ dh_pk ‖ sign_pk ‖ cid
   --  ‖ u48 (gen)).
   function Wrap_Ref
     (Secret : Kome.Crypto.DH_Secret; Peer, Box_PK, DH_PK, Sign_PK : Pubkey;
      Cid : Hash256; Gen : U48) return Hash256
   is
      Shared : Kome.Crypto.Shared_Secret;
      Contr  : Boolean;
   begin
      Kome.Crypto.X25519 (Secret, Peer, Shared, Contr);
      return F (Shared, Ascii ("kome/wrap") & Box_PK & DH_PK & Sign_PK & Cid & U48_BE (Gen));
   end Wrap_Ref;

   --  f (k_g, "kome/box" ‖ dh_pk)[0:24].
   function Nonce_Ref (K : Key256; DH_PK : Pubkey) return Nonce is
     (F (Kome.Keys.To_Bytes (K), Ascii ("kome/box") & DH_PK) (0 .. Nonce_Len - 1));

   --  An AEAD box of K under Key, nonce N and AD cid ‖ u48 (gen). Box_Key
   --  makes this box if N is the synthetic nonce.
   function Lock_Ref
     (Key : Byte_Array; N : Nonce; Cid : Hash256; Gen : U48; K : Key256) return Kome.Box
   is
      Cipher : Kome.Crypto.AEAD_Key;
      Mac    : Kome.Crypto.Tag;
   begin
      Kome.Crypto.Lock (Key, N, Cid & U48_BE (Gen), Kome.Keys.To_Bytes (K), Cipher, Mac);
      return Cipher & Mac;
   end Lock_Ref;

   function Flip (B : Byte_Array; I : Natural) return Byte_Array is
      R : Byte_Array := B;
   begin
      R (I) := R (I) xor 16#01#;
      return R;
   end Flip;

   function Xor_Bytes (A, B : Byte_Array) return Byte_Array is
      R : Byte_Array (0 .. A'Length - 1);
   begin
      for I in R'Range loop
         R (I) := A (A'First + I) xor B (B'First + I);
      end loop;
      return R;
   end Xor_Bytes;

   ---------------------------------------------------------------------------
   --  Labels and layouts
   ---------------------------------------------------------------------------

   procedure Layouts is
      Cid : constant Hash256 := Pattern (Hash_Len, 13, 7);
      S   : constant Pubkey  := Pattern (Pubkey_Len, 7, 3);
      D   : constant Pubkey  := Pattern (Pubkey_Len, 3, 1);
   begin
      Check ("labels are the ASCII strings",
             Key_Label = Ascii ("kome/key") and then Eph_Label = Ascii ("kome/eph")
             and then Box_Label = Ascii ("kome/box") and then Wrap_Label = Ascii ("kome/wrap")
             and then Bundle_Label = Ascii ("kome/bundle"));
      Check ("gen_ctx = cid ‖ u48 (gen), big-endian",
             Gen_Ctx (Cid, 16#0102_0304_0506#) = Cid & Byte_Array'(1, 2, 3, 4, 5, 6)
             and then Gen_Ctx (Cid, U48'Last) = Cid & U48_BE (U48'Last)
             and then Gen_Ctx (Cid, 0)'Length = 38);
      Check ("eph input = ""kome/eph"" ‖ cid ‖ u48 (gen) ‖ signer (78 bytes)",
             Eph_Input (Cid, 9, S) = Ascii ("kome/eph") & Cid & U48_BE (9) & S
             and then Eph_Input (Cid, 9, S)'Length = 78);
      Check ("wrap input = ""kome/wrap"" ‖ box_pk ‖ dh_pk ‖ sign_pk ‖ cid ‖ u48 (gen)"
             & " (143 bytes)",
             Wrap_Input (S, D, S, Cid, 9)
               = Ascii ("kome/wrap") & S & D & S & Cid & U48_BE (9)
             and then Wrap_Input (S, D, S, Cid, 9)'Length = 143);
   end Layouts;

   ---------------------------------------------------------------------------
   --  (a) Known answers (Python reference)
   ---------------------------------------------------------------------------

   procedure Vectors is
      Path : constant String := Find ("vectors/epochs.txt");
      Fl   : File_Type;
      Line : String (1 .. 1024);
      Last : Natural;

      type Bounds is record
         First, Last : Natural;
      end record;
      Fields   : array (1 .. 14) of Bounds;
      N_Fields : Natural;
      N_Key, N_Box, N_Bundle : Natural := 0;
      Ok_Key, Ok_Box, Ok_Bundle : Boolean := True;

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
         Put_Line ("  mismatch: " & What & " (" & Field (1) & " line, field 2 = "
                   & Field (2) & ")");
      end Bad;
   begin
      if not Ada.Directories.Exists (Path) then
         Check ("vectors_present (" & Path & ")", False);
         return;
      end if;
      Open (Fl, In_File, Path);
      while not End_Of_File (Fl) loop
         Get_Line (Fl, Line, Last);
         if Last > 0 and then Line (1) /= '#' then
            Tokenize (Line (1 .. Last));
            if Field (1) = "key" and then N_Fields = 6 then
               declare
                  Seed : constant Kome.Crypto.Seed := From_Hex (Field (2));
                  Cid  : constant Hash256 := From_Hex (Field (3));
                  Gen  : constant U48 := U48'Value (Field (4));
                  Rnd  : constant Kome.Crypto.Random_Bytes := From_Hex (Field (5));
                  Want : constant Key256 := Key_Of (Field (6));
                  SK   : Kome.Crypto.Secret_Key;
                  PK   : Pubkey;
                  K    : Key256;
               begin
                  N_Key := N_Key + 1;
                  Kome.Crypto.Key_Pair (Seed, SK, PK);
                  Key_For_Gen (SK, Cid, Gen, Rnd, K);
                  pragma Assert (K = Gen_Key_Of (SK, Cid, Gen, Rnd));
                  if K /= Want
                    or else Kome.Keys.To_Bytes (Want)
                            /= F (Seed, Ascii ("kome/key") & Cid & U48_BE (Gen) & Rnd)
                  then
                     Ok_Key := False;
                     Bad ("Key_For_Gen");
                  end if;
                  Kome.Crypto.Wipe (SK);
               end;
            elsif Field (1) = "box" and then N_Fields = 13 then
               declare
                  K       : constant Key256 := Key_Of (Field (2));
                  Cid     : constant Hash256 := From_Hex (Field (3));
                  Gen     : constant U48 := U48'Value (Field (4));
                  Signer  : constant Pubkey := From_Hex (Field (5));
                  DH_SK   : constant Kome.Crypto.DH_Secret := From_Hex (Field (6));
                  Sign_PK : constant Pubkey := From_Hex (Field (7));
                  Eph     : constant Kome.Crypto.DH_Secret := From_Hex (Field (8));
                  Box_PK  : constant Pubkey := From_Hex (Field (9));
                  DH_PK   : constant Pubkey := From_Hex (Field (10));
                  Wrap    : constant Hash256 := From_Hex (Field (11));
                  Want_N  : constant Nonce := From_Hex (Field (12));
                  Want_B  : constant Kome.Box := From_Hex (Field (13));
                  N       : Nonce;
                  Sealed  : Kome.Box;
                  Got_PK  : Pubkey;
                  St      : Box_Status;
                  Got     : Key256;
               begin
                  N_Box := N_Box + 1;
                  --  The derived ephemeral secret (A6): the ghost model
                  --  Eph_SK_Of (an assertion, it is ghost), the
                  --  literal-label computation, and Box_PK_Of.
                  pragma Assert (Eph_SK_Of (K, Cid, Gen, Signer) = Eph);
                  if Eph_Ref (K, Cid, Gen, Signer) /= Eph
                    or else Box_PK_Of (K, Cid, Gen, Signer) /= Box_PK
                  then
                     Ok_Box := False;
                     Bad ("eph_sk / Box_PK_Of");
                  end if;
                  if Kome.Crypto.X25519_Public (Eph) /= Box_PK
                    or else Kome.Crypto.X25519_Public (DH_SK) /= DH_PK
                  then
                     Ok_Box := False;
                     Bad ("box_pk/dh_pk");
                  end if;
                  if Wrap_Ref (Eph, DH_PK, Box_PK, DH_PK, Sign_PK, Cid, Gen) /= Wrap
                    or else Wrap_Ref (DH_SK, Box_PK, Box_PK, DH_PK, Sign_PK, Cid, Gen) /= Wrap
                  then
                     Ok_Box := False;
                     Bad ("wrap_key");
                  end if;
                  if Box_Nonce (K, DH_PK) /= Want_N or else Nonce_Ref (K, DH_PK) /= Want_N then
                     Ok_Box := False;
                     Bad ("box nonce");
                  end if;
                  if Lock_Ref (Wrap, Want_N, Cid, Gen, K) /= Want_B then
                     Ok_Box := False;
                     Bad ("AEAD box");
                  end if;
                  Box_Key (K, Cid, Gen, Signer, DH_PK, Sign_PK, Got_PK, N, Sealed, St);
                  if St /= Box_OK or else Got_PK /= Box_PK or else N /= Want_N
                    or else Sealed /= Want_B
                  then
                     Ok_Box := False;
                     Bad ("Box_Key");
                  end if;
                  Unbox_Key (DH_SK, Sign_PK, Box_PK, Cid, Gen, Want_N, Want_B, Got, St);
                  if St /= Box_OK or else Got /= K then
                     Ok_Box := False;
                     Bad ("Unbox_Key");
                  end if;
               end;
            elsif Field (1) = "bundle" and then N_Fields = 3 then
               declare
                  K    : constant Key256 := Key_Of (Field (2));
                  Want : constant Key256 := Key_Of (Field (3));
               begin
                  N_Bundle := N_Bundle + 1;
                  if Bundle_Key_Of (K) /= Want
                    or else Kome.Keys.To_Bytes (Want)
                            /= F (Kome.Keys.To_Bytes (K), Ascii ("kome/bundle"))
                  then
                     Ok_Bundle := False;
                     Bad ("Bundle_Key_Of");
                  end if;
               end;
            else
               Check ("vector_line_parses (" & Field (1) & ")", False);
            end if;
         end if;
      end loop;
      Close (Fl);
      Check ("key_for_gen_matches_python_reference (" & N_Key'Image & " vectors)",
             Ok_Key and then N_Key = 6);
      Check ("box_matches_python_reference (" & N_Box'Image & " vectors)",
             Ok_Box and then N_Box = 6);
      Check ("bundle_key_matches_python_reference (" & N_Bundle'Image & " vectors)",
             Ok_Bundle and then N_Bundle = 3);
   end Vectors;

   ---------------------------------------------------------------------------
   --  (b) k_g (A6)
   ---------------------------------------------------------------------------

   procedure Keys is
      use Kome.Crypto;
      Seed_A : constant Seed := Pattern (Seed_Len, 1, 1);
      Seed_B : constant Seed := Pattern (Seed_Len, 7, 3);
      Cid_1  : constant Hash256 := Pattern (Hash_Len, 13, 7);
      Cid_2  : constant Hash256 := Pattern (Hash_Len, 29, 200);
      Rnd_1  : constant Random_Bytes := Pattern (Rnd_Len, 3, 17);
      Rnd_0  : constant Random_Bytes := [others => 0];
      SK_A, SK_B : Secret_Key;
      PK_A, PK_B : Pubkey;
      K, K2      : Key256;
      Ok_Fresh   : Boolean := True;
   begin
      Key_Pair (Seed_A, SK_A, PK_A);
      Key_Pair (Seed_B, SK_B, PK_B);
      Key_For_Gen (SK_A, Cid_1, 1, Rnd_1, K);
      Check ("k_g = f (seed, ""kome/key"" ‖ cid ‖ u48 (gen) ‖ rnd) (the hedge)",
             Kome.Keys.To_Bytes (K)
               = F (Seed_A, Ascii ("kome/key") & Cid_1 & U48_BE (1) & Rnd_1)
             and then K /= Zero_Key);
      Key_For_Gen (SK_A, Cid_1, 1, Rnd_1, K2);
      Check ("k_g is deterministic in (issuer, cid, gen, rnd)", K2 = K);
      Key_For_Gen (SK_A, Cid_1, 2, Rnd_1, K2);
      Ok_Fresh := Ok_Fresh and then K2 /= K;
      Key_For_Gen (SK_A, Cid_2, 1, Rnd_1, K2);
      Ok_Fresh := Ok_Fresh and then K2 /= K;
      Key_For_Gen (SK_A, Cid_1, 1, Rnd_0, K2);
      Ok_Fresh := Ok_Fresh and then K2 /= K;
      Key_For_Gen (SK_B, Cid_1, 1, Rnd_1, K2);
      Ok_Fresh := Ok_Fresh and then K2 /= K;
      Check ("k_g differs for another gen, cid, rnd or issuer", Ok_Fresh);
      --  A6: an attacker who knows rnd (here the all-zero rnd of a broken
      --  RNG) but not the seed does not get k_g: it is not the unkeyed or
      --  the public-key-keyed hash of the same message.
      Key_For_Gen (SK_A, Cid_1, 1, Rnd_0, K);
      Check ("k_g with a known rnd still depends on the secret seed (A6)",
             Kome.Keys.To_Bytes (K)
               /= Blake2b_256 (Ascii ("kome/key") & Cid_1 & U48_BE (1) & Rnd_0)
             and then Kome.Keys.To_Bytes (K)
               /= F (PK_A, Ascii ("kome/key") & Cid_1 & U48_BE (1) & Rnd_0)
             and then Kome.Keys.To_Bytes (K)
               = F (Seed_A, Ascii ("kome/key") & Cid_1 & U48_BE (1) & Rnd_0));
      Key_For_Gen (SK_B, Cid_2, U48'Last, Rnd_0, K);
      Check ("k_g at gen 2^48 - 1 is the hedge",
             Kome.Keys.To_Bytes (K)
               = F (Seed_B, Ascii ("kome/key") & Cid_2 & U48_BE (U48'Last) & Rnd_0));
      declare
         Bad_SK : Secret_Key;
         procedure Hedge_Invalid is
         begin
            Key_For_Gen (Bad_SK, Cid_1, 1, Rnd_1, K2);
         end Hedge_Invalid;
         function R is new Refused (Hedge_Invalid);
      begin
         Check ("key_for_gen_invalid_issuer_refused_by_pre", R);
      end;
      Wipe (SK_A);
      Wipe (SK_B);
   end Keys;

   ---------------------------------------------------------------------------
   --  (c) Boxes
   ---------------------------------------------------------------------------

   procedure Boxes is
      use Kome.Crypto;
      --  The roster identity (A6): the ephemeral secret is derived from
      --  (k_g, cid, gen, signer). Signer_A at gen 1 is "the roster".
      Signer_A   : constant Pubkey := Pattern (Pubkey_Len, 7, 3);
      Signer_B   : constant Pubkey := Pattern (Pubkey_Len, 11, 77);
      Member_SK  : constant DH_Secret := Pattern (DH_Key_Len, 13, 101);
      Other_SK   : constant DH_Secret := Pattern (DH_Key_Len, 31, 9);
      Member_Sig : constant Pubkey := Pattern (Pubkey_Len, 17, 5);
      Other_Sig  : constant Pubkey := Pattern (Pubkey_Len, 3, 200);
      Member_PK  : constant Pubkey := X25519_Public (Member_SK);
      Other_PK   : constant Pubkey := X25519_Public (Other_SK);
      Cid_1      : constant Hash256 := Pattern (Hash_Len, 13, 7);
      Cid_2      : constant Hash256 := Flip (Cid_1, 31);
      K_G        : constant Key256 :=
        Key_Of ("ba7fa1f528a3ae574e52dbbc4c8fd147b24842609ea89437adca6c7541f9c24c");
      K_H        : constant Key256 :=
        Key_Of ("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f");
      G          : constant U48 := 1_234;

      Eph_SK  : constant DH_Secret := Eph_Ref (K_G, Cid_1, G, Signer_A);
      Box_PK  : constant Pubkey := Box_PK_Of (K_G, Cid_1, G, Signer_A);

      N, N2         : Nonce;
      Sealed, Sealed2, Bad : Kome.Box;
      PK, PK2       : Pubkey;
      St, St2       : Box_Status;
      Got           : Key256;
   begin
      Check ("eph_sk_is_keyed_blake2b_of_kome_eph_inputs",
             Box_PK = X25519_Public (Eph_SK));
      pragma Assert (Eph_SK_Of (K_G, Cid_1, G, Signer_A) = Eph_SK);
      Check ("box_pk_is_reduced", Kome.Epochs.Is_Reduced_U (Box_PK));
      --  Each derivation input changes eph_sk (and so box_pk).
      Check ("eph_sk_covers_every_input",
             Box_PK_Of (K_G, Cid_1, G, Signer_B) /= Box_PK
             and then Box_PK_Of (K_G, Cid_2, G, Signer_A) /= Box_PK
             and then Box_PK_Of (K_G, Cid_1, G + 1, Signer_A) /= Box_PK
             and then Box_PK_Of (K_H, Cid_1, G, Signer_A) /= Box_PK
             and then Box_PK_Of (K_G, Cid_1, U48'Last, Signer_A) /= Box_PK
             and then Box_PK_Of (K_G, Cid_1, G, Signer_A) = Box_PK);

      Box_Key (K_G, Cid_1, G, Signer_A, Member_PK, Member_Sig, PK, N, Sealed, St);
      Check ("box_ok", St = Box_OK and then not Is_Zero_Box (Sealed)
                       and then not Is_Zero_Nonce (N));
      Check ("box_pk_by_construction (G7)", PK = Box_PK);
      Check ("box_layout_cipher_tag",
             Cipher_Of (Sealed) = Sealed (0 .. 31)
             and then Tag_Of (Sealed) = Sealed (32 .. 47)
             and then Cipher_Of (Sealed) & Tag_Of (Sealed) = Sealed);
      Check ("box_hides_key", Cipher_Of (Sealed) /= Kome.Keys.To_Bytes (K_G));

      --  The nonce is the synthetic nonce, computed again independently.
      --  The box is the AEAD under the wrap key.
      declare
         WK : constant Hash256 :=
           Wrap_Ref (Eph_SK, Member_PK, Box_PK, Member_PK, Member_Sig, Cid_1, G);
      begin
         Check ("box_nonce_is_synthetic",
                N = Nonce_Ref (K_G, Member_PK) and then N = Box_Nonce (K_G, Member_PK));
         Check ("box_is_aead_under_wrap_key", Sealed = Lock_Ref (WK, N, Cid_1, G, K_G));
         Check ("wrap_key_agrees_both_sides",
                WK = Wrap_Ref (Member_SK, Box_PK, Box_PK, Member_PK, Member_Sig, Cid_1, G));

         --  This box passes the AEAD under the correct wrap key, but its
         --  nonce is not the synthetic nonce. The member's nonce check
         --  refuses it (D6).
         declare
            Forged_N : constant Nonce := Pattern (Nonce_Len, 5, 1);
            Forged   : constant Kome.Box := Lock_Ref (WK, Forged_N, Cid_1, G, K_G);
         begin
            Unbox_Key (Member_SK, Member_Sig, Box_PK, Cid_1, G, Forged_N, Forged, Got, St);
            Check ("unbox_non_synthetic_nonce_refused",
                   Forged_N /= N and then St = Not_Authentic and then Got = Zero_Key);
         end;
         --  A box of the all-zero key with its synthetic nonce passes the
         --  AEAD and the nonce check, and Unbox_Key still refuses it.
         declare
            Zero_N : constant Nonce := Nonce_Ref (Zero_Key, Member_PK);
            Zero_B : constant Kome.Box := Lock_Ref (WK, Zero_N, Cid_1, G, Zero_Key);
         begin
            Unbox_Key (Member_SK, Member_Sig, Box_PK, Cid_1, G, Zero_N, Zero_B, Got, St);
            Check ("unbox_zero_key_refused", St = Not_Authentic and then Got = Zero_Key);
         end;
      end;

      Unbox_Key (Member_SK, Member_Sig, Box_PK, Cid_1, G, N, Sealed, Got, St);
      Check ("unbox_round_trip", St = Box_OK and then Got = K_G);

      Box_Key (K_G, Cid_1, G, Signer_A, Member_PK, Member_Sig, PK2, N2, Sealed2, St2);
      Check ("box_deterministic",
             St2 = Box_OK and then PK2 = PK and then N2 = N and then Sealed2 = Sealed);

      --  A box to a different member is different. It opens only for that
      --  member. Every member box of one roster carries the same box_pk.
      Box_Key (K_G, Cid_1, G, Signer_A, Other_PK, Other_Sig, PK2, N2, Sealed2, St2);
      Check ("box_per_member",
             St2 = Box_OK and then Sealed2 /= Sealed and then N2 /= N
             and then PK2 = Box_PK);
      Unbox_Key (Other_SK, Other_Sig, Box_PK, Cid_1, G, N2, Sealed2, Got, St);
      Check ("unbox_other_member", St = Box_OK and then Got = K_G);

      --  The wrap key binds sign_pk: the same dh_pk with a different
      --  sign_pk gets a different box (the nonce depends on dh_pk only).
      Box_Key (K_G, Cid_1, G, Signer_A, Member_PK, Other_Sig, PK2, N2, Sealed2, St2);
      Check ("box_binds_sign_pk",
             St2 = Box_OK and then Sealed2 /= Sealed and then N2 = N);

      --  Wrong inputs fail and give the zero key.
      Unbox_Key (Other_SK, Member_Sig, Box_PK, Cid_1, G, N, Sealed, Got, St);
      Check ("unbox_wrong_member_fails", St = Not_Authentic and then Got = Zero_Key);
      Unbox_Key (Member_SK, Other_Sig, Box_PK, Cid_1, G, N, Sealed, Got, St);
      Check ("unbox_wrong_sign_pk_fails", St = Not_Authentic and then Got = Zero_Key);
      Unbox_Key (Member_SK, Member_Sig, Other_PK, Cid_1, G, N, Sealed, Got, St);
      Check ("unbox_wrong_box_pk_fails", St = Not_Authentic and then Got = Zero_Key);
      Unbox_Key (Member_SK, Member_Sig, Box_PK, Cid_1, G, Flip (N, 7), Sealed, Got, St);
      Check ("unbox_wrong_nonce_fails", St = Not_Authentic and then Got = Zero_Key);
      Unbox_Key (Member_SK, Member_Sig, Box_PK, Cid_1, G + 1, N, Sealed, Got, St);
      Check ("unbox_wrong_gen_fails", St = Not_Authentic and then Got = Zero_Key);
      Unbox_Key (Member_SK, Member_Sig, Box_PK, Cid_2, G, N, Sealed, Got, St);
      Check ("unbox_wrong_cid_fails", St = Not_Authentic and then Got = Zero_Key);

      declare
         Ok : Boolean := True;
      begin
         for I in Sealed'Range loop
            Bad := Flip (Sealed, I);
            Unbox_Key (Member_SK, Member_Sig, Box_PK, Cid_1, G, N, Bad, Got, St);
            if St /= Not_Authentic or else Got /= Zero_Key then
               Ok := False;
            end if;
         end loop;
         Check ("unbox_tamper_every_byte_fails", Ok);
      end;

      --  Low-order peers, all with reduced encodings (so the refusal is for
      --  the low order, not for the encoding): u = 0, u = 1, the two points
      --  of order 8 and u = p - 1 (order 2).
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
            Box_Key (K_G, Cid_1, G, Signer_A, U, Member_Sig, PK2, N2, Bad, St);
            if St /= Low_Order_Peer or else not Is_Zero_Box (Bad)
              or else not Is_Zero_Nonce (N2) or else PK2 /= Box_PK
            then
               Ok_Box := False;
            end if;
            Unbox_Key (Member_SK, Member_Sig, U, Cid_1, G, N, Sealed, Got, St);
            if St /= Low_Order_Peer or else Got /= Zero_Key then
               Ok_Unbox := False;
            end if;
         end loop;
         Check ("low_order_points_are_reduced_and_not_good", Ok_Red);
         Check ("box_low_order_refused (u=0, u=1, order 8 x2, p-1)", Ok_Box);
         Check ("unbox_low_order_box_pk_refused (u=0, u=1, order 8 x2, p-1)", Ok_Unbox);
      end;

      --  Non-reduced encodings. Member_PK with bit 255 set is the same
      --  point (X25519 ignores the bit) and gives the same shared secret.
      --  But the wrap key and the nonce hash the bytes, so a box sealed to
      --  it never opens for the member. It is refused. Each u >= p is also
      --  refused.
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
                and then Kome.Epochs.Is_Reduced_U (P1_Enc)
                and then Kome.Epochs.Is_Reduced_U (Mid_Enc)
                and then not Kome.Epochs.Is_Reduced_U (P_Enc)
                and then not Kome.Epochs.Is_Reduced_U (P2_Enc)
                and then not Kome.Epochs.Is_Reduced_U (Max_Enc)
                and then not Kome.Epochs.Is_Reduced_U (Hi_Member));
         Box_Key (K_G, Cid_1, G, Signer_A, Hi_Member, Member_Sig, PK2, N2, Bad, St);
         Check ("box_member_bit255_refused",
                St = Non_Canonical_Peer and then Is_Zero_Box (Bad)
                and then Is_Zero_Nonce (N2) and then PK2 = Box_PK);
         Box_Key (K_G, Cid_1, G, Signer_A, P2_Enc, Member_Sig, PK2, N2, Bad, St);
         Check ("box_member_u_ge_p_refused",
                St = Non_Canonical_Peer and then Is_Zero_Box (Bad) and then Is_Zero_Nonce (N2));
         Box_Key (K_G, Cid_1, G, Signer_A, P_Enc, Member_Sig, PK2, N2, Bad, St);
         Check ("box_member_u_eq_p_refused_as_non_canonical",
                St = Non_Canonical_Peer and then Is_Zero_Box (Bad));
         Unbox_Key (Member_SK, Member_Sig, Hi_Box, Cid_1, G, N, Sealed, Got, St);
         Check ("unbox_box_pk_bit255_refused",
                St = Non_Canonical_Peer and then Got = Zero_Key);
         Unbox_Key (Member_SK, Member_Sig, P2_Enc, Cid_1, G, N, Sealed, Got, St);
         Check ("unbox_box_pk_u_ge_p_refused",
                St = Non_Canonical_Peer and then Got = Zero_Key);
         Check ("x25519_public_is_reduced",
                Kome.Epochs.Is_Reduced_U (X25519_Public (Member_SK))
                and then Kome.Epochs.Is_Reduced_U (X25519_Public (Other_SK))
                and then Kome.Epochs.Is_Reduced_U (Box_PK));
      end;

      --  Edge gens.
      Box_Key (K_H, Cid_1, U48'Last, Signer_B, Member_PK, Member_Sig, PK2, N2, Sealed2, St2);
      Unbox_Key (Member_SK, Member_Sig, PK2, Cid_1, U48'Last, N2, Sealed2, Got, St);
      Check ("box_round_trip_max_gen",
             St2 = Box_OK and then St = Box_OK and then Got = K_H
             and then PK2 = Box_PK_Of (K_H, Cid_1, U48'Last, Signer_B));
      Box_Key (K_H, Cid_1, 0, Signer_A, Member_PK, Member_Sig, PK2, N2, Sealed2, St2);
      Unbox_Key (Member_SK, Member_Sig, PK2, Cid_1, 0, N2, Sealed2, Got, St);
      Check ("box_round_trip_gen_0", St2 = Box_OK and then St = Box_OK and then Got = K_H);

      --  The all-zero key is refused by Pre (A27): Unbox_Key's refusal
      --  value must never be sealed on.
      declare
         procedure Box_Zero is
         begin
            Box_Key (Zero_Key, Cid_1, 0, Signer_A, Member_PK, Member_Sig,
                     PK2, N2, Sealed2, St2);
         end Box_Zero;
         function Box_Zero_Refused is new Refused (Box_Zero);
      begin
         Check ("box_zero_key_refused_by_pre", Box_Zero_Refused);
      end;

      --  The bundle key: one PRF output under k_g, different per key.
      Check ("bundle_key_is_f_kome_bundle",
             Kome.Keys.To_Bytes (Bundle_Key_Of (K_G))
               = F (Kome.Keys.To_Bytes (K_G), Ascii ("kome/bundle"))
             and then Bundle_Key_Of (K_G) /= Bundle_Key_Of (K_H)
             and then Bundle_Key_Of (K_G) /= K_G);
   end Boxes;

   ---------------------------------------------------------------------------
   --  (d) Regressions: a refresh (same members, next gen) has a fresh key
   ---------------------------------------------------------------------------

   procedure Regressions is
      use Kome.Crypto;
      Seed_A     : constant Seed := Pattern (Seed_Len, 1, 1);
      Signer_A   : Pubkey;
      SK_A       : Secret_Key;
      Member_SK  : constant DH_Secret := Pattern (DH_Key_Len, 13, 101);
      Member_Sig : constant Pubkey := Pattern (Pubkey_Len, 17, 5);
      Member_PK  : constant Pubkey := X25519_Public (Member_SK);
      Cid        : constant Hash256 := Pattern (Hash_Len, 13, 7);
      Rnd        : constant Random_Bytes := Pattern (Rnd_Len, 3, 17);
      K1, K2     : Key256;
      P1, P2     : Pubkey;
      N1, N2     : Nonce;
      B1, B2     : Kome.Box;
      S1, S2     : Box_Status;
      Got        : Key256;
      St         : Box_Status;
   begin
      Key_Pair (Seed_A, SK_A, Signer_A);
      --  The roster at gen 1 and its refresh at gen 2 (same rnd: even a
      --  stuck RNG gives a new key, because gen is in the hedge).
      Key_For_Gen (SK_A, Cid, 1, Rnd, K1);
      Key_For_Gen (SK_A, Cid, 2, Rnd, K2);
      Box_Key (K1, Cid, 1, Signer_A, Member_PK, Member_Sig, P1, N1, B1, S1);
      Box_Key (K2, Cid, 2, Signer_A, Member_PK, Member_Sig, P2, N2, B2, S2);
      Check ("refresh_fresh_key_box_pk_nonce",
             S1 = Box_OK and then S2 = Box_OK and then K1 /= K2
             and then P1 /= P2 and then N1 /= N2 and then B1 /= B2);
      Check ("k1_does_not_recover_k2 (no keystream reuse across gens)",
             Xor_Bytes (Xor_Bytes (Cipher_Of (B1), Cipher_Of (B2)), Kome.Keys.To_Bytes (K1))
               /= Kome.Keys.To_Bytes (K2));
      Unbox_Key (Member_SK, Member_Sig, P1, Cid, 2, N1, B1, Got, St);
      Check ("box_gen1_not_open_at_gen2", St = Not_Authentic and then Got = Zero_Key);
      Unbox_Key (Member_SK, Member_Sig, P2, Cid, 2, N2, B2, Got, St);
      Check ("box_gen2_opens", St = Box_OK and then Got = K2);
      Check ("bundle_key_changes_with_the_roster", Bundle_Key_Of (K1) /= Bundle_Key_Of (K2));
      Wipe (SK_A);
   end Regressions;

begin
   Layouts;
   Vectors;
   Keys;
   Boxes;
   Regressions;
   if Failed then
      Set_Exit_Status (Failure);
   end if;
end Test_Epochs;
