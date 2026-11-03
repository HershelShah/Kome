--  Test main for Kome.Crypto. The known answers come from vectors/crypto.txt
--  (its header tells where each answer comes from):
--    * BLAKE2b;
--    * RFC 8032 Ed25519 TESTs 1-3;
--    * a Wycheproof ed25519 subset (valid, S >= L, non-canonical R,
--      truncated);
--    * non-canonical encodings that plain monocypher accepts;
--    * regressions that show that Kome now rejects the pre-D4
--      BLAKE2b-EdDSA answers;
--    * X25519 (RFC 7748, low order, Is_Reduced_U / Is_Low_Order_U answers);
--    * AEAD.
--  Then the test checks named answers, round trips, tamper rejection, the
--  wipes, the default-initial conditions and the refusals of the
--  contracts. Only a failed Pre of Kome.Crypto counts as a refusal. The
--  test is compiled with -gnata. Thus each Pre, Post and DIC of the
--  binding, and the ghost functions Is_Valid and Seed_Of, run against the
--  real output of monocypher.
pragma Ada_2022;
with Ada.Command_Line;   use Ada.Command_Line;
with Ada.Text_IO;        use Ada.Text_IO;
with Ada.Directories;
with Ada.Exceptions;
with Ada.Assertions;
with Ada.Strings.Fixed;
with Ada.Numerics.Discrete_Random;
with Kome;               use Kome;
with Kome.Crypto;        use Kome.Crypto;

procedure Test_Crypto with SPARK_Mode => Off is

   Failed : Boolean := False;

   --  The results of calls that the test makes only for their refusal go
   --  here. The object is Volatile, so no store (and thus no call) is dead.
   Sink_Sig  : Sig     := [others => 0] with Volatile;
   Sink_Hash : Hash256 := [others => 0] with Volatile;

   procedure Check (Name : String; Ok : Boolean) is
   begin
      Put_Line ((if Ok then "PASS " else "FAIL ") & Name);
      if not Ok then
         Failed := True;
      end if;
   end Check;

   ---------------------------------------------------------------------------
   --  Hex helpers
   ---------------------------------------------------------------------------

   function Nibble (C : Character) return Byte is
     (case C is
         when '0' .. '9' => Character'Pos (C) - Character'Pos ('0'),
         when 'a' .. 'f' => Character'Pos (C) - Character'Pos ('a') + 10,
         when 'A' .. 'F' => Character'Pos (C) - Character'Pos ('A') + 10,
         when others     => raise Constraint_Error with "bad hex");

   --  "-" denotes the empty byte string.
   function From_Hex (S : String) return Byte_Array is
   begin
      if S = "-" then
         return Empty : Byte_Array (1 .. 0);
      end if;
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

   function Ascii (S : String) return Byte_Array is
      R : Byte_Array (0 .. S'Length - 1);
   begin
      for I in R'Range loop
         R (I) := Character'Pos (S (S'First + I));
      end loop;
      return R;
   end Ascii;

   function Pattern (N : Natural; Mul, Add : Natural) return Byte_Array is
      R : Byte_Array (0 .. N - 1);
   begin
      for I in R'Range loop
         R (I) := Byte ((I * Mul + Add) mod 256);
      end loop;
      return R;
   end Pattern;

   --  Expect a refusal by a precondition of Kome.Crypto. Under -gnata, a
   --  failed Pre raises Assertion_Error with the message "failed
   --  precondition from kome-crypto.ads:<line>". Any other exception is not
   --  a refusal, and it propagates as a test failure. Examples are a
   --  Constraint_Error in the body or the test, a failed Post, and a failed
   --  Pre in a different unit.
   Pre_Tag : constant String := "failed precondition from kome-crypto.ads";

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

   --  Only assertions can state facts about the ghost functions (Is_Valid,
   --  Seed_Of). Holds runs a procedure made of pragma Asserts, and it
   --  reports whether all of them held. Under -gnata, a false assertion
   --  raises Assertion_Error.
   generic
      with procedure Run;
   function Holds return Boolean;
   function Holds return Boolean is
   begin
      Run;
      return True;
   exception
      when E : Ada.Assertions.Assertion_Error =>
         Put_Line ("  assertion failed: " & Ada.Exceptions.Exception_Message (E));
         return False;
   end Holds;

   --  True iff B cannot become a Sig (its length is not Sig_Len). The
   --  conversion raises Constraint_Error, so such bytes never get to Verify.
   function Not_A_Sig (B : Byte_Array) return Boolean is
   begin
      declare
         S : constant Sig := B;
      begin
         Sink_Sig := S;
         return False;
      end;
   exception
      when Constraint_Error => return True;
   end Not_A_Sig;

   ---------------------------------------------------------------------------
   --  Named answers
   ---------------------------------------------------------------------------

   --  python3 -c "import hashlib; print(hashlib.blake2b(b'', digest_size=32).hexdigest())"
   B2_Empty : constant Byte_Array := From_Hex
     ("0e5751c026e543b2e8ab2eb06099daa1d1e5df47778f7787faab45cdf12fe3a8");
   --  python3 -c "import hashlib; print(hashlib.blake2b(b'abc', digest_size=32).hexdigest())"
   B2_Abc : constant Byte_Array := From_Hex
     ("bddd813c634239723171ef3fee98579b94964e3bb1cb3e427262c8c068d52319");

   --  RFC 8032 §7.1 TEST 1 (Ed25519, SHA-512 internal). The binding uses
   --  this scheme since D4.
   RFC_Seed : constant Byte_Array := From_Hex
     ("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60");
   RFC_Pub : constant Byte_Array := From_Hex
     ("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a");
   RFC_Sig : constant Byte_Array := From_Hex
     ("e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e06522490155"
      & "5fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b");
   --  REGRESSION: the same seed and message under crypto_eddsa of
   --  monocypher (BLAKE2b-512 in place of SHA-512). This was the binding
   --  before D4. The values come from the independent reference behind
   --  vectors/crypto.txt. Verify must now reject them.
   B2_Pub : constant Byte_Array := From_Hex
     ("78e65bf30f893d32fc57ef051c341bdede242544fc2a2112f0fa2c7afdebc02f");
   B2_Sig : constant Byte_Array := From_Hex
     ("99a523bd4616c8161144d6a99d3c32400cb4a326f4d79e307340f6afa11750a0"
      & "085d7d84626bc9e4b153fc0e396d15ce44c39bae4533804db1fe5b52f2b1b805");

   --  The group order L, little-endian (RFC 8032 §5.1).
   L_LE : constant Byte_Array := From_Hex
     ("edd3f55c1a631258d69cf7a2def9de1400000000000000000000000000000010");

   procedure Named_Answers is
      D   : Hash256;
      Ctx : Blake2b_Context;
      SK  : Secret_Key;
      PK  : Pubkey;
      Empty : constant Byte_Array (1 .. 0) := [];
   begin
      Check ("blake2b256_empty", Blake2b_256 (Empty) = B2_Empty);
      Check ("blake2b256_abc", Blake2b_256 (Ascii ("abc")) = B2_Abc);
      Init (Ctx);
      Final (Ctx, D);
      Check ("blake2b256_empty_incremental", D = B2_Empty);
      Init (Ctx);
      Update (Ctx, Ascii ("a"));
      Update (Ctx, Empty);
      Update (Ctx, Ascii ("bc"));
      Check ("blake2b256_count", Absorbed (Ctx) = 3 and then Is_Active (Ctx));
      Final (Ctx, D);
      Check ("blake2b256_abc_incremental", D = B2_Abc);
      Check ("blake2b256_final_inactive",
             not Is_Active (Ctx) and then Absorbed (Ctx) = 0);

      --  RFC 8032 TEST 1: the key pair layout, the public key, the
      --  signature, and verification (D4: RFC 8032 Ed25519).
      Key_Pair (RFC_Seed, SK, PK);
      declare
         procedure Layout is
         begin
            pragma Assert (Is_Valid (SK));
            pragma Assert (Seed_Of (SK) = RFC_Seed);
         end Layout;
         function Layout_Holds is new Holds (Layout);
      begin
         Check ("ed25519_rfc8032_t1_secret_layout",
                Layout_Holds and then Public_Of (SK) = PK);
      end;
      Check ("ed25519_rfc8032_t1_public", PK = RFC_Pub);
      Check ("ed25519_rfc8032_t1_derive_public", Derive_Public (RFC_Seed) = RFC_Pub);
      Check ("ed25519_rfc8032_t1_sign", Sign (SK, Empty) = RFC_Sig);
      Check ("ed25519_rfc8032_t1_verify", Verify (RFC_Sig, RFC_Pub, Empty));
      Check ("ed25519_rfc8032_t1_encodings_canonical",
             S_Below_L (RFC_Sig)
             and then Is_Canonical_Point (RFC_Sig (0 .. 31))
             and then Is_Canonical_Point (RFC_Pub));

      --  REGRESSION (D4: Ed25519, not BLAKE2b-EdDSA): the BLAKE2b-EdDSA
      --  public key is not derived from the TEST 1 seed. Verify rejects its
      --  signature under both the BLAKE2b-EdDSA key and the Ed25519 key.
      Check ("b2eddsa_rfc8032_t1_public_no_longer_derived", PK /= B2_Pub);
      Check ("b2eddsa_rfc8032_t1_old_sig_rejected",
             not Verify (B2_Sig, B2_Pub, Empty)
             and then not Verify (B2_Sig, RFC_Pub, Empty));
      Wipe (SK);
   end Named_Answers;

   ---------------------------------------------------------------------------
   --  Vector file
   ---------------------------------------------------------------------------

   --  check.sh runs the binary from spark. Also accept a run from
   --  bin/<module>.
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

   --  Hash Msg through the incremental interface in chunks of Step bytes.
   function Chunked (Msg : Byte_Array; Step : Positive) return Hash256 is
      Ctx : Blake2b_Context;
      D   : Hash256;
      I   : Natural := Msg'First;
   begin
      Init (Ctx);
      while I <= Msg'Last loop
         declare
            J : constant Natural := Natural'Min (Msg'Last, I + Step - 1);
         begin
            Update (Ctx, Msg (I .. J));
            I := J + 1;
         end;
      end loop;
      if Absorbed (Ctx) /= Stream_Len (Msg'Length) then
         return [others => 0];
      end if;
      Final (Ctx, D);
      return D;
   end Chunked;

   --  Hash Msg as two pieces split at K.
   function Split (Msg : Byte_Array; K : Natural) return Hash256 is
      Ctx : Blake2b_Context;
      D   : Hash256;
   begin
      Init (Ctx);
      Update (Ctx, Msg (Msg'First .. Msg'First + K - 1));
      Update (Ctx, Msg (Msg'First + K .. Msg'Last));
      Final (Ctx, D);
      return D;
   end Split;

   procedure Vectors is
      Path : constant String := Find ("vectors/crypto.txt");
      F    : File_Type;
      Line : String (1 .. 8192);
      Last : Natural;

      type Field_Bounds is record
         First, Last : Natural;
      end record;
      Fields   : array (1 .. 8) of Field_Bounds;
      N_Fields : Natural;

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
      function Hex (K : Positive) return Byte_Array is (From_Hex (Field (K)));

      N_B2, N_Ed, N_Old, N_Old_Pk, N_X, N_Low, N_DH, N_AE, N_Key,
      N_Strict_Valid, N_Strict_Invalid : Natural := 0;
      N_Wp_Valid, N_Wp_Invalid, N_Wp_Length : Natural := 0;
      Seen_151, Seen_S_Over_L : Boolean := False;
      Ok_B2, Ok_B2_Inc, Ok_Ed, Ok_Ed_Tamper, Ok_Old, Ok_Old_Pk, Ok_Wp,
      Ok_Strict, Ok_X, Ok_Low, Ok_DH, Ok_AE, Ok_AE_Tamper, Ok_Key : Boolean
        := True;

      procedure Fail (Flag : in out Boolean; What : String) is
      begin
         Flag := False;
         Put_Line ("  mismatch: " & What & " " & Field (2)
                   (Field (2)'First .. Field (2)'First
                      + Natural'Min (15, Field (2)'Length - 1)));
      end Fail;

      type Positive_List is array (Positive range <>) of Positive;
      Steps : constant Positive_List := [1, 3, 64, 127, 128, 129, 1000];

      procedure Do_Blake2b is
         Msg  : constant Byte_Array := Hex (2);
         Want : constant Byte_Array := Hex (3);
      begin
         N_B2 := N_B2 + 1;
         if Blake2b_256 (Msg) /= Want then
            Fail (Ok_B2, "blake2b256");
         end if;
         --  Incremental: the whole input, one byte at a time, around the
         --  block size, and two pieces at each split point.
         for Step of Steps loop
            if Chunked (Msg, Step) /= Want then
               Fail (Ok_B2_Inc, "blake2b256 chunked" & Step'Image);
            end if;
         end loop;
         for K in 0 .. Msg'Length loop
            if Split (Msg, K) /= Want then
               Fail (Ok_B2_Inc, "blake2b256 split" & K'Image);
            end if;
         end loop;
      end Do_Blake2b;

      --  RFC 8032 §7.1: seed -> public key, sign, verify, and tamper checks.
      procedure Do_Ed25519 is
         S    : constant Seed       := Hex (2);
         Pub  : constant Pubkey     := Hex (3);
         Msg  : constant Byte_Array := Hex (4);
         Want : constant Sig        := Hex (5);
         SK   : Secret_Key;
         PK   : Pubkey;
         T    : Sig;
         Other : Pubkey;
         procedure Seed_Kept is
         begin
            pragma Assert (Seed_Of (SK) = S);
         end Seed_Kept;
         function Seed_Kept_Holds is new Holds (Seed_Kept);
      begin
         N_Ed := N_Ed + 1;
         Key_Pair (S, SK, PK);
         if PK /= Pub or else Public_Of (SK) /= Pub
           or else Derive_Public (S) /= Pub or else not Seed_Kept_Holds
         then
            Fail (Ok_Ed, "ed25519 public");
         end if;
         if Sign (SK, Msg) /= Want then
            Fail (Ok_Ed, "ed25519 sign");
         end if;
         if not Verify (Want, Pub, Msg) then
            Fail (Ok_Ed, "ed25519 verify");
         end if;
         --  Tamper checks: a bit of R, a bit of S, the message, the key.
         T := Want;
         T (0) := T (0) xor 1;
         if Verify (T, Pub, Msg) then
            Fail (Ok_Ed_Tamper, "ed25519 R flip");
         end if;
         T := Want;
         T (40) := T (40) xor 16#80#;
         if Verify (T, Pub, Msg) then
            Fail (Ok_Ed_Tamper, "ed25519 S flip");
         end if;
         if Verify (Want, Pub, Msg & Byte (0)) then
            Fail (Ok_Ed_Tamper, "ed25519 msg extended");
         end if;
         if Msg'Length > 0 then
            declare
               M2 : Byte_Array := Msg;
            begin
               M2 (M2'Last) := M2 (M2'Last) xor 1;
               if Verify (Want, Pub, M2) then
                  Fail (Ok_Ed_Tamper, "ed25519 msg flip");
               end if;
            end;
         end if;
         Other := Pub;
         Other (5) := Other (5) xor 4;
         if Verify (Want, Other, Msg) then
            Fail (Ok_Ed_Tamper, "ed25519 other key");
         end if;
         Wipe (SK);
      end Do_Ed25519;

      --  Wycheproof ed25519_test.json: Verify agrees with "result" on each
      --  64-byte signature. A signature of a different length cannot become
      --  a Sig.
      procedure Do_Wycheproof is
         Id    : constant String     := Field (2);
         Res   : constant String     := Field (3);
         Pub   : constant Pubkey     := Hex (4);
         Msg   : constant Byte_Array := Hex (5);
         Raw   : constant Byte_Array := Hex (6);
         Valid : constant Boolean    := Res = "valid";
      begin
         if Res /= "valid" and then Res /= "invalid" then
            Fail (Ok_Wp, "wycheproof result " & Res & " tcId " & Id);
            return;
         end if;
         if Raw'Length = Sig_Len then
            declare
               S : constant Sig := Raw;
            begin
               if Valid then
                  N_Wp_Valid := N_Wp_Valid + 1;
               else
                  N_Wp_Invalid := N_Wp_Invalid + 1;
               end if;
               if Verify (S, Pub, Msg) /= Valid then
                  Fail (Ok_Wp, "wycheproof tcId " & Id);
               end if;
               if Id = "151" then
                  Seen_151 := True;
               end if;
               if not S_Below_L (S) then
                  Seen_S_Over_L := True;
               end if;
            end;
         else
            N_Wp_Length := N_Wp_Length + 1;
            if Valid or else not Not_A_Sig (Raw) then
               Fail (Ok_Wp, "wycheproof length tcId " & Id);
            end if;
         end if;
      end Do_Wycheproof;

      --  Non-canonical encodings that plain crypto_ed25519_check accepts:
      --  Verify rejects exactly those. The encoding check causes the
      --  rejection (the S scalar is reduced on each line).
      procedure Do_Strict is
         Valid : constant Boolean    := Field (2) = "valid";
         Pub   : constant Pubkey     := Hex (3);
         Msg   : constant Byte_Array := Hex (4);
         S     : constant Sig        := Hex (5);
         Canon : constant Boolean    :=
           Is_Canonical_Point (S (0 .. 31)) and then Is_Canonical_Point (Pub);
      begin
         if Valid then
            N_Strict_Valid := N_Strict_Valid + 1;
         else
            N_Strict_Invalid := N_Strict_Invalid + 1;
         end if;
         if Verify (S, Pub, Msg) /= Valid or else Canon /= Valid
           or else not S_Below_L (S)
         then
            Fail (Ok_Strict, "ed25519_strict");
         end if;
      end Do_Strict;

      --  REGRESSION: Verify now rejects the pre-D4 BLAKE2b-EdDSA answers.
      procedure Do_Old is
         S       : constant Seed       := Hex (2);
         Old_Pub : constant Pubkey     := Hex (3);
         Msg     : constant Byte_Array := Hex (4);
         Old_Sig : constant Sig        := Hex (5);
         SK      : Secret_Key;
         PK      : Pubkey;
      begin
         N_Old := N_Old + 1;
         Key_Pair (S, SK, PK);
         if PK = Old_Pub or else Verify (Old_Sig, Old_Pub, Msg)
           or else Verify (Old_Sig, PK, Msg)
         then
            Fail (Ok_Old, "b2eddsa_old accepted");
         end if;
         Wipe (SK);
      end Do_Old;

      procedure Do_X25519 is
         K    : constant DH_Secret     := Hex (2);
         U    : constant Pubkey        := Hex (3);
         Want : constant Shared_Secret := Hex (4);
         Got  : Shared_Secret;
         Contrib : Boolean;
      begin
         N_X := N_X + 1;
         X25519 (K, U, Got, Contrib);
         if Got /= Want or else not Contrib then
            Fail (Ok_X, "x25519");
         end if;
      end Do_X25519;

      --  A low-order u: each scalar gives all zeros, and X25519 reports
      --  this as not contributory. The test uses several secrets.
      procedure Do_Low_Order is
         U       : constant Pubkey := Hex (2);
         Got     : Shared_Secret;
         Contrib : Boolean;
      begin
         N_Low := N_Low + 1;
         for K in 0 .. 3 loop
            X25519 (Pattern (DH_Key_Len, 37, K * 11 + 5), U, Got, Contrib);
            if Contrib or else not Is_Zero (Got)
              or else (for some X of Got => X /= 0)
            then
               Fail (Ok_Low, "x25519 low order");
            end if;
         end loop;
      end Do_Low_Order;

      --  REGRESSION: a published Ed25519-BLAKE2b key pair is not the key
      --  pair that Kome derives now.
      procedure Do_Old_Pk is
         S   : constant Seed   := Hex (2);
         Pub : constant Pubkey := Hex (3);
         SK  : Secret_Key;
         PK  : Pubkey;
      begin
         N_Old_Pk := N_Old_Pk + 1;
         Key_Pair (S, SK, PK);
         if PK = Pub or else Derive_Public (S) = Pub then
            Fail (Ok_Old_Pk, "b2eddsa published public key still derived");
         end if;
         Wipe (SK);
      end Do_Old_Pk;

      --  Is_Reduced_U, Is_Low_Order_U and Is_Good_DH_Key against the
      --  expected answers. A low-order key is also never contributory.
      procedure Do_DH_Key is
         U       : constant Pubkey  := Hex (2);
         Reduced : constant Boolean := Field (3) = "1";
         Low     : constant Boolean := Field (4) = "1";
         Got     : Shared_Secret;
         Contrib : Boolean;
      begin
         N_Key := N_Key + 1;
         if Is_Reduced_U (U) /= Reduced or else Is_Low_Order_U (U) /= Low
           or else Is_Good_DH_Key (U) /= (Reduced and then not Low)
         then
            Fail (Ok_Key, "dh_key");
         end if;
         if Low then
            X25519 (Pattern (DH_Key_Len, 41, 3), U, Got, Contrib);
            if Contrib then
               Fail (Ok_Key, "dh_key low order contributory");
            end if;
         end if;
      end Do_DH_Key;

      procedure Do_DH is
         A_SK : constant DH_Secret     := Hex (2);
         A_PK : constant Pubkey        := Hex (3);
         B_SK : constant DH_Secret     := Hex (4);
         B_PK : constant Pubkey        := Hex (5);
         Want : constant Shared_Secret := Hex (6);
         AB, BA : Shared_Secret;
         C1, C2 : Boolean;
      begin
         N_DH := N_DH + 1;
         X25519 (A_SK, B_PK, AB, C1);
         X25519 (B_SK, A_PK, BA, C2);
         if X25519_Public (A_SK) /= A_PK or else X25519_Public (B_SK) /= B_PK
           or else AB /= Want or else BA /= Want
           or else not C1 or else not C2
         then
            Fail (Ok_DH, "x25519 dh");
         end if;
      end Do_DH;

      procedure Do_Aead is
         Key   : constant AEAD_Key   := Hex (2);
         N     : constant Nonce      := Hex (3);
         AD    : constant Byte_Array := Hex (4);
         Plain : constant Byte_Array := Hex (5);
         Want  : constant Byte_Array := Hex (6);
         WMac  : constant Tag        := Hex (7);
         C     : Byte_Array (0 .. Plain'Length - 1);
         P     : Byte_Array (0 .. Plain'Length - 1);
         Mac   : Tag;
         Auth  : Boolean;

         function Rejects
           (K : AEAD_Key; NN : Nonce; A : Byte_Array; CC : Byte_Array; M : Tag)
            return Boolean
         is
            Out_P : Byte_Array (0 .. CC'Length - 1) := [others => 16#AA#];
            Au    : Boolean;
         begin
            Unlock (K, NN, A, CC, M, Out_P, Au);
            return not Au and then (for all X of Out_P => X = 0);
         end Rejects;
      begin
         N_AE := N_AE + 1;
         Lock (Key, N, AD, Plain, C, Mac);
         if C /= Want or else Mac /= WMac then
            Fail (Ok_AE, "aead lock");
         end if;
         Unlock (Key, N, AD, Want, WMac, P, Auth);
         if not Auth or else P /= Plain then
            Fail (Ok_AE, "aead unlock");
         end if;
         --  Tamper checks: mac, ciphertext, ad, nonce, key, truncation.
         declare
            M2 : Tag := WMac;
            K2 : AEAD_Key := Key;
            N2 : Nonce := N;
         begin
            M2 (15) := M2 (15) xor 1;
            K2 (0) := K2 (0) xor 1;
            N2 (23) := N2 (23) xor 1;
            if not Rejects (Key, N, AD, Want, M2)
              or else not Rejects (K2, N, AD, Want, WMac)
              or else not Rejects (Key, N2, AD, Want, WMac)
              or else not Rejects (Key, N, AD & Byte (0), Want, WMac)
            then
               Fail (Ok_AE_Tamper, "aead mac/key/nonce/ad");
            end if;
         end;
         if Want'Length > 0 then
            declare
               C2 : Byte_Array := Want;
            begin
               C2 (C2'First) := C2 (C2'First) xor 1;
               if not Rejects (Key, N, AD, C2, WMac)
                 or else not Rejects (Key, N, AD, Want (Want'First .. Want'Last - 1), WMac)
               then
                  Fail (Ok_AE_Tamper, "aead cipher");
               end if;
            end;
         end if;
         if AD'Length > 0 then
            declare
               A2 : Byte_Array := AD;
            begin
               A2 (A2'Last) := A2 (A2'Last) xor 1;
               if not Rejects (Key, N, A2, Want, WMac) then
                  Fail (Ok_AE_Tamper, "aead ad flip");
               end if;
            end;
         end if;
      end Do_Aead;

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
            declare
               Kind : constant String := Field (1);
            begin
               if Kind = "blake2b256" and then N_Fields = 3 then
                  Do_Blake2b;
               elsif Kind = "ed25519" and then N_Fields = 5 then
                  Do_Ed25519;
               elsif Kind = "wycheproof" and then N_Fields = 6 then
                  Do_Wycheproof;
               elsif Kind = "ed25519_strict" and then N_Fields = 5 then
                  Do_Strict;
               elsif Kind = "b2eddsa_old" and then N_Fields = 5 then
                  Do_Old;
               elsif Kind = "b2eddsa_old_pk" and then N_Fields = 3 then
                  Do_Old_Pk;
               elsif Kind = "x25519_low" and then N_Fields = 2 then
                  Do_Low_Order;
               elsif Kind = "dh_key" and then N_Fields = 4 then
                  Do_DH_Key;
               elsif Kind = "x25519" and then N_Fields = 4 then
                  Do_X25519;
               elsif Kind = "x25519dh" and then N_Fields = 6 then
                  Do_DH;
               elsif Kind = "aead" and then N_Fields = 7 then
                  Do_Aead;
               else
                  Check ("vector_line_parses (" & Kind & ")", False);
               end if;
            end;
         end if;
      end loop;
      Close (F);
      Check ("blake2b256_vectors" & N_B2'Image, Ok_B2 and then N_B2 >= 2);
      Check ("blake2b256_incremental_every_split", Ok_B2_Inc and then N_B2 >= 2);
      Check ("ed25519_rfc8032_vectors" & N_Ed'Image, Ok_Ed and then N_Ed = 3);
      Check ("ed25519_tampered_rejected", Ok_Ed_Tamper and then N_Ed = 3);
      Check ("wycheproof_valid_accepted" & N_Wp_Valid'Image,
             Ok_Wp and then N_Wp_Valid >= 12);
      Check ("wycheproof_invalid_rejected" & N_Wp_Invalid'Image,
             Ok_Wp and then N_Wp_Invalid >= 14);
      Check ("wycheproof_s_at_least_l_rejected",
             Ok_Wp and then Seen_S_Over_L);
      Check ("wycheproof_tc151_noncanonical_r_rejected",
             Ok_Wp and then Seen_151);
      Check ("wycheproof_wrong_length_not_a_sig" & N_Wp_Length'Image,
             Ok_Wp and then N_Wp_Length >= 5);
      Check ("ed25519_noncanonical_encodings_rejected" & N_Strict_Invalid'Image,
             Ok_Strict and then N_Strict_Invalid >= 6 and then N_Strict_Valid >= 3);
      Check ("b2eddsa_old_signatures_rejected" & N_Old'Image,
             Ok_Old and then N_Old = 3);
      Check ("b2eddsa_old_public_keys_not_derived" & N_Old_Pk'Image,
             Ok_Old_Pk and then N_Old_Pk >= 5);
      Check ("x25519_rfc7748_vectors" & N_X'Image, Ok_X and then N_X >= 1);
      Check ("x25519_low_order_not_contributory" & N_Low'Image,
             Ok_Low and then N_Low >= 5);
      Check ("x25519_rfc7748_dh", Ok_DH and then N_DH >= 1);
      Check ("dh_key_reduced_low_order_answers" & N_Key'Image,
             Ok_Key and then N_Key >= 13);
      Check ("aead_vectors" & N_AE'Image, Ok_AE and then N_AE >= 1);
      Check ("aead_tampered_rejected", Ok_AE_Tamper and then N_AE >= 1);
   end Vectors;

   ---------------------------------------------------------------------------
   --  Round trips and properties
   ---------------------------------------------------------------------------

   type Natural_List is array (Positive range <>) of Natural;
   Sign_Lengths : constant Natural_List :=
     [0, 1, 31, 32, 33, 127, 128, 129, 1000, 65_535 + 100];
   AEAD_Lengths : constant Natural_List :=
     [0, 1, 15, 16, 17, 63, 64, 65, 1000, 65_535];
   AD_Lengths   : constant Natural_List := [0, 1, 16, 33];

   procedure Round_Trips is
      Ok : Boolean;
   begin
      --  Sign then verify, with messages of many lengths and several keys.
      --  The signature is canonical (the Post of Sign) and deterministic.
      Ok := True;
      for K in 0 .. 3 loop
         declare
            SK : Secret_Key;
            PK : Pubkey;
         begin
            Key_Pair (Pattern (Seed_Len, 17, K * 31 + 1), SK, PK);
            for L of Sign_Lengths loop
               declare
                  M : constant Byte_Array := Pattern (L, 7, K);
                  S : constant Sig := Sign (SK, M);
               begin
                  if not Verify (S, PK, M) or else Sign (SK, M) /= S
                    or else not S_Below_L (S)
                  then
                     Ok := False;
                  end if;
               end;
            end loop;
         end;
      end loop;
      Check ("ed25519_sign_then_verify", Ok);

      --  A message signed by one key does not verify under another.
      declare
         SK1, SK2 : Secret_Key;
         PK1, PK2 : Pubkey;
         M : constant Byte_Array := Ascii ("kome record");
      begin
         Key_Pair (Pattern (Seed_Len, 3, 1), SK1, PK1);
         Key_Pair (Pattern (Seed_Len, 3, 2), SK2, PK2);
         Check ("ed25519_wrong_key_rejected",
                PK1 /= PK2 and then not Verify (Sign (SK1, M), PK2, M)
                and then Verify (Sign (SK2, M), PK2, M));
      end;

      --  Non-malleability: S + L encodes the same scalar mod L and is a
      --  mathematically valid signature. But Verify refuses it (the Post of
      --  Verify: True implies S < L).
      declare
         SK    : Secret_Key;
         PK    : Pubkey;
         M     : constant Byte_Array := Ascii ("malleable?");
         S, T  : Sig;
         Carry : Natural := 0;
      begin
         Key_Pair (Pattern (Seed_Len, 5, 9), SK, PK);
         S := Sign (SK, M);
         T := S;
         for I in 0 .. 31 loop
            declare
               V : constant Natural :=
                 Natural (S (32 + I)) + Natural (L_LE (I)) + Carry;
            begin
               T (32 + I) := Byte (V mod 256);
               Carry := V / 256;
            end;
         end loop;
         Check ("ed25519_s_plus_l_rejected",
                Carry = 0 and then Verify (S, PK, M)
                and then not S_Below_L (T) and then not Verify (T, PK, M));
      end;

      --  S_Below_L at its boundary: 0 and L - 1 are below; L, L + 1 and
      --  2**256 - 1 are not. Also, a difference only in the top byte or only
      --  in the low byte.
      declare
         function With_S (Scalar : Byte_Array) return Sig is
           ([for I in Sig'Range =>
               (if I < 32 then 16#77# else Scalar (Scalar'First + I - 32))]);
         L_Minus_1 : Byte_Array := L_LE;
         L_Plus_1  : Byte_Array := L_LE;
         Top_Over  : Byte_Array := L_LE;
         Mid_Under : Byte_Array := L_LE;
      begin
         L_Minus_1 (0) := L_Minus_1 (0) - 1;
         L_Plus_1 (0)  := L_Plus_1 (0) + 1;
         Top_Over (31) := 16#11#;
         Top_Over (0)  := 0;
         Mid_Under (20) := 0;
         Mid_Under (15) := 16#13#;
         Mid_Under (0)  := 16#FF#;
         Check ("s_below_l_boundaries",
                S_Below_L (With_S ([0 .. 31 => 0]))
                and then S_Below_L (With_S (L_Minus_1))
                and then not S_Below_L (With_S (L_LE))
                and then not S_Below_L (With_S (L_Plus_1))
                and then not S_Below_L (With_S ([0 .. 31 => 16#FF#]))
                and then not S_Below_L (With_S (Top_Over))
                and then S_Below_L (With_S (Mid_Under)));
      end;

      --  Is_Canonical_Point at its boundaries (RFC 8032 §5.1.3): y = p - 1
      --  and y = 1 are canonical only with the sign bit clear. y = 0 with the
      --  sign bit set is canonical (x /= 0 there). y >= p is never canonical.
      declare
         function Enc (Hex_Str : String) return Pubkey is (From_Hex (Hex_Str));
         P_Minus_1   : constant Pubkey := Enc
           ("ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f");
         P_Minus_1_S : constant Pubkey := Enc
           ("ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff");
         P_Minus_2_S : constant Pubkey := Enc
           ("ebffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff");
         P_Enc       : constant Pubkey := Enc
           ("edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f");
         P_Enc_S     : constant Pubkey := Enc
           ("edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff");
         Max_Enc     : constant Pubkey := [others => 16#FF#];
         One         : constant Pubkey := Enc
           ("0100000000000000000000000000000000000000000000000000000000000000");
         One_S       : constant Pubkey := Enc
           ("0100000000000000000000000000000000000000000000000000000000000080");
         Zero_S      : constant Pubkey := Enc
           ("0000000000000000000000000000000000000000000000000000000000000080");
         Two_S       : constant Pubkey := Enc
           ("0200000000000000000000000000000000000000000000000000000000000080");
         Ok_Keys     : Boolean := True;
      begin
         for K in 0 .. 15 loop
            if not Is_Canonical_Point (Derive_Public (Pattern (Seed_Len, 23, K)))
            then
               Ok_Keys := False;
            end if;
         end loop;
         Check ("canonical_point_boundaries",
                Is_Canonical_Point (P_Minus_1)
                and then not Is_Canonical_Point (P_Minus_1_S)
                and then Is_Canonical_Point (P_Minus_2_S)
                and then not Is_Canonical_Point (P_Enc)
                and then not Is_Canonical_Point (P_Enc_S)
                and then not Is_Canonical_Point (Max_Enc)
                and then Is_Canonical_Point (One)
                and then not Is_Canonical_Point (One_S)
                and then Is_Canonical_Point (Zero_S)
                and then Is_Canonical_Point (Two_S)
                and then Ok_Keys);
         --  Is_Reduced_U on p and p + 1 (not reduced), p - 1 (reduced).
         Check ("is_reduced_u_p_and_p_plus_1",
                not Is_Reduced_U (P_Enc)
                and then not Is_Reduced_U (Enc
                  ("eeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f"))
                and then Is_Reduced_U (P_Minus_1)
                and then not Is_Reduced_U (Max_Enc));
      end;

      --  Is_Low_Order_U is false, and Is_Good_DH_Key is true, for the public
      --  key of each of 64 random secrets. The generator seed is fixed, so
      --  the run is reproducible.
      declare
         package Random_Byte is new Ada.Numerics.Discrete_Random (Byte);
         G      : Random_Byte.Generator;
         Secret : DH_Secret;
         Ok_R   : Boolean := True;
      begin
         Random_Byte.Reset (G, 2026);
         for K in 1 .. 64 loop
            for I in Secret'Range loop
               Secret (I) := Random_Byte.Random (G);
            end loop;
            declare
               U : constant Pubkey := X25519_Public (Secret);
            begin
               if Is_Low_Order_U (U) or else not Is_Reduced_U (U)
                 or else not Is_Good_DH_Key (U)
               then
                  Ok_R := False;
               end if;
            end;
         end loop;
         Wipe (Secret);
         Check ("x25519_public_of_random_secret_not_low_order", Ok_R);
      end;

      --  X25519: both sides of a fresh exchange agree, and different peers
      --  give different results.
      declare
         A : constant DH_Secret := Pattern (DH_Key_Len, 9, 1);
         B : constant DH_Secret := Pattern (DH_Key_Len, 11, 2);
         C : constant DH_Secret := Pattern (DH_Key_Len, 13, 3);
         AB, BA, AC : Shared_Secret;
         C1, C2, C3 : Boolean;
      begin
         X25519 (A, X25519_Public (B), AB, C1);
         X25519 (B, X25519_Public (A), BA, C2);
         X25519 (A, X25519_Public (C), AC, C3);
         Check ("x25519_exchange_agrees",
                AB = BA and then AB /= AC and then C1 and then C2 and then C3
                and then not Is_Zero (AB));
         --  The Post of X25519 (checked here under -gnata) says that the
         --  procedure computes the ghost function X25519_Shared. Restate it
         --  for both directions of the exchange.
         pragma Assert (AB = X25519_Shared (A, X25519_Public (B)));
         pragma Assert (BA = X25519_Shared (B, X25519_Public (A)));
         pragma Assert (X25519_Shared (A, X25519_Public (B))
                        = X25519_Shared (B, X25519_Public (A)));
         Check ("x25519_shared_function_matches_procedure", not Is_Zero (AB));
         Wipe (AB);
         Wipe (BA);
         Wipe (AC);
      end;

      --  AEAD round trips at many lengths (the block size of ChaCha20 is 64,
      --  and Poly1305 pads to 16), with and without AD. Also the DESIGN.md §2
      --  Box shape (a sealed 32-byte key: 32 + 16 = Box_Len bytes).
      Ok := True;
      for L of AEAD_Lengths loop
         for LA of AD_Lengths loop
            declare
               Key : constant AEAD_Key   := Pattern (AEAD_Key_Len, 3, L);
               N   : constant Nonce      := Pattern (Nonce_Len, 5, LA);
               AD  : constant Byte_Array := Pattern (LA, 1, 2);
               P   : constant Byte_Array := Pattern (L, 7, 3);
               C   : Byte_Array (100 .. 99 + L);
               Q   : Byte_Array (0 .. L - 1);
               Mac : Tag;
               Au  : Boolean;
            begin
               Lock (Key, N, AD, P, C, Mac);
               Unlock (Key, N, AD, C, Mac, Q, Au);
               if not Au or else Q /= P or else (L > 16 and then C = P) then
                  Ok := False;
               end if;
               if L > 0 then
                  C (C'Last) := C (C'Last) xor 16#40#;
                  Unlock (Key, N, AD, C, Mac, Q, Au);
                  if Au or else (for some X of Q => X /= 0) then
                     Ok := False;
                  end if;
               end if;
            end;
         end loop;
      end loop;
      Check ("aead_lock_unlock_round_trip_and_tamper", Ok);

      declare
         Epoch_Key : constant AEAD_Key := Pattern (AEAD_Key_Len, 29, 4);
         Wrap_Key  : constant AEAD_Key := Pattern (AEAD_Key_Len, 23, 8);
         N         : constant Nonce := Pattern (Nonce_Len, 1, 0);
         Sealed    : Box;
         Back      : AEAD_Key;
         Au        : Boolean;
      begin
         Lock (Wrap_Key, N, [1 .. 0 => 0], Epoch_Key,
               Sealed (0 .. AEAD_Key_Len - 1),
               Sealed (AEAD_Key_Len .. Box_Len - 1));
         Unlock (Wrap_Key, N, [1 .. 0 => 0], Sealed (0 .. AEAD_Key_Len - 1),
                 Sealed (AEAD_Key_Len .. Box_Len - 1), Back, Au);
         Check ("aead_box_shape", Au and then Back = Epoch_Key);
      end;

      --  Lemma_Blake2b_Congruent is an axiom for the prover. Under -gnata
      --  its Pre and Post run. Thus this test checks it on inputs with equal
      --  bytes and different bounds (a slid copy, and two interior slices).
      declare
         Src     : constant Byte_Array := Pattern (300, 7, 1);
         Shifted : constant Byte_Array (1000 .. 1299) := Src;
      begin
         Lemma_Blake2b_Congruent (Src, Shifted);
         Lemma_Blake2b_Congruent (Src (10 .. 109), Shifted (1010 .. 1109));
         Lemma_Blake2b_Congruent (Src (0 .. -1), Shifted (1300 .. 1299));
         Check ("blake2b256_congruent_across_bounds",
                Src'First = 0
                and then Blake2b_256 (Src) = Blake2b_256 (Shifted)
                and then Blake2b_256 (Src (10 .. 109)) = Blake2b_256 (Shifted (1010 .. 1109))
                and then Blake2b_256 (Src (10 .. 109)) /= Blake2b_256 (Src (11 .. 110)));
      end;
   end Round_Trips;

   ---------------------------------------------------------------------------
   --  Contracts: refusals by precondition, Wipe, the context state machine
   ---------------------------------------------------------------------------

   procedure Contracts is
      Ctx : Blake2b_Context;
      D   : Hash256;
      K   : constant AEAD_Key := [others => 1];
      N   : constant Nonce := [others => 2];
      P   : constant Byte_Array (0 .. 9) := [others => 3];
      C9  : Byte_Array (0 .. 8);
      Mac : Tag;
      Au  : Boolean;

      procedure Update_Inactive is
         Fresh : Blake2b_Context;
      begin
         Update (Fresh, P);
      end Update_Inactive;
      procedure Final_Inactive is
         Fresh : Blake2b_Context;
      begin
         Final (Fresh, D);
      end Final_Inactive;
      procedure Update_After_Final is
         C2 : Blake2b_Context;
      begin
         Init (C2);
         Final (C2, D);
         Update (C2, P);
      end Update_After_Final;
      procedure Lock_Short is
      begin
         Lock (K, N, P, P, C9, Mac);
      end Lock_Short;
      procedure Unlock_Short is
      begin
         Unlock (K, N, P, P, Mac, C9, Au);
      end Unlock_Short;

      procedure Sign_Default_Key is
         Fresh : Secret_Key;
      begin
         Sink_Sig := Sign (Fresh, P);
      end Sign_Default_Key;
      procedure Sign_After_Wipe is
         SK : Secret_Key;
         PK : Pubkey;
      begin
         Key_Pair ([others => 7], SK, PK);
         Sink_Sig := Sign (SK, P);
         Wipe (SK);
         Sink_Sig := Sign (SK, P);
      end Sign_After_Wipe;
      procedure Update_After_Wipe is
         C2 : Blake2b_Context;
      begin
         Init (C2);
         Update (C2, P);
         Wipe (C2);
         Update (C2, P);
      end Update_After_Wipe;
      procedure Hash_Too_Long is
         Big : constant Byte_Array (0 .. Max_Data_Len) := [others => 1];
      begin
         Sink_Hash := Blake2b_256 (Big);
      end Hash_Too_Long;

      function R1 is new Refused (Update_Inactive);
      function R2 is new Refused (Final_Inactive);
      function R3 is new Refused (Update_After_Final);
      function R4 is new Refused (Lock_Short);
      function R5 is new Refused (Unlock_Short);
      function R6 is new Refused (Sign_Default_Key);
      function R7 is new Refused (Sign_After_Wipe);
      function R8 is new Refused (Update_After_Wipe);
      function R9 is new Refused (Hash_Too_Long);
   begin
      Check ("context_default_inactive",
             not Is_Active (Ctx) and then Absorbed (Ctx) = 0);
      Check ("update_inactive_refused", R1);
      Check ("final_inactive_refused", R2);
      Check ("update_after_final_refused", R3);
      Check ("lock_length_mismatch_refused", R4);
      Check ("unlock_length_mismatch_refused", R5);
      Check ("sign_default_key_refused", R6);
      Check ("sign_after_wipe_refused", R7);
      Check ("update_after_wipe_refused", R8);
      Check ("hash_over_max_data_len_refused", R9);

      --  Blake2b_256 accepts the largest buffer that the bound admits, and
      --  the one-shot, procedure and incremental forms agree on it.
      declare
         Big  : constant Byte_Array (0 .. Max_Data_Len - 1) :=
           Pattern (Max_Data_Len, 13, 7);
         D1, D2 : Hash256;
      begin
         Blake2b_256 (Big, D1);
         D2 := Chunked (Big, 65_536);
         Check ("blake2b256_max_data_len", D1 = Blake2b_256 (Big) and then D1 = D2);
      end;

      --  The procedure form of the one-shot hash (its Post is the function).
      declare
         D1 : Hash256;
      begin
         Blake2b_256 (Ascii ("abc"), D1);
         Check ("blake2b256_procedure_form", D1 = B2_Abc);
      end;

      --  A key pair is valid and consistent. A default key is not valid
      --  (its DIC, also checked at its declaration under -gnata). Wipe sets
      --  both halves to zero and makes the key invalid. Is_Valid and Seed_Of
      --  are ghost, so the test asserts them.
      declare
         Fresh, SK : Secret_Key;
         PK        : Pubkey;
         S         : constant Seed := Pattern (Seed_Len, 19, 3);
         procedure Fresh_Invalid is
         begin
            pragma Assert (not Is_Valid (Fresh));
            pragma Assert (for all B of Seed_Of (Fresh) => B = 0);
         end Fresh_Invalid;
         procedure Made_Valid is
         begin
            pragma Assert (Is_Valid (SK));
            pragma Assert (Seed_Of (SK) = S);
         end Made_Valid;
         procedure Wiped is
         begin
            pragma Assert (not Is_Valid (SK));
            pragma Assert (for all B of Seed_Of (SK) => B = 0);
         end Wiped;
         function Fresh_Invalid_Holds is new Holds (Fresh_Invalid);
         function Made_Valid_Holds is new Holds (Made_Valid);
         function Wiped_Holds is new Holds (Wiped);
      begin
         Check ("secret_key_default_not_valid", Fresh_Invalid_Holds);
         Key_Pair (S, SK, PK);
         Check ("key_pair_valid_and_derived",
                Made_Valid_Holds
                and then Public_Of (SK) = Derive_Public (S)
                and then Derive_Public (S) = PK);
         Wipe (SK);
         Check ("wipe_secret_key",
                Wiped_Holds
                and then (for all B of Public_Of (SK) => B = 0));
      end;

      --  Default-initialized contexts satisfy their DIC (checked at each
      --  declaration under -gnata, and here explicitly).
      declare
         C4, C5 : Blake2b_Context;
      begin
         Check ("context_default_initial_condition",
                not Is_Active (C4) and then Absorbed (C4) = 0
                and then not Is_Active (C5) and then Absorbed (C5) = 0);
      end;

      --  Wipe discards a context in the middle of a stream. After that, Init
      --  starts a new stream.
      declare
         C3 : Blake2b_Context;
      begin
         Init (C3);
         Update (C3, Ascii ("secret epoch key material"));
         Wipe (C3);
         Check ("wipe_context_inactive",
                not Is_Active (C3) and then Absorbed (C3) = 0);
         Wipe (C3);   --  idempotent on an inactive context
         Init (C3);
         Update (C3, Ascii ("abc"));
         Final (C3, D);
         Check ("init_after_wipe", D = B2_Abc);
      end;

      --  A new Init after Final starts a new stream.
      Init (Ctx);
      Update (Ctx, Ascii ("xyz"));
      Final (Ctx, D);
      Init (Ctx);
      Update (Ctx, Ascii ("abc"));
      Final (Ctx, D);
      Check ("reinit_after_final", D = B2_Abc);

      declare
         Secret : Byte_Array (5 .. 70) := [others => 16#5A#];
         None   : Byte_Array (1 .. 0);
      begin
         Wipe (Secret);
         Wipe (None);
         Check ("wipe_zeroes", (for all X of Secret => X = 0));
      end;
   end Contracts;

begin
   Named_Answers;
   Vectors;
   Round_Trips;
   Contracts;
   if Failed then
      Set_Exit_Status (Failure);
   end if;
end Test_Crypto;
