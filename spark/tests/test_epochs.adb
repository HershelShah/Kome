--  Test main for Kome.Epochs (DESIGN.md §6). (a) The chain: Derive against
--  vectors/epochs.txt, computed independently with Python's hashlib.blake2b
--  (digest_size=32), including the full 2**16 - 1 step walk; Step is one
--  link. (b) The chain algebra: the ghost lemmas executed under -gnata on
--  real keys (identity, one step, composition, shift, Iter_Add). (c) Boxes
--  through Kome.Crypto: round trip, the member derives older keys from the
--  boxed one, and refusals (wrong member, wrong root key, wrong nonce, wrong
--  epoch, wrong collection, tampered cipher or tag, low-order peers u = 0,
--  u = 1, both order-8 points and u = p - 1, non-reduced peer encodings:
--  bit 255 set and u >= p) each leave zeros.
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
   --  (a) Chain against the hashlib reference
   ---------------------------------------------------------------------------

   procedure Chain_Vectors is
      Path : constant String := Find ("vectors/epochs.txt");
      F    : File_Type;
      Line : String (1 .. 512);
      Last : Natural;

      type Bounds is record
         First, Last : Natural;
      end record;
      Fields   : array (1 .. 6) of Bounds;
      N_Fields : Natural;
      N_Chain  : Natural := 0;
      Ok       : Boolean := True;
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
            else
               Check ("vector_line_parses (" & Field (1) & ")", False);
            end if;
         end if;
      end loop;
      Close (F);
      Check ("chain_matches_hashlib (" & N_Chain'Image & " vectors)",
             Ok and then N_Chain >= 10);
      Check ("chain_full_walk_65535_to_0_present", Full);
   end Chain_Vectors;

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
      --  BLAKE2b; a false law would raise Assertion_Error.
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

      --  The same laws checked directly over longer walks, where running
      --  the ghost model would be slow.
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

   procedure Boxes is
      use Kome.Crypto;
      Root_SK   : constant DH_Secret := Pattern (DH_Key_Len, 7, 3);
      Member_SK : constant DH_Secret := Pattern (DH_Key_Len, 13, 101);
      Other_SK  : constant DH_Secret := Pattern (DH_Key_Len, 31, 9);
      Root_PK   : constant Pubkey := X25519_Public (Root_SK);
      Member_PK : constant Pubkey := X25519_Public (Member_SK);
      Other_PK  : constant Pubkey := X25519_Public (Other_SK);
      N1        : constant Nonce := Pattern (Nonce_Len, 5, 1);
      N2        : constant Nonce := Pattern (Nonce_Len, 5, 2);
      NS1       : constant Id128 := (16#6B6F6D65#, 1, 2, 3);
      NS2       : constant Id128 := (16#6B6F6D65#, 1, 2, 4);

      Top   : constant Epoch := 50_000;
      E     : constant Epoch := 1_234;
      K_Top : constant Key256 := Other_Key;
      K_E   : constant Key256 := Derive (K_Top, Top, E);

      Sealed, Sealed2, Bad : Kome.Box;
      St, St2              : Box_Status;
      Got                  : Key256;
   begin
      Box_Key (Root_SK, Member_PK, NS1, E, K_E, N1, Sealed, St);
      Check ("box_ok", St = Box_OK and then not Is_Zero_Box (Sealed));
      Check ("box_layout_cipher_tag",
             Cipher_Of (Sealed) = Sealed (0 .. 31)
             and then Tag_Of (Sealed) = Sealed (32 .. 47)
             and then Cipher_Of (Sealed) & Tag_Of (Sealed) = Sealed);
      Check ("box_hides_key",
             Cipher_Of (Sealed) /= Kome.Keys.To_Bytes (K_E));

      Unbox_Key (Member_SK, Root_PK, NS1, E, N1, Sealed, Got, St);
      Check ("unbox_round_trip", St = Box_OK and then Got = K_E);

      --  The member derives every older key from its one box (§6).
      Check ("member_derives_history",
             Derive (Got, E, 0) = Derive (K_Top, Top, 0)
             and then Derive (Got, E, 17) = Derive (K_Top, Top, 17));

      --  Deterministic given the nonce; a fresh nonce gives a fresh box.
      Box_Key (Root_SK, Member_PK, NS1, E, K_E, N1, Sealed2, St2);
      Check ("box_deterministic_in_nonce", St2 = Box_OK and then Sealed2 = Sealed);
      Box_Key (Root_SK, Member_PK, NS1, E, K_E, N2, Sealed2, St2);
      Check ("box_fresh_nonce_differs", St2 = Box_OK and then Sealed2 /= Sealed);
      Unbox_Key (Member_SK, Root_PK, NS1, E, N2, Sealed2, Got, St);
      Check ("unbox_round_trip_second_nonce", St = Box_OK and then Got = K_E);

      --  A box to another member differs and opens only for that member.
      Box_Key (Root_SK, Other_PK, NS1, E, K_E, N1, Sealed2, St2);
      Check ("box_per_member", St2 = Box_OK and then Sealed2 /= Sealed);
      Unbox_Key (Other_SK, Root_PK, NS1, E, N1, Sealed2, Got, St);
      Check ("unbox_other_member", St = Box_OK and then Got = K_E);

      --  Wrong keys fail and leave the zero key.
      Unbox_Key (Other_SK, Root_PK, NS1, E, N1, Sealed, Got, St);
      Check ("unbox_wrong_member_fails",
             St = Not_Authentic and then Got = Zero_Key);
      Unbox_Key (Member_SK, Other_PK, NS1, E, N1, Sealed, Got, St);
      Check ("unbox_wrong_root_fails",
             St = Not_Authentic and then Got = Zero_Key);
      Unbox_Key (Member_SK, Root_PK, NS1, E, N2, Sealed, Got, St);
      Check ("unbox_wrong_nonce_fails",
             St = Not_Authentic and then Got = Zero_Key);
      Unbox_Key (Member_SK, Root_PK, NS1, E + 1, N1, Sealed, Got, St);
      Check ("unbox_wrong_epoch_fails",
             St = Not_Authentic and then Got = Zero_Key);
      --  AD = ns ‖ epoch: the same root and member keys in another
      --  collection do not open it.
      Unbox_Key (Member_SK, Root_PK, NS2, E, N1, Sealed, Got, St);
      Check ("unbox_wrong_ns_fails",
             St = Not_Authentic and then Got = Zero_Key);

      declare
         Ok : Boolean := True;
      begin
         for I in Sealed'Range loop
            Bad := Sealed;
            Bad (I) := Bad (I) xor 16#01#;
            Unbox_Key (Member_SK, Root_PK, NS1, E, N1, Bad, Got, St);
            if St /= Not_Authentic or else Got /= Zero_Key then
               Ok := False;
            end if;
         end loop;
         Check ("unbox_tamper_every_byte_fails", Ok);
      end;

      --  Low-order peers, all reduced encodings (so the refusal is the
      --  exchange's, not the encoding's): u = 0, u = 1, the two points of
      --  order 8 (libsodium's blocklist, cf. RFC 7748 §6.1) and u = p - 1
      --  (order 2). Each makes every exchange all zeros (checked
      --  independently with an RFC 7748 ladder in Python).
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
            Ok_Red := Ok_Red and then Is_Reduced_U (U);
            Box_Key (Root_SK, U, NS1, E, K_E, N1, Bad, St);
            if St /= Low_Order_Peer or else not Is_Zero_Box (Bad) then
               Ok_Box := False;
            end if;
            Unbox_Key (Member_SK, U, NS1, E, N1, Sealed, Got, St);
            if St /= Low_Order_Peer or else Got /= Zero_Key then
               Ok_Unbox := False;
            end if;
         end loop;
         Check ("low_order_points_are_reduced", Ok_Red);
         Check ("box_low_order_refused (u=0, u=1, order 8 x2, p-1)", Ok_Box);
         Check ("unbox_low_order_root_refused (u=0, u=1, order 8 x2, p-1)",
                Ok_Unbox);
      end;

      --  Non-reduced encodings. Member_PK with bit 255 set is the same
      --  point (X25519 ignores the bit) and gives the same shared secret,
      --  but the wrap key hashes the bytes, so a box sealed to it would
      --  never open for the member. It is refused, as is any u >= p.
      declare
         Hi_Member : Pubkey := Member_PK;
         Hi_Root   : Pubkey := Root_PK;
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
         Hi_Root (31) := Hi_Root (31) or 16#80#;
         Check ("is_reduced_u_boundaries",
                Is_Reduced_U (Member_PK) and then Is_Reduced_U (Root_PK)
                and then Is_Reduced_U (P1_Enc) and then Is_Reduced_U (Mid_Enc)
                and then not Is_Reduced_U (P_Enc)
                and then not Is_Reduced_U (P2_Enc)
                and then not Is_Reduced_U (Max_Enc)
                and then not Is_Reduced_U (Hi_Member));

         Box_Key (Root_SK, Hi_Member, NS1, E, K_E, N1, Bad, St);
         Check ("box_member_bit255_refused",
                St = Non_Canonical_Peer and then Is_Zero_Box (Bad));
         Box_Key (Root_SK, P2_Enc, NS1, E, K_E, N1, Bad, St);
         Check ("box_member_u_ge_p_refused",
                St = Non_Canonical_Peer and then Is_Zero_Box (Bad));
         Box_Key (Root_SK, P_Enc, NS1, E, K_E, N1, Bad, St);
         Check ("box_member_u_eq_p_refused_as_non_canonical",
                St = Non_Canonical_Peer and then Is_Zero_Box (Bad));
         Unbox_Key (Member_SK, Hi_Root, NS1, E, N1, Sealed, Got, St);
         Check ("unbox_root_bit255_refused",
                St = Non_Canonical_Peer and then Got = Zero_Key);
         Unbox_Key (Member_SK, P2_Enc, NS1, E, N1, Sealed, Got, St);
         Check ("unbox_root_u_ge_p_refused",
                St = Non_Canonical_Peer and then Got = Zero_Key);
         --  What Box_Key accepts is what Unbox_Key hashes: the member's own
         --  public key is the reduced encoding.
         Check ("x25519_public_is_reduced",
                Is_Reduced_U (X25519_Public (Member_SK))
                and then Is_Reduced_U (X25519_Public (Other_SK))
                and then Is_Reduced_U (X25519_Public (Root_SK)));
      end;

      --  Edge epochs.
      Box_Key (Root_SK, Member_PK, NS1, Epoch'Last, K_Top, N1, Sealed2, St2);
      Unbox_Key (Member_SK, Root_PK, NS1, Epoch'Last, N1, Sealed2, Got, St);
      Check ("box_round_trip_top_epoch",
             St2 = Box_OK and then St = Box_OK and then Got = K_Top);
      Box_Key (Root_SK, Member_PK, NS1, 0, Zero_Key, N1, Sealed2, St2);
      Unbox_Key (Member_SK, Root_PK, NS1, 0, N1, Sealed2, Got, St);
      Check ("box_round_trip_zero_key_epoch_0",
             St2 = Box_OK and then St = Box_OK and then Got = Zero_Key);
   end Boxes;

begin
   Chain_Vectors;
   Algebra;
   Boxes;
   if Failed then
      Set_Exit_Status (Failure);
   end if;
end Test_Epochs;
