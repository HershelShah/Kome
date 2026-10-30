--  Test main for Kome.SHA256. Contract corner cases, the ghost laws run at
--  run time (-gnata evaluates their postconditions), and the differential
--  vectors in vectors/sha256.txt produced by vectors/gen/sha256_gen.cpp.
pragma Ada_2022;
with Ada.Assertions;
with Ada.Command_Line;   use Ada.Command_Line;
with Ada.Text_IO;        use Ada.Text_IO;
with Ada.Directories;
with Ada.Strings.Fixed;
with Kome;               use Kome;
with Kome.SHA256;        use Kome.SHA256;

procedure Test_SHA256 with SPARK_Mode => Off is

   Failed : Boolean := False;

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

   --  "-" denotes the empty byte string (the generator's convention).
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

   function To_Hex (B : Byte_Array) return String is
      Digits_Lc : constant String := "0123456789abcdef";
      R : String (1 .. 2 * B'Length);
      J : Positive := 1;
   begin
      for I in B'Range loop
         R (J)     := Digits_Lc (Natural (B (I) / 16) + 1);
         R (J + 1) := Digits_Lc (Natural (B (I) mod 16) + 1);
         J := J + 2;
      end loop;
      return R;
   end To_Hex;

   function Ascii (S : String) return Byte_Array is
      R : Byte_Array (0 .. S'Length - 1);
   begin
      for I in R'Range loop
         R (I) := Character'Pos (S (S'First + I));
      end loop;
      return R;
   end Ascii;

   ---------------------------------------------------------------------------
   --  Contract corner cases
   ---------------------------------------------------------------------------

   NIST_Empty : constant String :=
     "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855";
   NIST_Abc : constant String :=
     "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad";
   NIST_Two_Block : constant String :=
     "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1";

   --  Identity on U64 that is not static, so the checks below are evaluated
   --  rather than folded (and flagged) by the compiler.
   function V (X : U64) return U64 is (X);

   procedure Corner_Cases is
      Ctx     : Context;
      D       : Hash256;
      Refused : Boolean;
   begin
      --  Default initialization equals Initial equals Reset.
      Check ("default_is_initial", Ctx = Initial);
      Check ("initial_count_zero",
             Byte_Count (Initial) = 0 and then not Is_Finished (Initial));
      Update (Ctx, Ascii ("abc"));
      Reset (Ctx);
      Check ("reset_is_initial", Ctx = Initial);

      --  Empty message: digest of the IV through padding only.
      Finish (Ctx, D);
      Check ("empty_digest", To_Hex (D) = NIST_Empty);
      Check ("empty_finished", Is_Finished (Ctx));
      Check ("empty_padded_count", Byte_Count (Ctx) = 64);

      --  Finished context refuses Update and Finish (precondition).
      Refused := False;
      begin
         Update (Ctx, Ascii ("x"));
      exception
         when others => Refused := True;
      end;
      Check ("update_after_finish_refused", Refused);
      Refused := False;
      begin
         Finish (Ctx, D);
      exception
         when others => Refused := True;
      end;
      Check ("finish_after_finish_refused", Refused);

      --  "abc" incrementally, byte at a time, with empty updates in between.
      Reset (Ctx);
      Update (Ctx, Ascii ("a"));
      Update (Ctx, Ascii (""));
      Update (Ctx, Ascii ("b"));
      Check ("count_after_two", Byte_Count (Ctx) = 2);
      Update (Ctx, Ascii ("c"));
      Check ("digest_of_matches_hash",
             Digest_Of (Ctx) = Hash (Ascii ("abc")));
      Finish (Ctx, D);
      Check ("abc_incremental", To_Hex (D) = NIST_Abc);
      Check ("abc_padded_count", Byte_Count (Ctx) = 64);
      Check ("abc_one_shot", To_Hex (Hash (Ascii ("abc"))) = NIST_Abc);

      --  Padding boundaries: 55 bytes fit one block, 56 need two.
      declare
         M55 : constant Byte_Array (0 .. 54) := [others => 16#61#];
         M56 : constant Byte_Array (0 .. 55) := [others => 16#61#];
         M64 : constant Byte_Array (0 .. 63) := [others => 16#61#];
      begin
         Reset (Ctx);
         Update (Ctx, M55);
         Finish (Ctx, D);
         Check ("pad_55_one_block", Byte_Count (Ctx) = 64);
         Reset (Ctx);
         Update (Ctx, M56);
         Finish (Ctx, D);
         Check ("pad_56_two_blocks", Byte_Count (Ctx) = 128);
         Reset (Ctx);
         Update (Ctx, M64);
         Finish (Ctx, D);
         Check ("pad_64_two_blocks", Byte_Count (Ctx) = 128);
         Check ("padded_length_values",
                Padded_Length (0) = 64 and then Padded_Length (55) = 64
                and then Padded_Length (56) = 128 and then Padded_Length (64) = 128
                and then Padded_Length (119) = 128 and then Padded_Length (120) = 192);
      end;

      --  Two-block NIST answer through the procedure form of Hash.
      Hash (Ascii ("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"), D);
      Check ("two_block_kat", To_Hex (D) = NIST_Two_Block);

      --  The counter bound is exactly where 8 * N would wrap a uint64.
      Check ("max_message_bytes_is_u64_bits",
             V (Max_Message_Bytes) = U64'Last / 8
             and then V (Max_Message_Bytes) * 8 + 7 = U64'Last);
      Check ("padded_length_at_max_fits",
             Padded_Length (Max_Message_Bytes) = 2**61 + 64);

      --  Precondition refuses a length the counter cannot take. We cannot
      --  feed 2**61 bytes, so check the guard expression at the boundary
      --  the way Update evaluates it.
      declare
         One : constant Byte_Array (0 .. 0) := [0];
      begin
         Check ("guard_accepts_at_zero",
                U64 (One'Length) <= Max_Message_Bytes - Byte_Count (Initial));
         Check ("guard_arith_at_limit",
                U64 (One'Length) > Max_Message_Bytes - V (Max_Message_Bytes));
      end;

      --  Array bounds are not part of the message: the same bytes with a
      --  non-zero 'First (a slice, as every engine caller passes) hash alike.
      declare
         Base   : Byte_Array (0 .. 299);
         Shifted : Byte_Array (1000 .. 1299);
         Ctx2   : Context;
      begin
         for I in Base'Range loop
            Base (I) := Byte ((I * 31 + 7) mod 256);
            Shifted (I + 1000) := Base (I);
         end loop;
         Check ("hash_ignores_first_index", Hash (Base) = Hash (Shifted));
         Check ("hash_of_slice_equals_whole",
                Hash (Base (100 .. 299)) = Hash (Shifted (1100 .. 1299)));
         Reset (Ctx);
         Reset (Ctx2);
         Update (Ctx, Base (0 .. 62));
         Update (Ctx, Base (63 .. 63));
         Update (Ctx, Base (64 .. 299));
         Update (Ctx2, Shifted (1000 .. 1062));
         Update (Ctx2, Shifted (1063 .. 1063));
         Update (Ctx2, Shifted (1064 .. 1299));
         Check ("context_ignores_first_index", Ctx = Ctx2);
      end;

      --  An empty Update is the identity on the whole context, including a
      --  partially filled buffer (Updated's Post says so; check it directly).
      declare
         Empty : constant Byte_Array (5 .. 4) := [others => 0];
         Before : Context;
      begin
         Reset (Ctx);
         Update (Ctx, Ascii ("partial block"));
         Before := Ctx;
         Update (Ctx, Empty);
         Check ("empty_update_is_identity", Ctx = Before);
         Check ("empty_updated_is_identity", Updated (Ctx, Empty) = Ctx);
      end;

      --  Reset after Finish gives a fresh object: the C++ "reset to reuse".
      Reset (Ctx);
      Update (Ctx, Ascii ("garbage that must not leak"));
      Finish (Ctx, D);
      Reset (Ctx);
      Check ("reset_after_finish_is_initial", Ctx = Initial);
      Update (Ctx, Ascii ("abc"));
      Finish (Ctx, D);
      Check ("reuse_after_reset", To_Hex (D) = NIST_Abc);

      --  Finish leaves a whole number of blocks for every length 0 .. 200,
      --  and the count equals Padded_Length (the Is_Finished / Finish Posts
      --  are evaluated by -gnata here as well).
      declare
         Ok : Boolean := True;
         M  : constant Byte_Array (0 .. 200) := [others => 16#5a#];
      begin
         for N in 0 .. 200 loop
            Reset (Ctx);
            Update (Ctx, M (0 .. N - 1));
            Finish (Ctx, D);
            if Byte_Count (Ctx) mod 64 /= 0
              or else Byte_Count (Ctx) /= Padded_Length (U64 (N))
              or else Byte_Count (Ctx) < U64 (N) + 9
              or else Byte_Count (Ctx) > U64 (N) + 72
              or else not Is_Finished (Ctx)
            then
               Ok := False;
            end if;
            Lemma_Finished_Block_Aligned (Ctx);
            --  The same message in one Update and in N single-byte Updates
            --  give equal contexts (record equality, buffer included).
            declare
               C1 : Context;
               C2 : Context;
            begin
               Update (C1, M (0 .. N - 1));
               for I in 0 .. N - 1 loop
                  Update (C2, M (I .. I));
               end loop;
               if C1 /= C2 or else Digest_Of (C1) /= Digest_Of (C2) then
                  Ok := False;
               end if;
            end;
         end loop;
         Check ("finish_count_block_aligned_0_200", Ok);
      end;

      --  Finalize and Absorb are not boundary subprograms, so the invariant
      --  facts they need (Buf_Len = Total mod 64, Total <= Max_Message_Bytes)
      --  are in their own Pre. -gnata evaluates that Pre on every call;
      --  drive it through each public entry point (Digest_Of, Finish, Hash)
      --  at every buffer fill 0 .. 63 and at the block-aligned counts 64 and
      --  128, and after a Finish/Reset cycle.
      declare
         Ok : Boolean := True;
         M  : Byte_Array (0 .. 129);
         D1, D2 : Hash256;
      begin
         for I in M'Range loop
            M (I) := Byte ((I * 17 + 3) mod 256);
         end loop;
         for N in 0 .. 129 loop
            Reset (Ctx);
            Update (Ctx, M (0 .. N - 1));
            D1 := Digest_Of (Ctx);
            Finish (Ctx, D2);
            if D1 /= D2
              or else D1 /= Hash (M (0 .. N - 1))
              or else Byte_Count (Ctx) /= Padded_Length (U64 (N))
            then
               Ok := False;
            end if;
            --  A second cycle on the same object after Reset.
            Reset (Ctx);
            Update (Ctx, M (0 .. N - 1));
            if Digest_Of (Ctx) /= D1 then
               Ok := False;
            end if;
         end loop;
         Check ("finalize_pre_every_fill", Ok);
      end;

      --  Padding boundary digests are distinct from their neighbours (a
      --  length-encoding bug that dropped the low bits would collide them).
      declare
         M : constant Byte_Array (0 .. 127) := [others => 0];
      begin
         Check ("neighbour_lengths_differ",
                Hash (M (0 .. 54)) /= Hash (M (0 .. 55))
                and then Hash (M (0 .. 55)) /= Hash (M (0 .. 56))
                and then Hash (M (0 .. 62)) /= Hash (M (0 .. 63))
                and then Hash (M (0 .. 63)) /= Hash (M (0 .. 64))
                and then Hash (M (1 .. 0)) /= Hash (M (0 .. 0)));
      end;
   end Corner_Cases;

   ---------------------------------------------------------------------------
   --  Ghost laws, evaluated at run time through their postconditions
   ---------------------------------------------------------------------------

   procedure Laws is
      Ok : Boolean := True;
   begin
      declare
         A : Byte_Array (0 .. 99);
         B : Byte_Array (0 .. 129);
         C : Context := Initial;
      begin
         for I in A'Range loop
            A (I) := Byte (I * 7 mod 256);
         end loop;
         for I in B'Range loop
            B (I) := Byte (I * 13 mod 256);
         end loop;
         Lemma_Update_Concat (Initial, A, B);
         Lemma_Update_Concat (Initial, B, A);
         Lemma_Update_Concat (Initial, A (0 .. 54), A (55 .. 99));
         Lemma_Update_Concat (Initial, A (0 .. 55), A (56 .. 99));
         Lemma_Update_Concat (Initial, A (0 .. 63), A (64 .. 99));
         Lemma_Update_Concat (Initial, A (1 .. 0), B);
         Lemma_Update_Concat (Initial, A, B (1 .. 0));
         Update (C, A (0 .. 62));
         Lemma_Update_Concat (C, A, B);
         Lemma_Update_Concat (C, A (0 .. 0), B);
         --  Every buffer fill level 0 .. 63 against second pieces that
         --  stop short of, land on, and cross the block boundary.
         for Fill in 0 .. 63 loop
            declare
               C2 : Context := Initial;
            begin
               Update (C2, B (0 .. Fill - 1));
               Lemma_Update_Concat (C2, A (0 .. 0), B (0 .. 0));
               Lemma_Update_Concat (C2, A (0 .. 63 - Fill), B (0 .. 0));
               Lemma_Update_Concat (C2, A (0 .. 63 - Fill), B (0 .. 64));
               Lemma_Update_Concat (C2, A (0 .. 62 - Fill), B (0 .. 129));
               Lemma_Update_Concat (C2, A (1 .. 0), B (0 .. 63 - Fill));
            end;
         end loop;
         --  Associativity through three pieces.
         if Updated (Updated (Updated (Initial, A), B), A (0 .. 9))
           /= Updated (Initial, A & B & A (0 .. 9))
         then
            Ok := False;
         end if;
      exception
         when others => Ok := False;
      end;
      Check ("lemma_update_concat", Ok);

      --  The lemma's body is a proof (Lemma_Absorbed_Concat and the lemmas
      --  under it) whose every assertion -gnata executes: sweep it at every
      --  buffer fill 0 .. 63 with first pieces that stop short of, land on,
      --  and cross the block boundary, and second pieces of every length
      --  0 .. 200 (the chunk sizes the split vectors use).
      Ok := True;
      declare
         M : Byte_Array (0 .. 300);
      begin
         for I in M'Range loop
            M (I) := Byte ((I * 101 + 29) mod 256);
         end loop;
         for Fill in 0 .. 63 loop
            declare
               C2 : Context := Initial;
            begin
               Update (C2, M (0 .. Fill - 1));
               for L in 0 .. 200 loop
                  Lemma_Update_Concat (C2, M (1 .. 0), M (100 .. 99 + L));
                  Lemma_Update_Concat (C2, M (0 .. 0), M (100 .. 99 + L));
                  Lemma_Update_Concat (C2, M (0 .. 62 - Fill), M (100 .. 99 + L));
                  Lemma_Update_Concat (C2, M (0 .. 63 - Fill), M (100 .. 99 + L));
                  Lemma_Update_Concat (C2, M (0 .. 99), M (100 .. 99 + L));
               end loop;
            end;
         end loop;
      exception
         when others => Ok := False;
      end;
      Check ("lemma_update_concat_sweep", Ok);

      --  The proof of Lemma_Update_Concat (Lemma_Absorbed_Concat in the
      --  body) splits on how A sits against the room left in the buffer:
      --  A empty; B empty; A shorter than the room with B stopping inside
      --  the block, completing it, or crossing it; A exactly the room; A
      --  longer than the room (the inductive step, once and several times).
      --  Drive every case at every fill with operands whose 'First differ
      --  (A from 1000, B from 5) so the rebase steps run on shifted bounds,
      --  and check the law directly as well as through the lemma.
      Ok := True;
      declare
         Base_A : Byte_Array (1000 .. 1399);
         Base_B : Byte_Array (5 .. 404);
         Pre    : Byte_Array (0 .. 63);
         N_Calls : Natural := 0;
      begin
         for I in Base_A'Range loop
            Base_A (I) := Byte ((I * 37 + 11) mod 256);
         end loop;
         for I in Base_B'Range loop
            Base_B (I) := Byte ((I * 53 + 5) mod 256);
         end loop;
         for I in Pre'Range loop
            Pre (I) := Byte ((I * 71 + 1) mod 256);
         end loop;
         for Fill in 0 .. 63 loop
            declare
               Room : constant Positive := 64 - Fill;
               C    : Context := Initial;
               LA   : constant array (1 .. 7) of Natural :=
                 [0, 1, Room - 1, Room, Room + 1, 2 * Room + 5, 300];
            begin
               Update (C, Pre (0 .. Fill - 1));
               for IA in LA'Range loop
                  declare
                     NA   : constant Natural := LA (IA);
                     A    : constant Byte_Array := Base_A (1000 .. 1000 + NA - 1);
                     Left : constant Integer := Room - NA;   --  room after A
                     LB   : constant array (1 .. 7) of Integer :=
                       [0, 1, Left - 1, Left, Left + 1, 64, 300];
                  begin
                     for IB in LB'Range loop
                        if LB (IB) >= 0 then
                           declare
                              NB : constant Natural := LB (IB);
                              B  : constant Byte_Array := Base_B (5 .. 5 + NB - 1);
                              CA : Context := C;
                           begin
                              Lemma_Update_Concat (C, A, B);
                              N_Calls := N_Calls + 1;
                              Update (CA, A);
                              Update (CA, B);
                              if CA /= Updated (C, A & B)
                                or else Digest_Of (CA) /= Digest_Of (Updated (C, A & B))
                              then
                                 Ok := False;
                              end if;
                           end;
                        end if;
                     end loop;
                  end;
               end loop;
               --  Three pieces: the law applied twice, with the middle piece
               --  itself a concatenation, equals the one-shot form.
               declare
                  X : constant Byte_Array := Base_A (1000 .. 1099);
                  Y : constant Byte_Array := Base_B (5 .. 134);
                  Z : constant Byte_Array := Pre (0 .. 63);
               begin
                  Lemma_Update_Concat (C, X, Y);
                  Lemma_Update_Concat (C, X & Y, Z);
                  Lemma_Update_Concat (Updated (C, X), Y, Z);
                  if Updated (Updated (Updated (C, X), Y), Z) /= Updated (C, X & Y & Z) then
                     Ok := False;
                  end if;
               end;
            end;
         end loop;
         if N_Calls < 64 * 7 * 4 then
            Ok := False;
         end if;
      exception
         when others => Ok := False;
      end;
      Check ("lemma_update_concat_proof_cases", Ok);

      --  `A & B` is indexed from A'First, so the Pre bounds A'Last. The
      --  largest permitted value (A & B ending exactly at Natural'Last) must
      --  run clean, as must a null A with any 'First (A & B is then B) and
      --  the both-empty case; the shape the adversarial review used (A'First
      --  = Natural'Last - 5, |A| = 6, |B| = 10) must be refused by the Pre
      --  as Assertion_Error, never reach the Post and raise Constraint_Error.
      Ok := True;
      declare
         A_Max  : constant Byte_Array (Natural'Last - 15 .. Natural'Last - 10)
           := [others => 1];   --  A'Last + 10 = Natural'Last
         E_High : constant Byte_Array (Natural'Last .. Natural'Last - 1)
           := [others => 1];   --  null, 'First = Natural'Last
         B10    : constant Byte_Array (0 .. 9) := [others => 2];
      begin
         Lemma_Update_Concat (Initial, A_Max, B10);
         Lemma_Update_Concat (Initial, A_Max, B10 (1 .. 0));
         Lemma_Update_Concat (Initial, E_High, B10);
         Lemma_Update_Concat (Initial, E_High, B10 (1 .. 0));
         Lemma_Update_Concat (Initial, B10 (1 .. 0), B10 (1 .. 0));
      exception
         when others => Ok := False;
      end;
      Check ("lemma_update_concat_first_at_bound", Ok);
      Ok := False;
      declare
         A_Over : constant Byte_Array (Natural'Last - 5 .. Natural'Last)
           := [others => 1];
         B10    : constant Byte_Array (0 .. 9) := [others => 2];
      begin
         Lemma_Update_Concat (Initial, A_Over, B10);
      exception
         when Ada.Assertions.Assertion_Error => Ok := True;
         when others => Ok := False;
      end;
      Check ("lemma_update_concat_first_over_bound_refused", Ok);

      Ok := True;
      begin
         for N in U64 range 0 .. 300 loop
            Lemma_Padded_Length (N);
         end loop;
         Lemma_Padded_Length (Max_Message_Bytes);
         Lemma_Padded_Length (Max_Message_Bytes - 8);
         Lemma_Padded_Length (Max_Message_Bytes - 9);
         Lemma_Padded_Length (2**32 - 1);
         Lemma_Padded_Length (2**32);
      exception
         when others => Ok := False;
      end;
      Check ("lemma_padded_length", Ok);
   end Laws;

   ---------------------------------------------------------------------------
   --  Differential vectors
   ---------------------------------------------------------------------------

   --  check.sh runs the binary from formal/spark; tolerate bin/<module> too.
   function Find (Rel : String) return String is
      A : constant String := Rel;
      B : constant String := "../" & Rel;
      C : constant String := "../../" & Rel;
   begin
      if Ada.Directories.Exists (A) then
         return A;
      elsif Ada.Directories.Exists (B) then
         return B;
      elsif Ada.Directories.Exists (C) then
         return C;
      else
         return A;
      end if;
   end Find;

   function Vector_Path return String is (Find ("vectors/sha256.txt"));

   ---------------------------------------------------------------------------
   --  Proof-status regression: the chunking law was once a pragma Assume in
   --  the body (adversarial review finding). Its proof is now executed by
   --  the Laws above; this keeps the assumption from coming back in any
   --  form. Comments are ignored, code is not.
   ---------------------------------------------------------------------------

   procedure No_Assume is
      Path  : constant String := Find ("src/kome-sha256.adb");
      F     : File_Type;
      Line  : String (1 .. 1024);
      Last  : Natural;
      Found : Boolean := False;
   begin
      if not Ada.Directories.Exists (Path) then
         Check ("no_pragma_assume_in_body (" & Path & ")", False);
         return;
      end if;
      Open (F, In_File, Path);
      while not End_Of_File (F) loop
         Get_Line (F, Line, Last);
         declare
            Code_End : constant Natural :=
              Ada.Strings.Fixed.Index (Line (1 .. Last), "--");
            Code     : constant String :=
              (if Code_End = 0 then Line (1 .. Last) else Line (1 .. Code_End - 1));
         begin
            if Ada.Strings.Fixed.Index (Code, "Assume") > 0 then
               Found := True;
               Put_Line ("  assumption in " & Path & ": " & Code);
            end if;
         end;
      end loop;
      Close (F);
      Check ("no_pragma_assume_in_body", not Found);
   end No_Assume;

   procedure Vectors is
      F        : File_Type;
      Line     : String (1 .. 131_072);
      Last     : Natural;
      N_Kat    : Natural := 0;
      N_Repeat : Natural := 0;
      N_Split  : Natural := 0;
      Bad      : Natural := 0;

      --  Split a line into its space-separated fields.
      type Field_Bounds is record
         First, Last : Natural;
      end record;
      Fields : array (1 .. 4) of Field_Bounds;
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

      procedure Do_Kat is
         Msg : constant Byte_Array := From_Hex (Field (2));
         Want : constant Byte_Array := From_Hex (Field (3));
         Got : Hash256;
         Ctx : Context;
      begin
         N_Kat := N_Kat + 1;
         if Hash (Msg) /= Want then
            Bad := Bad + 1;
            Put_Line ("  kat mismatch at line " & Field (2) (1 .. Natural'Min (16, Field (2)'Length)));
         end if;
         --  Same bytes through the incremental form in one Update.
         Update (Ctx, Msg);
         Finish (Ctx, Got);
         if Got /= Want then
            Bad := Bad + 1;
            Put_Line ("  kat (incremental) mismatch");
         end if;
      end Do_Kat;

      --  The C++ generator feeds 4096-byte chunks; the mirror feeds the same
      --  byte stream through rotating chunk sizes around the block size (and
      --  big ones for the 2**29-byte vector), so the buffer logic is hit at
      --  every fill level while the total grows past 2**32 bits.
      Rotation : constant array (0 .. 7) of Natural :=
        [1, 63, 64, 65, 4095, 4096, 4097, 65_536];

      procedure Do_Repeat is
         B     : constant Byte_Array := From_Hex (Field (2));
         Cnt   : constant Byte_Array := From_Hex (Field (3));
         Want  : constant Byte_Array := From_Hex (Field (4));
         Count : U64 := 0;
         Chunk : constant Byte_Array (0 .. 65_535) := [others => B (B'First)];
         Left  : U64;
         Ctx   : Context;
         Got   : Hash256;
         R     : Natural := 0;
      begin
         N_Repeat := N_Repeat + 1;
         for I in Cnt'Range loop
            Count := Count * 256 + U64 (Cnt (I));
         end loop;
         Left := Count;
         while Left > 0 loop
            declare
               Want_Take : constant Natural :=
                 (if Count > 2**24 and then R mod 8 < 4
                  then Chunk'Length else Rotation (R mod 8));
               Take : constant Natural :=
                 Natural (U64'Min (Left, U64 (Want_Take)));
            begin
               Update (Ctx, Chunk (0 .. Take - 1));
               Left := Left - U64 (Take);
               R := R + 1;
            end;
         end loop;
         if Byte_Count (Ctx) /= Count then
            Bad := Bad + 1;
            Put_Line ("  repeat count mismatch");
         end if;
         Finish (Ctx, Got);
         if Got /= Want then
            Bad := Bad + 1;
            Put_Line ("  repeat mismatch");
         end if;
      end Do_Repeat;

      procedure Do_Split is
         Msg   : constant Byte_Array := From_Hex (Field (2));
         Sizes : constant Byte_Array := From_Hex (Field (3));
         Want  : constant Byte_Array := From_Hex (Field (4));
         Ctx   : Context := Initial;
         Off   : Natural := Msg'First;
         Got   : Hash256;
      begin
         N_Split := N_Split + 1;
         if Sizes'Length mod 2 /= 0 then
            raise Constraint_Error with "odd sizes field";
         end if;
         for I in 0 .. Sizes'Length / 2 - 1 loop
            declare
               S : constant Natural :=
                 Natural (Sizes (Sizes'First + 2 * I)) * 256
                 + Natural (Sizes (Sizes'First + 2 * I + 1));
            begin
               Update (Ctx, Msg (Off .. Off + S - 1));
               Off := Off + S;
            end;
         end loop;
         if Off /= Msg'First + Msg'Length then
            raise Constraint_Error with "sizes do not cover message";
         end if;
         if Byte_Count (Ctx) /= U64 (Msg'Length) then
            Bad := Bad + 1;
            Put_Line ("  split count mismatch");
         end if;
         Finish (Ctx, Got);
         if Got /= Want then
            Bad := Bad + 1;
            Put_Line ("  split mismatch, " & Natural'Image (Sizes'Length / 2) & " chunks");
         end if;
         if Hash (Msg) /= Want then
            Bad := Bad + 1;
            Put_Line ("  split one-shot mismatch");
         end if;
      end Do_Split;

      Path : constant String := Vector_Path;
   begin
      if not Ada.Directories.Exists (Path) then
         Check ("vectors_file_present (" & Path & ")", False);
         return;
      end if;
      Open (F, In_File, Path);
      while not End_Of_File (F) loop
         Get_Line (F, Line, Last);
         if Last = Line'Last then
            Put_Line ("  vector line too long for the buffer");
            Bad := Bad + 1;
         end if;
         Tokenize (Line (1 .. Last));
         if N_Fields > 0 and then Field (1) (Fields (1).First) /= '#' then
            if Field (1) = "kat" and then N_Fields = 3 then
               Do_Kat;
            elsif Field (1) = "repeat" and then N_Fields = 4 then
               Do_Repeat;
            elsif Field (1) = "split" and then N_Fields = 4 then
               Do_Split;
            else
               Put_Line ("  unknown vector line: " & Field (1));
               Bad := Bad + 1;
            end if;
         end if;
      end loop;
      Close (F);
      Check ("vectors_kat (" & N_Kat'Image & " )", N_Kat >= 200 and then Bad = 0);
      Check ("vectors_repeat (" & N_Repeat'Image & " )", N_Repeat >= 20 and then Bad = 0);
      Check ("vectors_split (" & N_Split'Image & " )", N_Split >= 600 and then Bad = 0);
      Check ("vectors_all_match", Bad = 0);
   end Vectors;

begin
   Corner_Cases;
   Laws;
   No_Assume;
   Vectors;
   if Failed then
      Set_Exit_Status (Failure);
   end if;
end Test_SHA256;
