--  Test main for Kome.Digest (DESIGN.md §8, T6). (a) Known answers: acc(e)
--  and fp(R) against vectors/digest.txt, computed with Python's hashlib
--  independently of monocypher and of the SPARK code. (b) The empty set,
--  one record, two and three records. (c) Order independence: the same
--  records added in every order give the same state and fingerprint;
--  Lemma_Add_Commute and Lemma_Sum_Swap run on them. (d) Add then remove
--  restores the state; removing from the empty state is refused and
--  changes nothing. (e) Two states holding the same records, reached by
--  different paths (orders, interleaved removals), have the same
--  fingerprint, and Lemma_Fingerprint_Congruent runs on them. (f) The
--  digest of a Kome.Frontier state is fp of its held records, and two
--  replicas that applied the same records in different orders, and so
--  hold them in different array orders (checked), have the same digest;
--  Lemma_Frontier_Digest_Perm runs on them with a computed witness.
--  (g) Prefix sums: Range_Sum over many ranges of a 150-element list
--  (crossing, ending on and spanning 64-element blocks, and walking
--  forward and backward to the nearest block boundary) equals the
--  directly computed sum. (h) Models: a running state carried through
--  adds, removals and a permutation with the Models lemmas, and
--  Lemma_Sum_Perm on a reversed list. Under -gnata every Pre, Post and
--  lemma Post also runs on these data.
pragma Ada_2022;
with Ada.Text_IO;       use Ada.Text_IO;
with Ada.Command_Line;  use Ada.Command_Line;
with Ada.Directories;
with Kome;              use Kome;
with Kome.Keys;
with Kome.Headers;      use Kome.Headers;
with Kome.Frontier;
with Kome.Accumulator;  use Kome.Accumulator;
with Kome.Crypto;
with Kome.Digest;       use Kome.Digest;

procedure Test_Digest with SPARK_Mode => Off is

   Failed : Boolean := False;

   procedure Check (Name : String; Cond : Boolean) is
   begin
      Put_Line ((if Cond then "PASS " else "FAIL ") & Name);
      if not Cond then
         Failed := True;
      end if;
   end Check;

   function Hex_Digit (C : Character) return Byte is
     (case C is
        when '0' .. '9' => Character'Pos (C) - Character'Pos ('0'),
        when 'a' .. 'f' => Character'Pos (C) - Character'Pos ('a') + 10,
        when 'A' .. 'F' => Character'Pos (C) - Character'Pos ('A') + 10,
        when others     => raise Constraint_Error);

   function From_Hex (S : String) return Byte_Array is
      R : Byte_Array (0 .. S'Length / 2 - 1);
   begin
      for I in R'Range loop
         R (I) := Hex_Digit (S (S'First + 2 * I)) * 16
                  + Hex_Digit (S (S'First + 2 * I + 1));
      end loop;
      return R;
   end From_Hex;

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

   --  Kome.Digest.Count, not Kome.Frontier.Count or Ada.Text_IO.Count.
   function Count (S : Digest_State) return Elem_Count is
     (Kome.Digest.Count (S));

   function Same (A, B : Digest_State) return Boolean is
     (Count (A) = Count (B) and then Sum (A) = Sum (B)
      and then Fingerprint (A) = Fingerprint (B));

   --  Distinct, unstructured element hashes.
   function H (N : Natural) return Key256 is
      X : Word :=
        Word ((Long_Long_Integer (N) * 2_654_435_761 + 12_345) mod 2**32);
      R : Key256;
      function Next return Word is
      begin
         X := Word ((Long_Long_Integer (X) * 1_103_515_245 + 12_345)
                    mod 2**32);
         return X;
      end Next;
   begin
      R.W0 := Next; R.W1 := Next; R.W2 := Next; R.W3 := Next;
      R.W4 := Next; R.W5 := Next; R.W6 := Next; R.W7 := Word (N);
      return R;
   end H;

   function Fold (L : Hash_Array) return Digest_State is
      S : Digest_State := Empty;
      R : Digest_Status;
   begin
      for I in L'Range loop
         Add_Record (S, L (I), R);
         if R /= D_OK then
            raise Program_Error;
         end if;
      end loop;
      return S;
   end Fold;

   ---------------------------------------------------------------------------
   --  (a) Known answers
   ---------------------------------------------------------------------------

   Empty_Fp : Hash256 := [others => 0];
   Have_Empty_Fp : Boolean := False;

   procedure Vectors is
      Path : constant String := Find ("vectors/digest.txt");
      F    : File_Type;
      Line : String (1 .. 4096);
      Last : Natural;

      type Bounds is record
         First, Last : Natural;
      end record;
      Fields   : array (1 .. 6) of Bounds;
      N_Fields : Natural;
      N_Acc    : Natural := 0;
      N_Fp     : Natural := 0;
      Ok_Acc   : Boolean := True;
      Ok_Fp    : Boolean := True;
      Ok_Fold  : Boolean := True;

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
            if Field (1) = "acc" and then N_Fields = 3 then
               declare
                  K    : constant Key256 := Key_Of (Field (2));
                  Want : constant Byte_Array := From_Hex (Field (3));
               begin
                  N_Acc := N_Acc + 1;
                  Lemma_Elem_Acc_Value (K);
                  if Acc_Byte_Array (Want) /= To_Bytes (Elem_Acc (K))
                    or else Acc_Byte_Array (Want) /= Acc_Bytes_Of (K)
                  then
                     Ok_Acc := False;
                     Put_Line ("  mismatch: acc " & Field (2));
                  end if;
               end;
            elsif Field (1) = "fp" and then N_Fields = 4 then
               declare
                  N    : constant Natural := Natural'Value (Field (2));
                  Want : constant Hash256 := From_Hex (Field (4));
                  L    : Hash_Array (1 .. N);
               begin
                  N_Fp := N_Fp + 1;
                  if N > 0 then
                     for I in 1 .. N loop
                        L (I) := Key_Of
                          (Field (3) (Fields (3).First + 64 * (I - 1)
                                      .. Fields (3).First + 64 * I - 1));
                     end loop;
                  end if;
                  if Fingerprint (Digest_Of (L)) /= Want then
                     Ok_Fp := False;
                     Put_Line ("  mismatch: fp " & Field (2));
                  end if;
                  if Fingerprint (Fold (L)) /= Want
                    or else not Same (Fold (L), Digest_Of (L))
                  then
                     Ok_Fold := False;
                  end if;
                  if N = 0 then
                     Empty_Fp := Want;
                     Have_Empty_Fp := True;
                  end if;
               end;
            else
               Check ("vector_line_parses (" & Field (1) & ")", False);
            end if;
         end if;
      end loop;
      Close (F);
      Check ("acc_matches_hashlib (" & N_Acc'Image & " vectors)",
             Ok_Acc and then N_Acc >= 5);
      Check ("fp_matches_hashlib (" & N_Fp'Image & " vectors)",
             Ok_Fp and then N_Fp >= 9);
      Check ("add_record_fold_matches_digest_of", Ok_Fold);
   end Vectors;

   ---------------------------------------------------------------------------
   --  (b), (c), (d), (e) The incremental state
   ---------------------------------------------------------------------------

   procedure State_Laws is
      E  : constant Digest_State := Empty;
      S  : Digest_State;
      R  : Digest_Status;
      A  : constant Key256 := H (1);
      B  : constant Key256 := H (2);
      C  : constant Key256 := H (3);
   begin
      --  (b) Empty.
      Check ("empty_count_zero", Count (E) = 0);
      Check ("empty_sum_zero", Sum (E) = Zero);
      Check ("empty_fp_is_vector",
             Have_Empty_Fp and then Fingerprint (E) = Empty_Fp);
      Check ("empty_fp_is_hash_of_tag_zero_count_zero_acc",
             Fingerprint (E)
               = Kome.Crypto.Blake2b_256
                   (Byte_Array'([16#6B#, 16#6F#, 16#6D#, 16#65#, 16#2F#,
                                 16#66#, 16#70#])
                    & Byte_Array'(0 .. 519 => 0)));

      --  One record.
      S := E;
      Add_Record (S, A, R);
      Check ("one_record_ok", R = D_OK and then Count (S) = 1);
      Check ("one_record_sum_is_acc", Sum (S) = Elem_Acc (A));
      Check ("one_record_fp_is_fp_of_acc",
             Fingerprint (S) = Fp (1, Elem_Acc (A)));
      Check ("one_record_fp_differs_from_empty",
             Fingerprint (S) /= Fingerprint (E));
      Check ("distinct_records_distinct_fp",
             Fingerprint (With_Record (E, A))
               /= Fingerprint (With_Record (E, B)));

      --  (c) Order independence: all six orders of three records.
      declare
         Orders : constant array (1 .. 6) of Hash_Array (1 .. 3) :=
           [[A, B, C], [A, C, B], [B, A, C], [B, C, A], [C, A, B], [C, B, A]];
         Ref    : constant Digest_State := Fold (Orders (1));
         Ok     : Boolean := True;
      begin
         for O of Orders loop
            Ok := Ok and then Same (Fold (O), Ref)
                     and then Same (Digest_Of (O), Ref);
         end loop;
         Check ("order_independent_all_6_orders", Ok);
         Check ("three_records_count", Count (Ref) = 3);
         Check ("three_records_sum_is_sum_of_accs",
                Sum (Ref) = Add (Add (Elem_Acc (A), Elem_Acc (B)),
                                 Elem_Acc (C)));
         --  Every adjacent swap, through the lemma.
         Lemma_Sum_Swap (Orders (1), Orders (3), 1);
         Lemma_Sum_Swap (Orders (1), Orders (2), 2);
         Lemma_Sum_Swap (Orders (4), Orders (6), 1);
         Check ("lemma_sum_swap_runs", True);
         --  Split: ACC (A, B, C) = ACC (A) + ACC (B, C), and every split.
         for Mid in 0 .. 3 loop
            Lemma_Sum_Split (Orders (1), 1, Mid, 3);
         end loop;
         Check ("lemma_sum_split_runs", True);
         Check ("t6_split_union",
                Sum (Ref) = Add (Sum (Digest_Of (Orders (1) (1 .. 1))),
                                 Sum (Digest_Of (Orders (1) (2 .. 3)))));
         Lemma_Sum_Ext (Orders (1), Orders (2), 1, 1);
         Lemma_Sum_Of_Empty (Orders (1), 2, 1);
         Lemma_Sum_Of_Step (Orders (1), 1, 3);
      end;
      Lemma_Add_Commute (E, A, B);
      Lemma_Add_Commute (With_Record (E, C), B, A);
      Check ("add_commute",
             Same (With_Record (With_Record (E, A), B),
                   With_Record (With_Record (E, B), A)));
      Check ("duplicate_counts_twice",
             Count (With_Record (With_Record (E, A), A)) = 2
             and then Fingerprint (With_Record (With_Record (E, A), A))
                        /= Fingerprint (With_Record (E, A)));

      --  (d) Add then remove.
      S := Fold ([A, B]);
      declare
         Before : constant Digest_State := S;
      begin
         Add_Record (S, C, R);
         Check ("add_ok", R = D_OK and then Count (S) = 3);
         Remove_Record (S, C, R);
         Check ("add_then_remove_restores", R = D_OK and then Same (S, Before));
         Remove_Record (S, A, R);
         Check ("remove_first_added_leaves_rest",
                R = D_OK and then Same (S, With_Record (E, B)));
         Remove_Record (S, B, R);
         Check ("remove_all_is_empty", R = D_OK and then Same (S, E));
         Remove_Record (S, B, R);
         Check ("remove_from_empty_refused",
                R = D_Empty and then Same (S, E));
         Lemma_Remove_Add (Before, C);
         Lemma_Add_Remove (Before, A);
         Check ("without_with_identity",
                Same (Without_Record (With_Record (Before, C), C), Before));
         Check ("with_without_identity",
                Same (With_Record (Without_Record (Before, B), B), Before));
         Check ("remove_before_add_then_add_is_empty",
                Same (With_Record (Without_Record (Fold ([A]), C), C),
                      Fold ([A])));
      end;

      --  (e) Same records by different paths.
      declare
         P1 : Digest_State := Fold ([A, B, C]);
         P2 : Digest_State := Fold ([C, H (99), A]);
      begin
         Remove_Record (P2, H (99), R);
         Add_Record (P2, B, R);
         Check ("same_records_different_paths_same_fp",
                Count (P1) = Count (P2)
                and then Fingerprint (P1) = Fingerprint (P2));
         Lemma_Fingerprint_Congruent (P1, P2);
         Lemma_Fp_Congruent (Count (P1), Sum (P1), Sum (P2));
         Remove_Record (P1, A, R);
         Check ("different_records_different_fp",
                Fingerprint (P1) /= Fingerprint (P2));
      end;
   end State_Laws;

   ---------------------------------------------------------------------------
   --  (f) Frontier digest
   ---------------------------------------------------------------------------

   procedure Frontier_Part is
      use Kome.Frontier;
      NS : constant Id128 := (others => 7);

      function K (B : Natural) return Key256 is (others => Word (B));
      function Ent (B : Natural) return Id128 is (others => Word (B));

      function Put (E : Natural; F : Natural; T : U48; A : Natural;
                    Hh : Natural) return Header is
        (K => K_Put, NS => NS, Ent => Ent (E), FH => K (F),
         V => (T => T, Author => K (A), Seq => 1, H => H (Hh)),
         Ceiling => 0);

      Roster : constant Header :=
        (K => K_Roster, NS => NS, Ent => Ent (0), FH => K (0),
         V => (T => 0, Author => K (9), Seq => 1, H => H (500)),
         Ceiling => 100);
      Members : constant Member_Keys (1 .. 2) := [K (1), K (2)];
      None    : constant Member_Keys (1 .. 0) := [];

      Recs : constant array (1 .. 4) of Header :=
        [Put (1, 1, 10, 1, 501), Put (1, 2, 11, 2, 502),
         Put (1, 1, 12, 2, 503),   --  beats the first on cell (1, 1)
         Put (2, 1, 13, 1, 504)];

      X : State := Empty (NS, 16);
      Y : State := Empty (NS, 16);
      Z : constant State := Empty (NS, 16);
      St : Status;
   begin
      Check ("frontier_empty_digest_is_empty_fp",
             Frontier_Digest (Z) = Fingerprint (Kome.Digest.Empty));
      --  Both replicas take the roster first (so the records are
      --  admissible), then the same four records: X in order, Y in
      --  reverse. In Y, Recs (1) arrives after Recs (3), which beats it on
      --  cell (1, 1), so it is Dominated; in X it is held and then dropped.
      Apply (X, Roster, Members, St);
      Check ("frontier_x_roster_ok", St = OK);
      Apply (Y, Roster, Members, St);
      Check ("frontier_y_roster_ok", St = OK);
      declare
         All_OK : Boolean := True;
      begin
         for I in Recs'Range loop
            Apply (X, Recs (I), None, St);
            All_OK := All_OK and then St = Kome.OK;
         end loop;
         Check ("frontier_x_forward_all_ok", All_OK);
      end;
      for I in reverse Recs'Range loop
         Apply (Y, Recs (I), None, St);
         Check ("frontier_y_reverse_rec" & I'Image & "_status",
                (if I = 1 then St = Dominated else St = OK));
      end loop;
      Check ("frontier_holds_4", Kome.Frontier.Count (X) = 4
             and then Kome.Frontier.Count (Y) = 4);
      Check ("frontier_held_orders_differ",
             Held (X, 2).V.H /= Held (Y, 2).V.H);
      declare
         L : Hash_Array (1 .. Kome.Frontier.Count (X));
      begin
         for I in L'Range loop
            L (I) := Held (X, I).V.H;
         end loop;
         Check ("frontier_digest_is_fp_of_held",
                Frontier_Digest (X) = Fingerprint (Digest_Of (L)));
         Check ("frontier_state_of_matches",
                Same (State_Of (X), Digest_Of (L)));
         Lemma_Frontier_Sum_List (X, L, Kome.Frontier.Count (X));
         Lemma_State_Of_Models (X, L);
         Check ("frontier_lemmas_run", True);
      end;
      --  The witness: M (I) is where Y holds X's I-th hash.
      declare
         N  : constant Natural := Kome.Frontier.Count (X);
         M  : Index_Map (1 .. N) := [others => 1];
         Ok : Boolean := True;
      begin
         for I in 1 .. N loop
            declare
               Found : Boolean := False;
            begin
               for J in 1 .. Kome.Frontier.Count (Y) loop
                  if Held (Y, J).V.H = Held (X, I).V.H then
                     M (I) := J;
                     Found := True;
                  end if;
               end loop;
               Ok := Ok and then Found;
            end;
         end loop;
         Check ("frontier_same_record_set", Ok);
         Check ("frontier_witness_not_identity",
                (for some I in 1 .. N => M (I) /= I));
         Lemma_Frontier_Digest_Perm (X, Y, M);
         Check ("frontier_same_records_any_order_same_digest",
                Frontier_Digest (X) = Frontier_Digest (Y));
      end;
      Check ("frontier_digest_changes_with_frontier",
             Frontier_Digest (X) /= Frontier_Digest (Z));
   end Frontier_Part;

   ---------------------------------------------------------------------------
   --  (g) Prefix sums
   ---------------------------------------------------------------------------

   procedure Prefix_Sums is
      N : constant := 150;
      L : Hash_Array (1 .. N);
      P : Acc_Array (1 .. N / Block_Elems);
      type Pair is record
         Lo, Hi : Natural;
      end record;
      Ranges : constant array (Positive range <>) of Pair :=
        [(1, 0), (1, 150), (5, 5), (60, 70), (64, 64), (65, 128), (1, 64),
         (100, 150), (130, 150), (129, 128), (2, 127), (151, 150),
         --  Ends with r > 32 below a stored block: walk back.
         (40, 120), (97, 127), (34, 96), (33, 33), (35, 100), (98, 99)];
      Ok : Boolean := True;
   begin
      for I in L'Range loop
         L (I) := H (1000 + I);
      end loop;
      Build_Prefix (L, P);
      Check ("prefix_count", P'Length = 2);
      Check ("prefix_1_is_first_block",
             P (1) = Sum (Digest_Of (L (1 .. 64))));
      Check ("prefix_2_is_first_two_blocks",
             P (2) = Sum (Digest_Of (L (1 .. 128))));
      for Rg of Ranges loop
         declare
            Got  : constant Acc := Range_Sum (L, P, Rg.Lo, Rg.Hi);
            Want : constant Acc :=
              (if Rg.Hi < Rg.Lo then Zero
               else Sum (Digest_Of (L (Rg.Lo .. Rg.Hi))));
         begin
            if Got /= Want then
               Ok := False;
               Put_Line ("  mismatch: range" & Rg.Lo'Image & Rg.Hi'Image);
            end if;
         end;
      end loop;
      Check ("range_sum_matches_direct_sum (" & Ranges'Length'Image
             & " ranges)", Ok);
      --  A range's fingerprint is fp of its records.
      Check ("range_fp_is_fp_of_records",
             Fp (40, Range_Sum (L, P, 61, 100))
               = Fingerprint (Digest_Of (L (61 .. 100))));
   end Prefix_Sums;

   ---------------------------------------------------------------------------
   --  (h) Models, permutations, deletion
   ---------------------------------------------------------------------------

   procedure Models_Part is
      L   : Hash_Array (1 .. 8) := [others => H (0)];
      L0  : Hash_Array (1 .. 8);
      S   : Digest_State := Empty;
      R   : Digest_Status;
      N   : Natural := 0;
      Rev : Hash_Array (1 .. 5);
      Fwd : Hash_Array (1 .. 5);
      Mr  : Index_Map (1 .. 5);
   begin
      Lemma_Models_Empty (L);
      --  Add five records, carrying Models.
      for I in 1 .. 5 loop
         L0 := L;
         L (N + 1) := H (200 + I);
         Lemma_Models_Add (S, L0, L, N, H (200 + I));
         Add_Record (S, H (200 + I), R);
         N := N + 1;
      end loop;
      Check ("models_after_adds", Count (S) = 5
             and then Same (S, Digest_Of (L (1 .. 5))));
      Lemma_Digest_Of_Models (L (1 .. 5));
      --  Remove the member at index 2, shifting the rest down.
      L0 := L;
      for I in 2 .. 4 loop
         L (I) := L0 (I + 1);
      end loop;
      Lemma_Models_Remove (S, L0, L, N, 2);
      Remove_Record (S, L0 (2), R);
      N := N - 1;
      Check ("models_after_remove",
             R = D_OK and then Same (S, Digest_Of (L (1 .. 4))));
      --  A permutation: reverse L (1 .. 4).
      declare
         P  : Hash_Array (1 .. 8) := L;
         M  : Index_Map (1 .. 8) := [others => 1];
         S2 : Digest_State := Empty;
      begin
         for I in 1 .. 4 loop
            P (5 - I) := L (I);
            M (I) := 5 - I;
         end loop;
         Lemma_Models_Perm (S, L, P, M, 4);
         for I in 1 .. 4 loop
            Add_Record (S2, P (I), R);
         end loop;
         Lemma_Models_Fingerprint (S, S2, L, P, M, 4);
         Check ("models_permuted_same_fingerprint",
                Fingerprint (S) = Fingerprint (S2));
      end;
      --  Lemma_Sum_Perm and Lemma_Sum_Delete directly.
      for I in 1 .. 5 loop
         Fwd (I) := H (300 + I);
         Rev (6 - I) := H (300 + I);
         Mr (I) := 6 - I;
      end loop;
      Lemma_Sum_Perm (Fwd, Rev, Mr, 5);
      Lemma_Sum_Perm (Fwd, Rev, Mr, 0);
      Lemma_Sum_Delete (Fwd, [Fwd (1), Fwd (2), Fwd (4), Fwd (5)], 5, 3);
      Lemma_Sum_Delete (Fwd, Fwd, 5, 5);
      Check ("perm_reverse_same_digest",
             Same (Digest_Of (Fwd), Digest_Of (Rev)));
      Check ("delete_lemmas_run", True);
      --  Wire form of the fp input, and the exported congruences.
      Lemma_Fp_Input_Acc (3, Sum (Digest_Of (Fwd)));
      Lemma_Add_Congruent (Sum (S), Sum (S), Elem_Acc (H (1)), Elem_Acc (H (1)));
      Lemma_Sub_Congruent (Sum (S), Sum (S), Elem_Acc (H (1)), Elem_Acc (H (1)));
      Check ("fp_input_acc_is_to_bytes",
             Fp_Input (3, Sum (S)) (Acc_Pos .. Fp_Input_Len - 1)
               = To_Bytes (Sum (S)));
   end Models_Part;

begin
   Vectors;
   State_Laws;
   Frontier_Part;
   Prefix_Sums;
   Models_Part;
   if Failed then
      Set_Exit_Status (Failure);
   end if;
end Test_Digest;
