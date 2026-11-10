--  Test main for Kome.Digest (DESIGN.md §8, D7, D15, T6). The test has
--  these parts:
--    (a) Known answers: acc(e) and fp(R) against vectors/digest.txt.
--        Python hashlib computed these, independently of monocypher and of
--        the SPARK code.
--    (b) The empty set, one record, two records and three records.
--    (c) Order independence: the same records, added in each order, give
--        the same state and fingerprint. Lemma_Add_Commute and
--        Lemma_Sum_Swap run on them.
--    (d) Add then remove restores the state. A removal from the empty
--        state is refused and changes nothing.
--    (e) Two states that hold the same records, reached through different
--        paths (orders, interleaved removals), have the same fingerprint.
--        Lemma_Fingerprint_Congruent runs on them. Also the documented
--        contract: the removal of a non-member, or a second add, returns
--        D_OK and gives a state that is not the state of any set.
--    (f) The digest of a Kome.Frontier state is fp of its held records
--        (data row and authorization rows). Two replicas that applied the
--        same records in different orders hold them in different array
--        orders (checked), and they have the same digest.
--        Lemma_Frontier_Digest_Perm runs on them with a computed witness.
--    (g) Prefix sums (D15), for lists of 150, 127, 64, 40, 1 and 0
--        elements:
--          * each stored block prefix and the total P_end;
--          * Range_Sum against the directly computed sum, on ranges that
--            cross, end on and span 64-element blocks and end in the tail
--            (r > 32, a one-element range at 127, [1 .. 96] that walks
--            back from P_end);
--          * the Add and Sub calls that Range_Sum reports on each sampled
--            range, against an independently computed cost (1 for
--            [127 .. 127] of 127, 31 for [1 .. 96] of 127, 64 for
--            [33 .. 96] of 150; one Sub);
--          * the bound Range_Cost <= 64 on each range of each list.
--        The reported counts are out values, so these checks test the
--        body's counters and the formula, not the Add calls actually
--        made. A body that ignored P and set the counts from Range_Cost
--        would pass them (the spec header records this limit).
--    (h) Models: a running state carried through adds, removals and a
--        permutation with the Models lemmas, the intro and elim lemmas of
--        Is_Perm, and Lemma_Sum_Perm on a reversed list.
--    (i) Capacity: D_No_Space at |R| = Elem_Max
--        (= Kome.Frontier.Held_Max), and the state does not change.
--  The test checks each Result. Under -gnata, each Pre, Post and lemma
--  Post also runs on these data.
pragma Ada_2022;
with Ada.Text_IO;       use Ada.Text_IO;
with Ada.Command_Line;  use Ada.Command_Line;
with Ada.Directories;
with Ada.Exceptions;
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

   --  Different, unstructured element hashes.
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
         --  Each adjacent swap, through the lemma.
         Lemma_Sum_Swap (Orders (1), Orders (3), 1);
         Lemma_Sum_Swap (Orders (1), Orders (2), 2);
         Lemma_Sum_Swap (Orders (4), Orders (6), 1);
         Check ("lemma_sum_swap_runs", True);
         --  Split: ACC (A, B, C) = ACC (A) + ACC (B, C), and each split.
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

      --  (e) The same records through different paths.
      declare
         P1 : Digest_State := Fold ([A, B, C]);
         P2 : Digest_State := Fold ([C, H (99), A]);
      begin
         Remove_Record (P2, H (99), R);
         Check ("path_remove_ok", R = D_OK and then Count (P2) = 2);
         Add_Record (P2, B, R);
         Check ("path_add_ok", R = D_OK and then Count (P2) = 3);
         Check ("same_records_different_paths_same_fp",
                Count (P1) = Count (P2)
                and then Fingerprint (P1) = Fingerprint (P2));
         Lemma_Fingerprint_Congruent (P1, P2);
         Lemma_Fp_Congruent (Count (P1), Sum (P1), Sum (P2));
         Remove_Record (P1, A, R);
         Check ("different_records_different_fp",
                R = D_OK and then Count (P1) = 2
                and then Fingerprint (P1) /= Fingerprint (P2));
      end;

      --  The documented contract (header): the state does not hold R, so
      --  the removal of a non-member, or a second add of a member, returns
      --  D_OK and applies the arithmetic. The result is not the state of
      --  any set. Only the caller's Models discipline guards against this.
      declare
         P3 : Digest_State := Fold ([A]);
      begin
         Remove_Record (P3, C, R);
         Check ("contract_remove_non_member_is_ok",
                R = D_OK and then Count (P3) = 0
                and then Sum (P3) = Sub (Elem_Acc (A), Elem_Acc (C)));
         Check ("contract_remove_non_member_is_no_set",
                Sum (P3) /= Zero and then not Same (P3, E));
         P3 := Fold ([A]);
         Add_Record (P3, A, R);
         Check ("contract_add_twice_is_ok",
                R = D_OK and then Count (P3) = 2
                and then Sum (P3) = Add (Elem_Acc (A), Elem_Acc (A))
                and then not Same (P3, Fold ([A])));
      end;
   end State_Laws;

   ---------------------------------------------------------------------------
   --  (f) Frontier digest
   ---------------------------------------------------------------------------

   procedure Frontier_Part is
      use Kome.Frontier;
      Fnd : constant Natural := 9;           --  the founding key

      function K (B : Natural) return Key256 is (others => Word (B));
      function Ent (B : Natural) return Id128 is (others => Word (B));

      function Put (E : Natural; F : Natural; T : U48; A : Natural;
                    Hh : Natural) return Header is
        (K => K_Put, Ent => Ent (E), FH => K (F),
         V => (T => T, Author => K (A), Seq => 1, H => H (Hh)),
         Issuer => Zero_Key);

      --  The founding key's roster (V = (ceiling_t, signer, gen, h))
      --  and its GRANTs (V = (0, subject, 0, h)) to the two writers.
      Roster : constant Header :=
        (K => K_Roster, Ent => Zero_Id, FH => Zero_Key,
         V => (T => 100, Author => K (Fnd), Seq => 1, H => H (500)),
         Issuer => K (Fnd));
      function Grant (Subject : Natural; Hh : Natural) return Header is
        (K => K_Grant, Ent => Zero_Id, FH => Zero_Key,
         V => (T => U48'Last, Author => K (Subject), Seq => 0, H => H (Hh)),
         Issuer => K (Fnd));
      Auth : constant array (1 .. 3) of Header :=
        [Roster, Grant (1, 510), Grant (2, 511)];

      Recs : constant array (1 .. 4) of Header :=
        [Put (1, 1, 10, 1, 501), Put (1, 2, 11, 2, 502),
         Put (1, 1, 12, 2, 503),   --  beats the first on cell (1, 1)
         Put (2, 1, 13, 1, 504)];

      X : State := Empty (K (Fnd), 16);
      Y : State := Empty (K (Fnd), 16);
      Z : constant State := Empty (K (Fnd), 16);
      St : Status;
   begin
      Check ("frontier_empty_digest_is_empty_fp",
             Frontier_Digest (Z) = Fingerprint (Kome.Digest.Empty));
      --  The two replicas first take the roster and the grants (so that
      --  the records are admissible): X in order, Y in reverse order, so
      --  their slots hold them in different orders. Then they take the
      --  same four records: X in order, Y in reverse order. In Y, Recs (1)
      --  comes after Recs (3), which beats it on cell (1, 1), so it is
      --  Dominated. In X, it is held and then dropped. (The data row is
      --  sorted by key, AUDIT.md G25, so the two data rows end in the same
      --  order; the slot order differs.)
      for I in Auth'Range loop
         Apply (X, Auth (I), U64 (I), St);
         Check ("frontier_x_auth" & I'Image & "_ok", St = OK);
         Apply (Y, Auth (Auth'Last + 1 - I), U64 (I), St);
         Check ("frontier_y_auth" & I'Image & "_ok", St = OK);
      end loop;
      for I in Recs'Range loop
         Apply (X, Recs (I), U64 (I), St);
         Check ("frontier_x_forward_rec" & I'Image & "_ok", St = OK);
      end loop;
      for I in reverse Recs'Range loop
         Apply (Y, Recs (I), U64 (I), St);
         Check ("frontier_y_reverse_rec" & I'Image & "_status",
                (if I = 1 then St = Dominated else St = OK));
      end loop;
      Check ("frontier_holds_3_data_3_auth",
             Kome.Frontier.Count (X) = 6 and then Kome.Frontier.Count (Y) = 6
             and then Data_Count (X) = 3 and then Data_Count (Y) = 3);
      Check ("frontier_held_orders_differ",
             (for some I in 1 .. Kome.Frontier.Count (X) =>
                Held (X, I).V.H /= Held (Y, I).V.H));
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
      --  The witness: M (I) is where Y holds the I-th hash of X.
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

   type Pair is record
      Lo, Hi : Natural;
   end record;
   type Pair_Array is array (Positive range <>) of Pair;

   --  The sum of L (Lo .. Hi), computed directly.
   function Direct (L : Hash_Array; Lo, Hi : Natural) return Acc is
     (if Hi < Lo then Zero else Sum (Digest_Of (L (Lo .. Hi))));

   --  The expected number of Add calls for an end X of an N-element list,
   --  computed here independently of the spec's formula. It is the
   --  distance from X to the block boundary below it, or to the stored
   --  point above it (the next block boundary, or N where P_end is
   --  stored). The nearer of the two applies.
   function End_Cost (X, N : Natural) return Natural is
      R  : constant Natural := X mod 64;
      Up : constant Natural :=
        (if 64 * (X / 64 + 1) <= N then 64 - R else N - X);
   begin
      return Natural'Min (R, Up);
   end End_Cost;

   --  Run Range_Sum on L (Lo .. Hi) and return its result and counts.
   procedure Run_Range
     (L : Hash_Array; P : Acc_Array; Lo, Hi : Natural;
      Got : out Acc; Adds : out Natural; Subs : out Natural)
   is
      A : Add_Count;
   begin
      Range_Sum (L, P, Lo, Hi, Got, A, Subs);
      Adds := A;
   end Run_Range;

   --  Build the prefix array of an N-element list (with the tail after the
   --  last full block), and check each stored entry and the total. Check
   --  Range_Sum against the direct sum on each range. Check the Add and
   --  Sub calls that it reports on each range against the independently
   --  computed cost (End_Cost at both ends, one Sub). Check the formula
   --  Range_Cost on each range of the list.
   procedure Prefix_List (N : Natural; Ranges : Pair_Array; Tag : String) is
      L  : Hash_Array (1 .. N);
      P  : Acc_Array (1 .. N / Block_Elems + 1);
      Ok : Boolean := True;
      Cost_Ok  : Boolean := True;
      Max_Cost : Natural := 0;
   begin
      for I in L'Range loop
         L (I) := H (1000 + I);
      end loop;
      Build_Prefix (L, P);
      Lemma_Prefix_Total (L, P);
      Check (Tag & "_prefix_count", P'Length = N / 64 + 1);
      for K in 1 .. P'Last - 1 loop
         Ok := Ok and then P (K) = Direct (L, 1, 64 * K);
      end loop;
      Check (Tag & "_prefix_blocks", Ok);
      Check (Tag & "_prefix_last_is_total", P (P'Last) = Direct (L, 1, N));
      Ok := True;
      for Rg of Ranges loop
         declare
            Got        : Acc;
            Adds, Subs : Natural;
            Want : constant Acc := Direct (L, Rg.Lo, Rg.Hi);
            C    : constant Natural :=
              End_Cost (Rg.Lo - 1, N) + End_Cost (Rg.Hi, N);
         begin
            Run_Range (L, P, Rg.Lo, Rg.Hi, Got, Adds, Subs);
            if Got /= Want then
               Ok := False;
               Put_Line ("  mismatch: range" & Rg.Lo'Image & Rg.Hi'Image);
            end if;
            if Adds /= C or else Adds /= Range_Cost (Rg.Lo - 1, Rg.Hi, N)
              or else Adds > 64 or else Subs /= 1
            then
               Cost_Ok := False;
               Put_Line ("  cost: range" & Rg.Lo'Image & Rg.Hi'Image
                         & " adds" & Adds'Image & " want" & C'Image
                         & " subs" & Subs'Image);
            end if;
         end;
      end loop;
      Check (Tag & "_range_sum_matches_direct_sum (" & Ranges'Length'Image
             & " ranges)", Ok);
      Check (Tag & "_range_sum_counted_adds_and_one_sub (" &
             Ranges'Length'Image & " ranges)", Cost_Ok);
      --  The bound is true for each range, not only for the sampled
      --  ranges, and each end walks at most 32 terms.
      Ok := True;
      for A in 0 .. N loop
         Ok := Ok and then Walk_Len (A, N) <= 32
                  and then Walk_Len (A, N) = End_Cost (A, N);
         for B in A .. N loop
            Max_Cost := Natural'Max (Max_Cost, Range_Cost (A, B, N));
         end loop;
      end loop;
      Check (Tag & "_every_end_walks_at_most_32", Ok);
      Check (Tag & "_every_range_costs_at_most_64 (max" & Max_Cost'Image
             & ")", Max_Cost <= 64);
   end Prefix_List;

   procedure Prefix_Sums is
      --  150 elements: two full blocks and a 22-element tail.
      R150 : constant Pair_Array :=
        [(1, 0), (1, 150), (5, 5), (60, 70), (64, 64), (65, 128), (1, 64),
         (100, 150), (130, 150), (129, 128), (2, 127), (151, 150),
         --  Ends with r > 32 below a stored block: they walk back.
         (40, 120), (97, 127), (34, 96), (33, 33), (35, 100), (98, 99),
         --  Ends in the tail: back from P_end, forward from P (2).
         (140, 150), (150, 150), (129, 140), (1, 141), (141, 149)];
      --  127 elements: one full block and a 63-element tail, so each end
      --  above 64 is in the tail.
      R127 : constant Pair_Array :=
        [(127, 127),   --  one element at the end
         (1, 96),      --  b = 96 walks back 31 terms from P_end
         (1, 127), (1, 0), (128, 127), (65, 127), (100, 127), (98, 126),
         (66, 96), (97, 97), (96, 98), (70, 110), (2, 63), (33, 64),
         (64, 65), (1, 120), (120, 127), (126, 127)];
      --  Exactly one block (no tail: P_end = P (1)), and short lists.
      R64 : constant Pair_Array :=
        [(1, 64), (64, 64), (1, 33), (34, 64), (32, 40), (65, 64)];
      R40 : constant Pair_Array :=
        [(1, 40), (40, 40), (1, 1), (21, 40), (20, 20), (41, 40)];
      R1  : constant Pair_Array := [(1, 1), (1, 0), (2, 1)];
      R0  : constant Pair_Array := [(1, 0)];
   begin
      Prefix_List (150, R150, "n150");
      Prefix_List (127, R127, "n127");
      Prefix_List (64, R64, "n64");
      Prefix_List (40, R40, "n40");
      Prefix_List (1, R1, "n1");
      Prefix_List (0, R0, "n0");
      --  A one-element range at the end of a 127-element list walks 1
      --  term (a = 126, back from P_end) plus 0 (b = 127 is P_end), not
      --  the 125 terms of two forward walks from the block boundary at 64.
      Check ("n127_one_element_at_end_costs_1",
             Range_Cost (126, 127, 127) = 1
             and then Walks_Back (126, 127) and then Start_Pos (127, 127) = 127);
      Check ("n127_1_96_walks_back_31_from_p_end",
             Walks_Back (96, 127) and then Start_Pos (96, 127) = 127
             and then Walk_Len (96, 127) = 31
             and then Range_Cost (0, 96, 127) = 31);
      Check ("n127_tail_end_r_above_32_walks_back",
             Walks_Back (110, 127) and then Above (110, 127) = 127
             and then Walk_Len (110, 127) = 17);
      Check ("n150_worst_case_64",
             Range_Cost (32, 96, 150) = 64);
      --  The counts that Range_Sum reports (not only the formula):
      --  [127 .. 127] of 127 costs 1 Add, [1 .. 96] of 127 walks back 31
      --  terms from P_end, and [33 .. 96] of 150 is the worst case, 64.
      --  Each range costs one Sub.
      declare
         L127 : Hash_Array (1 .. 127);
         P127 : Acc_Array (1 .. 2);
         L    : Hash_Array (1 .. 150);
         P    : Acc_Array (1 .. 3);
         Got  : Acc;
         Adds, Subs : Natural;
      begin
         for I in L127'Range loop
            L127 (I) := H (1000 + I);
         end loop;
         for I in L'Range loop
            L (I) := H (1000 + I);
         end loop;
         Build_Prefix (L127, P127);
         Build_Prefix (L, P);
         Run_Range (L127, P127, 127, 127, Got, Adds, Subs);
         Check ("n127_one_element_at_end_counted_1_add_1_sub",
                Adds = 1 and then Subs = 1
                and then Got = Direct (L127, 127, 127));
         Run_Range (L127, P127, 1, 96, Got, Adds, Subs);
         Check ("n127_1_96_counted_31_adds_1_sub",
                Adds = 31 and then Subs = 1
                and then Got = Direct (L127, 1, 96));
         Run_Range (L, P, 33, 96, Got, Adds, Subs);
         Check ("n150_33_96_counted_64_adds_1_sub",
                Adds = 64 and then Subs = 1
                and then Got = Direct (L, 33, 96));
         --  The fingerprint of a range is fp of its records.
         Run_Range (L, P, 61, 100, Got, Adds, Subs);
         Check ("range_fp_is_fp_of_records",
                Fp (40, Got) = Fingerprint (Digest_Of (L (61 .. 100)))
                and then Adds = End_Cost (60, 150) + End_Cost (100, 150)
                and then Subs = 1);
      end;
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
         Check ("models_add" & I'Image & "_ok", R = D_OK);
         N := N + 1;
      end loop;
      Check ("models_after_adds", Count (S) = 5
             and then Same (S, Digest_Of (L (1 .. 5))));
      Lemma_Digest_Of_Models (L (1 .. 5));
      --  Remove the member at index 2, and shift the rest down.
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
         Lemma_Is_Perm_Intro (L, P, M, 4);
         Lemma_Is_Perm_Elim (L, P, M, 4);
         --  Is_Perm is ghost, so the test asserts it (Runner reports a
         --  failure).
         pragma Assert (Is_Perm (L, P, M, 4));
         pragma Assert (not Is_Perm (L, P, [1, 1, 3, 4, 5, 6, 7, 8], 4));
         Check ("is_perm_reverse_and_rejects_non_injective", True);
         Lemma_Models_Perm (S, L, P, M, 4);
         for I in 1 .. 4 loop
            Add_Record (S2, P (I), R);
            Check ("models_perm_add" & I'Image & "_ok", R = D_OK);
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
      --  Wire form of the fp input, and the congruences of
      --  Kome.Accumulator.
      Lemma_Fp_Input_Acc (3, Sum (Digest_Of (Fwd)));
      Lemma_Add_Congruent (Sum (S), Sum (S), Elem_Acc (H (1)), Elem_Acc (H (1)));
      Lemma_Sub_Congruent (Sum (S), Sum (S), Elem_Acc (H (1)), Elem_Acc (H (1)));
      Check ("fp_input_acc_is_to_bytes",
             Fp_Input (3, Sum (S)) (Acc_Pos .. Fp_Input_Len - 1)
               = To_Bytes (Sum (S)));
   end Models_Part;

   ---------------------------------------------------------------------------
   --  (i) Capacity: D_No_Space at |R| = Elem_Max
   ---------------------------------------------------------------------------

   --  To get to |R| = Elem_Max (2^20) by adds would take more than an
   --  hour under -gnata (about 5 ms for each Add_Record, measured), so
   --  the test restores the full state from its count and sum.
   procedure Capacity is
      A    : constant Key256 := H (1);
      B    : constant Key256 := H (2);
      Full : constant Digest_State := Restore (Elem_Max, Sum (Fold ([A, B])));
      S    : Digest_State := Full;
      R    : Digest_Status;
   begin
      --  Static, so the compiler knows it; the check records it.
      pragma Warnings (Off, "condition is always True");
      Check ("elem_max_is_frontier_held_max",
             Elem_Max = Kome.Frontier.Held_Max and then Elem_Max = 2**20);
      pragma Warnings (On, "condition is always True");
      Check ("restore_count_and_sum",
             Count (Full) = Elem_Max and then Sum (Full) = Sum (Fold ([A, B]))
             and then Fingerprint (Full) = Fp (Elem_Max, Sum (Full)));
      Add_Record (S, H (3), R);
      Check ("add_at_elem_max_is_no_space", R = D_No_Space);
      Check ("no_space_leaves_state_unchanged", Same (S, Full));
      Remove_Record (S, B, R);
      Check ("remove_at_elem_max_ok",
             R = D_OK and then Count (S) = Elem_Max - 1
             and then Sum (S) = Elem_Acc (A));
      Add_Record (S, B, R);
      Check ("add_back_to_elem_max_ok", R = D_OK and then Same (S, Full));
      Add_Record (S, B, R);
      Check ("add_past_elem_max_again_no_space",
             R = D_No_Space and then Same (S, Full));
      --  Just below the bound, one more record fits.
      S := Restore (Elem_Max - 1, Zero);
      Add_Record (S, A, R);
      Check ("add_at_elem_max_minus_1_ok",
             R = D_OK and then Count (S) = Elem_Max
             and then Sum (S) = Elem_Acc (A));
      --  And D_Empty from a restored empty state.
      S := Restore (0, Zero);
      Remove_Record (S, A, R);
      Check ("remove_from_restored_empty_refused",
             R = D_Empty and then Same (S, Empty));
   end Capacity;

   procedure Run_All is
   begin
      Vectors;
      State_Laws;
      Frontier_Part;
      Prefix_Sums;
      Models_Part;
      Capacity;
   end Run_All;

begin
   --  A Kome.Frontier.State holds Signers_Max * Slice_Max authorization
   --  rows. Under -gnata, each Post evaluation copies states, so the checks run
   --  in a task with a large stack (as in test_frontier). The block waits
   --  for the task.
   declare
      task Runner with Storage_Size => 512 * 1024 * 1024;

      task body Runner is
      begin
         Run_All;
      exception
         when E : others =>
            Put_Line ("FAIL unexpected exception: "
                      & Ada.Exceptions.Exception_Information (E));
            Failed := True;
      end Runner;
   begin
      null;
   end;
   if Failed then
      Set_Exit_Status (Failure);
   end if;
end Test_Digest;
