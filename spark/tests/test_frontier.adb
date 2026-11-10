--  Test main for Kome.Frontier: it tests the lattice core as the Lean
--  theorems and DESIGN.md §3, §4, §7 state it. Contracts and ghost lemmas
--  are evaluated at run time (-gnata) on each call. The tests include:
--  (a) admission by GRANT (D1′) and refusal without one; the admission
--      views Max_Ceil, In_W and W_Cap (SIMPLIFY.md S6);
--  (b) GRANT domination keyed by (issuer, subject) (D1′);
--  (c) roster domination as the product order (D3); REVOKE domination
--      keyed by (issuer, subject), the least from_t kept (S5);
--  (d) each refusal leaves the state unchanged (D11, T13);
--  (e) capacity rows: a data flood or a full slice takes no room from a
--      different row, and the founding key's REVOKE is held (E1, E2);
--  (f) expiry (D10): Expire;
--  (g) convergence: the same set in several orders, with duplicates and
--      records offered again, gives the same held set and views (T4);
--  (h) the sorted data row (AUDIT.md G25): insertion in the middle, an
--      entity with many fields, an entity's DEL at the start of its run,
--      replacement in place, and Expire keeps the order;
--  (i) payload tags, runs and slots (S14): a new record has its tag, the
--      others keep theirs, a data Apply changes only its run and an
--      authorization Apply only its slot;
--  (j) the ceiling cell (AUDIT.md H12; DESIGN.md §7): Raise_Ceil and
--      Set_Ceil_Tag keep the rows, only Max_Ceil reads the cell, no other
--      operation changes it, and with the capture rule of Kome.Store a
--      roster that a full slice or a full slot table refuses still raises
--      Max_Ceil, so the audit scenario gives the same Max_Ceil in both
--      arrival orders.
pragma Ada_2022;
with Ada.Text_IO;      use Ada.Text_IO;
with Ada.Command_Line; use Ada.Command_Line;
with Ada.Exceptions;   use Ada.Exceptions;
with Ada.Assertions;
with Ada.Strings.Fixed;
with Contract_Mode;    use Contract_Mode;
with Kome;             use Kome;
with Kome.Versions;    use Kome.Versions;
with Kome.Headers;     use Kome.Headers;
with Kome.Frontier;    use Kome.Frontier;

procedure Test_Frontier with SPARK_Mode => Off is

   Failed : Boolean := False;

   procedure Check (Name : String; Cond : Boolean) is
   begin
      Put_Line ((if Cond then "PASS " else "FAIL ") & Name);
      if not Cond then
         Failed := True;
      end if;
   end Check;

   Fnd : constant Byte := 9;                --  the founding key

   function Key (B : Byte) return Key256 is (others => Word (B));
   --  Keys beyond the 256 of Key, for full slices.
   function Key_N (N : Natural) return Key256 is (W0 => Word (N), W1 => 77, others => 0);
   function Hsh (B : Natural) return Key256 is (W0 => Word (B), others => 5);
   function Ent (B : Byte) return Id128 is (others => Word (B));
   function Fld (C : Character) return Key256 is
     (others => Word (Character'Pos (C)));

   function V (T : U48; A : Byte; Seq : U48; H : Natural) return Version is
     (T => T, Author => Key (A), Seq => Seq, H => Hsh (H));

   function Put (E : Byte; F : Character; Ver : Version) return Header is
     (K => K_Put, Ent => Ent (E), FH => Fld (F), V => Ver, Issuer => Zero_Key);

   function Del (E : Byte; Ver : Version) return Header is
     (K => K_Del, Ent => Ent (E), FH => Zero_Key, V => Ver, Issuer => Zero_Key);

   --  V = (ceiling_t, signer, gen, h), Issuer = signer.
   function Roster (Signer : Byte; Gen, Ceiling : U48; H : Natural) return Header is
     (K => K_Roster, Ent => Zero_Id, FH => Zero_Key,
      V => (T => Ceiling, Author => Key (Signer), Seq => Gen, H => Hsh (H)),
      Issuer => Key (Signer));

   --  V = (cap, subject, 0, h), Issuer = signer. The cap is unbounded
   --  unless Cap says otherwise.
   function Grant_K (Issuer : Byte; Subject : Key256; H : Natural; Cap : U48 := U48'Last)
     return Header is
     (K => K_Grant, Ent => Zero_Id, FH => Zero_Key,
      V => (T => Cap, Author => Subject, Seq => 0, H => Hsh (H)),
      Issuer => Key (Issuer));

   function Grant (Issuer, Subject : Byte; H : Natural; Cap : U48 := U48'Last) return Header is
     (Grant_K (Issuer, Key (Subject), H, Cap));

   --  V = (from_t, subject, 0, h), Issuer = signer.
   function Revoke (Issuer, Subject : Byte; From_T : U48; H : Natural) return Header is
     (K => K_Revoke, Ent => Zero_Id, FH => Zero_Key,
      V => (T => From_T, Author => Key (Subject), Seq => 0, H => Hsh (H)),
      Issuer => Key (Issuer));

   --  V = (from_t, subject, 0, h) for a subject beyond the 256 of Key.
   function Revoke_K (Issuer : Byte; Subject : Key256; From_T : U48; H : Natural)
     return Header is
     (K => K_Revoke, Ent => Zero_Id, FH => Zero_Key,
      V => (T => From_T, Author => Subject, Seq => 0, H => Hsh (H)),
      Issuer => Key (Issuer));

   function New_State (Cap : Data_Size := 64) return State is (Empty (Key (Fnd), Cap));

   --  A call that its precondition must refuse (run only when
   --  Contracts_On).
   Pre_Tag : constant String := "failed precondition from kome-frontier.ads";

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

   --  The two states have the same ceiling cell, tag included (Ceil_Same,
   --  read by the test).
   function Same_Cell (X, Y : State) return Boolean is
     (Has_Ceil (X) = Has_Ceil (Y)
      and then (if Has_Ceil (X)
                then Ceil_Held (X) = Ceil_Held (Y) and then Ceil_Tag (X) = Ceil_Tag (Y)));

   --  The rows of two states agree, tags included. This is how the test
   --  reads Same_Held, which is ghost.
   function Same_Rows (X, Y : State) return Boolean is
   begin
      if Kome.Frontier.Count (X) /= Kome.Frontier.Count (Y)
        or else Data_Count (X) /= Data_Count (Y)
        or else Slots_Used (X) /= Slots_Used (Y)
        or else Held_Ceil (X) /= Held_Ceil (Y)
      then
         return False;
      end if;
      for I in 1 .. Kome.Frontier.Count (X) loop
         if Held (X, I) /= Held (Y, I) or else Tag (X, I) /= Tag (Y, I) then
            return False;
         end if;
      end loop;
      for K in 1 .. Slots_Used (X) loop
         if Slot_Key (X, K) /= Slot_Key (Y, K) or else Slot_Count (X, K) /= Slot_Count (Y, K) then
            return False;
         end if;
      end loop;
      return True;
   end Same_Rows;

   --  Each public view of two states agrees, tags and the ceiling cell
   --  included. This is how the test reads Unchanged, which is ghost. The
   --  Post of Apply also checks Unchanged.
   function Same_State (X, Y : State) return Boolean is
     (Same_Rows (X, Y) and then Same_Cell (X, Y) and then Max_Ceil (X) = Max_Ceil (Y));

   --  The keys on which the tests compare W and wcap.
   type Key_List is array (Positive range <>) of Byte;
   Probe_Keys : constant Key_List := [1, 2, 9, 21, 50, 54, 61];

   --  Held sets as unordered collections, and the same admission views.
   --  (Not Kome.Frontier.Same_Held, which compares the rows in order.)
   function Same_Set (X, Y : State) return Boolean is
   begin
      if Kome.Frontier.Count (X) /= Kome.Frontier.Count (Y) then
         return False;
      end if;
      for I in 1 .. Kome.Frontier.Count (X) loop
         if not Holds (Y, Held (X, I)) then
            return False;
         end if;
      end loop;
      return Max_Ceil (X) = Max_Ceil (Y)
        and then (for all K of Probe_Keys =>
                    In_W (X, Key (K)) = In_W (Y, Key (K))
                    and then W_Cap (X, Key (K)) = W_Cap (Y, Key (K)));
   end Same_Set;

   --  The data row is strictly increasing in (ent, kind, fh), the
   --  entity-major key of Kome.Frontier (AUDIT.md G25).
   function Key_Below (A, B : Header) return Boolean is
     (A.Ent.W0 < B.Ent.W0
      or else (A.Ent.W0 = B.Ent.W0
               and then (A.Ent.W1 < B.Ent.W1
                         or else (A.Ent.W1 = B.Ent.W1
                                  and then (A.Ent.W2 < B.Ent.W2
                                            or else (A.Ent.W2 = B.Ent.W2
                                                     and then A.Ent.W3 < B.Ent.W3)))))
      or else (A.Ent = B.Ent
               and then (A.K < B.K or else (A.K = B.K and then Kome.Lt (A.FH, B.FH)))));

   function Row_Sorted (S : State) return Boolean is
     (for all I in 1 .. Data_Count (S) - 1 =>
        Key_Below (Data_Held (S, I), Data_Held (S, I + 1)));

   --  Each Apply gets a fresh tag.
   Next_Tag : U64 := 1000;

   --  Apply with a fresh tag, and check that a refusal or a duplicate
   --  changed nothing, that a new hold has its tag, and the run and slot
   --  lemmas.
   procedure App (S : in out State; R : Header; St : out Status) is
      Before : constant State := S;
      Was    : constant Boolean := Holds (S, R);
      T      : constant U64 := Next_Tag;
   begin
      Next_Tag := Next_Tag + 1;
      Apply (S, R, T, St);
      pragma Assert (Is_Frontier (S));
      if not Same_Cell (Before, S) then
         Check ("Apply left the ceiling cell as it was", False);
      end if;
      if St /= OK or else Was then
         pragma Assert (Unchanged (Before, S));
         Lemma_Unchanged (Before, S);   --  executable: runs under -gnata
         if not Same_State (Before, S) then
            Check ("refusal or duplicate left the state unchanged", False);
         end if;
      else
         if Tag_Of (S, R) /= T then
            Check ("a new record has its tag", False);
         end if;
         if Is_Data (R) then
            Lemma_Outside_Run (Before, S, R.Ent);
         else
            Lemma_Outside_Slot (Before, S, R.Issuer);
         end if;
         for K of Probe_Keys loop
            Lemma_Views_Step (Before, S, R, Key (K));
         end loop;
         Lemma_Views_Step (Before, S, R, R.V.Author);
      end if;
   end App;

   --  The capture rule of Kome.Store.Put_Frame, on the state alone
   --  (DESIGN.md §7; AUDIT.md H12): Apply, and a roster that Apply refuses
   --  for room (Auth_Full) and whose ceiling is above maxceil goes to the
   --  ceiling cell. Captured says that the cell took R. Whatever the
   --  outcome, maxceil is the old maxceil joined with R's ceiling (T19,
   --  the step).
   procedure Offer (S : in out State; R : Header; St : out Status; Captured : out Boolean) is
      M : constant U48 := Max_Ceil (S);
   begin
      Captured := False;
      App (S, R, St);
      if St = Auth_Full and then Raises_Ceil (S, R) then
         Raise_Ceil (S, R, Next_Tag);
         Next_Tag := Next_Tag + 1;
         Captured := True;
      end if;
      if Max_Ceil (S) /= U48'Max (M, Ceil_Of (R)) then
         Check ("an offer joins maxceil with the record's ceiling", False);
      end if;
   end Offer;

   --  Each lemma on each index of a state. Each lemma's Is_Frontier
   --  precondition costs O(Count^2) at run time, so on a large state (a
   --  full slice) only the whole-state lemmas run.
   procedure Lemmas (S : State) is
      Small : constant Boolean := Kome.Frontier.Count (S) <= 64;
   begin
      Lemma_Unchanged_Refl (S);
      Lemma_Unchanged (S, S);
      Lemma_Same_Held (S, S);
      Lemma_Frontier_Shape (S);
      Lemma_Held_Ceil_Def (S);
      Lemma_Max_Ceil_Def (S);
      if Has_Ceil (S) then
         Lemma_Frontier_Ceil (S);
      end if;
      for I in 1 .. (if Small then Kome.Frontier.Count (S) else 0) loop
         Lemma_Held_Cases (S, I);
         Lemma_Frontier_Held (S, I);
         Lemma_Tag_Of (S, I);
         if Held (S, I).K = K_Grant then
            Lemma_In_W_Def (S, Held (S, I).V.Author);
            Lemma_W_Cap_Def (S, Held (S, I).V.Author);
         end if;
      end loop;
      for I in 1 .. (if Small then Data_Count (S) else 0) loop
         Lemma_Held_Data (S, I);
         Lemma_Frontier_Data (S, I);
         Lemma_Run_Def (S, Data_Held (S, I).Ent);
      end loop;
      Lemma_Run_Def (S, Ent (200));
      for K in 1 .. Slots_Used (S) loop
         Lemma_Slot_Def (S, Slot_Key (S, K));
         for J in 1 .. (if Small then Slot_Count (S, K) else 0) loop
            Lemma_Held_Auth (S, K, J);
            Lemma_Frontier_Auth (S, K, J);
         end loop;
      end loop;
      Lemma_Slot_Def (S, Key (250));
      for K of Probe_Keys loop
         Lemma_In_W_Def (S, Key (K));
         Lemma_W_Cap_Def (S, Key (K));
         Lemma_Same_Auth_Views (S, S, Key (K));
      end loop;
   end Lemmas;

   type Header_List is array (Positive range <>) of Header;

   --  A complete reconciliation: the holder of a refused record offers it
   --  again (DESIGN.md §4), so Run applies the list in passes until a pass
   --  holds no new record. Admission is monotone, so this stops (T4).
   function Run (L : Header_List) return State is
      S        : State := New_State;
      St       : Status;
      Progress : Boolean := True;
   begin
      while Progress loop
         Progress := False;
         for I in L'Range loop
            declare
               Before : constant Boolean := Holds (S, L (I));
            begin
               App (S, L (I), St);
               if St = OK and then not Before then
                  Progress := True;
               end if;
            end;
         end loop;
      end loop;
      return S;
   end Run;

   --  A State holds its rows inline, so it is large. Under -gnata, each
   --  Post evaluation copies states, so the checks run in a task with a
   --  large stack.
   procedure Run_All;

   task Runner with Storage_Size => 512 * 1024 * 1024;

   task body Runner is
   begin
      Run_All;
   exception
      when E : others =>
         Put_Line ("FAIL unexpected exception: " & Exception_Information (E));
         Set_Exit_Status (Failure);
   end Runner;

   procedure Run_All is
   St : Status;
begin
   --  Header lemmas on hand-built records.
   declare
      R1 : constant Header := Roster (Fnd, 1, 5000, 1);
      R2 : constant Header := Roster (Fnd, 2, 6000, 2);
      G1 : constant Header := Grant (Fnd, 1, 31);
      G2 : constant Header := Grant (Fnd, 1, 40);
      P1 : constant Header := Put (1, 'n', V (100, 1, 1, 10));
      D1 : constant Header := Del (1, V (300, 2, 2, 13));
   begin
      Lemma_Roster_Dom (R1, R2);
      Lemma_Grant_Dom (G1, G2);
      Lemma_Dominator_Same_Key (R2, R1);
      Lemma_Same_Row (D1, P1);
      Lemma_Same_Row (G2, G1);
      Lemma_Dominates_Trans (P1, Put (1, 'n', V (200, 1, 1, 11)), D1);
      Check ("header lemmas evaluated",
             Dominates (R2, R1) and then Dominates (G2, G1) and then Dominates (D1, P1)
             and then Canonical (R1) and then Canonical (G1) and then Canonical (D1));
   end;

   --  (a) Admission by GRANT.
   declare
      S  : State := New_State;
      P1 : constant Header := Put (1, 'n', V (100, 1, 1, 10));
   begin
      Check ("empty: slot 1 is the founding key",
             Slots_Used (S) = 1 and then Slot_Key (S, 1) = Key (Fnd)
             and then Kome.Frontier.Count (S) = 0 and then Is_Frontier (S));
      App (S, Roster (Fnd, 1, 5000, 1), St);
      Check ("roster held, ceiling raised", St = OK and then Max_Ceil (S) = 5000
             and then not In_W (S, Key (1)));
      App (S, P1, St);
      Check ("PUT by a key without a GRANT is Inadmissible",
             St = Inadmissible and then not Holds (S, P1));
      App (S, Grant (Fnd, 1, 31), St);
      Check ("GRANT held, subject is a writer",
             St = OK and then In_W (S, Key (1)) and then not In_W (S, Key (2)));
      App (S, P1, St);
      Check ("a GRANT admits its subject", St = OK and then Holds (S, P1));
      App (S, P1, St);
      Check ("duplicate is a no-op and OK", St = OK and then Kome.Frontier.Count (S) = 3);
      App (S, Put (2, 'n', V (9000, 1, 2, 11)), St);
      Check ("PUT above the ceiling is Inadmissible", St = Inadmissible);
      Lemmas (S);
      --  Lemmas ran Lemma_Unchanged_Refl and Lemma_Unchanged (S, S). App
      --  ran Lemma_Unchanged after each refusal and duplicate. The two
      --  lemmas are executable (bounded quantifiers) and returned.
      Lemma_Unchanged_Refl (S);
      Lemma_Unchanged (S, S);
      Check ("Lemma_Unchanged_Refl and Lemma_Unchanged execute (3 held)",
             Kome.Frontier.Count (S) = 3);
   end;

   --  (a') A1: the write cap. A GRANT by a certified root caps its
   --  subject at the root's cap; a second GRANT with a larger cap raises
   --  wcap, and a GRANT with a smaller cap and a greater h does not evict
   --  the larger one.
   declare
      S   : State := New_State;
      GC  : constant Header := Grant (21, 1, 51, Cap => 4000);
      GC2 : constant Header := Grant (21, 1, 52, Cap => 4500);
      GC3 : constant Header := Grant (21, 1, 53, Cap => 1000);
      P   : constant Header := Put (1, 'n', V (4500, 1, 1, 10));
      Q   : constant Header := Put (1, 'n', V (4000, 1, 2, 11));
   begin
      App (S, Roster (Fnd, 1, 5000, 1), St);
      App (S, GC, St);
      Check ("A1: a capped GRANT admits its subject up to the cap",
             St = OK and then In_W (S, Key (1))
             and then W_Cap (S, Key (1)) = 4000
             and then Admitted (S, Q) and then not Admitted (S, P));
      App (S, P, St);
      Check ("A1: a PUT above the writer's cap is Inadmissible although below maxceil",
             St = Inadmissible and then not Holds (S, P));
      Lemma_W_Cap_Def (S, Key (1));
      App (S, GC2, St);
      Check ("A1: a GRANT with a larger cap raises wcap and admits the PUT",
             St = OK and then W_Cap (S, Key (1)) = 4500 and then Admitted (S, P)
             and then not Holds (S, GC));
      App (S, GC3, St);
      Check ("A1: a GRANT with a smaller cap does not evict the larger one; wcap stays",
             St = OK and then Holds (S, GC3) and then Holds (S, GC2)
             and then W_Cap (S, Key (1)) = 4500);
      Lemma_W_Cap_Def (S, Key (1));
      Lemmas (S);
   end;

   --  (b) GRANT domination is keyed by (issuer, subject).
   declare
      S   : State := New_State;
      GF  : constant Header := Grant (Fnd, 1, 31);
      GA  : constant Header := Grant (21, 1, 32);
      GF2 : constant Header := Grant (Fnd, 1, 40);
      GF0 : constant Header := Grant (Fnd, 1, 20);
   begin
      App (S, GF, St);
      App (S, GA, St);
      Check ("two GRANTs of one subject by different issuers are both held",
             St = OK and then Holds (S, GF) and then Holds (S, GA)
             and then Slots_Used (S) = 2 and then Slot_Of (S, Key (21)) = 2
             and then In_W (S, Key (1)) and then not In_W (S, Key (21)));
      App (S, GF2, St);
      Check ("the same issuer's higher-h GRANT dominates",
             St = OK and then Holds (S, GF2) and then not Holds (S, GF)
             and then Holds (S, GA) and then In_W (S, Key (1)));
      App (S, GF0, St);
      Check ("a lower-h GRANT of the same issuer is Dominated", St = Dominated);
      Lemmas (S);
   end;

   --  (c) Roster domination is the product order.
   declare
      S  : State := New_State;
      R1 : constant Header := Roster (Fnd, 1, 5000, 1);
      R2 : constant Header := Roster (Fnd, 2, 6000, 2);
      RS : constant Header := Roster (Fnd, 1, 9000, 3);    --  stale: lower gen, higher ceiling
      R3 : constant Header := Roster (Fnd, 3, 5500, 4);    --  higher gen, lower ceiling
      R4 : constant Header := Roster (Fnd, 4, 9000, 5);    --  higher gen, ceiling >= all
   begin
      App (S, R1, St);
      App (S, R2, St);
      Check ("higher gen and ceiling >= dominates", St = OK and then not Holds (S, R1));
      App (S, RS, St);
      Check ("a stale roster is held beside the newer one",
             St = OK and then Holds (S, RS) and then Holds (S, R2)
             and then not Dominates (RS, R2) and then not Dominates (R2, RS)
             and then Max_Ceil (S) = 9000);
      App (S, R3, St);
      Check ("a roster with higher gen and lower ceiling does not dominate",
             St = OK and then Holds (S, R3) and then Holds (S, R2) and then Holds (S, RS));
      Lemmas (S);
      App (S, R4, St);
      Check ("a roster with higher gen and ceiling >= dominates the antichain",
             St = OK and then Holds (S, R4) and then not Holds (S, R2)
             and then not Holds (S, RS) and then not Holds (S, R3)
             and then Max_Ceil (S) = 9000);
      App (S, R2, St);
      Check ("a roster dominated on arrival is Dominated and changes nothing",
             St = Dominated and then not Holds (S, R2) and then Max_Ceil (S) = 9000);
      App (S, Roster (Fnd, 2, 20_000, 6), St);
      Check ("a stale-gen roster with a higher ceiling is held and raises the ceiling",
             St = OK and then Max_Ceil (S) = 20_000);
      Lemmas (S);
   end;

   --  (c') REVOKE domination (S5): keyed by (issuer, subject); the least
   --  from_t is kept, an equal from_t is decided by h.
   declare
      S  : State := New_State;
      X1 : constant Header := Revoke (Fnd, 1, 50, 60);
      X2 : constant Header := Revoke (Fnd, 1, 10, 61);   --  lower from_t
      X3 : constant Header := Revoke (Fnd, 1, 100, 62);  --  higher from_t
      X4 : constant Header := Revoke (Fnd, 1, 10, 63);   --  equal from_t, greater h
      X5 : constant Header := Revoke (21, 1, 100, 64);   --  another issuer
   begin
      App (S, X1, St);
      App (S, X2, St);
      Check ("a REVOKE with a lower from_t replaces the key's REVOKE",
             St = OK and then Holds (S, X2) and then not Holds (S, X1));
      App (S, X3, St);
      Check ("a REVOKE with a higher from_t is Dominated", St = Dominated);
      App (S, X4, St);
      Check ("an equal from_t with a greater h replaces it",
             St = OK and then Holds (S, X4) and then not Holds (S, X2));
      App (S, X5, St);
      Check ("another issuer's REVOKE of the same subject is held beside it",
             St = OK and then Holds (S, X5) and then Holds (S, X4));
      Lemmas (S);
   end;

   --  (d)+(e) Data flood, then the founding key's REVOKE.
   declare
      S : State := New_State (Cap => 8);
      Before : State := New_State (Cap => 8);
      Extra  : constant Header := Put (99, 'z', V (900, 1, 99, 99));
   begin
      App (S, Roster (Fnd, 1, 5000, 1), St);
      App (S, Grant (Fnd, 1, 31), St);
      for I in 1 .. 8 loop
         App (S, Put (Byte (I), 'a', V (U48 (100 + I), 1, U48 (I), 100 + I)), St);
      end loop;
      Check ("data flood fills Cap", St = OK and then Data_Count (S) = 8);
      Before := S;
      App (S, Extra, St);
      Check ("a full data row refuses with No_Space and changes nothing",
             St = No_Space and then Same_State (Before, S) and then not Holds (S, Extra));
      App (S, Revoke (Fnd, 1, 0, 77), St);
      Check ("after a data flood the founding key's REVOKE returns OK",
             St = OK and then Holds (S, Revoke (Fnd, 1, 0, 77)));
      App (S, Del (1, V (500, 1, 50, 120)), St);
      Check ("a DEL that frees its entity's PUT is held in a full row", St = OK);
      Before := S;
      App (S, Put (1, 'a', V (101, 1, 1, 101)), St);
      Check ("a dominated record never needs room: Dominated, unchanged",
             St = Dominated and then Same_State (Before, S));
      Lemmas (S);
   end;

   --  (e) Slices: one signer's slice is full. Records of other
   --  signers are still held.
   declare
      S      : State := New_State (Cap => 8);
      Before : State := New_State (Cap => 8);
   begin
      --  Apply, not App: App's lemma calls would make the fill cubic.
      for I in 0 .. Slice_Max - 1 loop
         Apply (S, Grant_K (21, Key_N (I), 2000 + I), U64 (I), St);
         pragma Assert (St = OK);
      end loop;
      Check ("a root's slice fills",
             St = OK and then Slot_Count (S, Slot_Of (S, Key (21))) = Slice_Max);
      Before := S;
      App (S, Grant_K (21, Key_N (Slice_Max), 2000 + Slice_Max), St);
      Check ("Auth_Full when the signer's slice is full, nothing changed",
             St = Auth_Full and then Same_State (Before, S)
             and then not In_W (S, Key_N (Slice_Max)));
      App (S, Grant_K (21, Key_N (0), 9000), St);
      Check ("a full slice still takes a record that frees one",
             St = OK and then not Holds (S, Grant_K (21, Key_N (0), 2000))
             and then Slot_Count (S, Slot_Of (S, Key (21))) = Slice_Max);
      App (S, Grant (22, 60, 300), St);
      Check ("another signer's records land beside a full slice", St = OK);
      App (S, Grant (Fnd, 61, 301), St);
      App (S, Revoke (Fnd, 21, 0, 302), St);
      Check ("the founding key's records land beside a full slice",
             St = OK and then Holds (S, Grant (Fnd, 61, 301)));
      Lemmas (S);
   end;

   --  (e) Slots: all 16 used.
   declare
      S      : State := New_State (Cap => 4);
      Before : State := New_State (Cap => 4);
   begin
      for I in 0 .. 14 loop
         App (S, Grant (Byte (30 + I), Byte (100 + I), 400 + I), St);
      end loop;
      Check ("15 certified roots take slots 2 .. 16",
             St = OK and then Slots_Used (S) = Signers_Max
             and then Slot_Of (S, Key (44)) = 16 and then Slot_Of (S, Key (45)) = 0);
      Before := S;
      App (S, Grant (45, 120, 500), St);
      Check ("Auth_Full when all 16 slots are used, nothing changed",
             St = Auth_Full and then Same_State (Before, S));
      App (S, Grant (Fnd, 121, 501), St);
      Check ("the founding key's slot is always there", St = OK);
      App (S, Grant (37, 122, 502), St);
      Check ("a known root still lands in its slot", St = OK);
      Lemmas (S);
   end;

   --  (f) Expire removes exactly the expired DELs.
   declare
      S  : State := New_State;
      D1 : constant Header := Del (1, V (100, 1, 1, 1));
      D2 : constant Header := Del (2, V (200, 1, 2, 2));
      D3 : constant Header := Del (3, V (300, 1, 3, 3));
      P1 : constant Header := Put (4, 'a', V (150, 1, 4, 4));
      P2 : constant Header := Put (5, 'a', V (250, 1, 5, 5));
      G  : constant Header := Grant (Fnd, 1, 6);
   begin
      App (S, Roster (Fnd, 1, 5000, 7), St);
      App (S, G, St);
      for R of Header_List'[D1, D2, D3, P1, P2] loop
         App (S, R, St);
      end loop;
      Expire (S, 99);
      Check ("Expire below every DEL removes nothing", Kome.Frontier.Count (S) = 7);
      Expire (S, 200);
      Check ("Expire removes exactly the expired DELs",
             not Holds (S, D1) and then not Holds (S, D2) and then Holds (S, D3)
             and then Holds (S, P1) and then Holds (S, P2) and then Holds (S, G)
             and then Kome.Frontier.Count (S) = 5 and then Max_Ceil (S) = 5000);
      Lemmas (S);
   end;

   --  (g) Convergence (T4): several orders and duplications of one set.
   declare
      R1  : constant Header := Roster (Fnd, 1, 5000, 1);
      R2  : constant Header := Roster (Fnd, 2, 10_000, 2);
      G1  : constant Header := Grant (Fnd, 1, 31);
      G2  : constant Header := Grant (21, 2, 32);
      P1  : constant Header := Put (1, 'n', V (100, 1, 1, 10));
      P2  : constant Header := Put (1, 'n', V (200, 2, 1, 11));   --  beats P1
      P3  : constant Header := Put (1, 'a', V (150, 1, 2, 12));   --  other field
      D1  : constant Header := Del (1, V (300, 2, 2, 13));        --  beats P1..P3
      P4  : constant Header := Put (1, 'n', V (400, 1, 3, 14));   --  re-creates
      X1  : constant Header := Revoke (Fnd, 2, 250, 15);
      Far : constant Header := Put (2, 'n', V (9000, 1, 4, 16));  --  needs R2
      O1 : constant Header_List := [R1, G1, G2, P1, P2, P3, D1, P4, X1, Far, R2];
      O2 : constant Header_List := [R2, Far, X1, P4, D1, P3, P2, P1, G2, G1, R1];
      O3 : constant Header_List := [P4, D1, R1, R1, P2, Far, G1, R2, P1, X1, P3, Far, D1, G2];
      O4 : constant Header_List := [Far, Far, R1, P3, X1, R2, P1, P2, D1, P4, P4, G2, G1];
      A  : constant State := Run (O1);
      B  : constant State := Run (O2);
      C  : constant State := Run (O3);
      D  : constant State := Run (O4);
   begin
      Check ("orders 1 and 2 converge", Same_Set (A, B));
      Check ("orders 1 and 3 converge (duplicates)", Same_Set (A, C));
      Check ("orders 1 and 4 converge (duplicates)", Same_Set (A, D));
      Check ("final frontier is {R2, G1, G2, D1, P4, X1, Far}",
             Kome.Frontier.Count (A) = 7 and then Holds (A, R2) and then Holds (A, G1)
             and then Holds (A, G2) and then Holds (A, D1) and then Holds (A, P4)
             and then Holds (A, X1) and then Holds (A, Far));
      Check ("registers converge",
             Max_Ceil (A) = 10_000 and then In_W (A, Key (1)) and then In_W (A, Key (2))
             and then not In_W (A, Key (21)));
      Lemmas (A);
   end;

   --  Is_Frontier after each step of a long mixed run.
   declare
      Mixed : constant Header_List :=
        [Put (1, 'n', V (100, 1, 1, 10)), Roster (Fnd, 1, 5000, 1),
         Grant (Fnd, 1, 31), Put (1, 'n', V (100, 1, 1, 10)),
         Roster (Fnd, 1, 9000, 3), Roster (Fnd, 2, 6000, 2),
         Del (1, V (300, 1, 2, 13)), Revoke (Fnd, 1, 250, 15),
         Grant (21, 1, 32), Grant (Fnd, 1, 40), Put (1, 'a', V (400, 1, 3, 14)),
         Roster (21, 7, 4000, 20), Roster (Fnd, 3, 9000, 4)];
      T  : State := New_State (Cap => 16);
      Ok : Boolean := True;
   begin
      for I in Mixed'Range loop
         App (T, Mixed (I), St);
         Ok := Ok and then Is_Frontier (T);
      end loop;
      Check ("Is_Frontier after every apply", Ok);
      Lemmas (T);
   end;

   --  (h) The data row is sorted entity-major by (ent, kind, fh)
   --  (AUDIT.md G25): an entity's DEL starts its run, its PUTs follow by
   --  field, and Apply finds them with one binary search.
   declare
      S     : State := New_State (Cap => 64);
      Order : constant String := "qhcmatrjbklsdfognpei";   --  20 fields
      N0    : Natural;
      P0    : Natural := 0;
      Up    : constant Header := Put (2, 'c', V (500, 1, 60, 700));
      Mid   : constant Header := Put (2, 'h', V (510, 1, 61, 701));   --  'h' was dropped
   begin
      App (S, Roster (Fnd, 1, 50_000, 1), St);
      App (S, Grant (Fnd, 1, 31), St);
      App (S, Put (5, 'a', V (100, 1, 1, 10)), St);
      App (S, Put (1, 'a', V (100, 1, 2, 11)), St);
      App (S, Put (3, 'b', V (100, 1, 3, 12)), St);
      App (S, Put (3, 'a', V (100, 1, 4, 13)), St);
      Check ("insertion in the middle keeps the row sorted",
             Data_Count (S) = 4 and then Row_Sorted (S)
             and then Data_Held (S, 1).Ent = Ent (1)
             and then Data_Held (S, 2) = Put (3, 'a', V (100, 1, 4, 13))
             and then Data_Held (S, 3) = Put (3, 'b', V (100, 1, 3, 12))
             and then Data_Held (S, 4).Ent = Ent (5));

      --  An entity with many fields, applied out of order.
      for I in Order'Range loop
         App (S, Put (2, Order (I), V (U48 (100 + I), 1, U48 (I), 200 + I)), St);
      end loop;
      Check ("an entity with 20 fields: all held, row sorted, run contiguous",
             St = OK and then Data_Count (S) = 24 and then Row_Sorted (S)
             and then (for all I in 2 .. 21 => Data_Held (S, I).Ent = Ent (2))
             and then Data_Held (S, 1).Ent = Ent (1)
             and then Data_Held (S, 22).Ent = Ent (3));

      --  A field update replaces its cell in place.
      for I in 1 .. Data_Count (S) loop
         if Data_Held (S, I).Ent = Ent (2) and then Data_Held (S, I).FH = Fld ('c') then
            P0 := I;
         end if;
      end loop;
      N0 := Data_Count (S);
      App (S, Up, St);
      Check ("a newer PUT of a held cell takes the cell's place",
             St = OK and then Data_Count (S) = N0 and then P0 /= 0
             and then Data_Held (S, P0) = Up and then Row_Sorted (S));

      --  A DEL of the wide entity: held at the start of its run, drops the
      --  older PUTs (t <= 110: the first 10 of Order) and keeps the others.
      App (S, Del (2, V (110, 1, 50, 900)), St);
      Check ("the DEL starts its entity's run and drops only older PUTs",
             St = OK and then Data_Count (S) = 1 + 1 + 11 + 2 + 1
             and then Data_Held (S, 2) = Del (2, V (110, 1, 50, 900))
             and then (for all I in 3 .. 13 =>
                         Data_Held (S, I).Ent = Ent (2) and then Data_Held (S, I).K = K_Put)
             and then Row_Sorted (S));
      App (S, Put (2, 'z', V (105, 1, 70, 902)), St);
      Check ("a PUT older than its entity's DEL is Dominated",
             St = Dominated and then Data_Count (S) = 16);
      App (S, Put (2, 'q', V (101, 1, 1, 201)), St);
      Check ("a PUT that the DEL dropped is Dominated when offered again",
             St = Dominated and then Data_Count (S) = 16);
      App (S, Mid, St);
      Check ("a new field in the middle of a run is inserted in order",
             St = OK and then Data_Count (S) = 17 and then Holds (S, Mid)
             and then Row_Sorted (S));

      --  A newer DEL replaces the DEL and drops more PUTs.
      App (S, Del (2, V (115, 1, 51, 903)), St);
      Check ("a newer DEL replaces the DEL at the run start",
             St = OK and then Data_Held (S, 2) = Del (2, V (115, 1, 51, 903))
             and then not Holds (S, Del (2, V (110, 1, 50, 900)))
             and then Data_Count (S) = 17 - 6 + 1 and then Row_Sorted (S));

      --  A DEL of entity 3 replaces its run, then Expire removes it (the
      --  path of a DEL that arrives expired: Kome.Store applies, then
      --  expires).
      App (S, Del (3, V (120, 1, 52, 904)), St);
      Check ("a DEL replaces the run of entity 3 and keeps the row sorted",
             St = OK and then Data_Count (S) = 12 - 2 + 1 and then Row_Sorted (S)
             and then Data_Held (S, Data_Count (S)).Ent = Ent (5));
      Expire (S, 200);
      Check ("Expire removes the DELs and keeps the row sorted",
             Data_Count (S) = 9 and then Row_Sorted (S)
             and then Data_Held (S, 2).K = K_Put);
      Lemmas (S);
   end;

   --  (i) Tags, runs and slots (S14).
   declare
      S      : State := New_State (Cap => 16);
      Before : State := New_State (Cap => 16);
      P2     : constant Header := Put (2, 'a', V (100, 1, 1, 10));
      P2b    : constant Header := Put (2, 'b', V (100, 1, 2, 11));
      P1     : constant Header := Put (1, 'a', V (100, 1, 3, 12));
      P3     : constant Header := Put (3, 'a', V (100, 1, 4, 13));
      D2     : constant Header := Del (2, V (150, 1, 5, 14));
   begin
      App (S, Roster (Fnd, 1, 5000, 1), St);
      App (S, Grant (Fnd, 1, 31), St);
      Apply (S, P2, 7, St);
      Apply (S, P1, 8, St);
      Apply (S, P3, 9, St);
      Apply (S, P2b, 10, St);
      Check ("each record has the tag it was applied with",
             Tag_Of (S, P2) = 7 and then Tag_Of (S, P1) = 8 and then Tag_Of (S, P3) = 9
             and then Tag_Of (S, P2b) = 10 and then Tag_Of (S, D2) = 0);
      Check ("Run gives the entity's data rows",
             Run (S, Ent (2)).First = 2 and then Run (S, Ent (2)).Last = 3
             and then Run (S, Ent (1)).First = 1 and then Run (S, Ent (1)).Last = 1
             and then Run (S, Ent (4)).First = 5 and then Run (S, Ent (4)).Last = 4);
      Check ("Slot gives the signer's rows",
             Slot (S, Key (Fnd)).First = Data_Count (S) + 1
             and then Slot (S, Key (Fnd)).Last = Kome.Frontier.Count (S)
             and then Slot (S, Key (21)).First = Kome.Frontier.Count (S) + 1);
      Apply (S, P2, 99, St);
      Check ("a duplicate keeps its old tag", St = OK and then Tag_Of (S, P2) = 7);
      Before := S;
      Apply (S, D2, 11, St);
      Lemma_Outside_Run (Before, S, Ent (2));
      Check ("a DEL replaces its run; the other records keep their tags",
             St = OK and then Run (S, Ent (2)).First = 2 and then Run (S, Ent (2)).Last = 2
             and then Data_Held (S, 2) = D2 and then Data_Tag (S, 2) = 11
             and then Tag_Of (S, P1) = 8 and then Tag_Of (S, P3) = 9
             and then Data_Held (S, 3) = P3);
      Expire (S, 120);
      Check ("Expire keeps the survivors' tags",
             Holds (S, D2) and then Tag_Of (S, D2) = 11 and then Tag_Of (S, P3) = 9);
      Expire (S, 150);
      Check ("Expire at t = 150 removes the DEL",
             not Holds (S, D2) and then Tag_Of (S, P1) = 8 and then Tag_Of (S, P3) = 9);
      Lemmas (S);
   end;

   --  (j) The ceiling cell (AUDIT.md H12; DESIGN.md §7).
   --  F1 - F4: Raise_Ceil, Set_Ceil_Tag and the cell across every other
   --  operation, on a small state.
   declare
      S      : State := New_State (Cap => 8);
      Before : State := New_State (Cap => 8);
      R1  : constant Header := Roster (Fnd, 1, 5000, 1);
      G1  : constant Header := Grant (Fnd, 1, 31);
      P1  : constant Header := Put (1, 'a', V (100, 1, 1, 10));
      D2  : constant Header := Del (2, V (200, 1, 2, 11));
      Far : constant Header := Put (3, 'a', V (6000, 1, 3, 12));   --  above R1's ceiling
      RC  : constant Header := Roster (21, 3, 7000, 2);            --  for the cell
      R17 : constant Header := Roster (46, 1, 8000, 3);            --  a 17th signer
      Took : Boolean;
   begin
      App (S, R1, St);
      App (S, G1, St);
      App (S, P1, St);
      App (S, D2, St);
      Check ("before a raise: no cell, maxceil is the held ceiling",
             not Has_Ceil (S) and then Ceil_Value (S) = 0 and then not Ceil_Live (S)
             and then Max_Ceil (S) = 5000 and then Held_Ceil (S) = 5000
             and then Raises_Ceil (S, RC) and then not Raises_Ceil (S, R1)
             and then not Raises_Ceil (S, Grant (21, 1, 32, Cap => 9000))
             and then not Admitted (S, Far));

      --  F1. Raise_Ceil.
      Before := S;
      Raise_Ceil (S, RC, 4242);
      pragma Assert (Is_Frontier (S));
      pragma Assert (Kome.Frontier.Same_Held (Before, S));
      Lemma_Same_Held (Before, S);
      pragma Assert (not Unchanged (Before, S));
      Lemma_Held_Ceil_Def (S);
      Lemma_Max_Ceil_Def (S);
      Lemma_Frontier_Ceil (S);
      Check ("Raise_Ceil: the cell holds the roster and its tag",
             Has_Ceil (S) and then Ceil_Held (S) = RC and then Ceil_Tag (S) = 4242
             and then Ceil_Value (S) = 7000);
      Check ("Raise_Ceil: maxceil is the roster's ceiling, the held ceiling stays",
             Max_Ceil (S) = Ceil_Of (RC) and then Max_Ceil (S) = 7000
             and then Held_Ceil (S) = 5000 and then Ceil_Live (S));
      Check ("Raise_Ceil: the rows are the same, and the roster is not held",
             Same_Rows (Before, S) and then not Holds (S, RC)
             and then Slot_Of (S, Key (21)) = 0 and then Tag_Of (S, RC) = 0
             and then Kome.Frontier.Count (S) = 4);
      Check ("Raise_Ceil: a record below the new maxceil is admitted",
             Admitted (S, Far) and then Admitted (S, P1));
      for K of Probe_Keys loop
         Lemma_Same_Auth_Views (Before, S, Key (K));
         if In_W (Before, Key (K)) /= In_W (S, Key (K))
           or else W_Cap (Before, Key (K)) /= W_Cap (S, Key (K))
         then
            Check ("Raise_Ceil leaves W and wcap", False);
         end if;
      end loop;
      Lemmas (S);

      --  F4. The cell is a strict max-register.
      declare
         T : State := S;
         procedure Equal_Ceiling is
         begin
            Raise_Ceil (T, Roster (22, 1, 7000, 4), 1);
         end Equal_Ceiling;
         function R is new Refused (Equal_Ceiling);
      begin
         if Contracts_On then
            Check ("Raise_Ceil with a ceiling equal to maxceil is refused by its Pre", R);
         else
            Skip ("Raise_Ceil with a ceiling equal to maxceil is refused by its Pre");
         end if;
      end;

      --  F2. No other operation changes the cell. (App checks the cell
      --  after each Apply, and Unchanged after each refusal and duplicate.)
      Before := S;
      App (S, R1, St);
      Check ("a duplicate leaves the cell", St = OK and then Same_State (Before, S));
      App (S, Roster (Fnd, 0, 4000, 9), St);
      Check ("a dominated roster leaves the cell",
             St = Dominated and then Same_State (Before, S));
      App (S, Grant (Fnd, 2, 33), St);
      Check ("a new hold leaves the cell",
             St = OK and then Same_Cell (Before, S) and then Max_Ceil (S) = 7000);
      App (S, Far, St);
      Check ("a data record above every held roster is held under the cell's ceiling",
             St = OK and then Holds (S, Far) and then Same_Cell (Before, S));
      Before := S;
      Expire (S, 300);
      Check ("Expire leaves the cell",
             not Holds (S, D2) and then Same_Cell (Before, S) and then Max_Ceil (S) = 7000
             and then Holds (S, Far));
      Before := S;
      Set_Tag (S, 1, 777);
      Check ("Set_Tag leaves the cell",
             Tag (S, 1) = 777 and then Same_Cell (Before, S) and then Max_Ceil (S) = 7000);

      --  F3. Set_Ceil_Tag changes only the cell's tag.
      Before := S;
      Set_Ceil_Tag (S, 555);
      pragma Assert (Kome.Frontier.Same_Held (Before, S));
      Lemma_Same_Held (Before, S);
      pragma Assert (not Unchanged (Before, S));
      Check ("Set_Ceil_Tag changes only the cell's tag",
             Has_Ceil (S) and then Ceil_Tag (S) = 555 and then Ceil_Held (S) = RC
             and then Same_Rows (Before, S) and then Max_Ceil (S) = 7000
             and then Is_Frontier (S));

      --  The slot table: 15 more signers take every slot. A roster of a
      --  17th signer is refused for room, and the capture rule records
      --  its ceiling when it is above maxceil.
      for I in 0 .. 14 loop
         App (S, Grant (Byte (30 + I), Byte (100 + I), 400 + I), St);
      end loop;
      Check ("all 16 slots are used", St = OK and then Slots_Used (S) = Signers_Max);
      Before := S;
      Offer (S, Roster (45, 1, 6000, 5), St, Took);
      Check ("Auth_Full for a roster at or below maxceil changes nothing, the cell included",
             St = Auth_Full and then not Took and then Same_State (Before, S)
             and then Ceil_Held (S) = RC);
      Offer (S, Roster (45, 1, 7000, 6), St, Took);
      Check ("Auth_Full for a roster with the cell's ceiling does not move the cell",
             St = Auth_Full and then not Took and then Same_State (Before, S));
      Offer (S, R17, St, Took);
      Check ("a roster of a 17th signer above maxceil takes the cell and no slot",
             St = Auth_Full and then Took and then Ceil_Held (S) = R17
             and then Max_Ceil (S) = 8000 and then Ceil_Live (S)
             and then Same_Rows (Before, S) and then Slot_Of (S, Key (46)) = 0);

      --  A held roster with the cell's ceiling, then one above it: the
      --  cell stays and is no longer live.
      Before := S;
      App (S, Roster (Fnd, 2, 8000, 7), St);
      Check ("a held roster with the cell's ceiling: maxceil stays, the cell is not live",
             St = OK and then Max_Ceil (S) = 8000 and then Held_Ceil (S) = 8000
             and then not Ceil_Live (S) and then Same_Cell (Before, S));
      App (S, Roster (Fnd, 3, 9000, 8), St);
      Check ("a held roster above the cell raises maxceil and leaves the cell",
             St = OK and then Max_Ceil (S) = 9000 and then Held_Ceil (S) = 9000
             and then not Ceil_Live (S) and then Same_Cell (Before, S)
             and then Ceil_Value (S) = 8000);
      Offer (S, R17, St, Took);
      Check ("the cell's own roster offered again changes nothing",
             St = Auth_Full and then not Took and then Ceil_Held (S) = R17);
      Lemmas (S);
   end;

   --  (j) The audit scenario (AUDIT.md H12): a stolen root fills its slice
   --  with 512 REVOKEs at replica A and sends a roster R2 with a high
   --  ceiling first at replica B. A refuses R2 for room, B holds it. With
   --  the capture rule the two have the same maxceil, so they admit the
   --  same data records.
   declare
      C0   : constant U48 := 1000;
      C2   : constant U48 := 90_000;
      Root : constant Byte := 21;
      R0   : constant Header := Roster (Fnd, 5, C0, 1);
      G    : constant Header := Grant (Fnd, 1, 31);
      R2   : constant Header := Roster (Root, 1, C2, 2);
      R3   : constant Header := Roster (Root, 20, C2, 3);       --  R2's ceiling, a higher gen
      R4   : constant Header := Roster (Root, 1, C2 + 1, 4);    --  a higher ceiling, R2's gen
      RL   : constant Header := Roster (Root, 0, C2 - 1, 5);    --  R2 dominates it
      RF   : constant Header := Roster (Fnd, 6, C2 + 5, 6);     --  a founding refresh
      Far  : constant Header := Put (7, 'n', V (5000, 1, 1, 10));   --  C0 < t <= C2
      function X (I : Positive) return Header is (Revoke_K (Root, Key_N (I), 0, 3000 + I));
      A      : State := New_State (Cap => 8);
      B      : State := New_State (Cap => 8);
      Before : State := New_State (Cap => 8);
      Took   : Boolean;
      SA, SB : Status;
   begin
      --  Order A: the REVOKEs, then R2.
      App (A, R0, St);
      App (A, G, St);
      --  Apply, not App: App's lemma calls would make the fill cubic.
      for I in 1 .. Slice_Max loop
         Apply (A, X (I), U64 (I), St);
         pragma Assert (St = OK);
      end loop;
      Check ("order A: the stolen root's slice is full of REVOKEs",
             St = OK and then Slot_Count (A, Slot_Of (A, Key (Root))) = Slice_Max
             and then Max_Ceil (A) = C0 and then not Admitted (A, Far));
      Before := A;
      Offer (A, R2, SA, Took);
      Check ("order A: the full slice refuses R2, and the cell takes its ceiling",
             SA = Auth_Full and then Took and then not Holds (A, R2)
             and then Has_Ceil (A) and then Ceil_Held (A) = R2 and then Ceil_Live (A)
             and then Max_Ceil (A) = C2 and then Held_Ceil (A) = C0
             and then Same_Rows (Before, A));

      --  Order B: R2, then the REVOKEs.
      App (B, R0, St);
      App (B, G, St);
      Offer (B, R2, SB, Took);
      Check ("order B: R2 is held", SB = OK and then not Took and then Holds (B, R2));
      for I in 1 .. Slice_Max - 1 loop
         Apply (B, X (I), U64 (I), St);
         pragma Assert (St = OK);
      end loop;
      Before := B;
      Offer (B, X (Slice_Max), SB, Took);
      Check ("order B: the last REVOKE is refused, nothing changes, no cell",
             SB = Auth_Full and then not Took and then Same_State (Before, B)
             and then not Has_Ceil (B) and then Holds (B, R2)
             and then Held_Ceil (B) = C2);
      Check ("the two arrival orders give the same maxceil",
             Max_Ceil (A) = C2 and then Max_Ceil (B) = C2);
      Check ("the two arrival orders admit the same data record",
             Admitted (A, Far) and then Admitted (B, Far));
      App (A, Far, SA);
      App (B, Far, SB);
      Check ("a record above the old ceiling is held at both replicas",
             SA = OK and then SB = OK and then Holds (A, Far) and then Holds (B, Far));

      --  A dominated roster: B holds its dominator, A does not.
      Before := A;
      Offer (A, RL, SA, Took);
      Check ("a lower roster at the replica with the cell: refused, nothing changes",
             SA = Auth_Full and then not Took and then Same_State (Before, A));
      Before := B;
      Offer (B, RL, SB, Took);
      Check ("the same roster at the replica that holds R2: Dominated, nothing changes",
             SB = Dominated and then not Took and then Same_State (Before, B));
      Check ("a dominated roster: the same maxceil", Max_Ceil (A) = Max_Ceil (B));

      --  Equal ceilings: a roster with R2's ceiling never moves the cell.
      --  B holds it (it dominates R2 and frees its place).
      Before := A;
      Offer (A, R3, SA, Took);
      Check ("a roster with the cell's ceiling does not move the cell",
             SA = Auth_Full and then not Took and then Same_State (Before, A)
             and then Ceil_Held (A) = R2);
      Offer (B, R3, SB, Took);
      Check ("the same roster replaces R2 in the full slice of the other replica",
             SB = OK and then not Took and then Holds (B, R3) and then not Holds (B, R2)
             and then not Has_Ceil (B));
      Check ("equal ceilings: the same maxceil",
             Max_Ceil (A) = C2 and then Max_Ceil (B) = C2);

      --  A later roster with a higher ceiling: both slices are full and
      --  it frees nothing, so both cells take it.
      Offer (A, R4, SA, Took);
      Check ("a higher ceiling replaces the cell's roster",
             SA = Auth_Full and then Took and then Ceil_Held (A) = R4
             and then Max_Ceil (A) = C2 + 1 and then not Holds (A, R4));
      Before := B;
      Offer (B, R4, SB, Took);
      Check ("a higher ceiling at the replica without a cell: captured, the rows stay",
             SB = Auth_Full and then Took and then Ceil_Held (B) = R4 and then Ceil_Live (B)
             and then Held_Ceil (B) = C2 and then Same_Rows (Before, B)
             and then Holds (B, R3));
      Check ("a higher ceiling: the same maxceil",
             Max_Ceil (A) = C2 + 1 and then Max_Ceil (B) = C2 + 1);

      --  A held roster above the cell (a founding refresh): maxceil is
      --  the held ceiling again, at both.
      Before := A;
      App (A, RF, SA);
      App (B, RF, SB);
      Check ("a held roster above the cell: the same maxceil, the cells stay and are not live",
             SA = OK and then SB = OK
             and then Max_Ceil (A) = C2 + 5 and then Max_Ceil (B) = C2 + 5
             and then Held_Ceil (A) = C2 + 5 and then not Ceil_Live (A)
             and then not Ceil_Live (B) and then Same_Cell (Before, A)
             and then Ceil_Held (B) = R4);
      Lemmas (A);
      Lemmas (B);
   end;

   if Failed then
      Set_Exit_Status (Failure);
   end if;
   end Run_All;

begin
   null;
end Test_Frontier;
