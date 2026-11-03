--  Test main for Kome.Frontier: the lattice core exercised the way the Lean
--  theorems and DESIGN.md §3, §4, §7 state it. Contracts and ghost lemmas
--  are evaluated at run time (-gnata) on every call. Covered:
--  (a) admission by GRANT (D1′) and refusal without one;
--  (b) GRANT domination keyed by (issuer, subject) (R1);
--  (c) roster domination as the product order (R4);
--  (d) every refusal leaves the state unchanged (D11, T13);
--  (e) capacity rows: a data flood or a full slice takes no one else's
--      room, and the founding key's REVOKE lands (E1, E2, R5);
--  (f) expiry (D10): Expire and Apply_Expired;
--  (g) convergence: the same set in several orders, with duplicates and
--      re-offers, gives the same held set and registers (T4).
pragma Ada_2022;
with Ada.Text_IO;      use Ada.Text_IO;
with Ada.Command_Line; use Ada.Command_Line;
with Ada.Exceptions;   use Ada.Exceptions;
with Kome;             use Kome;
with Kome.Versions;    use Kome.Versions;
with Kome.Headers;     use Kome.Headers;
with Kome.Registers;   use Kome.Registers;
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

   NS  : constant Id128 := (others => 7);
   Fnd : constant Byte := 9;                --  the founding key

   function Key (B : Byte) return Key256 is (others => Word (B));
   function Hsh (B : Natural) return Key256 is (W0 => Word (B), others => 5);
   function Ent (B : Byte) return Id128 is (others => Word (B));
   function Fld (C : Character) return Key256 is
     (others => Word (Character'Pos (C)));

   function V (T : U48; A : Byte; Seq : U48; H : Natural) return Version is
     (T => T, Author => Key (A), Seq => Seq, H => Hsh (H));

   function Put (E : Byte; F : Character; Ver : Version) return Header is
     (K => K_Put, NS => NS, Ent => Ent (E), FH => Fld (F), V => Ver,
      Issuer => Zero_Key, Del_TTL => 0);

   function Del (E : Byte; Ver : Version) return Header is
     (K => K_Del, NS => NS, Ent => Ent (E), FH => Zero_Key, V => Ver,
      Issuer => Zero_Key, Del_TTL => 0);

   --  V = (ceiling_t, signer, gen, h), Issuer = signer.
   function Roster (Signer : Byte; Gen, Ceiling : U48; H : Natural) return Header is
     (K => K_Roster, NS => NS, Ent => Zero_Id, FH => Zero_Key,
      V => (T => Ceiling, Author => Key (Signer), Seq => Gen, H => Hsh (H)),
      Issuer => Key (Signer), Del_TTL => Del_TTL_Default);

   --  V = (0, subject, 0, h), Issuer = signer.
   function Grant (Issuer, Subject : Byte; H : Natural) return Header is
     (K => K_Grant, NS => NS, Ent => Zero_Id, FH => Zero_Key,
      V => (T => 0, Author => Key (Subject), Seq => 0, H => Hsh (H)),
      Issuer => Key (Issuer), Del_TTL => 0);

   --  V = (from_t, subject, rev_seq, h), Issuer = signer.
   function Revoke (Issuer, Subject : Byte; From_T : U48; H : Natural) return Header is
     (K => K_Revoke, NS => NS, Ent => Zero_Id, FH => Zero_Key,
      V => (T => From_T, Author => Key (Subject), Seq => 1, H => Hsh (H)),
      Issuer => Key (Issuer), Del_TTL => 0);

   function New_State (Cap : Data_Size := 64; Slice : Slice_Count := 8) return State is
     (Empty (NS, Key (Fnd), Cap, Slice));

   --  Every public view of two states agrees (the test's reading of
   --  Unchanged, which is ghost; Apply's Post also checks Unchanged itself).
   function Same_State (X, Y : State) return Boolean is
   begin
      if Kome.Frontier.Count (X) /= Kome.Frontier.Count (Y)
        or else Data_Count (X) /= Data_Count (Y)
        or else Slots_Used (X) /= Slots_Used (Y)
        or else Ceil (Regs (X)) /= Ceil (Regs (Y))
        or else Kome.Registers.Count (Regs (X)) /= Kome.Registers.Count (Regs (Y))
      then
         return False;
      end if;
      for I in 1 .. Kome.Frontier.Count (X) loop
         if Held (X, I) /= Held (Y, I) then
            return False;
         end if;
      end loop;
      for K in 1 .. Slots_Used (X) loop
         if Slot_Key (X, K) /= Slot_Key (Y, K) or else Slot_Count (X, K) /= Slot_Count (Y, K) then
            return False;
         end if;
      end loop;
      return True;
   end Same_State;

   --  Held sets as unordered collections.
   function Same_Held (X, Y : State) return Boolean is
   begin
      if Kome.Frontier.Count (X) /= Kome.Frontier.Count (Y) then
         return False;
      end if;
      for I in 1 .. Kome.Frontier.Count (X) loop
         if not Holds (Y, Held (X, I)) then
            return False;
         end if;
      end loop;
      return Ceil (Regs (X)) = Ceil (Regs (Y))
        and then Kome.Registers.Count (Regs (X)) = Kome.Registers.Count (Regs (Y));
   end Same_Held;

   --  Apply, and check that a refusal or a duplicate changed nothing.
   procedure App (S : in out State; R : Header; St : out Status) is
      Before : constant State := S;
      Was    : constant Boolean := Holds (S, R);
   begin
      Apply (S, R, St);
      pragma Assert (Is_Frontier (S));
      if St /= OK or else Was then
         pragma Assert (Unchanged (Before, S));
         Lemma_Unchanged (Before, S);   --  executable: runs under -gnata
         if not Same_State (Before, S) then
            Check ("refusal or duplicate left the state unchanged", False);
         end if;
      end if;
   end App;

   --  Every lemma on every index of a state.
   procedure Lemmas (S : State) is
   begin
      Lemma_Unchanged_Refl (S);
      Lemma_Unchanged (S, S);
      Lemma_Frontier_Shape (S);
      for I in 1 .. Kome.Frontier.Count (S) loop
         Lemma_Held_Cases (S, I);
         Lemma_Frontier_Held (S, I);
         Lemma_Ceil_Bound (S, I);
         if Held (S, I).K = K_Grant then
            Lemma_W_Complete (S, I);
         end if;
      end loop;
      for I in 1 .. Data_Count (S) loop
         Lemma_Held_Data (S, I);
         Lemma_Frontier_Data (S, I);
      end loop;
      for K in 1 .. Slots_Used (S) loop
         for J in 1 .. Slot_Count (S, K) loop
            Lemma_Held_Auth (S, K, J);
            Lemma_Frontier_Auth (S, K, J);
         end loop;
      end loop;
      if Ceil (Regs (S)) > 0 then
         Lemma_Ceil_Witness (S);
      end if;
      for I in 1 .. Kome.Registers.Count (Regs (S)) loop
         Lemma_W_Sound (S, Writer (Regs (S), I));
      end loop;
   end Lemmas;

   type Header_List is array (Positive range <>) of Header;

   --  A complete reconciliation: a refused record is re-offered by whoever
   --  holds it (DESIGN.md §4), so apply the list in passes until a pass
   --  holds nothing new. Admission is monotone, so this terminates (T4).
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

   --  A State carries a Register_File of Writers_Max keys (256 KiB), and
   --  under -gnata every Post evaluation copies states and registers, so
   --  the checks run in a task with a large stack.
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
      Lemma_Dominator_Keeps_Registers (R2, R1);
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
      Check ("roster held, ceiling raised", St = OK and then Ceil (Regs (S)) = 5000
             and then Kome.Registers.Count (Regs (S)) = 0);
      App (S, P1, St);
      Check ("PUT by a key without a GRANT is Inadmissible",
             St = Inadmissible and then not Holds (S, P1));
      App (S, Grant (Fnd, 1, 31), St);
      Check ("GRANT held, subject is a writer",
             St = OK and then In_W (Regs (S), Key (1)) and then Kome.Registers.Count (Regs (S)) = 1);
      App (S, P1, St);
      Check ("a GRANT admits its subject", St = OK and then Holds (S, P1));
      App (S, P1, St);
      Check ("duplicate is a no-op and OK", St = OK and then Kome.Frontier.Count (S) = 3);
      App (S, Put (2, 'n', V (9000, 1, 2, 11)), St);
      Check ("PUT above the ceiling is Inadmissible", St = Inadmissible);
      Lemmas (S);
      --  Lemmas ran Lemma_Unchanged_Refl and Lemma_Unchanged (S, S), and App
      --  ran Lemma_Unchanged after each refusal and duplicate: both lemmas
      --  are executable (bounded quantifiers) and returned.
      Lemma_Unchanged_Refl (S);
      Lemma_Unchanged (S, S);
      Check ("Lemma_Unchanged_Refl and Lemma_Unchanged execute (3 held)",
             Kome.Frontier.Count (S) = 3);
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
             and then Kome.Registers.Count (Regs (S)) = 1);
      App (S, GF2, St);
      Check ("the same issuer's higher-h GRANT dominates",
             St = OK and then Holds (S, GF2) and then not Holds (S, GF)
             and then Holds (S, GA) and then In_W (Regs (S), Key (1)));
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
             and then Ceil (Regs (S)) = 9000);
      App (S, R3, St);
      Check ("a roster with higher gen and lower ceiling does not dominate",
             St = OK and then Holds (S, R3) and then Holds (S, R2) and then Holds (S, RS));
      Lemmas (S);
      App (S, R4, St);
      Check ("a roster with higher gen and ceiling >= dominates the antichain",
             St = OK and then Holds (S, R4) and then not Holds (S, R2)
             and then not Holds (S, RS) and then not Holds (S, R3)
             and then Ceil (Regs (S)) = 9000);
      App (S, R2, St);
      Check ("a roster dominated on arrival is Dominated and changes nothing",
             St = Dominated and then not Holds (S, R2) and then Ceil (Regs (S)) = 9000);
      App (S, Roster (Fnd, 2, 20_000, 6), St);
      Check ("a stale-gen roster with a higher ceiling is held and raises the ceiling",
             St = OK and then Ceil (Regs (S)) = 20_000);
      Lemmas (S);
   end;

   --  (d)+(e) Data flood, then the founding key's REVOKE.
   declare
      S : State := New_State (Cap => 8, Slice => 4);
      Before : State := New_State (Cap => 8, Slice => 4);
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

   --  (e) Slices: one signer's slice full; others still land.
   declare
      S      : State := New_State (Cap => 8, Slice => 4);
      Before : State := New_State (Cap => 8, Slice => 4);
   begin
      for I in 0 .. 3 loop
         App (S, Grant (21, Byte (50 + I), 200 + I), St);
      end loop;
      Check ("a root's slice fills", St = OK and then Slot_Count (S, Slot_Of (S, Key (21))) = 4);
      Before := S;
      App (S, Grant (21, 54, 204), St);
      Check ("Auth_Full when the signer's slice is full, nothing changed",
             St = Auth_Full and then Same_State (Before, S)
             and then not In_W (Regs (S), Key (54)));
      App (S, Grant (21, 50, 250), St);
      Check ("a full slice still takes a record that frees one",
             St = OK and then not Holds (S, Grant (21, 50, 200)));
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
      S      : State := New_State (Cap => 4, Slice => 2);
      Before : State := New_State (Cap => 4, Slice => 2);
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
      Expire (S, No_Horizon);
      Check ("Expire with no horizon removes nothing", Kome.Frontier.Count (S) = 7);
      Expire (S, 200);
      Check ("Expire removes exactly the expired DELs",
             not Holds (S, D1) and then not Holds (S, D2) and then Holds (S, D3)
             and then Holds (S, P1) and then Holds (S, P2) and then Holds (S, G)
             and then Kome.Frontier.Count (S) = 5 and then Ceil (Regs (S)) = 5000);
      Lemmas (S);
   end;

   --  (f) Apply_Expired drops what the DEL dominates and does not hold it.
   declare
      S      : State := New_State;
      Before : State := New_State;
      P1 : constant Header := Put (1, 'a', V (100, 1, 1, 1));
      P2 : constant Header := Put (1, 'b', V (150, 1, 2, 2));
      P3 : constant Header := Put (2, 'a', V (120, 1, 3, 3));
      D  : constant Header := Del (1, V (200, 1, 4, 4));
      D0 : constant Header := Del (2, V (100, 1, 5, 5));
   begin
      App (S, Roster (Fnd, 1, 5000, 7), St);
      App (S, Grant (Fnd, 1, 6), St);
      App (S, P1, St);
      App (S, P2, St);
      App (S, P3, St);
      Apply_Expired (S, D, St);
      Check ("Apply_Expired drops the PUTs the DEL dominates and does not hold it",
             St = OK and then not Holds (S, P1) and then not Holds (S, P2)
             and then Holds (S, P3) and then not Holds (S, D)
             and then Kome.Frontier.Count (S) = 3);
      App (S, Del (2, V (130, 1, 7, 9)), St);
      Check ("a held DEL drops its entity's PUT", St = OK and then not Holds (S, P3));
      Before := S;
      Apply_Expired (S, D0, St);
      Check ("Apply_Expired of a dominated DEL is Dominated, unchanged",
             St = Dominated and then Same_State (Before, S));
      Apply_Expired (S, Del (3, V (9000, 1, 6, 8)), St);
      Check ("Apply_Expired of an inadmissible DEL is Inadmissible",
             St = Inadmissible and then Same_State (Before, S));
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
      Check ("orders 1 and 2 converge", Same_Held (A, B));
      Check ("orders 1 and 3 converge (duplicates)", Same_Held (A, C));
      Check ("orders 1 and 4 converge (duplicates)", Same_Held (A, D));
      Check ("final frontier is {R2, G1, G2, D1, P4, X1, Far}",
             Kome.Frontier.Count (A) = 7 and then Holds (A, R2) and then Holds (A, G1)
             and then Holds (A, G2) and then Holds (A, D1) and then Holds (A, P4)
             and then Holds (A, X1) and then Holds (A, Far));
      Check ("registers converge",
             Ceil (Regs (A)) = 10_000 and then Kome.Registers.Count (Regs (A)) = 2);
      Lemmas (A);
   end;

   --  Is_Frontier after every step of a long mixed run.
   declare
      Mixed : constant Header_List :=
        [Put (1, 'n', V (100, 1, 1, 10)), Roster (Fnd, 1, 5000, 1),
         Grant (Fnd, 1, 31), Put (1, 'n', V (100, 1, 1, 10)),
         Roster (Fnd, 1, 9000, 3), Roster (Fnd, 2, 6000, 2),
         Del (1, V (300, 1, 2, 13)), Revoke (Fnd, 1, 250, 15),
         Grant (21, 1, 32), Grant (Fnd, 1, 40), Put (1, 'a', V (400, 1, 3, 14)),
         Roster (21, 7, 4000, 20), Roster (Fnd, 3, 9000, 4)];
      T  : State := New_State (Cap => 16, Slice => 4);
      Ok : Boolean := True;
   begin
      for I in Mixed'Range loop
         App (T, Mixed (I), St);
         Ok := Ok and then Is_Frontier (T);
      end loop;
      Check ("Is_Frontier after every apply", Ok);
      Lemmas (T);
   end;

   if Failed then
      Set_Exit_Status (Failure);
   end if;
   end Run_All;

begin
   null;
end Test_Frontier;
