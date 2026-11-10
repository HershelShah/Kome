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
--      authorization Apply only its slot.
pragma Ada_2022;
with Ada.Text_IO;      use Ada.Text_IO;
with Ada.Command_Line; use Ada.Command_Line;
with Ada.Exceptions;   use Ada.Exceptions;
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

   function New_State (Cap : Data_Size := 64) return State is (Empty (Key (Fnd), Cap));

   --  Each public view of two states agrees, tags included. This is how
   --  the test reads Unchanged, which is ghost. The Post of Apply also
   --  checks Unchanged.
   function Same_State (X, Y : State) return Boolean is
   begin
      if Kome.Frontier.Count (X) /= Kome.Frontier.Count (Y)
        or else Data_Count (X) /= Data_Count (Y)
        or else Slots_Used (X) /= Slots_Used (Y)
        or else Max_Ceil (X) /= Max_Ceil (Y)
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
   end Same_State;

   --  The keys on which the tests compare W and wcap.
   type Key_List is array (Positive range <>) of Byte;
   Probe_Keys : constant Key_List := [1, 2, 9, 21, 50, 54, 61];

   --  Held sets as unordered collections, and the same admission views.
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
      return Max_Ceil (X) = Max_Ceil (Y)
        and then (for all K of Probe_Keys =>
                    In_W (X, Key (K)) = In_W (Y, Key (K))
                    and then W_Cap (X, Key (K)) = W_Cap (Y, Key (K)));
   end Same_Held;

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

   --  Each lemma on each index of a state. Each lemma's Is_Frontier
   --  precondition costs O(Count^2) at run time, so on a large state (a
   --  full slice) only the whole-state lemmas run.
   procedure Lemmas (S : State) is
      Small : constant Boolean := Kome.Frontier.Count (S) <= 64;
   begin
      Lemma_Unchanged_Refl (S);
      Lemma_Unchanged (S, S);
      Lemma_Frontier_Shape (S);
      Lemma_Max_Ceil_Def (S);
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
      Check ("orders 1 and 2 converge", Same_Held (A, B));
      Check ("orders 1 and 3 converge (duplicates)", Same_Held (A, C));
      Check ("orders 1 and 4 converge (duplicates)", Same_Held (A, D));
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

   if Failed then
      Set_Exit_Status (Failure);
   end if;
   end Run_All;

begin
   null;
end Test_Frontier;
