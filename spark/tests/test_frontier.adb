--  Test main for Kome.Frontier: the lattice core exercised the way the Lean
--  theorems state it. (a) Contracts and ghost lemmas evaluated at run time
--  (-gnata) on hand-built records; (b) convergence: the same record set
--  applied in several orders, with duplicates, gives the same held set and
--  registers; (c) admission is monotone: a record refused under a low
--  ceiling is accepted once a roster raises it, and the result equals the
--  order where the roster came first; (d) GC: a DEL frees every field of its
--  entity and a later PUT re-creates it; (e) REVOKE is never dominated.
pragma Ada_2022;
with Ada.Text_IO;      use Ada.Text_IO;
with Ada.Command_Line; use Ada.Command_Line;
with Kome;             use Kome;
with Kome.Versions;     use Kome.Versions;
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

   NS : constant Id128 := (others => 7);

   function Key (B : Byte) return Key256 is (others => Word (B));
   function Hsh (B : Byte) return Key256 is (others => Word (B));
   function Ent (B : Byte) return Id128 is (others => Word (B));

   function Fld (C : Character) return Key256 is
     (others => Word (Character'Pos (C)));

   function V (T : U48; A : Byte; Seq : U48; H : Byte) return Version is
     (T => T, Author => Key (A), Seq => Seq, H => Hsh (H));

   function Put (E : Byte; F : Character; Ver : Version) return Header is
     (K => K_Put, NS => NS, Ent => Ent (E), FH => Fld (F), V => Ver,
      Ceiling => 0);

   function Del (E : Byte; Ver : Version) return Header is
     (K => K_Del, NS => NS, Ent => Ent (E), FH => Hsh (0), V => Ver,
      Ceiling => 0);

   --  Root key 9 signs every roster: V = (0, signer, gen, h).
   function Roster (Gen, Ceiling : U48; H : Byte) return Header is
     (K => K_Roster, NS => NS, Ent => Ent (0), FH => Hsh (0),
      V => (T => 0, Author => Key (9), Seq => Gen, H => Hsh (H)),
      Ceiling => Ceiling);

   --  V = (from_t, subject, rev_seq, h).
   function Revoke (A : Byte; From_T : U48) return Header is
     (K => K_Revoke, NS => NS, Ent => Ent (0), FH => Hsh (0),
      V => (T => From_T, Author => Key (A), Seq => 1, H => Hsh (200 + A)),
      Ceiling => 0);

   None : constant Member_Keys (1 .. 0) := [];
   AB   : constant Member_Keys (1 .. 2) := [Key (1), Key (2)];

   --  Held sets as unordered collections: equal iff same count and every
   --  record of one is held by the other.
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
      return Ceil (Regs (X)) = Ceil (Regs (Y)) and then Kome.Registers.Count (Regs (X)) = Kome.Registers.Count (Regs (Y));
   end Same_Held;

   type Header_List is array (Positive range <>) of Header;

   --  A complete reconciliation: a refused record is re-offered by whoever
   --  holds it (DESIGN.md §4), so apply the list in passes until a pass holds
   --  nothing new. Admission is monotone, so this terminates and the result
   --  is the frontier of the admitted set under the final registers (T4).
   function Run (L : Header_List; Roster_Members : Member_Keys) return State is
      S  : State := Empty (NS, 64);
      St : Status;
      Progress : Boolean := True;
   begin
      while Progress loop
         Progress := False;
         for I in L'Range loop
            declare
               Before : constant Natural := Kome.Frontier.Count (S);
            begin
               if L (I).K = K_Roster then
                  Apply (S, L (I), Roster_Members, St);
               else
                  Apply (S, L (I), None, St);
               end if;
               if St = OK and then Kome.Frontier.Count (S) /= Before then
                  Progress := True;
               end if;
            end;
         end loop;
      end loop;
      return S;
   end Run;

   R1  : constant Header := Roster (1, 5000, 1);
   P1  : constant Header := Put (1, 'n', V (100, 1, 1, 10));
   P2  : constant Header := Put (1, 'n', V (200, 2, 1, 11));   --  beats P1
   P3  : constant Header := Put (1, 'a', V (150, 1, 2, 12));   --  other field
   D1  : constant Header := Del (1, V (300, 2, 2, 13));        --  beats P1..P3
   P4  : constant Header := Put (1, 'n', V (400, 1, 3, 14));   --  re-creates
   X1  : constant Header := Revoke (2, 250);
   Far : constant Header := Put (2, 'n', V (9000, 1, 4, 15));  --  above ceil
   R2  : constant Header := Roster (2, 10_000, 2);             --  raises it
   S   : State := Empty (NS, 64);
   St  : Status;

begin
   --  Lemmas at run time on a few shapes.
   Lemma_Lt_Irrefl (P1.V);
   Lemma_Lt_Trans (P1.V, P2.V, D1.V);
   Lemma_Trichotomy (P1.V, P2.V);
   Lemma_Dominates_Irrefl (P1);
   Lemma_Dominates_Trans (P1, P2, D1);
   Lemma_Revoke_Never_Dominated (D1, X1);
   Check ("lemmas evaluated", True);

   --  Admission refuses an unrostered author and an unraised ceiling.
   S := Empty (NS, 64);
   Apply (S, P1, None, St);
   Check ("refused before any roster", St = Inadmissible and Kome.Frontier.Count (S) = 0);
   Apply (S, R1, AB, St);
   Check ("roster held, registers raised",
          St = OK and Ceil (Regs (S)) = 5000 and Kome.Registers.Count (Regs (S)) = 2);
   Apply (S, P1, None, St);
   Check ("admitted after roster", St = OK and Holds (S, P1));
   Apply (S, P1, None, St);
   Check ("duplicate is a no-op and OK",
          St = OK and Kome.Frontier.Count (S) = 2);

   --  Domination and GC.
   Apply (S, P2, None, St);
   Check ("newer PUT replaces older", St = OK and not Holds (S, P1) and Holds (S, P2));
   Apply (S, P1, None, St);
   Check ("older PUT re-offered is dominated", St = Dominated and not Holds (S, P1));
   Apply (S, P3, None, St);
   Apply (S, D1, None, St);
   Check ("DEL frees every field", St = OK and not Holds (S, P2)
          and not Holds (S, P3) and Holds (S, D1));
   Apply (S, P4, None, St);
   Check ("later PUT re-creates beside the DEL", St = OK and Holds (S, P4) and Holds (S, D1));
   Apply (S, X1, None, St);
   Apply (S, X1, None, St);
   Check ("REVOKE held and never dominated", Holds (S, X1));
   Apply (S, Far, None, St);
   Check ("far-future PUT refused under ceiling 5000", St = Inadmissible and not Holds (S, Far));
   Apply (S, R2, AB, St);
   Check ("second roster dominates the first", Holds (S, R2) and not Holds (S, R1));
   Apply (S, Far, None, St);
   Check ("same PUT admitted once the ceiling rose", St = OK and Holds (S, Far));

   --  Convergence (T4): several orders and duplications of one set.
   declare
      All_Recs : constant Header_List := [R1, P1, P2, P3, D1, P4, X1, Far, R2];
      O1 : constant Header_List := [R1, P1, P2, P3, D1, P4, X1, Far, R2];
      O2 : constant Header_List := [R2, Far, X1, P4, D1, P3, P2, P1, R1];
      O3 : constant Header_List := [P4, D1, R1, R1, P2, Far, R2, P1, X1, P3, Far, D1];
      O4 : constant Header_List := [Far, Far, R1, P3, X1, R2, P1, P2, D1, P4, P4];
      A  : constant State := Run (O1, AB);
      B  : constant State := Run (O2, AB);
      C  : constant State := Run (O3, AB);
      D  : constant State := Run (O4, AB);
   begin
      Check ("orders 1 and 2 converge", Same_Held (A, B));
      Check ("orders 1 and 3 converge (duplicates)", Same_Held (A, C));
      Check ("orders 1 and 4 converge (duplicates)", Same_Held (A, D));
      Check ("final frontier is {R2, D1, P4, X1, Far}",
             Kome.Frontier.Count (A) = 5 and Holds (A, R2) and Holds (A, D1) and Holds (A, P4)
             and Holds (A, X1) and Holds (A, Far));
      Check ("registers converge", Ceil (Regs (A)) = 10_000 and Kome.Registers.Count (Regs (A)) = 2);
      Check ("all records accounted for", All_Recs'Length = 9);
   end;

   --  Frontier invariant holds after every step of a long mixed run.
   declare
      Mixed : constant Header_List :=
        [P1, R1, Far, P3, R2, D1, X1, P2, P4, Far, R1, P1];
      T  : State := Empty (NS, 64);
      Ok : Boolean := True;
   begin
      for I in Mixed'Range loop
         if Mixed (I).K = K_Roster then
            Apply (T, Mixed (I), AB, St);
         else
            Apply (T, Mixed (I), None, St);
         end if;
         Ok := Ok and Is_Frontier (T);
      end loop;
      Check ("Is_Frontier after every apply", Ok);
   end;

   if Failed then
      Set_Exit_Status (Failure);
   end if;
end Test_Frontier;
