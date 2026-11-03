--  Test main for Kome.Emit: the write path of DESIGN.md §5 on states built
--  with Kome.Frontier.Apply.
--  (a) Chase above a far-future floor.
--  (b) At the ceiling: Shadowed if the floor wins the tie, OK if the write
--      wins it. No shadow after a roster raises the ceiling (T9).
--  (c) Seq exhaustion refuses and changes nothing (T13).
--  (d) With no clock (Now = 0), the write also chases.
--  (e) The floor of a DEL includes each field and the prior DELs. The
--      floor of a PUT includes the DEL of the entity.
--  (f) floor.t = 2^48 - 1 does not wrap.
--  (g) An OK write, applied back to the state, is held (read-your-writes,
--      T8).
--  (h) H8 restore/clone detection: seq jumps past a held own record and
--      Clone_Suspected is True. Thus v_emit is never equal to a held
--      version.
--  (i) A non-member key is Inadmissible.
--  (j) In_Floor excludes neighbours.
--  (k) The state-level T9 lemmas.
--  (l) D8: the outcome is the same under three different content hashes.
--      The test builds and applies each record, and each gets the
--      predicted outcome. The two H lemmas are true on each emitted write.
--  (m) Seq_Exhausted after an H8 jump to 2^48 - 1.
--  In the states, a GRANT gives write access, and the V of a roster is
--  (ceiling_t, signer, gen, h).
--  Contracts and lemmas run (-gnata).
pragma Ada_2022;
with Ada.Text_IO;      use Ada.Text_IO;
with Ada.Command_Line; use Ada.Command_Line;
with Ada.Exceptions;   use Ada.Exceptions;
with Kome;             use Kome;
with Kome.Versions;    use Kome.Versions;
with Kome.Headers;     use Kome.Headers;
with Kome.Registers;   use Kome.Registers;
with Kome.Frontier;    use Kome.Frontier;
with Kome.Emit;        use Kome.Emit;

procedure Test_Emit with SPARK_Mode => Off is

   Failed : Boolean := False;

   procedure Check (Name : String; Cond : Boolean) is
   begin
      Put_Line ((if Cond then "PASS " else "FAIL ") & Name);
      if not Cond then
         Failed := True;
      end if;
   end Check;

   NS  : constant Id128 := (others => 7);
   Fnd : constant Byte  := 9;   --  the founding key

   function Key (B : Byte) return Key256 is (others => Word (B));
   function Hsh (B : Byte) return Key256 is (others => Word (B));
   function Ent (B : Byte) return Id128 is (others => Word (B));
   function Fld (C : Character) return Key256 is
     (others => Word (Character'Pos (C)));

   function Ver (T : U48; A : Byte; Seq : U48; H : Byte) return Version is
     (T => T, Author => Key (A), Seq => Seq, H => Hsh (H));

   function Put (E : Byte; F : Character; V : Version) return Header is
     (K => K_Put, NS => NS, Ent => Ent (E), FH => Fld (F), V => V,
      Issuer => Zero_Key, Del_TTL => 0);

   function Del (E : Byte; V : Version) return Header is
     (K => K_Del, NS => NS, Ent => Ent (E), FH => Zero_Key, V => V,
      Issuer => Zero_Key, Del_TTL => 0);

   --  A founding-key roster: V = (ceiling_t, signer, gen, h).
   function Roster (Gen, Ceiling : U48; H : Byte) return Header is
     (K => K_Roster, NS => NS, Ent => Zero_Id, FH => Zero_Key,
      V => (T => Ceiling, Author => Key (Fnd), Seq => Gen, H => Hsh (H)),
      Issuer => Key (Fnd), Del_TTL => Del_TTL_Default);

   --  A founding-key GRANT to Subject: V = (0, subject, 0, h).
   function Grant (Subject : Byte) return Header is
     (K => K_Grant, NS => NS, Ent => Zero_Id, FH => Zero_Key,
      V => (T => 0, Author => Key (Subject), Seq => 0, H => Hsh (Subject)),
      Issuer => Key (Fnd), Del_TTL => 0);

   function Put_T (E : Byte; F : Character) return Target is
     (Op => W_Put, NS => NS, Ent => Ent (E), FH => Fld (F));
   function Del_T (E : Byte) return Target is
     (Op => W_Del, NS => NS, Ent => Ent (E), FH => (others => 0));

   function New_State (Cap : Data_Size) return State is
     (Empty (NS, Key (Fnd), Cap, 8));

   No_V : constant Version := (others => <>);

   type Byte_List is array (Positive range <>) of Byte;
   type Key_List is array (Positive range <>) of Key256;
   Writers : constant Byte_List := [1, 2, 3, 5, 6];

   Self : constant Key256 := Key (3);
   HC   : constant Key256 := Hsh (77);   --  the content hash of the caller
   --  Two extreme content hashes for the D8 checks.
   H_Lo : constant Key256 := (others => 0);
   H_Hi : constant Key256 := (others => Word'Last);

   S   : State := New_State (64);
   St  : Status;
   R   : Status;
   Seq : U48;
   V   : Version;
   Cl  : Boolean;   --  Clone_Suspected of the last call
   Out_Ok : Boolean := True;   --  each Choose output agreed with Seq_Self

   --  Writers: 1, 2, 3 (this device), 5 (a key above 3), 6 (above 5).
   procedure Grant_Writers (X : in out State) is
   begin
      for B of Writers loop
         Apply (X, Grant (B), St);
         if St /= OK then
            Out_Ok := False;
         end if;
      end loop;
   end Grant_Writers;

   --  Step 1 (Choose), then the version that the record gets after step 2
   --  hashes it with content hash H. A refusal gives (0, 0, 0, 0). The D8
   --  lemmas run on each chosen write, for H and for two other hashes.
   procedure Do_Emit
     (X    : State; Tgt : Target; Now : U48; Self : Key256; H : Key256;
      Seq  : in out U48; V : out Version; R : out Status)
   is
      T, Sq : U48;
   begin
      Choose (X, Tgt, Now, Self, Seq, T, Sq, R, Cl);
      if R in OK | Shadowed then
         V := Stamp (T, Self, Sq, H);
         if Sq /= Seq then
            Out_Ok := False;
         end if;
         for HX of Key_List'[H, H_Lo, H_Hi] loop
            Lemma_Outcome_Independent_Of_H (X, Tgt, T, Self, Sq, HX);
            if R = OK then
               Lemma_OK_Undominated (X, Tgt, T, Self, Sq, HX);
            end if;
         end loop;
      else
         V := (T => T, Author => (others => 0), Seq => Sq, H => (others => 0));
      end if;
   end Do_Emit;

   procedure Apply_Data (X : Header) is
   begin
      Apply (S, X, St);
   end Apply_Data;

   --  D8: do these steps:
   --    1. Choose once.
   --    2. Build the record under three content hashes (H_Lo, H_Hi, HC).
   --    3. Apply each record to a copy of X.
   --    4. Check that each record gets the outcome that Choose predicted:
   --       OK -> held; Shadowed (on a PUT) -> Dominated.
   function Same_Under_Two_Hashes (X : State; Tgt : Target; Now : U48;
                                   Self : Key256; Seq_Self : U48;
                                   Expect : Status) return Boolean
   is
      Sq_S  : U48 := Seq_Self;
      T, Sq : U48;
      Res   : Status;
      C     : Boolean;
      Good  : Boolean := True;
   begin
      Choose (X, Tgt, Now, Self, Sq_S, T, Sq, Res, C);
      if Res /= Expect then
         return False;
      end if;
      for HX of Key_List'[H_Lo, H_Hi, HC] loop
         declare
            Y   : State := X;
            Rec : constant Header := To_Header (Tgt, Stamp (T, Self, Sq, HX));
            A   : Status;
         begin
            Apply (Y, Rec, A);
            case Res is
               when OK =>
                  Good := Good and then A = OK and then Holds (Y, Rec);
               when Shadowed =>
                  Good := Good and then A = Dominated and then not Holds (Y, Rec);
               when others =>
                  Good := False;
            end case;
         end;
      end loop;
      return Good;
   end Same_Under_Two_Hashes;

   --  A State has a Register_File of Writers_Max keys. Under -gnata, each
   --  Post evaluation copies states. Thus the checks run in a task with a
   --  large stack (as in test_frontier).
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
   begin
   Grant_Writers (S);
   Apply (S, Roster (1, 10_000, 1), St);
   Check ("setup: writers granted, roster ceiling 10000",
          Out_Ok and St = OK and Ceil (Regs (S)) = 10_000);

   --  (d) No floor, no clock: t = 0.
   Seq := 0;
   Do_Emit (S, Put_T (1, 'n'), 0, Self, HC, Seq, V, R);
   Check ("no floor, Now = 0: t = 0, OK, seq 1",
          R = OK and V.T = 0 and V.Seq = 1 and Seq = 1 and not Cl
          and V.Author = Self and V.H = HC);

   --  No floor, clock above the ceiling: clamped.
   Do_Emit (S, Put_T (1, 'n'), 50_000, Self, HC, Seq, V, R);
   Check ("no floor, Now above ceiling: t = ceiling, OK",
          R = OK and V.T = 10_000 and Seq = 2);

   --  (a) Chase above a far-future floor.
   Apply_Data (Put (1, 'n', Ver (9_000, 2, 1, 10)));
   Check ("setup: far-future PUT held", St = OK);
   Do_Emit (S, Put_T (1, 'n'), 100, Self, HC, Seq, V, R);
   Check ("chase above a far-future floor: t = floor.t + 1",
          R = OK and V.T = 9_001 and Lt (Ver (9_000, 2, 1, 10), V));
   Do_Emit (S, Put_T (1, 'n'), 9_500, Self, HC, Seq, V, R);
   Check ("clock above the floor wins: t = Now", R = OK and V.T = 9_500);
   Do_Emit (S, Put_T (1, 'x'), 100, Self, HC, Seq, V, R);
   Check ("other field has no floor: t = Now", R = OK and V.T = 100);

   --  (d) With no clock, the write also chases.
   Do_Emit (S, Put_T (1, 'n'), 0, Self, HC, Seq, V, R);
   Check ("Now = 0 chases the floor", R = OK and V.T = 9_001);

   --  (g) Read-your-writes: the emitted PUT, when applied, replaces the
   --  floor.
   declare
      P : constant Header := To_Header (Put_T (1, 'n'), V);
   begin
      Apply_Data (P);
      Check ("emitted PUT applied is held, floor gone",
             St = OK and Holds (S, P)
             and not Holds (S, Put (1, 'n', Ver (9_000, 2, 1, 10))));
   end;

   --  (e) The PUT floor includes the DEL of the entity.
   Apply_Data (Del (4, Ver (700, 2, 2, 20)));
   Do_Emit (S, Put_T (4, 'q'), 10, Self, HC, Seq, V, R);
   Check ("PUT chases the entity's DEL", R = OK and V.T = 701);

   --  The DEL floor includes each field and the prior DELs.
   Apply_Data (Put (6, 'a', Ver (300, 2, 3, 21)));
   Apply_Data (Put (6, 'b', Ver (800, 1, 4, 22)));
   Apply_Data (Put (6, 'c', Ver (500, 2, 5, 23)));
   Do_Emit (S, Del_T (6), 0, Self, HC, Seq, V, R);
   Check ("DEL chases the newest field of the entity", R = OK and V.T = 801);
   declare
      D : constant Header := To_Header (Del_T (6), V);
   begin
      Apply_Data (D);
      Check ("emitted DEL applied frees every field",
             St = OK and Holds (S, D)
             and not Holds (S, Put (6, 'b', Ver (800, 1, 4, 22))));
   end;
   Do_Emit (S, Del_T (6), 0, Self, HC, Seq, V, R);
   Check ("DEL chases the prior DEL", R = OK and V.T = 802);

   --  (b) At the ceiling. Floor at t = 10000 by key 5 (above Self = 3).
   Apply_Data (Put (8, 'n', Ver (10_000, 5, 6, 30)));
   Check ("setup: PUT at the ceiling held", St = OK);
   declare
      Before : constant U48 := Seq;
   begin
      Do_Emit (S, Put_T (8, 'n'), 20_000, Self, HC, Seq, V, R);
      Check ("at the ceiling, floor wins the tie: Shadowed",
             R = Shadowed and V.T = 10_000 and Lt (V, Ver (10_000, 5, 6, 30))
             and Seq = Before + 1);
   end;
   --  Floor at t = 10000 by key 2 (below Self = 3): the write wins the tie.
   Apply_Data (Put (9, 'n', Ver (10_000, 2, 7, 31)));
   Do_Emit (S, Put_T (9, 'n'), 0, Self, HC, Seq, V, R);
   Check ("at the ceiling, write wins the tie: OK",
          R = OK and V.T = 10_000 and Lt (Ver (10_000, 2, 7, 31), V));

   --  T9: a roster with a higher ceiling unpins the shadowed cell.
   Lemma_Floor_Admitted (S, Put_T (8, 'n'));
   declare
      S1 : constant State := S;
   begin
      Apply (S, Roster (2, 20_000, 2), St);
      Check ("setup: ceiling raised to 20000",
             St = OK and Ceil (Regs (S)) = 20_000);
      --  T9 state form: each floor of the new state is below its ceiling.
      Lemma_Roster_Unpins (S1, S, Put_T (8, 'n'));
      Lemma_Roster_Unpins (S1, S, Del_T (6));
   end;
   Do_Emit (S, Put_T (8, 'n'), 0, Self, HC, Seq, V, R);
   Check ("after the raise the same cell is unshadowed",
          R = OK and V.T = 10_001 and Lt (Ver (10_000, 5, 6, 30), V));

   --  (c) Seq exhaustion: nothing is emitted, Seq_Self does not change.
   Seq := U48'Last;
   V := Ver (1, 1, 1, 1);
   Do_Emit (S, Put_T (1, 'n'), 100, Self, HC, Seq, V, R);
   Check ("seq exhausted: refused, nothing emitted, seq unchanged",
          R = Seq_Exhausted and Seq = U48'Last and V = No_V);
   Seq := U48'Last - 1;
   Do_Emit (S, Put_T (1, 'n'), 100, Self, HC, Seq, V, R);
   Check ("last seq value is ordinary", R = OK and Seq = U48'Last
          and V.Seq = U48'Last);

   --  (f) Floor at t = 2^48 - 1 under a ceiling of 2^48 - 1: no wrap.
   declare
      T : State := New_State (8);
   begin
      Grant_Writers (T);
      Apply (T, Roster (1, U48'Last, 1), St);
      Apply (T, Put (1, 'n', Ver (U48'Last, 5, 1, 40)), St);
      Check ("setup: PUT at t = 2^48 - 1 held", St = OK);
      Seq := 10;
      Do_Emit (T, Put_T (1, 'n'), 0, Self, HC, Seq, V, R);
      Check ("floor.t = 2^48 - 1: t = ceiling, Shadowed, no wrap",
             R = Shadowed and V.T = U48'Last and Seq = 11);
      Do_Emit (T, Put_T (1, 'n'), 0, Key (6), HC, Seq, V, R);
      Check ("floor.t = 2^48 - 1, higher key: OK at the ceiling",
             R = OK and V.T = U48'Last);
   end;

   --  No roster yet: W is empty, so no key can write.
   declare
      T : State := New_State (4);
   begin
      Seq := 0;
      Do_Emit (T, Put_T (1, 'n'), 12_345, Self, HC, Seq, V, R);
      Check ("no GRANT: Inadmissible, nothing changed",
             R = Inadmissible and V = No_V and Seq = 0 and not Cl);
      --  Granted, but no roster: ceiling 0, each write is at t = 0.
      Grant_Writers (T);
      Do_Emit (T, Put_T (1, 'n'), 12_345, Self, HC, Seq, V, R);
      Check ("ceiling 0: t = 0", R = OK and V.T = 0 and Seq = 1);
   end;

   --  Non-member key: refused, nothing changes (DESIGN.md §4).
   Seq := 40;
   Do_Emit (S, Put_T (1, 'n'), 100, Key (8), HC, Seq, V, R);
   Check ("non-member key: Inadmissible, nothing changed",
          R = Inadmissible and V = No_V and Seq = 40);

   --  H8: backup restore / clone self-detection, on a fresh collection.
   declare
      U : State := New_State (32);
      F : Version;
   begin
      Grant_Writers (U);
      Apply (U, Roster (1, 10_000, 1), St);
      --  The device emitted seq 50 before. A restore set seq_self to 10.
      Apply (U, Put (1, 'n', Ver (9_000, 3, 50, 50)), St);
      Check ("setup: own record with seq 50 held", St = OK);
      Seq := 10;
      Do_Emit (U, Put_T (1, 'n'), 0, Self, HC, Seq, V, R);
      Check ("restored seq: CLONE_SUSPECTED, seq jumps past the held 50",
             R = OK and Cl and V.Seq = 51 and Seq = 51 and V.T = 9_001);
      Do_Emit (U, Put_T (1, 'n'), 0, Self, HC, Seq, V, R);
      Check ("after the jump: ordinary write, seq + 1",
             R = OK and not Cl and V.Seq = 52 and Seq = 52);
      Seq := 10;
      Do_Emit (U, Put_T (2, 'z'), 5, Self, HC, Seq, V, R);
      Check ("restored seq detected from another cell's record",
             R = OK and Cl and V.Seq = 51 and V.T = 5);
      Seq := 50;
      Do_Emit (U, Put_T (2, 'z'), 5, Self, HC, Seq, V, R);
      Check ("held own seq = seq_self is not a clone",
             R = OK and not Cl and V.Seq = 51);
      --  A record of a different key with a high seq is not a record of
      --  this device.
      Apply (U, Put (7, 'n', Ver (100, 2, 900, 51)), St);
      Seq := 60;
      Do_Emit (U, Put_T (7, 'n'), 0, Self, HC, Seq, V, R);
      Check ("other author's high seq: no clone", R = OK and not Cl
             and V.Seq = 61 and V.T = 101);

      --  The floor is exactly the version that a restored device would
      --  emit again: (ceil, self, seq_self + 1, h). Without H8, the write
      --  would be equal to the floor. With H8, seq jumps and the write
      --  wins.
      Seq := 60;
      F := (T => 10_000, Author => Self, Seq => 61, H => HC);
      Apply (U, Put (3, 'n', F), St);
      Check ("setup: floor = (ceil, self, seq_self + 1, h) held", St = OK);
      Do_Emit (U, Put_T (3, 'n'), 0, Self, HC, Seq, V, R);
      Check ("v_emit = floor is impossible: seq jumps, OK above the floor",
             R = OK and Cl and V.Seq = 62 and V.T = 10_000 and Lt (F, V)
             and V /= F);
      Apply (U, To_Header (Put_T (3, 'n'), V), St);
      Check ("that write applied is held, the floor freed",
             St = OK and Holds (U, To_Header (Put_T (3, 'n'), V))
             and not Holds (U, Put (3, 'n', F)));

      --  DEL with a nonzero FH in the target: Choose ignores FH.
      Apply (U, Put (5, 'a', Ver (400, 2, 1, 1)), St);
      Seq := 100;
      Do_Emit (U, (Op => W_Del, NS => NS, Ent => Ent (5), FH => Fld ('z')),
               0, Self, HC, Seq, V, R);
      Check ("DEL with nonzero target FH: floor spans the entity",
             R = OK and V.T = 401
             and To_Header ((Op => W_Del, NS => NS, Ent => Ent (5),
                             FH => Fld ('z')), V)
                 = To_Header (Del_T (5), V)
             and To_Header (Del_T (5), V).FH = Key256'(others => 0));

      --  In_Floor excludes different entities and different fields.
      Apply (U, Put (11, 'n', Ver (9_500, 2, 2, 2)), St);
      Apply (U, Del (12, Ver (9_600, 2, 3, 3)), St);
      Apply (U, Put (10, 'm', Ver (9_700, 2, 4, 4)), St);
      Check ("setup: neighbours held", St = OK);
      Do_Emit (U, Put_T (10, 'n'), 100, Self, HC, Seq, V, R);
      Check ("other entities and fields are not the PUT's floor",
             R = OK and V.T = 100);
      Do_Emit (U, Del_T (10), 100, Self, HC, Seq, V, R);
      Check ("DEL floor spans the entity's other field only",
             R = OK and V.T = 9_701);
      Lemma_Floor_Admitted (U, Put_T (1, 'n'));
   end;

   --  H8 jump at the bound: after a held own record at seq 2^48 - 1, no
   --  seq is available. Choose refuses and changes nothing. It also gives
   --  the clone flag.
   declare
      X : State := New_State (8);
   begin
      Grant_Writers (X);
      Apply (X, Roster (1, 10_000, 1), St);
      Apply (X, Put (4, 'n', Ver (5, 3, U48'Last, 9)), St);
      Check ("setup: own record at seq 2^48 - 1 held", St = OK);
      Seq := 10;
      V := Ver (1, 1, 1, 1);
      Do_Emit (X, Put_T (1, 'n'), 0, Self, HC, Seq, V, R);
      Check ("jump past 2^48 - 1: Seq_Exhausted, clone, nothing changed",
             R = Seq_Exhausted and Cl and Seq = 10 and V = No_V);
   end;

   --  (m) Seq_Exhausted after an H8 jump to 2^48 - 1. A held own record at
   --  seq 2^48 - 2 makes a restored device jump to 2^48 - 1 (an ordinary
   --  write, with the clone flag). When the state holds that write, no seq
   --  is available.
   declare
      M : State := New_State (8);
   begin
      Grant_Writers (M);
      Apply (M, Roster (1, 10_000, 1), St);
      Apply (M, Put (4, 'n', Ver (5, 3, U48'Last - 1, 9)), St);
      Check ("setup: own record at seq 2^48 - 2 held", St = OK);
      Seq := 10;
      Do_Emit (M, Put_T (1, 'n'), 0, Self, HC, Seq, V, R);
      Check ("H8 jump to 2^48 - 1: OK, clone, seq = 2^48 - 1",
             R = OK and Cl and Seq = U48'Last and V.Seq = U48'Last);
      Apply (M, To_Header (Put_T (1, 'n'), V), St);
      Check ("the write at seq 2^48 - 1 is held",
             St = OK and Holds (M, To_Header (Put_T (1, 'n'), V)));
      Do_Emit (M, Put_T (2, 'n'), 0, Self, HC, Seq, V, R);
      Check ("after the jump to 2^48 - 1: Seq_Exhausted, seq unchanged",
             R = Seq_Exhausted and not Cl and Seq = U48'Last and V = No_V);
      Seq := 10;
      Do_Emit (M, Put_T (2, 'n'), 0, Self, HC, Seq, V, R);
      Check ("restored seq after the jump to 2^48 - 1: Seq_Exhausted, clone",
             R = Seq_Exhausted and Cl and Seq = 10 and V = No_V);
   end;

   --  (l) D8: the outcome does not depend on the content hash. Each case
   --  chooses once and builds the record under three hashes (all-zero,
   --  all-ones, and HC). Each record gets the predicted outcome.
   declare
      D : State := New_State (32);
   begin
      Grant_Writers (D);
      Apply (D, Roster (1, 10_000, 1), St);
      Apply (D, Put (1, 'n', Ver (9_000, 2, 1, 10)), St);
      Apply (D, Put (8, 'n', Ver (10_000, 5, 6, 30)), St);
      Apply (D, Put (9, 'n', Ver (10_000, 2, 7, 31)), St);
      --  Own record at the ceiling with seq 61 and h = HC, seq_self 60.
      --  Without H8, the all-zero h would lose and the all-ones h would
      --  win.
      Apply (D, Put (3, 'n', (T => 10_000, Author => Self, Seq => 61,
                              H => HC)), St);
      Check ("setup: D8 floors held", St = OK);
      Check ("D8: chase, OK under every h",
             Same_Under_Two_Hashes (D, Put_T (1, 'n'), 100, Self, 0, OK));
      Check ("D8: ceiling, floor key above: Shadowed (Dominated) under every h",
             Same_Under_Two_Hashes (D, Put_T (8, 'n'), 0, Self, 0, Shadowed));
      Check ("D8: ceiling, floor key below: OK under every h",
             Same_Under_Two_Hashes (D, Put_T (9, 'n'), 0, Self, 0, OK));
      Check ("D8: own floor, restored seq: OK under every h",
             Same_Under_Two_Hashes (D, Put_T (3, 'n'), 0, Self, 60, OK));
      Check ("D8: DEL above the entity's PUT: OK under every h",
             Same_Under_Two_Hashes (D, Del_T (1), 0, Self, 0, OK));
      Check ("D8: no floor: OK under every h",
             Same_Under_Two_Hashes (D, Put_T (20, 'n'), 7, Self, 0, OK));
   end;

   Check ("every chosen Seq equals the new Seq_Self; every GRANT applied",
          Out_Ok);

   --  Lemmas at run time.
   Lemma_Emit_Bounded (5, True, 3, 4);
   Lemma_T_Emit_Formula (5, 3, 4);
   Lemma_T_Emit_Formula (0, U48'Last, U48'Last);
   Lemma_Chase (0, 100, Ver (50, 9, 9, 9), (T => T_Emit (0, True, 50, 100),
                                             Author => Key (1), Seq => 1,
                                             H => Hsh (1)));
   Lemma_Shadow_At_Ceiling (0, 100, Ver (100, 9, 9, 9),
                            (T => T_Emit (0, True, 100, 100), Author => Key (1),
                             Seq => 1, H => Hsh (1)));
   Lemma_Raise_Unpins (0, 100, 200, Ver (100, 9, 9, 9),
                       (T => T_Emit (0, True, 100, 200), Author => Key (1),
                        Seq => 1, H => Hsh (1)));
   Lemma_Respects_Clock (70, True, 10, 100);
   Check ("lemmas evaluated", True);

   if Failed then
      Set_Exit_Status (Failure);
   end if;
   end Run_All;

begin
   null;
end Test_Emit;
