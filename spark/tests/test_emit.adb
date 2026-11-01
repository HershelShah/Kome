--  Test main for Kome.Emit: the write path of DESIGN.md §5 on states built
--  with Kome.Frontier.Apply. (a) chase above a far-future floor; (b) at the
--  ceiling: Shadowed when the floor wins the tie, OK when the write does,
--  and unshadowed once a roster raises the ceiling (T9); (c) seq exhaustion
--  refuses with nothing changed (T13); (d) no clock (Now = 0) still chases;
--  (e) a DEL's floor spans every field and the prior DELs, a PUT's floor
--  includes the entity's DEL; (f) floor.t = 2^48 - 1 does not wrap; (g) an
--  OK write applied back to the state is held (read-your-writes, T8);
--  (h) H8 restore/clone detection: seq jumps past a held own record and
--  Clone_Suspected is raised, so v_emit never equals a held version; (i) a
--  non-member key is Inadmissible; (j) In_Floor excludes neighbours; (k)
--  the state-level T9 lemmas.
--  Contracts and lemmas are executed (-gnata).
pragma Ada_2022;
with Ada.Text_IO;      use Ada.Text_IO;
with Ada.Command_Line; use Ada.Command_Line;
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

   NS : constant Id128 := (others => 7);

   function Key (B : Byte) return Key256 is (others => Word (B));
   function Hsh (B : Byte) return Key256 is (others => Word (B));
   function Ent (B : Byte) return Id128 is (others => Word (B));
   function Fld (C : Character) return Key256 is
     (others => Word (Character'Pos (C)));

   function Ver (T : U48; A : Byte; Seq : U48; H : Byte) return Version is
     (T => T, Author => Key (A), Seq => Seq, H => Hsh (H));

   function Put (E : Byte; F : Character; V : Version) return Header is
     (K => K_Put, NS => NS, Ent => Ent (E), FH => Fld (F), V => V,
      Ceiling => 0);

   function Del (E : Byte; V : Version) return Header is
     (K => K_Del, NS => NS, Ent => Ent (E), FH => Hsh (0), V => V,
      Ceiling => 0);

   function Roster (Gen, Ceiling : U48; H : Byte) return Header is
     (K => K_Roster, NS => NS, Ent => Ent (0), FH => Hsh (0),
      V => (T => 0, Author => Key (9), Seq => Gen, H => Hsh (H)),
      Ceiling => Ceiling);

   function Put_T (E : Byte; F : Character) return Target is
     (Op => W_Put, NS => NS, Ent => Ent (E), FH => Fld (F));
   function Del_T (E : Byte) return Target is
     (Op => W_Del, NS => NS, Ent => Ent (E), FH => (others => 0));

   None : constant Member_Keys (1 .. 0) := [];
   --  Writers: 1, 2, 3 (this device), 5 (a key above 3), 6 (above 5).
   W    : constant Member_Keys (1 .. 5) :=
     [Key (1), Key (2), Key (3), Key (5), Key (6)];
   No_V : constant Version := (others => <>);

   Self : constant Key256 := Key (3);
   HC   : constant Key256 := Hsh (77);   --  the caller's content hash

   S   : State := Empty (NS, 64);
   St  : Status;
   R   : Status;
   Seq : U48;
   V   : Version;
   Cl  : Boolean;   --  Clone_Suspected of the last call

   procedure Do_Emit
     (X    : State; Tgt : Target; Now : U48; Self : Key256; H : Key256;
      Seq  : in out U48; V : out Version; R : out Status) is
   begin
      Emit_Version (X, Tgt, Now, Self, H, Seq, V, R, Cl);
   end Do_Emit;

   procedure Apply_Data (X : Header) is
   begin
      Apply (S, X, None, St);
   end Apply_Data;

begin
   Apply (S, Roster (1, 10_000, 1), W, St);
   Check ("setup: roster ceiling 10000", St = OK and Ceil (Regs (S)) = 10_000);

   --  (d) No floor, no clock: t = 0.
   Seq := 0;
   Do_Emit (S, Put_T (1, 'n'), 0, Self, HC, Seq, V, R);
   Check ("no floor, Now = 0: t = 0, OK, seq 1",
          R = OK and V.T = 0 and V.Seq = 1 and Seq = 1 and not Cl
          and V.Author = Self and V.H = HC);

   --  No floor, clock beyond the ceiling: clamped.
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

   --  (d) No clock still chases.
   Do_Emit (S, Put_T (1, 'n'), 0, Self, HC, Seq, V, R);
   Check ("Now = 0 chases the floor", R = OK and V.T = 9_001);

   --  (g) Read-your-writes: the emitted PUT, applied, replaces the floor.
   declare
      P : constant Header := To_Header (Put_T (1, 'n'), V);
   begin
      Apply_Data (P);
      Check ("emitted PUT applied is held, floor gone",
             St = OK and Holds (S, P)
             and not Holds (S, Put (1, 'n', Ver (9_000, 2, 1, 10))));
   end;

   --  (e) PUT floor includes the entity's DEL.
   Apply_Data (Del (4, Ver (700, 2, 2, 20)));
   Do_Emit (S, Put_T (4, 'q'), 10, Self, HC, Seq, V, R);
   Check ("PUT chases the entity's DEL", R = OK and V.T = 701);

   --  DEL floor spans every field and the prior DELs.
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
      Apply (S, Roster (2, 20_000, 2), W, St);
      Check ("setup: ceiling raised to 20000",
             St = OK and Ceil (Regs (S)) = 20_000);
      --  T9 state form: every floor of the new state is under its ceiling.
      Lemma_Roster_Unpins (S1, S, Put_T (8, 'n'));
      Lemma_Roster_Unpins (S1, S, Del_T (6));
   end;
   Do_Emit (S, Put_T (8, 'n'), 0, Self, HC, Seq, V, R);
   Check ("after the raise the same cell is unshadowed",
          R = OK and V.T = 10_001 and Lt (Ver (10_000, 5, 6, 30), V));

   --  (c) Seq exhaustion: nothing emitted, Seq_Self unchanged.
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
      T : State := Empty (NS, 8);
   begin
      Apply (T, Roster (1, U48'Last, 1), W, St);
      Apply (T, Put (1, 'n', Ver (U48'Last, 5, 1, 40)), None, St);
      Check ("setup: PUT at t = 2^48 - 1 held", St = OK);
      Seq := 10;
      Do_Emit (T, Put_T (1, 'n'), 0, Self, HC, Seq, V, R);
      Check ("floor.t = 2^48 - 1: t = ceiling, Shadowed, no wrap",
             R = Shadowed and V.T = U48'Last and Seq = 11);
      Do_Emit (T, Put_T (1, 'n'), 0, Key (6), HC, Seq, V, R);
      Check ("floor.t = 2^48 - 1, higher key: OK at the ceiling",
             R = OK and V.T = U48'Last);
   end;

   --  No roster yet: W is empty, so nobody may write.
   declare
      T : State := Empty (NS, 4);
   begin
      Seq := 0;
      Do_Emit (T, Put_T (1, 'n'), 12_345, Self, HC, Seq, V, R);
      Check ("no roster: Inadmissible, nothing changed",
             R = Inadmissible and V = No_V and Seq = 0 and not Cl);
      --  Ceiling 0: every write is at t = 0.
      Apply (T, Roster (1, 0, 1), W, St);
      Do_Emit (T, Put_T (1, 'n'), 12_345, Self, HC, Seq, V, R);
      Check ("ceiling 0: t = 0", R = OK and V.T = 0 and Seq = 1);
   end;

   --  Non-member key: refused, nothing changed (DESIGN.md §4).
   Seq := 40;
   Do_Emit (S, Put_T (1, 'n'), 100, Key (8), HC, Seq, V, R);
   Check ("non-member key: Inadmissible, nothing changed",
          R = Inadmissible and V = No_V and Seq = 40);

   --  H8: backup restore / clone self-detection, on a fresh collection.
   declare
      U : State := Empty (NS, 32);
      F : Version;
   begin
      Apply (U, Roster (1, 10_000, 1), W, St);
      --  The device already emitted seq 50; seq_self was restored to 10.
      Apply (U, Put (1, 'n', Ver (9_000, 3, 50, 50)), None, St);
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
      --  Another key's record with a high seq is not this device's.
      Apply (U, Put (7, 'n', Ver (100, 2, 900, 51)), None, St);
      Seq := 60;
      Do_Emit (U, Put_T (7, 'n'), 0, Self, HC, Seq, V, R);
      Check ("other author's high seq: no clone", R = OK and not Cl
             and V.Seq = 61 and V.T = 101);

      --  The floor is exactly the version a restored device would emit
      --  again: (ceil, self, seq_self + 1, h). Without H8 the write would
      --  equal the floor; with it, seq jumps and the write wins.
      Seq := 60;
      F := (T => 10_000, Author => Self, Seq => 61, H => HC);
      Apply (U, Put (3, 'n', F), None, St);
      Check ("setup: floor = (ceil, self, seq_self + 1, h) held", St = OK);
      Do_Emit (U, Put_T (3, 'n'), 0, Self, HC, Seq, V, R);
      Check ("v_emit = floor is impossible: seq jumps, OK above the floor",
             R = OK and Cl and V.Seq = 62 and V.T = 10_000 and Lt (F, V)
             and V /= F);
      Apply (U, To_Header (Put_T (3, 'n'), V), None, St);
      Check ("that write applied is held, the floor freed",
             St = OK and Holds (U, To_Header (Put_T (3, 'n'), V))
             and not Holds (U, Put (3, 'n', F)));

      --  DEL with a nonzero FH in the target: FH is ignored.
      Apply (U, Put (5, 'a', Ver (400, 2, 1, 1)), None, St);
      Seq := 100;
      Do_Emit (U, (Op => W_Del, NS => NS, Ent => Ent (5), FH => Fld ('z')),
               0, Self, HC, Seq, V, R);
      Check ("DEL with nonzero target FH: floor spans the entity",
             R = OK and V.T = 401
             and To_Header ((Op => W_Del, NS => NS, Ent => Ent (5),
                             FH => Fld ('z')), V)
                 = To_Header (Del_T (5), V)
             and To_Header (Del_T (5), V).FH = Key256'(others => 0));

      --  In_Floor excludes other entities and other fields.
      Apply (U, Put (11, 'n', Ver (9_500, 2, 2, 2)), None, St);
      Apply (U, Del (12, Ver (9_600, 2, 3, 3)), None, St);
      Apply (U, Put (10, 'm', Ver (9_700, 2, 4, 4)), None, St);
      Check ("setup: neighbours held", St = OK);
      Do_Emit (U, Put_T (10, 'n'), 100, Self, HC, Seq, V, R);
      Check ("other entities and fields are not the PUT's floor",
             R = OK and V.T = 100);
      Do_Emit (U, Del_T (10), 100, Self, HC, Seq, V, R);
      Check ("DEL floor spans the entity's other field only",
             R = OK and V.T = 9_701);
      Lemma_Floor_Admitted (U, Put_T (1, 'n'));
   end;

   --  H8 jump at the bound: a held own record at seq 2^48 - 1 leaves no
   --  seq to emit; refused with nothing changed, clone still reported.
   declare
      X : State := Empty (NS, 8);
   begin
      Apply (X, Roster (1, 10_000, 1), W, St);
      Apply (X, Put (4, 'n', Ver (5, 3, U48'Last, 9)), None, St);
      Check ("setup: own record at seq 2^48 - 1 held", St = OK);
      Seq := 10;
      V := Ver (1, 1, 1, 1);
      Do_Emit (X, Put_T (1, 'n'), 0, Self, HC, Seq, V, R);
      Check ("jump past 2^48 - 1: Seq_Exhausted, clone, nothing changed",
             R = Seq_Exhausted and Cl and Seq = 10 and V = No_V);
   end;

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
end Test_Emit;
