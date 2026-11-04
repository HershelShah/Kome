--  Test main for Kome.Views: the views of DESIGN.md §3 and §6 over states
--  built with Kome.Frontier.Apply. Contracts and ghost lemmas run on the
--  test data (-gnata). The tests include:
--  (a) cell / deleted_at / exists through a PUT, a newer PUT, a DEL and a
--      PUT that creates the entity again;
--  (b) void at, below and above from_t, and for a different author;
--  (c) ROSTER_eff across signers and under a founding root revocation;
--  (d) T5: Lemma_Cell_Unique / Lemma_Del_Unique / Lemma_Roster_Unique on
--      each pair that they apply to, and each view from two arrival orders;
--  (e) T12:
--      - around each applied ROSTER, REVOKE and GRANT (held, dominated, or
--        refused with Auth_Full), Lemma_Apply_Auth_Local then
--        Lemma_Views_Local;
--      - around each PUT and DEL (held, Dominated, Inadmissible or
--        No_Space), Lemma_Apply_Data_Local then each authorization-view
--        locality lemma;
--      - root_void only grows;
--  (f) root revocation as decided (D2): a compromised certified root, its
--      root-void by the founding key, W_eff (D1′), re-signed revocations,
--      del_ttl_eff, a stale same-signer roster;
--  (g) the hypothesis boundary: rosters that are equal in V but different
--      in del_ttl (A2 fails) still give one ROSTER_eff in each order (full
--      tie-break).
pragma Ada_2022;
with Ada.Text_IO;      use Ada.Text_IO;
with Ada.Command_Line; use Ada.Command_Line;
with Ada.Exceptions;   use Ada.Exceptions;
with Kome;             use Kome;
with Kome.Versions;    use Kome.Versions;
with Kome.Headers;     use Kome.Headers;
with Kome.Frontier;    use Kome.Frontier;
with Kome.Views;       use Kome.Views;

procedure Test_Views with SPARK_Mode => Off is

   Failed : Boolean := False;

   procedure Check (Name : String; Cond : Boolean) is
   begin
      Put_Line ((if Cond then "PASS " else "FAIL ") & Name);
      if not Cond then
         Failed := True;
      end if;
   end Check;

   NS  : constant Id128 := (others => 7);
   Fnd : constant Byte := 9;                 --  the founding key

   function Key (B : Byte) return Key256 is (others => Word (B));
   function Hsh (B : Natural) return Key256 is (W0 => Word (B), others => 5);
   function Ent (B : Byte) return Id128 is (others => Word (B));
   function Fld (C : Character) return Key256 is
     (others => Word (Character'Pos (C)));

   function V (T : U48; A : Byte; Seq : U48; H : Natural) return Version is
     (T => T, Author => Key (A), Seq => Seq, H => Hsh (H));

   function Put (E : Byte; F : Character; Ver : Version) return Header is
     (K => K_Put, NS => NS, Ent => Ent (E), FH => Fld (F), V => Ver,
      Issuer => Zero_Key, Del_TTL => 0, Epoch => 0);

   function Del (E : Byte; Ver : Version) return Header is
     (K => K_Del, NS => NS, Ent => Ent (E), FH => Zero_Key, V => Ver,
      Issuer => Zero_Key, Del_TTL => 0, Epoch => 0);

   --  V = (ceiling_t, signer, gen, h), Issuer = signer.
   function Roster (Signer : Byte; Gen, Ceiling : U48; H : Natural;
                    TTL : U48 := Del_TTL_Default; E : Kome.Epoch := 0) return Header is
     (K => K_Roster, NS => NS, Ent => Zero_Id, FH => Zero_Key,
      V => (T => Ceiling, Author => Key (Signer), Seq => Gen, H => Hsh (H)),
      Issuer => Key (Signer), Del_TTL => TTL, Epoch => E);

   --  V = (cap, subject, 0, h), Issuer = signer. The cap is unbounded
   --  unless Cap says otherwise.
   function Grant (Issuer, Subject : Byte; H : Natural; Cap : U48 := U48'Last) return Header is
     (K => K_Grant, NS => NS, Ent => Zero_Id, FH => Zero_Key,
      V => (T => Cap, Author => Key (Subject), Seq => 0, H => Hsh (H)),
      Issuer => Key (Issuer), Del_TTL => 0, Epoch => 0);

   --  V = (from_t, subject, rev_seq, h), Issuer = signer.
   function Revoke (Issuer, Subject : Byte; From_T : U48; H : Natural) return Header is
     (K => K_Revoke, NS => NS, Ent => Zero_Id, FH => Zero_Key,
      V => (T => From_T, Author => Key (Subject), Seq => 1, H => Hsh (H)),
      Issuer => Key (Issuer), Del_TTL => 0, Epoch => 0);

   function New_State (Cap : Data_Size := 64; Slice : Slice_Count := 16) return State is
     (Empty (NS, Key (Fnd), Cap, Slice));

   function All_Canonical (S : State) return Boolean is
     (for all I in 1 .. Kome.Frontier.Count (S) => Canonical (Held (S, I)));

   --  A2 on the held set, computed. Unique_Versions is ghost, so a test
   --  verdict cannot use it directly. The assertion ties the two together.
   function Versions_Unique (S : State) return Boolean is
     (for all I in 1 .. Kome.Frontier.Count (S) =>
        (for all J in 1 .. Kome.Frontier.Count (S) =>
           (if Held (S, I).V = Held (S, J).V then Held (S, I) = Held (S, J))));

   function A2 (S : State) return Boolean is
      R : constant Boolean := Versions_Unique (S);
   begin
      pragma Assert (R = Unique_Versions (S));
      return R;
   end A2;

   function Index_In (S : State; X : Header) return Natural is
   begin
      for I in 1 .. Kome.Frontier.Count (S) loop
         if Held (S, I) = X then
            return I;
         end if;
      end loop;
      return 0;
   end Index_In;

   --  The fields and entities on which the test compares the data views.
   type Probe is record
      E : Byte;
      F : Character;
   end record;
   Probes : constant array (1 .. 6) of Probe :=
     [(1, 'n'), (1, 'a'), (1, 'z'), (2, 'n'), (3, 'n'), (0, 'n')];

   --  The keys and records on which the test compares the authorization
   --  views.
   type Key_List is array (Positive range <>) of Byte;
   Keys : constant Key_List := [1, 2, 4, 6, 8, 9, 20, 21, 30];

   type Header_List is array (Positive range <>) of Header;

   function Same_Views (A, B : State) return Boolean is
   begin
      for P of Probes loop
         if Cell (A, NS, Ent (P.E), Fld (P.F)) /= Cell (B, NS, Ent (P.E), Fld (P.F))
           or else Deleted_At (A, NS, Ent (P.E)) /= Deleted_At (B, NS, Ent (P.E))
           or else Exists (A, NS, Ent (P.E)) /= Exists (B, NS, Ent (P.E))
         then
            return False;
         end if;
      end loop;
      return True;
   end Same_Views;

   --  T5: Lemma_Cell_Unique / Lemma_Del_Unique / Lemma_Roster_Unique on
   --  each pair that they apply to. It returns the number of checked pairs.
   function Unique_Checked (S : State) return Natural is
      N : Natural := 0;
   begin
      for I in 1 .. Kome.Frontier.Count (S) loop
         for J in 1 .. Kome.Frontier.Count (S) loop
            declare
               X : constant Header := Held (S, I);
            begin
               if X.K = K_Put and then Put_On (Held (S, J), X.NS, X.Ent, X.FH) then
                  Lemma_Cell_Unique (S, I, J);
                  N := N + 1;
               elsif X.K = K_Del and then Del_On (Held (S, J), X.NS, X.Ent) then
                  Lemma_Del_Unique (S, I, J);
                  N := N + 1;
               elsif X.K = K_Roster and then Held (S, J).K = K_Roster
                 and then not Roster_Lt (X, Held (S, J))
                 and then not Roster_Lt (Held (S, J), X)
               then
                  Lemma_Roster_Unique (S, I, J);
                  N := N + 1;
               end if;
            end;
         end loop;
      end loop;
      return N;
   end Unique_Checked;

   --  Each definition lemma on the probes (their Posts run under -gnata).
   procedure Def_Lemmas (S : State; Void_Probes : Header_List) is
   begin
      for P of Probes loop
         Lemma_Cell_Def (S, NS, Ent (P.E), Fld (P.F));
         Lemma_Deleted_At_Def (S, NS, Ent (P.E));
         Lemma_Exists_Def (S, NS, Ent (P.E));
         Lemma_Exists_Cell (S, NS, Ent (P.E), Fld (P.F));
      end loop;
      for K of Keys loop
         Lemma_Root_Void_Def (S, Key (K));
         Lemma_Root_Void_Slot (S, Key (K));
         Lemma_W_Eff_Def (S, Key (K));
      end loop;
      for P of Void_Probes loop
         Lemma_Is_Void_Def (S, P);
      end loop;
      Lemma_Roster_Eff_Def (S);
      Lemma_Del_TTL_Eff_Def (S);
   end Def_Lemmas;

   function Same_Auth_Views (A, B : State; Void_Probes : Header_List) return Boolean is
   begin
      if Roster_Eff (A) /= Roster_Eff (B) or else Del_TTL_Eff (A) /= Del_TTL_Eff (B) then
         return False;
      end if;
      for K of Keys loop
         if Root_Void (A, Key (K)) /= Root_Void (B, Key (K))
           or else W_Eff (A, Key (K)) /= W_Eff (B, Key (K))
         then
            return False;
         end if;
      end loop;
      for P of Void_Probes loop
         if Is_Void (A, P) /= Is_Void (B, P) or else Revoke_Void (A, P) /= Revoke_Void (B, P) then
            return False;
         end if;
      end loop;
      return True;
   end Same_Auth_Views;

   St : Status;

   --  Apply an authorization record and check T12 around it:
   --    * the lemma chain runs (and its contracts are evaluated);
   --    * the data views on each probe do not change, for all values of
   --      Status;
   --    * root_void only grows.
   procedure Apply_Auth
     (T : in out State; R : Header; Name : String; Expect : Status := OK)
   is
      Old : constant State := T;
   begin
      Apply (T, R, St);
      Lemma_Apply_Auth_Local (Old, T, R);
      Lemma_Apply_Keeps_Revokes (Old, T, R);
      for P of Probes loop
         Lemma_Views_Local (Old, T, NS, Ent (P.E), Fld (P.F));
      end loop;
      for K of Keys loop
         Lemma_Root_Void_Monotone (Old, T, Key (K));
      end loop;
      Check ("T12: data views unchanged by " & Name & " (" & Status'Image (St) & ")",
             St = Expect and then Same_Views (Old, T));
   end Apply_Auth;

   --  Apply a data record and check the converse: root_void, W_eff, void,
   --  ROSTER_eff and del_ttl_eff do not change. The check uses
   --  Lemma_Apply_Data_Local and the authorization-view locality lemmas.
   procedure Apply_Data
     (T : in out State; R : Header; Name : String; Void_Probes : Header_List;
      Expect : Status := OK)
   is
      Old : constant State := T;
   begin
      Apply (T, R, St);
      Lemma_Apply_Data_Local (Old, T, R);
      Lemma_Roster_Local (Old, T);
      Lemma_Del_TTL_Local (Old, T);
      for K of Keys loop
         Lemma_Root_Void_Local (Old, T, Key (K));
         Lemma_W_Eff_Local (Old, T, Key (K));
      end loop;
      for P of Void_Probes loop
         Lemma_Void_Local (Old, T, P);
      end loop;
      Check ("T12: authorization views unchanged by " & Name
             & " (" & Status'Image (St) & ")",
             St = Expect and then Same_Auth_Views (Old, T, Void_Probes));
   end Apply_Data;

   --  A complete reconciliation of a list: a refused record is offered
   --  again (DESIGN.md §4), so Run applies it in passes until no new record
   --  is held.
   function Run (L : Header_List) return State is
      S        : State := New_State;
      Progress : Boolean := True;
      Dummy    : Status;
   begin
      while Progress loop
         Progress := False;
         for R of L loop
            declare
               Was : constant Boolean := Holds (S, R);
            begin
               Apply (S, R, Dummy);
               if not Was and then Holds (S, R) then
                  Progress := True;
               end if;
            end;
         end loop;
      end loop;
      return S;
   end Run;

   procedure Run_All;

   --  A State has a Register_File of Writers_Max keys (256 KiB). Under
   --  -gnata, each Post evaluation copies states, so the checks run in a
   --  task with a large stack.
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

      RF  : constant Header := Roster (Fnd, 1, 5000, 1);
      GF1 : constant Header := Grant (Fnd, 1, 31);
      GF2 : constant Header := Grant (Fnd, 2, 32);
      P1  : constant Header := Put (1, 'n', V (100, 1, 1, 10));
      P2  : constant Header := Put (1, 'n', V (200, 2, 1, 11));   --  beats P1
      P3  : constant Header := Put (1, 'a', V (150, 1, 2, 12));   --  other field
      P5  : constant Header := Put (2, 'n', V (120, 1, 3, 15));   --  other entity
      D1  : constant Header := Del (1, V (300, 2, 2, 13));        --  beats P1..P3
      D0  : constant Header := Del (1, V (50, 1, 4, 16));         --  older DEL
      P4  : constant Header := Put (1, 'n', V (400, 1, 5, 14));   --  re-creates
      X2  : constant Header := Revoke (Fnd, 2, 250, 60);
      P6  : constant Header := Put (3, 'n', V (260, 2, 3, 17));   --  void
      P7  : constant Header := Put (3, 'a', V (250, 2, 4, 18));   --  void, t = from_t
      P8  : constant Header := Put (3, 'b', V (249, 2, 5, 19));   --  not void
      RS8 : constant Header := Roster (8, 3, 6000, 3);           --  second root
      R2  : constant Header := Roster (Fnd, 2, 7000, 2);         --  beats RF
      X8  : constant Header := Revoke (Fnd, 8, 0, 61);           --  root-voids 8

      Void_Probes : constant Header_List := [P6, P7, P8, P2, P4];

      S : State := New_State;

   begin
      Lemma_No_Header_Not_Canonical;
      Check ("No_Header is not canonical", not Canonical (No_Header));
      Check ("empty state: no cell, no DEL, nothing exists, no roster, default del_ttl",
             not Cell (S, NS, Ent (1), Fld ('n')).Present
             and Cell (S, NS, Ent (1), Fld ('n')).Hdr = No_Header
             and not Deleted_At (S, NS, Ent (1)).Present
             and not Exists (S, NS, Ent (1))
             and not Roster_Eff (S).Present
             and Del_TTL_Eff (S) = Del_TTL_Default
             and Max_Ceil (S) = 0
             and not Is_Writer (S, Key (1)));
      Check ("empty state: a record with no grant is void, nothing root-void",
             Is_Void (S, P1) and not Revoke_Void (S, P1)
             and not Root_Void (S, Key (8)) and not Root_Void (S, Key (Fnd)));
      Def_Lemmas (S, Void_Probes);

      Apply_Auth (S, RF, "first roster");
      Check ("roster held", St = OK and Holds (S, RF));
      Check ("ROSTER_eff is the only roster", Roster_Eff (S) = (Present => True, Hdr => RF));
      Apply_Auth (S, GF1, "GRANT of writer 1");
      Apply_Auth (S, GF2, "GRANT of writer 2");
      Check ("named views: maxceil and W",
             Max_Ceil (S) = 5000 and Is_Writer (S, Key (1)) and Is_Writer (S, Key (2))
             and W_Eff (S, Key (1)) and W_Eff (S, Key (2)) and not W_Eff (S, Key (3)));

      --  (a) cell, exists, deleted_at.
      Apply_Data (S, P1, "P1", Void_Probes);
      Apply_Data (S, P3, "P3", Void_Probes);
      Apply_Data (S, P5, "P5", Void_Probes);
      Check ("cell is the held PUT",
             Cell (S, NS, Ent (1), Fld ('n')) = (Present => True, Hdr => P1)
             and Cell (S, NS, Ent (1), Fld ('a')) = (Present => True, Hdr => P3)
             and Cell (S, NS, Ent (2), Fld ('n')) = (Present => True, Hdr => P5));
      Check ("absent field has no cell",
             Cell (S, NS, Ent (1), Fld ('z')) = (Present => False, Hdr => No_Header));
      Check ("another collection has no cell",
             not Cell (S, (others => 8), Ent (1), Fld ('n')).Present
             and not Exists (S, (others => 8), Ent (1)));
      Check ("entity with a live PUT exists",
             Exists (S, NS, Ent (1)) and Exists (S, NS, Ent (2))
             and not Exists (S, NS, Ent (3)));
      Check ("no held record equals No_Header", not Holds (S, No_Header));
      Apply_Data (S, P2, "P2", Void_Probes);
      Check ("newer PUT is the cell",
             St = OK and Cell (S, NS, Ent (1), Fld ('n')) = (Present => True, Hdr => P2));
      Check ("no DEL yet",
             Deleted_At (S, NS, Ent (1)) = (Present => False, V => No_Version));
      Check ("T5: unique on every PUT/roster pair", Unique_Checked (S) = 4);

      --  T12 converse with each data refusal: Dominated,
      --  Inadmissible (author not in W; t above maxceil).
      Apply_Data (S, P1, "a dominated PUT", Void_Probes, Expect => Dominated);
      Apply_Data (S, Put (1, 'q', V (100, 30, 1, 70)), "a PUT by a key not in W",
                  Void_Probes, Expect => Inadmissible);
      Apply_Data (S, Put (1, 'q', V (9000, 1, 9, 71)), "a PUT above maxceil",
                  Void_Probes, Expect => Inadmissible);

      Apply_Data (S, D0, "D0", Void_Probes);
      Check ("older DEL held beside newer PUTs",
             St = OK and Deleted_At (S, NS, Ent (1)) = (Present => True, V => D0.V)
             and Exists (S, NS, Ent (1)));
      Apply_Data (S, D1, "D1", Void_Probes);
      Check ("deleted_at is the newest DEL",
             St = OK and Deleted_At (S, NS, Ent (1)) = (Present => True, V => D1.V));
      Check ("DEL removes every cell of the entity",
             not Cell (S, NS, Ent (1), Fld ('n')).Present
             and not Cell (S, NS, Ent (1), Fld ('a')).Present
             and not Exists (S, NS, Ent (1)));
      Check ("other entity untouched",
             Cell (S, NS, Ent (2), Fld ('n')) = (Present => True, Hdr => P5)
             and not Deleted_At (S, NS, Ent (2)).Present);
      Apply_Data (S, D0, "a dominated DEL", Void_Probes, Expect => Dominated);
      Apply_Data (S, P4, "P4", Void_Probes);
      Check ("later PUT re-creates the entity",
             Exists (S, NS, Ent (1))
             and Cell (S, NS, Ent (1), Fld ('n')) = (Present => True, Hdr => P4)
             and not Cell (S, NS, Ent (1), Fld ('a')).Present
             and Deleted_At (S, NS, Ent (1)) = (Present => True, V => D1.V));

      --  (b) void.
      Check ("nothing void before any REVOKE",
             not Is_Void (S, P2) and not Is_Void (S, P6) and not Is_Void (S, P4));
      Apply_Auth (S, X2, "REVOKE of a writer");
      Check ("REVOKE held", St = OK and Holds (S, X2));
      Check ("void at t > from_t", Is_Void (S, P6) and Revoke_Void (S, P6));
      Check ("void at t = from_t", Is_Void (S, P7));
      Check ("not void at t < from_t", not Is_Void (S, P8) and not Is_Void (S, P2));
      Check ("not void for another author", not Is_Void (S, P4));
      Apply_Data (S, P6, "P6", Void_Probes);
      Apply_Data (S, P7, "P7", Void_Probes);
      Apply_Data (S, P8, "P8", Void_Probes);
      Check ("void records stay held and visible as cells",
             Cell (S, NS, Ent (3), Fld ('n')) = (Present => True, Hdr => P6)
             and Is_Void (S, Cell (S, NS, Ent (3), Fld ('n')).Hdr)
             and Exists (S, NS, Ent (3)));
      Def_Lemmas (S, Void_Probes);

      --  (c) ROSTER_eff and root revocation.
      Apply_Auth (S, RS8, "roster of a second root");
      Check ("ROSTER_eff is the greater generation across signers",
             Roster_Eff (S) = (Present => True, Hdr => RS8) and Holds (S, RF));
      Apply_Auth (S, R2, "newer founding roster");
      Check ("per-signer domination: R2 replaces RF, RS8 still effective",
             Holds (S, R2) and not Holds (S, RF)
             and Roster_Eff (S) = (Present => True, Hdr => RS8));
      Check ("root not void before its REVOKE", not Root_Void (S, Key (8)));
      declare
         Before : constant State := S;
      begin
         Apply_Auth (S, X8, "founding REVOKE of a root");
         Check ("root void after the founding key's REVOKE",
                Root_Void (S, Key (8)) and not Root_Void (S, Key (Fnd)));
         Check ("ROSTER_eff skips the root-voided root's roster",
                Holds (S, RS8) and Roster_Eff (S) = (Present => True, Hdr => R2));
         for P of Void_Probes loop
            Lemma_Void_Monotone (Before, S, P);
         end loop;
         Check ("REVOKE clause of void only grows",
                Is_Void (S, P6) and Is_Void (S, P7) and not Is_Void (S, P8));
      end;
      Apply_Auth (S, RF, "dominated roster", Expect => Dominated);
      Check ("dominated roster not held, ROSTER_eff unchanged",
             not Holds (S, RF) and Roster_Eff (S) = (Present => True, Hdr => R2));
      Apply_Auth (S, GF1, "duplicate GRANT");
      Check ("all held records canonical and A2 holds", All_Canonical (S) and A2 (S));
      Check ("T5: unique on every PUT/DEL/roster pair (late)", Unique_Checked (S) = 8);
      declare
         I : constant Natural := Index_In (S, R2);
      begin
         Lemma_Roster_Eff_Unique (S, I);
         Lemma_Roster_Eff_Present (S);
         Check ("T5: the maximal eligible roster is ROSTER_eff", I /= 0);
      end;
      Def_Lemmas (S, Void_Probes);

      --  D2: a certified root cannot root-void a key, and the founding key
      --  is never root_void, so if a founding roster is held, ROSTER_eff
      --  is always present.
      declare
         T : State := S;
      begin
         Apply_Auth (T, Revoke (8, Fnd, 0, 62), "a certified root's REVOKE of the founding key");
         Apply_Auth (T, Revoke (Fnd, Fnd, 1_000_000, 63), "a REVOKE of the founding key by itself");
         Check ("the founding key is never root_void; ROSTER_eff stays the founding roster",
                not Root_Void (T, Key (Fnd))
                and Roster_Eff (T) = (Present => True, Hdr => R2));
         Lemma_Roster_Eff_Present (T);
         Def_Lemmas (T, Void_Probes);
      end;

      --  Data and authorization refusals for space (T12 both ways).
      declare
         T : State := New_State (Cap => 2, Slice => 2);
         VP : constant Header_List := [P1, P5];
      begin
         Apply_Auth (T, RF, "roster into a small state");
         Apply_Auth (T, GF1, "GRANT into a small state");
         Apply_Data (T, P1, "P1 into a small state", VP);
         Apply_Data (T, P5, "P5 into a small state", VP);
         Check ("small state: data row and founding slice full",
                Data_Count (T) = 2 and Slot_Count (T, 1) = 2);
         Apply_Data (T, P3, "a PUT into a full data row", VP, Expect => No_Space);
         Apply_Auth (T, GF2, "a GRANT into a full slice", Expect => Auth_Full);
         Apply_Auth (T, X2, "a REVOKE into a full slice", Expect => Auth_Full);
         Apply_Auth (T, Roster (Fnd, 2, 5000, 4), "a roster that frees its predecessor");
         Check ("a roster that frees its predecessor fits in a full slice",
                St = OK and not Holds (T, RF) and Holds (T, P1));
         Apply_Data (T, Put (1, 'n', V (200, 1, 6, 72)), "a PUT that frees what it dominates", VP);
         Check ("a PUT that frees what it dominates fits in a full row",
                St = OK and Holds (T, Put (1, 'n', V (200, 1, 6, 72))) and not Holds (T, P1));
         Def_Lemmas (T, VP);
      end;

      --  h decides between equal generations of two signers, in each
      --  order.
      declare
         RA : constant Header := Roster (5, 7, 100, 40);
         RB : constant Header := Roster (6, 7, 200, 30);
         A  : constant State := Run ([RA, RB]);
         B  : constant State := Run ([RB, RA]);
      begin
         Check ("equal gen, two signers: both held, greater h is ROSTER_eff",
                Holds (A, RA) and Holds (A, RB)
                and Roster_Eff (A) = (Present => True, Hdr => RA)
                and Roster_Eff (B) = (Present => True, Hdr => RA));
         Lemma_Roster_Local (A, B);
         Check ("T5: Lemma_Roster_Local on equal generations", A2 (A));
      end;

      --  A2: epoch comes first in the ROSTER_eff order. A roster at a
      --  newer epoch is effective whatever its gen, in each arrival order.
      declare
         RA : constant Header := Roster (5, 9, 100, 41, E => 4);
         RB : constant Header := Roster (6, 7, 200, 31, E => 5);
         A  : constant State := Run ([RA, RB]);
         B  : constant State := Run ([RB, RA]);
      begin
         Check ("epoch first: the roster at the newer epoch is ROSTER_eff despite a lower gen",
                Holds (A, RA) and Holds (A, RB)
                and Roster_Lt (RA, RB) and not Roster_Lt (RB, RA)
                and Roster_Eff (A) = (Present => True, Hdr => RB)
                and Roster_Eff (B) = (Present => True, Hdr => RB));
         Lemma_Dominates_Roster_Lt (Roster (5, 1, 100, 1), Roster (5, 2, 100, 2));
         Lemma_Roster_Local (A, B);
         Def_Lemmas (A, Void_Probes);
      end;

      --  H1: a same-signer roster at equal gen (a root restored from
      --  backup) does not evict the newer roster. Both stay, ROSTER_FORK
      --  reports the pair, and the roster at the higher epoch stays
      --  effective whatever its h.
      declare
         R6  : constant Header := Roster (5, 6, 300, 10, E => 7);   --  removes a member
         R6F : constant Header := Roster (5, 6, 300, 90, E => 6);   --  from the backup
         R7  : constant Header := Roster (5, 7, 300, 11, E => 8);   --  above both
         A   : constant State := Run ([R6, R6F]);
         B   : constant State := Run ([R6F, R6]);
         C   : State := A;
      begin
         Check ("H1: equal gen, same signer: both held, neither dominates",
                Holds (A, R6) and Holds (A, R6F) and Holds (B, R6) and Holds (B, R6F)
                and not Dominates (R6F, R6) and not Dominates (R6, R6F));
         Check ("H1: the roster at the higher epoch stays ROSTER_eff, in each order",
                Roster_Eff (A) = (Present => True, Hdr => R6)
                and Roster_Eff (B) = (Present => True, Hdr => R6));
         Check ("H1: ROSTER_FORK reports the pair, and nothing else",
                Roster_Fork (A) and Roster_Fork (B)
                and not Roster_Fork (Run ([R6])) and not Roster_Fork (Run ([R6, R7])));
         Lemma_Roster_Fork_Def (A);
         Lemma_Roster_Fork_Def (Run ([R6]));
         Apply_Auth (C, R7, "a roster above both forks");
         Check ("H1: a roster above both forks dominates both and clears the fork",
                Holds (C, R7) and not Holds (C, R6) and not Holds (C, R6F)
                and not Roster_Fork (C)
                and Roster_Eff (C) = (Present => True, Hdr => R7));
         Lemma_Roster_Local (A, B);
         Def_Lemmas (A, Void_Probes);
      end;

      --  A3: revoked(k) reads every counting REVOKE of k, whatever its
      --  from_t, so the gate can refuse a member before the roster that
      --  removes it arrives. A root-voided issuer's REVOKE stops counting.
      declare
         XF : constant Header := Revoke (Fnd, 3, 1_000_000, 71);   --  from_t in the future
         X8 : constant Header := Revoke (8, 4, 0, 72);             --  by root 8
         V8 : constant Header := Revoke (Fnd, 8, 0, 73);           --  root-void of 8
         A  : State := Run ([RF, XF, X8]);
      begin
         Check ("revoked: a REVOKE with a future from_t still revokes the key for the gate",
                Revoked (A, Key (3)) and not Revoke_Void (A, Put (1, 'n', V (5, 3, 1, 1))));
         Check ("revoked: a certified root's REVOKE counts, other keys are not revoked",
                Revoked (A, Key (4)) and not Revoked (A, Key (5)) and not Revoked (A, Key (Fnd)));
         Lemma_Revoked_Def (A, Key (3));
         Lemma_Revoked_Def (A, Key (5));
         Lemma_Revoke_Void_Revoked (A, Put (1, 'n', V (2_000_000, 3, 1, 1)));
         Apply_Auth (A, V8, "root-void of root 8");
         Check ("revoked: a root-voided root's REVOKE stops counting",
                not Revoked (A, Key (4)) and Revoked (A, Key (3)) and Revoked (A, Key (8)));
         Lemma_Revoked_Def (A, Key (4));
      end;

      --  (d) T5 across arrival orders: two states built from the same
      --  records in different orders hold the same records, and each view
      --  agrees.
      declare
         A : constant State :=
           Run ([RF, GF1, GF2, P1, P3, P5, P2, D0, D1, P4, X2, P6, P7, P8, RS8, R2, X8]);
         B : constant State :=
           Run ([X8, R2, RS8, P8, P7, P6, X2, P4, D1, D0, P2, P5, P3, P1, GF2, GF1, RF]);
      begin
         Check ("T5: same data views from two arrival orders", Same_Views (A, B));
         for P of Probes loop
            Lemma_Views_Local (A, B, NS, Ent (P.E), Fld (P.F));
         end loop;
         Lemma_Roster_Local (A, B);
         Lemma_Del_TTL_Local (A, B);
         for P of Void_Probes loop
            Lemma_Void_Local (A, B, P);
         end loop;
         for K of Keys loop
            Lemma_Root_Void_Local (A, B, Key (K));
            Lemma_W_Eff_Local (A, B, Key (K));
         end loop;
         Check ("T5: same authorization views from two orders",
                Same_Auth_Views (A, B, Void_Probes)
                and Roster_Eff (A) = (Present => True, Hdr => R2));
      end;

      --  (f) A compromised certified root (DESIGN.md §6, D1′, D2, D13).
      declare
         M1  : constant Byte := 1;    --  granted by the founding key and by R
         M2  : constant Byte := 2;    --  granted by H; revoked by R and re-revoked by F
         M4  : constant Byte := 4;    --  granted by H; revoked by R
         H   : constant Byte := 6;    --  an honest certified root
         R   : constant Byte := 8;    --  the compromised certified root
         K2  : constant Byte := 20;   --  granted by R only
         K3  : constant Byte := 21;   --  granted by R after its root-void
         Day : constant U48 := 86_400_000;

         CRF : constant Header := Roster (Fnd, 1, 10_000, 11);
         CRH : constant Header := Roster (H, 2, 9_000, 12, TTL => 200 * Day);
         --  H7: gen is at most ceiling_t, so a stolen certified root's gen
         --  stops at its cap.
         CRR : constant Header := Roster (R, 12_000, 12_000, 13, TTL => Del_TTL_Max);
         GFM1 : constant Header := Grant (Fnd, M1, 21);
         GRM1 : constant Header := Grant (R, M1, 22);
         GHM2 : constant Header := Grant (H, M2, 23);
         GHM4 : constant Header := Grant (H, M4, 24);
         GRK2 : constant Header := Grant (R, K2, 25);
         GRK3 : constant Header := Grant (R, K3, 26);
         PM1 : constant Header := Put (11, 'n', V (100, M1, 1, 41));
         PM2 : constant Header := Put (12, 'n', V (110, M2, 1, 42));
         PM4 : constant Header := Put (14, 'n', V (120, M4, 1, 43));
         PK2 : constant Header := Put (15, 'n', V (130, K2, 1, 44));
         PK3 : constant Header := Put (16, 'n', V (140, K3, 1, 45));
         XRH : constant Header := Revoke (R, H, 0, 51);     --  R revokes the other root
         XRF : constant Header := Revoke (R, Fnd, 0, 52);   --  ... and the founding key
         XR1 : constant Header := Revoke (R, M1, 0, 53);    --  ... and every member
         XR2 : constant Header := Revoke (R, M2, 0, 54);
         XR4 : constant Header := Revoke (R, M4, 0, 55);
         XFR : constant Header := Revoke (Fnd, R, 5_000, 56);   --  from_t ignored
         XF2 : constant Header := Revoke (Fnd, M2, 0, 57);      --  re-signed

         VP : constant Header_List := [PM1, PM2, PM4, PK2, PK3];
         C  : State := New_State;
      begin
         for X of Header_List'[CRF, CRH, GFM1, GHM2, GHM4, GRM1] loop
            Apply_Auth (C, X, "honest setup");
         end loop;
         for X of Header_List'[PM1, PM2, PM4] loop
            Apply_Data (C, X, "member data", VP);
         end loop;
         Check ("honest: ROSTER_eff is the best roster, del_ttl_eff the max",
                Roster_Eff (C) = (Present => True, Hdr => CRH)
                and Del_TTL_Eff (C) = 200 * Day);
         Check ("honest: no member void",
                not Is_Void (C, PM1) and not Is_Void (C, PM2) and not Is_Void (C, PM4));

         --  R is compromised.
         for X of Header_List'[XRH, XRF, XR1, XR2, XR4, GRK2] loop
            Apply_Auth (C, X, "compromised root's record");
         end loop;
         Apply_Data (C, PK2, "data of R's grantee", VP);
         Apply_Auth (C, CRR, "compromised root's roster at gen = its cap (H7)");
         Check ("before root-void: ROSTER_eff is R's roster, del_ttl_eff R's",
                Roster_Eff (C) = (Present => True, Hdr => CRR)
                and Del_TTL_Eff (C) = Del_TTL_Max);
         Check ("before root-void: every member R revoked is void",
                Is_Void (C, PM1) and Is_Void (C, PM2) and Is_Void (C, PM4)
                and Revoke_Void (C, PM1));
         Check ("before root-void: R's grantee is not void",
                W_Eff (C, Key (K2)) and not Is_Void (C, PK2));
         Check ("a certified root root-voids no one",
                not Root_Void (C, Key (H)) and not Root_Void (C, Key (Fnd))
                and not Root_Void (C, Key (R)));
         Def_Lemmas (C, VP);

         --  The founding key root-voids R.
         declare
            Before : constant State := C;
         begin
            Apply_Auth (C, XFR, "founding REVOKE of R (from_t 5000)");
            for K of Keys loop
               Lemma_Root_Void_Monotone (Before, C, Key (K));
            end loop;
         end;
         Check ("after root-void: R is root_void whatever from_t",
                Root_Void (C, Key (R)) and not Root_Void (C, Key (H)));
         Check ("after root-void: ROSTER_eff is the best honest roster",
                Holds (C, CRR) and Roster_Eff (C) = (Present => True, Hdr => CRH));
         Check ("after root-void: del_ttl_eff ignores R's larger del_ttl",
                Del_TTL_Eff (C) = 200 * Day);
         Check ("after root-void: members R revoked are un-voided",
                not Is_Void (C, PM1) and not Is_Void (C, PM2) and not Is_Void (C, PM4));
         Check ("a member granted by the founding key and by R stays non-void",
                W_Eff (C, Key (M1)) and not Is_Void (C, PM1));
         Check ("after root-void: R's grantee is void through W_eff",
                Is_Void (C, PK2) and not Revoke_Void (C, PK2) and not W_Eff (C, Key (K2))
                and Is_Writer (C, Key (K2)));

         --  Recovery step 3: the founding key re-signs the revocation of M2
         --  by R.
         declare
            Before : constant State := C;
         begin
            Apply_Auth (C, XF2, "founding re-signed REVOKE of M2");
            for P of VP loop
               Lemma_Void_Monotone (Before, C, P);
            end loop;
         end;
         Check ("a revocation the founding key re-signed still voids",
                Is_Void (C, PM2) and Revoke_Void (C, PM2)
                and not Is_Void (C, PM1) and not Is_Void (C, PM4));

         --  R continues to grant. Admission accepts the grants (W only
         --  grows), but the views do not (W_eff).
         declare
            Before : constant State := C;
         begin
            Apply_Auth (C, GRK3, "root-voided root's new GRANT");
            for K of Keys loop
               Lemma_W_Eff_Monotone (Before, C, Key (K));
            end loop;
         end;
         Apply_Data (C, PK3, "data of a key R granted after its root-void", VP);
         Check ("a key R grants after its root-void is admitted and void",
                St = OK and Holds (C, PK3) and Is_Writer (C, Key (K3))
                and Is_Void (C, PK3) and not W_Eff (C, Key (K3)));
         Check ("R's earlier grantee stays void", Is_Void (C, PK2));
         Check ("all held records canonical, A2", All_Canonical (C) and A2 (C));
         Check ("T5: unique pairs in the compromised state", Unique_Checked (C) = 8);
         Lemma_Roster_Eff_Unique (C, Index_In (C, CRH));
         Def_Lemmas (C, VP);

         --  T5: the same records in reverse order give the same views.
         declare
            D : constant State :=
              Run ([GRK3, XF2, XFR, CRR, PK3, PK2, GRK2, XR4, XR2, XR1, XRF, XRH,
                    PM4, PM2, PM1, GRM1, GHM4, GHM2, GFM1, CRH, CRF]);
         begin
            Lemma_Roster_Local (C, D);
            Lemma_Del_TTL_Local (C, D);
            for K of Keys loop
               Lemma_Root_Void_Local (C, D, Key (K));
               Lemma_W_Eff_Local (C, D, Key (K));
            end loop;
            for P of VP loop
               Lemma_Void_Local (C, D, P);
            end loop;
            Check ("T5: compromised-root views agree in reverse order",
                   Same_Auth_Views (C, D, VP) and Kome.Frontier.Count (C) = Kome.Frontier.Count (D));
         end;

         --  Only a root-voided roster: del_ttl_eff is the default and
         --  ROSTER_eff is absent.
         declare
            E : constant State := Run ([CRR, XFR]);
         begin
            Check ("only a root-voided roster: del_ttl_eff default, ROSTER_eff absent",
                   Holds (E, CRR) and Del_TTL_Eff (E) = Del_TTL_Default
                   and Roster_Eff (E) = (Present => False, Hdr => No_Header));
            Def_Lemmas (E, VP);
         end;
      end;

      --  A stale same-signer roster (lower gen, higher ceiling) stays held
      --  under the product order (D3). It never becomes ROSTER_eff.
      declare
         RH2 : constant Header := Roster (6, 3, 9_000, 80);
         RHS : constant Header := Roster (6, 2, 15_000, 81);
         T   : State := New_State;
      begin
         Apply_Auth (T, Roster (Fnd, 1, 1000, 82), "founding roster");
         Apply_Auth (T, RH2, "newer roster of H");
         Apply_Auth (T, RHS, "stale roster of H, higher ceiling");
         Check ("stale same-signer roster held beside the newer one",
                St = OK and Holds (T, RH2) and Holds (T, RHS) and Max_Ceil (T) = 15_000);
         Check ("stale same-signer roster does not become ROSTER_eff",
                Roster_Eff (T) = (Present => True, Hdr => RH2));
         Lemma_Roster_Eff_Unique (T, Index_In (T, RH2));
         Check ("T5: unique roster pairs with an antichain", Unique_Checked (T) = 3);
      end;

      --  (g) Hypothesis boundary. Two canonical rosters with the same V and
      --  different del_ttl violate A2. No roster of the two dominates the
      --  other, so the two are held. The full tie-break still chooses one
      --  header in each order.
      declare
         RA : constant Header := Roster (5, 3, 1000, 50);
         RB : constant Header := (RA with delta Del_TTL => Del_TTL_Max, Epoch => 0);
         Q0 : constant Header := Put (4, 'n', V (10, 1, 1, 90));
         A  : constant State := Run ([RF, GF1, Q0, RA, RB]);
         B  : constant State := Run ([RB, RA, Q0, GF1, RF]);
         T  : State := A;
      begin
         Check ("boundary: equal-V rosters are both held, A2 fails",
                Holds (A, RA) and Holds (A, RB) and Canonical (RA) and Canonical (RB)
                and not A2 (A) and not A2 (B));
         Lemma_Roster_Local (A, B);
         Lemma_Del_TTL_Local (A, B);
         Check ("boundary: ROSTER_eff is the same header in both orders",
                Roster_Eff (A) = (Present => True, Hdr => RB)
                and Roster_Eff (B) = (Present => True, Hdr => RB)
                and Del_TTL_Eff (A) = Del_TTL_Max and Del_TTL_Eff (B) = Del_TTL_Max);
         Apply_Data (T, Q0, "an equal canonical PUT (a duplicate)", [Q0]);
         Check ("boundary: equal-V canonical PUTs are one record",
                St = OK and Unique_Checked (T) = 4);
         Lemma_Cell_Local (A, B, NS, Ent (4), Fld ('n'));
         Check ("boundary: cell is the same header in both orders",
                Cell (A, NS, Ent (4), Fld ('n')) = (Present => True, Hdr => Q0)
                and Cell (B, NS, Ent (4), Fld ('n')) = (Present => True, Hdr => Q0));
      end;

      --  far(p): advisory, with no overflow at the top of U48.
      Check ("far: above now + slack",
             Is_Far (P4, 300, 50) and not Is_Far (P4, 350, 50)
             and not Is_Far (P4, 400, 0) and Is_Far (P4, 399, 0));
      Check ("far: no overflow at the top of the range",
             not Is_Far (P4, U48'Last, U48'Last)
             and not Is_Far ((P4 with delta V => V (U48'Last, 1, 1, 1)), U48'Last, 0)
             and Is_Far ((P4 with delta V => V (U48'Last, 1, 1, 1)), U48'Last - 1, 0));

      if Failed then
         Set_Exit_Status (Failure);
      end if;
   end Run_All;

begin
   null;
end Test_Views;
