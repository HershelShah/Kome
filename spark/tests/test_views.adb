--  Test main for Kome.Views: the views of DESIGN.md §3 and §6 over states
--  built with Kome.Frontier.Apply. Contracts and ghost lemmas run on the
--  test data (-gnata): (a) cell / deleted_at / exists through a PUT, a newer
--  PUT, a DEL and a re-creating PUT; (b) void at, below and above from_t, for
--  another author and another collection; (c) ROSTER_eff across signers and
--  under a root revocation; (d) T5: Lemma_Cell_Unique on every pair of held
--  PUTs, and the same views from two arrival orders; (e) T12: around every
--  REVOKE and ROSTER applied (held, dominated or refused for space),
--  Lemma_Apply_Auth_Local then Lemma_Views_Local; around every PUT and DEL,
--  Lemma_Apply_Data_Local then the authorization-view lemmas; void only
--  grows; (f) ROSTER_eff with every root revoked and with equal generations;
--  (g) the hypothesis boundary: non-canonical PUTs and A2-violating rosters
--  keep the versions of the views order-independent, not their payload.
pragma Ada_2022;
with Ada.Text_IO;      use Ada.Text_IO;
with Ada.Command_Line; use Ada.Command_Line;
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

   NS    : constant Id128 := (others => 7);
   Other : constant Id128 := (others => 8);

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

   --  V = (0, signer, gen, h).
   function Roster (Signer : Byte; Gen, Ceiling : U48; H : Byte) return Header is
     (K => K_Roster, NS => NS, Ent => Ent (0), FH => Hsh (0),
      V => (T => 0, Author => Key (Signer), Seq => Gen, H => Hsh (H)),
      Ceiling => Ceiling);

   --  V = (from_t, subject, rev_seq, h).
   function Revoke (A : Byte; From_T : U48) return Header is
     (K => K_Revoke, NS => NS, Ent => Ent (0), FH => Hsh (0),
      V => (T => From_T, Author => Key (A), Seq => 1, H => Hsh (200 + A)),
      Ceiling => 0);

   None : constant Member_Keys (1 .. 0) := [];
   AB   : constant Member_Keys (1 .. 2) := [Key (1), Key (2)];

   function All_Canonical (S : State) return Boolean is
     (for all I in 1 .. Kome.Frontier.Count (S) => Canonical (Held (S, I)));

   --  A2 on the held set, computed (Unique_Versions is ghost, so a test
   --  verdict cannot use it directly; the assertion ties the two together).
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

   --  The fields and entities the views are compared on.
   type Probe is record
      E : Byte;
      F : Character;
   end record;
   Probes : constant array (1 .. 6) of Probe :=
     [(1, 'n'), (1, 'a'), (1, 'z'), (2, 'n'), (3, 'n'), (0, 'n')];

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

   --  T5: Lemma_Cell_Unique / Lemma_Del_Unique on every pair they apply to.
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
                 and then Versions_Unique (S)
                 and then not Gen_Lt (X, Held (S, J))
                 and then not Gen_Lt (Held (S, J), X)
               then
                  Lemma_Roster_Unique (S, I, J);
                  N := N + 1;
               end if;
            end;
         end loop;
      end loop;
      return N;
   end Unique_Checked;

   S  : State := Empty (NS, 64);
   St : Status;

   --  Records whose void verdict the T12 checks compare.
   Void_Probes : array (1 .. 4) of Header;

   function Same_Auth_Views (A, B : State) return Boolean is
     (Roster_Eff (A, NS) = Roster_Eff (B, NS)
      and then Root_Void (A, NS, Key (8)) = Root_Void (B, NS, Key (8))
      and then Root_Void (A, NS, Key (9)) = Root_Void (B, NS, Key (9))
      and then (for all P of Void_Probes => Is_Void (A, P) = Is_Void (B, P)));

   --  Apply an authorization record and check T12 around it: the lemma
   --  chain runs (and its contracts are evaluated), and the data views on
   --  every probe are unchanged, whatever the Status.
   procedure Apply_Auth
     (T : in out State; R : Header; Members : Member_Keys; Name : String;
      Expect : Status := OK)
   is
      Old : constant State := T;
   begin
      Apply (T, R, Members, St);
      Lemma_Apply_Auth_Local (Old, T, R);
      Lemma_Apply_Keeps_Revokes (Old, T);
      for P of Probes loop
         Lemma_Views_Local (Old, T, NS, Ent (P.E), Fld (P.F));
         Lemma_Exists_Cell (T, NS, Ent (P.E), Fld (P.F));
      end loop;
      Check ("T12: views unchanged by " & Name & " (" & Status'Image (St) & ")",
             St = Expect and then Same_Views (Old, T));
   end Apply_Auth;

   procedure Apply_Auth (R : Header; Members : Member_Keys; Name : String;
                         Expect : Status := OK) is
   begin
      Apply_Auth (S, R, Members, Name, Expect);
   end Apply_Auth;

   --  Apply a data record and check the converse: void, root_void and
   --  ROSTER_eff are unchanged, through Lemma_Apply_Data_Local and the
   --  authorization-view locality lemmas.
   procedure Apply_Data (R : Header; Name : String; Expect : Status := OK) is
      Old : constant State := S;
   begin
      Apply (S, R, None, St);
      Lemma_Apply_Data_Local (Old, S, R);
      Lemma_Roster_Local (Old, S, NS);
      Lemma_Root_Void_Local (Old, S, NS, Key (8));
      Lemma_Root_Void_Local (Old, S, NS, Key (9));
      for P of Void_Probes loop
         Lemma_Void_Local (Old, S, P);
      end loop;
      Check ("T12: authorization views unchanged by " & Name,
             St = Expect and then Same_Auth_Views (Old, S));
   end Apply_Data;

   R1  : constant Header := Roster (9, 1, 5000, 1);
   P1  : constant Header := Put (1, 'n', V (100, 1, 1, 10));
   P2  : constant Header := Put (1, 'n', V (200, 2, 1, 11));   --  beats P1
   P3  : constant Header := Put (1, 'a', V (150, 1, 2, 12));   --  other field
   P5  : constant Header := Put (2, 'n', V (120, 1, 3, 15));   --  other entity
   D1  : constant Header := Del (1, V (300, 2, 2, 13));        --  beats P1..P3
   D0  : constant Header := Del (1, V (50, 1, 4, 16));         --  older DEL
   P4  : constant Header := Put (1, 'n', V (400, 1, 5, 14));   --  re-creates
   X2  : constant Header := Revoke (2, 250);
   P6  : constant Header := Put (3, 'n', V (260, 2, 3, 17));   --  void
   P7  : constant Header := Put (3, 'a', V (250, 2, 4, 18));   --  void, t = from_t
   P8  : constant Header := Put (3, 'b', V (249, 2, 5, 19));   --  not void
   RS8 : constant Header := Roster (8, 3, 6000, 3);           --  second root
   R2  : constant Header := Roster (9, 2, 7000, 2);           --  beats R1
   X8  : constant Header := Revoke (8, 0);                    --  root revoked

begin
   Void_Probes := [P6, P7, P8, P2];
   Check ("empty state: no cell, no DEL, nothing exists, no roster",
          not Cell (S, NS, Ent (1), Fld ('n')).Present
          and Cell (S, NS, Ent (1), Fld ('n')).Hdr = No_Header
          and not Deleted_At (S, NS, Ent (1)).Present
          and not Exists (S, NS, Ent (1))
          and not Roster_Eff (S, NS).Present
          and not Is_Void (S, P1));

   Apply_Auth (R1, AB, "first roster");
   Check ("roster held", St = OK and Holds (S, R1));
   Check ("ROSTER_eff is the only roster",
          Roster_Eff (S, NS) = (Present => True, Hdr => R1));
   Check ("ROSTER_eff of another collection is absent",
          not Roster_Eff (S, Other).Present);

   --  (a) cell, exists, deleted_at.
   Apply_Data (P1, "P1");
   Apply_Data (P3, "P3");
   Apply_Data (P5, "P5");
   Check ("cell is the held PUT",
          Cell (S, NS, Ent (1), Fld ('n')) = (Present => True, Hdr => P1)
          and Cell (S, NS, Ent (1), Fld ('a')) = (Present => True, Hdr => P3)
          and Cell (S, NS, Ent (2), Fld ('n')) = (Present => True, Hdr => P5));
   Check ("absent field has no cell",
          Cell (S, NS, Ent (1), Fld ('z')) = (Present => False, Hdr => No_Header));
   Check ("another collection has no cell",
          not Cell (S, Other, Ent (1), Fld ('n')).Present
          and not Exists (S, Other, Ent (1)));
   Check ("entity with a live PUT exists",
          Exists (S, NS, Ent (1)) and Exists (S, NS, Ent (2))
          and not Exists (S, NS, Ent (3)));
   Apply_Data (P2, "P2");
   Check ("newer PUT is the cell",
          St = OK and Cell (S, NS, Ent (1), Fld ('n')) = (Present => True, Hdr => P2));
   Check ("no DEL yet", Deleted_At (S, NS, Ent (1)) = (Present => False, V => No_Version));
   Check ("T5: unique on every PUT/roster pair", Unique_Checked (S) = 4);

   Apply_Data (D0, "D0");
   Check ("older DEL held beside newer PUTs",
          St = OK and Deleted_At (S, NS, Ent (1)) = (Present => True, V => D0.V)
          and Exists (S, NS, Ent (1)));
   Apply_Data (D1, "D1");
   Check ("deleted_at is the newest DEL",
          St = OK and Deleted_At (S, NS, Ent (1)) = (Present => True, V => D1.V));
   Check ("DEL removes every cell of the entity",
          not Cell (S, NS, Ent (1), Fld ('n')).Present
          and not Cell (S, NS, Ent (1), Fld ('a')).Present
          and not Exists (S, NS, Ent (1)));
   Check ("other entity untouched",
          Cell (S, NS, Ent (2), Fld ('n')) = (Present => True, Hdr => P5)
          and not Deleted_At (S, NS, Ent (2)).Present);
   Apply_Data (P4, "P4");
   Check ("later PUT re-creates the entity",
          Exists (S, NS, Ent (1))
          and Cell (S, NS, Ent (1), Fld ('n')) = (Present => True, Hdr => P4)
          and not Cell (S, NS, Ent (1), Fld ('a')).Present
          and Deleted_At (S, NS, Ent (1)) = (Present => True, V => D1.V));

   --  (b) void.
   Check ("nothing void before any REVOKE",
          not Is_Void (S, P2) and not Is_Void (S, P6) and not Is_Void (S, P4));
   Apply_Auth (X2, None, "REVOKE of a writer");
   Check ("REVOKE held", St = OK and Holds (S, X2));
   Check ("void at t > from_t", Is_Void (S, P6));
   Check ("void at t = from_t", Is_Void (S, P7));
   Check ("not void at t < from_t", not Is_Void (S, P8) and not Is_Void (S, P2));
   Check ("not void for another author", not Is_Void (S, P4));
   Check ("not void in another collection",
          not Is_Void (S, (P6 with delta NS => Other)));
   Apply_Data (P6, "P6");
   Apply_Data (P7, "P7");
   Apply_Data (P8, "P8");
   Check ("void records stay held and visible as cells",
          Cell (S, NS, Ent (3), Fld ('n')) = (Present => True, Hdr => P6)
          and Is_Void (S, Cell (S, NS, Ent (3), Fld ('n')).Hdr)
          and Exists (S, NS, Ent (3)));

   --  (c) ROSTER_eff and root revocation.
   Apply_Auth (RS8, AB, "roster of a second root");
   Check ("ROSTER_eff is the greater generation across signers",
          Roster_Eff (S, NS) = (Present => True, Hdr => RS8)
          and Holds (S, R1));
   Apply_Auth (R2, AB, "newer roster of the first root");
   Check ("per-signer domination: R2 replaces R1, RS8 still effective",
          Holds (S, R2) and not Holds (S, R1)
          and Roster_Eff (S, NS) = (Present => True, Hdr => RS8));
   Check ("root not void before its REVOKE", not Root_Void (S, NS, Key (8)));
   declare
      Before : constant State := S;
      type List is array (Positive range <>) of Header;
      Ps : constant List := [P6, P7, P8, P2, P4];
   begin
      Apply_Auth (X8, None, "REVOKE of a root");
      Check ("root void after its REVOKE",
             Root_Void (S, NS, Key (8)) and not Root_Void (S, NS, Key (9)));
      Check ("ROSTER_eff skips the revoked root's roster",
             Holds (S, RS8) and Roster_Eff (S, NS) = (Present => True, Hdr => R2));
      for P of Ps loop
         if Is_Void (Before, P) then
            Lemma_Void_Monotone (Before, S, P);
         end if;
      end loop;
      Check ("void only grows", Is_Void (S, P6) and Is_Void (S, P7) and not Is_Void (S, P8));
   end;
   Apply_Auth (R1, AB, "dominated roster", Expect => Dominated);
   Check ("dominated roster not held, ROSTER_eff unchanged",
          not Holds (S, R1) and Roster_Eff (S, NS) = (Present => True, Hdr => R2));
   Check ("all held records canonical and A2 holds", All_Canonical (S) and A2 (S));
   Check ("T5: unique on every PUT/DEL/roster pair (late)", Unique_Checked (S) = 8);
   declare
      I : Natural := 0;
   begin
      for K in 1 .. Kome.Frontier.Count (S) loop
         if Held (S, K) = R2 then
            I := K;
         end if;
      end loop;
      Lemma_Roster_Eff_Unique (S, NS, I);
      Check ("T5: the maximal eligible roster is ROSTER_eff", I /= 0);
   end;

   --  (f) every root revoked: ROSTER_eff is None.
   declare
      T : State := S;
   begin
      Apply_Auth (T, Revoke (9, 1_000_000), None, "REVOKE of the last root");
      Check ("every root revoked (even with a far from_t): ROSTER_eff absent",
             Holds (T, R2) and Holds (T, RS8)
             and Root_Void (T, NS, Key (9))
             and Roster_Eff (T, NS) = (Present => False, Hdr => No_Header));
   end;

   --  No_Space: a full state refuses a REVOKE and every view is unchanged.
   declare
      T : State := Empty (NS, 2);
   begin
      Apply_Auth (T, R1, AB, "roster into a small state");
      Apply (T, P1, None, St);
      Check ("small state full", St = OK and Kome.Frontier.Count (T) = 2);
      Apply_Auth (T, X2, None, "REVOKE into a full state", Expect => No_Space);
      Apply_Auth (T, RS8, AB, "roster into a full state", Expect => No_Space);
      Apply_Auth (T, R2, AB, "dominating roster into a full state");
      Check ("a roster that frees its predecessor fits",
             Holds (T, R2) and not Holds (T, R1) and Holds (T, P1));
   end;

   --  Equal generations across two signers are decided by h, in any order.
   declare
      RA : constant Header := Roster (5, 7, 100, 40);
      RB : constant Header := Roster (6, 7, 200, 30);
      A  : State := Empty (NS, 8);
      B  : State := Empty (NS, 8);
   begin
      Apply (A, RA, AB, St);
      Apply (A, RB, AB, St);
      Apply (B, RB, AB, St);
      Apply (B, RA, AB, St);
      Check ("equal gen, two signers: both held, greater h is ROSTER_eff",
             Holds (A, RA) and Holds (A, RB)
             and Roster_Eff (A, NS) = (Present => True, Hdr => RA)
             and Roster_Eff (B, NS) = (Present => True, Hdr => RA));
      Lemma_Roster_Local (A, B, NS);
      Check ("T5: Lemma_Roster_Local on equal generations", A2 (A));
   end;

   --  (d) T5 across arrival orders: two states built from the same records
   --  in different orders hold the same data, and every view agrees.
   declare
      type List is array (Positive range <>) of Header;
      procedure Build (T : in out State; L : List) is
         Dummy : Status;
      begin
         for R of L loop
            if R.K = K_Roster then
               Apply (T, R, AB, Dummy);
            else
               Apply (T, R, None, Dummy);
            end if;
         end loop;
      end Build;
      A : State := Empty (NS, 64);
      B : State := Empty (NS, 64);
   begin
      Build (A, [R1, P1, P3, P5, P2, D0, D1, P4, X2, P6, P7, P8, RS8, R2, X8]);
      Build (B, [R2, RS8, X8, X2, P8, P7, P6, P4, D1, D0, P2, P5, P3, P1, R1]);
      Check ("T5: same views from two arrival orders", Same_Views (A, B));
      for P of Probes loop
         Lemma_Views_Local (A, B, NS, Ent (P.E), Fld (P.F));
      end loop;
      Check ("T5: Lemma_Views_Local holds on the two orders", True);
      Lemma_Roster_Local (A, B, NS);
      Lemma_Void_Local (A, B, P6);
      Lemma_Void_Local (A, B, P8);
      Check ("T5: same ROSTER_eff and void from two orders",
             A2 (A)
             and Roster_Eff (A, NS) = Roster_Eff (B, NS)
             and Roster_Eff (A, NS) = (Present => True, Hdr => R2)
             and Is_Void (A, P6) = Is_Void (B, P6)
             and Is_Void (A, P8) = Is_Void (B, P8));
   end;

   --  (g) Hypothesis boundary. Records that differ only outside V violate
   --  A2; both are held (neither dominates the other). The views' presence
   --  and version are still order-independent (the unconditional part of
   --  Lemma_Cell_Local / Lemma_Roster_Local), which is all the lemmas claim.
   declare
      type List is array (Positive range <>) of Header;
      procedure Build (T : in out State; L : List) is
      begin
         for R of L loop
            Apply (T, R, (if R.K = K_Roster then AB else None), St);
         end loop;
      end Build;
      Q0 : constant Header := Put (4, 'n', V (10, 1, 1, 90));
      Q1 : constant Header := (Q0 with delta Ceiling => 77);   --  not canonical
      RA : constant Header := Roster (5, 3, 1000, 50);
      RB : constant Header := (RA with delta Ceiling => 2000);  --  canonical, same V
      A  : State := Empty (NS, 8);
      B  : State := Empty (NS, 8);
   begin
      Build (A, [R1, Q0, Q1, RA, RB]);
      Build (B, [R1, Q1, Q0, RB, RA]);
      Check ("boundary: equal-V records are all held",
             Holds (A, Q0) and Holds (A, Q1) and Holds (A, RA) and Holds (A, RB)
             and not Canonical (Q1) and Canonical (RA) and Canonical (RB));
      Check ("boundary: A2 fails, PUTs not all canonical",
             not A2 (A) and not A2 (B) and not All_Canonical (A));
      Lemma_Cell_Local (A, B, NS, Ent (4), Fld ('n'));
      Lemma_Data_Local (A, B, NS, Ent (4));
      Lemma_Roster_Local (A, B, NS);
      Check ("boundary: cell present with the same version in both orders",
             Cell (A, NS, Ent (4), Fld ('n')).Present
             and Cell (B, NS, Ent (4), Fld ('n')).Present
             and Cell (A, NS, Ent (4), Fld ('n')).Hdr.V = Q0.V
             and Cell (B, NS, Ent (4), Fld ('n')).Hdr.V = Q0.V);
      Check ("boundary: ROSTER_eff has the same version in both orders",
             Roster_Eff (A, NS).Present
             and Roster_Eff (A, NS).Hdr.V = RA.V
             and Roster_Eff (B, NS).Hdr.V = RA.V);
      Check ("boundary: Lemma_Cell_Unique gives equal versions on the pair",
             Unique_Checked (A) = 4);
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
end Test_Views;
