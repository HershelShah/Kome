--  Test main for Kome.Headers. It tests the wire codes, the canonical form,
--  domination for each kind, and expiry. Domination follows the DESIGN.md
--  §3 table: the roster product order D3 (ceiling_t, gen strictly; AUDIT.md
--  H1; no epoch and no del_ttl, SIMPLIFY.md S2, S4, S22), grants keyed by
--  (issuer, subject) D1′, and REVOKEs keyed by (issuer, subject) with the
--  least from_t winning (SIMPLIFY.md S5). The test evaluates the ghost
--  lemmas at run time (-gnata) on each pair of a grid.
pragma Ada_2022;
with Ada.Text_IO;      use Ada.Text_IO;
with Ada.Command_Line; use Ada.Command_Line;
with Kome;             use Kome;
with Kome.Headers;     use Kome.Headers;

procedure Test_Headers with SPARK_Mode => Off is

   Failed : Boolean := False;

   procedure Check (Name : String; Cond : Boolean) is
   begin
      Put_Line ((if Cond then "PASS " else "FAIL ") & Name);
      if not Cond then
         Failed := True;
      end if;
   end Check;

   function Key (B : Byte) return Key256 is (others => Word (B));
   function Hsh (B : Natural) return Key256 is (W0 => Word (B), others => 5);
   function Ent (B : Byte) return Id128 is (others => Word (B));

   function Put (E : Byte; T : U48; A : Byte; Seq : U48; H : Natural) return Header is
     (K => K_Put, Ent => Ent (E), FH => Key (1),
      V => (T, Key (A), Seq, Hsh (H)), Issuer => Zero_Key);

   function Del (E : Byte; T : U48; A : Byte; Seq : U48; H : Natural) return Header is
     (K => K_Del, Ent => Ent (E), FH => Zero_Key,
      V => (T, Key (A), Seq, Hsh (H)), Issuer => Zero_Key);

   function Roster (Signer : Byte; Gen, Ceiling : U48; H : Natural) return Header is
     (K => K_Roster, Ent => Zero_Id, FH => Zero_Key,
      V => (Ceiling, Key (Signer), Gen, Hsh (H)), Issuer => Key (Signer));

   --  V = (cap, subject, 0, h). The founding key's cap is 2^48 - 1.
   function Grant (Issuer, Subject : Byte; H : Natural; Cap : U48 := U48'Last) return Header is
     (K => K_Grant, Ent => Zero_Id, FH => Zero_Key,
      V => (Cap, Key (Subject), 0, Hsh (H)), Issuer => Key (Issuer));

   function Revoke (Issuer, Subject : Byte; From_T : U48; H : Natural) return Header is
     (K => K_Revoke, Ent => Zero_Id, FH => Zero_Key,
      V => (From_T, Key (Subject), 0, Hsh (H)), Issuer => Key (Issuer));

   type List is array (Positive range <>) of Header;

   Grid : constant List :=
     [Put (1, 100, 1, 1, 1), Put (1, 200, 1, 2, 2), Put (2, 100, 1, 3, 3),
      Del (1, 150, 2, 1, 4), Del (1, 300, 2, 2, 5), Del (2, 50, 2, 3, 6),
      Roster (9, 1, 5000, 7), Roster (9, 2, 6000, 8), Roster (9, 1, 9000, 9),
      Roster (9, 3, 5500, 10), Roster (9, 4, 9000, 11), Roster (21, 5, 9000, 12),
      Roster (9, 2, 6000, 19),
      Grant (9, 1, 13), Grant (9, 1, 14), Grant (21, 1, 15), Grant (9, 2, 16),
      Revoke (9, 1, 0, 17), Revoke (9, 1, 0, 18), Revoke (9, 1, 50, 25),
      Revoke (9, 1, 50, 26), Revoke (21, 1, 0, 27), Revoke (9, 2, 0, 28),
      Revoke (9, 1, 10, 29)];

   R1 : constant Header := Roster (9, 1, 5000, 7);
   R2 : constant Header := Roster (9, 2, 6000, 8);
   RS : constant Header := Roster (9, 1, 9000, 9);
   R3 : constant Header := Roster (9, 3, 5500, 10);
   R4 : constant Header := Roster (9, 4, 9000, 11);
   --  Equal gen and ceiling as R2, another h (a root restored from backup).
   R2F : constant Header := Roster (9, 2, 6000, 19);
begin
   Check ("Kind'Pos is the wire tag",
          Kind'Pos (K_Roster) = 0 and then Kind'Pos (K_Revoke) = 1
          and then Kind'Pos (K_Grant) = 2 and then Kind'Pos (K_Del) = 3
          and then Kind'Pos (K_Put) = 4);

   Check ("every grid record is canonical",
          (for all X of Grid => Canonical (X)));
   Check ("non-canonical: a PUT with an issuer, a DEL with a field hash",
          not Canonical ((Put (1, 1, 1, 1, 1) with delta Issuer => Key (3)))
          and then not Canonical ((Del (1, 1, 1, 1, 1) with delta FH => Key (3))));
   Check ("non-canonical: a roster whose issuer is not its signer, or with an entity",
          not Canonical ((R1 with delta Issuer => Key (3)))
          and then not Canonical ((R1 with delta Ent => Ent (1))));
   Check ("non-canonical: a roster with gen above ceiling_t (H7), a REVOKE with a field hash",
          not Canonical (Roster (9, 6001, 6000, 8))
          and then Canonical (Roster (9, 6000, 6000, 8))
          and then not Canonical ((Revoke (9, 1, 0, 17) with delta FH => Key (3))));
   Check ("non-canonical: a grant with seq set; a grant carries its cap in t",
          Canonical ((Grant (9, 1, 1) with delta V => (1, Key (1), 0, Hsh (1))))
          and then not Canonical ((Grant (9, 1, 1) with delta V => (0, Key (1), 1, Hsh (1))))
          and then Cap_Of (Grant (9, 1, 1, Cap => 77)) = 77
          and then Cap_Of (Roster (9, 1, 5000, 7)) = 0);

   --  Rosters: the product order (D3).
   Check ("roster: higher gen and higher ceiling dominates", Dominates (R2, R1));
   Check ("roster: a stale roster (lower gen, higher ceiling) and the newer one are incomparable",
          not Dominates (RS, R2) and then not Dominates (R2, RS));
   Check ("roster: higher gen and lower ceiling does not dominate",
          not Dominates (R3, R2) and then not Dominates (R3, RS));
   Check ("roster: higher gen and ceiling >= dominates every other",
          Dominates (R4, R2) and then Dominates (R4, RS) and then Dominates (R4, R3));
   Check ("roster: another signer never dominates",
          not Dominates (Roster (21, 5, 9000, 12), R1));
   --  H1: domination is strict in gen. Two rosters of one signer at equal
   --  gen are incomparable whatever their h and ceiling.
   Check ("roster: equal gen, same signer: neither dominates (H1, strict gen)",
          not Dominates (R2F, R2) and then not Dominates (R2, R2F)
          and then not Dominates (R2F, R1) = False);
   Check ("roster: equal gen is incomparable even with a higher ceiling",
          not Dominates ((R2F with delta V => (9000, Key (9), 2, Hsh (19))), R2));
   Lemma_Equal_Gen_No_Dom (R2, R2F);
   Lemma_Equal_Gen_No_Dom (R2F, R2);
   Lemma_Roster_Dom (R2, R4);
   Lemma_Dominator_Same_Key (R4, R2);

   --  Grants: keyed by (issuer, subject), ordered by h (D1′).
   Check ("grant: same issuer and subject, higher h dominates",
          Dominates (Grant (9, 1, 14), Grant (9, 1, 13))
          and then not Dominates (Grant (9, 1, 13), Grant (9, 1, 14)));
   Check ("grant: another issuer never dominates",
          not Dominates (Grant (21, 1, 15), Grant (9, 1, 13)));
   Check ("grant: another subject never dominates",
          not Dominates (Grant (9, 2, 16), Grant (9, 1, 13)));
   --  A1: the product order (cap, h). A higher h with a lower cap does not
   --  dominate, so wcap never shrinks.
   Check ("grant: higher h and higher cap dominates, higher h and lower cap does not",
          Dominates (Grant (9, 1, 14, Cap => 200), Grant (9, 1, 13, Cap => 100))
          and then not Dominates (Grant (9, 1, 14, Cap => 100), Grant (9, 1, 13, Cap => 200))
          and then not Dominates (Grant (9, 1, 13, Cap => 200), Grant (9, 1, 14, Cap => 100)));
   Lemma_Grant_Dom (Grant (9, 1, 13, Cap => 200), Grant (9, 1, 14, Cap => 100));
   Lemma_Dominator_Same_Key (Grant (9, 1, 14, Cap => 200), Grant (9, 1, 13, Cap => 100));

   --  REVOKEs (S5): keyed by (issuer, subject); a lower from_t wins, an
   --  equal from_t is decided by h.
   Check ("revoke: a lower from_t of the same key dominates",
          Dominates (Revoke (9, 1, 0, 17), Revoke (9, 1, 50, 25))
          and then Dominates (Revoke (9, 1, 10, 29), Revoke (9, 1, 50, 25))
          and then not Dominates (Revoke (9, 1, 50, 25), Revoke (9, 1, 0, 17)));
   Check ("revoke: an equal from_t and a greater h dominates",
          Dominates (Revoke (9, 1, 0, 18), Revoke (9, 1, 0, 17))
          and then not Dominates (Revoke (9, 1, 0, 17), Revoke (9, 1, 0, 18))
          and then Dominates (Revoke (9, 1, 50, 26), Revoke (9, 1, 50, 25)));
   Check ("revoke: another issuer or another subject never dominates",
          not Dominates (Revoke (21, 1, 0, 27), Revoke (9, 1, 50, 25))
          and then not Dominates (Revoke (9, 2, 0, 28), Revoke (9, 1, 50, 25)));
   Check ("revoke: only a REVOKE dominates a REVOKE, and a REVOKE dominates no other kind",
          (for all X of Grid =>
             (if X.K /= K_Revoke then not Dominates (X, Revoke (9, 1, 50, 25))))
          and then (for all X of Grid =>
                      (if X.K /= K_Revoke then not Dominates (Revoke (9, 1, 0, 17), X))));
   Lemma_Dominator_Same_Key (Revoke (9, 1, 0, 17), Revoke (9, 1, 50, 25));
   Check ("data: a newer DEL dominates the entity's PUTs",
          Dominates (Del (1, 150, 2, 1, 4), Put (1, 100, 1, 1, 1))
          and then not Dominates (Del (1, 150, 2, 1, 4), Put (1, 200, 1, 2, 2)));

   Check ("Expired: only DELs at or below the horizon",
          Expired (Del (1, 150, 2, 1, 4), 150) and then not Expired (Del (1, 150, 2, 1, 4), 149)
          and then not Expired (Put (1, 100, 1, 1, 1), 1000)
          and then Expired (Del (1, 0, 2, 1, 4), 0));
   Check ("Ceil_Of: a roster's ceiling_t, else 0",
          Ceil_Of (R4) = 9000 and then Ceil_Of (Grant (9, 1, 13)) = 0
          and then Ceil_Of (Revoke (9, 1, 1234, 17)) = 0);

   --  Each lemma on each pair (and on each triple, for transitivity).
   for X of Grid loop
      Lemma_Dominates_Irrefl (X);
      Lemma_Gen_Lt_Irrefl (X);
      for Y of Grid loop
         Lemma_Gen_Lt_Total (X, Y);
         if X.K = K_Roster and then Y.K = K_Roster then
            Lemma_Roster_Dom (X, Y);
         end if;
         if X.K = K_Grant and then Y.K = K_Grant then
            Lemma_Grant_Dom (X, Y);
         end if;
         if X.K = K_Revoke then
            Lemma_Revoke_Dom (X, Y);
         end if;
         if Y.K = K_Revoke and then Dominates (Y, X) then
            Lemma_Revoke_Dominates_Only_Revokes (Y, X);
         end if;
         if X.K = K_Roster and then Y.K = K_Roster
           and then X.V.Author = Y.V.Author and then X.V.Seq = Y.V.Seq
         then
            Lemma_Equal_Gen_No_Dom (X, Y);
         end if;
         if Dominates (Y, X) then
            Lemma_Dominator_Same_Key (Y, X);
            Lemma_Same_Row (Y, X);
         end if;
         for Z of Grid loop
            if Dominates (Y, X) and then Dominates (Z, Y) then
               Lemma_Dominates_Trans (X, Y, Z);
            end if;
            if Gen_Lt (X, Y) and then Gen_Lt (Y, Z) then
               Lemma_Gen_Lt_Trans (X, Y, Z);
            end if;
         end loop;
      end loop;
   end loop;
   Check ("lemmas hold on the grid", True);

   if Failed then
      Set_Exit_Status (Failure);
   end if;
end Test_Headers;
