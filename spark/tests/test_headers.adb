--  Test main for Kome.Headers. It tests the wire codes, the canonical form,
--  domination for each kind, and expiry. Domination follows the DESIGN.md
--  §3 table: the roster product order D3 (ceiling_t, epoch, gen strictly,
--  del_ttl; AUDIT.md H1, H15), grants keyed by (issuer, subject) D1′, and
--  REVOKE never dominated. The test evaluates the ghost lemmas at run time
--  (-gnata) on each pair of a grid.
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

   NS : constant Id128 := (others => 7);

   function Key (B : Byte) return Key256 is (others => Word (B));
   function Hsh (B : Natural) return Key256 is (W0 => Word (B), others => 5);
   function Ent (B : Byte) return Id128 is (others => Word (B));

   function Put (E : Byte; T : U48; A : Byte; Seq : U48; H : Natural) return Header is
     (K => K_Put, NS => NS, Ent => Ent (E), FH => Key (1),
      V => (T, Key (A), Seq, Hsh (H)), Issuer => Zero_Key, Del_TTL => 0, Epoch => 0);

   function Del (E : Byte; T : U48; A : Byte; Seq : U48; H : Natural) return Header is
     (K => K_Del, NS => NS, Ent => Ent (E), FH => Zero_Key,
      V => (T, Key (A), Seq, Hsh (H)), Issuer => Zero_Key, Del_TTL => 0, Epoch => 0);

   function Roster (Signer : Byte; Gen, Ceiling : U48; H : Natural;
                    E : Kome.Epoch := 0; TTL : U48 := Del_TTL_Min) return Header is
     (K => K_Roster, NS => NS, Ent => Zero_Id, FH => Zero_Key,
      V => (Ceiling, Key (Signer), Gen, Hsh (H)), Issuer => Key (Signer),
      Del_TTL => TTL, Epoch => E);

   --  V = (cap, subject, 0, h). The founding key's cap is 2^48 - 1.
   function Grant (Issuer, Subject : Byte; H : Natural; Cap : U48 := U48'Last) return Header is
     (K => K_Grant, NS => NS, Ent => Zero_Id, FH => Zero_Key,
      V => (Cap, Key (Subject), 0, Hsh (H)), Issuer => Key (Issuer), Del_TTL => 0, Epoch => 0);

   function Revoke (Issuer, Subject : Byte; From_T : U48; H : Natural) return Header is
     (K => K_Revoke, NS => NS, Ent => Zero_Id, FH => Zero_Key,
      V => (From_T, Key (Subject), 1, Hsh (H)), Issuer => Key (Issuer), Del_TTL => 0, Epoch => 0);

   type List is array (Positive range <>) of Header;

   Grid : constant List :=
     [Put (1, 100, 1, 1, 1), Put (1, 200, 1, 2, 2), Put (2, 100, 1, 3, 3),
      Del (1, 150, 2, 1, 4), Del (1, 300, 2, 2, 5), Del (2, 50, 2, 3, 6),
      Roster (9, 1, 5000, 7), Roster (9, 2, 6000, 8), Roster (9, 1, 9000, 9),
      Roster (9, 3, 5500, 10), Roster (9, 4, 9000, 11), Roster (21, 5, 9000, 12),
      Roster (9, 2, 6000, 19), Roster (9, 4, 9000, 20, E => 3),
      Roster (9, 5, 9000, 21, E => 2),
      Roster (9, 2, 6000, 23, TTL => Del_TTL_Max), Roster (9, 3, 9000, 24, TTL => Del_TTL_Max),
      Grant (9, 1, 13), Grant (9, 1, 14), Grant (21, 1, 15), Grant (9, 2, 16),
      Revoke (9, 1, 0, 17), Revoke (9, 1, 0, 18)];

   R1 : constant Header := Roster (9, 1, 5000, 7);
   R2 : constant Header := Roster (9, 2, 6000, 8);
   RS : constant Header := Roster (9, 1, 9000, 9);
   R3 : constant Header := Roster (9, 3, 5500, 10);
   R4 : constant Header := Roster (9, 4, 9000, 11);
   --  Equal gen and ceiling as R2, another h (a root restored from backup).
   R2F : constant Header := Roster (9, 2, 6000, 19);
   --  R4 at epoch 3, and gen 5 at the lower epoch 2.
   R4E : constant Header := Roster (9, 4, 9000, 20, E => 3);
   R5E : constant Header := Roster (9, 5, 9000, 21, E => 2);
   --  R2 with the longest del_ttl (the only long value, AUDIT.md H15), and
   --  a gen-3 refresh that keeps it.
   R2L : constant Header := Roster (9, 2, 6000, 23, TTL => Del_TTL_Max);
   R3L : constant Header := Roster (9, 3, 9000, 24, TTL => Del_TTL_Max);
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
   Check ("non-canonical: a roster whose issuer is not its signer, or del_ttl out of range",
          not Canonical ((R1 with delta Issuer => Key (3)))
          and then not Canonical ((R1 with delta Del_TTL => 0))
          and then not Canonical ((R1 with delta Del_TTL => Del_TTL_Max + 1)));
   Check ("non-canonical: a roster with gen above ceiling_t (H7), or a PUT, DEL, GRANT with an epoch",
          not Canonical (Roster (9, 6001, 6000, 8))
          and then Canonical (Roster (9, 6000, 6000, 8))
          and then not Canonical ((Put (1, 1, 1, 1, 1) with delta Epoch => 1))
          and then not Canonical ((Del (1, 1, 1, 1, 1) with delta Epoch => 1))
          and then not Canonical ((Grant (9, 1, 1) with delta Epoch => 1))
          and then not Canonical ((Revoke (9, 1, 0, 17) with delta Epoch => 1)));
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
   --  A2: a dominator is not lower in epoch.
   Check ("roster: higher gen at a higher epoch dominates", Dominates (R4E, R2));
   Check ("roster: higher gen at a lower epoch does not dominate",
          not Dominates (R5E, R4E) and then Dominates (R5E, R2));
   Lemma_Equal_Gen_No_Dom (R2, R2F);
   Lemma_Equal_Gen_No_Dom (R2F, R2);
   --  H15: a dominator is not lower in del_ttl. A thief's roster (gen + 1,
   --  ceiling >=, a short del_ttl) does not dominate the long-ttl roster,
   --  and neither dominates the other.
   Check ("roster: higher gen and ceiling but lower del_ttl does not dominate (H15)",
          not Dominates (R4, R2L) and then not Dominates (R2L, R4)
          and then not Dominates (R3, R2L));
   Check ("roster: higher gen and equal del_ttl dominates",
          Dominates (R4, R2) and then Dominates (R3L, R2L)
          and then Dominates ((R4 with delta Del_TTL => Del_TTL_Max), R2L));
   Check ("roster: higher gen and higher del_ttl dominates",
          Dominates (R3L, R2) and then Dominates (R3L, R1) and then Dominates (R3L, RS));
   Check ("roster: equal gen is incomparable whatever del_ttl",
          not Dominates (R2L, R2) and then not Dominates (R2, R2L));
   Lemma_Roster_Dom (R2L, R4);
   Lemma_Roster_Dom (R2L, R3L);
   Lemma_Dominator_Keeps_Registers (R3L, R2);

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
   Lemma_Dominator_Keeps_Registers (Grant (9, 1, 14, Cap => 200), Grant (9, 1, 13, Cap => 100));

   Check ("revoke: never dominated",
          (for all X of Grid => not Dominates (X, Revoke (9, 1, 0, 17))));
   Check ("data: a newer DEL dominates the entity's PUTs",
          Dominates (Del (1, 150, 2, 1, 4), Put (1, 100, 1, 1, 1))
          and then not Dominates (Del (1, 150, 2, 1, 4), Put (1, 200, 1, 2, 2)));

   Check ("Expired: only DELs at or below the horizon",
          Expired (Del (1, 150, 2, 1, 4), 150) and then not Expired (Del (1, 150, 2, 1, 4), 149)
          and then not Expired (Put (1, 100, 1, 1, 1), 1000)
          and then not Expired (Del (1, 0, 2, 1, 4), No_Horizon));
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
            Lemma_Revoke_Never_Dominated (Y, X);
         end if;
         if Dominates (Y, X) then
            Lemma_Dominator_Keeps_Registers (Y, X);
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
