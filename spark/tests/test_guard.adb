--  Test main for Kome.Guard: the REVOKE-aware session gate (AUDIT.md A3)
--  and the quarantine view (AUDIT.md H2, SIMPLIFY.md S10).
--  Contracts and ghost lemmas run on the test data (-gnata).
--  (a) Member_Of on a roster with two members;
--  (b) the gate admits a listed member, refuses an unlisted key, and
--      refuses a listed member as soon as a counting REVOKE of its
--      sign_pk is held, whatever the from_t, and before any roster
--      removes it; a root-voided issuer's REVOKE stops closing the gate;
--  (c) the quarantine: set when a founding REVOKE root-voids the signer
--      of the maximal roster, cleared by the recovery roster at a higher
--      gen; Admits = Gate and not Quarantined.
pragma Ada_2022;
with Ada.Text_IO;      use Ada.Text_IO;
with Ada.Command_Line; use Ada.Command_Line;
with Ada.Exceptions;   use Ada.Exceptions;
with Kome;             use Kome;
with Kome.Keys;        use Kome.Keys;
with Kome.Headers;     use Kome.Headers;
with Kome.Crypto;
with Kome.Records;     use Kome.Records;
with Kome.Frontier;    use Kome.Frontier;
with Kome.Views;       use Kome.Views;
with Kome.Guard;       use Kome.Guard;

procedure Test_Guard with SPARK_Mode => Off is

   Failed : Boolean := False;

   procedure Check (Name : String; Cond : Boolean) is
   begin
      if Cond then
         Put_Line ("PASS " & Name);
      else
         Put_Line ("FAIL " & Name);
         Failed := True;
      end if;
   end Check;

   function Fill (Len : Natural; Seed : Natural) return Byte_Array is
     ([for I in 0 .. Len - 1 => Byte ((Seed + 7 * I) mod 256)]);

   function Good_DH (Seed : Natural) return Pubkey is
      K : Pubkey := Pubkey (Fill (Pubkey_Len, Seed));
   begin
      K (31) := K (31) and 16#3F#;
      return K;
   end Good_DH;

   --  N members { sign_pk dh_pk nonce box }. Each dh_pk is a good key.
   function Members_Of (N : Natural; Seed : Natural) return Byte_Array is
      B : Byte_Array := Fill (N * Member_Len, Seed);
   begin
      for I in 0 .. N - 1 loop
         B (I * Member_Len + Pubkey_Len + 31) := B (I * Member_Len + Pubkey_Len + 31) and 16#3F#;
      end loop;
      return B;
   end Members_Of;

   function Hsh (B : Natural) return Key256 is (W0 => Word (B), others => 5);
   function Key (B : Natural) return Key256 is (others => Word (B));

   Root_SK : Kome.Crypto.Secret_Key;
   Root_PK : Pubkey;
   Salt_A  : constant Salt := Salt (Fill (Salt_Len, 90));
   Box_A   : constant Pubkey := Good_DH (15);
   Day     : constant U48 := 86_400_000;
   TTL     : constant U48 := 30 * Day;

   procedure Run_All;

   --  A State holds Signers_Max * Slice_Max authorization rows. Under
   --  -gnata, each Post evaluation copies states, so the checks run in a
   --  task with a large stack (as in test_views).
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
   Kome.Crypto.Key_Pair (Kome.Crypto.Seed (Fill (Kome.Crypto.Seed_Len, 3)), Root_SK, Root_PK);
   declare
      Fnd  : constant Key256 := To_Key256 (Root_PK);
      Mem  : constant Byte_Array := Members_Of (2, 33);
      DH1  : constant Pubkey := Pubkey (Mem (Pubkey_Len .. 2 * Pubkey_Len - 1));
      DH2  : constant Pubkey :=
        Pubkey (Mem (Member_Len + Pubkey_Len .. Member_Len + 2 * Pubkey_Len - 1));
      DHX  : constant Pubkey := Good_DH (200);
      --  The founding roster at gen 1.
      R    : constant Roster_Record :=
        Make_Roster (Root_PK, Salt_A, Root_PK, 0, Zero_Sig, Box_A, 1, 5000, TTL, 2,
                     Fill (Link_Len, 5), Mem);
      RH   : constant Header := To_Header (R);
      S1   : constant Key256 := Member_Key (R.C, 1);
      S2   : constant Key256 := Member_Key (R.C, 2);
      --  The founding key's recovery roster at gen 3, with the same members.
      RFR  : constant Roster_Record :=
        Make_Roster (Root_PK, Salt_A, Root_PK, 0, Zero_Sig, Box_A, 3, 7000, TTL, 2,
                     Fill (Link_Len, 5), Mem);
      RF   : constant Header := To_Header (RFR);
      --  A certified root 8, its roster at gen 2, and the founding REVOKE
      --  that root-voids it.
      R8   : constant Header :=
        (K => K_Roster, Ent => Zero_Id, FH => Zero_Key,
         V => (T => 6000, Author => Key (8), Seq => 2, H => Hsh (80)),
         Issuer => Key (8));
      X8   : constant Header :=
        (K => K_Revoke, Ent => Zero_Id, FH => Zero_Key,
         V => (T => 0, Author => Key (8), Seq => 0, H => Hsh (81)),
         Issuer => Fnd);
      --  REVOKEs of member 1: by the founding key with a future from_t,
      --  and by root 8 from 0.
      XF1  : constant Header :=
        (K => K_Revoke, Ent => Zero_Id, FH => Zero_Key,
         V => (T => 1_000_000, Author => S1, Seq => 0, H => Hsh (83)),
         Issuer => Fnd);
      X81  : constant Header :=
        (K => K_Revoke, Ent => Zero_Id, FH => Zero_Key,
         V => (T => 0, Author => S1, Seq => 0, H => Hsh (84)),
         Issuer => Key (8));
      S    : State := Empty (Fnd, 16);
      St   : Status;

      function Index_In (T : State; X : Header) return Natural is
      begin
         for I in 1 .. Kome.Frontier.Count (T) loop
            if Held (T, I) = X then
               return I;
            end if;
         end loop;
         return 0;
      end Index_In;
   begin
      --  (a) Member_Of.
      Check ("Member_Of finds each member's dh_pk and nothing else",
             Member_Of (R.C, DH1) = 1 and then Member_Of (R.C, DH2) = 2
             and then Member_Of (R.C, DHX) = 0 and then S1 /= S2);

      --  (b) The gate.
      Apply (S, RH, 1, St);
      Check ("founding roster applied and effective",
             St = OK and then Roster_Eff (S) = (Present => True, Hdr => RH));
      Check ("gate admits each listed member, refuses an unlisted key",
             Gate (S, R, DH1) and then Gate (S, R, DH2) and then not Gate (S, R, DHX)
             and then Admits (S, R, DH1));
      --  G8: the founding roster is not void (its signer is in no W_eff,
      --  and that is irrelevant off data). S12: one roster is not contested.
      Check ("the effective roster is not void (G8) and not contested (S12)",
             not Is_Void (S, RH) and then not Revoke_Void (S, RH) and then not Contested (S));
      Lemma_Is_Void_Def (S, RH);
      Lemma_Contested_Def (S);
      Apply (S, X81, 2, St);
      Check ("a certified root's REVOKE of member 1 (from 0) closes the gate for its dh_pk",
             St = OK and then Revoked (S, S1) and then not Gate (S, R, DH1)
             and then Gate (S, R, DH2) and then not Admits (S, R, DH1));
      Lemma_Gate_Refuses_Revoked (S, R, DH1);
      declare
         T : State := S;
      begin
         --  Root-voiding root 8 makes its REVOKE stop counting.
         Apply (T, X8, 3, St);
         Check ("after the root-void of its issuer, the REVOKE stops closing the gate",
                St = OK and then Root_Void (T, Key (8)) and then not Revoked (T, S1)
                and then Gate (T, R, DH1));
         Apply (T, XF1, 4, St);
         Check ("a founding REVOKE with a future from_t closes the gate at once (A3)",
                St = OK and then Revoked (T, S1) and then not Gate (T, R, DH1)
                and then Gate (T, R, DH2));
         Lemma_Gate_Refuses_Revoked (T, R, DH1);
      end;

      --  (c) The quarantine. Root 8's roster at gen 2 is ROSTER_eff.
      declare
         Before : State := S;
         After  : State := S;
      begin
         Apply (Before, R8, 5, St);
         Check ("the certified root's roster at the higher gen is ROSTER_eff, no quarantine",
                St = OK and then Roster_Eff (Before) = (Present => True, Hdr => R8)
                and then not Quarantined (Before));
         --  S12: a rival at the same gen by another root (7) makes the
         --  membership contested; the founding roster at gen 1 does not.
         declare
            R7 : constant Header :=
              (R8 with delta V => (T => 6000, Author => Key (7), Seq => 2, H => Hsh (85)),
                             Issuer => Key (7));
            W  : State := Before;
         begin
            Check ("the founding roster at a lower gen is no rival", not Contested (Before));
            Apply (W, R7, 6, St);
            Check ("a second root's roster at the gen of ROSTER_eff: contested (S12)",
                   St = OK and then Contested (W)
                   and then Roster_Eff (W) = (Present => True, Hdr => R7));
            Lemma_Contested_Def (W);
         end;
         --  A founding REVOKE root-voids root 8: ROSTER_eff falls back to
         --  the founding roster at gen 1, which lists member 1 again.
         After := Before;
         Apply (After, X8, 7, St);
         Check ("the root-void makes ROSTER_eff fall back to the older founding roster",
                St = OK and then Roster_Eff (After) = (Present => True, Hdr => RH));
         Check ("the root-void of the maximal roster's signer quarantines (S10, H2)",
                Quarantined (After) and then Roster_Max (After) = (Present => True, Hdr => R8));
         Lemma_Quarantine_Set (After, Index_In (After, R8));
         Check ("while quarantined, Admits refuses a member the gate would admit",
                Gate (After, R, DH2) and then not Admits (After, R, DH2));
         Lemma_Quarantine_Refuses (After, R, DH2);
         declare
            Rec : State := After;
         begin
            Apply (Rec, RF, 8, St);
            Check ("the recovery roster at a higher gen is ROSTER_eff and the maximum",
                   St = OK and then Roster_Eff (Rec) = (Present => True, Hdr => RF)
                   and then Roster_Max (Rec) = (Present => True, Hdr => RF)
                   and then Holds (Rec, R8) and then not Holds (Rec, RH));
            Lemma_Quarantine_Cleared (Rec, Index_In (Rec, RF));
            Check ("the recovery roster clears the quarantine; Admits = Gate",
                   not Quarantined (Rec) and then Admits (Rec, RFR, DH2)
                   and then Admits (Rec, RFR, DH2) = Gate (Rec, RFR, DH2));
         end;
      end;
   end;
      if Failed then
         Set_Exit_Status (Failure);
      end if;
   end Run_All;

begin
   null;
end Test_Guard;
