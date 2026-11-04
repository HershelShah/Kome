--  Test main for Kome.Guard: the REVOKE-aware session gate (AUDIT.md A3)
--  and the quarantine flag after a pre-gate root-void (AUDIT.md H2).
--  Contracts and ghost lemmas run on the test data (-gnata).
--  (a) Member_Of on a roster with two members;
--  (b) the gate admits a listed member, refuses an unlisted key, and
--      refuses a listed member as soon as a counting REVOKE of its
--      sign_pk is held, whatever the from_t, and before any roster
--      removes it; a root-voided issuer's REVOKE stops closing the gate;
--  (c) the quarantine flag: set when a pre-gate OPEN root-voids the
--      signer of ROSTER_eff, kept by anything else, cleared only by a
--      founding roster that is ROSTER_eff; Admits reads it.
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

   --  A State has a Register_File of Writers_Max keys (256 KiB). Under
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
      NS   : constant Id128  := To_Id128 (Collection_Id (Root_PK, Salt_A));
      Fnd  : constant Key256 := To_Key256 (Root_PK);
      Mem  : constant Byte_Array := Members_Of (2, 33);
      DH1  : constant Pubkey := Pubkey (Mem (Pubkey_Len .. 2 * Pubkey_Len - 1));
      DH2  : constant Pubkey :=
        Pubkey (Mem (Member_Len + Pubkey_Len .. Member_Len + 2 * Pubkey_Len - 1));
      DHX  : constant Pubkey := Good_DH (200);
      --  The founding roster at epoch 2, gen 1.
      R    : constant Roster_Record :=
        Make_Roster (Root_PK, Salt_A, Root_PK, 0, Zero_Sig, Box_A, 1, 5000, TTL, 2,
                     Fill (Link_Len, 5), Mem);
      RH   : constant Header := To_Header (R);
      S1   : constant Key256 := Member_Key (R.C, 1);
      S2   : constant Key256 := Member_Key (R.C, 2);
      --  A certified root 8, its roster at epoch 3 (ROSTER_eff), and the
      --  founding REVOKE that root-voids it.
      R8   : constant Header :=
        (K => K_Roster, NS => NS, Ent => Zero_Id, FH => Zero_Key,
         V => (T => 6000, Author => Key (8), Seq => 2, H => Hsh (80)),
         Issuer => Key (8), Del_TTL => TTL, Epoch => 3);
      X8   : constant Header :=
        (K => K_Revoke, NS => NS, Ent => Zero_Id, FH => Zero_Key,
         V => (T => 0, Author => Key (8), Seq => 1, H => Hsh (81)),
         Issuer => Fnd, Del_TTL => 0, Epoch => 0);
      --  The recovery roster: founding-signed, at the next segment.
      RF   : constant Header :=
        (K => K_Roster, NS => NS, Ent => Zero_Id, FH => Zero_Key,
         V => (T => 7000, Author => Fnd, Seq => 2, H => Hsh (82)),
         Issuer => Fnd, Del_TTL => TTL, Epoch => 4096);
      --  REVOKEs of member 1: by the founding key with a future from_t,
      --  and by root 8 from 0.
      XF1  : constant Header :=
        (K => K_Revoke, NS => NS, Ent => Zero_Id, FH => Zero_Key,
         V => (T => 1_000_000, Author => S1, Seq => 1, H => Hsh (83)),
         Issuer => Fnd, Del_TTL => 0, Epoch => 0);
      X81  : constant Header :=
        (K => K_Revoke, NS => NS, Ent => Zero_Id, FH => Zero_Key,
         V => (T => 0, Author => S1, Seq => 1, H => Hsh (84)),
         Issuer => Key (8), Del_TTL => 0, Epoch => 0);
      S    : State := Empty (NS, Fnd, 16, 16);
      St   : Status;
   begin
      --  (a) Member_Of.
      Check ("Member_Of finds each member's dh_pk and nothing else",
             Member_Of (R.C, DH1) = 1 and then Member_Of (R.C, DH2) = 2
             and then Member_Of (R.C, DHX) = 0 and then S1 /= S2);

      --  (b) The gate.
      Apply (S, RH, St);
      Check ("founding roster applied and effective",
             St = OK and then Roster_Eff (S) = (Present => True, Hdr => RH));
      Check ("gate admits each listed member, refuses an unlisted key",
             Gate (S, R, DH1) and then Gate (S, R, DH2) and then not Gate (S, R, DHX));
      Apply (S, X81, St);
      Check ("a certified root's REVOKE of member 1 (from 0) closes the gate for its dh_pk",
             St = OK and then Revoked (S, S1) and then not Gate (S, R, DH1)
             and then Gate (S, R, DH2));
      Lemma_Gate_Refuses_Revoked (S, R, DH1);
      declare
         T : State := S;
      begin
         --  Root-voiding root 8 makes its REVOKE stop counting.
         Apply (T, X8, St);
         Check ("after the root-void of its issuer, the REVOKE stops closing the gate",
                St = OK and then Root_Void (T, Key (8)) and then not Revoked (T, S1)
                and then Gate (T, R, DH1));
         Apply (T, XF1, St);
         Check ("a founding REVOKE with a future from_t closes the gate at once (A3)",
                St = OK and then Revoked (T, S1) and then not Gate (T, R, DH1)
                and then Gate (T, R, DH2));
         Lemma_Gate_Refuses_Revoked (T, R, DH1);
      end;

      --  (c) The quarantine flag. Root 8's roster at epoch 3 is ROSTER_eff.
      declare
         G      : Guard_State;
         Before : State := S;
         After  : State := S;
      begin
         Apply (Before, R8, St);
         Check ("the certified root's roster at the newer epoch is ROSTER_eff",
                St = OK and then Roster_Eff (Before) = (Present => True, Hdr => R8));
         Check ("the flag starts clear", not G.Quarantined);
         --  An OPEN that carries no root-void keeps it clear.
         Note_Open (G, Before, Before);
         Check ("an OPEN without a root-void keeps the flag clear", not G.Quarantined);
         --  A pre-gate OPEN root-voids root 8: ROSTER_eff falls back to
         --  the founding roster at epoch 2, which lists member 1 again.
         After := Before;
         Apply (After, X8, St);
         Check ("the root-void makes ROSTER_eff fall back to the older founding roster",
                St = OK and then Roster_Eff (After) = (Present => True, Hdr => RH));
         Note_Open (G, Before, After);
         Check ("a pre-gate root-void of the signer of ROSTER_eff sets the flag (H2)",
                G.Quarantined);
         Check ("while quarantined, Admits refuses a member the gate would admit",
                Gate (After, R, DH2) and then not Admits (G, After, R, DH2));
         --  A credential that is not founding-signed, or not ROSTER_eff,
         --  does not clear it. The recovery roster does.
         Note_Credential (G, After, R8);
         Check ("a root-voided root's roster as credential keeps the flag", G.Quarantined);
         Note_Credential (G, After, RH);
         Check ("a founding roster that is ROSTER_eff clears the flag", not G.Quarantined);
         G.Quarantined := True;
         declare
            Rec : State := After;
         begin
            Apply (Rec, RF, St);
            Check ("the recovery roster at the next segment is ROSTER_eff whatever the voided root's gen",
                   St = OK and then Roster_Eff (Rec) = (Present => True, Hdr => RF));
            Note_Credential (G, Rec, RH);
            Check ("an older founding roster that is not ROSTER_eff keeps the flag", G.Quarantined);
            Note_Credential (G, Rec, RF);
            Check ("the recovery roster as credential clears the flag", not G.Quarantined);
            Note_Open (G, Rec, Rec);
            Check ("Admits = gate once the flag is clear",
                   not G.Quarantined and then Admits (G, After, R, DH2) = Gate (After, R, DH2));
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
