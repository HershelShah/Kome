--  Test main for Kome.Write: the write path (DESIGN.md §5, §7; SIMPLIFY.md
--  S8, S16, S17; AUDIT.md H18) on real stores with signed frames.
--
--  The tests cover these items:
--    (a) Write of a PUT and of a DEL: OK, the frame is the APPLY at the old
--        log length, the record is held, its seq is seq_self + 1 and
--        seq_self follows it; a reopen of the log holds the record and
--        recovers seq_self (S16);
--    (b) read-your-writes: a second write on the cell is above the first
--        (T8) and replaces it; a write lands at t >= maxceil - Cap_Lead
--        (S8) for PUT and DEL alike;
--    (c) every outcome (S17): OK, Shadowed (a floor at the ceiling by a
--        larger key; nothing built, no seq consumed), Seq_Exhausted,
--        Inadmissible, No_Space (a full data row), Log_Full (a full log);
--        Malformed is the self check, not reached with a Key_Pair key; a
--        refusal changes nothing;
--    (d) the flag Clamped (t_emit < max (now, floor_t + 1));
--    (e) the crash case of S16: a write whose APPLY is lost (the log tail
--        is cut) was never sent, so the next write reuses its seq and
--        nothing is flagged;
--    (f) H18: the same-pace clone. Receive flags an own-key record that
--        changes the pair; a duplicate, a dominated own record and another
--        key's record are not flagged; Clone_Pair and Clone_View hold;
--    (g) AUDIT.md H12: Receive of a roster that finds no room in the
--        authorization rows and raises maxceil returns Ceil_Only, with no
--        flag;
--    (h) AUDIT.md H12: Receive_Ceil, the receiver side of the ceiling
--        frame of a HELLO. A roster above maxceil goes to the cell and to
--        no row, although its signer's slice has room (Ceil_Only;
--        ROSTER_eff is unchanged); the same frame again and a roster at or
--        below maxceil change nothing (OK); bytes that are not a verified
--        ROSTER are Malformed and change nothing; SUSPECT_RELAY is set
--        exactly when the frame raised maxceil and its signer was
--        root-voided before the call.
--  The build uses -gnata, so every Pre / Post runs on these stores.
pragma Ada_2022;
with Ada.Text_IO;      use Ada.Text_IO;
with Ada.Command_Line; use Ada.Command_Line;
with Ada.Exceptions;   use Ada.Exceptions;
with Kome;             use Kome;
with Kome.Versions;    use Kome.Versions;
with Kome.Headers;     use Kome.Headers;
with Kome.Frontier;    use Kome.Frontier;
with Kome.Views;       use Kome.Views;
with Kome.Keys;        use Kome.Keys;
with Kome.Crypto;
with Kome.Records;     use Kome.Records;
with Kome.Emit;        use Kome.Emit;
with Kome.Store;       use Kome.Store;
with Kome.Write;       use Kome.Write;

procedure Test_Write with SPARK_Mode => Off is

   subtype Store_T is Kome.Store.Store;
   subtype Lattice is Kome.Frontier.State;

   function Cnt (L : Lattice) return Held_Count renames Kome.Frontier.Count;

   Failed : Boolean := False;

   procedure Check (Name : String; Cond : Boolean) is
   begin
      Put_Line ((if Cond then "PASS " else "FAIL ") & Name);
      if not Cond then
         Failed := True;
      end if;
   end Check;

   function Fill (Len : Natural; Seed : Natural) return Byte_Array is
     ([for I in 0 .. Len - 1 => Byte ((Seed + 7 * I) mod 256)]);

   function Seed_Of (N : Natural) return Kome.Crypto.Seed is
     (Kome.Crypto.Seed (Fill (Kome.Crypto.Seed_Len, N)));

   function Good_DH (Seed : Natural) return Pubkey is
      K : Pubkey := Pubkey (Fill (Pubkey_Len, Seed));
   begin
      K (31) := K (31) and 16#3F#;
      return K;
   end Good_DH;

   Day : constant U48 := 86_400_000;
   TTL : constant U48 := Del_TTL_Min;

   Root_SK, Dev_SK, Peer_SK, Stranger_SK : Kome.Crypto.Secret_Key;
   Root_PK, Dev_PK, Peer_PK, Stranger_PK : Pubkey;
   Salt_A : constant Salt := Salt (Fill (Salt_Len, 90));
   Cid_A  : Hash256;
   Cert_R : Sig;
   Fnd    : Key256;

   function Member (PK : Pubkey; Seed : Natural) return Byte_Array is
     (PK & Good_DH (Seed) & Fill (Nonce_Len, Seed + 1) & Fill (Box_Len, Seed + 2));

   function Roster_Of (Gen, Ceil : U48) return Byte_Array is
      R : Roster_Record :=
        Make_Roster (Cid_A, Root_PK, Founding_Cap, Cert_R, Good_DH (77), Gen, Ceil,
                     Member (Dev_PK, 11));
   begin
      Sign (Cid_A, R, Root_SK);
      return Encode (R);
   end Roster_Of;

   function Grant_Of (Subject : Pubkey) return Byte_Array is
      G : Grant_Record := Make_Grant (Cid_A, Root_PK, Founding_Cap, Cert_R, Subject);
   begin
      Sign (Cid_A, G, Root_SK);
      return Encode (G);
   end Grant_Of;

   function Ent_B (Ent : Byte) return Ent_Id is (Ent_Id (Fill (Ent_Len, Natural (Ent))));

   function Put_Of
     (Ent : Byte; Field : Character; T, Seq : U48; Value : Byte_Array;
      SK  : Kome.Crypto.Secret_Key; PK : Pubkey) return Byte_Array
   is
      R : Put_Record :=
        Make_Put (Cid_A, Ent_B (Ent), [Character'Pos (Field)], T, Seq, PK, Value);
   begin
      Sign (Cid_A, R, SK);
      return Encode (R);
   end Put_Of;

   procedure Recv
     (S : in out Store_T; L : in out Lattice; F : Byte_Array; St : out Status;
      Flag : out Boolean)
   is
      Off : Log_Size;
   begin
      if not Verified (Cid (S), Root_Key (S), F) then
         raise Program_Error with "test frame not well-formed";
      end if;
      Receive (S, L, F, Header_Of (Cid (S), F), Off, St, Flag);
   end Recv;

   procedure Recv (S : in out Store_T; L : in out Lattice; F : Byte_Array) is
      St : Status;
      Fl : Boolean;
   begin
      Recv (S, L, F, St, Fl);
      if St /= OK then
         raise Program_Error with "setup frame refused: " & St'Image;
      end if;
   end Recv;

   --  A store of the collection for the device key Self, with a roster at
   --  ceiling Ceil and grants to the device and the peer.
   procedure Setup
     (S : out Store_T; L : out Lattice; Self : Pubkey; Ceil : U48 := 30 * Day) is
   begin
      L := Empty (Fnd, L.Cap);
      Open (Root_PK, Salt_A, TTL, Self, L, S);
      Recv (S, L, Roster_Of (1, Ceil));
      Recv (S, L, Grant_Of (Dev_PK));
      Recv (S, L, Grant_Of (Peer_PK));
   end Setup;

   procedure Wr
     (S : in out Store_T; L : in out Lattice; Op : Write_Op; Ent : Byte; Field : Character;
      Now : U48; SK : Kome.Crypto.Secret_Key; Rec : out Header; St : out Status;
      Clamped : out Boolean) is
   begin
      Kome.Write.Write (S, L, Op, Ent_B (Ent), [Character'Pos (Field)], Fill (5, Natural (Ent)), Now, SK,
             Rec, St, Clamped);
   end Wr;

   Log_Cap_A : constant := 64 * 1024;

   procedure Run_All;

   task Runner with Storage_Size => 1024 * 1024 * 1024;

   task body Runner is
   begin
      Run_All;
   exception
      when E : others =>
         Put_Line ("FAIL unexpected exception: " & Exception_Information (E));
         Set_Exit_Status (Failure);
   end Runner;

   procedure Run_All is
      Self : Key256;
   begin
   Kome.Crypto.Key_Pair (Seed_Of (1), Dev_SK, Dev_PK);
   Kome.Crypto.Key_Pair (Seed_Of (2), Stranger_SK, Stranger_PK);
   Kome.Crypto.Key_Pair (Seed_Of (3), Root_SK, Root_PK);
   Kome.Crypto.Key_Pair (Seed_Of (5), Peer_SK, Peer_PK);
   Cid_A := Cid_Of (Root_PK, Salt_A, TTL);
   Fnd := To_Key256 (Root_PK);
   Cert_R := Make_Cert (Root_SK, Cid_A, Root_PK, Founding_Cap);
   Self := To_Key256 (Dev_PK);

   --  (a), (b), (d): OK writes, read-your-writes, the S8 bound, Clamped.
   declare
      L   : Lattice (32);
      S   : Store_T (Log_Cap_A);
      St  : Status;
      Rec, Rec2, Rec3 : Header;
      Cl  : Boolean;
      LL  : Log_Size;
   begin
      Setup (S, L, Dev_PK);
      LL := Log_Length (S);
      Wr (S, L, W_Put, 1, 'a', 28 * Day, Dev_SK, Rec, St, Cl);
      Check ("(a) Write PUT: OK, held, seq = seq_self + 1, seq_self follows",
             St = OK and then Holds (L, Rec) and then Rec.V.Seq = 1
             and then Seq_Self (S) = 1 and then Rec.V.T = 28 * Day
             and then Rec.V.Author = Self and then Rec.K = K_Put and then not Cl);
      Check ("(a) the frame is the APPLY at the old log length",
             Tag_Off (Tag_Of (L, Rec)) = LL and then Log_Byte (S, LL) = Op_Apply
             and then Header_Of (Cid (S), Read_Frame (S, LL)) = Rec);
      Wr (S, L, W_Put, 1, 'a', 27 * Day + 5, Dev_SK, Rec2, St, Cl);
      Check ("(b) T8: a write with a clock behind goes above the first and replaces it",
             St = OK and then Lt (Rec.V, Rec2.V) and then Rec2.V.T = 28 * Day + 1
             and then Holds (L, Rec2) and then not Holds (L, Rec) and then Seq_Self (S) = 2);
      Wr (S, L, W_Put, 2, 'a', 0, Dev_SK, Rec3, St, Cl);
      Check ("(b) S8: a clockless PUT lands at maxceil - Cap_Lead",
             St = OK and then Rec3.V.T = 30 * Day - Cap_Lead and then not Cl);
      Wr (S, L, W_Del, 1, 'a', 0, Dev_SK, Rec, St, Cl);
      Check ("(a) Write DEL: OK above the entity's floor, the entity's PUT gone",
             St = OK and then Rec.K = K_Del and then Holds (L, Rec)
             and then Rec.V.T = 28 * Day + 2 and then not Holds (L, Rec2)
             and then Seq_Self (S) = 4);
      Wr (S, L, W_Put, 3, 'a', 31 * Day, Dev_SK, Rec, St, Cl);
      Check ("(d) Clamped: a clock above maxceil gives t = maxceil",
             St = OK and then Rec.V.T = 30 * Day and then Cl);
      Wr (S, L, W_Put, 4, 'a', 29 * Day, Dev_SK, Rec, St, Cl);
      Check ("(d) not clamped below the ceiling", St = OK and then not Cl);
      declare
         R  : Store_T (Log_Cap_A);
         RL : Lattice (32);
         VL : Log_Size;
      begin
         Open_From_Log (Log_Bytes (S), Dev_PK, RL, R, VL, St);
         Check ("(a) reopen: the written log replays, seq_self recovered from the APPLYs",
                St = OK and then Seq_Self (R) = Seq_Self (S) and then Seq_Self (R) = 6
                and then Cnt (RL) = Cnt (L) and then Holds (RL, Rec));
      end;
   end;

   --  (c) Shadowed, Seq_Exhausted, Inadmissible, No_Space, Log_Full. The
   --  device here is the smaller of the two writer keys, so a floor at the
   --  ceiling by the larger key wins the tie.
   declare
      procedure Shadow_Case
        (Lo_SK : Kome.Crypto.Secret_Key; Lo_PK : Pubkey;
         Hi_SK : Kome.Crypto.Secret_Key; Hi_PK : Pubkey)
      is
      L   : Lattice (32);
      S   : Store_T (Log_Cap_A);
      St  : Status;
      Rec : Header;
      Cl  : Boolean;
      LL  : Log_Size;
      Fl  : Boolean;
   begin
      Setup (S, L, Lo_PK);
      Recv (S, L, Put_Of (1, 'a', 30 * Day, 5, [1], Hi_SK, Hi_PK));
      LL := Log_Length (S);
      Wr (S, L, W_Put, 1, 'a', 0, Lo_SK, Rec, St, Cl);
      Check ("(c) Shadowed: nothing built, nothing appended, no seq consumed",
             St = Shadowed and then Log_Length (S) = LL and then Seq_Self (S) = 0
             and then Rec.V.T = 30 * Day and then Rec.V.Seq = 1 and then Cl
             and then Rec.V.H = Zero_Key);
      Wr (S, L, W_Put, 2, 'a', 0, Lo_SK, Rec, St, Cl);
      Check ("(c) after a Shadowed write the next seq is seq_self + 1",
             St = OK and then Rec.V.Seq = 1 and then Seq_Self (S) = 1);
      --  seq_self at 2^48 - 1: an own-key frame from a peer raised it.
      Recv (S, L, Put_Of (9, 'a', 2 * Day, U48'Last, [1], Lo_SK, Lo_PK), St, Fl);
      Check ("(f) an own-key frame from a peer sets the flag", St = OK and then Fl);
      LL := Log_Length (S);
      Wr (S, L, W_Put, 3, 'a', 0, Lo_SK, Rec, St, Cl);
      Check ("(c) Seq_Exhausted at seq_self = 2^48 - 1, nothing changes",
             Seq_Self (S) = U48'Last and then St = Seq_Exhausted
             and then Log_Length (S) = LL and then not Cl);
      end Shadow_Case;
   begin
      if Lt (Self, To_Key256 (Peer_PK)) then
         Shadow_Case (Dev_SK, Dev_PK, Peer_SK, Peer_PK);
      else
         Shadow_Case (Peer_SK, Peer_PK, Dev_SK, Dev_PK);
      end if;
   end;
   declare
      L   : Lattice (32);
      S   : Store_T (Log_Cap_A);
      St  : Status;
      Rec : Header;
      Cl  : Boolean;
      LL  : Log_Size;
   begin
      Setup (S, L, Stranger_PK);
      LL := Log_Length (S);
      Wr (S, L, W_Put, 1, 'a', 0, Stranger_SK, Rec, St, Cl);
      Check ("(c) a key not in W: Inadmissible, nothing changes",
             St = Inadmissible and then Log_Length (S) = LL and then not Cl);
   end;
   declare
      L   : Lattice (1);
      S   : Store_T (Log_Cap_A);
      St  : Status;
      Rec : Header;
      Cl  : Boolean;
      LL  : Log_Size;
   begin
      Setup (S, L, Dev_PK);
      Wr (S, L, W_Put, 1, 'a', 0, Dev_SK, Rec, St, Cl);
      LL := Log_Length (S);
      Wr (S, L, W_Put, 2, 'a', 0, Dev_SK, Rec, St, Cl);
      Check ("(c) a full data row: No_Space, nothing changes, no seq consumed",
             St = No_Space and then Log_Length (S) = LL and then Seq_Self (S) = 1);
   end;
   declare
      L   : Lattice (8);
      S   : Store_T (Header_Len + 212 + 136 + 4 + 2 * (4 + 199) + 4 + 140);
      St  : Status;
      Rec : Header;
      Cl  : Boolean;
      LL  : Log_Size;
   begin
      Setup (S, L, Dev_PK);
      Wr (S, L, W_Put, 1, 'a', 0, Dev_SK, Rec, St, Cl);
      Check ("(c) setup: one write fits", St = OK);
      LL := Log_Length (S);
      Wr (S, L, W_Put, 2, 'a', 0, Dev_SK, Rec, St, Cl);
      Check ("(c) a full log: Log_Full, nothing changes, no seq consumed",
             St = Log_Full and then Log_Length (S) = LL and then Seq_Self (S) = 1);
   end;

   --  (e) The crash case of S16: the APPLY of a write is lost.
   declare
      L   : Lattice (32);
      S   : Store_T (Log_Cap_A);
      St  : Status;
      Rec, Rec2 : Header;
      Cl  : Boolean;
      Pre_Log : Byte_Array (0 .. Log_Cap_A);
      PL  : Log_Size;
   begin
      Setup (S, L, Dev_PK);
      Wr (S, L, W_Put, 1, 'a', 0, Dev_SK, Rec, St, Cl);
      PL := Log_Length (S);
      Pre_Log (0 .. PL - 1) := Log_Bytes (S);
      Wr (S, L, W_Put, 2, 'a', 0, Dev_SK, Rec, St, Cl);
      Check ("(e) setup: two writes, seq 2", St = OK and then Rec.V.Seq = 2);
      declare
         R  : Store_T (Log_Cap_A);
         RL : Lattice (32);
         VL : Log_Size;
      begin
         --  The tail with the second APPLY is lost before it was durable:
         --  the frame was never sent.
         Open_From_Log (Pre_Log (0 .. PL - 1), Dev_PK, RL, R, VL, St);
         Check ("(e) reopen after the lost tail: seq_self 1", St = OK and then Seq_Self (R) = 1);
         Wr (R, RL, W_Put, 3, 'a', 0, Dev_SK, Rec2, St, Cl);
         Check ("(e) the next write reuses seq 2, nothing flagged",
                St = OK and then Rec2.V.Seq = 2
                and then not Clone_View (RL, Self, Seq_Self (R)));
      end;
   end;

   --  (f) H18: Receive's flag, Clone_Pair, Clone_View.
   declare
      L1, L2 : Lattice (32);
      S1, S2 : Store_T (Log_Cap_A);
      St     : Status;
      Fl     : Boolean;
      Q1, Q2 : Header;
      Cl     : Boolean;
      Off    : Log_Size;
   begin
      Setup (S1, L1, Dev_PK);
      Setup (S2, L2, Dev_PK);
      --  Two devices with one key and equal seq_self write one record each.
      Wr (S1, L1, W_Put, 1, 'a', 0, Dev_SK, Q1, St, Cl);
      Wr (S2, L2, W_Put, 2, 'a', 0, Dev_SK, Q2, St, Cl);
      Check ("(f) both write at seq 1", Q1.V.Seq = 1 and then Q2.V.Seq = 1 and then St = OK);
      Receive (S1, L1, Read_Frame (S2, Tag_Off (Tag_Of (L2, Q2))), Q2, Off, St, Fl);
      Check ("(f) H18: the clone's record at the same pace sets the flag", St = OK and then Fl);
      Lemma_Clone_Pair_Def (L1, Self);
      Check ("(f) Clone_Pair and Clone_View hold; Clone_Detected is quiet (S16)",
             Clone_Pair (L1, Self) and then Clone_View (L1, Self, Seq_Self (S1))
             and then not Clone_Detected (Seq_Self (S1), Max_Own_Seq (L1, Self)));
      Receive (S1, L1, Read_Frame (S2, Tag_Off (Tag_Of (L2, Q2))), Q2, Off, St, Fl);
      Check ("(f) a duplicate own record: OK, not flagged", St = OK and then not Fl);
      Recv (S1, L1, Put_Of (5, 'a', 2 * Day, 3, [1], Peer_SK, Peer_PK), St, Fl);
      Check ("(f) another key's record: OK, not flagged", St = OK and then not Fl);
      Recv (S1, L1, Put_Of (5, 'a', 1 * Day, 8, [1], Dev_SK, Dev_PK), St, Fl);
      Check ("(f) a dominated own record: Dominated, not flagged",
             St = Dominated and then not Fl);
   end;

   ---------------------------------------------------------------------------
   --  (g) W1 (AUDIT.md H12): Receive of a roster that the authorization
   --  rows have no room for and whose ceiling is above maxceil returns
   --  Ceil_Only, with no flag; its Post (Put_Done) executes. The rows are
   --  filled through the slot table (15 certified roots take the slots
   --  2 .. 16, so the roster's signer has none): a full slice of 512
   --  records is too slow under -gnata (see test_store.adb).
   ---------------------------------------------------------------------------
   declare
      L   : Lattice (8);
      S   : Store_T (Log_Cap_A);
      St  : Status;
      Fl  : Boolean;
      LL  : Log_Size;
      Cap_Q : constant U48 := 40 * Day;
      Q_SK  : Kome.Crypto.Secret_Key;
      Q_PK  : Pubkey;
   begin
      Setup (S, L, Dev_PK);
      for I in 1 .. Signers_Max - 1 loop
         Kome.Crypto.Key_Pair (Seed_Of (100 + I), Q_SK, Q_PK);
         declare
            X : Revoke_Record :=
              Make_Revoke (Cid_A, Q_PK, Cap_Q, Make_Cert (Root_SK, Cid_A, Q_PK, Cap_Q),
                           Stranger_PK, 0);
         begin
            Sign (Cid_A, X, Q_SK);
            Recv (S, L, Encode (X));
         end;
      end loop;
      Kome.Crypto.Key_Pair (Seed_Of (100 + Signers_Max), Q_SK, Q_PK);
      declare
         R : Roster_Record :=
           Make_Roster (Cid_A, Q_PK, Cap_Q, Make_Cert (Root_SK, Cid_A, Q_PK, Cap_Q),
                        Good_DH (77), 1, 35 * Day, Member (Dev_PK, 11));
      begin
         Sign (Cid_A, R, Q_SK);
         LL := Log_Length (S);
         Recv (S, L, Encode (R), St, Fl);
         Check ("(g) W1: Receive of a roster with no slot and a higher ceiling: Ceil_Only,"
                & " not flagged",
                St = Ceil_Only and then not Fl and then Max_Ceil (L) = 35 * Day
                and then Has_Ceil (L) and then Ceil_Held (L) = Header_Of (Cid_A, Encode (R))
                and then not Holds (L, Header_Of (Cid_A, Encode (R)))
                and then Log_Byte (S, LL) = Op_Ceil
                and then Log_Length (S) = LL + Apply_Prefix + Encode (R)'Length);
         LL := Log_Length (S);
         Recv (S, L, Encode (R), St, Fl);
         Check ("(g) W1: the same roster again: Auth_Full, nothing appended, not flagged",
                St = Auth_Full and then not Fl and then Log_Length (S) = LL);
      end;
   end;

   ---------------------------------------------------------------------------
   --  (h) W2 (AUDIT.md H12): Receive_Ceil. The store has room in every
   --  slice: what keeps the roster out of the rows is the operation, not
   --  the capacity.
   ---------------------------------------------------------------------------
   declare
      L   : Lattice (8);
      S   : Store_T (Log_Cap_A);
      S0  : Store_T (Log_Cap_A);
      St  : Status;
      Fl  : Boolean;
      Off : Log_Size;
      LL  : Log_Size;
      LL0 : Log_Size;                       --  the log length after Setup
      Cap_Q : constant U48 := 60 * Day;
      Q_SK  : Kome.Crypto.Secret_Key;
      Q_PK  : Pubkey;
      Eff0  : Header_View;
      Cnt0  : Held_Count;

      function Q_Roster (Gen, Ceil : U48) return Byte_Array is
         R : Roster_Record :=
           Make_Roster (Cid_A, Q_PK, Cap_Q, Make_Cert (Root_SK, Cid_A, Q_PK, Cap_Q),
                        Good_DH (77), Gen, Ceil, Member (Stranger_PK, 31));
      begin
         Sign (Cid_A, R, Q_SK);
         return Encode (R);
      end Q_Roster;

      function Void_Q return Byte_Array is
         X : Revoke_Record :=
           Make_Revoke (Cid_A, Root_PK, Founding_Cap, Cert_R, Q_PK, 0);
      begin
         Sign (Cid_A, X, Root_SK);
         return Encode (X);
      end Void_Q;
   begin
      Kome.Crypto.Key_Pair (Seed_Of (200), Q_SK, Q_PK);
      Setup (S, L, Dev_PK);
      Eff0 := Roster_Eff (L);
      Cnt0 := Cnt (L);
      LL0 := Log_Length (S);
      declare
         --  A roster of Q with gen 9 (above the founding roster's gen 1)
         --  that lists a stranger only: in a row it would be ROSTER_eff.
         R35  : constant Byte_Array := Q_Roster (9, 35 * Day);
         R20  : constant Byte_Array := Q_Roster (9, 20 * Day);
         R40  : constant Byte_Array := Q_Roster (9, 40 * Day);
         Bad  : Byte_Array := R40;
         G    : constant Byte_Array := Grant_Of (Stranger_PK);
         None : constant Byte_Array (1 .. 0) := [];
      begin
         LL := Log_Length (S);
         Receive_Ceil (S, L, R35, Off, St, Fl);
         Check ("(h) W2: Receive_Ceil of a roster above maxceil: Ceil_Only, a CEIL entry,"
                & " the cell holds it, not flagged",
                St = Ceil_Only and then not Fl and then Off = LL
                and then Max_Ceil (L) = 35 * Day
                and then Has_Ceil (L) and then Ceil_Held (L) = Header_Of (Cid_A, R35)
                and then Ceil_Live (L)
                and then Log_Byte (S, LL) = Op_Ceil
                and then Log_Length (S) = LL + Apply_Prefix + R35'Length);
         Check ("(h) W2: the roster is in no row although its signer has room;"
                & " ROSTER_eff is unchanged",
                not Holds (L, Header_Of (Cid_A, R35)) and then Cnt (L) = Cnt0
                and then Roster_Eff (L) = Eff0);

         LL := Log_Length (S);
         S0 := S;
         Receive_Ceil (S, L, R35, Off, St, Fl);
         Check ("(h) W2: the same frame again: OK, nothing changes, not flagged",
                St = OK and then not Fl and then S = S0 and then Off = LL);
         Receive_Ceil (S, L, R20, Off, St, Fl);
         Check ("(h) W2: a roster below maxceil: OK, nothing changes",
                St = OK and then not Fl and then S = S0
                and then Ceil_Held (L) = Header_Of (Cid_A, R35));

         Receive_Ceil (S, L, G, Off, St, Fl);
         Check ("(h) W2: a verified GRANT frame is not a ceiling frame: Malformed,"
                & " nothing changes",
                Verified (Cid_A, Root_PK, G)
                and then St = Malformed and then not Fl and then S = S0 and then Off = LL
                and then Max_Ceil (L) = 35 * Day);
         Bad (Bad'Last) := Bad (Bad'Last) xor 1;
         Receive_Ceil (S, L, Bad, Off, St, Fl);
         Check ("(h) W2: a roster above maxceil with a bad signature: Malformed,"
                & " nothing changes",
                St = Malformed and then not Fl and then S = S0
                and then Max_Ceil (L) = 35 * Day
                and then Ceil_Held (L) = Header_Of (Cid_A, R35));
         Receive_Ceil (S, L, None, Off, St, Fl);
         Check ("(h) W2: an empty frame: Malformed, nothing changes",
                St = Malformed and then not Fl and then S = S0);

         --  The founding REVOKE of Q: Q is root-voided from here on.
         Recv (S, L, Void_Q);
         Check ("(h) W2: the founding REVOKE of the signer: root-voided; the cell stays",
                Root_Void (L, To_Key256 (Q_PK)) and then Max_Ceil (L) = 35 * Day
                and then Ceil_Held (L) = Header_Of (Cid_A, R35));
         S0 := S;
         Receive_Ceil (S, L, R35, Off, St, Fl);
         Check ("(h) W2: a frame of a root-voided signer that changes nothing: OK,"
                & " not flagged",
                St = OK and then not Fl and then S = S0);
         Receive_Ceil (S, L, R40, Off, St, Fl);
         Check ("(h) W2: a frame of a root-voided signer that raises maxceil: Ceil_Only,"
                & " SUSPECT_RELAY",
                St = Ceil_Only and then Fl and then Max_Ceil (L) = 40 * Day
                and then Ceil_Held (L) = Header_Of (Cid_A, R40)
                and then not Holds (L, Header_Of (Cid_A, R40))
                and then Roster_Eff (L) = Eff0);
         Receive_Ceil (S, L, R40, Off, St, Fl);
         Check ("(h) W2: the same frame again: OK, not flagged a second time",
                St = OK and then not Fl);
      end;

      --  A log with room for the records of Setup and 100 bytes more:
      --  Log_Full, nothing changes; the flag is not set.
      declare
         L2 : Lattice (8);
         S2 : Store_T (LL0 + 100);
         S3 : Store_T (LL0 + 100);
         R45 : constant Byte_Array := Q_Roster (9, 45 * Day);
      begin
         Setup (S2, L2, Dev_PK);
         S3 := S2;
         Receive_Ceil (S2, L2, R45, Off, St, Fl);
         Check ("(h) W2: no log room for the CEIL entry: Log_Full, nothing changes",
                Log_Length (S3) = LL0 and then St = Log_Full and then not Fl and then S2 = S3
                and then Max_Ceil (L2) = 30 * Day and then not Has_Ceil (L2));
      end;
   end;

   if Failed then
      Set_Exit_Status (Failure);
   end if;
   end Run_All;

begin
   null;
end Test_Write;
