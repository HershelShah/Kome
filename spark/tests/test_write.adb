--  Test main for Kome.Write: the write path (DESIGN.md §5 steps 1-3, §7;
--  AUDIT.md A10, H18) on real stores with signed frames.
--
--  The tests cover these items:
--    (a) Prepare / Commit of a PUT and of a DEL: OK, the frame is the APPLY
--        at Off, the record is held, Seq_Persist is seq_self + 1, and a
--        reopen of the log holds the record (T18 on the written log);
--    (b) read-your-writes: a second write on the cell is above the first
--        (T8) and replaces it;
--    (c) every status of Prepare: OK, Shadowed (a floor at the ceiling by
--        a larger key), Seq_Exhausted, Inadmissible; Malformed is the
--        self check, not reached with a Key_Pair key (only its absence is
--        tested: every Ready frame verifies);
--    (d) every status of Commit: OK, Dominated (a peer record on the cell
--        arrived between Prepare and Commit, and a Shadowed write),
--        Inadmissible (a store of the collection without the grant),
--        No_Space (a full data row), Log_Full (a full log); a refusal
--        changes nothing;
--    (e) the flags Clamped and Born_Expired as Choose gives them, and
--        Clone_Suspected after a backup restore (H8);
--    (f) seq_self at open: Seq_Self_At_Open, and Open_Seq for no store, a
--        value below and above the held own seq, and a torn store
--        (Seq_Corrupt, apart from Seq_Exhausted); no refusal of a large
--        jump;
--    (g) the crash scenario of A10: seq_self is persisted after Prepare and
--        before Commit; a crash between them loses the frame, which no
--        peer has; on reopen the next write takes a larger seq (no reuse)
--        and nothing is flagged. The bad order (the frame sent before its
--        APPLY was durable, the log tail lost) flags the frame when a peer
--        offers it back;
--    (h) H18, the same-pace clone: two devices with one key and equal
--        seq_self write one record each at the same seq. Clone_Detected
--        misses it; Receive flags the other's record; Clone_Pair and
--        Clone_View hold;
--    (i) Receive does not flag a duplicate own record, a dominated own
--        record, an expired own DEL or a record by another key.
--  The build uses -gnata, so every Pre / Post runs on these stores.
pragma Ada_2022;
with Ada.Text_IO;      use Ada.Text_IO;
with Ada.Command_Line; use Ada.Command_Line;
with Ada.Exceptions;   use Ada.Exceptions;
with Kome;             use Kome;
with Kome.Versions;    use Kome.Versions;
with Kome.Headers;     use Kome.Headers;
with Kome.Frontier;    use Kome.Frontier;
with Kome.Keys;        use Kome.Keys;
with Kome.Crypto;
with Kome.Records;     use Kome.Records;
with Kome.Emit;        use Kome.Emit;
with Kome.Store;       use Kome.Store;
with Kome.Write;       use Kome.Write;

procedure Test_Write with SPARK_Mode => Off is

   subtype Store_T is Kome.Store.Store;
   subtype Lattice is Kome.Frontier.State;

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

   function Member (PK : Pubkey; Seed : Natural) return Byte_Array is
     (PK & Good_DH (Seed) & Fill (Nonce_Len, Seed + 1) & Fill (Box_Len, Seed + 2));

   Day  : constant U48 := 86_400_000;
   TTL  : constant U48 := Del_TTL_Min;
   Ceil_T : constant U48 := 100 * Day;

   Root_SK, Dev_SK, Peer_SK, Stranger_SK : Kome.Crypto.Secret_Key;
   Root_PK, Dev_PK, Peer_PK, Stranger_PK : Pubkey;
   Salt_A : constant Salt := Salt (Fill (Salt_Len, 90));
   NS_A   : NS_Id;
   NS     : Id128;
   Fnd    : Key256;

   function Ent_B (E : Byte) return Ent_Id is (Ent_Id (Fill (Ent_Len, Natural (E))));

   function Roster_Frame return Byte_Array is
      R : Roster_Record :=
        Make_Roster (Root_PK, Salt_A, Root_PK, 0, Zero_Sig, Good_DH (77), 1, Ceil_T, TTL, 0,
                     [], Member (Dev_PK, 11) & Member (Peer_PK, 21));
   begin
      Sign (R, Root_SK);
      return Encode (R);
   end Roster_Frame;

   function Grant_Frame (Subject : Pubkey) return Byte_Array is
      G : Grant_Record := Make_Grant (Root_PK, Salt_A, Root_PK, 0, Zero_Sig, Subject);
   begin
      Sign (G, Root_SK);
      return Encode (G);
   end Grant_Frame;

   --  A PUT or a DEL signed by SK, built outside Kome.Write (a peer's).
   function Put_Of
     (Ent : Byte; Field : Character; T, Seq : U48; Value : Byte_Array;
      SK  : Kome.Crypto.Secret_Key; PK : Pubkey) return Byte_Array
   is
      R : Put_Record :=
        Make_Put (NS_A, Ent_B (Ent), [Character'Pos (Field)], T, Seq, PK, Value);
   begin
      Sign (R, SK);
      return Encode (R);
   end Put_Of;

   function Del_Of (Ent : Byte; T, Seq : U48; SK : Kome.Crypto.Secret_Key; PK : Pubkey)
     return Byte_Array
   is
      R : Del_Record := Make_Del (NS_A, Ent_B (Ent), T, Seq, PK);
   begin
      Sign (R, SK);
      return Encode (R);
   end Del_Of;

   function Hdr (F : Byte_Array) return Header is (Header_Of (F));

   Cap   : constant := 32;
   Slice : constant := 8;
   ICap  : constant := Cap + Signers_Max * Slice;
   LCap  : constant := 65_536;

   procedure Put (S : in out Store_T; L : in out Lattice; F : Byte_Array) is
      Off : Log_Size;
      St  : Status;
   begin
      Put_Frame (S, L, F, Hdr (F), Off, St);
      if St /= OK then
         raise Program_Error with "setup frame refused: " & St'Image;
      end if;
   end Put;

   --  A store of the collection with the roster and, if Granted, the
   --  grants of the device and of the peer.
   procedure Setup (S : out Store_T; L : out Lattice; Granted : Boolean := True) is
   begin
      L := Empty (NS, Fnd, L.Cap, L.Slice);
      Open (Root_PK, Salt_A, L, S);
      Put (S, L, Roster_Frame);
      if Granted then
         Put (S, L, Grant_Frame (Dev_PK));
         Put (S, L, Grant_Frame (Peer_PK));
      end if;
   end Setup;

   --  Prepare a write; the flags go to the globals below.
   Cl, Cm, Bx : Boolean;

   procedure Prep
     (S        : Store_T; L : Lattice; Op : Write_Op; Ent : Byte; Field : Character;
      Value    : Byte_Array; Now : U48; SK : Kome.Crypto.Secret_Key; Seq_Self : U48;
      P        : out Prepared; Seq_P : out U48; St : out Status) is
   begin
      Prepare (S, L, Op, Ent_B (Ent), [Character'Pos (Field)], Value, Now, SK, Seq_Self,
               P, Seq_P, St, Cl, Cm, Bx);
   end Prep;

   --  Prepare and Commit; Seq_Self becomes the persisted value.
   procedure Write_Once
     (S   : in out Store_T; L : in out Lattice; Op : Write_Op; Ent : Byte;
      Field : Character; Value : Byte_Array; Now : U48; SK : Kome.Crypto.Secret_Key;
      Seq_Self : in out U48; P : out Prepared; St : out Status)
   is
      Seq_P : U48;
      Off   : Log_Size;
   begin
      Prep (S, L, Op, Ent, Field, Value, Now, SK, Seq_Self, P, Seq_P, St);
      if St in OK | Shadowed then
         Seq_Self := Seq_P;               --  the binding persists it here
         Commit (S, L, P, Off, St);
      end if;
   end Write_Once;

   procedure Reopen (S : Store_T; R : out Store_T; RL : out Lattice; St : out Status) is
      VL : Log_Size;
   begin
      Open_From_Log (Log_Bytes (S), RL, R, VL, St);
   end Reopen;

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
   begin
   Kome.Crypto.Key_Pair (Seed_Of (1), Dev_SK, Dev_PK);
   Kome.Crypto.Key_Pair (Seed_Of (2), Stranger_SK, Stranger_PK);
   Kome.Crypto.Key_Pair (Seed_Of (3), Root_SK, Root_PK);
   Kome.Crypto.Key_Pair (Seed_Of (5), Peer_SK, Peer_PK);
   NS_A := Collection_Id (Root_PK, Salt_A);
   NS := To_Id128 (NS_A);
   Fnd := To_Key256 (Root_PK);

   ---------------------------------------------------------------------------
   --  (a) PUT and DEL through Prepare / Commit; (b) read-your-writes.
   ---------------------------------------------------------------------------
   declare
      S     : Store_T (ICap, LCap, Kome.Store.Bnd_Cap_For (LCap));
      L     : Lattice (Cap, Slice);
      P, P2 : Prepared;
      Seq_P : U48;
      St    : Status;
      Off   : Log_Size;
      LL    : Log_Size;
   begin
      Setup (S, L);
      Prep (S, L, W_Put, 1, 'a', [1, 2, 3], 10 * Day, Dev_SK, 0, P, Seq_P, St);
      Check ("(a) Prepare PUT: OK, Ready, Seq_Persist = seq_self + 1, no flag",
             St = OK and then Ready (P) and then Seq_P = 1 and then not Cl
             and then not Cm and then not Bx);
      Check ("(a) the frame verifies and decodes to Rec (P), with t = now and the device key",
             Verified (Frame_Of (P)) and then Hdr (Frame_Of (P)) = Rec (P)
             and then Rec (P).V.T = 10 * Day and then Rec (P).V.Seq = 1
             and then Rec (P).V.Author = Self_Of (Dev_SK) and then Rec (P).K = K_Put);
      Check ("(a) Prepare changes nothing (the record is not held yet)",
             not Holds (L, Rec (P)));
      LL := Log_Length (S);
      Commit (S, L, P, Off, St);
      Check ("(a) Commit: OK, held, indexed, APPLY at Off = old log length",
             St = OK and then Holds (L, Rec (P)) and then Indexed (S, Rec (P))
             and then Off = LL and then Read_Frame (S, Off) = Frame_Of (P));
      Prep (S, L, W_Put, 1, 'a', [4], 5 * Day, Dev_SK, Seq_P, P2, Seq_P, St);
      Check ("(b) T8: a second write with a clock behind still goes above the first",
             St = OK and then Seq_P = 2 and then Lt (Rec (P).V, Rec (P2).V)
             and then Rec (P2).V.T = 10 * Day + 1 and then Dominates (Rec (P2), Rec (P)));
      Commit (S, L, P2, Off, St);
      Check ("(b) Commit replaces the first record",
             St = OK and then Holds (L, Rec (P2)) and then not Holds (L, Rec (P)));
      Prep (S, L, W_Del, 1, 'x', [], 20 * Day, Dev_SK, Seq_P, P, Seq_P, St);
      Check ("(a) Prepare DEL: OK, a DEL at t >= maxceil - Cap_Lead",
             St = OK and then Ready (P) and then Rec (P).K = K_Del and then Seq_P = 3
             and then Rec (P).V.T = Ceil_T - Cap_Lead);
      Commit (S, L, P, Off, St);
      Check ("(a) Commit DEL: held, and the PUT of the entity is gone",
             St = OK and then Holds (L, Rec (P)) and then not Holds (L, Rec (P2)));
      declare
         R  : Store_T (ICap, LCap, Kome.Store.Bnd_Cap_For (LCap));
         RL : Lattice (Cap, Slice);
      begin
         Reopen (S, R, RL, St);
         Check ("(a) reopen: the written log replays and holds the DEL",
                St = OK and then Holds (RL, Rec (P)) and then not Holds (RL, Rec (P2))
                and then Kome.Frontier.Count (RL) = Kome.Frontier.Count (L));
         Check ("(f) reopen: seq_self = max (stored, held own) = 3 (the DEL)",
                Seq_Self_At_Open (0, RL, Self_Of (Dev_SK)) = 3
                and then Seq_Self_At_Open (7, RL, Self_Of (Dev_SK)) = 7);
      end;
   end;

   ---------------------------------------------------------------------------
   --  (c) the statuses of Prepare; (e) the flags.
   ---------------------------------------------------------------------------
   declare
      S     : Store_T (ICap, LCap, Kome.Store.Bnd_Cap_For (LCap));
      L     : Lattice (Cap, Slice);
      P     : Prepared;
      Seq_P : U48;
      St    : Status;
      Off   : Log_Size;
   begin
      Setup (S, L);
      Prep (S, L, W_Put, 2, 'a', [1], Day, Stranger_SK, 0, P, Seq_P, St);
      Check ("(c) a key not in W: Inadmissible, not Ready, seq_self unchanged",
             St = Inadmissible and then not Ready (P) and then Seq_P = 0);
      Prep (S, L, W_Put, 2, 'a', [1], Day, Dev_SK, U48'Last, P, Seq_P, St);
      Check ("(c) seq_self at 2^48 - 1: Seq_Exhausted, not Ready, nothing persisted",
             St = Seq_Exhausted and then not Ready (P) and then Seq_P = U48'Last);
      Prep (S, L, W_Put, 2, 'a', [1], 2**40, Dev_SK, 2**40, P, Seq_P, St);
      Check ("(f) no refusal of a large seq jump: seq_self 2^40 gives 2^40 + 1",
             St = OK and then Seq_P = 2**40 + 1);
      --  Clamped: the clock is above the ceiling.
      Prep (S, L, W_Put, 2, 'a', [1], Ceil_T + Day, Dev_SK, 0, P, Seq_P, St);
      Check ("(e) Clamped: a clock above maxceil gives t = maxceil",
             St = OK and then Cm and then not Bx and then Rec (P).V.T = Ceil_T);
      --  Born_Expired: a DEL with t + del_ttl_eff <= now.
      Prep (S, L, W_Del, 2, 'x', [], Ceil_T + TTL, Dev_SK, 0, P, Seq_P, St);
      Check ("(e) Born_Expired: a DEL at the ceiling with now = ceiling + del_ttl",
             St = OK and then Bx and then Cm and then Rec (P).V.T = Ceil_T);
      --  Shadowed: the floor is at the ceiling, by the larger key of the
      --  two writers; the smaller key writes.
      declare
         Dev_Big : constant Boolean := Lt (Self_Of (Peer_SK), Self_Of (Dev_SK));
         F_Big   : constant Byte_Array :=
           (if Dev_Big then Put_Of (3, 'a', Ceil_T, 1, [9], Dev_SK, Dev_PK)
            else Put_Of (3, 'a', Ceil_T, 1, [9], Peer_SK, Peer_PK));
      begin
         Put (S, L, F_Big);
         if Dev_Big then
            Prep (S, L, W_Put, 3, 'a', [1], Ceil_T + Day, Peer_SK, 5, P, Seq_P, St);
         else
            Prep (S, L, W_Put, 3, 'a', [1], Ceil_T + Day, Dev_SK, 5, P, Seq_P, St);
         end if;
         Check ("(c) Shadowed: the floor at the ceiling has a larger key; Ready, seq persisted",
                St = Shadowed and then Ready (P) and then Seq_P = 6
                and then Rec (P).V.T = Ceil_T and then Lt (Rec (P).V, Hdr (F_Big).V));
         Commit (S, L, P, Off, St);
         Check ("(d) Commit of a Shadowed write: Dominated, not held",
                St = Dominated and then not Holds (L, Rec (P)));
      end;
      --  H8: a held own record above seq_self (a restored backup).
      Put (S, L, Put_Of (4, 'b', Day, 50, [1], Dev_SK, Dev_PK));
      Prep (S, L, W_Put, 4, 'c', [1], 2 * Day, Dev_SK, 10, P, Seq_P, St);
      Check ("(e) H8: Clone_Suspected, seq jumps past the held own seq 50",
             St = OK and then Cl and then Seq_P = 51
             and then Clone_View (L, Self_Of (Dev_SK), 10)
             and then not Clone_View (L, Self_Of (Dev_SK), 51));
   end;

   ---------------------------------------------------------------------------
   --  (d) the statuses of Commit.
   ---------------------------------------------------------------------------
   declare
      S     : Store_T (ICap, LCap, Kome.Store.Bnd_Cap_For (LCap));
      L     : Lattice (Cap, Slice);
      P     : Prepared;
      Seq_P : U48;
      St    : Status;
      Off   : Log_Size;
      LL    : Log_Size;
      Fl    : Boolean;
   begin
      Setup (S, L);
      Prep (S, L, W_Put, 5, 'a', [1], 10 * Day, Dev_SK, 0, P, Seq_P, St);
      --  A peer's write on the cell arrives between Prepare and Commit.
      declare
         Peer : constant Byte_Array := Put_Of (5, 'a', 20 * Day, 1, [2], Peer_SK, Peer_PK);
      begin
         Receive (S, L, Peer, Hdr (Peer), Self_Of (Dev_SK), Off, St, Fl);
         Check ("(i) a peer's record: OK, not flagged", St = OK and then not Fl);
         LL := Log_Length (S);
         Commit (S, L, P, Off, St);
         Check ("(d) Commit after a newer peer write on the cell: Dominated, nothing appended",
                St = Dominated and then not Holds (L, Rec (P)) and then Log_Length (S) = LL
                and then Holds (L, Hdr (Peer)));
      end;
      --  Commit to a store of the collection that lacks the grant.
      declare
         S2 : Store_T (ICap, LCap, Kome.Store.Bnd_Cap_For (LCap));
         L2 : Lattice (Cap, Slice);
      begin
         Setup (S2, L2, Granted => False);
         Prep (S, L, W_Put, 6, 'a', [1], 10 * Day, Dev_SK, 1, P, Seq_P, St);
         LL := Log_Length (S2);
         Commit (S2, L2, P, Off, St);
         Check ("(d) Commit on a store without the grant: Inadmissible, nothing changes",
                St = Inadmissible and then Log_Length (S2) = LL
                and then not Holds (L2, Rec (P)));
      end;
   end;

   --  No_Space: a data row of one record.
   declare
      S     : Store_T (1 + Signers_Max * Slice, LCap, Kome.Store.Bnd_Cap_For (LCap));
      L     : Lattice (1, Slice);
      P     : Prepared;
      Seq_P : U48 := 0;
      St    : Status;
      Off   : Log_Size;
      LL    : Log_Size;
   begin
      Setup (S, L);
      Write_Once (S, L, W_Put, 7, 'a', [1], Day, Dev_SK, Seq_P, P, St);
      Prep (S, L, W_Put, 8, 'a', [1], Day, Dev_SK, Seq_P, P, Seq_P, St);
      Check ("(d) Prepare on a full data row: OK (Choose does not see room)", St = OK);
      LL := Log_Length (S);
      Commit (S, L, P, Off, St);
      Check ("(d) Commit on a full data row: No_Space, nothing changes",
             St = No_Space and then not Holds (L, Rec (P)) and then Log_Length (S) = LL);
   end;

   --  Log_Full: a log with room for the HEADER, the roster and the grants.
   declare
      Need : constant Natural :=
        Header_Len + 5 + Roster_Frame'Length + 2 * (5 + Grant_Frame (Dev_PK)'Length) + 10;
      S     : Store_T (ICap, Need, Kome.Store.Bnd_Cap_For (Need));
      L     : Lattice (Cap, Slice);
      P     : Prepared;
      Seq_P : U48;
      St    : Status;
      Off   : Log_Size;
   begin
      Setup (S, L);
      Prep (S, L, W_Put, 9, 'a', [1], Day, Dev_SK, 0, P, Seq_P, St);
      Commit (S, L, P, Off, St);
      Check ("(d) Commit on a full log: Log_Full, nothing changes",
             St = Log_Full and then not Holds (L, Rec (P)) and then Log_Length (S) = Need - 10);
   end;

   ---------------------------------------------------------------------------
   --  (f) Open_Seq.
   ---------------------------------------------------------------------------
   declare
      S     : Store_T (ICap, LCap, Kome.Store.Bnd_Cap_For (LCap));
      L     : Lattice (Cap, Slice);
      Sq    : U48;
      St    : Status;
   begin
      Setup (S, L);
      Put (S, L, Put_Of (10, 'a', Day, 12, [1], Dev_SK, Dev_PK));
      Open_Seq (Seq_None, 99, L, Self_Of (Dev_SK), Sq, St);
      Check ("(f) Open_Seq, no store: OK, the held own seq (12)", St = OK and then Sq = 12);
      Open_Seq (Seq_Read, 5, L, Self_Of (Dev_SK), Sq, St);
      Check ("(f) Open_Seq, a stored value below the held own seq: OK, 12", St = OK and then Sq = 12);
      Open_Seq (Seq_Read, 40, L, Self_Of (Dev_SK), Sq, St);
      Check ("(f) Open_Seq, a stored value above: OK, 40", St = OK and then Sq = 40);
      Open_Seq (Seq_Torn, 40, L, Self_Of (Dev_SK), Sq, St);
      Check ("(f) Open_Seq, a torn store: Seq_Corrupt (not Seq_Exhausted), Max_Own_Seq (12)",
             St = Seq_Corrupt and then Sq = 12);
      Open_Seq (Seq_None, 0, L, Self_Of (Peer_SK), Sq, St);
      Check ("(f) Open_Seq, no own record: 0", St = OK and then Sq = 0);
   end;

   ---------------------------------------------------------------------------
   --  (g) The crash scenario of A10.
   ---------------------------------------------------------------------------
   declare
      S        : Store_T (ICap, LCap, Kome.Store.Bnd_Cap_For (LCap));
      L        : Lattice (Cap, Slice);
      P, Lost  : Prepared;
      Seq_Self : U48 := 0;
      Stored   : U48;
      Seq_P    : U48;
      St       : Status;
      Off      : Log_Size;
      Fl       : Boolean;
   begin
      Setup (S, L);
      Write_Once (S, L, W_Put, 11, 'a', [1], Day, Dev_SK, Seq_Self, P, St);
      Stored := Seq_Self;                       --  1, durable
      --  Prepare, persist, crash before Commit: the frame is lost, no peer
      --  has it.
      Prep (S, L, W_Put, 11, 'b', [2], 2 * Day, Dev_SK, Seq_Self, Lost, Seq_P, St);
      Stored := Seq_P;                          --  2, persisted before the APPLY
      declare
         R  : Store_T (ICap, LCap, Kome.Store.Bnd_Cap_For (LCap));
         RL : Lattice (Cap, Slice);
      begin
         Reopen (S, R, RL, St);
         Open_Seq (Seq_Read, Stored, RL, Self_Of (Dev_SK), Seq_Self, St);
         Check ("(g) after the crash: seq_self = the persisted 2, above the held own seq 1",
                St = OK and then Seq_Self = 2 and then not Holds (RL, Rec (Lost)));
         Prep (R, RL, W_Put, 11, 'c', [3], 3 * Day, Dev_SK, Seq_Self, P, Seq_P, St);
         Check ("(g) the next write takes seq 3: no reuse of the lost seq, no flag",
                St = OK and then Seq_P = 3 and then Seq_P > Rec (Lost).V.Seq
                and then not Cl);
         Seq_Self := Seq_P;
         Commit (R, RL, P, Off, St);
         Check ("(g) committed; no clone view", St = OK
                and then not Clone_View (RL, Self_Of (Dev_SK), Seq_Self));
         --  The bad order: the lost frame had been sent before its APPLY was
         --  durable, and a peer offers it back. Receive flags it (a lost
         --  log tail is a backup restore, A4′).
         Receive (R, RL, Frame_Of (Lost), Rec (Lost), Self_Of (Dev_SK), Off, St, Fl);
         Check ("(g) the bad order: an own frame that the log lost comes back and is flagged",
                St = OK and then Fl and then Holds (RL, Rec (Lost)));
      end;
   end;

   ---------------------------------------------------------------------------
   --  (h) H18: the same-pace clone; (i) no flag for the other cases.
   ---------------------------------------------------------------------------
   declare
      S1, S2   : Store_T (ICap, LCap, Kome.Store.Bnd_Cap_For (LCap));
      L1, L2   : Lattice (Cap, Slice);
      P1, P2   : Prepared;
      Q1, Q2   : U48 := 0;
      St       : Status;
      Off      : Log_Size;
      Fl       : Boolean;
      Base     : constant Byte_Array := Put_Of (12, 'z', Day, 1, [1], Dev_SK, Dev_PK);
   begin
      Setup (S1, L1);
      Setup (S2, L2);
      --  Both devices hold the key's record at seq 1 and have seq_self 1.
      Put (S1, L1, Base);
      Put (S2, L2, Base);
      Q1 := 1;
      Q2 := 1;
      --  Partitioned, each writes one record at seq 2.
      Write_Once (S1, L1, W_Put, 13, 'x', [1], 2 * Day, Dev_SK, Q1, P1, St);
      Write_Once (S2, L2, W_Put, 14, 'y', [2], 2 * Day, Dev_SK, Q2, P2, St);
      Check ("(h) both write at seq 2", Q1 = 2 and then Q2 = 2 and then St = OK);
      Receive (S1, L1, Frame_Of (P2), Rec (P2), Self_Of (Dev_SK), Off, St, Fl);
      Check ("(h) H18: the clone's record at the same pace sets Clone_Suspected at Apply",
             St = OK and then Fl and then Holds (L1, Rec (P2)));
      Check ("(h) Clone_Detected misses it (Max_Own_Seq = seq_self = 2)",
             not Clone_Detected (Q1, Max_Own_Seq (L1, Self_Of (Dev_SK))));
      Lemma_Clone_Pair_Def (L1, Self_Of (Dev_SK));
      Check ("(h) Clone_Pair and Clone_View hold: two own records at seq 2, different h",
             Clone_Pair (L1, Self_Of (Dev_SK)) and then Clone_View (L1, Self_Of (Dev_SK), Q1));
      --  A duplicate own record.
      Receive (S1, L1, Frame_Of (P1), Rec (P1), Self_Of (Dev_SK), Off, St, Fl);
      Check ("(i) a duplicate own record: OK, not flagged", St = OK and then not Fl);
      --  A dominated own record: an older own PUT on a cell that holds a
      --  newer own PUT.
      declare
         Old_Own : constant Byte_Array := Put_Of (13, 'x', Day, 1, [7], Dev_SK, Dev_PK);
      begin
         Receive (S1, L1, Old_Own, Hdr (Old_Own), Self_Of (Dev_SK), Off, St, Fl);
         Check ("(i) a dominated own record: Dominated, not flagged",
                St = Dominated and then not Fl);
      end;
      --  The same record seen as another key's: not own, not flagged.
      Receive (S2, L2, Frame_Of (P1), Rec (P1), Self_Of (Peer_SK), Off, St, Fl);
      Check ("(i) a newly held record of another key: OK, not flagged",
             St = OK and then not Fl and then Holds (L2, Rec (P1)));
      --  An expired own DEL: applied for its effect, not flagged.
      declare
         Exp_Del : constant Byte_Array := Del_Of (15, Day, 40, Dev_SK, Dev_PK);
      begin
         Kome.Store.Expire (S1, L1, 50 * Day, St);
         Check ("(i) setup: horizon above the DEL", St = OK and then Horizon (S1) >= Time64 (Day));
         Put (S1, L1, Put_Of (15, 'q', Day / 2, 39, [1], Dev_SK, Dev_PK));
         Receive (S1, L1, Exp_Del, Hdr (Exp_Del), Self_Of (Dev_SK), Off, St, Fl);
         Check ("(i) an expired own DEL that drops a record: OK, not held, not flagged",
                St = OK and then not Fl and then not Holds (L1, Hdr (Exp_Del)));
      end;
   end;

   if Failed then
      Set_Exit_Status (Failure);
   end if;
   end Run_All;

begin
   null;
end Test_Write;
