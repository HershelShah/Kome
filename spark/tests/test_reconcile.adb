--  Test main for Kome.Reconcile (DESIGN.md §8, D12-D15). It has these
--  parts:
--  (a) The key order: its lemmas, Data_Lo, and that Key_Lt is bytewise
--      order on the 81-byte wire key (against the Ada lexicographic "<"
--      on byte arrays; Lemma_Key_Lt_First_Difference /
--      Lemma_Key_Eq_Is_Bytewise execute).
--  (b) Snapshots: appends in order, kinds 0 .. 4, no refusal changes the
--      snapshot, and Append accepts a 41 136-byte frame. Seal and the
--      prefix-sum fingerprint (Fingerprint_Of = Range_Fp, D15).
--  (c) Windows and the cover on examples.
--  (d) Encode / Decode round trips for RANGE, ELEMENTS, HAVE and the
--      confirm. OPEN with 0 and 15 frames and HELLO with cred_len 0 and
--      10 099, against the known answers in vectors/reconcile.txt. Decode
--      refuses malformed inputs.
--  (e) The responder: the reply contract (Answers) on examples. The
--      empty-HAVE mutant violates it.
--  (f) Frame tables and Snapshot_Of (A12): the snapshot of a frontier
--      holds exactly its records in key order, with their frames, and
--      its digest is Frontier_Digest; the refusals; a duplicate key.
--  (g) Select_Voids (H5): one founding REVOKE per root-voided subject,
--      the least (from_t, h) one, the 15-subject bound, the fill;
--      Lemma_Voids_Cover; Lists_Peer.
--  (h) The session:
--      * Start: the initiator emits its OPEN, the responder waits and
--        answers the OPEN of the initiator (A14); root-void frames only
--        for a known peer.
--      * A foreign ns aborts.
--      * The HELLO credential (A13, G12): not a roster, a roster that does
--        not list the peer, or one from a root-voided signer aborts, and
--        the credential is not returned.
--      * Receive refuses these messages, and they change nothing: a HELLO
--        before the gate, a RANGE before Auth, a g = 0 HAVE, a partial
--        root, the data root first, a repeated root, a data root while
--        something is open, any g = 0 at the initiator, a reply that is
--        not the head's group, and a duplicated reply (G4, H19).
--      * The gate again under a new Auth_Gen (H11): a REVOKE of the peer's
--        member aborts Receive and Next_Phase.
--      * Equal digests end the session after the HELLOs.
--      * Admit-then-receive and receive-then-Admit both work.
--      * Next_Phase.
--      * Mutants of Receive and Admit (the M, Open, Peer and status of
--        Receive come from the wire and Status_Of; Admit keeps the
--        budgets; Same_Snapshot).
--  (i) Two snapshots with different authorization and data records, and
--      one frame of 41 136 bytes, converge to the union in a two-phase
--      session. A second session ends at the HELLOs.
--  Under -gnata, every Pre, Post and lemma executes on these data.
pragma Ada_2022;
with Ada.Text_IO;      use Ada.Text_IO;
with Ada.Command_Line; use Ada.Command_Line;
with Ada.Exceptions;   use Ada.Exceptions;
with Ada.Directories;
with Ada.Containers.Indefinite_Vectors;
with Kome;             use Kome;
with Kome.Keys;        use Kome.Keys;
with Kome.Headers;     use Kome.Headers;
with Kome.Digest;
with Kome.Frontier;    use Kome.Frontier;
with Kome.Views;       use Kome.Views;
with Kome.Guard;       use Kome.Guard;
with Kome.Records;     use Kome.Records;
with Kome.Reconcile;   use Kome.Reconcile;

procedure Test_Reconcile with SPARK_Mode => Off is

   Failed : Boolean := False;

   procedure Check (Name : String; Cond : Boolean) is
   begin
      Put_Line ((if Cond then "PASS " else "FAIL ") & Name);
      if not Cond then
         Failed := True;
      end if;
   end Check;

   ----------------------------------------------------------------------
   --  Helpers
   ----------------------------------------------------------------------

   function K256 (B : Byte) return Key256 is
     (others => Word (B) * 16#0101_0101#);

   function Id (B : Byte) return Id128 is (others => Word (B));

   function EK (K : Kind_Code; E : Byte; F : Byte; H : Byte) return Elem_Key is
     (K => K, Ent => Id (E), FH => K256 (F), H => K256 (H));

   function Frame_Of (Len : Positive; Fill : Byte) return Byte_Array is
     ([for I in 0 .. Len - 1 => Fill]);

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

   function Msg (K : Msg_Kind; Lo, Hi : Elem_Key; Count : Natural := 0;
                 Fp : Hash256 := [others => 0]) return Message is
     (Kind => K, G => 1, Lo => Lo, Hi => Hi, Count => Count, Fp => Fp,
      N => 0, Items => <>);

   package Msg_Vectors is new Ada.Containers.Indefinite_Vectors
     (Positive, Byte_Array);

   function Slice (B : Msg_Buffer; L : Msg_Length) return Byte_Array is
     (B (0 .. L - 1));

   --  The wire bytes of a key (kind ‖ ent ‖ fh ‖ h).
   function To_Wire (K : Elem_Key) return Key_Wire is
     ([Byte (K.K)] & Kome.Keys.To_Bytes (K.Ent) & Kome.Keys.To_Bytes (K.FH)
      & Kome.Keys.To_Bytes (K.H));

   --  A small snapshot of synthetic elements I = 1 .. N, key (Kind, I, I,
   --  I), frame of Len bytes, sealed.
   procedure Fill (S : in out Snapshot; N : Natural; Len : Positive;
                   Kind : Kind_Code := 3) is
      St : Snap_Status;
   begin
      Clear (S);
      for I in 1 .. N loop
         Append (S, EK (Kind, Byte (I), Byte (I), Byte (I)),
                 Frame_Of (Len, Byte (I)), St);
         if St /= Snap_OK then
            raise Program_Error with "fill";
         end if;
      end loop;
   end Fill;

   --  The prefix-sum table of S (Seal, D15), sized for its count.
   function Table_Of (S : Snapshot) return Prefix is
   begin
      return P : Prefix (Prefix_Slots (Kome.Reconcile.Count (S))) do
         Seal (S, P);
      end return;
   end Table_Of;

   --  Every plan encodes to Plan_Len bytes and decodes back.
   function Plans_Fit (S : Snapshot; O : Outbox) return Boolean is
      PS  : constant Prefix := Table_Of (S);
      Buf : Msg_Buffer;
      L   : Msg_Length;
      M   : Message;
      OK  : Boolean;
   begin
      for T in 1 .. O.N loop
         Encode (S, PS, O.P (T), Group (O), Buf, L);
         if L /= Plan_Len (S, O.P (T)) then
            return False;
         end if;
         Decode (Slice (Buf, L), M, OK);
         if not OK or else M.G /= Group (O) then
            return False;
         end if;
      end loop;
      return True;
   end Plans_Fit;

   --  The number of our elements in [Lo, Hi): My_Count, which is ghost.
   function Cnt (S : Snapshot; Lo, Hi : Elem_Key) return Natural is
     (Window (S, Lo, Hi).Last + 1 - Window (S, Lo, Hi).First);

   --  The reply contract Answers (ghost in the spec), with Cnt for
   --  My_Count, so a test can evaluate it on any outbox.
   function Answers_T (S : Snapshot; M : Message; O : Outbox) return Boolean is
     ((if M.Kind = M_Have then O.N = 0 else O.N >= 1 and then O.Reply)
      and then (if M.Kind = M_Range then
                  (if Confirms (S, M) then Is_Confirm (O, M.Lo, M.Hi)
                   else Tiles (O, M.Lo, M.Hi) and then Exact_Plans (S, O)
                        and then (if Cnt (S, M.Lo, M.Hi) <= Ship_Threshold
                                  then All_Kind (O, P_Elements)
                                  else All_Kind (O, P_Range))))
      and then (if M.Kind = M_Elements then
                  (if Cnt (S, M.Lo, M.Hi) <= Ship_Threshold
                   then Have_Exact (S, M, O)
                   else Tiles (O, M.Lo, M.Hi) and then Exact_Plans (S, O)
                        and then All_Kind (O, P_Range))));

   function From_Hex (S : String) return Byte_Array is
      function Nib (C : Character) return Byte is
        (case C is
           when '0' .. '9' => Character'Pos (C) - Character'Pos ('0'),
           when 'a' .. 'f' => Character'Pos (C) - Character'Pos ('a') + 10,
           when 'A' .. 'F' => Character'Pos (C) - Character'Pos ('A') + 10,
           when others     => raise Constraint_Error);
   begin
      if S = "-" then
         return [];
      end if;
      return R : Byte_Array (0 .. S'Length / 2 - 1) do
         for I in R'Range loop
            R (I) := Nib (S (S'First + 2 * I)) * 16 + Nib (S (S'First + 2 * I + 1));
         end loop;
      end return;
   end From_Hex;

   --  Find vectors/ in the current directory or in one of its parents.
   function Find (Rel : String) return String is
   begin
      if Ada.Directories.Exists (Rel) then
         return Rel;
      elsif Ada.Directories.Exists ("../" & Rel) then
         return "../" & Rel;
      elsif Ada.Directories.Exists ("spark/" & Rel) then
         return "spark/" & Rel;
      else
         return Rel;
      end if;
   end Find;

   ----------------------------------------------------------------------
   --  The fixture of the sessions: a collection with a founding roster
   --  that lists two members (DH1, DH2), its frame as the credential, the
   --  frontier F that holds it (ROSTER_eff), the table of its
   --  authorization frames and the guard state. DHX is a stranger.
   ----------------------------------------------------------------------

   Root_PK : constant Pubkey := Pubkey (Fill (Pubkey_Len, 3));
   Salt_A  : constant Salt := Salt (Fill (Salt_Len, 90));
   Box_A   : constant Pubkey := Good_DH (15);
   Day     : constant U48 := 86_400_000;
   TTL     : constant U48 := 30 * Day;
   NS_X    : constant Id128 := To_Id128 (Collection_Id (Root_PK, Salt_A));
   NS_Y    : constant Id128 := (W0 => 16#4B4F_4D45#, W1 => 1, W2 => 2, W3 => 4);
   Fnd     : constant Key256 := To_Key256 (Root_PK);
   Mem     : constant Byte_Array := Members_Of (2, 33);
   DH1     : constant Pubkey := Pubkey (Mem (Pubkey_Len .. 2 * Pubkey_Len - 1));
   DH2     : constant Pubkey :=
     Pubkey (Mem (Member_Len + Pubkey_Len .. Member_Len + 2 * Pubkey_Len - 1));
   DHX     : constant Pubkey := Good_DH (200);
   --  The founding roster at epoch 2, gen 1 (ROSTER_eff of F), and its
   --  frame: the credential of both peers.
   R_Eff   : constant Roster_Record :=
     Make_Roster (Root_PK, Salt_A, Root_PK, 0, Zero_Sig, Box_A, 1, 5000, TTL, 2, [], Mem);
   RH      : constant Header := To_Header (R_Eff);
   Cred_T  : constant Byte_Array := Encode (R_Eff);
   S1_Key  : constant Key256 := Member_Key (R_Eff.C, 1);
   No_Bytes : constant Byte_Array (1 .. 0) := [];

   function Hsh (B : Natural) return Key256 is (W0 => Word (B), others => 5);
   function KeyB (B : Natural) return Key256 is (others => Word (B));

   --  V = (from_t, subject, 0, h), Issuer = the founding key.
   function Founding_Revoke (Subject : Key256; From_T : U48; H : Natural) return Header is
     (K => K_Revoke, NS => NS_X, Ent => Zero_Id, FH => Zero_Key,
      V => (T => From_T, Author => Subject, Seq => 0, H => Hsh (H)),
      Issuer => Fnd, Del_TTL => 0, Epoch => 0);

   --  V = (cap, subject, 0, h), Issuer = signer.
   function Grant_H (Issuer, Subject : Key256; H : Natural) return Header is
     (K => K_Grant, NS => NS_X, Ent => Zero_Id, FH => Zero_Key,
      V => (T => U48'Last, Author => Subject, Seq => 0, H => Hsh (H)),
      Issuer => Issuer, Del_TTL => 0, Epoch => 0);

   function Put_H (E : Byte; Fld : Byte; T : U48; Author : Key256; Seq : U48; H : Natural)
     return Header is
     (K => K_Put, NS => NS_X, Ent => Id (E), FH => K256 (Fld),
      V => (T => T, Author => Author, Seq => Seq, H => Hsh (H)),
      Issuer => Zero_Key, Del_TTL => 0, Epoch => 0);

   function Del_H (E : Byte; T : U48; Author : Key256; Seq : U48; H : Natural)
     return Header is
     (K => K_Del, NS => NS_X, Ent => Id (E), FH => Zero_Key,
      V => (T => T, Author => Author, Seq => Seq, H => Hsh (H)),
      Issuer => Zero_Key, Del_TTL => 0, Epoch => 0);

   --  A 269-byte REVOKE frame with a distinct content byte.
   function Rv (Seed : Byte) return Rv_Frame is
      B : Rv_Frame := [others => Seed];
   begin
      B (0) := Tag_Revoke;
      return B;
   end Rv;

   --  Apply, and fail loudly if the record is not held.
   procedure Must_Apply (F : in out State; H : Header) is
      St : Status;
   begin
      Apply (F, H, St);
      if St /= OK then
         raise Program_Error with "apply " & St'Image;
      end if;
   end Must_Apply;

   procedure Must_Add (T : in out Frame_Table; Fr : Byte_Array) is
      St : Snap_Status;
   begin
      Add_Frame (T, Fr, St);
      if St /= Snap_OK then
         raise Program_Error with "add_frame " & St'Image;
      end if;
   end Must_Add;

   --  Receive, but keep only the values that a test examines.
   procedure Recv
     (Sess : in out Session; S : Snapshot; P : Prefix; F : State; G : Guard_State;
      Auth_Gen : U64; Input : Byte_Array; O : out Outbox; Res : out Session_Status)
   is
      M  : Message;
      Op : Open_Msg;
      Pr : Hello;
      Gt : Delivery;
      OB : Msg_Buffer;
      OL : Msg_Length;
   begin
      Receive (Sess, S, P, F, G, R_Eff, Auth_Gen, Input, M, Op, Pr, O, Gt, OB, OL, Res);
   end Recv;

   --  A HELLO with the given digest and credential.
   function Hello_Bytes (Digest : Hash256; Cred : Byte_Array := Cred_T) return Byte_Array is
      Buf : Msg_Buffer;
      L   : Msg_Length;
   begin
      Encode_Hello (3, 4, Digest, Cred, Buf, L);
      return Slice (Buf, L);
   end Hello_Bytes;

   function Open_Bytes_Of (NS : Id128) return Byte_Array is
      Buf : Msg_Buffer;
      L   : Msg_Length;
   begin
      Encode_Open ((Proto => Proto_Version, NS => NS, N_RV => 0, RV => [others => Zero_Rv]),
                   Buf, L);
      return Slice (Buf, L);
   end Open_Bytes_Of;

   function Plan_Bytes (S : Snapshot; P : Plan; G : Group_Size) return Byte_Array is
      PS  : constant Prefix := Table_Of (S);
      Buf : Msg_Buffer;
      L   : Msg_Length;
   begin
      Encode (S, PS, P, G, Buf, L);
      return Slice (Buf, L);
   end Plan_Bytes;

   function Range_Plan (S : Snapshot; Lo, Hi : Elem_Key) return Plan is
     (Kind => P_Range, Lo => Lo, Hi => Hi, First => Window (S, Lo, Hi).First,
      Last => Window (S, Lo, Hi).Last, N => 0, Items => [others => 1]);

   function Confirm_Plan (Lo, Hi : Elem_Key) return Plan is
     (Kind => P_Have, Lo => Lo, Hi => Hi, First => 1, Last => 0, N => 0,
      Items => [others => 1]);

   ----------------------------------------------------------------------
   --  Replicas for the convergence test: a list of (key, frame).
   ----------------------------------------------------------------------

   type Elem (Len : Natural) is record
      Key : Elem_Key;
      F   : Byte_Array (1 .. Len);
   end record;

   function Before (A, B : Elem) return Boolean is (Key_Lt (A.Key, B.Key));

   package Elem_Vectors is new Ada.Containers.Indefinite_Vectors
     (Positive, Elem);
   package Elem_Sort is new Elem_Vectors.Generic_Sorting (Before);

   type Replica is record
      Els : Elem_Vectors.Vector;
   end record;

   function Holds (R : Replica; K : Elem_Key) return Boolean is
   begin
      for E of R.Els loop
         if E.Key = K then
            return True;
         end if;
      end loop;
      return False;
   end Holds;

   function Frame_Of_Key (R : Replica; K : Elem_Key) return Byte_Array is
   begin
      for E of R.Els loop
         if E.Key = K then
            return E.F;
         end if;
      end loop;
      return No_Bytes;
   end Frame_Of_Key;

   procedure Add (R : in out Replica; K : Elem_Key; F : Byte_Array) is
   begin
      R.Els.Append (Elem'(Len => F'Length, Key => K, F => F));
   end Add;

   function Same_Set (A, B : Replica) return Boolean is
   begin
      if Natural (A.Els.Length) /= Natural (B.Els.Length) then
         return False;
      end if;
      for E of A.Els loop
         if not Holds (B, E.Key) or else Frame_Of_Key (B, E.Key) /= E.F then
            return False;
         end if;
      end loop;
      return True;
   end Same_Set;

   --  One session, with A as the initiator (static key DH1) and B the
   --  responder (DH2). Messages go in one direction at a time: each side
   --  only answers what it received. The gate of each side admits the
   --  peer when its OPEN arrives (the fixture F, with both members, is
   --  the frontier of both sides for the gate). Rounds counts one-way
   --  batches. Delivered counts the frames given to a replica.
   procedure Run_Session
     (A, B : in out Replica; F : State; Auth_T : Frame_Table; G : Guard_State;
      Rounds : out Natural; Delivered : out Natural;
      All_OK : out Boolean; Both_Complete : out Boolean)
   is
      SA : Snapshot (Cap => 256, Pool_Cap => 400_000);
      SB : Snapshot (Cap => 256, Pool_Cap => 400_000);
      Sess_A, Sess_B : Session (Oblig_Cap => 256);
      To_B, To_A : Msg_Vectors.Vector;
      Buf : Msg_Buffer;
      L   : Msg_Length;

      procedure Snap (R : in out Replica; S : in out Snapshot) is
         St : Snap_Status;
      begin
         Elem_Sort.Sort (R.Els);
         Clear (S);
         for E of R.Els loop
            Append (S, E.Key, E.F, St);
            if St /= Snap_OK then
               All_OK := False;
            end if;
         end loop;
      end Snap;

      procedure Emit (S : Snapshot; P : Prefix; O : Outbox; Q : in out Msg_Vectors.Vector) is
      begin
         for T in 1 .. O.N loop
            Encode (S, P, O.P (T), Group (O), Buf, L);
            Q.Append (Slice (Buf, L));
         end loop;
      end Emit;

      --  Deliver every message of In_Q to replica R. Its answers go to
      --  Out_Q.
      procedure Deliver_All
        (R : in out Replica; S : Snapshot; P : Prefix; Sess : in out Session;
         In_Q : in out Msg_Vectors.Vector; Out_Q : in out Msg_Vectors.Vector)
      is
         M    : Message;
         Op   : Open_Msg;
         Peer : Hello;
         Got  : Delivery;
         St   : Session_Status;
         O2   : Outbox;
         O3   : Outbox;
         OB   : Msg_Buffer;
         OL   : Msg_Length;
      begin
         for Raw of In_Q loop
            Receive (Sess, S, P, F, G, R_Eff, 1, Raw, M, Op, Peer, O2, Got, OB, OL, St);
            if St /= S_OK then
               All_OK := False;
            end if;
            if OL > 0 then
               Out_Q.Append (Slice (OB, OL));
            end if;
            if St = S_OK and then M.Kind = M_Open then
               --  The gate admits the peer: our HELLO.
               Admit (Sess, S, P, F, G, R_Eff, 1, Cred_T, Buf, L, O3);
               Out_Q.Append (Slice (Buf, L));
               Emit (S, P, O3, Out_Q);
            end if;
            for T in Got'Range loop
               if Got (T) then
                  declare
                     It : constant In_Item := M.Items (T);
                  begin
                     if not Holds (R, It.Key) then
                        Add (R, It.Key, Raw (It.Off .. It.Off + It.Len - 1));
                     end if;
                     Delivered := Delivered + 1;
                  end;
               end if;
            end loop;
            Emit (S, P, O2, Out_Q);
         end loop;
         In_Q.Clear;
         --  The initiator, with nothing open in Auth: go to the data range.
         if Sess.R = Initiator and then Sess.P = Auth and then Open_Count (Sess) = 0 then
            Next_Phase (Sess, S, P, F, G, R_Eff, 1, O2, St);
            if St /= S_OK then
               All_OK := False;
            end if;
            Emit (S, P, O2, Out_Q);
         end if;
      end Deliver_All;

   begin
      All_OK := True;
      Rounds := 0;
      Delivered := 0;
      Snap (A, SA);
      Snap (B, SB);
      declare
         PA : constant Prefix := Table_Of (SA);
         PB : constant Prefix := Table_Of (SB);
      begin
         Start (Sess_A, Initiator, NS_X, DH2, F, Auth_T, Buf, L);
         To_B.Append (Slice (Buf, L));
         Start (Sess_B, Responder, NS_X, DH1, F, Auth_T, Buf, L);
         if L /= 0 then
            All_OK := False;
         end if;
         while not To_B.Is_Empty or else not To_A.Is_Empty loop
            if not To_B.Is_Empty then
               Rounds := Rounds + 1;
               Deliver_All (B, SB, PB, Sess_B, To_B, To_A);
            end if;
            if not To_A.Is_Empty then
               Rounds := Rounds + 1;
               Deliver_All (A, SA, PA, Sess_A, To_A, To_B);
            end if;
            exit when Rounds > 100;
         end loop;
      end;
      Both_Complete := Complete (Sess_A) and then Complete (Sess_B);
   end Run_Session;

   procedure Run_All;

   --  A State has a Register_File of Writers_Max keys (256 KiB), and the
   --  snapshots and tables hold their pools. Under -gnata, each Post
   --  evaluation copies them, so the checks run in a task with a large
   --  stack (as in test_views and test_guard).
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
      Small : Snapshot (Cap => 64, Pool_Cap => 300_000);
      St    : Snap_Status;
      --  The fixture frontier: the founding roster is ROSTER_eff.
      F      : State := Empty (NS_X, Fnd, 64, 16);
      Auth_T : Frame_Table (Cap => 32, Pool_Cap => 65_536);
      G      : Guard_State;
   begin
   Must_Apply (F, RH);
   Clear_Table (Auth_T);
   Must_Add (Auth_T, Cred_T);
   Check ("fixture: the founding roster is ROSTER_eff and lists DH1 and DH2",
          Roster_Eff (F) = (Present => True, Hdr => RH)
          and then Gate (F, R_Eff, DH1) and then Gate (F, R_Eff, DH2)
          and then not Gate (F, R_Eff, DHX)
          and then Is_Roster_Frame (Cred_T) and then Roster_Lists_DH (Cred_T, DH1)
          and then not Roster_Lists_DH (Cred_T, DHX));

   ----------------------------------------------------------------------
   --  (a) Key order.
   ----------------------------------------------------------------------
   declare
      A : constant Elem_Key := EK (0, 9, 9, 9);
      B : constant Elem_Key := EK (3, 1, 1, 1);
      C : constant Elem_Key := EK (3, 1, 1, 2);
      D : constant Elem_Key := EK (3, 1, 2, 0);
      P : constant Elem_Key := EK (4, 0, 0, 0);
   begin
      Lemma_Key_Lt_Irrefl (A);
      Lemma_Key_Lt_Trans (A, B, C);
      Lemma_Key_Lt_Asym (B, C);
      Lemma_Key_Trichotomy (C, D);
      Lemma_Key_Le_Lt_Trans (B, B, C);
      Check ("kind decides first (rosters sort first)", Key_Lt (A, B));
      Check ("h decides last", Key_Lt (B, C) and then not Key_Lt (C, B));
      Check ("field before h", Key_Lt (C, D));
      Check ("Min_Key <= every key < Max_Key",
             Key_Le (Min_Key, A) and then Key_Lt (D, Max_Key) and then Key_Lt (P, Max_Key));
      Check ("Data_Lo splits: authorization kinds below, DEL and PUT at or above",
             Key_Lt (EK (2, 255, 255, 255), Data_Lo) and then Key_Le (Data_Lo, B)
             and then Key_Le (Data_Lo, P) and then Key_Lt (Min_Key, Data_Lo));
      Check ("Data_Lo is 03 followed by 80 zero bytes",
             To_Wire (Data_Lo) = [3] & [1 .. 80 => 0]);
   end;
   --  Key_Lt is bytewise order on the 81-byte wire key.
   declare
      Keys : constant array (1 .. 12) of Elem_Key :=
        [EK (0, 0, 0, 0), EK (0, 0, 0, 1), EK (0, 1, 0, 0), EK (1, 0, 9, 9),
         EK (2, 7, 7, 7), EK (3, 7, 7, 7), EK (3, 7, 8, 0), EK (4, 0, 0, 0),
         (K => 3, Ent => (W0 => 1, others => 0), FH => (others => 0), H => (others => 0)),
         (K => 3, Ent => (others => 0), FH => (W7 => 5, others => 0), H => (others => 0)),
         (K => 3, Ent => (others => 0), FH => (others => 0), H => (W0 => 16#FF00_0000#, others => 0)),
         Max_Key];
      Ok_Lt : Boolean := True;
      Ok_Eq : Boolean := True;
   begin
      for X of Keys loop
         for Y of Keys loop
            declare
               WX : constant Key_Wire := To_Wire (X);
               WY : constant Key_Wire := To_Wire (Y);
            begin
               Kome.Reconcile.Lemma_Key_Eq_Is_Bytewise (WX, WY);
               if Wire_Key (WX, 0) /= X or else Wire_Key (WY, 0) /= Y then
                  Ok_Eq := False;
               end if;
               if Key_Lt (X, Y) /= (WX < WY) or else (X = Y) /= (WX = WY) then
                  Ok_Lt := False;
               end if;
               if WX /= WY then
                  for I in Key_Wire'Range loop
                     if WX (I) /= WY (I) then
                        Lemma_Key_Lt_First_Difference (WX, WY, I);
                        exit;
                     end if;
                  end loop;
               end if;
            end;
         end loop;
      end loop;
      Check ("Wire_Key reads back the encoded key", Ok_Eq);
      Check ("Key_Lt is bytewise order on the wire key (144 pairs)", Ok_Lt);
   end;

   ----------------------------------------------------------------------
   --  (b) Snapshots.
   ----------------------------------------------------------------------
   Clear (Small);
   Append (Small, EK (3, 2, 2, 2), Frame_Of (10, 1), St);
   Check ("append first", St = Snap_OK and then Kome.Reconcile.Count (Small) = 1
          and then Frame_Bytes (Small) = 10 and then Source (Small, 1) = 1);
   Append (Small, EK (3, 1, 1, 1), Frame_Of (10, 1), St);
   Check ("append out of order refused, unchanged",
          St = Snap_Unsorted and then Kome.Reconcile.Count (Small) = 1);
   Append (Small, EK (3, 2, 2, 2), Frame_Of (10, 1), St);
   Check ("append duplicate refused", St = Snap_Unsorted);
   Append (Small, EK (5, 9, 9, 9), Frame_Of (10, 1), St);
   Check ("append kind 5 refused", St = Snap_Bad_Kind);
   Append (Small, EK (4, 1, 1, 1), Frame_Of (10, 1), St);
   Check ("append a PUT (kind 4)", St = Snap_OK and then Kome.Reconcile.Count (Small) = 2);
   Append (Small, EK (4, 3, 3, 3), Frame_Of (Frame_Ship_Max + 1, 1), St);
   Check ("append frame over Frame_Ship_Max refused", St = Snap_Too_Large);
   Append (Small, EK (4, 3, 3, 3), No_Bytes, St);
   Check ("append empty frame refused", St = Snap_Too_Large);
   Lemma_Frame_Ships (Kome.Records.Frame_Max);
   Append (Small, EK (4, 3, 3, 3), Frame_Of (Kome.Records.Frame_Max, 9), St);
   Check ("append a frame of Kome.Records.Frame_Max = 41 136 bytes",
          St = Snap_OK and then Frame (Small, 3) = Frame_Of (41_136, 9));
   Append (Small, EK (4, 4, 4, 4), Frame_Of (Frame_Ship_Max, 7), St);
   Check ("append frame of exactly Frame_Ship_Max",
          St = Snap_OK and then Kome.Reconcile.Count (Small) = 4
          and then Frame (Small, 4) = Frame_Of (Frame_Ship_Max, 7));
   declare
      Tiny : Snapshot (Cap => 1, Pool_Cap => 5);
   begin
      Clear (Tiny);
      Append (Tiny, EK (3, 1, 1, 1), Frame_Of (6, 1), St);
      Check ("append beyond the pool refused", St = Snap_No_Space and then Kome.Reconcile.Count (Tiny) = 0);
      Append (Tiny, EK (3, 1, 1, 1), Frame_Of (5, 1), St);
      Append (Tiny, EK (3, 2, 1, 1), Frame_Of (1, 1), St);
      Check ("append beyond Cap refused", St = Snap_No_Space and then Kome.Reconcile.Count (Tiny) = 1);
   end;
   --  Seal and the prefix-sum fingerprint (D15): on 70 elements (one full
   --  block and a tail), Fingerprint_Of is Range_Fp on every window
   --  (its Post), and Seal keeps the elements.
   declare
      Big : Snapshot (Cap => 128, Pool_Cap => 8_192);
      FP  : Hash256;
      Ok  : Boolean := True;
      type Win is record
         A : Positive;
         B : Natural;
      end record;
      Windows : constant array (1 .. 10) of Win :=
        [(1, 0), (5, 4), (1, 1), (1, 64), (2, 65), (60, 70), (64, 64), (65, 70), (33, 40), (71, 70)];
   begin
      Fill (Big, 70, 8);
      declare
         PB : constant Prefix := Table_Of (Big);
      begin
         Check ("Seal: a table of Prefix_Slots (70) = 2 slots", PB.Slots = 2 and then Prefix_Slots (70) = 2);
         --  Windows across the block boundary (64), at the ends, empty and
         --  full. (Each call also runs the Pre Sealed and the Post Range_Fp
         --  under -gnata, which recompute sums from the start.)
         for W of Windows loop
            Fingerprint_Of (Big, PB, W.A, W.B, FP);
            Ok := Ok and then FP = Range_Fp (Big, W.A, W.B);
         end loop;
         Check ("Fingerprint_Of (prefix sums) = Range_Fp on windows of 70 elements", Ok);
         Fingerprint_Of (Big, PB, 1, 70, FP);
         Check ("the full fingerprint is the digest of the list",
                FP = Kome.Digest.Fingerprint (Kome.Digest.Digest_Of
                       ([for I in 1 .. 70 => Key (Big, I).H])));
      end;
   end;

   ----------------------------------------------------------------------
   --  (c) Windows.
   ----------------------------------------------------------------------
   Fill (Small, 10, 20);
   declare
      W1 : constant Span := Window (Small, Min_Key, Max_Key);
      W2 : constant Span := Window (Small, Key (Small, 3), Key (Small, 7));
      W3 : constant Span := Window (Small, EK (3, 3, 3, 4), EK (3, 3, 3, 5));
      W4 : constant Span := Window (Small, EK (3, 3, 3, 4), EK (3, 6, 0, 0));
      W5 : constant Span := Window (Small, Min_Key, Data_Lo);
   begin
      Check ("window of the whole range", W1.First = 1 and then W1.Last = 10);
      Check ("window [k3, k7) is 3 .. 6", W2.First = 3 and then W2.Last = 6);
      Check ("empty window between two keys", W3.Last + 1 = W3.First);
      Check ("window between keys is 4 .. 5", W4.First = 4 and then W4.Last = 5);
      Check ("no DEL in the authorization range", W5.Last + 1 = W5.First);
      Check ("count of [k3, k7) is 4", Cnt (Small, Key (Small, 3), Key (Small, 7)) = 4);
      Lemma_Child (Small, Min_Key, Max_Key, 1, 10, 4, 6);
      Lemma_My_Count (Small, Key (Small, 3), Key (Small, 7), 3, 6);
      Check ("child bounds of run 4 .. 6",
             Child_Lo (Small, Min_Key, 1, 4) = Key (Small, 4)
             and then Child_Hi (Small, Max_Key, 10, 6) = Key (Small, 7));
   end;

   ----------------------------------------------------------------------
   --  (d) Encoding.
   ----------------------------------------------------------------------
   declare
      PS  : constant Prefix := Table_Of (Small);
      Buf : Msg_Buffer;
      L   : Msg_Length;
      M   : Message;
      OK  : Boolean;
      P   : Plan;
   begin
      P := (Kind => P_Range, Lo => Key (Small, 2), Hi => Key (Small, 9),
            First => 2, Last => 8, N => 0, Items => [others => 1]);
      Encode (Small, PS, P, 3, Buf, L);
      Lemma_Range_Accepted (Small, P, 3, Buf);
      Decode (Slice (Buf, L), M, OK);
      Check ("RANGE is 200 bytes", L = Range_Len and then L = 200);
      Check ("RANGE round trip",
             OK and then M.Kind = M_Range and then M.Lo = P.Lo and then M.Hi = P.Hi
             and then M.G = 3
             and then M.Count = 7 and then M.Fp = Range_Fp (Small, 2, 8)
             and then Range_Wire_OK (Slice (Buf, L)));

      P := (Kind => P_Elements, Lo => Key (Small, 2), Hi => Key (Small, 6),
            First => 2, Last => 5, N => 0, Items => [others => 1]);
      Encode (Small, PS, P, 1, Buf, L);
      Decode (Slice (Buf, L), M, OK);
      Check ("ELEMENTS length = Plan_Len", L = Plan_Len (Small, P) and then L = 165 + 4 * (85 + 20));
      Check ("ELEMENTS round trip",
             OK and then M.Kind = M_Elements and then M.N = 4
             and then M.Items (1).Key = Key (Small, 2)
             and then M.Items (4).Key = Key (Small, 5)
             and then Buf (M.Items (3).Off .. M.Items (3).Off + M.Items (3).Len - 1)
                      = Frame (Small, 4));

      P := (Kind => P_Have, Lo => Min_Key, Hi => Max_Key,
            First => 1, Last => 0, N => 0, Items => [others => 1]);
      Encode (Small, PS, P, 2, Buf, L);
      Lemma_Confirm_Accepted (Small, P, 2, Buf);
      Decode (Slice (Buf, L), M, OK);
      Check ("confirm (empty HAVE) round trip",
             OK and then L = Elems_Fixed and then M.Kind = M_Have and then M.N = 0
             and then M.G = 2 and then Empty_Wire_OK (Slice (Buf, L)));

      P := (Kind => P_Have, Lo => Min_Key, Hi => Max_Key,
            First => 1, Last => 0, N => 2, Items => [1, 7, 1, 1]);
      Encode (Small, PS, P, 1, Buf, L);
      Decode (Slice (Buf, L), M, OK);
      Check ("HAVE round trip",
             OK and then M.Kind = M_Have and then M.N = 2
             and then M.Items (2).Key = Key (Small, 7)
             and then L = Plan_Len (Small, P));

      --  Malformed inputs.
      Decode (Buf (0 .. L - 2), M, OK);
      Check ("truncated HAVE refused", not OK);
      Decode (Buf (0 .. L), M, OK);
      Check ("HAVE with a trailing byte refused", not OK);
      declare
         B2 : Msg_Buffer := Buf;
      begin
         B2 (0) := 9;
         Decode (Slice (B2, L), M, OK);
         Check ("unknown tag refused", not OK);
         B2 := Buf;
         B2 (0) := Tag_Open;
         Decode (Slice (B2, L), M, OK);
         Check ("Decode refuses the OPEN tag", not OK);
         B2 := Buf;
         B2 (Elems_O_N) := 5;
         Decode (Slice (B2, L), M, OK);
         Check ("more than Ship_Threshold items refused", not OK);
         B2 := Buf;
         B2 (O_G) := 17;
         Decode (Slice (B2, L), M, OK);
         Check ("group size above Split_Fanout refused", not OK);
      end;
      --  Items out of order: HAVE [7, 1] is not ascending.
      declare
         B2 : Msg_Buffer := Buf;
         Item : constant Natural := 85 + 20;
      begin
         B2 (Elems_Fixed .. Elems_Fixed + Item - 1) := Buf (Elems_Fixed + Item .. Elems_Fixed + 2 * Item - 1);
         B2 (Elems_Fixed + Item .. Elems_Fixed + 2 * Item - 1) := Buf (Elems_Fixed .. Elems_Fixed + Item - 1);
         Decode (Slice (B2, L), M, OK);
         Check ("descending items refused", not OK);
         B2 := Buf;
         B2 (Elems_Fixed) := 5;
         Decode (Slice (B2, L), M, OK);
         Check ("item of kind 5 refused", not OK);
         B2 := Buf;
         B2 (Elems_Fixed + 81 .. Elems_Fixed + 84) := [0, 0, 0, 0];
         Decode (Slice (B2, L), M, OK);
         Check ("zero frame length refused", not OK);
      end;
      --  lo >= hi.
      P := (Kind => P_Range, Lo => Key (Small, 2), Hi => Key (Small, 9),
            First => 2, Last => 8, N => 0, Items => [others => 1]);
      Encode (Small, PS, P, 1, Buf, L);
      declare
         B2 : Msg_Buffer := Buf;
      begin
         B2 (O_Lo .. O_Lo + 80) := Buf (O_Hi .. O_Hi + 80);
         Decode (Slice (B2, L), M, OK);
         Check ("RANGE with lo = hi refused", not OK);
         B2 := Buf;
         B2 (O_Lo .. O_Lo + 80) := Buf (O_Hi .. O_Hi + 80);
         B2 (O_Hi .. O_Hi + 80) := Buf (O_Lo .. O_Lo + 80);
         Decode (Slice (B2, L), M, OK);
         Check ("RANGE with lo > hi refused", not OK);
         --  An item outside [lo, hi): HAVE over [k2, k3) that lists k5.
         Encode (Small, PS, (Kind => P_Have, Lo => Min_Key, Hi => Max_Key, First => 1,
                         Last => 0, N => 1, Items => [5, 1, 1, 1]), 1, Buf, L);
         Encode (Small, PS, (Kind => P_Range, Lo => Key (Small, 2), Hi => Key (Small, 3),
                         First => 2, Last => 2, N => 0, Items => [others => 1]), 1, B2, L);
         Buf (O_Lo .. Elems_O_N - 1) := B2 (O_Lo .. Elems_O_N - 1);
         Decode (Buf (0 .. Elems_Fixed + 85 + 20 - 1), M, OK);
         Check ("item outside [lo, hi) refused", not OK);
      end;
   end;

   --  OPEN and HELLO round trips at both ends of their ranges.
   declare
      Buf : Msg_Buffer;
      L   : Msg_Length;
      O   : Open_Msg;
      H   : Hello;
      OK  : Boolean;
      RVs : Rv_Array;
      Dg  : constant Hash256 := [for I in 0 .. 31 => Byte (I * 7 mod 256)];
      No_Voids : constant Rv_Array := [others => Zero_Rv];
   begin
      Encode_Open ((Proto => Proto_Version, NS => NS_X, N_RV => 0, RV => No_Voids), Buf, L);
      Decode_Open (Slice (Buf, L), O, OK);
      Check ("OPEN with 0 frames: 19 bytes, round trip",
             OK and then L = 19 and then Open_Wire_OK (Slice (Buf, L))
             and then O.NS = NS_X and then O.N_RV = 0 and then O.Proto = 1
             and then O.RV = No_Voids);
      for I in Rv_Index loop
         RVs (I) := [for J in 0 .. Rv_Frame_Len - 1 => Byte ((I * 31 + J) mod 256)];
      end loop;
      Encode_Open ((Proto => Proto_Version, NS => NS_Y, N_RV => Rv_Max, RV => RVs), Buf, L);
      Decode_Open (Slice (Buf, L), O, OK);
      Check ("OPEN with 15 frames: Open_Max_Len = 4 054 bytes, round trip",
             OK and then L = Open_Max_Len and then L = 4_054
             and then O.NS = NS_Y and then O.N_RV = 15 and then O.RV = RVs);
      Encode_Open ((Proto => Proto_Version, NS => NS_Y, N_RV => 2, RV => RVs), Buf, L);
      Decode_Open (Slice (Buf, L), O, OK);
      Check ("OPEN with 2 frames is canonical: unused frames zero",
             OK and then L = 19 + 2 * 269 and then O.RV (2) = RVs (2)
             and then O.RV (3) = Zero_Rv and then O.RV (15) = Zero_Rv);
      declare
         B2 : Msg_Buffer := Buf;
      begin
         B2 (Open_O_Proto) := 2;
         Decode_Open (Slice (B2, L), O, OK);
         Check ("OPEN with a wrong proto refused", not OK);
         B2 := Buf;
         B2 (Open_O_NRV) := 16;
         Decode_Open (B2 (0 .. 19 + 16 * 269 - 1), O, OK);
         Check ("OPEN with n_rv = 16 refused", not OK);
         Decode_Open (Buf (0 .. L - 2), O, OK);
         Check ("truncated OPEN refused", not OK);
         Decode_Open (Buf (0 .. L), O, OK);
         Check ("OPEN with a trailing byte refused", not OK);
         B2 := Buf;
         B2 (0) := Tag_Hello;
         Decode_Open (Slice (B2, L), O, OK);
         Check ("OPEN with the HELLO tag refused", not OK);
      end;

      Encode_Hello (7, 16#FFFF_FFFF#, Dg, No_Bytes, Buf, L);
      Decode_Hello (Slice (Buf, L), H, OK);
      Check ("HELLO with cred_len 0: 43 bytes, round trip",
             OK and then L = Hello_Fixed and then L = 43
             and then Hello_Wire_OK (Slice (Buf, L))
             and then H.N_Auth = 7 and then H.N_Data = 16#FFFF_FFFF#
             and then H.Digest = Dg and then H.Cred_Len = 0
             and then H.Cred = [0 .. Cred_Max - 1 => 0]);
      Check ("claimed counts enter as min (claimed, Elem_Max)",
             Claim (H.N_Data) = Elem_Max and then Claim (H.N_Auth) = 7);
      declare
         Big : constant Byte_Array (5 .. Cred_Max + 4) :=
           [for I in 5 .. Cred_Max + 4 => Byte (I mod 253)];
      begin
         Encode_Hello (1, 2, Dg, Big, Buf, L);
         Decode_Hello (Slice (Buf, L), H, OK);
         Check ("HELLO with cred_len 10 099: Hello_Max_Len = 10 142 bytes, round trip",
                OK and then L = Hello_Max_Len and then L = 10_142
                and then H.Cred_Len = 10_099 and then H.Cred = Big
                and then H.N_Auth = 1 and then H.N_Data = 2);
      end;
      Encode_Hello (1, 2, Dg, Cred_T, Buf, L);
      declare
         B2 : Msg_Buffer := Buf;
      begin
         Decode_Hello (Buf (0 .. L - 2), H, OK);
         Check ("truncated HELLO refused", not OK);
         Decode_Hello (Buf (0 .. L), H, OK);
         Check ("HELLO with a trailing byte refused", not OK);
         B2 (Hello_O_CLen) := 16#27#;
         B2 (Hello_O_CLen + 1) := 16#74#;    --  10 100 > Cred_Max
         Decode_Hello (B2 (0 .. Hello_Fixed + 10_100 - 1), H, OK);
         Check ("HELLO with cred_len > Cred_Max refused", not OK);
         B2 := Buf;
         B2 (0) := Tag_Open;
         Decode_Hello (Slice (B2, L), H, OK);
         Check ("HELLO with the OPEN tag refused", not OK);
      end;
   end;

   --  Known answers (vectors/reconcile.txt).
   declare
      Path  : constant String := Find ("vectors/reconcile.txt");
      Fl    : File_Type;
      Line  : String (1 .. 20_000);
      Last  : Natural;
      N_Vec : Natural := 0;
      Ok    : Boolean := True;
      Buf   : Msg_Buffer;
      L     : Msg_Length;
      type Bounds is record
         First, Last : Natural;
      end record;
      Fields   : array (1 .. 8) of Bounds;
      N_Fields : Natural;

      procedure Tokenize (S : String) is
         I : Natural := S'First;
      begin
         N_Fields := 0;
         while I <= S'Last and then N_Fields < Fields'Last loop
            while I <= S'Last and then S (I) = ' ' loop
               I := I + 1;
            end loop;
            exit when I > S'Last;
            N_Fields := N_Fields + 1;
            Fields (N_Fields).First := I;
            while I <= S'Last and then S (I) /= ' ' loop
               I := I + 1;
            end loop;
            Fields (N_Fields).Last := I - 1;
         end loop;
      end Tokenize;

      function Field (K : Positive) return String is
        (Line (Fields (K).First .. Fields (K).Last));
   begin
      if not Ada.Directories.Exists (Path) then
         Check ("vectors present (" & Path & ")", False);
      else
         Open (Fl, In_File, Path);
         while not End_Of_File (Fl) loop
            Get_Line (Fl, Line, Last);
            if Last > 0 and then Line (1) /= '#' then
               Tokenize (Line (1 .. Last));
               if Field (1) = "open" and then N_Fields = 4 then
                  declare
                     NSB  : constant Byte_Array := From_Hex (Field (2));
                     Fr   : constant Byte_Array := From_Hex (Field (3));
                     Want : constant Byte_Array := From_Hex (Field (4));
                     RVs  : Rv_Array := [others => Zero_Rv];
                     N    : constant Natural := Fr'Length / Rv_Frame_Len;
                     O    : Open_Msg;
                     OK   : Boolean;
                  begin
                     N_Vec := N_Vec + 1;
                     for I in 1 .. N loop
                        RVs (I) := Fr (Fr'First + Rv_Frame_Len * (I - 1)
                                       .. Fr'First + Rv_Frame_Len * I - 1);
                     end loop;
                     Encode_Open ((Proto => Proto_Version,
                                   NS    => Kome.Keys.To_Id128 (NSB),
                                   N_RV  => N, RV => RVs), Buf, L);
                     Decode_Open (Want, O, OK);
                     if Slice (Buf, L) /= Want or else not OK or else O.N_RV /= N
                       or else O.NS /= Kome.Keys.To_Id128 (NSB)
                     then
                        Ok := False;
                        Put_Line ("  mismatch: open " & Field (2));
                     end if;
                  end;
               elsif Field (1) = "hello" and then N_Fields = 6 then
                  declare
                     NA   : constant Word := Word'Value (Field (2));
                     ND   : constant Word := Word'Value (Field (3));
                     Dg   : constant Byte_Array := From_Hex (Field (4));
                     Cr   : constant Byte_Array := From_Hex (Field (5));
                     Want : constant Byte_Array := From_Hex (Field (6));
                     H    : Hello;
                     OK   : Boolean;
                  begin
                     N_Vec := N_Vec + 1;
                     Encode_Hello (NA, ND, Dg, Cr, Buf, L);
                     Decode_Hello (Want, H, OK);
                     if Slice (Buf, L) /= Want or else not OK or else H.N_Auth /= NA
                       or else H.N_Data /= ND or else H.Cred_Len /= Cr'Length
                     then
                        Ok := False;
                        Put_Line ("  mismatch: hello " & Field (2));
                     end if;
                  end;
               end if;
            end if;
         end loop;
         Close (Fl);
         Check ("OPEN and HELLO match the known answers (" & N_Vec'Image & " vectors)",
                Ok and then N_Vec >= 4);
      end if;
   end;

   ----------------------------------------------------------------------
   --  (e) The responder and the reply contract.
   ----------------------------------------------------------------------
   Fill (Small, 40, 20);
   declare
      PS  : constant Prefix := Table_Of (Small);
      M   : Message;
      O   : Outbox;
      Got : Delivery;
      Mut : Outbox;
   begin
      M := Msg (M_Range, Min_Key, Max_Key, 40, Range_Fp (Small, 1, 40));
      Respond (Small, PS, M, O, Got);
      Check ("equal fingerprint: an explicit confirm, nothing delivered",
             Is_Confirm (O, Min_Key, Max_Key) and then O.Reply
             and then Got = No_Delivery and then Plans_Fit (Small, O)
             and then Answers_T (Small, M, O));

      M.Count := 39;
      Respond (Small, PS, M, O, Got);
      Check ("40 elements, mismatch: 16-way split",
             O.N = 16 and then Tiles (O, Min_Key, Max_Key) and then Plans_Fit (Small, O)
             and then All_Kind (O, P_Range) and then Exact_Plans (Small, O)
             and then Answers_T (Small, M, O));
      --  A mutant: an empty HAVE for every mismatched RANGE. It violates
      --  the reply contract.
      Mut := O;
      Mut.N := 1;
      Mut.P (1) := Confirm_Plan (Min_Key, Max_Key);
      Check ("empty-HAVE mutant to a mismatched RANGE violates the contract",
             not Confirms (Small, M) and then not Answers_T (Small, M, Mut)
             and then not All_Kind (Mut, P_Range) and then not All_Kind (Mut, P_Elements));
      declare
         Ok : Boolean := O.P (1).Lo = Min_Key and then O.P (16).Hi = Max_Key;
         Sum : Natural := 0;
      begin
         for T in 1 .. O.N loop
            Lemma_Exact_Plan (Small, O, T);
            Ok := Ok and then O.P (T).Kind = P_Range
                  and then Cnt (Small, O.P (T).Lo, O.P (T).Hi) < 40
                  and then Cnt (Small, O.P (T).Lo, O.P (T).Hi) >= 1;
            Sum := Sum + Cnt (Small, O.P (T).Lo, O.P (T).Hi);
            if T > 1 then
               Ok := Ok and then O.P (T - 1).Hi = O.P (T).Lo;
            end if;
         end loop;
         Check ("children partition the range, each strictly smaller",
                Ok and then Sum = 40 and then Num_Ranges (O) = 16
                and then Obligations (O) = 16 and then Item_Bytes (Small, O) = 0);
      end;

      --  A mutant whose child RANGE carries a run that is not its window.
      Mut := O;
      Mut.P (2).Last := Mut.P (2).Last - 1;
      Check ("a child with a short run is not exact", not Exact_Plans (Small, Mut));

      M := Msg (M_Range, Key (Small, 5), Key (Small, 9));
      Respond (Small, PS, M, O, Got);
      Check ("4 elements, mismatch: one ELEMENTS",
             O.N = 1 and then O.P (1).Kind = P_Elements
             and then O.P (1).First = 5 and then O.P (1).Last = 8
             and then Item_Bytes (Small, O) = 4 * (85 + 20)
             and then Plans_Fit (Small, O) and then Answers_T (Small, M, O));
      Mut := O;
      Mut.P (1) := Confirm_Plan (Key (Small, 5), Key (Small, 9));
      Check ("empty-HAVE mutant to a small mismatched RANGE violates the contract",
             not Answers_T (Small, M, Mut));

      M := Msg (M_Range, Key (Small, 5), Key (Small, 11));
      Respond (Small, PS, M, O, Got);
      Check ("6 elements, mismatch: split into 6 singletons",
             O.N = 6 and then Tiles (O, Key (Small, 5), Key (Small, 11))
             and then (for all T in 1 .. 6 => O.P (T).Kind = P_Range
                                 and then O.P (T).First = O.P (T).Last)
             and then Plans_Fit (Small, O) and then Answers_T (Small, M, O));

      --  A mismatched RANGE over an empty window: an empty ELEMENTS.
      M := Msg (M_Range, EK (3, 5, 5, 6), EK (3, 6, 0, 0), 1);
      Respond (Small, PS, M, O, Got);
      Check ("mismatch over an empty window: one empty ELEMENTS, exact",
             O.N = 1 and then O.P (1).Kind = P_Elements
             and then O.P (1).Last + 1 = O.P (1).First
             and then Answers_T (Small, M, O));

      --  ELEMENTS from the peer that lists k5 and a key that we do not
      --  have. We hold k5 .. k8 in the range, so HAVE answers k6, k7, k8,
      --  and the unknown key is delivered.
      M := Msg (M_Elements, Key (Small, 5), Key (Small, 9));
      M.N := 2;
      M.Items := [(Key => Key (Small, 5), Off => 0, Len => 1),
                  (Key => EK (3, 6, 0, 0), Off => 0, Len => 1),
                  others => <>];
      Respond (Small, PS, M, O, Got);
      Check ("ELEMENTS: exactly the key we lack is delivered",
             Got = [False, True, False, False]);
      Check ("ELEMENTS: HAVE answers exactly what the peer lacked",
             O.N = 1 and then O.P (1).Kind = P_Have and then O.P (1).N = 3
             and then O.P (1).Items (1) = 6 and then O.P (1).Items (3) = 8
             and then Have_Exact (Small, M, O)
             and then Plans_Fit (Small, O) and then Answers_T (Small, M, O));
      Mut := O;
      Mut.P (1) := Confirm_Plan (Key (Small, 5), Key (Small, 9));
      Check ("empty-HAVE mutant to ELEMENTS (peer lacks 3) violates the contract",
             not Answers_T (Small, M, Mut));

      M.Kind := M_Have;
      Respond (Small, PS, M, O, Got);
      Check ("HAVE: delivered, never answered",
             O.N = 0 and then Got = [False, True, False, False]
             and then Answers_T (Small, M, O));

      --  ELEMENTS that lists all that we hold in the range: an empty HAVE.
      M := Msg (M_Elements, Key (Small, 5), Key (Small, 7));
      M.N := 2;
      M.Items := [(Key => Key (Small, 5), Off => 0, Len => 1),
                  (Key => Key (Small, 6), Off => 0, Len => 1),
                  others => <>];
      Respond (Small, PS, M, O, Got);
      Check ("ELEMENTS with nothing missing either way: confirm, nothing delivered",
             Is_Confirm (O, Key (Small, 5), Key (Small, 7))
             and then Got = No_Delivery and then Plans_Fit (Small, O));

      --  ELEMENTS over a range where we hold more than Ship_Threshold:
      --  the split, never a HAVE.
      M := Msg (M_Elements, Min_Key, Max_Key);
      Respond (Small, PS, M, O, Got);
      Check ("ELEMENTS where we hold 40: a split, all RANGE, exact",
             O.N = 16 and then All_Kind (O, P_Range) and then Answers_T (Small, M, O));
   end;

   --  Large frames: three of 20 000 bytes do not fit one message.
   Fill (Small, 3, 20_000);
   declare
      PS  : constant Prefix := Table_Of (Small);
      M   : Message;
      O   : Outbox;
      Got : Delivery;
   begin
      M := Msg (M_Range, Min_Key, Max_Key);
      Respond (Small, PS, M, O, Got);
      Check ("ELEMENTS too large for one message: one per element",
             O.N = 3 and then (for all T in 1 .. 3 => O.P (T).Kind = P_Elements
                                 and then O.P (T).First = T and then O.P (T).Last = T)
             and then O.P (1).Lo = Min_Key and then O.P (3).Hi = Max_Key
             and then O.P (1).Hi = O.P (2).Lo and then O.P (2).Hi = O.P (3).Lo
             and then Plans_Fit (Small, O) and then Answers_T (Small, M, O));
      M.Kind := M_Elements;
      Respond (Small, PS, M, O, Got);
      Check ("HAVE too large for one message: one per element",
             O.N = 3 and then (for all T in 1 .. 3 => O.P (T).Kind = P_Have
                                 and then O.P (T).N = 1)
             and then Have_Exact (Small, M, O)
             and then Plans_Fit (Small, O));
   end;
   --  Two frames of Frame_Ship_Max: each frame alone is exactly
   --  Max_Message_Len. Also, the largest well-formed frame ships.
   Clear (Small);
   Append (Small, EK (3, 1, 1, 1), Frame_Of (Frame_Ship_Max, 1), St);
   Append (Small, EK (4, 2, 2, 2), Frame_Of (Frame_Ship_Max, 2), St);
   Append (Small, EK (4, 3, 3, 3), Frame_Of (Kome.Records.Frame_Max, 3), St);
   declare
      PS  : constant Prefix := Table_Of (Small);
      M   : Message;
      O   : Outbox;
      Got : Delivery;
      Buf : Msg_Buffer;
      L   : Msg_Length;
      OK  : Boolean;
   begin
      M := Msg (M_Range, Min_Key, Max_Key);
      Respond (Small, PS, M, O, Got);
      Encode (Small, PS, O.P (1), Group (O), Buf, L);
      Check ("largest frame ships in a message of exactly Max_Message_Len",
             O.N = 3 and then L = Max_Message_Len and then Plans_Fit (Small, O));
      Encode (Small, PS, O.P (3), Group (O), Buf, L);
      Decode (Slice (Buf, L), M, OK);
      Check ("a 41 136-byte frame ships in one ELEMENTS",
             OK and then M.N = 1 and then M.Items (1).Len = 41_136
             and then Buf (M.Items (1).Off .. M.Items (1).Off + 41_135)
                      = Frame_Of (41_136, 3));
   end;

   ----------------------------------------------------------------------
   --  (f) Frame tables and Snapshot_Of (A12).
   ----------------------------------------------------------------------
   declare
      --  F4: the founding roster, a GRANT of author A2, three PUTs, one
      --  DEL, and a GRANT by a certified root 8 (its own slot). The data
      --  row is in application order, the authorization rows slot by
      --  slot.
      A2     : constant Key256 := KeyB (2);
      F4     : State := Empty (NS_X, Fnd, 16, 8);
      Data_T : Frame_Table (Cap => 16, Pool_Cap => 4_096);
      Aut_T  : Frame_Table (Cap => 16, Pool_Cap => 4_096);
      S4     : Snapshot (Cap => 16, Pool_Cap => 8_192);
      Res    : Snap_Status;
      Ok     : Boolean := True;
      GH     : constant Header := Grant_H (Fnd, A2, 11);
      G8     : constant Header := Grant_H (KeyB (8), A2, 12);
      P1     : constant Header := Put_H (5, 1, 100, A2, 1, 21);
      P2     : constant Header := Put_H (3, 1, 100, A2, 2, 22);
      P3     : constant Header := Put_H (3, 2, 100, A2, 3, 23);
      D1     : constant Header := Del_H (9, 100, A2, 4, 24);
   begin
      Must_Apply (F4, RH);
      Must_Apply (F4, GH);
      Must_Apply (F4, G8);
      Must_Apply (F4, P1);
      Must_Apply (F4, P2);
      Must_Apply (F4, P3);
      Must_Apply (F4, D1);
      Check ("F4 holds 4 data and 3 authorization records",
             Data_Count (F4) = 4 and then Auth_Count (F4) = 3
             and then Kome.Frontier.Count (F4) = 7 and then Slots_Used (F4) = 2);
      --  The tables: entry I is the frame of Data_Held (F4, I), and of the
      --  I-th authorization record. The frames are synthetic (opaque).
      Clear_Table (Data_T);
      for I in 1 .. Data_Count (F4) loop
         Must_Add (Data_T, Frame_Of (30 + I, Byte (Data_Held (F4, I).V.H.W0 mod 256)));
      end loop;
      Clear_Table (Aut_T);
      for I in 1 .. Auth_Count (F4) loop
         Must_Add (Aut_T, Frame_Of (300 + I, Byte (Held (F4, Data_Count (F4) + I).V.H.W0 mod 256)));
      end loop;
      Check ("tables: counts, lengths and frames",
             Table_Count (Data_T) = 4 and then Table_Count (Aut_T) = 3
             and then Table_Len (Data_T, 3) = 33 and then Table_Frame (Aut_T, 2) = Frame_Of (302, 11)
             and then Table_Bytes (Data_T) = 31 + 32 + 33 + 34);
      Snapshot_Of (F4, Data_T, Aut_T, S4, Res);
      Check ("Snapshot_Of: OK, |S| = |F|", Res = Snap_OK
             and then Kome.Reconcile.Count (S4) = 7 and then Valid (S4)
             and then Frame_Bytes (S4) = Table_Bytes (Data_T) + Table_Bytes (Aut_T));
      for I in 1 .. Kome.Reconcile.Count (S4) loop
         Ok := Ok and then Key (S4, I) = Key_Of (Held (F4, Source (S4, I)))
               and then Frame (S4, I) = Record_Frame (F4, Data_T, Aut_T, Source (S4, I));
         if I > 1 then
            Ok := Ok and then Key_Lt (Key (S4, I - 1), Key (S4, I));
         end if;
      end loop;
      Check ("Snapshot_Of: each element is a held record with its frame, in key order", Ok);
      Check ("Snapshot_Of: authorization records first, then DEL, then PUTs",
             Key (S4, 1).K = 0 and then Key (S4, 2).K = 2 and then Key (S4, 3).K = 2
             and then Key (S4, 4).K = 3 and then Key (S4, 5).K = 4 and then Key (S4, 7).K = 4
             and then Key (S4, 4) = Key_Of (D1)
             and then Key (S4, 5) = Key_Of (P2) and then Key (S4, 6) = Key_Of (P3)
             and then Key (S4, 7) = Key_Of (P1));
      Check ("Snapshot_Of: the sources are distinct",
             (for all I in 1 .. 7 => (for all J in 1 .. 7 =>
                (if I /= J then Source (S4, I) /= Source (S4, J)))));
      Check ("Snapshot_Of: the digest of S is Frontier_Digest (F) (T6)",
             Range_Fp (S4, 1, 7) = Kome.Digest.Frontier_Digest (F4));
      declare
         P4 : constant Prefix := Table_Of (S4);
         FP : Hash256;
      begin
         Fingerprint_Of (S4, P4, 1, 7, FP);
         Check ("the prefix sums of the snapshot of F give its digest",
                FP = Kome.Digest.Frontier_Digest (F4));
         Fingerprint_Of (S4, P4, 4, 7, FP);
         Check ("the data range fingerprint from the prefix sums",
                FP = Range_Fp (S4, 4, 7) and then Cnt (S4, Data_Lo, Max_Key) = 4);
      end;
      --  Refusals: too few elements, too small a pool.
      declare
         S5 : Snapshot (Cap => 6, Pool_Cap => 8_192);
         S6 : Snapshot (Cap => 16, Pool_Cap => 1_000);
      begin
         Snapshot_Of (F4, Data_T, Aut_T, S5, Res);
         Check ("Snapshot_Of: Cap below |F| is Snap_No_Space, S empty",
                Res = Snap_No_Space and then Kome.Reconcile.Count (S5) = 0);
         Snapshot_Of (F4, Data_T, Aut_T, S6, Res);
         Check ("Snapshot_Of: a pool below the frames is Snap_No_Space",
                Res = Snap_No_Space and then Kome.Reconcile.Count (S6) = 0);
      end;
      --  An empty frontier.
      declare
         F0 : constant State := Empty (NS_X, Fnd, 16, 8);
         T0 : Frame_Table (Cap => 1, Pool_Cap => 16);
         S0 : Snapshot (Cap => 1, Pool_Cap => 16);
      begin
         Clear_Table (T0);
         Snapshot_Of (F0, T0, T0, S0, Res);
         Check ("Snapshot_Of of an empty frontier: OK, empty, digest of the empty set",
                Res = Snap_OK and then Kome.Reconcile.Count (S0) = 0
                and then Range_Fp (S0, 1, 0) = Kome.Digest.Frontier_Digest (F0));
      end;
      --  Two held GRANTs with one key (same h, two issuers): the scan
      --  refuses (Snap_Unsorted), a case no run with distinct hashes makes.
      declare
         F7 : State := Empty (NS_X, Fnd, 16, 8);
         T7 : Frame_Table (Cap => 16, Pool_Cap => 4_096);
         S7 : Snapshot (Cap => 16, Pool_Cap => 8_192);
         E7 : Frame_Table (Cap => 1, Pool_Cap => 16);
      begin
         Must_Apply (F7, Grant_H (Fnd, A2, 50));
         Must_Apply (F7, Grant_H (KeyB (8), A2, 50));
         Clear_Table (T7);
         Must_Add (T7, Frame_Of (40, 1));
         Must_Add (T7, Frame_Of (40, 2));
         Clear_Table (E7);
         Check ("two GRANTs with one key are both held",
                Auth_Count (F7) = 2 and then Key_Of (Held (F7, 1)) = Key_Of (Held (F7, 2)));
         Snapshot_Of (F7, E7, T7, S7, Res);
         Check ("Snapshot_Of refuses two records with one key (Snap_Unsorted), S empty",
                Res = Snap_Unsorted and then Kome.Reconcile.Count (S7) = 0 and then Valid (S7));
      end;
      --  A larger frontier: 40 PUTs in scrambled order (the heap sort on
      --  many elements), with a small pool of 1-byte frames.
      declare
         F8 : State := Empty (NS_X, Fnd, 64, 8);
         T8 : Frame_Table (Cap => 64, Pool_Cap => 4_096);
         A8 : Frame_Table (Cap => 8, Pool_Cap => 4_096);
         S8 : Snapshot (Cap => 64, Pool_Cap => 8_192);
         Ok8 : Boolean := True;
      begin
         Must_Apply (F8, RH);
         Must_Apply (F8, GH);
         for I in 1 .. 40 loop
            Must_Apply (F8, Put_H (Byte ((I * 17) mod 41), Byte ((I * 5) mod 7), 100, A2,
                                   U48 (I), 100 + I));
         end loop;
         Clear_Table (T8);
         for I in 1 .. Data_Count (F8) loop
            Must_Add (T8, Frame_Of (1, Byte (I)));
         end loop;
         Clear_Table (A8);
         Must_Add (A8, Cred_T);
         Must_Add (A8, Frame_Of (200, 9));
         Snapshot_Of (F8, T8, A8, S8, Res);
         for I in 1 .. Kome.Reconcile.Count (S8) loop
            Ok8 := Ok8 and then Key (S8, I) = Key_Of (Held (F8, Source (S8, I)))
                   and then Frame (S8, I) = Record_Frame (F8, T8, A8, Source (S8, I));
            if I > 1 then
               Ok8 := Ok8 and then Key_Lt (Key (S8, I - 1), Key (S8, I));
            end if;
         end loop;
         Check ("Snapshot_Of sorts 42 records (heap sort), frames and digest agree",
                Res = Snap_OK and then Kome.Reconcile.Count (S8) = 42 and then Ok8
                and then Range_Fp (S8, 1, 42) = Kome.Digest.Frontier_Digest (F8)
                and then Frame (S8, 1) = Cred_T);
      end;
   end;

   ----------------------------------------------------------------------
   --  (g) Select_Voids (H5) and Lists_Peer (A14).
   ----------------------------------------------------------------------
   declare
      --  F3: the founding roster, then founding REVOKEs of A (from 0 with
      --  h 5, from 0 with h 3, from 7 with h 1), of B (from 9, h 2) and
      --  of C (from 0, h 4). Slot 1 holds them in this order.
      KA  : constant Key256 := KeyB (31);
      KB  : constant Key256 := KeyB (32);
      KC  : constant Key256 := KeyB (33);
      F3  : State := Empty (NS_X, Fnd, 16, 32);
      T3  : Frame_Table (Cap => 32, Pool_Cap => 65_536);
      V   : Void_Set;
   begin
      Must_Apply (F3, RH);
      Must_Apply (F3, Founding_Revoke (KA, 0, 5));
      Must_Apply (F3, Founding_Revoke (KA, 0, 3));
      Must_Apply (F3, Founding_Revoke (KA, 7, 1));
      Must_Apply (F3, Founding_Revoke (KB, 9, 2));
      Must_Apply (F3, Founding_Revoke (KC, 0, 4));
      Clear_Table (T3);
      Must_Add (T3, Cred_T);
      for I in 2 .. 6 loop
         Must_Add (T3, Rv (Byte (I)));
      end loop;
      Check ("F3: slot 1 holds the roster and 5 founding REVOKEs; A, B, C are root-voided",
             Slot_Count (F3, 1) = 6 and then Root_Void (F3, KA) and then Root_Void (F3, KB)
             and then Root_Void (F3, KC) and then not Root_Void (F3, KeyB (34)));
      V := Select_Voids (F3, T3);
      Lemma_Voids_OK_Def (F3, T3, V);
      Check ("Select_Voids: one frame per subject (3), the least (from_t, h) one",
             V.N_Subj = 3
             and then V.Picked (1) = 3 and then V.Picked (2) = 5 and then V.Picked (3) = 6
             and then Void_Subject (F3, V, 1) = KA and then Void_Subject (F3, V, 2) = KB
             and then Void_Subject (F3, V, 3) = KC
             and then V.RV (1) = Rv (3) and then V.RV (2) = Rv (5) and then V.RV (3) = Rv (6));
      Check ("Select_Voids: the other from_t = 0 REVOKE fills the fourth frame",
             V.N = 4 and then V.Picked (4) = 2 and then V.RV (4) = Rv (2)
             and then Voids_OK (F3, T3, V));
      Lemma_Voids_Cover (F3, T3, V, KA);
      Lemma_Voids_Cover (F3, T3, V, KB);
      Lemma_Voids_Cover (F3, T3, V, KC);
      Check ("Lists_Peer: a member of the roster in the table, not a stranger",
             Lists_Peer (T3, DH1) and then Lists_Peer (T3, DH2) and then not Lists_Peer (T3, DHX));
      Lemma_Lists_Peer_Def (T3, DH1);
      Lemma_Lists_Peer_Def (T3, DHX);
      --  A frame that is not a REVOKE frame is not a candidate.
      declare
         T9 : Frame_Table (Cap => 32, Pool_Cap => 65_536);
         V9 : Void_Set;
      begin
         Clear_Table (T9);
         Must_Add (T9, Cred_T);
         Must_Add (T9, Frame_Of (269, 7));          --  tag 7: not a REVOKE frame
         for I in 3 .. 6 loop
            Must_Add (T9, Rv (Byte (I)));
         end loop;
         V9 := Select_Voids (F3, T9);
         Check ("a slot-1 REVOKE without a REVOKE frame is skipped",
                V9.N_Subj = 3 and then V9.N = 3 and then V9.Picked (1) = 3
                and then not Void_Candidate (F3, T9, 2));
      end;
      --  Seventeen subjects: 15 frames, each a subject, and two subjects
      --  are left out (the bound of the OPEN).
      declare
         F16 : State := Empty (NS_X, Fnd, 16, 32);
         T16 : Frame_Table (Cap => 32, Pool_Cap => 65_536);
         V16 : Void_Set;
         Ok  : Boolean := True;
      begin
         Must_Apply (F16, RH);
         Clear_Table (T16);
         Must_Add (T16, Cred_T);
         for I in 1 .. 17 loop
            Must_Apply (F16, Founding_Revoke (KeyB (40 + I), 0, 60 + I));
            Must_Add (T16, Rv (Byte (I)));
         end loop;
         V16 := Select_Voids (F16, T16);
         for I in 1 .. 15 loop
            Ok := Ok and then V16.Picked (I) = I + 1 and then V16.RV (I) = Rv (Byte (I));
         end loop;
         Check ("17 root-voided subjects: 15 frames, one per subject, in slot order",
                V16.N_Subj = 15 and then V16.N = 15 and then Ok
                and then Voids_OK (F16, T16, V16));
         Lemma_Voids_Cover (F16, T16, V16, KeyB (57));
      end;
   end;

   ----------------------------------------------------------------------
   --  (h) The session state machine.
   ----------------------------------------------------------------------
   --  Small: 3 authorization records (kinds 0, 1, 2) and 6 data records.
   Clear (Small);
   Append (Small, EK (0, 1, 1, 1), Frame_Of (30, 1), St);
   Append (Small, EK (1, 2, 2, 2), Frame_Of (30, 2), St);
   Append (Small, EK (2, 3, 3, 3), Frame_Of (30, 3), St);
   for I in Byte range 4 .. 9 loop
      Append (Small, EK ((if I <= 6 then 3 else 4), I, I, I), Frame_Of (30, I), St);
   end loop;
   Check ("session snapshot: 3 authorization and 6 data records",
          Kome.Reconcile.Count (Small) = 9 and then Cnt (Small, Min_Key, Data_Lo) = 3);
   declare
      PS    : constant Prefix := Table_Of (Small);
      Other : constant Hash256 := [others => 16#EE#];
      Ours  : constant Hash256 := Range_Fp (Small, 1, Kome.Reconcile.Count (Small));
      Sess  : Session (Oblig_Cap => 64);
      Saved : Session (Oblig_Cap => 64);
      O     : Outbox;
      Res   : Session_Status;
      Buf   : Msg_Buffer;
      L     : Msg_Length;
      M     : Message;
      Op    : Open_Msg;
      Peer  : Hello;
      Got   : Delivery;
      OB    : Msg_Buffer;
      OL    : Msg_Length;
      OK    : Boolean;
      Auth_Root : constant Byte_Array :=
        Plan_Bytes (Small, Range_Plan (Small, Min_Key, Data_Lo), 0);
      Data_Root : constant Byte_Array :=
        Plan_Bytes (Small, Range_Plan (Small, Data_Lo, Max_Key), 0);
      Peer_Open : constant Byte_Array := Open_Bytes_Of (NS_X);
   begin
      --  Start: the responder waits; the initiator emits its OPEN.
      Start (Sess, Responder, NS_X, DH1, F, Auth_T, Buf, L);
      Check ("Start (responder): nothing emitted, Await_Open, peer known, no voids",
             L = 0 and then Sess.P = Await_Open and then Sess.Peer_Known
             and then Sess.Our_Open.N_RV = 0 and then Sess.Peer_DH = DH1
             and then Open_Count (Sess) = 0 and then Sess.Gate_Gen = 0);
      Start (Sess, Initiator, NS_X, DH1, F, Auth_T, Buf, L);
      Decode_Open (Slice (Buf, L), Op, OK);
      Check ("Start (initiator) emits our OPEN (ns, no revocations)",
             OK and then Op.NS = NS_X and then Op.N_RV = 0 and then Sess.P = Await_Open
             and then Open_Written (Sess.Our_Open, Buf, L));
      Lemma_Open_Written (Sess.Our_Open, Buf, L);
      --  With root-voids in F, a known peer gets them, a stranger does not.
      declare
         F3  : State := Empty (NS_X, Fnd, 16, 32);
         T3  : Frame_Table (Cap => 32, Pool_Cap => 65_536);
      begin
         Must_Apply (F3, RH);
         Must_Apply (F3, Founding_Revoke (KeyB (31), 0, 5));
         Must_Apply (F3, Founding_Revoke (KeyB (32), 3, 6));
         Clear_Table (T3);
         Must_Add (T3, Cred_T);
         Must_Add (T3, Rv (2));
         Must_Add (T3, Rv (3));
         Start (Sess, Initiator, NS_X, DH2, F3, T3, Buf, L);
         Decode_Open (Slice (Buf, L), Op, OK);
         Check ("Start: the OPEN to a member carries the root-void set (H5)",
                OK and then Op.N_RV = 2 and then Op.RV (1) = Rv (2) and then Op.RV (2) = Rv (3)
                and then Sess.Peer_Known and then L = Open_Len (2));
         Start (Sess, Initiator, NS_X, DHX, F3, T3, Buf, L);
         Decode_Open (Slice (Buf, L), Op, OK);
         Check ("Start: the OPEN to a stranger carries no root-void frame (A14)",
                OK and then Op.N_RV = 0 and then not Sess.Peer_Known and then L = 19);
      end;

      --  A HELLO or a RANGE before the OPEN is refused.
      Start (Sess, Responder, NS_X, DH1, F, Auth_T, Buf, L);
      Saved := Sess;
      Recv (Sess, Small, PS, F, G, 1, Hello_Bytes (Other), O, Res);
      Check ("a HELLO before the gate refused, nothing changes",
             Res = S_Unexpected and then Sess = Saved and then O.N = 0);
      Recv (Sess, Small, PS, F, G, 1, Auth_Root, O, Res);
      Check ("a RANGE before the OPEN refused, nothing changes",
             Res = S_Unexpected and then Sess = Saved);
      Recv (Sess, Small, PS, F, G, 1, No_Bytes, O, Res);
      Check ("empty input refused", Res = S_Malformed and then Sess = Saved);
      declare
         B : Byte_Array := Peer_Open;
      begin
         B (B'First + Open_O_Proto) := 9;
         Recv (Sess, Small, PS, F, G, 1, B, O, Res);
         Check ("an OPEN with a wrong proto refused, nothing changes",
                Res = S_Malformed and then Sess = Saved);
      end;

      --  A foreign ns aborts.
      Receive (Sess, Small, PS, F, G, R_Eff, 1, Open_Bytes_Of (NS_Y), M, Op, Peer, O, Got, OB, OL, Res);
      Check ("an OPEN with a foreign ns aborts the session",
             Res = S_Aborted and then Sess.P = Done and then Sess.Aborted
             and then not Complete (Sess) and then Op.NS = NS_Y and then O.N = 0 and then OL = 0);
      Recv (Sess, Small, PS, F, G, 1, Peer_Open, O, Res);
      Check ("after the abort every message is refused", Res = S_Unexpected);

      --  The OPEN: the responder goes to the gate and answers with its OPEN.
      Start (Sess, Responder, NS_X, DH1, F, Auth_T, Buf, L);
      Receive (Sess, Small, PS, F, G, R_Eff, 1, Peer_Open, M, Op, Peer, O, Got, OB, OL, Res);
      Decode_Open (Slice (OB, OL), Op, OK);
      Check ("our ns: the OPEN opens the gate, and the responder answers with its OPEN (A14)",
             Res = S_OK and then Sess.P = Gate and then Sess.Msgs = 1 and then O.N = 0
             and then OL = 19 and then OK and then Op.NS = NS_X
             and then Open_Written (Sess.Our_Open, OB, OL));
      Saved := Sess;
      Recv (Sess, Small, PS, F, G, 1, Peer_Open, O, Res);
      Check ("a second OPEN refused", Res = S_Unexpected and then Sess = Saved);
      Recv (Sess, Small, PS, F, G, 1, Auth_Root, O, Res);
      Check ("a RANGE in the gate refused (before Auth)",
             Res = S_Unexpected and then Sess = Saved);

      --  The HELLO credential (A13, G12).
      Receive (Sess, Small, PS, F, G, R_Eff, 1, Hello_Bytes (Other, Fill (300, 5)),
               M, Op, Peer, O, Got, OB, OL, Res);
      Check ("a HELLO whose credential is not a roster frame aborts; the credential is not returned",
             Res = S_Aborted and then Sess.P = Done and then Sess.Aborted
             and then Peer = Empty_Hello and then M.Kind = M_Hello and then O.N = 0);
      Sess := Saved;
      Receive (Sess, Small, PS, F, G, R_Eff, 1, Hello_Bytes (Other, No_Bytes),
               M, Op, Peer, O, Got, OB, OL, Res);
      Check ("a HELLO with an empty credential aborts", Res = S_Aborted and then Sess.Aborted);
      Sess := Saved;
      declare
         --  A roster that lists only DH2 and DHX: it does not list DH1.
         Other_Mem : constant Byte_Array := Members_Of (1, 77);
         R_No  : constant Roster_Record :=
           Make_Roster (Root_PK, Salt_A, Root_PK, 0, Zero_Sig, Box_A, 2, 6000, TTL, 2, [],
                        Mem (Member_Len .. 2 * Member_Len - 1) & Other_Mem);
         --  A roster signed by root 8, which F_Void root-voids.
         R8_PK : constant Pubkey := Pubkey (Fill (Pubkey_Len, 8));
         R_8   : constant Roster_Record :=
           Make_Roster (Root_PK, Salt_A, R8_PK, 9000, Sig (Fill (Sig_Len, 2)), Box_A, 3, 7000,
                        TTL, 3, [], Mem);
         F_Void : State := Empty (NS_X, Fnd, 64, 16);
      begin
         Check ("the other roster lists DH2 but not DH1",
                Roster_Lists_DH (Encode (R_No), DH2) and then not Roster_Lists_DH (Encode (R_No), DH1));
         Receive (Sess, Small, PS, F, G, R_Eff, 1, Hello_Bytes (Other, Encode (R_No)),
                  M, Op, Peer, O, Got, OB, OL, Res);
         Check ("a credential that does not list the peer's static key aborts (A13)",
                Res = S_Aborted and then Sess.Aborted and then Peer = Empty_Hello
                and then not Cred_Admissible (F, DH1, Encode (R_No)));
         Sess := Saved;
         Must_Apply (F_Void, RH);
         Must_Apply (F_Void, Founding_Revoke (To_Key256 (R8_PK), 0, 88));
         Check ("F_Void root-voids root 8, whose roster lists DH1",
                Root_Void (F_Void, To_Key256 (R8_PK)) and then Roster_Lists_DH (Encode (R_8), DH1)
                and then Cred_Signer (Encode (R_8)) = To_Key256 (R8_PK)
                and then Cred_Signer (Encode (R_8)) = Signer_Key (Parse_Roster (Encode (R_8)))
                and then Cred_Admissible (F, DH1, Encode (R_8))
                and then not Cred_Admissible (F_Void, DH1, Encode (R_8)));
         Receive (Sess, Small, PS, F_Void, G, R_Eff, 1, Hello_Bytes (Other, Encode (R_8)),
                  M, Op, Peer, O, Got, OB, OL, Res);
         Check ("a credential from a root-voided signer aborts before the decode (G12)",
                Res = S_Aborted and then Sess.P = Done and then Sess.Aborted
                and then Peer = Empty_Hello and then Peer.Cred_Len = 0 and then OL = 0);
         Sess := Saved;
         Receive (Sess, Small, PS, F, G, R_Eff, 1, Hello_Bytes (Other, Encode (R_8)),
                  M, Op, Peer, O, Got, OB, OL, Res);
         Check ("the same credential is accepted where its signer is not root-voided",
                Res = S_OK and then Sess.P = Gate and then Peer.Cred_Len = Encode (R_8)'Length);
         Sess := Saved;
      end;

      --  Responder, receive-then-Admit, different digests.
      Receive (Sess, Small, PS, F, G, R_Eff, 1, Hello_Bytes (Other), M, Op, Peer, O, Got, OB, OL, Res);
      Check ("responder: the peer's HELLO is stored, still in the gate",
             Res = S_OK and then Sess.P = Gate and then Sess.Peer_Hello_Seen
             and then Sess.Peer_Auth = 3 and then Sess.Peer_Data = 4 and then O.N = 0
             and then Peer.Cred_Len = Cred_T'Length and then Peer.Cred (0 .. Cred_T'Length - 1) = Cred_T
             and then OL = 0);
      Saved := Sess;
      Recv (Sess, Small, PS, F, G, 1, Hello_Bytes (Other), O, Res);
      Check ("a second HELLO refused", Res = S_Unexpected and then Sess = Saved);
      Admit (Sess, Small, PS, F, G, R_Eff, 7, Cred_T, Buf, L, O);
      Decode_Hello (Slice (Buf, L), Peer, OK);
      Check ("responder receive-then-Admit: our HELLO, then Auth, nothing to send, Gate_Gen recorded",
             OK and then Sess.P = Auth and then Sess.Hello_Sent and then O.N = 0
             and then Peer.N_Auth = 3 and then Peer.N_Data = 6
             and then Peer.Digest = Ours and then Peer.Cred_Len = Cred_T'Length
             and then Peer.Cred (0 .. Cred_T'Length - 1) = Cred_T
             and then Sess.Budget = Msg_Budget (9, 7) and then Sess.Gate_Gen = 7
             and then Open_Count (Sess) = 0);

      --  The responder in Auth: every wrong g = 0 is refused.
      Saved := Sess;
      Recv (Sess, Small, PS, F, G, 7, Plan_Bytes (Small, Confirm_Plan (Min_Key, Data_Lo), 0), O, Res);
      Check ("responder: a g = 0 HAVE refused, nothing changes",
             Res = S_Unexpected and then Sess = Saved and then O.N = 0);
      Recv (Sess, Small, PS, F, G, 7,
            Plan_Bytes (Small, (Kind => P_Elements, Lo => Min_Key, Hi => Data_Lo,
                                First => 1, Last => 3, N => 0, Items => [others => 1]), 0),
            O, Res);
      Check ("responder: a g = 0 ELEMENTS refused", Res = S_Unexpected and then Sess = Saved);
      Recv (Sess, Small, PS, F, G, 7, Plan_Bytes (Small, Range_Plan (Small, Min_Key, Key (Small, 3)), 0), O, Res);
      Check ("responder: a partial root over [Min_Key, k3) refused",
             Res = S_Unexpected and then Sess = Saved);
      Recv (Sess, Small, PS, F, G, 7, Plan_Bytes (Small, Range_Plan (Small, Min_Key, Max_Key), 0), O, Res);
      Check ("responder: the old whole-space root refused",
             Res = S_Unexpected and then Sess = Saved);
      Recv (Sess, Small, PS, F, G, 7, Data_Root, O, Res);
      Check ("responder: the data root before the authorization root refused",
             Res = S_Unexpected and then Sess = Saved);
      Recv (Sess, Small, PS, F, G, 7, Plan_Bytes (Small, Confirm_Plan (Min_Key, Data_Lo), 1), O, Res);
      Check ("responder: a reply nobody asked for refused (nothing open)",
             Res = S_Unexpected and then Sess = Saved);

      --  The authorization root with a wrong count: we ship our 3, one
      --  obligation.
      declare
         R : Byte_Array := Auth_Root;
      begin
         R (R'First + Range_O_Count + 3) := 2;
         Recv (Sess, Small, PS, F, G, 7, R, O, Res);
         Check ("responder: the authorization root accepted, answered with ELEMENTS",
                Res = S_OK and then Sess.P = Auth and then Sess.Auth_Root_Seen
                and then O.N = 1 and then O.P (1).Kind = P_Elements
                and then O.P (1).Last + 1 - O.P (1).First = 3
                and then Open_Count (Sess) = 1
                and then Kome.Reconcile.Open (Sess, 1) = Fresh (Min_Key, Data_Lo)
                and then not Complete (Sess));
         Saved := Sess;
         Recv (Sess, Small, PS, F, G, 7, R, O, Res);
         Check ("responder: a repeated authorization root refused",
                Res = S_Unexpected and then Sess = Saved);
         Recv (Sess, Small, PS, F, G, 7, Data_Root, O, Res);
         Check ("responder: the data root while something is open refused",
                Res = S_Unexpected and then Sess = Saved);
         --  A reply over another range than the obligation's is refused.
         Recv (Sess, Small, PS, F, G, 7, Plan_Bytes (Small, Confirm_Plan (Min_Key, Key (Small, 2)), 1), O, Res);
         Check ("responder: a reply over a range that is not the obligation's refused",
                Res = S_Unexpected and then Sess = Saved);
         Recv (Sess, Small, PS, F, G, 7, Plan_Bytes (Small, Range_Plan (Small, Min_Key, Data_Lo), 2), O, Res);
         Check ("responder: a RANGE with g = 2 that ends the range at once refused (a tiling group)",
                Res = S_Unexpected and then Sess = Saved);
      end;
      --  The peer answers our ELEMENTS (it needed nothing): an empty HAVE.
      Recv (Sess, Small, PS, F, G, 7, Plan_Bytes (Small, Confirm_Plan (Min_Key, Data_Lo), 1), O, Res);
      Check ("responder: the answer closes the authorization phase",
             Res = S_OK and then Sess.P = Auth and then Open_Count (Sess) = 0 and then O.N = 0);
      Saved := Sess;
      Recv (Sess, Small, PS, F, G, 7, Plan_Bytes (Small, Confirm_Plan (Min_Key, Data_Lo), 1), O, Res);
      Check ("responder: the same answer delivered again is refused (G4)",
             Res = S_Unexpected and then Sess = Saved);
      Recv (Sess, Small, PS, F, G, 7, Data_Root, O, Res);
      Check ("responder: the data root, equal: confirmed, Done",
             Res = S_OK and then Is_Confirm (O, Data_Lo, Max_Key) and then Group (O) = 1
             and then Sess.P = Done and then Complete (Sess) and then Open_Count (Sess) = 0);
      Saved := Sess;
      Recv (Sess, Small, PS, F, G, 7, Data_Root, O, Res);
      Check ("a message after Done refused", Res = S_Unexpected and then Sess = Saved);

      --  Initiator, Admit-then-receive.
      Start (Sess, Initiator, NS_X, DH1, F, Auth_T, Buf, L);
      Recv (Sess, Small, PS, F, G, 1, Peer_Open, O, Res);
      Admit (Sess, Small, PS, F, G, R_Eff, 1, Cred_T, Buf, L, O);
      Check ("initiator Admit before the peer's HELLO: HELLO only, still in the gate",
             Sess.P = Gate and then Sess.Hello_Sent and then O.N = 0
             and then L = Hello_Fixed + Cred_T'Length);
      Recv (Sess, Small, PS, F, G, 1, Hello_Bytes (Other), O, Res);
      Check ("initiator Admit-then-receive: the authorization root goes out, one obligation",
             Res = S_OK and then Sess.P = Auth and then O.N = 1 and then Group (O) = 0
             and then O.P (1).Kind = P_Range and then O.P (1).Lo = Min_Key
             and then O.P (1).Hi = Data_Lo and then O.P (1).Last + 1 - O.P (1).First = 3
             and then Open_Count (Sess) = 1
             and then Kome.Reconcile.Open (Sess, 1) = Fresh (Min_Key, Data_Lo)
             and then Sess.Auth_Root_Seen);
      Saved := Sess;
      Recv (Sess, Small, PS, F, G, 1, Auth_Root, O, Res);
      Check ("initiator: a g = 0 RANGE refused", Res = S_Unexpected and then Sess = Saved);
      Recv (Sess, Small, PS, F, G, 1, Data_Root, O, Res);
      Check ("initiator: the data root refused", Res = S_Unexpected and then Sess = Saved);
      declare
         Saved2 : constant Session := Sess;
         SBuf   : Msg_Buffer;
         SL     : Msg_Length;
      begin
         --  A RANGE reply (count 1 over [Min_Key, Data_Lo), where we hold
         --  3) that needs ELEMENTS above the ship budget.
         Encode (Small, PS, Range_Plan (Small, Min_Key, Data_Lo), 1, SBuf, SL);
         SBuf (Range_O_Count + 3) := 1;
         Sess.Shipped := Ship_Budget (Small);
         Recv (Sess, Small, PS, F, G, 1, Slice (SBuf, SL), O, Res);
         Check ("a reply beyond the ship budget refused, nothing changes",
                Res = S_Limit and then Sess.Shipped = Ship_Budget (Small)
                and then Open_Count (Sess) = 1 and then O.N = 0);
         Sess := Saved2;
         Sess.Msgs := Sess.Budget;
         Recv (Sess, Small, PS, F, G, 1, Plan_Bytes (Small, Confirm_Plan (Min_Key, Data_Lo), 1), O, Res);
         Check ("over the message budget refused", Res = S_Limit and then Sess.Msgs = Sess.Budget);
         Sess := Saved2;
      end;
      --  The FIFO (G4, H19): the peer splits the root 2 ways. The first
      --  child starts the group (g = 2); a duplicate of it, a message
      --  with another g, and the second child with the wrong hi are
      --  refused; the second child completes the group and the head
      --  leaves. Our answers (ELEMENTS) become two new obligations, in
      --  plan order, and a reply to the second before the first is
      --  refused.
      declare
         K2  : constant Elem_Key := Key (Small, 2);
         C1  : constant Byte_Array := Plan_Bytes (Small, Range_Plan (Small, Min_Key, K2), 2);
         C2  : constant Byte_Array := Plan_Bytes (Small, Range_Plan (Small, K2, Data_Lo), 2);
         C2b : constant Byte_Array := Plan_Bytes (Small, Range_Plan (Small, K2, Key (Small, 3)), 2);
         C1g : constant Byte_Array := Plan_Bytes (Small, Range_Plan (Small, Min_Key, K2), 3);
         Mid : Session (Oblig_Cap => 64);
      begin
         Saved := Sess;
         --  Each child carries count 1 (we hold 1 and 2), so the counts
         --  do not match: we answer each with ELEMENTS.
         declare
            B1 : Byte_Array := C1;
            B2 : Byte_Array := C2;
         begin
            B1 (B1'First + Range_O_Count + 3) := 9;
            B2 (B2'First + Range_O_Count + 3) := 9;
            Receive (Sess, Small, PS, F, G, R_Eff, 1, B1, M, Op, Peer, O, Got, OB, OL, Res);
            Lemma_Queue_Step_Def (Saved, Sess, M, O);
            Check ("FIFO: the first child of the split starts the group, one ELEMENTS back",
                   Res = S_OK and then Open_Count (Sess) = 2
                   and then Kome.Reconcile.Open (Sess, 1)
                              = (Lo => Min_Key, Hi => Data_Lo, Started => True, Kind => M_Range,
                                 G => 2, Got => 1, Next => K2)
                   and then Kome.Reconcile.Open (Sess, 2) = Fresh (Min_Key, K2)
                   and then O.N = 1 and then O.P (1).Kind = P_Elements);
            pragma Assert (Queue_Step (Saved, Sess, M, O));
            Mid := Sess;
            Recv (Sess, Small, PS, F, G, 1, B1, O, Res);
            Check ("FIFO: the first child delivered again is refused (it does not continue the head)",
                   Res = S_Unexpected and then Sess = Mid);
            Recv (Sess, Small, PS, F, G, 1, C1g, O, Res);
            Check ("FIFO: a message with another g than the group's is refused",
                   Res = S_Unexpected and then Sess = Mid);
            Recv (Sess, Small, PS, F, G, 1, C2b, O, Res);
            Check ("FIFO: the last message of the group must end at the obligation's hi",
                   Res = S_Unexpected and then Sess = Mid);
            Receive (Sess, Small, PS, F, G, R_Eff, 1, B2, M, Op, Peer, O, Got, OB, OL, Res);
            Lemma_Queue_Step_Def (Mid, Sess, M, O);
            Check ("FIFO: the second child completes the group: the head leaves, our ELEMENTS are appended",
                   Res = S_OK and then Group_Done (Mid, M) and then Open_Count (Sess) = 2
                   and then Kome.Reconcile.Open (Sess, 1) = Fresh (Min_Key, K2)
                   and then Kome.Reconcile.Open (Sess, 2) = Fresh (K2, Data_Lo));
            pragma Assert (Queue_Step (Mid, Sess, M, O));
         end;
         Mid := Sess;
         Recv (Sess, Small, PS, F, G, 1, Plan_Bytes (Small, Confirm_Plan (K2, Data_Lo), 1), O, Res);
         Check ("FIFO: a reply to the second obligation before the first is refused",
                Res = S_Unexpected and then Sess = Mid);
         Recv (Sess, Small, PS, F, G, 1, Plan_Bytes (Small, Confirm_Plan (Min_Key, K2), 1), O, Res);
         Check ("FIFO: the reply to the first obligation is accepted",
                Res = S_OK and then Open_Count (Sess) = 1
                and then Kome.Reconcile.Open (Sess, 1) = Fresh (K2, Data_Lo));
         Recv (Sess, Small, PS, F, G, 1, Plan_Bytes (Small, Confirm_Plan (K2, Data_Lo), 1), O, Res);
         Check ("FIFO: the reply to the second obligation closes the phase",
                Res = S_OK and then Open_Count (Sess) = 0 and then Sess.P = Auth);
         Sess := Saved;
      end;
      Recv (Sess, Small, PS, F, G, 1, Plan_Bytes (Small, Confirm_Plan (Min_Key, Data_Lo), 1), O, Res);
      Check ("initiator: the confirm closes the authorization root",
             Res = S_OK and then O.N = 0 and then Open_Count (Sess) = 0 and then Sess.P = Auth);
      Next_Phase (Sess, Small, PS, F, G, R_Eff, 1, O, Res);
      Check ("initiator Next_Phase: the data root, g = 0, Data, one obligation",
             Res = S_OK and then Sess.P = Data and then Open_Count (Sess) = 1
             and then Kome.Reconcile.Open (Sess, 1) = Fresh (Data_Lo, Max_Key)
             and then O.N = 1 and then Group (O) = 0 and then O.P (1).Lo = Data_Lo
             and then O.P (1).Hi = Max_Key and then O.P (1).Last + 1 - O.P (1).First = 6);
      Recv (Sess, Small, PS, F, G, 1, Plan_Bytes (Small, Confirm_Plan (Data_Lo, Max_Key), 1), O, Res);
      Check ("initiator: the data confirm ends the session",
             Res = S_OK and then Sess.P = Done and then Complete (Sess));

      --  The gate again (H11): under a new Auth_Gen, a REVOKE of the
      --  peer's member closes the gate, and Receive / Next_Phase abort.
      declare
         F_Rev : State := F;
         Sess2 : Session (Oblig_Cap => 64);
      begin
         Must_Apply (F_Rev, Founding_Revoke (S1_Key, 1_000_000, 90));
         Check ("F_Rev: member 1 is revoked, the gate refuses DH1 and admits DH2",
                Revoked (F_Rev, S1_Key) and then not Gate (F_Rev, R_Eff, DH1)
                and then Gate (F_Rev, R_Eff, DH2));
         Start (Sess, Initiator, NS_X, DH1, F, Auth_T, Buf, L);
         Recv (Sess, Small, PS, F, G, 1, Peer_Open, O, Res);
         Admit (Sess, Small, PS, F, G, R_Eff, 1, Cred_T, Buf, L, O);
         Recv (Sess, Small, PS, F, G, 1, Hello_Bytes (Other), O, Res);
         Sess2 := Sess;
         Saved := Sess;
         --  The same Auth_Gen: the gate is not evaluated again (Eff is
         --  not read), the reply is accepted.
         Recv (Sess, Small, PS, F_Rev, G, 1, Plan_Bytes (Small, Confirm_Plan (Min_Key, Data_Lo), 1), O, Res);
         Check ("H11: under the recorded Auth_Gen the gate is not evaluated again",
                Res = S_OK and then Sess.P = Auth and then Sess.Gate_Gen = 1);
         Sess := Saved;
         Recv (Sess, Small, PS, F_Rev, G, 2, Plan_Bytes (Small, Confirm_Plan (Min_Key, Data_Lo), 1), O, Res);
         Check ("H11: under a new Auth_Gen a closed gate aborts Receive",
                Res = S_Aborted and then Sess.P = Done and then Sess.Aborted and then O.N = 0
                and then Status_Of (Saved, Small, F_Rev, G, R_Eff, 2,
                                    Plan_Bytes (Small, Confirm_Plan (Min_Key, Data_Lo), 1)) = S_Aborted);
         Sess := Saved;
         Recv (Sess, Small, PS, F, G, 2, Plan_Bytes (Small, Confirm_Plan (Min_Key, Data_Lo), 1), O, Res);
         Check ("H11: under a new Auth_Gen an open gate accepts and records the generation",
                Res = S_OK and then Sess.Gate_Gen = 2 and then Open_Count (Sess) = 0);
         Saved := Sess;
         Next_Phase (Sess, Small, PS, F_Rev, G, R_Eff, 3, O, Res);
         Check ("H11: a closed gate aborts Next_Phase, nothing goes out",
                Res = S_Aborted and then Sess.P = Done and then Sess.Aborted and then O.N = 0);
         Sess := Saved;
         Next_Phase (Sess, Small, PS, F, G, R_Eff, 3, O, Res);
         Check ("H11: an open gate lets Next_Phase emit the data root under the new generation",
                Res = S_OK and then Sess.P = Data and then Sess.Gate_Gen = 3);
         --  While quarantined, Admits refuses, and so does the re-check.
         declare
            GQ : Guard_State := (Quarantined => True);
         begin
            Recv (Sess2, Small, PS, F, GQ, 5, Plan_Bytes (Small, Confirm_Plan (Min_Key, Data_Lo), 1), O, Res);
            Check ("H11: the quarantine flag closes the gate at the re-check (H2)",
                   Res = S_Aborted and then Sess2.Aborted);
         end;
      end;

      --  Initiator, receive-then-Admit.
      Start (Sess, Initiator, NS_X, DH1, F, Auth_T, Buf, L);
      Recv (Sess, Small, PS, F, G, 1, Peer_Open, O, Res);
      Recv (Sess, Small, PS, F, G, 1, Hello_Bytes (Other), O, Res);
      Check ("initiator: the peer's HELLO first, still in the gate",
             Res = S_OK and then Sess.P = Gate and then O.N = 0);
      Admit (Sess, Small, PS, F, G, R_Eff, 1, Cred_T, Buf, L, O);
      Check ("initiator receive-then-Admit: HELLO and the authorization root",
             Sess.P = Auth and then Hello_Wire_OK (Slice (Buf, L)) and then O.N = 1
             and then Group (O) = 0 and then O.P (1).Lo = Min_Key
             and then O.P (1).Hi = Data_Lo and then Open_Count (Sess) = 1);

      --  Responder, Admit-then-receive.
      Start (Sess, Responder, NS_X, DH1, F, Auth_T, Buf, L);
      Recv (Sess, Small, PS, F, G, 1, Peer_Open, O, Res);
      Admit (Sess, Small, PS, F, G, R_Eff, 1, Cred_T, Buf, L, O);
      Recv (Sess, Small, PS, F, G, 1, Hello_Bytes (Other), O, Res);
      Check ("responder Admit-then-receive: Auth, nothing to send",
             Res = S_OK and then Sess.P = Auth and then O.N = 0 and then Open_Count (Sess) = 0);

      --  Equal digests: Done directly after the HELLO exchange, in the two
      --  orders.
      Start (Sess, Initiator, NS_X, DH1, F, Auth_T, Buf, L);
      Recv (Sess, Small, PS, F, G, 1, Peer_Open, O, Res);
      Admit (Sess, Small, PS, F, G, R_Eff, 1, Cred_T, Buf, L, O);
      Recv (Sess, Small, PS, F, G, 1, Hello_Bytes (Ours), O, Res);
      Check ("equal digests: initiator Done after the HELLOs, no root",
             Res = S_OK and then Sess.P = Done and then Complete (Sess) and then O.N = 0);
      Start (Sess, Responder, NS_X, DH1, F, Auth_T, Buf, L);
      Recv (Sess, Small, PS, F, G, 1, Peer_Open, O, Res);
      Recv (Sess, Small, PS, F, G, 1, Hello_Bytes (Ours), O, Res);
      Admit (Sess, Small, PS, F, G, R_Eff, 1, Cred_T, Buf, L, O);
      Check ("equal digests: responder Done at Admit",
             Sess.P = Done and then Complete (Sess) and then O.N = 0);
      Recv (Sess, Small, PS, F, G, 1, Auth_Root, O, Res);
      Check ("equal digests: a root after Done refused", Res = S_Unexpected);

      --  Mutants: the out parameters of Receive come from the wire, and
      --  its status is exactly Status_Of.
      declare
         V2   : Rv_Array := [others => Zero_Rv];
         Tiny : Snapshot (Cap => 4, Pool_Cap => 100);
      begin
         Clear (Tiny);
         V2 (1) := [others => 16#11#];
         V2 (2) := [others => 16#22#];
         Start (Sess, Responder, NS_X, DH1, F, Auth_T, Buf, L);
         Saved := Sess;
         Check ("Status_Of: a foreign ns is S_Aborted, not S_Malformed (mutant c)",
                Status_Of (Saved, Small, F, G, R_Eff, 1, Open_Bytes_Of (NS_Y)) = S_Aborted);
         Encode_Open ((Proto => Proto_Version, NS => NS_X, N_RV => 2, RV => V2), Buf, L);
         declare
            Raw : constant Byte_Array := Slice (Buf, L);
         begin
            Check ("Status_Of: our OPEN is S_OK", Status_Of (Sess, Small, F, G, R_Eff, 1, Raw) = S_OK);
            Receive (Sess, Small, PS, F, G, R_Eff, 1, Raw, M, Op, Peer, O, Got, OB, OL, Res);
            Check ("an OPEN's revocations reach the caller intact (mutant b)",
                   Res = S_OK and then Op.N_RV = 2 and then Op.RV (1) = V2 (1)
                   and then Op.RV (2) = V2 (2) and then Op.RV (3) = Zero_Rv
                   and then Open_Decoded (Raw, Op));
         end;
         Receive (Sess, Small, PS, F, G, R_Eff, 1, Hello_Bytes (Other), M, Op, Peer, O, Got, OB, OL, Res);
         Check ("a HELLO's digest and cred reach the session and the caller intact (mutant a)",
                Res = S_OK and then Peer.Digest = Other
                and then Sess.Peer_Digest = Kome.Keys.To_Key256 (Other)
                and then Peer.Cred_Len = Cred_T'Length
                and then Peer.Cred (0 .. Cred_T'Length - 1) = Cred_T
                and then Hello_Decoded (Hello_Bytes (Other), Peer));
         Sess.Ranges := 5;
         Sess.Shipped := 77;
         Admit (Sess, Small, PS, F, G, R_Eff, 1, Cred_T, Buf, L, O);
         Check ("Admit leaves Ranges and Shipped (mutant f)",
                Sess.Ranges = 5 and then Sess.Shipped = 77 and then Sess.P = Auth);
         Check ("Same_Snapshot: the snapshot of Admit, not another",
                Same_Snapshot (Sess, Small) and then not Same_Snapshot (Sess, Tiny));
         Sess.Ranges := 0;
         Sess.Shipped := 0;
         declare
            R : Byte_Array := Auth_Root;
         begin
            R (R'First + Range_O_Count + 3) := 2;
            Check ("Status_Of: the expected root within budget is S_OK (mutant d)",
                   Status_Of (Sess, Small, F, G, R_Eff, 1, R) = S_OK);
            Receive (Sess, Small, PS, F, G, R_Eff, 1, R, M, Op, Peer, O, Got, OB, OL, Res);
            Check ("Receive's M is the wire's: count 2, not a confirm, our 3 shipped (mutant e)",
                   Res = S_OK and then M = Decode_Of (R).M and then M.Count = 2
                   and then not Confirms (Small, M)
                   and then not Is_Confirm (O, Min_Key, Data_Lo)
                   and then O.N = 1 and then O.P (1).Kind = P_Elements
                   and then O = Reply_Of (Small, M).Box);
            Check ("an ELEMENTS reply counts 1 obligation, no RANGE, its run's item bytes",
                   Num_Ranges (O) = 0 and then Obligations (O) = 1
                   and then Item_Bytes (Small, O) = Byte_Total (Run_Size (Small, 1, 3))
                   and then Item_Bytes (Small, O) = Byte_Total (Plan_Items (Small, O.P (1)))
                   and then Item_Bytes (Small, O) = 3 * (Item_Overhead + 30));
         end;
         --  The data root (forced: nothing open), count 0 against our 6:
         --  a 6-way split. If the replies already sent 35 RANGEs, 6 more go
         --  above Range_Budget (40): S_Limit, exactly as Status_Of says.
         --  With 34, they fit exactly, and Receive accepts the same root.
         declare
            Big : Byte_Array := Data_Root;
         begin
            Big (Big'First + Range_O_Count + 3) := 0;
            Sess.Q_Len := 0;
            Sess.Ranges := Range_Budget (Small) - 5;
            Saved := Sess;
            Check ("Status_Of: the data root whose split passes Range_Budget is S_Limit",
                   Range_Budget (Small) = 40
                   and then Num_Ranges (Reply_Of (Small, Decode_Of (Big).M).Box) = 6
                   and then Status_Of (Sess, Small, F, G, R_Eff, 1, Big) = S_Limit);
            Recv (Sess, Small, PS, F, G, 1, Big, O, Res);
            Check ("the data root over Range_Budget refused, nothing changes",
                   Res = S_Limit and then Sess = Saved and then O.N = 0);
            Sess.Ranges := Range_Budget (Small) - 6;
            Saved := Sess;
            Recv (Sess, Small, PS, F, G, 1, Big, O, Res);
            Check ("exactly within Range_Budget the same data root is accepted (Status_Of S_OK)",
                   Res = S_OK and then Status_Of (Saved, Small, F, G, R_Eff, 1, Big) = S_OK
                   and then Sess.P = Data and then O.N = 6
                   and then Sess.Ranges = Range_Budget (Small));
            --  The accounting functions are the true counts of the reply.
            --  So the 6-way split opens six obligations, in plan order,
            --  and the responder is not Done.
            pragma Assert (Ranges_Upto (O, O.N) = 6
                           and then Obligations_Upto (O, O.N) = 6
                           and then Items_Upto (Small, O, O.N) = 0);
            Check ("the accepted 6-way split counts 6 RANGEs, 6 obligations, no item bytes",
                   Num_Ranges (O) = 6 and then Obligations (O) = 6
                   and then Item_Bytes (Small, O) = 0);
            Check ("the accepted 6-way split leaves 6 obligations open, in plan order: Data, not Done",
                   Saved.Q_Len = 0 and then Open_Count (Sess) = 6
                   and then (for all T in 1 .. 6 =>
                               Kome.Reconcile.Open (Sess, T) = Fresh (O.P (T).Lo, O.P (T).Hi))
                   and then Sess.P = Data and then not Complete (Sess));
            --  The FIFO bound: a session with room for 5 refuses the split.
            declare
               S5 : Session (Oblig_Cap => 5);
            begin
               Start (S5, Responder, NS_X, DH1, F, Auth_T, Buf, L);
               Recv (S5, Small, PS, F, G, 1, Peer_Open, O, Res);
               Admit (S5, Small, PS, F, G, R_Eff, 1, Cred_T, Buf, L, O);
               Recv (S5, Small, PS, F, G, 1, Hello_Bytes (Other), O, Res);
               Recv (S5, Small, PS, F, G, 1, Auth_Root, O, Res);
               Check ("a 5-entry FIFO: the authorization root (equal) is confirmed",
                      Res = S_OK and then Open_Count (S5) = 0);
               Recv (S5, Small, PS, F, G, 1, Big, O, Res);
               Check ("a 5-entry FIFO refuses the 6-way split with S_Limit, nothing changes",
                      Res = S_Limit and then Open_Count (S5) = 0 and then S5.P = Auth);
            end;
         end;
      end;

      --  A HAVE reply (to an empty ELEMENTS over the authorization range):
      --  no obligation, no RANGE, the item bytes of the offered elements.
      declare
         HO : Outbox;
         HG : Delivery;
      begin
         Respond (Small, PS, Msg (M_Elements, Min_Key, Data_Lo), HO, HG);
         pragma Assert (Obligations_Upto (HO, HO.N) = 0
                        and then Item_Bytes (Small, HO) = Items_Upto (Small, HO, HO.N));
         Check ("a HAVE reply counts no obligation and no RANGE, its items' bytes",
                HO.N = 1 and then HO.P (1).Kind = P_Have and then HO.P (1).N = 3
                and then Num_Ranges (HO) = 0 and then Obligations (HO) = 0
                and then Item_Bytes (Small, HO) = 3 * (Item_Overhead + 30));
      end;

      --  Decode_Of an ELEMENTS with items: keys and lengths come from the
      --  wire.
      declare
         E : constant Byte_Array :=
           Plan_Bytes (Small, (Kind => P_Elements, Lo => Min_Key, Hi => Data_Lo,
                               First => 1, Last => 3, N => 0, Items => [others => 1]), 1);
         D : constant Decoding := Decode_Of (E);
      begin
         Check ("Decode_Of an ELEMENTS: item keys, places and lengths are the wire's",
                D.OK and then D.M.N = 3 and then Decode_Facts (E, D.M, True)
                and then D.M.Items (2).Key = Key (Small, 2)
                and then D.M.Items (1).Off = E'First + Elems_Fixed + Item_Overhead
                and then D.M.Items (1).Len = 30);
      end;
   end;

   ----------------------------------------------------------------------
   --  (i) Two snapshots converge in a two-phase session.
   ----------------------------------------------------------------------
   declare
      A, B   : Replica;
      Rounds, Delivered : Natural;
      All_OK, Done : Boolean;
      Union  : Natural;
      Huge   : constant Elem_Key := EK (4, 44, 44, 44);
   begin
      for E in Byte range 1 .. 6 loop                 --  shared authorization
         Add (A, EK (Kind_Code (E mod 3), E, 0, E), Frame_Of (40, E));
         Add (B, EK (Kind_Code (E mod 3), E, 0, E), Frame_Of (40, E));
      end loop;
      for E in Byte range 7 .. 9 loop                 --  A-only authorization
         Add (A, EK (Kind_Code (E mod 3), E, 0, E), Frame_Of (300, E));
      end loop;
      Add (B, EK (2, 10, 0, 10), Frame_Of (300, 10));  --  B-only authorization
      for E in Byte range 1 .. 20 loop                --  shared data
         Add (A, EK (3 + Kind_Code (E mod 2), E, 16#78#, E), Frame_Of (8, E));
         Add (B, EK (3 + Kind_Code (E mod 2), E, 16#78#, E), Frame_Of (8, E));
      end loop;
      for E in Byte range 21 .. 40 loop               --  A-only data
         Add (A, EK (4, E, 16#78#, E), Frame_Of (12, E));
      end loop;
      for Fl in Byte range 16#61# .. 16#63# loop      --  A-only, large
         Add (A, EK (4, 43, Fl, 1), Frame_Of (20_000, Fl));
      end loop;
      Add (A, Huge, Frame_Of (Kome.Records.Frame_Max, 16#AB#));   --  41 136 bytes
      for E in Byte range 50 .. 59 loop               --  B-only data
         Add (B, EK (3, E, 16#78#, E), Frame_Of (8, E));
      end loop;
      Union := 6 + 3 + 1 + 20 + 20 + 3 + 1 + 10;

      Run_Session (A, B, F, Auth_T, G, Rounds, Delivered, All_OK, Done);
      Check ("two-phase session: every message accepted", All_OK);
      Check ("two-phase session: both sides end Complete", Done);
      Check ("two-phase session: the replicas converge to the union",
             Same_Set (A, B) and then Natural (A.Els.Length) = Union);
      Check ("the 41 136-byte frame reached B intact",
             Frame_Of_Key (B, Huge) = Frame_Of (41_136, 16#AB#));
      --  Rounds: OPEN, HELLO, then at most 2s + 3 one-way batches for
      --  each phase. In the larger (data) phase, A holds 44 records and B
      --  holds 30, so s = ⌈log₁₆ 44⌉ + ⌈log₁₆ 30⌉ = 4 splits.
      Check ("bounded number of rounds (" & Rounds'Image (2 .. Rounds'Image'Last)
             & " one-way rounds," & Delivered'Image & " frames delivered)",
             Rounds <= 3 + 2 * (2 * 4 + 3) and then Delivered >= 38);

      Run_Session (A, B, F, Auth_T, G, Rounds, Delivered, All_OK, Done);
      Check ("second session ends at the HELLOs: equal digests",
             All_OK and then Done and then Rounds <= 3 and then Delivered = 0
             and then Same_Set (A, B));
   end;

      if Failed then
         Set_Exit_Status (Failure);
      end if;
   end Run_All;

begin
   null;
end Test_Reconcile;
