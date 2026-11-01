--  Test main for Kome.Reconcile (DESIGN.md §8, §4). (a) The key order and
--  its lemmas on examples. (b) Snapshots: appends in order, every refusal
--  leaves the snapshot unchanged. (c) Windows and the cover on examples.
--  (d) Encode / Decode round trips for RANGE, ELEMENTS, HAVE, the confirm
--  and HELLO (with roots_ever), every message within Max_Message_Len,
--  malformed inputs refused. (e) The responder: an explicit confirm on
--  equal fingerprints, ship at most Ship_Threshold, a 16-way split with
--  strictly smaller children that partition the range, exactly the
--  missing elements delivered and exactly the peer's missing ones sent
--  back, and large frames split further so every message fits. (f) The
--  HELLO join is max / union, reports a full W, and is bounded above.
--  (g) The session state machine refuses out-of-phase, malformed,
--  unsolicited and over-budget messages and changes nothing; an untrusted
--  HELLO leaves the registers alone; Complete marks the end. (h) Two
--  in-memory replicas with differing frontiers, real Kome.Records PUT
--  frames, converge to the union in a bounded number of rounds, including
--  a record above B's ceiling and one by a writer B has never listed: both
--  inadmissible at B until A's HELLO joins the registers; both sessions
--  end Complete; a second session confirms at the root range.
--  Under -gnata every Pre, Post and lemma runs on these data.
pragma Ada_2022;
with Ada.Text_IO;      use Ada.Text_IO;
with Ada.Command_Line; use Ada.Command_Line;
with Ada.Containers.Indefinite_Vectors;
with Kome;             use Kome;
with Kome.Keys;
with Kome.Headers;     use Kome.Headers;
with Kome.Registers;   use Kome.Registers;
with Kome.Records;
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

   function Msg (K : Msg_Kind; Lo, Hi : Elem_Key; Count : Natural := 0;
                 Fp : Hash256 := [others => 0]) return Message is
     (Kind => K, G => 1, Lo => Lo, Hi => Hi, Count => Count, Fp => Fp,
      N => 0, Items => <>, W_Full => False);

   package Msg_Vectors is new Ada.Containers.Indefinite_Vectors
     (Positive, Byte_Array);

   function Slice (B : Msg_Buffer; L : Msg_Length) return Byte_Array is
     (B (0 .. L - 1));

   No_Roots : constant Writer_List (1 .. 0) := [];


   --  A small snapshot of synthetic elements I = 1 .. N, key (3, I, I, I),
   --  frame of Len bytes.
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

   --  Every plan encodes to Plan_Len bytes and decodes back.
   function Plans_Fit (S : Snapshot; O : Outbox) return Boolean is
      Buf : Msg_Buffer;
      L   : Msg_Length;
      M   : Message;
      OK  : Boolean;
   begin
      for T in 1 .. O.N loop
         Encode (S, O.P (T), Group (O), Buf, L);
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

   ----------------------------------------------------------------------
   --  Replicas for the convergence test: a list of (key, header, frame)
   --  plus the registers and a sorted mirror of W (Kome.Registers cannot
   --  enumerate W, so the HELLO list is kept beside it; Encode_Hello's
   --  Pre checks the mirror against the registers).
   ----------------------------------------------------------------------

   type Elem (Len : Natural) is record
      Key : Elem_Key;
      Hdr : Header;
      F   : Byte_Array (1 .. Len);
   end record;

   function Before (A, B : Elem) return Boolean is (Key_Lt (A.Key, B.Key));

   package Elem_Vectors is new Ada.Containers.Indefinite_Vectors
     (Positive, Elem);
   package Elem_Sort is new Elem_Vectors.Generic_Sorting (Before);

   type Replica is record
      Els  : Elem_Vectors.Vector;
      Regs : Register_File := Kome.Registers.Empty;
      WL   : Writer_List (1 .. 16) := [others => (others => 0)];
      NW   : Natural := 0;
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

   function Admissible (Regs : Register_File; H : Header) return Boolean is
     (if Is_Data (H)
      then Data_T (H) <= Ceil (Regs) and then In_W (Regs, Data_Author (H))
      else True);

   --  Insert K into the sorted mirror (not the registers).
   procedure Mirror (R : in out Replica; K : Key256) is
      Pos : Natural := R.NW + 1;
   begin
      for I in 1 .. R.NW loop
         if R.WL (I) = K then
            return;
         end if;
      end loop;
      for I in 1 .. R.NW loop
         if Lt (K, R.WL (I)) then
            Pos := I;
            exit;
         end if;
      end loop;
      R.WL (Pos + 1 .. R.NW + 1) := R.WL (Pos .. R.NW);
      R.WL (Pos) := K;
      R.NW := R.NW + 1;
   end Mirror;

   procedure Add_W (R : in out Replica; K : Key256) is
   begin
      Mirror (R, K);
      Add_Writer (R.Regs, K);
   end Add_W;

   NS_B : constant NS_Id := [others => 16#5A#];

   function Pk (B : Byte) return Pubkey is ([others => B]);

   --  A PUT on entity E, field F, by author A at time T, with a value of
   --  VLen bytes.
   function Make (E : Byte; F : Byte; A : Byte; T : U48; VLen : Natural)
     return Elem
   is
      R  : constant Kome.Records.Put_Record :=
        Kome.Records.Make_Put
          (NS_B, [others => E], [F], T, 1, Pk (A),
           [for I in 1 .. VLen => Byte (I mod 251)]);
      Fr : constant Byte_Array := Kome.Records.Encode (R);
      H  : constant Header := Kome.Records.To_Header (R);
   begin
      return (Len => Fr'Length, Key => Key_Of (H), Hdr => H, F => Fr);
   end Make;

   --  Apply one received frame: decode it, check that it is the element it
   --  was shipped as, check admission under the current registers, hold
   --  it if new.
   Refused_Mismatch : Natural := 0;

   procedure Apply (R : in out Replica; K : Elem_Key; Fr : Byte_Array) is
      PR : Kome.Records.Put_Record;
      St : Status;
   begin
      Kome.Records.Decode (Fr, PR, St);
      if St /= OK then
         Refused_Mismatch := Refused_Mismatch + 1;
         return;
      end if;
      declare
         H : constant Header := Kome.Records.To_Header (PR);
      begin
         if Key_Of (H) /= K then
            Refused_Mismatch := Refused_Mismatch + 1;
         elsif Admissible (R.Regs, H) and then not Holds (R, K) then
            R.Els.Append (Elem'(Len => Fr'Length, Key => K, Hdr => H, F => Fr));
         end if;
      end;
   end Apply;

   --  One session, A initiating. Messages flow one direction at a time:
   --  each side only answers what it received. Rounds counts one-way
   --  deliveries; Delivered counts frames handed to a replica.
   procedure Run_Session
     (A, B : in out Replica; Rounds : out Natural; Delivered : out Natural;
      All_OK : out Boolean; Both_Complete : out Boolean)
   is
      SA : Snapshot (Cap => 256, Pool_Cap => 400_000);
      SB : Snapshot (Cap => 256, Pool_Cap => 400_000);
      Sess_A, Sess_B : Session;
      To_B, To_A : Msg_Vectors.Vector;
      O  : Outbox;

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

      procedure Emit (R : Replica; S : Snapshot; O : Outbox;
                      Q : in out Msg_Vectors.Vector) is
         Buf : Msg_Buffer;
         L   : Msg_Length;
      begin
         if O.Hello then
            Encode_Hello (R.Regs, Kome.Reconcile.Count (S), R.WL (1 .. R.NW),
                          No_Roots, Buf, L);
            Q.Append (Slice (Buf, L));
         end if;
         for T in 1 .. O.N loop
            Encode (S, O.P (T), Group (O), Buf, L);
            Q.Append (Slice (Buf, L));
         end loop;
      end Emit;

      --  Deliver every message of In_Q to replica R; its answers go to
      --  Out_Q.
      procedure Deliver_All
        (R : in out Replica; S : Snapshot; Sess : in out Session;
         In_Q : in out Msg_Vectors.Vector; Out_Q : in out Msg_Vectors.Vector)
      is
         M    : Message;
         Peer : Hello;
         Got  : Delivery;
         St   : Session_Status;
         O2   : Outbox;
      begin
         for Raw of In_Q loop
            Receive (Sess, S, R.Regs, True, Raw, M, Peer, O2, Got, St);
            if St /= S_OK then
               All_OK := False;
            end if;
            --  Keep the W mirror in step with the join (test bookkeeping).
            if St = S_OK and then M.Kind = M_Hello then
               for I in 1 .. Natural (Peer.N) loop
                  Mirror (R, Peer.W (I));
               end loop;
            end if;
            for T in Got'Range loop
               if Got (T) then
                  declare
                     It : constant In_Item := M.Items (T);
                  begin
                     Apply (R, It.Key, Raw (It.Off .. It.Off + It.Len - 1));
                     Delivered := Delivered + 1;
                  end;
               end if;
            end loop;
            Emit (R, S, O2, Out_Q);
         end loop;
         In_Q.Clear;
      end Deliver_All;

   begin
      All_OK := True;
      Rounds := 0;
      Delivered := 0;
      Snap (A, SA);
      Snap (B, SB);
      Start (Sess_A, Initiator, O);
      Emit (A, SA, O, To_B);
      Start (Sess_B, Responder, O);
      Emit (B, SB, O, To_A);
      while not To_B.Is_Empty or else not To_A.Is_Empty loop
         if not To_B.Is_Empty then
            Rounds := Rounds + 1;
            Deliver_All (B, SB, Sess_B, To_B, To_A);
         end if;
         if not To_A.Is_Empty then
            Rounds := Rounds + 1;
            Deliver_All (A, SA, Sess_A, To_A, To_B);
         end if;
         exit when Rounds > 100;
      end loop;
      Both_Complete := Complete (Sess_A) and then Complete (Sess_B);
   end Run_Session;

   function Same_Set (A, B : Replica) return Boolean is
   begin
      if Natural (A.Els.Length) /= Natural (B.Els.Length) then
         return False;
      end if;
      for E of A.Els loop
         if not Holds (B, E.Key) then
            return False;
         end if;
      end loop;
      return True;
   end Same_Set;

   --  The number of our elements in [Lo, Hi): My_Count, which is ghost.
   function Cnt (S : Snapshot; Lo, Hi : Elem_Key) return Natural is
     (Window (S, Lo, Hi).Last + 1 - Window (S, Lo, Hi).First);

   No_Bytes : constant Byte_Array (1 .. 0) := [];

   Small : Snapshot (Cap => 64, Pool_Cap => 300_000);
   St    : Snap_Status;

begin
   ----------------------------------------------------------------------
   --  (a) Key order.
   ----------------------------------------------------------------------
   declare
      A : constant Elem_Key := EK (0, 9, 9, 9);
      B : constant Elem_Key := EK (3, 1, 1, 1);
      C : constant Elem_Key := EK (3, 1, 1, 2);
      D : constant Elem_Key := EK (3, 1, 2, 0);
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
             Key_Le (Min_Key, A) and then Key_Lt (D, Max_Key));
   end;

   ----------------------------------------------------------------------
   --  (b) Snapshots.
   ----------------------------------------------------------------------
   Clear (Small);
   Append (Small, EK (3, 2, 2, 2), Frame_Of (10, 1), St);
   Check ("append first", St = Snap_OK and then Kome.Reconcile.Count (Small) = 1
          and then Frame_Bytes (Small) = 10);
   Append (Small, EK (3, 1, 1, 1), Frame_Of (10, 1), St);
   Check ("append out of order refused, unchanged",
          St = Snap_Unsorted and then Kome.Reconcile.Count (Small) = 1);
   Append (Small, EK (3, 2, 2, 2), Frame_Of (10, 1), St);
   Check ("append duplicate refused", St = Snap_Unsorted);
   Append (Small, EK (4, 9, 9, 9), Frame_Of (10, 1), St);
   Check ("append kind 4 refused", St = Snap_Bad_Kind);
   Append (Small, EK (3, 3, 3, 3), Frame_Of (Frame_Ship_Max + 1, 1), St);
   Check ("append frame over Frame_Ship_Max refused", St = Snap_Too_Large);
   Append (Small, EK (3, 3, 3, 3), Frame_Of (Frame_Ship_Max, 7), St);
   Check ("append frame of exactly Frame_Ship_Max",
          St = Snap_OK and then Kome.Reconcile.Count (Small) = 2
          and then Frame (Small, 2) = Frame_Of (Frame_Ship_Max, 7));
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

   ----------------------------------------------------------------------
   --  (c) Windows.
   ----------------------------------------------------------------------
   Fill (Small, 10, 20);
   declare
      W1 : constant Span := Window (Small, Min_Key, Max_Key);
      W2 : constant Span := Window (Small, Key (Small, 3), Key (Small, 7));
      W3 : constant Span := Window (Small, EK (3, 3, 3, 4), EK (3, 3, 3, 5));
      W4 : constant Span := Window (Small, EK (3, 3, 3, 4), EK (3, 6, 0, 0));
   begin
      Check ("window of the whole range", W1.First = 1 and then W1.Last = 10);
      Check ("window [k3, k7) is 3 .. 6", W2.First = 3 and then W2.Last = 6);
      Check ("empty window between two keys", W3.Last + 1 = W3.First);
      Check ("window between keys is 4 .. 5", W4.First = 4 and then W4.Last = 5);
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
      Buf : Msg_Buffer;
      L   : Msg_Length;
      M   : Message;
      OK  : Boolean;
      P   : Plan;
   begin
      P := (Kind => P_Range, Lo => Key (Small, 2), Hi => Key (Small, 9),
            First => 2, Last => 8, N => 0, Items => [others => 1]);
      Encode (Small, P, 3, Buf, L);
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
      Encode (Small, P, 1, Buf, L);
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
      Encode (Small, P, 2, Buf, L);
      Lemma_Confirm_Accepted (Small, P, 2, Buf);
      Decode (Slice (Buf, L), M, OK);
      Check ("confirm (empty HAVE) round trip",
             OK and then L = Elems_Fixed and then M.Kind = M_Have and then M.N = 0
             and then M.G = 2 and then Empty_Wire_OK (Slice (Buf, L)));

      P := (Kind => P_Have, Lo => Min_Key, Hi => Max_Key,
            First => 1, Last => 0, N => 2, Items => [1, 7, 1, 1]);
      Encode (Small, P, 1, Buf, L);
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
         --  Swap the two items in place.
         B2 (Elems_Fixed .. Elems_Fixed + Item - 1) := Buf (Elems_Fixed + Item .. Elems_Fixed + 2 * Item - 1);
         B2 (Elems_Fixed + Item .. Elems_Fixed + 2 * Item - 1) := Buf (Elems_Fixed .. Elems_Fixed + Item - 1);
         Decode (Slice (B2, L), M, OK);
         Check ("descending items refused", not OK);
         --  An item kind of 4.
         B2 := Buf;
         B2 (Elems_Fixed) := 4;
         Decode (Slice (B2, L), M, OK);
         Check ("item of kind 4 refused", not OK);
         --  A zero frame length.
         B2 := Buf;
         B2 (Elems_Fixed + 81 .. Elems_Fixed + 84) := [0, 0, 0, 0];
         Decode (Slice (B2, L), M, OK);
         Check ("zero frame length refused", not OK);
      end;
      --  lo >= hi.
      P := (Kind => P_Range, Lo => Key (Small, 2), Hi => Key (Small, 9),
            First => 2, Last => 8, N => 0, Items => [others => 1]);
      Encode (Small, P, 1, Buf, L);
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
         --  An item outside [lo, hi): HAVE over [k2, k3) listing k5.
         Encode (Small, (Kind => P_Have, Lo => Min_Key, Hi => Max_Key, First => 1,
                         Last => 0, N => 1, Items => [5, 1, 1, 1]), 1, Buf, L);
         Encode (Small, (Kind => P_Range, Lo => Key (Small, 2), Hi => Key (Small, 3),
                         First => 2, Last => 2, N => 0, Items => [others => 1]), 1, B2, L);
         Buf (O_Lo .. Elems_O_N - 1) := B2 (O_Lo .. Elems_O_N - 1);
         Decode (Buf (0 .. Elems_Fixed + 85 + 20 - 1), M, OK);
         Check ("item outside [lo, hi) refused", not OK);
      end;

      --  HELLO.
      declare
         R  : Register_File := Kome.Registers.Empty;
         WL : constant Writer_List := [K256 (1), K256 (2), K256 (3)];
         RL : constant Writer_List := [K256 (9)];
         H  : Hello;
      begin
         Raise_Ceiling (R, 16#1234_5678_9ABC#);
         for K of WL loop
            Add_Writer (R, K);
         end loop;
         Encode_Hello (R, 42, WL, RL, Buf, L);
         Decode_Hello (Slice (Buf, L), H, OK);
         Check ("HELLO round trip",
                OK and then L = Hello_Len (3, 1) and then H.Ceil = 16#1234_5678_9ABC#
                and then H.F_Cnt = 42 and then H.N = 3 and then H.W (2) = K256 (2)
                and then H.R = 1 and then H.Roots (1) = K256 (9));
         declare
            B2 : Msg_Buffer := Buf;
         begin
            B2 (15 .. 46) := Buf (47 .. 78);
            B2 (47 .. 78) := Buf (15 .. 46);
            Decode_Hello (Slice (B2, L), H, OK);
            Check ("HELLO with a descending writer list refused", not OK);
            Decode_Hello (Buf (0 .. L - 2), H, OK);
            Check ("truncated HELLO refused", not OK);
            B2 := Buf;
            B2 (Hello_O_N + 1) := 4;
            Decode_Hello (Slice (B2, L), H, OK);
            Check ("HELLO whose counts disagree with its length refused", not OK);
         end;
      end;
      declare
         R    : Register_File := Kome.Registers.Empty;
         Many : constant Writer_List (1 .. Writers_Max) :=
           [for I in 1 .. Writers_Max => (W0 => Word (I), others => 0)];
         Rts  : constant Writer_List (1 .. Roots_Ever_Max) :=
           [for I in 1 .. Roots_Ever_Max => (W0 => Word (I), others => 1)];
         H    : Hello;
      begin
         for K of Many loop
            Add_Writer (R, K);
         end loop;
         Encode_Hello (R, 0, Many, Rts, Buf, L);
         Decode_Hello (Slice (Buf, L), H, OK);
         Check ("HELLO with Writers_Max writers and Roots_Ever_Max roots fits",
                OK and then L = Hello_Max_Len and then H.N = Writers_Max
                and then H.R = Roots_Ever_Max);
      end;
   end;

   ----------------------------------------------------------------------
   --  (e) The responder.
   ----------------------------------------------------------------------
   Fill (Small, 40, 20);
   declare
      M   : Message;
      O   : Outbox;
      Got : Delivery;
   begin
      M := Msg (M_Range, Min_Key, Max_Key, 40, Range_Fp (Small, 1, 40));
      Respond (Small, M, O, Got);
      Check ("equal fingerprint: an explicit confirm, nothing delivered",
             Is_Confirm (O, Min_Key, Max_Key) and then O.Reply
             and then Got = No_Delivery and then Plans_Fit (Small, O));

      M.Count := 39;
      Respond (Small, M, O, Got);
      Check ("40 elements, mismatch: 16-way split",
             O.N = 16 and then Tiles (O, Min_Key, Max_Key) and then Plans_Fit (Small, O));
      declare
         Ok : Boolean := O.P (1).Lo = Min_Key and then O.P (16).Hi = Max_Key;
         Sum : Natural := 0;
      begin
         for T in 1 .. O.N loop
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

      M := Msg (M_Range, Key (Small, 5), Key (Small, 9));
      Respond (Small, M, O, Got);
      Check ("4 elements, mismatch: one ELEMENTS",
             O.N = 1 and then O.P (1).Kind = P_Elements
             and then O.P (1).First = 5 and then O.P (1).Last = 8
             and then Item_Bytes (Small, O) = 4 * (85 + 20)
             and then Plans_Fit (Small, O));

      M := Msg (M_Range, Key (Small, 5), Key (Small, 11));
      Respond (Small, M, O, Got);
      Check ("6 elements, mismatch: split into 6 singletons",
             O.N = 6 and then Tiles (O, Key (Small, 5), Key (Small, 11))
             and then (for all T in 1 .. 6 => O.P (T).Kind = P_Range
                                 and then O.P (T).First = O.P (T).Last)
             and then Plans_Fit (Small, O));

      --  ELEMENTS from the peer listing k5 and a key we lack; we hold
      --  k5 .. k8 in the range, so HAVE answers k6, k7, k8 and the
      --  unknown key is delivered.
      M := Msg (M_Elements, Key (Small, 5), Key (Small, 9));
      M.N := 2;
      M.Items := [(Key => Key (Small, 5), Off => 0, Len => 1),
                  (Key => EK (3, 6, 0, 0), Off => 0, Len => 1),
                  others => <>];
      Respond (Small, M, O, Got);
      Check ("ELEMENTS: exactly the key we lack is delivered",
             Got = [False, True, False, False]);
      Check ("ELEMENTS: HAVE answers exactly what the peer lacked",
             O.N = 1 and then O.P (1).Kind = P_Have and then O.P (1).N = 3
             and then O.P (1).Items (1) = 6 and then O.P (1).Items (3) = 8
             and then Have_Exact (Small, M, O)
             and then Plans_Fit (Small, O));

      M.Kind := M_Have;
      Respond (Small, M, O, Got);
      Check ("HAVE: delivered, never answered",
             O.N = 0 and then Got = [False, True, False, False]);

      --  ELEMENTS listing everything we hold in the range: an empty HAVE.
      M := Msg (M_Elements, Key (Small, 5), Key (Small, 7));
      M.N := 2;
      M.Items := [(Key => Key (Small, 5), Off => 0, Len => 1),
                  (Key => Key (Small, 6), Off => 0, Len => 1),
                  others => <>];
      Respond (Small, M, O, Got);
      Check ("ELEMENTS with nothing missing either way: confirm, nothing delivered",
             Is_Confirm (O, Key (Small, 5), Key (Small, 7))
             and then Got = No_Delivery and then Plans_Fit (Small, O));
   end;

   --  Large frames: three of 20 000 bytes do not fit one message.
   Fill (Small, 3, 20_000);
   declare
      M   : Message;
      O   : Outbox;
      Got : Delivery;
   begin
      M := Msg (M_Range, Min_Key, Max_Key);
      Respond (Small, M, O, Got);
      Check ("ELEMENTS too large for one message: one per element",
             O.N = 3 and then (for all T in 1 .. 3 => O.P (T).Kind = P_Elements
                                 and then O.P (T).First = T and then O.P (T).Last = T)
             and then O.P (1).Lo = Min_Key and then O.P (3).Hi = Max_Key
             and then O.P (1).Hi = O.P (2).Lo and then O.P (2).Hi = O.P (3).Lo
             and then Plans_Fit (Small, O));
      M.Kind := M_Elements;
      Respond (Small, M, O, Got);
      Check ("HAVE too large for one message: one per element",
             O.N = 3 and then (for all T in 1 .. 3 => O.P (T).Kind = P_Have
                                 and then O.P (T).N = 1)
             and then Have_Exact (Small, M, O)
             and then Plans_Fit (Small, O));
   end;
   --  Two frames of Frame_Ship_Max: each alone is exactly Max_Message_Len.
   Clear (Small);
   Append (Small, EK (3, 1, 1, 1), Frame_Of (Frame_Ship_Max, 1), St);
   Append (Small, EK (3, 2, 2, 2), Frame_Of (Frame_Ship_Max, 2), St);
   declare
      M   : Message;
      O   : Outbox;
      Got : Delivery;
      Buf : Msg_Buffer;
      L   : Msg_Length;
   begin
      M := Msg (M_Range, Min_Key, Max_Key);
      Respond (Small, M, O, Got);
      Encode (Small, O.P (1), Group (O), Buf, L);
      Check ("largest frame ships in a message of exactly Max_Message_Len",
             O.N = 2 and then L = Max_Message_Len and then Plans_Fit (Small, O));
   end;

   ----------------------------------------------------------------------
   --  (f) The HELLO join.
   ----------------------------------------------------------------------
   declare
      R  : Register_File := Kome.Registers.Empty;
      H  : Hello;
      JR : Join_Status;
   begin
      Raise_Ceiling (R, 100);
      Add_Writer (R, K256 (1));
      H.Ceil := 50;
      H.N := 2;
      H.W (1) := K256 (2);
      H.W (2) := K256 (3);
      Join (R, H, JR);
      Check ("join keeps the larger ceiling", JR = J_OK and then Ceil (R) = 100);
      Check ("join is the union of the writer sets, and nothing else",
             In_W (R, K256 (1)) and then In_W (R, K256 (2)) and then In_W (R, K256 (3))
             and then Kome.Registers.Count (R) = 3 and then Has_All (R, H));
      H.Ceil := 500;
      Join (R, H, JR);
      Check ("join raises to the peer's ceiling, idempotent on W",
             JR = J_OK and then Ceil (R) = 500 and then Kome.Registers.Count (R) = 3);
   end;
   declare
      R  : Register_File := Kome.Registers.Empty;
      H  : Hello;
      JR : Join_Status;
   begin
      for I in 1 .. Writers_Max loop
         Add_Writer (R, (W0 => Word (I), others => 0));
      end loop;
      H.N := 2;
      H.W (1) := (W0 => 1, others => 0);             --  already held
      H.W (2) := (W0 => 0, others => 7);             --  new: no room
      Join (R, H, JR);
      Check ("join at Writers_Max reports the dropped key",
             JR = J_W_Full and then Kome.Registers.Count (R) = Writers_Max
             and then not In_W (R, H.W (2)) and then In_W (R, H.W (1)));
   end;

   ----------------------------------------------------------------------
   --  (g) The session state machine.
   ----------------------------------------------------------------------
   Fill (Small, 10, 20);
   declare
      Sess : Session;
      R    : Register_File := Kome.Registers.Empty;
      O    : Outbox;
      M    : Message;
      Peer : Hello;
      Got  : Delivery;
      Res  : Session_Status;
      Buf  : Msg_Buffer;
      L    : Msg_Length;
      RBuf : Msg_Buffer;
      RL   : Msg_Length;
      CBuf : Msg_Buffer;
      CL   : Msg_Length;
      HR   : Register_File := Kome.Registers.Empty;
      Root : constant Plan :=
        (Kind => P_Range, Lo => Min_Key, Hi => Max_Key, First => 1,
         Last => 10, N => 0, Items => [others => 1]);
      Conf : constant Plan :=
        (Kind => P_Have, Lo => Min_Key, Hi => Max_Key, First => 1,
         Last => 0, N => 0, Items => [others => 1]);
   begin
      Encode (Small, Root, 0, RBuf, RL);              --  the root RANGE (g = 0)
      Encode (Small, Conf, 1, CBuf, CL);              --  a confirm (g = 1)
      Raise_Ceiling (HR, 777);
      Add_Writer (HR, K256 (4));
      Encode_Hello (HR, 3, [K256 (4)], No_Roots, Buf, L);

      Start (Sess, Responder, O);
      Check ("responder starts silent, awaiting HELLO",
             O.N = 0 and then not O.Hello and then Sess.P = Await_Hello);
      Receive (Sess, Small, R, True, Slice (RBuf, RL), M, Peer, O, Got, Res);
      Check ("RANGE before HELLO refused, nothing changes",
             Res = S_Unexpected and then Sess.P = Await_Hello and then Sess.Msgs = 0
             and then Ceil (R) = 0 and then O.N = 0);
      Receive (Sess, Small, R, True, Buf (0 .. L - 2), M, Peer, O, Got, Res);
      Check ("malformed HELLO refused, registers unchanged",
             Res = S_Malformed and then Ceil (R) = 0 and then Sess.Msgs = 0);
      Receive (Sess, Small, R, True, No_Bytes, M, Peer, O, Got, Res);
      Check ("empty input refused", Res = S_Malformed);
      declare
         S2 : Session;
         R2 : Register_File := Kome.Registers.Empty;
      begin
         Start (S2, Responder, O);
         Receive (S2, Small, R2, False, Slice (Buf, L), M, Peer, O, Got, Res);
         Check ("untrusted HELLO: session proceeds, registers unchanged",
                Res = S_OK and then S2.P = Ready and then Ceil (R2) = 0
                and then Kome.Registers.Count (R2) = 0 and then Peer.Ceil = 777);
      end;
      Receive (Sess, Small, R, True, Slice (Buf, L), M, Peer, O, Got, Res);
      Check ("HELLO joins and is answered with HELLO",
             Res = S_OK and then Sess.P = Ready and then Ceil (R) = 777
             and then In_W (R, K256 (4)) and then O.Hello and then O.N = 0
             and then not Complete (Sess));
      Receive (Sess, Small, R, True, Slice (Buf, L), M, Peer, O, Got, Res);
      Check ("second HELLO refused", Res = S_Unexpected and then Sess.Msgs = 1);
      Receive (Sess, Small, R, True, Slice (CBuf, CL), M, Peer, O, Got, Res);
      Check ("a reply nobody asked for refused",
             Res = S_Unexpected and then Sess.Msgs = 1 and then Sess.Pending = 0);
      declare
         Saved : constant Session := Sess;
      begin
         Sess.Shipped := Ship_Budget (Small);
         Receive (Sess, Small, R, True, Slice (RBuf, RL), M, Peer, O, Got, Res);
         Check ("root RANGE over our own set: no item bytes needed, accepted",
                Res = S_OK);
         Sess := Saved;
      end;
      Receive (Sess, Small, R, True, Slice (RBuf, RL), M, Peer, O, Got, Res);
      Check ("root RANGE over our own set: confirmed explicitly, complete",
             Res = S_OK and then Is_Confirm (O, Min_Key, Max_Key) and then O.Reply
             and then Sess.Msgs = 2 and then Sess.Pending = 0 and then Complete (Sess));
      Receive (Sess, Small, R, True, Slice (RBuf, RL), M, Peer, O, Got, Res);
      Check ("a second root RANGE refused", Res = S_Unexpected and then Sess.Msgs = 2);
      Sess.Msgs := Sess.Budget;
      Receive (Sess, Small, R, True, Slice (RBuf, RL), M, Peer, O, Got, Res);
      Check ("over the message budget refused",
             Res = S_Limit and then Sess.Msgs = Sess.Budget);

      --  The initiator: HELLO, then the root RANGE, then the confirm.
      Start (Sess, Initiator, O);
      Check ("initiator starts with HELLO",
             O.Hello and then O.N = 0 and then Sess.P = Hello_Sent);
      Receive (Sess, Small, R, True, Slice (Buf, L), M, Peer, O, Got, Res);
      Check ("initiator answers the HELLO with the root RANGE",
             Res = S_OK and then O.N = 1 and then O.P (1).Kind = P_Range
             and then Group (O) = 0
             and then O.P (1).Lo = Min_Key and then O.P (1).Hi = Max_Key
             and then O.P (1).Last = 10 and then Sess.Pending = Unit
             and then not Complete (Sess));
      Receive (Sess, Small, R, True, Slice (RBuf, RL), M, Peer, O, Got, Res);
      Check ("initiator refuses a root RANGE", Res = S_Unexpected);
      declare
         Saved : constant Session := Sess;
         SBuf  : Msg_Buffer;
         SL    : Msg_Length;
      begin
         --  A RANGE reply (count 1 over [Min_Key, k3), where we hold 2)
         --  that would need ELEMENTS beyond the ship budget.
         Encode (Small, (Kind => P_Range, Lo => Min_Key, Hi => Key (Small, 3),
                         First => 1, Last => 2, N => 0, Items => [others => 1]),
                 16, SBuf, SL);
         SBuf (Range_O_Count + 3) := 1;
         Sess.Shipped := Ship_Budget (Small);
         Receive (Sess, Small, R, True, Slice (SBuf, SL), M, Peer, O, Got, Res);
         Check ("a reply beyond the ship budget refused, nothing changes",
                Res = S_Limit and then Sess.Shipped = Ship_Budget (Small)
                and then Sess.Pending = Unit and then O.N = 0);
         Sess := Saved;
      end;
      Receive (Sess, Small, R, True, Slice (CBuf, CL), M, Peer, O, Got, Res);
      Check ("initiator: the confirm closes the root, complete",
             Res = S_OK and then O.N = 0 and then Sess.Pending = 0
             and then Complete (Sess));
   end;

   ----------------------------------------------------------------------
   --  (h) Two replicas converge to the union.
   ----------------------------------------------------------------------
   declare
      A, B   : Replica;
      Far    : constant Elem := Make (41, 16#6E#, 1, 9_000, 10);   --  above B's ceiling
      By3    : constant Elem := Make (42, 16#6E#, 3, 50, 10);      --  author 3 not in B's W
      Rounds, Delivered : Natural;
      All_OK, Done : Boolean;
      Union  : Natural;
   begin
      --  A: ceiling 10 000, W = {1, 2, 3} (as from a roster since
      --  dominated everywhere). B: ceiling 5 000, W = {1, 2}.
      Raise_Ceiling (A.Regs, 10_000);
      Add_W (A, Kome.Keys.To_Key256 (Pk (1)));
      Add_W (A, Kome.Keys.To_Key256 (Pk (2)));
      Add_W (A, Kome.Keys.To_Key256 (Pk (3)));
      Raise_Ceiling (B.Regs, 5_000);
      Add_W (B, Kome.Keys.To_Key256 (Pk (1)));
      Add_W (B, Kome.Keys.To_Key256 (Pk (2)));

      for E in Byte range 1 .. 20 loop                --  shared
         A.Els.Append (Make (E, 16#78#, 1, 100 + U48 (E), 8));
         B.Els.Append (Make (E, 16#78#, 1, 100 + U48 (E), 8));
      end loop;
      for E in Byte range 21 .. 40 loop               --  A only
         A.Els.Append (Make (E, 16#78#, 2, 200 + U48 (E), 8));
      end loop;
      A.Els.Append (Far);
      A.Els.Append (By3);
      for F in Byte range 16#61# .. 16#63# loop       --  A only, large
         A.Els.Append (Make (43, F, 1, 300, 20_000));
      end loop;
      for E in Byte range 50 .. 59 loop               --  B only
         B.Els.Append (Make (E, 16#78#, 1, 400 + U48 (E), 8));
      end loop;
      Union := 20 + 20 + 2 + 3 + 10;

      Check ("before: the far record is inadmissible at B",
             not Admissible (B.Regs, Far.Hdr) and then Admissible (A.Regs, Far.Hdr));
      Check ("before: the record by writer 3 is inadmissible at B",
             not Admissible (B.Regs, By3.Hdr));

      Run_Session (A, B, Rounds, Delivered, All_OK, Done);
      Check ("every message accepted and within the bound", All_OK);
      Check ("both sessions end Complete", Done);
      Check ("no frame mismatched its key", Refused_Mismatch = 0);
      Check ("replicas converge to the union",
             Same_Set (A, B) and then Natural (A.Els.Length) = Union);
      Check ("B now holds the far record and writer 3's record",
             Holds (B, Far.Key) and then Holds (B, By3.Key));
      Check ("registers joined: max ceiling, union of W",
             Ceil (A.Regs) = 10_000 and then Ceil (B.Regs) = 10_000
             and then In_W (B.Regs, Kome.Keys.To_Key256 (Pk (3)))
             and then Kome.Registers.Count (A.Regs) = 3
             and then Kome.Registers.Count (B.Regs) = 3);
      --  Rounds: 2 for the HELLOs, then at most 2s + 3 one-way messages
      --  along any chain, s = ⌈log₁₆ 45⌉ + ⌈log₁₆ 30⌉ = 4 splits.
      Check ("bounded number of rounds (" & Rounds'Image (2 .. Rounds'Image'Last)
             & " one-way rounds," & Delivered'Image & " frames delivered)",
             Rounds <= 2 + 2 * 4 + 3 and then Delivered >= 35);

      Run_Session (A, B, Rounds, Delivered, All_OK, Done);
      Check ("second session confirms at the root: HELLO, HELLO, RANGE, confirm",
             All_OK and then Done and then Rounds = 4 and then Delivered = 0
             and then Same_Set (A, B));
   end;

   if Failed then
      Set_Exit_Status (Failure);
   end if;
end Test_Reconcile;
