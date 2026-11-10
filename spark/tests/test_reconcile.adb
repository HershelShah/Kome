--  Test main for Kome.Reconcile (DESIGN.md §8, D12-D15; SIMPLIFY.md S9,
--  S11, S18-S21). It has these parts:
--  (a) The key order: its lemmas, Data_Lo, the 82-byte data and
--      authorization layouts (S18), and that Key_Lt is bytewise order on
--      the wire key (against the Ada lexicographic "<" on byte arrays;
--      Lemma_Key_Lt_First_Difference / Lemma_Key_Eq_Is_Bytewise execute).
--  (b) Snapshots: appends in order, no refusal changes the snapshot.
--      Seal and the prefix-sum fingerprint (Fingerprint_Of = Range_Fp).
--  (c) Windows and the cover on examples.
--  (d) Snapshot_Of (A12, S18): the snapshot of a frontier with
--      authorization records of three signers (whose slot order is not
--      key order) and data records holds exactly its records in key
--      order, the data part in the frontier's row order (entity-major,
--      DEL before PUT), linked to the frame table, with the digest of
--      the frontier; the No_Space refusal.
--  (e) The responder: the reply contract (Answers) on examples, the
--      confirm, the ship, the 16-way split as one RANGE message with 17
--      bounds (S19), the HAVE reply that tiles the range when its frames
--      do not fit one message, and the cuts on multiples of 64 for a
--      window of at least 1 024 elements (S20).
--  (f) The wire: Encode_Ranges / Decode_Of of every part, ELEMENTS and
--      HAVE items with frames and caller-derived keys (Item_Places), the
--      ROOT, the confirm, the HELLO, the prologue and the keys against
--      vectors/reconcile.txt; Decode refuses malformed inputs.
--  (g) The session:
--      * the HELLO from the digest states, before any snapshot (S21);
--      * the HELLO credential (A13, G12);
--      * the ROOT, its bounds by phase, refused at the initiator;
--      * a tiling answer in two ELEMENTS tiles, and a duplicate tile;
--      * the gate evaluated on every Receive and Next_Phase (S9): a
--        REVOKE of the peer's member applied after a batch aborts;
--      * the quarantine ends a session (S10);
--      * equal digests end the session after the HELLOs.
--  (h) Two replicas with different authorization and data records, and
--      one frame of 41 120 bytes, converge to the union in a two-phase
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
with Kome.Crypto;
with Kome.Digest;
with Kome.Frontier;    use Kome.Frontier;
with Kome.Views;       use Kome.Views;
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

   function K256 (B : Natural) return Key256 is
     (others => Word (B mod 256) * 16#0101_0101#);

   function Id (B : Natural) return Id128 is (others => Word (B));

   function DK (E : Natural; Sub : Kind_Code; F : Natural; H : Natural) return Elem_Key is
     (K => Data_Key_Tag, Ent => Id (E), Sub => Sub, FH => K256 (F), H => K256 (H));

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

   package Msg_Vectors is new Ada.Containers.Indefinite_Vectors
     (Positive, Byte_Array);

   function Slice (B : Msg_Buffer; L : Msg_Length) return Byte_Array is
     (B (0 .. L - 1));

   --  The wire bytes of a key (tag ‖ ent ‖ sub ‖ fh ‖ h).
   function To_Wire (K : Elem_Key) return Key_Wire is
     (Key_Wire'([Byte (K.K)] & Kome.Keys.To_Bytes (K.Ent) & [Byte (K.Sub)]
                & Kome.Keys.To_Bytes (K.FH) & Kome.Keys.To_Bytes (K.H)));

   --  A frame of Len (>= 82) bytes that starts with the wire key of K: the
   --  test derives the key of a received frame from it, as a caller
   --  derives it from the decoded record.
   function Frame_For (K : Elem_Key; Len : Positive; Seed : Natural := 0) return Byte_Array is
     (Byte_Array (To_Wire (K)) & Fill (Len - Key_Wire_Len, Seed));

   No_Keys : constant Key_List := [others => Min_Key];

   --  The keys of the items of Raw, from their frames.
   function Keys_Of (Raw : Byte_Array) return Key_List is
      PL : constant Places := Item_Places (Raw);
      K  : Key_List := No_Keys;
   begin
      if PL.OK then
         for T in 1 .. PL.N loop
            if PL.Len (T) >= Key_Wire_Len then
               K (T) := Wire_Key (Raw, PL.Off (T));
            end if;
         end loop;
      end if;
      return K;
   end Keys_Of;

   --  The prefix-sum table of S (Seal, D15), sized for its count.
   function Table_Of (S : Snapshot) return Prefix is
   begin
      return P : Prefix (Prefix_Slots (Kome.Reconcile.Count (S))) do
         Seal (S, P);
      end return;
   end Table_Of;

   --  The number of our elements in [Lo, Hi): My_Count, which is ghost.
   function Cnt (S : Snapshot; Lo, Hi : Elem_Key) return Natural is
     (Window (S, Lo, Hi).Last + 1 - Window (S, Lo, Hi).First);

   --  The reply contract Answers (ghost in the spec), with Cnt for
   --  My_Count, so a test can evaluate it on any outbox.
   function Answers_T (S : Snapshot; M : Message; O : Outbox) return Boolean is
     ((if M.Kind = M_Have then O.N = 0 else O.N >= 1)
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

   function Range_Msg (Lo, Hi : Elem_Key; Count : Natural := 0;
                       Fp : Hash256 := [others => 0]) return Message is
     (Kind => M_Range, Root => False, Lo => Lo, Hi => Hi, Count => Count, Fp => Fp,
      N => 0, Items => <>);

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

   --  The digest state of a list of hashes.
   function State_Of_List (L : Kome.Digest.Hash_Array) return Kome.Digest.Digest_State is
     (Kome.Digest.Digest_Of (L));

   ----------------------------------------------------------------------
   --  Replicas for the session tests: a sorted list of (key, frame), and
   --  the snapshot, frame table and digest states built from it.
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
      return [];
   end Frame_Of_Key;

   procedure Add (R : in out Replica; K : Elem_Key; F : Byte_Array) is
   begin
      R.Els.Append (Elem'(Len => F'Length, Key => K, F => F));
   end Add;

   procedure Add_Elem (R : in out Replica; K : Elem_Key; Len : Positive) is
   begin
      Add (R, K, Frame_For (K, Len, Natural (K.H.W0 mod 200)));
   end Add_Elem;

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

   --  Snapshot, frame table (element I has source I) and the two digest
   --  states of R.
   procedure Build
     (R  : in out Replica;
      S  : in out Snapshot;
      T  : in out Frame_Table;
      DA : out Kome.Digest.Digest_State;
      DD : out Kome.Digest.Digest_State)
   is
      St : Snap_Status;
      NA, ND : Natural := 0;
   begin
      Elem_Sort.Sort (R.Els);
      Clear (S);
      Clear_Table (T);
      for E of R.Els loop
         if E.Key.K < Data_Key_Tag then
            NA := NA + 1;
         else
            ND := ND + 1;
         end if;
      end loop;
      declare
         LA : Kome.Digest.Hash_Array (1 .. NA);
         LD : Kome.Digest.Hash_Array (1 .. ND);
         IA, ID : Natural := 0;
         I : Natural := 0;
      begin
         for E of R.Els loop
            I := I + 1;
            Add_Frame (T, E.F, St);
            if St /= Snap_OK then
               raise Program_Error with "add_frame " & St'Image;
            end if;
            Append (S, E.Key, E.F'Length, I, St);
            if St /= Snap_OK then
               raise Program_Error with "append " & St'Image;
            end if;
            if E.Key.K < Data_Key_Tag then
               IA := IA + 1;
               LA (IA) := E.Key.H;
            else
               ID := ID + 1;
               LD (ID) := E.Key.H;
            end if;
         end loop;
         DA := State_Of_List (LA);
         DD := State_Of_List (LD);
      end;
   end Build;

   ----------------------------------------------------------------------
   --  The fixture: a collection with a founding roster that lists two
   --  members (DH1, DH2), its frame as the credential, and the frontier
   --  F0 that holds it (ROSTER_eff). DHX is a stranger.
   ----------------------------------------------------------------------

   Salt_A : constant Salt := Salt (Fill (Salt_Len, 90));
   Box_A  : constant Pubkey := Good_DH (15);
   Day    : constant U48 := 86_400_000;
   TTL    : constant U48 := 30 * Day;
   Mem    : constant Byte_Array := Members_Of (2, 33);
   DH1    : constant Pubkey := Pubkey (Mem (Pubkey_Len .. 2 * Pubkey_Len - 1));
   DH2    : constant Pubkey :=
     Pubkey (Mem (Member_Len + Pubkey_Len .. Member_Len + 2 * Pubkey_Len - 1));
   DHX    : constant Pubkey := Good_DH (200);

   function Hsh (B : Natural) return Key256 is (W0 => Word (B), others => 5);

   procedure Recv
     (Sess : in out Session; S : Snapshot; P : Prefix; F : State; Eff : Roster_Record;
      Input : Byte_Array; Part : Positive; O : out Outbox; Rt : out Root_Out;
      M : out Message; Got : out Delivery; Res : out Session_Status)
   is
      Pr : Hello;
   begin
      Receive (Sess, S, P, F, Eff, Input, Part, Keys_Of (Input), M, Pr, O, Got, Rt, Res);
   end Recv;

   function Root_Bytes (R : Root_Out) return Byte_Array is
      Buf : Msg_Buffer;
      L   : Msg_Length;
   begin
      Encode_Root (R, Buf, L);
      return Slice (Buf, L);
   end Root_Bytes;

   function Plan_Bytes (S : Snapshot; T : Frame_Table; P : Plan) return Byte_Array is
      Buf : Msg_Buffer;
      L   : Msg_Length;
   begin
      Encode (S, T, P, Buf, L);
      return Slice (Buf, L);
   end Plan_Bytes;

   function Ranges_Bytes (S : Snapshot; O : Outbox) return Byte_Array is
      PS  : constant Prefix := Table_Of (S);
      Buf : Msg_Buffer;
      L   : Msg_Length;
   begin
      Encode_Ranges (S, PS, O, Buf, L);
      return Slice (Buf, L);
   end Ranges_Bytes;

   --  The wire messages of an outbox: one RANGE message for a split, one
   --  message for each ELEMENTS or HAVE plan.
   procedure Emit (S : Snapshot; P : Prefix; T : Frame_Table; O : Outbox;
                   Q : in out Msg_Vectors.Vector) is
      Buf : Msg_Buffer;
      L   : Msg_Length;
   begin
      if O.N = 0 then
         return;
      end if;
      if All_Kind (O, P_Range) then
         Encode_Ranges (S, P, O, Buf, L);
         Q.Append (Slice (Buf, L));
      else
         for I in 1 .. O.N loop
            Encode (S, T, O.P (I), Buf, L);
            Q.Append (Slice (Buf, L));
         end loop;
      end if;
   end Emit;

   function Parts_Of (Raw : Byte_Array) return Positive is
     (if Raw'Length >= 2 and then Raw (Raw'First) = Tag_Range and then Raw (Raw'First + 1) >= 1
      then Natural (Raw (Raw'First + 1)) else 1);

   procedure Run_All;

   --  A State holds Signers_Max * Slice_Max authorization rows, and the
   --  snapshots and tables are large. Under -gnata, each Post evaluation
   --  copies them, so the checks run in a task with a large stack.
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
      Root_SK : Kome.Crypto.Secret_Key;
      Root_PK : Pubkey;
   begin
   Kome.Crypto.Key_Pair (Kome.Crypto.Seed (Fill (Kome.Crypto.Seed_Len, 3)), Root_SK, Root_PK);
   declare
      Cid_A : constant Hash256 := Cid_Of (Root_PK, Salt_A, TTL);
      Fnd   : constant Key256 := To_Key256 (Root_PK);
      R_Eff : constant Roster_Record :=
        Make_Roster (Cid_A, Root_PK, Founding_Cap, Zero_Sig, Box_A, 1, 5000, Mem);
      RH    : constant Header := To_Header (Cid_A, R_Eff);
      Cred_T : constant Byte_Array := Encode (R_Eff);
      S1_Key : constant Key256 := Member_Key (R_Eff.C, 1);
      F0    : State := Empty (Fnd, 64);
      St    : Status;
      SS    : Snap_Status;
   begin
      Apply (F0, RH, 1, St);
      Check ("fixture: the founding roster is ROSTER_eff and the gate admits DH1 and DH2",
             St = OK and then Gate_Open (Cid_A, F0, R_Eff, DH1)
             and then Gate_Open (Cid_A, F0, R_Eff, DH2)
             and then not Gate_Open (Cid_A, F0, R_Eff, DHX));

      ------------------------------------------------------------------
      --  (a) Keys
      ------------------------------------------------------------------
      declare
         Put1 : constant Header :=
           (K => K_Put, Ent => Id (7), FH => K256 (9),
            V => (T => 5, Author => K256 (1), Seq => 1, H => Hsh (11)), Issuer => Zero_Key);
         Del1 : constant Header :=
           (K => K_Del, Ent => Id (7), FH => Zero_Key,
            V => (T => 6, Author => K256 (1), Seq => 2, H => Hsh (12)), Issuer => Zero_Key);
         Gr1  : constant Header :=
           (K => K_Grant, Ent => Zero_Id, FH => Zero_Key,
            V => (T => U48'Last, Author => K256 (3), Seq => 0, H => Hsh (13)), Issuer => K256 (40));
         KP : constant Elem_Key := Key_Of (Put1);
         KD : constant Elem_Key := Key_Of (Del1);
         KG : constant Elem_Key := Key_Of (Gr1);
         W  : constant Key_Wire := To_Wire (KG);
         Ks : constant array (1 .. 8) of Elem_Key :=
           [Min_Key, Key_Of (RH), KG, Data_Lo, KD, KP, DK (7, 1, 10, 0), Max_Key];
         Order_OK : Boolean := True;
      begin
         Check ("S18: a data key is 03 ‖ ent ‖ sub ‖ fh ‖ h, sub = 0 for a DEL, 1 for a PUT",
                KP.K = 3 and then KP.Ent = Id (7) and then KP.Sub = 1 and then KP.FH = K256 (9)
                and then KP.H = Hsh (11) and then KD.Sub = 0 and then KD.FH = Zero_Key);
         Check ("S18: an authorization key is tag ‖ 0^17 ‖ signer ‖ h",
                KG.K = 2 and then W (0) = 2
                and then (for all I in 1 .. 17 => W (I) = 0)
                and then Kome.Keys.To_Key256 (W (18 .. 49)) = K256 (40)
                and then Kome.Keys.To_Key256 (W (50 .. 81)) = Hsh (13)
                and then Key_Of (RH).K = 0 and then Key_Of (RH).FH = Fnd);
         Check ("Data_Lo = 03 ‖ 0^81 splits authorization from data",
                To_Wire (Data_Lo) = Key_Wire'([3] & [1 .. 81 => 0])
                and then Key_Lt (KG, Data_Lo) and then Key_Le (Data_Lo, KD));
         Lemma_Key_Ranges (Put1);
         Lemma_Key_Ranges (Gr1);
         Lemma_Data_Key_Order (Del1, Put1);
         Check ("DEL before PUT of one entity; entity-major (Lemma_Data_Key_Order)",
                Key_Lt (KD, KP) and then Key_Lt (KP, DK (8, 0, 0, 0)));
         for I in Ks'Range loop
            for J in Ks'Range loop
               Lemma_Key_Trichotomy (Ks (I), Ks (J));
               Kome.Reconcile.Lemma_Key_Eq_Is_Bytewise (To_Wire (Ks (I)), To_Wire (Ks (J)));
               if Key_Lt (Ks (I), Ks (J)) /= (To_Wire (Ks (I)) < To_Wire (Ks (J)))
                 or else Key_Lt (Ks (I), Ks (J)) /= (I < J)
                 or else (Wire_Key (To_Wire (Ks (I)), 0) = Ks (I)) = False
               then
                  Order_OK := False;
               end if;
               if I /= J then
                  declare
                     A : constant Key_Wire := To_Wire (Ks (I));
                     B : constant Key_Wire := To_Wire (Ks (J));
                     D : Natural := 0;
                  begin
                     while A (D) = B (D) loop
                        D := D + 1;
                     end loop;
                     Lemma_Key_Lt_First_Difference (A, B, D);
                  end;
               end if;
            end loop;
         end loop;
         Check ("Key_Lt is the bytewise order of the 82-byte wire keys", Order_OK);
      end;

      ------------------------------------------------------------------
      --  (b), (c) Snapshots, prefix sums, windows
      ------------------------------------------------------------------
      declare
         S : Snapshot (Cap => 200);
         Keep : Boolean := True;
      begin
         Clear (S);
         for I in 1 .. 150 loop
            Append (S, DK (I, 1, I, I), 100 + I, I, SS);
            Keep := Keep and then SS = Snap_OK;
         end loop;
         Check ("150 ascending appends", Keep and then Kome.Reconcile.Count (S) = 150);
         Append (S, DK (3, 1, 3, 3), 50, 1, SS);
         Check ("an append below the last key is Snap_Unsorted and changes nothing",
                SS = Snap_Unsorted and then Kome.Reconcile.Count (S) = 150);
         declare
            P  : constant Prefix := Table_Of (S);
            FP : Hash256;
            OK : Boolean := True;
            type AB is record
               A, B : Natural;
            end record;
            --  Ranges that cross, end on and span 64-element blocks, end
            --  in the tail, and are empty.
            Ranges : constant array (1 .. 9) of AB :=
              [(1, 150), (1, 64), (65, 128), (33, 96), (60, 70), (129, 150),
               (150, 150), (40, 39), (100, 140)];
         begin
            for R of Ranges loop
               Fingerprint_Of (S, P, R.A, R.B, FP);
               OK := OK and then FP = Range_Fp (S, R.A, R.B);
            end loop;
            Check ("Fingerprint_Of (prefix sums) = Range_Fp on sampled ranges (D15)", OK);
         end;
         declare
            W1 : constant Span := Window (S, DK (10, 0, 0, 0), DK (20, 0, 0, 0));
            W2 : constant Span := Window (S, Min_Key, Data_Lo);
            W3 : constant Span := Window (S, DK (10, 1, 10, 10), DK (10, 1, 10, 11));
         begin
            Check ("windows: [e10, e20) holds 10 .. 19, the auth range none, one exact key",
                   W1.First = 10 and then W1.Last = 19 and then W2.Last + 1 = W2.First
                   and then W3.First = 10 and then W3.Last = 10);
         end;
      end;

      ------------------------------------------------------------------
      --  (d) Snapshot_Of
      ------------------------------------------------------------------
      declare
         F  : State := F0;
         --  Grants of three signers that reach F in the order 30, 10, 20,
         --  so the slot order is not the key order.
         function Gr (Issuer, Subject, H : Natural) return Header is
           (K => K_Grant, Ent => Zero_Id, FH => Zero_Key,
            V => (T => U48'Last, Author => K256 (Subject), Seq => 0, H => Hsh (H)),
            Issuer => (if Issuer = 0 then Fnd else K256 (Issuer)));
         function Pt (E, Fld, T : Natural) return Header is
           (K => K_Put, Ent => Id (E), FH => K256 (Fld),
            V => (T => U48 (T), Author => K256 (50), Seq => U48 (T), H => Hsh (1000 + E * 10 + Fld)),
            Issuer => Zero_Key);
         function Dl (E, T : Natural) return Header is
           (K => K_Del, Ent => Id (E), FH => Zero_Key,
            V => (T => U48 (T), Author => K256 (50), Seq => U48 (T), H => Hsh (2000 + E)),
            Issuer => Zero_Key);
         T  : Frame_Table (Cap => 64, Pool_Cap => 64 * 300);
         S  : Snapshot (Cap => 64);
         Tiny : Snapshot (Cap => 3);
         Tg : U64 := 10;
         procedure Ap (H : Header) is
         begin
            Tg := Tg + 1;
            Apply (F, H, Tg, St);
            if St /= OK then
               raise Program_Error with "apply " & St'Image;
            end if;
         end Ap;
      begin
         Ap (Gr (0, 50, 1));            --  50 is a writer
         Ap (Gr (0, 30, 2));
         Ap (Gr (0, 10, 3));
         Ap (Gr (0, 20, 4));
         Ap (Gr (30, 31, 5));
         Ap (Gr (10, 11, 6));
         Ap (Gr (20, 21, 7));
         Ap (Gr (10, 12, 8));
         Ap (Pt (5, 2, 100));
         Ap (Pt (3, 1, 101));
         Ap (Dl (5, 50));
         Ap (Pt (5, 1, 102));
         Ap (Pt (9, 4, 103));
         Clear_Table (T);
         for I in 1 .. Kome.Frontier.Count (F) loop
            Add_Frame (T, Fill (90 + I, I), SS);
         end loop;
         Snapshot_Of (F, T, S, SS);
         declare
            N  : constant Natural := Kome.Reconcile.Count (S);
            DC : constant Natural := Data_Count (F);
            OK_Src, In_Order, Data_Order : Boolean := True;
         begin
            Check ("Snapshot_Of: OK, |S| = |F|, linked to the table",
                   SS = Snap_OK and then N = Kome.Frontier.Count (F) and then Linked (S, T)
                   and then Valid (S));
            for I in 1 .. N loop
               OK_Src := OK_Src
                 and then Key (S, I) = Key_Of (Held (F, Source (S, I)))
                 and then Elem_Frame (S, T, I) = Table_Frame (T, Source (S, I));
               if I > 1 then
                  In_Order := In_Order and then Key_Lt (Key (S, I - 1), Key (S, I));
               end if;
            end loop;
            --  The data part of S is the data row of F, in its order.
            for I in 1 .. DC loop
               Data_Order := Data_Order and then Source (S, N - DC + I) = I;
            end loop;
            Check ("each element is its held record with its frame, keys ascending",
                   OK_Src and then In_Order);
            Check ("S18: the data part is the frontier's data row, in its order (no sort)",
                   Data_Order and then DC = 5);
            Check ("the authorization slots were not in key order (the insertion sorted them)",
                   (for some I in 2 .. N - DC => Source (S, I - 1) > Source (S, I)));
            Check ("T6: the snapshot digest is the frontier digest",
                   Range_Fp (S, 1, N) = Kome.Digest.Frontier_Digest (F));
         end;
         Snapshot_Of (F, T, Tiny, SS);
         Check ("Snapshot_Of refuses a frontier above the capacity (Snap_No_Space), empty",
                SS = Snap_No_Space and then Kome.Reconcile.Count (Tiny) = 0);
      end;

      ------------------------------------------------------------------
      --  (e) The responder
      ------------------------------------------------------------------
      declare
         S  : Snapshot (Cap => 64);
         T  : Frame_Table (Cap => 64, Pool_Cap => 64 * 41_200);
         R  : Replica;
         DA, DD : Kome.Digest.Digest_State;
      begin
         for I in 1 .. 40 loop
            Add_Elem (R, DK (I, 1, I, I), 120);
         end loop;
         Build (R, S, T, DA, DD);
         declare
            P   : constant Prefix := Table_Of (S);
            O   : Outbox;
            Got : Delivery;
            All_M : constant Message := Range_Msg (Data_Lo, Max_Key, 40, Range_Fp (S, 1, 40));
            Wrong : constant Message := Range_Msg (Data_Lo, Max_Key, 40, [others => 7]);
            Small : constant Message := Range_Msg (DK (3, 0, 0, 0), DK (6, 0, 0, 0), 9);
         begin
            Respond (S, P, All_M, O, Got);
            Check ("equal count and fingerprint: the confirm", Is_Confirm (O, Data_Lo, Max_Key)
                   and then Answers_T (S, All_M, O));
            Respond (S, P, Wrong, O, Got);
            Check ("a different fingerprint over 40: a 16-way split of RANGE parts",
                   O.N = 16 and then All_Kind (O, P_Range) and then Tiles (O, Data_Lo, Max_Key)
                   and then Answers_T (S, Wrong, O));
            declare
               B : constant Byte_Array := Ranges_Bytes (S, O);
               OK : Boolean := B'Length = Range_Msg_Len (16) and then B'Length = 2_004;
            begin
               for J in 1 .. 16 loop
                  declare
                     D : constant Decoding := Decode_Of (B, J, No_Keys);
                  begin
                     OK := OK and then D.OK and then D.M.Lo = O.P (J).Lo and then D.M.Hi = O.P (J).Hi
                       and then D.M.Count = O.P (J).Last + 1 - O.P (J).First
                       and then D.M.Fp = Range_Fp (S, O.P (J).First, O.P (J).Last);
                  end;
               end loop;
               Check ("S19: the split is one RANGE message with 17 bounds; each part decodes",
                      OK and then not Decode_Of (B, 17, No_Keys).OK);
            end;
            Respond (S, P, Small, O, Got);
            Check ("a small window (3 elements): ELEMENTS with all of them",
                   O.N = 1 and then O.P (1).Kind = P_Elements and then O.P (1).First = 3
                   and then O.P (1).Last = 5 and then Answers_T (S, Small, O));
            declare
               B  : constant Byte_Array := Plan_Bytes (S, T, O.P (1));
               PL : constant Places := Item_Places (B);
               Ks : constant Key_List := Keys_Of (B);
               D  : constant Decoding := Decode_Of (B, 1, Ks);
               Bad : Key_List := Ks;
            begin
               Check ("ELEMENTS items are frames only; the keys come from the frames",
                      PL.OK and then PL.N = 3
                      and then B (PL.Off (1) .. PL.Off (1) + PL.Len (1) - 1) = Elem_Frame (S, T, 3)
                      and then D.OK and then D.M.Kind = M_Elements and then D.M.N = 3
                      and then D.M.Items (2).Key = Key (S, 4));
               Bad (2) := Key (S, 1);
               Check ("Decode refuses item keys that are not ascending in [lo, hi)",
                      not Decode_Of (B, 1, Bad).OK);
               Check ("Decode refuses a length mismatch and a part 2 of an ELEMENTS",
                      not Decode_Of (B (B'First .. B'Last - 1), 1, Ks).OK
                      and then not Decode_Of (B, 2, Ks).OK);
               --  The responder of the ELEMENTS: we hold 3, 4, 5; the
               --  message lists 3 and 5 of ours and a new key.
               declare
                  M : Message := D.M;
               begin
                  M.Items (2).Key := DK (4, 0, 0, 1);
                  Respond (S, P, M, O, Got);
                  Check ("ELEMENTS: deliver the new key, HAVE back our element 4",
                         Got (2) and then not Got (1) and then not Got (3)
                         and then O.N = 1 and then O.P (1).Kind = P_Have and then O.P (1).N = 1
                         and then O.P (1).Items (1) = 4 and then Answers_T (S, M, O));
               end;
            end;
         end;
      end;

      --  HAVE that tiles: our 3 elements in the range have frames of
      --  20 000 bytes, which do not fit one message.
      declare
         S  : Snapshot (Cap => 8);
         T  : Frame_Table (Cap => 8, Pool_Cap => 8 * 20_000);
         R  : Replica;
         DA, DD : Kome.Digest.Digest_State;
      begin
         for I in 1 .. 4 loop
            Add_Elem (R, DK (I, 1, I, I), 20_000);
         end loop;
         Build (R, S, T, DA, DD);
         declare
            P   : constant Prefix := Table_Of (S);
            O   : Outbox;
            Got : Delivery;
            M   : constant Message :=
              (Kind => M_Elements, Root => False, Lo => DK (2, 0, 0, 0), Hi => Max_Key,
               Count => 0, Fp => [others => 0], N => 0, Items => <>);
         begin
            Respond (S, P, M, O, Got);
            Check ("S19: a HAVE whose frames do not fit tiles the range, one element each",
                   O.N = 3 and then All_Kind (O, P_Have) and then Tiles (O, M.Lo, M.Hi)
                   and then O.P (2).Lo = Key (S, 3) and then O.P (2).Hi = Key (S, 4)
                   and then Have_Exact (S, M, O) and then Answers_T (S, M, O));
            Respond (S, P, (M with delta Lo => DK (9, 0, 0, 0)), O, Got);
            Check ("an ELEMENTS with nothing of ours in range: the empty HAVE (confirm)",
                   Is_Confirm (O, DK (9, 0, 0, 0), Max_Key));
            declare
               B : constant Byte_Array := Plan_Bytes (S, T, O.P (1));
               Buf : Msg_Buffer := [others => 0];
            begin
               Buf (0 .. B'Length - 1) := B;
               Lemma_Confirm_Accepted (S, O.P (1), Buf);
               Check ("the confirm decodes (Empty_Wire_OK)",
                      Empty_Wire_OK (B) and then Decode_Of (B, 1, No_Keys).OK
                      and then Decode_Of (B, 1, No_Keys).M.Kind = M_Have);
            end;
         end;
      end;

      --  S20: the cuts of a split of at least 1 024 elements are on
      --  multiples of 64, strictly increasing, inside the window, and each
      --  child is not empty. (Split uses them; an end-to-end split of a
      --  1 024-element snapshot is too slow under -gnata, where each
      --  prefix-sum check recomputes the sums.)
      declare
         OK : Boolean := True;
         type Nat_List is array (1 .. 6) of Positive;
         Firsts : constant Nat_List := [1, 2, 63, 64, 65, 500];
         Sizes  : constant Nat_List := [1_024, 1_025, 1_100, 2_047, 4_096, 10_001];
      begin
         for First of Firsts loop
            for N of Sizes loop
               for T in 1 .. Split_Fanout - 1 loop
                  declare
                     C    : constant Natural := Cut_At (First, N, T);
                     Prev : constant Natural :=
                       (if T = 1 then First - 1 else Cut_At (First, N, T - 1));
                  begin
                     OK := OK and then C mod 64 = 0 and then C > Prev
                       and then C >= First and then C < First + N - 1;
                  end;
               end loop;
            end loop;
         end loop;
         Check ("S20: the 15 interior cuts of a window of >= 1 024 are multiples of 64, "
                & "increasing, inside the window", OK);
      end;

      ------------------------------------------------------------------
      --  (f) Wire vectors
      ------------------------------------------------------------------
      declare
         Path  : constant String := Find ("vectors/reconcile.txt");
         File  : File_Type;
         Line  : String (1 .. 40_000);
         Last  : Natural;
         type Bounds is record
            First, Last : Natural;
         end record;
         Fields   : array (1 .. 8) of Bounds;
         N_Fields : Natural;
         N_Vec    : Natural := 0;
         All_OK   : Boolean := True;
         Buf      : Msg_Buffer;
         L        : Msg_Length;

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

         procedure Mark (Name : String; Cond : Boolean) is
         begin
            N_Vec := N_Vec + 1;
            if not Cond then
               All_OK := False;
               Put_Line ("  vector mismatch: " & Name);
            end if;
         end Mark;
      begin
         if not Ada.Directories.Exists (Path) then
            Check ("vectors present (" & Path & ")", False);
         else
            Open (File, In_File, Path);
            while not End_Of_File (File) loop
               Get_Line (File, Line, Last);
               if Last > 0 and then Line (1) /= '#' then
                  Tokenize (Line (1 .. Last));
                  declare
                     Kind : constant String := Field (1);
                     Wire : constant Byte_Array := From_Hex (Field (N_Fields));
                  begin
                     if Kind = "dkey" then
                        declare
                           H : constant Header :=
                             (K => (if Field (3) = "del" then K_Del else K_Put),
                              Ent => To_Id128 (From_Hex (Field (2))),
                              FH => To_Key256 (From_Hex (Field (4))),
                              V => (T => 0, Author => Zero_Key, Seq => 0,
                                    H => To_Key256 (From_Hex (Field (5)))),
                              Issuer => Zero_Key);
                        begin
                           Mark ("dkey", Byte_Array (To_Wire (Key_Of (H))) = Wire);
                        end;
                     elsif Kind = "akey" then
                        declare
                           H : constant Header :=
                             (K => Kome.Headers.Kind'Val (Natural'Value (Field (2))),
                              Ent => Zero_Id, FH => Zero_Key,
                              V => (T => 0, Author => Zero_Key, Seq => 0,
                                    H => To_Key256 (From_Hex (Field (4)))),
                              Issuer => To_Key256 (From_Hex (Field (3))));
                        begin
                           Mark ("akey", Byte_Array (To_Wire (Key_Of (H))) = Wire);
                        end;
                     elsif Kind = "prologue" then
                        Mark ("prologue", Byte_Array (Prologue (From_Hex (Field (2)))) = Wire);
                     elsif Kind = "hello" then
                        declare
                           Cr : constant Byte_Array := From_Hex (Field (5));
                           H  : Hello;
                           OK : Boolean;
                        begin
                           Encode_Hello (Word'Value (Field (2)), Word'Value (Field (3)),
                                         From_Hex (Field (4)), Cr, Buf, L);
                           Decode_Hello (Wire, H, OK);
                           Mark ("hello", Slice (Buf, L) = Wire and then OK
                                 and then H.N_Data = Word'Value (Field (3))
                                 and then H.Cred_Len = Cr'Length);
                        end;
                     elsif Kind = "root" then
                        declare
                           R : constant Root_Out :=
                             (Send => True, Count => Natural'Value (Field (2)),
                              Fp => From_Hex (Field (3)));
                           D : constant Decoding := Decode_Of (Wire, 1, No_Keys);
                        begin
                           Mark ("root", Root_Bytes (R) = Wire and then D.OK and then D.M.Root
                                 and then D.M.Count = R.Count and then D.M.Fp = R.Fp
                                 and then not Decode_Of (Wire, 2, No_Keys).OK);
                        end;
                     elsif Kind = "range" then
                        declare
                           K   : constant Positive := Positive'Value (Field (2));
                           Bnd : constant Byte_Array := From_Hex (Field (3));
                           Fps : constant Byte_Array := From_Hex (Field (5));
                           OK  : Boolean := Wire'Length = Range_Msg_Len (K);
                           C   : Natural := Fields (4).First;
                        begin
                           for J in 1 .. K loop
                              declare
                                 D : constant Decoding := Decode_Of (Wire, J, No_Keys);
                                 E : Natural := C;
                              begin
                                 while E <= Fields (4).Last and then Line (E) /= ',' loop
                                    E := E + 1;
                                 end loop;
                                 OK := OK and then D.OK and then not D.M.Root
                                   and then D.M.Lo = Wire_Key (Bnd, 82 * (J - 1))
                                   and then D.M.Hi = Wire_Key (Bnd, 82 * J)
                                   and then D.M.Count = Natural'Value (Line (C .. E - 1))
                                   and then D.M.Fp = Fps (32 * (J - 1) .. 32 * J - 1);
                                 C := E + 1;
                              end;
                           end loop;
                           Mark ("range", OK and then not Decode_Of (Wire, K + 1, No_Keys).OK);
                        end;
                     elsif Kind = "elements" then
                        declare
                           PL : constant Places := Item_Places (Wire);
                           D  : constant Decoding := Decode_Of (Wire, 1, Keys_Of (Wire));
                           Fr : constant String := Field (5);
                           OK : Boolean := PL.OK and then D.OK
                             and then D.M.Kind = (if Field (2) = "3" then M_Elements else M_Have)
                             and then D.M.Lo = Wire_Key (From_Hex (Field (3)), 0)
                             and then D.M.Hi = Wire_Key (From_Hex (Field (4)), 0);
                           C  : Natural := Fr'First;
                        begin
                           if Fr /= "-" then
                              for T in 1 .. PL.N loop
                                 declare
                                    E : Natural := C;
                                 begin
                                    while E <= Fr'Last and then Fr (E) /= ',' loop
                                       E := E + 1;
                                    end loop;
                                    OK := OK and then Wire (PL.Off (T) .. PL.Off (T) + PL.Len (T) - 1)
                                                        = From_Hex (Fr (C .. E - 1));
                                    C := E + 1;
                                 end;
                              end loop;
                           else
                              OK := OK and then PL.N = 0 and then Empty_Wire_OK (Wire);
                           end if;
                           Mark ("elements", OK);
                        end;
                     else
                        Mark ("unknown vector kind " & Kind, False);
                     end if;
                  end;
               end if;
            end loop;
            Close (File);
            Check ("wire vectors: keys, prologue, HELLO, ROOT, RANGE parts, ELEMENTS items ("
                   & N_Vec'Image & " vectors)", All_OK and then N_Vec = 23);
         end if;
      end;

      --  Malformed inputs.
      declare
         Rt : constant Byte_Array := Root_Bytes ((Send => True, Count => 3, Fp => [others => 1]));
         Big : Byte_Array := Rt;
         Rg : constant Byte_Array := From_Hex ("02" & "02");
      begin
         Big (1 .. 6) := [0, 0, 16#FF#, 0, 0, 0];
         Check ("Decode refuses a ROOT count above Elem_Max, a short ROOT, an empty input",
                not Decode_Of (Big, 1, No_Keys).OK
                and then not Decode_Of (Rt (0 .. Rt'Last - 1), 1, No_Keys).OK
                and then not Decode_Of (Rt (1 .. 0), 1, No_Keys).OK);
         Check ("Decode refuses a RANGE with a length that k does not give",
                not Decode_Of (Rg, 1, No_Keys).OK);
      end;

      ------------------------------------------------------------------
      --  (g) The session
      ------------------------------------------------------------------
      declare
         --  Two replicas: A has the founding roster and data e1 .. e6;
         --  B has the roster, e1 .. e3 and e7 (frames of 21 000 bytes, so
         --  that an ELEMENTS answer of B tiles in several messages).
         RA, RB : Replica;
         SA, SB : Snapshot (Cap => 32);
         TA, TB : Frame_Table (Cap => 32, Pool_Cap => 32 * 21_000);
         AA, AD, BA, BD : Kome.Digest.Digest_State;
         Empty_S : Snapshot (Cap => 0);
         EP : Prefix (1);
         Ses_I, Ses_R : Session (Oblig_Cap => 64);
         Buf : Msg_Buffer;
         L   : Msg_Length;
         Rt  : Root_Out;
         O   : Outbox;
         M   : Message;
         Got : Delivery;
         Res : Session_Status;
      begin
         Add (RA, Key_Of (RH), Frame_For (Key_Of (RH), 300));
         Add (RB, Key_Of (RH), Frame_For (Key_Of (RH), 300));
         for I in 1 .. 6 loop
            Add_Elem (RA, DK (I, 1, I, I), 21_000);
         end loop;
         for I in 1 .. 3 loop
            Add_Elem (RB, DK (I, 1, I, I), 21_000);
         end loop;
         Add_Elem (RB, DK (7, 1, 7, 7), 21_000);
         Build (RA, SA, TA, AA, AD);
         Build (RB, SB, TB, BA, BD);
         Clear (Empty_S);
         Seal (Empty_S, EP);

         --  S21: the HELLO comes from the digest states, before any
         --  snapshot; a Receive in Gate needs none (an empty one).
         Start (Ses_I, Initiator, Cid_A, DH2);
         Start (Ses_R, Responder, Cid_A, DH1);
         Check ("Start: Gate, nothing sent", Ses_I.P = Gate and then Ses_R.P = Gate);
         Recv (Ses_I, Empty_S, EP, F0, R_Eff, Root_Bytes ((True, 1, [others => 0])), 1, O, Rt, M,
               Got, Res);
         Check ("a ROOT before the HELLO exchange is unexpected", Res = S_Unexpected);
         Admit (Ses_I, F0, R_Eff, AA, AD, Cred_T, Buf, L, Rt);
         declare
            HA : constant Byte_Array := Slice (Buf, L);
         begin
            Check ("Admit: the HELLO carries n_auth, n_data and the union digest (S21)",
                   Ses_I.Hello_Sent and then not Rt.Send
                   and then Wire_U32 (Buf, Hello_O_NAuth) = 1
                   and then Wire_U32 (Buf, Hello_O_NData) = 6
                   and then Buf (Hello_O_Digest .. Hello_O_Digest + 31) = Range_Fp (SA, 1, 7));
            --  The credential checks at B.
            declare
               X : Session (Oblig_Cap => 8);
               Mem_X : constant Byte_Array := Members_Of (1, 77);
               R_X : constant Roster_Record :=
                 Make_Roster (Cid_A, Root_PK, Founding_Cap, Zero_Sig, Box_A, 1, 5000, Mem_X);
               HX : Byte_Array := HA;
            begin
               Encode_Hello (1, 6, Range_Fp (SA, 1, 7), Encode (R_X), Buf, L);
               Start (X, Responder, Cid_A, DH1);
               Recv (X, Empty_S, EP, F0, R_Eff, Slice (Buf, L), 1, O, Rt, M, Got, Res);
               Check ("A13: a HELLO credential that does not list the peer aborts",
                      Res = S_Aborted and then X.Aborted);
               Encode_Hello (1, 6, Range_Fp (SA, 1, 7), Fill (300, 1), Buf, L);
               Start (X, Responder, Cid_A, DH1);
               Recv (X, Empty_S, EP, F0, R_Eff, Slice (Buf, L), 1, O, Rt, M, Got, Res);
               Check ("a credential that is not a ROSTER frame aborts", Res = S_Aborted);
               HX (HX'Last) := HX (HX'Last) xor 1;
               Start (X, Responder, Cid_A, DHX);
               Recv (X, Empty_S, EP, F0, R_Eff, HA, 1, O, Rt, M, Got, Res);
               Check ("a stranger's static key is not in the credential: aborts",
                      Res = S_Aborted);
            end;
            Recv (Ses_R, Empty_S, EP, F0, R_Eff, HA, 1, O, Rt, M, Got, Res);
            Check ("B accepts A's HELLO before its own Admit, stays in Gate",
                   Res = S_OK and then Ses_R.P = Gate and then Ses_R.Peer_Hello_Seen);
         end;
         Admit (Ses_R, F0, R_Eff, BA, BD, Cred_T, Buf, L, Rt);
         Check ("B's Admit completes the exchange: the responder is in Auth, sends no ROOT",
                Ses_R.P = Auth and then not Rt.Send and then Open_Count (Ses_R) = 0);
         declare
            HB : constant Byte_Array := Slice (Buf, L);
            PA : constant Prefix := Table_Of (SA);
            PB : constant Prefix := Table_Of (SB);
            Root_A : Byte_Array (0 .. Root_Len - 1);
         begin
            Recv (Ses_I, Empty_S, EP, F0, R_Eff, HB, 1, O, Rt, M, Got, Res);
            Check ("A gets B's HELLO: Auth, the authorization ROOT goes out from the state",
                   Res = S_OK and then Ses_I.P = Auth and then Rt.Send and then Rt.Count = 1
                   and then Rt.Fp = Kome.Digest.Fingerprint (AA)
                   and then Open_Count (Ses_I) = 1 and then Open (Ses_I, 1) = Fresh (Min_Key, Data_Lo));
            Root_A := Root_Bytes (Rt);
            --  The snapshots are built now (lazily) and match the HELLOs.
            Check ("the snapshots built after the HELLOs match them (Same_Snapshot)",
                   Same_Snapshot (Ses_I, SA) and then Same_Snapshot (Ses_R, SB));
            Recv (Ses_I, SA, PA, F0, R_Eff, Root_A, 1, O, Rt, M, Got, Res);
            Check ("the initiator refuses a ROOT", Res = S_Unexpected);
            Recv (Ses_R, SB, PB, F0, R_Eff, Root_A, 1, O, Rt, M, Got, Res);
            Check ("B: the authorization ROOT is bound to [Min_Key, Data_Lo) and confirmed",
                   Res = S_OK and then M.Root and then M.Lo = Min_Key and then M.Hi = Data_Lo
                   and then Is_Confirm (O, Min_Key, Data_Lo) and then Ses_R.Auth_Root_Seen);
            Recv (Ses_R, SB, PB, F0, R_Eff, Root_A, 1, O, Rt, M, Got, Res);
            Check ("B: a second ROOT is the data ROOT, bound to [Data_Lo, Max_Key)",
                   Res = S_OK and then M.Lo = Data_Lo and then M.Hi = Max_Key
                   and then Ses_R.P = Data);
            --  B split the data range (its fp differs): one RANGE message.
            declare
               Q  : Msg_Vectors.Vector;
               Ses_R2 : Session := Ses_R;
            begin
               Emit (SB, PB, TB, O, Q);
               Check ("B's answer to the data ROOT: one RANGE message", Natural (Q.Length) = 1
                      or else (O.N >= 1 and then All_Kind (O, P_Elements)));
               pragma Unreferenced (Ses_R2);
            end;
         end;

         --  A tiling answer, by hand: A has asked [Data_Lo, Max_Key); B
         --  answers with ELEMENTS of e1, e2 (one tile [Data_Lo, e3)) and
         --  e3, e7 (a second tile [e3, Max_Key)).
         declare
            PA : constant Prefix := Table_Of (SA);
            Ses_I_D : Session := Ses_I;
            Res2 : Session_Status;
         begin
            --  A sends nothing in Auth any more: the confirm of B closes it.
            declare
               Conf : constant Byte_Array :=
                 Plan_Bytes (SB, TB, (Kind => P_Have, Lo => Min_Key, Hi => Data_Lo, First => 1,
                                      Last => 0, N => 0, Items => [others => 1]));
            begin
               Recv (Ses_I_D, SA, PA, F0, R_Eff, Conf, 1, O, Rt, M, Got, Res2);
               Check ("A: B's confirm closes the authorization obligation",
                      Res2 = S_OK and then Open_Count (Ses_I_D) = 0 and then Ses_I_D.P = Auth);
            end;
            Next_Phase (Ses_I_D, SA, PA, F0, R_Eff, Rt, Res2);
            Check ("Next_Phase: the data ROOT from the snapshot window, Data",
                   Res2 = S_OK and then Rt.Send and then Rt.Count = 6 and then Ses_I_D.P = Data
                   and then Open (Ses_I_D, 1) = Fresh (Data_Lo, Max_Key));
            declare
               T1 : constant Byte_Array :=
                 Plan_Bytes (SB, TB, (Kind => P_Elements, Lo => Data_Lo, Hi => Key (SB, 4),
                                      First => 2, Last => 3, N => 0, Items => [others => 1]));
               T2 : constant Byte_Array :=
                 Plan_Bytes (SB, TB, (Kind => P_Elements, Lo => Key (SB, 4), Hi => Max_Key,
                                      First => 4, Last => 5, N => 0, Items => [others => 1]));
               Ses_I_X : Session := Ses_I_D;
            begin
               Recv (Ses_I_X, SA, PA, F0, R_Eff, T2, 1, O, Rt, M, Got, Res2);
               Check ("S19: a tile that does not start at the head's Next is unexpected",
                      Res2 = S_Unexpected);
               Recv (Ses_I_D, SA, PA, F0, R_Eff, T1, 1, O, Rt, M, Got, Res2);
               Check ("S19: the first tile advances the head (Next = its hi), the head stays",
                      Res2 = S_OK and then Open (Ses_I_D, 1).Next = Key (SB, 4)
                      and then Open (Ses_I_D, 1).Hi = Max_Key
                      and then not Got (1) and then not Got (2));
               Recv (Ses_I_D, SA, PA, F0, R_Eff, T1, 1, O, Rt, M, Got, Res2);
               Check ("a duplicate tile is unexpected", Res2 = S_Unexpected);
               declare
                  Before_Len : constant Natural := Open_Count (Ses_I_D);
               begin
                  Recv (Ses_I_D, SA, PA, F0, R_Eff, T2, 1, O, Rt, M, Got, Res2);
                  Check ("the last tile (hi = the head's hi) completes the answer (Group_Done)",
                         Res2 = S_OK and then Got (2) and then not Got (1)
                         and then Open_Count (Ses_I_D) = Before_Len - 1 + Obligations (O));
               end;
            end;
         end;

         --  S9: the gate on every call. A REVOKE of member 1 (DH1, the
         --  initiator's key at B) is applied after a batch: B aborts.
         declare
            PB : constant Prefix := Table_Of (SB);
            F1 : State := F0;
            Xr : constant Header :=
              (K => K_Revoke, Ent => Zero_Id, FH => Zero_Key,
               V => (T => 0, Author => S1_Key, Seq => 0, H => Hsh (900)), Issuer => Fnd);
            Ses_R_G : Session := Ses_R;
            Res2 : Session_Status;
         begin
            Apply (F1, Xr, 50, St);
            Check ("a founding REVOKE of member 1 closes the gate for DH1, not DH2",
                   St = OK and then not Gate_Open (Cid_A, F1, R_Eff, DH1)
                   and then Gate_Open (Cid_A, F1, R_Eff, DH2));
            Recv (Ses_R_G, SB, PB, F1, R_Eff, Root_Bytes ((True, 1, [others => 0])), 1, O, Rt, M,
                  Got, Res2);
            Check ("S9: Receive after the batch evaluates the gate again and aborts",
                   Res2 = S_Aborted and then Ses_R_G.Aborted and then Ses_R_G.P = Done);
         end;
         declare
            PA : constant Prefix := Table_Of (SA);
            Ses_I_G : Session := Ses_I;
            F2 : State := F0;
            S2_Key : constant Key256 := Member_Key (R_Eff.C, 2);
            Xr : constant Header :=
              (K => K_Revoke, Ent => Zero_Id, FH => Zero_Key,
               V => (T => 5, Author => S2_Key, Seq => 0, H => Hsh (901)), Issuer => Fnd);
            Res2 : Session_Status;
            Conf : constant Byte_Array :=
              Plan_Bytes (SB, TB, (Kind => P_Have, Lo => Min_Key, Hi => Data_Lo, First => 1,
                                   Last => 0, N => 0, Items => [others => 1]));
         begin
            Recv (Ses_I_G, SA, PA, F0, R_Eff, Conf, 1, O, Rt, M, Got, Res2);
            Apply (F2, Xr, 51, St);
            Next_Phase (Ses_I_G, SA, PA, F2, R_Eff, Rt, Res2);
            Check ("S9: Next_Phase evaluates the gate: a REVOKE of the peer's member aborts",
                   Res2 = S_Aborted and then Ses_I_G.Aborted and then not Rt.Send);
         end;

         --  S10: the quarantine ends a session. A certified root's roster
         --  at gen 2 is root-voided by a founding REVOKE: ROSTER_eff falls
         --  back to R_Eff, and the replica is quarantined.
         declare
            PB : constant Prefix := Table_Of (SB);
            FQ : State := F0;
            R8 : constant Header :=
              (K => K_Roster, Ent => Zero_Id, FH => Zero_Key,
               V => (T => 6000, Author => K256 (8), Seq => 2, H => Hsh (80)),
               Issuer => K256 (8));
            X8 : constant Header :=
              (K => K_Revoke, Ent => Zero_Id, FH => Zero_Key,
               V => (T => 0, Author => K256 (8), Seq => 0, H => Hsh (81)), Issuer => Fnd);
            Ses_R_Q : Session := Ses_R;
            Res2 : Session_Status;
         begin
            Apply (FQ, R8, 60, St);
            Apply (FQ, X8, 61, St);
            Check ("fixture: quarantined, ROSTER_eff is R_Eff, the plain gate would admit",
                   Quarantined (FQ) and then Roster_Eff (FQ) = (Present => True, Hdr => RH)
                   and then not Gate_Open (Cid_A, FQ, R_Eff, DH1));
            Recv (Ses_R_Q, SB, PB, FQ, R_Eff, Root_Bytes ((True, 1, [others => 0])), 1, O, Rt, M,
                  Got, Res2);
            Check ("S10: while quarantined, the next Receive aborts the session",
                   Res2 = S_Aborted and then Ses_R_Q.Aborted);
         end;

         --  Equal digests end the session at the HELLOs.
         declare
            X1, X2 : Session (Oblig_Cap => 8);
            Res2 : Session_Status;
         begin
            Start (X1, Initiator, Cid_A, DH2);
            Start (X2, Responder, Cid_A, DH1);
            Admit (X1, F0, R_Eff, AA, AD, Cred_T, Buf, L, Rt);
            declare
               H1 : constant Byte_Array := Slice (Buf, L);
            begin
               Admit (X2, F0, R_Eff, AA, AD, Cred_T, Buf, L, Rt);
               Recv (X1, Empty_S, EP, F0, R_Eff, Slice (Buf, L), 1, O, Rt, M, Got, Res2);
               Check ("equal digests: the initiator is Complete after the HELLOs, no ROOT",
                      Res2 = S_OK and then Complete (X1) and then not Rt.Send);
               Recv (X2, Empty_S, EP, F0, R_Eff, H1, 1, O, Rt, M, Got, Res2);
               Check ("equal digests: the responder is Complete", Res2 = S_OK and then Complete (X2));
               Recv (X2, Empty_S, EP, F0, R_Eff, H1, 1, O, Rt, M, Got, Res2);
               Check ("any message after Done is unexpected", Res2 = S_Unexpected);
            end;
         end;
      end;

      ------------------------------------------------------------------
      --  (h) Convergence
      ------------------------------------------------------------------
      declare
         RA, RB : Replica;

         procedure Run_Session
           (A, B : in out Replica; Rounds : out Natural; All_OK : out Boolean;
            Both_Complete : out Boolean)
         is
            SA, SB : Snapshot (Cap => 256);
            TA, TB : Frame_Table (Cap => 256, Pool_Cap => 600_000);
            AA, AD, BA, BD : Kome.Digest.Digest_State;
            Sess_A, Sess_B : Session (Oblig_Cap => 512);
            To_B, To_A : Msg_Vectors.Vector;
            New_A, New_B : Replica;
            Buf : Msg_Buffer;
            L   : Msg_Length;
            Rt  : Root_Out;

            procedure Deliver_All
              (S : Snapshot; P : Prefix; T : Frame_Table; Sess : in out Session;
               Into : in out Replica;
               In_Q : in out Msg_Vectors.Vector; Out_Q : in out Msg_Vectors.Vector)
            is
               M    : Message;
               Peer : Hello;
               Got  : Delivery;
               St2  : Session_Status;
               O2   : Outbox;
               R2   : Root_Out;
            begin
               for Raw of In_Q loop
                  for J in 1 .. Parts_Of (Raw) loop
                     Receive (Sess, S, P, F0, R_Eff, Raw, J, Keys_Of (Raw), M, Peer, O2, Got,
                              R2, St2);
                     if St2 /= S_OK then
                        All_OK := False;
                     end if;
                     if R2.Send then
                        Out_Q.Append (Root_Bytes (R2));
                     end if;
                     for I in Got'Range loop
                        if Got (I) then
                           declare
                              It : constant In_Item := M.Items (I);
                           begin
                              if not Holds (Into, It.Key) then
                                 Add (Into, It.Key, Raw (It.Off .. It.Off + It.Len - 1));
                              end if;
                           end;
                        end if;
                     end loop;
                     Emit (S, P, T, O2, Out_Q);
                  end loop;
               end loop;
               In_Q.Clear;
               --  The initiator, with nothing open in Auth: the data range.
               if Sess.R = Initiator and then Sess.P = Auth and then Open_Count (Sess) = 0 then
                  Next_Phase (Sess, S, P, F0, R_Eff, R2, St2);
                  if St2 /= S_OK then
                     All_OK := False;
                  end if;
                  if R2.Send then
                     Out_Q.Append (Root_Bytes (R2));
                  end if;
               end if;
            end Deliver_All;
         begin
            All_OK := True;
            Rounds := 0;
            Build (A, SA, TA, AA, AD);
            Build (B, SB, TB, BA, BD);
            declare
               PA : constant Prefix := Table_Of (SA);
               PB : constant Prefix := Table_Of (SB);
            begin
               Start (Sess_A, Initiator, Cid_A, DH2);
               Start (Sess_B, Responder, Cid_A, DH1);
               Admit (Sess_A, F0, R_Eff, AA, AD, Cred_T, Buf, L, Rt);
               To_B.Append (Slice (Buf, L));
               Admit (Sess_B, F0, R_Eff, BA, BD, Cred_T, Buf, L, Rt);
               To_A.Append (Slice (Buf, L));
               while not To_B.Is_Empty or else not To_A.Is_Empty loop
                  if not To_B.Is_Empty then
                     Rounds := Rounds + 1;
                     Deliver_All (SB, PB, TB, Sess_B, New_B, To_B, To_A);
                  end if;
                  if not To_A.Is_Empty then
                     Rounds := Rounds + 1;
                     Deliver_All (SA, PA, TA, Sess_A, New_A, To_A, To_B);
                  end if;
                  exit when Rounds > 200;
               end loop;
            end;
            for E of New_A.Els loop
               if not Holds (A, E.Key) then
                  Add (A, E.Key, E.F);
               end if;
            end loop;
            for E of New_B.Els loop
               if not Holds (B, E.Key) then
                  Add (B, E.Key, E.F);
               end if;
            end loop;
            Both_Complete := Complete (Sess_A) and then Complete (Sess_B);
         end Run_Session;

         Rounds : Natural;
         OK, Done_Both : Boolean;
      begin
         --  Authorization records (as keys: the roster, grants of two
         --  signers), data records over 60 entities, and one frame of the
         --  largest record size (41 120 bytes).
         Add (RA, Key_Of (RH), Frame_For (Key_Of (RH), 400));
         Add (RB, Key_Of (RH), Frame_For (Key_Of (RH), 400));
         for I in 1 .. 6 loop
            declare
               G : constant Elem_Key :=
                 (K => 2, Ent => (others => 0), Sub => 0, FH => K256 (I mod 2 + 1), H => Hsh (I));
            begin
               if I mod 3 /= 0 then
                  Add (RA, G, Frame_For (G, 199));
               end if;
               if I mod 2 = 0 then
                  Add (RB, G, Frame_For (G, 199));
               end if;
            end;
         end loop;
         for I in 1 .. 60 loop
            if I mod 4 /= 1 then
               Add_Elem (RA, DK (I, 1, I, I), 140 + I);
            end if;
            if I mod 5 /= 2 then
               Add_Elem (RB, DK (I, 1, I, I), 140 + I);
            end if;
            if I mod 9 = 0 then
               Add_Elem (RB, DK (I, 0, 0, I + 500), 125);
            end if;
         end loop;
         Add (RA, DK (99, 1, 1, 1), Frame_For (DK (99, 1, 1, 1), Kome.Records.Frame_Max));
         Check ("the replicas differ before the session", not Same_Set (RA, RB));
         Run_Session (RA, RB, Rounds, OK, Done_Both);
         Check ("two-phase session: every message accepted, both Complete ("
                & Rounds'Image & " one-way rounds)", OK and then Done_Both);
         Check ("the replicas hold the same records with the same frames (T7 on this run)",
                Same_Set (RA, RB));
         Run_Session (RA, RB, Rounds, OK, Done_Both);
         Check ("a second session ends at the HELLOs (equal digests)",
                OK and then Done_Both and then Rounds = 2);
      end;
   end;
      if Failed then
         Set_Exit_Status (Failure);
      end if;
   end Run_All;

begin
   null;
end Test_Reconcile;
