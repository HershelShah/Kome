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
--  (i) The ceiling cell (AUDIT.md H12): sessions between real stores
--      (Kome.Store), run by the reference caller of the duties that
--      kome-reconcile.ads lists (procedure Store_Sessions): the sender
--      duty (the cell's frame in the HELLO while the cell is live), the
--      two frames of a HELLO and which operation takes which (the
--      credential by Kome.Write.Receive, the ceiling frame by
--      Kome.Store.Put_Ceil only), the two orders against the snapshot, and
--      the SUSPECT_RELAY rule of the ceiling frame. R2 to R9: the audit
--      scenario by sync in both roles (both sides end with the same
--      maxceil); the second session (re-offers, no log growth); equal
--      digests with different ceilings; a replica with room (the roster
--      reaches its cell, never a row); a credential that returns
--      Ceil_Only in both orders; an exclusive roster in the carrier's
--      cell; the same after the root-void of its signer.
--      As in test_store.adb, the scenario has two forms: the rows are
--      filled through the slot table (15 certified roots; this is what
--      the check mode runs, with every contract of the store and of the
--      session executing), or through the slice (512 REVOKEs of one root,
--      the audit's own case; under -gnata 512 held records do not end in
--      reasonable time, so this form runs in the release mode only).
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
with Kome.Store;
with Kome.Write;
with Contract_Mode;    use Contract_Mode;

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


   ----------------------------------------------------------------------
   --  (i) Sessions between real stores (AUDIT.md H12; DESIGN.md §8): the
   --  reference caller of the duties in kome-reconcile.ads.
   ----------------------------------------------------------------------

   package KS renames Kome.Store;

   --  How the authorization rows are filled, so that a roster of the root
   --  R finds no room: By_Slots, 15 certified roots each sign one REVOKE
   --  and take the slots 2 .. 16; By_Slice, R signs Slice_Max REVOKEs.
   type Fill_Kind is (By_Slots, By_Slice);

   --  Near: the replicas "with room" already hold x1 .. x(N-1), so that a
   --  session delivers one authorization record and not N (the check mode:
   --  each Put_Frame is slow under -gnata). Otherwise they are the small
   --  replicas {r0, g, ..}, and B is built in the order r0, g, r2, x1 ..
   --  x(N-1).
   procedure Store_Sessions (Kind : Fill_Kind; Near : Boolean) is
      Name : constant String :=
        (if Kind = By_Slice then "H12 (full slice) " else "H12 (full slot table) ");
      N    : constant Positive := (if Kind = By_Slice then Slice_Max else Signers_Max - 1);
      TTL_S  : constant U48 := Del_TTL_Min;
      C0     : constant U48 := 1_000;
      C2     : constant U48 := Del_TTL_Min + 600;   --  the horizon is then 600
      Cap_RR : constant U48 := Del_TTL_Min + 1_000_000;
      Salt_S : constant Salt := Salt (Fill (Salt_Len, 91));
      DHA    : constant Pubkey := Good_DH (11);
      DHB    : constant Pubkey := Good_DH (21);
      Nothing : constant Byte_Array (1 .. 0) := [];

      K0_SK, RR_SK, T_SK, Wr_SK, M1_SK, M2_SK : Kome.Crypto.Secret_Key;
      K0_PK, RR_PK, T_PK, Wr_PK, M1_PK, M2_PK : Pubkey;
      Cid     : Hash256;
      Cert_0  : Sig;
      Cert_RR : Sig;

      procedure Chk (What : String; Cond : Boolean) is
      begin
         Check (Name & What, Cond);
      end Chk;

      function Seed_Of (S : Natural) return Kome.Crypto.Seed is
        (Kome.Crypto.Seed (Fill (Kome.Crypto.Seed_Len, S)));

      function Member (PK, DH : Pubkey; Seed : Natural) return Byte_Array is
        (PK & DH & Fill (Nonce_Len, Seed + 1) & Fill (Box_Len, Seed + 2));

      --  The test replicas: member 1 (DHA) and member 2 (DHB).
      function Both return Byte_Array is (Member (M1_PK, DHA, 11) & Member (M2_PK, DHB, 21));

      function Roster_By
        (SK : Kome.Crypto.Secret_Key; PK : Pubkey; Cap : U48; Cert : Sig; Gen, Ceil : U48;
         Members : Byte_Array) return Byte_Array
      is
         R : Roster_Record := Make_Roster (Cid, PK, Cap, Cert, Good_DH (77), Gen, Ceil, Members);
      begin
         Sign (Cid, R, SK);
         return Encode (R);
      end Roster_By;

      function Revoke_By
        (SK : Kome.Crypto.Secret_Key; PK : Pubkey; Cap : U48; Cert : Sig; Subject : Pubkey)
         return Byte_Array
      is
         X : Revoke_Record := Make_Revoke (Cid, PK, Cap, Cert, Subject, 0);
      begin
         Sign (Cid, X, SK);
         return Encode (X);
      end Revoke_By;

      function Hdr (F : Byte_Array) return Header is (KS.Header_Of (Cid, F));

      Log_H : constant := 192 * 1024;

      --  A replica: its store, its lattice state and its Noise static key.
      type Node is record
         S  : KS.Store (Log_H);
         F  : State (8);
         DH : Pubkey := [others => 0];
      end record;

      procedure New_Node (X : out Node; Self, DH : Pubkey) is
      begin
         X.F := Empty (To_Key256 (K0_PK), 8);
         KS.Open (K0_PK, Salt_S, TTL_S, Self, X.F, X.S);
         X.DH := DH;
      end New_Node;

      --  Put_Frame of a verified frame.
      procedure Offer (X : in out Node; Fr : Byte_Array; St : out Status) is
         Off : KS.Log_Size;
      begin
         if not KS.Verified (Cid, K0_PK, Fr) then
            raise Program_Error with "test frame not well-formed";
         end if;
         KS.Put_Frame (X.S, X.F, Fr, Hdr (Fr), Off, St);
      end Offer;

      procedure Hold (X : in out Node; Fr : Byte_Array) is
         St : Status;
      begin
         Offer (X, Fr, St);
         if St /= OK then
            raise Program_Error with "setup frame refused: " & St'Image;
         end if;
      end Hold;

      --  The frame of the held record H, from the store.
      function Frame_Of (X : Node; H : Header) return Byte_Array is
        (KS.Read_Frame (X.S, KS.Tag_Off (Tag_Of (X.F, H))));

      --  The decoded record of ROSTER_eff (the caller's Eff).
      function Eff_Of (X : Node) return Roster_Record is
         V  : constant Header_View := Roster_Eff (X.F);
         R  : Roster_Record :=
           Make_Roster (Cid, K0_PK, Founding_Cap, Zero_Sig, Good_DH (15), 1, 1, Nothing);
         St : Status;
      begin
         if V.Present then
            Decode_Verified (Cid, K0_PK, Frame_Of (X, V.Hdr), R, St);
            if St /= OK then
               raise Program_Error with "ROSTER_eff does not decode";
            end if;
         end if;
         return R;
      end Eff_Of;

      --  The credential a replica sends: the frame of its ROSTER_eff.
      function Cred_Of_Node (X : Node) return Byte_Array is
        (Frame_Of (X, Roster_Eff (X.F).Hdr));

      --  What one side did in a session.
      type Item_Rec is record
         Hdr : Header;
         St  : Status := OK;
      end record;
      type Item_List is array (1 .. 1_200) of Item_Rec;
      type Report is record
         Done_OK      : Boolean := False;        --  Complete (Sess) at the end
         Hello_Res    : Session_Status := S_OK;  --  Receive of the peer's HELLO
         Admitted     : Boolean := False;
         Ceil_Sent    : Natural := 0;            --  ceil_len of our HELLO
         Ceil_Got     : Natural := 0;            --  ceil_len of the peer's HELLO
         Cred_Applied : Boolean := False;
         Cred_St      : Status := OK;
         Ceil_Applied : Boolean := False;        --  Put_Ceil was called
         Ceil_St      : Status := OK;
         Ceil_Flags   : Natural := 0;            --  SUSPECT_RELAY from the ceiling frame
         Item_Flags   : Natural := 0;            --  SUSPECT_RELAY from items
         N_Items      : Natural := 0;            --  delivered frames, in order
         Items        : Item_List;
         Recv         : Natural := 0;            --  one-way messages received
         Bad          : Natural := 0;            --  results other than S_OK after the HELLOs
      end record;

      --  The status of the delivered item H, if exactly one item is H.
      function Item_Is (Rep : Report; H : Header; St : Status) return Boolean is
         Seen : Natural := 0;
         Good : Boolean := False;
      begin
         for K in 1 .. Rep.N_Items loop
            if Rep.Items (K).Hdr = H then
               Seen := Seen + 1;
               Good := Rep.Items (K).St = St;
            end if;
         end loop;
         return Seen = 1 and then Good;
      end Item_Is;

      --  One session between two replicas, I the initiator and R the
      --  responder, by the duties of kome-reconcile.ads. I_First and
      --  R_First say whether a side calls Admit before it has the peer's
      --  HELLO (at least one does). Cred_R replaces the responder's
      --  credential when it is not empty.
      procedure Run_Store_Session
        (I, R             : in out Node;
         I_First, R_First : Boolean;
         Rep_I, Rep_R     : out Report;
         Cred_R           : Byte_Array := Nothing)
      is
         Elem_Cap : constant := 1_024;
         type Prefix_Ptr is access Prefix;
         type Side is record
            Sess   : Session (Oblig_Cap => 1_024);
            Snap   : Snapshot (Cap => Elem_Cap);
            T      : Frame_Table (Cap => Elem_Cap, Pool_Cap => 400_000);
            P      : Prefix_Ptr;
            Sealed : Boolean := False;
         end record;

         Empty_S : Snapshot (Cap => 0);
         EP      : Prefix (1);
         SI, SR  : Side;
         To_I, To_R : Msg_Vectors.Vector;
         Rounds  : Natural := 0;
         Opened  : Boolean;

         --  The snapshot, when the session enters Auth: pin, the frame
         --  table in flat order, Snapshot_Of, Seal.
         procedure Seal_Snapshot (X : in out Node; SX : in out Side) is
            SS : Snap_Status;
         begin
            KS.Pin (X.S, X.F);
            Clear_Table (SX.T);
            for K in 1 .. Kome.Frontier.Count (X.F) loop
               KS.Lemma_Tag (X.S, X.F, K);
               Add_Frame (SX.T, KS.Read_Frame (X.S, KS.Tag_Off (Tag (X.F, K))), SS);
               if SS /= Snap_OK then
                  raise Program_Error with "add_frame " & SS'Image;
               end if;
            end loop;
            Snapshot_Of (X.F, SX.T, SX.Snap, SS);
            if SS /= Snap_OK then
               raise Program_Error with "snapshot_of " & SS'Image;
            end if;
            SX.P := new Prefix (Prefix_Slots (Kome.Reconcile.Count (SX.Snap)));
            Seal (SX.Snap, SX.P.all);
            SX.Sealed := True;
         end Seal_Snapshot;

         --  The credential: an authorization record (Put_Frame). It can
         --  enter a row, and it can return Ceil_Only.
         procedure Apply_Cred (X : in out Node; Rep : in out Report; Peer : Hello) is
            Fr  : constant Byte_Array := Peer.Cred (0 .. Peer.Cred_Len - 1);
            Off : KS.Log_Size;
            Fl  : Boolean;
         begin
            if not KS.Verified (Cid, K0_PK, Fr) then
               raise Program_Error with "the credential does not verify";
            end if;
            Kome.Write.Receive (X.S, X.F, Fr, Hdr (Fr), Off, Rep.Cred_St, Fl);
            Rep.Cred_Applied := True;
         end Apply_Cred;

         --  The ceiling frame: Put_Ceil, and nothing else. The peer is
         --  flagged exactly when the frame raised our maxceil and its
         --  signer was root-voided in our view before the call.
         procedure Apply_Ceil (X : in out Node; Rep : in out Report; Peer : Hello) is
         begin
            Rep.Ceil_Got := Peer.Ceil_Len;
            if Peer.Ceil_Len = 0 then
               return;
            end if;
            declare
               Fr  : constant Byte_Array := Peer.Ceil (0 .. Peer.Ceil_Len - 1);
               Rec : Roster_Record := Eff_Of (X);
               St  : Status;
               Off : KS.Log_Size;
            begin
               Decode_Verified (Cid, K0_PK, Fr, Rec, St);
               if St /= OK then
                  raise Program_Error with "the ceiling frame is not a verified ROSTER";
               end if;
               declare
                  H : constant Header := Hdr (Fr);
                  V : constant Boolean := Root_Void (X.F, H.Issuer);
               begin
                  KS.Put_Ceil (X.S, X.F, Fr, H, Off, Rep.Ceil_St);
                  Rep.Ceil_Applied := True;
                  if Rep.Ceil_St = Ceil_Only and then V then
                     Rep.Ceil_Flags := Rep.Ceil_Flags + 1;
                  end if;
               end;
            end;
         end Apply_Ceil;

         --  Admit, when the gate is open: our HELLO from the digest states
         --  as they are now, with the cell's frame if the cell is live
         --  (the sender duty).
         procedure Do_Admit
           (X : in out Node; SX : in out Side; Rep : in out Report; Cred : Byte_Array;
            Out_Q : in out Msg_Vectors.Vector; Open : out Boolean)
         is
            Eff : constant Roster_Record := Eff_Of (X);
            Buf : Msg_Buffer;
            L   : Msg_Length;
            Rt  : Root_Out;
         begin
            Open := Gate_Open (Cid, X.F, Eff, SX.Sess.Peer_DH);
            if not Open then
               return;
            end if;
            if Ceil_Live (X.F) then
               KS.Lemma_Ceil_Tag (X.S, X.F);
               declare
                  Ceil : constant Byte_Array :=
                    KS.Read_Frame (X.S, KS.Tag_Off (Ceil_Tag (X.F)));
               begin
                  Rep.Ceil_Sent := Ceil'Length;
                  Admit (SX.Sess, X.F, Eff, KS.Digest_Auth (X.S), KS.Digest_Data (X.S), Cred,
                         Ceil, Buf, L, Rt);
               end;
            else
               Admit (SX.Sess, X.F, Eff, KS.Digest_Auth (X.S), KS.Digest_Data (X.S), Cred,
                      Nothing, Buf, L, Rt);
            end if;
            Rep.Admitted := True;
            Out_Q.Append (Slice (Buf, L));
            if Rt.Send then
               Out_Q.Append (Root_Bytes (Rt));
            end if;
         end Do_Admit;

         --  The peer's HELLO, and the two orders.
         procedure On_Hello
           (X : in out Node; SX : in out Side; Rep : in out Report; Raw : Byte_Array;
            Cred : Byte_Array; Out_Q : in out Msg_Vectors.Vector)
         is
            Was_Out : constant Boolean := SX.Sess.Hello_Sent;
            M    : Message;
            Peer : Hello;
            O    : Outbox;
            Got  : Delivery;
            Rt   : Root_Out;
            Res  : Session_Status;
            Open : Boolean;
         begin
            Receive (SX.Sess, Empty_S, EP, X.F, Eff_Of (X), Raw, 1, No_Keys, M, Peer, O, Got,
                     Rt, Res);
            Rep.Hello_Res := Res;
            if Res /= S_OK then
               --  A refused HELLO: Peer is Empty_Hello, nothing is applied.
               return;
            end if;
            if Was_Out then
               --  Our HELLO was out: the snapshot it described, then the
               --  credential, then the ceiling frame.
               if SX.Sess.P = Auth then
                  Seal_Snapshot (X, SX);
               end if;
               Apply_Cred (X, Rep, Peer);
               Apply_Ceil (X, Rep, Peer);
               if Rt.Send then
                  Out_Q.Append (Root_Bytes (Rt));
               end if;
            else
               --  Our HELLO was not out: the credential, the gate, Admit,
               --  the snapshot, then the ceiling frame.
               Apply_Cred (X, Rep, Peer);
               Do_Admit (X, SX, Rep, Cred, Out_Q, Open);
               if not Open then
                  return;
               end if;
               if SX.Sess.P = Auth then
                  Seal_Snapshot (X, SX);
               end if;
               Apply_Ceil (X, Rep, Peer);
            end if;
         end On_Hello;

         --  The keys of the items of Raw, from the decoded frames. A frame
         --  that does not verify is a protocol violation.
         function Item_Keys (Raw : Byte_Array) return Key_List is
            PL : constant Places := Item_Places (Raw);
            K  : Key_List := No_Keys;
         begin
            if PL.OK then
               for T in 1 .. PL.N loop
                  declare
                     Fr : constant Byte_Array := Raw (PL.Off (T) .. PL.Off (T) + PL.Len (T) - 1);
                  begin
                     if not KS.Verified (Cid, K0_PK, Fr) then
                        raise Program_Error with "an item frame does not verify";
                     end if;
                     K (T) := Key_Of (Hdr (Fr));
                  end;
               end loop;
            end if;
            return K;
         end Item_Keys;

         --  Any other message: Receive, apply the delivered frames in item
         --  order, send the reply.
         procedure On_Message
           (X : in out Node; SX : in out Side; Rep : in out Report; Raw : Byte_Array;
            Out_Q : in out Msg_Vectors.Vector)
         is
            Keys : constant Key_List := Item_Keys (Raw);
            M    : Message;
            Peer : Hello;
            O    : Outbox;
            Got  : Delivery;
            Rt   : Root_Out;
            Res  : Session_Status;
         begin
            for J in 1 .. Parts_Of (Raw) loop
               if SX.Sealed then
                  Receive (SX.Sess, SX.Snap, SX.P.all, X.F, Eff_Of (X), Raw, J, Keys, M, Peer,
                           O, Got, Rt, Res);
               else
                  Receive (SX.Sess, Empty_S, EP, X.F, Eff_Of (X), Raw, J, Keys, M, Peer, O,
                           Got, Rt, Res);
               end if;
               if Res /= S_OK then
                  Rep.Bad := Rep.Bad + 1;
               end if;
               if Rt.Send then
                  Out_Q.Append (Root_Bytes (Rt));
               end if;
               for T in Got'Range loop
                  if Got (T) then
                     declare
                        It  : constant In_Item := M.Items (T);
                        Fr  : constant Byte_Array := Raw (It.Off .. It.Off + It.Len - 1);
                        H   : constant Header := Hdr (Fr);
                        Sus : constant Boolean :=
                          (if Is_Data (H) then Is_Void (X.F, H) else Root_Void (X.F, H.Issuer));
                        Off : KS.Log_Size;
                        St  : Status;
                        Fl  : Boolean;
                     begin
                        Kome.Write.Receive (X.S, X.F, Fr, H, Off, St, Fl);
                        Rep.N_Items := Rep.N_Items + 1;
                        Rep.Items (Rep.N_Items) := (Hdr => H, St => St);
                        if Sus then
                           Rep.Item_Flags := Rep.Item_Flags + 1;
                        end if;
                     end;
                  end if;
               end loop;
               if SX.Sealed then
                  Emit (SX.Snap, SX.P.all, SX.T, O, Out_Q);
               end if;
            end loop;
         end On_Message;

         procedure Deliver
           (X : in out Node; SX : in out Side; Rep : in out Report; Cred : Byte_Array;
            In_Q, Out_Q : in out Msg_Vectors.Vector)
         is
            Batch : constant Msg_Vectors.Vector := In_Q;
            Rt    : Root_Out;
            Res   : Session_Status;
         begin
            In_Q.Clear;
            for Raw of Batch loop
               Rep.Recv := Rep.Recv + 1;
               if Raw'Length > 0 and then Raw (Raw'First) = Tag_Hello then
                  On_Hello (X, SX, Rep, Raw, Cred, Out_Q);
               else
                  On_Message (X, SX, Rep, Raw, Out_Q);
               end if;
            end loop;
            --  The initiator, with nothing open in Auth: the data range.
            if SX.Sealed and then SX.Sess.R = Initiator and then SX.Sess.P = Auth
              and then Open_Count (SX.Sess) = 0
            then
               Next_Phase (SX.Sess, SX.Snap, SX.P.all, X.F, Eff_Of (X), Rt, Res);
               if Res /= S_OK then
                  Rep.Bad := Rep.Bad + 1;
               end if;
               if Rt.Send then
                  Out_Q.Append (Root_Bytes (Rt));
               end if;
            end if;
         end Deliver;

         Cred_I_B : constant Byte_Array := Cred_Of_Node (I);
         Cred_R_B : constant Byte_Array :=
           (if Cred_R'Length > 0 then Cred_R else Cred_Of_Node (R));
      begin
         Rep_I := (others => <>);
         Rep_R := (others => <>);
         Clear (Empty_S);
         Seal (Empty_S, EP);
         Start (SI.Sess, Initiator, Cid, R.DH);
         Start (SR.Sess, Responder, Cid, I.DH);
         if I_First then
            Do_Admit (I, SI, Rep_I, Cred_I_B, To_R, Opened);
         end if;
         if R_First then
            Do_Admit (R, SR, Rep_R, Cred_R_B, To_I, Opened);
         end if;
         while not To_R.Is_Empty or else not To_I.Is_Empty loop
            if not To_R.Is_Empty then
               Deliver (R, SR, Rep_R, Cred_R_B, To_R, To_I);
            end if;
            if not To_I.Is_Empty then
               Deliver (I, SI, Rep_I, Cred_I_B, To_I, To_R);
            end if;
            Rounds := Rounds + 1;
            exit when Rounds > 400;
         end loop;
         if SI.Sealed then
            KS.Unpin (I.S, I.F);
         end if;
         if SR.Sealed then
            KS.Unpin (R.S, R.F);
         end if;
         Rep_I.Done_OK := Complete (SI.Sess);
         Rep_R.Done_OK := Complete (SR.Sess);
      end Run_Store_Session;

   begin
      Kome.Crypto.Key_Pair (Seed_Of (3), K0_SK, K0_PK);
      Kome.Crypto.Key_Pair (Seed_Of (7), RR_SK, RR_PK);
      Kome.Crypto.Key_Pair (Seed_Of (9), T_SK, T_PK);
      Kome.Crypto.Key_Pair (Seed_Of (13), Wr_SK, Wr_PK);
      Kome.Crypto.Key_Pair (Seed_Of (17), M1_SK, M1_PK);
      Kome.Crypto.Key_Pair (Seed_Of (19), M2_SK, M2_PK);
      Cid := Cid_Of (K0_PK, Salt_S, TTL_S);
      Cert_0 := Make_Cert (K0_SK, Cid, K0_PK, Founding_Cap);
      Cert_RR := Make_Cert (K0_SK, Cid, RR_PK, Cap_RR);
      declare
         type Rev_Frames is array (1 .. N) of Byte_Array (0 .. Revoke_Frame_Len - 1);
         X : Rev_Frames;

         function G_Frame return Byte_Array is
            G : Grant_Record := Make_Grant (Cid, K0_PK, Founding_Cap, Cert_0, Wr_PK);
         begin
            Sign (Cid, G, K0_SK);
            return Encode (G);
         end G_Frame;

         function D_Frame return Byte_Array is
            R : Del_Record := Make_Del (Cid, Ent_Id (Fill (Ent_Len, 3)), 500, 1, Wr_PK);
         begin
            Sign (Cid, R, Wr_SK);
            return Encode (R);
         end D_Frame;

         function P_Frame return Byte_Array is
            R : Put_Record :=
              Make_Put (Cid, Ent_Id (Fill (Ent_Len, 4)), [16#61#], 900, 2, Wr_PK, [1, 2, 3]);
         begin
            Sign (Cid, R, Wr_SK);
            return Encode (R);
         end P_Frame;

         R0 : constant Byte_Array := Roster_By (K0_SK, K0_PK, Founding_Cap, Cert_0, 5, C0, Both);
         G  : constant Byte_Array := G_Frame;
         D  : constant Byte_Array := D_Frame;
         P  : constant Byte_Array := P_Frame;
         R2 : constant Byte_Array := Roster_By (RR_SK, RR_PK, Cap_RR, Cert_RR, 1, C2, Both);
         --  A roster of R with a high gen that lists only the thief's
         --  device: in a row it is ROSTER_eff and closes the gate.
         R3 : constant Byte_Array :=
           Roster_By (RR_SK, RR_PK, Cap_RR, Cert_RR, 20, C2, Member (T_PK, Good_DH (31), 31));
         --  The founding REVOKE of R, and a recovery roster.
         V  : constant Byte_Array := Revoke_By (K0_SK, K0_PK, Founding_Cap, Cert_0, RR_PK);
         RV : constant Byte_Array := Roster_By (K0_SK, K0_PK, Founding_Cap, Cert_0, 9, C0, Both);

         P0, PX, A0, B0, A2, B2, AX, BX, C, DN, A8 : Node;
         RA, RB, RC, RD : Report;
         St : Status;
         LA, LB : KS.Log_Size;

         procedure Hold_X (Nd : in out Node; From, To : Natural) is
         begin
            for K in From .. To loop
               Hold (Nd, X (K));
            end loop;
         end Hold_X;
      begin
         for K in 1 .. N loop
            declare
               Sd   : Byte_Array := Fill (Kome.Crypto.Seed_Len, 77);
               Q_SK : Kome.Crypto.Secret_Key;
               Q_PK : Pubkey;
            begin
               Sd (0) := Byte (K mod 256);
               Sd (1) := Byte (K / 256);
               Kome.Crypto.Key_Pair (Kome.Crypto.Seed (Sd), Q_SK, Q_PK);
               if Kind = By_Slice then
                  X (K) := Revoke_By (RR_SK, RR_PK, Cap_RR, Cert_RR, Q_PK);
               else
                  X (K) := Revoke_By
                    (Q_SK, Q_PK, 2_000, Make_Cert (K0_SK, Cid, Q_PK, 2_000), T_PK);
               end if;
            end;
         end loop;

         --  P0 = {r0, g}; PX = P0 and x1 .. x(N-1); A0 = PX and xN: the rows
         --  have no room for a roster of R. B0 holds r2 and x1 .. x(N-1).
         New_Node (P0, M1_PK, DHA);
         Hold (P0, R0);
         Hold (P0, G);
         PX := P0;
         Hold_X (PX, 1, N - 1);
         A0 := PX;
         Hold (A0, X (N));
         if Near then
            B0 := PX;
            Hold (B0, R2);
         else
            B0 := P0;
            Hold (B0, R2);
            Hold_X (B0, 1, N - 1);
         end if;
         B0.DH := DHB;
         Chk ("setup: A has no room for a roster of R; B holds r2 and has no room for xN",
              KS.Auth_Rule (A0.F, Hdr (R2)) and then Max_Ceil (A0.F) = C0
              and then Holds (B0.F, Hdr (R2)) and then KS.Auth_Rule (B0.F, Hdr (X (N)))
              and then Max_Ceil (B0.F) = C2);

         ---------------------------------------------------------------
         --  R2. The audit scenario by sync, in both roles.
         ---------------------------------------------------------------
         A2 := A0;
         B2 := B0;
         Run_Store_Session (A2, B2, True, True, RA, RB);
         Chk ("R2 (A initiates): both Complete, every message accepted",
              RA.Done_OK and then RB.Done_OK and then RA.Bad = 0 and then RB.Bad = 0);
         Chk ("R2 (A initiates): A's Receive of r2 is Ceil_Only, B's of xN is Auth_Full",
              Item_Is (RA, Hdr (R2), Ceil_Only) and then Item_Is (RB, Hdr (X (N)), Auth_Full)
              and then RA.N_Items = 1 and then RB.N_Items = 1);
         Chk ("R2 (A initiates): the two sides have the same maxceil and horizon (T19)",
              Max_Ceil (A2.F) = C2 and then Max_Ceil (B2.F) = C2
              and then KS.Hz (A2.F, TTL_S) = KS.Hz (B2.F, TTL_S)
              and then Has_Ceil (A2.F) and then Ceil_Held (A2.F) = Hdr (R2)
              and then not Holds (A2.F, Hdr (R2)) and then not Has_Ceil (B2.F));
         AX := A0;
         BX := B0;
         Run_Store_Session (BX, AX, True, False, RB, RA);
         Chk ("R2 (B initiates): both Complete; Ceil_Only at A, Auth_Full at B",
              RA.Done_OK and then RB.Done_OK and then RA.Bad = 0 and then RB.Bad = 0
              and then Item_Is (RA, Hdr (R2), Ceil_Only)
              and then Item_Is (RB, Hdr (X (N)), Auth_Full));
         Chk ("R2 (B initiates): the two sides have the same maxceil (T19)",
              Max_Ceil (AX.F) = C2 and then Max_Ceil (BX.F) = C2);

         ---------------------------------------------------------------
         --  R3. The second session of the pair: the re-offers.
         ---------------------------------------------------------------
         LA := KS.Log_Length (A2.S);
         LB := KS.Log_Length (B2.S);
         Run_Store_Session (A2, B2, True, True, RA, RB);
         Chk ("R3: the second session is Complete; r2 and xN are offered again, Auth_Full",
              RA.Done_OK and then RB.Done_OK
              and then RA.N_Items = 1 and then Item_Is (RA, Hdr (R2), Auth_Full)
              and then RB.N_Items = 1 and then Item_Is (RB, Hdr (X (N)), Auth_Full));
         Chk ("R3: neither log grows",
              KS.Log_Length (A2.S) = LA and then KS.Log_Length (B2.S) = LB);
         Chk ("R3: A's HELLO carries r2 (its cell is live); B's Put_Ceil returns OK",
              RA.Ceil_Sent = R2'Length and then RB.Ceil_Got = R2'Length
              and then RB.Ceil_Applied and then RB.Ceil_St = OK and then RB.Ceil_Flags = 0
              and then RB.Ceil_Sent = 0 and then not RA.Ceil_Applied);

         ---------------------------------------------------------------
         --  R4. Equal digests, different ceilings: A (cell r2) and D, whose
         --  rows are A's and which was never offered r2.
         ---------------------------------------------------------------
         for Role in 1 .. 2 loop
            AX := A2;
            DN := A0;
            DN.DH := DHB;
            if Role = 1 then
               Run_Store_Session (AX, DN, True, True, RA, RD);
            else
               Run_Store_Session (DN, AX, True, False, RD, RA);
            end if;
            Chk ("R4 (" & (if Role = 1 then "A" else "D")
                 & " initiates): equal digests end the session at the HELLOs",
                 RA.Done_OK and then RD.Done_OK and then RA.Recv = 1 and then RD.Recv = 1
                 and then RA.N_Items = 0 and then RD.N_Items = 0);
            Chk ("R4: A's HELLO carries r2, D's none; D's Put_Ceil is Ceil_Only",
                 RA.Ceil_Sent = R2'Length and then RD.Ceil_Sent = 0
                 and then RD.Ceil_Applied and then RD.Ceil_St = Ceil_Only
                 and then RD.Ceil_Flags = 0 and then not RA.Ceil_Applied);
            Chk ("R4: D has A's maxceil, and holds r2 in its cell only",
                 Max_Ceil (DN.F) = C2 and then Max_Ceil (AX.F) = C2
                 and then Has_Ceil (DN.F) and then Ceil_Held (DN.F) = Hdr (R2)
                 and then not Holds (DN.F, Hdr (R2)));
         end loop;

         ---------------------------------------------------------------
         --  R5. A replica with room: r2 reaches its cell, never a row.
         ---------------------------------------------------------------
         C := (if Near then PX else P0);
         C.DH := DHB;
         Hold (C, D);
         Hold (C, P);
         AX := A2;
         Run_Store_Session (AX, C, True, False, RA, RC);
         Chk ("R5: Complete; C has the maxceil of A",
              RA.Done_OK and then RC.Done_OK and then RA.Bad = 0 and then RC.Bad = 0
              and then Max_Ceil (C.F) = C2 and then Max_Ceil (AX.F) = C2);
         Chk ("R5: C has r2 in its cell and in no row, though its rows have room",
              RC.Ceil_St = Ceil_Only and then Has_Ceil (C.F) and then Ceil_Held (C.F) = Hdr (R2)
              and then not Holds (C.F, Hdr (R2))
              and then Slot_Of (C.F, To_Key256 (RR_PK))
                       = (if Kind = By_Slice then Slot_Of (AX.F, To_Key256 (RR_PK)) else 0)
              and then Roster_Eff (C.F) = (Present => True, Hdr => Hdr (R0)));
         Chk ("R5: the capture expired d at C; p is held on both sides",
              not Holds (C.F, Hdr (D)) and then Holds (C.F, Hdr (P))
              and then Holds (AX.F, Hdr (P)) and then not Holds (AX.F, Hdr (D)));

         ---------------------------------------------------------------
         --  R7. A credential that returns Ceil_Only, in both orders.
         ---------------------------------------------------------------
         for Order in 1 .. 2 loop
            AX := A0;
            Hold (AX, D);
            Hold (AX, P);
            BX := B0;
            if Order = 1 then
               --  A's HELLO is out when B's arrives: seal, then the credential.
               Run_Store_Session (AX, BX, True, True, RA, RB, Cred_R => R2);
            else
               --  B's HELLO arrives first: the credential, the gate, Admit,
               --  then the seal.
               Run_Store_Session (AX, BX, False, True, RA, RB, Cred_R => R2);
            end if;
            Chk ("R7 (order" & Order'Image & "): the credential r2 returns Ceil_Only at A"
                 & " and expires d",
                 RA.Cred_Applied and then RA.Cred_St = Ceil_Only
                 and then not Holds (AX.F, Hdr (D)) and then Holds (AX.F, Hdr (P)));
            Chk ("R7 (order" & Order'Image & "): every later Receive and Next_Phase is"
                 & " accepted (Same_Snapshot); Complete; the same maxceil",
                 RA.Bad = 0 and then RB.Bad = 0 and then RA.Done_OK and then RB.Done_OK
                 and then Max_Ceil (AX.F) = C2 and then Max_Ceil (BX.F) = C2
                 and then Holds (BX.F, Hdr (P)));
         end loop;

         ---------------------------------------------------------------
         --  R8. An exclusive roster in the carrier's cell.
         ---------------------------------------------------------------
         A8 := A0;
         Offer (A8, R3, St);
         Chk ("R8: setup: r3 is captured at A; ROSTER_eff of A is still r0",
              St = Ceil_Only and then Ceil_Held (A8.F) = Hdr (R3)
              and then Roster_Eff (A8.F) = (Present => True, Hdr => Hdr (R0)));
         for Role in 1 .. 2 loop
            AX := A8;
            C := (if Near then PX else P0);
            C.DH := DHB;
            if Role = 1 then
               Run_Store_Session (AX, C, True, False, RA, RC);
            else
               Run_Store_Session (C, AX, True, True, RC, RA);
            end if;
            Chk ("R8 (" & (if Role = 1 then "A" else "C") & " initiates): Complete; C has the"
                 & " maxceil; r3 is in C's cell and in no row",
                 RA.Done_OK and then RC.Done_OK and then RA.Bad = 0 and then RC.Bad = 0
                 and then Max_Ceil (C.F) = C2 and then RC.Ceil_St = Ceil_Only
                 and then Ceil_Held (C.F) = Hdr (R3) and then not Holds (C.F, Hdr (R3)));
            Chk ("R8: ROSTER_eff of C is still r0, and its gate still admits A",
                 Roster_Eff (C.F) = (Present => True, Hdr => Hdr (R0))
                 and then not Quarantined (C.F)
                 and then Gate_Open (Cid, C.F, Eff_Of (C), DHA)
                 and then RC.Ceil_Flags = 0);
            Run_Store_Session (AX, C, True, True, RA, RC);
            Chk ("R8: a second session is Complete too",
                 RA.Done_OK and then RC.Done_OK and then RC.Ceil_St = OK
                 and then Max_Ceil (C.F) = C2);
         end loop;

         ---------------------------------------------------------------
         --  R9. After the root-void: D holds the founding REVOKE of R and a
         --  recovery roster.
         ---------------------------------------------------------------
         for Role in 1 .. 2 loop
            AX := A8;
            DN := (if Near then PX else P0);
            DN.DH := DHB;
            Hold (DN, V);
            Hold (DN, RV);
            if Role = 1 then
               Run_Store_Session (AX, DN, True, False, RA, RD);
            else
               Run_Store_Session (DN, AX, True, True, RD, RA);
            end if;
            Chk ("R9 (" & (if Role = 1 then "A" else "D") & " initiates): Complete; D has the"
                 & " maxceil and does not hold r3",
                 RA.Done_OK and then RD.Done_OK and then RA.Bad = 0 and then RD.Bad = 0
                 and then Max_Ceil (DN.F) = C2 and then not Holds (DN.F, Hdr (R3))
                 and then Ceil_Held (DN.F) = Hdr (R3));
            Chk ("R9: Roster_Max of D is the recovery roster; D is not quarantined",
                 Roster_Max (DN.F) = (Present => True, Hdr => Hdr (RV))
                 and then not Quarantined (DN.F));
            Chk ("R9: D flags A once for the ceiling frame (SUSPECT_RELAY); A now holds"
                 & " the REVOKE and the recovery roster",
                 RD.Ceil_St = Ceil_Only and then RD.Ceil_Flags = 1
                 and then Holds (AX.F, Hdr (V)) and then Holds (AX.F, Hdr (RV)));
            Run_Store_Session (AX, DN, True, True, RA, RD);
            Chk ("R9: a second session: Complete; A's HELLO still carries r3; D's Put_Ceil"
                 & " returns OK and flags nobody",
                 RA.Done_OK and then RD.Done_OK and then RA.Ceil_Sent = R3'Length
                 and then RD.Ceil_Applied and then RD.Ceil_St = OK
                 and then RD.Ceil_Flags = 0);
         end loop;
      end;
   end Store_Sessions;

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
      --  A ceiling frame for the wire tests (Kome.Reconcile checks only its
      --  length), and the empty one.
      Ceil_T : constant Byte_Array := Fill (212, 44);
      No_Ceil : constant Byte_Array (1 .. 0) := [];
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
         Line  : String (1 .. 80_000);
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
                           Ce : constant Byte_Array := From_Hex (Field (6));
                           H  : Hello;
                           OK : Boolean;
                        begin
                           Encode_Hello (Word'Value (Field (2)), Word'Value (Field (3)),
                                         From_Hex (Field (4)), Cr, Ce, Buf, L);
                           Decode_Hello (Wire, H, OK);
                           Mark ("hello", Slice (Buf, L) = Wire and then OK
                                 and then Hello_Wire_OK (Wire)
                                 and then Wire'Length = Hello_Fixed + Cr'Length + Ce'Length
                                 and then H.N_Auth = Word'Value (Field (2))
                                 and then H.N_Data = Word'Value (Field (3))
                                 and then H.Digest = From_Hex (Field (4))
                                 and then H.Cred_Len = Cr'Length
                                 and then H.Cred (0 .. H.Cred_Len - 1) = Cr
                                 and then H.Ceil_Len = Ce'Length
                                 and then H.Ceil (0 .. H.Ceil_Len - 1) = Ce
                                 and then Cred_Of (Wire) = Cr
                                 and then Hello_Ceil_Of (Wire) = Ce
                                 and then Cred_Canonical (H));
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
                   & N_Vec'Image & " vectors)", All_OK and then N_Vec = 26);
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

      --  R1 (AUDIT.md H12): the HELLO with a ceiling frame. The round
      --  trip with the four combinations of an empty and a non-empty cred
      --  and ceil; Cred_Of and Hello_Ceil_Of; the refusals of
      --  Hello_Wire_OK; the largest HELLO.
      declare
         Buf : Msg_Buffer;
         L   : Msg_Length;
         Dg  : constant Hash256 := Hash256 (Fill (32, 9));
         C1  : constant Byte_Array := Fill (300, 1);
         K1  : constant Byte_Array := Fill (212, 2);
         No  : constant Byte_Array (1 .. 0) := [];
         OK_All : Boolean := True;

         procedure Round_Trip (Cr, Ce : Byte_Array) is
            H  : Hello;
            OK : Boolean;
         begin
            Encode_Hello (3, 4, Dg, Cr, Ce, Buf, L);
            declare
               W : constant Byte_Array := Slice (Buf, L);
            begin
               Decode_Hello (W, H, OK);
               OK_All := OK_All and then OK and then L = Hello_Fixed + Cr'Length + Ce'Length
                 and then Hello_Wire_OK (W) and then Hello_Decoded (W, H)
                 and then H.N_Auth = 3 and then H.N_Data = 4 and then H.Digest = Dg
                 and then H.Cred_Len = Cr'Length and then H.Ceil_Len = Ce'Length
                 and then H.Cred (0 .. H.Cred_Len - 1) = Cr
                 and then H.Ceil (0 .. H.Ceil_Len - 1) = Ce
                 and then Cred_Of (W) = Cr and then Hello_Ceil_Of (W) = Ce
                 and then Wire_U16 (W, Hello_O_CLen) = Cr'Length
                 and then Wire_U16 (W, Hello_O_KLen) = Ce'Length
                 and then (for all I in H.Cred_Len .. Cred_Max - 1 => H.Cred (I) = 0)
                 and then (for all I in H.Ceil_Len .. Cred_Max - 1 => H.Ceil (I) = 0);
               if H.Cred_Len < Cred_Max then
                  Lemma_Cred_Zero (H, H.Cred_Len);
               end if;
               if H.Ceil_Len < Cred_Max then
                  Lemma_Ceil_Zero (H, H.Ceil_Len);
               end if;
            end;
         end Round_Trip;
      begin
         Round_Trip (No, No);
         Round_Trip (C1, No);
         Round_Trip (No, K1);
         Round_Trip (C1, K1);
         Check ("R1: the HELLO round trip with an empty and a non-empty cred and ceil", OK_All);
         Encode_Hello (3, 4, Dg, Fill (Cred_Max, 5), Fill (Cred_Max, 6), Buf, L);
         Check ("R1: the largest HELLO is 17 877 bytes",
                L = 17_877 and then L = Hello_Max_Len
                and then Hello_Wire_OK (Slice (Buf, L))
                and then Hello_Ceil_Of (Slice (Buf, L)) = Fill (Cred_Max, 6)
                and then Cred_Of (Slice (Buf, L)) = Fill (Cred_Max, 5));
         Encode_Hello (3, 4, Dg, C1, K1, Buf, L);
         declare
            W    : constant Byte_Array := Slice (Buf, L);
            Big  : Byte_Array := W & Fill (Cred_Max, 0);
            Long : constant Byte_Array := W & Byte_Array'[0];
            H    : Hello;
            OK   : Boolean;
         begin
            --  ceil_len = Cred_Max + 1, with the bytes to match it.
            Big (Hello_O_KLen)     := Byte ((Cred_Max + 1) / 256);
            Big (Hello_O_KLen + 1) := Byte ((Cred_Max + 1) mod 256);
            Decode_Hello (Big (0 .. Hello_Fixed + C1'Length + Cred_Max), H, OK);
            Check ("R1: Hello_Wire_OK refuses ceil_len > Cred_Max",
                   not OK and then not Hello_Wire_OK (Big (0 .. Hello_Fixed + C1'Length + Cred_Max))
                   and then H = Empty_Hello);
            Decode_Hello (Long, H, OK);
            Check ("R1: Hello_Wire_OK refuses a length that the two lengths do not give",
                   not OK and then not Hello_Wire_OK (Long)
                   and then not Hello_Wire_OK (W (0 .. W'Last - 1)));
         end;
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
         Admit (Ses_I, F0, R_Eff, AA, AD, Cred_T, Ceil_T, Buf, L, Rt);
         declare
            HA : constant Byte_Array := Slice (Buf, L);
         begin
            Check ("Admit: the HELLO carries n_auth, n_data and the union digest (S21)",
                   Ses_I.Hello_Sent and then not Rt.Send
                   and then Wire_U32 (Buf, Hello_O_NAuth) = 1
                   and then Wire_U32 (Buf, Hello_O_NData) = 6
                   and then Buf (Hello_O_Digest .. Hello_O_Digest + 31) = Range_Fp (SA, 1, 7));
            Check ("R1: Admit puts Ceil after Cred",
                   L = Hello_Fixed + Cred_T'Length + Ceil_T'Length
                   and then Cred_Of (HA) = Cred_T and then Hello_Ceil_Of (HA) = Ceil_T
                   and then Wire_U16 (HA, Hello_O_KLen) = Ceil_T'Length);
            --  The credential checks at B.
            declare
               X : Session (Oblig_Cap => 8);
               Mem_X : constant Byte_Array := Members_Of (1, 77);
               R_X : constant Roster_Record :=
                 Make_Roster (Cid_A, Root_PK, Founding_Cap, Zero_Sig, Box_A, 1, 5000, Mem_X);
               HX : Byte_Array := HA;
            begin
               Encode_Hello (1, 6, Range_Fp (SA, 1, 7), Encode (R_X), Ceil_T, Buf, L);
               Start (X, Responder, Cid_A, DH1);
               declare
                  Pr : Hello;
               begin
                  Receive (X, Empty_S, EP, F0, R_Eff, Slice (Buf, L), 1, No_Keys, M, Pr, O, Got,
                           Rt, Res);
                  Check ("A13: a HELLO credential that does not list the peer aborts",
                         Res = S_Aborted and then X.Aborted);
                  --  R6: nothing of a refused HELLO is returned, so the
                  --  caller applies nothing, the ceiling frame included.
                  Check ("R6: a refused HELLO returns Empty_Hello: no credential, no ceiling"
                         & " frame", Pr = Empty_Hello and then Pr.Ceil_Len = 0);
               end;
               Encode_Hello (1, 6, Range_Fp (SA, 1, 7), Fill (300, 1), No_Ceil, Buf, L);
               Start (X, Responder, Cid_A, DH1);
               Recv (X, Empty_S, EP, F0, R_Eff, Slice (Buf, L), 1, O, Rt, M, Got, Res);
               Check ("a credential that is not a ROSTER frame aborts", Res = S_Aborted);
               HX (HX'Last) := HX (HX'Last) xor 1;
               Start (X, Responder, Cid_A, DHX);
               Recv (X, Empty_S, EP, F0, R_Eff, HA, 1, O, Rt, M, Got, Res);
               Check ("a stranger's static key is not in the credential: aborts",
                      Res = S_Aborted);
            end;
            declare
               Pr : Hello;
            begin
               Receive (Ses_R, Empty_S, EP, F0, R_Eff, HA, 1, No_Keys, M, Pr, O, Got, Rt, Res);
               Check ("B accepts A's HELLO before its own Admit, stays in Gate",
                      Res = S_OK and then Ses_R.P = Gate and then Ses_R.Peer_Hello_Seen);
               Check ("R1: the accepted HELLO returns the credential and the ceiling frame",
                      Pr.Cred_Len = Cred_T'Length and then Pr.Cred (0 .. Pr.Cred_Len - 1) = Cred_T
                      and then Pr.Ceil_Len = Ceil_T'Length
                      and then Pr.Ceil (0 .. Pr.Ceil_Len - 1) = Ceil_T);
            end;
         end;
         Admit (Ses_R, F0, R_Eff, BA, BD, Cred_T, No_Ceil, Buf, L, Rt);
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
            Admit (X1, F0, R_Eff, AA, AD, Cred_T, No_Ceil, Buf, L, Rt);
            declare
               H1 : constant Byte_Array := Slice (Buf, L);
            begin
               Admit (X2, F0, R_Eff, AA, AD, Cred_T, No_Ceil, Buf, L, Rt);
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
               Admit (Sess_A, F0, R_Eff, AA, AD, Cred_T, No_Ceil, Buf, L, Rt);
               To_B.Append (Slice (Buf, L));
               Admit (Sess_B, F0, R_Eff, BA, BD, Cred_T, No_Ceil, Buf, L, Rt);
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

      ------------------------------------------------------------------
      --  (i) Sessions between real stores (AUDIT.md H12)
      ------------------------------------------------------------------
      if Contracts_On then
         Store_Sessions (By_Slots, Near => True);
         Put_Line ("SKIP H12 (full slice): the 512-record form of the store sessions (check"
                   & " mode: under -gnata the digest contracts of 512 held records do not"
                   & " end in reasonable time; it runs with MODE=release)");
      else
         Store_Sessions (By_Slots, Near => True);
         Store_Sessions (By_Slots, Near => False);
         Store_Sessions (By_Slice, Near => False);
      end if;
      if Failed then
         Set_Exit_Status (Failure);
      end if;
   end Run_All;

begin
   null;
end Test_Reconcile;
