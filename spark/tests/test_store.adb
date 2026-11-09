--  Test main for Kome.Store (DESIGN.md §7, §9 T11, T13, T18). Real signed
--  frames from Kome.Records go through the store.
--
--  The tests cover these items:
--    * the HEADER against independent vectors (vectors/store.txt);
--    * put and overwrite (the older frame leaves the index), a dominated
--      re-offer and a duplicate (nothing appended), and a DEL that frees
--      every field of its entity;
--    * refusals that change nothing: an unrostered author and a record
--      above the ceiling (Inadmissible), a full frontier (No_Space), a full
--      slice (Auth_Full) and a full log (Log_Full);
--    * a dominated PUT and a dominated roster on a full log give Dominated,
--      not No_Space;
--    * an authorization record of a foreign founding key;
--    * expiry: the horizon of DESIGN.md §7 with del_ttl_eff and the maxceil
--      clamp; EXPIRE logged iff a record was removed or the horizon was
--      lowered; periodic calls that do not make the log larger; a clock set
--      back; a horizon below 0;
--    * apply-then-expire: an arriving expired DEL frees its entity, the
--      store logs it as APPLY_EXPIRED, and the DEL is not held;
--    * compaction: the HEADER, authorization records first, each part in
--      index order, byte for byte, EXPIRE (horizon);
--    * the index itself never causes a refusal (index = F);
--    * replay (T18) after these sequences: a roster refresh, a
--      dominated-on-arrival roster and a stale incomparable roster; a member
--      revoke; a GRANT that arrives after a PUT that it admits; a clock set
--      back and a stale PUT; a data row full of DELs that expire. When the
--      store opens again from the log, it has the same held set (Holds both
--      ways), the same index entries up to order, the same
--      Kome.Digest.Frontier_Digest and a horizon at most the live horizon.
--      Its log is the input byte for byte;
--    * Open_From_Log opens at any data capacity that the log replays at
--      and refuses another slice (No_Space); a corrupt or torn log is
--      Malformed, and Valid_Length names the replayed prefix (H23); a
--      duplicated APPLY replays as OK; a logged horizon above the bound
--      is clamped (H24);
--    * the counters Auth_Gen (H11) and Expire_Mark (H28), the compaction
--      duty Compact_Due (H26) and Horizon_Frozen (N4).
--  The build uses -gnata, so the tests also execute every Pre / Post (Valid
--  included) and every ghost lemma on these stores.
pragma Ada_2022;
with Ada.Text_IO;      use Ada.Text_IO;
with Ada.Command_Line; use Ada.Command_Line;
with Ada.Directories;
with Ada.Exceptions;   use Ada.Exceptions;
with Kome;             use Kome;
with Kome.Headers;     use Kome.Headers;
with Kome.Registers;   use type Kome.Registers.Writer_Count;
with Kome.Frontier;    use Kome.Frontier;
with Kome.Keys;        use Kome.Keys;
with Kome.Crypto;
with Kome.Records;     use Kome.Records;
with Kome.Digest;
with Kome.Store;       use Kome.Store;

procedure Test_Store with SPARK_Mode => Off is

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

   --  A reduced X25519 encoding that is not low order (E5).
   function Good_DH (Seed : Natural) return Pubkey is
      K : Pubkey := Pubkey (Fill (Pubkey_Len, Seed));
   begin
      K (31) := K (31) and 16#3F#;
      return K;
   end Good_DH;

   --  One roster member { sign_pk dh_pk nonce box } with a good dh_pk.
   function Member (PK : Pubkey; Seed : Natural) return Byte_Array is
     (PK & Good_DH (Seed) & Fill (Nonce_Len, Seed + 1) & Fill (Box_Len, Seed + 2));

   function Hex (S : String) return Byte_Array is
      function Nib (C : Character) return Byte is
        (case C is
            when '0' .. '9' => Character'Pos (C) - Character'Pos ('0'),
            when 'a' .. 'f' => Character'Pos (C) - Character'Pos ('a') + 10,
            when 'A' .. 'F' => Character'Pos (C) - Character'Pos ('A') + 10,
            when others     => 0);
   begin
      return [for I in 0 .. S'Length / 2 - 1 =>
                Nib (S (S'First + 2 * I)) * 16 + Nib (S (S'First + 2 * I + 1))];
   end Hex;

   function Find (Rel : String) return String is
   begin
      if Ada.Directories.Exists (Rel) then
         return Rel;
      elsif Ada.Directories.Exists ("../" & Rel) then
         return "../" & Rel;
      elsif Ada.Directories.Exists ("../../" & Rel) then
         return "../../" & Rel;
      else
         return Rel;
      end if;
   end Find;

   --  Big-endian u48 and u32, written independently of Kome.Records.
   function BE48 (V : U48) return Byte_Array is
     ([for I in 0 .. 5 => Byte ((V / 2 ** (8 * (5 - I))) mod 256)]);
   function BE32 (V : Natural) return Byte_Array is
     ([for I in 0 .. 3 => Byte ((V / 2 ** (8 * (3 - I))) mod 256)]);

   Day : constant U48 := 86_400_000;
   TTL : constant U48 := Del_TTL_Min;   --  7 days

   Root_SK, Root2_SK, RootX_SK, Author_SK, Author2_SK, Stranger_SK : Kome.Crypto.Secret_Key;
   Root_PK, Root2_PK, RootX_PK, Author_PK, Author2_PK, Stranger_PK : Pubkey;
   Salt_A : constant Salt := Salt (Fill (Salt_Len, 90));
   NS_A   : NS_Id;
   NS     : Id128;
   Fnd    : Key256;

   --  The certified root Root2, with two certificates (two caps), so that
   --  it can sign two different GRANTs of one subject.
   Cap2           : constant U48 := 1000 * Day;
   Cert2a, Cert2b : Sig;

   ---------------------------------------------------------------------------
   --  Frames.
   ---------------------------------------------------------------------------

   function Roster_Of
     (SK : Kome.Crypto.Secret_Key; PK : Pubkey; Cap : U48; Cert : Sig;
      Gen, Ceil, Del_TTL : U48; Members : Byte_Array) return Byte_Array
   is
      R : Roster_Record :=
        Make_Roster (Root_PK, Salt_A, PK, Cap, Cert, Good_DH (77), Gen, Ceil, Del_TTL, 0,
                     [], Members);
   begin
      Sign (R, SK);
      return Encode (R);
   end Roster_Of;

   function Founding_Roster (Gen, Ceil : U48; Del_TTL : U48 := TTL) return Byte_Array is
     (Roster_Of (Root_SK, Root_PK, 0, Zero_Sig, Gen, Ceil, Del_TTL,
                 Member (Author_PK, 11) & Member (Author2_PK, 21)));

   function Grant_Of
     (SK : Kome.Crypto.Secret_Key; PK : Pubkey; Cap : U48; Cert : Sig; Subject : Pubkey)
      return Byte_Array
   is
      G : Grant_Record := Make_Grant (Root_PK, Salt_A, PK, Cap, Cert, Subject);
   begin
      Sign (G, SK);
      return Encode (G);
   end Grant_Of;

   function Founding_Grant (Subject : Pubkey) return Byte_Array is
     (Grant_Of (Root_SK, Root_PK, 0, Zero_Sig, Subject));

   function Revoke_Of (Subject : Pubkey; From_T, Rev_Seq : U48) return Byte_Array is
      R : Revoke_Record :=
        Make_Revoke (Root_PK, Salt_A, Root_PK, 0, Zero_Sig, Subject, From_T, Rev_Seq);
   begin
      Sign (R, Root_SK);
      return Encode (R);
   end Revoke_Of;

   function Put_Of
     (Ent : Byte; Field : Character; T, Seq : U48; Value : Byte_Array;
      SK  : Kome.Crypto.Secret_Key; PK : Pubkey) return Byte_Array
   is
      R : Put_Record :=
        Make_Put (NS_A, Ent_Id (Fill (Ent_Len, Natural (Ent))),
                  [Character'Pos (Field)], T, Seq, PK, Value);
   begin
      Sign (R, SK);
      return Encode (R);
   end Put_Of;

   function Put_Of (Ent : Byte; Field : Character; T, Seq : U48; Value : Byte_Array)
     return Byte_Array is (Put_Of (Ent, Field, T, Seq, Value, Author_SK, Author_PK));

   function Del_Of (Ent : Byte; T, Seq : U48) return Byte_Array is
      R : Del_Record;
   begin
      R.C := (NS => NS_A, Ent => Ent_Id (Fill (Ent_Len, Natural (Ent))),
              T => T, Seq => Seq, Author => Author_PK);
      Sign (R, Author_SK);
      return Encode (R);
   end Del_Of;

   function Hdr (F : Byte_Array) return Header is (Header_Of (F));

   function Cell_Of (Field : Character) return Key256 is
     (To_Key256 (Kome.Crypto.Blake2b_256 ([Character'Pos (Field)])));

   function Ent_Of (Ent : Byte) return Id128 is
     (To_Id128 (Ent_Id (Fill (Ent_Len, Natural (Ent)))));

   ---------------------------------------------------------------------------
   --  Operations and comparisons.
   ---------------------------------------------------------------------------

   procedure Put
     (S : in out Store_T; L : in out Lattice; F : Byte_Array; Off : out Log_Size;
      St : out Status) is
   begin
      if not Verified (F) then
         raise Program_Error with "test frame not well-formed";
      end if;
      Put_Frame (S, L, F, Hdr (F), Off, St);
   end Put;

   procedure Put (S : in out Store_T; L : in out Lattice; F : Byte_Array; St : out Status) is
      Off : Log_Size;
   begin
      Put (S, L, F, Off, St);
   end Put;

   procedure Put (S : in out Store_T; L : in out Lattice; F : Byte_Array) is
      St : Status;
   begin
      Put (S, L, F, St);
      if St /= OK then
         raise Program_Error with "setup frame refused: " & St'Image;
      end if;
   end Put;

   procedure Exp (S : in out Store_T; L : in out Lattice; Now : U48) is
      St : Status;
   begin
      Kome.Store.Expire (S, L, Now, St);
      if St /= OK then
         raise Program_Error with "setup expire refused";
      end if;
   end Exp;

   function Frame_Of (S : Store_T; I : Positive) return Byte_Array is
     (Read_Frame (S, Entry_At (S, I).Off));

   function Has_Header (S : Store_T; X : Header) return Boolean is
     (for some I in 1 .. Entries (S) => Entry_At (S, I).H = X);

   --  The frame of each index entry decodes to its header (tested, not
   --  proved).
   function Every_Frame_Matches (S : Store_T) return Boolean is
     (for all I in 1 .. Entries (S) =>
        Is_Record_Frame (Frame_Of (S, I))
        and then Hdr (Frame_Of (S, I)) = Entry_At (S, I).H
        and then Frame_Of (S, I)'Length = Entry_At (S, I).Len);

   --  A scan of the log as a file (offset 0, then Next_Offset) visits
   --  exactly the entry chain of the invariant and stops at the end of the
   --  log.
   function Scan_Matches_Chain (S : Store_T; L : Lattice) return Boolean is
      Off : Natural := 0;
      K   : Natural := 0;
   begin
      Lemma_Scan (S, L);
      while Off < Log_Length (S) loop
         K := K + 1;
         if K > Log_Entries (S) or else Entry_Start (S, K) /= Off
           or else not Has_Log_Entry (S, Off)
           or else (Op_At (S, Off) = Op_Header) /= (K = 1)
         then
            return False;
         end if;
         Off := Next_Offset (S, Off);
      end loop;
      return K = Log_Entries (S) and then Off = Log_Length (S);
   end Scan_Matches_Chain;

   --  The index is F exactly.
   function Index_Is_F (S : Store_T; L : Lattice) return Boolean is
     (Entries (S) = Kome.Frontier.Count (L)
      and then (for all K in 1 .. Kome.Frontier.Count (L) => Indexed (S, Held (L, K)))
      and then (for all I in 1 .. Entries (S) => Holds (L, Entry_At (S, I).H)));

   function Same_Set (A, B : Lattice) return Boolean is
     (Kome.Frontier.Count (A) = Kome.Frontier.Count (B)
      and then (for all K in 1 .. Kome.Frontier.Count (A) => Holds (B, Held (A, K)))
      and then (for all K in 1 .. Kome.Frontier.Count (B) => Holds (A, Held (B, K))));

   function Same_Index (A, B : Store_T) return Boolean is
     (Entries (A) = Entries (B)
      and then (for all I in 1 .. Entries (A) => Indexed (B, Entry_At (A, I).H))
      and then (for all I in 1 .. Entries (B) => Indexed (A, Entry_At (B, I).H)));

   --  T18: the same held set (and thus the same registers and digest), the
   --  same index entries up to order, and a horizon at most the live horizon.
   function T18 (S : Store_T; L : Lattice; R : Store_T; RL : Lattice) return Boolean is
     (Valid (R, RL)
      and then Same_Set (L, RL)
      and then Same_Index (S, R)
      and then Kome.Digest.Frontier_Digest (L) = Kome.Digest.Frontier_Digest (RL)
      and then Kome.Registers.Ceil (Regs (L)) = Kome.Registers.Ceil (Regs (RL))
      and then Kome.Registers.Count (Regs (L)) = Kome.Registers.Count (Regs (RL))
      and then Horizon (R) <= Horizon (S)
      and then Expire_Mark (R) <= Expire_Mark (S)
      and then Log_Bytes (R) = Log_Bytes (S));

   --  The number of APPLY entries of authorization records in the log:
   --  Auth_Gen after a reopen (AUDIT.md H11).
   function Auth_Applies (S : Store_T) return Natural is
      N : Natural := 0;
   begin
      for K in 2 .. Log_Entries (S) loop
         declare
            Off : constant Natural := Entry_Start (S, K);
         begin
            if Op_At (S, Off) = Op_Apply
              and then Is_Auth_Frame (Read_Frame (S, Off))
            then
               N := N + 1;
            end if;
         end;
      end loop;
      return N;
   end Auth_Applies;

   --  An EXPIRE entry with the code C, as the log writes it.
   function Expire_Entry (C : U48) return Byte_Array is
     (Byte_Array'(0 => Op_Expire) & BE48 (C));

   --  The compacted layout: authorization entries first, then data.
   function Auth_First (S : Store_T) return Boolean is
     (for all I in 1 .. Entries (S) =>
        (for all J in I + 1 .. Entries (S) =>
           (if Is_Data (Entry_At (S, I).H) then Is_Data (Entry_At (S, J).H))));

   function Position_Of (S : Store_T; X : Header) return Natural is
   begin
      for I in 1 .. Entries (S) loop
         if Entry_At (S, I).H = X then
            return I;
         end if;
      end loop;
      return 0;
   end Position_Of;

   --  An APPLY entry for Frame, as the log writes it.
   function Apply_Entry (Frame : Byte_Array) return Byte_Array is
     (Byte_Array'(0 => Op_Apply) & BE32 (Frame'Length) & Frame);

   Cap     : constant := 32;
   Slice   : constant := 8;
   ICap    : constant := Cap + Signers_Max * Slice;
   LCap    : constant := 16_384;

   procedure Fresh_Store (S : out Store_T; L : out Lattice) is
   begin
      L := Empty (NS, Fnd, L.Cap, L.Slice);
      Open (Root_PK, Salt_A, L, S);
   end Fresh_Store;

   procedure Reopen
     (S : Store_T; R : out Store_T; RL : out Lattice; St : out Status)
   is
      VL : Log_Size;
   begin
      Open_From_Log (Log_Bytes (S), RL, R, VL, St);
      if St = OK and then VL /= Log_Length (S) then
         raise Program_Error with "Valid_Length is not the input length on OK";
      end if;
   end Reopen;

   --  A State contains a Register_File of Writers_Max keys (256 KiB). Under
   --  -gnata, each evaluation of a Post copies states and stores, so the
   --  checks run in a task with a large stack.
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
   Kome.Crypto.Key_Pair (Seed_Of (1), Author_SK, Author_PK);
   Kome.Crypto.Key_Pair (Seed_Of (2), Stranger_SK, Stranger_PK);
   Kome.Crypto.Key_Pair (Seed_Of (3), Root_SK, Root_PK);
   Kome.Crypto.Key_Pair (Seed_Of (4), Root2_SK, Root2_PK);
   Kome.Crypto.Key_Pair (Seed_Of (5), Author2_SK, Author2_PK);
   Kome.Crypto.Key_Pair (Seed_Of (6), RootX_SK, RootX_PK);
   NS_A := Collection_Id (Root_PK, Salt_A);
   NS := To_Id128 (NS_A);
   Fnd := To_Key256 (Root_PK);
   Cert2a := Make_Cert (Root_SK, NS_A, Root2_PK, Cap2);
   Cert2b := Make_Cert (Root_SK, NS_A, Root2_PK, Cap2 + 1);

   ---------------------------------------------------------------------------
   --  Known-answer vectors: the HEADER and EXPIRE encodings.
   ---------------------------------------------------------------------------
   declare
      File    : File_Type;
      Headers : Natural := 0;
      Expires : Natural := 0;
      Ok      : Boolean := True;
   begin
      Open (File, In_File, Find ("vectors/store.txt"));
      while not End_Of_File (File) loop
         declare
            Line : constant String := Get_Line (File);
            function Field (N : Positive) return String is
               Start : Natural := Line'First;
               Count : Natural := 0;
            begin
               for I in Line'Range loop
                  if Line (I) = ' ' then
                     Count := Count + 1;
                     if Count = N then
                        return Line (Start .. I - 1);
                     end if;
                     Start := I + 1;
                  end if;
               end loop;
               return Line (Start .. Line'Last);
            end Field;
         begin
            if Line'Length > 7 and then Line (Line'First .. Line'First + 6) = "header " then
               declare
                  RK  : constant Pubkey := Pubkey (Hex (Field (2)));
                  SL  : constant Salt := Salt (Hex (Field (3)));
                  DC  : constant Natural := Natural'Value (Field (4));
                  SC  : constant Natural := Natural'Value (Field (5));
                  Exp : constant Byte_Array := Hex (Field (6));
                  VL  : Lattice (DC, SC);
                  VS  : Store_T (DC + Signers_Max * SC, 128);
               begin
                  VL := Empty (To_Id128 (Collection_Id (RK, SL)), To_Key256 (RK), DC, SC);
                  Open (RK, SL, VL, VS);
                  Ok := Ok and then Log_Bytes (VS) = Exp;
                  Headers := Headers + 1;
               end;
            elsif Line'Length > 7 and then Line (Line'First .. Line'First + 6) = "expire " then
               declare
                  C   : constant U48 := U48'Value (Field (2));
                  Exp : constant Byte_Array := Hex (Field (3));
               begin
                  Ok := Ok and then Horizon_Code (Horizon_Of_Code (C)) = C
                    and then Byte_Array'(0 => Op_Expire) & BE48 (C) = Exp;
                  Expires := Expires + 1;
               end;
            end if;
         end;
      end loop;
      Close (File);
      Check ("vectors: 3 HEADERs written by Open and 4 EXPIRE codes match hashlib",
             Ok and then Headers = 3 and then Expires = 4);
      Check ("horizon codes: none is 2**48 - 1, a horizon is its own code",
             Horizon_Code (No_Horizon) = U48'Last
             and then Horizon_Of_Code (U48'Last) = No_Horizon
             and then Horizon_Code (0) = 0
             and then Horizon_Of_Code (U48'Last - 1) = Time64 (U48'Last - 1));
   end;

   declare
      R1  : constant Byte_Array := Founding_Roster (1, 100 * Day);
      G1  : constant Byte_Array := Founding_Grant (Author_PK);
      P1  : constant Byte_Array := Put_Of (1, 'n', 10 * Day, 1, [1, 2, 3]);
      P2  : constant Byte_Array := Put_Of (1, 'n', 20 * Day, 2, [4, 5]);
      P3  : constant Byte_Array := Put_Of (1, 'a', 15 * Day, 3, []);
      D1  : constant Byte_Array := Del_Of (1, 30 * Day, 4);
      P4  : constant Byte_Array := Put_Of (2, 'n', 40 * Day, 5, [9]);
      P5  : constant Byte_Array := Put_Of (3, 'x', 20 * Day, 6, [7, 7]);
      D2  : constant Byte_Array := Del_Of (3, 25 * Day, 7);
      PX  : constant Byte_Array := Put_Of (4, 'n', 10 * Day, 1, [1], Stranger_SK, Stranger_PK);
      PH  : constant Byte_Array := Put_Of (5, 'n', 200 * Day, 8, [1]);
      S       : Store_T (ICap, LCap);
      SL      : Lattice (Cap, Slice);
      Raw     : Store_T (ICap, LCap);   --  the log before compaction
      RawL    : Lattice (Cap, Slice);
      Off     : Log_Size;
      St      : Status;
      Found   : Boolean;
      I       : Held_Count;
   begin
      ------------------------------------------------------------------------
      --  Open.
      ------------------------------------------------------------------------
      Fresh_Store (S, SL);
      Check ("open: valid, the HEADER only",
             Valid (S, SL) and then Entries (S) = 0 and then Log_Length (S) = Header_Len
             and then Log_Entries (S) = 1 and then Horizon (S) = No_Horizon
             and then Logged_Cap (S) = Cap and then Logged_Slice (S) = Slice
             and then Collection (S) = NS and then Founding (S) = Fnd
             and then Auth_Gen (S) = 0 and then Expire_Mark (S) = 0
             and then not Compact_Due (S));
      Lemma_Log_Header (S, SL);
      Lemma_Valid_Facts (S, SL);
      Check ("open: the HEADER bytes (op, magic, version, ns, root_pk, salt, caps)",
             Log_Bytes (S) =
               Byte_Array'(0 => 0) & Magic & Byte_Array'(0 => 1) & NS_A & Root_PK & Salt_A
               & BE32 (Cap) & Byte_Array'(0 => 0, 1 => Slice));

      ------------------------------------------------------------------------
      --  Put.
      ------------------------------------------------------------------------
      Put (S, SL, R1, Off, St);
      Check ("roster: OK, an APPLY at offset 80, maxceil raised",
             St = OK and then Off = Header_Len and then Entries (S) = 1
             and then Log_Length (S) = Header_Len + Apply_Prefix + R1'Length
             and then Op_At (S, Off) = Op_Apply and then Read_Frame (S, Off) = R1
             and then Kome.Registers.Ceil (Regs (SL)) = 100 * Day);
      Check ("roster: Auth_Gen went up to 1", Auth_Gen (S) = 1);
      Put (S, SL, G1, St);
      Check ("grant: OK, its subject is a writer",
             St = OK and then Entries (S) = 2
             and then Kome.Registers.In_W (Regs (SL), To_Key256 (Author_PK)));
      Check ("grant: Auth_Gen went up to 2", Auth_Gen (S) = 2);

      Put (S, SL, P1, Off, St);
      Check ("put: OK, appended", St = OK and then Read_Frame (S, Off) = P1);
      Check ("put: Auth_Gen unchanged by a data record", Auth_Gen (S) = 2);
      Find_Cell (S, SL, NS, Ent_Of (1), Cell_Of ('n'), Found, I);
      Check ("put: the cell index finds it",
             Found and then Entry_At (S, I).Off = Off and then Entry_At (S, I).H = Hdr (P1));

      declare
         L : constant Log_Size := Log_Length (S);
      begin
         Put (S, SL, P2, Off, St);
         Find_Cell (S, SL, NS, Ent_Of (1), Cell_Of ('n'), Found, I);
         Check ("overwrite: newer PUT indexed, older gone from index and frontier",
                St = OK and then Off = L and then Found and then Entry_At (S, I).H = Hdr (P2)
                and then not Has_Header (S, Hdr (P1)) and then not Holds (SL, Hdr (P1)));
         Check ("overwrite: the log is append-only (the old frame is still there)",
                Read_Frame (S, Off - Apply_Prefix - P1'Length) = P1
                and then Log_Length (S) = L + Apply_Prefix + P2'Length);
      end;
      declare
         L : constant Log_Size := Log_Length (S);
      begin
         Put (S, SL, P1, Off, St);
         Check ("older PUT re-offered: Dominated, nothing appended, Off = the log length",
                St = Dominated and then Log_Length (S) = L and then Off = L);
         Put (S, SL, P2, Off, St);
         Check ("duplicate: OK, nothing appended, Off = the log length",
                St = OK and then Log_Length (S) = L and then Off = L);
      end;
      Put (S, SL, P3, St);
      Check ("second field of the entity", St = OK and then Entries (S) = 4);
      Put (S, SL, D1, St);
      Find_Cell (S, SL, NS, Ent_Of (1), Cell_Of ('n'), Found, I);
      Check ("delete: DEL indexed, every field of the entity freed",
             St = OK and then Entries (S) = 3 and then Has_Header (S, Hdr (D1))
             and then not Has_Header (S, Hdr (P2)) and then not Has_Header (S, Hdr (P3))
             and then not Found and then not Holds (SL, Hdr (P2)));
      Put (S, SL, P4);
      Put (S, SL, P5);
      Check ("other entities; the index is F", Entries (S) = 5 and then Index_Is_F (S, SL));
      Check ("every entry's frame decodes to its header", Every_Frame_Matches (S));
      Check ("the log scans as its entry chain", Scan_Matches_Chain (S, SL));

      ------------------------------------------------------------------------
      --  Refusals change nothing.
      ------------------------------------------------------------------------
      declare
         B  : constant Store_T := S;
         BL : constant Lattice := SL;
      begin
         Put (S, SL, PX, Off, St);
         Check ("author without a GRANT: Inadmissible, nothing changed, Off = the log length",
                St = Inadmissible and then S = B and then SL = BL and then Off = Log_Length (B));
         Put (S, SL, PH, St);
         Check ("t above maxceil: Inadmissible, nothing changed",
                St = Inadmissible and then S = B and then SL = BL);
      end;

      --  An authorization record of a foreign founding key. Its ns is the
      --  collection of that key, so the precondition of Put_Frame
      --  (H.NS = Collection) already excludes it, unless a 128-bit collision
      --  occurs. But step 0 of the store still names it, and a log that
      --  contains it is Malformed.
      declare
         GX : Byte_Array := Founding_Grant (Author2_PK);
      begin
         declare
            G : Grant_Record := Make_Grant (RootX_PK, Salt_A, RootX_PK, 0, Zero_Sig, Author2_PK);
         begin
            Sign (G, RootX_SK);
            GX := Encode (G);
         end;
         Check ("foreign root_pk: Foreign_Root, and its ns is not the collection's",
                Verified (GX) and then Foreign_Root (S, GX)
                and then Hdr (GX).NS /= Collection (S)
                and then not Foreign_Root (S, G1) and then not Foreign_Root (S, P1));
         declare
            R  : Store_T (ICap, LCap);
            RL : Lattice (Cap, Slice);
            VL : Log_Size;
         begin
            Open_From_Log (Log_Bytes (S) & Apply_Entry (GX), RL, R, VL, St);
            Check ("foreign root_pk: a log carrying it is Malformed, Valid_Length before it",
                   St = Malformed and then VL = Log_Length (S) and then Valid (R, RL)
                   and then Log_Bytes (R) = Log_Bytes (S) and then Same_Set (SL, RL));
         end;
      end;

      ------------------------------------------------------------------------
      --  Room: Dominated never needs room; No_Space and Auth_Full change
      --  nothing.
      ------------------------------------------------------------------------
      declare
         Room   : constant Natural :=
           Header_Len + Apply_Prefix + R1'Length + Apply_Prefix + G1'Length
           + Apply_Prefix + P2'Length + 3;
         Sm     : Store_T (ICap, Room);
         SmL    : Lattice (Cap, Slice);
         Stale  : constant Byte_Array := Founding_Roster (0, 50 * Day);
         R2     : constant Byte_Array := Founding_Roster (2, 200 * Day);
         DE     : constant Byte_Array := Del_Of (1, 24 * Day, 9);
         DN     : constant Byte_Array := Del_Of (9, 24 * Day, 10);
      begin
         SmL := Empty (NS, Fnd, Cap, Slice);
         Open (Root_PK, Salt_A, SmL, Sm);
         Put (Sm, SmL, R1);
         Put (Sm, SmL, G1);
         Put (Sm, SmL, P2);
         Check ("small log: holds the roster, the grant and one PUT, no room for more",
                Log_Short (Sm, Apply_Prefix + P1'Length)
                and then Log_Short (Sm, Apply_Prefix + DE'Length));
         declare
            B  : constant Store_T := Sm;
            BL : constant Lattice := SmL;
         begin
            Put (Sm, SmL, P1, St);
            Check ("log full: a dominated PUT is Dominated (not No_Space), nothing changed",
                   St = Dominated and then Sm = B and then SmL = BL);
            Put (Sm, SmL, Stale, St);
            Check ("log full: a dominated roster is Dominated (not No_Space), nothing changed",
                   St = Dominated and then Sm = B and then SmL = BL);
            Put (Sm, SmL, P2, St);
            Check ("log full: a duplicate needs no room and is OK",
                   St = OK and then Sm = B and then SmL = BL);
            Put (Sm, SmL, P4, St);
            Check ("log full: a PUT Frontier would hold is Log_Full, nothing changed",
                   St = Log_Full and then Sm = B and then SmL = BL);
            Put (Sm, SmL, R2, St);
            Check ("log full: a roster refresh is Log_Full, maxceil not raised",
                   St = Log_Full and then Sm = B and then SmL = BL
                   and then Kome.Registers.Ceil (Regs (SmL)) = 100 * Day);
         end;
         Kome.Store.Expire (Sm, SmL, 32 * Day, St);
         Check ("log full: an Expire that removes nothing raises the horizon, logs nothing",
                St = OK and then Horizon (Sm) = Time64 (25 * Day));
         declare
            B  : constant Store_T := Sm;
            BL : constant Lattice := SmL;
         begin
            Put (Sm, SmL, DE, St);
            Check ("log full: an expired DEL that drops something is Log_Full, nothing changed",
                   St = Log_Full and then Sm = B and then SmL = BL
                   and then Holds (SmL, Hdr (P2)));
            Put (Sm, SmL, DN, St);
            Check ("log full: an expired DEL that drops nothing is OK and changes nothing",
                   St = OK and then Sm = B and then SmL = BL);
         end;
      end;

      declare
         --  A data row of 2.
         Tiny  : Store_T (2 + Signers_Max * Slice, LCap);
         TinyL : Lattice (2, Slice);
      begin
         TinyL := Empty (NS, Fnd, 2, Slice);
         Open (Root_PK, Salt_A, TinyL, Tiny);
         Put (Tiny, TinyL, R1);
         Put (Tiny, TinyL, G1);
         Put (Tiny, TinyL, P1);
         Put (Tiny, TinyL, P4);
         declare
            B  : constant Store_T := Tiny;
            BL : constant Lattice := TinyL;
         begin
            Put (Tiny, TinyL, P5, St);
            Check ("data row full: No_Space, nothing changed",
                   St = No_Space and then Tiny = B and then TinyL = BL);
         end;
         Put (Tiny, TinyL, P2, St);
         Check ("data row full: an overwrite still fits (it frees its slot); index = F",
                St = OK and then Has_Header (Tiny, Hdr (P2))
                and then not Has_Header (Tiny, Hdr (P1)) and then Index_Is_F (Tiny, TinyL));
      end;

      declare
         --  A slice of 2: the founding roster and one GRANT fill it.
         Sl   : Store_T (Cap + Signers_Max * 2, LCap);
         SlL  : Lattice (Cap, 2);
         G2   : constant Byte_Array := Founding_Grant (Author2_PK);
         R2   : constant Byte_Array := Founding_Roster (2, 100 * Day);
      begin
         SlL := Empty (NS, Fnd, Cap, 2);
         Open (Root_PK, Salt_A, SlL, Sl);
         Put (Sl, SlL, R1);
         Put (Sl, SlL, G1);
         declare
            B  : constant Store_T := Sl;
            BL : constant Lattice := SlL;
         begin
            Put (Sl, SlL, G2, St);
            Check ("slice full: Auth_Full, nothing changed, no writer added",
                   St = Auth_Full and then Sl = B and then SlL = BL
                   and then not Kome.Registers.In_W (Regs (SlL), To_Key256 (Author2_PK)));
         end;
         Put (Sl, SlL, R2, St);
         Check ("slice full: a roster that dominates the held one frees its place",
                St = OK and then Holds (SlL, Hdr (R2)) and then not Holds (SlL, Hdr (R1))
                and then Index_Is_F (Sl, SlL));
      end;

      Raw := S;
      RawL := SL;

      ------------------------------------------------------------------------
      --  Expire (D10): horizon = min (now, maxceil) - del_ttl_eff.
      ------------------------------------------------------------------------
      declare
         L0 : constant Log_Size := Log_Length (S);
         E0 : constant Natural := Log_Entries (S);
      begin
         Check ("before expiry: the mark is 0; the clamp is not active at 36 d (maxceil 100 d)",
                Expire_Mark (S) = 0 and then not Horizon_Frozen (SL, 36 * Day)
                and then Horizon_Frozen (SL, 100 * Day + 1));
         Kome.Store.Expire (S, SL, 36 * Day, St);
         Check ("expire at 36 d (DEL at 30 d, del_ttl 7 d): kept, horizon 29 d, nothing logged",
                St = OK and then Horizon (S) = Time64 (29 * Day)
                and then Has_Header (S, Hdr (D1)) and then Holds (SL, Hdr (D1))
                and then Log_Length (S) = L0);
         Check ("the mark follows the raised horizon (29 d)", Expire_Mark (S) = 29 * Day);
         Kome.Store.Expire (S, SL, 37 * Day, St);
         Check ("expire at 37 d: the DEL leaves F and the index, EXPIRE (30 d) logged",
                St = OK and then Horizon (S) = Time64 (30 * Day)
                and then not Has_Header (S, Hdr (D1)) and then not Holds (SL, Hdr (D1))
                and then Has_Header (S, Hdr (P4)) and then Index_Is_F (S, SL)
                and then Log_Entries (S) = E0 + 1
                and then Log_Length (S) = L0 + Expire_Len
                and then Op_At (S, L0) = Op_Expire
                and then Code_At (S, L0 + 1) = 30 * Day
                and then Expire_Mark (S) = 30 * Day and then Auth_Gen (S) = 2);
         Check ("the EXPIRE entry is the vector's bytes",
                Byte_Array'[for J in 0 .. Expire_Len - 1 => Log_Byte (S, L0 + J)]
                = Hex ("0300009a7ec800"));
      end;
      declare
         L0 : constant Log_Size := Log_Length (S);
      begin
         for K in 1 .. 5 loop
            Exp (S, SL, 37 * Day + U48 (K));
         end loop;
         Check ("periodic Expire calls that remove nothing do not grow the log",
                Log_Length (S) = L0 and then Horizon (S) = Time64 (30 * Day) + 5);
         Exp (S, SL, 1000 * Day);
         Check ("a clock far ahead is clamped to maxceil: horizon 100 d - 7 d, nothing logged",
                Horizon (S) = Time64 (93 * Day) and then Log_Length (S) = L0
                and then Horizon_Frozen (SL, 1000 * Day) and then Expire_Mark (S) = 93 * Day);
      end;

      --  Apply-then-expire.
      declare
         L0 : constant Log_Size := Log_Length (S);
      begin
         Put (S, SL, D2, Off, St);
         Check ("arriving expired DEL: applied, frees its entity, not held, not indexed",
                St = OK and then not Holds (SL, Hdr (D2)) and then not Has_Header (S, Hdr (D2))
                and then not Holds (SL, Hdr (P5)) and then not Has_Header (S, Hdr (P5))
                and then Index_Is_F (S, SL));
         Check ("it is logged as APPLY_EXPIRED (replay frees the same fields)",
                Off = L0 and then Op_At (S, Off) = Op_Apply_Expired
                and then Read_Frame (S, Off) = D2
                and then Log_Length (S) = L0 + Apply_Prefix + D2'Length);
         Put (S, SL, D2, St);
         Check ("re-offered expired DEL: drops nothing, OK, nothing appended",
                St = OK and then Log_Length (S) = L0 + Apply_Prefix + D2'Length);
      end;

      --  A clock set back, then a stale PUT.
      declare
         L0 : constant Log_Size := Log_Length (S);
         PS : constant Byte_Array := Put_Of (1, 'n', 25 * Day, 11, [6]);
      begin
         Kome.Store.Expire (S, SL, 20 * Day, St);
         Check ("clock stepped back: the horizon is lowered (13 d) and EXPIRE logged",
                St = OK and then Horizon (S) = Time64 (13 * Day)
                and then Log_Length (S) = L0 + Expire_Len
                and then Code_At (S, L0 + 1) = 13 * Day);
         Check ("a lowered horizon does not lower the mark (93 d)", Expire_Mark (S) = 93 * Day);
         Put (S, SL, PS, St);
         Check ("a stale PUT older than the expired DEL is held again (A4' residual)",
                St = OK and then Holds (SL, Hdr (PS)) and then Index_Is_F (S, SL));
         Kome.Store.Expire (S, SL, 3 * Day, St);
         Check ("a horizon below 0 is none, logged as 2**48 - 1",
                St = OK and then Horizon (S) = No_Horizon
                and then Code_At (S, Log_Length (S) - 6) = No_Horizon_Code);
         declare
            L1 : constant Log_Size := Log_Length (S);
         begin
            Exp (S, SL, 40 * Day);
            Check ("and raised again (33 d) without removing anything: not logged",
                   Horizon (S) = Time64 (33 * Day) and then Log_Length (S) = L1);
         end;
      end;

      --  No_Space from Expire: a full log refuses an EXPIRE that Expire must
      --  write.
      declare
         Room : constant Natural :=
           Header_Len + Apply_Prefix + R1'Length + Apply_Prefix + G1'Length
           + Apply_Prefix + D1'Length + 3;
         Sm   : Store_T (ICap, Room);
         SmL  : Lattice (Cap, Slice);
      begin
         SmL := Empty (NS, Fnd, Cap, Slice);
         Open (Root_PK, Salt_A, SmL, Sm);
         Put (Sm, SmL, R1);
         Put (Sm, SmL, G1);
         Put (Sm, SmL, D1);
         declare
            B  : constant Store_T := Sm;
            BL : constant Lattice := SmL;
         begin
            Kome.Store.Expire (Sm, SmL, 50 * Day, St);
            Check ("expire on a full log, something to remove: Log_Full, nothing changed",
                   St = Log_Full and then Sm = B and then SmL = BL
                   and then Holds (SmL, Hdr (D1)));
         end;
      end;

      ------------------------------------------------------------------------
      --  Compact, then open again (T18). Also open the raw log again.
      ------------------------------------------------------------------------
      declare
         Before  : constant Store_T := S;
         BeforeL : constant Lattice := SL;
         R       : Store_T (ICap, LCap);
         RL      : Lattice (Cap, Slice);
      begin
         Reopen (S, R, RL, St);
         Check ("reopen the uncompacted log (APPLY_EXPIRED, EXPIREs, a stale PUT): T18",
                St = OK and then T18 (S, SL, R, RL));
         Check ("reopen: Auth_Gen is the number of logged authorization APPLYs (2); "
                & "the mark is the largest logged horizon (30 d)",
                Auth_Gen (R) = 2 and then Auth_Applies (R) = 2
                and then Expire_Mark (R) = 30 * Day);
         Compact (S, SL);
         Check ("compact: frontier, horizon, counters and index records unchanged",
                SL = BeforeL and then Horizon (S) = Horizon (Before)
                and then Auth_Gen (S) = Auth_Gen (Before)
                and then Expire_Mark (S) = Expire_Mark (Before)
                and then Same_Index (S, Before) and then Index_Is_F (S, SL)
                and then not Compact_Due (S));
         Check ("compact: the HEADER, then authorization first, contiguous APPLYs",
                Log_Bytes (S) (0 .. Header_Len - 1) = Log_Bytes (Before) (0 .. Header_Len - 1)
                and then Auth_First (S)
                and then Entry_At (S, 1).Off = Header_Len
                and then (for all K in 1 .. Entries (S) - 1 =>
                            Entry_At (S, K + 1).Off = End_Of (Entry_At (S, K))));
         Check ("compact: then EXPIRE (horizon), and nothing else",
                Log_Length (S) = End_Of (Entry_At (S, Entries (S))) + Expire_Len
                and then Op_At (S, End_Of (Entry_At (S, Entries (S)))) = Op_Expire
                and then Code_At (S, End_Of (Entry_At (S, Entries (S))) + 1) = 33 * Day
                and then Log_Entries (S) = Entries (S) + 2
                and then Log_Length (S) < Log_Length (Before));
         Check ("compact: the same frames, byte for byte",
                (for all K in 1 .. Entries (S) =>
                   Frame_Of (S, K) = Frame_Of (Before, Position_Of (Before, Entry_At (S, K).H))));
         Check ("compact: frames decode to their headers", Every_Frame_Matches (S));
         Check ("compact: the entry chain scans", Scan_Matches_Chain (S, SL));
         Find_Cell (S, SL, NS, Ent_Of (2), Cell_Of ('n'), Found, I);
         Check ("compact: the cell index still finds the live PUT",
                Found and then Read_Frame (S, Entry_At (S, I).Off) = P4);
      end;
      declare
         R  : Store_T (ICap, LCap);
         RL : Lattice (Cap, Slice);
      begin
         Reopen (S, R, RL, St);
         Check ("reopen the compacted log: T18 (same set, index, digest, horizon <= live)",
                St = OK and then T18 (S, SL, R, RL));
         Check ("the reopened horizon is the compacted one (made durable); "
                & "the mark is that horizon (33 d), Auth_Gen the held authorization records",
                Horizon (R) = Horizon (S) and then Expire_Mark (R) = 33 * Day
                and then Auth_Gen (R) = 2);
      end;
      declare
         R  : Store_T (ICap, LCap);
         RL : Lattice (Cap, Slice);
      begin
         Kome.Store.Expire (Raw, RawL, 37 * Day, St);
         Reopen (Raw, R, RL, St);
         Check ("reopen an older log (before expiry): T18",
                St = OK and then T18 (Raw, RawL, R, RL));
      end;

      --  Capacities (AUDIT.md A11), corruption and Valid_Length (AUDIT.md
      --  H23). The compacted log holds 2 authorization records and 2 data
      --  records, then EXPIRE.
      declare
         R   : Store_T (ICap, LCap);
         RLs : Lattice (Cap - 1, Slice);
         RL1 : Lattice (1, Slice);
         R1s : Store_T (1 + Signers_Max * Slice, LCap);
         RLt : Lattice (Cap, Slice - 1);
         RLu : Lattice (Cap, Slice + 1);
         Ru  : Store_T (Cap + Signers_Max * (Slice + 1), LCap);
         RLb : Lattice (Cap + 4, Slice);
         Rb  : Store_T (Cap + 4 + Signers_Max * Slice, LCap * 2);
         Rs  : Store_T (ICap, 200);
         RL  : Lattice (Cap, Slice);
         Img : constant Byte_Array := Log_Bytes (S);
         VL  : Log_Size;
      begin
         Check ("the compacted log: 2 authorization and 2 data records",
                Entries (S) = 4 and then Data_Count (SL) = 2);
         Open_From_Log (Img, RLs, R, VL, St);
         Check ("reopen with a smaller data capacity that fits: OK, T18, the HEADER unchanged",
                St = OK and then T18 (S, SL, R, RLs) and then Logged_Cap (R) = Cap);
         Open_From_Log (Img, RL1, R1s, VL, St);
         Check ("reopen with a data capacity of 1 (2 data records): No_Space at the second "
                & "data APPLY; Valid_Length names it, and the pair is the replay of the prefix",
                St = No_Space and then VL = Entry_At (S, 4).Off
                and then Valid (R1s, RL1) and then Log_Length (R1s) = VL
                and then Log_Bytes (R1s) = Img (0 .. VL - 1)
                and then Entries (R1s) = 3 and then Data_Count (RL1) = 1);
         Open_From_Log (Img, RLt, R, VL, St);
         Check ("reopen with a smaller slice: No_Space, Valid_Length 0", St = No_Space and then VL = 0);
         Open_From_Log (Img, RLu, Ru, VL, St);
         Check ("reopen with a larger slice: No_Space (the slice is fixed)", St = No_Space);
         Open_From_Log (Img, RL, Rs, VL, St);
         Check ("reopen into a log buffer too small for the log: No_Space, Valid_Length 0",
                St = No_Space and then VL = 0);
         Open_From_Log (Img, RLb, Rb, VL, St);
         Check ("reopen with a larger data capacity: OK, T18, the HEADER keeps the old one",
                St = OK and then T18 (S, SL, Rb, RLb) and then Logged_Cap (Rb) = Cap);
         declare
            Img_B : constant Byte_Array := Log_Bytes (Rb);
            R2    : Store_T (Cap + 4 + Signers_Max * Slice, LCap * 2);
            RL2   : Lattice (Cap + 4, Slice);
         begin
            Open_From_Log (Img_B, RL, R, VL, St);
            Check ("its log still opens at the old capacity (T18)",
                   St = OK and then T18 (Rb, RLb, R, RL));
            Open_From_Log (Img_B, RL2, R2, VL, St);
            Check ("and at the new one byte for byte (T18)",
                   St = OK and then T18 (Rb, RLb, R2, RL2));
         end;
         declare
            Bad : Byte_Array := Img;
         begin
            Check ("Header_Well_Formed holds of a store's log", Header_Well_Formed (Img));
            Bad (HO_Magic) := Character'Pos ('K');
            Check ("Header_Well_Formed fails on a corrupt magic", not Header_Well_Formed (Bad));
            Open_From_Log (Bad, RL, R, VL, St);
            Check ("corrupt magic: Malformed, Valid_Length 0", St = Malformed and then VL = 0);
            Bad := Img;
            Bad (HO_NS + 3) := Bad (HO_NS + 3) xor 1;
            Check ("Header_Well_Formed fails on a wrong ns", not Header_Well_Formed (Bad));
            Open_From_Log (Bad, RL, R, VL, St);
            Check ("ns not BLAKE2b (root_pk || salt): Malformed", St = Malformed);
            Bad := Img;
            Bad (HO_Version) := 2;
            Open_From_Log (Bad, RL, R, VL, St);
            Check ("unknown version: Malformed", St = Malformed);
            Bad := Img;
            Bad (HO_Cap) := 16#FF#;
            Check ("Header_Well_Formed fails on a data_cap out of range",
                   not Header_Well_Formed (Bad));
            Open_From_Log (Bad, RL, R, VL, St);
            Check ("data_cap above Data_Size'Last: Malformed", St = Malformed);
            Bad := Img;
            Bad (Bad'Last - Expire_Len - 1) := Bad (Bad'Last - Expire_Len - 1) xor 16#40#;
            Open_From_Log (Bad, RL, R, VL, St);
            Check ("a frame whose signature fails: Malformed; Valid_Length is its offset, "
                   & "and the pair is the replay of the prefix",
                   St = Malformed and then VL = Entry_At (S, 4).Off
                   and then Valid (R, RL) and then Log_Bytes (R) = Img (0 .. VL - 1)
                   and then Entries (R) = 3);
         end;
         Open_From_Log (Img (0 .. Img'Last - 1), RL, R, VL, St);
         Check ("a truncated last entry (EXPIRE): Malformed, Valid_Length at its boundary",
                St = Malformed and then VL = Body_End (S)
                and then Valid (R, RL) and then Same_Set (SL, RL)
                and then Horizon (R) = No_Horizon);
         declare
            Cut : constant Byte_Array := Img (0 .. Entry_At (S, 4).Off + 20);
         begin
            Open_From_Log (Cut, RL, R, VL, St);
            Check ("a log cut inside the last APPLY: Malformed, Valid_Length at its start",
                   St = Malformed and then VL = Entry_At (S, 4).Off);
            Open_From_Log (Cut (0 .. VL - 1), RL, R, VL, St);
            Check ("truncated to Valid_Length, the log opens (T18-prefix)",
                   St = OK and then VL = Entry_At (S, 4).Off and then Entries (R) = 3);
         end;
         Open_From_Log (Img & Img (0 .. Header_Len - 1), RL, R, VL, St);
         Check ("a second HEADER: Malformed, Valid_Length = the whole log before it",
                St = Malformed and then VL = Img'Length);
         Open_From_Log (Img & Apply_Entry (P4), RL, R, VL, St);
         Check ("an APPLY of a record already held: OK as for Put_Frame, no change, "
                & "the entry stays in the log",
                St = OK and then VL = Img'Length + Apply_Prefix + P4'Length
                and then Same_Set (SL, RL) and then Same_Index (S, R)
                and then Log_Bytes (R) = Img & Apply_Entry (P4)
                and then Log_Entries (R) = Log_Entries (S) + 1
                and then Auth_Gen (R) = Auth_Gen (S));
         Open_From_Log (Img & Apply_Entry (P4) & Apply_Entry (P4), RL, R, VL, St);
         Check ("twice: still OK", St = OK and then Same_Index (S, R));
         Open_From_Log (Img (0 .. Header_Len - 2), RL, R, VL, St);
         Check ("a log shorter than the HEADER: Malformed", St = Malformed);
         Open_From_Log (Img (0 .. Header_Len - 1), RL, R, VL, St);
         Check ("a log that is only the HEADER: OK, empty",
                St = OK and then Kome.Frontier.Count (RL) = 0 and then Entries (R) = 0
                and then VL = Header_Len);
         --  The completeness clause of the Post of Open_From_Log. (Without it,
         --  a replay that refused every log would meet the contract.)
         Open_From_Log (Img (0 .. Header_Len - 1), RLb, Rb, VL, St);
         Check ("only the HEADER, a larger data capacity: OK, empty, the HEADER as logged",
                St = OK and then Kome.Frontier.Count (RLb) = 0 and then Entries (Rb) = 0
                and then Logged_Cap (Rb) = Cap and then Logged_Slice (Rb) = Slice
                and then Log_Length (Rb) = Header_Len);
      end;

      --  AUDIT.md H24: replay clamps a logged horizon to maxceil -
      --  del_ttl_eff of the frontier at that point.
      declare
         Img : constant Byte_Array := Log_Bytes (S);
         R   : Store_T (ICap, LCap);
         RL  : Lattice (Cap, Slice);
         VL  : Log_Size;
      begin
         Open_From_Log (Img & Expire_Entry (U48'Last - 1), RL, R, VL, St);
         Check ("an EXPIRE far above the bound replays at maxceil - del_ttl_eff (93 d), "
                & "the bytes stay",
                St = OK and then Horizon (R) = Time64 (93 * Day)
                and then Expire_Mark (R) = 93 * Day
                and then Log_Bytes (R) = Img & Expire_Entry (U48'Last - 1));
         Open_From_Log (Img & Expire_Entry (No_Horizon_Code), RL, R, VL, St);
         Check ("an EXPIRE (none) after it lowers the horizon to none",
                St = OK and then Horizon (R) = No_Horizon);
      end;

      --  The invariant, unpacked, on the final store.
      declare
         Ok : Boolean := True;
      begin
         for K in 1 .. Entries (S) loop
            Lemma_Entry_Held (S, SL, K);
            Lemma_Indexed (S, Entry_At (S, K).H);
            Lemma_Position (S, SL, K);
         end loop;
         for K in 1 .. Kome.Frontier.Count (SL) loop
            Lemma_Held_Indexed (S, SL, K);
            Lemma_No_Expired (S, SL, K);
            Ok := Ok and then Indexed (S, Held (SL, K));
         end loop;
         Check ("lemmas evaluated on the final store; held records are indexed", Ok);
      end;
   end;

   ---------------------------------------------------------------------------
   --  T18: a roster refresh, a dominated-on-arrival roster, a stale
   --  incomparable roster, a GRANT, data, Compact, open again.
   ---------------------------------------------------------------------------
   declare
      S   : Store_T (ICap, LCap);
      SL  : Lattice (Cap, Slice);
      R1  : constant Byte_Array := Founding_Roster (1, 200 * Day);
      R2  : constant Byte_Array := Founding_Roster (2, 200 * Day);
      RD  : constant Byte_Array := Founding_Roster (1, 180 * Day, 30 * Day);
      RS  : constant Byte_Array := Founding_Roster (1, 250 * Day, 9 * Day);
      PA  : constant Byte_Array := Put_Of (6, 'n', 150 * Day, 21, [1]);
      PB  : constant Byte_Array := Put_Of (7, 'n', 240 * Day, 22, [2]);
      G2  : constant Byte_Array := Founding_Grant (Author2_PK);
      PC  : constant Byte_Array := Put_Of (8, 'q', 100 * Day, 1, [3], Author2_SK, Author2_PK);
      St  : Status;
   begin
      Fresh_Store (S, SL);
      Put (S, SL, R1);
      Put (S, SL, Founding_Grant (Author_PK));
      Put (S, SL, PA);
      Put (S, SL, R2);
      Check ("roster refresh: the newer roster replaces the older; the PUT it admits stays",
             Holds (SL, Hdr (R2)) and then not Holds (SL, Hdr (R1)) and then Holds (SL, Hdr (PA))
             and then Position_Of (S, Hdr (PA)) < Position_Of (S, Hdr (R2)));
      declare
         B  : constant Store_T := S;
         BL : constant Lattice := SL;
      begin
         Put (S, SL, RD, St);
         Check ("a dominated-on-arrival roster: Dominated, nothing changed (not even del_ttl)",
                St = Dominated and then S = B and then SL = BL);
      end;
      Put (S, SL, RS, St);
      Check ("a stale incomparable roster (lower gen, higher ceiling) is held beside it",
             St = OK and then Holds (SL, Hdr (RS)) and then Holds (SL, Hdr (R2))
             and then Kome.Registers.Ceil (Regs (SL)) = 250 * Day);
      Put (S, SL, PB);
      Put (S, SL, G2);
      Put (S, SL, PC);
      Check ("rosters: Auth_Gen counts the applied authorization records (5), "
             & "not the dominated one",
             Auth_Gen (S) = 5);
      declare
         R  : Store_T (ICap, LCap);
         RL : Lattice (Cap, Slice);
      begin
         Reopen (S, R, RL, St);
         Check ("rosters: reopen before Compact: T18, Auth_Gen rebuilt (5)",
                St = OK and then T18 (S, SL, R, RL) and then Auth_Gen (R) = 5);
      end;
      Compact (S, SL);
      Check ("rosters: Compact puts the authorization records first, keeps Auth_Gen",
             Auth_First (S) and then Position_Of (S, Hdr (R2)) < Position_Of (S, Hdr (PA))
             and then Auth_Gen (S) = 5);
      declare
         R  : Store_T (ICap, LCap);
         RL : Lattice (Cap, Slice);
      begin
         Reopen (S, R, RL, St);
         Check ("rosters: reopen after Compact: T18 (every held PUT replays); "
                & "Auth_Gen is the held authorization records (4)",
                St = OK and then T18 (S, SL, R, RL) and then Holds (RL, Hdr (PA))
                and then Holds (RL, Hdr (PB)) and then Auth_Gen (R) = 4);
      end;
   end;

   ---------------------------------------------------------------------------
   --  AUDIT.md H26: Compact_Due after many overwrites of one cell, and
   --  never after Compact.
   ---------------------------------------------------------------------------
   declare
      S  : Store_T (ICap, LCap);
      SL : Lattice (Cap, Slice);
      St : Status;
      --  Overwrites of one cell: 3 held records, and the HEADER, so the log
      --  has exactly 2 * 3 + Compact_Slack entries after them.
      N  : constant := 2 * 3 + Compact_Slack - 3;
   begin
      Fresh_Store (S, SL);
      Put (S, SL, Founding_Roster (1, 100 * Day));
      Put (S, SL, Founding_Grant (Author_PK));
      for K in 1 .. N loop
         Put (S, SL, Put_Of (70, 'n', 10 * Day + U48 (K), U48 (K), [Byte (K mod 256)]));
      end loop;
      Check ("compaction duty: one entry below the bound is not due",
             Entries (S) = 3 and then Log_Entries (S) = 2 * Entries (S) + Compact_Slack
             and then not Compact_Due (S));
      Put (S, SL, Put_Of (70, 'n', 20 * Day, U48 (N + 1), [9]));
      Check ("one more dominated-away entry: Compact_Due", Compact_Due (S));
      Compact (S, SL);
      Check ("after Compact: not due, 3 APPLYs and the HEADER",
             not Compact_Due (S) and then Log_Entries (S) = 4);
      declare
         R  : Store_T (ICap, LCap);
         RL : Lattice (Cap, Slice);
      begin
         Reopen (S, R, RL, St);
         Check ("compaction duty: reopen (T18)", St = OK and then T18 (S, SL, R, RL));
      end;
   end;

   ---------------------------------------------------------------------------
   --  T18: a member revoke and a roster that drops a member.
   ---------------------------------------------------------------------------
   declare
      S   : Store_T (ICap, LCap);
      SL  : Lattice (Cap, Slice);
      R2  : constant Byte_Array :=
        Roster_Of (Root_SK, Root_PK, 0, Zero_Sig, 2, 100 * Day, TTL, Member (Author_PK, 11));
      St  : Status;
   begin
      Fresh_Store (S, SL);
      Put (S, SL, Founding_Roster (1, 100 * Day));
      Put (S, SL, Founding_Grant (Author_PK));
      Put (S, SL, Founding_Grant (Author2_PK));
      Put (S, SL, Put_Of (1, 'n', 10 * Day, 1, [1]));
      Put (S, SL, Put_Of (2, 'n', 11 * Day, 1, [2], Author2_SK, Author2_PK));
      Put (S, SL, Revoke_Of (Author2_PK, 0, 1));
      Put (S, SL, R2);
      Put (S, SL, Put_Of (3, 'n', 12 * Day, 2, [3], Author2_SK, Author2_PK));
      Check ("revoke: admission ignores REVOKE; the revoked key's records stay held",
             Kome.Frontier.Count (SL) = 7 and then Index_Is_F (S, SL));
      Compact (S, SL);
      declare
         R  : Store_T (ICap, LCap);
         RL : Lattice (Cap, Slice);
      begin
         Reopen (S, R, RL, St);
         Check ("revoke: Compact then reopen: T18", St = OK and then T18 (S, SL, R, RL));
      end;
   end;

   ---------------------------------------------------------------------------
   --  T18: a GRANT that arrives after a PUT that it admits.
   ---------------------------------------------------------------------------
   declare
      S    : Store_T (ICap, LCap);
      SL   : Lattice (Cap, Slice);
      RR2  : constant Byte_Array :=
        Roster_Of (Root2_SK, Root2_PK, Cap2, Cert2a, 1, 100 * Day, TTL, Member (Author2_PK, 31));
      Ga   : constant Byte_Array := Grant_Of (Root2_SK, Root2_PK, Cap2, Cert2a, Author2_PK);
      Gb   : constant Byte_Array := Grant_Of (Root2_SK, Root2_PK, Cap2 + 1, Cert2b, Author2_PK);
      --  A1: GRANT domination is the product order (cap, h). Gb has the
      --  larger cap. If it also has the larger h, it replaces Ga; if not,
      --  both stay, and wcap is the larger cap either way.
      Lo   : constant Boolean := Kome.Lt (Hdr (Ga).V.H, Hdr (Gb).V.H);
      GLow : constant Byte_Array := Ga;
      GHi  : constant Byte_Array := Gb;
      PG   : constant Byte_Array := Put_Of (4, 'g', 50 * Day, 1, [4], Author2_SK, Author2_PK);
      St   : Status;
   begin
      Fresh_Store (S, SL);
      Put (S, SL, RR2);
      Put (S, SL, PG, St);
      Check ("a PUT before the GRANT that admits it: Inadmissible", St = Inadmissible);
      Put (S, SL, GLow);
      Put (S, SL, PG, St);
      Check ("after the GRANT the re-offered PUT is held", St = OK);
      Put (S, SL, GHi, St);
      Check ("a second GRANT of the same issuer and subject, with a larger cap and h, replaces the first after the PUT; with a smaller h both stay",
             St = OK and then Holds (SL, Hdr (GHi))
             and then (if Lo then not Holds (SL, Hdr (GLow)) else Holds (SL, Hdr (GLow)))
             and then Kome.Registers.W_Cap (Regs (SL), To_Key256 (Author2_PK)) = Cap2 + 1
             and then Position_Of (S, Hdr (PG)) < Position_Of (S, Hdr (GHi)));
      Compact (S, SL);
      Check ("Compact writes the GRANT before the PUT it admits",
             Auth_First (S) and then Position_Of (S, Hdr (GHi)) < Position_Of (S, Hdr (PG)));
      declare
         R  : Store_T (ICap, LCap);
         RL : Lattice (Cap, Slice);
      begin
         Reopen (S, R, RL, St);
         Check ("grant after put: Compact then reopen: T18, the PUT replays",
                St = OK and then T18 (S, SL, R, RL) and then Holds (RL, Hdr (PG)));
      end;
   end;

   ---------------------------------------------------------------------------
   --  A data row full of DELs (the "wedge"): expired DELs leave F, so the
   --  frontier does not stay full.
   ---------------------------------------------------------------------------
   declare
      W   : Store_T (4 + Signers_Max * Slice, LCap);
      WL  : Lattice (4, Slice);
      P8  : constant Byte_Array := Put_Of (8, 'n', 50 * Day, 9, [8]);
      St  : Status;
   begin
      WL := Empty (NS, Fnd, 4, Slice);
      Open (Root_PK, Salt_A, WL, W);
      Put (W, WL, Founding_Roster (1, 100 * Day));
      Put (W, WL, Founding_Grant (Author_PK));
      for E in Byte range 5 .. 8 loop
         Put (W, WL, Put_Of (E, 'n', 10 * Day, U48 (E), [E]));
         Put (W, WL, Del_Of (E, 20 * Day, U48 (E) + 10));
      end loop;
      Check ("wedge setup: the data row is full of DELs",
             Data_Count (WL) = 4 and then Kome.Frontier.Count (WL) = 6);
      Exp (W, WL, 30 * Day);
      Check ("expiry removes the DELs from F, not only from the index",
             Data_Count (WL) = 0 and then Index_Is_F (W, WL));
      Put (W, WL, P8, St);
      Check ("so a new PUT is held (formerly No_Space for good)", St = OK);
      Compact (W, WL);
      declare
         R  : Store_T (4 + Signers_Max * Slice, LCap);
         RL : Lattice (4, Slice);
      begin
         Reopen (W, R, RL, St);
         Check ("and a reopened replica has the same frontier and digest (T18)",
                St = OK and then T18 (W, WL, R, RL));
      end;
   end;

   --  T18 with a raised capacity (AUDIT.md A11): a log of data_cap 4 opens
   --  again with data_cap 8 and then gets more than 4 data records. Its
   --  HEADER still records 4 (no rewrite). An open at 4 refuses it where
   --  the fifth data record does not fit (No_Space, Valid_Length there),
   --  and it replays at 8, before and after Compact.
   declare
      S4  : Store_T (4 + Signers_Max * Slice, LCap);
      L4  : Lattice (4, Slice);
      S8  : Store_T (8 + Signers_Max * Slice, LCap);
      L8  : Lattice (8, Slice);
      R4  : Store_T (4 + Signers_Max * Slice, LCap);
      RL4 : Lattice (4, Slice);
      R8  : Store_T (8 + Signers_Max * Slice, LCap);
      RL8 : Lattice (8, Slice);
      VL  : Log_Size;
      St  : Status;
   begin
      L4 := Empty (NS, Fnd, 4, Slice);
      Open (Root_PK, Salt_A, L4, S4);
      Put (S4, L4, Founding_Roster (1, 100 * Day));
      Put (S4, L4, Founding_Grant (Author_PK));
      Put (S4, L4, Put_Of (30, 'n', 10 * Day, 1, [1]));
      Open_From_Log (Log_Bytes (S4), L8, S8, VL, St);
      Check ("raised capacity: reopen with data_cap 8 over a log of data_cap 4 (T18)",
             St = OK and then Logged_Cap (S8) = 4 and then T18 (S4, L4, S8, L8));
      for E in Byte range 31 .. 36 loop
         Put (S8, L8, Put_Of (E, 'n', 10 * Day, U48 (E), [E]));
      end loop;
      Check ("raised capacity: 7 data records held, the HEADER still says 4",
             Data_Count (L8) = 7 and then Logged_Cap (S8) = 4);
      Open_From_Log (Log_Bytes (S8), RL4, R4, VL, St);
      Check ("raised capacity: reopen at 4 is refused (No_Space) at the fifth data APPLY",
             St = No_Space and then VL = Entry_At (S8, 7).Off
             and then Valid (R4, RL4) and then Data_Count (RL4) = 4);
      Open_From_Log (Log_Bytes (S8), RL8, R8, VL, St);
      Check ("raised capacity: reopen at 8 (T18)", St = OK and then T18 (S8, L8, R8, RL8));
      Compact (S8, L8);
      Open_From_Log (Log_Bytes (S8), RL4, R4, VL, St);
      Check ("raised capacity: compacted, reopen at 4 is refused", St = No_Space);
      Open_From_Log (Log_Bytes (S8), RL8, R8, VL, St);
      Check ("raised capacity: compacted, reopen at 8 (T18)",
             St = OK and then T18 (S8, L8, R8, RL8));
   end;

   --  Expire lowers the horizon on a full log: No_Space, and nothing
   --  changes. If Compact has no room for the EXPIRE, it keeps the horizon
   --  in memory only, and the reopened horizon is none.
   declare
      R1   : constant Byte_Array := Founding_Roster (1, 100 * Day);
      G1   : constant Byte_Array := Founding_Grant (Author_PK);
      P1   : constant Byte_Array := Put_Of (40, 'n', 10 * Day, 1, [1]);
      Room : constant Natural :=
        Header_Len + Apply_Prefix + R1'Length + Apply_Prefix + G1'Length
        + Apply_Prefix + P1'Length + 3;
      Sm   : Store_T (ICap, Room);
      SmL  : Lattice (Cap, Slice);
      St   : Status;
   begin
      SmL := Empty (NS, Fnd, Cap, Slice);
      Open (Root_PK, Salt_A, SmL, Sm);
      Put (Sm, SmL, R1);
      Put (Sm, SmL, G1);
      Put (Sm, SmL, P1);
      Exp (Sm, SmL, 50 * Day);
      Check ("full log: a raise that removes nothing is kept in memory",
             Horizon (Sm) = Time64 (43 * Day) and then Log_Length (Sm) = Room - 3);
      declare
         B  : constant Store_T := Sm;
         BL : constant Lattice := SmL;
      begin
         Kome.Store.Expire (Sm, SmL, 20 * Day, St);
         Check ("full log: lowering the horizon is Log_Full, nothing changed",
                St = Log_Full and then Sm = B and then SmL = BL);
      end;
      Compact (Sm, SmL);
      Check ("full log: Compact has no room for EXPIRE, the horizon stays in memory",
             Horizon (Sm) = Time64 (43 * Day)
             and then Log_Entries (Sm) = Entries (Sm) + 1);
      declare
         R  : Store_T (ICap, Room);
         RL : Lattice (Cap, Slice);
      begin
         Reopen (Sm, R, RL, St);
         Check ("full log: reopen (T18), the reopened horizon is none",
                St = OK and then T18 (Sm, SmL, R, RL) and then Horizon (R) = No_Horizon);
      end;
   end;

   --  Compact, then more operations (an APPLY_EXPIRED, a lowered EXPIRE, a
   --  DEL that is held again), then open again.
   declare
      S   : Store_T (ICap, LCap);
      SL  : Lattice (Cap, Slice);
      St  : Status;
      DA  : constant Byte_Array := Del_Of (50, 20 * Day, 2);
   begin
      Fresh_Store (S, SL);
      Put (S, SL, Founding_Roster (1, 100 * Day));
      Put (S, SL, Founding_Grant (Author_PK));
      Put (S, SL, Put_Of (50, 'n', 10 * Day, 1, [1]));
      Put (S, SL, Put_Of (51, 'n', 10 * Day, 3, [1]));
      Put (S, SL, Del_Of (51, 15 * Day, 4));
      Exp (S, SL, 25 * Day);    --  horizon 18 d, removes DEL 51 (logged)
      Compact (S, SL);
      Exp (S, SL, 30 * Day);    --  horizon 23 d, nothing removed, not logged
      Put (S, SL, DA, St);      --  DEL t = 20 d <= 23 d: APPLY_EXPIRED
      Check ("after Compact: an expired DEL applied for its effect; the mark (23 d) stays",
             St = OK and then not Holds (SL, Hdr (DA)) and then Expire_Mark (S) = 23 * Day);
      declare
         R  : Store_T (ICap, LCap);
         RL : Lattice (Cap, Slice);
      begin
         Reopen (S, R, RL, St);
         Check ("reopen: the mark is max (logged horizon 18 d, APPLY_EXPIRED t 20 d) = 20 d",
                St = OK and then Expire_Mark (R) = 20 * Day and then Horizon (R) = Time64 (18 * Day));
      end;
      Exp (S, SL, 26 * Day);    --  lowered to 19 d: logged
      Put (S, SL, DA, St);      --  t = 20 d > 19 d: held now
      Check ("after a lowered horizon the DEL is held again",
             St = OK and then Holds (SL, Hdr (DA)) and then Horizon (S) = Time64 (19 * Day));
      declare
         R  : Store_T (ICap, LCap);
         RL : Lattice (Cap, Slice);
      begin
         Reopen (S, R, RL, St);
         Check ("reopen a compacted log with entries after it: T18, the last EXPIRE's horizon",
                St = OK and then T18 (S, SL, R, RL) and then Horizon (R) = Time64 (19 * Day));
      end;
      Compact (S, SL);
      declare
         R  : Store_T (ICap, LCap);
         RL : Lattice (Cap, Slice);
      begin
         Reopen (S, R, RL, St);
         Check ("compact again, reopen: T18",
                St = OK and then T18 (S, SL, R, RL) and then Horizon (R) = Horizon (S));
      end;
   end;

   if Failed then
      Set_Exit_Status (Failure);
   end if;
   end Run_All;

begin
   null;
end Test_Store;
