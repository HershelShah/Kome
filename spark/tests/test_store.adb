--  Test main for Kome.Store (DESIGN.md §7 after SIMPLIFY.md S7, S14 to
--  S17, S21; T11, T13, T18). Real signed frames from Kome.Records go
--  through the store.
--
--  The tests cover these items:
--    * the HEADER, the APPLY prefix and the SEQ entry against independent
--      vectors (vectors/store.txt, with its embedded generator);
--    * tags (S14): Make_Tag / Tag_Off / Tag_Len round trips, and every
--      held record's tag reads back its own frame (Read_Frame, Lemma_Tag);
--    * put, overwrite, a dominated re-offer and a duplicate (nothing
--      appended), refusals that change nothing (Inadmissible, No_Space,
--      Log_Full);
--    * the digests (S21): Digest_Data and Digest_Auth against a digest
--      recomputed from the rows, and against Kome.Digest.State_Of (F)
--      (Lemma_Digest_Split), after puts, an expiry and a compaction;
--    * automatic expiry (S7): a ROSTER that raises Max_Ceil expires the
--      DELs at or below the new horizon in the same call; a DEL that
--      arrives expired drops what it dominates and is not held, or is a
--      no-op when it drops nothing; and the replay of both;
--    * seq_self (S16): from own APPLY entries (also a peer frame signed by
--      the device key), and after Compact from the SEQ entry when the
--      record with the largest own seq is no longer held;
--    * Compact: Busy while Pinned, the layout (HEADER, authorization rows
--      first, frames byte for byte, SEQ), not due afterwards, and the
--      replay of the compacted log;
--    * replay (T18): the reopened pair holds the same records, the same
--      digests and seq_self, and its log is the input; every APPLY frame
--      of a written log is a verified frame (Trusted_Frame); a corrupt,
--      torn or foreign log is refused with the right Valid_Length (H23);
--      a duplicated APPLY replays as OK; a smaller data capacity gives
--      No_Space; Compact_Due (H26).
--  The build uses -gnata, so the tests also execute every Pre / Post (Valid
--  included) and every ghost lemma on these stores.
pragma Ada_2022;
with Ada.Text_IO;      use Ada.Text_IO;
with Ada.Command_Line; use Ada.Command_Line;
with Ada.Directories;
with Ada.Exceptions;   use Ada.Exceptions;
with Kome;             use Kome;
with Kome.Headers;     use Kome.Headers;
with Kome.Frontier;    use Kome.Frontier;
with Kome.Keys;        use Kome.Keys;
with Kome.Crypto;
with Kome.Records;     use Kome.Records;
with Kome.Accumulator;
with Kome.Digest;
with Kome.Store;       use Kome.Store;

procedure Test_Store with SPARK_Mode => Off is

   use type Kome.Accumulator.Acc;
   use type Kome.Digest.Digest_State;

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

   --  A reduced X25519 encoding that is not low order (E5).
   function Good_DH (Seed : Natural) return Pubkey is
      K : Pubkey := Pubkey (Fill (Pubkey_Len, Seed));
   begin
      K (31) := K (31) and 16#3F#;
      return K;
   end Good_DH;

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

   Day : constant U48 := 86_400_000;
   TTL : constant U48 := Del_TTL_Min;   --  7 days

   Root_SK, Author_SK, Author2_SK, Stranger_SK : Kome.Crypto.Secret_Key;
   Root_PK, Author_PK, Author2_PK, Stranger_PK : Pubkey;
   Salt_A : constant Salt := Salt (Fill (Salt_Len, 90));
   Cid_A  : Hash256;
   Cert_R : Sig;    --  the founding key's certificate of itself (S3)
   Fnd    : Key256;

   ---------------------------------------------------------------------------
   --  Frames.
   ---------------------------------------------------------------------------

   function Member (PK : Pubkey; Seed : Natural) return Byte_Array is
     (PK & Good_DH (Seed) & Fill (Nonce_Len, Seed + 1) & Fill (Box_Len, Seed + 2));

   function Roster_Of (Gen, Ceil : U48) return Byte_Array is
      R : Roster_Record :=
        Make_Roster (Cid_A, Root_PK, Founding_Cap, Cert_R, Good_DH (77), Gen, Ceil,
                     Member (Author_PK, 11) & Member (Author2_PK, 21));
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

   function Put_Of (Ent : Byte; Field : Character; T, Seq : U48) return Byte_Array is
     (Put_Of (Ent, Field, T, Seq, Fill (3, Natural (Seq)), Author_SK, Author_PK));

   function Del_Of
     (Ent : Byte; T, Seq : U48; SK : Kome.Crypto.Secret_Key; PK : Pubkey) return Byte_Array
   is
      R : Del_Record := Make_Del (Cid_A, Ent_B (Ent), T, Seq, PK);
   begin
      Sign (Cid_A, R, SK);
      return Encode (R);
   end Del_Of;

   function Del_Of (Ent : Byte; T, Seq : U48) return Byte_Array is
     (Del_Of (Ent, T, Seq, Author_SK, Author_PK));

   function Hdr (F : Byte_Array) return Header is (Header_Of (Cid_A, F));

   ---------------------------------------------------------------------------
   --  Operations and comparisons.
   ---------------------------------------------------------------------------

   procedure Put
     (S : in out Store_T; L : in out Lattice; F : Byte_Array; Off : out Log_Size;
      St : out Status) is
   begin
      if not Verified (Cid (S), Root_Key (S), F) then
         raise Program_Error with "test frame not well-formed";
      end if;
      Put_Frame (S, L, F, Header_Of (Cid (S), F), Off, St);
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

   --  The digest of the data row and of the authorization rows, from the
   --  rows (Kome.Digest.Digest_Of), independent of the store's states.
   function Data_Digest (L : Lattice) return Kome.Digest.Digest_State is
     (Kome.Digest.Digest_Of
        (Kome.Digest.Hash_Array'
           [for I in 1 .. Data_Count (L) => Data_Held (L, I).V.H]));

   function Auth_Digest (L : Lattice) return Kome.Digest.Digest_State is
     (Kome.Digest.Digest_Of
        (Kome.Digest.Hash_Array'
           [for I in 1 .. Auth_Count (L) => Held (L, Data_Count (L) + I).V.H]));

   function Same_State (A, B : Kome.Digest.Digest_State) return Boolean is
     (Kome.Digest.Count (A) = Kome.Digest.Count (B)
      and then Kome.Digest.Sum (A) = Kome.Digest.Sum (B));

   --  The two store digests are the digests of the rows, and together the
   --  digest of F (S21).
   function Digests_Match (S : Store_T; L : Lattice) return Boolean is
   begin
      Lemma_Digest_Split (S, L);
      return Same_State (Digest_Data (S), Data_Digest (L))
        and then Same_State (Digest_Auth (S), Auth_Digest (L))
        and then Kome.Digest.Count (Digest_Data (S)) + Kome.Digest.Count (Digest_Auth (S))
                 = Kome.Digest.Count (Kome.Digest.State_Of (L))
        and then Kome.Accumulator.Add (Kome.Digest.Sum (Digest_Data (S)),
                                       Kome.Digest.Sum (Digest_Auth (S)))
                 = Kome.Digest.Sum (Kome.Digest.State_Of (L));
   end Digests_Match;

   --  S14: every held record's tag reads back a frame whose header is the
   --  record.
   function Tags_Read_Back (S : Store_T; L : Lattice) return Boolean is
   begin
      for I in 1 .. Cnt (L) loop
         Lemma_Tag (S, L, I);
         declare
            T : constant U64 := Tag (L, I);
         begin
            if not Has_Frame (S, Tag_Off (T))
              or else Len_At (S, Tag_Off (T)) /= Tag_Len (T)
              or else Header_Of (Cid (S), Read_Frame (S, Tag_Off (T))) /= Held (L, I)
            then
               return False;
            end if;
         end;
      end loop;
      return True;
   end Tags_Read_Back;

   function Same_Set (A, B : Lattice) return Boolean is
     (Cnt (A) = Cnt (B)
      and then (for all I in 1 .. Cnt (A) => Holds (B, Held (A, I)))
      and then (for all I in 1 .. Cnt (B) => Holds (A, Held (B, I))));

   --  The entries of a log after its HEADER, as the test reads the file:
   --  each APPLY frame is a verified frame of the collection (the replay
   --  assumption Trusted_Frame, S15), and the scan ends at the length.
   --  Applies and Seqs count the entries.
   procedure Scan
     (Log : Byte_Array; Good : out Boolean; Applies, Seqs : out Natural)
   is
      P : Natural := Header_Len;
   begin
      Good := True;
      Applies := 0;
      Seqs := 0;
      while P < Log'Length loop
         if Log (P) = Op_Apply and then Log'Length - P >= Apply_Prefix then
            declare
               L : constant Natural := U24_Of (Log (P + 1), Log (P + 2), Log (P + 3));
            begin
               if L = 0 or else Log'Length - P - Apply_Prefix < L
                 or else not Verified (Cid_A, Root_PK, Log (P + 4 .. P + 3 + L))
               then
                  Good := False;
                  return;
               end if;
               Applies := Applies + 1;
               P := P + Apply_Prefix + L;
            end;
         elsif Log (P) = Op_Seq and then Log'Length - P >= Seq_Len then
            Seqs := Seqs + 1;
            P := P + Seq_Len;
         else
            Good := False;
            return;
         end if;
      end loop;
   end Scan;

   --  T18: the reopened pair has the same held records, digests,
   --  seq_self and log.
   function T18 (S : Store_T; L : Lattice; R : Store_T; RL : Lattice) return Boolean is
     (Same_Set (L, RL)
      and then Max_Ceil (L) = Max_Ceil (RL)
      and then Same_State (Digest_Data (S), Digest_Data (R))
      and then Same_State (Digest_Auth (S), Digest_Auth (R))
      and then Seq_Self (S) = Seq_Self (R)
      and then Log_Bytes (S) = Log_Bytes (R)
      and then Cid (R) = Cid (S)
      and then Del_TTL (R) = Del_TTL (S));

   Log_Cap_A : constant := 64 * 1024;

   procedure Fresh_Store (S : out Store_T; L : out Lattice) is
   begin
      L := Empty (Fnd, L.Cap);
      Open (Root_PK, Salt_A, TTL, Author_PK, L, S);
   end Fresh_Store;

   procedure Reopen
     (S : Store_T; R : out Store_T; RL : out Lattice; St : out Status)
   is
      VL : Log_Size;
   begin
      Open_From_Log (Log_Bytes (S), Author_PK, RL, R, VL, St);
      if St = OK and then VL /= Log_Length (S) then
         raise Program_Error with "Valid_Length is not the input length on OK";
      end if;
   end Reopen;

   procedure Compact (S : in out Store_T; L : in out Lattice; St : out Status) is
      Buf : Byte_Array (0 .. S.Log_Cap) := [others => 16#EE#];
   begin
      Kome.Store.Compact (S, L, Buf, St);
      if St = OK and then Buf (0 .. Log_Length (S) - 1) /= Log_Bytes (S) then
         raise Program_Error with "Buf is not the image of the compacted log";
      end if;
   end Compact;

   --  A State holds Signers_Max * Slice_Max authorization entries, and under
   --  -gnata each evaluation of a Post copies states and stores, so the
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
   Kome.Crypto.Key_Pair (Seed_Of (5), Author2_SK, Author2_PK);
   Cid_A := Cid_Of (Root_PK, Salt_A, TTL);
   Fnd := To_Key256 (Root_PK);
   Cert_R := Make_Cert (Root_SK, Cid_A, Root_PK, Founding_Cap);

   ---------------------------------------------------------------------------
   --  Known-answer vectors: the HEADER, the APPLY prefix, the SEQ entry.
   ---------------------------------------------------------------------------
   declare
      File    : File_Type;
      Headers : Natural := 0;
      Applies : Natural := 0;
      Seqs    : Natural := 0;
      All_Good : Boolean := True;
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
            if Line'Length >= 7 and then Line (Line'First .. Line'First + 6) = "header " then
               declare
                  RP  : constant Pubkey  := Pubkey (Hex (Field (2)));
                  SL  : constant Salt    := Salt (Hex (Field (3)));
                  DT  : constant U48     := U48'Value (Field (4));
                  CI  : constant Hash256 := Hash256 (Hex (Field (5)));
                  HB  : constant Byte_Array := Hex (Field (6));
                  L   : Lattice (4);
                  S   : Store_T (256);
               begin
                  L := Empty (To_Key256 (RP), 4);
                  Open (RP, SL, DT, Author_PK, L, S);
                  All_Good := All_Good and then Log_Bytes (S) = HB and then Cid (S) = CI
                        and then Cid_Of (RP, SL, DT) = CI and then Del_TTL (S) = DT
                        and then Header_Well_Formed (HB);
                  Headers := Headers + 1;
               end;
            elsif Line'Length >= 6 and then Line (Line'First .. Line'First + 5) = "apply " then
               declare
                  N  : constant Natural := Natural'Value (Field (2));
                  PB : constant Byte_Array := Hex (Field (3));
               begin
                  All_Good := All_Good and then PB'Length = Apply_Prefix
                        and then PB (0) = Op_Apply
                        and then PB (1) = Byte_Of_U24 (N, 0)
                        and then PB (2) = Byte_Of_U24 (N, 1)
                        and then PB (3) = Byte_Of_U24 (N, 2)
                        and then U24_Of (PB (1), PB (2), PB (3)) = N;
                  Applies := Applies + 1;
               end;
            elsif Line'Length >= 4 and then Line (Line'First .. Line'First + 3) = "seq " then
               declare
                  V  : constant U48 := U48'Value (Field (2));
                  SB : constant Byte_Array := Hex (Field (3));
                  L  : Lattice (4);
                  S  : Store_T (256);
                  R  : Store_T (256);
                  RL : Lattice (4);
                  VL : Log_Size;
                  St : Status;
               begin
                  --  A log that is a HEADER and this SEQ entry reopens with
                  --  seq_self = V, and its log is the input (S16).
                  L := Empty (Fnd, 4);
                  Open (Root_PK, Salt_A, TTL, Author_PK, L, S);
                  Open_From_Log (Log_Bytes (S) & SB, Author_PK, RL, R, VL, St);
                  All_Good := All_Good and then SB'Length = Seq_Len and then St = OK
                        and then Seq_Self (R) = V and then Log_Entries (R) = 1
                        and then Log_Bytes (R) = Log_Bytes (S) & SB;
                  Seqs := Seqs + 1;
               end;
            end if;
         end;
      end loop;
      Close (File);
      Check ("vectors: HEADER (59 bytes) and cid, APPLY prefix, SEQ entry",
             All_Good and then Headers = 3 and then Applies = 6 and then Seqs = 5);
   end;

   ---------------------------------------------------------------------------
   --  Tags (S14).
   ---------------------------------------------------------------------------
   Check ("tags: Make_Tag / Tag_Off / Tag_Len round trip",
          Tag_Off (Make_Tag (0, 1)) = 0 and then Tag_Len (Make_Tag (0, 1)) = 1
          and then Tag_Off (Make_Tag (Log_Max, Kome.Records.Frame_Max)) = Log_Max
          and then Tag_Len (Make_Tag (Log_Max, Kome.Records.Frame_Max)) = Kome.Records.Frame_Max
          and then Tag_Off (Make_Tag (123_456, 125)) = 123_456
          and then Make_Tag (2, 3) = 2 * 2**24 + 3);
   Lemma_Tag_Round_Trip (Log_Max, Kome.Records.Frame_Max);
   Lemma_U24_Round_Trip (2**24 - 1);
   Lemma_U24_Bytes_Round_Trip (16#AB#, 16#CD#, 16#EF#);

   ---------------------------------------------------------------------------
   --  Put, overwrite, duplicates, refusals; digests and tags.
   ---------------------------------------------------------------------------
   declare
      L   : Lattice (32);
      S   : Store_T (Log_Cap_A);
      St  : Status;
      Off : Log_Size;
      LL  : Log_Size;
      P1  : constant Byte_Array := Put_Of (1, 'a', 2 * Day, 1);
      P2  : constant Byte_Array := Put_Of (1, 'a', 3 * Day, 2);
   begin
      Fresh_Store (S, L);
      Check ("open: HEADER only, no entries, empty digests",
             Log_Length (S) = Header_Len and then Log_Entries (S) = 0
             and then Seq_Self (S) = 0 and then Pinned (S) = 0
             and then Kome.Digest.Count (Digest_Data (S)) = 0
             and then Kome.Digest.Count (Digest_Auth (S)) = 0
             and then Digests_Match (S, L));
      Put (S, L, Roster_Of (1, 30 * Day), Off, St);
      Check ("roster: OK at the HEADER's end, Max_Ceil", St = OK and then Off = Header_Len
             and then Max_Ceil (L) = 30 * Day
             and then Tag_Of (L, Hdr (Roster_Of (1, 30 * Day)))
                      = Make_Tag (Header_Len, Roster_Of (1, 30 * Day)'Length));
      Put (S, L, Grant_Of (Author_PK));
      Put (S, L, Grant_Of (Author2_PK));
      Check ("authorization digests", Digests_Match (S, L) and then Auth_Count (L) = 3);
      Put (S, L, P1, Off, St);
      Check ("put: OK, held, its tag is its APPLY entry",
             St = OK and then Holds (L, Hdr (P1))
             and then Tag_Off (Tag_Of (L, Hdr (P1))) = Off
             and then Read_Frame (S, Off) = P1
             and then Log_Byte (S, Off) = Op_Apply);
      Put (S, L, Put_Of (1, 'b', 2 * Day, 3));
      Put (S, L, Put_Of (2, 'a', 2 * Day, 4));
      Put (S, L, P2, Off, St);
      Check ("overwrite: the newer PUT replaces the older",
             St = OK and then Holds (L, Hdr (P2)) and then not Holds (L, Hdr (P1)));
      Check ("data digests after an overwrite", Digests_Match (S, L));
      Check ("tags read back their frames", Tags_Read_Back (S, L));
      LL := Log_Length (S);
      Put (S, L, P1, St);
      Check ("dominated re-offer: Dominated, nothing appended",
             St = Dominated and then Log_Length (S) = LL);
      Put (S, L, P2, St);
      Check ("duplicate: OK, nothing appended", St = OK and then Log_Length (S) = LL);
      Put (S, L, Put_Of (3, 'a', 2 * Day, 1, [1], Stranger_SK, Stranger_PK), St);
      Check ("a non-writer: Inadmissible, nothing appended",
             St = Inadmissible and then Log_Length (S) = LL);
      Put (S, L, Put_Of (3, 'a', 31 * Day, 9), St);
      Check ("above the ceiling: Inadmissible", St = Inadmissible and then Log_Length (S) = LL);
      Check ("seq_self: the largest own seq of the APPLY entries", Seq_Self (S) = 4);
      Put (S, L, Put_Of (4, 'a', 2 * Day, 9, [7], Author2_SK, Author2_PK));
      Check ("seq_self: another author's seq does not count", Seq_Self (S) = 4);
      --  A frame signed by the device key that arrives from a peer (a
      --  clone or a restored device) also raises seq_self (S16).
      Put (S, L, Put_Of (5, 'a', 2 * Day, 11));
      Check ("seq_self: an own frame from a peer counts", Seq_Self (S) = 11);
      Check ("digests and tags after the puts",
             Digests_Match (S, L) and then Tags_Read_Back (S, L));
   end;

   --  The data row is full: No_Space, nothing changes.
   declare
      L  : Lattice (2);
      S  : Store_T (Log_Cap_A);
      St : Status;
      LL : Log_Size;
   begin
      Fresh_Store (S, L);
      Put (S, L, Roster_Of (1, 30 * Day));
      Put (S, L, Grant_Of (Author_PK));
      Put (S, L, Put_Of (1, 'a', 2 * Day, 1));
      Put (S, L, Put_Of (2, 'a', 2 * Day, 2));
      LL := Log_Length (S);
      Put (S, L, Put_Of (3, 'a', 2 * Day, 3), St);
      Check ("full data row: No_Space, nothing appended",
             St = No_Space and then Log_Length (S) = LL and then Data_Count (L) = 2);
      Put (S, L, Put_Of (1, 'a', 3 * Day, 4), St);
      Check ("full data row: an overwrite frees its own room, OK",
             St = OK and then Data_Count (L) = 2);
   end;

   --  The log is full: Log_Full, nothing changes.
   declare
      L  : Lattice (8);
      S  : Store_T (Header_Len + 212 + 2 * 136 + 4 + 199 + 4 + 150);
      St : Status;
      LL : Log_Size;
   begin
      Fresh_Store (S, L);
      Put (S, L, Roster_Of (1, 30 * Day));
      Put (S, L, Grant_Of (Author_PK));
      Put (S, L, Put_Of (1, 'a', 2 * Day, 1));
      LL := Log_Length (S);
      Put (S, L, Put_Of (2, 'a', 2 * Day, 2), St);
      Check ("full log: Log_Full, nothing appended",
             St = Log_Full and then Log_Length (S) = LL and then Data_Count (L) = 1);
      Put (S, L, Put_Of (1, 'a', 1 * Day, 3), St);
      Check ("full log: a dominated record is Dominated, not Log_Full", St = Dominated);
   end;

   ---------------------------------------------------------------------------
   --  Automatic expiry (S7) and its replay.
   ---------------------------------------------------------------------------
   declare
      L   : Lattice (32);
      S   : Store_T (Log_Cap_A);
      R   : Store_T (Log_Cap_A);
      RL  : Lattice (32);
      St  : Status;
      LL  : Log_Size;
      D1  : constant Byte_Array := Del_Of (3, 25 * Day, 3);   --  above hz = 23 days
      D0  : constant Byte_Array := Del_Of (4, 22 * Day, 5);   --  at or below hz
      DN  : constant Byte_Array := Del_Of (6, 21 * Day, 6);   --  below hz, drops nothing
      P4  : constant Byte_Array := Put_Of (4, 'a', 20 * Day, 4);
      P5  : constant Byte_Array := Put_Of (5, 'a', 26 * Day, 7);
   begin
      Fresh_Store (S, L);
      Put (S, L, Roster_Of (1, 30 * Day));
      Put (S, L, Grant_Of (Author_PK));
      Put (S, L, Put_Of (3, 'a', 24 * Day, 1));
      Put (S, L, D1);
      Put (S, L, P4);
      Put (S, L, P5);
      Check ("expiry setup: hz = maxceil - del_ttl = 23 days",
             Has_Hz (L, TTL) and then Hz (L, TTL) = 23 * Day
             and then Holds (L, Hdr (D1)) and then Holds (L, Hdr (P4))
             and then not Expired_In (Hdr (D1), L, TTL)
             and then Expired_In (Hdr (D0), L, TTL));
      Put (S, L, D0, St);
      Check ("a DEL that arrives expired drops what it dominates and is not held",
             St = OK and then not Holds (L, Hdr (D0)) and then not Holds (L, Hdr (P4))
             and then Holds (L, Hdr (D1)));
      LL := Log_Length (S);
      Put (S, L, DN, St);
      Check ("an expired DEL that drops nothing: OK, nothing appended",
             St = OK and then Log_Length (S) = LL and then not Holds (L, Hdr (DN)));
      Check ("digests after an expired arrival", Digests_Match (S, L));
      --  A ROSTER that raises Max_Ceil to 40 days: hz = 33 days, and the
      --  DEL at 25 days expires in the same call.
      Put (S, L, Roster_Of (2, 40 * Day), St);
      Check ("a ceiling raise expires the DELs at or below the new horizon",
             St = OK and then Max_Ceil (L) = 40 * Day and then Hz (L, TTL) = 33 * Day
             and then not Holds (L, Hdr (D1)) and then Holds (L, Hdr (P5))
             and then not Holds (L, Hdr (Roster_Of (1, 30 * Day))));
      Check ("digests and tags after the expiry",
             Digests_Match (S, L) and then Tags_Read_Back (S, L));
      for I in 1 .. Cnt (L) loop
         Lemma_No_Expired (S, L, I);
      end loop;
      Reopen (S, R, RL, St);
      Check ("replay reproduces the expiry (T18)", St = OK and then T18 (S, L, R, RL));
      Check ("replayed digests and tags",
             Digests_Match (R, RL) and then Tags_Read_Back (R, RL));
      declare
         Good : Boolean;
         A, Q : Natural;
      begin
         Scan (Log_Bytes (S), Good, A, Q);
         Check ("every APPLY frame of the log is a verified frame (Trusted_Frame)",
                Good and then A = Log_Entries (S) and then Q = 0);
      end;
   end;

   ---------------------------------------------------------------------------
   --  Compact, Pinned, seq_self from SEQ (S14, S16, S21).
   ---------------------------------------------------------------------------
   declare
      L   : Lattice (32);
      S   : Store_T (Log_Cap_A);
      R   : Store_T (Log_Cap_A);
      RL  : Lattice (32);
      St  : Status;
      Old : Byte_Array (0 .. Log_Cap_A);
      OL  : Log_Size;
      Own : constant Byte_Array := Put_Of (1, 'a', 2 * Day, 7);
   begin
      Fresh_Store (S, L);
      Put (S, L, Roster_Of (1, 30 * Day));
      Put (S, L, Grant_Of (Author_PK));
      Put (S, L, Put_Of (2, 'a', 2 * Day, 1));
      Put (S, L, Grant_Of (Author2_PK));
      Put (S, L, Put_Of (3, 'b', 2 * Day, 2));
      Put (S, L, Own);
      --  Another author overwrites the record with the largest own seq.
      Put (S, L, Put_Of (1, 'a', 3 * Day, 1, [9], Author2_SK, Author2_PK));
      Put (S, L, Put_Of (3, 'b', 3 * Day, 3));
      Check ("compact setup: seq_self 7, the own seq-7 record is not held",
             Seq_Self (S) = 7 and then not Holds (L, Hdr (Own)));
      Reopen (S, R, RL, St);
      Check ("replay recovers seq_self from the APPLY entries",
             St = OK and then Seq_Self (R) = 7 and then T18 (S, L, R, RL));
      Pin (S, L);
      OL := Log_Length (S);
      Old (0 .. OL - 1) := Log_Bytes (S);
      Compact (S, L, St);
      Check ("Compact while Pinned: Busy, nothing changes",
             St = Busy and then Log_Length (S) = OL and then Log_Bytes (S) = Old (0 .. OL - 1));
      Unpin (S, L);
      Check ("Unpin", Pinned (S) = 0);
      Compact (S, L, St);
      Check ("Compact: OK, one APPLY per held record and a SEQ",
             St = OK and then Log_Entries (S) = Cnt (L) + 1
             and then not Compact_Due (S, L)
             and then Log_Bytes (S) (0 .. Header_Len - 1) = Old (0 .. Header_Len - 1)
             and then Log_Byte (S, Log_Length (S) - Seq_Len) = Op_Seq
             and then Code_At (S, Log_Length (S) - Seq_Len + 1) = 7
             and then Log_Length (S) < OL);
      Check ("Compact: the authorization rows come first",
             Auth_Count (L) = 3
             and then Tag_Off (Tag (L, Data_Count (L) + 1)) = Header_Len
             and then (for all I in 1 .. Data_Count (L) =>
                         Tag_Off (Tag (L, I)) > Tag_Off (Tag (L, Data_Count (L) + 3))));
      Check ("Compact: tags and digests", Tags_Read_Back (S, L) and then Digests_Match (S, L));
      Reopen (S, R, RL, St);
      Check ("replay of the compacted log: seq_self from the SEQ entry",
             St = OK and then Seq_Self (R) = 7 and then T18 (S, L, R, RL));
      declare
         Good : Boolean;
         A, Q : Natural;
      begin
         Scan (Log_Bytes (S), Good, A, Q);
         Check ("the compacted log scans: Count APPLYs and one SEQ",
                Good and then A = Cnt (L) and then Q = 1);
      end;
   end;

   ---------------------------------------------------------------------------
   --  Replay refusals (H23), duplicates, capacity, Compact_Due (H26).
   ---------------------------------------------------------------------------
   declare
      L   : Lattice (32);
      S   : Store_T (Log_Cap_A);
      R   : Store_T (Log_Cap_A);
      RL  : Lattice (32);
      St  : Status;
      VL  : Log_Size;
      LB  : Byte_Array (0 .. Log_Cap_A);
      N   : Log_Size;
      E1  : Log_Size;   --  the offset of the second APPLY entry
   begin
      Fresh_Store (S, L);
      Put (S, L, Roster_Of (1, 30 * Day));
      E1 := Log_Length (S);
      Put (S, L, Grant_Of (Author_PK));
      Put (S, L, Put_Of (1, 'a', 2 * Day, 1));
      N := Log_Length (S);
      LB (0 .. N - 1) := Log_Bytes (S);

      --  A torn tail: the last entry is cut.
      Open_From_Log (LB (0 .. N - 2), Author_PK, RL, R, VL, St);
      Check ("torn tail: Malformed, Valid_Length = the start of the torn entry",
             St = Malformed and then VL = N - (Apply_Prefix + Put_Of (1, 'a', 2 * Day, 1)'Length)
             and then Cnt (RL) = 2);
      --  A corrupt frame byte in the second entry.
      declare
         C : Byte_Array := LB (0 .. N - 1);
      begin
         C (E1 + Apply_Prefix + Grant_O_Subject + 5) :=
           C (E1 + Apply_Prefix + Grant_O_Subject + 5) xor 1;
         Open_From_Log (C, Author_PK, RL, R, VL, St);
         --  Replay does not verify signatures (S15, Trusted_Frame): the
         --  corrupt GRANT replays as a GRANT to another key, so the PUT
         --  after it is Inadmissible and refused.
         Check ("a corrupt entry: the first refused entry ends the replay",
                St = Malformed
                and then VL = N - (Apply_Prefix + Put_Of (1, 'a', 2 * Day, 1)'Length)
                and then Cnt (RL) = 2);
      end;
      --  An unknown op.
      Open_From_Log (LB (0 .. N - 1) & Byte_Array'[16#07#], Author_PK, RL, R, VL, St);
      Check ("an unknown op: Malformed, Valid_Length = the whole valid log",
             St = Malformed and then VL = N);
      --  A bad HEADER.
      declare
         C : Byte_Array := LB (0 .. N - 1);
      begin
         C (0) := 16#4C#;
         Open_From_Log (C, Author_PK, RL, R, VL, St);
         Check ("a bad magic: Malformed, Valid_Length 0", St = Malformed and then VL = 0);
         C := LB (0 .. N - 1);
         C (HO_TTL + 5) := 0;
         C (HO_TTL + 4) := 0;
         C (HO_TTL + 3) := 0;
         Open_From_Log (C, Author_PK, RL, R, VL, St);
         Check ("a del_ttl out of range: Malformed", St = Malformed and then VL = 0);
      end;
      --  A log that does not fit.
      declare
         Small  : Store_T (N - 1);
         SmallL : Lattice (32);
      begin
         Open_From_Log (LB (0 .. N - 1), Author_PK, SmallL, Small, VL, St);
         Check ("a log larger than Log_Cap: No_Space", St = No_Space and then VL = 0);
      end;
      --  A smaller data capacity than the log needs.
      declare
         Tiny  : Store_T (Log_Cap_A);
         TinyL : Lattice (0);
      begin
         Open_From_Log (LB (0 .. N - 1), Author_PK, TinyL, Tiny, VL, St);
         Check ("a smaller data capacity: No_Space at the first data entry",
                St = No_Space and then VL = N - (Apply_Prefix + Put_Of (1, 'a', 2 * Day, 1)'Length));
      end;
      --  A duplicated APPLY (a retried append) replays as OK and stays.
      declare
         Dup : constant Byte_Array :=
           LB (0 .. N - 1) & Byte_Array'(Op_Apply, Byte_Of_U24 (Grant_Of (Author_PK)'Length, 0),
                                         Byte_Of_U24 (Grant_Of (Author_PK)'Length, 1),
                                         Byte_Of_U24 (Grant_Of (Author_PK)'Length, 2))
           & Grant_Of (Author_PK);
      begin
         Open_From_Log (Dup, Author_PK, RL, R, VL, St);
         Check ("a duplicated APPLY replays as OK and stays in the log",
                St = OK and then VL = Dup'Length and then Log_Bytes (R) = Dup
                and then Same_Set (L, RL) and then Log_Entries (R) = 4);
      end;
      --  A HEADER only.
      Open_From_Log (LB (0 .. Header_Len - 1), Author_PK, RL, R, VL, St);
      Check ("a HEADER only opens", St = OK and then VL = Header_Len and then Cnt (RL) = 0);
      --  Compact_Due: overwrite one cell until the log has more than
      --  2 * |F| + Compact_Slack entries.
      for I in 1 .. 2 * 4 + Compact_Slack loop
         Put (S, L, Put_Of (1, 'a', 2 * Day + U48 (I), U48 (I + 1)));
      end loop;
      Check ("Compact_Due after many overwrites", Compact_Due (S, L));
      Compact (S, L, St);
      Check ("not due after Compact", St = OK and then not Compact_Due (S, L)
             and then Digests_Match (S, L));
   end;

   if Failed then
      Set_Exit_Status (Failure);
   end if;
   end Run_All;

begin
   null;
end Test_Store;
