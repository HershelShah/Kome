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
--      No_Space; Compact_Due (H26);
--    * the ceiling cell (AUDIT.md H12, T19; procedure Ceiling_Cell): the
--      audit scenario in both arrival orders (the roster that finds no
--      room is captured, Ceil_Only; with room it is held) with the same
--      Max_Ceil, the same horizon and the same data row; two more
--      deliveries; reopen (T18 with a cell); Compact (the CEIL entry
--      first) and reopen; re-offers; a dead cell; the cell's record
--      entering its slice; Log_Full; the replay refusals and duplicates
--      of a CEIL; Put_Ceil with room (the roster never enters a row);
--      Log_Fits; the CEIL prefix against vectors/store.txt.
--      The scenario runs in two forms. "full slot table": 15 certified
--      roots take the slots, so the roster of a 16th root finds none (17
--      signers with the founding key). "full slice": the audit's own
--      case, 512 REVOKEs of one root. Under -gnata each Put_Frame
--      evaluates the digest models with the ghost big-integer arithmetic
--      of Kome.Accumulator, and its time grows with the square of the
--      number of held records (about 3 s at 20 records), so the 512-record
--      form runs only in the release mode (MODE=release), where no
--      contract executes; the check mode runs the slot-table form, which
--      takes the same paths of Put_Frame, Put_Ceil, replay and Compact.
--  The build uses -gnata, so the tests also execute every Pre / Post (Valid
--  included) and every ghost lemma on these stores.
pragma Ada_2022;
with Ada.Text_IO;      use Ada.Text_IO;
with Ada.Command_Line; use Ada.Command_Line;
with Ada.Directories;
with Ada.Exceptions;   use Ada.Exceptions;
with Ada.Assertions;
with Ada.Strings.Fixed;
with Contract_Mode;    use Contract_Mode;
with Kome;             use Kome;
with Kome.Headers;     use Kome.Headers;
with Kome.Frontier;    use Kome.Frontier;
with Kome.Keys;        use Kome.Keys;
with Kome.Crypto;
with Kome.Records;     use Kome.Records;
with Kome.Accumulator;
with Kome.Digest;
with Kome.Store;       use Kome.Store;
with Kome.Views;

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

   --  A roster and a REVOKE of any signer (a certified root with its
   --  certificate), for the ceiling-cell tests.
   function Roster_By
     (SK : Kome.Crypto.Secret_Key; PK : Pubkey; Cap : U48; Cert : Sig; Gen, Ceil : U48;
      Members : Byte_Array) return Byte_Array
   is
      R : Roster_Record := Make_Roster (Cid_A, PK, Cap, Cert, Good_DH (77), Gen, Ceil, Members);
   begin
      Sign (Cid_A, R, SK);
      return Encode (R);
   end Roster_By;

   function Revoke_By
     (SK : Kome.Crypto.Secret_Key; PK : Pubkey; Cap : U48; Cert : Sig; Subject : Pubkey)
      return Byte_Array
   is
      X : Revoke_Record := Make_Revoke (Cid_A, PK, Cap, Cert, Subject, 0);
   begin
      Sign (Cid_A, X, SK);
      return Encode (X);
   end Revoke_By;

   --  The I-th key pair of a family (the seed holds I in two bytes, so the
   --  keys of one family are distinct).
   procedure Key_Of_Index
     (Family : Byte; I : Natural; SK : out Kome.Crypto.Secret_Key; PK : out Pubkey)
   is
      Sd : Byte_Array := Fill (Kome.Crypto.Seed_Len, 77);
   begin
      Sd (0) := Byte (I mod 256);
      Sd (1) := Byte (I / 256);
      Sd (2) := Family;
      Kome.Crypto.Key_Pair (Kome.Crypto.Seed (Sd), SK, PK);
   end Key_Of_Index;

   --  A log entry: op ‖ len:u24 ‖ frame.
   function Entry_Of (Op : Byte; F : Byte_Array) return Byte_Array is
     (Byte_Array'(Op, Byte_Of_U24 (F'Length, 0), Byte_Of_U24 (F'Length, 1),
                  Byte_Of_U24 (F'Length, 2)) & F);

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

   --  Put_Ceil of a ROSTER frame (the ceiling frame of a HELLO).
   procedure Ceil
     (S : in out Store_T; L : in out Lattice; F : Byte_Array; Off : out Log_Size;
      St : out Status) is
   begin
      if not Verified (Cid (S), Root_Key (S), F) then
         raise Program_Error with "test frame not well-formed";
      end if;
      Put_Ceil (S, L, F, Header_Of (Cid (S), F), Off, St);
   end Ceil;

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
   --  record, from an APPLY entry; and the tag of the ceiling cell's record
   --  reads back its frame from a CEIL entry (AUDIT.md H12).
   function Tags_Read_Back (S : Store_T; L : Lattice) return Boolean is
   begin
      if Has_Ceil (L) then
         Lemma_Ceil_Tag (S, L);
         declare
            T : constant U64 := Ceil_Tag (L);
         begin
            if not Has_Frame (S, Tag_Off (T))
              or else Log_Byte (S, Tag_Off (T)) /= Op_Ceil
              or else Len_At (S, Tag_Off (T)) /= Tag_Len (T)
              or else Header_Of (Cid (S), Read_Frame (S, Tag_Off (T))) /= Ceil_Held (L)
            then
               return False;
            end if;
         end;
      end if;
      for I in 1 .. Cnt (L) loop
         Lemma_Tag (S, L, I);
         declare
            T : constant U64 := Tag (L, I);
         begin
            if not Has_Frame (S, Tag_Off (T))
              or else Log_Byte (S, Tag_Off (T)) /= Op_Apply
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
   --  each APPLY and each CEIL frame is a verified frame of the collection
   --  (the replay assumption Trusted_Frame, S15), a CEIL frame is a ROSTER,
   --  and the scan ends at the length. Applies, Seqs and Ceils count the
   --  entries.
   procedure Scan
     (Log : Byte_Array; Good : out Boolean; Applies, Seqs, Ceils : out Natural)
   is
      P : Natural := Header_Len;
   begin
      Good := True;
      Applies := 0;
      Seqs := 0;
      Ceils := 0;
      while P < Log'Length loop
         if Log (P) in Op_Apply | Op_Ceil and then Log'Length - P >= Apply_Prefix then
            declare
               L : constant Natural := U24_Of (Log (P + 1), Log (P + 2), Log (P + 3));
            begin
               if L = 0 or else Log'Length - P - Apply_Prefix < L
                 or else not Verified (Cid_A, Root_PK, Log (P + 4 .. P + 3 + L))
               then
                  Good := False;
                  return;
               end if;
               if Log (P) = Op_Ceil then
                  if not Is_Roster_Frame (Log (P + 4 .. P + 3 + L)) then
                     Good := False;
                     return;
                  end if;
                  Ceils := Ceils + 1;
               else
                  Applies := Applies + 1;
               end if;
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

   --  The two states have the same ceiling cell, tag included.
   function Same_Cell (A, B : Lattice) return Boolean is
     (Has_Ceil (A) = Has_Ceil (B)
      and then (if Has_Ceil (A)
                then Ceil_Held (A) = Ceil_Held (B) and then Ceil_Tag (A) = Ceil_Tag (B)));

   --  The two data rows hold the same records.
   function Same_Data (A, B : Lattice) return Boolean is
     (Data_Count (A) = Data_Count (B)
      and then (for all I in 1 .. Data_Count (A) => Holds (B, Data_Held (A, I))));

   --  T18: the reopened pair has the same held records, the same ceiling
   --  cell, digests, seq_self and log.
   function T18 (S : Store_T; L : Lattice; R : Store_T; RL : Lattice) return Boolean is
     (Same_Set (L, RL)
      and then Same_Cell (L, RL)
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


   ---------------------------------------------------------------------------
   --  The ceiling cell (AUDIT.md H12, T19; DESIGN.md §7).
   ---------------------------------------------------------------------------

   --  The stolen root R of the audit scenario, with a long cert cap, and
   --  the numbers of the scenario: the founding roster r0 has the ceiling
   --  C0; R's roster r2 has the ceiling C2 = del_ttl + 600, so after a
   --  raise to C2 the horizon is 600: a DEL at 500 expires, a PUT at 900
   --  stays.
   RR_SK   : Kome.Crypto.Secret_Key;
   RR_PK   : Pubkey;
   Cert_RR : Sig;
   Cap_RR  : constant U48 := Del_TTL_Min + 1_000_000;
   C0      : constant U48 := 1_000;
   C2      : constant U48 := Del_TTL_Min + 600;

   function Both_Members return Byte_Array is
     (Member (Author_PK, 11) & Member (Author2_PK, 21));

   function RR_Roster (Gen, Ceil : U48; Members : Byte_Array) return Byte_Array is
     (Roster_By (RR_SK, RR_PK, Cap_RR, Cert_RR, Gen, Ceil, Members));

   --  A call that its precondition must refuse (run only when
   --  Contracts_On).
   generic
      with procedure Run;
   function Refused return Boolean;
   function Refused return Boolean is
   begin
      Run;
      return False;
   exception
      when E : Ada.Assertions.Assertion_Error =>
         if Ada.Strings.Fixed.Index
              (Exception_Message (E), "failed precondition from kome-store.ads") = 0
         then
            Put_Line ("  unexpected assertion: " & Exception_Message (E));
            return False;
         end if;
         return True;
   end Refused;

   --  How the authorization rows are filled, so that R's roster r2 finds
   --  no room: By_Slots, 15 certified roots Q1 .. Q15 each sign one REVOKE
   --  and take the slots 2 .. 16 (R is then a 17th signer, with no slot);
   --  By_Slice, R signs Slice_Max REVOKEs on distinct subjects (the audit
   --  scenario as written).
   type Fill_Kind is (By_Slots, By_Slice);

   procedure Ceiling_Cell (Kind : Fill_Kind) is
      Name  : constant String :=
        (if Kind = By_Slice then "H12 (full slice) " else "H12 (full slot table) ");
      N     : constant Positive := (if Kind = By_Slice then Slice_Max else Signers_Max - 1);
      Log_H : constant := 192 * 1024;
      subtype Sto is Store_T (Log_H);
      subtype Lat is Lattice (8);

      procedure Chk (What : String; Cond : Boolean) is
      begin
         Check (Name & What, Cond);
      end Chk;

      --  x1 .. xN.
      type Rev_Frames is array (1 .. N) of Byte_Array (0 .. Revoke_Frame_Len - 1);
      X : Rev_Frames;

      R0  : constant Byte_Array := Roster_Of (5, C0);
      G   : constant Byte_Array := Grant_Of (Author_PK);
      D   : constant Byte_Array := Del_Of (3, 500, 1);
      P   : constant Byte_Array := Put_Of (4, 'a', 900, 2);
      R2  : constant Byte_Array := RR_Roster (1, C2, Both_Members);
      --  Another roster of R with the ceiling of r2, and one above it.
      R2B : constant Byte_Array := RR_Roster (2, C2, Both_Members);
      R4  : constant Byte_Array := RR_Roster (1, C2 + 1, Both_Members);
      --  A founding roster above the cell (gen 6 replaces r0).
      RF  : constant Byte_Array := Roster_Of (6, C2 + 5);

      procedure Put_X (S : in out Sto; L : in out Lat; From, To : Natural) is
      begin
         for I in From .. To loop
            Put (S, L, X (I));
         end loop;
      end Put_X;

      SBase, S0A, S1, S2, S3, S7U, W, R : Sto;
      LBase, L0A, L1, L2, L3, L7U, WL, RL : Lat;
      St   : Status;
      Off  : Log_Size;
      Off1 : Log_Size;   --  the CEIL entry of S1
      LL   : Log_Size;
      VL   : Log_Size;
      Good : Boolean;
      A, Q, C : Natural;
   begin
      for I in 1 .. N loop
         declare
            K_SK : Kome.Crypto.Secret_Key;
            K_PK : Pubkey;
         begin
            if Kind = By_Slice then
               --  R revokes the I-th of N distinct keys.
               Key_Of_Index (1, I, K_SK, K_PK);
               X (I) := Revoke_By (RR_SK, RR_PK, Cap_RR, Cert_RR, K_PK);
            else
               --  The certified root Q_I revokes one key.
               Key_Of_Index (2, I, K_SK, K_PK);
               X (I) := Revoke_By
                 (K_SK, K_PK, 2_000, Make_Cert (Root_SK, Cid_A, K_PK, 2_000), Stranger_PK);
            end if;
         end;
      end loop;

      --  The base {r0, g, d, p}.
      Fresh_Store (SBase, LBase);
      Put (SBase, LBase, R0);
      Put (SBase, LBase, G);
      Put (SBase, LBase, D);
      Put (SBase, LBase, P);

      ------------------------------------------------------------------------
      --  S1. The audit scenario, order A: r0, g, d, p, x1 .. xN, r2.
      ------------------------------------------------------------------------
      S0A := SBase;
      L0A := LBase;
      Put_X (S0A, L0A, 1, N);
      Chk ("setup: the rows have no room for a roster of R, maxceil is c0",
           Auth_Rule (L0A, Hdr (R2)) and then Max_Ceil (L0A) = C0
           and then not Has_Ceil (L0A) and then Holds (L0A, Hdr (D)));
      S1 := S0A;
      L1 := L0A;
      Put (S1, L1, R2, Off1, St);
      Chk ("S1: the roster that finds no room is captured: Ceil_Only",
           St = Ceil_Only and then Off1 = Log_Length (S0A));
      Chk ("S1: maxceil is its ceiling; it is not held; the cell holds it and is live",
           Max_Ceil (L1) = C2 and then not Holds (L1, Hdr (R2))
           and then Has_Ceil (L1) and then Ceil_Held (L1) = Hdr (R2)
           and then Ceil_Live (L1) and then Held_Ceil (L1) = C0);
      Chk ("S1: the expiry at the new horizon: d is gone, p is held, the rows are the old ones",
           Hz (L1, TTL) = 600 and then not Holds (L1, Hdr (D)) and then Holds (L1, Hdr (P))
           and then Cnt (L1) = Cnt (L0A) - 1 and then Auth_Count (L1) = Auth_Count (L0A)
           and then Slots_Used (L1) = Slots_Used (L0A)
           and then (for all I in 1 .. Cnt (L1) => Holds (L0A, Held (L1, I))));
      Chk ("S1: the entry at Off is a CEIL with the frame, and the cell's tag points at it",
           Log_Byte (S1, Off1) = Op_Ceil and then Has_Frame (S1, Off1)
           and then Read_Frame (S1, Off1) = R2
           and then Ceil_Tag (L1) = Make_Tag (Off1, R2'Length)
           and then Log_Entries (S1) = Log_Entries (S0A) + 1
           and then Log_Length (S1) = Off1 + Apply_Prefix + R2'Length);
      Chk ("S1: the authorization digest and seq_self are the ones before; the data digest"
           & " matches its rows",
           Same_State (Digest_Auth (S1), Digest_Auth (S0A)) and then Digests_Match (S1, L1)
           and then Seq_Self (S1) = Seq_Self (S0A) and then Tags_Read_Back (S1, L1));
      for I in 1 .. Cnt (L1) loop
         Lemma_No_Expired (S1, L1, I);
      end loop;

      ------------------------------------------------------------------------
      --  S2. Order B: r0, g, d, p, r2, x1 .. xN.
      ------------------------------------------------------------------------
      S2 := SBase;
      L2 := LBase;
      Put (S2, L2, R2, St);
      Chk ("S2: with room the roster is held, and expires d",
           St = OK and then Holds (L2, Hdr (R2)) and then Max_Ceil (L2) = C2
           and then not Holds (L2, Hdr (D)) and then Holds (L2, Hdr (P)));
      Put_X (S2, L2, 1, N - 1);
      LL := Log_Length (S2);
      W := S2;
      WL := L2;
      Put (S2, L2, X (N), St);
      Chk ("S2: the last REVOKE finds no room: Auth_Full, nothing changes, no cell",
           St = Auth_Full and then Log_Length (S2) = LL and then Log_Bytes (S2) = Log_Bytes (W)
           and then Same_Set (WL, L2) and then not Holds (L2, Hdr (X (N)))
           and then not Has_Ceil (L2));

      ------------------------------------------------------------------------
      --  S3. T19: the same maxceil in every delivery.
      ------------------------------------------------------------------------
      Chk ("S3 (T19): the two arrival orders have the same maxceil, horizon and data row",
           Max_Ceil (L1) = Max_Ceil (L2) and then Max_Ceil (L1) = C2
           and then Hz (L1, TTL) = Hz (L2, TTL) and then Same_Data (L1, L2));
      --  A third order: x1 .. xN, r2, r0, g, p. r2 is captured on a state
      --  with maxceil 0.
      Fresh_Store (S3, L3);
      Put_X (S3, L3, 1, N);
      Put (S3, L3, R2, St);
      Chk ("S3: a third order: r2 is captured at maxceil 0",
           St = Ceil_Only and then Max_Ceil (L3) = C2 and then Held_Ceil (L3) = 0);
      Put (S3, L3, R0);
      Put (S3, L3, G);
      Put (S3, L3, P);
      Put (S3, L3, D, St);
      Chk ("S3: a third order: the same maxceil and data row (d arrives expired)",
           St = OK and then Max_Ceil (L3) = C2 and then Has_Ceil (L3)
           and then Same_Data (L3, L1) and then Hz (L3, TTL) = Hz (L1, TTL));
      --  A fourth delivery: r0, g, d, p, then r2 as the ceiling frame of a
      --  HELLO.
      W := SBase;
      WL := LBase;
      Ceil (W, WL, R2, Off, St);
      Chk ("S3: a fourth delivery (Put_Ceil): the same maxceil and data row",
           St = Ceil_Only and then Max_Ceil (WL) = C2 and then Same_Data (WL, L1)
           and then Hz (WL, TTL) = Hz (L1, TTL));

      ------------------------------------------------------------------------
      --  S4. Reopen.
      ------------------------------------------------------------------------
      Reopen (S1, R, RL, St);
      Chk ("S4: reopen of S1: the same rows, cell, maxceil, digests, seq_self and log (T18)",
           St = OK and then T18 (S1, L1, R, RL) and then Has_Ceil (RL)
           and then Ceil_Held (RL) = Hdr (R2) and then Max_Ceil (RL) = C2
           and then Tags_Read_Back (R, RL) and then Digests_Match (R, RL));
      Reopen (S2, R, RL, St);
      Chk ("S4: reopen of S2 (T18)",
           St = OK and then T18 (S2, L2, R, RL) and then not Has_Ceil (RL)
           and then Max_Ceil (RL) = C2 and then Tags_Read_Back (R, RL));
      Scan (Log_Bytes (S1), Good, A, Q, C);
      Chk ("S4: every APPLY and CEIL frame of S1's log is a verified frame (Trusted_Frame)",
           Good and then C = 1 and then A = Log_Entries (S1) - 1 and then Q = 0);

      ------------------------------------------------------------------------
      --  S5. Compact, then reopen.
      ------------------------------------------------------------------------
      W := S1;
      WL := L1;
      Compact (W, WL, St);
      Chk ("S5: Compact of S1: the CEIL of the cell is the first entry, Count + 2 entries",
           St = OK and then Log_Entries (W) = Cnt (WL) + 2 and then not Compact_Due (W, WL)
           and then Log_Byte (W, Header_Len) = Op_Ceil
           and then Read_Frame (W, Header_Len) = R2
           and then Tag_Off (Ceil_Tag (WL)) = Header_Len and then Ceil_Held (WL) = Hdr (R2)
           and then Tag_Off (Tag (WL, Data_Count (WL) + 1))
                    = Header_Len + Apply_Prefix + R2'Length
           and then Same_Set (L1, WL) and then Max_Ceil (WL) = C2
           and then Log_Byte (W, Log_Length (W) - Seq_Len) = Op_Seq);
      Chk ("S5: Compact of S1: every tag reads back its frame, the cell's included",
           Tags_Read_Back (W, WL) and then Digests_Match (W, WL));
      Scan (Log_Bytes (W), Good, A, Q, C);
      Chk ("S5: the compacted log of S1 scans: one CEIL, Count APPLYs, one SEQ",
           Good and then C = 1 and then A = Cnt (WL) and then Q = 1);
      Reopen (W, R, RL, St);
      Chk ("S5: reopen of the compacted S1 (T18)",
           St = OK and then T18 (W, WL, R, RL) and then Has_Ceil (RL)
           and then Ceil_Held (RL) = Hdr (R2) and then Max_Ceil (RL) = C2
           and then not Holds (RL, Hdr (R2)) and then Tags_Read_Back (R, RL));
      LL := Log_Length (R);
      Put (R, RL, R2, St);
      Chk ("S5: r2 at the reopened S1: Auth_Full, nothing appended",
           St = Auth_Full and then Log_Length (R) = LL);
      W := S2;
      WL := L2;
      Compact (W, WL, St);
      Chk ("S5: Compact of S2: no CEIL, Count + 1 entries",
           St = OK and then Log_Entries (W) = Cnt (WL) + 1 and then not Compact_Due (W, WL)
           and then Log_Byte (W, Header_Len) = Op_Apply and then not Has_Ceil (WL)
           and then Tags_Read_Back (W, WL));
      Reopen (W, R, RL, St);
      Chk ("S5: reopen of the compacted S2 (T18)",
           St = OK and then T18 (W, WL, R, RL) and then Max_Ceil (RL) = C2);

      ------------------------------------------------------------------------
      --  S6. Re-offers at S1.
      ------------------------------------------------------------------------
      W := S1;
      WL := L1;
      LL := Log_Length (W);
      Put (W, WL, R2, St);
      Chk ("S6: r2 again by Put_Frame: Auth_Full, nothing changes",
           St = Auth_Full and then Log_Length (W) = LL and then Same_Cell (WL, L1));
      Ceil (W, WL, R2, Off, St);
      Chk ("S6: r2 again by Put_Ceil: OK, nothing changes",
           St = OK and then Log_Length (W) = LL and then Same_Cell (WL, L1));
      Put (W, WL, R2B, St);
      Chk ("S6: another roster with the cell's ceiling by Put_Frame: Auth_Full",
           St = Auth_Full and then Log_Length (W) = LL and then Same_Cell (WL, L1));
      Ceil (W, WL, R2B, Off, St);
      Chk ("S6: another roster with the cell's ceiling by Put_Ceil: OK, the cell keeps r2",
           St = OK and then Log_Length (W) = LL and then Same_Cell (WL, L1)
           and then Max_Ceil (WL) = C2 and then Same_Set (WL, L1));
      Put (W, WL, R4, Off, St);
      Chk ("S6: a roster with a higher ceiling takes the cell: Ceil_Only",
           St = Ceil_Only and then Off = LL and then Ceil_Held (WL) = Hdr (R4)
           and then Max_Ceil (WL) = C2 + 1 and then not Holds (WL, Hdr (R4))
           and then Same_Set (WL, L1));
      Compact (W, WL, St);
      Scan (Log_Bytes (W), Good, A, Q, C);
      Chk ("S6: Compact keeps one CEIL, of the cell's record",
           St = OK and then Good and then C = 1 and then Read_Frame (W, Header_Len) = R4);
      Reopen (W, R, RL, St);
      Chk ("S6: reopen (T18)", St = OK and then T18 (W, WL, R, RL)
           and then Ceil_Held (RL) = Hdr (R4));

      ------------------------------------------------------------------------
      --  S7. A dead cell: a held roster above it.
      ------------------------------------------------------------------------
      W := S1;
      WL := L1;
      Put (W, WL, RF, St);
      Chk ("S7: a held roster above the cell: maxceil is its ceiling, the cell is not live",
           St = OK and then Holds (WL, Hdr (RF)) and then Max_Ceil (WL) = C2 + 5
           and then Has_Ceil (WL) and then Ceil_Held (WL) = Hdr (R2)
           and then not Ceil_Live (WL));
      S7U := W;
      L7U := WL;
      Compact (W, WL, St);
      Chk ("S7: Compact keeps the dead cell",
           St = OK and then Log_Entries (W) = Cnt (WL) + 2 and then Has_Ceil (WL)
           and then Read_Frame (W, Header_Len) = R2 and then Tags_Read_Back (W, WL));
      Reopen (W, R, RL, St);
      Chk ("S7: reopen gives the same state (T18)",
           St = OK and then T18 (W, WL, R, RL) and then Max_Ceil (RL) = C2 + 5
           and then not Ceil_Live (RL));

      ------------------------------------------------------------------------
      --  S8. The cell's record enters its slice (the slice form only: a
      --  slot is never freed).
      ------------------------------------------------------------------------
      if Kind = By_Slice then
         declare
            RA : constant Byte_Array := RR_Roster (1, 100, Both_Members);
            RB : constant Byte_Array := RR_Roster (2, 50, Both_Members);
            RC : constant Byte_Array := RR_Roster (3, 100, Both_Members);
            S8U : Sto;
            L8U : Lat;
         begin
            W := SBase;
            WL := LBase;
            Put (W, WL, RA);
            Put (W, WL, RB);
            Put_X (W, WL, 1, N - 2);
            Put (W, WL, R2, St);
            Chk ("S8: the slice holds two rosters and 510 REVOKEs: r2 is captured",
                 St = Ceil_Only and then Slot_Count (WL, Slot_Of (WL, To_Key256 (RR_PK))) = Slice_Max
                 and then Ceil_Live (WL));
            Put (W, WL, RC, St);
            Chk ("S8: a roster that dominates the two frees room",
                 St = OK and then Slot_Count (WL, Slot_Of (WL, To_Key256 (RR_PK))) = Slice_Max - 1
                 and then not Holds (WL, Hdr (RA)) and then not Holds (WL, Hdr (RB)));
            Put (W, WL, R2, St);
            Chk ("S8: r2 again enters the slice; the cell keeps its copy and is not live",
                 St = OK and then Holds (WL, Hdr (R2)) and then Has_Ceil (WL)
                 and then Ceil_Held (WL) = Hdr (R2) and then not Ceil_Live (WL)
                 and then Max_Ceil (WL) = C2
                 and then Log_Byte (W, Tag_Off (Tag_Of (WL, Hdr (R2)))) = Op_Apply
                 and then Log_Byte (W, Tag_Off (Ceil_Tag (WL))) = Op_Ceil);
            S8U := W;
            L8U := WL;
            Reopen (W, R, RL, St);
            Chk ("S8: reopen of the uncompacted log (T18)",
                 St = OK and then T18 (W, WL, R, RL) and then Holds (RL, Hdr (R2)));
            Compact (W, WL, St);
            Reopen (W, R, RL, St);
            Chk ("S8: reopen of the compacted log (T18)",
                 St = OK and then T18 (W, WL, R, RL) and then Holds (RL, Hdr (R2))
                 and then Has_Ceil (RL) and then Tags_Read_Back (R, RL));
            --  S10: a copy of the CEIL entry after the last entry (two
            --  APPLYs lie between) replays as OK and changes nothing.
            declare
               Dup : constant Byte_Array := Log_Bytes (S8U) & Entry_Of (Op_Ceil, R2);
            begin
               Open_From_Log (Dup, Author_PK, RL, R, VL, St);
               Chk ("S10: a later copy of the cell's CEIL replays as OK and changes nothing",
                    St = OK and then VL = Dup'Length and then Log_Bytes (R) = Dup
                    and then Same_Set (L8U, RL) and then Same_Cell (L8U, RL)
                    and then Max_Ceil (RL) = C2
                    and then Log_Entries (R) = Log_Entries (S8U) + 1);
            end;
         end;
      end if;

      ------------------------------------------------------------------------
      --  S9. Log_Full: fewer than 4 + len (r2) bytes are left.
      ------------------------------------------------------------------------
      declare
         Small : Store_T (Log_Length (S0A) + Apply_Prefix + R2'Length - 1);
         SL    : Lat;
      begin
         Open_From_Log (Log_Bytes (S0A), Author_PK, SL, Small, VL, St);
         LL := Log_Length (Small);
         Chk ("S9: setup: the log of the state before r2 reopens in a short store",
              St = OK and then Same_Set (SL, L0A));
         Put (Small, SL, R2, St);
         Chk ("S9: Put_Frame of r2 with no log room: Log_Full, nothing changes",
              St = Log_Full and then Log_Length (Small) = LL and then Max_Ceil (SL) = C0
              and then not Has_Ceil (SL));
         Ceil (Small, SL, R2, Off, St);
         Chk ("S9: Put_Ceil of r2 with no log room: Log_Full, nothing changes",
              St = Log_Full and then Log_Length (Small) = LL and then Max_Ceil (SL) = C0
              and then not Has_Ceil (SL) and then Holds (SL, Hdr (D)));
      end;

      ------------------------------------------------------------------------
      --  S10. Replay of CEIL entries: refusals and duplicates.
      ------------------------------------------------------------------------
      declare
         Bad : Byte_Array := Log_Bytes (S1);
      begin
         Bad (Off1) := Op_Apply;
         Open_From_Log (Bad, Author_PK, RL, R, VL, St);
         Chk ("S10: an APPLY that Put_Frame would capture: Malformed at that entry",
              St = Malformed and then VL = Off1 and then Same_Set (L0A, RL)
              and then not Has_Ceil (RL) and then Max_Ceil (RL) = C0);
      end;
      declare
         Low : constant Byte_Array :=
           Log_Bytes (SBase) & Entry_Of (Op_Ceil, RR_Roster (1, 100, Both_Members));
         Gr  : constant Byte_Array :=
           Log_Bytes (SBase) & Entry_Of (Op_Ceil, Grant_Of (Author2_PK));
         Eq  : constant Byte_Array :=
           Log_Bytes (S1) & Entry_Of (Op_Ceil, R2B);
      begin
         Open_From_Log (Low, Author_PK, RL, R, VL, St);
         Chk ("S10: a CEIL whose ceiling is not above maxceil: Malformed",
              St = Malformed and then VL = Log_Length (SBase) and then not Has_Ceil (RL));
         Open_From_Log (Gr, Author_PK, RL, R, VL, St);
         Chk ("S10: a CEIL that carries a GRANT frame: Malformed",
              St = Malformed and then VL = Log_Length (SBase) and then not Has_Ceil (RL)
              and then not In_W (RL, To_Key256 (Author2_PK)));
         Open_From_Log (Eq, Author_PK, RL, R, VL, St);
         Chk ("S10: a CEIL with the cell's ceiling that is not the cell's record: Malformed",
              St = Malformed and then VL = Log_Length (S1) and then Ceil_Held (RL) = Hdr (R2));
      end;
      declare
         Dup : constant Byte_Array := Log_Bytes (S1) & Entry_Of (Op_Ceil, R2);
      begin
         Open_From_Log (Dup, Author_PK, RL, R, VL, St);
         Chk ("S10: the CEIL entry written twice in a row replays as OK, with the same state",
              St = OK and then VL = Dup'Length and then Log_Bytes (R) = Dup
              and then Same_Set (L1, RL) and then Same_Cell (L1, RL)
              and then Max_Ceil (RL) = C2 and then Log_Entries (R) = Log_Entries (S1) + 1
              and then Tags_Read_Back (R, RL));
      end;
      declare
         Dup : constant Byte_Array := Log_Bytes (S7U) & Entry_Of (Op_Ceil, R2);
      begin
         Open_From_Log (Dup, Author_PK, RL, R, VL, St);
         Chk ("S10: a copy of the cell's CEIL after a later APPLY replays as OK",
              St = OK and then VL = Dup'Length and then Log_Bytes (R) = Dup
              and then Same_Set (L7U, RL) and then Same_Cell (L7U, RL)
              and then Max_Ceil (RL) = C2 + 5);
      end;
   end Ceiling_Cell;

   --  S13. Put_Ceil with room: the roster goes to the cell and never to a
   --  row, whatever room its signer's slice has. r3 is a roster of R with
   --  gen 20 that lists only a stranger: in a row it would be ROSTER_eff.
   procedure Ceil_With_Room is
      Log_H : constant := 16 * 1024;
      subtype Sto is Store_T (Log_H);
      subtype Lat is Lattice (8);
      use type Kome.Views.Header_View;
      R0 : constant Byte_Array := Roster_Of (5, C0);
      G  : constant Byte_Array := Grant_Of (Author_PK);
      D  : constant Byte_Array := Del_Of (3, 500, 1);
      P  : constant Byte_Array := Put_Of (4, 'a', 900, 2);
      R3 : constant Byte_Array := RR_Roster (20, C2, Member (Stranger_PK, 31));
      --  The founding REVOKE of R, and a recovery roster.
      V  : constant Byte_Array := Revoke_By (Root_SK, Root_PK, Founding_Cap, Cert_R, RR_PK);
      RR : constant Byte_Array := Roster_Of (9, C0);
      SBase, S, R : Sto;
      LBase, L, RL : Lat;
      St  : Status;
      Off : Log_Size;
   begin
      Fresh_Store (SBase, LBase);
      Put (SBase, LBase, R0);
      Put (SBase, LBase, G);
      Put (SBase, LBase, D);
      Put (SBase, LBase, P);
      S := SBase;
      L := LBase;
      Ceil (S, L, R3, Off, St);
      Check ("S13: Put_Ceil with room: Ceil_Only, the roster is in the cell and in no row",
             St = Ceil_Only and then not Holds (L, Hdr (R3))
             and then Slots_Used (L) = Slots_Used (LBase)
             and then Auth_Count (L) = Auth_Count (LBase)
             and then Slot_Of (L, To_Key256 (RR_PK)) = 0
             and then Has_Ceil (L) and then Ceil_Held (L) = Hdr (R3) and then Ceil_Live (L)
             and then Max_Ceil (L) = C2);
      Check ("S13: the capture expires d, appends a CEIL, keeps the authorization digest",
             not Holds (L, Hdr (D)) and then Holds (L, Hdr (P))
             and then Off = Log_Length (SBase) and then Log_Byte (S, Off) = Op_Ceil
             and then Read_Frame (S, Off) = R3
             and then Same_State (Digest_Auth (S), Digest_Auth (SBase))
             and then Digests_Match (S, L) and then Tags_Read_Back (S, L));
      Check ("S13: ROSTER_eff is still r0, and the replica is not quarantined",
             Kome.Views.Roster_Eff (L) = (Present => True, Hdr => Hdr (R0)) and then not Kome.Views.Quarantined (L)
             and then Kome.Views.Roster_Max (L) = (Present => True, Hdr => Hdr (R0)));
      Reopen (S, R, RL, St);
      Check ("S13: reopen of the uncompacted log: the same state, r3 still in no row",
             St = OK and then T18 (S, L, R, RL) and then not Holds (RL, Hdr (R3))
             and then Ceil_Held (RL) = Hdr (R3)
             and then Kome.Views.Roster_Eff (RL) = (Present => True, Hdr => Hdr (R0)));
      Compact (S, L, St);
      Reopen (S, R, RL, St);
      Check ("S13: reopen of the compacted log: the same state, r3 still in no row",
             St = OK and then T18 (S, L, R, RL) and then not Holds (RL, Hdr (R3))
             and then Ceil_Held (RL) = Hdr (R3) and then Max_Ceil (RL) = C2
             and then Slot_Of (RL, To_Key256 (RR_PK)) = 0);
      --  After the root-void of R and a recovery roster.
      S := SBase;
      L := LBase;
      Put (S, L, V);
      Put (S, L, RR);
      R := S;
      RL := L;
      Ceil (S, L, R3, Off, St);
      Check ("S13: after the root-void of its signer the ceiling frame still raises maxceil",
             St = Ceil_Only and then Max_Ceil (L) = C2 and then not Holds (L, Hdr (R3))
             and then Kome.Views.Root_Void (L, To_Key256 (RR_PK)));
      Check ("S13: Roster_Max is the recovery roster, and the replica is not quarantined",
             Kome.Views.Roster_Max (L) = (Present => True, Hdr => Hdr (RR)) and then not Kome.Views.Quarantined (L)
             and then Kome.Views.Roster_Eff (L) = (Present => True, Hdr => Hdr (RR)));
      --  For contrast: the same roster as a record enters a row and
      --  quarantines the replica.
      Put (R, RL, R3, St);
      Check ("S13: for contrast, Put_Frame of r3 holds it and quarantines the replica",
             St = OK and then Holds (RL, Hdr (R3)) and then Kome.Views.Quarantined (RL));
      declare
         T : Sto := SBase;
         TL : Lat := LBase;
         procedure Grant_As_Ceil is
            GF : constant Byte_Array := Grant_Of (Author2_PK);
            O  : Log_Size;
            X  : Status;
         begin
            Put_Ceil (T, TL, GF, Header_Of (Cid (T), GF), O, X);
         end Grant_As_Ceil;
         function Pre_Refuses is new Refused (Grant_As_Ceil);
      begin
         if Contracts_On then
            Check ("S13: Put_Ceil of a GRANT frame is refused by its Pre", Pre_Refuses);
         else
            Skip ("S13: Put_Ceil of a GRANT frame is refused by its Pre");
         end if;
      end;
   end Ceil_With_Room;

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
   Kome.Crypto.Key_Pair (Seed_Of (7), RR_SK, RR_PK);
   Cid_A := Cid_Of (Root_PK, Salt_A, TTL);
   Fnd := To_Key256 (Root_PK);
   Cert_R := Make_Cert (Root_SK, Cid_A, Root_PK, Founding_Cap);
   Cert_RR := Make_Cert (Root_SK, Cid_A, RR_PK, Cap_RR);

   ---------------------------------------------------------------------------
   --  Known-answer vectors: the HEADER, the APPLY prefix, the SEQ entry.
   ---------------------------------------------------------------------------
   declare
      File    : File_Type;
      Headers : Natural := 0;
      Applies : Natural := 0;
      Seqs    : Natural := 0;
      Ceils   : Natural := 0;
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
            elsif Line'Length >= 5 and then Line (Line'First .. Line'First + 4) = "ceil " then
               --  S12: the CEIL prefix, 03 ‖ len:u24 (AUDIT.md H12).
               declare
                  N  : constant Natural := Natural'Value (Field (2));
                  PB : constant Byte_Array := Hex (Field (3));
                  E  : constant Byte_Array := Entry_Of (Op_Ceil, Fill (N, 1));
               begin
                  All_Good := All_Good and then PB'Length = Apply_Prefix
                        and then PB (0) = Op_Ceil
                        and then PB (1) = Byte_Of_U24 (N, 0)
                        and then PB (2) = Byte_Of_U24 (N, 1)
                        and then PB (3) = Byte_Of_U24 (N, 2)
                        and then U24_Of (PB (1), PB (2), PB (3)) = N
                        and then E (0 .. Apply_Prefix - 1) = PB;
                  Ceils := Ceils + 1;
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
      Check ("vectors: HEADER (59 bytes) and cid, APPLY prefix, SEQ entry, CEIL prefix",
             All_Good and then Headers = 3 and then Applies = 6 and then Seqs = 5
             and then Ceils = 3);
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
         A, Q, C : Natural;
      begin
         Scan (Log_Bytes (S), Good, A, Q, C);
         Check ("every APPLY frame of the log is a verified frame (Trusted_Frame)",
                Good and then A = Log_Entries (S) and then Q = 0 and then C = 0);
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
         A, Q, C : Natural;
      begin
         Scan (Log_Bytes (S), Good, A, Q, C);
         Check ("the compacted log scans: Count APPLYs and one SEQ",
                Good and then A = Cnt (L) and then Q = 1 and then C = 0);
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

   ---------------------------------------------------------------------------
   --  The ceiling cell (AUDIT.md H12).
   ---------------------------------------------------------------------------
   Check ("S11: Log_Fits keeps room for a CEIL: 17 915 fits a 1 GiB log, 17 916 does not",
          Log_Fits (17_915, 2**30) and then not Log_Fits (17_916, 2**30));
   Ceil_With_Room;
   Ceiling_Cell (By_Slots);
   if Contracts_On then
      Put_Line ("SKIP H12 (full slice): the 512-record form of the scenario (check mode:"
                & " under -gnata the digest contracts of 512 held records do not end in"
                & " reasonable time; it runs with MODE=release)");
   else
      Ceiling_Cell (By_Slice);
   end if;

   if Failed then
      Set_Exit_Status (Failure);
   end if;
   end Run_All;

begin
   null;
end Test_Store;
