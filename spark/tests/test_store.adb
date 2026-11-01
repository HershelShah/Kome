--  Test main for Kome.Store (DESIGN.md §7). Real signed frames from
--  Kome.Records go through the store: put, overwrite (the older frame leaves
--  the index), a dominated re-offer and a duplicate (nothing appended), a
--  DEL that frees every field of its entity, an unrostered author refused
--  with the store unchanged, every No_Space path refused with the store and
--  the frontier unchanged (frontier full, log full, index full, a would-be
--  dominated record on a full log, an expired DEL on a full log, a roster
--  on a full frontier whose registers must not rise), expiry (a DEL past
--  del_ttl leaves the index; an arriving DEL already past it is applied,
--  frees its entity's fields, and is not indexed; the u48 sum at
--  t = 2**48 - 1 does not wrap), compaction (the log shrinks to exactly the
--  indexed frames, byte for byte, the frontier unchanged), and reopening a
--  store by scanning its log's frame chain and replaying every frame: the
--  same index and registers (writer by writer), and the same frontier
--  except for the expired DELs the live one still holds (Kome.Frontier has
--  no Remove; the wedge this causes is shown too). Compiled with -gnata, so
--  every Pre / Post (Valid included) is also executed on these stores.
pragma Ada_2022;
with Ada.Text_IO;      use Ada.Text_IO;
with Ada.Command_Line; use Ada.Command_Line;
with Kome;             use Kome;
with Kome.Headers;     use Kome.Headers;
with Kome.Registers;   use Kome.Registers;
with Kome.Frontier;    use Kome.Frontier;
with Kome.Keys;        use Kome.Keys;
with Kome.Crypto;
with Kome.Records;     use Kome.Records;
with Kome.Store;       use Kome.Store;

procedure Test_Store with SPARK_Mode => Off is

   subtype Store_T is Kome.Store.Store;

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

   Author_SK, Stranger_SK, Root_SK, Root2_SK : Kome.Crypto.Secret_Key;
   Author_PK, Stranger_PK, Root_PK, Root2_PK : Pubkey;
   Salt_A : constant Salt := Salt (Fill (Salt_Len, 90));
   NS_A   : NS_Id;
   NS     : Id128;

   Cap     : constant := 32;
   Log_Cap : constant := 8192;
   TTL     : constant U48 := 1000;

   --  The header and roster member keys of a verified frame: what the
   --  caller of Put_Frame supplies.
   function Hdr (F : Byte_Array) return Header is (Header_Of (F));

   function Mem (F : Byte_Array) return Member_Keys is
   begin
      if Kind_Of (F) = K_Roster then
         declare
            C : constant Roster_Content := Parse_Roster (F).C;
         begin
            return [for I in 1 .. C.N_Members => Member_Key (C, I)];
         end;
      else
         return [];
      end if;
   end Mem;

   function Verified (F : Byte_Array) return Boolean is
     (case Kind_Of (F) is
         when K_Put    => Is_Put_Frame (F) and then Well_Formed (Parse_Put (F)),
         when K_Del    => Is_Del_Frame (F) and then Well_Formed (Parse_Del (F)),
         when K_Roster => Is_Roster_Frame (F) and then Well_Formed (Parse_Roster (F)),
         when K_Revoke => Is_Revoke_Frame (F) and then Well_Formed (Parse_Revoke (F)));

   subtype Lattice is Kome.Frontier.State;

   procedure Put
     (S : in out Store_T; L : in out Lattice; F : Byte_Array; Off : out Log_Size;
      St : out Status) is
   begin
      if not Verified (F) then
         raise Program_Error with "test frame not well-formed";
      end if;
      if not Members_Agree (F, Mem (F)) then
         raise Program_Error with "test members do not agree";
      end if;
      Put_Frame (S, L, F, Hdr (F), Mem (F), Off, St);
   end Put;

   procedure Put (S : in out Store_T; L : in out Lattice; F : Byte_Array; St : out Status) is
      Off : Log_Size;
   begin
      Put (S, L, F, Off, St);
   end Put;

   function Put_Frame_Of
     (Ent : Byte; Field : Character; T, Seq : U48; Value : Byte_Array;
      SK  : Kome.Crypto.Secret_Key; PK : Pubkey) return Byte_Array
   is
      R : Put_Record :=
        Make_Put (NS_A, Ent_Id (Fill (Ent_Len, Natural (Ent))),
                  [Character'Pos (Field)], T, Seq, PK, Value);
   begin
      Sign (R, SK);
      return Encode (R);
   end Put_Frame_Of;

   function Del_Frame_Of (Ent : Byte; T, Seq : U48) return Byte_Array is
      R : Del_Record;
   begin
      R.C := (NS => NS_A, Ent => Ent_Id (Fill (Ent_Len, Natural (Ent))),
              T => T, Seq => Seq, Author => Author_PK);
      Sign (R, Author_SK);
      return Encode (R);
   end Del_Frame_Of;

   function Roster_Frame_Of (Gen, Ceiling : U48) return Byte_Array is
      Member : constant Byte_Array :=
        Author_PK & Fill (Pubkey_Len, 11) & Fill (Nonce_Len, 12) & Fill (Box_Len, 13);
      R : Roster_Record :=
        Make_Roster (Root_PK, Salt_A, Root_PK, [for I in 0 .. Hash_Len - 1 => 0],
                     Gen, Ceiling, TTL, 0, [], Member);
   begin
      Sign (R, Root_SK);
      return Encode (R);
   end Roster_Frame_Of;

   --  A roster issued by a second root (listed as a root of its own), with
   --  Stranger as member: it neither dominates nor is dominated by the
   --  first root's roster.
   function Roster2_Frame_Of (Gen, Ceiling : U48) return Byte_Array is
      Member : constant Byte_Array :=
        Stranger_PK & Fill (Pubkey_Len, 21) & Fill (Nonce_Len, 22) & Fill (Box_Len, 23);
      R : Roster_Record :=
        Make_Roster (Root_PK, Salt_A, Root2_PK, [for I in 0 .. Hash_Len - 1 => 0],
                     Gen, Ceiling, TTL, 0, Root2_PK, Member);
   begin
      Sign (R, Root2_SK);
      return Encode (R);
   end Roster2_Frame_Of;

   function Cell_Of (Field : Character) return Key256 is
     (To_Key256 (Kome.Crypto.Blake2b_256 ([Character'Pos (Field)])));

   function Ent_Of (Ent : Byte) return Id128 is
     (To_Id128 (Ent_Id (Fill (Ent_Len, Natural (Ent)))));

   --  The frame an index entry points at.
   function Frame_Of (S : Store_T; I : Positive) return Byte_Array is
     (Read_Frame (S, Entry_At (S, I).Off));

   function Has_Header (S : Store_T; X : Header) return Boolean is
     (for some I in 1 .. Entries (S) => Entry_At (S, I).H = X);

   type Key_List is array (Positive range <>) of Pubkey;

   --  The same registers: ceiling, writer count, and writer by writer for
   --  every key the test uses.
   function Same_Regs (AL, BL : Lattice) return Boolean is
     (Ceil (Regs (AL)) = Ceil (Regs (BL))
      and then Kome.Registers.Count (Regs (AL)) = Kome.Registers.Count (Regs (BL))
      and then (for all K of Key_List'[Author_PK, Stranger_PK, Root_PK, Root2_PK] =>
                  In_W (Regs (AL), To_Key256 (K)) = In_W (Regs (BL), To_Key256 (K))));

   --  Two stores index the same records and have the same registers.
   function Same_Index (A : Store_T; AL : Lattice; B : Store_T; BL : Lattice)
     return Boolean is
     (Entries (A) = Entries (B)
      and then (for all I in 1 .. Entries (A) => Has_Header (B, Entry_At (A, I).H))
      and then Same_Regs (AL, BL));

   --  The frontier of a reopened replica against the live one: the reopened
   --  one holds a subset, and what it lacks is exactly the live one's
   --  expired DELs (Kome.Frontier cannot remove them; see Kome.Store).
   function Expired_Held (L : Lattice; Hz : Time64) return Natural is
      N : Natural := 0;
   begin
      for K in 1 .. Kome.Frontier.Count (L) loop
         if Expired (Held (L, K), Hz) then
            N := N + 1;
         end if;
      end loop;
      return N;
   end Expired_Held;

   function Live_Minus_Expired
     (LL : Lattice; Hz : Time64; RL : Lattice) return Boolean is
     ((for all K in 1 .. Kome.Frontier.Count (RL) => Holds (LL, Held (RL, K)))
      and then (for all K in 1 .. Kome.Frontier.Count (LL) =>
                  Holds (RL, Held (LL, K)) or else Expired (Held (LL, K), Hz))
      and then (for all K in 1 .. Kome.Frontier.Count (RL) =>
                  not Expired (Held (RL, K), Hz))
      and then Kome.Frontier.Count (LL) = Kome.Frontier.Count (RL) + Expired_Held (LL, Hz));

   --  A scan of the log as a file (offset 0, then Next_Offset) visits
   --  exactly the frame chain of the invariant and ends at the log's end.
   function Scan_Matches_Chain (S : Store_T; L : Lattice) return Boolean is
      Off : Natural := 0;
      K   : Natural := 0;
   begin
      Lemma_Scan (S, L);
      while Off < Log_Length (S) loop
         K := K + 1;
         if K > Frames (S) or else Frame_Start (S, K) /= Off
           or else not Has_Frame (S, Off)
         then
            return False;
         end if;
         Off := Next_Offset (S, Off);
      end loop;
      return K = Frames (S) and then Off = Log_Length (S);
   end Scan_Matches_Chain;

   --  Reopen: replay the frames of the log, in order, into a fresh store
   --  and lattice.
   procedure Reopen (S : Store_T; L : Lattice; R : out Store_T; RL : out Lattice) is
      St : Status;
   begin
      if not Scan_Matches_Chain (S, L) then
         raise Program_Error with "log does not scan as its frame chain";
      end if;
      RL := Empty (Collection (S), RL.Cap);
      Open (Collection (S), RL, R);
      for K in 1 .. Frames (S) loop
         Put (R, RL, Read_Frame (S, Frame_Start (S, K)), St);
      end loop;
   end Reopen;

   function Every_Frame_Matches (S : Store_T) return Boolean is
     (for all I in 1 .. Entries (S) =>
        Hdr (Frame_Of (S, I)) = Entry_At (S, I).H
        and then Frame_Of (S, I)'Length = Entry_At (S, I).Len);

begin
   Kome.Crypto.Key_Pair (Seed_Of (1), Author_SK, Author_PK);
   Kome.Crypto.Key_Pair (Seed_Of (2), Stranger_SK, Stranger_PK);
   Kome.Crypto.Key_Pair (Seed_Of (3), Root_SK, Root_PK);
   Kome.Crypto.Key_Pair (Seed_Of (4), Root2_SK, Root2_PK);
   NS_A := Collection_Id (Root_PK, Salt_A);
   NS := To_Id128 (NS_A);

   declare
      Roster : constant Byte_Array := Roster_Frame_Of (1, 10_000);
      P1     : constant Byte_Array := Put_Frame_Of (1, 'n', 100, 1, [1, 2, 3], Author_SK, Author_PK);
      P2     : constant Byte_Array := Put_Frame_Of (1, 'n', 200, 2, [4, 5], Author_SK, Author_PK);
      P3     : constant Byte_Array := Put_Frame_Of (1, 'a', 150, 3, [], Author_SK, Author_PK);
      D1     : constant Byte_Array := Del_Frame_Of (1, 300, 4);
      P4     : constant Byte_Array := Put_Frame_Of (2, 'n', 400, 5, [9], Author_SK, Author_PK);
      P5     : constant Byte_Array := Put_Frame_Of (3, 'x', 200, 6, [7, 7], Author_SK, Author_PK);
      D2     : constant Byte_Array := Del_Frame_Of (3, 250, 7);
      PX     : constant Byte_Array := Put_Frame_Of (4, 'n', 100, 1, [1], Stranger_SK, Stranger_PK);
      Roster2 : constant Byte_Array := Roster2_Frame_Of (1, 20_000);
      S       : Store_T (Cap, Log_Cap);
      SL      : Lattice (Cap);
      Raw     : Store_T (Cap, Log_Cap);   --  the log before compaction
      RawL    : Lattice (Cap);
      Before  : Store_T (Cap, Log_Cap);
      BeforeL : Lattice (Cap);
      Off    : Log_Size;
      St     : Status;
      Found  : Boolean;
      I      : Held_Count;
   begin
      SL := Empty (NS, SL.Cap);
      Open (NS, SL, S);
      Check ("open: empty and valid",
             Valid (S, SL) and then Entries (S) = 0 and then Log_Length (S) = 0
             and then Kome.Frontier.Count (SL) = 0 and then Horizon (S) = No_Horizon);

      --  Put.
      Put (S, SL, Roster, Off, St);
      Check ("roster: OK, appended at offset 0, registers raised",
             St = OK and then Off = 0 and then Entries (S) = 1
             and then Log_Length (S) = Prefix_Len + Roster'Length
             and then Ceil (Regs (SL)) = 10_000
             and then Kome.Registers.Count (Regs (SL)) = 1);
      Check ("roster: Read_Frame (0) is the frame", Read_Frame (S, 0) = Roster);

      Put (S, SL, P1, Off, St);
      Check ("put: OK, appended after the roster",
             St = OK and then Off = Prefix_Len + Roster'Length and then Entries (S) = 2
             and then Read_Frame (S, Off) = P1);
      Find_Cell (S, SL, NS, Ent_Of (1), Cell_Of ('n'), Found, I);
      Check ("put: cell index finds it",
             Found and then Entry_At (S, I).Off = Off and then Entry_At (S, I).H = Hdr (P1)
             and then Entry_At (S, I).H.V.T = 100);

      --  Overwrite.
      declare
         L : constant Log_Size := Log_Length (S);
      begin
         Put (S, SL, P2, Off, St);
         Find_Cell (S, SL, NS, Ent_Of (1), Cell_Of ('n'), Found, I);
         Check ("overwrite: newer PUT indexed, older gone from index and frontier",
                St = OK and then Off = L and then Entries (S) = 2
                and then Found and then Entry_At (S, I).H = Hdr (P2)
                and then Read_Frame (S, Entry_At (S, I).Off) = P2
                and then not Has_Header (S, Hdr (P1))
                and then not Holds (SL, Hdr (P1)));
         Check ("overwrite: the log is append-only (old frame still there)",
                Read_Frame (S, Prefix_Len + Roster'Length) = P1
                and then Log_Length (S) = L + Prefix_Len + P2'Length);
      end;

      declare
         L : constant Log_Size := Log_Length (S);
      begin
         Put (S, SL, P1, St);
         Check ("older PUT re-offered: Dominated, nothing appended",
                St = Dominated and then Log_Length (S) = L and then Entries (S) = 2);
         Put (S, SL, P2, St);
         Check ("duplicate: OK, nothing appended",
                St = OK and then Log_Length (S) = L and then Entries (S) = 2);
      end;

      Put (S, SL, P3, St);
      Check ("second field of the entity", St = OK and then Entries (S) = 3);

      --  Delete frees fields.
      Put (S, SL, D1, St);
      Find_Cell (S, SL, NS, Ent_Of (1), Cell_Of ('n'), Found, I);
      Check ("delete: DEL indexed, every field of the entity freed",
             St = OK and then Entries (S) = 2 and then Has_Header (S, Hdr (D1))
             and then not Has_Header (S, Hdr (P2)) and then not Has_Header (S, Hdr (P3))
             and then not Found
             and then not Holds (SL, Hdr (P2))
             and then not Holds (SL, Hdr (P3)));

      Put (S, SL, P4, St);
      Put (S, SL, P5, St);
      Check ("other entities", St = OK and then Entries (S) = 4);
      Check ("every entry's frame decodes to its header", Every_Frame_Matches (S));
      Check ("the log scans as its frame chain", Scan_Matches_Chain (S, SL));
      Check ("a header or member keys not the frame's violate Put_Frame's Pre",
             Header_Of (P1) /= Hdr (P2)
             and then not Members_Agree (Roster, [To_Key256 (Stranger_PK)])
             and then not Members_Agree (Roster, [])
             and then Members_Agree (Roster, [To_Key256 (Author_PK)])
             and then not Members_Agree (P1, [To_Key256 (Author_PK)]));

      --  Refusals change nothing.
      Before := S;
      BeforeL := SL;
      Put (S, SL, PX, St);
      Check ("unrostered author: Inadmissible, store unchanged",
             St = Inadmissible and then S = Before and then SL = BeforeL);
      declare
         Small  : Store_T (Cap, Prefix_Len + Roster'Length + 10);
         SmallL : Lattice (Cap);
         Snap   : Store_T (Cap, Prefix_Len + Roster'Length + 10);
         SnapL  : Lattice (Cap);
      begin
         SmallL := Empty (NS, SmallL.Cap);
      Open (NS, SmallL, Small);
         Put (Small, SmallL, Roster, St);
         Snap := Small;
         SnapL := SmallL;
         Put (Small, SmallL, P1, St);
         Check ("log full: No_Space, store unchanged (registers too)",
                St = No_Space and then Small = Snap and then SmallL = SnapL);
      end;
      declare
         Tiny  : Store_T (2, Log_Cap);
         TinyL : Lattice (2);
         Snap  : Store_T (2, Log_Cap);
         SnapL : Lattice (2);
      begin
         TinyL := Empty (NS, TinyL.Cap);
      Open (NS, TinyL, Tiny);
         Put (Tiny, TinyL, Roster, St);
         Put (Tiny, TinyL, P1, St);
         Snap := Tiny;
         SnapL := TinyL;
         Put (Tiny, TinyL, P4, St);
         Check ("frontier full: No_Space, store unchanged",
                St = No_Space and then Tiny = Snap and then TinyL = SnapL);
         Put (Tiny, TinyL, P2, St);
         Check ("frontier full: an overwrite still fits (it frees its slot)",
                St = OK and then Has_Header (Tiny, Hdr (P2))
                and then not Has_Header (Tiny, Hdr (P1)) and then Entries (Tiny) = 2);
         Snap := Tiny;
         SnapL := TinyL;
         Put (Tiny, TinyL, Roster2, St);
         Check ("frontier full: a roster that frees nothing is refused, registers not raised",
                St = No_Space and then Tiny = Snap and then TinyL = SnapL
                and then Ceil (Regs (TinyL)) = 10_000
                and then not In_W (Regs (TinyL), To_Key256 (Stranger_PK)));
      end;
      declare
         --  Index of 2 entries beside a frontier of 8.
         Ix    : Store_T (2, Log_Cap);
         IxL   : Lattice (8);
         Snap  : Store_T (2, Log_Cap);
         SnapL : Lattice (8);
      begin
         IxL := Empty (NS, IxL.Cap);
         Open (NS, IxL, Ix);
         Put (Ix, IxL, Roster, St);
         Put (Ix, IxL, P1, St);
         Snap := Ix;
         SnapL := IxL;
         Put (Ix, IxL, P4, St);
         Check ("index full, frontier not: No_Space, store and frontier unchanged",
                St = No_Space and then Ix = Snap and then IxL = SnapL
                and then Kome.Frontier.Count (IxL) = 2);
         Put (Ix, IxL, P2, St);
         Check ("index full: an overwrite frees its entry and fits",
                St = OK and then Entries (Ix) = 2 and then Has_Header (Ix, Hdr (P2))
                and then not Has_Header (Ix, Hdr (P1)));
      end;
      declare
         --  Room for the roster and P2 and not one more frame.
         Cap2  : constant Natural := Prefix_Len + Roster'Length + Prefix_Len + P2'Length + 3;
         Sm    : Store_T (Cap, Cap2);
         SmL   : Lattice (Cap);
         Snap  : Store_T (Cap, Cap2);
         SnapL : Lattice (Cap);
         Fr    : Lattice (Cap);
      begin
         SmL := Empty (NS, SmL.Cap);
         Open (NS, SmL, Sm);
         Put (Sm, SmL, Roster, St);
         Put (Sm, SmL, P2, St);
         Check ("small log holds the roster and one PUT",
                St = OK and then Entries (Sm) = 2
                and then Cap2 - Log_Length (Sm) < Prefix_Len + P1'Length
                and then Cap2 - Log_Length (Sm) < Prefix_Len + D1'Length);
         Snap := Sm;
         SnapL := SmL;
         Put (Sm, SmL, P1, St);
         Check ("log full: a record that would be dominated is refused unchanged",
                St = No_Space and then Sm = Snap and then SmL = SnapL);
         Put (Sm, SmL, P2, St);
         Check ("log full: a duplicate needs no room and is OK",
                St = OK and then Sm = Snap and then SmL = SnapL);
         Expire (Sm, SmL, 1300, TTL);
         Snap := Sm;
         Put (Sm, SmL, D1, St);
         Check ("log full: an already expired DEL is refused unchanged (P2 stays)",
                St = No_Space and then Sm = Snap and then SmL = SnapL
                and then Holds (SmL, Hdr (P2)));
         --  On a store with room, the second root's roster raises the
         --  registers and admits its member.
         Fr := Empty (NS, Fr.Cap);
         declare
            Wide : Store_T (Cap, Log_Cap);
         begin
            Open (NS, Fr, Wide);
            Put (Wide, Fr, Roster, St);
            Put (Wide, Fr, Roster2, St);
            Check ("with room, the second root's roster raises the registers",
                   St = OK and then Ceil (Regs (Fr)) = 20_000
                   and then In_W (Regs (Fr), To_Key256 (Stranger_PK))
                   and then Holds (Fr, Hdr (Roster)) and then Holds (Fr, Hdr (Roster2)));
            Put (Wide, Fr, PX, St);
            Check ("and its member's PUT is then admitted", St = OK);
         end;
      end;

      Raw := S;
      RawL := SL;

      --  Expire.
      Expire (S, SL, 1000, TTL);
      Check ("expire at now = 1000: DEL at t = 300 is younger than del_ttl, kept",
             Entries (S) = 4 and then Has_Header (S, Hdr (D1)));
      Expire (S, SL, 1299, TTL);
      Check ("expire at now = 1299: still kept (300 + 1000 > 1299)",
             Entries (S) = 4 and then Has_Header (S, Hdr (D1)));
      Expire (S, SL, 1300, TTL);
      Check ("expire at now = 1300: DEL dropped from the index",
             Entries (S) = 3 and then not Has_Header (S, Hdr (D1))
             and then Has_Header (S, Hdr (P4)) and then Has_Header (S, Hdr (P5))
             and then Horizon (S) = 300);
      Check ("expire: the lattice and the log are untouched",
             SL = RawL and then Log_Length (S) = Log_Length (Raw));
      Expire (S, SL, 500, TTL);
      Check ("expire with the clock stepped back: horizon does not retreat",
             Horizon (S) = 300 and then Entries (S) = 3);

      --  Apply-then-expire.
      declare
         L : constant Log_Size := Log_Length (S);
      begin
         Put (S, SL, D2, Off, St);
         Check ("arriving DEL already past del_ttl: applied, frees its entity, not indexed",
                St = OK and then Holds (SL, Hdr (D2))
                and then not Has_Header (S, Hdr (D2))
                and then not Has_Header (S, Hdr (P5))
                and then not Holds (SL, Hdr (P5))
                and then Entries (S) = 2);
         Check ("its frame is logged until compaction (replay frees the same fields)",
                Off = L and then Read_Frame (S, Off) = D2
                and then Log_Length (S) = L + Prefix_Len + D2'Length);
         Put (S, SL, D2, St);
         Check ("re-offered expired DEL: a duplicate, nothing appended",
                St = OK and then Log_Length (S) = L + Prefix_Len + D2'Length);
      end;
      Expire (Raw, RawL, 1300, TTL);
      Put (Raw, RawL, D2, St);

      --  The u48 wrap hazard (DESIGN.md §7): computed in 64 bits.
      declare
         Last : constant Header :=
           (K => K_Del, NS => NS, Ent => Ent_Of (9), FH => (others => 0),
            V => (T => U48'Last, Author => To_Key256 (Author_PK), Seq => 1,
                  H => (others => 1)),
            Ceiling => 0);
      begin
         Check ("t = 2**48 - 1: not expired at any now < t + del_ttl",
                not Expired_At (Last, U48'Last, TTL)
                and then not Expired_At (Last, 0, TTL)
                and then not Expired_At (Last, U48'Last, 1)
                and then Expired_At (Last, U48'Last, 0));
      end;

      --  Compact.
      Before := S;
      BeforeL := SL;
      Compact (S, SL);
      Check ("compact: frontier, registers and horizon unchanged",
             SL = BeforeL and then Horizon (S) = Horizon (Before));
      Check ("compact: the log is exactly the indexed frames",
             Entries (S) = 2
             and then Log_Length (S) =
               Prefix_Len + Roster'Length + Prefix_Len + P4'Length
             and then Log_Length (S) < Log_Length (Before)
             and then Entry_At (S, 1).Off = 0
             and then Entry_At (S, 2).Off = End_Of (Entry_At (S, 1)));
      Check ("compact: the same frames, byte for byte",
             (for all K in 1 .. Entries (S) =>
                Frame_Of (S, K) = Frame_Of (Before, K)
                and then Entry_At (S, K).H = Entry_At (Before, K).H));
      Check ("compact: frames decode to their headers", Every_Frame_Matches (S));
      Check ("compact: the frame chain is the index",
             Frames (S) = Entries (S) and then Scan_Matches_Chain (S, SL)
             and then (for all K in 1 .. Entries (S) =>
                         Frame_Start (S, K) = Entry_At (S, K).Off));
      Find_Cell (S, SL, NS, Ent_Of (2), Cell_Of ('n'), Found, I);
      Check ("compact: cell index still finds the live PUT",
             Found and then Entry_At (S, I).H = Hdr (P4)
             and then Read_Frame (S, Entry_At (S, I).Off) = P4);

      --  Reopen.
      declare
         R1  : Store_T (Cap, Log_Cap);
         R1L : Lattice (Cap);
         R2  : Store_T (Cap, Log_Cap);
         R2L : Lattice (Cap);
      begin
         Reopen (S, SL, R1, R1L);
         Reopen (Raw, RawL, R2, R2L);
         Check ("reopen from the compacted log: same index and registers",
                Valid (R1, R1L) and then Same_Index (S, SL, R1, R1L));
         Check ("reopen from the compacted log: its frontier is the indexed records",
                Kome.Frontier.Count (R1L) = Entries (S)
                and then (for all K in 1 .. Kome.Frontier.Count (R1L) =>
                            Has_Header (S, Held (R1L, K))));
         Check ("reopen: the live frontier is the reopened one plus its 2 expired DELs",
                Live_Minus_Expired (SL, Horizon (S), R1L)
                and then Expired_Held (SL, Horizon (S)) = 2
                and then Kome.Frontier.Count (SL) = 4
                and then Kome.Frontier.Count (R1L) = 2
                and then Holds (SL, Hdr (D1)) and then Holds (SL, Hdr (D2))
                and then not Holds (R1L, Hdr (D1)) and then not Holds (R1L, Hdr (D2)));
         Check ("reopen from the uncompacted log replays every frame",
                Valid (R2, R2L) and then Entries (R2) > Entries (S));
         Expire (R2, R2L, 1300, TTL);
         Check ("reopen from the uncompacted log, then the same expiry: same index",
                Same_Index (S, SL, R2, R2L));
         Compact (R2, R2L);
         Check ("and compacting it gives the same log length",
                Log_Length (R2) = Log_Length (S));
         Check ("and the frontier replayed from it holds the same records as the live one",
                Kome.Frontier.Count (R2L) = Kome.Frontier.Count (SL)
                and then (for all K in 1 .. Kome.Frontier.Count (SL) =>
                            Holds (R2L, Held (SL, K))));
         Expire (R1, R1L, 1300, TTL);
         Check ("expire after reopen drops nothing more", Same_Index (S, SL, R1, R1L));
      end;

      --  The wedge (the cost of Kome.Frontier having no Remove): a frontier
      --  of 4 that has held a roster and three PUT / DEL pairs holds the
      --  roster and three DELs for good. Expire and Compact empty the index
      --  and the log of them, but every new record that frees nothing is
      --  refused, at any later time.
      declare
         W   : Store_T (4, Log_Cap);
         WL  : Lattice (4);
         P8  : constant Byte_Array := Put_Frame_Of (8, 'n', 100, 9, [8], Author_SK, Author_PK);
      begin
         WL := Empty (NS, WL.Cap);
         Open (NS, WL, W);
         Put (W, WL, Roster, St);
         for E in Byte range 5 .. 7 loop
            Put (W, WL, Put_Frame_Of (E, 'n', 100, U48 (E), [E], Author_SK, Author_PK), St);
            Put (W, WL, Del_Frame_Of (E, 300, U48 (E) + 10), St);
         end loop;
         Expire (W, WL, 5000, TTL);
         Compact (W, WL);
         Check ("wedge setup: index and log hold the roster only, frontier is full",
                Entries (W) = 1 and then Frames (W) = 1
                and then Log_Length (W) = Prefix_Len + Roster'Length
                and then Kome.Frontier.Count (WL) = 4
                and then Expired_Held (WL, Horizon (W)) = 3);
         Put (W, WL, P8, St);
         Check ("KNOWN LIMITATION (needs Frontier.Remove): expired DELs fill the frontier, No_Space",
                St = No_Space and then Entries (W) = 1);
         Expire (W, WL, 9_000_000, TTL);
         Put (W, WL, P8, St);
         Check ("KNOWN LIMITATION (needs Frontier.Remove): and stays so at any later time",
                St = No_Space and then Kome.Frontier.Count (WL) = 4);
      end;

      --  The invariant, unpacked, on the final store.
      declare
         Ok : Boolean := True;
      begin
         for K in 1 .. Entries (S) loop
            Lemma_Entry_Held (S, SL, K);
            Lemma_Indexed (S, Entry_At (S, K).H);
         end loop;
         for K in 1 .. Kome.Frontier.Count (SL) loop
            if not Expired (Held (SL, K), Horizon (S)) then
               Lemma_Held_Indexed (S, SL, K);
               Ok := Ok and then Indexed (S, Held (SL, K));
            end if;
         end loop;
         Check ("lemmas evaluated; held unexpired records are indexed", Ok);
      end;
   end;

   if Failed then
      Set_Exit_Status (Failure);
   end if;
end Test_Store;
