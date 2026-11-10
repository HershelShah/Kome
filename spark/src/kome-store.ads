--  Kome.Store: the storage model of DESIGN.md §7 after SIMPLIFY.md S7,
--  S14 to S17 and S21. The replica of one collection has two parts:
--    * a lattice state F (Kome.Frontier.State), whose held records each
--      carry a payload tag (S14), and whose ceiling cell, if it holds a
--      roster, carries one too (AUDIT.md H12);
--    * a Store: an append-only log, the identity of the collection, the
--      device's seq_self (S16), the two digest states (S21) and a pin
--      counter.
--  Each operation takes the pair (S, F). Valid (S, F) relates them.
--  There is no index (S14): the tag of a held record packs the place of
--  its frame in the log, Off (40 bits) and Len (24 bits) (Make_Tag,
--  Tag_Off, Tag_Len), and the store reads frames by tag (Read_Frame).
--
--  F is a parameter and not a component of Store, for these reasons:
--    * Frontier.Unchanged is the only comparison of two States. When F is
--      beside the Store, the Store's state stays small;
--    * gnatprove 14 crashed on a Frontier.State record component when
--      Frontier.State had a Dynamic_Predicate (CONVENTIONS.md forbids
--      that predicate).
--  No operation has to restore a state: each finds every refusal before
--  it changes S or F, so a refused call changes neither.
--
--  The log (S15, D9). All integers are big-endian:
--
--    HEADER  "KOME" ‖ version:u8 (= 1) ‖ root_pk[32] ‖ salt[16] ‖ del_ttl:u48
--                                                              (59 bytes)
--    APPLY   01 ‖ len:u24 ‖ frame        a frame that Put_Frame applied
--    SEQ     02 ‖ seq:u48                written by Compact: seq_self
--    CEIL    03 ‖ len:u24 ‖ frame        a ROSTER frame that Put_Frame or
--                                        Put_Ceil recorded in the ceiling
--                                        cell only (AUDIT.md H12)
--
--  The log is HEADER ‖ (APPLY | SEQ | CEIL)*. The HEADER fixes the collection:
--  cid = BLAKE2b-256 (root_pk ‖ salt ‖ u48 (del_ttl)) (Cid_Of, S1), the
--  founding key root_pk (D1) and the tombstone lifetime del_ttl in
--  [Del_TTL_Min, Del_TTL_Max] (S2). There is no slice or data_cap field
--  (S15): Slice_Max is a constant, and the data capacity is a parameter
--  of each open. A frame is tag ‖ content ‖ sig, exactly as Kome.Records
--  encodes it.
--
--  The model of the log is a bounded byte buffer, written only at its
--  end, so an OS file can replace it. The binding flushes the file to
--  Log_Length (the sync point) before a session counts as Complete and
--  before a frame is sent or a bundle is acknowledged (DESIGN.md §8; A4′:
--  a lost log tail is a backup restore). Under Log_Fits (below), a
--  Log_Full result means "compact and retry".
--
--  Order of Put_Frame for a frame whose header is H (D11, E1, E2; §7):
--    (1) H is held already: OK, nothing changes;
--    (2) not admitted: Inadmissible;
--    (3) dominated: Dominated;
--    (4) H is a DEL at or below the horizon hz (F) (it arrives expired,
--        below) and drops no held record: OK, nothing changes (applyH of
--        Lean gives back F);
--    (5) the log has no room for its APPLY: Log_Full;
--    (6) the frontier has no room (Frontier.Apply): No_Space for the data
--        row; for a full slice of the signer or the slot table, Auth_Full,
--        unless H is a ROSTER whose ceiling is above Max_Ceil (F): then
--        the store records it in the ceiling cell (the capture, below)
--        and the result is Ceil_Only;
--    (7) Frontier.Apply holds H with the tag of its new APPLY entry, and
--        the store appends the entry, updates the two digests and
--        seq_self, and then expires (S7): if H raised Max_Ceil or arrived
--        expired, Frontier.Expire (F, hz (F)) removes the DELs at or
--        below the horizon.
--  A refusal changes nothing (T13): the Post says Unchanged (F'Old, F)
--  and S = S'Old. Ceil_Only is not a refusal.
--
--  The ceiling cell (AUDIT.md H12; DESIGN.md §7). Max_Ceil (F) is the
--  larger of the held rosters' ceiling and the ceiling of the cell's
--  roster. A roster reaches the cell in two ways, and in no other: step
--  (6) above, and Put_Ceil, the entry point for the ceiling frame of a
--  peer's HELLO (§8), which never tries the rows. The capture appends the
--  frame as a CEIL entry, calls Frontier.Raise_Ceil with the tag of that
--  entry, and expires at the new horizon. The rows, the two digests and
--  seq_self do not change, apart from the DELs that the expiry removes:
--  the cell's record is not a held record and not an element. So each
--  Put_Frame and each Put_Ceil that does not return Log_Full gives
--    Max_Ceil (after) = max (Max_Ceil (before), Ceil_Of (H))
--  (Ceil_Step, T19), whatever the slices or the slot table refused.
--
--  Expiry (S7, D10, T11): the horizon is a function of F,
--    hz (F) = Max_Ceil (F) - del_ttl   if Max_Ceil (F) >= del_ttl, else none
--  (Lean `hz delTtl H`), and a DEL d is expired when d.t <= hz (F). It is
--  automatic: Put_Frame of a ROSTER that raises Max_Ceil expires in the
--  same call, so Put_Frame is Lean's `applyH delTtl S r := expireHz
--  delTtl (applyD S r)` (Applied_H). No local clock is read, and the log
--  has no expiry entry: replay reruns Put_Frame and reaches the same F.
--  An own write lands at t >= maxceil - Cap_Lead > hz (Kome.Emit, S8), so
--  only a DEL from a writer far behind this replica's maxceil (or one
--  whose cap is below the horizon) arrives expired.
--
--  Digests (S21). The store keeps two Kome.Digest.Digest_State values,
--  one over the authorization rows (Digest_Auth) and one over the data
--  row (Digest_Data). Valid states that they are the states of the held
--  hashes (Kome.Digest.Models over Auth_Hashes (F) and Data_Hashes (F);
--  Lemma_Digests, and Lemma_Digest_Split for Kome.Digest.State_Of (F)).
--  Put_Frame keeps them by diffing: a data apply changes one entity run
--  (Frontier.Outside_Run) and an authorization apply one signer slot
--  (Frontier.Outside_Slot), so the store subtracts the sum of the run or
--  slot before the apply and adds its sum after (Kome.Digest's arithmetic,
--  one Elem_Acc per record of the run or slot). An expiry can remove DELs
--  of many runs, and Frontier.Expire states the survivors as a set, so
--  the data digest is summed again over the data row after an expiry
--  that removes a record (expiry happens only when a ROSTER raises the
--  ceiling past a held DEL, or for a DEL that arrives expired and drops
--  a record).
--
--  seq_self (S16). Seq_Self (S) is the largest seq over the logged APPLY
--  entries whose author is the device key Self_Key (S), and over the SEQ
--  entries; replay rebuilds it from the log, and Compact writes it as a
--  SEQ entry after the copied frames. Valid states that it bounds the seq
--  of every held own record, so a write's seq is above all of them. A
--  frame lost before its APPLY is durable was never sent (A21), so its
--  seq is reusable.
--
--  Replay (S15, T18). Open_From_Log checks the HEADER, starts from
--  Frontier.Empty and reruns every APPLY through the same code as
--  Put_Frame, in trusted mode: it decodes the frame once (Header_Of: one
--  parse and one BLAKE2b) and does not verify the signature. The frames
--  of a store's own log are trusted (Trusted_Frame; DESIGN.md §7 places
--  the integrity of the log with the host); the proof does not use that
--  assumption, and the test main checks it on each log it reopens.
--  A SEQ entry raises seq_self. A CEIL entry reruns the capture through
--  the same code as Put_Ceil; an APPLY that Put_Frame would have captured
--  is refused (a store writes a CEIL for it), and a CEIL that repeats the
--  cell's record is kept and changes nothing. Valid_Length and
--  Replayed_Prefix give the longest prefix that replays (AUDIT.md H23).
--
--  Compaction (S14, S21). Compact writes HEADER ‖ the CEIL of the cell's
--  record, if there is one ‖ one APPLY per held record ‖ SEQ (seq_self).
--  The CEIL is first, so a replay has the cell before the rows. The
--  APPLYs are in row order (the authorization rows, slot
--  by slot, then the data row, entity-major: S18 puts the authorization
--  rows first, so a replay admits every data record). Compact gives each
--  record the tag of its new place (Frontier.Set_Tag, Set_Ceil_Tag). It copies each
--  frame once into the binding's buffer and then copies only the new
--  length back (no whole-capacity copy). It is refused (Busy) while a
--  reconciliation session holds a snapshot of the log (Pinned (S) > 0).
--  It is a store duty of the binding (AUDIT.md H26): it calls Compact when
--  Compact_Due (S, F) holds.
--
--  What is proved (Valid is the store invariant; each operation keeps it):
--    * every held record's tag points at an APPLY entry of the log whose
--      frame has that record as its header (Tag_OK, Lemma_Tag), and the
--      tag of the cell's record points at a CEIL entry whose frame has
--      that record as its header (Lemma_Ceil_Tag);
--    * no held DEL is at or below the horizon (T11 (a), Lemma_No_Expired);
--    * seq_self bounds every held own seq (Lemma_Seq_Self);
--    * the two digest states model the authorization and the data rows
--      (Lemma_Digests);
--    * the HEADER bytes are those of the collection (Lemma_Log_Header);
--    * Put_Frame refines Lean's applyH in the order above; the contract
--      states each refusal as an iff, a refusal changes nothing, the log
--      only grows and the entry is at the returned offset;
--    * the step of T19 (Ceil_Step) for Put_Frame and for Put_Ceil, and
--      what a capture changes (Captured): the CEIL entry, the cell, and
--      the DELs at or below the new horizon; no held authorization record
--      is added or removed, and Put_Ceil changes nothing else;
--    * Compact keeps F's records, the cell's record, the digests and
--      seq_self, gives every record the tag of its copied frame (Valid),
--      puts the CEIL at Header_Len and ends the log with the SEQ entry
--      (Compact_Layout), and the result is not due; the copy order and
--      the absence of gaps are tested, not stated;
--    * Open_From_Log returns a Valid pair whose log is its input.
--  SPARK does not prove that replay accepts every log that a store writes
--  and gives back its frontier and its cell (T18, Lean `auth_first`); the
--  tests test it. The fold of T19 over a delivery is Lean
--  (`maxCeil_order_indep_H`); SPARK proves the step.
pragma Ada_2022;
with Kome.Headers;  use Kome.Headers;
with Kome.Frontier; use Kome.Frontier;
with Kome.Keys;
with Kome.Records;
with Kome.Accumulator;
with Kome.Digest;
package Kome.Store with SPARK_Mode is

   use type Kome.Digest.Digest_State;
   use type Kome.Accumulator.Acc;

   ---------------------------------------------------------------------------
   --  Bounds and the log layout (S15).
   ---------------------------------------------------------------------------

   --  The bound on the log buffer of the model (1 GiB). With this bound,
   --  each offset + entry is a Natural, and an offset fits the 40 bits of
   --  a tag. A file binding keeps this bound.
   Log_Max : constant := 2**30;
   subtype Log_Size is Natural range 0 .. Log_Max;

   Op_Apply : constant Byte := 1;
   Op_Seq   : constant Byte := 2;
   Op_Ceil  : constant Byte := 3;   --  AUDIT.md H12

   Magic_Len   : constant := 4;
   Magic       : constant Byte_Array (0 .. Magic_Len - 1) :=
     [16#4B#, 16#4F#, 16#4D#, 16#45#];   --  "KOME"
   Log_Version : constant Byte := 1;

   --  HEADER field offsets.
   HO_Version : constant := Magic_Len;                --   4
   HO_Root    : constant := HO_Version + 1;           --   5
   HO_Salt    : constant := HO_Root + Pubkey_Len;     --  37
   HO_TTL     : constant := HO_Salt + Salt_Len;       --  53
   Header_Len : constant := HO_TTL + 6;               --  59
   pragma Compile_Time_Error
     (Header_Len /= 59, "SIMPLIFY.md S15: the HEADER is 4 + 1 + 32 + 16 + 6 = 59 bytes");

   Apply_Prefix : constant := 4;   --  01 ‖ len:u24 (APPLY), 03 ‖ len:u24 (CEIL)
   Seq_Len      : constant := 7;   --  02 ‖ seq:u48

   subtype Frame_Size is Positive range 1 .. Kome.Records.Frame_Max;

   --  The largest log entry: the APPLY prefix and the largest frame. (A
   --  CEIL has the layout of an APPLY and holds a ROSTER frame, so it is
   --  at most 4 + 8 916 bytes.)
   Entry_Max : constant := Apply_Prefix + Kome.Records.Frame_Max;   --  41 124
   pragma Compile_Time_Error (Entry_Max /= 41_124, "an APPLY is at most 41 124 bytes");

   --  Compaction as a store duty (AUDIT.md H26): the binding calls Compact
   --  when Compact_Due (S, F) holds, that is, when the log has more than
   --  2 * Count (F) + Compact_Slack entries after the HEADER. A compacted
   --  log (at most one CEIL, one APPLY per held record and one SEQ) is
   --  never due.
   Compact_Slack : constant := 64;

   ---------------------------------------------------------------------------
   --  u24 (the length of an APPLY).
   ---------------------------------------------------------------------------

   subtype U24_Value is Natural range 0 .. 2**24 - 1;
   subtype U24_Lane is Natural range 0 .. 2;

   function Byte_Of_U24 (V : U24_Value; K : U24_Lane) return Byte is
     (Kome.Keys.Byte_Of_Word (Word (V), K + 1));

   function U24_Of (B0, B1, B2 : Byte) return U24_Value is
     (Natural (Kome.Keys.Word_Of (0, B0, B1, B2)));

   procedure Lemma_U24_Round_Trip (V : U24_Value) with
     Ghost, Global => null,
     Post => U24_Of (Byte_Of_U24 (V, 0), Byte_Of_U24 (V, 1), Byte_Of_U24 (V, 2)) = V;

   procedure Lemma_U24_Bytes_Round_Trip (B0, B1, B2 : Byte) with
     Ghost, Global => null,
     Post => Byte_Of_U24 (U24_Of (B0, B1, B2), 0) = B0
       and then Byte_Of_U24 (U24_Of (B0, B1, B2), 1) = B1
       and then Byte_Of_U24 (U24_Of (B0, B1, B2), 2) = B2;

   ---------------------------------------------------------------------------
   --  Tags (S14): the place of a held record's frame in the log.
   ---------------------------------------------------------------------------

   --  Off in the high 40 bits, Len in the low 24 bits. Off is the offset
   --  of the APPLY entry (of the CEIL entry, for the tag of the ceiling
   --  cell); the frame starts at Off + Apply_Prefix.
   function Make_Tag (Off : Log_Size; Len : Frame_Size) return U64 is
     (U64 (Off) * 2**24 + U64 (Len));

   function Tag_Off (T : U64) return Natural is
     (if T / 2**24 <= U64 (Log_Max) then Natural (T / 2**24) else Log_Max + 1);

   function Tag_Len (T : U64) return U24_Value is (Natural (T mod 2**24));

   procedure Lemma_Tag_Round_Trip (Off : Log_Size; Len : Frame_Size) with
     Ghost, Global => null,
     Post => Tag_Off (Make_Tag (Off, Len)) = Off and then Tag_Len (Make_Tag (Off, Len)) = Len;

   ---------------------------------------------------------------------------
   --  Frames and their headers (the wire boundary, Kome.Records).
   ---------------------------------------------------------------------------

   --  Frame is the encoding of one record of the kind that its tag names.
   function Is_Record_Frame (Frame : Byte_Array) return Boolean is
     (Kome.Records.Has_Kind (Frame)
      and then (case Kome.Records.Kind_Of (Frame) is
                  when K_Put    => Kome.Records.Is_Put_Frame (Frame),
                  when K_Del    => Kome.Records.Is_Del_Frame (Frame),
                  when K_Roster => Kome.Records.Is_Roster_Frame (Frame),
                  when K_Revoke => Kome.Records.Is_Revoke_Frame (Frame),
                  when K_Grant  => Kome.Records.Is_Grant_Frame (Frame)));

   --  Frame is a well-formed record of the collection (Cid, Root_PK):
   --  exactly what Kome.Records.Decode_Verified accepts for its kind
   --  (DESIGN.md §2 items 1-5, S1, S3). A store passes its own Cid (S) and
   --  Root_Key (S).
   function Verified (Cid : Hash256; Root_PK : Pubkey; Frame : Byte_Array) return Boolean is
     (Is_Record_Frame (Frame)
      and then (case Kome.Records.Kind_Of (Frame) is
                  when K_Put    =>
                    Kome.Records.Well_Formed (Cid, Kome.Records.Parse_Put (Frame)),
                  when K_Del    =>
                    Kome.Records.Well_Formed (Cid, Kome.Records.Parse_Del (Frame)),
                  when K_Roster =>
                    Kome.Records.Well_Formed (Cid, Root_PK, Kome.Records.Parse_Roster (Frame)),
                  when K_Revoke =>
                    Kome.Records.Well_Formed (Cid, Root_PK, Kome.Records.Parse_Revoke (Frame)),
                  when K_Grant  =>
                    Kome.Records.Well_Formed (Cid, Root_PK, Kome.Records.Parse_Grant (Frame))));

   --  The assumption of trusted replay (S15): a frame of the store's own
   --  log is one that Put_Frame verified when it arrived. The host keeps
   --  the log intact (DESIGN.md §7). Replay does not check it and the
   --  proof does not use it; the test main checks it on each log it
   --  reopens.
   function Trusted_Frame (Cid : Hash256; Root_PK : Pubkey; Frame : Byte_Array) return Boolean
   is (Verified (Cid, Root_PK, Frame))
   with Ghost;

   --  The lattice header of a record frame in the collection of Cid
   --  (Kome.Records.To_Header of the parse result; h is under Cid).
   --  Lemma_Header_Of gives the full definition. Computing it parses the
   --  frame once and hashes its content once.
   function Header_Of (Cid : Hash256; Frame : Byte_Array) return Header with
     Global => null,
     Pre    => Is_Record_Frame (Frame);

   procedure Lemma_Header_Of (Cid : Hash256; Frame : Byte_Array) with
     Ghost, Global => null,
     Pre  => Is_Record_Frame (Frame),
     Post => Header_Of (Cid, Frame).K = Kome.Records.Kind_Of (Frame)
       and then Header_Of (Cid, Frame) =
               (case Kome.Records.Kind_Of (Frame) is
                  when K_Put    =>
                    Kome.Records.To_Header (Cid, Kome.Records.Parse_Put (Frame)),
                  when K_Del    =>
                    Kome.Records.To_Header (Cid, Kome.Records.Parse_Del (Frame)),
                  when K_Roster =>
                    Kome.Records.To_Header (Cid, Kome.Records.Parse_Roster (Frame)),
                  when K_Revoke =>
                    Kome.Records.To_Header (Cid, Kome.Records.Parse_Revoke (Frame)),
                  when K_Grant  =>
                    Kome.Records.To_Header (Cid, Kome.Records.Parse_Grant (Frame)));

   --  The header of a verified frame is canonical (D3; Kome.Records
   --  Lemma_Header_Canonical; a ROSTER's gen <= ceiling_t is part of
   --  Well_Formed).
   procedure Lemma_Verified_Canonical (Cid : Hash256; Root_PK : Pubkey; Frame : Byte_Array)
   with
     Ghost, Global => null,
     Pre  => Verified (Cid, Root_PK, Frame),
     Post => Canonical (Header_Of (Cid, Frame))
             and then Header_Of (Cid, Frame).K = Kome.Records.Kind_Of (Frame);

   --  Two byte strings with the same elements are frames of the same
   --  record (the bounds may differ). gnatprove has no extensionality for
   --  arrays; this is the congruence that carries a header across a copy
   --  of a frame (into the log, by Compact, by Read_Frame), from
   --  Kome.Crypto.Lemma_Blake2b_Congruent.
   procedure Lemma_Header_Of_Congruent (Cid : Hash256; A, B : Byte_Array) with
     Ghost, Global => null,
     Pre  => Is_Record_Frame (A)
             and then A'Length = B'Length
             and then (for all J in A'Range => B (J - A'First + B'First) = A (J)),
     Post => Is_Record_Frame (B) and then Header_Of (Cid, A) = Header_Of (Cid, B);

   ---------------------------------------------------------------------------
   --  Expiry (S7): the horizon is a function of F.
   ---------------------------------------------------------------------------

   --  hz (F) exists (Lean `hz delTtl H = some (maxCeil H - delTtl)`).
   function Has_Hz (F : Frontier.State; TTL : U48) return Boolean is
     (Max_Ceil (F) >= TTL);

   function Hz (F : Frontier.State; TTL : U48) return U48 is
     (Max_Ceil (F) - TTL)
     with Pre => Has_Hz (F, TTL);

   --  X is a DEL at or below the horizon of F.
   function Expired_In (X : Header; F : Frontier.State; TTL : U48) return Boolean is
     (Has_Hz (F, TTL) and then Expired (X, Hz (F, TTL)));

   ---------------------------------------------------------------------------
   --  The store.
   ---------------------------------------------------------------------------

   --  Log_Cap bytes of log (S15: no index, no entry boundaries, no slice).
   type Store (Log_Cap : Log_Size) is private;

   function Founding (S : Store) return Key256 with Global => null;
   function Root_Key (S : Store) return Pubkey with Global => null;
   function Salt_Of (S : Store) return Salt with Global => null;
   --  del_ttl, fixed at founding (S2; Lean `delTtl`).
   function Del_TTL (S : Store) return U48 with Global => null;
   --  cid = Cid_Of (root_pk, salt, del_ttl) (S1), computed once by Open
   --  and Open_From_Log. The store applies every frame under it, and
   --  Kome.Write signs under it.
   function Cid (S : Store) return Hash256 with Global => null;
   --  The device key whose seq the store tracks (S16).
   function Self_Key (S : Store) return Key256 with Global => null;
   function Seq_Self (S : Store) return U48 with Global => null;
   --  The digest states of the authorization rows and of the data row
   --  (S21). Kome.Reconcile.Start takes them.
   function Digest_Auth (S : Store) return Kome.Digest.Digest_State with Global => null;
   function Digest_Data (S : Store) return Kome.Digest.Digest_State with Global => null;
   --  The number of reconciliation sessions that hold a snapshot of the
   --  log (S21). Compact is refused while it is positive.
   function Pinned (S : Store) return Natural with Global => null;

   function Log_Length (S : Store) return Log_Size with
     Global => null,
     Post => Log_Length'Result <= S.Log_Cap;
   function Log_Byte (S : Store; J : Natural) return Byte with
     Global => null,
     Pre => J < Log_Length (S);
   --  The number of APPLY, SEQ and CEIL entries after the HEADER.
   function Log_Entries (S : Store) return Natural with
     Global => null,
     Post => Log_Entries'Result <= Log_Max;

   --  The log is due for compaction (AUDIT.md H26; see Compact_Slack).
   function Compact_Due (S : Store; F : Frontier.State) return Boolean is
     (Log_Entries (S) > 2 * Count (F) + Compact_Slack);

   --  The hashes of the held records, row by row (ghost): the data row,
   --  and the authorization rows in flat order. The digests model them.
   function Data_Hashes (F : Frontier.State) return Kome.Digest.Hash_Array with
     Ghost, Global => null,
     Post => Data_Hashes'Result'First = 1
       and then Data_Hashes'Result'Last = Data_Count (F)
       and then (for all I in 1 .. Data_Count (F) =>
                   Data_Hashes'Result (I) = Data_Held (F, I).V.H);

   function Auth_Hashes (F : Frontier.State) return Kome.Digest.Hash_Array with
     Ghost, Global => null,
     Post => Auth_Hashes'Result'First = 1
       and then Auth_Hashes'Result'Last = Auth_Count (F)
       and then (for all I in 1 .. Auth_Count (F) =>
                   Auth_Hashes'Result (I) = Held (F, Data_Count (F) + I).V.H);

   --  The store invariant. It relates the store to its lattice state F
   --  (see the package comment). Opaque: use the lemmas below to read it.
   function Valid (S : Store; F : Frontier.State) return Boolean with Ghost, Global => null;

   --  The identity of a store: collection, founding key, del_ttl, device
   --  key. Every operation keeps it.
   function Same_Identity (Old_S, New_S : Store) return Boolean is
     (Founding (New_S) = Founding (Old_S)
      and then Root_Key (New_S) = Root_Key (Old_S)
      and then Salt_Of (New_S) = Salt_Of (Old_S)
      and then Del_TTL (New_S) = Del_TTL (Old_S)
      and then Cid (New_S) = Cid (Old_S)
      and then Self_Key (New_S) = Self_Key (Old_S));

   ---------------------------------------------------------------------------
   --  The log as a file.
   ---------------------------------------------------------------------------

   function Op_At (S : Store; P : Natural) return Byte is (Log_Byte (S, P))
     with Pre => P < Log_Length (S);

   --  The len:u24 of the APPLY or CEIL entry at P.
   function Len_At (S : Store; P : Natural) return U24_Value is
     (U24_Of (Log_Byte (S, P + 1), Log_Byte (S, P + 2), Log_Byte (S, P + 3)))
     with Pre => P < Log_Length (S) and then Log_Length (S) - P >= Apply_Prefix;

   --  The u48 at P (a SEQ's value is at its offset + 1).
   function Code_At (S : Store; P : Natural) return U48 is
     (Kome.Records.U48_Of (Log_Byte (S, P), Log_Byte (S, P + 1), Log_Byte (S, P + 2),
                           Log_Byte (S, P + 3), Log_Byte (S, P + 4), Log_Byte (S, P + 5)))
     with Pre => P < Log_Length (S) and then Log_Length (S) - P >= 6;

   --  A whole APPLY or CEIL entry starts at P.
   function Has_Frame (S : Store; P : Natural) return Boolean is
     (P < Log_Length (S)
      and then Log_Length (S) - P >= Apply_Prefix
      and then Op_At (S, P) in Op_Apply | Op_Ceil
      and then Len_At (S, P) in Frame_Size
      and then Len_At (S, P) <= Log_Length (S) - P - Apply_Prefix);

   --  The frame of the APPLY or CEIL entry at Off (indexed from 0).
   function Read_Frame (S : Store; Off : Natural) return Byte_Array with
     Global => null,
     Pre  => Has_Frame (S, Off),
     Post => Read_Frame'Result'First = 0
       and then Read_Frame'Result'Length = Len_At (S, Off)
       and then (for all K in Read_Frame'Result'Range =>
                   Read_Frame'Result (K) = Log_Byte (S, Off + Apply_Prefix + K));

   --  The file image of the log.
   function Log_Bytes (S : Store) return Byte_Array with
     Global => null,
     Post => Log_Bytes'Result'First = 0
       and then Log_Bytes'Result'Length = Log_Length (S)
       and then (for all J in Log_Bytes'Result'Range => Log_Bytes'Result (J) = Log_Byte (S, J));

   ---------------------------------------------------------------------------
   --  Named parts of the contracts of the operations.
   ---------------------------------------------------------------------------

   --  The room rules of Frontier.Apply, copied from its Post: the data row
   --  is full and R frees nothing (No_Space) ...
   function Data_Full (F : Frontier.State; R : Header) return Boolean is
     (Is_Data (R) and then Data_Count (F) = F.Cap and then not Drops_Any (F, R));

   --  ... and the authorization rules (Auth_Full): the slice of the signer
   --  is full and R frees nothing; or the signer is new and all slots are
   --  used.
   function Auth_Rule (F : Frontier.State; R : Header) return Boolean is
     (Is_Auth (R)
      and then ((Slot_Of (F, R.Issuer) /= 0
                 and then Slot_Count (F, Slot_Of (F, R.Issuer)) = Slice_Max
                 and then not Drops_Any (F, R))
                or else (Slot_Of (F, R.Issuer) = 0 and then Slots_Used (F) = Signers_Max)));

   --  The capture rule of Put_Frame (AUDIT.md H12): a roster that the
   --  authorization rows refuse for room and whose ceiling is above maxceil.
   function Ceil_Rule (F : Frontier.State; R : Header) return Boolean is
     (Auth_Rule (F, R) and then Raises_Ceil (F, R));

   --  Fewer than Need bytes of log are left.
   function Log_Short (S : Store; Need : Natural) return Boolean is
     (S.Log_Cap - Log_Length (S) < Need);

   --  Put_Frame of H changes the pair: H is admitted, not held, not
   --  dominated, and not a DEL that arrives expired and drops nothing.
   function Effective (F : Frontier.State; TTL : U48; H : Header) return Boolean is
     (Admitted (F, H) and then not Holds (F, H) and then not Dom (F, H)
      and then (if Expired_In (H, F, TTL) then Drops_Any (F, H)));

   --  Log bytes are a capacity class shared by every record (DESIGN.md §7,
   --  E1; AUDIT.md H3). Under Log_Fits, a compacted log (the HEADER, at
   --  most one CEIL, one APPLY per held record, one SEQ) has room for one
   --  more entry of any kind, so Log_Full only ever means "compact first",
   --  and no flood of large values can block the founding REVOKE. The
   --  binding checks it when it chooses Log_Cap for a data capacity Cap.
   --  It is stated as a quotient so that it never overflows.
   function Log_Fits (Cap : Data_Size; Log_Cap : Log_Size) return Boolean is
     (Log_Cap >= Header_Len + Seq_Len
      and then (Log_Cap - Header_Len - Seq_Len) / Entry_Max
               >= Cap + Signers_Max * Slice_Max + 2);

   --  Lean `applyH delTtl S r := expireHz delTtl (applyD S r)` (S7): the
   --  views grow exactly by H; each held record was held before or is H,
   --  and none is expired at the new horizon; a record leaves only by
   --  domination by H or by expiry; H is held unless it is itself expired.
   function Applied_H (Old_F, New_F : Frontier.State; H : Header; TTL : U48) return Boolean is
     (Max_Ceil (New_F) = U48'Max (Max_Ceil (Old_F), Ceil_Of (H))
      and then (Holds (New_F, H) or else Expired_In (H, New_F, TTL))
      and then (for all I in 1 .. Count (New_F) =>
                  (Holds (Old_F, Held (New_F, I)) or else Held (New_F, I) = H)
                  and then not Expired_In (Held (New_F, I), New_F, TTL))
      and then (for all I in 1 .. Count (Old_F) =>
                  Holds (New_F, Held (Old_F, I)) or else Dominates (H, Held (Old_F, I))
                  or else Expired_In (Held (Old_F, I), New_F, TTL)));

   --  The log of New_S extends the log of Old_S: no written byte changes.
   function Log_Extends (Old_S, New_S : Store) return Boolean is
     (Log_Length (New_S) >= Log_Length (Old_S)
      and then Log_Entries (New_S) >= Log_Entries (Old_S)
      and then (for all J in 0 .. Log_Length (Old_S) - 1 =>
                  Log_Byte (New_S, J) = Log_Byte (Old_S, J)));

   --  APPLY (Frame) was appended at Off, as the new last entry.
   function Appended (Old_S, New_S : Store; Frame : Byte_Array; Off : Natural) return Boolean is
     (Off = Log_Length (Old_S)
      and then Log_Length (New_S) >= Off
      and then Log_Length (New_S) - Off = Apply_Prefix + Frame'Length
      and then Log_Entries (New_S) = Log_Entries (Old_S) + 1
      and then Op_At (New_S, Off) = Op_Apply
      and then Len_At (New_S, Off) = Frame'Length
      and then (for all J in Frame'Range =>
                  Log_Byte (New_S, J - Frame'First + (Off + Apply_Prefix)) = Frame (J)))
     with Pre => Frame'Length in Frame_Size;

   --  seq_self after an APPLY of H was logged (S16).
   function Seq_After (S : Store; H : Header) return U48 is
     (if Is_Data (H) and then H.V.Author = Self_Key (S)
      then U48'Max (Seq_Self (S), H.V.Seq) else Seq_Self (S));

   --  CEIL (Frame) was appended at Off, as the new last entry.
   function Ceil_Appended (Old_S, New_S : Store; Frame : Byte_Array; Off : Natural) return Boolean
   is (Off = Log_Length (Old_S)
       and then Log_Length (New_S) >= Off
       and then Log_Length (New_S) - Off = Apply_Prefix + Frame'Length
       and then Log_Entries (New_S) = Log_Entries (Old_S) + 1
       and then Op_At (New_S, Off) = Op_Ceil
       and then Len_At (New_S, Off) = Frame'Length
       and then (for all J in Frame'Range =>
                   Log_Byte (New_S, J - Frame'First + (Off + Apply_Prefix)) = Frame (J)))
     with Pre => Frame'Length in Frame_Size;

   --  A capture: the cell holds H, maxceil is H's ceiling, and the held
   --  records are the old ones without the DELs at or below the new horizon.
   --  (So every held authorization record stays, and none is added.)
   function Ceiled (Old_F, New_F : Frontier.State; H : Header; TTL : U48) return Boolean is
     (Max_Ceil (New_F) = Ceil_Of (H)
      and then Has_Ceil (New_F) and then Ceil_Held (New_F) = H
      and then (for all I in 1 .. Count (New_F) =>
                  Holds (Old_F, Held (New_F, I))
                  and then not Expired_In (Held (New_F, I), New_F, TTL))
      and then (for all I in 1 .. Count (Old_F) =>
                  Holds (New_F, Held (Old_F, I))
                  or else Expired_In (Held (Old_F, I), New_F, TTL)));

   --  What a capture did to the pair (Put_Frame with Ceil_Only, Put_Ceil
   --  with Ceil_Only).
   function Captured
     (Old_S, S : Store; Old_F, F : Frontier.State; Frame : Byte_Array; H : Header;
      Off : Natural) return Boolean
   is (Ceil_Appended (Old_S, S, Frame, Off)
       and then Ceiled (Old_F, F, H, Del_TTL (S))
       and then Ceil_Tag (F) = Make_Tag (Off, Frame'Length)
       and then Seq_Self (S) = Seq_Self (Old_S)
       and then Digest_Auth (S) = Digest_Auth (Old_S))
   with Ghost, Pre => Frame'Length in Frame_Size;

   --  T19, the step: unless the log was full, maxceil is the old maxceil
   --  joined with the ceiling of H, whatever the rows refused.
   function Ceil_Step (Old_F, F : Frontier.State; H : Header; Result : Status) return Boolean is
     (if Result /= Log_Full then Max_Ceil (F) = U48'Max (Max_Ceil (Old_F), Ceil_Of (H)));

   --  The contract of Put_Frame (Kome.Write.Receive states it too). The
   --  top-level conjuncts use "and" (each conjunct guards its own
   --  preconditions); the functions above name the long conjuncts.
   function Put_Done
     (Old_S, S : Store; Old_F, F : Frontier.State; Frame : Byte_Array; H : Header;
      Off : Natural; Result : Status) return Boolean
   is (Valid (S, F)
       and Same_Identity (Old_S, S)
       and Pinned (S) = Pinned (Old_S)
       and Off = Log_Length (Old_S)
       and Log_Extends (Old_S, S)
       and Result in OK | Dominated | Inadmissible | No_Space | Auth_Full | Log_Full
                     | Ceil_Only
       --  The order of DESIGN.md §7, each outcome as an iff.
       and (Result = Inadmissible) = (not Admitted (Old_F, H))
       and (Result = Dominated)
             = (Admitted (Old_F, H) and then not Holds (Old_F, H) and then Dom (Old_F, H))
       and (Result = Log_Full)
             = (Effective (Old_F, Del_TTL (Old_S), H)
                and then Log_Short (Old_S, Apply_Prefix + Frame'Length))
       and (Result = No_Space)
             = (Effective (Old_F, Del_TTL (Old_S), H)
                and then not Log_Short (Old_S, Apply_Prefix + Frame'Length)
                and then Data_Full (Old_F, H))
       and (Result = Auth_Full)
             = (Effective (Old_F, Del_TTL (Old_S), H)
                and then not Log_Short (Old_S, Apply_Prefix + Frame'Length)
                and then Auth_Rule (Old_F, H)
                and then not Raises_Ceil (Old_F, H))
       --  The capture (AUDIT.md H12).
       and (Result = Ceil_Only)
             = (Effective (Old_F, Del_TTL (Old_S), H)
                and then not Log_Short (Old_S, Apply_Prefix + Frame'Length)
                and then Ceil_Rule (Old_F, H))
       --  Nothing changes on a refusal, on a duplicate, or for an expired
       --  DEL that drops nothing (T13).
       and (if Result not in OK | Ceil_Only
              or else not Effective (Old_F, Del_TTL (Old_S), H)
            then Unchanged (Old_F, F) and then S = Old_S)
       --  OK and effective: Lean's applyH, the APPLY entry at Off, the
       --  tag of H, and seq_self (S16).
       and (if Result = OK and then Effective (Old_F, Del_TTL (Old_S), H) then
              Appended (Old_S, S, Frame, Off)
              and then Applied_H (Old_F, F, H, Del_TTL (S))
              and then (if Holds (F, H) then Tag_Of (F, H) = Make_Tag (Off, Frame'Length))
              and then Seq_Self (S) = Seq_After (Old_S, H))
       --  Ceil_Only: the CEIL entry at Off, the cell, the expiry.
       and (if Result = Ceil_Only then Captured (Old_S, S, Old_F, F, Frame, H, Off))
       --  T19, the step.
       and Ceil_Step (Old_F, F, H, Result))
   with Ghost, Pre => Frame'Length in Frame_Size;

   --  The contract of Put_Ceil.
   function Ceil_Done
     (Old_S, S : Store; Old_F, F : Frontier.State; Frame : Byte_Array; H : Header;
      Off : Natural; Result : Status) return Boolean
   is (Valid (S, F)
       and Same_Identity (Old_S, S)
       and Pinned (S) = Pinned (Old_S)
       and Off = Log_Length (Old_S)
       and Log_Extends (Old_S, S)
       and Result in OK | Ceil_Only | Log_Full
       and (Result = Ceil_Only)
             = (Raises_Ceil (Old_F, H)
                and then not Log_Short (Old_S, Apply_Prefix + Frame'Length))
       and (Result = Log_Full)
             = (Raises_Ceil (Old_F, H)
                and then Log_Short (Old_S, Apply_Prefix + Frame'Length))
       and (if Result /= Ceil_Only then Unchanged (Old_F, F) and then S = Old_S)
       and (if Result = Ceil_Only then Captured (Old_S, S, Old_F, F, Frame, H, Off))
       and Ceil_Step (Old_F, F, H, Result))
   with Ghost, Pre => Frame'Length in Frame_Size;

   ---------------------------------------------------------------------------
   --  Operations.
   ---------------------------------------------------------------------------

   --  A new store for the collection of (Root_PK, Salt, Del_TTL), beside
   --  the empty lattice state F (Frontier.Empty (To_Key256 (Root_PK),
   --  Cap)), for the device key Self_PK. It writes the HEADER and computes
   --  the cid once. Del_TTL is in [Del_TTL_Min, Del_TTL_Max] (S2), and the
   --  founding key is a usable signing key (Sign_Key_OK; AUDIT.md H13,
   --  A27).
   procedure Open
     (Root_PK : Pubkey;
      Salt    : Kome.Salt;
      Del_TTL : U48;
      Self_PK : Pubkey;
      F       : Frontier.State;
      S       : out Store)
   with
     Global => null,
     Pre  => Is_Frontier (F)
       and then Count (F) = 0
       and then not Has_Ceil (F)
       and then Kome.Keys.To_Key256 (Root_PK) = Frontier.Founding (F)
       and then Del_TTL in Del_TTL_Min .. Del_TTL_Max
       and then S.Log_Cap >= Header_Len
       and then Kome.Records.Sign_Key_OK (Root_PK),
     Post => Valid (S, F)
       and then Founding (S) = Frontier.Founding (F)
       and then Root_Key (S) = Root_PK
       and then Salt_Of (S) = Salt
       and then Kome.Store.Del_TTL (S) = Del_TTL
       and then Cid (S) = Kome.Records.Cid_Of (Root_PK, Salt, Del_TTL)
       and then Self_Key (S) = Kome.Keys.To_Key256 (Self_PK)
       and then Seq_Self (S) = 0
       and then Pinned (S) = 0
       and then Log_Length (S) = Header_Len
       and then Log_Entries (S) = 0;

   --  Apply one frame from a peer, or one that Kome.Write built and
   --  checked, and store it (DESIGN.md §7, the steps above). Before the
   --  call, the caller decodes and verifies Frame (Verified, what
   --  Kome.Records.Decode_Verified accepts) and gives its header H. Off is
   --  always the log length before the call: the offset of the appended
   --  entry, if the call appended one (AUDIT.md G22).
   procedure Put_Frame
     (S      : in out Store;
      F      : in out Frontier.State;
      Frame  : in     Byte_Array;
      H      : in     Header;
      Off    :    out Log_Size;
      Result :    out Status)
   with
     Global => null,
     Pre  => Valid (S, F)
       and then Frame'Length in Frame_Size
       and then Verified (Cid (S), Root_Key (S), Frame)
       and then Header_Of (Cid (S), Frame) = H,
     Post => Put_Done (S'Old, S, F'Old, F, Frame, H, Off, Result);

   --  Record the ceiling of the roster frame that a peer sent as the `ceil`
   --  of its HELLO (DESIGN.md §8; AUDIT.md H12). If the roster's ceiling is
   --  above maxceil, the frame goes to the ceiling cell (a CEIL entry) and
   --  the store expires at the new horizon: Ceil_Only. Otherwise nothing
   --  changes: OK. The roster never enters a row here, whatever room its
   --  signer's slice has: ROSTER_eff, the gate and the quarantine of this
   --  replica do not change. Before the call, the caller decodes and
   --  verifies Frame as a ROSTER and gives its header H. Off is the log
   --  length before the call.
   procedure Put_Ceil
     (S      : in out Store;
      F      : in out Frontier.State;
      Frame  : in     Byte_Array;
      H      : in     Header;
      Off    :    out Log_Size;
      Result :    out Status)
   with
     Global => null,
     Pre  => Valid (S, F)
       and then Frame'Length in Frame_Size
       and then Verified (Cid (S), Root_Key (S), Frame)
       and then Header_Of (Cid (S), Frame) = H
       and then H.K = K_Roster,
     Post => Ceil_Done (S'Old, S, F'Old, F, Frame, H, Off, Result);

   --  Compact the log (S14, S15, S16): HEADER ‖ the CEIL of the cell's
   --  record, if Has_Ceil (F) ‖ one APPLY per held record
   --  in row order (the authorization rows slot by slot, then the data
   --  row) ‖ SEQ (Seq_Self (S)). Each record gets the tag of its new place
   --  (Frontier.Set_Tag, Set_Ceil_Tag); nothing else of F changes. A cell
   --  whose ceiling a held roster has reached is kept (nothing clears the
   --  cell). Compact builds the new
   --  log in Buf, the binding's buffer for the new file (it reads the old
   --  log in place), and copies only the new length back into the store.
   --  On OK, Buf (0 .. Log_Length (S) - 1) is the image of the new file,
   --  which the binding writes and renames over the old one.
   --    Busy      a reconciliation session holds a snapshot (Pinned).
   --    Log_Full  the compacted log does not fit Log_Cap. This does not
   --              happen: the held frames are disjoint parts of the old log
   --              (tested, not proved; the check makes it a refusal).
   procedure Compact
     (S      : in out Store;
      F      : in out Frontier.State;
      Buf    : in out Byte_Array;
      Result :    out Status)
   with
     Global => null,
     Pre  => Valid (S, F) and then Buf'First = 0 and then Buf'Last = S.Log_Cap,
     Post => Valid (S, F)
       and Same_Identity (S'Old, S)
       and Pinned (S) = Pinned (S'Old)
       and Seq_Self (S) = Seq_Self (S'Old)
       and Digest_Auth (S) = Digest_Auth (S'Old)
       and Digest_Data (S) = Digest_Data (S'Old)
       and Result in OK | Busy | Log_Full
       and (Result = Busy) = (Pinned (S'Old) > 0)
       and (if Result /= OK then Unchanged (F'Old, F) and then S = S'Old)
       and (if Result = OK then
              Retagged (F'Old, F)
              and then Compact_Layout (S'Old, F'Old, S, F)
              --  AUDIT.md H26: a compacted log is never due.
              and then not Compact_Due (S, F)
              --  The new file image (AUDIT.md G15).
              and then (for all J in 0 .. Log_Length (S) - 1 => Buf (J) = Log_Byte (S, J)));

   --  F differs from Old_F only in its tags (Compact). Ghost; its Post
   --  defines it.
   function Retagged (Old_F, F : Frontier.State) return Boolean with
     Ghost, Global => null,
     Post => Retagged'Result =
       (Is_Frontier (F)
        and then Frontier.Founding (F) = Frontier.Founding (Old_F)
        and then Max_Ceil (F) = Max_Ceil (Old_F)
        and then Data_Count (F) = Data_Count (Old_F)
        and then Auth_Count (F) = Auth_Count (Old_F)
        and then Count (F) = Count (Old_F)
        and then (for all J in 1 .. Data_Count (F) => Data_Held (F, J) = Data_Held (Old_F, J))
        and then (for all J in 1 .. Count (F) =>
                    Held (F, J) = Held (Old_F, J)
                    and then Tag_Len (Tag (F, J)) = Tag_Len (Tag (Old_F, J)))
        and then Has_Ceil (F) = Has_Ceil (Old_F)
        and then (if Has_Ceil (F)
                  then Ceil_Held (F) = Ceil_Held (Old_F)
                       and then Tag_Len (Ceil_Tag (F)) = Tag_Len (Ceil_Tag (Old_F))));

   --  The copy order of Compact: authorization rows first (flat indices
   --  Data_Count + 1 .. Count), then the data row (1 .. Data_Count). Ord
   --  gives the flat index of the C-th record written.
   function Ord (F : Frontier.State; C : Positive) return Positive is
     (if C <= Auth_Count (F) then Data_Count (F) + C else C - Auth_Count (F))
     with Pre => C <= Count (F);

   --  The offset just after the APPLY of a tag.
   function Tag_End (T : U64) return Natural is
     (Tag_Off (T) + Apply_Prefix + Tag_Len (T));

   --  The layout clause of Compact (ghost; its Post defines it): the
   --  HEADER bytes of the old log; the CEIL of the cell's record, if there
   --  is one, right after the HEADER; every record's APPLY before the SEQ
   --  (seq_self) that ends the log; exactly Count + 1 entries, and one more
   --  with a cell. That each tag holds its record's frame is Valid
   --  (Lemma_Tag, Lemma_Ceil_Tag); Compact writes the APPLYs in copy order
   --  (Ord) with no gaps (tested, not stated).
   function Compact_Layout (Old_S : Store; Old_F : Frontier.State; S : Store; F : Frontier.State)
     return Boolean
   with
     Ghost, Global => null,
     Pre  => Count (F) = Count (Old_F),
     Post => Compact_Layout'Result =
       (Log_Length (S) >= Header_Len + Seq_Len
        and then Log_Length (Old_S) >= Header_Len
        and then (for all K in 0 .. Header_Len - 1 => Log_Byte (S, K) = Log_Byte (Old_S, K))
        and then (for all J in 1 .. Count (F) =>
                    Tag_End (Tag (F, J)) <= Log_Length (S) - Seq_Len
                    and then Tag_Len (Tag (F, J)) = Tag_Len (Tag (Old_F, J)))
        and then Op_At (S, Log_Length (S) - Seq_Len) = Op_Seq
        and then Code_At (S, Log_Length (S) - Seq_Len + 1) = Seq_Self (S)
        and then Log_Entries (S) = Count (F) + 1 + (if Has_Ceil (F) then 1 else 0)
        and then (if Has_Ceil (F)
                  then Tag_Off (Ceil_Tag (F)) = Header_Len
                       and then Tag_End (Ceil_Tag (F)) <= Log_Length (S) - Seq_Len));

   --  A reconciliation session takes (Pin) and releases (Unpin) a snapshot
   --  of the log (S21). Nothing else changes.
   procedure Pin (S : in out Store; F : Frontier.State) with
     Global => null,
     Pre  => Valid (S, F) and then Pinned (S) < Natural'Last,
     Post => Valid (S, F)
       and then Pinned (S) = Pinned (S'Old) + 1
       and then Same_Identity (S'Old, S)
       and then Seq_Self (S) = Seq_Self (S'Old)
       and then Digest_Auth (S) = Digest_Auth (S'Old)
       and then Digest_Data (S) = Digest_Data (S'Old)
       and then Log_Length (S) = Log_Length (S'Old)
       and then Log_Entries (S) = Log_Entries (S'Old)
       and then (for all J in 0 .. Log_Length (S) - 1 => Log_Byte (S, J) = Log_Byte (S'Old, J));

   procedure Unpin (S : in out Store; F : Frontier.State) with
     Global => null,
     Pre  => Valid (S, F) and then Pinned (S) > 0,
     Post => Valid (S, F)
       and then Pinned (S) = Pinned (S'Old) - 1
       and then Same_Identity (S'Old, S)
       and then Seq_Self (S) = Seq_Self (S'Old)
       and then Digest_Auth (S) = Digest_Auth (S'Old)
       and then Digest_Data (S) = Digest_Data (S'Old)
       and then Log_Length (S) = Log_Length (S'Old)
       and then Log_Entries (S) = Log_Entries (S'Old)
       and then (for all J in 0 .. Log_Length (S) - 1 => Log_Byte (S, J) = Log_Byte (S'Old, J));

   --  The del_ttl that the HEADER of a log records.
   function Header_TTL (Input : Byte_Array) return U48 is
     (Kome.Records.U48_Of (Input (HO_TTL), Input (HO_TTL + 1), Input (HO_TTL + 2),
                           Input (HO_TTL + 3), Input (HO_TTL + 4), Input (HO_TTL + 5)))
     with Pre => Input'First = 0 and then Input'Last >= Header_Len - 1;

   --  Input starts with a HEADER: its magic and version, a usable founding
   --  key (Sign_Key_OK, as Open requires) and a del_ttl in [Del_TTL_Min,
   --  Del_TTL_Max] (S2). These are the checks that Open_From_Log does on
   --  the bytes of the HEADER.
   function Header_Well_Formed (Input : Byte_Array) return Boolean is
     (Input'Last >= Header_Len - 1
      and then Input (0 .. Magic_Len - 1) = Magic
      and then Input (HO_Version) = Log_Version
      and then Kome.Records.Sign_Key_OK (Input (HO_Root .. HO_Root + Pubkey_Len - 1))
      and then Header_TTL (Input) in Del_TTL_Min .. Del_TTL_Max)
     with Pre => Input'First = 0;

   --  The T18-prefix clause of Open_From_Log (AUDIT.md H23): (S, F) is a
   --  Valid pair, its log is the first VL bytes of Input, and its identity
   --  is the HEADER of Input. Its Post defines it (one atom in the
   --  contract of Open_From_Log).
   function Replayed_Prefix
     (Input : Byte_Array; Self_PK : Pubkey; F : Frontier.State; S : Store; VL : Log_Size)
     return Boolean
   with
     Ghost, Global => null,
     Pre  => Input'First = 0,
     Post => Replayed_Prefix'Result =
       (Valid (S, F)
        and then VL >= Header_Len
        and then Input'Last < S.Log_Cap
        and then Header_Well_Formed (Input)
        and then Log_Length (S) = VL
        and then VL - 1 <= Input'Last
        and then (for all J in 0 .. VL - 1 => Log_Byte (S, J) = Input (J))
        and then (for all J in 0 .. Pubkey_Len - 1 => Root_Key (S) (J) = Input (HO_Root + J))
        and then (for all J in 0 .. Salt_Len - 1 => Salt_Of (S) (J) = Input (HO_Salt + J))
        and then Del_TTL (S) = Header_TTL (Input)
        and then Self_Key (S) = Kome.Keys.To_Key256 (Self_PK)
        and then Pinned (S) = 0);

   --  Open a store again from its log (replay, S15, T18). F.Cap is the data
   --  capacity of this open; it can be above or below the capacity of the
   --  store that wrote the log.
   --    No_Space   the log does not fit S (Input'Last >= S.Log_Cap), or an
   --               APPLY does not fit the data row of this open.
   --    Malformed  a HEADER that is not well formed; an entry that does not
   --               parse; a frame that is not a record frame or whose
   --               header is not canonical; an APPLY that Put_Frame would
   --               refuse (Inadmissible, Dominated, Auth_Full) or capture
   --               (Ceil_Only: a store writes a CEIL for it); a CEIL whose
   --               frame is not a ROSTER, or whose ceiling is not above
   --               maxceil unless it repeats the cell's record.
   --  Replay applies each APPLY in trusted mode (decode once, hash once, no
   --  signature check: Trusted_Frame), and an APPLY that Put_Frame accepts
   --  without a change (a duplicate, an expired DEL that drops nothing)
   --  stays in the log. A SEQ raises seq_self. A CEIL reruns the capture
   --  of Put_Ceil (the rows are not tried); a CEIL that repeats the cell's
   --  record stays in the log and changes nothing, wherever it stands.
   --  Valid_Length (AUDIT.md H23) is the length of the longest prefix of
   --  Input at an entry boundary that replays: on OK the whole input; on
   --  Malformed or No_Space from an entry, the start of the refused entry
   --  (at least the HEADER). When it is positive, (S, F) is the replay of
   --  exactly that prefix (Replayed_Prefix). It is 0 when the HEADER is
   --  refused or the log does not fit.
   procedure Open_From_Log
     (Input        : in     Byte_Array;
      Self_PK      : in     Pubkey;
      F            :    out Frontier.State;
      S            :    out Store;
      Valid_Length :    out Log_Size;
      Result       :    out Status)
   with
     Global => null,
     Pre  => Input'First = 0,
     Post => Result in OK | Malformed | No_Space
       and (if Input'Last >= S.Log_Cap then Result = No_Space)
       --  Part of completeness: a log that is only a well-formed HEADER
       --  opens. The result is Malformed only for a HEADER that is not a
       --  HEADER, or for a log that has entries after the HEADER.
       and (if Input'Last = Header_Len - 1
              and then Input'Last < S.Log_Cap
              and then Header_Well_Formed (Input)
            then Result = OK)
       and (if Result = Malformed then
              not Header_Well_Formed (Input) or else Input'Last >= Header_Len)
       and (if Result = No_Space then
              Input'Last >= S.Log_Cap or else Input'Last >= Header_Len)
       and (Valid_Length = 0 or else Valid_Length - 1 <= Input'Last)
       and (if Result = OK then Valid_Length > 0 and then Valid_Length - 1 = Input'Last)
       --  T18-prefix (AUDIT.md H23): the replayed prefix is a log.
       and (if Valid_Length > 0
            then Replayed_Prefix (Input, Self_PK, F, S, Valid_Length));

   ---------------------------------------------------------------------------
   --  The invariant, unpacked.
   ---------------------------------------------------------------------------

   --  The pair's identity.
   procedure Lemma_Valid_Facts (S : Store; F : Frontier.State) with
     Ghost, Global => null,
     Pre  => Valid (S, F),
     Post => Is_Frontier (F)
       and then Frontier.Founding (F) = Founding (S)
       and then Founding (S) = Kome.Keys.To_Key256 (Root_Key (S))
       and then Del_TTL (S) in Del_TTL_Min .. Del_TTL_Max
       and then Cid (S) = Kome.Records.Cid_Of (Root_Key (S), Salt_Of (S), Del_TTL (S))
       and then Log_Length (S) >= Header_Len
       and then Log_Entries (S) <= Log_Length (S);

   --  The HEADER's bytes.
   procedure Lemma_Log_Header (S : Store; F : Frontier.State) with
     Ghost, Global => null,
     Pre  => Valid (S, F),
     Post => Log_Length (S) >= Header_Len
       and then (for all J in 0 .. Magic_Len - 1 => Log_Byte (S, J) = Magic (J))
       and then Log_Byte (S, HO_Version) = Log_Version
       and then (for all J in 0 .. Pubkey_Len - 1 =>
                   Log_Byte (S, HO_Root + J) = Root_Key (S) (J))
       and then (for all J in 0 .. Salt_Len - 1 =>
                   Log_Byte (S, HO_Salt + J) = Salt_Of (S) (J))
       and then Code_At (S, HO_TTL) = Del_TTL (S);

   --  S14: the tag of a held record points at an APPLY entry whose frame
   --  has that record as its header.
   procedure Lemma_Tag (S : Store; F : Frontier.State; I : Held_Index) with
     Ghost, Global => null,
     Pre  => Valid (S, F) and then I <= Count (F),
     Post => Tag_Off (Tag (F, I)) >= Header_Len
       and then Has_Frame (S, Tag_Off (Tag (F, I)))
       and then Op_At (S, Tag_Off (Tag (F, I))) = Op_Apply
       and then Len_At (S, Tag_Off (Tag (F, I))) = Tag_Len (Tag (F, I))
       and then Is_Record_Frame (Read_Frame (S, Tag_Off (Tag (F, I))))
       and then Header_Of (Cid (S), Read_Frame (S, Tag_Off (Tag (F, I)))) = Held (F, I);

   --  AUDIT.md H12: the cell's tag points at a CEIL entry whose frame has
   --  the cell's record as its header. The frame is a ROSTER frame, so it
   --  is at most Kome.Records.Roster_Frame_Max bytes (what
   --  Kome.Reconcile.Admit requires of the ceiling frame of a HELLO).
   procedure Lemma_Ceil_Tag (S : Store; F : Frontier.State) with
     Ghost, Global => null,
     Pre  => Valid (S, F) and then Has_Ceil (F),
     Post => Tag_Off (Ceil_Tag (F)) >= Header_Len
       and then Has_Frame (S, Tag_Off (Ceil_Tag (F)))
       and then Op_At (S, Tag_Off (Ceil_Tag (F))) = Op_Ceil
       and then Len_At (S, Tag_Off (Ceil_Tag (F))) = Tag_Len (Ceil_Tag (F))
       and then Is_Record_Frame (Read_Frame (S, Tag_Off (Ceil_Tag (F))))
       and then Kome.Records.Is_Roster_Frame (Read_Frame (S, Tag_Off (Ceil_Tag (F))))
       and then Header_Of (Cid (S), Read_Frame (S, Tag_Off (Ceil_Tag (F)))) = Ceil_Held (F);

   --  T11 (a): no held record is a DEL at or below the horizon.
   procedure Lemma_No_Expired (S : Store; F : Frontier.State; I : Held_Index) with
     Ghost, Global => null,
     Pre  => Valid (S, F) and then I <= Count (F),
     Post => not Expired_In (Held (F, I), F, Del_TTL (S));

   --  S16: seq_self bounds every held own seq.
   procedure Lemma_Seq_Self (S : Store; F : Frontier.State; I : Held_Index) with
     Ghost, Global => null,
     Pre  => Valid (S, F) and then I <= Count (F)
             and then Is_Data (Held (F, I)) and then Held (F, I).V.Author = Self_Key (S),
     Post => Held (F, I).V.Seq <= Seq_Self (S);

   --  S21: the digests model the two row sets.
   procedure Lemma_Digests (S : Store; F : Frontier.State) with
     Ghost, Global => null,
     Pre  => Valid (S, F),
     Post => Kome.Digest.Models (Digest_Data (S), Data_Hashes (F), Data_Count (F))
       and then Kome.Digest.Models (Digest_Auth (S), Auth_Hashes (F), Auth_Count (F));

   --  S21, the bridge to Kome.Digest.State_Of: the digest of all of F is
   --  the data digest plus the authorization digest.
   procedure Lemma_Digest_Split (S : Store; F : Frontier.State) with
     Ghost, Global => null,
     Pre  => Valid (S, F),
     Post => Kome.Digest.Count (Digest_Data (S)) + Kome.Digest.Count (Digest_Auth (S))
               = Kome.Digest.Count (Kome.Digest.State_Of (F))
       and then Kome.Accumulator.Add (Kome.Digest.Sum (Digest_Data (S)),
                                      Kome.Digest.Sum (Digest_Auth (S)))
                = Kome.Digest.Sum (Kome.Digest.State_Of (F));

private

   --  No Dynamic_Predicate: the bounds of the components are part of
   --  Valid, and the accessors clamp, so clients can assign a Store.
   type Store (Log_Cap : Log_Size) is record
      Root : Pubkey  := [others => 0];
      Slt  : Salt    := [others => 0];
      TTL  : U48     := Del_TTL_Min;
      Cid  : Hash256 := [others => 0];   --  Cid_Of (Root, Slt, TTL) (S1)
      Fnd  : Key256  := (others => 0);
      Self : Key256  := (others => 0);
      SS   : U48     := 0;               --  seq_self (S16)
      DA   : Kome.Digest.Digest_State;   --  the authorization rows (S21)
      DD   : Kome.Digest.Digest_State;   --  the data row (S21)
      Pins : Natural := 0;
      LL   : Log_Size := 0;
      NE   : Natural  := 0;              --  entries after the HEADER
      Log  : Byte_Array (0 .. Log_Cap) := [others => 0];   --  Log (0 .. LL - 1)
   end record;

   function Founding (S : Store) return Key256 is (S.Fnd);
   function Root_Key (S : Store) return Pubkey is (S.Root);
   function Salt_Of (S : Store) return Salt is (S.Slt);
   function Del_TTL (S : Store) return U48 is (S.TTL);
   function Cid (S : Store) return Hash256 is (S.Cid);
   function Self_Key (S : Store) return Key256 is (S.Self);
   function Seq_Self (S : Store) return U48 is (S.SS);
   function Digest_Auth (S : Store) return Kome.Digest.Digest_State is (S.DA);
   function Digest_Data (S : Store) return Kome.Digest.Digest_State is (S.DD);
   function Pinned (S : Store) return Natural is (S.Pins);
   function Log_Length (S : Store) return Log_Size is
     (if S.LL <= S.Log_Cap then S.LL else S.Log_Cap);
   function Log_Byte (S : Store; J : Natural) return Byte is (S.Log (J));
   function Log_Entries (S : Store) return Natural is
     (if S.NE <= Log_Max then S.NE else 0);

   function Header_Of (Cid : Hash256; Frame : Byte_Array) return Header is
     (case Kome.Records.Kind_Of (Frame) is
        when K_Put    => Kome.Records.To_Header (Cid, Kome.Records.Parse_Put (Frame)),
        when K_Del    => Kome.Records.To_Header (Cid, Kome.Records.Parse_Del (Frame)),
        when K_Roster => Kome.Records.To_Header (Cid, Kome.Records.Parse_Roster (Frame)),
        when K_Revoke => Kome.Records.To_Header (Cid, Kome.Records.Parse_Revoke (Frame)),
        when K_Grant  => Kome.Records.To_Header (Cid, Kome.Records.Parse_Grant (Frame)));

end Kome.Store;
