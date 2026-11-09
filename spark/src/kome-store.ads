--  Kome.Store: the storage model of DESIGN.md §7. The replica of one
--  collection has two parts:
--    * a lattice state F (Kome.Frontier.State);
--    * a Store, which has an append-only log and an in-memory index. The
--      log is a journal of the operations on F. The index gives the frame
--      in the log of each held record (DESIGN.md §7: "an in-memory index
--      cell -> (offset, v) that holds exactly the records of F").
--  Each operation takes the pair (S, F). Valid (S, F) relates S and F.
--
--  F is a parameter and not a component of Store, for these reasons:
--    * Frontier.Unchanged is the only comparison of two States. When F is
--      beside the Store, the Store's state stays small.
--    * Compact takes F in mode `in`, so flow analysis alone proves that
--      Compact does not change the frontier.
--    * gnatprove 14 crashed on a Frontier.State record component when
--      Frontier.State had a Dynamic_Predicate. (CONVENTIONS.md forbids
--      that predicate.)
--  No operation has to restore a state. Put_Frame and Expire find each
--  refusal before they change F, so a refused call changes neither S
--  nor F.
--
--  The log (D9, DESIGN.md §7) is a journal. All integers are big-endian:
--
--    HEADER         op 0 ‖ "kome/log" ‖ version:u8 (= 1) ‖ ns[16] ‖ root_pk[32]
--                   ‖ salt[16] ‖ data_cap:u32 ‖ slice:u16            (80 bytes)
--    APPLY          op 1 ‖ len:u32 ‖ frame     a record applied and held
--    APPLY_EXPIRED  op 2 ‖ len:u32 ‖ frame     a DEL applied for its effect, not held
--    EXPIRE         op 3 ‖ horizon:u48         Frontier.Expire at horizon, or a
--                                              lowered horizon
--
--  The HEADER is the first entry, and the log has exactly one HEADER. Its
--  ns is BLAKE2b-256 (root_pk ‖ salt)[0:16], which fixes the founding key.
--  Its capacities are those of the store's last open (see
--  Capacities below). A frame is tag ‖ content ‖ sig, exactly as
--  Kome.Records encodes it. The horizon u48 2**48 - 1 encodes "no
--  horizon" (a lowered horizon below 0). A real horizon is
--  min (now, maxceil) - del_ttl_eff <= 2**48 - 1 - Del_TTL_Min, so this
--  code is never a real horizon. (DESIGN.md §7 does not specify this
--  encoding.)
--
--  The model of the log is a bounded byte buffer. The model writes only at
--  the end of the buffer, so an OS file can replace it. The binding
--  flushes the file to Log_Length (the sync point) before a session counts
--  as Complete and before a bundle is acknowledged or deleted from a
--  mailbox (DESIGN.md §8; A4′: a lost log tail is a backup restore).
--  Under Log_Fits (below), a Log_Full result means "compact and retry":
--    * Put_Frame returns the offset of the entry that it appended;
--    * Read_Frame reads a frame back;
--    * Log_Bytes is the file image;
--    * Compact writes the full log again, as a program writes a new file
--      and renames it.
--  The invariant states that the log is a chain of entries from offset 0
--  to its length (Log_Entries, Entry_Start, Lemma_Scan). The first entry
--  is the HEADER, so a scan of the log can open a replica again. Each
--  index entry points to one of the APPLY entries of the log.
--
--  The index is F exactly (D9). A record is held iff it has an index
--  entry. The entries are distinct, and the APPLY of each entry contains
--  its frame. The index capacity covers F (S.Cap >= F.Cap + Signers_Max *
--  F.Slice, the precondition of Open), so the index itself never causes
--  a refusal.
--
--  Order of operations (D11, E1, E2; DESIGN.md §7) for a decoded, verified
--  frame:
--    (0) An authorization record whose root_pk is not the founding key:
--        Malformed.
--    (1) Not admitted: Inadmissible.
--    (2) Already held: OK, no change.
--    (3) Dominated: Dominated. This step needs no room, so it never gives
--        No_Space.
--    (4) A DEL with t <= horizon (expired on arrival): the store applies it
--        for its effect (Frontier.Apply_Expired). If it drops one or more
--        records, the store logs it as APPLY_EXPIRED. If not, the result is
--        OK with no change. This step needs only log room.
--    (5) Room: first the rules of Frontier (No_Space for the data row,
--        Auth_Full for the slice of a signer, the slot table or W), then
--        the authorization generation counter at its bound (Auth_Full,
--        unreachable in practice), then the log bytes (Log_Full: the
--        binding compacts and retries; under Log_Fits a compacted log
--        always has the room, AUDIT.md H3).
--    (6) Apply the record, append APPLY, index the record, and remove the
--        index entries of the records that it dominated.
--  A refusal changes nothing (T13): the Post says Unchanged (F'Old, F)
--  and S = S'Old.
--
--  Expiry (D10, DESIGN.md §7, T11): Expire (Now) computes this horizon in
--  64 bits:
--    horizon := min (now, maxceil (F)) - del_ttl_eff (F)
--  If this value is below 0, the horizon is "none". A higher horizon
--  removes exactly the DELs with t <= horizon from F (Frontier.Expire) and
--  from the index. A lower horizon only lowers the horizon of the store,
--  so fewer arriving DELs expire on arrival.
--  Expire logs EXPIRE iff the call removed a record or lowered the
--  horizon, so periodic calls do not make the log larger. If a raise
--  removed nothing, the store keeps the new horizon only in memory.
--  Compact makes it durable.
--
--  Compaction writes the log again in this layout:
--    * the HEADER (the same bytes);
--    * one APPLY for each index entry: first all authorization records,
--      then all data records, each part in index order;
--    * one EXPIRE (horizon), if the store has a horizon.
--  If fewer than Expire_Len (7) bytes of the log are left after the
--  frames, there is no EXPIRE. Compact_Layout states when this happens
--  (DESIGN.md §10 item 10 (b), AUDIT.md G23): only when the old log was
--  the HEADER and the held APPLYs with fewer than 7 bytes to spare, that
--  is, in the full-log state of AUDIT.md H3, which Log_Fits excludes. The
--  reopened horizon is then lower, and T18 allows this.
--
--  Compaction is a store duty of the binding (AUDIT.md H26): it calls
--  Compact when Compact_Due (S) holds (more than 2 * |F| + Compact_Slack
--  log entries). Put_Frame never compacts on its own. Replay then checks
--  at most 2 * |F| + Compact_Slack signatures.
--
--  Two counters (AUDIT.md H11, H28) are part of the store and of the
--  contracts of every operation, and replay rebuilds them from the log:
--    * Auth_Gen goes up by one iff Put_Frame holds a ROSTER, REVOKE or
--      GRANT. A session compares two reads of it to see whether the gate
--      must be evaluated again. At its bound, Put_Frame refuses the record
--      (Auth_Full, Gen_Full);
--    * Expire_Mark is a monotone lower bound for the write floor
--      (Kome.Emit.Choose): the largest horizon the store ever applied
--      (at or above the t of every DEL that Expire removed), and at least
--      the t of every DEL applied for its effect.
--
--  Replay (T18): Open_From_Log does these steps:
--    1. It checks the HEADER (bytes, and the slice of this open).
--    2. It starts from Frontier.Empty with the logged founding key and the
--       capacities of this open.
--    3. It performs the entries in order:
--         * APPLY through Put_Frame, which must hold the record as a new
--           record, or find it held already (any other result is
--           Malformed; No_Space when the data row of this open is full);
--         * APPLY_EXPIRED through Frontier.Apply_Expired;
--         * EXPIRE through Frontier.Expire if it raises the horizon. In
--           all cases, replay sets the horizon, clamped to
--           Horizon_At (F, U48'Last) = maxceil - del_ttl_eff of the
--           frontier at that point (AUDIT.md H24).
--  The clamp refuses nothing: the logged bytes stay as they are, only the
--  horizon that replay applies is bounded. Every EXPIRE that Expire
--  writes meets the bound (its Post), maxceil never falls (the Post of
--  Frontier.Apply keeps Ceil non-decreasing), and del_ttl_eff is at least
--  Del_TTL_Min; so on a store's own log the clamp changes a horizon only
--  when a later roster raised del_ttl_eff (then the reopened horizon is
--  lower, which T18 allows). The horizon u48 2**48 - 1 still encodes "no
--  horizon" on the wire; it is below every bound, so a corrupt EXPIRE can
--  at most lower the horizon.
--
--  Capacities (for T18; DESIGN.md §10 item 10 (a), AUDIT.md A11): the
--  slice is fixed for a collection (DESIGN.md §7; a binding opens every
--  store with Slice_Max), and the HEADER's slice field is only a check.
--  The data capacity is a parameter of each open: a store can open again
--  with a larger or a smaller data_cap, as long as its log replays at
--  that capacity (No_Space otherwise). The HEADER keeps the data_cap of
--  the open that wrote it, so the log is never rewritten in place: the
--  only writes are appends at Log_Length and the rename of Compact.
--
--  Footprint (for a file binding): Open_From_Log replays against its
--  input in place. Compact copies the full log buffer before it writes
--  the log again, so it needs stack or memory for one more log image (up
--  to Log_Max bytes). For this reason, the test main runs in a task with
--  a large stack.
--
--  gnatprove proves these facts about Open_From_Log:
--    * the result is Valid and its HEADER is well formed;
--    * its log is the input, byte for byte;
--    * its horizon is at most the horizon of the last EXPIRE entry (none
--      if there is no EXPIRE entry);
--    * the result is No_Space only for a log that does not fit, for a
--      logged slice that is not the slice of this open, or for an entry
--      after the HEADER (one that the data row of this open refuses);
--    * the result is Malformed only for a HEADER that is not a HEADER, or
--      for a log with entries after the HEADER;
--    * a log that is only a well-formed HEADER, with the slice of this
--      open, opens;
--    * Valid_Length is the length of the replayed prefix, and (S, F) is
--      the replay of that prefix (T18-prefix, AUDIT.md H23).
--  SPARK does not prove that replay accepts every log that a store writes
--  and gives back its frontier (T18, Lean `auth_first`). This is a set
--  statement. Lean proves it, and the tests here test it. A replay that
--  refused every log with entries would also meet this contract.
--
--  What is proved (Valid is the store invariant; each operation keeps it):
--    * the index is F: a record is held iff it is indexed, the entries are
--      distinct, no held DEL is expired at the horizon of the store, and a
--      cell has at most one entry (T5);
--    * the log is a chain of entries from 0. The HEADER is first and only
--      there. Its bytes are those of the collection, founding key, salt
--      and logged capacities of the store. Each index entry is an APPLY
--      entry of the chain, with its length and the tag of its kind;
--    * Put_Frame refines Frontier.Apply and Frontier.Apply_Expired, in the
--      order above. The contract states each refusal as an iff, and a
--      refusal changes nothing. The log only grows, written bytes never
--      change, and the entry is at the returned offset;
--    * Expire computes the horizon of DESIGN.md §7 and removes exactly the
--      expired DELs. It logs EXPIRE only as stated, and it leaves no held
--      DEL at or below the horizon (T11 (a));
--    * Compact keeps F, the horizon, the counters and the records of the
--      index. It writes the log in the stated layout, with frames byte
--      for byte, and the result is not due for compaction;
--    * Open_From_Log returns a Valid pair. Its log is its input, and its
--      horizon is at most the last logged horizon.
--  This fact is not in the invariant, and the tests check it: the frame of
--  each entry decodes to the header of the entry. The header contains h,
--  a BLAKE2b hash of the content of the frame. gnatprove 14 has no
--  extensionality for arrays. Kome.Crypto.Blake2b_256 is a function of the
--  full array value, so gnatprove does not know that two byte arrays
--  with equal elements have equal headers. Examples of such arrays are the
--  frame given to Put_Frame, its copy in the log and its copy after
--  Compact. To keep this fact in the invariant, the proof needs
--  Kome.Crypto.Lemma_Blake2b_Congruent and a congruence lemma for
--  To_Header (Parse_*) in Kome.Records. That lemma does not exist. The
--  test main checks the fact on each index entry (Every_Frame_Matches),
--  after Put_Frame and after Compact.
pragma Ada_2022;
with Kome.Headers;   use Kome.Headers;
with Kome.Registers; use Kome.Registers;
with Kome.Frontier;  use Kome.Frontier;
with Kome.Keys;
with Kome.Records;
with Kome.Views;
package Kome.Store with SPARK_Mode is

   ---------------------------------------------------------------------------
   --  Bounds and the log layout.
   ---------------------------------------------------------------------------

   --  The bound on the log buffer of the model (1 GiB). With this bound,
   --  each offset + entry is a Natural. A file binding keeps this bound.
   Log_Max : constant := 2**30;
   subtype Log_Size is Natural range 0 .. Log_Max;

   Op_Header        : constant Byte := 0;
   Op_Apply         : constant Byte := 1;
   Op_Apply_Expired : constant Byte := 2;
   Op_Expire        : constant Byte := 3;

   Magic_Len   : constant := 8;
   Magic       : constant Byte_Array (0 .. Magic_Len - 1) :=
     [16#6B#, 16#6F#, 16#6D#, 16#65#, 16#2F#, 16#6C#, 16#6F#, 16#67#];   --  "kome/log"
   Log_Version : constant Byte := 1;

   --  HEADER field offsets.
   HO_Magic   : constant := 1;
   HO_Version : constant := HO_Magic + Magic_Len;      --   9
   HO_NS      : constant := HO_Version + 1;            --  10
   HO_Root    : constant := HO_NS + NS_Len;            --  26
   HO_Salt    : constant := HO_Root + Pubkey_Len;      --  58
   HO_Cap     : constant := HO_Salt + Salt_Len;        --  74
   HO_Slice   : constant := HO_Cap + 4;                --  78
   Header_Len : constant := HO_Slice + 2;              --  80
   pragma Compile_Time_Error (Header_Len /= 80, "DESIGN.md §7: the HEADER is 80 bytes");

   Apply_Prefix : constant := 5;   --  op ‖ len:u32
   Expire_Len   : constant := 7;   --  op ‖ horizon:u48
   Min_Entry    : constant := Apply_Prefix + 1;

   subtype Frame_Size is Positive range 1 .. Kome.Records.Frame_Max;

   --  The horizon of the store: No_Horizon (-1, nothing expired) or a
   --  real horizon of at most 2**48 - 2 (see the comment at the top of
   --  this file).
   subtype Horizon_Value is Time64 range No_Horizon .. Time64 (U48'Last) - 1;
   No_Horizon_Code : constant U48 := U48'Last;

   function Horizon_Code (H : Horizon_Value) return U48 is
     (if H = No_Horizon then No_Horizon_Code else U48 (H));

   function Horizon_Of_Code (C : U48) return Horizon_Value is
     (if C = No_Horizon_Code then No_Horizon else Time64 (C));

   --  The authorization generation counter (AUDIT.md H11). A range type,
   --  as CONVENTIONS.md asks: Put_Frame refuses (Auth_Full) an
   --  authorization record at the bound, so the counter never wraps. No
   --  replica applies 2**62 authorization records.
   Auth_Gen_Max : constant := 2**62;
   type Auth_Counter is range 0 .. Auth_Gen_Max with Size => 64;

   --  Compaction as a store duty (AUDIT.md H26): the binding calls Compact
   --  when Compact_Due (S) holds, that is, when the log has more than
   --  2 * Entries (S) + Compact_Slack entries. Compact never auto-runs
   --  inside Put_Frame. Then, before each operation, the log has at most
   --  2 * |F| + Compact_Slack entries, and Open_From_Log verifies at most
   --  that many signatures (one for each APPLY or APPLY_EXPIRED entry).
   --  Compact_Slack is at least 2, so a compacted log (the HEADER, one
   --  APPLY for each held record, at most one EXPIRE) is never due.
   Compact_Slack : constant := 64;

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

   --  Frame is a well-formed record: exactly what Kome.Records.Decode_Verified
   --  accepts for its kind (DESIGN.md §2 items 1-5).
   function Verified (Frame : Byte_Array) return Boolean is
     (Is_Record_Frame (Frame)
      and then (case Kome.Records.Kind_Of (Frame) is
                  when K_Put    => Kome.Records.Well_Formed (Kome.Records.Parse_Put (Frame)),
                  when K_Del    => Kome.Records.Well_Formed (Kome.Records.Parse_Del (Frame)),
                  when K_Roster => Kome.Records.Well_Formed (Kome.Records.Parse_Roster (Frame)),
                  when K_Revoke => Kome.Records.Well_Formed (Kome.Records.Parse_Revoke (Frame)),
                  when K_Grant  => Kome.Records.Well_Formed (Kome.Records.Parse_Grant (Frame))));

   --  The lattice header of a record frame (Kome.Records.To_Header of the
   --  parse result). Lemma_Header_Of gives the full definition.
   function Header_Of (Frame : Byte_Array) return Header with
     Global => null,
     Pre    => Is_Record_Frame (Frame);

   procedure Lemma_Header_Of (Frame : Byte_Array) with
     Ghost, Global => null,
     Pre  => Is_Record_Frame (Frame),
     Post => Header_Of (Frame).K = Kome.Records.Kind_Of (Frame)
       and then Header_Of (Frame) =
               (case Kome.Records.Kind_Of (Frame) is
                  when K_Put    => Kome.Records.To_Header (Kome.Records.Parse_Put (Frame)),
                  when K_Del    => Kome.Records.To_Header (Kome.Records.Parse_Del (Frame)),
                  when K_Roster => Kome.Records.To_Header (Kome.Records.Parse_Roster (Frame)),
                  when K_Revoke => Kome.Records.To_Header (Kome.Records.Parse_Revoke (Frame)),
                  when K_Grant  => Kome.Records.To_Header (Kome.Records.Parse_Grant (Frame)));

   --  The header of a verified frame is canonical (D3; Kome.Records
   --  Lemma_Header_Canonical, and the del_ttl clamp of the roster from
   --  Well_Formed).
   procedure Lemma_Verified_Canonical (Frame : Byte_Array) with
     Ghost, Global => null,
     Pre  => Verified (Frame),
     Post => Canonical (Header_Of (Frame))
             and then Header_Of (Frame).K = Kome.Records.Kind_Of (Frame);

   ---------------------------------------------------------------------------
   --  The store.
   ---------------------------------------------------------------------------

   --  One index entry: the record (its header, which contains v and the
   --  cell), the offset of its APPLY entry and the length of the frame.
   type Index_Entry is record
      H   : Header;
      Off : Log_Size   := 0;
      Len : Frame_Size := 1;
   end record;

   --  The offset immediately after the APPLY of an entry.
   function End_Of (E : Index_Entry) return Natural is
     (E.Off + Apply_Prefix + E.Len);

   --  Cap index entries, Log_Cap bytes of log.
   type Store (Cap : Held_Count; Log_Cap : Log_Size) is private;

   function Collection (S : Store) return Id128 with Global => null;
   function Founding (S : Store) return Key256 with Global => null;
   function Root_Key (S : Store) return Pubkey with Global => null;
   function Salt_Of (S : Store) return Salt with Global => null;
   --  The capacities logged in the HEADER.
   function Logged_Cap (S : Store) return Data_Size with Global => null;
   function Logged_Slice (S : Store) return Slice_Count with Global => null;
   function Horizon (S : Store) return Horizon_Value with Global => null;
   --  The authorization generation (AUDIT.md H11): a monotone counter
   --  that goes up by one with every ROSTER, REVOKE or GRANT that
   --  Put_Frame holds, also through replay. A session records it at Admit
   --  and evaluates the gate again when it has changed. Expire and Compact
   --  keep it. After Open_From_Log it is the number of APPLY entries of
   --  authorization records in the log.
   function Auth_Gen (S : Store) return Auth_Counter with Global => null;
   --  The expiry mark (AUDIT.md H28): a monotone lower bound for the write
   --  floor of Kome.Emit.Choose (which takes it as Mark). It is 0 at Open.
   --  It rises to the new horizon whenever Expire raises the horizon (so
   --  it is the largest horizon the store ever applied: at least the t of
   --  every DEL that Expire removed, and below maxceil), and to the t of
   --  a DEL that Put_Frame applies for its effect (APPLY_EXPIRED). Nothing
   --  lowers it. Open_From_Log rebuilds it from the logged EXPIRE and
   --  APPLY_EXPIRED entries through the same steps, so after a reopen it
   --  is at most the live mark (a raise that removed nothing is not
   --  logged), and a compacted log's EXPIRE (horizon) carries it.
   function Expire_Mark (S : Store) return U48 with Global => null;
   function Entries (S : Store) return Held_Count with
     Global => null,
     Post => Entries'Result <= S.Cap;
   function Entry_At (S : Store; I : Held_Index) return Index_Entry with
     Global => null,
     Pre => I <= Entries (S);
   function Log_Length (S : Store) return Log_Size with
     Global => null,
     Post => Log_Length'Result <= S.Log_Cap;
   function Log_Byte (S : Store; J : Natural) return Byte with
     Global => null,
     Pre => J < Log_Length (S);

   --  The entries of the log, in order. There are Log_Entries (S) entries,
   --  and the K-th entry is at offset Entry_Start (S, K) (Lemma_Scan).
   function Log_Entries (S : Store) return Natural with
     Global => null,
     Post => Log_Entries'Result <= S.Log_Cap;
   function Entry_Start (S : Store; K : Positive) return Log_Size with
     Global => null,
     Pre => K <= Log_Entries (S);

   --  The log is due for compaction (AUDIT.md H26; see Compact_Slack).
   --  Under Valid, Entries (S) = Count (F).
   function Compact_Due (S : Store) return Boolean is
     (Log_Entries (S) > 2 * Entries (S) + Compact_Slack);

   --  At least one index entry is the record X. Opaque (quantified).
   function Indexed (S : Store; X : Header) return Boolean with Global => null;

   --  The index position of an indexed record (ghost; unique on a valid
   --  store, Lemma_Position).
   function Position (S : Store; X : Header) return Held_Index with
     Ghost, Global => null,
     Pre  => Indexed (S, X),
     Post => Position'Result <= Entries (S) and then Entry_At (S, Position'Result).H = X;

   --  The store invariant. It relates the store to its lattice state F
   --  (see the package comment). Opaque: use the lemmas below to read it.
   function Valid (S : Store; F : Frontier.State) return Boolean with Global => null;

   --  The identity of a store: collection, founding key, salt, logged
   --  capacities. Every operation keeps it.
   function Same_Identity (Old_S, New_S : Store) return Boolean is
     (Collection (New_S) = Collection (Old_S)
      and then Founding (New_S) = Founding (Old_S)
      and then Root_Key (New_S) = Root_Key (Old_S)
      and then Salt_Of (New_S) = Salt_Of (Old_S)
      and then Logged_Cap (New_S) = Logged_Cap (Old_S)
      and then Logged_Slice (New_S) = Logged_Slice (Old_S));

   ---------------------------------------------------------------------------
   --  The log as a file.
   ---------------------------------------------------------------------------

   function Op_At (S : Store; P : Natural) return Byte is (Log_Byte (S, P))
     with Pre => P < Log_Length (S);

   --  The len:u32 of the APPLY or APPLY_EXPIRED entry at P.
   function Len_At (S : Store; P : Natural) return Word is
     (Kome.Keys.Word_Of (Log_Byte (S, P + 1), Log_Byte (S, P + 2),
                         Log_Byte (S, P + 3), Log_Byte (S, P + 4)))
     with Pre => P < Log_Length (S) and then Log_Length (S) - P >= Apply_Prefix;

   --  The u48 at P (an EXPIRE's horizon code is at its offset + 1).
   function Code_At (S : Store; P : Natural) return U48 is
     (Kome.Records.U48_Of (Log_Byte (S, P), Log_Byte (S, P + 1), Log_Byte (S, P + 2),
                           Log_Byte (S, P + 3), Log_Byte (S, P + 4), Log_Byte (S, P + 5)))
     with Pre => P < Log_Length (S) and then Log_Length (S) - P >= 6;

   --  A whole APPLY or APPLY_EXPIRED entry starts at P.
   function Has_Frame (S : Store; P : Natural) return Boolean is
     (P < Log_Length (S)
      and then Log_Length (S) - P >= Apply_Prefix
      and then Op_At (S, P) in Op_Apply | Op_Apply_Expired
      and then Len_At (S, P) in 1 .. Kome.Records.Frame_Max
      and then Natural (Len_At (S, P)) <= Log_Length (S) - P - Apply_Prefix);

   --  A whole entry of any kind starts at P.
   function Has_Log_Entry (S : Store; P : Natural) return Boolean is
     (P < Log_Length (S)
      and then (if Op_At (S, P) = Op_Header then Log_Length (S) - P >= Header_Len
                elsif Op_At (S, P) = Op_Expire then Log_Length (S) - P >= Expire_Len
                else Has_Frame (S, P)));

   --  The size of the entry at P, and the offset of the next entry.
   function Entry_Size (S : Store; P : Natural) return Natural is
     (if Op_At (S, P) = Op_Header then Header_Len
      elsif Op_At (S, P) = Op_Expire then Expire_Len
      else Apply_Prefix + Natural (Len_At (S, P)))
     with Pre => Has_Log_Entry (S, P);

   function Next_Offset (S : Store; P : Natural) return Natural is
     (P + Entry_Size (S, P))
     with Pre => Has_Log_Entry (S, P);

   --  The frame of the APPLY or APPLY_EXPIRED entry at Off (indexed from 0).
   function Read_Frame (S : Store; Off : Natural) return Byte_Array with
     Global => null,
     Pre  => Has_Frame (S, Off),
     Post => Read_Frame'Result'First = 0
       and then Read_Frame'Result'Length = Natural (Len_At (S, Off))
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

   --  Step 0 (DESIGN.md §7): an authorization record whose root_pk is not
   --  the store's founding key.
   function Foreign_Root (S : Store; Frame : Byte_Array) return Boolean is
     (Kome.Records.Is_Auth_Frame (Frame)
      and then Kome.Records.Root_Key_Of (Frame) /= Founding (S));

   --  The room rules of Frontier.Apply, copied from its Post: the data row
   --  is full and R frees nothing (No_Space) ...
   function Data_Full (F : Frontier.State; R : Header) return Boolean is
     (Is_Data (R) and then Data_Count (F) = F.Cap and then not Drops_Any (F, R));

   --  ... and the authorization rules (Auth_Full): the slice of the signer
   --  is full and R frees nothing; or the signer is new and all slots are
   --  used; or W is full (unreachable, see Kome.Frontier.Apply).
   function Auth_Rule (F : Frontier.State; R : Header) return Boolean is
     (Is_Auth (R)
      and then ((Slot_Of (F, R.Issuer) /= 0
                 and then Slot_Count (F, Slot_Of (F, R.Issuer)) = F.Slice
                 and then not Drops_Any (F, R))
                or else (Slot_Of (F, R.Issuer) = 0 and then Slots_Used (F) = Signers_Max)
                or else (R.K = K_Grant
                         and then not In_W (Regs (F), R.V.Author)
                         and then Kome.Registers.Count (Regs (F)) = Writers_Max)));

   --  The authorization generation counter is at its bound, and R would
   --  raise it (Auth_Full; AUDIT.md H11).
   function Gen_Full (S : Store; R : Header) return Boolean is
     (Is_Auth (R) and then Auth_Gen (S) = Auth_Gen_Max);

   --  Fewer than Need bytes of log are left.
   function Log_Short (S : Store; Need : Natural) return Boolean is
     (S.Log_Cap - Log_Length (S) < Need);

   --  The largest log entry: the APPLY prefix and the largest frame.
   Entry_Max : constant := Apply_Prefix + Kome.Records.Frame_Max;   --  41 141

   --  Log bytes are a capacity class shared by every record (DESIGN.md §7,
   --  E1; AUDIT.md H3). Under Log_Fits, a compacted log (the HEADER, one
   --  APPLY per held record, one EXPIRE) has room for one more entry of
   --  any kind, so Log_Full only ever means "compact first", and no flood
   --  of large values can block the founding REVOKE. Open and
   --  Open_From_Log do not require it: a small log is legitimate (tests,
   --  tiny stores), and then Log_Full can be permanent. The binding checks
   --  it when it chooses Log_Cap for a Cap and a Slice. It is stated as a
   --  quotient so that it never overflows.
   function Log_Fits (Cap : Data_Size; Slice : Slice_Count; Log_Cap : Log_Size)
     return Boolean
   is
     (Log_Cap >= Header_Len + Expire_Len
      and then (Log_Cap - Header_Len - Expire_Len) / Entry_Max
               >= Cap + Signers_Max * Slice + 1);

   --  The result is No_Space only at a bound (T13), after the admission,
   --  duplicate and domination tests: a record that Frontier.Apply refuses
   --  for the data row.
   function At_Bound (S : Store; F : Frontier.State; H : Header; Len : Natural) return Boolean is
     (not Holds (F, H) and then not Dom (F, H)
      and then not Expired (H, Horizon (S)) and then Data_Full (F, H))
     with Pre => Len <= Kome.Records.Frame_Max;

   --  The result is Log_Full only when F can take the record but its entry
   --  does not fit the log: an expired DEL that drops a record and has no
   --  log room for its APPLY_EXPIRED, or a record that Frontier can hold,
   --  but its APPLY does not fit.
   function At_Log_Bound (S : Store; F : Frontier.State; H : Header; Len : Natural)
     return Boolean
   is
     (not Holds (F, H) and then not Dom (F, H)
      and then (if Expired (H, Horizon (S))
                then Drops_Any (F, H) and then Log_Short (S, Apply_Prefix + Len)
                else not Data_Full (F, H) and then not Auth_Rule (F, H)
                     and then not Gen_Full (S, H)
                     and then Log_Short (S, Apply_Prefix + Len)))
     with Pre => Len <= Kome.Records.Frame_Max;

   --  The refinement statement of Frontier.Apply (Frontier.lean `applyA` /
   --  `keep`; T4'): the registers grow exactly by H. Each held record was
   --  held before or is H. A held record leaves only by domination.
   function Applied (Old_F, New_F : Frontier.State; H : Header) return Boolean is
     (Ceil (Regs (New_F)) = U48'Max (Ceil (Regs (Old_F)), Ceil_Of (H))
      and then Extends (Regs (Old_F), Regs (New_F))
      and then (for all I in 1 .. Count (New_F) =>
                  Holds (Old_F, Held (New_F, I)) or else Held (New_F, I) = H)
      and then (for all I in 1 .. Count (Old_F) =>
                  Holds (New_F, Held (Old_F, I)) or else Dominates (H, Held (Old_F, I))));

   --  The effect of Frontier.Apply_Expired (apply-then-expire): exactly
   --  the records that H dominates leave F. H is not held, and the
   --  registers do not change.
   function Expired_Applied (Old_F, New_F : Frontier.State; H : Header) return Boolean is
     (Ceil (Regs (New_F)) = Ceil (Regs (Old_F))
      and then Extends (Regs (Old_F), Regs (New_F))
      and then Extends (Regs (New_F), Regs (Old_F))
      and then not Holds (New_F, H)
      and then (for all I in 1 .. Count (New_F) =>
                  Holds (Old_F, Held (New_F, I)) and then not Dominates (H, Held (New_F, I)))
      and then (for all I in 1 .. Count (Old_F) =>
                  Holds (New_F, Held (Old_F, I)) or else Dominates (H, Held (Old_F, I))));

   --  The effect of tombstone expiry (T11 (a)): exactly the DELs with
   --  t <= Hz leave F. The registers do not change.
   function Expired_Out (Old_F, New_F : Frontier.State; Hz : Time64) return Boolean is
     (Ceil (Regs (New_F)) = Ceil (Regs (Old_F))
      and then Extends (Regs (Old_F), Regs (New_F))
      and then Extends (Regs (New_F), Regs (Old_F))
      and then (for all I in 1 .. Count (New_F) =>
                  Holds (Old_F, Held (New_F, I)) and then not Expired (Held (New_F, I), Hz))
      and then (for all I in 1 .. Count (Old_F) =>
                  Holds (New_F, Held (Old_F, I)) or else Expired (Held (Old_F, I), Hz)));

   --  At least one held DEL is expired at Hz.
   function Expires_Any (F : Frontier.State; Hz : Time64) return Boolean is
     (for some I in 1 .. Count (F) => Expired (Held (F, I), Hz));

   --  The expiry horizon of DESIGN.md §7 (D10), in 64 bits:
   --  min (now_local, maxceil (F)) - del_ttl_eff (F), or none if this
   --  value is below 0.
   function Horizon_At (F : Frontier.State; Now : U48) return Horizon_Value is
     (if Time64'Min (Time64 (Now), Time64 (Ceil (Regs (F))))
           - Time64 (Kome.Views.Del_TTL_Eff (F)) < 0
      then No_Horizon
      else Time64'Min (Time64 (Now), Time64 (Ceil (Regs (F))))
           - Time64 (Kome.Views.Del_TTL_Eff (F)))
     with Pre => Is_Frontier (F);

   --  The clamp of the horizon is active (AUDIT.md N4): Expire (Now) would
   --  bound the horizon by maxceil (F), not by Now. Advisory, for the
   --  binding (shown beside Kome.Views.Ceiling_Stale): the horizon stays
   --  where it is until a root raises the ceiling.
   function Horizon_Frozen (F : Frontier.State; Now : U48) return Boolean is
     (Now > Ceil (Regs (F)))
     with Global => null, Pre => Is_Frontier (F);

   --  Expire (Now) logs EXPIRE. It does this if it raises the horizon and
   --  removes a record, or if it lowers the horizon.
   function Logs_Expire (S : Store; F : Frontier.State; Now : U48) return Boolean is
     ((Horizon_At (F, Now) > Horizon (S) and then Expires_Any (F, Horizon_At (F, Now)))
      or else Horizon_At (F, Now) < Horizon (S))
     with Pre => Is_Frontier (F);

   --  The log of New_S extends the log of Old_S: no written byte changes,
   --  and each entry stays at its offset.
   function Log_Extends (Old_S, New_S : Store) return Boolean is
     (Log_Length (New_S) >= Log_Length (Old_S)
      and then (for all J in 0 .. Log_Length (Old_S) - 1 =>
                  Log_Byte (New_S, J) = Log_Byte (Old_S, J))
      and then Log_Entries (New_S) >= Log_Entries (Old_S)
      and then (for all K in 1 .. Log_Entries (Old_S) =>
                  Entry_Start (New_S, K) = Entry_Start (Old_S, K)));

   --  One entry of Size bytes was appended at Off, as the new last entry.
   function Grew_By (Old_S, New_S : Store; Off, Size : Natural) return Boolean is
     (Off = Log_Length (Old_S)
      and then Log_Length (New_S) >= Off
      and then Log_Length (New_S) - Off = Size
      and then Log_Entries (New_S) = Log_Entries (Old_S) + 1
      and then Entry_Start (New_S, Log_Entries (New_S)) = Off);

   --  The bytes of Frame are the frame of the entry at Off.
   function Frame_Stored (S : Store; Off : Natural; Frame : Byte_Array) return Boolean is
     (Off < Log_Length (S)
      and then Log_Length (S) - Off >= Apply_Prefix + Frame'Length
      and then Len_At (S, Off) = Word (Frame'Length)
      and then (for all K in 0 .. Frame'Length - 1 =>
                  Log_Byte (S, Off + Apply_Prefix + K) = Frame (Frame'First + K)))
     with Pre => Frame'Length in Frame_Size;

   --  APPLY (Frame) was appended at Off and indexed as the new last entry.
   function Appended
     (Old_S, New_S : Store; Frame : Byte_Array; H : Header; Off : Natural) return Boolean is
     (Grew_By (Old_S, New_S, Off, Apply_Prefix + Frame'Length)
      and then Op_At (New_S, Off) = Op_Apply
      and then Frame_Stored (New_S, Off, Frame)
      and then Entries (New_S) >= 1
      and then Entry_At (New_S, Entries (New_S)) = (H => H, Off => Off, Len => Frame'Length))
     with Pre => Frame'Length in Frame_Size;

   --  APPLY_EXPIRED (Frame) was appended at Off; it is not indexed.
   function Appended_Expired
     (Old_S, New_S : Store; Frame : Byte_Array; Off : Natural) return Boolean is
     (Grew_By (Old_S, New_S, Off, Apply_Prefix + Frame'Length)
      and then Op_At (New_S, Off) = Op_Apply_Expired
      and then Frame_Stored (New_S, Off, Frame))
     with Pre => Frame'Length in Frame_Size;

   --  EXPIRE (Hz) was appended at Off.
   function Appended_Expire
     (Old_S, New_S : Store; Off : Natural; Hz : Horizon_Value) return Boolean is
     (Grew_By (Old_S, New_S, Off, Expire_Len)
      and then Op_At (New_S, Off) = Op_Expire
      and then Code_At (New_S, Off + 1) = Horizon_Code (Hz));

   --  A (PA .. PA + Len - 1) = B (PB .. PB + Len - 1) in the two logs.
   --  Its Post defines it (one atom for each range in goals that carry
   --  it).
   function Same_Bytes (A : Store; PA : Natural; B : Store; PB : Natural; Len : Natural)
     return Boolean
   with
     Global => null,
     Pre  => PA <= Log_Length (A) and then Len <= Log_Length (A) - PA
             and then PB <= Log_Length (B) and then Len <= Log_Length (B) - PB,
     Post => Same_Bytes'Result =
       (for all K in 0 .. Len - 1 => Log_Byte (A, PA + K) = Log_Byte (B, PB + K));

   --  The offset where the frames of a compacted log end.
   function Body_End (S : Store) return Natural is
     (if Entries (S) = 0 then Header_Len else End_Of (Entry_At (S, Entries (S))));

   --  The index clause of Compact: the same records, frame for frame, byte
   --  for byte, with the authorization records first. Its Post defines it
   --  (one atom in the contract of Compact; Lemma_Compact_Index in the
   --  body proves it, so that no goal of the Post carries the whole
   --  clause, AUDIT.md G17). The order inside each part is not stated:
   --  nothing uses it (AUDIT.md A28).
   function Compact_Index (Old_S, S : Store) return Boolean
   with
     Ghost, Global => null,
     Post => Compact_Index'Result =
       ((for all J in 1 .. Entries (Old_S) => Indexed (S, Entry_At (Old_S, J).H))
        and then (for all I in 1 .. Entries (S) =>
                    Indexed (Old_S, Entry_At (S, I).H)
                    and then Entry_At (Old_S, Position (Old_S, Entry_At (S, I).H)).Len
                             = Entry_At (S, I).Len
                    and then End_Of (Entry_At (S, I)) <= Log_Length (S)
                    and then End_Of (Entry_At (Old_S, Position (Old_S, Entry_At (S, I).H)))
                             <= Log_Length (Old_S)
                    and then Same_Bytes (S, Entry_At (S, I).Off,
                                         Old_S,
                                         Entry_At (Old_S, Position (Old_S, Entry_At (S, I).H)).Off,
                                         Apply_Prefix + Entry_At (S, I).Len))
        and then (for all I in 1 .. Entries (S) =>
                    (for all J in I + 1 .. Entries (S) =>
                       (if Is_Data (Entry_At (S, I).H) then Is_Data (Entry_At (S, J).H)))));

   --  The layout clause of Compact: the HEADER bytes, the APPLYs with no
   --  gaps, then EXPIRE (horizon) if the store has a horizon and the log
   --  has room for it. Its Post defines it (Lemma_Compact_Layout proves
   --  it). The last conjunct is the lemma of DESIGN.md §10 item 10 (b)
   --  (AUDIT.md G23): Compact omits a horizon only when the old log had
   --  fewer than Expire_Len bytes beyond the HEADER and the held APPLYs,
   --  that is, only in the full-log state of AUDIT.md H3 (every entry is
   --  at least Min_Entry bytes, so the old log was the HEADER, the held
   --  APPLYs and at most one entry that is not a record). Under Log_Fits
   --  this state is unreachable.
   function Compact_Layout (Old_S, S : Store) return Boolean
   with
     Ghost, Global => null,
     Post => Compact_Layout'Result =
       (Log_Length (S) >= Header_Len
        and then Log_Length (Old_S) >= Header_Len
        and then Body_End (S) <= Log_Length (Old_S)
        and then (for all K in 0 .. Header_Len - 1 => Log_Byte (S, K) = Log_Byte (Old_S, K))
        and then (if Entries (S) > 0 then Entry_At (S, 1).Off = Header_Len)
        and then (for all I in 1 .. Entries (S) - 1 =>
                    Entry_At (S, I + 1).Off = End_Of (Entry_At (S, I)))
        and then (for all I in 1 .. Entries (S) =>
                    I + 1 <= Log_Entries (S)
                    and then Entry_Start (S, I + 1) = Entry_At (S, I).Off)
        and then (if Horizon (S) >= 0 and then S.Log_Cap - Body_End (S) >= Expire_Len
                  then Log_Length (S) >= Body_End (S)
                       and then Log_Length (S) - Body_End (S) = Expire_Len
                       and then Log_Entries (S) = Entries (S) + 2
                       and then Op_At (S, Body_End (S)) = Op_Expire
                       and then Code_At (S, Body_End (S) + 1) = Horizon_Code (Horizon (S))
                  else Log_Length (S) = Body_End (S)
                       and then Log_Entries (S) = Entries (S) + 1)
        and then (if Horizon (S) >= 0 and then Log_Length (S) = Body_End (S)
                  then Log_Length (Old_S) - Body_End (S) < Expire_Len));

   ---------------------------------------------------------------------------
   --  Operations.
   ---------------------------------------------------------------------------

   --  A new store for the collection of (Root_PK, Salt), beside the empty
   --  lattice state F (Frontier.Empty (ns, To_Key256 (Root_PK), Cap,
   --  Slice)). It writes the HEADER with the capacities of F. The
   --  precondition connects F to the founding key, so the decoder, the
   --  capacity rows and root_void agree on the founding key (DESIGN.md §7
   --  step 0, and E6 of §1).
   procedure Open (Root_PK : Pubkey; Salt : Kome.Salt; F : Frontier.State; S : out Store) with
     Global => null,
     Pre  => Is_Frontier (F)
       and then Count (F) = 0
       and then Kome.Keys.To_Id128 (Kome.Records.Collection_Id (Root_PK, Salt)) = Collection (F)
       and then Kome.Keys.To_Key256 (Root_PK) = Frontier.Founding (F)
       and then S.Cap >= F.Cap + Signers_Max * F.Slice
       and then S.Log_Cap >= Header_Len,
     Post => Valid (S, F)
       and then Collection (S) = Collection (F)
       and then Founding (S) = Frontier.Founding (F)
       and then Root_Key (S) = Root_PK
       and then Salt_Of (S) = Salt
       and then Logged_Cap (S) = F.Cap
       and then Logged_Slice (S) = F.Slice
       and then Entries (S) = 0
       and then Log_Length (S) = Header_Len
       and then Log_Entries (S) = 1
       and then Horizon (S) = No_Horizon
       and then Auth_Gen (S) = 0
       and then Expire_Mark (S) = 0;

   --  Apply one record and store its frame (DESIGN.md §7, steps 0-6 above).
   --  Before the call, the caller decodes and verifies Frame (Verified,
   --  that is, what Kome.Records.Decode_Verified accepts). The caller
   --  gives the header H of Frame. Off is always the log length before
   --  the call: the offset of the appended entry, if the call appended
   --  one (AUDIT.md G22).
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
       and then Verified (Frame)
       and then Header_Of (Frame) = H
       and then Kome.Records.Kind_Of (Frame) = H.K
       and then Canonical (H)
       and then H.NS = Collection (S),
     --  The top-level conjuncts use "and" (each conjunct guards its own
     --  preconditions). The functions above name the long conjuncts.
     Post => Valid (S, F)
       and Same_Identity (S'Old, S)
       and Horizon (S) = Horizon (S'Old)
       and Off = Log_Length (S'Old)
       and Result in OK | Dominated | Inadmissible | Malformed | No_Space | Auth_Full | Log_Full
       --  The order of DESIGN.md §7, each outcome as an iff.
       and (Result = Malformed) = Foreign_Root (S'Old, Frame)
       and (Result = Inadmissible)
             = (not Foreign_Root (S'Old, Frame) and then not Admitted (F'Old, H))
       and (Result = Dominated)
             = (not Foreign_Root (S'Old, Frame) and then Admitted (F'Old, H)
                and then not Holds (F'Old, H) and then Dom (F'Old, H))
       and (Result = Auth_Full)
             = (not Foreign_Root (S'Old, Frame) and then not Holds (F'Old, H)
                and then not Dom (F'Old, H)
                and then (Auth_Rule (F'Old, H) or else Gen_Full (S'Old, H)))
       and (Result = No_Space)
             = (not Foreign_Root (S'Old, Frame) and then Admitted (F'Old, H)
                and then At_Bound (S'Old, F'Old, H, Frame'Length))
       and (Result = Log_Full)
             = (not Foreign_Root (S'Old, Frame) and then Admitted (F'Old, H)
                and then At_Log_Bound (S'Old, F'Old, H, Frame'Length))
       --  Nothing changes on a refusal, on a duplicate, or for an expired
       --  DEL that drops nothing (T13).
       and (if Result /= OK or else Holds (F'Old, H)
               or else (Expired (H, Horizon (S'Old)) and then not Drops_Any (F'Old, H))
            then Unchanged (F'Old, F) and then S = S'Old)
       --  Append-only.
       and Log_Extends (S'Old, S)
       --  The counters (AUDIT.md H11, H28): Auth_Gen goes up by one iff
       --  the call held an authorization record; Expire_Mark rises to the
       --  t of a DEL applied for its effect, and otherwise stays.
       and (if Result = OK and then not Holds (F'Old, H) and then Is_Auth (H)
            then Auth_Gen (S'Old) < Auth_Gen_Max and then Auth_Gen (S) = Auth_Gen (S'Old) + 1
            else Auth_Gen (S) = Auth_Gen (S'Old))
       and (if Result = OK and then not Holds (F'Old, H)
               and then Expired (H, Horizon (S'Old)) and then Drops_Any (F'Old, H)
            then Expire_Mark (S) = U48'Max (Expire_Mark (S'Old), H.V.T)
            else Expire_Mark (S) = Expire_Mark (S'Old))
       --  OK: held and indexed, or an expired DEL applied for its effect.
       and (if Result = OK and then not Holds (F'Old, H) then
              (if Expired (H, Horizon (S'Old))
               then (if Drops_Any (F'Old, H)
                     then Expired_Applied (F'Old, F, H)
                          and then Appended_Expired (S'Old, S, Frame, Off))
               else Holds (F, H)
                    and then Indexed (S, H)
                    and then Applied (F'Old, F, H)
                    and then Appended (S'Old, S, Frame, H, Off)));

   --  Tombstone expiry at local time Now (D10, DESIGN.md §7, T11 (a)). The
   --  new horizon is Horizon_At (F, Now):
   --    * if it is higher, Expire removes the expired DELs from F and the
   --      index, and logs EXPIRE iff it removed a record;
   --    * if it is lower, Expire sets it and logs EXPIRE;
   --    * if it is equal, Expire changes nothing.
   --  If the EXPIRE entry that Expire must log does not fit, the result is
   --  Log_Full and nothing changes.
   procedure Expire
     (S      : in out Store;
      F      : in out Frontier.State;
      Now    : in     U48;
      Result :    out Status)
   with
     Global => null,
     Pre  => Valid (S, F),
     Post => Valid (S, F)
       and Same_Identity (S'Old, S)
       and Auth_Gen (S) = Auth_Gen (S'Old)
       and Result in OK | Log_Full
       and (Result = Log_Full)
             = (Logs_Expire (S'Old, F'Old, Now) and then Log_Short (S'Old, Expire_Len))
       and (if Result = Log_Full then Unchanged (F'Old, F) and then S = S'Old)
       and Log_Extends (S'Old, S)
       and (if Result = OK then
              Horizon (S) = Horizon_At (F'Old, Now)
              --  AUDIT.md H24: the horizon that Expire writes is at most
              --  maxceil - del_ttl_eff of the frontier it was computed
              --  on, so the clamp of replay never lowers it on the same
              --  frontier.
              and then Horizon (S) <= Horizon_At (F'Old, U48'Last)
              --  The held set is the old set minus exactly the DELs at or
              --  below the new horizon (none if the horizon did not rise).
              and then Expired_Out (F'Old, F, Horizon (S))
              and then (if Logs_Expire (S'Old, F'Old, Now)
                        then Appended_Expire (S'Old, S, Log_Length (S'Old), Horizon (S))
                        else Log_Length (S) = Log_Length (S'Old)
                             and then Log_Entries (S) = Log_Entries (S'Old))
              --  AUDIT.md H28: the mark rises to the new horizon iff the
              --  call raised the horizon (every DEL removed is at or
              --  below it), and otherwise stays.
              and then (if Horizon (S) > Horizon (S'Old)
                        then Expire_Mark (S) = U48'Max (Expire_Mark (S'Old), U48 (Horizon (S)))
                        else Expire_Mark (S) = Expire_Mark (S'Old)))
       and Expire_Mark (S) >= Expire_Mark (S'Old)
       --  T11 (a): no held DEL is at or below the horizon.
       and (for all I in 1 .. Count (F) => not Expired (Held (F, I), Horizon (S)));

   --  Write the log again as: the HEADER; one APPLY for each index entry
   --  (first all authorization records, then all data records, each part
   --  in index order); and one EXPIRE (Horizon (S)) if the store has a
   --  horizon and the log has room for it. The frontier does not change.
   procedure Compact (S : in out Store; F : Frontier.State) with
     Global => null,
     Pre  => Valid (S, F),
     Post => Valid (S, F)
       and Same_Identity (S'Old, S)
       and Horizon (S) = Horizon (S'Old)
       and Auth_Gen (S) = Auth_Gen (S'Old)
       and Expire_Mark (S) = Expire_Mark (S'Old)
       and Entries (S) = Entries (S'Old)
       --  The same records, frame for frame, byte for byte, authorization
       --  records first (Compact_Index); the layout (Compact_Layout).
       and Compact_Index (S'Old, S)
       and Compact_Layout (S'Old, S)
       --  AUDIT.md H26: a compacted log is never due for compaction.
       and not Compact_Due (S);

   --  The capacities that the HEADER of a log records.
   function Header_Cap (Input : Byte_Array) return Word is
     (Kome.Keys.Word_Of (Input (HO_Cap), Input (HO_Cap + 1),
                         Input (HO_Cap + 2), Input (HO_Cap + 3)))
     with Pre => Input'First = 0 and then Input'Last >= Header_Len - 1;

   function Header_Slice (Input : Byte_Array) return Kome.Records.U16_Value is
     (Kome.Records.U16_Of (Input (HO_Slice), Input (HO_Slice + 1)))
     with Pre => Input'First = 0 and then Input'Last >= Header_Len - 1;

   --  Input starts with a HEADER: its op, magic and version, an ns that
   --  is BLAKE2b-256 (root_pk ‖ salt)[0:16] of its root_pk and salt, and
   --  a data_cap in the range of Data_Size. These are the checks that
   --  Open_From_Log does on the bytes of the HEADER. (The slice is a
   --  check against the slice of this open, below.)
   function Header_Well_Formed (Input : Byte_Array) return Boolean is
     (Input'Last >= Header_Len - 1
      and then Input (0) = Op_Header
      and then Input (HO_Magic .. HO_Magic + Magic_Len - 1) = Magic
      and then Input (HO_Version) = Log_Version
      and then Input (HO_NS .. HO_NS + NS_Len - 1) =
                 Kome.Records.Collection_Id (Input (HO_Root .. HO_Root + Pubkey_Len - 1),
                                             Input (HO_Salt .. HO_Salt + Salt_Len - 1))
      and then Header_Cap (Input) <= Word (Data_Size'Last))
     with Pre => Input'First = 0;

   --  The K-th entry of the log is an EXPIRE entry.
   function Is_Expire (S : Store; K : Positive) return Boolean is
     (K <= Log_Entries (S)
      and then Entry_Start (S, K) < Log_Length (S)
      and then Log_Length (S) - Entry_Start (S, K) >= Expire_Len
      and then Op_At (S, Entry_Start (S, K)) = Op_Expire);

   --  The horizon that the K-th entry (an EXPIRE) logs.
   function Expire_Horizon (S : Store; K : Positive) return Horizon_Value is
     (Horizon_Of_Code (Code_At (S, Entry_Start (S, K) + 1)))
     with Pre => Is_Expire (S, K);

   --  Horizon (S) is at most the horizon of the last EXPIRE entry of the
   --  log, or none if the log has no EXPIRE entry. (This is true for a
   --  replayed store: replay clamps each logged horizon to the bound of
   --  its frontier, AUDIT.md H24, and the EXPIREs that a store writes
   --  meet the bound, so the horizon of the last EXPIRE is reached unless
   --  del_ttl_eff rose after it. A live store can have a higher horizon
   --  that is only in memory, DESIGN.md §7.)
   function Horizon_Logged (S : Store) return Boolean is
     (if (for some K in 1 .. Log_Entries (S) => Is_Expire (S, K))
      then (for some K in 1 .. Log_Entries (S) =>
              Is_Expire (S, K)
              and then Horizon (S) <= Expire_Horizon (S, K)
              and then (for all K2 in K + 1 .. Log_Entries (S) => not Is_Expire (S, K2)))
      else Horizon (S) = No_Horizon);

   --  Open a store again from its log (replay, T18). The discriminants of
   --  F and S are the capacities for this open (AUDIT.md A11):
   --    * the slice is fixed for a collection (DESIGN.md §7 requires the
   --      same slice at every replica; a binding opens with Slice_Max).
   --      The HEADER's slice field is only a check: a HEADER whose slice
   --      is not F.Slice is refused (No_Space);
   --    * the data capacity of this open can be above or below the logged
   --      one. The HEADER keeps the data_cap of the open that wrote it
   --      (the log is never rewritten in place). If the log does not
   --      replay at F.Cap (the data row is full for an APPLY), the result
   --      is No_Space, and Valid_Length names the prefix that did replay.
   --  The result is also No_Space when the log does not fit S, that is,
   --  Input'Last >= S.Log_Cap (because Input'First = 0).
   --  The result is Malformed for:
   --    * a HEADER that is not a HEADER (op, magic, version,
   --      ns = BLAKE2b-256 (root_pk ‖ salt)[0:16], a data_cap in range);
   --    * an entry that does not parse;
   --    * a frame that is not well-formed or not of the collection;
   --    * an authorization record whose root_pk is not the founding key;
   --    * an APPLY that Put_Frame would not hold and index as a new
   --      record, except an APPLY of a record that is already held: as
   --      the live Put_Frame does (OK, no change), replay keeps the entry
   --      in the log and changes nothing else (AUDIT.md H23: a binding
   --      that retried an append after a write error);
   --    * an APPLY_EXPIRED that is not an admitted, undominated DEL.
   --  Replay accepts an APPLY_EXPIRED of an admitted, undominated DEL that
   --  drops nothing. This entry changes only the log. No store writes such
   --  an entry, because Put_Frame logs APPLY_EXPIRED only when it drops a
   --  record.
   --  Replay clamps each EXPIRE horizon to Horizon_At (F, U48'Last), the
   --  bound maxceil - del_ttl_eff of the frontier at that point (AUDIT.md
   --  H24), so a torn or corrupt EXPIRE cannot drop every DEL. Every
   --  EXPIRE that Expire writes meets the bound (its Post), so replay of
   --  a store's own log reaches the same horizons, unless a later roster
   --  raised del_ttl_eff; then the reopened horizon is lower, which T18
   --  allows (DESIGN.md §10 item 10 (b)).
   --  Valid_Length (AUDIT.md H23) is the length of the longest prefix of
   --  Input at an entry boundary that replays: on OK the whole input; on
   --  Malformed or on No_Space from an entry, the start of the refused
   --  entry (at least the HEADER). When it is positive, (S, F) is the
   --  replay of exactly that prefix, Valid, with that prefix as its log.
   --  A binding that finds a torn tail truncates the file to Valid_Length
   --  and opens again, or uses (S, F) as they are. It is 0 when the HEADER
   --  is refused or the log does not fit.
   --  On OK, the pair is Valid, the horizon is at most the last logged
   --  horizon, and the log is the input byte for byte.
   procedure Open_From_Log
     (Input        : in     Byte_Array;
      F            :    out Frontier.State;
      S            :    out Store;
      Valid_Length :    out Log_Size;
      Result       :    out Status)
   with
     Global => null,
     Pre  => Input'First = 0
       and then F.Slice >= 1
       and then F.Cap + Signers_Max * F.Slice <= Held_Max
       and then S.Cap >= F.Cap + Signers_Max * F.Slice,
     Post => Result in OK | Malformed | No_Space
       and (if Input'Last >= S.Log_Cap then Result = No_Space)
       --  Part of completeness: a log that is only a well-formed HEADER,
       --  with the slice of this open, opens. The result is Malformed only
       --  for a HEADER that is not a HEADER, or for a log that has entries
       --  after the HEADER.
       and (if Input'Last = Header_Len - 1
              and then Input'Last < S.Log_Cap
              and then Header_Well_Formed (Input)
              and then Header_Slice (Input) = F.Slice
            then Result = OK)
       and (if Result = Malformed then
              not Header_Well_Formed (Input) or else Input'Last >= Header_Len)
       and (if Result = No_Space then
              Input'Last >= S.Log_Cap
              or else (Input'Last >= Header_Len - 1 and then Header_Slice (Input) /= F.Slice)
              or else Input'Last >= Header_Len)
       and Valid_Length - 1 <= Input'Last
       and (if Result = OK then Valid_Length - 1 = Input'Last)
       --  T18-prefix (AUDIT.md H23): the replayed prefix is a log.
       and (if Valid_Length > 0 then
              Valid (S, F)
              and then Valid_Length >= Header_Len
              and then Input'Last < S.Log_Cap
              and then Header_Well_Formed (Input)
              and then Header_Slice (Input) = F.Slice
              and then Log_Length (S) = Valid_Length
              and then (for all J in 0 .. Valid_Length - 1 => Log_Byte (S, J) = Input (J))
              and then Word (Logged_Cap (S)) = Header_Cap (Input)
              and then Logged_Slice (S) = F.Slice
              and then Horizon_Logged (S));

   --  The cell index (DESIGN.md §7 "cell -> (offset, v)"): the entry of
   --  the PUT on (NS, Ent, FH), if there is one.
   procedure Find_Cell
     (S     : in     Store;
      F     : in     Frontier.State;
      NS    : in     Id128;
      Ent   : in     Id128;
      FH    : in     Key256;
      Found :    out Boolean;
      I     :    out Held_Count)
   with
     Global => null,
     Pre  => Valid (S, F),
     Post => (if Found
              then I in 1 .. Entries (S)
                   and then Kome.Views.Put_On (Entry_At (S, I).H, NS, Ent, FH)
                   and then (for all J in 1 .. Entries (S) =>
                               (if Kome.Views.Put_On (Entry_At (S, J).H, NS, Ent, FH)
                                then J = I))
              else I = 0
                   and then (for all J in 1 .. Entries (S) =>
                               not Kome.Views.Put_On (Entry_At (S, J).H, NS, Ent, FH)));

   ---------------------------------------------------------------------------
   --  The invariant, unpacked.
   ---------------------------------------------------------------------------

   --  The pair's identity and capacities.
   procedure Lemma_Valid_Facts (S : Store; F : Frontier.State) with
     Ghost, Global => null,
     Pre  => Valid (S, F),
     Post => Is_Frontier (F)
       and then Collection (F) = Collection (S)
       and then Frontier.Founding (F) = Founding (S)
       and then Founding (S) = Kome.Keys.To_Key256 (Root_Key (S))
       and then Collection (S) =
                  Kome.Keys.To_Id128 (Kome.Records.Collection_Id (Root_Key (S), Salt_Of (S)))
       and then Logged_Slice (S) = F.Slice
       and then S.Cap >= F.Cap + Signers_Max * F.Slice
       and then Log_Length (S) >= Header_Len;

   --  The HEADER's bytes.
   procedure Lemma_Log_Header (S : Store; F : Frontier.State) with
     Ghost, Global => null,
     Pre  => Valid (S, F),
     Post => Log_Length (S) >= Header_Len
       and then Op_At (S, 0) = Op_Header
       and then (for all J in 0 .. Magic_Len - 1 => Log_Byte (S, HO_Magic + J) = Magic (J))
       and then Log_Byte (S, HO_Version) = Log_Version
       and then (for all J in 0 .. NS_Len - 1 =>
                   Log_Byte (S, HO_NS + J) =
                     Kome.Records.Collection_Id (Root_Key (S), Salt_Of (S)) (J))
       and then (for all J in 0 .. Pubkey_Len - 1 =>
                   Log_Byte (S, HO_Root + J) = Root_Key (S) (J))
       and then (for all J in 0 .. Salt_Len - 1 =>
                   Log_Byte (S, HO_Salt + J) = Salt_Of (S) (J))
       and then Kome.Keys.Word_Of (Log_Byte (S, HO_Cap), Log_Byte (S, HO_Cap + 1),
                                   Log_Byte (S, HO_Cap + 2), Log_Byte (S, HO_Cap + 3))
                = Word (Logged_Cap (S))
       and then Kome.Records.U16_Of (Log_Byte (S, HO_Slice), Log_Byte (S, HO_Slice + 1))
                = Logged_Slice (S);

   --  Each index entry is a held record. Its APPLY entry is one of the
   --  entries of the log, with its length and the tag of its kind.
   procedure Lemma_Entry_Held (S : Store; F : Frontier.State; I : Held_Index) with
     Ghost, Global => null,
     Pre  => Valid (S, F) and then I <= Entries (S),
     Post => Holds (F, Entry_At (S, I).H)
       and then Has_Frame (S, Entry_At (S, I).Off)
       and then Op_At (S, Entry_At (S, I).Off) = Op_Apply
       and then Natural (Len_At (S, Entry_At (S, I).Off)) = Entry_At (S, I).Len
       and then Log_Byte (S, Entry_At (S, I).Off + Apply_Prefix) =
                  Kome.Records.Tag_Of (Entry_At (S, I).H.K)
       and then (for some K in 1 .. Log_Entries (S) =>
                   Entry_Start (S, K) = Entry_At (S, I).Off);

   --  Every held record is indexed (the index is F) ...
   procedure Lemma_Held_Indexed (S : Store; F : Frontier.State; K : Held_Index) with
     Ghost, Global => null,
     Pre  => Valid (S, F) and then K <= Count (F),
     Post => Indexed (S, Held (F, K));

   --  ... and none is a DEL at or below the horizon (T11 (a)).
   procedure Lemma_No_Expired (S : Store; F : Frontier.State; K : Held_Index) with
     Ghost, Global => null,
     Pre  => Valid (S, F) and then K <= Count (F),
     Post => not Expired (Held (F, K), Horizon (S));

   --  The full definition of Indexed.
   procedure Lemma_Indexed (S : Store; X : Header) with
     Ghost, Global => null,
     Post => Indexed (S, X) = (for some I in 1 .. Entries (S) => Entry_At (S, I).H = X);

   --  Entries are distinct, so an indexed record has one position.
   procedure Lemma_Position (S : Store; F : Frontier.State; I : Held_Index) with
     Ghost, Global => null,
     Pre  => Valid (S, F) and then I <= Entries (S),
     Post => Indexed (S, Entry_At (S, I).H)
             and then Position (S, Entry_At (S, I).H) = I;

   --  The log is a chain of entries from offset 0 to its length. The
   --  HEADER is first and only there. A reader that scans the log as a
   --  file relies on this fact.
   procedure Lemma_Scan (S : Store; F : Frontier.State) with
     Ghost, Global => null,
     Pre  => Valid (S, F),
     Post => Log_Entries (S) >= 1
       and then Entry_Start (S, 1) = 0
       and then (for all K in 1 .. Log_Entries (S) =>
                   Has_Log_Entry (S, Entry_Start (S, K))
                   and then (Op_At (S, Entry_Start (S, K)) = Op_Header) = (K = 1)
                   and then Next_Offset (S, Entry_Start (S, K)) =
                              (if K < Log_Entries (S) then Entry_Start (S, K + 1)
                               else Log_Length (S)));

   --  T5 through the index (Frontier.lean `cell_unique`): a cell has at
   --  most one entry, so "cell -> (offset, v)" is a function.
   procedure Lemma_Cell_Unique (S : Store; F : Frontier.State; I, J : Held_Index) with
     Ghost, Global => null,
     Pre  => Valid (S, F)
             and then I <= Entries (S) and then J <= Entries (S)
             and then Entry_At (S, I).H.K = K_Put
             and then Kome.Views.Put_On (Entry_At (S, J).H, Entry_At (S, I).H.NS,
                                         Entry_At (S, I).H.Ent, Entry_At (S, I).H.FH),
     Post => I = J;

private

   type Entry_Array is array (Held_Index range <>) of Index_Entry;

   --  The entry boundaries of the log, in order. In the model, they replace
   --  the framing of the file (a file binding finds them with a scan). Only
   --  the discriminant sets the size (Ada allows nothing else in a
   --  component constraint). The store uses at most Log_Cap / Min_Entry of
   --  them.
   type Offset_Array is array (Positive range <>) of Log_Size;

   --  No Dynamic_Predicate: the bounds of the counters are part of Valid,
   --  and the accessors clamp, so clients can assign a Store.
   type Store (Cap : Held_Count; Log_Cap : Log_Size) is record
      NS   : Id128;
      NSb  : NS_Id         := [others => 0];   --  ns as bytes, for the HEADER
      Fnd  : Key256;
      Root : Pubkey        := [others => 0];
      Slt  : Salt          := [others => 0];
      DCap : Data_Size     := 0;
      Slc  : Slice_Count   := 0;
      Hz   : Horizon_Value := No_Horizon;
      AG   : Auth_Counter  := 0;       --  Auth_Gen (AUDIT.md H11)
      EM   : U48           := 0;       --  Expire_Mark (AUDIT.md H28)
      NI   : Held_Count    := 0;
      Idx  : Entry_Array (1 .. Cap);
      LL   : Log_Size      := 0;
      Log  : Byte_Array (0 .. Log_Cap);   --  bytes 0 .. LL - 1 are the log
      NB   : Log_Size      := 0;
      Bnd  : Offset_Array (1 .. Log_Cap);  --  Bnd (1 .. NB) are its entries
   end record;

   function Collection (S : Store) return Id128 is (S.NS);
   function Founding (S : Store) return Key256 is (S.Fnd);
   function Root_Key (S : Store) return Pubkey is (S.Root);
   function Salt_Of (S : Store) return Salt is (S.Slt);
   function Logged_Cap (S : Store) return Data_Size is (S.DCap);
   function Logged_Slice (S : Store) return Slice_Count is (S.Slc);
   function Horizon (S : Store) return Horizon_Value is (S.Hz);
   function Auth_Gen (S : Store) return Auth_Counter is (S.AG);
   function Expire_Mark (S : Store) return U48 is (S.EM);
   function Entries (S : Store) return Held_Count is
     (if S.NI <= S.Cap then S.NI else S.Cap);
   function Entry_At (S : Store; I : Held_Index) return Index_Entry is (S.Idx (I));
   function Log_Length (S : Store) return Log_Size is
     (if S.LL <= S.Log_Cap then S.LL else S.Log_Cap);
   function Log_Byte (S : Store; J : Natural) return Byte is (S.Log (J));
   function Log_Entries (S : Store) return Natural is
     (if S.NB <= S.Log_Cap then S.NB else S.Log_Cap);
   function Entry_Start (S : Store; K : Positive) return Log_Size is (S.Bnd (K));

   function Header_Of (Frame : Byte_Array) return Header is
     (case Kome.Records.Kind_Of (Frame) is
        when K_Put    => Kome.Records.To_Header (Kome.Records.Parse_Put (Frame)),
        when K_Del    => Kome.Records.To_Header (Kome.Records.Parse_Del (Frame)),
        when K_Roster => Kome.Records.To_Header (Kome.Records.Parse_Roster (Frame)),
        when K_Revoke => Kome.Records.To_Header (Kome.Records.Parse_Revoke (Frame)),
        when K_Grant  => Kome.Records.To_Header (Kome.Records.Parse_Grant (Frame)));

   ---------------------------------------------------------------------------
   --  The invariant, in parts over explicit components, so that each step
   --  of an operation can make one part true again at a time. Their Posts
   --  define the quantified parts (not expression functions), so a goal
   --  that only carries one part along sees one atom.
   ---------------------------------------------------------------------------

   --  At least one entry of Idx (1 .. N) is the record X. Its Post defines
   --  it, so it stays one atom in goals that only carry it along.
   function Has_Entry (Idx : Entry_Array; N : Held_Count; X : Header) return Boolean
   with
     Global => null,
     Pre  => Idx'First = 1 and then N <= Idx'Last,
     Post => Has_Entry'Result = (for some I in 1 .. N => Idx (I).H = X);

   --  Every entry is a held record.
   function Live (F : Frontier.State; Idx : Entry_Array; N : Held_Count) return Boolean
   with
     Global => null,
     Pre  => Idx'First = 1 and then N <= Idx'Last,
     Post => Live'Result = (for all I in 1 .. N => Holds (F, Idx (I).H));

   --  Every held record is indexed.
   function Covered (F : Frontier.State; Idx : Entry_Array; N : Held_Count) return Boolean
   with
     Global => null,
     Pre  => Idx'First = 1 and then N <= Idx'Last,
     Post => Covered'Result = (for all K in 1 .. Count (F) => Has_Entry (Idx, N, Held (F, K)));

   --  No held DEL is expired at Hz.
   function Fresh (F : Frontier.State; Hz : Time64) return Boolean
   with
     Global => null,
     Post => Fresh'Result = (for all K in 1 .. Count (F) => not Expired (Held (F, K), Hz));

   --  The len:u32 of an APPLY or APPLY_EXPIRED entry at P, that is, the
   --  word at P + 1 .. P + 4 (0 if there is no such word). Total, so its
   --  definition never needs a guard inside a quantifier.
   function Len_Word (Log : Byte_Array; P : Natural) return Word is
     (if P >= Log'First and then P < Log'Last and then Log'Last - P >= 4
      then Kome.Keys.Word_Of (Log (P + 1), Log (P + 2), Log (P + 3), Log (P + 4))
      else 0);

   --  The APPLY of entry E is in Log (0 .. LL - 1), after the HEADER. Its
   --  Post defines it, so a goal about one entry keeps the atom on which
   --  the prover instantiates the quantifier of Framed.
   function Frame_OK (Log : Byte_Array; LL : Log_Size; E : Index_Entry) return Boolean
   with
     Global => null,
     Pre  => Log'First = 0 and then LL <= Log'Last,
     Post => Frame_OK'Result =
       (E.Off >= Header_Len
        and then E.Off <= LL
        and then LL - E.Off >= Apply_Prefix + E.Len
        and then Log (E.Off) = Op_Apply
        and then Len_Word (Log, E.Off) = Word (E.Len)
        and then Log (E.Off + Apply_Prefix) = Kome.Records.Tag_Of (E.H.K));

   function Framed (Log : Byte_Array; LL : Log_Size; Idx : Entry_Array; N : Held_Count)
     return Boolean
   with
     Global => null,
     Pre  => Log'First = 0 and then LL <= Log'Last
             and then Idx'First = 1 and then N <= Idx'Last,
     Post => Framed'Result = (for all I in 1 .. N => Frame_OK (Log, LL, Idx (I)));

   --  The entries are in log order, their APPLYs are disjoint, and their
   --  records are distinct.
   function Sorted (Idx : Entry_Array; N : Held_Count) return Boolean
   with
     Global => null,
     Pre  => Idx'First = 1 and then N <= Idx'Last,
     Post => Sorted'Result =
               (for all I in 1 .. N =>
                  (for all J in I + 1 .. N =>
                     End_Of (Idx (I)) <= Idx (J).Off and then Idx (I).H /= Idx (J).H));

   --  A whole entry starts at P in Log (0 .. LL - 1). Its Post defines it,
   --  as for Frame_OK.
   function Entry_OK (Log : Byte_Array; LL : Log_Size; P : Natural) return Boolean
   with
     Global => null,
     Pre  => Log'First = 0,
     Post => Entry_OK'Result =
       (LL <= Log'Last
        and then P < LL
        and then (if Log (P) = Op_Header then LL - P >= Header_Len
                  elsif Log (P) = Op_Expire then LL - P >= Expire_Len
                  elsif Log (P) = Op_Apply or else Log (P) = Op_Apply_Expired
                  then LL - P >= Apply_Prefix
                       and then Len_Word (Log, P) in 1 .. Kome.Records.Frame_Max
                       and then Natural (Len_Word (Log, P)) <= LL - P - Apply_Prefix
                  else False));

   --  The size of the entry at P (0 if there is no entry). Total.
   function Size_At (Log : Byte_Array; P : Natural) return Natural is
     (if P < Log'First or else P > Log'Last then 0
      elsif Log (P) = Op_Header then Header_Len
      elsif Log (P) = Op_Expire then Expire_Len
      elsif Len_Word (Log, P) <= Kome.Records.Frame_Max
      then Apply_Prefix + Natural (Len_Word (Log, P))
      else 0);

   --  Bnd (1 .. NB) is a chain of entries from 0 to LL: the HEADER is at 0
   --  and at no other offset, and each entry ends where the next starts.
   function Chain (Log : Byte_Array; LL : Log_Size; Bnd : Offset_Array; NB : Natural)
     return Boolean
   with
     Global => null,
     Pre  => Log'First = 0 and then LL <= Log'Last
             and then Bnd'First = 1 and then NB <= Bnd'Last,
     Post => Chain'Result =
       (NB >= 1
        and then NB <= LL / Min_Entry
        and then Bnd (1) = 0
        and then (for all K in 1 .. NB =>
                    Entry_OK (Log, LL, Bnd (K))
                    and then (Log (Bnd (K)) = Op_Header) = (K = 1)
                    and then Bnd (K) + Size_At (Log, Bnd (K)) =
                               (if K < NB then Bnd (K + 1) else LL)));

   --  Each entry's APPLY is one of the chain's entries.
   function At_Bounds (Idx : Entry_Array; N : Held_Count; Bnd : Offset_Array; NB : Natural)
     return Boolean
   with
     Global => null,
     Pre  => Idx'First = 1 and then N <= Idx'Last
             and then Bnd'First = 1 and then NB <= Bnd'Last,
     Post => At_Bounds'Result =
               (for all I in 1 .. N => (for some K in 1 .. NB => Bnd (K) = Idx (I).Off));

   --  The HEADER of the collection NSb of (Root, Slt) with the logged
   --  capacities DCap and Slc is Log (0 .. Header_Len - 1). (The store
   --  keeps ns as bytes beside Root and Slt. BLAKE2b is opaque, so the
   --  prover does not know that a copy of Root has the same Collection_Id
   --  as Root. But the prover knows that two byte arrays with
   --  equal elements are equal.)
   function Head_OK
     (Log : Byte_Array; LL : Log_Size; NSb : NS_Id; Root : Pubkey; Slt : Salt;
      DCap : Data_Size; Slc : Slice_Count) return Boolean
   with
     Global => null,
     Pre  => Log'First = 0 and then LL <= Log'Last,
     Post => Head_OK'Result =
       (LL >= Header_Len
        and then Log (0) = Op_Header
        and then (for all J in 0 .. Magic_Len - 1 => Log (HO_Magic + J) = Magic (J))
        and then Log (HO_Version) = Log_Version
        and then (for all J in 0 .. NS_Len - 1 => Log (HO_NS + J) = NSb (J))
        and then (for all J in 0 .. Pubkey_Len - 1 => Log (HO_Root + J) = Root (J))
        and then (for all J in 0 .. Salt_Len - 1 => Log (HO_Salt + J) = Slt (J))
        and then Kome.Keys.Word_Of (Log (HO_Cap), Log (HO_Cap + 1),
                                    Log (HO_Cap + 2), Log (HO_Cap + 3)) = Word (DCap)
        and then Kome.Records.U16_Of (Log (HO_Slice), Log (HO_Slice + 1)) = Slc);

   function Valid (S : Store; F : Frontier.State) return Boolean is
     (S.NI <= S.Cap
      and then S.LL <= S.Log_Cap
      and then S.NB <= S.Log_Cap
      and then Is_Frontier (F)
      and then Collection (F) = S.NS
      and then Frontier.Founding (F) = S.Fnd
      and then S.Fnd = Kome.Keys.To_Key256 (S.Root)
      and then S.NS = Kome.Keys.To_Id128 (S.NSb)
      and then S.NSb = Kome.Records.Collection_Id (S.Root, S.Slt)
      and then S.Slc = F.Slice
      and then S.Cap >= F.Cap + Signers_Max * F.Slice
      and then Head_OK (S.Log, S.LL, S.NSb, S.Root, S.Slt, S.DCap, S.Slc)
      and then Live (F, S.Idx, S.NI)
      and then Covered (F, S.Idx, S.NI)
      and then Fresh (F, S.Hz)
      and then Framed (S.Log, S.LL, S.Idx, S.NI)
      and then Sorted (S.Idx, S.NI)
      and then Chain (S.Log, S.LL, S.Bnd, S.NB)
      and then At_Bounds (S.Idx, S.NI, S.Bnd, S.NB));

   function Indexed (S : Store; X : Header) return Boolean is
     (Has_Entry (S.Idx, Entries (S), X));

end Kome.Store;
