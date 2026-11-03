--  Kome.Store: the storage model of DESIGN.md §7. One collection's replica
--  is a lattice state F (Kome.Frontier.State) plus a Store: an append-only
--  log that is a journal of the operations performed on F, and an
--  in-memory index from each held record to its frame in the log
--  (DESIGN.md §7: "an in-memory index cell -> (offset, v) that holds
--  exactly the records of F"). Every operation takes the pair (S, F) and
--  Valid (S, F) relates them.
--
--  Why F is a parameter and not a component of Store: gnatprove 14 crashed
--  on a record component of type Frontier.State and on assignments to a
--  State while Frontier.State carried a Dynamic_Predicate (GNAT BUG
--  DETECTED in "generation of Global contracts", einfo-entities.ads:1973).
--  The predicate is gone and assignment no longer crashes (Open_From_Log
--  assigns Frontier.Empty to its out parameter), but a State is still
--  compared only through Frontier.Unchanged, and keeping F beside the
--  Store keeps the store's own state small: Compact takes F in mode `in`,
--  so flow analysis alone proves it leaves the frontier unchanged. Nothing
--  ever needs restoring: Put_Frame and Expire decide every refusal before
--  they change F, so a refused call changes neither S nor F.
--
--  The log (D9, DESIGN.md §7) is a journal, all integers big-endian:
--
--    HEADER         op 0 ‖ "kome/log" ‖ version:u8 (= 1) ‖ ns[16] ‖ root_pk[32]
--                   ‖ salt[16] ‖ data_cap:u32 ‖ slice:u16            (80 bytes)
--    APPLY          op 1 ‖ len:u32 ‖ frame     a record applied and held
--    APPLY_EXPIRED  op 2 ‖ len:u32 ‖ frame     a DEL applied for its effect, not held
--    EXPIRE         op 3 ‖ horizon:u48         Frontier.Expire at horizon, or a
--                                              lowered horizon
--
--  The HEADER is the first entry, exactly once; its ns is BLAKE2b-256
--  (root_pk ‖ salt)[0:16], which fixes the founding key, and its capacities
--  are those the store was last opened with (see Capacities below). A frame is tag ‖ content ‖ sig
--  exactly as Kome.Records encodes it. The horizon u48 2**48 - 1 encodes
--  "no horizon" (a lowered horizon below 0): a real horizon is
--  min (now, maxceil) - del_ttl_eff <= 2**48 - 1 - Del_TTL_Min, so the code
--  is never a horizon (DESIGN.md §7 leaves this encoding open).
--  The log is modelled as a bounded byte buffer written only at its end,
--  so that an OS file can replace it: Put_Frame returns the offset of the
--  entry it appended, Read_Frame reads a frame back, Log_Bytes is the file
--  image, and Compact rewrites the whole log the way a file is rewritten
--  and renamed. The invariant states that the log is a chain of entries
--  from offset 0 to its length (Log_Entries, Entry_Start, Lemma_Scan), the
--  first the HEADER, so a replica can be reopened by scanning it, and every
--  index entry points to one of its APPLY entries.
--
--  The index is F exactly (D9): a record is held iff it has an index entry,
--  entries are distinct, and every entry's APPLY carries its frame. The
--  index capacity covers F (S.Cap >= F.Cap + Signers_Max * F.Slice, Open's
--  precondition), so the index never refuses on its own.
--
--  Order of operations (D11, E1, E2; DESIGN.md §7) for a decoded, verified
--  frame: (0) an authorization record whose root_pk is not the founding
--  key: Malformed; (1) not admitted: Inadmissible; (2) already held: OK, no
--  change; (3) dominated: Dominated, no room needed, never No_Space;
--  (4) a DEL with t <= horizon (expired on arrival): applied for its
--  effect (Frontier.Apply_Expired) and logged as APPLY_EXPIRED if it drops
--  anything, else OK with no change; it needs log room only; (5) room:
--  Frontier's own rules (No_Space for the data row, Auth_Full for a signer's
--  slice, the slot table or W), then the log bytes (No_Space); (6) apply,
--  append APPLY, index it, and drop the index entries of the records it
--  dominated. Every refusal changes nothing (T13): the Post says
--  Unchanged (F'Old, F) and S = S'Old.
--
--  Expiry (D10, DESIGN.md §7, T11): Expire (Now) computes, in 64 bits,
--  horizon := min (now, maxceil (F)) - del_ttl_eff (F), or "none" if that
--  is below 0. A higher horizon removes from F (Frontier.Expire) and from
--  the index exactly the DELs with t <= horizon; a lower one only lowers
--  the store's horizon, so fewer arriving DELs expire on arrival. EXPIRE is
--  logged iff the call removed something or lowered the horizon, so
--  periodic calls do not grow the log; a raise that removed nothing is kept
--  in memory only, and Compact makes it durable.
--
--  Compaction rewrites the log as the HEADER (the same bytes), one APPLY per
--  index entry, every authorization record first and then every data
--  record, each part in index order, and one EXPIRE (horizon) if the store
--  has a horizon (and, on a log with no 7 bytes left after the frames, no
--  EXPIRE: the reopened horizon is then lower, which T18 allows).
--
--  Replay (T18): Open_From_Log checks the HEADER, refuses capacities below
--  the logged ones (No_Space), starts from Frontier.Empty with the logged
--  founding key and the capacities it is opened with, and performs the
--  entries in order (APPLY through Put_Frame, which must newly hold the
--  record, anything else is Malformed; APPLY_EXPIRED through
--  Frontier.Apply_Expired; EXPIRE through Frontier.Expire when it raises the
--  horizon, and the horizon is set either way). Replay trusts the logged
--  horizons: an EXPIRE no live store could write (a horizon above
--  maxceil - del_ttl_eff) is performed as written. A bound such as
--  horizon <= maxceil - Del_TTL_Min would not refuse a store's own log
--  (maxceil never falls: Frontier.Apply's Post keeps Ceil non-decreasing,
--  and del_ttl_eff >= Del_TTL_Min), but DESIGN.md §7 does not ask for it
--  and it is not made: the log is sealed at rest (a later layer).
--
--  Capacities (a decision taken here, for T18; DESIGN.md §7 does not say
--  it): the HEADER's capacities are always those of F (Valid states
--  Logged_Cap (S) = F.Cap and Logged_Slice (S) = F.Slice). A store reopened
--  with larger capacities can hold more than the old HEADER allows, and its
--  log would then not replay at the logged capacities; so Open_From_Log
--  writes the capacities it is opened with into the HEADER (the six bytes
--  data_cap ‖ slice) and keeps every other byte. The log equals the input
--  byte for byte iff the capacities are the logged ones. A file binding
--  must therefore persist those six bytes (an in-place write of bytes
--  74 .. 79, or a rewrite and rename) before it appends to a log reopened
--  with larger capacities; this is the one write that is not at the end.
--
--  Footprint (for a file binding): Open_From_Log replays against a copy
--  of its input (the image with the new capacities) and Compact copies
--  the whole log buffer before rewriting it, so each needs stack or
--  memory for one more log image (up to Log_Max bytes); the test main
--  runs in a task with a large stack for this reason.
--
--  Open_From_Log proves: the result is Valid, its HEADER well formed, its
--  log the input (but for the capacities as above), its horizon that of
--  the last EXPIRE entry (none if there is none); No_Space only for a log
--  that does not fit or logged capacities above the open ones; Malformed
--  only for a HEADER that is not one or a log with entries after it; and
--  a log that is only a well-formed HEADER whose capacities fit opens.
--  That replay accepts every log a store writes and reproduces its
--  frontier (T18, Lean `auth_first`) is a set statement proved in Lean
--  and tested here, not proved in SPARK: a replay that refused every
--  log with entries would still meet this contract.
--
--  What is proved (Valid is the store invariant; every operation keeps it):
--    * the index is F: held iff indexed, distinct entries, no held DEL is
--      expired at the store's horizon, a cell has at most one entry (T5);
--    * the log is a chain of entries from 0, the HEADER first and only
--      there, its bytes those of the store's collection, founding key,
--      salt and logged capacities; every index entry is an APPLY entry of
--      the chain with its length and its kind's tag;
--    * Put_Frame refines Frontier.Apply and Frontier.Apply_Expired, in the
--      order above, with each refusal stated as an iff and changing
--      nothing; the log only grows, bytes written never change, the entry
--      is at the returned offset;
--    * Expire computes the horizon of DESIGN.md §7, removes exactly the
--      expired DELs, logs EXPIRE only as stated, and leaves no held DEL at
--      or below the horizon (T11 (a));
--    * Compact keeps F, the horizon and the index's records, and lays the
--      log out as stated, frames byte for byte;
--    * Open_From_Log returns a Valid pair whose log is its input (but for
--      the capacities) and whose horizon is the last logged one.
--  Not in the invariant, and tested instead: that each entry's frame
--  decodes to the entry's header. The header contains h, a BLAKE2b hash of
--  the frame's content, and gnatprove 14 has no extensionality for arrays:
--  two element-wise equal byte arrays (the frame passed to Put_Frame, its
--  copy in the log, its copy after Compact) are not known to have equal
--  hashes, because Kome.Crypto.Blake2b_256 is a function of the whole array
--  value. Carrying it needs a congruence lemma for Blake2b_256 in
--  Kome.Crypto (now present: Lemma_Blake2b_Congruent) and one for
--  To_Header (Parse_*) in Kome.Records (not yet written). The test main checks it on every entry.
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

   --  Bound on the log buffer of the model (1 GiB). Chosen so that every
   --  offset + entry is a Natural; a file binding keeps it.
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

   --  The store's horizon: No_Horizon (-1, nothing expired) or a real
   --  horizon, at most 2**48 - 2 (see the header comment).
   subtype Horizon_Value is Time64 range No_Horizon .. Time64 (U48'Last) - 1;
   No_Horizon_Code : constant U48 := U48'Last;

   function Horizon_Code (H : Horizon_Value) return U48 is
     (if H = No_Horizon then No_Horizon_Code else U48 (H));

   function Horizon_Of_Code (C : U48) return Horizon_Value is
     (if C = No_Horizon_Code then No_Horizon else Time64 (C));

   ---------------------------------------------------------------------------
   --  Frames and their headers (the wire boundary, Kome.Records).
   ---------------------------------------------------------------------------

   --  Frame is the encoding of one record of the kind its tag names.
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

   --  The lattice header of a record frame (Kome.Records.To_Header of what
   --  it parses to). Lemma_Header_Of spells it out.
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

   --  A verified frame's header is canonical (D3; Kome.Records
   --  Lemma_Header_Canonical, the roster's del_ttl clamp from Well_Formed).
   procedure Lemma_Verified_Canonical (Frame : Byte_Array) with
     Ghost, Global => null,
     Pre  => Verified (Frame),
     Post => Canonical (Header_Of (Frame))
             and then Header_Of (Frame).K = Kome.Records.Kind_Of (Frame);

   ---------------------------------------------------------------------------
   --  The store.
   ---------------------------------------------------------------------------

   --  One index entry: the record (its header, which carries v and the
   --  cell), the offset of its APPLY entry and the frame's length.
   type Index_Entry is record
      H   : Header;
      Off : Log_Size   := 0;
      Len : Frame_Size := 1;
   end record;

   --  The offset just past an entry's APPLY.
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

   --  The entries of the log, in order: Log_Entries (S) of them, the K-th
   --  at offset Entry_Start (S, K) (Lemma_Scan).
   function Log_Entries (S : Store) return Natural with
     Global => null,
     Post => Log_Entries'Result <= S.Log_Cap;
   function Entry_Start (S : Store; K : Positive) return Log_Size with
     Global => null,
     Pre => K <= Log_Entries (S);

   --  Some index entry is the record X. Opaque (quantified).
   function Indexed (S : Store; X : Header) return Boolean with Global => null;

   --  The index position of an indexed record (ghost; unique on a valid
   --  store, Lemma_Position).
   function Position (S : Store; X : Header) return Held_Index with
     Ghost, Global => null,
     Pre  => Indexed (S, X),
     Post => Position'Result <= Entries (S) and then Entry_At (S, Position'Result).H = X;

   --  The store invariant, relating the store to its lattice state F (see
   --  the package comment). Opaque; read it through the lemmas below.
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
   --  Reading the log as a file.
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

   --  The size of the entry at P, and where the next one starts.
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
   --  The parts of the operations' contracts, named.
   ---------------------------------------------------------------------------

   --  Step 0 (DESIGN.md §7): an authorization record whose root_pk is not
   --  the store's founding key.
   function Foreign_Root (S : Store; Frame : Byte_Array) return Boolean is
     (Kome.Records.Is_Auth_Frame (Frame)
      and then Kome.Records.Root_Key_Of (Frame) /= Founding (S));

   --  Frontier.Apply's room rules, copied from its Post: the data row is
   --  full and R frees nothing (No_Space) ...
   function Data_Full (F : Frontier.State; R : Header) return Boolean is
     (Is_Data (R) and then Data_Count (F) = F.Cap and then not Drops_Any (F, R));

   --  ... and the authorization rules (Auth_Full): the signer's slice is
   --  full and R frees nothing, or the signer is new and every slot is
   --  taken, or W is full (unreachable, see Kome.Frontier.Apply).
   function Auth_Rule (F : Frontier.State; R : Header) return Boolean is
     (Is_Auth (R)
      and then ((Slot_Of (F, R.Issuer) /= 0
                 and then Slot_Count (F, Slot_Of (F, R.Issuer)) = F.Slice
                 and then not Drops_Any (F, R))
                or else (Slot_Of (F, R.Issuer) = 0 and then Slots_Used (F) = Signers_Max)
                or else (R.K = K_Grant
                         and then not In_W (Regs (F), R.V.Author)
                         and then Kome.Registers.Count (Regs (F)) = Writers_Max)));

   --  Fewer than Need bytes of log are left.
   function Log_Short (S : Store; Need : Natural) return Boolean is
     (S.Log_Cap - Log_Length (S) < Need);

   --  No_Space is answered only at a bound (T13), after admission, the
   --  duplicate and the domination test: an expired DEL that drops
   --  something and has no log room for its APPLY_EXPIRED, or a record that
   --  Frontier.Apply refuses for the data row, or one that Frontier would
   --  hold but whose APPLY does not fit the log.
   function At_Bound (S : Store; F : Frontier.State; H : Header; Len : Natural) return Boolean is
     (not Holds (F, H) and then not Dom (F, H)
      and then (if Expired (H, Horizon (S))
                then Drops_Any (F, H) and then Log_Short (S, Apply_Prefix + Len)
                else Data_Full (F, H)
                     or else (not Auth_Rule (F, H) and then Log_Short (S, Apply_Prefix + Len))))
     with Pre => Len <= Kome.Records.Frame_Max;

   --  Frontier.Apply's refinement statement (Frontier.lean `applyA` /
   --  `keep`; T4'): the registers grow exactly by H, nothing is held that
   --  was not held or is not H, nothing held is lost except by domination.
   function Applied (Old_F, New_F : Frontier.State; H : Header) return Boolean is
     (Ceil (Regs (New_F)) = U48'Max (Ceil (Regs (Old_F)), Ceil_Of (H))
      and then Extends (Regs (Old_F), Regs (New_F))
      and then (for all I in 1 .. Count (New_F) =>
                  Holds (Old_F, Held (New_F, I)) or else Held (New_F, I) = H)
      and then (for all I in 1 .. Count (Old_F) =>
                  Holds (New_F, Held (Old_F, I)) or else Dominates (H, Held (Old_F, I))));

   --  Frontier.Apply_Expired's effect (apply-then-expire): exactly the
   --  records H dominates leave F, H is not held, the registers are kept.
   function Expired_Applied (Old_F, New_F : Frontier.State; H : Header) return Boolean is
     (Ceil (Regs (New_F)) = Ceil (Regs (Old_F))
      and then Extends (Regs (Old_F), Regs (New_F))
      and then Extends (Regs (New_F), Regs (Old_F))
      and then not Holds (New_F, H)
      and then (for all I in 1 .. Count (New_F) =>
                  Holds (Old_F, Held (New_F, I)) and then not Dominates (H, Held (New_F, I)))
      and then (for all I in 1 .. Count (Old_F) =>
                  Holds (New_F, Held (Old_F, I)) or else Dominates (H, Held (Old_F, I))));

   --  Tombstone expiry's effect (T11 (a)): exactly the DELs with
   --  t <= Hz leave F, the registers are kept.
   function Expired_Out (Old_F, New_F : Frontier.State; Hz : Time64) return Boolean is
     (Ceil (Regs (New_F)) = Ceil (Regs (Old_F))
      and then Extends (Regs (Old_F), Regs (New_F))
      and then Extends (Regs (New_F), Regs (Old_F))
      and then (for all I in 1 .. Count (New_F) =>
                  Holds (Old_F, Held (New_F, I)) and then not Expired (Held (New_F, I), Hz))
      and then (for all I in 1 .. Count (Old_F) =>
                  Holds (New_F, Held (Old_F, I)) or else Expired (Held (Old_F, I), Hz)));

   --  Some held DEL is expired at Hz.
   function Expires_Any (F : Frontier.State; Hz : Time64) return Boolean is
     (for some I in 1 .. Count (F) => Expired (Held (F, I), Hz));

   --  The expiry horizon of DESIGN.md §7 (D10), in 64 bits:
   --  min (now_local, maxceil (F)) - del_ttl_eff (F), or none below 0.
   function Horizon_At (F : Frontier.State; Now : U48) return Horizon_Value is
     (if Time64'Min (Time64 (Now), Time64 (Ceil (Regs (F))))
           - Time64 (Kome.Views.Del_TTL_Eff (F)) < 0
      then No_Horizon
      else Time64'Min (Time64 (Now), Time64 (Ceil (Regs (F))))
           - Time64 (Kome.Views.Del_TTL_Eff (F)))
     with Pre => Is_Frontier (F);

   --  Expire (Now) logs EXPIRE: it raises the horizon and removes
   --  something, or it lowers the horizon.
   function Logs_Expire (S : Store; F : Frontier.State; Now : U48) return Boolean is
     ((Horizon_At (F, Now) > Horizon (S) and then Expires_Any (F, Horizon_At (F, Now)))
      or else Horizon_At (F, Now) < Horizon (S))
     with Pre => Is_Frontier (F);

   --  The log of New_S extends that of Old_S: no byte written changes and
   --  every entry stays where it was.
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

   --  Frame's bytes are the frame of the entry at Off.
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
   --  Defined by its Post (one atom per range in goals that carry it).
   function Same_Bytes (A : Store; PA : Natural; B : Store; PB : Natural; Len : Natural)
     return Boolean
   with
     Global => null,
     Pre  => PA <= Log_Length (A) and then Len <= Log_Length (A) - PA
             and then PB <= Log_Length (B) and then Len <= Log_Length (B) - PB,
     Post => Same_Bytes'Result =
       (for all K in 0 .. Len - 1 => Log_Byte (A, PA + K) = Log_Byte (B, PB + K));

   --  Within each part (authorization records, data records), S's entries
   --  are in the order of their positions in Old_S's index. Defined by its
   --  Post (one atom in Compact's contract).
   function In_Old_Order (Old_S, S : Store) return Boolean
   with
     Ghost, Global => null,
     Post => In_Old_Order'Result =
       (for all I in 1 .. Entries (S) =>
          (for all J in I + 1 .. Entries (S) =>
             (if Is_Data (Entry_At (S, I).H) = Is_Data (Entry_At (S, J).H)
              then Indexed (Old_S, Entry_At (S, I).H)
                   and then Indexed (Old_S, Entry_At (S, J).H)
                   and then Position (Old_S, Entry_At (S, I).H)
                            < Position (Old_S, Entry_At (S, J).H))));

   --  Where the frames of a compacted log end.
   function Body_End (S : Store) return Natural is
     (if Entries (S) = 0 then Header_Len else End_Of (Entry_At (S, Entries (S))));

   ---------------------------------------------------------------------------
   --  Operations.
   ---------------------------------------------------------------------------

   --  A new store for the collection of (Root_PK, Salt), beside the empty
   --  lattice state F (Frontier.Empty (ns, To_Key256 (Root_PK), Cap,
   --  Slice)). It writes the HEADER with F's capacities. The precondition
   --  ties F to the founding key, so the decoder, the capacity rows and
   --  root_void agree on it (DESIGN.md §7 step 0, round-three minor).
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
       and then Horizon (S) = No_Horizon;

   --  Apply one record and store its frame (DESIGN.md §7, steps 0-6 above).
   --  The caller has decoded and verified Frame (Verified, which is what
   --  Kome.Records.Decode_Verified accepts) and passes its header H.
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
     --  Top-level conjuncts are joined with "and" (each guards its own
     --  preconditions); the long ones are named above.
     Post => Valid (S, F)
       and Same_Identity (S'Old, S)
       and Horizon (S) = Horizon (S'Old)
       and Result in OK | Dominated | Inadmissible | Malformed | No_Space | Auth_Full
       --  The order of DESIGN.md §7, each outcome as an iff.
       and (Result = Malformed) = Foreign_Root (S'Old, Frame)
       and (Result = Inadmissible)
             = (not Foreign_Root (S'Old, Frame) and then not Admitted (F'Old, H))
       and (Result = Dominated)
             = (not Foreign_Root (S'Old, Frame) and then Admitted (F'Old, H)
                and then not Holds (F'Old, H) and then Dom (F'Old, H))
       and (Result = Auth_Full)
             = (not Foreign_Root (S'Old, Frame) and then not Holds (F'Old, H)
                and then not Dom (F'Old, H) and then Auth_Rule (F'Old, H))
       and (Result = No_Space)
             = (not Foreign_Root (S'Old, Frame) and then Admitted (F'Old, H)
                and then At_Bound (S'Old, F'Old, H, Frame'Length))
       --  Nothing changes on a refusal, on a duplicate, or for an expired
       --  DEL that drops nothing (T13).
       and (if Result /= OK or else Holds (F'Old, H)
               or else (Expired (H, Horizon (S'Old)) and then not Drops_Any (F'Old, H))
            then Unchanged (F'Old, F) and then S = S'Old)
       --  Append-only.
       and Log_Extends (S'Old, S)
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
   --  horizon is Horizon_At (F, Now). A higher one removes the expired
   --  DELs from F and the index and is logged iff it removed something; a
   --  lower one is set and logged; an equal one changes nothing. No_Space
   --  when the EXPIRE entry it must log does not fit, with no change.
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
       and Result in OK | No_Space
       and (Result = No_Space)
             = (Logs_Expire (S'Old, F'Old, Now) and then Log_Short (S'Old, Expire_Len))
       and (if Result = No_Space then Unchanged (F'Old, F) and then S = S'Old)
       and Log_Extends (S'Old, S)
       and (if Result = OK then
              Horizon (S) = Horizon_At (F'Old, Now)
              --  The held set is the old one minus exactly the DELs at or
              --  below the new horizon (none unless it rose).
              and then Expired_Out (F'Old, F, Horizon (S))
              and then (if Logs_Expire (S'Old, F'Old, Now)
                        then Appended_Expire (S'Old, S, Log_Length (S'Old), Horizon (S))
                        else Log_Length (S) = Log_Length (S'Old)
                             and then Log_Entries (S) = Log_Entries (S'Old)))
       --  T11 (a): no held DEL is at or below the horizon.
       and (for all I in 1 .. Count (F) => not Expired (Held (F, I), Horizon (S)));

   --  Rewrite the log as the HEADER, one APPLY per index entry (every
   --  authorization record first, then every data record, each part in
   --  index order) and one EXPIRE (Horizon (S)) if the store has a horizon
   --  and the log has room for it. The frontier is unchanged.
   procedure Compact (S : in out Store; F : Frontier.State) with
     Global => null,
     Pre  => Valid (S, F),
     Post => Valid (S, F)
       and Same_Identity (S'Old, S)
       and Horizon (S) = Horizon (S'Old)
       and Entries (S) = Entries (S'Old)
       and Body_End (S) <= Log_Length (S'Old)
       --  The same records, frame for frame, byte for byte.
       and (for all J in 1 .. Entries (S'Old) => Indexed (S, Entry_At (S'Old, J).H))
       and (for all I in 1 .. Entries (S) =>
              Indexed (S'Old, Entry_At (S, I).H)
              and then Entry_At (S'Old, Position (S'Old, Entry_At (S, I).H)).Len
                       = Entry_At (S, I).Len
              and then End_Of (Entry_At (S, I)) <= Log_Length (S)
              and then End_Of (Entry_At (S'Old, Position (S'Old, Entry_At (S, I).H)))
                       <= Log_Length (S'Old)
              and then Same_Bytes (S, Entry_At (S, I).Off,
                                   S'Old, Entry_At (S'Old, Position (S'Old, Entry_At (S, I).H)).Off,
                                   Apply_Prefix + Entry_At (S, I).Len))
       --  Authorization records first; each part in index order.
       and (for all I in 1 .. Entries (S) =>
              (for all J in I + 1 .. Entries (S) =>
                 (if Is_Data (Entry_At (S, I).H) then Is_Data (Entry_At (S, J).H))))
       and In_Old_Order (S'Old, S)
       --  The layout: the HEADER bytes, the APPLYs contiguous, then EXPIRE.
       and Log_Length (S) >= Header_Len
       and Log_Length (S'Old) >= Header_Len
       and (for all K in 0 .. Header_Len - 1 => Log_Byte (S, K) = Log_Byte (S'Old, K))
       and (if Entries (S) > 0 then Entry_At (S, 1).Off = Header_Len)
       and (for all I in 1 .. Entries (S) - 1 =>
              Entry_At (S, I + 1).Off = End_Of (Entry_At (S, I)))
       and (for all I in 1 .. Entries (S) =>
              I + 1 <= Log_Entries (S) and then Entry_Start (S, I + 1) = Entry_At (S, I).Off)
       and (if Horizon (S) >= 0 and then S.Log_Cap - Body_End (S) >= Expire_Len
            then Log_Length (S) >= Body_End (S)
                 and then Log_Length (S) - Body_End (S) = Expire_Len
                 and then Log_Entries (S) = Entries (S) + 2
                 and then Op_At (S, Body_End (S)) = Op_Expire
                 and then Code_At (S, Body_End (S) + 1) = Horizon_Code (Horizon (S))
            else Log_Length (S) = Body_End (S)
                 and then Log_Entries (S) = Entries (S) + 1);

   --  The capacities a log's HEADER records.
   function Header_Cap (Input : Byte_Array) return Word is
     (Kome.Keys.Word_Of (Input (HO_Cap), Input (HO_Cap + 1),
                         Input (HO_Cap + 2), Input (HO_Cap + 3)))
     with Pre => Input'First = 0 and then Input'Last >= Header_Len - 1;

   function Header_Slice (Input : Byte_Array) return Kome.Records.U16_Value is
     (Kome.Records.U16_Of (Input (HO_Slice), Input (HO_Slice + 1)))
     with Pre => Input'First = 0 and then Input'Last >= Header_Len - 1;

   --  Input begins with a HEADER: its op, magic and version, and an ns that
   --  is BLAKE2b-256 (root_pk ‖ salt)[0:16] of its root_pk and salt. These
   --  are the checks Open_From_Log makes on the HEADER.
   function Header_Well_Formed (Input : Byte_Array) return Boolean is
     (Input'Last >= Header_Len - 1
      and then Input (0) = Op_Header
      and then Input (HO_Magic .. HO_Magic + Magic_Len - 1) = Magic
      and then Input (HO_Version) = Log_Version
      and then Input (HO_NS .. HO_NS + NS_Len - 1) =
                 Kome.Records.Collection_Id (Input (HO_Root .. HO_Root + Pubkey_Len - 1),
                                             Input (HO_Salt .. HO_Salt + Salt_Len - 1)))
     with Pre => Input'First = 0;

   --  The K-th entry of the log is an EXPIRE entry.
   function Is_Expire (S : Store; K : Positive) return Boolean is
     (K <= Log_Entries (S)
      and then Entry_Start (S, K) < Log_Length (S)
      and then Log_Length (S) - Entry_Start (S, K) >= Expire_Len
      and then Op_At (S, Entry_Start (S, K)) = Op_Expire);

   --  The horizon the K-th entry, an EXPIRE, logs.
   function Expire_Horizon (S : Store; K : Positive) return Horizon_Value is
     (Horizon_Of_Code (Code_At (S, Entry_Start (S, K) + 1)))
     with Pre => Is_Expire (S, K);

   --  Horizon (S) is the horizon of the log's last EXPIRE entry, or none
   --  if the log has no EXPIRE entry. (True of a replayed store; a live
   --  store may hold a higher horizon only in memory, DESIGN.md §7.)
   function Horizon_Logged (S : Store) return Boolean is
     (if (for some K in 1 .. Log_Entries (S) => Is_Expire (S, K))
      then (for some K in 1 .. Log_Entries (S) =>
              Is_Expire (S, K)
              and then Horizon (S) = Expire_Horizon (S, K)
              and then (for all K2 in K + 1 .. Log_Entries (S) => not Is_Expire (S, K2)))
      else Horizon (S) = No_Horizon);

   --  Reopen a store from its log (replay, T18). F's and S's discriminants
   --  are the capacities to open with; they must be at least the logged
   --  ones (No_Space otherwise, and when the log does not fit S, which is
   --  Input'Last >= S.Log_Cap since Input'First = 0). Malformed:
   --  a HEADER that is not one (op, magic, version, ns = BLAKE2b-256
   --  (root_pk ‖ salt)[0:16]), an entry that does not parse, a frame that is
   --  not well-formed or not of the collection, an authorization record
   --  whose root_pk is not the founding key, an APPLY that Put_Frame would
   --  not newly hold and index (including one it refuses for room), an
   --  APPLY_EXPIRED that is not an admitted, undominated DEL. (An
   --  APPLY_EXPIRED of an admitted, undominated DEL that drops nothing is
   --  accepted and changes nothing but the log; no store writes one, since
   --  Put_Frame logs APPLY_EXPIRED only when it drops something.) On OK the pair
   --  is Valid, the log is the input with the HEADER's capacities set to
   --  F's (so the input itself when they were F's already), and the horizon
   --  is the last logged one.
   procedure Open_From_Log
     (Input  : in     Byte_Array;
      F      :    out Frontier.State;
      S      :    out Store;
      Result :    out Status)
   with
     Global => null,
     Pre  => Input'First = 0
       and then F.Slice >= 1
       and then F.Cap + Signers_Max * F.Slice <= Held_Max
       and then S.Cap >= F.Cap + Signers_Max * F.Slice,
     Post => Result in OK | Malformed | No_Space
       and (if Input'Last >= S.Log_Cap then Result = No_Space)
       --  Completeness, in part: a log that is only a well-formed HEADER
       --  whose capacities fit opens; Malformed only for a HEADER that is
       --  not one or for a log that has entries after it.
       and (if Input'Last = Header_Len - 1
              and then Input'Last < S.Log_Cap
              and then Header_Well_Formed (Input)
              and then Header_Cap (Input) <= Word (F.Cap)
              and then Header_Slice (Input) <= F.Slice
            then Result = OK)
       and (if Result = Malformed then
              not Header_Well_Formed (Input) or else Input'Last >= Header_Len)
       and (if Result = No_Space then
              Input'Last >= S.Log_Cap
              or else (Input'Last >= Header_Len - 1
                       and then (Header_Cap (Input) > Word (F.Cap)
                                 or else Header_Slice (Input) > F.Slice)))
       and (if Result = OK then
              Valid (S, F)
              and then Input'Last < S.Log_Cap
              and then Input'Last >= Header_Len - 1
              and then Header_Well_Formed (Input)
              and then Header_Cap (Input) <= Word (F.Cap)
              and then Header_Slice (Input) <= F.Slice
              and then Log_Length (S) = Input'Last + 1
              and then (for all J in 0 .. Input'Last =>
                          (if J < HO_Cap or else J >= Header_Len
                           then Log_Byte (S, J) = Input (J)))
              and then Logged_Cap (S) = F.Cap
              and then Logged_Slice (S) = F.Slice
              and then (if Header_Cap (Input) = Word (F.Cap)
                          and then Header_Slice (Input) = F.Slice
                        then (for all J in 0 .. Input'Last => Log_Byte (S, J) = Input (J)))
              and then Horizon_Logged (S));

   --  The cell index (DESIGN.md §7 "cell -> (offset, v)"): the entry of
   --  the PUT on (NS, Ent, FH), if any.
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
       and then Logged_Cap (S) = F.Cap
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

   --  Every index entry is a held record whose APPLY entry is one of the
   --  log's entries, with its length and its kind's tag.
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

   --  Indexed, spelled out.
   procedure Lemma_Indexed (S : Store; X : Header) with
     Ghost, Global => null,
     Post => Indexed (S, X) = (for some I in 1 .. Entries (S) => Entry_At (S, I).H = X);

   --  Entries are distinct, so an indexed record has one position.
   procedure Lemma_Position (S : Store; F : Frontier.State; I : Held_Index) with
     Ghost, Global => null,
     Pre  => Valid (S, F) and then I <= Entries (S),
     Post => Indexed (S, Entry_At (S, I).H)
             and then Position (S, Entry_At (S, I).H) = I;

   --  The log is a chain of entries from offset 0 to its length, the
   --  HEADER first and only there: what a reader scanning it as a file
   --  relies on.
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

   --  T5 through the index (Frontier.lean `cell_unique`): one cell, at most
   --  one entry, so "cell -> (offset, v)" is a function.
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

   --  Entry boundaries of the log, in order: the model's stand-in for the
   --  file's own framing (a file binding finds them by scanning). Sized by
   --  the discriminant alone (Ada allows nothing else in a component
   --  constraint); at most Log_Cap / Min_Entry are used.
   type Offset_Array is array (Positive range <>) of Log_Size;

   --  No Dynamic_Predicate: the bounds of the counters are part of Valid
   --  and the accessors clamp, so that clients may assign a Store.
   type Store (Cap : Held_Count; Log_Cap : Log_Size) is record
      NS   : Id128;
      NSb  : NS_Id         := [others => 0];   --  ns as bytes, for the HEADER
      Fnd  : Key256;
      Root : Pubkey        := [others => 0];
      Slt  : Salt          := [others => 0];
      DCap : Data_Size     := 0;
      Slc  : Slice_Count   := 0;
      Hz   : Horizon_Value := No_Horizon;
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
   --  The invariant, in parts over explicit components so that each step of
   --  an operation can re-establish one part at a time. The quantified
   --  parts are defined by their Posts rather than as expression functions,
   --  so that a goal that only carries one along sees one atom.
   ---------------------------------------------------------------------------

   --  Some entry of Idx (1 .. N) is the record X. Defined by its Post, so
   --  that it stays one atom in goals that only carry it along.
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

   --  The len:u32 of an APPLY or APPLY_EXPIRED entry at P, that is the
   --  word at P + 1 .. P + 4 (0 where there is none). Total, so that its
   --  definition is never guarded inside a quantifier.
   function Len_Word (Log : Byte_Array; P : Natural) return Word is
     (if P >= Log'First and then P < Log'Last and then Log'Last - P >= 4
      then Kome.Keys.Word_Of (Log (P + 1), Log (P + 2), Log (P + 3), Log (P + 4))
      else 0);

   --  Entry E's APPLY is in Log (0 .. LL - 1), after the HEADER. Defined
   --  by its Post, so that a goal about one entry keeps the atom that the
   --  quantifier of Framed is instantiated on.
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

   --  Entries are in log order, their APPLYs disjoint, their records
   --  distinct.
   function Sorted (Idx : Entry_Array; N : Held_Count) return Boolean
   with
     Global => null,
     Pre  => Idx'First = 1 and then N <= Idx'Last,
     Post => Sorted'Result =
               (for all I in 1 .. N =>
                  (for all J in I + 1 .. N =>
                     End_Of (Idx (I)) <= Idx (J).Off and then Idx (I).H /= Idx (J).H));

   --  A whole entry starts at P in Log (0 .. LL - 1). Defined by its Post,
   --  like Frame_OK.
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

   --  The size of the entry at P (0 where there is none). Total.
   function Size_At (Log : Byte_Array; P : Natural) return Natural is
     (if P < Log'First or else P > Log'Last then 0
      elsif Log (P) = Op_Header then Header_Len
      elsif Log (P) = Op_Expire then Expire_Len
      elsif Len_Word (Log, P) <= Kome.Records.Frame_Max
      then Apply_Prefix + Natural (Len_Word (Log, P))
      else 0);

   --  Bnd (1 .. NB) is a chain of entries from 0 to LL: the HEADER at 0
   --  and nowhere else, each entry ending where the next begins.
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

   --  Every entry's APPLY is one of the chain's.
   function At_Bounds (Idx : Entry_Array; N : Held_Count; Bnd : Offset_Array; NB : Natural)
     return Boolean
   with
     Global => null,
     Pre  => Idx'First = 1 and then N <= Idx'Last
             and then Bnd'First = 1 and then NB <= Bnd'Last,
     Post => At_Bounds'Result =
               (for all I in 1 .. N => (for some K in 1 .. NB => Bnd (K) = Idx (I).Off));

   --  The HEADER of the collection NSb of (Root, Slt) with the logged
   --  capacities DCap and Slc is Log (0 .. Header_Len - 1). (ns is kept as
   --  bytes beside Root and Slt: BLAKE2b is opaque, so Collection_Id of a
   --  copy of Root is not known to be Collection_Id of Root, while a byte
   --  array equal element by element is.)
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
      and then S.DCap = F.Cap
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
