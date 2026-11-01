--  Kome.Store: the storage model of DESIGN.md §7. One collection's replica
--  is a lattice state F (Kome.Frontier.State: the held headers and the
--  grow-only registers) plus a Store: an append-only log of frames and an
--  in-memory index from each stored record to its frame (DESIGN.md §7:
--  "in-memory index cell -> (offset, v)"). Every operation takes the pair
--  (S, F) and Valid (S, F) relates them.
--
--  Why F is a parameter and not a component of Store: a record component
--  of type Frontier.State (Cap), and any assignment statement whose target
--  is a Frontier.State, make gnatprove 14 (gnatprove-fsf-14) crash in
--  "generation of Global contracts" (GNAT BUG DETECTED,
--  einfo-entities.ads:1973). The trigger is the Dynamic_Predicate on the
--  full view of Frontier.State used from another unit; an object
--  declaration with an initial value does not trigger it, an assignment
--  does (five-line repros kept with the report). Holding F beside the Store
--  is the workaround; Expire and Compact take F in mode `in`, so flow
--  analysis alone proves they leave the frontier unchanged, and Put_Frame
--  decides every refusal before it calls Frontier.Apply because it cannot
--  copy F back.
--
--  The log is modelled as a bounded byte buffer with a capacity
--  discriminant, written only at its end, so that an OS file can replace it
--  later: Put_Frame returns the offset it appended at, Read_Frame (offset)
--  returns the frame there, and Compact rewrites the whole log the way a
--  file would be rewritten and renamed. Byte Log_Cap of the buffer is never
--  written: the buffer is 0 .. Log_Cap so that every LL <= Log'Last and the
--  length-prefix reads stay in range without a case split.
--
--  Log format. The log is a sequence of  len:u32 ‖ frame  where frame is
--  tag ‖ content ‖ sig exactly as Kome.Records encodes it and len is its
--  length, big-endian (Kome.Keys word lanes). DESIGN.md §7 says
--  "append-only log of content ‖ sig frames" and leaves the framing open;
--  this is the framing chosen here (sealing at rest is a later layer). The
--  invariant states that the log is exactly a chain of such frames from
--  offset 0 to its length (Frames, Frame_Start, Lemma_Scan), so a replica
--  can be reopened by scanning it, and every index entry is one of them.
--
--  The drop rule (DESIGN.md §7):
--
--    drop x  iff  dom (x, F)  ∨  (x is DEL ∧ now_local >= x.t + del_ttl)
--
--  The first clause is Kome.Frontier.Apply (T3) and the index follows it:
--  an entry leaves the index the moment its record is dominated. The second
--  clause is apply-then-expire: an arriving DEL is always applied (it
--  dominates and frees its entity's fields) and only then dropped if it is
--  already past del_ttl. The store keeps an expiry horizon, the largest
--  now - del_ttl any Expire was called with (computed in 64 bits: DESIGN.md
--  §7 notes that x.t + del_ttl wraps in 48 bits at x.t = 2**48 - 1). A DEL
--  with t <= horizon is expired: Expire drops it from the index; Put_Frame
--  applies such a DEL and logs its frame but does not index it (so that
--  replaying the log replays what it freed); Compact removes its frame
--  from the log.
--
--  NOT DONE: the second clause is applied to the index and the log, NOT to
--  the lattice state F. Kome.Frontier has no operation that removes a held
--  record, and the store cannot rebuild F (the assignment above crashes
--  gnatprove), so an expired DEL stays held in F, where it still dominates
--  and still occupies a slot. Consequences, all of them real:
--    * F is not bounded by DESIGN.md §7's |F| <= live cells + DELs younger
--      than del_ttl + 1 roster + revocations: every DEL ever applied stays.
--      A frontier that fills with expired DELs refuses every record that
--      frees nothing with No_Space, for good (test: "wedge").
--    * F, and any digest of it (T6), differs from a replica reopened from
--      the log, which holds exactly the indexed records: the live frontier
--      is the reopened one plus its expired DELs (test: "reopen").
--    * The live replica refuses a record older than a DEL it has expired;
--      the reopened one accepts it (DESIGN.md §7's resurrection residual).
--  It needs Frontier.Remove (S, X) or Frontier.Drop_Expired (S, Horizon),
--  with Post "held set = old minus X, registers unchanged, Is_Frontier";
--  Expire would then remove the expired DELs from F, Valid would state
--  that F holds no expired DEL, and Covered would become "held iff
--  indexed". DESIGN.md §10 should record this until then.
--
--  The horizon only advances, so a dropped tombstone stays dropped if the
--  clock steps back, and Put_Frame uses the stored horizon (the clock at
--  the last Expire, which is conservative). It is one number for all
--  del_ttl values: if ROSTER_max.del_ttl is later raised, DELs with t
--  between the new now - del_ttl and the old horizon still count as
--  expired, earlier than the new del_ttl allows (narrowing A4'; DESIGN.md
--  §10 should record it, or the horizon be kept per del_ttl).
--
--  What is proved (Valid is the store invariant; every operation keeps it):
--    * The index corresponds to the frontier: every index entry is a held,
--      unexpired record (Lemma_Entry_Held), every held unexpired record has
--      an index entry (Lemma_Held_Indexed), entries are distinct, and a
--      cell has at most one entry (Lemma_Cell_Unique, from T5).
--    * The log is a chain of frames from 0 to its length; every entry's
--      frame is one of them, with its length and its kind's tag; entries
--      are in log order.
--    * Put_Frame refines Frontier.Apply (its Post is Apply's, lifted),
--      appends iff the record is newly held and indexes it iff it is also
--      unexpired; the log only grows and bytes already written never
--      change; the frame is at the returned offset. Inadmissible and
--      No_Space leave the store and the frontier unchanged (S = S'Old and
--      F = F'Old, T13); Inadmissible is returned iff the record is not
--      admitted, and No_Space only at a stated bound.
--    * Expire drops exactly the entries that are expired DELs at (now,
--      del_ttl) and nothing else; every remaining DEL is younger than
--      del_ttl (T11, the apply-then-expire half, for the index).
--    * Compact leaves the frontier, the registers, the horizon and the
--      index's records unchanged and rewrites the log to be exactly the
--      indexed frames, contiguous, in index order, byte for byte.
--  Not proved: one assertion in Put_Frame, that Frontier.Apply does not
--  return No_Space after the store has pre-checked Frontier.Apply's own
--  No_Space rule (full, and the record frees nothing). Frontier.Apply's
--  contract does not state when it returns No_Space, nor that the state is
--  unchanged when it does, so the prover cannot see it; the assertion is
--  executed by the test main (-gnata). It goes once Frontier.Apply's Post
--  says "No_Space => S = S'Old" or "No_Space only if Count = Cap and R is
--  not held, not dominated, and dominates nothing held".
--  Not in the invariant: that each entry's frame decodes to the entry's
--  header. Put_Frame's Pre ties Frame to H and Members (Header_Of,
--  Members_Agree) and every Post carries the bytes exactly, but a function
--  of a byte slice cannot be carried through the invariant: gnatprove 14
--  has no extensionality for arrays (two element-wise equal arrays are not
--  known to give equal results under a function; tested). The test main
--  checks it on every entry.
pragma Ada_2022;
with Kome.Headers;   use Kome.Headers;
with Kome.Registers; use Kome.Registers;
with Kome.Frontier;  use Kome.Frontier;
with Kome.Keys;
with Kome.Records;
with Kome.Views;
package Kome.Store with SPARK_Mode is

   ---------------------------------------------------------------------------
   --  Bounds.
   ---------------------------------------------------------------------------

   --  Bound on the log buffer of the model (1 GiB). Chosen so that every
   --  offset + prefix + frame is a Natural; a file binding keeps it.
   Log_Max : constant := 2**30;
   subtype Log_Size is Natural range 0 .. Log_Max;

   --  len:u32 before every frame.
   Prefix_Len : constant := 4;

   --  The shortest stored frame: a prefix and a one-byte frame.
   Min_Frame : constant := Prefix_Len + 1;

   --  A frame is at most Kome.Records.Frame_Max bytes (a PUT with a 32-byte
   --  field and a 65 535-byte value, DESIGN.md §2).
   subtype Frame_Size is Positive range 1 .. Kome.Records.Frame_Max;

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
                  when K_Revoke => Kome.Records.Is_Revoke_Frame (Frame)));

   --  The lattice header of a record frame (Kome.Records.To_Header of what
   --  it parses to). Opaque to other units; Lemma_Header_Of spells it out.
   function Header_Of (Frame : Byte_Array) return Header with
     Global => null,
     Pre    => Is_Record_Frame (Frame);

   --  Members are exactly a roster frame's member signing keys, in order
   --  (Kome.Records.Member_Key), and nothing for the other kinds. Opaque;
   --  Lemma_Members_Agree spells it out.
   function Members_Agree (Frame : Byte_Array; Members : Member_Keys) return Boolean with
     Global => null,
     Pre    => Is_Record_Frame (Frame);

   procedure Lemma_Header_Of (Frame : Byte_Array) with
     Ghost, Global => null,
     Pre  => Is_Record_Frame (Frame),
     Post => Header_Of (Frame) =
               (case Kome.Records.Kind_Of (Frame) is
                  when K_Put    => Kome.Records.To_Header (Kome.Records.Parse_Put (Frame)),
                  when K_Del    => Kome.Records.To_Header (Kome.Records.Parse_Del (Frame)),
                  when K_Roster => Kome.Records.To_Header (Kome.Records.Parse_Roster (Frame)),
                  when K_Revoke => Kome.Records.To_Header (Kome.Records.Parse_Revoke (Frame)));

   procedure Lemma_Members_Agree (Frame : Byte_Array; Members : Member_Keys) with
     Ghost, Global => null,
     Pre  => Is_Record_Frame (Frame),
     Post => Members_Agree (Frame, Members) =
               (if Kome.Records.Kind_Of (Frame) = K_Roster
                then Members'Length = Kome.Records.Parse_Roster (Frame).C.N_Members
                     and then (for all I in 1 .. Members'Length =>
                                 Members (Members'First + (I - 1)) =
                                   Kome.Records.Member_Key
                                     (Kome.Records.Parse_Roster (Frame).C, I))
                else Members'Length = 0);

   ---------------------------------------------------------------------------
   --  Tombstone expiry, in 64 bits (DESIGN.md §7).
   ---------------------------------------------------------------------------

   type Time64 is range -(2**62) .. 2**62 with Size => 64;

   --  The drop rule's second clause, literally: x is a DEL and
   --  now_local >= x.t + del_ttl, the sum taken in 64 bits so that it never
   --  wraps (x.t = 2**48 - 1 stays immortal under any del_ttl > 0 until now
   --  reaches it).
   function Expired_At (X : Header; Now, Del_TTL : U48) return Boolean is
     (X.K = K_Del and then Time64 (X.V.T) + Time64 (Del_TTL) <= Time64 (Now));

   --  Expired under a horizon (the largest now - del_ttl seen):
   --  t <= now - del_ttl iff now >= t + del_ttl.
   function Expired (X : Header; Horizon : Time64) return Boolean is
     (X.K = K_Del and then Time64 (X.V.T) <= Horizon);

   --  Nothing is expired before the first Expire (every t >= 0).
   No_Horizon : constant Time64 := -1;

   ---------------------------------------------------------------------------
   --  The store.
   ---------------------------------------------------------------------------

   --  One index entry: the record (its header, which carries v and the
   --  cell), and where its frame is: offset of its length prefix and the
   --  frame's length.
   type Index_Entry is record
      H   : Header;
      Off : Log_Size   := 0;
      Len : Frame_Size := 1;
   end record;

   --  The offset just past an entry's frame.
   function End_Of (E : Index_Entry) return Natural is
     (E.Off + Prefix_Len + E.Len);

   --  Cap index entries, Log_Cap bytes of log.
   type Store (Cap : Held_Count; Log_Cap : Log_Size) is private;

   function Collection (S : Store) return Id128 with Global => null;
   function Horizon (S : Store) return Time64 with Global => null;
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

   --  The frames of the log, in order: Frames (S) of them, the K-th at
   --  offset Frame_Start (S, K) (Lemma_Scan).
   function Frames (S : Store) return Natural with
     Global => null,
     Post => Frames'Result <= S.Log_Cap;
   function Frame_Start (S : Store; K : Positive) return Log_Size with
     Global => null,
     Pre => K <= Frames (S);

   --  Some index entry is the record X. Opaque (quantified).
   function Indexed (S : Store; X : Header) return Boolean with Global => null;

   --  The store invariant, relating the store to its lattice state F (see
   --  the package comment). Opaque (quantified); read it through the
   --  lemmas below.
   function Valid (S : Store; F : Frontier.State) return Boolean with Global => null;

   --  R dominates a held record (applying it frees a slot), and R
   --  dominates an indexed record (indexing it frees an entry).
   function Frees (F : Frontier.State; R : Header) return Boolean is
     (for some K in 1 .. Count (F) => Dominates (R, Held (F, K)));
   function Index_Frees (S : Store; R : Header) return Boolean is
     (for some I in 1 .. Entries (S) => Dominates (R, Entry_At (S, I).H));

   ---------------------------------------------------------------------------
   --  Reading the log as a file.
   ---------------------------------------------------------------------------

   --  The length prefix at Off.
   function Len_At (S : Store; Off : Natural) return Word is
     (Kome.Keys.Word_Of (Log_Byte (S, Off), Log_Byte (S, Off + 1),
                         Log_Byte (S, Off + 2), Log_Byte (S, Off + 3)))
     with Pre => Off <= Log_Length (S) and then Log_Length (S) - Off >= Prefix_Len;

   --  A whole frame starts at Off.
   function Has_Frame (S : Store; Off : Natural) return Boolean is
     (Off <= Log_Length (S)
      and then Log_Length (S) - Off >= Prefix_Len
      and then Len_At (S, Off) in 1 .. Kome.Records.Frame_Max
      and then Natural (Len_At (S, Off)) <= Log_Length (S) - Off - Prefix_Len);

   --  Where the next frame starts.
   function Next_Offset (S : Store; Off : Natural) return Natural is
     (Off + Prefix_Len + Natural (Len_At (S, Off)))
     with Pre => Has_Frame (S, Off);

   --  The frame at Off (its bytes, indexed from 0).
   function Read_Frame (S : Store; Off : Natural) return Byte_Array with
     Global => null,
     Pre  => Has_Frame (S, Off),
     Post => Read_Frame'Result'First = 0
       and then Read_Frame'Result'Length = Natural (Len_At (S, Off))
       and then (for all K in Read_Frame'Result'Range =>
                   Read_Frame'Result (K) = Log_Byte (S, Off + Prefix_Len + K));

   ---------------------------------------------------------------------------
   --  The parts of Put_Frame's contract, named.
   ---------------------------------------------------------------------------

   --  Frontier.Apply's refinement statement (Frontier.lean `applyA` /
   --  `keep`; T4'): the registers only grow, nothing is held that was not
   --  held or is not H, and nothing held is lost except by domination.
   function Applied (Old_F, New_F : Frontier.State; H : Header) return Boolean is
     (Ceil (Regs (New_F)) >= Ceil (Regs (Old_F))
      and then Extends (Regs (Old_F), Regs (New_F))
      and then (for all I in 1 .. Count (New_F) =>
                  Holds (Old_F, Held (New_F, I)) or else Held (New_F, I) = H)
      and then (for all I in 1 .. Count (Old_F) =>
                  Holds (New_F, Held (Old_F, I)) or else Dom (New_F, Held (Old_F, I))));

   --  No_Space is answered only at a bound (T13): H is not yet held and
   --  needs a frontier slot it cannot free (Frontier.Apply's rule), or
   --  room for Len bytes of frame in the log, or an index entry that no
   --  entry it dominates can free.
   function At_Bound (S : Store; F : Frontier.State; H : Header; Len : Natural) return Boolean is
     (not Holds (F, H)
      and then ((not Dom (F, H) and then Count (F) = F.Cap and then not Frees (F, H))
                or else S.Log_Cap - Log_Length (S) < Prefix_Len + Len
                or else (not Expired (H, Horizon (S))
                         and then Entries (S) = S.Cap
                         and then not Index_Frees (S, H))))
     with Pre => Len <= Kome.Records.Frame_Max;

   --  The log of New_S extends that of Old_S: no byte written changes and
   --  every frame stays where it was.
   function Log_Extends (Old_S, New_S : Store) return Boolean is
     (Log_Length (New_S) >= Log_Length (Old_S)
      and then (for all J in 0 .. Log_Length (Old_S) - 1 =>
                  Log_Byte (New_S, J) = Log_Byte (Old_S, J))
      and then Frames (New_S) >= Frames (Old_S)
      and then (for all K in 1 .. Frames (Old_S) =>
                  Frame_Start (New_S, K) = Frame_Start (Old_S, K)));

   --  Frame was appended at Off, as the new last frame of the log, and,
   --  unless H is expired, indexed as the new last entry.
   function Appended
     (Old_S, New_S : Store; Frame : Byte_Array; H : Header; Off : Natural) return Boolean is
     (Off = Log_Length (Old_S)
      and then Log_Length (New_S) >= Off + Prefix_Len
      and then Frame'Length = Log_Length (New_S) - Off - Prefix_Len
      and then Frames (New_S) = Frames (Old_S) + 1
      and then Frame_Start (New_S, Frames (New_S)) = Off
      and then Has_Frame (New_S, Off)
      and then Natural (Len_At (New_S, Off)) = Frame'Length
      and then (for all K in 0 .. Frame'Length - 1 =>
                  Log_Byte (New_S, Off + Prefix_Len + K) = Frame (Frame'First + K))
      and then (if not Expired (H, Horizon (New_S))
                then Entries (New_S) >= 1
                     and then Entry_At (New_S, Entries (New_S)) =
                                (H => H, Off => Off, Len => Frame'Length)))
     with Pre => Frame'Length in Frame_Size;

   ---------------------------------------------------------------------------
   --  Operations.
   ---------------------------------------------------------------------------

   --  An empty store for collection NS, beside the empty lattice state F
   --  (Frontier.Empty (NS, Cap)). The capacities are S's discriminants.
   --  (Frontier exposes no collection accessor, so that F was made for NS
   --  is the caller's to keep; Put_Frame checks every record's ns.)
   procedure Open (NS : Id128; F : Frontier.State; S : out Store) with
     Global => null,
     Pre  => Count (F) = 0,
     Post => Valid (S, F)
       and then Collection (S) = NS
       and then Entries (S) = 0
       and then Log_Length (S) = 0
       and then Frames (S) = 0
       and then Horizon (S) = No_Horizon;

   --  Apply one record and store its frame. Frame is the record's encoding
   --  (Kome.Records), already verified well-formed by the caller; H must be
   --  its header and Members its roster's member keys (empty for the other
   --  kinds), exactly (Header_Of, Members_Agree), as for Frontier.Apply.
   --
   --  Frontier.Apply first (DESIGN.md §3, §4). Then:
   --    OK, newly held, not expired  -> the frame is appended at Off and
   --                                    indexed; entries H dominates leave
   --                                    the index (dom (x, F), T3)
   --    OK, newly held, expired DEL  -> applied, freeing its entity's
   --                                    fields, appended but not indexed:
   --                                    apply-then-expire (DESIGN.md §7)
   --    OK, already held             -> a duplicate is a no-op
   --    Dominated                    -> applied (a roster still raises the
   --                                    registers), nothing appended
   --    Inadmissible, No_Space       -> nothing changed at all
   --  No_Space: the frontier, the log or the index is full, as stated in
   --  the Post. Room is checked before the record is applied, so a record
   --  that would turn out to be dominated is refused too when the log or
   --  the index is full (and a roster then does not raise the registers).
   procedure Put_Frame
     (S       : in out Store;
      F       : in out Frontier.State;
      Frame   : in     Byte_Array;
      H       : in     Header;
      Members : in     Member_Keys;
      Off     :    out Log_Size;
      Result  :    out Status)
   with
     Global => null,
     Pre  => Valid (S, F)
       and then Frame'Length in Frame_Size
       and then Is_Record_Frame (Frame)
       and then Header_Of (Frame) = H
       and then Members_Agree (Frame, Members)
       and then Kome.Records.Kind_Of (Frame) = H.K
       and then H.NS = Collection (S)
       and then Kome.Views.Canonical (H)
       and then (if H.K /= K_Roster then Members'Length = 0)
       and then Members'Length <= Members_Max,
     --  Top-level conjuncts are joined with "and" (each guards its own
     --  preconditions); the long ones are named above.
     Post => Valid (S, F)
       and Collection (S) = Collection (S'Old)
       and Horizon (S) = Horizon (S'Old)
       --  Failures change nothing (T13).
       and (if Result in Inadmissible | No_Space then S = S'Old and then F = F'Old)
       --  Refused for admission exactly when not admitted (DESIGN.md §4).
       and (Result = Inadmissible) = not Admitted (F'Old, H)
       --  Otherwise Frontier.Apply's refinement statement, lifted.
       and (if Result in OK | Dominated then Applied (F'Old, F, H))
       and (case Result is
              when OK           => Holds (F, H)
                                   and then (if not Expired (H, Horizon (S))
                                             then Indexed (S, H)),
              when Dominated    => Dom (F, H) and then not Holds (F, H),
              when Inadmissible => True,
              when No_Space     => At_Bound (S'Old, F'Old, H, Frame'Length),
              when others       => False)
       --  Append-only: the log only grows, written bytes never change, the
       --  frames already in it stay where they are.
       and Log_Extends (S'Old, S)
       --  Appended iff newly held, then the frame is at Off, as the last
       --  frame of the log; indexed iff also unexpired. An expired DEL's
       --  frame stays in the log, outside the index, until Compact, so that
       --  replaying the log replays what it freed.
       and (if Result = OK and then not Holds (F'Old, H)
            then Appended (S'Old, S, Frame, H, Off)
            else Log_Length (S) = Log_Length (S'Old) and then Frames (S) = Frames (S'Old));

   --  Tombstone expiry at local time Now under del_ttl (the maximal roster's,
   --  supplied by the caller). Drops from the index exactly the DELs with
   --  now >= t + del_ttl; the frames go at the next Compact. The lattice
   --  state F is NOT changed (see the package comment: the expired DELs
   --  stay held in F until Kome.Frontier can remove a record).
   procedure Expire (S : in out Store; F : Frontier.State; Now, Del_TTL : U48) with
     Global => null,
     Pre  => Valid (S, F),
     Post => Valid (S, F)
       and Collection (S) = Collection (S'Old)
       and Horizon (S) = Time64'Max (Horizon (S'Old), Time64 (Now) - Time64 (Del_TTL))
       and Log_Length (S) = Log_Length (S'Old)
       and (for all J in 0 .. Log_Length (S'Old) - 1 =>
              J < Log_Length (S) and then Log_Byte (S, J) = Log_Byte (S'Old, J))
       and Frames (S) = Frames (S'Old)
       and (for all K in 1 .. Frames (S'Old) =>
              K <= Frames (S) and then Frame_Start (S, K) = Frame_Start (S'Old, K))
       and Entries (S) <= Entries (S'Old)
       --  T11 (apply-then-expire): every remaining DEL is younger than
       --  del_ttl; every other entry is untouched.
       and (for all I in 1 .. Entries (S) =>
              not Expired_At (Entry_At (S, I).H, Now, Del_TTL))
       and (for all I in 1 .. Entries (S) =>
              (for some J in 1 .. Entries (S'Old) =>
                 Entry_At (S, I) = Entry_At (S'Old, J)))
       and (for all J in 1 .. Entries (S'Old) =>
              Expired_At (Entry_At (S'Old, J).H, Now, Del_TTL)
              or else (for some I in 1 .. Entries (S) =>
                         Entry_At (S, I) = Entry_At (S'Old, J)));

   --  Rewrite the log to hold exactly the indexed frames (DESIGN.md §7
   --  "compaction rewrites exactly F", here: exactly the index), contiguous
   --  and in index order. The frontier is unchanged.
   procedure Compact (S : in out Store; F : Frontier.State) with
     Global => null,
     Pre  => Valid (S, F),
     Post => Valid (S, F)
       and Collection (S) = Collection (S'Old)
       and Horizon (S) = Horizon (S'Old)
       and Entries (S) = Entries (S'Old)
       and Log_Length (S) <= Log_Length (S'Old)
       and (for all I in 1 .. Entries (S) =>
              I <= Entries (S'Old)
              and then Entry_At (S, I).H = Entry_At (S'Old, I).H
              and then Entry_At (S, I).Len = Entry_At (S'Old, I).Len)
       --  Contiguous, in index order, nothing else: the K-th frame of the
       --  log is the K-th entry's.
       and (if Entries (S) = 0 then Log_Length (S) = 0
            else Entry_At (S, 1).Off = 0
                 and then Log_Length (S) = End_Of (Entry_At (S, Entries (S))))
       and (for all I in 1 .. Entries (S) - 1 =>
              Entry_At (S, I + 1).Off = End_Of (Entry_At (S, I)))
       and Frames (S) = Entries (S)
       and (for all I in 1 .. Entries (S) =>
              I <= Frames (S) and then Frame_Start (S, I) = Entry_At (S, I).Off)
       --  Byte for byte the same frames.
       and (for all I in 1 .. Entries (S) =>
              I <= Entries (S'Old)
              and then End_Of (Entry_At (S, I)) <= Log_Length (S)
              and then End_Of (Entry_At (S'Old, I)) <= Log_Length (S'Old)
              and then (for all K in 0 .. Prefix_Len + Entry_At (S, I).Len - 1 =>
                          Log_Byte (S, Entry_At (S, I).Off + K) =
                            Log_Byte (S'Old, Entry_At (S'Old, I).Off + K)));

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

   --  Every index entry is a held, unexpired record whose frame is one of
   --  the log's frames, with its length and its kind's tag.
   procedure Lemma_Entry_Held (S : Store; F : Frontier.State; I : Held_Index) with
     Ghost, Global => null,
     Pre  => Valid (S, F) and then I <= Entries (S),
     Post => Holds (F, Entry_At (S, I).H)
       and then not Expired (Entry_At (S, I).H, Horizon (S))
       and then Has_Frame (S, Entry_At (S, I).Off)
       and then Natural (Len_At (S, Entry_At (S, I).Off)) = Entry_At (S, I).Len
       and then Log_Byte (S, Entry_At (S, I).Off + Prefix_Len) =
                  Kome.Records.Tag_Of (Entry_At (S, I).H.K)
       and then (for some K in 1 .. Frames (S) => Frame_Start (S, K) = Entry_At (S, I).Off);

   --  Every held, unexpired record is indexed.
   procedure Lemma_Held_Indexed (S : Store; F : Frontier.State; K : Held_Index) with
     Ghost, Global => null,
     Pre  => Valid (S, F)
             and then K <= Count (F)
             and then not Expired (Held (F, K), Horizon (S)),
     Post => Indexed (S, Held (F, K));

   --  Indexed, spelled out.
   procedure Lemma_Indexed (S : Store; X : Header) with
     Ghost, Global => null,
     Post => Indexed (S, X) = (for some I in 1 .. Entries (S) => Entry_At (S, I).H = X);

   --  The log is a chain of frames from offset 0 to its length: what a
   --  reader scanning it as a file relies on.
   procedure Lemma_Scan (S : Store; F : Frontier.State) with
     Ghost, Global => null,
     Pre  => Valid (S, F),
     Post => (Frames (S) = 0) = (Log_Length (S) = 0)
       and then (if Frames (S) > 0 then Frame_Start (S, 1) = 0)
       and then (for all K in 1 .. Frames (S) =>
                   Has_Frame (S, Frame_Start (S, K))
                   and then Next_Offset (S, Frame_Start (S, K)) =
                              (if K < Frames (S) then Frame_Start (S, K + 1)
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

   --  Frame boundaries of the log, in order. The model's stand-in for the
   --  file's own framing (a file binding finds them by scanning and keeps
   --  nothing). Sized by the discriminant alone (Ada allows nothing else in
   --  a component constraint); at most Log_Cap / Min_Frame are used.
   type Offset_Array is array (Positive range <>) of Log_Size;

   type Store (Cap : Held_Count; Log_Cap : Log_Size) is record
      NS  : Id128;
      Hz  : Time64     := No_Horizon;
      NI  : Held_Count := 0;
      Idx : Entry_Array (1 .. Cap);
      LL  : Log_Size   := 0;
      Log : Byte_Array (0 .. Log_Cap);   --  bytes 0 .. LL - 1 are the log
      NB  : Log_Size   := 0;
      Bnd : Offset_Array (1 .. Log_Cap);  --  Bnd (1 .. NB) are its frames
   end record
   with Dynamic_Predicate =>
     Store.NI <= Store.Cap and then Store.LL <= Store.Log_Cap
     and then Store.NB <= Store.Log_Cap;

   function Collection (S : Store) return Id128 is (S.NS);
   function Horizon (S : Store) return Time64 is (S.Hz);
   function Entries (S : Store) return Held_Count is (S.NI);
   function Entry_At (S : Store; I : Held_Index) return Index_Entry is (S.Idx (I));
   function Log_Length (S : Store) return Log_Size is (S.LL);
   function Log_Byte (S : Store; J : Natural) return Byte is (S.Log (J));
   function Frames (S : Store) return Natural is (S.NB);
   function Frame_Start (S : Store; K : Positive) return Log_Size is (S.Bnd (K));

   function Header_Of (Frame : Byte_Array) return Header is
     (case Kome.Records.Kind_Of (Frame) is
        when K_Put    => Kome.Records.To_Header (Kome.Records.Parse_Put (Frame)),
        when K_Del    => Kome.Records.To_Header (Kome.Records.Parse_Del (Frame)),
        when K_Roster => Kome.Records.To_Header (Kome.Records.Parse_Roster (Frame)),
        when K_Revoke => Kome.Records.To_Header (Kome.Records.Parse_Revoke (Frame)));

   function Members_Agree (Frame : Byte_Array; Members : Member_Keys) return Boolean is
     (if Kome.Records.Kind_Of (Frame) = K_Roster
      then Members'Length = Kome.Records.Parse_Roster (Frame).C.N_Members
           and then (for all I in 1 .. Members'Length =>
                       Members (Members'First + (I - 1)) =
                         Kome.Records.Member_Key (Kome.Records.Parse_Roster (Frame).C, I))
      else Members'Length = 0);

   ---------------------------------------------------------------------------
   --  The invariant, in parts over explicit components so that each step of
   --  an operation can re-establish one part at a time.
   ---------------------------------------------------------------------------

   function Has_Entry (Idx : Entry_Array; N : Held_Count; X : Header) return Boolean is
     (for some I in 1 .. N => Idx (I).H = X)
     with Pre => Idx'First = 1 and then N <= Idx'Last;

   --  The frontier's records are canonical (what makes a cell's PUT unique).
   function Canon (F : Frontier.State) return Boolean is
     (for all K in 1 .. Count (F) => Kome.Views.Canonical (Held (F, K)));

   --  The parts below are defined by their Posts rather than as expression
   --  functions, so that a goal that only carries one along sees one atom
   --  (an expression function is unfolded in every goal it appears in).

   --  Every entry is a held, unexpired record.
   function Live (F : Frontier.State; Hz : Time64; Idx : Entry_Array; N : Held_Count)
     return Boolean
   with
     Global => null,
     Pre  => Idx'First = 1 and then N <= Idx'Last,
     Post => Live'Result =
               (for all I in 1 .. N =>
                  Holds (F, Idx (I).H) and then not Expired (Idx (I).H, Hz));

   --  Entry E's frame is in Log (0 .. LL - 1).
   function Frame_OK (Log : Byte_Array; LL : Log_Size; E : Index_Entry) return Boolean is
     (E.Off <= LL
      and then LL - E.Off >= Prefix_Len + E.Len
      and then Kome.Keys.Word_Of (Log (E.Off), Log (E.Off + 1),
                                  Log (E.Off + 2), Log (E.Off + 3)) = Word (E.Len)
      and then Log (E.Off + Prefix_Len) = Kome.Records.Tag_Of (E.H.K))
     with Pre => Log'First = 0 and then LL <= Log'Last;

   function Framed (Log : Byte_Array; LL : Log_Size; Idx : Entry_Array; N : Held_Count)
     return Boolean
   with
     Global => null,
     Pre  => Log'First = 0 and then LL <= Log'Last
             and then Idx'First = 1 and then N <= Idx'Last,
     Post => Framed'Result = (for all I in 1 .. N => Frame_OK (Log, LL, Idx (I)));

   --  Entries are in log order, their frames disjoint, their records
   --  distinct.
   function Sorted (Idx : Entry_Array; N : Held_Count) return Boolean
   with
     Global => null,
     Pre  => Idx'First = 1 and then N <= Idx'Last,
     Post => Sorted'Result =
               (for all I in 1 .. N =>
                  (for all J in I + 1 .. N =>
                     End_Of (Idx (I)) <= Idx (J).Off and then Idx (I).H /= Idx (J).H));

   --  Every held, unexpired record is indexed.
   function Covered (F : Frontier.State; Hz : Time64; Idx : Entry_Array; N : Held_Count)
     return Boolean
   with
     Global => null,
     Pre  => Idx'First = 1 and then N <= Idx'Last,
     Post => Covered'Result =
               (for all K in 1 .. Count (F) =>
                  Expired (Held (F, K), Hz) or else Has_Entry (Idx, N, Held (F, K)));

   --  The length prefix at P (0 where there is none). Total, without a
   --  precondition, so that its definition is never guarded inside the
   --  quantifier of Chain.
   function Len_Word (Log : Byte_Array; P : Natural) return Word is
     (if P >= Log'First and then P <= Log'Last and then Log'Last - P >= 3
      then Kome.Keys.Word_Of (Log (P), Log (P + 1), Log (P + 2), Log (P + 3))
      else 0);

   --  A whole frame starts at P in Log (0 .. LL - 1).
   function Frame_At (Log : Byte_Array; LL : Log_Size; P : Natural) return Boolean is
     (LL <= Log'Last
      and then P <= LL
      and then LL - P >= Min_Frame
      and then Len_Word (Log, P) in 1 .. Kome.Records.Frame_Max
      and then Natural (Len_Word (Log, P)) <= LL - P - Prefix_Len);

   --  Bnd (1 .. NB) is a chain of frames from 0 to LL: the log is exactly
   --  a sequence of frames (each at least Min_Frame bytes), each ending
   --  where the next begins. Defined by its Post rather than as an
   --  expression function, so that provers see it as one atom until a
   --  proof needs its definition (Lemma_Chain_At in the body).
   function Chain (Log : Byte_Array; LL : Log_Size; Bnd : Offset_Array; NB : Natural)
     return Boolean
   with
     Global => null,
     Pre  => Log'First = 0 and then LL <= Log'Last
             and then Bnd'First = 1 and then NB <= Bnd'Last,
     Post => Chain'Result =
       ((NB = 0) = (LL = 0)
        and then (if NB > 0 then Bnd (1) = 0)
        and then NB <= LL / Min_Frame
        and then (for all K in 1 .. NB =>
                    Frame_At (Log, LL, Bnd (K))
                    and then Bnd (K) + Prefix_Len + Natural (Len_Word (Log, Bnd (K))) =
                               (if K < NB then Bnd (K + 1) else LL)));

   --  Every entry's frame is one of the chain's. Defined by its Post, like
   --  Chain, so that it stays one atom in goals that only carry it along.
   function At_Bounds (Idx : Entry_Array; N : Held_Count; Bnd : Offset_Array; NB : Natural)
     return Boolean
   with
     Global => null,
     Pre  => Idx'First = 1 and then N <= Idx'Last
             and then Bnd'First = 1 and then NB <= Bnd'Last,
     Post => At_Bounds'Result =
               (for all I in 1 .. N => (for some K in 1 .. NB => Bnd (K) = Idx (I).Off));

   function Valid (S : Store; F : Frontier.State) return Boolean is
     (Is_Frontier (F)
      and then Canon (F)
      and then Live (F, S.Hz, S.Idx, S.NI)
      and then Framed (S.Log, S.LL, S.Idx, S.NI)
      and then Sorted (S.Idx, S.NI)
      and then Covered (F, S.Hz, S.Idx, S.NI)
      and then Chain (S.Log, S.LL, S.Bnd, S.NB)
      and then At_Bounds (S.Idx, S.NI, S.Bnd, S.NB));

   function Indexed (S : Store; X : Header) return Boolean is
     (Has_Entry (S.Idx, S.NI, X));

end Kome.Store;
