--  Kome.Frontier: the replica state of one collection and its operations
--  (DESIGN.md §3, §4, §7; Frontier.lean `F`, `adm`, `applyD`, `expire`).
--
--  The state is the frontier F: the held records, each with an opaque
--  payload tag (below), and the ceiling cell (below). Nothing else in the
--  state is important.
--  Admission reads three views of the state (SIMPLIFY.md S6):
--    * Max_Ceil (F), maxceil(F): the largest ceiling_t of the held
--      rosters (Held_Ceil) and of the ceiling cell;
--    * In_W (F, k), k ∈ W(F): k is the subject of a held GRANT;
--    * W_Cap (F, k), wcap(F, k): the largest cap of the held GRANTs of k
--      (AUDIT.md A1).
--  They are opaque functions over the authorization rows (Max_Ceil also
--  reads the ceiling cell), each with a _Def lemma (Lemma_Held_Ceil_Def
--  and Lemma_Max_Ceil_Def, Lemma_In_W_Def, Lemma_W_Cap_Def). They are not
--  stored: a binding may cache them outside the proof. A record that is
--  not held never raises In_W or W_Cap, and raises Max_Ceil only through
--  the ceiling cell: a dominated roster or grant changes nothing
--  (DESIGN.md §4, D1′). Domination does not make them lose a value (T4',
--  Kome.Headers.Lemma_Dominator_Same_Key; Lemma_Views_Step):
--    * a roster leaves F only under a roster of its signer with a ceiling
--      that is at least its own ceiling;
--    * a grant leaves F only under a grant of the same issuer and subject
--      with a cap that is at least its own cap.
--
--  The ceiling cell (AUDIT.md H12; DESIGN.md §7). The state has one cell
--  outside the rows. It holds one roster, with a payload tag, that is not
--  a held record: Count, Held, Tag, Holds, Dom, Drops_Any, Run and Slot do
--  not read it, and only Max_Ceil does. Raise_Ceil writes it, for a
--  roster whose ceiling is above Max_Ceil. Kome.Store calls Raise_Ceil
--  for a roster that does not enter a row (Apply answered Auth_Full, or
--  the roster is the ceiling frame of a peer's HELLO), so a refusal for
--  room never keeps maxceil below a roster that the replica was offered.
--  Apply, Expire and Set_Tag never change the cell (Ceil_Same), and a
--  held record never leaves the rows because of it. The cell is a
--  max-register on the ceiling: Raise_Ceil requires a ceiling strictly
--  above Max_Ceil, which is at least the ceiling of the roster that the
--  cell held. There is no relation between the cell and the rows: the
--  cell's roster can also be held, and a held roster can have a ceiling
--  at or above the cell's (the cell is then not Ceil_Live).
--
--  Payload tags (SIMPLIFY.md S14). Each held record carries a Tag : U64
--  that the lattice ignores: Is_Frontier, Admitted, Dom and the views do
--  not read it. Apply takes the tag of the new record and stores it with
--  the header; every record that stays keeps its tag (Tag_Of). Kome.Store
--  packs the frame's place in the log into it.
--
--  Discard model (DESIGN.md §4, §10 item 1): Apply refuses inadmissible
--  records (Status = Inadmissible) and does not hold them, so the held
--  set is bounded. The peer that holds them offers them again, and
--  admission is monotone (T4'), so replicas converge (T4).
--
--  Capacity rows (E1, E9; DESIGN.md §7).
--    * Data records share one row of Cap records.
--    * Each signer has its own row, a *slice* of Slice_Max authorization
--      records, in one of Signers_Max slots.
--    * Slot 1 belongs to the founding key from Empty on.
--    * A certified root gets a slot when its first record is held. The
--      slot is never freed (a signer's record leaves F only under a
--      different record of the same signer).
--  Each dominator is in the same row as the record that it dominates
--  (Kome.Headers.Lemma_Same_Row), so one Apply changes exactly one row,
--  and drops records only in that row. A data Apply changes only the run
--  of its entity (Run, Outside_Run); an authorization Apply changes only
--  its signer's slot (Slot, Outside_Slot). A data flood or a stolen root
--  cannot take room from a different row, and the founding key's REVOKEs
--  are always held. A full row refuses with No_Space (data) or Auth_Full
--  (a slice, or the slot table; E2), and nothing changes.
--
--  Order of Apply (D11, DESIGN.md §7): admission, duplicate, domination,
--  room, commit. Nothing changes before the room decision. On each
--  refusal, nothing changes (T13): the Post says `Unchanged (S'Old, S)`.
--  (Kome.Store decides after an Auth_Full whether the roster goes to the
--  ceiling cell; Apply itself never writes the cell.)
--
--  Expiry (D10, DESIGN.md §7, SIMPLIFY.md S7): `Expire (F, Hz)` removes
--  the DELs with t <= Hz from the data row (G1: it is scoped to data) and
--  does not change an authorization row; Kome.Store computes Hz from
--  Max_Ceil and del_ttl. A DEL that arrives expired is applied by Apply
--  and then removed by Expire (Lean `applyH`).
--
--  Theorems:
--    * Apply refines Frontier.lean `applyD` (OK: F (held ++ [r]) for an
--      admitted r; Inadmissible: the state unchanged; nothing is lost
--      except by domination);
--    * T3 (the held set is its own frontier after each step);
--    * T4' (the admission views only grow, Lemma_Views_Step);
--    * T11 (a) (Expire leaves a frontier with no expired DEL and the same
--      authorization rows);
--    * T12 (an authorization record changes only its own row);
--    * T13 (bounds; each refusal leaves the state unchanged);
--    * T19, the part of this package (AUDIT.md H12): Raise_Ceil gives
--      Max_Ceil = Ceil_Of (R) for a roster above Max_Ceil and keeps the
--      rows (Same_Held); Lemma_Ceil_Bound bounds the ceiling of a held or
--      dominated record by Max_Ceil. Kome.Store states the step.
--
--  gnatprove 14 workaround (documented, keep it): State has no
--  Dynamic_Predicate, because gnatprove 14 crashes when it sees an
--  assignment of a State with a predicate. Clients must not assign a State
--  in proved code. They compare states with the ghost `Unchanged`, not
--  with "=". `Is_Frontier` carries the invariants in place of a predicate.
--  Each operation requires and preserves it. The accessors clamp to the
--  discriminant, so they are total on each State.
pragma Ada_2022;
with Kome.Headers; use Kome.Headers;
package Kome.Frontier with SPARK_Mode is

   --  Bound on the records that one replica holds for one collection
   --  (DESIGN.md §7): Cap data records plus Signers_Max * Slice_Max
   --  authorization records. The data capacity is set when the state is
   --  created (discriminant); Slice_Max is a constant (SIMPLIFY.md S15).
   Held_Max : constant := 2**20;
   subtype Held_Count is Natural range 0 .. Held_Max;
   subtype Held_Index is Natural range 1 .. Held_Max;

   type Header_Array is array (Held_Index range <>) of Header;

   --  (The names are not Data_Count and Slot_Count: those are the accessor
   --  functions below, and Ada does not overload a subtype with a
   --  function.)
   subtype Data_Size   is Natural range 0 .. Held_Max - Signers_Max * Slice_Max;
   subtype Slice_Count is Natural range 0 .. Slice_Max;
   subtype Slot_Index  is Positive range 1 .. Signers_Max;
   subtype Slot_Number is Natural range 0 .. Signers_Max;

   --  An index range First .. Last of the flat view (empty when
   --  Last < First). Run and Slot return one.
   subtype Range_First is Positive range 1 .. Held_Max + 1;
   type Index_Range is record
      First : Range_First := 1;
      Last  : Held_Count  := 0;
   end record;

   type State (Cap : Data_Size) is private;

   ---------------------------------------------------------------------
   --  Accessors
   ---------------------------------------------------------------------

   function Founding (S : State) return Key256 with Global => null;

   --  The data row.
   function Data_Count (S : State) return Data_Size with
     Global => null,
     Post   => Data_Count'Result <= S.Cap;
   function Data_Held (S : State; I : Held_Index) return Header with
     Global => null,
     Pre    => I <= Data_Count (S);
   function Data_Tag (S : State; I : Held_Index) return U64 with
     Global => null,
     Pre    => I <= Data_Count (S);

   --  The authorization rows: slot K belongs to signer Slot_Key (S, K).
   function Slots_Used (S : State) return Slot_Number with Global => null;
   function Slot_Key (S : State; K : Slot_Index) return Key256 with
     Global => null,
     Pre    => K <= Slots_Used (S);
   function Slot_Count (S : State; K : Slot_Index) return Slice_Count with
     Global => null;
   function Auth_Held (S : State; K : Slot_Index; J : Held_Index) return Header with
     Global => null,
     Pre    => K <= Slots_Used (S) and then J <= Slot_Count (S, K);
   function Auth_Tag (S : State; K : Slot_Index; J : Held_Index) return U64 with
     Global => null,
     Pre    => K <= Slots_Used (S) and then J <= Slot_Count (S, K);

   --  A signer's slot: 0 if no used slot has that key.
   function Slot_Of (S : State; Key : Key256) return Slot_Number with
     Global => null,
     Post   => (if Slot_Of'Result = 0
                then (for all K in 1 .. Slots_Used (S) => Slot_Key (S, K) /= Key)
                else Slot_Of'Result <= Slots_Used (S)
                     and then Slot_Key (S, Slot_Of'Result) = Key);

   --  The number of authorization records in the slots before K
   --  (Lemma_Frontier_Shape: Off (S, 1) = 0 and Off (S, K + 1) =
   --  Off (S, K) + Slot_Count (S, K)).
   function Off (S : State; K : Slot_Index) return Natural with Global => null;

   function Auth_Count (S : State) return Held_Count with
     Global => null,
     Post   => Auth_Count'Result <= Held_Max - Data_Count (S);

   function Count (S : State) return Held_Count with
     Global => null,
     Post   => Count'Result = Data_Count (S) + Auth_Count (S);

   --  The flat view: the data row, then slot 1, slot 2, and so on. Read it
   --  with Lemma_Held_Data, Lemma_Held_Auth and Lemma_Held_Cases.
   function Held (S : State; I : Held_Index) return Header with
     Global => null,
     Pre    => I <= Count (S);

   --  The payload tag of flat index I (Data_Tag or Auth_Tag, by the same
   --  lemmas).
   function Tag (S : State; I : Held_Index) return U64 with
     Global => null,
     Pre    => I <= Count (S);

   --  For a flat index after the data row, the slot that contains it.
   function Slot_At (S : State; I : Held_Index) return Slot_Index with
     Global => null;

   --  The tag of the held record X, 0 if X is not held (opaque;
   --  Lemma_Tag_Of).
   function Tag_Of (S : State; X : Header) return U64 with Global => null;

   --  Some index of S holds X with the tag T (opaque; Lemma_Has_Tag_Def).
   --  On a frontier a record is held at one index, so T is then Tag_Of
   --  (S, X) (Lemma_Has_Tag_Of). The Posts of Apply and Expire state
   --  tags with it: it needs no uniqueness, so it is linear to check.
   function Has_Tag (S : State; X : Header; T : U64) return Boolean with Global => null;

   ---------------------------------------------------------------------
   --  The admission views (SIMPLIFY.md S6; opaque, with _Def lemmas)
   ---------------------------------------------------------------------

   --  The largest ceiling_t of the held rosters, 0 if none (Frontier.lean
   --  `maxCeil` of the held list). Opaque; Lemma_Held_Ceil_Def. This is the
   --  function that Max_Ceil was before the ceiling cell.
   function Held_Ceil (S : State) return U48 with Global => null;

   --  The ceiling cell (AUDIT.md H12; DESIGN.md §7): whether it holds a
   --  roster, the roster, and its payload tag.
   function Has_Ceil (S : State) return Boolean with Global => null;
   function Ceil_Held (S : State) return Header with
     Global => null,
     Pre    => Has_Ceil (S);
   function Ceil_Tag (S : State) return U64 with
     Global => null,
     Pre    => Has_Ceil (S);

   --  The ceiling that the cell carries, 0 if it is empty.
   function Ceil_Value (S : State) return U48 is
     (if Has_Ceil (S) then Ceil_Of (Ceil_Held (S)) else 0);

   --  maxceil(F): the larger of Held_Ceil and the ceiling cell (opaque;
   --  Lemma_Max_Ceil_Def).
   function Max_Ceil (S : State) return U48 with Global => null;

   --  The cell is the only reason for maxceil: it is strictly above every
   --  held roster. A replica sends the cell's frame in its HELLO exactly
   --  then (DESIGN.md §8). When a held roster has the cell's ceiling or
   --  more, that roster is an element and travels as one.
   function Ceil_Live (S : State) return Boolean is
     (Has_Ceil (S) and then Ceil_Value (S) > Held_Ceil (S));

   --  The two states have the same cell, tag included. Quantifier-free.
   function Ceil_Same (Old, Upd : State) return Boolean is
     (Has_Ceil (Old) = Has_Ceil (Upd)
      and then (if Has_Ceil (Old)
                then Ceil_Held (Upd) = Ceil_Held (Old)
                     and then Ceil_Tag (Upd) = Ceil_Tag (Old)));

   --  R is a roster whose ceiling is above maxceil: the cell takes it.
   --  "Dominates" for the cell: a strict order on ceilings.
   function Raises_Ceil (S : State; R : Header) return Boolean is
     (R.K = K_Roster and then R.V.T > Max_Ceil (S));

   --  k ∈ W(F): F holds a GRANT of k (from any issuer).
   function In_W (S : State; K : Key256) return Boolean with Global => null;

   --  wcap(F, k): the largest cap of the held GRANTs of k, 0 if k is not
   --  a writer (Frontier.lean `wcap`).
   function W_Cap (S : State; K : Key256) return U48 with
     Global => null,
     Post   => (if not In_W (S, K) then W_Cap'Result = 0);

   ---------------------------------------------------------------------
   --  The lattice predicates
   ---------------------------------------------------------------------

   --  Admission (DESIGN.md §4; Frontier.lean `adm`): a data record is
   --  admitted iff t <= maxceil, author ∈ W and t <= wcap (author).
   --  Authorization records are always admitted.
   function Admitted (S : State; R : Header) return Boolean is
     (if Is_Data (R)
      then Data_T (R) <= Max_Ceil (S) and then In_W (S, Data_Author (R))
           and then Data_T (R) <= W_Cap (S, Data_Author (R))
      else True);

   --  Frontier.lean `Dom` restricted to admitted held records.
   function Dom (S : State; X : Header) return Boolean is
     (for some I in 1 .. Count (S) =>
        Admitted (S, Held (S, I)) and then Dominates (Held (S, I), X));

   function Holds (S : State; X : Header) return Boolean is
     (for some I in 1 .. Count (S) => Held (S, I) = X);

   --  R would drop a held record (opaque; Lemma_Drops_Any).
   function Drops_Any (S : State; R : Header) return Boolean with Global => null;

   --  The invariant that each State satisfies (opaque):
   --    * the held set is its own frontier (no held record dominates a
   --      held record);
   --    * no record is held two times;
   --    * each held record is canonical and admitted;
   --    * the data row holds data, sorted entity-major, and slot K holds
   --      authorization records issued by Slot_Key (S, K);
   --    * slot 1 belongs to the founding key, slot keys are distinct, and
   --      each used slot after slot 1 is not empty;
   --    * the rows are within their capacities;
   --    * the ceiling cell, if it holds a record, holds a canonical roster
   --      with a ceiling of at least 1 (Lemma_Frontier_Ceil).
   --  It does not read the tags.
   function Is_Frontier (S : State) return Boolean with Global => null;

   --  The rows are the same, tags included; the ceiling cell can differ
   --  (opaque, ghost; Lemma_Same_Held).
   function Same_Held (Old, Upd : State) return Boolean with Ghost, Global => null;

   --  Nothing observable changed, tags and the ceiling cell included
   --  (opaque, ghost; Lemma_Unchanged). Clients use this, not "=", on
   --  State (see the header comment).
   function Unchanged (Old, Upd : State) return Boolean with Ghost, Global => null;

   ---------------------------------------------------------------------
   --  Runs and slots (SIMPLIFY.md S14)
   ---------------------------------------------------------------------

   --  The data rows of entity Ent: Run (S, Ent).First .. Run (S, Ent).Last
   --  (Lemma_Run_Def). For an entity with no held record it is the empty
   --  range at the place where the entity's records would go.
   function Run (S : State; Ent : Id128) return Index_Range with
     Global => null,
     Pre    => Is_Frontier (S),
     Post   => Run'Result.Last <= Data_Count (S)
               and then Run'Result.First <= Run'Result.Last + 1;

   --  The flat indices of the authorization rows of Signer, its slot
   --  (Lemma_Slot_Def). For a signer with no slot it is the empty range
   --  after the last held record.
   function Slot (S : State; Signer : Key256) return Index_Range with
     Global => null,
     Post   => (if Slot_Of (S, Signer) = 0
                then Slot'Result.First = Count (S) + 1 and then Slot'Result.Last = Count (S)
                else Slot'Result.First = Data_Count (S) + Off (S, Slot_Of (S, Signer)) + 1
                     and then Slot'Result.Last
                              = Data_Count (S) + Off (S, Slot_Of (S, Signer))
                                + Slot_Count (S, Slot_Of (S, Signer)));

   --  A data step for entity E changed nothing outside E's run (opaque,
   --  ghost; Lemma_Outside_Run): the records before the run did not move,
   --  the records after it moved by the change in its length, tags
   --  included, and no authorization row changed.
   function Outside_Run (Old, Upd : State; E : Id128) return Boolean with
     Ghost, Global => null,
     Pre => Is_Frontier (Old) and then Is_Frontier (Upd);

   --  An authorization step for Signer changed nothing outside Signer's
   --  slot (opaque, ghost; Lemma_Outside_Slot): the data row and every
   --  other slot are the same, tags included.
   function Outside_Slot (Old, Upd : State; Signer : Key256) return Boolean with
     Ghost, Global => null,
     Pre => Is_Frontier (Old) and then Is_Frontier (Upd);

   ---------------------------------------------------------------------
   --  Operations
   ---------------------------------------------------------------------

   function Empty (Founding : Key256; Cap : Data_Size) return State with
     Global => null,
     Post   => Empty'Result.Cap = Cap
               and then Kome.Frontier.Founding (Empty'Result) = Founding
               and then Count (Empty'Result) = 0
               and then Data_Count (Empty'Result) = 0
               and then Slots_Used (Empty'Result) = 1
               and then Slot_Key (Empty'Result, 1) = Founding
               and then Slot_Count (Empty'Result, 1) = 0
               and then Max_Ceil (Empty'Result) = 0
               and then Is_Frontier (Empty'Result)
               and then not Has_Ceil (Empty'Result);

   --  Apply one record R with payload tag T (DESIGN.md §7 steps 1-6).
   --    * OK means that R is held, now or before. A duplicate is a no-op
   --      (its old tag stays) and also gives OK, so to apply a set with
   --      repetitions is to apply the set.
   --    * Dominated means that a held record beats R.
   --    * Inadmissible, No_Space and Auth_Full are refusals.
   --  Each outcome other than a new hold leaves the state Unchanged. A new
   --  hold of a data record changes only R's run (Outside_Run), and of an
   --  authorization record only its signer's slot (Outside_Slot). No
   --  outcome changes the ceiling cell (Ceil_Same).
   procedure Apply (S : in out State; R : Header; T : U64; Result : out Status) with
     Global => null,
     Pre    => Is_Frontier (S) and then Canonical (R),
     Post   => Is_Frontier (S)
       and then Founding (S) = Founding (S'Old)
       and then Result in OK | Dominated | Inadmissible | No_Space | Auth_Full
       and then (Result = Inadmissible) = not Admitted (S'Old, R)
       and then (Result = Dominated)
                = (Admitted (S'Old, R) and then not Holds (S'Old, R)
                   and then Dom (S'Old, R))
       and then (Result = No_Space)
                = (Admitted (S'Old, R) and then not Holds (S'Old, R)
                   and then not Dom (S'Old, R) and then Is_Data (R)
                   and then Data_Count (S'Old) = S.Cap
                   and then not Drops_Any (S'Old, R))
       and then (Result = Auth_Full)
                = (Is_Auth (R) and then not Holds (S'Old, R)
                   and then not Dom (S'Old, R)
                   and then
                     --  (a) the signer's slice is full, R frees no room
                     ((Slot_Of (S'Old, R.Issuer) /= 0
                       and then Slot_Count (S'Old, Slot_Of (S'Old, R.Issuer)) = Slice_Max
                       and then not Drops_Any (S'Old, R))
                      --  (b) a new signer, and all slots are used
                      or else (Slot_Of (S'Old, R.Issuer) = 0
                               and then Slots_Used (S'Old) = Signers_Max)))
       and then (if Result /= OK or else Holds (S'Old, R) then Unchanged (S'Old, S))
       and then (if Result = OK then
                   Holds (S, R)
                   and then Max_Ceil (S) = U48'Max (Max_Ceil (S'Old), Ceil_Of (R))
                   --  Frontier.lean `keep`: a filter of held ++ [r].
                   and then (for all I in 1 .. Count (S) =>
                               Holds (S'Old, Held (S, I)) or else Held (S, I) = R)
                   --  Nothing is lost except by domination.
                   and then (for all I in 1 .. Count (S'Old) =>
                               Holds (S, Held (S'Old, I))
                               or else Dominates (R, Held (S'Old, I))))
       and then (if Result = OK and then not Holds (S'Old, R) then
                   --  R has the tag T; every other record keeps its tag.
                   (for all I in 1 .. Count (S) =>
                      (if Held (S, I) = R then Tag (S, I) = T
                                    else Has_Tag (S'Old, Held (S, I), Tag (S, I))))
                   and then (if Is_Data (R) then Outside_Run (S'Old, S, R.Ent)
                             else Outside_Slot (S'Old, S, R.Issuer)))
       and then Ceil_Same (S'Old, S);

   --  Tombstone expiry at the horizon Hz (D10, DESIGN.md §7, T11 (a),
   --  SIMPLIFY.md S7): remove from the data row exactly the DELs with
   --  t <= Hz. Only the data row changes; the survivors keep their order
   --  and their tags.
   procedure Expire (S : in out State; Hz : U48) with
     Global => null,
     Pre    => Is_Frontier (S),
     Post   => Is_Frontier (S)
       and then Founding (S) = Founding (S'Old)
       and then Max_Ceil (S) = Max_Ceil (S'Old)
       and then Data_Count (S) <= Data_Count (S'Old)
       --  No authorization slot changes.
       and then Slots_Used (S) = Slots_Used (S'Old)
       and then Auth_Count (S) = Auth_Count (S'Old)
       and then (for all K in Slot_Index =>
                   Slot_Count (S, K) = Slot_Count (S'Old, K)
                   and then Off (S, K) = Off (S'Old, K))
       and then (for all K in 1 .. Slots_Used (S) =>
                   Slot_Key (S, K) = Slot_Key (S'Old, K)
                   and then (for all J in 1 .. Slot_Count (S, K) =>
                               Auth_Held (S, K, J) = Auth_Held (S'Old, K, J)
                               and then Auth_Tag (S, K, J) = Auth_Tag (S'Old, K, J)))
       --  The data row is the old one without the expired DELs.
       and then (for all I in 1 .. Data_Count (S) =>
                   Holds (S'Old, Data_Held (S, I))
                   and then not Expired (Data_Held (S, I), Hz)
                   and then Has_Tag (S'Old, Data_Held (S, I), Data_Tag (S, I)))
       and then (for all I in 1 .. Data_Count (S'Old) =>
                   Expired (Data_Held (S'Old, I), Hz)
                   or else Holds (S, Data_Held (S'Old, I)))
       and then Ceil_Same (S'Old, S);

   --  Give the record at flat index I the payload tag T (SIMPLIFY.md S14:
   --  Kome.Store.Compact moves the record's frame in the log and writes
   --  its new place). Only that tag changes: the rows, their records, the
   --  views and every other tag stay. The lattice does not read tags, so
   --  the state stays a frontier.
   procedure Set_Tag (S : in out State; I : Held_Index; T : U64) with
     Global => null,
     Pre    => Is_Frontier (S) and then I <= Count (S),
     Post   => Is_Frontier (S)
       and then Founding (S) = Founding (S'Old)
       and then Max_Ceil (S) = Max_Ceil (S'Old)
       and then Data_Count (S) = Data_Count (S'Old)
       and then Auth_Count (S) = Auth_Count (S'Old)
       and then Count (S) = Count (S'Old)
       and then Slots_Used (S) = Slots_Used (S'Old)
       and then (for all K in Slot_Index =>
                   Slot_Count (S, K) = Slot_Count (S'Old, K)
                   and then Off (S, K) = Off (S'Old, K))
       and then (for all K in 1 .. Slots_Used (S) =>
                   Slot_Key (S, K) = Slot_Key (S'Old, K)
                   and then (for all J in 1 .. Slot_Count (S, K) =>
                               Auth_Held (S, K, J) = Auth_Held (S'Old, K, J)))
       and then (for all J in 1 .. Data_Count (S) => Data_Held (S, J) = Data_Held (S'Old, J))
       and then (for all J in 1 .. Count (S) =>
                   Held (S, J) = Held (S'Old, J)
                   and then Tag (S, J) = (if J = I then T else Tag (S'Old, J)))
       and then Ceil_Same (S'Old, S);

   --  Put the roster R with payload tag T in the ceiling cell (AUDIT.md
   --  H12). Kome.Store calls it for a roster whose ceiling is above maxceil
   --  and that does not enter a row: Apply refused it with Auth_Full, or it
   --  is the ceiling frame of a peer's HELLO. The rows do not change. The
   --  record that the cell held, if any, is gone: it was not a held record,
   --  and R's ceiling is above its ceiling.
   procedure Raise_Ceil (S : in out State; R : Header; T : U64) with
     Global => null,
     Pre    => Is_Frontier (S) and then Canonical (R) and then Raises_Ceil (S, R),
     Post   => Is_Frontier (S)
       and then Founding (S) = Founding (S'Old)
       and then Same_Held (S'Old, S)
       and then Has_Ceil (S) and then Ceil_Held (S) = R and then Ceil_Tag (S) = T
       and then Max_Ceil (S) = Ceil_Of (R);

   --  Give the cell's record the payload tag T (Kome.Store.Compact moves
   --  the record's frame in the log and writes its new place). Only that
   --  tag changes.
   procedure Set_Ceil_Tag (S : in out State; T : U64) with
     Global => null,
     Pre    => Is_Frontier (S) and then Has_Ceil (S),
     Post   => Is_Frontier (S)
       and then Founding (S) = Founding (S'Old)
       and then Same_Held (S'Old, S)
       and then Has_Ceil (S) and then Ceil_Held (S) = Ceil_Held (S'Old)
       and then Ceil_Tag (S) = T
       and then Max_Ceil (S) = Max_Ceil (S'Old);

   ---------------------------------------------------------------------
   --  Lemmas
   ---------------------------------------------------------------------

   --  The flat view, data part.
   procedure Lemma_Held_Data (S : State; I : Held_Index) with
     Ghost, Global => null,
     Pre  => I <= Data_Count (S),
     Post => I <= Count (S) and then Held (S, I) = Data_Held (S, I)
             and then Tag (S, I) = Data_Tag (S, I);

   --  The flat view, slot K.
   procedure Lemma_Held_Auth (S : State; K : Slot_Index; J : Held_Index) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S) and then K <= Slots_Used (S)
             and then J <= Slot_Count (S, K),
     Post => Data_Count (S) + Off (S, K) + J <= Count (S)
             and then Slot_At (S, Data_Count (S) + Off (S, K) + J) = K
             and then Held (S, Data_Count (S) + Off (S, K) + J) = Auth_Held (S, K, J)
             and then Tag (S, Data_Count (S) + Off (S, K) + J) = Auth_Tag (S, K, J);

   --  Each flat index is one of the two.
   procedure Lemma_Held_Cases (S : State; I : Held_Index) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S) and then I <= Count (S),
     Post => (if I <= Data_Count (S) then
                Held (S, I) = Data_Held (S, I) and then Tag (S, I) = Data_Tag (S, I)
              else Slot_At (S, I) <= Slots_Used (S)
                   and then I - Data_Count (S) - Off (S, Slot_At (S, I)) >= 1
                   and then I - Data_Count (S) - Off (S, Slot_At (S, I))
                            <= Slot_Count (S, Slot_At (S, I))
                   and then Held (S, I)
                            = Auth_Held (S, Slot_At (S, I),
                                         I - Data_Count (S) - Off (S, Slot_At (S, I)))
                   and then Tag (S, I)
                            = Auth_Tag (S, Slot_At (S, I),
                                        I - Data_Count (S) - Off (S, Slot_At (S, I))));

   --  The shape of a frontier's rows and slots.
   procedure Lemma_Frontier_Shape (S : State) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S),
     Post => S.Cap + Signers_Max * Slice_Max <= Held_Max
             and then Slots_Used (S) >= 1
             and then Slot_Key (S, 1) = Founding (S)
             and then (for all K in 1 .. Slots_Used (S) =>
                         (for all K2 in 1 .. Slots_Used (S) =>
                            (if K /= K2 then Slot_Key (S, K) /= Slot_Key (S, K2))))
             and then (for all K in 2 .. Slots_Used (S) => Slot_Count (S, K) >= 1)
             and then (for all K in Slot_Index =>
                         (if K > Slots_Used (S) then Slot_Count (S, K) = 0))
             and then Off (S, 1) = 0
             and then (for all K in 1 .. Signers_Max - 1 =>
                         Off (S, K + 1) = Off (S, K) + Slot_Count (S, K))
             and then Auth_Count (S) = Off (S, Signers_Max) + Slot_Count (S, Signers_Max)
             and then Count (S) <= S.Cap + Signers_Max * Slice_Max;

   --  Each held data record is data, canonical and admitted.
   procedure Lemma_Frontier_Data (S : State; I : Held_Index) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S) and then I <= Data_Count (S),
     Post => Is_Data (Data_Held (S, I)) and then Canonical (Data_Held (S, I))
             and then Admitted (S, Data_Held (S, I));

   --  Each record of slot K is an authorization record issued by its key.
   procedure Lemma_Frontier_Auth (S : State; K : Slot_Index; J : Held_Index) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S) and then K <= Slots_Used (S)
             and then J <= Slot_Count (S, K),
     Post => Is_Auth (Auth_Held (S, K, J)) and then Canonical (Auth_Held (S, K, J))
             and then Auth_Held (S, K, J).Issuer = Slot_Key (S, K);

   --  In the flat view: each held record is canonical, admitted, not
   --  dominated by a held record, and held one time.
   procedure Lemma_Frontier_Held (S : State; I : Held_Index) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S) and then I <= Count (S),
     Post => Canonical (Held (S, I))
             and then Admitted (S, Held (S, I))
             and then not Dom (S, Held (S, I))
             and then (for all J in 1 .. Count (S) =>
                         not Dominates (Held (S, J), Held (S, I)))
             and then (for all J in 1 .. Count (S) =>
                         (if J /= I then Held (S, J) /= Held (S, I)));

   --  The tag of a held record is the tag at its (unique) index.
   procedure Lemma_Tag_Of (S : State; I : Held_Index) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S) and then I <= Count (S),
     Post => Tag_Of (S, Held (S, I)) = Tag (S, I);

   procedure Lemma_Has_Tag_Def (S : State; X : Header; T : U64) with
     Ghost, Global => null,
     Post => Has_Tag (S, X, T)
             = (for some J in 1 .. Count (S) => Held (S, J) = X and then Tag (S, J) = T);

   procedure Lemma_Has_Tag_Of (S : State; X : Header; T : U64) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S) and then Has_Tag (S, X, T),
     Post => Tag_Of (S, X) = T;

   --  The ceiling cell of a frontier holds a canonical roster, and its
   --  ceiling is at least 1.
   procedure Lemma_Frontier_Ceil (S : State) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S) and then Has_Ceil (S),
     Post => Ceil_Held (S).K = K_Roster and then Canonical (Ceil_Held (S))
             and then Ceil_Value (S) = Ceil_Held (S).V.T
             and then Ceil_Value (S) >= 1;

   --  The definitions of the admission views (SIMPLIFY.md S6).
   --  Held_Ceil bounds the ceiling of each held record, and it is the
   --  ceiling of a held roster, or 0.
   procedure Lemma_Held_Ceil_Def (S : State) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S),
     Post => (for all I in 1 .. Count (S) => Ceil_Of (Held (S, I)) <= Held_Ceil (S))
             and then (Held_Ceil (S) = 0
                       or else (for some I in 1 .. Count (S) =>
                                  Held (S, I).K = K_Roster
                                  and then Held (S, I).V.T = Held_Ceil (S)));

   --  maxceil is the larger of the held rosters' ceiling and the cell's.
   procedure Lemma_Max_Ceil_Def (S : State) with
     Ghost, Global => null,
     Post => Max_Ceil (S) = U48'Max (Held_Ceil (S), Ceil_Value (S));

   --  A held or dominated record carries no ceiling above Held_Ceil
   --  (Kome.Headers.Lemma_Dominator_Same_Key). Kome.Store uses it for the
   --  step of T19.
   procedure Lemma_Ceil_Bound (S : State; R : Header) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S) and then (Holds (S, R) or else Dom (S, R)),
     Post => Ceil_Of (R) <= Held_Ceil (S) and then Ceil_Of (R) <= Max_Ceil (S);

   --  k ∈ W iff F holds a GRANT of k.
   procedure Lemma_In_W_Def (S : State; K : Key256) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S),
     Post => In_W (S, K)
             = (for some I in 1 .. Count (S) =>
                  Held (S, I).K = K_Grant and then Held (S, I).V.Author = K);

   --  wcap(k) bounds the cap of each held GRANT of k, and it is the cap
   --  of a held GRANT of k, or 0 if there is none (Frontier.lean
   --  `wcap_F`).
   procedure Lemma_W_Cap_Def (S : State; K : Key256) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S),
     Post => (for all I in 1 .. Count (S) =>
                (if Held (S, I).K = K_Grant and then Held (S, I).V.Author = K
                 then Held (S, I).V.T <= W_Cap (S, K)))
             and then (if In_W (S, K)
                       then (for some I in 1 .. Count (S) =>
                               Held (S, I).K = K_Grant and then Held (S, I).V.Author = K
                               and then Held (S, I).V.T = W_Cap (S, K))
                       else W_Cap (S, K) = 0);

   --  T4' (the admission views only grow), Frontier.lean `maxCeil_F` and
   --  `wcap_F`: across a step whose result holds R, is a filter of
   --  Before ++ [R] and loses nothing except by domination (the Post of
   --  Apply when Result = OK), the views are those of Before joined with
   --  R's contribution. Max_Ceil follows Held_Ceil when the two states
   --  carry the same ceiling in the cell (Apply: Ceil_Same).
   procedure Lemma_Views_Step (Before, After : State; R : Header; K : Key256) with
     Ghost, Global => null,
     Pre  => Is_Frontier (Before) and then Is_Frontier (After)
             and then Holds (After, R)
             and then (for all I in 1 .. Count (After) =>
                         Holds (Before, Held (After, I)) or else Held (After, I) = R)
             and then (for all I in 1 .. Count (Before) =>
                         Holds (After, Held (Before, I))
                         or else Dominates (R, Held (Before, I))),
     Post => Held_Ceil (After) = U48'Max (Held_Ceil (Before), Ceil_Of (R))
             and then (if Ceil_Value (After) = Ceil_Value (Before)
                       then Max_Ceil (After) = U48'Max (Max_Ceil (Before), Ceil_Of (R)))
             and then In_W (After, K)
                      = (In_W (Before, K) or else (R.K = K_Grant and then R.V.Author = K))
             and then W_Cap (After, K)
                      = (if R.K = K_Grant and then R.V.Author = K
                         then U48'Max (W_Cap (Before, K), R.V.T)
                         else W_Cap (Before, K));

   --  Two frontiers with the same authorization rows have the same
   --  admission views (Expire gives the hypothesis); for Max_Ceil, when
   --  their cells also carry the same ceiling.
   procedure Lemma_Same_Auth_Views (S1, S2 : State; K : Key256) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S1) and then Is_Frontier (S2)
             and then Slots_Used (S1) = Slots_Used (S2)
             and then (for all K2 in Slot_Index => Slot_Count (S1, K2) = Slot_Count (S2, K2))
             and then (for all K2 in 1 .. Slots_Used (S1) =>
                         (for all J in 1 .. Slot_Count (S1, K2) =>
                            Auth_Held (S1, K2, J) = Auth_Held (S2, K2, J))),
     Post => Held_Ceil (S1) = Held_Ceil (S2)
             and then (if Ceil_Value (S1) = Ceil_Value (S2)
                       then Max_Ceil (S1) = Max_Ceil (S2))
             and then In_W (S1, K) = In_W (S2, K)
             and then W_Cap (S1, K) = W_Cap (S2, K);

   --  The run of an entity: exactly the data rows of that entity.
   procedure Lemma_Run_Def (S : State; E : Id128) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S),
     Post => (declare
                R : constant Index_Range := Run (S, E);
              begin
                (for all I in 1 .. Data_Count (S) =>
                   (Data_Held (S, I).Ent = E) = (I in R.First .. R.Last)));

   --  The slot of a signer: exactly the held authorization records that
   --  it issued, and they are Auth_Held of its slot in order.
   procedure Lemma_Slot_Def (S : State; Signer : Key256) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S),
     Post => (declare
                R : constant Index_Range := Slot (S, Signer);
              begin
                R.Last <= Count (S)
                and then (for all I in 1 .. Count (S) =>
                            (Is_Auth (Held (S, I)) and then Held (S, I).Issuer = Signer)
                            = (I in R.First .. R.Last))
                and then (for all I in R.First .. R.Last =>
                            Held (S, I) = Auth_Held (S, Slot_Of (S, Signer), I - R.First + 1)
                            and then Tag (S, I)
                                     = Auth_Tag (S, Slot_Of (S, Signer), I - R.First + 1)));

   --  What Outside_Run means.
   procedure Lemma_Outside_Run (Old, Upd : State; E : Id128) with
     Ghost, Global => null,
     Pre  => Is_Frontier (Old) and then Is_Frontier (Upd)
             and then Outside_Run (Old, Upd, E),
     Post => (declare
                RO : constant Index_Range := Run (Old, E);
                RU : constant Index_Range := Run (Upd, E);
              begin
                RU.First = RO.First
                and then Data_Count (Upd) - RU.Last = Data_Count (Old) - RO.Last
                and then (for all I in 1 .. RO.First - 1 =>
                            Data_Held (Upd, I) = Data_Held (Old, I)
                            and then Data_Tag (Upd, I) = Data_Tag (Old, I))
                and then (for all I in RO.Last + 1 .. Data_Count (Old) =>
                            Data_Held (Upd, I - RO.Last + RU.Last) = Data_Held (Old, I)
                            and then Data_Tag (Upd, I - RO.Last + RU.Last) = Data_Tag (Old, I)))
             and then Slots_Used (Upd) = Slots_Used (Old)
             and then (for all K in Slot_Index =>
                         Slot_Count (Upd, K) = Slot_Count (Old, K)
                         and then Off (Upd, K) = Off (Old, K))
             and then (for all K in 1 .. Slots_Used (Old) =>
                         Slot_Key (Upd, K) = Slot_Key (Old, K)
                         and then (for all J in 1 .. Slot_Count (Old, K) =>
                                     Auth_Held (Upd, K, J) = Auth_Held (Old, K, J)
                                     and then Auth_Tag (Upd, K, J) = Auth_Tag (Old, K, J)));

   --  What Outside_Slot means.
   procedure Lemma_Outside_Slot (Old, Upd : State; Signer : Key256) with
     Ghost, Global => null,
     Pre  => Is_Frontier (Old) and then Is_Frontier (Upd)
             and then Outside_Slot (Old, Upd, Signer),
     Post => Data_Count (Upd) = Data_Count (Old)
             and then (for all I in 1 .. Data_Count (Old) =>
                         Data_Held (Upd, I) = Data_Held (Old, I)
                         and then Data_Tag (Upd, I) = Data_Tag (Old, I))
             and then Slot_Of (Upd, Signer) /= 0
             and then (if Slot_Of (Old, Signer) /= 0
                       then Slot_Of (Upd, Signer) = Slot_Of (Old, Signer)
                            and then Slots_Used (Upd) = Slots_Used (Old)
                       else Slot_Of (Upd, Signer) = Slots_Used (Old) + 1
                            and then Slots_Used (Upd) = Slots_Used (Old) + 1)
             and then (for all K in 1 .. Slots_Used (Old) =>
                         Slot_Key (Upd, K) = Slot_Key (Old, K))
             and then (for all K in Slot_Index =>
                         (if K /= Slot_Of (Upd, Signer) then
                            Slot_Count (Upd, K) = Slot_Count (Old, K)
                            and then (for all J in 1 .. Slot_Count (Old, K) =>
                                        Auth_Held (Upd, K, J) = Auth_Held (Old, K, J)
                                        and then Auth_Tag (Upd, K, J) = Auth_Tag (Old, K, J))));

   procedure Lemma_Drops_Any (S : State; R : Header) with
     Ghost, Global => null,
     Post => Drops_Any (S, R)
             = (for some I in 1 .. Count (S) => Dominates (R, Held (S, I)));

   --  Unchanged is reflexive: a state that did not change is Unchanged.
   --  A refusal that never calls an operation on S (Kome.Store) gives its
   --  "nothing changed" Post with this lemma.
   procedure Lemma_Unchanged_Refl (S : State) with
     Ghost, Global => null,
     Post => Unchanged (S, S);

   --  What Same_Held means through the public view. It is executable: the
   --  counts of the state bound each quantifier, so -gnata runs it.
   --  (For In_W and W_Cap, Lemma_Same_Auth_Views.)
   procedure Lemma_Same_Held (Old, Upd : State) with
     Ghost, Global => null,
     Pre  => Same_Held (Old, Upd),
     Post => Old.Cap = Upd.Cap
             and then Founding (Upd) = Founding (Old)
             and then Held_Ceil (Upd) = Held_Ceil (Old)
             and then Data_Count (Upd) = Data_Count (Old)
             and then (for all I in 1 .. Data_Count (Old) =>
                         Data_Held (Upd, I) = Data_Held (Old, I)
                         and then Data_Tag (Upd, I) = Data_Tag (Old, I))
             and then Slots_Used (Upd) = Slots_Used (Old)
             and then (for all K in Slot_Index =>
                         Slot_Count (Upd, K) = Slot_Count (Old, K)
                         and then Off (Upd, K) = Off (Old, K))
             and then (for all K in 1 .. Slots_Used (Old) =>
                         Slot_Key (Upd, K) = Slot_Key (Old, K)
                         and then (for all J in 1 .. Slot_Count (Old, K) =>
                                     Auth_Held (Upd, K, J) = Auth_Held (Old, K, J)
                                     and then Auth_Tag (Upd, K, J) = Auth_Tag (Old, K, J)))
             and then Auth_Count (Upd) = Auth_Count (Old)
             and then Count (Upd) = Count (Old)
             and then (for all I in 1 .. Count (Old) =>
                         Held (Upd, I) = Held (Old, I) and then Tag (Upd, I) = Tag (Old, I));

   --  What Unchanged means through the public view: the rows are the same
   --  (Same_Held, Lemma_Same_Held) and so is the ceiling cell. It is
   --  executable, as Lemma_Same_Held is.
   procedure Lemma_Unchanged (Old, Upd : State) with
     Ghost, Global => null,
     Pre  => Unchanged (Old, Upd),
     Post => Old.Cap = Upd.Cap
             and then Founding (Upd) = Founding (Old)
             and then Max_Ceil (Upd) = Max_Ceil (Old)
             and then Data_Count (Upd) = Data_Count (Old)
             and then (for all I in 1 .. Data_Count (Old) =>
                         Data_Held (Upd, I) = Data_Held (Old, I)
                         and then Data_Tag (Upd, I) = Data_Tag (Old, I))
             and then Slots_Used (Upd) = Slots_Used (Old)
             and then (for all K in Slot_Index =>
                         Slot_Count (Upd, K) = Slot_Count (Old, K)
                         and then Off (Upd, K) = Off (Old, K))
             and then (for all K in 1 .. Slots_Used (Old) =>
                         Slot_Key (Upd, K) = Slot_Key (Old, K)
                         and then (for all J in 1 .. Slot_Count (Old, K) =>
                                     Auth_Held (Upd, K, J) = Auth_Held (Old, K, J)
                                     and then Auth_Tag (Upd, K, J) = Auth_Tag (Old, K, J)))
             and then Auth_Count (Upd) = Auth_Count (Old)
             and then Count (Upd) = Count (Old)
             and then (for all I in 1 .. Count (Old) =>
                         Held (Upd, I) = Held (Old, I) and then Tag (Upd, I) = Tag (Old, I))
             and then Ceil_Same (Old, Upd)
             and then Same_Held (Old, Upd);

private

   --  A held record and its payload tag. Each move of a header moves its
   --  entry, so the tag goes with it.
   type Entry_Rec is record
      Hdr : Header;
      Tag : U64 := 0;
   end record;
   type Entry_Array is array (Held_Index range <>) of Entry_Rec;

   subtype Slice_Pos is Positive range 1 .. Slice_Max;
   type Auth_Matrix is array (Slot_Index, Slice_Pos) of Entry_Rec;
   type Slot_Counts is array (Slot_Index) of Slice_Count;
   type Slot_Keys   is array (Slot_Index) of Key256;
   --  Offs (K) <= (K - 1) * Slice_Max (Lemma_Frontier_Shape); the total
   --  can reach Signers_Max * Slice_Max.
   subtype Off_Value  is Natural range 0 .. (Signers_Max - 1) * Slice_Max;
   subtype Auth_Total is Natural range 0 .. Signers_Max * Slice_Max;
   type Slot_Offs   is array (Slot_Index) of Off_Value;

   --  The ceiling cell (AUDIT.md H12): the roster with the largest ceiling
   --  that reached this replica without entering a row, and its payload
   --  tag (Kome.Store: the place of its CEIL entry in the log).
   --  The header and the tag are two components, not one Entry_Rec: with
   --  an Entry_Rec as a record component of Auth_Rows, gnatprove 14 no
   --  longer proves the row lemmas of the body (Lemma_Same_Auth_Views is
   --  the smallest case), although no row lemma reads the cell.
   type Ceil_Cell is record
      Present : Boolean := False;
      Hdr     : Header;
      Tag     : U64 := 0;
   end record;

   --  The authorization rows:
   --    * one row of Slice_Max records for each signer slot;
   --    * the number of records in each row (NA);
   --    * the signer of each slot (Keys);
   --    * the number of used slots;
   --    * the offsets of the flat view, and the total;
   --    * the ceiling cell (C). It is here, not beside the rows, so that
   --      Max_Ceil stays a function of this record. No row view reads it.
   --  They are a separate record, so an operation on the data row keeps
   --  this component equal as a whole (then the prover needs no frame
   --  lemma).
   type Auth_Rows is record
      H      : Auth_Matrix;
      NA     : Slot_Counts := [others => 0];
      Keys   : Slot_Keys   := [others => (others => 0)];
      NSlots : Slot_Number := 0;
      Offs   : Slot_Offs   := [others => 0];
      NAuth  : Auth_Total  := 0;
      C      : Ceil_Cell;
   end record;

   --  Records in slot K.
   function SC (A : Auth_Rows; K : Slot_Index) return Slice_Count is (A.NA (K));

   --  Data_E (1 .. ND) is sorted entity-major by (ent, kind, fh), strictly
   --  (AUDIT.md G25; the body's Data_Sorted, a conjunct of Is_Frontier).
   --  An entity's records are one run, its DEL first. Every dominator of
   --  a data record is in that record's run, so Apply finds the run with
   --  one binary search and reads only the run. Clients see the order
   --  through Data_Held, Held, Run and quantifiers over them.
   type State (Cap : Data_Size) is record
      Fnd    : Key256;
      Data_E : Entry_Array (1 .. Cap);
      ND     : Data_Size := 0;
      A      : Auth_Rows;
   end record;

   function Founding (S : State) return Key256 is (S.Fnd);

   function Data_Count (S : State) return Data_Size is
     (if S.ND <= S.Cap then S.ND else S.Cap);
   function Data_Held (S : State; I : Held_Index) return Header is (S.Data_E (I).Hdr);
   function Data_Tag (S : State; I : Held_Index) return U64 is (S.Data_E (I).Tag);

   function Slots_Used (S : State) return Slot_Number is (S.A.NSlots);
   function Slot_Key (S : State; K : Slot_Index) return Key256 is (S.A.Keys (K));
   function Slot_Count (S : State; K : Slot_Index) return Slice_Count is (SC (S.A, K));
   function Auth_Held (S : State; K : Slot_Index; J : Held_Index) return Header is
     (S.A.H (K, J).Hdr);
   function Auth_Tag (S : State; K : Slot_Index; J : Held_Index) return U64 is
     (S.A.H (K, J).Tag);

   function Off (S : State; K : Slot_Index) return Natural is (S.A.Offs (K));

   function Auth_Count (S : State) return Held_Count is (S.A.NAuth);

   function Has_Ceil (S : State) return Boolean is (S.A.C.Present);
   function Ceil_Held (S : State) return Header is (S.A.C.Hdr);
   function Ceil_Tag (S : State) return U64 is (S.A.C.Tag);

   function Count (S : State) return Held_Count is
     (Data_Count (S) + Auth_Count (S));

end Kome.Frontier;
