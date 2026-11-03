--  Kome.Frontier: one collection's replica state and its operations
--  (DESIGN.md §3, §4, §7; Frontier.lean `State`, `adm`, `keep`, `applyA`,
--  `expire`).
--
--  The state is the frontier F: the held records, and nothing else that
--  matters. Admission reads two views of F, maxceil(F) (the largest
--  ceiling_t of the held rosters) and W(F) (the subjects of the held
--  GRANTs); the state caches them in a Register_File (Kome.Registers), and
--  the invariant `Is_Frontier` includes that the cache equals the views
--  (`Coherent`, exported as Lemma_Ceil_Bound, Lemma_Ceil_Witness,
--  Lemma_W_Sound and Lemma_W_Complete). The registers are derived, never
--  raised by a record that is not held: a dominated roster or grant changes
--  nothing (DESIGN.md §4, D1′). They lose nothing to domination, because a
--  roster leaves F only under a roster of its signer with a ceiling at
--  least its own and a grant only under a grant of the same issuer and
--  subject (T4', Kome.Headers.Lemma_Dominator_Keeps_Registers).
--
--  Discard model (DESIGN.md §4, §10 item 1): inadmissible records are
--  refused (Status = Inadmissible), not held, so the held set is bounded;
--  the peer that holds them re-offers them, and admission is monotone
--  (T4'), so replicas converge (T4).
--
--  Capacity rows (E1, R5, R6; DESIGN.md §7). Data records share one row of
--  Cap records. Every signer has its own row, a *slice* of Slice
--  authorization records, in one of Signers_Max slots; slot 1 is the
--  founding key's from Empty on, and a slot is assigned to a certified
--  root when its first record is held and never freed (none of a signer's
--  records leaves F except under another of its own). Every dominator is
--  in the row of what it dominates (Kome.Headers.Lemma_Same_Row), so one
--  Apply touches exactly one row and drops only inside it: neither a data
--  flood nor a stolen root can take room from anyone else, and the founding
--  key's REVOKE always lands. A full row refuses with No_Space (data) or
--  Auth_Full (a slice, or the slot table, or W; E2), and nothing changes.
--
--  Order of Apply (D11, DESIGN.md §7): admission, duplicate, domination,
--  room, commit. Nothing changes before the room decision, and on every
--  refusal nothing changes (T13): the Post says `Unchanged (S'Old, S)`.
--
--  Expiry (D10, DESIGN.md §7): `Expire` removes the DELs at or below a
--  horizon from the data row; `Apply_Expired` applies a DEL that is already
--  expired for its effect (drop what it dominates) without holding it.
--  Neither touches the registers or an authorization row.
--
--  Theorems: Apply refines Frontier.lean `applyA` (keep is a filter of
--  held ++ [r]; nothing is lost except by domination); T3 (the held set is
--  its own frontier after every step), T4' (registers only grow), T11 (a)
--  (Expire leaves a frontier with no expired DEL and the same registers),
--  T12 (an authorization record changes only its own row) and T13 (bounds;
--  every refusal leaves the state unchanged).
--
--  gnatprove 14 workaround (documented, keep it): State has no
--  Dynamic_Predicate, because gnatprove 14 crashes when a State with a
--  predicate is assigned, and clients must not assign a State in proved
--  code: they compare states with the ghost `Unchanged` instead of "=".
--  The invariants are therefore carried by `Is_Frontier`, which every
--  operation requires and preserves, and the accessors clamp to the
--  discriminants so they are total on any State.
pragma Ada_2022;
with Kome.Headers;   use Kome.Headers;
with Kome.Registers; use Kome.Registers;
package Kome.Frontier with SPARK_Mode is

   --  Bound on the records one replica holds for one collection (DESIGN.md
   --  §7): Cap data records plus Signers_Max * Slice authorization records.
   --  The capacities are chosen when the state is created (discriminants).
   Held_Max : constant := 2**20;
   subtype Held_Count is Natural range 0 .. Held_Max;
   subtype Held_Index is Natural range 1 .. Held_Max;

   type Header_Array is array (Held_Index range <>) of Header;

   --  (The work order's subtype names Data_Count and Slot_Count are taken by
   --  the functions of the same names; Ada does not overload a subtype with
   --  a function, so the subtypes are Data_Size and Slot_Number.)
   subtype Data_Size   is Natural range 0 .. Held_Max;
   subtype Slice_Count is Natural range 0 .. Slice_Max;
   subtype Slot_Index  is Positive range 1 .. Signers_Max;
   subtype Slot_Number is Natural range 0 .. Signers_Max;

   type State (Cap : Data_Size; Slice : Slice_Count) is private;

   ---------------------------------------------------------------------
   --  Accessors
   ---------------------------------------------------------------------

   function Collection (S : State) return Id128 with Global => null;
   function Founding (S : State) return Key256 with Global => null;
   function Regs (S : State) return Register_File with Global => null;

   --  The data row.
   function Data_Count (S : State) return Data_Size with
     Global => null,
     Post   => Data_Count'Result <= S.Cap;
   function Data_Held (S : State; I : Held_Index) return Header with
     Global => null,
     Pre    => I <= Data_Count (S);

   --  The authorization rows: slot K belongs to signer Slot_Key (S, K).
   function Slots_Used (S : State) return Slot_Number with Global => null;
   function Slot_Key (S : State; K : Slot_Index) return Key256 with
     Global => null,
     Pre    => K <= Slots_Used (S);
   function Slot_Count (S : State; K : Slot_Index) return Slice_Count with
     Global => null,
     Post   => Slot_Count'Result <= S.Slice;
   function Auth_Held (S : State; K : Slot_Index; J : Held_Index) return Header with
     Global => null,
     Pre    => K <= Slots_Used (S) and then J <= Slot_Count (S, K);

   --  The slot of a signer: 0 if no used slot has that key.
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

   --  For a flat index past the data row, the slot it falls in.
   function Slot_At (S : State; I : Held_Index) return Slot_Index with
     Global => null;

   ---------------------------------------------------------------------
   --  The lattice predicates
   ---------------------------------------------------------------------

   --  Admission (DESIGN.md §4; Frontier.lean `adm` plus the W register):
   --  a data record is admitted iff t <= maxceil and author ∈ W;
   --  authorization records always are.
   function Admitted (S : State; R : Header) return Boolean is
     (if Is_Data (R)
      then Data_T (R) <= Ceil (Regs (S)) and then In_W (Regs (S), Data_Author (R))
      else True);

   --  Frontier.lean `Dom` restricted to admitted held records.
   function Dom (S : State; X : Header) return Boolean is
     (for some I in 1 .. Count (S) =>
        Admitted (S, Held (S, I)) and then Dominates (Held (S, I), X));

   function Holds (S : State; X : Header) return Boolean is
     (for some I in 1 .. Count (S) => Held (S, I) = X);

   --  R would drop some held record (opaque; Lemma_Drops_Any).
   function Drops_Any (S : State; R : Header) return Boolean with Global => null;

   --  The invariant every State satisfies (opaque). The held set is its own
   --  frontier (nothing held is dominated by anything held), nothing is held
   --  twice, everything held is canonical, of this collection and admitted;
   --  the data row holds data and slot K holds authorization records issued
   --  by Slot_Key (S, K); slot 1 is the founding key's, slot keys are
   --  distinct and every used slot past 1 is non-empty; the rows are within
   --  their capacities; and the registers equal the views (Coherent).
   function Is_Frontier (S : State) return Boolean with Global => null;

   --  Nothing observable changed (opaque, ghost; Lemma_Unchanged). Clients
   --  use this instead of "=" on State (see the header comment).
   function Unchanged (Old, Upd : State) return Boolean with Ghost, Global => null;

   ---------------------------------------------------------------------
   --  Operations
   ---------------------------------------------------------------------

   function Empty
     (NS       : Id128;
      Founding : Key256;
      Cap      : Data_Size;
      Slice    : Slice_Count) return State
   with
     Global => null,
     Pre    => Slice >= 1 and then Cap + Signers_Max * Slice <= Held_Max,
     Post   => Empty'Result.Cap = Cap
               and then Empty'Result.Slice = Slice
               and then Collection (Empty'Result) = NS
               and then Kome.Frontier.Founding (Empty'Result) = Founding
               and then Count (Empty'Result) = 0
               and then Data_Count (Empty'Result) = 0
               and then Slots_Used (Empty'Result) = 1
               and then Slot_Key (Empty'Result, 1) = Founding
               and then Slot_Count (Empty'Result, 1) = 0
               and then Ceil (Regs (Empty'Result)) = 0
               and then Kome.Registers.Count (Regs (Empty'Result)) = 0
               and then Is_Frontier (Empty'Result);

   --  Apply one record (DESIGN.md §7 steps 1-6). OK means R is held (newly,
   --  or already: a duplicate is a no-op and still OK, so applying a set
   --  with repetitions is applying the set); Dominated means a held record
   --  beats R; Inadmissible, No_Space and Auth_Full are refusals. Every
   --  outcome other than a new hold leaves the state Unchanged.
   --
   --  Auth_Full (c), W full, is unreachable on a frontier whose slices are
   --  within Slice_Max: |W| is at most the number of held GRANTs, at most
   --  Signers_Max * Slice_Max = Writers_Max (DESIGN.md §7). It is kept as a
   --  refusal so that Add_Writer's bound is checked, not assumed; the
   --  counting argument is not proved here.
   procedure Apply (S : in out State; R : Header; Result : out Status) with
     Global => null,
     Pre    => Is_Frontier (S) and then Canonical (R)
               and then R.NS = Collection (S),
     Post   => Is_Frontier (S)
       and then Collection (S) = Collection (S'Old)
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
                     --  (a) the signer's slice is full and R frees nothing
                     ((Slot_Of (S'Old, R.Issuer) /= 0
                       and then Slot_Count (S'Old, Slot_Of (S'Old, R.Issuer)) = S.Slice
                       and then not Drops_Any (S'Old, R))
                      --  (b) a new signer, and every slot is taken
                      or else (Slot_Of (S'Old, R.Issuer) = 0
                               and then Slots_Used (S'Old) = Signers_Max)
                      --  (c) W is full (unreachable, see above)
                      or else (R.K = K_Grant
                               and then not In_W (Regs (S'Old), R.V.Author)
                               and then Kome.Registers.Count (Regs (S'Old)) = Writers_Max)))
       and then (if Result /= OK or else Holds (S'Old, R) then Unchanged (S'Old, S))
       and then (if Result = OK then
                   Holds (S, R)
                   and then Ceil (Regs (S)) = U48'Max (Ceil (Regs (S'Old)), Ceil_Of (R))
                   and then Extends (Regs (S'Old), Regs (S))
                   and then (if R.K = K_Grant
                             then Added (Regs (S'Old), Regs (S), R.V.Author)
                             else Extends (Regs (S), Regs (S'Old)))
                   --  Frontier.lean `keep`: a filter of held ++ [r].
                   and then (for all I in 1 .. Count (S) =>
                               Holds (S'Old, Held (S, I)) or else Held (S, I) = R)
                   --  Nothing is lost except by domination.
                   and then (for all I in 1 .. Count (S'Old) =>
                               Holds (S, Held (S'Old, I))
                               or else Dominates (R, Held (S'Old, I))));

   --  Tombstone expiry at Horizon (D10, DESIGN.md §7, T11 (a)): remove from
   --  the data row exactly the DELs with t <= Horizon. Only the data row
   --  changes.
   procedure Expire (S : in out State; Horizon : Time64) with
     Global => null,
     Pre    => Is_Frontier (S),
     Post   => Is_Frontier (S)
       and then Collection (S) = Collection (S'Old)
       and then Founding (S) = Founding (S'Old)
       and then Regs (S) = Regs (S'Old)
       and then Ceil (Regs (S)) = Ceil (Regs (S'Old))
       and then Extends (Regs (S), Regs (S'Old))
       and then Extends (Regs (S'Old), Regs (S))
       and then Data_Count (S) <= Data_Count (S'Old)
       --  Every authorization slot is unchanged.
       and then Slots_Used (S) = Slots_Used (S'Old)
       and then Auth_Count (S) = Auth_Count (S'Old)
       and then (for all K in Slot_Index =>
                   Slot_Count (S, K) = Slot_Count (S'Old, K)
                   and then Off (S, K) = Off (S'Old, K))
       and then (for all K in 1 .. Slots_Used (S) =>
                   Slot_Key (S, K) = Slot_Key (S'Old, K)
                   and then (for all J in 1 .. Slot_Count (S, K) =>
                               Auth_Held (S, K, J) = Auth_Held (S'Old, K, J)))
       --  The data row is the old one without the expired DELs.
       and then (for all I in 1 .. Data_Count (S) =>
                   Holds (S'Old, Data_Held (S, I))
                   and then not Expired (Data_Held (S, I), Horizon))
       and then (for all I in 1 .. Data_Count (S'Old) =>
                   Expired (Data_Held (S'Old, I), Horizon)
                   or else Holds (S, Data_Held (S'Old, I)));

   --  A DEL already expired on arrival (DESIGN.md §7 step 4): applied for
   --  its effect and not held. Never No_Space or Auth_Full: it needs no room.
   procedure Apply_Expired (S : in out State; R : Header; Result : out Status) with
     Global => null,
     Pre    => Is_Frontier (S) and then Canonical (R) and then R.K = K_Del
               and then R.NS = Collection (S),
     Post   => Is_Frontier (S)
       and then Collection (S) = Collection (S'Old)
       and then Founding (S) = Founding (S'Old)
       and then Result in OK | Dominated | Inadmissible
       and then (Result = Inadmissible) = not Admitted (S'Old, R)
       and then (Result = Dominated) = (Admitted (S'Old, R) and then Dom (S'Old, R))
       and then (if Result /= OK or else Holds (S'Old, R) then Unchanged (S'Old, S))
       and then (if Result = OK and then not Holds (S'Old, R) then
                   not Holds (S, R)
                   and then Regs (S) = Regs (S'Old)
                   and then Ceil (Regs (S)) = Ceil (Regs (S'Old))
                   and then Extends (Regs (S), Regs (S'Old))
                   and then Extends (Regs (S'Old), Regs (S))
                   and then Slots_Used (S) = Slots_Used (S'Old)
                   and then Auth_Count (S) = Auth_Count (S'Old)
                   and then (for all K in Slot_Index =>
                               Slot_Count (S, K) = Slot_Count (S'Old, K)
                               and then Off (S, K) = Off (S'Old, K))
                   and then (for all K in 1 .. Slots_Used (S) =>
                               Slot_Key (S, K) = Slot_Key (S'Old, K)
                               and then (for all J in 1 .. Slot_Count (S, K) =>
                                           Auth_Held (S, K, J) = Auth_Held (S'Old, K, J)))
                   and then (for all I in 1 .. Count (S) =>
                               Holds (S'Old, Held (S, I))
                               and then not Dominates (R, Held (S, I)))
                   and then (for all I in 1 .. Count (S'Old) =>
                               Dominates (R, Held (S'Old, I))
                               or else Holds (S, Held (S'Old, I))));

   ---------------------------------------------------------------------
   --  Lemmas
   ---------------------------------------------------------------------

   --  The flat view, data part.
   procedure Lemma_Held_Data (S : State; I : Held_Index) with
     Ghost, Global => null,
     Pre  => I <= Data_Count (S),
     Post => I <= Count (S) and then Held (S, I) = Data_Held (S, I);

   --  The flat view, slot K.
   procedure Lemma_Held_Auth (S : State; K : Slot_Index; J : Held_Index) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S) and then K <= Slots_Used (S)
             and then J <= Slot_Count (S, K),
     Post => Data_Count (S) + Off (S, K) + J <= Count (S)
             and then Slot_At (S, Data_Count (S) + Off (S, K) + J) = K
             and then Held (S, Data_Count (S) + Off (S, K) + J) = Auth_Held (S, K, J);

   --  Every flat index is one of the two.
   procedure Lemma_Held_Cases (S : State; I : Held_Index) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S) and then I <= Count (S),
     Post => (if I <= Data_Count (S) then Held (S, I) = Data_Held (S, I)
              else Slot_At (S, I) <= Slots_Used (S)
                   and then I - Data_Count (S) - Off (S, Slot_At (S, I)) >= 1
                   and then I - Data_Count (S) - Off (S, Slot_At (S, I))
                            <= Slot_Count (S, Slot_At (S, I))
                   and then Held (S, I)
                            = Auth_Held (S, Slot_At (S, I),
                                         I - Data_Count (S) - Off (S, Slot_At (S, I))));

   --  The shape of a frontier's rows and slots.
   procedure Lemma_Frontier_Shape (S : State) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S),
     Post => S.Slice >= 1
             and then S.Cap + Signers_Max * S.Slice <= Held_Max
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
             and then Count (S) <= S.Cap + Signers_Max * S.Slice;

   --  Every data record held is data, canonical, of this collection and
   --  admitted.
   procedure Lemma_Frontier_Data (S : State; I : Held_Index) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S) and then I <= Data_Count (S),
     Post => Is_Data (Data_Held (S, I)) and then Canonical (Data_Held (S, I))
             and then Data_Held (S, I).NS = Collection (S)
             and then Admitted (S, Data_Held (S, I));

   --  Every record of slot K is an authorization record issued by its key.
   procedure Lemma_Frontier_Auth (S : State; K : Slot_Index; J : Held_Index) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S) and then K <= Slots_Used (S)
             and then J <= Slot_Count (S, K),
     Post => Is_Auth (Auth_Held (S, K, J)) and then Canonical (Auth_Held (S, K, J))
             and then Auth_Held (S, K, J).NS = Collection (S)
             and then Auth_Held (S, K, J).Issuer = Slot_Key (S, K);

   --  In the flat view: everything held is canonical, of this collection,
   --  admitted, not dominated by anything held, and held once.
   procedure Lemma_Frontier_Held (S : State; I : Held_Index) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S) and then I <= Count (S),
     Post => Canonical (Held (S, I))
             and then Held (S, I).NS = Collection (S)
             and then Admitted (S, Held (S, I))
             and then not Dom (S, Held (S, I))
             and then (for all J in 1 .. Count (S) =>
                         not Dominates (Held (S, J), Held (S, I)))
             and then (for all J in 1 .. Count (S) =>
                         (if J /= I then Held (S, J) /= Held (S, I)));

   --  The register cache equals the views (Coherent).
   --  maxceil(F) bounds every held roster's ceiling ...
   procedure Lemma_Ceil_Bound (S : State; I : Held_Index) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S) and then I <= Count (S),
     Post => Ceil_Of (Held (S, I)) <= Ceil (Regs (S));

   --  ... and is the ceiling of some held roster, or 0.
   procedure Lemma_Ceil_Witness (S : State) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S) and then Ceil (Regs (S)) > 0,
     Post => (for some I in 1 .. Count (S) =>
                Held (S, I).K = K_Roster and then Held (S, I).V.T = Ceil (Regs (S)));

   --  Every writer is the subject of a held GRANT ...
   procedure Lemma_W_Sound (S : State; A : Key256) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S) and then In_W (Regs (S), A),
     Post => (for some I in 1 .. Count (S) =>
                Held (S, I).K = K_Grant and then Held (S, I).V.Author = A);

   --  ... and the subject of every held GRANT is a writer.
   procedure Lemma_W_Complete (S : State; I : Held_Index) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S) and then I <= Count (S)
             and then Held (S, I).K = K_Grant,
     Post => In_W (Regs (S), Held (S, I).V.Author);

   procedure Lemma_Drops_Any (S : State; R : Header) with
     Ghost, Global => null,
     Post => Drops_Any (S, R)
             = (for some I in 1 .. Count (S) => Dominates (R, Held (S, I)));

   --  Unchanged is reflexive: a state that was not touched is Unchanged.
   --  A refusal that never calls an operation on S (Kome.Store) states
   --  its "nothing changed" Post with this lemma.
   procedure Lemma_Unchanged_Refl (S : State) with
     Ghost, Global => null,
     Post => Unchanged (S, S);

   --  What Unchanged means through the public view. Executable: every
   --  quantifier is bounded by the state's own counts, so -gnata runs it.
   procedure Lemma_Unchanged (Old, Upd : State) with
     Ghost, Global => null,
     Pre  => Unchanged (Old, Upd),
     Post => Old.Cap = Upd.Cap and then Old.Slice = Upd.Slice
             and then Collection (Upd) = Collection (Old)
             and then Founding (Upd) = Founding (Old)
             and then Regs (Upd) = Regs (Old)
             and then Ceil (Regs (Upd)) = Ceil (Regs (Old))
             and then Kome.Registers.Count (Regs (Upd)) = Kome.Registers.Count (Regs (Old))
             and then Extends (Regs (Upd), Regs (Old))
             and then Extends (Regs (Old), Regs (Upd))
             and then Data_Count (Upd) = Data_Count (Old)
             and then (for all I in 1 .. Data_Count (Old) =>
                         Data_Held (Upd, I) = Data_Held (Old, I))
             and then Slots_Used (Upd) = Slots_Used (Old)
             and then (for all K in Slot_Index =>
                         Slot_Count (Upd, K) = Slot_Count (Old, K)
                         and then Off (Upd, K) = Off (Old, K))
             and then (for all K in 1 .. Slots_Used (Old) =>
                         Slot_Key (Upd, K) = Slot_Key (Old, K)
                         and then (for all J in 1 .. Slot_Count (Old, K) =>
                                     Auth_Held (Upd, K, J) = Auth_Held (Old, K, J)))
             and then Auth_Count (Upd) = Auth_Count (Old)
             and then Count (Upd) = Count (Old)
             and then (for all I in 1 .. Count (Old) => Held (Upd, I) = Held (Old, I));

private

   subtype Slice_Pos is Positive range 1 .. Slice_Max;
   type Auth_Matrix is array (Slot_Index range <>, Slice_Pos range <>) of Header;
   type Slot_Counts is array (Slot_Index) of Slice_Count;
   type Slot_Keys   is array (Slot_Index) of Key256;
   subtype Off_Value is Natural range 0 .. Signers_Max * Slice_Max;
   type Slot_Offs   is array (Slot_Index) of Off_Value;

   --  The authorization rows: one row of Slice records per signer slot,
   --  how many each holds (NA), the signer of each slot (Keys), how many
   --  slots are used, the offsets of the flat view and the total. A record
   --  of their own, so that an operation on the data row leaves this
   --  component equal as a whole (the prover then needs no frame lemma).
   type Auth_Rows (Slice : Slice_Count) is record
      H      : Auth_Matrix (Slot_Index, 1 .. Slice);
      NA     : Slot_Counts := [others => 0];
      Keys   : Slot_Keys   := [others => (others => 0)];
      NSlots : Slot_Number := 0;
      Offs   : Slot_Offs   := [others => 0];
      NAuth  : Off_Value   := 0;
   end record;

   --  Records in slot K, clamped to the slice so it is total.
   function SC (A : Auth_Rows; K : Slot_Index) return Slice_Count is
     (if A.NA (K) <= A.Slice then A.NA (K) else A.Slice);

   --  Every discriminant appears alone in a component constraint
   --  (RM 3.8(12)), which is why the authorization records are a matrix of
   --  Signers_Max rows of Slice, not part of one array with the data.
   type State (Cap : Data_Size; Slice : Slice_Count) is record
      NS     : Id128;
      Fnd    : Key256;
      RG     : Register_File;
      Data_H : Header_Array (1 .. Cap);
      ND     : Data_Size := 0;
      A      : Auth_Rows (Slice);
   end record;

   function Collection (S : State) return Id128 is (S.NS);
   function Founding (S : State) return Key256 is (S.Fnd);
   function Regs (S : State) return Register_File is (S.RG);

   function Data_Count (S : State) return Data_Size is
     (if S.ND <= S.Cap then S.ND else S.Cap);
   function Data_Held (S : State; I : Held_Index) return Header is (S.Data_H (I));

   function Slots_Used (S : State) return Slot_Number is (S.A.NSlots);
   function Slot_Key (S : State; K : Slot_Index) return Key256 is (S.A.Keys (K));
   function Slot_Count (S : State; K : Slot_Index) return Slice_Count is (SC (S.A, K));
   function Auth_Held (S : State; K : Slot_Index; J : Held_Index) return Header is
     (S.A.H (K, J));

   function Off (S : State; K : Slot_Index) return Natural is (S.A.Offs (K));

   function Auth_Count (S : State) return Held_Count is
     (if S.A.NAuth <= Held_Max - Data_Count (S) then S.A.NAuth
      else Held_Max - Data_Count (S));

   function Count (S : State) return Held_Count is
     (Data_Count (S) + Auth_Count (S));

end Kome.Frontier;
