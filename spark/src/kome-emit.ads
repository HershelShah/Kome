--  Kome.Emit: the write path (DESIGN.md §5, "Clocks and writing", D8; T8
--  chase, T9 bounded pin, T13 bounds, H8 backup-restore self-detection;
--  Frontier.lean `emitT`, `chase`, `emitT_le`, `lt_iff_prefix`).
--
--    floor(cell)  := max(cell(ns,ent,f).v, deleted_at(ns,ent))
--                    -- for DEL: max over all fields and deleted_at
--    floor.t      := max(floor.t, mark)
--                    -- mark: the store's expire mark, the largest
--                    -- horizon the store applied, at or above the t of
--                    -- every DEL that it expired (AUDIT.md H28). An
--                    -- absent floor has t = 0, so the floor term always
--                    -- exists, and a write is above the mark whenever the
--                    -- mark is below the writer's ceiling.
--    t_emit       := max(now_ms, floor.t + 1);
--                    if t_emit > maxceil then t_emit := maxceil
--    clamped      := t_emit < max(now_ms, floor.t + 1)
--                    -- the write was back-dated to the ceiling (H22)
--    born_expired := DEL and t_emit + del_ttl_eff <= now_ms
--                    -- the DEL expires on arrival at a replica with this
--                    -- clock (H22); the caller syncs before it writes it
--    seq_emit     := seq_self(ns) + 1, and above every seq of this device's
--                    records held in F(ns); at 2^48 - 1 the write fails
--                    SEQ_EXHAUSTED
--    v_emit       := (t_emit, self_pk, seq_emit, h)
--    status       := SHADOWED if floor exists and v_emit < floor
--                    (only when t_emit = maxceil) else OK
--
--  The write path has three steps (D8, DESIGN.md §5). h hashes content that
--  contains t and seq, so h cannot be an input to the step that chooses
--  them:
--
--    1. Choose (this package): (t_emit, seq_emit, status, clone_suspected,
--       clamped, born_expired) from the frontier, the target, now_ms, the
--       store's expire mark, del_ttl_eff, the device key and seq_self(ns).
--       No h.
--    2. Build the PUT or DEL content with that (t, seq) and hash it:
--       Kome.Records.Make_Put or Make_Del (h is the record's hash).
--    3. Sign and apply (Kome.Write: Prepare, then the binding persists
--       seq_self(ns), then Commit through Kome.Store.Put_Frame; A5,
--       AUDIT.md A10).
--
--  The target of step 1 is built with Put_Target or Del_Target from the
--  inputs of step 2 (AUDIT.md G21): the field hash is
--  To_Key256 (Blake2b_256 (field)), as Kome.Records.To_Header computes it.
--  Lemma_Put_Target_Matches and Lemma_Del_Target_Matches state that the
--  header of the built record is To_Header (target, Stamp (t, self, seq, h)),
--  so the cell that Choose looks at is the cell that the record occupies.
--
--  Two flags come next to Clone_Suspected (AUDIT.md H22):
--    * Clamped: t_emit is below max (now_ms, floor.t + 1). The ceiling held
--      the write back. Under a stale maxceil the caller syncs first.
--    * Born_Expired: the write is a DEL and t_emit + del_ttl_eff <= now_ms.
--      A replica with this clock expires it on arrival and does not hold
--      it, so the caller syncs before it writes such a DEL.
--  Both are flags, not statuses: the write occurred.
--
--  H18: Clone_Detected sees a clone that is ahead of seq_self. A clone that
--  writes at the owner's pace leaves pairs in F: two own records with equal
--  seq and different h (Clone_Pair). The caller shows CLONE_SUSPECTED for
--  either. The apply-side flag (an admitted own-key record that was not
--  held before) belongs to the write path, Kome.Write.
--
--  The outcome of step 1 does not depend on h
--  (Lemma_Outcome_Independent_Of_H, from
--  Kome.Versions.Lemma_Prefix_Decides):
--    * seq_emit is more than each seq of this device's held records, so
--      the prefix (t_emit, self, seq_emit) is different from the prefix of
--      each held data version.
--    * Two versions with different prefixes compare by the prefix only.
--  Choose gives its order facts with Kome.Versions.Prefix_Lt on the
--  prefix Stamp (T, Self, Seq, Zero_Key). For each h, the record of step 2,
--  To_Header (Tgt, Stamp (T, Self, Seq, h)), has these properties:
--    * it is admitted;
--    * it compares with each floor record exactly as the prefix does;
--    * if Choose gave OK, no held record dominates it
--      (Lemma_OK_Undominated).
--  As a result, Apply holds an OK write, unless the store is full (No_Space,
--  DESIGN.md §7).
--
--  seq_self is per collection (D8, DESIGN.md §5). Seq_Self is the counter
--  of (device key, Collection (S)). The caller keeps it next to that
--  collection's store and persists it before the APPLY (A5;
--  Kome.Write.Prepare returns it as Seq_Persist, and
--  Kome.Write.Seq_Self_At_Open gives it on open). A thief can force a jump to
--  2^48 - 1 in one collection. This exhausts only that collection's
--  counter for that key.
--
--  H8 (backup restore / clone): before the write, Choose scans the held
--  records for the device's data records. Possibly one of them has
--  seq >= seq_self + 1 (seq_self came from a backup, or the key is cloned).
--  If so, seq jumps past it and Clone_Suspected is True. The emitted
--  (author, seq) is strictly above each own record that this replica holds
--  (T8, "v_emit.seq is larger than each seq that this device emitted", as
--  far as the replica can see).
--  CLONE_SUSPECTED is a flag reported next to the write's status. It is
--  not a status: the write occurred (DESIGN.md §5, and §10.6, the out
--  flag of the C ABI). For this reason, Clone_Suspected is an out Boolean
--  next to Result.
--  SEQ_EXHAUSTED is a clone alarm (DESIGN.md §5). The device moves to a
--  fresh key in that collection (a new GRANT and roster), and the old key
--  is revoked.
--
--  Admission: if a write's key is not in W, Choose refuses the write with
--  Inadmissible and changes nothing, so OK and Shadowed mean that the
--  emitted record is admitted (DESIGN.md §4). Tgt.NS must be the state's
--  collection (Pre).
--
--  t_emit is exactly the formula of DESIGN.md §5 (Lemma_T_Emit_Formula).
--  There is no refusal at floor.t + 1 = 2^48. If floor.t >= maxceil, the
--  result is maxceil and floor.t + 1 is never formed, so
--  floor.t = 2^48 - 1 is an ordinary write at the ceiling (Shadowed, unless
--  it wins the tie on author/seq). There is no wrap (T13). If a seq would
--  go past 2^48 - 1 (seq_self at the bound, or a held own record at the
--  bound), Choose refuses with Seq_Exhausted and changes nothing.
--
--  There is no engine clock, and nothing comes from a peer. The only inputs
--  are:
--    * the replica state;
--    * the local clock Now (0 on a device with no real-time clock: then
--      each write chases);
--    * the device key;
--    * the persisted seq_self(ns).
--
--  Floor scans each held record through the public view of Kome.Frontier
--  (Count, Held). It keeps the largest version of the records that are
--  In_Floor. Only data records satisfy In_Floor, so only their versions
--  count, and the result is a function of F (T5). Floor needs no
--  Is_Frontier hypothesis: on each held array it is the maximum of the
--  In_Floor versions. On a frontier, its source record is admitted, so the
--  floor is never above the ceiling (Lemma_Floor_Admitted).
--
--  The loops that only carry proofs are in ghost lemmas, so they do not
--  run outside -gnata.
--
--  This package declares no public constants (for example no No_Version
--  or Zero_Key; the all-zero version is the function Zero_Version), so a
--  client can `use` it together with Kome.Views.
pragma Ada_2022;
with Kome.Versions; use Kome.Versions;
with Kome.Headers;  use Kome.Headers;
with Kome.Keys;     use Kome.Keys;
with Kome.Crypto;
with Kome.Records;
with Kome.Registers; use Kome.Registers;
with Kome.Frontier;  use Kome.Frontier;
package Kome.Emit with SPARK_Mode is

   --  The all-zero version: an absent floor has this version. It is a
   --  function, not a constant named No_Version (see the header).
   function Zero_Version return Version is
     ((T => 0, Author => (others => 0), Seq => 0, H => (others => 0)));

   --  The version of a write: (t, author, seq, h). Choose chooses T and
   --  Seq. H is the content hash of the record built from them (step 2).
   function Stamp (T : U48; Self : Key256; Seq : U48; H : Key256)
     return Version
   is
     ((T => T, Author => Self, Seq => Seq, H => H));

   --  The write: a PUT on the cell (ns, ent, fh) or a DEL of the entity
   --  (ns, ent). A DEL ignores FH (the emitted header has zero there, the
   --  canonical form of Kome.Headers).
   type Write_Op is (W_Put, W_Del);

   type Target is record
      Op  : Write_Op := W_Put;
      NS  : Id128;
      Ent : Id128;
      FH  : Key256;
   end record;

   --  G21: the target of a PUT on field Field of (NS, Ent). FH is the
   --  field hash that Kome.Records.To_Header computes for a PUT record
   --  with this field, To_Key256 (BLAKE2b-256 (field)). A caller builds
   --  its target here, from the inputs it gives to Make_Put, so the cell
   --  that Choose looks at is the cell that the record occupies
   --  (Lemma_Put_Target_Matches).
   function Put_Target (NS, Ent : Id128; Field : Byte_Array) return Target is
     (Op => W_Put, NS => NS, Ent => Ent,
      FH => To_Key256 (Kome.Crypto.Blake2b_256 (Field)))
   with Pre => Field'Length in 1 .. Field_Max;

   --  G21: the target of a DEL of (NS, Ent). A DEL has no field: FH is zero,
   --  the value that Kome.Records.To_Header gives a DEL record
   --  (Lemma_Del_Target_Matches).
   function Del_Target (NS, Ent : Id128) return Target is
     (Op => W_Del, NS => NS, Ent => Ent, FH => (others => 0));

   --  X is one of the records whose versions make the floor of Tgt
   --  (DESIGN.md §5):
   --    * for a PUT, a PUT on the same cell or a DEL of the entity;
   --    * for a DEL, a PUT or DEL of the entity.
   --  Only data records are possible. It has no quantifier, so it is
   --  public. It includes each record that can dominate the emitted record
   --  (Kome.Headers.Dominates). This gives T8 read-your-writes.
   function In_Floor (X : Header; Tgt : Target) return Boolean is
     (X.NS = Tgt.NS and then X.Ent = Tgt.Ent
      and then (X.K = K_Del
                or else (X.K = K_Put
                         and then (Tgt.Op = W_Del or else X.FH = Tgt.FH))));

   --  The header of the record that a write emits with version V. It is
   --  canonical (Kome.Headers.Canonical): the fields that a data record
   --  does not use are zero.
   function To_Header (Tgt : Target; V : Version) return Header is
     (K       => (if Tgt.Op = W_Put then K_Put else K_Del),
      NS      => Tgt.NS,
      Ent     => Tgt.Ent,
      FH      => (if Tgt.Op = W_Put then Tgt.FH else Key256'(others => 0)),
      V       => V,
      Issuer  => (others => 0),
      Del_TTL => 0, Epoch => 0);

   --  Option-like floor. Absent: V is Zero_Version.
   type Floor_View is record
      Present : Boolean := False;
      V       : Version;
   end record;

   --  floor(cell): the maximum version among the held records In_Floor.
   function Floor (S : State; Tgt : Target) return Floor_View with
     Global => null,
     Pre  => True,   --  total: defined on any state
     Post =>
       Floor'Result.Present =
         (for some I in 1 .. Count (S) => In_Floor (Held (S, I), Tgt))
       and then
       (if Floor'Result.Present then
          (for some I in 1 .. Count (S) =>
             In_Floor (Held (S, I), Tgt) and then Held (S, I).V = Floor'Result.V)
          and then
          (for all I in 1 .. Count (S) =>
             (if In_Floor (Held (S, I), Tgt)
              then Held (S, I).V = Floor'Result.V
                   or else Lt (Held (S, I).V, Floor'Result.V)))
        else Floor'Result.V = Zero_Version);

   --  X is a data record that this device (key Self) signed. Only PUT and
   --  DEL have the device's seq in V.Seq (a ROSTER has gen, a REVOKE and
   --  a GRANT have 0), so only they count for H8. It has no
   --  quantifier, so it is public.
   function Own (X : Header; Self : Key256) return Boolean is
     (Is_Data (X) and then X.V.Author = Self);

   --  Option-like maximum own seq. Absent: Seq is 0.
   type Own_Seq_View is record
      Present : Boolean := False;
      Seq     : U48     := 0;
   end record;

   --  The largest seq among the held records Own by Self (H8 detection).
   function Max_Own_Seq (S : State; Self : Key256) return Own_Seq_View with
     Global => null,
     Pre  => True,
     Post =>
       Max_Own_Seq'Result.Present =
         (for some I in 1 .. Count (S) => Own (Held (S, I), Self))
       and then
       (if Max_Own_Seq'Result.Present then
          (for some I in 1 .. Count (S) =>
             Own (Held (S, I), Self)
             and then Held (S, I).V.Seq = Max_Own_Seq'Result.Seq)
          and then
          (for all I in 1 .. Count (S) =>
             (if Own (Held (S, I), Self)
              then Held (S, I).V.Seq <= Max_Own_Seq'Result.Seq))
        else Max_Own_Seq'Result.Seq = 0);

   --  H8: the seq that the next write increments. This is seq_self, but a
   --  held own record can have seq >= seq_self + 1 (written without the
   --  + 1). Then seq jumps to that record's seq. No quantifier.
   function Seq_Base (Seq_Self : U48; O : Own_Seq_View) return U48 is
     (if O.Present and then O.Seq > Seq_Self then O.Seq else Seq_Self);

   --  H8: the clone / backup-restore condition of DESIGN.md §5.
   function Clone_Detected (Seq_Self : U48; O : Own_Seq_View) return Boolean is
     (O.Present and then O.Seq > Seq_Self);

   --  H18: X and Y are two records of this device with equal seq and
   --  different h. An honest device never emits one seq twice, so a pair
   --  means a clone (or a restored backup) that wrote at the owner's pace.
   --  No quantifier, so it is public.
   function Pair (X, Y : Header; Self : Key256) return Boolean is
     (Own (X, Self) and then Own (Y, Self)
      and then X.V.Seq = Y.V.Seq and then X.V.H /= Y.V.H);

   --  H18: F holds a Pair (AUDIT.md H18, the pace-matching clone). It is a
   --  function of F, in the style of Kome.Views: the quantified definition
   --  is in Lemma_Clone_Pair_Def. The caller shows CLONE_SUSPECTED when
   --  Clone_Suspected or Clone_Pair holds.
   function Clone_Pair (S : State; Self : Key256) return Boolean with
     Global => null;

   procedure Lemma_Clone_Pair_Def (S : State; Self : Key256) with
     Ghost, Global => null,
     Post => Clone_Pair (S, Self) =
               (for some I in 1 .. Count (S) =>
                  (for some J in 1 .. Count (S) =>
                     Pair (Held (S, I), Held (S, J), Self)));

   --  t_emit (DESIGN.md §5). It does not form floor.t + 1 if that value
   --  can wrap. It has no quantifier, so it is public.
   function T_Emit (Now : U48; Has_Floor : Boolean; Floor_T, Ceil : U48)
     return U48
   is
     (if Has_Floor and then Floor_T >= Ceil then Ceil
      elsif Has_Floor then U48'Min (U48'Max (Now, Floor_T + 1), Ceil)
      else U48'Min (Now, Ceil));

   --  The ceiling of one writer (DESIGN.md §4, AUDIT.md A1): maxceil, and
   --  its own write cap wcap. A write never goes above either.
   function Eff_Ceil (S : State; Self : Key256) return U48 is
     (U48'Min (Ceil (Regs (S)), W_Cap (Regs (S), Self)));

   --  The lower bound of a DEL (DESIGN.md §5, §7; AUDIT.md A5):
   --  maxceil - Cap_Lead, so that a DEL from a slow or clockless writer
   --  does not expire on arrival at a replica whose clock is at most
   --  Cap_Lead behind maxceil, and lives at least del_ttl_eff - Cap_Lead
   --  everywhere. A PUT has no lower bound (0).
   function Del_Low (Ceil : U48) return U48 is
     (if Ceil >= Cap_Lead then Ceil - Cap_Lead else 0);

   --  The clock that t_emit reads: Now, raised to Del_Low for a DEL.
   function Now_Eff (Tgt : Target; Now, Ceil : U48) return U48 is
     (if Tgt.Op = W_Del then U48'Max (Now, Del_Low (Ceil)) else Now);

   --  H28: the floor time of a write, with the store's expire mark as a
   --  floor term: max (floor.t, mark). An absent floor has Zero_Version,
   --  so its t is 0 and the term is the mark alone. The floor term always
   --  exists (T_Emit is called with Has_Floor = True).
   function Floor_Time (S : State; Tgt : Target; Mark : U48) return U48 is
     (U48'Max (Floor (S, Tgt).V.T, Mark));

   --  H22: T is below u = max (Now, Floor_T + 1). This is the same as
   --  T < Now or T <= Floor_T, which does not form Floor_T + 1 (2^48 is
   --  possible). Lemma_Clamped_Formula states the equality.
   function Is_Clamped (T, Now, Floor_T : U48) return Boolean is
     (T < Now or else T <= Floor_T);

   --  H22: the write is a DEL and T + Del_TTL <= Now, so a replica with
   --  this clock expires it on arrival. Stated without forming T + Del_TTL.
   --  Lemma_Born_Expired_Formula states the equality.
   function Is_Born_Expired (Tgt : Target; T, Del_TTL, Now : U48)
     return Boolean
   is
     (Tgt.Op = W_Del and then Now >= Del_TTL and then T <= Now - Del_TTL);

   --  Step 1 of the write path: choose (t, seq) for one write on Tgt.
   --    Inadmissible   Self is not in W. Nothing is chosen. Seq_Self does
   --                   not change.
   --    Seq_Exhausted  the seq would go past 2^48 - 1. Nothing is chosen.
   --                   Seq_Self does not change (T13). A clone alarm (§5).
   --    OK / Shadowed  build the record with (T, Seq), hash it, sign it and
   --                   apply it. Seq_Self = Seq is larger (by one, or past
   --                   a held own record, H8). The caller persists it as
   --                   seq_self(Collection (S)) (A5).
   --  Clone_Suspected gives the H8 condition in all cases: a held data
   --  record by Self has seq > Seq_Self (the caller shows the
   --  CLONE_SUSPECTED flag next to the status, DESIGN.md §5, §10.6).
   --  Mark is the store's expire mark (Kome.Store.Expire_Mark, H28): the
   --  largest horizon the store applied, at or above the t of every DEL
   --  that this store expired, 0 if none. Del_TTL is
   --  del_ttl_eff of the state (Kome.Views.Del_TTL_Eff), which only
   --  Born_Expired reads. Clamped and Born_Expired are False on a refusal.
   --  The Post gives each order fact on the prefix
   --  Stamp (T, Self, Seq, Zero_Key) with Prefix_Lt.
   --  Lemma_Outcome_Independent_Of_H carries them to the version with the
   --  real h.
   procedure Choose
     (S               : in     State;
      Tgt             : in     Target;
      Now             : in     U48;
      Mark            : in     U48;
      Del_TTL         : in     U48;
      Self            : in     Key256;
      Seq_Self        : in out U48;
      T               :    out U48;
      Seq             :    out U48;
      Result          :    out Status;
      Clone_Suspected :    out Boolean;
      Clamped         :    out Boolean;
      Born_Expired    :    out Boolean)
   with
     Global => null,
     Pre  => Is_Frontier (S) and then Tgt.NS = Collection (S)
             and then Del_TTL in Del_TTL_Min .. Del_TTL_Max,
     Post =>
       Result in OK | Shadowed | Seq_Exhausted | Inadmissible
       --  H8: the restore/clone condition, always given.
       and then Clone_Suspected =
                  Clone_Detected (Seq_Self'Old, Max_Own_Seq (S, Self))
       --  T13: seq_self at the bound never emits.
       and then (if Seq_Self'Old = U48'Last
                 then Result in Seq_Exhausted | Inadmissible)
       --  DESIGN.md §4: a non-writer's record would be refused.
       and then (Result = Inadmissible) = (not In_W (Regs (S), Self))
       --  T13: a seq past 2^48 - 1 (after the H8 jump) is refused.
       and then (Result = Seq_Exhausted) =
                  (In_W (Regs (S), Self)
                   and Seq_Base (Seq_Self'Old, Max_Own_Seq (S, Self)) = U48'Last)
       --  A refusal has no side effect, and no flag but the clone flag.
       and then (if Result in Inadmissible | Seq_Exhausted
                 then Seq_Self = Seq_Self'Old and then T = 0 and then Seq = 0
                      and then not Clamped and then not Born_Expired)
       --  The cases below are per Result, not an if/elsif on In_W. GNAT
       --  14.4 crashes (decl.cc:464) under -gnatVa on Seq_Self'Old in
       --  branches of a condition known on entry.
       and then
       (if Result in OK | Shadowed then
          --  T13 / T8: seq strictly increases, with no wrap. It increases
          --  by exactly one, unless H8 made it jump.
          Seq = Seq_Self
          and then Seq_Self = Seq_Base (Seq_Self'Old, Max_Own_Seq (S, Self)) + 1
          and then Seq_Self > Seq_Self'Old
          and then (if not Clone_Suspected then Seq_Self = Seq_Self'Old + 1)
          --  DESIGN.md §5 exactly: the formula over the writer's ceiling
          --  (maxceil and its cap), with a DEL's clock raised to Del_Low
          --  and the expire mark as a floor term (H28).
          and then T = T_Emit (Now_Eff (Tgt, Now, Ceil (Regs (S))),
                               True, Floor_Time (S, Tgt, Mark),
                               Eff_Ceil (S, Self))
          --  T8 / H8: the emitted seq is more than each held own seq.
          and then
          (for all I in 1 .. Count (S) =>
             (if Own (Held (S, I), Self) then Held (S, I).V.Seq < Seq))
          --  T9 / T13: never above the ceiling, nor above the cap.
          and then T <= Ceil (Regs (S))
          and then T <= W_Cap (Regs (S), Self)
          --  H28: above the expire mark, unless the mark is at or above
          --  the writer's ceiling (then T is the ceiling, and Clamped).
          and then (if Mark < Eff_Ceil (S, Self) then T > Mark)
          --  H22: Clamped iff T < max (Now, floor.t + 1): the ceiling held
          --  the write back. Then T is the ceiling.
          and then Clamped = Is_Clamped (T, Now, Floor_Time (S, Tgt, Mark))
          and then (if Clamped then T = Eff_Ceil (S, Self))
          --  H22: Born_Expired iff a DEL with T + Del_TTL <= Now.
          and then Born_Expired = Is_Born_Expired (Tgt, T, Del_TTL, Now)
          --  If the real clock is below the ceiling, T obeys it.
          and then (if Now <= Eff_Ceil (S, Self) then T >= Now)
          --  A5: a DEL is at least maxceil - Cap_Lead, unless the cap is
          --  lower.
          and then (if Tgt.Op = W_Del
                    then T >= U48'Min (Del_Low (Ceil (Regs (S))), Eff_Ceil (S, Self)))
          --  T8 chase: the write always goes above a floor below the
          --  writer's ceiling.
          and then (if Floor (S, Tgt).Present
                      and then Floor (S, Tgt).V.T < Eff_Ceil (S, Self)
                    then Prefix_Lt (Floor (S, Tgt).V,
                                    Stamp (T, Self, Seq, Zero_Key))
                         and then Result = OK)
          --  DESIGN.md §5: Shadowed iff a floor exists and v_emit < floor,
          --  decided on the prefix (D8). This is the same as: the write is
          --  not above the floor (the prefixes are different, H8). This
          --  occurs only at the ceiling, with the floor exactly at it (T9:
          --  the floor is admitted).
          and then (Result = Shadowed) =
                     (Floor (S, Tgt).Present
                      and then Prefix_Lt (Stamp (T, Self, Seq, Zero_Key),
                                          Floor (S, Tgt).V))
          and then (Result = Shadowed) =
                     (Floor (S, Tgt).Present
                      and then not Prefix_Lt (Floor (S, Tgt).V,
                                              Stamp (T, Self, Seq, Zero_Key)))
          and then (if Result = Shadowed
                    then T = Eff_Ceil (S, Self)
                         and then Floor (S, Tgt).V.T >= Eff_Ceil (S, Self))
          --  T8 read-your-writes: on the prefix, an OK write is above each
          --  record that can dominate it, so for each h it is admitted
          --  and undominated (Lemma_OK_Undominated). Kome.Frontier.Apply
          --  holds it, unless the store is full.
          and then
          (if Result = OK then
             (for all I in 1 .. Count (S) =>
                (if In_Floor (Held (S, I), Tgt)
                 then Prefix_Lt (Held (S, I).V,
                                 Stamp (T, Self, Seq, Zero_Key))))));

   ---------------------------------------------------------------------------
   --  D8: the outcome of Choose does not depend on h.
   ---------------------------------------------------------------------------

   --  For each content hash H, the record built from (T, Self, Seq) is
   --  canonical and admitted. It compares with each floor record exactly as
   --  its prefix does. The Post of Choose gives the Pre for OK and
   --  Shadowed. Frontier.lean `lt_iff_prefix`.
   procedure Lemma_Outcome_Independent_Of_H
     (S : State; Tgt : Target; T : U48; Self : Key256; Seq : U48; H : Key256)
   with
     Ghost, Global => null,
     Pre  => Is_Frontier (S)
             and then T <= Ceil (Regs (S))
             and then T <= W_Cap (Regs (S), Self)
             and then In_W (Regs (S), Self)
             and then (for all I in 1 .. Count (S) =>
                         (if Own (Held (S, I), Self)
                          then Held (S, I).V.Seq < Seq)),
     Post => Canonical (To_Header (Tgt, Stamp (T, Self, Seq, H)))
             and then Admitted (S, To_Header (Tgt, Stamp (T, Self, Seq, H)))
             and then
             (for all I in 1 .. Count (S) =>
                (if In_Floor (Held (S, I), Tgt)
                 then Lt (Held (S, I).V, Stamp (T, Self, Seq, H))
                        = Prefix_Lt (Held (S, I).V, Stamp (T, Self, Seq, H))
                      and then
                      Lt (Stamp (T, Self, Seq, H), Held (S, I).V)
                        = Prefix_Lt (Stamp (T, Self, Seq, H), Held (S, I).V)));

   --  The corollary: if Choose gave OK, then for each H the record built
   --  from (T, Self, Seq) is admitted, and no held record dominates it.
   --  Kome.Frontier.Apply then holds it, unless the store is full
   --  (No_Space). The Post of Choose gives exactly this Pre for OK.
   procedure Lemma_OK_Undominated
     (S : State; Tgt : Target; T : U48; Self : Key256; Seq : U48; H : Key256)
   with
     Ghost, Global => null,
     Pre  => Is_Frontier (S)
             and then T <= Ceil (Regs (S))
             and then T <= W_Cap (Regs (S), Self)
             and then In_W (Regs (S), Self)
             and then (for all I in 1 .. Count (S) =>
                         (if Own (Held (S, I), Self)
                          then Held (S, I).V.Seq < Seq))
             and then (for all I in 1 .. Count (S) =>
                         (if In_Floor (Held (S, I), Tgt)
                          then Prefix_Lt (Held (S, I).V,
                                          Stamp (T, Self, Seq, Zero_Key)))),
     Post => Admitted (S, To_Header (Tgt, Stamp (T, Self, Seq, H)))
             and then
             (for all I in 1 .. Count (S) =>
                (if In_Floor (Held (S, I), Tgt)
                 then Lt (Held (S, I).V, Stamp (T, Self, Seq, H))))
             and then
             (for all I in 1 .. Count (S) =>
                not Dominates (Held (S, I), To_Header (Tgt, Stamp (T, Self, Seq, H))))
             and then not Dom (S, To_Header (Tgt, Stamp (T, Self, Seq, H)));

   ---------------------------------------------------------------------------
   --  G21: the record of step 2 occupies the cell of the target of step 1.
   ---------------------------------------------------------------------------

   --  The header of Kome.Records.Make_Put (Cid, NS, Ent, Field, T, Seq,
   --  Author, Value) in the collection of Cid is To_Header (Put_Target (ns,
   --  ent, Field), Stamp (T, author, Seq, h)), where ns, ent and author are
   --  the Id128 / Key256 forms of the byte arguments and h is the hash of
   --  the built content under Cid (AUDIT.md A26). The Post of Make_Put
   --  gives the header; this lemma states it in Emit's terms.
   procedure Lemma_Put_Target_Matches
     (Cid    : Hash256;
      NS     : NS_Id;
      Ent    : Ent_Id;
      Field  : Byte_Array;
      T, Seq : U48;
      Author : Pubkey;
      Value  : Byte_Array)
   with
     Ghost, Global => null,
     Pre  => Field'Length in 1 .. Field_Max and then Value'Length <= Value_Max,
     Post =>
       Kome.Records.To_Header
         (Cid, Kome.Records.Make_Put (Cid, NS, Ent, Field, T, Seq, Author, Value))
       = To_Header
           (Put_Target (To_Id128 (NS), To_Id128 (Ent), Field),
            Stamp (T, To_Key256 (Author), Seq,
                   To_Key256
                     (Kome.Records.Hash
                        (Cid,
                         Kome.Records.Make_Put
                           (Cid, NS, Ent, Field, T, Seq, Author, Value).C))));

   --  The DEL counterpart: the header of Kome.Records.Make_Del (Cid, NS,
   --  Ent, T, Seq, Author) is To_Header (Del_Target (ns, ent), Stamp (T,
   --  author, Seq, h)), h under Cid.
   procedure Lemma_Del_Target_Matches
     (Cid    : Hash256;
      NS     : NS_Id;
      Ent    : Ent_Id;
      T, Seq : U48;
      Author : Pubkey)
   with
     Ghost, Global => null,
     Post =>
       Kome.Records.To_Header (Cid, Kome.Records.Make_Del (Cid, NS, Ent, T, Seq, Author))
       = To_Header
           (Del_Target (To_Id128 (NS), To_Id128 (Ent)),
            Stamp (T, To_Key256 (Author), Seq,
                   To_Key256
                     (Kome.Records.Hash
                        (Cid, Kome.Records.Make_Del (Cid, NS, Ent, T, Seq, Author).C))));

   ---------------------------------------------------------------------------
   --  Laws of the flags (H22).
   ---------------------------------------------------------------------------

   --  Is_Clamped is T < max (Now, Floor_T + 1) over the integers.
   procedure Lemma_Clamped_Formula (T, Now, Floor_T : U48) with
     Ghost, Global => null,
     Post => Is_Clamped (T, Now, Floor_T) =
               (Long_Long_Integer (T) <
                  Long_Long_Integer'Max (Long_Long_Integer (Now),
                                         Long_Long_Integer (Floor_T) + 1));

   --  Is_Born_Expired is "a DEL with T + Del_TTL <= Now" over the integers.
   procedure Lemma_Born_Expired_Formula
     (Tgt : Target; T, Del_TTL, Now : U48)
   with
     Ghost, Global => null,
     Post => Is_Born_Expired (Tgt, T, Del_TTL, Now) =
               (Tgt.Op = W_Del
                and then Long_Long_Integer (T) + Long_Long_Integer (Del_TTL)
                           <= Long_Long_Integer (Now));

   --  H28 / T8: with the floor term below the ceiling, t_emit is above it
   --  for every value of Now; otherwise t_emit is the ceiling.
   procedure Lemma_Above_Floor (Now, Floor_T, Ceil : U48) with
     Ghost, Global => null,
     Post => (if Floor_T < Ceil
              then T_Emit (Now, True, Floor_T, Ceil) > Floor_T
              else T_Emit (Now, True, Floor_T, Ceil) = Ceil);

   ---------------------------------------------------------------------------
   --  Laws of t_emit. T_Emit refines Frontier.lean `emitT`
   --  (Lemma_T_Emit_Formula).
   ---------------------------------------------------------------------------

   --  T9 / T13: never above the ceiling. Frontier.lean `emitT_le`.
   procedure Lemma_Emit_Bounded (Now : U48; Has_Floor : Boolean; Floor_T, Ceil : U48)
   with
     Ghost, Global => null,
     Post => T_Emit (Now, Has_Floor, Floor_T, Ceil) <= Ceil;

   --  T13 (no wrap): t_emit is the formula of DESIGN.md §5 evaluated over
   --  the integers, min (max (now, floor.t + 1), maxceil). The result fits
   --  in U48.
   procedure Lemma_T_Emit_Formula (Now, Floor_T, Ceil : U48) with
     Ghost, Global => null,
     Post => Long_Long_Integer (T_Emit (Now, True, Floor_T, Ceil)) =
               Long_Long_Integer'Min
                 (Long_Long_Integer'Max (Long_Long_Integer (Now),
                                         Long_Long_Integer (Floor_T) + 1),
                  Long_Long_Integer (Ceil))
             and then T_Emit (Now, False, Floor_T, Ceil) = U48'Min (Now, Ceil);

   --  T8 chase, Frontier.lean `chase`: if floor.t < maxceil, then
   --  v_emit > floor for all values of Now
   --  (Now = 0, a device with no clock, also chases).
   procedure Lemma_Chase (Now, Ceil : U48; Floor_V, V : Version) with
     Ghost, Global => null,
     Pre  => Floor_V.T < Ceil
             and then V.T = T_Emit (Now, True, Floor_V.T, Ceil),
     Post => Lt (Floor_V, V) and then Prefix_Lt (Floor_V, V)
             and then V.T > Floor_V.T;

   --  A write is shadowed only at the ceiling, and only if the floor is at
   --  or above the ceiling.
   procedure Lemma_Shadow_At_Ceiling (Now, Ceil : U48; Floor_V, V : Version) with
     Ghost, Global => null,
     Pre  => V.T = T_Emit (Now, True, Floor_V.T, Ceil)
             and then not Lt (Floor_V, V),
     Post => V.T = Ceil and then Floor_V.T >= Ceil;

   --  T9 (bounded pin): a higher ceiling never gives a lower t_emit. When
   --  the ceiling is above the floor, no write is shadowed.
   procedure Lemma_Raise_Unpins
     (Now : U48; Ceil1, Ceil2 : U48; Floor_V, V : Version)
   with
     Ghost, Global => null,
     Pre  => Ceil1 <= Ceil2
             and then Floor_V.T < Ceil2
             and then V.T = T_Emit (Now, True, Floor_V.T, Ceil2),
     Post => T_Emit (Now, True, Floor_V.T, Ceil1) <= V.T
             and then Lt (Floor_V, V);

   --  Below the ceiling, t_emit obeys the real clock.
   procedure Lemma_Respects_Clock (Now : U48; Has_Floor : Boolean; Floor_T, Ceil : U48)
   with
     Ghost, Global => null,
     Pre  => Now <= Ceil,
     Post => T_Emit (Now, Has_Floor, Floor_T, Ceil) >= Now;

   ---------------------------------------------------------------------------
   --  State-level T9: the floor against Kome.Frontier's invariant.
   ---------------------------------------------------------------------------

   --  T9: on a frontier each held record is admitted, so the floor is
   --  never above the ceiling. The Post of Choose says that Shadowed means
   --  floor.t >= maxceil. Thus a Shadowed write on a frontier has exactly
   --  floor.t = t_emit = maxceil.
   procedure Lemma_Floor_Admitted (S : State; Tgt : Target) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S),
     Post => (if Floor (S, Tgt).Present
              then Floor (S, Tgt).V.T <= Ceil (Regs (S)));

   --  T9 (bounded pin), state form: "after Kome applies a roster with a
   --  higher ceiling, no honest write to any cell is shadowed". S2 is S1
   --  after a change that raised the ceiling and added no new data record
   --  (Kome.Frontier.Apply of a ROSTER: each record held after it was held
   --  before it, or is the roster). Then each floor of S2 is strictly below
   --  the ceiling of S2, so Choose on S2 chases it and gives OK (or
   --  Inadmissible / Seq_Exhausted, which emit nothing).
   procedure Lemma_Roster_Unpins (S1, S2 : State; Tgt : Target) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S1)
             and then Ceil (Regs (S1)) < Ceil (Regs (S2))
             and then (for all I in 1 .. Count (S2) =>
                         (if Is_Data (Held (S2, I))
                          then Holds (S1, Held (S2, I)))),
     Post => (if Floor (S2, Tgt).Present
              then Floor (S2, Tgt).V.T < Ceil (Regs (S2)));

end Kome.Emit;
