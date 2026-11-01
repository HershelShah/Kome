--  Kome.Emit: the write path (DESIGN.md §5, "Clocks and writing"; T8 chase,
--  T9 bounded pin, T13 bounds, H8 backup-restore self-detection;
--  Frontier.lean `emitT`, `chase`, `emitT_le`).
--
--    floor(cell)  := max(cell(ns,ent,f).v, deleted_at(ns,ent))
--                    -- for DEL: max over all fields and deleted_at
--    t_emit       := max(now_ms, floor.t + 1 if floor exists);
--                    if t_emit > maxceil then t_emit := maxceil
--    seq_emit     := seq_self + 1; at 2^48 - 1 the write fails SEQ_EXHAUSTED
--    v_emit       := (t_emit, self_pk, seq_emit, h)
--    status       := SHADOWED if floor exists and v_emit < floor
--                    (only when t_emit = maxceil) else OK
--
--  H8 (backup restore / clone): before the write, the held records are
--  scanned for the device's own data records. If one has seq >= seq_self + 1
--  (seq_self was restored from a backup, or the key is cloned), seq jumps
--  past it and Clone_Suspected is raised. So the emitted (author, seq) is
--  strictly above every own record this replica holds (T8, "v_emit.seq
--  exceeds every seq this device emitted", as far as the replica can see),
--  and the emitted version is never equal to a held one. Kome.Status has no
--  CLONE_SUSPECTED literal, so the flag is a separate out parameter; the
--  write itself still succeeds with its own Result.
--
--  Because the emitted version is never equal to a held floor version (it
--  is by Self and its seq is above every held own seq), DESIGN.md's
--  "v_emit < floor" and "v_emit not above floor" coincide; the Post states
--  both, and an OK write is strictly above every record that could
--  dominate it.
--
--  Admission: a write by a key not in W is refused with Inadmissible and
--  nothing changes, so OK implies the emitted record is admitted (DESIGN.md
--  §4) and not dominated, i.e. Kome.Frontier.Apply will hold it. Tgt.NS must
--  be the state's collection; Kome.Frontier exposes no accessor for it, so
--  this is the caller's obligation (Kome.Records builds Tgt from the handle).
--
--  There is no engine clock and nothing is adopted from a peer: the only
--  inputs are the replica state, the local clock Now (0 on a device with no
--  real-time clock: every write then chases), the device key, the persisted
--  seq_self and the content hash H, which Kome.Records computes from the
--  canonical content and passes in. Emit fills the version; the caller
--  builds, signs and applies the record and persists Seq_Self (A5).
--
--  The floor is computed by scanning the held records through
--  Kome.Frontier's public view (Count, Held), so it is a function of F (T5).
--  It needs no Is_Frontier hypothesis: on any held array it is the maximum
--  of the relevant versions. On a frontier it is admitted, so it is never
--  above the ceiling (Lemma_Floor_Admitted).
--
--  No wrap (T13). t_emit is computed exactly as the formula above over the
--  integers (Lemma_T_Emit_Formula): when floor.t >= maxceil the result is
--  maxceil and floor.t + 1 is never formed, so floor.t = 2^48 - 1 is not a
--  refusal but an ordinary write at the ceiling (Shadowed unless it wins the
--  tie on author/seq/h). A seq that would pass 2^48 - 1 (seq_self at the
--  bound, or a held own record at the bound) refuses with Seq_Exhausted and
--  changes nothing.
--
--  This package declares no public constants (in particular no No_Version
--  or Zero_Key; the all-zero version is the function Zero_Version), so a
--  client may `use` it together with Kome.Views.
pragma Ada_2022;
with Kome.Versions; use Kome.Versions;
with Kome.Headers;  use Kome.Headers;
with Kome.Registers; use Kome.Registers;
with Kome.Frontier;  use Kome.Frontier;
package Kome.Emit with SPARK_Mode is

   --  The all-zero version: what an absent floor carries and what a refused
   --  write returns. A function with a name of its own (not No_Version), so
   --  it neither clashes with Kome.Views.No_Version under `use` nor needs a
   --  shared constant in Kome.Versions.
   function Zero_Version return Version is
     ((T => 0, Author => (others => 0), Seq => 0, H => (others => 0)));

   --  What is written: a PUT on the cell (ns, ent, fh) or a DEL of the
   --  entity (ns, ent). FH is ignored for a DEL (the emitted header carries
   --  zero there, Kome.Headers canonical form).
   type Write_Op is (W_Put, W_Del);

   type Target is record
      Op  : Write_Op := W_Put;
      NS  : Id128;
      Ent : Id128;
      FH  : Key256;
   end record;

   --  X is one of the records whose versions make up the floor of Tgt
   --  (DESIGN.md §5): for a PUT, a PUT on the same cell or a DEL of the
   --  entity; for a DEL, any PUT or DEL of the entity. Quantifier-free, so
   --  public. It covers every record that could dominate the emitted one
   --  (Kome.Headers.Dominates), which is what makes T8 read-your-writes.
   function In_Floor (X : Header; Tgt : Target) return Boolean is
     (X.NS = Tgt.NS and then X.Ent = Tgt.Ent
      and then (X.K = K_Del
                or else (X.K = K_Put
                         and then (Tgt.Op = W_Del or else X.FH = Tgt.FH))));

   --  The header of the record a write emits with version V.
   function To_Header (Tgt : Target; V : Version) return Header is
     (K       => (if Tgt.Op = W_Put then K_Put else K_Del),
      NS      => Tgt.NS,
      Ent     => Tgt.Ent,
      FH      => (if Tgt.Op = W_Put then Tgt.FH else Key256'(others => 0)),
      V       => V,
      Ceiling => 0);

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

   --  X is a data record this device (key Self) signed. Only PUT and DEL
   --  carry the device's seq in V.Seq (a ROSTER carries gen, a REVOKE the
   --  subject), so only they count for H8. Quantifier-free, so public.
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

   --  H8: the seq the next write increments. seq_self, unless a held own
   --  record has seq >= seq_self + 1 (written without forming the + 1), in
   --  which case seq jumps to that record's seq. Quantifier-free.
   function Seq_Base (Seq_Self : U48; O : Own_Seq_View) return U48 is
     (if O.Present and then O.Seq > Seq_Self then O.Seq else Seq_Self);

   --  H8: the clone / backup-restore condition DESIGN.md §5 names.
   function Clone_Detected (Seq_Self : U48; O : Own_Seq_View) return Boolean is
     (O.Present and then O.Seq > Seq_Self);

   --  t_emit (DESIGN.md §5), computed without forming floor.t + 1 when it
   --  could wrap. Quantifier-free, so public.
   function T_Emit (Now : U48; Has_Floor : Boolean; Floor_T, Ceil : U48)
     return U48
   is
     (if Has_Floor and then Floor_T >= Ceil then Ceil
      elsif Has_Floor then U48'Min (U48'Max (Now, Floor_T + 1), Ceil)
      else U48'Min (Now, Ceil));

   --  The version a write emits, given the floor and the incremented seq.
   function V_Emit
     (Now : U48; F : Floor_View; Ceil : U48; Self : Key256; Seq : U48;
      H   : Key256) return Version
   is
     ((T      => T_Emit (Now, F.Present, F.V.T, Ceil),
       Author => Self,
       Seq    => Seq,
       H      => H));

   --  Emit one write on Tgt.
   --    Inadmissible   Self is not in W: nothing emitted, Seq_Self unchanged.
   --    Seq_Exhausted  the seq would pass 2^48 - 1: nothing emitted,
   --                   Seq_Self unchanged (T13).
   --    OK / Shadowed  V is the version of the record to build (H is the
   --                   caller's content hash); Seq_Self has advanced (by one,
   --                   or past a held own record, H8); the caller persists it.
   --  Clone_Suspected reports the H8 condition in every case: a held record
   --  by Self has seq > Seq_Self (the caller surfaces CLONE_SUSPECTED).
   procedure Emit_Version
     (S               : in     State;
      Tgt             : in     Target;
      Now             : in     U48;
      Self            : in     Key256;
      H               : in     Key256;
      Seq_Self        : in out U48;
      V               :    out Version;
      Result          :    out Status;
      Clone_Suspected :    out Boolean)
   with
     Global => null,
     Pre  => True,   --  total: every input is acceptable
     Post =>
       Result in OK | Shadowed | Seq_Exhausted | Inadmissible
       --  H8: the restore/clone condition, always reported.
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
       --  A refusal has no side effect.
       and then (if Result in Inadmissible | Seq_Exhausted
                 then Seq_Self = Seq_Self'Old and then V = Zero_Version)
       --  The cases below are stated per Result rather than as an
       --  if/elsif on In_W: GNAT 14.4 crashes (decl.cc:464) under -gnatVa
       --  on Seq_Self'Old in branches of a condition known on entry.
       and then
       (if Result in OK | Shadowed then
          --  T13 / T8: seq strictly increases, no wrap; by exactly one
          --  unless H8 made it jump.
          Seq_Self = Seq_Base (Seq_Self'Old, Max_Own_Seq (S, Self)) + 1
          and then Seq_Self > Seq_Self'Old
          and then (if not Clone_Suspected then Seq_Self = Seq_Self'Old + 1)
          --  DESIGN.md §5 exactly.
          and then V = V_Emit (Now, Floor (S, Tgt), Ceil (Regs (S)), Self,
                               Seq_Self, H)
          --  T8 / H8: the emitted seq exceeds every own seq held.
          and then
          (for all I in 1 .. Count (S) =>
             (if Own (Held (S, I), Self) then Held (S, I).V.Seq < V.Seq))
          --  T9 / T13: never above the ceiling.
          and then V.T <= Ceil (Regs (S))
          --  The real clock is honoured when it is under the ceiling.
          and then (if Now <= Ceil (Regs (S)) then V.T >= Now)
          --  T8 chase: a floor below the ceiling is always overtaken.
          and then (if Floor (S, Tgt).Present
                      and then Floor (S, Tgt).V.T < Ceil (Regs (S))
                    then Lt (Floor (S, Tgt).V, V) and then Result = OK)
          --  DESIGN.md §5: Shadowed iff a floor exists and v_emit < floor;
          --  equivalently the write is not above the floor (H8 rules out
          --  equality). Only at the ceiling, with the floor at or above it.
          and then (Result = Shadowed) =
                     (Floor (S, Tgt).Present and then Lt (V, Floor (S, Tgt).V))
          and then (Result = Shadowed) =
                     (Floor (S, Tgt).Present
                      and then not Lt (Floor (S, Tgt).V, V))
          and then (if Result = Shadowed
                    then V.T = Ceil (Regs (S))
                         and then Floor (S, Tgt).V.T >= Ceil (Regs (S)))
          --  T8 read-your-writes: an OK write is admitted and above every
          --  record that could dominate it, so no held record dominates it
          --  and Kome.Frontier.Apply holds it.
          and then
          (if Result = OK then
             Admitted (S, To_Header (Tgt, V))
             and then
             (for all I in 1 .. Count (S) =>
                (if In_Floor (Held (S, I), Tgt)
                 then Lt (Held (S, I).V, V)))
             and then
             (for all I in 1 .. Count (S) =>
                not Dominates (Held (S, I), To_Header (Tgt, V)))
             and then not Dom (S, To_Header (Tgt, V))));

   ---------------------------------------------------------------------------
   --  Laws of t_emit. T_Emit refines Frontier.lean `emitT` (Lemma_T_Emit_Formula).
   ---------------------------------------------------------------------------

   --  T9 / T13: never above the ceiling. Frontier.lean `emitT_le`.
   procedure Lemma_Emit_Bounded (Now : U48; Has_Floor : Boolean; Floor_T, Ceil : U48)
   with
     Ghost, Global => null,
     Post => T_Emit (Now, Has_Floor, Floor_T, Ceil) <= Ceil;

   --  T13 (no wrap): t_emit is DESIGN.md §5's formula evaluated over the
   --  integers, min (max (now, floor.t + 1), maxceil), and is representable.
   procedure Lemma_T_Emit_Formula (Now, Floor_T, Ceil : U48) with
     Ghost, Global => null,
     Post => Long_Long_Integer (T_Emit (Now, True, Floor_T, Ceil)) =
               Long_Long_Integer'Min
                 (Long_Long_Integer'Max (Long_Long_Integer (Now),
                                         Long_Long_Integer (Floor_T) + 1),
                  Long_Long_Integer (Ceil))
             and then T_Emit (Now, False, Floor_T, Ceil) = U48'Min (Now, Ceil);

   --  T8 chase, Frontier.lean `chase`: if floor.t < maxceil then
   --  v_emit > floor, whatever Now is
   --  (Now = 0, a device with no clock, still chases).
   procedure Lemma_Chase (Now, Ceil : U48; Floor_V, V : Version) with
     Ghost, Global => null,
     Pre  => Floor_V.T < Ceil
             and then V.T = T_Emit (Now, True, Floor_V.T, Ceil),
     Post => Lt (Floor_V, V) and then V.T > Floor_V.T;

   --  Shadowing happens only at the ceiling, and only when the floor itself
   --  is at or above it.
   procedure Lemma_Shadow_At_Ceiling (Now, Ceil : U48; Floor_V, V : Version) with
     Ghost, Global => null,
     Pre  => V.T = T_Emit (Now, True, Floor_V.T, Ceil)
             and then not Lt (Floor_V, V),
     Post => V.T = Ceil and then Floor_V.T >= Ceil;

   --  T9 (bounded pin): raising the ceiling never lowers t_emit, and once
   --  the ceiling is above the floor every write is unshadowed.
   procedure Lemma_Raise_Unpins
     (Now : U48; Ceil1, Ceil2 : U48; Floor_V, V : Version)
   with
     Ghost, Global => null,
     Pre  => Ceil1 <= Ceil2
             and then Floor_V.T < Ceil2
             and then V.T = T_Emit (Now, True, Floor_V.T, Ceil2),
     Post => T_Emit (Now, True, Floor_V.T, Ceil1) <= V.T
             and then Lt (Floor_V, V);

   --  The real clock is honoured below the ceiling.
   procedure Lemma_Respects_Clock (Now : U48; Has_Floor : Boolean; Floor_T, Ceil : U48)
   with
     Ghost, Global => null,
     Pre  => Now <= Ceil,
     Post => T_Emit (Now, Has_Floor, Floor_T, Ceil) >= Now;

   ---------------------------------------------------------------------------
   --  State-level T9: the floor against Kome.Frontier's invariant.
   ---------------------------------------------------------------------------

   --  T9: on a frontier every held record is admitted, so the floor is
   --  never above the ceiling. With Emit_Version's Post (Shadowed implies
   --  floor.t >= maxceil), a Shadowed write on a frontier has
   --  floor.t = v_emit.t = maxceil exactly.
   procedure Lemma_Floor_Admitted (S : State; Tgt : Target) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S),
     Post => (if Floor (S, Tgt).Present
              then Floor (S, Tgt).V.T <= Ceil (Regs (S)));

   --  T9 (bounded pin), state form: "once a roster with a higher ceiling is
   --  applied, every honest write to any cell is unshadowed". S2 is S1 after
   --  something that raised the ceiling and brought no new data record
   --  (Kome.Frontier.Apply of a ROSTER: every record held after is held
   --  before or is the roster). Then every floor of S2 is strictly below
   --  S2's ceiling, so Emit_Version on S2 chases it and returns OK (or
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
