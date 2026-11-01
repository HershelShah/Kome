--  Kome.Views: the pure views over one replica's frontier (DESIGN.md §3
--  "Views", §6 module J and revocation). Each view is a function of the held
--  records only, read through Kome.Frontier's public functions (Count, Held),
--  so it is a function of F and nothing else (T5); the lemmas below state
--  that as SPARK facts:
--
--    cell(ns, ent, f)    := the unique PUT in F on (ns, ent, f)     -- Option
--    deleted_at(ns, ent) := max { d.v | d ∈ F, DEL on (ns, ent) }   -- Option
--    exists(ns, ent)     := ∃ f. cell(ns, ent, f) ≠ None
--    void(p)             := ∃ REVOKE(p.author, from_t) ∈ F : p.t ≥ from_t
--    far(p)              := p.t > now_local + slack                -- advisory
--    ROSTER_eff(ns)      := max_(gen,h) over frontier rosters whose signer
--                           is not root_void
--
--  `cell`, `deleted_at` and `ROSTER_eff` are computed as maxima, so they are
--  well defined on any held array. That the maximum is the *only* candidate
--  (so that the result does not depend on the order of the held array) needs
--  the hypothesis Lean's `cell_unique` calls `hinj`: a version determines its
--  record. Two forms are offered:
--
--    Canonical (X)        unused fields zero (Kome.Records enforces it). For
--                         PUT and DEL this suffices, because every field a
--                         PUT or DEL uses is in its cell key or its V.
--    Unique_Versions (S)  A2 on the held set: equal V means equal record
--                         (h is the content hash). Needed for ROSTER, whose
--                         Ceiling is used but not in V, so Canonical rosters
--                         equal in V may still differ.
--
--  Without either hypothesis every lemma below still proves that the
--  *versions* of the views agree; only the payload-level equality is
--  conditional.
--
--  Lemmas (T5, T12):
--    Lemma_Cell_Unique / Lemma_Del_Unique / Lemma_Roster_Unique /
--    Lemma_Roster_Eff_Unique   the maximum is unique (T5, `cell_unique`);
--    Lemma_Data_Local / Lemma_Cell_Local / Lemma_Views_Local
--                              the data views depend only on held PUT/DEL;
--    Lemma_Root_Void_Local / Lemma_Void_Local / Lemma_Roster_Local
--                              the authorization views depend only on held
--                              ROSTER/REVOKE;
--    Lemma_Apply_Auth_Local    applying a ROSTER or REVOKE keeps the PUT/DEL
--                              records (T12);
--    Lemma_Apply_Data_Local    applying a PUT or DEL keeps the ROSTER/REVOKE
--                              records;
--    Lemma_Void_Monotone / Lemma_Apply_Keeps_Revokes
--                              void only grows (T12).
pragma Ada_2022;
with Kome.Versions; use Kome.Versions;
with Kome.Headers;  use Kome.Headers;
with Kome.Frontier; use Kome.Frontier;
package Kome.Views with SPARK_Mode is

   No_Header  : constant Header  := (others => <>);
   No_Version : constant Version := (others => <>);
   Zero_Id    : constant Id128   := (others => 0);
   Zero_Key   : constant Key256  := (others => 0);

   --  Option-like results. When Present is False the payload is the default
   --  value, so two absent results compare equal.
   type Header_View is record
      Present : Boolean := False;
      Hdr     : Header  := No_Header;
   end record;

   type Version_View is record
      Present : Boolean := False;
      V       : Version := No_Version;
   end record;

   ---------------------------------------------------------------------------
   --  Quantifier-free predicates on one header (public, so callers unfold).
   ---------------------------------------------------------------------------

   --  A PUT on the cell (ns, ent, fh).
   function Put_On (X : Header; NS, Ent : Id128; FH : Key256) return Boolean is
     (X.K = K_Put and then X.NS = NS and then X.Ent = Ent and then X.FH = FH);

   --  A PUT on some field of the entity (ns, ent).
   function Put_In (X : Header; NS, Ent : Id128) return Boolean is
     (X.K = K_Put and then X.NS = NS and then X.Ent = Ent);

   --  A DEL of the entity (ns, ent).
   function Del_On (X : Header; NS, Ent : Id128) return Boolean is
     (X.K = K_Del and then X.NS = NS and then X.Ent = Ent);

   --  A REVOKE of Subject in ns. The revoked key is the REVOKE's V.Author
   --  and from_t is its V.T (Kome.Headers: V = (from_t, subject, rev_seq, h)).
   function Revokes (X : Header; NS : Id128; Subject : Key256) return Boolean is
     (X.K = K_Revoke and then X.NS = NS and then X.V.Author = Subject);

   --  X is a REVOKE that voids P: same collection, P's author is the
   --  subject, and P.t >= from_t (DESIGN.md §3 `void`).
   function Voids (X, P : Header) return Boolean is
     (Revokes (X, P.NS, P.V.Author) and then P.V.T >= X.V.T);

   function Roster_In (X : Header; NS : Id128) return Boolean is
     (X.K = K_Roster and then X.NS = NS);

   --  The effective-roster order (DESIGN.md §6 module J): (gen, h), where a
   --  roster's V is (0, signer, gen, h). Ties on (gen, h) can only occur
   --  between non-distinct records (A2); they are broken by the full version
   --  order so that the order is strict and total on versions
   --  (Lemma_Gen_Lt_Total).
   function Gen_Lt (A, B : Header) return Boolean is
     (A.V.Seq < B.V.Seq
      or else (A.V.Seq = B.V.Seq
        and then (Lt (A.V.H, B.V.H)
          or else (A.V.H = B.V.H and then Lt (A.V, B.V)))));

   --  Canonical form: the fields a kind does not use are zero (Kome.Headers;
   --  enforced by Kome.Records at decode). For PUT and DEL it is what makes
   --  "same cell, same version" mean "same record" (the hypothesis `hinj` of
   --  Frontier.lean `cell_unique`). It is NOT enough for ROSTER, whose
   --  Ceiling is a used field outside V: use Unique_Versions there.
   function Canonical (X : Header) return Boolean is
     (case X.K is
        when K_Put    => X.Ceiling = 0,
        when K_Del    => X.FH = Zero_Key and then X.Ceiling = 0,
        when K_Roster => X.Ent = Zero_Id and then X.FH = Zero_Key and then X.V.T = 0,
        when K_Revoke => X.Ent = Zero_Id and then X.FH = Zero_Key and then X.Ceiling = 0);

   --  far(p): advisory flag only, never consulted by the lattice (DESIGN.md
   --  §3). Written without the sum Now + Slack, which could exceed U48.
   function Is_Far (P : Header; Now, Slack : U48) return Boolean is
     (P.V.T > Slack and then P.V.T - Slack > Now);

   ---------------------------------------------------------------------------
   --  Ghost predicates on states (quantified, so opaque: see private part).
   ---------------------------------------------------------------------------

   --  A2 on the held set (DESIGN.md §9 assumption A2; Frontier.lean `hinj`):
   --  two held records with the same version are the same record. h is the
   --  record's BLAKE2b content hash, so this holds for every state built from
   --  verified records except with negligible probability; it is a
   --  cryptographic assumption, not something Kome.Frontier can check.
   function Unique_Versions (S : State) return Boolean with Ghost, Global => null;

   --  S1 and S2 hold the same PUT and DEL records.
   function Same_Data (S1, S2 : State) return Boolean with Ghost, Global => null;

   --  S1 and S2 hold the same ROSTER and REVOKE records.
   function Same_Auth (S1, S2 : State) return Boolean with Ghost, Global => null;

   ---------------------------------------------------------------------------
   --  The views (T5: each is a function of the held records).
   ---------------------------------------------------------------------------

   --  cell(ns, ent, fh): the live PUT on the cell, if any. On a frontier it is
   --  the only one (Lemma_Cell_Unique); in general it is a maximal one.
   function Cell (S : State; NS, Ent : Id128; FH : Key256) return Header_View with
     Global => null,
     Post =>
       Cell'Result.Present =
         (for some I in 1 .. Count (S) => Put_On (Held (S, I), NS, Ent, FH))
       and then
       (if Cell'Result.Present then
          Put_On (Cell'Result.Hdr, NS, Ent, FH)
          and then (for some I in 1 .. Count (S) => Held (S, I) = Cell'Result.Hdr)
          and then (for all I in 1 .. Count (S) =>
                      (if Put_On (Held (S, I), NS, Ent, FH)
                       then not Lt (Cell'Result.Hdr.V, Held (S, I).V)))
        else Cell'Result.Hdr = No_Header);

   --  deleted_at(ns, ent): the maximal DEL version on the entity, if any.
   function Deleted_At (S : State; NS, Ent : Id128) return Version_View with
     Global => null,
     Post =>
       Deleted_At'Result.Present =
         (for some I in 1 .. Count (S) => Del_On (Held (S, I), NS, Ent))
       and then
       (if Deleted_At'Result.Present then
          (for some I in 1 .. Count (S) =>
             Del_On (Held (S, I), NS, Ent) and then Held (S, I).V = Deleted_At'Result.V)
          and then (for all I in 1 .. Count (S) =>
                      (if Del_On (Held (S, I), NS, Ent)
                       then not Lt (Deleted_At'Result.V, Held (S, I).V)))
        else Deleted_At'Result.V = No_Version);

   --  exists(ns, ent): some live PUT on the entity. There is no presence
   --  bit: a deleted entity is a DEL and nothing else (DESIGN.md §3).
   function Exists (S : State; NS, Ent : Id128) return Boolean with
     Global => null,
     Post => Exists'Result =
               (for some I in 1 .. Count (S) => Put_In (Held (S, I), NS, Ent));

   --  void(p): some held REVOKE of p's author with from_t <= p.t.
   function Is_Void (S : State; P : Header) return Boolean with
     Global => null,
     Post => Is_Void'Result =
               (for some I in 1 .. Count (S) => Voids (Held (S, I), P));

   --  root_void(k): some held REVOKE of key K in ns, whatever its from_t.
   --
   --  DESIGN.md §6 uses `root_void` without defining it; this is the reading
   --  chosen here (to be recorded in DESIGN.md §6 / §10). The reason: a
   --  roster's V.T is 0, so void(roster) would only fire for from_t = 0.
   --  Consequences, all deliberate under this reading:
   --   * a REVOKE of a root with any from_t, even one far in the future that
   --     was meant to keep the root's earlier data records, disregards every
   --     roster that root ever signed, including older ones;
   --   * the header carries no issuer, so a REVOKE counts whoever signed it,
   --     including a root that is itself revoked (admission, `signer ∈
   --     roots_ever`, is the only gate, as for every authorization record);
   --   * if every root that signed a held roster is revoked, ROSTER_eff is
   --     None (Present = False).
   function Root_Void (S : State; NS : Id128; K : Key256) return Boolean with
     Global => null,
     Post => Root_Void'Result =
               (for some I in 1 .. Count (S) => Revokes (Held (S, I), NS, K));

   --  ROSTER_eff(ns): the (gen, h)-maximal held ROSTER of ns whose signer
   --  (its V.Author) is not root_void (DESIGN.md §6 module J). None when no
   --  held roster of ns has an unrevoked signer, in particular when every
   --  signing root has been revoked. Under Unique_Versions it is the unique
   --  such maximum (Lemma_Roster_Eff_Unique).
   function Roster_Eff (S : State; NS : Id128) return Header_View with
     Global => null,
     Post =>
       Roster_Eff'Result.Present =
         (for some I in 1 .. Count (S) =>
            Roster_In (Held (S, I), NS)
            and then not Root_Void (S, NS, Held (S, I).V.Author))
       and then
       (if Roster_Eff'Result.Present then
          Roster_In (Roster_Eff'Result.Hdr, NS)
          and then not Root_Void (S, NS, Roster_Eff'Result.Hdr.V.Author)
          and then (for some I in 1 .. Count (S) => Held (S, I) = Roster_Eff'Result.Hdr)
          and then (for all I in 1 .. Count (S) =>
                      (if Roster_In (Held (S, I), NS)
                         and then not Root_Void (S, NS, Held (S, I).V.Author)
                       then not Gen_Lt (Roster_Eff'Result.Hdr, Held (S, I))))
        else Roster_Eff'Result.Hdr = No_Header);

   ---------------------------------------------------------------------------
   --  Laws: uniqueness of the maxima (T5).
   ---------------------------------------------------------------------------

   --  T5, Frontier.lean `cell_unique`: two held PUTs on one cell of a
   --  frontier have the same version (else the newer dominates the older);
   --  when both are canonical, or under A2, they are the same record at the
   --  same index.
   procedure Lemma_Cell_Unique (S : State; I, J : Held_Index) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S)
             and then I <= Count (S) and then J <= Count (S)
             and then Held (S, I).K = K_Put
             and then Put_On (Held (S, J), Held (S, I).NS, Held (S, I).Ent, Held (S, I).FH),
     Post => Held (S, I).V = Held (S, J).V
             and then (if (Canonical (Held (S, I)) and then Canonical (Held (S, J)))
                          or else Unique_Versions (S)
                       then Held (S, I) = Held (S, J) and then I = J);

   --  T5 for deleted_at: a frontier holds at most one DEL version per entity.
   procedure Lemma_Del_Unique (S : State; I, J : Held_Index) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S)
             and then I <= Count (S) and then J <= Count (S)
             and then Held (S, I).K = K_Del
             and then Del_On (Held (S, J), Held (S, I).NS, Held (S, I).Ent),
     Post => Held (S, I).V = Held (S, J).V
             and then (if (Canonical (Held (S, I)) and then Canonical (Held (S, J)))
                          or else Unique_Versions (S)
                       then Held (S, I) = Held (S, J) and then I = J);

   --  Gen_Lt is a strict total order up to equal versions.
   procedure Lemma_Gen_Lt_Total (A, B : Header) with
     Ghost, Global => null,
     Post => Gen_Lt (A, B) or else A.V = B.V or else Gen_Lt (B, A);

   procedure Lemma_Gen_Lt_Irrefl (A : Header) with
     Ghost, Global => null,
     Post => not Gen_Lt (A, A);

   --  T5 for ROSTER_eff: under A2, two held records that are Gen_Lt-
   --  incomparable (for instance two Gen_Lt-maximal eligible rosters) are
   --  the same record, and on a frontier the same index.
   procedure Lemma_Roster_Unique (S : State; I, J : Held_Index) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S) and then Unique_Versions (S)
             and then I <= Count (S) and then J <= Count (S)
             and then not Gen_Lt (Held (S, I), Held (S, J))
             and then not Gen_Lt (Held (S, J), Held (S, I)),
     Post => Held (S, I) = Held (S, J) and then I = J;

   --  T5 for ROSTER_eff, as a characterisation: under A2, any held eligible
   --  roster that no held eligible roster beats in (gen, h) IS ROSTER_eff,
   --  whatever the order of the held array. No frontier hypothesis needed.
   procedure Lemma_Roster_Eff_Unique (S : State; NS : Id128; I : Held_Index) with
     Ghost, Global => null,
     Pre  => Unique_Versions (S)
             and then I <= Count (S)
             and then Roster_In (Held (S, I), NS)
             and then not Root_Void (S, NS, Held (S, I).V.Author)
             and then (for all J in 1 .. Count (S) =>
                         (if Roster_In (Held (S, J), NS)
                            and then not Root_Void (S, NS, Held (S, J).V.Author)
                          then not Gen_Lt (Held (S, I), Held (S, J)))),
     Post => Roster_Eff (S, NS) = (Present => True, Hdr => Held (S, I));

   --  exists(ns, ent) = ∃ f. cell(ns, ent, f) ≠ None, in both directions:
   --  a present cell makes the entity exist, and an existing entity has a
   --  present cell at the field of one of its held PUTs.
   procedure Lemma_Exists_Cell (S : State; NS, Ent : Id128; FH : Key256) with
     Ghost, Global => null,
     Post => (if Cell (S, NS, Ent, FH).Present then Exists (S, NS, Ent))
             and then
             (if Exists (S, NS, Ent) then
                (for some I in 1 .. Count (S) =>
                   Put_In (Held (S, I), NS, Ent)
                   and then Cell (S, NS, Ent, Held (S, I).FH).Present));

   ---------------------------------------------------------------------------
   --  Laws: locality (T5, T12).
   ---------------------------------------------------------------------------

   --  deleted_at and exists are functions of the held PUT and DEL records
   --  alone; no hypothesis on the records is needed.
   procedure Lemma_Data_Local (S1, S2 : State; NS, Ent : Id128) with
     Ghost, Global => null,
     Pre  => Same_Data (S1, S2),
     Post => Deleted_At (S1, NS, Ent) = Deleted_At (S2, NS, Ent)
             and then Exists (S1, NS, Ent) = Exists (S2, NS, Ent);

   --  cell is a function of the held PUT and DEL records: its presence and
   --  version always, its whole header when S1's PUTs are canonical or S1
   --  satisfies A2 (Same_Data carries every PUT of S2 into S1, so a
   --  hypothesis on S1 alone suffices).
   procedure Lemma_Cell_Local (S1, S2 : State; NS, Ent : Id128; FH : Key256) with
     Ghost, Global => null,
     Pre  => Same_Data (S1, S2),
     Post => Cell (S1, NS, Ent, FH).Present = Cell (S2, NS, Ent, FH).Present
             and then Cell (S1, NS, Ent, FH).Hdr.V = Cell (S2, NS, Ent, FH).Hdr.V
             and then
             (if (for all I in 1 .. Count (S1) =>
                    (if Held (S1, I).K = K_Put then Canonical (Held (S1, I))))
                 or else Unique_Versions (S1)
              then Cell (S1, NS, Ent, FH) = Cell (S2, NS, Ent, FH));

   --  T5 / T12: the three data views together (Lemma_Data_Local and
   --  Lemma_Cell_Local).
   procedure Lemma_Views_Local (S1, S2 : State; NS, Ent : Id128; FH : Key256) with
     Ghost, Global => null,
     Pre  => Same_Data (S1, S2)
             and then
             ((for all I in 1 .. Count (S1) =>
                 (if Held (S1, I).K = K_Put then Canonical (Held (S1, I))))
              or else Unique_Versions (S1)),
     Post => Cell (S1, NS, Ent, FH) = Cell (S2, NS, Ent, FH)
             and then Deleted_At (S1, NS, Ent) = Deleted_At (S2, NS, Ent)
             and then Exists (S1, NS, Ent) = Exists (S2, NS, Ent);

   --  root_void and void are functions of the held REVOKE records.
   procedure Lemma_Root_Void_Local (S1, S2 : State; NS : Id128; K : Key256) with
     Ghost, Global => null,
     Pre  => Same_Auth (S1, S2),
     Post => Root_Void (S1, NS, K) = Root_Void (S2, NS, K);

   procedure Lemma_Void_Local (S1, S2 : State; P : Header) with
     Ghost, Global => null,
     Pre  => Same_Auth (S1, S2),
     Post => Is_Void (S1, P) = Is_Void (S2, P);

   --  ROSTER_eff is a function of the held ROSTER and REVOKE records: its
   --  presence and version always, its whole header under A2 on S1 (the
   --  hypothesis Canonical cannot replace: two canonical rosters may share V
   --  and differ in Ceiling).
   procedure Lemma_Roster_Local (S1, S2 : State; NS : Id128) with
     Ghost, Global => null,
     Pre  => Same_Auth (S1, S2),
     Post => Roster_Eff (S1, NS).Present = Roster_Eff (S2, NS).Present
             and then Roster_Eff (S1, NS).Hdr.V = Roster_Eff (S2, NS).Hdr.V
             and then (if Unique_Versions (S1)
                       then Roster_Eff (S1, NS) = Roster_Eff (S2, NS));

   --  T12 (revocation locality): applying a REVOKE or a ROSTER never adds or
   --  removes a PUT or DEL. The hypotheses are Kome.Frontier.Apply's
   --  postcondition clauses for Before = S'Old and After = S, whatever the
   --  Status.
   procedure Lemma_Apply_Auth_Local (Before, After : State; R : Header) with
     Ghost, Global => null,
     Pre  => Is_Frontier (Before)
             and then R.K in K_Roster | K_Revoke
             and then (for all I in 1 .. Count (After) =>
                         Holds (Before, Held (After, I)) or else Held (After, I) = R)
             and then (for all I in 1 .. Count (Before) =>
                         Holds (After, Held (Before, I)) or else Dom (After, Held (Before, I))),
     Post => Same_Data (Before, After);

   --  The converse: applying a PUT or a DEL never adds or removes a ROSTER
   --  or REVOKE, so it changes neither void, root_void nor ROSTER_eff.
   --  Same hypotheses (Apply's postcondition), whatever the Status.
   procedure Lemma_Apply_Data_Local (Before, After : State; R : Header) with
     Ghost, Global => null,
     Pre  => Is_Frontier (Before)
             and then R.K in K_Put | K_Del
             and then (for all I in 1 .. Count (After) =>
                         Holds (Before, Held (After, I)) or else Held (After, I) = R)
             and then (for all I in 1 .. Count (Before) =>
                         Holds (After, Held (Before, I)) or else Dom (After, Held (Before, I))),
     Post => Same_Auth (Before, After);

   --  T12, "void is monotone in F": a void verdict survives into any state
   --  that holds every REVOKE of the first.
   procedure Lemma_Void_Monotone (S1, S2 : State; P : Header) with
     Ghost, Global => null,
     Pre  => (for all I in 1 .. Count (S1) =>
                (if Held (S1, I).K = K_Revoke then Holds (S2, Held (S1, I))))
             and then Is_Void (S1, P),
     Post => Is_Void (S2, P);

   --  T12 (part), Frontier.lean `revoke_never_dominated`: Apply never loses a
   --  REVOKE, so with Lemma_Void_Monotone, void only ever grows. The
   --  hypothesis is Apply's "nothing lost except by domination" clause.
   procedure Lemma_Apply_Keeps_Revokes (Before, After : State) with
     Ghost, Global => null,
     Pre  => (for all I in 1 .. Count (Before) =>
                Holds (After, Held (Before, I)) or else Dom (After, Held (Before, I))),
     Post => (for all I in 1 .. Count (Before) =>
                (if Held (Before, I).K = K_Revoke then Holds (After, Held (Before, I))));

private

   --  Quantified, so private: other units reason about them only through
   --  the lemmas above (CONVENTIONS.md, "keep the prover's view small").

   function Unique_Versions (S : State) return Boolean is
     (for all I in 1 .. Count (S) =>
        (for all J in 1 .. Count (S) =>
           (if Held (S, I).V = Held (S, J).V then Held (S, I) = Held (S, J))));

   function Same_Data (S1, S2 : State) return Boolean is
     ((for all I in 1 .. Count (S1) =>
         (if Is_Data (Held (S1, I)) then Holds (S2, Held (S1, I))))
      and then
      (for all I in 1 .. Count (S2) =>
         (if Is_Data (Held (S2, I)) then Holds (S1, Held (S2, I)))));

   function Same_Auth (S1, S2 : State) return Boolean is
     ((for all I in 1 .. Count (S1) =>
         (if not Is_Data (Held (S1, I)) then Holds (S2, Held (S1, I))))
      and then
      (for all I in 1 .. Count (S2) =>
         (if not Is_Data (Held (S2, I)) then Holds (S1, Held (S2, I)))));

end Kome.Views;
