--  Kome.Views: the pure views over one collection's frontier
--  (DESIGN.md §3 "Views", §6 C9, root revocation D2 and D1′). A State is
--  one collection (Kome.Frontier.Collection (S)) with one founding key
--  (Kome.Frontier.Founding (S)). Each view is a function of only the held
--  records and the founding key. It reads them through the public
--  functions of Kome.Frontier (Count, Held, Founding), so it is a
--  function of F and of nothing else (T5). The lemmas below give this as
--  SPARK facts:
--
--    cell(ns, ent, f)    := the unique PUT in F on (ns, ent, f)     -- Option
--    deleted_at(ns, ent) := max { d.v | d ∈ F, DEL on (ns, ent) }   -- Option
--    exists(ns, ent)     := ∃ f. cell(ns, ent, f) ≠ None
--    root_void(k)        := k ≠ root_pk ∧ ∃ x ∈ F : REVOKE, x.subject = k,
--                                                   x.issuer = root_pk
--    W_eff(F)            := { g.subject | g ∈ F, GRANT, ¬ root_void(g.issuer) }
--    void(p)             := (∃ x ∈ F : REVOKE, x.subject = p.author,
--                              p.t ≥ x.from_t, ¬ root_void(x.issuer))
--                           ∨ p.author ∉ W_eff(F)
--    ROSTER_eff          := the maximal ROSTER r ∈ F with ¬ root_void(r.issuer),
--                           by (gen, h), ties by (signer, ceiling_t, del_ttl)
--    del_ttl_eff         := max { r.del_ttl | r ∈ F, ROSTER, ¬ root_void(r.issuer) },
--                           or Del_TTL_Default if there is none
--    far(p)              := p.t > now_local + slack                -- advisory
--
--  Each quantified view is opaque (declared here, defined in the body).
--  Other units read it through its Lemma_<View>_Def, which gives exactly
--  the definition above (CONVENTIONS.md rule 2). Only the facts without a
--  quantifier are postconditions.
--
--  Uniqueness (T5). On a frontier, each held record is canonical (D3,
--  Kome.Headers.Canonical; Kome.Frontier.Lemma_Frontier_Held). This is all
--  of the hypothesis that `cell_unique` in Lean calls `hinj` for PUT and
--  DEL. Each field that a canonical PUT or DEL uses is in its cell key or
--  its V, so two held PUTs on one cell are one record (Lemma_Cell_Unique,
--  Lemma_Del_Unique, unconditional). For ROSTER_eff, the order is Lean's
--  full roster tuple (gen, h, signer, ceiling_t, del_ttl) (Roster_Lt).
--  On a canonical roster of the collection, that tuple determines the
--  header, so ROSTER_eff does not depend on the order on a frontier,
--  without A2 (Lemma_Roster_Unique, Lemma_Roster_Eff_Unique). This is
--  exactly what Frontier.lean `rosterEff_congr` gives for the model. A2
--  (Unique_Versions) stays only as an alternative hypothesis for states
--  that are not frontiers.
--
--  Lemmas (T5, T12):
--    Lemma_<View>_Def          the definitions of the opaque views;
--    Lemma_Cell_Unique / Lemma_Del_Unique / Lemma_Roster_Unique /
--    Lemma_Roster_Eff_Unique   the maximum is unique (T5, `cell_unique`);
--    Lemma_Roster_Eff_Present  a founding roster makes ROSTER_eff present;
--    Lemma_Root_Void_Slot      root_void read through slot 1 (the founding
--                              key's row) of Kome.Frontier;
--    Lemma_Data_Local / Lemma_Cell_Local / Lemma_Views_Local
--                              the data views depend only on held PUT/DEL;
--    Lemma_Root_Void_Local / Lemma_W_Eff_Local / Lemma_Void_Local /
--    Lemma_Roster_Local / Lemma_Del_TTL_Local
--                              the authorization views depend only on held
--                              ROSTER/REVOKE/GRANT and the founding key;
--    Lemma_Apply_Auth_Local    to apply a ROSTER, REVOKE or GRANT keeps the
--                              PUT/DEL records (T12);
--    Lemma_Apply_Data_Local    to apply a PUT or DEL keeps the
--                              ROSTER/REVOKE/GRANT records;
--    Lemma_Root_Void_Monotone / Lemma_W_Eff_Monotone / Lemma_Void_Monotone /
--    Lemma_Apply_Keeps_Revokes root_void grows; for a fixed root_void set,
--                              W_eff and the REVOKE clause of void grow
--                              (T12).
pragma Ada_2022;
with Kome.Versions;  use Kome.Versions;
with Kome.Headers;   use Kome.Headers;
with Kome.Registers;
with Kome.Frontier;  use Kome.Frontier;
package Kome.Views with SPARK_Mode is

   --  The payload of an absent Header_View. It is NOT canonical, on
   --  purpose (a PUT with a non-zero issuer; Lemma_No_Header_Not_Canonical).
   --  It is never the same as a held record, because each held record is
   --  canonical (Kome.Frontier.Lemma_Frontier_Held).
   All_Ones   : constant Key256  := (others => 16#FFFF_FFFF#);
   No_Header  : constant Header  :=
     (K => K_Put, NS => Zero_Id, Ent => Zero_Id, FH => Zero_Key,
      V => (T => 0, Author => Zero_Key, Seq => 0, H => Zero_Key),
      Issuer => All_Ones, Del_TTL => 0);
   No_Version : constant Version := (others => <>);

   --  Option-like results. If Present is False, the payload is the default
   --  value, so two absent results are equal.
   type Header_View is record
      Present : Boolean := False;
      Hdr     : Header  := No_Header;
   end record;

   type Version_View is record
      Present : Boolean := False;
      V       : Version := No_Version;
   end record;

   ---------------------------------------------------------------------------
   --  Predicates on one header with no quantifier (public, so callers
   --  unfold them).
   ---------------------------------------------------------------------------

   --  A PUT on the cell (ns, ent, fh).
   function Put_On (X : Header; NS, Ent : Id128; FH : Key256) return Boolean is
     (X.K = K_Put and then X.NS = NS and then X.Ent = Ent and then X.FH = FH);

   --  A PUT on a field of the entity (ns, ent).
   function Put_In (X : Header; NS, Ent : Id128) return Boolean is
     (X.K = K_Put and then X.NS = NS and then X.Ent = Ent);

   --  A DEL of the entity (ns, ent).
   function Del_On (X : Header; NS, Ent : Id128) return Boolean is
     (X.K = K_Del and then X.NS = NS and then X.Ent = Ent);

   --  A REVOKE of Subject, by any issuer. The revoked key is V.Author of
   --  the REVOKE, and from_t is its V.T (Kome.Headers: V = (from_t,
   --  subject, rev_seq, h)). No collection test: each held record has
   --  NS = Collection (S).
   function Revokes (X : Header; Subject : Key256) return Boolean is
     (X.K = K_Revoke and then X.V.Author = Subject);

   --  A REVOKE of K issued by the key Fnd (root_void reads it with
   --  Fnd = the founding key).
   function Root_Revokes (X : Header; Fnd, K : Key256) return Boolean is
     (X.K = K_Revoke and then X.Issuer = Fnd and then X.V.Author = K);

   --  X is a REVOKE that voids P: P's author is the subject and
   --  P.t >= from_t (DESIGN.md §3 `void`). root_void decides if X's issuer
   --  counts (Revoke_Void below).
   function Voids (X, P : Header) return Boolean is
     (Revokes (X, P.V.Author) and then P.V.T >= X.V.T);

   --  A GRANT of K (V = (0, subject, 0, h)), by any issuer.
   function Grants (X : Header; K : Key256) return Boolean is
     (X.K = K_Grant and then X.V.Author = K);

   --  The ROSTER_eff order: Frontier.lean `rkLt`, lexicographic on
   --  (gen, h, signer, ceiling_t, del_ttl). The V of a roster is
   --  (ceiling_t, signer, gen, h). Its first half is Kome.Headers.Gen_Lt
   --  (the (gen, h) order of DESIGN.md §3). The rest is the tie-break of
   --  DESIGN.md §3 and T5:
   --    * only rosters that are equal in (gen, h) get to it (impossible
   --      under A2);
   --    * it makes the order strict and total on that tuple
   --      (Lemma_Roster_Lt_Total).
   --  As a result, the maximum does not depend on the held array's order.
   function Roster_Lt (A, B : Header) return Boolean is
     (Gen_Lt (A, B)
      or else (A.V.Seq = B.V.Seq and then A.V.H = B.V.H
        and then (Lt (A.V.Author, B.V.Author)
          or else (A.V.Author = B.V.Author
            and then (A.V.T < B.V.T
              or else (A.V.T = B.V.T and then A.Del_TTL < B.Del_TTL))))));

   --  far(p): an advisory flag only. The lattice never reads it (DESIGN.md
   --  §3). It does not use the sum Now + Slack, which can be more than U48.
   function Is_Far (P : Header; Now, Slack : U48) return Boolean is
     (P.V.T > Slack and then P.V.T - Slack > Now);

   ---------------------------------------------------------------------------
   --  Ghost predicates on states (quantified; defined in the private part).
   ---------------------------------------------------------------------------

   --  A2 on the held set (DESIGN.md §9 assumption A2; Frontier.lean `hinj`):
   --  two held records with the same version are the same record. h is the
   --  BLAKE2b content hash of the record, so this is true for each state
   --  built from verified records, except with negligible probability. No
   --  lemma below needs it on a frontier. It is an alternative hypothesis
   --  for the payload halves of the locality lemmas on arbitrary states.
   function Unique_Versions (S : State) return Boolean with Ghost, Global => null;

   --  S1 and S2 hold the same PUT and DEL records.
   function Same_Data (S1, S2 : State) return Boolean with Ghost, Global => null;

   --  S1 and S2 have the same founding key and hold the same ROSTER, REVOKE
   --  and GRANT records: the inputs of each authorization view.
   function Same_Auth (S1, S2 : State) return Boolean with Ghost, Global => null;

   ---------------------------------------------------------------------------
   --  The data views (T5: each is a function of the held PUT and DEL).
   ---------------------------------------------------------------------------

   --  cell(ns, ent, fh): the live PUT on the cell, if there is one. On a
   --  frontier, it is the only one (Lemma_Cell_Unique). In general, it is a
   --  maximal one.
   function Cell (S : State; NS, Ent : Id128; FH : Key256) return Header_View with
     Global => null,
     Post   => (if Cell'Result.Present then Put_On (Cell'Result.Hdr, NS, Ent, FH)
                else Cell'Result.Hdr = No_Header);

   --  deleted_at(ns, ent): the maximal DEL version on the entity, if there
   --  is one.
   function Deleted_At (S : State; NS, Ent : Id128) return Version_View with
     Global => null,
     Post   => (if not Deleted_At'Result.Present then Deleted_At'Result.V = No_Version);

   --  exists(ns, ent): a live PUT on the entity. There is no presence bit:
   --  a deleted entity is a DEL and nothing else (DESIGN.md §3).
   function Exists (S : State; NS, Ent : Id128) return Boolean with
     Global => null;

   ---------------------------------------------------------------------------
   --  The authorization views (DESIGN.md §3, §6 D2, D1′).
   ---------------------------------------------------------------------------

   --  root_void(k) (D2, as decided): only the founding key root-voids.
   --  root_void(k) is true iff k is not the founding key and F holds a
   --  REVOKE of k issued by the founding key. root_void ignores its from_t:
   --  a root-issued record has no trustworthy time, and a thief would
   --  backdate.
   --    * The founding key is never root_void. Decode refuses a REVOKE of
   --      root_pk. If F held one, it would still not root-void the key.
   --    * A REVOKE issued by a certified root never root-voids a key. If it
   --      names a different root, it only voids that key's data records.
   --    * All records that a root-voided root issued, before or after, stop
   --      to count in each view. Its rosters leave ROSTER_eff and
   --      del_ttl_eff, its REVOKEs stop voiding (Revoke_Void), and its
   --      GRANTs leave W_eff.
   --  Admission never reads root_void (T4'). In the core's two-level API,
   --  the REVOKEs that it reads are exactly the REVOKEs of slot 1
   --  (Lemma_Root_Void_Slot).
   function Root_Void (S : State; K : Key256) return Boolean with
     Global => null,
     Post   => (if Root_Void'Result then K /= Founding (S));

   --  k ∈ W_eff(F) (D1′): a held GRANT of k with an issuer that is not
   --  root_void. W (Kome.Registers, admission) counts each held GRANT. The
   --  only difference between the two is the grants of root-voided issuers.
   --  Admission must keep these grants (monotone, §4), and the views ignore
   --  them.
   function W_Eff (S : State; K : Key256) return Boolean with
     Global => null;

   --  The REVOKE clause of void(p): a held REVOKE of p's author, with
   --  from_t <= p.t and with an issuer that is not root_void.
   function Revoke_Void (S : State; P : Header) return Boolean with
     Global => null;

   --  void(p) := Revoke_Void (S, p) or else p.author ∉ W_eff (DESIGN.md §3).
   --
   --  What from_t can do (E4, DESIGN.md §6): with from_t > 0, a key's
   --  earlier records do not get the flag. This protects only a key that
   --  was LOST and that no person used. It cannot protect against a STOLEN
   --  key. A thief chooses t and can backdate below from_t, and these
   --  records look the same as honest records.
   --  Caution: for a stolen key, revoke from 0.
   --
   --  void is a view flag only. It never changes admission (T4': admission
   --  reads W and maxceil, never REVOKE, root_void or W_eff). It never
   --  changes domination (Kome.Headers.Dominates ignores it). A void PUT
   --  still frees what it dominates. A void DEL still frees each value of
   --  its entity and is still a tombstone.
   --
   --  Monotonicity (T12): for a fixed root_void set, the REVOKE clause grows
   --  with F (Lemma_Void_Monotone). The W_eff clause is ANTI-monotone (a
   --  GRANT can un-void), so void as a whole is not monotone in F.
   function Is_Void (S : State; P : Header) return Boolean with
     Global => null;

   --  A roster eligible for ROSTER_eff and del_ttl_eff: its issuer is not
   --  root_void. The founding key is never root_void, so each founding
   --  roster is eligible.
   function Eligible (S : State; X : Header) return Boolean is
     (X.K = K_Roster and then not Root_Void (S, X.Issuer));

   --  ROSTER_eff (DESIGN.md §3, §6 C9): the Roster_Lt-maximal eligible
   --  held roster, so it is also maximal in (gen, h) (Gen_Lt).
   --    * It is None if no held roster is eligible.
   --    * It is present if F holds a roster issued by the founding key
   --      (Lemma_Roster_Eff_Present).
   --    * On a frontier, it is the unique eligible roster that no eligible
   --      roster beats (Lemma_Roster_Eff_Unique).
   --  The tie-break on the full tuple, as `rkLt` in Lean, makes it
   --  independent of the held array's order. This is true in the
   --  model (`rosterEff_congr`) and here, without A2. The product order can
   --  keep a stale roster of one signer (lower gen, higher ceiling_t) next
   --  to a newer one. That stale roster never becomes ROSTER_eff.
   function Roster_Eff (S : State) return Header_View with
     Global => null,
     Post   => (if Roster_Eff'Result.Present then Eligible (S, Roster_Eff'Result.Hdr)
                else Roster_Eff'Result.Hdr = No_Header);

   --  del_ttl_eff (D10, DESIGN.md §3, §7): the largest del_ttl of the
   --  eligible held rosters, or Del_TTL_Default if there is none. It is a
   --  maximum, so a root can make tombstone life longer, but it can never
   --  make it shorter than a different root's value. When a root is
   --  root-voided, the longer life that it set stops. Kome.Store computes
   --  the expiry horizon from it. On a frontier, each held roster is
   --  canonical, so its del_ttl is in range, and this value is too.
   function Del_TTL_Eff (S : State) return U48 with
     Global => null,
     Pre    => Is_Frontier (S),
     Post   => Del_TTL_Eff'Result in Del_TTL_Min .. Del_TTL_Max;

   --  maxceil(F) and W(F) as named views (Kome.Frontier keeps its
   --  registers equal to them; Lemma_Ceil_Bound, Lemma_W_Sound, ...).
   function Max_Ceil (S : State) return U48 is (Kome.Registers.Ceil (Regs (S)));

   function Is_Writer (S : State; K : Key256) return Boolean is
     (Kome.Registers.In_W (Regs (S), K));

   ---------------------------------------------------------------------------
   --  Definitions of the opaque views.
   ---------------------------------------------------------------------------

   procedure Lemma_Cell_Def (S : State; NS, Ent : Id128; FH : Key256) with
     Ghost, Global => null,
     Post =>
       Cell (S, NS, Ent, FH).Present =
         (for some I in 1 .. Count (S) => Put_On (Held (S, I), NS, Ent, FH))
       and then
       (if Cell (S, NS, Ent, FH).Present then
          Put_On (Cell (S, NS, Ent, FH).Hdr, NS, Ent, FH)
          and then (for some I in 1 .. Count (S) => Held (S, I) = Cell (S, NS, Ent, FH).Hdr)
          and then (for all I in 1 .. Count (S) =>
                      (if Put_On (Held (S, I), NS, Ent, FH)
                       then not Lt (Cell (S, NS, Ent, FH).Hdr.V, Held (S, I).V)))
        else Cell (S, NS, Ent, FH).Hdr = No_Header);

   procedure Lemma_Deleted_At_Def (S : State; NS, Ent : Id128) with
     Ghost, Global => null,
     Post =>
       Deleted_At (S, NS, Ent).Present =
         (for some I in 1 .. Count (S) => Del_On (Held (S, I), NS, Ent))
       and then
       (if Deleted_At (S, NS, Ent).Present then
          (for some I in 1 .. Count (S) =>
             Del_On (Held (S, I), NS, Ent) and then Held (S, I).V = Deleted_At (S, NS, Ent).V)
          and then (for all I in 1 .. Count (S) =>
                      (if Del_On (Held (S, I), NS, Ent)
                       then not Lt (Deleted_At (S, NS, Ent).V, Held (S, I).V)))
        else Deleted_At (S, NS, Ent).V = No_Version);

   procedure Lemma_Exists_Def (S : State; NS, Ent : Id128) with
     Ghost, Global => null,
     Post => Exists (S, NS, Ent) =
               (for some I in 1 .. Count (S) => Put_In (Held (S, I), NS, Ent));

   procedure Lemma_Root_Void_Def (S : State; K : Key256) with
     Ghost, Global => null,
     Post => Root_Void (S, K) =
               (K /= Founding (S)
                and then (for some I in 1 .. Count (S) =>
                            Root_Revokes (Held (S, I), Founding (S), K)));

   procedure Lemma_W_Eff_Def (S : State; K : Key256) with
     Ghost, Global => null,
     Post => W_Eff (S, K) =
               (for some I in 1 .. Count (S) =>
                  Grants (Held (S, I), K)
                  and then not Root_Void (S, Held (S, I).Issuer));

   procedure Lemma_Is_Void_Def (S : State; P : Header) with
     Ghost, Global => null,
     Post => Revoke_Void (S, P) =
               (for some I in 1 .. Count (S) =>
                  Voids (Held (S, I), P)
                  and then not Root_Void (S, Held (S, I).Issuer))
             and then
             Is_Void (S, P) =
               ((for some I in 1 .. Count (S) =>
                   Voids (Held (S, I), P)
                   and then not Root_Void (S, Held (S, I).Issuer))
                or else not W_Eff (S, P.V.Author));

   procedure Lemma_Roster_Eff_Def (S : State) with
     Ghost, Global => null,
     Post =>
       Roster_Eff (S).Present =
         (for some I in 1 .. Count (S) => Eligible (S, Held (S, I)))
       and then
       (if Roster_Eff (S).Present then
          Eligible (S, Roster_Eff (S).Hdr)
          and then (for some I in 1 .. Count (S) => Held (S, I) = Roster_Eff (S).Hdr)
          and then (for all I in 1 .. Count (S) =>
                      (if Eligible (S, Held (S, I))
                       then not Roster_Lt (Roster_Eff (S).Hdr, Held (S, I))
                            and then not Gen_Lt (Roster_Eff (S).Hdr, Held (S, I))))
        else Roster_Eff (S).Hdr = No_Header);

   procedure Lemma_Del_TTL_Eff_Def (S : State) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S),
     Post =>
       (if (for some I in 1 .. Count (S) => Eligible (S, Held (S, I))) then
          (for some I in 1 .. Count (S) =>
             Eligible (S, Held (S, I)) and then Held (S, I).Del_TTL = Del_TTL_Eff (S))
          and then (for all I in 1 .. Count (S) =>
                      (if Eligible (S, Held (S, I))
                       then Held (S, I).Del_TTL <= Del_TTL_Eff (S)))
        else Del_TTL_Eff (S) = Del_TTL_Default);

   --  root_void in the core's two-level API: slot 1 is the founding key's
   --  row, so the REVOKEs that root_void reads are the REVOKEs of slot 1.
   procedure Lemma_Root_Void_Slot (S : State; K : Key256) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S),
     Post => Slots_Used (S) >= 1
             and then Root_Void (S, K) =
               (K /= Founding (S)
                and then (for some J in 1 .. Slot_Count (S, 1) =>
                            Auth_Held (S, 1, J).K = K_Revoke
                            and then Auth_Held (S, 1, J).V.Author = K));

   ---------------------------------------------------------------------------
   --  Laws: the order, the sentinel, uniqueness of the maxima (T5).
   ---------------------------------------------------------------------------

   procedure Lemma_No_Header_Not_Canonical with
     Ghost, Global => null,
     Post => not Canonical (No_Header);

   --  Roster_Lt is a strict total order on (V, Del_TTL).
   procedure Lemma_Roster_Lt_Total (A, B : Header) with
     Ghost, Global => null,
     Post => Roster_Lt (A, B)
             or else (A.V = B.V and then A.Del_TTL = B.Del_TTL)
             or else Roster_Lt (B, A);

   procedure Lemma_Roster_Lt_Irrefl (A : Header) with
     Ghost, Global => null,
     Post => not Roster_Lt (A, A);

   --  T5, Frontier.lean `cell_unique`: two held PUTs on one cell of a
   --  frontier are the same record at the same index. (If not, the newer
   --  dominates the older. Equal versions of canonical PUTs on one cell are
   --  equal records.) Unconditional: Is_Frontier makes each held record
   --  canonical.
   procedure Lemma_Cell_Unique (S : State; I, J : Held_Index) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S)
             and then I <= Count (S) and then J <= Count (S)
             and then Held (S, I).K = K_Put
             and then Put_On (Held (S, J), Held (S, I).NS, Held (S, I).Ent, Held (S, I).FH),
     Post => Held (S, I).V = Held (S, J).V
             and then Held (S, I) = Held (S, J) and then I = J;

   --  T5 for deleted_at: a frontier holds at most one DEL per entity.
   procedure Lemma_Del_Unique (S : State; I, J : Held_Index) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S)
             and then I <= Count (S) and then J <= Count (S)
             and then Held (S, I).K = K_Del
             and then Del_On (Held (S, J), Held (S, I).NS, Held (S, I).Ent),
     Post => Held (S, I).V = Held (S, J).V
             and then Held (S, I) = Held (S, J) and then I = J;

   --  T5 for ROSTER_eff: two held rosters of a frontier that are
   --  Roster_Lt-incomparable (for example two maximal eligible rosters) are
   --  the same record at the same index. No A2: the compared tuple includes
   --  del_ttl. The other fields of a canonical roster are its collection,
   --  zeros and its signer. (Under the product order, an antichain of
   --  rosters for each signer is possible. Its members are different in
   --  this tuple.)
   procedure Lemma_Roster_Unique (S : State; I, J : Held_Index) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S)
             and then I <= Count (S) and then J <= Count (S)
             and then Held (S, I).K = K_Roster and then Held (S, J).K = K_Roster
             and then not Roster_Lt (Held (S, I), Held (S, J))
             and then not Roster_Lt (Held (S, J), Held (S, I)),
     Post => Held (S, I) = Held (S, J) and then I = J;

   --  T5 for ROSTER_eff, as a characterisation: on a frontier, a held
   --  eligible roster that no held eligible roster beats IS ROSTER_eff.
   --  This is true for all orders of the held array.
   procedure Lemma_Roster_Eff_Unique (S : State; I : Held_Index) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S)
             and then I <= Count (S)
             and then Eligible (S, Held (S, I))
             and then (for all J in 1 .. Count (S) =>
                         (if Eligible (S, Held (S, J))
                          then not Roster_Lt (Held (S, I), Held (S, J)))),
     Post => Roster_Eff (S) = (Present => True, Hdr => Held (S, I));

   --  DESIGN.md §3: ROSTER_eff is present if F holds a roster issued by the
   --  founding key (the collection's first roster is one). The reason
   --  is that the founding key is never root_void.
   procedure Lemma_Roster_Eff_Present (S : State) with
     Ghost, Global => null,
     Pre  => (for some I in 1 .. Count (S) =>
                Held (S, I).K = K_Roster and then Held (S, I).Issuer = Founding (S)),
     Post => Roster_Eff (S).Present;

   --  exists(ns, ent) = ∃ f. cell(ns, ent, f) ≠ None, in the two
   --  directions. If a cell is present, the entity exists. If an entity
   --  exists, it has a present cell at the field of one of its held PUTs.
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

   --  deleted_at and exists are functions of only the held PUT and DEL
   --  records. They need no hypothesis on the records.
   procedure Lemma_Data_Local (S1, S2 : State; NS, Ent : Id128) with
     Ghost, Global => null,
     Pre  => Same_Data (S1, S2),
     Post => Deleted_At (S1, NS, Ent) = Deleted_At (S2, NS, Ent)
             and then Exists (S1, NS, Ent) = Exists (S2, NS, Ent);

   --  cell is a function of the held PUT and DEL records:
   --    * its presence and version, always;
   --    * its full header, if S1 is a frontier, or the PUTs of S1 are
   --      canonical, or S1 satisfies A2.
   --  (Same_Data carries each PUT of S2 into S1, so a hypothesis on S1
   --  only is sufficient.)
   procedure Lemma_Cell_Local (S1, S2 : State; NS, Ent : Id128; FH : Key256) with
     Ghost, Global => null,
     Pre  => Same_Data (S1, S2),
     Post => Cell (S1, NS, Ent, FH).Present = Cell (S2, NS, Ent, FH).Present
             and then Cell (S1, NS, Ent, FH).Hdr.V = Cell (S2, NS, Ent, FH).Hdr.V
             and then
             (if Is_Frontier (S1)
                 or else (for all I in 1 .. Count (S1) =>
                            (if Held (S1, I).K = K_Put then Canonical (Held (S1, I))))
                 or else Unique_Versions (S1)
              then Cell (S1, NS, Ent, FH) = Cell (S2, NS, Ent, FH));

   --  T5 / T12: the three data views together (Lemma_Data_Local and
   --  Lemma_Cell_Local).
   procedure Lemma_Views_Local (S1, S2 : State; NS, Ent : Id128; FH : Key256) with
     Ghost, Global => null,
     Pre  => Same_Data (S1, S2)
             and then
             (Is_Frontier (S1)
              or else (for all I in 1 .. Count (S1) =>
                         (if Held (S1, I).K = K_Put then Canonical (Held (S1, I))))
              or else Unique_Versions (S1)),
     Post => Cell (S1, NS, Ent, FH) = Cell (S2, NS, Ent, FH)
             and then Deleted_At (S1, NS, Ent) = Deleted_At (S2, NS, Ent)
             and then Exists (S1, NS, Ent) = Exists (S2, NS, Ent);

   --  root_void, W_eff and void are functions of the founding key and the
   --  held REVOKE and GRANT records.
   procedure Lemma_Root_Void_Local (S1, S2 : State; K : Key256) with
     Ghost, Global => null,
     Pre  => Same_Auth (S1, S2),
     Post => Root_Void (S1, K) = Root_Void (S2, K);

   procedure Lemma_W_Eff_Local (S1, S2 : State; K : Key256) with
     Ghost, Global => null,
     Pre  => Same_Auth (S1, S2),
     Post => W_Eff (S1, K) = W_Eff (S2, K);

   procedure Lemma_Void_Local (S1, S2 : State; P : Header) with
     Ghost, Global => null,
     Pre  => Same_Auth (S1, S2),
     Post => Revoke_Void (S1, P) = Revoke_Void (S2, P)
             and then Is_Void (S1, P) = Is_Void (S2, P);

   --  ROSTER_eff is a function of the founding key and the held ROSTER and
   --  REVOKE records:
   --    * its presence and its order tuple (V, del_ttl), always;
   --    * its full header, if S1 is a frontier (canonical rosters of one
   --      collection) or satisfies A2.
   procedure Lemma_Roster_Local (S1, S2 : State) with
     Ghost, Global => null,
     Pre  => Same_Auth (S1, S2),
     Post => Roster_Eff (S1).Present = Roster_Eff (S2).Present
             and then Roster_Eff (S1).Hdr.V = Roster_Eff (S2).Hdr.V
             and then Roster_Eff (S1).Hdr.Del_TTL = Roster_Eff (S2).Hdr.Del_TTL
             and then (if Is_Frontier (S1) or else Unique_Versions (S1)
                       then Roster_Eff (S1) = Roster_Eff (S2));

   --  The same for del_ttl_eff (T5).
   procedure Lemma_Del_TTL_Local (S1, S2 : State) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S1) and then Is_Frontier (S2) and then Same_Auth (S1, S2),
     Post => Del_TTL_Eff (S1) = Del_TTL_Eff (S2);

   --  T12 (revocation locality): to apply a ROSTER, REVOKE or GRANT never
   --  adds or removes a PUT or DEL. The postcondition of
   --  Kome.Frontier.Apply gives the hypotheses for Before = S'Old and
   --  After = S, for all values of Status. (On a refusal or a duplicate,
   --  Unchanged is true, so Held is the same at each index.)
   procedure Lemma_Apply_Auth_Local (Before, After : State; R : Header) with
     Ghost, Global => null,
     Pre  => Is_Auth (R)
             and then (for all I in 1 .. Count (After) =>
                         Holds (Before, Held (After, I)) or else Held (After, I) = R)
             and then (for all I in 1 .. Count (Before) =>
                         Holds (After, Held (Before, I))
                         or else Dominates (R, Held (Before, I))),
     Post => Same_Data (Before, After);

   --  The converse: to apply a PUT or a DEL never adds or removes a ROSTER,
   --  REVOKE or GRANT, so it does not change root_void, W_eff, void,
   --  ROSTER_eff or del_ttl_eff. The hypotheses are the same, plus
   --  "Founding (S) = Founding (S'Old)" from Apply.
   procedure Lemma_Apply_Data_Local (Before, After : State; R : Header) with
     Ghost, Global => null,
     Pre  => Is_Data (R)
             and then Founding (After) = Founding (Before)
             and then (for all I in 1 .. Count (After) =>
                         Holds (Before, Held (After, I)) or else Held (After, I) = R)
             and then (for all I in 1 .. Count (Before) =>
                         Holds (After, Held (Before, I))
                         or else Dominates (R, Held (Before, I))),
     Post => Same_Auth (Before, After);

   --  T12, Frontier.lean `rootVoid_mono`: root_void is monotone in F.
   procedure Lemma_Root_Void_Monotone (S1, S2 : State; K : Key256) with
     Ghost, Global => null,
     Pre  => Founding (S1) = Founding (S2)
             and then (for all I in 1 .. Count (S1) =>
                         (if Held (S1, I).K = K_Revoke then Holds (S2, Held (S1, I)))),
     Post => (if Root_Void (S1, K) then Root_Void (S2, K));

   --  T12: for a fixed root_void set, W_eff is monotone in F (so a GRANT
   --  can only un-void). The hypothesis on root_void is necessary: a new
   --  founding REVOKE of an issuer removes that issuer's grants from W_eff.
   procedure Lemma_W_Eff_Monotone (S1, S2 : State; K : Key256) with
     Ghost, Global => null,
     Pre  => (for all I in 1 .. Count (S1) =>
                (if Held (S1, I).K = K_Grant
                 then Holds (S2, Held (S1, I))
                      and then Root_Void (S1, Held (S1, I).Issuer)
                               = Root_Void (S2, Held (S1, I).Issuer))),
     Post => (if W_Eff (S1, K) then W_Eff (S2, K));

   --  T12: for a fixed root_void set, the REVOKE clause of void is monotone
   --  in F (a REVOKE can only void). The W_eff clause is anti-monotone (a
   --  GRANT can un-void, DESIGN.md T12), so this lemma is only for the
   --  REVOKE clause, Revoke_Void.
   procedure Lemma_Void_Monotone (S1, S2 : State; P : Header) with
     Ghost, Global => null,
     Pre  => (for all I in 1 .. Count (S1) =>
                (if Held (S1, I).K = K_Revoke
                 then Holds (S2, Held (S1, I))
                      and then Root_Void (S1, Held (S1, I).Issuer)
                               = Root_Void (S2, Held (S1, I).Issuer))),
     Post => (if Revoke_Void (S1, P) then Revoke_Void (S2, P));

   --  T12 (part), Frontier.lean `revoke_never_dominated`: Apply never loses
   --  a REVOKE, so with Lemma_Root_Void_Monotone, root_void only grows.
   --  The hypothesis is the "nothing lost except by domination" clause of
   --  Apply.
   procedure Lemma_Apply_Keeps_Revokes (Before, After : State; R : Header) with
     Ghost, Global => null,
     Pre  => (for all I in 1 .. Count (Before) =>
                Holds (After, Held (Before, I)) or else Dominates (R, Held (Before, I))),
     Post => (for all I in 1 .. Count (Before) =>
                (if Held (Before, I).K = K_Revoke then Holds (After, Held (Before, I))));

private

   --  The three ghost predicates. The views are completed in the body, but
   --  these are completed here. gnatprove 14 shows private-part expression
   --  functions to clients (CONVENTIONS.md, "Proof hygiene"), so a
   --  client's prover can unfold them.

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
     (Founding (S1) = Founding (S2)
      and then
      (for all I in 1 .. Count (S1) =>
         (if Is_Auth (Held (S1, I)) then Holds (S2, Held (S1, I))))
      and then
      (for all I in 1 .. Count (S2) =>
         (if Is_Auth (Held (S2, I)) then Holds (S1, Held (S2, I)))));

end Kome.Views;
