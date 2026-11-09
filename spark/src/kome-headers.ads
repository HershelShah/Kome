--  Kome.Headers: the part of a record that the lattice sees, and domination
--  (DESIGN.md §2, §3; Frontier.lean `Record` and `dominates`).
--
--  A header is a record without its payload. Kome.Store keeps the payload
--  out of line: the value of a PUT, the member boxes of a ROSTER, the
--  signer block and the field name itself. `dom` never reads them. Each
--  function below is a pure function of header fields, so the frontier is
--  a function of the held set and of nothing else (T5).
--
--  The header is small and flat by design: one kind tag, the entity, the
--  field hash, one version and the issuer (SIMPLIFY.md S22). A replica
--  holds one collection, so no header carries its ns: the collection is
--  the cid that verified the record (Kome.Records), not a field. Each
--  kind keeps its identity in V, so one version order serves all five
--  kinds (DESIGN.md §3 table):
--
--    PUT     V = (t, author, seq, h)            cell = (ent, fh)
--    DEL     V = (t, author, seq, h)            entity = ent, FH = 0
--    ROSTER  V = (ceiling_t, signer, gen, h)    Issuer = signer
--    REVOKE  V = (from_t, subject, 0, h)        Issuer = signer
--    GRANT   V = (cap, subject, 0, h)           Issuer = signer; cap is the
--                                               issuer's cert_cap
--
--  If a kind does not use a field, that field is zero. This is the
--  canonical header (D3). Decode makes it (Kome.Records), and the lattice
--  requires it (the precondition of Kome.Frontier.Apply). This makes
--  record equality content equality.
pragma Ada_2022;
with Kome.Versions; use Kome.Versions;
package Kome.Headers with SPARK_Mode, Pure is

   --  Kinds in reconciliation key order (DESIGN.md §8): authorization
   --  records sort first. Kind'Pos is the wire tag (DESIGN.md §2).
   --  Kome.Reconcile depends on this.
   type Kind is (K_Roster, K_Revoke, K_Grant, K_Del, K_Put);
   for Kind use (K_Roster => 0, K_Revoke => 1, K_Grant => 2, K_Del => 3, K_Put => 4);

   Zero_Id  : constant Id128  := (others => 0);
   Zero_Key : constant Key256 := (others => 0);

   type Header is record
      K       : Kind   := K_Put;
      Ent     : Id128;                 --  PUT, DEL
      FH      : Key256;                --  PUT: BLAKE2b-256 of the field name
      V       : Version;
      Issuer  : Key256;                --  ROSTER, REVOKE, GRANT: the signer
   end record;

   function Is_Data (R : Header) return Boolean is (R.K in K_Put | K_Del);

   --  ROSTER, REVOKE and GRANT: the records that a signer's slice holds
   --  (§7).
   function Is_Auth (R : Header) return Boolean is (not Is_Data (R));

   --  The (gen, h) order of rosters (DESIGN.md §3, §6; SIMPLIFY.md S4).
   --  The V of a roster is (ceiling_t, signer, gen, h). Kome.Views orders
   --  ROSTER_eff and the quarantine by this order. Domination (below) does
   --  not use it: a roster dominates only with a strictly greater gen, so
   --  h never decides between two rosters of one signer (AUDIT.md H1).
   function Gen_Lt (A, B : Header) return Boolean is
     (A.V.Seq < B.V.Seq
      or else (A.V.Seq = B.V.Seq and then Lt (A.V.H, B.V.H)));

   --  The REVOKE order of one (issuer, subject) key (SIMPLIFY.md S5): a
   --  lower from_t is greater, and an equal from_t is decided by h. So of
   --  the REVOKEs of one key, the frontier keeps exactly the one with the
   --  least from_t (and, among those, the greatest h).
   function Revoke_Lt (P, Q : Header) return Boolean is
     (Q.V.T < P.V.T or else (Q.V.T = P.V.T and then Lt (P.V.H, Q.V.H)));

   --  Dominates (Q, P): Q beats P (DESIGN.md §3, the witness of `dom`).
   --  For each kind of P, this table gives the records Q that beat P:
   --    PUT     a newer PUT on the same cell, or a newer DEL of its entity
   --    DEL     a newer DEL of the same entity
   --    ROSTER  a roster of the same signer with a strictly greater gen,
   --            and not lower in ceiling_t: the product order (D3). Two
   --            rosters of one signer at equal gen are both held
   --            (Kome.Views.Contested reports this).
   --    GRANT   a GRANT of the same issuer and subject with a greater h
   --            and a cap at least as large: the product order (D1′; keyed
   --            by (issuer, subject)). So wcap, the largest cap of a
   --            subject's held GRANTs, never shrinks (T4').
   --    REVOKE  a REVOKE of the same (issuer, subject) with a lower
   --            from_t, or an equal from_t and a greater h (SIMPLIFY.md
   --            S5, Revoke_Lt). The least from_t of a key is never lost,
   --            so void, revoked and root_void do not change.
   --  No REVOKE dominates a record of another kind, and no record of
   --  another kind dominates a REVOKE (T2′). A data clause implies that
   --  the dominator's version is greater; the authorization clauses imply
   --  the same issuer. The expression has no quantifier, so it can be
   --  public at no proof cost to other units.
   function Dominates (Q, P : Header) return Boolean is
     (case P.K is
        when K_Put    => Lt (P.V, Q.V)
                         and then ((Q.K = K_Put and then Q.Ent = P.Ent and then Q.FH = P.FH)
                                   or else (Q.K = K_Del and then Q.Ent = P.Ent)),
        when K_Del    => Lt (P.V, Q.V) and then Q.K = K_Del and then Q.Ent = P.Ent,
        when K_Roster => Q.K = K_Roster and then Q.V.Author = P.V.Author
                         and then P.V.T <= Q.V.T and then P.V.Seq < Q.V.Seq,
        when K_Grant  => Q.K = K_Grant and then Q.V.Author = P.V.Author
                         and then Q.Issuer = P.Issuer
                         and then P.V.T <= Q.V.T and then Lt (P.V.H, Q.V.H),
        when K_Revoke => Q.K = K_Revoke and then Q.Issuer = P.Issuer
                         and then Q.V.Author = P.V.Author
                         and then Revoke_Lt (P, Q));

   --  The ceiling that a record carries: ROSTER.ceiling_t (its V.T), else
   --  nothing (0 adds nothing to a maximum). Frontier.lean `ceilOf`.
   function Ceil_Of (R : Header) return U48 is
     (if R.K = K_Roster then R.V.T else 0);

   --  The write cap that a GRANT carries (its V.T), else 0. wcap(F, k) is
   --  the largest Cap_Of over the held GRANTs of subject k (DESIGN.md §3,
   --  §4; Frontier.lean `capOf`, `wcap`).
   function Cap_Of (R : Header) return U48 is
     (if R.K = K_Grant then R.V.T else 0);

   function Data_T (R : Header) return U48 is (R.V.T);

   function Data_Author (R : Header) return Key256 is (R.V.Author);

   --  The canonical header (D3, DESIGN.md §3): the fields that a kind does
   --  not use are zero. The issuer of a roster is its signer, and its gen
   --  is at most its ceiling_t (DESIGN.md §2 rule 3; AUDIT.md H7: a
   --  certified root's gen is then bounded by its cap). The V of a grant
   --  is (cap, subject, 0, h).
   function Canonical (X : Header) return Boolean is
     (case X.K is
        when K_Put    => X.Issuer = Zero_Key,
        when K_Del    => X.FH = Zero_Key and then X.Issuer = Zero_Key,
        when K_Roster => X.Ent = Zero_Id and then X.FH = Zero_Key
                         and then X.Issuer = X.V.Author
                         and then X.V.Seq <= X.V.T,
        when K_Revoke => X.Ent = Zero_Id and then X.FH = Zero_Key,
        when K_Grant  => X.Ent = Zero_Id and then X.FH = Zero_Key
                         and then X.V.Seq = 0);

   --  True if X is a tombstone that is expired at the horizon Hz
   --  (DESIGN.md §7 drop rule, second clause; SIMPLIFY.md S7). The store
   --  computes Hz = Max_Ceil (F) - del_ttl, and has no horizon (expires
   --  nothing) while Max_Ceil (F) < del_ttl.
   function Expired (X : Header; Hz : U48) return Boolean is
     (X.K = K_Del and then X.V.T <= Hz);

   --  Gen_Lt is a strict total order up to equal (gen, h).
   procedure Lemma_Gen_Lt_Total (A, B : Header) with
     Ghost, Global => null,
     Post => Gen_Lt (A, B)
             or else (A.V.Seq = B.V.Seq and then A.V.H = B.V.H)
             or else Gen_Lt (B, A);

   procedure Lemma_Gen_Lt_Irrefl (A : Header) with
     Ghost, Global => null,
     Post => not Gen_Lt (A, A);

   procedure Lemma_Gen_Lt_Trans (A, B, C : Header) with
     Ghost, Global => null,
     Pre  => Gen_Lt (A, B) and then Gen_Lt (B, C),
     Post => Gen_Lt (A, C);

   --  Frontier.lean `dominates_irrefl`.
   procedure Lemma_Dominates_Irrefl (X : Header) with
     Ghost, Global => null,
     Post => not Dominates (X, X);

   --  T2' (upward closure), Frontier.lean `dominates_trans`: a dominator of
   --  a dominator is a dominator. The frontier homomorphism depends on this
   --  lemma. It is also the reason that a REVOKE must dominate only
   --  REVOKEs of its own key.
   procedure Lemma_Dominates_Trans (X, Y, Z : Header) with
     Ghost, Global => null,
     Pre  => Dominates (Y, X) and then Dominates (Z, Y),
     Post => Dominates (Z, X);

   --  T12 (part), Frontier.lean `dominates_revoke` (SIMPLIFY.md S5):
   --  only a
   --  REVOKE of the same (issuer, subject) dominates a REVOKE, with a
   --  lower from_t or an equal from_t and a greater h.
   procedure Lemma_Revoke_Dom (P, Q : Header) with
     Ghost, Global => null,
     Pre  => P.K = K_Revoke,
     Post => Dominates (Q, P)
             = (Q.K = K_Revoke and then Q.Issuer = P.Issuer
                and then Q.V.Author = P.V.Author
                and then (Q.V.T < P.V.T
                          or else (Q.V.T = P.V.T and then Lt (P.V.H, Q.V.H))));

   --  T2′, Frontier.lean `revoke_dominates`: a REVOKE
   --  dominates no record of another kind (in particular no data record).
   procedure Lemma_Revoke_Dominates_Only_Revokes (Q, P : Header) with
     Ghost, Global => null,
     Pre  => Q.K = K_Revoke and then Dominates (Q, P),
     Post => P.K = K_Revoke;

   --  Roster domination is the product order (D3) on (ceiling_t, gen):
   --  the other conjuncts imply that the dominator's version is greater.
   --  It is strict in gen, so two rosters of one signer at equal gen never
   --  dominate each other (AUDIT.md H1).
   procedure Lemma_Roster_Dom (P, Q : Header) with
     Ghost, Global => null,
     Pre  => P.K = K_Roster and then Q.K = K_Roster,
     Post => Dominates (Q, P)
             = (Q.V.Author = P.V.Author and then P.V.T <= Q.V.T
                and then P.V.Seq < Q.V.Seq)
             and then (if Dominates (Q, P) then Lt (P.V, Q.V));

   --  Two rosters of one signer at equal gen never dominate each other
   --  (Frontier.lean `roster_same_gen`).
   procedure Lemma_Equal_Gen_No_Dom (P, Q : Header) with
     Ghost, Global => null,
     Pre  => P.K = K_Roster and then Q.K = K_Roster
             and then P.V.Author = Q.V.Author and then P.V.Seq = Q.V.Seq,
     Post => not Dominates (Q, P) and then not Dominates (P, Q);

   --  Grant domination uses the key (issuer, subject) and the product
   --  order of (cap, h) (D1′, AUDIT.md A1).
   procedure Lemma_Grant_Dom (P, Q : Header) with
     Ghost, Global => null,
     Pre  => P.K = K_Grant and then Q.K = K_Grant
             and then Canonical (P) and then Canonical (Q),
     Post => Dominates (Q, P)
             = (Q.V.Author = P.V.Author and then Q.Issuer = P.Issuer
                and then P.V.T <= Q.V.T and then Lt (P.V.H, Q.V.H))
             and then (if Dominates (Q, P) then Lt (P.V, Q.V));

   --  T4' (the admission views lose nothing to domination, DESIGN.md §3):
   --  a dominator has the same kind class as the record that it
   --  dominates. The dominator of a roster is a roster of the same signer,
   --  with a ceiling at least equal to its own. The dominator of a grant
   --  is a grant of the same issuer and subject, with a cap at least equal
   --  to its own. The dominator of a REVOKE is a REVOKE of the same
   --  issuer and subject with a from_t at most its own.
   procedure Lemma_Dominator_Keeps_Registers (Q, P : Header) with
     Ghost, Global => null,
     Pre  => Dominates (Q, P),
     Post => (if Is_Auth (P) then Q.K = P.K)
             and then (if Is_Data (P) then Is_Data (Q))
             and then (if P.K = K_Roster
                       then Ceil_Of (Q) >= Ceil_Of (P)
                            and then Q.V.Author = P.V.Author)
             and then (if P.K = K_Grant
                       then Q.V.Author = P.V.Author
                            and then Q.Issuer = P.Issuer
                            and then Cap_Of (Q) >= Cap_Of (P))
             and then (if P.K = K_Revoke
                       then Q.V.Author = P.V.Author
                            and then Q.Issuer = P.Issuer
                            and then Q.V.T <= P.V.T);

   --  Each dominator stays in the same capacity row as the record that it
   --  dominates (DESIGN.md §3, §7). Only data dominates data. Only an
   --  authorization record of the same issuer dominates an authorization
   --  record. The rows of Kome.Frontier depend on this.
   procedure Lemma_Same_Row (Q, P : Header) with
     Ghost, Global => null,
     Pre  => Dominates (Q, P) and then Canonical (P) and then Canonical (Q),
     Post => Is_Data (Q) = Is_Data (P)
             and then (if Is_Auth (P) then Q.Issuer = P.Issuer);

end Kome.Headers;
