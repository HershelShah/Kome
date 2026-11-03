--  Kome.Headers: the part of a record the lattice sees, and domination
--  (DESIGN.md §2, §3; Frontier.lean `Record` and `dominates`).
--
--  A header is a record without its payload: the value of a PUT, the member
--  boxes and links of a ROSTER, the signer block and the field name itself
--  are stored out of line (Kome.Store) and never consulted by `dom`.
--  Everything below is a pure function of header fields, so the frontier is
--  a function of the held set and nothing else (T5).
--
--  The header is small and flat on purpose: one kind tag, the collection,
--  the entity, the field hash, one version, the issuer and del_ttl. Every
--  kind carries its identity in V, so one version order serves all five
--  kinds (DESIGN.md §3 table):
--
--    PUT     V = (t, author, seq, h)            cell = (ns, ent, fh)
--    DEL     V = (t, author, seq, h)            entity = (ns, ent), FH = 0
--    ROSTER  V = (ceiling_t, signer, gen, h)    Issuer = signer, Del_TTL
--    REVOKE  V = (from_t, subject, rev_seq, h)  Issuer = signer
--    GRANT   V = (0, subject, 0, h)             Issuer = signer
--
--  Fields a kind does not use are zero: that is the canonical header (D3),
--  which decode produces (Kome.Records) and the lattice requires
--  (Kome.Frontier.Apply's precondition), so record equality is content
--  equality.
pragma Ada_2022;
with Kome.Versions; use Kome.Versions;
package Kome.Headers with SPARK_Mode, Pure is

   --  Kinds in reconciliation key order (DESIGN.md §8): authorization
   --  records sort first. Kind'Pos is the wire tag (DESIGN.md §2), and
   --  Kome.Reconcile relies on that.
   type Kind is (K_Roster, K_Revoke, K_Grant, K_Del, K_Put);
   for Kind use (K_Roster => 0, K_Revoke => 1, K_Grant => 2, K_Del => 3, K_Put => 4);

   Zero_Id  : constant Id128  := (others => 0);
   Zero_Key : constant Key256 := (others => 0);

   type Header is record
      K       : Kind   := K_Put;
      NS      : Id128;
      Ent     : Id128;                 --  PUT, DEL
      FH      : Key256;                --  PUT: BLAKE2b-256 of the field name
      V       : Version;
      Issuer  : Key256;                --  ROSTER, REVOKE, GRANT: the signer
      Del_TTL : U48    := 0;           --  ROSTER: del_ttl (milliseconds)
   end record;

   function Is_Data (R : Header) return Boolean is (R.K in K_Put | K_Del);

   --  ROSTER, REVOKE and GRANT: the records a signer's slice holds (§7).
   function Is_Auth (R : Header) return Boolean is (not Is_Data (R));

   --  The roster generation order (DESIGN.md §3, §6): (gen, h), with a
   --  roster's V = (ceiling_t, signer, gen, h). It is the (gen, h) half of
   --  roster domination and the order of ROSTER_eff.
   function Gen_Lt (A, B : Header) return Boolean is
     (A.V.Seq < B.V.Seq
      or else (A.V.Seq = B.V.Seq and then Lt (A.V.H, B.V.H)));

   --  Dominates (Q, P): Q beats P (DESIGN.md §3, `dom`'s witness).
   --    PUT     beaten by a newer PUT on the same cell or a newer DEL of its entity
   --    DEL     beaten by a newer DEL of the same entity
   --    ROSTER  beaten by a roster of the same signer that is greater in
   --            (gen, h) and not lower in ceiling_t: the product order (R4)
   --    GRANT   beaten by a GRANT of the same issuer and subject with a
   --            greater h (R1; keyed by (ns, issuer, subject))
   --    REVOKE  never beaten (so it can never be lost)
   --  Collections never mix: a record only dominates within its own ns, and
   --  every clause implies that the dominator's version is greater.
   --  Quantifier-free, so it can be public without burdening other units.
   function Dominates (Q, P : Header) return Boolean is
     (Q.NS = P.NS
      and then Lt (P.V, Q.V)
      and then
      (case P.K is
         when K_Put    => (Q.K = K_Put and then Q.Ent = P.Ent and then Q.FH = P.FH)
                          or else (Q.K = K_Del and then Q.Ent = P.Ent),
         when K_Del    => Q.K = K_Del and then Q.Ent = P.Ent,
         when K_Roster => Q.K = K_Roster and then Q.V.Author = P.V.Author
                          and then P.V.T <= Q.V.T and then Gen_Lt (P, Q),
         when K_Grant  => Q.K = K_Grant and then Q.V.Author = P.V.Author
                          and then Q.Issuer = P.Issuer,
         when K_Revoke => False));

   --  The ceiling a record carries: ROSTER.ceiling_t (its V.T), else nothing
   --  (0 adds nothing to a max-register). Frontier.lean `ceilOf`.
   function Ceil_Of (R : Header) return U48 is
     (if R.K = K_Roster then R.V.T else 0);

   function Data_T (R : Header) return U48 is (R.V.T);

   function Data_Author (R : Header) return Key256 is (R.V.Author);

   --  The canonical header (D3, DESIGN.md §3): the fields a kind does not
   --  use are zero, a roster's issuer is its signer and its del_ttl is in
   --  range, a grant's V is (0, subject, 0, h).
   function Canonical (X : Header) return Boolean is
     (case X.K is
        when K_Put    => X.Issuer = Zero_Key and then X.Del_TTL = 0,
        when K_Del    => X.FH = Zero_Key and then X.Issuer = Zero_Key
                         and then X.Del_TTL = 0,
        when K_Roster => X.Ent = Zero_Id and then X.FH = Zero_Key
                         and then X.Issuer = X.V.Author
                         and then X.Del_TTL in Del_TTL_Min .. Del_TTL_Max,
        when K_Revoke => X.Ent = Zero_Id and then X.FH = Zero_Key
                         and then X.Del_TTL = 0,
        when K_Grant  => X.Ent = Zero_Id and then X.FH = Zero_Key
                         and then X.V.T = 0 and then X.V.Seq = 0
                         and then X.Del_TTL = 0);

   --  A tombstone expired at Horizon (DESIGN.md §7 drop rule, second
   --  clause). With No_Horizon (-1) nothing is expired.
   function Expired (X : Header; Horizon : Time64) return Boolean is
     (X.K = K_Del and then Time64 (X.V.T) <= Horizon);

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
   --  a dominator is a dominator. The frontier homomorphism rests on this,
   --  and it is why REVOKE must not dominate anything.
   procedure Lemma_Dominates_Trans (X, Y, Z : Header) with
     Ghost, Global => null,
     Pre  => Dominates (Y, X) and then Dominates (Z, Y),
     Post => Dominates (Z, X);

   --  T12 (part), Frontier.lean `revoke_never_dominated`.
   procedure Lemma_Revoke_Never_Dominated (Q, X : Header) with
     Ghost, Global => null,
     Pre  => X.K = K_Revoke,
     Post => not Dominates (Q, X);

   --  Roster domination is the product order (R4): the version conjunct is
   --  implied by the others.
   procedure Lemma_Roster_Dom (P, Q : Header) with
     Ghost, Global => null,
     Pre  => P.K = K_Roster and then Q.K = K_Roster and then P.NS = Q.NS,
     Post => Dominates (Q, P)
             = (Q.V.Author = P.V.Author and then P.V.T <= Q.V.T
                and then Gen_Lt (P, Q));

   --  Grant domination is keyed by (ns, issuer, subject) and ordered by h
   --  (R1).
   procedure Lemma_Grant_Dom (P, Q : Header) with
     Ghost, Global => null,
     Pre  => P.K = K_Grant and then Q.K = K_Grant
             and then Canonical (P) and then Canonical (Q)
             and then P.NS = Q.NS,
     Post => Dominates (Q, P)
             = (Q.V.Author = P.V.Author and then Q.Issuer = P.Issuer
                and then Lt (P.V.H, Q.V.H));

   --  T4' (registers lose nothing to domination, DESIGN.md §3): a dominator
   --  has the dominated record's kind class; a roster's dominator is a roster
   --  of the same signer with a ceiling at least its own; a grant's is a
   --  grant of the same issuer and subject.
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
                            and then Q.Issuer = P.Issuer);

   --  Every dominator stays in the same capacity row as what it dominates
   --  (DESIGN.md §3, §7): data only by data, an authorization record only
   --  by one of the same issuer. Kome.Frontier's rows rely on this.
   procedure Lemma_Same_Row (Q, P : Header) with
     Ghost, Global => null,
     Pre  => Dominates (Q, P) and then Canonical (P) and then Canonical (Q),
     Post => Is_Data (Q) = Is_Data (P)
             and then (if Is_Auth (P) then Q.Issuer = P.Issuer);

end Kome.Headers;
