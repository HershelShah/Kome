--  Kome.Headers: the part of a record that the lattice sees, and domination
--  (DESIGN.md §2, §3; Frontier.lean `Record` and `dominates`).
--
--  A header is a record without its payload. Kome.Store keeps the payload
--  out of line: the value of a PUT, the member boxes and links of a ROSTER,
--  the signer block and the field name itself. `dom` never reads them.
--  Each function below is a pure function of header fields, so the
--  frontier is a function of the held set and of nothing else (T5).
--
--  The header is small and flat by design: one kind tag, the collection,
--  the entity, the field hash, one version, the issuer and del_ttl. Each
--  kind keeps its identity in V, so one version order serves all five kinds
--  (DESIGN.md §3 table):
--
--    PUT     V = (t, author, seq, h)            cell = (ns, ent, fh)
--    DEL     V = (t, author, seq, h)            entity = (ns, ent), FH = 0
--    ROSTER  V = (ceiling_t, signer, gen, h)    Issuer = signer, Del_TTL
--    REVOKE  V = (from_t, subject, rev_seq, h)  Issuer = signer
--    GRANT   V = (0, subject, 0, h)             Issuer = signer
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
      NS      : Id128;
      Ent     : Id128;                 --  PUT, DEL
      FH      : Key256;                --  PUT: BLAKE2b-256 of the field name
      V       : Version;
      Issuer  : Key256;                --  ROSTER, REVOKE, GRANT: the signer
      Del_TTL : U48    := 0;           --  ROSTER: del_ttl (milliseconds)
   end record;

   function Is_Data (R : Header) return Boolean is (R.K in K_Put | K_Del);

   --  ROSTER, REVOKE and GRANT: the records that a signer's slice holds
   --  (§7).
   function Is_Auth (R : Header) return Boolean is (not Is_Data (R));

   --  The roster generation order (DESIGN.md §3, §6) is (gen, h). The V of a
   --  roster is (ceiling_t, signer, gen, h). This order is the (gen, h) half
   --  of roster domination, and it is the order of ROSTER_eff.
   function Gen_Lt (A, B : Header) return Boolean is
     (A.V.Seq < B.V.Seq
      or else (A.V.Seq = B.V.Seq and then Lt (A.V.H, B.V.H)));

   --  Dominates (Q, P): Q beats P (DESIGN.md §3, the witness of `dom`).
   --  For each kind of P, this table gives the records Q that beat P:
   --    PUT     a newer PUT on the same cell, or a newer DEL of its entity
   --    DEL     a newer DEL of the same entity
   --    ROSTER  a roster of the same signer that is greater in (gen, h)
   --            and not lower in ceiling_t: the product order (D3)
   --    GRANT   a GRANT of the same issuer and subject with a greater h
   --            (D1′; keyed by (ns, issuer, subject))
   --    REVOKE  no record (so a REVOKE can never be lost)
   --  Collections never mix: a record only dominates in its own ns. Each
   --  clause implies that the dominator's version is greater. The
   --  expression has no quantifier, so it can be public at no proof cost to
   --  other units.
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

   --  The ceiling that a record carries: ROSTER.ceiling_t (its V.T), else
   --  nothing (0 adds nothing to a max-register). Frontier.lean `ceilOf`.
   function Ceil_Of (R : Header) return U48 is
     (if R.K = K_Roster then R.V.T else 0);

   function Data_T (R : Header) return U48 is (R.V.T);

   function Data_Author (R : Header) return Key256 is (R.V.Author);

   --  The canonical header (D3, DESIGN.md §3): the fields that a kind does
   --  not use are zero. The issuer of a roster is its signer, and its
   --  del_ttl is in range. The V of a grant is (0, subject, 0, h).
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

   --  True if X is a tombstone that is expired at Horizon (DESIGN.md §7 drop
   --  rule, second clause). With No_Horizon (-1), no record is expired.
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
   --  a dominator is a dominator. The frontier homomorphism depends on this
   --  lemma. This lemma is also the reason that REVOKE must not dominate a
   --  record.
   procedure Lemma_Dominates_Trans (X, Y, Z : Header) with
     Ghost, Global => null,
     Pre  => Dominates (Y, X) and then Dominates (Z, Y),
     Post => Dominates (Z, X);

   --  T12 (part), Frontier.lean `revoke_never_dominated`.
   procedure Lemma_Revoke_Never_Dominated (Q, X : Header) with
     Ghost, Global => null,
     Pre  => X.K = K_Revoke,
     Post => not Dominates (Q, X);

   --  Roster domination is the product order (D3): the other conjuncts imply
   --  the version conjunct.
   procedure Lemma_Roster_Dom (P, Q : Header) with
     Ghost, Global => null,
     Pre  => P.K = K_Roster and then Q.K = K_Roster and then P.NS = Q.NS,
     Post => Dominates (Q, P)
             = (Q.V.Author = P.V.Author and then P.V.T <= Q.V.T
                and then Gen_Lt (P, Q));

   --  Grant domination uses the key (ns, issuer, subject) and the order of h
   --  (D1′).
   procedure Lemma_Grant_Dom (P, Q : Header) with
     Ghost, Global => null,
     Pre  => P.K = K_Grant and then Q.K = K_Grant
             and then Canonical (P) and then Canonical (Q)
             and then P.NS = Q.NS,
     Post => Dominates (Q, P)
             = (Q.V.Author = P.V.Author and then Q.Issuer = P.Issuer
                and then Lt (P.V.H, Q.V.H));

   --  T4' (registers lose nothing to domination, DESIGN.md §3): a dominator
   --  has the same kind class as the record that it dominates. The dominator
   --  of a roster is a roster of the same signer, with a ceiling at least
   --  equal to its own. The dominator of a grant is a grant of the same
   --  issuer and subject.
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
