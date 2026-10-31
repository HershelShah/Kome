--  Kome.Headers: the part of a record the lattice sees, and domination
--  (DESIGN.md §2, §3; Frontier.lean `Record` and `dominates`).
--
--  A header is a record without its payload: the value of a PUT, the member
--  boxes of a ROSTER and the field name itself are stored out of line
--  (Kome.Store) and never consulted by `dom`. Everything below is a pure
--  function of header fields, so the frontier is a function of the held set
--  and nothing else (T5).
--
--  The header is small and flat on purpose: one kind tag, the collection,
--  the entity, the field hash, one version, one ceiling. Every kind carries
--  its identity in V so that one version order serves all four kinds:
--
--    PUT     V = (t, author, seq, h)      cell = (ns, ent, fh)
--    DEL     V = (t, author, seq, h)      entity = (ns, ent)
--    ROSTER  V = (0, signer, gen, h)      dominated per signer by (gen, h)
--    REVOKE  V = (from_t, subject, rev_seq, h)   never dominated
--
--  Fields a kind does not use are canonically zero (Kome.Records enforces
--  it), so record equality is content equality.
pragma Ada_2022;
with Kome.Versions; use Kome.Versions;
package Kome.Headers with SPARK_Mode, Pure is

   --  Kinds in reconciliation key order (DESIGN.md §8): authorization
   --  records sort first.
   type Kind is (K_Roster, K_Revoke, K_Del, K_Put);
   for Kind use (K_Roster => 0, K_Revoke => 1, K_Del => 2, K_Put => 3);

   type Header is record
      K       : Kind   := K_Put;
      NS      : Id128;
      Ent     : Id128;                 --  PUT, DEL
      FH      : Key256;                --  PUT: BLAKE2b-256 of the field name
      V       : Version;
      Ceiling : U48    := 0;           --  ROSTER: ceiling_t
   end record;

   --  Dominates (Q, P): Q beats P (DESIGN.md §3, `dom`'s witness).
   --    PUT     beaten by a newer PUT on the same cell or a newer DEL of its entity
   --    DEL     beaten by a newer DEL of the same entity
   --    ROSTER  beaten by a roster of the same signer with greater (gen, h)
   --    REVOKE  never beaten (so it can never be lost)
   --  Collections never mix: a record only dominates within its own ns.
   --  Quantifier-free, so it can be public without burdening other units.
   function Dominates (Q, P : Header) return Boolean is
     (Q.NS = P.NS
      and then Lt (P.V, Q.V)
      and then
      (case P.K is
         when K_Put    => (Q.K = K_Put and then Q.Ent = P.Ent and then Q.FH = P.FH)
                          or else (Q.K = K_Del and then Q.Ent = P.Ent),
         when K_Del    => Q.K = K_Del and then Q.Ent = P.Ent,
         when K_Roster => Q.K = K_Roster and then Q.V.Author = P.V.Author,
         when K_Revoke => False));

   --  The ceiling a record carries: ROSTER.ceiling_t, else nothing (0 adds
   --  nothing to a max-register). Frontier.lean `ceilOf`.
   function Ceil_Of (R : Header) return U48 is
     (if R.K = K_Roster then R.Ceiling else 0);

   function Is_Data (R : Header) return Boolean is (R.K in K_Put | K_Del);

   function Data_T (R : Header) return U48 is (R.V.T);

   function Data_Author (R : Header) return Key256 is (R.V.Author);

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

end Kome.Headers;
