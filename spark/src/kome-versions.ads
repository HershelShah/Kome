--  Kome.Versions: the version tuple and its strict total order (DESIGN.md §2,
--  T1). Refines lean/Kome/Frontier.lean `Version` and `Version.lt`.
--
--    v = (t : u48, author : [32]u8, seq : u48, h : [32]u8)
--
--  compared lexicographically, with `author` and `h` as unsigned 256-bit
--  integers. `h` is the record's own content hash, so two distinct
--  well-formed records never compare equal (A2) and the order is total by
--  construction. Keys are Key256 words, so the whole order is a quantifier-
--  free formula and every lemma below is proved by unfolding.
pragma Ada_2022;
package Kome.Versions with SPARK_Mode, Pure is

   type Version is record
      T      : U48    := 0;
      Author : Key256;
      Seq    : U48    := 0;
      H      : Key256;
   end record;

   function Lt (A, B : Version) return Boolean is
     (A.T < B.T
      or else (A.T = B.T
        and then (Lt (A.Author, B.Author)
          or else (A.Author = B.Author
            and then (A.Seq < B.Seq
              or else (A.Seq = B.Seq and then Lt (A.H, B.H)))))));

   function "<" (A, B : Version) return Boolean renames Lt;

   --  T1: strict total order. Each is a theorem of Frontier.lean.

   procedure Lemma_Lt_Irrefl (A : Version) with
     Ghost, Global => null,
     Post => not Lt (A, A);

   procedure Lemma_Lt_Asym (A, B : Version) with
     Ghost, Global => null,
     Pre  => Lt (A, B),
     Post => not Lt (B, A);

   procedure Lemma_Lt_Trans (A, B, C : Version) with
     Ghost, Global => null,
     Pre  => Lt (A, B) and then Lt (B, C),
     Post => Lt (A, C);

   procedure Lemma_Trichotomy (A, B : Version) with
     Ghost, Global => null,
     Post => Lt (A, B) or else A = B or else Lt (B, A);

   --  D8: the write path picks (t, seq) before it knows h (h hashes content
   --  that includes t and seq). Two versions that differ in their prefix
   --  (t, author, seq) are ordered by that prefix alone, whatever their h.
   function Same_Prefix (A, B : Version) return Boolean is
     (A.T = B.T and then A.Author = B.Author and then A.Seq = B.Seq);

   function Prefix_Lt (A, B : Version) return Boolean is
     (A.T < B.T
      or else (A.T = B.T
        and then (Lt (A.Author, B.Author)
          or else (A.Author = B.Author and then A.Seq < B.Seq))));

   --  Frontier.lean `lt_iff_prefix`.
   procedure Lemma_Prefix_Decides (A, B : Version) with
     Ghost, Global => null,
     Pre  => not Same_Prefix (A, B),
     Post => Lt (A, B) = Prefix_Lt (A, B) and then Lt (B, A) = Prefix_Lt (B, A);

end Kome.Versions;
