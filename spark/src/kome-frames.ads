--  Kome.Frames: one opaque fact about a frame of the log, "Frame is the
--  record X of the collection Cid" (Frame_Is), for the proof of
--  Kome.Store (SIMPLIFY.md S14).
--
--  Kome.Store's invariant says that the tag of every held record points
--  at an APPLY entry whose frame has that record as its header. Stated
--  with Kome.Store.Header_Of directly, every goal about tags unfolds the
--  Kome.Records parsers and the content hash of two frames (the old and
--  the new place of the bytes) and times out, though the tag lemmas only
--  move bytes. Frame_Is is completed in the body of this package, so it
--  is opaque in every other unit (CONVENTIONS.md: "to hide an expression
--  function, complete it in the body"). Kome.Store reads it with the two
--  lemmas below: Lemma_Frame_Is_Def where the header is needed (the
--  boundary of a public contract), Lemma_Frame_Is_Congruent where bytes
--  move (an append, Compact, Read_Frame). Frame_Is is executable, so the
--  test main evaluates it; Kome.Store uses it in ghost code only.
pragma Ada_2022;
with Kome.Headers; use Kome.Headers;
with Kome.Store;
package Kome.Frames with SPARK_Mode is

   function Frame_Is (Frame : Byte_Array; Cid : Hash256; X : Header) return Boolean
   with Global => null;

   procedure Lemma_Frame_Is_Def (Frame : Byte_Array; Cid : Hash256; X : Header) with
     Ghost, Global => null,
     Post => Frame_Is (Frame, Cid, X)
             = (Kome.Store.Is_Record_Frame (Frame)
                and then Kome.Store.Header_Of (Cid, Frame) = X);

   --  Two byte strings with the same elements hold the same record
   --  (Kome.Store.Lemma_Header_Of_Congruent).
   procedure Lemma_Frame_Is_Congruent (Cid : Hash256; X : Header; A, B : Byte_Array) with
     Ghost, Global => null,
     Pre  => Frame_Is (A, Cid, X)
             and then A'Length = B'Length
             and then (for all J in A'Range => B (J - A'First + B'First) = A (J)),
     Post => Frame_Is (B, Cid, X);

end Kome.Frames;
