pragma Ada_2022;
package body Kome.Frames with SPARK_Mode is

   function Frame_Is (Frame : Byte_Array; Cid : Hash256; X : Header) return Boolean is
     (Kome.Store.Is_Record_Frame (Frame) and then Kome.Store.Header_Of (Cid, Frame) = X);

   procedure Lemma_Frame_Is_Def (Frame : Byte_Array; Cid : Hash256; X : Header) is null;

   procedure Lemma_Frame_Is_Congruent (Cid : Hash256; X : Header; A, B : Byte_Array) is
   begin
      Kome.Store.Lemma_Header_Of_Congruent (Cid, A, B);
   end Lemma_Frame_Is_Congruent;

end Kome.Frames;
