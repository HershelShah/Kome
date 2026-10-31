pragma Ada_2022;
package body Kome.Headers with SPARK_Mode is

   procedure Lemma_Dominates_Irrefl (X : Header) is
   begin
      Lemma_Lt_Irrefl (X.V);
   end Lemma_Dominates_Irrefl;

   procedure Lemma_Dominates_Trans (X, Y, Z : Header) is
   begin
      Lemma_Lt_Trans (X.V, Y.V, Z.V);
   end Lemma_Dominates_Trans;

   procedure Lemma_Revoke_Never_Dominated (Q, X : Header) is null;

end Kome.Headers;
