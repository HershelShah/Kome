pragma Ada_2022;
package body Kome.Headers with SPARK_Mode is

   procedure Lemma_Gen_Lt_Total (A, B : Header) is null;

   procedure Lemma_Gen_Lt_Irrefl (A : Header) is null;

   procedure Lemma_Gen_Lt_Trans (A, B, C : Header) is null;

   procedure Lemma_Dominates_Irrefl (X : Header) is
   begin
      Lemma_Lt_Irrefl (X.V);
   end Lemma_Dominates_Irrefl;

   procedure Lemma_Dominates_Trans (X, Y, Z : Header) is
   begin
      Lemma_Lt_Trans (X.V, Y.V, Z.V);
   end Lemma_Dominates_Trans;

   procedure Lemma_Revoke_Never_Dominated (Q, X : Header) is null;

   procedure Lemma_Roster_Dom (P, Q : Header) is null;

   procedure Lemma_Equal_Gen_No_Dom (P, Q : Header) is null;

   procedure Lemma_Grant_Dom (P, Q : Header) is null;

   procedure Lemma_Dominator_Keeps_Registers (Q, P : Header) is null;

   procedure Lemma_Same_Row (Q, P : Header) is null;

end Kome.Headers;
