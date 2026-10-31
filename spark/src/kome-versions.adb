pragma Ada_2022;
package body Kome.Versions with SPARK_Mode is

   procedure Lemma_Lt_Irrefl (A : Version) is null;
   procedure Lemma_Lt_Asym (A, B : Version) is null;
   procedure Lemma_Lt_Trans (A, B, C : Version) is null;
   procedure Lemma_Trichotomy (A, B : Version) is null;

end Kome.Versions;
