pragma Ada_2022;
package body Kome.Guard with SPARK_Mode is

   function Member_Of (C : Roster_Content; DH : Pubkey) return Member_Count is
   begin
      for I in 1 .. C.N_Members loop
         if Member_DH_PK (C, I) = DH then
            return I;
         end if;
         pragma Loop_Invariant (for all J in 1 .. I => Member_DH_PK (C, J) /= DH);
      end loop;
      return 0;
   end Member_Of;

   procedure Lemma_Gate_Refuses_Revoked (Cid : Hash256; S : State; R : Roster_Record; DH : Pubkey) is null;

   procedure Lemma_Quarantine_Set (S : State; I : Held_Index) is
   begin
      Lemma_Roster_Max_Unique (S, I);
   end Lemma_Quarantine_Set;

   procedure Lemma_Quarantine_Refuses (Cid : Hash256; S : State; R : Roster_Record; DH : Pubkey) is null;

   procedure Lemma_Quarantine_Cleared (S : State; I : Held_Index) is
   begin
      --  No held roster is above Held (S, I): every other one has a lower
      --  gen.
      for J in 1 .. Count (S) loop
         if Held (S, J).K = K_Roster then
            if J = I then
               Lemma_Roster_Lt_Irrefl (Held (S, I));
            else
               pragma Assert (Held (S, J).V.Seq < Held (S, I).V.Seq);
            end if;
         end if;
         pragma Loop_Invariant
           (for all J2 in 1 .. J =>
              (if Held (S, J2).K = K_Roster
               then not Roster_Lt (Held (S, I), Held (S, J2))));
      end loop;
      Lemma_Roster_Max_Unique (S, I);
      Lemma_Roster_Eff_Unique (S, I);
      pragma Assert (not Root_Void (S, Roster_Max (S).Hdr.Issuer));
   end Lemma_Quarantine_Cleared;

end Kome.Guard;
