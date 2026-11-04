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

   procedure Lemma_Gate_Refuses_Revoked (S : State; R : Roster_Record; DH : Pubkey) is null;

   procedure Note_Open (G : in out Guard_State; Before, After : State) is
      E : constant Header_View := Roster_Eff (Before);
   begin
      if E.Present and then Root_Void (After, E.Hdr.Issuer) then
         G.Quarantined := True;
      end if;
   end Note_Open;

   procedure Note_Credential (G : in out Guard_State; After : State; Cred : Header) is
   begin
      if Cred.K = K_Roster and then Cred.Issuer = Founding (After)
        and then Roster_Eff (After) = (Present => True, Hdr => Cred)
      then
         G.Quarantined := False;
      end if;
   end Note_Credential;

end Kome.Guard;
