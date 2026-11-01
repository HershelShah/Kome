pragma Ada_2022;
package body Kome.Views with SPARK_Mode is

   --  Each view is a scan of the held array for a maximal (or any) witness.
   --  The scans return an index (0 for none) so that the lemmas below can
   --  name the witness; the public views are expression functions over the
   --  index, so inside this body the prover sees their definitions.

   ---------------------------------------------------------------------------
   --  Witness scans
   ---------------------------------------------------------------------------

   function Find_Put (S : State; NS, Ent : Id128; FH : Key256) return Held_Count with
     Global => null,
     Post =>
       Find_Put'Result <= Count (S)
       and then
       (if Find_Put'Result = 0 then
          (for all I in 1 .. Count (S) => not Put_On (Held (S, I), NS, Ent, FH))
        else
          Put_On (Held (S, Find_Put'Result), NS, Ent, FH)
          and then (for all I in 1 .. Count (S) =>
                      (if Put_On (Held (S, I), NS, Ent, FH)
                       then not Lt (Held (S, Find_Put'Result).V, Held (S, I).V))))
   is
      Best : Held_Count := 0;
   begin
      for I in 1 .. Count (S) loop
         if Put_On (Held (S, I), NS, Ent, FH)
           and then (Best = 0 or else Lt (Held (S, Best).V, Held (S, I).V))
         then
            if Best /= 0 then
               pragma Assert
                 (for all J in 1 .. I - 1 =>
                    (if Put_On (Held (S, J), NS, Ent, FH)
                     then not Lt (Held (S, Best).V, Held (S, J).V)));
               pragma Assert
                 (for all J in 1 .. I - 1 =>
                    (if Lt (Held (S, I).V, Held (S, J).V)
                     then Lt (Held (S, Best).V, Held (S, J).V)));
            end if;
            Lemma_Lt_Irrefl (Held (S, I).V);
            Best := I;
         end if;
         pragma Loop_Invariant (Best <= I);
         pragma Loop_Invariant
           (if Best = 0 then
              (for all J in 1 .. I => not Put_On (Held (S, J), NS, Ent, FH))
            else
              Put_On (Held (S, Best), NS, Ent, FH)
              and then (for all J in 1 .. I =>
                          (if Put_On (Held (S, J), NS, Ent, FH)
                           then not Lt (Held (S, Best).V, Held (S, J).V))));
      end loop;
      return Best;
   end Find_Put;

   function Find_Del (S : State; NS, Ent : Id128) return Held_Count with
     Global => null,
     Post =>
       Find_Del'Result <= Count (S)
       and then
       (if Find_Del'Result = 0 then
          (for all I in 1 .. Count (S) => not Del_On (Held (S, I), NS, Ent))
        else
          Del_On (Held (S, Find_Del'Result), NS, Ent)
          and then (for all I in 1 .. Count (S) =>
                      (if Del_On (Held (S, I), NS, Ent)
                       then not Lt (Held (S, Find_Del'Result).V, Held (S, I).V))))
   is
      Best : Held_Count := 0;
   begin
      for I in 1 .. Count (S) loop
         if Del_On (Held (S, I), NS, Ent)
           and then (Best = 0 or else Lt (Held (S, Best).V, Held (S, I).V))
         then
            if Best /= 0 then
               pragma Assert
                 (for all J in 1 .. I - 1 =>
                    (if Del_On (Held (S, J), NS, Ent)
                     then not Lt (Held (S, Best).V, Held (S, J).V)));
               pragma Assert
                 (for all J in 1 .. I - 1 =>
                    (if Lt (Held (S, I).V, Held (S, J).V)
                     then Lt (Held (S, Best).V, Held (S, J).V)));
            end if;
            Lemma_Lt_Irrefl (Held (S, I).V);
            Best := I;
         end if;
         pragma Loop_Invariant (Best <= I);
         pragma Loop_Invariant
           (if Best = 0 then
              (for all J in 1 .. I => not Del_On (Held (S, J), NS, Ent))
            else
              Del_On (Held (S, Best), NS, Ent)
              and then (for all J in 1 .. I =>
                          (if Del_On (Held (S, J), NS, Ent)
                           then not Lt (Held (S, Best).V, Held (S, J).V))));
      end loop;
      return Best;
   end Find_Del;

   function Find_Put_In (S : State; NS, Ent : Id128) return Held_Count with
     Global => null,
     Post =>
       Find_Put_In'Result <= Count (S)
       and then
       (if Find_Put_In'Result = 0 then
          (for all I in 1 .. Count (S) => not Put_In (Held (S, I), NS, Ent))
        else Put_In (Held (S, Find_Put_In'Result), NS, Ent))
   is
   begin
      for I in 1 .. Count (S) loop
         if Put_In (Held (S, I), NS, Ent) then
            return I;
         end if;
         pragma Loop_Invariant
           (for all J in 1 .. I => not Put_In (Held (S, J), NS, Ent));
      end loop;
      return 0;
   end Find_Put_In;

   function Find_Void (S : State; P : Header) return Held_Count with
     Global => null,
     Post =>
       Find_Void'Result <= Count (S)
       and then
       (if Find_Void'Result = 0 then
          (for all I in 1 .. Count (S) => not Voids (Held (S, I), P))
        else Voids (Held (S, Find_Void'Result), P))
   is
   begin
      for I in 1 .. Count (S) loop
         if Voids (Held (S, I), P) then
            return I;
         end if;
         pragma Loop_Invariant
           (for all J in 1 .. I => not Voids (Held (S, J), P));
      end loop;
      return 0;
   end Find_Void;

   function Find_Revoke (S : State; NS : Id128; K : Key256) return Held_Count with
     Global => null,
     Post =>
       Find_Revoke'Result <= Count (S)
       and then
       (if Find_Revoke'Result = 0 then
          (for all I in 1 .. Count (S) => not Revokes (Held (S, I), NS, K))
        else Revokes (Held (S, Find_Revoke'Result), NS, K))
   is
   begin
      for I in 1 .. Count (S) loop
         if Revokes (Held (S, I), NS, K) then
            return I;
         end if;
         pragma Loop_Invariant
           (for all J in 1 .. I => not Revokes (Held (S, J), NS, K));
      end loop;
      return 0;
   end Find_Revoke;

   ---------------------------------------------------------------------------
   --  Views
   ---------------------------------------------------------------------------

   --  Each scan runs once (a declare expression binds its index).
   function Cell (S : State; NS, Ent : Id128; FH : Key256) return Header_View is
     (declare
        I : constant Held_Count := Find_Put (S, NS, Ent, FH);
      begin
        (if I = 0 then (Present => False, Hdr => No_Header)
         else (Present => True, Hdr => Held (S, I))));

   function Deleted_At (S : State; NS, Ent : Id128) return Version_View is
     (declare
        I : constant Held_Count := Find_Del (S, NS, Ent);
      begin
        (if I = 0 then (Present => False, V => No_Version)
         else (Present => True, V => Held (S, I).V)));

   function Exists (S : State; NS, Ent : Id128) return Boolean is
     (Find_Put_In (S, NS, Ent) /= 0);

   function Is_Void (S : State; P : Header) return Boolean is
     (Find_Void (S, P) /= 0);

   function Root_Void (S : State; NS : Id128; K : Key256) return Boolean is
     (Find_Revoke (S, NS, K) /= 0);

   --  A roster eligible for ROSTER_eff.
   function Eligible (S : State; NS : Id128; X : Header) return Boolean is
     (Roster_In (X, NS) and then not Root_Void (S, NS, X.V.Author))
   with Global => null;

   --  One pass. The root_void scan runs only for a roster of ns that would
   --  improve on the best so far, so at most once per roster of ns (on a
   --  frontier, at most one per signer: older ones are dominated), not once
   --  per held record.
   function Roster_Eff (S : State; NS : Id128) return Header_View is
      Best : Held_Count := 0;
   begin
      for I in 1 .. Count (S) loop
         if Roster_In (Held (S, I), NS)
           and then (Best = 0 or else Gen_Lt (Held (S, Best), Held (S, I)))
           and then not Root_Void (S, NS, Held (S, I).V.Author)
         then
            if Best /= 0 then
               pragma Assert
                 (for all J in 1 .. I - 1 =>
                    (if Eligible (S, NS, Held (S, J))
                     then not Gen_Lt (Held (S, Best), Held (S, J))));
               pragma Assert
                 (for all J in 1 .. I - 1 =>
                    (if Gen_Lt (Held (S, I), Held (S, J))
                     then Gen_Lt (Held (S, Best), Held (S, J))));
            end if;
            Lemma_Gen_Lt_Irrefl (Held (S, I));
            Best := I;
         end if;
         pragma Loop_Invariant (Best <= I);
         pragma Loop_Invariant
           (if Best = 0 then
              (for all J in 1 .. I => not Eligible (S, NS, Held (S, J)))
            else
              Eligible (S, NS, Held (S, Best))
              and then (for all J in 1 .. I =>
                          (if Eligible (S, NS, Held (S, J))
                           then not Gen_Lt (Held (S, Best), Held (S, J)))));
      end loop;
      if Best = 0 then
         return (Present => False, Hdr => No_Header);
      else
         return (Present => True, Hdr => Held (S, Best));
      end if;
   end Roster_Eff;

   ---------------------------------------------------------------------------
   --  Laws
   ---------------------------------------------------------------------------

   --  A record held in S, with the index it is held at.
   function Index_Of (S : State; X : Header) return Held_Count with
     Ghost, Global => null,
     Pre  => Holds (S, X),
     Post => Index_Of'Result in 1 .. Count (S) and then Held (S, Index_Of'Result) = X
   is
      R : Held_Count := 0;
   begin
      for I in 1 .. Count (S) loop
         if Held (S, I) = X then
            R := I;
            exit;
         end if;
         pragma Loop_Invariant (R = 0);
         pragma Loop_Invariant (for all J in 1 .. I => Held (S, J) /= X);
      end loop;
      --  R = 0 would contradict Holds (S, X).
      return R;
   end Index_Of;

   --  Unique_Versions instantiated at two indices; kept separate so that the
   --  quantifier is unfolded in a small context.
   procedure Lemma_A2 (S : State; I, J : Held_Index) with
     Ghost, Global => null,
     Pre  => Unique_Versions (S)
             and then I <= Count (S) and then J <= Count (S)
             and then Held (S, I).V = Held (S, J).V,
     Post => Held (S, I) = Held (S, J)
   is
   begin
      null;
   end Lemma_A2;

   procedure Lemma_Cell_Unique (S : State; I, J : Held_Index) is
   begin
      --  Is_Frontier, instantiated at I and J.
      pragma Assert (Admitted (S, Held (S, I)) and then Admitted (S, Held (S, J)));
      pragma Assert (not Dom (S, Held (S, I)) and then not Dom (S, Held (S, J)));
      pragma Assert (not Dominates (Held (S, J), Held (S, I)));
      pragma Assert (not Dominates (Held (S, I), Held (S, J)));
      --  Same cell, so a strictly newer version would dominate.
      pragma Assert (not Lt (Held (S, I).V, Held (S, J).V));
      pragma Assert (not Lt (Held (S, J).V, Held (S, I).V));
      Lemma_Trichotomy (Held (S, I).V, Held (S, J).V);
      pragma Assert (Held (S, I).V = Held (S, J).V);
      if Unique_Versions (S) then
         pragma Assert (Held (S, I) = Held (S, J));
         pragma Assert (I = J);
      end if;
      if Canonical (Held (S, I)) and then Canonical (Held (S, J)) then
         pragma Assert (Held (S, I) = Held (S, J));
         pragma Assert (I = J);
      end if;
   end Lemma_Cell_Unique;

   procedure Lemma_Del_Unique (S : State; I, J : Held_Index) is
   begin
      pragma Assert (Admitted (S, Held (S, I)) and then Admitted (S, Held (S, J)));
      pragma Assert (not Dom (S, Held (S, I)) and then not Dom (S, Held (S, J)));
      pragma Assert (not Dominates (Held (S, J), Held (S, I)));
      pragma Assert (not Dominates (Held (S, I), Held (S, J)));
      pragma Assert (not Lt (Held (S, I).V, Held (S, J).V));
      pragma Assert (not Lt (Held (S, J).V, Held (S, I).V));
      Lemma_Trichotomy (Held (S, I).V, Held (S, J).V);
      pragma Assert (Held (S, I).V = Held (S, J).V);
      if Unique_Versions (S) then
         pragma Assert (Held (S, I) = Held (S, J));
         pragma Assert (I = J);
      end if;
      if Canonical (Held (S, I)) and then Canonical (Held (S, J)) then
         pragma Assert (Held (S, I) = Held (S, J));
         pragma Assert (I = J);
      end if;
   end Lemma_Del_Unique;

   procedure Lemma_Gen_Lt_Total (A, B : Header) is
   begin
      Lemma_Trichotomy (A.V, B.V);
      pragma Assert (Lt (A.V.H, B.V.H) or else A.V.H = B.V.H or else Lt (B.V.H, A.V.H));
   end Lemma_Gen_Lt_Total;

   procedure Lemma_Gen_Lt_Irrefl (A : Header) is
   begin
      Lemma_Lt_Irrefl (A.V);
      pragma Assert (not Lt (A.V.H, A.V.H));
   end Lemma_Gen_Lt_Irrefl;

   procedure Lemma_Roster_Unique (S : State; I, J : Held_Index) is
   begin
      Lemma_Gen_Lt_Total (Held (S, I), Held (S, J));
      pragma Assert (Held (S, I).V = Held (S, J).V);
      pragma Assert (Held (S, I) = Held (S, J));
      --  Is_Frontier: no record is held twice.
      pragma Assert (I = J);
   end Lemma_Roster_Unique;

   procedure Lemma_Roster_Eff_Unique (S : State; NS : Id128; I : Held_Index) is
      E : constant Header_View := Roster_Eff (S, NS);
   begin
      pragma Assert (E.Present);
      declare
         K : constant Held_Count := Index_Of (S, E.Hdr);
      begin
         pragma Assert (Roster_In (Held (S, K), NS)
                        and then not Root_Void (S, NS, Held (S, K).V.Author));
         pragma Assert (not Gen_Lt (Held (S, I), Held (S, K)));
         pragma Assert (not Gen_Lt (Held (S, K), Held (S, I)));
         Lemma_Gen_Lt_Total (Held (S, I), Held (S, K));
         pragma Assert (Held (S, I).V = Held (S, K).V);
         pragma Assert (Held (S, I) = Held (S, K));
      end;
   end Lemma_Roster_Eff_Unique;

   procedure Lemma_Exists_Cell (S : State; NS, Ent : Id128; FH : Key256) is
      W : constant Held_Count := Find_Put_In (S, NS, Ent);
   begin
      if Find_Put (S, NS, Ent, FH) /= 0 then
         pragma Assert (Put_In (Held (S, Find_Put (S, NS, Ent, FH)), NS, Ent));
         pragma Assert (Exists (S, NS, Ent));
      end if;
      if W /= 0 then
         pragma Assert (Put_On (Held (S, W), NS, Ent, Held (S, W).FH));
         pragma Assert (Find_Put (S, NS, Ent, Held (S, W).FH) /= 0);
         pragma Assert (Cell (S, NS, Ent, Held (S, W).FH).Present);
      end if;
   end Lemma_Exists_Cell;

   procedure Lemma_Data_Local (S1, S2 : State; NS, Ent : Id128) is
   begin
      --  Same_Data, unfolded.
      pragma Assert
        (for all I in 1 .. Count (S1) =>
           (if Is_Data (Held (S1, I)) then Holds (S2, Held (S1, I))));
      pragma Assert
        (for all I in 1 .. Count (S2) =>
           (if Is_Data (Held (S2, I)) then Holds (S1, Held (S2, I))));

      --  deleted_at: each maximum is held on the other side, so neither
      --  version is below the other, so they are equal.
      declare
         I1 : constant Held_Count := Find_Del (S1, NS, Ent);
         I2 : constant Held_Count := Find_Del (S2, NS, Ent);
      begin
         if I1 /= 0 then
            declare
               X1 : constant Header := Held (S1, I1);
               J  : constant Held_Count := Index_Of (S2, X1);
            begin
               pragma Assert (Del_On (Held (S2, J), NS, Ent));
               pragma Assert (I2 /= 0);
               pragma Assert (not Lt (Held (S2, I2).V, X1.V));
            end;
         end if;
         if I2 /= 0 then
            declare
               X2 : constant Header := Held (S2, I2);
               J  : constant Held_Count := Index_Of (S1, X2);
            begin
               pragma Assert (Del_On (Held (S1, J), NS, Ent));
               pragma Assert (I1 /= 0);
               pragma Assert (not Lt (Held (S1, I1).V, X2.V));
            end;
         end if;
         pragma Assert ((I1 = 0) = (I2 = 0));
         if I1 /= 0 then
            Lemma_Trichotomy (Held (S1, I1).V, Held (S2, I2).V);
            pragma Assert (Held (S1, I1).V = Held (S2, I2).V);
         end if;
         pragma Assert (Deleted_At (S1, NS, Ent) = Deleted_At (S2, NS, Ent));
      end;

      --  exists: a witness on either side is a witness on the other.
      declare
         I1 : constant Held_Count := Find_Put_In (S1, NS, Ent);
         I2 : constant Held_Count := Find_Put_In (S2, NS, Ent);
      begin
         if I1 /= 0 then
            declare
               J : constant Held_Count := Index_Of (S2, Held (S1, I1));
            begin
               pragma Assert (Put_In (Held (S2, J), NS, Ent));
               pragma Assert (I2 /= 0);
            end;
         end if;
         if I2 /= 0 then
            declare
               J : constant Held_Count := Index_Of (S1, Held (S2, I2));
            begin
               pragma Assert (Put_In (Held (S1, J), NS, Ent));
               pragma Assert (I1 /= 0);
            end;
         end if;
         pragma Assert (Exists (S1, NS, Ent) = Exists (S2, NS, Ent));
      end;
   end Lemma_Data_Local;

   procedure Lemma_Cell_Local (S1, S2 : State; NS, Ent : Id128; FH : Key256) is
      I1 : constant Held_Count := Find_Put (S1, NS, Ent, FH);
      I2 : constant Held_Count := Find_Put (S2, NS, Ent, FH);
   begin
      pragma Assert
        (for all I in 1 .. Count (S1) =>
           (if Is_Data (Held (S1, I)) then Holds (S2, Held (S1, I))));
      pragma Assert
        (for all I in 1 .. Count (S2) =>
           (if Is_Data (Held (S2, I)) then Holds (S1, Held (S2, I))));

      if I1 /= 0 then
         declare
            X1 : constant Header := Held (S1, I1);
            J  : constant Held_Count := Index_Of (S2, X1);
         begin
            pragma Assert (Put_On (Held (S2, J), NS, Ent, FH));
            pragma Assert (I2 /= 0);
            pragma Assert (not Lt (Held (S2, I2).V, X1.V));
         end;
      end if;
      if I2 /= 0 then
         declare
            X2 : constant Header := Held (S2, I2);
            J  : constant Held_Count := Index_Of (S1, X2);
         begin
            pragma Assert (Put_On (Held (S1, J), NS, Ent, FH));
            pragma Assert (I1 /= 0);
            pragma Assert (not Lt (Held (S1, I1).V, X2.V));
         end;
      end if;
      pragma Assert ((I1 = 0) = (I2 = 0));

      if I1 = 0 then
         pragma Assert (Cell (S1, NS, Ent, FH) = Cell (S2, NS, Ent, FH));
      else
         Lemma_Trichotomy (Held (S1, I1).V, Held (S2, I2).V);
         pragma Assert (Held (S1, I1).V = Held (S2, I2).V);
         pragma Assert (Cell (S1, NS, Ent, FH).Hdr.V = Cell (S2, NS, Ent, FH).Hdr.V);
         --  The two maxima are both held in S1 (at I1 and at J) with the
         --  same version and on the same cell.
         declare
            J : constant Held_Count := Index_Of (S1, Held (S2, I2));
         begin
            pragma Assert (Held (S1, I1).V = Held (S1, J).V);
            pragma Assert (Put_On (Held (S1, J), NS, Ent, FH));
            if Unique_Versions (S1) then
               Lemma_A2 (S1, I1, J);
               pragma Assert (Held (S1, I1) = Held (S1, J));
            end if;
            if (for all I in 1 .. Count (S1) =>
                  (if Held (S1, I).K = K_Put then Canonical (Held (S1, I))))
            then
               pragma Assert (Canonical (Held (S1, I1)) and then Canonical (Held (S1, J)));
               pragma Assert (Held (S1, I1) = Held (S1, J));
            end if;
         end;
      end if;
   end Lemma_Cell_Local;

   procedure Lemma_Views_Local (S1, S2 : State; NS, Ent : Id128; FH : Key256) is
   begin
      Lemma_Data_Local (S1, S2, NS, Ent);
      Lemma_Cell_Local (S1, S2, NS, Ent, FH);
   end Lemma_Views_Local;

   procedure Lemma_Root_Void_Local (S1, S2 : State; NS : Id128; K : Key256) is
      I1 : constant Held_Count := Find_Revoke (S1, NS, K);
      I2 : constant Held_Count := Find_Revoke (S2, NS, K);
   begin
      --  Same_Auth, unfolded.
      pragma Assert
        (for all I in 1 .. Count (S1) =>
           (if not Is_Data (Held (S1, I)) then Holds (S2, Held (S1, I))));
      pragma Assert
        (for all I in 1 .. Count (S2) =>
           (if not Is_Data (Held (S2, I)) then Holds (S1, Held (S2, I))));
      if I1 /= 0 then
         declare
            J : constant Held_Count := Index_Of (S2, Held (S1, I1));
         begin
            pragma Assert (Revokes (Held (S2, J), NS, K));
            pragma Assert (I2 /= 0);
         end;
      end if;
      if I2 /= 0 then
         declare
            J : constant Held_Count := Index_Of (S1, Held (S2, I2));
         begin
            pragma Assert (Revokes (Held (S1, J), NS, K));
            pragma Assert (I1 /= 0);
         end;
      end if;
   end Lemma_Root_Void_Local;

   procedure Lemma_Void_Local (S1, S2 : State; P : Header) is
      I1 : constant Held_Count := Find_Void (S1, P);
      I2 : constant Held_Count := Find_Void (S2, P);
   begin
      pragma Assert
        (for all I in 1 .. Count (S1) =>
           (if not Is_Data (Held (S1, I)) then Holds (S2, Held (S1, I))));
      pragma Assert
        (for all I in 1 .. Count (S2) =>
           (if not Is_Data (Held (S2, I)) then Holds (S1, Held (S2, I))));
      if I1 /= 0 then
         declare
            J : constant Held_Count := Index_Of (S2, Held (S1, I1));
         begin
            pragma Assert (Voids (Held (S2, J), P));
            pragma Assert (I2 /= 0);
         end;
      end if;
      if I2 /= 0 then
         declare
            J : constant Held_Count := Index_Of (S1, Held (S2, I2));
         begin
            pragma Assert (Voids (Held (S1, J), P));
            pragma Assert (I1 /= 0);
         end;
      end if;
   end Lemma_Void_Local;

   procedure Lemma_Roster_Local (S1, S2 : State; NS : Id128) is
      E1 : constant Header_View := Roster_Eff (S1, NS);
      E2 : constant Header_View := Roster_Eff (S2, NS);
   begin
      pragma Assert
        (for all I in 1 .. Count (S1) =>
           (if not Is_Data (Held (S1, I)) then Holds (S2, Held (S1, I))));
      pragma Assert
        (for all I in 1 .. Count (S2) =>
           (if not Is_Data (Held (S2, I)) then Holds (S1, Held (S2, I))));

      --  Each side's result is held and eligible on the other side, so it
      --  makes the other side present and is not beaten there.
      if E1.Present then
         declare
            I1 : constant Held_Count := Index_Of (S1, E1.Hdr);
            J  : constant Held_Count := Index_Of (S2, E1.Hdr);
         begin
            pragma Assert (not Is_Data (Held (S1, I1)));
            Lemma_Root_Void_Local (S1, S2, NS, E1.Hdr.V.Author);
            pragma Assert (Roster_In (Held (S2, J), NS)
                           and then not Root_Void (S2, NS, Held (S2, J).V.Author));
            pragma Assert (E2.Present);
            pragma Assert (not Gen_Lt (E2.Hdr, E1.Hdr));
         end;
      end if;
      if E2.Present then
         declare
            I2 : constant Held_Count := Index_Of (S2, E2.Hdr);
            J  : constant Held_Count := Index_Of (S1, E2.Hdr);
         begin
            pragma Assert (not Is_Data (Held (S2, I2)));
            Lemma_Root_Void_Local (S1, S2, NS, E2.Hdr.V.Author);
            pragma Assert (Roster_In (Held (S1, J), NS)
                           and then not Root_Void (S1, NS, Held (S1, J).V.Author));
            pragma Assert (E1.Present);
            pragma Assert (not Gen_Lt (E1.Hdr, E2.Hdr));
         end;
      end if;
      pragma Assert (E1.Present = E2.Present);

      if E1.Present then
         Lemma_Gen_Lt_Total (E1.Hdr, E2.Hdr);
         pragma Assert (E1.Hdr.V = E2.Hdr.V);
         declare
            I1 : constant Held_Count := Index_Of (S1, E1.Hdr);
            J  : constant Held_Count := Index_Of (S1, E2.Hdr);
         begin
            pragma Assert (Held (S1, I1).V = Held (S1, J).V);
            if Unique_Versions (S1) then
               pragma Assert (Held (S1, I1) = Held (S1, J));
               pragma Assert (E1 = E2);
            end if;
         end;
      else
         pragma Assert (E1 = E2);
      end if;
   end Lemma_Roster_Local;

   procedure Lemma_Apply_Auth_Local (Before, After : State; R : Header) is
   begin
      --  Is_Frontier (Before), unfolded: no held record dominates another.
      pragma Assert (for all K in 1 .. Count (Before) => Admitted (Before, Held (Before, K)));
      pragma Assert
        (for all K in 1 .. Count (Before) =>
           (for all L in 1 .. Count (Before) =>
              not Dominates (Held (Before, L), Held (Before, K))));

      --  After ⊆ Before ∪ {R}, and R is not data: every data record of After is
      --  held in Before.
      for I in 1 .. Count (After) loop
         pragma Assert (Holds (Before, Held (After, I)) or else Held (After, I) = R);
         pragma Assert (if Is_Data (Held (After, I)) then Holds (Before, Held (After, I)));
         pragma Loop_Invariant
           (for all J in 1 .. I =>
              (if Is_Data (Held (After, J)) then Holds (Before, Held (After, J))));
      end loop;

      --  Before ⊆ After for data: a data record of Before could be lost only by a
      --  dominator in After, which is R (an authorization record, which
      --  dominates no data) or a record of Before (which dominates nothing in
      --  Before, Before being a frontier).
      for I in 1 .. Count (Before) loop
         if Is_Data (Held (Before, I)) and then not Holds (After, Held (Before, I)) then
            pragma Assert (Dom (After, Held (Before, I)));
            for K in 1 .. Count (After) loop
               if Held (After, K) /= R then
                  declare
                     L : constant Held_Count := Index_Of (Before, Held (After, K));
                  begin
                     pragma Assert (not Dominates (Held (Before, L), Held (Before, I)));
                  end;
               end if;
               pragma Assert (not Dominates (Held (After, K), Held (Before, I)));
               pragma Loop_Invariant
                 (for all J in 1 .. K => not Dominates (Held (After, J), Held (Before, I)));
            end loop;
            pragma Assert (not Dom (After, Held (Before, I)));
         end if;
         pragma Loop_Invariant
           (for all J in 1 .. I =>
              (if Is_Data (Held (Before, J)) then Holds (After, Held (Before, J))));
      end loop;
   end Lemma_Apply_Auth_Local;

   procedure Lemma_Apply_Data_Local (Before, After : State; R : Header) is
   begin
      pragma Assert (for all K in 1 .. Count (Before) => Admitted (Before, Held (Before, K)));
      pragma Assert
        (for all K in 1 .. Count (Before) =>
           (for all L in 1 .. Count (Before) =>
              not Dominates (Held (Before, L), Held (Before, K))));

      --  After ⊆ Before ∪ {R}, and R is data: every authorization record of
      --  After is held in Before.
      for I in 1 .. Count (After) loop
         pragma Assert (Holds (Before, Held (After, I)) or else Held (After, I) = R);
         pragma Assert
           (if not Is_Data (Held (After, I)) then Holds (Before, Held (After, I)));
         pragma Loop_Invariant
           (for all J in 1 .. I =>
              (if not Is_Data (Held (After, J)) then Holds (Before, Held (After, J))));
      end loop;

      --  Before ⊆ After for authorization records: a ROSTER or REVOKE is
      --  dominated only by a ROSTER, so neither R (data) nor a record of the
      --  frontier Before can be the dominator.
      for I in 1 .. Count (Before) loop
         if not Is_Data (Held (Before, I)) and then not Holds (After, Held (Before, I)) then
            pragma Assert (Dom (After, Held (Before, I)));
            for K in 1 .. Count (After) loop
               if Held (After, K) /= R then
                  declare
                     L : constant Held_Count := Index_Of (Before, Held (After, K));
                  begin
                     pragma Assert (not Dominates (Held (Before, L), Held (Before, I)));
                  end;
               end if;
               pragma Assert (not Dominates (Held (After, K), Held (Before, I)));
               pragma Loop_Invariant
                 (for all J in 1 .. K => not Dominates (Held (After, J), Held (Before, I)));
            end loop;
            pragma Assert (not Dom (After, Held (Before, I)));
         end if;
         pragma Loop_Invariant
           (for all J in 1 .. I =>
              (if not Is_Data (Held (Before, J)) then Holds (After, Held (Before, J))));
      end loop;
   end Lemma_Apply_Data_Local;

   procedure Lemma_Void_Monotone (S1, S2 : State; P : Header) is
      I : constant Held_Count := Find_Void (S1, P);
      J : constant Held_Count := Index_Of (S2, Held (S1, I));
   begin
      pragma Assert (Voids (Held (S2, J), P));
   end Lemma_Void_Monotone;

   procedure Lemma_Apply_Keeps_Revokes (Before, After : State) is
   begin
      for I in 1 .. Count (Before) loop
         if Held (Before, I).K = K_Revoke then
            --  Nothing dominates a REVOKE, so Dom (After, it) is false.
            pragma Assert
              (for all K in 1 .. Count (After) =>
                 not Dominates (Held (After, K), Held (Before, I)));
            pragma Assert (not Dom (After, Held (Before, I)));
            pragma Assert (Holds (After, Held (Before, I)));
         end if;
         pragma Loop_Invariant
           (for all J in 1 .. I =>
              (if Held (Before, J).K = K_Revoke then Holds (After, Held (Before, J))));
      end loop;
   end Lemma_Apply_Keeps_Revokes;

end Kome.Views;
