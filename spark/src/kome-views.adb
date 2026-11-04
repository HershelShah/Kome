pragma Ada_2022;
package body Kome.Views with SPARK_Mode is

   --  Each view scans the held array for a maximal witness (or for one
   --  witness). The scans return an index (0 for none), so that the lemmas
   --  below can name the witness. The public views are expression functions
   --  over the index, so in this body the prover sees their definitions,
   --  and outside it they are opaque (Lemma_<View>_Def).

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

   --  A REVOKE of K issued by the founding key.
   function Find_Root_Revoke (S : State; K : Key256) return Held_Count with
     Global => null,
     Post =>
       Find_Root_Revoke'Result <= Count (S)
       and then
       (if Find_Root_Revoke'Result = 0 then
          (for all I in 1 .. Count (S) =>
             not Root_Revokes (Held (S, I), Founding (S), K))
        else Root_Revokes (Held (S, Find_Root_Revoke'Result), Founding (S), K))
   is
   begin
      for I in 1 .. Count (S) loop
         if Root_Revokes (Held (S, I), Founding (S), K) then
            return I;
         end if;
         pragma Loop_Invariant
           (for all J in 1 .. I => not Root_Revokes (Held (S, J), Founding (S), K));
      end loop;
      return 0;
   end Find_Root_Revoke;

   function Root_Void (S : State; K : Key256) return Boolean is
     (K /= Founding (S) and then Find_Root_Revoke (S, K) /= 0);

   --  A GRANT of K with an issuer that is not root_void.
   function Find_Grant (S : State; K : Key256) return Held_Count with
     Global => null,
     Post =>
       Find_Grant'Result <= Count (S)
       and then
       (if Find_Grant'Result = 0 then
          (for all I in 1 .. Count (S) =>
             not (Grants (Held (S, I), K)
                  and then not Root_Void (S, Held (S, I).Issuer)))
        else Grants (Held (S, Find_Grant'Result), K)
             and then not Root_Void (S, Held (S, Find_Grant'Result).Issuer))
   is
   begin
      for I in 1 .. Count (S) loop
         if Grants (Held (S, I), K) and then not Root_Void (S, Held (S, I).Issuer) then
            return I;
         end if;
         pragma Loop_Invariant
           (for all J in 1 .. I =>
              not (Grants (Held (S, J), K)
                   and then not Root_Void (S, Held (S, J).Issuer)));
      end loop;
      return 0;
   end Find_Grant;

   --  A REVOKE of K, with any from_t, with an issuer that is not root_void.
   function Find_Revoked (S : State; K : Key256) return Held_Count with
     Global => null,
     Post =>
       Find_Revoked'Result <= Count (S)
       and then
       (if Find_Revoked'Result = 0 then
          (for all I in 1 .. Count (S) =>
             not (Revokes (Held (S, I), K)
                  and then not Root_Void (S, Held (S, I).Issuer)))
        else Revokes (Held (S, Find_Revoked'Result), K)
             and then not Root_Void (S, Held (S, Find_Revoked'Result).Issuer))
   is
   begin
      for I in 1 .. Count (S) loop
         if Revokes (Held (S, I), K) and then not Root_Void (S, Held (S, I).Issuer) then
            return I;
         end if;
         pragma Loop_Invariant
           (for all J in 1 .. I =>
              not (Revokes (Held (S, J), K)
                   and then not Root_Void (S, Held (S, J).Issuer)));
      end loop;
      return 0;
   end Find_Revoked;

   --  A roster that is forked with another held roster.
   function Find_Fork (S : State) return Held_Count with
     Global => null,
     Post =>
       Find_Fork'Result <= Count (S)
       and then
       (if Find_Fork'Result = 0 then
          (for all I in 1 .. Count (S) =>
             (for all J in 1 .. Count (S) => not Forked (Held (S, I), Held (S, J))))
        else
          (for some J in 1 .. Count (S) => Forked (Held (S, Find_Fork'Result), Held (S, J))))
   is
   begin
      for I in 1 .. Count (S) loop
         for J in 1 .. Count (S) loop
            if Forked (Held (S, I), Held (S, J)) then
               return I;
            end if;
            pragma Loop_Invariant
              (for all J2 in 1 .. J => not Forked (Held (S, I), Held (S, J2)));
         end loop;
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              (for all J in 1 .. Count (S) => not Forked (Held (S, I2), Held (S, J))));
      end loop;
      return 0;
   end Find_Fork;

   --  A REVOKE that voids P and has an issuer that is not root_void.
   function Find_Void (S : State; P : Header) return Held_Count with
     Global => null,
     Post =>
       Find_Void'Result <= Count (S)
       and then
       (if Find_Void'Result = 0 then
          (for all I in 1 .. Count (S) =>
             not (Voids (Held (S, I), P)
                  and then not Root_Void (S, Held (S, I).Issuer)))
        else Voids (Held (S, Find_Void'Result), P)
             and then not Root_Void (S, Held (S, Find_Void'Result).Issuer))
   is
   begin
      for I in 1 .. Count (S) loop
         if Voids (Held (S, I), P) and then not Root_Void (S, Held (S, I).Issuer) then
            return I;
         end if;
         pragma Loop_Invariant
           (for all J in 1 .. I =>
              not (Voids (Held (S, J), P)
                   and then not Root_Void (S, Held (S, J).Issuer)));
      end loop;
      return 0;
   end Find_Void;

   --  An eligible rival of the roster E (A22).
   function Find_Rival (S : State; E : Header) return Held_Count with
     Global => null,
     Post =>
       Find_Rival'Result <= Count (S)
       and then
       (if Find_Rival'Result = 0 then
          (for all I in 1 .. Count (S) =>
             not (Eligible (S, Held (S, I)) and then Rivals (Held (S, I), E)))
        else Eligible (S, Held (S, Find_Rival'Result))
             and then Rivals (Held (S, Find_Rival'Result), E))
   is
   begin
      for I in 1 .. Count (S) loop
         if Rivals (Held (S, I), E) and then not Root_Void (S, Held (S, I).Issuer) then
            return I;
         end if;
         pragma Loop_Invariant
           (for all J in 1 .. I =>
              not (Eligible (S, Held (S, J)) and then Rivals (Held (S, J), E)));
      end loop;
      return 0;
   end Find_Rival;

   --  The Roster_Lt-maximal eligible roster. The root_void scan runs only
   --  for a roster that is better than the best roster found before it.
   function Find_Roster (S : State) return Held_Count with
     Global => null,
     Post =>
       Find_Roster'Result <= Count (S)
       and then
       (if Find_Roster'Result = 0 then
          (for all I in 1 .. Count (S) => not Eligible (S, Held (S, I)))
        else
          Eligible (S, Held (S, Find_Roster'Result))
          and then (for all I in 1 .. Count (S) =>
                      (if Eligible (S, Held (S, I))
                       then not Roster_Lt (Held (S, Find_Roster'Result), Held (S, I)))))
   is
      Best : Held_Count := 0;
   begin
      for I in 1 .. Count (S) loop
         if Held (S, I).K = K_Roster
           and then (Best = 0 or else Roster_Lt (Held (S, Best), Held (S, I)))
           and then not Root_Void (S, Held (S, I).Issuer)
         then
            if Best /= 0 then
               pragma Assert
                 (for all J in 1 .. I - 1 =>
                    (if Eligible (S, Held (S, J))
                     then not Roster_Lt (Held (S, Best), Held (S, J))));
               pragma Assert
                 (for all J in 1 .. I - 1 =>
                    (if Roster_Lt (Held (S, I), Held (S, J))
                     then Roster_Lt (Held (S, Best), Held (S, J))));
            end if;
            Lemma_Roster_Lt_Irrefl (Held (S, I));
            Best := I;
         end if;
         pragma Loop_Invariant (Best <= I);
         pragma Loop_Invariant
           (if Best = 0 then
              (for all J in 1 .. I => not Eligible (S, Held (S, J)))
            else
              Eligible (S, Held (S, Best))
              and then (for all J in 1 .. I =>
                          (if Eligible (S, Held (S, J))
                           then not Roster_Lt (Held (S, Best), Held (S, J)))));
      end loop;
      return Best;
   end Find_Roster;

   --  The eligible roster with the largest del_ttl. On a frontier, its
   --  del_ttl is in range (canonical rosters).
   function Find_TTL (S : State) return Held_Count with
     Global => null,
     Pre  => Is_Frontier (S),
     Post =>
       Find_TTL'Result <= Count (S)
       and then
       (if Find_TTL'Result = 0 then
          (for all I in 1 .. Count (S) => not Eligible (S, Held (S, I)))
        else
          Eligible (S, Held (S, Find_TTL'Result))
          and then Held (S, Find_TTL'Result).Del_TTL in Del_TTL_Min .. Del_TTL_Max
          and then (for all I in 1 .. Count (S) =>
                      (if Eligible (S, Held (S, I))
                       then Held (S, I).Del_TTL <= Held (S, Find_TTL'Result).Del_TTL)))
   is
      Best : Held_Count := 0;
   begin
      for I in 1 .. Count (S) loop
         if Held (S, I).K = K_Roster
           and then (Best = 0 or else Held (S, Best).Del_TTL < Held (S, I).Del_TTL)
           and then not Root_Void (S, Held (S, I).Issuer)
         then
            Lemma_Frontier_Held (S, I);
            pragma Assert (Canonical (Held (S, I)));
            Best := I;
         end if;
         pragma Loop_Invariant (Best <= I);
         pragma Loop_Invariant
           (if Best = 0 then
              (for all J in 1 .. I => not Eligible (S, Held (S, J)))
            else
              Eligible (S, Held (S, Best))
              and then Held (S, Best).Del_TTL in Del_TTL_Min .. Del_TTL_Max
              and then (for all J in 1 .. I =>
                          (if Eligible (S, Held (S, J))
                           then Held (S, J).Del_TTL <= Held (S, Best).Del_TTL)));
      end loop;
      return Best;
   end Find_TTL;

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

   function W_Eff (S : State; K : Key256) return Boolean is
     (Find_Grant (S, K) /= 0);

   function Revoke_Void (S : State; P : Header) return Boolean is
     (Is_Data (P) and then Find_Void (S, P) /= 0);

   function Revoked (S : State; K : Key256) return Boolean is
     (Find_Revoked (S, K) /= 0);

   function Roster_Fork (S : State) return Boolean is
     (Find_Fork (S) /= 0);

   function Is_Void (S : State; P : Header) return Boolean is
     (Is_Data (P) and then (Revoke_Void (S, P) or else not W_Eff (S, P.V.Author)));

   function Roster_Eff (S : State) return Header_View is
     (declare
        I : constant Held_Count := Find_Roster (S);
      begin
        (if I = 0 then (Present => False, Hdr => No_Header)
         else (Present => True, Hdr => Held (S, I))));

   function Contested (S : State) return Boolean is
     (declare
        E : constant Header_View := Roster_Eff (S);
      begin
        E.Present and then Find_Rival (S, E.Hdr) /= 0);

   function Del_TTL_Eff (S : State) return U48 is
     (declare
        I : constant Held_Count := Find_TTL (S);
      begin
        (if I = 0 then Del_TTL_Default else Held (S, I).Del_TTL));

   ---------------------------------------------------------------------------
   --  Definitions
   ---------------------------------------------------------------------------

   procedure Lemma_Cell_Def (S : State; NS, Ent : Id128; FH : Key256) is null;

   procedure Lemma_Deleted_At_Def (S : State; NS, Ent : Id128) is null;

   procedure Lemma_Exists_Def (S : State; NS, Ent : Id128) is null;

   procedure Lemma_Root_Void_Def (S : State; K : Key256) is null;

   procedure Lemma_W_Eff_Def (S : State; K : Key256) is null;

   procedure Lemma_Is_Void_Def (S : State; P : Header) is null;

   procedure Lemma_Roster_Eff_Def (S : State) is
      I : constant Held_Count := Find_Roster (S);
   begin
      if I /= 0 then
         --  A greater epoch is the first disjunct of Roster_Lt.
         pragma Assert
           (for all J in 1 .. Count (S) =>
              (if Held (S, I).Epoch < Held (S, J).Epoch
               then Roster_Lt (Held (S, I), Held (S, J))));
      end if;
   end Lemma_Roster_Eff_Def;

   procedure Lemma_Revoked_Def (S : State; K : Key256) is null;

   procedure Lemma_Roster_Fork_Def (S : State) is null;

   procedure Lemma_Contested_Def (S : State) is null;

   procedure Lemma_Revoke_Void_Revoked (S : State; P : Header) is
      I : constant Held_Count := Find_Void (S, P);
   begin
      pragma Assert (I /= 0);
      pragma Assert (Revokes (Held (S, I), P.V.Author));
      pragma Assert (Find_Revoked (S, P.V.Author) /= 0);
   end Lemma_Revoke_Void_Revoked;

   procedure Lemma_Del_TTL_Eff_Def (S : State) is null;

   ---------------------------------------------------------------------------
   --  Laws
   ---------------------------------------------------------------------------

   --  A record held in S, with the index where S holds it.
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

   procedure Lemma_Root_Void_Slot (S : State; K : Key256) is
   begin
      Lemma_Frontier_Shape (S);
      pragma Assert (Slot_Key (S, 1) = Founding (S));

      --  Flat to slot: the founding REVOKE is in the authorization rows (it
      --  is not data). It is in the slot that has its issuer as key. This
      --  is slot 1, because slot keys are distinct.
      if Root_Void (S, K) then
         declare
            I : constant Held_Count := Find_Root_Revoke (S, K);
         begin
            pragma Assert (I /= 0);
            Lemma_Held_Cases (S, I);
            if I <= Data_Count (S) then
               Lemma_Frontier_Data (S, I);
               pragma Assert (False);
            end if;
            declare
               Sl : constant Slot_Index := Slot_At (S, I);
               J  : constant Held_Index := I - Data_Count (S) - Off (S, Sl);
            begin
               pragma Assert (Held (S, I) = Auth_Held (S, Sl, J));
               Lemma_Frontier_Auth (S, Sl, J);
               pragma Assert (Slot_Key (S, Sl) = Founding (S));
               pragma Assert (Sl = 1);
               pragma Assert (Auth_Held (S, 1, J).K = K_Revoke
                              and then Auth_Held (S, 1, J).V.Author = K);
            end;
         end;
      end if;

      --  Slot to flat: a REVOKE of slot 1 is held, and Slot_Key (S, 1)
      --  issued it.
      for J in 1 .. Slot_Count (S, 1) loop
         Lemma_Held_Auth (S, 1, J);
         Lemma_Frontier_Auth (S, 1, J);
         if Auth_Held (S, 1, J).K = K_Revoke and then Auth_Held (S, 1, J).V.Author = K then
            pragma Assert
              (Root_Revokes (Held (S, Data_Count (S) + Off (S, 1) + J), Founding (S), K));
            pragma Assert (Find_Root_Revoke (S, K) /= 0);
         end if;
         pragma Loop_Invariant
           (for all J2 in 1 .. J =>
              (if Auth_Held (S, 1, J2).K = K_Revoke
                 and then Auth_Held (S, 1, J2).V.Author = K
               then Find_Root_Revoke (S, K) /= 0));
      end loop;
   end Lemma_Root_Void_Slot;

   procedure Lemma_No_Header_Not_Canonical is null;

   procedure Lemma_Roster_Lt_Total (A, B : Header) is
   begin
      Lemma_Gen_Lt_Total (A, B);
      pragma Assert (Lt (A.V.Author, B.V.Author) or else A.V.Author = B.V.Author
                     or else Lt (B.V.Author, A.V.Author));
   end Lemma_Roster_Lt_Total;

   procedure Lemma_Roster_Lt_Irrefl (A : Header) is
   begin
      Lemma_Gen_Lt_Irrefl (A);
      pragma Assert (not Lt (A.V.Author, A.V.Author));
   end Lemma_Roster_Lt_Irrefl;

   procedure Lemma_Dominates_Roster_Lt (P, Q : Header) is
   begin
      Lemma_Roster_Dom (P, Q);
      pragma Assert (P.Epoch <= Q.Epoch and then P.V.Seq < Q.V.Seq);
      pragma Assert (Gen_Lt (P, Q));
   end Lemma_Dominates_Roster_Lt;

   procedure Lemma_Cell_Unique (S : State; I, J : Held_Index) is
   begin
      Lemma_Frontier_Held (S, I);
      Lemma_Frontier_Held (S, J);
      --  Same cell, so a strictly newer version would dominate.
      pragma Assert (not Dominates (Held (S, J), Held (S, I)));
      pragma Assert (not Dominates (Held (S, I), Held (S, J)));
      pragma Assert (not Lt (Held (S, I).V, Held (S, J).V));
      pragma Assert (not Lt (Held (S, J).V, Held (S, I).V));
      Lemma_Trichotomy (Held (S, I).V, Held (S, J).V);
      pragma Assert (Held (S, I).V = Held (S, J).V);
      --  Canonical PUTs: Issuer and Del_TTL are zero.
      pragma Assert (Canonical (Held (S, I)) and then Canonical (Held (S, J)));
      pragma Assert (Held (S, I) = Held (S, J));
      pragma Assert (I = J);
   end Lemma_Cell_Unique;

   procedure Lemma_Del_Unique (S : State; I, J : Held_Index) is
   begin
      Lemma_Frontier_Held (S, I);
      Lemma_Frontier_Held (S, J);
      pragma Assert (not Dominates (Held (S, J), Held (S, I)));
      pragma Assert (not Dominates (Held (S, I), Held (S, J)));
      pragma Assert (not Lt (Held (S, I).V, Held (S, J).V));
      pragma Assert (not Lt (Held (S, J).V, Held (S, I).V));
      Lemma_Trichotomy (Held (S, I).V, Held (S, J).V);
      pragma Assert (Held (S, I).V = Held (S, J).V);
      --  Canonical DELs: FH, Issuer and Del_TTL are zero.
      pragma Assert (Canonical (Held (S, I)) and then Canonical (Held (S, J)));
      pragma Assert (Held (S, I) = Held (S, J));
      pragma Assert (I = J);
   end Lemma_Del_Unique;

   --  Two canonical rosters of one collection that are equal in
   --  (V, Del_TTL) are one record: Ent and FH are zero and Issuer is
   --  V.Author.
   procedure Lemma_Roster_Eq (X, Y : Header) with
     Ghost, Global => null,
     Pre  => X.K = K_Roster and then Y.K = K_Roster
             and then Canonical (X) and then Canonical (Y)
             and then X.NS = Y.NS
             and then X.V = Y.V and then X.Del_TTL = Y.Del_TTL
             and then X.Epoch = Y.Epoch,
     Post => X = Y
   is
   begin
      null;
   end Lemma_Roster_Eq;

   procedure Lemma_Roster_Unique (S : State; I, J : Held_Index) is
   begin
      Lemma_Roster_Lt_Total (Held (S, I), Held (S, J));
      Lemma_Frontier_Held (S, I);
      Lemma_Frontier_Held (S, J);
      Lemma_Roster_Eq (Held (S, I), Held (S, J));
      pragma Assert (Held (S, I) = Held (S, J));
      pragma Assert (I = J);
   end Lemma_Roster_Unique;

   procedure Lemma_Roster_Eff_Unique (S : State; I : Held_Index) is
      K : constant Held_Count := Find_Roster (S);
   begin
      pragma Assert (K /= 0);
      pragma Assert (not Roster_Lt (Held (S, I), Held (S, K)));
      pragma Assert (not Roster_Lt (Held (S, K), Held (S, I)));
      Lemma_Roster_Unique (S, I, K);
      pragma Assert (Held (S, I) = Held (S, K));
   end Lemma_Roster_Eff_Unique;

   procedure Lemma_Roster_Eff_Present (S : State) is
   begin
      --  The founding key is never root_void, so each founding roster is
      --  eligible. Find_Roster finds an eligible roster if there is one.
      pragma Assert (not Root_Void (S, Founding (S)));
      pragma Assert
        (for all I in 1 .. Count (S) =>
           (if Held (S, I).K = K_Roster and then Held (S, I).Issuer = Founding (S)
            then Eligible (S, Held (S, I))));
      pragma Assert (Find_Roster (S) /= 0);
   end Lemma_Roster_Eff_Present;

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

      --  deleted_at: the other side holds each maximum. Neither version is
      --  below the other, so they are equal.
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

      --  exists: a witness on one side is a witness on the other side.
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

   --  Unique_Versions instantiated at two indices. It is separate, so that
   --  the prover unfolds the quantifier in a small context.
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
         --  S1 holds the two maxima (at I1 and at J), with the same version
         --  and on the same cell.
         declare
            J : constant Held_Count := Index_Of (S1, Held (S2, I2));
         begin
            pragma Assert (Held (S1, I1).V = Held (S1, J).V);
            pragma Assert (Put_On (Held (S1, J), NS, Ent, FH));
            if Unique_Versions (S1) then
               Lemma_A2 (S1, I1, J);
               pragma Assert (Held (S1, I1) = Held (S1, J));
            end if;
            if Is_Frontier (S1) then
               Lemma_Frontier_Held (S1, I1);
               Lemma_Frontier_Held (S1, J);
               pragma Assert (Canonical (Held (S1, I1)) and then Canonical (Held (S1, J)));
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

   procedure Lemma_Root_Void_Local (S1, S2 : State; K : Key256) is
      I1 : constant Held_Count := Find_Root_Revoke (S1, K);
      I2 : constant Held_Count := Find_Root_Revoke (S2, K);
   begin
      --  Same_Auth, unfolded.
      pragma Assert (Founding (S1) = Founding (S2));
      pragma Assert
        (for all I in 1 .. Count (S1) =>
           (if Is_Auth (Held (S1, I)) then Holds (S2, Held (S1, I))));
      pragma Assert
        (for all I in 1 .. Count (S2) =>
           (if Is_Auth (Held (S2, I)) then Holds (S1, Held (S2, I))));
      if I1 /= 0 then
         declare
            J : constant Held_Count := Index_Of (S2, Held (S1, I1));
         begin
            pragma Assert (Root_Revokes (Held (S2, J), Founding (S2), K));
            pragma Assert (I2 /= 0);
         end;
      end if;
      if I2 /= 0 then
         declare
            J : constant Held_Count := Index_Of (S1, Held (S2, I2));
         begin
            pragma Assert (Root_Revokes (Held (S1, J), Founding (S1), K));
            pragma Assert (I1 /= 0);
         end;
      end if;
   end Lemma_Root_Void_Local;

   procedure Lemma_W_Eff_Local (S1, S2 : State; K : Key256) is
      I1 : constant Held_Count := Find_Grant (S1, K);
      I2 : constant Held_Count := Find_Grant (S2, K);
   begin
      pragma Assert
        (for all I in 1 .. Count (S1) =>
           (if Is_Auth (Held (S1, I)) then Holds (S2, Held (S1, I))));
      pragma Assert
        (for all I in 1 .. Count (S2) =>
           (if Is_Auth (Held (S2, I)) then Holds (S1, Held (S2, I))));
      if I1 /= 0 then
         declare
            X : constant Header := Held (S1, I1);
            J : constant Held_Count := Index_Of (S2, X);
         begin
            Lemma_Root_Void_Local (S1, S2, X.Issuer);
            pragma Assert (Grants (Held (S2, J), K)
                           and then not Root_Void (S2, Held (S2, J).Issuer));
            pragma Assert (I2 /= 0);
         end;
      end if;
      if I2 /= 0 then
         declare
            X : constant Header := Held (S2, I2);
            J : constant Held_Count := Index_Of (S1, X);
         begin
            Lemma_Root_Void_Local (S1, S2, X.Issuer);
            pragma Assert (Grants (Held (S1, J), K)
                           and then not Root_Void (S1, Held (S1, J).Issuer));
            pragma Assert (I1 /= 0);
         end;
      end if;
   end Lemma_W_Eff_Local;

   procedure Lemma_Void_Local (S1, S2 : State; P : Header) is
      I1 : constant Held_Count := Find_Void (S1, P);
      I2 : constant Held_Count := Find_Void (S2, P);
   begin
      pragma Assert
        (for all I in 1 .. Count (S1) =>
           (if Is_Auth (Held (S1, I)) then Holds (S2, Held (S1, I))));
      pragma Assert
        (for all I in 1 .. Count (S2) =>
           (if Is_Auth (Held (S2, I)) then Holds (S1, Held (S2, I))));
      if I1 /= 0 then
         declare
            X : constant Header := Held (S1, I1);
            J : constant Held_Count := Index_Of (S2, X);
         begin
            Lemma_Root_Void_Local (S1, S2, X.Issuer);
            pragma Assert (Voids (Held (S2, J), P)
                           and then not Root_Void (S2, Held (S2, J).Issuer));
            pragma Assert (I2 /= 0);
         end;
      end if;
      if I2 /= 0 then
         declare
            X : constant Header := Held (S2, I2);
            J : constant Held_Count := Index_Of (S1, X);
         begin
            Lemma_Root_Void_Local (S1, S2, X.Issuer);
            pragma Assert (Voids (Held (S1, J), P)
                           and then not Root_Void (S1, Held (S1, J).Issuer));
            pragma Assert (I1 /= 0);
         end;
      end if;
      pragma Assert (Revoke_Void (S1, P) = Revoke_Void (S2, P));
      Lemma_W_Eff_Local (S1, S2, P.V.Author);
   end Lemma_Void_Local;

   procedure Lemma_Roster_Local (S1, S2 : State) is
      I1 : constant Held_Count := Find_Roster (S1);
      I2 : constant Held_Count := Find_Roster (S2);
   begin
      pragma Assert
        (for all I in 1 .. Count (S1) =>
           (if Is_Auth (Held (S1, I)) then Holds (S2, Held (S1, I))));
      pragma Assert
        (for all I in 1 .. Count (S2) =>
           (if Is_Auth (Held (S2, I)) then Holds (S1, Held (S2, I))));

      --  The result of each side is held and eligible on the other side, so
      --  it makes the other side present, and no roster beats it there.
      if I1 /= 0 then
         declare
            X : constant Header := Held (S1, I1);
            J : constant Held_Count := Index_Of (S2, X);
         begin
            Lemma_Root_Void_Local (S1, S2, X.Issuer);
            pragma Assert (Eligible (S2, Held (S2, J)));
            pragma Assert (I2 /= 0);
            pragma Assert (not Roster_Lt (Held (S2, I2), X));
         end;
      end if;
      if I2 /= 0 then
         declare
            X : constant Header := Held (S2, I2);
            J : constant Held_Count := Index_Of (S1, X);
         begin
            Lemma_Root_Void_Local (S1, S2, X.Issuer);
            pragma Assert (Eligible (S1, Held (S1, J)));
            pragma Assert (I1 /= 0);
            pragma Assert (not Roster_Lt (Held (S1, I1), X));
         end;
      end if;
      pragma Assert ((I1 = 0) = (I2 = 0));

      if I1 /= 0 then
         Lemma_Roster_Lt_Total (Held (S1, I1), Held (S2, I2));
         pragma Assert (Held (S1, I1).V = Held (S2, I2).V);
         pragma Assert (Held (S1, I1).Del_TTL = Held (S2, I2).Del_TTL);
         declare
            J : constant Held_Count := Index_Of (S1, Held (S2, I2));
         begin
            pragma Assert (Held (S1, I1).V = Held (S1, J).V);
            if Unique_Versions (S1) then
               Lemma_A2 (S1, I1, J);
               pragma Assert (Held (S1, I1) = Held (S2, I2));
            end if;
            if Is_Frontier (S1) then
               Lemma_Frontier_Held (S1, I1);
               Lemma_Frontier_Held (S1, J);
               Lemma_Roster_Eq (Held (S1, I1), Held (S1, J));
               pragma Assert (Held (S1, I1) = Held (S2, I2));
            end if;
         end;
      end if;
   end Lemma_Roster_Local;

   procedure Lemma_Dominates_Del_TTL (P, Q : Header) is
   begin
      Lemma_Roster_Dom (P, Q);
   end Lemma_Dominates_Del_TTL;

   --  To apply a record that is not a REVOKE keeps root_void: each REVOKE
   --  of Before is in After (nothing dominates a REVOKE), and each REVOKE
   --  of After is in Before (R is not one).
   procedure Lemma_Root_Void_Apply (Before, After : State; R : Header; K : Key256) with
     Ghost, Global => null,
     Pre  => R.K /= K_Revoke
             and then Founding (After) = Founding (Before)
             and then (for all I in 1 .. Count (After) =>
                         Holds (Before, Held (After, I)) or else Held (After, I) = R)
             and then (for all I in 1 .. Count (Before) =>
                         Holds (After, Held (Before, I))
                         or else Dominates (R, Held (Before, I))),
     Post => Root_Void (After, K) = Root_Void (Before, K)
   is
      I1 : constant Held_Count := Find_Root_Revoke (Before, K);
      I2 : constant Held_Count := Find_Root_Revoke (After, K);
   begin
      if I1 /= 0 then
         pragma Assert (Held (Before, I1).K = K_Revoke);
         pragma Assert (not Dominates (R, Held (Before, I1)));
         pragma Assert (Holds (After, Held (Before, I1)));
         declare
            J : constant Held_Count := Index_Of (After, Held (Before, I1));
         begin
            pragma Assert (Root_Revokes (Held (After, J), Founding (After), K));
            pragma Assert (I2 /= 0);
         end;
      end if;
      if I2 /= 0 then
         pragma Assert (Held (After, I2).K = K_Revoke);
         pragma Assert (Held (After, I2) /= R);
         pragma Assert (Holds (Before, Held (After, I2)));
         declare
            J : constant Held_Count := Index_Of (Before, Held (After, I2));
         begin
            pragma Assert (Root_Revokes (Held (Before, J), Founding (Before), K));
            pragma Assert (I1 /= 0);
         end;
      end if;
      pragma Assert ((I1 = 0) = (I2 = 0));
   end Lemma_Root_Void_Apply;

   procedure Lemma_Del_TTL_Eff_Apply (Before, After : State; R : Header) is
      IB : constant Held_Count := Find_TTL (Before);
      IA : constant Held_Count := Find_TTL (After);
      JR : constant Held_Count := Index_Of (After, R);
   begin
      --  R, if eligible, is at most the maximum of After.
      if Eligible (After, R) then
         pragma Assert (Eligible (After, Held (After, JR)));
         pragma Assert (IA /= 0);
         pragma Assert (R.Del_TTL <= Held (After, IA).Del_TTL);
         pragma Assert (R.Del_TTL <= Del_TTL_Eff (After));
      end if;

      --  (1) Each eligible roster of Before is at most the maximum of
      --  After: it is held in After and eligible there (root_void is the
      --  same), or R dominates it, and then R has the same signer, so R is
      --  eligible, and R is not lower in del_ttl.
      for I in 1 .. Count (Before) loop
         --  The invariant comes first: gnatprove 14 does not support a
         --  non-scalar object (X below) declared before it.
         pragma Loop_Invariant
           (for all J in 1 .. I - 1 =>
              (if Eligible (Before, Held (Before, J))
               then IA /= 0
                    and then Held (Before, J).Del_TTL <= Held (After, IA).Del_TTL));
         if Eligible (Before, Held (Before, I)) then
            declare
               X : constant Header := Held (Before, I);
            begin
               Lemma_Root_Void_Apply (Before, After, R, X.Issuer);
               if Holds (After, X) then
                  declare
                     J : constant Held_Count := Index_Of (After, X);
                  begin
                     pragma Assert (Eligible (After, Held (After, J)));
                     pragma Assert (IA /= 0);
                     pragma Assert (X.Del_TTL <= Held (After, IA).Del_TTL);
                  end;
               else
                  pragma Assert (Dominates (R, X));
                  Lemma_Dominates_Del_TTL (X, R);
                  Lemma_Frontier_Held (Before, I);
                  Lemma_Frontier_Held (After, JR);
                  pragma Assert (Canonical (X) and then Canonical (R));
                  pragma Assert (R.Issuer = R.V.Author and then X.Issuer = X.V.Author);
                  pragma Assert (R.V.Author = X.V.Author);
                  pragma Assert (R.Issuer = X.Issuer);
                  pragma Assert (Eligible (After, R));
                  pragma Assert (IA /= 0);
                  pragma Assert (X.Del_TTL <= R.Del_TTL);
                  pragma Assert (X.Del_TTL <= Held (After, IA).Del_TTL);
               end if;
            end;
         end if;
         pragma Assert
           (if Eligible (Before, Held (Before, I))
            then IA /= 0
                 and then Held (Before, I).Del_TTL <= Held (After, IA).Del_TTL);
      end loop;
      pragma Assert
        (for all J in 1 .. Count (Before) =>
           (if Eligible (Before, Held (Before, J))
            then IA /= 0
                 and then Held (Before, J).Del_TTL <= Del_TTL_Eff (After)));

      --  (2) If Before has an eligible roster, its maximum is one of them.
      if IB /= 0 then
         pragma Assert (Eligible (Before, Held (Before, IB)));
         pragma Assert (IA /= 0);
         pragma Assert (Held (Before, IB).Del_TTL <= Held (After, IA).Del_TTL);
         pragma Assert (Del_TTL_Eff (Before) <= Del_TTL_Eff (After));
      end if;

      --  (3) The maximum of After is R, or a roster of Before that was
      --  already its maximum there.
      if IA = 0 then
         --  No eligible roster in After, so none in Before (1), so both
         --  values are the default.
         pragma Assert (IB = 0);
         pragma Assert (Del_TTL_Eff (After) = Del_TTL_Eff (Before));
      else
         declare
            X : constant Header := Held (After, IA);
         begin
            if X = R then
               pragma Assert (Eligible (After, R));
               pragma Assert (Del_TTL_Eff (After) = R.Del_TTL);
            else
               pragma Assert (Holds (Before, X));
               declare
                  J : constant Held_Count := Index_Of (Before, X);
               begin
                  Lemma_Root_Void_Apply (Before, After, R, X.Issuer);
                  pragma Assert (Eligible (Before, Held (Before, J)));
                  pragma Assert (IB /= 0);
                  pragma Assert (X.Del_TTL <= Held (Before, IB).Del_TTL);
                  pragma Assert (Held (Before, IB).Del_TTL <= Held (After, IA).Del_TTL);
                  pragma Assert (Held (Before, IB).Del_TTL = X.Del_TTL);
                  pragma Assert (Del_TTL_Eff (After) = Del_TTL_Eff (Before));
               end;
            end if;
         end;
      end if;
   end Lemma_Del_TTL_Eff_Apply;

   procedure Lemma_Del_TTL_Local (S1, S2 : State) is
      I1 : constant Held_Count := Find_TTL (S1);
      I2 : constant Held_Count := Find_TTL (S2);
   begin
      pragma Assert
        (for all I in 1 .. Count (S1) =>
           (if Is_Auth (Held (S1, I)) then Holds (S2, Held (S1, I))));
      pragma Assert
        (for all I in 1 .. Count (S2) =>
           (if Is_Auth (Held (S2, I)) then Holds (S1, Held (S2, I))));
      if I1 /= 0 then
         declare
            X : constant Header := Held (S1, I1);
            J : constant Held_Count := Index_Of (S2, X);
         begin
            Lemma_Root_Void_Local (S1, S2, X.Issuer);
            pragma Assert (Eligible (S2, Held (S2, J)));
            pragma Assert (I2 /= 0);
            pragma Assert (X.Del_TTL <= Held (S2, I2).Del_TTL);
         end;
      end if;
      if I2 /= 0 then
         declare
            X : constant Header := Held (S2, I2);
            J : constant Held_Count := Index_Of (S1, X);
         begin
            Lemma_Root_Void_Local (S1, S2, X.Issuer);
            pragma Assert (Eligible (S1, Held (S1, J)));
            pragma Assert (I1 /= 0);
            pragma Assert (X.Del_TTL <= Held (S1, I1).Del_TTL);
         end;
      end if;
      pragma Assert ((I1 = 0) = (I2 = 0));
   end Lemma_Del_TTL_Local;

   procedure Lemma_Apply_Auth_Local (Before, After : State; R : Header) is
   begin
      --  After ⊆ Before ∪ {R}, and R is not data, so Before holds each
      --  data record of After.
      pragma Assert
        (for all I in 1 .. Count (After) =>
           (if Is_Data (Held (After, I)) then Holds (Before, Held (After, I))));
      --  Before ⊆ After for data: only a data record can dominate a data
      --  record, and R is not a data record.
      pragma Assert
        (for all I in 1 .. Count (Before) =>
           (if Is_Data (Held (Before, I)) then not Dominates (R, Held (Before, I))));
      pragma Assert
        (for all I in 1 .. Count (Before) =>
           (if Is_Data (Held (Before, I)) then Holds (After, Held (Before, I))));
   end Lemma_Apply_Auth_Local;

   procedure Lemma_Apply_Data_Local (Before, After : State; R : Header) is
   begin
      pragma Assert
        (for all I in 1 .. Count (After) =>
           (if Is_Auth (Held (After, I)) then Holds (Before, Held (After, I))));
      --  Only a record of the same kind can dominate an authorization record
      --  (nothing dominates a REVOKE), and R is data.
      pragma Assert
        (for all I in 1 .. Count (Before) =>
           (if Is_Auth (Held (Before, I)) then not Dominates (R, Held (Before, I))));
      pragma Assert
        (for all I in 1 .. Count (Before) =>
           (if Is_Auth (Held (Before, I)) then Holds (After, Held (Before, I))));
   end Lemma_Apply_Data_Local;

   procedure Lemma_Root_Void_Monotone (S1, S2 : State; K : Key256) is
   begin
      if Root_Void (S1, K) then
         declare
            I : constant Held_Count := Find_Root_Revoke (S1, K);
            J : constant Held_Count := Index_Of (S2, Held (S1, I));
         begin
            pragma Assert (Root_Revokes (Held (S2, J), Founding (S2), K));
            pragma Assert (Find_Root_Revoke (S2, K) /= 0);
         end;
      end if;
   end Lemma_Root_Void_Monotone;

   procedure Lemma_W_Eff_Monotone (S1, S2 : State; K : Key256) is
   begin
      if W_Eff (S1, K) then
         declare
            I : constant Held_Count := Find_Grant (S1, K);
            J : constant Held_Count := Index_Of (S2, Held (S1, I));
         begin
            pragma Assert (Grants (Held (S2, J), K)
                           and then not Root_Void (S2, Held (S2, J).Issuer));
            pragma Assert (Find_Grant (S2, K) /= 0);
         end;
      end if;
   end Lemma_W_Eff_Monotone;

   procedure Lemma_Void_Monotone (S1, S2 : State; P : Header) is
   begin
      if Revoke_Void (S1, P) then
         declare
            I : constant Held_Count := Find_Void (S1, P);
            J : constant Held_Count := Index_Of (S2, Held (S1, I));
         begin
            pragma Assert (Voids (Held (S2, J), P)
                           and then not Root_Void (S2, Held (S2, J).Issuer));
            pragma Assert (Find_Void (S2, P) /= 0);
         end;
      end if;
   end Lemma_Void_Monotone;

   procedure Lemma_Apply_Keeps_Revokes (Before, After : State; R : Header) is
   begin
      --  Nothing dominates a REVOKE.
      pragma Assert
        (for all I in 1 .. Count (Before) =>
           (if Held (Before, I).K = K_Revoke then not Dominates (R, Held (Before, I))));
   end Lemma_Apply_Keeps_Revokes;

end Kome.Views;
