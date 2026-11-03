pragma Ada_2022;
package body Kome.Frontier with SPARK_Mode is

   --  Proof style, learned the hard way (CONVENTIONS.md): every quantified
   --  definition lives in this body, out of the clients' view; each state
   --  change is followed by "bridge" assertions relating the new state to
   --  the old one; and every "some record" in an invariant is a named index
   --  held in a ghost witness array (Src: where a kept record came from;
   --  Dst: where an old record went, 0 if it was dropped).

   Null_Header : constant Header := (others => <>);

   pragma Compile_Time_Error
     (Signers_Max /= 16, "Flat_Slot below is written out for 16 slots");

   ---------------------------------------------------------------------
   --  The rows and the flat view
   ---------------------------------------------------------------------

   --  Row 0 is the data row, rows 1 .. Signers_Max the slots.
   function Row_Count (S : State; K : Slot_Number) return Natural is
     (if K = 0 then Data_Count (S) else SC (S.A, K));

   function Row_At (S : State; K : Slot_Number; J : Integer) return Header is
     (if K = 0 then (if J in 1 .. Data_Count (S) then S.Data_H (J) else Null_Header)
      elsif J in 1 .. SC (S.A, K) then S.A.H (K, J)
      else Null_Header);

   --  The slot an authorization position J (counted after the data row)
   --  falls in: the first K with J <= Offs (K + 1), else the last slot.
   function Flat_Slot (S : State; J : Integer) return Slot_Index is
     (if    J <= S.A.Offs (2)  then 1
      elsif J <= S.A.Offs (3)  then 2
      elsif J <= S.A.Offs (4)  then 3
      elsif J <= S.A.Offs (5)  then 4
      elsif J <= S.A.Offs (6)  then 5
      elsif J <= S.A.Offs (7)  then 6
      elsif J <= S.A.Offs (8)  then 7
      elsif J <= S.A.Offs (9)  then 8
      elsif J <= S.A.Offs (10) then 9
      elsif J <= S.A.Offs (11) then 10
      elsif J <= S.A.Offs (12) then 11
      elsif J <= S.A.Offs (13) then 12
      elsif J <= S.A.Offs (14) then 13
      elsif J <= S.A.Offs (15) then 14
      elsif J <= S.A.Offs (16) then 15
      else 16);

   function Row_Of (S : State; I : Held_Index) return Slot_Number is
     (if I <= Data_Count (S) then 0 else Flat_Slot (S, I - Data_Count (S)));

   function Pos_Of (S : State; I : Held_Index) return Integer is
     (if I <= Data_Count (S) then I
      else I - Data_Count (S) - S.A.Offs (Flat_Slot (S, I - Data_Count (S))));

   function Flat_Index (S : State; K : Slot_Number; J : Held_Count) return Integer is
     (if K = 0 then J else Data_Count (S) + S.A.Offs (K) + J);

   function Held (S : State; I : Held_Index) return Header is
     (Row_At (S, Row_Of (S, I), Pos_Of (S, I)));

   function Slot_At (S : State; I : Held_Index) return Slot_Index is
     (if I <= Data_Count (S) then 1 else Flat_Slot (S, I - Data_Count (S)));

   function Slot_Of (S : State; Key : Key256) return Slot_Number is
   begin
      for K in 1 .. S.A.NSlots loop
         if S.A.Keys (K) = Key then
            return K;
         end if;
         pragma Loop_Invariant (for all K2 in 1 .. K => S.A.Keys (K2) /= Key);
      end loop;
      return 0;
   end Slot_Of;

   ---------------------------------------------------------------------
   --  The invariant
   ---------------------------------------------------------------------

   --  Capacities and the slot offsets of the authorization rows.
   function Auth_Shape (A : Auth_Rows) return Boolean is
     (A.Slice >= 1
      and then A.NSlots >= 1
      and then (for all K in Slot_Index => A.NA (K) <= A.Slice)
      and then (for all K in Slot_Index => (if K > A.NSlots then A.NA (K) = 0))
      and then A.Offs (1) = 0
      and then (for all K in 2 .. Signers_Max => A.Offs (K) = A.Offs (K - 1) + A.NA (K - 1))
      and then (for all K in Slot_Index => A.Offs (K) <= (K - 1) * A.Slice)
      and then A.NAuth = A.Offs (Signers_Max) + A.NA (Signers_Max));

   function Shape (S : State) return Boolean is
     (Auth_Shape (S.A)
      and then S.A.Slice = S.Slice
      and then S.Cap + Signers_Max * S.Slice <= Held_Max
      and then S.ND <= S.Cap);

   function Slots_OK (A : Auth_Rows; Fnd : Key256) return Boolean is
     (A.Keys (1) = Fnd
      and then (for all K in 1 .. A.NSlots =>
                  (for all K2 in 1 .. A.NSlots =>
                     (if K /= K2 then A.Keys (K) /= A.Keys (K2))))
      and then (for all K in 2 .. A.NSlots => A.NA (K) >= 1));

   function Data_Item_OK (S : State; X : Header) return Boolean is
     (Is_Data (X) and then Canonical (X) and then X.NS = S.NS
      and then Admitted (S, X));

   function Data_OK (S : State) return Boolean is
     ((for all I in 1 .. Data_Count (S) => Data_Item_OK (S, S.Data_H (I)))
      and then (for all I in 1 .. Data_Count (S) =>
                  (for all I2 in 1 .. Data_Count (S) =>
                     not Dominates (S.Data_H (I2), S.Data_H (I))))
      and then (for all I in 1 .. Data_Count (S) =>
                  (for all I2 in 1 .. Data_Count (S) =>
                     (if I /= I2 then S.Data_H (I) /= S.Data_H (I2)))));

   function Auth_Item_OK (S : State; K : Slot_Index; X : Header) return Boolean is
     (Is_Auth (X) and then Canonical (X) and then X.NS = S.NS
      and then X.Issuer = S.A.Keys (K));

   --  Each slot holds canonical authorization records of this collection
   --  issued by its key, as an antichain without repetition. Written flat
   --  (no per-row predicate under the quantifier), which the provers need.
   function Auth_OK (A : Auth_Rows; NS : Id128) return Boolean is
     ((for all K in Slot_Index =>
         (for all J in 1 .. SC (A, K) =>
            Is_Auth (A.H (K, J)) and then Canonical (A.H (K, J))
            and then A.H (K, J).NS = NS and then A.H (K, J).Issuer = A.Keys (K)))
      and then (for all K in Slot_Index =>
                  (for all J in 1 .. SC (A, K) =>
                     (for all J2 in 1 .. SC (A, K) =>
                        not Dominates (A.H (K, J2), A.H (K, J)))))
      and then (for all K in Slot_Index =>
                  (for all J in 1 .. SC (A, K) =>
                     (for all J2 in 1 .. SC (A, K) =>
                        (if J /= J2 then A.H (K, J) /= A.H (K, J2))))));

   function Roster_At (A : Auth_Rows; C : U48) return Boolean is
     (for some K in Slot_Index =>
        (for some J in 1 .. SC (A, K) =>
           A.H (K, J).K = K_Roster and then A.H (K, J).V.T = C));

   function Grant_Of (A : Auth_Rows; W : Key256) return Boolean is
     (for some K in Slot_Index =>
        (for some J in 1 .. SC (A, K) =>
           A.H (K, J).K = K_Grant and then A.H (K, J).V.Author = W));

   --  The register cache equals the views maxceil(F) and W(F).
   function Coherent (A : Auth_Rows; RG : Register_File) return Boolean is
     ((for all K in Slot_Index =>
         (for all J in 1 .. SC (A, K) => Ceil_Of (A.H (K, J)) <= Ceil (RG)))
      and then (for all K in Slot_Index =>
                  (for all J in 1 .. SC (A, K) =>
                     (if A.H (K, J).K = K_Grant then In_W (RG, A.H (K, J).V.Author))))
      and then (Ceil (RG) = 0 or else Roster_At (A, Ceil (RG)))
      and then (for all I in 1 .. Registers.Count (RG) => Grant_Of (A, Writer (RG, I))));

   function Is_Frontier (S : State) return Boolean is
     (Shape (S) and then Slots_OK (S.A, S.Fnd) and then Data_OK (S)
      and then Auth_OK (S.A, S.NS) and then Coherent (S.A, S.RG));

   function Drops_Any (S : State; R : Header) return Boolean is
     (for some I in 1 .. Count (S) => Dominates (R, Held (S, I)));

   function Unchanged (Old, Upd : State) return Boolean is
     (Old.Cap = Upd.Cap and then Old.Slice = Upd.Slice
      and then Old.NS = Upd.NS and then Old.Fnd = Upd.Fnd
      and then Old.RG = Upd.RG
      and then Old.ND = Upd.ND
      and then (for all I in 1 .. Data_Count (Old) => Upd.Data_H (I) = Old.Data_H (I))
      and then Old.A.NSlots = Upd.A.NSlots
      and then (for all K in Slot_Index =>
                  Upd.A.NA (K) = Old.A.NA (K) and then Upd.A.Keys (K) = Old.A.Keys (K)
                  and then Upd.A.Offs (K) = Old.A.Offs (K))
      and then (for all K in Slot_Index =>
                  (for all J in 1 .. Slot_Count (Old, K) =>
                     Upd.A.H (K, J) = Old.A.H (K, J)))
      and then Old.A.NAuth = Upd.A.NAuth);

   ---------------------------------------------------------------------
   --  Lemmas on the flat view
   ---------------------------------------------------------------------

   --  The slot intervals (Offs (K), Offs (K) + NA (K)] are consecutive.
   procedure Lemma_Off_Mono (S : State) with
     Ghost, Global => null,
     Pre  => Shape (S),
     Post => (for all K1 in Slot_Index =>
                (for all K2 in Slot_Index =>
                   (if K1 < K2 then S.A.Offs (K1) + S.A.NA (K1) <= S.A.Offs (K2))))
             and then (for all K in Slot_Index => S.A.Offs (K) + S.A.NA (K) <= S.A.NAuth)
             and then S.A.NAuth <= Signers_Max * S.Slice
             and then Data_Count (S) = S.ND
             and then Auth_Count (S) = S.A.NAuth
             and then Count (S) = S.ND + S.A.NAuth
             and then (for all K in Slot_Index => Slot_Count (S, K) = S.A.NA (K))
   is
   begin
      for K2 in 2 .. Signers_Max loop
         pragma Assert (S.A.Offs (K2) = S.A.Offs (K2 - 1) + S.A.NA (K2 - 1));
         pragma Loop_Invariant
           (for all K in 2 .. K2 =>
              (for all K1 in 1 .. K - 1 => S.A.Offs (K1) + S.A.NA (K1) <= S.A.Offs (K)));
      end loop;
      pragma Assert (S.A.Offs (Signers_Max) <= (Signers_Max - 1) * S.Slice);
   end Lemma_Off_Mono;

   --  Flat_Slot finds the slot interval a position falls in.
   procedure Lemma_Flat_Slot (S : State; J : Integer) with
     Ghost, Global => null,
     Pre  => Shape (S) and then J in 1 .. S.A.NAuth,
     Post => S.A.Offs (Flat_Slot (S, J)) < J
             and then J <= S.A.Offs (Flat_Slot (S, J)) + S.A.NA (Flat_Slot (S, J))
             and then Flat_Slot (S, J) <= S.A.NSlots
   is
   begin
      null;
   end Lemma_Flat_Slot;

   --  ... and that slot is unique.
   procedure Lemma_Flat_Unique (S : State; K : Slot_Index; J : Integer) with
     Ghost, Global => null,
     Pre  => Shape (S) and then J in 1 .. S.A.NA (K),
     Post => S.A.Offs (K) + J <= S.A.NAuth and then Flat_Slot (S, S.A.Offs (K) + J) = K
   is
   begin
      Lemma_Off_Mono (S);
      Lemma_Flat_Slot (S, S.A.Offs (K) + J);
   end Lemma_Flat_Unique;

   --  Row position (K, J) is flat index Flat_Index (S, K, J).
   procedure Lemma_Row_Flat (S : State; K : Slot_Number; J : Integer) with
     Ghost, Global => null,
     Pre  => Shape (S) and then J in 1 .. Row_Count (S, K),
     Post => K <= S.A.NSlots
             and then Flat_Index (S, K, J) in 1 .. Count (S)
             and then Row_Of (S, Flat_Index (S, K, J)) = K
             and then Pos_Of (S, Flat_Index (S, K, J)) = J
             and then Held (S, Flat_Index (S, K, J)) = Row_At (S, K, J)
   is
   begin
      Lemma_Off_Mono (S);
      if K /= 0 then
         Lemma_Flat_Unique (S, K, J);
      end if;
   end Lemma_Row_Flat;

   --  Flat index I is row position (Row_Of, Pos_Of).
   procedure Lemma_Flat_Row (S : State; I : Held_Index) with
     Ghost, Global => null,
     Pre  => Shape (S) and then I <= Count (S),
     Post => Row_Of (S, I) <= S.A.NSlots
             and then Pos_Of (S, I) in 1 .. Row_Count (S, Row_Of (S, I))
             and then Held (S, I) = Row_At (S, Row_Of (S, I), Pos_Of (S, I))
             and then Flat_Index (S, Row_Of (S, I), Pos_Of (S, I)) = I
   is
   begin
      Lemma_Off_Mono (S);
      if I > Data_Count (S) then
         Lemma_Flat_Slot (S, I - Data_Count (S));
      end if;
   end Lemma_Flat_Row;

   --  Quantified form of Lemma_Flat_Row, for the whole view.
   procedure Lemma_All_Flat (S : State) with
     Ghost, Global => null,
     Pre  => Shape (S),
     Post => (for all I in 1 .. Count (S) =>
                Row_Of (S, I) <= S.A.NSlots
                and then Pos_Of (S, I) in 1 .. Row_Count (S, Row_Of (S, I))
                and then Held (S, I) = Row_At (S, Row_Of (S, I), Pos_Of (S, I)))
   is
   begin
      for I in 1 .. Count (S) loop
         Lemma_Flat_Row (S, I);
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              Row_Of (S, I2) <= S.A.NSlots
              and then Pos_Of (S, I2) in 1 .. Row_Count (S, Row_Of (S, I2))
              and then Held (S, I2) = Row_At (S, Row_Of (S, I2), Pos_Of (S, I2)));
      end loop;
   end Lemma_All_Flat;

   --  What a held row position is, by row.
   procedure Lemma_Item (S : State; K : Slot_Number; J : Integer) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S) and then J in 1 .. Row_Count (S, K),
     Post => K <= S.A.NSlots
             and then (if K = 0 then Data_Item_OK (S, Row_At (S, K, J))
                       else Auth_Item_OK (S, K, Row_At (S, K, J)))
             and then Admitted (S, Row_At (S, K, J))
   is
   begin
      Lemma_Off_Mono (S);
   end Lemma_Item;

   ---------------------------------------------------------------------
   --  Classification: which row a record can be held, dominated or
   --  dropping in (Kome.Headers.Lemma_Same_Row).
   ---------------------------------------------------------------------

   function Row_For (S : State; R : Header) return Slot_Number is
     (if Is_Data (R) then 0 else Slot_Of (S, R.Issuer));

   function Has_Row (S : State; R : Header) return Boolean is
     (Is_Data (R) or else Slot_Of (S, R.Issuer) /= 0);

   function In_Row (S : State; K : Slot_Number; X : Header) return Boolean is
     (if K = 0 then (for some J in 1 .. Data_Count (S) => S.Data_H (J) = X)
      else (for some J in 1 .. SC (S.A, K) => S.A.H (K, J) = X));

   function Dom_In_Row (S : State; K : Slot_Number; X : Header) return Boolean is
     (if K = 0 then (for some J in 1 .. Data_Count (S) => Dominates (S.Data_H (J), X))
      else (for some J in 1 .. SC (S.A, K) => Dominates (S.A.H (K, J), X)));

   function Drops_In_Row (S : State; K : Slot_Number; R : Header) return Boolean is
     (if K = 0 then (for some J in 1 .. Data_Count (S) => Dominates (R, S.Data_H (J)))
      else (for some J in 1 .. SC (S.A, K) => Dominates (R, S.A.H (K, J))));

   procedure Lemma_Classify (S : State; R : Header) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S) and then Canonical (R) and then R.NS = S.NS,
     Post => Holds (S, R) = (Has_Row (S, R) and then In_Row (S, Row_For (S, R), R))
             and then Dom (S, R) = (Has_Row (S, R) and then Dom_In_Row (S, Row_For (S, R), R))
             and then Drops_Any (S, R)
                      = (Has_Row (S, R) and then Drops_In_Row (S, Row_For (S, R), R))
   is
      RK : constant Slot_Number := Row_For (S, R);
   begin
      Lemma_Off_Mono (S);
      Lemma_All_Flat (S);
      --  Flat to row: a held record equal to, dominating or dominated by R
      --  is in R's row.
      for I in 1 .. Count (S) loop
         Lemma_Item (S, Row_Of (S, I), Pos_Of (S, I));
         if Held (S, I) = R then
            pragma Assert (Row_Of (S, I) = RK);
            pragma Assert (Has_Row (S, R));
         end if;
         if Dominates (Held (S, I), R) then
            Lemma_Same_Row (Held (S, I), R);
            pragma Assert (Row_Of (S, I) = RK);
            pragma Assert (Has_Row (S, R));
         end if;
         if Dominates (R, Held (S, I)) then
            Lemma_Same_Row (R, Held (S, I));
            pragma Assert (Row_Of (S, I) = RK);
            pragma Assert (Has_Row (S, R));
         end if;
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              (if Held (S, I2) = R
               then Has_Row (S, R) and then In_Row (S, RK, R)));
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              (if Dominates (Held (S, I2), R)
               then Has_Row (S, R) and then Dom_In_Row (S, RK, R)));
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              (if Dominates (R, Held (S, I2))
               then Has_Row (S, R) and then Drops_In_Row (S, RK, R)));
      end loop;
      pragma Assert (if Holds (S, R) then Has_Row (S, R) and then In_Row (S, RK, R));
      pragma Assert (if Dom (S, R) then Has_Row (S, R) and then Dom_In_Row (S, RK, R));
      pragma Assert
        (if Drops_Any (S, R) then Has_Row (S, R) and then Drops_In_Row (S, RK, R));

      --  Row to flat.
      if Has_Row (S, R) then
         for J in 1 .. Row_Count (S, RK) loop
            Lemma_Row_Flat (S, RK, J);
            Lemma_Item (S, RK, J);
            pragma Loop_Invariant
              (for all J2 in 1 .. J => (if Row_At (S, RK, J2) = R then Holds (S, R)));
            pragma Loop_Invariant
              (for all J2 in 1 .. J =>
                 (if Dominates (Row_At (S, RK, J2), R) then Dom (S, R)));
            pragma Loop_Invariant
              (for all J2 in 1 .. J =>
                 (if Dominates (R, Row_At (S, RK, J2)) then Drops_Any (S, R)));
         end loop;
         pragma Assert
           (for all J in 1 .. Row_Count (S, RK) =>
              Row_At (S, RK, J) = (if RK = 0 then S.Data_H (J) else S.A.H (RK, J)));
         pragma Assert
           (if In_Row (S, RK, R) then
              (for some J in 1 .. Row_Count (S, RK) => Row_At (S, RK, J) = R));
         pragma Assert (if In_Row (S, RK, R) then Holds (S, R));
      end if;
   end Lemma_Classify;

   ---------------------------------------------------------------------
   --  One step on one row K0: every other row is unchanged; row K0 keeps
   --  some of its old records (Src) and maybe appends R; Dst says where
   --  each old record of row K0 went (0: dropped).
   ---------------------------------------------------------------------

   type Index_Map is array (Positive range <>) of Natural with Ghost;

   function Step
     (Old, Upd : State; K0 : Slot_Number; R : Header; Src, Dst : Index_Map)
      return Boolean
   is
     (Src'First = 1 and then Dst'First = 1
      and then Src'Last >= Row_Count (Upd, K0)
      and then Dst'Last >= Row_Count (Old, K0)
      and then (for all K in Slot_Number =>
                  (if K /= K0 then
                     Row_Count (Upd, K) = Row_Count (Old, K)
                     and then (for all J in 1 .. Row_Count (Old, K) =>
                                 Row_At (Upd, K, J) = Row_At (Old, K, J))))
      and then (for all J in 1 .. Row_Count (Upd, K0) =>
                  (if Src (J) = 0 then Row_At (Upd, K0, J) = R
                   else Src (J) <= Row_Count (Old, K0)
                        and then Row_At (Upd, K0, J) = Row_At (Old, K0, Src (J))))
      and then (for all J in 1 .. Row_Count (Old, K0) =>
                  (if Dst (J) /= 0 then
                     Dst (J) <= Row_Count (Upd, K0)
                     and then Row_At (Upd, K0, Dst (J)) = Row_At (Old, K0, J))))
   with Ghost;

   --  The step in the flat view: Frontier.lean `keep`.
   procedure Lemma_Step_Flat
     (Old, Upd : State; K0 : Slot_Number; R : Header; Src, Dst : Index_Map)
   with
     Ghost, Global => null,
     Pre  => Shape (Old) and then Shape (Upd)
             and then Step (Old, Upd, K0, R, Src, Dst),
     Post => (for all I in 1 .. Count (Upd) =>
                Holds (Old, Held (Upd, I))
                or else (Row_Of (Upd, I) = K0
                         and then Pos_Of (Upd, I) in 1 .. Row_Count (Upd, K0)
                         and then Src (Pos_Of (Upd, I)) = 0
                         and then Held (Upd, I) = R))
             and then (for all I in 1 .. Count (Old) =>
                         Holds (Upd, Held (Old, I))
                         or else (Row_Of (Old, I) = K0
                                  and then Pos_Of (Old, I) in 1 .. Row_Count (Old, K0)
                                  and then Dst (Pos_Of (Old, I)) = 0
                                  and then Held (Old, I) = Row_At (Old, K0, Pos_Of (Old, I))))
   is
   begin
      Lemma_All_Flat (Old);
      Lemma_All_Flat (Upd);
      for I in 1 .. Count (Upd) loop
         declare
            K : constant Slot_Number := Row_Of (Upd, I);
            P : constant Integer := Pos_Of (Upd, I);
         begin
            if K /= K0 then
               Lemma_Row_Flat (Old, K, P);
               pragma Assert (Held (Old, Flat_Index (Old, K, P)) = Held (Upd, I));
            elsif Src (P) /= 0 then
               Lemma_Row_Flat (Old, K0, Src (P));
               pragma Assert (Held (Old, Flat_Index (Old, K0, Src (P))) = Held (Upd, I));
            else
               pragma Assert (Held (Upd, I) = R);
            end if;
         end;
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              Holds (Old, Held (Upd, I2))
              or else (Row_Of (Upd, I2) = K0
                       and then Pos_Of (Upd, I2) in 1 .. Row_Count (Upd, K0)
                       and then Src (Pos_Of (Upd, I2)) = 0
                       and then Held (Upd, I2) = R));
      end loop;
      for I in 1 .. Count (Old) loop
         declare
            K : constant Slot_Number := Row_Of (Old, I);
            P : constant Integer := Pos_Of (Old, I);
         begin
            if K /= K0 then
               Lemma_Row_Flat (Upd, K, P);
               pragma Assert (Held (Upd, Flat_Index (Upd, K, P)) = Held (Old, I));
            elsif Dst (P) /= 0 then
               Lemma_Row_Flat (Upd, K0, Dst (P));
               pragma Assert (Held (Upd, Flat_Index (Upd, K0, Dst (P))) = Held (Old, I));
            end if;
         end;
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              Holds (Upd, Held (Old, I2))
              or else (Row_Of (Old, I2) = K0
                       and then Pos_Of (Old, I2) in 1 .. Row_Count (Old, K0)
                       and then Dst (Pos_Of (Old, I2)) = 0
                       and then Held (Old, I2) = Row_At (Old, K0, Pos_Of (Old, I2))));
      end loop;
   end Lemma_Step_Flat;

   ---------------------------------------------------------------------
   --  Coherence across an authorization step
   ---------------------------------------------------------------------

   procedure Find_Roster (A : Auth_Rows; C : U48; K : out Slot_Index; J : out Positive) with
     Ghost, Global => null,
     Pre  => Roster_At (A, C),
     Post => J <= SC (A, K) and then A.H (K, J).K = K_Roster and then A.H (K, J).V.T = C
   is
   begin
      for K2 in Slot_Index loop
         for J2 in 1 .. SC (A, K2) loop
            if A.H (K2, J2).K = K_Roster and then A.H (K2, J2).V.T = C then
               K := K2;
               J := J2;
               return;
            end if;
            pragma Loop_Invariant
              (for all J3 in 1 .. J2 =>
                 not (A.H (K2, J3).K = K_Roster and then A.H (K2, J3).V.T = C));
         end loop;
         pragma Loop_Invariant
           (for all K3 in 1 .. K2 =>
              (for all J3 in 1 .. SC (A, K3) =>
                 not (A.H (K3, J3).K = K_Roster and then A.H (K3, J3).V.T = C)));
      end loop;
      pragma Assert (False);
      K := 1;
      J := 1;
   end Find_Roster;

   procedure Find_Grant (A : Auth_Rows; W : Key256; K : out Slot_Index; J : out Positive) with
     Ghost, Global => null,
     Pre  => Grant_Of (A, W),
     Post => J <= SC (A, K) and then A.H (K, J).K = K_Grant and then A.H (K, J).V.Author = W
   is
   begin
      for K2 in Slot_Index loop
         for J2 in 1 .. SC (A, K2) loop
            if A.H (K2, J2).K = K_Grant and then A.H (K2, J2).V.Author = W then
               K := K2;
               J := J2;
               return;
            end if;
            pragma Loop_Invariant
              (for all J3 in 1 .. J2 =>
                 not (A.H (K2, J3).K = K_Grant and then A.H (K2, J3).V.Author = W));
         end loop;
         pragma Loop_Invariant
           (for all K3 in 1 .. K2 =>
              (for all J3 in 1 .. SC (A, K3) =>
                 not (A.H (K3, J3).K = K_Grant and then A.H (K3, J3).V.Author = W)));
      end loop;
      pragma Assert (False);
      K := 1;
      J := 1;
   end Find_Grant;

   --  An authorization step on slot K0, on the rows themselves: every other
   --  slot is unchanged; slot K0 keeps some of its old records (Src) and
   --  ends in R; an old record of slot K0 is kept (Dst) or dominated by R.
   function Auth_Step
     (Old, Upd : Auth_Rows; K0 : Slot_Index; R : Header; Src, Dst : Index_Map)
      return Boolean
   is
     (Old.Slice = Upd.Slice
      and then Src'First = 1 and then Dst'First = 1
      and then Src'Last >= Upd.Slice and then Dst'Last >= Old.Slice
      and then (for all K in Slot_Index =>
                  (if K /= K0 then
                     SC (Upd, K) = SC (Old, K)
                     and then (for all J in 1 .. SC (Old, K) => Upd.H (K, J) = Old.H (K, J))))
      and then SC (Upd, K0) >= 1
      and then Upd.H (K0, SC (Upd, K0)) = R
      and then (for all J in 1 .. SC (Upd, K0) - 1 =>
                  Src (J) in 1 .. SC (Old, K0)
                  and then Upd.H (K0, J) = Old.H (K0, Src (J)))
      and then (for all J in 1 .. SC (Old, K0) =>
                  (if Dst (J) = 0 then Dominates (R, Old.H (K0, J))
                   else Dst (J) in 1 .. SC (Upd, K0) - 1
                        and then Upd.H (K0, Dst (J)) = Old.H (K0, J))))
   with Ghost;

   procedure Lemma_Grant_Kept
     (Old, Upd : Auth_Rows; K0 : Slot_Index; R : Header; Src, Dst : Index_Map; W : Key256)
   with
     Ghost, Global => null,
     Pre  => Grant_Of (Old, W) and then Auth_Step (Old, Upd, K0, R, Src, Dst),
     Post => Grant_Of (Upd, W)
   is
      K : Slot_Index;
      J : Positive;
   begin
      Find_Grant (Old, W, K, J);
      if K /= K0 then
         pragma Assert (SC (Upd, K) = SC (Old, K));
         pragma Assert (J <= SC (Upd, K));
         pragma Assert (Upd.H (K, J) = Old.H (K, J));
         pragma Assert (Upd.H (K, J).K = K_Grant and then Upd.H (K, J).V.Author = W);
      elsif Dst (J) /= 0 then
         pragma Assert (Dst (J) <= SC (Upd, K0));
         pragma Assert (Upd.H (K0, Dst (J)) = Old.H (K0, J));
         pragma Assert (Upd.H (K0, Dst (J)).K = K_Grant
                        and then Upd.H (K0, Dst (J)).V.Author = W);
      else
         Lemma_Dominator_Keeps_Registers (R, Old.H (K0, J));
         pragma Assert (R.K = K_Grant and then R.V.Author = W);
         pragma Assert (Upd.H (K0, SC (Upd, K0)) = R);
         pragma Assert (Upd.H (K0, SC (Upd, K0)).K = K_Grant
                        and then Upd.H (K0, SC (Upd, K0)).V.Author = W);
      end if;
   end Lemma_Grant_Kept;

   procedure Lemma_Roster_Kept
     (Old, Upd : Auth_Rows; K0 : Slot_Index; R : Header; Src, Dst : Index_Map; C : U48)
   with
     Ghost, Global => null,
     Pre  => Roster_At (Old, C) and then Auth_Step (Old, Upd, K0, R, Src, Dst)
             and then Ceil_Of (R) <= C,
     Post => Roster_At (Upd, C)
   is
      K : Slot_Index;
      J : Positive;
   begin
      Find_Roster (Old, C, K, J);
      if K /= K0 then
         pragma Assert (SC (Upd, K) = SC (Old, K));
         pragma Assert (J <= SC (Upd, K));
         pragma Assert (Upd.H (K, J) = Old.H (K, J));
         pragma Assert (Upd.H (K, J).K = K_Roster and then Upd.H (K, J).V.T = C);
      elsif Dst (J) /= 0 then
         pragma Assert (Dst (J) <= SC (Upd, K0));
         pragma Assert (Upd.H (K0, Dst (J)) = Old.H (K0, J));
         pragma Assert (Upd.H (K0, Dst (J)).K = K_Roster
                        and then Upd.H (K0, Dst (J)).V.T = C);
      else
         Lemma_Dominator_Keeps_Registers (R, Old.H (K0, J));
         pragma Assert (R.K = K_Roster and then R.V.T = C);
         pragma Assert (Upd.H (K0, SC (Upd, K0)) = R);
         pragma Assert (Upd.H (K0, SC (Upd, K0)).K = K_Roster
                        and then Upd.H (K0, SC (Upd, K0)).V.T = C);
      end if;
   end Lemma_Roster_Kept;

   procedure Lemma_Coherent_Step
     (Old, Upd : Auth_Rows; Old_RG, Upd_RG : Register_File;
      K0 : Slot_Index; R : Header; Src, Dst : Index_Map)
   with
     Ghost, Global => null,
     Pre  => Coherent (Old, Old_RG) and then Is_Auth (R)
             and then Auth_Step (Old, Upd, K0, R, Src, Dst)
             and then Ceil (Upd_RG) = U48'Max (Ceil (Old_RG), Ceil_Of (R))
             and then Extends (Old_RG, Upd_RG)
             and then (if R.K = K_Grant then Added (Old_RG, Upd_RG, R.V.Author)
                       else Registers.Count (Upd_RG) = Registers.Count (Old_RG)
                            and then (for all I in 1 .. Registers.Count (Upd_RG) =>
                                        Writer (Upd_RG, I) = Writer (Old_RG, I))),
     Post => Coherent (Upd, Upd_RG)
   is
      N : constant Natural := SC (Upd, K0);
   begin
      --  The ceiling bounds every held roster, and every held grant's
      --  subject is a writer.
      for K in Slot_Index loop
         for J in 1 .. SC (Upd, K) loop
            if K /= K0 then
               pragma Assert (SC (Upd, K) = SC (Old, K));
               pragma Assert (J <= SC (Old, K));
               pragma Assert (Upd.H (K, J) = Old.H (K, J));
               pragma Assert (Ceil_Of (Old.H (K, J)) <= Ceil (Old_RG));
               if Upd.H (K, J).K = K_Grant then
                  pragma Assert (In_W (Old_RG, Old.H (K, J).V.Author));
                  Lemma_Extends_In_W (Old_RG, Upd_RG, Upd.H (K, J).V.Author);
               end if;
            elsif J < N then
               pragma Assert (Src (J) in 1 .. SC (Old, K));
               pragma Assert (Upd.H (K, J) = Old.H (K, Src (J)));
               pragma Assert (Ceil_Of (Old.H (K, Src (J))) <= Ceil (Old_RG));
               if Upd.H (K, J).K = K_Grant then
                  pragma Assert (In_W (Old_RG, Old.H (K, Src (J)).V.Author));
                  Lemma_Extends_In_W (Old_RG, Upd_RG, Upd.H (K, J).V.Author);
               end if;
            else
               pragma Assert (Upd.H (K, J) = R);
               if R.K = K_Grant then
                  Lemma_Added_In_W (Old_RG, Upd_RG, R.V.Author, R.V.Author);
               end if;
            end if;
            pragma Loop_Invariant
              (for all J2 in 1 .. J => Ceil_Of (Upd.H (K, J2)) <= Ceil (Upd_RG));
            pragma Loop_Invariant
              (for all J2 in 1 .. J =>
                 (if Upd.H (K, J2).K = K_Grant then In_W (Upd_RG, Upd.H (K, J2).V.Author)));
         end loop;
         pragma Loop_Invariant
           (for all K2 in 1 .. K =>
              (for all J2 in 1 .. SC (Upd, K2) => Ceil_Of (Upd.H (K2, J2)) <= Ceil (Upd_RG)));
         pragma Loop_Invariant
           (for all K2 in 1 .. K =>
              (for all J2 in 1 .. SC (Upd, K2) =>
                 (if Upd.H (K2, J2).K = K_Grant
                  then In_W (Upd_RG, Upd.H (K2, J2).V.Author))));
      end loop;

      --  The ceiling is some held roster's, or 0.
      if Ceil (Upd_RG) /= 0 then
         if R.K = K_Roster and then R.V.T = Ceil (Upd_RG) then
            pragma Assert (N >= 1 and then N <= SC (Upd, K0));
            pragma Assert (Upd.H (K0, N) = R);
            pragma Assert (Upd.H (K0, N).K = K_Roster and then Upd.H (K0, N).V.T = Ceil (Upd_RG));
            pragma Assert (Roster_At (Upd, Ceil (Upd_RG)));
         else
            pragma Assert (Ceil (Upd_RG) = Ceil (Old_RG));
            pragma Assert (Roster_At (Old, Ceil (Old_RG)));
            Lemma_Roster_Kept (Old, Upd, K0, R, Src, Dst, Ceil (Old_RG));
         end if;
      end if;

      --  Every writer is a held grant's subject.
      for I in 1 .. Registers.Count (Upd_RG) loop
         if R.K = K_Grant then
            Lemma_In_W_Iff (Upd_RG, Writer (Upd_RG, I));
            Lemma_Added_In_W (Old_RG, Upd_RG, R.V.Author, Writer (Upd_RG, I));
            if Writer (Upd_RG, I) = R.V.Author then
               pragma Assert (N >= 1 and then N <= SC (Upd, K0));
               pragma Assert (Upd.H (K0, N) = R);
               pragma Assert (Upd.H (K0, N).K = K_Grant
                              and then Upd.H (K0, N).V.Author = Writer (Upd_RG, I));
               pragma Assert (Grant_Of (Upd, Writer (Upd_RG, I)));
            else
               pragma Assert (In_W (Old_RG, Writer (Upd_RG, I)));
               Lemma_In_W_Iff (Old_RG, Writer (Upd_RG, I));
               pragma Assert (Grant_Of (Old, Writer (Upd_RG, I)));
               Lemma_Grant_Kept (Old, Upd, K0, R, Src, Dst, Writer (Upd_RG, I));
            end if;
         else
            pragma Assert (Writer (Upd_RG, I) = Writer (Old_RG, I));
            pragma Assert (Grant_Of (Old, Writer (Old_RG, I)));
            Lemma_Grant_Kept (Old, Upd, K0, R, Src, Dst, Writer (Upd_RG, I));
         end if;
         pragma Loop_Invariant
           (for all I2 in 1 .. I => Grant_Of (Upd, Writer (Upd_RG, I2)));
      end loop;
   end Lemma_Coherent_Step;

   --  The offsets of the flat view from the slot counts.
   function Offs_OK (NA : Slot_Counts; Slice : Slice_Count; Offs : Slot_Offs; NAuth : Natural)
     return Boolean
   is
     (Offs (1) = 0
      and then (for all K in 2 .. Signers_Max => Offs (K) = Offs (K - 1) + NA (K - 1))
      and then (for all K in Slot_Index => Offs (K) <= (K - 1) * Slice)
      and then NAuth = Offs (Signers_Max) + NA (Signers_Max));

   procedure Compute_Offs
     (NA    : Slot_Counts;
      Slice : Slice_Count;
      Offs  : out Slot_Offs;
      NAuth : out Off_Value)
   with
     Global => null,
     Pre    => (for all K in Slot_Index => NA (K) <= Slice),
     Post   => Offs_OK (NA, Slice, Offs, NAuth)
   is
   begin
      Offs := [others => 0];
      for K in 2 .. Signers_Max loop
         pragma Assert (Offs (K - 1) <= (K - 2) * Slice);
         pragma Assert ((K - 2) * Slice + Slice = (K - 1) * Slice);
         pragma Assert ((K - 1) * Slice <= (Signers_Max - 1) * Slice);
         pragma Assert ((Signers_Max - 1) * Slice <= (Signers_Max - 1) * Slice_Max);
         Offs (K) := Offs (K - 1) + NA (K - 1);
         pragma Loop_Invariant (Offs (1) = 0);
         pragma Loop_Invariant
           (for all K2 in 2 .. K => Offs (K2) = Offs (K2 - 1) + NA (K2 - 1));
         pragma Loop_Invariant
           (for all K2 in 1 .. K => Offs (K2) <= (K2 - 1) * Slice);
      end loop;
      pragma Assert (Offs (Signers_Max) <= (Signers_Max - 1) * Slice);
      NAuth := Offs (Signers_Max) + NA (Signers_Max);
   end Compute_Offs;

   --  Shape and slot table across an authorization step on slot K0 (Fresh:
   --  K0 is a newly assigned slot).
   procedure Lemma_Slots_Step
     (Old, Upd : Auth_Rows; Fnd : Key256; K0 : Slot_Index; Fresh : Boolean)
   with
     Ghost, Global => null,
     Pre  => Auth_Shape (Old) and then Slots_OK (Old, Fnd)
             and then Upd.Slice = Old.Slice
             and then (for all K in Slot_Index =>
                         (if K /= K0 then Upd.NA (K) = Old.NA (K)
                                          and then Upd.Keys (K) = Old.Keys (K)))
             and then Upd.NA (K0) in 1 .. Upd.Slice
             and then (if Fresh then
                         Old.NSlots < Signers_Max and then K0 = Old.NSlots + 1
                         and then Upd.NSlots = K0
                         and then (for all K in 1 .. Old.NSlots => Old.Keys (K) /= Upd.Keys (K0))
                       else
                         K0 <= Old.NSlots and then Upd.NSlots = Old.NSlots
                         and then Upd.Keys (K0) = Old.Keys (K0))
             and then Offs_OK (Upd.NA, Upd.Slice, Upd.Offs, Upd.NAuth),
     Post => Auth_Shape (Upd) and then Slots_OK (Upd, Fnd)
   is
   begin
      pragma Assert (K0 >= 2 or else not Fresh);
      pragma Assert (Upd.Keys (1) = Fnd);
      pragma Assert (for all K in Slot_Index => Upd.NA (K) <= Upd.Slice);
      pragma Assert (for all K in Slot_Index => (if K > Upd.NSlots then Upd.NA (K) = 0));
      pragma Assert (for all K in 2 .. Upd.NSlots => Upd.NA (K) >= 1);
      pragma Assert
        (for all K in 1 .. Upd.NSlots =>
           (for all K2 in 1 .. Upd.NSlots =>
              (if K /= K2 then Upd.Keys (K) /= Upd.Keys (K2))));
   end Lemma_Slots_Step;

   --  The data row is still a frontier row under widened registers (T4').
   procedure Lemma_Data_OK_Regs (Old, Upd : State) with
     Ghost, Global => null,
     Pre  => Data_OK (Old)
             and then Upd.Cap = Old.Cap and then Upd.ND = Old.ND and then Upd.NS = Old.NS
             and then (for all I in 1 .. Data_Count (Old) => Upd.Data_H (I) = Old.Data_H (I))
             and then Ceil (Upd.RG) >= Ceil (Old.RG)
             and then Extends (Old.RG, Upd.RG),
     Post => Data_OK (Upd)
   is
   begin
      pragma Assert (Data_Count (Upd) = Data_Count (Old));
      for I in 1 .. Data_Count (Upd) loop
         pragma Assert (Data_Item_OK (Old, Old.Data_H (I)));
         Lemma_Extends_In_W (Old.RG, Upd.RG, Upd.Data_H (I).V.Author);
         pragma Loop_Invariant (for all I2 in 1 .. I => Data_Item_OK (Upd, Upd.Data_H (I2)));
      end loop;
   end Lemma_Data_OK_Regs;

   --  Auth_OK across an authorization step: R is a canonical record of the
   --  slot's issuer, undominated in its row and not already in it; the kept
   --  records are distinct old ones R does not dominate.
   procedure Lemma_Auth_OK_Step
     (Old, Upd : Auth_Rows; Old_NS, NS : Id128; K0 : Slot_Index; R : Header;
      Src, Dst : Index_Map)
   with
     Ghost, Global => null,
     Pre  => Old_NS = NS and then Auth_OK (Old, Old_NS)
             and then Auth_Step (Old, Upd, K0, R, Src, Dst)
             and then (for all K in Slot_Index =>
                         (if K /= K0 then Upd.Keys (K) = Old.Keys (K)))
             and then Upd.Keys (K0) = R.Issuer
             and then (if SC (Old, K0) > 0 then Old.Keys (K0) = R.Issuer)
             and then Is_Auth (R) and then Canonical (R) and then R.NS = NS
             and then (for all J in 1 .. SC (Old, K0) =>
                         Old.H (K0, J) /= R and then not Dominates (Old.H (K0, J), R))
             and then (for all J in 1 .. SC (Upd, K0) - 1 =>
                         not Dominates (R, Old.H (K0, Src (J))))
             and then (for all J in 1 .. SC (Upd, K0) - 1 =>
                         (for all J2 in 1 .. SC (Upd, K0) - 1 =>
                            (if J /= J2 then Src (J) /= Src (J2)))),
     Post => Auth_OK (Upd, NS)
   is
      N : constant Natural := SC (Upd, K0);
   begin
      Lemma_Dominates_Irrefl (R);
      pragma Assert
        (for all J in 1 .. N =>
           (if J < N then Upd.H (K0, J) = Old.H (K0, Src (J)) else Upd.H (K0, J) = R));
      pragma Assert
        (for all J in 1 .. N =>
           Is_Auth (Upd.H (K0, J)) and then Canonical (Upd.H (K0, J))
           and then Upd.H (K0, J).NS = NS and then Upd.H (K0, J).Issuer = Upd.Keys (K0));
      pragma Assert
        (for all J in 1 .. N =>
           (for all J2 in 1 .. N => not Dominates (Upd.H (K0, J2), Upd.H (K0, J))));
      pragma Assert
        (for all J in 1 .. N =>
           (for all J2 in 1 .. N => (if J /= J2 then Upd.H (K0, J) /= Upd.H (K0, J2))));
      pragma Assert
        (for all K in Slot_Index =>
           (if K /= K0 then
              (for all J in 1 .. SC (Upd, K) =>
                 Is_Auth (Upd.H (K, J)) and then Canonical (Upd.H (K, J))
                 and then Upd.H (K, J).NS = NS and then Upd.H (K, J).Issuer = Upd.Keys (K))));
      pragma Assert
        (for all K in Slot_Index =>
           (if K /= K0 then
              (for all J in 1 .. SC (Upd, K) =>
                 (for all J2 in 1 .. SC (Upd, K) =>
                    not Dominates (Upd.H (K, J2), Upd.H (K, J))))));
      pragma Assert
        (for all K in Slot_Index =>
           (if K /= K0 then
              (for all J in 1 .. SC (Upd, K) =>
                 (for all J2 in 1 .. SC (Upd, K) =>
                    (if J /= J2 then Upd.H (K, J) /= Upd.H (K, J2))))));
   end Lemma_Auth_OK_Step;

   ---------------------------------------------------------------------
   --  Public accessors and lemmas
   ---------------------------------------------------------------------

   function Empty
     (NS       : Id128;
      Founding : Key256;
      Cap      : Data_Size;
      Slice    : Slice_Count) return State
   is
     (Cap => Cap, Slice => Slice, NS => NS, Fnd => Founding,
      RG => Registers.Empty,
      Data_H => [others => Null_Header], ND => 0,
      A => (Slice  => Slice,
            H      => [others => [others => Null_Header]],
            NA     => [others => 0],
            Keys   => [1 => Founding, others => Zero_Key],
            NSlots => 1,
            Offs   => [others => 0],
            NAuth  => 0));

   procedure Lemma_Held_Data (S : State; I : Held_Index) is null;

   procedure Lemma_Held_Auth (S : State; K : Slot_Index; J : Held_Index) is
   begin
      Lemma_Off_Mono (S);
      Lemma_Row_Flat (S, K, J);
   end Lemma_Held_Auth;

   procedure Lemma_Held_Cases (S : State; I : Held_Index) is
   begin
      Lemma_Flat_Row (S, I);
   end Lemma_Held_Cases;

   procedure Lemma_Frontier_Shape (S : State) is
   begin
      Lemma_Off_Mono (S);
   end Lemma_Frontier_Shape;

   procedure Lemma_Frontier_Data (S : State; I : Held_Index) is null;

   procedure Lemma_Frontier_Auth (S : State; K : Slot_Index; J : Held_Index) is null;

   procedure Lemma_Frontier_Held (S : State; I : Held_Index) is
      K : constant Slot_Number := Row_Of (S, I);
      P : Integer;
   begin
      Lemma_Off_Mono (S);
      Lemma_All_Flat (S);
      P := Pos_Of (S, I);
      Lemma_Item (S, K, P);
      for J in 1 .. Count (S) loop
         Lemma_Item (S, Row_Of (S, J), Pos_Of (S, J));
         if Dominates (Held (S, J), Held (S, I)) then
            Lemma_Same_Row (Held (S, J), Held (S, I));
            pragma Assert (Row_Of (S, J) = K);
            pragma Assert (False);
         end if;
         if Held (S, J) = Held (S, I) then
            pragma Assert (Row_Of (S, J) = K);
            pragma Assert (Pos_Of (S, J) = P);
            Lemma_Flat_Row (S, J);
            Lemma_Flat_Row (S, I);
            pragma Assert (J = I);
         end if;
         pragma Loop_Invariant
           (for all J2 in 1 .. J => not Dominates (Held (S, J2), Held (S, I)));
         pragma Loop_Invariant
           (for all J2 in 1 .. J => (if J2 /= I then Held (S, J2) /= Held (S, I)));
      end loop;
   end Lemma_Frontier_Held;

   procedure Lemma_Ceil_Bound (S : State; I : Held_Index) is
   begin
      Lemma_Flat_Row (S, I);
   end Lemma_Ceil_Bound;

   procedure Lemma_Ceil_Witness (S : State) is
      K : Slot_Index;
      J : Positive;
   begin
      Lemma_Off_Mono (S);
      Find_Roster (S.A, Ceil (S.RG), K, J);
      Lemma_Row_Flat (S, K, J);
      pragma Assert (Held (S, Flat_Index (S, K, J)) = S.A.H (K, J));
   end Lemma_Ceil_Witness;

   procedure Lemma_W_Sound (S : State; A : Key256) is
      K : Slot_Index;
      J : Positive;
   begin
      Lemma_Off_Mono (S);
      Lemma_In_W_Iff (S.RG, A);
      pragma Assert (Grant_Of (S.A, A));
      Find_Grant (S.A, A, K, J);
      Lemma_Row_Flat (S, K, J);
      pragma Assert (Held (S, Flat_Index (S, K, J)) = S.A.H (K, J));
   end Lemma_W_Sound;

   procedure Lemma_W_Complete (S : State; I : Held_Index) is
   begin
      Lemma_Off_Mono (S);
      Lemma_Flat_Row (S, I);
      Lemma_Item (S, Row_Of (S, I), Pos_Of (S, I));
   end Lemma_W_Complete;

   procedure Lemma_Drops_Any (S : State; R : Header) is null;

   procedure Lemma_Unchanged_Refl (S : State) is null;

   --  Every quantifier is bounded by Count (Old) or a slot count, so the
   --  lemma also runs under -gnata (Kome.Store calls it on every refusal).
   procedure Lemma_Unchanged (Old, Upd : State) is
   begin
      Lemma_Eq (Old.RG, Upd.RG);
      pragma Assert (Data_Count (Upd) = Data_Count (Old));
      pragma Assert (for all K in Slot_Index => Slot_Count (Upd, K) = Slot_Count (Old, K));
      pragma Assert (for all K in Slot_Number => Row_Count (Upd, K) = Row_Count (Old, K));
      pragma Assert
        (for all J in 1 .. Data_Count (Old) => Row_At (Upd, 0, J) = Row_At (Old, 0, J));
      pragma Assert
        (for all K in Slot_Index =>
           (for all J in 1 .. Slot_Count (Old, K) => Upd.A.H (K, J) = Old.A.H (K, J)));
      pragma Assert
        (for all K in Slot_Index =>
           (for all J in 1 .. Row_Count (Old, K) => Row_At (Upd, K, J) = Row_At (Old, K, J)));
      pragma Assert
        (for all K in Slot_Number =>
           (for all J in 1 .. Row_Count (Old, K) => Row_At (Upd, K, J) = Row_At (Old, K, J)));
      pragma Assert (Count (Upd) = Count (Old));
      for I in 1 .. Count (Old) loop
         pragma Assert (Flat_Slot (Upd, I - Data_Count (Old))
                        = Flat_Slot (Old, I - Data_Count (Old)));
         pragma Assert (Row_Of (Upd, I) = Row_Of (Old, I));
         pragma Assert (Pos_Of (Upd, I) = Pos_Of (Old, I));
         declare
            K : constant Slot_Number := Row_Of (Old, I);
            J : constant Integer := Pos_Of (Old, I);
         begin
            --  Inside the row both rows agree (above); outside it both
            --  are Null_Header.
            if J not in 1 .. Row_Count (Old, K) then
               pragma Assert (Row_At (Old, K, J) = Null_Header);
               pragma Assert (Row_At (Upd, K, J) = Null_Header);
            end if;
            pragma Assert (Row_At (Upd, K, J) = Row_At (Old, K, J));
         end;
         pragma Assert (Held (Upd, I) = Held (Old, I));
         pragma Loop_Invariant (for all I2 in 1 .. I => Held (Upd, I2) = Held (Old, I2));
      end loop;
   end Lemma_Unchanged;

   ---------------------------------------------------------------------
   --  Apply
   ---------------------------------------------------------------------

   --  Apply to the data row (R admitted).
   procedure Apply_Data (S : in out State; R : Header; Result : out Status) with
     Global => null,
     Pre  => Is_Frontier (S) and then Canonical (R) and then R.NS = S.NS
             and then Is_Data (R) and then Admitted (S, R),
     Post => Is_Frontier (S)
       and then S.NS = S'Old.NS and then S.Fnd = S'Old.Fnd
       and then Result in OK | Dominated | No_Space
       and then (Result = Dominated) = (not Holds (S'Old, R) and then Dom (S'Old, R))
       and then (Result = No_Space)
                = (not Holds (S'Old, R) and then not Dom (S'Old, R)
                   and then Data_Count (S'Old) = S.Cap
                   and then not Drops_Any (S'Old, R))
       and then (if Result /= OK or else Holds (S'Old, R) then Unchanged (S'Old, S))
       and then (if Result = OK then
                   Holds (S, R)
                   and then Admitted (S, R)
                   and then Ceil (Regs (S)) = Ceil (Regs (S'Old))
                   and then Extends (Regs (S'Old), Regs (S))
                   and then Extends (Regs (S), Regs (S'Old))
                   and then (for all I in 1 .. Count (S) =>
                               Holds (S'Old, Held (S, I)) or else Held (S, I) = R)
                   and then (for all I in 1 .. Count (S'Old) =>
                               Holds (S, Held (S'Old, I))
                               or else Dominates (R, Held (S'Old, I))))
   is
      Old_S : constant State := S with Ghost;
      Cap   : constant Data_Size := S.Cap;
      N     : constant Data_Size := S.ND;
   begin
      Lemma_Classify (S, R);
      Lemma_Off_Mono (S);
      pragma Assert (Data_Count (S) = N and then N <= Cap);
      pragma Assert (Row_For (S, R) = 0 and then Has_Row (S, R));
      pragma Assert (Data_OK (S));
      Lemma_Extends_Refl (S.RG);

      --  Duplicate, or beaten by a held record?
      for I in 1 .. N loop
         pragma Loop_Invariant
           (for all J in 1 .. I - 1 =>
              S.Data_H (J) /= R and then not Dominates (S.Data_H (J), R));
         if S.Data_H (I) = R then
            pragma Assert (Row_At (S, 0, I) = R);
            pragma Assert (In_Row (S, 0, R));
            pragma Assert (Holds (S, R));
            Result := OK;
            return;
         end if;
         if Dominates (S.Data_H (I), R) then
            pragma Assert (Row_At (S, 0, I) = S.Data_H (I));
            pragma Assert (Dom_In_Row (S, 0, R));
            --  A held copy of R would be dominated too.
            pragma Assert
              (for all J in 1 .. N => not Dominates (S.Data_H (I), S.Data_H (J)));
            pragma Assert (for all J in 1 .. N => S.Data_H (J) /= R);
            pragma Assert (not In_Row (S, 0, R));
            Result := Dominated;
            return;
         end if;
      end loop;
      pragma Assert (not In_Row (S, 0, R));
      pragma Assert (not Dom_In_Row (S, 0, R));

      --  Room: decided before anything changes.
      declare
         Any_Drop : Boolean := False;
         Kept     : Data_Size := 0;
         Dropped  : Data_Size := 0;
         Src : Index_Map (1 .. Cap) := [others => 0] with Ghost;
         Dst : Index_Map (1 .. Cap) := [others => 0] with Ghost;
      begin
         for I in 1 .. N loop
            pragma Loop_Invariant
              (Any_Drop = (for some J in 1 .. I - 1 => Dominates (R, S.Data_H (J))));
            if Dominates (R, S.Data_H (I)) then
               Any_Drop := True;
            end if;
         end loop;
         pragma Assert (Any_Drop = Drops_In_Row (S, 0, R));
         if N = Cap and then not Any_Drop then
            Result := No_Space;
            return;
         end if;

         --  Drop what R beats, compacting in place; then hold R.
         for I in 1 .. N loop
            pragma Loop_Invariant (Kept + Dropped = I - 1);
            pragma Loop_Invariant
              ((Dropped > 0) = (for some J in 1 .. I - 1 => Dominates (R, Old_S.Data_H (J))));
            pragma Loop_Invariant (S.ND = N);
            pragma Loop_Invariant (for all J in I .. N => S.Data_H (J) = Old_S.Data_H (J));
            pragma Loop_Invariant
              (for all J in 1 .. Kept =>
                 Src (J) in 1 .. I - 1
                 and then S.Data_H (J) = Old_S.Data_H (Src (J))
                 and then not Dominates (R, Old_S.Data_H (Src (J))));
            pragma Loop_Invariant
              (for all J in 1 .. Kept =>
                 (for all J2 in 1 .. Kept => (if J < J2 then Src (J) < Src (J2))));
            pragma Loop_Invariant
              (for all J in 1 .. I - 1 =>
                 (if Dominates (R, Old_S.Data_H (J)) then Dst (J) = 0
                  else Dst (J) in 1 .. Kept and then S.Data_H (Dst (J)) = Old_S.Data_H (J)));
            if not Dominates (R, S.Data_H (I)) then
               Kept := Kept + 1;
               S.Data_H (Kept) := S.Data_H (I);
               Src (Kept) := I;
               Dst (I) := Kept;
            else
               Dropped := Dropped + 1;
               Dst (I) := 0;
            end if;
         end loop;
         pragma Assert (Kept + Dropped = N);
         pragma Assert (if Any_Drop then Dropped > 0);
         pragma Assert (Kept < Cap);
         Lemma_Dominates_Irrefl (R);

         pragma Assert
           (for all J in 1 .. Kept =>
              Src (J) in 1 .. N and then S.Data_H (J) = Old_S.Data_H (Src (J)));
         pragma Assert
           (for all J in 1 .. Kept =>
              (for all J2 in 1 .. Kept => (if J /= J2 then Src (J) /= Src (J2))));

         S.ND := Kept + 1;
         S.Data_H (Kept + 1) := R;
         Src (Kept + 1) := 0;

         --  Bridge: the data row is the kept records plus R.
         pragma Assert (Data_Count (S) = Kept + 1);
         pragma Assert
           (for all J in 1 .. Kept => S.Data_H (J) = Old_S.Data_H (Src (J)));
         pragma Assert (S.Data_H (Kept + 1) = R);
         pragma Assert
           (for all J in 1 .. N =>
              (if Dst (J) = 0 then Dominates (R, Old_S.Data_H (J))
               else Dst (J) in 1 .. Kept and then S.Data_H (Dst (J)) = Old_S.Data_H (J)));
         pragma Assert (for all J in 1 .. Kept + 1 => Data_Item_OK (S, S.Data_H (J)));
         pragma Assert
           (for all J in 1 .. Kept + 1 =>
              (for all J2 in 1 .. Kept + 1 =>
                 not Dominates (S.Data_H (J2), S.Data_H (J))));
         pragma Assert
           (for all J in 1 .. Kept + 1 =>
              (for all J2 in 1 .. Kept + 1 =>
                 (if J /= J2 then S.Data_H (J) /= S.Data_H (J2))));
         pragma Assert (Data_OK (S));
         pragma Assert (Shape (S));
         pragma Assert (Slots_OK (S.A, S.Fnd));
         pragma Assert (Auth_OK (S.A, S.NS));
         pragma Assert (Coherent (S.A, S.RG));
         pragma Assert (Is_Frontier (S));

         pragma Assert (Step (Old_S, S, 0, R, Src, Dst));
         Lemma_Step_Flat (Old_S, S, 0, R, Src, Dst);
         Lemma_Row_Flat (S, 0, Kept + 1);
         pragma Assert (Holds (S, R));
         Lemma_Extends_Refl (S.RG);
      end;
      Result := OK;
   end Apply_Data;

   --  Apply to the signer's slot (R an authorization record).
   --  Commit an authorization record to slot K0 (Fresh: a newly assigned
   --  slot): drop what R beats in its own row, hold R, move the offsets,
   --  derive the registers. Every refusal has been decided by the caller.
   procedure Commit_Auth (S : in out State; R : Header; K0 : Slot_Index; Fresh : Boolean) with
     Global => null,
     Pre  => Is_Frontier (S) and then Canonical (R) and then R.NS = S.NS
             and then Is_Auth (R)
             and then (if Fresh then
                         S.A.NSlots < Signers_Max and then K0 = S.A.NSlots + 1
                         and then (for all K in 1 .. S.A.NSlots => S.A.Keys (K) /= R.Issuer)
                       else
                         K0 <= S.A.NSlots and then S.A.Keys (K0) = R.Issuer)
             and then (for all J in 1 .. SC (S.A, K0) =>
                         S.A.H (K0, J) /= R and then not Dominates (S.A.H (K0, J), R))
             and then (SC (S.A, K0) < S.A.Slice
                       or else (for some J in 1 .. SC (S.A, K0) => Dominates (R, S.A.H (K0, J))))
             and then (if R.K = K_Grant then
                         In_W (S.RG, R.V.Author) or else Registers.Count (S.RG) < Writers_Max),
     Post => Is_Frontier (S)
       and then S.NS = S'Old.NS and then S.Fnd = S'Old.Fnd
       and then Holds (S, R)
       and then Ceil (Regs (S)) = U48'Max (Ceil (Regs (S'Old)), Ceil_Of (R))
       and then Extends (Regs (S'Old), Regs (S))
       and then (if R.K = K_Grant
                 then Added (Regs (S'Old), Regs (S), R.V.Author)
                 else Extends (Regs (S), Regs (S'Old)))
       and then (for all I in 1 .. Count (S) =>
                   Holds (S'Old, Held (S, I)) or else Held (S, I) = R)
       and then (for all I in 1 .. Count (S'Old) =>
                   Holds (S, Held (S'Old, I)) or else Dominates (R, Held (S'Old, I)))
   is
      Old_S   : constant State := S with Ghost;
      Slice   : constant Slice_Count := S.A.Slice;
      N       : constant Slice_Count := SC (S.A, K0);
      Kept    : Slice_Count := 0;
      Dropped : Slice_Count := 0;
      Src     : Index_Map (1 .. Slice) := [others => 0] with Ghost;
      Dst     : Index_Map (1 .. Slice) := [others => 0] with Ghost;
   begin
      Lemma_Off_Mono (S);
      pragma Assert (Shape (Old_S) and then Auth_Shape (Old_S.A));
      pragma Assert (Slots_OK (Old_S.A, Old_S.Fnd) and then Data_OK (Old_S));
      pragma Assert (Auth_OK (Old_S.A, Old_S.NS) and then Coherent (Old_S.A, Old_S.RG));
      pragma Assert (N = S.A.NA (K0) and then Slice = S.Slice and then Slice >= 1);
      pragma Assert (if Fresh then N = 0);

      --  Drop what R beats in its own row, compacting in place.
      for J in 1 .. N loop
         pragma Loop_Invariant (Kept + Dropped = J - 1);
         pragma Loop_Invariant
           ((Dropped > 0)
            = (for some J2 in 1 .. J - 1 => Dominates (R, Old_S.A.H (K0, J2))));
         pragma Loop_Invariant
           (for all K in Slot_Index =>
              (if K /= K0 then
                 (for all J2 in 1 .. Slice => S.A.H (K, J2) = Old_S.A.H (K, J2))));
         pragma Loop_Invariant
           (for all J2 in J .. N => S.A.H (K0, J2) = Old_S.A.H (K0, J2));
         pragma Loop_Invariant
           (for all J2 in 1 .. Kept =>
              Src (J2) in 1 .. J - 1
              and then S.A.H (K0, J2) = Old_S.A.H (K0, Src (J2))
              and then not Dominates (R, Old_S.A.H (K0, Src (J2))));
         pragma Loop_Invariant
           (for all J2 in 1 .. Kept =>
              (for all J3 in 1 .. Kept => (if J2 < J3 then Src (J2) < Src (J3))));
         pragma Loop_Invariant
           (for all J2 in 1 .. J - 1 =>
              (if Dominates (R, Old_S.A.H (K0, J2)) then Dst (J2) = 0
               else Dst (J2) in 1 .. Kept
                    and then S.A.H (K0, Dst (J2)) = Old_S.A.H (K0, J2)));
         if not Dominates (R, S.A.H (K0, J)) then
            Kept := Kept + 1;
            S.A.H (K0, Kept) := S.A.H (K0, J);
            Src (Kept) := J;
            Dst (J) := Kept;
         else
            Dropped := Dropped + 1;
            Dst (J) := 0;
         end if;
      end loop;
      pragma Assert (Kept + Dropped = N);
      pragma Assert (if N = Slice then Dropped > 0);
      pragma Assert (Kept < Slice);
      Lemma_Dominates_Irrefl (R);
      pragma Assert
        (for all J in 1 .. Kept =>
           Src (J) in 1 .. N and then S.A.H (K0, J) = Old_S.A.H (K0, Src (J)));
      pragma Assert
        (for all J in 1 .. Kept =>
           (for all J2 in 1 .. Kept => (if J /= J2 then Src (J) /= Src (J2))));

      --  Hold R, and assign the slot if the signer is new.
      S.A.H (K0, Kept + 1) := R;
      Src (Kept + 1) := 0;
      S.A.NA (K0) := Kept + 1;
      if Fresh then
         S.A.NSlots := K0;
         S.A.Keys (K0) := R.Issuer;
      end if;

      --  The offsets of the slots after K0 move.
      Compute_Offs (S.A.NA, S.A.Slice, S.A.Offs, S.A.NAuth);

      --  The registers: derived from the held set, so raised only now
      --  that R is held.
      pragma Assert (S.RG = Old_S.RG);
      Lemma_Eq (S.RG, Old_S.RG);
      if R.K = K_Roster then
         Raise_Ceiling (S.RG, R.V.T);
         pragma Assert (Registers.Count (S.RG) = Registers.Count (Old_S.RG));
         pragma Assert
           (for all I in 1 .. Registers.Count (S.RG) => Writer (S.RG, I) = Writer (Old_S.RG, I));
      elsif R.K = K_Grant then
         Add_Writer (S.RG, R.V.Author);
      else
         Lemma_Extends_Refl (S.RG);
         pragma Assert (Registers.Count (S.RG) = Registers.Count (Old_S.RG));
         pragma Assert
           (for all I in 1 .. Registers.Count (S.RG) => Writer (S.RG, I) = Writer (Old_S.RG, I));
      end if;
      pragma Assert
        (if R.K /= K_Grant then
           Registers.Count (S.RG) = Registers.Count (Old_S.RG)
           and then (for all I in 1 .. Registers.Count (S.RG) =>
                       Writer (S.RG, I) = Writer (Old_S.RG, I)));
      pragma Assert (Ceil (S.RG) = U48'Max (Ceil (Old_S.RG), Ceil_Of (R)));
      pragma Assert (Extends (Old_S.RG, S.RG));

      --  Bridge: slot K0 is the kept records plus R; nothing else moved.
      pragma Assert (Slot_Count (S, K0) = Kept + 1);
      pragma Assert (S.A.H (K0, Kept + 1) = R);
      pragma Assert
        (for all J in 1 .. Kept => S.A.H (K0, J) = Old_S.A.H (K0, Src (J)));
      pragma Assert
        (for all J in 1 .. N =>
           (if Dst (J) = 0 then Dominates (R, Old_S.A.H (K0, J))
            else Dst (J) in 1 .. Kept
                 and then S.A.H (K0, Dst (J)) = Old_S.A.H (K0, J)));
      pragma Assert
        (for all K in Slot_Index =>
           (if K /= K0 then S.A.NA (K) = Old_S.A.NA (K) and then S.A.Keys (K) = Old_S.A.Keys (K)));
      pragma Assert (S.A.Keys (K0) = R.Issuer);

      Lemma_Slots_Step (Old_S.A, S.A, S.Fnd, K0, Fresh);
      pragma Assert (Shape (S));
      pragma Assert (Slots_OK (S.A, S.Fnd));
      Lemma_Data_OK_Regs (Old_S, S);
      pragma Assert (Data_OK (S));

      pragma Assert (Auth_Step (Old_S.A, S.A, K0, R, Src, Dst));
      pragma Assert (S.NS = Old_S.NS);
      pragma Assert (for all K in Slot_Index => (if K /= K0 then S.A.Keys (K) = Old_S.A.Keys (K)));
      pragma Assert (SC (S.A, K0) = Kept + 1);
      pragma Assert
        (for all J in 1 .. SC (S.A, K0) - 1 => not Dominates (R, Old_S.A.H (K0, Src (J))));
      pragma Assert
        (for all J in 1 .. SC (S.A, K0) - 1 =>
           (for all J2 in 1 .. SC (S.A, K0) - 1 => (if J /= J2 then Src (J) /= Src (J2))));
      Lemma_Auth_OK_Step (Old_S.A, S.A, Old_S.NS, S.NS, K0, R, Src, Dst);
      pragma Assert (Auth_OK (S.A, S.NS));
      pragma Assert (Coherent (Old_S.A, Old_S.RG));
      pragma Assert (Ceil (S.RG) = U48'Max (Ceil (Old_S.RG), Ceil_Of (R)));
      pragma Assert (Extends (Old_S.RG, S.RG));
      Lemma_Coherent_Step (Old_S.A, S.A, Old_S.RG, S.RG, K0, R, Src, Dst);
      pragma Assert (Is_Frontier (S));

      pragma Assert (Step (Old_S, S, K0, R, Src, Dst));
      Lemma_Step_Flat (Old_S, S, K0, R, Src, Dst);
      Lemma_Row_Flat (S, K0, Kept + 1);
      pragma Assert (Holds (S, R));
      Lemma_All_Flat (Old_S);
      pragma Assert
        (for all I in 1 .. Count (Old_S) =>
           Holds (S, Held (Old_S, I)) or else Dominates (R, Held (Old_S, I)));
   end Commit_Auth;

   procedure Apply_Auth (S : in out State; R : Header; Result : out Status) with
     Global => null,
     Pre  => Is_Frontier (S) and then Canonical (R) and then R.NS = S.NS
             and then Is_Auth (R),
     Post => Is_Frontier (S)
       and then S.NS = S'Old.NS and then S.Fnd = S'Old.Fnd
       and then Result in OK | Dominated | Auth_Full
       and then (Result = Dominated) = (not Holds (S'Old, R) and then Dom (S'Old, R))
       and then (Result = Auth_Full)
                = (not Holds (S'Old, R) and then not Dom (S'Old, R)
                   and then
                     ((Slot_Of (S'Old, R.Issuer) /= 0
                       and then Slot_Count (S'Old, Slot_Of (S'Old, R.Issuer)) = S.Slice
                       and then not Drops_Any (S'Old, R))
                      or else (Slot_Of (S'Old, R.Issuer) = 0
                               and then Slots_Used (S'Old) = Signers_Max)
                      or else (R.K = K_Grant
                               and then not In_W (Regs (S'Old), R.V.Author)
                               and then Registers.Count (Regs (S'Old)) = Writers_Max)))
       and then (if Result /= OK or else Holds (S'Old, R) then Unchanged (S'Old, S))
       and then (if Result = OK then
                   Holds (S, R)
                   and then Ceil (Regs (S)) = U48'Max (Ceil (Regs (S'Old)), Ceil_Of (R))
                   and then Extends (Regs (S'Old), Regs (S))
                   and then (if R.K = K_Grant
                             then Added (Regs (S'Old), Regs (S), R.V.Author)
                             else Extends (Regs (S), Regs (S'Old)))
                   and then (for all I in 1 .. Count (S) =>
                               Holds (S'Old, Held (S, I)) or else Held (S, I) = R)
                   and then (for all I in 1 .. Count (S'Old) =>
                               Holds (S, Held (S'Old, I))
                               or else Dominates (R, Held (S'Old, I))))
   is
      Old_S : constant State := S with Ghost;
      Slice : constant Slice_Count := S.Slice;
      K0    : Slot_Index;
      Fresh : Boolean;
      N     : Slice_Count;
   begin
      Lemma_Classify (S, R);
      Lemma_Off_Mono (S);
      pragma Assert (Shape (S) and then Slots_OK (S.A, S.Fnd) and then Auth_OK (S.A, S.NS));
      pragma Assert (Shape (Old_S) and then Auth_Shape (Old_S.A));
      pragma Assert (Slots_OK (Old_S.A, Old_S.Fnd) and then Data_OK (Old_S));
      pragma Assert (Auth_OK (Old_S.A, Old_S.NS) and then Coherent (Old_S.A, Old_S.RG));

      if Slot_Of (S, R.Issuer) = 0 then
         pragma Assert (not Has_Row (S, R));
         pragma Assert (not Holds (S, R) and then not Dom (S, R) and then not Drops_Any (S, R));
         if S.A.NSlots = Signers_Max then
            Result := Auth_Full;
            return;
         end if;
         Fresh := True;
         K0 := S.A.NSlots + 1;
         N := 0;
         pragma Assert (S.A.NA (K0) = 0);
         pragma Assert (for all K in 1 .. S.A.NSlots => S.A.Keys (K) /= R.Issuer);
      else
         Fresh := False;
         K0 := Slot_Of (S, R.Issuer);
         N := S.A.NA (K0);
         pragma Assert (Row_For (S, R) = K0 and then Has_Row (S, R));
         --  Duplicate, or beaten by a held record?
         for J in 1 .. N loop
            pragma Loop_Invariant
              (for all J2 in 1 .. J - 1 =>
                 S.A.H (K0, J2) /= R and then not Dominates (S.A.H (K0, J2), R));
            if S.A.H (K0, J) = R then
               pragma Assert (Row_At (S, K0, J) = R);
               pragma Assert (In_Row (S, K0, R));
               pragma Assert (Holds (S, R));
               pragma Assert (Coherent (S.A, S.RG));
               pragma Assert (Ceil_Of (R) <= Ceil (S.RG));
               if R.K = K_Grant then
                  pragma Assert (In_W (S.RG, R.V.Author));
                  Lemma_Added_Refl (S.RG, R.V.Author);
               end if;
               Lemma_Extends_Refl (S.RG);
               Result := OK;
               return;
            end if;
            if Dominates (S.A.H (K0, J), R) then
               pragma Assert (Row_At (S, K0, J) = S.A.H (K0, J));
               pragma Assert (Dom_In_Row (S, K0, R));
               pragma Assert
                 (for all J2 in 1 .. N => not Dominates (S.A.H (K0, J), S.A.H (K0, J2)));
               pragma Assert (for all J2 in 1 .. N => S.A.H (K0, J2) /= R);
               pragma Assert (not In_Row (S, K0, R));
               Result := Dominated;
               return;
            end if;
         end loop;
         pragma Assert (not In_Row (S, K0, R));
         pragma Assert (not Dom_In_Row (S, K0, R));
         pragma Assert (Old_S.A.Keys (K0) = R.Issuer);
      end if;
      --  The same facts, about the state before any change.
      pragma Assert (N = SC (Old_S.A, K0));
      pragma Assert
        (for all J in 1 .. N =>
           Old_S.A.H (K0, J) /= R and then not Dominates (Old_S.A.H (K0, J), R));
      pragma Assert (if N > 0 then Old_S.A.Keys (K0) = R.Issuer);
      pragma Assert (not Holds (S, R) and then not Dom (S, R));

      --  Room: decided before anything changes. W first: it is never full
      --  on a frontier (see the spec), but Add_Writer's bound is checked.
      if R.K = K_Grant and then not In_W (S.RG, R.V.Author)
        and then Registers.Count (S.RG) = Writers_Max
      then
         Result := Auth_Full;
         return;
      end if;

      declare
         Any_Drop : Boolean := False;
      begin
         for J in 1 .. N loop
            pragma Loop_Invariant
              (Any_Drop = (for some J2 in 1 .. J - 1 => Dominates (R, S.A.H (K0, J2))));
            if Dominates (R, S.A.H (K0, J)) then
               Any_Drop := True;
            end if;
         end loop;
         pragma Assert (if not Fresh then Any_Drop = Drops_In_Row (S, K0, R));
         if N = Slice and then not Any_Drop then
            pragma Assert (not Fresh);
            Result := Auth_Full;
            return;
         end if;

         pragma Assert (S.A.Slice = Slice);
         pragma Assert (N = SC (S.A, K0));
         Commit_Auth (S, R, K0, Fresh);
      end;
      Result := OK;
   end Apply_Auth;

   procedure Apply (S : in out State; R : Header; Result : out Status) is
   begin
      --  Admitted (S, R), read on the component (Regs would copy the
      --  register file).
      if Is_Data (R) and then not (R.V.T <= Ceil (S.RG) and then In_W (S.RG, R.V.Author)) then
         Result := Inadmissible;
         return;
      end if;
      if Is_Data (R) then
         Apply_Data (S, R, Result);
      else
         Apply_Auth (S, R, Result);
      end if;
   end Apply;

   ---------------------------------------------------------------------
   --  Expiry
   ---------------------------------------------------------------------

   procedure Expire (S : in out State; Horizon : Time64) is
      Old_S : constant State := S with Ghost;
      Cap   : constant Data_Size := S.Cap;
      N     : constant Data_Size := S.ND;
      Kept  : Data_Size := 0;
      Src   : Index_Map (1 .. Cap) := [others => 0] with Ghost;
      Dst   : Index_Map (1 .. Cap) := [others => 0] with Ghost;
   begin
      Lemma_Off_Mono (S);
      pragma Assert (Data_Count (S) = N);
      pragma Assert (Data_OK (S));
      for I in 1 .. N loop
         pragma Loop_Invariant (Kept <= I - 1);
         pragma Loop_Invariant (S.ND = N);
         pragma Loop_Invariant (for all J in I .. N => S.Data_H (J) = Old_S.Data_H (J));
         pragma Loop_Invariant
           (for all J in 1 .. Kept =>
              Src (J) in 1 .. I - 1
              and then S.Data_H (J) = Old_S.Data_H (Src (J))
              and then not Expired (Old_S.Data_H (Src (J)), Horizon));
         pragma Loop_Invariant
           (for all J in 1 .. Kept =>
              (for all J2 in 1 .. Kept => (if J < J2 then Src (J) < Src (J2))));
         pragma Loop_Invariant
           (for all J in 1 .. I - 1 =>
              (if Expired (Old_S.Data_H (J), Horizon) then Dst (J) = 0
               else Dst (J) in 1 .. Kept and then S.Data_H (Dst (J)) = Old_S.Data_H (J)));
         if not Expired (S.Data_H (I), Horizon) then
            Kept := Kept + 1;
            S.Data_H (Kept) := S.Data_H (I);
            Src (Kept) := I;
            Dst (I) := Kept;
         else
            Dst (I) := 0;
         end if;
      end loop;
      pragma Assert
        (for all J in 1 .. Kept =>
           (for all J2 in 1 .. Kept => (if J /= J2 then Src (J) /= Src (J2))));
      S.ND := Kept;

      pragma Assert (Data_Count (S) = Kept);
      pragma Assert (for all J in 1 .. Kept => S.Data_H (J) = Old_S.Data_H (Src (J)));
      pragma Assert (for all J in 1 .. Kept => Data_Item_OK (S, S.Data_H (J)));
      pragma Assert
        (for all J in 1 .. Kept =>
           (for all J2 in 1 .. Kept => not Dominates (S.Data_H (J2), S.Data_H (J))));
      pragma Assert
        (for all J in 1 .. Kept =>
           (for all J2 in 1 .. Kept => (if J /= J2 then S.Data_H (J) /= S.Data_H (J2))));
      pragma Assert (Data_OK (S));
      pragma Assert (Shape (S));
      pragma Assert (Slots_OK (S.A, S.Fnd));
      pragma Assert (Auth_OK (S.A, S.NS));
      pragma Assert (Coherent (S.A, S.RG));
      pragma Assert (Is_Frontier (S));
      Lemma_Extends_Refl (S.RG);

      --  In the terms of the contract.
      for J in 1 .. Kept loop
         Lemma_Held_Data (Old_S, Src (J));
         pragma Loop_Invariant
           (for all J2 in 1 .. J =>
              Held (Old_S, Src (J2)) = S.Data_H (J2) and then Holds (Old_S, S.Data_H (J2)));
      end loop;
      for I in 1 .. N loop
         pragma Assert
           (if Dst (I) /= 0 then
              Dst (I) <= Count (S)
              and then Held (S, Dst (I)) = S.Data_H (Dst (I))
              and then S.Data_H (Dst (I)) = Old_S.Data_H (I));
         pragma Assert
           (if not Expired (Old_S.Data_H (I), Horizon) then Holds (S, Old_S.Data_H (I)));
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              Expired (Old_S.Data_H (I2), Horizon) or else Holds (S, Old_S.Data_H (I2)));
      end loop;
   end Expire;

   procedure Apply_Expired (S : in out State; R : Header; Result : out Status) is
      Old_S : constant State := S with Ghost;
      Cap   : constant Data_Size := S.Cap;
      N     : constant Data_Size := S.ND;
   begin
      if not (R.V.T <= Ceil (S.RG) and then In_W (S.RG, R.V.Author)) then
         Result := Inadmissible;
         return;
      end if;
      Lemma_Classify (S, R);
      Lemma_Off_Mono (S);
      pragma Assert (Data_Count (S) = N);
      pragma Assert (Row_For (S, R) = 0 and then Has_Row (S, R));
      pragma Assert (Data_OK (S));

      for I in 1 .. N loop
         pragma Loop_Invariant
           (for all J in 1 .. I - 1 =>
              S.Data_H (J) /= R and then not Dominates (S.Data_H (J), R));
         if S.Data_H (I) = R then
            pragma Assert (Row_At (S, 0, I) = R);
            pragma Assert (In_Row (S, 0, R));
            pragma Assert (for all J in 1 .. N => not Dominates (S.Data_H (J), S.Data_H (I)));
            pragma Assert (for all J in 1 .. N => not Dominates (S.Data_H (J), R));
            pragma Assert (not Dom_In_Row (S, 0, R));
            Result := OK;
            return;
         end if;
         if Dominates (S.Data_H (I), R) then
            pragma Assert (Row_At (S, 0, I) = S.Data_H (I));
            pragma Assert (Dom_In_Row (S, 0, R));
            Result := Dominated;
            return;
         end if;
      end loop;
      pragma Assert (for all J in 1 .. N => S.Data_H (J) /= R);
      pragma Assert (for all J in 1 .. N => not Dominates (S.Data_H (J), R));
      pragma Assert
        (not (for some J in 1 .. Data_Count (S) => Dominates (S.Data_H (J), R)));
      pragma Assert (not In_Row (S, 0, R));
      pragma Assert (not Dom_In_Row (S, 0, R));

      declare
         Kept : Data_Size := 0;
         Src  : Index_Map (1 .. Cap) := [others => 0] with Ghost;
         Dst  : Index_Map (1 .. Cap) := [others => 0] with Ghost;
      begin
         for I in 1 .. N loop
            pragma Loop_Invariant (Kept <= I - 1);
            pragma Loop_Invariant (S.ND = N);
            pragma Loop_Invariant (for all J in I .. N => S.Data_H (J) = Old_S.Data_H (J));
            pragma Loop_Invariant
              (for all J in 1 .. Kept =>
                 Src (J) in 1 .. I - 1
                 and then S.Data_H (J) = Old_S.Data_H (Src (J))
                 and then not Dominates (R, Old_S.Data_H (Src (J))));
            pragma Loop_Invariant
              (for all J in 1 .. Kept =>
                 (for all J2 in 1 .. Kept => (if J < J2 then Src (J) < Src (J2))));
            pragma Loop_Invariant
              (for all J in 1 .. I - 1 =>
                 (if Dominates (R, Old_S.Data_H (J)) then Dst (J) = 0
                  else Dst (J) in 1 .. Kept and then S.Data_H (Dst (J)) = Old_S.Data_H (J)));
            if not Dominates (R, S.Data_H (I)) then
               Kept := Kept + 1;
               S.Data_H (Kept) := S.Data_H (I);
               Src (Kept) := I;
               Dst (I) := Kept;
            else
               Dst (I) := 0;
            end if;
         end loop;
         pragma Assert
           (for all J in 1 .. Kept =>
              (for all J2 in 1 .. Kept => (if J /= J2 then Src (J) /= Src (J2))));
         S.ND := Kept;

         pragma Assert (Data_Count (S) = Kept);
         pragma Assert (for all J in 1 .. Kept => S.Data_H (J) = Old_S.Data_H (Src (J)));
         pragma Assert
           (for all J in 1 .. N =>
              (if Dst (J) = 0 then Dominates (R, Old_S.Data_H (J))
               else Dst (J) in 1 .. Kept and then S.Data_H (Dst (J)) = Old_S.Data_H (J)));
         pragma Assert (for all J in 1 .. Kept => Data_Item_OK (S, S.Data_H (J)));
         pragma Assert
           (for all J in 1 .. Kept =>
              (for all J2 in 1 .. Kept => not Dominates (S.Data_H (J2), S.Data_H (J))));
         pragma Assert
           (for all J in 1 .. Kept =>
              (for all J2 in 1 .. Kept => (if J /= J2 then S.Data_H (J) /= S.Data_H (J2))));
         pragma Assert (Data_OK (S));
         pragma Assert (Shape (S));
         pragma Assert (Slots_OK (S.A, S.Fnd));
         pragma Assert (Auth_OK (S.A, S.NS));
         pragma Assert (Coherent (S.A, S.RG));
         pragma Assert (Is_Frontier (S));
         Lemma_Extends_Refl (S.RG);

         pragma Assert (for all J in 1 .. Kept => Src (J) /= 0);
         pragma Assert (Step (Old_S, S, 0, R, Src, Dst));
         Lemma_Step_Flat (Old_S, S, 0, R, Src, Dst);
         Lemma_All_Flat (S);
         Lemma_All_Flat (Old_S);
         --  Every record held now was held before, so R is not held; and
         --  R dominates none of them (a kept data record, or an
         --  authorization record, which a DEL never dominates).
         pragma Assert (for all I in 1 .. Count (S) => Holds (Old_S, Held (S, I)));
         pragma Assert (not Holds (S, R));
         for I in 1 .. Count (S) loop
            Lemma_Item (S, Row_Of (S, I), Pos_Of (S, I));
            if Row_Of (S, I) = 0 then
               pragma Assert (Pos_Of (S, I) in 1 .. Kept);
               pragma Assert (Held (S, I) = S.Data_H (Pos_Of (S, I)));
               pragma Assert (S.Data_H (Pos_Of (S, I)) = Old_S.Data_H (Src (Pos_Of (S, I))));
               pragma Assert (not Dominates (R, Held (S, I)));
            else
               pragma Assert (Is_Auth (Held (S, I)));
               pragma Assert (not Dominates (R, Held (S, I)));
            end if;
            pragma Loop_Invariant
              (for all I2 in 1 .. I => not Dominates (R, Held (S, I2)));
         end loop;
      end;
      Result := OK;
   end Apply_Expired;

end Kome.Frontier;
