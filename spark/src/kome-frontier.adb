pragma Ada_2022;
package body Kome.Frontier with SPARK_Mode is

   Null_Header : constant Header := (others => <>);

   function Empty (NS : Id128; Cap : Held_Count) return State is
     (Cap => Cap, NS => NS, N => 0, H => [others => Null_Header],
      RG => Registers.Empty);

   --  Proof style, learned the hard way: every assertion is written with
   --  the public functions (Held, Count, Regs), never with the fields, and
   --  each state change is followed by a "bridge" assertion relating the
   --  new state's Held to the old state's Held. SMT provers instantiate a
   --  hypothesis only on terms that already exist in the goal; the bridge
   --  creates them.

   procedure Apply
     (S       : in out State;
      R       : in     Header;
      Members : in     Member_Keys;
      Result  :    out Status)
   is
      Old_S : constant State := S with Ghost;
      Cap   : constant Held_Count := S.Cap;
      N     : constant Held_Count := S.N;
   begin
      pragma Assert (Is_Frontier (Old_S));
      pragma Assert (Count (Old_S) = N);
      --  Is_Frontier (Old_S), unfolded into the three facts used below.
      pragma Assert (for all K in 1 .. N => Admitted (Old_S, Held (Old_S, K)));
      pragma Assert
        (for all K in 1 .. N =>
           (for all K2 in 1 .. N =>
              not Dominates (Held (Old_S, K2), Held (Old_S, K))));
      pragma Assert
        (for all K in 1 .. N =>
           (for all K2 in 1 .. N =>
              (if K /= K2 then Held (Old_S, K) /= Held (Old_S, K2))));

      --  1. Registers. A roster raises the ceiling and widens W whether or
      --  not it is itself dominated on arrival (DESIGN.md §4).
      Lemma_Extends_Refl (S.RG);
      if R.K = K_Roster then
         Raise_Ceiling (S.RG, R.Ceiling);
         for M in Members'Range loop
            pragma Loop_Invariant (Count (S) = N);
            pragma Loop_Invariant (for all I in 1 .. N => Held (S, I) = Held (Old_S, I));
            pragma Loop_Invariant (Ceil (Regs (S)) >= Ceil (Regs (Old_S)));
            pragma Loop_Invariant (Extends (Regs (Old_S), Regs (S)));
            declare
               Before : constant Register_File := S.RG with Ghost;
            begin
               Add_Writer (S.RG, Members (M));
               Lemma_Extends_Trans (Old_S.RG, Before, S.RG);
            end;
         end loop;
      end if;
      --  Bridge.
      pragma Assert (Count (S) = N);
      pragma Assert (for all I in 1 .. N => Held (S, I) = Held (Old_S, I));
      pragma Assert (Ceil (Regs (S)) >= Ceil (Regs (Old_S)));
      pragma Assert (Extends (Regs (Old_S), Regs (S)));

      --  Widening the registers cannot un-admit a held record (T4'), so the
      --  held set is still its own frontier, and stays so below because the
      --  registers do not change again.
      for I in 1 .. N loop
         pragma Loop_Invariant (for all J in 1 .. I - 1 => Admitted (S, Held (S, J)));
         pragma Assert (Admitted (Old_S, Held (Old_S, I)));
         if Is_Data (Held (S, I)) then
            Lemma_Extends_In_W (Regs (Old_S), Regs (S), Data_Author (Held (S, I)));
         end if;
         pragma Assert (Admitted (S, Held (S, I)));
      end loop;
      pragma Assert (for all I in 1 .. N => Admitted (S, Held (S, I)));
      pragma Assert
        (for all K in 1 .. N =>
           (for all K2 in 1 .. N => not Dominates (Held (S, K2), Held (S, K))));
      pragma Assert
        (for all K in 1 .. N =>
           (for all K2 in 1 .. N => (if K /= K2 then Held (S, K) /= Held (S, K2))));
      pragma Assert (for all K in 1 .. N => not Dom (S, Held (S, K)));
      pragma Assert (Is_Frontier (S));

      --  2. Admission.
      if not Admitted (S, R) then
         Result := Inadmissible;
         return;
      end if;

      --  3. Already held, or beaten by something held? Every held record is
      --  admitted, so Dom (S, R) is a scan.
      for I in 1 .. N loop
         pragma Loop_Invariant (for all J in 1 .. I - 1 => Held (S, J) /= R);
         pragma Loop_Invariant (for all J in 1 .. I - 1 => not Dominates (Held (S, J), R));
         if Held (S, I) = R then
            Result := OK;
            return;
         end if;
         if Dominates (Held (S, I), R) then
            --  R is dominated by an admitted held record, and cannot also be
            --  held: a held copy would be dominated too, against Is_Frontier.
            pragma Assert (Dom (S, R));
            pragma Assert
              (for all J in 1 .. N =>
                 (if Held (S, J) = R then Dominates (Held (S, I), Held (S, J))));
            pragma Assert (for all J in 1 .. N => Held (S, J) /= R);
            Result := Dominated;
            return;
         end if;
      end loop;
      pragma Assert (for all J in 1 .. N => Held (S, J) /= R);
      pragma Assert (for all J in 1 .. N => not Dominates (Held (S, J), R));

      --  4. R is admitted, new and undominated. If the store is full, R can
      --  only be held if it frees at least one record; decide that before
      --  anything changes, so that No_Space leaves the state as it was.
      declare
         Any_Drop : Boolean := False;
         Kept     : Held_Count := 0;
         Dropped  : Held_Count := 0;
         --  Ghost witnesses: Src (J) is the old index of kept record J, and
         --  Dst (K) is where old record K went (0 if R dropped it). They make
         --  every "some record" in the invariants a named index.
         Src : array (1 .. Cap) of Held_Count := [others => 0] with Ghost;
         Dst : array (1 .. Cap) of Held_Count := [others => 0] with Ghost;
      begin
         for I in 1 .. N loop
            pragma Loop_Invariant
              (Any_Drop = (for some K in 1 .. I - 1 => Dominates (R, Held (S, K))));
            if Dominates (R, Held (S, I)) then
               Any_Drop := True;
            end if;
         end loop;
         if N = Cap and then not Any_Drop then
            Result := No_Space;
            return;
         end if;

         --  Drop what R beats, compacting in place; the order of the held
         --  array is not significant. Then hold R. Throughout, Count (S) = N
         --  and Held (S, K) for K >= I is still the old record.
         for I in 1 .. N loop
            pragma Loop_Invariant (Kept + Dropped = I - 1);
            pragma Loop_Invariant
              ((Dropped > 0) = (for some K in 1 .. I - 1 => Dominates (R, Held (Old_S, K))));
            pragma Loop_Invariant (Count (S) = N and then S.RG = S.RG'Loop_Entry);
            pragma Loop_Invariant (for all K in I .. N => Held (S, K) = Held (Old_S, K));
            pragma Loop_Invariant
              (for all J in 1 .. Kept =>
                 Src (J) in 1 .. I - 1
                 and then Held (S, J) = Held (Old_S, Src (J))
                 and then not Dominates (R, Held (Old_S, Src (J))));
            pragma Loop_Invariant
              (for all J in 1 .. Kept =>
                 (for all J2 in 1 .. Kept => (if J < J2 then Src (J) < Src (J2))));
            pragma Loop_Invariant
              (for all K in 1 .. I - 1 =>
                 (if Dominates (R, Held (Old_S, K)) then Dst (K) = 0
                  else Dst (K) in 1 .. Kept and then Held (S, Dst (K)) = Held (Old_S, K)));
            if not Dominates (R, Held (S, I)) then
               Kept := Kept + 1;
               S.H (Kept) := S.H (I);
               Src (Kept) := I;
               Dst (I) := Kept;
               pragma Assert (Held (S, Kept) = Held (Old_S, I));
            else
               Dropped := Dropped + 1;
               Dst (I) := 0;
            end if;
         end loop;
         pragma Assert (Kept + Dropped = N);
         pragma Assert (if Any_Drop then Dropped > 0);
         pragma Assert (Kept < Cap);
         Lemma_Dominates_Irrefl (R);

         --  What the compaction established, in the terms of the contract.
         pragma Assert
           (for all J in 1 .. Kept =>
              Src (J) in 1 .. N and then Held (S, J) = Held (Old_S, Src (J)));
         pragma Assert (for all J in 1 .. Kept => Admitted (S, Held (S, J)));
         pragma Assert (for all J in 1 .. Kept => not Dominates (R, Held (S, J)));
         pragma Assert (for all J in 1 .. Kept => not Dominates (Held (S, J), R));
         pragma Assert (for all J in 1 .. Kept => Held (S, J) /= R);
         pragma Assert
           (for all J in 1 .. Kept =>
              (for all J2 in 1 .. Kept => not Dominates (Held (S, J2), Held (S, J))));
         pragma Assert
           (for all J in 1 .. Kept =>
              (for all J2 in 1 .. Kept => (if J /= J2 then Src (J) /= Src (J2))));
         pragma Assert
           (for all J in 1 .. Kept =>
              (for all J2 in 1 .. Kept => (if J /= J2 then Held (S, J) /= Held (S, J2))));
         pragma Assert
           (for all K in 1 .. N =>
              (if not Dominates (R, Held (Old_S, K))
               then Dst (K) in 1 .. Kept and then Held (S, Dst (K)) = Held (Old_S, K)));

         S.N := Kept + 1;
         S.H (S.N) := R;

         --  Bridge: the new state is the kept records plus R.
         pragma Assert (Count (S) = Kept + 1);
         pragma Assert (Held (S, Kept + 1) = R);
         pragma Assert (for all J in 1 .. Kept => Held (S, J) = Held (Old_S, Src (J)));
         pragma Assert (for all J in 1 .. Count (S) => Admitted (S, Held (S, J)));
         pragma Assert
           (for all J in 1 .. Count (S) =>
              (for all J2 in 1 .. Count (S) =>
                 not Dominates (Held (S, J2), Held (S, J))));
         pragma Assert (for all J in 1 .. Count (S) => not Dom (S, Held (S, J)));
         pragma Assert
           (for all J in 1 .. Count (S) =>
              (for all J2 in 1 .. Count (S) =>
                 (if J /= J2 then Held (S, J) /= Held (S, J2))));
         pragma Assert (Is_Frontier (S));
         pragma Assert
           (for all J in 1 .. Count (S) => Holds (Old_S, Held (S, J)) or else Held (S, J) = R);
         pragma Assert
           (for all K in 1 .. N =>
              (if not Dominates (R, Held (Old_S, K)) then Holds (S, Held (Old_S, K))));
         pragma Assert
           (for all K in 1 .. N =>
              (if Dominates (R, Held (Old_S, K)) then Dom (S, Held (Old_S, K))));
         pragma Assert (Holds (S, R));
      end;
      Result := OK;
   end Apply;

end Kome.Frontier;
