pragma Ada_2022;
package body Kome.Emit with SPARK_Mode is

   -----------
   -- Floor --
   -----------

   function Floor (S : State; Tgt : Target) return Floor_View is
      R : Floor_View := (Present => False, V => Zero_Version);
   begin
      for I in 1 .. Count (S) loop
         if In_Floor (Held (S, I), Tgt) then
            if not R.Present then
               R := (Present => True, V => Held (S, I).V);
            elsif Lt (R.V, Held (S, I).V) then
               --  Every earlier candidate is <= R.V < Held (S, I).V.
               pragma Assert
                 (for all J in 1 .. I - 1 =>
                    (if In_Floor (Held (S, J), Tgt)
                     then Held (S, J).V = R.V or else Lt (Held (S, J).V, R.V)));
               for J in 1 .. I - 1 loop
                  if In_Floor (Held (S, J), Tgt) and then Held (S, J).V /= R.V then
                     Lemma_Lt_Trans (Held (S, J).V, R.V, Held (S, I).V);
                  end if;
                  pragma Loop_Invariant
                    (for all K in 1 .. J =>
                       (if In_Floor (Held (S, K), Tgt)
                        then Lt (Held (S, K).V, Held (S, I).V)));
               end loop;
               R := (Present => True, V => Held (S, I).V);
            else
               --  Not above R.V, so at or below it (T1, trichotomy).
               Lemma_Trichotomy (R.V, Held (S, I).V);
            end if;
         end if;
         pragma Loop_Invariant
           (R.Present = (for some J in 1 .. I => In_Floor (Held (S, J), Tgt)));
         pragma Loop_Invariant
           (if R.Present then
              (for some J in 1 .. I =>
                 In_Floor (Held (S, J), Tgt) and then Held (S, J).V = R.V));
         pragma Loop_Invariant
           (if R.Present then
              (for all J in 1 .. I =>
                 (if In_Floor (Held (S, J), Tgt)
                  then Held (S, J).V = R.V or else Lt (Held (S, J).V, R.V))));
         pragma Loop_Invariant
           (if not R.Present then R.V = Zero_Version);
      end loop;
      return R;
   end Floor;

   -----------------
   -- Max_Own_Seq --
   -----------------

   function Max_Own_Seq (S : State; Self : Key256) return Own_Seq_View is
      R : Own_Seq_View := (Present => False, Seq => 0);
   begin
      for I in 1 .. Count (S) loop
         if Own (Held (S, I), Self)
           and then (not R.Present or else R.Seq < Held (S, I).V.Seq)
         then
            R := (Present => True, Seq => Held (S, I).V.Seq);
         end if;
         pragma Loop_Invariant
           (R.Present = (for some J in 1 .. I => Own (Held (S, J), Self)));
         pragma Loop_Invariant
           (if R.Present then
              (for some J in 1 .. I =>
                 Own (Held (S, J), Self) and then Held (S, J).V.Seq = R.Seq));
         pragma Loop_Invariant
           (for all J in 1 .. I =>
              (if Own (Held (S, J), Self) then Held (S, J).V.Seq <= R.Seq));
         pragma Loop_Invariant (if not R.Present then R.Seq = 0);
      end loop;
      return R;
   end Max_Own_Seq;

   ------------------
   -- Emit_Version --
   ------------------

   procedure Emit_Version
     (S               : in     State;
      Tgt             : in     Target;
      Now             : in     U48;
      Self            : in     Key256;
      H               : in     Key256;
      Seq_Self        : in out U48;
      V               :    out Version;
      Result          :    out Status;
      Clone_Suspected :    out Boolean)
   is
      F : constant Floor_View   := Floor (S, Tgt);
      C : constant U48          := Ceil (Regs (S));
      O : constant Own_Seq_View := Max_Own_Seq (S, Self);
      B : constant U48          := Seq_Base (Seq_Self, O);
   begin
      Clone_Suspected := Clone_Detected (Seq_Self, O);

      if not In_W (Regs (S), Self) then
         V := Zero_Version;
         Result := Inadmissible;
         return;
      end if;

      if B = U48'Last then
         V := Zero_Version;
         Result := Seq_Exhausted;
         return;
      end if;

      Seq_Self := B + 1;
      V := V_Emit (Now, F, C, Self, Seq_Self, H);
      Lemma_Emit_Bounded (Now, F.Present, F.V.T, C);

      --  H8: every own held record has seq <= O.Seq <= B < V.Seq.
      pragma Assert
        (for all I in 1 .. Count (S) =>
           (if Own (Held (S, I), Self) then Held (S, I).V.Seq < V.Seq));

      --  So V equals no held floor version: a floor record with version V
      --  would be a data record by Self with seq V.Seq.
      if F.Present then
         pragma Assert
           (for all I in 1 .. Count (S) =>
              (if In_Floor (Held (S, I), Tgt) then Held (S, I).V /= V));
         pragma Assert (F.V /= V);
         Lemma_Trichotomy (F.V, V);
         pragma Assert (Lt (F.V, V) or else Lt (V, F.V));
         if Lt (V, F.V) then
            Lemma_Lt_Asym (V, F.V);
         else
            Lemma_Lt_Asym (F.V, V);
         end if;
      end if;

      if F.Present and then Lt (V, F.V) then
         Lemma_Shadow_At_Ceiling (Now, C, F.V, V);
         Result := Shadowed;
      else
         Result := OK;
         if F.Present then
            --  T8: every floor record is <= F.V < V.
            for I in 1 .. Count (S) loop
               if In_Floor (Held (S, I), Tgt) and then Held (S, I).V /= F.V then
                  Lemma_Lt_Trans (Held (S, I).V, F.V, V);
               end if;
               pragma Loop_Invariant
                 (for all J in 1 .. I =>
                    (if In_Floor (Held (S, J), Tgt) then Lt (Held (S, J).V, V)));
            end loop;
         end if;
         pragma Assert
           (for all I in 1 .. Count (S) =>
              (if In_Floor (Held (S, I), Tgt) then Lt (Held (S, I).V, V)));
         --  A dominator of the emitted record is In_Floor and above V,
         --  contradicting the line above (T1, asymmetry).
         for I in 1 .. Count (S) loop
            if In_Floor (Held (S, I), Tgt) then
               Lemma_Lt_Asym (Held (S, I).V, V);
            end if;
            pragma Assert (not Dominates (Held (S, I), To_Header (Tgt, V)));
            pragma Loop_Invariant
              (for all J in 1 .. I =>
                 not Dominates (Held (S, J), To_Header (Tgt, V)));
         end loop;
         pragma Assert (not Dom (S, To_Header (Tgt, V)));
         pragma Assert (Admitted (S, To_Header (Tgt, V)));
      end if;

      if F.Present and then F.V.T < C then
         Lemma_Chase (Now, C, F.V, V);
      end if;
      if Now <= C then
         Lemma_Respects_Clock (Now, F.Present, F.V.T, C);
      end if;
   end Emit_Version;

   ------------
   -- Lemmas --
   ------------

   procedure Lemma_Emit_Bounded
     (Now : U48; Has_Floor : Boolean; Floor_T, Ceil : U48) is null;

   procedure Lemma_T_Emit_Formula (Now, Floor_T, Ceil : U48) is null;

   procedure Lemma_Chase (Now, Ceil : U48; Floor_V, V : Version) is null;

   procedure Lemma_Shadow_At_Ceiling (Now, Ceil : U48; Floor_V, V : Version)
   is null;

   procedure Lemma_Raise_Unpins
     (Now : U48; Ceil1, Ceil2 : U48; Floor_V, V : Version) is null;

   procedure Lemma_Respects_Clock
     (Now : U48; Has_Floor : Boolean; Floor_T, Ceil : U48) is null;

   --------------------------
   -- Lemma_Floor_Admitted --
   --------------------------

   procedure Lemma_Floor_Admitted (S : State; Tgt : Target) is
      F : constant Floor_View := Floor (S, Tgt);
   begin
      if F.Present then
         --  Every In_Floor held record is a data record, admitted, hence
         --  at or below the ceiling; the floor is one of them.
         for I in 1 .. Count (S) loop
            pragma Assert (Admitted (S, Held (S, I)));
            pragma Loop_Invariant
              (for all J in 1 .. I =>
                 (if In_Floor (Held (S, J), Tgt)
                  then Held (S, J).V.T <= Ceil (Regs (S))));
         end loop;
      end if;
   end Lemma_Floor_Admitted;

   -------------------------
   -- Lemma_Roster_Unpins --
   -------------------------

   procedure Lemma_Roster_Unpins (S1, S2 : State; Tgt : Target) is
      F : constant Floor_View := Floor (S2, Tgt);
   begin
      if F.Present then
         --  Every In_Floor record of S2 is a data record, so it was held in
         --  S1, where it was admitted: its t is <= the old ceiling.
         for I in 1 .. Count (S2) loop
            if In_Floor (Held (S2, I), Tgt) then
               pragma Assert (Is_Data (Held (S2, I)));
               pragma Assert (Holds (S1, Held (S2, I)));
               for J in 1 .. Count (S1) loop
                  pragma Assert (Admitted (S1, Held (S1, J)));
                  pragma Loop_Invariant
                    (for all K in 1 .. J =>
                       (if Held (S1, K) = Held (S2, I)
                        then Held (S2, I).V.T <= Ceil (Regs (S1))));
               end loop;
               pragma Assert (Held (S2, I).V.T <= Ceil (Regs (S1)));
            end if;
            pragma Loop_Invariant
              (for all J in 1 .. I =>
                 (if In_Floor (Held (S2, J), Tgt)
                  then Held (S2, J).V.T <= Ceil (Regs (S1))));
         end loop;
      end if;
   end Lemma_Roster_Unpins;

end Kome.Emit;
