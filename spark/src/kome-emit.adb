pragma Ada_2022;
package body Kome.Emit with SPARK_Mode is

   ---------------------------------------------------------------------------
   --  Proof-only helpers. Ghost, so neither they nor their loops run outside
   --  -gnata (the Known gap "proof-only loops run as executable code").
   ---------------------------------------------------------------------------

   --  A version at or below B is, on the prefix, below anything whose
   --  prefix is above B's.
   procedure Lemma_Le_Prefix_Lt (A, B, C : Version) with
     Ghost, Global => null,
     Pre  => (A = B or else Lt (A, B)) and then Prefix_Lt (B, C),
     Post => Prefix_Lt (A, C);

   procedure Lemma_Le_Prefix_Lt (A, B, C : Version) is null;

   --  Two different prefixes are strictly ordered one way (T1 on the
   --  prefix).
   procedure Lemma_Prefix_Total (A, B : Version) with
     Ghost, Global => null,
     Pre  => not Same_Prefix (A, B),
     Post => Prefix_Lt (A, B) = not Prefix_Lt (B, A);

   procedure Lemma_Prefix_Total (A, B : Version) is null;

   --  Floor's step: when the running maximum Old_V is replaced by a greater
   --  New_V, every earlier candidate (at or below Old_V) is below New_V.
   procedure Lemma_Raise_Max
     (S : State; Tgt : Target; I : Held_Index; Old_V, New_V : Version)
   with
     Ghost, Global => null,
     Pre  => I <= Count (S)
             and then Lt (Old_V, New_V)
             and then (for all J in 1 .. I - 1 =>
                         (if In_Floor (Held (S, J), Tgt)
                          then Held (S, J).V = Old_V
                               or else Lt (Held (S, J).V, Old_V))),
     Post => (for all J in 1 .. I - 1 =>
                (if In_Floor (Held (S, J), Tgt)
                 then Lt (Held (S, J).V, New_V)));

   procedure Lemma_Raise_Max
     (S : State; Tgt : Target; I : Held_Index; Old_V, New_V : Version) is
   begin
      for J in 1 .. I - 1 loop
         if In_Floor (Held (S, J), Tgt) and then Held (S, J).V /= Old_V then
            Lemma_Lt_Trans (Held (S, J).V, Old_V, New_V);
         end if;
         pragma Loop_Invariant
           (for all K in 1 .. J =>
              (if In_Floor (Held (S, K), Tgt)
               then Lt (Held (S, K).V, New_V)));
      end loop;
   end Lemma_Raise_Max;

   --  Choose's OK case: every floor record is at or below the floor FV,
   --  whose prefix is below P, so every floor record's prefix is below P.
   procedure Lemma_Below_Prefix
     (S : State; Tgt : Target; FV, P : Version)
   with
     Ghost, Global => null,
     Pre  => Prefix_Lt (FV, P)
             and then (for all I in 1 .. Count (S) =>
                         (if In_Floor (Held (S, I), Tgt)
                          then Held (S, I).V = FV
                               or else Lt (Held (S, I).V, FV))),
     Post => (for all I in 1 .. Count (S) =>
                (if In_Floor (Held (S, I), Tgt)
                 then Prefix_Lt (Held (S, I).V, P)));

   procedure Lemma_Below_Prefix
     (S : State; Tgt : Target; FV, P : Version) is
   begin
      for I in 1 .. Count (S) loop
         if In_Floor (Held (S, I), Tgt) then
            Lemma_Le_Prefix_Lt (Held (S, I).V, FV, P);
         end if;
         pragma Loop_Invariant
           (for all J in 1 .. I =>
              (if In_Floor (Held (S, J), Tgt)
               then Prefix_Lt (Held (S, J).V, P)));
      end loop;
   end Lemma_Below_Prefix;

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
               Lemma_Raise_Max (S, Tgt, I, R.V, Held (S, I).V);
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

   ------------
   -- Choose --
   ------------

   procedure Choose
     (S               : in     State;
      Tgt             : in     Target;
      Now             : in     U48;
      Self            : in     Key256;
      Seq_Self        : in out U48;
      T               :    out U48;
      Seq             :    out U48;
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
         T := 0;
         Seq := 0;
         Result := Inadmissible;
         return;
      end if;

      if B = U48'Last then
         T := 0;
         Seq := 0;
         Result := Seq_Exhausted;
         return;
      end if;

      Seq_Self := B + 1;
      Seq := Seq_Self;
      T := T_Emit (Now, F.Present, F.V.T, C);
      Lemma_Emit_Bounded (Now, F.Present, F.V.T, C);

      --  H8: every own held record has seq <= O.Seq <= B < Seq.
      pragma Assert
        (for all I in 1 .. Count (S) =>
           (if Own (Held (S, I), Self) then Held (S, I).V.Seq < Seq));

      if F.Present then
         Lemma_Floor_Admitted (S, Tgt);
         pragma Assert (F.V.T <= C);
         --  The floor is a held data record: by another author, or by
         --  Self with a smaller seq. Either way its prefix differs (D8).
         pragma Assert
           (for all I in 1 .. Count (S) =>
              (if In_Floor (Held (S, I), Tgt)
               then not Same_Prefix (Held (S, I).V,
                                     Stamp (T, Self, Seq, Zero_Key))));
         pragma Assert (not Same_Prefix (F.V, Stamp (T, Self, Seq, Zero_Key)));
         Lemma_Prefix_Total (F.V, Stamp (T, Self, Seq, Zero_Key));
      end if;

      if F.Present and then Prefix_Lt (Stamp (T, Self, Seq, Zero_Key), F.V) then
         --  Only at the ceiling: below it t_emit > floor.t.
         pragma Assert (T <= F.V.T);
         pragma Assert (F.V.T >= C);
         Result := Shadowed;
      else
         Result := OK;
         if F.Present then
            --  T8: every floor record is <= F.V, whose prefix is below.
            Lemma_Below_Prefix (S, Tgt, F.V, Stamp (T, Self, Seq, Zero_Key));
         end if;
      end if;

      if F.Present and then F.V.T < C then
         Lemma_Chase (Now, C, F.V, Stamp (T, Self, Seq, Zero_Key));
      end if;
      if Now <= C then
         Lemma_Respects_Clock (Now, F.Present, F.V.T, C);
      end if;
   end Choose;

   ------------------------------------
   -- Lemma_Outcome_Independent_Of_H --
   ------------------------------------

   procedure Lemma_Outcome_Independent_Of_H
     (S : State; Tgt : Target; T : U48; Self : Key256; Seq : U48; H : Key256)
   is
      X : constant Version := Stamp (T, Self, Seq, H);
   begin
      for I in 1 .. Count (S) loop
         if In_Floor (Held (S, I), Tgt) then
            --  A floor record is data: by another author, or Own with a
            --  smaller seq, so its prefix is not X's.
            pragma Assert (Is_Data (Held (S, I)));
            pragma Assert (not Same_Prefix (Held (S, I).V, X));
            Lemma_Prefix_Decides (Held (S, I).V, X);
         end if;
         pragma Loop_Invariant
           (for all J in 1 .. I =>
              (if In_Floor (Held (S, J), Tgt)
               then Lt (Held (S, J).V, X) = Prefix_Lt (Held (S, J).V, X)
                    and then Lt (X, Held (S, J).V) = Prefix_Lt (X, Held (S, J).V)));
      end loop;
      pragma Assert (Admitted (S, To_Header (Tgt, X)));
   end Lemma_Outcome_Independent_Of_H;

   --------------------------
   -- Lemma_OK_Undominated --
   --------------------------

   procedure Lemma_OK_Undominated
     (S : State; Tgt : Target; T : U48; Self : Key256; Seq : U48; H : Key256)
   is
      X : constant Version := Stamp (T, Self, Seq, H);
      P : constant Header  := To_Header (Tgt, X);
   begin
      Lemma_Outcome_Independent_Of_H (S, Tgt, T, Self, Seq, H);
      for I in 1 .. Count (S) loop
         if In_Floor (Held (S, I), Tgt) then
            --  Prefix_Lt ignores h.
            pragma Assert (Prefix_Lt (Held (S, I).V, X));
            pragma Assert (Lt (Held (S, I).V, X));
            Lemma_Lt_Asym (Held (S, I).V, X);
         end if;
         --  A dominator of P is In_Floor and above X, contradicting the
         --  line above (T1, asymmetry).
         pragma Assert (not Dominates (Held (S, I), P));
         pragma Loop_Invariant
           (for all J in 1 .. I =>
              (if In_Floor (Held (S, J), Tgt) then Lt (Held (S, J).V, X)));
         pragma Loop_Invariant
           (for all J in 1 .. I => not Dominates (Held (S, J), P));
      end loop;
      pragma Assert (not Dom (S, P));
   end Lemma_OK_Undominated;

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
            Lemma_Frontier_Held (S, I);
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
                  Lemma_Frontier_Held (S1, J);
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
