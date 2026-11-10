pragma Ada_2022;
with Kome.Versions;
package body Kome.Frontier with SPARK_Mode is

   --  Proof style (CONVENTIONS.md):
   --    * each quantified definition is in this body, out of the clients'
   --      view;
   --    * after each state change, "bridge" assertions relate the new state
   --      to the old state;
   --    * each "some record" in an invariant is a named index in a ghost
   --      witness array (Src: the source of a kept record; Dst: the new
   --      position of an old record, 0 if it was dropped).
   --    * a record moves as an entry (header and tag together), so every
   --      fact "entry J is old entry Src (J)" also carries the tag.

   Null_Header : constant Header := (others => <>);
   Null_Entry  : constant Entry_Rec := (Hdr => Null_Header, Tag => 0);

   pragma Compile_Time_Error
     (Signers_Max /= 16, "Flat_Slot below is written out for 16 slots");

   ---------------------------------------------------------------------
   --  The rows and the flat view
   ---------------------------------------------------------------------

   --  Row 0 is the data row. Rows 1 .. Signers_Max are the slots.
   function Row_Count (S : State; K : Slot_Number) return Natural is
     (if K = 0 then Data_Count (S) else SC (S.A, K));

   function Row_Ent (S : State; K : Slot_Number; J : Integer) return Entry_Rec is
     (if K = 0 then (if J in 1 .. Data_Count (S) then S.Data_E (J) else Null_Entry)
      elsif J in 1 .. SC (S.A, K) then S.A.H (K, J)
      else Null_Entry);

   function Row_At (S : State; K : Slot_Number; J : Integer) return Header is
     (Row_Ent (S, K, J).Hdr);

   --  The slot that contains an authorization position J (counted after
   --  the data row): the first K with J <= Offs (K + 1), else the last
   --  slot.
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

   function Flat_Ent (S : State; I : Held_Index) return Entry_Rec is
     (Row_Ent (S, Row_Of (S, I), Pos_Of (S, I)));

   function Held (S : State; I : Held_Index) return Header is (Flat_Ent (S, I).Hdr);

   function Tag (S : State; I : Held_Index) return U64 is (Flat_Ent (S, I).Tag);

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

   --  The first flat index that holds X, 0 if none.
   function Find_Held (S : State; X : Header) return Held_Count with
     Global => null,
     Post   => Find_Held'Result <= Count (S)
               and then (if Find_Held'Result = 0 then not Holds (S, X)
                         else Held (S, Find_Held'Result) = X)
   is
      --  Proved; at run time the invariants would make each call
      --  quadratic (CONVENTIONS.md, IMPLEMENTATION_PLAN.md).
      pragma Assertion_Policy (Loop_Invariant => Ignore);
   begin
      for I in 1 .. Count (S) loop
         if Held (S, I) = X then
            return I;
         end if;
         pragma Loop_Invariant (for all I2 in 1 .. I => Held (S, I2) /= X);
      end loop;
      return 0;
   end Find_Held;

   function Tag_Of (S : State; X : Header) return U64 is
     (declare
        I : constant Held_Count := Find_Held (S, X);
      begin
        (if I = 0 then 0 else Tag (S, I)));

   function Has_Tag (S : State; X : Header; T : U64) return Boolean is
     (for some J in 1 .. Count (S) => Held (S, J) = X and then Tag (S, J) = T);

   ---------------------------------------------------------------------
   --  The invariant
   ---------------------------------------------------------------------

   --  Capacities and the slot offsets of the authorization rows.
   function Auth_Shape (A : Auth_Rows) return Boolean is
     (A.NSlots >= 1
      and then (for all K in Slot_Index => (if K > A.NSlots then A.NA (K) = 0))
      and then A.Offs (1) = 0
      and then (for all K in 2 .. Signers_Max => A.Offs (K) = A.Offs (K - 1) + A.NA (K - 1))
      and then (for all K in Slot_Index => A.Offs (K) <= (K - 1) * Slice_Max)
      and then A.NAuth = A.Offs (Signers_Max) + A.NA (Signers_Max));

   function Shape (S : State) return Boolean is
     (Auth_Shape (S.A) and then S.ND <= S.Cap);

   function Slots_OK (A : Auth_Rows; Fnd : Key256) return Boolean is
     (A.Keys (1) = Fnd
      and then (for all K in 1 .. A.NSlots =>
                  (for all K2 in 1 .. A.NSlots =>
                     (if K /= K2 then A.Keys (K) /= A.Keys (K2))))
      and then (for all K in 2 .. A.NSlots => A.NA (K) >= 1));

   ---------------------------------------------------------------------
   --  The admission views over the authorization rows (SIMPLIFY.md S6)
   ---------------------------------------------------------------------

   function Roster_At (A : Auth_Rows; C : U48) return Boolean is
     (for some K in Slot_Index =>
        (for some J in 1 .. SC (A, K) =>
           A.H (K, J).Hdr.K = K_Roster and then A.H (K, J).Hdr.V.T = C));

   function Grant_Of (A : Auth_Rows; W : Key256) return Boolean is
     (for some K in Slot_Index =>
        (for some J in 1 .. SC (A, K) =>
           A.H (K, J).Hdr.K = K_Grant and then A.H (K, J).Hdr.V.Author = W));

   --  A held GRANT of W with cap C.
   function Grant_Cap_Of (A : Auth_Rows; W : Key256; C : U48) return Boolean is
     (for some K in Slot_Index =>
        (for some J in 1 .. SC (A, K) =>
           A.H (K, J).Hdr.K = K_Grant and then A.H (K, J).Hdr.V.Author = W
           and then A.H (K, J).Hdr.V.T = C));

   --  C bounds every ceiling of the rows, and it is a held roster's
   --  ceiling or 0: the definition of maxceil.
   function Is_Max_Ceil (A : Auth_Rows; C : U48) return Boolean is
     ((for all K in Slot_Index =>
         (for all J in 1 .. SC (A, K) => Ceil_Of (A.H (K, J).Hdr) <= C))
      and then (C = 0 or else Roster_At (A, C)));

   --  C bounds the cap of every held GRANT of W, and it is such a cap, or
   --  0 if there is none: the definition of wcap.
   function Is_W_Cap (A : Auth_Rows; W : Key256; C : U48) return Boolean is
     ((for all K in Slot_Index =>
         (for all J in 1 .. SC (A, K) =>
            (if A.H (K, J).Hdr.K = K_Grant and then A.H (K, J).Hdr.V.Author = W
             then A.H (K, J).Hdr.V.T <= C)))
      and then (if Grant_Of (A, W) then Grant_Cap_Of (A, W, C) else C = 0));

   --  Two row sets that agree on every used position.
   function Rows_Agree (A1, A2 : Auth_Rows) return Boolean is
     ((for all K in Slot_Index => A1.NA (K) = A2.NA (K))
      and then (for all K in Slot_Index =>
                  (for all J in 1 .. SC (A1, K) => A1.H (K, J).Hdr = A2.H (K, J).Hdr)))
   with Ghost;

   --  The admission views over the rows, opaque to the rest of this body:
   --  their quantified definitions reach a proof only through the lemmas
   --  below, so the data-row proofs, which mention Admitted, do not carry
   --  them.
   package Auth_Views with SPARK_Mode is

      function Max_Ceil_A (A : Auth_Rows) return U48 with Global => null;

      function In_W_A (A : Auth_Rows; W : Key256) return Boolean with Global => null;

      function W_Cap_A (A : Auth_Rows; W : Key256) return U48 with
        Global => null,
        Post   => (if not In_W_A (A, W) then W_Cap_A'Result = 0);

      procedure Lemma_Max_Ceil_A (A : Auth_Rows) with
        Ghost, Global => null,
        Post => Is_Max_Ceil (A, Max_Ceil_A (A));

      procedure Lemma_In_W_A (A : Auth_Rows; W : Key256) with
        Ghost, Global => null,
        Post => In_W_A (A, W) = Grant_Of (A, W);

      procedure Lemma_W_Cap_A (A : Auth_Rows; W : Key256) with
        Ghost, Global => null,
        Post => Is_W_Cap (A, W, W_Cap_A (A, W));

      --  The definitions determine the views.
      procedure Lemma_Max_Ceil_Unique (A : Auth_Rows; C : U48) with
        Ghost, Global => null,
        Pre  => Is_Max_Ceil (A, C),
        Post => Max_Ceil_A (A) = C;

      procedure Lemma_W_Cap_Unique (A : Auth_Rows; W : Key256; C : U48) with
        Ghost, Global => null,
        Pre  => Is_W_Cap (A, W, C),
        Post => W_Cap_A (A, W) = C;

      procedure Lemma_Rows_Agree_Views (A1, A2 : Auth_Rows; W : Key256) with
        Ghost, Global => null,
        Pre  => Rows_Agree (A1, A2),
        Post => Max_Ceil_A (A1) = Max_Ceil_A (A2)
                and then In_W_A (A1, W) = In_W_A (A2, W)
                and then W_Cap_A (A1, W) = W_Cap_A (A2, W);

   end Auth_Views;

   package body Auth_Views with SPARK_Mode is

      function Max_Ceil_Impl (A : Auth_Rows) return U48 with
        Global => null,
        Post   => Is_Max_Ceil (A, Max_Ceil_Impl'Result)
      is
         --  Proved; at run time the invariants would make each call
         --  quadratic (CONVENTIONS.md, IMPLEMENTATION_PLAN.md).
         pragma Assertion_Policy (Loop_Invariant => Ignore);
         Best : U48 := 0;
         WK   : Slot_Index := 1 with Ghost;
         WJ   : Natural := 0 with Ghost;
      begin
         for K in Slot_Index loop
            for J in 1 .. SC (A, K) loop
               if Ceil_Of (A.H (K, J).Hdr) > Best then
                  Best := Ceil_Of (A.H (K, J).Hdr);
                  WK := K;
                  WJ := J;
               end if;
               pragma Loop_Invariant
                 (for all K2 in 1 .. K - 1 =>
                    (for all J2 in 1 .. SC (A, K2) => Ceil_Of (A.H (K2, J2).Hdr) <= Best));
               pragma Loop_Invariant
                 (for all J2 in 1 .. J => Ceil_Of (A.H (K, J2).Hdr) <= Best);
               pragma Loop_Invariant
                 (Best = 0 or else
                    (WJ in 1 .. SC (A, WK) and then A.H (WK, WJ).Hdr.K = K_Roster
                     and then A.H (WK, WJ).Hdr.V.T = Best));
            end loop;
            pragma Loop_Invariant
              (for all K2 in 1 .. K =>
                 (for all J2 in 1 .. SC (A, K2) => Ceil_Of (A.H (K2, J2).Hdr) <= Best));
            pragma Loop_Invariant
              (Best = 0 or else
                 (WJ in 1 .. SC (A, WK) and then A.H (WK, WJ).Hdr.K = K_Roster
                  and then A.H (WK, WJ).Hdr.V.T = Best));
         end loop;
         return Best;
      end Max_Ceil_Impl;

      function W_Cap_Impl (A : Auth_Rows; W : Key256) return U48 with
        Global => null,
        Post   => Is_W_Cap (A, W, W_Cap_Impl'Result)
      is
         --  Proved; at run time the invariants would make each call
         --  quadratic (CONVENTIONS.md, IMPLEMENTATION_PLAN.md).
         pragma Assertion_Policy (Loop_Invariant => Ignore);
         Best  : U48 := 0;
         Found : Boolean := False;
         WK    : Slot_Index := 1 with Ghost;
         WJ    : Natural := 0 with Ghost;
      begin
         for K in Slot_Index loop
            for J in 1 .. SC (A, K) loop
               if A.H (K, J).Hdr.K = K_Grant and then A.H (K, J).Hdr.V.Author = W
                 and then (not Found or else A.H (K, J).Hdr.V.T > Best)
               then
                  Best := A.H (K, J).Hdr.V.T;
                  Found := True;
                  WK := K;
                  WJ := J;
               end if;
               pragma Loop_Invariant
                 (for all K2 in 1 .. K - 1 =>
                    (for all J2 in 1 .. SC (A, K2) =>
                       (if A.H (K2, J2).Hdr.K = K_Grant and then A.H (K2, J2).Hdr.V.Author = W
                        then Found and then A.H (K2, J2).Hdr.V.T <= Best)));
               pragma Loop_Invariant
                 (for all J2 in 1 .. J =>
                    (if A.H (K, J2).Hdr.K = K_Grant and then A.H (K, J2).Hdr.V.Author = W
                     then Found and then A.H (K, J2).Hdr.V.T <= Best));
               pragma Loop_Invariant
                 (if Found then
                    WJ in 1 .. SC (A, WK) and then A.H (WK, WJ).Hdr.K = K_Grant
                    and then A.H (WK, WJ).Hdr.V.Author = W
                    and then A.H (WK, WJ).Hdr.V.T = Best
                  else Best = 0);
            end loop;
            pragma Loop_Invariant
              (for all K2 in 1 .. K =>
                 (for all J2 in 1 .. SC (A, K2) =>
                    (if A.H (K2, J2).Hdr.K = K_Grant and then A.H (K2, J2).Hdr.V.Author = W
                     then Found and then A.H (K2, J2).Hdr.V.T <= Best)));
            pragma Loop_Invariant
              (if Found then
                 WJ in 1 .. SC (A, WK) and then A.H (WK, WJ).Hdr.K = K_Grant
                 and then A.H (WK, WJ).Hdr.V.Author = W
                 and then A.H (WK, WJ).Hdr.V.T = Best
               else Best = 0);
         end loop;
         pragma Assert (Found = Grant_Of (A, W));
         return Best;
      end W_Cap_Impl;


      function Max_Ceil_A (A : Auth_Rows) return U48 is (Max_Ceil_Impl (A));

      function In_W_A (A : Auth_Rows; W : Key256) return Boolean is (Grant_Of (A, W));

      function W_Cap_A (A : Auth_Rows; W : Key256) return U48 is (W_Cap_Impl (A, W));

      procedure Lemma_Max_Ceil_A (A : Auth_Rows) is null;

      procedure Lemma_In_W_A (A : Auth_Rows; W : Key256) is null;

      procedure Lemma_W_Cap_A (A : Auth_Rows; W : Key256) is null;

      procedure Lemma_Max_Ceil_Unique (A : Auth_Rows; C : U48) is
         M : constant U48 := Max_Ceil_A (A);
      begin
         if M /= C then
            if M < C then
               pragma Assert (Roster_At (A, C));
            else
               pragma Assert (Roster_At (A, M));
            end if;
            pragma Assert (False);
         end if;
      end Lemma_Max_Ceil_Unique;

      procedure Lemma_W_Cap_Unique (A : Auth_Rows; W : Key256; C : U48) is
         M : constant U48 := W_Cap_A (A, W);
      begin
         if In_W_A (A, W) and then M /= C then
            if M < C then
               pragma Assert (Grant_Cap_Of (A, W, C));
            else
               pragma Assert (Grant_Cap_Of (A, W, M));
            end if;
            pragma Assert (False);
         end if;
      end Lemma_W_Cap_Unique;

      procedure Lemma_Rows_Agree_Views (A1, A2 : Auth_Rows; W : Key256) is
      begin
         pragma Assert (Roster_At (A1, Max_Ceil_A (A1)) = Roster_At (A2, Max_Ceil_A (A1)));
         pragma Assert (Is_Max_Ceil (A2, Max_Ceil_A (A1)));
         Lemma_Max_Ceil_Unique (A2, Max_Ceil_A (A1));
         pragma Assert (Grant_Of (A1, W) = Grant_Of (A2, W));
         pragma Assert
           (Grant_Cap_Of (A1, W, W_Cap_A (A1, W)) = Grant_Cap_Of (A2, W, W_Cap_A (A1, W)));
         declare
            C : constant U48 := W_Cap_A (A1, W);
         begin
            pragma Assert (Is_W_Cap (A1, W, C));
            for K in Slot_Index loop
               for J in 1 .. SC (A2, K) loop
                  pragma Assert (J <= SC (A1, K));
                  pragma Assert (A2.H (K, J).Hdr = A1.H (K, J).Hdr);
                  pragma Assert
                    (if A1.H (K, J).Hdr.K = K_Grant and then A1.H (K, J).Hdr.V.Author = W
                     then A1.H (K, J).Hdr.V.T <= C);
                  pragma Loop_Invariant
                    (for all J2 in 1 .. J =>
                       (if A2.H (K, J2).Hdr.K = K_Grant and then A2.H (K, J2).Hdr.V.Author = W
                        then A2.H (K, J2).Hdr.V.T <= C));
               end loop;
               pragma Loop_Invariant
                 (for all K2 in 1 .. K =>
                    (for all J2 in 1 .. SC (A2, K2) =>
                       (if A2.H (K2, J2).Hdr.K = K_Grant and then A2.H (K2, J2).Hdr.V.Author = W
                        then A2.H (K2, J2).Hdr.V.T <= C)));
            end loop;
         end;
         pragma Assert (Is_W_Cap (A2, W, W_Cap_A (A1, W)));
         Lemma_W_Cap_Unique (A2, W, W_Cap_A (A1, W));
      end Lemma_Rows_Agree_Views;


   end Auth_Views;
   use Auth_Views;

   function Max_Ceil (S : State) return U48 is (Max_Ceil_A (S.A));

   function In_W (S : State; K : Key256) return Boolean is (In_W_A (S.A, K));

   function W_Cap (S : State; K : Key256) return U48 is (W_Cap_A (S.A, K));

   function Data_Item_OK (S : State; X : Header) return Boolean is
     (Is_Data (X) and then Canonical (X) and then Admitted (S, X));

   function Data_OK (S : State) return Boolean is
     ((for all I in 1 .. Data_Count (S) => Data_Item_OK (S, S.Data_E (I).Hdr))
      and then (for all I in 1 .. Data_Count (S) =>
                  (for all I2 in 1 .. Data_Count (S) =>
                     not Dominates (S.Data_E (I2).Hdr, S.Data_E (I).Hdr)))
      and then (for all I in 1 .. Data_Count (S) =>
                  (for all I2 in 1 .. Data_Count (S) =>
                     (if I /= I2 then S.Data_E (I).Hdr /= S.Data_E (I2).Hdr))));

   function Auth_Item_OK (S : State; K : Slot_Index; X : Header) return Boolean is
     (Is_Auth (X) and then Canonical (X) and then X.Issuer = S.A.Keys (K));

   --  Each slot holds canonical authorization records issued by its key,
   --  as an antichain without repetition. It is written flat (no per-row
   --  predicate under the quantifier) because the provers need this form.
   function Auth_OK (A : Auth_Rows) return Boolean is
     ((for all K in Slot_Index =>
         (for all J in 1 .. SC (A, K) =>
            Is_Auth (A.H (K, J).Hdr) and then Canonical (A.H (K, J).Hdr)
            and then A.H (K, J).Hdr.Issuer = A.Keys (K)))
      and then (for all K in Slot_Index =>
                  (for all J in 1 .. SC (A, K) =>
                     (for all J2 in 1 .. SC (A, K) =>
                        not Dominates (A.H (K, J2).Hdr, A.H (K, J).Hdr))))
      and then (for all K in Slot_Index =>
                  (for all J in 1 .. SC (A, K) =>
                     (for all J2 in 1 .. SC (A, K) =>
                        (if J /= J2 then A.H (K, J).Hdr /= A.H (K, J2).Hdr)))));

   --  The order of the data row (AUDIT.md G25): entity-major, by the key
   --  (ent, kind, fh). A DEL (kind 3, fh = 0) sorts first in its entity's
   --  run. This is the order of the design's data element key (SIMPLIFY.md
   --  S18: 03 ‖ ent ‖ sub ‖ fh ‖ h, sub = 0 for DEL and 1 for PUT).
   --
   --  Ent_Lt is the unsigned big-endian order on Id128 (Kome.Keys.Id_Lt).
   function Ent_Lt (A, B : Id128) return Boolean is
     (A.W0 < B.W0 or else (A.W0 = B.W0 and then
      (A.W1 < B.W1 or else (A.W1 = B.W1 and then
      (A.W2 < B.W2 or else (A.W2 = B.W2 and then A.W3 < B.W3))))));

   function Key_Lt (A, B : Header) return Boolean is
     (Ent_Lt (A.Ent, B.Ent)
      or else (A.Ent = B.Ent
               and then (A.K < B.K or else (A.K = B.K and then Lt (A.FH, B.FH)))));

   --  The first N records of H are strictly increasing in the key. On a
   --  frontier the key is unique: two held data records with one key would
   --  differ only in V, and the greater would dominate the other
   --  (Lemma_Key_Total).
   function Sorted_Row (H : Entry_Array; N : Natural) return Boolean is
     (H'First = 1 and then N <= H'Last
      and then (for all I in 1 .. N =>
                  (for all J in I + 1 .. N => Key_Lt (H (I).Hdr, H (J).Hdr))));

   function Data_Sorted (S : State) return Boolean is
     (Sorted_Row (S.Data_E, Data_Count (S)));

   function Is_Frontier (S : State) return Boolean is
     (Shape (S) and then Slots_OK (S.A, S.Fnd) and then Data_OK (S)
      and then Data_Sorted (S) and then Auth_OK (S.A));

   function Drops_Any (S : State; R : Header) return Boolean is
     (for some I in 1 .. Count (S) => Dominates (R, Held (S, I)));

   function Unchanged (Old, Upd : State) return Boolean is
     (Old.Cap = Upd.Cap
      and then Old.Fnd = Upd.Fnd
      and then Old.ND = Upd.ND
      and then (for all I in 1 .. Data_Count (Old) => Upd.Data_E (I) = Old.Data_E (I))
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
             and then S.A.NAuth <= Signers_Max * Slice_Max
             and then Data_Count (S) = S.ND
             and then Auth_Count (S) = S.A.NAuth
             and then Count (S) = S.ND + S.A.NAuth
             and then (for all K in Slot_Index => Slot_Count (S, K) = S.A.NA (K))
   is
      --  Proved; at run time the invariants would cost O(16^2) per call.
      pragma Assertion_Policy (Loop_Invariant => Ignore);
   begin
      for K2 in 2 .. Signers_Max loop
         pragma Assert (S.A.Offs (K2) = S.A.Offs (K2 - 1) + S.A.NA (K2 - 1));
         pragma Loop_Invariant
           (for all K in 2 .. K2 =>
              (for all K1 in 1 .. K - 1 => S.A.Offs (K1) + S.A.NA (K1) <= S.A.Offs (K)));
      end loop;
      pragma Assert (S.A.Offs (Signers_Max) <= (Signers_Max - 1) * Slice_Max);
   end Lemma_Off_Mono;

   --  Flat_Slot finds the slot interval that contains a position.
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
             and then Flat_Ent (S, Flat_Index (S, K, J)) = Row_Ent (S, K, J)
             and then Tag (S, Flat_Index (S, K, J)) = Row_Ent (S, K, J).Tag
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
             and then Flat_Ent (S, I) = Row_Ent (S, Row_Of (S, I), Pos_Of (S, I))
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
      --  Proved; at run time the invariants would cost O(n^3) per Apply
      --  (CONVENTIONS.md: a region listed in IMPLEMENTATION_PLAN.md).
      pragma Assertion_Policy (Assert => Ignore, Loop_Invariant => Ignore);
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
   --  The private lemmas below are called once per held record inside
   --  other lemmas; their Is_Frontier precondition is proved at each call,
   --  and at run time it would make an Apply cost O(n^3)
   --  (CONVENTIONS.md: a region listed in IMPLEMENTATION_PLAN.md).
   pragma Assertion_Policy (Pre => Ignore);

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
      if K = 0 then
         pragma Assert (Row_At (S, K, J) = S.Data_E (J).Hdr);
         pragma Assert (Data_Item_OK (S, S.Data_E (J).Hdr));
      else
         pragma Assert (Row_At (S, K, J) = S.A.H (K, J).Hdr);
         pragma Assert (Is_Auth (Row_At (S, K, J)));
      end if;
   end Lemma_Item;

   --  No other flat index holds the record at I.
   procedure Lemma_Distinct_Held (S : State; I : Held_Index) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S) and then I <= Count (S),
     Post => (for all J in 1 .. Count (S) =>
                not Dominates (Held (S, J), Held (S, I))
                and then (if J /= I then Held (S, J) /= Held (S, I)))
   is
      --  Proved; at run time the invariants would cost O(n^2) per record.
      pragma Assertion_Policy (Assert => Ignore, Loop_Invariant => Ignore);
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
           (for all J2 in 1 .. J =>
              not Dominates (Held (S, J2), Held (S, I))
              and then (if J2 /= I then Held (S, J2) /= Held (S, I)));
      end loop;
   end Lemma_Distinct_Held;

   procedure Lemma_Tag_Of_P (S : State; I : Held_Index) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S) and then I <= Count (S),
     Post => Tag_Of (S, Held (S, I)) = Tag (S, I)
   is
      J : constant Held_Count := Find_Held (S, Held (S, I));
   begin
      Lemma_Distinct_Held (S, I);
      pragma Assert (J /= 0);
      pragma Assert (Held (S, J) = Held (S, I));
      pragma Assert (J = I);
   end Lemma_Tag_Of_P;

   pragma Assertion_Policy (Pre => Check);

   ---------------------------------------------------------------------
   --  Classification: the row in which a record can be held, dominated or
   --  dropped (Kome.Headers.Lemma_Same_Row).
   ---------------------------------------------------------------------

   function Row_For (S : State; R : Header) return Slot_Number is
     (if Is_Data (R) then 0 else Slot_Of (S, R.Issuer));

   function Has_Row (S : State; R : Header) return Boolean is
     (Is_Data (R) or else Slot_Of (S, R.Issuer) /= 0);

   function In_Row (S : State; K : Slot_Number; X : Header) return Boolean is
     (if K = 0 then (for some J in 1 .. Data_Count (S) => S.Data_E (J).Hdr = X)
      else (for some J in 1 .. SC (S.A, K) => S.A.H (K, J).Hdr = X));

   function Dom_In_Row (S : State; K : Slot_Number; X : Header) return Boolean is
     (if K = 0 then (for some J in 1 .. Data_Count (S) => Dominates (S.Data_E (J).Hdr, X))
      else (for some J in 1 .. SC (S.A, K) => Dominates (S.A.H (K, J).Hdr, X)));

   function Drops_In_Row (S : State; K : Slot_Number; R : Header) return Boolean is
     (if K = 0 then (for some J in 1 .. Data_Count (S) => Dominates (R, S.Data_E (J).Hdr))
      else (for some J in 1 .. SC (S.A, K) => Dominates (R, S.A.H (K, J).Hdr)));

   procedure Lemma_Classify (S : State; R : Header) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S) and then Canonical (R),
     Post => Holds (S, R) = (Has_Row (S, R) and then In_Row (S, Row_For (S, R), R))
             and then Dom (S, R) = (Has_Row (S, R) and then Dom_In_Row (S, Row_For (S, R), R))
             and then Drops_Any (S, R)
                      = (Has_Row (S, R) and then Drops_In_Row (S, Row_For (S, R), R))
   is
      RK : constant Slot_Number := Row_For (S, R);
      --  Proved; at run time the invariants would cost O(n^3) per Apply
      --  (CONVENTIONS.md: a region listed in IMPLEMENTATION_PLAN.md).
      pragma Assertion_Policy (Assert => Ignore, Loop_Invariant => Ignore);
   begin
      Lemma_Off_Mono (S);
      Lemma_All_Flat (S);
      --  Flat to row: a held record that is equal to R, dominates R or is
      --  dominated by R is in R's row.
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
              Row_At (S, RK, J) = (if RK = 0 then S.Data_E (J).Hdr else S.A.H (RK, J).Hdr));
         pragma Assert
           (if In_Row (S, RK, R) then
              (for some J in 1 .. Row_Count (S, RK) => Row_At (S, RK, J) = R));
         pragma Assert (if In_Row (S, RK, R) then Holds (S, R));
      end if;
   end Lemma_Classify;

   ---------------------------------------------------------------------
   --  One step on one row K0:
   --    * no other row changes;
   --    * row K0 keeps some of its old records (Src) and possibly adds R;
   --    * Dst gives the new position of each old record in row K0
   --      (0: dropped).
   ---------------------------------------------------------------------

   type Index_Map is array (Positive range <>) of Natural with Ghost;

   function Step
     (Old, Upd : State; K0 : Slot_Number; R : Header; Tg : U64; Src, Dst : Index_Map)
      return Boolean
   is
     (Src'First = 1 and then Dst'First = 1
      and then Src'Last >= Row_Count (Upd, K0)
      and then Dst'Last >= Row_Count (Old, K0)
      and then (for all K in Slot_Number =>
                  (if K /= K0 then
                     Row_Count (Upd, K) = Row_Count (Old, K)
                     and then (for all J in 1 .. Row_Count (Old, K) =>
                                 Row_Ent (Upd, K, J) = Row_Ent (Old, K, J))))
      and then (for all J in 1 .. Row_Count (Upd, K0) =>
                  (if Src (J) = 0 then Row_Ent (Upd, K0, J) = (Hdr => R, Tag => Tg)
                   else Src (J) <= Row_Count (Old, K0)
                        and then Row_Ent (Upd, K0, J) = Row_Ent (Old, K0, Src (J))))
      and then (for all J in 1 .. Row_Count (Old, K0) =>
                  (if Dst (J) /= 0 then
                     Dst (J) <= Row_Count (Upd, K0)
                     and then Row_Ent (Upd, K0, Dst (J)) = Row_Ent (Old, K0, J))))
   with Ghost;

   --  The step in the flat view: Frontier.lean `keep`.
   procedure Lemma_Step_Flat
     (Old, Upd : State; K0 : Slot_Number; R : Header; Tg : U64; Src, Dst : Index_Map)
   with
     Ghost, Global => null,
     Pre  => Shape (Old) and then Shape (Upd)
             and then Step (Old, Upd, K0, R, Tg, Src, Dst),
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
      --  Proved; at run time the invariants would cost O(n^3) per Apply
      --  (CONVENTIONS.md: a region listed in IMPLEMENTATION_PLAN.md).
      pragma Assertion_Policy (Assert => Ignore, Loop_Invariant => Ignore);
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


   --  The tags across a step: R has the new tag, and every other record
   --  of Upd has a tag that it had in Old.
   procedure Lemma_Step_Tags
     (Old, Upd : State; K0 : Slot_Number; R : Header; Tg : U64; Src, Dst : Index_Map)
   with
     Ghost, Global => null,
     Pre  => Shape (Old) and then Shape (Upd) and then not Holds (Old, R)
             and then Step (Old, Upd, K0, R, Tg, Src, Dst),
     Post => (for all I in 1 .. Count (Upd) =>
                (if Held (Upd, I) = R then Tag (Upd, I) = Tg
                 else Has_Tag (Old, Held (Upd, I), Tag (Upd, I))))
   is
      --  Proved; at run time the invariant would cost O(n^2) per Apply.
      pragma Assertion_Policy (Assert => Ignore, Loop_Invariant => Ignore);
   begin
      Lemma_All_Flat (Upd);
      for I in 1 .. Count (Upd) loop
         declare
            K : constant Slot_Number := Row_Of (Upd, I);
            P : constant Integer := Pos_Of (Upd, I);
         begin
            pragma Assert (Flat_Ent (Upd, I) = Row_Ent (Upd, K, P));
            if K /= K0 then
               Lemma_Row_Flat (Old, K, P);
               pragma Assert (Flat_Ent (Old, Flat_Index (Old, K, P)) = Flat_Ent (Upd, I));
               pragma Assert (Held (Upd, I) /= R);
               pragma Assert (Has_Tag (Old, Held (Upd, I), Tag (Upd, I)));
            elsif Src (P) /= 0 then
               Lemma_Row_Flat (Old, K0, Src (P));
               pragma Assert (Flat_Ent (Old, Flat_Index (Old, K0, Src (P))) = Flat_Ent (Upd, I));
               pragma Assert (Held (Upd, I) /= R);
               pragma Assert (Has_Tag (Old, Held (Upd, I), Tag (Upd, I)));
            else
               pragma Assert (Flat_Ent (Upd, I) = (Hdr => R, Tag => Tg));
            end if;
         end;
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              (if Held (Upd, I2) = R then Tag (Upd, I2) = Tg
               else Has_Tag (Old, Held (Upd, I2), Tag (Upd, I2))));
      end loop;
   end Lemma_Step_Tags;

   ---------------------------------------------------------------------
   --  Coherence across an authorization step
   ---------------------------------------------------------------------

   procedure Find_Roster (A : Auth_Rows; C : U48; K : out Slot_Index; J : out Positive) with
     Ghost, Global => null,
     Pre  => Roster_At (A, C),
     Post => J <= SC (A, K) and then A.H (K, J).Hdr.K = K_Roster and then A.H (K, J).Hdr.V.T = C
   is
   begin
      for K2 in Slot_Index loop
         for J2 in 1 .. SC (A, K2) loop
            if A.H (K2, J2).Hdr.K = K_Roster and then A.H (K2, J2).Hdr.V.T = C then
               K := K2;
               J := J2;
               return;
            end if;
            pragma Loop_Invariant
              (for all J3 in 1 .. J2 =>
                 not (A.H (K2, J3).Hdr.K = K_Roster and then A.H (K2, J3).Hdr.V.T = C));
         end loop;
         pragma Loop_Invariant
           (for all K3 in 1 .. K2 =>
              (for all J3 in 1 .. SC (A, K3) =>
                 not (A.H (K3, J3).Hdr.K = K_Roster and then A.H (K3, J3).Hdr.V.T = C)));
      end loop;
      pragma Assert (False);
      K := 1;
      J := 1;
   end Find_Roster;

   procedure Find_Grant (A : Auth_Rows; W : Key256; K : out Slot_Index; J : out Positive) with
     Ghost, Global => null,
     Pre  => Grant_Of (A, W),
     Post => J <= SC (A, K) and then A.H (K, J).Hdr.K = K_Grant and then A.H (K, J).Hdr.V.Author = W
   is
   begin
      for K2 in Slot_Index loop
         for J2 in 1 .. SC (A, K2) loop
            if A.H (K2, J2).Hdr.K = K_Grant and then A.H (K2, J2).Hdr.V.Author = W then
               K := K2;
               J := J2;
               return;
            end if;
            pragma Loop_Invariant
              (for all J3 in 1 .. J2 =>
                 not (A.H (K2, J3).Hdr.K = K_Grant and then A.H (K2, J3).Hdr.V.Author = W));
         end loop;
         pragma Loop_Invariant
           (for all K3 in 1 .. K2 =>
              (for all J3 in 1 .. SC (A, K3) =>
                 not (A.H (K3, J3).Hdr.K = K_Grant and then A.H (K3, J3).Hdr.V.Author = W)));
      end loop;
      pragma Assert (False);
      K := 1;
      J := 1;
   end Find_Grant;

   procedure Find_Grant_Cap
     (A : Auth_Rows; W : Key256; C : U48; K : out Slot_Index; J : out Positive)
   with
     Ghost, Global => null,
     Pre  => Grant_Cap_Of (A, W, C),
     Post => J <= SC (A, K) and then A.H (K, J).Hdr.K = K_Grant
             and then A.H (K, J).Hdr.V.Author = W and then A.H (K, J).Hdr.V.T = C
   is
   begin
      for K2 in Slot_Index loop
         for J2 in 1 .. SC (A, K2) loop
            if A.H (K2, J2).Hdr.K = K_Grant and then A.H (K2, J2).Hdr.V.Author = W
              and then A.H (K2, J2).Hdr.V.T = C
            then
               K := K2;
               J := J2;
               return;
            end if;
            pragma Loop_Invariant
              (for all J3 in 1 .. J2 =>
                 not (A.H (K2, J3).Hdr.K = K_Grant and then A.H (K2, J3).Hdr.V.Author = W
                      and then A.H (K2, J3).Hdr.V.T = C));
         end loop;
         pragma Loop_Invariant
           (for all K3 in 1 .. K2 =>
              (for all J3 in 1 .. SC (A, K3) =>
                 not (A.H (K3, J3).Hdr.K = K_Grant and then A.H (K3, J3).Hdr.V.Author = W
                      and then A.H (K3, J3).Hdr.V.T = C)));
      end loop;
      pragma Assert (False);
      K := 1;
      J := 1;
   end Find_Grant_Cap;

   --  An authorization step on slot K0, on the rows:
   --    * no other slot changes;
   --    * slot K0 keeps some of its old records (Src) and ends in R, with
   --      the tag Tg;
   --    * an old record of slot K0 is kept (Dst) or dominated by R.
   function Auth_Step
     (Old, Upd : Auth_Rows; K0 : Slot_Index; R : Header; Tg : U64; Src, Dst : Index_Map)
      return Boolean
   is
     (Src'First = 1 and then Dst'First = 1
      and then Src'Last >= Slice_Max and then Dst'Last >= Slice_Max
      and then (for all K in Slot_Index =>
                  (if K /= K0 then
                     SC (Upd, K) = SC (Old, K)
                     and then (for all J in 1 .. SC (Old, K) => Upd.H (K, J) = Old.H (K, J))))
      and then SC (Upd, K0) >= 1
      and then Upd.H (K0, SC (Upd, K0)) = (Hdr => R, Tag => Tg)
      and then (for all J in 1 .. SC (Upd, K0) - 1 =>
                  Src (J) in 1 .. SC (Old, K0)
                  and then Upd.H (K0, J) = Old.H (K0, Src (J)))
      and then (for all J in 1 .. SC (Old, K0) =>
                  (if Dst (J) = 0 then Dominates (R, Old.H (K0, J).Hdr)
                   else Dst (J) in 1 .. SC (Upd, K0) - 1
                        and then Upd.H (K0, Dst (J)) = Old.H (K0, J))))
   with Ghost;

   procedure Lemma_Grant_Kept
     (Old, Upd : Auth_Rows; K0 : Slot_Index; R : Header; Tg : U64; Src, Dst : Index_Map; W : Key256)
   with
     Ghost, Global => null,
     Pre  => Grant_Of (Old, W) and then Auth_Step (Old, Upd, K0, R, Tg, Src, Dst),
     Post => Grant_Of (Upd, W)
   is
      K : Slot_Index;
      J : Positive;
   begin
      Find_Grant (Old, W, K, J);
      if K /= K0 then
         pragma Assert (SC (Upd, K) = SC (Old, K));
         pragma Assert (J <= SC (Upd, K));
         pragma Assert (Upd.H (K, J).Hdr = Old.H (K, J).Hdr);
         pragma Assert (Upd.H (K, J).Hdr.K = K_Grant and then Upd.H (K, J).Hdr.V.Author = W);
      elsif Dst (J) /= 0 then
         pragma Assert (Dst (J) <= SC (Upd, K0));
         pragma Assert (Upd.H (K0, Dst (J)).Hdr = Old.H (K0, J).Hdr);
         pragma Assert (Upd.H (K0, Dst (J)).Hdr.K = K_Grant
                        and then Upd.H (K0, Dst (J)).Hdr.V.Author = W);
      else
         Lemma_Dominator_Keeps_Registers (R, Old.H (K0, J).Hdr);
         pragma Assert (R.K = K_Grant and then R.V.Author = W);
         pragma Assert (Upd.H (K0, SC (Upd, K0)).Hdr = R);
         pragma Assert (Upd.H (K0, SC (Upd, K0)).Hdr.K = K_Grant
                        and then Upd.H (K0, SC (Upd, K0)).Hdr.V.Author = W);
      end if;
   end Lemma_Grant_Kept;

   --  A held grant of W with cap C is kept, unless R is a grant of W with a
   --  cap at least C (then R dominated it).
   procedure Lemma_Grant_Cap_Kept
     (Old, Upd : Auth_Rows; K0 : Slot_Index; R : Header; Tg : U64; Src, Dst : Index_Map;
      W : Key256; C : U48)
   with
     Ghost, Global => null,
     Pre  => Grant_Cap_Of (Old, W, C) and then Auth_Step (Old, Upd, K0, R, Tg, Src, Dst),
     Post => Grant_Cap_Of (Upd, W, C)
             or else (R.K = K_Grant and then R.V.Author = W and then Cap_Of (R) >= C)
   is
      K : Slot_Index;
      J : Positive;
   begin
      Find_Grant_Cap (Old, W, C, K, J);
      if K /= K0 then
         pragma Assert (SC (Upd, K) = SC (Old, K));
         pragma Assert (J <= SC (Upd, K));
         pragma Assert (Upd.H (K, J).Hdr = Old.H (K, J).Hdr);
         pragma Assert (Upd.H (K, J).Hdr.K = K_Grant and then Upd.H (K, J).Hdr.V.Author = W
                        and then Upd.H (K, J).Hdr.V.T = C);
      elsif Dst (J) /= 0 then
         pragma Assert (Dst (J) <= SC (Upd, K0));
         pragma Assert (Upd.H (K0, Dst (J)).Hdr = Old.H (K0, J).Hdr);
         pragma Assert (Upd.H (K0, Dst (J)).Hdr.K = K_Grant
                        and then Upd.H (K0, Dst (J)).Hdr.V.Author = W
                        and then Upd.H (K0, Dst (J)).Hdr.V.T = C);
      else
         Lemma_Dominator_Keeps_Registers (R, Old.H (K0, J).Hdr);
         pragma Assert (R.K = K_Grant and then R.V.Author = W and then Cap_Of (R) >= C);
      end if;
   end Lemma_Grant_Cap_Kept;

   procedure Lemma_Roster_Kept
     (Old, Upd : Auth_Rows; K0 : Slot_Index; R : Header; Tg : U64; Src, Dst : Index_Map; C : U48)
   with
     Ghost, Global => null,
     Pre  => Roster_At (Old, C) and then Auth_Step (Old, Upd, K0, R, Tg, Src, Dst)
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
         pragma Assert (Upd.H (K, J).Hdr = Old.H (K, J).Hdr);
         pragma Assert (Upd.H (K, J).Hdr.K = K_Roster and then Upd.H (K, J).Hdr.V.T = C);
      elsif Dst (J) /= 0 then
         pragma Assert (Dst (J) <= SC (Upd, K0));
         pragma Assert (Upd.H (K0, Dst (J)).Hdr = Old.H (K0, J).Hdr);
         pragma Assert (Upd.H (K0, Dst (J)).Hdr.K = K_Roster
                        and then Upd.H (K0, Dst (J)).Hdr.V.T = C);
      else
         Lemma_Dominator_Keeps_Registers (R, Old.H (K0, J).Hdr);
         pragma Assert (R.K = K_Roster and then R.V.T = C);
         pragma Assert (Upd.H (K0, SC (Upd, K0)).Hdr = R);
         pragma Assert (Upd.H (K0, SC (Upd, K0)).Hdr.K = K_Roster
                        and then Upd.H (K0, SC (Upd, K0)).Hdr.V.T = C);
      end if;
   end Lemma_Roster_Kept;

   --  Instances of the row predicates, each in a small context.
   procedure Lemma_Roster_At_Intro (A : Auth_Rows; C : U48; K : Slot_Index; J : Positive) with
     Ghost, Global => null,
     Pre  => J <= SC (A, K) and then A.H (K, J).Hdr.K = K_Roster and then A.H (K, J).Hdr.V.T = C,
     Post => Roster_At (A, C)
   is
   begin
      null;
   end Lemma_Roster_At_Intro;

   procedure Lemma_Grant_Of_Intro (A : Auth_Rows; W : Key256; K : Slot_Index; J : Positive) with
     Ghost, Global => null,
     Pre  => J <= SC (A, K) and then A.H (K, J).Hdr.K = K_Grant
             and then A.H (K, J).Hdr.V.Author = W,
     Post => Grant_Of (A, W)
   is
   begin
      null;
   end Lemma_Grant_Of_Intro;

   procedure Lemma_Grant_Cap_Of_Intro
     (A : Auth_Rows; W : Key256; C : U48; K : Slot_Index; J : Positive)
   with
     Ghost, Global => null,
     Pre  => J <= SC (A, K) and then A.H (K, J).Hdr.K = K_Grant
             and then A.H (K, J).Hdr.V.Author = W and then A.H (K, J).Hdr.V.T = C,
     Post => Grant_Cap_Of (A, W, C)
   is
   begin
      null;
   end Lemma_Grant_Cap_Of_Intro;

   procedure Lemma_Max_Ceil_At (A : Auth_Rows; K : Slot_Index; J : Positive) with
     Ghost, Global => null,
     Pre  => J <= SC (A, K),
     Post => Ceil_Of (A.H (K, J).Hdr) <= Max_Ceil_A (A)
   is
   begin
      Lemma_Max_Ceil_A (A);
   end Lemma_Max_Ceil_At;

   procedure Lemma_W_Cap_At (A : Auth_Rows; W : Key256; K : Slot_Index; J : Positive) with
     Ghost, Global => null,
     Pre  => J <= SC (A, K) and then A.H (K, J).Hdr.K = K_Grant
             and then A.H (K, J).Hdr.V.Author = W,
     Post => A.H (K, J).Hdr.V.T <= W_Cap_A (A, W)
   is
   begin
      Lemma_W_Cap_A (A, W);
   end Lemma_W_Cap_At;

   --  maxceil across an authorization step: the old maximum joined with
   --  R's ceiling (T4', Frontier.lean `maxCeil_F`).
   procedure Lemma_Ceil_Step
     (Old, Upd : Auth_Rows; K0 : Slot_Index; R : Header; Tg : U64; Src, Dst : Index_Map)
   with
     Ghost, Global => null,
     Pre  => Auth_Step (Old, Upd, K0, R, Tg, Src, Dst),
     Post => Max_Ceil_A (Upd) = U48'Max (Max_Ceil_A (Old), Ceil_Of (R))
   is
      N : constant Natural := SC (Upd, K0);
      C : constant U48 := U48'Max (Max_Ceil_A (Old), Ceil_Of (R));
   begin
      Lemma_Max_Ceil_A (Old);
      for K in Slot_Index loop
         for J in 1 .. SC (Upd, K) loop
            if K /= K0 then
               pragma Assert (SC (Upd, K) = SC (Old, K));
               pragma Assert (Upd.H (K, J) = Old.H (K, J));
               Lemma_Max_Ceil_At (Old, K, J);
            elsif J < N then
               pragma Assert (Src (J) in 1 .. SC (Old, K));
               pragma Assert (Upd.H (K, J) = Old.H (K, Src (J)));
               Lemma_Max_Ceil_At (Old, K, Src (J));
            else
               pragma Assert (Upd.H (K, J).Hdr = R);
            end if;
            pragma Assert (Ceil_Of (Upd.H (K, J).Hdr) <= C);
            pragma Loop_Invariant
              (for all J2 in 1 .. J => Ceil_Of (Upd.H (K, J2).Hdr) <= C);
         end loop;
         pragma Loop_Invariant
           (for all K2 in 1 .. K =>
              (for all J2 in 1 .. SC (Upd, K2) => Ceil_Of (Upd.H (K2, J2).Hdr) <= C));
      end loop;
      if C /= 0 then
         if R.K = K_Roster and then R.V.T = C then
            pragma Assert (Upd.H (K0, N).Hdr = R);
            Lemma_Roster_At_Intro (Upd, C, K0, N);
         else
            pragma Assert (C = Max_Ceil_A (Old));
            pragma Assert (Roster_At (Old, C));
            Lemma_Roster_Kept (Old, Upd, K0, R, Tg, Src, Dst, C);
         end if;
      end if;
      pragma Assert (Is_Max_Ceil (Upd, C));
      Lemma_Max_Ceil_Unique (Upd, C);
   end Lemma_Ceil_Step;

   --  W and wcap across an authorization step (T4', Frontier.lean
   --  `isWriter_F`, `wcap_F`).
   procedure Lemma_W_Step
     (Old, Upd : Auth_Rows; K0 : Slot_Index; R : Header; Tg : U64; Src, Dst : Index_Map;
      W : Key256)
   with
     Ghost, Global => null,
     Pre  => Auth_Step (Old, Upd, K0, R, Tg, Src, Dst),
     Post => In_W_A (Upd, W) = (In_W_A (Old, W) or else (R.K = K_Grant and then R.V.Author = W))
             and then W_Cap_A (Upd, W)
                      = (if R.K = K_Grant and then R.V.Author = W
                         then U48'Max (W_Cap_A (Old, W), R.V.T)
                         else W_Cap_A (Old, W))
   is
      N  : constant Natural := SC (Upd, K0);
      RW : constant Boolean := R.K = K_Grant and then R.V.Author = W;
      M  : constant U48 := W_Cap_A (Old, W);
      C  : constant U48 := (if RW then U48'Max (M, R.V.T) else M);
   begin
      Lemma_In_W_A (Old, W);
      Lemma_In_W_A (Upd, W);
      Lemma_W_Cap_A (Old, W);
      pragma Assert (Is_W_Cap (Old, W, M));
      --  W: each new grant of W is an old one or R; each old grant of W is
      --  kept or dominated by a grant of W (R).
      if Grant_Of (Upd, W) then
         declare
            K : Slot_Index;
            J : Positive;
         begin
            Find_Grant (Upd, W, K, J);
            if K /= K0 then
               pragma Assert (Upd.H (K, J) = Old.H (K, J));
               Lemma_Grant_Of_Intro (Old, W, K, J);
            elsif J < N then
               pragma Assert (Upd.H (K, J) = Old.H (K, Src (J)));
               Lemma_Grant_Of_Intro (Old, W, K, Src (J));
            else
               pragma Assert (RW);
            end if;
         end;
      end if;
      if Grant_Of (Old, W) then
         Lemma_Grant_Kept (Old, Upd, K0, R, Tg, Src, Dst, W);
      end if;
      if RW then
         pragma Assert (Upd.H (K0, N).Hdr = R);
         Lemma_Grant_Of_Intro (Upd, W, K0, N);
      end if;
      pragma Assert (Grant_Of (Upd, W) = (Grant_Of (Old, W) or else RW));

      --  wcap: C bounds every new grant of W ...
      for K in Slot_Index loop
         for J in 1 .. SC (Upd, K) loop
            if Upd.H (K, J).Hdr.K = K_Grant and then Upd.H (K, J).Hdr.V.Author = W then
               if K /= K0 then
                  pragma Assert (Upd.H (K, J) = Old.H (K, J));
                  Lemma_W_Cap_At (Old, W, K, J);
               elsif J < N then
                  pragma Assert (Upd.H (K, J) = Old.H (K, Src (J)));
                  Lemma_W_Cap_At (Old, W, K, Src (J));
               else
                  pragma Assert (Upd.H (K, J).Hdr = R);
               end if;
               pragma Assert (Upd.H (K, J).Hdr.V.T <= C);
            end if;
            pragma Loop_Invariant
              (for all J2 in 1 .. J =>
                 (if Upd.H (K, J2).Hdr.K = K_Grant and then Upd.H (K, J2).Hdr.V.Author = W
                  then Upd.H (K, J2).Hdr.V.T <= C));
         end loop;
         pragma Loop_Invariant
           (for all K2 in 1 .. K =>
              (for all J2 in 1 .. SC (Upd, K2) =>
                 (if Upd.H (K2, J2).Hdr.K = K_Grant and then Upd.H (K2, J2).Hdr.V.Author = W
                  then Upd.H (K2, J2).Hdr.V.T <= C)));
      end loop;
      --  ... and it is the cap of one of them, or 0.
      if Grant_Of (Upd, W) then
         if RW and then R.V.T = C then
            pragma Assert (Upd.H (K0, N).Hdr = R);
            Lemma_Grant_Cap_Of_Intro (Upd, W, C, K0, N);
         else
            pragma Assert (Grant_Of (Old, W));
            pragma Assert (C = M);
            pragma Assert (Grant_Cap_Of (Old, W, M));
            Lemma_Grant_Cap_Kept (Old, Upd, K0, R, Tg, Src, Dst, W, M);
            pragma Assert (Grant_Cap_Of (Upd, W, C));
         end if;
      else
         pragma Assert (not Grant_Of (Old, W) and then not RW);
         pragma Assert (C = 0);
      end if;
      pragma Assert (Is_W_Cap (Upd, W, C));
      Lemma_W_Cap_Unique (Upd, W, C);
   end Lemma_W_Step;

   --  The offsets of the flat view from the slot counts.
   function Offs_OK (NA : Slot_Counts; Offs : Slot_Offs; NAuth : Natural)
     return Boolean
   is
     (Offs (1) = 0
      and then (for all K in 2 .. Signers_Max => Offs (K) = Offs (K - 1) + NA (K - 1))
      and then (for all K in Slot_Index => Offs (K) <= (K - 1) * Slice_Max)
      and then NAuth = Offs (Signers_Max) + NA (Signers_Max));

   procedure Compute_Offs
     (NA    : Slot_Counts;
      Offs  : out Slot_Offs;
      NAuth : out Auth_Total)
   with
     Global => null,
     Post   => Offs_OK (NA, Offs, NAuth)
   is
   begin
      Offs := [others => 0];
      for K in 2 .. Signers_Max loop
         pragma Assert (Offs (K - 1) <= (K - 2) * Slice_Max);
         pragma Assert ((K - 2) * Slice_Max + Slice_Max = (K - 1) * Slice_Max);
         Offs (K) := Offs (K - 1) + NA (K - 1);
         pragma Loop_Invariant (Offs (1) = 0);
         pragma Loop_Invariant
           (for all K2 in 2 .. K => Offs (K2) = Offs (K2 - 1) + NA (K2 - 1));
         pragma Loop_Invariant
           (for all K2 in 1 .. K => Offs (K2) <= (K2 - 1) * Slice_Max);
      end loop;
      pragma Assert (Offs (Signers_Max) <= (Signers_Max - 1) * Slice_Max);
      NAuth := Offs (Signers_Max) + NA (Signers_Max);
   end Compute_Offs;

   --  Shape and slot table across an authorization step on slot K0 (Fresh:
   --  K0 is a slot that the step assigns now).
   procedure Lemma_Slots_Step
     (Old, Upd : Auth_Rows; Fnd : Key256; K0 : Slot_Index; Fresh : Boolean)
   with
     Ghost, Global => null,
     Pre  => Auth_Shape (Old) and then Slots_OK (Old, Fnd)
             and then (for all K in Slot_Index =>
                         (if K /= K0 then Upd.NA (K) = Old.NA (K)
                                          and then Upd.Keys (K) = Old.Keys (K)))
             and then Upd.NA (K0) >= 1
             and then (if Fresh then
                         Old.NSlots < Signers_Max and then K0 = Old.NSlots + 1
                         and then Upd.NSlots = K0
                         and then (for all K in 1 .. Old.NSlots => Old.Keys (K) /= Upd.Keys (K0))
                       else
                         K0 <= Old.NSlots and then Upd.NSlots = Old.NSlots
                         and then Upd.Keys (K0) = Old.Keys (K0))
             and then Offs_OK (Upd.NA, Upd.Offs, Upd.NAuth),
     Post => Auth_Shape (Upd) and then Slots_OK (Upd, Fnd)
   is
   begin
      pragma Assert (K0 >= 2 or else not Fresh);
      pragma Assert (Upd.Keys (1) = Fnd);
      pragma Assert (for all K in Slot_Index => (if K > Upd.NSlots then Upd.NA (K) = 0));
      pragma Assert (for all K in 2 .. Upd.NSlots => Upd.NA (K) >= 1);
      pragma Assert
        (for all K in 1 .. Upd.NSlots =>
           (for all K2 in 1 .. Upd.NSlots =>
              (if K /= K2 then Upd.Keys (K) /= Upd.Keys (K2))));
   end Lemma_Slots_Step;


   --  The data row is still a frontier row after an authorization step:
   --  the admission views only grow (T4').
   procedure Lemma_Data_OK_Auth
     (Old, Upd : State; K0 : Slot_Index; R : Header; Tg : U64; Src, Dst : Index_Map)
   with
     Ghost, Global => null,
     Pre  => Data_OK (Old) and then Data_Sorted (Old)
             and then Upd.Cap = Old.Cap and then Upd.ND = Old.ND
             and then (for all I in 1 .. Data_Count (Old) => Upd.Data_E (I) = Old.Data_E (I))
             and then Auth_Step (Old.A, Upd.A, K0, R, Tg, Src, Dst),
     Post => Data_OK (Upd) and then Data_Sorted (Upd)
   is
   begin
      pragma Assert (Data_Count (Upd) = Data_Count (Old));
      pragma Assert (Data_Sorted (Upd));
      Lemma_Ceil_Step (Old.A, Upd.A, K0, R, Tg, Src, Dst);
      for I in 1 .. Data_Count (Upd) loop
         pragma Assert (Data_Item_OK (Old, Old.Data_E (I).Hdr));
         Lemma_W_Step (Old.A, Upd.A, K0, R, Tg, Src, Dst, Upd.Data_E (I).Hdr.V.Author);
         pragma Assert (Data_Item_OK (Upd, Upd.Data_E (I).Hdr));
         pragma Loop_Invariant
           (for all I2 in 1 .. I => Data_Item_OK (Upd, Upd.Data_E (I2).Hdr));
      end loop;
   end Lemma_Data_OK_Auth;

   --  Auth_OK across an authorization step: R is a canonical record of the
   --  slot's issuer, undominated in its row and not already in it. The
   --  kept records are distinct old records that R does not dominate.
   procedure Lemma_Auth_OK_Step
     (Old, Upd : Auth_Rows; K0 : Slot_Index; R : Header; Tg : U64; Src, Dst : Index_Map)
   with
     Ghost, Global => null,
     Pre  => Auth_OK (Old)
             and then Auth_Step (Old, Upd, K0, R, Tg, Src, Dst)
             and then (for all K in Slot_Index =>
                         (if K /= K0 then Upd.Keys (K) = Old.Keys (K)))
             and then Upd.Keys (K0) = R.Issuer
             and then (if SC (Old, K0) > 0 then Old.Keys (K0) = R.Issuer)
             and then Is_Auth (R) and then Canonical (R)
             and then (for all J in 1 .. SC (Old, K0) =>
                         Old.H (K0, J).Hdr /= R and then not Dominates (Old.H (K0, J).Hdr, R))
             and then (for all J in 1 .. SC (Upd, K0) - 1 =>
                         not Dominates (R, Old.H (K0, Src (J)).Hdr))
             and then (for all J in 1 .. SC (Upd, K0) - 1 =>
                         (for all J2 in 1 .. SC (Upd, K0) - 1 =>
                            (if J /= J2 then Src (J) /= Src (J2)))),
     Post => Auth_OK (Upd)
   is
      N : constant Natural := SC (Upd, K0);
   begin
      Lemma_Dominates_Irrefl (R);
      for J in 1 .. N loop
         if J < N then
            pragma Assert (Src (J) in 1 .. SC (Old, K0));
            pragma Assert (Upd.H (K0, J).Hdr = Old.H (K0, Src (J)).Hdr);
            pragma Assert (Is_Auth (Old.H (K0, Src (J)).Hdr)
                           and then Canonical (Old.H (K0, Src (J)).Hdr)
                           and then Old.H (K0, Src (J)).Hdr.Issuer = Old.Keys (K0));
            pragma Assert (Old.Keys (K0) = R.Issuer);
         else
            pragma Assert (Upd.H (K0, J).Hdr = R);
         end if;
         pragma Loop_Invariant
           (for all J2 in 1 .. J =>
              Is_Auth (Upd.H (K0, J2).Hdr) and then Canonical (Upd.H (K0, J2).Hdr)
              and then Upd.H (K0, J2).Hdr.Issuer = Upd.Keys (K0));
      end loop;
      pragma Assert
        (for all J in 1 .. N =>
           (if J < N then Upd.H (K0, J).Hdr = Old.H (K0, Src (J)).Hdr
            else Upd.H (K0, J).Hdr = R));
      pragma Assert
        (for all J in 1 .. N =>
           Is_Auth (Upd.H (K0, J).Hdr) and then Canonical (Upd.H (K0, J).Hdr)
           and then Upd.H (K0, J).Hdr.Issuer = Upd.Keys (K0));
      pragma Assert
        (for all J in 1 .. N =>
           (for all J2 in 1 .. N => not Dominates (Upd.H (K0, J2).Hdr, Upd.H (K0, J).Hdr)));
      pragma Assert
        (for all J in 1 .. N =>
           (for all J2 in 1 .. N =>
              (if J /= J2 then Upd.H (K0, J).Hdr /= Upd.H (K0, J2).Hdr)));
      for K in Slot_Index loop
         if K /= K0 then
            pragma Assert (SC (Upd, K) = SC (Old, K) and then Upd.Keys (K) = Old.Keys (K));
            pragma Assert
              (for all J in 1 .. SC (Upd, K) => Upd.H (K, J) = Old.H (K, J));
            pragma Assert
              (for all J in 1 .. SC (Old, K) =>
                 Is_Auth (Old.H (K, J).Hdr) and then Canonical (Old.H (K, J).Hdr)
                 and then Old.H (K, J).Hdr.Issuer = Old.Keys (K));
            pragma Assert
              (for all J in 1 .. SC (Old, K) =>
                 (for all J2 in 1 .. SC (Old, K) =>
                    not Dominates (Old.H (K, J2).Hdr, Old.H (K, J).Hdr)));
            pragma Assert
              (for all J in 1 .. SC (Old, K) =>
                 (for all J2 in 1 .. SC (Old, K) =>
                    (if J /= J2 then Old.H (K, J).Hdr /= Old.H (K, J2).Hdr)));
         end if;
         pragma Loop_Invariant
           (for all K2 in 1 .. K =>
              (if K2 /= K0 then
                 (for all J in 1 .. SC (Upd, K2) =>
                    Is_Auth (Upd.H (K2, J).Hdr) and then Canonical (Upd.H (K2, J).Hdr)
                    and then Upd.H (K2, J).Hdr.Issuer = Upd.Keys (K2))));
         pragma Loop_Invariant
           (for all K2 in 1 .. K =>
              (if K2 /= K0 then
                 (for all J in 1 .. SC (Upd, K2) =>
                    (for all J2 in 1 .. SC (Upd, K2) =>
                       not Dominates (Upd.H (K2, J2).Hdr, Upd.H (K2, J).Hdr)))));
         pragma Loop_Invariant
           (for all K2 in 1 .. K =>
              (if K2 /= K0 then
                 (for all J in 1 .. SC (Upd, K2) =>
                    (for all J2 in 1 .. SC (Upd, K2) =>
                       (if J /= J2 then Upd.H (K2, J).Hdr /= Upd.H (K2, J2).Hdr)))));
      end loop;
   end Lemma_Auth_OK_Step;

   ---------------------------------------------------------------------
   --  Public accessors and lemmas
   ---------------------------------------------------------------------

   function Empty (Founding : Key256; Cap : Data_Size) return State is
     (Cap => Cap, Fnd => Founding,
      Data_E => [others => Null_Entry], ND => 0,
      A => (H      => [others => [others => Null_Entry]],
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
   begin
      Lemma_Off_Mono (S);
      Lemma_Flat_Row (S, I);
      Lemma_Item (S, Row_Of (S, I), Pos_Of (S, I));
      Lemma_Distinct_Held (S, I);
   end Lemma_Frontier_Held;

   procedure Lemma_Tag_Of (S : State; I : Held_Index) is
   begin
      Lemma_Tag_Of_P (S, I);
   end Lemma_Tag_Of;

   procedure Lemma_Has_Tag_Def (S : State; X : Header; T : U64) is null;

   procedure Lemma_Has_Tag_Of (S : State; X : Header; T : U64) is
   begin
      for J in 1 .. Count (S) loop
         if Held (S, J) = X and then Tag (S, J) = T then
            Lemma_Tag_Of_P (S, J);
            return;
         end if;
         pragma Loop_Invariant
           (for all J2 in 1 .. J => not (Held (S, J2) = X and then Tag (S, J2) = T));
      end loop;
   end Lemma_Has_Tag_Of;

   --  A held record of the flat view with a property: the witness of an
   --  existential in a _Def lemma, as an index.
   function Find_Flat_Roster (S : State; C : U48) return Held_Index with
     Ghost, Global => null,
     Pre  => (for some I in 1 .. Count (S) =>
                Held (S, I).K = K_Roster and then Held (S, I).V.T = C),
     Post => Find_Flat_Roster'Result <= Count (S)
             and then Held (S, Find_Flat_Roster'Result).K = K_Roster
             and then Held (S, Find_Flat_Roster'Result).V.T = C
   is
   begin
      for I in 1 .. Count (S) loop
         if Held (S, I).K = K_Roster and then Held (S, I).V.T = C then
            return I;
         end if;
         pragma Loop_Invariant
           (for all I2 in 1 .. I => not (Held (S, I2).K = K_Roster and then Held (S, I2).V.T = C));
      end loop;
      pragma Assert (False);
      return 1;
   end Find_Flat_Roster;

   function Find_Flat_Grant (S : State; W : Key256) return Held_Index with
     Ghost, Global => null,
     Pre  => (for some I in 1 .. Count (S) =>
                Held (S, I).K = K_Grant and then Held (S, I).V.Author = W),
     Post => Find_Flat_Grant'Result <= Count (S)
             and then Held (S, Find_Flat_Grant'Result).K = K_Grant
             and then Held (S, Find_Flat_Grant'Result).V.Author = W
   is
   begin
      for I in 1 .. Count (S) loop
         if Held (S, I).K = K_Grant and then Held (S, I).V.Author = W then
            return I;
         end if;
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              not (Held (S, I2).K = K_Grant and then Held (S, I2).V.Author = W));
      end loop;
      pragma Assert (False);
      return 1;
   end Find_Flat_Grant;

   function Find_Flat_Grant_Cap (S : State; W : Key256; C : U48) return Held_Index with
     Ghost, Global => null,
     Pre  => (for some I in 1 .. Count (S) =>
                Held (S, I).K = K_Grant and then Held (S, I).V.Author = W
                and then Held (S, I).V.T = C),
     Post => Find_Flat_Grant_Cap'Result <= Count (S)
             and then Held (S, Find_Flat_Grant_Cap'Result).K = K_Grant
             and then Held (S, Find_Flat_Grant_Cap'Result).V.Author = W
             and then Held (S, Find_Flat_Grant_Cap'Result).V.T = C
   is
   begin
      for I in 1 .. Count (S) loop
         if Held (S, I).K = K_Grant and then Held (S, I).V.Author = W
           and then Held (S, I).V.T = C
         then
            return I;
         end if;
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              not (Held (S, I2).K = K_Grant and then Held (S, I2).V.Author = W
                   and then Held (S, I2).V.T = C));
      end loop;
      pragma Assert (False);
      return 1;
   end Find_Flat_Grant_Cap;

   procedure Lemma_Max_Ceil_Def (S : State) is
      M : constant U48 := Max_Ceil (S);
   begin
      Lemma_Max_Ceil_A (S.A);
      Lemma_Off_Mono (S);
      pragma Assert (Is_Max_Ceil (S.A, M));
      for I in 1 .. Count (S) loop
         Lemma_Flat_Row (S, I);
         Lemma_Item (S, Row_Of (S, I), Pos_Of (S, I));
         if Row_Of (S, I) /= 0 then
            pragma Assert (Held (S, I) = S.A.H (Row_Of (S, I), Pos_Of (S, I)).Hdr);
         end if;
         pragma Assert (Ceil_Of (Held (S, I)) <= M);
         pragma Loop_Invariant (for all I2 in 1 .. I => Ceil_Of (Held (S, I2)) <= M);
      end loop;
      if M /= 0 then
         declare
            K : Slot_Index;
            J : Positive;
         begin
            Find_Roster (S.A, M, K, J);
            Lemma_Row_Flat (S, K, J);
            pragma Assert (Held (S, Flat_Index (S, K, J)) = S.A.H (K, J).Hdr);
         end;
      end if;
   end Lemma_Max_Ceil_Def;

   procedure Lemma_In_W_Def (S : State; K : Key256) is
   begin
      Lemma_In_W_A (S.A, K);
      Lemma_Off_Mono (S);
      if Grant_Of (S.A, K) then
         declare
            K2 : Slot_Index;
            J  : Positive;
         begin
            Find_Grant (S.A, K, K2, J);
            Lemma_Row_Flat (S, K2, J);
            pragma Assert (Held (S, Flat_Index (S, K2, J)) = S.A.H (K2, J).Hdr);
         end;
      end if;
      for I in 1 .. Count (S) loop
         Lemma_Flat_Row (S, I);
         Lemma_Item (S, Row_Of (S, I), Pos_Of (S, I));
         if Held (S, I).K = K_Grant and then Held (S, I).V.Author = K then
            pragma Assert (Row_Of (S, I) /= 0);
            pragma Assert (Held (S, I) = S.A.H (Row_Of (S, I), Pos_Of (S, I)).Hdr);
            pragma Assert (Grant_Of (S.A, K));
         end if;
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              (if Held (S, I2).K = K_Grant and then Held (S, I2).V.Author = K
               then Grant_Of (S.A, K)));
      end loop;
   end Lemma_In_W_Def;

   procedure Lemma_W_Cap_Def (S : State; K : Key256) is
      M : constant U48 := W_Cap (S, K);
   begin
      Lemma_In_W_A (S.A, K);
      Lemma_W_Cap_A (S.A, K);
      Lemma_Off_Mono (S);
      pragma Assert (Is_W_Cap (S.A, K, M));
      for I in 1 .. Count (S) loop
         Lemma_Flat_Row (S, I);
         Lemma_Item (S, Row_Of (S, I), Pos_Of (S, I));
         if Held (S, I).K = K_Grant and then Held (S, I).V.Author = K then
            pragma Assert (Row_Of (S, I) /= 0);
            pragma Assert (Held (S, I) = S.A.H (Row_Of (S, I), Pos_Of (S, I)).Hdr);
         end if;
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              (if Held (S, I2).K = K_Grant and then Held (S, I2).V.Author = K
               then Held (S, I2).V.T <= M));
      end loop;
      if Grant_Of (S.A, K) then
         declare
            K2 : Slot_Index;
            J  : Positive;
         begin
            Find_Grant_Cap (S.A, K, M, K2, J);
            Lemma_Row_Flat (S, K2, J);
            pragma Assert (Held (S, Flat_Index (S, K2, J)) = S.A.H (K2, J).Hdr);
         end;
      end if;
   end Lemma_W_Cap_Def;

   procedure Lemma_Views_Step (Before, After : State; R : Header; K : Key256) is
      IR : constant Held_Count := Find_Held (After, R);
      RW : constant Boolean := R.K = K_Grant and then R.V.Author = K;
   begin
      Lemma_Max_Ceil_Def (Before);
      Lemma_Max_Ceil_Def (After);
      Lemma_In_W_Def (Before, K);
      Lemma_In_W_Def (After, K);
      Lemma_W_Cap_Def (Before, K);
      Lemma_W_Cap_Def (After, K);
      pragma Assert (IR /= 0);

      --  maxceil.
      pragma Assert (Ceil_Of (R) <= Max_Ceil (After));
      if Max_Ceil (Before) /= 0 then
         declare
            I : constant Held_Index := Find_Flat_Roster (Before, Max_Ceil (Before));
         begin
            if Holds (After, Held (Before, I)) then
               pragma Assert (Find_Held (After, Held (Before, I)) /= 0);
               pragma Assert (Max_Ceil (Before) <= Max_Ceil (After));
            else
               Lemma_Dominator_Keeps_Registers (R, Held (Before, I));
               pragma Assert (Max_Ceil (Before) <= Ceil_Of (R));
            end if;
         end;
      end if;
      if Max_Ceil (After) /= 0 then
         declare
            I : constant Held_Index := Find_Flat_Roster (After, Max_Ceil (After));
         begin
            if Held (After, I) /= R then
               pragma Assert (Find_Held (Before, Held (After, I)) /= 0);
               pragma Assert (Max_Ceil (After) <= Max_Ceil (Before));
            end if;
         end;
      end if;
      pragma Assert (Max_Ceil (After) = U48'Max (Max_Ceil (Before), Ceil_Of (R)));

      --  W.
      if In_W (After, K) then
         declare
            I : constant Held_Index := Find_Flat_Grant (After, K);
         begin
            if Held (After, I) /= R then
               pragma Assert (Find_Held (Before, Held (After, I)) /= 0);
               pragma Assert (In_W (Before, K));
            end if;
         end;
      end if;
      if In_W (Before, K) then
         declare
            I : constant Held_Index := Find_Flat_Grant (Before, K);
         begin
            if Holds (After, Held (Before, I)) then
               pragma Assert (Find_Held (After, Held (Before, I)) /= 0);
            else
               Lemma_Dominator_Keeps_Registers (R, Held (Before, I));
               pragma Assert (RW);
            end if;
         end;
      end if;
      pragma Assert (if RW then In_W (After, K));
      pragma Assert (In_W (After, K) = (In_W (Before, K) or else RW));

      --  wcap: an upper bound ...
      if In_W (After, K) then
         declare
            I : constant Held_Index := Find_Flat_Grant_Cap (After, K, W_Cap (After, K));
         begin
            if Held (After, I) /= R then
               pragma Assert (Find_Held (Before, Held (After, I)) /= 0);
               pragma Assert (W_Cap (After, K) <= W_Cap (Before, K));
            end if;
         end;
      end if;
      --  ... and a lower bound.
      if In_W (Before, K) then
         declare
            I : constant Held_Index := Find_Flat_Grant_Cap (Before, K, W_Cap (Before, K));
         begin
            if Holds (After, Held (Before, I)) then
               pragma Assert (Find_Held (After, Held (Before, I)) /= 0);
               pragma Assert (W_Cap (Before, K) <= W_Cap (After, K));
            else
               Lemma_Dominator_Keeps_Registers (R, Held (Before, I));
               pragma Assert (W_Cap (Before, K) <= R.V.T);
            end if;
         end;
      end if;
      pragma Assert (if RW then R.V.T <= W_Cap (After, K));
   end Lemma_Views_Step;

   procedure Lemma_Same_Auth_Views (S1, S2 : State; K : Key256) is
   begin
      for K2 in Slot_Index loop
         pragma Assert (Slot_Count (S1, K2) = Slot_Count (S2, K2));
         pragma Assert (S1.A.NA (K2) = S2.A.NA (K2));
         if K2 <= S1.A.NSlots then
            for J in 1 .. SC (S1.A, K2) loop
               pragma Assert (Auth_Held (S1, K2, J) = Auth_Held (S2, K2, J));
               pragma Assert (S1.A.H (K2, J).Hdr = S2.A.H (K2, J).Hdr);
               pragma Loop_Invariant
                 (for all J2 in 1 .. J => S1.A.H (K2, J2).Hdr = S2.A.H (K2, J2).Hdr);
            end loop;
         else
            pragma Assert (SC (S1.A, K2) = 0);
         end if;
         pragma Loop_Invariant (for all K3 in 1 .. K2 => S1.A.NA (K3) = S2.A.NA (K3));
         pragma Loop_Invariant
           (for all K3 in 1 .. K2 =>
              (for all J in 1 .. SC (S1.A, K3) => S1.A.H (K3, J).Hdr = S2.A.H (K3, J).Hdr));
      end loop;
      pragma Assert (Rows_Agree (S1.A, S2.A));
      Lemma_Rows_Agree_Views (S1.A, S2.A, K);
   end Lemma_Same_Auth_Views;

   procedure Lemma_Drops_Any (S : State; R : Header) is null;

   procedure Lemma_Unchanged_Refl (S : State) is null;

   procedure Lemma_Unchanged (Old, Upd : State) is
   begin
      pragma Assert (Rows_Agree (Old.A, Upd.A));
      Lemma_Rows_Agree_Views (Old.A, Upd.A, Zero_Key);
      pragma Assert (Data_Count (Upd) = Data_Count (Old));
      pragma Assert (for all K in Slot_Index => Slot_Count (Upd, K) = Slot_Count (Old, K));
      pragma Assert (for all K in Slot_Number => Row_Count (Upd, K) = Row_Count (Old, K));
      pragma Assert
        (for all J in 1 .. Data_Count (Old) => Row_Ent (Upd, 0, J) = Row_Ent (Old, 0, J));
      pragma Assert
        (for all K in Slot_Index =>
           (for all J in 1 .. Slot_Count (Old, K) => Upd.A.H (K, J) = Old.A.H (K, J)));
      pragma Assert (for all K in Slot_Index => SC (Upd.A, K) = SC (Old.A, K));
      for K in Slot_Index loop
         --  One slot at a time: the outer quantifier, instantiated at K.
         pragma Assert
           (for all J2 in 1 .. Slot_Count (Old, K) => Upd.A.H (K, J2) = Old.A.H (K, J2));
         pragma Assert (Row_Count (Old, K) = Slot_Count (Old, K));
         for J in 1 .. Row_Count (Old, K) loop
            pragma Assert (J <= SC (Old.A, K) and then J <= SC (Upd.A, K));
            pragma Assert (Upd.A.H (K, J) = Old.A.H (K, J));
            pragma Assert (Row_Ent (Upd, K, J) = Upd.A.H (K, J));
            pragma Assert (Row_Ent (Old, K, J) = Old.A.H (K, J));
            pragma Loop_Invariant
              (for all J2 in 1 .. J => Row_Ent (Upd, K, J2) = Row_Ent (Old, K, J2));
         end loop;
         pragma Loop_Invariant
           (for all K2 in 1 .. K =>
              (for all J in 1 .. Row_Count (Old, K2) => Row_Ent (Upd, K2, J) = Row_Ent (Old, K2, J)));
      end loop;
      pragma Assert
        (for all K in Slot_Index =>
           (for all J in 1 .. Row_Count (Old, K) => Row_Ent (Upd, K, J) = Row_Ent (Old, K, J)));
      pragma Assert
        (for all K in Slot_Number =>
           (for all J in 1 .. Row_Count (Old, K) => Row_Ent (Upd, K, J) = Row_Ent (Old, K, J)));
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
            --  In the row, the two rows agree (above). Outside it, the two
            --  are Null_Entry.
            if J not in 1 .. Row_Count (Old, K) then
               pragma Assert (Row_Ent (Old, K, J) = Null_Entry);
               pragma Assert (Row_Ent (Upd, K, J) = Null_Entry);
            end if;
            pragma Assert (Row_Ent (Upd, K, J) = Row_Ent (Old, K, J));
         end;
         pragma Assert (Flat_Ent (Upd, I) = Flat_Ent (Old, I));
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              Held (Upd, I2) = Held (Old, I2) and then Tag (Upd, I2) = Tag (Old, I2));
      end loop;
   end Lemma_Unchanged;

   ---------------------------------------------------------------------
   --  The sorted data row (AUDIT.md G25)
   --
   --  The data row is sorted by Key_Lt (entity-major). Obligation (G25):
   --  every dominator of a data record P lies in P's entity run, and so
   --  does every record that P dominates (Lemma_Dominator_In_Run: the
   --  dominator has P's entity, and its key is not above P's key). So
   --  one binary search (Find_Run) gives the run of R's entity, and the
   --  duplicate, domination and drop tests of Apply read only that run:
   --  O(log |F| + fields of the entity) Dominates calls in place of
   --  O(|F|). A record outside the run differs from R in its entity, so
   --  it neither equals, dominates nor is dominated by R
   --  (Lemma_Outside_Run).
   ---------------------------------------------------------------------

   procedure Lemma_Key_Lt_Trans (A, B, C : Header) with
     Ghost, Global => null,
     Pre  => Key_Lt (A, B) and then Key_Lt (B, C),
     Post => Key_Lt (A, C)
   is
   begin
      null;
   end Lemma_Key_Lt_Trans;

   procedure Lemma_Key_Not_Below (A, B, R : Header) with
     Ghost, Global => null,
     Pre  => Key_Lt (A, B) and then not Key_Lt (A, R),
     Post => not Key_Lt (B, R)
   is
   begin
      if Key_Lt (B, R) then
         Lemma_Key_Lt_Trans (A, B, R);
      end if;
   end Lemma_Key_Not_Below;

   --  The G25 obligation: a dominator Q of a data record P is a data
   --  record of P's entity, and its key is not above P's key (a newer PUT
   --  of the cell has P's key; a DEL of the entity sorts before P).
   procedure Lemma_Dominator_In_Run (Q, P : Header) with
     Ghost, Global => null,
     Pre  => Dominates (Q, P) and then Is_Data (P)
             and then Canonical (P) and then Canonical (Q),
     Post => Is_Data (Q) and then Q.Ent = P.Ent and then not Key_Lt (P, Q)
   is
   begin
      null;
   end Lemma_Dominator_In_Run;

   --  On a frontier the key is unique: two distinct data records of one
   --  ns with one key are ordered by V, so one dominates the other.
   procedure Lemma_Key_Total (X, Y : Header) with
     Ghost, Global => null,
     Pre  => Is_Data (X) and then Is_Data (Y)
             and then Canonical (X) and then Canonical (Y)
             and then X /= Y
             and then not Dominates (X, Y) and then not Dominates (Y, X),
     Post => Key_Lt (X, Y) or else Key_Lt (Y, X)
   is
   begin
      Kome.Versions.Lemma_Trichotomy (X.V, Y.V);
      if not Key_Lt (X, Y) and then not Key_Lt (Y, X) then
         pragma Assert (X.Ent = Y.Ent and then X.K = Y.K and then X.FH = Y.FH);
         pragma Assert (not Kome.Versions."=" (X.V, Y.V));
         pragma Assert (Kome.Versions.Lt (X.V, Y.V) or else Kome.Versions.Lt (Y.V, X.V));
         pragma Assert (False);
      end if;
   end Lemma_Key_Total;

   --  A sorted row is monotone in the entity.
   procedure Lemma_Ent_Mono (H : Entry_Array; N : Natural; I, J : Positive) with
     Ghost, Global => null, Always_Terminates,
     Pre  => Sorted_Row (H, N) and then I < J and then J <= N,
     Post => Ent_Lt (H (I).Hdr.Ent, H (J).Hdr.Ent) or else H (I).Hdr.Ent = H (J).Hdr.Ent
   is
   begin
      pragma Assert (Key_Lt (H (I).Hdr, H (J).Hdr));
   end Lemma_Ent_Mono;

   procedure Lemma_Ent_Below (H : Entry_Array; N : Natural; L, M : Positive; E : Id128) with
     Ghost, Global => null, Always_Terminates,
     Pre  => Sorted_Row (H, N) and then L <= M and then M <= N
             and then Ent_Lt (H (M).Hdr.Ent, E),
     Post => (for all I in L .. M => Ent_Lt (H (I).Hdr.Ent, E))
   is
   begin
      for I in L .. M - 1 loop
         Lemma_Ent_Mono (H, N, I, M);
         pragma Loop_Invariant (for all I2 in L .. I => Ent_Lt (H (I2).Hdr.Ent, E));
      end loop;
   end Lemma_Ent_Below;

   procedure Lemma_Ent_Above (H : Entry_Array; N : Natural; M, U : Positive; E : Id128) with
     Ghost, Global => null, Always_Terminates,
     Pre  => Sorted_Row (H, N) and then M < U and then U <= N + 1
             and then not Ent_Lt (H (M).Hdr.Ent, E),
     Post => (for all I in M .. U - 1 => not Ent_Lt (H (I).Hdr.Ent, E))
   is
   begin
      for I in M + 1 .. U - 1 loop
         Lemma_Ent_Mono (H, N, M, I);
         pragma Loop_Invariant (for all I2 in M .. I => not Ent_Lt (H (I2).Hdr.Ent, E));
      end loop;
   end Lemma_Ent_Above;

   procedure Lemma_Ent_After (H : Entry_Array; N : Natural; Lo, Hi : Positive; E : Id128) with
     Ghost, Global => null, Always_Terminates,
     Pre  => Sorted_Row (H, N) and then Lo <= Hi and then Hi <= N + 1
             and then (for all I in Lo .. N => not Ent_Lt (H (I).Hdr.Ent, E))
             and then (if Hi <= N then H (Hi).Hdr.Ent /= E),
     Post => (for all I in Hi .. N => Ent_Lt (E, H (I).Hdr.Ent))
   is
   begin
      if Hi <= N then
         pragma Assert (not Ent_Lt (H (Hi).Hdr.Ent, E));
         pragma Assert (Ent_Lt (E, H (Hi).Hdr.Ent));
         for I in Hi + 1 .. N loop
            Lemma_Ent_Mono (H, N, Hi, I);
            pragma Loop_Invariant (for all I2 in Hi .. I => Ent_Lt (E, H (I2).Hdr.Ent));
         end loop;
      end if;
   end Lemma_Ent_After;

   --  The run of entity E: Lo .. Hi - 1. One binary search finds Lo, the
   --  first record whose entity is not below E (the entity's DEL, if it
   --  is held, is there); a scan of the run finds Hi.
   procedure Find_Run (H : Entry_Array; N : Natural; E : Id128; Lo, Hi : out Positive) with
     Global => null, Always_Terminates,
     Pre  => Sorted_Row (H, N) and then N < Held_Max,
     Post => Lo <= Hi and then Hi <= N + 1
             and then (for all I in 1 .. Lo - 1 => Ent_Lt (H (I).Hdr.Ent, E))
             and then (for all I in Lo .. Hi - 1 => H (I).Hdr.Ent = E)
             and then (for all I in Hi .. N => Ent_Lt (E, H (I).Hdr.Ent))
   is
      L : Positive := 1;
      U : Positive := N + 1;
      M : Positive;
   begin
      while L < U loop
         pragma Loop_Invariant (L <= U and then U <= N + 1);
         pragma Loop_Invariant (for all I in 1 .. L - 1 => Ent_Lt (H (I).Hdr.Ent, E));
         pragma Loop_Invariant (for all I in U .. N => not Ent_Lt (H (I).Hdr.Ent, E));
         pragma Loop_Variant (Decreases => U - L);
         M := L + (U - L) / 2;
         if Ent_Lt (H (M).Hdr.Ent, E) then
            Lemma_Ent_Below (H, N, L, M, E);
            L := M + 1;
         else
            Lemma_Ent_Above (H, N, M, U, E);
            U := M;
         end if;
      end loop;
      pragma Assert (L = U);
      Lo := L;
      Hi := L;
      while Hi <= N and then H (Hi).Hdr.Ent = E loop
         pragma Loop_Invariant (Lo <= Hi and then Hi <= N);
         pragma Loop_Invariant (for all I in Lo .. Hi - 1 => H (I).Hdr.Ent = E);
         pragma Loop_Variant (Increases => Hi);
         Hi := Hi + 1;
      end loop;
      Lemma_Ent_After (H, N, Lo, Hi, E);
   end Find_Run;

   --  The run of E as a range: Find_Run, as a function.
   function Run_Of (H : Entry_Array; N : Natural; E : Id128) return Index_Range with
     Global => null,
     Pre    => Sorted_Row (H, N) and then N < Held_Max,
     Post   => Run_Of'Result.First <= Run_Of'Result.Last + 1
               and then Run_Of'Result.Last <= N
               and then (for all I in 1 .. Run_Of'Result.First - 1 => Ent_Lt (H (I).Hdr.Ent, E))
               and then (for all I in Run_Of'Result.First .. Run_Of'Result.Last =>
                           H (I).Hdr.Ent = E)
               and then (for all I in Run_Of'Result.Last + 1 .. N => Ent_Lt (E, H (I).Hdr.Ent))
   is
      Lo, Hi : Positive;
   begin
      Find_Run (H, N, E, Lo, Hi);
      return (First => Lo, Last => Hi - 1);
   end Run_Of;

   --  The three conditions of Run_Of decide the run.
   procedure Lemma_Run_Unique (H : Entry_Array; N : Natural; E : Id128; Lo, Hi : Positive) with
     Ghost, Global => null,
     Pre  => Sorted_Row (H, N) and then N < Held_Max
             and then Lo <= Hi and then Hi <= N + 1
             and then (for all I in 1 .. Lo - 1 => Ent_Lt (H (I).Hdr.Ent, E))
             and then (for all I in Lo .. Hi - 1 => H (I).Hdr.Ent = E)
             and then (for all I in Hi .. N => Ent_Lt (E, H (I).Hdr.Ent)),
     Post => Run_Of (H, N, E) = (First => Lo, Last => Hi - 1)
   is
      R : constant Index_Range := Run_Of (H, N, E);
   begin
      pragma Assert (not Ent_Lt (E, E));
      pragma Assert (for all I in 1 .. N => not (Ent_Lt (H (I).Hdr.Ent, E)
                                                 and then Ent_Lt (E, H (I).Hdr.Ent)));
      if R.First < Lo then
         pragma Assert (Ent_Lt (H (R.First).Hdr.Ent, E));
         pragma Assert (False);
      elsif R.First > Lo then
         pragma Assert (Lo <= N);
         pragma Assert (Ent_Lt (H (Lo).Hdr.Ent, E));
         pragma Assert (False);
      end if;
      if R.Last + 1 < Hi then
         pragma Assert (Ent_Lt (E, H (R.Last + 1).Hdr.Ent));
         pragma Assert (False);
      elsif R.Last + 1 > Hi then
         pragma Assert (Ent_Lt (E, H (Hi).Hdr.Ent));
         pragma Assert (False);
      end if;
   end Lemma_Run_Unique;

   procedure Lemma_Key_After (H : Entry_Array; N : Natural; R : Header; P, Hi : Positive) with
     Ghost, Global => null,
     Pre  => Sorted_Row (H, N) and then P <= Hi and then Hi <= N + 1
             and then (if P < Hi then not Key_Lt (H (P).Hdr, R))
             and then (for all I in Hi .. N => Ent_Lt (R.Ent, H (I).Hdr.Ent)),
     Post => (for all I in P .. N => not Key_Lt (H (I).Hdr, R))
   is
   begin
      for I in P .. N loop
         if I < Hi and then I > P then
            pragma Assert (Key_Lt (H (P).Hdr, H (I).Hdr));
            Lemma_Key_Not_Below (H (P).Hdr, H (I).Hdr, R);
         end if;
         pragma Loop_Invariant (for all I2 in P .. I => not Key_Lt (H (I2).Hdr, R));
      end loop;
   end Lemma_Key_After;

   --  R's place in the run of its entity: the records before P have a key
   --  below R's, the others do not.
   procedure Find_Pos
     (H : Entry_Array; N : Natural; R : Header; Lo, Hi : Positive; P : out Positive)
   with
     Global => null,
     Pre  => Sorted_Row (H, N) and then Lo <= Hi and then Hi <= N + 1
             and then (for all I in 1 .. Lo - 1 => Ent_Lt (H (I).Hdr.Ent, R.Ent))
             and then (for all I in Lo .. Hi - 1 => H (I).Hdr.Ent = R.Ent)
             and then (for all I in Hi .. N => Ent_Lt (R.Ent, H (I).Hdr.Ent)),
     Post => P in Lo .. Hi
             and then (for all I in 1 .. N =>
                         (if I < P then Key_Lt (H (I).Hdr, R) else not Key_Lt (H (I).Hdr, R)))
   is
   begin
      P := Lo;
      while P < Hi and then Key_Lt (H (P).Hdr, R) loop
         pragma Loop_Invariant (Lo <= P and then P < Hi);
         pragma Loop_Invariant (for all I in Lo .. P - 1 => Key_Lt (H (I).Hdr, R));
         pragma Loop_Variant (Increases => P);
         P := P + 1;
      end loop;
      Lemma_Key_After (H, N, R, P, Hi);
      pragma Assert (for all I in 1 .. Lo - 1 => Key_Lt (H (I).Hdr, R));
   end Find_Pos;

   --  Outside the run of R's entity, no record equals R, dominates R or is
   --  dominated by R (R is data, so each of the three needs R's entity).
   procedure Lemma_Outside_Run_Row (H : Entry_Array; N : Natural; R : Header; Lo, Hi : Positive) with
     Ghost, Global => null,
     Pre  => H'First = 1 and then N <= H'Last and then Is_Data (R)
             and then Lo <= Hi and then Hi <= N + 1
             and then (for all I in 1 .. Lo - 1 => Ent_Lt (H (I).Hdr.Ent, R.Ent))
             and then (for all I in Hi .. N => Ent_Lt (R.Ent, H (I).Hdr.Ent)),
     Post => (for all I in 1 .. N =>
                (if I < Lo or else I >= Hi then
                   H (I).Hdr /= R and then not Dominates (H (I).Hdr, R)
                   and then not Dominates (R, H (I).Hdr)))
   is
   begin
      pragma Assert (for all I in 1 .. Lo - 1 => H (I).Hdr.Ent /= R.Ent);
      pragma Assert (for all I in Hi .. N => H (I).Hdr.Ent /= R.Ent);
   end Lemma_Outside_Run_Row;

   --  R dominates no record below its key (Lemma_Dominator_In_Run).
   procedure Lemma_No_Drop_Below (H : Entry_Array; N : Natural; R : Header; P : Positive) with
     Ghost, Global => null,
     Pre  => H'First = 1 and then N <= H'Last and then Is_Data (R) and then Canonical (R)
             and then (for all I in 1 .. N => Is_Data (H (I).Hdr) and then Canonical (H (I).Hdr))
             and then (for all I in 1 .. N => (if I < P then Key_Lt (H (I).Hdr, R))),
     Post => (for all I in 1 .. N => (if I < P then not Dominates (R, H (I).Hdr)))
   is
   begin
      for I in 1 .. N loop
         if I < P and then Dominates (R, H (I).Hdr) then
            Lemma_Dominator_In_Run (R, H (I).Hdr);
         end if;
         pragma Loop_Invariant
           (for all I2 in 1 .. I => (if I2 < P then not Dominates (R, H (I2).Hdr)));
      end loop;
   end Lemma_No_Drop_Below;

   --  A subsequence of a sorted row is sorted.
   procedure Lemma_Sub_Sorted
     (OH : Entry_Array; ON : Natural; H : Entry_Array; N : Natural; Src : Index_Map)
   with
     Ghost, Global => null,
     Pre  => Sorted_Row (OH, ON) and then H'First = 1 and then N <= H'Last
             and then Src'First = 1 and then Src'Last >= N
             and then (for all J in 1 .. N => Src (J) in 1 .. ON and then H (J) = OH (Src (J)))
             and then (for all J in 1 .. N =>
                         (for all J2 in 1 .. N => (if J < J2 then Src (J) < Src (J2)))),
     Post => Sorted_Row (H, N)
   is
   begin
      for J in 1 .. N loop
         pragma Assert
           (for all J2 in J + 1 .. N => Key_Lt (OH (Src (J)).Hdr, OH (Src (J2)).Hdr));
         pragma Loop_Invariant
           (for all J3 in 1 .. J =>
              (for all J2 in J3 + 1 .. N => Key_Lt (H (J3).Hdr, H (J2).Hdr)));
      end loop;
   end Lemma_Sub_Sorted;

   --  Set the maps to the identity on 1 .. M.
   procedure Identity_Maps (Src, Dst : in out Index_Map; M : Natural) with
     Ghost, Global => null,
     Pre  => Src'First = 1 and then Dst'First = 1
             and then M <= Src'Last and then M <= Dst'Last
             and then Src'Last <= Held_Max and then Dst'Last <= Held_Max,
     Post => (for all J in 1 .. M => Src (J) = J and then Dst (J) = J)
             and then (for all J in M + 1 .. Src'Last => Src (J) = Src'Old (J))
             and then (for all J in M + 1 .. Dst'Last => Dst (J) = Dst'Old (J))
   is
   begin
      for J in 1 .. M loop
         Src (J) := J;
         Dst (J) := J;
         pragma Loop_Invariant (for all J2 in 1 .. J => Src (J2) = J2 and then Dst (J2) = J2);
         pragma Loop_Invariant (for all J2 in J + 1 .. Src'Last => Src (J2) = Src'Loop_Entry (J2));
         pragma Loop_Invariant (for all J2 in J + 1 .. Dst'Last => Dst (J2) = Dst'Loop_Entry (J2));
      end loop;
   end Identity_Maps;

   --  The maps after an insertion at P into a row of N1 records (ON: the
   --  length of the original row that Dst maps).
   procedure Shift_Maps (Src, Dst : in out Index_Map; N1, ON : Natural; P : Positive) with
     Ghost, Global => null,
     Pre  => Src'First = 1 and then Dst'First = 1 and then N1 < Src'Last
             and then Src'Last <= Held_Max
             and then ON <= Dst'Last and then P <= N1 + 1
             and then (for all I in 1 .. ON => Dst (I) <= N1),
     Post => Src (P) = 0
             and then (for all J in 1 .. P - 1 => Src (J) = Src'Old (J))
             and then (for all J in P + 1 .. N1 + 1 => Src (J) = Src'Old (J - 1))
             and then (for all I in 1 .. ON =>
                         Dst (I) = (if Dst'Old (I) = 0 then 0
                                    elsif Dst'Old (I) < P then Dst'Old (I)
                                    else Dst'Old (I) + 1))
   is
   begin
      for J in reverse P .. N1 loop
         pragma Loop_Invariant (for all K in 1 .. J => Src (K) = Src'Loop_Entry (K));
         pragma Loop_Invariant
           (for all K in J + 2 .. N1 + 1 => Src (K) = Src'Loop_Entry (K - 1));
         Src (J + 1) := Src (J);
      end loop;
      Src (P) := 0;
      for I in 1 .. ON loop
         pragma Loop_Invariant (for all K in I .. ON => Dst (K) = Dst'Loop_Entry (K));
         pragma Loop_Invariant
           (for all K in 1 .. I - 1 =>
              Dst (K) = (if Dst'Loop_Entry (K) = 0 then 0
                         elsif Dst'Loop_Entry (K) < P then Dst'Loop_Entry (K)
                         else Dst'Loop_Entry (K) + 1));
         if Dst (I) >= P then
            Dst (I) := Dst (I) + 1;
         end if;
      end loop;
   end Shift_Maps;

   --  The row (H, N) is the old row (OH, ON) without some records that R
   --  dominates. The records before P did not move; the others come from
   --  P or later, in order. Dst gives the new place of each old record (0:
   --  dropped).
   function Mid_Row
     (OH : Entry_Array; ON : Natural; H : Entry_Array; N : Natural;
      R : Header; P : Positive; Src, Dst : Index_Map) return Boolean
   is
     (OH'First = 1 and then H'First = 1 and then ON <= OH'Last and then N <= H'Last
      and then Src'First = 1 and then Dst'First = 1
      and then Src'Last >= N and then Dst'Last >= ON
      and then P <= N + 1 and then N <= ON
      and then (for all J in 1 .. N =>
                  Src (J) in 1 .. ON and then H (J) = OH (Src (J))
                  and then not Dominates (R, OH (Src (J)).Hdr)
                  and then (if J < P then Src (J) = J else Src (J) >= P))
      and then (for all J in 1 .. N =>
                  (for all J2 in J + 1 .. N => Src (J) < Src (J2)))
      and then (for all I in 1 .. ON =>
                  (if Dst (I) = 0 then Dominates (R, OH (I).Hdr)
                   else Dst (I) in 1 .. N and then Src (Dst (I)) = I)))
   with Ghost;

   --  The new row (H, N) is the old row without the records that R
   --  dominates, with R at P: the records before P come from before P,
   --  the records after P from P or later, in order.
   --  (Kept_Src: the part on Src. Dst is the inverse of Src on the kept
   --  records, Src (Dst (I)) = I, so no fact reads H at Dst (I): an array
   --  read there would let the provers chain Src and Dst without end.)
   function Kept_Src
     (OH : Entry_Array; ON : Natural; H : Entry_Array; N : Natural;
      R : Header; Tg : U64; P : Positive; Src : Index_Map) return Boolean
   is
     (OH'First = 1 and then H'First = 1 and then ON <= OH'Last and then N <= H'Last
      and then Src'First = 1 and then Src'Last >= N
      and then P <= N and then H (P) = (Hdr => R, Tag => Tg) and then Src (P) = 0
      and then (for all J in 1 .. N =>
                  (if J /= P then
                     Src (J) in 1 .. ON and then H (J) = OH (Src (J))
                     and then not Dominates (R, OH (Src (J)).Hdr)
                     and then (if J < P then Src (J) < P else Src (J) >= P)))
      and then (for all J in 1 .. N =>
                  (for all J2 in J + 1 .. N =>
                     (if J /= P and then J2 /= P then Src (J) < Src (J2)))))
   with Ghost;

   function Kept_Row
     (OH : Entry_Array; ON : Natural; H : Entry_Array; N : Natural;
      R : Header; Tg : U64; P : Positive; Src, Dst : Index_Map) return Boolean
   is
     (Kept_Src (OH, ON, H, N, R, Tg, P, Src)
      and then Dst'First = 1 and then Dst'Last >= ON
      and then (for all I in 1 .. ON =>
                  (if Dst (I) = 0 then Dominates (R, OH (I).Hdr)
                   else Dst (I) in 1 .. N and then Dst (I) /= P
                        and then Src (Dst (I)) = I)))
   with Ghost;

   --  The order conjunct of Kept_Row, alone.
   procedure Lemma_Kept_Mono
     (OH : Entry_Array; ON : Natural; H : Entry_Array; N : Natural;
      R : Header; Tg : U64; P : Positive; Src : Index_Map)
   with
     Ghost, Global => null,
     Pre  => Kept_Src (OH, ON, H, N, R, Tg, P, Src),
     Post => (for all J in 1 .. N =>
                (for all J2 in J + 1 .. N =>
                   (if J /= P and then J2 /= P then Src (J) < Src (J2))))
             and then (for all J in 1 .. N =>
                         (if J /= P then
                            Src (J) in 1 .. ON and then H (J) = OH (Src (J))
                            and then not Dominates (R, OH (Src (J)).Hdr)
                            and then (if J < P then Src (J) < P else Src (J) >= P)))
   is
   begin
      null;
   end Lemma_Kept_Mono;

   procedure Lemma_Insert_Kept
     (OH : Entry_Array; ON : Natural; H1 : Entry_Array; N1 : Natural;
      H2 : Entry_Array; N2 : Natural; R : Header; Tg : U64; P : Positive;
      Src1, Dst1, Src2, Dst2 : Index_Map)
   with
     Ghost, Global => null,
     Pre  => Mid_Row (OH, ON, H1, N1, R, P, Src1, Dst1)
             and then H2'First = 1 and then N2 = N1 + 1 and then N2 <= H2'Last
             and then H2 (P) = (Hdr => R, Tag => Tg)
             and then (for all J in 1 .. P - 1 => H2 (J) = H1 (J))
             and then (for all J in P + 1 .. N2 => H2 (J) = H1 (J - 1))
             and then Src2'First = 1 and then Src2'Last >= N2
             and then Dst2'First = 1 and then Dst2'Last >= ON
             and then Src2 (P) = 0
             and then (for all J in 1 .. P - 1 => Src2 (J) = Src1 (J))
             and then (for all J in P + 1 .. N2 => Src2 (J) = Src1 (J - 1))
             and then (for all I in 1 .. ON =>
                         Dst2 (I) = (if Dst1 (I) = 0 then 0
                                     elsif Dst1 (I) < P then Dst1 (I)
                                     else Dst1 (I) + 1)),
     Post => Kept_Row (OH, ON, H2, N2, R, Tg, P, Src2, Dst2)
   is
   begin
      pragma Assert
        (for all J in 1 .. P - 1 =>
           Src2 (J) = J and then H2 (J) = OH (J) and then not Dominates (R, OH (J).Hdr));
      pragma Assert
        (for all J in P + 1 .. N2 =>
           Src2 (J) = Src1 (J - 1) and then Src1 (J - 1) in P .. ON
           and then H2 (J) = OH (Src2 (J)) and then not Dominates (R, OH (Src2 (J)).Hdr));
      pragma Assert
        (for all J in 1 .. N2 =>
           (if J /= P then
              Src2 (J) in 1 .. ON and then H2 (J) = OH (Src2 (J))
              and then not Dominates (R, OH (Src2 (J)).Hdr)
              and then (if J < P then Src2 (J) < P else Src2 (J) >= P)));
      pragma Assert
        (for all J in P + 1 .. N2 =>
           (for all J2 in J + 1 .. N2 => Src2 (J) < Src2 (J2)));
      pragma Assert
        (for all J in 1 .. P - 1 =>
           (for all J2 in J + 1 .. N2 => (if J2 /= P then Src2 (J) < Src2 (J2))));
      pragma Assert
        (for all J in 1 .. N2 =>
           (for all J2 in J + 1 .. N2 =>
              (if J /= P and then J2 /= P then Src2 (J) < Src2 (J2))));
      pragma Assert (Kept_Src (OH, ON, H2, N2, R, Tg, P, Src2));
      for I in 1 .. ON loop
         if Dst1 (I) /= 0 then
            pragma Assert (Src1 (Dst1 (I)) = I);
            if Dst1 (I) < P then
               pragma Assert (Dst2 (I) = Dst1 (I) and then Src2 (Dst1 (I)) = Src1 (Dst1 (I)));
            else
               pragma Assert (Dst2 (I) = Dst1 (I) + 1);
               pragma Assert (Src2 (Dst1 (I) + 1) = Src1 (Dst1 (I)));
            end if;
         end if;
         pragma Assert
           (if Dst2 (I) = 0 then Dominates (R, OH (I).Hdr)
            else Dst2 (I) in 1 .. N2 and then Dst2 (I) /= P
                 and then Src2 (Dst2 (I)) = I);
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              (if Dst2 (I2) = 0 then Dominates (R, OH (I2).Hdr)
               else Dst2 (I2) in 1 .. N2 and then Dst2 (I2) /= P
                    and then Src2 (Dst2 (I2)) = I2));
      end loop;
   end Lemma_Insert_Kept;

   --  The maps of an insertion at P after a compaction (Mid_Row): shift
   --  them, and the new row is Kept_Row, with the records from Hi on one
   --  place further.
   procedure Lemma_Insert_Maps
     (OH : Entry_Array; ON : Natural; H1 : Entry_Array; N1 : Natural;
      H2 : Entry_Array; N2 : Natural; R : Header; Tg : U64; P, Hi : Positive;
      Src1, Dst1 : Index_Map; Src2, Dst2 : out Index_Map)
   with
     Ghost, Global => null,
     Pre  => Mid_Row (OH, ON, H1, N1, R, P, Src1, Dst1)
             and then Src2'First = Src1'First and then Src2'Last = Src1'Last
             and then Dst2'First = Dst1'First and then Dst2'Last = Dst1'Last
             and then N1 < Src1'Last and then Src1'Last <= Held_Max
             and then H2'First = 1 and then N2 = N1 + 1 and then N2 <= H2'Last
             and then H2 (P) = (Hdr => R, Tag => Tg)
             and then (for all J in 1 .. P - 1 => H2 (J) = H1 (J))
             and then (for all J in P + 1 .. N2 => H2 (J) = H1 (J - 1))
             and then (for all I in Hi .. ON => Dst1 (I) = I + N1 - ON and then Dst1 (I) >= P),
     Post => Kept_Row (OH, ON, H2, N2, R, Tg, P, Src2, Dst2)
             and then (for all I in Hi .. ON => Dst2 (I) = I + N2 - ON)
   is
   begin
      Src2 := Src1;
      Dst2 := Dst1;
      pragma Assert (for all I in 1 .. ON => Dst2 (I) <= N1);
      Shift_Maps (Src2, Dst2, N1, ON, P);
      Lemma_Insert_Kept (OH, ON, H1, N1, H2, N2, R, Tg, P, Src1, Dst1, Src2, Dst2);
   end Lemma_Insert_Maps;

   --  The three row facts of a step, each on the arrays alone (a small
   --  context): the new row (H, N) holds R at P and old records elsewhere
   --  (Src).

   procedure Lemma_Step_Antichain
     (OH : Entry_Array; ON : Natural; H : Entry_Array; N : Natural;
      R : Header; P : Positive; Src : Index_Map)
   with
     Ghost, Global => null,
     Pre  => OH'First = 1 and then H'First = 1 and then ON <= OH'Last and then N <= H'Last
             and then Src'First = 1 and then Src'Last >= N
             and then P <= N and then H (P).Hdr = R and then not Dominates (R, R)
             and then (for all J in 1 .. N =>
                         (if J /= P then Src (J) in 1 .. ON and then H (J) = OH (Src (J))))
             and then (for all I in 1 .. ON =>
                         (for all I2 in 1 .. ON => not Dominates (OH (I2).Hdr, OH (I).Hdr)))
             and then (for all I in 1 .. ON => not Dominates (OH (I).Hdr, R))
             and then (for all J in 1 .. N =>
                         (if J /= P then not Dominates (R, OH (Src (J)).Hdr))),
     Post => (for all J in 1 .. N =>
                (for all J2 in 1 .. N => not Dominates (H (J2).Hdr, H (J).Hdr)))
   is
   begin
      for J in 1 .. N loop
         for J2 in 1 .. N loop
            if J /= P and then J2 /= P then
               pragma Assert (not Dominates (OH (Src (J2)).Hdr, OH (Src (J)).Hdr));
            elsif J /= P then
               pragma Assert (H (J2).Hdr = R and then not Dominates (R, OH (Src (J)).Hdr));
            elsif J2 /= P then
               pragma Assert (H (J).Hdr = R and then not Dominates (OH (Src (J2)).Hdr, R));
            end if;
            pragma Assert (not Dominates (H (J2).Hdr, H (J).Hdr));
            pragma Loop_Invariant
              (for all J3 in 1 .. J2 => not Dominates (H (J3).Hdr, H (J).Hdr));
         end loop;
         pragma Loop_Invariant
           (for all J4 in 1 .. J =>
              (for all J3 in 1 .. N => not Dominates (H (J3).Hdr, H (J4).Hdr)));
      end loop;
   end Lemma_Step_Antichain;

   procedure Lemma_Step_Distinct
     (OH : Entry_Array; ON : Natural; H : Entry_Array; N : Natural;
      R : Header; P : Positive; Src : Index_Map)
   with
     Ghost, Global => null,
     Pre  => OH'First = 1 and then H'First = 1 and then ON <= OH'Last and then N <= H'Last
             and then Src'First = 1 and then Src'Last >= N
             and then P <= N and then H (P).Hdr = R
             and then (for all J in 1 .. N =>
                         (if J /= P then Src (J) in 1 .. ON and then H (J) = OH (Src (J))))
             and then (for all J in 1 .. N =>
                         (for all J2 in J + 1 .. N =>
                            (if J /= P and then J2 /= P then Src (J) < Src (J2))))
             and then (for all I in 1 .. ON =>
                         (for all I2 in 1 .. ON =>
                            (if I /= I2 then OH (I).Hdr /= OH (I2).Hdr)))
             and then (for all I in 1 .. ON => OH (I).Hdr /= R),
     Post => (for all J in 1 .. N =>
                (for all J2 in 1 .. N => (if J /= J2 then H (J).Hdr /= H (J2).Hdr)))
   is
   begin
      for J in 1 .. N loop
         for J2 in 1 .. N loop
            if J /= J2 then
               if J /= P and then J2 /= P then
                  if J < J2 then
                     pragma Assert (Src (J) < Src (J2));
                  else
                     pragma Assert (Src (J2) < Src (J));
                  end if;
                  pragma Assert (OH (Src (J)).Hdr /= OH (Src (J2)).Hdr);
               elsif J /= P then
                  pragma Assert (H (J2).Hdr = R and then OH (Src (J)).Hdr /= R);
               else
                  pragma Assert (H (J).Hdr = R and then OH (Src (J2)).Hdr /= R);
               end if;
               pragma Assert (H (J).Hdr /= H (J2).Hdr);
            end if;
            pragma Loop_Invariant
              (for all J3 in 1 .. J2 => (if J /= J3 then H (J).Hdr /= H (J3).Hdr));
         end loop;
         pragma Loop_Invariant
           (for all J4 in 1 .. J =>
              (for all J3 in 1 .. N => (if J4 /= J3 then H (J4).Hdr /= H (J3).Hdr)));
      end loop;
   end Lemma_Step_Distinct;

   procedure Lemma_Step_Sorted
     (OH : Entry_Array; ON : Natural; H : Entry_Array; N : Natural;
      R : Header; P : Positive; Src : Index_Map)
   with
     Ghost, Global => null,
     Pre  => Sorted_Row (OH, ON) and then H'First = 1 and then N <= H'Last
             and then Src'First = 1 and then Src'Last >= N
             and then P <= N and then H (P).Hdr = R
             and then (for all J in 1 .. N =>
                         (if J /= P then Src (J) in 1 .. ON and then H (J) = OH (Src (J))))
             and then (for all J in 1 .. N =>
                         (for all J2 in J + 1 .. N =>
                            (if J /= P and then J2 /= P then Src (J) < Src (J2))))
             and then (for all J in 1 .. P - 1 => Key_Lt (H (J).Hdr, R))
             and then (for all J in P + 1 .. N => Key_Lt (R, H (J).Hdr)),
     Post => Sorted_Row (H, N)
   is
   begin
      for J in 1 .. N loop
         for J2 in J + 1 .. N loop
            if J /= P and then J2 /= P then
               pragma Assert (Src (J) < Src (J2));
               pragma Assert (Key_Lt (OH (Src (J)).Hdr, OH (Src (J2)).Hdr));
            end if;
            pragma Assert (Key_Lt (H (J).Hdr, H (J2).Hdr));
            pragma Loop_Invariant
              (for all J3 in J + 1 .. J2 => Key_Lt (H (J).Hdr, H (J3).Hdr));
         end loop;
         pragma Loop_Invariant
           (for all J4 in 1 .. J =>
              (for all J3 in J4 + 1 .. N => Key_Lt (H (J4).Hdr, H (J3).Hdr)));
      end loop;
   end Lemma_Step_Sorted;
   --  The data row of Upd is a sorted frontier row: Kept_Row from a sorted
   --  frontier row, R undominated and new, and R's place P in key order.
   procedure Lemma_Data_Step
     (Old, Upd : State; R : Header; Tg : U64; P : Positive; Src : Index_Map)
   with
     Ghost, Global => null,
     Pre  => Shape (Old) and then Data_OK (Old) and then Data_Sorted (Old)
             and then Upd.ND <= Upd.Cap
             and then Kept_Src (Old.Data_E, Old.ND, Upd.Data_E, Upd.ND, R, Tg, P, Src)
             and then (for all I in 1 .. Old.ND => Data_Item_OK (Upd, Old.Data_E (I).Hdr))
             and then Data_Item_OK (Upd, R)
             and then (for all I in 1 .. Old.ND =>
                         Old.Data_E (I).Hdr /= R and then not Dominates (Old.Data_E (I).Hdr, R))
             and then (for all I in 1 .. Old.ND =>
                         (if I < P then Key_Lt (Old.Data_E (I).Hdr, R)
                          else not Key_Lt (Old.Data_E (I).Hdr, R))),
     Post => Data_OK (Upd) and then Data_Sorted (Upd)
   is
      ON : constant Natural := Old.ND;
      UN : constant Natural := Upd.ND;
   begin
      pragma Assert (Data_Count (Old) = ON and then Data_Count (Upd) = UN);
      Lemma_Dominates_Irrefl (R);
      Lemma_Kept_Mono (Old.Data_E, Old.ND, Upd.Data_E, Upd.ND, R, Tg, P, Src);
      --  R is below each later record (the key is unique, Lemma_Key_Total).
      for J in P + 1 .. UN loop
         pragma Assert (Src (J) in P .. ON);
         pragma Assert (Data_Item_OK (Old, Old.Data_E (Src (J)).Hdr));
         Lemma_Key_Total (Old.Data_E (Src (J)).Hdr, R);
         pragma Assert (Key_Lt (R, Upd.Data_E (J).Hdr));
         pragma Loop_Invariant (for all J2 in P + 1 .. J => Key_Lt (R, Upd.Data_E (J2).Hdr));
      end loop;

      pragma Assert (for all J in 1 .. UN => Data_Item_OK (Upd, Upd.Data_E (J).Hdr));

      --  The facts of the three row lemmas.
      pragma Assert
        (for all J in 1 .. UN =>
           (if J /= P then Src (J) in 1 .. ON and then Upd.Data_E (J) = Old.Data_E (Src (J))));
      pragma Assert
        (for all J in 1 .. UN => (if J /= P then not Dominates (R, Old.Data_E (Src (J)).Hdr)));
      pragma Assert
        (for all J in 1 .. UN =>
           (for all J2 in J + 1 .. UN =>
              (if J /= P and then J2 /= P then Src (J) < Src (J2))));
      pragma Assert (for all J in 1 .. P - 1 => Src (J) < P);
      pragma Assert (for all J in 1 .. P - 1 => Key_Lt (Upd.Data_E (J).Hdr, R));
      pragma Assert
        (for all I in 1 .. ON =>
           (for all I2 in 1 .. ON => not Dominates (Old.Data_E (I2).Hdr, Old.Data_E (I).Hdr)));
      pragma Assert
        (for all I in 1 .. ON =>
           (for all I2 in 1 .. ON =>
              (if I /= I2 then Old.Data_E (I).Hdr /= Old.Data_E (I2).Hdr)));
      pragma Assert (Sorted_Row (Old.Data_E, ON));

      Lemma_Step_Antichain (Old.Data_E, ON, Upd.Data_E, UN, R, P, Src);
      Lemma_Step_Distinct (Old.Data_E, ON, Upd.Data_E, UN, R, P, Src);
      Lemma_Step_Sorted (Old.Data_E, ON, Upd.Data_E, UN, R, P, Src);
      pragma Assert (Data_OK (Upd));
      pragma Assert (Data_Sorted (Upd));
   end Lemma_Data_Step;

   ---------------------------------------------------------------------
   --  Runs and slots (SIMPLIFY.md S14)
   ---------------------------------------------------------------------

   function Run (S : State; Ent : Id128) return Index_Range is
     (Run_Of (S.Data_E, Data_Count (S), Ent));

   function Slot (S : State; Signer : Key256) return Index_Range is
     (declare
        K : constant Slot_Number := Slot_Of (S, Signer);
      begin
        (if K = 0 then (First => Count (S) + 1, Last => Count (S))
         else (First => Data_Count (S) + S.A.Offs (K) + 1,
               Last  => Data_Count (S) + S.A.Offs (K) + SC (S.A, K))));

   --  Outside_Run is opaque to the rest of this body (Lemma_Outside_Run_P
   --  unfolds it), so a Post that names it is proved from a lemma's Post
   --  by congruence, not by unfolding.
   package Run_Views with SPARK_Mode is
      function Outside_Run_P (Old, Upd : State; E : Id128) return Boolean with
        Global => null,
        Pre    => Is_Frontier (Old) and then Is_Frontier (Upd);
      procedure Lemma_Outside_Run_P (Old, Upd : State; E : Id128) with
        Ghost, Global => null,
        Pre  => Is_Frontier (Old) and then Is_Frontier (Upd),
        Post => Outside_Run_P (Old, Upd, E) =
             ((declare
                      RO : constant Index_Range := Run (Old, E);
                      RU : constant Index_Range := Run (Upd, E);
                    begin
                      RU.First = RO.First
                      and then Data_Count (Upd) - RU.Last = Data_Count (Old) - RO.Last
                      and then (for all I in 1 .. RO.First - 1 =>
                                  Data_Held (Upd, I) = Data_Held (Old, I)
                                  and then Data_Tag (Upd, I) = Data_Tag (Old, I))
                      and then (for all I in RO.Last + 1 .. Data_Count (Old) =>
                                  Data_Held (Upd, I - RO.Last + RU.Last) = Data_Held (Old, I)
                                  and then Data_Tag (Upd, I - RO.Last + RU.Last) = Data_Tag (Old, I)))
                   and then Slots_Used (Upd) = Slots_Used (Old)
                   and then (for all K in Slot_Index =>
                               Slot_Count (Upd, K) = Slot_Count (Old, K)
                               and then Off (Upd, K) = Off (Old, K))
                   and then (for all K in 1 .. Slots_Used (Old) =>
                               Slot_Key (Upd, K) = Slot_Key (Old, K)
                               and then (for all J in 1 .. Slot_Count (Old, K) =>
                                           Auth_Held (Upd, K, J) = Auth_Held (Old, K, J)
                                           and then Auth_Tag (Upd, K, J) = Auth_Tag (Old, K, J))));
   end Run_Views;

   package body Run_Views with SPARK_Mode is
      function Outside_Run_P (Old, Upd : State; E : Id128) return Boolean is
        ((declare
            RO : constant Index_Range := Run (Old, E);
            RU : constant Index_Range := Run (Upd, E);
          begin
            RU.First = RO.First
            and then Data_Count (Upd) - RU.Last = Data_Count (Old) - RO.Last
            and then (for all I in 1 .. RO.First - 1 =>
                        Data_Held (Upd, I) = Data_Held (Old, I)
                        and then Data_Tag (Upd, I) = Data_Tag (Old, I))
            and then (for all I in RO.Last + 1 .. Data_Count (Old) =>
                        Data_Held (Upd, I - RO.Last + RU.Last) = Data_Held (Old, I)
                        and then Data_Tag (Upd, I - RO.Last + RU.Last) = Data_Tag (Old, I)))
         and then Slots_Used (Upd) = Slots_Used (Old)
         and then (for all K in Slot_Index =>
                     Slot_Count (Upd, K) = Slot_Count (Old, K)
                     and then Off (Upd, K) = Off (Old, K))
         and then (for all K in 1 .. Slots_Used (Old) =>
                     Slot_Key (Upd, K) = Slot_Key (Old, K)
                     and then (for all J in 1 .. Slot_Count (Old, K) =>
                                 Auth_Held (Upd, K, J) = Auth_Held (Old, K, J)
                                 and then Auth_Tag (Upd, K, J) = Auth_Tag (Old, K, J))));

      procedure Lemma_Outside_Run_P (Old, Upd : State; E : Id128) is null;
   end Run_Views;
   use Run_Views;

   function Outside_Run (Old, Upd : State; E : Id128) return Boolean is
     (Outside_Run_P (Old, Upd, E));

   function Outside_Slot (Old, Upd : State; Signer : Key256) return Boolean is
     (Data_Count (Upd) = Data_Count (Old)
      and then (for all I in 1 .. Data_Count (Old) =>
                  Data_Held (Upd, I) = Data_Held (Old, I)
                  and then Data_Tag (Upd, I) = Data_Tag (Old, I))
      and then Slot_Of (Upd, Signer) /= 0
      and then (if Slot_Of (Old, Signer) /= 0
                then Slot_Of (Upd, Signer) = Slot_Of (Old, Signer)
                     and then Slots_Used (Upd) = Slots_Used (Old)
                else Slot_Of (Upd, Signer) = Slots_Used (Old) + 1
                     and then Slots_Used (Upd) = Slots_Used (Old) + 1)
      and then (for all K in 1 .. Slots_Used (Old) =>
                  Slot_Key (Upd, K) = Slot_Key (Old, K))
      and then (for all K in Slot_Index =>
                  (if K /= Slot_Of (Upd, Signer) then
                     Slot_Count (Upd, K) = Slot_Count (Old, K)
                     and then (for all J in 1 .. Slot_Count (Old, K) =>
                                 Auth_Held (Upd, K, J) = Auth_Held (Old, K, J)
                                 and then Auth_Tag (Upd, K, J) = Auth_Tag (Old, K, J)))));

   procedure Lemma_Outside_Run (Old, Upd : State; E : Id128) is
   begin
      Lemma_Outside_Run_P (Old, Upd, E);
   end Lemma_Outside_Run;

   procedure Lemma_Outside_Slot (Old, Upd : State; Signer : Key256) is null;

   procedure Lemma_Run_Def (S : State; E : Id128) is
      R : constant Index_Range := Run (S, E);
   begin
      pragma Assert (not Ent_Lt (E, E));
      pragma Assert (for all I in 1 .. R.First - 1 => S.Data_E (I).Hdr.Ent /= E);
      pragma Assert (for all I in R.Last + 1 .. Data_Count (S) => S.Data_E (I).Hdr.Ent /= E);
   end Lemma_Run_Def;

   procedure Lemma_Slot_Def (S : State; Signer : Key256) is
      K  : constant Slot_Number := Slot_Of (S, Signer);
      SR : constant Index_Range := Slot (S, Signer);
      DC : constant Natural := Data_Count (S);
   begin
      Lemma_Off_Mono (S);
      Lemma_All_Flat (S);
      for I in 1 .. Count (S) loop
         Lemma_Flat_Row (S, I);
         Lemma_Item (S, Row_Of (S, I), Pos_Of (S, I));
         declare
            K2 : constant Slot_Number := Row_Of (S, I);
         begin
            if K2 = 0 then
               pragma Assert (I <= DC);
               pragma Assert (not Is_Auth (Held (S, I)));
               pragma Assert (I not in SR.First .. SR.Last);
            else
               pragma Assert (I = DC + S.A.Offs (K2) + Pos_Of (S, I));
               pragma Assert (Held (S, I).Issuer = S.A.Keys (K2));
               if K2 = K then
                  pragma Assert (I in SR.First .. SR.Last);
               elsif K = 0 then
                  pragma Assert (S.A.Keys (K2) /= Signer);
                  pragma Assert (I not in SR.First .. SR.Last);
               else
                  pragma Assert (S.A.Keys (K2) /= Signer);
                  if K2 < K then
                     pragma Assert (S.A.Offs (K2) + S.A.NA (K2) <= S.A.Offs (K));
                  else
                     pragma Assert (S.A.Offs (K) + S.A.NA (K) <= S.A.Offs (K2));
                  end if;
                  pragma Assert (I not in SR.First .. SR.Last);
               end if;
            end if;
         end;
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              (Is_Auth (Held (S, I2)) and then Held (S, I2).Issuer = Signer)
              = (I2 in SR.First .. SR.Last));
      end loop;
      if K /= 0 then
         for J in 1 .. SC (S.A, K) loop
            Lemma_Row_Flat (S, K, J);
            pragma Assert (Flat_Index (S, K, J) = SR.First + J - 1);
            pragma Loop_Invariant
              (for all J2 in 1 .. J =>
                 Held (S, SR.First + J2 - 1) = S.A.H (K, J2).Hdr
                 and then Tag (S, SR.First + J2 - 1) = S.A.H (K, J2).Tag);
         end loop;
         pragma Assert
           (for all I in SR.First .. SR.Last =>
              Held (S, I) = S.A.H (K, I - SR.First + 1).Hdr
              and then Tag (S, I) = S.A.H (K, I - SR.First + 1).Tag);
      end if;
   end Lemma_Slot_Def;

   --  One instance of the order conjunct of Kept_Src.
   procedure Lemma_Src_Mono
     (OH : Entry_Array; ON : Natural; H : Entry_Array; N : Natural;
      R : Header; Tg : U64; P : Positive; Src : Index_Map; J, J2 : Positive)
   with
     Ghost, Global => null,
     Pre  => Kept_Src (OH, ON, H, N, R, Tg, P, Src)
             and then J < J2 and then J2 <= N and then J /= P and then J2 /= P,
     Post => Src (J) < Src (J2)
   is
   begin
      Lemma_Kept_Mono (OH, ON, H, N, R, Tg, P, Src);
   end Lemma_Src_Mono;

   --  The run of R's entity after a commit (AUDIT.md G25): the records
   --  before P did not move, the records from Hi on moved by N - ON, so
   --  the new run is Lo .. Hi + N - ON - 1.
   procedure Lemma_New_Run
     (OH : Entry_Array; ON : Natural; H : Entry_Array; N : Natural;
      R : Header; Tg : U64; P : Positive; Src, Dst : Index_Map; Lo, Hi : Positive)
   with
     Ghost, Global => null,
     Pre  => Is_Data (R)
             and then Kept_Row (OH, ON, H, N, R, Tg, P, Src, Dst)
             and then Sorted_Row (OH, ON) and then Sorted_Row (H, N)
             and then ON < Held_Max and then N < Held_Max
             and then Lo <= P and then P <= Hi and then Hi <= ON + 1
             and then (for all I in 1 .. Lo - 1 => Ent_Lt (OH (I).Hdr.Ent, R.Ent))
             and then (for all I in Lo .. Hi - 1 => OH (I).Hdr.Ent = R.Ent)
             and then (for all I in Hi .. ON => Ent_Lt (R.Ent, OH (I).Hdr.Ent))
             and then (for all I in 1 .. P - 1 => H (I) = OH (I))
             and then (for all I in Hi .. ON => Dst (I) = I + N - ON),
     Post => Hi + N - ON >= P + 1
             and then Hi + N - ON <= N + 1
             and then (for all I in Hi .. ON => H (I + N - ON) = OH (I))
             and then Run_Of (H, N, R.Ent) = (First => Lo, Last => Hi + N - ON - 1)
   is
      NH : constant Integer := Hi + N - ON;
   begin
      Lemma_Kept_Mono (OH, ON, H, N, R, Tg, P, Src);
      --  The suffix: each old record from Hi on is at I + N - ON.
      for I in Hi .. ON loop
         pragma Assert (OH (I).Hdr.Ent /= R.Ent);
         pragma Assert (not Dominates (R, OH (I).Hdr));
         pragma Assert (Dst (I) /= 0);
         pragma Assert (Src (Dst (I)) = I and then Dst (I) /= P);
         pragma Assert (H (I + N - ON) = OH (I));
         pragma Loop_Invariant (for all I2 in Hi .. I => H (I2 + N - ON) = OH (I2));
      end loop;
      --  The number of records from NH on is the number from Hi on, and
      --  P < NH: R and the records of the run before P come first.
      pragma Assert (N - NH = ON - Hi);
      if NH <= P then
         pragma Assert (P - N + ON in Hi .. ON);
         pragma Assert (H (P) = OH (P - N + ON));
         pragma Assert (Ent_Lt (R.Ent, R.Ent));
         pragma Assert (False);
      end if;
      pragma Assert (NH >= P + 1);
      --  The new run.
      for J in Lo .. NH - 1 loop
         if J < P then
            pragma Assert (H (J) = OH (J));
         elsif J > P then
            pragma Assert (Src (J) >= P);
            if Hi <= ON then
               pragma Assert (Dst (Hi) = NH);
               pragma Assert (Src (Dst (Hi)) = Hi);
               pragma Assert (Src (NH) = Hi);
               pragma Assert (J /= P and then NH /= P and then J < NH);
               Lemma_Src_Mono (OH, ON, H, N, R, Tg, P, Src, J, NH);
               pragma Assert (Src (J) < Src (NH));
            end if;
            pragma Assert (Src (J) <= Hi - 1);
            pragma Assert (H (J).Hdr.Ent = R.Ent);
         end if;
         pragma Loop_Invariant (for all J2 in Lo .. J => H (J2).Hdr.Ent = R.Ent);
      end loop;
      pragma Assert (for all J in 1 .. Lo - 1 => Ent_Lt (H (J).Hdr.Ent, R.Ent));
      pragma Assert (for all J in NH .. N => J - N + ON in Hi .. ON);
      pragma Assert (for all J in NH .. N => H (J) = OH (J - N + ON));
      pragma Assert (for all J in NH .. N => Ent_Lt (R.Ent, H (J).Hdr.Ent));
      Lemma_Run_Unique (H, N, R.Ent, Lo, NH);
   end Lemma_New_Run;

   --  Two authorization row sets that are equal at every used position,
   --  tags included.
   function Same_Rows (A1, A2 : Auth_Rows) return Boolean is
     (A1.NSlots = A2.NSlots and then A1.NAuth = A2.NAuth
      and then (for all K in Slot_Index =>
                  A1.NA (K) = A2.NA (K) and then A1.Keys (K) = A2.Keys (K)
                  and then A1.Offs (K) = A2.Offs (K))
      and then (for all K in Slot_Index =>
                  (for all J in 1 .. SC (A1, K) => A1.H (K, J) = A2.H (K, J))))
   with Ghost;

   --  Rows that agree at every used position share the authorization
   --  invariants.
   procedure Lemma_Same_Rows_OK (A1, A2 : Auth_Rows; Fnd : Key256) with
     Ghost, Global => null,
     Pre  => Same_Rows (A1, A2) and then Auth_Shape (A1) and then Slots_OK (A1, Fnd)
             and then Auth_OK (A1),
     Post => Auth_Shape (A2) and then Slots_OK (A2, Fnd) and then Auth_OK (A2)
             and then Rows_Agree (A1, A2)
   is
   begin
      for K in Slot_Index loop
         pragma Assert (SC (A1, K) = SC (A2, K));
         pragma Assert (for all J in 1 .. SC (A1, K) => A2.H (K, J) = A1.H (K, J));
         pragma Loop_Invariant
           (for all K2 in 1 .. K =>
              (for all J in 1 .. SC (A2, K2) =>
                 Is_Auth (A2.H (K2, J).Hdr) and then Canonical (A2.H (K2, J).Hdr)
                 and then A2.H (K2, J).Hdr.Issuer = A2.Keys (K2)));
         pragma Loop_Invariant
           (for all K2 in 1 .. K =>
              (for all J in 1 .. SC (A2, K2) =>
                 (for all J2 in 1 .. SC (A2, K2) =>
                    not Dominates (A2.H (K2, J2).Hdr, A2.H (K2, J).Hdr))));
         pragma Loop_Invariant
           (for all K2 in 1 .. K =>
              (for all J in 1 .. SC (A2, K2) =>
                 (for all J2 in 1 .. SC (A2, K2) =>
                    (if J /= J2 then A2.H (K2, J).Hdr /= A2.H (K2, J2).Hdr))));
      end loop;
   end Lemma_Same_Rows_OK;

   --  The frontier invariant after a data commit, in a small context: the
   --  new data row is a sorted frontier row and the authorization rows did
   --  not change.
   procedure Lemma_Data_Frontier
     (Old, Upd : State; R : Header; Tg : U64; P : Positive; Src : Index_Map)
   with
     Ghost, Global => null,
     Pre  => Is_Frontier (Old) and then Canonical (R) and then Is_Data (R)
             and then Admitted (Old, R)
             and then Upd.Cap = Old.Cap and then Upd.Fnd = Old.Fnd
             and then Upd.ND <= Upd.Cap
             and then Same_Rows (Old.A, Upd.A)
             and then Kept_Src (Old.Data_E, Old.ND, Upd.Data_E, Upd.ND, R, Tg, P, Src)
             and then (for all I in 1 .. Old.ND =>
                         Old.Data_E (I).Hdr /= R and then not Dominates (Old.Data_E (I).Hdr, R))
             and then (for all I in 1 .. Old.ND =>
                         (if I < P then Key_Lt (Old.Data_E (I).Hdr, R)
                          else not Key_Lt (Old.Data_E (I).Hdr, R))),
     Post => Is_Frontier (Upd) and then Max_Ceil (Upd) = Max_Ceil (Old)
   is
      N : constant Natural := Old.ND;
   begin
      Lemma_Same_Rows_OK (Old.A, Upd.A, Old.Fnd);
      Lemma_Rows_Agree_Views (Old.A, Upd.A, R.V.Author);
      pragma Assert (Data_Item_OK (Upd, R));
      for I in 1 .. N loop
         pragma Assert (Data_Item_OK (Old, Old.Data_E (I).Hdr));
         Lemma_Rows_Agree_Views (Old.A, Upd.A, Old.Data_E (I).Hdr.V.Author);
         pragma Assert (Data_Item_OK (Upd, Old.Data_E (I).Hdr));
         pragma Loop_Invariant
           (for all I2 in 1 .. I => Data_Item_OK (Upd, Old.Data_E (I2).Hdr));
      end loop;
      pragma Assert (Shape (Old) and then Data_OK (Old) and then Data_Sorted (Old));
      Lemma_Data_Step (Old, Upd, R, Tg, P, Src);
      pragma Assert (Shape (Upd));
      pragma Assert (Is_Frontier (Upd));
   end Lemma_Data_Frontier;

   --  Outside_Run after a data commit, in a small context.
   procedure Lemma_Commit_Run
     (Old, Upd : State; R : Header; Tg : U64; P : Positive; Src, Dst : Index_Map;
      Lo, Hi : Positive)
   with
     Ghost, Global => null,
     Pre  => Is_Frontier (Old) and then Is_Frontier (Upd) and then Is_Data (R)
             and then Same_Rows (Old.A, Upd.A)
             and then Kept_Row (Old.Data_E, Old.ND, Upd.Data_E, Upd.ND, R, Tg, P, Src, Dst)
             and then Lo <= P and then P <= Hi and then Hi <= Old.ND + 1
             and then Run (Old, R.Ent) = (First => Lo, Last => Hi - 1)
             and then (for all I in 1 .. P - 1 => Upd.Data_E (I) = Old.Data_E (I))
             and then (for all I in Hi .. Old.ND => Dst (I) = I + Upd.ND - Old.ND),
     Post => Outside_Run (Old, Upd, R.Ent)
   is
      ON : constant Natural := Old.ND;
      UN : constant Natural := Upd.ND;
   begin
      pragma Assert (Data_Count (Old) = ON and then Data_Count (Upd) = UN);
      pragma Assert (Sorted_Row (Old.Data_E, ON));
      pragma Assert (Sorted_Row (Upd.Data_E, UN));
      pragma Assert (Run_Of (Old.Data_E, ON, R.Ent) = (First => Lo, Last => Hi - 1));
      Lemma_New_Run (Old.Data_E, ON, Upd.Data_E, UN, R, Tg, P, Src, Dst, Lo, Hi);
      pragma Assert (Run (Upd, R.Ent) = (First => Lo, Last => Hi + UN - ON - 1));
      pragma Assert
        (for all I in Hi .. ON => Upd.Data_E (I - (Hi - 1) + (Hi + UN - ON - 1)) = Old.Data_E (I));
      pragma Assert (for all I in 1 .. Lo - 1 => Upd.Data_E (I) = Old.Data_E (I));
      Lemma_Outside_Run_P (Old, Upd, R.Ent);
      pragma Assert
        (Run (Upd, R.Ent).First = Run (Old, R.Ent).First
         and then Data_Count (Upd) - Run (Upd, R.Ent).Last
                  = Data_Count (Old) - Run (Old, R.Ent).Last);
      pragma Assert
        (for all I in 1 .. Run (Old, R.Ent).First - 1 =>
           Data_Held (Upd, I) = Data_Held (Old, I)
           and then Data_Tag (Upd, I) = Data_Tag (Old, I));
      pragma Assert
        (for all I in Run (Old, R.Ent).Last + 1 .. Data_Count (Old) =>
           Data_Held (Upd, I - Run (Old, R.Ent).Last + Run (Upd, R.Ent).Last)
           = Data_Held (Old, I)
           and then Data_Tag (Upd, I - Run (Old, R.Ent).Last + Run (Upd, R.Ent).Last)
                    = Data_Tag (Old, I));
      pragma Assert (Slots_Used (Upd) = Slots_Used (Old));
      pragma Assert
        (for all K in Slot_Index =>
           Slot_Count (Upd, K) = Slot_Count (Old, K) and then Off (Upd, K) = Off (Old, K));
      pragma Assert
        (for all K in 1 .. Slots_Used (Old) =>
           Slot_Key (Upd, K) = Slot_Key (Old, K)
           and then (for all J in 1 .. Slot_Count (Old, K) =>
                       Auth_Held (Upd, K, J) = Auth_Held (Old, K, J)
                       and then Auth_Tag (Upd, K, J) = Auth_Tag (Old, K, J)));
      pragma Assert (Outside_Run_P (Old, Upd, R.Ent));
   end Lemma_Commit_Run;

   --  The slot of a used slot's key is that slot (slot keys are distinct).
   procedure Lemma_Slot_Of_Key (S : State; K0 : Slot_Index) with
     Ghost, Global => null,
     Pre  => Slots_OK (S.A, S.Fnd) and then K0 <= S.A.NSlots,
     Post => Slot_Of (S, S.A.Keys (K0)) = K0
   is
      K : constant Slot_Number := Slot_Of (S, S.A.Keys (K0));
   begin
      pragma Assert (K /= 0);
      pragma Assert (S.A.Keys (K) = S.A.Keys (K0));
      if K /= K0 then
         pragma Assert (S.A.Keys (K) /= S.A.Keys (K0));
      end if;
   end Lemma_Slot_Of_Key;

   --  The flat view after a data commit, in a small context: R is held
   --  with its tag, the rest is a filter of the old records with their
   --  tags, and nothing is lost except by domination.
   procedure Lemma_Data_Flat
     (Old, Upd : State; R : Header; Tg : U64; P : Positive; Src, Dst : Index_Map)
   with
     Ghost, Global => null,
     Pre  => Is_Frontier (Old) and then Is_Frontier (Upd) and then Is_Data (R)
             and then not Holds (Old, R)
             and then Same_Rows (Old.A, Upd.A)
             and then Kept_Row (Old.Data_E, Old.ND, Upd.Data_E, Upd.ND, R, Tg, P, Src, Dst),
     Post => Holds (Upd, R)
             and then (for all I in 1 .. Count (Upd) =>
                         Holds (Old, Held (Upd, I)) or else Held (Upd, I) = R)
             and then (for all I in 1 .. Count (Old) =>
                         Holds (Upd, Held (Old, I)) or else Dominates (R, Held (Old, I)))
             and then (for all I in 1 .. Count (Upd) =>
                         (if Held (Upd, I) = R then Tag (Upd, I) = Tg
                          else Has_Tag (Old, Held (Upd, I), Tag (Upd, I))))
   is
      --  Proved; at run time the invariants would cost O(n^3).
      pragma Assertion_Policy (Assert => Ignore, Loop_Invariant => Ignore);
   begin
      pragma Assert (Data_Count (Old) = Old.ND and then Data_Count (Upd) = Upd.ND);
      Lemma_Kept_Mono (Old.Data_E, Old.ND, Upd.Data_E, Upd.ND, R, Tg, P, Src);
      pragma Assert
        (for all J in 1 .. Upd.ND =>
           (if Src (J) = 0 then J = P and then Upd.Data_E (J) = (Hdr => R, Tag => Tg)
            else Src (J) <= Old.ND and then Upd.Data_E (J) = Old.Data_E (Src (J))));
      pragma Assert
        (for all I in 1 .. Old.ND =>
           (if Dst (I) /= 0 then
              Dst (I) <= Upd.ND and then Upd.Data_E (Dst (I)) = Old.Data_E (I)));
      pragma Assert
        (for all K in Slot_Index =>
           Row_Count (Upd, K) = Row_Count (Old, K)
           and then (for all J in 1 .. Row_Count (Old, K) =>
                       Row_Ent (Upd, K, J) = Row_Ent (Old, K, J)));
      pragma Assert (Step (Old, Upd, 0, R, Tg, Src, Dst));
      Lemma_Step_Flat (Old, Upd, 0, R, Tg, Src, Dst);
      Lemma_Step_Tags (Old, Upd, 0, R, Tg, Src, Dst);
      Lemma_Row_Flat (Upd, 0, P);
      pragma Assert (Holds (Upd, R));
      Lemma_All_Flat (Old);
      for I in 1 .. Count (Old) loop
         if not Holds (Upd, Held (Old, I)) then
            pragma Assert (Row_Of (Old, I) = 0);
            pragma Assert (Dst (Pos_Of (Old, I)) = 0);
            pragma Assert (Held (Old, I) = Old.Data_E (Pos_Of (Old, I)).Hdr);
            pragma Assert (Dominates (R, Held (Old, I)));
         end if;
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              Holds (Upd, Held (Old, I2)) or else Dominates (R, Held (Old, I2)));
      end loop;
   end Lemma_Data_Flat;

   --  Insert E at P into the row (H, N): the records from P on move up by
   --  one.
   procedure Insert_Entry (H : in out Entry_Array; N : in out Data_Size; E : Entry_Rec; P : Positive)
   with
     Global => null,
     Pre  => H'First = 1 and then N < H'Last and then H'Last <= Data_Size'Last
             and then P <= N + 1,
     Post => N = N'Old + 1 and then H (P) = E
             and then (for all J in 1 .. P - 1 => H (J) = H'Old (J))
             and then (for all J in P + 1 .. N => H (J) = H'Old (J - 1))
   is
      H0 : constant Entry_Array := H with Ghost;
   begin
      for J in reverse P .. N loop
         pragma Loop_Invariant (for all K in 1 .. J => H (K) = H0 (K));
         pragma Loop_Invariant (for all K in J + 2 .. N + 1 => H (K) = H0 (K - 1));
         H (J + 1) := H (J);
      end loop;
      H (P) := E;
      N := N + 1;
   end Insert_Entry;

   --  Commit a data record (Apply_Data decided every refusal): drop what R
   --  beats (all in its entity run, at P or later) and hold R at P with
   --  its tag.
   --    * R beats only the record at P: R takes its place.
   --    * R beats no record: the records from P on move up by one.
   --    * Otherwise: compact from P on, then insert.
   procedure Commit_Data
     (S : in out State; R : Header; Tg : U64; Lo, Hi, P : Positive;
      Any_Drop, Other_Drop : Boolean)
   with
     Global => null,
     Pre  => Is_Frontier (S) and then Canonical (R)
             and then Is_Data (R) and then Admitted (S, R)
             and then not Holds (S, R)
             and then Lo <= P and then P <= Hi and then Hi <= S.ND + 1
             and then Run (S, R.Ent) = (First => Lo, Last => Hi - 1)
             and then (for all I in 1 .. S.ND =>
                         (if I < P then Key_Lt (S.Data_E (I).Hdr, R)
                          else not Key_Lt (S.Data_E (I).Hdr, R)))
             and then (for all I in 1 .. S.ND =>
                         S.Data_E (I).Hdr /= R and then not Dominates (S.Data_E (I).Hdr, R)
                         and then (if I < Lo or else I >= Hi
                                   then not Dominates (R, S.Data_E (I).Hdr)))
             and then Any_Drop
                      = (for some I in Lo .. Hi - 1 => Dominates (R, S.Data_E (I).Hdr))
             and then Other_Drop
                      = (for some I in Lo .. Hi - 1 =>
                           I /= P and then Dominates (R, S.Data_E (I).Hdr))
             and then (S.ND < S.Cap or else Any_Drop),
     Post => Is_Frontier (S)
       and then S.Fnd = S'Old.Fnd
       and then Holds (S, R)
       and then Max_Ceil (S) = Max_Ceil (S'Old)
       and then (for all I in 1 .. Count (S) =>
                   Holds (S'Old, Held (S, I)) or else Held (S, I) = R)
       and then (for all I in 1 .. Count (S'Old) =>
                   Holds (S, Held (S'Old, I)) or else Dominates (R, Held (S'Old, I)))
       and then (for all I in 1 .. Count (S) =>
                   (if Held (S, I) = R then Tag (S, I) = Tg
                    else Has_Tag (S'Old, Held (S, I), Tag (S, I))))
       and then Outside_Run (S'Old, S, R.Ent)
   is
      Old_S : constant State := S with Ghost;
      N     : constant Data_Size := S.ND;
      Cap   : constant Data_Size := S.Cap;
      Src   : Index_Map (1 .. Cap) := [others => 0] with Ghost;
      Dst   : Index_Map (1 .. Cap) := [others => 0] with Ghost;
   begin
      Lemma_Off_Mono (S);
      pragma Assert (Data_Count (S) = N and then N <= Cap);
      pragma Assert (Shape (Old_S) and then Auth_Shape (Old_S.A));
      pragma Assert (Slots_OK (Old_S.A, Old_S.Fnd) and then Data_OK (Old_S));
      pragma Assert (Data_Sorted (Old_S));
      pragma Assert (Auth_OK (Old_S.A));
      pragma Assert (Data_OK (S) and then Data_Sorted (S));
      pragma Assert
        (for all I in 1 .. N => Is_Data (S.Data_E (I).Hdr) and then Canonical (S.Data_E (I).Hdr));
      Lemma_No_Drop_Below (S.Data_E, N, R, P);
      --  What R beats lies in P .. Hi - 1 (AUDIT.md G25).
      pragma Assert
        (for all I in 1 .. N => (if Dominates (R, S.Data_E (I).Hdr) then I in P .. Hi - 1));

      if Any_Drop and then not Other_Drop then
         pragma Assert (P < Hi and then Dominates (R, S.Data_E (P).Hdr));
         pragma Assert
           (for all I in 1 .. N => (if I /= P then not Dominates (R, S.Data_E (I).Hdr)));
         S.Data_E (P) := (Hdr => R, Tag => Tg);
         Identity_Maps (Src, Dst, N);
         Src (P) := 0;
         Dst (P) := 0;
         pragma Assert (S.ND = N);
         pragma Assert
           (for all J in 1 .. N => (if J /= P then S.Data_E (J) = Old_S.Data_E (J)));
         pragma Assert
           (Shape (S) and then Slots_OK (S.A, S.Fnd) and then Auth_OK (S.A));
         pragma Assert
           (for all I in 1 .. N => Data_Item_OK (S, Old_S.Data_E (I).Hdr));
         pragma Assert (Data_Item_OK (S, R));
         pragma Assert (for all I in Hi .. N => Dst (I) = I + S.ND - N);
      else
         if Any_Drop then
            declare
               Kept    : Data_Size := P - 1;
               Dropped : Data_Size := 0;
            begin
               for I in P .. N loop
                  pragma Loop_Invariant (Kept + Dropped = I - 1 and then P - 1 <= Kept);
                  pragma Loop_Invariant (Dropped <= Integer'Min (I, Hi) - P);
                  pragma Loop_Invariant
                    ((Dropped > 0)
                     = (for some J in P .. I - 1 => Dominates (R, Old_S.Data_E (J).Hdr)));
                  pragma Loop_Invariant (S.ND = N);
                  pragma Loop_Invariant
                    (for all J in 1 .. P - 1 => S.Data_E (J) = Old_S.Data_E (J));
                  pragma Loop_Invariant
                    (for all J in I .. N => S.Data_E (J) = Old_S.Data_E (J));
                  pragma Loop_Invariant
                    (for all J in P .. Kept =>
                       Src (J) in P .. I - 1
                       and then S.Data_E (J) = Old_S.Data_E (Src (J))
                       and then not Dominates (R, Old_S.Data_E (Src (J)).Hdr));
                  pragma Loop_Invariant
                    (for all J in P .. Kept =>
                       (for all J2 in J + 1 .. Kept => Src (J) < Src (J2)));
                  pragma Loop_Invariant
                    (for all J in P .. I - 1 =>
                       (if Dominates (R, Old_S.Data_E (J).Hdr) then Dst (J) = 0
                        else Dst (J) in P .. Kept and then Src (Dst (J)) = J));
                  pragma Loop_Invariant
                    (for all J in Hi .. I - 1 => Dst (J) = J - Dropped);
                  if I < Hi and then Dominates (R, S.Data_E (I).Hdr) then
                     Dropped := Dropped + 1;
                     Dst (I) := 0;
                  else
                     Kept := Kept + 1;
                     S.Data_E (Kept) := S.Data_E (I);
                     Src (Kept) := I;
                     Dst (I) := Kept;
                  end if;
               end loop;
               pragma Assert (Dropped > 0 and then Kept < N);
               pragma Assert (Dropped <= Hi - P);
               pragma Assert (for all J in Hi .. N => Dst (J) = J - Dropped);
               S.ND := Kept;
               pragma Assert (for all J in Hi .. N => Dst (J) = J + S.ND - N);
            end;
            Identity_Maps (Src, Dst, P - 1);
            pragma Assert (for all J in Hi .. N => Dst (J) >= P);
         else
            pragma Assert (for all I in 1 .. N => not Dominates (R, S.Data_E (I).Hdr));
            Identity_Maps (Src, Dst, N);
            pragma Assert (for all J in Hi .. N => Dst (J) = J + S.ND - N);
         end if;
         pragma Assert (S.ND < S.Cap);
         pragma Assert (Mid_Row (Old_S.Data_E, N, S.Data_E, S.ND, R, P, Src, Dst));
         declare
            H1   : constant Entry_Array := S.Data_E with Ghost;
            N1   : constant Data_Size := S.ND with Ghost;
            Src1 : constant Index_Map := Src with Ghost;
            Dst1 : constant Index_Map := Dst with Ghost;
         begin
            pragma Assert (for all J in Hi .. N => Dst1 (J) = J + N1 - N and then Dst1 (J) >= P);
            pragma Assert (Mid_Row (Old_S.Data_E, N, H1, N1, R, P, Src1, Dst1));
            --  Insert R at P: the records from P on move up by one.
            Insert_Entry (S.Data_E, S.ND, (Hdr => R, Tag => Tg), P);
            pragma Assert (for all J in 1 .. P - 1 => S.Data_E (J) = H1 (J));
            pragma Assert (for all J in P + 1 .. S.ND => S.Data_E (J) = H1 (J - 1));
            Lemma_Insert_Maps
              (Old_S.Data_E, N, H1, N1, S.Data_E, S.ND, R, Tg, P, Hi, Src1, Dst1, Src, Dst);
            pragma Assert (for all J in Hi .. N => Dst (J) = J + S.ND - N);
         end;
      end if;
      pragma Assert (Kept_Row (Old_S.Data_E, N, S.Data_E, S.ND, R, Tg, P, Src, Dst));
      pragma Assert (for all J in Hi .. N => Dst (J) = J + S.ND - N);
      pragma Assert (for all J in 1 .. P - 1 => S.Data_E (J) = Old_S.Data_E (J));
      pragma Assert (S.Cap = Cap and then S.ND <= S.Cap and then Old_S.ND = N);
      pragma Assert (Same_Rows (Old_S.A, S.A));
      Lemma_Data_Frontier (Old_S, S, R, Tg, P, Src);
      pragma Assert (Is_Frontier (S));

      --  The run of R's entity (Outside_Run).
      Lemma_Commit_Run (Old_S, S, R, Tg, P, Src, Dst, Lo, Hi);

      Lemma_Data_Flat (Old_S, S, R, Tg, P, Src, Dst);
      pragma Assert (Outside_Run (Old_S, S, R.Ent));
   end Commit_Data;

   ---------------------------------------------------------------------
   --  Apply
   ---------------------------------------------------------------------

   --  Apply to the data row (R admitted).
   procedure Apply_Data (S : in out State; R : Header; Tg : U64; Result : out Status) with
     Global => null,
     Pre  => Is_Frontier (S) and then Canonical (R)
             and then Is_Data (R) and then Admitted (S, R),
     Post => Is_Frontier (S)
       and then S.Fnd = S'Old.Fnd
       and then Result in OK | Dominated | No_Space
       and then (Result = Dominated) = (not Holds (S'Old, R) and then Dom (S'Old, R))
       and then (Result = No_Space)
                = (not Holds (S'Old, R) and then not Dom (S'Old, R)
                   and then Data_Count (S'Old) = S.Cap
                   and then not Drops_Any (S'Old, R))
       and then (if Result /= OK or else Holds (S'Old, R) then Unchanged (S'Old, S))
       and then (if Result = OK then
                   Holds (S, R)
                   and then Max_Ceil (S) = Max_Ceil (S'Old)
                   and then (for all I in 1 .. Count (S) =>
                               Holds (S'Old, Held (S, I)) or else Held (S, I) = R)
                   and then (for all I in 1 .. Count (S'Old) =>
                               Holds (S, Held (S'Old, I))
                               or else Dominates (R, Held (S'Old, I))))
       and then (if Result = OK and then not Holds (S'Old, R) then
                   (for all I in 1 .. Count (S) =>
                      (if Held (S, I) = R then Tag (S, I) = Tg
                                    else Has_Tag (S'Old, Held (S, I), Tag (S, I))))
                   and then Outside_Run (S'Old, S, R.Ent))
   is
      Cap : constant Data_Size := S.Cap;
      N   : constant Data_Size := S.ND;
      RR  : constant Index_Range := Run (S, R.Ent);
      Lo  : constant Positive := RR.First;
      Hi  : constant Positive := RR.Last + 1;
      P   : Positive;
   begin
      Lemma_Classify (S, R);
      Lemma_Off_Mono (S);
      pragma Assert (Data_Count (S) = N and then N <= Cap);
      pragma Assert (Row_For (S, R) = 0 and then Has_Row (S, R));
      pragma Assert (Data_OK (S) and then Data_Sorted (S));

      --  One binary search: the run of R's entity, and R's place in it.
      --  Only the run can hold R, a dominator of R or a record that R
      --  dominates (AUDIT.md G25).
      pragma Assert (Lo <= Hi and then Hi <= N + 1);
      Find_Pos (S.Data_E, N, R, Lo, Hi, P);
      Lemma_Outside_Run_Row (S.Data_E, N, R, Lo, Hi);

      --  Duplicate, or beaten by a held record?
      for I in Lo .. Hi - 1 loop
         pragma Loop_Invariant
           (for all J in Lo .. I - 1 =>
              S.Data_E (J).Hdr /= R and then not Dominates (S.Data_E (J).Hdr, R));
         if S.Data_E (I).Hdr = R then
            pragma Assert (Row_At (S, 0, I) = R);
            pragma Assert (In_Row (S, 0, R));
            pragma Assert (Holds (S, R));
            Result := OK;
            return;
         end if;
         if Dominates (S.Data_E (I).Hdr, R) then
            pragma Assert (Row_At (S, 0, I) = S.Data_E (I).Hdr);
            pragma Assert (Dom_In_Row (S, 0, R));
            --  A held copy of R would also be dominated.
            pragma Assert
              (for all J in 1 .. N => not Dominates (S.Data_E (I).Hdr, S.Data_E (J).Hdr));
            pragma Assert (for all J in 1 .. N => S.Data_E (J).Hdr /= R);
            pragma Assert (not In_Row (S, 0, R));
            Result := Dominated;
            return;
         end if;
      end loop;
      pragma Assert
        (for all J in 1 .. N =>
           S.Data_E (J).Hdr /= R and then not Dominates (S.Data_E (J).Hdr, R));
      pragma Assert (not In_Row (S, 0, R));
      pragma Assert (not Dom_In_Row (S, 0, R));
      pragma Assert (not Holds (S, R));

      --  Room: decided before anything changes.
      declare
         Any_Drop   : Boolean := False;
         Other_Drop : Boolean := False;
      begin
         for I in Lo .. Hi - 1 loop
            pragma Loop_Invariant
              (Any_Drop = (for some J in Lo .. I - 1 => Dominates (R, S.Data_E (J).Hdr)));
            pragma Loop_Invariant
              (Other_Drop
               = (for some J in Lo .. I - 1 =>
                    J /= P and then Dominates (R, S.Data_E (J).Hdr)));
            if Dominates (R, S.Data_E (I).Hdr) then
               Any_Drop := True;
               if I /= P then
                  Other_Drop := True;
               end if;
            end if;
         end loop;
         pragma Assert
           (for all J in 1 .. N =>
              (if J < Lo or else J >= Hi then not Dominates (R, S.Data_E (J).Hdr)));
         pragma Assert (Any_Drop = Drops_In_Row (S, 0, R));
         if N = Cap and then not Any_Drop then
            Result := No_Space;
            return;
         end if;
         Commit_Data (S, R, Tg, Lo, Hi, P, Any_Drop, Other_Drop);
      end;
      Result := OK;
   end Apply_Data;

   --  The frontier invariant after an authorization commit, in a small
   --  context.
   procedure Lemma_Auth_Frontier
     (Old, Upd : State; R : Header; Tg : U64; K0 : Slot_Index; Fresh : Boolean;
      Src, Dst : Index_Map)
   with
     Ghost, Global => null,
     Pre  => Is_Frontier (Old) and then Canonical (R) and then Is_Auth (R)
             and then Upd.Cap = Old.Cap and then Upd.Fnd = Old.Fnd and then Upd.ND = Old.ND
             and then (for all I in 1 .. Data_Count (Old) => Upd.Data_E (I) = Old.Data_E (I))
             and then Auth_Step (Old.A, Upd.A, K0, R, Tg, Src, Dst)
             and then (for all K in Slot_Index =>
                         (if K /= K0 then Upd.A.NA (K) = Old.A.NA (K)
                                          and then Upd.A.Keys (K) = Old.A.Keys (K)))
             and then Upd.A.Keys (K0) = R.Issuer
             and then (if SC (Old.A, K0) > 0 then Old.A.Keys (K0) = R.Issuer)
             and then (if Fresh then
                         Old.A.NSlots < Signers_Max and then K0 = Old.A.NSlots + 1
                         and then Upd.A.NSlots = K0
                         and then (for all K in 1 .. Old.A.NSlots =>
                                     Old.A.Keys (K) /= Upd.A.Keys (K0))
                       else
                         K0 <= Old.A.NSlots and then Upd.A.NSlots = Old.A.NSlots
                         and then Upd.A.Keys (K0) = Old.A.Keys (K0))
             and then Offs_OK (Upd.A.NA, Upd.A.Offs, Upd.A.NAuth)
             and then (for all J in 1 .. SC (Old.A, K0) =>
                         Old.A.H (K0, J).Hdr /= R
                         and then not Dominates (Old.A.H (K0, J).Hdr, R))
             and then (for all J in 1 .. SC (Upd.A, K0) - 1 =>
                         not Dominates (R, Old.A.H (K0, Src (J)).Hdr))
             and then (for all J in 1 .. SC (Upd.A, K0) - 1 =>
                         (for all J2 in 1 .. SC (Upd.A, K0) - 1 =>
                            (if J /= J2 then Src (J) /= Src (J2)))),
     Post => Is_Frontier (Upd)
   is
   begin
      pragma Assert (Upd.A.NA (K0) >= 1);
      Lemma_Slots_Step (Old.A, Upd.A, Upd.Fnd, K0, Fresh);
      pragma Assert (Shape (Upd));
      pragma Assert (Data_Sorted (Old));
      Lemma_Data_OK_Auth (Old, Upd, K0, R, Tg, Src, Dst);
      Lemma_Auth_OK_Step (Old.A, Upd.A, K0, R, Tg, Src, Dst);
      pragma Assert (Is_Frontier (Upd));
   end Lemma_Auth_Frontier;

   --  Commit an authorization record to slot K0 (Fresh: a slot that this
   --  step assigns now). Drop what R beats in its own row, hold R with its
   --  tag and move the offsets. The caller decided all refusals before
   --  this.
   procedure Commit_Auth
     (S : in out State; R : Header; Tg : U64; K0 : Slot_Index; Fresh : Boolean)
   with
     Global => null,
     Pre  => Is_Frontier (S) and then Canonical (R)
             and then Is_Auth (R) and then not Holds (S, R)
             and then (if Fresh then
                         S.A.NSlots < Signers_Max and then K0 = S.A.NSlots + 1
                         and then (for all K in 1 .. S.A.NSlots => S.A.Keys (K) /= R.Issuer)
                       else
                         K0 <= S.A.NSlots and then S.A.Keys (K0) = R.Issuer)
             and then (for all J in 1 .. SC (S.A, K0) =>
                         S.A.H (K0, J).Hdr /= R and then not Dominates (S.A.H (K0, J).Hdr, R))
             and then (SC (S.A, K0) < Slice_Max
                       or else (for some J in 1 .. SC (S.A, K0) =>
                                  Dominates (R, S.A.H (K0, J).Hdr))),
     Post => Is_Frontier (S)
       and then S.Fnd = S'Old.Fnd
       and then Holds (S, R)
       and then Max_Ceil (S) = U48'Max (Max_Ceil (S'Old), Ceil_Of (R))
       and then (for all I in 1 .. Count (S) =>
                   Holds (S'Old, Held (S, I)) or else Held (S, I) = R)
       and then (for all I in 1 .. Count (S'Old) =>
                   Holds (S, Held (S'Old, I)) or else Dominates (R, Held (S'Old, I)))
       and then (for all I in 1 .. Count (S) =>
                   (if Held (S, I) = R then Tag (S, I) = Tg
                    else Has_Tag (S'Old, Held (S, I), Tag (S, I))))
       and then Outside_Slot (S'Old, S, R.Issuer)
   is
      Old_S   : constant State := S with Ghost;
      N       : constant Slice_Count := SC (S.A, K0);
      Kept    : Slice_Count := 0;
      Dropped : Slice_Count := 0;
      Src     : Index_Map (1 .. Slice_Max) := [others => 0] with Ghost;
      Dst     : Index_Map (1 .. Slice_Max) := [others => 0] with Ghost;
   begin
      Lemma_Off_Mono (S);
      pragma Assert (Shape (Old_S) and then Auth_Shape (Old_S.A));
      pragma Assert (Slots_OK (Old_S.A, Old_S.Fnd) and then Data_OK (Old_S));
      pragma Assert (Auth_OK (Old_S.A));
      pragma Assert (N = S.A.NA (K0));
      pragma Assert (if Fresh then N = 0);

      --  Drop what R beats in its own row and compact in place.
      for J in 1 .. N loop
         pragma Loop_Invariant (Kept + Dropped = J - 1);
         pragma Loop_Invariant
           ((Dropped > 0)
            = (for some J2 in 1 .. J - 1 => Dominates (R, Old_S.A.H (K0, J2).Hdr)));
         pragma Loop_Invariant
           (for all K in Slot_Index =>
              (if K /= K0 then
                 (for all J2 in 1 .. Slice_Max => S.A.H (K, J2) = Old_S.A.H (K, J2))));
         pragma Loop_Invariant
           (for all J2 in J .. N => S.A.H (K0, J2) = Old_S.A.H (K0, J2));
         pragma Loop_Invariant
           (for all J2 in 1 .. Kept =>
              Src (J2) in 1 .. J - 1
              and then S.A.H (K0, J2) = Old_S.A.H (K0, Src (J2))
              and then not Dominates (R, Old_S.A.H (K0, Src (J2)).Hdr));
         pragma Loop_Invariant
           (for all J2 in 1 .. Kept =>
              (for all J3 in 1 .. Kept => (if J2 < J3 then Src (J2) < Src (J3))));
         pragma Loop_Invariant
           (for all J2 in 1 .. J - 1 =>
              (if Dominates (R, Old_S.A.H (K0, J2).Hdr) then Dst (J2) = 0
               else Dst (J2) in 1 .. Kept
                    and then S.A.H (K0, Dst (J2)) = Old_S.A.H (K0, J2)));
         if not Dominates (R, S.A.H (K0, J).Hdr) then
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
      pragma Assert (if N = Slice_Max then Dropped > 0);
      pragma Assert (Kept < Slice_Max);
      Lemma_Dominates_Irrefl (R);
      pragma Assert
        (for all J in 1 .. Kept =>
           Src (J) in 1 .. N and then S.A.H (K0, J) = Old_S.A.H (K0, Src (J)));
      pragma Assert
        (for all J in 1 .. Kept =>
           (for all J2 in 1 .. Kept => (if J /= J2 then Src (J) /= Src (J2))));

      --  Hold R, and assign the slot if the signer is new.
      S.A.H (K0, Kept + 1) := (Hdr => R, Tag => Tg);
      Src (Kept + 1) := 0;
      S.A.NA (K0) := Kept + 1;
      if Fresh then
         S.A.NSlots := K0;
         S.A.Keys (K0) := R.Issuer;
      end if;

      --  The offsets of the slots after K0 move.
      Compute_Offs (S.A.NA, S.A.Offs, S.A.NAuth);

      --  Bridge: slot K0 is the kept records plus R. Nothing else moved.
      pragma Assert (Slot_Count (S, K0) = Kept + 1);
      pragma Assert (S.A.H (K0, Kept + 1) = (Hdr => R, Tag => Tg));
      pragma Assert
        (for all J in 1 .. Kept => S.A.H (K0, J) = Old_S.A.H (K0, Src (J)));
      pragma Assert
        (for all J in 1 .. N =>
           (if Dst (J) = 0 then Dominates (R, Old_S.A.H (K0, J).Hdr)
            else Dst (J) in 1 .. Kept
                 and then S.A.H (K0, Dst (J)) = Old_S.A.H (K0, J)));
      pragma Assert
        (for all K in Slot_Index =>
           (if K /= K0 then S.A.NA (K) = Old_S.A.NA (K) and then S.A.Keys (K) = Old_S.A.Keys (K)));
      pragma Assert (S.A.Keys (K0) = R.Issuer);

      pragma Assert (Auth_Step (Old_S.A, S.A, K0, R, Tg, Src, Dst));
      pragma Assert (SC (S.A, K0) = Kept + 1);
      pragma Assert
        (for all J in 1 .. SC (S.A, K0) - 1 => not Dominates (R, Old_S.A.H (K0, Src (J)).Hdr));
      pragma Assert
        (for all J in 1 .. SC (S.A, K0) - 1 =>
           (for all J2 in 1 .. SC (S.A, K0) - 1 => (if J /= J2 then Src (J) /= Src (J2))));
      Lemma_Auth_Frontier (Old_S, S, R, Tg, K0, Fresh, Src, Dst);
      pragma Assert (Is_Frontier (S));
      Lemma_Ceil_Step (Old_S.A, S.A, K0, R, Tg, Src, Dst);

      --  Outside_Slot: the slot of R's issuer is K0 (slot keys are
      --  distinct).
      pragma Assert (K0 <= S.A.NSlots and then S.A.Keys (K0) = R.Issuer);
      Lemma_Slot_Of_Key (S, K0);
      pragma Assert (Slot_Of (S, R.Issuer) = K0);
      if Fresh then
         pragma Assert (Slot_Of (Old_S, R.Issuer) = 0);
      else
         Lemma_Slot_Of_Key (Old_S, K0);
         pragma Assert (Slot_Of (Old_S, R.Issuer) = K0);
      end if;
      pragma Assert (Outside_Slot (Old_S, S, R.Issuer));

      pragma Assert (Step (Old_S, S, K0, R, Tg, Src, Dst));
      Lemma_Step_Flat (Old_S, S, K0, R, Tg, Src, Dst);
      Lemma_Step_Tags (Old_S, S, K0, R, Tg, Src, Dst);
      Lemma_Row_Flat (S, K0, Kept + 1);
      pragma Assert (Holds (S, R));
      Lemma_All_Flat (Old_S);
      pragma Assert
        (for all I in 1 .. Count (Old_S) =>
           Holds (S, Held (Old_S, I)) or else Dominates (R, Held (Old_S, I)));
   end Commit_Auth;

   --  Apply to the signer's slot (R is an authorization record).
   procedure Apply_Auth (S : in out State; R : Header; Tg : U64; Result : out Status) with
     Global => null,
     Pre  => Is_Frontier (S) and then Canonical (R) and then Is_Auth (R),
     Post => Is_Frontier (S)
       and then S.Fnd = S'Old.Fnd
       and then Result in OK | Dominated | Auth_Full
       and then (Result = Dominated) = (not Holds (S'Old, R) and then Dom (S'Old, R))
       and then (Result = Auth_Full)
                = (not Holds (S'Old, R) and then not Dom (S'Old, R)
                   and then
                     ((Slot_Of (S'Old, R.Issuer) /= 0
                       and then Slot_Count (S'Old, Slot_Of (S'Old, R.Issuer)) = Slice_Max
                       and then not Drops_Any (S'Old, R))
                      or else (Slot_Of (S'Old, R.Issuer) = 0
                               and then Slots_Used (S'Old) = Signers_Max)))
       and then (if Result /= OK or else Holds (S'Old, R) then Unchanged (S'Old, S))
       and then (if Result = OK then
                   Holds (S, R)
                   and then Max_Ceil (S) = U48'Max (Max_Ceil (S'Old), Ceil_Of (R))
                   and then (for all I in 1 .. Count (S) =>
                               Holds (S'Old, Held (S, I)) or else Held (S, I) = R)
                   and then (for all I in 1 .. Count (S'Old) =>
                               Holds (S, Held (S'Old, I))
                               or else Dominates (R, Held (S'Old, I))))
       and then (if Result = OK and then not Holds (S'Old, R) then
                   (for all I in 1 .. Count (S) =>
                      (if Held (S, I) = R then Tag (S, I) = Tg
                                    else Has_Tag (S'Old, Held (S, I), Tag (S, I))))
                   and then Outside_Slot (S'Old, S, R.Issuer))
   is
      Old_S : constant State := S with Ghost;
      K0    : Slot_Index;
      Fresh : Boolean;
      N     : Slice_Count;
   begin
      Lemma_Classify (S, R);
      Lemma_Off_Mono (S);
      pragma Assert (Shape (S) and then Slots_OK (S.A, S.Fnd) and then Auth_OK (S.A));
      pragma Assert (Shape (Old_S) and then Auth_Shape (Old_S.A));
      pragma Assert (Slots_OK (Old_S.A, Old_S.Fnd) and then Data_OK (Old_S));
      pragma Assert (Auth_OK (Old_S.A));

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
                 S.A.H (K0, J2).Hdr /= R and then not Dominates (S.A.H (K0, J2).Hdr, R));
            if S.A.H (K0, J).Hdr = R then
               pragma Assert (Row_At (S, K0, J) = R);
               pragma Assert (In_Row (S, K0, R));
               pragma Assert (Holds (S, R));
               Lemma_Max_Ceil_At (S.A, K0, J);
               pragma Assert (Ceil_Of (R) <= Max_Ceil (S));
               Result := OK;
               return;
            end if;
            if Dominates (S.A.H (K0, J).Hdr, R) then
               pragma Assert (Row_At (S, K0, J) = S.A.H (K0, J).Hdr);
               pragma Assert (Dom_In_Row (S, K0, R));
               pragma Assert
                 (for all J2 in 1 .. N =>
                    not Dominates (S.A.H (K0, J).Hdr, S.A.H (K0, J2).Hdr));
               pragma Assert (for all J2 in 1 .. N => S.A.H (K0, J2).Hdr /= R);
               pragma Assert (not In_Row (S, K0, R));
               Result := Dominated;
               return;
            end if;
         end loop;
         pragma Assert (not In_Row (S, K0, R));
         pragma Assert (not Dom_In_Row (S, K0, R));
         pragma Assert (Old_S.A.Keys (K0) = R.Issuer);
      end if;
      --  The same facts, about the state before a change.
      pragma Assert (N = SC (Old_S.A, K0));
      pragma Assert
        (for all J in 1 .. N =>
           Old_S.A.H (K0, J).Hdr /= R and then not Dominates (Old_S.A.H (K0, J).Hdr, R));
      pragma Assert (if N > 0 then Old_S.A.Keys (K0) = R.Issuer);
      pragma Assert (not Holds (S, R) and then not Dom (S, R));

      --  Room: decided before something changes.
      declare
         Any_Drop : Boolean := False;
      begin
         for J in 1 .. N loop
            pragma Loop_Invariant
              (Any_Drop = (for some J2 in 1 .. J - 1 => Dominates (R, S.A.H (K0, J2).Hdr)));
            if Dominates (R, S.A.H (K0, J).Hdr) then
               Any_Drop := True;
            end if;
         end loop;
         pragma Assert (if not Fresh then Any_Drop = Drops_In_Row (S, K0, R));
         if N = Slice_Max and then not Any_Drop then
            pragma Assert (not Fresh);
            Result := Auth_Full;
            return;
         end if;

         pragma Assert (N = SC (S.A, K0));
         Commit_Auth (S, R, Tg, K0, Fresh);
      end;
      Result := OK;
   end Apply_Auth;

   procedure Apply (S : in out State; R : Header; T : U64; Result : out Status) is
   begin
      if not Admitted (S, R) then
         Result := Inadmissible;
         return;
      end if;
      if Is_Data (R) then
         Apply_Data (S, R, T, Result);
      else
         Apply_Auth (S, R, T, Result);
      end if;
   end Apply;

   ---------------------------------------------------------------------
   --  Expiry
   ---------------------------------------------------------------------

   procedure Expire (S : in out State; Hz : U48) is
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
         pragma Loop_Invariant (for all J in I .. N => S.Data_E (J) = Old_S.Data_E (J));
         pragma Loop_Invariant
           (for all J in 1 .. Kept =>
              Src (J) in 1 .. I - 1
              and then S.Data_E (J) = Old_S.Data_E (Src (J))
              and then not Expired (Old_S.Data_E (Src (J)).Hdr, Hz));
         pragma Loop_Invariant
           (for all J in 1 .. Kept =>
              (for all J2 in 1 .. Kept => (if J < J2 then Src (J) < Src (J2))));
         pragma Loop_Invariant
           (for all J in 1 .. I - 1 =>
              (if Expired (Old_S.Data_E (J).Hdr, Hz) then Dst (J) = 0
               else Dst (J) in 1 .. Kept and then S.Data_E (Dst (J)) = Old_S.Data_E (J)));
         if not Expired (S.Data_E (I).Hdr, Hz) then
            Kept := Kept + 1;
            S.Data_E (Kept) := S.Data_E (I);
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
      pragma Assert (for all J in 1 .. Kept => S.Data_E (J) = Old_S.Data_E (Src (J)));
      pragma Assert (for all J in 1 .. Kept => Data_Item_OK (S, S.Data_E (J).Hdr));
      pragma Assert
        (for all J in 1 .. Kept =>
           (for all J2 in 1 .. Kept => not Dominates (S.Data_E (J2).Hdr, S.Data_E (J).Hdr)));
      pragma Assert
        (for all J in 1 .. Kept =>
           (for all J2 in 1 .. Kept => (if J /= J2 then S.Data_E (J).Hdr /= S.Data_E (J2).Hdr)));
      pragma Assert (Data_OK (S));
      --  A subsequence of the sorted row is sorted.
      pragma Assert (Sorted_Row (Old_S.Data_E, N));
      pragma Assert
        (for all J in 1 .. Kept =>
           (for all J2 in 1 .. Kept => (if J < J2 then Src (J) < Src (J2))));
      pragma Assert (for all J in 1 .. Kept => Src (J) in 1 .. N);
      Lemma_Sub_Sorted (Old_S.Data_E, N, S.Data_E, Kept, Src);
      pragma Assert (Data_Sorted (S));
      pragma Assert (Shape (S));
      pragma Assert (Slots_OK (S.A, S.Fnd));
      pragma Assert (Auth_OK (S.A));
      pragma Assert (Is_Frontier (S));

      --  In the terms of the contract.
      for J in 1 .. Kept loop
         Lemma_Held_Data (Old_S, Src (J));
         pragma Loop_Invariant
           (for all J2 in 1 .. J =>
              Held (Old_S, Src (J2)) = S.Data_E (J2).Hdr and then Holds (Old_S, S.Data_E (J2).Hdr)
              and then Tag (Old_S, Src (J2)) = S.Data_E (J2).Tag
              and then Has_Tag (Old_S, S.Data_E (J2).Hdr, S.Data_E (J2).Tag));
      end loop;
      for I in 1 .. N loop
         pragma Assert
           (if Dst (I) /= 0 then
              Dst (I) <= Count (S)
              and then Held (S, Dst (I)) = S.Data_E (Dst (I)).Hdr
              and then S.Data_E (Dst (I)) = Old_S.Data_E (I));
         pragma Assert
           (if not Expired (Old_S.Data_E (I).Hdr, Hz) then Holds (S, Old_S.Data_E (I).Hdr));
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              Expired (Old_S.Data_E (I2).Hdr, Hz) or else Holds (S, Old_S.Data_E (I2).Hdr));
      end loop;
   end Expire;

   ---------------------------------------------------------------------
   --  Set_Tag (SIMPLIFY.md S14)
   ---------------------------------------------------------------------

   --  A retag of the authorization rows keeps every data record admitted:
   --  the rows agree on every header (Lemma_Rows_Agree_Views, one author
   --  at a time).
   procedure Lemma_Retag_Data (Old, Upd : State) with
     Ghost, Global => null,
     Pre  => Is_Frontier (Old) and then Upd.Cap = Old.Cap and then Upd.ND = Old.ND
             and then Upd.Data_E = Old.Data_E
             and then Rows_Agree (Old.A, Upd.A),
     Post => (for all D in 1 .. Data_Count (Upd) => Data_Item_OK (Upd, Upd.Data_E (D).Hdr))
             and then Max_Ceil (Upd) = Max_Ceil (Old)
   is
      --  Proved; at run time the invariant would cost O(n^2) per call.
      pragma Assertion_Policy (Loop_Invariant => Ignore);
   begin
      Lemma_Rows_Agree_Views (Old.A, Upd.A, Zero_Key);
      for D in 1 .. Data_Count (Upd) loop
         pragma Assert (Data_Item_OK (Old, Old.Data_E (D).Hdr));
         Lemma_Rows_Agree_Views (Old.A, Upd.A, Old.Data_E (D).Hdr.V.Author);
         pragma Assert (Data_Item_OK (Upd, Upd.Data_E (D).Hdr));
         pragma Loop_Invariant
           (for all D2 in 1 .. D => Data_Item_OK (Upd, Upd.Data_E (D2).Hdr));
      end loop;
   end Lemma_Retag_Data;

   --  The flat view after a retag at row position (K, J) = flat index I.
   procedure Lemma_Retag_Flat (Old, Upd : State; I : Held_Index; T : U64) with
     Ghost, Global => null,
     Pre  => Shape (Old) and then Upd.Cap = Old.Cap and then Upd.ND = Old.ND
             and then Upd.A.NSlots = Old.A.NSlots and then Upd.A.NAuth = Old.A.NAuth
             and then Upd.A.NA = Old.A.NA and then Upd.A.Offs = Old.A.Offs
             and then I <= Count (Old)
             and then (for all D in 1 .. Data_Count (Old) =>
                         Upd.Data_E (D).Hdr = Old.Data_E (D).Hdr
                         and then Upd.Data_E (D).Tag
                                  = (if Row_Of (Old, I) = 0 and then D = Pos_Of (Old, I)
                                     then T else Old.Data_E (D).Tag))
             and then (for all K in Slot_Index =>
                         (for all J in 1 .. SC (Old.A, K) =>
                            Upd.A.H (K, J).Hdr = Old.A.H (K, J).Hdr
                            and then Upd.A.H (K, J).Tag
                                     = (if K = Row_Of (Old, I) and then J = Pos_Of (Old, I)
                                        then T else Old.A.H (K, J).Tag))),
     Post => Count (Upd) = Count (Old)
             and then (for all J in 1 .. Count (Upd) =>
                         Held (Upd, J) = Held (Old, J)
                         and then Tag (Upd, J) = (if J = I then T else Tag (Old, J)))
   is
      --  Proved; at run time the invariant would cost O(n^2) per call.
      pragma Assertion_Policy (Loop_Invariant => Ignore);
   begin
      Lemma_Flat_Row (Old, I);
      for J in 1 .. Count (Old) loop
         Lemma_Flat_Row (Old, J);
         pragma Assert (Row_Of (Upd, J) = Row_Of (Old, J));
         pragma Assert (Pos_Of (Upd, J) = Pos_Of (Old, J));
         pragma Assert
           (if Row_Of (Old, J) = Row_Of (Old, I) and then Pos_Of (Old, J) = Pos_Of (Old, I)
            then J = I);
         pragma Assert (Held (Upd, J) = Held (Old, J));
         pragma Assert (Tag (Upd, J) = (if J = I then T else Tag (Old, J)));
         pragma Loop_Invariant
           (for all J2 in 1 .. J =>
              Held (Upd, J2) = Held (Old, J2)
              and then Tag (Upd, J2) = (if J2 = I then T else Tag (Old, J2)));
      end loop;
   end Lemma_Retag_Flat;

   procedure Set_Tag (S : in out State; I : Held_Index; T : U64) is
      Old : constant State := S with Ghost;
      K   : constant Slot_Number := Row_Of (S, I);
      J   : constant Integer := Pos_Of (S, I);
   begin
      Lemma_Off_Mono (S);
      Lemma_Flat_Row (S, I);
      if K = 0 then
         S.Data_E (J).Tag := T;
         pragma Assert (S.A = Old.A);
         pragma Assert (Shape (S) and then Slots_OK (S.A, S.Fnd) and then Auth_OK (S.A));
         pragma Assert (for all D in 1 .. Data_Count (S) =>
                          S.Data_E (D).Hdr = Old.Data_E (D).Hdr);
         pragma Assert (Data_OK (S));
         pragma Assert (Data_Sorted (S));
         pragma Assert (Max_Ceil (S) = Max_Ceil (Old));
      else
         S.A.H (K, J).Tag := T;
         pragma Assert (S.Data_E = Old.Data_E);
         pragma Assert (Rows_Agree (Old.A, S.A));
         Lemma_Retag_Data (Old, S);
         pragma Assert (Shape (S) and then Slots_OK (S.A, S.Fnd) and then Auth_OK (S.A));
         pragma Assert (Data_OK (S));
         pragma Assert (Data_Sorted (S));
      end if;
      Lemma_Retag_Flat (Old, S, I, T);
      pragma Assert (Is_Frontier (S));
      pragma Assert (for all K2 in 1 .. Slots_Used (S) =>
                       (for all J2 in 1 .. Slot_Count (S, K2) =>
                          Auth_Held (S, K2, J2) = Auth_Held (Old, K2, J2)));
   end Set_Tag;

end Kome.Frontier;
