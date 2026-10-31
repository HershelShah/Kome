--  Kome.Frontier: one collection's replica state and its apply step
--  (DESIGN.md §3, §4; Frontier.lean `State`, `adm`, `keep`, `applyA`).
--
--  The state is the held records plus the grow-only registers
--  (Kome.Registers: the ceiling max-register and the writer set W). `Apply`
--  is the SPARK refinement of Frontier.lean `applyA`: raise the registers
--  from the record, then keep exactly the records that no admitted held
--  record dominates. The postcondition states that refinement; the Lean
--  theorem `convergence` then says two replicas that applied the same set,
--  in any order, with any duplication, present the same view.
--
--  One deliberate difference from the Lean model, recorded in DESIGN.md
--  §10 item 1: the model holds inadmissible records and filters them from
--  the view; this implementation refuses them (Status = Inadmissible) so the
--  held set is bounded. Both converge, because admission is monotone (T4')
--  and a refused record is re-offered by whichever peer holds it.
pragma Ada_2022;
with Kome.Headers;   use Kome.Headers;
with Kome.Registers; use Kome.Registers;
package Kome.Frontier with SPARK_Mode is

   --  Bound on the records one replica holds for one collection. DESIGN.md
   --  §7: live cells + young tombstones + 1 roster + revocations. The
   --  capacity is chosen when the state is created (a discriminant), so an
   --  embedded build and a test choose their own; exceeding it fails with
   --  No_Space and no change.
   Held_Max : constant := 2**20;
   subtype Held_Count is Natural range 0 .. Held_Max;
   subtype Held_Index is Natural range 1 .. Held_Max;

   type Header_Array is array (Held_Index range <>) of Header;

   --  The replica state. Private so that the invariant below is the only way
   --  to build one. Cap is the number of records it can hold.
   type State (Cap : Held_Count) is private;

   function Count (S : State) return Held_Count with
     Post => Count'Result <= S.Cap;
   function Held (S : State; I : Held_Index) return Header with
     Pre => I <= Count (S);
   function Regs (S : State) return Register_File;

   --  Admission (DESIGN.md §4; Frontier.lean `adm` plus the W register):
   --  a data record is admitted iff t <= maxceil and author ∈ W;
   --  authorization records always are.
   function Admitted (S : State; R : Header) return Boolean is
     (if Is_Data (R)
      then Data_T (R) <= Ceil (Regs (S)) and then In_W (Regs (S), Data_Author (R))
      else True);

   --  Frontier.lean `Dom` restricted to admitted held records.
   function Dom (S : State; X : Header) return Boolean is
     (for some I in 1 .. Count (S) =>
        Admitted (S, Held (S, I)) and then Dominates (Held (S, I), X));

   function Holds (S : State; X : Header) return Boolean is
     (for some I in 1 .. Count (S) => Held (S, I) = X);

   --  Invariants every State satisfies (Frontier.lean: the held set is its
   --  own frontier under admission, everything held is admitted, and it is
   --  a set: no record is held twice).
   function Is_Frontier (S : State) return Boolean is
     ((for all I in 1 .. Count (S) => Admitted (S, Held (S, I)))
      and then (for all I in 1 .. Count (S) => not Dom (S, Held (S, I)))
      and then (for all I in 1 .. Count (S) =>
                  (for all J in 1 .. Count (S) =>
                     (if I /= J then Held (S, I) /= Held (S, J)))));

   function Empty (NS : Id128; Cap : Held_Count) return State with
     Post => Empty'Result.Cap = Cap
             and then Count (Empty'Result) = 0
             and then Ceil (Regs (Empty'Result)) = 0
             and then Is_Frontier (Empty'Result);

   --  A roster's member keys arrive separately from the header because the
   --  header does not carry the boxes; the caller passes them after
   --  verifying the record (Kome.Records).
   type Member_Keys is array (Positive range <>) of Key256;

   --  Apply one record. Status says what happened: OK means R is held
   --  (newly, or already: a duplicate is a no-op and still OK, so that
   --  applying a set with repetitions is applying the set); Dominated means
   --  R is beaten by a held record and was not held; Inadmissible and
   --  No_Space change nothing but the registers a roster raises.
   procedure Apply
     (S       : in out State;
      R       : in     Header;
      Members : in     Member_Keys;
      Result  :    out Status)
   with
     Pre  => Is_Frontier (S)
             and then (if R.K /= K_Roster then Members'Length = 0)
             and then Members'Length <= Members_Max,
     Post => Is_Frontier (S)
       --  Registers only grow (T4').
       and then Ceil (Regs (S)) >= Ceil (Regs (S'Old))
       and then Extends (Regs (S'Old), Regs (S))
       --  Nothing held is new except R: every held record was held before
       --  or is R (Frontier.lean `keep`: a filter of held ++ [r]).
       and then (for all I in 1 .. Count (S) =>
                   Holds (S'Old, Held (S, I)) or else Held (S, I) = R)
       --  Nothing is lost except by domination: every record held before is
       --  still held or is dominated by an admitted held record now.
       and then (for all I in 1 .. Count (S'Old) =>
                   Holds (S, Held (S'Old, I)) or else Dom (S, Held (S'Old, I)))
       --  The record itself: held, or dominated, or refused unchanged.
       and then (case Result is
                   when OK           => Holds (S, R),
                   when Dominated    => Dom (S, R) and then not Holds (S, R),
                   when Inadmissible => not Admitted (S, R)
                                        and then Count (S) = Count (S'Old),
                   when No_Space     => Count (S) = Count (S'Old),
                   when others       => False);

private

   type State (Cap : Held_Count) is record
      NS : Id128;
      N  : Held_Count := 0;
      H  : Header_Array (1 .. Cap);
      RG : Register_File := Registers.Empty;
   end record
   with Dynamic_Predicate => State.N <= State.Cap;

   function Count (S : State) return Held_Count is (S.N);
   function Held (S : State; I : Held_Index) return Header is (S.H (I));
   function Regs (S : State) return Register_File is (S.RG);

end Kome.Frontier;
