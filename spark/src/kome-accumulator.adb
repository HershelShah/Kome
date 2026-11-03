pragma Ada_2022;
package body Kome.Accumulator with SPARK_Mode is

   ----------------------------------------------------------------------
   --  Limb arithmetic is done in a range type wide enough for a + b + 1
   --  and a + 2^64 - b - 1, so the carry is an ordinary integer fact and
   --  not a bit-vector wraparound the prover would have to reconstruct.
   ----------------------------------------------------------------------

   Limb_Base : constant := 2**Limb_Bits;
   type Wide is range 0 .. 2 * Limb_Base;
   subtype Bit is Wide range 0 .. 1;

   subtype Byte_Index is Natural range 0 .. Acc_Bytes - 1;
   subtype Byte_Count is Natural range 0 .. Acc_Bytes;

   ----------------------------------------------------------------------
   --  Definitions of the ghost model.
   ----------------------------------------------------------------------

   package Wide_Conv is new Signed_Conversions (Wide);

   function To_Big (W : Wide) return Big_Integer is
     (Wide_Conv.To_Big_Integer (W))
     with Ghost;

   --  The integer value of one limb, 0 .. 2^64 - 1, and of one byte.
   function Limb_Value (X : U64) return Big_Integer is (To_Big (Wide (X)))
     with Ghost;

   function Byte_Value (X : Byte) return Big_Integer is (To_Big (Wide (X)))
     with Ghost;

   --  2^64 as a literal, so that limb bounds are linear facts.
   Base : constant Big_Integer := 18446744073709551616 with Ghost;

   --  Pow (N) = 2^(64·N).
   function Pow (N : Limb_Count) return Big_Integer is
     (if N = 0 then 1 else Pow (N - 1) * Base)
     with Ghost,
          Subprogram_Variant => (Decreases => N),
          Post => Pow'Result > 0;

   --  Suffix (A, K) = Σ_{K <= I < 64} A (I) · 2^(64·(I - K)), the value of
   --  limbs K .. 63 read as a number of their own, in Horner form:
   --  Suffix (A, K) = A (K) + 2^64 · Suffix (A, K + 1). Multiplying only by
   --  the literal 2^64 keeps every step of every proof linear.
   function Suffix (A : Acc; K : Limb_Count) return Big_Integer is
     (if K = Limbs then 0
      else Limb_Value (A (K)) + Base * Suffix (A, K + 1))
     with Ghost,
          Subprogram_Variant => (Increases => K);

   --  The same over bytes: Byte_Suffix (B, K) = B (K) + 256 ·
   --  Byte_Suffix (B, K + 1), the value of bytes K .. 511, little-endian.
   function Byte_Suffix (B : Acc_Byte_Array; K : Byte_Count)
                         return Big_Integer is
     (if K = Acc_Bytes then 0
      else Byte_Value (B (K)) + 256 * Byte_Suffix (B, K + 1))
     with Ghost,
          Subprogram_Variant => (Increases => K);

   ----------------------------------------------------------------------
   --  Completions of the public model functions. Being in the body, they
   --  are invisible to clients' provers.
   ----------------------------------------------------------------------

   function Value (A : Acc) return Big_Integer is (Suffix (A, 0));

   function Modulus return Big_Integer is (Pow (Limbs));

   function Bytes_Value (B : Acc_Byte_Array) return Big_Integer is
     (Byte_Suffix (B, 0));

   ----------------------------------------------------------------------
   --  Private proof helpers.
   ----------------------------------------------------------------------

   --  The carry (or borrow) into each limb, recorded by Add and Sub as
   --  they go: Cs (0) = 0, Cs (64) is the carry out that is discarded.
   type Carry_Array is array (Limb_Count) of Bit with Ghost;

   --  Base-2^64 digit uniqueness: X + 2^64·SX = Y + 2^64·SY with X and Y
   --  limbs forces X = Y and SX = SY.
   procedure Lemma_Digit (X, Y : U64; SX, SY : Big_Integer)
     with Ghost, Global => null,
          Pre  => Limb_Value (X) + Base * SX = Limb_Value (Y) + Base * SY,
          Post => X = Y and then SX = SY;

   procedure Lemma_Digit (X, Y : U64; SX, SY : Big_Integer) is
   begin
      pragma Assert (Limb_Value (X) >= 0 and then Limb_Value (X) < Base);
      pragma Assert (Limb_Value (Y) >= 0 and then Limb_Value (Y) < Base);
      if SX < SY then
         pragma Assert (Base * SY >= Base * SX + Base);
         pragma Assert (False);
      elsif SY < SX then
         pragma Assert (Base * SX >= Base * SY + Base);
         pragma Assert (False);
      end if;
      pragma Assert (SX = SY);
      pragma Assert (Limb_Value (X) = Limb_Value (Y));
      pragma Assert (Wide (X) = Wide (Y));
   end Lemma_Digit;

   --  The "mod" of Big_Integers on the two ranges Add and Sub produce.
   procedure Lemma_Mod_Add (S, M : Big_Integer)
     with Ghost, Global => null,
          Pre  => M > 0 and then S >= 0 and then S < 2 * M,
          Post => S mod M = (if S < M then S else S - M);

   procedure Lemma_Mod_Add (S, M : Big_Integer) is null;

   procedure Lemma_Mod_Sub (D, M : Big_Integer)
     with Ghost, Global => null,
          Pre  => M > 0 and then D >= -M and then D < M,
          Post => D mod M = (if D >= 0 then D else D + M);

   procedure Lemma_Mod_Sub (D, M : Big_Integer) is null;

   --  The carry chain of Add, limb by limb, sums to the integer identity
   --  Value (R) + carry_out · 2^4096 = Value (A) + Value (B). Induction
   --  from the top limb down over Suffix.
   procedure Lemma_Add_Chain (A, B, R : Acc; Cs : Carry_Array)
     with Ghost, Global => null,
          Pre  => Cs (0) = 0
            and then (for all J in Limb_Index =>
                        Wide (R (J)) + Limb_Base * Cs (J + 1)
                        = Wide (A (J)) + Wide (B (J)) + Cs (J)),
          Post => Value (R) + (if Cs (Limbs) = 1 then Modulus else 0)
                  = Value (A) + Value (B);

   procedure Lemma_Add_Chain (A, B, R : Acc; Cs : Carry_Array) is
      --  Proved; not re-executed under -gnata (only the Post is), so
      --  that Add and Sub stay cheap at run time (see the spec).
      pragma Assertion_Policy (Assert => Ignore, Loop_Invariant => Ignore);
   begin
      for K in reverse Limb_Index loop
         pragma Assert
           (Suffix (R, K + 1)
            + (if Cs (Limbs) = 1 then Pow (Limbs - (K + 1)) else 0)
            = Suffix (A, K + 1) + Suffix (B, K + 1) + To_Big (Cs (K + 1)));
         pragma Assert (Wide (R (K)) + Limb_Base * Cs (K + 1)
                        = Wide (A (K)) + Wide (B (K)) + Cs (K));
         pragma Assert (Limb_Value (R (K)) + Base * To_Big (Cs (K + 1))
                        = Limb_Value (A (K)) + Limb_Value (B (K))
                          + To_Big (Cs (K)));
         pragma Assert (Pow (Limbs - K) = Pow (Limbs - (K + 1)) * Base);
         pragma Loop_Invariant
           (Suffix (R, K) + (if Cs (Limbs) = 1 then Pow (Limbs - K) else 0)
            = Suffix (A, K) + Suffix (B, K) + To_Big (Cs (K)));
      end loop;
   end Lemma_Add_Chain;

   --  The borrow chain of Sub: Value (R) + Value (B)
   --  = Value (A) + borrow_out · 2^4096.
   procedure Lemma_Sub_Chain (A, B, R : Acc; Cs : Carry_Array)
     with Ghost, Global => null,
          Pre  => Cs (0) = 0
            and then (for all J in Limb_Index =>
                        Wide (R (J)) + Wide (B (J)) + Cs (J)
                        = Wide (A (J)) + Limb_Base * Cs (J + 1)),
          Post => Value (R) + Value (B)
                  = Value (A) + (if Cs (Limbs) = 1 then Modulus else 0);

   procedure Lemma_Sub_Chain (A, B, R : Acc; Cs : Carry_Array) is
      --  Proved; not re-executed under -gnata (only the Post is), so
      --  that Add and Sub stay cheap at run time (see the spec).
      pragma Assertion_Policy (Assert => Ignore, Loop_Invariant => Ignore);
   begin
      for K in reverse Limb_Index loop
         pragma Assert
           (Suffix (R, K + 1) + Suffix (B, K + 1) + To_Big (Cs (K + 1))
            = Suffix (A, K + 1)
              + (if Cs (Limbs) = 1 then Pow (Limbs - (K + 1)) else 0));
         pragma Assert (Wide (R (K)) + Wide (B (K)) + Cs (K)
                        = Wide (A (K)) + Limb_Base * Cs (K + 1));
         pragma Assert (Limb_Value (R (K)) + Limb_Value (B (K))
                        + To_Big (Cs (K))
                        = Limb_Value (A (K)) + Base * To_Big (Cs (K + 1)));
         pragma Assert (Pow (Limbs - K) = Pow (Limbs - (K + 1)) * Base);
         pragma Loop_Invariant
           (Suffix (R, K) + Suffix (B, K) + To_Big (Cs (K))
            = Suffix (A, K) + (if Cs (Limbs) = 1 then Pow (Limbs - K) else 0));
      end loop;
   end Lemma_Sub_Chain;

   ----------------------------------------------------------------------
   --  Add
   ----------------------------------------------------------------------

   function Add (A, B : Acc) return Acc is
      R  : Acc := Zero;
      C  : Bit := 0;
      Cs : Carry_Array := [others => 0] with Ghost;
   begin
      for I in Limb_Index loop
         declare
            S     : constant Wide := Wide (A (I)) + Wide (B (I)) + C;
            V     : U64;
            C_Old : constant Bit := C with Ghost;
         begin
            if S >= Limb_Base then
               V := U64 (S - Limb_Base);
               C := 1;
               pragma Assert (Wide (V) = S - Limb_Base);
            else
               V := U64 (S);
               C := 0;
               pragma Assert (Wide (V) = S);
            end if;
            pragma Assert (Wide (V) + Limb_Base * C
                           = Wide (A (I)) + Wide (B (I)) + C_Old);
            R (I) := V;
         end;
         Cs (I + 1) := C;
         pragma Loop_Invariant (Cs (0) = 0 and then C = Cs (I + 1));
         pragma Loop_Invariant
           (for all J in 0 .. I =>
              Wide (R (J)) + Limb_Base * Cs (J + 1)
              = Wide (A (J)) + Wide (B (J)) + Cs (J));
      end loop;

      Lemma_Add_Chain (A, B, R, Cs);
      Lemma_Value_Bounds (R);
      Lemma_Value_Bounds (A);
      Lemma_Value_Bounds (B);
      if C = 0 then
         pragma Assert (Value (R) = Value (A) + Value (B));
      else
         pragma Assert (Value (R) = Value (A) + Value (B) - Modulus);
      end if;
      pragma Assert (Value (R) = Wrap_Add (Value (A) + Value (B)));
      Lemma_Mod_Add (Value (A) + Value (B), Modulus);
      return R;
   end Add;

   ----------------------------------------------------------------------
   --  Sub
   ----------------------------------------------------------------------

   function Sub (A, B : Acc) return Acc is
      R  : Acc := Zero;
      C  : Bit := 0;   --  borrow
      Cs : Carry_Array := [others => 0] with Ghost;
   begin
      for I in Limb_Index loop
         declare
            --  Two steps, each obviously in range: D in 1 .. Limb_Base,
            --  then S in 0 .. 2 * Limb_Base - 1.
            D     : constant Wide := Limb_Base - Wide (B (I));
            S     : constant Wide := Wide (A (I)) + D - C;
            V     : U64;
            C_Old : constant Bit := C with Ghost;
         begin
            if S >= Limb_Base then
               V := U64 (S - Limb_Base);
               C := 0;
               pragma Assert (Wide (V) = S - Limb_Base);
            else
               V := U64 (S);
               C := 1;
               pragma Assert (Wide (V) = S);
            end if;
            pragma Assert (Wide (V) + Wide (B (I)) + C_Old
                           = Wide (A (I)) + Limb_Base * C);
            R (I) := V;
         end;
         Cs (I + 1) := C;
         pragma Loop_Invariant (Cs (0) = 0 and then C = Cs (I + 1));
         pragma Loop_Invariant
           (for all J in 0 .. I =>
              Wide (R (J)) + Wide (B (J)) + Cs (J)
              = Wide (A (J)) + Limb_Base * Cs (J + 1));
      end loop;

      Lemma_Sub_Chain (A, B, R, Cs);
      Lemma_Value_Bounds (R);
      Lemma_Value_Bounds (A);
      Lemma_Value_Bounds (B);
      if C = 0 then
         pragma Assert (Value (R) = Value (A) - Value (B));
      else
         pragma Assert (Value (R) = Value (A) - Value (B) + Modulus);
      end if;
      pragma Assert (Value (R) = Wrap_Sub (Value (A) - Value (B)));
      Lemma_Mod_Sub (Value (A) - Value (B), Modulus);
      return R;
   end Sub;

   ----------------------------------------------------------------------
   --  Wire form
   ----------------------------------------------------------------------

   function To_Bytes (A : Acc) return Acc_Byte_Array is
     ([for I in Acc_Byte_Array'Range => Byte_Of_U64 (A (I / 8), I mod 8)]);

   function From_Bytes (B : Acc_Byte_Array) return Acc is
     ([for L in Limb_Index => Read_U64LE (B, 8 * L)]);

   ----------------------------------------------------------------------
   --  Model facts
   ----------------------------------------------------------------------

   procedure Lemma_Value_Bounds (A : Acc) is
      --  Proved; at run time only the Post is evaluated.
      pragma Assertion_Policy (Assert => Ignore, Loop_Invariant => Ignore);
   begin
      --  0 <= Suffix (A, K) <= 2^(64·(64 - K)) - 1, from the top down.
      for K in reverse Limb_Index loop
         pragma Assert (Suffix (A, K + 1) >= 0
                        and then Suffix (A, K + 1) <= Pow (Limbs - (K + 1)) - 1);
         pragma Assert (Limb_Value (A (K)) >= 0
                        and then Limb_Value (A (K)) <= Base - 1);
         pragma Assert (Pow (Limbs - K) = Pow (Limbs - (K + 1)) * Base);
         pragma Assert (Base * Suffix (A, K + 1)
                        <= Base * Pow (Limbs - (K + 1)) - Base);
         pragma Loop_Invariant (Suffix (A, K) >= 0
                                and then Suffix (A, K) <= Pow (Limbs - K) - 1);
      end loop;
   end Lemma_Value_Bounds;

   procedure Lemma_Value_Injective (X, Y : Acc) is
   begin
      --  Peel limbs from the bottom: equal values have equal low limbs
      --  and equal quotients by 2^64, and so on up.
      for K in Limb_Index loop
         pragma Loop_Invariant (Suffix (X, K) = Suffix (Y, K));
         pragma Loop_Invariant (for all J in 0 .. K - 1 => X (J) = Y (J));
         Lemma_Digit (X (K), Y (K), Suffix (X, K + 1), Suffix (Y, K + 1));
      end loop;
      pragma Assert (for all J in Limb_Index => X (J) = Y (J));
   end Lemma_Value_Injective;

   procedure Lemma_Value_Zero is
   begin
      for K in reverse Limb_Index loop
         pragma Assert (Suffix (Zero, K + 1) = 0);
         pragma Assert (Limb_Value (Zero (K)) = 0);
         pragma Loop_Invariant (Suffix (Zero, K) = 0);
      end loop;
   end Lemma_Value_Zero;

   procedure Lemma_Value_Congruent (X, Y : Acc) is
   begin
      for K in reverse Limb_Index loop
         pragma Assert (Suffix (X, K + 1) = Suffix (Y, K + 1));
         pragma Assert (X (K) = Y (K));
         pragma Loop_Invariant (Suffix (X, K) = Suffix (Y, K));
      end loop;
   end Lemma_Value_Congruent;

   procedure Lemma_Eq_Iff_Value (A, B : Acc) is
   begin
      if A = B then
         Lemma_Value_Congruent (A, B);
      elsif Value (A) = Value (B) then
         Lemma_Value_Injective (A, B);
         pragma Assert (False);
      end if;
   end Lemma_Eq_Iff_Value;

   ----------------------------------------------------------------------
   --  Byte order as an integer fact
   ----------------------------------------------------------------------

   --  A limb is the little-endian number its eight bytes spell.
   procedure Lemma_Limb_Bytes (V : U64)
     with Ghost, Global => null,
          Post => Limb_Value (V)
            = Byte_Value (Byte_Of_U64 (V, 0)) + 256 *
              (Byte_Value (Byte_Of_U64 (V, 1)) + 256 *
              (Byte_Value (Byte_Of_U64 (V, 2)) + 256 *
              (Byte_Value (Byte_Of_U64 (V, 3)) + 256 *
              (Byte_Value (Byte_Of_U64 (V, 4)) + 256 *
              (Byte_Value (Byte_Of_U64 (V, 5)) + 256 *
              (Byte_Value (Byte_Of_U64 (V, 6)) + 256 *
               Byte_Value (Byte_Of_U64 (V, 7))))))));

   procedure Lemma_Limb_Bytes (V : U64) is
      --  The limb split into its eight byte lanes, then each lane is its
      --  byte times 256^K. Every step has a literal mask and shift, which
      --  is the form the SMT solvers' bit-vector-to-integer reasoning
      --  (bv2nat) handles; "mod 256" and "/ 256" on a 64-bit limb are not.
      B0 : constant Wide := Wide (Byte_Of_U64 (V, 0)) with Ghost;
      B1 : constant Wide := Wide (Byte_Of_U64 (V, 1)) with Ghost;
      B2 : constant Wide := Wide (Byte_Of_U64 (V, 2)) with Ghost;
      B3 : constant Wide := Wide (Byte_Of_U64 (V, 3)) with Ghost;
      B4 : constant Wide := Wide (Byte_Of_U64 (V, 4)) with Ghost;
      B5 : constant Wide := Wide (Byte_Of_U64 (V, 5)) with Ghost;
      B6 : constant Wide := Wide (Byte_Of_U64 (V, 6)) with Ghost;
      B7 : constant Wide := Wide (Byte_Of_U64 (V, 7)) with Ghost;
   begin
      pragma Assert
        (Wide (V)
         = Wide (V and 16#0000_0000_0000_00FF#)
           + Wide (V and 16#0000_0000_0000_FF00#)
           + Wide (V and 16#0000_0000_00FF_0000#)
           + Wide (V and 16#0000_0000_FF00_0000#)
           + Wide (V and 16#0000_00FF_0000_0000#)
           + Wide (V and 16#0000_FF00_0000_0000#)
           + Wide (V and 16#00FF_0000_0000_0000#)
           + Wide (V and 16#FF00_0000_0000_0000#));
      pragma Assert (Wide (V and 16#0000_0000_0000_00FF#) = B0);
      pragma Assert (Wide (V and 16#0000_0000_0000_FF00#) = 2**8 * B1);
      pragma Assert (Wide (V and 16#0000_0000_00FF_0000#) = 2**16 * B2);
      pragma Assert (Wide (V and 16#0000_0000_FF00_0000#) = 2**24 * B3);
      pragma Assert (Wide (V and 16#0000_00FF_0000_0000#) = 2**32 * B4);
      pragma Assert (Wide (V and 16#0000_FF00_0000_0000#) = 2**40 * B5);
      pragma Assert (Wide (V and 16#00FF_0000_0000_0000#) = 2**48 * B6);
      pragma Assert (Wide (V and 16#FF00_0000_0000_0000#) = 2**56 * B7);
      pragma Assert
        (Wide (V)
         = B0 + 256 * (B1 + 256 * (B2 + 256 * (B3 + 256 * (B4 + 256 *
           (B5 + 256 * (B6 + 256 * B7)))))));
   end Lemma_Limb_Bytes;

   --  Limb L read from bytes 8L .. 8L+7, in Horner form against the byte
   --  suffix: B (8L) + 256 · (... + 256 · B (8L + 7)) + 2^64 · rest.
   procedure Lemma_Limb_From_Bytes (B : Acc_Byte_Array; L : Limb_Index)
     with Ghost, Global => null,
          Post => Limb_Value (Read_U64LE (B, 8 * L))
                  + Base * Byte_Suffix (B, 8 * L + 8)
                  = Byte_Suffix (B, 8 * L);

   procedure Lemma_Limb_From_Bytes (B : Acc_Byte_Array; L : Limb_Index) is
      V : constant U64 := Read_U64LE (B, 8 * L) with Ghost;
      P : constant Byte_Index := 8 * L with Ghost;
   begin
      Lemma_Limb_Bytes (V);
      pragma Assert (for all I in U64_Index => Byte_Of_U64 (V, I) = B (P + I));
      pragma Assert (Byte_Suffix (B, P + 7)
                     = Byte_Value (B (P + 7)) + 256 * Byte_Suffix (B, P + 8));
      pragma Assert (Byte_Suffix (B, P + 6)
                     = Byte_Value (B (P + 6)) + 256 * Byte_Suffix (B, P + 7));
      pragma Assert (Byte_Suffix (B, P + 5)
                     = Byte_Value (B (P + 5)) + 256 * Byte_Suffix (B, P + 6));
      pragma Assert (Byte_Suffix (B, P + 4)
                     = Byte_Value (B (P + 4)) + 256 * Byte_Suffix (B, P + 5));
      pragma Assert (Byte_Suffix (B, P + 3)
                     = Byte_Value (B (P + 3)) + 256 * Byte_Suffix (B, P + 4));
      pragma Assert (Byte_Suffix (B, P + 2)
                     = Byte_Value (B (P + 2)) + 256 * Byte_Suffix (B, P + 3));
      pragma Assert (Byte_Suffix (B, P + 1)
                     = Byte_Value (B (P + 1)) + 256 * Byte_Suffix (B, P + 2));
      pragma Assert (Byte_Suffix (B, P)
                     = Byte_Value (B (P)) + 256 * Byte_Suffix (B, P + 1));
      pragma Assert (Limb_Value (V)
            = Byte_Value (B (P)) + 256 *
              (Byte_Value (B (P + 1)) + 256 *
              (Byte_Value (B (P + 2)) + 256 *
              (Byte_Value (B (P + 3)) + 256 *
              (Byte_Value (B (P + 4)) + 256 *
              (Byte_Value (B (P + 5)) + 256 *
              (Byte_Value (B (P + 6)) + 256 *
               Byte_Value (B (P + 7)))))))));
   end Lemma_Limb_From_Bytes;

   --  An accumulator whose limbs are read from B denotes B's integer.
   procedure Lemma_Limbs_Bytes (A : Acc; B : Acc_Byte_Array)
     with Ghost, Global => null,
          Pre  => (for all L in Limb_Index => A (L) = Read_U64LE (B, 8 * L)),
          Post => Value (A) = Bytes_Value (B);

   procedure Lemma_Limbs_Bytes (A : Acc; B : Acc_Byte_Array) is
      --  Proved; at run time only the Post is evaluated.
      pragma Assertion_Policy (Assert => Ignore, Loop_Invariant => Ignore);
   begin
      pragma Assert (Suffix (A, Limbs) = 0
                     and then Byte_Suffix (B, Acc_Bytes) = 0);
      for K in reverse Limb_Index loop
         pragma Assert (Suffix (A, K + 1) = Byte_Suffix (B, 8 * K + 8));
         Lemma_Limb_From_Bytes (B, K);
         pragma Assert (A (K) = Read_U64LE (B, 8 * K));
         pragma Assert (Suffix (A, K)
                        = Limb_Value (A (K)) + Base * Suffix (A, K + 1));
         pragma Loop_Invariant (Suffix (A, K) = Byte_Suffix (B, 8 * K));
      end loop;
   end Lemma_Limbs_Bytes;

   procedure Lemma_Value_From_Bytes (B : Acc_Byte_Array) is
   begin
      Lemma_Limbs_Bytes (From_Bytes (B), B);
   end Lemma_Value_From_Bytes;

   procedure Lemma_Value_To_Bytes (A : Acc) is
   begin
      Lemma_From_To_Bytes (A);
      pragma Assert (for all L in Limb_Index =>
                       A (L) = Read_U64LE (To_Bytes (A), 8 * L));
      Lemma_Limbs_Bytes (A, To_Bytes (A));
   end Lemma_Value_To_Bytes;

   ----------------------------------------------------------------------
   --  Laws
   ----------------------------------------------------------------------

   procedure Lemma_Add_Congruent (X1, X2, Y1, Y2 : Acc) is
   begin
      Lemma_Value_Congruent (X1, X2);
      Lemma_Value_Congruent (Y1, Y2);
      Lemma_Value_Injective (Add (X1, Y1), Add (X2, Y2));
   end Lemma_Add_Congruent;

   procedure Lemma_Sub_Congruent (X1, X2, Y1, Y2 : Acc) is
   begin
      Lemma_Value_Congruent (X1, X2);
      Lemma_Value_Congruent (Y1, Y2);
      Lemma_Value_Injective (Sub (X1, Y1), Sub (X2, Y2));
   end Lemma_Sub_Congruent;

   procedure Lemma_Add_Comm (A, B : Acc) is
   begin
      pragma Assert (Value (Add (A, B)) = Wrap_Add (Value (A) + Value (B)));
      pragma Assert (Value (Add (B, A)) = Wrap_Add (Value (B) + Value (A)));
      pragma Assert (Value (A) + Value (B) = Value (B) + Value (A));
      Lemma_Value_Injective (Add (A, B), Add (B, A));
   end Lemma_Add_Comm;

   procedure Lemma_Add_Assoc (A, B, C : Acc) is
      VA : constant Big_Integer := Value (A) with Ghost;
      VB : constant Big_Integer := Value (B) with Ghost;
      VC : constant Big_Integer := Value (C) with Ghost;
      M  : constant Big_Integer := Modulus with Ghost;
      AB : constant Acc := Add (A, B) with Ghost;
      BC : constant Acc := Add (B, C) with Ghost;
   begin
      Lemma_Value_Bounds (A);
      Lemma_Value_Bounds (B);
      Lemma_Value_Bounds (C);
      pragma Assert (Value (AB) = Wrap_Add (VA + VB));
      pragma Assert (Value (BC) = Wrap_Add (VB + VC));
      pragma Assert (Value (Add (AB, C)) = Wrap_Add (Value (AB) + VC));
      pragma Assert (Value (Add (A, BC)) = Wrap_Add (VA + Value (BC)));
      --  Both sides are VA + VB + VC reduced into [0, M).
      pragma Assert (Value (Add (AB, C))
                     = (if VA + VB + VC < M then VA + VB + VC
                        elsif VA + VB + VC < 2 * M then VA + VB + VC - M
                        else VA + VB + VC - 2 * M));
      pragma Assert (Value (Add (A, BC))
                     = (if VA + VB + VC < M then VA + VB + VC
                        elsif VA + VB + VC < 2 * M then VA + VB + VC - M
                        else VA + VB + VC - 2 * M));
      Lemma_Value_Injective (Add (AB, C), Add (A, BC));
   end Lemma_Add_Assoc;

   procedure Lemma_Add_Zero (A : Acc) is
   begin
      Lemma_Value_Zero;
      Lemma_Value_Bounds (A);
      pragma Assert (Value (Add (A, Zero)) = Wrap_Add (Value (A) + 0));
      pragma Assert (Value (Add (A, Zero)) = Value (A));
      Lemma_Value_Injective (Add (A, Zero), A);
      pragma Assert (Value (Add (Zero, A)) = Wrap_Add (0 + Value (A)));
      pragma Assert (Value (Add (Zero, A)) = Value (A));
      Lemma_Value_Injective (Add (Zero, A), A);
   end Lemma_Add_Zero;

   procedure Lemma_Sub_Add (A, B : Acc) is
      AB : constant Acc := Add (A, B) with Ghost;
   begin
      Lemma_Value_Bounds (A);
      Lemma_Value_Bounds (B);
      pragma Assert (Value (AB) = Wrap_Add (Value (A) + Value (B)));
      pragma Assert (Value (Sub (AB, B)) = Wrap_Sub (Value (AB) - Value (B)));
      pragma Assert (Value (Sub (AB, B)) = Value (A));
      Lemma_Value_Injective (Sub (AB, B), A);
   end Lemma_Sub_Add;

   procedure Lemma_Add_Sub (A, B : Acc) is
      D : constant Acc := Sub (A, B) with Ghost;
   begin
      Lemma_Value_Bounds (A);
      Lemma_Value_Bounds (B);
      pragma Assert (Value (D) = Wrap_Sub (Value (A) - Value (B)));
      pragma Assert (Value (Add (D, B)) = Wrap_Add (Value (D) + Value (B)));
      pragma Assert (Value (Add (D, B)) = Value (A));
      Lemma_Value_Injective (Add (D, B), A);
   end Lemma_Add_Sub;

   procedure Lemma_Sub_Self (A : Acc) is
   begin
      Lemma_Value_Zero;
      pragma Assert (Value (Sub (A, A)) = Wrap_Sub (Value (A) - Value (A)));
      pragma Assert (Value (Sub (A, A)) = Value (Zero));
      Lemma_Value_Injective (Sub (A, A), Zero);
   end Lemma_Sub_Self;

   procedure Lemma_From_To_Bytes (A : Acc) is
      T : constant Acc_Byte_Array := To_Bytes (A) with Ghost;
      F : constant Acc := From_Bytes (T) with Ghost;
   begin
      for L in Limb_Index loop
         pragma Assert (for all K in U64_Index =>
                          (8 * L + K) / 8 = L and then (8 * L + K) mod 8 = K);
         pragma Assert (for all K in U64_Index =>
                          T (8 * L + K) = Byte_Of_U64 (A (L), K));
         pragma Assert (T (8 * L .. 8 * L + 7) = To_LE_U64 (A (L)));
         Lemma_Read_Store_U64 (A (L));
         pragma Assert (Read_U64LE (T, 8 * L)
                        = Read_U64LE (To_LE_U64 (A (L)), 0));
         pragma Assert (F (L) = A (L));
         pragma Loop_Invariant (for all J in 0 .. L => F (J) = A (J));
      end loop;
   end Lemma_From_To_Bytes;

   procedure Lemma_To_From_Bytes (B : Acc_Byte_Array) is
      F : constant Acc := From_Bytes (B) with Ghost;
      T : constant Acc_Byte_Array := To_Bytes (F) with Ghost;
   begin
      for L in Limb_Index loop
         pragma Assert (F (L) = Read_U64LE (B, 8 * L));
         pragma Assert (for all I in 8 * L .. 8 * L + 7 =>
                          I / 8 = L and then I mod 8 = I - 8 * L);
         pragma Assert (for all I in 8 * L .. 8 * L + 7 =>
                          Byte_Of_U64 (F (L), I - 8 * L) = B (I));
         pragma Assert (for all I in 8 * L .. 8 * L + 7 => T (I) = B (I));
         pragma Loop_Invariant
           (for all I in 0 .. 8 * L + 7 => T (I) = B (I));
      end loop;
   end Lemma_To_From_Bytes;

end Kome.Accumulator;
