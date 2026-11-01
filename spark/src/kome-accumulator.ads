--  Kome.Accumulator: the 4096-bit homomorphic set accumulator of DESIGN.md
--  §8, arithmetic only.
--
--    acc(e) := BLAKE2b-256("kome/acc" ‖ h(e) ‖ i) for i in 0..15,
--              concatenated, as an integer mod 2^4096
--    ACC(R) := Σ acc(e) mod 2^4096
--
--  This package is the "integer mod 2^4096" and its "+" (and "-", which
--  removes an element when a record is dropped from F). Hashing an element
--  to its acc(e) is Kome.Digest's job; so are the block prefix sums of §8
--  (one Acc per 64 elements), which are sums of Adds and need nothing more
--  from this package than Add, Sub and the laws below.
--
--  Byte order (a wire-format decision; DESIGN.md §8 leaves it implicit).
--  The 512-byte string is the LITTLE-ENDIAN encoding of the integer: byte 0
--  is the least significant, and the sixteen 32-byte BLAKE2b outputs of
--  acc(e) are concatenated in counter order, i = 0 lowest. This is the
--  order of the removed C++ engine ("a 256-bit little-endian integer",
--  src/reconcile.cpp), and fp hashes ACC(R) in this same order. It is not
--  only a comment: Lemma_Value_From_Bytes and Lemma_Value_To_Bytes below
--  prove Value (From_Bytes (B)) = Σ B (I) · 256^I, so Kome.Digest can state
--  acc(e) as an integer and get the order from a proved fact.
--
--  Representation: 64 limbs of 64 bits, limb 0 least significant; on the
--  wire limb L is bytes 8L .. 8L+7, little-endian.
--
--  Contracts are stated against a ghost mathematical model: Value (A) is
--  the integer Σ A (I) · 2^(64·I) as an unbounded Big_Integer, and Add and
--  Sub are proved to be (Value (A) ± Value (B)) mod 2^4096. Value, Modulus
--  and Bytes_Value are opaque to clients: they are declared here and
--  completed in the package body, together with everything they are
--  built from (the limb and byte Horner forms, the wide integer type the
--  carries are computed in). A private-part completion would not do: the
--  prover sees private-part expression functions from client units. Their
--  definitions are recursive over 64 limbs or 512 bytes, and a client's
--  prover should work from the Posts and lemmas below, not unfold them
--  (CONVENTIONS.md, rule 2). The model functions are recursive, bounded by
--  a Subprogram_Variant; the executable code has no recursion.
--
--  Run-time cost. The model is ghost code over
--  Ada.Numerics.Big_Numbers.Big_Integers (mathematical integers for
--  gnatprove). Under -gnata (every build of kome_spark.gpr) each Add and
--  Sub evaluates its Post and the Posts of the lemmas it calls, a dozen or
--  so 4096-bit Value computations: about 1 ms per Add (measured, 1000 Adds
--  in 1.0 s). The limb-by-limb proof steps inside those lemmas are proved
--  but not re-executed (their bodies set Assert and Loop_Invariant to
--  Ignore). A client test doing tens of thousands of Adds can still afford
--  this; one doing millions should build Kome.Accumulator without -gnata.
pragma Ada_2022;
with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;
with Kome.Byteorder; use Kome.Byteorder;
package Kome.Accumulator with SPARK_Mode is

   --  DESIGN.md §8: a 4096-bit sum, 512 bytes on the wire.
   Acc_Bits  : constant := 4096;
   Limb_Bits : constant := 64;
   Limbs     : constant := Acc_Bits / Limb_Bits;   --  64
   Acc_Bytes : constant := Acc_Bits / 8;           --  512

   subtype Limb_Index is Natural range 0 .. Limbs - 1;
   subtype Limb_Count is Natural range 0 .. Limbs;

   --  Limb I has weight 2^(64·I). Modular limbs: wrap is the intended
   --  semantics of an accumulator (CONVENTIONS.md, modular types for
   --  hashing), and every carry is accounted for in the contracts.
   type Acc is array (Limb_Index) of U64;

   subtype Acc_Byte_Array is Byte_Array (0 .. Acc_Bytes - 1);

   --  ACC(∅).
   Zero : constant Acc := [others => 0];

   ----------------------------------------------------------------------
   --  Ghost model (T6). Opaque: defined in the package body.
   ----------------------------------------------------------------------

   --  The integer an accumulator denotes, Σ A (I) · 2^(64·I).
   function Value (A : Acc) return Big_Integer
     with Ghost, Global => null;

   --  2^4096.
   function Modulus return Big_Integer
     with Ghost, Global => null,
          Post => Modulus'Result > 0;

   --  The integer a 512-byte string denotes, little-endian:
   --  Σ B (I) · 256^I.
   function Bytes_Value (B : Acc_Byte_Array) return Big_Integer
     with Ghost, Global => null;

   --  (S mod 2^4096) and (D mod 2^4096) on the ranges an addition or a
   --  subtraction of two reduced values produces, written without "mod"
   --  so that the lemmas below are linear case analyses.
   function Wrap_Add (S : Big_Integer) return Big_Integer is
     (if S < Modulus then S else S - Modulus)
     with Ghost;

   function Wrap_Sub (D : Big_Integer) return Big_Integer is
     (if D >= 0 then D else D + Modulus)
     with Ghost;

   ----------------------------------------------------------------------
   --  Arithmetic (T6: the "+" of ACC and its inverse).
   ----------------------------------------------------------------------

   --  A + B mod 2^4096, with the carry propagated through all 64 limbs
   --  and the final carry discarded.
   function Add (A, B : Acc) return Acc
     with Global => null,
          Post => Value (Add'Result) = (Value (A) + Value (B)) mod Modulus
            and then Value (Add'Result) = Wrap_Add (Value (A) + Value (B));

   --  A - B mod 2^4096 (removes B's element from the sum), with the borrow
   --  propagated through all 64 limbs and the final borrow discarded.
   function Sub (A, B : Acc) return Acc
     with Global => null,
          Post => Value (Sub'Result) = (Value (A) - Value (B)) mod Modulus
            and then Value (Sub'Result) = Wrap_Sub (Value (A) - Value (B));

   ----------------------------------------------------------------------
   --  Wire form: 512 bytes, limb L at bytes 8L .. 8L+7, little-endian.
   --  Lemma_Value_To_Bytes / Lemma_Value_From_Bytes give the integer
   --  meaning of these bytes.
   ----------------------------------------------------------------------

   function To_Bytes (A : Acc) return Acc_Byte_Array
     with Global => null,
          Post => (for all I in Acc_Byte_Array'Range =>
                     To_Bytes'Result (I) = Byte_Of_U64 (A (I / 8), I mod 8));

   function From_Bytes (B : Acc_Byte_Array) return Acc
     with Global => null,
          Post => (for all L in Limb_Index =>
                     From_Bytes'Result (L) = Read_U64LE (B, 8 * L));

   ----------------------------------------------------------------------
   --  Model facts.
   ----------------------------------------------------------------------

   --  Every accumulator denotes a reduced residue: 0 <= Value < 2^4096.
   procedure Lemma_Value_Bounds (A : Acc)
     with Ghost, Global => null,
          Post => Value (A) >= 0 and then Value (A) < Modulus;

   --  The model is faithful: two accumulators with the same value are the
   --  same accumulator. Every law below goes through this.
   procedure Lemma_Value_Injective (X, Y : Acc)
     with Ghost, Global => null,
          Pre  => Value (X) = Value (Y),
          Post => X = Y;

   procedure Lemma_Value_Zero
     with Ghost, Global => null,
          Post => Value (Zero) = 0;

   --  The converse of injectivity, for clients: Ada "=" on two Acc is
   --  element-wise, which the prover does not turn into equal Values by
   --  itself (CONVENTIONS.md, rule 1, for arrays).
   procedure Lemma_Value_Congruent (X, Y : Acc)
     with Ghost, Global => null,
          Pre  => X = Y,
          Post => Value (X) = Value (Y);

   --  The byte order, as an integer fact: the 512 bytes read as a
   --  little-endian number are the accumulator's value (DESIGN.md §8,
   --  "concatenated, as an integer").
   procedure Lemma_Value_From_Bytes (B : Acc_Byte_Array)
     with Ghost, Global => null,
          Post => Value (From_Bytes (B)) = Bytes_Value (B);

   procedure Lemma_Value_To_Bytes (A : Acc)
     with Ghost, Global => null,
          Post => Bytes_Value (To_Bytes (A)) = Value (A);

   ----------------------------------------------------------------------
   --  Laws: the facts from which T6 ("ACC(R₁ ⊎ R₂) = ACC(R₁) + ACC(R₂)")
   --  follows for a sum over a multiset. Add is a commutative monoid with
   --  unit Zero, so the sum does not depend on order or grouping; dropping
   --  a record is Sub, which undoes its Add. The homomorphism over a
   --  multiset itself is stated where multisets of elements exist
   --  (Kome.Digest), not here.
   ----------------------------------------------------------------------

   procedure Lemma_Add_Comm (A, B : Acc)
     with Ghost, Global => null,
          Post => Add (A, B) = Add (B, A);

   procedure Lemma_Add_Assoc (A, B, C : Acc)
     with Ghost, Global => null,
          Post => Add (Add (A, B), C) = Add (A, Add (B, C));

   procedure Lemma_Add_Zero (A : Acc)
     with Ghost, Global => null,
          Post => Add (A, Zero) = A and then Add (Zero, A) = A;

   --  Removing what was added gives back the sum before it.
   procedure Lemma_Sub_Add (A, B : Acc)
     with Ghost, Global => null,
          Post => Sub (Add (A, B), B) = A;

   --  And adding back what was removed restores the sum.
   procedure Lemma_Add_Sub (A, B : Acc)
     with Ghost, Global => null,
          Post => Add (Sub (A, B), B) = A;

   procedure Lemma_Sub_Self (A : Acc)
     with Ghost, Global => null,
          Post => Sub (A, A) = Zero;

   --  The wire form is a bijection.
   procedure Lemma_From_To_Bytes (A : Acc)
     with Ghost, Global => null,
          Post => From_Bytes (To_Bytes (A)) = A;

   procedure Lemma_To_From_Bytes (B : Acc_Byte_Array)
     with Ghost, Global => null,
          Post => To_Bytes (From_Bytes (B)) = B;

end Kome.Accumulator;
