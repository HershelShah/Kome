--  Body of Kome.SHA256. See the spec and FIPS 180-4.
pragma Ada_2022;
package body Kome.SHA256 with SPARK_Mode is

   --  Rotate intrinsic for U32 (GNAT RM "Shifts and Rotates"); the
   --  Shift_Right intrinsics are in the spec's private part.
   function Rotate_Right (Value : U32; Amount : Natural) return U32
     with Import, Convention => Intrinsic, Global => null;

   --  FIPS 180-4 §4.2.2 round constants.
   K : constant array (Natural range 0 .. 63) of U32 :=
     [16#428a2f98#, 16#71374491#, 16#b5c0fbcf#, 16#e9b5dba5#,
      16#3956c25b#, 16#59f111f1#, 16#923f82a4#, 16#ab1c5ed5#,
      16#d807aa98#, 16#12835b01#, 16#243185be#, 16#550c7dc3#,
      16#72be5d74#, 16#80deb1fe#, 16#9bdc06a7#, 16#c19bf174#,
      16#e49b69c1#, 16#efbe4786#, 16#0fc19dc6#, 16#240ca1cc#,
      16#2de92c6f#, 16#4a7484aa#, 16#5cb0a9dc#, 16#76f988da#,
      16#983e5152#, 16#a831c66d#, 16#b00327c8#, 16#bf597fc7#,
      16#c6e00bf3#, 16#d5a79147#, 16#06ca6351#, 16#14292967#,
      16#27b70a85#, 16#2e1b2138#, 16#4d2c6dfc#, 16#53380d13#,
      16#650a7354#, 16#766a0abb#, 16#81c2c92e#, 16#92722c85#,
      16#a2bfe8a1#, 16#a81a664b#, 16#c24b8b70#, 16#c76c51a3#,
      16#d192e819#, 16#d6990624#, 16#f40e3585#, 16#106aa070#,
      16#19a4c116#, 16#1e376c08#, 16#2748774c#, 16#34b0bcb5#,
      16#391c0cb3#, 16#4ed8aa4a#, 16#5b9cca4f#, 16#682e6ff3#,
      16#748f82ee#, 16#78a5636f#, 16#84c87814#, 16#8cc70208#,
      16#90befffa#, 16#a4506ceb#, 16#bef9a3f7#, 16#c67178f2#];

   ---------------------------------------------------------------------------
   --  Compress_Words: FIPS 180-4 §6.2.2 steps 1-4 after the big-endian load
   --  (which is Compressed, in the spec). All word arithmetic is modular
   --  U32, which is the addition modulo 2**32 the standard specifies.
   ---------------------------------------------------------------------------

   function Compress_Words (H : Hash_Words; M : Message_Words) return State_Words is
      type Schedule is array (Natural range 0 .. 63) of U32;
      W : Schedule :=
        [M.M0, M.M1, M.M2, M.M3, M.M4, M.M5, M.M6, M.M7,
         M.M8, M.M9, M.M10, M.M11, M.M12, M.M13, M.M14, M.M15,
         others => 0];
      A : U32 := H.H0;
      B : U32 := H.H1;
      C : U32 := H.H2;
      D : U32 := H.H3;
      E : U32 := H.H4;
      F : U32 := H.H5;
      G : U32 := H.H6;
      HH : U32 := H.H7;
      S0, S1, Ch, Maj, T1, T2 : U32;
   begin
      for I in 16 .. 63 loop
         S0 := Rotate_Right (W (I - 15), 7) xor Rotate_Right (W (I - 15), 18)
           xor Shift_Right (W (I - 15), 3);
         S1 := Rotate_Right (W (I - 2), 17) xor Rotate_Right (W (I - 2), 19)
           xor Shift_Right (W (I - 2), 10);
         W (I) := W (I - 16) + S0 + W (I - 7) + S1;
      end loop;
      for I in 0 .. 63 loop
         S1  := Rotate_Right (E, 6) xor Rotate_Right (E, 11) xor Rotate_Right (E, 25);
         Ch  := (E and F) xor ((not E) and G);
         T1  := HH + S1 + Ch + K (I) + W (I);
         S0  := Rotate_Right (A, 2) xor Rotate_Right (A, 13) xor Rotate_Right (A, 22);
         Maj := (A and B) xor (A and C) xor (B and C);
         T2  := S0 + Maj;
         HH := G; G := F; F := E; E := D + T1;
         D := C; C := B; B := A; A := T1 + T2;
      end loop;
      return [H.H0 + A, H.H1 + B, H.H2 + C, H.H3 + D,
              H.H4 + E, H.H5 + F, H.H6 + G, H.H7 + HH];
   end Compress_Words;

   ---------------------------------------------------------------------------
   --  The counter and its U64 image.
   ---------------------------------------------------------------------------

   --  U64 (X), for an integer X, reaches the solvers as their native
   --  int2bv, and the bit-vector drivers of cvc5 and z3 drop the why3 axioms
   --  that relate it to bvadd: neither solver proves U64 (X + Y) =
   --  U64 (X) + U64 (Y) outright, even for 8-bit operands. They do prove,
   --  for a single constant K, that bit K of U64 (N) is (N / 2**K) mod 2,
   --  and that U64 (N) mod 2 = U64 (N mod 2). The lemmas below build the
   --  addition law from those facts alone:
   --
   --  * Lemma_Half_Bit_K (K = 0 .. 60): bit K of U64 (N / 2) is bit K + 1
   --    of U64 (N); one lemma per bit, because each needs its own constant
   --    2**K (the solvers do not case-split a symbolic exponent);
   --  * Lemma_U64_Half: so U64 (N) / 2 = U64 (N / 2) (bit-vector
   --    extensionality over the 62 bits a Byte_Total can have);
   --  * Lemma_U64_Split: U64 (N) = 2 * U64 (N / 2) + U64 (N mod 2);
   --  * Lemma_U64_Add_Carry: binary addition with carry, by induction on
   --    X + Y (the recursion halves both operands, so it is at most 62
   --    levels deep, also at run time under -gnata);
   --  * Lemma_U64_Add: the law, the carry-free case.
   --
   --  The lemmas are mechanical; Lemma_Half_Bit_0 .. 60 differ only in K.

   procedure Lemma_Half_Bit_0 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**0) /= 0) = ((U64 (N) and 2**1) /= 0);
   procedure Lemma_Half_Bit_0 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**0) /= 0) = (((N / 2) / 2**0) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**1) /= 0) = ((N / 2**1) mod 2 = 1));
      pragma Assert ((N / 2) / 2**0 = N / 2**1);
   end Lemma_Half_Bit_0;

   procedure Lemma_Half_Bit_1 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**1) /= 0) = ((U64 (N) and 2**2) /= 0);
   procedure Lemma_Half_Bit_1 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**1) /= 0) = (((N / 2) / 2**1) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**2) /= 0) = ((N / 2**2) mod 2 = 1));
      pragma Assert ((N / 2) / 2**1 = N / 2**2);
   end Lemma_Half_Bit_1;

   procedure Lemma_Half_Bit_2 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**2) /= 0) = ((U64 (N) and 2**3) /= 0);
   procedure Lemma_Half_Bit_2 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**2) /= 0) = (((N / 2) / 2**2) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**3) /= 0) = ((N / 2**3) mod 2 = 1));
      pragma Assert ((N / 2) / 2**2 = N / 2**3);
   end Lemma_Half_Bit_2;

   procedure Lemma_Half_Bit_3 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**3) /= 0) = ((U64 (N) and 2**4) /= 0);
   procedure Lemma_Half_Bit_3 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**3) /= 0) = (((N / 2) / 2**3) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**4) /= 0) = ((N / 2**4) mod 2 = 1));
      pragma Assert ((N / 2) / 2**3 = N / 2**4);
   end Lemma_Half_Bit_3;

   procedure Lemma_Half_Bit_4 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**4) /= 0) = ((U64 (N) and 2**5) /= 0);
   procedure Lemma_Half_Bit_4 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**4) /= 0) = (((N / 2) / 2**4) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**5) /= 0) = ((N / 2**5) mod 2 = 1));
      pragma Assert ((N / 2) / 2**4 = N / 2**5);
   end Lemma_Half_Bit_4;

   procedure Lemma_Half_Bit_5 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**5) /= 0) = ((U64 (N) and 2**6) /= 0);
   procedure Lemma_Half_Bit_5 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**5) /= 0) = (((N / 2) / 2**5) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**6) /= 0) = ((N / 2**6) mod 2 = 1));
      pragma Assert ((N / 2) / 2**5 = N / 2**6);
   end Lemma_Half_Bit_5;

   procedure Lemma_Half_Bit_6 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**6) /= 0) = ((U64 (N) and 2**7) /= 0);
   procedure Lemma_Half_Bit_6 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**6) /= 0) = (((N / 2) / 2**6) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**7) /= 0) = ((N / 2**7) mod 2 = 1));
      pragma Assert ((N / 2) / 2**6 = N / 2**7);
   end Lemma_Half_Bit_6;

   procedure Lemma_Half_Bit_7 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**7) /= 0) = ((U64 (N) and 2**8) /= 0);
   procedure Lemma_Half_Bit_7 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**7) /= 0) = (((N / 2) / 2**7) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**8) /= 0) = ((N / 2**8) mod 2 = 1));
      pragma Assert ((N / 2) / 2**7 = N / 2**8);
   end Lemma_Half_Bit_7;

   procedure Lemma_Half_Bit_8 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**8) /= 0) = ((U64 (N) and 2**9) /= 0);
   procedure Lemma_Half_Bit_8 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**8) /= 0) = (((N / 2) / 2**8) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**9) /= 0) = ((N / 2**9) mod 2 = 1));
      pragma Assert ((N / 2) / 2**8 = N / 2**9);
   end Lemma_Half_Bit_8;

   procedure Lemma_Half_Bit_9 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**9) /= 0) = ((U64 (N) and 2**10) /= 0);
   procedure Lemma_Half_Bit_9 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**9) /= 0) = (((N / 2) / 2**9) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**10) /= 0) = ((N / 2**10) mod 2 = 1));
      pragma Assert ((N / 2) / 2**9 = N / 2**10);
   end Lemma_Half_Bit_9;

   procedure Lemma_Half_Bit_10 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**10) /= 0) = ((U64 (N) and 2**11) /= 0);
   procedure Lemma_Half_Bit_10 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**10) /= 0) = (((N / 2) / 2**10) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**11) /= 0) = ((N / 2**11) mod 2 = 1));
      pragma Assert ((N / 2) / 2**10 = N / 2**11);
   end Lemma_Half_Bit_10;

   procedure Lemma_Half_Bit_11 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**11) /= 0) = ((U64 (N) and 2**12) /= 0);
   procedure Lemma_Half_Bit_11 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**11) /= 0) = (((N / 2) / 2**11) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**12) /= 0) = ((N / 2**12) mod 2 = 1));
      pragma Assert ((N / 2) / 2**11 = N / 2**12);
   end Lemma_Half_Bit_11;

   procedure Lemma_Half_Bit_12 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**12) /= 0) = ((U64 (N) and 2**13) /= 0);
   procedure Lemma_Half_Bit_12 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**12) /= 0) = (((N / 2) / 2**12) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**13) /= 0) = ((N / 2**13) mod 2 = 1));
      pragma Assert ((N / 2) / 2**12 = N / 2**13);
   end Lemma_Half_Bit_12;

   procedure Lemma_Half_Bit_13 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**13) /= 0) = ((U64 (N) and 2**14) /= 0);
   procedure Lemma_Half_Bit_13 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**13) /= 0) = (((N / 2) / 2**13) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**14) /= 0) = ((N / 2**14) mod 2 = 1));
      pragma Assert ((N / 2) / 2**13 = N / 2**14);
   end Lemma_Half_Bit_13;

   procedure Lemma_Half_Bit_14 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**14) /= 0) = ((U64 (N) and 2**15) /= 0);
   procedure Lemma_Half_Bit_14 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**14) /= 0) = (((N / 2) / 2**14) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**15) /= 0) = ((N / 2**15) mod 2 = 1));
      pragma Assert ((N / 2) / 2**14 = N / 2**15);
   end Lemma_Half_Bit_14;

   procedure Lemma_Half_Bit_15 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**15) /= 0) = ((U64 (N) and 2**16) /= 0);
   procedure Lemma_Half_Bit_15 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**15) /= 0) = (((N / 2) / 2**15) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**16) /= 0) = ((N / 2**16) mod 2 = 1));
      pragma Assert ((N / 2) / 2**15 = N / 2**16);
   end Lemma_Half_Bit_15;

   procedure Lemma_Half_Bit_16 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**16) /= 0) = ((U64 (N) and 2**17) /= 0);
   procedure Lemma_Half_Bit_16 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**16) /= 0) = (((N / 2) / 2**16) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**17) /= 0) = ((N / 2**17) mod 2 = 1));
      pragma Assert ((N / 2) / 2**16 = N / 2**17);
   end Lemma_Half_Bit_16;

   procedure Lemma_Half_Bit_17 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**17) /= 0) = ((U64 (N) and 2**18) /= 0);
   procedure Lemma_Half_Bit_17 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**17) /= 0) = (((N / 2) / 2**17) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**18) /= 0) = ((N / 2**18) mod 2 = 1));
      pragma Assert ((N / 2) / 2**17 = N / 2**18);
   end Lemma_Half_Bit_17;

   procedure Lemma_Half_Bit_18 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**18) /= 0) = ((U64 (N) and 2**19) /= 0);
   procedure Lemma_Half_Bit_18 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**18) /= 0) = (((N / 2) / 2**18) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**19) /= 0) = ((N / 2**19) mod 2 = 1));
      pragma Assert ((N / 2) / 2**18 = N / 2**19);
   end Lemma_Half_Bit_18;

   procedure Lemma_Half_Bit_19 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**19) /= 0) = ((U64 (N) and 2**20) /= 0);
   procedure Lemma_Half_Bit_19 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**19) /= 0) = (((N / 2) / 2**19) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**20) /= 0) = ((N / 2**20) mod 2 = 1));
      pragma Assert ((N / 2) / 2**19 = N / 2**20);
   end Lemma_Half_Bit_19;

   procedure Lemma_Half_Bit_20 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**20) /= 0) = ((U64 (N) and 2**21) /= 0);
   procedure Lemma_Half_Bit_20 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**20) /= 0) = (((N / 2) / 2**20) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**21) /= 0) = ((N / 2**21) mod 2 = 1));
      pragma Assert ((N / 2) / 2**20 = N / 2**21);
   end Lemma_Half_Bit_20;

   procedure Lemma_Half_Bit_21 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**21) /= 0) = ((U64 (N) and 2**22) /= 0);
   procedure Lemma_Half_Bit_21 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**21) /= 0) = (((N / 2) / 2**21) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**22) /= 0) = ((N / 2**22) mod 2 = 1));
      pragma Assert ((N / 2) / 2**21 = N / 2**22);
   end Lemma_Half_Bit_21;

   procedure Lemma_Half_Bit_22 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**22) /= 0) = ((U64 (N) and 2**23) /= 0);
   procedure Lemma_Half_Bit_22 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**22) /= 0) = (((N / 2) / 2**22) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**23) /= 0) = ((N / 2**23) mod 2 = 1));
      pragma Assert ((N / 2) / 2**22 = N / 2**23);
   end Lemma_Half_Bit_22;

   procedure Lemma_Half_Bit_23 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**23) /= 0) = ((U64 (N) and 2**24) /= 0);
   procedure Lemma_Half_Bit_23 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**23) /= 0) = (((N / 2) / 2**23) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**24) /= 0) = ((N / 2**24) mod 2 = 1));
      pragma Assert ((N / 2) / 2**23 = N / 2**24);
   end Lemma_Half_Bit_23;

   procedure Lemma_Half_Bit_24 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**24) /= 0) = ((U64 (N) and 2**25) /= 0);
   procedure Lemma_Half_Bit_24 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**24) /= 0) = (((N / 2) / 2**24) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**25) /= 0) = ((N / 2**25) mod 2 = 1));
      pragma Assert ((N / 2) / 2**24 = N / 2**25);
   end Lemma_Half_Bit_24;

   procedure Lemma_Half_Bit_25 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**25) /= 0) = ((U64 (N) and 2**26) /= 0);
   procedure Lemma_Half_Bit_25 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**25) /= 0) = (((N / 2) / 2**25) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**26) /= 0) = ((N / 2**26) mod 2 = 1));
      pragma Assert ((N / 2) / 2**25 = N / 2**26);
   end Lemma_Half_Bit_25;

   procedure Lemma_Half_Bit_26 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**26) /= 0) = ((U64 (N) and 2**27) /= 0);
   procedure Lemma_Half_Bit_26 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**26) /= 0) = (((N / 2) / 2**26) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**27) /= 0) = ((N / 2**27) mod 2 = 1));
      pragma Assert ((N / 2) / 2**26 = N / 2**27);
   end Lemma_Half_Bit_26;

   procedure Lemma_Half_Bit_27 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**27) /= 0) = ((U64 (N) and 2**28) /= 0);
   procedure Lemma_Half_Bit_27 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**27) /= 0) = (((N / 2) / 2**27) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**28) /= 0) = ((N / 2**28) mod 2 = 1));
      pragma Assert ((N / 2) / 2**27 = N / 2**28);
   end Lemma_Half_Bit_27;

   procedure Lemma_Half_Bit_28 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**28) /= 0) = ((U64 (N) and 2**29) /= 0);
   procedure Lemma_Half_Bit_28 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**28) /= 0) = (((N / 2) / 2**28) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**29) /= 0) = ((N / 2**29) mod 2 = 1));
      pragma Assert ((N / 2) / 2**28 = N / 2**29);
   end Lemma_Half_Bit_28;

   procedure Lemma_Half_Bit_29 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**29) /= 0) = ((U64 (N) and 2**30) /= 0);
   procedure Lemma_Half_Bit_29 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**29) /= 0) = (((N / 2) / 2**29) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**30) /= 0) = ((N / 2**30) mod 2 = 1));
      pragma Assert ((N / 2) / 2**29 = N / 2**30);
   end Lemma_Half_Bit_29;

   procedure Lemma_Half_Bit_30 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**30) /= 0) = ((U64 (N) and 2**31) /= 0);
   procedure Lemma_Half_Bit_30 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**30) /= 0) = (((N / 2) / 2**30) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**31) /= 0) = ((N / 2**31) mod 2 = 1));
      pragma Assert ((N / 2) / 2**30 = N / 2**31);
   end Lemma_Half_Bit_30;

   procedure Lemma_Half_Bit_31 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**31) /= 0) = ((U64 (N) and 2**32) /= 0);
   procedure Lemma_Half_Bit_31 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**31) /= 0) = (((N / 2) / 2**31) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**32) /= 0) = ((N / 2**32) mod 2 = 1));
      pragma Assert ((N / 2) / 2**31 = N / 2**32);
   end Lemma_Half_Bit_31;

   procedure Lemma_Half_Bit_32 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**32) /= 0) = ((U64 (N) and 2**33) /= 0);
   procedure Lemma_Half_Bit_32 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**32) /= 0) = (((N / 2) / 2**32) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**33) /= 0) = ((N / 2**33) mod 2 = 1));
      pragma Assert ((N / 2) / 2**32 = N / 2**33);
   end Lemma_Half_Bit_32;

   procedure Lemma_Half_Bit_33 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**33) /= 0) = ((U64 (N) and 2**34) /= 0);
   procedure Lemma_Half_Bit_33 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**33) /= 0) = (((N / 2) / 2**33) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**34) /= 0) = ((N / 2**34) mod 2 = 1));
      pragma Assert ((N / 2) / 2**33 = N / 2**34);
   end Lemma_Half_Bit_33;

   procedure Lemma_Half_Bit_34 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**34) /= 0) = ((U64 (N) and 2**35) /= 0);
   procedure Lemma_Half_Bit_34 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**34) /= 0) = (((N / 2) / 2**34) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**35) /= 0) = ((N / 2**35) mod 2 = 1));
      pragma Assert ((N / 2) / 2**34 = N / 2**35);
   end Lemma_Half_Bit_34;

   procedure Lemma_Half_Bit_35 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**35) /= 0) = ((U64 (N) and 2**36) /= 0);
   procedure Lemma_Half_Bit_35 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**35) /= 0) = (((N / 2) / 2**35) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**36) /= 0) = ((N / 2**36) mod 2 = 1));
      pragma Assert ((N / 2) / 2**35 = N / 2**36);
   end Lemma_Half_Bit_35;

   procedure Lemma_Half_Bit_36 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**36) /= 0) = ((U64 (N) and 2**37) /= 0);
   procedure Lemma_Half_Bit_36 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**36) /= 0) = (((N / 2) / 2**36) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**37) /= 0) = ((N / 2**37) mod 2 = 1));
      pragma Assert ((N / 2) / 2**36 = N / 2**37);
   end Lemma_Half_Bit_36;

   procedure Lemma_Half_Bit_37 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**37) /= 0) = ((U64 (N) and 2**38) /= 0);
   procedure Lemma_Half_Bit_37 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**37) /= 0) = (((N / 2) / 2**37) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**38) /= 0) = ((N / 2**38) mod 2 = 1));
      pragma Assert ((N / 2) / 2**37 = N / 2**38);
   end Lemma_Half_Bit_37;

   procedure Lemma_Half_Bit_38 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**38) /= 0) = ((U64 (N) and 2**39) /= 0);
   procedure Lemma_Half_Bit_38 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**38) /= 0) = (((N / 2) / 2**38) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**39) /= 0) = ((N / 2**39) mod 2 = 1));
      pragma Assert ((N / 2) / 2**38 = N / 2**39);
   end Lemma_Half_Bit_38;

   procedure Lemma_Half_Bit_39 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**39) /= 0) = ((U64 (N) and 2**40) /= 0);
   procedure Lemma_Half_Bit_39 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**39) /= 0) = (((N / 2) / 2**39) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**40) /= 0) = ((N / 2**40) mod 2 = 1));
      pragma Assert ((N / 2) / 2**39 = N / 2**40);
   end Lemma_Half_Bit_39;

   procedure Lemma_Half_Bit_40 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**40) /= 0) = ((U64 (N) and 2**41) /= 0);
   procedure Lemma_Half_Bit_40 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**40) /= 0) = (((N / 2) / 2**40) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**41) /= 0) = ((N / 2**41) mod 2 = 1));
      pragma Assert ((N / 2) / 2**40 = N / 2**41);
   end Lemma_Half_Bit_40;

   procedure Lemma_Half_Bit_41 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**41) /= 0) = ((U64 (N) and 2**42) /= 0);
   procedure Lemma_Half_Bit_41 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**41) /= 0) = (((N / 2) / 2**41) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**42) /= 0) = ((N / 2**42) mod 2 = 1));
      pragma Assert ((N / 2) / 2**41 = N / 2**42);
   end Lemma_Half_Bit_41;

   procedure Lemma_Half_Bit_42 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**42) /= 0) = ((U64 (N) and 2**43) /= 0);
   procedure Lemma_Half_Bit_42 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**42) /= 0) = (((N / 2) / 2**42) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**43) /= 0) = ((N / 2**43) mod 2 = 1));
      pragma Assert ((N / 2) / 2**42 = N / 2**43);
   end Lemma_Half_Bit_42;

   procedure Lemma_Half_Bit_43 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**43) /= 0) = ((U64 (N) and 2**44) /= 0);
   procedure Lemma_Half_Bit_43 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**43) /= 0) = (((N / 2) / 2**43) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**44) /= 0) = ((N / 2**44) mod 2 = 1));
      pragma Assert ((N / 2) / 2**43 = N / 2**44);
   end Lemma_Half_Bit_43;

   procedure Lemma_Half_Bit_44 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**44) /= 0) = ((U64 (N) and 2**45) /= 0);
   procedure Lemma_Half_Bit_44 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**44) /= 0) = (((N / 2) / 2**44) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**45) /= 0) = ((N / 2**45) mod 2 = 1));
      pragma Assert ((N / 2) / 2**44 = N / 2**45);
   end Lemma_Half_Bit_44;

   procedure Lemma_Half_Bit_45 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**45) /= 0) = ((U64 (N) and 2**46) /= 0);
   procedure Lemma_Half_Bit_45 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**45) /= 0) = (((N / 2) / 2**45) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**46) /= 0) = ((N / 2**46) mod 2 = 1));
      pragma Assert ((N / 2) / 2**45 = N / 2**46);
   end Lemma_Half_Bit_45;

   procedure Lemma_Half_Bit_46 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**46) /= 0) = ((U64 (N) and 2**47) /= 0);
   procedure Lemma_Half_Bit_46 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**46) /= 0) = (((N / 2) / 2**46) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**47) /= 0) = ((N / 2**47) mod 2 = 1));
      pragma Assert ((N / 2) / 2**46 = N / 2**47);
   end Lemma_Half_Bit_46;

   procedure Lemma_Half_Bit_47 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**47) /= 0) = ((U64 (N) and 2**48) /= 0);
   procedure Lemma_Half_Bit_47 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**47) /= 0) = (((N / 2) / 2**47) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**48) /= 0) = ((N / 2**48) mod 2 = 1));
      pragma Assert ((N / 2) / 2**47 = N / 2**48);
   end Lemma_Half_Bit_47;

   procedure Lemma_Half_Bit_48 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**48) /= 0) = ((U64 (N) and 2**49) /= 0);
   procedure Lemma_Half_Bit_48 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**48) /= 0) = (((N / 2) / 2**48) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**49) /= 0) = ((N / 2**49) mod 2 = 1));
      pragma Assert ((N / 2) / 2**48 = N / 2**49);
   end Lemma_Half_Bit_48;

   procedure Lemma_Half_Bit_49 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**49) /= 0) = ((U64 (N) and 2**50) /= 0);
   procedure Lemma_Half_Bit_49 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**49) /= 0) = (((N / 2) / 2**49) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**50) /= 0) = ((N / 2**50) mod 2 = 1));
      pragma Assert ((N / 2) / 2**49 = N / 2**50);
   end Lemma_Half_Bit_49;

   procedure Lemma_Half_Bit_50 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**50) /= 0) = ((U64 (N) and 2**51) /= 0);
   procedure Lemma_Half_Bit_50 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**50) /= 0) = (((N / 2) / 2**50) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**51) /= 0) = ((N / 2**51) mod 2 = 1));
      pragma Assert ((N / 2) / 2**50 = N / 2**51);
   end Lemma_Half_Bit_50;

   procedure Lemma_Half_Bit_51 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**51) /= 0) = ((U64 (N) and 2**52) /= 0);
   procedure Lemma_Half_Bit_51 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**51) /= 0) = (((N / 2) / 2**51) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**52) /= 0) = ((N / 2**52) mod 2 = 1));
      pragma Assert ((N / 2) / 2**51 = N / 2**52);
   end Lemma_Half_Bit_51;

   procedure Lemma_Half_Bit_52 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**52) /= 0) = ((U64 (N) and 2**53) /= 0);
   procedure Lemma_Half_Bit_52 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**52) /= 0) = (((N / 2) / 2**52) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**53) /= 0) = ((N / 2**53) mod 2 = 1));
      pragma Assert ((N / 2) / 2**52 = N / 2**53);
   end Lemma_Half_Bit_52;

   procedure Lemma_Half_Bit_53 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**53) /= 0) = ((U64 (N) and 2**54) /= 0);
   procedure Lemma_Half_Bit_53 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**53) /= 0) = (((N / 2) / 2**53) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**54) /= 0) = ((N / 2**54) mod 2 = 1));
      pragma Assert ((N / 2) / 2**53 = N / 2**54);
   end Lemma_Half_Bit_53;

   procedure Lemma_Half_Bit_54 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**54) /= 0) = ((U64 (N) and 2**55) /= 0);
   procedure Lemma_Half_Bit_54 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**54) /= 0) = (((N / 2) / 2**54) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**55) /= 0) = ((N / 2**55) mod 2 = 1));
      pragma Assert ((N / 2) / 2**54 = N / 2**55);
   end Lemma_Half_Bit_54;

   procedure Lemma_Half_Bit_55 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**55) /= 0) = ((U64 (N) and 2**56) /= 0);
   procedure Lemma_Half_Bit_55 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**55) /= 0) = (((N / 2) / 2**55) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**56) /= 0) = ((N / 2**56) mod 2 = 1));
      pragma Assert ((N / 2) / 2**55 = N / 2**56);
   end Lemma_Half_Bit_55;

   procedure Lemma_Half_Bit_56 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**56) /= 0) = ((U64 (N) and 2**57) /= 0);
   procedure Lemma_Half_Bit_56 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**56) /= 0) = (((N / 2) / 2**56) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**57) /= 0) = ((N / 2**57) mod 2 = 1));
      pragma Assert ((N / 2) / 2**56 = N / 2**57);
   end Lemma_Half_Bit_56;

   procedure Lemma_Half_Bit_57 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**57) /= 0) = ((U64 (N) and 2**58) /= 0);
   procedure Lemma_Half_Bit_57 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**57) /= 0) = (((N / 2) / 2**57) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**58) /= 0) = ((N / 2**58) mod 2 = 1));
      pragma Assert ((N / 2) / 2**57 = N / 2**58);
   end Lemma_Half_Bit_57;

   procedure Lemma_Half_Bit_58 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**58) /= 0) = ((U64 (N) and 2**59) /= 0);
   procedure Lemma_Half_Bit_58 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**58) /= 0) = (((N / 2) / 2**58) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**59) /= 0) = ((N / 2**59) mod 2 = 1));
      pragma Assert ((N / 2) / 2**58 = N / 2**59);
   end Lemma_Half_Bit_58;

   procedure Lemma_Half_Bit_59 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**59) /= 0) = ((U64 (N) and 2**60) /= 0);
   procedure Lemma_Half_Bit_59 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**59) /= 0) = (((N / 2) / 2**59) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**60) /= 0) = ((N / 2**60) mod 2 = 1));
      pragma Assert ((N / 2) / 2**59 = N / 2**60);
   end Lemma_Half_Bit_59;

   procedure Lemma_Half_Bit_60 (N : Byte_Total)
     with Ghost, Global => null,
          Post => ((U64 (N / 2) and 2**60) /= 0) = ((U64 (N) and 2**61) /= 0);
   procedure Lemma_Half_Bit_60 (N : Byte_Total) is
   begin
      pragma Assert (((U64 (N / 2) and 2**60) /= 0) = (((N / 2) / 2**60) mod 2 = 1));
      pragma Assert (((U64 (N) and 2**61) /= 0) = ((N / 2**61) mod 2 = 1));
      pragma Assert ((N / 2) / 2**60 = N / 2**61);
   end Lemma_Half_Bit_60;

   --  U64 (N) < 2**62 (N <= Max_Total), so bits 61 .. 63 of U64 (N / 2) and
   --  62 .. 63 of U64 (N) are zero, and the 61 lemmas cover the rest.
   procedure Lemma_U64_Half (N : Byte_Total)
     with Ghost, Global => null,
          Post => U64 (N) / 2 = U64 (N / 2);

   procedure Lemma_U64_Half (N : Byte_Total) is
   begin
      Lemma_Half_Bit_0 (N);
      Lemma_Half_Bit_1 (N);
      Lemma_Half_Bit_2 (N);
      Lemma_Half_Bit_3 (N);
      Lemma_Half_Bit_4 (N);
      Lemma_Half_Bit_5 (N);
      Lemma_Half_Bit_6 (N);
      Lemma_Half_Bit_7 (N);
      Lemma_Half_Bit_8 (N);
      Lemma_Half_Bit_9 (N);
      Lemma_Half_Bit_10 (N);
      Lemma_Half_Bit_11 (N);
      Lemma_Half_Bit_12 (N);
      Lemma_Half_Bit_13 (N);
      Lemma_Half_Bit_14 (N);
      Lemma_Half_Bit_15 (N);
      Lemma_Half_Bit_16 (N);
      Lemma_Half_Bit_17 (N);
      Lemma_Half_Bit_18 (N);
      Lemma_Half_Bit_19 (N);
      Lemma_Half_Bit_20 (N);
      Lemma_Half_Bit_21 (N);
      Lemma_Half_Bit_22 (N);
      Lemma_Half_Bit_23 (N);
      Lemma_Half_Bit_24 (N);
      Lemma_Half_Bit_25 (N);
      Lemma_Half_Bit_26 (N);
      Lemma_Half_Bit_27 (N);
      Lemma_Half_Bit_28 (N);
      Lemma_Half_Bit_29 (N);
      Lemma_Half_Bit_30 (N);
      Lemma_Half_Bit_31 (N);
      Lemma_Half_Bit_32 (N);
      Lemma_Half_Bit_33 (N);
      Lemma_Half_Bit_34 (N);
      Lemma_Half_Bit_35 (N);
      Lemma_Half_Bit_36 (N);
      Lemma_Half_Bit_37 (N);
      Lemma_Half_Bit_38 (N);
      Lemma_Half_Bit_39 (N);
      Lemma_Half_Bit_40 (N);
      Lemma_Half_Bit_41 (N);
      Lemma_Half_Bit_42 (N);
      Lemma_Half_Bit_43 (N);
      Lemma_Half_Bit_44 (N);
      Lemma_Half_Bit_45 (N);
      Lemma_Half_Bit_46 (N);
      Lemma_Half_Bit_47 (N);
      Lemma_Half_Bit_48 (N);
      Lemma_Half_Bit_49 (N);
      Lemma_Half_Bit_50 (N);
      Lemma_Half_Bit_51 (N);
      Lemma_Half_Bit_52 (N);
      Lemma_Half_Bit_53 (N);
      Lemma_Half_Bit_54 (N);
      Lemma_Half_Bit_55 (N);
      Lemma_Half_Bit_56 (N);
      Lemma_Half_Bit_57 (N);
      Lemma_Half_Bit_58 (N);
      Lemma_Half_Bit_59 (N);
      Lemma_Half_Bit_60 (N);
      pragma Assert (U64 (N) < 2**62);
      pragma Assert (U64 (N / 2) < 2**61);
   end Lemma_U64_Half;

   procedure Lemma_U64_Split (N : Byte_Total)
     with Ghost, Global => null,
          Post => U64 (N) = 2 * U64 (N / 2) + U64 (N mod 2);

   procedure Lemma_U64_Split (N : Byte_Total) is
   begin
      Lemma_U64_Half (N);
      pragma Assert (U64 (N) mod 2 = U64 (N mod 2));
      pragma Assert (U64 (N) = 2 * (U64 (N) / 2) + U64 (N) mod 2);
   end Lemma_U64_Split;

   subtype Carry is Byte_Total range 0 .. 1;

   --  X + Y + C in binary: the low bits give the low bit of the sum and the
   --  carry C2, and the halves add with carry C2 (the recursive call).
   procedure Lemma_U64_Add_Carry (X, Y : Byte_Total; C : Carry)
     with Ghost, Global => null,
          Subprogram_Variant => (Decreases => X + Y),
          Pre    => Y <= Max_Total - X - C,
          Post   => U64 (X + Y + C) = U64 (X) + U64 (Y) + U64 (C);

   procedure Lemma_U64_Add_Carry (X, Y : Byte_Total; C : Carry) is
   begin
      if X = 0 and then Y = 0 then
         pragma Assert (U64 (X) = 0 and then U64 (Y) = 0);
      else
         declare
            A  : constant Carry      := X mod 2;
            B  : constant Carry      := Y mod 2;
            C2 : constant Carry      := (A + B + C) / 2;
            S  : constant Byte_Total := X + Y + C;
         begin
            pragma Assert (X / 2 + Y / 2 < X + Y);
            pragma Assert (S / 2 = X / 2 + Y / 2 + C2);
            pragma Assert (S mod 2 = A + B + C - 2 * C2);
            Lemma_U64_Add_Carry (X / 2, Y / 2, C2);
            Lemma_U64_Split (S);
            Lemma_U64_Split (X);
            Lemma_U64_Split (Y);
            pragma Assert (U64 (A) = (if A = 0 then 0 else 1));
            pragma Assert (U64 (B) = (if B = 0 then 0 else 1));
            pragma Assert (U64 (C) = (if C = 0 then 0 else 1));
            pragma Assert (U64 (C2) = (if C2 = 0 then 0 else 1));
            pragma Assert (U64 (S mod 2) = (if S mod 2 = 0 then 0 else 1));
            pragma Assert (2 * U64 (C2) + U64 (S mod 2)
                           = U64 (A) + U64 (B) + U64 (C));
         end;
      end if;
   end Lemma_U64_Add_Carry;

   --  The relation between integer addition on the counter and modular
   --  addition on its U64 image (neither side wraps: X + Y < 2**62).
   procedure Lemma_U64_Add (X, Y : Byte_Total)
     with Ghost,
          Global => null,
          Pre    => Y <= Max_Total - X,
          Post   => U64 (X + Y) = U64 (X) + U64 (Y);

   procedure Lemma_U64_Add (X, Y : Byte_Total) is
   begin
      Lemma_U64_Add_Carry (X, Y, 0);
   end Lemma_U64_Add;

   procedure Lemma_U64_Sub (X, Y : Byte_Total)
     with Ghost,
          Global => null,
          Pre    => Y <= X,
          Post   => U64 (X - Y) = U64 (X) - U64 (Y);

   procedure Lemma_U64_Sub (X, Y : Byte_Total) is
   begin
      Lemma_U64_Add (X - Y, Y);
      pragma Assert (U64 (X) = U64 (X - Y) + U64 (Y));
   end Lemma_U64_Sub;

   procedure Lemma_U64_Times_64 (Q : Byte_Total)
     with Ghost,
          Global => null,
          Pre    => Q <= Max_Total / Block_Len,
          Post   => U64 (Block_Len * Q) = Block_Len * U64 (Q);

   procedure Lemma_U64_Times_64 (Q : Byte_Total) is
   begin
      Lemma_U64_Add (Q, Q);
      pragma Assert (U64 (2 * Q) = 2 * U64 (Q));
      Lemma_U64_Add (2 * Q, 2 * Q);
      pragma Assert (U64 (4 * Q) = 4 * U64 (Q));
      Lemma_U64_Add (4 * Q, 4 * Q);
      pragma Assert (U64 (8 * Q) = 8 * U64 (Q));
      Lemma_U64_Add (8 * Q, 8 * Q);
      pragma Assert (U64 (16 * Q) = 16 * U64 (Q));
      Lemma_U64_Add (16 * Q, 16 * Q);
      pragma Assert (U64 (32 * Q) = 32 * U64 (Q));
      Lemma_U64_Add (32 * Q, 32 * Q);
      pragma Assert (U64 (64 * Q) = 64 * U64 (Q));
   end Lemma_U64_Times_64;

   --------------------
   -- Lemma_Mod_Step --
   --------------------

   --  The counter and the buffer fill stay in step: if B is T mod 64 and K
   --  more bytes fit in the buffer, the fill after them is (T + K) mod 64,
   --  which is 0 exactly when they complete the block.
   procedure Lemma_Mod_Step (T : Byte_Total; B, K : Natural)
     with Ghost,
          Global => null,
          Pre    => B = Natural (T mod Block_Len)
                    and then K <= Block_Len - B
                    and then Byte_Total (K) <= Max_Total - T,
          Post   => Natural ((T + Byte_Total (K)) mod Block_Len)
                    = (if B + K = Block_Len then 0 else B + K);

   procedure Lemma_Mod_Step (T : Byte_Total; B, K : Natural) is
      Q : constant Byte_Total := T / Block_Len;
   begin
      pragma Assert (T = Block_Len * Q + Byte_Total (B));
      pragma Assert (T + Byte_Total (K) = Block_Len * Q + Byte_Total (B + K));
      if B + K = Block_Len then
         pragma Assert (T + Byte_Total (K) = Block_Len * (Q + 1));
      else
         pragma Assert (B + K < Block_Len);
      end if;
   end Lemma_Mod_Step;

   ------------
   -- Absorb --
   ------------

   function Absorb (Ctx : Context; Data : Byte_Array) return Context is
      --  The invariant that ties each iteration to the model evaluates
      --  Absorbed over the unread suffix, which would make an executed
      --  Absorb quadratic in Data'Length. gnatprove analyses loop invariants
      --  whatever the assertion policy, so proof is unaffected; at run time
      --  the same equation is checked once, by the Post, and the cheap
      --  invariants are repeated as Asserts so -gnata still checks them
      --  every iteration.
      pragma Assertion_Policy (Loop_Invariant => Ignore);
      Len       : constant Natural := Data'Length;
      R         : Context := Ctx;
      Remaining : Natural := Len;
      Take      : Natural;
   begin
      while Remaining > 0 loop
         pragma Loop_Invariant (Remaining <= Len);
         pragma Loop_Invariant (R.Total = Ctx.Total + Byte_Total (Len - Remaining));
         pragma Loop_Invariant (R.Finished = Ctx.Finished);
         pragma Loop_Invariant (R.Buf_Len = Natural (R.Total mod Block_Len));
         --  The unread suffix is Data (Data'Last - (Remaining - 1) .. Data'Last).
         pragma Loop_Invariant
           (Absorbed (Ctx, Data)
            = Absorbed (R, Data (Data'Last - (Remaining - 1) .. Data'Last)));
         pragma Loop_Variant (Decreases => Remaining);
         pragma Assert (Remaining <= Len);
         pragma Assert (R.Total = Ctx.Total + Byte_Total (Len - Remaining));
         pragma Assert (R.Finished = Ctx.Finished);
         pragma Assert (R.Buf_Len = Natural (R.Total mod Block_Len));
         Take := Take_Len (R, Remaining);
         Lemma_Mod_Step (R.Total, R.Buf_Len, Take);
         --  One unfolding of Absorbed on the suffix: its first Take bytes.
         R := Fill (R, Data (Data'Last - (Remaining - 1)
                             .. Data'Last - (Remaining - Take)));
         Remaining := Remaining - Take;
      end loop;
      return R;
   end Absorb;

   --------------------
   -- Absorb_Message --
   --------------------

   function Absorb_Message (Ctx : Context; Data : Byte_Array) return Context is
      L : constant Byte_Total := Byte_Total (Data'Length);
   begin
      --  The U64 bound as a Byte_Total bound: Max - T in U64 is the image
      --  of Max - T, and the image preserves order.
      Lemma_U64_Sub (Max_Message, Ctx.Total);
      pragma Assert (U64 (L) <= U64 (Max_Message - Ctx.Total));
      pragma Assert (L <= Max_Message - Ctx.Total);
      --  And the new count's image is the sum of the images.
      Lemma_U64_Add (Ctx.Total, L);
      return R : constant Context := Absorb (Ctx, Data) do
         --  Absorb's Post is not executed (spec, Model_Check_Len); check
         --  the model equation here when its recursion is shallow.
         if Data'Length <= Model_Check_Len then
            pragma Assert (R = Absorbed (Ctx, Data));
         end if;
      end return;
   end Absorb_Message;

   ------------
   -- Update --
   ------------

   procedure Update (Ctx : in out Context; Data : Byte_Array) is
   begin
      Ctx := Updated (Ctx, Data);
   end Update;

   -----------
   -- Reset --
   -----------

   procedure Reset (Ctx : out Context) is
   begin
      Ctx := Initial;
   end Reset;

   ---------------------
   -- Lemma_Pad_Total --
   ---------------------

   --  Integer form of the padding arithmetic: N bytes of padding (0x80, the
   --  zero run, 8 length bytes) after a T-byte message whose buffer holds
   --  B = T mod 64 bytes end on the next multiple of 64 after T + 8.
   procedure Lemma_Pad_Total (T : Byte_Total; B, N : Natural)
     with Ghost,
          Global => null,
          Pre    => T <= Max_Message
                    and then B = Natural (T mod Block_Len)
                    and then N in 9 .. 72
                    and then (B + N) mod Block_Len = 0,
          Post   => (T + Byte_Total (N)) mod Block_Len = 0
                    and then T + Byte_Total (N)
                             = Block_Len * ((T + 8) / Block_Len + 1);

   procedure Lemma_Pad_Total (T : Byte_Total; B, N : Natural) is
      Q : constant Byte_Total := T / Block_Len;
   begin
      pragma Assert (T = Block_Len * Q + Byte_Total (B));
      if B + N = Block_Len then
         pragma Assert (B <= 55);
         pragma Assert ((T + 8) / Block_Len = Q);
         pragma Assert (T + Byte_Total (N) = Block_Len * (Q + 1));
      else
         pragma Assert (B + N = 2 * Block_Len);
         pragma Assert (B >= 56);
         pragma Assert ((T + 8) / Block_Len = Q + 1);
         pragma Assert (T + Byte_Total (N) = Block_Len * (Q + 2));
      end if;
   end Lemma_Pad_Total;

   ------------------------
   -- Lemma_Padded_Image --
   ------------------------

   --  The U64 image of the integer padding arithmetic: what Finalize
   --  computes on Byte_Total is Padded_Length on Byte_Count.
   procedure Lemma_Padded_Image (T, P : Byte_Total)
     with Ghost,
          Global => null,
          Pre    => T <= Max_Message
                    and then P = Block_Len * ((T + 8) / Block_Len + 1),
          Post   => U64 (P) = Padded_Length (U64 (T))
                    and then U64 (P) - U64 (T) = U64 (P - T)
                    and then P - T in 9 .. 72;

   procedure Lemma_Padded_Image (T, P : Byte_Total) is
      Q : constant Byte_Total := (T + 8) / Block_Len;
      R : constant Byte_Total := (T + 8) mod Block_Len;
   begin
      pragma Assert (T + 8 = Block_Len * Q + R);
      Lemma_U64_Add (T, 8);
      pragma Assert (U64 (T) + 8 = U64 (T + 8));
      Lemma_U64_Times_64 (Q);
      Lemma_U64_Add (Block_Len * Q, R);
      pragma Assert (U64 (T) + 8 = Block_Len * U64 (Q) + U64 (R));
      pragma Assert (U64 (R) < Block_Len);
      pragma Assert (U64 (Q) <= U64 (Max_Total / Block_Len));
      pragma Assert ((U64 (T) + 8) / Block_Len = U64 (Q));
      pragma Assert (Padded_Length (U64 (T)) = Block_Len * U64 (Q) + Block_Len);
      Lemma_U64_Add (Block_Len * Q, Block_Len);
      pragma Assert (P = Block_Len * Q + Block_Len);
      pragma Assert (U64 (P) = Block_Len * U64 (Q) + Block_Len);
      pragma Assert (U64 (P) = Padded_Length (U64 (T)));
      Lemma_U64_Sub (P, T);
   end Lemma_Padded_Image;

   --------------
   -- Finalize --
   --------------

   --  FIPS 180-4 §5.1.1 padding, absorbed in one call, then the state
   --  words big-endian (§6.2.2 step 4).
   function Finalize (Ctx : Context) return Finish_Result is
      N   : constant Pad_Count  := Pad_Len (Ctx.Buf_Len);
      Pad : constant Byte_Array := Padding (Ctx.Total, Ctx.Buf_Len);
      R   : Finish_Result;
   begin
      --  The padding ends a block: with the Pre's Buf_Len = Total mod 64
      --  this makes the padded count block-aligned.
      pragma Assert (Pad'Length = N);
      pragma Assert ((Ctx.Buf_Len + N) mod Block_Len = 0);
      Lemma_Pad_Total (Ctx.Total, Ctx.Buf_Len, N);
      R.State := Absorb (Ctx, Pad);
      pragma Assert (R.State = Absorbed (Ctx, Pad));
      pragma Assert (R.State.Total = Ctx.Total + Byte_Total (N));
      pragma Assert (R.State.Total mod Block_Len = 0);
      pragma Assert (R.State.Buf_Len = 0);
      pragma Assert (R.State.Total
                     = Block_Len * ((Ctx.Total + 8) / Block_Len + 1));
      Lemma_Padded_Image (Ctx.Total, R.State.Total);
      R.Digest := Digest_Bytes (R.State.State);
      pragma Assert
        (for all I in State_Words'Range =>
           R.State.State (I) = Absorbed (Ctx, Pad).State (I));
      R.State.Finished := True;
      return R;
   end Finalize;

   ------------
   -- Finish --
   ------------

   procedure Finish (Ctx : in out Context; Digest : out Hash256) is
      R : constant Finish_Result := Finalize (Ctx);
   begin
      Ctx    := R.State;
      Digest := R.Digest;
   end Finish;

   ----------
   -- Hash --
   ----------

   function Hash (Data : Byte_Array) return Hash256 is
     (Digest_Of (Updated (Initial, Data)));

   procedure Hash (Data : Byte_Array; Digest : out Hash256) is
   begin
      Digest := Hash (Data);
   end Hash;

   ---------------------------------------------------------------------------
   --  Lemmas about the functional model. Each is a ghost procedure whose
   --  Post is the law and whose body is the proof: a chain of assertions
   --  gnatprove discharges from the expression functions in the spec
   --  (Written, Filled, Fill, Take_Len, Absorbed, Updated) and the recursive
   --  calls (induction, bounded by the Subprogram_Variant). Under -gnata
   --  every assertion and every Post is executed, so the test main checks
   --  each proof step on real data.
   --
   --  Context equality is Ada equality: a record holding two arrays, which
   --  the prover cannot substitute (CONVENTIONS.md, rule 1). Where a proof
   --  step replaces one context by an equal one under Fill or Absorbed it
   --  says so with Lemma_Fill_Eq / Lemma_Absorbed_Eq.
   ---------------------------------------------------------------------------

   --  X and Y hold the same bytes, whatever their bounds.
   function Same_Bytes (X, Y : Byte_Array) return Boolean is
     (X'Length = Y'Length
      and then (for all I in X'Range => X (I) = Y (Y'First + (I - X'First))))
     with Ghost, Global => null;

   --  Fill respects equality of contexts.
   procedure Lemma_Fill_Eq (X, Y : Context; Chunk : Byte_Array)
     with Ghost,
          Global => null,
          Pre    => X = Y
                    and then Chunk'Length <= Block_Len
                    and then Chunk'Length <= Block_Len - X.Buf_Len
                    and then Byte_Total (Chunk'Length) <= Max_Total - X.Total,
          Post   => Fill (X, Chunk) = Fill (Y, Chunk);

   procedure Lemma_Fill_Eq (X, Y : Context; Chunk : Byte_Array) is
      WX : constant Block := Written (X.Buf, X.Buf_Len, Chunk);
      WY : constant Block := Written (Y.Buf, Y.Buf_Len, Chunk);
   begin
      pragma Assert (for all I in Block'Range => WX (I) = WY (I));
      pragma Assert (for all I in 0 .. 15 =>
                       Big_Endian_Word (WX, I) = Big_Endian_Word (WY, I));
      pragma Assert (Compressed (X.State, WX) = Compressed (Y.State, WY));
      pragma Assert (Fill (X, Chunk).State = Fill (Y, Chunk).State);
      pragma Assert (Fill (X, Chunk).Buf = Fill (Y, Chunk).Buf);
   end Lemma_Fill_Eq;

   --  Writing A at Pos and then B right after it is writing A & B at Pos.
   procedure Lemma_Written_Concat
     (Buf : Block; Pos : Natural; A, B : Byte_Array)
     with Ghost,
          Global => null,
          Pre    => A'Length <= Block_Len
                    and then B'Length <= Block_Len
                    and then Pos <= Block_Len
                    and then A'Length <= Block_Len - Pos
                    and then B'Length <= Block_Len - Pos - A'Length
                    and then (A'Length = 0
                              or else A'Last <= Natural'Last - B'Length),
          Post   => Written (Written (Buf, Pos, A), Pos + A'Length, B)
                    = Written (Buf, Pos, A & B);

   procedure Lemma_Written_Concat
     (Buf : Block; Pos : Natural; A, B : Byte_Array)
   is
      W1 : constant Block := Written (Buf, Pos, A);
      W2 : constant Block := Written (W1, Pos + A'Length, B);
      W  : constant Block := Written (Buf, Pos, A & B);
   begin
      pragma Assert (for all I in Block'Range => W2 (I) = W (I));
      pragma Assert (W2 = W);
   end Lemma_Written_Concat;

   --  Fill composes across a chunk split as long as both pieces fit the room
   --  left in the buffer.
   procedure Lemma_Fill_Concat (Ctx : Context; A, B : Byte_Array)
     with Ghost,
          Global => null,
          Pre    => A'Length <= Block_Len
                    and then B'Length <= Block_Len
                    and then A'Length <= Block_Len - Ctx.Buf_Len
                    and then B'Length <= Block_Len - Ctx.Buf_Len - A'Length
                    and then (A'Length = 0
                              or else A'Last <= Natural'Last - B'Length)
                    and then Byte_Total (A'Length) + Byte_Total (B'Length)
                             <= Max_Total - Ctx.Total,
          Post   => Fill (Ctx, A & B) = Fill (Fill (Ctx, A), B);

   procedure Lemma_Fill_Concat (Ctx : Context; A, B : Byte_Array) is
      CA : constant Context := Fill (Ctx, A);
      W  : constant Block   := Written (Ctx.Buf, Ctx.Buf_Len, A & B);
   begin
      Lemma_Written_Concat (Ctx.Buf, Ctx.Buf_Len, A, B);
      if Ctx.Buf_Len + A'Length = Block_Len then
         --  A completes the block, so B is empty and Fill (CA, B) rewrites
         --  nothing: Written with an empty chunk is the identity.
         pragma Assert (B'Length = 0);
         pragma Assert (CA.Buf_Len = 0);
         pragma Assert (for all I in Block'Range =>
                          Written (CA.Buf, 0, B) (I) = CA.Buf (I));
         pragma Assert (Written (CA.Buf, 0, B) = CA.Buf);
         pragma Assert (Fill (CA, B) = CA);
         --  A & B holds A's bytes, so it writes the same block.
         pragma Assert (for all I in Block'Range =>
                          W (I) = Written (Ctx.Buf, Ctx.Buf_Len, A) (I));
         pragma Assert (for all I in 0 .. 15 =>
                          Big_Endian_Word (W, I)
                          = Big_Endian_Word (Written (Ctx.Buf, Ctx.Buf_Len, A), I));
         pragma Assert (Fill (Ctx, A & B).State = CA.State);
         pragma Assert (Fill (Ctx, A & B) = CA);
      else
         --  A leaves room, so CA has A in its buffer and the same state;
         --  Fill (CA, B) writes B after A, which Lemma_Written_Concat makes
         --  the write of A & B, and compresses exactly when A & B fills the
         --  block, as Fill (Ctx, A & B) does.
         pragma Assert (CA.Buf_Len = Ctx.Buf_Len + A'Length);
         pragma Assert (CA.State = Ctx.State);
         pragma Assert (CA.Buf = Written (Ctx.Buf, Ctx.Buf_Len, A));
         pragma Assert (Written (CA.Buf, CA.Buf_Len, B) = W);
         pragma Assert (for all I in Block'Range =>
                          Written (CA.Buf, CA.Buf_Len, B) (I) = W (I));
         pragma Assert (for all I in 0 .. 15 =>
                          Big_Endian_Word (Written (CA.Buf, CA.Buf_Len, B), I)
                          = Big_Endian_Word (W, I));
         pragma Assert (Fill (CA, B).Total
                        = Ctx.Total + Byte_Total (A'Length) + Byte_Total (B'Length));
         pragma Assert (Fill (CA, B).Buf = Fill (Ctx, A & B).Buf);
         pragma Assert (Fill (CA, B).Buf_Len = Fill (Ctx, A & B).Buf_Len);
         if CA.Buf_Len + B'Length = Block_Len then
            pragma Assert (Fill (CA, B).State
                           = Compressed (CA.State, Written (CA.Buf, CA.Buf_Len, B)));
            pragma Assert (Fill (Ctx, A & B).State = Compressed (Ctx.State, W));
         else
            pragma Assert (Fill (CA, B).State = CA.State);
            pragma Assert (Fill (Ctx, A & B).State = Ctx.State);
         end if;
         pragma Assert (Fill (CA, B).State = Fill (Ctx, A & B).State);
      end if;
   end Lemma_Fill_Concat;

   --  Fill depends on the bytes of its chunk, not on their bounds.
   procedure Lemma_Fill_Rebase (Ctx : Context; X, Y : Byte_Array)
     with Ghost,
          Global => null,
          Pre    => X'Length <= Block_Len
                    and then X'Length <= Block_Len - Ctx.Buf_Len
                    and then Byte_Total (X'Length) <= Max_Total - Ctx.Total
                    and then Same_Bytes (X, Y),
          Post   => Fill (Ctx, X) = Fill (Ctx, Y);

   procedure Lemma_Fill_Rebase (Ctx : Context; X, Y : Byte_Array) is
      WX : constant Block := Written (Ctx.Buf, Ctx.Buf_Len, X);
      WY : constant Block := Written (Ctx.Buf, Ctx.Buf_Len, Y);
   begin
      pragma Assert (for all I in Block'Range => WX (I) = WY (I));
      pragma Assert (WX = WY);
      pragma Assert (for all I in 0 .. 15 =>
                       Big_Endian_Word (WX, I) = Big_Endian_Word (WY, I));
      pragma Assert (Compressed (Ctx.State, WX) = Compressed (Ctx.State, WY));
   end Lemma_Fill_Rebase;

   --  Absorbed respects equality of contexts and depends on the bytes of
   --  its data, not on their bounds: one induction over the chunks, each
   --  step one Lemma_Fill_Eq and one Lemma_Fill_Rebase (constant work).
   --  This used to be two inductions (Lemma_Absorbed_Eq, and
   --  Lemma_Absorbed_Rebase, which called Lemma_Absorbed_Eq at every
   --  level), so that executing it under -gnata was cubic in the length;
   --  merged, it is quadratic (the Post at each level evaluates Absorbed
   --  on the rest of the data), see the spec, "Running the lemmas".
   procedure Lemma_Absorbed_Cong (X, Y : Context; DX, DY : Byte_Array)
     with Ghost,
          Global => null,
          Subprogram_Variant => (Decreases => DX'Length),
          Pre    => X = Y
                    and then DX'Length <= Max_Update_Len
                    and then Byte_Total (DX'Length) <= Max_Total - X.Total
                    and then Same_Bytes (DX, DY),
          Post   => Absorbed (X, DX) = Absorbed (Y, DY);

   procedure Lemma_Absorbed_Cong (X, Y : Context; DX, DY : Byte_Array) is
      T : constant Natural := Take_Len (X, DX'Length);
   begin
      if DX'Length = 0 then
         pragma Assert (DY'Length = 0);
      elsif T = DX'Length then
         pragma Assert (Take_Len (Y, DY'Length) = T);
         Lemma_Fill_Eq (X, Y, DX);
         Lemma_Fill_Rebase (Y, DX, DY);
         pragma Assert (Fill (X, DX) = Fill (Y, DY));
      else
         declare
            CX : constant Context := Fill (X, DX (DX'First .. DX'First + T - 1));
            CY : constant Context := Fill (Y, DY (DY'First .. DY'First + T - 1));
         begin
            pragma Assert (Take_Len (Y, DY'Length) = T);
            Lemma_Fill_Eq (X, Y, DX (DX'First .. DX'First + T - 1));
            pragma Assert (Same_Bytes (DX (DX'First .. DX'First + T - 1),
                                       DY (DY'First .. DY'First + T - 1)));
            Lemma_Fill_Rebase (Y, DX (DX'First .. DX'First + T - 1),
                                  DY (DY'First .. DY'First + T - 1));
            pragma Assert (CX = CY);
            pragma Assert (Same_Bytes (DX (DX'First + T .. DX'Last),
                                       DY (DY'First + T .. DY'Last)));
            Lemma_Absorbed_Cong (CX, CY, DX (DX'First + T .. DX'Last),
                                         DY (DY'First + T .. DY'Last));
            pragma Assert (Absorbed (X, DX)
                           = Absorbed (CX, DX (DX'First + T .. DX'Last)));
            pragma Assert (Absorbed (Y, DY)
                           = Absorbed (CY, DY (DY'First + T .. DY'Last)));
         end;
      end if;
   end Lemma_Absorbed_Cong;

   --  The equality step alone (same data on both sides).
   procedure Lemma_Absorbed_Eq (X, Y : Context; Data : Byte_Array)
     with Ghost,
          Global => null,
          Pre    => X = Y
                    and then Data'Length <= Max_Update_Len
                    and then Byte_Total (Data'Length) <= Max_Total - X.Total,
          Post   => Absorbed (X, Data) = Absorbed (Y, Data);

   procedure Lemma_Absorbed_Eq (X, Y : Context; Data : Byte_Array) is
   begin
      pragma Assert (Same_Bytes (Data, Data));
      Lemma_Absorbed_Cong (X, Y, Data, Data);
   end Lemma_Absorbed_Eq;

   --  X holds the bytes of A followed by the bytes of B, whatever the three
   --  sets of bounds: A & B without building it. Lemma_Absorbed_Concat
   --  takes X separately so that its induction runs on slices of X, A and
   --  B, and no level copies a concatenation.
   function Is_Concat (X, A, B : Byte_Array) return Boolean is
     (X'Length <= Max_Update_Len
      and then A'Length <= X'Length
      and then B'Length = X'Length - A'Length
      and then (for all I in A'Range => X (X'First + (I - A'First)) = A (I))
      and then (for all I in B'Range =>
                  X (X'First + A'Length + (I - B'First)) = B (I)))
     with Ghost, Global => null;

   --  The chunking law on the model, for any X holding A's bytes then B's
   --  and any two equal contexts: induction on A'Length, the recursive call
   --  on A minus its first chunk (strictly shorter). Each level takes the
   --  first chunk of X and of A (one Lemma_Fill_Eq, one Lemma_Fill_Rebase)
   --  and only the base cases call the induction Lemma_Absorbed_Cong, once,
   --  on what is left of B; so the whole proof is one induction deep and,
   --  executed, quadratic in the length (spec, "Running the lemmas"). The
   --  former version built A & B at every level and called two inductive
   --  lemmas there, which made it cubic and overflowed the stack.
   procedure Lemma_Absorbed_Concat (C1, C2 : Context; X, A, B : Byte_Array)
     with Ghost,
          Global => null,
          Subprogram_Variant => (Decreases => A'Length),
          Pre    => C1 = C2
                    and then Is_Concat (X, A, B)
                    and then (A'Length = 0
                              or else A'Last <= Natural'Last - B'Length)
                    and then Byte_Total (X'Length) <= Max_Total - C1.Total,
          Post   => Absorbed (C1, X) = Absorbed (Absorbed (C2, A), B);

   procedure Lemma_Absorbed_Concat (C1, C2 : Context; X, A, B : Byte_Array) is
      Room : constant Positive := Block_Len - C2.Buf_Len;
   begin
      pragma Assert (C1.Buf_Len = C2.Buf_Len and then C1.Total = C2.Total);
      if A'Length = 0 then
         --  Absorbed (C2, A) is C2 and X holds B's bytes.
         pragma Assert (Absorbed (C2, A) = C2);
         pragma Assert (Same_Bytes (X, B));
         Lemma_Absorbed_Cong (C1, Absorbed (C2, A), X, B);
      elsif B'Length = 0 then
         --  X holds A's bytes and absorbing nothing after A changes nothing.
         pragma Assert (Absorbed (Absorbed (C2, A), B) = Absorbed (C2, A));
         pragma Assert (Same_Bytes (X, A));
         Lemma_Absorbed_Cong (C1, C2, X, A);
      elsif A'Length >= Room then
         --  Both sides take their first Room bytes, which are the same.
         declare
            D1 : constant Context := Fill (C1, X (X'First .. X'First + Room - 1));
         begin
            pragma Assert (Take_Len (C1, X'Length) = Room);
            pragma Assert (Take_Len (C2, A'Length) = Room);
            pragma Assert (Absorbed (C1, X)
                           = Absorbed (D1, X (X'First + Room .. X'Last)));
            Lemma_Fill_Eq (C1, C2, X (X'First .. X'First + Room - 1));
            if A'Length = Room then
               --  A is exactly the chunk; the rest of X holds B's bytes.
               pragma Assert (Absorbed (C2, A) = Fill (C2, A));
               pragma Assert (Same_Bytes (X (X'First .. X'First + Room - 1), A));
               Lemma_Fill_Rebase (C2, X (X'First .. X'First + Room - 1), A);
               pragma Assert (D1 = Absorbed (C2, A));
               pragma Assert (Same_Bytes (X (X'First + Room .. X'Last), B));
               Lemma_Absorbed_Cong (D1, Absorbed (C2, A),
                                    X (X'First + Room .. X'Last), B);
            else
               --  The rest of X holds (the rest of A) then B: induction.
               pragma Assert (Same_Bytes (X (X'First .. X'First + Room - 1),
                                          A (A'First .. A'First + Room - 1)));
               Lemma_Fill_Rebase (C2, X (X'First .. X'First + Room - 1),
                                      A (A'First .. A'First + Room - 1));
               pragma Assert (D1 = Fill (C2, A (A'First .. A'First + Room - 1)));
               pragma Assert (Absorbed (C2, A)
                              = Absorbed (Fill (C2, A (A'First .. A'First + Room - 1)),
                                          A (A'First + Room .. A'Last)));
               pragma Assert (Is_Concat (X (X'First + Room .. X'Last),
                                         A (A'First + Room .. A'Last), B));
               Lemma_Absorbed_Concat
                 (D1, Fill (C2, A (A'First .. A'First + Room - 1)),
                  X (X'First + Room .. X'Last), A (A'First + Room .. A'Last), B);
            end if;
         end;
      else
         --  A fits in the buffer: Absorbed (C2, A) = Fill (C2, A), and the
         --  first chunk of X is A followed by the first T2 bytes of B,
         --  which is also the first chunk B contributes after A.
         declare
            CA : constant Context    := Fill (C2, A);
            T2 : constant Positive   := Natural'Min (Room - A'Length, B'Length);
            B1 : constant Byte_Array := B (B'First .. B'First + (T2 - 1));
            N1 : constant Positive   := A'Length + T2;
         begin
            pragma Assert (Absorbed (C2, A) = CA);
            pragma Assert (CA.Buf_Len = C2.Buf_Len + A'Length);
            pragma Assert (Take_Len (CA, B'Length) = T2);
            pragma Assert (Take_Len (C1, X'Length) = N1);
            if T2 = B'Length then
               --  X is a single chunk on both sides.
               Lemma_Fill_Concat (C2, A, B);
               pragma Assert (Same_Bytes (X, A & B));
               Lemma_Fill_Eq (C1, C2, X);
               Lemma_Fill_Rebase (C2, X, A & B);
               pragma Assert (Absorbed (C1, X) = Fill (C1, X));
               pragma Assert (Absorbed (CA, B) = Fill (CA, B));
               pragma Assert (Fill (C1, X) = Fill (CA, B));
            else
               --  Both sides continue from equal contexts with the same
               --  bytes (the rest of B), at different indices.
               Lemma_Fill_Concat (C2, A, B1);
               pragma Assert (Same_Bytes (X (X'First .. X'First + N1 - 1), A & B1));
               Lemma_Fill_Eq (C1, C2, X (X'First .. X'First + N1 - 1));
               Lemma_Fill_Rebase (C2, X (X'First .. X'First + N1 - 1), A & B1);
               pragma Assert (Fill (C1, X (X'First .. X'First + N1 - 1))
                              = Fill (CA, B1));
               pragma Assert (Absorbed (C1, X)
                              = Absorbed (Fill (C1, X (X'First .. X'First + N1 - 1)),
                                          X (X'First + N1 .. X'Last)));
               pragma Assert (Absorbed (CA, B)
                              = Absorbed (Fill (CA, B1), B (B'First + T2 .. B'Last)));
               pragma Assert (Same_Bytes (X (X'First + N1 .. X'Last),
                                          B (B'First + T2 .. B'Last)));
               Lemma_Absorbed_Cong (Fill (C1, X (X'First .. X'First + N1 - 1)),
                                    Fill (CA, B1),
                                    X (X'First + N1 .. X'Last),
                                    B (B'First + T2 .. B'Last));
            end if;
         end;
      end if;
   end Lemma_Absorbed_Concat;

   -------------------------
   -- Lemma_Update_Concat --
   -------------------------

   --  Updated is Absorb_Message, whose Post is the model; the law on the
   --  model is Lemma_Absorbed_Concat. The U64 bound of the Pre is carried
   --  to Byte_Total first.
   --  Updated is the model, under the public Pre written on the fields.
   procedure Lemma_Updated_Model (Ctx : Context; Data : Byte_Array)
     with Ghost,
          Global => null,
          Pre    => not Ctx.Finished
                    and then Ctx.Total <= Max_Message
                    and then Ctx.Buf_Len = Natural (Ctx.Total mod Block_Len)
                    and then Data'Length <= Max_Update_Len
                    and then U64 (Data'Length) <= Max_Message_Bytes - U64 (Ctx.Total),
          Post   => Updated (Ctx, Data) = Absorbed (Ctx, Data)
                    and then Updated (Ctx, Data).Total
                             = Ctx.Total + Byte_Total (Data'Length)
                    and then not Updated (Ctx, Data).Finished
                    and then Updated (Ctx, Data).Total <= Max_Message
                    and then Updated (Ctx, Data).Buf_Len
                             = Natural (Updated (Ctx, Data).Total mod Block_Len);

   procedure Lemma_Updated_Model (Ctx : Context; Data : Byte_Array) is
      R : constant Context := Absorb_Message (Ctx, Data);
   begin
      pragma Assert (R = Absorbed (Ctx, Data));
      pragma Assert (Updated (Ctx, Data) = R);
   end Lemma_Updated_Model;

   procedure Lemma_Update_Concat (Ctx : Context; A, B : Byte_Array) is
      T  : constant Byte_Total := Ctx.Total;
      LA : constant Byte_Total := Byte_Total (A'Length);
      LB : constant Byte_Total := Byte_Total (B'Length);
   begin
      --  The Pre's U64 bound as a Byte_Total bound.
      pragma Assert (not Ctx.Finished
                     and then T <= Max_Message
                     and then Ctx.Buf_Len = Natural (T mod Block_Len));
      Lemma_U64_Sub (Max_Message, T);
      Lemma_U64_Add (LA, LB);
      pragma Assert (U64 (LA + LB) <= U64 (Max_Message - T));
      pragma Assert (LA + LB <= Max_Message - T);
      pragma Assert (Byte_Array'(A & B)'Length = A'Length + B'Length);
      --  So each Updated below is called within its precondition.
      pragma Assert (U64 (LA) <= U64 (Max_Message - T));
      pragma Assert (U64 (A'Length) <= Max_Message_Bytes - U64 (T));
      pragma Assert (U64 (Byte_Array'(A & B)'Length)
                     <= Max_Message_Bytes - U64 (T));
      Lemma_Updated_Model (Ctx, A);
      Lemma_Updated_Model (Ctx, A & B);
      declare
         CA : constant Context := Updated (Ctx, A);
      begin
         Lemma_U64_Sub (Max_Message, T + LA);
         pragma Assert (U64 (LB) <= U64 (Max_Message - (T + LA)));
         pragma Assert (U64 (B'Length) <= Max_Message_Bytes - U64 (CA.Total));
         Lemma_Updated_Model (CA, B);
         declare
            AB : constant Byte_Array := A & B;
         begin
            --  AB is a concatenation in the sense of Is_Concat (RM 4.5.3:
            --  A & B is indexed from A'First, or is B when A is null).
            pragma Assert (AB'Length = A'Length + B'Length);
            if A'Length = 0 then
               pragma Assert (AB'First = B'First);
               pragma Assert (for all I in B'Range => AB (I) = B (I));
               pragma Assert (for all I in B'Range =>
                                AB (AB'First + A'Length + (I - B'First)) = B (I));
            else
               pragma Assert (AB'First = A'First);
               pragma Assert (for all I in A'Range => AB (I) = A (I));
               pragma Assert (for all I in A'Range =>
                                AB (AB'First + (I - A'First)) = A (I));
               pragma Assert (for all I in B'Range =>
                                AB (A'Last + 1 + (I - B'First)) = B (I));
               pragma Assert (for all I in B'Range =>
                                AB (AB'First + A'Length + (I - B'First)) = B (I));
            end if;
            pragma Assert (Is_Concat (AB, A, B));
            Lemma_Absorbed_Concat (Ctx, Ctx, AB, A, B);
            pragma Assert (Absorbed (Ctx, A & B) = Absorbed (Absorbed (Ctx, A), B));
         end;
         Lemma_Absorbed_Eq (CA, Absorbed (Ctx, A), B);
         pragma Assert (Updated (Ctx, A & B) = Updated (CA, B));
      end;
   end Lemma_Update_Concat;

   ----------------------------------------------
   -- Lemma_Updated_Eq, Lemma_Digest_Of_Eq --
   ----------------------------------------------

   procedure Lemma_Updated_Eq (C1, C2 : Context; Data : Byte_Array) is
   begin
      Lemma_Updated_Model (C1, Data);
      Lemma_Updated_Model (C2, Data);
      Lemma_Absorbed_Eq (C1, C2, Data);
   end Lemma_Updated_Eq;

   --  Finalize's Post defines the digest from the state after absorbing
   --  the padding; the padding is a function of the counters (scalars), and
   --  Lemma_Absorbed_Eq carries the equality through the absorption.
   procedure Lemma_Digest_Of_Eq (C1, C2 : Context) is
      P : constant Byte_Array := Padding (C1.Total, C1.Buf_Len);
   begin
      pragma Assert (Padding (C2.Total, C2.Buf_Len) = P);
      Lemma_Absorbed_Eq (C1, C2, P);
      pragma Assert
        (for all I in State_Words'Range =>
           Absorbed (C1, P).State (I) = Absorbed (C2, P).State (I));
      pragma Assert (Digest_Bytes (Absorbed (C1, P).State)
                     = Digest_Bytes (Absorbed (C2, P).State));
   end Lemma_Digest_Of_Eq;

   procedure Lemma_Finished_Block_Aligned (Ctx : Context) is
   begin
      pragma Assert (Ctx.Total mod Block_Len = 0);
      pragma Assert (U64 (Ctx.Total) mod Block_Len = U64 (Ctx.Total mod Block_Len));
   end Lemma_Finished_Block_Aligned;

   procedure Lemma_Padded_Length (N : U64) is null;

end Kome.SHA256;
