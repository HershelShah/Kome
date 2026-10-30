--  Kome.Byteorder: mirror of src/byteorder.h, the fixed-width little-endian
--  (de)serialization primitives every codec in the engine pins its encoding
--  on.
--
--  The C++ offers four shapes per width (u32, u64):
--    store_uNNle(out[N], v)         fixed buffer, caller owns the size
--    put_uNNle(std::string&, v)     append to a growing string
--    read_uNNle(p)                  raw read, caller checked N bytes exist
--    get_uNNle(p, end, v) -> bool   bounds-checked, cursor-advancing read
--
--  Here the "growing string" is a bounded buffer (array plus length, as
--  CONVENTIONS.md requires) and the pointer pair (p, end) is an index Pos
--  into an array whose 'Last plays the role of end - 1; a caller that has a
--  smaller "end" passes a slice. The functional views Byte_Of_*, To_LE_*
--  and With_LE_* are what every contract is written in terms of, and the
--  ghost lemmas state the round-trip law read(store(x)) = x, its converse,
--  and get(put(x)) = x on the buffer API.
--
--  Everything bit-level is written with the Shift_Left/Shift_Right
--  intrinsics and "and"/"or", exactly as the C++ writes it (v >> (i*8),
--  p[i] << (i*8)), so gnatprove maps the contracts to bit-vector operations
--  (bvlshr/bvshl/bvand/bvor) instead of an axiomatized power function with
--  a non-literal exponent, which is what a `V / 2 ** (8 * I)` view would
--  have produced.
--
--  No file, clock or global state is touched by anything here, so every
--  subprogram has Global => null (implied by Pure).
pragma Ada_2022;
package Kome.Byteorder with SPARK_Mode, Pure is

   --  Widths in bytes, as the C++ fixed arrays uint8_t out[4] / out[8].
   U32_Len : constant := 4;
   U64_Len : constant := 8;

   subtype U32_Index is Natural range 0 .. U32_Len - 1;
   subtype U64_Index is Natural range 0 .. U64_Len - 1;

   subtype U32_Bytes is Byte_Array (U32_Index);
   subtype U64_Bytes is Byte_Array (U64_Index);

   ----------------------------------------------------------------------
   --  Shift intrinsics on the modular types, the same profile as those in
   --  Interfaces (which SPARK models as bit-vector shifts). They are the
   --  C++ ">>" and "<<" on uint32_t / uint64_t for Amount < width.
   ----------------------------------------------------------------------

   function Shift_Right (Value : U32; Amount : Natural) return U32
     with Import, Convention => Intrinsic, Global => null;
   function Shift_Left (Value : U32; Amount : Natural) return U32
     with Import, Convention => Intrinsic, Global => null;
   function Shift_Right (Value : U64; Amount : Natural) return U64
     with Import, Convention => Intrinsic, Global => null;
   function Shift_Left (Value : U64; Amount : Natural) return U64
     with Import, Convention => Intrinsic, Global => null;

   ----------------------------------------------------------------------
   --  Functional views: byte I of the little-endian encoding of V, which
   --  is exactly the C++ (uint8_t)(v >> (i * 8)).
   ----------------------------------------------------------------------

   function Byte_Of_U32 (V : U32; I : U32_Index) return Byte is
     (Byte (Shift_Right (V, 8 * I) and 16#FF#));

   function Byte_Of_U64 (V : U64; I : U64_Index) return Byte is
     (Byte (Shift_Right (V, 8 * I) and 16#FF#));

   --  store_u32le / store_u64le into a fresh fixed-size buffer.
   function To_LE_U32 (V : U32) return U32_Bytes is
     ([for I in U32_Index => Byte_Of_U32 (V, I)]);

   function To_LE_U64 (V : U64) return U64_Bytes is
     ([for I in U64_Index => Byte_Of_U64 (V, I)]);

   --  store_uNNle(out + pos, v) as a function of the whole buffer: the N
   --  bytes at Pos are the encoding of V, every other byte is Buf's. The
   --  Store_* and Put_* postconditions are stated as equality with this
   --  view, so a caller can reason about the buffer after a store without
   --  unfolding the two-part "slice equals / rest unchanged" form.
   function With_LE_U32
     (Buf : Byte_Array; Pos : Natural; V : U32) return Byte_Array
   is
     ([for J in Buf'Range =>
         (if J >= Pos and then J <= Pos + (U32_Len - 1)
          then Byte_Of_U32 (V, J - Pos)
          else Buf (J))])
     with
       Global => null,
       Pre    => Pos in Buf'Range and then Buf'Last - Pos >= U32_Len - 1,
       Post   => With_LE_U32'Result'First = Buf'First
         and then With_LE_U32'Result'Last = Buf'Last
         and then With_LE_U32'Result (Pos .. Pos + (U32_Len - 1)) = To_LE_U32 (V);

   function With_LE_U64
     (Buf : Byte_Array; Pos : Natural; V : U64) return Byte_Array
   is
     ([for J in Buf'Range =>
         (if J >= Pos and then J <= Pos + (U64_Len - 1)
          then Byte_Of_U64 (V, J - Pos)
          else Buf (J))])
     with
       Global => null,
       Pre    => Pos in Buf'Range and then Buf'Last - Pos >= U64_Len - 1,
       Post   => With_LE_U64'Result'First = Buf'First
         and then With_LE_U64'Result'Last = Buf'Last
         and then With_LE_U64'Result (Pos .. Pos + (U64_Len - 1)) = To_LE_U64 (V);

   ----------------------------------------------------------------------
   --  store_uNNle(out, v): write the N bytes of V at Buf (Pos .. Pos+N-1).
   --  The C++ has no bounds ("caller owns the size"); here that is the
   --  precondition, so an out-of-bounds store is a proof failure, not UB.
   --  The Post adds N-1 in parentheses on purpose: Pos + (N - 1) never
   --  leaves Buf'Range, whereas (Pos + N) - 1 overflows Integer when the
   --  store ends at Natural'Last, which the C++ allows and so must we.
   ----------------------------------------------------------------------

   procedure Store_U32LE (Buf : in out Byte_Array; Pos : Natural; V : U32)
     with
       Global => null,
       Pre    => Pos in Buf'Range and then Buf'Last - Pos >= U32_Len - 1,
       Post   => Buf = With_LE_U32 (Buf'Old, Pos, V)
         and then Buf (Pos .. Pos + (U32_Len - 1)) = To_LE_U32 (V)
         and then (for all J in Buf'Range =>
                     (if J < Pos or else J > Pos + (U32_Len - 1)
                      then Buf (J) = Buf'Old (J)));

   procedure Store_U64LE (Buf : in out Byte_Array; Pos : Natural; V : U64)
     with
       Global => null,
       Pre    => Pos in Buf'Range and then Buf'Last - Pos >= U64_Len - 1,
       Post   => Buf = With_LE_U64 (Buf'Old, Pos, V)
         and then Buf (Pos .. Pos + (U64_Len - 1)) = To_LE_U64 (V)
         and then (for all J in Buf'Range =>
                     (if J < Pos or else J > Pos + (U64_Len - 1)
                      then Buf (J) = Buf'Old (J)));

   ----------------------------------------------------------------------
   --  put_uNNle(std::string &out, v): append to a growing buffer modeled
   --  as Buf (Buf'First .. Buf'First + Len - 1). Where the C++ std::string
   --  would grow (and could throw std::bad_alloc) the mirror has a capacity
   --  precondition: the caller proves there is room for N more bytes.
   --  Buf'Last < Natural'Last keeps the index arithmetic in the contracts
   --  free of overflow; no engine buffer comes near that size.
   ----------------------------------------------------------------------

   procedure Put_U32LE (Buf : in out Byte_Array; Len : in out Natural; V : U32)
     with
       Global => null,
       Pre    => Buf'Last < Natural'Last
         and then Len <= Buf'Length
         and then Buf'Length - Len >= U32_Len,
       Post   => Len = Len'Old + U32_Len
         and then Buf = With_LE_U32 (Buf'Old, Buf'First + Len'Old, V)
         and then Buf (Buf'First + Len'Old .. Buf'First + Len - 1) = To_LE_U32 (V)
         and then (for all J in Buf'Range =>
                     (if J < Buf'First + Len'Old or else J >= Buf'First + Len
                      then Buf (J) = Buf'Old (J)));

   procedure Put_U64LE (Buf : in out Byte_Array; Len : in out Natural; V : U64)
     with
       Global => null,
       Pre    => Buf'Last < Natural'Last
         and then Len <= Buf'Length
         and then Buf'Length - Len >= U64_Len,
       Post   => Len = Len'Old + U64_Len
         and then Buf = With_LE_U64 (Buf'Old, Buf'First + Len'Old, V)
         and then Buf (Buf'First + Len'Old .. Buf'First + Len - 1) = To_LE_U64 (V)
         and then (for all J in Buf'Range =>
                     (if J < Buf'First + Len'Old or else J >= Buf'First + Len
                      then Buf (J) = Buf'Old (J)));

   ----------------------------------------------------------------------
   --  read_uNNle(p): the C++ ORs (uintNN_t)p[i] << (i*8); the mirror is
   --  the same OR of shifts written as an expression function so the
   --  contracts can unfold it. "Caller checked there are N bytes" is the
   --  precondition.
   ----------------------------------------------------------------------

   function Read_U32LE (Buf : Byte_Array; Pos : Natural) return U32 is
     (U32 (Buf (Pos))
      or Shift_Left (U32 (Buf (Pos + 1)), 8)
      or Shift_Left (U32 (Buf (Pos + 2)), 16)
      or Shift_Left (U32 (Buf (Pos + 3)), 24))
     with
       Global => null,
       Pre    => Pos in Buf'Range and then Buf'Last - Pos >= U32_Len - 1,
       Post   => (for all I in U32_Index =>
                    Byte_Of_U32 (Read_U32LE'Result, I) = Buf (Pos + I));

   function Read_U64LE (Buf : Byte_Array; Pos : Natural) return U64 is
     (U64 (Buf (Pos))
      or Shift_Left (U64 (Buf (Pos + 1)), 8)
      or Shift_Left (U64 (Buf (Pos + 2)), 16)
      or Shift_Left (U64 (Buf (Pos + 3)), 24)
      or Shift_Left (U64 (Buf (Pos + 4)), 32)
      or Shift_Left (U64 (Buf (Pos + 5)), 40)
      or Shift_Left (U64 (Buf (Pos + 6)), 48)
      or Shift_Left (U64 (Buf (Pos + 7)), 56))
     with
       Global => null,
       Pre    => Pos in Buf'Range and then Buf'Last - Pos >= U64_Len - 1,
       Post   => (for all I in U64_Index =>
                    Byte_Of_U64 (Read_U64LE'Result, I) = Buf (Pos + I));

   ----------------------------------------------------------------------
   --  get_uNNle(p, end, v): bounds-checked, cursor-advancing read. Pos is
   --  the cursor (next unread index); the readable region is
   --  Buf (Pos .. Buf'Last), so Pos = Buf'Last + 1 is an exhausted cursor
   --  (p == end). On success V holds the value and Pos moves past it; on
   --  failure Pos is unchanged. The C++ leaves v untouched on failure
   --  and every caller returns without reading it; a SPARK out parameter
   --  must be assigned on every path, so the mirror sets V to 0 there.
   --  This is not observable through any caller.
   --  Buf'Last < Natural'Last: a successful read of the last N bytes
   --  leaves Pos = Buf'Last + 1 (the C++ p == end), which must be a
   --  Natural. Same guard as Put_*; no engine buffer comes near that size.
   ----------------------------------------------------------------------

   function Has_Bytes (Buf : Byte_Array; Pos : Natural; N : Positive)
                       return Boolean is
     (Buf'Last - Pos >= N - 1)
     with
       Global => null,
       Pre    => Pos >= Buf'First and then Pos - 1 <= Buf'Last;

   procedure Get_U32LE
     (Buf : Byte_Array; Pos : in out Natural; V : out U32; OK : out Boolean)
     with
       Global => null,
       Pre    => Buf'Last < Natural'Last
         and then Pos >= Buf'First and then Pos - 1 <= Buf'Last,
       Post   => OK = Has_Bytes (Buf, Pos'Old, U32_Len)
         and then (if OK
                   then Pos = Pos'Old + U32_Len
                     and then V = Read_U32LE (Buf, Pos'Old)
                   else Pos = Pos'Old and then V = 0);

   procedure Get_U64LE
     (Buf : Byte_Array; Pos : in out Natural; V : out U64; OK : out Boolean)
     with
       Global => null,
       Pre    => Buf'Last < Natural'Last
         and then Pos >= Buf'First and then Pos - 1 <= Buf'Last,
       Post   => OK = Has_Bytes (Buf, Pos'Old, U64_Len)
         and then (if OK
                   then Pos = Pos'Old + U64_Len
                     and then V = Read_U64LE (Buf, Pos'Old)
                   else Pos = Pos'Old and then V = 0);

   ----------------------------------------------------------------------
   --  Laws. Each is a ghost lemma procedure with the law as its Post. The
   --  bodies assert the per-lane equalities that lead to the law (so
   --  gnatprove works from bit-vector facts, one byte at a time, instead
   --  of having to find the decomposition itself), and -gnata evaluates
   --  every assertion and every Post at run time on the values the tests
   --  feed in.
   ----------------------------------------------------------------------

   --  read(store(x)) = x: the encoding is injective and get undoes put.
   procedure Lemma_Read_Store_U32 (V : U32)
     with Ghost, Global => null,
          Post => Read_U32LE (To_LE_U32 (V), 0) = V;

   procedure Lemma_Read_Store_U64 (V : U64)
     with Ghost, Global => null,
          Post => Read_U64LE (To_LE_U64 (V), 0) = V;

   --  store(read(b)) = b: the encoding is surjective onto N-byte strings,
   --  so every N bytes decode to exactly one value that re-encodes to them.
   procedure Lemma_Store_Read_U32 (B : U32_Bytes)
     with Ghost, Global => null,
          Post => To_LE_U32 (Read_U32LE (B, 0)) = B;

   procedure Lemma_Store_Read_U64 (B : U64_Bytes)
     with Ghost, Global => null,
          Post => To_LE_U64 (Read_U64LE (B, 0)) = B;

   --  get(put(x)) = x on the buffer API. Put_UNNLE on (Buf, Len) yields the
   --  buffer With_LE_UNN (Buf, Buf'First + Len, V) with Len + N bytes in
   --  use (its Post); the Post here says that in that buffer, at the
   --  cursor Buf'First + Len where the value was appended, a Get succeeds
   --  (Has_Bytes holds, so OK is True and Pos advances by exactly N) and
   --  returns V (Read_UNNLE there is V). The body performs Put then Get on
   --  a local copy and asserts those three outcomes so that the Post is
   --  reached through the real subprograms, not only through the views.
   procedure Lemma_Get_Put_U32 (Buf : Byte_Array; Len : Natural; V : U32)
     with Ghost, Global => null,
          Pre  => Buf'Last < Natural'Last
            and then Len <= Buf'Length
            and then Buf'Length - Len >= U32_Len,
          Post => Has_Bytes (With_LE_U32 (Buf, Buf'First + Len, V),
                             Buf'First + Len, U32_Len)
            and then Read_U32LE (With_LE_U32 (Buf, Buf'First + Len, V),
                                 Buf'First + Len) = V;

   procedure Lemma_Get_Put_U64 (Buf : Byte_Array; Len : Natural; V : U64)
     with Ghost, Global => null,
          Pre  => Buf'Last < Natural'Last
            and then Len <= Buf'Length
            and then Buf'Length - Len >= U64_Len,
          Post => Has_Bytes (With_LE_U64 (Buf, Buf'First + Len, V),
                             Buf'First + Len, U64_Len)
            and then Read_U64LE (With_LE_U64 (Buf, Buf'First + Len, V),
                                 Buf'First + Len) = V;

end Kome.Byteorder;
