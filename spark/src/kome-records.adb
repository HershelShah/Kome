--  Body of Kome.Records. An encoder is the layout, read position by
--  position (Frame_Byte) into one aggregate. A parser is one aggregate for
--  each field. For Decode o Encode, the round-trip lemmas instantiate the
--  per-byte Post of the encoder at the offsets of each field. For Encode o
--  Decode, they go through the frame one segment at a time. The u48 / u16
--  lemmas discharge the integer lanes, and these lemmas use the word lemmas
--  of Kome.Keys.
pragma Ada_2022;
package body Kome.Records with SPARK_Mode is

   ---------------------------------------------------------------------------
   --  Integers
   ---------------------------------------------------------------------------

   procedure Lemma_U48_Round_Trip (V : U48) is
      Hi : constant Word := Word (V / 2 ** 32);
      Lo : constant Word := Word (V mod 2 ** 32);
   begin
      pragma Assert (Hi < 2 ** 16);
      pragma Assert (V = U48 (Hi) * 2 ** 32 + U48 (Lo));
      Lemma_Word_Round_Trip (Hi);
      Lemma_Word_Round_Trip (Lo);
      pragma Assert (Hi / 256 / 256 = 0);
      pragma Assert (Byte_Of_Word (Hi, 0) = 0);
      pragma Assert (Byte_Of_Word (Hi, 1) = 0);
      pragma Assert (Word_Of (0, 0, Byte_Of_Word (Hi, 2), Byte_Of_Word (Hi, 3)) = Hi);
      pragma Assert (Word_Of (Byte_Of_Word (Lo, 0), Byte_Of_Word (Lo, 1),
                              Byte_Of_Word (Lo, 2), Byte_Of_Word (Lo, 3)) = Lo);
   end Lemma_U48_Round_Trip;

   procedure Lemma_U48_Bytes_Round_Trip (B0, B1, B2, B3, B4, B5 : Byte) is
      Hi : constant Word := Word_Of (0, 0, B0, B1);
      Lo : constant Word := Word_Of (B2, B3, B4, B5);
      V  : constant U48  := U48_Of (B0, B1, B2, B3, B4, B5);
   begin
      pragma Assert (Hi < 2 ** 16);
      pragma Assert (V = U48 (Hi) * 2 ** 32 + U48 (Lo));
      pragma Assert (V / 2 ** 32 = U48 (Hi));
      pragma Assert (V mod 2 ** 32 = U48 (Lo));
      Lemma_Lanes_Round_Trip (0, 0, B0, B1);
      Lemma_Lanes_Round_Trip (B2, B3, B4, B5);
   end Lemma_U48_Bytes_Round_Trip;

   procedure Lemma_U16_Round_Trip (V : U16_Value) is
      W : constant Word := Word (V);
   begin
      Lemma_Word_Round_Trip (W);
      pragma Assert (W / 256 / 256 = 0);
      pragma Assert (Byte_Of_Word (W, 0) = 0);
      pragma Assert (Byte_Of_Word (W, 1) = 0);
      pragma Assert (Word_Of (0, 0, Byte_Of_Word (W, 2), Byte_Of_Word (W, 3)) = W);
   end Lemma_U16_Round_Trip;

   procedure Lemma_U16_Bytes_Round_Trip (B0, B1 : Byte) is
   begin
      Lemma_Lanes_Round_Trip (0, 0, B0, B1);
   end Lemma_U16_Bytes_Round_Trip;

   ---------------------------------------------------------------------------
   --  PUT
   ---------------------------------------------------------------------------

   function Make_Put
     (NS     : NS_Id;
      Ent    : Ent_Id;
      Field  : Byte_Array;
      T, Seq : U48;
      Author : Pubkey;
      Value  : Byte_Array) return Put_Record
   is
      FL : constant Field_Len := Field'Length;
      VL : constant Value_Len := Value'Length;
      R  : constant Put_Record :=
        (C         =>
           (NS     => NS,
            Ent    => Ent,
            FLen   => FL,
            Field  => [for I in Field_Bytes'Range =>
                         (if I < FL then Field (Field'First + I) else 0)],
            T      => T,
            Seq    => Seq,
            Author => Author,
            VLen   => VL,
            Value  => [for I in Value_Bytes'Range =>
                         (if I < VL then Value (Value'First + I) else 0)]),
         Signature => [others => 0]);
   begin
      --  FH: the first FL bytes of the stored field are the argument bytes.
      pragma Assert (for all K in 0 .. FL - 1 => R.C.Field (K) = Field (Field'First + K));
      Kome.Crypto.Lemma_Blake2b_Congruent (R.C.Field (0 .. FL - 1), Field);
      Lemma_Header_Canonical (R);
      return R;
   end Make_Put;

   function Content_Bytes (C : Put_Content) return Byte_Array is
      L : constant Positive := Content_Len (C);
      B : constant Byte_Array (0 .. L - 1) :=
        [for J in 0 .. L - 1 => Content_Byte (C, J)];
   begin
      return B;
   end Content_Bytes;

   function Encode (R : Put_Record) return Byte_Array is
      L : constant Positive := Frame_Len (R);
      B : constant Byte_Array (0 .. L - 1) :=
        [for J in 0 .. L - 1 => Frame_Byte (R, J)];
      CB : constant Byte_Array := Content_Bytes (R.C) with Ghost;
   begin
      pragma Assert (for all J in 0 .. Content_Len (R.C) - 1 => B (J) = CB (J));
      return B;
   end Encode;

   function Parse_Put (Frame : Byte_Array) return Put_Record is
      F  : constant Natural   := Frame'First;
      FL : constant Field_Len := Put_FL (Frame);
      VL : constant Value_Len := Put_VL (Frame);
      OA : constant Natural   := F + Put_O_Author (FL);
      OV : constant Natural   := F + Put_O_Value (FL);
      OS : constant Natural   := OV + VL;
   begin
      return
        (C         =>
           (NS     => [for I in NS_Id'Range => Frame (F + Put_O_NS + I)],
            Ent    => [for I in Ent_Id'Range => Frame (F + Put_O_Ent + I)],
            FLen   => FL,
            Field  => [for I in Field_Bytes'Range =>
                         (if I < FL then Frame (F + Put_O_Field + I) else 0)],
            T      => U48_At (Frame, F + Put_O_T (FL)),
            Seq    => U48_At (Frame, F + Put_O_Seq (FL)),
            Author => [for I in Pubkey'Range => Frame (OA + I)],
            VLen   => VL,
            Value  => [for I in Value_Bytes'Range =>
                         (if I < VL then Frame (OV + I) else 0)]),
         Signature => [for I in Sig'Range => Frame (OS + I)]);
   end Parse_Put;

   procedure Decode (Frame : Byte_Array; R : in out Put_Record; Result : out Status) is
   begin
      if Is_Put_Frame (Frame) then
         R := Parse_Put (Frame);
         Result := OK;
      else
         Result := Malformed;
      end if;
   end Decode;

   procedure Decode_Verified
     (Frame : Byte_Array; R : in out Put_Record; Result : out Status) is
   begin
      Result := Malformed;
      if Is_Put_Frame (Frame) then
         declare
            P : constant Put_Record := Parse_Put (Frame);
         begin
            if Well_Formed (P) then
               R := P;
               Result := OK;
            end if;
         end;
      end if;
   end Decode_Verified;

   procedure Sign (R : in out Put_Record; SK : Kome.Crypto.Secret_Key) is
   begin
      R.Signature := Kome.Crypto.Sign (SK, Hash (R.C));
   end Sign;

   procedure Lemma_Header_Canonical (R : Put_Record) is null;

   --  Lemma_Decode_Encode (PUT) has one helper for each field. So each VC
   --  holds only the Posts of Encode and Parse_Put and the steps for one
   --  field. (With all the steps in one body, the late goals timed out.)

   function Put_Shape_OK (R : Put_Record) return Boolean is
     (Canonical (R)
      and then Is_Put_Frame (Encode (R))
      and then Put_FL (Encode (R)) = R.C.FLen
      and then Put_VL (Encode (R)) = R.C.VLen)
   with Ghost;

   procedure Lemma_Put_Shape (R : Put_Record) with
     Ghost, Global => null,
     Pre  => Canonical (R),
     Post => Put_Shape_OK (R);

   procedure Lemma_Put_Shape (R : Put_Record) is
      E  : constant Byte_Array := Encode (R);
      FL : constant Field_Len  := R.C.FLen;
      VL : constant Value_Len  := R.C.VLen;
      OL : constant Natural    := Put_O_VLen (FL);
   begin
      pragma Assert (E'First = 0 and then E'Length = Frame_Len (R));
      pragma Assert (E (0) = Tag_Put);
      pragma Assert (E (Put_O_FLen) = Byte (FL));
      pragma Assert (Put_FL (E) = FL);
      pragma Assert (E (OL) = Byte_Of_U16 (VL, 0));
      pragma Assert (E (OL + 1) = Byte_Of_U16 (VL, 1));
      Lemma_U16_Round_Trip (VL);
      pragma Assert (Put_VL (E) = VL);
      pragma Assert (Is_Put_Frame (E));
   end Lemma_Put_Shape;

   procedure Lemma_Put_Ints (R : Put_Record) with
     Ghost, Global => null,
     Pre  => Put_Shape_OK (R),
     Post => Parse_Put (Encode (R)).C.T = R.C.T
             and then Parse_Put (Encode (R)).C.Seq = R.C.Seq;

   procedure Lemma_Put_Ints (R : Put_Record) is
      E  : constant Byte_Array := Encode (R);
      FL : constant Field_Len  := R.C.FLen;
      OT : constant Natural    := Put_O_T (FL);
      OQ : constant Natural    := Put_O_Seq (FL);
   begin
      pragma Assert (E (OT)     = Byte_Of_U48 (R.C.T, 0));
      pragma Assert (E (OT + 1) = Byte_Of_U48 (R.C.T, 1));
      pragma Assert (E (OT + 2) = Byte_Of_U48 (R.C.T, 2));
      pragma Assert (E (OT + 3) = Byte_Of_U48 (R.C.T, 3));
      pragma Assert (E (OT + 4) = Byte_Of_U48 (R.C.T, 4));
      pragma Assert (E (OT + 5) = Byte_Of_U48 (R.C.T, 5));
      Lemma_U48_Round_Trip (R.C.T);
      pragma Assert (U48_At (E, OT) = R.C.T);

      pragma Assert (E (OQ)     = Byte_Of_U48 (R.C.Seq, 0));
      pragma Assert (E (OQ + 1) = Byte_Of_U48 (R.C.Seq, 1));
      pragma Assert (E (OQ + 2) = Byte_Of_U48 (R.C.Seq, 2));
      pragma Assert (E (OQ + 3) = Byte_Of_U48 (R.C.Seq, 3));
      pragma Assert (E (OQ + 4) = Byte_Of_U48 (R.C.Seq, 4));
      pragma Assert (E (OQ + 5) = Byte_Of_U48 (R.C.Seq, 5));
      Lemma_U48_Round_Trip (R.C.Seq);
      pragma Assert (U48_At (E, OQ) = R.C.Seq);
   end Lemma_Put_Ints;

   procedure Lemma_Put_Ids (R : Put_Record) with
     Ghost, Global => null,
     Pre  => Put_Shape_OK (R),
     Post => Parse_Put (Encode (R)).C.NS = R.C.NS
             and then Parse_Put (Encode (R)).C.Ent = R.C.Ent;

   procedure Lemma_Put_Ids (R : Put_Record) is
      E : constant Byte_Array := Encode (R);
      P : constant Put_Record := Parse_Put (E);
   begin
      pragma Assert (for all I in NS_Id'Range => P.C.NS (I) = E (Put_O_NS + I));
      pragma Assert (for all I in NS_Id'Range => E (Put_O_NS + I) = R.C.NS (I));
      pragma Assert (for all I in Ent_Id'Range => P.C.Ent (I) = E (Put_O_Ent + I));
      pragma Assert (for all I in Ent_Id'Range => E (Put_O_Ent + I) = R.C.Ent (I));
   end Lemma_Put_Ids;

   procedure Lemma_Put_Field (R : Put_Record) with
     Ghost, Global => null,
     Pre  => Put_Shape_OK (R),
     Post => Parse_Put (Encode (R)).C.Field = R.C.Field;

   procedure Lemma_Put_Field (R : Put_Record) is
      E  : constant Byte_Array := Encode (R);
      P  : constant Put_Record := Parse_Put (E);
      FL : constant Field_Len  := R.C.FLen;
   begin
      pragma Assert (for all I in 0 .. FL - 1 => P.C.Field (I) = E (Put_O_Field + I));
      pragma Assert (for all I in 0 .. FL - 1 => E (Put_O_Field + I) = R.C.Field (I));
      pragma Assert (for all I in FL .. Field_Max - 1 => P.C.Field (I) = 0);
      pragma Assert (for all I in FL .. Field_Max - 1 => R.C.Field (I) = 0);
      pragma Assert (for all I in Field_Bytes'Range => P.C.Field (I) = R.C.Field (I));
   end Lemma_Put_Field;

   procedure Lemma_Put_Author (R : Put_Record) with
     Ghost, Global => null,
     Pre  => Put_Shape_OK (R),
     Post => Parse_Put (Encode (R)).C.Author = R.C.Author;

   procedure Lemma_Put_Author (R : Put_Record) is
      E  : constant Byte_Array := Encode (R);
      P  : constant Put_Record := Parse_Put (E);
      OA : constant Natural    := Put_O_Author (R.C.FLen);
   begin
      pragma Assert (for all I in Pubkey'Range => P.C.Author (I) = E (OA + I));
      pragma Assert (for all I in Pubkey'Range => E (OA + I) = R.C.Author (I));
   end Lemma_Put_Author;

   procedure Lemma_Put_Value (R : Put_Record) with
     Ghost, Global => null,
     Pre  => Put_Shape_OK (R),
     Post => Parse_Put (Encode (R)).C.Value = R.C.Value;

   procedure Lemma_Put_Value (R : Put_Record) is
      E  : constant Byte_Array := Encode (R);
      P  : constant Put_Record := Parse_Put (E);
      VL : constant Value_Len  := R.C.VLen;
      OV : constant Natural    := Put_O_Value (R.C.FLen);
   begin
      pragma Assert (for all I in 0 .. VL - 1 => P.C.Value (I) = E (OV + I));
      pragma Assert (for all I in 0 .. VL - 1 => E (OV + I) = R.C.Value (I));
      pragma Assert (for all I in VL .. Value_Max - 1 => P.C.Value (I) = 0);
      pragma Assert (for all I in VL .. Value_Max - 1 => R.C.Value (I) = 0);
      pragma Assert (for all I in Value_Bytes'Range => P.C.Value (I) = R.C.Value (I));
   end Lemma_Put_Value;

   procedure Lemma_Put_Sig (R : Put_Record) with
     Ghost, Global => null,
     Pre  => Put_Shape_OK (R),
     Post => Parse_Put (Encode (R)).Signature = R.Signature;

   procedure Lemma_Put_Sig (R : Put_Record) is
      E  : constant Byte_Array := Encode (R);
      P  : constant Put_Record := Parse_Put (E);
      OS : constant Natural    := Content_Len (R.C);
   begin
      pragma Assert (OS = Put_O_Value (R.C.FLen) + R.C.VLen);
      pragma Assert (for all I in Sig'Range => P.Signature (I) = E (OS + I));
      pragma Assert (for all I in Sig'Range => E (OS + I) = R.Signature (I));
   end Lemma_Put_Sig;

   procedure Lemma_Decode_Encode (R : Put_Record) is
   begin
      Lemma_Put_Shape (R);
      Lemma_Put_Ints (R);
      Lemma_Put_Ids (R);
      Lemma_Put_Field (R);
      Lemma_Put_Author (R);
      Lemma_Put_Value (R);
      Lemma_Put_Sig (R);
      declare
         P : constant Put_Record := Parse_Put (Encode (R));
      begin
         pragma Assert (P.C.FLen = R.C.FLen);
         pragma Assert (P.C.VLen = R.C.VLen);
         pragma Assert (P.C = R.C);
         pragma Assert (P = R);
      end;
   end Lemma_Decode_Encode;

   procedure Lemma_Encode_Decode_Put (Frame : Byte_Array) is
      F  : constant Natural    := Frame'First;
      P  : constant Put_Record := Parse_Put (Frame);
      E  : constant Byte_Array := Encode (P);
      FL : constant Field_Len  := P.C.FLen;
      VL : constant Value_Len  := P.C.VLen;
      OT : constant Natural    := Put_O_T (FL);
      OQ : constant Natural    := Put_O_Seq (FL);
      OA : constant Natural    := Put_O_Author (FL);
      OL : constant Natural    := Put_O_VLen (FL);
      OV : constant Natural    := Put_O_Value (FL);
      OS : constant Natural    := OV + VL;
   begin
      Lemma_U16_Bytes_Round_Trip (Frame (F + OL), Frame (F + OL + 1));
      Lemma_U48_Bytes_Round_Trip
        (Frame (F + OT), Frame (F + OT + 1), Frame (F + OT + 2),
         Frame (F + OT + 3), Frame (F + OT + 4), Frame (F + OT + 5));
      Lemma_U48_Bytes_Round_Trip
        (Frame (F + OQ), Frame (F + OQ + 1), Frame (F + OQ + 2),
         Frame (F + OQ + 3), Frame (F + OQ + 4), Frame (F + OQ + 5));
      pragma Assert (E'First = 0 and then E'Length = Frame'Length);
      pragma Assert (E (0) = Frame (F));
      pragma Assert (for all J in Put_O_NS .. Put_O_Ent - 1 => E (J) = Frame (F + J));
      pragma Assert (for all J in Put_O_Ent .. Put_O_FLen - 1 => E (J) = Frame (F + J));
      pragma Assert (E (Put_O_FLen) = Frame (F + Put_O_FLen));
      pragma Assert (for all J in Put_O_Field .. OT - 1 => E (J) = Frame (F + J));
      pragma Assert (for all J in 0 .. OT - 1 => E (J) = Frame (F + J));
      pragma Assert (E (OT)     = Frame (F + OT));
      pragma Assert (E (OT + 1) = Frame (F + OT + 1));
      pragma Assert (E (OT + 2) = Frame (F + OT + 2));
      pragma Assert (E (OT + 3) = Frame (F + OT + 3));
      pragma Assert (E (OT + 4) = Frame (F + OT + 4));
      pragma Assert (E (OT + 5) = Frame (F + OT + 5));
      pragma Assert (E (OQ)     = Frame (F + OQ));
      pragma Assert (E (OQ + 1) = Frame (F + OQ + 1));
      pragma Assert (E (OQ + 2) = Frame (F + OQ + 2));
      pragma Assert (E (OQ + 3) = Frame (F + OQ + 3));
      pragma Assert (E (OQ + 4) = Frame (F + OQ + 4));
      pragma Assert (E (OQ + 5) = Frame (F + OQ + 5));
      pragma Assert (for all J in OT .. OA - 1 => E (J) = Frame (F + J));
      pragma Assert (for all J in OA .. OL - 1 => E (J) = Frame (F + J));
      pragma Assert (E (OL)     = Frame (F + OL));
      pragma Assert (E (OL + 1) = Frame (F + OL + 1));
      pragma Assert (for all J in OA .. OV - 1 => E (J) = Frame (F + J));
      pragma Assert (for all J in OV .. OS - 1 => E (J) = Frame (F + J));
      pragma Assert (for all J in OS .. E'Last => E (J) = Frame (F + J));
      pragma Assert (for all J in OV .. E'Last => E (J) = Frame (F + J));
      pragma Assert (for all J in 0 .. OA - 1 => E (J) = Frame (F + J));
      pragma Assert (for all J in E'Range => E (J) = Frame (F + J));
   end Lemma_Encode_Decode_Put;

   ---------------------------------------------------------------------------
   --  DEL
   ---------------------------------------------------------------------------

   function Make_Del
     (NS     : NS_Id;
      Ent    : Ent_Id;
      T, Seq : U48;
      Author : Pubkey) return Del_Record
   is
      R : constant Del_Record :=
        (C         => (NS => NS, Ent => Ent, T => T, Seq => Seq, Author => Author),
         Signature => [others => 0]);
   begin
      Lemma_Header_Canonical (R);
      return R;
   end Make_Del;

   function Content_Bytes (C : Del_Content) return Byte_Array is
      B : constant Byte_Array (0 .. Del_Content_Len - 1) :=
        [for J in 0 .. Del_Content_Len - 1 => Content_Byte (C, J)];
   begin
      return B;
   end Content_Bytes;

   function Encode (R : Del_Record) return Byte_Array is
      B : constant Byte_Array (0 .. Del_Frame_Len - 1) :=
        [for J in 0 .. Del_Frame_Len - 1 => Frame_Byte (R, J)];
      CB : constant Byte_Array := Content_Bytes (R.C) with Ghost;
   begin
      pragma Assert (for all J in 0 .. Del_Content_Len - 1 => B (J) = CB (J));
      return B;
   end Encode;

   function Parse_Del (Frame : Byte_Array) return Del_Record is
      F : constant Natural := Frame'First;
   begin
      return
        (C         =>
           (NS     => [for I in NS_Id'Range => Frame (F + Del_O_NS + I)],
            Ent    => [for I in Ent_Id'Range => Frame (F + Del_O_Ent + I)],
            T      => U48_At (Frame, F + Del_O_T),
            Seq    => U48_At (Frame, F + Del_O_Seq),
            Author => [for I in Pubkey'Range => Frame (F + Del_O_Author + I)]),
         Signature => [for I in Sig'Range => Frame (F + Del_Content_Len + I)]);
   end Parse_Del;

   procedure Decode (Frame : Byte_Array; R : in out Del_Record; Result : out Status) is
   begin
      if Is_Del_Frame (Frame) then
         R := Parse_Del (Frame);
         Result := OK;
      else
         Result := Malformed;
      end if;
   end Decode;

   procedure Decode_Verified
     (Frame : Byte_Array; R : in out Del_Record; Result : out Status) is
   begin
      Result := Malformed;
      if Is_Del_Frame (Frame) then
         declare
            P : constant Del_Record := Parse_Del (Frame);
         begin
            if Well_Formed (P) then
               R := P;
               Result := OK;
            end if;
         end;
      end if;
   end Decode_Verified;

   procedure Sign (R : in out Del_Record; SK : Kome.Crypto.Secret_Key) is
   begin
      R.Signature := Kome.Crypto.Sign (SK, Hash (R.C));
   end Sign;

   procedure Lemma_Header_Canonical (R : Del_Record) is null;

   procedure Lemma_Decode_Encode (R : Del_Record) is
      E : constant Byte_Array := Encode (R);
   begin
      pragma Assert (E'First = 0 and then E'Length = Del_Frame_Len);
      pragma Assert (E (0) = Tag_Del);
      pragma Assert (Is_Del_Frame (E));

      pragma Assert (E (Del_O_T)     = Byte_Of_U48 (R.C.T, 0));
      pragma Assert (E (Del_O_T + 1) = Byte_Of_U48 (R.C.T, 1));
      pragma Assert (E (Del_O_T + 2) = Byte_Of_U48 (R.C.T, 2));
      pragma Assert (E (Del_O_T + 3) = Byte_Of_U48 (R.C.T, 3));
      pragma Assert (E (Del_O_T + 4) = Byte_Of_U48 (R.C.T, 4));
      pragma Assert (E (Del_O_T + 5) = Byte_Of_U48 (R.C.T, 5));
      Lemma_U48_Round_Trip (R.C.T);
      pragma Assert (U48_At (E, Del_O_T) = R.C.T);

      pragma Assert (E (Del_O_Seq)     = Byte_Of_U48 (R.C.Seq, 0));
      pragma Assert (E (Del_O_Seq + 1) = Byte_Of_U48 (R.C.Seq, 1));
      pragma Assert (E (Del_O_Seq + 2) = Byte_Of_U48 (R.C.Seq, 2));
      pragma Assert (E (Del_O_Seq + 3) = Byte_Of_U48 (R.C.Seq, 3));
      pragma Assert (E (Del_O_Seq + 4) = Byte_Of_U48 (R.C.Seq, 4));
      pragma Assert (E (Del_O_Seq + 5) = Byte_Of_U48 (R.C.Seq, 5));
      Lemma_U48_Round_Trip (R.C.Seq);
      pragma Assert (U48_At (E, Del_O_Seq) = R.C.Seq);

      declare
         P : constant Del_Record := Parse_Del (E);
      begin
         pragma Assert (P.C.T = R.C.T);
         pragma Assert (P.C.Seq = R.C.Seq);
         pragma Assert (for all I in NS_Id'Range => P.C.NS (I) = R.C.NS (I));
         pragma Assert (for all I in Ent_Id'Range => P.C.Ent (I) = R.C.Ent (I));
         pragma Assert (for all I in Pubkey'Range => P.C.Author (I) = R.C.Author (I));
         pragma Assert (for all I in Sig'Range => P.Signature (I) = R.Signature (I));
         pragma Assert (P.C = R.C);
         pragma Assert (P = R);
      end;
   end Lemma_Decode_Encode;

   procedure Lemma_Encode_Decode_Del (Frame : Byte_Array) is
      F : constant Natural    := Frame'First;
      P : constant Del_Record := Parse_Del (Frame);
      E : constant Byte_Array := Encode (P);
      OT : constant := Del_O_T;
      OQ : constant := Del_O_Seq;
   begin
      Lemma_U48_Bytes_Round_Trip
        (Frame (F + OT), Frame (F + OT + 1), Frame (F + OT + 2),
         Frame (F + OT + 3), Frame (F + OT + 4), Frame (F + OT + 5));
      Lemma_U48_Bytes_Round_Trip
        (Frame (F + OQ), Frame (F + OQ + 1), Frame (F + OQ + 2),
         Frame (F + OQ + 3), Frame (F + OQ + 4), Frame (F + OQ + 5));
      pragma Assert (E'First = 0 and then E'Length = Frame'Length);
      pragma Assert (E (0) = Frame (F));
      pragma Assert (for all J in Del_O_NS .. Del_O_Ent - 1 => E (J) = Frame (F + J));
      pragma Assert (for all J in Del_O_Ent .. Del_O_T - 1 => E (J) = Frame (F + J));
      pragma Assert (E (OT)     = Frame (F + OT));
      pragma Assert (E (OT + 1) = Frame (F + OT + 1));
      pragma Assert (E (OT + 2) = Frame (F + OT + 2));
      pragma Assert (E (OT + 3) = Frame (F + OT + 3));
      pragma Assert (E (OT + 4) = Frame (F + OT + 4));
      pragma Assert (E (OT + 5) = Frame (F + OT + 5));
      pragma Assert (E (OQ)     = Frame (F + OQ));
      pragma Assert (E (OQ + 1) = Frame (F + OQ + 1));
      pragma Assert (E (OQ + 2) = Frame (F + OQ + 2));
      pragma Assert (E (OQ + 3) = Frame (F + OQ + 3));
      pragma Assert (E (OQ + 4) = Frame (F + OQ + 4));
      pragma Assert (E (OQ + 5) = Frame (F + OQ + 5));
      pragma Assert (for all J in Del_O_Author .. Del_Content_Len - 1 => E (J) = Frame (F + J));
      pragma Assert (for all J in Del_Content_Len .. E'Last => E (J) = Frame (F + J));
      pragma Assert (for all J in E'Range => E (J) = Frame (F + J));
   end Lemma_Encode_Decode_Del;


   ---------------------------------------------------------------------------
   --  Round-trip helpers shared by the authorization kinds.
   ---------------------------------------------------------------------------

   --  E agrees with Frame (shifted to 'First = 0) on Lo .. Hi. The caller
   --  gives E as an argument, so a run-time check under -gnata encodes only
   --  once.
   function Same_At (Frame, E : Byte_Array; Lo, Hi : Natural) return Boolean is
     (for all J in Lo .. Hi => E (J) = Frame (Frame'First + J))
   with Ghost,
        Pre => Frame'Length <= Frame_Max
               and then E'First = 0
               and then E'Length = Frame'Length
               and then Hi < Frame'Length;

   ---------------------------------------------------------------------------
   --  Certificates
   ---------------------------------------------------------------------------

   function Make_Cert
     (Founding : Kome.Crypto.Secret_Key; NS : NS_Id; Signer : Pubkey; Cap : U48) return Sig is
   begin
      return Kome.Crypto.Sign (Founding, Cert_Hash (NS, Signer, Cap));
   end Make_Cert;

   ---------------------------------------------------------------------------
   --  ROSTER
   ---------------------------------------------------------------------------

   procedure Lemma_Link_Bytes (C : Roster_Content; I : Link_Index) is null;

   procedure Lemma_Member_Bytes (C : Roster_Content; I : Member_Index) is null;

   procedure Lemma_DH_Keys_OK_Def (C : Roster_Content) is null;

   procedure Lemma_DH_Box_OK (C : Roster_Content) is null;

   procedure Lemma_DH_Keys_OK (C : Roster_Content; I : Member_Index) is null;

   procedure Lemma_Member_Keys_OK_Def (C : Roster_Content) is null;

   procedure Lemma_Member_Keys_OK (C : Roster_Content; I : Member_Index) is null;

   function Make_Roster
     (Root_PK   : Pubkey;
      S         : Salt;
      Signer    : Pubkey;
      Cert_Cap  : U48;
      Cert_Sig  : Sig;
      Box_PK    : Pubkey;
      Gen       : U48;
      Ceiling_T : U48;
      Del_TTL   : U48;
      E         : Epoch;
      Links     : Byte_Array;
      Members   : Byte_Array) return Roster_Record
   is
      LL : constant Natural := Links'Length;
      LM : constant Natural := Members'Length;
   begin
      return
        (C         =>
           (NS        => Collection_Id (Root_PK, S),
            Root_PK   => Root_PK,
            Salt      => S,
            Signer    => Signer,
            Cert_Cap  => Cert_Cap,
            Cert_Sig  => Cert_Sig,
            Box_PK    => Box_PK,
            Gen       => Gen,
            Ceiling_T => Ceiling_T,
            Del_TTL   => Del_TTL,
            Epoch     => E,
            N_Links   => LL / Link_Len,
            Links     => [for I in Links_Bytes'Range =>
                            (if I < LL then Links (Links'First + I) else 0)],
            N_Members => LM / Member_Len,
            Members   => [for I in Members_Bytes'Range =>
                            (if I < LM then Members (Members'First + I) else 0)]),
         Signature => [others => 0]);
   end Make_Roster;

   function Content_Bytes (C : Roster_Content) return Byte_Array is
      L : constant Positive := Content_Len (C);
      B : constant Byte_Array (0 .. L - 1) :=
        [for J in 0 .. L - 1 => Content_Byte (C, J)];
   begin
      return B;
   end Content_Bytes;

   function Encode (R : Roster_Record) return Byte_Array is
      L : constant Positive := Frame_Len (R);
      B : constant Byte_Array (0 .. L - 1) :=
        [for J in 0 .. L - 1 => Frame_Byte (R, J)];
      CB : constant Byte_Array := Content_Bytes (R.C) with Ghost;
   begin
      pragma Assert (for all J in 0 .. Content_Len (R.C) - 1 => B (J) = CB (J));
      return B;
   end Encode;

   function Parse_Roster (Frame : Byte_Array) return Roster_Record is
      F  : constant Natural      := Frame'First;
      NL : constant Link_Count   := Roster_NL (Frame);
      NM : constant Member_Count := Roster_NM (Frame);
      OM : constant Natural      := F + Roster_O_Members (NL);
      OS : constant Natural      := OM + Member_Len * NM;
   begin
      return
        (C         =>
           (NS        => [for I in NS_Id'Range => Frame (F + Roster_O_NS + I)],
            Root_PK   => [for I in Pubkey'Range => Frame (F + Roster_O_Root_PK + I)],
            Salt      => [for I in Salt'Range => Frame (F + Roster_O_Salt + I)],
            Signer    => [for I in Pubkey'Range => Frame (F + Roster_O_Signer + I)],
            Cert_Cap  => U48_At (Frame, F + Roster_O_Cert_Cap),
            Cert_Sig  => [for I in Sig'Range => Frame (F + Roster_O_Cert_Sig + I)],
            Box_PK    => [for I in Pubkey'Range => Frame (F + Roster_O_Box_PK + I)],
            Gen       => U48_At (Frame, F + Roster_O_Gen),
            Ceiling_T => U48_At (Frame, F + Roster_O_Ceiling),
            Del_TTL   => U48_At (Frame, F + Roster_O_TTL),
            Epoch     => Epoch (U16_At (Frame, F + Roster_O_Epoch)),
            N_Links   => NL,
            Links     => [for I in Links_Bytes'Range =>
                            (if I < Link_Len * NL
                             then Frame (F + Roster_O_Links + I) else 0)],
            N_Members => NM,
            Members   => [for I in Members_Bytes'Range =>
                            (if I < Member_Len * NM then Frame (OM + I) else 0)]),
         Signature => [for I in Sig'Range => Frame (OS + I)]);
   end Parse_Roster;

   procedure Decode (Frame : Byte_Array; R : in out Roster_Record; Result : out Status) is
   begin
      if Is_Roster_Frame (Frame) then
         R := Parse_Roster (Frame);
         Result := OK;
      else
         Result := Malformed;
      end if;
   end Decode;

   procedure Decode_Verified
     (Frame : Byte_Array; R : in out Roster_Record; Result : out Status) is
   begin
      Result := Malformed;
      if Is_Roster_Frame (Frame) then
         declare
            P : constant Roster_Record := Parse_Roster (Frame);
         begin
            if Well_Formed (P) then
               R := P;
               Result := OK;
            end if;
         end;
      end if;
   end Decode_Verified;

   procedure Sign (R : in out Roster_Record; SK : Kome.Crypto.Secret_Key) is
   begin
      R.Signature := Kome.Crypto.Sign (SK, Hash (R.C));
   end Sign;

   procedure Lemma_Header_Canonical (R : Roster_Record) is null;

   --  Lemma_Decode_Encode (ROSTER) has one helper for each group of fields,
   --  as for PUT. So each VC holds only the Posts of Encode and
   --  Parse_Roster and the steps for that group.

   function Roster_Shape_OK (R : Roster_Record) return Boolean is
     (Canonical (R)
      and then Is_Roster_Frame (Encode (R))
      and then Roster_NL (Encode (R)) = R.C.N_Links
      and then Roster_NM (Encode (R)) = R.C.N_Members)
   with Ghost;

   procedure Lemma_Roster_Shape (R : Roster_Record) with
     Ghost, Global => null,
     Pre  => Canonical (R),
     Post => Roster_Shape_OK (R);

   procedure Lemma_Roster_Shape (R : Roster_Record) is
      E  : constant Byte_Array   := Encode (R);
      NL : constant Link_Count   := R.C.N_Links;
      NM : constant Member_Count := R.C.N_Members;
   begin
      pragma Assert (E'First = 0 and then E'Length = Frame_Len (R));
      pragma Assert (E (0) = Tag_Roster);
      pragma Assert (E (Roster_O_NL) = Byte (NL));
      pragma Assert (Roster_NL (E) = NL);
      pragma Assert (E (Roster_O_NM (NL)) = Byte (NM));
      pragma Assert (Roster_NM (E) = NM);
      pragma Assert (Is_Roster_Frame (E));
   end Lemma_Roster_Shape;

   procedure Lemma_Roster_Ints_A (R : Roster_Record) with
     Ghost, Global => null,
     Pre  => Roster_Shape_OK (R),
     Post => Parse_Roster (Encode (R)).C.Cert_Cap = R.C.Cert_Cap
             and then Parse_Roster (Encode (R)).C.Gen = R.C.Gen;

   procedure Lemma_Roster_Ints_A (R : Roster_Record) is
      E : constant Byte_Array := Encode (R);
   begin
      pragma Assert (E (Roster_O_Cert_Cap) = Byte_Of_U48 (R.C.Cert_Cap, 0));
      pragma Assert (E (Roster_O_Cert_Cap + 1) = Byte_Of_U48 (R.C.Cert_Cap, 1));
      pragma Assert (E (Roster_O_Cert_Cap + 2) = Byte_Of_U48 (R.C.Cert_Cap, 2));
      pragma Assert (E (Roster_O_Cert_Cap + 3) = Byte_Of_U48 (R.C.Cert_Cap, 3));
      pragma Assert (E (Roster_O_Cert_Cap + 4) = Byte_Of_U48 (R.C.Cert_Cap, 4));
      pragma Assert (E (Roster_O_Cert_Cap + 5) = Byte_Of_U48 (R.C.Cert_Cap, 5));
      Lemma_U48_Round_Trip (R.C.Cert_Cap);
      pragma Assert (U48_At (E, Roster_O_Cert_Cap) = R.C.Cert_Cap);
      pragma Assert (E (Roster_O_Gen) = Byte_Of_U48 (R.C.Gen, 0));
      pragma Assert (E (Roster_O_Gen + 1) = Byte_Of_U48 (R.C.Gen, 1));
      pragma Assert (E (Roster_O_Gen + 2) = Byte_Of_U48 (R.C.Gen, 2));
      pragma Assert (E (Roster_O_Gen + 3) = Byte_Of_U48 (R.C.Gen, 3));
      pragma Assert (E (Roster_O_Gen + 4) = Byte_Of_U48 (R.C.Gen, 4));
      pragma Assert (E (Roster_O_Gen + 5) = Byte_Of_U48 (R.C.Gen, 5));
      Lemma_U48_Round_Trip (R.C.Gen);
      pragma Assert (U48_At (E, Roster_O_Gen) = R.C.Gen);
   end Lemma_Roster_Ints_A;

   procedure Lemma_Roster_Ints_B (R : Roster_Record) with
     Ghost, Global => null,
     Pre  => Roster_Shape_OK (R),
     Post => Parse_Roster (Encode (R)).C.Ceiling_T = R.C.Ceiling_T
             and then Parse_Roster (Encode (R)).C.Del_TTL = R.C.Del_TTL
             and then Parse_Roster (Encode (R)).C.Epoch = R.C.Epoch;

   procedure Lemma_Roster_Ints_B (R : Roster_Record) is
      E  : constant Byte_Array := Encode (R);
      EP : constant U16_Value  := Natural (R.C.Epoch);
   begin
      pragma Assert (E (Roster_O_Ceiling) = Byte_Of_U48 (R.C.Ceiling_T, 0));
      pragma Assert (E (Roster_O_Ceiling + 1) = Byte_Of_U48 (R.C.Ceiling_T, 1));
      pragma Assert (E (Roster_O_Ceiling + 2) = Byte_Of_U48 (R.C.Ceiling_T, 2));
      pragma Assert (E (Roster_O_Ceiling + 3) = Byte_Of_U48 (R.C.Ceiling_T, 3));
      pragma Assert (E (Roster_O_Ceiling + 4) = Byte_Of_U48 (R.C.Ceiling_T, 4));
      pragma Assert (E (Roster_O_Ceiling + 5) = Byte_Of_U48 (R.C.Ceiling_T, 5));
      Lemma_U48_Round_Trip (R.C.Ceiling_T);
      pragma Assert (U48_At (E, Roster_O_Ceiling) = R.C.Ceiling_T);
      pragma Assert (E (Roster_O_TTL) = Byte_Of_U48 (R.C.Del_TTL, 0));
      pragma Assert (E (Roster_O_TTL + 1) = Byte_Of_U48 (R.C.Del_TTL, 1));
      pragma Assert (E (Roster_O_TTL + 2) = Byte_Of_U48 (R.C.Del_TTL, 2));
      pragma Assert (E (Roster_O_TTL + 3) = Byte_Of_U48 (R.C.Del_TTL, 3));
      pragma Assert (E (Roster_O_TTL + 4) = Byte_Of_U48 (R.C.Del_TTL, 4));
      pragma Assert (E (Roster_O_TTL + 5) = Byte_Of_U48 (R.C.Del_TTL, 5));
      Lemma_U48_Round_Trip (R.C.Del_TTL);
      pragma Assert (U48_At (E, Roster_O_TTL) = R.C.Del_TTL);
      pragma Assert (E (Roster_O_Epoch)     = Byte_Of_U16 (EP, 0));
      pragma Assert (E (Roster_O_Epoch + 1) = Byte_Of_U16 (EP, 1));
      Lemma_U16_Round_Trip (EP);
      pragma Assert (U16_At (E, Roster_O_Epoch) = EP);
   end Lemma_Roster_Ints_B;

   procedure Lemma_Roster_Ids (R : Roster_Record) with
     Ghost, Global => null,
     Pre  => Roster_Shape_OK (R),
     Post => Parse_Roster (Encode (R)).C.NS = R.C.NS
             and then Parse_Roster (Encode (R)).C.Root_PK = R.C.Root_PK
             and then Parse_Roster (Encode (R)).C.Salt = R.C.Salt
             and then Parse_Roster (Encode (R)).C.Signer = R.C.Signer;

   procedure Lemma_Roster_Ids (R : Roster_Record) is
      E : constant Byte_Array    := Encode (R);
      P : constant Roster_Record := Parse_Roster (E);
   begin
      pragma Assert (for all I in NS_Id'Range => P.C.NS (I) = E (Roster_O_NS + I));
      pragma Assert (for all I in NS_Id'Range => E (Roster_O_NS + I) = R.C.NS (I));
      pragma Assert (for all I in NS_Id'Range => P.C.NS (I) = R.C.NS (I));
      pragma Assert (for all I in Pubkey'Range => P.C.Root_PK (I) = E (Roster_O_Root_PK + I));
      pragma Assert (for all I in Pubkey'Range => E (Roster_O_Root_PK + I) = R.C.Root_PK (I));
      pragma Assert (for all I in Pubkey'Range => P.C.Root_PK (I) = R.C.Root_PK (I));
      pragma Assert (for all I in Salt'Range => P.C.Salt (I) = E (Roster_O_Salt + I));
      pragma Assert (for all I in Salt'Range => E (Roster_O_Salt + I) = R.C.Salt (I));
      pragma Assert (for all I in Salt'Range => P.C.Salt (I) = R.C.Salt (I));
      pragma Assert (for all I in Pubkey'Range => P.C.Signer (I) = E (Roster_O_Signer + I));
      pragma Assert (for all I in Pubkey'Range => E (Roster_O_Signer + I) = R.C.Signer (I));
      pragma Assert (for all I in Pubkey'Range => P.C.Signer (I) = R.C.Signer (I));
   end Lemma_Roster_Ids;

   procedure Lemma_Roster_Keys (R : Roster_Record) with
     Ghost, Global => null,
     Pre  => Roster_Shape_OK (R),
     Post => Parse_Roster (Encode (R)).C.Cert_Sig = R.C.Cert_Sig
             and then Parse_Roster (Encode (R)).C.Box_PK = R.C.Box_PK;

   procedure Lemma_Roster_Keys (R : Roster_Record) is
      E : constant Byte_Array    := Encode (R);
      P : constant Roster_Record := Parse_Roster (E);
   begin
      pragma Assert (for all I in Sig'Range => P.C.Cert_Sig (I) = E (Roster_O_Cert_Sig + I));
      pragma Assert (for all I in Sig'Range => E (Roster_O_Cert_Sig + I) = R.C.Cert_Sig (I));
      pragma Assert (for all I in Sig'Range => P.C.Cert_Sig (I) = R.C.Cert_Sig (I));
      pragma Assert (for all I in Pubkey'Range => P.C.Box_PK (I) = E (Roster_O_Box_PK + I));
      pragma Assert (for all I in Pubkey'Range => E (Roster_O_Box_PK + I) = R.C.Box_PK (I));
      pragma Assert (for all I in Pubkey'Range => P.C.Box_PK (I) = R.C.Box_PK (I));
   end Lemma_Roster_Keys;

   procedure Lemma_Roster_Links (R : Roster_Record) with
     Ghost, Global => null,
     Pre  => Roster_Shape_OK (R),
     Post => Parse_Roster (Encode (R)).C.Links = R.C.Links;

   procedure Lemma_Roster_Links (R : Roster_Record) is
      E  : constant Byte_Array    := Encode (R);
      P  : constant Roster_Record := Parse_Roster (E);
      NL : constant Link_Count    := R.C.N_Links;
   begin
      pragma Assert (for all I in 0 .. Link_Len * NL - 1 =>
                       P.C.Links (I) = E (Roster_O_Links + I));
      pragma Assert (for all I in 0 .. Link_Len * NL - 1 =>
                       E (Roster_O_Links + I) = R.C.Links (I));
      pragma Assert (for all I in Link_Len * NL .. Links_Bytes_Len - 1 => P.C.Links (I) = 0);
      pragma Assert (for all I in Link_Len * NL .. Links_Bytes_Len - 1 => R.C.Links (I) = 0);
      pragma Assert (for all I in Links_Bytes'Range => P.C.Links (I) = R.C.Links (I));
   end Lemma_Roster_Links;

   procedure Lemma_Roster_Members (R : Roster_Record) with
     Ghost, Global => null,
     Pre  => Roster_Shape_OK (R),
     Post => Parse_Roster (Encode (R)).C.Members = R.C.Members;

   procedure Lemma_Roster_Members (R : Roster_Record) is
      E  : constant Byte_Array    := Encode (R);
      P  : constant Roster_Record := Parse_Roster (E);
      NM : constant Member_Count  := R.C.N_Members;
      OM : constant Natural       := Roster_O_Members (R.C.N_Links);
   begin
      pragma Assert (for all I in 0 .. Member_Len * NM - 1 => P.C.Members (I) = E (OM + I));
      pragma Assert (for all I in 0 .. Member_Len * NM - 1 => E (OM + I) = R.C.Members (I));
      pragma Assert (for all I in Member_Len * NM .. Members_Bytes_Len - 1 =>
                       P.C.Members (I) = 0);
      pragma Assert (for all I in Member_Len * NM .. Members_Bytes_Len - 1 =>
                       R.C.Members (I) = 0);
      pragma Assert (for all I in Members_Bytes'Range => P.C.Members (I) = R.C.Members (I));
   end Lemma_Roster_Members;

   procedure Lemma_Roster_Sig (R : Roster_Record) with
     Ghost, Global => null,
     Pre  => Roster_Shape_OK (R),
     Post => Parse_Roster (Encode (R)).Signature = R.Signature;

   procedure Lemma_Roster_Sig (R : Roster_Record) is
      E  : constant Byte_Array    := Encode (R);
      P  : constant Roster_Record := Parse_Roster (E);
      OS : constant Natural       := Content_Len (R.C);
   begin
      pragma Assert (OS = Roster_O_Members (R.C.N_Links) + Member_Len * R.C.N_Members);
      pragma Assert (for all I in Sig'Range => P.Signature (I) = E (OS + I));
      pragma Assert (for all I in Sig'Range => E (OS + I) = R.Signature (I));
   end Lemma_Roster_Sig;

   procedure Lemma_Decode_Encode (R : Roster_Record) is
   begin
      Lemma_Roster_Shape (R);
      Lemma_Roster_Ints_A (R);
      Lemma_Roster_Ints_B (R);
      Lemma_Roster_Ids (R);
      Lemma_Roster_Keys (R);
      Lemma_Roster_Links (R);
      Lemma_Roster_Members (R);
      Lemma_Roster_Sig (R);
      declare
         P : constant Roster_Record := Parse_Roster (Encode (R));
      begin
         pragma Assert (P.C.N_Links = R.C.N_Links);
         pragma Assert (P.C.N_Members = R.C.N_Members);
         pragma Assert (P.C = R.C);
         pragma Assert (P = R);
      end;
   end Lemma_Decode_Encode;

   --  Lemma_Encode_Decode_Roster has five parts: the fixed head (in two
   --  halves), the link block, the member block and the signature.

   procedure Lemma_Roster_ED_Head1 (Frame : Byte_Array) with
     Ghost, Global => null,
     Pre  => Is_Roster_Frame (Frame),
     Post => Encode (Parse_Roster (Frame))'First = 0
             and then Encode (Parse_Roster (Frame))'Length = Frame'Length
             and then Same_At (Frame, Encode (Parse_Roster (Frame)),
                               0, Roster_O_Box_PK - 1);

   procedure Lemma_Roster_ED_Head1 (Frame : Byte_Array) is
      F : constant Natural       := Frame'First;
      P : constant Roster_Record := Parse_Roster (Frame);
      E : constant Byte_Array    := Encode (P);
   begin
      Lemma_U48_Bytes_Round_Trip
        (Frame (F + Roster_O_Cert_Cap), Frame (F + Roster_O_Cert_Cap + 1), Frame (F + Roster_O_Cert_Cap + 2),
         Frame (F + Roster_O_Cert_Cap + 3), Frame (F + Roster_O_Cert_Cap + 4), Frame (F + Roster_O_Cert_Cap + 5));
      pragma Assert (E'First = 0 and then E'Length = Frame'Length);
      pragma Assert (E (0) = Frame (F));
      pragma Assert (for all J in Roster_O_NS .. Roster_O_Root_PK - 1 => E (J) = Frame (F + J));
      pragma Assert (for all J in Roster_O_Root_PK .. Roster_O_Salt - 1 => E (J) = Frame (F + J));
      pragma Assert (for all J in Roster_O_Salt .. Roster_O_Signer - 1 => E (J) = Frame (F + J));
      pragma Assert (for all J in Roster_O_Signer .. Roster_O_Cert_Cap - 1 => E (J) = Frame (F + J));
      pragma Assert (E (Roster_O_Cert_Cap) = Frame (F + Roster_O_Cert_Cap));
      pragma Assert (E (Roster_O_Cert_Cap + 1) = Frame (F + Roster_O_Cert_Cap + 1));
      pragma Assert (E (Roster_O_Cert_Cap + 2) = Frame (F + Roster_O_Cert_Cap + 2));
      pragma Assert (E (Roster_O_Cert_Cap + 3) = Frame (F + Roster_O_Cert_Cap + 3));
      pragma Assert (E (Roster_O_Cert_Cap + 4) = Frame (F + Roster_O_Cert_Cap + 4));
      pragma Assert (E (Roster_O_Cert_Cap + 5) = Frame (F + Roster_O_Cert_Cap + 5));
      pragma Assert (for all J in Roster_O_Cert_Sig .. Roster_O_Box_PK - 1 => E (J) = Frame (F + J));
      pragma Assert (for all J in 0 .. Roster_O_Box_PK - 1 => E (J) = Frame (F + J));
   end Lemma_Roster_ED_Head1;

   procedure Lemma_Roster_ED_Head2 (Frame : Byte_Array) with
     Ghost, Global => null,
     Pre  => Is_Roster_Frame (Frame)
             and then Encode (Parse_Roster (Frame))'First = 0
             and then Encode (Parse_Roster (Frame))'Length = Frame'Length,
     Post => Same_At (Frame, Encode (Parse_Roster (Frame)),
                      Roster_O_Box_PK, Roster_O_NL - 1);

   procedure Lemma_Roster_ED_Head2 (Frame : Byte_Array) is
      F : constant Natural       := Frame'First;
      P : constant Roster_Record := Parse_Roster (Frame);
      E : constant Byte_Array    := Encode (P);
   begin
      Lemma_U16_Bytes_Round_Trip (Frame (F + Roster_O_Epoch), Frame (F + Roster_O_Epoch + 1));
      Lemma_U48_Bytes_Round_Trip
        (Frame (F + Roster_O_Gen), Frame (F + Roster_O_Gen + 1), Frame (F + Roster_O_Gen + 2),
         Frame (F + Roster_O_Gen + 3), Frame (F + Roster_O_Gen + 4), Frame (F + Roster_O_Gen + 5));
      Lemma_U48_Bytes_Round_Trip
        (Frame (F + Roster_O_Ceiling), Frame (F + Roster_O_Ceiling + 1), Frame (F + Roster_O_Ceiling + 2),
         Frame (F + Roster_O_Ceiling + 3), Frame (F + Roster_O_Ceiling + 4), Frame (F + Roster_O_Ceiling + 5));
      Lemma_U48_Bytes_Round_Trip
        (Frame (F + Roster_O_TTL), Frame (F + Roster_O_TTL + 1), Frame (F + Roster_O_TTL + 2),
         Frame (F + Roster_O_TTL + 3), Frame (F + Roster_O_TTL + 4), Frame (F + Roster_O_TTL + 5));
      pragma Assert (for all J in Roster_O_Box_PK .. Roster_O_Gen - 1 => E (J) = Frame (F + J));
      pragma Assert (E (Roster_O_Gen) = Frame (F + Roster_O_Gen));
      pragma Assert (E (Roster_O_Gen + 1) = Frame (F + Roster_O_Gen + 1));
      pragma Assert (E (Roster_O_Gen + 2) = Frame (F + Roster_O_Gen + 2));
      pragma Assert (E (Roster_O_Gen + 3) = Frame (F + Roster_O_Gen + 3));
      pragma Assert (E (Roster_O_Gen + 4) = Frame (F + Roster_O_Gen + 4));
      pragma Assert (E (Roster_O_Gen + 5) = Frame (F + Roster_O_Gen + 5));
      pragma Assert (E (Roster_O_Ceiling) = Frame (F + Roster_O_Ceiling));
      pragma Assert (E (Roster_O_Ceiling + 1) = Frame (F + Roster_O_Ceiling + 1));
      pragma Assert (E (Roster_O_Ceiling + 2) = Frame (F + Roster_O_Ceiling + 2));
      pragma Assert (E (Roster_O_Ceiling + 3) = Frame (F + Roster_O_Ceiling + 3));
      pragma Assert (E (Roster_O_Ceiling + 4) = Frame (F + Roster_O_Ceiling + 4));
      pragma Assert (E (Roster_O_Ceiling + 5) = Frame (F + Roster_O_Ceiling + 5));
      pragma Assert (E (Roster_O_TTL) = Frame (F + Roster_O_TTL));
      pragma Assert (E (Roster_O_TTL + 1) = Frame (F + Roster_O_TTL + 1));
      pragma Assert (E (Roster_O_TTL + 2) = Frame (F + Roster_O_TTL + 2));
      pragma Assert (E (Roster_O_TTL + 3) = Frame (F + Roster_O_TTL + 3));
      pragma Assert (E (Roster_O_TTL + 4) = Frame (F + Roster_O_TTL + 4));
      pragma Assert (E (Roster_O_TTL + 5) = Frame (F + Roster_O_TTL + 5));
      pragma Assert (E (Roster_O_Epoch)     = Frame (F + Roster_O_Epoch));
      pragma Assert (E (Roster_O_Epoch + 1) = Frame (F + Roster_O_Epoch + 1));
      pragma Assert (for all J in Roster_O_Box_PK .. Roster_O_NL - 1 => E (J) = Frame (F + J));
   end Lemma_Roster_ED_Head2;

   procedure Lemma_Roster_ED_Links (Frame : Byte_Array) with
     Ghost, Global => null,
     Pre  => Is_Roster_Frame (Frame)
             and then Encode (Parse_Roster (Frame))'First = 0
             and then Encode (Parse_Roster (Frame))'Length = Frame'Length,
     Post => Same_At (Frame, Encode (Parse_Roster (Frame)),
                      Roster_O_NL, Roster_O_Members (Roster_NL (Frame)) - 1);

   procedure Lemma_Roster_ED_Links (Frame : Byte_Array) is
      F  : constant Natural       := Frame'First;
      P  : constant Roster_Record := Parse_Roster (Frame);
      E  : constant Byte_Array    := Encode (P);
      NL : constant Link_Count    := P.C.N_Links;
      ON : constant Natural       := Roster_O_NM (NL);
   begin
      pragma Assert (NL = Roster_NL (Frame));
      pragma Assert (E (Roster_O_NL) = Frame (F + Roster_O_NL));
      pragma Assert (for all J in Roster_O_Links .. ON - 1 => E (J) = P.C.Links (J - Roster_O_Links));
      pragma Assert (for all I in 0 .. Link_Len * NL - 1 =>
                       P.C.Links (I) = Frame (F + Roster_O_Links + I));
      pragma Assert (for all J in Roster_O_Links .. ON - 1 => E (J) = Frame (F + J));
      pragma Assert (E (ON) = Frame (F + ON));
      pragma Assert (for all J in Roster_O_NL .. ON => E (J) = Frame (F + J));
   end Lemma_Roster_ED_Links;

   procedure Lemma_Roster_ED_Members (Frame : Byte_Array) with
     Ghost, Global => null,
     Pre  => Is_Roster_Frame (Frame)
             and then Encode (Parse_Roster (Frame))'First = 0
             and then Encode (Parse_Roster (Frame))'Length = Frame'Length,
     Post => Same_At (Frame, Encode (Parse_Roster (Frame)),
                      Roster_O_Members (Roster_NL (Frame)),
                      Frame'Length - Sig_Len - 1);

   procedure Lemma_Roster_ED_Members (Frame : Byte_Array) is
      F  : constant Natural       := Frame'First;
      P  : constant Roster_Record := Parse_Roster (Frame);
      E  : constant Byte_Array    := Encode (P);
      NL : constant Link_Count    := P.C.N_Links;
      NM : constant Member_Count  := P.C.N_Members;
      OM : constant Natural       := Roster_O_Members (NL);
      OS : constant Natural       := OM + Member_Len * NM;
   begin
      pragma Assert (NL = Roster_NL (Frame) and then NM = Roster_NM (Frame));
      pragma Assert (Content_Len (P.C) = OS);
      pragma Assert (OS = Frame'Length - Sig_Len);
      pragma Assert (for all J in OM .. OS - 1 => E (J) = P.C.Members (J - OM));
      pragma Assert (for all I in 0 .. Member_Len * NM - 1 =>
                       P.C.Members (I) = Frame (F + OM + I));
      pragma Assert (for all J in OM .. OS - 1 => E (J) = Frame (F + J));
   end Lemma_Roster_ED_Members;

   procedure Lemma_Roster_ED_Sig (Frame : Byte_Array) with
     Ghost, Global => null,
     Pre  => Is_Roster_Frame (Frame)
             and then Encode (Parse_Roster (Frame))'First = 0
             and then Encode (Parse_Roster (Frame))'Length = Frame'Length,
     Post => Same_At (Frame, Encode (Parse_Roster (Frame)),
                      Frame'Length - Sig_Len, Frame'Length - 1);

   procedure Lemma_Roster_ED_Sig (Frame : Byte_Array) is
      F  : constant Natural       := Frame'First;
      P  : constant Roster_Record := Parse_Roster (Frame);
      E  : constant Byte_Array    := Encode (P);
      NL : constant Link_Count    := P.C.N_Links;
      NM : constant Member_Count  := P.C.N_Members;
      OS : constant Natural       := Roster_O_Members (NL) + Member_Len * NM;
   begin
      pragma Assert (NL = Roster_NL (Frame) and then NM = Roster_NM (Frame));
      pragma Assert (Content_Len (P.C) = OS);
      pragma Assert (OS = Frame'Length - Sig_Len);
      pragma Assert (for all J in OS .. OS + Sig_Len - 1 => E (J) = P.Signature (J - OS));
      pragma Assert (for all I in Sig'Range => P.Signature (I) = Frame (F + OS + I));
      pragma Assert (for all J in OS .. OS + Sig_Len - 1 => E (J) = Frame (F + J));
   end Lemma_Roster_ED_Sig;

   procedure Lemma_Encode_Decode_Roster (Frame : Byte_Array) is
      F : constant Natural := Frame'First;
   begin
      Lemma_Roster_ED_Head1 (Frame);
      Lemma_Roster_ED_Head2 (Frame);
      Lemma_Roster_ED_Links (Frame);
      Lemma_Roster_ED_Members (Frame);
      Lemma_Roster_ED_Sig (Frame);
      declare
         E  : constant Byte_Array := Encode (Parse_Roster (Frame));
         OM : constant Natural    := Roster_O_Members (Roster_NL (Frame));
         L  : constant Natural    := Frame'Length;
      begin
         pragma Assert (for all J in 0 .. Roster_O_Box_PK - 1 => E (J) = Frame (F + J));
         pragma Assert (for all J in Roster_O_Box_PK .. Roster_O_NL - 1 =>
                          E (J) = Frame (F + J));
         pragma Assert (for all J in Roster_O_NL .. OM - 1 => E (J) = Frame (F + J));
         pragma Assert (for all J in OM .. L - Sig_Len - 1 => E (J) = Frame (F + J));
         pragma Assert (for all J in L - Sig_Len .. L - 1 => E (J) = Frame (F + J));
         pragma Assert (for all J in E'Range => E (J) = Frame (F + J));
      end;
   end Lemma_Encode_Decode_Roster;

   ---------------------------------------------------------------------------
   --  REVOKE
   ---------------------------------------------------------------------------

   function Make_Revoke
     (Root_PK  : Pubkey;
      S        : Salt;
      Signer   : Pubkey;
      Cert_Cap : U48;
      Cert_Sig : Sig;
      Sign_PK  : Pubkey;
      From_T   : U48) return Revoke_Record is
   begin
      return
        (C         =>
           (NS       => Collection_Id (Root_PK, S),
            Root_PK  => Root_PK,
            Salt     => S,
            Signer   => Signer,
            Cert_Cap => Cert_Cap,
            Cert_Sig => Cert_Sig,
            Sign_PK  => Sign_PK,
            From_T   => From_T),
         Signature => [others => 0]);
   end Make_Revoke;

   function Content_Bytes (C : Revoke_Content) return Byte_Array is
      B : constant Byte_Array (0 .. Revoke_Content_Len - 1) :=
        [for J in 0 .. Revoke_Content_Len - 1 => Content_Byte (C, J)];
   begin
      return B;
   end Content_Bytes;

   function Encode (R : Revoke_Record) return Byte_Array is
      B : constant Byte_Array (0 .. Revoke_Frame_Len - 1) :=
        [for J in 0 .. Revoke_Frame_Len - 1 => Frame_Byte (R, J)];
      CB : constant Byte_Array := Content_Bytes (R.C) with Ghost;
   begin
      pragma Assert (for all J in 0 .. Revoke_Content_Len - 1 => B (J) = CB (J));
      return B;
   end Encode;

   function Parse_Revoke (Frame : Byte_Array) return Revoke_Record is
      F : constant Natural := Frame'First;
   begin
      return
        (C         =>
           (NS       => [for I in NS_Id'Range => Frame (F + Revoke_O_NS + I)],
            Root_PK  => [for I in Pubkey'Range => Frame (F + Revoke_O_Root_PK + I)],
            Salt     => [for I in Salt'Range => Frame (F + Revoke_O_Salt + I)],
            Signer   => [for I in Pubkey'Range => Frame (F + Revoke_O_Signer + I)],
            Cert_Cap => U48_At (Frame, F + Revoke_O_Cert_Cap),
            Cert_Sig => [for I in Sig'Range => Frame (F + Revoke_O_Cert_Sig + I)],
            Sign_PK  => [for I in Pubkey'Range => Frame (F + Revoke_O_Sign_PK + I)],
            From_T   => U48_At (Frame, F + Revoke_O_From_T)),
         Signature => [for I in Sig'Range => Frame (F + Revoke_Content_Len + I)]);
   end Parse_Revoke;

   procedure Decode (Frame : Byte_Array; R : in out Revoke_Record; Result : out Status) is
   begin
      if Is_Revoke_Frame (Frame) then
         R := Parse_Revoke (Frame);
         Result := OK;
      else
         Result := Malformed;
      end if;
   end Decode;

   procedure Decode_Verified
     (Frame : Byte_Array; R : in out Revoke_Record; Result : out Status) is
   begin
      Result := Malformed;
      if Is_Revoke_Frame (Frame) then
         declare
            P : constant Revoke_Record := Parse_Revoke (Frame);
         begin
            if Well_Formed (P) then
               R := P;
               Result := OK;
            end if;
         end;
      end if;
   end Decode_Verified;

   procedure Sign (R : in out Revoke_Record; SK : Kome.Crypto.Secret_Key) is
   begin
      R.Signature := Kome.Crypto.Sign (SK, Hash (R.C));
   end Sign;

   procedure Lemma_Header_Canonical (R : Revoke_Record) is null;

   procedure Lemma_Revoke_Ints (R : Revoke_Record) with
     Ghost, Global => null,
     Post => Is_Revoke_Frame (Encode (R))
             and then Parse_Revoke (Encode (R)).C.Cert_Cap = R.C.Cert_Cap
             and then Parse_Revoke (Encode (R)).C.From_T = R.C.From_T;

   procedure Lemma_Revoke_Ints (R : Revoke_Record) is
      E : constant Byte_Array := Encode (R);
   begin
      pragma Assert (E'First = 0 and then E'Length = Revoke_Frame_Len);
      pragma Assert (E (0) = Tag_Revoke);
      pragma Assert (Is_Revoke_Frame (E));
      pragma Assert (E (Revoke_O_Cert_Cap) = Byte_Of_U48 (R.C.Cert_Cap, 0));
      pragma Assert (E (Revoke_O_Cert_Cap + 1) = Byte_Of_U48 (R.C.Cert_Cap, 1));
      pragma Assert (E (Revoke_O_Cert_Cap + 2) = Byte_Of_U48 (R.C.Cert_Cap, 2));
      pragma Assert (E (Revoke_O_Cert_Cap + 3) = Byte_Of_U48 (R.C.Cert_Cap, 3));
      pragma Assert (E (Revoke_O_Cert_Cap + 4) = Byte_Of_U48 (R.C.Cert_Cap, 4));
      pragma Assert (E (Revoke_O_Cert_Cap + 5) = Byte_Of_U48 (R.C.Cert_Cap, 5));
      Lemma_U48_Round_Trip (R.C.Cert_Cap);
      pragma Assert (U48_At (E, Revoke_O_Cert_Cap) = R.C.Cert_Cap);
      pragma Assert (E (Revoke_O_From_T) = Byte_Of_U48 (R.C.From_T, 0));
      pragma Assert (E (Revoke_O_From_T + 1) = Byte_Of_U48 (R.C.From_T, 1));
      pragma Assert (E (Revoke_O_From_T + 2) = Byte_Of_U48 (R.C.From_T, 2));
      pragma Assert (E (Revoke_O_From_T + 3) = Byte_Of_U48 (R.C.From_T, 3));
      pragma Assert (E (Revoke_O_From_T + 4) = Byte_Of_U48 (R.C.From_T, 4));
      pragma Assert (E (Revoke_O_From_T + 5) = Byte_Of_U48 (R.C.From_T, 5));
      Lemma_U48_Round_Trip (R.C.From_T);
      pragma Assert (U48_At (E, Revoke_O_From_T) = R.C.From_T);
   end Lemma_Revoke_Ints;

   procedure Lemma_Decode_Encode (R : Revoke_Record) is
   begin
      Lemma_Revoke_Ints (R);
      declare
         E : constant Byte_Array    := Encode (R);
         P : constant Revoke_Record := Parse_Revoke (E);
      begin
         pragma Assert (for all I in NS_Id'Range => P.C.NS (I) = E (Revoke_O_NS + I));
         pragma Assert (for all I in NS_Id'Range => E (Revoke_O_NS + I) = R.C.NS (I));
         pragma Assert (for all I in NS_Id'Range => P.C.NS (I) = R.C.NS (I));
         pragma Assert (for all I in Pubkey'Range => P.C.Root_PK (I) = E (Revoke_O_Root_PK + I));
         pragma Assert (for all I in Pubkey'Range => E (Revoke_O_Root_PK + I) = R.C.Root_PK (I));
         pragma Assert (for all I in Pubkey'Range => P.C.Root_PK (I) = R.C.Root_PK (I));
         pragma Assert (for all I in Salt'Range => P.C.Salt (I) = E (Revoke_O_Salt + I));
         pragma Assert (for all I in Salt'Range => E (Revoke_O_Salt + I) = R.C.Salt (I));
         pragma Assert (for all I in Salt'Range => P.C.Salt (I) = R.C.Salt (I));
         pragma Assert (for all I in Pubkey'Range => P.C.Signer (I) = E (Revoke_O_Signer + I));
         pragma Assert (for all I in Pubkey'Range => E (Revoke_O_Signer + I) = R.C.Signer (I));
         pragma Assert (for all I in Pubkey'Range => P.C.Signer (I) = R.C.Signer (I));
         pragma Assert (for all I in Sig'Range => P.C.Cert_Sig (I) = E (Revoke_O_Cert_Sig + I));
         pragma Assert (for all I in Sig'Range => E (Revoke_O_Cert_Sig + I) = R.C.Cert_Sig (I));
         pragma Assert (for all I in Sig'Range => P.C.Cert_Sig (I) = R.C.Cert_Sig (I));
         pragma Assert (for all I in Pubkey'Range => P.C.Sign_PK (I) = E (Revoke_O_Sign_PK + I));
         pragma Assert (for all I in Pubkey'Range => E (Revoke_O_Sign_PK + I) = R.C.Sign_PK (I));
         pragma Assert (for all I in Pubkey'Range => P.C.Sign_PK (I) = R.C.Sign_PK (I));
         pragma Assert (for all I in Sig'Range =>
                          P.Signature (I) = E (Revoke_Content_Len + I));
         pragma Assert (for all I in Sig'Range =>
                          E (Revoke_Content_Len + I) = R.Signature (I));
         pragma Assert (P.C = R.C);
         pragma Assert (P = R);
      end;
   end Lemma_Decode_Encode;

   procedure Lemma_Revoke_ED_Head (Frame : Byte_Array) with
     Ghost, Global => null,
     Pre  => Is_Revoke_Frame (Frame),
     Post => Encode (Parse_Revoke (Frame))'First = 0
             and then Encode (Parse_Revoke (Frame))'Length = Frame'Length
             and then Same_At (Frame, Encode (Parse_Revoke (Frame)),
                               0, Revoke_O_Sign_PK - 1);

   procedure Lemma_Revoke_ED_Head (Frame : Byte_Array) is
      F : constant Natural       := Frame'First;
      P : constant Revoke_Record := Parse_Revoke (Frame);
      E : constant Byte_Array    := Encode (P);
   begin
      Lemma_U48_Bytes_Round_Trip
        (Frame (F + Revoke_O_Cert_Cap), Frame (F + Revoke_O_Cert_Cap + 1), Frame (F + Revoke_O_Cert_Cap + 2),
         Frame (F + Revoke_O_Cert_Cap + 3), Frame (F + Revoke_O_Cert_Cap + 4), Frame (F + Revoke_O_Cert_Cap + 5));
      pragma Assert (E'First = 0 and then E'Length = Frame'Length);
      pragma Assert (E (0) = Frame (F));
      pragma Assert (for all J in Revoke_O_NS .. Revoke_O_Root_PK - 1 => E (J) = Frame (F + J));
      pragma Assert (for all J in Revoke_O_Root_PK .. Revoke_O_Salt - 1 => E (J) = Frame (F + J));
      pragma Assert (for all J in Revoke_O_Salt .. Revoke_O_Signer - 1 => E (J) = Frame (F + J));
      pragma Assert (for all J in Revoke_O_Signer .. Revoke_O_Cert_Cap - 1 => E (J) = Frame (F + J));
      pragma Assert (E (Revoke_O_Cert_Cap) = Frame (F + Revoke_O_Cert_Cap));
      pragma Assert (E (Revoke_O_Cert_Cap + 1) = Frame (F + Revoke_O_Cert_Cap + 1));
      pragma Assert (E (Revoke_O_Cert_Cap + 2) = Frame (F + Revoke_O_Cert_Cap + 2));
      pragma Assert (E (Revoke_O_Cert_Cap + 3) = Frame (F + Revoke_O_Cert_Cap + 3));
      pragma Assert (E (Revoke_O_Cert_Cap + 4) = Frame (F + Revoke_O_Cert_Cap + 4));
      pragma Assert (E (Revoke_O_Cert_Cap + 5) = Frame (F + Revoke_O_Cert_Cap + 5));
      pragma Assert (for all J in Revoke_O_Cert_Sig .. Revoke_O_Sign_PK - 1 => E (J) = Frame (F + J));
      pragma Assert (for all J in 0 .. Revoke_O_Sign_PK - 1 => E (J) = Frame (F + J));
   end Lemma_Revoke_ED_Head;

   procedure Lemma_Revoke_ED_Tail (Frame : Byte_Array) with
     Ghost, Global => null,
     Pre  => Is_Revoke_Frame (Frame)
             and then Encode (Parse_Revoke (Frame))'First = 0
             and then Encode (Parse_Revoke (Frame))'Length = Frame'Length,
     Post => Same_At (Frame, Encode (Parse_Revoke (Frame)),
                      Revoke_O_Sign_PK, Revoke_Frame_Len - 1);

   procedure Lemma_Revoke_ED_Tail (Frame : Byte_Array) is
      F  : constant Natural       := Frame'First;
      P  : constant Revoke_Record := Parse_Revoke (Frame);
      E  : constant Byte_Array    := Encode (P);
   begin
      Lemma_U48_Bytes_Round_Trip
        (Frame (F + Revoke_O_From_T), Frame (F + Revoke_O_From_T + 1), Frame (F + Revoke_O_From_T + 2),
         Frame (F + Revoke_O_From_T + 3), Frame (F + Revoke_O_From_T + 4), Frame (F + Revoke_O_From_T + 5));
      pragma Assert (for all J in Revoke_O_Sign_PK .. Revoke_O_From_T - 1 => E (J) = Frame (F + J));
      pragma Assert (E (Revoke_O_From_T) = Frame (F + Revoke_O_From_T));
      pragma Assert (E (Revoke_O_From_T + 1) = Frame (F + Revoke_O_From_T + 1));
      pragma Assert (E (Revoke_O_From_T + 2) = Frame (F + Revoke_O_From_T + 2));
      pragma Assert (E (Revoke_O_From_T + 3) = Frame (F + Revoke_O_From_T + 3));
      pragma Assert (E (Revoke_O_From_T + 4) = Frame (F + Revoke_O_From_T + 4));
      pragma Assert (E (Revoke_O_From_T + 5) = Frame (F + Revoke_O_From_T + 5));
      pragma Assert (for all J in Revoke_Content_Len .. Revoke_Frame_Len - 1 => E (J) = Frame (F + J));
      pragma Assert (for all J in Revoke_O_Sign_PK .. Revoke_Frame_Len - 1 => E (J) = Frame (F + J));
   end Lemma_Revoke_ED_Tail;

   procedure Lemma_Encode_Decode_Revoke (Frame : Byte_Array) is
      F : constant Natural := Frame'First;
   begin
      Lemma_Revoke_ED_Head (Frame);
      Lemma_Revoke_ED_Tail (Frame);
      declare
         E : constant Byte_Array := Encode (Parse_Revoke (Frame));
      begin
         pragma Assert (for all J in 0 .. Revoke_O_Sign_PK - 1 => E (J) = Frame (F + J));
         pragma Assert (for all J in Revoke_O_Sign_PK .. Revoke_Frame_Len - 1 =>
                          E (J) = Frame (F + J));
         pragma Assert (for all J in E'Range => E (J) = Frame (F + J));
      end;
   end Lemma_Encode_Decode_Revoke;

   ---------------------------------------------------------------------------
   --  GRANT
   ---------------------------------------------------------------------------

   function Make_Grant
     (Root_PK  : Pubkey;
      S        : Salt;
      Signer   : Pubkey;
      Cert_Cap : U48;
      Cert_Sig : Sig;
      Subject  : Pubkey) return Grant_Record is
   begin
      return
        (C         =>
           (NS       => Collection_Id (Root_PK, S),
            Root_PK  => Root_PK,
            Salt     => S,
            Signer   => Signer,
            Cert_Cap => Cert_Cap,
            Cert_Sig => Cert_Sig,
            Subject  => Subject),
         Signature => [others => 0]);
   end Make_Grant;

   function Content_Bytes (C : Grant_Content) return Byte_Array is
      B : constant Byte_Array (0 .. Grant_Content_Len - 1) :=
        [for J in 0 .. Grant_Content_Len - 1 => Content_Byte (C, J)];
   begin
      return B;
   end Content_Bytes;

   function Encode (R : Grant_Record) return Byte_Array is
      B : constant Byte_Array (0 .. Grant_Frame_Len - 1) :=
        [for J in 0 .. Grant_Frame_Len - 1 => Frame_Byte (R, J)];
      CB : constant Byte_Array := Content_Bytes (R.C) with Ghost;
   begin
      pragma Assert (for all J in 0 .. Grant_Content_Len - 1 => B (J) = CB (J));
      return B;
   end Encode;

   function Parse_Grant (Frame : Byte_Array) return Grant_Record is
      F : constant Natural := Frame'First;
   begin
      return
        (C         =>
           (NS       => [for I in NS_Id'Range => Frame (F + Grant_O_NS + I)],
            Root_PK  => [for I in Pubkey'Range => Frame (F + Grant_O_Root_PK + I)],
            Salt     => [for I in Salt'Range => Frame (F + Grant_O_Salt + I)],
            Signer   => [for I in Pubkey'Range => Frame (F + Grant_O_Signer + I)],
            Cert_Cap => U48_At (Frame, F + Grant_O_Cert_Cap),
            Cert_Sig => [for I in Sig'Range => Frame (F + Grant_O_Cert_Sig + I)],
            Subject  => [for I in Pubkey'Range => Frame (F + Grant_O_Subject + I)]),
         Signature => [for I in Sig'Range => Frame (F + Grant_Content_Len + I)]);
   end Parse_Grant;

   procedure Decode (Frame : Byte_Array; R : in out Grant_Record; Result : out Status) is
   begin
      if Is_Grant_Frame (Frame) then
         R := Parse_Grant (Frame);
         Result := OK;
      else
         Result := Malformed;
      end if;
   end Decode;

   procedure Decode_Verified
     (Frame : Byte_Array; R : in out Grant_Record; Result : out Status) is
   begin
      Result := Malformed;
      if Is_Grant_Frame (Frame) then
         declare
            P : constant Grant_Record := Parse_Grant (Frame);
         begin
            if Well_Formed (P) then
               R := P;
               Result := OK;
            end if;
         end;
      end if;
   end Decode_Verified;

   procedure Sign (R : in out Grant_Record; SK : Kome.Crypto.Secret_Key) is
   begin
      R.Signature := Kome.Crypto.Sign (SK, Hash (R.C));
   end Sign;

   procedure Lemma_Header_Canonical (R : Grant_Record) is null;

   procedure Lemma_Decode_Encode (R : Grant_Record) is
      E : constant Byte_Array := Encode (R);
   begin
      pragma Assert (E'First = 0 and then E'Length = Grant_Frame_Len);
      pragma Assert (E (0) = Tag_Grant);
      pragma Assert (Is_Grant_Frame (E));
      pragma Assert (E (Grant_O_Cert_Cap) = Byte_Of_U48 (R.C.Cert_Cap, 0));
      pragma Assert (E (Grant_O_Cert_Cap + 1) = Byte_Of_U48 (R.C.Cert_Cap, 1));
      pragma Assert (E (Grant_O_Cert_Cap + 2) = Byte_Of_U48 (R.C.Cert_Cap, 2));
      pragma Assert (E (Grant_O_Cert_Cap + 3) = Byte_Of_U48 (R.C.Cert_Cap, 3));
      pragma Assert (E (Grant_O_Cert_Cap + 4) = Byte_Of_U48 (R.C.Cert_Cap, 4));
      pragma Assert (E (Grant_O_Cert_Cap + 5) = Byte_Of_U48 (R.C.Cert_Cap, 5));
      Lemma_U48_Round_Trip (R.C.Cert_Cap);
      pragma Assert (U48_At (E, Grant_O_Cert_Cap) = R.C.Cert_Cap);
      declare
         P : constant Grant_Record := Parse_Grant (E);
      begin
         pragma Assert (P.C.Cert_Cap = R.C.Cert_Cap);
         pragma Assert (for all I in NS_Id'Range => P.C.NS (I) = E (Grant_O_NS + I));
         pragma Assert (for all I in NS_Id'Range => E (Grant_O_NS + I) = R.C.NS (I));
         pragma Assert (for all I in NS_Id'Range => P.C.NS (I) = R.C.NS (I));
         pragma Assert (for all I in Pubkey'Range => P.C.Root_PK (I) = E (Grant_O_Root_PK + I));
         pragma Assert (for all I in Pubkey'Range => E (Grant_O_Root_PK + I) = R.C.Root_PK (I));
         pragma Assert (for all I in Pubkey'Range => P.C.Root_PK (I) = R.C.Root_PK (I));
         pragma Assert (for all I in Salt'Range => P.C.Salt (I) = E (Grant_O_Salt + I));
         pragma Assert (for all I in Salt'Range => E (Grant_O_Salt + I) = R.C.Salt (I));
         pragma Assert (for all I in Salt'Range => P.C.Salt (I) = R.C.Salt (I));
         pragma Assert (for all I in Pubkey'Range => P.C.Signer (I) = E (Grant_O_Signer + I));
         pragma Assert (for all I in Pubkey'Range => E (Grant_O_Signer + I) = R.C.Signer (I));
         pragma Assert (for all I in Pubkey'Range => P.C.Signer (I) = R.C.Signer (I));
         pragma Assert (for all I in Sig'Range => P.C.Cert_Sig (I) = E (Grant_O_Cert_Sig + I));
         pragma Assert (for all I in Sig'Range => E (Grant_O_Cert_Sig + I) = R.C.Cert_Sig (I));
         pragma Assert (for all I in Sig'Range => P.C.Cert_Sig (I) = R.C.Cert_Sig (I));
         pragma Assert (for all I in Pubkey'Range => P.C.Subject (I) = E (Grant_O_Subject + I));
         pragma Assert (for all I in Pubkey'Range => E (Grant_O_Subject + I) = R.C.Subject (I));
         pragma Assert (for all I in Pubkey'Range => P.C.Subject (I) = R.C.Subject (I));
         pragma Assert (for all I in Sig'Range =>
                          P.Signature (I) = E (Grant_Content_Len + I));
         pragma Assert (for all I in Sig'Range =>
                          E (Grant_Content_Len + I) = R.Signature (I));
         pragma Assert (P.C = R.C);
         pragma Assert (P = R);
      end;
   end Lemma_Decode_Encode;

   procedure Lemma_Encode_Decode_Grant (Frame : Byte_Array) is
      F : constant Natural      := Frame'First;
      P : constant Grant_Record := Parse_Grant (Frame);
      E : constant Byte_Array   := Encode (P);
   begin
      Lemma_U48_Bytes_Round_Trip
        (Frame (F + Grant_O_Cert_Cap), Frame (F + Grant_O_Cert_Cap + 1), Frame (F + Grant_O_Cert_Cap + 2),
         Frame (F + Grant_O_Cert_Cap + 3), Frame (F + Grant_O_Cert_Cap + 4), Frame (F + Grant_O_Cert_Cap + 5));
      pragma Assert (E'First = 0 and then E'Length = Frame'Length);
      pragma Assert (E (0) = Frame (F));
      pragma Assert (for all J in Grant_O_NS .. Grant_O_Root_PK - 1 => E (J) = Frame (F + J));
      pragma Assert (for all J in Grant_O_Root_PK .. Grant_O_Salt - 1 => E (J) = Frame (F + J));
      pragma Assert (for all J in Grant_O_Salt .. Grant_O_Signer - 1 => E (J) = Frame (F + J));
      pragma Assert (for all J in Grant_O_Signer .. Grant_O_Cert_Cap - 1 => E (J) = Frame (F + J));
      pragma Assert (E (Grant_O_Cert_Cap) = Frame (F + Grant_O_Cert_Cap));
      pragma Assert (E (Grant_O_Cert_Cap + 1) = Frame (F + Grant_O_Cert_Cap + 1));
      pragma Assert (E (Grant_O_Cert_Cap + 2) = Frame (F + Grant_O_Cert_Cap + 2));
      pragma Assert (E (Grant_O_Cert_Cap + 3) = Frame (F + Grant_O_Cert_Cap + 3));
      pragma Assert (E (Grant_O_Cert_Cap + 4) = Frame (F + Grant_O_Cert_Cap + 4));
      pragma Assert (E (Grant_O_Cert_Cap + 5) = Frame (F + Grant_O_Cert_Cap + 5));
      pragma Assert (for all J in Grant_O_Cert_Sig .. Grant_O_Subject - 1 => E (J) = Frame (F + J));
      pragma Assert (for all J in Grant_O_Subject .. Grant_Content_Len - 1 => E (J) = Frame (F + J));
      pragma Assert (for all J in Grant_Content_Len .. Grant_Frame_Len - 1 => E (J) = Frame (F + J));
      pragma Assert (for all J in E'Range => E (J) = Frame (F + J));
   end Lemma_Encode_Decode_Grant;

   ---------------------------------------------------------------------------
   --  Frame accessors
   ---------------------------------------------------------------------------

   procedure Lemma_Roster_Lists_DH (Frame : Byte_Array; DH : Pubkey) is
      F  : constant Natural       := Frame'First;
      P  : constant Roster_Record := Parse_Roster (Frame);
      NL : constant Link_Count    := Roster_NL (Frame);
      NM : constant Member_Count  := Roster_NM (Frame);
      OM : constant Natural       := F + Roster_O_Members (NL);
   begin
      pragma Assert (P.C.N_Members = NM);
      for I in 1 .. NM loop
         pragma Assert (for all K in Pubkey'Range =>
                          Member_DH_PK (P.C, I) (K)
                          = P.C.Members (Member_Len * (I - 1) + Pubkey_Len + K));
         pragma Assert (for all K in Pubkey'Range =>
                          P.C.Members (Member_Len * (I - 1) + Pubkey_Len + K)
                          = Frame (OM + Member_Len * (I - 1) + Pubkey_Len + K));
         pragma Assert (for all K in Pubkey'Range =>
                          Frame_DH (Frame, I) (K) = Member_DH_PK (P.C, I) (K));
         pragma Assert (Frame_DH (Frame, I) = Member_DH_PK (P.C, I));
         pragma Loop_Invariant
           (for all J in 1 .. I => Frame_DH (Frame, J) = Member_DH_PK (P.C, J));
      end loop;
      pragma Assert (for all J in 1 .. NM => Frame_DH (Frame, J) = Member_DH_PK (P.C, J));
   end Lemma_Roster_Lists_DH;

end Kome.Records;
