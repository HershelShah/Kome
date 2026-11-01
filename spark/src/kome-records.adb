--  Body of Kome.Records. Encoders are the layout read position by position
--  (Frame_Byte) into one aggregate; parsers are one aggregate per field.
--  The round-trip lemmas instantiate the encoder's per-byte Post at each
--  field's offsets (Decode o Encode) or walk the frame segment by segment
--  (Encode o Decode); the integer lanes are discharged by the u48 / u16
--  lemmas, which rest on Kome.Keys' word lemmas.
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
   begin
      return
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

   --  Lemma_Decode_Encode (PUT) is split into one helper per field so that
   --  each VC holds only Encode's and Parse_Put's Posts and one field's
   --  steps (a single body with every step timed out on the late goals).

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
   --  ROSTER
   ---------------------------------------------------------------------------

   procedure Lemma_Root_Bytes (C : Roster_Content; I : Root_Index) is null;

   procedure Lemma_Member_Bytes (C : Roster_Content; I : Member_Index) is null;

   procedure Lemma_Signer_Listed (C : Roster_Content) is
   begin
      pragma Assert
        (if C.N_Roots >= 1 then (Root (C, 1) = C.Signer) = (C.Roots (0 .. 31) = C.Signer));
      pragma Assert
        (if C.N_Roots >= 2 then (Root (C, 2) = C.Signer) = (C.Roots (32 .. 63) = C.Signer));
      pragma Assert
        (if C.N_Roots >= 3 then (Root (C, 3) = C.Signer) = (C.Roots (64 .. 95) = C.Signer));
      pragma Assert
        (if C.N_Roots = 4 then (Root (C, 4) = C.Signer) = (C.Roots (96 .. 127) = C.Signer));
   end Lemma_Signer_Listed;

   function Make_Roster
     (Root_PK   : Pubkey;
      S         : Salt;
      Signer    : Pubkey;
      Prev_H    : Hash256;
      Gen       : U48;
      Ceiling_T : U48;
      Del_TTL   : U48;
      E         : Epoch;
      Roots     : Byte_Array;
      Members   : Byte_Array) return Roster_Record
   is
      LR : constant Natural := Roots'Length;
      LM : constant Natural := Members'Length;
   begin
      return
        (C         =>
           (NS        => Collection_Id (Root_PK, S),
            Root_PK   => Root_PK,
            Salt      => S,
            Signer    => Signer,
            Prev_H    => Prev_H,
            Gen       => Gen,
            Ceiling_T => Ceiling_T,
            Del_TTL   => Del_TTL,
            Epoch     => E,
            N_Roots   => LR / Pubkey_Len,
            Roots     => [for I in Roots_Bytes'Range =>
                            (if I < LR then Roots (Roots'First + I) else 0)],
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
      NR : constant Root_Count   := Roster_NR (Frame);
      NM : constant Member_Count := Roster_NM (Frame);
      OM : constant Natural      := F + Roster_O_Members (NR);
      OS : constant Natural      := OM + Member_Len * NM;
   begin
      return
        (C         =>
           (NS        => [for I in NS_Id'Range => Frame (F + Roster_O_NS + I)],
            Root_PK   => [for I in Pubkey'Range => Frame (F + Roster_O_Root_PK + I)],
            Salt      => [for I in Salt'Range => Frame (F + Roster_O_Salt + I)],
            Signer    => [for I in Pubkey'Range => Frame (F + Roster_O_Signer + I)],
            Prev_H    => [for I in Hash256'Range => Frame (F + Roster_O_Prev_H + I)],
            Gen       => U48_At (Frame, F + Roster_O_Gen),
            Ceiling_T => U48_At (Frame, F + Roster_O_Ceiling),
            Del_TTL   => U48_At (Frame, F + Roster_O_TTL),
            Epoch     => Epoch (U16_At (Frame, F + Roster_O_Epoch)),
            N_Roots   => NR,
            Roots     => [for I in Roots_Bytes'Range =>
                            (if I < Pubkey_Len * NR
                             then Frame (F + Roster_O_Roots + I) else 0)],
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

   procedure Lemma_Decode_Encode (R : Roster_Record) is
      E  : constant Byte_Array   := Encode (R);
      NR : constant Root_Count   := R.C.N_Roots;
      NM : constant Member_Count := R.C.N_Members;
      EP : constant U16_Value    := Natural (R.C.Epoch);
   begin
      pragma Assert (E'First = 0 and then E'Length = Frame_Len (R));
      pragma Assert (E (0) = Tag_Roster);
      pragma Assert (E (Roster_O_NR) = Byte (NR));
      pragma Assert (Roster_NR (E) = NR);
      pragma Assert (E (Roster_O_NM (NR)) = Byte (NM));
      pragma Assert (Roster_NM (E) = NM);
      pragma Assert (Is_Roster_Frame (E));

      pragma Assert (E (Roster_O_Epoch)     = Byte_Of_U16 (EP, 0));
      pragma Assert (E (Roster_O_Epoch + 1) = Byte_Of_U16 (EP, 1));
      Lemma_U16_Round_Trip (EP);
      pragma Assert (U16_At (E, Roster_O_Epoch) = EP);

      pragma Assert (E (Roster_O_Gen)     = Byte_Of_U48 (R.C.Gen, 0));
      pragma Assert (E (Roster_O_Gen + 1) = Byte_Of_U48 (R.C.Gen, 1));
      pragma Assert (E (Roster_O_Gen + 2) = Byte_Of_U48 (R.C.Gen, 2));
      pragma Assert (E (Roster_O_Gen + 3) = Byte_Of_U48 (R.C.Gen, 3));
      pragma Assert (E (Roster_O_Gen + 4) = Byte_Of_U48 (R.C.Gen, 4));
      pragma Assert (E (Roster_O_Gen + 5) = Byte_Of_U48 (R.C.Gen, 5));
      Lemma_U48_Round_Trip (R.C.Gen);
      pragma Assert (U48_At (E, Roster_O_Gen) = R.C.Gen);

      pragma Assert (E (Roster_O_Ceiling)     = Byte_Of_U48 (R.C.Ceiling_T, 0));
      pragma Assert (E (Roster_O_Ceiling + 1) = Byte_Of_U48 (R.C.Ceiling_T, 1));
      pragma Assert (E (Roster_O_Ceiling + 2) = Byte_Of_U48 (R.C.Ceiling_T, 2));
      pragma Assert (E (Roster_O_Ceiling + 3) = Byte_Of_U48 (R.C.Ceiling_T, 3));
      pragma Assert (E (Roster_O_Ceiling + 4) = Byte_Of_U48 (R.C.Ceiling_T, 4));
      pragma Assert (E (Roster_O_Ceiling + 5) = Byte_Of_U48 (R.C.Ceiling_T, 5));
      Lemma_U48_Round_Trip (R.C.Ceiling_T);
      pragma Assert (U48_At (E, Roster_O_Ceiling) = R.C.Ceiling_T);

      pragma Assert (E (Roster_O_TTL)     = Byte_Of_U48 (R.C.Del_TTL, 0));
      pragma Assert (E (Roster_O_TTL + 1) = Byte_Of_U48 (R.C.Del_TTL, 1));
      pragma Assert (E (Roster_O_TTL + 2) = Byte_Of_U48 (R.C.Del_TTL, 2));
      pragma Assert (E (Roster_O_TTL + 3) = Byte_Of_U48 (R.C.Del_TTL, 3));
      pragma Assert (E (Roster_O_TTL + 4) = Byte_Of_U48 (R.C.Del_TTL, 4));
      pragma Assert (E (Roster_O_TTL + 5) = Byte_Of_U48 (R.C.Del_TTL, 5));
      Lemma_U48_Round_Trip (R.C.Del_TTL);
      pragma Assert (U48_At (E, Roster_O_TTL) = R.C.Del_TTL);

      declare
         P : constant Roster_Record := Parse_Roster (E);
      begin
         pragma Assert (P.C.N_Roots = NR);
         pragma Assert (P.C.N_Members = NM);
         pragma Assert (P.C.Gen = R.C.Gen);
         pragma Assert (P.C.Ceiling_T = R.C.Ceiling_T);
         pragma Assert (P.C.Del_TTL = R.C.Del_TTL);
         pragma Assert (P.C.Epoch = R.C.Epoch);
         pragma Assert (for all I in NS_Id'Range => P.C.NS (I) = E (Roster_O_NS + I));
         pragma Assert (for all I in NS_Id'Range => E (Roster_O_NS + I) = R.C.NS (I));
         pragma Assert (for all I in NS_Id'Range => P.C.NS (I) = R.C.NS (I));
         pragma Assert (for all I in Pubkey'Range =>
                          P.C.Root_PK (I) = E (Roster_O_Root_PK + I));
         pragma Assert (for all I in Pubkey'Range =>
                          E (Roster_O_Root_PK + I) = R.C.Root_PK (I));
         pragma Assert (for all I in Pubkey'Range => P.C.Root_PK (I) = R.C.Root_PK (I));
         pragma Assert (for all I in Salt'Range => P.C.Salt (I) = E (Roster_O_Salt + I));
         pragma Assert (for all I in Salt'Range => E (Roster_O_Salt + I) = R.C.Salt (I));
         pragma Assert (for all I in Salt'Range => P.C.Salt (I) = R.C.Salt (I));
         pragma Assert (for all I in Pubkey'Range =>
                          P.C.Signer (I) = E (Roster_O_Signer + I));
         pragma Assert (for all I in Pubkey'Range =>
                          E (Roster_O_Signer + I) = R.C.Signer (I));
         pragma Assert (for all I in Pubkey'Range => P.C.Signer (I) = R.C.Signer (I));
         pragma Assert (for all I in Hash256'Range =>
                          P.C.Prev_H (I) = E (Roster_O_Prev_H + I));
         pragma Assert (for all I in Hash256'Range =>
                          E (Roster_O_Prev_H + I) = R.C.Prev_H (I));
         pragma Assert (for all I in Hash256'Range => P.C.Prev_H (I) = R.C.Prev_H (I));
         pragma Assert (for all I in Roots_Bytes'Range =>
                          (if I < Pubkey_Len * NR
                           then P.C.Roots (I) = E (Roster_O_Roots + I)));
         pragma Assert (for all I in Roots_Bytes'Range =>
                          (if I < Pubkey_Len * NR
                           then E (Roster_O_Roots + I) = R.C.Roots (I)));
         pragma Assert (for all I in Roots_Bytes'Range =>
                          (if I >= Pubkey_Len * NR
                           then P.C.Roots (I) = 0 and then R.C.Roots (I) = 0));
         pragma Assert (for all I in Roots_Bytes'Range => P.C.Roots (I) = R.C.Roots (I));
         pragma Assert (for all I in Members_Bytes'Range =>
                          (if I < Member_Len * NM
                           then P.C.Members (I) = E (Roster_O_Members (NR) + I)));
         pragma Assert (for all I in Members_Bytes'Range =>
                          (if I < Member_Len * NM
                           then E (Roster_O_Members (NR) + I) = R.C.Members (I)));
         pragma Assert (for all I in Members_Bytes'Range =>
                          P.C.Members (I) = R.C.Members (I));
         pragma Assert (for all I in Sig'Range => P.Signature (I) = R.Signature (I));
         pragma Assert (P.C = R.C);
         pragma Assert (P = R);
      end;
   end Lemma_Decode_Encode;

   --  Lemma_Encode_Decode_Roster is split into the fixed head, the member
   --  block and the signature, for the same reason as the PUT lemma above.

   --  E is Encode (Parse_Roster (Frame)), passed in so that run-time
   --  evaluation under -gnata encodes once, not once per index.
   function Roster_ED (Frame, E : Byte_Array; Lo, Hi : Natural) return Boolean is
     (for all J in Lo .. Hi => E (J) = Frame (Frame'First + J))
   with Ghost,
        Pre => Frame'Length <= Roster_Frame_Max
               and then Hi < Frame'Length
               and then E'First = 0
               and then E'Length = Frame'Length;

   procedure Lemma_Roster_ED_Head (Frame : Byte_Array) with
     Ghost, Global => null,
     Pre  => Is_Roster_Frame (Frame),
     Post => Encode (Parse_Roster (Frame))'First = 0
             and then Encode (Parse_Roster (Frame))'Length = Frame'Length
             and then Roster_ED (Frame, Encode (Parse_Roster (Frame)),
                                 0, Roster_O_Members (Roster_NR (Frame)) - 1);

   procedure Lemma_Roster_ED_Head (Frame : Byte_Array) is
      F  : constant Natural       := Frame'First;
      P  : constant Roster_Record := Parse_Roster (Frame);
      E  : constant Byte_Array    := Encode (P);
      NR : constant Root_Count    := P.C.N_Roots;
      ON : constant Natural       := Roster_O_NM (NR);
      OM : constant Natural       := Roster_O_Members (NR);
   begin
      Lemma_U16_Bytes_Round_Trip (Frame (F + Roster_O_Epoch), Frame (F + Roster_O_Epoch + 1));
      Lemma_U48_Bytes_Round_Trip
        (Frame (F + Roster_O_Gen), Frame (F + Roster_O_Gen + 1),
         Frame (F + Roster_O_Gen + 2), Frame (F + Roster_O_Gen + 3),
         Frame (F + Roster_O_Gen + 4), Frame (F + Roster_O_Gen + 5));
      Lemma_U48_Bytes_Round_Trip
        (Frame (F + Roster_O_Ceiling), Frame (F + Roster_O_Ceiling + 1),
         Frame (F + Roster_O_Ceiling + 2), Frame (F + Roster_O_Ceiling + 3),
         Frame (F + Roster_O_Ceiling + 4), Frame (F + Roster_O_Ceiling + 5));
      Lemma_U48_Bytes_Round_Trip
        (Frame (F + Roster_O_TTL), Frame (F + Roster_O_TTL + 1),
         Frame (F + Roster_O_TTL + 2), Frame (F + Roster_O_TTL + 3),
         Frame (F + Roster_O_TTL + 4), Frame (F + Roster_O_TTL + 5));
      pragma Assert (E'First = 0 and then E'Length = Frame'Length);
      pragma Assert (E (0) = Frame (F));
      pragma Assert (for all J in Roster_O_NS .. Roster_O_Root_PK - 1 =>
                       E (J) = Frame (F + J));
      pragma Assert (for all J in Roster_O_Root_PK .. Roster_O_Salt - 1 =>
                       E (J) = Frame (F + J));
      pragma Assert (for all J in Roster_O_Salt .. Roster_O_Signer - 1 =>
                       E (J) = Frame (F + J));
      pragma Assert (for all J in Roster_O_Signer .. Roster_O_Prev_H - 1 =>
                       E (J) = Frame (F + J));
      pragma Assert (for all J in Roster_O_Prev_H .. Roster_O_Gen - 1 =>
                       E (J) = Frame (F + J));
      pragma Assert (E (Roster_O_Gen)     = Frame (F + Roster_O_Gen));
      pragma Assert (E (Roster_O_Gen + 1) = Frame (F + Roster_O_Gen + 1));
      pragma Assert (E (Roster_O_Gen + 2) = Frame (F + Roster_O_Gen + 2));
      pragma Assert (E (Roster_O_Gen + 3) = Frame (F + Roster_O_Gen + 3));
      pragma Assert (E (Roster_O_Gen + 4) = Frame (F + Roster_O_Gen + 4));
      pragma Assert (E (Roster_O_Gen + 5) = Frame (F + Roster_O_Gen + 5));
      pragma Assert (E (Roster_O_Ceiling)     = Frame (F + Roster_O_Ceiling));
      pragma Assert (E (Roster_O_Ceiling + 1) = Frame (F + Roster_O_Ceiling + 1));
      pragma Assert (E (Roster_O_Ceiling + 2) = Frame (F + Roster_O_Ceiling + 2));
      pragma Assert (E (Roster_O_Ceiling + 3) = Frame (F + Roster_O_Ceiling + 3));
      pragma Assert (E (Roster_O_Ceiling + 4) = Frame (F + Roster_O_Ceiling + 4));
      pragma Assert (E (Roster_O_Ceiling + 5) = Frame (F + Roster_O_Ceiling + 5));
      pragma Assert (E (Roster_O_TTL)     = Frame (F + Roster_O_TTL));
      pragma Assert (E (Roster_O_TTL + 1) = Frame (F + Roster_O_TTL + 1));
      pragma Assert (E (Roster_O_TTL + 2) = Frame (F + Roster_O_TTL + 2));
      pragma Assert (E (Roster_O_TTL + 3) = Frame (F + Roster_O_TTL + 3));
      pragma Assert (E (Roster_O_TTL + 4) = Frame (F + Roster_O_TTL + 4));
      pragma Assert (E (Roster_O_TTL + 5) = Frame (F + Roster_O_TTL + 5));
      pragma Assert (E (Roster_O_Epoch)     = Frame (F + Roster_O_Epoch));
      pragma Assert (E (Roster_O_Epoch + 1) = Frame (F + Roster_O_Epoch + 1));
      pragma Assert (E (Roster_O_NR) = Frame (F + Roster_O_NR));
      pragma Assert (for all J in Roster_O_Roots .. ON - 1 => E (J) = Frame (F + J));
      pragma Assert (E (ON) = Frame (F + ON));
      pragma Assert (for all J in 0 .. OM - 1 => E (J) = Frame (F + J));
   end Lemma_Roster_ED_Head;

   procedure Lemma_Roster_ED_Members (Frame : Byte_Array) with
     Ghost, Global => null,
     Pre  => Is_Roster_Frame (Frame)
             and then Encode (Parse_Roster (Frame))'First = 0
             and then Encode (Parse_Roster (Frame))'Length = Frame'Length,
     Post => Roster_ED (Frame, Encode (Parse_Roster (Frame)),
                        Roster_O_Members (Roster_NR (Frame)),
                        Frame'Length - Sig_Len - 1);

   procedure Lemma_Roster_ED_Members (Frame : Byte_Array) is
      F  : constant Natural       := Frame'First;
      P  : constant Roster_Record := Parse_Roster (Frame);
      E  : constant Byte_Array    := Encode (P);
      NR : constant Root_Count    := P.C.N_Roots;
      NM : constant Member_Count  := P.C.N_Members;
      OM : constant Natural       := Roster_O_Members (NR);
      OS : constant Natural       := OM + Member_Len * NM;
   begin
      pragma Assert (NR = Roster_NR (Frame) and then NM = Roster_NM (Frame));
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
     Post => Roster_ED (Frame, Encode (Parse_Roster (Frame)),
                        Frame'Length - Sig_Len, Frame'Length - 1);

   procedure Lemma_Roster_ED_Sig (Frame : Byte_Array) is
      F  : constant Natural       := Frame'First;
      P  : constant Roster_Record := Parse_Roster (Frame);
      E  : constant Byte_Array    := Encode (P);
      NR : constant Root_Count    := P.C.N_Roots;
      NM : constant Member_Count  := P.C.N_Members;
      OS : constant Natural       := Roster_O_Members (NR) + Member_Len * NM;
   begin
      pragma Assert (NR = Roster_NR (Frame) and then NM = Roster_NM (Frame));
      pragma Assert (Content_Len (P.C) = OS);
      pragma Assert (OS = Frame'Length - Sig_Len);
      pragma Assert (for all J in OS .. OS + Sig_Len - 1 => E (J) = P.Signature (J - OS));
      pragma Assert (for all I in Sig'Range => P.Signature (I) = Frame (F + OS + I));
      pragma Assert (for all J in OS .. OS + Sig_Len - 1 => E (J) = Frame (F + J));
   end Lemma_Roster_ED_Sig;

   procedure Lemma_Encode_Decode_Roster (Frame : Byte_Array) is
      F : constant Natural := Frame'First;
   begin
      Lemma_Roster_ED_Head (Frame);
      Lemma_Roster_ED_Members (Frame);
      Lemma_Roster_ED_Sig (Frame);
      declare
         E  : constant Byte_Array := Encode (Parse_Roster (Frame));
         OM : constant Natural    := Roster_O_Members (Roster_NR (Frame));
         L  : constant Natural    := Frame'Length;
      begin
         pragma Assert (for all J in 0 .. OM - 1 => E (J) = Frame (F + J));
         pragma Assert (for all J in OM .. L - Sig_Len - 1 => E (J) = Frame (F + J));
         pragma Assert (for all J in L - Sig_Len .. L - 1 => E (J) = Frame (F + J));
         pragma Assert (for all J in E'Range => E (J) = Frame (F + J));
      end;
   end Lemma_Encode_Decode_Roster;

   ---------------------------------------------------------------------------
   --  REVOKE
   ---------------------------------------------------------------------------

   function Make_Revoke
     (Root_PK : Pubkey;
      S       : Salt;
      Signer  : Pubkey;
      Sign_PK : Pubkey;
      From_T  : U48;
      Rev_Seq : U48) return Revoke_Record is
   begin
      return
        (C         =>
           (NS      => Collection_Id (Root_PK, S),
            Root_PK => Root_PK,
            Salt    => S,
            Signer  => Signer,
            Sign_PK => Sign_PK,
            From_T  => From_T,
            Rev_Seq => Rev_Seq),
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
           (NS      => [for I in NS_Id'Range => Frame (F + Revoke_O_NS + I)],
            Root_PK => [for I in Pubkey'Range => Frame (F + Revoke_O_Root_PK + I)],
            Salt    => [for I in Salt'Range => Frame (F + Revoke_O_Salt + I)],
            Signer  => [for I in Pubkey'Range => Frame (F + Revoke_O_Signer + I)],
            Sign_PK => [for I in Pubkey'Range => Frame (F + Revoke_O_Sign_PK + I)],
            From_T  => U48_At (Frame, F + Revoke_O_From_T),
            Rev_Seq => U48_At (Frame, F + Revoke_O_Rev_Seq)),
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

   procedure Lemma_Decode_Encode (R : Revoke_Record) is
      E  : constant Byte_Array := Encode (R);
      OT : constant := Revoke_O_From_T;
      OQ : constant := Revoke_O_Rev_Seq;
   begin
      pragma Assert (E'First = 0 and then E'Length = Revoke_Frame_Len);
      pragma Assert (E (0) = Tag_Revoke);
      pragma Assert (Is_Revoke_Frame (E));

      pragma Assert (E (OT)     = Byte_Of_U48 (R.C.From_T, 0));
      pragma Assert (E (OT + 1) = Byte_Of_U48 (R.C.From_T, 1));
      pragma Assert (E (OT + 2) = Byte_Of_U48 (R.C.From_T, 2));
      pragma Assert (E (OT + 3) = Byte_Of_U48 (R.C.From_T, 3));
      pragma Assert (E (OT + 4) = Byte_Of_U48 (R.C.From_T, 4));
      pragma Assert (E (OT + 5) = Byte_Of_U48 (R.C.From_T, 5));
      Lemma_U48_Round_Trip (R.C.From_T);
      pragma Assert (U48_At (E, OT) = R.C.From_T);

      pragma Assert (E (OQ)     = Byte_Of_U48 (R.C.Rev_Seq, 0));
      pragma Assert (E (OQ + 1) = Byte_Of_U48 (R.C.Rev_Seq, 1));
      pragma Assert (E (OQ + 2) = Byte_Of_U48 (R.C.Rev_Seq, 2));
      pragma Assert (E (OQ + 3) = Byte_Of_U48 (R.C.Rev_Seq, 3));
      pragma Assert (E (OQ + 4) = Byte_Of_U48 (R.C.Rev_Seq, 4));
      pragma Assert (E (OQ + 5) = Byte_Of_U48 (R.C.Rev_Seq, 5));
      Lemma_U48_Round_Trip (R.C.Rev_Seq);
      pragma Assert (U48_At (E, OQ) = R.C.Rev_Seq);

      declare
         P : constant Revoke_Record := Parse_Revoke (E);
      begin
         pragma Assert (P.C.From_T = R.C.From_T);
         pragma Assert (P.C.Rev_Seq = R.C.Rev_Seq);
         pragma Assert (for all I in NS_Id'Range => P.C.NS (I) = R.C.NS (I));
         pragma Assert (for all I in Pubkey'Range => P.C.Root_PK (I) = R.C.Root_PK (I));
         pragma Assert (for all I in Salt'Range => P.C.Salt (I) = R.C.Salt (I));
         pragma Assert (for all I in Pubkey'Range => P.C.Signer (I) = R.C.Signer (I));
         pragma Assert (for all I in Pubkey'Range => P.C.Sign_PK (I) = R.C.Sign_PK (I));
         pragma Assert (for all I in Sig'Range => P.Signature (I) = R.Signature (I));
         pragma Assert (P.C = R.C);
         pragma Assert (P = R);
      end;
   end Lemma_Decode_Encode;

   procedure Lemma_Encode_Decode_Revoke (Frame : Byte_Array) is
      F  : constant Natural       := Frame'First;
      P  : constant Revoke_Record := Parse_Revoke (Frame);
      E  : constant Byte_Array    := Encode (P);
      OT : constant := Revoke_O_From_T;
      OQ : constant := Revoke_O_Rev_Seq;
   begin
      Lemma_U48_Bytes_Round_Trip
        (Frame (F + OT), Frame (F + OT + 1), Frame (F + OT + 2),
         Frame (F + OT + 3), Frame (F + OT + 4), Frame (F + OT + 5));
      Lemma_U48_Bytes_Round_Trip
        (Frame (F + OQ), Frame (F + OQ + 1), Frame (F + OQ + 2),
         Frame (F + OQ + 3), Frame (F + OQ + 4), Frame (F + OQ + 5));
      pragma Assert (E'First = 0 and then E'Length = Frame'Length);
      pragma Assert (E (0) = Frame (F));
      pragma Assert (for all J in Revoke_O_NS .. Revoke_O_From_T - 1 =>
                       E (J) = Frame (F + J));
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
      pragma Assert (for all J in Revoke_Content_Len .. E'Last => E (J) = Frame (F + J));
      pragma Assert (for all J in E'Range => E (J) = Frame (F + J));
   end Lemma_Encode_Decode_Revoke;

end Kome.Records;
