pragma Ada_2022;
package body Kome.Write with SPARK_Mode is

   --  S16 under Store.Valid: seq_self bounds every held own seq, so the
   --  next seq is seq_self + 1 (Choose makes no H8 jump).
   procedure Lemma_Seq_Base (S : Kome.Store.Store; F : State) with
     Ghost, Global => null,
     Pre  => Valid (S, F),
     Post => (for all I in 1 .. Count (F) =>
                (if Own (Held (F, I), Self_Key (S)) then Held (F, I).V.Seq <= Seq_Self (S)))
             and then Seq_Base (Seq_Self (S), Max_Own_Seq (F, Self_Key (S))) = Seq_Self (S)
             and then not Clone_Detected (Seq_Self (S), Max_Own_Seq (F, Self_Key (S)))
   is
      --  Proved; at run time the invariant would cost O(n^2) per write.
      pragma Assertion_Policy (Loop_Invariant => Ignore);
   begin
      for I in 1 .. Count (F) loop
         if Own (Held (F, I), Self_Key (S)) then
            Lemma_Seq_Self (S, F, I);
         end if;
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              (if Own (Held (F, I2), Self_Key (S)) then Held (F, I2).V.Seq <= Seq_Self (S)));
      end loop;
   end Lemma_Seq_Base;

   --  Step 4 of Write: Store.Put_Frame of the device's own new record H
   --  (admitted, not held, undominated, seq = seq_self + 1), with the Post
   --  of Put_Frame read off in this small context.
   procedure Apply_Own
     (S      : in out Kome.Store.Store;
      F      : in out State;
      Frame  : in     Byte_Array;
      H      : in     Header;
      Result :    out Status)
   with
     Global => null,
     Pre  => Valid (S, F)
       and then Frame'Length in Frame_Size
       and then Verified (Cid (S), Root_Key (S), Frame)
       and then Header_Of (Cid (S), Frame) = H
       and then Is_Data (H) and then H.V.Author = Self_Key (S)
       and then Seq_Self (S) < U48'Last and then H.V.Seq = Seq_Self (S) + 1
       and then Admitted (F, H) and then not Holds (F, H) and then not Dom (F, H),
     Post => Valid (S, F)
       and Same_Identity (S'Old, S)
       and Pinned (S) = Pinned (S'Old)
       and Log_Extends (S'Old, S)
       and Result in OK | No_Space | Log_Full
       and (if Result /= OK then Unchanged (F'Old, F) and then S = S'Old)
       and (if Result = No_Space then Data_Full (F'Old, H))
       and (if Result = Log_Full then Effective (F'Old, Del_TTL (S'Old), H))
       and (if Result = OK then
              (if Effective (F'Old, Del_TTL (S'Old), H)
               then Applied_H (F'Old, F, H, Del_TTL (S))
                    and then Seq_Self (S) = H.V.Seq
                    and then Log_Entries (S) = Log_Entries (S'Old) + 1
               else Unchanged (F'Old, F) and then S = S'Old))
   is
      Off : Log_Size;
   begin
      pragma Assert (Seq_After (S, H) = H.V.Seq);
      Put_Frame (S, F, Frame, H, Off, Result);
   end Apply_Own;

   -----------
   -- Write --
   -----------

   procedure Write
     (S       : in out Kome.Store.Store;
      F       : in out State;
      Op      : in     Write_Op;
      Ent     : in     Ent_Id;
      Field   : in     Byte_Array;
      Value   : in     Byte_Array;
      Now     : in     U48;
      SK      : in     Kome.Crypto.Secret_Key;
      Rec     :    out Header;
      Result  :    out Status;
      Clamped :    out Boolean)
   is
      Self : constant Key256 := Self_Of (SK);
      Tgt  : constant Target := Target_Of (Op, Ent, Field);
      SS0  : constant U48    := Seq_Self (S);
      Sq_S : U48 := SS0;
      T    : U48;
      Seq  : U48;
      Res  : Status;
      Cl   : Boolean;
      Buf  : Byte_Array (0 .. Kome.Records.Frame_Max - 1) := [others => 0];
      Len  : Natural;
   begin
      Lemma_Valid_Facts (S, F);
      Lemma_Seq_Base (S, F);
      Rec := Kome.Emit.To_Header (Tgt, Stamp (0, Self, 0, Zero_Key));

      --  Step 1: Choose (no h).
      Choose (F, Tgt, Now, Self, Sq_S, T, Seq, Res, Cl, Clamped);
      if Res in Inadmissible | Seq_Exhausted then
         Result := Res;
         Lemma_Unchanged_Refl (F);
         return;
      end if;
      pragma Assert (Seq = SS0 + 1);
      Rec := Kome.Emit.To_Header (Tgt, Stamp (T, Self, Seq, Zero_Key));
      if Res = Shadowed then
         --  S17: a refusal; nothing is built or signed.
         Result := Shadowed;
         Lemma_Unchanged_Refl (F);
         return;
      end if;

      --  Steps 2 and 3: build the record with (T, Seq), sign it, encode it.
      if Op = W_Put then
         declare
            R : Kome.Records.Put_Record :=
              Kome.Records.Make_Put (Cid (S), Ent, Field, T, Seq,
                                     Kome.Crypto.Public_Of (SK), Value);
         begin
            Kome.Records.Sign (Cid (S), R, SK);
            declare
               Fr : constant Byte_Array := Kome.Records.Encode (R);
            begin
               Buf (0 .. Fr'Length - 1) := Fr;
               Len := Fr'Length;
            end;
         end;
      else
         declare
            R : Kome.Records.Del_Record :=
              Kome.Records.Make_Del (Cid (S), Ent, T, Seq, Kome.Crypto.Public_Of (SK));
         begin
            Kome.Records.Sign (Cid (S), R, SK);
            declare
               Fr : constant Byte_Array := Kome.Records.Encode (R);
            begin
               Buf (0 .. Fr'Length - 1) := Fr;
               Len := Fr'Length;
            end;
         end;
      end if;

      --  The self check (see the header): the bytes verify, and they decode
      --  to the record of the choice.
      if Len in Frame_Size and then Verified (Cid (S), Root_Key (S), Buf (0 .. Len - 1)) then
         declare
            H : constant Header := Header_Of (Cid (S), Buf (0 .. Len - 1));
         begin
            Lemma_Header_Of (Cid (S), Buf (0 .. Len - 1));
            Lemma_Verified_Canonical (Cid (S), Root_Key (S), Buf (0 .. Len - 1));
            if H = Kome.Emit.To_Header (Tgt, Stamp (T, Self, Seq, H.V.H)) then
               Rec := H;
               Lemma_OK_Undominated (F, Tgt, T, Self, Seq, H.V.H);
               pragma Assert (not Holds (F, H));
               pragma Assert
                 (if Floor (F, Tgt).Present
                    and then Floor (F, Tgt).V.T < Eff_Ceil (F, Self)
                  then Prefix_Lt (Floor (F, Tgt).V, Stamp (T, Self, Seq, Zero_Key)));
               pragma Assert (Is_Data (H) and then H.V.Author = Self_Key (S)
                              and then H.V.Seq = Seq_Self (S) + 1);
               Apply_Own (S, F, Buf (0 .. Len - 1), H, Result);
               return;
            end if;
         end;
      end if;

      Result := Malformed;
      Lemma_Unchanged_Refl (F);
   end Write;

   -------------
   -- Receive --
   -------------

   procedure Receive
     (S               : in out Kome.Store.Store;
      F               : in out State;
      Frame           : in     Byte_Array;
      H               : in     Header;
      Off             :    out Log_Size;
      Result          :    out Status;
      Clone_Suspected :    out Boolean)
   is
      Own_Change : constant Boolean :=
        Own (H, Self_Key (S)) and then Effective (F, Del_TTL (S), H);
   begin
      Put_Frame (S, F, Frame, H, Off, Result);
      Clone_Suspected := Own_Change and then Result = OK;
   end Receive;

   ------------------
   -- Receive_Ceil --
   ------------------

   procedure Receive_Ceil
     (S             : in out Kome.Store.Store;
      F             : in out State;
      Frame         : in     Byte_Array;
      Off           :    out Log_Size;
      Result        :    out Status;
      Suspect_Relay :    out Boolean)
   is
   begin
      if not Ceil_Frame_Verified (S, Frame) then
         Off := Log_Length (S);
         Result := Malformed;
         Suspect_Relay := False;
         Lemma_Unchanged_Refl (F);
         return;
      end if;
      declare
         H    : constant Header := Header_Of (Cid (S), Frame);
         Void : constant Boolean := Kome.Views.Root_Void (F, H.Issuer);
      begin
         --  A ROSTER frame has the kind K_Roster, and so has its header.
         Lemma_Header_Of (Cid (S), Frame);
         pragma Assert (H.K = K_Roster);
         Put_Ceil (S, F, Frame, H, Off, Result);
         Suspect_Relay := Result = Ceil_Only and then Void;
      end;
   end Receive_Ceil;

end Kome.Write;
