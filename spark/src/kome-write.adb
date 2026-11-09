pragma Ada_2022;
package body Kome.Write with SPARK_Mode is

   ----------------------
   -- Seq_Self_At_Open --
   ----------------------

   function Seq_Self_At_Open (Stored : U48; F : State; Self : Key256) return U48 is
     (U48'Max (Stored, Max_Own_Seq (F, Self).Seq));

   --------------
   -- Open_Seq --
   --------------

   procedure Open_Seq
     (Kind     : Seq_Stored;
      Stored   : U48;
      F        : State;
      Self     : Key256;
      Seq_Self : out U48;
      Result   : out Status)
   is
   begin
      case Kind is
         when Seq_None =>
            Seq_Self := Seq_Self_At_Open (0, F, Self);
            Result := OK;
         when Seq_Read =>
            Seq_Self := Seq_Self_At_Open (Stored, F, Self);
            Result := OK;
         when Seq_Torn =>
            Seq_Self := Seq_Self_At_Open (0, F, Self);
            Result := Seq_Corrupt;
      end case;
   end Open_Seq;

   -----------------
   -- Lemma_Ready --
   -----------------

   procedure Lemma_Ready (P : Prepared) is null;

   --  A Prepared that is not Ready (Len = 0).
   Blank : constant Prepared :=
     (Buf => [others => 0],
      Len => 0,
      H   => (K       => K_Put,
              NS      => (others => 0),
              Ent     => (others => 0),
              FH      => Zero_Key,
              V       => Zero_Version,
              Issuer  => Zero_Key,
              Del_TTL => 0,
              Epoch   => 0));

   -------------
   -- Prepare --
   -------------

   procedure Prepare
     (S               : in     Kome.Store.Store;
      F               : in     State;
      Op              : in     Write_Op;
      Ent             : in     Ent_Id;
      Field           : in     Byte_Array;
      Value           : in     Byte_Array;
      Now             : in     U48;
      SK              : in     Kome.Crypto.Secret_Key;
      Seq_Self        : in     U48;
      P               :    out Prepared;
      Seq_Persist     :    out U48;
      Result          :    out Status;
      Clone_Suspected :    out Boolean;
      Clamped         :    out Boolean;
      Born_Expired    :    out Boolean)
   is
      Self : constant Key256 := Self_Of (SK);
      Tgt  : constant Target := Target_Of (S, Op, Ent, Field);
      NS_B : constant NS_Id  := Kome.Records.Collection_Id (Root_Key (S), Salt_Of (S));
      Sq_S : U48 := Seq_Self;
      T    : U48;
      Seq  : U48;
      Res  : Status;
   begin
      Lemma_Valid_Facts (S, F);
      P := Blank;
      Seq_Persist := Seq_Self;

      --  Step 1: Choose (no h).
      Choose (F, Tgt, Now, Expire_Mark (S), Kome.Views.Del_TTL_Eff (F), Self,
              Sq_S, T, Seq, Res, Clone_Suspected, Clamped, Born_Expired);
      if Res not in OK | Shadowed then
         Result := Res;
         return;
      end if;

      --  Steps 2 and 3: build the record with (T, Seq), sign it, encode it.
      if Op = W_Put then
         declare
            R : Kome.Records.Put_Record :=
              Kome.Records.Make_Put (NS_B, Ent, Field, T, Seq,
                                     Kome.Crypto.Public_Of (SK), Value);
         begin
            Kome.Records.Sign (R, SK);
            declare
               Fr : constant Byte_Array := Kome.Records.Encode (R);
            begin
               P.Buf (0 .. Fr'Length - 1) := Fr;
               P.Len := Fr'Length;
            end;
         end;
      else
         declare
            R : Kome.Records.Del_Record :=
              Kome.Records.Make_Del (NS_B, Ent, T, Seq, Kome.Crypto.Public_Of (SK));
         begin
            Kome.Records.Sign (R, SK);
            declare
               Fr : constant Byte_Array := Kome.Records.Encode (R);
            begin
               P.Buf (0 .. Fr'Length - 1) := Fr;
               P.Len := Fr'Length;
            end;
         end;
      end if;

      --  The self check (see the header): the bytes verify, and they
      --  decode to the record of the choice.
      if P.Len in Frame_Size and then Verified (Frame_Of (P)) then
         declare
            H : constant Header := Header_Of (Frame_Of (P));
         begin
            Lemma_Header_Of (Frame_Of (P));
            Lemma_Verified_Canonical (Frame_Of (P));
            if H = Kome.Emit.To_Header (Tgt, Stamp (T, Self, Seq, H.V.H)) then
               P.H := H;
               pragma Assert (Ready (P));
               if Res = OK then
                  Lemma_OK_Undominated (F, Tgt, T, Self, Seq, H.V.H);
               end if;
               pragma Assert
                 (if Floor (F, Tgt).Present
                    and then Floor (F, Tgt).V.T < Eff_Ceil (F, Self)
                  then Prefix_Lt (Floor (F, Tgt).V, Stamp (T, Self, Seq, H.V.H)));
               Seq_Persist := Seq;
               Result := Res;
               return;
            end if;
         end;
      end if;

      P := Blank;
      Result := Malformed;
      Clamped := False;
      Born_Expired := False;
   end Prepare;

   ------------
   -- Commit --
   ------------

   procedure Commit
     (S      : in out Kome.Store.Store;
      F      : in out State;
      P      : in     Prepared;
      Off    :    out Log_Size;
      Result :    out Status)
   is
   begin
      Lemma_Ready (P);
      Put_Frame (S, F, Frame_Of (P), Rec (P), Off, Result);
   end Commit;

   -------------
   -- Receive --
   -------------

   procedure Receive
     (S               : in out Kome.Store.Store;
      F               : in out State;
      Frame           : in     Byte_Array;
      H               : in     Header;
      Self            : in     Key256;
      Off             :    out Log_Size;
      Result          :    out Status;
      Clone_Suspected :    out Boolean)
   is
      Was_Held : constant Boolean       := Holds (F, H);
      Hz       : constant Horizon_Value := Horizon (S);
   begin
      Put_Frame (S, F, Frame, H, Off, Result);
      Clone_Suspected := Own_Arrival (H, Self, Result, Was_Held, Hz);
   end Receive;

end Kome.Write;
