--  Test main for Kome.Records (DESIGN.md §2, §3, T13). Every kind is
--  encoded, decoded and verified at its extreme sizes (empty value,
--  40 960-byte value, 32-byte field, 15 links, 64 members, u48 at 0 and
--  2**48 - 1); truncated, oversized, mistagged and out-of-bound frames are
--  refused with the record unchanged; a tampered signature, content byte
--  or ns is refused by Well_Formed. The signer block (D1): an outsider-
--  signed ROSTER, REVOKE or GRANT is Malformed (the review blocker,
--  reproduced), a certified root's records are well-formed and its roster
--  above cert_cap is not, a certificate for another ns or cap is refused,
--  a nonzero block for the founding key is refused, and a REVOKE of
--  root_pk is refused. E5: del_ttl outside the clamp and a dh_pk or box_pk
--  that is p or low order are Malformed. D12: vlen 40 960 decodes and
--  40 961 is refused. The header fields are as DESIGN.md §3 /
--  Kome.Headers say, checked against values computed here from the frame
--  bytes (not through Kome.Records.Hash), and satisfy
--  Kome.Headers.Canonical (D3). Known answers in vectors/records.txt pin
--  each layout, h and the certificate hash independently of this package.
--  Compiled with -gnata, so every Pre / Post and the ghost lemmas are also
--  executed on these records.
pragma Ada_2022;
with Ada.Text_IO;      use Ada.Text_IO;
with Ada.Command_Line; use Ada.Command_Line;
with Ada.Directories;
with Kome;             use Kome;
with Kome.Headers;     use Kome.Headers;
with Kome.Keys;        use Kome.Keys;
with Kome.Crypto;
with Kome.Records;     use Kome.Records;

procedure Test_Records with SPARK_Mode => Off is

   Failed : Boolean := False;

   procedure Check (Name : String; Cond : Boolean) is
   begin
      Put_Line ((if Cond then "PASS " else "FAIL ") & Name);
      if not Cond then
         Failed := True;
      end if;
   end Check;

   --  Deterministic filler: byte I is (Seed + 7 * I) mod 256.
   function Fill (Len : Natural; Seed : Natural) return Byte_Array is
     ([for I in 0 .. Len - 1 => Byte ((Seed + 7 * I) mod 256)]);

   function Seed_Of (N : Natural) return Kome.Crypto.Seed is
     (Kome.Crypto.Seed (Fill (Kome.Crypto.Seed_Len, N)));

   --  A reduced X25519 encoding that is not low order: filler with the top
   --  byte cleared to below 16#40#.
   function Good_DH (Seed : Natural) return Pubkey is
      K : Pubkey := Pubkey (Fill (Pubkey_Len, Seed));
   begin
      K (31) := K (31) and 16#3F#;
      return K;
   end Good_DH;

   --  N members { sign_pk dh_pk nonce box }, each dh_pk a good key.
   function Members_Of (N : Natural; Seed : Natural) return Byte_Array is
      B : Byte_Array := Fill (N * Member_Len, Seed);
   begin
      for I in 0 .. N - 1 loop
         B (I * Member_Len + Pubkey_Len + 31) := B (I * Member_Len + Pubkey_Len + 31) and 16#3F#;
      end loop;
      return B;
   end Members_Of;

   --  Big-endian u48, written independently of Kome.Records.
   function BE48 (V : U48) return Byte_Array is
     ([for I in 0 .. 5 => Byte ((V / 2 ** (8 * (5 - I))) mod 256)]);

   function H_Of (Frame : Byte_Array) return Key256 is
     (To_Key256 (Kome.Crypto.Blake2b_256 (Frame (Frame'First .. Frame'Last - Sig_Len))));

   function From_Hex (S : String) return Byte_Array is
      function Nib (C : Character) return Byte is
        (case C is
            when '0' .. '9' => Character'Pos (C) - Character'Pos ('0'),
            when 'a' .. 'f' => Character'Pos (C) - Character'Pos ('a') + 10,
            when 'A' .. 'F' => Character'Pos (C) - Character'Pos ('A') + 10,
            when others     => 0);
   begin
      return [for I in 0 .. S'Length / 2 - 1 =>
                Nib (S (S'First + 2 * I)) * 16 + Nib (S (S'First + 2 * I + 1))];
   end From_Hex;

   --  check.sh runs the binary from spark; tolerate bin/<module> too.
   function Find (Rel : String) return String is
   begin
      if Ada.Directories.Exists (Rel) then
         return Rel;
      elsif Ada.Directories.Exists ("../" & Rel) then
         return "../" & Rel;
      elsif Ada.Directories.Exists ("../../" & Rel) then
         return "../../" & Rel;
      else
         return Rel;
      end if;
   end Find;

   Author_SK, Other_SK, Root_SK : Kome.Crypto.Secret_Key;
   Author_PK, Other_PK, Root_PK : Pubkey;

   Salt_A : constant Salt := Salt (Fill (Salt_Len, 90));
   Salt_B : constant Salt := Salt (Fill (Salt_Len, 91));
   NS_A   : NS_Id;
   NS_B   : NS_Id;
   Ent_A  : constant Ent_Id := Ent_Id (Fill (Ent_Len, 40));

   Max_U48 : constant U48 := U48'Last;
   Day     : constant U48 := 86_400_000;
   TTL_OK  : constant U48 := 30 * Day;

   --  X25519 encodings refused at decode (E5): p itself (not reduced) and
   --  low-order points.
   P_Enc   : constant Pubkey := Pubkey (From_Hex
     ("edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f"));
   Order_8 : constant Pubkey := Pubkey (From_Hex
     ("e0eb7a7c3b41b8ae1656e3faf19fc46ada098deb9c32b1fd866205165f49b800"));
   U_One   : constant Pubkey := [0 => 1, others => 0];
   U_Zero  : constant Pubkey := [others => 0];

   --  The certified secondary root: Other_PK, certified by the founding key
   --  for NS_A up to Cap_2.
   Cap_2  : constant U48 := 10_000;
   Cert_2 : Sig;

   Box_A  : constant Pubkey := Good_DH (15);

begin
   Kome.Crypto.Key_Pair (Seed_Of (1), Author_SK, Author_PK);
   Kome.Crypto.Key_Pair (Seed_Of (2), Other_SK, Other_PK);
   Kome.Crypto.Key_Pair (Seed_Of (3), Root_SK, Root_PK);
   NS_A := Collection_Id (Root_PK, Salt_A);
   NS_B := Collection_Id (Root_PK, Salt_B);
   Cert_2 := Make_Cert (Root_SK, NS_A, Other_PK, Cap_2);

   ---------------------------------------------------------------------------
   --  Integer codecs.
   ---------------------------------------------------------------------------
   declare
      Ok : Boolean := True;
      Vs : constant array (1 .. 6) of U48 :=
        [0, 1, 255, 16#0102_0304_0506#, 2 ** 32, Max_U48];
   begin
      for V of Vs loop
         Lemma_U48_Round_Trip (V);
         declare
            B : constant Byte_Array := BE48 (V);
         begin
            for K in U48_Lane loop
               Ok := Ok and then Byte_Of_U48 (V, K) = B (K);
            end loop;
            Ok := Ok and then U48_Of (B (0), B (1), B (2), B (3), B (4), B (5)) = V;
            Lemma_U48_Bytes_Round_Trip (B (0), B (1), B (2), B (3), B (4), B (5));
         end;
      end loop;
      for V in U16_Value range 0 .. 2 ** 16 - 1 loop
         Lemma_U16_Round_Trip (V);
         Ok := Ok and then Byte_Of_U16 (V, 0) = Byte (V / 256)
                  and then Byte_Of_U16 (V, 1) = Byte (V mod 256);
      end loop;
      Check ("u48 / u16 big-endian and round trips", Ok);
   end;

   ---------------------------------------------------------------------------
   --  Tags and bounds.
   ---------------------------------------------------------------------------
   Check ("tags: ROSTER 0, REVOKE 1, GRANT 2, DEL 3, PUT 4",
          Tag_Of (K_Roster) = 0 and then Tag_Of (K_Revoke) = 1
          and then Tag_Of (K_Grant) = 2 and then Tag_Of (K_Del) = 3
          and then Tag_Of (K_Put) = 4
          and then (for all K in Kind => Tag_Of (K) = Byte (Kind'Pos (K))));
   Check ("Has_Kind / Kind_Of: tags 0 .. 4 are kinds, 5 is not",
          Kind_Of ([Byte'(0)]) = K_Roster and then Kind_Of ([Byte'(1)]) = K_Revoke
          and then Kind_Of ([Byte'(2)]) = K_Grant and then Kind_Of ([Byte'(3)]) = K_Del
          and then Kind_Of ([Byte'(4)]) = K_Put
          and then Has_Kind ([Byte'(4)]) and then not Has_Kind ([Byte'(5)]));
   --  Frame_Max = 176 + Value_Max = 41 136, ROSTER 285 .. 10 099 <= Frame_Max,
   --  REVOKE 275 and GRANT 263 are Compile_Time_Errors in the spec; the
   --  encoded lengths are checked below.

   ---------------------------------------------------------------------------
   --  Certificates (D1).
   ---------------------------------------------------------------------------
   declare
      Want : constant Byte_Array :=
        [16#6B#, 16#6F#, 16#6D#, 16#65#, 16#2F#, 16#72#, 16#6F#, 16#6F#, 16#74#]
        & NS_A & Other_PK & BE48 (Cap_2);
   begin
      Check ("Cert_Input = ""kome/root"" ‖ ns ‖ signer ‖ u48 (cap), 63 bytes",
             Cert_Input (NS_A, Other_PK, Cap_2)'Length = 63
             and then Cert_Input (NS_A, Other_PK, Cap_2) = Want);
      Check ("Cert_Hash = BLAKE2b-256 (Cert_Input)",
             Cert_Hash (NS_A, Other_PK, Cap_2) = Kome.Crypto.Blake2b_256 (Want));
      Check ("Make_Cert = Sign (founding, Cert_Hash), and it verifies",
             Cert_2 = Kome.Crypto.Sign (Root_SK, Cert_Hash (NS_A, Other_PK, Cap_2))
             and then Kome.Crypto.Verify (Cert_2, Root_PK, Cert_Hash (NS_A, Other_PK, Cap_2)));
      Check ("Cert_OK: founding key with zero block",
             Cert_OK (Root_PK, NS_A, Root_PK, 0, Zero_Sig));
      Check ("Cert_OK: founding key with cap 1 or a nonzero cert is refused",
             not Cert_OK (Root_PK, NS_A, Root_PK, 1, Zero_Sig)
             and then not Cert_OK (Root_PK, NS_A, Root_PK, 0, Cert_2));
      Check ("Cert_OK: certified root for this ns and cap",
             Cert_OK (Root_PK, NS_A, Other_PK, Cap_2, Cert_2));
      Check ("Cert_OK: wrong ns, cap, signer or a zero cert is refused",
             not Cert_OK (Root_PK, NS_B, Other_PK, Cap_2, Cert_2)
             and then not Cert_OK (Root_PK, NS_A, Other_PK, Cap_2 + 1, Cert_2)
             and then not Cert_OK (Root_PK, NS_A, Author_PK, Cap_2, Cert_2)
             and then not Cert_OK (Root_PK, NS_A, Other_PK, Cap_2, Zero_Sig));
      Check ("Cert_OK: a certificate signed by the root itself is refused",
             not Cert_OK (Root_PK, NS_A, Author_PK, Cap_2,
                          Make_Cert (Author_SK, NS_A, Other_PK, Cap_2))
             and then not Cert_OK
               (Root_PK, NS_A, Author_PK, Cap_2,
                Kome.Crypto.Sign (Author_SK, Cert_Hash (NS_A, Author_PK, Cap_2))));
   end;

   ---------------------------------------------------------------------------
   --  PUT
   ---------------------------------------------------------------------------
   declare
      Field_N : constant Byte_Array := [Character'Pos ('n')];
      Small   : Put_Record := Make_Put (NS_A, Ent_A, Field_N, 0, 0, Author_PK, []);
      Back    : Put_Record;
      St      : Status;
   begin
      Sign (Small, Author_SK);
      declare
         E : constant Byte_Array := Encode (Small);
      begin
         Check ("PUT minimal: length 145 (1-byte field, empty value)",
                E'Length = 145 and then E'Length = Frame_Len (Small)
                and then E (0) = Tag_Put and then E (0) = 4 and then E (33) = 1
                and then E (35 .. 40) = BE48 (0)
                and then E (79) = 0 and then E (80) = 0);
         Decode (E, Back, St);
         Check ("PUT minimal: decode OK and equal", St = OK and then Back = Small);
         Check ("PUT minimal: well-formed", Well_Formed (Back));
         Lemma_Decode_Encode (Small);
         Lemma_Encode_Decode_Put (E);
         Check ("PUT minimal: Encode (Decode (frame)) = frame", Encode (Back) = E);
         Check ("PUT minimal: empty value is a value", Back.C.VLen = 0);
      end;
   end;

   declare
      Field_32 : constant Byte_Array := Fill (Field_Max, 200);
      Value_M  : constant Byte_Array := Fill (Value_Max, 3);
      Big      : Put_Record :=
        Make_Put (NS_A, Ent_A, Field_32, Max_U48, Max_U48, Author_PK, Value_M);
      Before   : Header;
      Back     : Put_Record;
      Keep     : Put_Record;
      St       : Status;
   begin
      Before := To_Header (Big);
      Sign (Big, Author_SK);
      Check ("PUT: signing changes neither h nor the header", To_Header (Big) = Before);
      declare
         E  : constant Byte_Array := Encode (Big);
         L  : constant Natural    := E'Length;
         FL : constant Natural    := Field_Max;
      begin
         Check ("PUT max: length 41136 (32-byte field, 40960-byte value)",
                L = 1 + 16 + 16 + 1 + 32 + 6 + 6 + 32 + 2 + 40_960 + 64
                and then L = Put_Frame_Max and then L = Frame_Max);
         Check ("PUT max: layout bytes",
                E (1 .. 16) = NS_A and then E (17 .. 32) = Ent_A
                and then E (33) = 32 and then E (34 .. 65) = Field_32
                and then E (34 + FL .. 39 + FL) = BE48 (Max_U48)
                and then E (40 + FL .. 45 + FL) = BE48 (Max_U48)
                and then E (46 + FL .. 77 + FL) = Author_PK
                and then E (78 + FL) = 16#A0# and then E (79 + FL) = 16#00#
                and then E (80 + FL .. L - 65) = Value_M
                and then E (L - 64 .. L - 1) = Big.Signature);
         Decode (E, Back, St);
         Check ("PUT max: decode OK and equal", St = OK and then Back = Big);
         Check ("PUT max: well-formed", Well_Formed (Back));
         Lemma_Decode_Encode (Big);
         Lemma_Encode_Decode_Put (E);

         --  A frame at a nonzero offset decodes the same.
         declare
            Shifted : Byte_Array (1000 .. 999 + L);
         begin
            Shifted := E;
            Decode (Shifted, Back, St);
            Check ("PUT max: decode at nonzero 'First", St = OK and then Back = Big);
         end;

         --  Header (DESIGN.md §3 / Kome.Headers).
         declare
            H : constant Header := To_Header (Big);
         begin
            Check ("PUT header: kind, ns, ent",
                   H.K = K_Put and then H.NS = To_Id128 (NS_A)
                   and then H.Ent = To_Id128 (Ent_A));
            Check ("PUT header: FH = BLAKE2b-256 (field name)",
                   H.FH = To_Key256 (Kome.Crypto.Blake2b_256 (Field_32)));
            Check ("PUT header: V = (t, author, seq, h)",
                   H.V.T = Max_U48 and then H.V.Author = To_Key256 (Author_PK)
                   and then H.V.Seq = Max_U48 and then H.V.H = H_Of (E));
            Check ("PUT header: no issuer, del_ttl 0",
                   H.Issuer = Zero_Key and then H.Del_TTL = 0);
            Check ("PUT header: h = BLAKE2b-256 (frame minus sig)",
                   To_Key256 (Hash (Big.C)) = H_Of (E));
            Lemma_Header_Canonical (Big);
            Check ("PUT header: Kome.Headers.Canonical", Kome.Headers.Canonical (H));
         end;

         --  Refusals leave the record unchanged.
         Keep := Back;
         Decode (E (0 .. L - 2), Back, St);
         Check ("PUT truncated by one byte refused, record unchanged",
                St = Malformed and then Back = Keep);
         Decode (E & Byte'(0), Back, St);
         Check ("PUT oversized by one byte refused, record unchanged",
                St = Malformed and then Back = Keep);
         Decode (E (0 .. 143), Back, St);
         Check ("PUT shorter than any frame refused", St = Malformed and then Back = Keep);
         declare
            Empty : constant Byte_Array (1 .. 0) := [];
         begin
            Decode (Empty, Back, St);
            Check ("PUT empty input refused", St = Malformed and then Back = Keep);
         end;
         declare
            Bad : Byte_Array := E;
         begin
            Bad (0) := Tag_Del;
            Decode (Bad, Back, St);
            Check ("PUT wrong tag refused", St = Malformed and then Back = Keep);
            Bad (0) := 3;
            Decode (Bad, Back, St);
            Check ("PUT frame with the old PUT tag 3 refused",
                   St = Malformed and then Back = Keep);
            Bad := E;
            Bad (33) := 0;
            Decode (Bad, Back, St);
            Check ("PUT flen 0 refused, record unchanged",
                   St = Malformed and then Back = Keep);
            Bad (33) := 33;
            Decode (Bad, Back, St);
            Check ("PUT flen 33 refused, record unchanged",
                   St = Malformed and then Back = Keep);
            Bad := E;
            Bad (78 + FL) := 16#FF#;
            Bad (79 + FL) := 16#FE#;
            Decode (Bad, Back, St);
            Check ("PUT vlen disagreeing with length refused",
                   St = Malformed and then Back = Keep);
         end;

         --  Signature and content tamper.
         declare
            Bad : Byte_Array := E;
            R2  : Put_Record;
         begin
            Bad (L - 1) := Bad (L - 1) xor 1;
            Decode (Bad, R2, St);
            Check ("PUT tampered signature: decodes", St = OK);
            Check ("PUT tampered signature: not well-formed", not Well_Formed (R2));
            Decode_Verified (Bad, R2, St);
            Check ("PUT tampered signature: Decode_Verified refuses", St = Malformed);
            Bad := E;
            Bad (80 + FL + 100) := Bad (80 + FL + 100) xor 16#80#;   --  value byte 100
            Decode (Bad, R2, St);
            Check ("PUT tampered value byte: decodes to the changed value, not well-formed",
                   St = OK and then R2.C.Value (100) /= Big.C.Value (100)
                   and then not Well_Formed (R2));
            Bad := E;
            Bad (46 + FL + 3) := Bad (46 + FL + 3) xor 1;   --  author byte 3
            Decode (Bad, R2, St);
            Check ("PUT tampered author byte: not well-formed",
                   St = OK and then R2.C.Author /= Big.C.Author
                   and then not Well_Formed (R2));
            Decode_Verified (E, R2, St);
            Check ("PUT Decode_Verified accepts the genuine frame",
                   St = OK and then R2 = Big);
         end;
      end;

      --  Signed by someone other than the author.
      declare
         Forged : Put_Record := Big;
      begin
         Forged.C.Author := Other_PK;
         Sign (Forged, Other_SK);
         Forged.C.Author := Author_PK;
         Check ("PUT signed by a non-author key is not well-formed",
                not Well_Formed (Forged));
      end;

      --  Non-canonical padding.
      declare
         Pad : Put_Record := Make_Put (NS_A, Ent_A, [1, 2], 5, 6, Author_PK, [7]);
      begin
         Sign (Pad, Author_SK);
         Check ("PUT canonical record is well-formed",
                Canonical (Pad) and then Well_Formed (Pad));
         Pad.C.Field (5) := 1;
         Check ("PUT nonzero field padding is not canonical / well-formed",
                not Canonical (Pad) and then not Well_Formed (Pad));
         Pad.C.Field (5) := 0;
         Pad.C.Value (9) := 1;
         Check ("PUT nonzero value padding is not canonical / well-formed",
                not Canonical (Pad) and then not Well_Formed (Pad));
      end;
   end;

   --  D12: vlen 40 960 is a value; 40 961 is refused even when the length
   --  agrees (a 1-byte field leaves room in Put_Frame_Max for it). Before
   --  the vlen bound, Is_Put_Frame accepted this frame and Parse_Put's
   --  Value_Len conversion failed.
   declare
      V  : Put_Record := Make_Put (NS_A, Ent_A, [16#66#], 1, 1, Author_PK, Fill (Value_Max, 9));
      R2 : Put_Record;
      K2 : Put_Record;
      St : Status;
   begin
      Sign (V, Author_SK);
      declare
         E   : constant Byte_Array := Encode (V);
         Big : Byte_Array := E (0 .. E'Last - Sig_Len) & Byte'(16#5A#) & V.Signature;
      begin
         Decode_Verified (E, R2, St);
         Check ("PUT vlen 40960 (1-byte field): length 41105, OK",
                E'Length = 144 + 1 + 40_960 and then E (79) = 16#A0# and then E (80) = 0
                and then St = OK and then R2 = V);
         Big (79) := 16#A0#;
         Big (80) := 16#01#;   --  vlen 40 961, and the length is 144 + 1 + 40 961
         K2 := R2;
         Check ("PUT vlen 40961: length agrees and fits Put_Frame_Max",
                Big'Length = 144 + 1 + 40_961 and then Big'Length <= Put_Frame_Max);
         Decode (Big, R2, St);
         Check ("PUT vlen 40961: Malformed, record unchanged",
                St = Malformed and then R2 = K2 and then not Is_Put_Frame (Big));
         Decode_Verified (Big, R2, St);
         Check ("PUT vlen 40961: Decode_Verified Malformed",
                St = Malformed and then R2 = K2);
      end;
   end;

   ---------------------------------------------------------------------------
   --  PUT, big-endian t: 0x010203040506.
   ---------------------------------------------------------------------------
   declare
      R : constant Put_Record :=
        Make_Put (NS_A, Ent_A, [16#61#, 16#62#], 16#0102_0304_0506#, 16#0A0B_0C0D_0E0F#,
                  Author_PK, [16#AA#, 16#BB#, 16#CC#]);
      E : constant Byte_Array := Encode (R);
   begin
      Check ("PUT t, seq, vlen big-endian",
             E (36 .. 41) = [1, 2, 3, 4, 5, 6]
             and then E (42 .. 47) = [16#0A#, 16#0B#, 16#0C#, 16#0D#, 16#0E#, 16#0F#]
             and then E (80 .. 81) = [0, 3]
             and then E (82 .. 84) = [16#AA#, 16#BB#, 16#CC#]
             and then E'Length = 144 + 2 + 3);
   end;

   ---------------------------------------------------------------------------
   --  Make_Del (DESIGN.md §5 step 2) and the builders' header Posts (both
   --  Posts run here under -gnata).
   ---------------------------------------------------------------------------
   declare
      D    : Del_Record := Make_Del (NS_A, Ent_A, 1234, Max_U48, Author_PK);
      Hand : constant Del_Record :=
        (C => (NS => NS_A, Ent => Ent_A, T => 1234, Seq => Max_U48, Author => Author_PK),
         Signature => [others => 0]);
      P    : constant Put_Record :=
        Make_Put (NS_A, Ent_A, [16#61#, 16#62#], 7, 8, Author_PK, [1]);
      Back : Del_Record;
      St   : Status;
   begin
      Check ("Make_Del equals the hand-built DEL", D = Hand);
      Sign (D, Author_SK);
      Decode_Verified (Encode (D), Back, St);
      Check ("Make_Del then Sign: verified decode, same header, h = hash of content",
             St = OK and then Back = D and then To_Header (Back) = To_Header (D)
             and then To_Header (D).V.H = H_Of (Encode (D))
             and then To_Header (D).V.T = 1234 and then To_Header (D).V.Seq = Max_U48);
      Check ("Make_Put header: FH = BLAKE2b (field), V from the arguments",
             To_Header (P).FH = To_Key256 (Kome.Crypto.Blake2b_256 ([16#61#, 16#62#]))
             and then To_Header (P).V.T = 7 and then To_Header (P).V.Seq = 8
             and then To_Header (P).V.Author = To_Key256 (Author_PK)
             and then To_Header (P).V.H = H_Of (Encode (P)));
   end;

   ---------------------------------------------------------------------------
   --  DEL
   ---------------------------------------------------------------------------
   declare
      D    : Del_Record := (C => (NS => NS_A, Ent => Ent_A, T => 1234, Seq => Max_U48,
                                  Author => Author_PK),
                            Signature => [others => 0]);
      Back : Del_Record;
      Keep : Del_Record;
      St   : Status;
   begin
      Sign (D, Author_SK);
      declare
         E    : constant Byte_Array := Encode (D);
         Want : constant Byte_Array :=
           [Byte'(3)] & NS_A & Ent_A & BE48 (1234) & BE48 (Max_U48) & Author_PK & D.Signature;
         H    : constant Header := To_Header (D);
      begin
         Check ("DEL: length 141 and bytes equal the hand-built layout (tag 3)",
                E'Length = 141 and then E = Want);
         Decode (E, Back, St);
         Check ("DEL: decode OK and equal", St = OK and then Back = D);
         Check ("DEL: well-formed", Well_Formed (Back));
         Lemma_Decode_Encode (D);
         Lemma_Encode_Decode_Del (E);
         Check ("DEL header: V = (t, author, seq, h), FH 0, no issuer, del_ttl 0",
                H.K = K_Del and then H.NS = To_Id128 (NS_A)
                and then H.Ent = To_Id128 (Ent_A)
                and then H.FH = Zero_Key
                and then H.V.T = 1234 and then H.V.Author = To_Key256 (Author_PK)
                and then H.V.Seq = Max_U48 and then H.V.H = H_Of (E)
                and then H.Issuer = Zero_Key and then H.Del_TTL = 0);
         Lemma_Header_Canonical (D);
         Check ("DEL header: Kome.Headers.Canonical", Kome.Headers.Canonical (H));
         Keep := Back;
         Decode (E (0 .. 139), Back, St);
         Check ("DEL truncated refused, record unchanged",
                St = Malformed and then Back = Keep);
         Decode (E & Byte'(0), Back, St);
         Check ("DEL oversized refused, record unchanged",
                St = Malformed and then Back = Keep);
         declare
            Bad : Byte_Array := E;
         begin
            Bad (100) := Bad (100) xor 4;   --  signature byte 23 (sig is 77 .. 140)
            Decode (Bad, Back, St);
            Check ("DEL tampered signature: decodes, not well-formed",
                   St = OK and then Back.C = D.C and then Back.Signature /= D.Signature
                   and then not Well_Formed (Back));
            Keep := Back;
            Decode_Verified (Bad, Back, St);
            Check ("DEL tampered signature: Decode_Verified refuses, record unchanged",
                   St = Malformed and then Back = Keep);
            Bad := E;
            Bad (70) := Bad (70) xor 4;     --  author byte 25 (author is 45 .. 76)
            Decode (Bad, Back, St);
            Check ("DEL tampered author: decodes, not well-formed",
                   St = OK and then Back.C.Author /= D.C.Author
                   and then Back.Signature = D.Signature
                   and then not Well_Formed (Back));
            Keep := Back;
            Decode_Verified (Bad, Back, St);
            Check ("DEL tampered author: Decode_Verified refuses, record unchanged",
                   St = Malformed and then Back = Keep);
            Bad := E;
            Bad (0) := 2;   --  the old DEL tag, now GRANT
            Decode (Bad, Back, St);
            Check ("DEL frame with the old DEL tag 2 refused",
                   St = Malformed and then Back = Keep);
         end;
         --  A DEL frame is not a PUT frame and vice versa.
         declare
            P  : Put_Record;
            P0 : Put_Record;
         begin
            P0 := P;
            Decode (E, P, St);
            Check ("DEL frame refused as PUT", St = Malformed and then P = P0);
         end;
         Check ("Kind_Of reads the tag", Has_Kind (E) and then Kind_Of (E) = K_Del);
      end;
   end;

   ---------------------------------------------------------------------------
   --  ROSTER
   ---------------------------------------------------------------------------
   declare
      Links_15   : constant Byte_Array := Fill (Links_Max * Link_Len, 11);
      Members_64 : constant Byte_Array := Members_Of (Members_Max, 77);
      Big  : Roster_Record :=
        Make_Roster (Root_PK, Salt_A, Root_PK, 0, Zero_Sig, Box_A, Max_U48, 5000,
                     Del_TTL_Max, 65_535, Links_15, Members_64);
      Back : Roster_Record;
      Keep : Roster_Record;
      St   : Status;
   begin
      Sign (Big, Root_SK);
      declare
         E : constant Byte_Array := Encode (Big);
         L : constant Natural    := E'Length;
         H : constant Header     := To_Header (Big);
      begin
         Check ("ROSTER max: length 10099 (15 links, 64 members)",
                L = 1 + 16 + 32 + 16 + 32 + 6 + 64 + 32 + 6 + 6 + 6 + 2 + 1 + 15 * 74 + 1
                    + 64 * 136 + 64
                and then L = Roster_Frame_Max and then L = Frame_Len (Big));
         Check ("ROSTER max: layout bytes at the DESIGN.md §2 offsets",
                E (0) = Tag_Roster and then E (0) = 0 and then E (1 .. 16) = NS_A
                and then E (17 .. 48) = Root_PK and then E (49 .. 64) = Salt_A
                and then E (65 .. 96) = Root_PK
                and then E (97 .. 102) = BE48 (0)
                and then E (103 .. 166) = Zero_Sig
                and then E (167 .. 198) = Box_A
                and then E (199 .. 204) = BE48 (Max_U48)
                and then E (205 .. 210) = BE48 (5000)
                and then E (211 .. 216) = BE48 (Del_TTL_Max)
                and then E (217 .. 218) = [16#FF#, 16#FF#]
                and then E (219) = 15 and then E (220 .. 220 + 1110 - 1) = Links_15
                and then E (220 + 1110) = 64
                and then E (221 + 1110 .. 221 + 1110 + 8704 - 1) = Members_64
                and then E (L - 64 .. L - 1) = Big.Signature);
         Decode (E, Back, St);
         Check ("ROSTER max: decode OK and equal", St = OK and then Back = Big);
         Check ("ROSTER max: well-formed (founder-signed)", Well_Formed (Back));
         Decode_Verified (E, Back, St);
         Check ("ROSTER max: Decode_Verified OK", St = OK and then Back = Big);
         Lemma_Decode_Encode (Big);
         Lemma_Encode_Decode_Roster (E);
         Check ("ROSTER max: Encode (Decode (frame)) = frame", Encode (Back) = E);
         Lemma_Link_Bytes (Back.C, 15);
         Lemma_Link_Bytes (Back.C, 1);
         Lemma_Member_Bytes (Back.C, 64);
         Lemma_Member_Bytes (Back.C, 1);
         Check ("ROSTER accessors: link 1, link 15",
                Natural (Link_From_Epoch (Back.C, 1)) =
                  Natural (Links_15 (0)) * 256 + Natural (Links_15 (1))
                and then Natural (Link_From_Epoch (Back.C, 15)) =
                  Natural (Links_15 (14 * 74)) * 256 + Natural (Links_15 (14 * 74 + 1))
                and then Link_Nonce (Back.C, 15) = Links_15 (14 * 74 + 2 .. 14 * 74 + 25)
                and then Link_Box (Back.C, 15) = Links_15 (14 * 74 + 26 .. 14 * 74 + 73)
                and then Link_Box (Back.C, 1) = Links_15 (26 .. 73));
         Check ("ROSTER accessors: member 1, member 64",
                Member_Sign_PK (Back.C, 64) = Members_64 (63 * 136 .. 63 * 136 + 31)
                and then Member_DH_PK (Back.C, 64) = Members_64 (63 * 136 + 32 .. 63 * 136 + 63)
                and then Member_Nonce (Back.C, 64) = Members_64 (63 * 136 + 64 .. 63 * 136 + 87)
                and then Member_Box (Back.C, 64) = Members_64 (63 * 136 + 88 .. 63 * 136 + 135)
                and then Member_Key (Back.C, 1) = To_Key256 (Members_64 (0 .. 31)));
         Lemma_DH_Keys_OK_Def (Back.C);
         Lemma_DH_Box_OK (Back.C);
         Lemma_DH_Keys_OK (Back.C, 64);
         Check ("ROSTER DH_Keys_OK (box_pk and 64 members)", DH_Keys_OK (Back.C));
         Check ("ROSTER header: V = (ceiling_t, signer, gen, h), issuer, del_ttl",
                H.K = K_Roster and then H.NS = To_Id128 (NS_A)
                and then H.Ent = Zero_Id and then H.FH = Zero_Key
                and then H.V.T = 5000 and then H.V.Author = To_Key256 (Root_PK)
                and then H.V.Author = Signer_Key (Big)
                and then H.V.Seq = Max_U48 and then H.V.H = H_Of (E)
                and then H.Issuer = To_Key256 (Root_PK)
                and then H.Del_TTL = Del_TTL_Max
                and then Ceil_Of (H) = 5000);
         Lemma_Header_Canonical (Big);
         Check ("ROSTER header: Kome.Headers.Canonical", Kome.Headers.Canonical (H));

         Keep := Back;
         Decode (E (0 .. L - 2), Back, St);
         Check ("ROSTER truncated refused, record unchanged",
                St = Malformed and then Back = Keep);
         Decode (E & Byte'(0), Back, St);
         Check ("ROSTER oversized refused, record unchanged",
                St = Malformed and then Back = Keep);
         Decode (E (0 .. Roster_Frame_Min - 2), Back, St);
         Check ("ROSTER shorter than any frame refused, record unchanged",
                St = Malformed and then Back = Keep);
         declare
            Bad : Byte_Array := E;
         begin
            Bad (219) := 16;   --  n_links 16
            Decode (Bad, Back, St);
            Check ("ROSTER n_links 16 refused", St = Malformed and then Back = Keep);
            Bad := E;
            Bad (220 + 1110) := 65;   --  n_members 65
            Decode (Bad, Back, St);
            Check ("ROSTER n_members 65 refused", St = Malformed and then Back = Keep);
            Bad := E;
            Bad (219) := 255;   --  n_links past the end: n_members never read
            Decode (Bad, Back, St);
            Check ("ROSTER n_links 255 refused", St = Malformed and then Back = Keep);
            Bad := E;
            Bad (L - 30) := Bad (L - 30) xor 2;
            Decode (Bad, Back, St);
            Check ("ROSTER tampered signature: not well-formed",
                   St = OK and then Back.C = Big.C and then not Well_Formed (Back));
            Bad := E;
            Bad (170) := Bad (170) xor 2;   --  box_pk byte 3
            Decode (Bad, Back, St);
            Check ("ROSTER tampered box_pk: not well-formed",
                   St = OK and then Back.C.Box_PK /= Box_A and then not Well_Formed (Back));
            Keep := Back;
            Bad := E;
            Bad (3000) := Bad (3000) xor 2;
            Decode_Verified (Bad, Back, St);
            Check ("ROSTER tampered member box: Decode_Verified refuses, unchanged",
                   St = Malformed and then Back = Keep);
         end;
      end;

      --  ns must match (root_pk, salt), even when correctly signed.
      declare
         Wrong : Roster_Record := Big;
      begin
         Wrong.C.NS (0) := Wrong.C.NS (0) xor 1;
         Sign (Wrong, Root_SK);
         Check ("ROSTER with ns not derived from (root_pk, salt) is not well-formed",
                not Well_Formed (Wrong));
         Wrong := Big;
         Wrong.C.Root_PK := Other_PK;
         Wrong.C.Signer := Other_PK;
         Wrong.C.NS := Collection_Id (Other_PK, Salt_A);
         Sign (Wrong, Other_SK);
         Wrong.C.Root_PK := Root_PK;
         Wrong.C.Signer := Root_PK;
         Wrong.C.NS := NS_A;
         Check ("ROSTER signed by a key other than signer is not well-formed",
                not Well_Formed (Wrong));
         Wrong := Big;
         Wrong.C.N_Members := 63;   --  member 64's bytes become padding
         Check ("ROSTER nonzero member padding is not canonical",
                not Canonical (Wrong) and then not Well_Formed (Wrong));
         Wrong := Big;
         Wrong.C.N_Links := 14;     --  link 15's bytes become padding
         Check ("ROSTER nonzero link padding is not canonical",
                not Canonical (Wrong) and then not Well_Formed (Wrong));
      end;

      --  Empty roster: no links, no members.
      declare
         Empty_R : Roster_Record :=
           Make_Roster (Root_PK, Salt_A, Root_PK, 0, Zero_Sig, Box_A, 0, 0, Del_TTL_Min, 0,
                        [], []);
      begin
         Sign (Empty_R, Root_SK);
         declare
            E : constant Byte_Array := Encode (Empty_R);
         begin
            Decode (E, Back, St);
            Check ("ROSTER empty: length 285, round trip, well-formed",
                   E'Length = 285 and then E (219) = 0 and then E (220) = 0
                   and then St = OK and then Back = Empty_R and then Well_Formed (Back));
            Lemma_Decode_Encode (Empty_R);
            Lemma_Encode_Decode_Roster (E);
         end;
      end;
   end;

   ---------------------------------------------------------------------------
   --  ROSTER signer admission (D1): the review blocker, reproduced.
   ---------------------------------------------------------------------------
   declare
      Mem  : constant Byte_Array := Members_Of (2, 33);
      Back : Roster_Record;
      Keep : Roster_Record;
      St   : Status;

      function R (Signer : Pubkey; Cap : U48; Cert : Sig; Ceil : U48;
                  TTL : U48 := TTL_OK; Box_PK : Pubkey := Box_A;
                  Members : Byte_Array := Mem) return Roster_Record is
        (Make_Roster (Root_PK, Salt_A, Signer, Cap, Cert, Box_PK, 7, Ceil, TTL, 2,
                      Fill (Link_Len, 5), Members));

      --  Sign with SK and run Decode_Verified on the frame.
      function Verdict (X : in out Roster_Record; SK : Kome.Crypto.Secret_Key) return Status is
         S : Status;
      begin
         Sign (X, SK);
         Keep := Back;
         Decode_Verified (Encode (X), Back, S);
         if S = Malformed and then Back /= Keep then
            Check ("ROSTER refusal leaves the record unchanged", False);
         end if;
         return S;
      end Verdict;

      X : Roster_Record;
   begin
      --  An outsider signs a roster raising the ceiling to 2^48 - 1 and
      --  names itself as signer: it used to pass Decode_Verified.
      X := R (Author_PK, 0, Zero_Sig, Max_U48);
      St := Verdict (X, Author_SK);
      Check ("ROSTER outsider-signed (zero cert), ceiling 2^48-1: Malformed",
             St = Malformed and then not Well_Formed (X)
             and then Kome.Crypto.Verify (X.Signature, Author_PK, Hash (X.C)));
      X := R (Author_PK, Max_U48, Make_Cert (Author_SK, NS_A, Other_PK, Max_U48), Max_U48);
      St := Verdict (X, Author_SK);
      Check ("ROSTER outsider-signed with a self-made certificate: Malformed",
             St = Malformed);
      X := R (Author_PK, Cap_2, Cert_2, 6000);
      St := Verdict (X, Author_SK);
      Check ("ROSTER outsider-signed carrying another root's certificate: Malformed",
             St = Malformed);

      --  The certified secondary root.
      X := R (Other_PK, Cap_2, Cert_2, 6000);
      St := Verdict (X, Other_SK);
      Check ("ROSTER by certified root, ceiling_t <= cert_cap: OK",
             St = OK and then Back = X and then Well_Formed (X));
      Check ("ROSTER by certified root: header author and issuer are the signer",
             To_Header (X).V.Author = To_Key256 (Other_PK)
             and then To_Header (X).Issuer = To_Key256 (Other_PK)
             and then To_Header (X).V.Author /= To_Key256 (Root_PK)
             and then Signer_Key (X) = To_Key256 (Other_PK));
      X := R (Other_PK, Cap_2, Cert_2, Cap_2);
      St := Verdict (X, Other_SK);
      Check ("ROSTER by certified root, ceiling_t = cert_cap: OK", St = OK);
      X := R (Other_PK, Cap_2, Cert_2, Cap_2 + 1);
      St := Verdict (X, Other_SK);
      Check ("ROSTER by certified root, ceiling_t > cert_cap: Malformed",
             St = Malformed and then not Well_Formed (X));
      X := R (Other_PK, Cap_2 + 5000, Cert_2, Cap_2 + 1);
      St := Verdict (X, Other_SK);
      Check ("ROSTER by certified root claiming a larger cap than certified: Malformed",
             St = Malformed);
      X := R (Other_PK, Cap_2, Make_Cert (Root_SK, NS_B, Other_PK, Cap_2), 6000);
      St := Verdict (X, Other_SK);
      Check ("ROSTER with a certificate made for another ns: Malformed", St = Malformed);

      --  The founding key's block must be zero.
      X := R (Root_PK, 0, Zero_Sig, Max_U48);
      St := Verdict (X, Root_SK);
      Check ("ROSTER by founding key, zero block, any ceiling: OK", St = OK);
      X := R (Root_PK, 1, Zero_Sig, 6000);
      St := Verdict (X, Root_SK);
      Check ("ROSTER by founding key with cert_cap 1: Malformed", St = Malformed);
      X := R (Root_PK, 0, Cert_2, 6000);
      St := Verdict (X, Root_SK);
      Check ("ROSTER by founding key with a nonzero cert_sig: Malformed", St = Malformed);

      --  del_ttl clamp (DESIGN.md §2 item 3).
      X := R (Root_PK, 0, Zero_Sig, 6000, TTL => Del_TTL_Min);
      St := Verdict (X, Root_SK);
      Check ("ROSTER del_ttl = Del_TTL_Min: OK", St = OK);
      X := R (Root_PK, 0, Zero_Sig, 6000, TTL => Del_TTL_Max);
      St := Verdict (X, Root_SK);
      Check ("ROSTER del_ttl = Del_TTL_Max: OK", St = OK);
      X := R (Root_PK, 0, Zero_Sig, 6000, TTL => Del_TTL_Min - 1);
      St := Verdict (X, Root_SK);
      Check ("ROSTER del_ttl = Del_TTL_Min - 1: Malformed", St = Malformed);
      X := R (Root_PK, 0, Zero_Sig, 6000, TTL => Del_TTL_Max + 1);
      St := Verdict (X, Root_SK);
      Check ("ROSTER del_ttl = Del_TTL_Max + 1: Malformed", St = Malformed);
      X := R (Root_PK, 0, Zero_Sig, 6000, TTL => 0);
      St := Verdict (X, Root_SK);
      Check ("ROSTER del_ttl = 0: Malformed", St = Malformed);

      --  X25519 keys (E5).
      declare
         type Key_List is array (Positive range <>) of Pubkey;
         Bad_Keys : constant Key_List := [P_Enc, Order_8, U_One, U_Zero];
         Names    : constant array (1 .. 4) of String (1 .. 7) :=
           ["p      ", "order 8", "u = 1  ", "u = 0  "];
      begin
         for K in Bad_Keys'Range loop
            X := R (Root_PK, 0, Zero_Sig, 6000, Box_PK => Bad_Keys (K));
            St := Verdict (X, Root_SK);
            Check ("ROSTER box_pk = " & Names (K) & ": Malformed",
                   St = Malformed and then not DH_Keys_OK (X.C)
                   and then Kome.Crypto.Verify (X.Signature, Root_PK, Hash (X.C)));
            declare
               M : Byte_Array := Mem;
            begin
               M (Member_Len + Pubkey_Len .. Member_Len + 2 * Pubkey_Len - 1) := Bad_Keys (K);
               X := R (Root_PK, 0, Zero_Sig, 6000, Members => M);
               St := Verdict (X, Root_SK);
               Check ("ROSTER member 2 dh_pk = " & Names (K) & ": Malformed",
                      St = Malformed and then not DH_Keys_OK (X.C));
            end;
         end loop;
      end;
   end;

   ---------------------------------------------------------------------------
   --  REVOKE
   ---------------------------------------------------------------------------
   declare
      X    : Revoke_Record :=
        Make_Revoke (Root_PK, Salt_A, Root_PK, 0, Zero_Sig, Author_PK, 777, 1);
      Back : Revoke_Record;
      Keep : Revoke_Record;
      St   : Status;
   begin
      Sign (X, Root_SK);
      declare
         E    : constant Byte_Array := Encode (X);
         Want : constant Byte_Array :=
           [Byte'(1)] & NS_A & Root_PK & Salt_A & Root_PK & BE48 (0) & Zero_Sig & Author_PK
           & BE48 (777) & BE48 (1) & X.Signature;
         H    : constant Header := To_Header (X);
      begin
         Check ("REVOKE: length 275 and bytes equal the hand-built layout",
                E'Length = 275 and then E = Want);
         Decode (E, Back, St);
         Check ("REVOKE: decode OK and equal", St = OK and then Back = X);
         Check ("REVOKE: well-formed", Well_Formed (Back));
         Lemma_Decode_Encode (X);
         Lemma_Encode_Decode_Revoke (E);
         Check ("REVOKE header: V = (from_t, sign_pk, rev_seq, h), issuer = signer",
                H.K = K_Revoke and then H.NS = To_Id128 (NS_A)
                and then H.Ent = Zero_Id and then H.FH = Zero_Key
                and then H.V.T = 777 and then H.V.Author = To_Key256 (Author_PK)
                and then H.V.Seq = 1 and then H.V.H = H_Of (E)
                and then H.Issuer = To_Key256 (Root_PK) and then H.Del_TTL = 0
                and then Signer_Key (X) = To_Key256 (Root_PK));
         Lemma_Header_Canonical (X);
         Check ("REVOKE header: Kome.Headers.Canonical", Kome.Headers.Canonical (H));
         Keep := Back;
         Decode (E (1 .. E'Last), Back, St);
         Check ("REVOKE truncated refused, record unchanged",
                St = Malformed and then Back = Keep);
         Decode (E & E, Back, St);
         Check ("REVOKE oversized refused, record unchanged",
                St = Malformed and then Back = Keep);
         declare
            Bad : Byte_Array := E;
         begin
            Bad (250) := Bad (250) xor 1;   --  signature byte 39 (sig is 211 .. 274)
            Decode_Verified (Bad, Back, St);
            Check ("REVOKE tampered signature: Decode_Verified refuses, unchanged",
                   St = Malformed and then Back = Keep);
            Bad := E;
            Bad (202) := Bad (202) xor 1;   --  from_t (199 .. 204)
            Decode (Bad, Back, St);
            Check ("REVOKE tampered from_t: not well-formed",
                   St = OK and then Back.C.From_T /= 777 and then not Well_Formed (Back));
         end;
      end;
      declare
         Wrong : Revoke_Record := X;
      begin
         Wrong.C.Salt (0) := Wrong.C.Salt (0) xor 1;
         Sign (Wrong, Root_SK);
         Check ("REVOKE with ns not derived from (root_pk, salt) is not well-formed",
                not Well_Formed (Wrong));
      end;

      --  Signer admission (D1, D2).
      declare
         function V (Y : in out Revoke_Record; SK : Kome.Crypto.Secret_Key) return Status is
            S : Status;
         begin
            Sign (Y, SK);
            Keep := Back;
            Decode_Verified (Encode (Y), Back, S);
            if S = Malformed and then Back /= Keep then
               Check ("REVOKE refusal leaves the record unchanged", False);
            end if;
            return S;
         end V;
         Y : Revoke_Record;
      begin
         Y := Make_Revoke (Root_PK, Salt_A, Author_PK, 0, Zero_Sig, Other_PK, 0, 1);
         St := V (Y, Author_SK);
         Check ("REVOKE outsider-signed (revoking a root): Malformed",
                St = Malformed and then not Well_Formed (Y)
                and then Kome.Crypto.Verify (Y.Signature, Author_PK, Hash (Y.C)));
         Y := Make_Revoke (Root_PK, Salt_A, Other_PK, Cap_2, Cert_2, Author_PK, 9, 2);
         St := V (Y, Other_SK);
         Check ("REVOKE by certified root: OK, signer key, subject in header",
                St = OK and then Back = Y and then Signer_Key (Y) = To_Key256 (Other_PK)
                and then To_Header (Y).V.Author = To_Key256 (Author_PK)
                and then To_Header (Y).Issuer = To_Key256 (Other_PK));
         Y := Make_Revoke (Root_PK, Salt_A, Other_PK, Cap_2,
                           Make_Cert (Root_SK, NS_B, Other_PK, Cap_2), Author_PK, 9, 2);
         St := V (Y, Other_SK);
         Check ("REVOKE with a certificate made for another ns: Malformed", St = Malformed);
         Y := Make_Revoke (Root_PK, Salt_A, Root_PK, 5, Zero_Sig, Author_PK, 9, 2);
         St := V (Y, Root_SK);
         Check ("REVOKE by founding key with a nonzero cert block: Malformed",
                St = Malformed);
         Y := Make_Revoke (Root_PK, Salt_A, Root_PK, 0, Zero_Sig, Root_PK, 0, 3);
         St := V (Y, Root_SK);
         Check ("REVOKE of root_pk (founding-signed): Malformed",
                St = Malformed and then not Well_Formed (Y));
         Y := Make_Revoke (Root_PK, Salt_A, Other_PK, Cap_2, Cert_2, Root_PK, 0, 3);
         St := V (Y, Other_SK);
         Check ("REVOKE of root_pk (by a certified root): Malformed", St = Malformed);
         Y := Make_Revoke (Root_PK, Salt_A, Root_PK, 0, Zero_Sig, Other_PK, 0, 4);
         St := V (Y, Root_SK);
         Check ("REVOKE of a certified root by the founding key: OK", St = OK);
         Y := Make_Revoke (Root_PK, Salt_A, Other_PK, Cap_2, Cert_2, Author_PK, 9, 2);
         Sign (Y, Other_SK);
         Y.C.Signer := Root_PK;
         Check ("REVOKE whose signer field is not the signing key is not well-formed",
                not Well_Formed (Y));
      end;
   end;

   ---------------------------------------------------------------------------
   --  GRANT
   ---------------------------------------------------------------------------
   declare
      G    : Grant_Record := Make_Grant (Root_PK, Salt_A, Root_PK, 0, Zero_Sig, Author_PK);
      Back : Grant_Record;
      Keep : Grant_Record;
      St   : Status;
   begin
      Sign (G, Root_SK);
      declare
         E    : constant Byte_Array := Encode (G);
         Want : constant Byte_Array :=
           [Byte'(2)] & NS_A & Root_PK & Salt_A & Root_PK & BE48 (0) & Zero_Sig & Author_PK
           & G.Signature;
         H    : constant Header := To_Header (G);
      begin
         Check ("GRANT: length 263 and bytes equal the hand-built layout",
                E'Length = 263 and then E = Want and then Is_Grant_Frame (E)
                and then Kind_Of (E) = K_Grant);
         Decode (E, Back, St);
         Check ("GRANT: decode OK and equal", St = OK and then Back = G);
         Check ("GRANT: well-formed", Well_Formed (Back));
         Decode_Verified (E, Back, St);
         Check ("GRANT: Decode_Verified OK", St = OK and then Back = G);
         Lemma_Decode_Encode (G);
         Lemma_Encode_Decode_Grant (E);
         Check ("GRANT: Encode (Decode (frame)) = frame", Encode (Back) = E);
         Check ("GRANT header: V = (0, subject, 0, h), issuer = signer",
                H.K = K_Grant and then H.NS = To_Id128 (NS_A)
                and then H.Ent = Zero_Id and then H.FH = Zero_Key
                and then H.V.T = 0 and then H.V.Author = To_Key256 (Author_PK)
                and then H.V.Seq = 0 and then H.V.H = H_Of (E)
                and then H.Issuer = To_Key256 (Root_PK) and then H.Del_TTL = 0
                and then Signer_Key (G) = To_Key256 (Root_PK));
         Lemma_Header_Canonical (G);
         Check ("GRANT header: Kome.Headers.Canonical", Kome.Headers.Canonical (H));
         Keep := Back;
         Decode (E (0 .. E'Last - 1), Back, St);
         Check ("GRANT truncated refused, record unchanged",
                St = Malformed and then Back = Keep);
         Decode (E & Byte'(0), Back, St);
         Check ("GRANT oversized refused, record unchanged",
                St = Malformed and then Back = Keep);
         declare
            Bad : Byte_Array := E;
         begin
            Bad (0) := Tag_Revoke;
            Decode (Bad, Back, St);
            Check ("GRANT wrong tag refused", St = Malformed and then Back = Keep);
            Bad := E;
            Bad (180) := Bad (180) xor 1;   --  subject byte 13 (subject is 167 .. 198)
            Decode (Bad, Back, St);
            Check ("GRANT tampered subject: decodes, not well-formed",
                   St = OK and then Back.C.Subject /= Author_PK
                   and then not Well_Formed (Back));
            Keep := Back;
            Bad := E;
            Bad (240) := Bad (240) xor 1;   --  signature
            Decode_Verified (Bad, Back, St);
            Check ("GRANT tampered signature: Decode_Verified refuses, unchanged",
                   St = Malformed and then Back = Keep);
            Bad := E;
            Bad (99) := Bad (99) xor 1;     --  cert_cap byte 2 (cert_cap is 97 .. 102)
            Decode (Bad, Back, St);
            Check ("GRANT tampered cert_cap: not well-formed",
                   St = OK and then Back.C.Cert_Cap /= 0 and then not Well_Formed (Back));
         end;
      end;

      declare
         function V (Y : in out Grant_Record; SK : Kome.Crypto.Secret_Key) return Status is
            S : Status;
         begin
            Sign (Y, SK);
            Keep := Back;
            Decode_Verified (Encode (Y), Back, S);
            if S = Malformed and then Back /= Keep then
               Check ("GRANT refusal leaves the record unchanged", False);
            end if;
            return S;
         end V;
         Y : Grant_Record;
      begin
         Y := Make_Grant (Root_PK, Salt_A, Author_PK, 0, Zero_Sig, Author_PK);
         St := V (Y, Author_SK);
         Check ("GRANT outsider-signed (granting itself): Malformed",
                St = Malformed and then not Well_Formed (Y)
                and then Kome.Crypto.Verify (Y.Signature, Author_PK, Hash (Y.C)));
         Y := Make_Grant (Root_PK, Salt_A, Other_PK, Cap_2, Cert_2, Author_PK);
         St := V (Y, Other_SK);
         Check ("GRANT by certified root: OK, issuer is the signer",
                St = OK and then Back = Y
                and then To_Header (Y).Issuer = To_Key256 (Other_PK)
                and then To_Header (Y).V.Author = To_Key256 (Author_PK));
         Y := Make_Grant (Root_PK, Salt_A, Other_PK, Cap_2,
                          Make_Cert (Root_SK, NS_B, Other_PK, Cap_2), Author_PK);
         St := V (Y, Other_SK);
         Check ("GRANT with a certificate made for another ns: Malformed", St = Malformed);
         Y := Make_Grant (Root_PK, Salt_A, Root_PK, 0, Cert_2, Author_PK);
         St := V (Y, Root_SK);
         Check ("GRANT by founding key with a nonzero cert_sig: Malformed", St = Malformed);
         Y := Make_Grant (Root_PK, Salt_A, Root_PK, 0, Zero_Sig, Author_PK);
         Y.C.NS (3) := Y.C.NS (3) xor 1;
         St := V (Y, Root_SK);
         Check ("GRANT with ns not derived from (root_pk, salt): Malformed", St = Malformed);
      end;
   end;

   ---------------------------------------------------------------------------
   --  Frame accessors: Root_Key_Of, Roster_Lists_DH, Is_Founding_Revoke.
   ---------------------------------------------------------------------------
   declare
      Mem : constant Byte_Array := Members_Of (3, 61);
      Ro  : Roster_Record :=
        Make_Roster (Root_PK, Salt_A, Root_PK, 0, Zero_Sig, Box_A, 1, 100, TTL_OK, 0,
                     [], Mem);
      Rv1 : Revoke_Record :=
        Make_Revoke (Root_PK, Salt_A, Root_PK, 0, Zero_Sig, Other_PK, 0, 1);
      Rv2 : Revoke_Record :=
        Make_Revoke (Root_PK, Salt_A, Other_PK, Cap_2, Cert_2, Author_PK, 0, 1);
      Gr  : Grant_Record :=
        Make_Grant (Root_PK, Salt_A, Other_PK, Cap_2, Cert_2, Author_PK);
      Alien : constant Revoke_Record :=
        Make_Revoke (Author_PK, Salt_A, Author_PK, 0, Zero_Sig, Other_PK, 0, 1);
   begin
      Sign (Ro, Root_SK);
      Sign (Rv1, Root_SK);
      Sign (Rv2, Other_SK);
      Sign (Gr, Other_SK);
      declare
         ER  : constant Byte_Array := Encode (Ro);
         EV1 : constant Byte_Array := Encode (Rv1);
         EV2 : constant Byte_Array := Encode (Rv2);
         EG  : constant Byte_Array := Encode (Gr);
         EA  : constant Byte_Array := Encode (Alien);
         Shifted : Byte_Array (500 .. 500 + ER'Length - 1);
      begin
         Shifted := ER;
         Check ("Root_Key_Of: ROSTER, REVOKE, GRANT give root_pk",
                Is_Auth_Frame (ER) and then Root_Key_Of (ER) = To_Key256 (Root_PK)
                and then Root_Key_Of (EV1) = To_Key256 (Root_PK)
                and then Root_Key_Of (EV2) = To_Key256 (Root_PK)
                and then Root_Key_Of (EG) = To_Key256 (Root_PK)
                and then Root_Key_Of (Shifted) = To_Key256 (Root_PK));
         Check ("Root_Key_Of: another collection's founding key, not the signer",
                Root_Key_Of (EA) = To_Key256 (Author_PK)
                and then Root_Key_Of (EV2) /= To_Key256 (Other_PK));
         Lemma_Roster_Lists_DH (ER, Mem (Pubkey_Len .. 2 * Pubkey_Len - 1));
         Lemma_Roster_Lists_DH (ER, Box_A);
         Check ("Roster_Lists_DH: each member's dh_pk is listed",
                Roster_Lists_DH (ER, Mem (Pubkey_Len .. 2 * Pubkey_Len - 1))
                and then Roster_Lists_DH
                  (ER, Mem (Member_Len + Pubkey_Len .. Member_Len + 2 * Pubkey_Len - 1))
                and then Roster_Lists_DH
                  (ER, Mem (2 * Member_Len + Pubkey_Len .. 2 * Member_Len + 2 * Pubkey_Len - 1))
                and then Roster_Lists_DH
                  (Shifted, Mem (2 * Member_Len + Pubkey_Len
                                 .. 2 * Member_Len + 2 * Pubkey_Len - 1)));
         Check ("Roster_Lists_DH: box_pk, a sign_pk and a stranger are not",
                not Roster_Lists_DH (ER, Box_A)
                and then not Roster_Lists_DH (ER, Mem (0 .. Pubkey_Len - 1))
                and then not Roster_Lists_DH (ER, Good_DH (99)));
         declare
            E0 : constant Byte_Array := Encode
              (Make_Roster (Root_PK, Salt_A, Root_PK, 0, Zero_Sig, Box_A, 1, 100, TTL_OK, 0,
                            [], []));
         begin
            Lemma_Roster_Lists_DH (E0, Box_A);
            Check ("Roster_Lists_DH: a roster with no members lists nothing",
                   not Roster_Lists_DH (E0, Box_A)
                   and then not Roster_Lists_DH (E0, Mem (Pubkey_Len .. 2 * Pubkey_Len - 1)));
         end;
         Check ("Is_Founding_Revoke: founding-signed REVOKE",
                Is_Founding_Revoke (EV1));
         Check ("Is_Founding_Revoke: not a certified root's REVOKE, a GRANT or a ROSTER",
                not Is_Founding_Revoke (EV2) and then not Is_Founding_Revoke (EG)
                and then not Is_Founding_Revoke (ER)
                and then not Is_Founding_Revoke (EV1 (0 .. EV1'Last - 1)));
      end;
   end;

   ---------------------------------------------------------------------------
   --  Known answers (vectors/records.txt): layout, h and the certificate
   --  hash, independent of this package.
   ---------------------------------------------------------------------------
   declare
      Path  : constant String := Find ("vectors/records.txt");
      F     : File_Type;
      Line  : String (1 .. 32_768);
      Last  : Natural;
      N     : Natural := 0;
      NS_V  : constant NS_Id  := NS_Id (Fill (16, 1));
      Ent_V : constant Ent_Id := Ent_Id (Fill (16, 2));
      Au_V  : constant Pubkey := Pubkey (Fill (32, 4));
      Rt_V  : constant Pubkey := Pubkey (Fill (32, 8));
      Sa_V  : constant Salt   := Salt (Fill (16, 9));
      Sg_V  : constant Pubkey := Pubkey (Fill (32, 10));

      procedure One (Name : String; Content, H : Byte_Array) is
         Ok : Boolean := False;
      begin
         if Name = "put1" or else Name = "put2" then
            declare
               R : constant Put_Record :=
                 (if Name = "put1"
                  then Make_Put (NS_V, Ent_V, Fill (5, 3), 16#0102_0304_0506#, 7, Au_V,
                                 Fill (10, 5))
                  else Make_Put (NS_V, Ent_V, Fill (32, 6), 0, Max_U48, Au_V, []));
            begin
               Ok := Content_Bytes (R.C) = Content and then Hash (R.C) = H
                     and then Encode (R) = Content & Zero_Sig;
            end;
         elsif Name = "del1" then
            declare
               R : constant Del_Record :=
                 (C => (NS => NS_V, Ent => Ent_V, T => 1234, Seq => Max_U48, Author => Au_V),
                  Signature => [others => 0]);
            begin
               Ok := Content_Bytes (R.C) = Content and then Hash (R.C) = H
                     and then Encode (R) = Content & Zero_Sig;
            end;
         elsif Name = "roster1" or else Name = "roster2" or else Name = "roster3" then
            declare
               R : constant Roster_Record :=
                 (if Name = "roster1"
                  then Make_Roster (Rt_V, Sa_V, Sg_V, 5000, Sig (Fill (64, 11)),
                                    Pubkey (Fill (32, 15)), 3, 1000, 30 * Day, 513,
                                    Fill (148, 12), Fill (272, 13))
                  elsif Name = "roster2"
                  then Make_Roster (Rt_V, Sa_V, Rt_V, 0, Zero_Sig, Pubkey (Fill (32, 16)),
                                    0, 0, 0, 0, [], [])
                  else Make_Roster (Rt_V, Sa_V, Rt_V, 0, Zero_Sig, Pubkey (Fill (32, 17)),
                                    Max_U48, Max_U48, 3650 * Day, 65_535,
                                    Fill (74 * 15, 18), Fill (136 * 64, 19)));
            begin
               Ok := Content_Bytes (R.C) = Content and then Hash (R.C) = H
                     and then Encode (R) = Content & Zero_Sig;
               if Ok then
                  Lemma_Encode_Decode_Roster (Encode (R));
                  Ok := Parse_Roster (Encode (R)) = R;
               end if;
            end;
         elsif Name = "revoke1" then
            declare
               R : constant Revoke_Record :=
                 Make_Revoke (Rt_V, Sa_V, Sg_V, 5000, Sig (Fill (64, 11)),
                              Pubkey (Fill (32, 14)), 777, 1);
            begin
               Ok := Content_Bytes (R.C) = Content and then Hash (R.C) = H
                     and then Encode (R) = Content & Zero_Sig;
            end;
         elsif Name = "grant1" then
            declare
               R : constant Grant_Record :=
                 Make_Grant (Rt_V, Sa_V, Sg_V, Max_U48, Sig (Fill (64, 20)),
                             Pubkey (Fill (32, 21)));
            begin
               Ok := Content_Bytes (R.C) = Content and then Hash (R.C) = H
                     and then Encode (R) = Content & Zero_Sig;
            end;
         elsif Name = "cert1" then
            Ok := Cert_Input (Collection_Id (Rt_V, Sa_V), Sg_V, 16#0000_0102_0304#) = Content
                  and then Cert_Hash (Collection_Id (Rt_V, Sa_V), Sg_V, 16#0000_0102_0304#) = H;
         end if;
         Check ("vector " & Name & ": bytes and hash", Ok);
         N := N + 1;
      end One;
   begin
      if not Ada.Directories.Exists (Path) then
         Check ("vectors present (" & Path & ")", False);
      else
         Open (F, In_File, Path);
         while not End_Of_File (F) loop
            Get_Line (F, Line, Last);
            if Last > 0 and then Line (1) /= '#' then
               declare
                  S1 : Natural := 0;
                  S2 : Natural := 0;
               begin
                  for I in 1 .. Last loop
                     if Line (I) = ' ' then
                        if S1 = 0 then
                           S1 := I;
                        elsif S2 = 0 then
                           S2 := I;
                        end if;
                     end if;
                  end loop;
                  if S1 > 0 and then S2 > S1 then
                     One (Line (1 .. S1 - 1),
                          From_Hex (Line (S1 + 1 .. S2 - 1)),
                          From_Hex (Line (S2 + 1 .. Last)));
                  else
                     Check ("vector line well-formed", False);
                  end if;
               end;
            end if;
         end loop;
         Close (F);
         Check ("vectors: all nine present", N = 9);
      end if;
   end;

   if Failed then
      Set_Exit_Status (Failure);
   end if;
end Test_Records;
