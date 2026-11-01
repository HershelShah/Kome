--  Test main for Kome.Records (DESIGN.md §2, T13). Every kind is encoded,
--  decoded and verified at its extreme sizes (empty value, 65 535-byte value,
--  32-byte field, 4 roots, 64 members, u48 at 0 and 2**48 - 1); truncated,
--  oversized, mistagged and out-of-bound frames are refused with the record
--  unchanged; a tampered signature, content byte or ns is refused by
--  Well_Formed; ROSTER / REVOKE issued by a listed secondary root are
--  well-formed and by an unlisted or mismatched key are not (module J,
--  DESIGN.md §6); the header fields are as DESIGN.md §2 / Kome.Headers say,
--  checked against values computed here from the frame bytes (not through
--  Kome.Records.Hash), and satisfy Kome.Views.Canonical. Known answers in
--  vectors/records.txt pin each layout and h independently of this package.
--  Compiled with -gnata, so every Pre / Post and the round-trip lemmas are
--  also executed on these records.
pragma Ada_2022;
with Ada.Text_IO;      use Ada.Text_IO;
with Ada.Command_Line; use Ada.Command_Line;
with Ada.Directories;
with Kome;             use Kome;
with Kome.Headers;     use Kome.Headers;
with Kome.Keys;        use Kome.Keys;
with Kome.Crypto;
with Kome.Records;     use Kome.Records;
with Kome.Views;

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
   NS_A   : NS_Id;
   Ent_A  : constant Ent_Id := Ent_Id (Fill (Ent_Len, 40));

   Max_U48 : constant U48 := U48'Last;

begin
   Kome.Crypto.Key_Pair (Seed_Of (1), Author_SK, Author_PK);
   Kome.Crypto.Key_Pair (Seed_Of (2), Other_SK, Other_PK);
   Kome.Crypto.Key_Pair (Seed_Of (3), Root_SK, Root_PK);
   NS_A := Collection_Id (Root_PK, Salt_A);

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
                and then E (0) = Tag_Put and then E (33) = 1
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
      Value_64 : constant Byte_Array := Fill (Value_Max, 3);
      Big      : Put_Record :=
        Make_Put (NS_A, Ent_A, Field_32, Max_U48, Max_U48, Author_PK, Value_64);
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
         Check ("PUT max: length 65711 (32-byte field, 65535-byte value)",
                L = 1 + 16 + 16 + 1 + 32 + 6 + 6 + 32 + 2 + 65_535 + 64
                and then L = Put_Frame_Max and then L = Frame_Max);
         Check ("PUT max: layout bytes",
                E (1 .. 16) = NS_A and then E (17 .. 32) = Ent_A
                and then E (33) = 32 and then E (34 .. 65) = Field_32
                and then E (34 + FL .. 39 + FL) = BE48 (Max_U48)
                and then E (40 + FL .. 45 + FL) = BE48 (Max_U48)
                and then E (46 + FL .. 77 + FL) = Author_PK
                and then E (78 + FL) = 16#FF# and then E (79 + FL) = 16#FF#
                and then E (80 + FL .. L - 65) = Value_64
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

         --  Header (DESIGN.md §2 / Kome.Headers).
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
            Check ("PUT header: ceiling 0", H.Ceiling = 0);
            Check ("PUT header: h = BLAKE2b-256 (frame minus sig)",
                   To_Key256 (Hash (Big.C)) = H_Of (E));
            Lemma_Header_Canonical (Big);
            Check ("PUT header: Kome.Views.Canonical", Kome.Views.Canonical (H));
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
           [Tag_Del] & NS_A & Ent_A & BE48 (1234) & BE48 (Max_U48) & Author_PK & D.Signature;
         H    : constant Header := To_Header (D);
      begin
         Check ("DEL: length 141 and bytes equal the hand-built layout",
                E'Length = 141 and then E = Want);
         Decode (E, Back, St);
         Check ("DEL: decode OK and equal", St = OK and then Back = D);
         Check ("DEL: well-formed", Well_Formed (Back));
         Lemma_Decode_Encode (D);
         Lemma_Encode_Decode_Del (E);
         Check ("DEL header: V = (t, author, seq, h), FH 0, ceiling 0",
                H.K = K_Del and then H.NS = To_Id128 (NS_A)
                and then H.Ent = To_Id128 (Ent_A)
                and then H.FH = Key256'(others => 0)
                and then H.V.T = 1234 and then H.V.Author = To_Key256 (Author_PK)
                and then H.V.Seq = Max_U48 and then H.V.H = H_Of (E)
                and then H.Ceiling = 0);
         Lemma_Header_Canonical (D);
         Check ("DEL header: Kome.Views.Canonical", Kome.Views.Canonical (H));
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
         Check ("Kind_Of reads the tag",
                Has_Kind (E) and then Kind_Of (E) = K_Del
                and then not Has_Kind ([Byte'(4)]));
      end;
   end;

   ---------------------------------------------------------------------------
   --  ROSTER
   ---------------------------------------------------------------------------
   declare
      Roots_4    : constant Byte_Array := Fill (4 * Pubkey_Len, 11);
      Members_64 : constant Byte_Array := Fill (64 * Member_Len, 77);
      Prev       : constant Hash256 := Hash256 (Fill (Hash_Len, 55));
      Big  : Roster_Record :=
        Make_Roster (Root_PK, Salt_A, Root_PK, Prev, Max_U48, 5000, 86_400_000, 65_535,
                     Roots_4, Members_64);
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
         Check ("ROSTER max: length 9047 (4 roots, 64 members)",
                L = 1 + 16 + 32 + 16 + 32 + 32 + 6 + 6 + 6 + 2 + 1 + 128 + 1 + 64 * 136 + 64
                and then L = Roster_Frame_Max);
         Check ("ROSTER max: layout bytes",
                E (0) = Tag_Roster and then E (1 .. 16) = NS_A
                and then E (17 .. 48) = Root_PK and then E (49 .. 64) = Salt_A
                and then E (65 .. 96) = Root_PK and then E (97 .. 128) = Prev
                and then E (129 .. 134) = BE48 (Max_U48)
                and then E (135 .. 140) = BE48 (5000)
                and then E (141 .. 146) = BE48 (86_400_000)
                and then E (147 .. 148) = [16#FF#, 16#FF#]
                and then E (149) = 4 and then E (150 .. 277) = Roots_4
                and then E (278) = 64 and then E (279 .. 279 + 8704 - 1) = Members_64
                and then E (L - 64 .. L - 1) = Big.Signature);
         Decode (E, Back, St);
         Check ("ROSTER max: decode OK and equal", St = OK and then Back = Big);
         Check ("ROSTER max: well-formed (founder-signed)", Well_Formed (Back));
         Lemma_Decode_Encode (Big);
         Lemma_Encode_Decode_Roster (E);
         Lemma_Root_Bytes (Back.C, 4);
         Lemma_Member_Bytes (Back.C, 64);
         Lemma_Member_Bytes (Back.C, 1);
         Check ("ROSTER accessors: root 4, member 64",
                Root (Back.C, 4) = Roots_4 (96 .. 127)
                and then Member_Sign_PK (Back.C, 64) = Members_64 (63 * 136 .. 63 * 136 + 31)
                and then Member_DH_PK (Back.C, 64) = Members_64 (63 * 136 + 32 .. 63 * 136 + 63)
                and then Member_Nonce (Back.C, 64) = Members_64 (63 * 136 + 64 .. 63 * 136 + 87)
                and then Member_Box (Back.C, 64) = Members_64 (63 * 136 + 88 .. 63 * 136 + 135)
                and then Member_Key (Back.C, 1) = To_Key256 (Members_64 (0 .. 31)));
         Check ("ROSTER header: V = (0, signer, gen, h), ceiling = ceiling_t",
                H.K = K_Roster and then H.NS = To_Id128 (NS_A)
                and then H.Ent = Id128'(others => 0) and then H.FH = Key256'(others => 0)
                and then H.V.T = 0 and then H.V.Author = To_Key256 (Root_PK)
                and then H.V.Author = Signer_Key (Big)
                and then H.V.Seq = Max_U48 and then H.V.H = H_Of (E)
                and then H.Ceiling = 5000);
         Lemma_Header_Canonical (Big);
         Check ("ROSTER header: Kome.Views.Canonical", Kome.Views.Canonical (H));

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
            Bad (149) := 5;   --  n_roots 5
            Decode (Bad, Back, St);
            Check ("ROSTER n_roots 5 refused", St = Malformed and then Back = Keep);
            Bad := E;
            Bad (278) := 65;   --  n_members 65
            Decode (Bad, Back, St);
            Check ("ROSTER n_members 65 refused", St = Malformed and then Back = Keep);
            Bad := E;
            Bad (149) := 255;   --  n_roots past the end: n_members never read
            Decode (Bad, Back, St);
            Check ("ROSTER n_roots 255 refused", St = Malformed and then Back = Keep);
            Bad := E;
            Bad (L - 30) := Bad (L - 30) xor 2;
            Decode (Bad, Back, St);
            Check ("ROSTER tampered signature: not well-formed",
                   St = OK and then Back.C = Big.C and then not Well_Formed (Back));
            Bad := E;
            Bad (100) := Bad (100) xor 2;   --  prev_h byte 3
            Decode (Bad, Back, St);
            Check ("ROSTER tampered prev_h: not well-formed",
                   St = OK and then Back.C.Prev_H /= Prev and then not Well_Formed (Back));
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
         Check ("ROSTER signed by a key other than signer is not well-formed",
                not Well_Formed (Wrong));
         Wrong := Big;
         Wrong.C.N_Members := 63;   --  member 64's bytes become padding
         Check ("ROSTER nonzero member padding is not canonical",
                not Canonical (Wrong) and then not Well_Formed (Wrong));
      end;

      --  Module J: a roster issued by a listed secondary root.
      declare
         Roots_2 : constant Byte_Array := Root_PK & Other_PK;
         Sec     : Roster_Record :=
           Make_Roster (Root_PK, Salt_A, Other_PK, Hash (Big.C), 7, 6000, 1000, 2,
                        Roots_2, Members_64 (0 .. Member_Len - 1));
         Unl     : Roster_Record :=
           Make_Roster (Root_PK, Salt_A, Author_PK, Hash (Big.C), 7, 6000, 1000, 2,
                        Roots_2, Members_64 (0 .. Member_Len - 1));
      begin
         Sign (Sec, Other_SK);
         Sign (Unl, Author_SK);
         Lemma_Signer_Listed (Sec.C);
         Lemma_Signer_Listed (Unl.C);
         Check ("ROSTER by listed secondary root: signer listed, well-formed",
                Signer_Listed (Sec.C) and then Root (Sec.C, 2) = Other_PK
                and then Well_Formed (Sec));
         Check ("ROSTER by secondary root: header author is the signer, not root_pk",
                To_Header (Sec).V.Author = To_Key256 (Other_PK)
                and then To_Header (Sec).V.Author /= To_Key256 (Root_PK)
                and then Signer_Key (Sec) = To_Key256 (Other_PK));
         Check ("ROSTER by unlisted key (valid signature) is not well-formed",
                not Signer_Listed (Unl.C) and then not Well_Formed (Unl)
                and then Kome.Crypto.Verify (Unl.Signature, Author_PK, Hash (Unl.C)));
         declare
            E : constant Byte_Array := Encode (Sec);
         begin
            Decode_Verified (E, Back, St);
            Check ("ROSTER by secondary root: Decode_Verified accepts",
                   St = OK and then Back = Sec);
            Keep := Back;
            Decode_Verified (Encode (Unl), Back, St);
            Check ("ROSTER by unlisted key: Decode_Verified refuses, unchanged",
                   St = Malformed and then Back = Keep);
         end;
      end;

      --  Empty roster: no roots, no members.
      declare
         Empty_R : Roster_Record :=
           Make_Roster (Root_PK, Salt_A, Root_PK, [others => 0], 0, 0, 0, 0, [], []);
      begin
         Sign (Empty_R, Root_SK);
         declare
            E : constant Byte_Array := Encode (Empty_R);
         begin
            Decode (E, Back, St);
            Check ("ROSTER empty: length 215, round trip, well-formed",
                   E'Length = 215 and then E (149) = 0 and then E (150) = 0
                   and then St = OK and then Back = Empty_R and then Well_Formed (Back));
            Lemma_Decode_Encode (Empty_R);
            Lemma_Encode_Decode_Roster (E);
         end;
      end;
   end;

   ---------------------------------------------------------------------------
   --  REVOKE
   ---------------------------------------------------------------------------
   declare
      X    : Revoke_Record := Make_Revoke (Root_PK, Salt_A, Root_PK, Author_PK, 777, 1);
      Back : Revoke_Record;
      Keep : Revoke_Record;
      St   : Status;
   begin
      Sign (X, Root_SK);
      declare
         E    : constant Byte_Array := Encode (X);
         Want : constant Byte_Array :=
           [Tag_Revoke] & NS_A & Root_PK & Salt_A & Root_PK & Author_PK
           & BE48 (777) & BE48 (1) & X.Signature;
         H    : constant Header := To_Header (X);
      begin
         Check ("REVOKE: length 205 and bytes equal the hand-built layout",
                E'Length = 205 and then E = Want);
         Decode (E, Back, St);
         Check ("REVOKE: decode OK and equal", St = OK and then Back = X);
         Check ("REVOKE: well-formed", Well_Formed (Back));
         Lemma_Decode_Encode (X);
         Lemma_Encode_Decode_Revoke (E);
         Check ("REVOKE header: V = (from_t, sign_pk, rev_seq, h)",
                H.K = K_Revoke and then H.NS = To_Id128 (NS_A)
                and then H.Ent = Id128'(others => 0) and then H.FH = Key256'(others => 0)
                and then H.V.T = 777 and then H.V.Author = To_Key256 (Author_PK)
                and then H.V.Seq = 1 and then H.V.H = H_Of (E) and then H.Ceiling = 0
                and then Signer_Key (X) = To_Key256 (Root_PK));
         Lemma_Header_Canonical (X);
         Check ("REVOKE header: Kome.Views.Canonical", Kome.Views.Canonical (H));
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
            Bad (150) := Bad (150) xor 1;   --  signature byte 9 (sig is 141 .. 204)
            Decode_Verified (Bad, Back, St);
            Check ("REVOKE tampered signature: Decode_Verified refuses, unchanged",
                   St = Malformed and then Back = Keep);
            Bad := E;
            Bad (132) := Bad (132) xor 1;   --  from_t (129 .. 134)
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

      --  Module J: a REVOKE issued by a secondary root verifies under its
      --  signer; one whose signer field names another key does not.
      declare
         Sec : Revoke_Record := Make_Revoke (Root_PK, Salt_A, Other_PK, Author_PK, 9, 2);
      begin
         Sign (Sec, Other_SK);
         Check ("REVOKE by secondary root: well-formed, signer key, subject in header",
                Well_Formed (Sec) and then Signer_Key (Sec) = To_Key256 (Other_PK)
                and then To_Header (Sec).V.Author = To_Key256 (Author_PK));
         Sec.C.Signer := Root_PK;
         Check ("REVOKE whose signer field is not the signing key is not well-formed",
                not Well_Formed (Sec));
      end;
   end;

   ---------------------------------------------------------------------------
   --  Known answers (vectors/records.txt): layout and h, independent of this
   --  package.
   ---------------------------------------------------------------------------
   declare
      Path  : constant String := Find ("vectors/records.txt");
      F     : File_Type;
      Line  : String (1 .. 4096);
      Last  : Natural;
      N     : Natural := 0;
      NS_V  : constant NS_Id  := NS_Id (Fill (16, 1));
      Ent_V : constant Ent_Id := Ent_Id (Fill (16, 2));
      Au_V  : constant Pubkey := Pubkey (Fill (32, 4));
      Rt_V  : constant Pubkey := Pubkey (Fill (32, 8));
      Sa_V  : constant Salt   := Salt (Fill (16, 9));
      Sg_V  : constant Pubkey := Pubkey (Fill (32, 10));
      Pv_V  : constant Hash256 := Hash256 (Fill (32, 11));
      Zero_Sig : constant Byte_Array (0 .. Sig_Len - 1) := [others => 0];

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
         elsif Name = "roster1" or else Name = "roster2" then
            declare
               R : constant Roster_Record :=
                 (if Name = "roster1"
                  then Make_Roster (Rt_V, Sa_V, Sg_V, Pv_V, 3, 1000, 86_400_000, 513,
                                    Fill (64, 12), Fill (272, 13))
                  else Make_Roster (Rt_V, Sa_V, Rt_V, [others => 0], 0, 0, 0, 0, [], []));
            begin
               Ok := Content_Bytes (R.C) = Content and then Hash (R.C) = H
                     and then Encode (R) = Content & Zero_Sig;
            end;
         elsif Name = "revoke1" then
            declare
               R : constant Revoke_Record :=
                 Make_Revoke (Rt_V, Sa_V, Sg_V, Pubkey (Fill (32, 14)), 777, 1);
            begin
               Ok := Content_Bytes (R.C) = Content and then Hash (R.C) = H
                     and then Encode (R) = Content & Zero_Sig;
            end;
         end if;
         Check ("vector " & Name & ": frame and h", Ok);
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
         Check ("vectors: all six present", N = 6);
      end if;
   end;

   if Failed then
      Set_Exit_Status (Failure);
   end if;
end Test_Records;
