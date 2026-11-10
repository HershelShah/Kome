--  Test main for Kome.Records (SIMPLIFY.md §2 S1-S4, DESIGN.md §2, §3, T13).
--  It checks these items:
--    * The collection context: cid = BLAKE2b-256 (root_pk ‖ salt ‖ u48
--      (del_ttl)), ns = cid[0:16], and h = BLAKE2b-256 (tag ‖ cid ‖
--      content) for every kind; a record is well-formed under its own cid
--      only (another salt or another del_ttl is another collection).
--    * Every kind encodes, decodes and verifies at its extreme sizes (empty
--      value, 40 960-byte value, 32-byte field, 64 members, u48 at 0 and
--      2**48 - 1).
--    * Decode refuses truncated, oversized, mistagged and out-of-bound
--      frames, and the record does not change.
--    * Well_Formed refuses a tampered signature or content byte.
--    * The signer block (D1, S3). Every signer carries a certificate from
--      the founding key, the founding key its own (cap 2^48 - 1); there is
--      no zero-certificate case. A ROSTER, REVOKE or GRANT that an outsider
--      signs is Malformed. The records of a certified root are
--      well-formed, but its roster above cert_cap is not. A certificate for
--      a different cid or cap is refused. A REVOKE of root_pk is refused.
--    * E5: a dh_pk or box_pk that is p or low order is Malformed.
--    * D12: vlen 40 960 decodes, and vlen 40 961 is refused.
--    * The header fields agree with DESIGN.md §3 / Kome.Headers, and they
--      satisfy Kome.Headers.Canonical (D3). The GRANT header carries the
--      issuer's cert_cap (wcap, S3). The test calculates the expected
--      values here from the frame bytes (not through Kome.Records.Hash).
--    * Known answers in vectors/records.txt pin each layout, h, the cid
--      and the certificate hash, independently of this package.
--  The test compiles with -gnata, so every Pre / Post and the ghost lemmas
--  also execute on these records.
pragma Ada_2022;
with Ada.Text_IO;      use Ada.Text_IO;
with Ada.Command_Line; use Ada.Command_Line;
with Ada.Directories;
with Ada.Assertions;
with Contract_Mode;    use Contract_Mode;
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
   --  byte made less than 16#40#.
   function Good_DH (Seed : Natural) return Pubkey is
      K : Pubkey := Pubkey (Fill (Pubkey_Len, Seed));
   begin
      K (31) := K (31) and 16#3F#;
      return K;
   end Good_DH;

   --  N members { sign_pk dh_pk nonce box }. Each dh_pk is a good key.
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

   --  The h of a frame under the collection context Cid: BLAKE2b-256 (tag
   --  ‖ cid ‖ content), written here from the frame bytes, independently
   --  of Kome.Records.Hash_Input.
   function H_Of (Frame : Byte_Array; Cid : Hash256) return Key256 is
     (To_Key256 (Kome.Crypto.Blake2b_256
        (Frame (Frame'First .. Frame'First) & Cid
         & Frame (Frame'First + 1 .. Frame'Last - Sig_Len))));

   --  BLAKE2b-256 (tag ‖ content): the h of an earlier design, which no
   --  kind uses now.
   function H_Plain (Frame : Byte_Array) return Key256 is
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

   --  check.sh runs the binary from spark. Also accept bin/<module>.
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

   Max_U48 : constant U48 := U48'Last;
   Day     : constant U48 := 86_400_000;
   TTL_OK  : constant U48 := 30 * Day;

   Salt_A : constant Salt := Salt (Fill (Salt_Len, 90));
   Salt_B : constant Salt := Salt (Fill (Salt_Len, 91));
   Cid_A  : Hash256;   --  the collection of (Root_PK, Salt_A, TTL_OK)
   Cid_B  : Hash256;   --  (Root_PK, Salt_B, TTL_OK): another salt
   Cid_T  : Hash256;   --  (Root_PK, Salt_A, TTL_OK + 1): another del_ttl
   NS_A   : NS_Id;
   Ent_A  : constant Ent_Id := Ent_Id (Fill (Ent_Len, 40));

   --  X25519 encodings that decode refuses (E5): p itself (not reduced)
   --  and low-order points.
   P_Enc   : constant Pubkey := Pubkey (From_Hex
     ("edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f"));
   Order_8 : constant Pubkey := Pubkey (From_Hex
     ("e0eb7a7c3b41b8ae1656e3faf19fc46ada098deb9c32b1fd866205165f49b800"));
   U_One   : constant Pubkey := [0 => 1, others => 0];
   U_Zero  : constant Pubkey := [others => 0];

   --  The founding key's certificate of itself (S3), and the certified
   --  secondary root: the founding key certifies Other_PK for Cid_A up to
   --  Cap_2.
   Cert_R : Sig;
   Cap_2  : constant U48 := 10_000;
   Cert_2 : Sig;

   Box_A  : constant Pubkey := Good_DH (15);

begin
   Kome.Crypto.Key_Pair (Seed_Of (1), Author_SK, Author_PK);
   Kome.Crypto.Key_Pair (Seed_Of (2), Other_SK, Other_PK);
   Kome.Crypto.Key_Pair (Seed_Of (3), Root_SK, Root_PK);
   Cid_A := Cid_Of (Root_PK, Salt_A, TTL_OK);
   Cid_B := Cid_Of (Root_PK, Salt_B, TTL_OK);
   Cid_T := Cid_Of (Root_PK, Salt_A, TTL_OK + 1);
   NS_A  := NS_Of (Cid_A);
   Check ("S1: cid = BLAKE2b-256 (root_pk ‖ salt ‖ u48 (del_ttl)), ns = cid[0:16]",
          Cid_A = Kome.Crypto.Blake2b_256 (Root_PK & Salt_A & BE48 (TTL_OK))
          and then Cid_Input (Root_PK, Salt_A, TTL_OK) = Root_PK & Salt_A & BE48 (TTL_OK)
          and then NS_A = Cid_A (0 .. NS_Len - 1)
          and then Cid_A /= Cid_B and then Cid_A /= Cid_T and then Cid_B /= Cid_T);
   Check ("S1: Hash_Input puts the cid after the tag",
          Hash_Input (Cid_A, [1, 2, 3]) = [Byte'(1)] & Cid_A & [Byte'(2), 3]
          and then Hash_Input (Cid_A, [Byte'(9)]) = [Byte'(9)] & Cid_A);
   Cert_R := Make_Cert (Root_SK, Cid_A, Root_PK, Founding_Cap);
   Cert_2 := Make_Cert (Root_SK, Cid_A, Other_PK, Cap_2);

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
   --  Compile_Time_Error pragmas in the spec check Frame_Max = 160 +
   --  Value_Max = 41 120, PUT 129 .. 41 120, ROSTER 212 .. 8 916, REVOKE
   --  205, GRANT 199 and DEL 125. The checks below examine the encoded
   --  lengths.

   ---------------------------------------------------------------------------
   --  Certificates (D1, S3).
   ---------------------------------------------------------------------------
   declare
      Want : constant Byte_Array :=
        [16#6B#, 16#6F#, 16#6D#, 16#65#, 16#2F#, 16#72#, 16#6F#, 16#6F#, 16#74#]
        & Cid_A & Other_PK & BE48 (Cap_2);
   begin
      Check ("Cert_Input = ""kome/root"" ‖ cid ‖ signer ‖ u48 (cap), 79 bytes",
             Cert_Input (Cid_A, Other_PK, Cap_2)'Length = 79
             and then Cert_Input (Cid_A, Other_PK, Cap_2) = Want);
      Check ("Cert_Hash = BLAKE2b-256 (Cert_Input)",
             Cert_Hash (Cid_A, Other_PK, Cap_2) = Kome.Crypto.Blake2b_256 (Want));
      Check ("Make_Cert = Sign (founding, Cert_Hash), and it verifies",
             Cert_2 = Kome.Crypto.Sign (Root_SK, Cert_Hash (Cid_A, Other_PK, Cap_2))
             and then Kome.Crypto.Verify (Cert_2, Root_PK, Cert_Hash (Cid_A, Other_PK, Cap_2)));
      Check ("Cert_OK: the founding key with its own certificate (cap 2^48 - 1)",
             Cert_OK (Cid_A, Root_PK, Root_PK, Founding_Cap, Cert_R)
             and then Cert_OK (Cid_A, Root_PK, Root_PK, U48'Last, Cert_R));
      Check ("Cert_OK: the founding key with a zero block is refused (no exception, S3)",
             not Cert_OK (Cid_A, Root_PK, Root_PK, 0, Zero_Sig)
             and then not Cert_OK (Cid_A, Root_PK, Root_PK, Founding_Cap, Zero_Sig)
             and then not Cert_OK (Cid_A, Root_PK, Root_PK, Founding_Cap - 1, Cert_R));
      Check ("Cert_OK: certified root for this cid and cap",
             Cert_OK (Cid_A, Root_PK, Other_PK, Cap_2, Cert_2));
      Check ("Cert_OK: wrong cid (salt or del_ttl), cap, signer, founding key or a zero cert"
             & " is refused",
             not Cert_OK (Cid_B, Root_PK, Other_PK, Cap_2, Cert_2)
             and then not Cert_OK (Cid_T, Root_PK, Other_PK, Cap_2, Cert_2)
             and then not Cert_OK (Cid_A, Root_PK, Other_PK, Cap_2 + 1, Cert_2)
             and then not Cert_OK (Cid_A, Root_PK, Author_PK, Cap_2, Cert_2)
             and then not Cert_OK (Cid_A, Author_PK, Other_PK, Cap_2, Cert_2)
             and then not Cert_OK (Cid_A, Root_PK, Other_PK, Cap_2, Zero_Sig));
      Check ("Cert_OK: a certificate signed by a non-founding key is refused",
             not Cert_OK (Cid_A, Root_PK, Author_PK, Cap_2,
                          Make_Cert (Author_SK, Cid_A, Author_PK, Cap_2))
             and then not Cert_OK (Cid_A, Root_PK, Other_PK, Cap_2,
                                   Make_Cert (Author_SK, Cid_A, Other_PK, Cap_2)));
   end;

   ---------------------------------------------------------------------------
   --  PUT
   ---------------------------------------------------------------------------
   declare
      Field_N : constant Byte_Array := [Character'Pos ('n')];
      Small   : Put_Record := Make_Put (Cid_A, Ent_A, Field_N, 0, 0, Author_PK, []);
      Back    : Put_Record;
      St      : Status;
   begin
      Sign (Cid_A, Small, Author_SK);
      declare
         E : constant Byte_Array := Encode (Small);
      begin
         Check ("PUT minimal: length 129 (1-byte field, empty value)",
                E'Length = 129 and then E'Length = Frame_Len (Small)
                and then E'Length = Put_Frame_Min
                and then E (0) = Tag_Put and then E (0) = 4 and then E (17) = 1
                and then E (19 .. 24) = BE48 (0)
                and then E (63) = 0 and then E (64) = 0);
         Decode (E, Back, St);
         Check ("PUT minimal: decode OK and equal", St = OK and then Back = Small);
         Check ("PUT minimal: well-formed", Well_Formed (Cid_A, Back));
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
        Make_Put (Cid_A, Ent_A, Field_32, Max_U48, Max_U48, Author_PK, Value_M);
      Before   : Header;
      Back     : Put_Record;
      Keep     : Put_Record;
      St       : Status;
   begin
      Before := To_Header (Cid_A, Big);
      Sign (Cid_A, Big, Author_SK);
      Check ("PUT: signing changes neither h nor the header", To_Header (Cid_A, Big) = Before);
      declare
         E  : constant Byte_Array := Encode (Big);
         L  : constant Natural    := E'Length;
         FL : constant Natural    := Field_Max;
      begin
         Check ("PUT max: length 41120 (32-byte field, 40960-byte value)",
                L = 1 + 16 + 1 + 32 + 6 + 6 + 32 + 2 + 40_960 + 64
                and then L = Put_Frame_Max and then L = Frame_Max);
         Check ("PUT max: layout bytes (no ns)",
                E (1 .. 16) = Ent_A
                and then E (17) = 32 and then E (18 .. 49) = Field_32
                and then E (18 + FL .. 23 + FL) = BE48 (Max_U48)
                and then E (24 + FL .. 29 + FL) = BE48 (Max_U48)
                and then E (30 + FL .. 61 + FL) = Author_PK
                and then E (62 + FL) = 16#A0# and then E (63 + FL) = 16#00#
                and then E (64 + FL .. L - 65) = Value_M
                and then E (L - 64 .. L - 1) = Big.Signature);
         Decode (E, Back, St);
         Check ("PUT max: decode OK and equal", St = OK and then Back = Big);
         Check ("PUT max: well-formed", Well_Formed (Cid_A, Back));
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
            H : constant Header := To_Header (Cid_A, Big);
         begin
            Check ("PUT header: kind, ent", H.K = K_Put and then H.Ent = To_Id128 (Ent_A));
            Check ("PUT header: FH = BLAKE2b-256 (field name)",
                   H.FH = To_Key256 (Kome.Crypto.Blake2b_256 (Field_32)));
            Check ("PUT header: V = (t, author, seq, h)",
                   H.V.T = Max_U48 and then H.V.Author = To_Key256 (Author_PK)
                   and then H.V.Seq = Max_U48 and then H.V.H = H_Of (E, Cid_A));
            Check ("PUT header: no issuer", H.Issuer = Zero_Key);
            Check ("PUT header: h = BLAKE2b-256 (tag ‖ cid ‖ frame minus sig)",
                   To_Key256 (Hash (Cid_A, Big.C)) = H_Of (E, Cid_A));
            Lemma_Header_Canonical (Cid_A, Big);
            Check ("PUT header: Kome.Headers.Canonical", Kome.Headers.Canonical (H));
         end;

         --  A refusal does not change the record.
         Keep := Back;
         Decode (E (0 .. L - 2), Back, St);
         Check ("PUT truncated by one byte refused, record unchanged",
                St = Malformed and then Back = Keep);
         Decode (E & Byte'(0), Back, St);
         Check ("PUT oversized by one byte refused, record unchanged",
                St = Malformed and then Back = Keep);
         Decode (E (0 .. 127), Back, St);
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
            Bad (17) := 0;
            Decode (Bad, Back, St);
            Check ("PUT flen 0 refused, record unchanged",
                   St = Malformed and then Back = Keep);
            Bad (17) := 33;
            Decode (Bad, Back, St);
            Check ("PUT flen 33 refused, record unchanged",
                   St = Malformed and then Back = Keep);
            Bad := E;
            Bad (62 + FL) := 16#FF#;
            Bad (63 + FL) := 16#FE#;
            Decode (Bad, Back, St);
            Check ("PUT vlen disagreeing with length refused",
                   St = Malformed and then Back = Keep);
         end;

         --  Tampered signature and content.
         declare
            Bad : Byte_Array := E;
            R2  : Put_Record;
         begin
            Bad (L - 1) := Bad (L - 1) xor 1;
            Decode (Bad, R2, St);
            Check ("PUT tampered signature: decodes", St = OK);
            Check ("PUT tampered signature: not well-formed", not Well_Formed (Cid_A, R2));
            Decode_Verified (Cid_A, Bad, R2, St);
            Check ("PUT tampered signature: Decode_Verified refuses", St = Malformed);
            Bad := E;
            Bad (64 + FL + 100) := Bad (64 + FL + 100) xor 16#80#;   --  value byte 100
            Decode (Bad, R2, St);
            Check ("PUT tampered value byte: decodes to the changed value, not well-formed",
                   St = OK and then R2.C.Value (100) /= Big.C.Value (100)
                   and then not Well_Formed (Cid_A, R2));
            Bad := E;
            Bad (30 + FL + 3) := Bad (30 + FL + 3) xor 1;   --  author byte 3
            Decode (Bad, R2, St);
            Check ("PUT tampered author byte: not well-formed",
                   St = OK and then R2.C.Author /= Big.C.Author
                   and then not Well_Formed (Cid_A, R2));
            Decode_Verified (Cid_A, E, R2, St);
            Check ("PUT Decode_Verified accepts the genuine frame",
                   St = OK and then R2 = Big);
         end;
      end;

      --  Signed by someone other than the author.
      declare
         Forged : Put_Record := Big;
      begin
         Forged.C.Author := Other_PK;
         Sign (Cid_A, Forged, Other_SK);
         Forged.C.Author := Author_PK;
         Check ("PUT signed by a non-author key is not well-formed",
                not Well_Formed (Cid_A, Forged));
      end;

      --  Non-canonical padding.
      declare
         Pad : Put_Record := Make_Put (Cid_A, Ent_A, [1, 2], 5, 6, Author_PK, [7]);
      begin
         Sign (Cid_A, Pad, Author_SK);
         Check ("PUT canonical record is well-formed",
                Canonical (Pad) and then Well_Formed (Cid_A, Pad));
         Pad.C.Field (5) := 1;
         Check ("PUT nonzero field padding is not canonical / well-formed",
                not Canonical (Pad) and then not Well_Formed (Cid_A, Pad));
         Pad.C.Field (5) := 0;
         Pad.C.Value (9) := 1;
         Check ("PUT nonzero value padding is not canonical / well-formed",
                not Canonical (Pad) and then not Well_Formed (Cid_A, Pad));
      end;
   end;

   --  D12: vlen 40 960 is a valid value. Decode refuses 40 961, also when
   --  the length agrees (with a 1-byte field, Put_Frame_Max has space for
   --  it).
   declare
      V  : Put_Record := Make_Put (Cid_A, Ent_A, [16#66#], 1, 1, Author_PK, Fill (Value_Max, 9));
      R2 : Put_Record;
      K2 : Put_Record;
      St : Status;
   begin
      Sign (Cid_A, V, Author_SK);
      declare
         E   : constant Byte_Array := Encode (V);
         Big : Byte_Array := E (0 .. E'Last - Sig_Len) & Byte'(16#5A#) & V.Signature;
      begin
         Decode_Verified (Cid_A, E, R2, St);
         Check ("PUT vlen 40960 (1-byte field): length 41089, OK",
                E'Length = 128 + 1 + 40_960 and then E (63) = 16#A0# and then E (64) = 0
                and then St = OK and then R2 = V);
         Big (63) := 16#A0#;
         Big (64) := 16#01#;   --  vlen 40 961, and the length is 128 + 1 + 40 961
         K2 := R2;
         Check ("PUT vlen 40961: length agrees and fits Put_Frame_Max",
                Big'Length = 128 + 1 + 40_961 and then Big'Length <= Put_Frame_Max);
         Decode (Big, R2, St);
         Check ("PUT vlen 40961: Malformed, record unchanged",
                St = Malformed and then R2 = K2 and then not Is_Put_Frame (Big));
         Decode_Verified (Cid_A, Big, R2, St);
         Check ("PUT vlen 40961: Decode_Verified Malformed",
                St = Malformed and then R2 = K2);
      end;
   end;

   ---------------------------------------------------------------------------
   --  PUT, big-endian t: 0x010203040506.
   ---------------------------------------------------------------------------
   declare
      R : constant Put_Record :=
        Make_Put (Cid_A, Ent_A, [16#61#, 16#62#], 16#0102_0304_0506#, 16#0A0B_0C0D_0E0F#,
                  Author_PK, [16#AA#, 16#BB#, 16#CC#]);
      E : constant Byte_Array := Encode (R);
   begin
      Check ("PUT t, seq, vlen big-endian",
             E (20 .. 25) = [1, 2, 3, 4, 5, 6]
             and then E (26 .. 31) = [16#0A#, 16#0B#, 16#0C#, 16#0D#, 16#0E#, 16#0F#]
             and then E (64 .. 65) = [0, 3]
             and then E (66 .. 68) = [16#AA#, 16#BB#, 16#CC#]
             and then E'Length = 128 + 2 + 3);
   end;

   ---------------------------------------------------------------------------
   --  Make_Del (DESIGN.md §5 step 2) and the header Posts of the builders
   --  (both Posts execute here under -gnata).
   ---------------------------------------------------------------------------
   declare
      D    : Del_Record := Make_Del (Cid_A, Ent_A, 1234, Max_U48, Author_PK);
      Hand : constant Del_Record :=
        (C => (Ent => Ent_A, T => 1234, Seq => Max_U48, Author => Author_PK),
         Signature => [others => 0]);
      P    : constant Put_Record :=
        Make_Put (Cid_A, Ent_A, [16#61#, 16#62#], 7, 8, Author_PK, [1]);
      Back : Del_Record;
      St   : Status;
   begin
      Check ("Make_Del equals the hand-built DEL", D = Hand);
      Sign (Cid_A, D, Author_SK);
      Decode_Verified (Cid_A, Encode (D), Back, St);
      Check ("Make_Del then Sign: verified decode, same header, h = hash of content",
             St = OK and then Back = D and then To_Header (Cid_A, Back) = To_Header (Cid_A, D)
             and then To_Header (Cid_A, D).V.H = H_Of (Encode (D), Cid_A)
             and then To_Header (Cid_A, D).V.T = 1234 and then To_Header (Cid_A, D).V.Seq = Max_U48);
      Check ("Make_Put header: FH = BLAKE2b (field), V from the arguments",
             To_Header (Cid_A, P).FH = To_Key256 (Kome.Crypto.Blake2b_256 ([16#61#, 16#62#]))
             and then To_Header (Cid_A, P).V.T = 7 and then To_Header (Cid_A, P).V.Seq = 8
             and then To_Header (Cid_A, P).V.Author = To_Key256 (Author_PK)
             and then To_Header (Cid_A, P).V.H = H_Of (Encode (P), Cid_A));
   end;

   ---------------------------------------------------------------------------
   --  DEL
   ---------------------------------------------------------------------------
   declare
      D    : Del_Record := (C => (Ent => Ent_A, T => 1234, Seq => Max_U48,
                                  Author => Author_PK),
                            Signature => [others => 0]);
      Back : Del_Record;
      Keep : Del_Record;
      St   : Status;
   begin
      Sign (Cid_A, D, Author_SK);
      declare
         E    : constant Byte_Array := Encode (D);
         Want : constant Byte_Array :=
           [Byte'(3)] & Ent_A & BE48 (1234) & BE48 (Max_U48) & Author_PK & D.Signature;
         H    : constant Header := To_Header (Cid_A, D);
      begin
         Check ("DEL: length 125 and bytes equal the hand-built layout (tag 3, no ns)",
                E'Length = 125 and then E = Want);
         Decode (E, Back, St);
         Check ("DEL: decode OK and equal", St = OK and then Back = D);
         Check ("DEL: well-formed", Well_Formed (Cid_A, Back));
         Lemma_Decode_Encode (D);
         Lemma_Encode_Decode_Del (E);
         Check ("DEL header: V = (t, author, seq, h), FH 0, no issuer",
                H.K = K_Del and then H.Ent = To_Id128 (Ent_A)
                and then H.FH = Zero_Key
                and then H.V.T = 1234 and then H.V.Author = To_Key256 (Author_PK)
                and then H.V.Seq = Max_U48 and then H.V.H = H_Of (E, Cid_A)
                and then H.Issuer = Zero_Key);
         Lemma_Header_Canonical (Cid_A, D);
         Check ("DEL header: Kome.Headers.Canonical", Kome.Headers.Canonical (H));
         Keep := Back;
         Decode (E (0 .. 123), Back, St);
         Check ("DEL truncated refused, record unchanged",
                St = Malformed and then Back = Keep);
         Decode (E & Byte'(0), Back, St);
         Check ("DEL oversized refused, record unchanged",
                St = Malformed and then Back = Keep);
         declare
            Bad : Byte_Array := E;
         begin
            Bad (100) := Bad (100) xor 4;   --  signature byte 39 (sig is 61 .. 124)
            Decode (Bad, Back, St);
            Check ("DEL tampered signature: decodes, not well-formed",
                   St = OK and then Back.C = D.C and then Back.Signature /= D.Signature
                   and then not Well_Formed (Cid_A, Back));
            Keep := Back;
            Decode_Verified (Cid_A, Bad, Back, St);
            Check ("DEL tampered signature: Decode_Verified refuses, record unchanged",
                   St = Malformed and then Back = Keep);
            Bad := E;
            Bad (40) := Bad (40) xor 4;     --  author byte 11 (author is 29 .. 60)
            Decode (Bad, Back, St);
            Check ("DEL tampered author: decodes, not well-formed",
                   St = OK and then Back.C.Author /= D.C.Author
                   and then Back.Signature = D.Signature
                   and then not Well_Formed (Cid_A, Back));
            Keep := Back;
            Decode_Verified (Cid_A, Bad, Back, St);
            Check ("DEL tampered author: Decode_Verified refuses, record unchanged",
                   St = Malformed and then Back = Keep);
            Bad := E;
            Bad (0) := 2;   --  Tag_Grant on a DEL frame
            Decode (Bad, Back, St);
            Check ("DEL frame with tag 2 refused", St = Malformed and then Back = Keep);
         end;
         --  A DEL frame is not a PUT frame.
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
   --  S1: the collection context. The same record bytes under two cids
   --  (another salt, or another del_ttl) have two different h, and a frame
   --  signed under one cid does not verify under the other.
   ---------------------------------------------------------------------------
   declare
      P    : Put_Record := Make_Put (Cid_A, Ent_A, [16#61#], 9, 10, Author_PK, [5, 6]);
      D    : Del_Record := Make_Del (Cid_A, Ent_A, 11, 12, Author_PK);
      PB   : Put_Record;
      DB   : Del_Record;
      St   : Status;
   begin
      Sign (Cid_A, P, Author_SK);
      Sign (Cid_A, D, Author_SK);
      Check ("S1 PUT: one record, two cids, two h (and two headers)",
             Hash (Cid_A, P.C) /= Hash (Cid_B, P.C)
             and then To_Key256 (Hash (Cid_A, P.C)) = H_Of (Encode (P), Cid_A)
             and then To_Key256 (Hash (Cid_B, P.C)) = H_Of (Encode (P), Cid_B)
             and then To_Header (Cid_A, P).V.H /= To_Header (Cid_B, P).V.H);
      Check ("S1 PUT: h is not BLAKE2b-256 (tag ‖ content)",
             To_Key256 (Hash (Cid_A, P.C)) /= H_Plain (Encode (P)));
      Check ("S1 PUT: well-formed under its cid only (not another salt or del_ttl)",
             Well_Formed (Cid_A, P) and then not Well_Formed (Cid_B, P)
             and then not Well_Formed (Cid_T, P));
      PB := P;
      PB.C.T := 0;
      Decode_Verified (Cid_B, Encode (P), PB, St);
      Check ("S1 PUT: Decode_Verified under the other cid refuses, record unchanged",
             St = Malformed and then PB.C.T = 0);
      Decode_Verified (Cid_A, Encode (P), PB, St);
      Check ("S1 PUT: Decode_Verified under its cid accepts", St = OK and then PB = P);
      Check ("S1 DEL: one record, two cids, two h",
             Hash (Cid_A, D.C) /= Hash (Cid_B, D.C)
             and then To_Key256 (Hash (Cid_B, D.C)) = H_Of (Encode (D), Cid_B)
             and then To_Header (Cid_A, D).V.H /= To_Header (Cid_B, D).V.H);
      Check ("S1 DEL: well-formed under its cid only",
             Well_Formed (Cid_A, D) and then not Well_Formed (Cid_B, D)
             and then not Well_Formed (Cid_T, D));
      DB := D;
      DB.C.T := 0;
      Decode_Verified (Cid_B, Encode (D), DB, St);
      Check ("S1 DEL: Decode_Verified under the other cid refuses, record unchanged",
             St = Malformed and then DB.C.T = 0);
      --  Same ns, two cids (the 2^64 ns collision, simulated): a record
      --  signed under a cid other than Cid_A whose first 16 bytes are
      --  NS_A does not verify under Cid_A.
      declare
         Other_Cid : Hash256 := Cid_A;
         Q         : Put_Record;
      begin
         Other_Cid (31) := Other_Cid (31) xor 1;   --  same first 16 bytes (ns)
         Q := Make_Put (Other_Cid, Ent_A, [16#62#], 1, 2, Author_PK, []);
         Sign (Other_Cid, Q, Author_SK);
         Check ("S1: same ns, other cid: well-formed there, refused here",
                NS_Of (Other_Cid) = NS_A
                and then Well_Formed (Other_Cid, Q) and then not Well_Formed (Cid_A, Q));
      end;
   end;

   ---------------------------------------------------------------------------
   --  ROSTER
   ---------------------------------------------------------------------------
   declare
      Members_64 : constant Byte_Array := Members_Of (Members_Max, 77);
      Big  : Roster_Record :=
        Make_Roster (Cid_A, Root_PK, Founding_Cap, Cert_R, Box_A, Max_U48, Max_U48,
                     Members_64);
      Back : Roster_Record;
      Keep : Roster_Record;
      St   : Status;
   begin
      Sign (Cid_A, Big, Root_SK);
      declare
         E : constant Byte_Array := Encode (Big);
         L : constant Natural    := E'Length;
         H : constant Header     := To_Header (Cid_A, Big);
      begin
         Check ("ROSTER max: length 8916 (64 members)",
                L = 1 + 32 + 6 + 64 + 32 + 6 + 6 + 1 + 64 * 136 + 64
                and then L = Roster_Frame_Max and then L = Frame_Len (Big));
         Check ("ROSTER max: layout bytes at the SIMPLIFY.md §2 offsets",
                E (0) = Tag_Roster and then E (0) = 0
                and then E (1 .. 32) = Root_PK
                and then E (33 .. 38) = BE48 (Founding_Cap)
                and then E (39 .. 102) = Cert_R
                and then E (103 .. 134) = Box_A
                and then E (135 .. 140) = BE48 (Max_U48)
                and then E (141 .. 146) = BE48 (Max_U48)
                and then E (147) = 64
                and then E (148 .. 148 + 8704 - 1) = Members_64
                and then E (L - 64 .. L - 1) = Big.Signature);
         Decode (E, Back, St);
         Check ("ROSTER max: decode OK and equal", St = OK and then Back = Big);
         Check ("ROSTER max: well-formed (founder-signed, self-certified)",
                Well_Formed (Cid_A, Root_PK, Back));
         Decode_Verified (Cid_A, Root_PK, E, Back, St);
         Check ("ROSTER max: Decode_Verified OK", St = OK and then Back = Big);
         Lemma_Decode_Encode (Big);
         Lemma_Encode_Decode_Roster (E);
         Check ("ROSTER max: Encode (Decode (frame)) = frame", Encode (Back) = E);
         Lemma_Member_Bytes (Back.C, 64);
         Lemma_Member_Bytes (Back.C, 1);
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
         Check ("ROSTER header: V = (ceiling_t, signer, gen, h), issuer = signer",
                H.K = K_Roster
                and then H.Ent = Zero_Id and then H.FH = Zero_Key
                and then H.V.T = Max_U48 and then H.V.Author = To_Key256 (Root_PK)
                and then H.V.Author = Signer_Key (Big)
                and then H.V.Seq = Max_U48 and then H.V.H = H_Of (E, Cid_A)
                and then H.V.H /= H_Plain (E)
                and then H.Issuer = To_Key256 (Root_PK)
                and then Ceil_Of (H) = Max_U48);
         Lemma_Header_Canonical (Cid_A, Big);
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
            Bad (147) := 65;   --  n_members 65
            Decode (Bad, Back, St);
            Check ("ROSTER n_members 65 refused", St = Malformed and then Back = Keep);
            Bad := E;
            Bad (147) := 63;   --  n_members disagrees with the length
            Decode (Bad, Back, St);
            Check ("ROSTER n_members 63 with 64 members' bytes refused",
                   St = Malformed and then Back = Keep);
            Bad := E;
            Bad (L - 30) := Bad (L - 30) xor 2;
            Decode (Bad, Back, St);
            Check ("ROSTER tampered signature: not well-formed",
                   St = OK and then Back.C = Big.C
                   and then not Well_Formed (Cid_A, Root_PK, Back));
            Bad := E;
            Bad (106) := Bad (106) xor 2;   --  box_pk byte 3
            Decode (Bad, Back, St);
            Check ("ROSTER tampered box_pk: not well-formed",
                   St = OK and then Back.C.Box_PK /= Box_A
                   and then not Well_Formed (Cid_A, Root_PK, Back));
            Keep := Back;
            Bad := E;
            Bad (3000) := Bad (3000) xor 2;
            Decode_Verified (Cid_A, Root_PK, Bad, Back, St);
            Check ("ROSTER tampered member box: Decode_Verified refuses, unchanged",
                   St = Malformed and then Back = Keep);
         end;
         Check ("ROSTER: not well-formed under another cid or another founding key",
                not Well_Formed (Cid_B, Root_PK, Big)
                and then not Well_Formed (Cid_T, Root_PK, Big)
                and then not Well_Formed (Cid_A, Other_PK, Big));
      end;

      declare
         Wrong : Roster_Record := Big;
      begin
         Wrong.C.Signer := Other_PK;
         Sign (Cid_A, Wrong, Other_SK);
         Wrong.C.Signer := Root_PK;
         Check ("ROSTER signed by a key other than signer is not well-formed",
                not Well_Formed (Cid_A, Root_PK, Wrong));
         Wrong := Big;
         Wrong.C.N_Members := 63;   --  the bytes of member 64 become padding
         Check ("ROSTER nonzero member padding is not canonical",
                not Canonical (Wrong) and then not Well_Formed (Cid_A, Root_PK, Wrong));
      end;

      --  Empty roster: no members.
      declare
         Empty_R : Roster_Record :=
           Make_Roster (Cid_A, Root_PK, Founding_Cap, Cert_R, Box_A, 0, 0, []);
      begin
         Sign (Cid_A, Empty_R, Root_SK);
         declare
            E : constant Byte_Array := Encode (Empty_R);
         begin
            Decode (E, Back, St);
            Check ("ROSTER empty: length 212, round trip, well-formed",
                   E'Length = 212 and then E (147) = 0
                   and then St = OK and then Back = Empty_R
                   and then Well_Formed (Cid_A, Root_PK, Back));
            Lemma_Decode_Encode (Empty_R);
            Lemma_Encode_Decode_Roster (E);
         end;
      end;
   end;

   ---------------------------------------------------------------------------
   --  ROSTER signer admission (D1, S3).
   ---------------------------------------------------------------------------
   declare
      Mem  : constant Byte_Array := Members_Of (2, 33);
      Back : Roster_Record;
      Keep : Roster_Record;
      St   : Status;

      function R (Signer : Pubkey; Cap : U48; Cert : Sig; Ceil : U48;
                  Box_PK : Pubkey := Box_A;
                  Members : Byte_Array := Mem) return Roster_Record is
        (Make_Roster (Cid_A, Signer, Cap, Cert, Box_PK, 7, Ceil, Members));

      --  Sign with SK and run Decode_Verified on the frame.
      function Verdict (X : in out Roster_Record; SK : Kome.Crypto.Secret_Key) return Status is
         S : Status;
      begin
         Sign (Cid_A, X, SK);
         Keep := Back;
         Decode_Verified (Cid_A, Root_PK, Encode (X), Back, S);
         if S = Malformed and then Back /= Keep then
            Check ("ROSTER refusal leaves the record unchanged", False);
         end if;
         return S;
      end Verdict;

      X : Roster_Record;
   begin
      --  An outsider signs a roster that increases the ceiling to 2^48 - 1.
      X := R (Author_PK, 0, Zero_Sig, Max_U48);
      St := Verdict (X, Author_SK);
      Check ("ROSTER outsider-signed (zero cert), ceiling 2^48-1: Malformed",
             St = Malformed and then not Well_Formed (Cid_A, Root_PK, X)
             and then Kome.Crypto.Verify (X.Signature, Author_PK, Hash (Cid_A, X.C)));
      X := R (Author_PK, Max_U48, Make_Cert (Author_SK, Cid_A, Author_PK, Max_U48), Max_U48);
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
             St = OK and then Back = X and then Well_Formed (Cid_A, Root_PK, X));
      Check ("ROSTER by certified root: header author and issuer are the signer",
             To_Header (Cid_A, X).V.Author = To_Key256 (Other_PK)
             and then To_Header (Cid_A, X).Issuer = To_Key256 (Other_PK)
             and then To_Header (Cid_A, X).V.Author /= To_Key256 (Root_PK)
             and then Signer_Key (X) = To_Key256 (Other_PK));
      X := R (Other_PK, Cap_2, Cert_2, Cap_2);
      St := Verdict (X, Other_SK);
      Check ("ROSTER by certified root, ceiling_t = cert_cap: OK", St = OK);
      X := R (Other_PK, Cap_2, Cert_2, Cap_2 + 1);
      St := Verdict (X, Other_SK);
      Check ("ROSTER by certified root, ceiling_t > cert_cap: Malformed",
             St = Malformed and then not Well_Formed (Cid_A, Root_PK, X));
      X := R (Other_PK, Cap_2 + 5000, Cert_2, Cap_2 + 1);
      St := Verdict (X, Other_SK);
      Check ("ROSTER by certified root claiming a larger cap than certified: Malformed",
             St = Malformed);
      --  H7: gen is bounded by ceiling_t, so a certified root's gen is
      --  bounded by its cap. The helper R uses gen 7.
      X := R (Other_PK, Cap_2, Cert_2, 7);
      St := Verdict (X, Other_SK);
      Check ("ROSTER with gen = ceiling_t: OK", St = OK and then Well_Formed (Cid_A, Root_PK, X));
      X := R (Other_PK, Cap_2, Cert_2, 6);
      St := Verdict (X, Other_SK);
      Check ("ROSTER with gen > ceiling_t (H7): Malformed",
             St = Malformed and then not Well_Formed (Cid_A, Root_PK, X)
             and then not Kome.Headers.Canonical (To_Header (Cid_A, X)));
      X := R (Other_PK, Cap_2, Make_Cert (Root_SK, Cid_B, Other_PK, Cap_2), 6000);
      St := Verdict (X, Other_SK);
      Check ("ROSTER with a certificate made for another salt: Malformed", St = Malformed);
      X := R (Other_PK, Cap_2, Make_Cert (Root_SK, Cid_T, Other_PK, Cap_2), 6000);
      St := Verdict (X, Other_SK);
      Check ("ROSTER with a certificate made for another del_ttl: Malformed", St = Malformed);

      --  The founding key carries its own certificate (S3).
      X := R (Root_PK, Founding_Cap, Cert_R, Max_U48);
      St := Verdict (X, Root_SK);
      Check ("ROSTER by founding key, self-certificate, any ceiling: OK", St = OK);
      X := R (Root_PK, 0, Zero_Sig, 6000);
      St := Verdict (X, Root_SK);
      Check ("ROSTER by founding key with a zero block: Malformed (no exception)",
             St = Malformed);
      X := R (Root_PK, Founding_Cap, Cert_2, 6000);
      St := Verdict (X, Root_SK);
      Check ("ROSTER by founding key with another signer's certificate: Malformed",
             St = Malformed);
      declare
         Low_R : constant Sig := Make_Cert (Root_SK, Cid_A, Root_PK, 5000);
      begin
         X := R (Root_PK, 5000, Low_R, 5000);
         St := Verdict (X, Root_SK);
         Check ("ROSTER by founding key under a self-certificate of cap 5000: OK at 5000",
                St = OK);
         X := R (Root_PK, 5000, Low_R, 5001);
         St := Verdict (X, Root_SK);
         Check ("ROSTER by founding key above its own certified cap: Malformed (no branch)",
                St = Malformed);
      end;

      --  X25519 keys (E5).
      declare
         type Key_List is array (Positive range <>) of Pubkey;
         Bad_Keys : constant Key_List := [P_Enc, Order_8, U_One, U_Zero];
         Names    : constant array (1 .. 4) of String (1 .. 7) :=
           ["p      ", "order 8", "u = 1  ", "u = 0  "];
      begin
         for K in Bad_Keys'Range loop
            X := R (Root_PK, Founding_Cap, Cert_R, 6000, Box_PK => Bad_Keys (K));
            St := Verdict (X, Root_SK);
            Check ("ROSTER box_pk = " & Names (K) & ": Malformed",
                   St = Malformed and then not DH_Keys_OK (X.C)
                   and then Kome.Crypto.Verify (X.Signature, Root_PK, Hash (Cid_A, X.C)));
            declare
               M : Byte_Array := Mem;
            begin
               M (Member_Len + Pubkey_Len .. Member_Len + 2 * Pubkey_Len - 1) := Bad_Keys (K);
               X := R (Root_PK, Founding_Cap, Cert_R, 6000, Members => M);
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
        Make_Revoke (Cid_A, Root_PK, Founding_Cap, Cert_R, Author_PK, 777);
      Back : Revoke_Record;
      Keep : Revoke_Record;
      St   : Status;
   begin
      Sign (Cid_A, X, Root_SK);
      declare
         E    : constant Byte_Array := Encode (X);
         Want : constant Byte_Array :=
           [Byte'(1)] & Root_PK & BE48 (Founding_Cap) & Cert_R & Author_PK
           & BE48 (777) & X.Signature;
         H    : constant Header := To_Header (Cid_A, X);
      begin
         Check ("REVOKE: length 205 and bytes equal the hand-built layout",
                E'Length = 205 and then E = Want);
         Decode (E, Back, St);
         Check ("REVOKE: decode OK and equal", St = OK and then Back = X);
         Check ("REVOKE: well-formed", Well_Formed (Cid_A, Root_PK, Back));
         Lemma_Decode_Encode (X);
         Lemma_Encode_Decode_Revoke (E);
         Check ("REVOKE header: V = (from_t, sign_pk, 0, h), issuer = signer",
                H.K = K_Revoke
                and then H.Ent = Zero_Id and then H.FH = Zero_Key
                and then H.V.T = 777 and then H.V.Author = To_Key256 (Author_PK)
                and then H.V.Seq = 0 and then H.V.H = H_Of (E, Cid_A)
                and then H.Issuer = To_Key256 (Root_PK)
                and then Signer_Key (X) = To_Key256 (Root_PK));
         Lemma_Header_Canonical (Cid_A, X);
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
            Bad (180) := Bad (180) xor 1;   --  signature byte 39 (sig is 141 .. 204)
            Decode_Verified (Cid_A, Root_PK, Bad, Back, St);
            Check ("REVOKE tampered signature: Decode_Verified refuses, unchanged",
                   St = Malformed and then Back = Keep);
            Bad := E;
            Bad (138) := Bad (138) xor 1;   --  from_t (135 .. 140)
            Decode (Bad, Back, St);
            Check ("REVOKE tampered from_t: not well-formed",
                   St = OK and then Back.C.From_T /= 777
                   and then not Well_Formed (Cid_A, Root_PK, Back));
         end;
         Check ("REVOKE: not well-formed under another cid",
                not Well_Formed (Cid_B, Root_PK, X) and then not Well_Formed (Cid_T, Root_PK, X));
      end;

      --  Signer admission (D1, D2, S3).
      declare
         function V (Y : in out Revoke_Record; SK : Kome.Crypto.Secret_Key) return Status is
            S : Status;
         begin
            Sign (Cid_A, Y, SK);
            Keep := Back;
            Decode_Verified (Cid_A, Root_PK, Encode (Y), Back, S);
            if S = Malformed and then Back /= Keep then
               Check ("REVOKE refusal leaves the record unchanged", False);
            end if;
            return S;
         end V;
         Y : Revoke_Record;
      begin
         Y := Make_Revoke (Cid_A, Author_PK, 0, Zero_Sig, Other_PK, 0);
         St := V (Y, Author_SK);
         Check ("REVOKE outsider-signed (revoking a root): Malformed",
                St = Malformed and then not Well_Formed (Cid_A, Root_PK, Y)
                and then Kome.Crypto.Verify (Y.Signature, Author_PK, Hash (Cid_A, Y.C)));
         Y := Make_Revoke (Cid_A, Other_PK, Cap_2, Cert_2, Author_PK, 9);
         St := V (Y, Other_SK);
         Check ("REVOKE by certified root: OK, signer key, subject in header",
                St = OK and then Back = Y and then Signer_Key (Y) = To_Key256 (Other_PK)
                and then To_Header (Cid_A, Y).V.Author = To_Key256 (Author_PK)
                and then To_Header (Cid_A, Y).Issuer = To_Key256 (Other_PK));
         Y := Make_Revoke (Cid_A, Other_PK, Cap_2,
                           Make_Cert (Root_SK, Cid_B, Other_PK, Cap_2), Author_PK, 9);
         St := V (Y, Other_SK);
         Check ("REVOKE with a certificate made for another cid: Malformed", St = Malformed);
         Y := Make_Revoke (Cid_A, Root_PK, 0, Zero_Sig, Author_PK, 9);
         St := V (Y, Root_SK);
         Check ("REVOKE by founding key with a zero cert block: Malformed", St = Malformed);
         Y := Make_Revoke (Cid_A, Root_PK, Founding_Cap, Cert_R, Root_PK, 0);
         St := V (Y, Root_SK);
         Check ("REVOKE of root_pk (founding-signed): Malformed",
                St = Malformed and then not Well_Formed (Cid_A, Root_PK, Y));
         Y := Make_Revoke (Cid_A, Other_PK, Cap_2, Cert_2, Root_PK, 0);
         St := V (Y, Other_SK);
         Check ("REVOKE of root_pk (by a certified root): Malformed", St = Malformed);
         Y := Make_Revoke (Cid_A, Root_PK, Founding_Cap, Cert_R, Other_PK, 0);
         St := V (Y, Root_SK);
         Check ("REVOKE of a certified root by the founding key: OK", St = OK);
         Y := Make_Revoke (Cid_A, Other_PK, Cap_2, Cert_2, Author_PK, 9);
         Sign (Cid_A, Y, Other_SK);
         Y.C.Signer := Root_PK;
         Check ("REVOKE whose signer field is not the signing key is not well-formed",
                not Well_Formed (Cid_A, Root_PK, Y));
      end;
   end;

   ---------------------------------------------------------------------------
   --  GRANT
   ---------------------------------------------------------------------------
   declare
      G    : Grant_Record := Make_Grant (Cid_A, Root_PK, Founding_Cap, Cert_R, Author_PK);
      Back : Grant_Record;
      Keep : Grant_Record;
      St   : Status;
   begin
      Sign (Cid_A, G, Root_SK);
      declare
         E    : constant Byte_Array := Encode (G);
         Want : constant Byte_Array :=
           [Byte'(2)] & Root_PK & BE48 (Founding_Cap) & Cert_R & Author_PK & G.Signature;
         H    : constant Header := To_Header (Cid_A, G);
      begin
         Check ("GRANT: length 199 and bytes equal the hand-built layout",
                E'Length = 199 and then E = Want and then Is_Grant_Frame (E)
                and then Kind_Of (E) = K_Grant);
         Decode (E, Back, St);
         Check ("GRANT: decode OK and equal", St = OK and then Back = G);
         Check ("GRANT: well-formed", Well_Formed (Cid_A, Root_PK, Back));
         Decode_Verified (Cid_A, Root_PK, E, Back, St);
         Check ("GRANT: Decode_Verified OK", St = OK and then Back = G);
         Lemma_Decode_Encode (G);
         Lemma_Encode_Decode_Grant (E);
         Check ("GRANT: Encode (Decode (frame)) = frame", Encode (Back) = E);
         Check ("GRANT header: V = (cert_cap, subject, 0, h), issuer = signer;"
                & " founding cap 2^48-1",
                H.K = K_Grant
                and then H.Ent = Zero_Id and then H.FH = Zero_Key
                and then H.V.T = U48'Last and then Cap_Of (H) = U48'Last
                and then H.V.Author = To_Key256 (Author_PK)
                and then H.V.Seq = 0 and then H.V.H = H_Of (E, Cid_A)
                and then H.Issuer = To_Key256 (Root_PK)
                and then Signer_Key (G) = To_Key256 (Root_PK));
         Lemma_Header_Canonical (Cid_A, G);
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
            Bad (116) := Bad (116) xor 1;   --  subject byte 13 (subject is 103 .. 134)
            Decode (Bad, Back, St);
            Check ("GRANT tampered subject: decodes, not well-formed",
                   St = OK and then Back.C.Subject /= Author_PK
                   and then not Well_Formed (Cid_A, Root_PK, Back));
            Keep := Back;
            Bad := E;
            Bad (170) := Bad (170) xor 1;   --  signature
            Decode_Verified (Cid_A, Root_PK, Bad, Back, St);
            Check ("GRANT tampered signature: Decode_Verified refuses, unchanged",
                   St = Malformed and then Back = Keep);
            Bad := E;
            Bad (35) := Bad (35) xor 1;     --  cert_cap byte 2 (cert_cap is 33 .. 38)
            Decode (Bad, Back, St);
            Check ("GRANT tampered cert_cap: not well-formed",
                   St = OK and then Back.C.Cert_Cap /= Founding_Cap
                   and then not Well_Formed (Cid_A, Root_PK, Back));
         end;
      end;

      declare
         function V (Y : in out Grant_Record; SK : Kome.Crypto.Secret_Key) return Status is
            S : Status;
         begin
            Sign (Cid_A, Y, SK);
            Keep := Back;
            Decode_Verified (Cid_A, Root_PK, Encode (Y), Back, S);
            if S = Malformed and then Back /= Keep then
               Check ("GRANT refusal leaves the record unchanged", False);
            end if;
            return S;
         end V;
         Y : Grant_Record;
      begin
         Y := Make_Grant (Cid_A, Author_PK, 0, Zero_Sig, Author_PK);
         St := V (Y, Author_SK);
         Check ("GRANT outsider-signed (granting itself): Malformed",
                St = Malformed and then not Well_Formed (Cid_A, Root_PK, Y)
                and then Kome.Crypto.Verify (Y.Signature, Author_PK, Hash (Cid_A, Y.C)));
         Y := Make_Grant (Cid_A, Other_PK, Cap_2, Cert_2, Author_PK);
         St := V (Y, Other_SK);
         Check ("GRANT by certified root: OK, issuer is the signer, V.T = cert_cap (wcap)",
                St = OK and then Back = Y
                and then To_Header (Cid_A, Y).Issuer = To_Key256 (Other_PK)
                and then To_Header (Cid_A, Y).V.Author = To_Key256 (Author_PK)
                and then To_Header (Cid_A, Y).V.T = Cap_2
                and then Cap_Of (To_Header (Cid_A, Y)) = Cap_2);
         Y := Make_Grant (Cid_A, Other_PK, Cap_2,
                          Make_Cert (Root_SK, Cid_B, Other_PK, Cap_2), Author_PK);
         St := V (Y, Other_SK);
         Check ("GRANT with a certificate made for another cid: Malformed", St = Malformed);
         Y := Make_Grant (Cid_A, Root_PK, Founding_Cap, Cert_2, Author_PK);
         St := V (Y, Root_SK);
         Check ("GRANT by founding key with another signer's certificate: Malformed",
                St = Malformed);
         Y := Make_Grant (Cid_A, Root_PK, 0, Zero_Sig, Author_PK);
         St := V (Y, Root_SK);
         Check ("GRANT by founding key with a zero block: Malformed", St = Malformed);

         --  H13 and A27: the 8 small-order points, the key of the all-zero
         --  seed and a non-canonical encoding (y = p, which no small-order
         --  test names) are refused as a GRANT subject (by bytes: the
         --  founding key's signature is genuine), as the founding key (the
         --  verifier's Root_PK; Cert_OK), and as a signer (Cert_OK, with a
         --  genuine certificate from the founding key). Make_Grant and
         --  Make_Cert refuse them by Pre.
         declare
            type Key_List is array (Positive range <>) of Pubkey;
            Bad : constant Key_List :=
              [Pubkey (From_Hex ("0100000000000000000000000000000000000000000000000000000000000000")),
               Pubkey (From_Hex ("ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f")),
               Pubkey (From_Hex ("0000000000000000000000000000000000000000000000000000000000000000")),
               Pubkey (From_Hex ("0000000000000000000000000000000000000000000000000000000000000080")),
               Pubkey (From_Hex ("26e8958fc2b227b045c3f489f2ef98f0d5dfac05d3c63339b13802886d53fc05")),
               Pubkey (From_Hex ("26e8958fc2b227b045c3f489f2ef98f0d5dfac05d3c63339b13802886d53fc85")),
               Pubkey (From_Hex ("c7176a703d4dd84fba3c0b760d10670f2a2053fa2c39ccc64ec7fd7792ac037a")),
               Pubkey (From_Hex ("c7176a703d4dd84fba3c0b760d10670f2a2053fa2c39ccc64ec7fd7792ac03fa")),
               Kome.Crypto.Zero_Seed_Public,
               Pubkey (From_Hex ("edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f"))];
            Ok_Subject, Ok_Root, Ok_Signer, Ok_Pre, Ok_Roster : Boolean := True;
            Forge : constant Sig := [0 => 1, others => 0];
            Cert_Sink : Sig := Zero_Sig with Volatile;
         begin
            Check ("Sign_Key_OK: the real keys are usable, the bad list is not",
                   Sign_Key_OK (Root_PK) and then Sign_Key_OK (Other_PK)
                   and then Sign_Key_OK (Author_PK)
                   and then (for all K of Bad => not Sign_Key_OK (K))
                   and then Kome.Crypto.Derive_Public ([others => 0]) = Bad (9)
                   and then not Kome.Crypto.Is_Canonical_Point (Bad (10))
                   and then not Kome.Crypto.Is_Small_Order_Point (Bad (10))
                   and then not Kome.Crypto.Is_Zero_Seed_Public (Bad (10)));
            for K of Bad loop
               --  Subject: a genuine founding-signed GRANT.
               Y := Make_Grant (Cid_A, Root_PK, Founding_Cap, Cert_R, Author_PK);
               Y.C.Subject := K;
               St := V (Y, Root_SK);
               if St /= Malformed or else Well_Formed (Cid_A, Root_PK, Y)
                 or else not Kome.Crypto.Verify (Y.Signature, Root_PK, Hash (Cid_A, Y.C))
               then
                  Ok_Subject := False;
               end if;
               --  Founding key = signer = K. No signature is possible, but
               --  Well_Formed refuses by bytes before the signature.
               Y := Make_Grant (Cid_A, Root_PK, Founding_Cap, Cert_R, Author_PK);
               Y.C.Signer := K;
               Y.Signature := Forge;
               if Well_Formed (Cid_A, K, Y)
                 or else Cert_OK (Cid_A, K, K, Founding_Cap, Forge)
                 or else Sign_Key_OK (K)
               then
                  Ok_Root := False;
               end if;
               Decode_Verified (Cid_A, K, Encode (Y), Back, St);
               if St /= Malformed then
                  Ok_Root := False;
               end if;
               --  Signer: a genuine certificate from the founding key.
               declare
                  Cert : constant Sig :=
                    Kome.Crypto.Sign (Root_SK, Cert_Hash (Cid_A, K, Cap_2));
               begin
                  Y := Make_Grant (Cid_A, Other_PK, Cap_2, Cert_2, Author_PK);
                  Y.C.Signer := K;
                  Y.C.Cert_Sig := Cert;
                  Y.Signature := Forge;
                  if Cert_OK (Cid_A, Root_PK, K, Cap_2, Cert)
                    or else Well_Formed (Cid_A, Root_PK, Y)
                    or else not Kome.Crypto.Verify (Cert, Root_PK, Cert_Hash (Cid_A, K, Cap_2))
                  then
                     Ok_Signer := False;
                  end if;
                  Decode_Verified (Cid_A, Root_PK, Encode (Y), Back, St);
                  if St /= Malformed then
                     Ok_Signer := False;
                  end if;
               end;
               --  ROSTER and REVOKE with founding key = signer = K.
               declare
                  RR : Roster_Record :=
                    Make_Roster (Cid_A, Root_PK, Founding_Cap, Cert_R, Box_A, 0, 0, Fill (0, 0));
                  RV : Revoke_Record :=
                    Make_Revoke (Cid_A, Root_PK, Founding_Cap, Cert_R, Author_PK, 0);
               begin
                  RR.C.Signer := K;
                  RV.C.Signer := K;
                  if Well_Formed (Cid_A, K, RR) or else Well_Formed (Cid_A, K, RV) then
                     Ok_Roster := False;
                  end if;
               end;
               --  The Pres of Make_Grant (subject) and Make_Cert (signer).
               declare
                  Hit : Natural := 0;
               begin
                  --  Only in the check mode (Contract_Mode).
                  if Contracts_On then
                     begin
                        Y := Make_Grant (Cid_A, Root_PK, Founding_Cap, Cert_R, K);
                     exception
                        when Ada.Assertions.Assertion_Error => Hit := Hit + 1;
                     end;
                     begin
                        Cert_Sink := Make_Cert (Root_SK, Cid_A, K, Cap_2);
                     exception
                        when Ada.Assertions.Assertion_Error => Hit := Hit + 1;
                     end;
                     if Hit /= 2 then
                        Ok_Pre := False;
                     end if;
                  end if;
               end;
            end loop;
            Check ("GRANT to a small-order, zero-seed or non-canonical subject: Malformed (10 keys)",
                   Ok_Subject);
            Check ("small-order, zero-seed or non-canonical founding key: not well-formed (GRANT)",
                   Ok_Root);
            Check ("small-order, zero-seed or non-canonical signer with a genuine certificate:"
                   & " not well-formed",
                   Ok_Signer);
            Check ("small-order, zero-seed or non-canonical founding key: not well-formed"
                   & " (ROSTER, REVOKE)",
                   Ok_Roster);
            if Contracts_On then
               Check ("Make_Grant and Make_Cert refuse a small-order, zero-seed or non-canonical"
                      & " key (Pre)",
                      Ok_Pre);
            else
               Skip ("Make_Grant and Make_Cert refuse a small-order, zero-seed or non-canonical"
                     & " key (Pre)");
            end if;
            --  The same 10 keys as a REVOKE subject (sign_pk) and as a
            --  ROSTER member sign_pk: refused by bytes, under a genuine
            --  signature of the founding key. Make_Revoke refuses them as
            --  the subject by Pre.
            declare
               Ok_Rv, Ok_Mem, Ok_Rv_Pre : Boolean := True;
               Base_Mem : constant Byte_Array := Members_Of (2, 61);
               RV   : Revoke_Record;
               RVB  : Revoke_Record;
               RM   : Roster_Record;
               RMB  : Roster_Record;
               S2   : Status;
               Rv_Sink : Revoke_Record with Volatile;
            begin
               RV := Make_Revoke (Cid_A, Root_PK, Founding_Cap, Cert_R, Author_PK, 0);
               Sign (Cid_A, RV, Root_SK);
               Decode_Verified (Cid_A, Root_PK, Encode (RV), RVB, S2);
               Check ("REVOKE with a usable subject: OK",
                      S2 = OK and then Well_Formed (Cid_A, Root_PK, RV));
               RM := Make_Roster (Cid_A, Root_PK, Founding_Cap, Cert_R, Box_A, 0, 0, Base_Mem);
               Sign (Cid_A, RM, Root_SK);
               Decode_Verified (Cid_A, Root_PK, Encode (RM), RMB, S2);
               Lemma_Member_Keys_OK_Def (RM.C);
               Lemma_Member_Keys_OK (RM.C, 2);
               Check ("ROSTER with usable member sign_pks: OK, Member_Keys_OK",
                      S2 = OK and then Well_Formed (Cid_A, Root_PK, RM)
                      and then Member_Keys_OK (RM.C));
               for K of Bad loop
                  RV := Make_Revoke (Cid_A, Root_PK, Founding_Cap, Cert_R, Author_PK, 0);
                  RV.C.Sign_PK := K;
                  Sign (Cid_A, RV, Root_SK);
                  RVB := Make_Revoke (Cid_A, Root_PK, Founding_Cap, Cert_R, Other_PK, 0);
                  Decode_Verified (Cid_A, Root_PK, Encode (RV), RVB, S2);
                  if S2 /= Malformed or else Well_Formed (Cid_A, Root_PK, RV)
                    or else RVB.C.Sign_PK /= Other_PK
                    or else not Kome.Crypto.Verify (RV.Signature, Root_PK, Hash (Cid_A, RV.C))
                  then
                     Ok_Rv := False;
                  end if;
                  if Contracts_On then
                     begin
                        Rv_Sink := Make_Revoke (Cid_A, Root_PK, Founding_Cap, Cert_R, K, 0);
                        Ok_Rv_Pre := False;
                     exception
                        when Ada.Assertions.Assertion_Error => null;
                     end;
                  end if;
                  --  Member 2's sign_pk is K; member 1 stays usable.
                  declare
                     Mem : Byte_Array := Base_Mem;
                  begin
                     for I in 0 .. Pubkey_Len - 1 loop
                        Mem (Mem'First + Member_Len + I) := K (I);
                     end loop;
                     RM := Make_Roster (Cid_A, Root_PK, Founding_Cap, Cert_R, Box_A, 0, 0, Mem);
                  end;
                  Sign (Cid_A, RM, Root_SK);
                  Decode_Verified (Cid_A, Root_PK, Encode (RM), RMB, S2);
                  if S2 /= Malformed or else Well_Formed (Cid_A, Root_PK, RM)
                    or else Member_Keys_OK (RM.C)
                    or else Member_Sign_PK (RM.C, 2) /= K
                    or else not Sign_Key_OK (Member_Sign_PK (RM.C, 1))
                    or else not DH_Keys_OK (RM.C)
                    or else not Kome.Crypto.Verify (RM.Signature, Root_PK, Hash (Cid_A, RM.C))
                  then
                     Ok_Mem := False;
                  end if;
               end loop;
               Check ("REVOKE of a small-order, zero-seed or non-canonical subject: Malformed"
                      & " (10 keys), record unchanged",
                      Ok_Rv);
               if Contracts_On then
                  Check ("Make_Revoke refuses a small-order, zero-seed or non-canonical subject"
                         & " (Pre)",
                         Ok_Rv_Pre);
               else
                  Skip ("Make_Revoke refuses a small-order, zero-seed or non-canonical subject"
                        & " (Pre)");
               end if;
               Check ("ROSTER with a small-order, zero-seed or non-canonical member sign_pk:"
                      & " Malformed (10 keys)",
                      Ok_Mem);
            end;
            --  A27: box_pk = X25519_Public (0^32) is a good DH key by E5,
            --  but Well_Formed refuses it; Box_A is accepted.
            declare
               RR : Roster_Record :=
                 Make_Roster (Cid_A, Root_PK, Founding_Cap, Cert_R, Box_A, 0, 0, Fill (0, 0));
               RB : Roster_Record;
               S2 : Status;
            begin
               Sign (Cid_A, RR, Root_SK);
               Decode_Verified (Cid_A, Root_PK, Encode (RR), RB, S2);
               Check ("ROSTER with box_pk = Box_A: OK",
                      S2 = OK and then Well_Formed (Cid_A, Root_PK, RR));
               RR.C.Box_PK := Kome.Crypto.Zero_Secret_DH_Public;
               Sign (Cid_A, RR, Root_SK);
               Decode_Verified (Cid_A, Root_PK, Encode (RR), RB, S2);
               Check ("ROSTER with box_pk = X25519_Public (0^32): Malformed",
                      S2 = Malformed and then not Well_Formed (Cid_A, Root_PK, RR)
                      and then DH_Keys_OK (RR.C)
                      and then Kome.Crypto.X25519_Public ([others => 0])
                               = Kome.Crypto.Zero_Secret_DH_Public);
            end;
         end;
      end;
   end;

   ---------------------------------------------------------------------------
   --  Frame accessors: Is_Auth_Frame, Roster_Lists_DH.
   ---------------------------------------------------------------------------
   declare
      Mem : constant Byte_Array := Members_Of (3, 61);
      Ro  : Roster_Record :=
        Make_Roster (Cid_A, Root_PK, Founding_Cap, Cert_R, Box_A, 1, 100, Mem);
      Rv  : Revoke_Record :=
        Make_Revoke (Cid_A, Root_PK, Founding_Cap, Cert_R, Other_PK, 0);
      Gr  : Grant_Record :=
        Make_Grant (Cid_A, Other_PK, Cap_2, Cert_2, Author_PK);
      Dl  : constant Del_Record := Make_Del (Cid_A, Ent_A, 1, 1, Author_PK);
   begin
      Sign (Cid_A, Ro, Root_SK);
      Sign (Cid_A, Rv, Root_SK);
      Sign (Cid_A, Gr, Other_SK);
      declare
         ER : constant Byte_Array := Encode (Ro);
         EV : constant Byte_Array := Encode (Rv);
         EG : constant Byte_Array := Encode (Gr);
         ED : constant Byte_Array := Encode (Dl);
         Shifted : Byte_Array (500 .. 500 + ER'Length - 1);
      begin
         Shifted := ER;
         Check ("Is_Auth_Frame: ROSTER, REVOKE, GRANT; not DEL",
                Is_Auth_Frame (ER) and then Is_Auth_Frame (EV) and then Is_Auth_Frame (EG)
                and then Is_Auth_Frame (Shifted) and then not Is_Auth_Frame (ED));
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
              (Make_Roster (Cid_A, Root_PK, Founding_Cap, Cert_R, Box_A, 1, 100, []));
         begin
            Lemma_Roster_Lists_DH (E0, Box_A);
            Check ("Roster_Lists_DH: a roster with no members lists nothing",
                   not Roster_Lists_DH (E0, Box_A)
                   and then not Roster_Lists_DH (E0, Mem (Pubkey_Len .. 2 * Pubkey_Len - 1)));
         end;
      end;
   end;

   ---------------------------------------------------------------------------
   --  Known answers (vectors/records.txt): layout, h, the cid and the
   --  certificate hash, independent of this package.
   ---------------------------------------------------------------------------
   declare
      Path  : constant String := Find ("vectors/records.txt");
      F     : File_Type;
      Line  : String (1 .. 32_768);
      Last  : Natural;
      N     : Natural := 0;
      Ent_V : constant Ent_Id := Ent_Id (Fill (16, 2));
      Au_V  : constant Pubkey := Pubkey (Fill (32, 4));
      Rt_V  : constant Pubkey := Pubkey (Fill (32, 8));
      Sa_V  : constant Salt   := Salt (Fill (16, 9));
      TTL_V : constant U48    := 30 * Day;
      Cid_V : constant Hash256 := Cid_Of (Rt_V, Sa_V, TTL_V);
      Sg_V  : constant Pubkey := Pubkey (Fill (32, 10));

      procedure One (Name : String; Content, H : Byte_Array) is
         Ok : Boolean := False;
      begin
         if Name = "put1" or else Name = "put2" then
            declare
               R : constant Put_Record :=
                 (if Name = "put1"
                  then Make_Put (Cid_V, Ent_V, Fill (5, 3), 16#0102_0304_0506#, 7,
                                 Au_V, Fill (10, 5))
                  else Make_Put (Cid_V, Ent_V, Fill (32, 6), 0, Max_U48, Au_V, []));
            begin
               Ok := Content_Bytes (R.C) = Content and then Hash (Cid_V, R.C) = H
                     and then Encode (R) = Content & Zero_Sig;
            end;
         elsif Name = "del1" then
            declare
               R : constant Del_Record := Make_Del (Cid_V, Ent_V, 1234, Max_U48, Au_V);
            begin
               Ok := Content_Bytes (R.C) = Content and then Hash (Cid_V, R.C) = H
                     and then Encode (R) = Content & Zero_Sig;
            end;
         elsif Name = "roster1" or else Name = "roster2" or else Name = "roster3" then
            declare
               R : constant Roster_Record :=
                 (if Name = "roster1"
                  then Make_Roster (Cid_V, Sg_V, 5000, Sig (Fill (64, 11)),
                                    Pubkey (Fill (32, 15)), 3, 1000, Fill (272, 13))
                  elsif Name = "roster2"
                  then Make_Roster (Cid_V, Rt_V, Max_U48, Sig (Fill (64, 20)),
                                    Pubkey (Fill (32, 16)), 0, 0, [])
                  else Make_Roster (Cid_V, Rt_V, Max_U48, Sig (Fill (64, 22)),
                                    Pubkey (Fill (32, 17)), Max_U48, Max_U48,
                                    Fill (136 * 64, 19)));
            begin
               Ok := Content_Bytes (R.C) = Content and then Hash (Cid_V, R.C) = H
                     and then Encode (R) = Content & Zero_Sig;
               if Ok then
                  Lemma_Encode_Decode_Roster (Encode (R));
                  Ok := Parse_Roster (Encode (R)) = R;
               end if;
            end;
         elsif Name = "revoke1" then
            declare
               R : constant Revoke_Record :=
                 Make_Revoke (Cid_V, Sg_V, 5000, Sig (Fill (64, 11)), Pubkey (Fill (32, 14)), 777);
            begin
               Ok := Content_Bytes (R.C) = Content and then Hash (Cid_V, R.C) = H
                     and then Encode (R) = Content & Zero_Sig;
            end;
         elsif Name = "grant1" then
            declare
               R : constant Grant_Record :=
                 Make_Grant (Cid_V, Sg_V, Max_U48, Sig (Fill (64, 20)), Pubkey (Fill (32, 21)));
            begin
               Ok := Content_Bytes (R.C) = Content and then Hash (Cid_V, R.C) = H
                     and then Encode (R) = Content & Zero_Sig;
            end;
         elsif Name = "cid1" then
            Ok := Content = Cid_Input (Rt_V, Sa_V, TTL_V) and then Cid_Of (Rt_V, Sa_V, TTL_V) = H
                  and then NS_Of (Cid_V) = H (0 .. NS_Len - 1);
         elsif Name = "cert1" then
            Ok := Cert_Input (Cid_V, Sg_V, 16#0000_0102_0304#) = Content
                  and then Cert_Hash (Cid_V, Sg_V, 16#0000_0102_0304#) = H;
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
         Check ("vectors: all ten present", N = 10);
      end if;
   end;

   if Failed then
      Set_Exit_Status (Failure);
   end if;
end Test_Records;
