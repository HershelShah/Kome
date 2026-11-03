--  Kome.Records: canonical record encoding, hashing, signing and
--  well-formedness (DESIGN.md §2 "Records"; T13 "every emitted record
--  satisfies the §2 layout"). This is the wire and crypto boundary: records
--  here hold bytes, and To_Header turns them into the lattice's word
--  records (Kome.Headers.Header, Id128 / Key256 via Kome.Keys).
--
--  The layout IS DESIGN.md §2 (the five layouts and the offset table).
--  All integers are big-endian; labels are ASCII with no terminator:
--
--    tag 0  ROSTER  ns[16] root_pk[32] salt[16] SIGNER box_pk[32]
--                   gen:u48 ceiling_t:u48 del_ttl:u48 epoch:u16
--                   n_links:u8 (<= 15)   links[n_links]
--                                        { from_epoch:u16 nonce[24] box[48] }
--                   n_members:u8 (<= 64) members[n_members]
--                                        { sign_pk[32] dh_pk[32] nonce[24] box[48] }
--    tag 1  REVOKE  ns[16] root_pk[32] salt[16] SIGNER sign_pk[32]
--                   from_t:u48 rev_seq:u48
--    tag 2  GRANT   ns[16] root_pk[32] salt[16] SIGNER subject[32]
--    tag 3  DEL     ns[16] ent[16] t:u48 seq:u48 author[32]
--    tag 4  PUT     ns[16] ent[16] flen:u8 field[flen] t:u48 seq:u48
--                   author[32] vlen:u16 value[vlen]   (vlen <= 40 960)
--
--    SIGNER = signer[32] cert_cap:u48 cert_sig[64]
--
--  A frame is  tag:u8 ‖ content ‖ sig[64];  h = BLAKE2b-256 (tag ‖ content);
--  sig = Ed25519 (RFC 8032, D4) over the 32 bytes of h, by author (PUT,
--  DEL) or by signer (ROSTER, REVOKE, GRANT). The tag is the Kind's
--  reconciliation-order code (Kome.Headers.Kind'Pos).
--
--  Roots (D1, DESIGN.md §2 "The signer block and root certificates").
--  root_pk is the collection's founding key: ns = BLAKE2b-256 (root_pk ‖
--  salt)[0:16] keeps the collection self-certifying. An authorization
--  record names its signer and proves, from its own bytes, that the signer
--  is a root: either signer = root_pk with cert_cap = 0 and a zero
--  cert_sig, or cert_sig is the founding key's signature over Cert_Hash =
--  BLAKE2b-256 ("kome/root" ‖ ns ‖ signer ‖ u48 (cert_cap)), and then a
--  ROSTER may not set ceiling_t above cert_cap. Only the founding key can
--  certify, so only it adds roots, and admission of authorization records
--  needs no history. Certificates cannot be narrowed: every certificate
--  ever issued stays valid, so a root's effective cap is the largest
--  cert_cap ever certified for it (§2); only root-voiding (§6, a view)
--  ends what a certificate allows. Kome.Store additionally refuses an
--  authorization record whose root_pk (Root_Key_Of) is not the store's
--  founding key (DESIGN.md §7 step 0).
--
--  Each kind has a content record (what is hashed) and a record = content
--  plus signature. Keeping the signature outside the content makes "signing
--  does not change h" a congruence the prover sees (Sign's Post).
--
--  What is proved, per kind (T13):
--    * Encode's length is the layout (Frame_Len) and every byte of the
--      frame is Frame_Byte, the layout read position by position; the
--      frame minus its signature is Content_Bytes, which is what Hash hashes.
--    * Decode accepts exactly the frames Is_<Kind>_Frame describes (exact
--      length, tag, flen in 1..32, vlen <= 40 960, n_links <= 15,
--      n_members <= 64), never reads out of bounds, returns Parse_<Kind> on
--      success and leaves the record unchanged on failure.
--    * Lemma_Decode_Encode: Parse (Encode (R)) = R for every canonical R,
--      so Decode (Encode (R)) returns OK and R.
--    * Lemma_Encode_Decode_<Kind>: Encode (Parse (B)) = B for every accepted
--      B: each record has exactly one encoding, so h is a function of the
--      record (A2 then makes h injective on records).
--    * Lemma_Header_Canonical: To_Header (R) is a canonical header
--      (Kome.Headers.Canonical, D3); for a ROSTER given that del_ttl is in
--      the clamp, which Well_Formed implies. So decode produces only
--      canonical headers.
--    * Decode_Verified accepts exactly the well-formed frames (DESIGN.md §2
--      items 1-5): shape, ns, the signer block, the certified ceiling, the
--      del_ttl clamp, the X25519 keys (E5), REVOKE never names root_pk,
--      and the signature.
--  Not proved: anything about BLAKE2b or Ed25519 themselves. Kome.Crypto's
--  Blake2b_256, Sign and Verify are opaque functions; Well_Formed calls
--  Verify, and no theorem here depends on what it returns.
--
--  Canonical form: unused field, value, link and member bytes are zero. On
--  canonical records Ada equality is equality of content; a record with
--  nonzero padding is Ada-unequal to its canonical twin yet has the same
--  content. So Encode and Sign require Canonical, Well_Formed includes it,
--  and Decode, the Make_* constructors and Sign only ever produce canonical
--  records. (The record types stay public so that tests can build
--  malformed records; Hash and To_Header read only the used bytes.)
--  Canonical is quantified, so it is opaque here (CONVENTIONS.md rule 2);
--  clients get it from Parse_*, Make_* and Sign Posts.
pragma Ada_2022;
with Kome.Headers;  use Kome.Headers;
with Kome.Keys;     use Kome.Keys;
with Kome.Crypto;
package Kome.Records with SPARK_Mode, Preelaborate is

   ---------------------------------------------------------------------------
   --  Tags (one byte, the Kind's representation, DESIGN.md §2 and §8 key
   --  order).
   ---------------------------------------------------------------------------

   Tag_Roster : constant Byte := 0;
   Tag_Revoke : constant Byte := 1;
   Tag_Grant  : constant Byte := 2;
   Tag_Del    : constant Byte := 3;
   Tag_Put    : constant Byte := 4;

   function Tag_Of (K : Kind) return Byte is
     (case K is
         when K_Roster => Tag_Roster,
         when K_Revoke => Tag_Revoke,
         when K_Grant  => Tag_Grant,
         when K_Del    => Tag_Del,
         when K_Put    => Tag_Put);

   --  The kind a frame claims to be (its first byte), if any.
   function Has_Kind (Frame : Byte_Array) return Boolean is
     (Frame'Length > 0 and then Frame (Frame'First) <= Tag_Put);

   function Kind_Of (Frame : Byte_Array) return Kind is
     (if Frame (Frame'First) = Tag_Roster then K_Roster
      elsif Frame (Frame'First) = Tag_Revoke then K_Revoke
      elsif Frame (Frame'First) = Tag_Grant then K_Grant
      elsif Frame (Frame'First) = Tag_Del then K_Del
      else K_Put)
     with Pre  => Has_Kind (Frame),
          Post => Tag_Of (Kind_Of'Result) = Frame (Frame'First);

   ---------------------------------------------------------------------------
   --  Big-endian integers (DESIGN.md §2 "all integers big-endian"), built on
   --  Kome.Keys' word lanes so the round trips reuse its proved lemmas.
   --  u48 = hi:u16 ‖ lo:u32; lane 0 is the most significant byte.
   ---------------------------------------------------------------------------

   subtype U48_Lane  is Natural range 0 .. 5;
   subtype U16_Lane  is Natural range 0 .. 1;
   subtype U16_Value is Natural range 0 .. 2 ** 16 - 1;

   function Byte_Of_U48 (V : U48; K : U48_Lane) return Byte is
     (case K is
         when 0 => Byte_Of_Word (Word (V / 2 ** 32), 2),
         when 1 => Byte_Of_Word (Word (V / 2 ** 32), 3),
         when 2 => Byte_Of_Word (Word (V mod 2 ** 32), 0),
         when 3 => Byte_Of_Word (Word (V mod 2 ** 32), 1),
         when 4 => Byte_Of_Word (Word (V mod 2 ** 32), 2),
         when 5 => Byte_Of_Word (Word (V mod 2 ** 32), 3));

   function U48_Of (B0, B1, B2, B3, B4, B5 : Byte) return U48 is
     (U48 (Word_Of (0, 0, B0, B1)) * 2 ** 32 + U48 (Word_Of (B2, B3, B4, B5)));

   function Byte_Of_U16 (V : U16_Value; K : U16_Lane) return Byte is
     (if K = 0 then Byte_Of_Word (Word (V), 2) else Byte_Of_Word (Word (V), 3));

   function U16_Of (B0, B1 : Byte) return U16_Value is
     (Natural (Word_Of (0, 0, B0, B1)));

   --  The integer stored at B (P ..): a view of a frame used by Decode.
   function U48_At (B : Byte_Array; P : Natural) return U48 is
     (U48_Of (B (P), B (P + 1), B (P + 2), B (P + 3), B (P + 4), B (P + 5)))
     with Pre => P >= B'First and then P <= B'Last and then B'Last - P >= 5;

   function U16_At (B : Byte_Array; P : Natural) return U16_Value is
     (U16_Of (B (P), B (P + 1)))
     with Pre => P >= B'First and then P <= B'Last and then B'Last - P >= 1;

   --  decode (encode V) = V.
   procedure Lemma_U48_Round_Trip (V : U48) with
     Ghost, Global => null,
     Post => U48_Of (Byte_Of_U48 (V, 0), Byte_Of_U48 (V, 1), Byte_Of_U48 (V, 2),
                     Byte_Of_U48 (V, 3), Byte_Of_U48 (V, 4), Byte_Of_U48 (V, 5)) = V;

   --  encode (decode B) = B: every six bytes are the encoding of one u48.
   procedure Lemma_U48_Bytes_Round_Trip (B0, B1, B2, B3, B4, B5 : Byte) with
     Ghost, Global => null,
     Post => Byte_Of_U48 (U48_Of (B0, B1, B2, B3, B4, B5), 0) = B0
       and then Byte_Of_U48 (U48_Of (B0, B1, B2, B3, B4, B5), 1) = B1
       and then Byte_Of_U48 (U48_Of (B0, B1, B2, B3, B4, B5), 2) = B2
       and then Byte_Of_U48 (U48_Of (B0, B1, B2, B3, B4, B5), 3) = B3
       and then Byte_Of_U48 (U48_Of (B0, B1, B2, B3, B4, B5), 4) = B4
       and then Byte_Of_U48 (U48_Of (B0, B1, B2, B3, B4, B5), 5) = B5;

   procedure Lemma_U16_Round_Trip (V : U16_Value) with
     Ghost, Global => null,
     Post => U16_Of (Byte_Of_U16 (V, 0), Byte_Of_U16 (V, 1)) = V;

   procedure Lemma_U16_Bytes_Round_Trip (B0, B1 : Byte) with
     Ghost, Global => null,
     Post => Byte_Of_U16 (U16_Of (B0, B1), 0) = B0
       and then Byte_Of_U16 (U16_Of (B0, B1), 1) = B1;

   ---------------------------------------------------------------------------
   --  Shared definitions.
   ---------------------------------------------------------------------------

   --  ns = BLAKE2b-256 (root_pk ‖ salt)[0:16] (DESIGN.md §2 "Identifiers").
   --  Kome.Store.Open checks its log HEADER with it (§7).
   function Collection_Id (Root_PK : Pubkey; Salt : Kome.Salt) return NS_Id is
     (Kome.Crypto.Blake2b_256 (Root_PK & Salt) (0 .. NS_Len - 1));

   --  Every frame is at most this long: a PUT with a 32-byte field and a
   --  40 960-byte value, 176 + Value_Max = 41 136 bytes (D12, §2 table);
   --  every hashed content is at most this minus 64.
   Frame_Max : constant := 1 + 16 + 16 + 1 + 32 + 6 + 6 + 32 + 2 + Value_Max + Sig_Len;
   pragma Compile_Time_Error
     (Frame_Max /= 41_136, "DESIGN.md §2: the largest frame is 41 136 bytes");

   Zero_Sig : constant Sig := [others => 0];

   ---------------------------------------------------------------------------
   --  The signer block and root certificates (D1, DESIGN.md §2).
   --    SIGNER = signer[32] cert_cap:u48 cert_sig[64]
   ---------------------------------------------------------------------------

   Cert_Label_Len : constant := 9;   --  "kome/root"
   Cert_Label     : constant Byte_Array (0 .. Cert_Label_Len - 1) :=
     [16#6B#, 16#6F#, 16#6D#, 16#65#, 16#2F#, 16#72#, 16#6F#, 16#6F#, 16#74#];
   Cert_Input_Len : constant := Cert_Label_Len + NS_Len + Pubkey_Len + 6;
   pragma Compile_Time_Error
     (Cert_Input_Len /= 63, "DESIGN.md §2: the certificate input is 63 bytes");
   subtype Cert_Input_Bytes is Byte_Array (0 .. Cert_Input_Len - 1);

   --  "kome/root" ‖ ns ‖ signer ‖ u48 (cap).
   function Cert_Input (NS : NS_Id; Signer : Pubkey; Cap : U48) return Cert_Input_Bytes is
     (Cert_Label & NS & Signer
      & Byte_Array'(Byte_Of_U48 (Cap, 0), Byte_Of_U48 (Cap, 1), Byte_Of_U48 (Cap, 2),
                    Byte_Of_U48 (Cap, 3), Byte_Of_U48 (Cap, 4), Byte_Of_U48 (Cap, 5)));

   --  What the founding key signs to certify a root.
   function Cert_Hash (NS : NS_Id; Signer : Pubkey; Cap : U48) return Hash256 is
     (Kome.Crypto.Blake2b_256 (Cert_Input (NS, Signer, Cap)));

   --  The signer block is valid: the founding key with a zero block, or a
   --  root certified by the founding key for this ns and cap.
   function Cert_OK
     (Root_PK : Pubkey; NS : NS_Id; Signer : Pubkey; Cap : U48; Cert : Sig) return Boolean
   is (if Signer = Root_PK then Cap = 0 and then Cert = Zero_Sig
       else Kome.Crypto.Verify (Cert, Root_PK, Cert_Hash (NS, Signer, Cap)));

   --  The certificate the founding key issues for a root (out of band, a
   --  key ceremony; DESIGN.md §2). The founding key itself takes no
   --  certificate (its block is zero).
   function Make_Cert
     (Founding : Kome.Crypto.Secret_Key; NS : NS_Id; Signer : Pubkey; Cap : U48) return Sig
   with Global => null,
        Pre  => Kome.Crypto.Is_Valid (Founding)
                and then Signer /= Kome.Crypto.Public_Of (Founding),
        Post => Make_Cert'Result = Kome.Crypto.Sign (Founding, Cert_Hash (NS, Signer, Cap));

   ---------------------------------------------------------------------------
   --  PUT   ns[16] ent[16] flen:u8 field[flen] t:u48 seq:u48 author[32]
   --        vlen:u16 value[vlen]
   ---------------------------------------------------------------------------

   subtype Field_Bytes is Byte_Array (0 .. Field_Max - 1);
   subtype Value_Bytes is Byte_Array (0 .. Value_Max - 1);

   type Put_Content is record
      NS     : NS_Id       := [others => 0];
      Ent    : Ent_Id      := [others => 0];
      FLen   : Field_Len   := 1;
      Field  : Field_Bytes := [others => 0];   --  Field (0 .. FLen - 1)
      T      : U48         := 0;
      Seq    : U48         := 0;
      Author : Pubkey      := [others => 0];
      VLen   : Value_Len   := 0;
      Value  : Value_Bytes := [others => 0];   --  Value (0 .. VLen - 1)
   end record;

   type Put_Record is record
      C         : Put_Content;
      Signature : Sig := [others => 0];
   end record;

   --  Frame offsets. The parts after the field move with flen.
   Put_O_NS    : constant := 1;
   Put_O_Ent   : constant := 17;
   Put_O_FLen  : constant := 33;
   Put_O_Field : constant := 34;
   Put_Fixed   : constant := 80;               --  tag + every fixed-width part
   Put_Frame_Min : constant := Put_Fixed + 1 + Sig_Len;
   Put_Frame_Max : constant := Put_Fixed + Field_Max + Value_Max + Sig_Len;

   function Put_O_T (FL : Field_Len) return Natural is (Put_O_Field + FL);
   function Put_O_Seq (FL : Field_Len) return Natural is (Put_O_Field + FL + 6);
   function Put_O_Author (FL : Field_Len) return Natural is (Put_O_Field + FL + 12);
   function Put_O_VLen (FL : Field_Len) return Natural is (Put_O_Field + FL + 44);
   function Put_O_Value (FL : Field_Len) return Natural is (Put_O_Field + FL + 46);

   function Content_Len (C : Put_Content) return Positive is
     (Put_Fixed + C.FLen + C.VLen);

   function Frame_Len (R : Put_Record) return Positive is
     (Content_Len (R.C) + Sig_Len);

   --  Byte J of tag ‖ content: the layout, position by position.
   function Content_Byte (C : Put_Content; J : Natural) return Byte is
     (if J = 0 then Tag_Put
      elsif J < Put_O_Ent then C.NS (J - Put_O_NS)
      elsif J < Put_O_FLen then C.Ent (J - Put_O_Ent)
      elsif J = Put_O_FLen then Byte (C.FLen)
      elsif J < Put_O_T (C.FLen) then C.Field (J - Put_O_Field)
      elsif J < Put_O_Seq (C.FLen) then Byte_Of_U48 (C.T, J - Put_O_T (C.FLen))
      elsif J < Put_O_Author (C.FLen) then Byte_Of_U48 (C.Seq, J - Put_O_Seq (C.FLen))
      elsif J < Put_O_VLen (C.FLen) then C.Author (J - Put_O_Author (C.FLen))
      elsif J < Put_O_Value (C.FLen) then Byte_Of_U16 (C.VLen, J - Put_O_VLen (C.FLen))
      else C.Value (J - Put_O_Value (C.FLen)))
     with Pre => J < Content_Len (C);

   function Frame_Byte (R : Put_Record; J : Natural) return Byte is
     (if J < Content_Len (R.C) then Content_Byte (R.C, J)
      else R.Signature (J - Content_Len (R.C)))
     with Pre => J < Frame_Len (R);

   --  Unused field and value bytes are zero. Opaque (quantified).
   function Canonical (R : Put_Record) return Boolean with Global => null;

   --  A canonical PUT with a zero signature (sign it with Sign).
   function Make_Put
     (NS     : NS_Id;
      Ent    : Ent_Id;
      Field  : Byte_Array;
      T, Seq : U48;
      Author : Pubkey;
      Value  : Byte_Array) return Put_Record
   with Global => null,
        Pre  => Field'Length in 1 .. Field_Max and then Value'Length <= Value_Max,
        Post => Canonical (Make_Put'Result)
          and then Make_Put'Result.C.NS = NS
          and then Make_Put'Result.C.Ent = Ent
          and then Make_Put'Result.C.FLen = Field'Length
          and then (for all I in 0 .. Field'Length - 1 =>
                      Make_Put'Result.C.Field (I) = Field (Field'First + I))
          and then Make_Put'Result.C.T = T
          and then Make_Put'Result.C.Seq = Seq
          and then Make_Put'Result.C.Author = Author
          and then Make_Put'Result.C.VLen = Value'Length
          and then (for all I in 0 .. Value'Length - 1 =>
                      Make_Put'Result.C.Value (I) = Value (Value'First + I))
          and then (for all I in Sig'Range => Make_Put'Result.Signature (I) = 0)
          --  The lattice header, from the arguments (DESIGN.md §5 step 2:
          --  the write path builds the record from the (t, seq) it chose,
          --  and h is the record's own hash). Kome.Emit's To_Header (Tgt,
          --  Stamp (T, Author, Seq, h)) for Tgt = (K_Put, NS, Ent, FH).
          and then To_Header (Make_Put'Result) =
                     (K       => K_Put,
                      NS      => To_Id128 (NS),
                      Ent     => To_Id128 (Ent),
                      FH      => To_Key256 (Kome.Crypto.Blake2b_256 (Field)),
                      V       => (T      => T,
                                  Author => To_Key256 (Author),
                                  Seq    => Seq,
                                  H      => To_Key256 (Hash (Make_Put'Result.C))),
                      Issuer  => Zero_Key,
                      Del_TTL => 0)
          and then Kome.Headers.Canonical (To_Header (Make_Put'Result));

   --  tag ‖ content, the bytes h is computed over.
   function Content_Bytes (C : Put_Content) return Byte_Array
   with Global => null,
        Post => Content_Bytes'Result'First = 0
          and then Content_Bytes'Result'Length = Content_Len (C)
          and then (for all J in 0 .. Content_Len (C) - 1 =>
                      Content_Bytes'Result (J) = Content_Byte (C, J));

   --  h = BLAKE2b-256 (tag ‖ content) (DESIGN.md §2).
   function Hash (C : Put_Content) return Hash256 is
     (Kome.Crypto.Blake2b_256 (Content_Bytes (C)));

   --  The frame. T13: its length is the layout, every byte is the layout.
   function Encode (R : Put_Record) return Byte_Array
   with Global => null,
        Pre  => Canonical (R),
        Post => Encode'Result'First = 0
          and then Encode'Result'Length = Frame_Len (R)
          and then (for all J in 0 .. Frame_Len (R) - 1 =>
                      Encode'Result (J) = Frame_Byte (R, J))
          and then Encode'Result (0 .. Content_Len (R.C) - 1) = Content_Bytes (R.C)
          and then Encode'Result (Content_Len (R.C) .. Frame_Len (R) - 1) = R.Signature;

   --  The shape Decode accepts. flen and vlen are read only after the
   --  length check that makes their positions exist.
   function Put_FL (Frame : Byte_Array) return Natural is
     (Natural (Frame (Frame'First + Put_O_FLen)))
     with Pre => Frame'Length >= Put_Frame_Min;

   function Put_VL (Frame : Byte_Array) return U16_Value is
     (U16_At (Frame, Frame'First + Put_O_VLen (Put_FL (Frame))))
     with Pre => Frame'Length >= Put_Frame_Min and then Put_FL (Frame) in Field_Len;

   --  vlen stays a u16 on the wire; a value above Value_Max (40 960, D12)
   --  is refused (§2 item 1).
   function Is_Put_Frame (Frame : Byte_Array) return Boolean is
     (Frame'Length >= Put_Frame_Min
      and then Frame'Length <= Put_Frame_Max
      and then Frame (Frame'First) = Tag_Put
      and then Put_FL (Frame) in Field_Len
      and then Put_VL (Frame) <= Value_Max
      and then Frame'Length = Put_Fixed + Sig_Len + Put_FL (Frame) + Put_VL (Frame));

   --  The record an accepted frame encodes, field by field.
   function Parse_Put (Frame : Byte_Array) return Put_Record
   with Global => null,
        Pre  => Is_Put_Frame (Frame),
        Post => Canonical (Parse_Put'Result)
          and then Parse_Put'Result.C.FLen = Put_FL (Frame)
          and then Parse_Put'Result.C.VLen = Put_VL (Frame)
          and then Parse_Put'Result.C.T =
                     U48_At (Frame, Frame'First + Put_O_T (Put_FL (Frame)))
          and then Parse_Put'Result.C.Seq =
                     U48_At (Frame, Frame'First + Put_O_Seq (Put_FL (Frame)))
          and then (for all I in NS_Id'Range =>
                      Parse_Put'Result.C.NS (I) = Frame (Frame'First + Put_O_NS + I))
          and then (for all I in Ent_Id'Range =>
                      Parse_Put'Result.C.Ent (I) = Frame (Frame'First + Put_O_Ent + I))
          and then (for all I in Field_Bytes'Range =>
                      Parse_Put'Result.C.Field (I) =
                        (if I < Put_FL (Frame)
                         then Frame (Frame'First + Put_O_Field + I) else 0))
          and then (for all I in Pubkey'Range =>
                      Parse_Put'Result.C.Author (I) =
                        Frame (Frame'First + Put_O_Author (Put_FL (Frame)) + I))
          and then (for all I in Value_Bytes'Range =>
                      Parse_Put'Result.C.Value (I) =
                        (if I < Put_VL (Frame)
                         then Frame (Frame'First + Put_O_Value (Put_FL (Frame)) + I)
                         else 0))
          and then (for all I in Sig'Range =>
                      Parse_Put'Result.Signature (I) =
                        Frame (Frame'First + Put_O_Value (Put_FL (Frame))
                               + Put_VL (Frame) + I));

   --  Total over all byte strings; R is unchanged on refusal.
   procedure Decode (Frame : Byte_Array; R : in out Put_Record; Result : out Status)
   with Global => null,
        Post => (if Is_Put_Frame (Frame)
                 then Result = OK and then R = Parse_Put (Frame)
                 else Result = Malformed and then R = R'Old);

   --  Well-formed (DESIGN.md §2): bounds (by type), canonical padding, and
   --  the signature over h verifies under author.
   function Well_Formed (R : Put_Record) return Boolean is
     (Canonical (R)
      and then Kome.Crypto.Verify (R.Signature, R.C.Author, Hash (R.C)));

   --  Decode, then refuse unless well-formed. R is unchanged on refusal.
   procedure Decode_Verified
     (Frame : Byte_Array; R : in out Put_Record; Result : out Status)
   with Global => null,
        Post => (if Is_Put_Frame (Frame) and then Well_Formed (Parse_Put (Frame))
                 then Result = OK and then R = Parse_Put (Frame)
                 else Result = Malformed and then R = R'Old);

   --  sig := Ed25519 (h) by the author's key. Only the signature changes,
   --  so h and the header do not.
   procedure Sign (R : in out Put_Record; SK : Kome.Crypto.Secret_Key)
   with Global => null,
        Pre  => Canonical (R)
                and then Kome.Crypto.Is_Valid (SK)
                and then Kome.Crypto.Public_Of (SK) = R.C.Author,
        Post => Canonical (R)
          and then R.C = R'Old.C
          and then R.Signature = Kome.Crypto.Sign (SK, Hash (R'Old.C))
          and then Hash (R.C) = Hash (R'Old.C);

   --  The lattice header (Kome.Headers): V = (t, author, seq, h),
   --  FH = BLAKE2b-256 (field name), no issuer, del_ttl 0.
   function To_Header (R : Put_Record) return Header is
     (K       => K_Put,
      NS      => To_Id128 (R.C.NS),
      Ent     => To_Id128 (R.C.Ent),
      FH      => To_Key256 (Kome.Crypto.Blake2b_256 (R.C.Field (0 .. R.C.FLen - 1))),
      V       => (T      => R.C.T,
                  Author => To_Key256 (R.C.Author),
                  Seq    => R.C.Seq,
                  H      => To_Key256 (Hash (R.C))),
      Issuer  => Zero_Key,
      Del_TTL => 0);

   --  D3: the header is canonical.
   procedure Lemma_Header_Canonical (R : Put_Record) with
     Ghost, Global => null,
     Post => To_Header (R).K = K_Put and then Kome.Headers.Canonical (To_Header (R));

   --  Round trip (T13): Parse (Encode (R)) = R, hence Decode (Encode (R))
   --  returns OK and R.
   procedure Lemma_Decode_Encode (R : Put_Record) with
     Ghost, Global => null,
     Pre  => Canonical (R),
     Post => Is_Put_Frame (Encode (R)) and then Parse_Put (Encode (R)) = R;

   --  The encoding is canonical: an accepted frame is the encoding of what
   --  it decodes to.
   procedure Lemma_Encode_Decode_Put (Frame : Byte_Array) with
     Ghost, Global => null,
     Pre  => Is_Put_Frame (Frame),
     Post => Encode (Parse_Put (Frame)) = Frame;

   ---------------------------------------------------------------------------
   --  DEL   ns[16] ent[16] t:u48 seq:u48 author[32]
   ---------------------------------------------------------------------------

   type Del_Content is record
      NS     : NS_Id  := [others => 0];
      Ent    : Ent_Id := [others => 0];
      T      : U48    := 0;
      Seq    : U48    := 0;
      Author : Pubkey := [others => 0];
   end record;

   type Del_Record is record
      C         : Del_Content;
      Signature : Sig := [others => 0];
   end record;

   Del_O_NS     : constant := 1;
   Del_O_Ent    : constant := 17;
   Del_O_T      : constant := 33;
   Del_O_Seq    : constant := 39;
   Del_O_Author : constant := 45;
   Del_Content_Len : constant := 77;
   Del_Frame_Len   : constant := Del_Content_Len + Sig_Len;

   function Content_Byte (C : Del_Content; J : Natural) return Byte is
     (if J = 0 then Tag_Del
      elsif J < Del_O_Ent then C.NS (J - Del_O_NS)
      elsif J < Del_O_T then C.Ent (J - Del_O_Ent)
      elsif J < Del_O_Seq then Byte_Of_U48 (C.T, J - Del_O_T)
      elsif J < Del_O_Author then Byte_Of_U48 (C.Seq, J - Del_O_Seq)
      else C.Author (J - Del_O_Author))
     with Pre => J < Del_Content_Len;

   function Frame_Byte (R : Del_Record; J : Natural) return Byte is
     (if J < Del_Content_Len then Content_Byte (R.C, J)
      else R.Signature (J - Del_Content_Len))
     with Pre => J < Del_Frame_Len;

   function Content_Bytes (C : Del_Content) return Byte_Array
   with Global => null,
        Post => Content_Bytes'Result'First = 0
          and then Content_Bytes'Result'Length = Del_Content_Len
          and then (for all J in 0 .. Del_Content_Len - 1 =>
                      Content_Bytes'Result (J) = Content_Byte (C, J));

   function Hash (C : Del_Content) return Hash256 is
     (Kome.Crypto.Blake2b_256 (Content_Bytes (C)));

   function Encode (R : Del_Record) return Byte_Array
   with Global => null,
        Post => Encode'Result'First = 0
          and then Encode'Result'Length = Del_Frame_Len
          and then (for all J in 0 .. Del_Frame_Len - 1 =>
                      Encode'Result (J) = Frame_Byte (R, J))
          and then Encode'Result (0 .. Del_Content_Len - 1) = Content_Bytes (R.C)
          and then Encode'Result (Del_Content_Len .. Del_Frame_Len - 1) = R.Signature;

   function Is_Del_Frame (Frame : Byte_Array) return Boolean is
     (Frame'Length = Del_Frame_Len and then Frame (Frame'First) = Tag_Del);

   function Parse_Del (Frame : Byte_Array) return Del_Record
   with Global => null,
        Pre  => Is_Del_Frame (Frame),
        Post => Parse_Del'Result.C.T = U48_At (Frame, Frame'First + Del_O_T)
          and then Parse_Del'Result.C.Seq = U48_At (Frame, Frame'First + Del_O_Seq)
          and then (for all I in NS_Id'Range =>
                      Parse_Del'Result.C.NS (I) = Frame (Frame'First + Del_O_NS + I))
          and then (for all I in Ent_Id'Range =>
                      Parse_Del'Result.C.Ent (I) = Frame (Frame'First + Del_O_Ent + I))
          and then (for all I in Pubkey'Range =>
                      Parse_Del'Result.C.Author (I) = Frame (Frame'First + Del_O_Author + I))
          and then (for all I in Sig'Range =>
                      Parse_Del'Result.Signature (I) =
                        Frame (Frame'First + Del_Content_Len + I));

   procedure Decode (Frame : Byte_Array; R : in out Del_Record; Result : out Status)
   with Global => null,
        Post => (if Is_Del_Frame (Frame)
                 then Result = OK and then R = Parse_Del (Frame)
                 else Result = Malformed and then R = R'Old);

   function Well_Formed (R : Del_Record) return Boolean is
     (Kome.Crypto.Verify (R.Signature, R.C.Author, Hash (R.C)));

   procedure Decode_Verified
     (Frame : Byte_Array; R : in out Del_Record; Result : out Status)
   with Global => null,
        Post => (if Is_Del_Frame (Frame) and then Well_Formed (Parse_Del (Frame))
                 then Result = OK and then R = Parse_Del (Frame)
                 else Result = Malformed and then R = R'Old);

   procedure Sign (R : in out Del_Record; SK : Kome.Crypto.Secret_Key)
   with Global => null,
        Pre  => Kome.Crypto.Is_Valid (SK)
                and then Kome.Crypto.Public_Of (SK) = R.C.Author,
        Post => R.C = R'Old.C
          and then R.Signature = Kome.Crypto.Sign (SK, Hash (R'Old.C))
          and then Hash (R.C) = Hash (R'Old.C);

   --  V = (t, author, seq, h); a DEL has no field (FH 0), no issuer and
   --  del_ttl 0.
   function To_Header (R : Del_Record) return Header is
     (K       => K_Del,
      NS      => To_Id128 (R.C.NS),
      Ent     => To_Id128 (R.C.Ent),
      FH      => Zero_Key,
      V       => (T      => R.C.T,
                  Author => To_Key256 (R.C.Author),
                  Seq    => R.C.Seq,
                  H      => To_Key256 (Hash (R.C))),
      Issuer  => Zero_Key,
      Del_TTL => 0);

   procedure Lemma_Header_Canonical (R : Del_Record) with
     Ghost, Global => null,
     Post => To_Header (R).K = K_Del and then Kome.Headers.Canonical (To_Header (R));

   --  A DEL with a zero signature (sign it with Sign): the DEL counterpart
   --  of Make_Put, for step 2 of the write path (DESIGN.md §5). Its lattice
   --  header is Kome.Emit's To_Header (Tgt, Stamp (T, Author, Seq, h)) for
   --  Tgt = (K_Del, NS, Ent, 0), with h the record's own hash.
   function Make_Del
     (NS     : NS_Id;
      Ent    : Ent_Id;
      T, Seq : U48;
      Author : Pubkey) return Del_Record
   with Global => null,
        Post => Make_Del'Result.C.NS = NS
          and then Make_Del'Result.C.Ent = Ent
          and then Make_Del'Result.C.T = T
          and then Make_Del'Result.C.Seq = Seq
          and then Make_Del'Result.C.Author = Author
          and then (for all I in Sig'Range => Make_Del'Result.Signature (I) = 0)
          and then To_Header (Make_Del'Result) =
                     (K       => K_Del,
                      NS      => To_Id128 (NS),
                      Ent     => To_Id128 (Ent),
                      FH      => Zero_Key,
                      V       => (T      => T,
                                  Author => To_Key256 (Author),
                                  Seq    => Seq,
                                  H      => To_Key256 (Hash (Make_Del'Result.C))),
                      Issuer  => Zero_Key,
                      Del_TTL => 0)
          and then Kome.Headers.Canonical (To_Header (Make_Del'Result));

   procedure Lemma_Decode_Encode (R : Del_Record) with
     Ghost, Global => null,
     Post => Is_Del_Frame (Encode (R)) and then Parse_Del (Encode (R)) = R;

   procedure Lemma_Encode_Decode_Del (Frame : Byte_Array) with
     Ghost, Global => null,
     Pre  => Is_Del_Frame (Frame),
     Post => Encode (Parse_Del (Frame)) = Frame;

   ---------------------------------------------------------------------------
   --  ROSTER  ns[16] root_pk[32] salt[16] SIGNER box_pk[32]
   --          gen:u48 ceiling_t:u48 del_ttl:u48 epoch:u16
   --          n_links:u8 links[n_links] { from_epoch:u16 nonce[24] box[48] }
   --          n_members:u8 members[n] { sign_pk[32] dh_pk[32] nonce[24] box[48] }
   --  Links and members are stored flat, as on the wire, so the encoding is
   --  a sequence of byte copies; the accessors below cut them up.
   ---------------------------------------------------------------------------

   Link_Len          : constant := 2 + Nonce_Len + Box_Len;                        --  74
   Member_Len        : constant := Pubkey_Len + Pubkey_Len + Nonce_Len + Box_Len;  --  136
   Links_Bytes_Len   : constant := Links_Max * Link_Len;
   Members_Bytes_Len : constant := Members_Max * Member_Len;

   subtype Link_Count    is Natural range 0 .. Links_Max;
   subtype Member_Count  is Natural range 0 .. Members_Max;
   subtype Link_Index    is Positive range 1 .. Links_Max;
   subtype Member_Index  is Positive range 1 .. Members_Max;
   subtype Links_Bytes   is Byte_Array (0 .. Links_Bytes_Len - 1);
   subtype Members_Bytes is Byte_Array (0 .. Members_Bytes_Len - 1);

   type Roster_Content is record
      NS        : NS_Id         := [others => 0];
      Root_PK   : Pubkey        := [others => 0];   --  founding key (ns)
      Salt      : Kome.Salt     := [others => 0];
      Signer    : Pubkey        := [others => 0];   --  issuing root
      Cert_Cap  : U48           := 0;
      Cert_Sig  : Sig           := [others => 0];
      Box_PK    : Pubkey        := [others => 0];   --  ephemeral X25519 (D5)
      Gen       : U48           := 0;
      Ceiling_T : U48           := 0;
      Del_TTL   : U48           := 0;
      Epoch     : Kome.Epoch    := 0;
      N_Links   : Link_Count    := 0;
      Links     : Links_Bytes   := [others => 0];   --  Links (0 .. 74 * N_Links - 1)
      N_Members : Member_Count  := 0;
      Members   : Members_Bytes := [others => 0];   --  Members (0 .. 136 * N_Members - 1)
   end record;

   type Roster_Record is record
      C         : Roster_Content;
      Signature : Sig := [others => 0];
   end record;

   Roster_O_NS       : constant := 1;
   Roster_O_Root_PK  : constant := 17;
   Roster_O_Salt     : constant := 49;
   Roster_O_Signer   : constant := 65;
   Roster_O_Cert_Cap : constant := 97;
   Roster_O_Cert_Sig : constant := 103;
   Roster_O_Box_PK   : constant := 167;
   Roster_O_Gen      : constant := 199;
   Roster_O_Ceiling  : constant := 205;
   Roster_O_TTL      : constant := 211;
   Roster_O_Epoch    : constant := 217;
   Roster_O_NL       : constant := 219;
   Roster_O_Links    : constant := 220;
   Roster_Fixed      : constant := 221;          --  tag + every fixed-width part
   Roster_Frame_Min  : constant := Roster_Fixed + Sig_Len;
   Roster_Frame_Max  : constant :=
     Roster_Fixed + Links_Bytes_Len + Members_Bytes_Len + Sig_Len;
   pragma Compile_Time_Error
     (Roster_Frame_Min /= 285 or else Roster_Frame_Max /= 10_099,
      "DESIGN.md §2: a ROSTER frame is 285 .. 10 099 bytes");
   pragma Compile_Time_Error
     (Roster_Frame_Max > Frame_Max, "every ROSTER frame must fit Frame_Max");

   function Roster_O_NM (NL : Natural) return Natural is
     (Roster_O_Links + Link_Len * NL)
     with Pre => NL <= 255;
   function Roster_O_Members (NL : Natural) return Natural is
     (Roster_O_Links + Link_Len * NL + 1)
     with Pre => NL <= 255;

   function Content_Len (C : Roster_Content) return Positive is
     (Roster_Fixed + Link_Len * C.N_Links + Member_Len * C.N_Members);

   function Frame_Len (R : Roster_Record) return Positive is
     (Content_Len (R.C) + Sig_Len);

   function Content_Byte (C : Roster_Content; J : Natural) return Byte is
     (if J = 0 then Tag_Roster
      elsif J < Roster_O_Root_PK then C.NS (J - Roster_O_NS)
      elsif J < Roster_O_Salt then C.Root_PK (J - Roster_O_Root_PK)
      elsif J < Roster_O_Signer then C.Salt (J - Roster_O_Salt)
      elsif J < Roster_O_Cert_Cap then C.Signer (J - Roster_O_Signer)
      elsif J < Roster_O_Cert_Sig then Byte_Of_U48 (C.Cert_Cap, J - Roster_O_Cert_Cap)
      elsif J < Roster_O_Box_PK then C.Cert_Sig (J - Roster_O_Cert_Sig)
      elsif J < Roster_O_Gen then C.Box_PK (J - Roster_O_Box_PK)
      elsif J < Roster_O_Ceiling then Byte_Of_U48 (C.Gen, J - Roster_O_Gen)
      elsif J < Roster_O_TTL then Byte_Of_U48 (C.Ceiling_T, J - Roster_O_Ceiling)
      elsif J < Roster_O_Epoch then Byte_Of_U48 (C.Del_TTL, J - Roster_O_TTL)
      elsif J < Roster_O_NL then Byte_Of_U16 (Natural (C.Epoch), J - Roster_O_Epoch)
      elsif J = Roster_O_NL then Byte (C.N_Links)
      elsif J < Roster_O_NM (C.N_Links) then C.Links (J - Roster_O_Links)
      elsif J = Roster_O_NM (C.N_Links) then Byte (C.N_Members)
      else C.Members (J - Roster_O_Members (C.N_Links)))
     with Pre => J < Content_Len (C);

   function Frame_Byte (R : Roster_Record; J : Natural) return Byte is
     (if J < Content_Len (R.C) then Content_Byte (R.C, J)
      else R.Signature (J - Content_Len (R.C)))
     with Pre => J < Frame_Len (R);

   --  Link I's parts (E3: link {from_epoch, nonce, box}) and member I's
   --  parts. The nonce, box and key accessors are opaque (each is a
   --  quantified aggregate, CONVENTIONS.md rule 2); their bytes are
   --  Lemma_Link_Bytes and Lemma_Member_Bytes.
   function Link_From_Epoch (C : Roster_Content; I : Link_Index) return Epoch is
     (Epoch (U16_Of (C.Links (Link_Len * (I - 1)), C.Links (Link_Len * (I - 1) + 1))))
     with Pre => I <= C.N_Links;

   function Link_Nonce (C : Roster_Content; I : Link_Index) return Nonce
     with Global => null, Pre => I <= C.N_Links;

   function Link_Box (C : Roster_Content; I : Link_Index) return Box
     with Global => null, Pre => I <= C.N_Links;

   function Member_Sign_PK (C : Roster_Content; I : Member_Index) return Pubkey
     with Global => null, Pre => I <= C.N_Members;

   function Member_DH_PK (C : Roster_Content; I : Member_Index) return Pubkey
     with Global => null, Pre => I <= C.N_Members;

   function Member_Nonce (C : Roster_Content; I : Member_Index) return Nonce
     with Global => null, Pre => I <= C.N_Members;

   function Member_Box (C : Roster_Content; I : Member_Index) return Box
     with Global => null, Pre => I <= C.N_Members;

   --  The member's signing key as the lattice sees it.
   function Member_Key (C : Roster_Content; I : Member_Index) return Key256 is
     (To_Key256 (Member_Sign_PK (C, I)))
     with Pre => I <= C.N_Members;

   procedure Lemma_Link_Bytes (C : Roster_Content; I : Link_Index) with
     Ghost, Global => null,
     Pre  => I <= C.N_Links,
     Post => Natural (Link_From_Epoch (C, I)) =
               U16_Of (C.Links (Link_Len * (I - 1)), C.Links (Link_Len * (I - 1) + 1))
       and then (for all K in Nonce'Range =>
                   Link_Nonce (C, I) (K) = C.Links (Link_Len * (I - 1) + 2 + K))
       and then (for all K in Box'Range =>
                   Link_Box (C, I) (K) = C.Links (Link_Len * (I - 1) + 2 + Nonce_Len + K));

   procedure Lemma_Member_Bytes (C : Roster_Content; I : Member_Index) with
     Ghost, Global => null,
     Pre  => I <= C.N_Members,
     Post => (for all K in Pubkey'Range =>
                Member_Sign_PK (C, I) (K) = C.Members (Member_Len * (I - 1) + K))
       and then (for all K in Pubkey'Range =>
                   Member_DH_PK (C, I) (K) =
                     C.Members (Member_Len * (I - 1) + Pubkey_Len + K))
       and then (for all K in Nonce'Range =>
                   Member_Nonce (C, I) (K) =
                     C.Members (Member_Len * (I - 1) + 2 * Pubkey_Len + K))
       and then (for all K in Box'Range =>
                   Member_Box (C, I) (K) =
                     C.Members (Member_Len * (I - 1) + 2 * Pubkey_Len + Nonce_Len + K));

   --  E5 (DESIGN.md §2 item 3): box_pk and every member dh_pk is a reduced
   --  X25519 encoding and not low order (Kome.Crypto.Is_Good_DH_Key), so
   --  every listed member can open its box. Opaque (quantified); its
   --  meaning is Lemma_DH_Keys_OK_Def, and Lemma_DH_Box_OK /
   --  Lemma_DH_Keys_OK give it one key at a time.
   function DH_Keys_OK (C : Roster_Content) return Boolean with Global => null;

   procedure Lemma_DH_Keys_OK_Def (C : Roster_Content) with
     Ghost, Global => null,
     Post => DH_Keys_OK (C) =
               (Kome.Crypto.Is_Good_DH_Key (C.Box_PK)
                and then (for all I in 1 .. C.N_Members =>
                            Kome.Crypto.Is_Good_DH_Key (Member_DH_PK (C, I))));

   procedure Lemma_DH_Box_OK (C : Roster_Content) with
     Ghost, Global => null,
     Pre  => DH_Keys_OK (C),
     Post => Kome.Crypto.Is_Good_DH_Key (C.Box_PK);

   procedure Lemma_DH_Keys_OK (C : Roster_Content; I : Member_Index) with
     Ghost, Global => null,
     Pre  => DH_Keys_OK (C) and then I <= C.N_Members,
     Post => Kome.Crypto.Is_Good_DH_Key (Member_DH_PK (C, I));

   --  Unused link and member bytes are zero. Opaque (quantified).
   function Canonical (R : Roster_Record) return Boolean with Global => null;

   --  A canonical ROSTER with ns derived from (root_pk, salt) and a zero
   --  signature. Links and Members are the flat wire bytes.
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
   with Global => null,
        Pre  => Links'Length <= Links_Bytes_Len
                and then Links'Length mod Link_Len = 0
                and then Members'Length <= Members_Bytes_Len
                and then Members'Length mod Member_Len = 0,
        Post => Canonical (Make_Roster'Result)
          and then Make_Roster'Result.C.NS = Collection_Id (Root_PK, S)
          and then Make_Roster'Result.C.Root_PK = Root_PK
          and then Make_Roster'Result.C.Salt = S
          and then Make_Roster'Result.C.Signer = Signer
          and then Make_Roster'Result.C.Cert_Cap = Cert_Cap
          and then Make_Roster'Result.C.Cert_Sig = Cert_Sig
          and then Make_Roster'Result.C.Box_PK = Box_PK
          and then Make_Roster'Result.C.Gen = Gen
          and then Make_Roster'Result.C.Ceiling_T = Ceiling_T
          and then Make_Roster'Result.C.Del_TTL = Del_TTL
          and then Make_Roster'Result.C.Epoch = E
          and then Make_Roster'Result.C.N_Links * Link_Len = Links'Length
          and then (for all I in 0 .. Links'Length - 1 =>
                      Make_Roster'Result.C.Links (I) = Links (Links'First + I))
          and then Make_Roster'Result.C.N_Members * Member_Len = Members'Length
          and then (for all I in 0 .. Members'Length - 1 =>
                      Make_Roster'Result.C.Members (I) = Members (Members'First + I))
          and then (for all I in Sig'Range => Make_Roster'Result.Signature (I) = 0);

   function Content_Bytes (C : Roster_Content) return Byte_Array
   with Global => null,
        Post => Content_Bytes'Result'First = 0
          and then Content_Bytes'Result'Length = Content_Len (C)
          and then (for all J in 0 .. Content_Len (C) - 1 =>
                      Content_Bytes'Result (J) = Content_Byte (C, J));

   function Hash (C : Roster_Content) return Hash256 is
     (Kome.Crypto.Blake2b_256 (Content_Bytes (C)));

   function Encode (R : Roster_Record) return Byte_Array
   with Global => null,
        Pre  => Canonical (R),
        Post => Encode'Result'First = 0
          and then Encode'Result'Length = Frame_Len (R)
          and then (for all J in 0 .. Frame_Len (R) - 1 =>
                      Encode'Result (J) = Frame_Byte (R, J))
          and then Encode'Result (0 .. Content_Len (R.C) - 1) = Content_Bytes (R.C)
          and then Encode'Result (Content_Len (R.C) .. Frame_Len (R) - 1) = R.Signature;

   function Roster_NL (Frame : Byte_Array) return Natural is
     (Natural (Frame (Frame'First + Roster_O_NL)))
     with Pre => Frame'Length >= Roster_Frame_Min;

   --  n_members sits after the links, so it is read only once the frame is
   --  long enough to hold n_links links.
   function Roster_NM (Frame : Byte_Array) return Natural is
     (Natural (Frame (Frame'First + Roster_O_NM (Roster_NL (Frame)))))
     with Pre => Frame'Length >= Roster_Frame_Min
                 and then Frame'Length <= Roster_Frame_Max
                 and then Frame'Length >= Roster_Frame_Min + Link_Len * Roster_NL (Frame);

   function Is_Roster_Frame (Frame : Byte_Array) return Boolean is
     (Frame'Length >= Roster_Frame_Min
      and then Frame'Length <= Roster_Frame_Max
      and then Frame (Frame'First) = Tag_Roster
      and then Roster_NL (Frame) <= Links_Max
      and then Frame'Length >= Roster_Frame_Min + Link_Len * Roster_NL (Frame)
      and then Roster_NM (Frame) <= Members_Max
      and then Frame'Length = Roster_Frame_Min + Link_Len * Roster_NL (Frame)
                              + Member_Len * Roster_NM (Frame));

   function Parse_Roster (Frame : Byte_Array) return Roster_Record
   with Global => null,
        Pre  => Is_Roster_Frame (Frame),
        Post => Canonical (Parse_Roster'Result)
          and then Parse_Roster'Result.C.Cert_Cap =
                     U48_At (Frame, Frame'First + Roster_O_Cert_Cap)
          and then Parse_Roster'Result.C.Gen = U48_At (Frame, Frame'First + Roster_O_Gen)
          and then Parse_Roster'Result.C.Ceiling_T =
                     U48_At (Frame, Frame'First + Roster_O_Ceiling)
          and then Parse_Roster'Result.C.Del_TTL = U48_At (Frame, Frame'First + Roster_O_TTL)
          and then Parse_Roster'Result.C.Epoch =
                     Epoch (U16_At (Frame, Frame'First + Roster_O_Epoch))
          and then Parse_Roster'Result.C.N_Links = Roster_NL (Frame)
          and then Parse_Roster'Result.C.N_Members = Roster_NM (Frame)
          and then (for all I in NS_Id'Range =>
                      Parse_Roster'Result.C.NS (I) = Frame (Frame'First + Roster_O_NS + I))
          and then (for all I in Pubkey'Range =>
                      Parse_Roster'Result.C.Root_PK (I) =
                        Frame (Frame'First + Roster_O_Root_PK + I))
          and then (for all I in Salt'Range =>
                      Parse_Roster'Result.C.Salt (I) = Frame (Frame'First + Roster_O_Salt + I))
          and then (for all I in Pubkey'Range =>
                      Parse_Roster'Result.C.Signer (I) =
                        Frame (Frame'First + Roster_O_Signer + I))
          and then (for all I in Sig'Range =>
                      Parse_Roster'Result.C.Cert_Sig (I) =
                        Frame (Frame'First + Roster_O_Cert_Sig + I))
          and then (for all I in Pubkey'Range =>
                      Parse_Roster'Result.C.Box_PK (I) =
                        Frame (Frame'First + Roster_O_Box_PK + I))
          and then (for all I in Links_Bytes'Range =>
                      Parse_Roster'Result.C.Links (I) =
                        (if I < Link_Len * Roster_NL (Frame)
                         then Frame (Frame'First + Roster_O_Links + I) else 0))
          and then (for all I in Members_Bytes'Range =>
                      Parse_Roster'Result.C.Members (I) =
                        (if I < Member_Len * Roster_NM (Frame)
                         then Frame (Frame'First + Roster_O_Members (Roster_NL (Frame)) + I)
                         else 0))
          and then (for all I in Sig'Range =>
                      Parse_Roster'Result.Signature (I) =
                        Frame (Frame'First + Roster_O_Members (Roster_NL (Frame))
                               + Member_Len * Roster_NM (Frame) + I));

   procedure Decode (Frame : Byte_Array; R : in out Roster_Record; Result : out Status)
   with Global => null,
        Post => (if Is_Roster_Frame (Frame)
                 then Result = OK and then R = Parse_Roster (Frame)
                 else Result = Malformed and then R = R'Old);

   --  Well-formed (DESIGN.md §2 items 1-3 and 5), all from the bytes:
   --  canonical, ns matches (root_pk, salt), the signer block is valid, a
   --  certified root's ceiling_t is within its cert_cap, del_ttl is in the
   --  clamp, the X25519 keys are good (E5), and the signature over h
   --  verifies under signer.
   function Well_Formed (R : Roster_Record) return Boolean is
     (Canonical (R)
      and then R.C.NS = Collection_Id (R.C.Root_PK, R.C.Salt)
      and then Cert_OK (R.C.Root_PK, R.C.NS, R.C.Signer, R.C.Cert_Cap, R.C.Cert_Sig)
      and then (if R.C.Signer /= R.C.Root_PK then R.C.Ceiling_T <= R.C.Cert_Cap)
      and then R.C.Del_TTL in Del_TTL_Min .. Del_TTL_Max
      and then DH_Keys_OK (R.C)
      and then Kome.Crypto.Verify (R.Signature, R.C.Signer, Hash (R.C)));

   procedure Decode_Verified
     (Frame : Byte_Array; R : in out Roster_Record; Result : out Status)
   with Global => null,
        Post => (if Is_Roster_Frame (Frame) and then Well_Formed (Parse_Roster (Frame))
                 then Result = OK and then R = Parse_Roster (Frame)
                 else Result = Malformed and then R = R'Old);

   procedure Sign (R : in out Roster_Record; SK : Kome.Crypto.Secret_Key)
   with Global => null,
        Pre  => Canonical (R)
                and then Kome.Crypto.Is_Valid (SK)
                and then Kome.Crypto.Public_Of (SK) = R.C.Signer,
        Post => Canonical (R)
          and then R.C = R'Old.C
          and then R.Signature = Kome.Crypto.Sign (SK, Hash (R'Old.C))
          and then Hash (R.C) = Hash (R'Old.C);

   --  The issuing root as the lattice sees it (the header's Issuer).
   function Signer_Key (R : Roster_Record) return Key256 is
     (To_Key256 (R.C.Signer));

   --  DESIGN.md §3: V = (ceiling_t, signer, gen, h); Issuer = signer;
   --  Del_TTL = del_ttl; no entity, no field.
   function To_Header (R : Roster_Record) return Header is
     (K       => K_Roster,
      NS      => To_Id128 (R.C.NS),
      Ent     => Zero_Id,
      FH      => Zero_Key,
      V       => (T      => R.C.Ceiling_T,
                  Author => Signer_Key (R),
                  Seq    => R.C.Gen,
                  H      => To_Key256 (Hash (R.C))),
      Issuer  => Signer_Key (R),
      Del_TTL => R.C.Del_TTL);

   --  D3: the header is canonical once del_ttl is in the clamp (which
   --  Well_Formed requires).
   procedure Lemma_Header_Canonical (R : Roster_Record) with
     Ghost, Global => null,
     Pre  => R.C.Del_TTL in Del_TTL_Min .. Del_TTL_Max,
     Post => To_Header (R).K = K_Roster and then Kome.Headers.Canonical (To_Header (R));

   procedure Lemma_Decode_Encode (R : Roster_Record) with
     Ghost, Global => null,
     Pre  => Canonical (R),
     Post => Is_Roster_Frame (Encode (R)) and then Parse_Roster (Encode (R)) = R;

   procedure Lemma_Encode_Decode_Roster (Frame : Byte_Array) with
     Ghost, Global => null,
     Pre  => Is_Roster_Frame (Frame),
     Post => Encode (Parse_Roster (Frame)) = Frame;

   ---------------------------------------------------------------------------
   --  REVOKE  ns[16] root_pk[32] salt[16] SIGNER sign_pk[32] from_t:u48
   --          rev_seq:u48
   --  sign_pk is the subject (the key revoked); signer is the issuing root.
   ---------------------------------------------------------------------------

   type Revoke_Content is record
      NS       : NS_Id     := [others => 0];
      Root_PK  : Pubkey    := [others => 0];   --  founding key (ns)
      Salt     : Kome.Salt := [others => 0];
      Signer   : Pubkey    := [others => 0];   --  issuing root
      Cert_Cap : U48       := 0;
      Cert_Sig : Sig       := [others => 0];
      Sign_PK  : Pubkey    := [others => 0];   --  subject
      From_T   : U48       := 0;
      Rev_Seq  : U48       := 0;
   end record;

   type Revoke_Record is record
      C         : Revoke_Content;
      Signature : Sig := [others => 0];
   end record;

   Revoke_O_NS       : constant := 1;
   Revoke_O_Root_PK  : constant := 17;
   Revoke_O_Salt     : constant := 49;
   Revoke_O_Signer   : constant := 65;
   Revoke_O_Cert_Cap : constant := 97;
   Revoke_O_Cert_Sig : constant := 103;
   Revoke_O_Sign_PK  : constant := 167;
   Revoke_O_From_T   : constant := 199;
   Revoke_O_Rev_Seq  : constant := 205;
   Revoke_Content_Len : constant := 211;
   Revoke_Frame_Len   : constant := Revoke_Content_Len + Sig_Len;
   pragma Compile_Time_Error
     (Revoke_Frame_Len /= 275, "DESIGN.md §2: a REVOKE frame is 275 bytes");

   function Content_Byte (C : Revoke_Content; J : Natural) return Byte is
     (if J = 0 then Tag_Revoke
      elsif J < Revoke_O_Root_PK then C.NS (J - Revoke_O_NS)
      elsif J < Revoke_O_Salt then C.Root_PK (J - Revoke_O_Root_PK)
      elsif J < Revoke_O_Signer then C.Salt (J - Revoke_O_Salt)
      elsif J < Revoke_O_Cert_Cap then C.Signer (J - Revoke_O_Signer)
      elsif J < Revoke_O_Cert_Sig then Byte_Of_U48 (C.Cert_Cap, J - Revoke_O_Cert_Cap)
      elsif J < Revoke_O_Sign_PK then C.Cert_Sig (J - Revoke_O_Cert_Sig)
      elsif J < Revoke_O_From_T then C.Sign_PK (J - Revoke_O_Sign_PK)
      elsif J < Revoke_O_Rev_Seq then Byte_Of_U48 (C.From_T, J - Revoke_O_From_T)
      else Byte_Of_U48 (C.Rev_Seq, J - Revoke_O_Rev_Seq))
     with Pre => J < Revoke_Content_Len;

   function Frame_Byte (R : Revoke_Record; J : Natural) return Byte is
     (if J < Revoke_Content_Len then Content_Byte (R.C, J)
      else R.Signature (J - Revoke_Content_Len))
     with Pre => J < Revoke_Frame_Len;

   --  A REVOKE with ns derived from (root_pk, salt) and a zero signature.
   function Make_Revoke
     (Root_PK  : Pubkey;
      S        : Salt;
      Signer   : Pubkey;
      Cert_Cap : U48;
      Cert_Sig : Sig;
      Sign_PK  : Pubkey;
      From_T   : U48;
      Rev_Seq  : U48) return Revoke_Record
   with Global => null,
        Post => Make_Revoke'Result.C.NS = Collection_Id (Root_PK, S)
          and then Make_Revoke'Result.C.Root_PK = Root_PK
          and then Make_Revoke'Result.C.Salt = S
          and then Make_Revoke'Result.C.Signer = Signer
          and then Make_Revoke'Result.C.Cert_Cap = Cert_Cap
          and then Make_Revoke'Result.C.Cert_Sig = Cert_Sig
          and then Make_Revoke'Result.C.Sign_PK = Sign_PK
          and then Make_Revoke'Result.C.From_T = From_T
          and then Make_Revoke'Result.C.Rev_Seq = Rev_Seq
          and then (for all I in Sig'Range => Make_Revoke'Result.Signature (I) = 0);

   function Content_Bytes (C : Revoke_Content) return Byte_Array
   with Global => null,
        Post => Content_Bytes'Result'First = 0
          and then Content_Bytes'Result'Length = Revoke_Content_Len
          and then (for all J in 0 .. Revoke_Content_Len - 1 =>
                      Content_Bytes'Result (J) = Content_Byte (C, J));

   function Hash (C : Revoke_Content) return Hash256 is
     (Kome.Crypto.Blake2b_256 (Content_Bytes (C)));

   function Encode (R : Revoke_Record) return Byte_Array
   with Global => null,
        Post => Encode'Result'First = 0
          and then Encode'Result'Length = Revoke_Frame_Len
          and then (for all J in 0 .. Revoke_Frame_Len - 1 =>
                      Encode'Result (J) = Frame_Byte (R, J))
          and then Encode'Result (0 .. Revoke_Content_Len - 1) = Content_Bytes (R.C)
          and then Encode'Result (Revoke_Content_Len .. Revoke_Frame_Len - 1) = R.Signature;

   function Is_Revoke_Frame (Frame : Byte_Array) return Boolean is
     (Frame'Length = Revoke_Frame_Len and then Frame (Frame'First) = Tag_Revoke);

   function Parse_Revoke (Frame : Byte_Array) return Revoke_Record
   with Global => null,
        Pre  => Is_Revoke_Frame (Frame),
        Post => Parse_Revoke'Result.C.Cert_Cap =
                  U48_At (Frame, Frame'First + Revoke_O_Cert_Cap)
          and then Parse_Revoke'Result.C.From_T =
                     U48_At (Frame, Frame'First + Revoke_O_From_T)
          and then Parse_Revoke'Result.C.Rev_Seq =
                     U48_At (Frame, Frame'First + Revoke_O_Rev_Seq)
          and then (for all I in NS_Id'Range =>
                      Parse_Revoke'Result.C.NS (I) = Frame (Frame'First + Revoke_O_NS + I))
          and then (for all I in Pubkey'Range =>
                      Parse_Revoke'Result.C.Root_PK (I) =
                        Frame (Frame'First + Revoke_O_Root_PK + I))
          and then (for all I in Salt'Range =>
                      Parse_Revoke'Result.C.Salt (I) = Frame (Frame'First + Revoke_O_Salt + I))
          and then (for all I in Pubkey'Range =>
                      Parse_Revoke'Result.C.Signer (I) =
                        Frame (Frame'First + Revoke_O_Signer + I))
          and then (for all I in Sig'Range =>
                      Parse_Revoke'Result.C.Cert_Sig (I) =
                        Frame (Frame'First + Revoke_O_Cert_Sig + I))
          and then (for all I in Pubkey'Range =>
                      Parse_Revoke'Result.C.Sign_PK (I) =
                        Frame (Frame'First + Revoke_O_Sign_PK + I))
          and then (for all I in Sig'Range =>
                      Parse_Revoke'Result.Signature (I) =
                        Frame (Frame'First + Revoke_Content_Len + I));

   procedure Decode (Frame : Byte_Array; R : in out Revoke_Record; Result : out Status)
   with Global => null,
        Post => (if Is_Revoke_Frame (Frame)
                 then Result = OK and then R = Parse_Revoke (Frame)
                 else Result = Malformed and then R = R'Old);

   --  Well-formed (DESIGN.md §2 items 2, 4, 5): ns matches (root_pk, salt),
   --  the signer block is valid, the founding key is never the subject
   --  (D2), and the signature over h verifies under signer.
   function Well_Formed (R : Revoke_Record) return Boolean is
     (R.C.NS = Collection_Id (R.C.Root_PK, R.C.Salt)
      and then Cert_OK (R.C.Root_PK, R.C.NS, R.C.Signer, R.C.Cert_Cap, R.C.Cert_Sig)
      and then R.C.Sign_PK /= R.C.Root_PK
      and then Kome.Crypto.Verify (R.Signature, R.C.Signer, Hash (R.C)));

   procedure Decode_Verified
     (Frame : Byte_Array; R : in out Revoke_Record; Result : out Status)
   with Global => null,
        Post => (if Is_Revoke_Frame (Frame) and then Well_Formed (Parse_Revoke (Frame))
                 then Result = OK and then R = Parse_Revoke (Frame)
                 else Result = Malformed and then R = R'Old);

   procedure Sign (R : in out Revoke_Record; SK : Kome.Crypto.Secret_Key)
   with Global => null,
        Pre  => Kome.Crypto.Is_Valid (SK)
                and then Kome.Crypto.Public_Of (SK) = R.C.Signer,
        Post => R.C = R'Old.C
          and then R.Signature = Kome.Crypto.Sign (SK, Hash (R'Old.C))
          and then Hash (R.C) = Hash (R'Old.C);

   --  The issuing root (the header's Issuer; V.Author is the subject).
   function Signer_Key (R : Revoke_Record) return Key256 is
     (To_Key256 (R.C.Signer));

   --  DESIGN.md §3: V = (from_t, sign_pk, rev_seq, h); Issuer = signer.
   function To_Header (R : Revoke_Record) return Header is
     (K       => K_Revoke,
      NS      => To_Id128 (R.C.NS),
      Ent     => Zero_Id,
      FH      => Zero_Key,
      V       => (T      => R.C.From_T,
                  Author => To_Key256 (R.C.Sign_PK),
                  Seq    => R.C.Rev_Seq,
                  H      => To_Key256 (Hash (R.C))),
      Issuer  => Signer_Key (R),
      Del_TTL => 0);

   procedure Lemma_Header_Canonical (R : Revoke_Record) with
     Ghost, Global => null,
     Post => To_Header (R).K = K_Revoke and then Kome.Headers.Canonical (To_Header (R));

   procedure Lemma_Decode_Encode (R : Revoke_Record) with
     Ghost, Global => null,
     Post => Is_Revoke_Frame (Encode (R)) and then Parse_Revoke (Encode (R)) = R;

   procedure Lemma_Encode_Decode_Revoke (Frame : Byte_Array) with
     Ghost, Global => null,
     Pre  => Is_Revoke_Frame (Frame),
     Post => Encode (Parse_Revoke (Frame)) = Frame;

   ---------------------------------------------------------------------------
   --  GRANT   ns[16] root_pk[32] salt[16] SIGNER subject[32]
   --  Write access (D1′): the subject may author PUTs and DELs. Keyed by
   --  (ns, issuer, subject) (R1).
   ---------------------------------------------------------------------------

   type Grant_Content is record
      NS       : NS_Id     := [others => 0];
      Root_PK  : Pubkey    := [others => 0];   --  founding key (ns)
      Salt     : Kome.Salt := [others => 0];
      Signer   : Pubkey    := [others => 0];   --  issuing root
      Cert_Cap : U48       := 0;
      Cert_Sig : Sig       := [others => 0];
      Subject  : Pubkey    := [others => 0];   --  the key granted
   end record;

   type Grant_Record is record
      C         : Grant_Content;
      Signature : Sig := [others => 0];
   end record;

   Grant_O_NS       : constant := 1;
   Grant_O_Root_PK  : constant := 17;
   Grant_O_Salt     : constant := 49;
   Grant_O_Signer   : constant := 65;
   Grant_O_Cert_Cap : constant := 97;
   Grant_O_Cert_Sig : constant := 103;
   Grant_O_Subject  : constant := 167;
   Grant_Content_Len : constant := 199;
   Grant_Frame_Len   : constant := Grant_Content_Len + Sig_Len;
   pragma Compile_Time_Error
     (Grant_Frame_Len /= 263, "DESIGN.md §2: a GRANT frame is 263 bytes");

   function Content_Byte (C : Grant_Content; J : Natural) return Byte is
     (if J = 0 then Tag_Grant
      elsif J < Grant_O_Root_PK then C.NS (J - Grant_O_NS)
      elsif J < Grant_O_Salt then C.Root_PK (J - Grant_O_Root_PK)
      elsif J < Grant_O_Signer then C.Salt (J - Grant_O_Salt)
      elsif J < Grant_O_Cert_Cap then C.Signer (J - Grant_O_Signer)
      elsif J < Grant_O_Cert_Sig then Byte_Of_U48 (C.Cert_Cap, J - Grant_O_Cert_Cap)
      elsif J < Grant_O_Subject then C.Cert_Sig (J - Grant_O_Cert_Sig)
      else C.Subject (J - Grant_O_Subject))
     with Pre => J < Grant_Content_Len;

   function Frame_Byte (R : Grant_Record; J : Natural) return Byte is
     (if J < Grant_Content_Len then Content_Byte (R.C, J)
      else R.Signature (J - Grant_Content_Len))
     with Pre => J < Grant_Frame_Len;

   --  A GRANT with ns derived from (root_pk, salt) and a zero signature.
   function Make_Grant
     (Root_PK  : Pubkey;
      S        : Salt;
      Signer   : Pubkey;
      Cert_Cap : U48;
      Cert_Sig : Sig;
      Subject  : Pubkey) return Grant_Record
   with Global => null,
        Post => Make_Grant'Result.C.NS = Collection_Id (Root_PK, S)
          and then Make_Grant'Result.C.Root_PK = Root_PK
          and then Make_Grant'Result.C.Salt = S
          and then Make_Grant'Result.C.Signer = Signer
          and then Make_Grant'Result.C.Cert_Cap = Cert_Cap
          and then Make_Grant'Result.C.Cert_Sig = Cert_Sig
          and then Make_Grant'Result.C.Subject = Subject
          and then (for all I in Sig'Range => Make_Grant'Result.Signature (I) = 0);

   function Content_Bytes (C : Grant_Content) return Byte_Array
   with Global => null,
        Post => Content_Bytes'Result'First = 0
          and then Content_Bytes'Result'Length = Grant_Content_Len
          and then (for all J in 0 .. Grant_Content_Len - 1 =>
                      Content_Bytes'Result (J) = Content_Byte (C, J));

   function Hash (C : Grant_Content) return Hash256 is
     (Kome.Crypto.Blake2b_256 (Content_Bytes (C)));

   function Encode (R : Grant_Record) return Byte_Array
   with Global => null,
        Post => Encode'Result'First = 0
          and then Encode'Result'Length = Grant_Frame_Len
          and then (for all J in 0 .. Grant_Frame_Len - 1 =>
                      Encode'Result (J) = Frame_Byte (R, J))
          and then Encode'Result (0 .. Grant_Content_Len - 1) = Content_Bytes (R.C)
          and then Encode'Result (Grant_Content_Len .. Grant_Frame_Len - 1) = R.Signature;

   function Is_Grant_Frame (Frame : Byte_Array) return Boolean is
     (Frame'Length = Grant_Frame_Len and then Frame (Frame'First) = Tag_Grant);

   function Parse_Grant (Frame : Byte_Array) return Grant_Record
   with Global => null,
        Pre  => Is_Grant_Frame (Frame),
        Post => Parse_Grant'Result.C.Cert_Cap =
                  U48_At (Frame, Frame'First + Grant_O_Cert_Cap)
          and then (for all I in NS_Id'Range =>
                      Parse_Grant'Result.C.NS (I) = Frame (Frame'First + Grant_O_NS + I))
          and then (for all I in Pubkey'Range =>
                      Parse_Grant'Result.C.Root_PK (I) =
                        Frame (Frame'First + Grant_O_Root_PK + I))
          and then (for all I in Salt'Range =>
                      Parse_Grant'Result.C.Salt (I) = Frame (Frame'First + Grant_O_Salt + I))
          and then (for all I in Pubkey'Range =>
                      Parse_Grant'Result.C.Signer (I) =
                        Frame (Frame'First + Grant_O_Signer + I))
          and then (for all I in Sig'Range =>
                      Parse_Grant'Result.C.Cert_Sig (I) =
                        Frame (Frame'First + Grant_O_Cert_Sig + I))
          and then (for all I in Pubkey'Range =>
                      Parse_Grant'Result.C.Subject (I) =
                        Frame (Frame'First + Grant_O_Subject + I))
          and then (for all I in Sig'Range =>
                      Parse_Grant'Result.Signature (I) =
                        Frame (Frame'First + Grant_Content_Len + I));

   procedure Decode (Frame : Byte_Array; R : in out Grant_Record; Result : out Status)
   with Global => null,
        Post => (if Is_Grant_Frame (Frame)
                 then Result = OK and then R = Parse_Grant (Frame)
                 else Result = Malformed and then R = R'Old);

   --  Well-formed (DESIGN.md §2 items 2, 5): ns matches (root_pk, salt),
   --  the signer block is valid, and the signature over h verifies under
   --  signer.
   function Well_Formed (R : Grant_Record) return Boolean is
     (R.C.NS = Collection_Id (R.C.Root_PK, R.C.Salt)
      and then Cert_OK (R.C.Root_PK, R.C.NS, R.C.Signer, R.C.Cert_Cap, R.C.Cert_Sig)
      and then Kome.Crypto.Verify (R.Signature, R.C.Signer, Hash (R.C)));

   procedure Decode_Verified
     (Frame : Byte_Array; R : in out Grant_Record; Result : out Status)
   with Global => null,
        Post => (if Is_Grant_Frame (Frame) and then Well_Formed (Parse_Grant (Frame))
                 then Result = OK and then R = Parse_Grant (Frame)
                 else Result = Malformed and then R = R'Old);

   procedure Sign (R : in out Grant_Record; SK : Kome.Crypto.Secret_Key)
   with Global => null,
        Pre  => Kome.Crypto.Is_Valid (SK)
                and then Kome.Crypto.Public_Of (SK) = R.C.Signer,
        Post => R.C = R'Old.C
          and then R.Signature = Kome.Crypto.Sign (SK, Hash (R'Old.C))
          and then Hash (R.C) = Hash (R'Old.C);

   --  The issuing root (the header's Issuer; V.Author is the subject).
   function Signer_Key (R : Grant_Record) return Key256 is
     (To_Key256 (R.C.Signer));

   --  DESIGN.md §3: V = (0, subject, 0, h); Issuer = signer.
   function To_Header (R : Grant_Record) return Header is
     (K       => K_Grant,
      NS      => To_Id128 (R.C.NS),
      Ent     => Zero_Id,
      FH      => Zero_Key,
      V       => (T      => 0,
                  Author => To_Key256 (R.C.Subject),
                  Seq    => 0,
                  H      => To_Key256 (Hash (R.C))),
      Issuer  => Signer_Key (R),
      Del_TTL => 0);

   procedure Lemma_Header_Canonical (R : Grant_Record) with
     Ghost, Global => null,
     Post => To_Header (R).K = K_Grant and then Kome.Headers.Canonical (To_Header (R));

   procedure Lemma_Decode_Encode (R : Grant_Record) with
     Ghost, Global => null,
     Post => Is_Grant_Frame (Encode (R)) and then Parse_Grant (Encode (R)) = R;

   procedure Lemma_Encode_Decode_Grant (Frame : Byte_Array) with
     Ghost, Global => null,
     Pre  => Is_Grant_Frame (Frame),
     Post => Encode (Parse_Grant (Frame)) = Frame;

   ---------------------------------------------------------------------------
   --  Frame accessors for Kome.Store and the transport (bytes only).
   ---------------------------------------------------------------------------

   --  The frame is an authorization record of some kind.
   function Is_Auth_Frame (Frame : Byte_Array) return Boolean is
     (Is_Roster_Frame (Frame) or else Is_Revoke_Frame (Frame)
      or else Is_Grant_Frame (Frame));

   --  The root_pk field (offset 17) as a key. Kome.Store refuses an
   --  authorization record whose Root_Key_Of is not the store's founding key
   --  (DESIGN.md §7 step 0).
   function Root_Key_Of (Frame : Byte_Array) return Key256 is
     (To_Key256 (Frame (Frame'First + Roster_O_Root_PK
                        .. Frame'First + Roster_O_Root_PK + Pubkey_Len - 1)))
     with Pre  => Is_Auth_Frame (Frame),
          Post => (if Is_Roster_Frame (Frame)
                   then Root_Key_Of'Result = To_Key256 (Parse_Roster (Frame).C.Root_PK))
                  and then (if Is_Revoke_Frame (Frame)
                            then Root_Key_Of'Result =
                                   To_Key256 (Parse_Revoke (Frame).C.Root_PK))
                  and then (if Is_Grant_Frame (Frame)
                            then Root_Key_Of'Result =
                                   To_Key256 (Parse_Grant (Frame).C.Root_PK));

   --  Some member of the ROSTER frame has dh_pk = DH (the credential HELLO
   --  of DESIGN.md §8 must list the sender's Noise key). Opaque
   --  (quantified); its meaning is Lemma_Roster_Lists_DH.
   function Roster_Lists_DH (Frame : Byte_Array; DH : Pubkey) return Boolean
     with Global => null, Pre => Is_Roster_Frame (Frame);

   procedure Lemma_Roster_Lists_DH (Frame : Byte_Array; DH : Pubkey) with
     Ghost, Global => null,
     Pre  => Is_Roster_Frame (Frame),
     Post => Roster_Lists_DH (Frame, DH) =
               (for some I in 1 .. Parse_Roster (Frame).C.N_Members =>
                  Member_DH_PK (Parse_Roster (Frame).C, I) = DH);

   --  A REVOKE issued by the founding key (signer = root_pk): a root
   --  revocation candidate, the records OPEN carries (DESIGN.md §8, R2).
   function Is_Founding_Revoke (Frame : Byte_Array) return Boolean is
     (Is_Revoke_Frame (Frame)
      and then Parse_Revoke (Frame).C.Signer = Parse_Revoke (Frame).C.Root_PK);

private

   function Canonical (R : Put_Record) return Boolean is
     ((for all I in Field_Bytes'Range => (if I >= R.C.FLen then R.C.Field (I) = 0))
      and then
      (for all I in Value_Bytes'Range => (if I >= R.C.VLen then R.C.Value (I) = 0)));

   function Canonical (R : Roster_Record) return Boolean is
     ((for all I in Links_Bytes'Range =>
         (if I >= Link_Len * R.C.N_Links then R.C.Links (I) = 0))
      and then
      (for all I in Members_Bytes'Range =>
         (if I >= Member_Len * R.C.N_Members then R.C.Members (I) = 0)));

   function Link_Nonce (C : Roster_Content; I : Link_Index) return Nonce is
     ([for K in Nonce'Range => C.Links (Link_Len * (I - 1) + 2 + K)]);

   function Link_Box (C : Roster_Content; I : Link_Index) return Box is
     ([for K in Box'Range => C.Links (Link_Len * (I - 1) + 2 + Nonce_Len + K)]);

   function Member_Sign_PK (C : Roster_Content; I : Member_Index) return Pubkey is
     ([for K in Pubkey'Range => C.Members (Member_Len * (I - 1) + K)]);

   function Member_DH_PK (C : Roster_Content; I : Member_Index) return Pubkey is
     ([for K in Pubkey'Range => C.Members (Member_Len * (I - 1) + Pubkey_Len + K)]);

   function Member_Nonce (C : Roster_Content; I : Member_Index) return Nonce is
     ([for K in Nonce'Range => C.Members (Member_Len * (I - 1) + 2 * Pubkey_Len + K)]);

   function Member_Box (C : Roster_Content; I : Member_Index) return Box is
     ([for K in Box'Range =>
         C.Members (Member_Len * (I - 1) + 2 * Pubkey_Len + Nonce_Len + K)]);

   function DH_Keys_OK (C : Roster_Content) return Boolean is
     (Kome.Crypto.Is_Good_DH_Key (C.Box_PK)
      and then (for all I in 1 .. C.N_Members =>
                  Kome.Crypto.Is_Good_DH_Key (Member_DH_PK (C, I))));

   --  Member I's dh_pk read straight from a ROSTER frame.
   function Frame_DH (Frame : Byte_Array; I : Member_Index) return Pubkey is
     ([for K in Pubkey'Range =>
         Frame (Frame'First + Roster_O_Members (Roster_NL (Frame))
                + Member_Len * (I - 1) + Pubkey_Len + K)])
     with Pre => Is_Roster_Frame (Frame) and then I <= Roster_NM (Frame);

   function Roster_Lists_DH (Frame : Byte_Array; DH : Pubkey) return Boolean is
     (for some I in 1 .. Roster_NM (Frame) => Frame_DH (Frame, I) = DH);

end Kome.Records;
