--  Kome.Records: the canonical encoding, hashing, signing and
--  well-formedness of records (DESIGN.md §2 "Records" as SIMPLIFY.md §2
--  restates it; T13 "every emitted record satisfies the §2 layout"). This
--  package is the wire and crypto boundary. The records here hold bytes.
--  To_Header changes them into the word records of the lattice
--  (Kome.Headers.Header, Id128 / Key256 through Kome.Keys).
--
--  The layout is SIMPLIFY.md §2 (S1, S3, S4). All integers are big-endian.
--  Labels are ASCII with no terminator:
--
--    tag 0  ROSTER  SIGNER box_pk[32] gen:u48 ceiling_t:u48
--                   n_members:u8 (<= 64) members[n_members]
--                                        { sign_pk[32] dh_pk[32] nonce[24] box[48] }
--    tag 1  REVOKE  SIGNER sign_pk[32] from_t:u48                    (205 B)
--    tag 2  GRANT   SIGNER subject[32]                               (199 B)
--    tag 3  DEL     ent[16] t:u48 seq:u48 author[32]                 (125 B)
--    tag 4  PUT     ent[16] flen:u8 field[flen] t:u48 seq:u48
--                   author[32] vlen:u16 value[vlen]   (vlen <= 40 960)
--
--    SIGNER = signer[32] cert_cap:u48 cert_sig[64]
--
--  A frame is  tag:u8 ‖ content ‖ sig[64]. For every kind, h = BLAKE2b-256
--  (tag ‖ cid ‖ content) (S1), where cid = BLAKE2b-256 (root_pk ‖ salt ‖
--  u48 (del_ttl)) is the collection context (Cid_Of). No frame carries ns,
--  root_pk or salt: the cid is implicit, the verifier supplies it (from the
--  store, the session or the bundle), and the frame bytes do not contain
--  it. So every function that reads h (Hash, To_Header, Well_Formed,
--  Decode_Verified, Sign, Make_*) takes the cid as its first parameter;
--  Parse, Decode and Encode do not. ns = cid[0:16] (NS_Of) is the routing
--  identifier only (Noise prologue, bundle header, file names).
--  sig = Ed25519 (RFC 8032, D4) over the 32 bytes of h, so every signature
--  binds the cid through h. The author signs a PUT or a DEL. The signer
--  signs a ROSTER, a REVOKE or a GRANT. The tag is the reconciliation-order
--  code of the Kind (Kome.Headers.Kind'Pos).
--
--  Roots (D1, S3). root_pk is the founding key of the collection; it is in
--  the cid, and the verifier supplies it with the cid (Well_Formed and
--  Decode_Verified of an authorization kind take Cid, then Root_PK). Every
--  authorization record names its signer and carries a certificate from
--  the founding key: cert_sig = Ed25519 (root_sk, Cert_Hash), Cert_Hash =
--  BLAKE2b-256 ("kome/root" ‖ cid ‖ signer ‖ u48 (cert_cap)). The founding
--  key self-certifies with cert_cap = 2^48 - 1 (Founding_Cap). There is no
--  zero-certificate case and no sentinel: every signer is checked the same
--  way (Cert_OK), a ROSTER must not set ceiling_t above cert_cap, and the
--  write cap of a GRANT is its issuer's cert_cap. Only the founding key can
--  certify, so only the founding key adds roots, and admission needs no
--  history. It is not possible to narrow a certificate: every certificate
--  that the founding key issued stays valid. Only root-voiding (§6, a view)
--  ends what a certificate allows.
--
--  Each kind has a content record (the hashed part) and a record (the
--  content and the signature). The signature is outside the content. So
--  "Sign does not change h" is a congruence that the prover sees (the Post
--  of Sign).
--
--  What is proved, for each kind (T13):
--    * The length of Encode is the layout (Frame_Len). Every byte of the
--      frame is Frame_Byte, the layout read position by position. The
--      frame without its signature is Content_Bytes. Hash hashes it, with
--      the cid after the tag (Hash_Input).
--    * Decode accepts exactly the frames that Is_<Kind>_Frame describes
--      (exact length, tag, flen in 1..32, vlen <= 40 960, n_members <= 64).
--      Decode never reads out of bounds. On success, it returns
--      Parse_<Kind>. On failure, it does not change the record.
--    * Lemma_Decode_Encode: Parse (Encode (R)) = R for every canonical R.
--      So Decode (Encode (R)) returns OK and R.
--    * Lemma_Encode_Decode_<Kind>: Encode (Parse (B)) = B for every
--      accepted B. Each record has exactly one encoding, so h is a function
--      of the record and of the cid (with A2, h is then injective on
--      records, and a record's h differs between two collections).
--    * Lemma_Header_Canonical: To_Header (Cid, R) is a canonical header
--      (Kome.Headers.Canonical, D3). For a ROSTER, this needs gen <=
--      ceiling_t, and Well_Formed implies that. So decode makes only
--      canonical headers.
--    * Decode_Verified accepts exactly the well-formed frames (DESIGN.md §2
--      items 1-5). It checks the shape, the signer's certificate, the
--      certified ceiling, gen <= ceiling_t and the X25519 keys (E5). It also
--      checks that a REVOKE never names root_pk, that the root_pk it is
--      given and every signer, GRANT subject, REVOKE subject and ROSTER
--      member sign_pk is a canonical point, not a small-order point and not
--      the key of the all-zero seed (Sign_Key_OK; AUDIT.md H13, A27), that
--      box_pk is not the key of the all-zero X25519 secret, and it checks
--      the signature. It does not check del_ttl: del_ttl is in the cid, and
--      Kome.Store checks the HEADER's value against [Del_TTL_Min,
--      Del_TTL_Max] (S2).
--  Not proved: any property of BLAKE2b or Ed25519. Blake2b_256, Sign and
--  Verify of Kome.Crypto are opaque functions. Well_Formed calls Verify,
--  and no theorem here depends on the result of Verify.
--
--  Canonical form: unused field, value and member bytes are zero. On
--  canonical records, Ada equality is equality of content. A record with
--  nonzero padding is not Ada-equal to its canonical twin, but it has the
--  same content. So Encode and Sign require Canonical, and Well_Formed
--  includes it. Decode, the Make_* constructors and Sign make only
--  canonical records. (The record types stay public, so tests can build
--  malformed records. Hash and To_Header read only the used bytes.)
--  Canonical has a quantifier, so its completion is in the private part
--  (CONVENTIONS.md rule 2). Clients use the Posts of Parse_*, Make_* and
--  Sign.
pragma Ada_2022;
with Kome.Headers;  use Kome.Headers;
with Kome.Keys;     use Kome.Keys;
with Kome.Crypto;
package Kome.Records with SPARK_Mode, Preelaborate is

   ---------------------------------------------------------------------------
   --  Tags (one byte, the representation of the Kind; DESIGN.md §2 and the
   --  §8 key order).
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
   --  Big-endian integers (DESIGN.md §2 "all integers big-endian"). They
   --  use the word lanes of Kome.Keys, so the round trips can use its
   --  proved lemmas. u48 = hi:u16 ‖ lo:u32. Lane 0 is the most significant
   --  byte.
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

   --  cid = BLAKE2b-256 (root_pk ‖ salt ‖ u48 (del_ttl)), the collection
   --  context of every record (SIMPLIFY.md S1, S2). Kome.Store computes it
   --  once, at Open and Open_From_Log, from its HEADER.
   Cid_Input_Len : constant := Pubkey_Len + Salt_Len + 6;
   pragma Compile_Time_Error
     (Cid_Input_Len /= 54, "SIMPLIFY.md §2: the cid input is 54 bytes");
   subtype Cid_Input_Bytes is Byte_Array (0 .. Cid_Input_Len - 1);

   function Cid_Input
     (Root_PK : Pubkey; Salt : Kome.Salt; Del_TTL : U48) return Cid_Input_Bytes is
     (Root_PK & Salt
      & Byte_Array'(Byte_Of_U48 (Del_TTL, 0), Byte_Of_U48 (Del_TTL, 1),
                    Byte_Of_U48 (Del_TTL, 2), Byte_Of_U48 (Del_TTL, 3),
                    Byte_Of_U48 (Del_TTL, 4), Byte_Of_U48 (Del_TTL, 5)));

   function Cid_Of (Root_PK : Pubkey; Salt : Kome.Salt; Del_TTL : U48) return Hash256 is
     (Kome.Crypto.Blake2b_256 (Cid_Input (Root_PK, Salt, Del_TTL)));

   --  ns = cid[0:16], the routing identifier (S1): the Noise prologue, the
   --  bundle header and file names. No frame carries it, and nothing in
   --  this package checks it.
   function NS_Of (Cid : Hash256) return NS_Id is (Cid (0 .. NS_Len - 1));

   --  The hash input of every record: tag ‖ cid ‖ content, from TC = tag ‖
   --  content (Content_Bytes). The cid goes right after the tag.
   function Hash_Input (Cid : Hash256; TC : Byte_Array) return Byte_Array is
     (TC (TC'First .. TC'First) & Cid & TC (TC'First + 1 .. TC'Last))
     with Pre => TC'Length >= 1 and then TC'Last < Natural'Last - Hash_Len;

   --  No frame is longer than this: a PUT with a 32-byte field and a
   --  40 960-byte value, 160 + Value_Max = 41 120 bytes (D12, §2 table).
   --  No hashed content is longer than this minus 64 (plus the 32-byte cid
   --  in the hash input).
   Frame_Max : constant := 1 + 16 + 1 + 32 + 6 + 6 + 32 + 2 + Value_Max + Sig_Len;
   pragma Compile_Time_Error
     (Frame_Max /= 41_120, "SIMPLIFY.md §2: the largest frame is 41 120 bytes");

   Zero_Sig : constant Sig := [others => 0];

   --  A signing key that may be the founding key, a signer, a subject
   --  (GRANT, REVOKE) or a member sign_pk (ROSTER) (AUDIT.md H13, A27): a
   --  canonical point encoding (Kome.Crypto.Is_Canonical_Point, so that
   --  each key has one encoding and one lattice identity; Verify refuses a
   --  non-canonical key too), not one of the 8 small-order points (a GRANT
   --  to such a key, or a signer or root of that form, would let anybody
   --  forge records: Kome.Crypto.Verify refuses them, and so does this
   --  check, byte-locally, so that decode stays total and the refusal does
   --  not depend on a signature check), and not the public key of the
   --  all-zero seed (a secret that everybody knows). The function has no
   --  quantifier, so it is public. Cert_OK requires it of root_pk and of
   --  the signer, GRANT and REVOKE Well_Formed of the subject, and ROSTER
   --  of every member sign_pk (Member_Keys_OK). Make_Cert, Make_Grant,
   --  Make_Revoke and Make_Roster require it of every key they take (Pre).
   --  Kome.Store.Open requires it of the founding key.
   function Sign_Key_OK (PK : Pubkey) return Boolean is
     (Kome.Crypto.Is_Canonical_Point (PK)
      and then not Kome.Crypto.Is_Small_Order_Point (PK)
      and then not Kome.Crypto.Is_Zero_Seed_Public (PK))
     with Global => null;

   ---------------------------------------------------------------------------
   --  The signer block and root certificates (D1, S3).
   --    SIGNER = signer[32] cert_cap:u48 cert_sig[64]
   ---------------------------------------------------------------------------

   --  The cert_cap of the founding key's certificate of itself (S3): it has
   --  no cap.
   Founding_Cap : constant U48 := U48'Last;

   Cert_Label_Len : constant := 9;   --  "kome/root"
   Cert_Label     : constant Byte_Array (0 .. Cert_Label_Len - 1) :=
     [16#6B#, 16#6F#, 16#6D#, 16#65#, 16#2F#, 16#72#, 16#6F#, 16#6F#, 16#74#];
   Cert_Input_Len : constant := Cert_Label_Len + Hash_Len + Pubkey_Len + 6;
   pragma Compile_Time_Error
     (Cert_Input_Len /= 79, "SIMPLIFY.md §2: the certificate input is 79 bytes");
   subtype Cert_Input_Bytes is Byte_Array (0 .. Cert_Input_Len - 1);

   --  "kome/root" ‖ cid ‖ signer ‖ u48 (cap).
   function Cert_Input (Cid : Hash256; Signer : Pubkey; Cap : U48) return Cert_Input_Bytes is
     (Cert_Label & Cid & Signer
      & Byte_Array'(Byte_Of_U48 (Cap, 0), Byte_Of_U48 (Cap, 1), Byte_Of_U48 (Cap, 2),
                    Byte_Of_U48 (Cap, 3), Byte_Of_U48 (Cap, 4), Byte_Of_U48 (Cap, 5)));

   --  What the founding key signs to certify a signer (itself included).
   function Cert_Hash (Cid : Hash256; Signer : Pubkey; Cap : U48) return Hash256 is
     (Kome.Crypto.Blake2b_256 (Cert_Input (Cid, Signer, Cap)));

   --  The signer block is valid in the collection of (Cid, Root_PK): the
   --  founding key and the signer are usable keys (Sign_Key_OK, H13), and
   --  cert_sig is the founding key's signature over Cert_Hash (Cid, Signer,
   --  Cap). This holds for the founding key too (its own certificate, S3).
   function Cert_OK
     (Cid : Hash256; Root_PK : Pubkey; Signer : Pubkey; Cap : U48; Cert : Sig) return Boolean
   is (Sign_Key_OK (Root_PK)
       and then Sign_Key_OK (Signer)
       and then Kome.Crypto.Verify (Cert, Root_PK, Cert_Hash (Cid, Signer, Cap)));

   --  The certificate that the founding key issues for a signer (out of
   --  band, in a key ceremony; S3). The founding key certifies itself with
   --  Make_Cert (Founding, Cid, Public_Of (Founding), Founding_Cap). Pre
   --  (H13, A27): the certified key is usable, so the certificate is one
   --  that Cert_OK can accept.
   function Make_Cert
     (Founding : Kome.Crypto.Secret_Key; Cid : Hash256; Signer : Pubkey; Cap : U48) return Sig
   with Global => null,
        Pre  => Kome.Crypto.Is_Valid (Founding) and then Sign_Key_OK (Signer),
        Post => Make_Cert'Result = Kome.Crypto.Sign (Founding, Cert_Hash (Cid, Signer, Cap));

   ---------------------------------------------------------------------------
   --  PUT   ent[16] flen:u8 field[flen] t:u48 seq:u48 author[32]
   --        vlen:u16 value[vlen]
   ---------------------------------------------------------------------------

   subtype Field_Bytes is Byte_Array (0 .. Field_Max - 1);
   subtype Value_Bytes is Byte_Array (0 .. Value_Max - 1);

   type Put_Content is record
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
   Put_O_Ent   : constant := 1;
   Put_O_FLen  : constant := 17;
   Put_O_Field : constant := 18;
   Put_Fixed   : constant := 64;               --  tag + every fixed-width part
   Put_Frame_Min : constant := Put_Fixed + 1 + Sig_Len;
   Put_Frame_Max : constant := Put_Fixed + Field_Max + Value_Max + Sig_Len;
   pragma Compile_Time_Error
     (Put_Frame_Min /= 129 or else Put_Frame_Max /= Frame_Max,
      "SIMPLIFY.md §2: a PUT frame is 129 .. 41 120 bytes");

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

   --  Unused field and value bytes are zero. This function has a
   --  quantifier, so its completion is in the private part.
   function Canonical (R : Put_Record) return Boolean with Global => null;

   --  tag ‖ content, the frame without its signature.
   function Content_Bytes (C : Put_Content) return Byte_Array
   with Global => null,
        Post => Content_Bytes'Result'First = 0
          and then Content_Bytes'Result'Length = Content_Len (C)
          and then (for all J in 0 .. Content_Len (C) - 1 =>
                      Content_Bytes'Result (J) = Content_Byte (C, J));

   --  h = BLAKE2b-256 (tag ‖ cid ‖ content) (S1).
   function Hash (Cid : Hash256; C : Put_Content) return Hash256 is
     (Kome.Crypto.Blake2b_256 (Hash_Input (Cid, Content_Bytes (C))));

   --  The lattice header (Kome.Headers) in the collection of Cid:
   --  V = (t, author, seq, h), FH = BLAKE2b-256 (field name), no issuer.
   function To_Header (Cid : Hash256; R : Put_Record) return Header is
     (K       => K_Put,
      Ent     => To_Id128 (R.C.Ent),
      FH      => To_Key256 (Kome.Crypto.Blake2b_256 (R.C.Field (0 .. R.C.FLen - 1))),
      V       => (T      => R.C.T,
                  Author => To_Key256 (R.C.Author),
                  Seq    => R.C.Seq,
                  H      => To_Key256 (Hash (Cid, R.C))),
      Issuer  => Zero_Key);

   --  A canonical PUT with a zero signature (sign it with Sign). Cid is
   --  the collection context of its h; it is not stored in the record, and
   --  the Post gives the header under it.
   function Make_Put
     (Cid    : Hash256;
      Ent    : Ent_Id;
      Field  : Byte_Array;
      T, Seq : U48;
      Author : Pubkey;
      Value  : Byte_Array) return Put_Record
   with Global => null,
        Pre  => Field'Length in 1 .. Field_Max and then Value'Length <= Value_Max,
        Post => Canonical (Make_Put'Result)
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
          --  the write path builds the record from the (t, seq) that it
          --  chose, and h is the hash of the record). This is the
          --  To_Header (Tgt, Stamp (T, Author, Seq, h)) of Kome.Emit for
          --  Tgt = (K_Put, Ent, FH).
          and then To_Header (Cid, Make_Put'Result) =
                     (K       => K_Put,
                      Ent     => To_Id128 (Ent),
                      FH      => To_Key256 (Kome.Crypto.Blake2b_256 (Field)),
                      V       => (T      => T,
                                  Author => To_Key256 (Author),
                                  Seq    => Seq,
                                  H      => To_Key256 (Hash (Cid, Make_Put'Result.C))),
                      Issuer  => Zero_Key)
          and then Kome.Headers.Canonical (To_Header (Cid, Make_Put'Result));

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

   --  The shape that Decode accepts. These functions read flen and vlen
   --  only after the length check that makes their positions exist.
   function Put_FL (Frame : Byte_Array) return Natural is
     (Natural (Frame (Frame'First + Put_O_FLen)))
     with Pre => Frame'Length >= Put_Frame_Min;

   function Put_VL (Frame : Byte_Array) return U16_Value is
     (U16_At (Frame, Frame'First + Put_O_VLen (Put_FL (Frame))))
     with Pre => Frame'Length >= Put_Frame_Min and then Put_FL (Frame) in Field_Len;

   --  vlen stays a u16 on the wire. Decode refuses a value above Value_Max
   --  (40 960, D12) (§2 item 1).
   function Is_Put_Frame (Frame : Byte_Array) return Boolean is
     (Frame'Length >= Put_Frame_Min
      and then Frame'Length <= Put_Frame_Max
      and then Frame (Frame'First) = Tag_Put
      and then Put_FL (Frame) in Field_Len
      and then Put_VL (Frame) <= Value_Max
      and then Frame'Length = Put_Fixed + Sig_Len + Put_FL (Frame) + Put_VL (Frame));

   --  The record that an accepted frame encodes, field by field.
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

   --  Total over all byte strings. On refusal, R does not change.
   procedure Decode (Frame : Byte_Array; R : in out Put_Record; Result : out Status)
   with Global => null,
        Post => (if Is_Put_Frame (Frame)
                 then Result = OK and then R = Parse_Put (Frame)
                 else Result = Malformed and then R = R'Old);

   --  Well-formed in the collection of Cid (DESIGN.md §2): the bounds (by
   --  type), canonical padding, and the signature over h (which binds Cid)
   --  verifies under author.
   function Well_Formed (Cid : Hash256; R : Put_Record) return Boolean is
     (Canonical (R)
      and then Kome.Crypto.Verify (R.Signature, R.C.Author, Hash (Cid, R.C)));

   --  Decode, then refuse the record if it is not well-formed in the
   --  collection of Cid. On refusal, R does not change.
   procedure Decode_Verified
     (Cid : Hash256; Frame : Byte_Array; R : in out Put_Record; Result : out Status)
   with Global => null,
        Post => (if Is_Put_Frame (Frame) and then Well_Formed (Cid, Parse_Put (Frame))
                 then Result = OK and then R = Parse_Put (Frame)
                 else Result = Malformed and then R = R'Old);

   --  sig := Ed25519 (h) with the key of the author, h under Cid. Only the
   --  signature changes, so h and the header do not change.
   procedure Sign (Cid : Hash256; R : in out Put_Record; SK : Kome.Crypto.Secret_Key)
   with Global => null,
        Pre  => Canonical (R)
                and then Kome.Crypto.Is_Valid (SK)
                and then Kome.Crypto.Public_Of (SK) = R.C.Author,
        Post => Canonical (R)
          and then R.C = R'Old.C
          and then R.Signature = Kome.Crypto.Sign (SK, Hash (Cid, R'Old.C))
          and then Hash (Cid, R.C) = Hash (Cid, R'Old.C);

   --  D3: the header is canonical.
   procedure Lemma_Header_Canonical (Cid : Hash256; R : Put_Record) with
     Ghost, Global => null,
     Post => To_Header (Cid, R).K = K_Put
             and then Kome.Headers.Canonical (To_Header (Cid, R));

   --  Round trip (T13): Parse (Encode (R)) = R. So Decode (Encode (R))
   --  returns OK and R.
   procedure Lemma_Decode_Encode (R : Put_Record) with
     Ghost, Global => null,
     Pre  => Canonical (R),
     Post => Is_Put_Frame (Encode (R)) and then Parse_Put (Encode (R)) = R;

   --  The encoding is canonical: an accepted frame is the encoding of the
   --  record that it decodes to.
   procedure Lemma_Encode_Decode_Put (Frame : Byte_Array) with
     Ghost, Global => null,
     Pre  => Is_Put_Frame (Frame),
     Post => Encode (Parse_Put (Frame)) = Frame;

   ---------------------------------------------------------------------------
   --  DEL   ent[16] t:u48 seq:u48 author[32]
   ---------------------------------------------------------------------------

   type Del_Content is record
      Ent    : Ent_Id := [others => 0];
      T      : U48    := 0;
      Seq    : U48    := 0;
      Author : Pubkey := [others => 0];
   end record;

   type Del_Record is record
      C         : Del_Content;
      Signature : Sig := [others => 0];
   end record;

   Del_O_Ent    : constant := 1;
   Del_O_T      : constant := 17;
   Del_O_Seq    : constant := 23;
   Del_O_Author : constant := 29;
   Del_Content_Len : constant := 61;
   Del_Frame_Len   : constant := Del_Content_Len + Sig_Len;
   pragma Compile_Time_Error
     (Del_Frame_Len /= 125, "SIMPLIFY.md §2: a DEL frame is 125 bytes");

   function Content_Byte (C : Del_Content; J : Natural) return Byte is
     (if J = 0 then Tag_Del
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

   --  h = BLAKE2b-256 (tag ‖ cid ‖ content) (S1).
   function Hash (Cid : Hash256; C : Del_Content) return Hash256 is
     (Kome.Crypto.Blake2b_256 (Hash_Input (Cid, Content_Bytes (C))));

   --  The header in the collection of Cid: V = (t, author, seq, h). A DEL
   --  has no field (FH 0) and no issuer.
   function To_Header (Cid : Hash256; R : Del_Record) return Header is
     (K       => K_Del,
      Ent     => To_Id128 (R.C.Ent),
      FH      => Zero_Key,
      V       => (T      => R.C.T,
                  Author => To_Key256 (R.C.Author),
                  Seq    => R.C.Seq,
                  H      => To_Key256 (Hash (Cid, R.C))),
      Issuer  => Zero_Key);

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

   --  Well-formed in the collection of Cid: the signature over h (which
   --  binds Cid) verifies under author.
   function Well_Formed (Cid : Hash256; R : Del_Record) return Boolean is
     (Kome.Crypto.Verify (R.Signature, R.C.Author, Hash (Cid, R.C)));

   procedure Decode_Verified
     (Cid : Hash256; Frame : Byte_Array; R : in out Del_Record; Result : out Status)
   with Global => null,
        Post => (if Is_Del_Frame (Frame) and then Well_Formed (Cid, Parse_Del (Frame))
                 then Result = OK and then R = Parse_Del (Frame)
                 else Result = Malformed and then R = R'Old);

   procedure Sign (Cid : Hash256; R : in out Del_Record; SK : Kome.Crypto.Secret_Key)
   with Global => null,
        Pre  => Kome.Crypto.Is_Valid (SK)
                and then Kome.Crypto.Public_Of (SK) = R.C.Author,
        Post => R.C = R'Old.C
          and then R.Signature = Kome.Crypto.Sign (SK, Hash (Cid, R'Old.C))
          and then Hash (Cid, R.C) = Hash (Cid, R'Old.C);

   procedure Lemma_Header_Canonical (Cid : Hash256; R : Del_Record) with
     Ghost, Global => null,
     Post => To_Header (Cid, R).K = K_Del
             and then Kome.Headers.Canonical (To_Header (Cid, R));

   --  A DEL with a zero signature (sign it with Sign). This is the DEL
   --  counterpart of Make_Put, for step 2 of the write path (DESIGN.md §5).
   --  Its lattice header is the To_Header (Tgt, Stamp (T, Author, Seq, h))
   --  of Kome.Emit for Tgt = (K_Del, Ent, 0), where h is the hash of the
   --  record under the collection context Cid.
   function Make_Del
     (Cid    : Hash256;
      Ent    : Ent_Id;
      T, Seq : U48;
      Author : Pubkey) return Del_Record
   with Global => null,
        Post => Make_Del'Result.C.Ent = Ent
          and then Make_Del'Result.C.T = T
          and then Make_Del'Result.C.Seq = Seq
          and then Make_Del'Result.C.Author = Author
          and then (for all I in Sig'Range => Make_Del'Result.Signature (I) = 0)
          and then To_Header (Cid, Make_Del'Result) =
                     (K       => K_Del,
                      Ent     => To_Id128 (Ent),
                      FH      => Zero_Key,
                      V       => (T      => T,
                                  Author => To_Key256 (Author),
                                  Seq    => Seq,
                                  H      => To_Key256 (Hash (Cid, Make_Del'Result.C))),
                      Issuer  => Zero_Key)
          and then Kome.Headers.Canonical (To_Header (Cid, Make_Del'Result));

   procedure Lemma_Decode_Encode (R : Del_Record) with
     Ghost, Global => null,
     Post => Is_Del_Frame (Encode (R)) and then Parse_Del (Encode (R)) = R;

   procedure Lemma_Encode_Decode_Del (Frame : Byte_Array) with
     Ghost, Global => null,
     Pre  => Is_Del_Frame (Frame),
     Post => Encode (Parse_Del (Frame)) = Frame;

   ---------------------------------------------------------------------------
   --  ROSTER  SIGNER box_pk[32] gen:u48 ceiling_t:u48
   --          n_members:u8 members[n] { sign_pk[32] dh_pk[32] nonce[24] box[48] }
   --  The box of a member holds the roster's collection key k_g (S4,
   --  Kome.Epochs). The record keeps the members flat, as on the wire, so
   --  the encoding is a sequence of byte copies. The accessors below cut
   --  them into parts.
   ---------------------------------------------------------------------------

   Member_Len        : constant := Pubkey_Len + Pubkey_Len + Nonce_Len + Box_Len;  --  136
   Members_Bytes_Len : constant := Members_Max * Member_Len;

   subtype Member_Count  is Natural range 0 .. Members_Max;
   subtype Member_Index  is Positive range 1 .. Members_Max;
   subtype Members_Bytes is Byte_Array (0 .. Members_Bytes_Len - 1);

   type Roster_Content is record
      Signer    : Pubkey        := [others => 0];   --  issuing root
      Cert_Cap  : U48           := 0;
      Cert_Sig  : Sig           := [others => 0];
      Box_PK    : Pubkey        := [others => 0];   --  ephemeral X25519 (D5)
      Gen       : U48           := 0;
      Ceiling_T : U48           := 0;
      N_Members : Member_Count  := 0;
      Members   : Members_Bytes := [others => 0];   --  Members (0 .. 136 * N_Members - 1)
   end record;

   type Roster_Record is record
      C         : Roster_Content;
      Signature : Sig := [others => 0];
   end record;

   Roster_O_Signer   : constant := 1;
   Roster_O_Cert_Cap : constant := 33;
   Roster_O_Cert_Sig : constant := 39;
   Roster_O_Box_PK   : constant := 103;
   Roster_O_Gen      : constant := 135;
   Roster_O_Ceiling  : constant := 141;
   Roster_O_NM       : constant := 147;
   Roster_O_Members  : constant := 148;
   Roster_Fixed      : constant := 148;          --  tag + every fixed-width part
   Roster_Frame_Min  : constant := Roster_Fixed + Sig_Len;
   Roster_Frame_Max  : constant := Roster_Fixed + Members_Bytes_Len + Sig_Len;
   pragma Compile_Time_Error
     (Roster_Frame_Min /= 212 or else Roster_Frame_Max /= 8_916,
      "SIMPLIFY.md §2: a ROSTER frame is 212 .. 8 916 bytes");
   pragma Compile_Time_Error
     (Roster_Frame_Max > Frame_Max, "every ROSTER frame must fit Frame_Max");

   function Content_Len (C : Roster_Content) return Positive is
     (Roster_Fixed + Member_Len * C.N_Members);

   function Frame_Len (R : Roster_Record) return Positive is
     (Content_Len (R.C) + Sig_Len);

   function Content_Byte (C : Roster_Content; J : Natural) return Byte is
     (if J = 0 then Tag_Roster
      elsif J < Roster_O_Cert_Cap then C.Signer (J - Roster_O_Signer)
      elsif J < Roster_O_Cert_Sig then Byte_Of_U48 (C.Cert_Cap, J - Roster_O_Cert_Cap)
      elsif J < Roster_O_Box_PK then C.Cert_Sig (J - Roster_O_Cert_Sig)
      elsif J < Roster_O_Gen then C.Box_PK (J - Roster_O_Box_PK)
      elsif J < Roster_O_Ceiling then Byte_Of_U48 (C.Gen, J - Roster_O_Gen)
      elsif J < Roster_O_NM then Byte_Of_U48 (C.Ceiling_T, J - Roster_O_Ceiling)
      elsif J = Roster_O_NM then Byte (C.N_Members)
      else C.Members (J - Roster_O_Members))
     with Pre => J < Content_Len (C);

   function Frame_Byte (R : Roster_Record; J : Natural) return Byte is
     (if J < Content_Len (R.C) then Content_Byte (R.C, J)
      else R.Signature (J - Content_Len (R.C)))
     with Pre => J < Frame_Len (R);

   --  The parts of member I. The completions of the accessors are in the
   --  private part (each is a quantified aggregate, CONVENTIONS.md rule 2).
   --  Lemma_Member_Bytes gives their bytes.
   function Member_Sign_PK (C : Roster_Content; I : Member_Index) return Pubkey
     with Global => null, Pre => I <= C.N_Members;

   function Member_DH_PK (C : Roster_Content; I : Member_Index) return Pubkey
     with Global => null, Pre => I <= C.N_Members;

   function Member_Nonce (C : Roster_Content; I : Member_Index) return Nonce
     with Global => null, Pre => I <= C.N_Members;

   function Member_Box (C : Roster_Content; I : Member_Index) return Box
     with Global => null, Pre => I <= C.N_Members;

   --  The signing key of the member, as the lattice sees it.
   function Member_Key (C : Roster_Content; I : Member_Index) return Key256 is
     (To_Key256 (Member_Sign_PK (C, I)))
     with Pre => I <= C.N_Members;

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
   --  X25519 encoding and not low order (Kome.Crypto.Is_Good_DH_Key). So
   --  every listed member can open its box. This function has a
   --  quantifier, so its completion is in the private part.
   --  Lemma_DH_Keys_OK_Def gives its meaning. Lemma_DH_Box_OK and
   --  Lemma_DH_Keys_OK give it for one key at a time.
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

   --  DESIGN.md §2 item 4: every member sign_pk is a usable signing key
   --  (Sign_Key_OK: canonical, not small order, not the all-zero seed).
   --  This function has a quantifier, so its completion is in the private
   --  part. Lemma_Member_Keys_OK_Def gives its meaning, and
   --  Lemma_Member_Keys_OK gives it for one member.
   function Member_Keys_OK (C : Roster_Content) return Boolean with Global => null;

   procedure Lemma_Member_Keys_OK_Def (C : Roster_Content) with
     Ghost, Global => null,
     Post => Member_Keys_OK (C) =
               (for all I in 1 .. C.N_Members => Sign_Key_OK (Member_Sign_PK (C, I)));

   procedure Lemma_Member_Keys_OK (C : Roster_Content; I : Member_Index) with
     Ghost, Global => null,
     Pre  => Member_Keys_OK (C) and then I <= C.N_Members,
     Post => Sign_Key_OK (Member_Sign_PK (C, I));

   --  Unused member bytes are zero. This function has a quantifier, so its
   --  completion is in the private part.
   function Canonical (R : Roster_Record) return Boolean with Global => null;

   function Content_Bytes (C : Roster_Content) return Byte_Array
   with Global => null,
        Post => Content_Bytes'Result'First = 0
          and then Content_Bytes'Result'Length = Content_Len (C)
          and then (for all J in 0 .. Content_Len (C) - 1 =>
                      Content_Bytes'Result (J) = Content_Byte (C, J));

   --  h = BLAKE2b-256 (tag ‖ cid ‖ content) (S1).
   function Hash (Cid : Hash256; C : Roster_Content) return Hash256 is
     (Kome.Crypto.Blake2b_256 (Hash_Input (Cid, Content_Bytes (C))));

   --  The issuing root, as the lattice sees it (the Issuer of the header).
   function Signer_Key (R : Roster_Record) return Key256 is
     (To_Key256 (R.C.Signer));

   --  DESIGN.md §3: V = (ceiling_t, signer, gen, h); Issuer = signer; no
   --  entity, no field.
   function To_Header (Cid : Hash256; R : Roster_Record) return Header is
     (K       => K_Roster,
      Ent     => Zero_Id,
      FH      => Zero_Key,
      V       => (T      => R.C.Ceiling_T,
                  Author => Signer_Key (R),
                  Seq    => R.C.Gen,
                  H      => To_Key256 (Hash (Cid, R.C))),
      Issuer  => Signer_Key (R));

   --  A canonical ROSTER with a zero signature. Members are the flat wire
   --  bytes. Pre (H13, A27): the signer is a usable key, as Well_Formed
   --  requires. (Box_PK and the members are not checked here, so tests can
   --  build rosters that decode refuses.) Box_PK is Kome.Epochs.Box_PK_Of
   --  of the roster's key k_g and (cid, gen, signer), and each member box
   --  is from Kome.Epochs.Box_Key with the same inputs (A6, G7); this
   --  package does not check that.
   function Make_Roster
     (Cid       : Hash256;
      Signer    : Pubkey;
      Cert_Cap  : U48;
      Cert_Sig  : Sig;
      Box_PK    : Pubkey;
      Gen       : U48;
      Ceiling_T : U48;
      Members   : Byte_Array) return Roster_Record
   with Global => null,
        Pre  => Sign_Key_OK (Signer)
                and then Members'Length <= Members_Bytes_Len
                and then Members'Length mod Member_Len = 0,
        Post => Canonical (Make_Roster'Result)
          and then Make_Roster'Result.C.Signer = Signer
          and then Make_Roster'Result.C.Cert_Cap = Cert_Cap
          and then Make_Roster'Result.C.Cert_Sig = Cert_Sig
          and then Make_Roster'Result.C.Box_PK = Box_PK
          and then Make_Roster'Result.C.Gen = Gen
          and then Make_Roster'Result.C.Ceiling_T = Ceiling_T
          and then Make_Roster'Result.C.N_Members * Member_Len = Members'Length
          and then (for all I in 0 .. Members'Length - 1 =>
                      Make_Roster'Result.C.Members (I) = Members (Members'First + I))
          and then (for all I in Sig'Range => Make_Roster'Result.Signature (I) = 0)
          and then To_Header (Cid, Make_Roster'Result) =
                     (K      => K_Roster,
                      Ent    => Zero_Id,
                      FH     => Zero_Key,
                      V      => (T      => Ceiling_T,
                                 Author => To_Key256 (Signer),
                                 Seq    => Gen,
                                 H      => To_Key256 (Hash (Cid, Make_Roster'Result.C))),
                      Issuer => To_Key256 (Signer));

   function Encode (R : Roster_Record) return Byte_Array
   with Global => null,
        Pre  => Canonical (R),
        Post => Encode'Result'First = 0
          and then Encode'Result'Length = Frame_Len (R)
          and then (for all J in 0 .. Frame_Len (R) - 1 =>
                      Encode'Result (J) = Frame_Byte (R, J))
          and then Encode'Result (0 .. Content_Len (R.C) - 1) = Content_Bytes (R.C)
          and then Encode'Result (Content_Len (R.C) .. Frame_Len (R) - 1) = R.Signature;

   function Roster_NM (Frame : Byte_Array) return Natural is
     (Natural (Frame (Frame'First + Roster_O_NM)))
     with Pre => Frame'Length >= Roster_Frame_Min;

   function Is_Roster_Frame (Frame : Byte_Array) return Boolean is
     (Frame'Length >= Roster_Frame_Min
      and then Frame'Length <= Roster_Frame_Max
      and then Frame (Frame'First) = Tag_Roster
      and then Roster_NM (Frame) <= Members_Max
      and then Frame'Length = Roster_Frame_Min + Member_Len * Roster_NM (Frame));

   function Parse_Roster (Frame : Byte_Array) return Roster_Record
   with Global => null,
        Pre  => Is_Roster_Frame (Frame),
        Post => Canonical (Parse_Roster'Result)
          and then Parse_Roster'Result.C.Cert_Cap =
                     U48_At (Frame, Frame'First + Roster_O_Cert_Cap)
          and then Parse_Roster'Result.C.Gen = U48_At (Frame, Frame'First + Roster_O_Gen)
          and then Parse_Roster'Result.C.Ceiling_T =
                     U48_At (Frame, Frame'First + Roster_O_Ceiling)
          and then Parse_Roster'Result.C.N_Members = Roster_NM (Frame)
          and then (for all I in Pubkey'Range =>
                      Parse_Roster'Result.C.Signer (I) =
                        Frame (Frame'First + Roster_O_Signer + I))
          and then (for all I in Sig'Range =>
                      Parse_Roster'Result.C.Cert_Sig (I) =
                        Frame (Frame'First + Roster_O_Cert_Sig + I))
          and then (for all I in Pubkey'Range =>
                      Parse_Roster'Result.C.Box_PK (I) =
                        Frame (Frame'First + Roster_O_Box_PK + I))
          and then (for all I in Members_Bytes'Range =>
                      Parse_Roster'Result.C.Members (I) =
                        (if I < Member_Len * Roster_NM (Frame)
                         then Frame (Frame'First + Roster_O_Members + I)
                         else 0))
          and then (for all I in Sig'Range =>
                      Parse_Roster'Result.Signature (I) =
                        Frame (Frame'First + Roster_O_Members
                               + Member_Len * Roster_NM (Frame) + I));

   procedure Decode (Frame : Byte_Array; R : in out Roster_Record; Result : out Status)
   with Global => null,
        Post => (if Is_Roster_Frame (Frame)
                 then Result = OK and then R = Parse_Roster (Frame)
                 else Result = Malformed and then R = R'Old);

   --  Well-formed in the collection of (Cid, Root_PK) (DESIGN.md §2 items
   --  1-3 and 5), all from the bytes and the two context values:
   --    * the record is canonical;
   --    * the signer block is valid (Cert_OK: root_pk and the signer are
   --      usable keys, and the founding key certified the signer for this
   --      cid and cap; S3);
   --    * ceiling_t is not more than cert_cap (the founding key's cap is
   --      2^48 - 1, so this bounds a certified root only);
   --    * gen is not more than ceiling_t (so a certified root's gen is
   --      bounded by its cap; AUDIT.md H7);
   --    * every member sign_pk is a usable key (Member_Keys_OK; H13, A27);
   --    * the X25519 keys are good (E5), and box_pk is not the public key
   --      of the all-zero secret (A27);
   --    * the signature over h verifies under signer.
   function Well_Formed (Cid : Hash256; Root_PK : Pubkey; R : Roster_Record) return Boolean is
     (Canonical (R)
      and then Cert_OK (Cid, Root_PK, R.C.Signer, R.C.Cert_Cap, R.C.Cert_Sig)
      and then R.C.Ceiling_T <= R.C.Cert_Cap
      and then R.C.Gen <= R.C.Ceiling_T
      and then Member_Keys_OK (R.C)
      and then DH_Keys_OK (R.C)
      and then not Kome.Crypto.Is_Zero_Secret_DH_Public (R.C.Box_PK)
      and then Kome.Crypto.Verify (R.Signature, R.C.Signer, Hash (Cid, R.C)));

   procedure Decode_Verified
     (Cid : Hash256; Root_PK : Pubkey; Frame : Byte_Array; R : in out Roster_Record;
      Result : out Status)
   with Global => null,
        Post => (if Is_Roster_Frame (Frame)
                    and then Well_Formed (Cid, Root_PK, Parse_Roster (Frame))
                 then Result = OK and then R = Parse_Roster (Frame)
                 else Result = Malformed and then R = R'Old);

   procedure Sign (Cid : Hash256; R : in out Roster_Record; SK : Kome.Crypto.Secret_Key)
   with Global => null,
        Pre  => Canonical (R)
                and then Kome.Crypto.Is_Valid (SK)
                and then Kome.Crypto.Public_Of (SK) = R.C.Signer,
        Post => Canonical (R)
          and then R.C = R'Old.C
          and then R.Signature = Kome.Crypto.Sign (SK, Hash (Cid, R'Old.C))
          and then Hash (Cid, R.C) = Hash (Cid, R'Old.C);

   --  D3: the header is canonical when gen is at most ceiling_t
   --  (Well_Formed requires it).
   procedure Lemma_Header_Canonical (Cid : Hash256; R : Roster_Record) with
     Ghost, Global => null,
     Pre  => R.C.Gen <= R.C.Ceiling_T,
     Post => To_Header (Cid, R).K = K_Roster
             and then Kome.Headers.Canonical (To_Header (Cid, R));

   procedure Lemma_Decode_Encode (R : Roster_Record) with
     Ghost, Global => null,
     Pre  => Canonical (R),
     Post => Is_Roster_Frame (Encode (R)) and then Parse_Roster (Encode (R)) = R;

   procedure Lemma_Encode_Decode_Roster (Frame : Byte_Array) with
     Ghost, Global => null,
     Pre  => Is_Roster_Frame (Frame),
     Post => Encode (Parse_Roster (Frame)) = Frame;

   ---------------------------------------------------------------------------
   --  REVOKE  SIGNER sign_pk[32] from_t:u48
   --  sign_pk is the subject (the revoked key). signer is the issuing root.
   --  A REVOKE has no sequence number (AUDIT.md E15): the header's seq is
   --  0 (DESIGN.md §3), and two REVOKEs of one subject by one issuer are
   --  told apart by from_t and h only.
   ---------------------------------------------------------------------------

   type Revoke_Content is record
      Signer   : Pubkey    := [others => 0];   --  issuing root
      Cert_Cap : U48       := 0;
      Cert_Sig : Sig       := [others => 0];
      Sign_PK  : Pubkey    := [others => 0];   --  subject
      From_T   : U48       := 0;
   end record;

   type Revoke_Record is record
      C         : Revoke_Content;
      Signature : Sig := [others => 0];
   end record;

   Revoke_O_Signer   : constant := 1;
   Revoke_O_Cert_Cap : constant := 33;
   Revoke_O_Cert_Sig : constant := 39;
   Revoke_O_Sign_PK  : constant := 103;
   Revoke_O_From_T   : constant := 135;
   Revoke_Content_Len : constant := 141;
   Revoke_Frame_Len   : constant := Revoke_Content_Len + Sig_Len;
   pragma Compile_Time_Error
     (Revoke_Frame_Len /= 205, "SIMPLIFY.md §2: a REVOKE frame is 205 bytes");

   function Content_Byte (C : Revoke_Content; J : Natural) return Byte is
     (if J = 0 then Tag_Revoke
      elsif J < Revoke_O_Cert_Cap then C.Signer (J - Revoke_O_Signer)
      elsif J < Revoke_O_Cert_Sig then Byte_Of_U48 (C.Cert_Cap, J - Revoke_O_Cert_Cap)
      elsif J < Revoke_O_Sign_PK then C.Cert_Sig (J - Revoke_O_Cert_Sig)
      elsif J < Revoke_O_From_T then C.Sign_PK (J - Revoke_O_Sign_PK)
      else Byte_Of_U48 (C.From_T, J - Revoke_O_From_T))
     with Pre => J < Revoke_Content_Len;

   function Frame_Byte (R : Revoke_Record; J : Natural) return Byte is
     (if J < Revoke_Content_Len then Content_Byte (R.C, J)
      else R.Signature (J - Revoke_Content_Len))
     with Pre => J < Revoke_Frame_Len;

   function Content_Bytes (C : Revoke_Content) return Byte_Array
   with Global => null,
        Post => Content_Bytes'Result'First = 0
          and then Content_Bytes'Result'Length = Revoke_Content_Len
          and then (for all J in 0 .. Revoke_Content_Len - 1 =>
                      Content_Bytes'Result (J) = Content_Byte (C, J));

   --  h = BLAKE2b-256 (tag ‖ cid ‖ content) (S1).
   function Hash (Cid : Hash256; C : Revoke_Content) return Hash256 is
     (Kome.Crypto.Blake2b_256 (Hash_Input (Cid, Content_Bytes (C))));

   --  The issuing root (the Issuer of the header; V.Author is the subject).
   function Signer_Key (R : Revoke_Record) return Key256 is
     (To_Key256 (R.C.Signer));

   --  DESIGN.md §3: V = (from_t, sign_pk, 0, h); Issuer = signer. A REVOKE
   --  has no sequence number (AUDIT.md E15), so seq is 0.
   function To_Header (Cid : Hash256; R : Revoke_Record) return Header is
     (K       => K_Revoke,
      Ent     => Zero_Id,
      FH      => Zero_Key,
      V       => (T      => R.C.From_T,
                  Author => To_Key256 (R.C.Sign_PK),
                  Seq    => 0,
                  H      => To_Key256 (Hash (Cid, R.C))),
      Issuer  => Signer_Key (R));

   --  A REVOKE with a zero signature. Pre (H13, A27): the signer and the
   --  subject are usable keys, as Well_Formed requires.
   function Make_Revoke
     (Cid      : Hash256;
      Signer   : Pubkey;
      Cert_Cap : U48;
      Cert_Sig : Sig;
      Sign_PK  : Pubkey;
      From_T   : U48) return Revoke_Record
   with Global => null,
        Pre  => Sign_Key_OK (Signer) and then Sign_Key_OK (Sign_PK),
        Post => Make_Revoke'Result.C.Signer = Signer
          and then Make_Revoke'Result.C.Cert_Cap = Cert_Cap
          and then Make_Revoke'Result.C.Cert_Sig = Cert_Sig
          and then Make_Revoke'Result.C.Sign_PK = Sign_PK
          and then Make_Revoke'Result.C.From_T = From_T
          and then (for all I in Sig'Range => Make_Revoke'Result.Signature (I) = 0)
          and then To_Header (Cid, Make_Revoke'Result) =
                     (K      => K_Revoke,
                      Ent    => Zero_Id,
                      FH     => Zero_Key,
                      V      => (T      => From_T,
                                 Author => To_Key256 (Sign_PK),
                                 Seq    => 0,
                                 H      => To_Key256 (Hash (Cid, Make_Revoke'Result.C))),
                      Issuer => To_Key256 (Signer));

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

   --  Well-formed in the collection of (Cid, Root_PK) (DESIGN.md §2 items
   --  2, 4, 5): the signer block is valid (Cert_OK), the subject is a
   --  usable key (Sign_Key_OK) and is never the founding key (D2), and the
   --  signature over h verifies under signer.
   function Well_Formed (Cid : Hash256; Root_PK : Pubkey; R : Revoke_Record) return Boolean is
     (Cert_OK (Cid, Root_PK, R.C.Signer, R.C.Cert_Cap, R.C.Cert_Sig)
      and then Sign_Key_OK (R.C.Sign_PK)
      and then R.C.Sign_PK /= Root_PK
      and then Kome.Crypto.Verify (R.Signature, R.C.Signer, Hash (Cid, R.C)));

   procedure Decode_Verified
     (Cid : Hash256; Root_PK : Pubkey; Frame : Byte_Array; R : in out Revoke_Record;
      Result : out Status)
   with Global => null,
        Post => (if Is_Revoke_Frame (Frame)
                    and then Well_Formed (Cid, Root_PK, Parse_Revoke (Frame))
                 then Result = OK and then R = Parse_Revoke (Frame)
                 else Result = Malformed and then R = R'Old);

   procedure Sign (Cid : Hash256; R : in out Revoke_Record; SK : Kome.Crypto.Secret_Key)
   with Global => null,
        Pre  => Kome.Crypto.Is_Valid (SK)
                and then Kome.Crypto.Public_Of (SK) = R.C.Signer,
        Post => R.C = R'Old.C
          and then R.Signature = Kome.Crypto.Sign (SK, Hash (Cid, R'Old.C))
          and then Hash (Cid, R.C) = Hash (Cid, R'Old.C);

   procedure Lemma_Header_Canonical (Cid : Hash256; R : Revoke_Record) with
     Ghost, Global => null,
     Post => To_Header (Cid, R).K = K_Revoke
             and then Kome.Headers.Canonical (To_Header (Cid, R));

   procedure Lemma_Decode_Encode (R : Revoke_Record) with
     Ghost, Global => null,
     Post => Is_Revoke_Frame (Encode (R)) and then Parse_Revoke (Encode (R)) = R;

   procedure Lemma_Encode_Decode_Revoke (Frame : Byte_Array) with
     Ghost, Global => null,
     Pre  => Is_Revoke_Frame (Frame),
     Post => Encode (Parse_Revoke (Frame)) = Frame;

   ---------------------------------------------------------------------------
   --  GRANT   SIGNER subject[32]
   --  Write access (D1′): the subject can author PUTs and DELs. The key is
   --  (issuer, subject) (D1′).
   ---------------------------------------------------------------------------

   type Grant_Content is record
      Signer   : Pubkey    := [others => 0];   --  issuing root
      Cert_Cap : U48       := 0;
      Cert_Sig : Sig       := [others => 0];
      Subject  : Pubkey    := [others => 0];   --  the key granted
   end record;

   type Grant_Record is record
      C         : Grant_Content;
      Signature : Sig := [others => 0];
   end record;

   Grant_O_Signer   : constant := 1;
   Grant_O_Cert_Cap : constant := 33;
   Grant_O_Cert_Sig : constant := 39;
   Grant_O_Subject  : constant := 103;
   Grant_Content_Len : constant := 135;
   Grant_Frame_Len   : constant := Grant_Content_Len + Sig_Len;
   pragma Compile_Time_Error
     (Grant_Frame_Len /= 199, "SIMPLIFY.md §2: a GRANT frame is 199 bytes");

   function Content_Byte (C : Grant_Content; J : Natural) return Byte is
     (if J = 0 then Tag_Grant
      elsif J < Grant_O_Cert_Cap then C.Signer (J - Grant_O_Signer)
      elsif J < Grant_O_Cert_Sig then Byte_Of_U48 (C.Cert_Cap, J - Grant_O_Cert_Cap)
      elsif J < Grant_O_Subject then C.Cert_Sig (J - Grant_O_Cert_Sig)
      else C.Subject (J - Grant_O_Subject))
     with Pre => J < Grant_Content_Len;

   function Frame_Byte (R : Grant_Record; J : Natural) return Byte is
     (if J < Grant_Content_Len then Content_Byte (R.C, J)
      else R.Signature (J - Grant_Content_Len))
     with Pre => J < Grant_Frame_Len;

   function Content_Bytes (C : Grant_Content) return Byte_Array
   with Global => null,
        Post => Content_Bytes'Result'First = 0
          and then Content_Bytes'Result'Length = Grant_Content_Len
          and then (for all J in 0 .. Grant_Content_Len - 1 =>
                      Content_Bytes'Result (J) = Content_Byte (C, J));

   --  h = BLAKE2b-256 (tag ‖ cid ‖ content) (S1).
   function Hash (Cid : Hash256; C : Grant_Content) return Hash256 is
     (Kome.Crypto.Blake2b_256 (Hash_Input (Cid, Content_Bytes (C))));

   --  The issuing root (the Issuer of the header; V.Author is the subject).
   function Signer_Key (R : Grant_Record) return Key256 is
     (To_Key256 (R.C.Signer));

   --  DESIGN.md §3: V = (cap, subject, 0, h); Issuer = signer. The write
   --  cap of a GRANT (DESIGN.md §2, §4; AUDIT.md A1; S3) is its issuer's
   --  cert_cap, for every issuer: the founding key's own certificate
   --  carries 2^48 - 1. wcap (k), the largest V.T over the held GRANTs of
   --  subject k, so reads cert_cap and nothing else.
   function To_Header (Cid : Hash256; R : Grant_Record) return Header is
     (K       => K_Grant,
      Ent     => Zero_Id,
      FH      => Zero_Key,
      V       => (T      => R.C.Cert_Cap,
                  Author => To_Key256 (R.C.Subject),
                  Seq    => 0,
                  H      => To_Key256 (Hash (Cid, R.C))),
      Issuer  => Signer_Key (R));

   --  A GRANT with a zero signature. Pre (H13, A27): the signer and the
   --  subject are usable keys, as Well_Formed requires. A GRANT to a
   --  small-order subject would let anybody write as that subject (the
   --  decision of H13: refuse).
   function Make_Grant
     (Cid      : Hash256;
      Signer   : Pubkey;
      Cert_Cap : U48;
      Cert_Sig : Sig;
      Subject  : Pubkey) return Grant_Record
   with Global => null,
        Pre  => Sign_Key_OK (Signer) and then Sign_Key_OK (Subject),
        Post => Make_Grant'Result.C.Signer = Signer
          and then Make_Grant'Result.C.Cert_Cap = Cert_Cap
          and then Make_Grant'Result.C.Cert_Sig = Cert_Sig
          and then Make_Grant'Result.C.Subject = Subject
          and then (for all I in Sig'Range => Make_Grant'Result.Signature (I) = 0)
          and then To_Header (Cid, Make_Grant'Result) =
                     (K      => K_Grant,
                      Ent    => Zero_Id,
                      FH     => Zero_Key,
                      V      => (T      => Cert_Cap,
                                 Author => To_Key256 (Subject),
                                 Seq    => 0,
                                 H      => To_Key256 (Hash (Cid, Make_Grant'Result.C))),
                      Issuer => To_Key256 (Signer));

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

   --  Well-formed in the collection of (Cid, Root_PK) (DESIGN.md §2 items
   --  2, 5): the subject is a usable key (H13, A27: a small-order subject,
   --  or the key of the all-zero seed, is refused by bytes), the signer
   --  block is valid (Cert_OK), and the signature over h verifies under
   --  signer.
   function Well_Formed (Cid : Hash256; Root_PK : Pubkey; R : Grant_Record) return Boolean is
     (Sign_Key_OK (R.C.Subject)
      and then Cert_OK (Cid, Root_PK, R.C.Signer, R.C.Cert_Cap, R.C.Cert_Sig)
      and then Kome.Crypto.Verify (R.Signature, R.C.Signer, Hash (Cid, R.C)));

   procedure Decode_Verified
     (Cid : Hash256; Root_PK : Pubkey; Frame : Byte_Array; R : in out Grant_Record;
      Result : out Status)
   with Global => null,
        Post => (if Is_Grant_Frame (Frame)
                    and then Well_Formed (Cid, Root_PK, Parse_Grant (Frame))
                 then Result = OK and then R = Parse_Grant (Frame)
                 else Result = Malformed and then R = R'Old);

   procedure Sign (Cid : Hash256; R : in out Grant_Record; SK : Kome.Crypto.Secret_Key)
   with Global => null,
        Pre  => Kome.Crypto.Is_Valid (SK)
                and then Kome.Crypto.Public_Of (SK) = R.C.Signer,
        Post => R.C = R'Old.C
          and then R.Signature = Kome.Crypto.Sign (SK, Hash (Cid, R'Old.C))
          and then Hash (Cid, R.C) = Hash (Cid, R'Old.C);

   procedure Lemma_Header_Canonical (Cid : Hash256; R : Grant_Record) with
     Ghost, Global => null,
     Post => To_Header (Cid, R).K = K_Grant
             and then Kome.Headers.Canonical (To_Header (Cid, R));

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

   --  One or more members of the ROSTER frame have dh_pk = DH (the
   --  credential HELLO of DESIGN.md §8 must list the Noise key of the
   --  sender). This function has a quantifier, so its completion is in the
   --  private part. Lemma_Roster_Lists_DH gives its meaning.
   function Roster_Lists_DH (Frame : Byte_Array; DH : Pubkey) return Boolean
     with Global => null, Pre => Is_Roster_Frame (Frame);

   procedure Lemma_Roster_Lists_DH (Frame : Byte_Array; DH : Pubkey) with
     Ghost, Global => null,
     Pre  => Is_Roster_Frame (Frame),
     Post => Roster_Lists_DH (Frame, DH) =
               (for some I in 1 .. Parse_Roster (Frame).C.N_Members =>
                  Member_DH_PK (Parse_Roster (Frame).C, I) = DH);

private

   function Canonical (R : Put_Record) return Boolean is
     ((for all I in Field_Bytes'Range => (if I >= R.C.FLen then R.C.Field (I) = 0))
      and then
      (for all I in Value_Bytes'Range => (if I >= R.C.VLen then R.C.Value (I) = 0)));

   function Canonical (R : Roster_Record) return Boolean is
     (for all I in Members_Bytes'Range =>
        (if I >= Member_Len * R.C.N_Members then R.C.Members (I) = 0));

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

   function Member_Keys_OK (C : Roster_Content) return Boolean is
     (for all I in 1 .. C.N_Members => Sign_Key_OK (Member_Sign_PK (C, I)));

   --  The dh_pk of member I, read directly from a ROSTER frame.
   function Frame_DH (Frame : Byte_Array; I : Member_Index) return Pubkey is
     ([for K in Pubkey'Range =>
         Frame (Frame'First + Roster_O_Members + Member_Len * (I - 1) + Pubkey_Len + K)])
     with Pre => Is_Roster_Frame (Frame) and then I <= Roster_NM (Frame);

   function Roster_Lists_DH (Frame : Byte_Array; DH : Pubkey) return Boolean is
     (for some I in 1 .. Roster_NM (Frame) => Frame_DH (Frame, I) = DH);

end Kome.Records;
