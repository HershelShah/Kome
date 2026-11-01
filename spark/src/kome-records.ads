--  Kome.Records: canonical record encoding, hashing, signing and
--  well-formedness (DESIGN.md §2 "Records"; T13 "every emitted record
--  satisfies the §2 layout"). This is the wire and crypto boundary: records
--  here hold bytes, and To_Header turns them into the lattice's word
--  records (Kome.Headers.Header, Id128 / Key256 via Kome.Keys).
--
--  Layouts, all integers big-endian (DESIGN.md §2, with the module J
--  fields of §6 for ROSTER and REVOKE):
--
--    PUT     ns[16] ent[16] flen:u8 field[flen] t:u48 seq:u48 author[32]
--            vlen:u16 value[vlen]
--    DEL     ns[16] ent[16] t:u48 seq:u48 author[32]
--    ROSTER  ns[16] root_pk[32] salt[16] signer[32] prev_h[32] gen:u48
--            ceiling_t:u48 del_ttl:u48 epoch:u16 n_roots:u8 (<= 4)
--            roots[n_roots][32] n_members:u8 (<= 64)
--            members[n] { sign_pk[32] dh_pk[32] nonce[24] box[48] }
--    REVOKE  ns[16] root_pk[32] salt[16] signer[32] sign_pk[32] from_t:u48
--            rev_seq:u48
--
--  A frame is  tag:u8 ‖ content ‖ sig[64];  h = BLAKE2b-256 (tag ‖ content);
--  sig = Ed25519 over h by author (PUT, DEL) or by signer (ROSTER, REVOKE).
--  The tag is the Kind's reconciliation-order code (Kome.Headers.Kind:
--  ROSTER 0, REVOKE 1, DEL 2, PUT 3).
--
--  Module J (DESIGN.md §6, "Several roots"). root_pk is the founding key:
--  ns = BLAKE2b-256 (root_pk ‖ salt)[0:16] keeps the collection
--  self-certifying. signer is the root that issued the record: "ROSTER,
--  REVOKE and the epoch key may be issued by any listed root". prev_h is
--  "the hash of the roster it extends" (zero for a first roster). What a
--  record's own bytes can decide is checked here (Well_Formed): a ROSTER's
--  signer is root_pk or one of its own roots, and the signature verifies
--  under signer. What needs other records is not: admission
--  `signer ∈ roots_ever` (Kome.Frontier) and "a root is added only by a
--  roster signed by the founding key", which compares a roster with the
--  one prev_h names (Kome.Roster, phase 8). A ROSTER header carries the
--  signer in V.Author, so roster domination is per signer (Kome.Headers);
--  a REVOKE header carries the subject there, and its signer is read with
--  Signer_Key. DESIGN.md §2's table predates module J and lists neither
--  signer nor prev_h; this layout is the reading of §6 chosen here, to be
--  recorded in DESIGN.md §10.
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
--      length, tag, flen in 1..32, n_roots <= 4, n_members <= 64), never
--      reads out of bounds, returns Parse_<Kind> on success and leaves the
--      record unchanged on failure.
--    * Lemma_Decode_Encode: Parse (Encode (R)) = R for every canonical R,
--      so Decode (Encode (R)) returns OK and R.
--    * Lemma_Encode_Decode_<Kind>: Encode (Parse (B)) = B for every accepted
--      B: each record has exactly one encoding, so h is a function of the
--      record (A2 then makes h injective on records).
--    * Lemma_Header_Canonical: To_Header has the shape Kome.Views.Canonical
--      asks of each kind. Lemma_Signer_Listed: Signer_Listed is "signer is
--      root_pk or some Root (C, I)".
--  Not proved: anything about BLAKE2b or Ed25519 themselves. Kome.Crypto's
--  Blake2b_256, Sign and Verify are opaque functions; Well_Formed calls
--  Verify, and no theorem here depends on what it returns.
--
--  Canonical form: unused field, value, root and member bytes are zero. On
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
   --  Tags (one byte, the Kind's representation, DESIGN.md §8 key order).
   ---------------------------------------------------------------------------

   Tag_Roster : constant Byte := 0;
   Tag_Revoke : constant Byte := 1;
   Tag_Del    : constant Byte := 2;
   Tag_Put    : constant Byte := 3;

   function Tag_Of (K : Kind) return Byte is
     (case K is
         when K_Roster => Tag_Roster,
         when K_Revoke => Tag_Revoke,
         when K_Del    => Tag_Del,
         when K_Put    => Tag_Put);

   --  The kind a frame claims to be (its first byte), if any.
   function Has_Kind (Frame : Byte_Array) return Boolean is
     (Frame'Length > 0 and then Frame (Frame'First) <= Tag_Put);

   function Kind_Of (Frame : Byte_Array) return Kind is
     (if Frame (Frame'First) = Tag_Roster then K_Roster
      elsif Frame (Frame'First) = Tag_Revoke then K_Revoke
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
   function Collection_Id (Root_PK : Pubkey; S : Salt) return NS_Id is
     (Kome.Crypto.Blake2b_256 (Root_PK & S) (0 .. NS_Len - 1));

   --  Every frame is at most this long (a PUT with a 32-byte field and a
   --  65 535-byte value); every hashed content is at most this minus 64.
   Frame_Max : constant := 1 + 16 + 16 + 1 + 32 + 6 + 6 + 32 + 2 + Value_Max + Sig_Len;

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
          and then (for all I in Sig'Range => Make_Put'Result.Signature (I) = 0);

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

   function Is_Put_Frame (Frame : Byte_Array) return Boolean is
     (Frame'Length >= Put_Frame_Min
      and then Frame'Length <= Put_Frame_Max
      and then Frame (Frame'First) = Tag_Put
      and then Put_FL (Frame) in Field_Len
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
   --  FH = BLAKE2b-256 (field name), Ceiling 0.
   function To_Header (R : Put_Record) return Header is
     (K       => K_Put,
      NS      => To_Id128 (R.C.NS),
      Ent     => To_Id128 (R.C.Ent),
      FH      => To_Key256 (Kome.Crypto.Blake2b_256 (R.C.Field (0 .. R.C.FLen - 1))),
      V       => (T      => R.C.T,
                  Author => To_Key256 (R.C.Author),
                  Seq    => R.C.Seq,
                  H      => To_Key256 (Hash (R.C))),
      Ceiling => 0);

   --  The header has the canonical shape Kome.Views.Canonical asks of a PUT
   --  (stated by its conjuncts: Kome.Views is not preelaborable, so it
   --  cannot be withed here; the test main checks the two agree).
   procedure Lemma_Header_Canonical (R : Put_Record) with
     Ghost, Global => null,
     Post => To_Header (R).K = K_Put and then To_Header (R).Ceiling = 0;

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

   --  V = (t, author, seq, h); a DEL has no field (FH 0) and no ceiling.
   function To_Header (R : Del_Record) return Header is
     (K       => K_Del,
      NS      => To_Id128 (R.C.NS),
      Ent     => To_Id128 (R.C.Ent),
      FH      => (others => 0),
      V       => (T      => R.C.T,
                  Author => To_Key256 (R.C.Author),
                  Seq    => R.C.Seq,
                  H      => To_Key256 (Hash (R.C))),
      Ceiling => 0);

   --  Kome.Views.Canonical for a DEL: FH and Ceiling zero.
   procedure Lemma_Header_Canonical (R : Del_Record) with
     Ghost, Global => null,
     Post => To_Header (R).K = K_Del
             and then To_Header (R).FH = Key256'(others => 0)
             and then To_Header (R).Ceiling = 0;

   procedure Lemma_Decode_Encode (R : Del_Record) with
     Ghost, Global => null,
     Post => Is_Del_Frame (Encode (R)) and then Parse_Del (Encode (R)) = R;

   procedure Lemma_Encode_Decode_Del (Frame : Byte_Array) with
     Ghost, Global => null,
     Pre  => Is_Del_Frame (Frame),
     Post => Encode (Parse_Del (Frame)) = Frame;

   ---------------------------------------------------------------------------
   --  ROSTER  ns[16] root_pk[32] salt[16] signer[32] prev_h[32] gen:u48
   --          ceiling_t:u48 del_ttl:u48 epoch:u16 n_roots:u8
   --          roots[n_roots][32] n_members:u8
   --          members[n] { sign_pk[32] dh_pk[32] nonce[24] box[48] }
   --  Roots and members are stored flat, as on the wire, so the encoding
   --  is a sequence of byte copies; the accessors below cut them up.
   ---------------------------------------------------------------------------

   Member_Len        : constant := Pubkey_Len + Pubkey_Len + Nonce_Len + Box_Len;
   Roots_Bytes_Len   : constant := Roots_Max * Pubkey_Len;
   Members_Bytes_Len : constant := Members_Max * Member_Len;

   subtype Root_Count   is Natural range 0 .. Roots_Max;
   subtype Member_Count is Natural range 0 .. Members_Max;
   subtype Root_Index   is Positive range 1 .. Roots_Max;
   subtype Member_Index is Positive range 1 .. Members_Max;
   subtype Roots_Bytes   is Byte_Array (0 .. Roots_Bytes_Len - 1);
   subtype Members_Bytes is Byte_Array (0 .. Members_Bytes_Len - 1);

   type Roster_Content is record
      NS        : NS_Id         := [others => 0];
      Root_PK   : Pubkey        := [others => 0];   --  founding key (ns)
      Salt      : Kome.Salt     := [others => 0];
      Signer    : Pubkey        := [others => 0];   --  issuing root (§6)
      Prev_H    : Hash256       := [others => 0];   --  roster extended (§6)
      Gen       : U48           := 0;
      Ceiling_T : U48           := 0;
      Del_TTL   : U48           := 0;
      Epoch     : Kome.Epoch    := 0;
      N_Roots   : Root_Count    := 0;
      Roots     : Roots_Bytes   := [others => 0];   --  Roots (0 .. 32 * N_Roots - 1)
      N_Members : Member_Count  := 0;
      Members   : Members_Bytes := [others => 0];   --  Members (0 .. 136 * N_Members - 1)
   end record;

   type Roster_Record is record
      C         : Roster_Content;
      Signature : Sig := [others => 0];
   end record;

   Roster_O_NS      : constant := 1;
   Roster_O_Root_PK : constant := 17;
   Roster_O_Salt    : constant := 49;
   Roster_O_Signer  : constant := 65;
   Roster_O_Prev_H  : constant := 97;
   Roster_O_Gen     : constant := 129;
   Roster_O_Ceiling : constant := 135;
   Roster_O_TTL     : constant := 141;
   Roster_O_Epoch   : constant := 147;
   Roster_O_NR      : constant := 149;
   Roster_O_Roots   : constant := 150;
   Roster_Fixed     : constant := 151;          --  tag + every fixed-width part
   Roster_Frame_Min : constant := Roster_Fixed + Sig_Len;
   Roster_Frame_Max : constant :=
     Roster_Fixed + Roots_Bytes_Len + Members_Bytes_Len + Sig_Len;

   function Roster_O_NM (NR : Natural) return Natural is
     (Roster_O_Roots + Pubkey_Len * NR)
     with Pre => NR <= 255;
   function Roster_O_Members (NR : Natural) return Natural is
     (Roster_O_Roots + Pubkey_Len * NR + 1)
     with Pre => NR <= 255;

   function Content_Len (C : Roster_Content) return Positive is
     (Roster_Fixed + Pubkey_Len * C.N_Roots + Member_Len * C.N_Members);

   function Frame_Len (R : Roster_Record) return Positive is
     (Content_Len (R.C) + Sig_Len);

   function Content_Byte (C : Roster_Content; J : Natural) return Byte is
     (if J = 0 then Tag_Roster
      elsif J < Roster_O_Root_PK then C.NS (J - Roster_O_NS)
      elsif J < Roster_O_Salt then C.Root_PK (J - Roster_O_Root_PK)
      elsif J < Roster_O_Signer then C.Salt (J - Roster_O_Salt)
      elsif J < Roster_O_Prev_H then C.Signer (J - Roster_O_Signer)
      elsif J < Roster_O_Gen then C.Prev_H (J - Roster_O_Prev_H)
      elsif J < Roster_O_Ceiling then Byte_Of_U48 (C.Gen, J - Roster_O_Gen)
      elsif J < Roster_O_TTL then Byte_Of_U48 (C.Ceiling_T, J - Roster_O_Ceiling)
      elsif J < Roster_O_Epoch then Byte_Of_U48 (C.Del_TTL, J - Roster_O_TTL)
      elsif J < Roster_O_NR then Byte_Of_U16 (Natural (C.Epoch), J - Roster_O_Epoch)
      elsif J = Roster_O_NR then Byte (C.N_Roots)
      elsif J < Roster_O_NM (C.N_Roots) then C.Roots (J - Roster_O_Roots)
      elsif J = Roster_O_NM (C.N_Roots) then Byte (C.N_Members)
      else C.Members (J - Roster_O_Members (C.N_Roots)))
     with Pre => J < Content_Len (C);

   function Frame_Byte (R : Roster_Record; J : Natural) return Byte is
     (if J < Content_Len (R.C) then Content_Byte (R.C, J)
      else R.Signature (J - Content_Len (R.C)))
     with Pre => J < Frame_Len (R);

   --  Root I and member I's parts. Opaque (each is a quantified aggregate,
   --  CONVENTIONS.md rule 2); their bytes are Lemma_Root_Bytes and
   --  Lemma_Member_Bytes.
   function Root (C : Roster_Content; I : Root_Index) return Pubkey
     with Global => null, Pre => I <= C.N_Roots;

   function Member_Sign_PK (C : Roster_Content; I : Member_Index) return Pubkey
     with Global => null, Pre => I <= C.N_Members;

   function Member_DH_PK (C : Roster_Content; I : Member_Index) return Pubkey
     with Global => null, Pre => I <= C.N_Members;

   function Member_Nonce (C : Roster_Content; I : Member_Index) return Nonce
     with Global => null, Pre => I <= C.N_Members;

   function Member_Box (C : Roster_Content; I : Member_Index) return Box
     with Global => null, Pre => I <= C.N_Members;

   --  The member's signing key as the lattice sees it (for W, Kome.Frontier).
   function Member_Key (C : Roster_Content; I : Member_Index) return Key256 is
     (To_Key256 (Member_Sign_PK (C, I)))
     with Pre => I <= C.N_Members;

   procedure Lemma_Root_Bytes (C : Roster_Content; I : Root_Index) with
     Ghost, Global => null,
     Pre  => I <= C.N_Roots,
     Post => (for all K in Pubkey'Range =>
                Root (C, I) (K) = C.Roots (Pubkey_Len * (I - 1) + K));

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

   --  The signer is the founding key or one of the roster's own roots
   --  (DESIGN.md §6: "ROSTER ... may be issued by any listed root").
   --  Spelled out over the four root slots so it stays quantifier-free.
   function Signer_Listed (C : Roster_Content) return Boolean is
     (C.Signer = C.Root_PK
      or else (C.N_Roots >= 1 and then C.Roots (0 .. 31) = C.Signer)
      or else (C.N_Roots >= 2 and then C.Roots (32 .. 63) = C.Signer)
      or else (C.N_Roots >= 3 and then C.Roots (64 .. 95) = C.Signer)
      or else (C.N_Roots = 4 and then C.Roots (96 .. 127) = C.Signer));

   --  The same, through the Root accessor.
   procedure Lemma_Signer_Listed (C : Roster_Content) with
     Ghost, Global => null,
     Post => Signer_Listed (C) =
               (C.Signer = C.Root_PK
                or else (for some I in 1 .. C.N_Roots => Root (C, I) = C.Signer));

   --  Unused root and member bytes are zero. Opaque (quantified).
   function Canonical (R : Roster_Record) return Boolean with Global => null;

   --  A canonical ROSTER with ns derived from (root_pk, salt) and a zero
   --  signature. Roots and Members are the flat wire bytes.
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
   with Global => null,
        Pre  => Roots'Length <= Roots_Bytes_Len
                and then Roots'Length mod Pubkey_Len = 0
                and then Members'Length <= Members_Bytes_Len
                and then Members'Length mod Member_Len = 0,
        Post => Canonical (Make_Roster'Result)
          and then Make_Roster'Result.C.NS = Collection_Id (Root_PK, S)
          and then Make_Roster'Result.C.Root_PK = Root_PK
          and then Make_Roster'Result.C.Salt = S
          and then Make_Roster'Result.C.Signer = Signer
          and then Make_Roster'Result.C.Prev_H = Prev_H
          and then Make_Roster'Result.C.Gen = Gen
          and then Make_Roster'Result.C.Ceiling_T = Ceiling_T
          and then Make_Roster'Result.C.Del_TTL = Del_TTL
          and then Make_Roster'Result.C.Epoch = E
          and then Make_Roster'Result.C.N_Roots * Pubkey_Len = Roots'Length
          and then (for all I in 0 .. Roots'Length - 1 =>
                      Make_Roster'Result.C.Roots (I) = Roots (Roots'First + I))
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

   function Roster_NR (Frame : Byte_Array) return Natural is
     (Natural (Frame (Frame'First + Roster_O_NR)))
     with Pre => Frame'Length >= Roster_Frame_Min;

   --  n_members sits after the roots, so it is read only once the frame is
   --  long enough to hold n_roots roots.
   function Roster_NM (Frame : Byte_Array) return Natural is
     (Natural (Frame (Frame'First + Roster_O_NM (Roster_NR (Frame)))))
     with Pre => Frame'Length >= Roster_Frame_Min
                 and then Frame'Length <= Roster_Frame_Max
                 and then Frame'Length >= Roster_Frame_Min + Pubkey_Len * Roster_NR (Frame);

   function Is_Roster_Frame (Frame : Byte_Array) return Boolean is
     (Frame'Length >= Roster_Frame_Min
      and then Frame'Length <= Roster_Frame_Max
      and then Frame (Frame'First) = Tag_Roster
      and then Roster_NR (Frame) <= Roots_Max
      and then Frame'Length >= Roster_Frame_Min + Pubkey_Len * Roster_NR (Frame)
      and then Roster_NM (Frame) <= Members_Max
      and then Frame'Length = Roster_Frame_Min + Pubkey_Len * Roster_NR (Frame)
                              + Member_Len * Roster_NM (Frame));

   function Parse_Roster (Frame : Byte_Array) return Roster_Record
   with Global => null,
        Pre  => Is_Roster_Frame (Frame),
        Post => Canonical (Parse_Roster'Result)
          and then Parse_Roster'Result.C.Gen = U48_At (Frame, Frame'First + Roster_O_Gen)
          and then Parse_Roster'Result.C.Ceiling_T =
                     U48_At (Frame, Frame'First + Roster_O_Ceiling)
          and then Parse_Roster'Result.C.Del_TTL = U48_At (Frame, Frame'First + Roster_O_TTL)
          and then Parse_Roster'Result.C.Epoch =
                     Epoch (U16_At (Frame, Frame'First + Roster_O_Epoch))
          and then Parse_Roster'Result.C.N_Roots = Roster_NR (Frame)
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
          and then (for all I in Hash256'Range =>
                      Parse_Roster'Result.C.Prev_H (I) =
                        Frame (Frame'First + Roster_O_Prev_H + I))
          and then (for all I in Roots_Bytes'Range =>
                      Parse_Roster'Result.C.Roots (I) =
                        (if I < Pubkey_Len * Roster_NR (Frame)
                         then Frame (Frame'First + Roster_O_Roots + I) else 0))
          and then (for all I in Members_Bytes'Range =>
                      Parse_Roster'Result.C.Members (I) =
                        (if I < Member_Len * Roster_NM (Frame)
                         then Frame (Frame'First + Roster_O_Members (Roster_NR (Frame)) + I)
                         else 0))
          and then (for all I in Sig'Range =>
                      Parse_Roster'Result.Signature (I) =
                        Frame (Frame'First + Roster_O_Members (Roster_NR (Frame))
                               + Member_Len * Roster_NM (Frame) + I));

   procedure Decode (Frame : Byte_Array; R : in out Roster_Record; Result : out Status)
   with Global => null,
        Post => (if Is_Roster_Frame (Frame)
                 then Result = OK and then R = Parse_Roster (Frame)
                 else Result = Malformed and then R = R'Old);

   --  Well-formed (DESIGN.md §2, §6): canonical, ns matches (root_pk, salt),
   --  the signer is root_pk or a listed root, and the signature over h
   --  verifies under signer. Whether signer is in roots_ever, and whether a
   --  non-founding signer added a root, need other records (see the
   --  package comment).
   function Well_Formed (R : Roster_Record) return Boolean is
     (Canonical (R)
      and then R.C.NS = Collection_Id (R.C.Root_PK, R.C.Salt)
      and then Signer_Listed (R.C)
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

   --  The issuing root as the lattice sees it (admission: signer ∈
   --  roots_ever, DESIGN.md §6).
   function Signer_Key (R : Roster_Record) return Key256 is
     (To_Key256 (R.C.Signer));

   --  V = (0, signer, gen, h) (Kome.Headers: roster domination is per
   --  signer); Ceiling = ceiling_t; no entity, no field.
   function To_Header (R : Roster_Record) return Header is
     (K       => K_Roster,
      NS      => To_Id128 (R.C.NS),
      Ent     => (others => 0),
      FH      => (others => 0),
      V       => (T      => 0,
                  Author => Signer_Key (R),
                  Seq    => R.C.Gen,
                  H      => To_Key256 (Hash (R.C))),
      Ceiling => R.C.Ceiling_T);

   --  Kome.Views.Canonical for a ROSTER: Ent, FH and V.T zero.
   procedure Lemma_Header_Canonical (R : Roster_Record) with
     Ghost, Global => null,
     Post => To_Header (R).K = K_Roster
             and then To_Header (R).Ent = Id128'(others => 0)
             and then To_Header (R).FH = Key256'(others => 0)
             and then To_Header (R).V.T = 0;

   procedure Lemma_Decode_Encode (R : Roster_Record) with
     Ghost, Global => null,
     Pre  => Canonical (R),
     Post => Is_Roster_Frame (Encode (R)) and then Parse_Roster (Encode (R)) = R;

   procedure Lemma_Encode_Decode_Roster (Frame : Byte_Array) with
     Ghost, Global => null,
     Pre  => Is_Roster_Frame (Frame),
     Post => Encode (Parse_Roster (Frame)) = Frame;

   ---------------------------------------------------------------------------
   --  REVOKE  ns[16] root_pk[32] salt[16] signer[32] sign_pk[32] from_t:u48
   --          rev_seq:u48
   --  sign_pk is the subject (the key revoked); signer is the issuing root.
   ---------------------------------------------------------------------------

   type Revoke_Content is record
      NS      : NS_Id     := [others => 0];
      Root_PK : Pubkey    := [others => 0];   --  founding key (ns)
      Salt    : Kome.Salt := [others => 0];
      Signer  : Pubkey    := [others => 0];   --  issuing root (§6)
      Sign_PK : Pubkey    := [others => 0];   --  subject
      From_T  : U48       := 0;
      Rev_Seq : U48       := 0;
   end record;

   type Revoke_Record is record
      C         : Revoke_Content;
      Signature : Sig := [others => 0];
   end record;

   Revoke_O_NS      : constant := 1;
   Revoke_O_Root_PK : constant := 17;
   Revoke_O_Salt    : constant := 49;
   Revoke_O_Signer  : constant := 65;
   Revoke_O_Sign_PK : constant := 97;
   Revoke_O_From_T  : constant := 129;
   Revoke_O_Rev_Seq : constant := 135;
   Revoke_Content_Len : constant := 141;
   Revoke_Frame_Len   : constant := Revoke_Content_Len + Sig_Len;

   function Content_Byte (C : Revoke_Content; J : Natural) return Byte is
     (if J = 0 then Tag_Revoke
      elsif J < Revoke_O_Root_PK then C.NS (J - Revoke_O_NS)
      elsif J < Revoke_O_Salt then C.Root_PK (J - Revoke_O_Root_PK)
      elsif J < Revoke_O_Signer then C.Salt (J - Revoke_O_Salt)
      elsif J < Revoke_O_Sign_PK then C.Signer (J - Revoke_O_Signer)
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
     (Root_PK : Pubkey;
      S       : Salt;
      Signer  : Pubkey;
      Sign_PK : Pubkey;
      From_T  : U48;
      Rev_Seq : U48) return Revoke_Record
   with Global => null,
        Post => Make_Revoke'Result.C.NS = Collection_Id (Root_PK, S)
          and then Make_Revoke'Result.C.Root_PK = Root_PK
          and then Make_Revoke'Result.C.Salt = S
          and then Make_Revoke'Result.C.Signer = Signer
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
        Post => Parse_Revoke'Result.C.From_T = U48_At (Frame, Frame'First + Revoke_O_From_T)
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

   --  Well-formed (DESIGN.md §2, §6): ns matches (root_pk, salt) and the
   --  signature over h verifies under signer. A REVOKE carries no root
   --  list, so which roots may issue it is admission alone (signer ∈
   --  roots_ever, Kome.Frontier), as DESIGN.md §6 says.
   function Well_Formed (R : Revoke_Record) return Boolean is
     (R.C.NS = Collection_Id (R.C.Root_PK, R.C.Salt)
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

   --  The issuing root (admission: signer ∈ roots_ever). Not in the header,
   --  whose V.Author is the subject.
   function Signer_Key (R : Revoke_Record) return Key256 is
     (To_Key256 (R.C.Signer));

   --  V = (from_t, sign_pk, rev_seq, h); no entity, field or ceiling.
   function To_Header (R : Revoke_Record) return Header is
     (K       => K_Revoke,
      NS      => To_Id128 (R.C.NS),
      Ent     => (others => 0),
      FH      => (others => 0),
      V       => (T      => R.C.From_T,
                  Author => To_Key256 (R.C.Sign_PK),
                  Seq    => R.C.Rev_Seq,
                  H      => To_Key256 (Hash (R.C))),
      Ceiling => 0);

   --  Kome.Views.Canonical for a REVOKE: Ent, FH and Ceiling zero.
   procedure Lemma_Header_Canonical (R : Revoke_Record) with
     Ghost, Global => null,
     Post => To_Header (R).K = K_Revoke
             and then To_Header (R).Ent = Id128'(others => 0)
             and then To_Header (R).FH = Key256'(others => 0)
             and then To_Header (R).Ceiling = 0;

   procedure Lemma_Decode_Encode (R : Revoke_Record) with
     Ghost, Global => null,
     Post => Is_Revoke_Frame (Encode (R)) and then Parse_Revoke (Encode (R)) = R;

   procedure Lemma_Encode_Decode_Revoke (Frame : Byte_Array) with
     Ghost, Global => null,
     Pre  => Is_Revoke_Frame (Frame),
     Post => Encode (Parse_Revoke (Frame)) = Frame;

private

   function Canonical (R : Put_Record) return Boolean is
     ((for all I in Field_Bytes'Range => (if I >= R.C.FLen then R.C.Field (I) = 0))
      and then
      (for all I in Value_Bytes'Range => (if I >= R.C.VLen then R.C.Value (I) = 0)));

   function Canonical (R : Roster_Record) return Boolean is
     ((for all I in Roots_Bytes'Range =>
         (if I >= Pubkey_Len * R.C.N_Roots then R.C.Roots (I) = 0))
      and then
      (for all I in Members_Bytes'Range =>
         (if I >= Member_Len * R.C.N_Members then R.C.Members (I) = 0)));

   function Root (C : Roster_Content; I : Root_Index) return Pubkey is
     ([for K in Pubkey'Range => C.Roots (Pubkey_Len * (I - 1) + K)]);

   function Member_Sign_PK (C : Roster_Content; I : Member_Index) return Pubkey is
     ([for K in Pubkey'Range => C.Members (Member_Len * (I - 1) + K)]);

   function Member_DH_PK (C : Roster_Content; I : Member_Index) return Pubkey is
     ([for K in Pubkey'Range => C.Members (Member_Len * (I - 1) + Pubkey_Len + K)]);

   function Member_Nonce (C : Roster_Content; I : Member_Index) return Nonce is
     ([for K in Nonce'Range => C.Members (Member_Len * (I - 1) + 2 * Pubkey_Len + K)]);

   function Member_Box (C : Roster_Content; I : Member_Index) return Box is
     ([for K in Box'Range =>
         C.Members (Member_Len * (I - 1) + 2 * Pubkey_Len + Nonce_Len + K)]);

end Kome.Records;
