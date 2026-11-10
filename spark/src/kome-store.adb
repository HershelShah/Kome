pragma Ada_2022;
with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;
with Kome.Crypto;
with Kome.Accumulator; use Kome.Accumulator;
with Kome.Frames;      use Kome.Frames;
package body Kome.Store with SPARK_Mode is

   package KR renames Kome.Records;
   package KD renames Kome.Digest;

   --  Proof style (CONVENTIONS.md): every quantified part of the invariant
   --  is a function of explicit components (Tag_OK, Tags_OK, ...), so each
   --  step of an operation makes one part true again at a time; the steps
   --  that only carry proofs are ghost lemmas, and the loops among them
   --  whose run-time checks would be quadratic run under an Ignore policy
   --  (each is listed in the Wave 2 report for IMPLEMENTATION_PLAN.md).
   --  Helper procedures take the components of a Store (Log, LL, ...), not
   --  the Store, so that the prover keeps every other component equal
   --  logically (an array component compared with Ada "=" would lose
   --  that, CONVENTIONS.md rule 1).

   ---------------------------------------------------------------------------
   --  u24 and tags.
   ---------------------------------------------------------------------------

   procedure Lemma_U24_Round_Trip (V : U24_Value) is
      W : constant Word := Word (V);
   begin
      Kome.Keys.Lemma_Word_Round_Trip (W);
      pragma Assert (W / 256 / 256 / 256 = 0);
      pragma Assert (Kome.Keys.Byte_Of_Word (W, 0) = 0);
      pragma Assert
        (Kome.Keys.Word_Of (0, Kome.Keys.Byte_Of_Word (W, 1), Kome.Keys.Byte_Of_Word (W, 2),
                            Kome.Keys.Byte_Of_Word (W, 3)) = W);
   end Lemma_U24_Round_Trip;

   procedure Lemma_U24_Bytes_Round_Trip (B0, B1, B2 : Byte) is
   begin
      Kome.Keys.Lemma_Lanes_Round_Trip (0, B0, B1, B2);
   end Lemma_U24_Bytes_Round_Trip;

   procedure Lemma_Tag_Round_Trip (Off : Log_Size; Len : Frame_Size) is
      T : constant U64 := Make_Tag (Off, Len);
   begin
      pragma Assert (U64 (Len) < 2**24);
      pragma Assert (U64 (Off) <= 2**30);
      pragma Assert (U64 (Off) * 2**24 <= 2**54);
      pragma Assert (T / 2**24 = U64 (Off));
      pragma Assert (T mod 2**24 = U64 (Len));
      pragma Assert (T / 2**24 <= U64 (Log_Max));
      pragma Assert (Natural (U64 (Off)) = Off);
      pragma Assert (Natural (U64 (Len)) = Len);
      pragma Assert (Tag_Off (T) = Natural (T / 2**24));
      pragma Assert (Tag_Len (T) = Natural (T mod 2**24));
      declare
         Q  : constant U64 := T / 2**24;
         UO : constant U64 := U64 (Off);
      begin
         pragma Assert (Q = UO);
         pragma Assert (Natural (UO) = Off);
         pragma Assert (Natural (Q) = Natural (UO));
         pragma Assert (Natural (T / 2**24) = Natural (Q));
      end;
      pragma Assert (Natural (T / 2**24) = Off);
      pragma Assert (Tag_Off (T) = Off and then Tag_Len (T) = Len);
      pragma Assert (T = Make_Tag (Off, Len));
   end Lemma_Tag_Round_Trip;

   ---------------------------------------------------------------------------
   --  Frames and their headers.
   ---------------------------------------------------------------------------

   procedure Lemma_Header_Of (Cid : Hash256; Frame : Byte_Array) is
   begin
      case KR.Kind_Of (Frame) is
         when K_Put    =>
            pragma Assert (Header_Of (Cid, Frame) = KR.To_Header (Cid, KR.Parse_Put (Frame)));
            pragma Assert (Header_Of (Cid, Frame).K = K_Put);
         when K_Del    =>
            pragma Assert (Header_Of (Cid, Frame) = KR.To_Header (Cid, KR.Parse_Del (Frame)));
            pragma Assert (Header_Of (Cid, Frame).K = K_Del);
         when K_Roster =>
            pragma Assert (Header_Of (Cid, Frame) = KR.To_Header (Cid, KR.Parse_Roster (Frame)));
            pragma Assert (Header_Of (Cid, Frame).K = K_Roster);
         when K_Revoke =>
            pragma Assert (Header_Of (Cid, Frame) = KR.To_Header (Cid, KR.Parse_Revoke (Frame)));
            pragma Assert (Header_Of (Cid, Frame).K = K_Revoke);
         when K_Grant  =>
            pragma Assert (Header_Of (Cid, Frame) = KR.To_Header (Cid, KR.Parse_Grant (Frame)));
            pragma Assert (Header_Of (Cid, Frame).K = K_Grant);
      end case;
   end Lemma_Header_Of;

   procedure Lemma_Verified_Canonical (Cid : Hash256; Root_PK : Pubkey; Frame : Byte_Array) is
      pragma Unreferenced (Root_PK);
   begin
      case KR.Kind_Of (Frame) is
         when K_Put    => KR.Lemma_Header_Canonical (Cid, KR.Parse_Put (Frame));
         when K_Del    => KR.Lemma_Header_Canonical (Cid, KR.Parse_Del (Frame));
         when K_Roster => KR.Lemma_Header_Canonical (Cid, KR.Parse_Roster (Frame));
         when K_Revoke => KR.Lemma_Header_Canonical (Cid, KR.Parse_Revoke (Frame));
         when K_Grant  => KR.Lemma_Header_Canonical (Cid, KR.Parse_Grant (Frame));
      end case;
   end Lemma_Verified_Canonical;

   --  The congruences, one kind at a time. Each reads the parse result
   --  field by field (the Post of Parse_*), then carries the content
   --  hash across the copy with Kome.Crypto.Lemma_Blake2b_Congruent.

   procedure Lemma_Put_Congruent (Cid : Hash256; A, B : Byte_Array) with
     Ghost, Global => null,
     Pre  => KR.Is_Put_Frame (A)
             and then A'Length = B'Length
             and then (for all J in A'Range => B (J - A'First + B'First) = A (J)),
     Post => KR.Is_Put_Frame (B)
             and then KR.To_Header (Cid, KR.Parse_Put (A)) = KR.To_Header (Cid, KR.Parse_Put (B))
   is
      use KR;
      use Kome.Keys;
      FL : constant Natural := Put_FL (A);
   begin
      pragma Assert (B (B'First) = A (A'First));
      pragma Assert (B (B'First + Put_O_FLen) = A (A'First + Put_O_FLen));
      pragma Assert (Put_FL (B) = FL);
      pragma Assert (B (B'First + Put_O_VLen (FL)) = A (A'First + Put_O_VLen (FL)));
      pragma Assert (B (B'First + Put_O_VLen (FL) + 1) = A (A'First + Put_O_VLen (FL) + 1));
      pragma Assert (Put_VL (B) = Put_VL (A));
      pragma Assert (Is_Put_Frame (B));
      declare
         RA : constant Put_Record := Parse_Put (A);
         RB : constant Put_Record := Parse_Put (B);
      begin
         pragma Assert (RB.C.FLen = RA.C.FLen and then RB.C.VLen = RA.C.VLen);
         pragma Assert (for all K in 0 .. 5 =>
                          B (B'First + Put_O_T (FL) + K) = A (A'First + Put_O_T (FL) + K));
         pragma Assert (RB.C.T = RA.C.T);
         pragma Assert (for all K in 0 .. 5 =>
                          B (B'First + Put_O_Seq (FL) + K) = A (A'First + Put_O_Seq (FL) + K));
         pragma Assert (RB.C.Seq = RA.C.Seq);
         pragma Assert (for all I in Ent_Id'Range => RB.C.Ent (I) = RA.C.Ent (I));
         pragma Assert (for all I in Field_Bytes'Range => RB.C.Field (I) = RA.C.Field (I));
         pragma Assert (for all I in Pubkey'Range => RB.C.Author (I) = RA.C.Author (I));
         pragma Assert (for all I in Value_Bytes'Range => RB.C.Value (I) = RA.C.Value (I));
         declare
            CA : constant Byte_Array := Content_Bytes (RA.C);
            CB : constant Byte_Array := Content_Bytes (RB.C);
         begin
            pragma Assert (CA'Length = CB'Length);
            pragma Assert (for all J in 0 .. Content_Len (RA.C) - 1 =>
                             Content_Byte (RB.C, J) = Content_Byte (RA.C, J));
            pragma Assert (for all J in 0 .. Content_Len (RA.C) - 1 => CB (J) = CA (J));
            Kome.Crypto.Lemma_Blake2b_Congruent (Hash_Input (Cid, CA), Hash_Input (Cid, CB));
         end;
         pragma Assert (Hash (Cid, RA.C) = Hash (Cid, RB.C));
         Kome.Crypto.Lemma_Blake2b_Congruent
           (RA.C.Field (0 .. RA.C.FLen - 1), RB.C.Field (0 .. RB.C.FLen - 1));
         pragma Assert (To_Id128 (RA.C.Ent) = To_Id128 (RB.C.Ent));
         pragma Assert (To_Key256 (RA.C.Author) = To_Key256 (RB.C.Author));
         pragma Assert (To_Header (Cid, RA) = To_Header (Cid, RB));
      end;
   end Lemma_Put_Congruent;

   procedure Lemma_Del_Congruent (Cid : Hash256; A, B : Byte_Array) with
     Ghost, Global => null,
     Pre  => KR.Is_Del_Frame (A)
             and then A'Length = B'Length
             and then (for all J in A'Range => B (J - A'First + B'First) = A (J)),
     Post => KR.Is_Del_Frame (B)
             and then KR.To_Header (Cid, KR.Parse_Del (A)) = KR.To_Header (Cid, KR.Parse_Del (B))
   is
      use KR;
      use Kome.Keys;
   begin
      pragma Assert (B (B'First) = A (A'First));
      declare
         RA : constant Del_Record := Parse_Del (A);
         RB : constant Del_Record := Parse_Del (B);
      begin
         pragma Assert (for all K in 0 .. 5 =>
                          B (B'First + Del_O_T + K) = A (A'First + Del_O_T + K));
         pragma Assert (RB.C.T = RA.C.T);
         pragma Assert (for all K in 0 .. 5 =>
                          B (B'First + Del_O_Seq + K) = A (A'First + Del_O_Seq + K));
         pragma Assert (RB.C.Seq = RA.C.Seq);
         pragma Assert (for all I in Ent_Id'Range => RB.C.Ent (I) = RA.C.Ent (I));
         pragma Assert (for all I in Pubkey'Range => RB.C.Author (I) = RA.C.Author (I));
         declare
            CA : constant Byte_Array := Content_Bytes (RA.C);
            CB : constant Byte_Array := Content_Bytes (RB.C);
         begin
            pragma Assert (for all J in 0 .. Del_Content_Len - 1 =>
                             Content_Byte (RB.C, J) = Content_Byte (RA.C, J));
            pragma Assert (for all J in 0 .. Del_Content_Len - 1 => CB (J) = CA (J));
            Kome.Crypto.Lemma_Blake2b_Congruent (Hash_Input (Cid, CA), Hash_Input (Cid, CB));
         end;
         pragma Assert (Hash (Cid, RA.C) = Hash (Cid, RB.C));
         pragma Assert (To_Id128 (RA.C.Ent) = To_Id128 (RB.C.Ent));
         pragma Assert (To_Key256 (RA.C.Author) = To_Key256 (RB.C.Author));
         pragma Assert (To_Header (Cid, RA) = To_Header (Cid, RB));
      end;
   end Lemma_Del_Congruent;

   procedure Lemma_Roster_Congruent (Cid : Hash256; A, B : Byte_Array) with
     Ghost, Global => null,
     Pre  => KR.Is_Roster_Frame (A)
             and then A'Length = B'Length
             and then (for all J in A'Range => B (J - A'First + B'First) = A (J)),
     Post => KR.Is_Roster_Frame (B)
             and then KR.To_Header (Cid, KR.Parse_Roster (A))
                      = KR.To_Header (Cid, KR.Parse_Roster (B))
   is
      use KR;
   begin
      pragma Assert (B (B'First) = A (A'First));
      pragma Assert (B (B'First + Roster_O_NM) = A (A'First + Roster_O_NM));
      pragma Assert (Roster_NM (B) = Roster_NM (A));
      pragma Assert (Is_Roster_Frame (B));
      declare
         RA : constant Roster_Record := Parse_Roster (A);
         RB : constant Roster_Record := Parse_Roster (B);
      begin
         pragma Assert (for all K in 0 .. 5 =>
                          B (B'First + Roster_O_Cert_Cap + K) = A (A'First + Roster_O_Cert_Cap + K));
         pragma Assert (RB.C.Cert_Cap = RA.C.Cert_Cap);
         pragma Assert (for all K in 0 .. 5 =>
                          B (B'First + Roster_O_Gen + K) = A (A'First + Roster_O_Gen + K));
         pragma Assert (RB.C.Gen = RA.C.Gen);
         pragma Assert (for all K in 0 .. 5 =>
                          B (B'First + Roster_O_Ceiling + K) = A (A'First + Roster_O_Ceiling + K));
         pragma Assert (RB.C.Ceiling_T = RA.C.Ceiling_T);
         pragma Assert (RB.C.N_Members = RA.C.N_Members);
         pragma Assert (for all I in Pubkey'Range => RB.C.Signer (I) = RA.C.Signer (I));
         pragma Assert (for all I in Sig'Range => RB.C.Cert_Sig (I) = RA.C.Cert_Sig (I));
         pragma Assert (for all I in Pubkey'Range => RB.C.Box_PK (I) = RA.C.Box_PK (I));
         pragma Assert (for all I in Members_Bytes'Range => RB.C.Members (I) = RA.C.Members (I));
         declare
            CA : constant Byte_Array := Content_Bytes (RA.C);
            CB : constant Byte_Array := Content_Bytes (RB.C);
         begin
            pragma Assert (CA'Length = CB'Length);
            pragma Assert (for all J in 0 .. Content_Len (RA.C) - 1 =>
                             Content_Byte (RB.C, J) = Content_Byte (RA.C, J));
            pragma Assert (for all J in 0 .. Content_Len (RA.C) - 1 => CB (J) = CA (J));
            Kome.Crypto.Lemma_Blake2b_Congruent (Hash_Input (Cid, CA), Hash_Input (Cid, CB));
         end;
         pragma Assert (Hash (Cid, RA.C) = Hash (Cid, RB.C));
         pragma Assert (Signer_Key (RA) = Signer_Key (RB));
         pragma Assert (To_Header (Cid, RA) = To_Header (Cid, RB));
      end;
   end Lemma_Roster_Congruent;

   procedure Lemma_Revoke_Congruent (Cid : Hash256; A, B : Byte_Array) with
     Ghost, Global => null,
     Pre  => KR.Is_Revoke_Frame (A)
             and then A'Length = B'Length
             and then (for all J in A'Range => B (J - A'First + B'First) = A (J)),
     Post => KR.Is_Revoke_Frame (B)
             and then KR.To_Header (Cid, KR.Parse_Revoke (A))
                      = KR.To_Header (Cid, KR.Parse_Revoke (B))
   is
      use KR;
      use Kome.Keys;
   begin
      pragma Assert (B (B'First) = A (A'First));
      declare
         RA : constant Revoke_Record := Parse_Revoke (A);
         RB : constant Revoke_Record := Parse_Revoke (B);
      begin
         pragma Assert (for all K in 0 .. 5 =>
                          B (B'First + Revoke_O_Cert_Cap + K) = A (A'First + Revoke_O_Cert_Cap + K));
         pragma Assert (RB.C.Cert_Cap = RA.C.Cert_Cap);
         pragma Assert (for all K in 0 .. 5 =>
                          B (B'First + Revoke_O_From_T + K) = A (A'First + Revoke_O_From_T + K));
         pragma Assert (RB.C.From_T = RA.C.From_T);
         pragma Assert (for all I in Pubkey'Range => RB.C.Signer (I) = RA.C.Signer (I));
         pragma Assert (for all I in Sig'Range => RB.C.Cert_Sig (I) = RA.C.Cert_Sig (I));
         pragma Assert (for all I in Pubkey'Range => RB.C.Sign_PK (I) = RA.C.Sign_PK (I));
         declare
            CA : constant Byte_Array := Content_Bytes (RA.C);
            CB : constant Byte_Array := Content_Bytes (RB.C);
         begin
            pragma Assert (for all J in 0 .. Revoke_Content_Len - 1 =>
                             Content_Byte (RB.C, J) = Content_Byte (RA.C, J));
            pragma Assert (for all J in 0 .. Revoke_Content_Len - 1 => CB (J) = CA (J));
            Kome.Crypto.Lemma_Blake2b_Congruent (Hash_Input (Cid, CA), Hash_Input (Cid, CB));
         end;
         pragma Assert (Hash (Cid, RA.C) = Hash (Cid, RB.C));
         pragma Assert (Signer_Key (RA) = Signer_Key (RB));
         pragma Assert (To_Key256 (RA.C.Sign_PK) = To_Key256 (RB.C.Sign_PK));
         pragma Assert (To_Header (Cid, RA) = To_Header (Cid, RB));
      end;
   end Lemma_Revoke_Congruent;

   procedure Lemma_Grant_Congruent (Cid : Hash256; A, B : Byte_Array) with
     Ghost, Global => null,
     Pre  => KR.Is_Grant_Frame (A)
             and then A'Length = B'Length
             and then (for all J in A'Range => B (J - A'First + B'First) = A (J)),
     Post => KR.Is_Grant_Frame (B)
             and then KR.To_Header (Cid, KR.Parse_Grant (A))
                      = KR.To_Header (Cid, KR.Parse_Grant (B))
   is
      use KR;
      use Kome.Keys;
   begin
      pragma Assert (B (B'First) = A (A'First));
      declare
         RA : constant Grant_Record := Parse_Grant (A);
         RB : constant Grant_Record := Parse_Grant (B);
      begin
         pragma Assert (for all K in 0 .. 5 =>
                          B (B'First + Grant_O_Cert_Cap + K) = A (A'First + Grant_O_Cert_Cap + K));
         pragma Assert (RB.C.Cert_Cap = RA.C.Cert_Cap);
         pragma Assert (for all I in Pubkey'Range => RB.C.Signer (I) = RA.C.Signer (I));
         pragma Assert (for all I in Sig'Range => RB.C.Cert_Sig (I) = RA.C.Cert_Sig (I));
         pragma Assert (for all I in Pubkey'Range => RB.C.Subject (I) = RA.C.Subject (I));
         declare
            CA : constant Byte_Array := Content_Bytes (RA.C);
            CB : constant Byte_Array := Content_Bytes (RB.C);
         begin
            pragma Assert (for all J in 0 .. Grant_Content_Len - 1 =>
                             Content_Byte (RB.C, J) = Content_Byte (RA.C, J));
            pragma Assert (for all J in 0 .. Grant_Content_Len - 1 => CB (J) = CA (J));
            Kome.Crypto.Lemma_Blake2b_Congruent (Hash_Input (Cid, CA), Hash_Input (Cid, CB));
         end;
         pragma Assert (Hash (Cid, RA.C) = Hash (Cid, RB.C));
         pragma Assert (Signer_Key (RA) = Signer_Key (RB));
         pragma Assert (To_Key256 (RA.C.Subject) = To_Key256 (RB.C.Subject));
         pragma Assert (To_Header (Cid, RA) = To_Header (Cid, RB));
      end;
   end Lemma_Grant_Congruent;

   procedure Lemma_Header_Of_Congruent (Cid : Hash256; A, B : Byte_Array) is
   begin
      pragma Assert (B (B'First) = A (A'First));
      pragma Assert (KR.Has_Kind (B) and then KR.Kind_Of (B) = KR.Kind_Of (A));
      case KR.Kind_Of (A) is
         when K_Put    => Lemma_Put_Congruent (Cid, A, B);
         when K_Del    => Lemma_Del_Congruent (Cid, A, B);
         when K_Roster => Lemma_Roster_Congruent (Cid, A, B);
         when K_Revoke => Lemma_Revoke_Congruent (Cid, A, B);
         when K_Grant  => Lemma_Grant_Congruent (Cid, A, B);
      end case;
   end Lemma_Header_Of_Congruent;

   --  Tag_OK reads a frame through Kome.Frames.Frame_Is, which is opaque
   --  here: a goal about tags then never unfolds Header_Of and the
   --  Kome.Records parsers unless it asks for them (Lemma_Frame_Is_Def).

   ---------------------------------------------------------------------------
   --  The parts of the invariant, over explicit components.
   ---------------------------------------------------------------------------

   --  Each part below is a function whose Post defines it, so that a goal
   --  that only carries a part along sees one atom, and a quantified part
   --  is instantiated on the atom (CONVENTIONS.md).

   --  The HEADER of (Root, Slt, TTL) is Log (0 .. Header_Len - 1).
   function Head_OK (Log : Byte_Array; LL : Log_Size; Root : Pubkey; Slt : Salt; TTL : U48)
     return Boolean
   with Global => null,
        Pre  => Log'First = 0 and then LL <= Log'Last,
        Post => Head_OK'Result =
          (LL >= Header_Len
           and then (for all J in 0 .. Magic_Len - 1 => Log (J) = Magic (J))
           and then Log (HO_Version) = Log_Version
           and then (for all J in 0 .. Pubkey_Len - 1 => Log (HO_Root + J) = Root (J))
           and then (for all J in 0 .. Salt_Len - 1 => Log (HO_Salt + J) = Slt (J))
           and then KR.U48_Of (Log (HO_TTL), Log (HO_TTL + 1), Log (HO_TTL + 2),
                               Log (HO_TTL + 3), Log (HO_TTL + 4), Log (HO_TTL + 5)) = TTL);

   function Head_OK (Log : Byte_Array; LL : Log_Size; Root : Pubkey; Slt : Salt; TTL : U48)
     return Boolean is
   begin
      return LL >= Header_Len
        and then (for all J in 0 .. Magic_Len - 1 => Log (J) = Magic (J))
        and then Log (HO_Version) = Log_Version
        and then (for all J in 0 .. Pubkey_Len - 1 => Log (HO_Root + J) = Root (J))
        and then (for all J in 0 .. Salt_Len - 1 => Log (HO_Salt + J) = Slt (J))
        and then KR.U48_Of (Log (HO_TTL), Log (HO_TTL + 1), Log (HO_TTL + 2),
                            Log (HO_TTL + 3), Log (HO_TTL + 4), Log (HO_TTL + 5)) = TTL;
   end Head_OK;

   --  The frame of the APPLY at Tag_Off (T), as a slice of Log.
   function Slice_At (Log : Byte_Array; T : U64) return Byte_Array is
     (Log (Tag_Off (T) + Apply_Prefix .. Tag_Off (T) + Apply_Prefix + Tag_Len (T) - 1))
   with Ghost,
        Pre => Log'First = 0 and then Tag_Off (T) <= Log_Max
               and then Tag_Off (T) + Apply_Prefix + Tag_Len (T) - 1 <= Log'Last;

   --  S14: the tag T of the record X points at an entry with the op byte
   --  Op of Log (0 .. LL - 1), after the HEADER, whose frame has the header
   --  X. Op is Op_Apply for a held record (Tags_OK) and Op_Ceil for the
   --  record of the ceiling cell (Ceil_OK; AUDIT.md H12).
   function Tag_OK
     (Log : Byte_Array; LL : Log_Size; Cid : Hash256; X : Header; T : U64; Op : Byte)
     return Boolean
   with Ghost, Global => null,
        Pre  => Log'First = 0 and then LL <= Log'Last,
        Post => Tag_OK'Result =
          (Tag_Len (T) in Frame_Size
           and then Tag_Off (T) >= Header_Len
           and then Tag_Off (T) <= LL
           and then LL - Tag_Off (T) >= Apply_Prefix + Tag_Len (T)
           and then Log (Tag_Off (T)) = Op
           and then U24_Of (Log (Tag_Off (T) + 1), Log (Tag_Off (T) + 2), Log (Tag_Off (T) + 3))
                    = Tag_Len (T)
           and then Frame_Is (Slice_At (Log, T), Cid, X));

   function Tag_OK
     (Log : Byte_Array; LL : Log_Size; Cid : Hash256; X : Header; T : U64; Op : Byte)
     return Boolean is
   begin
      return Tag_Len (T) in Frame_Size
        and then Tag_Off (T) >= Header_Len
        and then Tag_Off (T) <= LL
        and then LL - Tag_Off (T) >= Apply_Prefix + Tag_Len (T)
        and then Log (Tag_Off (T)) = Op
        and then U24_Of (Log (Tag_Off (T) + 1), Log (Tag_Off (T) + 2), Log (Tag_Off (T) + 3))
                 = Tag_Len (T)
        and then Frame_Is (Slice_At (Log, T), Cid, X);
   end Tag_OK;

   --  The bounds of a tag that Tag_OK accepts, on their own: in the large
   --  context of Lemma_Tag the provers do not find them in Tag_OK's Post
   --  at the project's proof level.
   procedure Lemma_Tag_OK_Bounds
     (Log : Byte_Array; LL : Log_Size; Cid : Hash256; X : Header; T : U64; Op : Byte)
   with Ghost, Global => null,
        Pre  => Log'First = 0 and then LL <= Log'Last
                and then Tag_OK (Log, LL, Cid, X, T, Op),
        Post => Tag_Len (T) in Frame_Size
                and then Tag_Off (T) >= Header_Len
                and then Tag_Off (T) <= LL
                and then LL - Tag_Off (T) >= Apply_Prefix + Tag_Len (T);

   procedure Lemma_Tag_OK_Bounds
     (Log : Byte_Array; LL : Log_Size; Cid : Hash256; X : Header; T : U64; Op : Byte) is null;

   function Tags_OK (Log : Byte_Array; LL : Log_Size; Cid : Hash256; F : Frontier.State)
     return Boolean
   with Ghost, Global => null,
        Pre  => Log'First = 0 and then LL <= Log'Last,
        Post => Tags_OK'Result =
          (for all I in 1 .. Count (F) =>
             Tag_OK (Log, LL, Cid, Held (F, I), Tag (F, I), Op_Apply));

   function Tags_OK (Log : Byte_Array; LL : Log_Size; Cid : Hash256; F : Frontier.State)
     return Boolean is
   begin
      return (for all I in 1 .. Count (F) =>
                Tag_OK (Log, LL, Cid, Held (F, I), Tag (F, I), Op_Apply));
   end Tags_OK;

   --  Tags_OK from its quantified form (a small context).
   procedure Lemma_Tags_OK_Intro (Log : Byte_Array; LL : Log_Size; Cid : Hash256; F : Frontier.State)
   with
     Ghost, Global => null,
     Pre  => Log'First = 0 and then LL <= Log'Last
             and then (for all I in 1 .. Count (F) =>
                         Tag_OK (Log, LL, Cid, Held (F, I), Tag (F, I), Op_Apply)),
     Post => Tags_OK (Log, LL, Cid, F)
   is
   begin
      null;
   end Lemma_Tags_OK_Intro;

   --  AUDIT.md H12: the tag of the ceiling cell's record, if there is one,
   --  points at a CEIL entry whose frame has that record as its header.
   function Ceil_OK (Log : Byte_Array; LL : Log_Size; Cid : Hash256; F : Frontier.State)
     return Boolean
   with Ghost, Global => null,
        Pre  => Log'First = 0 and then LL <= Log'Last,
        Post => Ceil_OK'Result =
          (if Has_Ceil (F) then Tag_OK (Log, LL, Cid, Ceil_Held (F), Ceil_Tag (F), Op_Ceil));

   function Ceil_OK (Log : Byte_Array; LL : Log_Size; Cid : Hash256; F : Frontier.State)
     return Boolean is
   begin
      return (if Has_Ceil (F) then Tag_OK (Log, LL, Cid, Ceil_Held (F), Ceil_Tag (F), Op_Ceil));
   end Ceil_OK;

   --  T11 (a): no held record is a DEL at or below the horizon.
   function Fresh (F : Frontier.State; TTL : U48) return Boolean
   with Global => null,
        Post => Fresh'Result = (for all I in 1 .. Count (F) => not Expired_In (Held (F, I), F, TTL));

   function Fresh (F : Frontier.State; TTL : U48) return Boolean is
   begin
      return (for all I in 1 .. Count (F) => not Expired_In (Held (F, I), F, TTL));
   end Fresh;

   --  S16: seq_self bounds every held own seq.
   function Seq_OK (F : Frontier.State; Self : Key256; SS : U48) return Boolean
   with Global => null,
        Post => Seq_OK'Result =
          (for all I in 1 .. Count (F) =>
             (if Is_Data (Held (F, I)) and then Held (F, I).V.Author = Self
              then Held (F, I).V.Seq <= SS));

   function Seq_OK (F : Frontier.State; Self : Key256; SS : U48) return Boolean is
   begin
      return (for all I in 1 .. Count (F) =>
                (if Is_Data (Held (F, I)) and then Held (F, I).V.Author = Self
                 then Held (F, I).V.Seq <= SS));
   end Seq_OK;

   --  S21: the digests model the two row sets.
   function Digests_OK (F : Frontier.State; DA, DD : KD.Digest_State) return Boolean is
     (KD.Models (DA, Auth_Hashes (F), Auth_Count (F))
      and then KD.Models (DD, Data_Hashes (F), Data_Count (F)))
   with Ghost;

   function Data_Hashes (F : Frontier.State) return KD.Hash_Array is
      L : KD.Hash_Array (1 .. Data_Count (F)) := [others => (others => 0)];
   begin
      for I in 1 .. Data_Count (F) loop
         L (I) := Data_Held (F, I).V.H;
         pragma Loop_Invariant (for all J in 1 .. I => L (J) = Data_Held (F, J).V.H);
      end loop;
      return L;
   end Data_Hashes;

   function Auth_Hashes (F : Frontier.State) return KD.Hash_Array is
      L : KD.Hash_Array (1 .. Auth_Count (F)) := [others => (others => 0)];
   begin
      for I in 1 .. Auth_Count (F) loop
         L (I) := Held (F, Data_Count (F) + I).V.H;
         pragma Loop_Invariant
           (for all J in 1 .. I => L (J) = Held (F, Data_Count (F) + J).V.H);
      end loop;
      return L;
   end Auth_Hashes;

   function Valid (S : Store; F : Frontier.State) return Boolean is
     (S.LL <= S.Log_Cap
      and then S.NE <= S.LL
      and then Is_Frontier (F)
      and then Frontier.Founding (F) = S.Fnd
      and then S.Fnd = Kome.Keys.To_Key256 (S.Root)
      and then S.TTL in Del_TTL_Min .. Del_TTL_Max
      and then S.Cid = KR.Cid_Of (S.Root, S.Slt, S.TTL)
      and then Head_OK (S.Log, S.LL, S.Root, S.Slt, S.TTL)
      and then Tags_OK (S.Log, S.LL, S.Cid, F)
      and then Ceil_OK (S.Log, S.LL, S.Cid, F)
      and then Fresh (F, S.TTL)
      and then Seq_OK (F, S.Self, S.SS)
      and then Digests_OK (F, S.DA, S.DD));

   --  Valid, unpacked into its parts and packed again, so that an
   --  operation reads and makes the invariant in a small context.
   procedure Lemma_Valid_Parts (S : Store; F : Frontier.State) with
     Ghost, Global => null,
     Pre  => Valid (S, F),
     Post => S.LL <= S.Log_Cap
       and then S.NE <= S.LL
       and then Is_Frontier (F)
       and then Frontier.Founding (F) = S.Fnd
       and then S.Fnd = Kome.Keys.To_Key256 (S.Root)
       and then S.TTL in Del_TTL_Min .. Del_TTL_Max
       and then S.Cid = KR.Cid_Of (S.Root, S.Slt, S.TTL)
       and then Head_OK (S.Log, S.LL, S.Root, S.Slt, S.TTL)
       and then Tags_OK (S.Log, S.LL, S.Cid, F)
       and then Ceil_OK (S.Log, S.LL, S.Cid, F)
       and then Fresh (F, S.TTL)
       and then Seq_OK (F, S.Self, S.SS)
       and then KD.Models (S.DA, Auth_Hashes (F), Auth_Count (F))
       and then KD.Models (S.DD, Data_Hashes (F), Data_Count (F))
   is
   begin
      null;
   end Lemma_Valid_Parts;

   procedure Lemma_Valid_Of_Parts (S : Store; F : Frontier.State) with
     Ghost, Global => null,
     Pre  => S.LL <= S.Log_Cap
       and then S.NE <= S.LL
       and then Is_Frontier (F)
       and then Frontier.Founding (F) = S.Fnd
       and then S.Fnd = Kome.Keys.To_Key256 (S.Root)
       and then S.TTL in Del_TTL_Min .. Del_TTL_Max
       and then S.Cid = KR.Cid_Of (S.Root, S.Slt, S.TTL)
       and then Head_OK (S.Log, S.LL, S.Root, S.Slt, S.TTL)
       and then Tags_OK (S.Log, S.LL, S.Cid, F)
       and then Ceil_OK (S.Log, S.LL, S.Cid, F)
       and then Fresh (F, S.TTL)
       and then Seq_OK (F, S.Self, S.SS)
       and then KD.Models (S.DA, Auth_Hashes (F), Auth_Count (F))
       and then KD.Models (S.DD, Data_Hashes (F), Data_Count (F)),
     Post => Valid (S, F)
   is
   begin
      null;
   end Lemma_Valid_Of_Parts;

   --  The index at which F holds X (ghost).
   function Index_Of (F : Frontier.State; X : Header) return Held_Index with
     Ghost, Global => null,
     Pre  => Holds (F, X),
     Post => Index_Of'Result <= Count (F) and then Held (F, Index_Of'Result) = X
   is
   begin
      for I in 1 .. Count (F) loop
         if Held (F, I) = X then
            return I;
         end if;
         pragma Loop_Invariant (for all I2 in 1 .. I => Held (F, I2) /= X);
      end loop;
      raise Program_Error;
   end Index_Of;

   ---------------------------------------------------------------------------
   --  Carrying the parts across a change.
   ---------------------------------------------------------------------------

   --  A tag stays good when the log grows: its frame's bytes are the same
   --  (Lemma_Frame_Is_Congruent).
   procedure Lemma_Tag_OK_Kept
     (Log0 : Byte_Array; LL0 : Log_Size; Log1 : Byte_Array; LL1 : Log_Size;
      Cid  : Hash256; X : Header; T : U64; Op : Byte)
   with
     Ghost, Global => null,
     Pre  => Log0'First = 0 and then LL0 <= Log0'Last
             and then Log1'First = 0 and then LL1 <= Log1'Last
             and then LL0 <= LL1
             and then (for all J in 0 .. LL0 - 1 => Log1 (J) = Log0 (J))
             and then Tag_OK (Log0, LL0, Cid, X, T, Op),
     Post => Tag_OK (Log1, LL1, Cid, X, T, Op)
   is
      O : constant Natural := Tag_Off (T);
      L : constant Natural := Tag_Len (T);
   begin
      pragma Assert (Tag_OK (Log0, LL0, Cid, X, T, Op));
      pragma Assert (L in Frame_Size and then O >= Header_Len and then O <= LL0);
      pragma Assert (O + Apply_Prefix + L <= LL0);
      pragma Assert (Frame_Is (Slice_At (Log0, T), Cid, X));
      pragma Assert (Log1 (O) = Log0 (O));
      pragma Assert (Log1 (O + 1) = Log0 (O + 1) and then Log1 (O + 2) = Log0 (O + 2)
                     and then Log1 (O + 3) = Log0 (O + 3));
      pragma Assert (for all J in O + Apply_Prefix .. O + Apply_Prefix + L - 1 =>
                       Log1 (J) = Log0 (J));
      pragma Assert (for all J in Slice_At (Log0, T)'Range =>
                       Slice_At (Log1, T) (J) = Slice_At (Log0, T) (J));
      Lemma_Frame_Is_Congruent (Cid, X, Slice_At (Log0, T), Slice_At (Log1, T));
      pragma Assert (Log1 (O) = Op);
      pragma Assert (U24_Of (Log1 (O + 1), Log1 (O + 2), Log1 (O + 3)) = L);
   end Lemma_Tag_OK_Kept;

   --  Every tag of F stays good when the log grows.
   procedure Lemma_Tags_Kept
     (Log0 : Byte_Array; LL0 : Log_Size; Log1 : Byte_Array; LL1 : Log_Size;
      Cid  : Hash256; F : Frontier.State)
   with
     Ghost, Global => null,
     Pre  => Log0'First = 0 and then LL0 <= Log0'Last
             and then Log1'First = 0 and then LL1 <= Log1'Last
             and then LL0 <= LL1
             and then (for all J in 0 .. LL0 - 1 => Log1 (J) = Log0 (J))
             and then Tags_OK (Log0, LL0, Cid, F),
     Post => Tags_OK (Log1, LL1, Cid, F)
   is
      --  Proved; at run time the invariant would cost O(n^2) per call.
      pragma Assertion_Policy (Loop_Invariant => Ignore);
   begin
      for I in 1 .. Count (F) loop
         Lemma_Tag_OK_Kept (Log0, LL0, Log1, LL1, Cid, Held (F, I), Tag (F, I), Op_Apply);
         pragma Loop_Invariant
           (for all I2 in 1 .. I => Tag_OK (Log1, LL1, Cid, Held (F, I2), Tag (F, I2), Op_Apply));
      end loop;
   end Lemma_Tags_Kept;

   --  The cell's tag stays good when the log grows and the cell is the
   --  same (AUDIT.md H12).
   procedure Lemma_Ceil_Kept
     (Log0 : Byte_Array; LL0 : Log_Size; Log1 : Byte_Array; LL1 : Log_Size;
      Cid  : Hash256; F0, F1 : Frontier.State)
   with
     Ghost, Global => null,
     Pre  => Log0'First = 0 and then LL0 <= Log0'Last
             and then Log1'First = 0 and then LL1 <= Log1'Last
             and then LL0 <= LL1
             and then (for all J in 0 .. LL0 - 1 => Log1 (J) = Log0 (J))
             and then Ceil_OK (Log0, LL0, Cid, F0)
             and then Ceil_Same (F0, F1),
     Post => Ceil_OK (Log1, LL1, Cid, F1)
   is
   begin
      if Has_Ceil (F0) then
         Lemma_Tag_OK_Kept
           (Log0, LL0, Log1, LL1, Cid, Ceil_Held (F0), Ceil_Tag (F0), Op_Ceil);
      end if;
   end Lemma_Ceil_Kept;

   --  The HEADER stays when the log grows.
   procedure Lemma_Head_Kept
     (Log0 : Byte_Array; LL0 : Log_Size; Log1 : Byte_Array; LL1 : Log_Size;
      Root : Pubkey; Slt : Salt; TTL : U48)
   with
     Ghost, Global => null,
     Pre  => Log0'First = 0 and then LL0 <= Log0'Last
             and then Log1'First = 0 and then LL1 <= Log1'Last
             and then LL0 <= LL1
             and then (for all J in 0 .. LL0 - 1 => Log1 (J) = Log0 (J))
             and then Head_OK (Log0, LL0, Root, Slt, TTL),
     Post => Head_OK (Log1, LL1, Root, Slt, TTL)
   is
   begin
      pragma Assert (for all J in 0 .. Header_Len - 1 => Log1 (J) = Log0 (J));
   end Lemma_Head_Kept;

   --  The HEADER stays when its bytes stay (Compact rewrites the rest).
   procedure Lemma_Head_Same
     (Log0 : Byte_Array; LL0 : Log_Size; Log1 : Byte_Array; LL1 : Log_Size;
      Root : Pubkey; Slt : Salt; TTL : U48)
   with
     Ghost, Global => null,
     Pre  => Log0'First = 0 and then LL0 <= Log0'Last
             and then Log1'First = 0 and then LL1 <= Log1'Last
             and then LL1 >= Header_Len
             and then Head_OK (Log0, LL0, Root, Slt, TTL)
             and then (for all J in 0 .. Header_Len - 1 => Log1 (J) = Log0 (J)),
     Post => Head_OK (Log1, LL1, Root, Slt, TTL)
   is
   begin
      pragma Assert (Log1 (HO_Version) = Log0 (HO_Version));
      pragma Assert (for all J in 0 .. 5 => Log1 (HO_TTL + J) = Log0 (HO_TTL + J));
   end Lemma_Head_Same;

   --  The same records with the same tags keep the tags good.
   procedure Lemma_Tags_Same
     (Log : Byte_Array; LL : Log_Size; Cid : Hash256; F0, F1 : Frontier.State)
   with
     Ghost, Global => null,
     Pre  => Log'First = 0 and then LL <= Log'Last
             and then Tags_OK (Log, LL, Cid, F0)
             and then Count (F1) = Count (F0)
             and then (for all I in 1 .. Count (F0) =>
                         Held (F1, I) = Held (F0, I) and then Tag (F1, I) = Tag (F0, I)),
     Post => Tags_OK (Log, LL, Cid, F1)
   is
      --  Proved; at run time the invariant would cost O(n^2) per call.
      pragma Assertion_Policy (Loop_Invariant => Ignore);
   begin
      for I in 1 .. Count (F1) loop
         pragma Assert (Tag_OK (Log, LL, Cid, Held (F0, I), Tag (F0, I), Op_Apply));
         pragma Loop_Invariant
           (for all I2 in 1 .. I => Tag_OK (Log, LL, Cid, Held (F1, I2), Tag (F1, I2), Op_Apply));
      end loop;
   end Lemma_Tags_Same;

   --  The same records under the same Max_Ceil are as fresh, and as far
   --  below seq_self.
   procedure Lemma_Rest_Same
     (F0, F1 : Frontier.State; TTL : U48; Self : Key256; SS : U48)
   with
     Ghost, Global => null,
     Pre  => Fresh (F0, TTL) and then Seq_OK (F0, Self, SS)
             and then Count (F1) = Count (F0)
             and then Max_Ceil (F1) = Max_Ceil (F0)
             and then (for all I in 1 .. Count (F0) => Held (F1, I) = Held (F0, I)),
     Post => Fresh (F1, TTL) and then Seq_OK (F1, Self, SS)
   is
      --  Proved; at run time the invariants would cost O(n^2) per call.
      pragma Assertion_Policy (Loop_Invariant => Ignore);
   begin
      for I in 1 .. Count (F1) loop
         pragma Assert (not Expired_In (Held (F0, I), F0, TTL));
         pragma Assert
           (if Is_Data (Held (F0, I)) and then Held (F0, I).V.Author = Self
            then Held (F0, I).V.Seq <= SS);
         pragma Loop_Invariant
           (for all I2 in 1 .. I => not Expired_In (Held (F1, I2), F1, TTL));
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              (if Is_Data (Held (F1, I2)) and then Held (F1, I2).V.Author = Self
               then Held (F1, I2).V.Seq <= SS));
      end loop;
   end Lemma_Rest_Same;

   --  The same records are as far below seq_self, whatever Max_Ceil is
   --  (a capture raises it, AUDIT.md H12).
   procedure Lemma_Seq_Same (F0, F1 : Frontier.State; Self : Key256; SS : U48) with
     Ghost, Global => null,
     Pre  => Seq_OK (F0, Self, SS)
             and then Count (F1) = Count (F0)
             and then (for all I in 1 .. Count (F0) => Held (F1, I) = Held (F0, I)),
     Post => Seq_OK (F1, Self, SS)
   is
      --  Proved; at run time the invariant would cost O(n^2) per call.
      pragma Assertion_Policy (Loop_Invariant => Ignore);
   begin
      for I in 1 .. Count (F1) loop
         pragma Assert
           (if Is_Data (Held (F0, I)) and then Held (F0, I).V.Author = Self
            then Held (F0, I).V.Seq <= SS);
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              (if Is_Data (Held (F1, I2)) and then Held (F1, I2).V.Author = Self
               then Held (F1, I2).V.Seq <= SS));
      end loop;
   end Lemma_Seq_Same;

   --  The same rows give the same hash lists.
   procedure Lemma_Hashes_Same (F0, F1 : Frontier.State) with
     Ghost, Global => null,
     Pre  => Is_Frontier (F0) and then Is_Frontier (F1)
             and then Data_Count (F1) = Data_Count (F0)
             and then Count (F1) = Count (F0)
             and then (for all I in 1 .. Data_Count (F0) => Data_Held (F1, I) = Data_Held (F0, I))
             and then (for all I in 1 .. Count (F0) => Held (F1, I) = Held (F0, I)),
     Post => (for all I in 1 .. Data_Count (F0) =>
                Data_Hashes (F1) (I) = Data_Hashes (F0) (I))
             and then Auth_Count (F1) = Auth_Count (F0)
             and then (for all I in 1 .. Auth_Count (F0) =>
                         Auth_Hashes (F1) (I) = Auth_Hashes (F0) (I))
   is
      --  Proved; at run time the invariant would cost O(n^2) per call.
      pragma Assertion_Policy (Loop_Invariant => Ignore);
   begin
      for I in 1 .. Auth_Count (F0) loop
         pragma Assert (Held (F1, Data_Count (F1) + I) = Held (F0, Data_Count (F0) + I));
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              Held (F1, Data_Count (F1) + I2) = Held (F0, Data_Count (F0) + I2));
      end loop;
   end Lemma_Hashes_Same;

   ---------------------------------------------------------------------------
   --  Sums over ranges of a hash list (S21).
   ---------------------------------------------------------------------------

   --  A range that moved by D has the same sum.
   procedure Lemma_Sum_Shift
     (L0, L1 : KD.Hash_Array; Lo : KD.Lo_Bound; Hi : KD.Elem_Count; D : Integer)
   with
     Ghost, Global => null,
     Pre  => D in -(KD.Elem_Max + 1) .. KD.Elem_Max + 1
             and then Lo + D >= 1 and then Lo + D <= KD.Elem_Max + 1
             and then Hi + D >= 0 and then Hi + D <= KD.Elem_Max
             and then (if Lo <= Hi then
                         Lo >= L0'First and then Hi <= L0'Last
                         and then Lo + D >= L1'First and then Hi + D <= L1'Last
                         and then (for all I in Lo .. Hi => L1 (I + D) = L0 (I))),
     Post => KD.Sum_Of (L1, Lo + D, Hi + D) = KD.Sum_Of (L0, Lo, Hi),
     Subprogram_Variant => (Decreases => Hi)
   is
   begin
      if Hi < Lo then
         KD.Lemma_Sum_Of_Empty (L0, Lo, Hi);
         KD.Lemma_Sum_Of_Empty (L1, Lo + D, Hi + D);
      else
         Lemma_Sum_Shift (L0, L1, Lo, Hi - 1, D);
         KD.Lemma_Sum_Of_Step (L0, Lo, Hi);
         KD.Lemma_Sum_Of_Step (L1, Lo + D, Hi + D);
         pragma Assert (L1 (Hi + D) = L0 (Hi));
         Lemma_Add_Congruent
           (KD.Sum_Of (L1, Lo + D, Hi + D - 1), KD.Sum_Of (L0, Lo, Hi - 1),
            KD.Elem_Acc (L1 (Hi + D)), KD.Elem_Acc (L0 (Hi)));
         Lemma_Eq_Iff_Value
           (KD.Sum_Of (L1, Lo + D, Hi + D),
            Add (KD.Sum_Of (L1, Lo + D, Hi + D - 1), KD.Elem_Acc (L1 (Hi + D))));
         Lemma_Eq_Iff_Value
           (Add (KD.Sum_Of (L1, Lo + D, Hi + D - 1), KD.Elem_Acc (L1 (Hi + D))),
            Add (KD.Sum_Of (L0, Lo, Hi - 1), KD.Elem_Acc (L0 (Hi))));
         Lemma_Eq_Iff_Value
           (Add (KD.Sum_Of (L0, Lo, Hi - 1), KD.Elem_Acc (L0 (Hi))), KD.Sum_Of (L0, Lo, Hi));
         Lemma_Eq_Iff_Value (KD.Sum_Of (L1, Lo + D, Hi + D), KD.Sum_Of (L0, Lo, Hi));
      end if;
   end Lemma_Sum_Shift;

   --  The algebra of a range replacement: take R0 out of P + (R0 + Q) and
   --  put R1 in.
   procedure Lemma_Replace (P, R0, Q, R1 : Acc) with
     Ghost, Global => null,
     Post => Value (Add (Sub (Add (P, Add (R0, Q)), R0), R1)) = Value (Add (P, Add (R1, Q)))
   is
      X : constant Acc := Add (P, Add (R0, Q));
   begin
      --  X = (P + Q) + R0.
      Lemma_Add_Comm (R0, Q);
      Lemma_Eq_Iff_Value (Add (R0, Q), Add (Q, R0));
      Lemma_Add_Assoc (P, Q, R0);
      Lemma_Eq_Iff_Value (Add (Add (P, Q), R0), Add (P, Add (Q, R0)));
      pragma Assert (Value (X) = Value (Add (Add (P, Q), R0)));
      --  X - R0 = P + Q.
      Lemma_Sub_Add (Add (P, Q), R0);
      Lemma_Eq_Iff_Value (Sub (Add (Add (P, Q), R0), R0), Add (P, Q));
      pragma Assert (Value (Sub (X, R0)) = Value (Add (P, Q)));
      --  (P + Q) + R1 = P + (R1 + Q).
      Lemma_Add_Assoc (P, Q, R1);
      Lemma_Eq_Iff_Value (Add (Add (P, Q), R1), Add (P, Add (Q, R1)));
      Lemma_Add_Comm (Q, R1);
      Lemma_Eq_Iff_Value (Add (Q, R1), Add (R1, Q));
      pragma Assert (Value (Add (Sub (X, R0), R1)) = Value (Add (Add (P, Q), R1)));
      pragma Assert (Value (Add (Add (P, Q), R1)) = Value (Add (P, Add (R1, Q))));
   end Lemma_Replace;

   --  S21: the digest of a list after one range of it changed. L0 (1 .. N0)
   --  becomes L1 (1 .. N1): the prefix before A is the same, the range
   --  A .. B0 became A .. B1, and the suffix after it moved. The state of
   --  L1 is the state of L0 minus the old range plus the new range.
   procedure Lemma_Range_Diff
     (D0 : KD.Digest_State; L0, L1 : KD.Hash_Array; N0, N1 : KD.Elem_Count;
      A : KD.Lo_Bound; B0, B1 : KD.Elem_Count; Old_Sum, New_Sum : Acc)
   with
     Ghost, Global => null,
     Pre  => KD.Models (D0, L0, N0)
             and then L1'First = 1 and then N1 <= L1'Last
             and then A <= B0 + 1 and then B0 <= N0
             and then A <= B1 + 1 and then B1 <= N1
             and then N1 - B1 = N0 - B0
             and then (for all I in 1 .. A - 1 => L1 (I) = L0 (I))
             and then (for all I in B0 + 1 .. N0 => L1 (I - B0 + B1) = L0 (I))
             and then Old_Sum = KD.Sum_Of (L0, A, B0)
             and then New_Sum = KD.Sum_Of (L1, A, B1),
     Post => KD.Models (KD.Restore (N1, Add (Sub (KD.Sum (D0), Old_Sum), New_Sum)), L1, N1)
   is
      P0 : constant Acc := KD.Sum_Of (L0, 1, A - 1);
      R0 : constant Acc := KD.Sum_Of (L0, A, B0);
      Q0 : constant Acc := KD.Sum_Of (L0, B0 + 1, N0);
      P1 : constant Acc := KD.Sum_Of (L1, 1, A - 1);
      R1 : constant Acc := KD.Sum_Of (L1, A, B1);
      Q1 : constant Acc := KD.Sum_Of (L1, B1 + 1, N1);
      T0 : constant Acc := KD.Sum_Of (L0, 1, N0);
      T1 : constant Acc := KD.Sum_Of (L1, 1, N1);
      X  : constant Acc := Add (Sub (KD.Sum (D0), Old_Sum), New_Sum);
   begin
      --  The two splits.
      KD.Lemma_Sum_Split (L0, 1, A - 1, N0);
      KD.Lemma_Sum_Split (L0, A, B0, N0);
      KD.Lemma_Sum_Split (L1, 1, A - 1, N1);
      KD.Lemma_Sum_Split (L1, A, B1, N1);
      Lemma_Eq_Iff_Value (T0, Add (P0, KD.Sum_Of (L0, A, N0)));
      Lemma_Eq_Iff_Value (KD.Sum_Of (L0, A, N0), Add (R0, Q0));
      Lemma_Eq_Iff_Value (T1, Add (P1, KD.Sum_Of (L1, A, N1)));
      Lemma_Eq_Iff_Value (KD.Sum_Of (L1, A, N1), Add (R1, Q1));
      pragma Assert (Value (T0) = Value (Add (P0, Add (R0, Q0))));
      pragma Assert (Value (T1) = Value (Add (P1, Add (R1, Q1))));
      --  The prefix is the same, the suffix moved.
      KD.Lemma_Sum_Ext (L0, L1, 1, A - 1);
      Lemma_Eq_Iff_Value (P0, P1);
      Lemma_Sum_Shift (L0, L1, B0 + 1, N0, B1 - B0);
      Lemma_Eq_Iff_Value (Q0, Q1);
      --  The given sums.
      Lemma_Eq_Iff_Value (Old_Sum, R0);
      Lemma_Eq_Iff_Value (New_Sum, R1);
      Lemma_Eq_Iff_Value (KD.Sum (D0), T0);
      --  The algebra.
      Lemma_Replace (P0, R0, Q0, R1);
      pragma Assert (Value (X) = Value (Add (Sub (Add (P0, Add (R0, Q0)), R0), R1)));
      pragma Assert (Value (Add (P0, Add (R1, Q0))) = Value (Add (P1, Add (R1, Q1))));
      pragma Assert (Value (X) = Value (T1));
      Lemma_Eq_Iff_Value (X, T1);
      pragma Assert (KD.Sum (KD.Restore (N1, X)) = X);
      pragma Assert (KD.Count (KD.Restore (N1, X)) = N1);
   end Lemma_Range_Diff;

   --  Two lists with the same elements have the same state.
   procedure Lemma_Models_Ext
     (D : KD.Digest_State; L0, L1 : KD.Hash_Array; N : KD.Elem_Count)
   with
     Ghost, Global => null,
     Pre  => KD.Models (D, L0, N)
             and then L1'First = 1 and then N <= L1'Last
             and then (for all I in 1 .. N => L1 (I) = L0 (I)),
     Post => KD.Models (D, L1, N)
   is
   begin
      KD.Lemma_Sum_Ext (L0, L1, 1, N);
      Lemma_Eq_Iff_Value (KD.Sum (D), KD.Sum_Of (L0, 1, N));
      Lemma_Eq_Iff_Value (KD.Sum_Of (L0, 1, N), KD.Sum_Of (L1, 1, N));
      Lemma_Eq_Iff_Value (KD.Sum (D), KD.Sum_Of (L1, 1, N));
   end Lemma_Models_Ext;

   --  The sum of the data rows Lo .. Hi, one Elem_Acc per record.
   function Data_Range_Sum (F : Frontier.State; Lo : KD.Lo_Bound; Hi : KD.Elem_Count) return Acc
   with
     Global => null,
     Pre  => Hi <= Data_Count (F) and then Lo <= Hi + 1,
     Post => Data_Range_Sum'Result = KD.Sum_Of (Data_Hashes (F), Lo, Hi)
   is
      --  Proved; at run time only the Post is evaluated (each invariant
      --  and step would sum the range again).
      pragma Assertion_Policy (Loop_Invariant => Ignore, Assert => Ignore, Ghost => Ignore);

      procedure Step (X1, X2, Y : Acc)
        with Ghost, Global => null,
             Pre  => X1 = X2,
             Post => Add (X1, Y) = Add (X2, Y);

      procedure Step (X1, X2, Y : Acc) is
      begin
         Lemma_Add_Congruent (X1, X2, Y, Y);
      end Step;

      procedure Empty_Step (FF : Frontier.State; LL : KD.Lo_Bound)
        with Ghost, Global => null,
             Post => KD.Sum_Of (Data_Hashes (FF), LL, LL - 1) = Zero;

      procedure Empty_Step (FF : Frontier.State; LL : KD.Lo_Bound) is
      begin
         KD.Lemma_Sum_Of_Empty (Data_Hashes (FF), LL, LL - 1);
      end Empty_Step;

      procedure Next (FF : Frontier.State; LL : KD.Lo_Bound; I : KD.Elem_Index)
        with Ghost, Global => null,
             Pre  => LL <= I and then I <= Data_Count (FF),
             Post => KD.Sum_Of (Data_Hashes (FF), LL, I)
                     = Add (KD.Sum_Of (Data_Hashes (FF), LL, I - 1),
                            KD.Elem_Acc (Data_Held (FF, I).V.H));

      procedure Next (FF : Frontier.State; LL : KD.Lo_Bound; I : KD.Elem_Index) is
      begin
         KD.Lemma_Sum_Of_Step (Data_Hashes (FF), LL, I);
      end Next;

      R : Acc := Zero;
   begin
      Empty_Step (F, Lo);
      for I in Lo .. Hi loop
         Step (R, KD.Sum_Of (Data_Hashes (F), Lo, I - 1), KD.Elem_Acc (Data_Held (F, I).V.H));
         R := Add (R, KD.Elem_Acc (Data_Held (F, I).V.H));
         Next (F, Lo, I);
         pragma Loop_Invariant (R = KD.Sum_Of (Data_Hashes (F), Lo, I));
      end loop;
      return R;
   end Data_Range_Sum;

   --  The sum of the authorization rows Lo .. Hi of Auth_Hashes (flat
   --  indices Data_Count + Lo .. Data_Count + Hi).
   function Auth_Range_Sum (F : Frontier.State; Lo : KD.Lo_Bound; Hi : KD.Elem_Count) return Acc
   with
     Global => null,
     Pre  => Hi <= Auth_Count (F) and then Lo <= Hi + 1,
     Post => Auth_Range_Sum'Result = KD.Sum_Of (Auth_Hashes (F), Lo, Hi)
   is
      --  Proved; at run time only the Post is evaluated.
      pragma Assertion_Policy (Loop_Invariant => Ignore, Assert => Ignore, Ghost => Ignore);

      procedure Step (X1, X2, Y : Acc)
        with Ghost, Global => null,
             Pre  => X1 = X2,
             Post => Add (X1, Y) = Add (X2, Y);

      procedure Step (X1, X2, Y : Acc) is
      begin
         Lemma_Add_Congruent (X1, X2, Y, Y);
      end Step;

      procedure Empty_Step (FF : Frontier.State; LL : KD.Lo_Bound)
        with Ghost, Global => null,
             Post => KD.Sum_Of (Auth_Hashes (FF), LL, LL - 1) = Zero;

      procedure Empty_Step (FF : Frontier.State; LL : KD.Lo_Bound) is
      begin
         KD.Lemma_Sum_Of_Empty (Auth_Hashes (FF), LL, LL - 1);
      end Empty_Step;

      procedure Next (FF : Frontier.State; LL : KD.Lo_Bound; I : KD.Elem_Index)
        with Ghost, Global => null,
             Pre  => LL <= I and then I <= Auth_Count (FF),
             Post => KD.Sum_Of (Auth_Hashes (FF), LL, I)
                     = Add (KD.Sum_Of (Auth_Hashes (FF), LL, I - 1),
                            KD.Elem_Acc (Held (FF, Data_Count (FF) + I).V.H));

      procedure Next (FF : Frontier.State; LL : KD.Lo_Bound; I : KD.Elem_Index) is
      begin
         KD.Lemma_Sum_Of_Step (Auth_Hashes (FF), LL, I);
      end Next;

      R : Acc := Zero;
   begin
      Empty_Step (F, Lo);
      for I in Lo .. Hi loop
         Step (R, KD.Sum_Of (Auth_Hashes (F), Lo, I - 1),
               KD.Elem_Acc (Held (F, Data_Count (F) + I).V.H));
         R := Add (R, KD.Elem_Acc (Held (F, Data_Count (F) + I).V.H));
         Next (F, Lo, I);
         pragma Loop_Invariant (R = KD.Sum_Of (Auth_Hashes (F), Lo, I));
      end loop;
      return R;
   end Auth_Range_Sum;

   ---------------------------------------------------------------------------
   --  The frontier views of one step, read in the flat view.
   ---------------------------------------------------------------------------

   --  The slot offsets after an authorization step of the slot K: below K
   --  they stay, above K they move by the change of K's count.
   procedure Lemma_Offs_Step (F0, F1 : Frontier.State; K : Slot_Index) with
     Ghost, Global => null,
     Pre  => Is_Frontier (F0) and then Is_Frontier (F1)
             and then (for all K2 in Slot_Index =>
                         (if K2 /= K then Slot_Count (F1, K2) = Slot_Count (F0, K2))),
     Post => (for all K2 in Slot_Index =>
                Off (F1, K2) = Off (F0, K2)
                               + (if K2 > K then Slot_Count (F1, K) - Slot_Count (F0, K) else 0))
             and then (for all K1 in Slot_Index =>
                         (for all K2 in Slot_Index =>
                            (if K1 < K2 then Off (F0, K1) + Slot_Count (F0, K1) <= Off (F0, K2))))
             and then Auth_Count (F1) - Off (F1, K) - Slot_Count (F1, K)
                      = Auth_Count (F0) - Off (F0, K) - Slot_Count (F0, K)
   is
      --  Proved; at run time the invariants would cost O(16^2) per call.
      pragma Assertion_Policy (Loop_Invariant => Ignore);
   begin
      Lemma_Frontier_Shape (F0);
      Lemma_Frontier_Shape (F1);
      for K2 in 1 .. Signers_Max loop
         pragma Loop_Invariant
           (for all K3 in 1 .. K2 =>
              Off (F1, K3) = Off (F0, K3)
                             + (if K3 > K then Slot_Count (F1, K) - Slot_Count (F0, K) else 0));
      end loop;
      for K2 in 2 .. Signers_Max loop
         pragma Loop_Invariant
           (for all K3 in 2 .. K2 =>
              (for all K1 in 1 .. K3 - 1 => Off (F0, K1) + Slot_Count (F0, K1) <= Off (F0, K3)));
      end loop;
      pragma Assert (Auth_Count (F0) = Off (F0, Signers_Max) + Slot_Count (F0, Signers_Max));
      pragma Assert (Auth_Count (F1) = Off (F1, Signers_Max) + Slot_Count (F1, Signers_Max));
      if K < Signers_Max then
         for K2 in K + 1 .. Signers_Max loop
            pragma Loop_Invariant
              (Off (F0, K2) - Off (F0, K + 1) = Off (F1, K2) - Off (F1, K + 1));
         end loop;
      end if;
   end Lemma_Offs_Step;

   --  S14: what an authorization step of Signer left untouched, in the
   --  flat view: the data row; the authorization records before the slot;
   --  the records after it, moved by the change of the slot's length.
   procedure Lemma_Slot_Flat (F0, F1 : Frontier.State; Signer : Key256) with
     Ghost, Global => null,
     Pre  => Is_Frontier (F0) and then Is_Frontier (F1)
             and then Outside_Slot (F0, F1, Signer),
     Post => Data_Count (F1) = Data_Count (F0)
             and then (for all I in 1 .. Data_Count (F0) => Data_Held (F1, I) = Data_Held (F0, I))
             and then Slot (F1, Signer).First = Slot (F0, Signer).First
             and then Slot (F0, Signer).First >= Data_Count (F0) + 1
             and then Slot (F0, Signer).First <= Slot (F0, Signer).Last + 1
             and then Slot (F1, Signer).First <= Slot (F1, Signer).Last + 1
             and then Slot (F1, Signer).Last <= Count (F1)
             and then Slot (F0, Signer).Last <= Count (F0)
             and then Count (F1) - Slot (F1, Signer).Last = Count (F0) - Slot (F0, Signer).Last
             and then (for all I in Data_Count (F0) + 1 .. Slot (F0, Signer).First - 1 =>
                         Held (F1, I) = Held (F0, I))
             and then (for all I in Slot (F0, Signer).Last + 1 .. Count (F0) =>
                         Held (F1, I - Slot (F0, Signer).Last + Slot (F1, Signer).Last)
                         = Held (F0, I))
   is
      --  Proved; at run time the invariants would cost O(n^2) per call.
      pragma Assertion_Policy (Loop_Invariant => Ignore);
      K   : Slot_Index;
      DC  : constant Natural := Data_Count (F0);
   begin
      Lemma_Outside_Slot (F0, F1, Signer);
      K := Slot_Of (F1, Signer);
      Lemma_Offs_Step (F0, F1, K);
      Lemma_Frontier_Shape (F0);
      Lemma_Frontier_Shape (F1);
      if Slot_Of (F0, Signer) = 0 then
         --  A new slot after the used ones: it starts after every old
         --  authorization record, and the old slot K is empty.
         pragma Assert (K = Slots_Used (F0) + 1);
         pragma Assert (Slot_Count (F0, K) = 0);
         for K2 in K .. Signers_Max loop
            pragma Assert (Slot_Count (F0, K2) = 0);
            pragma Loop_Invariant (Off (F0, K2) = Off (F0, K));
         end loop;
         pragma Assert (Auth_Count (F0) = Off (F0, K));
      end if;
      pragma Assert (Slot (F0, Signer).First = DC + Off (F0, K) + 1);
      pragma Assert (Slot (F0, Signer).Last = DC + Off (F0, K) + Slot_Count (F0, K));
      pragma Assert (Slot (F1, Signer).First = DC + Off (F1, K) + 1);
      pragma Assert (Slot (F1, Signer).Last = DC + Off (F1, K) + Slot_Count (F1, K));
      for I in DC + 1 .. Count (F0) loop
         Lemma_Held_Cases (F0, I);
         declare
            K2 : constant Slot_Index := Slot_At (F0, I);
            J  : constant Positive := I - DC - Off (F0, K2);
         begin
            if K2 /= K then
               pragma Assert (Auth_Held (F1, K2, J) = Auth_Held (F0, K2, J));
               Lemma_Held_Auth (F1, K2, J);
               if K2 < K then
                  pragma Assert (I < Slot (F0, Signer).First);
                  pragma Assert (Held (F1, I) = Held (F0, I));
               else
                  pragma Assert (I > Slot (F0, Signer).Last);
                  pragma Assert
                    (Held (F1, I - Slot (F0, Signer).Last + Slot (F1, Signer).Last) = Held (F0, I));
               end if;
            else
               pragma Assert (I in Slot (F0, Signer).First .. Slot (F0, Signer).Last);
            end if;
         end;
         pragma Loop_Invariant
           (for all I2 in DC + 1 .. I =>
              (if I2 < Slot (F0, Signer).First then Held (F1, I2) = Held (F0, I2)));
         pragma Loop_Invariant
           (for all I2 in DC + 1 .. I =>
              (if I2 > Slot (F0, Signer).Last
               then Held (F1, I2 - Slot (F0, Signer).Last + Slot (F1, Signer).Last)
                    = Held (F0, I2)));
      end loop;
   end Lemma_Slot_Flat;

   --  The authorization rows did not change (a data step, or Expire), in
   --  the flat view: the I-th authorization record is the same, after the
   --  data row of each state.
   --  Lemma_Auth_Flat at one index (the Posts of Lemma_Frontier_Shape stay
   --  inside this small context).
   --  The authorization rows keep their count (Lemma_Auth_Flat).
   procedure Lemma_Auth_Count_Same (F0, F1 : Frontier.State) with
     Ghost, Global => null,
     Pre  => Is_Frontier (F0) and then Is_Frontier (F1)
             and then Slots_Used (F1) = Slots_Used (F0)
             and then (for all K in Slot_Index =>
                         Slot_Count (F1, K) = Slot_Count (F0, K)
                         and then Off (F1, K) = Off (F0, K))
             and then (for all K in 1 .. Slots_Used (F0) =>
                         (for all J in 1 .. Slot_Count (F0, K) =>
                            Auth_Held (F1, K, J) = Auth_Held (F0, K, J)
                            and then Auth_Tag (F1, K, J) = Auth_Tag (F0, K, J)))
,
     Post => Auth_Count (F1) = Auth_Count (F0)
   is
   begin
      Lemma_Frontier_Shape (F0);
      Lemma_Frontier_Shape (F1);
   end Lemma_Auth_Count_Same;

   procedure Lemma_Auth_Flat_At (F0, F1 : Frontier.State; I : Positive) with
     Ghost, Global => null,
     Pre  => Is_Frontier (F0) and then Is_Frontier (F1)
             and then Slots_Used (F1) = Slots_Used (F0)
             and then (for all K in Slot_Index =>
                         Slot_Count (F1, K) = Slot_Count (F0, K)
                         and then Off (F1, K) = Off (F0, K))
             and then (for all K in 1 .. Slots_Used (F0) =>
                         (for all J in 1 .. Slot_Count (F0, K) =>
                            Auth_Held (F1, K, J) = Auth_Held (F0, K, J)
                            and then Auth_Tag (F1, K, J) = Auth_Tag (F0, K, J)))
             and then I <= Auth_Count (F0),
     Post => Auth_Count (F1) = Auth_Count (F0)
             and then Held (F1, Data_Count (F1) + I) = Held (F0, Data_Count (F0) + I)
             and then Tag (F1, Data_Count (F1) + I) = Tag (F0, Data_Count (F0) + I)
   is
   begin
      Lemma_Frontier_Shape (F0);
      Lemma_Frontier_Shape (F1);
      Lemma_Held_Cases (F0, Data_Count (F0) + I);
      declare
         K : constant Slot_Index := Slot_At (F0, Data_Count (F0) + I);
         J : constant Positive := I - Off (F0, K);
      begin
         pragma Assert (Off (F1, K) = Off (F0, K)
                        and then Slot_Count (F1, K) = Slot_Count (F0, K));
         pragma Assert (Auth_Held (F1, K, J) = Auth_Held (F0, K, J)
                        and then Auth_Tag (F1, K, J) = Auth_Tag (F0, K, J));
         Lemma_Held_Auth (F1, K, J);
         pragma Assert (Off (F1, K) + J = I);
         pragma Assert (Held (F1, Data_Count (F1) + I) = Auth_Held (F1, K, J));
         pragma Assert (Held (F0, Data_Count (F0) + I) = Auth_Held (F0, K, J));
      end;
   end Lemma_Auth_Flat_At;

   procedure Lemma_Auth_Flat (F0, F1 : Frontier.State) with
     Ghost, Global => null,
     Pre  => Is_Frontier (F0) and then Is_Frontier (F1)
             and then Slots_Used (F1) = Slots_Used (F0)
             and then (for all K in Slot_Index =>
                         Slot_Count (F1, K) = Slot_Count (F0, K)
                         and then Off (F1, K) = Off (F0, K))
             and then (for all K in 1 .. Slots_Used (F0) =>
                         (for all J in 1 .. Slot_Count (F0, K) =>
                            Auth_Held (F1, K, J) = Auth_Held (F0, K, J)
                            and then Auth_Tag (F1, K, J) = Auth_Tag (F0, K, J))),
     Post => Auth_Count (F1) = Auth_Count (F0)
             and then (for all I in 1 .. Auth_Count (F0) =>
                         Held (F1, Data_Count (F1) + I) = Held (F0, Data_Count (F0) + I)
                         and then Tag (F1, Data_Count (F1) + I) = Tag (F0, Data_Count (F0) + I))
   is
      --  Proved; at run time the invariant would cost O(n^2) per call.
      pragma Assertion_Policy (Loop_Invariant => Ignore);
   begin
      Lemma_Auth_Count_Same (F0, F1);
      for I in 1 .. Auth_Count (F0) loop
         Lemma_Auth_Flat_At (F0, F1, I);
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              Held (F1, Data_Count (F1) + I2) = Held (F0, Data_Count (F0) + I2));
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              Tag (F1, Data_Count (F1) + I2) = Tag (F0, Data_Count (F0) + I2));
      end loop;
   end Lemma_Auth_Flat;

   --  The Post of Frontier.Expire, read in the flat view (with tags).
   procedure Lemma_Expire_Flat (F0, F1 : Frontier.State; H : U48) with
     Ghost, Global => null,
     Pre  => Is_Frontier (F0) and then Is_Frontier (F1)
       and then Slots_Used (F1) = Slots_Used (F0)
       and then (for all K in Slot_Index =>
                   Slot_Count (F1, K) = Slot_Count (F0, K)
                   and then Off (F1, K) = Off (F0, K))
       and then (for all K in 1 .. Slots_Used (F1) =>
                   Slot_Key (F1, K) = Slot_Key (F0, K)
                   and then (for all J in 1 .. Slot_Count (F1, K) =>
                               Auth_Held (F1, K, J) = Auth_Held (F0, K, J)
                               and then Auth_Tag (F1, K, J) = Auth_Tag (F0, K, J)))
       and then (for all I in 1 .. Data_Count (F1) =>
                   Holds (F0, Data_Held (F1, I))
                   and then not Expired (Data_Held (F1, I), H)
                   and then Has_Tag (F0, Data_Held (F1, I), Data_Tag (F1, I)))
       and then (for all I in 1 .. Data_Count (F0) =>
                   Expired (Data_Held (F0, I), H)
                   or else Holds (F1, Data_Held (F0, I))),
     Post => (for all I in 1 .. Count (F1) =>
                Holds (F0, Held (F1, I)) and then not Expired (Held (F1, I), H)
                and then Has_Tag (F0, Held (F1, I), Tag (F1, I)))
       and then (for all I in 1 .. Count (F0) =>
                   Holds (F1, Held (F0, I)) or else Expired (Held (F0, I), H))
   is
      --  Proved; at run time the invariants would cost O(n^2) per call.
      pragma Assertion_Policy (Loop_Invariant => Ignore);
   begin
      for I in 1 .. Count (F1) loop
         Lemma_Held_Cases (F1, I);
         if I <= Data_Count (F1) then
            pragma Assert (Held (F1, I) = Data_Held (F1, I));
         else
            declare
               K : constant Slot_Index := Slot_At (F1, I);
               J : constant Held_Index := I - Data_Count (F1) - Off (F1, K);
            begin
               pragma Assert (Held (F1, I) = Auth_Held (F1, K, J));
               pragma Assert (Auth_Held (F1, K, J) = Auth_Held (F0, K, J));
               Lemma_Held_Auth (F0, K, J);
               Lemma_Frontier_Auth (F0, K, J);
               pragma Assert
                 (Held (F0, Data_Count (F0) + Off (F0, K) + J) = Held (F1, I));
               pragma Assert
                 (Tag (F0, Data_Count (F0) + Off (F0, K) + J) = Tag (F1, I));
               Lemma_Has_Tag_Def (F0, Held (F1, I), Tag (F1, I));
               pragma Assert (Holds (F0, Held (F1, I)));
               pragma Assert (not Expired (Held (F1, I), H));
            end;
         end if;
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              Holds (F0, Held (F1, I2)) and then not Expired (Held (F1, I2), H)
              and then Has_Tag (F0, Held (F1, I2), Tag (F1, I2)));
      end loop;
      for I in 1 .. Count (F0) loop
         Lemma_Held_Cases (F0, I);
         if I <= Data_Count (F0) then
            pragma Assert (Held (F0, I) = Data_Held (F0, I));
         else
            declare
               K : constant Slot_Index := Slot_At (F0, I);
               J : constant Held_Index := I - Data_Count (F0) - Off (F0, K);
            begin
               pragma Assert (Held (F0, I) = Auth_Held (F0, K, J));
               Lemma_Held_Auth (F1, K, J);
               pragma Assert
                 (Held (F1, Data_Count (F1) + Off (F1, K) + J) = Held (F0, I));
               pragma Assert (Holds (F1, Held (F0, I)));
            end;
         end if;
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              Holds (F1, Held (F0, I2)) or else Expired (Held (F0, I2), H));
      end loop;
   end Lemma_Expire_Flat;

   --  The index at which F holds X with the tag T (ghost).
   procedure Find_Tag (F : Frontier.State; X : Header; T : U64; J : out Held_Index) with
     Ghost, Global => null,
     Pre  => Has_Tag (F, X, T),
     Post => J <= Count (F) and then Held (F, J) = X and then Tag (F, J) = T
   is
   begin
      J := 1;
      Lemma_Has_Tag_Def (F, X, T);
      for I in 1 .. Count (F) loop
         if Held (F, I) = X and then Tag (F, I) = T then
            J := I;
            return;
         end if;
         pragma Loop_Invariant
           (for all I2 in 1 .. I => not (Held (F, I2) = X and then Tag (F, I2) = T));
      end loop;
      raise Program_Error;
   end Find_Tag;

   --  The tag of the APPLY that Commit appended at LL0 is good (and of the
   --  CEIL that Capture appended: Op).
   procedure Lemma_New_Tag
     (Log : Byte_Array; LL0, LL1 : Log_Size; Cid : Hash256; Frame : Byte_Array; H : Header;
      Tg  : U64; Op : Byte)
   with
     Ghost, Global => null,
     Pre  => Log'First = 0 and then LL1 <= Log'Last
             and then Frame'Length in Frame_Size
             and then LL0 >= Header_Len
             and then LL1 = LL0 + Apply_Prefix + Frame'Length
             and then Tg = Make_Tag (LL0, Frame'Length)
             and then Log (LL0) = Op
             and then U24_Of (Log (LL0 + 1), Log (LL0 + 2), Log (LL0 + 3)) = Frame'Length
             and then (for all J in Frame'Range =>
                         Log (J - Frame'First + (LL0 + Apply_Prefix)) = Frame (J))
             and then Is_Record_Frame (Frame)
             and then Header_Of (Cid, Frame) = H,
     Post => Tag_OK (Log, LL1, Cid, H, Tg, Op)
   is
   begin
      Lemma_Tag_Round_Trip (LL0, Frame'Length);
      declare
         SL : constant Byte_Array := Slice_At (Log, Tg);
      begin
         pragma Assert (SL'First = LL0 + Apply_Prefix and then SL'Length = Frame'Length);
         pragma Assert (for all J in Frame'Range =>
                          SL (J - Frame'First + (LL0 + Apply_Prefix)) = Frame (J));
         pragma Assert (for all J in Frame'Range => SL (J - Frame'First + SL'First) = Frame (J));
         Lemma_Frame_Is_Def (Frame, Cid, H);
         Lemma_Frame_Is_Congruent (Cid, H, Frame, SL);
         pragma Assert (Frame_Is (SL, Cid, H));
      end;
      pragma Assert (Frame_Is (Slice_At (Log, Tg), Cid, H));
   end Lemma_New_Tag;

   --  The tags after Frontier.Apply held R with the tag Tg of its new APPLY
   --  (Log1 is Log0 plus that entry).
   procedure Lemma_Tags_Apply
     (Log0 : Byte_Array; LL0 : Log_Size; Log1 : Byte_Array; LL1 : Log_Size;
      Cid  : Hash256; F0, F1 : Frontier.State; R : Header; Tg : U64)
   with
     Ghost, Global => null,
     Pre  => Log0'First = 0 and then LL0 <= Log0'Last
             and then Log1'First = 0 and then LL1 <= Log1'Last
             and then LL0 <= LL1
             and then (for all J in 0 .. LL0 - 1 => Log1 (J) = Log0 (J))
             and then Tags_OK (Log0, LL0, Cid, F0)
             and then Tag_OK (Log1, LL1, Cid, R, Tg, Op_Apply)
             and then (for all I in 1 .. Count (F1) =>
                         (if Held (F1, I) = R then Tag (F1, I) = Tg
                          else Has_Tag (F0, Held (F1, I), Tag (F1, I)))),
     Post => Tags_OK (Log1, LL1, Cid, F1)
   is
      --  Proved; at run time the invariant would cost O(n^2) per call.
      pragma Assertion_Policy (Loop_Invariant => Ignore);
      J : Held_Index := 1;
   begin
      for I in 1 .. Count (F1) loop
         if Held (F1, I) /= R then
            Find_Tag (F0, Held (F1, I), Tag (F1, I), J);
            pragma Assert (Tag_OK (Log0, LL0, Cid, Held (F0, J), Tag (F0, J), Op_Apply));
            Lemma_Tag_OK_Kept (Log0, LL0, Log1, LL1, Cid, Held (F1, I), Tag (F1, I), Op_Apply);
         end if;
         pragma Loop_Invariant
           (for all I2 in 1 .. I => Tag_OK (Log1, LL1, Cid, Held (F1, I2), Tag (F1, I2), Op_Apply));
      end loop;
   end Lemma_Tags_Apply;

   --  The tags after Frontier.Expire: every survivor kept its tag.
   procedure Lemma_Tags_Expire
     (Log : Byte_Array; LL : Log_Size; Cid : Hash256; F0, F1 : Frontier.State)
   with
     Ghost, Global => null,
     Pre  => Log'First = 0 and then LL <= Log'Last
             and then Tags_OK (Log, LL, Cid, F0)
             and then (for all I in 1 .. Count (F1) => Has_Tag (F0, Held (F1, I), Tag (F1, I))),
     Post => Tags_OK (Log, LL, Cid, F1)
   is
      --  Proved; at run time the invariant would cost O(n^2) per call.
      pragma Assertion_Policy (Loop_Invariant => Ignore);
      J : Held_Index := 1;
   begin
      for I in 1 .. Count (F1) loop
         Find_Tag (F0, Held (F1, I), Tag (F1, I), J);
         pragma Assert (Tag_OK (Log, LL, Cid, Held (F0, J), Tag (F0, J), Op_Apply));
         pragma Loop_Invariant
           (for all I2 in 1 .. I => Tag_OK (Log, LL, Cid, Held (F1, I2), Tag (F1, I2), Op_Apply));
      end loop;
   end Lemma_Tags_Expire;

   --  Unchanged frontiers keep every part of the invariant.
   procedure Lemma_Valid_Unchanged (S : Store; F0, F1 : Frontier.State) with
     Ghost, Global => null,
     Pre  => Valid (S, F0) and then Unchanged (F0, F1) and then Is_Frontier (F1),
     Post => Valid (S, F1)
   is
   begin
      Lemma_Unchanged (F0, F1);
      Lemma_Frontier_Shape (F0);
      Lemma_Tags_Same (S.Log, S.LL, S.Cid, F0, F1);
      Lemma_Ceil_Kept (S.Log, S.LL, S.Log, S.LL, S.Cid, F0, F1);
      Lemma_Rest_Same (F0, F1, S.TTL, S.Self, S.SS);
      Lemma_Hashes_Same (F0, F1);
      Lemma_Models_Ext (S.DD, Data_Hashes (F0), Data_Hashes (F1), Data_Count (F0));
      Lemma_Models_Ext (S.DA, Auth_Hashes (F0), Auth_Hashes (F1), Auth_Count (F0));
   end Lemma_Valid_Unchanged;

   ---------------------------------------------------------------------------
   --  Appending to the log.
   ---------------------------------------------------------------------------

   --  Log (P .. P + Frame'Length - 1) := Frame; nothing else changes.
   procedure Write_Frame (Log : in out Byte_Array; P : Natural; Frame : Byte_Array) with
     Global => null,
     Pre  => Log'First = 0 and then Log'Last <= Log_Max
             and then Frame'Length in Frame_Size
             and then P <= Log'Last and then Frame'Length - 1 <= Log'Last - P,
     Post => (for all Q in Log'Range =>
                (if Q < P or else Q > P + Frame'Length - 1 then Log (Q) = Log'Old (Q)))
       and then (for all J in Frame'Range => Log (J - Frame'First + P) = Frame (J))
   is
   begin
      for K in 0 .. Frame'Length - 1 loop
         Log (P + K) := Frame (Frame'First + K);
         pragma Loop_Invariant
           (for all Q in Log'Range =>
              (if Q < P or else Q > P + Frame'Length - 1 then Log (Q) = Log'Loop_Entry (Q)));
         pragma Loop_Invariant
           (for all J in Frame'First .. Frame'First + K => Log (J - Frame'First + P) = Frame (J));
      end loop;
   end Write_Frame;

   --  Append  Op ‖ len:u24 ‖ Frame  (Op_Apply: an APPLY; Op_Ceil: a CEIL).
   procedure Append_Apply
     (Log : in out Byte_Array; LL : in out Log_Size; Frame : Byte_Array; Off : Log_Size;
      Op  : Byte)
   with
     Global => null,
     Pre  => Off = LL
             and then Log'First = 0 and then LL <= Log'Last and then Log'Last <= Log_Max
             and then Frame'Length in Frame_Size
             and then Apply_Prefix + Frame'Length <= Log'Last - LL,
     Post => LL = Off + Apply_Prefix + Frame'Length
       and then (for all P in 0 .. Off - 1 => Log (P) = Log'Old (P))
       and then Log (Off) = Op
       and then Log (Off + 1) = Byte_Of_U24 (Frame'Length, 0)
       and then Log (Off + 2) = Byte_Of_U24 (Frame'Length, 1)
       and then Log (Off + 3) = Byte_Of_U24 (Frame'Length, 2)
       and then U24_Of (Log (Off + 1), Log (Off + 2), Log (Off + 3)) = Frame'Length
       and then (for all J in Frame'Range => Log (J - Frame'First + (Off + Apply_Prefix)) = Frame (J))
   is
   begin
      Lemma_U24_Round_Trip (Frame'Length);
      Log (Off)     := Op;
      Log (Off + 1) := Byte_Of_U24 (Frame'Length, 0);
      Log (Off + 2) := Byte_Of_U24 (Frame'Length, 1);
      Log (Off + 3) := Byte_Of_U24 (Frame'Length, 2);
      Write_Frame (Log, Off + Apply_Prefix, Frame);
      LL := Off + Apply_Prefix + Frame'Length;
   end Append_Apply;

   --  Append  02 ‖ seq:u48.
   procedure Append_Seq (Log : in out Byte_Array; LL : in out Log_Size; V : U48) with
     Global => null,
     Pre  => Log'First = 0 and then LL <= Log'Last and then Log'Last <= Log_Max
             and then Seq_Len <= Log'Last - LL,
     Post => LL = LL'Old + Seq_Len
       and then (for all P in 0 .. LL'Old - 1 => Log (P) = Log'Old (P))
       and then Log (LL'Old) = Op_Seq
       and then (for all K in 0 .. 5 => Log (LL'Old + 1 + K) = KR.Byte_Of_U48 (V, K))
       and then KR.U48_Of (Log (LL'Old + 1), Log (LL'Old + 2), Log (LL'Old + 3),
                           Log (LL'Old + 4), Log (LL'Old + 5), Log (LL'Old + 6)) = V
   is
      P : constant Log_Size := LL;
   begin
      KR.Lemma_U48_Round_Trip (V);
      Log (P) := Op_Seq;
      for K in 0 .. 5 loop
         Log (P + 1 + K) := KR.Byte_Of_U48 (V, K);
         pragma Loop_Invariant (for all Q in 0 .. P => Log (Q) = Log'Loop_Entry (Q)
                                                       or else Q = P);
         pragma Loop_Invariant (Log (P) = Op_Seq);
         pragma Loop_Invariant (for all Q in 0 .. P - 1 => Log (Q) = Log'Loop_Entry (Q));
         pragma Loop_Invariant (for all K2 in 0 .. K => Log (P + 1 + K2) = KR.Byte_Of_U48 (V, K2));
      end loop;
      LL := P + Seq_Len;
   end Append_Seq;

   ---------------------------------------------------------------------------
   --  Expiry helpers.
   ---------------------------------------------------------------------------

   --  Some held record is a DEL at or below Hz.
   function Expires_Any (F : Frontier.State; H : U48) return Boolean with
     Global => null,
     Post => Expires_Any'Result = (for some I in 1 .. Count (F) => Expired (Held (F, I), H))
   is
   begin
      for I in 1 .. Count (F) loop
         if Expired (Held (F, I), H) then
            return True;
         end if;
         pragma Loop_Invariant (for all I2 in 1 .. I => not Expired (Held (F, I2), H));
      end loop;
      return False;
   end Expires_Any;


   ---------------------------------------------------------------------------
   --  Put_Frame.
   ---------------------------------------------------------------------------

   --  Apply_Frame is Put_Frame without the signature precondition (replay).

   --  S21: the digest step of one apply, as a lemma (Commit computes the
   --  new sums). A data apply changed one entity run and an authorization
   --  apply one signer slot; the state loses the sum of the old run or slot
   --  and gains the sum of the new one, and the other state stays.
   function Range_Of (F : Frontier.State; H : Header) return Index_Range is
     (if Is_Data (H) then Run (F, H.Ent) else Slot (F, H.Issuer))
   with Pre => Is_Frontier (F);

   procedure Lemma_Digest_Step
     (DA, DD  : KD.Digest_State;
      F0, F1  : Frontier.State;
      H       : Header;
      Old_Sum : Acc;
      New_Sum : Acc)
   with
     Ghost, Global => null,
     Pre  => Is_Frontier (F0) and then Is_Frontier (F1)
       and then KD.Models (DA, Auth_Hashes (F0), Auth_Count (F0))
       and then KD.Models (DD, Data_Hashes (F0), Data_Count (F0))
       and then (if Is_Data (H) then Outside_Run (F0, F1, H.Ent)
                 else Outside_Slot (F0, F1, H.Issuer))
       and then Range_Of (F0, H).First > (if Is_Data (H) then 0 else Data_Count (F0))
       and then Range_Of (F1, H).First > (if Is_Data (H) then 0 else Data_Count (F1))
       and then Range_Of (F0, H).Last <= (if Is_Data (H) then Data_Count (F0) else Count (F0))
       and then Range_Of (F1, H).Last <= (if Is_Data (H) then Data_Count (F1) else Count (F1))
       and then Range_Of (F0, H).First <= Range_Of (F0, H).Last + 1
       and then Range_Of (F1, H).First <= Range_Of (F1, H).Last + 1
       and then (if Is_Data (H)
                 then Old_Sum = KD.Sum_Of (Data_Hashes (F0), Range_Of (F0, H).First,
                                           Range_Of (F0, H).Last)
                      and then New_Sum = KD.Sum_Of (Data_Hashes (F1), Range_Of (F1, H).First,
                                                    Range_Of (F1, H).Last)
                 else Old_Sum = KD.Sum_Of (Auth_Hashes (F0),
                                           Range_Of (F0, H).First - Data_Count (F0),
                                           Range_Of (F0, H).Last - Data_Count (F0))
                      and then New_Sum = KD.Sum_Of (Auth_Hashes (F1),
                                                    Range_Of (F1, H).First - Data_Count (F1),
                                                    Range_Of (F1, H).Last - Data_Count (F1))),
     Post => (if Is_Data (H)
              then KD.Models (KD.Restore (Data_Count (F1), Add (Sub (KD.Sum (DD), Old_Sum), New_Sum)),
                              Data_Hashes (F1), Data_Count (F1))
                   and then KD.Models (DA, Auth_Hashes (F1), Auth_Count (F1))
              else KD.Models (KD.Restore (Auth_Count (F1), Add (Sub (KD.Sum (DA), Old_Sum), New_Sum)),
                              Auth_Hashes (F1), Auth_Count (F1))
                   and then KD.Models (DD, Data_Hashes (F1), Data_Count (F1)))
   is
      RO : constant Index_Range := Range_Of (F0, H);
      RU : constant Index_Range := Range_Of (F1, H);
   begin
      Lemma_Frontier_Shape (F0);
      Lemma_Frontier_Shape (F1);
      if Is_Data (H) then
         Lemma_Outside_Run (F0, F1, H.Ent);
         pragma Assert (RU.First = RO.First);
         pragma Assert (for all I in 1 .. RO.First - 1 =>
                          Data_Hashes (F1) (I) = Data_Hashes (F0) (I));
         pragma Assert (for all I in RO.Last + 1 .. Data_Count (F0) =>
                          Data_Hashes (F1) (I - RO.Last + RU.Last) = Data_Hashes (F0) (I));
         Lemma_Range_Diff
           (DD, Data_Hashes (F0), Data_Hashes (F1), Data_Count (F0), Data_Count (F1),
            RO.First, RO.Last, RU.Last, Old_Sum, New_Sum);
         Lemma_Auth_Flat (F0, F1);
         pragma Assert (for all I in 1 .. Auth_Count (F0) =>
                          Auth_Hashes (F1) (I) = Auth_Hashes (F0) (I));
         Lemma_Models_Ext (DA, Auth_Hashes (F0), Auth_Hashes (F1), Auth_Count (F0));
      else
         Lemma_Slot_Flat (F0, F1, H.Issuer);
         declare
            DC : constant Natural := Data_Count (F1);
         begin
            pragma Assert (DC = Data_Count (F0) and then RU.First = RO.First);
            pragma Assert (for all I in 1 .. RO.First - DC - 1 =>
                             Auth_Hashes (F1) (I) = Auth_Hashes (F0) (I));
            pragma Assert (for all I in RO.Last - DC + 1 .. Auth_Count (F0) =>
                             Auth_Hashes (F1) (I - (RO.Last - DC) + (RU.Last - DC))
                             = Auth_Hashes (F0) (I));
            Lemma_Range_Diff
              (DA, Auth_Hashes (F0), Auth_Hashes (F1), Auth_Count (F0), Auth_Count (F1),
               RO.First - DC, RO.Last - DC, RU.Last - DC, Old_Sum, New_Sum);
         end;
         pragma Assert (for all I in 1 .. Data_Count (F0) =>
                          Data_Hashes (F1) (I) = Data_Hashes (F0) (I));
         Lemma_Models_Ext (DD, Data_Hashes (F0), Data_Hashes (F1), Data_Count (F0));
      end if;
   end Lemma_Digest_Step;

   --  S16: after an apply of R (each held record is old or R), seq_self
   --  still bounds the own seqs.
   procedure Lemma_Seq_Apply
     (F0, F1 : Frontier.State; R : Header; Self : Key256; SS0, SS1 : U48)
   with
     Ghost, Global => null,
     Pre  => Seq_OK (F0, Self, SS0) and then SS0 <= SS1
             and then (if Is_Data (R) and then R.V.Author = Self then R.V.Seq <= SS1)
             and then (for all I in 1 .. Count (F1) =>
                         Holds (F0, Held (F1, I)) or else Held (F1, I) = R),
     Post => Seq_OK (F1, Self, SS1)
   is
      --  Proved; at run time the invariant would cost O(n^2) per call.
      pragma Assertion_Policy (Loop_Invariant => Ignore);
   begin
      for I in 1 .. Count (F1) loop
         if Held (F1, I) /= R then
            pragma Assert (Holds (F0, Held (F1, I)));
            pragma Assert (Held (F0, Index_Of (F0, Held (F1, I))) = Held (F1, I));
         end if;
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              (if Is_Data (Held (F1, I2)) and then Held (F1, I2).V.Author = Self
               then Held (F1, I2).V.Seq <= SS1));
      end loop;
   end Lemma_Seq_Apply;

   --  S16: a subset of the held records is as far below seq_self.
   procedure Lemma_Seq_Sub (F0, F1 : Frontier.State; Self : Key256; SS : U48) with
     Ghost, Global => null,
     Pre  => Seq_OK (F0, Self, SS)
             and then (for all I in 1 .. Count (F1) => Holds (F0, Held (F1, I))),
     Post => Seq_OK (F1, Self, SS)
   is
      --  Proved; at run time the invariant would cost O(n^2) per call.
      pragma Assertion_Policy (Loop_Invariant => Ignore);
   begin
      for I in 1 .. Count (F1) loop
         pragma Assert (Held (F0, Index_Of (F0, Held (F1, I))) = Held (F1, I));
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              (if Is_Data (Held (F1, I2)) and then Held (F1, I2).V.Author = Self
               then Held (F1, I2).V.Seq <= SS));
      end loop;
   end Lemma_Seq_Sub;

   --  A frontier that holds no record twice holds each record with its tag.
   procedure Lemma_Self_Tags (F : Frontier.State) with
     Ghost, Global => null,
     Post => (for all I in 1 .. Count (F) => Has_Tag (F, Held (F, I), Tag (F, I)))
   is
      --  Proved; at run time the invariant would cost O(n^2) per call.
      pragma Assertion_Policy (Loop_Invariant => Ignore);
   begin
      for I in 1 .. Count (F) loop
         Lemma_Has_Tag_Def (F, Held (F, I), Tag (F, I));
         pragma Loop_Invariant
           (for all I2 in 1 .. I => Has_Tag (F, Held (F, I2), Tag (F, I2)));
      end loop;
   end Lemma_Self_Tags;

   --  S7: the expiry of Put_Frame. If some held DEL is at or below the
   --  horizon of F, Frontier.Expire removes the DELs at or below it and
   --  the data digest is summed again over the data row (Frontier.Expire
   --  states the survivors as a set). Otherwise nothing changes.
   procedure Expiry_Step
     (F    : in out Frontier.State;
      DD   : in out KD.Digest_State;
      DA   : KD.Digest_State;
      Log  : Byte_Array;
      LL   : Log_Size;
      Cid  : Hash256;
      TTL  : U48;
      Self : Key256;
      SS   : U48)
   with
     Global => null,
     Pre  => Is_Frontier (F) and then Log'First = 0 and then LL <= Log'Last
       and then Tags_OK (Log, LL, Cid, F) and then Seq_OK (F, Self, SS)
       and then KD.Models (DA, Auth_Hashes (F), Auth_Count (F))
       and then KD.Models (DD, Data_Hashes (F), Data_Count (F)),
     Post => Is_Frontier (F)
       and then Frontier.Founding (F) = Frontier.Founding (F'Old)
       and then Max_Ceil (F) = Max_Ceil (F'Old)
       and then Tags_OK (Log, LL, Cid, F) and then Seq_OK (F, Self, SS)
       and then Fresh (F, TTL)
       and then KD.Models (DA, Auth_Hashes (F), Auth_Count (F))
       and then KD.Models (DD, Data_Hashes (F), Data_Count (F))
       and then (for all I in 1 .. Count (F) =>
                   Holds (F'Old, Held (F, I)) and then Has_Tag (F'Old, Held (F, I), Tag (F, I)))
       and then (for all I in 1 .. Count (F'Old) =>
                   Holds (F, Held (F'Old, I)) or else Expired_In (Held (F'Old, I), F, TTL))
       and then Ceil_Same (F'Old, F)
   is
   begin
      if Has_Hz (F, TTL) and then Expires_Any (F, Hz (F, TTL)) then
         declare
            F1  : constant Frontier.State := F with Ghost;
            Hz1 : constant U48 := Hz (F, TTL);
         begin
            Frontier.Expire (F, Hz1);
            Lemma_Expire_Flat (F1, F, Hz1);
            pragma Assert (Hz (F, TTL) = Hz1);
            Lemma_Tags_Expire (Log, LL, Cid, F1, F);
            Lemma_Auth_Flat (F1, F);
            pragma Assert (for all I in 1 .. Auth_Count (F1) =>
                             Auth_Hashes (F) (I) = Auth_Hashes (F1) (I));
            Lemma_Models_Ext (DA, Auth_Hashes (F1), Auth_Hashes (F), Auth_Count (F1));
            DD := KD.Restore (Data_Count (F), Data_Range_Sum (F, 1, Data_Count (F)));
            Lemma_Seq_Sub (F1, F, Self, SS);
            pragma Assert (Fresh (F, TTL));
         end;
      else
         pragma Assert (Fresh (F, TTL));
         Lemma_Self_Tags (F);
      end if;
   end Expiry_Step;

   --  Lean's applyH (S7), from the Post of Frontier.Apply (F0 to F1) and
   --  of Expiry_Step (F1 to F2).
   procedure Lemma_Applied_H (F0, F1, F2 : Frontier.State; H : Header; TTL : U48) with
     Ghost, Global => null,
     Pre  => Holds (F1, H)
       and then Max_Ceil (F1) = U48'Max (Max_Ceil (F0), Ceil_Of (H))
       and then (for all I in 1 .. Count (F1) =>
                   Holds (F0, Held (F1, I)) or else Held (F1, I) = H)
       and then (for all I in 1 .. Count (F0) =>
                   Holds (F1, Held (F0, I)) or else Dominates (H, Held (F0, I)))
       and then Max_Ceil (F2) = Max_Ceil (F1)
       and then Fresh (F2, TTL)
       and then (for all I in 1 .. Count (F2) => Holds (F1, Held (F2, I)))
       and then (for all I in 1 .. Count (F1) =>
                   Holds (F2, Held (F1, I)) or else Expired_In (Held (F1, I), F2, TTL)),
     Post => Applied_H (F0, F2, H, TTL)
   is
      --  Proved; at run time the invariants would cost O(n^2) per call.
      pragma Assertion_Policy (Loop_Invariant => Ignore);
   begin
      pragma Assert (Held (F1, Index_Of (F1, H)) = H);
      for I in 1 .. Count (F2) loop
         pragma Assert (Held (F1, Index_Of (F1, Held (F2, I))) = Held (F2, I));
         pragma Assert (not Expired_In (Held (F2, I), F2, TTL));
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              (Holds (F0, Held (F2, I2)) or else Held (F2, I2) = H)
              and then not Expired_In (Held (F2, I2), F2, TTL));
      end loop;
      for I in 1 .. Count (F0) loop
         if Holds (F1, Held (F0, I)) then
            pragma Assert (Held (F1, Index_Of (F1, Held (F0, I))) = Held (F0, I));
         end if;
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              Holds (F2, Held (F0, I2)) or else Dominates (H, Held (F0, I2))
              or else Expired_In (Held (F0, I2), F2, TTL));
      end loop;
   end Lemma_Applied_H;

   --  The tag of H after Commit is the tag of its APPLY.
   procedure Lemma_Tag_Final (F1, F2 : Frontier.State; H : Header; Tg : U64) with
     Ghost, Global => null,
     Pre  => Is_Frontier (F1) and then Is_Frontier (F2)
       and then (for all I in 1 .. Count (F1) => (if Held (F1, I) = H then Tag (F1, I) = Tg))
       and then (for all I in 1 .. Count (F2) => Has_Tag (F1, Held (F2, I), Tag (F2, I))),
     Post => (if Holds (F2, H) then Tag_Of (F2, H) = Tg)
   is
      J1 : Held_Index := 1;
   begin
      if Holds (F2, H) then
         Lemma_Tag_Of (F2, Index_Of (F2, H));
         Find_Tag (F1, H, Tag (F2, Index_Of (F2, H)), J1);
         pragma Assert (Tag (F1, J1) = Tg);
      end if;
   end Lemma_Tag_Final;

   --  The bytes of Frame are the frame of the APPLY at Off (one atom for
   --  the contracts below; its Post defines it).
   function Bytes_At (Log : Byte_Array; Off : Natural; Frame : Byte_Array) return Boolean
   with
     Ghost, Global => null,
     Pre  => Log'First = 0 and then Frame'Length in Frame_Size
             and then Off <= Log_Max
             and then Off + Apply_Prefix + Frame'Length - 1 <= Log'Last,
     Post => Bytes_At'Result =
       (for all J in Frame'Range => Log (J - Frame'First + (Off + Apply_Prefix)) = Frame (J));

   function Bytes_At (Log : Byte_Array; Off : Natural; Frame : Byte_Array) return Boolean is
   begin
      return (for all J in Frame'Range => Log (J - Frame'First + (Off + Apply_Prefix)) = Frame (J));
   end Bytes_At;

   --  Step (7), the log part: append APPLY (Frame) at Off = LL, carry the
   --  HEADER across, and state the tag Tg of the new entry. Over the
   --  components, in a small context of its own. With Op_Ceil it appends
   --  the CEIL of a capture.
   procedure Log_Apply
     (Log   : in out Byte_Array;
      LL    : in out Log_Size;
      NE    : in out Natural;
      Root  : Pubkey;
      Slt   : Salt;
      TTL   : U48;
      Cid   : Hash256;
      Frame : Byte_Array;
      H     : Header;
      Tg    : U64;
      Off   : Log_Size;
      Op    : Byte)
   with
     Global => null,
     Pre  => Off = LL
       and then Log'First = 0 and then LL <= Log'Last and then Log'Last <= Log_Max
       and then Frame'Length in Frame_Size
       and then Apply_Prefix + Frame'Length <= Log'Last - LL
       and then NE <= LL
       and then LL >= Header_Len
       and then Tg = Make_Tag (Off, Frame'Length)
       and then Is_Record_Frame (Frame)
       and then Header_Of (Cid, Frame) = H
       and then Head_OK (Log, LL, Root, Slt, TTL),
     Post => LL = Off + Apply_Prefix + Frame'Length
       and then NE = NE'Old + 1
       and then NE <= LL
       and then (for all P in 0 .. Off - 1 => Log (P) = Log'Old (P))
       and then Log (Off) = Op
       and then U24_Of (Log (Off + 1), Log (Off + 2), Log (Off + 3)) = Frame'Length
       and then Bytes_At (Log, Off, Frame)
       and then Head_OK (Log, LL, Root, Slt, TTL)
       and then Tag_OK (Log, LL, Cid, H, Tg, Op)
   is
      Log0 : constant Byte_Array := Log with Ghost;
   begin
      Append_Apply (Log, LL, Frame, Off, Op);
      NE := NE + 1;
      Lemma_Head_Kept (Log0, Off, Log, LL, Root, Slt, TTL);
      Lemma_New_Tag (Log, Off, LL, Cid, Frame, H, Tg, Op);
      pragma Assert (Bytes_At (Log, Off, Frame));
   end Log_Apply;

   --  The Post of Commit from its parts (a small context for Put_Done).
   procedure Lemma_Commit_Done
     (S0, S : Store; F0, F : Frontier.State; Frame : Byte_Array; H : Header; Off : Log_Size)
   with
     Ghost, Global => null,
     Pre  => Off = S0.LL
       and then Frame'Length in Frame_Size
       and then S.Log_Cap = S0.Log_Cap
       and then Valid (S, F)
       and then S.Root = S0.Root and then S.Slt = S0.Slt and then S.TTL = S0.TTL
       and then S.Cid = S0.Cid and then S.Fnd = S0.Fnd and then S.Self = S0.Self
       and then S.Pins = S0.Pins
       and then S0.LL <= S0.Log_Cap and then S0.NE <= S0.LL
       and then S.LL = Off + Apply_Prefix + Frame'Length
       and then S.LL <= S.Log_Cap
       and then S.NE = S0.NE + 1
       and then (for all P in 0 .. Off - 1 => S.Log (P) = S0.Log (P))
       and then S.Log (Off) = Op_Apply
       and then U24_Of (S.Log (Off + 1), S.Log (Off + 2), S.Log (Off + 3)) = Frame'Length
       and then Bytes_At (S.Log, Off, Frame)
       and then Effective (F0, S0.TTL, H)
       and then not Log_Short (S0, Apply_Prefix + Frame'Length)
       and then not Data_Full (F0, H)
       and then not Auth_Rule (F0, H)
       and then Applied_H (F0, F, H, S.TTL)
       and then (if Holds (F, H) then Tag_Of (F, H) = Make_Tag (Off, Frame'Length))
       and then S.SS = Seq_After (S0, H),
     Post => Put_Done (S0, S, F0, F, Frame, H, Off, OK)
   is
   begin
      pragma Assert (Log_Length (S0) = S0.LL and then Log_Length (S) = S.LL);
      pragma Assert (Log_Entries (S0) = S0.NE and then Log_Entries (S) = S.NE);
      pragma Assert (Same_Identity (S0, S));
      pragma Assert (Log_Extends (S0, S));
      pragma Assert (for all J in Frame'Range =>
                       S.Log (J - Frame'First + (Off + Apply_Prefix)) = Frame (J));
      pragma Assert (for all J in Frame'Range =>
                       Log_Byte (S, J - Frame'First + (Off + Apply_Prefix)) = Frame (J));
      pragma Assert (Op_At (S, Off) = Op_Apply and then Len_At (S, Off) = Frame'Length);
      pragma Assert (Appended (S0, S, Frame, Off));
   end Lemma_Commit_Done;

   ---------------------------------------------------------------------------
   --  The capture (AUDIT.md H12).
   ---------------------------------------------------------------------------

   --  Ceiled, from the Posts of Frontier.Raise_Ceil (F0 to F1: the same
   --  rows) and of Expiry_Step (F1 to F2).
   procedure Lemma_Ceiled (F0, F1, F2 : Frontier.State; H : Header; TTL : U48) with
     Ghost, Global => null,
     Pre  => Count (F1) = Count (F0)
       and then (for all I in 1 .. Count (F0) => Held (F1, I) = Held (F0, I))
       and then Max_Ceil (F2) = Ceil_Of (H)
       and then Has_Ceil (F2) and then Ceil_Held (F2) = H
       and then Fresh (F2, TTL)
       and then (for all I in 1 .. Count (F2) => Holds (F1, Held (F2, I)))
       and then (for all I in 1 .. Count (F1) =>
                   Holds (F2, Held (F1, I)) or else Expired_In (Held (F1, I), F2, TTL)),
     Post => Ceiled (F0, F2, H, TTL)
   is
      --  Proved; at run time the invariants would cost O(n^2) per call.
      pragma Assertion_Policy (Loop_Invariant => Ignore);
   begin
      for I in 1 .. Count (F2) loop
         pragma Assert (Held (F0, Index_Of (F1, Held (F2, I))) = Held (F2, I));
         pragma Assert (not Expired_In (Held (F2, I), F2, TTL));
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              Holds (F0, Held (F2, I2)) and then not Expired_In (Held (F2, I2), F2, TTL));
      end loop;
      for I in 1 .. Count (F0) loop
         pragma Assert (Held (F1, I) = Held (F0, I));
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              Holds (F2, Held (F0, I2)) or else Expired_In (Held (F0, I2), F2, TTL));
      end loop;
   end Lemma_Ceiled;

   --  Ceiled against a state with the same records as the one the capture
   --  started from (Commit: the state before the refused Frontier.Apply).
   procedure Lemma_Ceiled_Old (FA, FB, F : Frontier.State; H : Header; TTL : U48) with
     Ghost, Global => null,
     Pre  => Count (FB) = Count (FA)
       and then (for all I in 1 .. Count (FA) => Held (FB, I) = Held (FA, I))
       and then Ceiled (FB, F, H, TTL),
     Post => Ceiled (FA, F, H, TTL)
   is
      --  Proved; at run time the invariants would cost O(n^2) per call.
      pragma Assertion_Policy (Loop_Invariant => Ignore);
   begin
      for I in 1 .. Count (F) loop
         pragma Assert (Held (FA, Index_Of (FB, Held (F, I))) = Held (F, I));
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              Holds (FA, Held (F, I2)) and then not Expired_In (Held (F, I2), F, TTL));
      end loop;
      for I in 1 .. Count (FA) loop
         pragma Assert (Held (FB, I) = Held (FA, I));
         pragma Loop_Invariant
           (for all I2 in 1 .. I =>
              Holds (F, Held (FA, I2)) or else Expired_In (Held (FA, I2), F, TTL));
      end loop;
   end Lemma_Ceiled_Old;

   --  The Post of Capture from its parts (a small context for Captured).
   procedure Lemma_Capture_Done
     (S0, S : Store; F0, F : Frontier.State; Frame : Byte_Array; H : Header; Off : Log_Size)
   with
     Ghost, Global => null,
     Pre  => Off = S0.LL
       and then Frame'Length in Frame_Size
       and then S.Log_Cap = S0.Log_Cap
       and then S.Root = S0.Root and then S.Slt = S0.Slt and then S.TTL = S0.TTL
       and then S.Cid = S0.Cid and then S.Fnd = S0.Fnd and then S.Self = S0.Self
       and then S.Pins = S0.Pins and then S.SS = S0.SS and then S.DA = S0.DA
       and then S0.LL <= S0.Log_Cap and then S0.NE <= S0.LL
       and then S.LL = Off + Apply_Prefix + Frame'Length
       and then S.LL <= S.Log_Cap
       and then S.NE = S0.NE + 1
       and then (for all P in 0 .. Off - 1 => S.Log (P) = S0.Log (P))
       and then S.Log (Off) = Op_Ceil
       and then U24_Of (S.Log (Off + 1), S.Log (Off + 2), S.Log (Off + 3)) = Frame'Length
       and then Bytes_At (S.Log, Off, Frame)
       and then Ceiled (F0, F, H, S.TTL)
       and then Ceil_Tag (F) = Make_Tag (Off, Frame'Length),
     Post => Same_Identity (S0, S)
       and then Pinned (S) = Pinned (S0)
       and then Log_Extends (S0, S)
       and then Off = Log_Length (S0)
       and then Captured (S0, S, F0, F, Frame, H, Off)
   is
   begin
      pragma Assert (Log_Length (S0) = S0.LL and then Log_Length (S) = S.LL);
      pragma Assert (Log_Entries (S0) = S0.NE and then Log_Entries (S) = S.NE);
      pragma Assert (Same_Identity (S0, S));
      pragma Assert (Log_Extends (S0, S));
      pragma Assert (for all J in Frame'Range =>
                       S.Log (J - Frame'First + (Off + Apply_Prefix)) = Frame (J));
      pragma Assert (for all J in Frame'Range =>
                       Log_Byte (S, J - Frame'First + (Off + Apply_Prefix)) = Frame (J));
      pragma Assert (Op_At (S, Off) = Op_Ceil and then Len_At (S, Off) = Frame'Length);
      pragma Assert (Ceil_Appended (S0, S, Frame, Off));
   end Lemma_Capture_Done;

   --  Record the roster frame in the ceiling cell: the CEIL entry at S.LL,
   --  the cell, then expiry at the new horizon. The rows keep their
   --  records and tags (Raise_Ceil has Same_Held), so the tags, seq_self
   --  and the two digest models go across; Expiry_Step sums the data
   --  digest again if it removes a DEL.
   procedure Capture
     (S : in out Store; F : in out Frontier.State; Frame : Byte_Array; H : Header)
   with
     Global => null,
     Pre  => Valid (S, F)
       and then Frame'Length in Frame_Size
       and then Is_Record_Frame (Frame)
       and then Header_Of (Cid (S), Frame) = H
       and then Canonical (H)
       and then Raises_Ceil (F, H)
       and then not Log_Short (S, Apply_Prefix + Frame'Length),
     Post => Valid (S, F)
       and Same_Identity (S'Old, S)
       and Pinned (S) = Pinned (S'Old)
       and Log_Extends (S'Old, S)
       and Captured (S'Old, S, F'Old, F, Frame, H, Log_Length (S'Old))
   is
      Len  : constant Frame_Size := Frame'Length;
      F0   : constant Frontier.State := F with Ghost;
      S0   : constant Store := S with Ghost;
      Log0 : constant Byte_Array := S.Log with Ghost;
      LL0  : constant Log_Size := S.LL;
      Tg   : constant U64 := Make_Tag (S.LL, Len);
   begin
      Lemma_Valid_Parts (S, F);
      Lemma_Frontier_Shape (F);

      --  The CEIL entry.
      Log_Apply (S.Log, S.LL, S.NE, S.Root, S.Slt, S.TTL, S.Cid, Frame, H, Tg, LL0, Op_Ceil);
      Lemma_Tags_Kept (Log0, LL0, S.Log, S.LL, S.Cid, F0);

      --  The cell.
      Frontier.Raise_Ceil (F, H, Tg);
      declare
         F1 : constant Frontier.State := F with Ghost;
      begin
         Lemma_Same_Held (F0, F1);
         Lemma_Tags_Same (S.Log, S.LL, S.Cid, F0, F1);
         Lemma_Seq_Same (F0, F1, S.Self, S.SS);
         Lemma_Hashes_Same (F0, F1);
         Lemma_Models_Ext (S.DD, Data_Hashes (F0), Data_Hashes (F1), Data_Count (F0));
         Lemma_Models_Ext (S.DA, Auth_Hashes (F0), Auth_Hashes (F1), Auth_Count (F0));
         pragma Assert (Ceil_OK (S.Log, S.LL, S.Cid, F1));

         --  Expiry at the new horizon (S7).
         Expiry_Step (F, S.DD, S.DA, S.Log, S.LL, S.Cid, S.TTL, S.Self, S.SS);
         Lemma_Ceil_Kept (S.Log, S.LL, S.Log, S.LL, S.Cid, F1, F);
         pragma Assert (Has_Ceil (F) and then Ceil_Held (F) = H and then Ceil_Tag (F) = Tg);
         Lemma_Ceiled (F0, F1, F, H, S.TTL);
      end;
      Lemma_Valid_Of_Parts (S, F);
      Lemma_Capture_Done (S0, S, F0, F, Frame, H, LL0);
   end Capture;

   --  Put_Done for a capture, from its parts (a small context).
   procedure Lemma_Capture_Put_Done
     (S0, S : Store; F0, F : Frontier.State; Frame : Byte_Array; H : Header; Off : Log_Size)
   with
     Ghost, Global => null,
     Pre  => Frame'Length in Frame_Size
       and then Valid (S, F)
       and then Same_Identity (S0, S)
       and then Pinned (S) = Pinned (S0)
       and then Off = Log_Length (S0)
       and then Log_Extends (S0, S)
       and then Effective (F0, Del_TTL (S0), H)
       and then not Log_Short (S0, Apply_Prefix + Frame'Length)
       and then Auth_Rule (F0, H)
       and then Raises_Ceil (F0, H)
       and then Captured (S0, S, F0, F, Frame, H, Off),
     Post => Put_Done (S0, S, F0, F, Frame, H, Off, Ceil_Only)
   is
   begin
      pragma Assert (Is_Auth (H) and then not Is_Data (H));
      pragma Assert (not Data_Full (F0, H));
      pragma Assert (Ceil_Rule (F0, H));
      pragma Assert (Max_Ceil (F) = Ceil_Of (H));
      pragma Assert (Ceil_Of (H) = H.V.T and then H.V.T > Max_Ceil (F0));
      pragma Assert (Ceil_Step (F0, F, H, Ceil_Only));
   end Lemma_Capture_Put_Done;

   --  Step (7): the record is effective and the log has room. Apply,
   --  append, digests, seq_self, then expiry. If the authorization rows
   --  have no room for a roster that raises maxceil, the capture.
   procedure Commit
     (S      : in out Store;
      F      : in out Frontier.State;
      Frame  : in     Byte_Array;
      H      : in     Header;
      Result :    out Status)
   with
     Global => null,
     Pre  => Valid (S, F)
       and then Frame'Length in Frame_Size
       and then Is_Record_Frame (Frame)
       and then Header_Of (Cid (S), Frame) = H
       and then Canonical (H)
       and then Effective (F, Del_TTL (S), H)
       and then not Log_Short (S, Apply_Prefix + Frame'Length),
     Post => Put_Done (S'Old, S, F'Old, F, Frame, H, Log_Length (S'Old), Result)
   is
      Len     : constant Frame_Size := Frame'Length;
      F0      : constant Frontier.State := F with Ghost;
      S0      : constant Store := S with Ghost;
      Log0    : constant Byte_Array := S.Log with Ghost;
      SS0     : constant U48 := S.SS with Ghost;
      LL0     : constant Log_Size := S.LL;
      Tg      : constant U64 := Make_Tag (S.LL, Len);
      RO      : Index_Range;
      Old_Sum : Acc;
      New_Sum : Acc;
      St      : Status;
   begin
      Lemma_Valid_Parts (S, F);
      Lemma_Frontier_Shape (F);
      RO := Range_Of (F, H);
      if Is_Data (H) then
         Old_Sum := Data_Range_Sum (F, RO.First, RO.Last);
         pragma Assert (Old_Sum = KD.Sum_Of (Data_Hashes (F0), Range_Of (F0, H).First,
                                             Range_Of (F0, H).Last));
      else
         Lemma_Slot_Def (F, H.Issuer);
         pragma Assert (RO.First >= Data_Count (F) + 1);
         Old_Sum := Auth_Range_Sum (F, RO.First - Data_Count (F), RO.Last - Data_Count (F));
         pragma Assert (Old_Sum = KD.Sum_Of (Auth_Hashes (F0),
                                             Range_Of (F0, H).First - Data_Count (F0),
                                             Range_Of (F0, H).Last - Data_Count (F0)));
      end if;

      Frontier.Apply (F, H, Tg, St);
      if St /= OK then
         --  No_Space or Auth_Full: nothing changed.
         Lemma_Valid_Unchanged (S, F0, F);
         Lemma_Unchanged (F0, F);
         pragma Assert (Max_Ceil (F) = Max_Ceil (F0));
         if St = Auth_Full and then Raises_Ceil (F, H) then
            --  AUDIT.md H12: the rows have no room for a roster whose
            --  ceiling is above maxceil. Its ceiling still counts.
            declare
               FM : constant Frontier.State := F with Ghost;
            begin
               pragma Assert (Auth_Rule (F0, H) and then Raises_Ceil (F0, H));
               Capture (S, F, Frame, H);
               Lemma_Ceiled_Old (F0, FM, F, H, S.TTL);
               pragma Assert (Captured (S0, S, F0, F, Frame, H, LL0));
               Lemma_Capture_Put_Done (S0, S, F0, F, Frame, H, LL0);
            end;
            Result := Ceil_Only;
         else
            Result := St;
            pragma Assert (if St = Auth_Full then not Raises_Ceil (F0, H));
            pragma Assert (if St = No_Space then Is_Data (H) and then Ceil_Of (H) = 0);
            pragma Assert (if St = Auth_Full then Ceil_Of (H) <= Max_Ceil (F0));
            pragma Assert (Ceil_Step (F0, F, H, St));
         end if;
         return;
      end if;

      pragma Assert (not Data_Full (F0, H) and then not Auth_Rule (F0, H));
      declare
         F1 : constant Frontier.State := F with Ghost;
      begin
         --  The APPLY entry, and the tags.
         Log_Apply (S.Log, S.LL, S.NE, S.Root, S.Slt, S.TTL, S.Cid, Frame, H, Tg, LL0, Op_Apply);
         Lemma_Tags_Apply (Log0, LL0, S.Log, S.LL, S.Cid, F0, F1, H, Tg);
         Lemma_Ceil_Kept (Log0, LL0, S.Log, S.LL, S.Cid, F0, F1);

         --  The digests (S21): the run or the slot, before and after.
         Lemma_Frontier_Shape (F);
         if Is_Data (H) then
            declare
               RU : constant Index_Range := Range_Of (F, H);
            begin
               New_Sum := Data_Range_Sum (F, RU.First, RU.Last);
               Lemma_Digest_Step (S.DA, S.DD, F0, F1, H, Old_Sum, New_Sum);
               S.DD := KD.Restore (Data_Count (F), Add (Sub (KD.Sum (S.DD), Old_Sum), New_Sum));
               pragma Assert (KD.Models (S.DD, Data_Hashes (F), Data_Count (F)));
               pragma Assert (KD.Models (S.DA, Auth_Hashes (F), Auth_Count (F)));
            end;
         else
            Lemma_Slot_Def (F, H.Issuer);
            declare
               RU : constant Index_Range := Range_Of (F, H);
            begin
               pragma Assert (RU.First >= Data_Count (F) + 1);
               New_Sum := Auth_Range_Sum (F, RU.First - Data_Count (F), RU.Last - Data_Count (F));
               Lemma_Digest_Step (S.DA, S.DD, F0, F1, H, Old_Sum, New_Sum);
               S.DA := KD.Restore (Auth_Count (F), Add (Sub (KD.Sum (S.DA), Old_Sum), New_Sum));
               pragma Assert (KD.Models (S.DA, Auth_Hashes (F), Auth_Count (F)));
               pragma Assert (KD.Models (S.DD, Data_Hashes (F), Data_Count (F)));
            end;
         end if;

         --  seq_self (S16).
         if Is_Data (H) and then H.V.Author = S.Self and then H.V.Seq > S.SS then
            S.SS := H.V.Seq;
         end if;
         Lemma_Seq_Apply (F0, F1, H, S.Self, SS0, S.SS);

         --  Expiry (S7).
         Expiry_Step (F, S.DD, S.DA, S.Log, S.LL, S.Cid, S.TTL, S.Self, S.SS);
         Lemma_Ceil_Kept (S.Log, S.LL, S.Log, S.LL, S.Cid, F1, F);
         Lemma_Applied_H (F0, F1, F, H, S.TTL);
         Lemma_Tag_Final (F1, F, H, Tg);
         pragma Assert (S.SS = Seq_After (S0, H));
         Lemma_Valid_Of_Parts (S, F);
         Lemma_Commit_Done (S0, S, F0, F, Frame, H, LL0);
      end;
      Result := OK;
   end Commit;

   procedure Apply_Frame
     (S      : in out Store;
      F      : in out Frontier.State;
      Frame  : in     Byte_Array;
      H      : in     Header;
      Off    :    out Log_Size;
      Result :    out Status)
   with
     Global => null,
     Pre  => Valid (S, F)
       and then Frame'Length in Frame_Size
       and then Is_Record_Frame (Frame)
       and then Header_Of (Cid (S), Frame) = H
       and then Canonical (H),
     Post => Put_Done (S'Old, S, F'Old, F, Frame, H, Off, Result)
   is
   begin
      Off := S.LL;
      if Holds (F, H) or else (Admitted (F, H) and then not Dom (F, H)
                               and then Expired_In (H, F, S.TTL)
                               and then not Drops_Any (F, H))
      then
         Result := OK;
         if Holds (F, H) then
            Lemma_Frontier_Held (F, Index_Of (F, H));
            --  T19, the step: a held record's ceiling is in maxceil.
            Lemma_Ceil_Bound (F, H);
         else
            pragma Assert (H.K = K_Del and then Ceil_Of (H) = 0);
         end if;
      elsif not Admitted (F, H) then
         Result := Inadmissible;
         pragma Assert (Is_Data (H) and then Ceil_Of (H) = 0);
      elsif Dom (F, H) then
         Result := Dominated;
         --  A dominated roster's ceiling is at most its dominator's.
         Lemma_Ceil_Bound (F, H);
      elsif S.Log_Cap - S.LL < Apply_Prefix + Frame'Length then
         Result := Log_Full;
      else
         Commit (S, F, Frame, H, Result);
         return;
      end if;
      Lemma_Unchanged_Refl (F);
   end Apply_Frame;

   procedure Put_Frame
     (S      : in out Store;
      F      : in out Frontier.State;
      Frame  : in     Byte_Array;
      H      : in     Header;
      Off    :    out Log_Size;
      Result :    out Status)
   is
   begin
      Lemma_Verified_Canonical (S.Cid, S.Root, Frame);
      Apply_Frame (S, F, Frame, H, Off, Result);
   end Put_Frame;

   --  Ceil_Frame is Put_Ceil without the signature precondition (replay).
   procedure Ceil_Frame
     (S      : in out Store;
      F      : in out Frontier.State;
      Frame  : in     Byte_Array;
      H      : in     Header;
      Off    :    out Log_Size;
      Result :    out Status)
   with
     Global => null,
     Pre  => Valid (S, F)
       and then Frame'Length in Frame_Size
       and then Is_Record_Frame (Frame)
       and then Header_Of (Cid (S), Frame) = H
       and then Canonical (H)
       and then H.K = K_Roster,
     Post => Ceil_Done (S'Old, S, F'Old, F, Frame, H, Off, Result)
   is
   begin
      Off := S.LL;
      if not Raises_Ceil (F, H) then
         Result := OK;
         pragma Assert (Ceil_Of (H) <= Max_Ceil (F));
      elsif S.Log_Cap - S.LL < Apply_Prefix + Frame'Length then
         Result := Log_Full;
      else
         Capture (S, F, Frame, H);
         Result := Ceil_Only;
         return;
      end if;
      Lemma_Unchanged_Refl (F);
   end Ceil_Frame;

   procedure Put_Ceil
     (S      : in out Store;
      F      : in out Frontier.State;
      Frame  : in     Byte_Array;
      H      : in     Header;
      Off    :    out Log_Size;
      Result :    out Status)
   is
   begin
      Lemma_Verified_Canonical (S.Cid, S.Root, Frame);
      Ceil_Frame (S, F, Frame, H, Off, Result);
   end Put_Ceil;

   ---------------------------------------------------------------------------
   --  Open.
   ---------------------------------------------------------------------------

   --  The HEADER bytes of (Root, Slt, TTL) at the start of Log.
   procedure Write_Header
     (Log : in out Byte_Array; Root : Pubkey; Slt : Salt; TTL : U48)
   with
     Global => null,
     Pre  => Log'First = 0 and then Log'Last >= Header_Len,
     Post => (for all J in 0 .. Magic_Len - 1 => Log (J) = Magic (J))
       and then Log (HO_Version) = Log_Version
       and then (for all J in 0 .. Pubkey_Len - 1 => Log (HO_Root + J) = Root (J))
       and then (for all J in 0 .. Salt_Len - 1 => Log (HO_Salt + J) = Slt (J))
       and then KR.U48_Of (Log (HO_TTL), Log (HO_TTL + 1), Log (HO_TTL + 2),
                           Log (HO_TTL + 3), Log (HO_TTL + 4), Log (HO_TTL + 5)) = TTL
   is
   begin
      KR.Lemma_U48_Round_Trip (TTL);
      Log (0 .. Magic_Len - 1) := Magic;
      Log (HO_Version) := Log_Version;
      Log (HO_Root .. HO_Root + Pubkey_Len - 1) := Root;
      Log (HO_Salt .. HO_Salt + Salt_Len - 1) := Slt;
      for K in 0 .. 5 loop
         Log (HO_TTL + K) := KR.Byte_Of_U48 (TTL, K);
         pragma Loop_Invariant (for all J in 0 .. Magic_Len - 1 => Log (J) = Magic (J));
         pragma Loop_Invariant (Log (HO_Version) = Log_Version);
         pragma Loop_Invariant (for all J in 0 .. Pubkey_Len - 1 => Log (HO_Root + J) = Root (J));
         pragma Loop_Invariant (for all J in 0 .. Salt_Len - 1 => Log (HO_Salt + J) = Slt (J));
         pragma Loop_Invariant
           (for all K2 in 0 .. K => Log (HO_TTL + K2) = KR.Byte_Of_U48 (TTL, K2));
      end loop;
   end Write_Header;

   --  A store with only a HEADER, beside an empty frontier, is Valid.
   procedure Lemma_Valid_Empty (S : Store; F : Frontier.State) with
     Ghost, Global => null,
     Pre  => S.LL = Header_Len and then S.LL <= S.Log_Cap and then S.NE = 0
             and then Is_Frontier (F) and then Count (F) = 0
             and then not Has_Ceil (F)
             and then Frontier.Founding (F) = S.Fnd
             and then S.Fnd = Kome.Keys.To_Key256 (S.Root)
             and then S.TTL in Del_TTL_Min .. Del_TTL_Max
             and then S.Cid = KR.Cid_Of (S.Root, S.Slt, S.TTL)
             and then Head_OK (S.Log, S.LL, S.Root, S.Slt, S.TTL)
             and then KD.Count (S.DA) = 0 and then KD.Sum (S.DA) = Zero
             and then KD.Count (S.DD) = 0 and then KD.Sum (S.DD) = Zero,
     Post => Valid (S, F)
   is
   begin
      pragma Assert (Data_Count (F) = 0 and then Auth_Count (F) = 0);
      KD.Lemma_Sum_Of_Empty (Auth_Hashes (F), 1, 0);
      KD.Lemma_Sum_Of_Empty (Data_Hashes (F), 1, 0);
      Lemma_Eq_Iff_Value (KD.Sum (S.DA), Zero);
      Lemma_Eq_Iff_Value (KD.Sum_Of (Auth_Hashes (F), 1, 0), Zero);
      Lemma_Eq_Iff_Value (KD.Sum (S.DA), KD.Sum_Of (Auth_Hashes (F), 1, 0));
      Lemma_Eq_Iff_Value (KD.Sum (S.DD), Zero);
      Lemma_Eq_Iff_Value (KD.Sum_Of (Data_Hashes (F), 1, 0), Zero);
      Lemma_Eq_Iff_Value (KD.Sum (S.DD), KD.Sum_Of (Data_Hashes (F), 1, 0));
      pragma Assert (Tags_OK (S.Log, S.LL, S.Cid, F));
      pragma Assert (Ceil_OK (S.Log, S.LL, S.Cid, F));
      pragma Assert (Fresh (F, S.TTL));
      pragma Assert (Seq_OK (F, S.Self, S.SS));
      pragma Assert (KD.Models (S.DA, Auth_Hashes (F), 0));
      pragma Assert (KD.Models (S.DD, Data_Hashes (F), 0));
   end Lemma_Valid_Empty;

   procedure Open
     (Root_PK : Pubkey;
      Salt    : Kome.Salt;
      Del_TTL : U48;
      Self_PK : Pubkey;
      F       : Frontier.State;
      S       : out Store)
   is
   begin
      S.Root := Root_PK;
      S.Slt  := Salt;
      S.TTL  := Del_TTL;
      S.Cid  := KR.Cid_Of (Root_PK, Salt, Del_TTL);
      S.Fnd  := Kome.Keys.To_Key256 (Root_PK);
      S.Self := Kome.Keys.To_Key256 (Self_PK);
      S.SS   := 0;
      S.DA   := KD.Empty;
      S.DD   := KD.Empty;
      S.Pins := 0;
      S.NE   := 0;
      S.Log  := [others => 0];
      Write_Header (S.Log, S.Root, S.Slt, S.TTL);
      S.LL   := Header_Len;
      pragma Assert (Head_OK (S.Log, S.LL, S.Root, S.Slt, S.TTL));
      Lemma_Valid_Empty (S, F);
   end Open;

   ---------------------------------------------------------------------------
   --  Reading.
   ---------------------------------------------------------------------------

   function Read_Frame (S : Store; Off : Natural) return Byte_Array is
      L : constant Natural := Len_At (S, Off);
   begin
      return R : Byte_Array (0 .. L - 1) := [others => 0] do
         for K in 0 .. L - 1 loop
            R (K) := S.Log (Off + Apply_Prefix + K);
            pragma Loop_Invariant
              (for all K2 in 0 .. K => R (K2) = Log_Byte (S, Off + Apply_Prefix + K2));
         end loop;
      end return;
   end Read_Frame;

   function Log_Bytes (S : Store) return Byte_Array is
     (S.Log (0 .. Log_Length (S) - 1));

   ---------------------------------------------------------------------------
   --  Pins.
   ---------------------------------------------------------------------------

   procedure Pin (S : in out Store; F : Frontier.State) is
   begin
      S.Pins := S.Pins + 1;
   end Pin;

   procedure Unpin (S : in out Store; F : Frontier.State) is
   begin
      S.Pins := S.Pins - 1;
   end Unpin;

   ---------------------------------------------------------------------------
   --  Compact.
   ---------------------------------------------------------------------------

   function Retagged (Old_F, F : Frontier.State) return Boolean is
     (Is_Frontier (F)
      and then Frontier.Founding (F) = Frontier.Founding (Old_F)
      and then Max_Ceil (F) = Max_Ceil (Old_F)
      and then Data_Count (F) = Data_Count (Old_F)
      and then Auth_Count (F) = Auth_Count (Old_F)
      and then Count (F) = Count (Old_F)
      and then (for all J in 1 .. Data_Count (F) => Data_Held (F, J) = Data_Held (Old_F, J))
      and then (for all J in 1 .. Count (F) =>
                  Held (F, J) = Held (Old_F, J)
                  and then Tag_Len (Tag (F, J)) = Tag_Len (Tag (Old_F, J)))
      and then Has_Ceil (F) = Has_Ceil (Old_F)
      and then (if Has_Ceil (F)
                then Ceil_Held (F) = Ceil_Held (Old_F)
                     and then Tag_Len (Ceil_Tag (F)) = Tag_Len (Ceil_Tag (Old_F))));

   function Compact_Layout (Old_S : Store; Old_F : Frontier.State; S : Store; F : Frontier.State)
     return Boolean
   is (Log_Length (S) >= Header_Len + Seq_Len
       and then Log_Length (Old_S) >= Header_Len
       and then (for all K in 0 .. Header_Len - 1 => Log_Byte (S, K) = Log_Byte (Old_S, K))
       and then (for all J in 1 .. Count (F) =>
                   Tag_End (Tag (F, J)) <= Log_Length (S) - Seq_Len
                   and then Tag_Len (Tag (F, J)) = Tag_Len (Tag (Old_F, J)))
       and then Op_At (S, Log_Length (S) - Seq_Len) = Op_Seq
       and then Code_At (S, Log_Length (S) - Seq_Len + 1) = Seq_Self (S)
       and then Log_Entries (S) = Count (F) + 1 + (if Has_Ceil (F) then 1 else 0)
       and then (if Has_Ceil (F)
                 then Tag_Off (Ceil_Tag (F)) = Header_Len
                      and then Tag_End (Ceil_Tag (F)) <= Log_Length (S) - Seq_Len));

   --  The position of flat index I in the copy order (the inverse of Ord).
   function Pos (F : Frontier.State; I : Held_Index) return Positive is
     (if I > Data_Count (F) then I - Data_Count (F) else Auth_Count (F) + I)
     with Pre => I <= Count (F);

   --  The bytes of the APPLYs of the first N records in copy order.
   function Body_Size (F : Frontier.State; N : Natural) return Long_Long_Integer is
     (if N = 0 then 0
      else Body_Size (F, N - 1) + Long_Long_Integer (Apply_Prefix + Tag_Len (Tag (F, Ord (F, N)))))
   with Ghost,
        Pre  => N <= Count (F),
        Post => Body_Size'Result >= 4 * Long_Long_Integer (N)
                and then Body_Size'Result <= Long_Long_Integer (N) * (2**24 + Apply_Prefix),
        Subprogram_Variant => (Decreases => N);

   --  A record whose frame moved from Log0 at T0 to Log1 at T1, byte for
   --  byte, keeps a good tag.
   procedure Lemma_Tag_Moved
     (Log0 : Byte_Array; LL0 : Log_Size; Log1 : Byte_Array; LL1 : Log_Size;
      Cid : Hash256; X : Header; T0, T1 : U64; Op : Byte)
   with
     Ghost, Global => null,
     Pre  => Log0'First = 0 and then LL0 <= Log0'Last
             and then Log1'First = 0 and then LL1 <= Log1'Last
             and then Tag_OK (Log0, LL0, Cid, X, T0, Op)
             and then Tag_Len (T1) = Tag_Len (T0)
             and then Tag_Off (T1) >= Header_Len
             and then Tag_End (T1) <= LL1
             and then (for all Q in Tag_Off (T1) .. Tag_End (T1) - 1 =>
                         Log1 (Q) = Log0 (Q - Tag_Off (T1) + Tag_Off (T0))),
     Post => Tag_OK (Log1, LL1, Cid, X, T1, Op)
   is
      O0 : constant Natural := Tag_Off (T0);
      O1 : constant Natural := Tag_Off (T1);
      L  : constant Natural := Tag_Len (T0);
   begin
      pragma Assert (Tag_OK (Log0, LL0, Cid, X, T0, Op));
      pragma Assert (L in Frame_Size and then O0 >= Header_Len and then O0 + Apply_Prefix + L <= LL0);
      pragma Assert (Frame_Is (Slice_At (Log0, T0), Cid, X));
      pragma Assert (Tag_End (T1) = O1 + Apply_Prefix + L);
      pragma Assert (O1 + Apply_Prefix + L <= LL1);
      pragma Assert (Log1 (O1) = Log0 (O0));
      pragma Assert (Log1 (O1 + 1) = Log0 (O0 + 1) and then Log1 (O1 + 2) = Log0 (O0 + 2)
                     and then Log1 (O1 + 3) = Log0 (O0 + 3));
      pragma Assert (for all Q in Slice_At (Log0, T0)'Range =>
                       Slice_At (Log1, T1) (Q - Slice_At (Log0, T0)'First
                                            + Slice_At (Log1, T1)'First)
                       = Slice_At (Log0, T0) (Q));
      Lemma_Frame_Is_Congruent (Cid, X, Slice_At (Log0, T0), Slice_At (Log1, T1));
   end Lemma_Tag_Moved;


   --  Pass 1 of Compact: the compacted log fits (every prefix of the copy
   --  order fits, Body_Size grows).
   procedure Fits_Compacted
     (F : Frontier.State; Lim : Long_Long_Integer; Fits : out Boolean)
   with
     Global => null,
     Pre  => Lim >= 0,
     Post => (if Fits then (for all C in 0 .. Count (F) => Body_Size (F, C) <= Lim))
   is
      Tot : Long_Long_Integer := 0;
   begin
      for C in 1 .. Count (F) loop
         Tot := Tot + Long_Long_Integer (Apply_Prefix + Tag_Len (Tag (F, Ord (F, C))));
         if Tot > Lim then
            Fits := False;
            return;
         end if;
         pragma Loop_Invariant (Tot = Body_Size (F, C) and then Tot <= Lim);
         pragma Loop_Invariant (for all C2 in 0 .. C => Body_Size (F, C2) <= Tot);
      end loop;
      Fits := True;
   end Fits_Compacted;

   --  One step of Copy_Frames: copy the APPLY of flat index I to Buf at P
   --  and give I the tag of its new place.
   procedure Copy_One
     (F   : in out Frontier.State;
      I   : Positive;
      Log : Byte_Array;
      LL  : Log_Size;
      Buf : in out Byte_Array;
      P   : in out Log_Size)
   with
     Global => null,
     Pre  => Is_Frontier (F) and then I <= Count (F)
       and then Log'First = 0 and then LL <= Log'Last
       and then Buf'First = 0 and then Buf'Last <= Log_Max
       and then Tag_Len (Tag (F, I)) in Frame_Size
       and then Tag_Off (Tag (F, I)) >= Header_Len
       and then Tag_End (Tag (F, I)) <= LL
       and then P >= Header_Len
       and then P + Apply_Prefix + Tag_Len (Tag (F, I)) <= Buf'Last,
     Post => P = P'Old + Apply_Prefix + Tag_Len (Tag (F'Old, I))
       and then Is_Frontier (F)
       and then Frontier.Founding (F) = Frontier.Founding (F'Old)
       and then Max_Ceil (F) = Max_Ceil (F'Old)
       and then Data_Count (F) = Data_Count (F'Old)
       and then Auth_Count (F) = Auth_Count (F'Old)
       and then Count (F) = Count (F'Old)
       and then (for all J in 1 .. Data_Count (F) => Data_Held (F, J) = Data_Held (F'Old, J))
       and then (for all J in 1 .. Count (F) =>
                   Held (F, J) = Held (F'Old, J)
                   and then (if J /= I then Tag (F, J) = Tag (F'Old, J)))
       and then Tag_Off (Tag (F, I)) = P'Old
       and then Tag_Len (Tag (F, I)) = Tag_Len (Tag (F'Old, I))
       and then Tag_End (Tag (F, I)) = P
       and then (for all Q in 0 .. P'Old - 1 => Buf (Q) = Buf'Old (Q))
       and then (for all Q in P'Old .. P - 1 =>
                   Buf (Q) = Log (Q - P'Old + Tag_Off (Tag (F'Old, I))))
       and then Ceil_Same (F'Old, F)
   is
      O  : constant Natural := Tag_Off (Tag (F, I));
      L  : constant Natural := Tag_Len (Tag (F, I));
      NT : constant U64 := Make_Tag (P, L);
   begin
      Buf (P .. P + Apply_Prefix + L - 1) := Log (O .. O + Apply_Prefix + L - 1);
      Lemma_Tag_Round_Trip (P, L);
      pragma Assert (Tag_Off (NT) = P and then Tag_Len (NT) = L);
      Frontier.Set_Tag (F, I, NT);
      pragma Assert (Tag (F, I) = NT);
      pragma Assert (Tag_Off (Tag (F, I)) = P);
      P := P + Apply_Prefix + L;
   end Copy_One;

   --  The records copied before step C keep good tags when Copy_One
   --  writes the next APPLY above them (Lemma_Tag_OK_Kept).
   procedure Lemma_Copied_Kept
     (Buf0 : Byte_Array; P0 : Log_Size; Buf1 : Byte_Array; P1 : Log_Size;
      Cid  : Hash256; F1, F : Frontier.State; C : Positive; I : Positive)
   with
     Ghost, Global => null,
     Pre  => Buf0'First = 0 and then P0 <= Buf0'Last
       and then Buf1'First = 0 and then P1 <= Buf1'Last
       and then P0 <= P1
       and then (for all Q in 0 .. P0 - 1 => Buf1 (Q) = Buf0 (Q))
       and then Count (F) = Count (F1)
       and then Data_Count (F) = Data_Count (F1)
       and then Auth_Count (F) = Auth_Count (F1)
       and then I <= Count (F1)
       and then Pos (F1, I) = C
       and then (for all J in 1 .. Count (F1) =>
                   Held (F, J) = Held (F1, J)
                   and then (if J /= I then Tag (F, J) = Tag (F1, J)))
       and then (for all J in 1 .. Count (F1) =>
                   (if Pos (F1, J) < C
                    then Tag_OK (Buf0, P0, Cid, Held (F1, J), Tag (F1, J), Op_Apply))),
     Post => (for all J in 1 .. Count (F) =>
                (if Pos (F, J) < C
                 then Tag_OK (Buf1, P1, Cid, Held (F, J), Tag (F, J), Op_Apply)))
   is
      --  Proved; at run time the invariant would cost O(n^2) per call.
      pragma Assertion_Policy (Loop_Invariant => Ignore);
   begin
      for J in 1 .. Count (F) loop
         if Pos (F, J) < C then
            pragma Assert (Pos (F1, J) = Pos (F, J) and then J /= I);
            pragma Assert (Tag_OK (Buf0, P0, Cid, Held (F1, J), Tag (F1, J), Op_Apply));
            Lemma_Tag_OK_Kept (Buf0, P0, Buf1, P1, Cid, Held (F, J), Tag (F, J), Op_Apply);
         end if;
         pragma Loop_Invariant
           (for all J2 in 1 .. J =>
              (if Pos (F, J2) < C
               then Tag_OK (Buf1, P1, Cid, Held (F, J2), Tag (F, J2), Op_Apply)));
      end loop;
   end Lemma_Copied_Kept;

   --  Step C of Copy_Frames: Copy_One, and the tags of the records copied
   --  so far (I = Ord (C) is new, the others are kept).
   procedure Copy_Step
     (F   : in out Frontier.State;
      I   : Positive;
      C   : Positive;
      Log : Byte_Array;
      LL  : Log_Size;
      Cid : Hash256;
      Buf : in out Byte_Array;
      P   : in out Log_Size)
   with
     Global => null,
     Pre  => Is_Frontier (F) and then I <= Count (F) and then Pos (F, I) = C
       and then Log'First = 0 and then LL <= Log'Last
       and then Buf'First = 0 and then Buf'Last <= Log_Max
       and then Tag_OK (Log, LL, Cid, Held (F, I), Tag (F, I), Op_Apply)
       and then P >= Header_Len
       and then P <= Buf'Last
       and then P + Apply_Prefix + Tag_Len (Tag (F, I)) <= Buf'Last
       and then (for all J in 1 .. Count (F) =>
                   (if Pos (F, J) < C
                    then Tag_OK (Buf, P, Cid, Held (F, J), Tag (F, J), Op_Apply))),
     Post => P = P'Old + Apply_Prefix + Tag_Len (Tag (F'Old, I))
       and then Is_Frontier (F)
       and then Frontier.Founding (F) = Frontier.Founding (F'Old)
       and then Max_Ceil (F) = Max_Ceil (F'Old)
       and then Data_Count (F) = Data_Count (F'Old)
       and then Auth_Count (F) = Auth_Count (F'Old)
       and then Count (F) = Count (F'Old)
       and then (for all J in 1 .. Data_Count (F) => Data_Held (F, J) = Data_Held (F'Old, J))
       and then (for all J in 1 .. Count (F) =>
                   Held (F, J) = Held (F'Old, J)
                   and then (if J /= I then Tag (F, J) = Tag (F'Old, J)))
       and then Tag_Len (Tag (F, I)) = Tag_Len (Tag (F'Old, I))
       and then (for all Q in 0 .. P'Old - 1 => Buf (Q) = Buf'Old (Q))
       and then (for all J in 1 .. Count (F) =>
                   (if Pos (F, J) <= C
                    then Tag_OK (Buf, P, Cid, Held (F, J), Tag (F, J), Op_Apply)))
       and then Ceil_Same (F'Old, F)
   is
      F1   : constant Frontier.State := F with Ghost;
      Buf0 : constant Byte_Array := Buf with Ghost;
      P0   : constant Log_Size := P;
   begin
      pragma Assert (Tag_Len (Tag (F, I)) in Frame_Size
                     and then Tag_Off (Tag (F, I)) >= Header_Len
                     and then Tag_End (Tag (F, I)) <= LL);
      Copy_One (F, I, Log, LL, Buf, P);
      pragma Assert (Tag_Off (Tag (F, I)) = P0 and then Tag_End (Tag (F, I)) = P);
      pragma Assert (for all Q in Tag_Off (Tag (F, I)) .. Tag_End (Tag (F, I)) - 1 =>
                       Buf (Q) = Log (Q - Tag_Off (Tag (F, I)) + Tag_Off (Tag (F1, I))));
      Lemma_Tag_Moved (Log, LL, Buf, P, Cid, Held (F, I), Tag (F1, I), Tag (F, I), Op_Apply);
      Lemma_Copied_Kept (Buf0, P0, Buf, P, Cid, F1, F, C, I);
      pragma Assert (for all J in 1 .. Count (F) => (if Pos (F, J) = C then J = I));
   end Copy_Step;

   --  Pass 2 of Compact: copy every APPLY, in copy order (Ord), into Buf
   --  from Base on, and retag the records. Base is the end of the HEADER,
   --  or of the CEIL entry of the cell's record; the bytes below it stay.
   --  P is where the frames end.
   procedure Copy_Frames
     (F    : in out Frontier.State;
      Log  : Byte_Array;
      LL   : Log_Size;
      Cid  : Hash256;
      Lim  : Long_Long_Integer;
      Base : Log_Size;
      Buf  : in out Byte_Array;
      P    : out Log_Size)
   with
     Global => null,
     Pre  => Is_Frontier (F)
       and then Log'First = 0 and then LL <= Log'Last and then Log'Last <= Log_Max
       and then LL >= Header_Len
       and then Buf'First = 0 and then Buf'Last <= Log_Max
       and then Base >= Header_Len and then Base <= Buf'Last
       and then Lim >= 0
       and then Lim = Long_Long_Integer (Buf'Last) - Long_Long_Integer (Base + Seq_Len)
       and then Tags_OK (Log, LL, Cid, F)
       and then (for all C in 0 .. Count (F) => Body_Size (F, C) <= Lim),
     Post => Retagged (F'Old, F)
       and then Ceil_Same (F'Old, F)
       and then Long_Long_Integer (P) = Long_Long_Integer (Base) + Body_Size (F'Old, Count (F))
       and then P >= Base
       and then P <= Buf'Last - Seq_Len
       and then (for all Q in 0 .. Base - 1 => Buf (Q) = Buf'Old (Q))
       and then Tags_OK (Buf, P, Cid, F)
   is
      --  Proved; at run time the invariants would check every copied
      --  record again at each step (O(n^2) frame parses).
      pragma Assertion_Policy (Loop_Invariant => Ignore);
      F0 : constant Frontier.State := F with Ghost;
   begin
      P := Base;
      for C in 1 .. Count (F) loop
         declare
            I : constant Positive := Ord (F, C);
         begin
            pragma Assert (Ord (F0, C) = I and then Pos (F, I) = C);
            pragma Assert (Tag (F, I) = Tag (F0, I) and then Held (F, I) = Held (F0, I));
            pragma Assert (Tag_OK (Log, LL, Cid, Held (F0, I), Tag (F0, I), Op_Apply));
            pragma Assert (Tag_OK (Log, LL, Cid, Held (F, I), Tag (F, I), Op_Apply));
            pragma Assert (Body_Size (F0, C)
                           = Body_Size (F0, C - 1)
                             + Long_Long_Integer (Apply_Prefix + Tag_Len (Tag (F0, I))));
            pragma Assert (Body_Size (F0, C) <= Lim);
            Copy_Step (F, I, C, Log, LL, Cid, Buf, P);
            pragma Assert (Long_Long_Integer (P) = Long_Long_Integer (Base) + Body_Size (F0, C));
         end;
         pragma Loop_Invariant (Retagged (F0, F));
         pragma Loop_Invariant (Ceil_Same (F0, F));
         pragma Loop_Invariant
           (Long_Long_Integer (P) = Long_Long_Integer (Base) + Body_Size (F0, C));
         pragma Loop_Invariant (P >= Base);
         pragma Loop_Invariant (for all Q in 0 .. Base - 1 => Buf (Q) = Buf'Loop_Entry (Q));
         pragma Loop_Invariant
           (for all J in 1 .. Count (F) =>
              (if Pos (F, J) <= C then Tag_OK (Buf, P, Cid, Held (F, J), Tag (F, J), Op_Apply)
               else Tag (F, J) = Tag (F0, J)));
         pragma Loop_Invariant (Count (F) = Count (F0));
      end loop;
      pragma Assert (Count (F) = Count (F0));
      pragma Assert (for all J in 1 .. Count (F) => Pos (F, J) <= Count (F0));
      pragma Assert (for all J in 1 .. Count (F) =>
                       Tag_OK (Buf, P, Cid, Held (F, J), Tag (F, J), Op_Apply));
      Lemma_Tags_OK_Intro (Buf, P, Cid, F);
   end Copy_Frames;

   --  AUDIT.md H12: the CEIL entry of the cell's record moved to
   --  Header_Len of Buf, byte for byte. Give the cell the tag of its new
   --  place; the rows keep their records and tags.
   procedure Retag_Cell
     (F   : in out Frontier.State;
      Log : Byte_Array;
      LL  : Log_Size;
      Cid : Hash256;
      Buf : Byte_Array;
      P   : Log_Size)
   with
     Global => null,
     Pre  => Is_Frontier (F) and then Has_Ceil (F)
       and then Log'First = 0 and then LL <= Log'Last
       and then Buf'First = 0 and then P <= Buf'Last
       and then Ceil_OK (Log, LL, Cid, F)
       and then Tags_OK (Buf, P, Cid, F)
       and then Header_Len + Apply_Prefix + Tag_Len (Ceil_Tag (F)) <= P
       and then (for all Q in Header_Len .. Header_Len + Apply_Prefix + Tag_Len (Ceil_Tag (F)) - 1 =>
                   Buf (Q) = Log (Q - Header_Len + Tag_Off (Ceil_Tag (F)))),
     Post => Is_Frontier (F)
       and then Frontier.Founding (F) = Frontier.Founding (F'Old)
       and then Same_Held (F'Old, F)
       and then Max_Ceil (F) = Max_Ceil (F'Old)
       and then Has_Ceil (F)
       and then Ceil_Held (F) = Ceil_Held (F'Old)
       and then Tag_Len (Ceil_Tag (F)) = Tag_Len (Ceil_Tag (F'Old))
       and then Tag_Off (Ceil_Tag (F)) = Header_Len
       and then Ceil_OK (Buf, P, Cid, F)
       and then Tags_OK (Buf, P, Cid, F)
   is
      F1 : constant Frontier.State := F with Ghost;
      T0 : constant U64 := Ceil_Tag (F);
      L  : constant Natural := Tag_Len (T0);
   begin
      Lemma_Tag_OK_Bounds (Log, LL, Cid, Ceil_Held (F), T0, Op_Ceil);
      Lemma_Tag_Round_Trip (Header_Len, L);
      declare
         NT : constant U64 := Make_Tag (Header_Len, L);
      begin
         pragma Assert (Tag_Off (NT) = Header_Len and then Tag_Len (NT) = L);
         pragma Assert (Tag_End (NT) = Header_Len + Apply_Prefix + L);
         Frontier.Set_Ceil_Tag (F, NT);
         Lemma_Tag_Moved (Log, LL, Buf, P, Cid, Ceil_Held (F), T0, NT, Op_Ceil);
      end;
      Lemma_Same_Held (F1, F);
      Lemma_Tags_Same (Buf, P, Cid, F1, F);
   end Retag_Cell;

   --  Retagged after Retag_Cell (F2 to F3) on a state that Copy_Frames
   --  retagged (F0 to F2).
   procedure Lemma_Retagged_Cell (F0, F2, F3 : Frontier.State) with
     Ghost, Global => null,
     Pre  => Retagged (F0, F2)
       and then Is_Frontier (F3)
       and then Frontier.Founding (F3) = Frontier.Founding (F2)
       and then Same_Held (F2, F3)
       and then Max_Ceil (F3) = Max_Ceil (F2)
       and then Has_Ceil (F2) and then Has_Ceil (F3)
       and then Ceil_Held (F3) = Ceil_Held (F2)
       and then Tag_Len (Ceil_Tag (F3)) = Tag_Len (Ceil_Tag (F2)),
     Post => Retagged (F0, F3)
   is
   begin
      Lemma_Same_Held (F2, F3);
   end Lemma_Retagged_Cell;

   procedure Compact
     (S      : in out Store;
      F      : in out Frontier.State;
      Buf    : in out Byte_Array;
      Result :    out Status)
   is
      --  The CEIL entry of the cell's record (AUDIT.md H12), and where the
      --  APPLYs start.
      CL   : constant Natural :=
        (if Has_Ceil (F) then Apply_Prefix + Tag_Len (Ceil_Tag (F)) else 0);
      Base : constant Natural := Header_Len + CL;
      Lim  : constant Long_Long_Integer :=
        Long_Long_Integer (S.Log_Cap) - Long_Long_Integer (Base + Seq_Len);
      Fits : Boolean;
   begin
      if S.Pins > 0 then
         Result := Busy;
         Lemma_Unchanged_Refl (F);
         return;
      end if;
      if Lim < 0 then
         Result := Log_Full;
         Lemma_Unchanged_Refl (F);
         return;
      end if;
      Fits_Compacted (F, Lim, Fits);
      if not Fits then
         Result := Log_Full;
         Lemma_Unchanged_Refl (F);
         return;
      end if;

      declare
         F0   : constant Frontier.State := F with Ghost;
         Log0 : constant Byte_Array := S.Log with Ghost;
         LL0  : constant Log_Size := S.LL with Ghost;
         P    : Log_Size;
      begin
         Lemma_Valid_Parts (S, F);

         --  The HEADER, then the CEIL of the cell's record.
         for Q in 0 .. Header_Len - 1 loop
            Buf (Q) := S.Log (Q);
            pragma Loop_Invariant (for all Q2 in 0 .. Q => Buf (Q2) = S.Log (Q2));
         end loop;
         if Has_Ceil (F) then
            Lemma_Tag_OK_Bounds (S.Log, S.LL, S.Cid, Ceil_Held (F), Ceil_Tag (F), Op_Ceil);
            declare
               O : constant Natural := Tag_Off (Ceil_Tag (F));
            begin
               Buf (Header_Len .. Base - 1) := S.Log (O .. O + CL - 1);
               pragma Assert (for all Q in Header_Len .. Base - 1 =>
                                Buf (Q) = S.Log (Q - Header_Len + O));
            end;
         end if;
         pragma Assert (for all Q in 0 .. Header_Len - 1 => Buf (Q) = S.Log (Q));

         --  The rows.
         Copy_Frames (F, S.Log, S.LL, S.Cid, Lim, Base, Buf, P);
         pragma Assert (for all Q in 0 .. Header_Len - 1 => Buf (Q) = S.Log (Q));
         Lemma_Ceil_Kept (S.Log, S.LL, S.Log, S.LL, S.Cid, F0, F);

         --  The cell's tag.
         if Has_Ceil (F) then
            declare
               F2 : constant Frontier.State := F with Ghost;
            begin
               pragma Assert (Ceil_Tag (F) = Ceil_Tag (F0));
               pragma Assert
                 (for all Q in Header_Len .. Header_Len + Apply_Prefix + Tag_Len (Ceil_Tag (F)) - 1 =>
                    Buf (Q) = S.Log (Q - Header_Len + Tag_Off (Ceil_Tag (F))));
               Retag_Cell (F, S.Log, S.LL, S.Cid, Buf, P);
               Lemma_Retagged_Cell (F0, F2, F);
               pragma Assert (Tag_End (Ceil_Tag (F)) = Base);
            end;
         end if;
         pragma Assert (Retagged (F0, F));
         pragma Assert (Ceil_OK (Buf, P, S.Cid, F));
         pragma Assert (for all J in 1 .. Count (F) =>
                          Tag_OK (Buf, P, S.Cid, Held (F, J), Tag (F, J), Op_Apply));
         pragma Assert (for all J in 1 .. Count (F) => Tag_End (Tag (F, J)) <= P);
         declare
            Buf1 : constant Byte_Array := Buf with Ghost;
            P1   : constant Log_Size := P with Ghost;
         begin
            Append_Seq (Buf, P, S.SS);
            Lemma_Tags_Kept (Buf1, P1, Buf, P, S.Cid, F);
            Lemma_Ceil_Kept (Buf1, P1, Buf, P, S.Cid, F, F);
            pragma Assert (for all Q in 0 .. Header_Len - 1 => Buf (Q) = Log0 (Q));
         end;

         --  Copy the new log back (only its length).
         for J in 0 .. P - 1 loop
            S.Log (J) := Buf (J);
            pragma Loop_Invariant (for all J2 in 0 .. J => S.Log (J2) = Buf (J2));
         end loop;
         S.LL := P;
         S.NE := Count (F) + 1 + (if Has_Ceil (F) then 1 else 0);
         Lemma_Tags_Kept (Buf, P, S.Log, S.LL, S.Cid, F);
         Lemma_Ceil_Kept (Buf, P, S.Log, S.LL, S.Cid, F, F);
         pragma Assert (for all J in 1 .. Count (F) => Tag_End (Tag (F, J)) <= S.LL - Seq_Len);
         pragma Assert (for all J in 0 .. Header_Len - 1 => S.Log (J) = Log0 (J));
         Lemma_Head_Same (Log0, LL0, S.Log, S.LL, S.Root, S.Slt, S.TTL);
         pragma Assert (Count (F) = Count (F0));
         pragma Assert (Log_Entries (S) = Count (F) + 1 + (if Has_Ceil (F) then 1 else 0));
         pragma Assert (not Compact_Due (S, F));
         pragma Assert (if Has_Ceil (F)
                        then Tag_Off (Ceil_Tag (F)) = Header_Len
                             and then Tag_End (Ceil_Tag (F)) <= Log_Length (S) - Seq_Len);
         Lemma_Rest_Same (F0, F, S.TTL, S.Self, S.SS);
         Lemma_Hashes_Same (F0, F);
         Lemma_Models_Ext (S.DD, Data_Hashes (F0), Data_Hashes (F), Data_Count (F0));
         Lemma_Models_Ext (S.DA, Auth_Hashes (F0), Auth_Hashes (F), Auth_Count (F0));
         Lemma_Valid_Of_Parts (S, F);
         pragma Assert (Valid (S, F));
         Result := OK;
      end;
   end Compact;

   ---------------------------------------------------------------------------
   --  Open_From_Log.
   ---------------------------------------------------------------------------

   function Replayed_Prefix
     (Input : Byte_Array; Self_PK : Pubkey; F : Frontier.State; S : Store; VL : Log_Size)
     return Boolean
   is (Valid (S, F)
       and then VL >= Header_Len
       and then Input'Last < S.Log_Cap
       and then Header_Well_Formed (Input)
       and then Log_Length (S) = VL
       and then VL - 1 <= Input'Last
       and then (for all J in 0 .. VL - 1 => Log_Byte (S, J) = Input (J))
       and then (for all J in 0 .. Pubkey_Len - 1 => Root_Key (S) (J) = Input (HO_Root + J))
       and then (for all J in 0 .. Salt_Len - 1 => Salt_Of (S) (J) = Input (HO_Salt + J))
       and then Del_TTL (S) = Header_TTL (Input)
       and then Self_Key (S) = Kome.Keys.To_Key256 (Self_PK)
       and then Pinned (S) = 0);

   --  One CEIL entry of replay at S.LL (AUDIT.md H12): the framing checks
   --  of an APPLY; the frame must be a ROSTER. A CEIL that repeats the
   --  cell's record stays in the log and changes nothing (a duplicated
   --  entry, wherever it stands). Any other CEIL reruns the capture of
   --  Put_Ceil (Ceil_Frame): the rows are not tried, and a roster whose
   --  ceiling is not above maxceil is refused. The contract is the one of
   --  Replay_Entry.
   procedure Replay_Ceil
     (Input  : Byte_Array;
      S      : in out Store;
      F      : in out Frontier.State;
      Result : out Status)
   with
     Global => null,
     Pre  => Input'First = 0 and then Input'Last < S.Log_Cap
       and then Valid (S, F)
       and then S.LL >= Header_Len and then S.LL <= Input'Last
       and then (for all J in 0 .. S.LL - 1 => S.Log (J) = Input (J))
       and then Input (S.LL) = Op_Ceil
       and then Input'Last - S.LL >= Apply_Prefix,
     Post => Valid (S, F)
       and then Same_Identity (S'Old, S)
       and then S.Pins = S'Old.Pins
       and then Result in OK | Malformed | No_Space
       and then (if Result = OK then S.LL > S'Old.LL else S.LL = S'Old.LL)
       and then S.LL - 1 <= Input'Last
       and then (for all J in 0 .. S.LL - 1 => S.Log (J) = Input (J))
   is
      P : constant Log_Size := S.LL;
      L : constant U24_Value := U24_Of (Input (P + 1), Input (P + 2), Input (P + 3));
   begin
      Lemma_Valid_Parts (S, F);
      if L not in Frame_Size or else L > Input'Last - P - Apply_Prefix + 1 then
         Result := Malformed;
         return;
      end if;
      if not Is_Record_Frame (Input (P + Apply_Prefix .. P + Apply_Prefix + L - 1)) then
         Result := Malformed;
         return;
      end if;
      declare
         Frame : constant Byte_Array := Input (P + Apply_Prefix .. P + Apply_Prefix + L - 1);
         H     : constant Header := Header_Of (S.Cid, Frame);
         S1    : constant Store := S with Ghost;
         Off   : Log_Size;
         St    : Status;
      begin
         pragma Assert (for all J in 0 .. P - 1 => S1.Log (J) = Input (J));
         if not Canonical (H) or else H.K /= K_Roster then
            Result := Malformed;
            return;
         end if;
         if Has_Ceil (F) and then Ceil_Held (F) = H then
            --  The cell's record again: the entry stays in the log.
            declare
               Log1 : constant Byte_Array := S.Log with Ghost;
            begin
               pragma Assert (Tags_OK (S.Log, S.LL, S.Cid, F));
               pragma Assert (Ceil_OK (S.Log, S.LL, S.Cid, F));
               pragma Assert (Head_OK (S.Log, S.LL, S.Root, S.Slt, S.TTL));
               pragma Assert (S.NE <= S.LL);
               Append_Apply (S.Log, S.LL, Frame, P, Op_Ceil);
               S.NE := S.NE + 1;
               Lemma_Tags_Kept (Log1, P, S.Log, S.LL, S.Cid, F);
               Lemma_Ceil_Kept (Log1, P, S.Log, S.LL, S.Cid, F, F);
               Lemma_Head_Kept (Log1, P, S.Log, S.LL, S.Root, S.Slt, S.TTL);
               pragma Assert (S.NE <= S.LL);
               pragma Assert (for all J in 0 .. P - 1 => S.Log (J) = Input (J));
               pragma Assert (for all J in Frame'Range => S.Log (J) = Frame (J));
               Lemma_Valid_Of_Parts (S, F);
               pragma Assert (Valid (S, F));
            end;
         else
            Ceil_Frame (S, F, Frame, H, Off, St);
            if St /= Ceil_Only then
               --  OK: the ceiling is not above maxceil. A store does not
               --  write such a CEIL. (Log_Full does not happen: the entry
               --  is inside Input, and Input fits the log.)
               Result := Malformed;
               return;
            end if;
            --  The capture appended the entry at P (Ceil_Appended).
            pragma Assert (Ceil_Appended (S1, S, Frame, P));
            pragma Assert (S.LL - P = Apply_Prefix + L);
            pragma Assert (Log_Length (S1) = P);
            pragma Assert (Log_Extends (S1, S));
            pragma Assert (for all J in 0 .. P - 1 => Log_Byte (S, J) = Log_Byte (S1, J));
            pragma Assert (for all J in 0 .. P - 1 => S.Log (J) = S1.Log (J));
            pragma Assert (for all J in 0 .. P - 1 => S.Log (J) = Input (J));
            pragma Assert (for all J in Frame'Range => Log_Byte (S, J) = Frame (J));
            pragma Assert (for all J in Frame'Range => S.Log (J) = Frame (J));
            pragma Assert (Op_At (S, P) = Op_Ceil and then Len_At (S, P) = L);
            pragma Assert (S.Log (P) = Op_Ceil);
            pragma Assert (U24_Of (S.Log (P + 1), S.Log (P + 2), S.Log (P + 3)) = L);
            pragma Assert (Valid (S, F));
         end if;
         Lemma_U24_Bytes_Round_Trip (Input (P + 1), Input (P + 2), Input (P + 3));
         Lemma_U24_Bytes_Round_Trip (S.Log (P + 1), S.Log (P + 2), S.Log (P + 3));
         pragma Assert (S.LL = P + Apply_Prefix + L);
         pragma Assert (S.Log (P) = Input (P));
         pragma Assert (S.Log (P + 1) = Byte_Of_U24 (L, 0)
                        and then S.Log (P + 2) = Byte_Of_U24 (L, 1)
                        and then S.Log (P + 3) = Byte_Of_U24 (L, 2));
         pragma Assert (S.Log (P + 1) = Input (P + 1)
                        and then S.Log (P + 2) = Input (P + 2)
                        and then S.Log (P + 3) = Input (P + 3));
         pragma Assert (for all J in Frame'Range => S.Log (J) = Frame (J));
         pragma Assert (for all J in Frame'Range => Frame (J) = Input (J));
         pragma Assert (for all J in P + Apply_Prefix .. S.LL - 1 => S.Log (J) = Input (J));
         pragma Assert (for all J in 0 .. P - 1 => S.Log (J) = Input (J));
         pragma Assert (for all J in P .. P + 3 => S.Log (J) = Input (J));
         pragma Assert (for all J in 0 .. P + 3 => S.Log (J) = Input (J));
         pragma Assert (for all J in 0 .. S.LL - 1 => S.Log (J) = Input (J));
         Result := OK;
      end;
   end Replay_Ceil;

   --  One entry of replay at S.LL (S15): an APPLY reruns Put_Frame in
   --  trusted mode (one parse, one hash, no signature check), and stays in
   --  the log when it changes nothing (H23); a SEQ raises seq_self; a CEIL
   --  is Replay_Ceil. On OK the log is one entry longer and is still the
   --  input's prefix; on a refusal nothing changes.
   procedure Replay_Entry
     (Input  : Byte_Array;
      S      : in out Store;
      F      : in out Frontier.State;
      Result : out Status)
   with
     Global => null,
     Pre  => Input'First = 0 and then Input'Last < S.Log_Cap
       and then Valid (S, F)
       and then S.LL >= Header_Len and then S.LL <= Input'Last
       and then (for all J in 0 .. S.LL - 1 => S.Log (J) = Input (J)),
     Post => Valid (S, F)
       and then Same_Identity (S'Old, S)
       and then S.Pins = S'Old.Pins
       and then Result in OK | Malformed | No_Space
       and then (if Result = OK then S.LL > S'Old.LL else S.LL = S'Old.LL)
       and then S.LL - 1 <= Input'Last
       and then (for all J in 0 .. S.LL - 1 => S.Log (J) = Input (J))
   is
      P : constant Log_Size := S.LL;
   begin
      Lemma_Valid_Parts (S, F);
      if Input (P) = Op_Apply and then Input'Last - P >= Apply_Prefix then
         declare
            L : constant U24_Value := U24_Of (Input (P + 1), Input (P + 2), Input (P + 3));
         begin
            if L not in Frame_Size or else L > Input'Last - P - Apply_Prefix + 1 then
               Result := Malformed;
               return;
            end if;
            if not Is_Record_Frame (Input (P + Apply_Prefix .. P + Apply_Prefix + L - 1)) then
               Result := Malformed;
               return;
            end if;
            declare
               Frame : constant Byte_Array := Input (P + Apply_Prefix .. P + Apply_Prefix + L - 1);
               H     : constant Header := Header_Of (S.Cid, Frame);
               S1    : constant Store := S with Ghost;
               Off   : Log_Size;
               St    : Status;
            begin
               pragma Assert (for all J in 0 .. P - 1 => S1.Log (J) = Input (J));
               if not Canonical (H) then
                  Result := Malformed;
                  return;
               end if;
               --  AUDIT.md H12: Put_Frame captures this frame, so a store
               --  wrote a CEIL for it and never this APPLY.
               if Ceil_Rule (F, H) then
                  Result := Malformed;
                  return;
               end if;
               Apply_Frame (S, F, Frame, H, Off, St);
               pragma Assert (St /= Ceil_Only);
               if St = No_Space then
                  Result := No_Space;
                  return;
               elsif St /= OK then
                  Result := Malformed;
                  return;
               end if;
               if S.LL = P then
                  --  A duplicate, or an expired DEL that dropped nothing:
                  --  the entry stays in the log (H23).
                  declare
                     Log1 : constant Byte_Array := S.Log with Ghost;
                  begin
                     Lemma_Valid_Parts (S, F);
                     pragma Assert (Tags_OK (S.Log, S.LL, S.Cid, F));
                     pragma Assert (Ceil_OK (S.Log, S.LL, S.Cid, F));
                     pragma Assert (Head_OK (S.Log, S.LL, S.Root, S.Slt, S.TTL));
                     pragma Assert (S.NE <= S.LL);
                     pragma Assert (for all J in 0 .. P - 1 => S.Log (J) = Input (J));
                     Append_Apply (S.Log, S.LL, Frame, P, Op_Apply);
                     S.NE := S.NE + 1;
                     Lemma_Tags_Kept (Log1, P, S.Log, S.LL, S.Cid, F);
                     Lemma_Ceil_Kept (Log1, P, S.Log, S.LL, S.Cid, F, F);
                     Lemma_Head_Kept (Log1, P, S.Log, S.LL, S.Root, S.Slt, S.TTL);
                     pragma Assert (S.NE <= S.LL);
                     pragma Assert (for all J in 0 .. P - 1 => S.Log (J) = Input (J));
                     pragma Assert (for all J in Frame'Range => S.Log (J) = Frame (J));
                     Lemma_Valid_Of_Parts (S, F);
                     pragma Assert (Valid (S, F));
                  end;
               else
                  --  Put_Frame appended the entry at P (Appended).
                  pragma Assert (S.LL - P = Apply_Prefix + L);
                  pragma Assert (Log_Length (S1) = P);
                  pragma Assert (Log_Extends (S1, S));
                  pragma Assert (for all J in 0 .. P - 1 => Log_Byte (S, J) = Log_Byte (S1, J));
                  pragma Assert (for all J in 0 .. P - 1 => S.Log (J) = S1.Log (J));
                  pragma Assert (for all J in 0 .. P - 1 => S.Log (J) = Input (J));
                  pragma Assert (for all J in Frame'Range => Log_Byte (S, J) = Frame (J));
                  pragma Assert (for all J in Frame'Range => S.Log (J) = Frame (J));
                  pragma Assert (Op_At (S, P) = Op_Apply and then Len_At (S, P) = L);
                  pragma Assert (S.Log (P) = Op_Apply);
                  pragma Assert (U24_Of (S.Log (P + 1), S.Log (P + 2), S.Log (P + 3)) = L);
                  pragma Assert (Valid (S, F));
               end if;
               Lemma_U24_Bytes_Round_Trip (Input (P + 1), Input (P + 2), Input (P + 3));
               Lemma_U24_Bytes_Round_Trip (S.Log (P + 1), S.Log (P + 2), S.Log (P + 3));
               pragma Assert (S.LL = P + Apply_Prefix + L);
               pragma Assert (S.Log (P) = Input (P));
               pragma Assert (S.Log (P + 1) = Byte_Of_U24 (L, 0)
                              and then S.Log (P + 2) = Byte_Of_U24 (L, 1)
                              and then S.Log (P + 3) = Byte_Of_U24 (L, 2));
               pragma Assert (S.Log (P + 1) = Input (P + 1)
                              and then S.Log (P + 2) = Input (P + 2)
                              and then S.Log (P + 3) = Input (P + 3));
               pragma Assert (for all J in Frame'Range => S.Log (J) = Frame (J));
               pragma Assert (for all J in Frame'Range => Frame (J) = Input (J));
               pragma Assert (for all J in P + Apply_Prefix .. S.LL - 1 => S.Log (J) = Input (J));
               pragma Assert (for all J in 0 .. P - 1 => S.Log (J) = Input (J));
               pragma Assert (for all J in P .. P + 3 => S.Log (J) = Input (J));
               pragma Assert (for all J in 0 .. P + 3 => S.Log (J) = Input (J));
               pragma Assert (for all J in 0 .. S.LL - 1 => S.Log (J) = Input (J));
               Result := OK;
            end;
         end;
      elsif Input (P) = Op_Ceil and then Input'Last - P >= Apply_Prefix then
         Replay_Ceil (Input, S, F, Result);
      elsif Input (P) = Op_Seq and then Input'Last - P >= Seq_Len - 1 then
         declare
            V    : constant U48 :=
              KR.U48_Of (Input (P + 1), Input (P + 2), Input (P + 3),
                         Input (P + 4), Input (P + 5), Input (P + 6));
            Log1 : constant Byte_Array := S.Log with Ghost;
         begin
            pragma Assert (S.NE <= S.LL);
            pragma Assert (for all J in 0 .. P - 1 => S.Log (J) = Input (J));
            Append_Seq (S.Log, S.LL, V);
            S.NE := S.NE + 1;
            pragma Assert (Seq_OK (F, S.Self, S.SS));
            if V > S.SS then
               S.SS := V;
            end if;
            pragma Assert (Seq_OK (F, S.Self, S.SS));
            Lemma_Tags_Kept (Log1, P, S.Log, S.LL, S.Cid, F);
            Lemma_Ceil_Kept (Log1, P, S.Log, S.LL, S.Cid, F, F);
            Lemma_Head_Kept (Log1, P, S.Log, S.LL, S.Root, S.Slt, S.TTL);
            KR.Lemma_U48_Bytes_Round_Trip
              (Input (P + 1), Input (P + 2), Input (P + 3),
               Input (P + 4), Input (P + 5), Input (P + 6));
            pragma Assert (for all J in 0 .. P - 1 => S.Log (J) = Input (J));
            pragma Assert (S.Log (P) = Input (P));
            pragma Assert (for all K in 0 .. 5 => S.Log (P + 1 + K) = KR.Byte_Of_U48 (V, K));
            pragma Assert (for all K in 0 .. 5 => S.Log (P + 1 + K) = Input (P + 1 + K));
            pragma Assert (for all J in 0 .. S.LL - 1 => S.Log (J) = Input (J));
            Lemma_Valid_Of_Parts (S, F);
            pragma Assert (Valid (S, F));
            Result := OK;
         end;
      else
         Result := Malformed;
      end if;
   end Replay_Entry;

   --  The T18-prefix clause from the components (Open_From_Log).
   procedure Lemma_Replayed
     (Input : Byte_Array; Self_PK : Pubkey; F : Frontier.State; S : Store; VL : Log_Size)
   with
     Ghost, Global => null,
     Pre  => Input'First = 0
       and then Valid (S, F)
       and then VL >= Header_Len
       and then Input'Last < S.Log_Cap
       and then Header_Well_Formed (Input)
       and then S.LL = VL
       and then VL - 1 <= Input'Last
       and then (for all J in 0 .. VL - 1 => S.Log (J) = Input (J))
       and then (for all J in 0 .. Pubkey_Len - 1 => S.Root (J) = Input (HO_Root + J))
       and then (for all J in 0 .. Salt_Len - 1 => S.Slt (J) = Input (HO_Salt + J))
       and then S.TTL = Header_TTL (Input)
       and then S.Self = Kome.Keys.To_Key256 (Self_PK)
       and then S.Pins = 0,
     Post => Replayed_Prefix (Input, Self_PK, F, S, VL)
   is
   begin
      pragma Assert (Log_Length (S) = VL);
      pragma Assert (for all J in 0 .. VL - 1 => Log_Byte (S, J) = Input (J));
      pragma Assert (for all J in 0 .. Pubkey_Len - 1 => Root_Key (S) (J) = Input (HO_Root + J));
      pragma Assert (for all J in 0 .. Salt_Len - 1 => Salt_Of (S) (J) = Input (HO_Salt + J));
   end Lemma_Replayed;

   procedure Open_From_Log
     (Input        : in     Byte_Array;
      Self_PK      : in     Pubkey;
      F            :    out Frontier.State;
      S            :    out Store;
      Valid_Length :    out Log_Size;
      Result       :    out Status)
   is
      St : Status;
   begin
      Valid_Length := 0;
      F := Frontier.Empty ((others => 0), F.Cap);
      S.Root := [others => 0];
      S.Slt  := [others => 0];
      S.TTL  := Del_TTL_Min;
      S.Cid  := [others => 0];
      S.Fnd  := (others => 0);
      S.Self := Kome.Keys.To_Key256 (Self_PK);
      S.SS   := 0;
      S.DA   := KD.Empty;
      S.DD   := KD.Empty;
      S.Pins := 0;
      S.LL   := 0;
      S.NE   := 0;
      S.Log  := [others => 0];
      if Input'Last >= S.Log_Cap then
         Result := No_Space;
         return;
      end if;
      if not Header_Well_Formed (Input) then
         Result := Malformed;
         return;
      end if;

      --  The HEADER.
      S.Root := Input (HO_Root .. HO_Root + Pubkey_Len - 1);
      S.Slt  := Input (HO_Salt .. HO_Salt + Salt_Len - 1);
      S.TTL  := Header_TTL (Input);
      S.Cid  := KR.Cid_Of (S.Root, S.Slt, S.TTL);
      S.Fnd  := Kome.Keys.To_Key256 (S.Root);
      F := Frontier.Empty (S.Fnd, F.Cap);
      for J in 0 .. Header_Len - 1 loop
         S.Log (J) := Input (J);
         pragma Loop_Invariant (for all J2 in 0 .. J => S.Log (J2) = Input (J2));
      end loop;
      S.LL := Header_Len;
      pragma Assert (for all J in 0 .. Magic_Len - 1 => Input (J) = Magic (J));
      pragma Assert (for all J in 0 .. Magic_Len - 1 => S.Log (J) = Magic (J));
      pragma Assert (S.Log (HO_Version) = Log_Version);
      pragma Assert (for all J in 0 .. Pubkey_Len - 1 => S.Root (J) = Input (HO_Root + J));
      pragma Assert (for all J in 0 .. Pubkey_Len - 1 => S.Log (HO_Root + J) = S.Root (J));
      pragma Assert (for all J in 0 .. Salt_Len - 1 => S.Slt (J) = Input (HO_Salt + J));
      pragma Assert (for all J in 0 .. Salt_Len - 1 => S.Log (HO_Salt + J) = S.Slt (J));
      pragma Assert (KR.U48_Of (S.Log (HO_TTL), S.Log (HO_TTL + 1), S.Log (HO_TTL + 2),
                                S.Log (HO_TTL + 3), S.Log (HO_TTL + 4), S.Log (HO_TTL + 5))
                     = S.TTL);
      pragma Assert (Head_OK (S.Log, S.LL, S.Root, S.Slt, S.TTL));
      Lemma_Valid_Empty (S, F);
      Valid_Length := Header_Len;

      --  The entries.
      while S.LL <= Input'Last loop
         pragma Loop_Invariant (Valid (S, F));
         pragma Loop_Invariant (S.LL = Valid_Length and then S.LL >= Header_Len);
         pragma Loop_Invariant (S.LL - 1 <= Input'Last);
         pragma Loop_Invariant (for all J in 0 .. S.LL - 1 => S.Log (J) = Input (J));
         pragma Loop_Invariant
           (for all J in 0 .. Pubkey_Len - 1 => S.Root (J) = Input (HO_Root + J));
         pragma Loop_Invariant
           (for all J in 0 .. Salt_Len - 1 => S.Slt (J) = Input (HO_Salt + J));
         pragma Loop_Invariant (S.TTL = Header_TTL (Input));
         pragma Loop_Invariant (S.Self = Kome.Keys.To_Key256 (Self_PK));
         pragma Loop_Invariant (S.Pins = 0);
         pragma Loop_Variant (Increases => S.LL);
         Replay_Entry (Input, S, F, St);
         if St /= OK then
            Result := St;
            Lemma_Replayed (Input, Self_PK, F, S, Valid_Length);
            return;
         end if;
         Valid_Length := S.LL;
      end loop;
      Lemma_Replayed (Input, Self_PK, F, S, Valid_Length);
      Result := OK;
   end Open_From_Log;

   ---------------------------------------------------------------------------
   --  The invariant, unpacked.
   ---------------------------------------------------------------------------

   procedure Lemma_Valid_Facts (S : Store; F : Frontier.State) is null;

   procedure Lemma_Log_Header (S : Store; F : Frontier.State) is null;

   procedure Lemma_Tag (S : Store; F : Frontier.State; I : Held_Index) is
   begin
      Lemma_Valid_Parts (S, F);
      pragma Assert (Tag_OK (S.Log, S.LL, S.Cid, Held (F, I), Tag (F, I), Op_Apply));
      Lemma_Tag_OK_Bounds (S.Log, S.LL, S.Cid, Held (F, I), Tag (F, I), Op_Apply);
      pragma Assert (Log_Length (S) = S.LL);
      pragma Assert (Tag_Off (Tag (F, I)) + Apply_Prefix + Tag_Len (Tag (F, I)) <= S.LL);
      pragma Assert (Tag_Off (Tag (F, I)) < Log_Length (S));
      pragma Assert (Log_Length (S) - Tag_Off (Tag (F, I)) >= Apply_Prefix);
      pragma Assert (Op_At (S, Tag_Off (Tag (F, I))) = Op_Apply);
      pragma Assert (Tag_Len (Tag (F, I)) >= 1 and then Tag_Len (Tag (F, I)) <= KR.Frame_Max);
      pragma Assert (Len_At (S, Tag_Off (Tag (F, I))) = Tag_Len (Tag (F, I)));
      pragma Assert (Len_At (S, Tag_Off (Tag (F, I))) >= 1
                     and then Len_At (S, Tag_Off (Tag (F, I))) <= KR.Frame_Max);
      pragma Assert (Len_At (S, Tag_Off (Tag (F, I))) in Frame_Size);
      pragma Assert (Len_At (S, Tag_Off (Tag (F, I)))
                     <= Log_Length (S) - Tag_Off (Tag (F, I)) - Apply_Prefix);
      pragma Assert (Has_Frame (S, Tag_Off (Tag (F, I))));
      pragma Assert (for all J in Slice_At (S.Log, Tag (F, I))'Range =>
                       Read_Frame (S, Tag_Off (Tag (F, I))) (J - Slice_At (S.Log, Tag (F, I))'First)
                       = Slice_At (S.Log, Tag (F, I)) (J));
      Lemma_Frame_Is_Congruent
        (S.Cid, Held (F, I), Slice_At (S.Log, Tag (F, I)), Read_Frame (S, Tag_Off (Tag (F, I))));
      Lemma_Frame_Is_Def (Read_Frame (S, Tag_Off (Tag (F, I))), S.Cid, Held (F, I));
   end Lemma_Tag;

   procedure Lemma_Ceil_Tag (S : Store; F : Frontier.State) is
      X : constant Header := Ceil_Held (F);
      T : constant U64 := Ceil_Tag (F);
   begin
      Lemma_Valid_Parts (S, F);
      pragma Assert (Tag_OK (S.Log, S.LL, S.Cid, X, T, Op_Ceil));
      Lemma_Tag_OK_Bounds (S.Log, S.LL, S.Cid, X, T, Op_Ceil);
      pragma Assert (Log_Length (S) = S.LL);
      pragma Assert (Tag_Off (T) + Apply_Prefix + Tag_Len (T) <= S.LL);
      pragma Assert (Tag_Off (T) < Log_Length (S));
      pragma Assert (Log_Length (S) - Tag_Off (T) >= Apply_Prefix);
      pragma Assert (Op_At (S, Tag_Off (T)) = Op_Ceil);
      pragma Assert (Tag_Len (T) >= 1 and then Tag_Len (T) <= KR.Frame_Max);
      pragma Assert (Len_At (S, Tag_Off (T)) = Tag_Len (T));
      pragma Assert (Len_At (S, Tag_Off (T)) in Frame_Size);
      pragma Assert (Len_At (S, Tag_Off (T)) <= Log_Length (S) - Tag_Off (T) - Apply_Prefix);
      pragma Assert (Has_Frame (S, Tag_Off (T)));
      pragma Assert (for all J in Slice_At (S.Log, T)'Range =>
                       Read_Frame (S, Tag_Off (T)) (J - Slice_At (S.Log, T)'First)
                       = Slice_At (S.Log, T) (J));
      Lemma_Frame_Is_Congruent (S.Cid, X, Slice_At (S.Log, T), Read_Frame (S, Tag_Off (T)));
      Lemma_Frame_Is_Def (Read_Frame (S, Tag_Off (T)), S.Cid, X);
      --  The cell's record is a roster, so its frame is a ROSTER frame.
      Lemma_Frontier_Ceil (F);
      Lemma_Header_Of (S.Cid, Read_Frame (S, Tag_Off (T)));
      pragma Assert (KR.Kind_Of (Read_Frame (S, Tag_Off (T))) = K_Roster);
   end Lemma_Ceil_Tag;

   procedure Lemma_No_Expired (S : Store; F : Frontier.State; I : Held_Index) is null;

   procedure Lemma_Seq_Self (S : Store; F : Frontier.State; I : Held_Index) is null;

   procedure Lemma_Digests (S : Store; F : Frontier.State) is null;

   procedure Lemma_Digest_Split (S : Store; F : Frontier.State) is
      --  Proved; at run time the invariant would sum the list again.
      pragma Assertion_Policy (Loop_Invariant => Ignore);
      DC : constant Natural := Data_Count (F);
      N  : constant Natural := Count (F);
      L  : KD.Hash_Array (1 .. N) := [others => (others => 0)] with Ghost;
   begin
      for I in 1 .. N loop
         L (I) := Held (F, I).V.H;
         pragma Loop_Invariant (for all J in 1 .. I => L (J) = Held (F, J).V.H);
      end loop;
      KD.Lemma_State_Of_Models (F, L);
      for I in 1 .. DC loop
         Lemma_Held_Data (F, I);
         pragma Loop_Invariant (for all J in 1 .. I => L (J) = Data_Held (F, J).V.H);
      end loop;
      KD.Lemma_Sum_Split (L, 1, DC, N);
      KD.Lemma_Sum_Ext (L, Data_Hashes (F), 1, DC);
      Lemma_Sum_Shift (Auth_Hashes (F), L, 1, Auth_Count (F), DC);
      Lemma_Add_Congruent
        (KD.Sum_Of (L, 1, DC), KD.Sum (S.DD), KD.Sum_Of (L, DC + 1, N), KD.Sum (S.DA));
      Lemma_Eq_Iff_Value (KD.Sum_Of (L, 1, N),
                          Add (KD.Sum_Of (L, 1, DC), KD.Sum_Of (L, DC + 1, N)));
      Lemma_Eq_Iff_Value (Add (KD.Sum_Of (L, 1, DC), KD.Sum_Of (L, DC + 1, N)),
                          Add (KD.Sum (S.DD), KD.Sum (S.DA)));
      Lemma_Eq_Iff_Value (KD.Sum (KD.State_Of (F)), KD.Sum_Of (L, 1, N));
      Lemma_Eq_Iff_Value (Add (KD.Sum (S.DD), KD.Sum (S.DA)), KD.Sum (KD.State_Of (F)));
   end Lemma_Digest_Split;

end Kome.Store;
