--  Kome.Crypto body: the C binding. SPARK_Mode Off is the one exception
--  that CONVENTIONS.md allows. Each subprogram here is a direct call into
--  monocypher 4.0.2 (third_party/monocypher/monocypher.h and, for Ed25519,
--  monocypher-ed25519.h). The lengths are converted to size_t, and the
--  buffers are passed by address. The only Ada logic is the encoding check
--  of Verify. It calls the (SPARK, proved) expression functions of the
--  spec. Callers prove against the contracts of the spec. The test main
--  executes these contracts on the output of monocypher under -gnata.
--
--  The body passes empty buffers as NULL with size 0. The manual of
--  monocypher documents this as valid for each pointer/size pair here.
pragma Ada_2022;
with System;
with Interfaces.C;

package body Kome.Crypto with SPARK_Mode => Off is

   use type Interfaces.C.int;
   subtype size_t is Interfaces.C.size_t;
   subtype int is Interfaces.C.int;

   ---------------------------------------------------------------------------
   --  monocypher.h prototypes
   ---------------------------------------------------------------------------

   procedure C_Blake2b
     (Hash : System.Address; Hash_Size : size_t;
      Msg  : System.Address; Msg_Size  : size_t)
     with Import, Convention => C, External_Name => "crypto_blake2b";

   procedure C_Blake2b_Init (Ctx : System.Address; Hash_Size : size_t)
     with Import, Convention => C, External_Name => "crypto_blake2b_init";

   procedure C_Blake2b_Update
     (Ctx : System.Address; Msg : System.Address; Msg_Size : size_t)
     with Import, Convention => C, External_Name => "crypto_blake2b_update";

   procedure C_Blake2b_Final (Ctx : System.Address; Hash : System.Address)
     with Import, Convention => C, External_Name => "crypto_blake2b_final";

   --  monocypher-ed25519.h (RFC 8032 Ed25519, SHA-512 internal). This body
   --  intentionally does not import the core crypto_eddsa_* (BLAKE2b-512
   --  EdDSA).
   procedure C_Ed25519_Key_Pair
     (SK : System.Address; PK : System.Address; Seed : System.Address)
     with Import, Convention => C, External_Name => "crypto_ed25519_key_pair";

   procedure C_Ed25519_Sign
     (Signature : System.Address; SK : System.Address;
      Msg       : System.Address; Msg_Size : size_t)
     with Import, Convention => C, External_Name => "crypto_ed25519_sign";

   function C_Ed25519_Check
     (Signature : System.Address; PK : System.Address;
      Msg       : System.Address; Msg_Size : size_t) return int
     with Import, Convention => C, External_Name => "crypto_ed25519_check";

   procedure C_X25519_Public_Key (PK : System.Address; SK : System.Address)
     with Import, Convention => C, External_Name => "crypto_x25519_public_key";

   procedure C_X25519
     (Shared : System.Address; SK : System.Address; PK : System.Address)
     with Import, Convention => C, External_Name => "crypto_x25519";

   procedure C_Aead_Lock
     (Cipher : System.Address; Mac : System.Address;
      Key    : System.Address; N   : System.Address;
      AD     : System.Address; AD_Size : size_t;
      Plain  : System.Address; Text_Size : size_t)
     with Import, Convention => C, External_Name => "crypto_aead_lock";

   function C_Aead_Unlock
     (Plain  : System.Address; Mac : System.Address;
      Key    : System.Address; N   : System.Address;
      AD     : System.Address; AD_Size : size_t;
      Cipher : System.Address; Text_Size : size_t) return int
     with Import, Convention => C, External_Name => "crypto_aead_unlock";

   procedure C_Wipe (Secret : System.Address; Size : size_t)
     with Import, Convention => C, External_Name => "crypto_wipe";

   ---------------------------------------------------------------------------
   --  Layout check: Ctx_Storage must hold crypto_blake2b_ctx.
   ---------------------------------------------------------------------------

   type U64_8  is array (0 .. 7) of U64 with Convention => C;
   type U64_2  is array (0 .. 1) of U64 with Convention => C;
   type U64_16 is array (0 .. 15) of U64 with Convention => C;
   type C_Blake2b_Ctx is record          --  monocypher.h crypto_blake2b_ctx
      Hash         : U64_8;
      Input_Offset : U64_2;
      Input        : U64_16;
      Input_Idx    : size_t;
      Hash_Size    : size_t;
   end record
     with Convention => C;

   pragma Compile_Time_Error
     (C_Blake2b_Ctx'Size > Ctx_Storage'Size,
      "Ctx_Storage is smaller than crypto_blake2b_ctx");
   --  Alignment: each member of crypto_blake2b_ctx is a uint64_t or a
   --  size_t. Thus its alignment is at most the alignment of uint64_t, and
   --  Ctx_Storage (an array of U64, Size 64) has that alignment. GNAT cannot
   --  fold 'Alignment of a C record at compile time. Thus this comment
   --  states this half, and no code checks it.

   ---------------------------------------------------------------------------
   --  Helpers
   ---------------------------------------------------------------------------

   --  Address of the first byte of a buffer, or NULL when the buffer is
   --  empty. For an `out` buffer, the caller writes the same expression on
   --  the formal itself ('Address of the formal). Thus the compiler sees the
   --  buffer as written.
   function Addr (B : Byte_Array) return System.Address is
     (if B'Length = 0 then System.Null_Address else B'Address);

   function Len (B : Byte_Array) return size_t is (size_t (B'Length));

   Ctx_Bytes : constant size_t := size_t (Ctx_Storage'Size / 8);

   ---------------------------------------------------------------------------
   --  BLAKE2b-256
   ---------------------------------------------------------------------------

   function Blake2b_256 (Data : Byte_Array) return Hash256 is
      Result : Hash256 := [others => 0];
   begin
      C_Blake2b (Result'Address, Hash_Len, Addr (Data), Len (Data));
      return Result;
   end Blake2b_256;

   procedure Blake2b_256 (Data : Byte_Array; Digest : out Hash256) is
   begin
      C_Blake2b (Digest'Address, Hash_Len, Addr (Data), Len (Data));
   end Blake2b_256;

   --  An axiom (refer to the spec): there is nothing to execute. Under
   --  -gnata, the Pre and the Post are evaluated. This checks the axiom on
   --  the data of the caller.
   procedure Lemma_Blake2b_Congruent (A, B : Byte_Array) is null;

   procedure Init (Ctx : out Blake2b_Context) is
   begin
      Ctx.Raw    := [others => 0];
      Ctx.Active := True;
      Ctx.Count  := 0;
      C_Blake2b_Init (Ctx.Raw'Address, Hash_Len);
   end Init;

   procedure Update (Ctx : in out Blake2b_Context; Data : Byte_Array) is
   begin
      C_Blake2b_Update (Ctx.Raw'Address, Addr (Data), Len (Data));
      Ctx.Count := Ctx.Count + Stream_Len (Data'Length);
   end Update;

   procedure Final (Ctx : in out Blake2b_Context; Digest : out Hash256) is
   begin
      C_Blake2b_Final (Ctx.Raw'Address, Digest'Address);
      Wipe (Ctx);   --  monocypher wipes its struct; this wipes all of Raw
   end Final;

   procedure Wipe (Ctx : in out Blake2b_Context) is
   begin
      C_Wipe (Ctx.Raw'Address, Ctx_Bytes);
      Ctx.Active := False;
      Ctx.Count  := 0;
   end Wipe;

   ---------------------------------------------------------------------------
   --  Ed25519
   ---------------------------------------------------------------------------

   function Derive_Public (S : Seed) return Pubkey is
      Copy   : Seed := S;   --  crypto_ed25519_key_pair wipes its seed argument
      Full   : Byte_Array (0 .. Secret_Key_Len - 1) := [others => 0];
      Result : Pubkey := [others => 0];
   begin
      C_Ed25519_Key_Pair (Full'Address, Result'Address, Copy'Address);
      C_Wipe (Full'Address, Secret_Key_Len);
      C_Wipe (Copy'Address, Seed_Len);
      return Result;
   end Derive_Public;

   procedure Key_Pair (S : Seed; SK : out Secret_Key; PK : out Pubkey) is
      Copy : Seed := S;   --  crypto_ed25519_key_pair wipes its seed argument
   begin
      C_Ed25519_Key_Pair (SK.Raw'Address, PK'Address, Copy'Address);
      C_Wipe (Copy'Address, Seed_Len);
      SK.Valid := True;
   end Key_Pair;

   procedure Wipe (SK : in out Secret_Key) is
   begin
      C_Wipe (SK.Raw'Address, Secret_Key_Len);
      SK.Valid := False;
   end Wipe;

   function Sign (SK : Secret_Key; Msg : Byte_Array) return Sig is
      Result : Sig := [others => 0];
   begin
      C_Ed25519_Sign (Result'Address, SK.Raw'Address, Addr (Msg), Len (Msg));
      return Result;
   end Sign;

   --  Strict verification (spec header): first the encoding checks, then
   --  monocypher. S_Below_L repeats the check that crypto_ed25519_check
   --  enforces. Thus the first conjunct of the Post does not depend on C
   --  alone.
   function Verify (Signature : Sig; PK : Pubkey; Msg : Byte_Array) return Boolean is
     (S_Below_L (Signature)
      and then Is_Canonical_Point (Signature (0 .. 31))
      and then Is_Canonical_Point (PK)
      and then C_Ed25519_Check
                 (Signature'Address, PK'Address, Addr (Msg), Len (Msg)) = 0);

   ---------------------------------------------------------------------------
   --  X25519
   ---------------------------------------------------------------------------

   function X25519_Public (Secret : DH_Secret) return Pubkey is
      Result : Pubkey := [others => 0];
   begin
      C_X25519_Public_Key (Result'Address, Secret'Address);
      return Result;
   end X25519_Public;

   function X25519_Shared (Secret : DH_Secret; Their_Public : Pubkey) return Shared_Secret is
      Result : Shared_Secret := [others => 0];
   begin
      C_X25519 (Result'Address, Secret'Address, Their_Public'Address);
      return Result;
   end X25519_Shared;

   procedure X25519
     (Secret       : DH_Secret;
      Their_Public : Pubkey;
      Shared       : out Shared_Secret;
      Contributory : out Boolean) is
   begin
      C_X25519 (Shared'Address, Secret'Address, Their_Public'Address);
      Contributory := not Is_Zero (Shared);
   end X25519;

   ---------------------------------------------------------------------------
   --  AEAD
   ---------------------------------------------------------------------------

   procedure Lock
     (Key    : AEAD_Key;
      N      : Nonce;
      AD     : Byte_Array;
      Plain  : Byte_Array;
      Cipher : out Byte_Array;
      Mac    : out Tag) is
   begin
      C_Aead_Lock ((if Cipher'Length = 0 then System.Null_Address
                    else Cipher'Address),
                   Mac'Address, Key'Address, N'Address,
                   Addr (AD), Len (AD), Addr (Plain), Len (Plain));
   end Lock;

   procedure Unlock
     (Key       : AEAD_Key;
      N         : Nonce;
      AD        : Byte_Array;
      Cipher    : Byte_Array;
      Mac       : Tag;
      Plain     : out Byte_Array;
      Authentic : out Boolean) is
   begin
      Authentic :=
        C_Aead_Unlock ((if Plain'Length = 0 then System.Null_Address
                        else Plain'Address),
                       Mac'Address, Key'Address, N'Address,
                       Addr (AD), Len (AD), Addr (Cipher), Len (Cipher)) = 0;
      if not Authentic then
         Wipe (Plain);
      end if;
   end Unlock;

   procedure Wipe (B : out Byte_Array) is
   begin
      if B'Length > 0 then
         C_Wipe (B'Address, Len (B));
      end if;
   end Wipe;

end Kome.Crypto;
