--  Root of the Kome SPARK mirror: the byte types and the size constants every
--  module shares. Each module lives in a child package (Kome.HLC, Kome.Codec,
--  ...). See CONVENTIONS.md for the rules every child package follows.
pragma Ada_2022;
package Kome with SPARK_Mode, Pure is

   type Byte is mod 2**8 with Size => 8;
   type Byte_Array is array (Natural range <>) of Byte;

   type U16 is mod 2**16 with Size => 16;
   type U32 is mod 2**32 with Size => 32;
   type U64 is mod 2**64 with Size => 64;

   --  Fixed-size cryptographic values (include/sync_engine.h: SYNC_*_LEN).
   Site_Id_Len : constant := 32;
   Pubkey_Len  : constant := 32;
   Sig_Len     : constant := 64;
   Seed_Len    : constant := 32;
   Digest_Len  : constant := 32;
   Hash_Len    : constant := 32;   --  SHA-256 / BLAKE2b-256 outputs
   Blob_Id_Len : constant := 32;

   subtype Site_Id is Byte_Array (0 .. Site_Id_Len - 1);
   subtype Pubkey  is Byte_Array (0 .. Pubkey_Len - 1);
   subtype Sig     is Byte_Array (0 .. Sig_Len - 1);
   subtype Seed    is Byte_Array (0 .. Seed_Len - 1);
   subtype Digest  is Byte_Array (0 .. Digest_Len - 1);
   subtype Hash256 is Byte_Array (0 .. Hash_Len - 1);
   subtype Blob_Id is Byte_Array (0 .. Blob_Id_Len - 1);

   --  Bounds. SPARK forbids unbounded growth, so every variable-length value
   --  carries an explicit maximum. These mirror the C++ engine's enforced
   --  limits where one exists and otherwise pick a bound the C++ never
   --  exceeds in practice; a module that needs a tighter or looser bound
   --  declares its own constant in its spec and says why.
   Max_Name_Len     : constant := 1024;         --  namespace / entity / field
   Max_Value_Len    : constant := 65_536;       --  one register value
   Blob_Chunk_Max   : constant := 32_768;       --  SYNC_BLOB_CHUNK_MAX
   Max_Message_Len  : constant := 48 * 1024;    --  reconcile.h kMaxMessageBytes
   Max_Recv_Message : constant := 8 * 1024 * 1024;  --  reconcile.h kMaxRecvMessageBytes
   Max_Batch_Depth  : constant := 1024;         --  storage.h kMaxBatchDepth

   --  Error codes, mirroring sync_error in include/sync_engine.h. The mirror
   --  returns these from the same operations the C ABI does.
   type Error is
     (OK, Err_Invalid, Err_Nomem, Err_Notfound, Err_Internal, Err_Badsig,
      Err_Unauthorized, Err_Corrupt);
   for Error use
     (OK => 0, Err_Invalid => 1, Err_Nomem => 2, Err_Notfound => 3,
      Err_Internal => 4, Err_Badsig => 5, Err_Unauthorized => 6,
      Err_Corrupt => 7);

end Kome;
