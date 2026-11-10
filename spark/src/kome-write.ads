--  Kome.Write: the write path of one replica (DESIGN.md §5 "The write path
--  has three steps", §7; SIMPLIFY.md S16, S17; AUDIT.md H18). It joins the
--  steps that the other packages prove one by one, in one call:
--
--    Write = Choose (Kome.Emit)  ->  Make (Kome.Records Make_Put /
--            Make_Del with the chosen t and seq)  ->  Sign  ->
--            Store.Put_Frame (Kome.Store)
--
--  seq_self lives in the store's log (S16): Kome.Store.Seq_Self (S) is the
--  largest own seq of the logged APPLY entries and SEQ entries, and
--  Put_Frame of the written frame raises it to the new seq. There is no
--  second durable file, no persist-before-append duty and no Prepare /
--  Commit split. A crash before the APPLY entry is durable loses a frame
--  that was never sent (the binding flushes the log to Log_Length before
--  it sends a frame, DESIGN.md §8; A21), so the next write may reuse its
--  seq: no peer can hold that frame.
--
--  Outcomes (S17):
--    * OK: the record was applied (Store.Put_Frame OK); Rec is its header.
--    * Shadowed: a refusal decided before signing (t_emit = ceil and the
--      floor beats the prefix of v_emit, Kome.Emit.Choose). Nothing is
--      built or signed, and no seq is consumed.
--    * Inadmissible (the device key is not a writer) and Seq_Exhausted
--      (seq_self is at 2^48 - 1, a clone alarm): Choose's refusals.
--    * No_Space, Log_Full: Put_Frame's refusals for the data row and the
--      log. (Auth_Full and Ceil_Only are only for authorization records,
--      which this path does not write; Dominated cannot occur: an OK choice
--      is above every record that can dominate it,
--      Kome.Emit.Lemma_OK_Undominated.)
--    * Malformed: the signed frame failed Write's own check (below).
--  Every outcome except OK changes nothing.
--  One advisory flag, Clamped (H22): t_emit < max (now, floor_t + 1), the
--  ceiling held the write back. CLONE_SUSPECTED is read from Clone_View,
--  not from the write.
--
--  Write checks its own frame before it applies it: it verifies the bytes
--  (Kome.Store.Verified, the Pre of Put_Frame) and compares the decoded
--  header with the choice. Kome.Crypto does not state Verify (Sign (M))
--  (A1), so this check is code, not proof. It fails only for a signing key
--  whose signatures do not verify; then Write gives Malformed and changes
--  nothing. With a key from Kome.Crypto.Key_Pair it does not fail (tested,
--  not proved).
--
--  What the contracts state:
--    * Write (T8, cited from the Post of Kome.Emit.Choose): the record's
--      header is To_Header (target, Stamp (t, self, seq, h)) with h the
--      record's hash and seq = Seq_Self (S) + 1, above every held own seq
--      (Store.Lemma_Seq_Self); t is the formula of DESIGN.md §5 with the
--      S8 lower bound; Shadowed iff the floor beats the prefix; a floor
--      below the writer's ceiling is beaten (chase); an OK record is
--      admitted and undominated, and Put_Frame applied it (Lean's applyH;
--      seq_self is its seq);
--    * Receive (H18): Put_Frame for a frame from a peer, plus the flag
--      Clone_Suspected: the record is the device's own data record and
--      Put_Frame changed the pair with it (an own-key record that was not
--      held, not dominated and not a no-op). Receive can return Ceil_Only
--      (AUDIT.md H12: a ROSTER that the authorization rows had no room for
--      and whose ceiling the store recorded in the ceiling cell); it is a
--      change of the pair, not a refusal, and it never sets the flag (a
--      roster is not a data record).
--  Kome.Store.Put_Ceil, the entry point for the ceiling frame of a peer's
--  HELLO, has no wrapper here: Receive exists for the H18 flag, which is
--  about the device's own data records. The session caller calls
--  Kome.Store.Put_Ceil directly (kome-reconcile.ads).
--
--  CLONE_SUSPECTED (DESIGN.md §5, H8, H18) is shown when the Clone_Suspected
--  of Receive is set, or when Clone_View (F, self, seq_self) holds: a held
--  own seq above seq_self (H8; under Store.Valid this cannot hold, since
--  every own APPLY raises seq_self), or two held own records with equal seq
--  and different h (H18, Kome.Emit.Clone_Pair).
pragma Ada_2022;
with Kome.Versions;  use Kome.Versions;
with Kome.Headers;   use Kome.Headers;
with Kome.Keys;
with Kome.Crypto;
with Kome.Frontier;  use Kome.Frontier;
with Kome.Emit;      use Kome.Emit;
with Kome.Store;     use Kome.Store;
package Kome.Write with SPARK_Mode is

   ---------------------------------------------------------------------------
   --  The device key and the target.
   ---------------------------------------------------------------------------

   --  The lattice form of the device's public key.
   function Self_Of (SK : Kome.Crypto.Secret_Key) return Key256 is
     (Kome.Keys.To_Key256 (Kome.Crypto.Public_Of (SK)));

   --  The target of a write: a PUT of Field on Ent, or a DEL of Ent (Field
   --  is not read). The field hash is the one that Kome.Records.To_Header
   --  computes (G21).
   function Target_Of (Op : Write_Op; Ent : Ent_Id; Field : Byte_Array) return Target is
     (if Op = W_Put
      then Put_Target (Kome.Keys.To_Id128 (Ent), Field)
      else Del_Target (Kome.Keys.To_Id128 (Ent)))
   with Pre => (if Op = W_Put then Field'Length in 1 .. Field_Max);

   ---------------------------------------------------------------------------
   --  The write (S16, S17).
   ---------------------------------------------------------------------------

   --  Choose, Make, Sign and Put_Frame, on the store's collection and its
   --  frontier F, with the store's device key (Self_Key (S) is the key of
   --  SK) and its seq_self. See the header for the outcomes.
   procedure Write
     (S       : in out Kome.Store.Store;
      F       : in out State;
      Op      : in     Write_Op;
      Ent     : in     Ent_Id;
      Field   : in     Byte_Array;
      Value   : in     Byte_Array;
      Now     : in     U48;
      SK      : in     Kome.Crypto.Secret_Key;
      Rec     :    out Header;
      Result  :    out Status;
      Clamped :    out Boolean)
   with
     Global => null,
     Pre  => Valid (S, F)
       and then Kome.Crypto.Is_Valid (SK)
       and then Self_Of (SK) = Self_Key (S)
       and then (if Op = W_Put
                 then Field'Length in 1 .. Field_Max
                      and then Value'Length <= Value_Max),
     Post => Valid (S, F)
       and Same_Identity (S'Old, S)
       and Pinned (S) = Pinned (S'Old)
       and Log_Extends (S'Old, S)
       and Result in OK | Shadowed | Seq_Exhausted | Inadmissible | Malformed
                     | No_Space | Log_Full
       --  The refusals of Choose, as iffs (DESIGN.md §4, T13).
       and (Result = Inadmissible) = (not In_W (F'Old, Self_Key (S'Old)))
       and (Result = Seq_Exhausted)
             = (In_W (F'Old, Self_Key (S'Old)) and then Seq_Self (S'Old) = U48'Last)
       --  Every outcome but OK changes nothing; no seq is consumed.
       and (if Result /= OK then Unchanged (F'Old, F) and then S = S'Old)
       and (if Result in Inadmissible | Seq_Exhausted then not Clamped)
       --  The choice (Kome.Emit.Choose), for every outcome after it.
       and (if Result not in Inadmissible | Seq_Exhausted then
              Seq_Self (S'Old) < U48'Last
              and then Rec = Kome.Emit.To_Header
                               (Target_Of (Op, Ent, Field),
                                Stamp (Rec.V.T, Self_Key (S'Old), Seq_Self (S'Old) + 1,
                                       Rec.V.H))
              --  DESIGN.md §5 with the S8 lower bound.
              and then Rec.V.T = T_Emit (Now_Eff (Now, Max_Ceil (F'Old)), True,
                                         Floor_T (F'Old, Target_Of (Op, Ent, Field)),
                                         Eff_Ceil (F'Old, Self_Key (S'Old)))
              --  T8 / H8: above every held own seq.
              and then (for all I in 1 .. Count (F'Old) =>
                          (if Own (Held (F'Old, I), Self_Key (S'Old))
                           then Held (F'Old, I).V.Seq < Rec.V.Seq))
              --  H22, S17: the flag.
              and then Clamped = Is_Clamped (Rec.V.T, Now,
                                             Floor_T (F'Old, Target_Of (Op, Ent, Field)))
              --  S17: Shadowed iff the floor beats the prefix of v_emit;
              --  then nothing is built (h is zero in Rec).
              and then (Result = Shadowed)
                       = (Floor (F'Old, Target_Of (Op, Ent, Field)).Present
                          and then not Prefix_Lt
                                         (Floor (F'Old, Target_Of (Op, Ent, Field)).V,
                                          Stamp (Rec.V.T, Self_Key (S'Old), Rec.V.Seq,
                                                 Zero_Key)))
              and then (if Result = Shadowed then Rec.V.H = Zero_Key)
              --  T8 chase: a floor below the writer's ceiling is beaten.
              and then (if Floor (F'Old, Target_Of (Op, Ent, Field)).Present
                          and then Floor (F'Old, Target_Of (Op, Ent, Field)).V.T
                                   < Eff_Ceil (F'Old, Self_Key (S'Old))
                        then Result /= Shadowed
                             and then Prefix_Lt
                                        (Floor (F'Old, Target_Of (Op, Ent, Field)).V,
                                         Stamp (Rec.V.T, Self_Key (S'Old), Rec.V.Seq,
                                                Zero_Key))))
       --  A built record is admitted, new and undominated (T8 read your
       --  writes), so Put_Frame refuses it only for room.
       and (if Result in OK | No_Space | Log_Full then
              Admitted (F'Old, Rec) and then not Holds (F'Old, Rec)
              and then not Dom (F'Old, Rec)
              and then (if Result = No_Space then Data_Full (F'Old, Rec))
              and then (if Result = Log_Full then Effective (F'Old, Del_TTL (S'Old), Rec)))
       --  OK: Put_Frame applied it (Lean's applyH) and seq_self is its seq
       --  (S16), unless it is a DEL that arrived expired and dropped
       --  nothing (only a writer capped below the horizon can write one).
       and (if Result = OK then
              (if Effective (F'Old, Del_TTL (S'Old), Rec)
               then Applied_H (F'Old, F, Rec, Del_TTL (S))
                    and then Seq_Self (S) = Rec.V.Seq
                    and then Log_Entries (S) = Log_Entries (S'Old) + 1
               else Unchanged (F'Old, F) and then S = S'Old));

   ---------------------------------------------------------------------------
   --  The apply side of CLONE_SUSPECTED (AUDIT.md H18).
   ---------------------------------------------------------------------------

   --  Store.Put_Frame for a frame from a peer (DESIGN.md §7), and the H18
   --  flag. The Post is the Post of Put_Frame (Put_Done), and the flag.
   procedure Receive
     (S               : in out Kome.Store.Store;
      F               : in out State;
      Frame           : in     Byte_Array;
      H               : in     Header;
      Off             :    out Log_Size;
      Result          :    out Status;
      Clone_Suspected :    out Boolean)
   with
     Global => null,
     Pre  => Valid (S, F)
       and then Frame'Length in Frame_Size
       and then Verified (Cid (S), Root_Key (S), Frame)
       and then Header_Of (Cid (S), Frame) = H,
     Post => Put_Done (S'Old, S, F'Old, F, Frame, H, Off, Result)
       --  H18: an own record that changes the pair sets the flag, and
       --  nothing else does.
       and (Clone_Suspected
              = (Own (H, Self_Key (S'Old)) and then Result = OK
                 and then Effective (F'Old, Del_TTL (S'Old), H)));

   --  CLONE_SUSPECTED as a view over F and seq_self: a held own seq above
   --  seq_self (H8), or two held own records with equal seq and different
   --  h (H18, Kome.Emit.Clone_Pair). The caller ORs in the flag of the
   --  last Receive.
   function Clone_View (F : State; Self : Key256; Seq_Self : U48) return Boolean is
     (Clone_Detected (Seq_Self, Max_Own_Seq (F, Self)) or else Clone_Pair (F, Self));

end Kome.Write;
