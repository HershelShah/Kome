--  Kome.Write: the write path of one replica (DESIGN.md §5 "The write path
--  has three steps", §7; AUDIT.md A10, H18). It joins the steps that the
--  other packages prove one by one:
--
--    Choose (Kome.Emit)  ->  Make (Kome.Records Make_Put / Make_Del with
--    the chosen t and seq)  ->  Sign  ->  Store.Put_Frame (Kome.Store)
--
--  The write is split into two procedures, because a durable step of the
--  binding must come between them (AUDIT.md A10):
--
--    1. Prepare: Choose, Make, Sign and Encode. It changes nothing. On OK
--       or Shadowed it gives a Prepared frame (Ready) and Seq_Persist, the
--       new seq_self of (device key, collection).
--    2. The binding persists seq_self := Seq_Persist durably (write and
--       flush). SPARK has no file I/O here, so this step is a duty, stated
--       by the out value: Commit does not read seq_self at all.
--    3. Commit: Store.Put_Frame of the Prepared frame. Its Pre is Ready,
--       which only Prepare makes (Prepared is private; a default
--       Prepared is not Ready), so Commit appends no frame that Prepare
--       did not build, sign and check.
--    4. The binding flushes the log to Log_Length (S) before it sends the
--       frame to any peer or puts it in a bundle.
--
--  A5, restated (binding duty): seq_self is persisted before the APPLY is
--  appended, and a frame is sent only after its APPLY is durable. Then:
--    * a crash after step 2 and before step 4 loses at most a frame that
--      no peer has. The next write takes a larger seq (the persisted one
--      plus one), so no seq is reused, and no peer can offer the lost
--      frame back, so the apply-side flag below raises no false alarm
--      (AUDIT.md refuted item 65);
--    * a crash before step 2 loses nothing: Prepare changed nothing.
--  If the binding sends before the APPLY is durable and the log tail is
--  lost, the frame comes back from a peer as an own record that is not
--  held: Receive flags it, which is right (a lost log tail is a backup
--  restore, A4′).
--
--  On open, seq_self := max (stored, Max_Own_Seq (F, self))
--  (Seq_Self_At_Open), so a seq_self that lags the log (a stored value
--  from before the last write, a restored backup) never reissues a seq
--  that F holds. Open_Seq reports a seq store that the binding cannot read
--  (torn, bad checksum) as Seq_Corrupt, apart from Seq_Exhausted: the
--  write path then starts from Max_Own_Seq alone, exactly as after a
--  backup restore (H8), and the caller shows the status. Neither step
--  refuses a large jump of seq: own records leave F when they are
--  dominated, so a gap between the stored seq and the held ones is
--  normal.
--
--  What the contracts state:
--    * Prepare (T8, cited from the Post of Kome.Emit.Choose): the frame's
--      header is To_Header (target, Stamp (t, self, seq, h)) with h the
--      record's hash; seq is above seq_self and above every own held seq;
--      if the cell's floor is below the writer's ceiling, the result is
--      OK and the version is above the floor (Lt); an OK write is admitted
--      and no held record dominates it (Kome.Emit.Lemma_OK_Undominated);
--      t never passes the ceiling; the flags of Choose. The refusals of
--      Choose (Inadmissible, Seq_Exhausted) are iffs and leave seq_self.
--    * Commit: Store Valid is preserved; it refines Put_Frame for the
--      prepared record (each outcome as an iff, nothing changes on a
--      refusal, the APPLY entry is at Off, append-only).
--    * Receive (H18): Put_Frame for a frame from a peer, plus the flag
--      Clone_Suspected: the record is the device's own (Kome.Emit.Own),
--      it is OK, it was not held before and it is not an expired DEL. Then
--      it is held now: an admitted own-key record that was not held
--      before sets the flag. A duplicate, a dominated record and an
--      expired DEL do not.
--
--  Prepare checks its own frame before it gives it out. It verifies the
--  bytes (Kome.Store.Verified, the Pre of Put_Frame) and compares the
--  decoded header with the choice. Kome.Crypto does not state
--  Verify (Sign (M)) (A1), so this check is code, not proof. It fails only
--  for a signing key whose signatures do not verify; then Prepare gives
--  Malformed and changes nothing. With a key from Kome.Crypto.Key_Pair it
--  does not fail (tested, not proved).
--
--  CLONE_SUSPECTED (DESIGN.md §5, H8, H18) is shown when any of these
--  holds: the Clone_Suspected of Prepare (a held own seq above seq_self),
--  the Clone_Suspected of Receive (an own record arrived that changes F),
--  or Kome.Emit.Clone_Pair (F, self) (two held own records with equal seq
--  and different h). Clone_View is the view over F and seq_self.
pragma Ada_2022;
with Kome.Versions;  use Kome.Versions;
with Kome.Headers;   use Kome.Headers;
with Kome.Keys;
with Kome.Crypto;
with Kome.Records;
with Kome.Registers; use Kome.Registers;
with Kome.Frontier;  use Kome.Frontier;
with Kome.Emit;      use Kome.Emit;
with Kome.Views;
with Kome.Store;     use Kome.Store;
package Kome.Write with SPARK_Mode is

   ---------------------------------------------------------------------------
   --  The device key and the target.
   ---------------------------------------------------------------------------

   --  The lattice form of the device's public key.
   function Self_Of (SK : Kome.Crypto.Secret_Key) return Key256 is
     (Kome.Keys.To_Key256 (Kome.Crypto.Public_Of (SK)));

   --  The target of a write in the store's collection: a PUT of Field on
   --  (ns, Ent), or a DEL of (ns, Ent) (Field is not read). The field hash
   --  is the one that Kome.Records.To_Header computes (G21).
   function Target_Of
     (S : Kome.Store.Store; Op : Write_Op; Ent : Ent_Id; Field : Byte_Array) return Target
   is
     (if Op = W_Put
      then Put_Target (Collection (S), Kome.Keys.To_Id128 (Ent), Field)
      else Del_Target (Collection (S), Kome.Keys.To_Id128 (Ent)))
   with Pre => (if Op = W_Put then Field'Length in 1 .. Field_Max);

   ---------------------------------------------------------------------------
   --  seq_self at open (AUDIT.md A10).
   ---------------------------------------------------------------------------

   --  seq_self := max (stored, Max_Own_Seq (F, Self)). The result is at
   --  least the stored value and at least the seq of every held own
   --  record, so the next write's seq is above all of them.
   function Seq_Self_At_Open (Stored : U48; F : State; Self : Key256) return U48
   with
     Global => null,
     Post => Seq_Self_At_Open'Result = U48'Max (Stored, Max_Own_Seq (F, Self).Seq)
       and then Seq_Self_At_Open'Result >= Stored
       and then (for all I in 1 .. Count (F) =>
                   (if Own (Held (F, I), Self)
                    then Held (F, I).V.Seq <= Seq_Self_At_Open'Result));

   --  What the binding read from its seq store for (device key,
   --  collection): nothing (a new collection on this device), a value,
   --  or bytes it cannot read (torn, bad checksum).
   type Seq_Stored is (Seq_None, Seq_Read, Seq_Torn);

   --  seq_self at open. Seq_Torn gives Seq_Corrupt, which is a report, not
   --  a refusal: Seq_Self is then Max_Own_Seq alone (as after a backup
   --  restore, H8), and the caller shows the status. Otherwise the result
   --  is OK. Stored is read only for Seq_Read.
   procedure Open_Seq
     (Kind     : Seq_Stored;
      Stored   : U48;
      F        : State;
      Self     : Key256;
      Seq_Self : out U48;
      Result   : out Status)
   with
     Global => null,
     Post => (Result = Seq_Corrupt) = (Kind = Seq_Torn)
       and then (if Kind /= Seq_Torn then Result = OK)
       and then Seq_Self =
                  Seq_Self_At_Open ((if Kind = Seq_Read then Stored else 0), F, Self);

   ---------------------------------------------------------------------------
   --  The prepared write.
   ---------------------------------------------------------------------------

   subtype Frame_Length is Natural range 0 .. Kome.Records.Frame_Max;

   --  A frame that Prepare built, signed and checked, with its header.
   --  Private, so only Prepare makes a Ready value.
   type Prepared is private;

   function Length (P : Prepared) return Frame_Length with Global => null;

   function Frame_Of (P : Prepared) return Byte_Array with
     Global => null,
     Post => Frame_Of'Result'First = 0 and then Frame_Of'Result'Length = Length (P);

   --  The lattice header of the prepared record.
   function Rec (P : Prepared) return Header with Global => null;

   --  The frame is a verified data frame whose header is Rec (P): what
   --  Put_Frame requires (except the collection, which Commit checks
   --  against the store).
   function Ready (P : Prepared) return Boolean with Global => null;

   procedure Lemma_Ready (P : Prepared) with
     Ghost, Global => null,
     Pre  => Ready (P),
     Post => Length (P) in Frame_Size
       and then Verified (Frame_Of (P))
       and then Header_Of (Frame_Of (P)) = Rec (P)
       and then Kome.Records.Kind_Of (Frame_Of (P)) = Rec (P).K
       and then Canonical (Rec (P))
       and then Is_Data (Rec (P));

   --  Step 1 of the write: Choose, Make, Sign, Encode, on the store's
   --  collection and its frontier F. Nothing changes (all inputs are in).
   --    Inadmissible   the device key is not in W.
   --    Seq_Exhausted  the seq would pass 2^48 - 1 (a clone alarm, §5).
   --    Malformed      the signed frame failed Prepare's own check (see
   --                   the header; not reached with a Key_Pair key).
   --    OK / Shadowed  P is Ready, and Seq_Persist is the seq_self that
   --                   the binding persists before Commit (A5).
   --  On a refusal, P is not Ready and Seq_Persist = Seq_Self.
   procedure Prepare
     (S               : in     Kome.Store.Store;
      F               : in     State;
      Op              : in     Write_Op;
      Ent             : in     Ent_Id;
      Field           : in     Byte_Array;
      Value           : in     Byte_Array;
      Now             : in     U48;
      SK              : in     Kome.Crypto.Secret_Key;
      Seq_Self        : in     U48;
      P               :    out Prepared;
      Seq_Persist     :    out U48;
      Result          :    out Status;
      Clone_Suspected :    out Boolean;
      Clamped         :    out Boolean;
      Born_Expired    :    out Boolean)
   with
     Global => null,
     Pre  => Valid (S, F)
       and then Kome.Crypto.Is_Valid (SK)
       and then (if Op = W_Put
                 then Field'Length in 1 .. Field_Max
                      and then Value'Length <= Value_Max),
     Post => Result in OK | Shadowed | Seq_Exhausted | Inadmissible | Malformed
       --  H8: the restore / clone condition, always given (Choose).
       and then Clone_Suspected
                  = Clone_Detected (Seq_Self, Max_Own_Seq (F, Self_Of (SK)))
       --  The refusals of Choose, as iffs (DESIGN.md §4, T13).
       and then (Result = Inadmissible) = (not In_W (Regs (F), Self_Of (SK)))
       and then (Result = Seq_Exhausted)
                  = (In_W (Regs (F), Self_Of (SK))
                     and then Seq_Base (Seq_Self, Max_Own_Seq (F, Self_Of (SK))) = U48'Last)
       and then (Ready (P)) = (Result in OK | Shadowed)
       and then
       (if Result in OK | Shadowed then
          --  The record of step 2: the target of step 1, the chosen
          --  (t, seq), the device key, and its own hash (G21, D8).
          Rec (P) = Kome.Emit.To_Header
                      (Target_Of (S, Op, Ent, Field),
                       Stamp (Rec (P).V.T, Self_Of (SK), Seq_Persist, Rec (P).V.H))
          and then Rec (P).NS = Collection (S)
          --  T8 / H8 / T13: seq strictly increases, above every held own
          --  seq; by exactly one unless H8 made it jump.
          and then Seq_Persist = Seq_Base (Seq_Self, Max_Own_Seq (F, Self_Of (SK))) + 1
          and then Seq_Persist > Seq_Self
          and then (if not Clone_Suspected then Seq_Persist = Seq_Self + 1)
          and then (for all I in 1 .. Count (F) =>
                      (if Own (Held (F, I), Self_Of (SK))
                       then Held (F, I).V.Seq < Seq_Persist))
          --  T9 / T13: never above the writer's ceiling.
          and then Rec (P).V.T <= Eff_Ceil (F, Self_Of (SK))
          --  H28: above the store's expire mark below the ceiling.
          and then (if Expire_Mark (S) < Eff_Ceil (F, Self_Of (SK))
                    then Rec (P).V.T > Expire_Mark (S))
          --  T8 chase (Kome.Emit.Choose): a floor below the writer's
          --  ceiling is beaten, and the write is OK.
          and then (if Floor (F, Target_Of (S, Op, Ent, Field)).Present
                      and then Floor (F, Target_Of (S, Op, Ent, Field)).V.T
                               < Eff_Ceil (F, Self_Of (SK))
                    then Result = OK
                         and then Lt (Floor (F, Target_Of (S, Op, Ent, Field)).V, Rec (P).V))
          --  T8 read-your-writes: an OK write is admitted and undominated
          --  (Kome.Emit.Lemma_OK_Undominated), so Commit on this F holds
          --  it unless the store is full.
          and then (if Result = OK
                    then Admitted (F, Rec (P)) and then not Dom (F, Rec (P)))
          --  H22 flags, as Choose gives them.
          and then Clamped
                     = Is_Clamped (Rec (P).V.T, Now,
                                   Floor_Time (F, Target_Of (S, Op, Ent, Field),
                                               Expire_Mark (S)))
          and then Born_Expired
                     = Is_Born_Expired (Target_Of (S, Op, Ent, Field), Rec (P).V.T,
                                        Kome.Views.Del_TTL_Eff (F), Now)
        else Seq_Persist = Seq_Self
             and then not Clamped and then not Born_Expired);

   --  Step 3 of the write: append the prepared record (Store.Put_Frame).
   --  The binding has persisted Seq_Persist before this call, and flushes
   --  the log to Log_Length (S) before it sends Frame_Of (P) (A5). Off is
   --  the offset of the APPLY entry.
   procedure Commit
     (S      : in out Kome.Store.Store;
      F      : in out State;
      P      : in     Prepared;
      Off    :    out Log_Size;
      Result :    out Status)
   with
     Global => null,
     Pre  => Valid (S, F) and then Ready (P) and then Rec (P).NS = Collection (S),
     Post => Valid (S, F)
       and Same_Identity (S'Old, S)
       and Horizon (S) = Horizon (S'Old)
       and Auth_Gen (S) = Auth_Gen (S'Old)
       and Off = Log_Length (S'Old)
       and Log_Extends (S'Old, S)
       and Result in OK | Dominated | Inadmissible | No_Space | Log_Full
       and (Result = Inadmissible) = (not Admitted (F'Old, Rec (P)))
       and (Result = Dominated)
             = (Admitted (F'Old, Rec (P)) and then not Holds (F'Old, Rec (P))
                and then Dom (F'Old, Rec (P)))
       and (Result = No_Space)
             = (Admitted (F'Old, Rec (P))
                and then At_Bound (S'Old, F'Old, Rec (P), Length (P)))
       and (Result = Log_Full)
             = (Admitted (F'Old, Rec (P))
                and then At_Log_Bound (S'Old, F'Old, Rec (P), Length (P)))
       and (if Result /= OK or else Holds (F'Old, Rec (P))
            then Unchanged (F'Old, F) and then S = S'Old)
       --  OK on a record that was not held and is not an expired DEL: it
       --  is held, indexed, and its APPLY is the entry at Off.
       and (if Result = OK and then not Holds (F'Old, Rec (P))
               and then not Expired (Rec (P), Horizon (S'Old))
            then Holds (F, Rec (P))
                 and then Indexed (S, Rec (P))
                 and then Applied (F'Old, F, Rec (P))
                 and then Appended (S'Old, S, Frame_Of (P), Rec (P), Off));

   ---------------------------------------------------------------------------
   --  The apply side of CLONE_SUSPECTED (AUDIT.md H18).
   ---------------------------------------------------------------------------

   --  The flag of Receive: the record is the device's own data record, it
   --  was applied (OK), it was not held before, and it is not an expired
   --  DEL. No quantifier, so it is public; Was_Held is Holds (F, H)
   --  before the call.
   function Own_Arrival
     (H : Header; Self : Key256; Result : Status; Was_Held : Boolean; Hz : Time64)
      return Boolean
   is
     (Own (H, Self) and then Result = OK and then not Was_Held
      and then not Expired (H, Hz));

   --  Store.Put_Frame for a frame from a peer (DESIGN.md §7 steps 0-6), and
   --  the H18 flag. The Post is the Post of Put_Frame, and the flag.
   procedure Receive
     (S               : in out Kome.Store.Store;
      F               : in out State;
      Frame           : in     Byte_Array;
      H               : in     Header;
      Self            : in     Key256;
      Off             :    out Log_Size;
      Result          :    out Status;
      Clone_Suspected :    out Boolean)
   with
     Global => null,
     Pre  => Valid (S, F)
       and then Frame'Length in Frame_Size
       and then Verified (Frame)
       and then Header_Of (Frame) = H
       and then Kome.Records.Kind_Of (Frame) = H.K
       and then Canonical (H)
       and then H.NS = Collection (S),
     Post => Valid (S, F)
       and Same_Identity (S'Old, S)
       and Horizon (S) = Horizon (S'Old)
       and Off = Log_Length (S'Old)
       and Result in OK | Dominated | Inadmissible | Malformed | No_Space | Auth_Full | Log_Full
       and (Result = Malformed) = Foreign_Root (S'Old, Frame)
       and (Result = Inadmissible)
             = (not Foreign_Root (S'Old, Frame) and then not Admitted (F'Old, H))
       and (Result = Dominated)
             = (not Foreign_Root (S'Old, Frame) and then Admitted (F'Old, H)
                and then not Holds (F'Old, H) and then Dom (F'Old, H))
       and (Result = Auth_Full)
             = (not Foreign_Root (S'Old, Frame) and then not Holds (F'Old, H)
                and then not Dom (F'Old, H)
                and then (Auth_Rule (F'Old, H) or else Gen_Full (S'Old, H)))
       and (Result = No_Space)
             = (not Foreign_Root (S'Old, Frame) and then Admitted (F'Old, H)
                and then At_Bound (S'Old, F'Old, H, Frame'Length))
       and (Result = Log_Full)
             = (not Foreign_Root (S'Old, Frame) and then Admitted (F'Old, H)
                and then At_Log_Bound (S'Old, F'Old, H, Frame'Length))
       and (if Result /= OK or else Holds (F'Old, H)
               or else (Expired (H, Horizon (S'Old)) and then not Drops_Any (F'Old, H))
            then Unchanged (F'Old, F) and then S = S'Old)
       and Log_Extends (S'Old, S)
       and (if Result = OK and then not Holds (F'Old, H) and then Is_Auth (H)
            then Auth_Gen (S'Old) < Auth_Gen_Max and then Auth_Gen (S) = Auth_Gen (S'Old) + 1
            else Auth_Gen (S) = Auth_Gen (S'Old))
       and (if Result = OK and then not Holds (F'Old, H)
               and then Expired (H, Horizon (S'Old)) and then Drops_Any (F'Old, H)
            then Expire_Mark (S) = U48'Max (Expire_Mark (S'Old), H.V.T)
            else Expire_Mark (S) = Expire_Mark (S'Old))
       and (if Result = OK and then not Holds (F'Old, H) then
              (if Expired (H, Horizon (S'Old))
               then (if Drops_Any (F'Old, H)
                     then Expired_Applied (F'Old, F, H)
                          and then Appended_Expired (S'Old, S, Frame, Off))
               else Holds (F, H)
                    and then Indexed (S, H)
                    and then Applied (F'Old, F, H)
                    and then Appended (S'Old, S, Frame, H, Off)))
       --  H18: an own record that changes F (OK, not held before, not an
       --  expired DEL) sets the flag, and nothing else does.
       and Clone_Suspected
             = Own_Arrival (H, Self, Result, Holds (F'Old, H), Horizon (S'Old))
       --  The flag means: an admitted own-key record that was not held
       --  before, and is not dominated, is held now.
       and (if Clone_Suspected
            then Own (H, Self) and then Admitted (F'Old, H)
                 and then not Holds (F'Old, H) and then not Dom (F'Old, H)
                 and then Holds (F, H))
       and (if Own (H, Self) and then Result = OK and then not Holds (F'Old, H)
               and then not Expired (H, Horizon (S'Old))
            then Clone_Suspected);

   --  CLONE_SUSPECTED as a view over F and seq_self: a held own seq above
   --  seq_self (H8), or two held own records with equal seq and different
   --  h (H18, Kome.Emit.Clone_Pair). The caller ORs in the flag of the
   --  last Receive.
   function Clone_View (F : State; Self : Key256; Seq_Self : U48) return Boolean is
     (Clone_Detected (Seq_Self, Max_Own_Seq (F, Self)) or else Clone_Pair (F, Self));

private

   type Prepared is record
      Buf : Byte_Array (0 .. Kome.Records.Frame_Max - 1) := [others => 0];
      Len : Frame_Length := 0;
      H   : Header;
   end record;

   function Length (P : Prepared) return Frame_Length is (P.Len);

   function Frame_Of (P : Prepared) return Byte_Array is (P.Buf (0 .. P.Len - 1));

   function Rec (P : Prepared) return Header is (P.H);

   function Ready (P : Prepared) return Boolean is
     (P.Len in Frame_Size
      and then Verified (Frame_Of (P))
      and then Header_Of (Frame_Of (P)) = P.H
      and then Kome.Records.Kind_Of (Frame_Of (P)) = P.H.K
      and then Canonical (P.H)
      and then Is_Data (P.H));

end Kome.Write;
