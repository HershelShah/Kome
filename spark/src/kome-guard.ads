--  Kome.Guard: the session gate and the quarantine flag of one replica
--  (DESIGN.md §6 "Two gates on transport"; AUDIT.md A3 and H2). The
--  transport (phase 9) calls it: nothing here reads the network, a clock
--  or an RNG, and nothing here changes F.
--
--  THE GATE (A3). A peer may open a session for the collection of S iff
--  its Noise static key is the dh_pk of a member of ROSTER_eff whose
--  sign_pk is not revoked. "Revoked" is Kome.Views.Revoked: a held REVOKE
--  of the sign_pk from an issuer that is not root_void, whatever its
--  from_t. So a revocation closes the gate at once, before the roster that
--  removes the member arrives and wins ROSTER_eff. The same test applies
--  to a HELLO credential (the peer's member entry in the credential) and
--  to the boxes that a roster seals (Kome.Roster seals no box for a
--  revoked member). The gate is a transport decision: it reads REVOKE, so
--  it is not monotone in F, and it never feeds admission (T4').
--
--  THE QUARANTINE FLAG (H2). A pre-gate OPEN carries founding REVOKEs, and
--  the receiver applies them before its gate. If such a REVOKE root-voids
--  the signer of the current ROSTER_eff, ROSTER_eff falls back to an older
--  roster, which can list members that the voided root had removed. The
--  recovery roster that the founding key issues with that REVOKE may not
--  have arrived. The flag records this: it is set when a pre-gate OPEN
--  root-voids the signer of ROSTER_eff, and it clears only when a
--  founding-signed roster is applied and is ROSTER_eff. While it is set,
--  the replica admits a peer only through a HELLO whose credential is such
--  a roster (so the credential itself clears the flag), takes no sealed
--  bundle and seals none. The flag lives outside F (it depends on the
--  order of arrival, which F does not record), and the transport keeps it
--  with the store. It is not "gen or epoch non-regression": a thief can
--  set gen or epoch to the largest value, and no recovery roster could
--  exceed it. A founding roster is ROSTER_eff as soon as it beats every
--  roster of a signer that is not root-voided, whatever the voided root
--  wrote.
--
--  The transport evaluates Admits (G, S, R, DH) after it applied the
--  peer's OPEN (and its credential R, if the HELLO came first), with S the
--  state after those applications. R must be the record of ROSTER_eff
--  (the precondition states this through To_Header).
pragma Ada_2022;
with Kome.Keys;     use Kome.Keys;
with Kome.Headers;  use Kome.Headers;
with Kome.Frontier; use Kome.Frontier;
with Kome.Views;    use Kome.Views;
with Kome.Records;  use Kome.Records;
package Kome.Guard with SPARK_Mode is

   --  The index of the member of C whose dh_pk is DH, or 0.
   function Member_Of (C : Roster_Content; DH : Pubkey) return Member_Count with
     Global => null,
     Post   => (if Member_Of'Result = 0
                then (for all I in 1 .. C.N_Members => Member_DH_PK (C, I) /= DH)
                else Member_Of'Result <= C.N_Members
                     and then Member_DH_PK (C, Member_Of'Result) = DH);

   --  The gate (A3): DH is the dh_pk of a member of the roster R, which is
   --  ROSTER_eff of S, and that member's sign_pk is not revoked in S.
   function Gate (S : State; R : Roster_Record; DH : Pubkey) return Boolean is
     (declare
        I : constant Member_Count := Member_Of (R.C, DH);
      begin
        I /= 0 and then not Revoked (S, Member_Key (R.C, I)))
   with Pre => Roster_Eff (S) = (Present => True, Hdr => To_Header (R));

   --  A held REVOKE of a member's sign_pk, from an issuer that is not
   --  root_void, closes the gate for that member's dh_pk.
   procedure Lemma_Gate_Refuses_Revoked (S : State; R : Roster_Record; DH : Pubkey) with
     Ghost, Global => null,
     Pre  => Roster_Eff (S) = (Present => True, Hdr => To_Header (R))
             and then Member_Of (R.C, DH) /= 0
             and then Revoked (S, Member_Key (R.C, Member_Of (R.C, DH))),
     Post => not Gate (S, R, DH);

   --  The quarantine flag (H2).
   type Guard_State is record
      Quarantined : Boolean := False;
   end record;

   --  The transport calls Note_Open after it applied the frames of a
   --  pre-gate OPEN: Before is the state before them, After the state
   --  after them. The flag is set if the OPEN root-voided the signer of
   --  the ROSTER_eff of Before. It never clears here.
   procedure Note_Open (G : in out Guard_State; Before, After : State) with
     Global => null,
     Post   => G.Quarantined =
                 (G'Old.Quarantined
                  or else (Roster_Eff (Before).Present
                           and then Root_Void (After, Roster_Eff (Before).Hdr.Issuer)));

   --  The transport calls Note_Credential after it applied a HELLO
   --  credential Cred (a roster, as its header): After is the state after
   --  it. The flag clears iff the credential is founding-signed and is
   --  ROSTER_eff of After. Nothing else clears it.
   procedure Note_Credential (G : in out Guard_State; After : State; Cred : Header) with
     Global => null,
     Post   => G.Quarantined =
                 (G'Old.Quarantined
                  and then not (Cred.K = K_Roster
                                and then Cred.Issuer = Founding (After)
                                and then Roster_Eff (After) = (Present => True, Hdr => Cred)));

   --  The transport admits a peer iff the flag is clear and the gate
   --  admits it. While the flag is set, it also takes no sealed bundle and
   --  seals none (a caller duty; this package sees no bundle).
   function Admits (G : Guard_State; S : State; R : Roster_Record; DH : Pubkey)
     return Boolean is
     (not G.Quarantined and then Gate (S, R, DH))
   with Pre => Roster_Eff (S) = (Present => True, Hdr => To_Header (R));

end Kome.Guard;
