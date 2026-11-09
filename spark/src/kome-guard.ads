--  Kome.Guard: the session gate of one replica (DESIGN.md §6 "Two gates on
--  transport"; AUDIT.md A3 and H2; SIMPLIFY.md S9, S10, S11). The
--  transport calls it: nothing here reads the network, a clock or an RNG,
--  nothing here changes F, and it keeps no state.
--
--  THE GATE (A3). A peer may open a session for the collection of S iff
--  its Noise static key is the dh_pk of a member of ROSTER_eff whose
--  sign_pk is not revoked. "Revoked" is Kome.Views.Revoked: a held REVOKE
--  of the sign_pk from an issuer that is not root_void, whatever its
--  from_t. So a revocation closes the gate at once, before the roster that
--  removes the member arrives and wins ROSTER_eff. The same test applies
--  to a HELLO credential (the peer's member entry in the credential) and
--  to the boxes that a roster seals (no box for a revoked member). The
--  gate is a transport decision: it reads REVOKE, so it is not monotone
--  in F, and it never feeds admission (T4').
--
--  THE QUARANTINE (H2, S10) is a view of F: Kome.Views.Quarantined, the
--  maximal held roster (root-voided ones included) has a root-voided
--  signer. If a founding REVOKE root-voids the signer of the newest
--  roster, ROSTER_eff falls back to an older roster, which can list
--  members that the voided root had removed; the quarantine holds until a
--  roster of a signer that is not voided beats the voided root's rosters
--  by gen (the recovery roster; Lemma_Quarantine_Cleared). While it holds,
--  the replica admits no peer, takes no sealed bundle and seals none (a
--  caller duty for the bundles; this package sees none). It depends only
--  on F, so it needs no durable flag and no order of arrival: a batch
--  applies its ROSTERs before its REVOKEs (key order, tag 0 < 1), and the
--  recovery roster reaches a captured replica as a HELLO credential
--  (S11). A thief can set gen high, but a thief's roster is in the
--  maximum only until a recovery roster at a higher gen arrives.
--
--  The transport evaluates Admits (S, R, DH) on every Receive and
--  Next_Phase (S9), with S the state after the batch, and R the record of
--  ROSTER_eff (the precondition states this through To_Header).
pragma Ada_2022;
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

   --  The transport admits a peer iff the gate admits it and the replica
   --  is not quarantined (SIMPLIFY.md S10).
   function Admits (S : State; R : Roster_Record; DH : Pubkey) return Boolean is
     (Gate (S, R, DH) and then not Quarantined (S))
   with Pre => Roster_Eff (S) = (Present => True, Hdr => To_Header (R));

   --  A held REVOKE of a member's sign_pk, from an issuer that is not
   --  root_void, closes the gate for that member's dh_pk.
   procedure Lemma_Gate_Refuses_Revoked (S : State; R : Roster_Record; DH : Pubkey) with
     Ghost, Global => null,
     Pre  => Roster_Eff (S) = (Present => True, Hdr => To_Header (R))
             and then Member_Of (R.C, DH) /= 0
             and then Revoked (S, Member_Key (R.C, Member_Of (R.C, DH))),
     Post => not Gate (S, R, DH) and then not Admits (S, R, DH);

   --  The quarantine is set by a root-void of the maximal roster's signer:
   --  if a held roster that no held roster beats in the roster order has
   --  a root-voided signer, the replica is quarantined and admits no peer.
   procedure Lemma_Quarantine_Set (S : State; I : Held_Index) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S) and then I <= Count (S)
             and then Held (S, I).K = K_Roster
             and then Root_Void (S, Held (S, I).Issuer)
             and then (for all J in 1 .. Count (S) =>
                         (if Held (S, J).K = K_Roster
                          then not Roster_Lt (Held (S, I), Held (S, J)))),
     Post => Quarantined (S)
             and then Roster_Max (S) = (Present => True, Hdr => Held (S, I));

   --  While quarantined, no peer is admitted.
   procedure Lemma_Quarantine_Refuses (S : State; R : Roster_Record; DH : Pubkey) with
     Ghost, Global => null,
     Pre  => Roster_Eff (S) = (Present => True, Hdr => To_Header (R))
             and then Quarantined (S),
     Post => not Admits (S, R, DH);

   --  The quarantine is cleared by a roster of a signer that is not
   --  root-voided at a gen above every other held roster (the recovery
   --  roster): it is then the maximal roster and ROSTER_eff.
   procedure Lemma_Quarantine_Cleared (S : State; I : Held_Index) with
     Ghost, Global => null,
     Pre  => Is_Frontier (S) and then I <= Count (S)
             and then Held (S, I).K = K_Roster
             and then not Root_Void (S, Held (S, I).Issuer)
             and then (for all J in 1 .. Count (S) =>
                         (if Held (S, J).K = K_Roster and then J /= I
                          then Held (S, J).V.Seq < Held (S, I).V.Seq)),
     Post => not Quarantined (S)
             and then Roster_Max (S) = (Present => True, Hdr => Held (S, I))
             and then Roster_Eff (S) = (Present => True, Hdr => Held (S, I));

end Kome.Guard;
