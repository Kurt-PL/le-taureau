(* The hypotheses of M2DQCasHoistX.CASHoistX_forbidden_Q are not
   vacuous: CASHoistX has a done run of M2DQ (in order: r0 = y reads 0, the
   CAS of x is passed (its condition fails), the CAS of w happens in parts
   (load part alone, then store part), z = r1 + r2; then context 1, then
   context 2). Built as an M2DA run (runD) and mapped by M2DQ.runD_runQ. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Lit M2Ev M2EvLit M2Oota M2CasSplitProof M2DA M2DP M2DQ M2CasHoistXNeg.

Ltac nameD := match goal with |- exists t, starD _ ?S t /\ _ =>
  let s := fresh "s" in set (s := S) end.

(* a step that sets context c's oc at slot k0 only, where it is no whole CAS *)
Lemma nowhole_set : forall s s' c X k0 v, cs s' = upd (cs s) c X -> oc X = upd (oc (cs s c)) k0 v ->
  oh (cs s c) k0 <> None \/ is_cas (ai X k0) = false -> nowhole s s'.
Proof.
  intros s s' c X k0 v E O H0. apply (nowhole_upd s s' c X E). intros k Ne.
  destruct (Nat.eq_dec k k0) as [->|Nk]; [exact H0|exfalso; apply Ne; rewrite O; apply upd_n; exact Nk].
Qed.

Lemma some_ne : forall (o : option nat), match o with Some _ => true | None => false end = true -> o <> None.
Proof. intros [a|] H; [discriminate|discriminate H]. Qed.

(* an access that is not a CAS *)
Ltac NWo c := eapply (nowhole_set _ _ c); [reflexivity|reflexivity|right; vm_compute; reflexivity].
(* nothing happens *)
Ltac NWn c := eapply (nowhole_keep _ _ c); reflexivity.
(* the store part of a CAS whose load part happened alone *)
Ltac NWh c := eapply (nowhole_set _ _ c); [reflexivity|reflexivity|left; apply some_ne; vm_compute; reflexivity].

Lemma CASHoistX_runs : exists s, runQ CASHoistX s /\ done CASHoistX s.
Proof.
  cut (exists s, runD CASHoistX s /\ done CASHoistX s).
  { intros (s & R & D). exists s. split; [apply runD_runQ; exact R|exact D]. }
  apply startD.
  eapply fwdD. { ord 0. LD (@None nat). vis_none. } { NWo 0. } nameD.
  eapply fwdD. { skip 0. } { NWn 0. } nameD.
  eapply fwdD. { cread 0 2 [3] 2. LD (@None nat). vis_none. } { NWn 0. } nameD.
  eapply fwdD. { cw 0. eapply (e_cas_ok1 _ _ _ _ _ _ _ _ None); [reflexivity|vis_none|vm_compute; reflexivity|W0]. }
  { NWh 0. } nameD.
  eapply fwdD. { ordH 0. ST. W0. } { NWo 0. } nameD.
  eapply fwdD. { ord 1. LD (@None nat). vis_none. } { NWo 1. } nameD.
  eapply fwdD. { ord 1. ST. W0. } { NWo 1. } nameD.
  eapply fwdD. { ord 2. ST. W0. } { NWo 2. } nameD.
  eexists; split; [apply sd0|]. done_tac.
Qed.

Print Assumptions CASHoistX_runs.
