(* Instances of M2DA's model at real states.
     CAS1: CAS(x, 0, 5)
   - CAS1_split: a done run of M2DA's model (runD): read alone, then write
     half; the CAS succeeds (vd true 0), final x = 5.
   - CAS1_whole_not_D: the whole-CAS step from the initial state is a step of
     M2Model but not of M2DA's model (nowhole fails). *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Lit M2Ev M2EvLit M2Oota M2CasSplitProof M2DA.

Ltac nameD := match goal with |- exists t, starD _ ?S t /\ _ =>
  let s := fresh "s" in set (s := S) end.

Definition CAS1 : prog := stat [ [ICas Plain [0] T (K 0) (K 5)] ].

Lemma CAS1_split : exists s, runD CAS1 s /\ done CAS1 s /\ evok s /\ rg (cs s 0) 0 = vd true 0 /\ final s 0 = 5.
Proof.
  apply startD.
  eapply fwdD. { cread 0 0 [0] 0. LD (@None nat). vis_none. }
  { apply nowhole_oc. intros c k. cbn [cs]. unfold upd. destruct (Nat.eqb c 0); reflexivity. }
  nameD.
  eapply fwdD. { cw 0. eapply (e_cas_ok1 _ _ _ _ _ _ _ _ None); [reflexivity|vis_none|vm_compute; reflexivity|W0]. }
  { apply nowhole_at. intros c k Nq. destruct (Nat.eq_dec c 0) as [->|Nc].
    - destruct (Nat.eq_dec k 0) as [->|Nk].
      + subst s. cbn [cs]. rewrite upd_o. cbn [oh]. rewrite upd_o. discriminate.
      + exfalso. apply Nq. cbn [cs]. rewrite !upd_o. cbn [oc]. rewrite upd_n by exact Nk. reflexivity.
    - exfalso. apply Nq. cbn [cs]. rewrite !upd_n by exact Nc. reflexivity. }
  nameD.
  eexists; split; [apply sd0|].
  split; [done_tac|split; [evok_tac [0;1]|split; reflexivity]].
Qed.

Lemma CAS1_whole_not_D : exists s1, step CAS1 sinit s1 /\ ~ nowhole sinit s1 /\ rg (cs s1 0) 0 = vd true 0.
Proof.
  eexists. split; [ord 0; eapply (e_cas_ok1 _ _ _ _ _ _ _ _ None); [reflexivity|vis_none|vm_compute; reflexivity|W0]|].
  split; [|reflexivity].
  intros N. apply (N 0 0); [reflexivity|cbn [cs]; rewrite upd_o; cbn [oc]; rewrite upd_o; discriminate|reflexivity|reflexivity].
Qed.

Print Assumptions CAS1_split.
Print Assumptions CAS1_whole_not_D.
