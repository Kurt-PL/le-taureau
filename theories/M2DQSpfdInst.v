(* SPFD on M2DQ (retarget of M2DPSpfdInst.v, the M2DP run).
     SPFD: r0 = y; [r0 = 0] CAS(x, 0, 5); [r0 <> 0] CAS(x, 7, 5); x = 1  ||  r1 = x; y = r1
   Changes against the M2DP script: startP/starP/fwdO/fwdR/p_old/p_rfix become
   startQ/starQ/fwdQ/fwdRQ/q_old/q_rfix. fwdRQ enters the state sbd (scfail s c k) c B, which is
   what q_rfix produces. Statement: SPFD_Q. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Lit M2Ev M2EvLit M2Oota M2CasSplitProof.
Require Import M2DA M2DAInv M2DP M2DPSpfdStep M2DQ M2DQInst.

Ltac nameP := match goal with |- exists t, starQ _ ?S t /\ _ =>
  let s := fresh "s" in set (s := S) end.
Ltac nwQ :=   first [eapply nowhole_put; [reflexivity|reflexivity|vm_compute; reflexivity]
        |eapply nowhole_keep; [reflexivity|reflexivity]].

(* the record fix on M2DQ: q_rfix leaves the state sbd (scfail s c k) c B *)
Lemma fwdRQ : forall p s c k B (Q : M2Model.st -> Prop), rfail_ok p c (cs s c) (pcs s c) (tp s c) k B ->
  (forall j, pcs s c <= j -> fx (cs s c) j = None -> ~ cfix_ok p c (cs s c) (pcs s c) (tp s c) j false B (Some k)) ->
  (exists t, starQ p (sbd (scfail s c k) c B) t /\ Q t) -> exists t, starQ p s t /\ Q t.
Proof. intros p s c k B Q O N (t & A & Bq). exists t. split; [eapply sqS; [exact (q_rfix p s c k B O N)|exact A]|exact Bq]. Qed.

(* the read alone, early, at slot 2: its claim is 1 or 2 by the free value of y *)
Ltac SPFD_cread := eapply (s_cread _ _ 0 2 Plain [0] (fun _ => false) _ _ _ _ _ true);
  [vm_compute; lia|vm_compute; reflexivity|vm_compute; reflexivity|slot_tac
  |let f := fresh "f" in let E := fresh "E" in intros f; cbv zeta; destruct (f 0 1) as [|n] eqn:E;
     [exists 1|exists 2]; (split;
     [fatRN 3; vm_compute; rewrite ?E; vm_compute; bitsplit; reflexivity
     |let x := fresh "x" in let b := fresh "b" in let X := fresh "X" in intros x b _ X; vm_compute in X; discriminate X])
  | |fxr_tac].

(* rfail_ok for the record at slot 2, value 0 *)
Ltac SPc E := vm_compute; rewrite ?E; vm_compute; bitsplit; reflexivity.
Ltac SPFD_rfail := split; [vm_compute; reflexivity|]; split; [vm_compute; discriminate|]; split; [vm_compute; reflexivity|];
  exists 0; let f := fresh "f" in let E := fresh "E" in intros f; cbv zeta; destruct (f 0 1) as [|n] eqn:E;
  [exists 1|exists 2];
  (split; [split; [vm_compute; lia|split; [SPc E|split; [SPc E|split; [SPc E|split; [SPc E|SPc E]]]]]|SPc E]).

Ltac SPFD_nf := let j := fresh "j" in let L := fresh "L" in let Fx := fresh "Fx" in let Cf := fresh "Cf" in
  let P0 := fresh "P0" in let OC := fresh "OC" in let k := fresh "k" in
  intros j L Fx Cf;
  match type of Cf with cfix_ok _ _ ?cc ?pc _ _ _ _ _ =>
    assert (P0 : pc = 0) by (vm_compute; reflexivity);
    assert (OC : forall k, oc cc k = None) by (intros k; vm_compute; reflexivity);
    rewrite P0 in Cf; exact (SPFD_nofix_any _ _ _ _ _ _ OC Cf) end.

Theorem SPFD_Q : exists s, runQ SPFD s /\ done SPFD s /\ evok s /\
  rg (cs s 0) 0 = 1 /\ rg (cs s 0) 1 = 0 /\ rg (cs s 0) 2 = vd false 0 /\ rg (cs s 1) 0 = 1.
Proof.
  apply startQ.
  eapply fwdQ. { SPFD_cread. LD (@None nat). vis_none. } { nwQ. } nameP.
  eapply (fwdRQ _ _ 0 2 (fun _ => false)). { SPFD_rfail. } { SPFD_nf. } nameP.
  (* x = 1 early: under every free values, the CAS at the record's claim fails *)
  eapply fwdQ. { eapply (s_early _ _ 0 3 (DSt Plain [0] 1) (fun _ => false));
    [vm_compute; lia|vm_compute; reflexivity|vm_compute; reflexivity|slot_tac
    |let f := fresh "f" in let E := fresh "E" in intros f; cbv zeta; exists 3; split; [vm_compute; lia|]; split;
       [fatN 3; vm_compute; destruct (f 0 1) eqn:E; vm_compute; bitsplit; reflexivity
       |let X := fresh "X" in intros X; discriminate X]
    | |fxe_tac]. ST. W0. } { nwQ. } nameP.
  eapply fwdQ. { ord 1. LD (Some 1). vis_some. } { nwQ. } nameP.
  eapply fwdQ. { ord 1. ST. W0. } { nwQ. } nameP.
  eapply fwdQ. { ordH 0. LD (Some 3). vis_some. } { nwQ. } nameP.
  eapply fwdQ. { skipH 0. } { nwQ. } nameP.
  eapply fwdQ. { skipF 0. } { nwQ. } nameP.
  eapply fwdQ. { mtchH 0 (DSt Plain [0] 1). } { nwQ. } nameP.
  eexists; split; [apply sq0|].
  split; [done_tac|split; [evok_tac [0;1;2;3;4]|split; [reflexivity|split; [reflexivity|split; reflexivity]]]].
Qed.

Print Assumptions SPFD_Q.
