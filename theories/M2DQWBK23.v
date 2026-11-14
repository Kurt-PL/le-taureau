(* Part 23: instances for parts 19-22.
   - FWB (M2DQWBK16: F; CAS(x,1,2); F || F; r1 = x; F) is race-free (race_free_g, by the decision
     procedure of M2Trap), and its finished runWB, whose read takes the write-back store, satisfies
     KM and WK and is evok at every earlier state (stepWB_evok_back), so race-free code with an
     observed write-back meets the premises of parts 19-22 (non-vacuity).
   - KM, vmono and WK each fail on a state built to break them (negative instances). *)
From Stdlib Require Import Arith Lia List Bool Relations PArith.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Lit M2Ev M2DQWB M2DQWBK1 M2DQWBK16 M2DQWBK19 M2DQWBK20 M2DQWBK22 M2Trap.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

Theorem FWB_race_free : race_free_g FWB.
Proof. unfold FWB. apply (stat_race_free_g _ 2 1000%positive); [wf_tac|vm_compute; reflexivity|vm_compute; reflexivity]. Qed.

(* the finished run of FWB that observes its write-back satisfies KM and WK; its log has a store
   (the write-back, entry 1, with what it conveys inside the release view of its context) *)
Theorem FWB_WK : exists s, runWB FWB s /\ race_free_g FWB /\ KM s /\ WK s /\
  option_map (fun e => (ec e, ew e)) (ent s 1) = Some (0, true) /\ option_map (fun e => (ec e, erf e 0)) (ent s 4) = Some (1, Some 1) /\
  vsub (wc s 1) (vor (vR (cs s 0)) (vone 1)).
Proof.
  destruct FWB_run as (s & R & Q). exists s. pose proof (WK_run FWB FWB_wf s R) as Wk.
  split; [exact R|]. split; [exact FWB_race_free|]. split; [exact (runWB_KM FWB s R)|]. split; [exact Wk|].
  destruct Q as (_ & _ & _ & E4 & _ & _ & _ & _ & _ & _ & E1 & _).
  split; [destruct (ent s 1) as [e|]; [cbn in E1 |- *; injection E1 as -> -> _; reflexivity|discriminate]|].
  split; [exact E4|].
  destruct (ent s 1) as [e|] eqn:Ee; [|discriminate]. cbn in E1. injection E1 as Ec Ew _.
  pose proof (wk_R s Wk 1 e Ee Ew) as H. rewrite Ec in H. exact H.
Qed.

(* ---------- negative instances ---------- *)
Definition cbad : cst :=
  mkC (fun _ => None) (fun _ => 0) (fun _ => INop) (fun _ _ => None) (fun _ _ => 0) (fun _ => false)
      vnil vnil (vone 0) vnil vnil (fun _ => None) (fun _ => None).
Definition sbad : M2Model.st :=
  mkS 0 (fun _ => cbad) (fun _ _ => 0) (fun _ => vnil) (fun _ => []) vnil
      (fun _ => 0) (fun _ => 0) [] [] (fun _ => None).
Definition stm1 : M2Model.st :=
  mkS 1 (fun _ => cinit) (fun _ _ => 0) (fun _ => vnil) (fun _ => []) vnil
      (fun _ => 0) (fun _ => 0) [] [] (fun _ => None).

Lemma KM_neg : ~ KM sbad.
Proof. intros H. destruct (proj1 (H 0) 0 eq_refl) as [Z|Z]; cbn in Z; contradiction. Qed.
Lemma vmono_neg : ~ vmono sbad sinit.
Proof. intros (_ & H). destruct (H 0) as (_ & _ & R & _). exact (R 0 eq_refl). Qed.
Lemma vmono_pos : vmono sinit sbad.
Proof. split; [intros z Z; exact Z|]. intros c. cbn. repeat split; intros z Z; contradiction. Qed.
Lemma WK_neg : ~ WK stm1.
Proof. intros H. pose proof (wk_tm stm1 H) as E. cbn in E. discriminate. Qed.
Lemma KM_pos : KM sinit.
Proof. exact KM_init. Qed.
Lemma WK_pos : WK sinit.
Proof. exact WK_init. Qed.

Print Assumptions FWB_race_free.
Print Assumptions FWB_WK.
