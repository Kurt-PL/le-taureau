(* Instances of part 30 on litmus runs (no vacuous premises).
     WBF:  F; r0 = CAS(x, 1, 2); F  ||  F; x = 3; F       (x = cell 0, initially 0)
   It is race-free (the conflicting accesses are both fenced; M2Trap decision procedure).
   Context 1 runs first (times 0..2), then context 0's guard() (time 3).  At that state:
     - wbP: the CAS's read half happens alone (time 4, reading x = 3, the store at time 1),
       failure is fixed (s_cfix), and the context passes the CAS (s_skip, partskip); wbc_wbP
       holds for u = 1.
   The states before the write-back are M2DQ runs, their own images (M2DQWBK29.self_image).
   WBF_stands: the same split failure written back (id 4, right after the store 1 it read) on a
   runWB; stands_for_kept.  stands_for_kept on FWB's write-back run (M2DQWBK16) is not
   instantiated with a stood-for store (FWB's write-back stands for the initial value);
   kept_ent and stands_kept are. *)
From Stdlib Require Import Arith Lia List Bool PArith.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO M2SC M2SCx MIPComp MIPNeg M2Iface MIPSync MIBase MIPDrf.
Require Import M2Lit M2Ev M2EvLit M2EvTimeProof M2CasSplitProof M2Trap.
Require Import M2DQWBK13 M2DQWBK16 M2DQIfaceUse M2IfaceInst M2DQIfaceInst M2WBRel M2DQWBPatch M2DQWB M2DQWBK1 M2DQWBK3 M2DQWBK15 M2DQWBK20 M2DQWBK22 M2DQWBK29 M2DQWBK30.
Require Import M2DA M2DP M2DQDec M2DQCas2Inst.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

Ltac W0 := enter_at (@nil (nat * bool)) (@nil (nat * bool)).
Ltac LD u := eapply (e_ld1 _ _ _ _ _ _ u); [reflexivity|].
Ltac ST := eapply e_st1; [reflexivity|].

(* an M2DQ run built forward from q_old steps, kept both as a run of M2DQ and as a run of A *)
Lemma startV2 : forall p (Q : M2Model.st -> Prop),
  (exists t, starV p sinit t /\ (M2Model.run p t -> runQ p t -> Q t)) -> exists t, runQ p t /\ Q t.
Proof.
  intros p Q (t & H & q). destruct (starV_both p sinit t H) as [A B].
  assert (RQ : runQ p t) by exact (starQ_run p sinit t (x0 p) B).
  exists t. split; [exact RQ|]. apply q; [exact (M2Lit.star_run p sinit t (M2Model.r0 p) A)|exact RQ].
Qed.

Definition WBF : prog := stat
  [ [IFn FFull; ICas Plain [0] T (K 1) (K 2); IFn FFull];
    [IFn FFull; st 0 3; IFn FFull] ].

Lemma WBF_wf : wf WBF.
Proof. unfold WBF. wf_tac. Qed.

Lemma WBF_race_free : race_free_g WBF.
Proof. unfold WBF. apply (stat_race_free_g _ 2 1000%positive); [wf_tac|vm_compute; reflexivity|vm_compute; reflexivity]. Qed.

Lemma WBF_cellful : cellful WBF.
Proof.
  apply cellful_of. intros c k r A. unfold WBF in *. rewrite ins_stat in *.
  destruct c as [|[|c]]; [| |destruct c]; destruct k as [|[|[|k]]]; try destruct k; cbn in A |- *; discriminate.
Qed.

Definition H0 : cell -> hist := fun _ => [].

Lemma WBF_wbP : exists s0, run WBF s0 /\ exists s', step WBF s0 s' /\ partskip s0 s' 0 1 4 /\
  ((forall z, wc (wbst s' 0 1 4 H0) 1 z -> z = 1 \/ wc (wbst s' 0 1 4 H0) 4 z) \/
   (fa WBF 1 1 /\ fa WBF 0 1)).
Proof.
  apply startV2.
  eapply fwdV. { M2Lit.ord 1. apply e_full. } { nwP. } nameV.
  eapply fwdV. { M2Lit.ord 1. ST. W0. } { nwP. } nameV.
  eapply fwdV. { M2Lit.ord 1. apply e_full. } { nwP. } nameV.
  eapply fwdV. { M2Lit.ord 0. apply e_full. } { nwP. } nameV.
  eapply fwdV. { cread 0 1 [0] 1. LD (Some 1). vis_some. } { nwK. } nameV.
  eapply fwdV. { cfailH 0 1 1 3. } { nwF. } nameV.
  finV. intros RM RA.
  match goal with |- exists s', step WBF ?S s' /\ _ => set (sB := S) in * end.
  eexists. split; [qA ltac:(skipF 0)|].
  match goal with |- partskip _ ?S _ _ _ /\ _ => set (s' := S) end.
  assert (St : step WBF sB s') by (qA ltac:(skipF 0)).
  assert (P : partskip sB s' 0 1 4).
  { unfold partskip, nowrite. split; [intros x; vm_compute; reflexivity|].
    do 7 (split; [vm_compute; reflexivity|]). vm_compute; reflexivity. }
  split; [exact P|].
  destruct (self_image WBF (fun _ => True) sB WBF_wf RA) as [Rl K].
  pose proof (Q_in_WB WBF sB RA) as RW.
  assert (EV : evok sB).
  { apply (evok_time _ _ RM); [et_hist|refine (newer_dec _ _); vm_compute; reflexivity
                                    |refine (po_dec _ _); vm_compute; reflexivity]. }
  destruct (drf_prefix_dq WBF sB WBF_wf WBF_cellful WBF_race_free RA EV) as (l & g & B1 & B2 & B3 & B4 & B5).
  assert (Eu : exists eu, ent sB 1 = Some eu) by (eexists; vm_compute; reflexivity). destruct Eu as (eu & Eu).
  assert (Pe : option_map (fun e => (ec e, ek e, ew e)) (ent sB 1) = Some (1, 1, true)) by (vm_compute; reflexivity).
  rewrite Eu in Pe. cbn in Pe.
  assert (Ce : ec eu = 1) by congruence. assert (Ke : ek eu = 1) by congruence. assert (We : ew eu = true) by congruence.
  assert (Fr : forall y, ~ In 4 (ids (hs sB y))).
  { intros y. destruct y as [|y]; vm_compute; intuition lia. }
  destruct (wbc_wbP WBF False (fun _ => True) sw0 sB sB l g s' 0 1 4 H0 0 1 eu WBF_wf WBF_cellful WBF_race_free RA EV Rl K
     (WK_run WBF WBF_wf sB RW) (conj B1 (conj B2 (conj B3 (conj B4 B5)))) St P Fr
     ltac:(vm_compute; auto) Eu We ltac:(vm_compute; auto)) as [H|(_ & F1 & F2)].
  - left. exact H.
  - right. rewrite Ce, Ke in F1. auto.
Qed.

(* a write-back that stands for a store: WBF with the store first and the CAS's failure written
   back when its context passes it (id 4, right after the store 1 it read); the image of runWBK;
   stands_for_kept *)
(* a step of M2DQ before any write-back store: every history flag is false *)
Ltac wAF t := eapply wbA; [qA t|apply flagsF_fhsafe; let x := fresh "x" in let w := fresh "w" in let b := fresh "b" in
  intros x w b; destruct x; vm_compute; intuition congruence].

Definition WBF_H (x : cell) : hist := if Nat.eqb x 0 then [(1, false); (4, true)] else [].

Lemma WBF_stands : exists s, runWB WBF s /\ hs s 0 = [(1, false); (4, true)] /\
  exists sw sA f, run WBF sA /\ rel sw s sA /\ sw 4 = Some f /\ f 0 = Some 1 /\
    In (1, false) (hs s 0) /\ exists eu, ent s 1 = Some eu /\ ew eu = true.
Proof.
  apply wstart.
  eapply wfwd. { wAF ltac:(M2Lit.ord 1; apply e_full). } nameW.
  eapply wfwd. { wAF ltac:(M2Lit.ord 1; ST; W0). } nameW.
  eapply wfwd. { wAF ltac:(M2Lit.ord 1; apply e_full). } nameW.
  eapply wfwd. { wAF ltac:(M2Lit.ord 0; apply e_full). } nameW.
  eapply wfwd. { wAF ltac:(cread 0 1 [0] 1; LD (Some 1); vis_some). } nameW.
  eapply wfwd. { wAF ltac:(cfailH 0 1 1 3). } nameW.
  eapply wfwd.
  { eapply (wbP _ _ _ 0 1 4 WBF_H).
    - qA ltac:(skipF 0).
    - unfold partskip, nowrite. split; [intros x; vm_compute; reflexivity|].
      do 7 (split; [vm_compute; reflexivity|]). vm_compute; reflexivity.
    - intros y. destruct y as [|y]; vm_compute; intuition lia.
    - match goal with |- wbok ?S _ _ _ _ => set (s' := S) end. unfold wbok.
      replace (icells (ai (cs s' 0) 1)) with [0] by (vm_compute; reflexivity).
      intros x. split.
      + intros [<-|[]]. vm_compute. exists [(1, false)], []. split; [reflexivity|].
        split; [exists [], false; reflexivity|]. split; [intros w g h' E; discriminate|reflexivity].
      + intros Nx. unfold WBF_H. destruct x as [|x]; [exfalso; apply Nx; left; reflexivity|vm_compute; reflexivity]. }
  nameW.
  wfin. intros RW. split; [vm_compute; reflexivity|].
  match goal with |- exists sw sA f, run WBF sA /\ rel sw ?S sA /\ _ => set (sF := S) in * end.
  destruct (runWBK WBF WBF_wf False (fun _ => True) sF RW (fun F => False_ind _ F) (fun F => False_ind _ F))
    as (sw & sA & RA & Rl & K).
  assert (Iw : In (4, true) (hs sF 0)) by (vm_compute; auto).
  destruct (w_bet False (fun _ => True) sw sF sA K 0 4 Iw) as (f & Sw & Sg).
  assert (F0 : f 0 = Some 1).
  { assert (Hh : hs sF 0 = [(1, false); (4, true)]) by (vm_compute; reflexivity). rewrite Hh in Sg.
    destruct (f 0) as [u|] eqn:E.
    - destruct Sg as (h0 & h1 & h2 & Eh & _). destruct h0 as [|a h0]; [injection Eh as -> _; reflexivity|].
      injection Eh as _ Eh. destruct h0 as [|b h0]; [destruct h1; discriminate|].
      injection Eh as _ Eh. destruct h0; discriminate.
    - destruct Sg as (h1 & h2 & Eh & Al). destruct h1 as [|a h1]; [discriminate|].
      injection Eh as Ea _. subst a. inversion Al as [|? ? Hb _]. discriminate. }
  exists sw, sA, f. split; [exact RA|]. split; [exact Rl|]. split; [exact Sw|]. split; [exact F0|].
  exact (stands_for_kept WBF False (fun _ => True) sw sF sA 0 4 f 1 RA Rl K Iw Sw F0).
Qed.

Lemma stands_kept_inst : In (1, false) [(1, false); (5, true)] /\ seg [(1, false); (5, true)] 5 (Some 1).
Proof. split; [left; reflexivity|]. exists [], [], []. split; [reflexivity|constructor]. Qed.
Lemma stands_kept_use : In (1, false) [(1, false); (5, true)].
Proof. exact (stands_kept _ 5 1 (proj2 stands_kept_inst)). Qed.

Print Assumptions WBF_wbP.
Print Assumptions WBF_stands.
