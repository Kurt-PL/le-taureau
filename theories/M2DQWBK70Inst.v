(* instances of parts 68-69 (no vacuous premises).
   - FWB (M2DQWBK16: F; r0 = CAS(x, 1, 2); F  ||  F; r1 = x; F) is wf, cellful and race-free; its
     finished runWB, in which the read of context 1 (entry 4) takes the write-back store 1 (the only
     entry of x's history, flagged), is evok; M2DQWBK69.drf_sc_WB applies to it: an interleaving with
     the same next instructions, registers and final storage (FWB_G2).
   - INVF holds with its premise met on WBF's write-back run (M2DQWBK30Inst: the CAS's read half takes
     the store 1, the CAS fails in parts and writes back 4, which stands for 1): the image entry at 4 read 1
     in x (WBF_INVF); INVF fails on a pair whose sw names a store with no image entry (INVF_neg). *)
From Stdlib Require Import Arith Lia List Bool Relations PArith.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Lit M2Ev M2EvLit M2WBRel M2DQWBPatch M2DQWB.
Require Import M2DQWBK1 M2DQWBK3 M2DQWBK16 M2DQWBK23 M2DQWBK30Inst M2DQWBK37 M2DQWBK68 M2DQWBK69.
Require Import M2CasSplitProof.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

Lemma FWB_cellful : cellful FWB.
Proof.
  apply cellful_of. intros c k r A. unfold FWB in *. rewrite ins_stat in *.
  destruct c as [|[|c]]; [| |destruct c]; destruct k as [|[|[|k]]]; try destruct k; cbn in A |- *; discriminate.
Qed.

Theorem FWB_G2 : exists s, runWB FWB s /\ done FWB s /\ evok s /\ hs s 0 = [(1, true)] /\
  option_map (fun e => (ec e, erf e 0)) (ent s 4) = Some (1, Some 1) /\
  exists l g, srun FWB l g /\ (forall c, sp g c = pcs s c) /\
    (forall c j, j < pcs s c -> sr g c j = rg (cs s c) j) /\ (forall x, sm g x = final s x).
Proof.
  destruct FWB_run as (s & R & D & EV & H & E4 & _).
  exists s. split; [exact R|]. split; [exact D|]. split; [exact EV|]. split; [exact H|]. split; [exact E4|].
  exact (drf_sc_WB FWB FWB_wf FWB_cellful FWB_race_free s R D EV).
Qed.

Lemma WBF_INVF : exists s sw sA f, wch WBF False (fun _ => True) s sw sA /\ sw 4 = Some f /\ f 0 = Some 1 /\
  exists e0, ent sA 4 = Some e0 /\ erf e0 0 = Some 1.
Proof.
  assert (Hr : exists s, runWB WBF s /\ hs s 0 = [(1, false); (4, true)]).
  { apply wstart.
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
    wfin. intros RW. vm_compute; reflexivity. }
  destruct Hr as (s & RW & Hh).
  destruct (runWBK_chain WBF WBF_wf False (fun _ => True) s RW (fun F => False_ind _ F) (fun F => False_ind _ F))
    as (sw & sA & Ch).
  assert (Iw : In (4, true) (hs s 0)) by (rewrite Hh; right; left; reflexivity).
  destruct (w_bet False (fun _ => True) sw s sA (wch_KR WBF False (fun _ => True) s sw sA Ch) 0 4 Iw) as (f & Sw & Sg).
  assert (F0 : f 0 = Some 1).
  { rewrite Hh in Sg. destruct (f 0) as [u|] eqn:E.
    - destruct Sg as (h0 & h1 & h2 & Eh & _). destruct h0 as [|a h0]; [injection Eh as -> _; reflexivity|].
      injection Eh as _ Eh. destruct h0 as [|b h0]; [destruct h1; discriminate|].
      injection Eh as _ Eh. destruct h0; discriminate.
    - destruct Sg as (h1 & h2 & Eh & Al). destruct h1 as [|a h1]; [discriminate|].
      injection Eh as Ea _. subst a. inversion Al as [|? ? Hb _]. discriminate. }
  exists s, sw, sA, f. split; [exact Ch|]. split; [exact Sw|]. split; [exact F0|].
  exact (wch_INVF WBF False (fun _ => True) s sw sA Ch 4 f 0 1 Sw F0).
Qed.

Lemma INVF_neg : ~ INVF (fun w => if Nat.eqb w 0 then Some (fun _ => Some 0) else None) sinit.
Proof.
  intros H. destruct (H 0 (fun _ => Some 0) 0 0 eq_refl eq_refl) as (e0 & E & _).
  unfold ent in E. cbn in E. discriminate.
Qed.

Print Assumptions FWB_cellful.
Print Assumptions FWB_G2.
Print Assumptions WBF_INVF.
Print Assumptions INVF_neg.
