(* Model2, a CAS in two parts, allowed: CASPDEP. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Lit M2Ev M2EvLit M2Oota M2CasSplitProof M2EvTimeProof.

(* CASPDEP: r0 = y; r1 = CAS((x, w), (7, 7), (r0, r0)); z = r1 || r = z; y = r || (x, w) = (7, 7)
   with r0 = r1 = (7, 7): a two-cell CAS's read happens alone, as one read *)
Definition V77 : val := enc [7; 7].
Definition CASPDEP : prog := stat
  [ [ld 1; ICas Plain [0; 3] T (K V77) (fun r => enc [r 0; r 0]); ISt Plain [2] T (fun r => vv (r 1))];
    [ld 2; ISt Plain [1] T (RG 0)];
    [ISt Plain [0; 3] T (K V77)] ].

(* detH with each settled register rewritten by its own instance of the
   settled premise (rewriting by the premise itself unifies its pattern with
   every subterm of the computed goal) *)
Local Ltac detH := let r := fresh "r" in let Hs := fresh "Hs" in
  intros r Hs; split; [vm_compute; reflexivity|]; vm_compute;
  first [ reflexivity
        | repeat match goal with |- context [r ?j] =>
            let H0 := fresh in
            assert (H0 := Hs j ltac:(first [left; vm_compute; lia
                                           | right; let Z := fresh in intro Z; vm_compute in Z; discriminate]));
            rewrite H0; clear H0 end;
          vm_compute; reflexivity ].
Local Ltac cw c := eapply (s_cw _ _ c);
  [vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; reflexivity
  |vm_compute; reflexivity|detH|pend_tac|hblk_ne|vm_compute; reflexivity| |reflexivity|fx_tac].

Lemma CASPDEP_allowed : exists s, run CASPDEP s /\ done CASPDEP s /\ evok s /\
  rg (cs s 0) 0 = V77 /\ vv (rg (cs s 0) 1) = V77.
Proof.
  apply startR.
  eapply fwd. { ord 2. eapply (e_st2 _ _ 0 3); [lia|reflexivity|W0|W0]. } nameS.
  eapply fwd. { cread 0 1 [0; 3] 1. eapply (e_ld2 _ _ 0 3 _ _ _ (Some 0) (Some 0)); [lia|reflexivity|vis_some|vis_some]. } nameS.
  eapply fwd. { earlyH 0 2 (DSt Plain [2] V77) 2. ST. W0. } nameS.
  eapply fwd. { ord 1. LD (Some 2). vis_some. } nameS.
  eapply fwd. { ord 1. ST. W0. } nameS.
  eapply fwd. { ordH 0. LD (Some 4). vis_some. } nameS.
  eapply fwd. { cw 0. eapply (e_cas_ok2 _ _ 0 3 _ _ _ _ _ (Some 0) (Some 0));
    [lia|reflexivity|vis_some|vis_some|vm_compute; reflexivity
    |enter_at [(0, false)] (@nil (nat * bool))|enter_at [(0, false)] (@nil (nat * bool))]. } nameS.
  eapply fwd. { mtchH 0 (DSt Plain [2] V77). } nameS.
  finish. intros RUN. split; [done_tp_tac RUN|split; [evok_time_tac RUN|split; reflexivity]].
Qed.

