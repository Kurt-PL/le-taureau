(* Model2, a CAS in two parts, allowed: CASDEP. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Lit M2Ev M2EvLit M2Oota M2CasSplitProof.

(* CASDEP: r0 = y; r1 = CAS(x, 7, r0); z = r1 || r = z; y = r || x = 7
   with r0 = r1 = 7. The CAS's new value depends on r0, so the CAS cannot
   happen early in one step; its read can, and z = r1 follows it. *)
Definition CASDEP : prog := stat
  [ [ld 1; ICas Plain [0] T (K 7) (RG 0); ISt Plain [2] T (fun r => vv (r 1))];
    [ld 2; ISt Plain [1] T (RG 0)];
    [st 0 7] ].

Lemma CASDEP_allowed : exists s, run CASDEP s /\ done CASDEP s /\ evok s /\
  rg (cs s 0) 0 = 7 /\ vv (rg (cs s 0) 1) = 7.
Proof.
  apply start.
  eapply fwd. { ord 2. ST. W0. } nameS.
  eapply fwd. { cread 0 1 [0] 1. LD (Some 0). vis_some. } nameS.
  eapply fwd. { earlyH 0 2 (DSt Plain [2] 7) 2. ST. W0. } nameS.
  eapply fwd. { ord 1. LD (Some 2). vis_some. } nameS.
  eapply fwd. { ord 1. ST. W0. } nameS.
  eapply fwd. { ordH 0. LD (Some 4). vis_some. } nameS.
  eapply fwd. { cw 0. eapply (e_cas_ok1 _ _ _ _ _ _ _ _ (Some 0));
    [reflexivity|vis_some|vm_compute; reflexivity|enter_at [(0, false)] (@nil (nat * bool))]. } nameS.
  eapply fwd. { mtchH 0 (DSt Plain [2] 7). } nameS.
  finish. split; [done_tac|split; [evok_tac [0;1;2;3;4;5;6]|split; reflexivity]].
Qed.

