(* Model2 litmus, one instance per file: LBWC. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Lit M2Ev M2EvLit.

Definition SUB1 (j : nat) : regs -> val := fun r => r j - 1.

Ltac W0 := enter_at (@nil (nat * bool)) (@nil (nat * bool)).
Ltac LD u := eapply (e_ld1 _ _ _ _ _ _ u); [reflexivity|].
Ltac ST := eapply e_st1; [reflexivity|].
Definition cas (x : cell) (e n : val) := ICas Plain [x] T (K e) (K n).
(* each state of a run is named, not normalised *)
Ltac nameS := match goal with |- exists t, star _ ?S t /\ _ =>
  let s := fresh "s" in set (s := S) end.

(* LBWC: r0 = z; x = 1; r1 = cas(x, 1, 2) || r2 = x; z = r2
   with r0 = r2 = 2, the CAS reading its own context's x = 1 (r1 = 1), final x = 2 *)
Definition LBWC : prog := stat [ [ld 2; st 0 1; cas 0 1 2]; [ld 0; ISt Plain [2] T (RG 0)] ].
Lemma LBWC_allowed : exists s, run LBWC s /\ done LBWC s /\ evok s /\
  rg (cs s 0) 0 = 2 /\ vv (rg (cs s 0) 2) = 1 /\ rg (cs s 1) 0 = 2 /\ final s 0 = 2.
Proof.
  apply start.
  eapply fwd. { early 0 1 (DSt Plain [0] 1) 1. ST. W0. } nameS.
  eapply fwd. { early 0 2 (DCas Plain [0] 1 2) 2.
    eapply (e_cas_ok1 _ _ _ _ _ _ _ _ (Some 0)); [reflexivity|vis_some|vm_compute; reflexivity|enter_at [(0, false)] (@nil (nat * bool))]. } nameS.
  eapply fwd. { ord 1. LD (Some 1). vis_some. } nameS.
  eapply fwd. { ord 1. ST. W0. } nameS.
  eapply fwd. { ord 0. LD (Some 3). vis_some. } nameS.
  eapply fwd. { mtch 0 (DSt Plain [0] 1). } nameS.
  eapply fwd. { mtch 0 (DCas Plain [0] 1 2). } nameS.
  finish. split; [done_tac|split; [evok_tac [0;1;2;3;4]|repeat split; reflexivity]].
Qed.

