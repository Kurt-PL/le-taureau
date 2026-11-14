(* Model2 litmus, one instance per file: LBCW. *)
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

(* LBCW: r0 = z; r1 = cas(x, 0, 1); x = 2 || r2 = x; z = r2
   with r0 = r2 = 2, the CAS succeeding (r1 = 0), final x = 2 *)
Definition LBCW : prog := stat [ [ld 2; cas 0 0 1; st 0 2]; [ld 0; ISt Plain [2] T (RG 0)] ].
Lemma LBCW_allowed : exists s, run LBCW s /\ done LBCW s /\ evok s /\
  rg (cs s 0) 0 = 2 /\ vv (rg (cs s 0) 1) = 0 /\ rg (cs s 1) 0 = 2 /\ final s 0 = 2.
Proof.
  apply start.
  eapply fwd. { early 0 1 (DCas Plain [0] 0 1) 1.
    eapply (e_cas_ok1 _ _ _ _ _ _ _ _ None); [reflexivity|vis_none|vm_compute; reflexivity|W0]. } nameS.
  eapply fwd. { early 0 2 (DSt Plain [0] 2) 2. ST. enter_at [(0, false)] (@nil (nat * bool)). } nameS.
  eapply fwd. { ord 1. LD (Some 1). vis_some. } nameS.
  eapply fwd. { ord 1. ST. W0. } nameS.
  eapply fwd. { ord 0. LD (Some 3). vis_some. } nameS.
  eapply fwd. { mtch 0 (DCas Plain [0] 0 1). } nameS.
  eapply fwd. { mtch 0 (DSt Plain [0] 2). } nameS.
  finish. split; [done_tac|split; [evok_tac [0;1;2;3;4]|repeat split; reflexivity]].
Qed.

