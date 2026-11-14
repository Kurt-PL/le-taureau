(* Model2: R1 counting on a read taking its binder's write, with binders of
   every kind (spec wording: "the write that its context's previous access to
   the cell read or made") and a CAS's read as the read counted on. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Lit M2Ev M2EvLit.

Ltac W0 := enter_at (@nil (nat * bool)) (@nil (nat * bool)).
Ltac LD u := eapply (e_ld1 _ _ _ _ _ _ u); [reflexivity|].
Ltac ST := eapply e_st1; [reflexivity|].

Definition cas (x : cell) (e n : val) := ICas Plain [x] T (K e) (K n).
Definition PLUS1 (j : nat) : regs -> val := fun r => r j + 1.

(* an early store whose value R1 knows through the reads B counts on *)
Ltac earlyB c k d j B := eapply (s_early _ _ c k d B);
  [vm_compute; lia|vm_compute; reflexivity|vm_compute; reflexivity|slot_tac
  |let f := fresh "f" in intros f; cbv zeta; exists j; split; [vm_compute; lia|];
   split; [fat_tac|let X := fresh "X" in intros X; discriminate X]
  | |fxe_tac].

(* a read counted on takes its binder's write *)
Ltac bnd2_tac := let x := fresh "x" in let b := fresh "b" in let Hx := fresh "Hx" in let H := fresh "H" in
  intros x b _ Hx H; vm_compute in Hx; destruct Hx as [<-|[]]; vm_compute in H; injection H as <-;
  vm_compute; reflexivity.
Ltac ordB c := eapply (s_ord _ _ c); [vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; reflexivity|det_tac|blk_tac|hblk_tac|shelve| |fx_tac].

(* each state of a run is named, not normalised *)
Ltac nameS := match goal with |- exists t, star _ ?S t /\ _ =>
  let s := fresh "s" in set (s := S) end.

(* CASRFWD: r0 = x; x = 1; c = CAS(x, 1, 2); y = c || r1 = y; x = r1
   with r0 = 1, c = 1, r1 = 1: the CAS's read is counted on taking x = 1 *)
Definition CASRFWD : prog :=
  stat [ [ld 0; st 0 1; cas 0 1 2; ISt Plain [1] T (fun r => vv (r 2))]; [ld 1; ISt Plain [0] T (RG 0)] ].
Lemma CASRFWD_allowed : exists s, run CASRFWD s /\ done CASRFWD s /\ evok s /\
  rg (cs s 0) 0 = 1 /\ vv (rg (cs s 0) 2) = 1 /\ rg (cs s 1) 0 = 1.
Proof.
  apply start.
  eapply fwd. { earlyB 0 3 (DSt Plain [1] 1) 3 (fun j => Nat.eqb j 2). ST. W0. } nameS.
  eapply fwd. { ord 1. LD (Some 0). vis_some. } nameS.
  eapply fwd. { ord 1. ST. W0. } nameS.
  eapply fwd. { ord 0. LD (Some 2). vis_some. } nameS.
  eapply fwd. { ord 0. ST. enter_at [(2, false)] (@nil (nat * bool)). } nameS.
  eapply fwd. { ordB 0. eapply (e_cas_ok1 _ _ _ _ _ _ _ _ (Some 4));
    [reflexivity|vis_some|vm_compute; reflexivity|enter_at [(2, false); (4, false)] (@nil (nat * bool))]. Unshelve. bnd2_tac. } nameS.
  eapply fwd. { mtch 0 (DSt Plain [1] 1). } nameS.
  finish. split; [done_tac|split; [evok_tac [0;1;2;3;4;5]|repeat split; reflexivity]].
Qed.

