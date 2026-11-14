(* Model2, light fences that may happen early: guard.rs() orders a store
   after earlier stores and fences, and carries to it only its context's own
   writes; guard.rl() orders only later loads and fences; a light fence may
   happen early under R1. Outcomes this allows. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Lit M2Ev M2EvLit M2Acyc M2Timeline2.

Ltac W0 := enter_at (@nil (nat * bool)) (@nil (nat * bool)).
Ltac LD u := eapply (e_ld1 _ _ _ _ _ _ u); [reflexivity|].
Ltac ST := eapply e_st1; [reflexivity|].

Definition cas (x : cell) (e n : val) := ICas Plain [x] T (K e) (K n).

(* knowledge views decomposed, keeping what each case fixes *)
Ltac kn2' H :=
  match type of H with
  | _ \/ _ => let H1 := fresh "H" in destruct H as [H1|H1]; kn2' H1
  | False => destruct H
  | exists _, _ => let z := fresh "z" in let H1 := fresh "H" in destruct H as [z H1]; kn2' H1
  | _ /\ _ => let H1 := fresh "H" in let H2 := fresh "H" in destruct H as [H1 H2]; kn2' H1; kn2' H2
  | context [if ?b then _ else _] =>
      let E := fresh "E" in destruct b eqn:E;
      try (apply Nat.eqb_eq in E; subst); vm_compute in H; kn2' H
  | Some _ = Some _ => injection H as H; try subst; try kn2' H
  | None = Some _ => discriminate H
  | Some _ = None => discriminate H
  | ?a = ?b => try subst; try discriminate
  | _ => idtac
  end.

Ltac ev_cedge3 :=
  let x := fresh "x" in let a := fresh "a" in let b := fresh "b" in let E := fresh "E" in
  let O := fresh "O" in let e := fresh "e" in let e2 := fresh "e" in
  let L := fresh "L" in let L2 := fresh "L" in let Ix := fresh "Ix" in let Ib := fresh "Ib" in
  let N := fresh "N" in let M := fresh "M" in let Q := fresh "Q" in let C := fresh "C" in let K := fresh "K" in
  intros x a b E;
  destruct E as [O|[(e & L & Ix & Ib & N & M)|[(e & L & Ix & M & N)|[(e & L & Ix & Q & Ib & N)|(e & e2 & L & L2 & C & K & Ix & Ib)]]]];
  [ apply older_pairs in O; cell4 x; inlist O; try (injection O as <- <-); rk_close
  | at_ent L a; inlist Ix; subst x; inlist Ib; subst b; vm_compute in M;
    try (apply older_b in M; vm_compute in M; discriminate); rk_close
  | at_ent L b; inlist Ix; subst x; vm_compute in M; first [discriminate M | injection M as <-]; rk_close
  | at_ent L b; inlist Ix; subst x; inlist Ib; subst a; vm_compute in Q;
    first [rk_close | (kn2' Q; try discriminate; try (exfalso; lia); try refute_neg; rk_close)]
  | at_ent L a; at_ent L2 b; vm_compute in C, K; try discriminate; try lia;
    inlist Ix; subst x; inlist Ib; rk_close ].

Ltac evok_tac3 ordg ordc := apply (evok_rank2 _ (fun a => idx a ordg) (fun a => idx a ordc)); [ev_gedge|ev_cedge3].

(* each state of a run is named, not normalised *)
Ltac nameS := match goal with |- exists t, star _ ?S t /\ _ =>
  let s := fresh "s" in set (s := S) end.

(* a lock release read back (LOCKREL):
     r0 = x; guard.rs(); y = 5 || r1 = cas(y, 5, 1); guard.rl(); x = 9
   with r0 = 9 and the CAS reading 5. The release's guard.rs() does not
   order the read before it. *)
Definition LOCKREL : prog := stat [ [ld 0; fss; st 1 5]; [cas 1 5 1; fll; st 0 9] ].
Lemma LOCKREL_allowed : exists s, run LOCKREL s /\ done LOCKREL s /\ evok s /\
  rg (cs s 0) 0 = 9 /\ vv (rg (cs s 1) 0) = 5.
Proof.
  apply start.
  eapply fwd. { early 0 1 (DFn FSs) 1. apply e_ss. } nameS.
  eapply fwd. { early 0 2 (DSt Plain [1] 5) 2. ST. W0. } nameS.
  eapply fwd. { ord 1.
    eapply (e_cas_ok1 _ _ _ _ _ _ _ _ (Some 1)); [reflexivity|vis_some|vm_compute; reflexivity|enter_at [(1, false)] (@nil (nat * bool))]. } nameS.
  eapply fwd. { ord 1. apply e_ll. } nameS.
  eapply fwd. { ord 1. ST. W0. } nameS.
  eapply fwd. { ord 0. LD (Some 4). vis_some. } nameS.
  eapply fwd. { mtch 0 (DFn FSs). } nameS.
  eapply fwd. { mtch 0 (DSt Plain [1] 5). } nameS.
  finish. split; [done_tac|split; [evok_tac3 [0;1;2;3;4;5] [0;1;2;3;4;5]|repeat split; reflexivity]].
Qed.

