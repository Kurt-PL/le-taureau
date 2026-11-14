(* Model2, S3c, tools and programmes: a CAS whose read is led fixes its result
   before its read half, and a later read it leads knows its result.
     CASLBW: r0 = f; x = r0; x = 1; r3 = CAS(x, 1, 7); r4 = x; z = r4  ||  r1 = z; f = r1
   - CASLBW_succ: r0 = 7, the CAS reads 1 and succeeds, r4 = r1 = 7;
   - CASLBW_fail: r0 = 1, the CAS reads 1 and fails, r4 = r1 = 1.
     CASBIND3 (the mirror's CASBIND): r0 = x; x = 1; c = CAS(x, 9, 9); v = x; y = v  ||  r1 = y; x = r1
   - CASBIND3_allowed: r0 = 1, the CAS reads 1 and fails, v = 1, r1 = 1, final x = 1, y = 1. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Lit M2Ev M2EvLit.

Ltac W0 := enter_at (@nil (nat * bool)) (@nil (nat * bool)).
Ltac LD u := eapply (e_ld1 _ _ _ _ _ _ u); [reflexivity|].
Ltac ST := eapply e_st1; [reflexivity|].
Definition cas (x : cell) (e n : val) := ICas Plain [x] T (K e) (K n).

Ltac nameS := match goal with |- exists t, star _ ?S t /\ _ =>
  let s := fresh "s" in set (s := S) end.

(* a read counted on takes its binder's write *)
Ltac bnd2_tac := let x := fresh "x" in let b := fresh "b" in let Hx := fresh "Hx" in let H := fresh "H" in
  intros x b _ Hx H; vm_compute in Hx; destruct Hx as [<-|[]]; vm_compute in H; injection H as <-;
  vm_compute; reflexivity.
(* in order, with the reads counted on and the results fixed *)
Ltac ordX c := eapply (s_ord _ _ c);
  [vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; reflexivity|det_tac|blk_tac|hblk_tac
  |first [bnd_tac|shelve]| |].
(* an early access that is no CAS: no result fixed concerns it *)
Ltac fxs_tac := let f := fresh "f" in let j := fresh "j" in let F := fresh "F" in let b := fresh "b" in
  let E := fresh "E" in let Ci := fresh "Ci" in intros f j F b E Ci; vm_compute in Ci; discriminate Ci.
(* an early store whose value R1 knows through the reads B counts on *)
Ltac earlyB c k d j B := eapply (s_early _ _ c k d B);
  [vm_compute; lia|vm_compute; reflexivity|vm_compute; reflexivity|slot_tac
  |let f := fresh "f" in intros f; cbv zeta; exists j; split; [vm_compute; lia|];
   split; [fat_tac|let X := fresh "X" in intros X; discriminate X]
  | |fxs_tac].
(* S3c: the CAS at place j fixes its result b, its read led by the reads B
   counted on, the value it takes v *)
Ltac cfix c j b B v := eapply (s_cfix _ _ c j b B);
  [vm_compute; lia|vm_compute; reflexivity
  |exists v; let f := fresh "f" in intros f; cbv zeta; vm_compute; bitsplit;
   repeat split; first [reflexivity|let k := fresh "k" in let E := fresh "E" in intros k E; discriminate E
                       |let E := fresh "E" in intros E; first [reflexivity|discriminate E]]].

(* ---------- CASLBW ---------- *)
Definition CASLBW : prog := stat
  [ [ld 3; ISt Plain [0] T (RG 0); st 0 1; cas 0 1 7; ld 0; ISt Plain [2] T (RG 4)];
    [ld 2; ISt Plain [3] T (RG 0)] ].

(* ---------- CASBIND (the mirror suite's) ---------- *)
Definition CASBIND3 : prog := stat
  [ [ld 0; st 0 1; cas 0 9 9; ld 0; ISt Plain [1] T (RG 3)]; [ld 1; ISt Plain [0] T (RG 0)] ].

