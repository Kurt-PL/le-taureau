(* T1 counter-run, positive half (outcome: r0 = 1, slot 1 untouched, slot 2 vd false 0, r1 = 1): in M2Model a CAS hoisted as a whole above a
   branch whose two sides CAS the same cell fails spuriously early, and a later
   store passes it before the load the branch depends on.
     SPFH: r0 = y; [r0 = 0] CAS(x, 0, 5); [r0 <> 0] CAS(x, 0, 5); x = 1  ||  r1 = x; y = r1
   SPFH_whole: done run, evok, r0 = 1, the CAS at slot 2 read 0 and failed
   (vd false 0), r1 = 1. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Lit M2Ev M2EvLit M2Oota M2CasSplitProof.

Definition SPFHc : list (list instr) :=
  [ [ld 1; ICas Plain [0] (EQ 0 0) (K 0) (K 5); ICas Plain [0] (NE 0 0) (K 0) (K 5); st 0 1];
    [ld 0; ISt Plain [1] T (RG 0)] ].
Definition SPFH : prog := stat SPFHc.

Lemma SPFH_whole : exists s, run SPFH s /\ done SPFH s /\ evok s /\
  rg (cs s 0) 0 = 1 /\ rg (cs s 0) 1 = 0 /\ rg (cs s 0) 2 = vd false 0 /\ rg (cs s 1) 0 = 1.
Proof.
  apply start.
  (* the CAS as a whole, early: its place is 1 if the free value of y is 0, else 2;
     it reads 0 and fails (spurious failure of a whole CAS) *)
  eapply fwd. { eapply (s_early _ _ 0 2 (DCas Plain [0] 0 5) (fun _ => false));
    [vm_compute; lia|vm_compute; reflexivity|vm_compute; reflexivity|slot_tac
    |let f := fresh "f" in let E := fresh "E" in intros f; cbv zeta; destruct (f 0 1) as [|n] eqn:E;
       [exists 1|exists 2]; (split; [vm_compute; lia|]); split;
       [fatN 3; vm_compute; rewrite ?E; vm_compute; bitsplit; reflexivity
       |let X := fresh "X" in intros X; first [discriminate X | bnd_tac]
       |fatN 3; vm_compute; rewrite ?E; vm_compute; bitsplit; reflexivity
       |let X := fresh "X" in intros X; first [discriminate X | bnd_tac]]
    | |fxe_tac].
    eapply (e_cas_no _ _ _ _ _ _ _ _ (src1 0 None)); [reflexivity|apply takes1; vis_none]. } nameS.
  (* x = 1 early: the CAS's place, whichever it is, has happened *)
  eapply fwd. { eapply (s_early _ _ 0 3 (DSt Plain [0] 1) (fun _ => false));
    [vm_compute; lia|vm_compute; reflexivity|vm_compute; reflexivity|slot_tac
    |let f := fresh "f" in let E := fresh "E" in intros f; cbv zeta; exists 3; split; [vm_compute; lia|]; split;
       [fatN 3; vm_compute; destruct (f 0 1) eqn:E; vm_compute; bitsplit; reflexivity
       |let X := fresh "X" in intros X; discriminate X]
    | |fxe_tac]. ST. W0. } nameS.
  eapply fwd. { ord 1. LD (Some 1). vis_some. } nameS.
  eapply fwd. { ord 1. ST. W0. } nameS.
  eapply fwd. { ord 0. LD (Some 3). vis_some. } nameS.
  eapply fwd. { skip 0. } nameS.
  eapply fwd. { mtch 0 (DCas Plain [0] 0 5). } nameS.
  eapply fwd. { mtch 0 (DSt Plain [0] 1). } nameS.
  finish. split; [done_tac|split; [evok_tac [0;1;2;3;4]|split; [reflexivity|split; [reflexivity|split; reflexivity]]]].
Qed.

Print Assumptions SPFH_whole.
