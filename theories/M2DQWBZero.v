(* Zero-size accesses in M2DQ.
   M2DQ's convention (M2Inv.cellful, comment there): an access of a zero-size referent covers no
   cell, and is modelled as INop.  A load of no cell is not tied to a load of a cell
   (lzp_not_tied), and an access of no cell does not meet M2Inv.cellful (LZP_not_cellful). *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Inv M2Lit.

(* the load of no cell *)
Definition lzp : instr := ILd Plain [] (fun _ => true).

(* a load of no cell is not tied to a load of a cell, on either side *)
Theorem lzp_not_tied : ~ tied lzp (ILd Plain [0] (fun _ => true)) /\ ~ tied (ILd Plain [0] (fun _ => true)) lzp.
Proof.
  split; intros H; unfold tied in H; cbn in H;
    repeat match goal with
           | H : _ \/ _ |- _ => destruct H as [H|H]
           | H : _ /\ _ |- _ => destruct H as [? H]
           | H : exists _, _ |- _ => destruct H as [? H]
           end; try discriminate; try contradiction; try (destruct H; discriminate).
Qed.

Definition LZP : prog := stat [[lzp]].

(* an access of no cell is not cellful *)
Lemma LZP_not_cellful : ~ cellful LZP.
Proof.
  intros H. specialize (H 0 0 (fun _ => 0)). unfold LZP in H; rewrite ins_stat in H; cbn in H.
  apply H; reflexivity.
Qed.
