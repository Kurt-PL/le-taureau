(* Write-back over M2DQ: the predicates of part 1 do not see a record fix (rfx). *)
From Stdlib Require Import Arith Lia List Bool Relations.
Require Import M2Model M2Inv M2DQWBQ M2DQWBK1.

Lemma isFF_rfx : forall s s', rfx s s' -> forall t g, isFF s' t g <-> isFF s t g.
Proof. intros s s' RF t g. unfold isFF. rfx_rw RF. reflexivity. Qed.

Lemma LFB_rfx : forall s s', rfx s s' -> forall c t, LFB s' c t <-> LFB s c t.
Proof.
  intros s s' RF c t. unfold LFB, ent. rfx_rw RF.
  split; intros (tg & g & A & B & C & D & F); exists tg, g; rewrite ?(isFF_rfx s s' RF) in *; auto.
Qed.
