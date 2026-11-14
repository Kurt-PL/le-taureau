(* Write-back over M2DQ: evok of the state after an M2DQ step gives evok of the state before it. *)
From Stdlib Require Import Arith Lia List Bool.
Require Import M2Model M2Inv M2Ev M2DQ M2DQIface M2DQWBQ.

Lemma evok_stepQ : forall p s t, runQ p s -> stepQ p s t -> evok t -> evok s.
Proof.
  intros p s t R H E. destruct (IS_run p s R) as [I J _ _ _].
  destruct (stepQ_split p s t H) as [[St _]|RF].
  - exact (evok_st p s t I J St E).
  - exact (evok_hl s t (rfx_hs _ _ RF) (rfx_lg _ _ RF) E).
Qed.
