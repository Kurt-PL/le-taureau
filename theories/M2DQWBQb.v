(* Write-back over M2DQ: a record fix keeps the registers below the context's place (a failed
   record is a pending slot, M2DQ.rfail_ge; the CAS fix touches no register). *)
From Stdlib Require Import Arith Lia List Bool.
Require Import M2Model M2Inv M2Cont M2DA M2DP M2DQ M2DQWBQ.

Lemma stepQ_split_rg : forall p s s', stepQ p s s' -> (step p s s' /\ nowhole s s') \/
  (rfx s s' /\ forall c j, j < pcs s c -> rg (cs s' c) j = rg (cs s c) j).
Proof.
  intros p s s' H. destruct H as [s s' St V|s c k B Rf _|s c j k B _ _ _].
  - left. auto.
  - right. split; [apply rfx_rfix|]. pose proof (rfail_ge _ _ _ _ _ _ _ Rf) as Ge.
    intros c0 j L. unfold sbd, scfail, cc_fx, upd. cbn.
    destruct (Nat.eqb_spec c0 c) as [->|_]; cbn; [rewrite Nat.eqb_refl; cbn|reflexivity].
    destruct (Nat.eqb_spec j k) as [->|_]; [lia|reflexivity].
  - right. split; [apply rfx_sfix|]. intros c0 j0 _. unfold scfix0, upd. cbn.
    destruct (Nat.eqb_spec c0 c) as [->|_]; reflexivity.
Qed.

(* the image's runs are M2DQ runs: the constructors of run read as those of runQ *)
Notation r0 := x0 (only parsing).
Notation rS := xS (only parsing).
