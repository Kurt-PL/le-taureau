(* Write-back over M2DQ: a record fix of M2DQ (rfx) on both sides keeps the knowledge relation KR. *)
From Stdlib Require Import Arith Lia List Bool Relations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB M2DQWBK1 M2DQWBK2 M2DQWBK3 M2DQWBQ.
Lemma KR_rfx : forall Fk Good sw sW sA sW' sA', KR Fk Good sw sW sA -> rfx sW sW' -> rfx sA sA' -> KR Fk Good sw sW' sA'.
Proof.
  intros Fk Good sw sW sA sW' sA' K RW RA.
  destruct K as [K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16].
  constructor.
  14: { intros c j t1 O S. rewrite (rfx_oh _ _ RW) in O. destruct (K14 c j t1 O S) as [O' [L|F]];
        rewrite (rfx_oc _ _ RW), (rfx_pcs _ _ RW); split; [exact O'|left; exact L|exact O'|right; exact (rfx_fail _ _ RW c j F)]. }
  14: { intros t f S. destruct (K15 t f S) as (e & E & C). exists e. unfold ent in *. rewrite (rfx_lg _ _ RW), (rfx_ai _ _ RW). auto. }
  all: intros; unfold ent, ksame, cov, Pth, gedge, isFF, ownw, tmo in *; rfx_rw RW; rfx_rw RA; try solve [eauto].
Qed.
