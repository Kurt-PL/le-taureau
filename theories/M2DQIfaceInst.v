(* M2DQ (stepQ) has the guarantees of M2Iface. The fields
   are M2DQIface (step by step), M2DQTrace (g_birth, g_pending_cells) and
   g_pending_source from the DRF core re-checked on M2DQ (M2DQPCore.core). *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO M2Oota M2Cont M2DQEquiv M2Snap M2SC M2SCx
  M2Trace M2DQMono M2DQPComp M2DQPNeg M2DQPSync M2DQPFix M2DQPCore M2Ev M2Timeline2 M2Iface
  M2DA M2DP M2DQ M2DQInv M2DQOota M2DQIface M2DQTrace M2DQTr M2DQShim.

Section I.
Variable p : prog.

Lemma i_pending_sourceQ : wf p -> cellful p -> forall f nb, gtrace (step p) f nb -> evok (f nb) ->
  forall lb gb, base p (f nb) lb gb ->
  forall c dh x y EY, dof (ins p c (sp gb c) (sr gb c)) (sr gb c) = Some dh -> In x (icells (inst_of dh)) ->
  ent (f nb) y = Some EY -> ew EY = true -> In x (icells (einstr p (f nb) EY)) -> ec EY <> c ->
  oc (cs (f nb) (ec EY)) (ek EY) = Some y -> pcs (f nb) (ec EY) <= ek EY ->
  RACY p.
Proof.
  intros W Wc f nb T EVb lb gb (Bsr & Bsp & Brg & Bgo & Bco) c dh x y EY Dgb Ixd AY WY IY Nc OY Gp.
  destruct (early_of_pending p f nb T nb (ec EY) (ek EY) y (le_n nb) Gp OY) as (iy & dy & By & uy & Eay & Liy & Tiy).
  destruct (pend_meet p W Wc f nb T lb gb Bsr Bsp Brg (tm (f nb)) lb gb c dh x (ec EY) (ek EY) iy dy By uy EY
              (core p W Wc f nb T lb gb Bsr Bsp Brg Bgo Bco EVb (tm (f iy))) (CONS_base p f nb lb gb Bsp Brg)
              Dgb Nc Ixd Eay Gp ltac:(rewrite Tiy; pose proof (oc_lt_tm p (f nb) _ _ _ (Inv1_run p (f nb) (tr_run p f nb T nb (le_n nb))) OY); lia)
              ltac:(rewrite Tiy; exact AY) WY IY) as (l' & g' & H' & Xr).
  - intros q e Lq Q. exfalso. assert (q < length lb) by (apply nth_error_Some; congruence). lia.
  - exists l', g'. auto.
Qed.

Theorem m2dq_guarantees : M2Guarantees p (stepQ p).
Proof.
  constructor.
  - exact (gq_slots p).
  - exact (gq_values p).
  - exact (gq_knowledge p).
  - exact (gq_in_order p).
  - exact (gq_keeps p).
  - exact (gq_rule_back p).
  - exact gq_two_level.
  - exact (gq_no_thin_air p).
  - exact (gq_slot0 p).
  - exact (gq_no_half p).
  - exact (i_birthQ p).
  - exact (i_pending_cellsQ p).
  - exact i_pending_sourceQ.
Qed.

End I.

Instance dqmodel : Model := {| STEP := stepQ; GG := m2dq_guarantees |}.

Print Assumptions m2dq_guarantees.
