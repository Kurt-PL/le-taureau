(* Part 63: race-freedom at an access taken in order, keeping the guard() pair
   (sync_ord2 / sync_ord_all2: M2DQWBK28.wbc_sync_ord / wbc_ord with the guard() events and their
   times as the conclusion instead of what they imply for wc). *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO M2SC M2SCx MIPComp MIPNeg M2Iface MIPSync MIBase MIPDrf.
Require Import M2IfaceInst M2DQIfaceInst M2WBRel M2DQWB M2DQWBK1 M2DQWBK3 M2DQWBK15 M2DQWBK22 M2DQWBK26 M2DQWBK27 M2DQWBK28.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

Theorem sync_ord2 : forall p Fk Good sw s0 sA0 l g u eu x d c2,
  wf p -> race_free_g p -> run p sA0 -> rel sw s0 sA0 -> KR Fk Good sw s0 sA0 -> WK s0 ->
  srun p l g -> (forall c, sp g c = pcs sA0 c) -> (forall c j, j < pcs sA0 c -> sr g c j = rg (cs sA0 c) j) ->
  gordS sA0 l ->
  ent s0 u = Some eu -> In (u, false) (hs s0 x) -> ec eu <> c2 -> ek eu < pcs s0 (ec eu) ->
  dof (ins p c2 (pcs s0 c2) (rg (cs s0 c2))) (rg (cs s0 c2)) = Some d -> In x (icells (inst_of d)) ->
  (exists t1 F1 t2 F2, ent s0 t1 = Some F1 /\ isFF s0 t1 F1 /\ ec F1 = ec eu /\ u < t1 /\
     ent s0 t2 = Some F2 /\ isFF s0 t2 F2 /\ ec F2 = c2 /\ t1 < t2) \/ (fa p (ec eu) (ek eu) /\ fa p c2 (pcs s0 c2)).
Proof.
  intros p Fk Good sw s0 sA0 l g u eu x d c2 W RF RA Rl K Wk Sl Sp Sr Go Eu Iu Nc Lu Dd Id.
  pose proof (proj2 (reach_runQ p sA0) RA) as R.
  (* u in the image *)
  assert (IuA : In u (ids (hs sA0 x))).
  { rewrite (r_hs sw s0 sA0 Rl x). apply (in_ids_of _ u false). apply in_hers. auto. }
  destruct (hist_ev p sA0 l g W RA Sl Sp Sr x u IuA) as (EY & AY & WY & HY & OY & Ev).
  destruct (k_ent Fk Good sw s0 sA0 K u EY AY) as (eu' & Eu' & (_ & S2 & S3 & _ & _ & _ & _ & _ & _ & S10)).
  rewrite Eu in Eu'. injection Eu' as <-.
  assert (Ewu : ew eu = true) by (rewrite (S10 (proj1 (r_kept sw s0 sA0 Rl x u Iu))); exact WY).
  assert (LpA : ek EY < pcs sA0 (ec EY)) by (rewrite (r_pcs sw s0 sA0 Rl), S2, S3; exact Lu).
  destruct (Ev LpA) as (q1 & e1 & Q1 & X1 & K1 & Wx & Bt1).
  destruct (wx_sacc e1 x Wx) as (ys & A1 & Iy).
  (* the next instruction of c2, read under the interleaving's registers *)
  assert (Spc : sp g c2 = pcs s0 c2) by (rewrite Sp, (r_pcs sw s0 sA0 Rl); reflexivity).
  destruct (crel_eq p Fk Good sw s0 sA0 RA Rl K c2) as (_ & _ & _ & Rg2 & _).
  assert (Ag : forall j, j < pcs s0 c2 -> sr g c2 j = rg (cs s0 c2) j).
  { intros j Lj. rewrite <- Rg2. apply Sr. rewrite (r_pcs sw s0 sA0 Rl). exact Lj. }
  destruct (W c2 (pcs s0 c2) (sr g c2) (rg (cs s0 c2)) Ag) as [Ei Ee].
  assert (Dg : dof (ins p c2 (sp g c2) (sr g c2)) (sr g c2) = Some d).
  { rewrite Spc, Ei. rewrite Ei in Ee. rewrite (dof_ieval _ _ _ Ee). exact Dd. }
  assert (Fa : forall c j, j < sp g c -> j < pcs sA0 c -> sr g c j = MIPComp.rrg sA0 c j)
    by (intros c j _ L; apply Sr; exact L).
  assert (AllP : forall q e, nth_error l q = Some e -> sk e < pcs sA0 (sx e)).
  { intros q e Q. rewrite <- Sp. apply (proj2 (srun_pos p W l g Sl (sx e) (sk e))). eauto. }
  assert (N1 : sx e1 <> c2) by (rewrite X1, S2; exact Nc).
  destruct (next_sync (IFM := dqmodel) p sA0 R W l g Sl Fa AllP Go RF (fun _ _ => true) q1 e1 ys c2 d x Q1 A1 Iy N1 Dg Id)
    as [(k1 & k2 & F1 & F2 & _ & P1 & (EF1 & C1 & D1) & I1 & _ & O1 & P2 & (EF2 & C2 & D2) & I2 & _ & O2 & T1 & T2 & _)|[Fa1 Fa2]].
  - left. rewrite Bt1 in T1.
    destruct (isFF_AW p Fk Good sw s0 sA0 RA Rl K _ _ _ F1 EF1 C1 D1 I1 P1 O1) as (G1 & EG1 & FF1 & GC1 & _).
    destruct (isFF_AW p Fk Good sw s0 sA0 RA Rl K _ _ _ F2 EF2 C2 D2 I2 P2 O2) as (G2 & EG2 & FF2 & GC2 & _).
    exists (MIPComp.bt sA0 (sx e1) k1), G1, (MIPComp.bt sA0 c2 k2), G2.
    split; [exact EG1|]. split; [exact FF1|]. split; [congruence|]. split; [exact T1|].
    split; [exact EG2|]. split; [exact FF2|]. split; [congruence|exact T2].
  - right. rewrite X1, K1, S2, S3 in Fa1. rewrite Spc in Fa2. auto.
Qed.

Theorem sync_ord_all2 : forall p Fk Good sw s0 sA0 l g u eu x d c2,
  wf p -> cellful p -> race_free_g p -> run p sA0 -> evok sA0 -> rel sw s0 sA0 -> KR Fk Good sw s0 sA0 -> WK s0 ->
  base p sA0 l g ->
  ent s0 u = Some eu -> In (u, false) (hs s0 x) -> ec eu <> c2 ->
  dof (ins p c2 (pcs s0 c2) (rg (cs s0 c2))) (rg (cs s0 c2)) = Some d -> In x (icells (inst_of d)) ->
  (exists t1 F1 t2 F2, ent s0 t1 = Some F1 /\ isFF s0 t1 F1 /\ ec F1 = ec eu /\ u < t1 /\
     ent s0 t2 = Some F2 /\ isFF s0 t2 F2 /\ ec F2 = c2 /\ t1 < t2) \/
  (fa p (ec eu) (ek eu) /\ ek eu < pcs s0 (ec eu) /\ fa p c2 (pcs s0 c2)).
Proof.
  intros p Fk Good sw s0 sA0 l g u eu x d c2 W Wc RF RA EV Rl K Wk B Eu Iu Nc Dd Id.
  pose proof B as (Sl & Sp & Sr & Go & _).
  destruct (Nat.lt_ge_cases (ek eu) (pcs s0 (ec eu))) as [Lu|Gu].
  - destruct (sync_ord2 p Fk Good sw s0 sA0 l g u eu x d c2 W RF RA Rl K Wk Sl Sp Sr Go Eu Iu Nc Lu Dd Id) as [H|[F1 F2]];
      [left; exact H|right; auto].
  - exfalso. pose proof (proj2 (reach_runQ p sA0) RA) as R.
    assert (IuA : In u (ids (hs sA0 x))).
    { rewrite (r_hs sw s0 sA0 Rl x). apply (in_ids_of _ u false). apply in_hers. auto. }
    pose proof (I1g (M := dqmodel) p sA0 R) as I. pose proof (I2g (M := dqmodel) p sA0 R) as J.
    destruct (j_hist p sA0 J x u IuA) as (EY & iy & AY & WY & EIY & ICY).
    destruct (i_et p sA0 I u EY AY) as (_ & OY).
    assert (EhY : eh EY = false) by (destruct (j_ew p sA0 J _ EY _ AY eq_refl) as [W1 _]; rewrite WY in W1; destruct (eh EY); [discriminate|reflexivity]).
    rewrite EhY in OY.
    destruct (k_ent Fk Good sw s0 sA0 K u EY AY) as (eu' & Eu' & (_ & S2 & S3 & _)).
    rewrite Eu in Eu'. injection Eu' as <-.
    assert (Spc : sp g c2 = pcs s0 c2) by (rewrite Sp, (r_pcs sw s0 sA0 Rl); reflexivity).
    destruct (crel_eq p Fk Good sw s0 sA0 RA Rl K c2) as (_ & _ & _ & Rg2 & _).
    assert (Ag : forall j, j < pcs s0 c2 -> sr g c2 j = rg (cs s0 c2) j).
    { intros j Lj. rewrite <- Rg2. apply Sr. rewrite (r_pcs sw s0 sA0 Rl). exact Lj. }
    destruct (W c2 (pcs s0 c2) (sr g c2) (rg (cs s0 c2)) Ag) as [Ei Ee].
    assert (Dg : dof (ins p c2 (sp g c2) (sr g c2)) (sr g c2) = Some d).
    { rewrite Spc, Ei. rewrite Ei in Ee. rewrite (dof_ieval _ _ _ Ee). exact Dd. }
    destruct (reach_gtrace (IFM := dqmodel) p sA0 R) as (f & n & T & Ef).
    assert (Pend : RACY p).
    { subst sA0. apply (g_pending_source p _ (GG (Model := dqmodel) p) W Wc f n T EV l g B c2 d x u EY Dg Id AY WY
        ltac:(rewrite EIY; exact ICY) ltac:(rewrite S2; exact Nc) OY).
      rewrite (r_pcs sw s0 (f n) Rl), S2, S3. exact Gu. }
    destruct Pend as (l' & g' & Sl' & Rc). exact (RF l' g' Sl' Rc).
Qed.


Print Assumptions sync_ord_all2.
