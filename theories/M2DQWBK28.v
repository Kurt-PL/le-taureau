(* Part 28: (WBC'') at a CAS taken in order, from race-freedom (in-order case, u passed).  The state s0 is a write-back state before the step, sA0 an A image of it
   (rel, structural part of KR), and l an interleaving of sA0's passed slots (MIPSync.WIT).  Let the
   next instruction of context c2 be an access covering x, and let u be a store of another context
   c1 in x's history, not written back, at a passed slot.  Then (wbc_sync_ord):
     - u conveys at most u and what c2 releases now: wc u <= {u} u vR(c2)  (a write-back of that
       CAS conveys vR(c2) u {itself}, and vR only grows, M2DQWBK20.vmono); or
     - u and the access are both fenced (fa), the case of M2DQWBK24.fa_wc.
   Chain: M2DQWBK27.next_sync (race_free_g on l plus the next step), then the guard() pair is a
   pair of guard() events of s0 (M2DQWBK26.isFF_AW), then WK s0: wk_ug, wk_gg, wk_Rg. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO M2SC M2SCx MIPComp MIPNeg M2Iface MIPSync MIBase MIPDrf.
Require Import M2IfaceInst M2DQIfaceInst M2WBRel M2DQWB M2DQWBK1 M2DQWBK3 M2DQWBK15 M2DQWBK22 M2DQWBK26 M2DQWBK27.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

Lemma dof_ieval : forall i r r', ieval i r = ieval i r' -> dof i r = dof i r'.
Proof.
  intros [m xs c|m xs c v|m xs c e n|f|] r r' H; cbn in H |- *; try reflexivity.
  - injection H as H1. rewrite H1. reflexivity.
  - injection H as H1 H2. rewrite H1, H2. reflexivity.
  - injection H as H1 H2 H3. rewrite H1, H2, H3. reflexivity.
Qed.

(* a write of a history at a passed slot is an event of the interleaving *)
Lemma hist_ev : forall p s l g, wf p -> run p s -> srun p l g -> (forall c, sp g c = pcs s c) ->
  (forall c j, j < pcs s c -> sr g c j = rg (cs s c) j) -> forall x y, In y (ids (hs s x)) ->
  exists EY, ent s y = Some EY /\ ew EY = true /\ eh EY = false /\ oc (cs s (ec EY)) (ek EY) = Some y /\
    (ek EY < pcs s (ec EY) ->
     exists q e, nth_error l q = Some e /\ sx e = ec EY /\ sk e = ek EY /\ writes_x e x = true /\
       MIPComp.bt s (sx e) (sk e) = y).
Proof.
  intros p s l g W RA Rl Sp Sr x y Hy. pose proof (proj2 (reach_runQ p s) RA) as R.
  pose proof (I1g (M := dqmodel) p s R) as I. pose proof (I2g (M := dqmodel) p s R) as J.
  destruct (j_hist p s J x y Hy) as (EY & iy & AY & WY & EIY & ICY).
  destruct (i_et p s I y EY AY) as (_ & OY).
  assert (EhY : eh EY = false) by (destruct (j_ew p s J _ EY _ AY eq_refl) as [W1 _]; rewrite WY in W1; destruct (eh EY); [discriminate|reflexivity]).
  rewrite EhY in OY. exists EY. split; [exact AY|]. split; [exact WY|]. split; [exact EhY|]. split; [exact OY|].
  intros Lp.
  assert (REY : MIPNeg.RE s (ec EY) (ek EY) EY) by (unfold MIPNeg.RE, MIPComp.bt, tmo; rewrite OY; auto).
  destruct (lb_has_write (IFM := dqmodel) p W s R l g Rl Sp Sr (ec EY) (ek EY) EY x Lp REY WY ltac:(rewrite EIY; auto))
    as (q & e & Q & Xe & Ke & We).
  exists q, e. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. rewrite Xe, Ke. unfold MIPComp.bt, tmo. rewrite OY. reflexivity.
Qed.

Theorem wbc_sync_ord : forall p Fk Good sw s0 sA0 l g u eu x d c2,
  wf p -> race_free_g p -> run p sA0 -> rel sw s0 sA0 -> KR Fk Good sw s0 sA0 -> WK s0 ->
  srun p l g -> (forall c, sp g c = pcs sA0 c) -> (forall c j, j < pcs sA0 c -> sr g c j = rg (cs sA0 c) j) ->
  gordS sA0 l ->
  ent s0 u = Some eu -> In (u, false) (hs s0 x) -> ec eu <> c2 -> ek eu < pcs s0 (ec eu) ->
  dof (ins p c2 (pcs s0 c2) (rg (cs s0 c2))) (rg (cs s0 c2)) = Some d -> In x (icells (inst_of d)) ->
  (forall z, wc s0 u z -> z = u \/ vR (cs s0 c2) z) \/ (fa p (ec eu) (ek eu) /\ fa p c2 (pcs s0 c2)).
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
    intros z Z.
    destruct (wk_ug s0 Wk u eu _ G1 x Eu Ewu Iu EG1 FF1 ltac:(congruence) T1 z Z) as [Z1|Z1]; [|left; exact Z1].
    right. pose proof (wk_gg s0 Wk _ G1 _ G2 EG1 FF1 EG2 FF2 T2 z Z1) as Z2.
    pose proof (wk_Rg s0 Wk _ G2 EG2 FF2 z Z2) as Z3. rewrite GC2 in Z3. exact Z3.
  - right. rewrite X1, K1, S2, S3 in Fa1. rewrite Spc in Fa2. auto.
Qed.

(* the same without the premise that u's slot is passed: a store of another context still
   pending (happened early, not reached) under the next access of c2 makes the programme racy
   (M2Iface.g_pending_source), so for race-free code u's slot is passed.  Needs the image to be
   evok (the base DRF proof's premise) and l to be a base of it (MIPSync.WIT). *)
Theorem wbc_ord : forall p Fk Good sw s0 sA0 l g u eu x d c2,
  wf p -> cellful p -> race_free_g p -> run p sA0 -> evok sA0 -> rel sw s0 sA0 -> KR Fk Good sw s0 sA0 -> WK s0 ->
  base p sA0 l g ->
  ent s0 u = Some eu -> In (u, false) (hs s0 x) -> ec eu <> c2 ->
  dof (ins p c2 (pcs s0 c2) (rg (cs s0 c2))) (rg (cs s0 c2)) = Some d -> In x (icells (inst_of d)) ->
  (forall z, wc s0 u z -> z = u \/ vR (cs s0 c2) z) \/ (fa p (ec eu) (ek eu) /\ fa p c2 (pcs s0 c2)).
Proof.
  intros p Fk Good sw s0 sA0 l g u eu x d c2 W Wc RF RA EV Rl K Wk B Eu Iu Nc Dd Id.
  pose proof B as (Sl & Sp & Sr & Go & _).
  destruct (Nat.lt_ge_cases (ek eu) (pcs s0 (ec eu))) as [Lu|Gu].
  - exact (wbc_sync_ord p Fk Good sw s0 sA0 l g u eu x d c2 W RF RA Rl K Wk Sl Sp Sr Go Eu Iu Nc Lu Dd Id).
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

(* every context, c2's own stores included (wk_R: a store conveys at most its context's release
   view, which only grows) *)
Theorem wbc_ord_all : forall p Fk Good sw s0 sA0 l g u eu x d c2,
  wf p -> cellful p -> race_free_g p -> run p sA0 -> evok sA0 -> rel sw s0 sA0 -> KR Fk Good sw s0 sA0 -> WK s0 ->
  base p sA0 l g ->
  ent s0 u = Some eu -> ew eu = true -> In (u, false) (hs s0 x) ->
  dof (ins p c2 (pcs s0 c2) (rg (cs s0 c2))) (rg (cs s0 c2)) = Some d -> In x (icells (inst_of d)) ->
  (forall z, wc s0 u z -> z = u \/ vR (cs s0 c2) z) \/ (ec eu <> c2 /\ fa p (ec eu) (ek eu) /\ fa p c2 (pcs s0 c2)).
Proof.
  intros p Fk Good sw s0 sA0 l g u eu x d c2 W Wc RF RA EV Rl K Wk B Eu Ewu Iu Dd Id.
  destruct (Nat.eq_dec (ec eu) c2) as [Ec|Nc].
  - left. intros z Z. destruct (wk_R s0 Wk u eu Eu Ewu z Z) as [Z1|Z1]; [right; rewrite <- Ec; exact Z1|left; exact Z1].
  - destruct (wbc_ord p Fk Good sw s0 sA0 l g u eu x d c2 W Wc RF RA EV Rl K Wk B Eu Iu Nc Dd Id) as [H|H]; auto.
Qed.

Print Assumptions wbc_sync_ord.
Print Assumptions wbc_ord.
Print Assumptions wbc_ord_all.
