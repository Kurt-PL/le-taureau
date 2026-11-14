(* Part 33: (WBC'') at a write-back by a CAS passed in order, all cases together.
   For wbP, every kept store u in a cell of the CAS conveys, in the state after the write-back, at
   most u, what the write-back store conveys, and what guard() has published (vG):
       wc(u) <= {u} u wc(t) u vG                          (wbc_full_wbP)
   - synced case and same context: M2DQWBK30 (wc(t) = vR(c) u {t});
   - both fenced (fa): u's slot is passed (a pending store of another context under the CAS makes
     the programme racy: u_passed), so M2DQWBK32.fa_wb_all gives wc(u) <= vG u {u}, given that the
     image's run goes on to a finished state (the guard() after u is passed by then).
   Premises: those of M2DQWBK28.wbc_ord_all plus runWB of the state and the image's finished future. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO M2SC M2SCx MIPComp MIPNeg M2Iface MIPSync MIBase MIPDrf.
Require Import M2Lit M2IfaceInst M2DQIfaceInst M2WBRel M2DQWBPatch M2DQWB M2DQWBK1 M2DQWBK3 M2DQWBK13 M2DQWBK15 M2DQWBK20 M2DQWBK21 M2DQWBK22 M2DQWBK28 M2DQWBK30 M2DQWBK32.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

(* a store under the next access of another context has been passed (or the programme is racy) *)
Lemma u_passed : forall p Fk Good sw s0 sA0 l g u eu x d c2,
  wf p -> cellful p -> race_free_g p -> run p sA0 -> evok sA0 -> rel sw s0 sA0 -> KR Fk Good sw s0 sA0 ->
  base p sA0 l g ->
  ent s0 u = Some eu -> In (u, false) (hs s0 x) -> ec eu <> c2 ->
  dof (ins p c2 (pcs s0 c2) (rg (cs s0 c2))) (rg (cs s0 c2)) = Some d -> In x (icells (inst_of d)) ->
  ek eu < pcs s0 (ec eu).
Proof.
  intros p Fk Good sw s0 sA0 l g u eu x d c2 W Wc RF RA EV Rl K B Eu Iu Nc Dd Id.
  pose proof B as (Sl & Sp & Sr & Go & _).
  destruct (Nat.lt_ge_cases (ek eu) (pcs s0 (ec eu))) as [Lu|Gu]; [exact Lu|].
  exfalso. pose proof (proj2 (reach_runQ p sA0) RA) as R.
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

(* a kept store's slot and time in the write-back state, and its condition, from the image *)
Lemma kept_slot : forall p Fk Good sw s0 sA0 u eu x, run p sA0 -> rel sw s0 sA0 -> KR Fk Good sw s0 sA0 ->
  ent s0 u = Some eu -> In (u, false) (hs s0 x) -> ek eu < pcs s0 (ec eu) ->
  oc (cs s0 (ec eu)) (ek eu) = Some u /\
  executes (ins p (ec eu) (ek eu) (rg (cs s0 (ec eu)))) (rg (cs s0 (ec eu))) = true.
Proof.
  intros p Fk Good sw s0 sA0 u eu x RA Rl K Eu Iu Lu.
  pose proof (Inv1_run p sA0 RA) as I. pose proof (proj2 (Inv2_run p sA0 RA)) as J.
  assert (IuA : In u (ids (hs sA0 x))).
  { rewrite (r_hs sw s0 sA0 Rl x). apply (in_ids_of _ u false). apply in_hers. auto. }
  destruct (j_hist p sA0 J x u IuA) as (EY & iy & AY & WY & _).
  destruct (i_et p sA0 I u EY AY) as (_ & OY).
  destruct (j_ew p sA0 J _ EY _ AY eq_refl) as [W1 _]. rewrite WY in W1.
  assert (EhY : eh EY = false) by (destruct (eh EY); [discriminate|reflexivity]).
  rewrite EhY in OY.
  destruct (k_ent Fk Good sw s0 sA0 K u EY AY) as (eu' & Eu' & (_ & S2 & S3 & _)).
  rewrite Eu in Eu'. injection Eu' as <-. rewrite S2, S3 in OY.
  destruct (crel_eq p Fk Good sw s0 sA0 RA Rl K (ec eu)) as (OcE & _ & AiE & RgE & _).
  split; [rewrite <- OcE; exact OY|].
  assert (LA : ek eu < pcs sA0 (ec eu)) by (rewrite (r_pcs sw s0 sA0 Rl); exact Lu).
  destruct (proj1 (i_cmA p sA0 I (ec eu) (ek eu)) LA) as (tau & Inm).
  pose proof (proj2 (i_set p sA0 I (ec eu) (ek eu) tau Inm)) as Ai.
  unfold einstr, rgof in W1. rewrite S2, S3, Ai, EhY in W1. symmetry in W1. rewrite <- RgE.
  destruct (ins p (ec eu) (ek eu) (rg (cs sA0 (ec eu)))) as [| | | |]; cbn in W1 |- *;
    repeat rewrite andb_true_iff in W1; try discriminate; unfold executes, icond; cbn; intuition.
Qed.

Theorem wbc_full_wbP : forall p Fk Good sw s0 sA0 l g s' c k t1 H'' x u eu,
  wf p -> cellful p -> race_free_g p -> run p sA0 -> evok sA0 -> rel sw s0 sA0 -> KR Fk Good sw s0 sA0 ->
  runWB p s0 -> base p sA0 l g -> (exists sAf, star p sA0 sAf /\ done p sAf) ->
  step p s0 s' -> partskip s0 s' c k t1 -> (forall y, ~ In t1 (ids (hs s0 y))) -> In x (icells (ai (cs s' c) k)) ->
  ent s0 u = Some eu -> ew eu = true -> In (u, false) (hs s0 x) ->
  forall z, wc (wbst s' c k t1 H'') u z ->
    z = u \/ wc (wbst s' c k t1 H'') t1 z \/ vG (wbst s' c k t1 H'') z.
Proof.
  intros p Fk Good sw s0 sA0 l g s' c k t1 H'' x u eu W Wc RF RA EV Rl K RW B Fut St P Fr Ix Eu Ewu Iu z Z.
  pose proof (WK_run p W s0 RW) as Wk.
  destruct (wbc_wbP p Fk Good sw s0 sA0 l g s' c k t1 H'' x u eu W Wc RF RA EV Rl K Wk B St P Fr Ix Eu Ewu Iu)
    as [H|(N & F1 & F2)].
  - destruct (H z Z); auto.
  - pose proof (partskip_form p s0 s' c k t1 St P) as Es.
    pose proof P as (_ & _ & Pk & _ & Oc & Oh & _).
    assert (Ax : exists xs, ai (cs s0 c) k = crd Plain xs).
    { destruct (crel_eq p Fk Good sw s0 sA0 RA Rl K c) as (OcE & OhE & AiE & _).
      assert (OcA : oc (cs sA0 c) k = None) by (rewrite OcE; exact Oc).
      assert (OhA : oh (cs sA0 c) k = Some t1) by (rewrite OhE; exact Oh).
      destruct (i_half p sA0 (Inv1_run p sA0 RA) c k t1 OcA OhA ltac:(rewrite (r_pcs sw s0 sA0 Rl); lia)) as (_ & (xs & A) & _).
      exists xs. rewrite <- AiE. exact A. }
    destruct (ps_next p s0 s' c k t1 St P Ax) as (d & D & Ic). rewrite <- Ic in Ix. rewrite <- Pk in D.
    pose proof (u_passed p Fk Good sw s0 sA0 l g u eu x d c W Wc RF RA EV Rl K B Eu Iu N D Ix) as Lu.
    destruct (kept_slot p Fk Good sw s0 sA0 u eu x RA Rl K Eu Iu Lu) as (Ou & Ex).
    assert (Nu : u <> t1) by (intros ->; apply (Fr x); apply (in_ids_of _ t1 false); exact Iu).
    rewrite (wbst_wc_old s' c k t1 H'' u Nu) in Z. rewrite Es in Z. cbn [sskip wc] in Z.
    destruct (fa_wb_all p Fk Good sw s0 sA0 (ec eu) (ek eu) u eu x W RA Rl K RW F1 Lu (or_intror Fut) Ou Ex Eu Ewu Iu z Z)
      as [Zg|Zu]; [|left; exact Zu].
    right; right. cbn [wbst vG]. rewrite Es. exact Zg.
Qed.

Print Assumptions u_passed.
Print Assumptions wbc_full_wbP.
