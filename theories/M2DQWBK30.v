(* Part 30: step-level glue for (WBC'') at a CAS passed in order.
   A write-back step wbP (partskip, k = pcs): the CAS at slot k is the context's next instruction,
   an access of the cells it records (ps_next).
   Then for every kept store u in the history of one of those cells (WBC'' at the step, wbc_wbP):
   in the state after the write-back, u conveys at most u and what the
   write-back store (id t) conveys, or u is of another context and both slots are fenced (fa).
   Uses M2DQWBK28.wbc_ord_all on the state before the step (and its image), M2DQWBK20.step_km (vR grows),
   M2DQWBK21.sh_wc_old (old conveyed sets unchanged), and the definition of wbst. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO M2SC M2SCx MIPComp MIPNeg M2Iface MIPSync MIBase MIPDrf.
Require Import M2IfaceInst M2DQIfaceInst M2WBRel M2DQWBPatch M2DQWB M2DQWBK1 M2DQWBK3 M2DQWBK13 M2DQWBK15 M2DQWBK20 M2DQWBK21 M2DQWBK22 M2DQWBK28.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

Lemma cas_dofR : forall i r m xs, eofR i r = Some (m, xs) ->
  exists d, dof i r = Some d /\ icells (inst_of d) = icells i.
Proof.
  intros [m0 xs0 c|m0 xs0 c v|m0 xs0 c e n|f|] r m xs E; try discriminate.
  cbn in E. destruct (c r) eqn:C; [|discriminate]. exists (DCas m0 xs0 (e r) (n r)). cbn. rewrite C. auto.
Qed.

(* the CAS a context passes after its read half happened is its next instruction *)
Lemma ps_next : forall p s s' c k t1, step p s s' -> partskip s s' c k t1 ->
  (exists xs, ai (cs s c) k = crd Plain xs) ->
  exists d, dof (ins p c k (rg (cs s c))) (rg (cs s c)) = Some d /\ icells (inst_of d) = icells (ai (cs s' c) k).
Proof.
  intros p s s' c k t1 H P (xs & Ax). pose proof (partskip_form p s s' c k t1 H P) as Es.
  destruct P as (NW & Tm & Pk & Pk' & Oc & Oh & _).
  destruct (stepQ_split p s s' H) as [[HA _]|RF]; [|exfalso; rewrite (rfx_pcs _ _ RF) in Pk'; lia].
  destruct (step_cases p s s' HA) as
    [(c0 & i & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ->)
    |[(c0 & k0 & d & B & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & _ & _ & ->)
    |[(c0 & d & S1 & _ & _ & _ & _ & _ & ->)
    |[(c0 & k0 & xs0 & B & m' & a & K & u & w & bv & _ & _ & _ & _ & _ & _ & _ & ->)
    |[(c0 & X & Oc0 & E & _ & _ & _ & _ & ->)
    |(cX & jX & bX & BX & oX & _ & _ & _ & ->)]]]]].
  - exfalso. cbn in Tm. lia.
  - exfalso. cbn in Tm. lia.
  - exfalso. cbn [smatch pcs] in Pk'. unfold upd in Pk'. destruct (Nat.eqb_spec c c0) as [->|N]; [|lia].
    apply S1. rewrite Pk. exact Oc.
  - exfalso. cbn in Tm. lia.
  - cbn [sskip pcs] in Pk'. unfold upd in Pk'. destruct (Nat.eqb_spec c c0) as [<-|N]; [|lia].
    subst k. rewrite Ax in E. rewrite Oh in E. specialize (E ltac:(discriminate)).
    destruct (cas_dofR _ _ _ _ E) as (d & D & Ic). exists d. split; [exact D|].
    rewrite Ic. unfold sskip, upd. cbn. rewrite !Nat.eqb_refl. cbn. rewrite ?Nat.eqb_refl. reflexivity.
  - exfalso. unfold scfix0 in Pk'. cbn [pcs] in Pk'. rewrite pcs_flp in Pk'. lia.
Qed.

Lemma wbst_wc_new : forall s c k t H'' z, wc (wbst s c k t H'') t z <-> vR (cs s c) z \/ z = t.
Proof. intros. cbn [wbst wc]. unfold upd. rewrite Nat.eqb_refl. unfold vor, vone. tauto. Qed.

Lemma wbst_wc_old : forall s c k t H'' y, y <> t -> wc (wbst s c k t H'') y = wc s y.
Proof. intros s c k t H'' y N. cbn [wbst wc]. unfold upd. destruct (Nat.eqb_spec y t); [congruence|reflexivity]. Qed.

(* (WBC'') at a write-back by a CAS passed after its read half failed (wbP) *)
Theorem wbc_wbP : forall p Fk Good sw s0 sA0 l g s' c k t1 H'' x u eu,
  wf p -> cellful p -> race_free_g p -> run p sA0 -> evok sA0 -> rel sw s0 sA0 -> KR Fk Good sw s0 sA0 ->
  WK s0 -> base p sA0 l g ->
  step p s0 s' -> partskip s0 s' c k t1 -> (forall y, ~ In t1 (ids (hs s0 y))) -> In x (icells (ai (cs s' c) k)) ->
  ent s0 u = Some eu -> ew eu = true -> In (u, false) (hs s0 x) ->
  (forall z, wc (wbst s' c k t1 H'') u z -> z = u \/ wc (wbst s' c k t1 H'') t1 z) \/
  (ec eu <> c /\ fa p (ec eu) (ek eu) /\ fa p c k).
Proof.
  intros p Fk Good sw s0 sA0 l g s' c k t1 H'' x u eu W Wc RF RA EV Rl K Wk B St P Fr Ix Eu Ewu Iu.
  pose proof (partskip_form p s0 s' c k t1 St P) as Es.
  pose proof P as (_ & _ & Pk & _ & Oc & Oh & _).
  assert (Ax : exists xs, ai (cs s0 c) k = crd Plain xs).
  { destruct (crel_eq p Fk Good sw s0 sA0 RA Rl K c) as (OcE & OhE & AiE & _).
    assert (OcA : oc (cs sA0 c) k = None) by (rewrite OcE; exact Oc).
    assert (OhA : oh (cs sA0 c) k = Some t1) by (rewrite OhE; exact Oh).
    destruct (i_half p sA0 (Inv1_run p sA0 RA) c k t1 OcA OhA ltac:(rewrite (r_pcs sw s0 sA0 Rl); lia)) as (_ & (xs & A) & _).
    exists xs. rewrite <- AiE. exact A. }
  destruct (ps_next p s0 s' c k t1 St P Ax) as (d & D & Ic).
  rewrite <- Ic in Ix. rewrite <- Pk in D.
  destruct (wbc_ord_all p Fk Good sw s0 sA0 l g u eu x d c W Wc RF RA EV Rl K Wk B Eu Ewu Iu D Ix) as [H|(N & F1 & F2)].
  - left. intros z Z.
    assert (Nu : u <> t1) by (intros ->; apply (Fr x); apply (in_ids_of _ t1 false); exact Iu).
    rewrite (wbst_wc_old s' c k t1 H'' u Nu) in Z. rewrite Es in Z. cbn [sskip wc] in Z.
    destruct (H z Z) as [Zu|Zr]; [left; exact Zu|right].
    apply wbst_wc_new. left. rewrite Es. unfold sskip. cbn [cs]. unfold upd. rewrite Nat.eqb_refl. cbn [vR]. exact Zr.
  - right. rewrite <- Pk. auto.
Qed.

Print Assumptions wbc_wbP.

(* the write a written-back store stands for is a kept store of the same cell, with a write entry *)
Lemma kept_ent : forall p Fk Good sw s0 sA0 x u, run p sA0 -> rel sw s0 sA0 -> KR Fk Good sw s0 sA0 ->
  In (u, false) (hs s0 x) -> exists eu, ent s0 u = Some eu /\ ew eu = true.
Proof.
  intros p Fk Good sw s0 sA0 x u RA Rl K Iu.
  pose proof (proj2 (reach_runQ p sA0) RA) as R. pose proof (I2g (M := dqmodel) p sA0 R) as J.
  assert (IuA : In u (ids (hs sA0 x))).
  { rewrite (r_hs sw s0 sA0 Rl x). apply (in_ids_of _ u false). apply in_hers. auto. }
  destruct (j_hist p sA0 J x u IuA) as (EY & iy & AY & WY & _).
  destruct (k_ent Fk Good sw s0 sA0 K u EY AY) as (eu & Eu & (_ & _ & _ & _ & _ & _ & _ & _ & _ & S10)).
  exists eu. split; [exact Eu|]. rewrite (S10 (proj1 (r_kept sw s0 sA0 Rl x u Iu))). exact WY.
Qed.

Lemma stands_kept : forall h w u, seg h w (Some u) -> In (u, false) h.
Proof. intros h w u (h0 & h1 & h2 & E & _). rewrite E. apply in_or_app. right. left. reflexivity. Qed.

(* the case where the CAS read a write-back store w' (flag true): w' stands for a kept store u of
   the same cell with a write entry, to which wbc_wbP applies (the new write-back stands
   for u too) *)
Lemma stands_for_kept : forall p Fk Good sw s0 sA0 x w' f u, run p sA0 -> rel sw s0 sA0 -> KR Fk Good sw s0 sA0 ->
  In (w', true) (hs s0 x) -> sw w' = Some f -> f x = Some u ->
  In (u, false) (hs s0 x) /\ exists eu, ent s0 u = Some eu /\ ew eu = true.
Proof.
  intros p Fk Good sw s0 sA0 x w' f u RA Rl K Iw Sw Fx.
  destruct (w_bet Fk Good sw s0 sA0 K x w' Iw) as (f' & Sw' & Sg). rewrite Sw in Sw'. injection Sw' as <-.
  rewrite Fx in Sg. pose proof (stands_kept _ _ _ Sg) as Iu.
  split; [exact Iu|exact (kept_ent p Fk Good sw s0 sA0 x u RA Rl K Iu)].
Qed.

Print Assumptions stands_for_kept.
