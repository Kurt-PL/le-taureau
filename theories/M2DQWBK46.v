(* Part 46: WBCall along the chain.  A step of A keeps every stand-for pair of the
   state before and makes none (seg_del_f), keeps old conveyed sets, and only grows vG
   (WBCall_stepA).  The write-back patch adds the pairs of the new written-back store t, which
   (WBC'') of t covers (WBCall_wb, with the stood-for store below t as a premise), and keeps the
   others (seg_del_t).  wch_wbc2: M2DQWBK37.wch_wbc returning the link's own decomposition with
   (WBC''). *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Lit.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB.
Require Import M2Iface M2IfaceInst M2DQIfaceInst M2DQIfaceUse.
Require Import M2DQWBK1 M2DQWBK2 M2DQWBK3 M2DQWBK4 M2DQWBK7 M2DQWBK9 M2DQWBK10 M2DQWBK11 M2DQWBK12 M2DQWBK13 M2DQWBK19 M2DQWBFsc.
Require Import M2DQWBK20 M2DQWBK21 M2DQWBK22 M2DQWBK30 M2DQWBK33 M2DQWBK36 M2DQWBK15 M2DQWBK37 M2DQWBK38 M2DQWBK40 M2DQWBK44.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

Lemma WBCall_stepA : forall p s s', step p s s' -> fhsafe s s' -> tm s = length (lg s) -> KM s ->
  (forall x w, In w (ids (hs s x)) -> w < tm s) -> WBCall s -> WBCall s'.
Proof.
  intros p s s' H FH Tl Km Ii WB x w z Sg y Y.
  assert (Sg0 : seg (hs s x) w (Some z)).
  { destruct (step_hs p s s' H x) as [E|(h1 & h2 & E1 & E2)]; [rewrite <- E; exact Sg|].
    rewrite E2 in Sg. rewrite E1. apply (seg_del_f h1 h2 (tm s)); [exact Sg|exact (FH x h1 h2 E1 E2)|].
    intros I. rewrite <- E1 in I. pose proof (Ii x (tm s) I). lia. }
  pose proof (Ii x z (in_ids_of _ _ _ (stands_kept _ _ _ Sg0))) as Lz'.
  pose proof (Ii x w (seg_in_l _ _ _ Sg0)) as Lw.
  rewrite (sh_wc_old p s s' H Tl z Lz') in Y.
  destruct (WB x w z Sg0 y Y) as [E|[E|E]]; [left; exact E|right; left|right; right].
  - rewrite (sh_wc_old p s s' H Tl w Lw). exact E.
  - exact (proj1 (proj1 (step_km p s s' H Km)) y E).
Qed.

Section WbC.
Variables (s : st) (c k t : nat) (H'' : cell -> hist).
Hypothesis Hfresh : forall x, ~ In t (ids (hs s x)).
Hypothesis Hok : wbok s c k t H''.
Hypothesis WB : WBCall s.
Hypothesis Hw : WBC (wbst s c k t H'') c k t.
Hypothesis Hst : forall x u, In (u, false) (hs s x) -> exists eu, ent s u = Some eu /\ ew eu = true.
Hypothesis Hlt : forall x z, seg (H'' x) t (Some z) -> z < t.

Theorem WBCall_wb : WBCall (wbst s c k t H'').
Proof.
  intros x w z Sg y Y. cbn [hs wbst] in Sg. cbn [wc wbst vG] in Y |- *.
  destruct (Nat.eq_dec w t) as [->|Nw].
  - assert (Ix : In x (icells (ai (cs s c) k))).
    { destruct (in_dec Nat.eq_dec x (icells (ai (cs s c) k))) as [I|N]; [exact I|exfalso].
      destruct (Hok x) as [_ E2]. rewrite (E2 N) in Sg. exact (Hfresh x (seg_in_l _ _ _ Sg)). }
    pose proof (stands_kept _ _ _ Sg) as Kz.
    assert (Kz0 : In (z, false) (hs s x)).
    { destruct (enters_tied_cell _ _ _ _ _ x Hok) as [E|(h1 & h2 & E1 & E2 & _)]; [rewrite <- E; exact Kz|].
      rewrite E2 in Kz. rewrite E1. apply in_app_iff in Kz. apply in_app_iff. destruct Kz as [K1|[K1|K1]]; [left; exact K1|discriminate|right; exact K1]. }
    destruct (Hst x z Kz0) as (eu & Eu & Ewu).
    assert (Ezt : z <> t) by (intros Ez; subst z; exact (Hfresh x (in_ids_of _ _ _ Kz0))).
    refine (Hw x _ z (sete t eu) _ _ Kz (Hlt x z Sg) y _).
    + cbn [wbst cs]. rewrite upd_eq. exact Ix.
    + unfold ent. cbn [wbst lg]. rewrite nth_setew. unfold ent in Eu. rewrite Eu. reflexivity.
    + unfold sete. destruct (Nat.eqb (et eu) t); [reflexivity|exact Ewu].
    + cbn [wc wbst]. exact Y.
  - assert (Sg0 : seg (hs s x) w (Some z)).
    { destruct (enters_tied_cell _ _ _ _ _ x Hok) as [E|(h1 & h2 & E1 & E2 & _)]; [rewrite <- E; exact Sg|].
      rewrite E2 in Sg. rewrite E1. exact (seg_del_t h1 h2 t w z Sg Nw). }
    assert (Nz : z <> t) by (intros Ez; subst z; exact (Hfresh x (in_ids_of _ _ _ (stands_kept _ _ _ Sg0)))).
    rewrite upd_neq in Y by exact Nz. rewrite upd_neq by exact Nw. exact (WB x w z Sg0 y Y).
Qed.
End WbC.

Section Wbc2.
Variables (p : prog) (W : wf p) (Fk : Prop) (Good : nat -> Prop).
Theorem wch_wbc2 : forall sW sw sA sw' sW' sA', cellful p -> race_free_g p ->
  wch p Fk Good sW sw sA -> wlink p Fk Good sw sW sA sw' sW' sA' ->
  run p sA' -> rel sw' sW' sA' -> KR Fk Good sw' sW' sA' ->
  evok sA -> evok sA' -> (exists sAf, star p sA' sAf /\ done p sAf) ->
  (step p sW sW' /\ fhsafe sW sW' /\ step p sA sA' /\ sw' = sw) \/
  exists s' c k t H'', sW' = wbst s' c k t H'' /\
    ((step p sW s' /\ partskip sW s' c k t /\ (forall x, ~ In t (ids (hs sW x))) /\ wbok s' c k t H'' /\
        rel sw s' sA' /\ KR Fk Good sw s' sA') \/
     (s' = sW /\ sA' = sA /\ pcs sW c < k /\ oh (cs sW c) k = Some t /\ oc (cs sW c) k = None /\
        (forall x, ~ In t (ids (hs sW x))) /\ wbok sW c k t H'')) /\ WBC sW' c k t.
Proof.
  intros sW sw sA sw' sW' sA' Wc RF Ch L RA' Rl' K' EV EV' Fut.
  destruct (wch_inv p Fk Good sW sw sA Ch) as (RA & Rl & K & RW).
  pose proof (wrS p sW sW' RW (wlink_stepWB p Fk Good sw sW sA sw' sW' sA' L)) as RW'.
  pose proof (WK_run p W sW RW) as Wk.
  assert (FutA : exists sAf, star p sA sAf /\ done p sAf).
  { destruct Fut as (sAf & S & D). exists sAf. split; [exact (wlink_star p Fk Good sw sW sA sw' sW' sA' sAf L S)|exact D]. }
  destruct L as [LA|[(s' & c & k & t1 & H'' & St & Ps & Fr & Ok & E & StA & Rl0 & K0 & _)
    |(c & k & t1 & xs & H'' & Lk & Oc & Oh & Ai & Vk & Eo & Fr & Ok & E & EA & _)]].
  - left. exact LA.
  - right. exists s', c, k, t1, H''. split; [exact E|]. split; [left; auto 10|]. subst sW'.
    intros x Ix u eu Eu Ewu Iu Lu z Z.
    assert (Ix' : In x (icells (ai (cs s' c) k))) by (cbn [wbst cs] in Ix; rewrite upd_eq in Ix; exact Ix).
    pose proof Ps as (NW & _ & _ & _ & _ & Oh0 & _).
    pose proof (i_oh sw sW sA Rl c k t1 Oh0) as Lt.
    destruct (wb_old p sW s' c k t1 H'' u eu x Wk St NW Ok ltac:(lia) ltac:(lia) Eu Iu) as [Eu0 Iu0].
    destruct (drf_prefix_dq p sA W Wc RF RA EV) as (l & g & B).
    exact (wbc_full_wbP p Fk Good sw sW sA l g s' c k t1 H'' x u eu W Wc RF RA EV Rl K RW B FutA St Ps Fr Ix' Eu0 Ewu Iu0 z Z).
  - right. exists sW, c, k, t1, H''. split; [exact E|]. split; [right; auto 10|]. subst sW' sA'.
    intros x Ix u eu Eu Ewu Iu Lu z Z.
    destruct (crel_eq p Fk Good sw sW sA RA Rl K c) as (_ & OhE & AiE & _).
    apply (wbc_wbE p Fk Good sw' (wbst sW c k t1 H'') sA c k t1 xs x u eu W Wc RF RA Rl' K' RW' EV Fut).
    + rewrite OhE. exact Oh.
    + rewrite (r_pcs sw sW sA Rl). exact Lk.
    + rewrite AiE, Ai. reflexivity.
    + cbn [wbst cs] in Ix. rewrite upd_eq in Ix. cbn [ai] in Ix. rewrite Ai in Ix. cbn [icells crd] in Ix.
      exact (proj1 (dd_in x xs) Ix).
    + intros z0 Z0. cbn [wbst cs wc] in Z0 |- *. rewrite upd_eq in Z0. cbn [vR] in Z0. rewrite upd_eq. left. exact Z0.
    + exact Eu.
    + exact Ewu.
    + exact Iu.
    + exact Lu.
    + exact Z.
Qed.
End Wbc2.

Print Assumptions WBCall_stepA.
Print Assumptions WBCall_wb.
Print Assumptions wch_wbc2.
