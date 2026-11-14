(* Part 1: paths of the event graph, what a view is covered by, the guard() an
   access follows (LFB), and two facts on any step: the event graph only grows, and after a
   guard() with nothing of its context but reads of CASes after it, the release view is within
   what the context knows in order through guard() (LFR). *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQShim.

(* ---------- paths, cover ---------- *)
Definition Pth (s : st) : nat -> nat -> Prop := clos_trans nat (gedge s).
(* t is in V, or there is a path from t to something in V *)
Definition cov (s : st) (V : view) : view := fun t => V t \/ exists y, V y /\ Pth s t y.

Lemma cov_in : forall s V t, V t -> cov s V t.
Proof. intros. left. auto. Qed.
Lemma cov_mono : forall s V V', vsub V V' -> vsub (cov s V) (cov s V').
Proof. intros s V V' H t [A|(y & A & P)]; [left; auto|right; exists y; auto]. Qed.
Lemma cov_path : forall s V t y, Pth s t y -> cov s V y -> cov s V t.
Proof.
  intros s V t y P [A|(z & A & Q)]; right; [exists y; auto|exists z; split; auto; econstructor 2; eauto].
Qed.
Lemma cov_cov : forall s V t, cov s (cov s V) t -> cov s V t.
Proof. intros s V t [A|(y & A & P)]; [exact A|exact (cov_path s V t y P A)]. Qed.
Lemma cov_sub : forall s V V', vsub V (cov s V') -> vsub (cov s V) (cov s V').
Proof. intros s V V' H t C. apply cov_cov. exact (cov_mono s V (cov s V') H t C). Qed.
Lemma cov_or : forall s A B A' B', vsub A (cov s A') -> vsub B (cov s B') -> vsub (vor A B) (cov s (vor A' B')).
Proof.
  intros s A B A' B' H1 H2 t [X|X]; [apply (cov_mono s A' (vor A' B')); [intros z Z; left; exact Z|apply H1; exact X]|].
  apply (cov_mono s B' (vor A' B')); [intros z Z; right; exact Z|apply H2; exact X].
Qed.
Lemma cov_grow : forall s s', (forall a b, gedge s a b -> gedge s' a b) -> forall V, vsub (cov s V) (cov s' V).
Proof.
  intros s s' G V t [A|(y & A & P)]; [left; auto|right; exists y; split; auto].
  unfold Pth in *. clear A. induction P as [a b H|a b c' _ IH1 _ IH2]; [constructor; apply G; exact H|exact (t_trans _ _ a b c' IH1 IH2)].
Qed.

(* ---------- slots, guard() events ---------- *)
(* the event g at time t is a guard() of its context, at a passed slot whose record is t *)
Definition isFF (s : st) (t : nat) (g : oev) : Prop :=
  ai (cs s (ec g)) (ek g) = IFn FFull /\ ek g < pcs s (ec g) /\ oc (cs s (ec g)) (ek g) = Some t.
(* before time t, context c's last guard() is followed only by reads of CASes that store nothing *)
Definition LFB (s : st) (c t : nat) : Prop :=
  exists tg g, tg < t /\ ent s tg = Some g /\ ec g = c /\ isFF s tg g /\
    forall t' e', tg < t' -> t' < t -> ent s t' = Some e' -> ec e' = c -> eh e' = true /\ ew e' = false.
(* after a guard() followed only by reads of CASes, the release view is within vOg *)
Definition LFR (s : st) : Prop :=
  forall c tg g, ent s tg = Some g -> ec g = c -> isFF s tg g ->
    (forall t' e', tg < t' -> ent s t' = Some e' -> ec e' = c -> eh e' = true) ->
    vsub (vR (cs s c)) (vOg (cs s c)).

Lemma ent_app : forall l (e : oev) t g, nth_error (l ++ [e]) t = Some g ->
  (nth_error l t = Some g /\ t < length l) \/ (t = length l /\ g = e).
Proof.
  intros l e t g H. rewrite nth_error_app_last in H. destruct (Nat.ltb_spec t (length l)) as [L|L].
  - left. auto.
  - destruct (Nat.eqb_spec t (length l)) as [E|E]; [|discriminate]. injection H as <-. right. auto.
Qed.

Lemma eff_full : forall t r m m' a K u w, eff t (IFn FFull) r m m' a K u w -> m' = gpost (gpre m) /\ w = false.
Proof. intros t r m m' a K u w H. inversion H; subst; auto; discriminate. Qed.
(* an access, a CAS's read or another fence leaves vR and vOg as they are, or it is a fence *)
Lemma eff_R : forall t i r m m' a K u w, eff t i r m m' a K u w ->
  (forall f, i <> IFn f) -> mR m' = mR m.
Proof. intros t i r m m' a K u w H N. inversion H; subst; try reflexivity; exfalso; eapply N; reflexivity. Qed.

Lemma eof_notFF : forall i r d, eof i r = Some d -> i <> IFn FFull.
Proof. intros i r d H E. subst. discriminate. Qed.

Lemma isacc_eof : forall i r d, eof i r = Some d -> isacc i = isacc (inst_of d).
Proof.
  intros [m x c0|m x c0 v|m x c0 e n|f|] r d H; simpl in H; try discriminate.
  all: try (destruct f; [injection H as <-| injection H as <-| injection H as <-| injection H as <-|discriminate]; reflexivity).
  all: unfold dof in H; simpl in H; destruct (c0 r); [|discriminate]; injection H as <-; reflexivity.
Qed.

Section LFR.
Variable p : prog.

Lemma LFR_init : LFR sinit.
Proof. intros c tg g E. unfold ent in E. destruct tg; discriminate. Qed.

(* the slot of a guard() event: its own record; a step changes no passed slot *)
Lemma LFR_stepA : forall s s', M2Model.step p s s' -> tm s = length (lg s) -> LFR s -> LFR s'.
Proof.
  intros s s' H Tl L. intros c0 tg g Eg Ec (Fa & Fp & Fo) Lt.
  destruct (step_cases p s s' H) as
    [(c & i & m' & a & K & u & w & Hi & Hoc & _ & _ & _ & Hh & _ & _ & He & _ & ->)
    |[(c & k & d & B & m' & a & K & u & w & L1 & Hoc & _ & Hd & _ & _ & He & _ & ->)
    |[(c & d & H1 & H2 & H3 & _ & _ & _ & ->)
    |[(c & k & xs & B & m' & a & K & u & w & bv & L1 & Hoc & Hoh & _ & _ & He & _ & ->)
    |[(c & S1 & S2 & _ & _ & _ & _ & _ & ->)
    |(cX & jX & bX & BX & oX & HjX & HfX & HcX & ->)]]]]].
  - (* in order *)
    unfold sord, evs, ent in *; cbn [cs lg pcs vR vOg oc ai] in *.
    destruct (ent_app _ _ _ _ Eg) as [(Eg' & Lg)|(Eg' & ->)].
    + destruct (Nat.eqb_spec c0 c) as [->|N].
      * exfalso. assert (Lnew : tg < tm s) by lia.
        assert (Z : eh (newev s c (pcs s c) i K u w) = true).
        { apply (Lt (tm s)); [exact Lnew|rewrite nth_error_app_last, Tl, Nat.ltb_irrefl, Nat.eqb_refl; reflexivity|reflexivity]. }
        discriminate.
      * subst c0. rewrite !upd_neq in * by exact N. apply (L (ec g) tg g); auto; [split; [|split]; auto; rewrite upd_neq in Fp by exact N; exact Fp|].
        intros t' e' L2 E2 C2. apply (Lt t' e' L2); [rewrite nth_error_app1; [exact E2|apply nth_error_Some; unfold ent in E2; congruence]|exact C2].
    + cbn in Ec. subst c0. rewrite !upd_eq in *. cbn in Fa. rewrite upd_eq in Fa. subst i.
      destruct (eff_full _ _ _ _ _ _ _ _ He) as [-> _]. cbn. intros y Y. exact Y.
  - (* early *)
    unfold searly, set_es, searly0, evs, ent in *; cbn [cs lg pcs vR vOg oc ai] in *.
    destruct (ent_app _ _ _ _ Eg) as [(Eg' & Lg)|(Eg' & ->)].
    + destruct (Nat.eqb_spec c0 c) as [->|N].
      * exfalso. assert (Lnew : tg < tm s) by lia.
        assert (Z : eh (newev s c k (inst_of d) K u w) = true).
        { apply (Lt (tm s)); [exact Lnew|rewrite nth_error_app_last, Tl, Nat.ltb_irrefl, Nat.eqb_refl; reflexivity|reflexivity]. }
        discriminate.
      * subst c0. rewrite !upd_neq in * by exact N. apply (L (ec g) tg g); auto; [split; [|split]; auto|].
        intros t' e' L2 E2 C2. apply (Lt t' e' L2); [rewrite nth_error_app1; [exact E2|apply nth_error_Some; unfold ent in E2; congruence]|exact C2].
    + exfalso. cbn in Fp. lia.
  - (* the context reaches an access that happened early *)
    unfold smatch, ent in *; cbn [cs lg pcs vR vOg oc ai] in *.
    destruct (Nat.eqb_spec c0 c) as [->|N].
    + subst c. rewrite upd_eq in *. cbn [ai oc vR vOg] in *. apply (L (ec g) tg g); auto. split; [|split]; auto.
      * destruct (Nat.eqb_spec (ek g) (pcs s (ec g))) as [Ek|Ek].
        -- exfalso. rewrite Ek, upd_eq in Fa. exact (eof_notFF _ _ _ H3 Fa).
        -- rewrite upd_neq in Fa by exact Ek. exact Fa.
      * rewrite upd_eq in Fp. destruct (Nat.eqb_spec (ek g) (pcs s (ec g))) as [Ek|Ek]; [|lia].
        exfalso. rewrite Ek, upd_eq in Fa. exact (eof_notFF _ _ _ H3 Fa).
    + subst c0. rewrite !upd_neq in * by exact N. apply (L (ec g) tg g); auto. split; [|split]; auto.
  - (* a CAS's read alone *)
    unfold sread, ent in *; cbn [cs lg pcs vR vOg oc ai] in *.
    destruct (ent_app _ _ _ _ Eg) as [(Eg' & Lg)|(Eg' & ->)].
    + assert (Lt' : forall t' e', tg < t' -> nth_error (lg s) t' = Some e' -> ec e' = c0 -> eh e' = true).
      { intros t' e' L2 E2 C2. apply (Lt t' e' L2); [rewrite nth_error_app1; [exact E2|apply nth_error_Some; unfold ent in E2; congruence]|exact C2]. }
      destruct (Nat.eqb_spec c0 c) as [->|N].
      * subst c. rewrite !upd_eq in *. cbn [ai oc vR vOg] in *.
        assert (Ek : ek g <> k) by (intros Ek; rewrite Ek, upd_eq in Fa; discriminate).
        rewrite upd_neq in Fa by exact Ek.
        rewrite (eff_R _ _ _ _ _ _ _ _ _ He) by discriminate. cbn [newOg].
        exact (L (ec g) tg g Eg' eq_refl (conj Fa (conj Fp Fo)) Lt').
      * subst c0. rewrite !upd_neq in * by exact N. apply (L (ec g) tg g Eg' eq_refl); [split; [|split]; auto|exact Lt'].
    + exfalso. cbn in Fo. rewrite upd_eq in Fo. cbn in Fo. congruence.
  - (* passing an instruction that does not execute *)
    unfold sskip, ent in *; cbn [cs lg pcs vR vOg oc ai] in *.
    destruct (Nat.eqb_spec c0 c) as [->|N].
    + subst c. rewrite upd_eq in *. cbn [ai oc vR vOg] in *. apply (L (ec g) tg g); auto. split; [|split]; auto.
      * destruct (Nat.eqb_spec (ek g) (pcs s (ec g))) as [Ek|Ek].
        -- exfalso. rewrite Ek, upd_eq in Fa. rewrite Ek in Fo. congruence.
        -- rewrite upd_neq in Fa by exact Ek. exact Fa.
      * rewrite upd_eq in Fp. destruct (Nat.eqb_spec (ek g) (pcs s (ec g))) as [Ek|Ek]; [|lia].
        exfalso. rewrite Ek in Fo. congruence.
    + subst c0. rewrite !upd_neq in * by exact N. apply (L (ec g) tg g); auto. split; [|split]; auto.
  - (* a result fixed *)
    unfold ent in *. unfold scfix0 in *. cbn [cs lg pcs vR vOg oc ai] in *.
    rewrite (lg_flp s cX oX bX) in Eg, Lt. rewrite (pcs_flp s cX oX bX) in Fp.
    destruct (Nat.eqb_spec c0 cX) as [->|N].
    + rewrite upd_eq in *. cbn [ai oc vR vOg] in *. rewrite (ai_flp s cX oX bX), (oc_flp s cX oX bX) in *.
      rewrite (vR_flp s cX oX bX), (vOg_flp s cX oX bX). subst cX.
      apply (L (ec g) tg g); auto. split; [|split]; auto; [rewrite upd_eq in Fa|rewrite upd_eq in Fo]; cbn [ai oc] in *; auto.
    + subst c0. rewrite !upd_neq in * by exact N. rewrite (ai_flp s cX oX bX), (oc_flp s cX oX bX) in *.
      rewrite (vR_flp s cX oX bX), (vOg_flp s cX oX bX). apply (L (ec g) tg g); auto. split; [|split]; auto.
Qed.

(* a record fix keeps every field LFR reads *)
Lemma LFR_rfx : forall s s', rfx s s' -> LFR s -> LFR s'.
Proof.
  intros s s' RF L c0 tg g Eg Ec F Lt. unfold isFF, ent in *. rfx_rw RF. exact (L c0 tg g Eg Ec F Lt).
Qed.

Lemma LFR_step : forall s s', step p s s' -> tm s = length (lg s) -> LFR s -> LFR s'.
Proof.
  intros s s' H Tl L. destruct (stepQ_split p s s' H) as [[H' _]|RF]; [exact (LFR_stepA s s' H' Tl L)|exact (LFR_rfx s s' RF L)].
Qed.

Lemma LFR_run : forall s, run p s -> LFR s.
Proof.
  intros s R. induction R as [|s s' R IH St]; [exact LFR_init|].
  apply (LFR_step s s' St); [exact (i_tm p s (Inv1_run p s R))|exact IH].
Qed.
End LFR.
