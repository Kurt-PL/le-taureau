(* Part 6: what a read takes in the image is covered by what it takes in the state;
   what an access knows in order through guard() in the image is covered, after a guard()
   followed only by reads of CASes. *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB M2DQWBK1 M2DQWBK2 M2DQWBK3 M2DQWBK5.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQShim.

Section Src.
Set Default Proof Using "All".
Variables (p : prog) (Fk : Prop) (Good : nat -> Prop) (sw : nat -> option (cell -> option nat)) (sW sA : st).
Hypothesis RA : run p sA.
Hypothesis R : rel sw sW sA.
Hypothesis K : KR Fk Good sw sW sA.
Hypothesis HF : Fk.

Lemma older_gedge : forall x a b, older (hs sW x) a b -> Pth sW a b.
Proof. intros x a b O. constructor. left. exists x. exact O. Qed.

Lemma seg_older : forall h w u, seg h w (Some u) -> older h u w.
Proof.
  intros h w u (h0 & h1 & h2 & E & _). rewrite E. exists (h0 ++ [(u, false)]), (h1 ++ (w, true) :: h2). split.
  - rewrite <- app_assoc. reflexivity.
  - split; rewrite ids_app, in_app_iff; [right; left; reflexivity|right; left; reflexivity].
Qed.

Lemma in_ids_flag : forall h w, In w (ids h) -> exists b, In (w, b) h.
Proof.
  intros h w I. unfold ids in I. apply in_map_iff in I. destruct I as ([w' b] & E & I). simpl in E. subst. eauto.
Qed.

(* the write a read of the image took has a path into the write the state's read took *)
Lemma src_path : forall x z' z, In z' (ids (hs sW x)) -> pi sw x (Some z') = Some z -> z = z' \/ Pth sW z z'.
Proof.
  intros x z' z I E. unfold pi in E. destruct (sw z') as [f|] eqn:Sw.
  - right. destruct (in_ids_flag _ _ I) as [[|] Ib].
    + destruct (w_bet Fk Good sw sW sA K x z' Ib) as (f' & Sw' & Sg). rewrite Sw in Sw'. injection Sw' as <-.
      rewrite E in Sg. exact (older_gedge x z z' (seg_older _ _ _ Sg)).
    + destruct (r_kept sw sW sA R x z' Ib) as [Sn _]. congruence.
  - left. injection E as ->. reflexivity.
Qed.

Lemma srcs_cov : forall S u uA, (forall a b, gedge sW a b -> gedge S a b) -> (forall x, uA x = pi sw x (u x)) ->
  (forall x w', u x = Some w' -> In w' (ids (hs sW x))) -> vsub (srcs uA) (cov S (srcs u)).
Proof.
  intros S u uA G Hu Hk z (x & Ex). apply (cov_grow sW S G). rewrite Hu in Ex. destruct (u x) as [z'|] eqn:Eu; [|discriminate].
  destruct (src_path x z' z (Hk x z' Eu) Ex) as [->|P].
  - left. exists x. exact Eu.
  - right. exists z'. split; [exists x; exact Eu|exact P].
Qed.

Lemma carr_cov : forall S c u uA, (forall a b, gedge sW a b -> gedge S a b) -> (forall x, uA x = pi sw x (u x)) ->
  (forall x w', u x = Some w' -> In w' (ids (hs sW x))) -> vsub (carrieds (mof sA c) uA) (cov S (carrieds (mof sW c) u)).
Proof.
  intros S c u uA G Hu Hk v (x & y & Ey & Hv). apply (cov_grow sW S G). rewrite Hu in Ey.
  destruct (u x) as [z'|] eqn:Eu; [|discriminate].
  assert (Cz : carrieds (mof sW c) u z') by (exists x, z'; split; [exact Eu|right; reflexivity]).
  assert (Py : y = z' \/ Pth sW y z') by exact (src_path x z' y (Hk x z' Eu) Ey).
  assert (Iy : In y (ids (hs sA x))).
  { pose proof (pi_inm sw sW sA x z' R (Hk x z' Eu)) as M. rewrite Ey in M. exact M. }
  assert (Pv : v = y \/ Pth sW v y).
  { destruct Hv as [Hv| ->]; [|left; reflexivity]. exact (k_wc Fk Good sw sW sA K HF y x Iy v Hv). }
  assert (Cy : cov sW (carrieds (mof sW c) u) y).
  { destruct Py as [->|P']; [left; exact Cz|right; exists z'; split; [exact Cz|exact P']]. }
  destruct Pv as [->|Pvy]; [exact Cy|exact (cov_path sW _ v y Pvy Cy)].
Qed.

Lemma ownw_dec : forall s c z, ownw s c z \/ ~ ownw s c z.
Proof.
  intros s c z. destruct (nth_error (lg s) z) as [e|] eqn:E; unfold ownw.
  - destruct (Nat.eq_dec (ec e) c) as [Ec|Nc]; destruct (ew e) eqn:W.
    + left. exists e. auto.
    + right. intros (e' & E' & _ & W'). rewrite E in E'. injection E' as <-. congruence.
    + right. intros (e' & E' & C' & _). rewrite E in E'. injection E' as <-. congruence.
    + right. intros (e' & E' & C' & _). rewrite E in E'. injection E' as <-. congruence.
  - right. intros (e' & E' & _). congruence.
Qed.

(* after a guard() followed only by reads of CASes that store nothing, an own write before now
   is known in order through guard() *)
Lemma own_og : forall c t z, LFB sW c t -> ownw sW c z -> z < t -> vOg (cs sW c) z.
Proof.
  intros c t z (tg & g & L & Eg & Ec & F & Lt) (e & Ez & Cz & Wz) Lz.
  destruct (lt_eq_lt_dec z tg) as [[L1|L1]|L1].
  - subst c. destruct (w_OGP Fk Good sw sW sA K tg g Eg F) as [O _]. apply O.
    apply (w_OWG Fk Good sw sW sA K tg g z Eg F); [exists e; auto|exact L1].
  - subst z. unfold ent in Eg. rewrite Ez in Eg. injection Eg as <-.
    rewrite (ffew p Fk Good sw sW sA RA R K tg e Ez F) in Wz. discriminate.
  - destruct (Lt z e L1 Lz Ez Cz) as [_ W]. congruence.
Qed.

Lemma tookord_cov : forall S c u uA, (forall a b, gedge sW a b -> gedge S a b) -> (forall x, uA x = pi sw x (u x)) ->
  (forall x w', u x = Some w' -> In w' (ids (hs sW x))) -> LFB sW c (tm sW) ->
  vsub (tookord sA c (vO (cs sA c)) uA) (cov S (vor (vOg (cs sW c)) (tookord sW c (vO (cs sW c)) u))).
Proof.
  intros S c u uA G Hu Hk Lb z ((x & Ex) & _). apply (cov_grow sW S G). rewrite Hu in Ex.
  destruct (u x) as [z'|] eqn:Eu; [|discriminate].
  assert (C' : cov sW (vor (vOg (cs sW c)) (tookord sW c (vO (cs sW c)) u)) z').
  { left. destruct (ownw_dec sW c z') as [O|N].
    - left. apply (own_og c (tm sW) z' Lb O). exact (i_ids sw sW sA R x z' (Hk x z' Eu)).
    - right. split; [exists x; exact Eu|]. intros [O _]. exact (N O). }
  destruct (src_path x z' z (Hk x z' Eu) Ex) as [->|P]; [exact C'|exact (cov_path sW _ z z' P C')].
Qed.

Lemma evQ_cov : forall S c i r u uA w, (forall a b, gedge sW a b -> gedge S a b) -> (forall x, uA x = pi sw x (u x)) ->
  (forall x w', u x = Some w' -> In w' (ids (hs sW x))) -> LFB sW c (tm sW) ->
  vsub (evQ sA c i r (mof sA c) (vOg (cs sA c)) (vO (cs sA c)) uA w)
       (cov S (evQ sW c i r (mof sW c) (vOg (cs sW c)) (vO (cs sW c)) u w)).
Proof.
  intros S c i r u uA w G Hu Hk Lb. unfold evQ. destruct (w || (is_load i && icond i r)).
  - intros z [Z|Z].
    + apply (cov_grow sW S G). apply (cov_mono sW (vOg (cs sW c))); [intros y Y; left; exact Y|].
      exact (k_Og Fk Good sw sW sA K HF c z Z).
    + exact (tookord_cov S c u uA G Hu Hk Lb z Z).
  - intros z [].
Qed.

(* the release view of the image, after a guard() followed only by reads of CASes *)
Lemma R_og : forall c, LFB sW c (tm sW) -> vsub (vR (cs sA c)) (vOg (cs sA c)).
Proof.
  intros c (tg & g & L & Eg & Ec & F & Lt').
  destruct (entW p Fk Good sw sW sA RA R K tg g Eg) as (gA & EgA & Sg).
  pose proof Sg as (_ & E2 & _ & _ & _ & E6 & _).
  apply (LFR_run p sA RA c tg gA EgA ltac:(congruence) (isFF_WA p Fk Good sw sW sA RA R K tg g gA F Sg)).
  intros t' e' L1 E' C'. destruct (k_ent Fk Good sw sW sA K t' e' E') as (eW & EW & (_ & F2 & _ & _ & _ & F6 & _)).
  assert (L2 : t' < tm sW).
  { assert (t' < length (lg sA)) by (unfold ent in E'; apply nth_error_Some; congruence).
    rewrite (k_len Fk Good sw sW sA K), <- (tmW p Fk Good sw sW sA RA R K) in H. exact H. }
  destruct (Lt' t' eW L1 L2 EW ltac:(congruence)) as [Hh _]. congruence.
Qed.
End Src.

Lemma newOg_cov : forall S i m' m'A OgA OgW, vsub (mP m'A) (cov S (mP m')) -> vsub (mG m'A) (cov S (mG m')) ->
  vsub OgA (cov S OgW) -> vsub (newOg i m'A OgA) (cov S (newOg i m' OgW)).
Proof.
  intros S i m' m'A OgA OgW HP HG HO. destruct i as [| | |[]|]; cbn; auto; apply cov_or; auto.
Qed.
