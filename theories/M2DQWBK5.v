(* Part 5: one instruction's effect in the state and in its image keeps the cover. *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB M2DQWBK1 M2DQWBK2 M2DQWBK3.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQShim.

Lemma eff_Pmono : forall t i r m m' a K u w, eff t i r m m' a K u w -> vsub (mP m) (mP m').
Proof.
  intros t i r m m' a K u w H. inversion H; subst; cbn; intros z Z; auto; unfold vor; tauto.
Qed.

Lemma eff_C : forall t i r m m' a K u w, eff t i r m m' a K u w ->
  (w = true -> mC m' = upd (mC m) t (vor (mR m) (vone t))) /\ (w = false -> mC m' = mC m).
Proof. intros t i r m m' a K u w H. inversion H; subst; cbn; split; intros Z; try discriminate; reflexivity. Qed.

Lemma eff_ffK : forall t r m m' a K u w, eff t (IFn FFull) r m m' a K u w -> K = mP (gpre m) /\ m' = gpost (gpre m) /\ w = false.
Proof. intros t r m m' a K u w H. inversion H; subst; auto; discriminate. Qed.

Lemma eff_wput : forall t i r m m' a K u w, eff t i r m m' a K u w -> w = true -> mP m' t.
Proof. intros t i r m m' a K u w H W. inversion H; subst; try discriminate; cbn; right; reflexivity. Qed.

Lemma eff_G : forall t i r m m' a K u w, eff t i r m m' a K u w -> (forall f, i <> IFn f) -> mG m' = mG m.
Proof. intros t i r m m' a K u w H N. inversion H; subst; try reflexivity; exfalso; eapply N; reflexivity. Qed.

Section EffK.
Variable S : st.
Lemma covor_l : forall A B, vsub A (cov S (vor A B)).
Proof. intros A B z Z. left. left. exact Z. Qed.

Lemma effK : forall t i r mw ma m' m'A a K KA u uA w,
  eff t i r mw m' a K u w -> eff t i r ma m'A a KA uA w ->
  vsub (mP ma) (cov S (mP mw)) -> vsub (mA ma) (cov S (mA mw)) -> vsub (mG ma) (cov S (mG mw)) ->
  vsub (mW ma) (mW mw) ->
  vsub (srcs uA) (cov S (srcs u)) -> vsub (carrieds ma uA) (cov S (carrieds mw u)) ->
  vsub (mP m'A) (cov S (mP m')) /\ vsub (mA m'A) (cov S (mA m')) /\ vsub (mG m'A) (cov S (mG m')).
Proof.
  intros t i r mw ma m' m'A a K KA u uA w HW HA KP KA' KG KW KS KC.
  inversion HW; subst; inversion HA; subst; cbn; try discriminate; try congruence.
  all: repeat match goal with H : ?f _ = ?f _ |- _ => injection H; clear H; intros; subst end.
  all: try (exfalso; unfold icond, ieval in *; cbn in *; congruence).
  all: try (split; [|split]; first [exact KP|exact KA'|exact KG|apply cov_or; first [exact KP|exact KA'|exact KG|exact KS|exact KC]|idtac]).
  all: try (apply cov_or; [apply cov_or; [exact KP|exact KS]|intros z Z; left; exact Z]).
  all: try (apply cov_or; [exact KP|intros z Z; left; exact Z]).
  all: try (apply cov_or; [exact KP|exact KA']).
  all: try (apply cov_or; [exact KG|intros z Z; apply cov_in; apply KW; exact Z]).
  all: try (apply cov_or; [apply cov_or; [exact KP|exact KA']|exact KG]).
  all: try (apply cov_or; [apply cov_or; [apply cov_or; [exact KP|exact KA']|exact KG]|exact KA']).
Qed.
End EffK.
