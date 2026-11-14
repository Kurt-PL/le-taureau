(* What one instruction does to the knowledge sets and histories. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist.

Definition vsub (a b : view) : Prop := forall w, a w -> b w.

(* the writes an access read, and the one it made *)
Definition srcv (u : cell -> option nat) (wrote : bool) (t : nat) : view :=
  vor (srcs u) (if wrote then vone t else vnil).

(* executed: an access whose condition holds, or a fence *)
Definition xc (i : instr) (r : regs) : bool := icond i r.
(* guard(): the one instruction that takes and publishes G *)
Definition xgop (i : instr) (r : regs) : bool := isfn FFull i.
Definition xload (i : instr) (r : regs) : bool := is_load i && icond i r.

Definition wval (i : instr) (r : regs) : val :=
  match i with ISt _ _ _ v => v r | ICas _ _ _ _ n => n r | _ => 0 end.
Definition eval_e (i : instr) (r : regs) : val :=
  match i with ICas _ _ _ e _ => e r | _ => 0 end.



(* the values per cell an access writes *)
Definition wvals (i : instr) (r : regs) : list val := projs (length (icells i)) (wval i r).

Lemma ieval_cond : forall i r1 r2, ieval i r1 = ieval i r2 -> icond i r1 = icond i r2.
Proof. intros i r1 r2 H. unfold icond. rewrite H. reflexivity. Qed.
Lemma ieval_wval : forall i r1 r2, ieval i r1 = ieval i r2 -> wval i r1 = wval i r2.
Proof. intros [] r1 r2 H; simpl in *; try reflexivity; injection H; intros; auto. Qed.
Lemma ieval_e : forall i r1 r2, ieval i r1 = ieval i r2 -> eval_e i r1 = eval_e i r2.
Proof. intros [] r1 r2 H; simpl in *; try reflexivity; injection H; intros; auto. Qed.
Lemma ieval_wvals : forall i r1 r2, ieval i r1 = ieval i r2 -> wvals i r1 = wvals i r2.
Proof. intros i r1 r2 H. unfold wvals. rewrite (ieval_wval i r1 r2 H). reflexivity. Qed.

Lemma icond_fn : forall f r, icond (IFn f) r = true.
Proof. reflexivity. Qed.

Lemma lst_eqb_eq : forall a b, lst_eqb a b = true <-> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b]; simpl; split; intros H; try discriminate; auto.
  - apply andb_prop in H as [H1 H2]. apply Nat.eqb_eq in H1. apply IH in H2. subst. auto.
  - injection H as -> ->. rewrite Nat.eqb_refl. simpl. apply IH. auto.
Qed.

Section E.
Variable t : nat.
Variables (i : instr) (r : regs) (m m' : mst) (a : val) (K : view) (u : cell -> option nat) (w : bool).
Hypothesis H : eff t i r m m' a K u w.

Ltac eff_t := destruct H; repeat match goal with m0 := _ |- _ => subst m0 end;
  unfold vsub, vor, srcs, carrieds, srcv, learn, wput, gpre, gpost, xgop, xload, nosrc in *; simpl in *;
  intros; try discriminate; firstorder (try congruence).

Lemma eff_K_P : vsub (mP m) K.
Proof. eff_t. Qed.

Lemma eff_K_P' : vsub K (mP m').
Proof. eff_t. Qed.

Lemma eff_P_mono : vsub (mP m) (mP m').
Proof. intros x Hx. apply eff_K_P'. apply eff_K_P. exact Hx. Qed.

Lemma eff_src : vsub (srcv u w t) (mP m').
Proof.
  intros y Hy. unfold srcv, vor, srcs in Hy.
  destruct H; repeat match goal with m0 := _ |- _ => subst m0 end;
  unfold nosrc, vor, vone, srcs, learn, wput, gpre, gpost in *; simpl in *;
  destruct Hy as [(x & Hx)|Hy]; try discriminate; try contradiction; eauto.
  all: unfold vor, srcs, vone in *; simpl in *; eauto 6.
Qed.

(* what later stores carry is within what the context knows or received *)
Lemma eff_R : vsub (mR m) (vor (mP m) (mA m)) -> vsub (mR m') (vor (mP m') (mA m')).
Proof.
  intros RP y Hy. destruct H; repeat match goal with m0 := _ |- _ => subst m0 end;
  unfold vor, learn, wput, gpre, gpost in *; simpl in *; unfold vor in *;
  first [ tauto
        | (pose proof (RP y Hy) as Q; cbv beta in Q; tauto)
        | (destruct Hy as [Hy|Hy]; [pose proof (RP y Hy) as Q; cbv beta in Q; tauto|tauto]) ].
Qed.

(* and it only grows (guard() sets it to P, which holds it) *)
Lemma eff_R_mono : vsub (mR m) (vor (mP m) (mA m)) -> vsub (mR m) (mR m').
Proof.
  intros RP y Hy. destruct H; repeat match goal with m0 := _ |- _ => subst m0 end;
  unfold vor, learn, wput, gpre, gpost in *; simpl in *; unfold vor in *;
  first [ tauto | (pose proof (RP y Hy) as Q; cbv beta in Q; tauto) ].
Qed.

Lemma eff_A : vsub (mA m) (mA m').
Proof. eff_t. Qed.

Lemma eff_G : vsub (mG m) (mG m').
Proof. eff_t. Qed.

Lemma eff_gop : xgop i r = true ->
  vsub (mA m) K /\ vsub (mG m) K /\ vsub (mP m') (mG m') /\ vsub (mP m') (mR m').
Proof.
  intros X; destruct H; unfold xgop in X; simpl in X; try discriminate X;
  try (destruct i as [| | |[]|]; simpl in *; try discriminate X; congruence).
  unfold vsub, vor, gpre, gpost; simpl; firstorder.
Qed.

Lemma eff_gA : xgop i r = true -> vsub (mA m') (mP m').
Proof.
  intros X; destruct H; unfold xgop in X; simpl in X; try discriminate X;
  try (destruct i as [| | |[]|]; simpl in *; try discriminate X; congruence).
  unfold vsub, vor, gpre, gpost; simpl; firstorder.
Qed.

Lemma eff_ll : i = IFn FLl -> vsub (mA m) (mP m').
Proof. intros E. subst i. inversion H; subst; unfold vsub, vor; simpl in *; auto; congruence. Qed.

Lemma eff_ss : i = IFn FSs -> vsub (fun w => mP m w /\ mW m w) (mR m').
Proof. intros E. subst i. inversion H; subst; unfold vsub, vor; simpl in *; auto; congruence. Qed.

Lemma eff_carr_A : xload i r = true -> vsub (carrieds m u) (mA m').
Proof. eff_t. Qed.

Lemma eff_nowrite : w = false -> mH m' = mH m /\ mV m' = mV m /\ mC m' = mC m.
Proof.
  intros E; destruct H; try discriminate; repeat match goal with m0 := _ |- _ => subst m0 end;
  simpl; auto.
Qed.

Lemma eff_read : xload i r = true ->
  takes (mH m) (icells i) u /\ a = areg i w (enc (rdvals m (icells i) u)).
Proof.
  unfold xload; intros X; destruct H;
  try (match goal with Hc : icond _ _ = false |- _ => rewrite Hc, andb_false_r in X; discriminate end);
  try (simpl in X; discriminate);
  repeat match goal with m0 := _ |- _ => subst m0 end; simpl; auto.
Qed.

Lemma eff_noread : xload i r = false -> a = 0 /\ forall x, u x = None.
Proof.
  unfold xload; destruct H; simpl; intros X; unfold icond, ieval in X; simpl in X; auto; try congruence.
Qed.

Lemma eff_ucells : forall x, ~ In x (icells i) -> u x = None.
Proof.
  intros x N. destruct H; simpl in *; auto; match goal with Hr : takes _ _ _ |- _ => destruct Hr as (_ & Hr); auto end.
Qed.

Lemma eff_K : xgop i r = false -> K = mP m.
Proof.
  unfold xgop; destruct H; simpl; intros X; unfold icond, ieval in X; simpl in X; auto;
  repeat match goal with m0 := _ |- _ => subst m0 end;
  try (destruct md; simpl in *; auto; congruence); discriminate.
Qed.

Lemma eff_write : w = true -> exists H' R0,
  is_store i = true /\ icond i r = true /\
  mH m' = H' /\ (forall x, ~ In x (icells i) -> H' x = mH m x) /\
  (forall x, In x (icells i) -> exists h1 h2, mH m x = h1 ++ h2 /\ H' x = h1 ++ (t, false) :: h2) /\
  mV m' = upd (mV m) t (cval (icells i) (wvals i r)) /\ mC m' = upd (mC m) t (vor R0 (vone t)) /\
  vsub (mR m) R0 /\ (xgop i r = true -> vsub K R0) /\
  vsub R0 (vor (vor (vor (mP m) (mA m)) (mG m)) (mR m)) /\
  (is_cas i = true -> enc (rdvals m (icells i) u) = eval_e i r).
Proof.
  intros E; destruct H; try discriminate; repeat match goal with m0 := _ |- _ => subst m0 end.
  - exists H', (mR m). simpl. split; [auto|]. split; [unfold icond; simpl; auto|]. split; [auto|]. split.
    { intros x N. apply (proj2 (H1 x) N). }
    split; [intros x I; exact (proj1 (H1 x) I)|].
    unfold wvals; simpl. repeat split; auto; unfold vsub, vor; simpl; intros; auto; try discriminate;
      try (left; left; left; auto).
  - exists H', (mR m). simpl. split; [auto|]. split; [unfold icond; simpl; auto|]. split; [auto|]. split.
    { intros x N. apply (proj2 (H3 x) N). }
    split; [intros x I; exact (proj1 (H3 x) I)|].
    unfold wvals; simpl. repeat split; auto; unfold vsub, vor; simpl; intros; auto; try discriminate;
      try (left; left; left; auto).
Qed.

Definition old4 (m : mst) : view := vor (vor (vor (vor (mP m) (mA m)) (mG m)) (mR m)) (mW m).

Lemma eff_views : forall y,
  (mP m' y \/ mA m' y \/ mR m' y \/ mG m' y \/ K y) ->
  old4 m y \/ (exists x, u x = Some y) \/ (exists x z, u x = Some z /\ mC m z y) \/ (w = true /\ y = t).
Proof.
  intros y Hy. unfold old4.
  destruct H; repeat match goal with m0 := _ |- _ => subst m0 end;
  unfold vor, vone, srcs, carrieds, nosrc, learn, wput, gpre, gpost, upd in *; simpl in *;
  unfold vor, vone, srcs, carrieds, nosrc in *; simpl in *;
  repeat match goal with
  | Hx : _ \/ _ |- _ => destruct Hx
  | Hx : exists _, _ |- _ => destruct Hx
  | Hx : _ /\ _ |- _ => destruct Hx
  end; subst;
  first [ solve [left; tauto] | solve [right; left; eexists; eauto] | solve [right; right; left; do 2 eexists; eauto]
        | solve [right; right; right; auto] | discriminate ].
Qed.

Lemma eff_K_old : vsub K (old4 m).
Proof.
  unfold old4. destruct H; repeat match goal with m0 := _ |- _ => subst m0 end;
  unfold vsub, vor, gpre, gpost in *; simpl in *; firstorder.
Qed.

Lemma eff_u : forall x y, u x = Some y -> xload i r = true.
Proof.
  intros x y E. destruct (xload i r) eqn:X; auto. destruct (eff_noread X) as [_ U]. rewrite U in E. discriminate.
Qed.

Lemma eff_w_spec : w = (is_store i && icond i r &&
  (negb (is_cas i) || (Nat.eqb (enc (rdvals m (icells i) u)) (eval_e i r) && w))).
Proof.
  destruct H; repeat match goal with m0 := _ |- _ => subst m0 end;
  unfold icond, ieval in *; simpl in *; try rewrite H0; simpl; auto.
  - rewrite H1, andb_false_r; reflexivity.
  - destruct md; simpl in *; rewrite H2, Nat.eqb_refl; reflexivity.
  - destruct md; simpl in *; rewrite andb_false_r; reflexivity.
Qed.

End E.

Lemma eff_w_cas : forall t i r m m' a K u w, eff t i r m m' a K u w -> is_cas i = true -> w = true ->
  Nat.eqb (enc (rdvals m (icells i) u)) (cexp i r) = true.
Proof.
  intros t i r m m' a K u w H C Wt. inversion H; subst; simpl in *; try discriminate.
  apply Nat.eqb_eq. assumption.
Qed.
