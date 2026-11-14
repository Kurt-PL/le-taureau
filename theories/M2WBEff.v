(* Write-back, part 3: what an instruction does in sW is done in sA, with the reads the
   same value (a read of a write-back store takes the write it stands for). *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2WBReg M2WBRel.

Lemma takes_in : forall H xs u, takes H xs u -> forall x w, u x = Some w -> In w (ids (H x)).
Proof.
  intros H xs u [T1 T2] x w E. destruct (in_dec Nat.eq_dec x xs) as [I|N].
  - specialize (T1 x I). rewrite E in T1. exact T1.
  - rewrite (T2 x N) in E. discriminate.
Qed.

Section E.
Variables (sw : nat -> option (cell -> option nat)) (sW sA : st) (c : nat).
Hypothesis R : rel sw sW sA.
Let mw := mof sW c.
Let ma := mof sA c.

Lemma mH_W : mH mw = hs sW. Proof. reflexivity. Qed.
Lemma mH_A : mH ma = hs sA. Proof. reflexivity. Qed.

(* a read through pi takes the same values *)
Lemma rdvals_pi : forall xs u uA, (forall x, uA x = pi sw x (u x)) -> takes (hs sW) xs u ->
  rdvals ma xs uA = rdvals mw xs u.
Proof.
  intros xs u uA Hu T. unfold rdvals. apply map_ext. intros x. unfold rdval. cbn [mV ma mw mof]. rewrite (Hu x).
  destruct (u x) as [w|] eqn:E; [|reflexivity]. simpl.
  destruct (pi_in sw sW sA x w R (takes_in _ _ _ T x w E)) as [V _]. rewrite V. reflexivity.
Qed.

Lemma takes_pi : forall xs u uA, (forall x, uA x = pi sw x (u x)) -> takes (hs sW) xs u -> takes (hs sA) xs uA.
Proof.
  intros xs u uA Hu T. split.
  - intros x Ix. rewrite (Hu x). destruct (u x) as [w|] eqn:E; [|exact I]. simpl.
    exact (pi_inm sw sW sA x w R (takes_in _ _ _ T x w E)).
  - intros x Nx. rewrite (Hu x), (proj2 T x Nx). reflexivity.
Qed.

Lemma rdval_pi : forall xs u uA x, (forall x, uA x = pi sw x (u x)) -> takes (hs sW) xs u -> rdval ma uA x = rdval mw u x.
Proof.
  intros xs u uA x Hu T. unfold rdval. cbn [mV ma mw mof]. rewrite (Hu x). destruct (u x) as [w|] eqn:E; [|reflexivity]. simpl.
  destruct (pi_in sw sW sA x w R (takes_in _ _ _ T x w E)) as [V _]. rewrite V. reflexivity.
Qed.

(* the placement in A of a write placed in sW *)
Lemma places_hers : forall xs t H', places (hs sW) xs t H' ->
  places (hs sA) xs t (fun x => hers (H' x)).
Proof.
  intros xs t H' P x. destruct (P x) as [P1 P2]. split.
  - intros Ix. destruct (P1 Ix) as (h1 & h2 & E1 & E2). exists (hers h1), (hers h2). split.
    + rewrite (r_hs sw sW sA R x), E1. apply hers_app.
    + rewrite E2. apply hers_ins_f.
  - intros Nx. rewrite (P2 Nx). rewrite (r_hs sw sW sA R x). reflexivity.
Qed.

Lemma places_in : forall H xs t H' x, places H xs t H' -> In x xs -> In t (ids (H' x)).
Proof.
  intros H xs t H' x P Ix. destruct (proj1 (P x) Ix) as (h1 & h2 & _ & E). rewrite E. apply in_ids_ins. left. reflexivity.
Qed.

Definition effout (t : nat) (i : instr) (w : bool) (m' : mst) (u : cell -> option nat) (m'A : mst) (uA : cell -> option nat) : Prop :=
  (forall x, uA x = pi sw x (u x)) /\
  (forall x, mH m'A x = hers (mH m' x)) /\
  (forall x w', u x = Some w' -> In w' (ids (hs sW x))) /\
  ((mV m' = mV mw /\ mV m'A = mV ma /\ forall x, mH m' x = mH mw x) \/
   exists V xs, mV m' = upd (mV mw) t V /\ mV m'A = upd (mV ma) t V /\ places (mH mw) xs t (mH m')) /\
  (forall x, rdval ma uA x = rdval mw u x) /\
  (w = true -> forall x, In x (icells i) -> In t (ids (mH m' x))).

Ltac fence_case HH :=
  eexists; eexists; exists nosrc; split;
  [ first [ (apply e_skip; eassumption) | apply e_ll | apply e_ss | apply e_ls | apply e_sl | apply e_full | apply e_nop ] |
    unfold effout; split; [ intros x; reflexivity | split; [ intros x; apply HH | split; [ intros x w' E; discriminate | split; [ left; refine (conj eq_refl (conj eq_refl (fun x => eq_refl))) | split; [intros x; reflexivity | intros Hw; discriminate ] ] ] ] ] ].

Lemma eff_transfer : forall t i r m' a K u w, eff t i r mw m' a K u w ->
  exists m'A KA uA, eff t i r ma m'A a KA uA w /\ effout t i w m' u m'A uA.
Proof.
  intros t i r m' a K u w H.
  assert (HH : forall x, mH ma x = hers (mH mw x)) by (intros x; exact (r_hs sw sW sA R x)).
  inversion H; subst.
  - fence_case HH.
  - exists (learn ma (fun x => pi sw x (u x))), (mP ma), (fun x => pi sw x (u x)).
    pose proof (rdvals_pi _ _ _ (fun _ => eq_refl) H1) as RV.
    split; [rewrite <- RV; apply e_ld; [assumption|]; apply (takes_pi _ _ _ (fun _ => eq_refl) H1)|].
    unfold effout. split; [intros; reflexivity|split; [intros x; apply HH|split; [apply (takes_in _ _ _ H1)|split; [left; refine (conj eq_refl (conj eq_refl (fun x => eq_refl)))|split; [intros x; apply (rdval_pi _ _ _ x (fun _ => eq_refl) H1)|intros Hw; discriminate]]]]].
  - exists (wput ma (dd xs) t (projs (length (dd xs)) (v r)) (fun x => hers (H' x))), (mP ma), nosrc.
    split; [apply e_st; [assumption|]; apply places_hers; exact H1|].
    unfold effout. split; [intros x; reflexivity|split; [intros x; reflexivity|split; [intros x w' E; discriminate|split; [right; exists (cval (dd xs) (projs (length (dd xs)) (v r))), (dd xs); split; [reflexivity|split; [reflexivity|exact H1]]|split; [intros x; reflexivity|intros Hw x Ix; apply (places_in _ _ _ _ x H1); simpl in Ix; exact Ix]]]]].
  - exists (wput (learn ma (fun x => pi sw x (u x))) (dd xs) t (projs (length (dd xs)) (n r)) (fun x => hers (H' x))), (mP ma), (fun x => pi sw x (u x)).
    pose proof (rdvals_pi _ _ _ (fun _ => eq_refl) H1) as RV.
    split; [rewrite <- RV; apply e_cas_ok; [assumption|apply (takes_pi _ _ _ (fun _ => eq_refl) H1)|rewrite RV; assumption|apply places_hers; exact H3]|].
    unfold effout. split; [intros; reflexivity|split; [intros x; reflexivity|split; [apply (takes_in _ _ _ H1)|split; [right; exists (cval (dd xs) (projs (length (dd xs)) (n r))), (dd xs); split; [reflexivity|split; [reflexivity|exact H3]]|split; [intros x; apply (rdval_pi _ _ _ x (fun _ => eq_refl) H1)|intros Hw x Ix; apply (places_in _ _ _ _ x H3); simpl in Ix; exact Ix]]]]].
  - exists (learn ma (fun x => pi sw x (u x))), (mP ma), (fun x => pi sw x (u x)).
    pose proof (rdvals_pi _ _ _ (fun _ => eq_refl) H1) as RV.
    split; [rewrite <- RV; apply e_cas_no; [assumption|apply (takes_pi _ _ _ (fun _ => eq_refl) H1)]|].
    unfold effout. split; [intros; reflexivity|split; [intros x; apply HH|split; [apply (takes_in _ _ _ H1)|split; [left; refine (conj eq_refl (conj eq_refl (fun x => eq_refl)))|split; [intros x; apply (rdval_pi _ _ _ x (fun _ => eq_refl) H1)|intros Hw; discriminate]]]]].
  - fence_case HH.
  - fence_case HH.
  - fence_case HH.
  - fence_case HH.
  - fence_case HH.
  - fence_case HH.
Qed.

Lemma eff_transfer_cas : forall t i r m' a K u, eff t i r mw m' a K u true -> is_cas i = true ->
  forall uA, (forall x, uA x = pi sw x (u x)) ->
  exists m'A KA, eff t i r ma m'A a KA uA true /\ effout t i true m' u m'A uA.
Proof.
  intros t i r m' a K u H Hc uA Hu.
  inversion H; subst; try (simpl in Hc; discriminate); try discriminate.
  pose proof (rdvals_pi _ _ _ Hu H1) as RV.
  exists (wput (learn ma uA) (dd xs) t (projs (length (dd xs)) (n r)) (fun x => hers (H' x))), (mP ma).
  split; [rewrite <- RV; apply e_cas_ok; [assumption|apply (takes_pi _ _ _ Hu H1)|rewrite RV; assumption|apply places_hers; exact H3]|].
  unfold effout. split; [exact Hu|split; [intros x; reflexivity|split; [apply (takes_in _ _ _ H1)|split; [right; exists (cval (dd xs) (projs (length (dd xs)) (n r))), (dd xs); split; [reflexivity|split; [reflexivity|exact H3]]|split; [intros x; apply (rdval_pi _ _ _ x Hu H1)|intros Hw x Ix; apply (places_in _ _ _ _ x H3); simpl in Ix; exact Ix]]]]].
Qed.
End E.
