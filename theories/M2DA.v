(* Model M2DA for spec 0.1 §2.3.4: a joint access happens only in parts. The model of
   M2DA is M2Model's step with one restriction: no step makes a CAS's slot
   happen (oc) unless its read happened alone (oh) before, i.e. s_ord and
   s_early do not take a CAS as a whole; s_cread, s_cw, s_cwe, s_skip, s_cfix
   and every non-CAS step are kept unchanged. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model.

Definition nowhole (s s' : st) : Prop :=
  forall c k, oc (cs s c) k = None -> oc (cs s' c) k <> None -> is_cas (ai (cs s' c) k) = true ->
    oh (cs s c) k <> None.

Inductive runD (p : prog) : st -> Prop :=
| d0 : runD p sinit
| dS : forall s s', runD p s -> step p s s' -> nowhole s s' -> runD p s'.

Lemma runD_run : forall p s, runD p s -> run p s.
Proof. intros p s R. induction R; econstructor; eauto. Qed.

(* a step that leaves every oc as it was is no whole CAS *)
Lemma nowhole_oc : forall s s', (forall c k, oc (cs s' c) k = oc (cs s c) k) -> nowhole s s'.
Proof. intros s s' E c k O O' _. rewrite E in O'. congruence. Qed.

(* a step that changes oc only where a read happened alone is no whole CAS *)
Lemma nowhole_at : forall s s', (forall c k, oc (cs s' c) k <> oc (cs s c) k -> oh (cs s c) k <> None) ->
  nowhole s s'.
Proof. intros s s' E c k O O' _. apply E. congruence. Qed.

Lemma upd_o : forall {A} (f : nat -> A) k v, upd f k v k = v.
Proof. intros. unfold upd. rewrite Nat.eqb_refl. reflexivity. Qed.
Lemma upd_n : forall {A} (f : nat -> A) k v k', k' <> k -> upd f k v k' = f k'.
Proof. intros. unfold upd. destruct (Nat.eqb_spec k' k); [congruence|reflexivity]. Qed.

(* runs built forward *)
Inductive starD (p : prog) : st -> st -> Prop :=
| sd0 : forall s, starD p s s
| sdS : forall s s1 t, step p s s1 -> nowhole s s1 -> starD p s1 t -> starD p s t.

Lemma starD_run : forall p s t, runD p s -> starD p s t -> runD p t.
Proof. intros p s t R H. induction H; auto. apply IHstarD. econstructor; eauto. Qed.

Lemma startD : forall p (Q : st -> Prop), (exists t, starD p sinit t /\ Q t) -> exists t, runD p t /\ Q t.
Proof. intros p Q (t & H & q). exists t. split; auto. eapply starD_run; eauto. constructor. Qed.

Lemma fwdD : forall p s s1 (Q : st -> Prop), step p s s1 -> nowhole s s1 -> (exists t, starD p s1 t /\ Q t) ->
  exists t, starD p s t /\ Q t.
Proof. intros p s s1 Q H N (t & A & B). exists t. split; auto. econstructor; eauto. Qed.
