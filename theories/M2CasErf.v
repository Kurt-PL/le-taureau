(* M2CasErf: a CAS whose two halves both happened recorded the same read in both log entries.

   In every run state, if the slot of a CAS has oh = Some t1 (its read alone) and oc = Some t2
   (its write), the log entries at t1 and t2 have the same erf (the writes the CAS took, per
   cell). The write half (s_cw, s_cwe) takes u = rw cc k, which is what the read half
   recorded (i_rw, with ew = false for a read half, j_ew). This is a fact about the CAS
   itself; the ARM and POWER evok proofs need it to read the write entry's source. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2.

Definition ErfEq (s : st) : Prop :=
  forall c k t1 t2, oh (cs s c) k = Some t1 -> oc (cs s c) k = Some t2 ->
    exists E1 E2, ent s t1 = Some E1 /\ ent s t2 = Some E2 /\ erf E1 = erf E2.

(* a state with the same oc, oh and log *)
Lemma erf_same : forall s s', lg s' = lg s ->
  (forall c k, oc (cs s' c) k = oc (cs s c) k /\ oh (cs s' c) k = oh (cs s c) k) -> ErfEq s -> ErfEq s'.
Proof.
  intros s s' L F H c k t1 t2 H1 H2. destruct (F c k) as (F1 & F2). rewrite F2 in H1. rewrite F1 in H2.
  destruct (H c k t1 t2 H1 H2) as (E1 & E2 & A & B & C). exists E1, E2. unfold ent in *. rewrite L. auto.
Qed.

(* a state whose log is the old one and one more entry *)
Lemma ent_new : forall p s s' e, Inv1 p s -> lg s' = lg s ++ [e] ->
  (forall x, x < tm s -> ent s' x = ent s x) /\ ent s' (tm s) = Some e.
Proof.
  intros p s s' e I L. pose proof (i_tm p s I) as Tm. split.
  - intros x X. unfold ent. rewrite L. rewrite nth_error_app1; [reflexivity|lia].
  - unfold ent. rewrite L. rewrite nth_error_app2 by lia. rewrite Tm, Nat.sub_diag. reflexivity.
Qed.

Lemma erf_evs : forall p s c k i m' a K u w B pc' tp' cm', Inv1 p s -> Inv2 p s -> ErfEq s -> oc (cs s c) k = None ->
  (oh (cs s c) k = None \/ (exists t1, oh (cs s c) k = Some t1 /\ u = rw (cs s c) k)) ->
  ErfEq (evs s c k i m' a K u w B pc' tp' cm').
Proof.
  intros p s c k i m' a K u w B pc' tp' cm' I1 I2 H Ok Hh c' k' t1 t2 H1 H2.
  set (s' := evs s c k i m' a K u w B pc' tp' cm') in *.
  destruct (ent_new p s s' (newev s c k i K u w) I1 eq_refl) as (Eo & En).
  assert (Ooh : oh (cs s' c') k' = oh (cs s c') k').
  { unfold s', evs. simpl. unfold upd. destruct (Nat.eqb c' c) eqn:E; simpl; [apply Nat.eqb_eq in E; subst|]; reflexivity. }
  assert (Ooc : oc (cs s' c') k' = if Nat.eqb c' c && Nat.eqb k' k then Some (tm s) else oc (cs s c') k').
  { unfold s', evs. simpl. unfold upd. destruct (Nat.eqb c' c) eqn:E; simpl; [|reflexivity].
    apply Nat.eqb_eq in E. subst. destruct (Nat.eqb k' k); reflexivity. }
  rewrite Ooh in H1. rewrite Ooc in H2.
  destruct (Nat.eqb c' c && Nat.eqb k' k) eqn:Q.
  - apply andb_true_iff in Q as [Q1 Q2]. apply Nat.eqb_eq in Q1. apply Nat.eqb_eq in Q2. subst c' k'.
    injection H2 as <-.
    destruct Hh as [Hn|(t0 & Hs & Hu)]; [rewrite Hn in H1; discriminate|]. rewrite Hs in H1. injection H1 as E01. subst t0.
    destruct (i_oh p s I1 c k t1 Hs) as (E1 & Ent1 & Ec & Ek & Eh).
    destruct (i_rw p s I1 c k t1 (or_intror (conj Ok Hs))) as (E1' & Ent1' & Rw).
    rewrite Ent1 in Ent1'. injection Ent1' as <-.
    assert (Ew : ew E1 = false).
    { destruct (j_ew p s I2 t1 E1 (einstr p s E1) Ent1 eq_refl) as (Q & _). rewrite Q, Eh. reflexivity. }
    rewrite Ew in Rw.
    assert (L1 : t1 < tm s) by exact (oh_lt_tm p s c k t1 I1 Hs).
    exists E1, (newev s c k i K u w). split; [rewrite (Eo _ L1); exact Ent1|]. split; [exact En|].
    rewrite Hu, Rw. reflexivity.
  - destruct (H c' k' t1 t2 H1 H2) as (E1 & E2 & A0 & B0 & C0). exists E1, E2.
    pose proof (oh_lt_tm p s c' k' t1 I1 H1) as L1. pose proof (oc_lt_tm p s c' k' t2 I1 H2) as L2.
    rewrite (Eo _ L1), (Eo _ L2). auto.
Qed.

Lemma erf_sread : forall p s c k xs B m' a K u w bv, Inv1 p s -> ErfEq s -> oc (cs s c) k = None ->
  ErfEq (sread s c k Plain xs B m' a K u w bv).
Proof.
  intros p s c k xs B m' a K u w bv I1 H Ok c' k' t1 t2 H1 H2.
  set (s' := sread s c k Plain xs B m' a K u w bv) in *.
  destruct (ent_new p s s' (newevh s c k (ILd Plain xs (fun _ => true)) K u w) I1 eq_refl) as (Eo & En).
  assert (Ooc : oc (cs s' c') k' = oc (cs s c') k').
  { unfold s', sread. simpl. unfold upd. destruct (Nat.eqb c' c) eqn:E; simpl; [apply Nat.eqb_eq in E; subst|]; reflexivity. }
  assert (Ooh : oh (cs s' c') k' = if Nat.eqb c' c && Nat.eqb k' k then Some (tm s) else oh (cs s c') k').
  { unfold s', sread. simpl. unfold upd. destruct (Nat.eqb c' c) eqn:E; simpl; [|reflexivity].
    apply Nat.eqb_eq in E. subst. destruct (Nat.eqb k' k); reflexivity. }
  rewrite Ooc in H2. rewrite Ooh in H1.
  destruct (Nat.eqb c' c && Nat.eqb k' k) eqn:Q.
  - apply andb_true_iff in Q as [Q1 Q2]. apply Nat.eqb_eq in Q1. apply Nat.eqb_eq in Q2. subst c' k'. rewrite Ok in H2. discriminate.
  - destruct (H c' k' t1 t2 H1 H2) as (E1 & E2 & A0 & B0 & C0). exists E1, E2.
    pose proof (oh_lt_tm p s c' k' t1 I1 H1) as L1. pose proof (oc_lt_tm p s c' k' t2 I1 H2) as L2.
    rewrite (Eo _ L1), (Eo _ L2). auto.
Qed.

Theorem erf_eq_run : forall p s, run p s -> ErfEq s.
Proof.
  intros p s R. induction R as [|s t R IH H].
  - intros c k t1 t2 H1. simpl in H1. discriminate.
  - destruct (Inv2_run p s R) as [I1 I2].
    destruct (step_cases p s t H) as [(c & i & m' & a & K & u & w & H1 & H2 & H3 & H4 & Hbh & Hh & _ & _ & H6 & _ & ->)|[(c & k & d & B & m' & a & K & u & w & H1 & H2 & Hso & Hh & _ & _ & H5 & _ & ->)|[(c & d & H1 & H2 & H3 & H4 & H4m & Hfh & ->)|[(c & k & xs & B & m' & a & K & u & w & bv & H1 & H2 & Hh & Hso & H4 & H5 & _ & ->)|[(c & S1 & S2 & S3 & _ & S5 & S4 & _ & ->)|(cX & jX & bX & BX & oX & HjX & HfX & HcX & ->)]]]]].
    + unfold sord. apply (erf_evs p s c (pcs s c) i m' a K u w _ _ _ _ I1 I2 IH H2).
      destruct Hh as [(Z & _)|(t1 & Z & Ci & U & Ef)]; [left; exact Z|right; exists t1; split; [exact Z|exact U]].
    + exact (erf_evs p s c k (inst_of d) m' a K u w (bor (bd (cs s c)) B) (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s) I1 I2 IH H2
        (match Hh with
         | or_introl (conj Z _) => or_introl Z
         | or_intror (ex_intro _ t1 (ex_intro _ xs (ex_intro _ ev (ex_intro _ nv (conj Z (conj _ (conj U _))))))) =>
             or_intror (ex_intro _ t1 (conj Z U))
         end)).
    + apply (erf_same s); [reflexivity| |exact IH]. intros c' k'. unfold smatch. simpl. unfold upd.
      destruct (Nat.eqb c' c) eqn:E; [apply Nat.eqb_eq in E; subst|]; simpl; split; reflexivity.
    + exact (erf_sread p s c k xs B m' a K u w bv I1 IH H2).
    + apply (erf_same s); [reflexivity| |exact IH]. intros c' k'. unfold sskip. simpl. unfold upd.
      destruct (Nat.eqb c' c) eqn:E; [apply Nat.eqb_eq in E; subst|]; simpl; split; reflexivity.
    + apply (erf_same s); [unfold scfix0; simpl; apply lg_flp| |exact IH]. intros c' k'.
      rewrite oc_cx, oh_cx, oc_flp, oh_flp. split; reflexivity.
Qed.

Print Assumptions erf_eq_run.

(* negative instance: ErfEq is not trivial. A state (not a run) whose CAS slot has both halves
   recorded but two log entries with different erf violates it. *)
Definition badE (t : nat) (u : cell -> option nat) (h : bool) : oev :=
  mkO t 0 0 (fun _ => False) u h [] [] (fun _ => False) (fun _ => False) h.
Definition badS : st :=
  let cc := cs sinit 0 in
  mkS 2 (fun _ => mkC (fun k => if Nat.eqb k 0 then Some 1 else None) (rg cc) (ai cc) (rw cc) (rv cc) (bd cc)
           (vP cc) (vA cc) (vR cc) (vO cc) (vOg cc) (fun k => if Nat.eqb k 0 then Some 0 else None) (fx cc))
      (wv sinit) (wc sinit) (hs sinit) (vG sinit) (pcs sinit) (tp sinit) (cm sinit)
      [badE 0 (fun _ => None) false; badE 1 (fun _ => Some 5) true] (es sinit).

Lemma badS_violates : ~ ErfEq badS.
Proof.
  intros H. destruct (H 0 0 0 1 eq_refl eq_refl) as (E1 & E2 & A & B & C).
  unfold ent, badS in A, B. simpl in A, B. injection A as <-. injection B as <-.
  simpl in C. exact (match f_equal (fun f => f 0) C with eq_refl => I end).
Qed.
