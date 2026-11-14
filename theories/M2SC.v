(* Model2: facts about sequential interleavings. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv.

Definition evshape (i : instr) (r : regs) (k : nat) : option (list cell * bool) * bool :=
  match i with
  | ILd md xs c => if c r then (Some (dd xs, false), false) else (None, false)
  | ISt md xs c _ => if c r then (Some (dd xs, true), false) else (None, false)
  | ICas md xs c e _ => if c r then (Some (dd xs, vok (r k)), false) else (None, false)
  | IFn f => (None, match f with FFull => true | _ => false end)
  | INop => (None, false)
  end.

Lemma evshape_ext : forall i r r' k, ieval i r = ieval i r' -> r k = r' k ->
  evshape i r k = evshape i r' k.
Proof.
  intros [] r r' k H K; simpl in *; try reflexivity; injection H; intros; rewrite ?H0, ?H1, ?H2, ?K; reflexivity.
Qed.

Definition writes_x (e : sev) (x : cell) : bool :=
  match sacc e with Some (ys, true) => existsb (Nat.eqb x) ys | _ => false end.

Fixpoint lwr (rl : list sev) (x : cell) : option sev :=
  match rl with [] => None | e :: rl' => if writes_x e x then Some e else lwr rl' x end.
Definition lw (l : list sev) (x : cell) : option sev := lwr (rev l) x.

Lemma lw_app : forall l e x, lw (l ++ [e]) x = if writes_x e x then Some e else lw l x.
Proof. intros. unfold lw. rewrite rev_app_distr. reflexivity. Qed.

Lemma wf_ins : forall p c k r r', wf p -> (forall j, j < k -> r j = r' j) -> ins p c k r = ins p c k r'.
Proof. intros. apply H; auto. Qed.

Lemma wf_ieval : forall p c k i r r', wf p -> ins p c k r = i ->
  (forall j, j < k -> r j = r' j) -> ieval i r = ieval i r'.
Proof. intros. subst. apply H; auto. Qed.

Section S.
Variable p : prog.
Hypothesis W : wf p.

(* the new register file of a step *)
Lemma sstep_shape : forall s e s', sstep p s e s' ->
  exists i, ins p (sx e) (sk e) (sr s (sx e)) = i /\ ins p (sx e) (sk e) (sr s' (sx e)) = i /\
    sk e = sp s (sx e) /\
    sp s' = upd (sp s) (sx e) (S (sp s (sx e))) /\
    (forall c j, c <> sx e \/ j <> sk e -> sr s' c j = sr s c j) /\
    (if xload i (sr s (sx e)) then rval i (sr s' (sx e) (sk e)) = enc (map (sm s) (icells i))
     else sr s' (sx e) (sk e) = sr s (sx e) (sk e)) /\
    (forall y, sm s' y = if writes_x e y then cval (icells i) (wvals i (sr s (sx e))) y else sm s y) /\
    (forall y, writes_x e y = true -> In y (icells i)) /\
    (sacc e, sg e) = evshape i (sr s' (sx e)) (sk e).
Proof.
  intros s e s' H.
  assert (U : forall c k a c' j, c' <> c \/ j <> k -> upd (sr s) c (upd (sr s c) k a) c' j = sr s c' j).
  { intros c k a c' j N. unfold upd. destruct (Nat.eqb_spec c' c); auto. subst.
    destruct (Nat.eqb_spec j k); auto. lia. }
  assert (UE : forall c k a, upd (sr s) c (upd (sr s c) k a) c k = a).
  { intros. unfold upd. rewrite !Nat.eqb_refl. reflexivity. }
  assert (EV : forall c k i a, ins p c k (sr s c) = i ->
            ieval i (upd (sr s) c (upd (sr s c) k a) c) = ieval i (sr s c)).
  { intros c k i a Hi. symmetry. eapply wf_ieval; eauto. intros j Hj. symmetry. apply U. right; lia. }
  assert (EI : forall c k a, ins p c k (upd (sr s) c (upd (sr s c) k a) c) = ins p c k (sr s c)).
  { intros c k a. apply wf_ins; auto. intros j Hj. apply U. right; lia. }
  assert (EX : forall y xs, existsb (Nat.eqb y) xs = true -> In y xs).
  { intros y xs Q. apply existsb_exists in Q. destruct Q as (z & Z & Q). apply Nat.eqb_eq in Q. subst. auto. }
  destruct H; simpl.
  - exists i. repeat split; auto.
    all: first [ reflexivity | (intros; reflexivity) | (intros; discriminate)
               | (unfold xload; rewrite H1, andb_false_r; reflexivity)
               | (destruct i; simpl in *; unfold icond, ieval in H1; simpl in H1;
                  first [rewrite H1; reflexivity | discriminate]) ].
  - exists (ILd md xs cnd). repeat split; auto.
    all: first [ (rewrite EI; auto)
               | (rewrite UE; unfold xload, icond, ieval; simpl; rewrite H0; reflexivity)
               | (intros y Y; discriminate)
               | (simpl; pose proof (EV c (sp s c) _ (enc (map (sm s) (dd xs))) H) as Q; simpl in Q; injection Q as Q;
                  rewrite Q, H0; reflexivity) ].
  - exists (ISt md xs cnd v). repeat split; auto.
    all: first [ (intros y; unfold mupd, writes_x; simpl; reflexivity)
               | (intros y Y; unfold writes_x in Y; simpl in *; apply EX; auto)
               | (simpl; rewrite H0; reflexivity) ].
  - exists (ICas md xs cnd e n). repeat split; auto.
    all: first [ (rewrite EI; auto)
               | (rewrite UE; unfold xload, icond, ieval; simpl; rewrite H0; reflexivity)
               | (unfold xload, icond, ieval; simpl; rewrite H0; simpl; rewrite UE; apply vv_vd)
               | (intros y; unfold writes_x; simpl; subst ok; destruct (Nat.eqb _ _), b; simpl; reflexivity)
               | (intros y Y; unfold writes_x in Y; simpl in *; destruct ok; [apply EX; auto|discriminate])
               | (simpl; pose proof (EV c (sp s c) _ (enc (map (sm s) (dd xs))) H) as Q; simpl in Q; injection Q as Q1 Q2 Q3;
                  rewrite Q1, H0, UE, vok_vd; reflexivity)
               | (unfold evshape; rewrite UE, vok_vd;
                  pose proof (EV c (sp s c) _ (vd ok (enc (map (sm s) (dd xs)))) H) as Q; simpl in Q; injection Q as Q1 Q2 Q3;
                  rewrite Q1, H0; reflexivity) ].
  - exists (IFn f). repeat split; auto.
  - exists INop. repeat split; auto.
Qed.

Lemma sstep_exists : forall s c i, ins p c (sp s c) (sr s c) = i ->
  exists e s', sstep p s e s' /\ sx e = c.
Proof.
  intros s c i H. destruct i.
  - destruct (c0 (sr s c)) eqn:E.
    + do 2 eexists. split; [eapply ss_ld; eauto|reflexivity].
    + do 2 eexists. split; [eapply ss_skip; eauto; try (simpl; congruence); unfold icond, ieval; simpl; auto|reflexivity].
  - destruct (c0 (sr s c)) eqn:E.
    + do 2 eexists. split; [eapply ss_st; eauto|reflexivity].
    + do 2 eexists. split; [eapply ss_skip; eauto; try (simpl; congruence); unfold icond, ieval; simpl; auto|reflexivity].
  - destruct (c0 (sr s c)) eqn:E.
    + do 2 eexists. split; [eapply ss_cas; eauto|reflexivity].
    + do 2 eexists. split; [eapply ss_skip; eauto; try (simpl; congruence); unfold icond, ieval; simpl; auto|reflexivity].
  - do 2 eexists. split; [eapply ss_fn; eauto|reflexivity].
  - do 2 eexists. split; [eapply ss_nop; eauto|reflexivity].
  Unshelve. all: exact true.
Qed.

(* ---------- facts about whole runs ---------- *)
Lemma srun_regs0 : forall l s, srun p l s -> forall c j, sp s c <= j -> sr s c j = 0.
Proof.
  intros l s R. induction R as [|l s e s' R IH H]; intros c j Hj; [reflexivity|].
  destruct (sstep_shape s e s' H) as (i & Hi & _ & Hk & Hsp & Hr & _).
  rewrite Hsp in Hj. rewrite Hr.
  - apply IH. unfold upd in Hj. destruct (Nat.eqb_spec c (sx e)); subst; lia.
  - unfold upd in Hj. destruct (Nat.eqb_spec c (sx e)); [right; lia|left; auto].
Qed.

Lemma srun_pos : forall l s, srun p l s -> forall c j,
  j < sp s c <-> exists q e, nth_error l q = Some e /\ sx e = c /\ sk e = j.
Proof.
  intros l s R. induction R as [|l s e s' R IH H]; intros c j.
  - simpl. split; [lia|intros (q & e & E & _); destruct q; discriminate].
  - destruct (sstep_shape s e s' H) as (i & Hi & _ & Hk & Hsp & _). rewrite Hsp.
    split.
    + intros Hj. unfold upd in Hj. destruct (Nat.eqb_spec c (sx e)).
      * subst c. destruct (Nat.eq_dec j (sp s (sx e))).
        -- exists (length l), e. rewrite nth_error_app2, Nat.sub_diag by lia. simpl. auto with arith.
           repeat split; auto. lia.
        -- destruct (proj1 (IH (sx e) j) ltac:(lia)) as (q & e' & A & B & C).
           exists q, e'. rewrite nth_error_app1; auto. apply nth_error_Some. congruence.
      * destruct (proj1 (IH c j) Hj) as (q & e' & A & B & C).
        exists q, e'. rewrite nth_error_app1; auto. apply nth_error_Some. congruence.
    + intros (q & e' & A & B & C). unfold upd. destruct (Nat.lt_ge_cases q (length l)).
      * rewrite nth_error_app1 in A by auto. assert (j < sp s c) by (apply IH; eauto).
        destruct (Nat.eqb_spec c (sx e)); [subst c; rewrite e0 in H1|]; lia.
      * rewrite nth_error_app2 in A by auto. destruct (q - length l) as [|z] eqn:Z;
          [|destruct z; discriminate]. simpl in A. injection A as <-. subst.
        rewrite Nat.eqb_refl. lia.
Qed.

Lemma srun_order : forall l s, srun p l s -> forall q1 q2 e1 e2,
  q1 < q2 -> nth_error l q1 = Some e1 -> nth_error l q2 = Some e2 -> sx e1 = sx e2 -> sk e1 < sk e2.
Proof.
  intros l s R. induction R as [|l s e s' R IH H]; intros q1 q2 e1 e2 Q A B C.
  - destruct q1; discriminate.
  - destruct (sstep_shape s e s' H) as (i & Hi & _ & Hk & _).
    assert (L1 : q1 < length l).
    { destruct (Nat.lt_ge_cases q1 (length l)); auto.
      rewrite nth_error_app2 in B by lia. destruct (q2 - length l) as [|z] eqn:Z; [lia|destruct z; discriminate]. }
    rewrite nth_error_app1 in A by auto.
    destruct (Nat.lt_ge_cases q2 (length l)).
    + rewrite nth_error_app1 in B by auto. exact (IH q1 q2 e1 e2 Q A B C).
    + rewrite nth_error_app2 in B by auto. destruct (q2 - length l) as [|z]; [|destruct z; discriminate].
      simpl in B. injection B as <-.
      assert (sk e1 < sp s (sx e1)) by (apply (srun_pos l s R); eauto). rewrite Hk, <- C. exact H1.
Qed.

(* the event recorded for an instruction, in terms of the final registers *)
Lemma srun_ev : forall l s, srun p l s -> forall q e, nth_error l q = Some e ->
  exists i, ins p (sx e) (sk e) (sr s (sx e)) = i /\ sk e < sp s (sx e) /\
    (sacc e, sg e) = evshape i (sr s (sx e)) (sk e).
Proof.
  intros l s R. induction R as [|l s e s' R IH H]; intros q e0 A.
  - destruct q; discriminate.
  - destruct (sstep_shape s e s' H) as (i & Hi & Hi2 & Hk & Hsp & Hr & Hrk & _ & _ & Hsh).
    destruct (Nat.lt_ge_cases q (length l)).
    + rewrite nth_error_app1 in A by auto. destruct (IH q e0 A) as (i0 & B & C & D).
      assert (E0 : forall j, j <= sk e0 -> sr s' (sx e0) j = sr s (sx e0) j).
      { intros j Hj. apply Hr. destruct (Nat.eq_dec (sx e0) (sx e)); [right|left]; auto.
        rewrite Hk. rewrite <- e1. lia. }
      exists i0. split. { rewrite <- B. apply wf_ins; auto. intros j Hj. apply E0. lia. } split.
      * rewrite Hsp. unfold upd. destruct (Nat.eqb_spec (sx e0) (sx e)) as [E1|E1]; [rewrite <- E1|]; lia.
      * rewrite D. (* registers up to sk e0 unchanged *)
        assert (E : forall j, j <= sk e0 -> sr s' (sx e0) j = sr s (sx e0) j).
        { intros j Hj. apply Hr. destruct (Nat.eq_dec (sx e0) (sx e)); [right|left]; auto.
          rewrite Hk. rewrite <- e1. lia. }
        assert (F : ieval i0 (sr s' (sx e0)) = ieval i0 (sr s (sx e0))).
        { symmetry. apply (wf_ieval p (sx e0) (sk e0) i0 (sr s (sx e0)) (sr s' (sx e0)) W B).
          intros j Hj. symmetry. apply E. lia. }
        symmetry. apply evshape_ext; auto.
    + rewrite nth_error_app2 in A by auto. destruct (q - length l) as [|z]; [|destruct z; discriminate].
      simpl in A. injection A as <-. exists i. split; auto. split; auto.
      rewrite Hsp, Hk. unfold upd. rewrite Nat.eqb_refl. lia.
Qed.

Lemma srun_mem : forall l s, srun p l s -> forall x,
  (lw l x = None -> sm s x = 0) /\
  (forall e, lw l x = Some e -> exists i, ins p (sx e) (sk e) (sr s (sx e)) = i /\
     sm s x = cval (icells i) (wvals i (sr s (sx e))) x).
Proof.
  intros l s R. induction R as [|l s e s' R IH H]; intros x.
  - split; [reflexivity|intros e E; discriminate].
  - destruct (sstep_shape s e s' H) as (i & Hi & Hi2 & Hk & Hsp & Hr & Hrk & Hm & Hw & Hsh).
    rewrite lw_app.
    assert (AG : forall e0, (exists q, nth_error l q = Some e0) -> forall j, j < sk e0 ->
              sr s' (sx e0) j = sr s (sx e0) j).
    { intros e0 (q & Q) j Hj.
      apply Hr. destruct (Nat.eq_dec (sx e0) (sx e)) as [EE|EE]; [right|left]; auto.
      assert (sk e0 < sp s (sx e0)) by (apply (srun_pos l s R); eauto). rewrite Hk, <- EE. lia. }
    assert (ST : forall e0 i0, (exists q, nth_error l q = Some e0) -> ins p (sx e0) (sk e0) (sr s (sx e0)) = i0 ->
              wvals i0 (sr s' (sx e0)) = wvals i0 (sr s (sx e0))).
    { intros e0 i0 Qe Hi0. apply ieval_wvals. symmetry. eapply wf_ieval; eauto. intros j Hj.
      symmetry. apply AG; auto. }
    assert (WI : wvals i (sr s' (sx e)) = wvals i (sr s (sx e))).
    { apply ieval_wvals. symmetry. apply (wf_ieval p (sx e) (sk e) i (sr s (sx e)) (sr s' (sx e)) W Hi).
      intros j Hj. symmetry. apply Hr. right. lia. }
    rewrite (Hm x). destruct (writes_x e x) eqn:X.
    + split; [discriminate|]. intros e0 E. injection E as <-. exists i. split; auto.
      rewrite WI. reflexivity.
    + destruct (IH x) as [A B]. split; auto.
      intros e0 E. destruct (B e0 E) as (i0 & C & D).
      assert (Qe : exists q, nth_error l q = Some e0).
      { clear -E. unfold lw in E.
        assert (G : forall rl, lwr rl x = Some e0 -> In e0 rl).
        { induction rl; simpl; [discriminate|]. destruct (writes_x a x); [intros F; injection F; auto|auto]. }
        apply G in E. apply in_rev in E. apply In_nth_error in E. auto. }
      exists i0. split. { rewrite <- C. apply wf_ins; auto. }
      rewrite D. rewrite ST; auto.
Qed.

Lemma lw_spec : forall l x e, lw l x = Some e -> exists q, nth_error l q = Some e /\ writes_x e x = true /\
  forall q' e', q < q' -> nth_error l q' = Some e' -> writes_x e' x = false.
Proof.
  intros l x. induction l as [|e0 l IH] using rev_ind; intros e E; [discriminate|].
  rewrite lw_app in E. destruct (writes_x e0 x) eqn:X.
  - injection E as <-. exists (length l). rewrite nth_error_app2, Nat.sub_diag by lia. simpl.
    split; auto. split; auto. intros q' e' Q F. rewrite nth_error_app2 in F by lia.
    destruct (q' - length l) as [|z] eqn:Z; [lia|destruct z; discriminate].
  - destruct (IH e E) as (q & A & B & C). exists q. rewrite nth_error_app1 by (apply nth_error_Some; congruence).
    split; auto. split; auto. intros q' e' Q F. destruct (Nat.lt_ge_cases q' (length l)).
    + rewrite nth_error_app1 in F by auto. eauto.
    + rewrite nth_error_app2 in F by auto. destruct (q' - length l) as [|z]; [|destruct z; discriminate].
      simpl in F. injection F as <-. auto.
Qed.

Lemma lw_none : forall l x, lw l x = None -> forall q e, nth_error l q = Some e -> writes_x e x = false.
Proof.
  intros l x. induction l as [|e0 l IH] using rev_ind; intros E q e F; [destruct q; discriminate|].
  rewrite lw_app in E. destruct (writes_x e0 x) eqn:X; [discriminate|].
  destruct (Nat.lt_ge_cases q (length l)).
  - rewrite nth_error_app1 in F by auto. eauto.
  - rewrite nth_error_app2 in F by auto. destruct (q - length l) as [|z]; [|destruct z; discriminate].
    simpl in F. injection F as <-. auto.
Qed.

End S.
