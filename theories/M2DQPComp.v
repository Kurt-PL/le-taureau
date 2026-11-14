(* M2PComp.v re-checked on M2DQ (stepQ) through M2DQShim; scripts as in M2PComp.v except where marked DQ. *)
(* Model2: facts about any run, indexed by the slots it has passed. The
   finished-run facts of M2Comp, without "finished": a slot counts once the
   context has passed it. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2SC M2DA M2DP M2DQ M2DQInv M2DQIface M2DQShim.

Set Default Proof Using "All".
Section C.
Variable p : prog.
Variable s : st.
Hypothesis R : run p s.
Hypothesis W : wf p.

Lemma IA : InvAll p s. Proof. apply Inv_run; auto. Qed.
Definition I1 := ia1 p s IA.
Definition I2 := ia2 p s IA.
Definition I3 := ia3 p s IA.

(* the time of a slot's event: its access, or the read of a CAS that failed *)
Definition bt (c j : nat) : nat := match tmo (cs s c) j with Some t => t | None => 0 end.
Definition rrg (c : nat) : regs := rg (cs s c).

(* the instruction at slot j of context c, once the context has passed it *)
Definition insr (c j : nat) : option instr :=
  if Nat.ltb j (pcs s c) then Some (ins p c j (rrg c)) else None.

Lemma insr_lt : forall c j i, insr c j = Some i -> j < pcs s c.
Proof. intros c j i H. unfold insr in H. destruct (Nat.ltb_spec j (pcs s c)); [auto|discriminate]. Qed.

Lemma insr_ins : forall c j i, insr c j = Some i -> ins p c j (rrg c) = i.
Proof. intros c j i H. unfold insr in H. destruct (Nat.ltb j (pcs s c)); congruence. Qed.

(* a passed instruction that executes happened *)
Lemma occ : forall c j i, insr c j = Some i -> executes i (rrg c) = true -> tmo (cs s c) j = Some (bt c j).
Proof.
  intros c j i H X. rewrite <- (insr_ins c j i H) in X.
  destruct (tmo_passed p s c j I1 (insr_lt c j i H) X) as (t & O & _).
  unfold bt. rewrite O. reflexivity.
Qed.

(* the entry at a slot's time *)
Lemma tmo_ent : forall c j t, tmo (cs s c) j = Some t -> exists e, ent s t = Some e /\ ec e = c /\ ek e = j.
Proof.
  intros c j t H. unfold tmo in H. destruct (oc (cs s c) j) as [t'|] eqn:O.
  - injection H as <-. apply (i_oc p s I1 c j t' O).
  - destruct (i_oh p s I1 c j t H) as (e & A & B & C & _). eauto.
Qed.

Lemma insr_of : forall c j, j < pcs s c -> insr c j = Some (ins p c j (rrg c)).
Proof. intros c j H. unfold insr. rewrite (proj2 (Nat.ltb_lt j (pcs s c)) H). reflexivity. Qed.

Lemma ent_of : forall c j i, insr c j = Some i -> executes i (rrg c) = true ->
  exists e, ent s (bt c j) = Some e /\ ec e = c /\ ek e = j /\ einstr p s e = i.
Proof.
  intros c j i H X. destruct (tmo_ent c j (bt c j) (occ c j i H X)) as (e & A & B & C).
  exists e. repeat split; auto. unfold einstr. rewrite B, C.
  destruct (proj1 (i_cmA p s I1 c j) (insr_lt c j i H)) as (tau & T).
  rewrite (proj2 (i_set p s I1 c j tau T)). apply insr_ins. auto.
Qed.

Lemma einstr_ins : forall t e, ent s t = Some e -> ek e < pcs s (ec e) ->
  einstr p s e = ins p (ec e) (ek e) (rrg (ec e)).
Proof.
  intros t e H Lj.
  destruct (proj1 (i_cmA p s I1 (ec e) (ek e)) Lj) as (tau & T).
  unfold einstr. apply (proj2 (i_set p s I1 (ec e) (ek e) tau T)).
Qed.

Lemma bt_inj : forall c1 j1 c2 j2 i1 i2, insr c1 j1 = Some i1 -> insr c2 j2 = Some i2 ->
  executes i1 (rrg c1) = true -> executes i2 (rrg c2) = true ->
  bt c1 j1 = bt c2 j2 -> c1 = c2 /\ j1 = j2.
Proof.
  intros c1 j1 c2 j2 i1 i2 H1 H2 X1 X2 E.
  destruct (ent_of c1 j1 i1 H1 X1) as (e1 & A1 & B1 & C1 & _).
  destruct (ent_of c2 j2 i2 H2 X2) as (e2 & A2 & B2 & C2 & _).
  rewrite E in A1. rewrite A1 in A2. injection A2 as <-. split; congruence.
Qed.

(* R1, read back: of two passed instructions tied to each other, the
   earlier, if it comes, happened first *)
Lemma tie_bt : forall c j k ij ik, j < k -> insr c j = Some ij -> insr c k = Some ik ->
  executes ij (rrg c) = true -> executes ik (rrg c) = true -> tied ij ik -> bt c j < bt c k.
Proof.
  intros c j k ij ik L Hj Hk Ex Ek T.
  pose proof (occ c j ij Hj Ex) as Oj. pose proof (occ c k ik Hk Ek) as Ok.
  rewrite <- (insr_ins c j ij Hj) in T, Ex. rewrite <- (insr_ins c k ik Hk) in T.
  destruct (i_pot p s I1 c j k (bt c k) L (insr_lt c k ik Hk) Ok Ex T) as (tj & A & B).
  rewrite Oj in A. injection A as <-. auto.
Qed.

Lemma det_bt : forall c j i r, insr c j = Some i ->
  (forall j', j' < j -> r j' = rrg c j') ->
  ins p c j r = i /\ ieval i r = ieval i (rrg c).
Proof.
  intros c j i r H Hr. rewrite <- (insr_ins c j i H).
  destruct (W c j r (rrg c) Hr) as [E1 E2]. rewrite E1. split; auto. rewrite <- E1. exact E2.
Qed.

(* the order in which slots were passed *)
Lemma cm_has : forall c j, j < pcs s c -> exists q tau, nth_error (cm s) q = Some (c, j, tau).
Proof.
  intros c j H. destruct (proj1 (i_cmA p s I1 c j) H) as (tau & T).
  apply In_nth_error in T. destruct T as (q & Q). eauto.
Qed.

Lemma cm_lt : forall q c j tau, nth_error (cm s) q = Some (c, j, tau) -> j < pcs s c.
Proof. intros q c j tau H. apply (i_cmA p s I1 c j). exists tau. eapply nth_error_In; eauto. Qed.

Lemma cm_ins : forall q c j tau, nth_error (cm s) q = Some (c, j, tau) ->
  exists i, insr c j = Some i.
Proof. intros q c j tau H. rewrite insr_of by (eapply cm_lt; eauto). eauto. Qed.

Lemma cm_unique : forall q1 q2 c j t1 t2, nth_error (cm s) q1 = Some (c, j, t1) ->
  nth_error (cm s) q2 = Some (c, j, t2) -> q1 = q2.
Proof.
  intros q1 q2 c j t1 t2 A B. destruct (Nat.lt_trichotomy q1 q2) as [L|[L|L]]; auto.
  - pose proof (i_cmB p s I1 q1 q2 c j j t1 t2 L A B). lia.
  - pose proof (i_cmB p s I1 q2 q1 c j j t2 t1 L B A). lia.
Qed.

Lemma cm_time_ge : forall q c j tau, nth_error (cm s) q = Some (c, j, tau) ->
  executes (ins p c j (rrg c)) (rrg c) = true -> bt c j <= tau.
Proof.
  intros q c j tau H X. apply nth_error_In in H.
  destruct (i_cmDt p s I1 c j tau H j (le_n j) X) as (t' & Y & Z). unfold bt. rewrite Y. auto.
Qed.

(* a passed slot that is no access, such as guard(), was passed when it happened *)
Lemma cm_noacc : forall q c j tau i, nth_error (cm s) q = Some (c, j, tau) -> insr c j = Some i ->
  executes i (rrg c) = true -> eof i (rrg c) = None -> tau = bt c j.
Proof.
  intros q c j tau i H Hi X D. rewrite <- (insr_ins c j i Hi) in D, X. apply nth_error_In in H.
  pose proof (i_cmF p s I1 c j tau H X D) as O. unfold bt, tmo. rewrite O. reflexivity.
Qed.

(* the relaxed event of a passed instruction, in the shape of a sequential event *)
Lemma ev_rel : forall c j i e, insr c j = Some i -> executes i (rrg c) = true ->
  ent s (bt c j) = Some e -> ec e = c -> ek e = j ->
  evshape i (rrg c) j =
  (if icond i (rrg c) && isacc i
   then Some (icells i, ew e)
   else None, xgop i (rrg c)).
Proof.
  intros c j i e H X A B C.
  assert (Ei : einstr p s e = i).
  { destruct (ent_of c j i H X) as (e' & A' & B' & C' & D'). rewrite A in A'. injection A' as <-. auto. }
  destruct (j_ew p s I2 (bt c j) e i A Ei) as [E1 _]. unfold rgof in E1. rewrite B in E1.
  destruct (eh e) eqn:Eh.
  { (* the read of a CAS that failed: no write *)
    cbn [negb andb] in E1. pose proof (occ c j i H X) as O. unfold tmo in O.
    destruct (oc (cs s c) j) as [t2|] eqn:O2.
    - exfalso. injection O as O. rewrite O in O2. rewrite (oc_eh p s c j (bt c j) e I1 O2 A B C) in Eh. discriminate.
    - destruct (i_halfp p s I1 c j _ O2 O (insr_lt c j i H)) as (F & _). pose proof (i_halfv p s I1 c j _ O2 O (insr_lt c j i H)) as VK.
      assert (Ai : ai (cs s c) j = i) by (rewrite <- Ei; unfold einstr; rewrite B, C; reflexivity).
      rewrite Ai in F. unfold rrg. destruct i as [| |md x cn ee n| |]; simpl in F; try discriminate.
      apply andb_true_iff in F as [CN _].
      unfold evshape, icond, ieval; simpl. rewrite CN, VK, E1. reflexivity. }
  cbn [negb andb] in E1.
  destruct (j_val p s I2 (bt c j) e i A Ei) as [V _]. unfold rgof in V. rewrite B, C in V.
  pose proof (j_ok p s I2 (bt c j) e A) as OKv. unfold rgof in OKv. rewrite Ei, B, C in OKv.
  unfold rrg. destruct i as [md x cn|md x cn v|md x cn ee n|f|];
  unfold icond, ieval, xgop, gop in *; simpl in *;
  try (destruct f; reflexivity); try reflexivity;
  destruct (cn (rg (cs s c))) eqn:CN; unfold icond, ieval; simpl in *; rewrite ?CN; try rewrite E1; simpl;
  rewrite ?andb_true_r, ?andb_false_r; try reflexivity.
  first [rewrite V by (unfold xload, icond, ieval; simpl; rewrite CN; reflexivity); reflexivity
        |rewrite (OKv Eh eq_refl ltac:(unfold xload, icond, ieval; simpl; rewrite CN; reflexivity)); first [reflexivity|rewrite E1 at 1; reflexivity]].
Qed.

End C.
