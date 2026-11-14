(* Lemmas on cell histories: insertion keeps the order of what was there. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model.

Lemma ids_app : forall h1 h2, ids (h1 ++ h2) = ids h1 ++ ids h2.
Proof. intros; unfold ids; apply map_app. Qed.

Lemma ids_cons : forall a h, ids (a :: h) = fst a :: ids h.
Proof. reflexivity. Qed.

Lemma in_ids_ins : forall h1 h2 a w,
  In w (ids (h1 ++ a :: h2)) <-> w = fst a \/ In w (ids (h1 ++ h2)).
Proof.
  intros. rewrite !ids_app, ids_cons, !in_app_iff. simpl. split; intros H; intuition (subst; auto).
Qed.

(* older, characterised by positions in the id list *)
Lemma older_split : forall h a b,
  older h a b <-> exists l1 l2, ids h = l1 ++ l2 /\ In a l1 /\ In b l2.
Proof.
  intros h a b; split.
  - intros (h1 & h2 & -> & Ha & Hb). exists (ids h1), (ids h2). rewrite ids_app. auto.
  - intros (l1 & l2 & E & Ha & Hb).
    exists (firstn (length l1) h), (skipn (length l1) h).
    rewrite firstn_skipn. split; [reflexivity|].
    assert (E1 : ids (firstn (length l1) h) = l1).
    { unfold ids. rewrite <- firstn_map. fold (ids h). rewrite E.
      rewrite firstn_app, Nat.sub_diag, firstn_all. simpl. apply app_nil_r. }
    assert (E2 : ids (skipn (length l1) h) = l2).
    { unfold ids. rewrite <- skipn_map. fold (ids h). rewrite E.
      rewrite skipn_app, Nat.sub_diag, skipn_all. reflexivity. }
    rewrite E1, E2. auto.
Qed.

Lemma older_ins : forall h1 h2 x a b,
  older (h1 ++ h2) a b -> older (h1 ++ x :: h2) a b.
Proof.
  intros h1 h2 x a b H. apply older_split in H. apply older_split.
  destruct H as (l1 & l2 & E & Ha & Hb).
  rewrite ids_app in E. rewrite ids_app, ids_cons.
  (* split point of l1/l2 relative to ids h1 *)
  destruct (Nat.le_gt_cases (length l1) (length (ids h1))) as [Hl|Hl].
  - (* l1 is a prefix of ids h1 *)
    assert (H1 : ids h1 = l1 ++ skipn (length l1) (ids h1)).
    { assert (F : firstn (length l1) (ids h1 ++ ids h2) = l1).
      { rewrite E, firstn_app, Nat.sub_diag, firstn_all. simpl. apply app_nil_r. }
      rewrite firstn_app in F. replace (length l1 - length (ids h1)) with 0 in F by lia.
      simpl in F. rewrite app_nil_r in F. rewrite <- F at 1. symmetry.
      apply firstn_skipn. }
    exists l1, (skipn (length l1) (ids h1) ++ fst x :: ids h2). split.
    + rewrite H1 at 1. rewrite <- app_assoc. reflexivity.
    + split; [assumption|].
      assert (Hl2 : l2 = skipn (length l1) (ids h1) ++ ids h2).
      { apply (app_inv_head l1). rewrite <- E, app_assoc, <- H1. reflexivity. }
      subst l2. rewrite in_app_iff in *. simpl. tauto.
  - (* l1 extends past ids h1 *)
    assert (H2 : l1 = ids h1 ++ firstn (length l1 - length (ids h1)) (ids h2)).
    { assert (F : firstn (length l1) (ids h1 ++ ids h2) = l1).
      { rewrite E, firstn_app, Nat.sub_diag, firstn_all. simpl. apply app_nil_r. }
      rewrite firstn_app in F. rewrite firstn_all2 in F by lia. symmetry. exact F. }
    exists (ids h1 ++ fst x :: firstn (length l1 - length (ids h1)) (ids h2)), l2.
    split.
    + assert (E2 : ids h2 = firstn (length l1 - length (ids h1)) (ids h2) ++ l2).
      { apply (app_inv_head (ids h1)). transitivity (l1 ++ l2); [exact E|].
        rewrite H2 at 1. rewrite <- app_assoc. reflexivity. }
      rewrite E2 at 1. rewrite <- app_assoc. reflexivity.
    + split; [|assumption].
      set (q := firstn (length l1 - length (ids h1)) (ids h2)) in *.
      rewrite H2 in Ha. rewrite in_app_iff in *. simpl. tauto.
Qed.

Lemma older_del : forall h1 h2 x a b,
  older (h1 ++ x :: h2) a b -> a <> fst x -> b <> fst x -> older (h1 ++ h2) a b.
Proof.
  intros h1 h2 x a b H Na Nb. apply older_split in H. apply older_split.
  destruct H as (l1 & l2 & E & Ha & Hb).
  rewrite ids_app, ids_cons in E. rewrite ids_app.
  (* fst x sits either in l1 or in l2 *)
  assert (Hx : In (fst x) (l1 ++ l2)) by (rewrite <- E; apply in_app_iff; right; left; auto).
  destruct (Nat.le_gt_cases (length l1) (length (ids h1))) as [Hl|Hl].
  - (* fst x in l2 *)
    assert (H1 : ids h1 = l1 ++ skipn (length l1) (ids h1)).
    { assert (F : firstn (length l1) (ids h1 ++ fst x :: ids h2) = l1).
      { rewrite E, firstn_app, Nat.sub_diag, firstn_all. simpl. apply app_nil_r. }
      rewrite firstn_app in F. replace (length l1 - length (ids h1)) with 0 in F by lia.
      simpl in F. rewrite app_nil_r in F. rewrite <- F at 1. symmetry. apply firstn_skipn. }
    assert (Hl2 : l2 = skipn (length l1) (ids h1) ++ fst x :: ids h2).
    { apply (app_inv_head l1). rewrite <- E, app_assoc, <- H1. reflexivity. }
    exists l1, (skipn (length l1) (ids h1) ++ ids h2). split.
    + rewrite H1 at 1. rewrite <- app_assoc. reflexivity.
    + split; [assumption|]. subst l2. rewrite in_app_iff in *. simpl in Hb.
      destruct Hb as [Hb|[Hb|Hb]]; auto. congruence.
  - assert (H2 : l1 = ids h1 ++ fst x :: firstn (length l1 - S (length (ids h1))) (ids h2)).
    { assert (F : firstn (length l1) (ids h1 ++ fst x :: ids h2) = l1).
      { rewrite E, firstn_app, Nat.sub_diag, firstn_all. simpl. apply app_nil_r. }
      rewrite firstn_app in F. rewrite firstn_all2 in F by lia.
      replace (length l1 - length (ids h1)) with (S (length l1 - S (length (ids h1)))) in F by lia.
      simpl in F. symmetry. exact F. }
    exists (ids h1 ++ firstn (length l1 - S (length (ids h1))) (ids h2)), l2. split.
    + assert (E2 : ids h2 = firstn (length l1 - S (length (ids h1))) (ids h2) ++ l2).
      { assert (E' : ids h1 ++ fst x :: ids h2 =
                     ids h1 ++ fst x :: (firstn (length l1 - S (length (ids h1))) (ids h2) ++ l2)).
        { rewrite E. set (q := firstn (length l1 - S (length (ids h1))) (ids h2)) in *.
          rewrite H2 at 1. rewrite <- app_assoc. reflexivity. }
        apply app_inv_head in E'. injection E' as E'. exact E'. }
      rewrite E2 at 1. rewrite <- app_assoc. reflexivity.
    + split; [|assumption].
      set (q := firstn (length l1 - S (length (ids h1))) (ids h2)) in *.
      rewrite H2 in Ha. rewrite in_app_iff in *. simpl in Ha.
      destruct Ha as [Ha|[Ha|Ha]]; auto. congruence.
Qed.

Lemma older_new : forall h1 h2 t g w,
  In w (ids h1) -> older (h1 ++ (t, g) :: h2) w t.
Proof.
  intros. exists h1, ((t, g) :: h2). split; [reflexivity|]. split; [assumption|]. left; reflexivity.
Qed.

Lemma older_in : forall h a b, older h a b -> In a (ids h) /\ In b (ids h).
Proof.
  intros h a b (h1 & h2 & -> & Ha & Hb). rewrite ids_app, !in_app_iff. auto.
Qed.

Lemma older_total : forall h a b, In a (ids h) -> In b (ids h) -> a <> b ->
  older h a b \/ older h b a.
Proof.
  intros h a b Ha Hb N. rewrite !older_split.
  apply in_split in Ha. destruct Ha as (l1 & l2 & E).
  rewrite E in Hb. apply in_app_iff in Hb. destruct Hb as [Hb|[Hb|Hb]].
  - right. exists l1, (a :: l2). auto with datatypes.
  - congruence.
  - left. exists (l1 ++ [a]), l2. rewrite <- app_assoc. simpl. auto with datatypes.
Qed.


Lemma nodup_app_disj : forall (l1 l2 : list nat) a, NoDup (l1 ++ l2) -> In a l1 -> In a l2 -> False.
Proof.
  induction l1 as [|y l1 IH]; intros l2 a ND H1 H2; [destruct H1|].
  inversion ND; subst. destruct H1 as [<-|H1].
  - apply H3. apply in_app_iff. auto.
  - eapply IH; eauto.
Qed.

Lemma ids_prefix_in : forall (l k1 k2 k3 k4 : list nat), l = k1 ++ k2 -> l = k3 ++ k4 ->
  length k1 <= length k3 -> forall z, In z k1 -> In z k3.
Proof.
  intros l k1 k2 k3 k4 Ea Eb L z Hz.
  assert (F : firstn (length k3) l = k3).
  { rewrite Eb, firstn_app, Nat.sub_diag, firstn_all. simpl. apply app_nil_r. }
  rewrite Ea, firstn_app, firstn_all2 in F by lia. rewrite <- F. apply in_app_iff; auto.
Qed.

Lemma ids_disj : forall (l k1 k2 : list nat) z, NoDup l -> l = k1 ++ k2 -> In z k1 -> In z k2 -> False.
Proof. intros l k1 k2 z ND E H1 H2. subst. eapply nodup_app_disj; eauto. Qed.

Lemma older_asym : forall h a b, NoDup (ids h) -> older h a b -> ~ older h b a.
Proof.
  intros h a b ND H1 H2. apply older_split in H1, H2.
  destruct H1 as (l1 & l2 & E1 & A1 & B2). destruct H2 as (m1 & m2 & E2 & B1 & A2).
  destruct (Nat.le_gt_cases (length l1) (length m1)) as [L|L].
  - exact (ids_disj _ m1 m2 a ND E2 (ids_prefix_in _ l1 l2 m1 m2 E1 E2 L a A1) A2).
  - assert (L' : length m1 <= length l1) by lia.
    exact (ids_disj _ l1 l2 b ND E1 (ids_prefix_in _ m1 m2 l1 l2 E2 E1 L' b B1) B2).
Qed.

Lemma older_irrefl : forall h a, NoDup (ids h) -> ~ older h a a.
Proof. intros h a ND H. exact (older_asym h a a ND H H). Qed.

Lemma older_trans : forall h a b c, NoDup (ids h) -> older h a b -> older h b c -> older h a c.
Proof.
  intros h a b c ND H1 H2.
  destruct (Nat.eq_dec a c) as [->|Nac].
  - exfalso. exact (older_asym h b c ND H2 H1).
  - destruct (older_total h a c) as [H|H]; auto.
    + apply (older_in h a b H1).
    + apply (older_in h b c H2).
    + exfalso.
      (* positions: a < b < c < a impossible; use split points *)
      apply older_split in H1, H2, H.
      destruct H1 as (l1 & l2 & E1 & A1 & B1). destruct H2 as (m1 & m2 & E2 & B2 & C2).
      destruct H as (n1 & n2 & E3 & C3 & A3).
      (* index argument via lengths *)
      assert (Hpos : forall (k1 k2 : list nat) z, ids h = k1 ++ k2 -> In z k1 -> In z k2 -> False).
      { intros k1 k2 z E Hz1 Hz2. rewrite E in ND. eapply nodup_app_disj; eauto. }
      assert (Pre : forall (k1 k2 k3 k4 : list nat), ids h = k1 ++ k2 -> ids h = k3 ++ k4 ->
                length k1 <= length k3 -> forall z, In z k1 -> In z k3).
      { intros k1 k2 k3 k4 Ea Eb L z Hz.
        assert (F : firstn (length k3) (ids h) = k3).
        { rewrite Eb, firstn_app, Nat.sub_diag, firstn_all. simpl. apply app_nil_r. }
        rewrite Ea, firstn_app, firstn_all2 in F by lia. rewrite <- F. apply in_app_iff; auto. }
      destruct (Nat.le_gt_cases (length l1) (length n1)) as [L|L].
      * (* a in l1 subset n1, but a in n2 *)
        exact (Hpos n1 n2 a E3 (Pre l1 l2 n1 n2 E1 E3 L a A1) A3).
      * destruct (Nat.le_gt_cases (length m1) (length l1)) as [L2|L2].
        -- (* b in m1 subset l1, but b in l2 *)
           exact (Hpos l1 l2 b E1 (Pre m1 m2 l1 l2 E2 E1 L2 b B2) B1).
        -- (* n1 shorter than m1: c in n1 subset m1, but c in m2 *)
           assert (L3 : length n1 <= length m1) by lia.
           exact (Hpos m1 m2 c E2 (Pre n1 n2 m1 m2 E3 E2 L3 c C3) C2).
Qed.

Lemma last_older : forall h y, NoDup (ids h) -> In y (ids h) ->
  (forall z, In z (ids h) -> z <> y -> older h z y) -> exists gf r, rev h = (y, gf) :: r.
Proof.
  intros h y ND Hy Hz. destruct (rev h) as [|[w gf] r] eqn:E.
  - exfalso. apply (f_equal (@rev _)) in E. rewrite rev_involutive in E. subst. destruct Hy.
  - exists gf, r. destruct (Nat.eq_dec w y) as [->|N]; auto. exfalso.
    assert (Eh : h = rev r ++ [(w, gf)]) by (rewrite <- (rev_involutive h), E; reflexivity).
    assert (Iw : In w (ids h)) by (rewrite Eh, ids_app, in_app_iff; right; left; reflexivity).
    pose proof (Hz w Iw N) as O. apply older_split in O. destruct O as (l1 & l2 & E1 & A & B).
    rewrite Eh, ids_app in E1. simpl in E1.
    destruct l2 as [|z l2'] using rev_ind; [destruct B|].
    rewrite app_assoc in E1. apply app_inj_tail in E1. destruct E1 as [E1 <-].
    rewrite Eh, ids_app in ND. simpl in ND. rewrite E1 in ND.
    rewrite <- app_assoc in ND. eapply nodup_app_disj; [exact ND|exact A|].
    apply in_app_iff. right. left. reflexivity.
Qed.
