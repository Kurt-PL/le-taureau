(* Model2: invariants of runs: values, registers, cell histories. *)
From Stdlib Require Import Arith Lia List Bool Permutation Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv.

Definition rgof (s : st) (e : oev) : regs := rg (cs s (ec e)).
(* the instruction an entry executed *)
Definition einstr (p : prog) (s : st) (e : oev) : instr := ai (cs s (ec e)) (ek e).
Definition isw (s : st) (y : nat) : Prop := exists e, ent s y = Some e /\ ew e = true.
(* the value a read took in cell x, and in the cells xs *)
Definition rdv (s : st) (u : cell -> option nat) (x : cell) : val :=
  match u x with None => 0 | Some y => wv s y x end.
Definition rdvs (s : st) (xs : list cell) (u : cell -> option nat) : list val := map (rdv s u) xs.
Definition carr (s : st) (u : cell -> option nat) : view :=
  fun w' => exists x y, u x = Some y /\ (wc s y w' \/ w' = y).
Definition esrc (e : oev) : view := srcv (erf e) (ew e) (et e).
Lemma rdvals_mof : forall s c xs u, rdvals (mof s c) xs u = rdvs s xs u.
Proof. reflexivity. Qed.
Lemma carrieds_mof : forall s c u, carrieds (mof s c) u = carr s u.
Proof. reflexivity. Qed.

Record Inv2 (p : prog) (s : st) : Prop := {
  j_val : forall t e i, ent s t = Some e -> einstr p s e = i ->
    (xload i (rgof s e) = true -> rval i (rg (cs s (ec e)) (ek e)) = enc (rdvs s (icells i) (erf e))) /\
    (xload i (rgof s e) = false -> rg (cs s (ec e)) (ek e) = 0 /\ forall x, erf e x = None);
  j_rf : forall t e x y, ent s t = Some e -> erf e x = Some y ->
    y < t /\ isw s y /\ In x (icells (einstr p s e)) /\ In y (ids (hs s x));
  j_ew : forall t e i, ent s t = Some e -> einstr p s e = i ->
    ew e = (negb (eh e) && is_store i && icond i (rgof s e) &&
            (negb (is_cas i) || (Nat.eqb (enc (rdvs s (icells i) (erf e))) (eval_e i (rgof s e)) && ew e))) /\
    (ew e = true -> wv s t = cval (icells i) (wvals i (rgof s e)) /\ forall x, In x (icells i) -> In t (ids (hs s x)));
  j_hist : forall x y, In y (ids (hs s x)) ->
    exists e i, ent s y = Some e /\ ew e = true /\ einstr p s e = i /\ In x (icells i);
  j_nodup : forall x, NoDup (ids (hs s x));
  j_views : forall c y, (vP (cs s c) y \/ vA (cs s c) y \/ vR (cs s c) y \/ vG s y) -> isw s y;
  j_eP : forall t e y, ent s t = Some e -> eP e y -> isw s y /\ y < t;
  j_wc : forall y y', wc s y y' -> isw s y' /\ y' <= y /\ y < tm s;
  (* in each cell, the value a slot read is the value of the write it took *)
  j_rv : forall t e x, ent s t = Some e -> rv (cs s (ec e)) (ek e) x = rdv s (erf e) x;
  (* a CAS's event: its verdict says whether it wrote *)
  j_ok : forall t e, ent s t = Some e -> eh e = false -> is_cas (einstr p s e) = true ->
    xload (einstr p s e) (rgof s e) = true -> vok (rg (cs s (ec e)) (ek e)) = ew e
}.

(* what an access's step starts from is written *)
Lemma old4_isw : forall p s c y, Inv2 p s -> old4 (mof s c) y -> isw s y.
Proof.
  intros p s c y J H. unfold old4, vor in H; simpl in H.
  destruct H as [H|(e & E & _ & W)]; [apply (j_views p s J c); tauto|exists e; split; [exact E|exact W]].
Qed.

Lemma isw_lt : forall p s y, Inv1 p s -> isw s y -> y < tm s.
Proof.
  intros p s y I (e & He & _). rewrite (i_tm p s I). unfold ent in He.
  apply nth_error_Some. congruence.
Qed.

Lemma Inv2_init : forall p, Inv2 p sinit.
Proof.
  intros p. constructor; unfold ent, isw; simpl; intros.
  all: try (match goal with H : nth_error [] ?t = Some _ |- _ => destruct t; discriminate end).
  all: try contradiction.
  - constructor.
  - destruct H as [H|[H|[H|H]]]; contradiction.
Qed.

Lemma eofR_half : forall i r xs, eofR i r = eofR (crd Plain xs) r -> icells i = icells (crd Plain xs) /\ xload i r = true.
Proof.
  intros [m x c0|m x c0 v|m x c0 e n|f|] r xs H; cbn in H; try discriminate.
  destruct (c0 r) eqn:E; [injection H as -> ->|discriminate]. unfold xload; cbn. rewrite E. split; reflexivity.
Qed.

Lemma eofR_cas : forall i r mx, eofR i r = Some mx -> is_cas i = true.
Proof. intros [] r mx H; cbn in H; try discriminate; reflexivity. Qed.

Set Default Proof Using "All".
Section Step.
(* an event step: the access i acts at slot k; what the step does to the
   next instruction, the settle order and the bound reads does not matter
   here *)
Variables (p : prog) (s : st) (c k : nat) (i : instr) (m' : mst) (a : val) (K : view)
          (u : cell -> option nat) (w : bool) (Bd : nat -> bool) (pc' tp' : nat -> nat)
          (cm' : list (nat * nat * nat)).
Hypothesis I : Inv1 p s.
Hypothesis J : Inv2 p s.
Hypothesis Ho : oc (cs s c) k = None.
Hypothesis Hk : pcs s c <= k.
Hypothesis Hst : forall r, settled (cs s c) (pcs s c) r -> ieval i r = ieval i (rg (cs s c)).
Hypothesis He : eff (tm s) i (rg (cs s c)) (mof s c) m' a K u w.
(* a CAS whose read happened alone: its write, with the writes the read took *)
Hypothesis Hhk : oh (cs s c) k = None \/
  (u = rw (cs s c) k /\ eofR i (rg (cs s c)) = eofR (ai (cs s c) k) (rg (cs s c))).

Local Abbreviation t' := (evs s c k i m' a K u w Bd pc' tp' cm').
Local Abbreviation new := (newev s c k i K u w).

(* old entries see the same instruction and outcome *)
(* an old entry at the slot of the step: a CAS's read alone *)
Lemma at_k : forall t e, ent s t = Some e -> ec e = c -> ek e = k -> eh e = true /\ oh (cs s c) k = Some t.
Proof.
  intros t e H E1 E2. destruct (i_et p s I t e H) as (E3 & E4). rewrite E1, E2 in E4.
  destruct (eh e); [auto|]. congruence.
Qed.

Lemma ieval_old0 : forall t e, ent s t = Some e -> ~ (ec e = c /\ ek e = k) ->
  einstr p t' e = einstr p s e /\ ieval (einstr p s e) (rgof t' e) = ieval (einstr p s e) (rgof s e).
Proof.
  intros t e H N. unfold einstr, rgof.
  assert (A : ai (cs t' (ec e)) (ek e) = ai (cs s (ec e)) (ek e)).
  { rewrite ai_s'. destruct (Nat.eqb_spec (ec e) c) as [E|E]; [destruct (Nat.eqb_spec (ek e) k); [tauto|rewrite E; reflexivity]|reflexivity]. }
  rewrite A. split; [reflexivity|].
  apply (i_det p s I t e H). eapply settled_s'; eauto.
Qed.

Lemma ieval_old : forall t e i0, ent s t = Some e -> ~ (ec e = c /\ ek e = k) -> einstr p t' e = i0 ->
  einstr p s e = i0 /\ ieval i0 (rgof t' e) = ieval i0 (rgof s e).
Proof.
  intros t e i0 H N E. destruct (ieval_old0 t e H N) as [A B]. rewrite A in E. subst i0. auto.
Qed.

Lemma settled_new : settled (cs s c) (pcs s c) (rg (cs t' c)).
Proof. eapply settled_s'; eauto. Qed.

Lemma ins_new : einstr p t' new = i.
Proof. unfold einstr. cbn [ec ek]. rewrite ai_s', !Nat.eqb_refl. reflexivity. Qed.

Lemma ieval_new : ieval i (rg (cs t' c)) = ieval i (rg (cs s c)).
Proof. apply Hst. apply settled_new. Qed.

Lemma rg_old : forall e, ~ (ec e = c /\ ek e = k) -> rg (cs t' (ec e)) (ek e) = rg (cs s (ec e)) (ek e).
Proof.
  intros e N. rewrite rg_s'. destruct (Nat.eqb_spec (ec e) c) as [E|E]; [destruct (Nat.eqb_spec (ek e) k); [tauto|rewrite E; reflexivity]|reflexivity].
Qed.

Lemma rv_old : forall e, ~ (ec e = c /\ ek e = k) -> rv (cs t' (ec e)) (ek e) = rv (cs s (ec e)) (ek e).
Proof.
  intros e N. rewrite rv_s'. destruct (Nat.eqb_spec (ec e) c) as [E|E]; [destruct (Nat.eqb_spec (ek e) k); [tauto|rewrite E; reflexivity]|reflexivity].
Qed.

Lemma ent_t' : forall t0, ent t' t0 =
  if Nat.ltb t0 (tm s) then ent s t0 else if Nat.eqb t0 (tm s) then Some new else None.
Proof. intros. apply (ent_s' p); auto. Qed.

Lemma old_ent : forall t0 e, ent s t0 = Some e -> ent t' t0 = Some e /\ t0 < tm s.
Proof.
  intros t0 e H. assert (t0 < tm s).
  { rewrite (i_tm p s I). unfold ent in H. apply nth_error_Some. congruence. }
  rewrite ent_t'. apply Nat.ltb_lt in H0 as H1. rewrite H1. auto.
Qed.

Lemma ent_cases : forall t0 e, ent t' t0 = Some e ->
  (ent s t0 = Some e /\ t0 < tm s) \/ (t0 = tm s /\ e = new).
Proof.
  intros t0 e H. rewrite ent_t' in H. destruct (Nat.ltb_spec t0 (tm s)); auto.
  destruct (Nat.eqb_spec t0 (tm s)); [|discriminate]. injection H as <-. auto.
Qed.

Lemma isw_old : forall y, isw s y -> isw t' y.
Proof. intros y (e & H & Hw). exists e. split; auto. apply (old_ent y e H). Qed.

Local Abbreviation m := (mof s c).

Lemma t_hs0 : w = false -> hs t' = hs s /\ wv t' = wv s /\ wc t' = wc s.
Proof. intros W. destruct (eff_nowrite _ _ _ _ _ _ _ _ _ He W) as (A1 & A2 & A3). auto. Qed.

Lemma t_hs1 : w = true -> exists R0,
  is_store i = true /\ icond i (rg (cs s c)) = true /\
  (forall x, ~ In x (icells i) -> hs t' x = hs s x) /\
  (forall x, In x (icells i) -> exists h1 h2, hs s x = h1 ++ h2 /\ hs t' x = h1 ++ (tm s, false) :: h2) /\
  wv t' = upd (wv s) (tm s) (cval (icells i) (wvals i (rg (cs s c)))) /\
  wc t' = upd (wc s) (tm s) (vor R0 (vone (tm s))) /\
  vsub (vR (cs s c)) R0 /\
  (xgop i (rg (cs s c)) = true -> vsub K R0) /\ vsub R0 (old4 m) /\
  (is_cas i = true -> enc (rdvs s (icells i) u) = eval_e i (rg (cs s c))).
Proof.
  intros W. destruct (eff_write _ _ _ _ _ _ _ _ _ He W)
    as (H' & R0 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
  exists R0. unfold evs; simpl. rewrite Q3. repeat split; auto.
  intros y Hy. left. apply Q10. exact Hy.
Qed.

Lemma K_isw : forall y, K y -> isw s y.
Proof.
  intros y Hy. apply (eff_K_old _ _ _ _ _ _ _ _ _ He) in Hy. apply (old4_isw p s c y J Hy).
Qed.

Lemma u_reads : (exists x y, u x = Some y) -> takes (hs s) (icells i) u.
Proof.
  intros (x & y & E). pose proof (eff_u _ _ _ _ _ _ _ _ _ He x y E) as X.
  exact (proj1 (eff_read _ _ _ _ _ _ _ _ _ He X)).
Qed.

Lemma u_isw : forall x y, u x = Some y -> isw s y /\ In x (icells i) /\ In y (ids (hs s x)).
Proof.
  intros x y E. destruct (u_reads (ex_intro _ x (ex_intro _ y E))) as (R1 & R2).
  assert (Hx : In x (icells i)).
  { destruct (in_dec Nat.eq_dec x (icells i)) as [Q|Q]; auto. rewrite (R2 x Q) in E. discriminate. }
  pose proof (R1 x Hx) as V. rewrite E in V. split; [|auto].
  destruct (j_hist p s J x y V) as (e & i0 & H1 & H2 & _). exists e; auto.
Qed.

Lemma wv_old : forall y, y < tm s -> wv t' y = wv s y.
Proof.
  intros y Hy. destruct (bool_dec w true) as [W|W]; [|apply not_true_is_false in W].
  - destruct t_hs1 as (R0 & Q); auto. destruct Q as (_ & _ & _ & _ & Q & _).
    rewrite Q. apply upd_neq. lia.
  - destruct t_hs0 as (_ & Q & _); auto. rewrite Q. reflexivity.
Qed.

Lemma rdvs_old : forall xs u0, (forall x y, u0 x = Some y -> y < tm s) -> rdvs t' xs u0 = rdvs s xs u0.
Proof.
  intros xs u0 H. unfold rdvs. apply map_ext. intros x. unfold rdv.
  destruct (u0 x) as [y|] eqn:E; auto. rewrite wv_old; eauto.
Qed.

Lemma wc_old : forall y, y < tm s -> wc t' y = wc s y.
Proof.
  intros y Hy. destruct (bool_dec w true) as [W|W]; [|apply not_true_is_false in W].
  - destruct t_hs1 as (R0 & Q); auto. destruct Q as (_ & _ & _ & _ & _ & Q & _).
    rewrite Q. apply upd_neq. lia.
  - destruct t_hs0 as (_ & _ & Q); auto. rewrite Q. reflexivity.
Qed.

(* histories after the step: the old one with possibly the new write inserted *)
Lemma hs_rel : forall x, (hs t' x = hs s x) \/
  (w = true /\ In x (icells i) /\ exists h1 h2 g, hs s x = h1 ++ h2 /\ hs t' x = h1 ++ (tm s, g) :: h2).
Proof.
  intros x. destruct (bool_dec w true) as [W|W]; [|apply not_true_is_false in W].
  - destruct t_hs1 as (R0 & _ & _ & Q3 & Q4 & _); auto.
    destruct (in_dec Nat.eq_dec x (icells i)) as [Hx|Hx].
    + right. split; auto. split; auto. destruct (Q4 x Hx) as (h1 & h2 & A1 & A2). exists h1, h2, false. auto.
    + left. auto.
  - left. destruct t_hs0 as (Q & _); auto. rewrite Q. reflexivity.
Qed.

Lemma isw_lt_s : forall y, isw s y -> y < tm s.
Proof. intros. eapply isw_lt; eauto. Qed.

Lemma in_hs_old : forall x y, y < tm s -> In y (ids (hs t' x)) -> In y (ids (hs s x)).
Proof.
  intros x y Hy H. destruct (hs_rel x) as [E|(_ & _ & h1 & h2 & g & E1 & E2)].
  - rewrite E in H; auto.
  - rewrite E2 in H. rewrite E1. apply in_ids_ins in H. simpl in H. destruct H; [lia|auto].
Qed.

Lemma in_hs_new : forall x y, In y (ids (hs s x)) -> In y (ids (hs t' x)).
Proof.
  intros x y H. destruct (hs_rel x) as [E|(_ & _ & h1 & h2 & g & E1 & E2)].
  - rewrite E; auto.
  - rewrite E2. rewrite E1 in H. apply in_ids_ins. auto.
Qed.

Lemma older_new_old : forall x y z, older (hs s x) y z -> older (hs t' x) y z.
Proof.
  intros x y z H. destruct (hs_rel x) as [E|(_ & _ & h1 & h2 & g & E1 & E2)].
  - rewrite E; auto.
  - rewrite E2. rewrite E1 in H. apply older_ins. auto.
Qed.

Lemma older_old_new : forall x y z, y < tm s -> z < tm s -> older (hs t' x) y z -> older (hs s x) y z.
Proof.
  intros x y z Hy Hz H. destruct (hs_rel x) as [E|(_ & _ & h1 & h2 & g & E1 & E2)].
  - rewrite E in H; auto.
  - rewrite E2 in H. rewrite E1. eapply older_del; eauto; simpl; lia.
Qed.

Lemma u_lt : forall x y, u x = Some y -> y < tm s.
Proof. intros x y E. apply isw_lt_s. apply (u_isw x y E). Qed.

Lemma at_dec : forall e, {ec e = c /\ ek e = k} + {~ (ec e = c /\ ek e = k)}.
Proof.
  intros e. destruct (Nat.eq_dec (ec e) c), (Nat.eq_dec (ek e) k); [left; auto|right; tauto|right; tauto|right; tauto].
Qed.

(* the CAS's read alone at the slot of the step *)
Lemma half_k : forall t e, ent s t = Some e -> ec e = c -> ek e = k ->
  (forall x, u x = erf e x) /\ icells i = icells (ai (cs s c) k) /\ xload i (rg (cs s c)) = true /\
  eh e = true /\ ew e = false /\
  (exists xs, ai (cs s c) k = crd Plain xs /\ eofR i (rg (cs s c)) = Some (Plain, xs)) /\ is_cas i = true.
Proof.
  intros t e H E1 E2. destruct (at_k t e H E1 E2) as [Eh Oh].
  destruct Hhk as [Z|(U & Ef)]; [congruence|].
  destruct (i_half p s I c k t Ho Oh Hk) as (_ & (xs & Ax) & _). rewrite Ax in Ef.
  destruct (eofR_half _ _ _ Ef) as (Ic & Xl). rewrite <- Ax in Ic.
  destruct (i_rw p s I c k t (or_intror (conj Ho Oh))) as (e' & H' & Rw). rewrite H in H'. injection H' as <-.
  assert (Ew : ew e = false).
  { destruct (j_ew p s J t e _ H eq_refl) as [W _]. rewrite Eh in W. exact W. }
  split; [|split; [exact Ic|split; [exact Xl|split; [auto|split; [auto|split; [exists xs; split; [exact Ax|exact Ef]|apply (eofR_cas _ _ _ Ef)]]]]]].
  intros x. rewrite U, Rw, Ew. reflexivity.
Qed.

Lemma Inv2_step : Inv2 p t'.
Proof.
  constructor.
  - (* j_val *)
    intros t e i0 H Hi0. apply ent_cases in H. destruct H as [(H & Ht)|(-> & ->)].
    + destruct (at_dec e) as [(E1 & E2)|N].
      { destruct (half_k t e H E1 E2) as (U & Ic & Xl & Eh & Ew & _).
        unfold einstr in Hi0. rewrite E1, E2, ai_s', !Nat.eqb_refl in Hi0. subst i0.
        unfold rgof. rewrite E1, E2.
        assert (Ex : xload i (rg (cs t' c)) = true) by (unfold xload, icond; rewrite ieval_new; exact Xl).
        rewrite Ex. split; [intros _|intros Z; discriminate].
        rewrite rg_s', !Nat.eqb_refl. destruct (eff_read _ _ _ _ _ _ _ _ _ He Xl) as (_ & Ea).
        transitivity (enc (rdvals m (icells i) u)); [rewrite Ea; apply rval_areg|]. rewrite rdvals_mof.
        rewrite (rdvs_old (icells i) (erf e)).
        - f_equal. unfold rdvs, rdv. apply map_ext. intros x. rewrite U. reflexivity.
        - intros x y Ey. destruct (j_rf p s J t e x y H Ey) as (Hy & _). lia. }
      unfold rgof. rewrite (rg_old e N).
      assert (Ex : xload i0 (rg (cs t' (ec e))) = xload i0 (rg (cs s (ec e)))).
      { destruct (ieval_old t e i0 H N Hi0) as [_ Q]. unfold xload, icond. unfold rgof in Q. rewrite Q. auto. }
      rewrite Ex. destruct (j_val p s J t e i0 H (proj1 (ieval_old t e i0 H N Hi0))) as [V1 V2]. split; intros X.
      * rewrite (V1 X). f_equal. symmetry. apply rdvs_old.
        intros x y Ey. destruct (j_rf p s J t e x y H Ey) as (Hy & _). lia.
      * apply V2; auto.
    + rewrite ins_new in Hi0. subst i0.
      unfold rgof; cbn [ec ek et eP erf ew].
      assert (Ex : xload i (rg (cs t' c)) = xload i (rg (cs s c))).
      { unfold xload, icond. rewrite ieval_new. auto. }
      rewrite Ex. rewrite rg_s', !Nat.eqb_refl. split; intros X.
      * destruct (eff_read _ _ _ _ _ _ _ _ _ He X) as (_ & Ea).
        rewrite rdvs_old by exact u_lt. transitivity (enc (rdvals m (icells i) u)); [rewrite Ea; apply rval_areg|]. rewrite rdvals_mof. reflexivity.
      * apply (eff_noread _ _ _ _ _ _ _ _ _ He X).
  - (* j_rf *)
    intros t e x y H Ey. apply ent_cases in H. destruct H as [(H & Ht)|(-> & ->)].
    + destruct (j_rf p s J t e x y H Ey) as (A1 & A2 & A3 & A4).
      split; auto. split; [apply isw_old; auto|].
      split; [|apply in_hs_new; auto].
      destruct (at_dec e) as [(E1 & E2)|N].
      * destruct (half_k t e H E1 E2) as (_ & Ic & _). unfold einstr in *. rewrite E1, E2 in *.
        rewrite ai_s', !Nat.eqb_refl, Ic. exact A3.
      * rewrite (proj1 (ieval_old0 t e H N)); auto.
    + cbn [erf] in Ey. destruct (u_isw x y Ey) as (A1 & A2 & A3). split; [apply isw_lt_s; auto|].
      split; [apply isw_old; auto|]. rewrite ins_new. split; auto. apply in_hs_new; auto.
  - (* j_ew *)
    intros t e i0 H Hi0. apply ent_cases in H. destruct H as [(H & Ht)|(-> & ->)].
    + destruct (at_dec e) as [(E1 & E2)|N].
      { destruct (half_k t e H E1 E2) as (_ & _ & _ & Eh & Ew & _). rewrite Eh, Ew. split; [reflexivity|discriminate]. }
      destruct (ieval_old t e i0 H N Hi0) as [Hs Q].
      destruct (j_ew p s J t e i0 H Hs) as [W1 W2]. unfold rgof in *.
      assert (Ic : icond i0 (rg (cs t' (ec e))) = icond i0 (rg (cs s (ec e)))) by (unfold icond; rewrite Q; auto).
      assert (RD : rdvs t' (icells i0) (erf e) = rdvs s (icells i0) (erf e)).
      { apply rdvs_old. intros x y Ey. destruct (j_rf p s J t e x y H Ey) as (Hy & _). lia. }
      split.
      * rewrite Ic, (ieval_e _ _ _ Q), RD. exact W1.
      * intros X. destruct (W2 X) as [Y1 Y2]. split.
        -- rewrite wv_old by auto. rewrite Y1, (ieval_wvals _ _ _ Q). reflexivity.
        -- intros x Hx. apply in_hs_new. auto.
    + rewrite ins_new in Hi0. subst i0. unfold rgof; cbn [ec ek et eP erf ew].
      pose proof ieval_new as Q.
      assert (Ic : icond i (rg (cs t' c)) = icond i (rg (cs s c))) by (unfold icond; rewrite Q; auto).
      split.
      * cbn [eh negb andb]. transitivity (is_store i && icond i (rg (cs s c)) &&
          (negb (is_cas i) || (Nat.eqb (enc (rdvals m (icells i) u)) (eval_e i (rg (cs s c))) && w))).
        { apply (eff_w_spec _ _ _ _ _ _ _ _ _ He). }
        rewrite Ic, (ieval_e _ _ _ Q), rdvals_mof, rdvs_old; [reflexivity|exact u_lt].
      * intros W. destruct t_hs1 as (R0 & Q1 & Q2 & Q3 & Q4 & Q5 & _); auto.
        split.
        -- rewrite Q5, upd_eq, (ieval_wvals _ _ _ Q). reflexivity.
        -- intros x Hx. destruct (Q4 x Hx) as (h1 & h2 & A1 & A2). rewrite A2.
           apply in_ids_ins. simpl. auto.
  - (* j_hist *)
    intros x y Hy. destruct (Nat.lt_ge_cases y (tm s)) as [Ly|Ly].
    + apply in_hs_old in Hy; auto. destruct (j_hist p s J x y Hy) as (e & i0 & A1 & A2 & A3 & A4).
      exists e, i0. rewrite (proj1 (old_ent y e A1)).
      destruct (at_dec e) as [(E1 & E2)|N].
      * destruct (half_k y e A1 E1 E2) as (_ & _ & _ & _ & Ew & _). congruence.
      * rewrite (proj1 (ieval_old0 y e A1 N)). auto.
    + assert (NO : ~ In y (ids (hs s x))).
      { intros Hy'. destruct (j_hist p s J x y Hy') as (e & i0 & A1 & A2 & _).
        assert (isw s y) as Q by (exists e; auto). apply isw_lt_s in Q. lia. }
      destruct (hs_rel x) as [E|(W & Hx & h1 & h2 & g & E1 & E2)].
      * rewrite E in Hy. contradiction.
      * rewrite E2 in Hy. apply in_ids_ins in Hy. simpl in Hy. destruct Hy as [Hy|Hy].
        -- subst y. exists new, i. rewrite ent_t', Nat.ltb_irrefl, Nat.eqb_refl. rewrite ins_new.
           cbn [ew ec ek]. auto.
        -- rewrite <- E1 in Hy. contradiction.
  - (* j_nodup *)
    intros x. destruct (hs_rel x) as [E|(W & Hx & h1 & h2 & g & E1 & E2)].
    + rewrite E. apply (j_nodup p s J).
    + rewrite E2. pose proof (j_nodup p s J x) as ND. rewrite E1 in ND.
      assert (NI : ~ In (tm s) (ids (h1 ++ h2))).
      { rewrite <- E1. intros Hy. destruct (j_hist p s J x (tm s) Hy) as (e & i0 & A1 & A2 & _).
        assert (isw s (tm s)) as Q by (exists e; auto). apply isw_lt_s in Q. lia. }
      rewrite ids_app, ids_cons. rewrite ids_app in ND, NI. simpl.
      apply (Permutation_NoDup (Permutation_middle _ _ _)).
      constructor; auto.
  - (* j_views *)
    intros c' y Hy.
    assert (G : forall y, mP m' y \/ mA m' y \/ mR m' y \/ mG m' y \/ K y -> isw t' y).
    { intros y0 Hy0. destruct (eff_views _ _ _ _ _ _ _ _ _ He y0 Hy0)
        as [Q|[(x & Q)|[(x & z & Q1 & Q2)|(Q1 & Q2)]]].
      - apply isw_old. apply (old4_isw p s c y0 J Q).
      - apply isw_old. apply (u_isw x y0 Q).
      - apply isw_old. simpl in Q2. apply (j_wc p s J z y0 Q2).
      - subst y0. exists new. rewrite ent_t', Nat.ltb_irrefl, Nat.eqb_refl. auto. }
    unfold evs in Hy; simpl in Hy. unfold upd in Hy. destruct (Nat.eqb_spec c' c).
    + simpl in Hy. apply G. tauto.
    + destruct Hy as [Hy|[Hy|[Hy|Hy]]]; try (apply isw_old; apply (j_views p s J c'); tauto).
      apply G. tauto.
  - (* j_eP *)
    intros t e y H Hy. apply ent_cases in H. destruct H as [(H & Ht)|(-> & ->)].
    + destruct (j_eP p s J t e y H Hy). split; auto. apply isw_old; auto.
    + cbn [eP] in Hy. pose proof (K_isw y Hy). split; [apply isw_old; auto|]. apply isw_lt_s; auto.
  - (* j_wc *)
    intros y y' Hy. destruct (Nat.lt_ge_cases y (tm s)) as [Ly|Ly].
    + rewrite wc_old in Hy by auto. destruct (j_wc p s J y y' Hy) as (A1 & A2 & A3).
      split; [apply isw_old; auto|]. simpl. lia.
    + destruct (bool_dec w true) as [W|W]; [|apply not_true_is_false in W].
      * destruct t_hs1 as (R0 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & _); auto.
        rewrite Q6 in Hy. unfold upd in Hy. destruct (Nat.eqb_spec y (tm s)).
        -- subst y. destruct Hy as [Hy|Hy].
           ++ apply Q9 in Hy.
              assert (isw s y') by (apply (old4_isw p s c y' J Hy)).
              split; [apply isw_old; auto|]. apply isw_lt_s in H. simpl. lia.
           ++ unfold vone in Hy. subst y'. split; [|simpl; lia].
              exists new. rewrite ent_t', Nat.ltb_irrefl, Nat.eqb_refl. auto.
        -- destruct (j_wc p s J y y' Hy) as (_ & _ & A3). lia.
      * destruct t_hs0 as (_ & _ & Q); auto. rewrite Q in Hy.
        destruct (j_wc p s J y y' Hy) as (_ & _ & A3). lia.
  - (* j_rv *)
    intros t e x H. apply ent_cases in H. destruct H as [(H & Ht)|(-> & ->)].
    + destruct (at_dec e) as [(E1 & E2)|N].
      { destruct (half_k t e H E1 E2) as (U & _). rewrite E1, E2, rv_s', !Nat.eqb_refl. unfold rdval, rdv. cbn [mof mV].
        rewrite U. destruct (erf e x) as [y|] eqn:Ey; auto. destruct (j_rf p s J t e x y H Ey) as (Hy & _).
        rewrite wv_old by lia. reflexivity. }
      rewrite (rv_old e N), (j_rv p s J t e x H). unfold rdv.
      destruct (erf e x) as [y|] eqn:Ey; auto. destruct (j_rf p s J t e x y H Ey) as (Hy & _).
      rewrite wv_old by lia. reflexivity.
    + cbn [ec ek erf]. rewrite rv_s', !Nat.eqb_refl. unfold rdval, rdv. cbn [mof mV].
      destruct (u x) as [y|] eqn:Ey; auto. rewrite wv_old by (apply (u_lt x); auto). reflexivity.
  - (* j_ok *)
    intros t e H Eh Ci Xl. apply ent_cases in H. destruct H as [(H & Ht)|(-> & ->)].
    + destruct (at_dec e) as [(E1 & E2)|N].
      { destruct (half_k t e H E1 E2) as (_ & _ & _ & Eh' & _). congruence. }
      destruct (ieval_old0 t e H N) as (A & Q). rewrite A in Ci, Xl. rewrite (rg_old e N).
      assert (X' : xload (einstr p s e) (rgof s e) = true) by (unfold xload, icond in *; rewrite <- Q; exact Xl).
      exact (j_ok p s J t e H Eh Ci X').
    + unfold einstr, rgof in *. cbn [ec ek eh ew] in Ci, Xl |- *. rewrite ai_s', !Nat.eqb_refl in Ci, Xl. rewrite rg_s', !Nat.eqb_refl.
      assert (X' : xload i (rg (cs s c)) = true) by (unfold xload, icond in *; rewrite <- ieval_new; exact Xl).
      destruct (eff_read _ _ _ _ _ _ _ _ _ He X') as (_ & Ea). rewrite Ea.
      destruct i; simpl in Ci; try discriminate. simpl. apply vok_vd.
Qed.

End Step.

(* ---------- reaching an early access: the slot now records the
   programme's instruction, which does the same ---------- *)
Lemma same_prof : forall i1 i2 r d, dof i1 r = Some d -> dof i2 r = Some d ->
  icells i1 = icells i2 /\ xload i1 r = xload i2 r /\ is_store i1 = is_store i2 /\ icond i1 r = icond i2 r /\
  is_cas i1 = is_cas i2 /\ eval_e i1 r = eval_e i2 r /\ wval i1 r = wval i2 r /\ xgop i1 r = xgop i2 r /\
  i1 <> IFn FLl /\ i2 <> IFn FLl /\ i1 <> IFn FSs /\ i2 <> IFn FSs.
Proof.
  intros [m1 x1 c1|m1 x1 c1 v1|m1 x1 c1 e1 n1| |] [m2 x2 c2|m2 x2 c2 v2|m2 x2 c2 e2 n2| |] r d H1 H2;
  simpl in H1, H2; try discriminate;
  destruct (c1 r) eqn:C1; try discriminate; destruct (c2 r) eqn:C2; try discriminate;
  rewrite <- H2 in H1; injection H1; intros; subst;
  unfold xload, icond, ieval, xgop, eval_e, wval; simpl; rewrite ?C1, ?C2; repeat split; try discriminate; auto.
Qed.

Lemma dof_rval : forall i1 i2 r1 r2 d0, dof i1 r1 = Some d0 -> dof i2 r2 = Some d0 -> forall a0, rval i1 a0 = rval i2 a0.
Proof.
  intros i1 i2 r1 r2 d0 H1 H2 a0. destruct i1 as [mA xA cA|mA xA cA vA|mA xA cA eA nA|fA|], i2 as [mB xB cB|mB xB cB vB|mB xB cB eB nB|fB|];
    simpl in *; try reflexivity;
    repeat match goal with Hx : (if ?b then _ else _) = _ |- _ => destruct b; try discriminate end;
    congruence.
Qed.

Section Match2.
Variables (p : prog) (s : st) (c : nat) (d : desc).
Hypothesis I : Inv1 p s.
Hypothesis J : Inv2 p s.
Local Abbreviation cc := (cs s c).
Local Abbreviation k := (pcs s c).
Hypothesis Ho : oc cc k <> None.
Hypothesis Ha : ai cc k = inst_of d.
Hypothesis Hdf : eof (ins p c k (rg cc)) (rg cc) = Some d.
Local Abbreviation s' := (smatch p s c).

Lemma ent_match : forall t, ent s' t = ent s t.
Proof. reflexivity. Qed.

Lemma rgof_match : forall e, rgof s' e = rgof s e.
Proof. intros e. unfold rgof. apply rg_match. Qed.

(* the instruction an entry executed, before and after *)
Lemma einstr_match : forall e, einstr p s' e = einstr p s e \/
  (dof (einstr p s e) (rgof s e) = Some d /\ dof (einstr p s' e) (rgof s e) = Some d).
Proof.
  intros e. unfold einstr, rgof. rewrite ai_match.
  destruct (Nat.eqb_spec (ec e) c), (Nat.eqb_spec (ek e) k); simpl; auto.
  rewrite e0, e1, Ha. destruct (eof_same _ _ _ Hdf) as [D|E].
  - right. split; [apply dof_inst; apply (dof_accd _ _ _ D)|exact D].
  - left. exact E.
Qed.

Ltac prof e := let E := fresh "E" in
  destruct (einstr_match e) as [E|(D1 & D2)];
  [rewrite ?E in *|destruct (same_prof _ _ _ _ D2 D1) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12)];
  unfold rgof in *.

Lemma Inv2_match : Inv2 p s'.
Proof.
  constructor; unfold isw, carr; rewrite ?ent_match; unfold rgof; rewrite ?rg_match.
  - intros t e i0 H Hi0. rewrite ?rg_match. subst i0. prof e.
    + apply (j_val p s J t e _ H eq_refl).
    + rewrite P1, P2, <- (dof_rval _ _ _ _ _ D1 D2). apply (j_val p s J t e _ H eq_refl).
  - intros t e x y H Ey. destruct (j_rf p s J t e x y H Ey) as (A1 & (e' & A2 & A3) & A4 & A5).
    split; auto. split; [exists e'; auto|]. split; auto.
    prof e; [auto|rewrite P1; auto].
  - intros t e i0 H Hi0. rewrite ?rg_match. subst i0. prof e.
    + apply (j_ew p s J t e _ H eq_refl).
    + destruct (j_ew p s J t e _ H eq_refl) as [W1 W2]. unfold wvals in *.
      rewrite P1, P3, P4, P5, P6, P7. split; auto.
  - intros x y Hy. destruct (j_hist p s J x y Hy) as (e & i0 & A1 & A2 & A3 & A4).
    exists e, (einstr p s' e). split; auto. split; auto. split; auto. subst i0. prof e; [auto|rewrite P1; auto].
  - apply (j_nodup p s J).
  - intros c' y Hy. unfold smatch in Hy; simpl in Hy. unfold upd in Hy.
    destruct (Nat.eqb_spec c' c); [subst; apply (j_views p s J c); auto|apply (j_views p s J c'); auto].
  - apply (j_eP p s J).
  - apply (j_wc p s J).
  - intros t e x H. rewrite rv_match. apply (j_rv p s J t e x H).
  - intros t e H Eh Ci Xl. rewrite ?rg_match in Xl |- *. prof e.
    + exact (j_ok p s J t e H Eh Ci Xl).
    + rewrite P5 in Ci. rewrite P2 in Xl. exact (j_ok p s J t e H Eh Ci Xl).
Qed.

End Match2.


(* ---------- a CAS's read alone ---------- *)
Section Read2.
Variables (p : prog) (s : st) (c k : nat) (xs : list cell) (B : nat -> bool) (m' : mst) (a : val) (K : view)
          (u : cell -> option nat) (w : bool) (bv : bool).
Hypothesis I : Inv1 p s.
Hypothesis J : Inv2 p s.
Hypothesis Ho : oc (cs s c) k = None.
Hypothesis Hk : pcs s c <= k.
Hypothesis Hh : oh (cs s c) k = None.
Local Abbreviation i := (ILd Plain xs (fun _ => true)).
Hypothesis He : eff (tm s) i (rg (cs s c)) (mof s c) m' a K u w.
Local Abbreviation t' := (sread s c k Plain xs B m' a K u w bv).
Local Abbreviation new := (newevh s c k i K u w).
Local Abbreviation m := (mof s c).

Lemma rd_w : w = false.
Proof. rewrite (eff_w_spec _ _ _ _ _ _ _ _ _ He). reflexivity. Qed.

Lemma rd_mem : hs t' = hs s /\ wv t' = wv s /\ wc t' = wc s.
Proof. destruct (eff_nowrite _ _ _ _ _ _ _ _ _ He rd_w) as (A1 & A2 & A3). unfold sread; simpl. auto. Qed.

Lemma rd_ent : forall t0, ent t' t0 =
  if Nat.ltb t0 (tm s) then ent s t0 else if Nat.eqb t0 (tm s) then Some new else None.
Proof. intros t0. unfold ent, sread. simpl. rewrite nth_error_app_last, (i_tm p s I). reflexivity. Qed.

Lemma rd_cases : forall t0 e, ent t' t0 = Some e -> (ent s t0 = Some e /\ t0 < tm s) \/ (t0 = tm s /\ e = new).
Proof.
  intros t0 e H. rewrite rd_ent in H. destruct (Nat.ltb_spec t0 (tm s)); auto.
  destruct (Nat.eqb_spec t0 (tm s)); [|discriminate]. injection H as <-. auto.
Qed.

Lemma rd_isw : forall y, isw s y <-> isw t' y.
Proof.
  intros y. split.
  - intros (e & H & Hw). exists e. rewrite rd_ent. assert (L : y < tm s).
    { rewrite (i_tm p s I). unfold ent in H. apply nth_error_Some. congruence. }
    apply Nat.ltb_lt in L. rewrite L. auto.
  - intros (e & H & Hw). apply rd_cases in H. destruct H as [(H & _)|(-> & ->)]; [exists e; auto|].
    cbn [ew] in Hw. rewrite rd_w in Hw. discriminate.
Qed.

Lemma rd_cs : forall c' j, (c' <> c \/ j <> k) ->
  ai (cs t' c') j = ai (cs s c') j /\ rg (cs t' c') j = rg (cs s c') j /\ rv (cs t' c') j = rv (cs s c') j.
Proof.
  intros c' j N. unfold sread; simpl. unfold upd. destruct (Nat.eqb_spec c' c); [|repeat split].
  subst. simpl. destruct (Nat.eqb_spec j k); [destruct N; congruence|repeat split].
Qed.

Lemma rd_k : ai (cs t' c) k = crd Plain xs /\ rg (cs t' c) k = vd bv a /\ rv (cs t' c) k = rdval m u.
Proof. unfold sread; simpl. unfold upd. rewrite !Nat.eqb_refl. simpl. rewrite !Nat.eqb_refl. repeat split. Qed.

Lemma rd_old_not_k : forall t0 e, ent s t0 = Some e -> ~ (ec e = c /\ ek e = k).
Proof.
  intros t0 e H (E1 & E2). destruct (i_et p s I t0 e H) as (_ & X). rewrite E1, E2 in X.
  destruct (eh e); congruence.
Qed.

Lemma rd_u : forall x y, u x = Some y -> isw s y /\ In x (icells i) /\ In y (ids (hs s x)).
Proof.
  intros x y E. pose proof (eff_u _ _ _ _ _ _ _ _ _ He x y E) as X.
  destruct (eff_read _ _ _ _ _ _ _ _ _ He X) as ((R1 & R2) & _).
  assert (Hx : In x (icells i)).
  { destruct (in_dec Nat.eq_dec x (icells i)) as [Q|Q]; auto. rewrite (R2 x Q) in E. discriminate. }
  pose proof (R1 x Hx) as V. rewrite E in V. split; [|auto].
  destruct (j_hist p s J x y V) as (e & i0 & H1 & H2 & _). exists e; auto.
Qed.

Lemma rd_nk : forall c' j, ~ (c' = c /\ j = k) -> c' <> c \/ j <> k.
Proof. intros c' j N. destruct (Nat.eq_dec c' c); [right; intros ->; apply N; auto|left; auto]. Qed.

Lemma rd_old0 : forall t e, ent s t = Some e ->
  einstr p t' e = einstr p s e /\ ieval (einstr p s e) (rgof t' e) = ieval (einstr p s e) (rgof s e) /\
  rg (cs t' (ec e)) (ek e) = rg (cs s (ec e)) (ek e) /\ rv (cs t' (ec e)) (ek e) = rv (cs s (ec e)) (ek e).
Proof.
  intros t e H. pose proof (rd_cs (ec e) (ek e) (rd_nk _ _ (rd_old_not_k t e H))) as (A1 & A2 & A3).
  unfold einstr, rgof. rewrite A1. split; [reflexivity|]. split; [|auto].
  apply (i_det p s I t e H). intros j Hj.
  destruct (Nat.eq_dec (ec e) c) as [E|E]; [destruct (Nat.eq_dec j k) as [E'|E']|].
  - exfalso. subst j. rewrite E in Hj. destruct Hj as [Hj|Hj]; [lia|apply Hj; exact Ho].
  - apply (rd_cs (ec e) j). auto.
  - apply (rd_cs (ec e) j). auto.
Qed.

Lemma Inv2_read : Inv2 p t'.
Proof.
  destruct rd_mem as (Mh & Mv & Mc).
  assert (RDV : forall xs0 u0, rdvs t' xs0 u0 = rdvs s xs0 u0) by (intros; unfold rdvs, rdv; rewrite Mv; reflexivity).
  constructor.
  - (* j_val *)
    intros t e i0 H Hi0. apply rd_cases in H. destruct H as [(H & Ht)|(-> & ->)].
    + destruct (rd_old0 t e H) as (Ei & Q & RE & _). rewrite Ei in Hi0. subst i0.
      destruct (j_val p s J t e _ H eq_refl) as [V1 V2].
      assert (Ex : xload (einstr p s e) (rgof t' e) = xload (einstr p s e) (rgof s e)) by (unfold xload, icond; rewrite Q; auto).
      rewrite Ex, RE, RDV. auto.
    + unfold einstr, rgof in *. cbn [ec ek erf] in *. rewrite (proj1 rd_k) in Hi0. subst i0.
      assert (Xc : xload (crd Plain xs) (rg (cs t' c)) = true) by reflexivity. rewrite Xc.
      assert (Xl : xload i (rg (cs s c)) = true) by reflexivity.
      destruct (eff_read _ _ _ _ _ _ _ _ _ He Xl) as (_ & Ea).
      split; [intros _|intros Z; discriminate]. rewrite (proj1 (proj2 rd_k)), RDV, Ea, rdvals_mof. apply vv_vd.
  - (* j_rf *)
    intros t e x y H Ey. apply rd_cases in H. destruct H as [(H & Ht)|(-> & ->)].
    + destruct (j_rf p s J t e x y H Ey) as (A1 & A2 & A3 & A4). split; auto. split; [apply rd_isw; auto|].
      split; [rewrite (proj1 (rd_old0 t e H)); auto|rewrite Mh; auto].
    + cbn [erf] in Ey. destruct (rd_u x y Ey) as (A1 & A2 & A3). split; [eapply isw_lt; eauto|].
      split; [apply rd_isw; auto|]. unfold einstr. cbn [ec ek]. rewrite (proj1 rd_k). split; [exact A2|rewrite Mh; auto].
  - (* j_ew *)
    intros t e i0 H Hi0. apply rd_cases in H. destruct H as [(H & Ht)|(-> & ->)].
    + destruct (rd_old0 t e H) as (Ei & Q & _). rewrite Ei in Hi0. subst i0.
      destruct (j_ew p s J t e _ H eq_refl) as [W1 W2].
      split.
      * unfold icond in W1 |- *. rewrite Q, (ieval_e _ _ _ Q), RDV. exact W1.
      * intros X. destruct (W2 X) as [Y1 Y2]. split; [rewrite Mv, Y1, (ieval_wvals _ _ _ Q); reflexivity|].
        intros x Hx. rewrite Mh. auto.
    + cbn [eh ew]. rewrite rd_w. split; [reflexivity|discriminate].
  - (* j_hist *)
    intros x y Hy. rewrite Mh in Hy. destruct (j_hist p s J x y Hy) as (e & i0 & A1 & A2 & A3 & A4).
    exists e, i0. assert (L : y < tm s) by (rewrite (i_tm p s I); unfold ent in A1; apply nth_error_Some; congruence).
    rewrite rd_ent. apply Nat.ltb_lt in L. rewrite L. rewrite (proj1 (rd_old0 y e A1)). auto.
  - intros x. rewrite Mh. apply (j_nodup p s J).
  - (* j_views *)
    intros c' y Hy. apply rd_isw.
    assert (G : forall y, mP m' y \/ mA m' y \/ mR m' y \/ mG m' y \/ K y -> isw s y).
    { intros y0 Hy0. destruct (eff_views _ _ _ _ _ _ _ _ _ He y0 Hy0)
        as [Q|[(x & Q)|[(x & z & Q1 & Q2)|(Q1 & Q2)]]].
      - apply (old4_isw p s c y0 J Q).
      - apply (rd_u x y0 Q).
      - simpl in Q2. apply (j_wc p s J z y0 Q2).
      - rewrite rd_w in Q1. discriminate. }
    unfold sread in Hy; simpl in Hy. unfold upd in Hy. destruct (Nat.eqb_spec c' c).
    + simpl in Hy. apply G. tauto.
    + destruct Hy as [Hy|[Hy|[Hy|Hy]]]; try (apply (j_views p s J c'); tauto). apply G. tauto.
  - (* j_eP *)
    intros t e y H Hy. apply rd_cases in H. destruct H as [(H & Ht)|(-> & ->)].
    + destruct (j_eP p s J t e y H Hy). split; [apply rd_isw; auto|auto].
    + cbn [eP] in Hy. apply (eff_K_old _ _ _ _ _ _ _ _ _ He) in Hy.
      assert (Q : isw s y) by (apply (old4_isw p s c y J Hy)). split; [apply rd_isw; auto|]. eapply isw_lt; eauto.
  - (* j_wc *)
    intros y y' Hy. rewrite Mc in Hy. destruct (j_wc p s J y y' Hy) as (A1 & A2 & A3).
    split; [apply rd_isw; auto|]. simpl. lia.
  - (* j_rv *)
    intros t e x H. apply rd_cases in H. destruct H as [(H & Ht)|(-> & ->)].
    + rewrite (proj2 (proj2 (proj2 (rd_old0 t e H)))), (j_rv p s J t e x H). unfold rdv. rewrite Mv. reflexivity.
    + cbn [ec ek erf]. rewrite (proj2 (proj2 rd_k)). unfold rdval, rdv. cbn [mof mV]. rewrite Mv. reflexivity.
  - intros t e H Eh Ci Xl. apply rd_cases in H. destruct H as [(H & Ht)|(-> & ->)].
    + destruct (rd_old0 t e H) as (Ei & Q & RE & _). rewrite Ei in Ci, Xl. rewrite RE.
      assert (X' : xload (einstr p s e) (rgof s e) = true) by (unfold xload, icond in *; rewrite <- Q; exact Xl).
      exact (j_ok p s J t e H Eh Ci X').
    + discriminate.
Qed.

End Read2.

Section Skip2.
Variables (p : prog) (s : st) (c : nat).
Hypothesis I : Inv1 p s.
Hypothesis J : Inv2 p s.
Hypothesis Ho : oc (cs s c) (pcs s c) = None.
Hypothesis Hh : oh (cs s c) (pcs s c) <> None ->
  eofR (ins p c (pcs s c) (rg (cs s c))) (rg (cs s c)) = eofR (ai (cs s c) (pcs s c)) (rg (cs s c)).
Local Abbreviation s' := (sskip p s c).

(* the entries, and what each executed, are the same *)
Lemma ent_skip : forall t, ent s' t = ent s t.
Proof. reflexivity. Qed.

(* the entry of a CAS's read alone passed (it failed): it executed that CAS *)
Lemma einstr_skip : forall t e, ent s t = Some e -> einstr p s' e = einstr p s e \/
  (eh e = true /\ exists xs, einstr p s e = crd Plain xs /\ icells (einstr p s' e) = icells (crd Plain xs) /\
     xload (einstr p s' e) (rgof s e) = true /\ is_cas (einstr p s' e) = true).
Proof.
  intros t e H. unfold einstr. rewrite (ai_skip p s c). destruct (i_et p s I t e H) as (_ & E).
  destruct (Nat.eqb_spec (ec e) c), (Nat.eqb_spec (ek e) (pcs s c)); simpl; auto.
  right. rewrite e0, e1 in E |- *. destruct (eh e) eqn:Eh; [|congruence]. split; [reflexivity|].
  destruct (i_half p s I c (pcs s c) t Ho E (le_n _)) as (_ & (xs & Ax) & _). exists xs. split; [exact Ax|].
  unfold rgof. rewrite e0. assert (Ef : eofR (ins p c (pcs s c) (rg (cs s c))) (rg (cs s c)) = eofR (crd Plain xs) (rg (cs s c)))
    by (rewrite <- Ax; apply Hh; congruence).
  destruct (eofR_half _ _ _ Ef) as (G1 & G2). split; [exact G1|split; [exact G2|apply (eofR_cas _ (rg (cs s c)) (Plain, xs)); rewrite Ef; reflexivity]].
Qed.

Lemma rgof_skip : forall e, rgof s' e = rgof s e.
Proof. intros e. unfold rgof. rewrite (rg_skip p s c). reflexivity. Qed.

Lemma Inv2_skip : Inv2 p s'.
Proof.
  assert (RV : forall c', rv (cs s' c') = rv (cs s c')) by apply (rv_skip p s c).
  assert (RG : forall c', rg (cs s' c') = rg (cs s c')) by apply (rg_skip p s c).
  constructor; unfold isw, carr; rewrite ?ent_skip.
  - intros t e i0 H Hi0. rewrite rgof_skip, RG. destruct (einstr_skip t e H) as [E|(Eh & xs & A & Ic & Xl & Cs)].
    + rewrite E in Hi0. exact (j_val p s J t e i0 H Hi0).
    + subst i0. rewrite Ic, Xl. destruct (j_val p s J t e _ H A) as [V _]. split; [intros _|intros; discriminate].
      rewrite (rval_cas _ _ Cs). rewrite (rval_cas (crd Plain xs) _ eq_refl) in V. apply V. reflexivity.
  - intros t e x y H Ey. destruct (einstr_skip t e H) as [E|(Eh & xs & A & Ic & Xl & Cs)].
    + rewrite E. exact (j_rf p s J t e x y H Ey).
    + rewrite Ic, <- A. exact (j_rf p s J t e x y H Ey).
  - intros t e i0 H Hi0. rewrite rgof_skip. destruct (einstr_skip t e H) as [E|(Eh & xs & A & Ic & Xl & Cs)].
    + rewrite E in Hi0. exact (j_ew p s J t e i0 H Hi0).
    + destruct (j_ew p s J t e _ H A) as [W _]. rewrite Eh in W |- *. simpl in W |- *.
      split; [exact W|intros Z; congruence].
  - intros x y Hy. destruct (j_hist p s J x y Hy) as (e & i0 & A1 & A2 & A3 & A4).
    exists e, i0. split; [exact A1|]. split; [exact A2|]. split; [|exact A4].
    destruct (einstr_skip y e A1) as [E|(Eh & xs & A & Ic & Xl & Cs)]; [rewrite E; exact A3|].
    exfalso. destruct (j_ew p s J y e _ A1 eq_refl) as [W _]. rewrite Eh in W. simpl in W. congruence.
  - apply (j_nodup p s J).
  - intros c' y Hy. unfold sskip in Hy; simpl in Hy. unfold upd in Hy.
    destruct (Nat.eqb_spec c' c); [subst; apply (j_views p s J c); auto|apply (j_views p s J c'); auto].
  - apply (j_eP p s J).
  - apply (j_wc p s J).
  - intros t e x H. rewrite RV. apply (j_rv p s J t e x H).
  - intros t e H Eh Ci Xl. rewrite rgof_skip in Xl. rewrite RG.
    destruct (einstr_skip t e H) as [E|(Eh' & _)]; [|congruence]. rewrite E in Ci, Xl. exact (j_ok p s J t e H Eh Ci Xl).
Qed.

End Skip2.

(* ---------- a CAS whose read happened alone commits to failure ---------- *)
Section Cfail2.
Variables (p : prog) (s : st) (c k : nat).
Hypothesis I : Inv1 p s.
Hypothesis J : Inv2 p s.
Hypothesis Hp : pcs s c <= k.
Hypothesis Ho : oc (cs s c) k = None.
Hypothesis Hh : oh (cs s c) k <> None.
Local Abbreviation s' := (scfail s c k).

Lemma Inv2_cfail : Inv2 p s'.
Proof.
  assert (EI : forall e, einstr p s' e = einstr p s e).
  { intros e. unfold einstr. rewrite ai_cf. reflexivity. }
  assert (IE : forall t e, ent s t = Some e -> ieval (einstr p s e) (rgof s' e) = ieval (einstr p s e) (rgof s e)).
  { intros t e E. unfold einstr, rgof. eapply ieval_cf; eauto. }
  assert (XL : forall t e i, ent s t = Some e -> einstr p s e = i -> xload i (rgof s' e) = xload i (rgof s e)).
  { intros t e i E <-. unfold xload, icond. rewrite (IE t e E). reflexivity. }
  assert (RV : forall t e, ent s t = Some e ->
     rval (einstr p s e) (rg (cs s' (ec e)) (ek e)) = rval (einstr p s e) (rg (cs s (ec e)) (ek e)) /\
     (xload (einstr p s e) (rgof s e) = false -> rg (cs s' (ec e)) (ek e) = rg (cs s (ec e)) (ek e))).
  { intros t e E. destruct (Nat.eq_dec (ec e) c) as [Ec|Nc]; [destruct (Nat.eq_dec (ek e) k) as [Ek|Nk]|].
    - destruct (oh (cs s c) k) as [th|] eqn:Oh; [|congruence].
      destruct (i_half p s I c k th Ho Oh Hp) as (_ & (xs & Ax) & _).
      unfold einstr. rewrite Ec, Ek, Ax, cs_cf, Nat.eqb_refl. simpl. unfold upd. rewrite Nat.eqb_refl.
      split; [apply vv_vd|intros Z; discriminate].
    - rewrite rg_cf by (right; exact Nk). split; auto.
    - rewrite rg_cf by (left; exact Nc). split; auto. }
  constructor; unfold isw, carr; rewrite ?ent_cf; cbn [wv hs vG wc scfail].
  - intros t e i0 H Hi0. rewrite EI in Hi0. rewrite (XL t e i0 H Hi0). subst i0.
    destruct (j_val p s J t e _ H eq_refl) as [V1 V2]. destruct (RV t e H) as (R1 & R2). split.
    + intros X. rewrite R1. exact (V1 X).
    + intros X. destruct (V2 X) as (Z & N). split; [rewrite (R2 X); exact Z|exact N].
  - intros t e x y H Ey. rewrite EI. exact (j_rf p s J t e x y H Ey).
  - intros t e i0 H Hi0. rewrite EI in Hi0. subst i0. pose proof (IE t e H) as Q.
    destruct (j_ew p s J t e _ H eq_refl) as [W1 W2]. split.
    + unfold icond in W1 |- *. rewrite Q, (ieval_e _ _ _ Q). exact W1.
    + intros X. destruct (W2 X) as [Y1 Y2]. split; [rewrite Y1, (ieval_wvals _ _ _ Q); reflexivity|exact Y2].
  - intros x y Hy. destruct (j_hist p s J x y Hy) as (e & i0 & A1 & A2 & A3 & A4).
    exists e, i0. rewrite EI. auto.
  - apply (j_nodup p s J).
  - intros c' y Hy. rewrite cs_cf in Hy. destruct (Nat.eqb_spec c' c); [subst; apply (j_views p s J c); exact Hy|apply (j_views p s J c'); exact Hy].
  - apply (j_eP p s J).
  - apply (j_wc p s J).
  - intros t e x H. rewrite rv_cf. apply (j_rv p s J t e x H).
  - intros t e H Eh Ci Xl. rewrite EI in Ci, Xl. unfold rgof in Xl.
    assert (X' : xload (einstr p s e) (rgof s e) = true) by (unfold xload, icond in *; rewrite <- (IE t e H); exact Xl).
    rewrite rg_cf; [exact (j_ok p s J t e H Eh Ci X')|].
    destruct (Nat.eq_dec (ec e) c) as [Ec|N]; [right|left; exact N]. intros Ek.
    destruct (i_et p s I t e H) as (_ & Oc). rewrite Eh, Ec, Ek in Oc. congruence.
Qed.

End Cfail2.

(* S3c: a result fixed changes only bd and fx *)
Lemma Inv2_cfix : forall p s c j b B, Inv2 p s -> Inv2 p (scfix0 s c j b B).
Proof.
  intros p s c j b B J. destruct J; constructor; unfold einstr, rgof, isw, rdvs, rdv in *;
    change (tm (scfix0 s c j b B)) with (tm s) in *; change (hs (scfix0 s c j b B)) with (hs s) in *;
    change (wv (scfix0 s c j b B)) with (wv s) in *; change (wc (scfix0 s c j b B)) with (wc s) in *;
    change (vG (scfix0 s c j b B)) with (vG s) in *; intros;
    rewrite ?(ent_cx s c j b B), ?(ai_cx s c j b B), ?(rg_cx s c j b B), ?(rv_cx s c j b B),
      ?(vP_cx s c j b B), ?(vA_cx s c j b B), ?(vR_cx s c j b B) in *; eauto.
  match goal with Hy : In ?y (ids (hs s ?x)) |- _ =>
    destruct (j_hist0 x y Hy) as (e & i & ?); exists e, i; rewrite (ai_cx s c j b B); assumption end.
Qed.

Lemma Inv2_es : forall p t e, Inv2 p t -> Inv2 p (set_es t e).
Proof. intros p t e J. destruct J; constructor; auto. Qed.

Lemma Inv2_run : forall p s, run p s -> Inv1 p s /\ Inv2 p s.
Proof.
  intros p s R. induction R as [|s t R IH H].
  - split; [apply Inv1_init|apply Inv2_init].
  - destruct IH as [I J]. split; [apply (Inv1_run p t); econstructor; eauto|].
    destruct (step_cases p s t H) as [(c & i & m' & a & K & u & w & H1 & H2 & H3 & H4 & Hbh & Hh & _ & _ & H6 & _ & ->)
      |[(c & k & d & B & m' & a & K & u & w & H1 & H2 & Hso & Hh & _ & _ & H5 & _ & ->)
      |[(c & d & H1 & H2 & H3 & H4 & H4m & Hfh & ->)|[(c & k & xs & B & m' & a & K & u & w & bv & H1 & H2 & Hh & Hso & H4 & H5 & _ & ->)
      |[(c & S1 & S2 & S3 & S6 & S5 & S4 & _ & ->)|(cX & jX & bX & BX & oX & HjX & HfX & HcX & ->)]]]]].
    + eapply Inv2_step; eauto; [intros r Sr; apply (proj2 (H3 r Sr))|].
      destruct Hh as [(Z & _)|(t1 & Z & Ci & U & Ef)]; [left; exact Z|right].
      split; [exact U|exact Ef].
    + apply Inv2_es. eapply Inv2_step; eauto; [lia|intros r Sr; apply ieval_inst|].
      destruct Hh as [(Z & _)|(t1 & xs & ev & nv & Z & -> & U & Ac & _)]; [left; exact Z|right].
      split; [exact U|]. rewrite Ac. reflexivity.
    + eapply Inv2_match; eauto.
    + apply Inv2_read; auto.
    + apply Inv2_skip; auto.
    + destruct oX as [kX|]; [destruct bX|]; cbn [sflp]; apply Inv2_cfix; [auto| |auto].
      destruct (cfix_rec _ _ _ _ _ _ _ _ _ HcX) as (HpX & HoX & HhX & _). apply Inv2_cfail; auto.
Qed.
