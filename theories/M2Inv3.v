(* Model2: invariants of runs: what each context knows, and how fences and guard
   operations pass knowledge on. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2.

Definition xg (p : prog) (s : st) (e : oev) : Prop :=
  exists i, einstr p s e = i /\ xgop i (rgof s e) = true.
Definition xl (p : prog) (s : st) (e : oev) : Prop :=
  exists i, einstr p s e = i /\ xload i (rgof s e) = true.
Definition xll (p : prog) (s : st) (e : oev) : Prop := einstr p s e = IFn FLl.
Definition xss (p : prog) (s : st) (e : oev) : Prop := einstr p s e = IFn FSs.

Record Inv3 (p : prog) (s : st) : Prop := {
  k_RP : forall c, vsub (vR (cs s c)) (vor (vP (cs s c)) (vA (cs s c)));
  k_Pcur : forall t e, ent s t = Some e ->
    vsub (eP e) (vP (cs s (ec e))) /\ vsub (esrc e) (vP (cs s (ec e)));
  k_Ppair : forall t e t' e', ent s t = Some e -> ent s t' = Some e' -> ec e = ec e' -> t < t' ->
    vsub (eP e) (eP e') /\ vsub (esrc e) (eP e');
  k_Gcur : forall t e, ent s t = Some e -> xg p s e -> vsub (eP e) (vG s) /\ vsub (esrc e) (vG s);
  k_Gpair : forall t e t' e', ent s t = Some e -> ent s t' = Some e' -> xg p s e -> xg p s e' ->
    t < t' -> vsub (eP e) (eP e') /\ vsub (esrc e) (eP e');
  (* a guard.rs() or guard() f, with no guard.rs() of its context after
     it: the release view has what an earlier access knew or wrote; for
     guard.rs() only the context's own writes *)
  k_Rcur : forall t e t' f, ent s t = Some e -> ent s t' = Some f -> ec e = ec f -> t <= t' ->
    (xss p s f \/ xg p s f) ->
    (forall tg g, ent s tg = Some g -> ec g = ec f -> t' < tg -> ~ xss p s g) ->
    forall v, (eP e v \/ esrc e v) -> (xg p s f \/ ownw s (ec f) v) -> vR (cs s (ec f)) v;
  k_Rpair : forall te e tf f tw w', ent s te = Some e -> ent s tf = Some f -> ent s tw = Some w' ->
    ec e = ec f -> ec f = ec w' -> te <= tf -> tf <= tw -> te < tw -> (xss p s f \/ xg p s f) -> ew w' = true ->
    (forall tg g, ent s tg = Some g -> ec g = ec f -> tf < tg -> tg < tw -> ~ xss p s g) ->
    forall v, (eP e v \/ esrc e v) -> (xg p s f \/ ownw s (ec f) v) -> wc s tw v;
  k_Acur : forall t l, ent s t = Some l -> xl p s l -> vsub (carr s (erf l)) (vA (cs s (ec l)));
  k_Acq : forall tl l tf f, ent s tl = Some l -> ent s tf = Some f -> ec l = ec f -> tl < tf ->
    xl p s l -> (xll p s f \/ xg p s f) -> vsub (carr s (erf l)) (vP (cs s (ec f)));
  k_Aselfc : forall t l, ent s t = Some l -> xl p s l -> xg p s l ->
    vsub (carr s (erf l)) (vP (cs s (ec l)));
  k_Aself : forall tl l te e, ent s tl = Some l -> ent s te = Some e -> ec l = ec e -> tl < te ->
    xl p s l -> xg p s l -> vsub (carr s (erf l)) (eP e);
  k_Apair : forall tl l tf f te e, ent s tl = Some l -> ent s tf = Some f -> ent s te = Some e ->
    ec l = ec f -> ec f = ec e -> tl < tf -> xl p s l ->
    ((xll p s f /\ tf < te) \/ (xg p s f /\ tf <= te)) -> vsub (carr s (erf l)) (eP e)
}.

Lemma Inv3_init : forall p, Inv3 p sinit.
Proof.
  intros p. constructor; unfold ent; simpl; intros.
  all: try (match goal with H : nth_error [] ?t = Some _ |- _ => destruct t; discriminate end).
  unfold vsub; intros; contradiction.
Qed.

Lemma vsub_trans : forall a b c, vsub a b -> vsub b c -> vsub a c.
Proof. unfold vsub; auto. Qed.

Set Default Proof Using "All".
Section Step.
Variables (p : prog) (s : st) (c k : nat) (i : instr) (m' : mst) (a : val) (K : view)
          (u : cell -> option nat) (w : bool) (Bd : nat -> bool) (pc' tp' : nat -> nat)
          (cm' : list (nat * nat * nat)).
Hypothesis I : Inv1 p s.
Hypothesis J : Inv2 p s.
Hypothesis L : Inv3 p s.
Hypothesis Ho : oc (cs s c) k = None.
Hypothesis Hk : pcs s c <= k.
Hypothesis Hst : forall r, settled (cs s c) (pcs s c) r -> ieval i r = ieval i (rg (cs s c)).
Hypothesis He : eff (tm s) i (rg (cs s c)) (mof s c) m' a K u w.
Hypothesis Hhk : oh (cs s c) k = None \/
  (u = rw (cs s c) k /\ eofR i (rg (cs s c)) = eofR (ai (cs s c) k) (rg (cs s c))).

Local Abbreviation t' := (evs s c k i m' a K u w Bd pc' tp' cm').
Local Abbreviation new := (newev s c k i K u w).
Local Abbreviation m := (mof s c).
Local Abbreviation ent_cases' := (ent_cases p s c k i m' a K u w Bd pc' tp' cm' I J Ho Hk Hst He Hhk).
Local Abbreviation old_ent' := (old_ent p s c k i m' a K u w Bd pc' tp' cm' I J Ho Hk Hst He Hhk).
Local Abbreviation ieval_old' := (ieval_old p s c k i m' a K u w Bd pc' tp' cm' I J Ho Hk Hst He Hhk).
Local Abbreviation ieval_old0' := (ieval_old0 p s c k i m' a K u w Bd pc' tp' cm' I J Ho Hk Hst He Hhk).
Local Abbreviation ins_new' := (ins_new p s c k i m' a K u w Bd pc' tp' cm' I J Ho Hk Hst He Hhk).
Local Abbreviation ieval_new' := (ieval_new p s c k i m' a K u w Bd pc' tp' cm' I J Ho Hk Hst He Hhk).
Local Abbreviation t_hs1' := (t_hs1 p s c k i m' a K u w Bd pc' tp' cm' I J Ho Hk Hst He Hhk).
Local Abbreviation wc_old' := (wc_old p s c k i m' a K u w Bd pc' tp' cm' I J Ho Hk Hst He Hhk).

Lemma cs_new : cs t' c = mkC (upd (oc (cs s c)) k (Some (tm s))) (upd (rg (cs s c)) k a) (upd (ai (cs s c)) k i)
  (upd (rw (cs s c)) k (wrote (tm s) (icells i) u w)) (upd (rv (cs s c)) k (rdval (mof s c) u)) Bd (mP m') (mA m') (mR m')
  (newO s c i (mof s c) m' (vO (cs s c))) (newOg i m' (vOg (cs s c))) (oh (cs s c)) (fx (cs s c)).
Proof. unfold evs; simpl. apply upd_eq. Qed.

Lemma cs_old : forall c', c' <> c -> cs t' c' = cs s c'.
Proof. intros c' N. unfold evs; simpl. apply upd_neq. auto. Qed.

Lemma vG_new : vG t' = mG m'.
Proof. reflexivity. Qed.

Lemma ent_lt : forall t0 e, ent s t0 = Some e -> t0 < tm s.
Proof. intros t0 e H. apply (old_ent' t0 e H). Qed.

Lemma cas_nofn : forall i0 g, is_cas i0 = true -> isfn g i0 = false.
Proof. intros [] g H; try discriminate; reflexivity. Qed.

(* the CAS's read alone at the slot of the step, now with its write *)
Lemma half_x : forall t0 e, ent s t0 = Some e -> ec e = c -> ek e = k ->
  einstr p t' e = i /\ (exists xs, einstr p s e = crd Plain xs) /\ is_cas i = true /\ xload i (rgof t' e) = true.
Proof.
  intros t0 e H E1 E2.
  destruct (half_k p s c k i m' a K u w Bd pc' tp' cm' I J Ho Hk Hst He Hhk t0 e H E1 E2) as (_ & _ & Xl & _ & _ & (xs & Ax & _) & Ci).
  unfold einstr, rgof. rewrite E1, E2. split; [exact ins_new'|]. split; [exists xs; exact Ax|]. split; [exact Ci|].
  unfold xload. rewrite (ieval_cond _ _ _ ieval_new'). exact Xl.
Qed.

Lemma xg_old : forall t0 e, ent s t0 = Some e -> xg p t' e <-> xg p s e.
Proof.
  intros t0 e H. destruct (at_dec p s c k i m' a K u w Bd pc' tp' cm' I J Ho Hk Hst He Hhk e) as [(E1 & E2)|N].
  - destruct (half_x t0 e H E1 E2) as (A1 & (xs & A2) & A3 & _). unfold xg, xgop.
    split; intros (i0 & E & X); subst i0; [rewrite A1, cas_nofn in X by exact A3|rewrite A2 in X]; discriminate.
  - destruct (ieval_old0' t0 e H N) as [A _]. unfold xg, xgop.
    split; intros (i0 & E & X); exists i0; split; auto; congruence.
Qed.

Lemma xl_old : forall t0 e, ent s t0 = Some e -> xl p t' e <-> xl p s e.
Proof.
  intros t0 e H. destruct (at_dec p s c k i m' a K u w Bd pc' tp' cm' I J Ho Hk Hst He Hhk e) as [(E1 & E2)|N].
  - destruct (half_x t0 e H E1 E2) as (A1 & (xs & A2) & A3 & A4). unfold xl.
    split; intros _.
    + exists (crd Plain xs). split; [exact A2|reflexivity].
    + exists i. split; [exact A1|exact A4].
  - destruct (ieval_old0' t0 e H N) as [A B]. unfold xl, xload.
    rewrite A. pose proof (ieval_cond _ _ _ B) as Q.
    split; intros (i0 & E & X); exists i0; subst i0; split; auto; [rewrite <- Q|rewrite Q]; auto.
Qed.

Lemma xrel_old : forall t0 e, ent s t0 = Some e -> xss p t' e <-> xss p s e.
Proof.
  intros t0 e H. destruct (at_dec p s c k i m' a K u w Bd pc' tp' cm' I J Ho Hk Hst He Hhk e) as [(E1 & E2)|N].
  - destruct (half_x t0 e H E1 E2) as (A1 & (xs & A2) & A3 & _). unfold xss. rewrite A1, A2.
    split; intros X; [subst i; discriminate|discriminate].
  - destruct (ieval_old0' t0 e H N) as [A _]. unfold xss. rewrite A. tauto.
Qed.

Lemma xacq_old : forall t0 e, ent s t0 = Some e -> xll p t' e <-> xll p s e.
Proof.
  intros t0 e H. destruct (at_dec p s c k i m' a K u w Bd pc' tp' cm' I J Ho Hk Hst He Hhk e) as [(E1 & E2)|N].
  - destruct (half_x t0 e H E1 E2) as (A1 & (xs & A2) & A3 & _). unfold xll. rewrite A1, A2.
    split; intros X; [subst i; discriminate|discriminate].
  - destruct (ieval_old0' t0 e H N) as [A _]. unfold xll. rewrite A. tauto.
Qed.

Lemma xg_new : xg p t' new <-> xgop i (rg (cs s c)) = true.
Proof.
  unfold xg, xgop. split; [intros (i0 & A & B); rewrite ins_new' in A; subst i0; exact B|].
  intros B. exists i. split; auto. apply ins_new'.
Qed.

Lemma xl_new : xl p t' new <-> xload i (rg (cs s c)) = true.
Proof.
  unfold xl. rewrite ins_new'. unfold rgof; cbn [ec].
  pose proof (ieval_cond _ _ _ ieval_new') as Q.
  split; [intros (i0 & A & B); subst i0; unfold xload in *; rewrite <- Q; exact B|].
  intros B. exists i. split; auto. unfold xload in *. rewrite Q. exact B.
Qed.

Lemma carr_old : forall u0, (forall x y, u0 x = Some y -> y < tm s) -> vsub (carr t' u0) (carr s u0).
Proof.
  intros u0 H w' (x & y & E & Q). exists x, y. split; auto. rewrite wc_old' in Q; eauto.
Qed.

Lemma carr_l : forall t0 e, ent s t0 = Some e -> vsub (carr t' (erf e)) (carr s (erf e)).
Proof.
  intros t0 e H. apply carr_old. intros x y Ey. destruct (j_rf p s J t0 e x y H Ey). pose proof (ent_lt t0 e H). lia.
Qed.

Lemma carr_u : vsub (carr t' u) (carr s u).
Proof.
  apply carr_old. intros x y Ey. apply (isw_lt p s y I). apply (u_isw p s c k i m' a K u w Bd pc' tp' cm' I J Ho Hk Hst He Hhk x y Ey).
Qed.

Lemma esrc_new : esrc new = srcv u w (tm s).
Proof. reflexivity. Qed.

Lemma own_old : forall c' v, v < tm s -> ownw t' c' v -> ownw s c' v.
Proof.
  intros c' v Lv (e & E & C & W). exists e. split; auto. unfold evs in E; simpl in E.
  rewrite nth_error_app1 in E; auto. rewrite <- (i_tm p s I). exact Lv.
Qed.

(* what an old access knew or wrote is older than now *)
Lemma pv_old : forall t0 e, ent s t0 = Some e -> forall v, eP e v \/ esrc e v -> v < tm s.
Proof.
  intros t0 e H v [Hv|Hv].
  - destruct (j_eP p s J t0 e v H Hv) as [_ L0]. pose proof (ent_lt t0 e H). lia.
  - unfold esrc, srcv, vor, srcs, vone, vnil in Hv. destruct Hv as [(x & Hx)|Hv].
    + destruct (j_rf p s J t0 e x v H Hx) as (L0 & _). pose proof (ent_lt t0 e H). lia.
    + destruct (ew e); [|destruct Hv]. rewrite Hv. destruct (i_et p s I t0 e H) as [Et _]. rewrite Et. apply (ent_lt t0 e H).
Qed.

Lemma Inv3_step : Inv3 p t'.
Proof.
  pose proof (eff_K_P _ _ _ _ _ _ _ _ _ He) as KP.
  pose proof (eff_K_P' _ _ _ _ _ _ _ _ _ He) as KP'.
  pose proof (eff_src _ _ _ _ _ _ _ _ _ He) as SP'.
  pose proof (eff_R _ _ _ _ _ _ _ _ _ He (k_RP p s L c)) as RP'.
  pose proof (eff_A _ _ _ _ _ _ _ _ _ He) as AA.
  pose proof (eff_G _ _ _ _ _ _ _ _ _ He) as GG.
  assert (PP : vsub (vP (cs s c)) (mP m')) by (eapply vsub_trans; eauto).
  constructor.
  - (* k_RP *)
    intros c'. destruct (Nat.eq_dec c' c) as [->|N].
    + rewrite cs_new; cbn [vP vA vR oc rg]. exact RP'.
    + rewrite cs_old by auto. apply (k_RP p s L).
  - (* k_Pcur *)
    intros t e H. apply ent_cases' in H. destruct H as [(H & Ht)|(-> & ->)].
    + destruct (k_Pcur p s L t e H) as [A B]. destruct (Nat.eq_dec (ec e) c) as [E|N].
      * rewrite E in *. rewrite cs_new; cbn [vP vA vR oc rg]. split; eauto 6 using vsub_trans.
      * rewrite cs_old by auto. auto.
    + cbn [ec eP]. rewrite cs_new; cbn [vP vA vR oc rg]. split; auto.
  - (* k_Ppair *)
    intros t e t2 e2 H H2 E T. apply ent_cases' in H, H2.
    destruct H as [(H & Ht)|(-> & ->)]; destruct H2 as [(H2 & Ht2)|(-> & ->)]; try lia.
    + apply (k_Ppair p s L t e t2 e2 H H2 E T).
    + cbn [ec eP] in *. destruct (k_Pcur p s L t e H) as [A B]. rewrite E in A, B.
      split; eauto 6 using vsub_trans.
  - (* k_Gcur *)
    intros t e H X. apply ent_cases' in H. destruct H as [(H & Ht)|(-> & ->)].
    + rewrite xg_old in X by eauto. destruct (k_Gcur p s L t e H X) as [A B].
      rewrite vG_new. split; eauto 6 using vsub_trans.
    + apply xg_new in X. destruct (eff_gop _ _ _ _ _ _ _ _ _ He X) as (A1 & A2 & A3 & A4).
      rewrite vG_new. cbn [eP]. split; eauto 6 using vsub_trans.
  - (* k_Gpair *)
    intros t e t2 e2 H H2 X X2 T. apply ent_cases' in H, H2.
    destruct H as [(H & Ht)|(-> & ->)]; destruct H2 as [(H2 & Ht2)|(-> & ->)]; try lia.
    + rewrite xg_old in X, X2 by eauto. apply (k_Gpair p s L t e t2 e2 H H2 X X2 T).
    + rewrite xg_old in X by eauto. apply xg_new in X2.
      destruct (eff_gop _ _ _ _ _ _ _ _ _ He X2) as (A1 & A2 & A3 & A4).
      destruct (k_Gcur p s L t e H X) as [B1 B2]. cbn [eP]. split; eauto 6 using vsub_trans.
  - (* k_Rcur *)
    intros t e t2 f H H2 E T X NR v Hv Ov. apply ent_cases' in H, H2.
    destruct H as [(H & Ht)|(-> & ->)]; destruct H2 as [(H2 & Ht2)|(-> & ->)]; try lia.
    + assert (X' : xss p s f \/ xg p s f) by (destruct X; [left; rewrite <- xrel_old by eauto|right; rewrite <- xg_old by eauto]; auto).
      assert (Lv : v < tm s) by (apply (pv_old t e H v Hv)).
      assert (NR' : forall tg g, ent s tg = Some g -> ec g = ec f -> t2 < tg -> ~ xss p s g).
      { intros tg g Hg Eg Lg Rg. apply (NR tg g); auto.
        - unfold ent, evs; simpl. rewrite nth_error_app1; [exact Hg|]. rewrite <- (i_tm p s I). apply (ent_lt tg g Hg).
        - rewrite xrel_old by eauto. exact Rg. }
      assert (Ov' : xg p s f \/ ownw s (ec f) v).
      { destruct Ov as [Ov|Ov]; [left; rewrite <- xg_old by eauto; exact Ov|right; apply (own_old _ v Lv Ov)]. }
      pose proof (k_Rcur p s L t e t2 f H H2 E T X' NR' v Hv Ov') as Rv.
      destruct (Nat.eq_dec (ec f) c) as [Ef|N].
      * rewrite Ef in *. rewrite cs_new; cbn [vR].
        apply (eff_R_mono _ _ _ _ _ _ _ _ _ He (k_RP p s L c)). exact Rv.
      * rewrite cs_old by auto. exact Rv.
    + (* f is the new step *)
      cbn [ec] in *. rewrite cs_new; cbn [vR]. destruct (k_Pcur p s L t e H) as [A B]. rewrite E in A, B.
      assert (Pv : vP (cs s c) v) by (destruct Hv as [Hv|Hv]; [apply A|apply B]; exact Hv).
      assert (Lv : v < tm s) by (apply (pv_old t e H v Hv)).
      destruct X as [X|X].
      * unfold xss in X. rewrite ins_new' in X.
        apply (eff_ss _ _ _ _ _ _ _ _ _ He X). split; [exact Pv|].
        destruct Ov as [Ov|Ov]; [apply xg_new in Ov; rewrite X in Ov; discriminate Ov|]. apply (own_old _ v Lv Ov).
      * apply xg_new in X. destruct (eff_gop _ _ _ _ _ _ _ _ _ He X) as (A1 & A2 & A3 & A4).
        apply A4. apply (eff_P_mono _ _ _ _ _ _ _ _ _ He). exact Pv.
    + (* both the new step: a fence knows only what its context had *)
      cbn [ec eP esrc] in *. rewrite cs_new; cbn [vR]. destruct X as [X|X].
      * unfold xss in X. rewrite ins_new' in X.
        rewrite (eff_K _ _ _ _ _ _ _ _ _ He ltac:(rewrite X; reflexivity)) in Hv.
        destruct (eff_noread _ _ _ _ _ _ _ _ _ He ltac:(rewrite X; reflexivity)) as [_ U].
        rewrite (eff_w_spec _ _ _ _ _ _ _ _ _ He) in Hv. rewrite X in Hv.
        destruct Hv as [Hv|Hv].
        -- apply (eff_ss _ _ _ _ _ _ _ _ _ He X). split; [exact Hv|].
           destruct Ov as [Ov|Ov]; [apply xg_new in Ov; rewrite X in Ov; discriminate Ov|]. apply (own_old _ v (isw_lt p s v I (j_views p s J c v (or_introl Hv))) Ov).
        -- unfold esrc, srcv, vor, srcs, vnil in Hv. simpl in Hv. destruct Hv as [(x & Hx)|Hv]; [rewrite U in Hx; discriminate|tauto].
      * apply xg_new in X. destruct (eff_gop _ _ _ _ _ _ _ _ _ He X) as (A1 & A2 & A3 & A4).
        apply A4. destruct Hv as [Hv|Hv].
        -- apply (eff_K_P' _ _ _ _ _ _ _ _ _ He). exact Hv.
        -- apply (eff_src _ _ _ _ _ _ _ _ _ He). exact Hv.
  - (* k_Rpair *)
    intros te e tf f tw w2 H Hf Hw E1 E2 T1 T2 T3 X W NR v Hv Ov. apply ent_cases' in H, Hf, Hw.
    destruct H as [(H & Ht)|(-> & ->)]; [|lia].
    assert (Lv : v < tm s) by (apply (pv_old te e H v Hv)).
    destruct Hf as [(Hf & Htf)|(-> & ->)]; destruct Hw as [(Hw & Htw)|(-> & ->)]; try lia.
    + assert (X' : xss p s f \/ xg p s f) by (destruct X; [left; rewrite <- xrel_old by eauto|right; rewrite <- xg_old by eauto]; auto).
      assert (NR' : forall tg g, ent s tg = Some g -> ec g = ec f -> tf < tg -> tg < tw -> ~ xss p s g).
      { intros tg g Hg Eg Lg Lg2 Rg. apply (NR tg g); auto.
        - unfold ent, evs; simpl. rewrite nth_error_app1; [exact Hg|]. rewrite <- (i_tm p s I). apply (ent_lt tg g Hg).
        - rewrite xrel_old by eauto. exact Rg. }
      assert (Ov' : xg p s f \/ ownw s (ec f) v).
      { destruct Ov as [Ov|Ov]; [left; rewrite <- xg_old by eauto; exact Ov|right; apply (own_old _ v Lv Ov)]. }
      rewrite wc_old' by auto. apply (k_Rpair p s L te e tf f tw w2 H Hf Hw E1 E2 T1 T2 T3 X' W NR' v Hv Ov').
    + (* the write is the new step *)
      cbn [ew ec] in *.
      assert (X' : xss p s f \/ xg p s f) by (destruct X; [left; rewrite <- xrel_old by eauto|right; rewrite <- xg_old by eauto]; auto).
      assert (NR' : forall tg g, ent s tg = Some g -> ec g = ec f -> tf < tg -> ~ xss p s g).
      { intros tg g Hg Eg Lg Rg. apply (NR tg g); auto.
        - unfold ent, evs; simpl. rewrite nth_error_app1; [exact Hg|]. rewrite <- (i_tm p s I). apply (ent_lt tg g Hg).
        - pose proof (ent_lt tg g Hg). lia.
        - rewrite xrel_old by eauto. exact Rg. }
      assert (Ov' : xg p s f \/ ownw s (ec f) v).
      { destruct Ov as [Ov|Ov]; [left; rewrite <- xg_old by eauto; exact Ov|right; apply (own_old _ v Lv Ov)]. }
      pose proof (k_Rcur p s L te e tf f H Hf E1 T1 X' NR' v Hv Ov') as Rv. rewrite E2 in Rv.
      destruct t_hs1' as (R0 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _); auto.
      rewrite Q6, upd_eq. left. apply Q7. exact Rv.
    + (* the fence/guard is the write itself *)
      cbn [ew ec] in *. destruct X as [X|X].
      * unfold xss in X. rewrite ins_new' in X. rewrite X in *.
        inversion He; subst; discriminate.
      * apply xg_new in X. unfold xgop in X. destruct i as [| | |[]|]; simpl in X; try discriminate.
        inversion He; subst; discriminate.
  - (* k_Acur *)
    intros t l H X. apply ent_cases' in H. destruct H as [(H & Ht)|(-> & ->)].
    + rewrite xl_old in X by eauto. apply (vsub_trans _ _ _ (carr_l t l H)). pose proof (k_Acur p s L t l H X) as A.
      destruct (Nat.eq_dec (ec l) c) as [E|N].
      * rewrite E in *. rewrite cs_new; cbn [vP vA vR oc rg]. eauto 6 using vsub_trans.
      * rewrite cs_old by auto. auto.
    + apply xl_new in X. cbn [ec erf]. rewrite cs_new; cbn [vP vA vR oc rg]. apply (vsub_trans _ _ _ carr_u).
      exact (eff_carr_A _ _ _ _ _ _ _ _ _ He X).
  - (* k_Acq *)
    intros tl l tf f H Hf E T X Y. apply ent_cases' in H, Hf.
    destruct H as [(H & Ht)|(-> & ->)]; [|lia].
    rewrite xl_old in X by eauto. apply (vsub_trans _ _ _ (carr_l tl l H)).
    destruct Hf as [(Hf & Htf)|(-> & ->)].
    + assert (Y' : xll p s f \/ xg p s f) by (destruct Y; [left; rewrite <- xacq_old by eauto|right; rewrite <- xg_old by eauto]; auto).
      pose proof (k_Acq p s L tl l tf f H Hf E T X Y') as A.
      destruct (Nat.eq_dec (ec f) c) as [Ef|N].
      * rewrite Ef in *. rewrite cs_new; cbn [vP vA vR oc rg]. eauto 6 using vsub_trans.
      * rewrite cs_old by auto. auto.
    + cbn [ec] in *. rewrite cs_new; cbn [vP vA vR oc rg]. pose proof (k_Acur p s L tl l H X) as A. rewrite E in A.
      destruct Y as [Y|Y].
      * unfold xll in Y. rewrite ins_new' in Y. rewrite Y in *.
        pose proof (eff_ll _ _ _ _ _ _ _ _ _ He eq_refl). eauto 6 using vsub_trans.
      * apply xg_new in Y. destruct (eff_gop _ _ _ _ _ _ _ _ _ He Y) as (A1 & A2 & A3 & A4).
        eauto 6 using vsub_trans.
  - (* k_Aselfc *)
    intros t l H X G. apply ent_cases' in H. destruct H as [(H & Ht)|(-> & ->)].
    + rewrite xl_old in X by eauto. rewrite xg_old in G by eauto. apply (vsub_trans _ _ _ (carr_l t l H)).
      pose proof (k_Aselfc p s L t l H X G) as A.
      destruct (Nat.eq_dec (ec l) c) as [E|N].
      * rewrite E in *. rewrite cs_new; cbn [vP vA vR oc rg]. eauto 6 using vsub_trans.
      * rewrite cs_old by auto. auto.
    + apply xl_new in X. apply xg_new in G. cbn [ec erf]. rewrite cs_new; cbn [vP vA vR oc rg]. apply (vsub_trans _ _ _ carr_u).
      pose proof (eff_carr_A _ _ _ _ _ _ _ _ _ He X). pose proof (eff_gA _ _ _ _ _ _ _ _ _ He G).
      eauto using vsub_trans.
  - (* k_Aself *)
    intros tl l te e Hl He' E T X G. apply ent_cases' in Hl, He'.
    destruct Hl as [(Hl & Htl)|(-> & ->)]; [|destruct He' as [(_ & Z)|(Z & _)]; lia].
    rewrite xl_old in X by eauto. rewrite xg_old in G by eauto. apply (vsub_trans _ _ _ (carr_l tl l Hl)).
    destruct He' as [(He' & Hte)|(-> & ->)].
    + apply (k_Aself p s L tl l te e Hl He' E T X G).
    + cbn [ec eP] in *. pose proof (k_Aselfc p s L tl l Hl X G) as A. rewrite E in A.
      eauto using vsub_trans.
  - (* k_Apair *)
    intros tl l tf f te e H Hf He' E1 E2 T X Y. apply ent_cases' in H, Hf, He'.
    destruct H as [(H & Ht)|(-> & ->)]; [|lia].
    rewrite xl_old in X by eauto. apply (vsub_trans _ _ _ (carr_l tl l H)).
    destruct Hf as [(Hf & Htf)|(-> & ->)]; destruct He' as [(He' & Hte)|(-> & ->)];
      try (destruct Y as [(_ & Y)|(_ & Y)]; lia).
    + assert (Y' : (xll p s f /\ tf < te) \/ (xg p s f /\ tf <= te))
        by (destruct Y as [(Y1 & Y2)|(Y1 & Y2)]; [left; rewrite <- xacq_old by eauto|right; rewrite <- xg_old by eauto]; auto).
      apply (k_Apair p s L tl l tf f te e H Hf He' E1 E2 T X Y').
    + cbn [ec eP] in *.
      assert (Y' : xll p s f \/ xg p s f)
        by (destruct Y as [(Y & _)|(Y & _)]; [left; rewrite <- xacq_old by eauto|right; rewrite <- xg_old by eauto]; auto).
      pose proof (k_Acq p s L tl l tf f H Hf E1 T X Y') as A. rewrite E2 in A.
      eauto 6 using vsub_trans.
    + cbn [ec eP] in *. destruct Y as [(Y & Y2)|(Y & Y2)]; [lia|].
      apply xg_new in Y. destruct (eff_gop _ _ _ _ _ _ _ _ _ He Y) as (A1 & A2 & A3 & A4).
      pose proof (k_Acur p s L tl l H X) as A. rewrite E1 in A. eauto 6 using vsub_trans.
Qed.

End Step.

(* ---------- a CAS's read alone ---------- *)
Section Read3.
Variables (p : prog) (s : st) (c k : nat) (xs : list cell) (B : nat -> bool) (m' : mst) (a : val) (K : view)
          (u : cell -> option nat) (w : bool) (bv : bool).
Hypothesis I : Inv1 p s.
Hypothesis J : Inv2 p s.
Hypothesis L : Inv3 p s.
Hypothesis Ho : oc (cs s c) k = None.
Hypothesis Hk : pcs s c <= k.
Hypothesis Hh : oh (cs s c) k = None.
Local Abbreviation i := (ILd Plain xs (fun _ => true)).
Hypothesis He : eff (tm s) i (rg (cs s c)) (mof s c) m' a K u w.
Local Abbreviation t' := (sread s c k Plain xs B m' a K u w bv).
Local Abbreviation new := (newevh s c k i K u w).
Local Abbreviation m := (mof s c).
Local Abbreviation rd_cases' := (rd_cases p s c k xs B m' a K u w bv I J Ho Hk Hh He).
Local Abbreviation rd_old0' := (rd_old0 p s c k xs B m' a K u w bv I J Ho Hk Hh He).
Local Abbreviation rd_mem' := (rd_mem p s c k xs B m' a K u w bv I J Ho Hk Hh He).
Local Abbreviation rd_w' := (rd_w p s c k xs B m' a K u w bv I J Ho Hk Hh He).
Local Abbreviation rd_u' := (rd_u p s c k xs B m' a K u w bv I J Ho Hk Hh He).
Local Abbreviation rd_k' := (rd_k p s c k xs B m' a K u w bv I J Ho Hk Hh He).

Lemma r3_new : vP (cs t' c) = mP m' /\ vA (cs t' c) = mA m' /\ vR (cs t' c) = mR m'.
Proof. unfold sread; simpl. unfold upd. rewrite Nat.eqb_refl. auto. Qed.

Lemma r3_old : forall c', c' <> c -> cs t' c' = cs s c'.
Proof. intros c' N. unfold sread; simpl. apply upd_neq. auto. Qed.

Lemma r3_ent_lt : forall t0 e, ent s t0 = Some e -> t0 < tm s.
Proof. intros t0 e H. rewrite (i_tm p s I). unfold ent in H. apply nth_error_Some. congruence. Qed.

Lemma r3_ent_new : ent t' (tm s) = Some new.
Proof. unfold ent, sread; simpl. rewrite (i_tm p s I), nth_error_app2, Nat.sub_diag by lia. reflexivity. Qed.

Lemma r3_ent_old : forall t0 e, ent s t0 = Some e -> ent t' t0 = Some e.
Proof. intros t0 e H. unfold ent, sread; simpl. rewrite nth_error_app1; [exact H|]. rewrite <- (i_tm p s I). apply (r3_ent_lt t0 e H). Qed.

Lemma r3_xg_old : forall t0 e, ent s t0 = Some e -> xg p t' e <-> xg p s e.
Proof.
  intros t0 e H. destruct (rd_old0' t0 e H) as [A _]. unfold xg, xgop.
  split; intros (i0 & E & X); exists i0; split; auto; congruence.
Qed.

Lemma r3_xl_old : forall t0 e, ent s t0 = Some e -> xl p t' e <-> xl p s e.
Proof.
  intros t0 e H. destruct (rd_old0' t0 e H) as (A & B0 & _). unfold xl, xload.
  rewrite A. pose proof (ieval_cond _ _ _ B0) as Q.
  split; intros (i0 & E & X); exists i0; subst i0; split; auto; [rewrite <- Q|rewrite Q]; auto.
Qed.

Lemma r3_xrel_old : forall t0 e, ent s t0 = Some e -> xss p t' e <-> xss p s e.
Proof. intros t0 e H. destruct (rd_old0' t0 e H) as [A _]. unfold xss. rewrite A. tauto. Qed.

Lemma r3_xacq_old : forall t0 e, ent s t0 = Some e -> xll p t' e <-> xll p s e.
Proof. intros t0 e H. destruct (rd_old0' t0 e H) as [A _]. unfold xll. rewrite A. tauto. Qed.

Lemma r3_ins_new : einstr p t' new = crd Plain xs.
Proof. unfold einstr. cbn [ec ek]. exact (proj1 rd_k'). Qed.

Lemma r3_xg_new : ~ xg p t' new.
Proof. unfold xg, xgop. rewrite r3_ins_new. intros (i0 & <- & X). discriminate. Qed.
Lemma r3_xrel_new : ~ xss p t' new.
Proof. unfold xss. rewrite r3_ins_new. discriminate. Qed.
Lemma r3_xacq_new : ~ xll p t' new.
Proof. unfold xll. rewrite r3_ins_new. discriminate. Qed.

Lemma r3_carr : forall u0, carr t' u0 = carr s u0.
Proof. intros u0. destruct rd_mem' as (_ & _ & Mc). unfold carr. rewrite Mc. reflexivity. Qed.

Lemma r3_own : forall c' v, ownw t' c' v -> ownw s c' v.
Proof.
  intros c' v (e & E & C & W). exists e. split; auto. unfold sread in E; simpl in E.
  destruct (Nat.ltb_spec v (length (lg s))) as [Lv|Lv].
  - rewrite nth_error_app1 in E; auto.
  - rewrite nth_error_app2 in E by lia. destruct (v - length (lg s)) as [|n]; simpl in E.
    + injection E as <-. cbn [ew] in W. rewrite rd_w' in W. discriminate.
    + destruct n; discriminate.
Qed.

Lemma r3_pv_old : forall t0 e, ent s t0 = Some e -> forall v, eP e v \/ esrc e v -> v < tm s.
Proof.
  intros t0 e H v [Hv|Hv].
  - destruct (j_eP p s J t0 e v H Hv) as [_ L0]. pose proof (r3_ent_lt t0 e H). lia.
  - unfold esrc, srcv, vor, srcs, vone, vnil in Hv. destruct Hv as [(x & Hx)|Hv].
    + destruct (j_rf p s J t0 e x v H Hx) as (L0 & _). pose proof (r3_ent_lt t0 e H). lia.
    + destruct (ew e); [|destruct Hv]. rewrite Hv. destruct (i_et p s I t0 e H) as [Et _]. rewrite Et. apply (r3_ent_lt t0 e H).
Qed.

Lemma Inv3_read : Inv3 p t'.
Proof.
  pose proof (eff_K_P _ _ _ _ _ _ _ _ _ He) as KP.
  pose proof (eff_K_P' _ _ _ _ _ _ _ _ _ He) as KP'.
  pose proof (eff_src _ _ _ _ _ _ _ _ _ He) as SP'.
  pose proof (eff_R _ _ _ _ _ _ _ _ _ He (k_RP p s L c)) as RP'.
  pose proof (eff_A _ _ _ _ _ _ _ _ _ He) as AA.
  pose proof (eff_G _ _ _ _ _ _ _ _ _ He) as GG.
  pose proof (eff_R_mono _ _ _ _ _ _ _ _ _ He (k_RP p s L c)) as RR.
  assert (PP : vsub (vP (cs s c)) (mP m')) by (eapply vsub_trans; eauto).
  destruct r3_new as (NP & NA & NR0).
  assert (VG : vG t' = mG m') by reflexivity.
  destruct rd_mem' as (Mh & Mv & Mc).
  assert (WC : forall y, wc t' y = wc s y) by (intros; rewrite Mc; reflexivity).
  constructor.
  - (* k_RP *)
    intros c'. destruct (Nat.eq_dec c' c) as [->|N].
    + rewrite NP, NA, NR0. exact RP'.
    + rewrite r3_old by auto. apply (k_RP p s L).
  - (* k_Pcur *)
    intros t e H. apply rd_cases' in H. destruct H as [(H & Ht)|(-> & ->)].
    + destruct (k_Pcur p s L t e H) as [A B0]. destruct (Nat.eq_dec (ec e) c) as [E|N].
      * rewrite E in *. rewrite NP. split; eauto 6 using vsub_trans.
      * rewrite r3_old by auto. auto.
    + cbn [ec eP]. rewrite NP. split; auto.
  - (* k_Ppair *)
    intros t e t2 e2 H H2 E T. apply rd_cases' in H, H2.
    destruct H as [(H & Ht)|(-> & ->)]; destruct H2 as [(H2 & Ht2)|(-> & ->)]; try lia.
    + apply (k_Ppair p s L t e t2 e2 H H2 E T).
    + cbn [ec eP] in *. destruct (k_Pcur p s L t e H) as [A B0]. rewrite E in A, B0.
      split; eauto 6 using vsub_trans.
  - (* k_Gcur *)
    intros t e H X. apply rd_cases' in H. destruct H as [(H & Ht)|(-> & ->)].
    + rewrite r3_xg_old in X by eauto. destruct (k_Gcur p s L t e H X) as [A B0].
      rewrite VG. split; eauto 6 using vsub_trans.
    + exfalso. exact (r3_xg_new X).
  - (* k_Gpair *)
    intros t e t2 e2 H H2 X X2 T. apply rd_cases' in H, H2.
    destruct H as [(H & Ht)|(-> & ->)]; destruct H2 as [(H2 & Ht2)|(-> & ->)]; try lia.
    + rewrite r3_xg_old in X, X2 by eauto. apply (k_Gpair p s L t e t2 e2 H H2 X X2 T).
    + exfalso. exact (r3_xg_new X2).
  - (* k_Rcur *)
    intros t e t2 f H H2 E T X NR v Hv Ov. apply rd_cases' in H, H2.
    destruct H as [(H & Ht)|(-> & ->)]; destruct H2 as [(H2 & Ht2)|(-> & ->)]; try lia.
    + assert (X' : xss p s f \/ xg p s f) by (destruct X; [left; rewrite <- r3_xrel_old by eauto|right; rewrite <- r3_xg_old by eauto]; auto).
      assert (NR' : forall tg g, ent s tg = Some g -> ec g = ec f -> t2 < tg -> ~ xss p s g).
      { intros tg g Hg Eg Lg Rg. apply (NR tg g); auto.
        - apply r3_ent_old. exact Hg.
        - rewrite r3_xrel_old by eauto. exact Rg. }
      assert (Ov' : xg p s f \/ ownw s (ec f) v).
      { destruct Ov as [Ov|Ov]; [left; rewrite <- r3_xg_old by eauto; exact Ov|right; apply (r3_own _ v Ov)]. }
      pose proof (k_Rcur p s L t e t2 f H H2 E T X' NR' v Hv Ov') as Rv.
      destruct (Nat.eq_dec (ec f) c) as [Ef|N].
      * rewrite Ef in *. rewrite NR0. apply RR. exact Rv.
      * rewrite r3_old by auto. exact Rv.
    + exfalso. destruct X as [X|X]; [exact (r3_xrel_new X)|exact (r3_xg_new X)].
    + exfalso. destruct X as [X|X]; [exact (r3_xrel_new X)|exact (r3_xg_new X)].
  - (* k_Rpair *)
    intros te e tf f tw w2 H Hf Hw E1 E2 T1 T2 T3 X W NR v Hv Ov. apply rd_cases' in H, Hf, Hw.
    destruct H as [(H & Ht)|(-> & ->)]; [|lia].
    assert (Lv : v < tm s) by (apply (r3_pv_old te e H v Hv)).
    destruct Hw as [(Hw & Htw)|(-> & ->)]; [|cbn [ew] in W; rewrite rd_w' in W; discriminate].
    destruct Hf as [(Hf & Htf)|(-> & ->)]; [|lia].
    assert (X' : xss p s f \/ xg p s f) by (destruct X; [left; rewrite <- r3_xrel_old by eauto|right; rewrite <- r3_xg_old by eauto]; auto).
    assert (NR' : forall tg g, ent s tg = Some g -> ec g = ec f -> tf < tg -> tg < tw -> ~ xss p s g).
    { intros tg g Hg Eg Lg Lg2 Rg. apply (NR tg g); auto.
      - apply r3_ent_old. exact Hg.
      - rewrite r3_xrel_old by eauto. exact Rg. }
    assert (Ov' : xg p s f \/ ownw s (ec f) v).
    { destruct Ov as [Ov|Ov]; [left; rewrite <- r3_xg_old by eauto; exact Ov|right; apply (r3_own _ v Ov)]. }
    rewrite WC. apply (k_Rpair p s L te e tf f tw w2 H Hf Hw E1 E2 T1 T2 T3 X' W NR' v Hv Ov').
  - (* k_Acur *)
    intros t l H X. rewrite r3_carr. apply rd_cases' in H. destruct H as [(H & Ht)|(-> & ->)].
    + rewrite r3_xl_old in X by eauto. pose proof (k_Acur p s L t l H X) as A.
      destruct (Nat.eq_dec (ec l) c) as [E|N].
      * rewrite E in *. rewrite NA. eauto 6 using vsub_trans.
      * rewrite r3_old by auto. auto.
    + cbn [ec erf]. rewrite NA. exact (eff_carr_A _ _ _ _ _ _ _ _ _ He eq_refl).
  - (* k_Acq *)
    intros tl l tf f H Hf E T X Y. rewrite r3_carr. apply rd_cases' in H, Hf.
    destruct H as [(H & Ht)|(-> & ->)]; [|lia].
    rewrite r3_xl_old in X by eauto.
    destruct Hf as [(Hf & Htf)|(-> & ->)].
    + assert (Y' : xll p s f \/ xg p s f) by (destruct Y; [left; rewrite <- r3_xacq_old by eauto|right; rewrite <- r3_xg_old by eauto]; auto).
      pose proof (k_Acq p s L tl l tf f H Hf E T X Y') as A.
      destruct (Nat.eq_dec (ec f) c) as [Ef|N].
      * rewrite Ef in *. rewrite NP. eauto 6 using vsub_trans.
      * rewrite r3_old by auto. auto.
    + exfalso. destruct Y as [Y|Y]; [exact (r3_xacq_new Y)|exact (r3_xg_new Y)].
  - (* k_Aselfc *)
    intros t l H X G. rewrite r3_carr. apply rd_cases' in H. destruct H as [(H & Ht)|(-> & ->)].
    + rewrite r3_xl_old in X by eauto. rewrite r3_xg_old in G by eauto.
      pose proof (k_Aselfc p s L t l H X G) as A.
      destruct (Nat.eq_dec (ec l) c) as [E|N].
      * rewrite E in *. rewrite NP. eauto 6 using vsub_trans.
      * rewrite r3_old by auto. auto.
    + exfalso. exact (r3_xg_new G).
  - (* k_Aself *)
    intros tl l te e Hl He' E T X G. rewrite r3_carr. apply rd_cases' in Hl, He'.
    destruct Hl as [(Hl & Htl)|(-> & ->)]; [|destruct He' as [(_ & Z)|(Z & _)]; lia].
    rewrite r3_xl_old in X by eauto. rewrite r3_xg_old in G by eauto.
    destruct He' as [(He' & Hte)|(-> & ->)].
    + apply (k_Aself p s L tl l te e Hl He' E T X G).
    + cbn [ec eP] in *. pose proof (k_Aselfc p s L tl l Hl X G) as A. rewrite E in A.
      eauto using vsub_trans.
  - (* k_Apair *)
    intros tl l tf f te e H Hf He' E1 E2 T X Y. rewrite r3_carr. apply rd_cases' in H, Hf, He'.
    destruct H as [(H & Ht)|(-> & ->)]; [|lia].
    rewrite r3_xl_old in X by eauto.
    destruct Hf as [(Hf & Htf)|(-> & ->)]; destruct He' as [(He' & Hte)|(-> & ->)];
      try (destruct Y as [(_ & Y)|(_ & Y)]; lia).
    + assert (Y' : (xll p s f /\ tf < te) \/ (xg p s f /\ tf <= te))
        by (destruct Y as [(Y1 & Y2)|(Y1 & Y2)]; [left; rewrite <- r3_xacq_old by eauto|right; rewrite <- r3_xg_old by eauto]; auto).
      apply (k_Apair p s L tl l tf f te e H Hf He' E1 E2 T X Y').
    + cbn [ec eP] in *.
      assert (Y' : xll p s f \/ xg p s f)
        by (destruct Y as [(Y & _)|(Y & _)]; [left; rewrite <- r3_xacq_old by eauto|right; rewrite <- r3_xg_old by eauto]; auto).
      pose proof (k_Acq p s L tl l tf f H Hf E1 T X Y') as A. rewrite E2 in A.
      eauto 6 using vsub_trans.
    + exfalso. destruct Y as [(Y & _)|(Y & _)]; [exact (r3_xacq_new Y)|exact (r3_xg_new Y)].
Qed.

End Read3.

Record InvAll (p : prog) (s : st) : Prop := { ia1 : Inv1 p s; ia2 : Inv2 p s; ia3 : Inv3 p s }.

Section Match3.
Variables (p : prog) (s : st) (c : nat) (d : desc).
Hypothesis I : Inv1 p s.
Hypothesis J : Inv2 p s.
Hypothesis L : Inv3 p s.
Local Abbreviation cc := (cs s c).
Local Abbreviation k := (pcs s c).
Hypothesis Ho : oc cc k <> None.
Hypothesis Ha : ai cc k = inst_of d.
Hypothesis Hdf : eof (ins p c k (rg cc)) (rg cc) = Some d.
Local Abbreviation s' := (smatch p s c).

Lemma prof_of : forall e, einstr p s' e = einstr p s e \/
  exists d', dof (einstr p s' e) (rgof s e) = Some d' /\ dof (einstr p s e) (rgof s e) = Some d'.
Proof.
  intros e. destruct (einstr_match p s c d I J Ho Ha Hdf e) as [E|(D1 & D2)]; auto. right. eauto.
Qed.

Lemma xg_m : forall e, xg p s' e <-> xg p s e.
Proof.
  intros e. unfold xg. rewrite (rgof_match p s c d I J Ho Ha Hdf e). destruct (prof_of e) as [E|(d' & D1 & D2)].
  - rewrite E. tauto.
  - destruct (same_prof _ _ _ _ D1 D2) as (_ & _ & _ & _ & _ & _ & _ & P8 & _).
    split; intros (i0 & A & B); subst i0; eexists; split; eauto; congruence.
Qed.

Lemma xl_m : forall e, xl p s' e <-> xl p s e.
Proof.
  intros e. unfold xl. rewrite (rgof_match p s c d I J Ho Ha Hdf e). destruct (prof_of e) as [E|(d' & D1 & D2)].
  - rewrite E. tauto.
  - destruct (same_prof _ _ _ _ D1 D2) as (_ & P2 & _).
    split; intros (i0 & A & B); subst i0; eexists; split; eauto; congruence.
Qed.

Lemma xacq_m : forall e, xll p s' e <-> xll p s e.
Proof.
  intros e. unfold xll. destruct (prof_of e) as [E|(d' & D1 & D2)].
  - rewrite E. tauto.
  - destruct (same_prof _ _ _ _ D1 D2) as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & P10 & _). tauto.
Qed.

Lemma xrel_m : forall e, xss p s' e <-> xss p s e.
Proof.
  intros e. unfold xss. destruct (prof_of e) as [E|(d' & D1 & D2)].
  - rewrite E. tauto.
  - destruct (same_prof _ _ _ _ D1 D2) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P11 & P12). tauto.
Qed.

Lemma views_m : forall c', vP (cs s' c') = vP (cs s c') /\ vA (cs s' c') = vA (cs s c') /\ vR (cs s' c') = vR (cs s c').
Proof.
  intros c'. unfold smatch; cbn [cs]. unfold upd. destruct (Nat.eqb c' c) eqn:E; [apply Nat.eqb_eq in E; subst|]; simpl; auto.
Qed.

Lemma Inv3_match : Inv3 p s'.
Proof.
  assert (VP : forall c', vP (cs s' c') = vP (cs s c')) by (intros; apply views_m).
  assert (VA : forall c', vA (cs s' c') = vA (cs s c')) by (intros; apply views_m).
  assert (VR : forall c', vR (cs s' c') = vR (cs s c')) by (intros; apply views_m).
  assert (EN : forall t, ent s' t = ent s t) by reflexivity.
  destruct L.
  constructor; intros; rewrite ?VP, ?VA, ?VR, ?EN in *;
  repeat match goal with
         | H : context [xg p s' ?e] |- _ => setoid_rewrite (xg_m e) in H
         | H : context [xl p s' ?e] |- _ => setoid_rewrite (xl_m e) in H
         | H : context [xll p s' ?e] |- _ => setoid_rewrite (xacq_m e) in H
         | H : context [xss p s' ?e] |- _ => setoid_rewrite (xrel_m e) in H
         | H : context [xss p s' _] |- _ => setoid_rewrite xrel_m in H
         | H : context [xg p s' _] |- _ => setoid_rewrite xg_m in H
         end;
  try setoid_rewrite xg_m;
  unfold esrc, carr, ownw in *; simpl in *; eauto.
Qed.

End Match3.

Lemma xload_nfn : forall i r f, xload i r = true -> i <> IFn f.
Proof. intros i r f H. destruct i; simpl in H; discriminate || congruence. Qed.

Section Skip3.
Variables (p : prog) (s : st) (c : nat).
Hypothesis I : Inv1 p s.
Hypothesis J : Inv2 p s.
Hypothesis L : Inv3 p s.
Hypothesis Ho : oc (cs s c) (pcs s c) = None.
Hypothesis Hh : oh (cs s c) (pcs s c) <> None ->
  eofR (ins p c (pcs s c) (rg (cs s c))) (rg (cs s c)) = eofR (ai (cs s c) (pcs s c)) (rg (cs s c)).
Local Abbreviation s' := (sskip p s c).


(* an entry is of the same kind: the same instruction, or (the read of a CAS
   that failed and was passed) a CAS read in place of the CAS *)
Lemma xg_sk : forall t e, ent s t = Some e -> xg p s' e <-> xg p s e.
Proof.
  intros t e H. unfold xg. rewrite (rgof_skip p s c I J Ho Hh). destruct (einstr_skip p s c I J Ho Hh t e H) as [E|(Eh & xs & A & Ic & Xl & Cs)].
  - rewrite E. tauto.
  - rewrite A. split; intros (i & Ei & G); exfalso.
    + subst i. unfold xgop in G. revert Xl G. generalize (einstr p s' e). intros i Xl G.
      destruct i; simpl in Xl, G; discriminate.
    + subst i. discriminate.
Qed.

Lemma xl_sk : forall t e, ent s t = Some e -> xl p s' e <-> xl p s e.
Proof.
  intros t e H. unfold xl. rewrite (rgof_skip p s c I J Ho Hh). destruct (einstr_skip p s c I J Ho Hh t e H) as [E|(Eh & xs & A & Ic & Xl & Cs)].
  - rewrite E. tauto.
  - rewrite A. split; intros _; eexists; (split; [reflexivity|]); [reflexivity|exact Xl].
Qed.

Lemma xll_sk : forall t e, ent s t = Some e -> xll p s' e <-> xll p s e.
Proof.
  intros t e H. unfold xll. destruct (einstr_skip p s c I J Ho Hh t e H) as [E|(Eh & xs & A & Ic & Xl & Cs)].
  - rewrite E. tauto.
  - rewrite A. split; intros G; [exfalso; apply (xload_nfn _ _ _ Xl G)|discriminate].
Qed.

Lemma xss_sk : forall t e, ent s t = Some e -> xss p s' e <-> xss p s e.
Proof.
  intros t e H. unfold xss. destruct (einstr_skip p s c I J Ho Hh t e H) as [E|(Eh & xs & A & Ic & Xl & Cs)].
  - rewrite E. tauto.
  - rewrite A. split; intros G; [exfalso; apply (xload_nfn _ _ _ Xl G)|discriminate].
Qed.

Lemma Inv3_skip : Inv3 p s'.
Proof.
  assert (VS : forall c', vP (cs s' c') = vP (cs s c') /\ vA (cs s' c') = vA (cs s c') /\ vR (cs s' c') = vR (cs s c')).
  { intros c'. unfold sskip; cbn [cs]. unfold upd. destruct (Nat.eqb c' c) eqn:E; [apply Nat.eqb_eq in E; subst|]; simpl; auto. }
  assert (VP : forall c', vP (cs s' c') = vP (cs s c')) by (intros; apply VS).
  assert (VA : forall c', vA (cs s' c') = vA (cs s c')) by (intros; apply VS).
  assert (VR : forall c', vR (cs s' c') = vR (cs s c')) by (intros; apply VS).
  assert (EN : forall t, ent s' t = ent s t) by reflexivity.
  clear VS. destruct L.
  constructor; intros; rewrite ?VP, ?VA, ?VR, ?EN in *;
  repeat match goal with
         | E : ent s ?t = Some ?e, H : context [xg p s' ?e] |- _ => rewrite (xg_sk t e E) in H
         | E : ent s ?t = Some ?e, H : context [xl p s' ?e] |- _ => rewrite (xl_sk t e E) in H
         | E : ent s ?t = Some ?e, H : context [xll p s' ?e] |- _ => rewrite (xll_sk t e E) in H
         | E : ent s ?t = Some ?e, H : context [xss p s' ?e] |- _ => rewrite (xss_sk t e E) in H
         | E : ent s ?t = Some ?e |- context [xg p s' ?e] => rewrite (xg_sk t e E)
         end;
  unfold esrc, carr, ownw in *; simpl in *; eauto.
  (* release views: no ss of the context in between, read on the old state *)
  all: assert (Q : forall tg g, ent s tg = Some g -> xss p s g -> xss p s' g)
         by (intros tg g Hg X; apply (xss_sk tg g Hg); exact X).
  all: match goal with
  | E1 : ent s ?t = Some ?e, E2 : ent s ?t' = Some ?f, Ec : ec ?e = ec ?f, Lt : ?t <= ?t',
    X : xss p s ?f \/ xg p s ?f,
    NR : forall tg g, ent s' tg = Some g -> ec g = ec ?f -> ?t' < tg -> ~ xss p s' g,
    Hv : eP ?e ?v \/ _, Hw : xg p s ?f \/ _ |- vR _ ?v =>
      exact (k_Rcur0 t e t' f E1 E2 Ec Lt X (fun tg g Hg Eg Lg Xg => NR tg g Hg Eg Lg (Q tg g Hg Xg)) v Hv Hw)
  | E1 : ent s ?te = Some ?e, E2 : ent s ?tf = Some ?f, E3 : ent s ?tw = Some ?w,
    Ec1 : ec ?e = ec ?f, Ec2 : ec ?f = ec ?w, L1 : ?te <= ?tf, L2 : ?tf <= ?tw, L3 : ?te < ?tw,
    X : xss p s ?f \/ xg p s ?f, W : ew ?w = true,
    NR : forall tg g, ent s' tg = Some g -> ec g = ec ?f -> ?tf < tg -> tg < ?tw -> ~ xss p s' g,
    Hv : eP ?e ?v \/ _, Hw : xg p s ?f \/ _ |- wc s ?tw ?v =>
      exact (k_Rpair0 te e tf f tw w E1 E2 E3 Ec1 Ec2 L1 L2 L3 X W
               (fun tg g Hg Eg Lg Lg2 Xg => NR tg g Hg Eg Lg Lg2 (Q tg g Hg Xg)) v Hv Hw)
  end.
Qed.

End Skip3.

(* ---------- a CAS whose read happened alone commits to failure ---------- *)
Section Cfail3.
Variables (p : prog) (s : st) (c k : nat).
Hypothesis I : Inv1 p s.
Hypothesis L : Inv3 p s.
Hypothesis Hp : pcs s c <= k.
Hypothesis Ho : oc (cs s c) k = None.
Local Abbreviation s' := (scfail s c k).

Lemma einstr_cf : forall e, einstr p s' e = einstr p s e.
Proof. intros e. unfold einstr. rewrite ai_cf. reflexivity. Qed.

Lemma ieval_ent_cf : forall t e, ent s t = Some e -> ieval (einstr p s e) (rgof s' e) = ieval (einstr p s e) (rgof s e).
Proof. intros t e E. unfold einstr, rgof. eapply ieval_cf; eauto. Qed.

Lemma xg_cf : forall t e, ent s t = Some e -> xg p s' e <-> xg p s e.
Proof.
  intros t e E. unfold xg. rewrite einstr_cf. pose proof (ieval_ent_cf t e E) as Q.
  split; intros (i & Ei & G); exists i; split; auto; subst i; unfold xgop in *; unfold icond in *; rewrite ?Q in *; auto;
    destruct (einstr p s e) as [| | |[]|]; simpl in *; auto.
Qed.

Lemma xl_cf : forall t e, ent s t = Some e -> xl p s' e <-> xl p s e.
Proof.
  intros t e E. unfold xl. rewrite einstr_cf. pose proof (ieval_ent_cf t e E) as Q.
  split; intros (i & Ei & G); exists i; split; auto; subst i; unfold xload, icond in *; rewrite ?Q in *; auto.
Qed.

Lemma Inv3_cfail : Inv3 p s'.
Proof.
  assert (EI := einstr_cf). assert (XG := xg_cf). assert (XL := xl_cf).
  assert (XLL : forall e, xll p s' e <-> xll p s e) by (intros e; unfold xll; rewrite EI; tauto).
  assert (XSS : forall e, xss p s' e <-> xss p s e) by (intros e; unfold xss; rewrite EI; tauto).
  assert (CP : forall c', vP (cs s' c') = vP (cs s c') /\ vA (cs s' c') = vA (cs s c') /\ vR (cs s' c') = vR (cs s c')).
  { intros c'. rewrite cs_cf. destruct (Nat.eqb_spec c' c); [subst|]; repeat split. }
  destruct L. constructor; cbn [vG wc hs wv scfail].
  - intros c'. rewrite (proj1 (CP c')), (proj1 (proj2 (CP c'))), (proj2 (proj2 (CP c'))). apply k_RP0.
  - intros t e E. rewrite (proj1 (CP _)). exact (k_Pcur0 t e E).
  - exact k_Ppair0.
  - intros t e E X. apply (XG t e E) in X. exact (k_Gcur0 t e E X).
  - intros t e t' e' E E' X X'. apply (XG t e E) in X. apply (XG t' e' E') in X'. exact (k_Gpair0 t e t' e' E E' X X').
  - intros t e t' f E F Ec Lt Xf NS v Hv Hw. rewrite (proj2 (proj2 (CP _))).
    rewrite XSS, (XG t' f F) in Xf. rewrite (XG t' f F) in Hw.
    apply (k_Rcur0 t e t' f E F Ec Lt Xf); auto. intros tg g G Eg Lg. rewrite <- XSS. apply (NS tg g G Eg Lg).
  - intros te e tf f tw w' E F Wn Ec1 Ec2 L1 L2 L3 Xf Ew NS v Hv Hw.
    rewrite XSS, (XG tf f F) in Xf. rewrite (XG tf f F) in Hw.
    apply (k_Rpair0 te e tf f tw w' E F Wn Ec1 Ec2 L1 L2 L3 Xf Ew); auto. intros tg g G Eg Lg Lg2. rewrite <- XSS. apply (NS tg g G Eg Lg Lg2).
  - intros t l E X. apply (XL t l E) in X. rewrite (proj1 (proj2 (CP _))). exact (k_Acur0 t l E X).
  - intros tl l tf f E F Ec Lt X Y. apply (XL tl l E) in X. rewrite XLL, (XG tf f F) in Y. rewrite (proj1 (CP _)). exact (k_Acq0 tl l tf f E F Ec Lt X Y).
  - intros t l E X Y. apply (XL t l E) in X. apply (XG t l E) in Y. rewrite (proj1 (CP _)). exact (k_Aselfc0 t l E X Y).
  - intros tl l te e E E' Ec Lt X Y. apply (XL tl l E) in X. apply (XG tl l E) in Y. exact (k_Aself0 tl l te e E E' Ec Lt X Y).
  - intros tl l tf f te e E F E' Ec1 Ec2 Lt X Y. apply (XL tl l E) in X. rewrite XLL, (XG tf f F) in Y. exact (k_Apair0 tl l tf f te e E F E' Ec1 Ec2 Lt X Y).
Qed.

End Cfail3.

(* S3c: a result fixed changes only bd and fx *)
Lemma rgof_cx : forall s c j b B e, rgof (scfix0 s c j b B) e = rgof s e.
Proof. intros. unfold rgof. rewrite rg_cx. reflexivity. Qed.
Section Cfix3.
Variables (p : prog) (s : st) (c j : nat) (b : bool) (B : nat -> bool).
Local Abbreviation s' := (scfix0 s c j b B).

Lemma einstr_cx : forall e, einstr p s' e = einstr p s e.
Proof. intros e. unfold einstr. rewrite ai_cx. reflexivity. Qed.

Lemma Inv3_cfix : Inv3 p s -> Inv3 p s'.
Proof.
  intros L.
  assert (XG : forall e, xg p s' e <-> xg p s e) by (intros e; unfold xg; rewrite einstr_cx, rgof_cx; tauto).
  assert (XL : forall e, xl p s' e <-> xl p s e) by (intros e; unfold xl; rewrite einstr_cx, rgof_cx; tauto).
  assert (XLL : forall e, xll p s' e <-> xll p s e) by (intros e; unfold xll; rewrite einstr_cx; tauto).
  assert (XSS : forall e, xss p s' e <-> xss p s e) by (intros e; unfold xss; rewrite einstr_cx; tauto).
  assert (CP : forall c', vP (cs s' c') = vP (cs s c') /\ vA (cs s' c') = vA (cs s c') /\ vR (cs s' c') = vR (cs s c'))
    by (intros c'; rewrite vP_cx, vA_cx, vR_cx; repeat split).
  destruct L. constructor; cbn [vG wc hs wv scfix0].
  - intros c'. rewrite (proj1 (CP c')), (proj1 (proj2 (CP c'))), (proj2 (proj2 (CP c'))). apply k_RP0.
  - intros t e E. rewrite (proj1 (CP _)). exact (k_Pcur0 t e E).
  - exact k_Ppair0.
  - intros t e E X. apply XG in X. exact (k_Gcur0 t e E X).
  - intros t e t' e' E E' X X'. apply XG in X. apply XG in X'. exact (k_Gpair0 t e t' e' E E' X X').
  - intros t e t' f E F Ec Lt Xf NS v Hv Hw. rewrite (proj2 (proj2 (CP _))).
    rewrite XSS, XG in Xf. rewrite XG in Hw.
    apply (k_Rcur0 t e t' f E F Ec Lt Xf); auto. intros tg g G Eg Lg. rewrite <- XSS. apply (NS tg g G Eg Lg).
  - intros te e tf f tw w' E F Wn Ec1 Ec2 L1 L2 L3 Xf Ew NS v Hv Hw.
    rewrite XSS, XG in Xf. rewrite XG in Hw.
    apply (k_Rpair0 te e tf f tw w' E F Wn Ec1 Ec2 L1 L2 L3 Xf Ew); auto. intros tg g G Eg Lg Lg2. rewrite <- XSS. apply (NS tg g G Eg Lg Lg2).
  - intros t l E X. apply XL in X. rewrite (proj1 (proj2 (CP _))). exact (k_Acur0 t l E X).
  - intros tl l tf f E F Ec Lt X Y. apply XL in X. rewrite XLL, XG in Y. rewrite (proj1 (CP _)). exact (k_Acq0 tl l tf f E F Ec Lt X Y).
  - intros t l E X Y. apply XL in X. apply XG in Y. rewrite (proj1 (CP _)). exact (k_Aselfc0 t l E X Y).
  - intros tl l te e E E' Ec Lt X Y. apply XL in X. apply XG in Y. exact (k_Aself0 tl l te e E E' Ec Lt X Y).
  - intros tl l tf f te e E F E' Ec1 Ec2 Lt X Y. apply XL in X. rewrite XLL, XG in Y. exact (k_Apair0 tl l tf f te e E F E' Ec1 Ec2 Lt X Y).
Qed.
End Cfix3.

Lemma Inv3_es : forall p t e, Inv3 p t -> Inv3 p (set_es t e).
Proof. intros p t e J. destruct J; constructor; auto. Qed.

Lemma Inv_run : forall p s, run p s -> InvAll p s.
Proof.
  intros p s R. induction R as [|s t R IH H].
  - constructor; [apply Inv1_init|apply Inv2_init|apply Inv3_init].
  - destruct IH as [I J L].
    assert (R' : run p t) by (econstructor; eauto).
    constructor; [apply (Inv1_run p t R')|apply (proj2 (Inv2_run p t R'))|].
    destruct (step_cases p s t H) as [(c & i & m' & a & K & u & w & H1 & H2 & H3 & H4 & Hbh & Hh & _ & _ & H6 & _ & ->)|[(c & k & d & B & m' & a & K & u & w & H1 & H2 & Hso & Hh & _ & _ & H5 & _ & ->)|[(c & d & H1 & H2 & H3 & H4 & H4m & Hfh & ->)|[(c & k & xs & B & m' & a & K & u & w & bv & H1 & H2 & Hh & Hso & H4 & H5 & _ & ->)|[(c & S1 & S2 & S3 & _ & S5 & S4 & _ & ->)|(cX & jX & bX & BX & oX & HjX & HfX & HcX & ->)]]]]].
    + eapply Inv3_step; eauto; [intros r Sr; apply (proj2 (H3 r Sr))|].
      destruct Hh as [(Z & _)|(t1 & Z & Ci & U & Ef)]; [left; exact Z|right; split; [exact U|exact Ef]].
    + apply Inv3_es. eapply Inv3_step; eauto; [lia|intros r Sr; apply ieval_inst|].
      destruct Hh as [(Z & _)|(t1 & xs & ev & nv & Z & -> & U & Ac & _)]; [left; exact Z|right].
      split; [exact U|]. rewrite Ac. reflexivity.
    + eapply Inv3_match; eauto.
    + apply Inv3_read; auto.
    + apply Inv3_skip; auto.
    + destruct oX as [kX|]; [destruct bX|]; cbn [sflp]; apply Inv3_cfix; [auto| |auto].
      destruct (cfix_rec _ _ _ _ _ _ _ _ _ HcX) as (HpX & HoX & HhX & _). apply Inv3_cfail; auto.
Qed.
