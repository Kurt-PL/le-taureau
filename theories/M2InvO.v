(* Model2: invariants of what contexts and accesses know in order. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3.

(* an access that has an in-order view: a write, or a read that happened *)
Definition xacc (p : prog) (s : st) (e : oev) : Prop := ew e = true \/ xl p s e.

(* a cell G held when the event at te was made, written before it: every
   guard() after the event knows it (G is knowledge without perception, so
   it stands beside what the event perceived) *)
Definition gk (p : prog) (s : st) (te : nat) : view := fun y =>
  y < te /\ vG s y /\ forall tf f, ent s tf = Some f -> te < tf -> xg p s f -> eP f y.

Record InvO (p : prog) (s : st) : Prop := {
  o_sub_PG : forall c, vsub (vO (cs s c)) (vor (vP (cs s c)) (vG s));
  o_gsub : forall c, vsub (vOg (cs s c)) (vO (cs s c));
  o_gcur : forall t f, ent s t = Some f -> xg p s f -> vsub (eP f) (vOg (cs s (ec f)));
  o_gpair : forall tf f te e, ent s tf = Some f -> ent s te = Some e -> ec f = ec e -> tf < te ->
    xg p s f -> xacc p s e -> vsub (eP f) (eQ e);
  o_rfe : forall t e x y ey, ent s t = Some e -> erf e x = Some y -> ent s y = Some ey -> ec ey <> ec e ->
    eQ e y;
  o_acur : forall tl l tf f, ent s tl = Some l -> ent s tf = Some f -> ec l = ec f -> tl < tf ->
    xl p s l -> xll p s f -> forall w, carr s (erf l) w -> ~ ownw s (ec l) w -> vO (cs s (ec f)) w;
  o_apair : forall tl l tf f te e, ent s tl = Some l -> ent s tf = Some f -> ent s te = Some e ->
    ec l = ec f -> ec f = ec e -> tl < tf -> tf < te -> xl p s l -> xll p s f -> xl p s e ->
    forall w, carr s (erf l) w -> ~ ownw s (ec l) w -> eQc e w;
  o_QP_G : forall t e, ent s t = Some e -> vsub (eQ e) (vor (vor (eP e) (esrc e)) (gk p s t));
  o_eRC : forall t e, ent s t = Some e ->
    eR e = evR (einstr p s e) (rgof s e) /\ eC e = evC (einstr p s e) (rgof s e)
}.

Lemma InvO_init : forall p, InvO p sinit.
Proof.
  intros p. constructor; unfold ent; simpl; intros.
  all: try (match goal with H : nth_error [] ?t = Some _ |- _ => destruct t; discriminate end).
  all: unfold vsub; auto.
  all: intros; unfold vnil in *; contradiction.
Qed.

Lemma ownw_grow : forall s t c w, (forall a e, nth_error (lg s) a = Some e -> nth_error (lg t) a = Some e) ->
  ownw s c w -> ownw t c w.
Proof. intros s t c w G (e & E & C & W). exists e. auto. Qed.

Set Default Proof Using "All".
Section Step.
Variables (p : prog) (s : st) (c k : nat) (i : instr) (m' : mst) (a : val) (K : view)
          (u : cell -> option nat) (w : bool) (Bd : nat -> bool) (pc' tp' : nat -> nat)
          (cm' : list (nat * nat * nat)).
Hypothesis I : Inv1 p s.
Hypothesis J : Inv2 p s.
Hypothesis L : Inv3 p s.
Hypothesis Q : InvO p s.
Hypothesis Ho : oc (cs s c) k = None.
Hypothesis Hk : pcs s c <= k.
Hypothesis Hst : forall r, settled (cs s c) (pcs s c) r -> ieval i r = ieval i (rg (cs s c)).
Hypothesis He : eff (tm s) i (rg (cs s c)) (mof s c) m' a K u w.
Hypothesis Hhk : oh (cs s c) k = None \/
  (u = rw (cs s c) k /\ eofR i (rg (cs s c)) = eofR (ai (cs s c) k) (rg (cs s c))).

Local Abbreviation t' := (evs s c k i m' a K u w Bd pc' tp' cm').
Local Abbreviation new := (newev s c k i K u w).
Local Abbreviation m := (mof s c).
Local Abbreviation O := (vO (cs s c)).
Local Abbreviation O' := (newO s c i m m' O).
Local Abbreviation ent_cases' := (ent_cases p s c k i m' a K u w Bd pc' tp' cm' I J Ho Hk Hst He Hhk).
Local Abbreviation ins_new' := (ins_new p s c k i m' a K u w Bd pc' tp' cm' I J Ho Hk Hst He Hhk).
Local Abbreviation ieval_new' := (ieval_new p s c k i m' a K u w Bd pc' tp' cm' I J Ho Hk Hst He Hhk).
Local Abbreviation ieval_old0' := (ieval_old0 p s c k i m' a K u w Bd pc' tp' cm' I J Ho Hk Hst He Hhk).

Lemma o_cs_new : vO (cs t' c) = O'.
Proof using All. unfold evs; simpl. rewrite upd_eq. reflexivity. Qed.

Lemma o_cs_old : forall c', c' <> c -> cs t' c' = cs s c'.
Proof using All. intros c' N. unfold evs; simpl. apply upd_neq. auto. Qed.

Lemma og_cs_new : vOg (cs t' c) = newOg i m' (vOg (cs s c)).
Proof using All. unfold evs; simpl. rewrite upd_eq. reflexivity. Qed.

Lemma vP_new : vP (cs t' c) = mP m'.
Proof using All. unfold evs; simpl. rewrite upd_eq. reflexivity. Qed.

Lemma lg_grow : forall a0 e, nth_error (lg s) a0 = Some e -> nth_error (lg t') a0 = Some e.
Proof using All. intros a0 e E. unfold evs; simpl. rewrite nth_error_app1; auto. apply nth_error_Some. congruence. Qed.

Lemma ownw_old : forall c0 w0, ~ ownw t' c0 w0 -> ~ ownw s c0 w0.
Proof using All. intros c0 w0 N X. apply N. eapply ownw_grow; [exact lg_grow|exact X]. Qed.

Lemma P_mono : vsub (vP (cs s c)) (mP m').
Proof using All.
  intros x Hx. apply (eff_P_mono _ _ _ _ _ _ _ _ _ He). exact Hx.
Qed.

Lemma vG_new : vG t' = mG m'.
Proof using All. reflexivity. Qed.

Lemma G_mono : vsub (vG s) (mG m').
Proof using All. intros x Hx. apply (eff_G _ _ _ _ _ _ _ _ _ He). exact Hx. Qed.

(* guard() takes G into what it perceives *)
Lemma G_full : xgop i (rg (cs s c)) = true -> vsub (vG s) (mP m').
Proof using All.
  intros X x Hx. apply (eff_K_P' _ _ _ _ _ _ _ _ _ He).
  apply (proj1 (proj2 (eff_gop _ _ _ _ _ _ _ _ _ He X))). exact Hx.
Qed.

Lemma newO_mono : vsub O O'.
Proof using All.
  intros x Hx. pose proof P_mono as PM. pose proof G_full as GF. pose proof (o_sub_PG p s Q c x Hx) as S.
  unfold newO. destruct i as [| | |[]|]; try exact Hx; try (left; exact Hx).
  destruct S as [Px|Gx]; [apply PM; exact Px|apply GF; [reflexivity|exact Gx]].
Qed.

Lemma newO_sub : vsub O' (vor (mP m') (mG m')).
Proof using All.
  intros x Hx. pose proof (o_sub_PG p s Q c x) as S. pose proof P_mono as PM. pose proof G_mono as GM.
  pose proof (fun E => eff_ll _ _ _ _ _ _ _ _ _ He E) as EA.
  assert (OS : O x -> vor (mP m') (mG m') x).
  { intros Ox. destruct (S Ox) as [Px|Gx]; [left; apply PM; exact Px|right; apply GM; exact Gx]. }
  unfold newO in Hx. destruct i as [| | |[]|]; try (apply OS; exact Hx).
  - destruct Hx as [Hx|[[Hx|Hx] _]].
    + apply OS. exact Hx.
    + left. apply PM. exact Hx.
    + left. apply (EA eq_refl). exact Hx.
  - destruct Hx as [Hx|Hx]; [apply OS; exact Hx|right; exact Hx].
  - left. exact Hx.
Qed.

Lemma newOg_mono : vsub (vOg (cs s c)) (newOg i m' (vOg (cs s c))).
Proof using All.
  intros x Hx. pose proof P_mono as PM. pose proof G_full as GF.
  pose proof (o_sub_PG p s Q c x (o_gsub p s Q c x Hx)) as S.
  unfold newOg. destruct i as [| | |[]|]; try exact Hx; try (left; exact Hx).
  destruct S as [Px|Gx]; [apply PM; exact Px|apply GF; [reflexivity|exact Gx]].
Qed.

(* what G held stays known to every guard() made later, this one included *)
Lemma gk_old : forall te, vsub (gk p s te) (gk p t' te).
Proof using All.
  intros te y (Ly & Gy & Fy). split; [exact Ly|]. split; [rewrite vG_new; apply G_mono; exact Gy|].
  intros tf f Hf T X. apply ent_cases' in Hf. destruct Hf as [(Hf & Htf)|(-> & ->)].
  - rewrite (xg_old p s c k i m' a K u w Bd pc' tp' cm' I J L Ho Hk Hst He Hhk tf f Hf) in X. exact (Fy tf f Hf T X).
  - apply (xg_new p s c k i m' a K u w Bd pc' tp' cm' I J L Ho Hk Hst He Hhk) in X.
    cbn [eP]. apply (proj1 (proj2 (eff_gop _ _ _ _ _ _ _ _ _ He X))). exact Gy.
Qed.

Lemma gk_new : vsub (vG s) (gk p t' (tm s)).
Proof using All.
  intros y Gy. split; [apply (isw_lt p s y I); apply (j_views p s J c); tauto|].
  split; [rewrite vG_new; apply G_mono; exact Gy|].
  intros tf f Hf T X. apply ent_cases' in Hf. destruct Hf as [(_ & Htf)|(-> & _)]; lia.
Qed.

Lemma newOg_sub : vsub (newOg i m' (vOg (cs s c))) O'.
Proof using All.
  intros x Hx. pose proof newO_mono as NM. pose proof (o_gsub p s Q c) as OG.
  unfold newOg in Hx. unfold newO. destruct i as [| | |[]|]; try (apply NM; apply OG; exact Hx).
  - destruct Hx as [Hx|Hx]; [left; apply OG; exact Hx|right; exact Hx].
  - exact Hx.
Qed.

Lemma xacc_new : xacc p t' new -> w = true \/ xload i (rg (cs s c)) = true.
Proof using All.
  intros [W|X]; [left; exact W|right]. apply (proj1 (xl_new p s c k i m' a K u w Bd pc' tp' cm' I J L Ho Hk Hst He Hhk)). exact X.
Qed.

Lemma eQ_new : xacc p t' new -> vsub (vOg (cs s c)) (eQ new).
Proof using All.
  intros X x Hx. cbn [eQ]. unfold evQ. destruct (xacc_new X) as [W|Xl].
  - rewrite W. simpl. left. exact Hx.
  - unfold xload in Xl. rewrite Xl, orb_true_r. left. exact Hx.
Qed.

Lemma eQc_new : xl p t' new -> vsub O (eQc new).
Proof using All.
  intros X x Hx. cbn [eQc]. unfold evQc.
  apply (proj1 (xl_new p s c k i m' a K u w Bd pc' tp' cm' I J L Ho Hk Hst He Hhk)) in X.
  unfold xload in X. rewrite X. exact Hx.
Qed.

Lemma InvO_step : InvO p t'.
Proof using All.
  constructor.
  - (* o_sub_PG *)
    intros c'. rewrite vG_new. destruct (Nat.eq_dec c' c) as [->|N].
    + rewrite o_cs_new, vP_new. exact newO_sub.
    + rewrite o_cs_old by auto. intros x Hx.
      destruct (o_sub_PG p s Q c' x Hx) as [Px|Gx]; [left; exact Px|right; apply G_mono; exact Gx].
  - (* o_gsub *)
    intros c'. destruct (Nat.eq_dec c' c) as [->|N].
    + rewrite o_cs_new, og_cs_new. exact newOg_sub.
    + rewrite o_cs_old by auto. apply (o_gsub p s Q).
  - (* o_gcur *)
    intros t f H X. apply ent_cases' in H. destruct H as [(H & Ht)|(-> & ->)].
    + rewrite (xg_old p s c k i m' a K u w Bd pc' tp' cm' I J L Ho Hk Hst He Hhk t f H) in X.
      pose proof (o_gcur p s Q t f H X) as G. destruct (Nat.eq_dec (ec f) c) as [E|N].
      * rewrite E in *. rewrite og_cs_new. intros x Hx. apply newOg_mono. apply G. exact Hx.
      * rewrite o_cs_old by auto. exact G.
    + apply (xg_new p s c k i m' a K u w Bd pc' tp' cm' I J L Ho Hk Hst He Hhk) in X.
      cbn [ec eP]. rewrite og_cs_new. unfold xgop in X. pose proof (eff_K_P' _ _ _ _ _ _ _ _ _ He) as KP.
      destruct i as [| | |[]|]; simpl in X; try discriminate.
      unfold newOg. intros x Hx. apply KP. exact Hx.
  - (* o_gpair *)
    intros tf f te e Hf He2 E T X Y. apply ent_cases' in Hf, He2.
    destruct Hf as [(Hf & Htf)|(-> & ->)]; destruct He2 as [(He2 & Hte)|(-> & ->)]; try lia.
    + rewrite (xg_old p s c k i m' a K u w Bd pc' tp' cm' I J L Ho Hk Hst He Hhk tf f Hf) in X.
      assert (Y' : xacc p s e).
      { destruct Y as [Y|Y]; [left; exact Y|right].
        apply (proj1 (xl_old p s c k i m' a K u w Bd pc' tp' cm' I J L Ho Hk Hst He Hhk te e He2)). exact Y. }
      exact (o_gpair p s Q tf f te e Hf He2 E T X Y').
    + cbn [ec] in E. rewrite (xg_old p s c k i m' a K u w Bd pc' tp' cm' I J L Ho Hk Hst He Hhk tf f Hf) in X.
      intros x Hx. apply eQ_new; auto. rewrite <- E. apply (o_gcur p s Q tf f Hf X). exact Hx.
  - (* o_rfe *)
    intros t e x y ey H Ey Hy N. apply ent_cases' in H. destruct H as [(H & Ht)|(-> & ->)].
    + apply ent_cases' in Hy. destruct Hy as [(Hy & _)|(-> & ->)].
      * exact (o_rfe p s Q t e x y ey H Ey Hy N).
      * exfalso. destruct (j_rf p s J t e x (tm s) H Ey) as (Lt & _). lia.
    + cbn [erf ec eQ] in *. unfold evQ.
      assert (Xl : xload i (rg (cs s c)) = true) by (apply (eff_u _ _ _ _ _ _ _ _ _ He x y Ey)).
      unfold xload in Xl. rewrite Xl, orb_true_r. right. split; [eauto|].
      intros (Ow & _). destruct Ow as (e2 & E2 & C2 & _).
      apply ent_cases' in Hy. destruct Hy as [(Hy & _)|(-> & ->)].
      * unfold ent in Hy. rewrite E2 in Hy. injection Hy as <-. congruence.
      * cbn [ec] in N. congruence.
  - (* o_acur *)
    intros tl l tf f Hl Hf E T X Y w0 Cw Nw. apply ent_cases' in Hl, Hf.
    destruct Hl as [(Hl & Htl)|(-> & ->)]; [|lia].
    rewrite (xl_old p s c k i m' a K u w Bd pc' tp' cm' I J L Ho Hk Hst He Hhk tl l Hl) in X.
    apply (carr_l p s c k i m' a K u w Bd pc' tp' cm' I J L Ho Hk Hst He Hhk tl l Hl) in Cw.
    apply ownw_old in Nw.
    destruct Hf as [(Hf & Htf)|(-> & ->)].
    + rewrite (xacq_old p s c k i m' a K u w Bd pc' tp' cm' I J L Ho Hk Hst He Hhk tf f Hf) in Y.
      pose proof (o_acur p s Q tl l tf f Hl Hf E T X Y w0 Cw Nw) as G.
      destruct (Nat.eq_dec (ec f) c) as [Ef|N].
      * rewrite Ef in *. rewrite o_cs_new. apply newO_mono. exact G.
      * rewrite o_cs_old by auto. exact G.
    + cbn [ec] in *. unfold xll in Y. rewrite ins_new' in Y.
      rewrite o_cs_new. unfold newO. rewrite Y. right. split.
      * right. rewrite <- E. apply (k_Acur p s L tl l Hl X). exact Cw.
      * intros (Ow & _). apply Nw. rewrite E. exact Ow.
  - (* o_apair *)
    intros tl l tf f te e Hl Hf He2 E1 E2 T1 T2 X Y Z w0 Cw Nw.
    apply ent_cases' in Hl, Hf, He2.
    destruct Hl as [(Hl & Htl)|(-> & ->)]; [|lia].
    destruct Hf as [(Hf & Htf)|(-> & ->)]; [|destruct He2 as [(_ & Z')|(Z' & _)]; lia].
    rewrite (xl_old p s c k i m' a K u w Bd pc' tp' cm' I J L Ho Hk Hst He Hhk tl l Hl) in X.
    rewrite (xacq_old p s c k i m' a K u w Bd pc' tp' cm' I J L Ho Hk Hst He Hhk tf f Hf) in Y.
    apply (carr_l p s c k i m' a K u w Bd pc' tp' cm' I J L Ho Hk Hst He Hhk tl l Hl) in Cw.
    apply ownw_old in Nw.
    destruct He2 as [(He2 & Hte)|(-> & ->)].
    + assert (Z' : xl p s e) by (apply (proj1 (xl_old p s c k i m' a K u w Bd pc' tp' cm' I J L Ho Hk Hst He Hhk te e He2)); exact Z).
      exact (o_apair p s Q tl l tf f te e Hl Hf He2 E1 E2 T1 T2 X Y Z' w0 Cw Nw).
    + cbn [ec] in *. apply eQc_new; auto. rewrite <- E2. exact (o_acur p s Q tl l tf f Hl Hf E1 T1 X Y w0 Cw Nw).
  - (* o_QP_G *)
    intros t e H. apply ent_cases' in H. destruct H as [(H & Ht)|(-> & ->)].
    + intros y Y. destruct (o_QP_G p s Q t e H y Y) as [A|G]; [left; exact A|right; apply gk_old; exact G].
    + cbn [eQ eP esrc]. unfold esrc, srcv; cbn [erf ew et]. unfold evQ.
      intros x Hx. destruct (w || (is_load i && icond i (rg (cs s c)))) eqn:Z; [|destruct Hx].
      destruct Hx as [Hx|(Sx & _)].
      * destruct (xgop i (rg (cs s c))) eqn:G.
        -- exfalso. unfold xgop in G. destruct i as [| | |[]|]; simpl in G; try discriminate.
           simpl in Z. rewrite orb_false_r in Z. subst w. inversion He.
        -- destruct (o_sub_PG p s Q c x (o_gsub p s Q c x Hx)) as [Px|Gx].
           ++ left. left. rewrite (eff_K _ _ _ _ _ _ _ _ _ He G). exact Px.
           ++ right. apply gk_new. exact Gx.
      * left. right. left. exact Sx.
  - (* o_eRC *)
    intros t e H. apply ent_cases' in H. destruct H as [(H & Ht)|(-> & ->)].
    + destruct (at_dec p s c k i m' a K u w Bd pc' tp' cm' I J Ho Hk Hst He Hhk e) as [(E1 & E2)|N].
      * (* the CAS's read alone, now with its write *)
        destruct (half_x p s c k i m' a K u w Bd pc' tp' cm' I J L Ho Hk Hst He Hhk t e H E1 E2) as (A1 & (xs & A2) & A3 & A4).
        destruct (half_k p s c k i m' a K u w Bd pc' tp' cm' I J Ho Hk Hst He Hhk t e H E1 E2) as (_ & Ic & _).
        destruct (o_eRC p s Q t e H) as [R1 C1]. rewrite A1. rewrite A2 in R1, C1.
        assert (Ax : ai (cs s c) k = crd Plain xs) by (unfold einstr in A2; rewrite E1, E2 in A2; exact A2).
        rewrite Ax in Ic.
        unfold xload in A4. unfold evR, evC in *. rewrite A4, R1, C1, Ic.
        assert (Ia : isacc i = true) by (destruct i; try discriminate; reflexivity).
        apply andb_prop in A4. destruct A4 as [_ A4]. rewrite Ia, A4. auto.
      * destruct (ieval_old0' t e H N) as [A B]. destruct (o_eRC p s Q t e H) as [R1 C1].
        unfold evR, evC, rgof in *. rewrite A, R1, C1. rewrite (ieval_cond _ _ _ B). auto.
    + cbn [eR eC]. unfold rgof; cbn [ec ek]. rewrite ins_new'.
      unfold evR, evC. rewrite (ieval_cond _ _ _ ieval_new'). auto.
Qed.

End Step.

Lemma InvO_es : forall p t e, InvO p t -> InvO p (set_es t e).
Proof. intros p t e Q. destruct Q; constructor; auto. Qed.

(* ---------- a CAS's read alone ---------- *)
Section ReadO.
Variables (p : prog) (s : st) (c k : nat) (xs : list cell) (B : nat -> bool) (m' : mst) (a : val) (K : view)
          (u : cell -> option nat) (w : bool) (bv : bool).
Hypothesis I : Inv1 p s.
Hypothesis J : Inv2 p s.
Hypothesis L : Inv3 p s.
Hypothesis Q : InvO p s.
Hypothesis Ho : oc (cs s c) k = None.
Hypothesis Hk : pcs s c <= k.
Hypothesis Hh : oh (cs s c) k = None.
Local Abbreviation i := (ILd Plain xs (fun _ => true)).
Hypothesis He : eff (tm s) i (rg (cs s c)) (mof s c) m' a K u w.
Local Abbreviation t' := (sread s c k Plain xs B m' a K u w bv).
Local Abbreviation new := (newevh s c k i K u w).
Local Abbreviation rd_cases' := (rd_cases p s c k xs B m' a K u w bv I J Ho Hk Hh He).
Local Abbreviation rd_old0' := (rd_old0 p s c k xs B m' a K u w bv I J Ho Hk Hh He).
Local Abbreviation rd_k' := (rd_k p s c k xs B m' a K u w bv I J Ho Hk Hh He).
Local Abbreviation r3_xg_old' := (r3_xg_old p s c k xs B m' a K u w bv I J L Ho Hk Hh He).
Local Abbreviation r3_xl_old' := (r3_xl_old p s c k xs B m' a K u w bv I J L Ho Hk Hh He).
Local Abbreviation r3_xacq_old' := (r3_xacq_old p s c k xs B m' a K u w bv I J L Ho Hk Hh He).
Local Abbreviation r3_xg_new' := (r3_xg_new p s c k xs B m' a K u w bv I J L Ho Hk Hh He).
Local Abbreviation r3_xacq_new' := (r3_xacq_new p s c k xs B m' a K u w bv I J L Ho Hk Hh He).
Local Abbreviation r3_carr' := (r3_carr p s c k xs B m' a K u w bv I J L Ho Hk Hh He).
Local Abbreviation r3_old' := (r3_old p s c k xs B m' a K u w bv I J L Ho Hk Hh He).

Lemma ro_cs_new : vO (cs t' c) = vO (cs s c) /\ vOg (cs t' c) = vOg (cs s c) /\ vP (cs t' c) = mP m'.
Proof using All. unfold sread; simpl. unfold upd. rewrite Nat.eqb_refl. auto. Qed.

Lemma ro_lg_grow : forall a0 e, nth_error (lg s) a0 = Some e -> nth_error (lg t') a0 = Some e.
Proof using All. intros a0 e E. unfold sread; simpl. rewrite nth_error_app1; auto. apply nth_error_Some. congruence. Qed.

Lemma ro_ownw_old : forall c0 w0, ~ ownw t' c0 w0 -> ~ ownw s c0 w0.
Proof using All. intros c0 w0 N X. apply N. eapply ownw_grow; [exact ro_lg_grow|exact X]. Qed.

Lemma ro_eQ_new : vsub (vOg (cs s c)) (eQ new).
Proof using All. intros x Hx. cbn [eQ]. unfold evQ. rewrite orb_true_r. left. exact Hx. Qed.

Lemma ro_G : vsub (vG s) (vG t').
Proof using All. intros x Hx. change (mG m' x). apply (eff_G _ _ _ _ _ _ _ _ _ He). exact Hx. Qed.

Lemma ro_gk_old : forall te, vsub (gk p s te) (gk p t' te).
Proof using All.
  intros te y (Ly & Gy & Fy). split; [exact Ly|]. split; [apply ro_G; exact Gy|].
  intros tf f Hf T X. apply rd_cases' in Hf. destruct Hf as [(Hf & Htf)|(-> & ->)].
  - rewrite (r3_xg_old' tf f Hf) in X. exact (Fy tf f Hf T X).
  - exfalso. exact (r3_xg_new' X).
Qed.

Lemma ro_gk_new : vsub (vG s) (gk p t' (tm s)).
Proof using All.
  intros y Gy. split; [apply (isw_lt p s y I); apply (j_views p s J c); tauto|].
  split; [apply ro_G; exact Gy|].
  intros tf f Hf T X. apply rd_cases' in Hf. destruct Hf as [(_ & Htf)|(-> & _)]; lia.
Qed.

Lemma InvO_read : InvO p t'.
Proof using All.
  destruct ro_cs_new as (NO & NOg & NP).
  constructor.
  - (* o_sub_PG *)
    intros c'. destruct (Nat.eq_dec c' c) as [->|N].
    + rewrite NO, NP. intros x Hx. destruct (o_sub_PG p s Q c x Hx) as [Px|Gx].
      * left. apply (eff_P_mono _ _ _ _ _ _ _ _ _ He). exact Px.
      * right. apply ro_G. exact Gx.
    + rewrite r3_old' by auto. intros x Hx.
      destruct (o_sub_PG p s Q c' x Hx) as [Px|Gx]; [left; exact Px|right; apply ro_G; exact Gx].
  - (* o_gsub *)
    intros c'. destruct (Nat.eq_dec c' c) as [->|N].
    + rewrite NO, NOg. apply (o_gsub p s Q).
    + rewrite r3_old' by auto. apply (o_gsub p s Q).
  - (* o_gcur *)
    intros t f H X. apply rd_cases' in H. destruct H as [(H & Ht)|(-> & ->)].
    + rewrite (r3_xg_old' t f H) in X.
      pose proof (o_gcur p s Q t f H X) as G. destruct (Nat.eq_dec (ec f) c) as [E|N].
      * rewrite E in *. rewrite NOg. exact G.
      * rewrite r3_old' by auto. exact G.
    + exfalso. exact (r3_xg_new' X).
  - (* o_gpair *)
    intros tf f te e Hf He2 E T X Y. apply rd_cases' in Hf, He2.
    destruct Hf as [(Hf & Htf)|(-> & ->)]; destruct He2 as [(He2 & Hte)|(-> & ->)]; try lia.
    + rewrite (r3_xg_old' tf f Hf) in X.
      assert (Y' : xacc p s e).
      { destruct Y as [Y|Y]; [left; exact Y|right]. apply (proj1 (r3_xl_old' te e He2)). exact Y. }
      exact (o_gpair p s Q tf f te e Hf He2 E T X Y').
    + cbn [ec] in E. rewrite (r3_xg_old' tf f Hf) in X.
      intros x Hx. apply ro_eQ_new. rewrite <- E. apply (o_gcur p s Q tf f Hf X). exact Hx.
  - (* o_rfe *)
    intros t e x y ey H Ey Hy N. apply rd_cases' in H. destruct H as [(H & Ht)|(-> & ->)].
    + apply rd_cases' in Hy. destruct Hy as [(Hy & _)|(-> & ->)].
      * exact (o_rfe p s Q t e x y ey H Ey Hy N).
      * exfalso. destruct (j_rf p s J t e x (tm s) H Ey) as (Lt & _). lia.
    + cbn [erf ec eQ] in *. unfold evQ. rewrite orb_true_r. right. split; [eauto|].
      intros (Ow & _). destruct Ow as (e2 & E2 & C2 & _).
      apply rd_cases' in Hy. destruct Hy as [(Hy & _)|(-> & ->)].
      * unfold ent in Hy. rewrite E2 in Hy. injection Hy as <-. congruence.
      * cbn [ec] in N. congruence.
  - (* o_acur *)
    intros tl l tf f Hl Hf E T X Y w0 Cw Nw. apply rd_cases' in Hl, Hf.
    destruct Hl as [(Hl & Htl)|(-> & ->)]; [|lia].
    rewrite (r3_xl_old' tl l Hl) in X. rewrite r3_carr' in Cw. apply ro_ownw_old in Nw.
    destruct Hf as [(Hf & Htf)|(-> & ->)].
    + rewrite (r3_xacq_old' tf f Hf) in Y.
      pose proof (o_acur p s Q tl l tf f Hl Hf E T X Y w0 Cw Nw) as G.
      destruct (Nat.eq_dec (ec f) c) as [Ef|N].
      * rewrite Ef in *. rewrite NO. exact G.
      * rewrite r3_old' by auto. exact G.
    + exfalso. exact (r3_xacq_new' Y).
  - (* o_apair *)
    intros tl l tf f te e Hl Hf He2 E1 E2 T1 T2 X Y Z w0 Cw Nw.
    apply rd_cases' in Hl, Hf, He2.
    destruct Hl as [(Hl & Htl)|(-> & ->)]; [|lia].
    destruct Hf as [(Hf & Htf)|(-> & ->)]; [|destruct He2 as [(_ & Z')|(Z' & _)]; lia].
    rewrite (r3_xl_old' tl l Hl) in X. rewrite (r3_xacq_old' tf f Hf) in Y.
    rewrite r3_carr' in Cw. apply ro_ownw_old in Nw.
    destruct He2 as [(He2 & Hte)|(-> & ->)].
    + assert (Z' : xl p s e) by (apply (proj1 (r3_xl_old' te e He2)); exact Z).
      exact (o_apair p s Q tl l tf f te e Hl Hf He2 E1 E2 T1 T2 X Y Z' w0 Cw Nw).
    + cbn [ec eQc] in *. unfold evQc. cbn. rewrite <- E2. exact (o_acur p s Q tl l tf f Hl Hf E1 T1 X Y w0 Cw Nw).
  - (* o_QP_G *)
    intros t e H. apply rd_cases' in H. destruct H as [(H & Ht)|(-> & ->)].
    + intros y Y. destruct (o_QP_G p s Q t e H y Y) as [A|G]; [left; exact A|right; apply ro_gk_old; exact G].
    + cbn [eQ eP esrc]. unfold esrc, srcv; cbn [erf ew et]. unfold evQ. rewrite orb_true_r.
      intros x [Hx|(Sx & _)].
      * destruct (o_sub_PG p s Q c x (o_gsub p s Q c x Hx)) as [Px|Gx].
        -- left. left. rewrite (eff_K _ _ _ _ _ _ _ _ _ He eq_refl). exact Px.
        -- right. apply ro_gk_new. exact Gx.
      * left. right. left. exact Sx.
  - (* o_eRC *)
    intros t e H. apply rd_cases' in H. destruct H as [(H & Ht)|(-> & ->)].
    + destruct (rd_old0' t e H) as (A & B0 & _). destruct (o_eRC p s Q t e H) as [R1 C1].
      unfold evR, evC, rgof in *. rewrite A, R1, C1. rewrite (ieval_cond _ _ _ B0). auto.
    + cbn [eR eC]. unfold einstr, rgof; cbn [ec ek]. rewrite (proj1 rd_k'). split; reflexivity.
Qed.

End ReadO.

Section MatchO.
Variables (p : prog) (s : st) (c : nat) (d : desc).
Hypothesis I : Inv1 p s.
Hypothesis J : Inv2 p s.
Hypothesis L : Inv3 p s.
Hypothesis Q : InvO p s.
Local Abbreviation cc := (cs s c).
Local Abbreviation k := (pcs s c).
Hypothesis Ho : oc cc k <> None.
Hypothesis Ha : ai cc k = inst_of d.
Hypothesis Hdf : eof (ins p c k (rg cc)) (rg cc) = Some d.
Local Abbreviation s' := (smatch p s c).

Lemma vO_m : forall c', vO (cs s' c') = vO (cs s c').
Proof using All.
  intros c'. unfold smatch; cbn [cs]. unfold upd. destruct (Nat.eqb c' c) eqn:E; [apply Nat.eqb_eq in E; subst|]; simpl; auto.
Qed.

Lemma vOg_m : forall c', vOg (cs s' c') = vOg (cs s c').
Proof using All.
  intros c'. unfold smatch; cbn [cs]. unfold upd. destruct (Nat.eqb c' c) eqn:E; [apply Nat.eqb_eq in E; subst|]; simpl; auto.
Qed.

Lemma InvO_match : InvO p s'.
Proof using All.
  assert (VO : forall c', vO (cs s' c') = vO (cs s c')) by apply vO_m.
  assert (VOg : forall c', vOg (cs s' c') = vOg (cs s c')) by apply vOg_m.
  assert (VP : forall c', vP (cs s' c') = vP (cs s c')) by (intros; apply (views_m p s c d I J L Ho Ha Hdf)).
  assert (EN : forall t, ent s' t = ent s t) by reflexivity.
  assert (XG : forall e, xg p s' e <-> xg p s e) by (apply (xg_m p s c d I J L Ho Ha Hdf)).
  assert (XL : forall e, xl p s' e <-> xl p s e) by (apply (xl_m p s c d I J L Ho Ha Hdf)).
  assert (XA : forall e, xll p s' e <-> xll p s e) by (apply (xacq_m p s c d I J L Ho Ha Hdf)).
  assert (XC : forall e, xacc p s' e <-> xacc p s e) by (intros e; unfold xacc; rewrite XL; tauto).
  assert (RC : forall t e, ent s' t = Some e ->
    eR e = evR (einstr p s' e) (rgof s' e) /\ eC e = evC (einstr p s' e) (rgof s' e)).
  { intros t e H. rewrite EN in H. destruct (o_eRC p s Q t e H) as [R1 C1].
    rewrite (rgof_match p s c d I J Ho Ha Hdf e). rewrite R1, C1.
    destruct (prof_of p s c d I J L Ho Ha Hdf e) as [E|(d' & D1 & D2)]; [rewrite E; auto|].
    destruct (same_prof _ _ _ _ D1 D2) as (P1 & P2 & P3 & P4 & _).
    pose proof (dof_isacc _ _ _ D1) as A1. pose proof (dof_isacc _ _ _ D2) as A2.
    assert (ER : forall i0 r0, evR i0 r0 = if xload i0 r0 then icells i0 else []) by reflexivity.
    rewrite !ER, P1, P2. split; auto. unfold evC. rewrite A1, A2, P4, P1. auto. }
  assert (VG : vG s' = vG s) by reflexivity.
  assert (QG : forall t e, ent s' t = Some e -> vsub (eQ e) (vor (vor (eP e) (esrc e)) (gk p s' t))).
  { intros t e H y Y. rewrite EN in H. destruct (o_QP_G p s Q t e H y Y) as [A|(Ly & Gy & Fy)]; [left; exact A|right].
    split; [exact Ly|]. split; [rewrite VG; exact Gy|].
    intros tf f Hf T X. rewrite EN in Hf. apply XG in X. exact (Fy tf f Hf T X). }
  destruct Q. constructor; try exact RC; try exact QG; intros; rewrite ?VO, ?VOg, ?VP, ?VG, ?EN in *;
  repeat match goal with
         | H : xg p s' ?e |- _ => apply XG in H
         | H : xl p s' ?e |- _ => apply XL in H
         | H : xll p s' ?e |- _ => apply XA in H
         | H : xacc p s' ?e |- _ => apply XC in H
         end;
  unfold carr, ownw in *; simpl in *; eauto.
Qed.
End MatchO.

Section SkipO.
Variables (p : prog) (s : st) (c : nat).
Hypothesis I : Inv1 p s.
Hypothesis J : Inv2 p s.
Hypothesis L : Inv3 p s.
Hypothesis Q : InvO p s.
Hypothesis Ho : oc (cs s c) (pcs s c) = None.
Hypothesis Hh : oh (cs s c) (pcs s c) <> None ->
  eofR (ins p c (pcs s c) (rg (cs s c))) (rg (cs s c)) = eofR (ai (cs s c) (pcs s c)) (rg (cs s c)).
Local Abbreviation s' := (sskip p s c).

Lemma cs_skip_views : forall c', vP (cs s' c') = vP (cs s c') /\ vO (cs s' c') = vO (cs s c') /\
  vOg (cs s' c') = vOg (cs s c').
Proof. intros c'. unfold sskip; cbn [cs]. unfold upd. destruct (Nat.eqb c' c) eqn:E; [apply Nat.eqb_eq in E; subst|]; simpl; auto. Qed.

Lemma xg_skip : forall t e, ent s t = Some e -> xg p s' e <-> xg p s e.
Proof. apply (xg_sk p s c I J L Ho Hh). Qed.
Lemma xl_skip : forall t e, ent s t = Some e -> xl p s' e <-> xl p s e.
Proof. apply (xl_sk p s c I J L Ho Hh). Qed.
Lemma xll_skip : forall t e, ent s t = Some e -> xll p s' e <-> xll p s e.
Proof. apply (xll_sk p s c I J L Ho Hh). Qed.
Lemma xacc_skip : forall t e, ent s t = Some e -> xacc p s' e <-> xacc p s e.
Proof. intros t e H. unfold xacc. rewrite (xl_skip t e H). tauto. Qed.

Lemma InvO_skip : InvO p s'.
Proof.
  assert (VP : forall c', vP (cs s' c') = vP (cs s c')) by (intros; apply cs_skip_views).
  assert (VO : forall c', vO (cs s' c') = vO (cs s c')) by (intros; apply cs_skip_views).
  assert (VOg : forall c', vOg (cs s' c') = vOg (cs s c')) by (intros; apply cs_skip_views).
  destruct Q. constructor.
  - intros c'. rewrite VP, VO. exact (o_sub_PG0 c').
  - intros c'. rewrite VO, VOg. exact (o_gsub0 c').
  - intros t f H X. rewrite (xg_skip t f H) in X. rewrite VOg. exact (o_gcur0 t f H X).
  - intros tf f te e Hf He E T X Y. rewrite (xg_skip tf f Hf) in X. rewrite (xacc_skip te e He) in Y.
    exact (o_gpair0 tf f te e Hf He E T X Y).
  - exact o_rfe0.
  - intros tl l tf f Hl Hf E T X Y w0 Cw Nw. rewrite (xl_skip tl l Hl) in X. rewrite (xll_skip tf f Hf) in Y.
    rewrite VO. exact (o_acur0 tl l tf f Hl Hf E T X Y w0 Cw Nw).
  - intros tl l tf f te e Hl Hf He E1 E2 T1 T2 X Y Z w0 Cw Nw. rewrite (xl_skip tl l Hl) in X.
    rewrite (xll_skip tf f Hf) in Y. rewrite (xl_skip te e He) in Z.
    exact (o_apair0 tl l tf f te e Hl Hf He E1 E2 T1 T2 X Y Z w0 Cw Nw).
  - intros t e H y Yq. destruct (o_QP_G0 t e H y Yq) as [A|(Ly & Gy & Fy)]; [left; exact A|right].
    split; [exact Ly|]. split; [exact Gy|]. intros tf f Hf T X. rewrite (xg_skip tf f Hf) in X. exact (Fy tf f Hf T X).
  - intros t e H. rewrite (rgof_skip p s c I J Ho Hh).
    destruct (einstr_skip p s c I J Ho Hh t e H) as [A|(Eh & xs & A & Ic & Xl & Cs)]; [rewrite A; exact (o_eRC0 t e H)|].
    destruct (o_eRC0 t e H) as [R1 C1]. rewrite A in R1, C1. revert Xl Ic. generalize (einstr p s' e). intros i0 Xl Ic.
    unfold rgof, evR, evC in *. destruct i0; try discriminate; cbn in Xl, Ic, R1, C1 |- *; unfold icond; cbn; rewrite Xl; rewrite Ic; split; assumption.
Qed.
End SkipO.

(* ---------- a CAS whose read happened alone commits to failure ---------- *)
Section CfailO.
Variables (p : prog) (s : st) (c k : nat).
Hypothesis I : Inv1 p s.
Hypothesis L : Inv3 p s.
Hypothesis Q : InvO p s.
Hypothesis Hp : pcs s c <= k.
Hypothesis Ho : oc (cs s c) k = None.
Local Abbreviation s' := (scfail s c k).

Lemma InvO_cfail : InvO p s'.
Proof.
  assert (VW : forall c', vP (cs s' c') = vP (cs s c') /\ vO (cs s' c') = vO (cs s c') /\ vOg (cs s' c') = vOg (cs s c')).
  { intros c'. rewrite cs_cf. destruct (Nat.eqb_spec c' c); [subst|]; repeat split. }
  assert (XG : forall t e, ent s t = Some e -> xg p s' e <-> xg p s e) by (intros t e H; exact (xg_cf p s c k I L Hp Ho t e H)).
  assert (XL : forall t e, ent s t = Some e -> xl p s' e <-> xl p s e) by (intros t e H; exact (xl_cf p s c k I L Hp Ho t e H)).
  assert (XLL : forall e, xll p s' e <-> xll p s e) by (intros e; unfold xll; rewrite einstr_cf by assumption; tauto).
  assert (XA : forall t e, ent s t = Some e -> xacc p s' e <-> xacc p s e) by (intros t e H; unfold xacc; rewrite (XL t e H); tauto).
  destruct Q. constructor.
  - intros c'. rewrite (proj1 (VW c')), (proj1 (proj2 (VW c'))). exact (o_sub_PG0 c').
  - intros c'. rewrite (proj1 (proj2 (VW c'))), (proj2 (proj2 (VW c'))). exact (o_gsub0 c').
  - intros t f H X. rewrite (XG t f H) in X. rewrite (proj2 (proj2 (VW _))). exact (o_gcur0 t f H X).
  - intros tf f te e Hf He E T X Y. rewrite (XG tf f Hf) in X. rewrite (XA te e He) in Y.
    exact (o_gpair0 tf f te e Hf He E T X Y).
  - exact o_rfe0.
  - intros tl l tf f Hl Hf E T X Y w0 Cw Nw. rewrite (XL tl l Hl) in X. rewrite XLL in Y.
    rewrite (proj1 (proj2 (VW _))). exact (o_acur0 tl l tf f Hl Hf E T X Y w0 Cw Nw).
  - intros tl l tf f te e Hl Hf He E1 E2 T1 T2 X Y Z w0 Cw Nw. rewrite (XL tl l Hl) in X.
    rewrite XLL in Y. rewrite (XL te e He) in Z.
    exact (o_apair0 tl l tf f te e Hl Hf He E1 E2 T1 T2 X Y Z w0 Cw Nw).
  - intros t e H y Yq. destruct (o_QP_G0 t e H y Yq) as [A|(Ly & Gy & Fy)]; [left; exact A|right].
    split; [exact Ly|]. split; [exact Gy|]. intros tf f Hf T X. rewrite (XG tf f Hf) in X. exact (Fy tf f Hf T X).
  - intros t e H. rewrite einstr_cf by assumption. pose proof (ieval_ent_cf p s c k I L Hp Ho t e H) as Qv.
    destruct (o_eRC0 t e H) as [R1 C1]. unfold evR, evC, icond in *. rewrite Qv. split; assumption.
Qed.
End CfailO.

(* S3c: a result fixed changes only bd and fx *)
Lemma InvO_cfix : forall p s c j b B, InvO p s -> InvO p (scfix0 s c j b B).
Proof.
  intros p s c j b B Q.
  assert (XG : forall e, xg p (scfix0 s c j b B) e <-> xg p s e) by (intros e; unfold xg; rewrite einstr_cx, rgof_cx; tauto).
  assert (XL : forall e, xl p (scfix0 s c j b B) e <-> xl p s e) by (intros e; unfold xl; rewrite einstr_cx, rgof_cx; tauto).
  assert (XLL : forall e, xll p (scfix0 s c j b B) e <-> xll p s e) by (intros e; unfold xll; rewrite einstr_cx; tauto).
  assert (XA : forall e, xacc p (scfix0 s c j b B) e <-> xacc p s e) by (intros e; unfold xacc; rewrite XL; tauto).
  destruct Q. constructor.
  - intros c'. rewrite vO_cx, vP_cx. exact (o_sub_PG0 c').
  - intros c'. rewrite vO_cx, vOg_cx. exact (o_gsub0 c').
  - intros t f H X. rewrite XG in X. rewrite vOg_cx. exact (o_gcur0 t f H X).
  - intros tf f te e Hf He E T X Y. rewrite XG in X. rewrite XA in Y. exact (o_gpair0 tf f te e Hf He E T X Y).
  - exact o_rfe0.
  - intros tl l tf f Hl Hf E T X Y w0 Cw Nw. rewrite XL in X. rewrite XLL in Y.
    rewrite vO_cx. exact (o_acur0 tl l tf f Hl Hf E T X Y w0 Cw Nw).
  - intros tl l tf f te e Hl Hf He E1 E2 T1 T2 X Y Z w0 Cw Nw. rewrite XL in X. rewrite XLL in Y. rewrite XL in Z.
    exact (o_apair0 tl l tf f te e Hl Hf He E1 E2 T1 T2 X Y Z w0 Cw Nw).
  - intros t e H y Yq. destruct (o_QP_G0 t e H y Yq) as [A|(Ly & Gy & Fy)]; [left; exact A|right].
    split; [exact Ly|]. split; [exact Gy|]. intros tf f Hf T X. rewrite XG in X. exact (Fy tf f Hf T X).
  - intros t e H. rewrite einstr_cx, rgof_cx. exact (o_eRC0 t e H).
Qed.

Record InvAllO (p : prog) (s : st) : Prop := { iao1 : Inv1 p s; iao2 : Inv2 p s; iao3 : Inv3 p s; iaoO : InvO p s }.

Lemma InvO_run : forall p s, run p s -> InvAllO p s.
Proof.
  intros p s R. induction R as [|s t R IH H].
  - constructor; [apply Inv1_init|apply Inv2_init|apply Inv3_init|apply InvO_init].
  - destruct IH as [I J L Q].
    assert (R' : run p t) by (econstructor; eauto).
    destruct (Inv_run p t R') as [I' J' L'].
    constructor; auto.
    destruct (step_cases p s t H) as [(c & i & m' & a & K & u & w & H1 & H2 & H3 & H4 & Hbh & Hh & _ & _ & H6 & _ & ->)|[(c & k & d & B & m' & a & K & u & w & H1 & H2 & Hso & Hh & _ & _ & H5 & _ & ->)|[(c & d & H1 & H2 & H3 & H4 & H4m & Hfh & ->)|[(c & k & xs & B & m' & a & K & u & w & bv & H1 & H2 & Hh & Hso & H4 & H5 & _ & ->)|[(c & S1 & S2 & S3 & _ & S5 & S4 & _ & ->)|(cX & jX & bX & BX & oX & HjX & HfX & HcX & ->)]]]]].
    + eapply InvO_step; eauto; [intros r Sr; apply (proj2 (H3 r Sr))|].
      destruct Hh as [(Z & _)|(t1 & Z & Ci & U & Ef)]; [left; exact Z|right; split; [exact U|exact Ef]].
    + apply InvO_es. eapply InvO_step; eauto; [lia|intros r Sr; apply ieval_inst|].
      destruct Hh as [(Z & _)|(t1 & xs & ev & nv & Z & -> & U & Ac & _)]; [left; exact Z|right].
      split; [exact U|]. rewrite Ac. reflexivity.
    + eapply InvO_match; eauto.
    + apply InvO_read; auto.
    + apply InvO_skip; auto.
    + destruct oX as [kX|]; [destruct bX|]; cbn [sflp]; apply InvO_cfix; [auto| |auto].
      destruct (cfix_rec _ _ _ _ _ _ _ _ _ HcX) as (HpX & HoX & HhX & _). apply InvO_cfail; auto.
Qed.
