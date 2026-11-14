(* Model2 over the interface: traces of the model's steps, and a base (an
   interleaving of the slots a state has passed) with its writes. *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO M2SC M2SCx M2Trace MIPComp MIPNeg MIPSync M2Iface.

Lemma acc_ev : forall p l g q e xs w, wf p -> srun p l g -> nth_error l q = Some e -> sacc e = Some (xs, w) ->
  icells (ins p (sx e) (sk e) (sr g (sx e))) = xs /\
  executes (ins p (sx e) (sk e) (sr g (sx e))) (sr g (sx e)) = true.
Proof.
  intros p l g q e xs w W R Q A. destruct (srun_ev p W l g R q e Q) as (i & Hi & _ & Sh). rewrite Hi.
  rewrite A in Sh. unfold executes, icond.
  destruct i as [md y c|md y c u|md y c e0 n|fk|]; simpl in Sh |- *;
    try (destruct (c (sr g (sx e))) eqn:C; injection Sh; intros; subst; auto; discriminate);
    try (destruct fk; discriminate); discriminate.
Qed.

Section Tr.
Context `{IFM : Model}.
Variable p : prog.

Lemma gtrace_le : forall f n m, gtrace (STEP p) f n -> m <= n -> gtrace (STEP p) f m.
Proof. intros f n m [A B] L. split; auto. intros i Li. apply B. lia. Qed.

Lemma gtrace_reach : forall f n, gtrace (STEP p) f n -> forall i, i <= n -> reach (STEP p) (f i).
Proof.
  intros f n [A B] i L. induction i as [|i IH]; [rewrite A; constructor|].
  apply reS with (f i); [apply IH; lia|apply B; lia].
Qed.

Lemma reach_gtrace : forall s, reach (STEP p) s -> exists f n, gtrace (STEP p) f n /\ f n = s.
Proof.
  intros s R. induction R as [|s s' R IH St].
  - exists (fun _ => sinit), 0. split; [split; [auto|intros; lia]|auto].
  - destruct IH as (f & n & [A B] & E).
    exists (fun i => if Nat.leb i n then f i else s'), (S n). split; [split|].
    + simpl. auto.
    + intros i Li. destruct (Nat.leb_spec i n); [|lia].
      destruct (Nat.leb_spec (S i) n).
      * apply B. lia.
      * assert (i = n) by lia. subst i. rewrite E. auto.
    + destruct (Nat.leb_spec (S n) n); [lia|auto].
Qed.

Lemma gtr_ext : forall f n, gtrace (STEP p) f n -> forall i j, i <= j -> j <= n -> Ext (f i) (f j).
Proof.
  intros f n T i j L Lj. induction j as [|j IH].
  - assert (i = 0) by lia. subst. apply Ext_refl.
  - destruct (Nat.eq_dec i (S j)) as [->|N]; [apply Ext_refl|].
    apply Ext_trans with (f j); [apply IH; lia|].
    apply (g_keeps p _ (GG p)); [apply (gtrace_reach f n T); lia|apply (proj2 T); lia].
Qed.

Lemma evok_gtr : forall f n, gtrace (STEP p) f n -> evok (f n) -> forall m, m <= n -> evok (f m).
Proof.
  intros f n T E m L. remember (n - m) as d eqn:Ed. revert m L Ed. induction d as [|d IHd]; intros m L Ed.
  - assert (m = n) by lia. subst. exact E.
  - apply (g_rule_back p _ (GG p) (f m) (f (S m))); [apply (gtrace_reach f n T); lia|apply (proj2 T); lia|].
    apply IHd; lia.
Qed.
End Tr.

(* ---------- a base and its writes ---------- *)
Section Base.
Context `{IFM : Model}.
Variable p : prog.
Hypothesis W : wf p.
Variable sb : st.
Hypothesis Rb : reach (STEP p) sb.
Variables (lb : list sev) (gb : sst).
Hypothesis Bsr : srun p lb gb.
Hypothesis Bsp : forall c, sp gb c = pcs sb c.
Hypothesis Brg : forall c j, j < pcs sb c -> sr gb c j = rg (cs sb c) j.

Lemma Ib1 : Inv1 p sb. Proof. apply I1g. exact Rb. Qed.
Lemma Ib2 : Inv2 p sb. Proof. apply I2g. exact Rb. Qed.

Lemma lb_fa : forall c j, j < sp gb c -> j < pcs sb c -> sr gb c j = rrg sb c j.
Proof. intros c j _ L. apply Brg. auto. Qed.

Lemma lb_pass : forall q e, nth_error lb q = Some e -> sk e < pcs sb (sx e).
Proof. intros q e Q. destruct (srun_ev p W lb gb Bsr q e Q) as (_ & _ & L & _). rewrite Bsp in L. auto. Qed.

(* a sequential event that accesses comes from an instruction that executes *)
Lemma lb_exec : forall q e, nth_error lb q = Some e -> sacc e <> None ->
  executes (ins p (sx e) (sk e) (rrg sb (sx e))) (rrg sb (sx e)) = true.
Proof.
  intros q e Q N. pose proof (lb_pass q e Q) as P.
  pose proof (ev_faith p sb Rb W lb gb Bsr lb_fa q e Q P) as Sh.
  revert Sh. unfold executes. destruct (ins p (sx e) (sk e) (rrg sb (sx e))) as [m0 x0 c0|m0 x0 c0 v0|m0 x0 c0 e0 n0|f0|];
    intros Sh; unfold evshape in Sh; simpl; try reflexivity;
    unfold icond, ieval; simpl; destruct (c0 (rrg sb (sx e))); try reflexivity; exfalso; apply N;
    injection Sh as S1 _; exact S1.
Qed.

Lemma lb_ev : forall q e, nth_error lb q = Some e ->
  executes (ins p (sx e) (sk e) (rrg sb (sx e))) (rrg sb (sx e)) = true ->
  exists E, RE sb (sx e) (sk e) E /\ einstr p sb E = ins p (sx e) (sk e) (rrg sb (sx e)) /\
    sacc e = (if icond (ins p (sx e) (sk e) (rrg sb (sx e))) (rrg sb (sx e)) && isacc (ins p (sx e) (sk e) (rrg sb (sx e)))
              then Some (icells (ins p (sx e) (sk e) (rrg sb (sx e))), ew E)
              else None) /\
    sg e = xgop (ins p (sx e) (sk e) (rrg sb (sx e))) (rrg sb (sx e)).
Proof.
  intros q e Q Xe. pose proof (lb_pass q e Q) as P.
  destruct (n_ent p sb Rb W (sx e) (sk e) _ eq_refl P Xe) as (E & RE0 & Ei).
  exists E. split; [auto|]. split; [auto|].
  pose proof (ev_faith p sb Rb W lb gb Bsr lb_fa q e Q P) as Sh.
  destruct RE0 as (A & B & C).
  rewrite (ev_rel p sb Rb W (sx e) (sk e) _ E (insr_of p sb Rb W _ _ P) Xe A B C) in Sh.
  injection Sh as S1 S2. split; auto.
Qed.

Lemma lb_write : forall q e x, nth_error lb q = Some e -> writes_x e x = true ->
  exists E, RE sb (sx e) (sk e) E /\ ew E = true /\ In x (icells (einstr p sb E)) /\
    In (bt sb (sx e) (sk e)) (ids (hs sb x)) /\
    wv sb (bt sb (sx e) (sk e)) x = cval (icells (ins p (sx e) (sk e) (rrg sb (sx e)))) (wvals (ins p (sx e) (sk e) (rrg sb (sx e))) (rrg sb (sx e))) x.
Proof.
  intros q e x Q X.
  assert (Xe : executes (ins p (sx e) (sk e) (rrg sb (sx e))) (rrg sb (sx e)) = true).
  { apply (lb_exec q e Q). unfold writes_x in X. destruct (sacc e); [discriminate|discriminate X]. }
  destruct (lb_ev q e Q Xe) as (E & RE0 & Ei & Sa & _).
  unfold writes_x in X. rewrite Sa in X.
  destruct (icond _ _ && isacc _) eqn:Cd; [|discriminate].
  destruct (ew E) eqn:Ew; [|discriminate].
  apply existsb_exists in X. destruct X as (z & Iz & Z). apply Nat.eqb_eq in Z. subst z.
  destruct RE0 as (A & B & C).
  destruct (j_ew p sb Ib2 _ E _ A Ei) as [_ W2]. destruct (W2 Ew) as [V Hh].
  unfold rgof in V. rewrite B in V.
  exists E. split; [split; auto|]. split; [auto|]. split; [rewrite Ei; auto|]. split.
  - apply Hh. auto.
  - rewrite V. reflexivity.
Qed.

Lemma lb_has_write : forall cy ky Ey x, ky < pcs sb cy -> RE sb cy ky Ey -> ew Ey = true ->
  In x (icells (einstr p sb Ey)) ->
  exists q e, nth_error lb q = Some e /\ sx e = cy /\ sk e = ky /\ writes_x e x = true.
Proof.
  intros cy ky Ey x L REy Wy Iy.
  destruct (proj1 (srun_pos p W lb gb Bsr cy ky) ltac:(rewrite Bsp; auto)) as (q & e & Q & Xe & Ke).
  exists q, e. split; [auto|]. split; [auto|]. split; [auto|].
  assert (Xq : executes (ins p (sx e) (sk e) (rrg sb (sx e))) (rrg sb (sx e)) = true).
  { rewrite Xe, Ke. pose proof REy as (A0 & B0 & C0).
    destruct (j_ew p sb Ib2 _ Ey _ A0 eq_refl) as [Ew0 _]. rewrite Wy in Ew0. symmetry in Ew0.
    rewrite (einstr_ins p sb Rb W _ Ey A0 ltac:(rewrite B0, C0; exact L)), B0, C0 in Ew0. unfold rgof in Ew0. rewrite B0 in Ew0.
    apply andb_prop in Ew0 as [Ew0 _]. apply andb_prop in Ew0 as [St0 Cd0]. apply andb_prop in St0 as [_ St0].
    unfold executes, MIPComp.rrg in *. rewrite Cd0. destruct (isacc _); reflexivity. }
  destruct (lb_ev q e Q Xq) as (E' & RE' & Ei' & Sa & _). rewrite Xe, Ke in RE', Ei', Sa.
  assert (E' = Ey) by (destruct RE' as (A1 & _); destruct REy as (A2 & _); congruence). subst E'.
  rewrite Ei' in Iy.
  destruct REy as (A & B & C).
  destruct (j_ew p sb Ib2 _ Ey _ A Ei') as [Ew _]. rewrite Wy in Ew. symmetry in Ew.
  apply andb_prop in Ew as [Ew _]. apply andb_prop in Ew as [St Cd]. apply andb_prop in St as [_ St]. unfold rgof in Cd. rewrite B in Cd.
  unfold writes_x. rewrite Sa. unfold rrg, M2PComp.rrg in *. rewrite Cd. simpl.
  assert (Ia : isacc (ins p cy ky (rg (cs sb cy))) = true) by (destruct (ins p cy ky (rg (cs sb cy))); simpl in St; try discriminate; reflexivity).
  rewrite Ia, Wy. apply existsb_exists. exists x. split; [exact Iy|apply Nat.eqb_refl].
Qed.

(* the value the base leaves in a cell it wrote last *)
Lemma base_sm : forall q w x, lw lb x = Some w -> nth_error lb q = Some w ->
  sm gb x = wv sb (bt sb (sx w) (sk w)) x.
Proof.
  intros q w x Lw Q.
  destruct (lw_spec lb x w Lw) as (q' & Q' & X & _).
  destruct (lb_write q w x Q X) as (E & _ & _ & _ & _ & V). rewrite V.
  destruct (proj2 (srun_mem p W lb gb Bsr x) w Lw) as (i & Hi & M). rewrite M.
  pose proof (lb_pass q w Q) as P.
  assert (Ag : forall j, j < sk w -> sr gb (sx w) j = rrg sb (sx w) j) by (intros j L; apply Brg; lia).
  assert (Hi' : ins p (sx w) (sk w) (rrg sb (sx w)) = i) by (rewrite <- Hi; symmetry; apply wf_ins; auto).
  rewrite Hi'. rewrite (ieval_wvals i _ _ (wf_ieval p (sx w) (sk w) i _ _ W Hi Ag)). reflexivity.
Qed.

End Base.
