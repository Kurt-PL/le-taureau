(* Part 4: the write-back patch keeps KR. *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB M2DQWBK1 M2DQWBK2 M2DQWBK3.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQShim.

Lemma ids_ins_nodup : forall h1 h2 t b, NoDup (ids (h1 ++ h2)) -> ~ In t (ids (h1 ++ h2)) -> NoDup (ids (h1 ++ (t, b) :: h2)).
Proof.
  intros h1 h2 t b N I. rewrite ids_app in *. simpl. apply (NoDup_Add (Add_app t (ids h1) (ids h2))). auto.
Qed.

Section Patch.
Variables (p : prog) (Fk : Prop) (Good : nat -> Prop) (sw : nat -> option (cell -> option nat)) (s sA : st) (c k t : nat) (H'' : cell -> hist).
Hypothesis RA : run p sA.
Hypothesis R : rel sw s sA.
Hypothesis K : KR Fk Good sw s sA.
Hypothesis Ht : t < tm s.
Hypothesis Hfresh : forall x, ~ In t (ids (hs s x)).
Hypothesis Hok : wbok s c k t H''.
Hypothesis Hent : exists e, ent s t = Some e /\ ec e = c /\ ek e = k.
Hypothesis Hcas : is_cas (ai (cs s c) k) = true.
Hypothesis Htmo : tmo (cs s c) k = Some t.
Hypothesis Hoh : forall c' j, oh (cs s c') j = Some t -> c' = c /\ j = k /\ oc (cs s c) k = None /\ (k < pcs s c \/ vok (rg (cs s c) k) = false).
Hypothesis Hff : forall tf g, ent s tf = Some g -> isFF s tf g -> ec g = c -> tf < t.
Hypothesis HewA : forall eA, ent sA t = Some eA -> ew eA = false.

Let u := rw (cs s c) k.
Let f : cell -> option nat := fun x => pi sw x (u x).
Let sw' := upd sw t (Some f).
Let s' := wbst s c k t H''.

Lemma ent_wb : forall t', ent s' t' = option_map (sete t) (ent s t').
Proof. intros t'. unfold ent, s', wbst. cbv zeta. cbn [lg]. apply nth_setew. Qed.

Lemma cs_wb : forall c', cs s' c' = if Nat.eqb c' c then
  mkC (oc (cs s c)) (rg (cs s c)) (ai (cs s c)) (upd (rw (cs s c)) k (wbrw (cs s c) k (icells (ai (cs s c) k)) t)) (rv (cs s c)) (bd (cs s c))
      (vor (vP (cs s c)) (vone t)) (vA (cs s c)) (vR (cs s c)) (vO (cs s c)) (vOg (cs s c)) (oh (cs s c)) (fx (cs s c))
  else cs s c'.
Proof. intros c'. unfold s', wbst. cbv zeta. cbn [cs]. unfold upd. reflexivity. Qed.

Lemma cs_wb_f : forall c', oc (cs s' c') = oc (cs s c') /\ oh (cs s' c') = oh (cs s c') /\ ai (cs s' c') = ai (cs s c') /\
  rg (cs s' c') = rg (cs s c') /\ vA (cs s' c') = vA (cs s c') /\ vOg (cs s' c') = vOg (cs s c') /\
  vsub (vP (cs s c')) (vP (cs s' c')).
Proof.
  intros c'. rewrite cs_wb. destruct (Nat.eqb_spec c' c) as [->|N]; cbn; repeat split; try reflexivity; intros z Z; auto. left. exact Z.
Qed.

Lemma pcs_wb : pcs s' = pcs s. Proof. reflexivity. Qed.
Lemma hs_wb : hs s' = H''. Proof. reflexivity. Qed.

Lemma isFF_wb : forall tf g, isFF s' tf g <-> isFF s tf g.
Proof.
  intros tf g. unfold isFF. destruct (cs_wb_f (ec g)) as (Oc & _ & Ai & _). rewrite Oc, Ai, pcs_wb. tauto.
Qed.

Lemma G_wb : forall a b, gedge s a b -> gedge s' a b.
Proof. exact (wbst_grows s c k t H'' Hok). Qed.
Lemma cov_wb : forall V, vsub (cov s V) (cov s' V).
Proof. apply cov_grow. exact G_wb. Qed.
Lemma pth_wb : forall a b, Pth s a b -> Pth s' a b.
Proof.
  intros a b P. unfold Pth in *. induction P as [a b G|a b c' _ IH1 _ IH2];
    [constructor; exact (G_wb a b G)|exact (t_trans _ _ a b c' IH1 IH2)].
Qed.

Lemma hs_old : forall x w0, In w0 (ids (hs s x)) -> In w0 (ids (hs s' x)).
Proof.
  intros x w0 I. rewrite hs_wb. destruct (enters_tied_cell _ _ _ _ _ x Hok) as [E|(h1 & h2 & E1 & E2 & _)]; [rewrite E; exact I|].
  rewrite E2. rewrite E1 in I. apply in_ids_ins. right. exact I.
Qed.

Lemma et_t : forall t' e, ent s t' = Some e -> (Nat.eqb (et e) t = true <-> t' = t).
Proof.
  intros t' e E. destruct (i_etW p Fk Good sw s sA RA R K t' e E) as [Et _]. rewrite Et. apply Nat.eqb_eq.
Qed.

Lemma ownw_wb : forall c' z, ownw s' c' z -> ownw s c' z \/ (z = t /\ c' = c).
Proof.
  intros c' z (e' & E & Ec & Ew). unfold s', wbst in E. cbv zeta in E. cbn [lg] in E. rewrite nth_setew in E.
  destruct (nth_error (lg s) z) as [e|] eqn:Ez; [|discriminate]. cbn in E. injection E as <-.
  unfold sete in *. destruct (Nat.eqb (et e) t) eqn:Et.
  - right. apply (et_t z e Ez) in Et. subst z. split; [reflexivity|]. destruct Hent as (e0 & E0 & C0 & _).
    unfold ent in E0. rewrite Ez in E0. injection E0 as <-. cbn in Ec. congruence.
  - left. exists e. auto.
Qed.

Lemma seg_new : forall x, In x (icells (ai (cs s c) k)) -> seg (H'' x) t (f x).
Proof.
  intros x Ix. destruct (Hok x) as [Hin _]. destruct (Hin Ix) as (h1 & h2 & E1 & Hu & Fh & E2). rewrite E2.
  unfold f. fold u in Hu |- *. destruct (u x) as [v|] eqn:Eu.
  - destruct Hu as (h0 & g & ->). destruct g.
    + assert (Iv : In (v, true) (hs s x)) by (rewrite E1; apply in_app_iff; left; apply in_app_iff; right; left; reflexivity).
      destruct (w_bet Fk Good sw s sA K x v Iv) as (fv & Sv & Sg). cbn [pi]. rewrite Sv.
      assert (Ne : forall X Y, hs s x = X ++ (v, true) :: Y -> X = h0 /\ Y = h2).
      { intros X Y E. rewrite E1 in E. rewrite <- app_assoc in E. simpl in E.
        assert (N : NoDup (ids (h0 ++ (v, true) :: h2))) by (pose proof (w_nodup Fk Good sw s sA K x) as N; rewrite E1, <- app_assoc in N; exact N).
        destruct (nodup_place h0 h2 X Y v true true N E) as (A1 & _ & A2). auto. }
      destruct (fv x) as [u0|] eqn:Fu; cbn in Sg |- *.
      * destruct Sg as (A & B & C & E & Al).
        assert (E' : hs s x = (A ++ (u0, false) :: B) ++ (v, true) :: C) by (rewrite E; rewrite <- app_assoc; reflexivity).
        destruct (Ne _ _ E') as [<- <-]. exists A, (B ++ [(v, true)]), C. split.
        -- repeat (rewrite <- app_assoc; simpl). reflexivity.
        -- apply allt_app. split; [exact Al|constructor; [reflexivity|constructor]].
      * destruct Sg as (B & C & E & Al). destruct (Ne _ _ E) as [<- <-]. exists (B ++ [(v, true)]), C. split.
        -- rewrite <- app_assoc. reflexivity.
        -- apply allt_app. split; [exact Al|constructor; [reflexivity|constructor]].
    + assert (Iv : In (v, false) (hs s x)) by (rewrite E1; apply in_app_iff; left; apply in_app_iff; right; left; reflexivity).
      destruct (r_kept sw s sA R x v Iv) as [Sv _]. cbn [pi]. rewrite Sv. cbn. exists h0, [], h2. split.
      * rewrite <- app_assoc. reflexivity.
      * constructor.
  - subst h1. cbn. exists [], h2. split; [reflexivity|constructor].
Qed.

Theorem KR_wb : KR Fk Good sw' s' sA.
Proof.
  constructor.
  - rewrite (k_len Fk Good sw s sA K). unfold s', wbst. cbv zeta. cbn [lg]. unfold setew. rewrite length_map. reflexivity.
  - intros t' eA EA. destruct (k_ent Fk Good sw s sA K t' eA EA) as (eW & EW & (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10)).
    exists (sete t eW). rewrite ent_wb, EW. split; [reflexivity|].
    unfold sete. destruct (Nat.eqb (et eW) t) eqn:Ee; cbn [et ec ek eC eR eh erf ew].
    + apply (et_t t' eW EW) in Ee. subst t'. pose proof (HewA eA EA) as Wa.
      refine (conj S1 (conj S2 (conj S3 (conj S4 (conj S5 (conj S6 (conj _ (conj _ (conj _ _))))))))).
      * intros x. cbn [erf]. rewrite S7. destruct (erf eW x) as [w0|] eqn:Ew; [|reflexivity].
        unfold sw'; rewrite pi_upd; [reflexivity|]. intros E0. rewrite E0 in Ew. exact (Hfresh x (S8 x t Ew)).
      * intros x w0 Ew. cbn [erf] in Ew. exact (hs_old x w0 (S8 x w0 Ew)).
      * intros Z. rewrite Wa in Z. discriminate.
      * unfold sw'. rewrite upd_eq. discriminate.
    + assert (Nt : t' <> t) by (intros Z; apply (et_t t' eW EW) in Z; congruence).
      refine (conj S1 (conj S2 (conj S3 (conj S4 (conj S5 (conj S6 (conj _ (conj _ (conj _ _))))))))).
      * intros x. cbn [erf]. rewrite S7. destruct (erf eW x) as [w0|] eqn:Ew; [|reflexivity].
        unfold sw'; rewrite pi_upd; [reflexivity|]. intros E0. rewrite E0 in Ew. exact (Hfresh x (S8 x t Ew)).
      * intros x w0 Ew. cbn [erf] in Ew. exact (hs_old x w0 (S8 x w0 Ew)).
      * unfold sw'. rewrite upd_neq by exact Nt. exact S9.
      * unfold sw'. rewrite upd_neq by exact Nt. exact S10.
  - intros HF t' eA eW' EA EW' Gt. rewrite ent_wb in EW'. destruct (ent s t') as [eW|] eqn:EW; [|discriminate].
    cbn in EW'. injection EW' as <-. intros z Z. apply cov_wb.
    assert (Q : eQ (sete t eW) = eQ eW) by (unfold sete; destruct (Nat.eqb (et eW) t); reflexivity). rewrite Q.
    exact (k_eQ Fk Good sw s sA K HF t' eA eW EA EW Gt z Z).
  - intros HF c' z Z. apply (cov_mono s' (vP (cs s c'))); [exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (cs_wb_f c'))))))) |].
    apply cov_wb. exact (k_P Fk Good sw s sA K HF c' z Z).
  - intros HF c' z Z. destruct (cs_wb_f c') as (_ & _ & _ & _ & EA & _). rewrite EA. apply cov_wb. exact (k_A Fk Good sw s sA K HF c' z Z).
  - intros HF c' z Z. destruct (cs_wb_f c') as (_ & _ & _ & _ & _ & EO & _). rewrite EO. apply cov_wb. exact (k_Og Fk Good sw s sA K HF c' z Z).
  - intros HF z Z. apply cov_wb. exact (k_G Fk Good sw s sA K HF z Z).
  - intros HF y x I z Z. destruct (k_wc Fk Good sw s sA K HF y x I z Z) as [E|P]; [left; exact E|right; exact (pth_wb z y P)].
  - intros x w I. rewrite hs_wb in I. destruct (enters_tied_cell _ _ _ _ _ x Hok) as [E|(h1 & h2 & E1 & E2 & Fh & _)].
    + rewrite E in I. destruct (w_bet Fk Good sw s sA K x w I) as (fw & Sw & Sg). exists fw. unfold sw'.
      rewrite upd_neq; [split; [exact Sw|rewrite hs_wb, E; exact Sg]|].
      intros ->. apply (Hfresh x). unfold ids. apply in_map_iff. exists (t, true). auto.
    + rewrite E2 in I. apply in_app_iff in I. destruct I as [I|[I|I]].
      2: { injection I as <-. exists f. unfold sw'. rewrite upd_eq. split; [reflexivity|]. rewrite hs_wb.
           apply seg_new. destruct (in_dec Nat.eq_dec x (icells (ai (cs s c) k))) as [Ix|Nx]; [exact Ix|].
           exfalso. destruct (Hok x) as [_ H2]. rewrite (H2 Nx) in E2. rewrite E1 in E2.
           apply (f_equal (@length (nat * bool))) in E2. rewrite !length_app in E2. simpl in E2. lia. }
      all: assert (I' : In (w, true) (hs s x)) by (rewrite E1; apply in_app_iff; tauto).
      all: destruct (w_bet Fk Good sw s sA K x w I') as (fw & Sw & Sg); exists fw; unfold sw'.
      all: (rewrite upd_neq; [split; [exact Sw|rewrite hs_wb, E2; rewrite E1 in Sg; apply seg_ins_t; exact Sg]|]).
      all: intros ->; apply (Hfresh x); unfold ids; apply in_map_iff; exists (t, true); auto.
  - intros x. rewrite hs_wb. destruct (enters_tied_cell _ _ _ _ _ x Hok) as [E|(h1 & h2 & E1 & E2 & _)].
    + rewrite E. exact (w_nodup Fk Good sw s sA K x).
    + rewrite E2. apply ids_ins_nodup; rewrite <- E1; [exact (w_nodup Fk Good sw s sA K x)|exact (Hfresh x)].
  - intros c' z Z. destruct (ownw_wb c' z Z) as [O|(-> & ->)].
    + exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (cs_wb_f c')))))) z (w_OW Fk Good sw s sA K c' z O)).
    + rewrite cs_wb, Nat.eqb_refl. cbn. right. reflexivity.
  - intros tf g' E F. rewrite ent_wb in E. destruct (ent s tf) as [g|] eqn:Eg; [|discriminate]. cbn in E. injection E as <-.
    assert (H1 : ec (sete t g) = ec g) by (unfold sete; destruct (Nat.eqb (et g) t); auto).
    assert (H2 : ek (sete t g) = ek g) by (unfold sete; destruct (Nat.eqb (et g) t); auto).
    assert (H3 : eP (sete t g) = eP g) by (unfold sete; destruct (Nat.eqb (et g) t); auto). assert (F' : isFF s tf g) by (unfold isFF in *; rewrite H1, H2 in F; apply isFF_wb; exact F).
    rewrite H1, H3. destruct (w_OGP Fk Good sw s sA K tf g Eg F') as [A1 A2].
    destruct (cs_wb_f (ec g)) as (_ & _ & _ & _ & _ & EO & SP). rewrite EO. split; [exact A1|].
    intros z Z. apply SP. exact (A2 z Z).
  - intros tf g' z E F O L. rewrite ent_wb in E. destruct (ent s tf) as [g|] eqn:Eg; [|discriminate]. cbn in E. injection E as <-.
    assert (H1 : ec (sete t g) = ec g) by (unfold sete; destruct (Nat.eqb (et g) t); auto).
    assert (H2 : ek (sete t g) = ek g) by (unfold sete; destruct (Nat.eqb (et g) t); auto).
    assert (H3 : eP (sete t g) = eP g) by (unfold sete; destruct (Nat.eqb (et g) t); auto).
    assert (F' : isFF s tf g) by (unfold isFF in *; rewrite H1, H2 in F; apply isFF_wb; exact F).
    rewrite H3. rewrite H1 in O. destruct (ownw_wb (ec g) z O) as [O'|(-> & Ec)].
    + exact (w_OWG Fk Good sw s sA K tf g z Eg F' O' L).
    + exfalso. pose proof (Hff tf g Eg F' Ec). lia.
  - intros c' j t1 Oh Sw. destruct (cs_wb_f c') as (Oc & Oh' & _ & Rg & _). rewrite Oc, Rg. rewrite Oh' in Oh. rewrite pcs_wb.
    unfold sw' in Sw. destruct (Nat.eqb_spec t1 t) as [->|N].
    + destruct (Hoh c' j Oh) as (-> & -> & H1 & H2). auto.
    + rewrite upd_neq in Sw by exact N. exact (w_WBOC Fk Good sw s sA K c' j t1 Oh Sw).
  - intros t' f' Sw. rewrite ent_wb. unfold sw' in Sw. destruct (Nat.eqb_spec t' t) as [->|N].
    + destruct Hent as (e & E & Ec & Ek). exists (sete t e). rewrite E. split; [reflexivity|].
      assert (H1 : ec (sete t e) = ec e) by (unfold sete; destruct (Nat.eqb (et e) t); auto).
      assert (H2 : ek (sete t e) = ek e) by (unfold sete; destruct (Nat.eqb (et e) t); auto).
      rewrite H1, H2, Ec, Ek. destruct (cs_wb_f c) as (_ & _ & Ai & _). rewrite Ai. exact Hcas.
    + rewrite upd_neq in Sw by exact N. destruct (w_swc Fk Good sw s sA K t' f' Sw) as (e & E & C). exists (sete t e). rewrite E.
      split; [reflexivity|].
      assert (H1 : ec (sete t e) = ec e) by (unfold sete; destruct (Nat.eqb (et e) t); auto).
      assert (H2 : ek (sete t e) = ek e) by (unfold sete; destruct (Nat.eqb (et e) t); auto).
      rewrite H1, H2. destruct (cs_wb_f (ec e)) as (_ & _ & Ai & _). rewrite Ai. exact C.
  - intros t' e' E W'. rewrite ent_wb in E. destruct (ent s t') as [e|] eqn:Ee; [|discriminate]. cbn in E. injection E as <-.
    assert (H1 : ec (sete t e) = ec e) by (unfold sete; destruct (Nat.eqb (et e) t); auto).
    assert (H2 : ek (sete t e) = ek e) by (unfold sete; destruct (Nat.eqb (et e) t); auto).
    rewrite H1, H2. unfold tmo. destruct (cs_wb_f (ec e)) as (Oc & Oh & _). rewrite Oc, Oh. fold (tmo (cs s (ec e)) (ek e)).
    unfold sete in W'. destruct (Nat.eqb (et e) t) eqn:Et.
    + apply (et_t t' e Ee) in Et. subst t'. destruct Hent as (e0 & E0 & C0 & K0). rewrite Ee in E0. injection E0 as <-.
      rewrite C0, K0. exact Htmo.
    + exact (w_tmo Fk Good sw s sA K t' e Ee W').
Qed.
End Patch.
