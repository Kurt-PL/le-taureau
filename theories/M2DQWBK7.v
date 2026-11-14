(* Part 7: an access or fence performed and logged (in order, early, or the write of
   a CAS whose read happened alone) keeps KR. *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB M2DQWBK1 M2DQWBK2 M2DQWBK3 M2DQWBK4 M2DQWBK5 M2DQWBK6.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQShim.

Definition evsx (s : st) (c k : nat) (i : instr) (m' : mst) (a : val) (K : view) (u : cell -> option nat)
    (w : bool) (B : nat -> bool) (pc' tp' : nat -> nat) (cm' : list (nat * nat * nat))
    (es' : nat -> option (cst * nat * nat * (nat -> bool))) : st :=
  let cc := cs s c in
  mkS (S (tm s))
      (upd (cs s) c (mkC (upd (oc cc) k (Some (tm s))) (upd (rg cc) k a) (upd (ai cc) k i)
                         (upd (rw cc) k (wrote (tm s) (icells i) u w)) (upd (rv cc) k (rdval (mof s c) u)) B
                         (mP m') (mA m') (mR m')
                         (newO s c i (mof s c) m' (vO cc)) (newOg i m' (vOg cc)) (oh cc) (fx cc)))
      (mV m') (mC m') (mH m') (mG m') pc' tp' cm'
      (lg s ++ [mkO (tm s) c k K u w (evC i (rg cc)) (evR i (rg cc)) (evQ s c i (rg cc) (mof s c) (vOg cc) (vO cc) u w)
                    (evQc i (rg cc) (vO cc) w) false]) es'.

Lemma eff_evC : forall t i r m m' a K u w, eff t i r m m' a K u w -> w = true ->
  evC i r = icells i /\ places (mH m) (icells i) t (mH m').
Proof.
  intros t i r m m' a K u w H W. inversion H; subst; try discriminate; cbn; unfold evC, icond, ieval; cbn;
    match goal with Hc : ?c r = true |- _ => rewrite Hc end; cbn; split; auto.
Qed.

Lemma eff_histw : forall t i r m m' a K u w, eff t i r m m' a K u w ->
  (w = false -> mH m' = mH m) /\ (w = true -> exists xs, places (mH m) xs t (mH m')).
Proof. intros t i r m m' a K u w H. inversion H; subst; cbn; split; intros Z; try discriminate; eauto. Qed.

Lemma cs_upd : forall (f : nat -> cst) c v c', upd f c v c' = if Nat.eqb c' c then v else f c'.
Proof. reflexivity. Qed.

Section Evs.
Set Default Proof Using "All".
Variables (p : prog) (Fk : Prop) (Good : nat -> Prop) (sw : nat -> option (cell -> option nat)) (sW sA : st).
Variables (c k kA : nat) (i iA : instr) (m' m'A : mst) (a : val) (K KA : view) (u uA : cell -> option nat) (w : bool).
Variables (B BA : nat -> bool) (pc' pcA tp' tpA : nat -> nat) (cm' cmA : list (nat * nat * nat)).
Variables (es' esA : nat -> option (cst * nat * nat * (nat -> bool))).
Hypothesis RA : run p sA.
Hypothesis R : rel sw sW sA.
Hypothesis KK : KR Fk Good sw sW sA.
Hypothesis Ek : kA = k.
Hypothesis Ei : iA = i.
Hypothesis HW : eff (tm sW) i (rg (cs sW c)) (mof sW c) m' a K u w.
Hypothesis HA : eff (tm sA) iA (rg (cs sA c)) (mof sA c) m'A a KA uA w.
Hypothesis Hu : forall x, uA x = pi sw x (u x).
Hypothesis Htk : forall x w', u x = Some w' -> In w' (ids (hs sW x)).
Hypothesis Hoc : oc (cs sW c) k = None.
Hypothesis Hpk : pcs sW c <= k.
Hypothesis Hohv : oh (cs sW c) k <> None -> vok (rg (cs sW c) k) = true.
Hypothesis Hpc1 : forall c', pcs sW c' <= pc' c'.
Hypothesis Hpc2 : forall c' j, j < pc' c' -> j < pcs sW c' \/ (c' = c /\ j = k).
Hypothesis FH : forall x h1 h2, hs sW x = h1 ++ h2 -> mH m' x = h1 ++ (tm sW, false) :: h2 -> free_head h2.
Hypothesis HG1 : Fk -> Good (tm sW) -> LFB sW c (tm sW).
Hypothesis HG2 : Fk -> w = true -> evC i (rg (cs sW c)) <> [] -> Good (tm sW).

Local Abbreviation sW' := (evsx sW c k i m' a K u w B pc' tp' cm' es').
Local Abbreviation sA' := (evsx sA c kA iA m'A a KA uA w BA pcA tpA cmA esA).
Local Abbreviation eWn := (mkO (tm sW) c k K u w (evC i (rg (cs sW c))) (evR i (rg (cs sW c)))
             (evQ sW c i (rg (cs sW c)) (mof sW c) (vOg (cs sW c)) (vO (cs sW c)) u w) (evQc i (rg (cs sW c)) (vO (cs sW c)) w) false).
Local Abbreviation eAn := (mkO (tm sA) c kA KA uA w (evC iA (rg (cs sA c))) (evR iA (rg (cs sA c)))
             (evQ sA c iA (rg (cs sA c)) (mof sA c) (vOg (cs sA c)) (vO (cs sA c)) uA w) (evQc iA (rg (cs sA c)) (vO (cs sA c)) w) false).

Lemma TA : tm sA = tm sW. Proof. exact (r_tm sw sW sA R). Qed.
Lemma TWl : tm sW = length (lg sW). Proof. exact (tmW p Fk Good sw sW sA RA R KK). Qed.
Lemma TAl : tm sA = length (lg sA). Proof. exact (i_tm p sA (Inv1_run p sA RA)). Qed.
Lemma Rg : rg (cs sA c) = rg (cs sW c). Proof. exact (proj1 (proj2 (proj2 (proj2 (crel_eq p Fk Good sw sW sA RA R KK c))))). Qed.

Lemma entW' : forall t e, ent sW' t = Some e -> (t < tm sW /\ ent sW t = Some e) \/ (t = tm sW /\ e = eWn).
Proof.
  intros t e E. unfold ent, evsx in E. cbv zeta in E. cbn [lg] in E. destruct (ent_app _ _ _ _ E) as [(E1 & L)|(E1 & E2)].
  - left. rewrite TWl. unfold ent. auto.
  - right. split; [rewrite TWl; exact E1|exact E2].
Qed.
Lemma entW'_old : forall t e, ent sW t = Some e -> ent sW' t = Some e.
Proof. intros t e E. unfold ent, evsx. cbv zeta. cbn [lg]. apply app_ent. exact E. Qed.
Lemma entW'_new : ent sW' (tm sW) = Some eWn.
Proof. unfold ent, evsx. cbv zeta. cbn [lg]. rewrite nth_error_app_last, <- TWl, Nat.ltb_irrefl, Nat.eqb_refl. reflexivity. Qed.
Lemma entA' : forall t e, ent sA' t = Some e -> (t < tm sA /\ ent sA t = Some e) \/ (t = tm sA /\ e = eAn).
Proof.
  intros t e E. unfold ent, evsx in E. cbv zeta in E. cbn [lg] in E. destruct (ent_app _ _ _ _ E) as [(E1 & L)|(E1 & E2)].
  - left. rewrite TAl. unfold ent. auto.
  - right. split; [rewrite TAl; exact E1|exact E2].
Qed.

Lemma csW' : forall c', cs sW' c' = if Nat.eqb c' c then
  mkC (upd (oc (cs sW c)) k (Some (tm sW))) (upd (rg (cs sW c)) k a) (upd (ai (cs sW c)) k i)
      (upd (rw (cs sW c)) k (wrote (tm sW) (icells i) u w)) (upd (rv (cs sW c)) k (rdval (mof sW c) u)) B
      (mP m') (mA m') (mR m') (newO sW c i (mof sW c) m' (vO (cs sW c))) (newOg i m' (vOg (cs sW c))) (oh (cs sW c)) (fx (cs sW c))
  else cs sW c'.
Proof. intros c'. reflexivity. Qed.
Lemma csA' : forall c', cs sA' c' = if Nat.eqb c' c then
  mkC (upd (oc (cs sA c)) kA (Some (tm sA))) (upd (rg (cs sA c)) kA a) (upd (ai (cs sA c)) kA iA)
      (upd (rw (cs sA c)) kA (wrote (tm sA) (icells iA) uA w)) (upd (rv (cs sA c)) kA (rdval (mof sA c) uA)) BA
      (mP m'A) (mA m'A) (mR m'A) (newO sA c iA (mof sA c) m'A (vO (cs sA c))) (newOg iA m'A (vOg (cs sA c))) (oh (cs sA c)) (fx (cs sA c))
  else cs sA c'.
Proof. intros c'. reflexivity. Qed.

Lemma grW : grows sW sW'.
Proof.
  unfold grows. destruct (eff_hist _ _ _ _ _ _ _ _ _ HW) as [Eh|(xs0 & P)]; cbn [mH mof] in *.
  - split; [|split]; intros; unfold evsx; cbv zeta; cbn [hs]; [rewrite Eh; assumption|rewrite Eh; assumption|apply entW'_old; assumption].
  - split; [|split]; intros; unfold evsx; cbv zeta; cbn [hs];
      [exact (places_older _ _ _ _ _ _ _ P ltac:(eassumption))|exact (places_ids _ _ _ _ _ _ P ltac:(eassumption))|apply entW'_old; assumption].
Qed.
Lemma GW : forall a0 b0, gedge sW a0 b0 -> gedge sW' a0 b0.
Proof. exact (grows_gedge _ _ grW). Qed.
Lemma CW : forall V, vsub (cov sW V) (cov sW' V).
Proof. apply cov_grow. exact GW. Qed.
Lemma PW : forall a0 b0, Pth sW a0 b0 -> Pth sW' a0 b0.
Proof.
  intros a0 b0 P. unfold Pth in *. induction P as [a1 b1 G|a1 b1 c1 _ IH1 _ IH2];
    [constructor; exact (GW a1 b1 G)|exact (t_trans _ _ a1 b1 c1 IH1 IH2)].
Qed.

Lemma hsW' : forall x, hs sW' x = mH m' x. Proof. reflexivity. Qed.
Lemma hsA' : forall x, hs sA' x = mH m'A x. Proof. reflexivity. Qed.

Lemma effK_here : Fk -> vsub (mP m'A) (cov sW' (mP m')) /\ vsub (mA m'A) (cov sW' (mA m')) /\ vsub (mG m'A) (cov sW' (mG m')).
Proof.
  intros HF. pose proof HA as HA'. rewrite TA, Ei, Rg in HA'. apply (effK sW' (tm sW) i (rg (cs sW c)) (mof sW c) (mof sA c) m' m'A a K KA u uA w HW HA').
  - intros z Z. apply CW. exact (k_P Fk Good sw sW sA KK HF c z Z).
  - intros z Z. apply CW. exact (k_A Fk Good sw sW sA KK HF c z Z).
  - intros z Z. apply CW. exact (k_G Fk Good sw sW sA KK HF z Z).
  - intros z Z. exact (ownw_AW p Fk Good sw sW sA RA R KK c z Z).
  - exact (srcs_cov p Fk Good sw sW sA RA R KK HF sW' u uA GW Hu Htk).
  - exact (carr_cov p Fk Good sw sW sA RA R KK HF sW' c u uA GW Hu Htk).
Qed.

(* a slot with a read half that is written back is not where an access is performed now *)
Lemma no_wb_k : forall t1, oh (cs sW c) k = Some t1 -> sw t1 = None.
Proof.
  intros t1 Oh. destruct (sw t1) as [f|] eqn:S; [|reflexivity]. exfalso.
  destruct (w_WBOC Fk Good sw sW sA KK c k t1 Oh ltac:(congruence)) as [_ [L|V]]; [lia|].
  rewrite (Hohv ltac:(congruence)) in V. discriminate.
Qed.

(* an entry at slot (c, k) is a read half that is not written back *)
Lemma ent_k : forall t e, ent sW t = Some e -> ec e = c -> ek e = k -> eh e = true /\ oh (cs sW c) k = Some t /\ sw t = None.
Proof.
  intros t e E Ec Ek'. destruct (i_etW p Fk Good sw sW sA RA R KK t e E) as [_ O]. rewrite Ec, Ek' in O.
  destruct (eh e) eqn:Eh; [|congruence]. split; [reflexivity|]. split; [exact O|exact (no_wb_k t O)].
Qed.

Lemma isFF_back : forall tf f, ent sW tf = Some f -> isFF sW' tf f -> isFF sW tf f.
Proof.
  intros tf f E (Fa & Fp & Fo). rewrite csW' in Fa, Fo. unfold evsx in Fp. cbn [pcs] in Fp.
  assert (Lt : tf < tm sW) by exact (ent_ltW p Fk Good sw sW sA RA R KK tf f E).
  destruct (Nat.eqb_spec (ec f) c) as [Ec|Nc]; cbn [oc ai] in Fa, Fo.
  - destruct (Nat.eqb_spec (ek f) k) as [Ek'|Nk].
    + exfalso. rewrite Ek', upd_eq in Fo. injection Fo as Fo. lia.
    + rewrite upd_neq in Fa by exact Nk. rewrite upd_neq in Fo by exact Nk. unfold isFF. rewrite Ec. rewrite Ec in Fp.
      destruct (Hpc2 c (ek f) Fp) as [L|[_ L]]; [|congruence]. auto.
  - unfold isFF. destruct (Hpc2 (ec f) (ek f) Fp) as [L|[L _]]; [|congruence]. auto.
Qed.

Lemma vP_mono : forall c', vsub (vP (cs sW c')) (vP (cs sW' c')).
Proof.
  intros c'. rewrite csW'. destruct (Nat.eqb_spec c' c) as [->|N]; cbn [vP]; [|intros z Z; exact Z].
  exact (eff_Pmono _ _ _ _ _ _ _ _ _ HW).
Qed.
Lemma ownw_back : forall c' z, ownw sW' c' z -> z < tm sW -> ownw sW c' z.
Proof.
  intros c' z (e & E & Ec & Ew) L. destruct (entW' z e E) as [(_ & E')|(Z & _)]; [exists e; auto|lia].
Qed.

Lemma newOg_sup : forall X, vsub (vP (cs sW c)) (mP m') -> vsub X (vOg (cs sW c)) -> vsub X (vP (cs sW c)) ->
  vsub X (newOg i m' (vOg (cs sW c))).
Proof.
  intros X HP HO HV. destruct i as [| | |[]|]; cbn; auto; intros z Z; [left; apply HO; exact Z|apply HP; apply HV; exact Z].
Qed.

Lemma ksame_grow : forall t eA eW, ksame sw sW t eA eW -> ksame sw sW' t eA eW.
Proof.
  intros t eA eW (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
  refine (conj S1 (conj S2 (conj S3 (conj S4 (conj S5 (conj S6 (conj S7 (conj _ (conj S9 S10))))))))).
  intros x w0 E. destruct grW as (_ & HI & _). apply HI. exact (S8 x w0 E).
Qed.

Theorem KR_evs : KR Fk Good sw sW' sA'.
Proof.
  constructor.
  - unfold evsx. cbv zeta. cbn [lg]. rewrite !length_app. rewrite (k_len Fk Good sw sW sA KK). reflexivity.
  - intros t eA EA. destruct (entA' t eA EA) as [(Lt & EA0)|(-> & ->)].
    + destruct (k_ent Fk Good sw sW sA KK t eA EA0) as (eW & EW & S). exists eW. split; [exact (entW'_old t eW EW)|exact (ksame_grow t eA eW S)].
    + exists eWn. rewrite TA. split; [exact entW'_new|]. rewrite Ek, Ei, Rg.
      repeat split; cbn [et ec ek eC eR eh erf ew]; auto.
      * intros x w0 E. destruct grW as (_ & HI & _). apply HI. exact (Htk x w0 E).
      * exact (i_sw sw sW sA R (tm sW) (le_n _)).
  - intros HF t eA eW EA EW Gt. destruct (entA' t eA EA) as [(Lt & EA0)|(Et & ->)].
    + destruct (entW' t eW EW) as [(_ & EW0)|(Z & _)]; [|rewrite TA in Lt; lia].
      intros z Z. apply CW. exact (k_eQ Fk Good sw sW sA KK HF t eA eW EA0 EW0 Gt z Z).
    + rewrite TA in Et. subst t. destruct (entW' (tm sW) eW EW) as [(Z & _)|(_ & ->)]; [lia|].
      cbn [eQ]. rewrite Ei, Rg.
      exact (evQ_cov p Fk Good sw sW sA RA R KK HF sW' c i (rg (cs sW c)) u uA w GW Hu Htk (HG1 HF Gt)).
  - intros HF c' z Z. destruct (effK_here HF) as (KP & KA' & KG). rewrite csA' in Z. rewrite csW'. destruct (Nat.eqb_spec c' c) as [->|N]; cbn [vP] in *.
    + exact (KP z Z).
    + apply CW. exact (k_P Fk Good sw sW sA KK HF c' z Z).
  - intros HF c' z Z. destruct (effK_here HF) as (KP & KA' & KG). rewrite csA' in Z. rewrite csW'. destruct (Nat.eqb_spec c' c) as [->|N]; cbn [vA] in *.
    + exact (KA' z Z).
    + apply CW. exact (k_A Fk Good sw sW sA KK HF c' z Z).
  - intros HF c' z Z. destruct (effK_here HF) as (KP & KA' & KG). rewrite csA' in Z. rewrite csW'. destruct (Nat.eqb_spec c' c) as [->|N]; cbn [vOg] in *.
    + rewrite Ei in Z. apply (newOg_cov sW' i m' m'A (vOg (cs sA c)) (vOg (cs sW c)) KP KG); [|exact Z].
      intros y Y. apply CW. exact (k_Og Fk Good sw sW sA KK HF c y Y).
    + apply CW. exact (k_Og Fk Good sw sW sA KK HF c' z Z).
  - intros HF. destruct (effK_here HF) as (KP & KA' & KG). exact KG.
  - intros HF y x I z Z. rewrite hsA' in I. change (wc sA') with (mC m'A) in Z.
    destruct (eff_histw _ _ _ _ _ _ _ _ _ HA) as [H0 H1]. destruct (eff_C _ _ _ _ _ _ _ _ _ HA) as [C1 C0].
    assert (Wc : w = true \/ w = false) by (destruct w; auto). destruct Wc as [Ew|Ew].
    + destruct (H1 Ew) as (xs0 & P). rewrite (C1 Ew) in Z. cbn [mC mH mR mof] in Z, P.
      destruct (Nat.eq_dec y (tm sA)) as [->|Ny].
      * rewrite upd_eq in Z. destruct Z as [Z| ->]; [|left; reflexivity]. right.
        assert (Ne : evC i (rg (cs sW c)) <> []).
        { rewrite (proj1 (eff_evC _ _ _ _ _ _ _ _ _ HW Ew)). destruct (eff_evC _ _ _ _ _ _ _ _ _ HA Ew) as [_ PA].
          intros Ze. rewrite Ei, Ze in PA. destruct (PA x) as [_ PA2]. rewrite (PA2 (fun Q => Q)) in I. cbn [mH mof] in I.
          pose proof (tmA_ids sw sW sA R x (tm sA) ltac:(rewrite TA in I |- *; exact I)) as L. rewrite TA in L. lia. }
        assert (Gt : Good (tm sW)) by exact (HG2 HF Ew Ne).
        pose proof (R_og p Fk Good sw sW sA RA R KK HF c (HG1 HF Gt) z Z) as O.
        assert (InQ : forall y', vOg (cs sW c) y' -> eQ eWn y').
        { intros y' Y'. cbn [eQ]. unfold evQ. rewrite Ew. cbn. left. exact Y'. }
        assert (Ge : forall y', vOg (cs sW c) y' -> y' <> tm sW -> gedge sW' y' (tm sW)).
        { intros y' Y' N. right; right. exists eWn. split; [exact entW'_new|split; [exact (InQ y' Y')|exact N]]. }
        rewrite TA. destruct (k_Og Fk Good sw sW sA KK HF c z O) as [Oz|(y' & Oy & Pz)].
        -- destruct (Nat.eq_dec z (tm sW)) as [Ez|Nz].
           ++ exfalso. assert (Iw : isw sA z) by (apply (j_views p sA (proj2 (Inv2_run p sA RA)) c); right; right; left; exact Z).
              pose proof (isw_lt p sA z (Inv1_run p sA RA) Iw) as Lz. rewrite TA in Lz. lia.
           ++ constructor. exact (Ge z Oz Nz).
        -- destruct (Nat.eq_dec y' (tm sW)) as [->|Ny']; [exact (PW _ _ Pz)|].
           exact (t_trans _ _ _ _ _ (PW _ _ Pz) (t_step _ _ _ _ (Ge y' Oy Ny'))).
      * rewrite upd_neq in Z by exact Ny.
        assert (I' : In y (ids (hs sA x))).
        { destruct (places_cell _ _ _ _ x P) as [E|(h1 & h2 & E1 & E2)]; [rewrite <- E; exact I|].
          rewrite E2 in I. apply in_ids_ins in I. destruct I as [I|I]; [simpl in I; congruence|]. rewrite E1. exact I. }
        destruct (k_wc Fk Good sw sW sA KK HF y x I' z Z) as [E|Pz]; [left; exact E|right; exact (PW _ _ Pz)].
    + rewrite (H0 Ew) in I. rewrite (C0 Ew) in Z. cbn [mC mH mof] in I, Z.
      destruct (k_wc Fk Good sw sW sA KK HF y x I z Z) as [E|Pz]; [left; exact E|right; exact (PW _ _ Pz)].
  - intros x w0 I. rewrite hsW' in I. destruct (eff_hist _ _ _ _ _ _ _ _ _ HW) as [Eh|(xs0 & P)]; cbn [mH mof] in *.
    + rewrite Eh in I. destruct (w_bet Fk Good sw sW sA KK x w0 I) as (f & Sf & Sg). exists f. rewrite hsW', Eh. auto.
    + destruct (places_cell _ _ _ _ x P) as [E|(h1 & h2 & E1 & E2)].
      * rewrite E in I. destruct (w_bet Fk Good sw sW sA KK x w0 I) as (f & Sf & Sg). exists f. rewrite hsW', E. auto.
      * rewrite E2 in I. assert (I' : In (w0, true) (hs sW x)).
        { rewrite E1. apply in_app_iff in I. apply in_app_iff. destruct I as [I|[I|I]]; [left; exact I|discriminate|right; exact I]. }
        destruct (w_bet Fk Good sw sW sA KK x w0 I') as (f & Sf & Sg). exists f. split; [exact Sf|].
        rewrite hsW', E2. rewrite E1 in Sg. apply seg_ins_f; [exact Sg|]. exact (FH x h1 h2 E1 E2).
  - intros x. rewrite hsW'. destruct (eff_hist _ _ _ _ _ _ _ _ _ HW) as [Eh|(xs0 & P)]; cbn [mH mof] in *.
    + rewrite Eh. exact (w_nodup Fk Good sw sW sA KK x).
    + destruct (places_cell _ _ _ _ x P) as [E|(h1 & h2 & E1 & E2)]; [rewrite E; exact (w_nodup Fk Good sw sW sA KK x)|].
      rewrite E2. apply ids_ins_nodup; rewrite <- E1; [exact (w_nodup Fk Good sw sW sA KK x)|].
      intros J. pose proof (i_ids sw sW sA R x (tm sW) J). lia.
  - intros c' z O. destruct O as (e & E & Ec & Ew'). destruct (entW' z e E) as [(Lz & E0)|(-> & ->)].
    + apply vP_mono. apply (w_OW Fk Good sw sW sA KK c'). exists e. auto.
    + cbn [ec ew] in Ec, Ew'. rewrite <- Ec. rewrite csW', Nat.eqb_refl. cbn [vP]. exact (eff_wput _ _ _ _ _ _ _ _ _ HW Ew').
  - intros tf f E F. destruct (entW' tf f E) as [(Lt & E0)|(-> & ->)].
    + pose proof (isFF_back tf f E0 F) as F0. destruct (w_OGP Fk Good sw sW sA KK tf f E0 F0) as [O1 O2].
      rewrite csW'. destruct (Nat.eqb_spec (ec f) c) as [Ec|Nc]; cbn [vOg vP].
      * rewrite Ec in O1, O2. split.
        -- apply newOg_sup; [exact (eff_Pmono _ _ _ _ _ _ _ _ _ HW)|exact O1|exact O2].
        -- intros z Z. exact (eff_Pmono _ _ _ _ _ _ _ _ _ HW z (O2 z Z)).
      * auto.
    + destruct F as (Fa & _). rewrite csW', Nat.eqb_refl in Fa. cbn [ai ec ek] in Fa. rewrite upd_eq in Fa.
      pose proof HW as HW'. rewrite Fa in HW'. destruct (eff_ffK _ _ _ _ _ _ _ _ HW') as (EK & Em & _).
      cbn [ec eP]. rewrite csW', Nat.eqb_refl. cbn [vOg vP]. rewrite EK, Fa, Em. cbn [newOg mP gpost gpre].
      split; intros z Z; left; exact Z.
  - intros tf f z E F O L. destruct (entW' tf f E) as [(Lt & E0)|(-> & ->)].
    + pose proof (isFF_back tf f E0 F) as F0. apply (w_OWG Fk Good sw sW sA KK tf f z E0 F0); [|exact L].
      apply ownw_back; [exact O|lia].
    + destruct F as (Fa & _). rewrite csW', Nat.eqb_refl in Fa. cbn [ai ec ek] in Fa. rewrite upd_eq in Fa.
      pose proof HW as HW'. rewrite Fa in HW'. destruct (eff_ffK _ _ _ _ _ _ _ _ HW') as (EK & _ & _).
      cbn [ec eP] in *. rewrite EK. cbn. left. left.
      exact (w_OW Fk Good sw sW sA KK c z (ownw_back c z O L)).
  - intros c' j t1 Oh Sw. rewrite csW' in Oh |- *. unfold evsx. cbn [pcs]. destruct (Nat.eqb_spec c' c) as [->|N]; cbn [oh oc rg] in *.
    + destruct (Nat.eqb_spec j k) as [->|Nj].
      * exfalso. apply Sw. exact (no_wb_k t1 Oh).
      * rewrite !upd_neq by exact Nj. destruct (w_WBOC Fk Good sw sW sA KK c j t1 Oh Sw) as [A1 [A2|A2]]; split; auto.
        left. pose proof (Hpc1 c). lia.
    + destruct (w_WBOC Fk Good sw sW sA KK c' j t1 Oh Sw) as [A1 [A2|A2]]; split; auto. left. pose proof (Hpc1 c'). lia.
  - intros t f Sw. destruct (w_swc Fk Good sw sW sA KK t f Sw) as (e & E & Cc). exists e. split; [exact (entW'_old t e E)|].
    rewrite csW'. destruct (Nat.eqb_spec (ec e) c) as [Ec|Nc]; cbn [ai]; [|exact Cc].
    destruct (Nat.eqb_spec (ek e) k) as [Ek'|Nk].
    + exfalso. destruct (ent_k t e E Ec Ek') as (_ & _ & S). congruence.
    + rewrite upd_neq by exact Nk. rewrite <- Ec. exact Cc.
  - intros t e E W'. destruct (entW' t e E) as [(Lt & E0)|(-> & ->)].
    + pose proof (w_tmo Fk Good sw sW sA KK t e E0 W') as T. rewrite csW'. unfold tmo in *.
      destruct (Nat.eqb_spec (ec e) c) as [Ec|Nc]; cbn [oc oh]; [|exact T].
      destruct (Nat.eqb_spec (ek e) k) as [Ek'|Nk].
      * exfalso. destruct (ent_k t e E0 Ec Ek') as (Hh & _ & S).
        destruct (entW p Fk Good sw sW sA RA R KK t e E0) as (eA & EA & (_ & _ & _ & _ & _ & S6 & _ & _ & _ & S10)).
        rewrite (S10 S) in W'. destruct (j_ew p sA (proj2 (Inv2_run p sA RA)) t eA _ EA eq_refl) as [J _].
        rewrite J, S6, Hh in W'. discriminate.
      * rewrite !upd_neq by exact Nk. rewrite <- Ec. exact T.
    + cbn [ec ek]. rewrite csW', Nat.eqb_refl. unfold tmo. cbn [oc]. rewrite upd_eq. reflexivity.
Qed.
End Evs.
