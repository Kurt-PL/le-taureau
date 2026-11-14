(* Part 8: a CAS's read alone keeps KR; so does a step that logs nothing. *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB M2DQWBK1 M2DQWBK2 M2DQWBK3 M2DQWBK4 M2DQWBK5 M2DQWBK6 M2DQWBK7.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQShim.

Section Rd.
Set Default Proof Using "All".
Variables (p : prog) (Fk : Prop) (Good : nat -> Prop) (sw : nat -> option (cell -> option nat)) (sW sA : st).
Variables (c k kA : nat) (xs : list cell) (m' m'A : mst) (a : val) (K KA : view) (u uA : cell -> option nat) (w bv : bool).
Variables (B BA : nat -> bool).
Hypothesis RA : run p sA.
Hypothesis R : rel sw sW sA.
Hypothesis KK : KR Fk Good sw sW sA.
Hypothesis Ek : kA = k.
Hypothesis HW : eff (tm sW) (ILd Plain xs (fun _ => true)) (rg (cs sW c)) (mof sW c) m' a K u w.
Hypothesis HA : eff (tm sA) (ILd Plain xs (fun _ => true)) (rg (cs sA c)) (mof sA c) m'A a KA uA w.
Hypothesis Hu : forall x, uA x = pi sw x (u x).
Hypothesis Htk : forall x w', u x = Some w' -> In w' (ids (hs sW x)).
Hypothesis Hoc : oc (cs sW c) k = None.
Hypothesis Hoh : oh (cs sW c) k = None.
Hypothesis HG1 : Fk -> Good (tm sW) -> LFB sW c (tm sW).

Local Abbreviation i := (ILd Plain xs (fun _ => true)).
Local Abbreviation sW' := (sread sW c k Plain xs B m' a K u w bv).
Local Abbreviation sA' := (sread sA c kA Plain xs BA m'A a KA uA w bv).
Local Abbreviation eWn := (mkO (tm sW) c k K u w (evC i (rg (cs sW c))) (evR i (rg (cs sW c)))
             (evQ sW c i (rg (cs sW c)) (mof sW c) (vOg (cs sW c)) (vO (cs sW c)) u w) (evQc i (rg (cs sW c)) (vO (cs sW c)) w) true).
Local Abbreviation eAn := (mkO (tm sA) c kA KA uA w (evC i (rg (cs sA c))) (evR i (rg (cs sA c)))
             (evQ sA c i (rg (cs sA c)) (mof sA c) (vOg (cs sA c)) (vO (cs sA c)) uA w) (evQc i (rg (cs sA c)) (vO (cs sA c)) w) true).

Lemma Wf : w = false.
Proof. inversion HW; subst; auto; exfalso; unfold icond, ieval in *; cbn in *; discriminate. Qed.
Lemma HmW : mH m' = hs sW /\ mC m' = wc sW.
Proof. pose proof Wf as E. split; [exact (proj1 (eff_histw _ _ _ _ _ _ _ _ _ HW) E)|exact (proj2 (eff_C _ _ _ _ _ _ _ _ _ HW) E)]. Qed.
Lemma HmA : mH m'A = hs sA /\ mC m'A = wc sA.
Proof. pose proof Wf as E. split; [exact (proj1 (eff_histw _ _ _ _ _ _ _ _ _ HA) E)|exact (proj2 (eff_C _ _ _ _ _ _ _ _ _ HA) E)]. Qed.

Lemma TA' : tm sA = tm sW. Proof. exact (r_tm sw sW sA R). Qed.
Lemma TWl' : tm sW = length (lg sW). Proof. exact (tmW p Fk Good sw sW sA RA R KK). Qed.
Lemma TAl' : tm sA = length (lg sA). Proof. exact (i_tm p sA (Inv1_run p sA RA)). Qed.
Lemma Rg' : rg (cs sA c) = rg (cs sW c). Proof. exact (proj1 (proj2 (proj2 (proj2 (crel_eq p Fk Good sw sW sA RA R KK c))))). Qed.

Lemma entR : forall t e, ent sW' t = Some e -> (t < tm sW /\ ent sW t = Some e) \/ (t = tm sW /\ e = eWn).
Proof.
  intros t e E. unfold ent, sread in E. cbv zeta in E. cbn [lg] in E. destruct (ent_app _ _ _ _ E) as [(E1 & L)|(E1 & E2)].
  - left. rewrite TWl'. unfold ent. auto.
  - right. split; [rewrite TWl'; exact E1|exact E2].
Qed.
Lemma entR_old : forall t e, ent sW t = Some e -> ent sW' t = Some e.
Proof. intros t e E. unfold ent, sread. cbv zeta. cbn [lg]. apply app_ent. exact E. Qed.
Lemma entR_new : ent sW' (tm sW) = Some eWn.
Proof. unfold ent, sread. cbv zeta. cbn [lg]. rewrite nth_error_app_last, <- TWl', Nat.ltb_irrefl, Nat.eqb_refl. reflexivity. Qed.
Lemma entRA : forall t e, ent sA' t = Some e -> (t < tm sA /\ ent sA t = Some e) \/ (t = tm sA /\ e = eAn).
Proof.
  intros t e E. unfold ent, sread in E. cbv zeta in E. cbn [lg] in E. destruct (ent_app _ _ _ _ E) as [(E1 & L)|(E1 & E2)].
  - left. rewrite TAl'. unfold ent. auto.
  - right. split; [rewrite TAl'; exact E1|exact E2].
Qed.

Lemma csR : forall c', cs sW' c' = if Nat.eqb c' c then
  mkC (oc (cs sW c)) (upd (rg (cs sW c)) k (vd bv a)) (upd (ai (cs sW c)) k (crd Plain xs))
      (upd (rw (cs sW c)) k (wrote (tm sW) (icells i) u w)) (upd (rv (cs sW c)) k (rdval (mof sW c) u)) (bor (bd (cs sW c)) B)
      (mP m') (mA m') (mR m') (newO sW c i (mof sW c) m' (vO (cs sW c))) (newOg i m' (vOg (cs sW c)))
      (upd (oh (cs sW c)) k (Some (tm sW))) (fx (cs sW c))
  else cs sW c'.
Proof. intros c'. reflexivity. Qed.
Lemma csRA : forall c', cs sA' c' = if Nat.eqb c' c then
  mkC (oc (cs sA c)) (upd (rg (cs sA c)) kA (vd bv a)) (upd (ai (cs sA c)) kA (crd Plain xs))
      (upd (rw (cs sA c)) kA (wrote (tm sA) (icells i) uA w)) (upd (rv (cs sA c)) kA (rdval (mof sA c) uA)) (bor (bd (cs sA c)) BA)
      (mP m'A) (mA m'A) (mR m'A) (newO sA c i (mof sA c) m'A (vO (cs sA c))) (newOg i m'A (vOg (cs sA c)))
      (upd (oh (cs sA c)) kA (Some (tm sA))) (fx (cs sA c))
  else cs sA c'.
Proof. intros c'. reflexivity. Qed.

Lemma grR : grows sW sW'.
Proof.
  unfold grows. unfold sread. cbv zeta. cbn [hs]. destruct HmW as [Eh _]. rewrite Eh.
  split; [intros; assumption|split; [intros; assumption|intros; apply entR_old; assumption]].
Qed.
Lemma GR : forall a0 b0, gedge sW a0 b0 -> gedge sW' a0 b0.
Proof. exact (grows_gedge _ _ grR). Qed.
Lemma CR : forall V, vsub (cov sW V) (cov sW' V).
Proof. apply cov_grow. exact GR. Qed.
Lemma PR' : forall a0 b0, Pth sW a0 b0 -> Pth sW' a0 b0.
Proof.
  intros a0 b0 P. unfold Pth in *. induction P as [a1 b1 G|a1 b1 c1 _ IH1 _ IH2];
    [constructor; exact (GR a1 b1 G)|exact (t_trans _ _ a1 b1 c1 IH1 IH2)].
Qed.

Lemma effK_r : Fk -> vsub (mP m'A) (cov sW' (mP m')) /\ vsub (mA m'A) (cov sW' (mA m')) /\ vsub (mG m'A) (cov sW' (mG m')).
Proof.
  intros HF. pose proof HA as HA'. rewrite TA', Rg' in HA'. apply (effK sW' (tm sW) i (rg (cs sW c)) (mof sW c) (mof sA c) m' m'A a K KA u uA w HW HA').
  - intros z Z. apply CR. exact (k_P Fk Good sw sW sA KK HF c z Z).
  - intros z Z. apply CR. exact (k_A Fk Good sw sW sA KK HF c z Z).
  - intros z Z. apply CR. exact (k_G Fk Good sw sW sA KK HF z Z).
  - intros z Z. exact (ownw_AW p Fk Good sw sW sA RA R KK c z Z).
  - exact (srcs_cov p Fk Good sw sW sA RA R KK HF sW' u uA GR Hu Htk).
  - exact (carr_cov p Fk Good sw sW sA RA R KK HF sW' c u uA GR Hu Htk).
Qed.

(* no entry is at slot (c, k) yet *)
Lemma no_ent_k : forall t e, ent sW t = Some e -> ec e = c -> ek e = k -> False.
Proof.
  intros t e E Ec Ek'. destruct (i_etW p Fk Good sw sW sA RA R KK t e E) as [_ O]. rewrite Ec, Ek' in O.
  destruct (eh e); congruence.
Qed.

Lemma isFF_backR : forall tf f, isFF sW' tf f -> isFF sW tf f.
Proof.
  intros tf f (Fa & Fp & Fo). rewrite csR in Fa, Fo. unfold sread in Fp. cbn [pcs] in Fp.
  destruct (Nat.eqb_spec (ec f) c) as [Ec|Nc]; cbn [oc ai] in Fa, Fo.
  - destruct (Nat.eqb_spec (ek f) k) as [Ek'|Nk].
    + exfalso. rewrite Ek' in Fo. congruence.
    + rewrite upd_neq in Fa by exact Nk. unfold isFF. rewrite Ec. rewrite Ec in Fp. auto.
  - unfold isFF. auto.
Qed.

Lemma ownw_R : forall c' z, ownw sW' c' z -> ownw sW c' z.
Proof.
  intros c' z (e & E & Ec & Ew). destruct (entR z e E) as [(_ & E')|(_ & ->)]; [exists e; auto|].
  rewrite Wf in Ew. discriminate.
Qed.

Theorem KR_sread : KR Fk Good sw sW' sA'.
Proof.
  destruct HmW as [EhW EcW]. destruct HmA as [EhA EcA].
  constructor.
  - unfold sread. cbv zeta. cbn [lg]. rewrite !length_app. rewrite (k_len Fk Good sw sW sA KK). reflexivity.
  - intros t eA EA. destruct (entRA t eA EA) as [(Lt & EA0)|(-> & ->)].
    + destruct (k_ent Fk Good sw sW sA KK t eA EA0) as (eW & EW & (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10)).
      exists eW. split; [exact (entR_old t eW EW)|].
      refine (conj S1 (conj S2 (conj S3 (conj S4 (conj S5 (conj S6 (conj S7 (conj _ (conj S9 S10))))))))).
      intros x w0 E. unfold sread. cbv zeta. cbn [hs]. rewrite EhW. exact (S8 x w0 E).
    + exists eWn. rewrite TA'. split; [exact entR_new|]. rewrite Ek, Rg'.
      repeat split; cbn [et ec ek eC eR eh erf ew]; auto.
      * intros x w0 E. unfold sread. cbv zeta. cbn [hs]. rewrite EhW. exact (Htk x w0 E).
      * exact (i_sw sw sW sA R (tm sW) (le_n _)).
  - intros HF t eA eW EA EW Gt. destruct (entRA t eA EA) as [(Lt & EA0)|(Et & ->)].
    + destruct (entR t eW EW) as [(_ & EW0)|(Z & _)]; [|rewrite TA' in Lt; lia].
      intros z Z. apply CR. exact (k_eQ Fk Good sw sW sA KK HF t eA eW EA0 EW0 Gt z Z).
    + rewrite TA' in Et. subst t. destruct (entR (tm sW) eW EW) as [(Z & _)|(_ & ->)]; [lia|].
      cbn [eQ]. rewrite Rg'.
      exact (evQ_cov p Fk Good sw sW sA RA R KK HF sW' c i (rg (cs sW c)) u uA w GR Hu Htk (HG1 HF Gt)).
  - intros HF c' z Z. destruct (effK_r HF) as (KP & KA' & KG). rewrite csRA in Z. rewrite csR. destruct (Nat.eqb_spec c' c) as [->|N]; cbn [vP] in *.
    + exact (KP z Z).
    + apply CR. exact (k_P Fk Good sw sW sA KK HF c' z Z).
  - intros HF c' z Z. destruct (effK_r HF) as (KP & KA' & KG). rewrite csRA in Z. rewrite csR. destruct (Nat.eqb_spec c' c) as [->|N]; cbn [vA] in *.
    + exact (KA' z Z).
    + apply CR. exact (k_A Fk Good sw sW sA KK HF c' z Z).
  - intros HF c' z Z. destruct (effK_r HF) as (KP & KA' & KG). rewrite csRA in Z. rewrite csR. destruct (Nat.eqb_spec c' c) as [->|N]; cbn [vOg newOg] in *.
    + apply CR. exact (k_Og Fk Good sw sW sA KK HF c z Z).
    + apply CR. exact (k_Og Fk Good sw sW sA KK HF c' z Z).
  - intros HF. destruct (effK_r HF) as (KP & KA' & KG). exact KG.
  - intros HF y x I z Z. change (hs sA' x) with (mH m'A x) in I. change (wc sA') with (mC m'A) in Z. rewrite EhA in I. rewrite EcA in Z.
    destruct (k_wc Fk Good sw sW sA KK HF y x I z Z) as [E|Pz]; [left; exact E|right; exact (PR' _ _ Pz)].
  - intros x w0 I. change (hs sW' x) with (mH m' x) in I |- *. rewrite EhW in I |- *. exact (w_bet Fk Good sw sW sA KK x w0 I).
  - intros x. change (hs sW' x) with (mH m' x). rewrite EhW. exact (w_nodup Fk Good sw sW sA KK x).
  - intros c' z O. pose proof (ownw_R c' z O) as O'. pose proof (w_OW Fk Good sw sW sA KK c' z O') as V.
    rewrite csR. destruct (Nat.eqb_spec c' c) as [->|N]; cbn [vP]; [exact (eff_Pmono _ _ _ _ _ _ _ _ _ HW z V)|exact V].
  - intros tf f E F. destruct (entR tf f E) as [(Lt & E0)|(-> & ->)].
    + pose proof (isFF_backR tf f F) as F0. destruct (w_OGP Fk Good sw sW sA KK tf f E0 F0) as [O1 O2].
      rewrite csR. destruct (Nat.eqb_spec (ec f) c) as [Ec|Nc]; cbn [vOg vP newOg]; [|auto].
      rewrite Ec in O1, O2. split; [exact O1|intros z Z; exact (eff_Pmono _ _ _ _ _ _ _ _ _ HW z (O2 z Z))].
    + exfalso. destruct F as (_ & _ & Fo). rewrite csR, Nat.eqb_refl in Fo. cbn [oc ec ek] in Fo. congruence.
  - intros tf f z E F O L. destruct (entR tf f E) as [(Lt & E0)|(-> & ->)].
    + exact (w_OWG Fk Good sw sW sA KK tf f z E0 (isFF_backR tf f F) (ownw_R _ z O) L).
    + exfalso. destruct F as (_ & _ & Fo). rewrite csR, Nat.eqb_refl in Fo. cbn [oc ec ek] in Fo. congruence.
  - intros c' j t1 Oh Sw. rewrite csR in Oh |- *. unfold sread. cbn [pcs]. destruct (Nat.eqb_spec c' c) as [->|N]; cbn [oh oc rg] in *.
    + destruct (Nat.eqb_spec j k) as [->|Nj].
      * exfalso. rewrite upd_eq in Oh. injection Oh as <-. apply Sw. exact (i_sw sw sW sA R (tm sW) (le_n _)).
      * rewrite upd_neq in Oh by exact Nj. destruct (w_WBOC Fk Good sw sW sA KK c j t1 Oh Sw) as [A1 A2].
        split; [exact A1|]. rewrite upd_neq by exact Nj. exact A2.
    + exact (w_WBOC Fk Good sw sW sA KK c' j t1 Oh Sw).
  - intros t f Sw. destruct (w_swc Fk Good sw sW sA KK t f Sw) as (e & E & Cc). exists e. split; [exact (entR_old t e E)|].
    rewrite csR. destruct (Nat.eqb_spec (ec e) c) as [Ec|Nc]; cbn [ai]; [|exact Cc].
    destruct (Nat.eqb_spec (ek e) k) as [Ek'|Nk]; [exfalso; exact (no_ent_k t e E Ec Ek')|].
    rewrite upd_neq by exact Nk. rewrite <- Ec. exact Cc.
  - intros t e E W'. destruct (entR t e E) as [(Lt & E0)|(-> & ->)].
    + pose proof (w_tmo Fk Good sw sW sA KK t e E0 W') as T. rewrite csR. unfold tmo in *.
      destruct (Nat.eqb_spec (ec e) c) as [Ec|Nc]; cbn [oc oh]; [|exact T].
      destruct (Nat.eqb_spec (ek e) k) as [Ek'|Nk]; [exfalso; exact (no_ent_k t e E0 Ec Ek')|].
      rewrite upd_neq by exact Nk. rewrite <- Ec. exact T.
    + cbn [ew] in W'. rewrite Wf in W'. discriminate.
Qed.
End Rd.

(* ---------- a step that logs nothing: the views, log and histories are the same ---------- *)
Section NoLog.
Set Default Proof Using "All".
Variables (p : prog) (Fk : Prop) (Good : nat -> Prop) (sw : nat -> option (cell -> option nat)) (sW sA sW' sA' : st).
Hypothesis RA : run p sA.
Hypothesis R : rel sw sW sA.
Hypothesis KK : KR Fk Good sw sW sA.
Hypothesis Elg : lg sW' = lg sW.
Hypothesis Ehs : hs sW' = hs sW.
Hypothesis ElgA : lg sA' = lg sA.
Hypothesis EhsA : hs sA' = hs sA.
Hypothesis EwcA : wc sA' = wc sA.
Hypothesis EvG : vG sW' = vG sW.
Hypothesis EvGA : vG sA' = vG sA.
Hypothesis Evw : forall c', vP (cs sW' c') = vP (cs sW c') /\ vA (cs sW' c') = vA (cs sW c') /\ vOg (cs sW' c') = vOg (cs sW c').
Hypothesis Eva : forall c', vP (cs sA' c') = vP (cs sA c') /\ vA (cs sA' c') = vA (cs sA c') /\ vOg (cs sA' c') = vOg (cs sA c').
Hypothesis Eoc : forall c', oc (cs sW' c') = oc (cs sW c') /\ oh (cs sW' c') = oh (cs sW c').
Hypothesis Hpc : forall c', pcs sW c' <= pcs sW' c'.
Hypothesis Hrg : forall c' j, rg (cs sW' c') j = rg (cs sW c') j \/ vok (rg (cs sW' c') j) = false.
Hypothesis HFF : forall tf f, ent sW tf = Some f -> isFF sW' tf f -> isFF sW tf f.
Hypothesis Hcas : forall t f e, sw t = Some f -> ent sW t = Some e -> is_cas (ai (cs sW (ec e)) (ek e)) = true ->
  is_cas (ai (cs sW' (ec e)) (ek e)) = true.

Lemma G0 : forall a0 b0, gedge sW a0 b0 -> gedge sW' a0 b0.
Proof.
  intros a0 b0 G. unfold gedge in *. rewrite Ehs, Elg. exact G.
Qed.
Lemma C0 : forall V, vsub (cov sW V) (cov sW' V).
Proof. apply cov_grow. exact G0. Qed.
Lemma P0 : forall a0 b0, Pth sW a0 b0 -> Pth sW' a0 b0.
Proof.
  intros a0 b0 P. unfold Pth in *. induction P as [a1 b1 G|a1 b1 c1 _ IH1 _ IH2];
    [constructor; exact (G0 a1 b1 G)|exact (t_trans _ _ a1 b1 c1 IH1 IH2)].
Qed.
Lemma ent0 : forall t, ent sW' t = ent sW t. Proof. intros t. unfold ent. rewrite Elg. reflexivity. Qed.
Lemma ent0A : forall t, ent sA' t = ent sA t. Proof. intros t. unfold ent. rewrite ElgA. reflexivity. Qed.
Lemma own0 : forall c' z, ownw sW' c' z <-> ownw sW c' z. Proof. intros. unfold ownw. rewrite Elg. tauto. Qed.

Theorem KR_nolog : KR Fk Good sw sW' sA'.
Proof.
  constructor.
  - rewrite Elg, ElgA. exact (k_len Fk Good sw sW sA KK).
  - intros t eA EA. rewrite ent0A in EA. destruct (k_ent Fk Good sw sW sA KK t eA EA) as (eW & EW & S). exists eW. rewrite ent0.
    split; [exact EW|]. unfold ksame in *. rewrite Ehs. exact S.
  - intros HF t eA eW EA EW Gt. rewrite ent0A in EA. rewrite ent0 in EW. intros z Z. apply C0. exact (k_eQ Fk Good sw sW sA KK HF t eA eW EA EW Gt z Z).
  - intros HF c' z Z. rewrite (proj1 (Eva c')) in Z. rewrite (proj1 (Evw c')). apply C0. exact (k_P Fk Good sw sW sA KK HF c' z Z).
  - intros HF c' z Z. rewrite (proj1 (proj2 (Eva c'))) in Z. rewrite (proj1 (proj2 (Evw c'))). apply C0. exact (k_A Fk Good sw sW sA KK HF c' z Z).
  - intros HF c' z Z. rewrite (proj2 (proj2 (Eva c'))) in Z. rewrite (proj2 (proj2 (Evw c'))). apply C0. exact (k_Og Fk Good sw sW sA KK HF c' z Z).
  - intros HF z Z. rewrite EvGA in Z. rewrite EvG. apply C0. exact (k_G Fk Good sw sW sA KK HF z Z).
  - intros HF y x I z Z. rewrite EhsA in I. rewrite EwcA in Z. destruct (k_wc Fk Good sw sW sA KK HF y x I z Z) as [E|Pz]; [left; exact E|right; exact (P0 _ _ Pz)].
  - intros x w I. rewrite Ehs in I |- *. exact (w_bet Fk Good sw sW sA KK x w I).
  - intros x. rewrite Ehs. exact (w_nodup Fk Good sw sW sA KK x).
  - intros c' z O. apply own0 in O. rewrite (proj1 (Evw c')). exact (w_OW Fk Good sw sW sA KK c' z O).
  - intros tf f E F. rewrite ent0 in E. rewrite (proj1 (Evw (ec f))), (proj2 (proj2 (Evw (ec f)))).
    exact (w_OGP Fk Good sw sW sA KK tf f E (HFF tf f E F)).
  - intros tf f z E F O L. rewrite ent0 in E. apply own0 in O. exact (w_OWG Fk Good sw sW sA KK tf f z E (HFF tf f E F) O L).
  - intros c' j t1 Oh Sw. destruct (Eoc c') as [Oc Oh']. rewrite Oh' in Oh. rewrite Oc.
    destruct (w_WBOC Fk Good sw sW sA KK c' j t1 Oh Sw) as [A1 A2]. split; [exact A1|].
    destruct (Hrg c' j) as [Er|Vf]; [rewrite Er; destruct A2 as [L|V]; [left; pose proof (Hpc c'); lia|right; exact V]|right; exact Vf].
  - intros t f Sw. destruct (w_swc Fk Good sw sW sA KK t f Sw) as (e & E & Cc). exists e. rewrite ent0. split; [exact E|].
    exact (Hcas t f e Sw E Cc).
  - intros t e E W'. rewrite ent0 in E. pose proof (w_tmo Fk Good sw sW sA KK t e E W') as T. unfold tmo in *.
    destruct (Eoc (ec e)) as [Oc Oh']. rewrite Oc, Oh'. exact T.
Qed.
End NoLog.
