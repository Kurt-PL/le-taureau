(* Part 12: the premises HB1/HB2 of a later state hold of the earlier one. *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB M2DQWBK1 M2DQWBK2 M2DQWBK3 M2DQWBK7 M2DQWBK9 M2DQWBK10.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

Lemma HB_same : forall Good s s', (forall t, ent s' t = ent s t) ->
  (forall tf f, ent s tf = Some f -> isFF s' tf f -> isFF s tf f) ->
  HB1 Good s' -> HB2 Good s' -> HB1 Good s /\ HB2 Good s.
Proof.
  intros Good s s' E F H1 H2. split.
  - intros t e Et G. rewrite <- E in Et. destruct (H1 t e Et G) as (tg & g & L & Eg & Ec & Fg & Lt).
    rewrite E in Eg. exists tg, g. split; [exact L|split; [exact Eg|split; [exact Ec|split; [exact (F tg g Eg Fg)|]]]].
    intros t' e' L1 L2 E' C. rewrite <- E in E'. exact (Lt t' e' L1 L2 E' C).
  - intros t e Et W Ne. rewrite <- E in Et. exact (H2 t e Et W Ne).
Qed.

Lemma isFF_pass : forall s c i tpW cmW esW, i <> IFn FFull -> forall tf f,
  isFF (mkS (tm s) (upd (cs s) c (mkC (oc (cs s c)) (rg (cs s c)) (upd (ai (cs s c)) (pcs s c) i) (rw (cs s c)) (rv (cs s c)) (bd (cs s c))
                  (vP (cs s c)) (vA (cs s c)) (vR (cs s c)) (vO (cs s c)) (vOg (cs s c)) (oh (cs s c)) (fx (cs s c))))
       (wv s) (wc s) (hs s) (vG s) (upd (pcs s) c (S (pcs s c))) tpW cmW (lg s) esW) tf f -> isFF s tf f.
Proof.
  intros s c i tpW cmW esW Ni tf f (Fa & Fp & Fo). cbn [cs pcs] in Fa, Fp, Fo. rewrite cs_upd in Fa, Fo.
  destruct (Nat.eqb_spec (ec f) c) as [Ec|Nc]; cbn [ai oc] in Fa, Fo.
  - rewrite Ec in Fp. rewrite upd_eq in Fp. destruct (Nat.eqb_spec (ek f) (pcs s c)) as [Ek|Nk].
    + exfalso. rewrite Ek, upd_eq in Fa. exact (Ni Fa).
    + rewrite upd_neq in Fa by exact Nk. unfold isFF. rewrite Ec. split; [exact Fa|split; [lia|exact Fo]].
  - rewrite upd_neq in Fp by exact Nc. unfold isFF. auto.
Qed.

Lemma cfixc_g : forall o j b B cc, oc (cfixc cc o j b B) = oc cc /\ ai (cfixc cc o j b B) = ai cc.
Proof. intros o j b B cc. unfold cfixc, scfix_cc, scfail_cc. destruct o as [k|]; [destruct b|]; split; reflexivity. Qed.

Lemma step_HB_backA : forall p Good s s', M2Model.step p s s' -> tm s = length (lg s) -> HB1 Good s' -> HB2 Good s' -> HB1 Good s /\ HB2 Good s.
Proof.
  intros p Good s s' H Tl H1 H2.
  destruct (step_cases p s s' H) as
    [(c & i & m' & a & K & u & w & Hi & Hoc & _ & _ & _ & Hh & _ & _ & He & _ & ->)
    |[(c & k & d & B & m' & a & K & u & w & L1 & Hoc & _ & Hd & _ & _ & He & _ & ->)
    |[(c & d & S1 & S2 & S3 & _ & _ & _ & ->)
    |[(c & k & xs & B & m' & a & K & u & w & bv & L1 & Hoc & Hoh & _ & _ & He & _ & ->)
    |[(c & S1 & S2 & _ & _ & _ & _ & _ & ->)
    |(cX & jX & bX & BX & oX & HjX & HfX & HcX & ->)]]]]].
  - destruct (HB_evsx Good s c (pcs s c) i m' a K u w (bd (cs s c)) _ _ _ _ Tl Hoc (pc2_upd (pcs s) c) H1 H2) as (_ & _ & A & B). auto.
  - destruct (HB_evsx Good s c k (inst_of d) m' a K u w (bor (bd (cs s c)) B) _ _ _ _ Tl Hoc (pc2_id (pcs s) c k) H1 H2) as (_ & _ & A & B'). auto.
  - apply (HB_same Good s (smatch p s c) (fun t => eq_refl)); [|exact H1|exact H2].
    intros tf f _ F. exact (isFF_pass s c (ins p c (pcs s c) (rg (cs s c))) _ _ _ (eof_notFF _ _ _ S3) tf f F).
  - destruct (HB_sread Good s c k Plain xs B m' a K u w bv Tl Hoc H1 H2) as (_ & A & B'). auto.
  - apply (HB_same Good s (sskip p s c) (fun t => eq_refl)); [|exact H1|exact H2].
    intros tf f _ F. refine (isFF_pass s c (ins p c (pcs s c) (rg (cs s c))) _ _ _ _ tf f F).
    intros Z. pose proof (xex_FF (cs s c) (rg (cs s c)) (pcs s c)) as X. rewrite <- Z in X. congruence.
  - apply (HB_same Good s (scfix0 (sflp s cX oX bX) cX jX bX BX)).
    + intros t. unfold ent, scfix0. cbn [lg]. rewrite lg_flp. reflexivity.
    + intros tf f _ (Fa & Fp & Fo). rewrite cs_cfix in Fa, Fo. unfold scfix0 in Fp. cbn [pcs] in Fp. rewrite pcs_flp in Fp.
      destruct (Nat.eqb_spec (ec f) cX) as [Ec|]; [|unfold isFF; auto].
      destruct (cfixc_g oX jX bX BX (cs s cX)) as (E1 & E3). rewrite E1 in Fo. rewrite E3 in Fa.
      unfold isFF. rewrite Ec. rewrite Ec in Fp. auto.
    + exact H1.
    + exact H2.
Qed.

Lemma step_HB_back : forall p Good s s', step p s s' -> tm s = length (lg s) -> HB1 Good s' -> HB2 Good s' -> HB1 Good s /\ HB2 Good s.
Proof.
  intros. match goal with H : stepQ _ ?s ?s2 |- _ => destruct (stepQ_split _ s s2 H) as [[HA _]|RF]; [eapply step_HB_backA; eauto|] end.
  unfold HB1, HB2 in *. split; intros t e E; [intros G; apply (LFB_rfx _ _ RF)|]; unfold ent in *; rfx_rw RF; eauto.
Qed.

Lemma wb_HB_back : forall Good s c k t H'', HB1 Good (wbst s c k t H'') -> HB2 Good (wbst s c k t H'') -> HB1 Good s /\ HB2 Good s.
Proof.
  intros Good s c k t H'' H1 H2.
  assert (Ee : forall t' e, ent s t' = Some e -> ent (wbst s c k t H'') t' = Some (sete t e)).
  { intros t' e E. unfold ent, wbst. cbv zeta. cbn [lg]. rewrite nth_setew. unfold ent in E. rewrite E. reflexivity. }
  assert (Ef : forall e, ec (sete t e) = ec e /\ ek (sete t e) = ek e /\ eh (sete t e) = eh e /\ (ew e = true -> ew (sete t e) = true)).
  { intros e. unfold sete. destruct (Nat.eqb (et e) t); cbn; auto. }
  assert (Fb : forall tf f, isFF (wbst s c k t H'') tf f -> isFF s tf f).
  { intros tf f (Fa & Fp & Fo). unfold wbst in Fa, Fp, Fo. cbv zeta in Fa, Fp, Fo. cbn [cs pcs] in Fa, Fp, Fo. rewrite cs_upd in Fa, Fo.
    unfold isFF. destruct (Nat.eqb_spec (ec f) c) as [Ec|]; cbn [ai oc] in Fa, Fo; [rewrite Ec in *|]; (split; [|split]); auto. }
  split.
  - intros t' e E G. destruct (Ef e) as (C1 & _ & _ & _). pose proof (H1 t' (sete t e) (Ee t' e E) G) as L. rewrite C1 in L.
    destruct L as (tg & g & Lg & Eg & Ec & Fg & Lt).
    unfold ent, wbst in Eg. cbv zeta in Eg. cbn [lg] in Eg. rewrite nth_setew in Eg.
    destruct (nth_error (lg s) tg) as [g0|] eqn:Eg0; [|discriminate]. cbn in Eg. injection Eg as <-.
    destruct (Ef g0) as (G1 & G2 & _).
    exists tg, g0. split; [exact Lg|split; [exact Eg0|split; [congruence|split]]].
    + apply Fb. unfold isFF in *. rewrite G1, G2 in Fg. exact Fg.
    + intros t'' e' L1 L2 E' C. destruct (Ef e') as (D1 & _ & D3 & D4).
      destruct (Lt t'' (sete t e') L1 L2 (Ee t'' e' E') ltac:(congruence)) as [A B].
      split; [congruence|]. destruct (ew e') eqn:W; [|reflexivity]. rewrite (D4 eq_refl) in B. discriminate.
  - intros t' e E W Ne. destruct (Ef e) as (_ & _ & _ & D4). apply (H2 t' (sete t e) (Ee t' e E) (D4 W)).
    unfold sete. destruct (Nat.eqb (et e) t); exact Ne.
Qed.
