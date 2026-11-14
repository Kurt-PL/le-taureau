(* Part 13: every runWB whose events meet HB1/HB2 has an A image related by rel and KR. *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB M2DQWBK1 M2DQWBK2 M2DQWBK3 M2DQWBK4 M2DQWBK7 M2DQWBK9 M2DQWBK10 M2DQWBK11 M2DQWBK12.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

(* in the A image: a guard() passed before a CAS whose read happened alone happened before that read *)
Lemma ff_before_half : forall p s c k t1 j tf, run p s -> oh (cs s c) k = Some t1 -> oc (cs s c) k = None -> pcs s c <= k ->
  j < pcs s c -> ai (cs s c) j = IFn FFull -> oc (cs s c) j = Some tf -> tf < t1.
Proof.
  intros p s c k t1 j tf R Oh Oc Lk Lj Aj Oj. pose proof (Inv1_run p s R) as I.
  destruct (i_half p s I c k t1 Oc Oh Lk) as (_ & (xs & Ax) & _).
  destruct (proj1 (i_cmA p s I c j) Lj) as (tau & In').
  destruct (i_set p s I c j tau In') as [_ Es]. rewrite Aj in Es.
  assert (Hp : hpending (cs s c) (pcs s c) k Plain xs) by (split; [exact Lk|split; [congruence|rewrite Ax; reflexivity]]).
  destruct (i_ptieh p s I c k t1 Plain xs j Hp Oh Lj) as (tj & Tj & L).
  - rewrite <- Es. reflexivity.
  - rewrite <- Es. right; left. reflexivity.
  - unfold tmo in Tj. rewrite Oj in Tj. injection Tj as ->. exact L.
Qed.

(* an A entry of a CAS that fails as a whole, or of a read alone, stores nothing *)
Lemma ew_fail : forall p s t e, run p s -> ent s t = Some e -> is_cas (einstr p s e) = true ->
  (eh e = true \/ vok (rg (cs s (ec e)) (ek e)) = false) -> ew e = false.
Proof.
  intros p s t e R E C H. pose proof (proj2 (Inv2_run p s R)) as J.
  destruct (j_ew p s J t e _ E eq_refl) as [Ew _].
  destruct (eh e) eqn:Eh; [rewrite Ew; reflexivity|].
  destruct H as [H|H]; [discriminate|].
  destruct (icond (einstr p s e) (rgof s e)) eqn:Ic.
  - assert (Xl : xload (einstr p s e) (rgof s e) = true).
    { unfold xload. rewrite Ic. destruct (einstr p s e); try discriminate; reflexivity. }
    rewrite <- (j_ok p s J t e E Eh C Xl). exact H.
  - rewrite Ew. rewrite andb_false_r. reflexivity.
Qed.

Lemma partskip_formA : forall p s s' c k t1, M2Model.step p s s' -> partskip s s' c k t1 -> s' = sskip p s c.
Proof.
  intros p s s' c k t1 H (NW & Tm & Pk & Pk' & Oc & _).
  destruct (step_cases p s s' H) as
    [(c0 & i & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ->)
    |[(c0 & k0 & d & B & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & _ & _ & ->)
    |[(c0 & d & S1 & _ & _ & _ & _ & _ & ->)
    |[(c0 & k0 & xs & B & m' & a & K & u & w & bv & _ & _ & _ & _ & _ & _ & _ & ->)
    |[(c0 & _ & _ & _ & _ & _ & _ & _ & ->)
    |(cX & jX & bX & BX & oX & _ & _ & _ & ->)]]]]].
  - exfalso. cbn in Tm. lia.
  - exfalso. cbn in Tm. lia.
  - exfalso. cbn [smatch pcs] in Pk'. unfold upd in Pk'. destruct (Nat.eqb_spec c c0) as [->|N]; [|lia].
    apply S1. rewrite Pk. exact Oc.
  - exfalso. cbn in Tm. lia.
  - cbn [sskip pcs] in Pk'. unfold upd in Pk'. destruct (Nat.eqb_spec c c0) as [->|N]; [reflexivity|lia].
  - exfalso. unfold scfix0 in Pk'. cbn [pcs] in Pk'. rewrite pcs_flp in Pk'. lia.
Qed.

Lemma partskip_form : forall p s s' c k t1, step p s s' -> partskip s s' c k t1 -> s' = sskip p s c.
Proof.
  intros. match goal with H : stepQ _ ?s ?s2 |- _ => destruct (stepQ_split _ s s2 H) as [[HA _]|RF]; [eapply partskip_formA; eauto|] end.
  exfalso. match goal with P : partskip _ _ _ _ _ |- _ => destruct P as (_ & _ & P1 & P2 & _) end. rewrite (rfx_pcs _ _ RF) in P2. lia.
Qed.

Section Sim.
Variables (p : prog) (W : wf p) (Fk : Prop) (Good : nat -> Prop).

Theorem simWBK_step : forall sw sW sA sW', run p sA -> rel sw sW sA -> KR Fk Good sw sW sA -> stepWB p sW sW' ->
  (Fk -> HB1 Good sW') -> (Fk -> HB2 Good sW') ->
  exists sw' sA', run p sA' /\ rel sw' sW' sA' /\ KR Fk Good sw' sW' sA'.
Proof.
  intros sw sW sA sW' RA R K H H1 H2. pose proof (tmW p Fk Good sw sW sA RA R K) as TL.
  inversion H as [s0 s1 St FHs | s0 s1 c k t1 H'' St Ps Fr Ok | s0 c k t1 xs H'' Lk Oc Oh Ai Vk _ Fr Ok]; subst.
  - destruct (sim_stepK p W sw sW sA RA R Fk Good K sW' St FHs H1 H2) as (sA' & St' & R' & K').
    exists sw, sA'. split; [econstructor; eauto|]. auto.
  - assert (C1 : Fk -> HB1 Good s1) by (intros HF; exact (proj1 (wb_HB_back Good s1 c k t1 H'' (H1 HF) (H2 HF)))).
    assert (C2 : Fk -> HB2 Good s1) by (intros HF; exact (proj2 (wb_HB_back Good s1 c k t1 H'' (H1 HF) (H2 HF)))).
    pose proof (partskip_form p sW s1 c k t1 St Ps) as Es1.
    destruct Ps as (NW & T1 & Pk & Pk' & Oc0 & Oh0 & Oh1 & Cc & Vk).
    destruct (sim_stepK p W sw sW sA RA R Fk Good K s1 St (nowrite_fhsafe _ _ NW) C1 C2) as (sA' & St' & R' & K').
    assert (RA' : run p sA') by (econstructor; eauto).
    assert (Fr' : forall x, ~ In t1 (ids (hs s1 x))) by (intros x; rewrite (NW x); exact (Fr x)).
    assert (Oc1 : oc (cs s1 c) k = None) by (rewrite Es1; unfold sskip; cbn [cs]; rewrite upd_eq; cbn [oc]; exact Oc0).
    exists (upd sw t1 (Some (fun x => pi sw x (rw (cs s1 c) k x)))), sA'.
    split; [exact RA'|]. split.
    + apply (rel_wb sw s1 sA' c k t1 H'' R'); [exact (i_oh sw s1 sA' R' c k t1 Oh1)|exact Fr'|exact Ok].
    + apply (KR_wb p Fk Good sw s1 sA' c k t1 H'' RA' R' K'); [exact (i_oh sw s1 sA' R' c k t1 Oh1)|exact Fr'|exact Ok| | | | | | ].
      * destruct (i_ohW p Fk Good sw s1 sA' RA' R' K' c k t1 Oh1) as (e & E & Ec & Ek & _). eauto.
      * exact Cc.
      * unfold tmo. rewrite Oc1. exact Oh1.
      * intros c' j Oh'. destruct (i_ohW p Fk Good sw s1 sA' RA' R' K' c' j t1 Oh') as (e & E & Ec & Ek & _).
        destruct (i_ohW p Fk Good sw s1 sA' RA' R' K' c k t1 Oh1) as (e' & E' & Ec' & Ek' & _).
        rewrite E in E'. injection E' as <-. split; [congruence|split; [congruence|split; [exact Oc1|left; lia]]].
      * intros tf g Eg (Fa & Fp & Fo) Ec. rewrite Ec in Fa, Fp, Fo. rewrite Pk' in Fp.
        assert (Nk : ek g <> k) by (intros Z; rewrite Z in Fa; rewrite Fa in Cc; discriminate).
        rewrite Es1 in Fa, Fo. unfold sskip in Fa, Fo. cbn [cs] in Fa, Fo. rewrite upd_eq in Fa, Fo. cbn [ai oc] in Fa, Fo.
        rewrite Pk in Fa. rewrite upd_neq in Fa by exact Nk.
        destruct (crel_eq p Fk Good sw sW sA RA R K c) as (Oca & Oha & Aia & _).
        apply (ff_before_half p sA c k t1 (ek g) tf RA).
        -- rewrite Oha. exact Oh0.
        -- rewrite Oca. exact Oc0.
        -- rewrite (r_pcs sw sW sA R). lia.
        -- rewrite (r_pcs sw sW sA R). lia.
        -- rewrite Aia. exact Fa.
        -- rewrite Oca. exact Fo.
      * intros eA EA. destruct (M2Inv.i_oh p sA' (Inv1_run p sA' RA') c k t1) as (e & E & _ & _ & Eh).
        { destruct (crel_eq p Fk Good sw s1 sA' RA' R' K' c) as (_ & Oha & _). rewrite Oha. exact Oh1. }
        rewrite EA in E. injection E as <-.
        destruct (j_ew p sA' (proj2 (Inv2_run p sA' RA')) t1 eA _ EA eq_refl) as [J _]. rewrite J, Eh. reflexivity.
  - exists (upd sw t1 (Some (fun x => pi sw x (rw (cs sW c) k x)))), sA.
    split; [exact RA|]. split.
    + apply (rel_wb sw sW sA c k t1 H'' R); [exact (i_oh sw sW sA R c k t1 Oh)|exact Fr|exact Ok].
    + apply (KR_wb p Fk Good sw sW sA c k t1 H'' RA R K); [exact (i_oh sw sW sA R c k t1 Oh)|exact Fr|exact Ok| | | | | | ].
      * destruct (i_ohW p Fk Good sw sW sA RA R K c k t1 Oh) as (e & E & Ec & Ek & _). eauto.
      * rewrite Ai. reflexivity.
      * unfold tmo. rewrite Oc. exact Oh.
      * intros c' j Oh'. destruct (i_ohW p Fk Good sw sW sA RA R K c' j t1 Oh') as (e & E & Ec & Ek & _).
        destruct (i_ohW p Fk Good sw sW sA RA R K c k t1 Oh) as (e' & E' & Ec' & Ek' & _).
        rewrite E in E'. injection E' as <-. split; [congruence|split; [congruence|split; [exact Oc|right; exact Vk]]].
      * intros tf g Eg (Fa & Fp & Fo) Ec. rewrite Ec in Fa, Fp, Fo.
        destruct (crel_eq p Fk Good sw sW sA RA R K c) as (Oca & Oha & Aia & _).
        apply (ff_before_half p sA c k t1 (ek g) tf RA).
        -- rewrite Oha. exact Oh.
        -- rewrite Oca. exact Oc.
        -- rewrite (r_pcs sw sW sA R). lia.
        -- rewrite (r_pcs sw sW sA R). exact Fp.
        -- rewrite Aia. exact Fa.
        -- rewrite Oca. exact Fo.
      * intros eA EA. destruct (M2Inv.i_oh p sA (Inv1_run p sA RA) c k t1) as (e & E & _ & _ & Eh).
        { destruct (crel_eq p Fk Good sw sW sA RA R K c) as (_ & Oha & _). rewrite Oha. exact Oh. }
        rewrite EA in E. injection E as <-.
        destruct (j_ew p sA (proj2 (Inv2_run p sA RA)) t1 eA _ EA eq_refl) as [J _]. rewrite J, Eh. reflexivity.
Qed.

Lemma step_tmA : forall s s', M2Model.step p s s' -> tm s = length (lg s) -> tm s' = length (lg s').
Proof.
  intros s s' H T.
  destruct (step_cases p s s' H) as
    [(c & i & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ->)
    |[(c & k & d & B & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & _ & _ & ->)
    |[(c & d & _ & _ & _ & _ & _ & _ & ->)
    |[(c & k & xs & B & m' & a & K & u & w & bv & _ & _ & _ & _ & _ & _ & _ & ->)
    |[(c & _ & _ & _ & _ & _ & _ & _ & ->)
    |(cX & jX & bX & BX & oX & _ & _ & _ & ->)]]]]].
  all: cbn; rewrite ?length_app; cbn; try lia.
  unfold scfix0. cbn. rewrite tm_flp, lg_flp. exact T.
Qed.

Lemma step_tm : forall s s', step p s s' -> tm s = length (lg s) -> tm s' = length (lg s').
Proof.
  intros. match goal with H : stepQ _ ?s ?s2 |- _ => destruct (stepQ_split _ s s2 H) as [[HA _]|RF]; [eapply step_tmA; eauto|] end.
  rfx_rw RF. assumption.
Qed.

Lemma wb_tm : forall s c k t H'', tm s = length (lg s) -> tm (wbst s c k t H'') = length (lg (wbst s c k t H'')).
Proof. intros s c k t H'' T. unfold wbst. cbv zeta. cbn. unfold setew. rewrite length_map. exact T. Qed.

Lemma runWB_tm : forall s, runWB p s -> tm s = length (lg s).
Proof.
  intros s R. induction R as [|s s' R IH St]; [reflexivity|].
  inversion St; subst; [exact (step_tm s s' ltac:(eassumption) IH)| |];
    apply wb_tm; try exact IH; exact (step_tm s _ ltac:(eassumption) IH).
Qed.

Lemma stepWB_HB_back0 : forall s s', runWB p s -> stepWB p s s' -> HB1 Good s' -> HB2 Good s' -> HB1 Good s /\ HB2 Good s.
Proof.
  intros s s' R H H1 H2. pose proof (runWB_tm s R) as T.
  inversion H as [s0 s1 St _ | s0 s1 c k t1 H'' St _ _ _ | s0 c k t1 xs H'' _ _ _ _ _ _ _ _]; subst.
  - exact (step_HB_back p Good s s' St T H1 H2).
  - destruct (wb_HB_back Good s1 c k t1 H'' H1 H2) as [C1 C2]. exact (step_HB_back p Good s s1 St T C1 C2).
  - exact (wb_HB_back Good s c k t1 H'' H1 H2).
Qed.

Lemma stepWB_HB_back : forall s s', runWB p s -> stepWB p s s' -> (Fk -> HB1 Good s') -> (Fk -> HB2 Good s') ->
  (Fk -> HB1 Good s) /\ (Fk -> HB2 Good s).
Proof. intros s s' R H H1 H2. split; intros HF; destruct (stepWB_HB_back0 s s' R H (H1 HF) (H2 HF)); auto. Qed.

Theorem runWBK : forall s, runWB p s -> (Fk -> HB1 Good s) -> (Fk -> HB2 Good s) ->
  exists sw sA, run p sA /\ rel sw s sA /\ KR Fk Good sw s sA.
Proof.
  intros s R. induction R as [|s s' R IH St]; intros H1 H2.
  - exists sw0, sinit. split; [constructor|split; [exact rel_init|exact (KR_init Fk Good)]].
  - destruct (stepWB_HB_back s s' R St H1 H2) as [B1 B2].
    destruct (IH B1 B2) as (sw & sA & RA & Rl & K).
    destruct (simWBK_step sw s sA s' RA Rl K St H1 H2) as (sw' & sA' & RA' & Rl' & K').
    exists sw', sA'. auto.
Qed.
End Sim.
