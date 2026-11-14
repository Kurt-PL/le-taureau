(* Part 20: how knowledge moves in a write-back run (no premise on the programme).
   KM: a context's release view is within what it knows or has acquired, and what it knows in
   order through guard() is within what it knows or what guard() has published.  Along every
   step of the write-back model the shared view G and each context's P, A, R and Og only grow
   (vmono), and KM holds on every runWB state.  A guard() step publishes what its context knew
   or had acquired, and its release view then holds what was published before it (stepWB_ff).
   These are the links of the synchronisation chain the write-back cover (G2) uses. *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB M2DQWBK1 M2DQWBK2.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

Definition KM (s : st) : Prop := forall c,
  vsub (vR (cs s c)) (vor (vP (cs s c)) (vA (cs s c))) /\ vsub (vOg (cs s c)) (vor (vP (cs s c)) (vG s)).

Definition vmono (s s' : st) : Prop := vsub (vG s) (vG s') /\ forall c,
  vsub (vP (cs s c)) (vP (cs s' c)) /\ vsub (vA (cs s c)) (vA (cs s' c)) /\
  vsub (vR (cs s c)) (vR (cs s' c)) /\ vsub (vOg (cs s c)) (vOg (cs s' c)).

Lemma vmono_refl : forall s, vmono s s.
Proof. intros s. split; [intros z Z; exact Z|intros c; repeat split; intros z Z; exact Z]. Qed.
Lemma vmono_trans : forall a b c, vmono a b -> vmono b c -> vmono a c.
Proof.
  intros a b c (G1 & H1) (G2 & H2). split; [intros z Z; exact (G2 z (G1 z Z))|].
  intros c0. destruct (H1 c0) as (P1 & A1 & R1 & O1). destruct (H2 c0) as (P2 & A2 & R2 & O2).
  repeat split; intros z Z; auto.
Qed.

Lemma KM_init : KM sinit.
Proof. intros c. split; intros z Z; cbn in Z; contradiction. Qed.

(* ---------- one effect ---------- *)
Lemma eff_km : forall t i r m m' a K u w Og, eff t i r m m' a K u w ->
  vsub (mR m) (vor (mP m) (mA m)) -> vsub Og (vor (mP m) (mG m)) ->
  vsub (mP m) (mP m') /\ vsub (mA m) (mA m') /\ vsub (mR m) (mR m') /\ vsub (mG m) (mG m') /\
  vsub Og (newOg i m' Og) /\ vsub (mR m') (vor (mP m') (mA m')) /\ vsub (newOg i m' Og) (vor (mP m') (mG m')).
Proof.
  intros t i r m m' a K u w Og H HR HO. inversion H; subst; cbn [mP mA mR mG learn wput gpre gpost].
  all: try (destruct i as [| | | f |]; cbn [isacc] in *; try discriminate).
  all: cbn [newOg].
  all: unfold vsub, vor in *; repeat split; intros z Z; cbn in *.
  all: try tauto.
  all: try (destruct (HR z Z); tauto).
  all: try (destruct (HO z Z); tauto).
  all: try (destruct Z as [Z|Z]; [destruct (HR z Z)|]; tauto).
  all: try (destruct Z as [Z|Z]; [destruct (HO z Z)|]; tauto).
  all: destruct (HO z Z); unfold vor; tauto.
Qed.

(* a context's record replaced: what the others know is unchanged *)
Lemma upd_km : forall s s' c C, cs s' = upd (cs s) c C -> vsub (vG s) (vG s') -> KM s ->
  vsub (vP (cs s c)) (vP C) -> vsub (vA (cs s c)) (vA C) -> vsub (vR (cs s c)) (vR C) -> vsub (vOg (cs s c)) (vOg C) ->
  vsub (vR C) (vor (vP C) (vA C)) -> vsub (vOg C) (vor (vP C) (vG s')) -> vmono s s' /\ KM s'.
Proof.
  intros s s' c C E G Km P A R O KR KO. split.
  - split; [exact G|]. intros c0. rewrite E. destruct (Nat.eq_dec c0 c) as [->|N].
    + rewrite upd_eq. auto.
    + rewrite upd_neq by exact N. repeat split; intros z Z; exact Z.
  - intros c0. rewrite E. destruct (Nat.eq_dec c0 c) as [->|N].
    + rewrite upd_eq. auto.
    + rewrite upd_neq by exact N. destruct (Km c0) as [K1 K2]. split; [exact K1|].
      intros z Z. destruct (K2 z Z) as [Z'|Z']; [left; exact Z'|right; exact (G z Z')].
Qed.

Lemma same_km : forall s s', KM s -> (forall c, vP (cs s' c) = vP (cs s c) /\ vA (cs s' c) = vA (cs s c) /\
  vR (cs s' c) = vR (cs s c) /\ vOg (cs s' c) = vOg (cs s c)) -> vG s' = vG s -> vmono s s' /\ KM s'.
Proof.
  intros s s' Km E G. split.
  - split; [rewrite G; intros z Z; exact Z|]. intros c. destruct (E c) as (E1 & E2 & E3 & E4). rewrite E1, E2, E3, E4.
    repeat split; intros z Z; exact Z.
  - intros c. destruct (E c) as (E1 & E2 & E3 & E4). rewrite E1, E2, E3, E4, G. exact (Km c).
Qed.

Lemma step_kmA : forall p s s', M2Model.step p s s' -> KM s -> vmono s s' /\ KM s'.
Proof.
  intros p s s' H Km.
  destruct (step_cases p s s' H) as
    [(c & i & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & _ & _ & He & _ & ->)
    |[(c & k & d & B & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & He & _ & ->)
    |[(c & d & _ & _ & _ & _ & _ & _ & ->)
    |[(c & k & xs & B & m' & a & K & u & w & bv & _ & _ & _ & _ & _ & He & _ & ->)
    |[(c & _ & _ & _ & _ & _ & _ & _ & ->)
    |(cX & jX & bX & BX & oX & _ & _ & _ & ->)]]]]].
  1, 2, 4: destruct (Km c) as [HR HO];
    match goal with He : eff _ ?i _ _ _ _ _ _ _ |- _ =>
      destruct (eff_km _ _ _ _ _ _ _ _ _ (vOg (cs s c)) He HR HO) as (P1 & A1 & R1 & G1 & O1 & KR1 & KO1) end;
    eapply upd_km; [reflexivity|exact G1|exact Km|exact P1|exact A1|exact R1|exact O1|exact KR1|exact KO1].
  1, 2: eapply upd_km; [reflexivity|intros z Z; exact Z|exact Km|intros z Z; exact Z..|exact (proj1 (Km c))|exact (proj2 (Km c))].
  apply same_km; [exact Km| |unfold scfix0; cbn [vG]; exact (vG_flp s cX oX bX)].
  intros c0. unfold scfix0. cbn [cs]. destruct (Nat.eq_dec c0 cX) as [->|N].
  - rewrite upd_eq. cbn [vP vA vR vOg]. rewrite vP_flp, vA_flp, vR_flp, vOg_flp. auto.
  - rewrite upd_neq by exact N. rewrite vP_flp, vA_flp, vR_flp, vOg_flp. auto.
Qed.

Lemma step_km : forall p s s', step p s s' -> KM s -> vmono s s' /\ KM s'.
Proof.
  intros. match goal with H : stepQ _ ?s ?s2 |- _ => destruct (stepQ_split _ s s2 H) as [[HA _]|RF]; [eapply step_kmA; eauto|] end.
  split.
  - split; [rewrite (rfx_vG _ _ RF); intros z Z; exact Z|intros c; rfx_rw RF; repeat split; intros z Z; exact Z].
  - intros c. match goal with Km : KM _ |- _ => destruct (Km c) as [K1 K2] end. rfx_rw RF. split; [exact K1|exact K2].
Qed.

Lemma wbst_km : forall s c k t H'', KM s -> vmono s (wbst s c k t H'') /\ KM (wbst s c k t H'').
Proof.
  intros s c k t H'' Km. unfold wbst. cbv zeta. eapply upd_km; [reflexivity|cbn; intros z Z; exact Z|exact Km|..]; cbn [vP vA vR vOg vG].
  all: try (intros z Z; first [exact Z|left; exact Z]).
  - intros z Z. destruct (proj1 (Km c) z Z) as [Z'|Z']; [left; left; exact Z'|right; exact Z'].
  - intros z Z. destruct (proj2 (Km c) z Z) as [Z'|Z']; [left; left; exact Z'|right; exact Z'].
Qed.

Theorem stepWB_km : forall p s s', stepWB p s s' -> KM s -> vmono s s' /\ KM s'.
Proof.
  intros p s s' H. destruct H as [s0 s1 St _ | s0 s1 c k t1 H'' St _ _ Ok | s0 c k t1 xs H'' _ _ _ _ _ _ _ Ok]; intros Km.
  - exact (step_km p s0 s1 St Km).
  - destruct (step_km p s0 s1 St Km) as [M1 K1]. destruct (wbst_km s1 c k t1 H'' K1) as [M2 K2]. split; [exact (vmono_trans _ _ _ M1 M2)|exact K2].
  - exact (wbst_km s0 c k t1 H'' Km).
Qed.

Theorem runWB_KM : forall p s, runWB p s -> KM s.
Proof.
  intros p s R. induction R as [|s s' R IH St]; [exact KM_init|exact (proj2 (stepWB_km p s s' St IH))].
Qed.

(* ---------- a guard() step ---------- *)
Lemma eff_ff_pub : forall t r m m' a K u w, eff t (IFn FFull) r m m' a K u w ->
  vsub (vor (mP m) (mA m)) (mG m') /\ vsub (mG m) (mR m').
Proof.
  intros t r m m' a K u w H. destruct (eff_full _ _ _ _ _ _ _ _ H) as [-> _]. cbn. unfold vsub, vor. split; intros z Z; tauto.
Qed.

Lemma ent_new : forall (l : list oev) e t g, t = length l -> nth_error (l ++ [e]) t = Some g -> g = e.
Proof. intros l e t g -> H. rewrite nth_error_app2 in H by lia. rewrite Nat.sub_diag in H. injection H as <-. reflexivity. Qed.
Lemma ent_none : forall (l : list oev) t g, t = length l -> nth_error l t = Some g -> False.
Proof. intros l t g -> H. assert (length l < length l) by (apply nth_error_Some; congruence). lia. Qed.

(* the guard() logged at time tm s: it publishes what its context knew or had acquired, and its
   release view holds what was published before it *)
Lemma step_ffA : forall p s s' e, M2Model.step p s s' -> tm s = length (lg s) -> nth_error (lg s') (tm s) = Some e ->
  ai (cs s' (ec e)) (ek e) = IFn FFull ->
  vsub (vor (vP (cs s (ec e))) (vA (cs s (ec e)))) (vG s') /\ vsub (vG s) (vR (cs s' (ec e))).
Proof.
  intros p s s' e H Tl Ee Fa.
  destruct (step_cases p s s' H) as
    [(c & i & m' & a & K & u & w & Hi & _ & _ & _ & _ & _ & _ & _ & He & _ & ->)
    |[(c & k & d & B & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & He & _ & ->)
    |[(c & d & _ & _ & _ & _ & _ & _ & ->)
    |[(c & k & xs & B & m' & a & K & u & w & bv & _ & _ & _ & _ & _ & He & _ & ->)
    |[(c & _ & _ & _ & _ & _ & _ & _ & ->)
    |(cX & jX & bX & BX & oX & _ & _ & _ & ->)]]]]].
  - unfold sord, evs in *. cbn [lg cs vG] in *. pose proof (ent_new _ _ _ _ Tl Ee) as ->. cbn [ec ek] in *.
    rewrite upd_eq in Fa |- *. cbn [ai vR] in Fa |- *. rewrite upd_eq in Fa. subst i.
    exact (eff_ff_pub _ _ _ _ _ _ _ _ He).
  - unfold searly, set_es, searly0, evs in *. cbn [lg cs vG] in *. pose proof (ent_new _ _ _ _ Tl Ee) as ->. cbn [ec ek] in *.
    rewrite upd_eq in Fa |- *. cbn [ai vR] in Fa |- *. rewrite upd_eq in Fa. rewrite Fa in He.
    exact (eff_ff_pub _ _ _ _ _ _ _ _ He).
  - exfalso. unfold smatch in Ee. cbn [lg] in Ee. exact (ent_none _ _ _ Tl Ee).
  - exfalso. unfold sread in *. cbn [lg cs] in *. pose proof (ent_new _ _ _ _ Tl Ee) as ->. cbn [ec ek] in *.
    rewrite upd_eq in Fa. cbn [ai] in Fa. rewrite upd_eq in Fa. discriminate.
  - exfalso. unfold sskip in Ee. cbn [lg] in Ee. exact (ent_none _ _ _ Tl Ee).
  - exfalso. unfold scfix0 in Ee. cbn [lg] in Ee. rewrite lg_flp in Ee. exact (ent_none _ _ _ Tl Ee).
Qed.

Lemma step_ff : forall p s s' e, step p s s' -> tm s = length (lg s) -> nth_error (lg s') (tm s) = Some e ->
  ai (cs s' (ec e)) (ek e) = IFn FFull ->
  vsub (vor (vP (cs s (ec e))) (vA (cs s (ec e)))) (vG s') /\ vsub (vG s) (vR (cs s' (ec e))).
Proof.
  intros. match goal with H : stepQ _ ?s ?s2 |- _ => destruct (stepQ_split _ s s2 H) as [[HA _]|RF]; [eapply step_ffA; eauto|] end.
  exfalso. rewrite (rfx_lg _ _ RF) in *. match goal with Tl : tm _ = length _, Ee : nth_error _ _ = Some _ |- _ => exact (ent_none _ _ _ Tl Ee) end.
Qed.
