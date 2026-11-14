(* Part 21: the shape of one step of A (base) as the write-back state sees it, for
   the synchronisation invariant WK (part 22): an old log entry stays, and a guard() event at it
   stays a guard() event only if it was one; the new entry, if any, is the stepping context's;
   a new store conveys the release view; a new guard() event knew what its context knew or had
   acquired and what guard() had published, and publishes it and releases it. *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB M2DQWBK1 M2DQWBK2 M2DQWBK5 M2DQWBK20.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

Section Shape.
Set Default Proof Using "All".
Variables (p : prog) (s s' : st).
Hypothesis H : step p s s'.
Hypothesis Tl : tm s = length (lg s).

Lemma sh_lg : (tm s' = tm s /\ lg s' = lg s) \/ (tm s' = S (tm s) /\ exists e, lg s' = lg s ++ [e]).
Proof.
  destruct (stepQ_split p s s' H) as [[HA _]|RF]; [|left; rewrite (rfx_tm _ _ RF), (rfx_lg _ _ RF); split; reflexivity].
  destruct (step_cases p s s' HA) as
    [(c & i & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & _ & _ & He & _ & ->)
    |[(c & k & d & B & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & He & _ & ->)
    |[(c & d & _ & _ & _ & _ & _ & _ & ->)
    |[(c & k & xs & B & m' & a & K & u & w & bv & _ & _ & _ & _ & _ & He & _ & ->)
    |[(c & _ & _ & _ & _ & _ & _ & _ & ->)
    |(cX & jX & bX & BX & oX & _ & _ & _ & ->)]]]]].
  1, 2, 4: right; split; [reflexivity|eexists; reflexivity].
  1, 2: left; split; reflexivity.
  left. unfold scfix0. cbn [tm lg]. rewrite tm_flp, lg_flp. split; reflexivity.
Qed.

Lemma sh_tm : tm s' = length (lg s').
Proof. destruct sh_lg as [(E1 & E2)|(E1 & e & E2)]; rewrite E1, E2; [exact Tl|rewrite length_app; cbn; lia]. Qed.

Lemma sh_old : forall g, g < tm s -> ent s' g = ent s g.
Proof.
  intros g L. unfold ent. destruct sh_lg as [(_ & E)|(_ & e & E)]; rewrite E; [reflexivity|].
  rewrite nth_error_app1; [reflexivity|lia].
Qed.

Lemma sh_ent_lt : forall g e, ent s' g = Some e -> g <= tm s.
Proof.
  intros g e E. unfold ent in E. assert (L : g < length (lg s')) by (apply nth_error_Some; congruence).
  destruct sh_lg as [(_ & E2)|(_ & e2 & E2)]; rewrite E2 in L; [lia|rewrite length_app in L; cbn in L; lia].
Qed.

(* a guard() event at an old entry was one before *)
Lemma sh_isFF_old : forall g e, g < tm s -> ent s' g = Some e -> isFF s' g e -> isFF s g e.
Proof.
  intros g e L E (Fa & Fp & Fo).
  destruct (stepQ_split p s s' H) as [[HA _]|RF]; [|exact (proj1 (isFF_rfx _ _ RF g e) (conj Fa (conj Fp Fo)))].
  destruct (step_cases p s s' HA) as
    [(c & i & m' & a & K & u & w & Hi & _ & _ & _ & _ & _ & _ & _ & He & _ & ->)
    |[(c & k & d & B & m' & a & K & u & w & Lk & _ & _ & _ & _ & _ & He & _ & ->)
    |[(c & d & H1 & H2 & H3 & _ & _ & _ & ->)
    |[(c & k & xs & B & m' & a & K & u & w & bv & _ & Hoc & _ & _ & _ & He & _ & ->)
    |[(c & S1 & S2 & _ & _ & _ & _ & _ & ->)
    |(cX & jX & bX & BX & oX & _ & _ & _ & ->)]]]]].
  - unfold sord, evs in *; cbn [cs pcs] in *. unfold isFF.
    destruct (Nat.eq_dec (ec e) c) as [Ec|Nc].
    + rewrite Ec in Fa; rewrite Ec in Fo; rewrite Ec in Fp; rewrite Ec. rewrite upd_eq in Fa; rewrite upd_eq in Fo; rewrite upd_eq in Fp. cbn [ai oc] in Fa, Fo.
      destruct (Nat.eq_dec (ek e) (pcs s c)) as [Ek|Nk].
      * exfalso. rewrite Ek, upd_eq in Fo. injection Fo. lia.
      * rewrite upd_neq in Fa by exact Nk; rewrite upd_neq in Fo by exact Nk. split; [exact Fa|]. split; [lia|exact Fo].
    + rewrite upd_neq in Fa by exact Nc; rewrite upd_neq in Fo by exact Nc; rewrite upd_neq in Fp by exact Nc. auto.
  - unfold searly, set_es, searly0, evs in *; cbn [cs pcs] in *. unfold isFF.
    destruct (Nat.eq_dec (ec e) c) as [Ec|Nc].
    + rewrite Ec in Fa; rewrite Ec in Fo; rewrite Ec in Fp; rewrite Ec. rewrite upd_eq in Fa; rewrite upd_eq in Fo. cbn [ai oc] in Fa, Fo.
      destruct (Nat.eq_dec (ek e) k) as [Ek|Nk].
      * exfalso. rewrite Ek, upd_eq in Fo. injection Fo. lia.
      * rewrite upd_neq in Fa by exact Nk; rewrite upd_neq in Fo by exact Nk. auto.
    + rewrite upd_neq in Fa by exact Nc; rewrite upd_neq in Fo by exact Nc. auto.
  - unfold smatch in *; cbn [cs pcs] in *. unfold isFF.
    destruct (Nat.eq_dec (ec e) c) as [Ec|Nc].
    + rewrite Ec in Fa; rewrite Ec in Fo; rewrite Ec in Fp; rewrite Ec. rewrite upd_eq in Fa; rewrite upd_eq in Fo; rewrite upd_eq in Fp. cbn [ai oc] in Fa, Fo.
      destruct (Nat.eq_dec (ek e) (pcs s c)) as [Ek|Nk].
      * exfalso. rewrite Ek, upd_eq in Fa. exact (eof_notFF _ _ _ H3 Fa).
      * rewrite upd_neq in Fa by exact Nk. split; [exact Fa|]. split; [lia|exact Fo].
    + rewrite upd_neq in Fa by exact Nc; rewrite upd_neq in Fo by exact Nc; rewrite upd_neq in Fp by exact Nc. auto.
  - unfold sread in *; cbn [cs pcs] in *. unfold isFF.
    destruct (Nat.eq_dec (ec e) c) as [Ec|Nc].
    + rewrite Ec in Fa; rewrite Ec in Fo; rewrite Ec in Fp; rewrite Ec. rewrite upd_eq in Fa; rewrite upd_eq in Fo. cbn [ai oc] in Fa, Fo.
      destruct (Nat.eq_dec (ek e) k) as [Ek|Nk].
      * exfalso. rewrite Ek, upd_eq in Fa. discriminate.
      * rewrite upd_neq in Fa by exact Nk. auto.
    + rewrite upd_neq in Fa by exact Nc; rewrite upd_neq in Fo by exact Nc. auto.
  - unfold sskip in *; cbn [cs pcs] in *. unfold isFF.
    destruct (Nat.eq_dec (ec e) c) as [Ec|Nc].
    + rewrite Ec in Fa; rewrite Ec in Fo; rewrite Ec in Fp; rewrite Ec. rewrite upd_eq in Fa; rewrite upd_eq in Fo; rewrite upd_eq in Fp. cbn [ai oc] in Fa, Fo.
      destruct (Nat.eq_dec (ek e) (pcs s c)) as [Ek|Nk].
      * exfalso. rewrite Ek in Fo. congruence.
      * rewrite upd_neq in Fa by exact Nk. split; [exact Fa|]. split; [lia|exact Fo].
    + rewrite upd_neq in Fa by exact Nc; rewrite upd_neq in Fo by exact Nc; rewrite upd_neq in Fp by exact Nc. auto.
  - unfold scfix0 in *; cbn [cs pcs] in *. rewrite pcs_flp in Fp. unfold isFF.
    destruct (Nat.eq_dec (ec e) cX) as [Ec|Nc].
    + rewrite Ec in Fa; rewrite Ec in Fo; rewrite Ec in Fp; rewrite Ec. rewrite upd_eq in Fa; rewrite upd_eq in Fo. cbn [ai oc] in Fa, Fo. rewrite ai_flp in Fa. rewrite oc_flp in Fo. auto.
    + rewrite upd_neq in Fa by exact Nc; rewrite upd_neq in Fo by exact Nc. rewrite ai_flp in Fa. rewrite oc_flp in Fo. auto.
Qed.

(* the new entry, if any, and what the step does to the conveyed sets *)
Lemma sh_new : forall e, ent s' (tm s) = Some e ->
  (forall y, y <> tm s -> wc s' y = wc s y) /\
  (ew e = true -> wc s' (tm s) = vor (vR (cs s (ec e))) (vone (tm s))) /\
  (ew e = false -> wc s' (tm s) = wc s (tm s)) /\
  (isFF s' (tm s) e -> ew e = false /\ eP e = vor (vor (vP (cs s (ec e))) (vA (cs s (ec e)))) (vG s) /\
     vsub (eP e) (vR (cs s' (ec e))) /\ vsub (eP e) (vG s')).
Proof.
  intros e Ee.
  destruct (stepQ_split p s s' H) as [[HA _]|RF]; [|exfalso; unfold ent in Ee; rewrite (rfx_lg _ _ RF) in Ee; exact (ent_none _ _ _ Tl Ee)].
  destruct (step_cases p s s' HA) as
    [(c & i & m' & a & K & u & w & Hi & _ & _ & _ & _ & _ & _ & _ & He & _ & ->)
    |[(c & k & d & B & m' & a & K & u & w & Lk & _ & _ & _ & _ & _ & He & _ & ->)
    |[(c & d & _ & _ & _ & _ & _ & _ & ->)
    |[(c & k & xs & B & m' & a & K & u & w & bv & _ & _ & _ & _ & _ & He & _ & ->)
    |[(c & _ & _ & _ & _ & _ & _ & _ & ->)
    |(cX & jX & bX & BX & oX & _ & _ & _ & ->)]]]]].
  6: exfalso; unfold ent, scfix0 in Ee; cbn [lg] in Ee; rewrite lg_flp in Ee; exact (ent_none _ _ _ Tl Ee).
  3, 5: exfalso; unfold ent in Ee; first [unfold smatch in Ee|unfold sskip in Ee]; cbn [lg] in Ee; exact (ent_none _ _ _ Tl Ee).
  all: unfold sord, searly, set_es, searly0, evs, sread in *; cbn [lg cs wc vG pcs] in *;
       unfold ent in Ee; pose proof (ent_new _ _ _ _ Tl Ee) as ->; cbn [ec ek ew eP] in *.
  all: destruct (eff_C _ _ _ _ _ _ _ _ _ He) as [C1 C2].
  all: split; [intros y Ny; destruct w; [rewrite (C1 eq_refl); unfold upd; destruct (Nat.eqb_spec y (tm s)); [congruence|reflexivity]|rewrite (C2 eq_refl); reflexivity]|].
  all: split; [intros Ew; subst w; rewrite (C1 eq_refl), upd_eq; reflexivity|].
  all: split; [intros Ew; subst w; rewrite (C2 eq_refl); reflexivity|].
  all: intros (Fa & Fp & Fo); cbn [ec ek cs pcs oc] in Fa, Fp, Fo; rewrite upd_eq in Fa; cbn [ai] in Fa; try rewrite upd_eq in Fp; rewrite ?upd_eq.
  - rewrite upd_eq in Fa. rewrite Fa in He. destruct (eff_ffK _ _ _ _ _ _ _ _ He) as (-> & -> & ->). cbn. unfold vsub, vor.
    split; [reflexivity|split; [reflexivity|split; intros z Z; tauto]].
  - exfalso. lia.
  - exfalso. rewrite upd_eq in Fa. discriminate.
Qed.

(* the stores of a step: a store not written back is the new one or was there *)
Lemma sh_hs : forall x u, In (u, false) (hs s' x) -> In (u, false) (hs s x) \/ u = tm s.
Proof.
  intros x u I.
  destruct (stepQ_split p s s' H) as [[HA _]|RF]; [|left; rewrite (rfx_hs _ _ RF) in I; exact I].
  destruct (step_cases p s s' HA) as
    [(c & i & m' & a & K & u0 & w & _ & _ & _ & _ & _ & _ & _ & _ & He & _ & ->)
    |[(c & k & d & B & m' & a & K & u0 & w & _ & _ & _ & _ & _ & _ & He & _ & ->)
    |[(c & d & _ & _ & _ & _ & _ & _ & ->)
    |[(c & k & xs & B & m' & a & K & u0 & w & bv & _ & _ & _ & _ & _ & He & _ & ->)
    |[(c & _ & _ & _ & _ & _ & _ & _ & ->)
    |(cX & jX & bX & BX & oX & _ & _ & _ & ->)]]]]].
  6: left; unfold scfix0 in I; cbn [hs] in I; rewrite hs_flp in I; exact I.
  3, 5: left; exact I.
  all: unfold sord, searly, set_es, searly0, evs, sread in *; cbn [hs] in I.
  all: destruct (eff_hist _ _ _ _ _ _ _ _ _ He) as [Eh|(xs0 & P)]; [left; rewrite Eh in I; exact I|].
  all: destruct (places_cell _ _ _ _ x P) as [E|(h1 & h2 & E1 & E2)]; [left; rewrite E in I; exact I|].
  all: rewrite E2 in I; apply in_app_iff in I; destruct I as [I|[I|I]];
       [left; cbn [mH mof]; cbn [mH mof] in E1; rewrite E1; apply in_app_iff; left; exact I
       |right; injection I as <-; reflexivity
       |left; cbn [mH mof]; cbn [mH mof] in E1; rewrite E1; apply in_app_iff; right; exact I].
Qed.
(* the conveyed sets of the stores made before *)
Lemma sh_wc_old : forall y, y < tm s -> wc s' y = wc s y.
Proof.
  intros y L.
  destruct (stepQ_split p s s' H) as [[HA _]|RF]; [|rewrite (rfx_wc _ _ RF); reflexivity].
  destruct (step_cases p s s' HA) as
    [(c & i & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & _ & _ & He & _ & ->)
    |[(c & k & d & B & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & He & _ & ->)
    |[(c & d & _ & _ & _ & _ & _ & _ & ->)
    |[(c & k & xs & B & m' & a & K & u & w & bv & _ & _ & _ & _ & _ & He & _ & ->)
    |[(c & _ & _ & _ & _ & _ & _ & _ & ->)
    |(cX & jX & bX & BX & oX & _ & _ & _ & ->)]]]]].
  6: unfold scfix0; cbn [wc]; rewrite wc_flp; reflexivity.
  3, 5: reflexivity.
  all: unfold sord, searly, set_es, searly0, evs, sread; cbn [wc].
  all: destruct (eff_C _ _ _ _ _ _ _ _ _ He) as [C1 C2]; destruct w; [rewrite (C1 eq_refl); unfold upd; destruct (Nat.eqb_spec y (tm s)); [lia|reflexivity]|rewrite (C2 eq_refl); reflexivity].
Qed.
End Shape.
