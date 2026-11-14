(* Part 22: the synchronisation invariant WK of the write-back model (every runWB,
   no premise on the programme).  For log entries g, g' that are guard() events (isFF):
   - a store conveys at most its context's release view (wk_R), which holds what each of its
     guard() events knew (wk_Rg); guard() publishes what it knew (wk_Gg);
   - a store u that is not written back, followed by a guard() g of its context, conveys at most
     what g knew (wk_ug); a store of g's context made after g (written back or not) conveys what
     g knew (wk_gw); a later guard() knows what an earlier one knew (wk_gg).
   wk_ug, wk_gg, wk_gw are the three links of a guard() pair: a store u, then a guard() of its
   context, then (later in time) a guard() of another context, then a store w of that context:
   w conveys what u conveys (sync_wc). *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB M2DQWBK1 M2DQWBK2 M2DQWBK3 M2DQWBK5 M2DQWBK13 M2DQWBK20 M2DQWBK21.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

Record WK (s : st) : Prop := {
  wk_tm : tm s = length (lg s);
  wk_et : forall g e, ent s g = Some e -> et e = g;
  wk_ids : forall x t, In t (ids (hs s x)) -> t < tm s;
  wk_R : forall u e, ent s u = Some e -> ew e = true -> vsub (wc s u) (vor (vR (cs s (ec e))) (vone u));
  wk_Rg : forall g e, ent s g = Some e -> isFF s g e -> vsub (eP e) (vR (cs s (ec e)));
  wk_Gg : forall g e, ent s g = Some e -> isFF s g e -> vsub (eP e) (vG s);
  wk_ug : forall u eu g eg x, ent s u = Some eu -> ew eu = true -> In (u, false) (hs s x) ->
    ent s g = Some eg -> isFF s g eg -> ec eu = ec eg -> u < g -> vsub (wc s u) (vor (eP eg) (vone u));
  wk_gw : forall g eg w e, ent s g = Some eg -> isFF s g eg -> ent s w = Some e -> ew e = true ->
    ec e = ec eg -> g < w -> vsub (eP eg) (wc s w);
  wk_gg : forall g1 e1 g2 e2, ent s g1 = Some e1 -> isFF s g1 e1 -> ent s g2 = Some e2 -> isFF s g2 e2 ->
    g1 < g2 -> vsub (eP e1) (eP e2)
}.

Lemma WK_init : WK sinit.
Proof.
  constructor; unfold ent; cbn; intros.
  all: try (match goal with H : nth_error [] ?t = Some _ |- _ => destruct t; discriminate end).
  all: try contradiction. reflexivity.
Qed.

(* ---------- a step of A ---------- *)
Section StepA.
Variables (p : prog) (s s' : st).
Hypothesis H : step p s s'.
Hypothesis Wk : WK s.
Hypothesis Km : KM s.

Let Tl := wk_tm s Wk.
Let Mo := proj1 (step_km p s s' H Km).

Lemma ent_cases : forall g e, ent s' g = Some e -> (g < tm s /\ ent s g = Some e) \/ g = tm s.
Proof.
  intros g e E. pose proof (sh_ent_lt p s s' H Tl g e E) as L. destruct (Nat.eq_dec g (tm s)) as [->|N]; [right; reflexivity|].
  left. split; [lia|]. rewrite <- (sh_old p s s' H Tl g ltac:(lia)). exact E.
Qed.

(* the new entry's context and time *)
Lemma new_et : forall e, ent s' (tm s) = Some e -> et e = tm s.
Proof.
  intros e Ee.
  destruct (stepQ_split p s s' H) as [[HA _]|RF]; [|exfalso; unfold ent in Ee; rewrite (rfx_lg _ _ RF) in Ee; exact (ent_none _ _ _ Tl Ee)].
  destruct (step_cases p s s' HA) as
    [(c & i & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & _ & _ & He & _ & ->)
    |[(c & k & d & B & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & He & _ & ->)
    |[(c & d & _ & _ & _ & _ & _ & _ & ->)
    |[(c & k & xs & B & m' & a & K & u & w & bv & _ & _ & _ & _ & _ & He & _ & ->)
    |[(c & _ & _ & _ & _ & _ & _ & _ & ->)
    |(cX & jX & bX & BX & oX & _ & _ & _ & ->)]]]]].
  6: exfalso; unfold ent, scfix0 in Ee; cbn [lg] in Ee; rewrite lg_flp in Ee; exact (ent_none _ _ _ Tl Ee).
  3, 5: exfalso; unfold ent in Ee; first [unfold smatch in Ee|unfold sskip in Ee]; cbn [lg] in Ee; exact (ent_none _ _ _ Tl Ee).
  all: unfold ent, sord, searly, set_es, searly0, evs, sread in *; cbn [lg] in Ee; pose proof (ent_new _ _ _ _ Tl Ee) as ->; reflexivity.
Qed.

Lemma ids_step : forall x t, In t (ids (hs s' x)) -> t < tm s'.
Proof.
  intros x t I.
  assert (G : forall t0, In t0 (ids (hs s x)) -> t0 < tm s') by
    (intros t0 I0; pose proof (wk_ids s Wk x t0 I0); destruct (sh_lg p s s' H Tl) as [(E & _)|(E & _)]; rewrite E; lia).
  destruct (stepQ_split p s s' H) as [[HA _]|RF]; [|apply G; rewrite (rfx_hs _ _ RF) in I; exact I].
  destruct (step_cases p s s' HA) as
    [(c & i & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & _ & _ & He & _ & ->)
    |[(c & k & d & B & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & He & _ & ->)
    |[(c & d & _ & _ & _ & _ & _ & _ & ->)
    |[(c & k & xs & B & m' & a & K & u & w & bv & _ & _ & _ & _ & _ & He & _ & ->)
    |[(c & _ & _ & _ & _ & _ & _ & _ & ->)
    |(cX & jX & bX & BX & oX & _ & _ & _ & ->)]]]]].
  6: apply G; unfold scfix0 in I; cbn [hs] in I; rewrite hs_flp in I; exact I.
  3, 5: apply G; exact I.
  all: unfold sord, searly, set_es, searly0, evs, sread in *; cbn [hs tm] in *.
  all: destruct (eff_hist _ _ _ _ _ _ _ _ _ He) as [Eh|(xs0 & P)]; [apply G; cbn [tm]; rewrite Eh in I; exact I|].
  all: destruct (places_cell _ _ _ _ x P) as [E|(h1 & h2 & E1 & E2)]; [apply G; cbn [tm]; rewrite E in I; exact I|].
  all: rewrite E2 in I; apply in_ids_ins in I; destruct I as [I|I]; [cbn in I; lia|].
  all: apply G; cbn [tm]; cbn [mH mof] in E1; rewrite E1; exact I.
Qed.

Theorem WK_stepA : WK s'.
Proof.
  destruct Mo as (MG & MC).
  assert (OldFF : forall g e, ent s' g = Some e -> isFF s' g e -> g < tm s -> ent s g = Some e /\ isFF s g e).
  { intros g e E F L. split; [rewrite <- (sh_old p s s' H Tl g L); exact E|exact (sh_isFF_old p s s' H Tl g e L E F)]. }
  constructor.
  - exact (sh_tm p s s' H Tl).
  - intros g e E. destruct (ent_cases g e E) as [(_ & E0)| ->]; [exact (wk_et s Wk g e E0)|exact (new_et e E)].
  - exact ids_step.
  - intros u e E Ew. destruct (ent_cases u e E) as [(L & E0)| ->].
    + rewrite (sh_wc_old p s s' H Tl u L). intros z Z. destruct (wk_R s Wk u e E0 Ew z Z) as [Z'|Z']; [left; exact (proj1 (proj2 (proj2 (MC (ec e)))) z Z')|right; exact Z'].
    + destruct (sh_new p s s' H Tl e E) as (_ & W2 & _). rewrite (W2 Ew). intros z [Z|Z]; [left; exact (proj1 (proj2 (proj2 (MC (ec e)))) z Z)|right; exact Z].
  - intros g e E F. destruct (ent_cases g e E) as [(L & E0)| ->].
    + destruct (OldFF g e E F L) as [_ F0]. intros z Z. exact (proj1 (proj2 (proj2 (MC (ec e)))) z (wk_Rg s Wk g e E0 F0 z Z)).
    + destruct (sh_new p s s' H Tl e E) as (_ & _ & _ & F4). exact (proj1 (proj2 (proj2 (F4 F)))).
  - intros g e E F. destruct (ent_cases g e E) as [(L & E0)| ->].
    + destruct (OldFF g e E F L) as [_ F0]. intros z Z. exact (MG z (wk_Gg s Wk g e E0 F0 z Z)).
    + destruct (sh_new p s s' H Tl e E) as (_ & _ & _ & F4). exact (proj2 (proj2 (proj2 (F4 F)))).
  - intros u eu g eg x Eu Ew Iu Eg Fg Ec Lt. destruct (ent_cases g eg Eg) as [(L & E0)| ->].
    + destruct (OldFF g eg Eg Fg L) as [_ F0]. assert (Lu : u < tm s) by lia.
      assert (Eu0 : ent s u = Some eu) by (rewrite <- (sh_old p s s' H Tl u Lu); exact Eu).
      destruct (sh_hs p s s' H Tl x u Iu) as [Iu0|Eq]; [|lia].
      rewrite (sh_wc_old p s s' H Tl u Lu). exact (wk_ug s Wk u eu g eg x Eu0 Ew Iu0 E0 F0 Ec Lt).
    + assert (Eu0 : ent s u = Some eu) by (rewrite <- (sh_old p s s' H Tl u Lt); exact Eu).
      destruct (sh_new p s s' H Tl eg Eg) as (_ & _ & _ & F4). destruct (F4 Fg) as (_ & Ep & _ & _).
      rewrite (sh_wc_old p s s' H Tl u Lt). rewrite Ep. intros z Z. destruct (wk_R s Wk u eu Eu0 Ew z Z) as [Z'|Z']; [|right; exact Z'].
      left. rewrite Ec in Z'. destruct (proj1 (Km (ec eg)) z Z') as [Z2|Z2]; [left; left; exact Z2|left; right; exact Z2].
  - intros g eg w e Eg Fg Ew Eww Ec Lt. destruct (ent_cases w e Ew) as [(L & E0)| ->].
    + assert (Lg : g < tm s) by lia. destruct (OldFF g eg Eg Fg Lg) as [Eg0 F0].
      rewrite (sh_wc_old p s s' H Tl w L). exact (wk_gw s Wk g eg w e Eg0 F0 E0 Eww Ec Lt).
    + destruct (OldFF g eg Eg Fg Lt) as [Eg0 F0]. destruct (sh_new p s s' H Tl e Ew) as (_ & W2 & _).
      rewrite (W2 Eww). intros z Z. left. rewrite Ec. exact (wk_Rg s Wk g eg Eg0 F0 z Z).
  - intros g1 e1 g2 e2 E1 F1 E2 F2 Lt. destruct (ent_cases g2 e2 E2) as [(L & E0)| ->].
    + destruct (OldFF g1 e1 E1 F1 ltac:(lia)) as [E10 F10]. destruct (OldFF g2 e2 E2 F2 L) as [_ F20].
      exact (wk_gg s Wk g1 e1 g2 e2 E10 F10 E0 F20 Lt).
    + destruct (OldFF g1 e1 E1 F1 Lt) as [E10 F10]. destruct (sh_new p s s' H Tl e2 E2) as (_ & _ & _ & F4).
      destruct (F4 F2) as (_ & Ep & _ & _). rewrite Ep. intros z Z. right. exact (wk_Gg s Wk g1 e1 E10 F10 z Z).
Qed.
End StepA.

(* ---------- the write-back patch ---------- *)
Section Wb.
Set Default Proof Using "All".
Variables (s : st) (c k t : nat) (H'' : cell -> hist).
Hypothesis Ok : wbok s c k t H''.
Hypothesis Wk : WK s.
Hypothesis Et : forall e, ent s t = Some e -> ec e = c.
Hypothesis Fr : forall x, ~ In t (ids (hs s x)).
Hypothesis Lt : t < tm s.
Local Abbreviation s' := (wbst s c k t H'').

Lemma wb_ent : forall g e', ent s' g = Some e' -> exists e, ent s g = Some e /\ e' = sete t e.
Proof.
  intros g e' E. unfold ent, wbst in E. cbn [lg] in E. rewrite nth_setew in E.
  destruct (nth_error (lg s) g) as [e|] eqn:E0; [|discriminate]. injection E as <-. exists e. auto.
Qed.
Lemma sete_fields : forall e, ec (sete t e) = ec e /\ ek (sete t e) = ek e /\ eP (sete t e) = eP e /\ et (sete t e) = et e /\
  (ew (sete t e) = true -> et e = t \/ ew e = true).
Proof. intros e. unfold sete. destruct (Nat.eqb_spec (et e) t); cbn; auto 10. Qed.
Lemma wb_cs : forall c', ai (cs s' c') = ai (cs s c') /\ oc (cs s' c') = oc (cs s c') /\
  vR (cs s' c') = vR (cs s c') /\ vG s' = vG s /\ pcs s' = pcs s.
Proof.
  intros c'. unfold wbst. cbv zeta. cbn [cs vG pcs]. destruct (Nat.eq_dec c' c) as [->|N].
  - rewrite upd_eq. cbn. auto.
  - rewrite upd_neq by exact N. auto.
Qed.
Lemma wb_isFF : forall g e, isFF s' g (sete t e) -> isFF s g e.
Proof.
  intros g e (Fa & Fp & Fo). destruct (sete_fields e) as (E1 & E2 & _). rewrite E1, E2 in *.
  destruct (wb_cs (ec e)) as (A1 & A2 & _ & _ & A5). rewrite A1 in Fa. rewrite A2 in Fo. rewrite A5 in Fp. split; auto.
Qed.
Lemma wb_wc : forall y, y <> t -> wc s' y = wc s y.
Proof. intros y N. unfold wbst. cbn [wc]. unfold upd. destruct (Nat.eqb_spec y t); [congruence|reflexivity]. Qed.
Lemma wb_wct : wc s' t = vor (vR (cs s c)) (vone t).
Proof. unfold wbst. cbn [wc]. apply upd_eq. Qed.

Theorem WK_wbst : WK s'.
Proof.
  constructor.
  - unfold wbst. cbn [tm lg]. unfold setew. rewrite length_map. exact (wk_tm s Wk).
  - intros g e' E. destruct (wb_ent g e' E) as (e & E0 & ->). destruct (sete_fields e) as (_ & _ & _ & E4 & _). rewrite E4. exact (wk_et s Wk g e E0).
  - intros x t0 I. unfold wbst in I |- *. cbn [hs tm] in I |- *.
    destruct (enters_tied_cell _ _ _ _ _ x Ok) as [E|(h1 & h2 & E1 & E2 & _)]; [rewrite E in I; exact (wk_ids s Wk x t0 I)|].
    rewrite E2 in I. apply in_ids_ins in I. destruct I as [I|I]; [cbn in I; lia|]. rewrite <- E1 in I. exact (wk_ids s Wk x t0 I).
  - intros u e' E Ew. destruct (wb_ent u e' E) as (e & E0 & ->). destruct (sete_fields e) as (F1 & _ & _ & _ & F5).
    rewrite F1. destruct (wb_cs (ec e)) as (_ & _ & R1 & _). rewrite R1.
    destruct (Nat.eq_dec u t) as [->|N].
    + rewrite wb_wct, (Et e E0). intros z Z; exact Z.
    + rewrite (wb_wc u N). destruct (F5 Ew) as [X|X]; [rewrite (wk_et s Wk u e E0) in X; congruence|exact (wk_R s Wk u e E0 X)].
  - intros g e' E F. destruct (wb_ent g e' E) as (e & E0 & ->). destruct (sete_fields e) as (F1 & _ & F3 & _).
    rewrite F1, F3. destruct (wb_cs (ec e)) as (_ & _ & R1 & _). rewrite R1. exact (wk_Rg s Wk g e E0 (wb_isFF g e F)).
  - intros g e' E F. destruct (wb_ent g e' E) as (e & E0 & ->). destruct (sete_fields e) as (_ & _ & F3 & _).
    rewrite F3. destruct (wb_cs c) as (_ & _ & _ & G1 & _). rewrite G1. exact (wk_Gg s Wk g e E0 (wb_isFF g e F)).
  - intros u eu' g eg' x Eu Ew Iu Eg Fg Ec L.
    destruct (wb_ent u eu' Eu) as (eu & Eu0 & ->). destruct (wb_ent g eg' Eg) as (eg & Eg0 & ->).
    destruct (sete_fields eu) as (U1 & _ & _ & _ & U5). destruct (sete_fields eg) as (G1 & _ & G3 & _).
    rewrite U1, G1 in Ec. rewrite G3.
    assert (Iu0 : In (u, false) (hs s x)).
    { unfold wbst in Iu. cbn [hs] in Iu. destruct (enters_tied_cell _ _ _ _ _ x Ok) as [E|(h1 & h2 & E1 & E2 & _)]; [rewrite E in Iu; exact Iu|].
      rewrite E2 in Iu. rewrite E1. apply in_app_iff in Iu. apply in_app_iff. destruct Iu as [Iu|[Iu|Iu]]; [left; exact Iu|discriminate|right; exact Iu]. }
    assert (N : u <> t) by (intros ->; exact (Fr x (in_map fst _ _ Iu0))).
    rewrite (wb_wc u N). destruct (U5 Ew) as [X|X]; [rewrite (wk_et s Wk u eu Eu0) in X; congruence|].
    exact (wk_ug s Wk u eu g eg x Eu0 X Iu0 Eg0 (wb_isFF g eg Fg) Ec L).
  - intros g eg' w e' Eg Fg Ew Eww Ec L.
    destruct (wb_ent g eg' Eg) as (eg & Eg0 & ->). destruct (wb_ent w e' Ew) as (e & E0 & ->).
    destruct (sete_fields eg) as (G1 & _ & G3 & _). destruct (sete_fields e) as (F1 & _ & _ & _ & F5).
    rewrite G1, F1 in Ec. rewrite G3. pose proof (wb_isFF g eg Fg) as Fg0.
    destruct (Nat.eq_dec w t) as [->|N].
    + rewrite wb_wct. intros z Z. left. rewrite <- (Et e E0), Ec. exact (wk_Rg s Wk g eg Eg0 Fg0 z Z).
    + rewrite (wb_wc w N). destruct (F5 Eww) as [X|X]; [rewrite (wk_et s Wk w e E0) in X; congruence|].
      exact (wk_gw s Wk g eg w e Eg0 Fg0 E0 X Ec L).
  - intros g1 e1' g2 e2' E1 F1 E2 F2 L.
    destruct (wb_ent g1 e1' E1) as (e1 & E10 & ->). destruct (wb_ent g2 e2' E2) as (e2 & E20 & ->).
    destruct (sete_fields e1) as (_ & _ & A3 & _). destruct (sete_fields e2) as (_ & _ & B3 & _). rewrite A3, B3.
    exact (wk_gg s Wk g1 e1 g2 e2 E10 (wb_isFF g1 e1 F1) E20 (wb_isFF g2 e2 F2) L).
Qed.
End Wb.

(* ---------- every runWB ---------- *)
Theorem WK_run : forall p, wf p -> forall s, runWB p s -> WK s.
Proof.
  intros p W s R. induction R as [|s s' R IH St]; [exact WK_init|].
  pose proof (runWB_KM p s R) as Km.
  assert (KRof : forall s0, runWB p s0 -> exists sw sA, run p sA /\ rel sw s0 sA /\ KR False (fun _ => True) sw s0 sA).
  { intros s0 R0. exact (runWBK p W False (fun _ => True) s0 R0 (fun f => match f with end) (fun f => match f with end)). }
  inversion St as [s0 s1 St0 FH | s0 s1 c k t1 H'' St0 Ps Fr Ok | s0 c k t1 xs H'' Lk Oc Oh _ _ _ Fr Ok]; subst.
  - exact (WK_stepA p s s' St0 IH Km).
  - destruct Ps as (NW & T1 & _ & _ & _ & _ & Oh1 & _). pose proof (WK_stepA p s s1 St0 IH Km) as Wk1.
    assert (R1 : runWB p s1) by (apply (wrS p s s1 R); apply wbA; [exact St0|exact (nowrite_fhsafe _ _ NW)]).
    destruct (KRof s1 R1) as (sw & sA & RA & Rl & K).
    destruct (i_ohW p False (fun _ => True) sw s1 sA RA Rl K c k t1 Oh1) as (e0 & E0 & Ec0 & _).
    apply WK_wbst; [exact Ok|exact Wk1| | |].
    + intros e E. rewrite E0 in E. injection E as <-. exact Ec0.
    + intros x I. rewrite (NW x) in I. exact (Fr x I).
    + rewrite (wk_tm s1 Wk1). unfold ent in E0. apply nth_error_Some. congruence.
  - destruct (KRof s R) as (sw & sA & RA & Rl & K).
    destruct (i_ohW p False (fun _ => True) sw s sA RA Rl K c k t1 Oh) as (e0 & E0 & Ec0 & _).
    apply WK_wbst; [exact Ok|exact IH| | |].
    + intros e E. rewrite E0 in E. injection E as <-. exact Ec0.
    + exact Fr.
    + rewrite (wk_tm s IH). unfold ent in E0. apply nth_error_Some. congruence.
Qed.

(* ---------- the chain through a guard() pair ---------- *)
(* a store u not written back, a guard() g1 of its context after it, a guard() g2 after g1, and a
   store w of g2's context after g2: w conveys what u conveys (u itself aside) *)
Theorem sync_wc : forall s, WK s -> forall u eu g1 e1 g2 e2 w ew0 x,
  ent s u = Some eu -> ew eu = true -> In (u, false) (hs s x) ->
  ent s g1 = Some e1 -> isFF s g1 e1 -> ec eu = ec e1 -> u < g1 ->
  ent s g2 = Some e2 -> isFF s g2 e2 -> g1 < g2 ->
  ent s w = Some ew0 -> ew ew0 = true -> ec ew0 = ec e2 -> g2 < w ->
  forall z, wc s u z -> z = u \/ wc s w z.
Proof.
  intros s Wk u eu g1 e1 g2 e2 w ew0 x Eu Ewu Iu E1 F1 C1 L1 E2 F2 L2 Ew Eww C2 L3 z Z.
  destruct (wk_ug s Wk u eu g1 e1 x Eu Ewu Iu E1 F1 C1 L1 z Z) as [Z1|Z1]; [|left; exact Z1].
  right. exact (wk_gw s Wk g2 e2 w ew0 E2 F2 Ew Eww C2 L3 z (wk_gg s Wk g1 e1 g2 e2 E1 F1 E2 F2 L2 z Z1)).
Qed.

Print Assumptions WK_run.
Print Assumptions sync_wc.
