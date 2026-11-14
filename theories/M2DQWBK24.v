(* Part 24: a store right after a guard() of its context (both-fenced case of the
   write-back cover).  WKF (every runWB): while a guard() event g is the last event of its
   context, the context's release view is within what g knew (wf_last); so a store u not written
   back that is the first event of its context after g conveys at most what g knew (wf_fa), and
   g published that (M2DQWBK22.wk_Gg): fa_wc. *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB M2DQWBK1 M2DQWBK2 M2DQWBK3 M2DQWBK5 M2DQWBK13 M2DQWBK20 M2DQWBK21 M2DQWBK22.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

(* no event of context c has a time strictly between a and b *)
Definition quiet (s : st) (c a b : nat) : Prop := forall t e, a < t -> t < b -> ent s t = Some e -> ec e <> c.

Record WKF (s : st) : Prop := {
  wf_last : forall g e, ent s g = Some e -> isFF s g e -> quiet s (ec e) g (S (length (lg s))) ->
    vsub (vR (cs s (ec e))) (eP e);
  wf_fa : forall g eg u eu x, ent s g = Some eg -> isFF s g eg -> ent s u = Some eu -> ew eu = true ->
    In (u, false) (hs s x) -> ec eu = ec eg -> g < u -> quiet s (ec eg) g u -> vsub (wc s u) (vor (eP eg) (vone u))
}.

Lemma WKF_init : WKF sinit.
Proof. constructor; unfold ent; cbn; intros; match goal with H : nth_error [] ?t = Some _ |- _ => destruct t; discriminate end. Qed.

Section StepA.
Set Default Proof Using "All".
Variables (p : prog) (s s' : st).
Hypothesis H : step p s s'.
Hypothesis Wk : WK s.
Hypothesis Wf : WKF s.
Let Tl := wk_tm s Wk.

(* the release view of a context changes only by its own event *)
Lemma sh_R : forall c', (forall e, ent s' (tm s) = Some e -> ec e <> c') -> vR (cs s' c') = vR (cs s c').
Proof.
  intros c' N.
  destruct (stepQ_split p s s' H) as [[HA _]|RF]; [|exact (rfx_vR _ _ RF c')].
  destruct (step_cases p s s' HA) as
    [(c & i & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & _ & _ & He & _ & ->)
    |[(c & k & d & B & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & He & _ & ->)
    |[(c & d & _ & _ & _ & _ & _ & _ & ->)
    |[(c & k & xs & B & m' & a & K & u & w & bv & _ & _ & _ & _ & _ & He & _ & ->)
    |[(c & _ & _ & _ & _ & _ & _ & _ & ->)
    |(cX & jX & bX & BX & oX & _ & _ & _ & ->)]]]]].
  6: unfold scfix0; cbn [cs]; destruct (Nat.eq_dec c' cX) as [->|Nc]; [rewrite upd_eq; cbn [vR]; apply vR_flp|rewrite upd_neq by exact Nc; apply vR_flp].
  3, 5: unfold smatch, sskip; cbn [cs]; destruct (Nat.eq_dec c' c) as [->|Nc]; [rewrite upd_eq; reflexivity|rewrite upd_neq by exact Nc; reflexivity].
  all: unfold sord, searly, set_es, searly0, evs, sread in *; cbn [cs lg] in *.
  all: assert (Nc : c' <> c) by (intros ->; eapply N; [unfold ent; cbn [lg]; rewrite nth_error_app2 by (rewrite Tl; lia); rewrite Tl, Nat.sub_diag; reflexivity|reflexivity]).
  all: rewrite upd_neq by exact Nc; reflexivity.
Qed.

(* a new guard() event releases at most what it knew *)
Lemma sh_newR : forall e, ent s' (tm s) = Some e -> isFF s' (tm s) e -> vsub (vR (cs s' (ec e))) (eP e).
Proof.
  intros e Ee F.
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
  all: unfold ent, sord, searly, set_es, searly0, evs, sread in *; cbn [lg cs pcs] in *; pose proof (ent_new _ _ _ _ Tl Ee) as ->; cbn [ec ek eP] in *.
  all: destruct F as (Fa & Fp & Fo); cbn [ec ek cs pcs oc] in Fa, Fp, Fo; rewrite upd_eq in Fa; cbn [ai] in Fa; rewrite upd_eq; cbn [vR].
  - rewrite upd_eq in Fa. rewrite Fa in He. destruct (eff_ffK _ _ _ _ _ _ _ _ He) as (-> & -> & _). cbn. unfold vsub, vor. intros z Z; tauto.
  - exfalso. lia.
  - exfalso. rewrite upd_eq in Fa. discriminate.
Qed.

Theorem WKF_stepA : WKF s'.
Proof.
  assert (OldE : forall g, g < tm s -> ent s' g = ent s g) by exact (sh_old p s s' H Tl).
  assert (Len : length (lg s) <= length (lg s')) by (destruct (sh_lg p s s' H Tl) as [(_ & E)|(_ & e & E)]; rewrite E; [lia|rewrite length_app; cbn; lia]).
  assert (NoNew : forall e, ent s (tm s) = Some e -> False) by (intros e E; exact (ent_none _ _ _ Tl E)).
  assert (Cases : forall g e, ent s' g = Some e -> (g < tm s /\ ent s g = Some e) \/ g = tm s).
  { intros g e E. pose proof (sh_ent_lt p s s' H Tl g e E) as L. destruct (Nat.eq_dec g (tm s)) as [Eq|N]; [right; exact Eq|].
    left. split; [lia|]. rewrite <- (OldE g ltac:(lia)). exact E. }
  (* quiet up to the end of s, from quiet in s' up to b >= tm s *)
  assert (QS : forall c a b, tm s <= b -> quiet s' c a b -> quiet s c a (S (length (lg s)))).
  { intros c a b Lb Q t e L1 L2 E. destruct (Nat.eq_dec t (tm s)) as [->|N]; [exact (False_ind _ (NoNew e E))|].
    apply (Q t e L1 ltac:(lia)). rewrite (OldE t ltac:(lia)). exact E. }
  constructor.
  - intros g e E F Q. destruct (Cases g e E) as [(L & E0)| ->].
    + pose proof (sh_isFF_old p s s' H Tl g e L E F) as F0.
      rewrite (sh_R (ec e)).
      * apply (wf_last s Wf g e E0 F0). apply (QS (ec e) g (S (length (lg s')))); [lia|exact Q].
      * intros e1 E1. apply (Q (tm s) e1 L ltac:(lia) E1).
    + exact (sh_newR e E F).
  - intros g eg u eu x Eg Fg Eu Ew Iu Ec Lgu Q.
    assert (Lu : u <= tm s) by exact (sh_ent_lt p s s' H Tl u eu Eu).
    assert (Lg : g < tm s) by lia.
    assert (Eg0 : ent s g = Some eg) by (rewrite <- (OldE g Lg); exact Eg).
    pose proof (sh_isFF_old p s s' H Tl g eg Lg Eg Fg) as Fg0.
    destruct (Nat.eq_dec u (tm s)) as [->|Nu].
    + destruct (sh_new p s s' H Tl eu Eu) as (_ & W2 & _). rewrite (W2 Ew). rewrite Ec.
      intros z [Z|Z]; [left|right; exact Z].
      apply (wf_last s Wf g eg Eg0 Fg0); [|exact Z].
      intros t e L1 L2 E. destruct (Nat.eq_dec t (tm s)) as [->|N]; [exact (False_ind _ (NoNew e E))|].
      apply (Q t e L1 ltac:(lia)). rewrite (OldE t ltac:(lia)). exact E.
    + assert (Lu' : u < tm s) by lia.
      assert (Eu0 : ent s u = Some eu) by (rewrite <- (OldE u Lu'); exact Eu).
      destruct (sh_hs p s s' H Tl x u Iu) as [Iu0|Eq]; [|lia].
      rewrite (sh_wc_old p s s' H Tl u Lu').
      apply (wf_fa s Wf g eg u eu x Eg0 Fg0 Eu0 Ew Iu0 Ec Lgu).
      intros t e L1 L2 E. apply (Q t e L1 L2). rewrite (OldE t ltac:(lia)). exact E.
Qed.
End StepA.

Lemma sete_f : forall t e, ec (sete t e) = ec e /\ ek (sete t e) = ek e /\ eP (sete t e) = eP e /\ et (sete t e) = et e /\
  (ew (sete t e) = true -> et e = t \/ ew e = true).
Proof. intros t e. unfold sete. destruct (Nat.eqb_spec (et e) t); cbn; auto 10. Qed.

Section Wb.
Set Default Proof Using "All".
Variables (s : st) (c k t : nat) (H'' : cell -> hist).
Hypothesis Ok : wbok s c k t H''.
Hypothesis Wk : WK s.
Hypothesis Wf : WKF s.
Hypothesis Et : forall e, ent s t = Some e -> ec e = c.
Hypothesis Fr : forall x, ~ In t (ids (hs s x)).
Hypothesis Lt : t < tm s.
Local Abbreviation s' := (wbst s c k t H'').

Lemma wbq : forall c0 a b, quiet s' c0 a b -> quiet s c0 a b.
Proof.
  intros c0 a b Q t0 e L1 L2 E. destruct (sete_f t e) as (F1 & _).
  rewrite <- F1. apply (Q t0 (sete t e) L1 L2). unfold ent, wbst. cbn [lg]. rewrite nth_setew. unfold ent in E. rewrite E. reflexivity.
Qed.

Theorem WKF_wbst : WKF s'.
Proof.
  assert (Ln : length (lg s') = length (lg s)) by (unfold wbst; cbn [lg]; unfold setew; apply length_map).
  constructor.
  - intros g e' E F Q. destruct (wb_ent s c k t H'' Ok Wk Et Fr Lt g e' E) as (e & E0 & ->).
    destruct (sete_f t e) as (F1 & _ & F3 & _). rewrite F1, F3 in *.
    destruct (wb_cs s c k t H'' Ok Wk Et Fr Lt (ec e)) as (_ & _ & R1 & _). rewrite R1.
    apply (wf_last s Wf g e E0 (wb_isFF s c k t H'' Ok Wk Et Fr Lt g e F)). rewrite <- Ln. exact (wbq _ _ _ Q).
  - intros g eg' u eu' x Eg Fg Eu Ew Iu Ec L Q.
    destruct (wb_ent s c k t H'' Ok Wk Et Fr Lt u eu' Eu) as (eu & Eu0 & ->).
    destruct (wb_ent s c k t H'' Ok Wk Et Fr Lt g eg' Eg) as (eg & Eg0 & ->).
    destruct (sete_f t eu) as (U1 & _ & _ & _ & U5). destruct (sete_f t eg) as (G1 & _ & G3 & _).
    rewrite U1, G1 in Ec. rewrite G3. rewrite G1 in Q.
    assert (Iu0 : In (u, false) (hs s x)).
    { unfold wbst in Iu. cbn [hs] in Iu. destruct (enters_tied_cell _ _ _ _ _ x Ok) as [E|(h1 & h2 & E1 & E2 & _)]; [rewrite E in Iu; exact Iu|].
      rewrite E2 in Iu. rewrite E1. apply in_app_iff in Iu. apply in_app_iff. destruct Iu as [Iu|[Iu|Iu]]; [left; exact Iu|discriminate|right; exact Iu]. }
    assert (N : u <> t) by (intros ->; exact (Fr x (in_map fst _ _ Iu0))).
    rewrite (wb_wc s c k t H'' Ok Wk Et Fr Lt u N). destruct (U5 Ew) as [X|X]; [rewrite (wk_et s Wk u eu Eu0) in X; congruence|].
    exact (wf_fa s Wf g eg u eu x Eg0 (wb_isFF s c k t H'' Ok Wk Et Fr Lt g eg Fg) Eu0 X Iu0 Ec L (wbq _ _ _ Q)).
Qed.
End Wb.

Theorem WKF_run : forall p, wf p -> forall s, runWB p s -> WKF s.
Proof.
  intros p W s R. induction R as [|s s' R IH St]; [exact WKF_init|].
  pose proof (WK_run p W s R) as Wk.
  assert (KRof : forall s0, runWB p s0 -> exists sw sA, run p sA /\ rel sw s0 sA /\ KR False (fun _ => True) sw s0 sA).
  { intros s0 R0. exact (runWBK p W False (fun _ => True) s0 R0 (fun f => match f with end) (fun f => match f with end)). }
  inversion St as [s0 s1 St0 FH | s0 s1 c k t1 H'' St0 Ps Fr Ok | s0 c k t1 xs H'' Lk Oc Oh _ _ _ Fr Ok]; subst.
  - exact (WKF_stepA p s s' St0 Wk IH).
  - destruct Ps as (NW & T1 & _ & _ & _ & _ & Oh1 & _).
    assert (R1 : runWB p s1) by (apply (wrS p s s1 R); apply wbA; [exact St0|exact (nowrite_fhsafe _ _ NW)]).
    pose proof (WK_run p W s1 R1) as Wk1. pose proof (WKF_stepA p s s1 St0 Wk IH) as Wf1.
    destruct (KRof s1 R1) as (sw & sA & RA & Rl & K).
    destruct (i_ohW p False (fun _ => True) sw s1 sA RA Rl K c k t1 Oh1) as (e0 & E0 & Ec0 & _).
    apply (WKF_wbst s1 c k t1 H'' Ok Wk1 Wf1).
    + intros e E. rewrite E0 in E. injection E as <-. exact Ec0.
    + intros x I. rewrite (NW x) in I. exact (Fr x I).
    + rewrite (wk_tm s1 Wk1). unfold ent in E0. apply nth_error_Some. congruence.
  - destruct (KRof s R) as (sw & sA & RA & Rl & K).
    destruct (i_ohW p False (fun _ => True) sw s sA RA Rl K c k t1 Oh) as (e0 & E0 & Ec0 & _).
    apply (WKF_wbst s c k t1 H'' Ok Wk IH).
    + intros e E. rewrite E0 in E. injection E as <-. exact Ec0.
    + exact Fr.
    + rewrite (wk_tm s Wk). unfold ent in E0. apply nth_error_Some. congruence.
Qed.

(* both-fenced case of the cover: a store u not written back that is the first event of its
   context after a guard() event g conveys at most what guard() has published, and u itself *)
Theorem fa_wc : forall p, wf p -> forall s, runWB p s -> forall g eg u eu x,
  ent s g = Some eg -> isFF s g eg -> ent s u = Some eu -> ew eu = true -> In (u, false) (hs s x) ->
  ec eu = ec eg -> g < u -> quiet s (ec eg) g u -> vsub (wc s u) (vor (vG s) (vone u)).
Proof.
  intros p W s R g eg u eu x Eg Fg Eu Ew Iu Ec L Q z Z.
  destruct (wf_fa s (WKF_run p W s R) g eg u eu x Eg Fg Eu Ew Iu Ec L Q z Z) as [Z'|Z']; [|right; exact Z'].
  left. exact (wk_Gg s (WK_run p W s R) g eg Eg Fg z Z').
Qed.

Print Assumptions WKF_run.
Print Assumptions fa_wc.
