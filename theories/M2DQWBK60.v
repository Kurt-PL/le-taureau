(* Part 60: J goes along every step of an A run whose step satisfies RaceStep
   (J_step: the six kinds of step, by M2DQWBK59.J_evs and J_same), hence along a run all of whose
   steps do (J_run_of). *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO M2Ev.
Require Import M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB.
Require Import M2DQWBK1 M2DQWBK57 M2DQWBK58 M2DQWBK59.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBQc M2DQWBK1Q M2DQShim.

Section S.
Variable p : prog.
Hypothesis W : wf p.

Theorem J_step : forall s s', run p s -> step p s s' -> J p s -> RaceStep p s s' -> J p s'.
Proof.
  intros s s' R St Js RS. pose proof St as St0.
  destruct (stepQ_split p s s' St) as [[HA _]|RF]; [|apply (J_same p W s _ R St0 Js); [intros c'; rfx_rw RF; auto|exact (rfx_vG _ _ RF)|exact (rfx_lg _ _ RF)]].
  destruct (step_cases p s s' HA) as
    [(c & i & m' & a & K & u & w & Hi & Hoc & _ & _ & _ & Hh & _ & _ & He & _ & ->)
    |[(c & k & d & B & m' & a & K & u & w & L1 & Hoc & _ & Hd & _ & _ & He & _ & ->)
    |[(c & d & H1 & H2 & H3 & _ & _ & _ & ->)
    |[(c & k & xs & B & m' & a & K & u & w & bv & L1 & Hoc & Hoh & _ & _ & He & _ & ->)
    |[(c & S1 & S2 & _ & _ & _ & _ & _ & ->)
    |(cX & jX & bX & BX & oX & HjX & HfX & HcX & ->)]]]]].
  - (* in order *)
    apply (J_evs p W s _ c i m' a K u w (newev s c (pcs s c) i K u w) R St0 Js RS);
      unfold sord, evs; cbn [cs pcs vP vA vO vOg vG lg ec ew erf]; try reflexivity.
    + intros c' N. rewrite upd_neq by exact N. reflexivity.
    + intros c' N. rewrite upd_neq by exact N. reflexivity.
    + rewrite upd_eq. reflexivity.
    + rewrite upd_eq. reflexivity.
    + rewrite upd_eq. reflexivity.
    + rewrite upd_eq. reflexivity.
    + exact He.
    + intros Fl [N1|(_ & Ac)].
      * rewrite (N1 (rg (cs s c))), Fl in Hi. discriminate.
      * rewrite Hi, Fl in Ac. discriminate.
  - (* early *)
    apply (J_evs p W s _ c (inst_of d) m' a K u w (newev s c k (inst_of d) K u w) R St0 Js RS);
      unfold searly, set_es, searly0, evs; cbn [cs pcs vP vA vO vOg vG lg ec ew erf]; try reflexivity.
    + intros c' N. rewrite upd_neq by exact N. reflexivity.
    + rewrite upd_eq. reflexivity.
    + rewrite upd_eq. reflexivity.
    + rewrite upd_eq. reflexivity.
    + rewrite upd_eq. reflexivity.
    + exact He.
    + intros Fl Nf. destruct Hd as [(_ & Eo)|(t1 & xs & ev & nv & _ & Ed & _)].
      * exact (NF_no_early p s c _ _ d u B Nf Eo).
      * rewrite Ed in Fl. discriminate.
  - (* reaching an access that happened early *)
    apply (J_same p W s _ R St0 Js); unfold smatch; cbn [cs vG lg]; [|reflexivity|reflexivity].
    intros c'. destruct (Nat.eqb_spec c' c) as [->|N]; [rewrite upd_eq; cbn; auto|rewrite upd_neq by exact N; auto].
  - (* a CAS's read alone *)
    apply (J_evs p W s _ c (ILd Plain xs (fun _ => true)) m' a K u w (newevh s c k (ILd Plain xs (fun _ => true)) K u w) R St0 Js RS);
      unfold sread; cbn [cs pcs vP vA vO vOg vG lg ec ew erf]; try reflexivity.
    + intros c' N. rewrite upd_neq by exact N. reflexivity.
    + rewrite upd_eq. reflexivity.
    + rewrite upd_eq. reflexivity.
    + rewrite upd_eq. reflexivity.
    + rewrite upd_eq. reflexivity.
    + exact He.
    + intros Fl. discriminate.
  - (* passing an instruction that does not execute *)
    apply (J_same p W s _ R St0 Js); unfold sskip; cbn [cs vG lg]; [|reflexivity|reflexivity].
    intros c'. destruct (Nat.eqb_spec c' c) as [->|N]; [rewrite upd_eq; cbn; auto|rewrite upd_neq by exact N; auto].
  - (* a result fixed *)
    apply (J_same p W s _ R St0 Js); unfold scfix0; cbn [cs vG lg].
    + intros c'. destruct (Nat.eqb_spec c' cX) as [->|N]; [rewrite upd_eq; cbn|rewrite upd_neq by exact N].
      all: rewrite (vP_flp s cX oX bX), (vA_flp s cX oX bX), (vO_flp s cX oX bX), (vOg_flp s cX oX bX); auto.
    + exact (vG_flp s cX oX bX).
    + exact (lg_flp s cX oX bX).
Qed.

(* J along a run whose steps satisfy RaceStep when the state after them is evok *)
Theorem J_run_of : (forall s1 s2, run p s1 -> step p s1 s2 -> evok s2 -> RaceStep p s1 s2) ->
  forall s, run p s -> evok s -> J p s.
Proof.
  intros RS s R. induction R as [|s0 s1 R IH St]; intros EV; [exact (J_init p)|].
  apply (J_step s0 s1 R St); [exact (IH (evok_stepQ p s0 s1 R St EV))|exact (RS s0 s1 R St EV)].
Qed.
End S.

Print Assumptions J_step.
Print Assumptions J_run_of.
