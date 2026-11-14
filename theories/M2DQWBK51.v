(* Part 51: the entry a step logs, read off the entry (any state with tm = length lg,
   no run premise, so for the write-back state as well as for its image).  What it knows in order
   through guard() and took in order (eQ), and what it knows in order (eQc), are the views of its
   context before the step, gated by "it wrote, or it is a load that executes" (the load test
   taken on the instruction its slot records after the step). *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2DQWBK1 M2DQWBK20.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

Lemma step_newQ : forall p s s' e, step p s s' -> tm s = length (lg s) -> ent s' (tm s) = Some e ->
  let c := ec e in let fl := xload (ai (cs s' c) (ek e)) (rg (cs s c)) in
  eQ e = (if ew e || fl then vor (vOg (cs s c)) (tookord s c (vO (cs s c)) (erf e)) else vnil) /\
  eQc e = (if fl then vO (cs s c) else vnil).
Proof.
  intros p s s' e H Tl Ee.
  destruct (stepQ_split p s s' H) as [[HA _]|RF]; [|exfalso; unfold ent in Ee; rewrite (rfx_lg _ _ RF) in Ee; exact (ent_none _ _ _ Tl Ee)].
  destruct (step_cases p s s' HA) as
    [(c & i & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ->)
    |[(c & k & d & B & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & _ & _ & ->)
    |[(c & d & _ & _ & _ & _ & _ & _ & ->)
    |[(c & k & xs & B & m' & a & K & u & w & bv & _ & _ & _ & _ & _ & _ & _ & ->)
    |[(c & _ & _ & _ & _ & _ & _ & _ & ->)
    |(cX & jX & bX & BX & oX & _ & _ & _ & ->)]]]]].
  6: exfalso; unfold ent, scfix0 in Ee; cbn [lg] in Ee; rewrite lg_flp in Ee; exact (ent_none _ _ _ Tl Ee).
  3, 5: exfalso; unfold ent in Ee; first [unfold smatch in Ee|unfold sskip in Ee]; cbn [lg] in Ee; exact (ent_none _ _ _ Tl Ee).
  all: unfold sord, searly, set_es, searly0, evs, sread in *; cbn [lg] in Ee;
       unfold ent in Ee; pose proof (ent_new _ _ _ _ Tl Ee) as ->; cbn [ec ek ew eQ eQc erf cs]; rewrite upd_eq; cbn [ai];
       rewrite upd_eq; unfold evQ, evQc, xload; split; reflexivity.
Qed.

Print Assumptions step_newQ.
