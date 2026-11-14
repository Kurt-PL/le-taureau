(* Positive instance of M2CasErf.erf_eq_run on M2DQ (port of
   M2CasErfInst.v): the CAS2 run of M2DQCas2Inst is a runQ and an M2 run;
   slot 2 of context 0 has both halves recorded, and the two log entries
   carry the same erf. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Inv M2DQ M2CasErf M2DQCas2Inst.

Lemma CAS2_erf_Q : exists s t1 t2 E1 E2, runQ CAS2 s /\ oh (cs s 0) 2 = Some t1 /\ oc (cs s 0) 2 = Some t2 /\
  ent s t1 = Some E1 /\ ent s t2 = Some E2 /\ erf E1 = erf E2.
Proof.
  destruct CAS2_allowed_Q as (s & Q & R & _ & _ & _ & _ & _ & H1 & H2).
  destruct (oh (cs s 0) 2) as [t1|] eqn:O1; [|exfalso; apply H1; reflexivity].
  destruct (oc (cs s 0) 2) as [t2|] eqn:O2; [|exfalso; apply H2; reflexivity].
  destruct (erf_eq_run CAS2 s R 0 2 t1 t2 O1 O2) as (E1 & E2 & A & B & C).
  exists s, t1, t2, E1, E2. repeat split; auto.
Qed.

Print Assumptions CAS2_erf_Q.
