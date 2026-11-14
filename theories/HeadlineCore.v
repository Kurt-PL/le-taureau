(* Headline results of the M2DQ model, part 1 of 3: the invariants, no value out of thin air,
   the interface guarantees, fenced SC and DRF-SC, and every CAS in two parts.
   Print Assumptions on each. *)
Require Import M2DQInv M2DQOota M2DQIfaceInst M2DQIfaceUse M2DQInst.
Print Assumptions M2DQInv.IQ_run.
Print Assumptions M2DQOota.no_thin_air_Q.
Print Assumptions M2DQIfaceInst.m2dq_guarantees.
Print Assumptions M2DQIfaceUse.fenced_sc_dq.
Print Assumptions M2DQIfaceUse.drf_sc_dq.
Print Assumptions M2DQInst.cas_in_parts.
