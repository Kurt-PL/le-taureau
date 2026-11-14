(* Headline results of the M2DQ model, part 2 of 3: compare-and-swap litmus results.
   Print Assumptions on each. *)
Require Import M2DQCasHoistX M2DQCasHoistXRun M2DQSpfhInst M2DQSpfdInst M2DQCasDepInst M2DQLitmusLBCWInst M2DQLitmusLBWCInst.
Check M2DQCasHoistX.CASHoistX_forbidden_Q.
Print Assumptions M2DQCasHoistX.CASHoistX_forbidden_Q.
Print Assumptions M2DQCasHoistXRun.CASHoistX_runs.
Print Assumptions M2DQSpfhInst.SPFH_Q.
Print Assumptions M2DQSpfdInst.SPFD_Q.
Print Assumptions M2DQCasDepInst.CASDEP_allowed_Q.
Print Assumptions M2DQLitmusLBCWInst.LBCW_allowed_Q.
Print Assumptions M2DQLitmusLBWCInst.LBWC_allowed_Q.
