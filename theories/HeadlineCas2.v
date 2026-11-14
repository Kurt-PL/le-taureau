(* Headline results of the M2DQ model, part 3 of 3: compare-and-swap litmus results (continued).
   Print Assumptions on each. *)
Require Import M2DQBindCASRFWDInst M2DQSTWLOCKRELInst M2DQS3cLBWInst M2DQCasPDepInst M2DQCas2Inst M2DQCasErfInst.
Print Assumptions M2DQBindCASRFWDInst.CASRFWD_allowed_Q.
Print Assumptions M2DQSTWLOCKRELInst.LOCKREL_allowed_Q.
Print Assumptions M2DQS3cLBWInst.CASLBW_succ_Q.
Print Assumptions M2DQCasPDepInst.CASPDEP_allowed_Q.
Print Assumptions M2DQCas2Inst.CAS2_allowed_Q.
Print Assumptions M2DQCasErfInst.CAS2_erf_Q.
