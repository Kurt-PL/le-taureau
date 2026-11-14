(* Write-back over M2DQ: Print Assumptions on the headline results (small tuples). *)
Require Import M2DQWB M2DQWBK15 M2DQWBK69 M2DQWBK70Inst M2DQWBZero M2DQWBK30 M2DQWBLeadInst.
Print Assumptions M2DQWBK15.fenced_sc_WB.
Print Assumptions M2DQWBK69.drf_sc_WB.
Print Assumptions M2DQWBK70Inst.FWB_G2.
Print Assumptions M2DQWB.WB_sim.
Print Assumptions M2DQWB.Q_in_WB.
Print Assumptions M2DQWB.sim_stepQ.
Print Assumptions M2DQWBZero.lzp_not_tied.
Print Assumptions M2DQWBZero.LZP_not_cellful.
(* what a write conveys after a write-back by a CAS passed after its load part failed *)
Print Assumptions M2DQWBK30.wbc_wbP.
(* the write-back store as a write the CAS made: a read counted on with the CAS as its leader
   observes it (instance and negative instance) *)
Print Assumptions M2DQWBLeadInst.WBL_led.
Print Assumptions M2DQWBLeadInst.WBL_neg.
Check M2DQWBK15.fenced_sc_WB.
Check M2DQWBK69.drf_sc_WB.
Locate runWB.
