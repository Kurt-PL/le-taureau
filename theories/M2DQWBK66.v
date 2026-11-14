(* Part 66: G2 = drf_sc over stepWB for every race-free programme for which the one
   corner CO2nK (M2DQWBK62) has its path: J holds at every evok image (M2DQWBK65.J_run), so
   M2DQWBK62.drf_sc_WB_of_J applies. *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO M2Ev M2DQWB.
Require Import M2DQWBK58 M2DQWBK62 M2DQWBK65.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

Theorem drf_sc_WB_of_CO2n : forall p, wf p -> cellful p -> race_free_g p -> CO2nK p ->
  forall s, runWB p s -> done p s -> evok s ->
  exists l g, srun p l g /\ (forall c, sp g c = pcs s c) /\
    (forall c j, j < pcs s c -> sr g c j = rg (cs s c) j) /\ (forall x, sm g x = final s x).
Proof.
  intros p W Wc RF HC. exact (drf_sc_WB_of_J p W Wc RF (J_run p W Wc RF) HC).
Qed.

Print Assumptions drf_sc_WB_of_CO2n.
