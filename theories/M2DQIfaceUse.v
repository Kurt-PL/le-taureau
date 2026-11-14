(* The results proved over the interface (MI*.v), for M2DQ
   (M2DQIfaceInst.dqmodel): fenced code is SC, DRF prefix, DRF-SC, and the
   two forbidden litmus outcomes of M2IfaceUse. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Inv M2SC M2Lit M2Iface MIPSync MIFSC MIPDrf MILitNeg MIParade M2DQ M2DQIface M2DQIfaceInst.

Theorem fenced_sc_dq : forall p s, wf p -> fenced p -> runQ p s -> done p s -> evok s ->
  exists l g, srun p l g /\ (forall c, sp g c = pcs s c) /\
    (forall c j, j < pcs s c -> sr g c j = rg (cs s c) j) /\ (forall x, sm g x = final s x).
Proof. intros p s W F R. apply (fenced_sc (IFM := dqmodel) p s W F (proj2 (reach_runQ p s) R)). Qed.

Theorem drf_prefix_dq : forall p s, wf p -> cellful p -> race_free_g p -> runQ p s -> evok s -> WIT p s.
Proof. intros p s W Wc RF R. apply (drf_prefix_m2 (IFM := dqmodel) p s W Wc RF (proj2 (reach_runQ p s) R)). Qed.

Theorem drf_sc_dq : forall p s, wf p -> cellful p -> race_free_g p -> runQ p s -> done p s -> evok s ->
  exists l g, srun p l g /\ (forall c, sp g c = pcs s c) /\
    (forall c j, j < pcs s c -> sr g c j = rg (cs s c) j) /\ (forall x, sm g x = final s x).
Proof. intros p s W Wc RF R. apply (drf_sc_m2 (IFM := dqmodel) p s W Wc RF (proj2 (reach_runQ p s) R)). Qed.

Theorem MPra_forbidden_dq : forall s, runQ MPra s -> done MPra s -> evok s -> ~ (rg (cs s 1) 0 = 1 /\ rg (cs s 1) 2 = 0).
Proof. intros s R. apply (MPra_forbidden (IFM := dqmodel) s (proj2 (reach_runQ _ s) R)). Qed.

Theorem Rmc_forbidden_dq : forall s, runQ Rmc s -> done Rmc s -> evok s -> ~ (rg (cs s 1) 3 = 0 /\ final s 1 = 2).
Proof. intros s R. apply (Rmc_forbidden (IFM := dqmodel) s (proj2 (reach_runQ _ s) R)). Qed.

Print Assumptions fenced_sc_dq.
Print Assumptions drf_prefix_dq.
Print Assumptions drf_sc_dq.
Print Assumptions MPra_forbidden_dq.
Print Assumptions Rmc_forbidden_dq.
