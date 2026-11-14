(* Part 62: NewKc3 from J at every evok image and the one corner CO2n.
   CO2nK p: at the new entry of every link, an item a <> t in the CO2n corner of M2DQWBK61 has a
   path a -> t in the state after the step (up to a double negation); an item of e's
   knowledge (eQ e or eQc e), as Og_cases has it.
   NewKc3_of_J: wf p -> (J at every run state that is evok) -> CO2nK p -> NewKc3 p.
   drf_sc_WB_of_J: G2 from the same two premises (with M2DQWBK55.drf_sc_WB_of_corners3). *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Lit.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB.
Require Import M2DQWBK1 M2DQWBK2 M2DQWBK3 M2DQWBK15 M2DQWBK17 M2DQWBK19 M2DQWBK37 M2DQWBK38 M2DQWBK40.
Require Import M2DQWBK49 M2DQWBK50 M2DQWBK52 M2DQWBK53 M2DQWBK54 M2DQWBK55 M2DQWBK57 M2DQWBK58 M2DQWBK61.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

Section G.
Variable p : prog.

Definition CO2nK : Prop := forall sW sw sA sw' sW' sA' s1,
  wch p False G0 sW sw sA -> wlink p False G0 sw sW sA sw' sW' sA' ->
  run p sA' -> rel sw' sW' sA' -> KR False G0 sw' sW' sA' ->
  UK sw sW sA -> WBCall sW -> UK sw' sW' sA' ->
  KGn sW sA -> KCn sW sA -> evok sA -> evok sW' -> (exists sAf, star p sA' sAf /\ done p sAf) ->
  step p sW s1 -> step p sA sA' -> rel sw s1 sA' -> KR False G0 sw s1 sA' ->
  s1 = sW' ->
  forall e eW, ent sA' (tm sA) = Some e -> ent s1 (tm sA) = Some eW ->
  forall a, a <> tm sA -> CO2n sw sW sA e eW a -> (eQ e a \/ eQc e a) -> ~ ~ Pth s1 a (tm sA).

Theorem NewKc3_of_J : (forall s, run p s -> evok s -> J p s) -> CO2nK -> NewKc3 p.
Proof.
  intros HJ HC sW sw sA sw' sW' sA' s1 Ch L RA' R' K' U0 WB U1 G C EVA EV' Fut St StA R1 K1 Hs1 e eW Ee EW.
  pose proof (wch_run p False G0 sW sw sA Ch) as RA. pose proof (wch_rel p False G0 sW sw sA Ch) as Rl.
  pose proof (wch_KR p False G0 sW sw sA Ch) as K.
  assert (SG : forall x w a, seg (hs sW x) w (Some a) -> seg (hs s1 x) w (Some a)).
  { intros x w a Sg. rewrite Hs1.
    exact (seg_stepWB p sW sW' x w a (wlink_stepWB p False G0 sw sW sA sw' sW' sA' L) Sg). }
  assert (EV1 : evok s1).
  { rewrite Hs1. exact EV'. }
  destruct (k_ent False G0 sw s1 sA' K1 (tm sA) e Ee) as (eW' & E' & Ks). rewrite EW in E'. injection E' as <-.
  pose proof (HJ sA RA EVA) as Js.
  pose proof (HC sW sw sA sw' sW' sA' s1 Ch L RA' R' K' U0 WB U1 G C EVA EV' Fut St StA R1 K1 Hs1 e eW Ee EW) as H2.
  split.
  - intros a Q N NQ NS _ NP.
    apply (Og_cases p sw sW sA sA' s1 e eW RA Rl K U0 RA' R1 K1 St StA SG Ee EW Js a (or_introl Q)).
    intros [Og|[H|[H|H]]].
    + apply (Og_up p sw sW sA sA' s1 e eW RA Rl K U0 RA' R1 K1 St StA SG Ee EW Js a Og (or_introl Q)).
      intros [H|H]; [exact (NQ H)|exact (NS H)].
    + exact (NQ H).
    + exact (NS H).
    + exact (H2 a N H (or_introl Q) NP).
  - intros x a Ix Q Ia N ND NS _ NP.
    assert (Ia1 : In a (ids (hs s1 x))).
    { destruct (in_ids_fl _ _ Ia) as [b Ib]. rewrite (r_hs sw s1 sA' R1 x) in Ib. apply in_hers in Ib.
      exact (in_ids_of _ _ _ (proj1 Ib)). }
    assert (Stand : forall w x', eQ eW w -> seg (hs s1 x') w (Some a) -> False).
    { intros w x' Qw Sg. destruct (Nat.eq_dec x' x) as [->|Nx].
      - apply NS. exists w. split; [left; exact Qw|exact Sg].
      - apply NP. apply (co4_path p sw s1 sA' (tm sA) e eW RA' R1 K1 Ee EW Ks EV1 x a Ix Ia1 N).
        exists w, x'. auto. }
    apply (Og_cases p sw sW sA sA' s1 e eW RA Rl K U0 RA' R1 K1 St StA SG Ee EW Js a Q).
    intros [Og|[H|[(w & x' & Qw & Sg)|H]]].
    + apply (Og_up p sw sW sA sA' s1 e eW RA Rl K U0 RA' R1 K1 St StA SG Ee EW Js a Og Q).
      intros [H|(w & x' & Qw & Sg)]; [apply ND; split; [left; exact H|exact Ia1]|exact (Stand w x' Qw Sg)].
    + apply ND. split; [left; exact H|exact Ia1].
    + exact (Stand w x' Qw Sg).
    + apply (H2 a N H Q). intros P. apply NP. exact (path_cell p sw s1 sA' (tm sA) e eW RA' R1 Ee EW Ks EV1 x a P Ix Ia1 N).
Qed.

Theorem drf_sc_WB_of_J : wf p -> cellful p -> race_free_g p -> (forall s, run p s -> evok s -> J p s) -> CO2nK ->
  forall s, runWB p s -> done p s -> evok s ->
  exists l g, srun p l g /\ (forall c, sp g c = pcs s c) /\
    (forall c j, j < pcs s c -> sr g c j = rg (cs s c) j) /\ (forall x, sm g x = final s x).
Proof. intros W Wc RF HJ HC. exact (drf_sc_WB_of_corners3 p W Wc RF (NewKc3_of_J HJ HC)). Qed.
End G.

Print Assumptions NewKc3_of_J.
Print Assumptions drf_sc_WB_of_J.
