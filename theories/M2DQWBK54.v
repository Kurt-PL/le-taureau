(* Part 54: G2 from the four corners.  NewKc p: at the new entry of every link (with
   everything NewKr has), each corner item of M2DQWBK53 has, up to a double negation, a path into
   the entry (per cell for the per-cell items).  drf_sc_WB_of_corners: NewKc gives G2
   (NewKc -> NewKr -> NewK -> LinkK -> drf_sc over stepWB). *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Lit.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB.
Require Import M2DQWBK1 M2DQWBK2 M2DQWBK3 M2DQWBK17 M2DQWBK37 M2DQWBK38 M2DQWBK40.
Require Import M2DQWBK49 M2DQWBK50 M2DQWBK52 M2DQWBK53.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

Section G.
Variable p : prog.

Definition NewKc : Prop := forall sW sw sA sw' sW' sA' s1,
  wch p False G0 sW sw sA -> wlink p False G0 sw sW sA sw' sW' sA' ->
  run p sA' -> rel sw' sW' sA' -> KR False G0 sw' sW' sA' ->
  UK sw sW sA -> WBCall sW -> UK sw' sW' sA' ->
  KGn sW sA -> KCn sW sA -> evok sA -> evok sW' -> (exists sAf, star p sA' sAf /\ done p sAf) ->
  step p sW s1 -> step p sA sA' -> rel sw s1 sA' -> KR False G0 sw s1 sA' ->
  s1 = sW' ->
  forall e eW, ent sA' (tm sA) = Some e -> ent s1 (tm sA) = Some eW ->
  (forall a, eQ e a -> a <> tm sA -> ~ eQ eW a -> ~ (exists w x, eQ eW w /\ seg (hs s1 x) w (Some a)) ->
     (CO1 sw sW (ec eW) eW a \/ CO2 sw sW (ec eW) eW a) -> ~ ~ Pth s1 a (tm sA)) /\
  (forall x a, In x (eC e) -> (eQ e a \/ eQc e a) -> In a (ids (hs sA' x)) -> a <> tm sA ->
     ~ ((eQ eW a \/ eQc eW a) /\ In a (ids (hs s1 x))) ->
     ~ (exists w, (eQ eW w \/ eQc eW w) /\ seg (hs s1 x) w (Some a)) ->
     (CO1 sw sW (ec eW) eW a \/ CO2 sw sW (ec eW) eW a \/ CO3 sW (ec eW) a \/ CO4 s1 eW x a) ->
     ~ ~ clos_trans nat (cedge s1 x) a (tm sA)).

Theorem NewKr_of_NewKc : NewKc -> NewKr p.
Proof.
  intros NC sW sw sA sw' sW' sA' s1 Ch L RA' R' K' U0 WB U1 G C EVA EV' Fut St StA R1 K1 Hs1 e eW Ee EW.
  pose proof (wch_run p False G0 sW sw sA Ch) as RA. pose proof (wch_rel p False G0 sW sw sA Ch) as Rl.
  pose proof (wch_KR p False G0 sW sw sA Ch) as K.
  assert (SG : forall x w a, seg (hs sW x) w (Some a) -> seg (hs s1 x) w (Some a)).
  { intros x w a Sg. rewrite Hs1.
    exact (seg_stepWB p sW sW' x w a (wlink_stepWB p False G0 sw sW sA sw' sW' sA' L) Sg). }
  destruct (res_corners p sw sW sA sA' s1 e eW RA Rl K U0 RA' R1 K1 St StA SG Ee EW) as [CG CC].
  destruct (NC sW sw sA sw' sW' sA' s1 Ch L RA' R' K' U0 WB U1 G C EVA EV' Fut St StA R1 K1 Hs1 e eW Ee EW) as [NG NCc].
  split.
  - intros a Q N NQ NS NP. apply (CG a Q NQ NS). intros Co. exact (NG a Q N NQ NS Co NP).
  - intros x a Ix Q Ia N ND NS NP. apply (CC x a Ix Q Ia ND NS). intros Co. exact (NCc x a Ix Q Ia N ND NS Co NP).
Qed.

(* G2 from the corners *)
Theorem drf_sc_WB_of_corners : wf p -> cellful p -> race_free_g p -> NewKc ->
  forall s, runWB p s -> done p s -> evok s ->
  exists l g, srun p l g /\ (forall c, sp g c = pcs s c) /\
    (forall c j, j < pcs s c -> sr g c j = rg (cs s c) j) /\ (forall x, sm g x = final s x).
Proof.
  intros W Wc RF NC. apply (drf_sc_WB_of_link p W Wc RF).
  apply LinkK_of_NewK. apply NewK_of_NewKr. exact (NewKr_of_NewKc NC).
Qed.
End G.

Print Assumptions NewKr_of_NewKc.
Print Assumptions drf_sc_WB_of_corners.
