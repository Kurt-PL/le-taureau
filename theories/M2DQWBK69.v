(* Part 69: CO2nK holds for every wf, cellful, race-free programme, so G2 holds for it.
   At the new entry t of context c (image entry e, state entry eW) in the CO2n corner: t takes, in
   the image, a store a that is not c's; in the state, c's own written-back store w0 standing for a.
   - The image entry e0 at time w0 is c's CAS (its read half) and read a in
     x (M2DQWBK68.wch_INVF), so the image's c knows a (k_Pcur), and J (j1, M2DQWBK65.J_run) gives
     vOg(c) a or NF.  From vOg(c) a, UK's u_Og gives the path (M2DQWBK61.Og_up).
   - NF, guard() form: t is at or beyond the guard() at c's next slot (new_slot), and nothing is
     recorded there (no_past_guard, no_past_guard_h), unless t's step passed that slot, when t is
     the guard() itself (ent_new_pcs), which reads nothing.
   - NF, fenced form (slot kp, guard()s at kp - 1 and kp + 1): t is at kp; the CAS of w0 is at a
     slot kc <= kp (nothing at or beyond kp + 1), not kp (its record at kp is the write-back's,
     which leaves no write at kp: w_WBOC, i_hoc), not kp - 1 (a guard(), not a CAS: w_swc), so
     kc < kp - 1: its entry is before the guard() at kp - 1 (JE), which knew a (k_Ppair) and put
     it in vOg(c) (w_OGP). *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Lit.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO M2Trace M2DQTrace M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB.
Require Import M2DQWBK1 M2DQWBK2 M2DQWBK3 M2DQWBK14 M2DQWBK15 M2DQWBK17 M2DQWBK19 M2DQWBK29 M2DQWBK32 M2DQWBK37 M2DQWBK38 M2DQWBK40.
Require Import M2DQWBK49 M2DQWBK50 M2DQWBK52 M2DQWBK53 M2DQWBK54 M2DQWBK55 M2DQWBK57 M2DQWBK58 M2DQWBK61 M2DQWBK62 M2DQWBK65 M2DQWBK66 M2DQWBK68.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim M2DQTr.

Section CO.
Variable p : prog.
Hypothesis W : wf p.
Hypothesis Wc : cellful p.
Hypothesis RF : race_free_g p.

Theorem CO2nK_holds : CO2nK p.
Proof.
  intros sW sw sA sw' sW' sA' s1 Ch L RA' R' K' U0 WB U1 KG KC EVA EV' Fut St StA R1 K1 Hs1 e eW Ee EW a N Co Q.
  pose proof (wch_run p False G0 sW sw sA Ch) as RA. pose proof (wch_rel p False G0 sW sw sA Ch) as Rl.
  pose proof (wch_KR p False G0 sW sw sA Ch) as K.
  assert (SG : forall x w a, seg (hs sW x) w (Some a) -> seg (hs s1 x) w (Some a)).
  { intros x w a0 Sg. rewrite Hs1.
    exact (seg_stepWB p sW sW' x w a0 (wlink_stepWB p False G0 sw sW sA sw' sW' sA' L) Sg). }
  pose proof (J_run p W Wc RF sA RA EVA) as Js.
  (* from vOg(c) a: the path *)
  assert (OgP : vOg (cs sA (ec eW)) a -> ~ ~ Pth s1 a (tm sA)).
  { intros Og NP. apply (Og_up p sw sW sA sA' s1 e eW RA Rl K U0 RA' R1 K1 St StA SG Ee EW Js a Og Q).
    intros [H|(w & x' & Qw & Sg)]; apply NP.
    - constructor. right; right. exists eW. split; [exact EW|]. split; [exact H|exact N].
    - pose proof (seg_old _ _ _ Sg) as O.
      destruct (Nat.eq_dec w (tm sA)) as [->|Nw].
      + constructor. left. exists x'. exact O.
      + apply (t_trans _ _ a w (tm sA)); constructor; [left; exists x'; exact O|].
        right; right. exists eW. split; [exact EW|]. split; [exact Qw|exact Nw]. }
  destruct Co as (x & w0 & f & Ea & Ew0 & Sw & Fx & Ow & NO & Na).
  (* the image entry at w0: c's, and it read a *)
  destruct (wch_INVF p False G0 sW sw sA Ch w0 f x a Sw Fx) as (e0 & E0 & R0).
  destruct (k_ent False G0 sw sW sA K w0 e0 E0) as (eW0 & EW0 & Ks0).
  pose proof Ks0 as (_ & Ce0 & Ke0 & _).
  assert (Cc : ec eW0 = ec eW).
  { destruct Ow as (e' & E' & C' & _). unfold ent in EW0. rewrite EW0 in E'. injection E' as <-. exact C'. }
  destruct (Inv_run p sA RA) as [I I2 L3].
  assert (Pa : vP (cs sA (ec eW)) a).
  { rewrite <- Cc, <- Ce0. apply (proj2 (k_Pcur p sA L3 w0 e0 E0)). left. exists x. exact R0. }
  destruct (j1 p sA Js (ec eW) a Na (or_introl Pa)) as [Og|Nf]; [exact (OgP Og)|].
  apply OgP.
  (* NF *)
  destruct Fut as (sAf & SF & DF).
  assert (SA : star p sA sAf) by exact (stS p sA sA' sAf StA SF).
  pose proof (Inv1_run p sA' RA') as I'.
  pose proof (Ext_step p sA sA' RA StA) as X.
  pose proof (M2DQWBK53.Ks p sw sW sA sA' s1 e eW RA Rl K U0 RA' R1 K1 St StA SG Ee EW) as Kse.
  pose proof Kse as (_ & Ce & _).
  destruct (new_slot p sA sA' e RA StA Ee) as (Lt & Ft).
  rewrite Ce in Lt, Ft.
  pose proof (j_rf p sA' (proj2 (Inv2_run p sA' RA')) (tm sA) e x a Ee Ea) as (_ & _ & Ix & _).
  unfold einstr in Ix. rewrite Ce in Ix.
  destruct Nf as [Gd|((L1 & Fa) & Ac)].
  - (* guard() next: t is no access *)
    exfalso.
    destruct (Nat.eq_dec (pcs sA' (ec eW)) (pcs sA (ec eW))) as [Ep|Np].
    + revert Ft. destruct (eh e); intros Ft.
      * rewrite (no_past_guard_h p sA' sAf (ec eW) (pcs sA (ec eW)) (ek e) W RA' SF DF Gd ltac:(lia) Lt) in Ft. discriminate.
      * rewrite (no_past_guard p sA' sAf (ec eW) (pcs sA (ec eW)) (ek e) W RA' SF DF Gd ltac:(lia) Lt) in Ft. discriminate.
    + destruct (ent_new_pcs p sA sA' e RA StA Ee ltac:(rewrite Ce; exact Np)) as (Ek & Ai).
      rewrite Ce in Ai. rewrite Ai, (Gd (rg (cs sA (ec eW)))) in Ix. destruct Ix.
  - (* a fenced access next *)
    assert (Gp : forall r, ins p (ec eW) (S (pcs sA (ec eW))) r = IFn FFull) by (intros r; exact (proj2 (Fa r))).
    assert (Gm : forall r, ins p (ec eW) (pcs sA (ec eW) - 1) r = IFn FFull) by (intros r; exact (proj1 (Fa r))).
    (* t is at the fenced slot *)
    assert (Kt : ek e = pcs sA (ec eW)).
    { destruct (Nat.eq_dec (pcs sA' (ec eW)) (pcs sA (ec eW))) as [Ep|Np].
      - destruct (Nat.le_gt_cases (ek e) (pcs sA (ec eW))) as [Le|Gt]; [lia|exfalso].
        revert Ft. destruct (eh e); intros Ft.
        + rewrite (no_past_guard_h p sA' sAf (ec eW) (S (pcs sA (ec eW))) (ek e) W RA' SF DF Gp ltac:(lia) ltac:(lia)) in Ft. discriminate.
        + rewrite (no_past_guard p sA' sAf (ec eW) (S (pcs sA (ec eW))) (ek e) W RA' SF DF Gp ltac:(lia) ltac:(lia)) in Ft. discriminate.
      - destruct (ent_new_pcs p sA sA' e RA StA Ee ltac:(rewrite Ce; exact Np)) as (Ek & _). rewrite Ce in Ek. exact Ek. }
    rewrite Kt in Ft.
    pose proof (M2Inv.i_et p sA I w0 e0 E0) as (_ & F0).
    rewrite Ce0, Cc in F0.
    assert (Lw : w0 < tm sA) by (rewrite (i_tm p sA I); unfold ent in E0; apply nth_error_Some; congruence).
    (* the CAS of w0 is not beyond the fenced slot *)
    assert (Kc1 : ek e0 <= pcs sA (ec eW)).
    { destruct (Nat.le_gt_cases (ek e0) (pcs sA (ec eW))) as [Le|Gt]; [exact Le|exfalso].
      revert F0. destruct (eh e0); intros F0.
      + rewrite (no_past_guard_h p sA sAf (ec eW) (S (pcs sA (ec eW))) (ek e0) W RA SA DF Gp ltac:(lia) ltac:(lia)) in F0. discriminate.
      + rewrite (no_past_guard p sA sAf (ec eW) (S (pcs sA (ec eW))) (ek e0) W RA SA DF Gp ltac:(lia) ltac:(lia)) in F0. discriminate. }
    (* nor at it: t is there *)
    assert (Kc2 : ek e0 <> pcs sA (ec eW)).
    { intros Ek0. rewrite Ek0 in F0. revert F0 Ft. destruct (eh e0), (eh e); intros F0 Ft.
      - rewrite (x_oh _ _ X _ _ _ F0) in Ft. injection Ft as Z. lia.
      - pose proof (x_oh _ _ X _ _ _ F0) as F0'.
        destruct (crel_eq p False G0 sw s1 sA' RA' R1 K1 (ec eW)) as (Eoc & Eoh & _).
        rewrite Eoh in F0'.
        destruct (w_WBOC False G0 sw s1 sA' K1 (ec eW) (pcs sA (ec eW)) w0 F0' ltac:(rewrite Sw; discriminate)) as (Oc1 & _).
        rewrite Eoc, Oc1 in Ft. discriminate.
      - pose proof (x_oc _ _ X _ _ _ F0) as F0'.
        destruct (i_hoc p sA' I' (ec eW) (pcs sA (ec eW)) (tm sA) w0 Ft F0') as (Z & _). lia.
      - rewrite (x_oc _ _ X _ _ _ F0) in Ft. injection Ft as Z. lia. }
    (* nor at the guard() before it *)
    assert (Pm : pcs sA (ec eW) - 1 < pcs sA (ec eW)) by lia.
    destruct (proj1 (i_cmA p sA I (ec eW) (pcs sA (ec eW) - 1)) Pm) as (tg & Inm).
    assert (Ai : ai (cs sA (ec eW)) (pcs sA (ec eW) - 1) = IFn FFull).
    { rewrite (proj2 (i_set p sA I (ec eW) _ tg Inm)). apply Gm. }
    assert (Kc3 : ek e0 <> pcs sA (ec eW) - 1).
    { intros Ek0. destruct (w_swc False G0 sw sW sA K w0 f Sw) as (e' & E' & Cas).
      rewrite EW0 in E'. injection E' as <-.
      destruct (crel_eq p False G0 sw sW sA RA Rl K (ec eW)) as (_ & _ & Eai & _).
      rewrite Cc, <- Ke0, Ek0, <- Eai, Ai in Cas. discriminate. }
    (* so it is before the guard() at kp - 1, which knew a and put it into vOg *)
    assert (Og : oc (cs sA (ec eW)) (pcs sA (ec eW) - 1) = Some tg).
    { apply (i_cmF p sA I _ _ tg Inm); rewrite (Gm (rg (cs sA (ec eW)))); reflexivity. }
    destruct (M2Inv.i_oc p sA I _ _ tg Og) as (F & EF & CF & KF).
    assert (Lwg : w0 < tg).
    { apply (JE_run p sA RA w0 e0 (pcs sA (ec eW) - 1) tg E0); [rewrite Ce0, Cc; exact Inm|lia]. }
    assert (Pe : eP F a).
    { apply (proj2 (k_Ppair p sA L3 w0 e0 tg F E0 EF ltac:(rewrite Ce0, Cc, CF; reflexivity) Lwg)). left. exists x. exact R0. }
    destruct (self_image p G1' sA W RA) as [_ K0].
    assert (FF : isFF sA tg F).
    { unfold isFF. rewrite CF, KF. split; [exact Ai|]. split; [lia|exact Og]. }
    pose proof (proj1 (w_OGP False G1' sw0 sA sA K0 tg F EF FF) a Pe) as Z. rewrite CF in Z. exact Z.
Qed.
End CO.

(* G2: drf_sc over stepWB for every wf, cellful, race-free programme *)
Theorem drf_sc_WB : forall p, wf p -> cellful p -> race_free_g p ->
  forall s, runWB p s -> done p s -> evok s ->
  exists l g, srun p l g /\ (forall c, sp g c = pcs s c) /\
    (forall c j, j < pcs s c -> sr g c j = rg (cs s c) j) /\ (forall x, sm g x = final s x).
Proof. intros p W Wc RF. exact (drf_sc_WB_of_CO2n p W Wc RF (CO2nK_holds p W Wc RF)). Qed.

Print Assumptions CO2nK_holds.
Print Assumptions drf_sc_WB.
