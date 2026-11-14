(* Part 65: every step of an A run of a race-free programme whose state after the step
   is evok satisfies RaceStep (RaceStep_of); hence J holds at every evok run state (J_run).
   - in order (s_ord): M2DQWBK63.sync_ord_all2 on the base of the state before the step (the image
     is the state itself, M2DQWBK29.self_image); a guard() pair, or both slots fenced, and then the
     reader is at the guard() after its slot (NF);
   - an early access or a CAS's read alone: M2DQWBK64.early_item_sync2 on the base of the state
     after the step; a guard() pair (both guard() events are older than the step), or both
     fenced: the place of the item is then the reader's next slot (a fenced place beyond it would
     pass the guard() before it), which is NF's fenced-access form;
   - the other steps log nothing. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO M2Ev M2SC M2SCx M2Trace M2DQTrace M2DQMono M2DQPCore.
Require Import MIPComp MIPNeg M2Iface MIPSync MIBase MIPDrf M2IfaceInst M2DQIfaceInst M2DQIfaceUse.
Require Import M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB.
Require Import M2DQWBK1 M2DQWBK3 M2DQWBK15 M2DQWBK22 M2DQWBK26 M2DQWBK29 M2DQWBK30 M2DQWBK35 M2DQWBK57 M2DQWBK58 M2DQWBK59 M2DQWBK60 M2DQWBK63 M2DQWBK64.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBQb M2DQWBQc M2DQWBK1Q M2DQShim M2DQTr.

Section R.
Variable p : prog.
Hypothesis W : wf p.
Hypothesis Wc : cellful p.
Hypothesis RF : race_free_g p.

Let G1' := M2DQWBK58.G1'.

(* a fenced place of an item is the context's next slot *)
Lemma place_pcs : forall cc pc c r T gt j, plc p c cc pc r (S T) T gt j -> fa p c j -> j = pc.
Proof.
  intros cc pc c r T gt j F (L1 & Fa). pose proof (plc_le _ _ _ _ _ _ _ _ F) as Lj.
  destruct (Nat.eq_dec j pc) as [E|N]; [exact E|exfalso].
  assert (Tk : taken p c cc pc r T (j - 1)).
  { apply (plc_before _ _ _ _ _ _ _ _ F (j - 1)); [lia|lia| | |]; rewrite (proj1 (Fa r));
      [reflexivity|intros v _; reflexivity|right; left; reflexivity]. }
  destruct (taken_dof _ _ _ _ _ _ _ Tk) as (d0 & D0). rewrite (proj1 (Fa r)) in D0. discriminate.
Qed.

Lemma tat_acc : forall i r gt, tatp i r gt -> (forall d, gt = TF d -> isaccd d = true) -> isacc i = true.
Proof.
  intros i r [d|m xs] T A.
  - cbn in T. pose proof (eof_acc i r d T (A d eq_refl)) as D. destruct i as [| | |f|]; cbn in D; try discriminate; reflexivity.
  - cbn in T. destruct i as [| | |f|]; cbn in T; try discriminate. reflexivity.
Qed.

Lemma eff_dof : forall t i r m m' a K u w x y, eff t i r m m' a K u w -> u x = Some y ->
  exists d, dof i r = Some d /\ In x (icells (inst_of d)) /\ isaccd d = true.
Proof.
  intros t i r m m' a K u w x y H U. inversion H; subst; try discriminate.
  all: match goal with Tk : takes _ _ _ |- _ => destruct Tk as [T1 T2] end.
  all: assert (Ix : In x (dd xs)) by (destruct (in_dec Nat.eq_dec x (dd xs)) as [I0|N0]; [exact I0|rewrite (T2 x N0) in U; discriminate]).
  all: cbn [dof]; match goal with C : ?cc ?rr = true |- context [?cc ?rr] => rewrite C end; eexists; split; [reflexivity|]; split; [exact Ix|reflexivity].
Qed.

(* a guard() event of the state after an early step or a read half, older than the step, is
   one of the state before it *)
Lemma isFF_back : forall s s' t F, (forall c j, oc (cs s' c) j = Some t -> oc (cs s c) j = Some t /\ ai (cs s' c) j = ai (cs s c) j) ->
  pcs s' = pcs s -> ent s' t = Some F -> ent s t = Some F -> isFF s' t F -> isFF s t F.
Proof.
  intros s s' t F H Pc E' E (A & L & O). destruct (H (ec F) (ek F) O) as [O0 A0].
  split; [rewrite <- A0; exact A|]. split; [rewrite <- Pc; exact L|exact O0].
Qed.


Lemma dof_cells : forall i r d, dof i r = Some d -> icells (inst_of d) = icells i.
Proof. intros [m xs c|m xs c v|m xs c e n|f|] r d H; cbn in H; try discriminate; destruct (c r); try discriminate; injection H as <-; reflexivity. Qed.

Lemma eofR_cells : forall i r m xs, eofR i r = Some (m, xs) -> icells i = dd xs.
Proof. intros [| | |f|] r m0 xs0 H; cbn in H; try discriminate. match goal with |- context [ICas _ _ ?cc _ _] => destruct (cc r) end; [injection H as <- <-; reflexivity|discriminate]. Qed.

Lemma acc_isaccd : forall d, isacc (inst_of d) = true -> isaccd d = true.
Proof. intros [] H; cbn in *; try reflexivity; discriminate. Qed.

Lemma dof_isacc : forall i r d, dof i r = Some d -> isacc i = true.
Proof. intros [| | |f|] r d H; cbn in H; try discriminate; reflexivity. Qed.



(* the item case: the step is the item's birth, the last step of a trace ending at s' *)
Lemma item_sync : forall s s' f n0 c k gt y ey x, run p s' -> evok s' -> trace p f (S n0) -> f n0 = s -> f (S n0) = s' ->
  item p f (S n0) c k n0 gt -> pcs s' c <= k -> tm s' = S (tm s) ->
  (forall r j, tatp (ins p c j r) r gt -> exists d, dof (ins p c j r) r = Some d /\ In x (icells (inst_of d))) ->
  (forall d, gt = TF d -> isaccd d = true) ->
  (forall c' j t, oc (cs s' c') j = Some t -> t < tm s -> oc (cs s c') j = Some t /\ ai (cs s' c') j = ai (cs s c') j) ->
  pcs s' = pcs s -> (forall t, t < tm s -> ent s' t = ent s t) ->
  (forall F, ent s' (tm s) = Some F -> isFF s' (tm s) F -> False) ->
  ent s y = Some ey -> ew ey = true -> In y (ids (hs s' x)) -> ec ey <> c -> y < tm s ->
  SyncY p s s' (ec ey) c y ey.
Proof.
  intros s s' f n0 c k gt y ey x R' EV' T F0 F1 It Pk Tm Hd HA HB Pc Lent Enew Ey Ew Iy Nc Ly.
  destruct (drf_prefix_dq p s' W Wc RF R' EV') as (lb & gb & B).
  rewrite <- F1 in B. assert (EVf : evok (f (S n0))) by (rewrite F1; exact EV').
  assert (Ey' : ent (f (S n0)) y = Some ey) by (rewrite F1, (Lent y Ly); exact Ey).
  rewrite <- F1 in Pk, Iy.
  assert (Lt : tm (f n0) < tm (f (S n0))) by (rewrite F0, F1, Tm; lia).
  assert (Ly' : y < tm (f n0)) by (rewrite F0; exact Ly).
  destruct (early_item_sync2 p W Wc RF f (S n0) T lb gb B EVf n0 k c gt x y ey It eq_refl Pk Lt Hd Ey' Ew Iy Nc Ly')
    as (Lu & [(k1 & k2 & G1 & G2 & _ & P1 & (EG1 & C1 & D1) & I1 & _ & O1 & P2 & (EG2 & C2 & D2) & I2 & _ & O2 & T1 & T2)|(Fy & r & j & Fj & Pj & Ag)]).
  - rewrite F1 in *. destruct (self_image p G1' s' W R') as [Rl' K'].
    destruct (isFF_AW p False G1' sw0 s' s' R' Rl' K' _ _ _ G1 EG1 C1 D1 I1 P1 O1) as (H1 & EH1 & FF1 & HC1 & _).
    destruct (isFF_AW p False G1' sw0 s' s' R' Rl' K' _ _ _ G2 EG2 C2 D2 I2 P2 O2) as (H2 & EH2 & FF2 & HC2 & _).
    set (t1 := MIPComp.bt s' (ec ey) k1) in *. set (t2 := MIPComp.bt s' c k2) in *.
    assert (L2 : t2 < tm s).
    { assert (Lq : t2 < tm s') by (unfold ent in EH2; rewrite (i_tm p s' (Inv1_run p s' R')); apply nth_error_Some; congruence).
      destruct (Nat.eq_dec t2 (tm s)) as [E|N]; [|lia]. exfalso. rewrite E in EH2, FF2. exact (Enew H2 EH2 FF2). }
    left. exists t1, H1, t2, H2.
    assert (FF1' : isFF s t1 H1).
    { destruct FF1 as (A & Lp & O). destruct (HB (ec H1) (ek H1) t1 O ltac:(lia)) as [O0 A0].
      split; [rewrite <- A0; exact A|]. split; [rewrite <- Pc; exact Lp|exact O0]. }
    assert (FF2' : isFF s t2 H2).
    { destruct FF2 as (A & Lp & O). destruct (HB (ec H2) (ek H2) t2 O L2) as [O0 A0].
      split; [rewrite <- A0; exact A|]. split; [rewrite <- Pc; exact Lp|exact O0]. }
    rewrite (Lent t1 ltac:(lia)) in EH1. rewrite (Lent t2 L2) in EH2.
    split; [exact EH1|]. split; [exact FF1'|]. split; [exact HC1|]. split; [exact T1|].
    split; [exact EH2|]. split; [exact FF2'|]. split; [exact HC2|exact T2].
  - right. rewrite F1 in Lu, Ag. rewrite Pc in Lu. split; [exact Fy|]. split; [exact Lu|].
    rewrite F1 in Pj. pose proof (place_pcs _ _ _ _ _ _ _ Pj Fj) as Ej. subst j.
    right. split; [exact Fj|].
    pose proof (tat_acc _ _ _ (plc_tat _ _ _ _ _ _ _ _ Pj) HA) as Ac.
    rewrite (ins_below p W c (pcs s' c) r (rg (cs s' c)) Ag) in Ac. exact Ac.
Qed.

Theorem RaceStep_of : forall s s', run p s -> step p s s' -> evok s' -> RaceStep p s s'.
Proof.
  intros s s' R St EV' e x y ey Ee Ex Ey Nc.
  pose proof (rS p s s' R St) as R'. pose proof (evok_stepQ p s s' R St EV') as EV.
  pose proof (Inv1_run p s R) as I. pose proof (proj2 (Inv2_run p s' R')) as J2'.
  destruct (j_rf p s' J2' (tm s) e x y Ee Ex) as (Ly & _ & _ & Iy').
  destruct (stepQ_split p s s' St) as [[HA _]|RX]; [|exfalso; unfold ent in Ee; rewrite (rfx_lg _ _ RX), (i_tm p s I) in Ee; assert (Lt : length (lg s) < length (lg s)) by (apply nth_error_Some; rewrite Ee; discriminate); lia].
  destruct (step_cases p s s' HA) as
    [(c & i & m' & a & K & u & w & Hi & Hoc & _ & _ & _ & Hh & _ & _ & He & _ & ->)
    |[(c & k & d & B & m' & a & K & u & w & L1 & Hoc & _ & Hd & _ & _ & He & _ & ->)
    |[(c & d & H1 & H2 & H3 & _ & _ & _ & ->)
    |[(c & k & xs & B & m' & a & K & u & w & bv & L1 & Hoc & Hoh & _ & _ & He & _ & ->)
    |[(c & S1 & S2 & _ & _ & _ & _ & _ & ->)
    |(cX & jX & bX & BX & oX & HjX & HfX & HcX & ->)]]]]].
  - (* in order *)
    unfold sord, evs, ent in Ee. cbn [lg] in Ee. rewrite nth_error_app_last, <- (i_tm p s I), Nat.ltb_irrefl, Nat.eqb_refl in Ee.
    injection Ee as <-. cbn [ec erf] in Ex, Nc |- *.
    destruct (eff_dof _ _ _ _ _ _ _ _ _ x y He Ex) as (dd0 & Dd & Id & _).
    pose proof (eff_takes _ _ _ _ _ _ _ _ _ x y He Ex) as Iy. cbn [mof mH] in Iy.
    destruct (self_image p G1' s W R) as [Rl K0].
    destruct (drf_prefix_dq p s W Wc RF R EV) as (l & g & B).
    assert (Ew : ew ey = true).
    { destruct (j_hist p s (proj2 (Inv2_run p s R)) x y Iy) as (ey' & _ & Ey' & Wy & _). rewrite Ey in Ey'.
      injection Ey' as <-. exact Wy. }
    rewrite <- Hi in Dd.
    destruct (sync_ord_all2 p False G1' sw0 s s l g y ey x dd0 c W Wc RF R EV Rl K0 (WK_run p W s (Q_in_WB p s R)) B
                Ey (A_flag p W s R x y Iy) Nc Dd Id) as [H|(F1 & L2 & F2)].
    + left. exact H.
    + right. split; [exact F1|]. split; [exact L2|]. apply (NF_after p s); [exact F2|]. unfold sord, evs. cbn [pcs]. rewrite upd_eq. reflexivity.
  - (* early *)
    assert (E0 : ent (searly s c k d B m' a K u w) (tm s) = Some (newev s c k (inst_of d) K u w)).
    { unfold searly, set_es, searly0, evs, ent. cbn [lg]. rewrite nth_error_app_last, <- (i_tm p s I), Nat.ltb_irrefl, Nat.eqb_refl. reflexivity. }
    rewrite E0 in Ee. injection Ee as <-. cbn [ec erf] in Ex, Nc |- *.
    destruct (eff_dof _ _ _ _ _ _ _ _ _ x y He Ex) as (dd0 & Dd & Id & Acd).
    pose proof (dof_isacc _ _ _ Dd) as Aci. pose proof (acc_isaccd d Aci) as Acdd.
    rewrite (dof_cells _ _ _ Dd) in Id.
    assert (Ew : ew ey = true).
    { pose proof (eff_takes _ _ _ _ _ _ _ _ _ x y He Ex) as Iy. cbn [mof mH] in Iy.
      destruct (j_hist p s (proj2 (Inv2_run p s R)) x y Iy) as (ey' & _ & Ey' & Wy & _). rewrite Ey in Ey'.
      injection Ey' as <-. exact Wy. }
    destruct (run_trace p s R) as (f0 & n0 & T0 & Ef0).
    set (f := fun j => if Nat.leb j n0 then f0 j else searly s c k d B m' a K u w).
    assert (T : trace p f (S n0)) by (apply trace_snoc; [exact T0|rewrite Ef0; exact St]).
    assert (Fn : f (S n0) = searly s c k d B m' a K u w) by (unfold f; replace (Nat.leb (S n0) n0) with false by (symmetry; apply Nat.leb_gt; lia); reflexivity).
    assert (Fn0 : f n0 = s) by (unfold f; rewrite Nat.leb_refl; exact Ef0).
    assert (Oc1 : oc (cs (f (S n0)) c) k = Some (tm s)) by (rewrite Fn; unfold searly, set_es, searly0, evs; cbn [cs oc oh]; rewrite !upd_eq; cbn [oc oh]; rewrite ?upd_eq; reflexivity).
    assert (Pk : pcs (f (S n0)) c <= k) by (rewrite Fn; unfold searly, set_es, searly0, evs; cbn [pcs]; lia).
    destruct (early_of_pending p f (S n0) T (S n0) c k (tm s) (le_n _) Pk Oc1) as (i0 & d' & Bd & ud & Ea & Li & Ti).
    assert (Ei : i0 = n0).
    { destruct (Nat.eq_dec i0 n0) as [E|N]; [exact E|exfalso].
      destruct (early_post p f (S n0) c k i0 d' Bd ud Ea) as (O1 & _).
      pose proof (x_oc _ _ (tr_ext p f (S n0) T (S i0) n0 ltac:(lia) ltac:(lia)) c k _ O1) as X.
      rewrite Fn0, Hoc in X. discriminate. }
    subst i0.
    destruct (early_post p f (S n0) c k n0 d' Bd ud Ea) as (_ & Ad & _).
    rewrite Fn in Ad. unfold searly, set_es, searly0, evs in Ad. cbn [cs ai] in Ad. rewrite !upd_eq in Ad. cbn [ai] in Ad. rewrite ?upd_eq in Ad.
    rewrite Fn, Fn0 in *.
    apply (item_sync s _ f n0 c k (TF d') y ey x R' EV' T Fn0 Fn).
    + left. exists d', Bd, ud. auto.
    + exact Pk.
    + unfold searly, set_es, searly0, evs. reflexivity.
    + intros r j Tt. cbn [tatp] in Tt. assert (Ad' : isaccd d' = true) by (apply acc_isaccd; rewrite <- Ad; exact Aci).
      exists d'. split; [exact (eof_acc _ _ _ Tt Ad')|rewrite <- Ad; exact Id].
    + intros d0 E. injection E as <-. apply acc_isaccd. rewrite <- Ad. exact Aci.
    + intros c' j t O Lt. unfold searly, set_es, searly0, evs, upd in O |- *. cbn [cs oc ai] in O |- *.
      destruct (Nat.eqb_spec c' c) as [->|N]; cbn [oc ai] in O |- *; [|split; auto].
      destruct (Nat.eqb_spec j k) as [->|Nj]; [injection O as <-; lia|split; auto].
    + unfold searly, set_es, searly0, evs. reflexivity.
    + intros t Lt. unfold searly, set_es, searly0, evs, ent. cbn [lg]. rewrite nth_error_app1; [reflexivity|rewrite <- (i_tm p s I); exact Lt].
    + intros F EF (A & _). rewrite E0 in EF. injection EF as <-. cbn [ec ek] in A.
      unfold searly, set_es, searly0, evs in A. cbn [cs ai] in A. rewrite !upd_eq in A. cbn [ai] in A. rewrite ?upd_eq in A.
      rewrite A in Aci. discriminate.
    + exact Ey.
    + exact Ew.
    + exact Iy'.
    + exact Nc.
    + exact Ly.
  - (* reaching an early access: no entry *)
    exfalso. unfold smatch, ent in Ee. cbn [lg] in Ee. rewrite (i_tm p s I) in Ee. rewrite (proj2 (nth_error_None _ _) (le_n _)) in Ee. discriminate.
  - (* a CAS's read alone *)
    assert (E0 : ent (sread s c k Plain xs B m' a K u w bv) (tm s) = Some (newevh s c k (ILd Plain xs (fun _ => true)) K u w)).
    { unfold sread, ent. cbn [lg]. rewrite nth_error_app_last, <- (i_tm p s I), Nat.ltb_irrefl, Nat.eqb_refl. reflexivity. }
    rewrite E0 in Ee. injection Ee as <-. cbn [ec erf] in Ex, Nc |- *.
    destruct (eff_dof _ _ _ _ _ _ _ _ _ x y He Ex) as (dd0 & Dd & Id & _).
    rewrite (dof_cells _ _ _ Dd) in Id. cbn [icells] in Id.
    assert (Ew : ew ey = true).
    { pose proof (eff_takes _ _ _ _ _ _ _ _ _ x y He Ex) as Iy. cbn [mof mH] in Iy.
      destruct (j_hist p s (proj2 (Inv2_run p s R)) x y Iy) as (ey' & _ & Ey' & Wy & _). rewrite Ey in Ey'.
      injection Ey' as <-. exact Wy. }
    destruct (run_trace p s R) as (f0 & n0 & T0 & Ef0).
    set (f := fun j => if Nat.leb j n0 then f0 j else sread s c k Plain xs B m' a K u w bv).
    assert (T : trace p f (S n0)) by (apply trace_snoc; [exact T0|rewrite Ef0; exact St]).
    assert (Fn : f (S n0) = sread s c k Plain xs B m' a K u w bv) by (unfold f; replace (Nat.leb (S n0) n0) with false by (symmetry; apply Nat.leb_gt; lia); reflexivity).
    assert (Fn0 : f n0 = s) by (unfold f; rewrite Nat.leb_refl; exact Ef0).
    assert (Oh1 : oh (cs (f (S n0)) c) k = Some (tm s)) by (rewrite Fn; unfold sread; cbn [cs oc oh]; rewrite !upd_eq; cbn [oc oh]; rewrite ?upd_eq; reflexivity).
    destruct (early_of_hpending p f (S n0) T (S n0) c k (tm s) (le_n _) Oh1) as (i0 & xs' & Bd & ud & Ea & Li & Ti).
    assert (Ei : i0 = n0).
    { destruct (Nat.eq_dec i0 n0) as [E|N]; [exact E|exfalso].
      destruct (early_postR p f (S n0) c k i0 xs' Bd ud Ea) as (O1 & _).
      pose proof (x_oh _ _ (tr_ext p f (S n0) T (S i0) n0 ltac:(lia) ltac:(lia)) c k _ O1) as X.
      rewrite Fn0, Hoh in X. discriminate. }
    subst i0.
    destruct (early_postR p f (S n0) c k n0 xs' Bd ud Ea) as (_ & Ad & _).
    rewrite Fn in Ad. unfold sread in Ad. cbn [cs ai] in Ad. rewrite !upd_eq in Ad. cbn [ai] in Ad. rewrite ?upd_eq in Ad.
    unfold crd in Ad. injection Ad as <-.
    rewrite Fn, Fn0 in *.
    apply (item_sync s _ f n0 c k (TH Plain xs) y ey x R' EV' T Fn0 Fn).
    + right. exists xs, Bd, ud. auto.
    + unfold sread. cbn [pcs]. exact L1.
    + unfold sread. reflexivity.
    + intros r j Tt. cbn [tatp] in Tt. destruct (cas_dofR _ _ _ _ Tt) as (d0 & D0 & C0).
      exists d0. split; [exact D0|]. rewrite C0, (eofR_cells _ _ _ _ Tt). exact Id.
    + intros d0 E. discriminate.
    + intros c' j t O Lt. unfold sread, upd in O |- *. cbn [cs oc ai] in O |- *.
      destruct (Nat.eqb_spec c' c) as [->|N]; cbn [oc ai] in O |- *; [|split; auto].
      destruct (Nat.eqb_spec j k) as [->|Nj]; [rewrite Hoc in O; discriminate|split; auto].
    + unfold sread. reflexivity.
    + intros t Lt. unfold sread, ent. cbn [lg]. rewrite nth_error_app1; [reflexivity|rewrite <- (i_tm p s I); exact Lt].
    + intros F EF (A & _). rewrite E0 in EF. injection EF as <-. cbn [ec ek] in A.
      unfold sread in A. cbn [cs ai] in A. rewrite !upd_eq in A. cbn [ai] in A. rewrite ?upd_eq in A. discriminate.
    + exact Ey.
    + exact Ew.
    + exact Iy'.
    + exact Nc.
    + exact Ly.
  - exfalso. unfold sskip, ent in Ee. cbn [lg] in Ee. rewrite (i_tm p s I) in Ee. rewrite (proj2 (nth_error_None _ _) (le_n _)) in Ee. discriminate.
  - exfalso. unfold scfix0, ent in Ee. cbn [lg] in Ee. rewrite (lg_flp s cX oX bX), (i_tm p s I) in Ee.
    rewrite (proj2 (nth_error_None _ _) (le_n _)) in Ee. discriminate.
Qed.
(* J at every evok run state of a race-free programme *)
Theorem J_run : forall s, run p s -> evok s -> J p s.
Proof. exact (J_run_of p W RaceStep_of). Qed.
End R.

Print Assumptions RaceStep_of.
Print Assumptions J_run.
