(* Part 64: M2DQWBK34.early_item_sync with the reader's side of the both-fenced case
   kept: when the guard() pair is missing, the race-free programme has both accesses fenced, the
   item's place j (a plc of the state after the step, under registers r that agree with the
   state's below its next instruction) is fenced too (early_item_sync2). *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO M2SC M2SCx M2Trace M2DQTrace M2DQMono M2DQPCore.
Require Import MIPComp MIPNeg M2Iface MIPSync MIBase MIPDrf M2IfaceInst M2DQIfaceInst.
Require Import M2DQWBK26 M2DQWBK27 M2DQWBK28.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim M2DQTr.


Section Early.
Variables (p : prog) (W : wf p) (Wc : cellful p) (RF : race_free_g p).
Variables (f : nat -> st) (nb : nat) (T : trace p f nb).
Variables (lb : list sev) (gb : sst).
Hypothesis B : base p (f nb) lb gb.
Hypothesis EVb : evok (f nb).

Lemma nth_beyond2 : forall (F' : list sev) q e, length lb <= q -> nth_error (lb ++ F') q = Some e -> In e F'.
Proof.
  intros F' q e L Q. rewrite nth_error_app2 in Q by exact L. exact (nth_error_In _ _ Q).
Qed.

(* M2PCore.pend_meet, with the no-write premise only for the writer's own context *)
Lemma pend_meet_x2 : forall tau l g c d x cy ky iy dy By uy Ey,
  CONS p f nb lb gb l g tau -> dof (ins p c (sp g c) (sr g c)) (sr g c) = Some d -> cy <> c ->
  In x (icells (inst_of d)) ->
  early_at p f nb cy ky iy dy By uy -> pcs (f nb) cy <= ky -> tm (f iy) < tau ->
  ent (f nb) (tm (f iy)) = Some Ey -> ew Ey = true -> In x (icells (einstr p (f nb) Ey)) ->
  (forall q e, length lb <= q -> nth_error l q = Some e -> sx e = cy -> writes_x e x = false) ->
  RACY p.
Proof.
  intros tau l g c d x cy ky iy dy By uy Ey Co Dd Nc Ixd Eay Pky Lty AEy Wy Iy NoW.
  destruct B as (Bsr & Bsp & Brg & Bgo & Bco).
  pose proof (core p W Wc f nb T lb gb Bsr Bsp Brg Bgo Bco EVb (tm (f iy))) as IH.
  pose proof Eay as (Liy & _).
  assert (Ib1 : Inv1 p (f nb)) by (apply Inv1_run; apply (tr_run p f nb T); lia).
  destruct (early_pending p f nb T W cy ky iy dy By uy nb Eay Liy ltac:(lia) Pky) as (Py & Oy).
  destruct (i_oc p (f nb) Ib1 cy ky _ Oy) as (Ey' & AEy' & Xy & Ky). rewrite AEy in AEy'. injection AEy' as <-.
  assert (Eiy : einstr p (f nb) Ey = inst_of dy) by (unfold einstr; rewrite Xy, Ky; destruct Py as (_ & _ & P3); exact P3).
  rewrite Eiy in Iy.
  assert (Ity : item p f nb cy ky iy (TF dy)) by (left; exists dy, By, uy; auto).
  destruct (fwd p W Wc f nb T lb gb Bsr Bsp Brg l g tau cy ky iy (TF dy) IH Co Ity Pky ltac:(lia))
    as [Rc|[(j' & Lj' & Fj')|(F' & g' & S' & X' & Co' & Fp & Cg')]].
  - exact Rc.
  - apply (pend_passed p W Wc f nb T lb gb Bsr Bsp Brg tau l g cy ky iy dy By uy Ey x j' IH Co Eay Pky Lty AEy Wy
             ltac:(rewrite Eiy; exact Iy) (fun q e L Q X _ => NoW q e L Q X) Lj' Fj').
  - apply (pend_reached p W Wc f nb T lb gb Bsr Bsp Brg tau l g c d x cy ky iy dy By uy Ey F' g' IH Co Dd Nc Ixd Eay Pky Lty AEy Wy
             ltac:(rewrite Eiy; exact Iy) S' X' Co' Fp Cg').
Qed.

(* the CAS's place is reached by a guard()-free run of c2; a write of another context in one of
   its cells, made before it, is passed, and a guard() pair orders the two, or the write is fenced *)
Theorem early_item_sync2 : forall i k c2 gt x y EY,
  item p f nb c2 k i gt -> nb = S i -> pcs (f nb) c2 <= k -> tm (f i) < tm (f nb) ->
  (forall r j, tatp (ins p c2 j r) r gt -> exists d, dof (ins p c2 j r) r = Some d /\ In x (icells (inst_of d))) ->
  ent (f nb) y = Some EY -> ew EY = true -> In y (ids (hs (f nb) x)) -> ec EY <> c2 -> y < tm (f i) ->
  ek EY < pcs (f nb) (ec EY) /\
  ((exists k1 k2 F1 F2, ek EY < k1 /\ k1 < pcs (f nb) (ec EY) /\ RE (f nb) (ec EY) k1 F1 /\
      einstr p (f nb) F1 = IFn FFull /\ eh F1 = false /\ oc (cs (f nb) (ec EY)) k1 = Some (bt (f nb) (ec EY) k1) /\
      k2 < pcs (f nb) c2 /\ RE (f nb) c2 k2 F2 /\ einstr p (f nb) F2 = IFn FFull /\
      eh F2 = false /\ oc (cs (f nb) c2) k2 = Some (bt (f nb) c2 k2) /\
      y < bt (f nb) (ec EY) k1 /\ bt (f nb) (ec EY) k1 < bt (f nb) c2 k2)
   \/ (fa p (ec EY) (ek EY) /\ exists r j, fa p c2 j /\
        plc p c2 (cs (f (S i)) c2) (pcs (f (S i)) c2) r (S (tm (f i))) (tm (f i)) gt j /\
        (forall jj, jj < pcs (f nb) c2 -> r jj = rg (cs (f nb) c2) jj))).
Proof.
  intros i k c2 gt x y EY Itc Enb Pk Lt Hd AY WY IY Nc Ly.
  pose proof B as (Bsr & Bsp & Brg & Bgo & Bco).
  assert (Rb : run p (f nb)) by (apply (tr_run p f nb T); lia).
  pose proof (proj2 (reach_runQ p (f nb)) Rb) as R.
  pose proof (Inv1_run p (f nb) Rb) as I. pose proof (proj2 (Inv2_run p (f nb) Rb)) as J.
  destruct (j_hist p (f nb) J x y IY) as (EY' & iy & AY' & WY' & EIY & ICY). rewrite AY in AY'. injection AY' as <-.
  destruct (i_et p (f nb) I y EY AY) as (_ & OY).
  assert (EhY : eh EY = false) by (destruct (j_ew p (f nb) J _ EY _ AY eq_refl) as [W1 _]; rewrite WY in W1; destruct (eh EY); [discriminate|reflexivity]).
  rewrite EhY in OY.
  pose proof (core p W Wc f nb T lb gb Bsr Bsp Brg Bgo Bco EVb) as Core.
  destruct (fwd p W Wc f nb T lb gb Bsr Bsp Brg lb gb (tm (f nb)) c2 k i gt (Core (tm (f i)))
              (CONS_base p f nb lb gb Bsp Brg) Itc Pk Lt) as [Rc|[(j & Lj & Fj)|(F' & g' & S' & X' & Co' & Fp & Cg')]].
  - exfalso. destruct Rc as (l' & g' & Sl & Rc). exact (RF l' g' Sl Rc).
  - exfalso. apply plc_le in Fj. rewrite Bsp in Lj. rewrite Enb in Lj. lia.
  - (* c2 at the CAS's place, after a guard()-free run of its own *)
    destruct (Hd _ _ (plc_tat _ _ _ _ _ _ _ _ Fp)) as (d & Dd & Ix).
    destruct Co' as (Fc & EF & NR & NG & Gv).
    assert (EF' : F' = Fc) by exact (app_inv_head _ _ _ EF). subst Fc.
    assert (Co'' : CONS p f nb lb gb (lb ++ F') g' (tm (f i))) by (exists F'; auto).
    destruct (Nat.lt_ge_cases (ek EY) (pcs (f nb) (ec EY))) as [Lu|Gu].
    2:{ exfalso.
        destruct (early_of_pending p f nb T nb (ec EY) (ek EY) y (le_n nb) Gu OY) as (iy' & dy & By & uy & Eay & _ & Tiy).
        assert (Rc : RACY p).
        { apply (pend_meet_x2 (tm (f i)) (lb ++ F') g' c2 d x (ec EY) (ek EY) iy' dy By uy EY Co'' Dd Nc Ix Eay Gu
                   ltac:(rewrite Tiy; exact Ly) ltac:(rewrite Tiy; exact AY) WY ltac:(rewrite EIY; exact ICY)).
          intros q e Lq Q Xe. exfalso. apply Nc. rewrite <- Xe. apply X'. exact (nth_beyond2 F' q e Lq Q). }
        destruct Rc as (l' & g'' & Sl & Rc). exact (RF l' g'' Sl Rc). }
    split; [exact Lu|].
    (* y is an event of the base *)
    destruct (hist_ev p (f nb) lb gb W Rb Bsr Bsp Brg x y IY) as (EY2 & AY2 & _ & _ & _ & Ev).
    rewrite AY in AY2. injection AY2 as <-.
    destruct (Ev Lu) as (q1 & e1 & Q1 & X1 & K1 & Wx & Bt1).
    destruct (wx_sacc e1 x Wx) as (ys & A1 & Iy).
    set (l1 := lb ++ F').
    assert (Sl1 : srun p l1 g') by exact (CONS_run p f nb lb gb Bsr _ _ _ Co'').
    destruct (snext_acc p (fun _ _ => true) g' c2 d Dd) as (wh & Ah & Gh).
    set (eh := fst (snext p (fun _ _ => true) g' c2)) in *. set (gh := snd (snext p (fun _ _ => true) g' c2)).
    assert (St : sstep p g' eh gh) by apply snext_step.
    assert (Xe : sx eh = c2) by apply snext_x.
    assert (Ke : sk eh = sp g' c2) by (destruct (sstep_shape p W _ _ _ St) as (? & _ & _ & Hk & _); rewrite Hk, Xe; reflexivity).
    assert (Rl' : srun p (l1 ++ [eh]) gh) by (econstructor; eauto).
    assert (Lq0 : q1 < length lb) by (apply nth_error_Some; congruence).
    assert (Lq : q1 < length l1) by (unfold l1; rewrite length_app; lia).
    assert (Q1l : nth_error l1 q1 = Some e1) by (unfold l1; rewrite nth_error_app1 by exact Lq0; exact Q1).
    assert (Q1' : nth_error (l1 ++ [eh]) q1 = Some e1) by (rewrite nth_app_old' by exact Lq; exact Q1l).
    assert (FaB : forall c j, j < sp gb c -> j < pcs (f nb) c -> sr gb c j = MIPComp.rrg (f nb) c j)
      by (intros c j _ L; apply Brg; exact L).
    assert (AllP : forall q e, nth_error lb q = Some e -> sk e < pcs (f nb) (sx e)).
    { intros q e Q. rewrite <- Bsp. apply (proj2 (srun_pos p W lb gb Bsr (sx e) (sk e))). eauto. }
    destruct (gsync_dec (l1 ++ [eh]) q1 (length l1) (sx e1) c2) as [G|NGs].
    + left. destruct G as (a & b & f1 & f2 & La & Lab & Lb & F1 & F2 & Sg1 & Sg2 & Xf1 & Xf2).
      assert (Nb : b <> length l1) by (intros ->; rewrite nth_app_last' in F2; injection F2 as <-; congruence).
      assert (F2l : nth_error l1 b = Some f2) by (rewrite nth_app_old' in F2 by lia; exact F2).
      assert (Bl : b < length lb).
      { destruct (Nat.lt_ge_cases b (length lb)) as [Hb|Hb]; [exact Hb|].
        exfalso. pose proof (NG f2 (nth_beyond2 F' b f2 Hb F2l)) as Z. congruence. }
      assert (F2' : nth_error lb b = Some f2) by (unfold l1 in F2l; rewrite nth_error_app1 in F2l by exact Bl; exact F2l).
      assert (F1' : nth_error lb a = Some f1).
      { rewrite nth_app_old' in F1 by lia. unfold l1 in F1. rewrite nth_error_app1 in F1 by lia. exact F1. }
      assert (Sge1 : sg e1 = false) by exact (acc_nog p lb gb q1 e1 ys true W Bsr Q1 A1).
      assert (Na : a <> q1) by (intros ->; rewrite Q1 in F1'; injection F1' as <-; congruence).
      assert (K1' : sk e1 < sk f1) by (apply (srun_order p W lb gb Bsr q1 a e1 f1); auto; lia).
      pose proof (AllP _ _ F1') as P1. pose proof (AllP _ _ F2') as P2.
      pose proof (sg_ffull (IFM := dqmodel) p (f nb) R W lb gb Bsr FaB a f1 F1' P1 Sg1) as I1.
      pose proof (sg_ffull (IFM := dqmodel) p (f nb) R W lb gb Bsr FaB b f2 F2' P2 Sg2) as I2.
      rewrite Xf1 in I1, P1. rewrite Xf2 in I2, P2.
      destruct (acc_cond (IFM := dqmodel) p (f nb) R W lb gb Bsr FaB q1 e1 ys true Q1 (AllP _ _ Q1) A1) as [Ex1 _].
      destruct (n_ent (IFM := dqmodel) p (f nb) R W (sx e1) (sk f1) _ I1 P1 eq_refl) as (F1E & RF1 & EF1).
      destruct (n_ent (IFM := dqmodel) p (f nb) R W c2 (sk f2) _ I2 P2 eq_refl) as (F2E & RF2 & EF2).
      destruct (guard_RE (IFM := dqmodel) p (f nb) R W lb gb Bsr FaB _ _ _ RF1 P1 I1) as [H1 O1].
      destruct (guard_RE (IFM := dqmodel) p (f nb) R W lb gb Bsr FaB _ _ _ RF2 P2 I2) as [H2 O2].
      assert (Bt : MIPComp.bt (f nb) (sx e1) (sk f1) < MIPComp.bt (f nb) c2 (sk f2)).
      { destruct (Nat.lt_ge_cases a b) as [Ab|Ab].
        - pose proof (Bgo a b f1 f2 Ab F1' F2' Sg1 Sg2 ltac:(congruence)) as Tq. rewrite Xf1, Xf2 in Tq. exact Tq.
        - assert (a = b) by lia. subst b. rewrite F1' in F2'. injection F2' as <-. congruence. }
      assert (T1 : MIPComp.bt (f nb) (sx e1) (sk e1) < MIPComp.bt (f nb) (sx e1) (sk f1)).
      { apply (n_tie (IFM := dqmodel) p (f nb) R W (sx e1) (sk e1) (sk f1) _ _ K1' eq_refl I1 Ex1 eq_refl
                 ltac:(right; right; left; reflexivity) P1). }
      rewrite Bt1 in T1. rewrite X1 in *. rewrite K1 in K1'.
      exists (sk f1), (sk f2), F1E, F2E.
      exact (conj K1' (conj P1 (conj RF1 (conj EF1 (conj H1 (conj O1 (conj P2 (conj RF2 (conj EF2 (conj H2
        (conj O2 (conj T1 Bt)))))))))))).
    + right. assert (FF : fa p (sx e1) (sk e1) /\ fa p c2 (sp g' c2)).
      { apply fa2_nn. intros NF.
        apply (RF (l1 ++ [eh]) gh Rl').
        apply (racy_g_mk p (l1 ++ [eh]) q1 (length l1) e1 eh x ys (icells (inst_of d)) true wh).
        - exact Lq.
        - exact Q1'.
        - apply nth_app_last'.
        - rewrite Xe, X1. exact Nc.
        - exact A1.
        - exact Ah.
        - exact Iy.
        - exact Ix.
        - reflexivity.
        - rewrite Xe. exact NGs.
        - rewrite Xe, Ke. exact NF. }
      rewrite X1, K1 in FF. split; [exact (proj1 FF)|]. exists (sr g' c2), (sp g' c2).
      split; [exact (proj2 FF)|]. split; [exact Fp|].
      intros jj Ljj. exact (CONS_rg p W f nb lb gb Bsp Brg _ _ _ Co'' c2 jj Ljj).
Qed.
End Early.

Print Assumptions early_item_sync2.
