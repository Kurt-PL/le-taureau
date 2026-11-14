(* Part 36: (WBC'') at an early write-back (wbE).
   wbE adds no step of A: the write-back state s1 = wbst s0 c k t1 H'' has the image sA of s0.
   The CAS's read half happened alone, early, at time t1 (an item of M2Mono: early_atR at step ih
   of the image's run).  M2DQWBK34.early_half_sync is applied to the run cut just after that step
   (f (S ih), evok by M2IfaceInst/MIBase.evok_gtr, with its own base): a kept store u of another
   context in a cell of the CAS, made before t1, is passed there, and a guard() pair orders u
   before a guard() of c passed there, or u is fenced.  The guard() events and u's slot are kept
   by the later image sA (M2Trace.Ext); then as in M2DQWBK35:
       wc(u) <= {u} u wc(t1) u vG                                        (wbc_wbE)
   for every kept store u < t1 in a cell of the CAS (the store the write-back stands for is one:
   the write its read half took is older than t1). *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO M2SC M2SCx M2Trace M2DQTrace M2DQMono M2DQPCore.
Require Import MIPComp MIPNeg M2Iface MIPSync MIBase MIPDrf M2IfaceInst M2DQIfaceInst M2Lit.
Require Import M2WBRel M2DQWBPatch M2DQWB M2DQWBK1 M2DQWBK3 M2DQWBK13 M2DQWBK15 M2DQWBK20 M2DQWBK21 M2DQWBK22 M2DQWBK26 M2DQWBK32 M2DQWBK33
  M2DQWBK34 M2DQWBK35.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim M2DQTr.

Lemma trace_le : forall p f n m, trace p f n -> m <= n -> trace p f m.
Proof. intros p f n m (F0 & Fs) L. split; [exact F0|]. intros i Li. apply Fs. lia. Qed.

(* a write of a later state, made before an earlier state of the run, is a write of that state *)
Lemma w_back : forall p f n m x y, wf p -> trace p f n -> m <= n -> y < tm (f m) -> In y (ids (hs (f n) x)) ->
  exists e, ent (f m) y = Some e /\ ent (f n) y = Some e /\ ew e = true /\ In y (ids (hs (f m) x)).
Proof.
  intros p f n m x y W T Lm Ly Iy.
  assert (Rn : run p (f n)) by (apply (tr_run p f n T); lia).
  assert (Rm : run p (f m)) by (apply (tr_run p f n T); lia).
  pose proof (Inv1_run p (f n) Rn) as In1. pose proof (proj2 (Inv2_run p (f n) Rn)) as Jn.
  pose proof (Inv1_run p (f m) Rm) as Im1. pose proof (proj2 (Inv2_run p (f m) Rm)) as Jm.
  pose proof (tr_ext p f n T m n Lm (le_n n)) as X.
  destruct (j_hist p (f n) Jn x y Iy) as (e & i & Ae & We & Ei & Ix).
  destruct (i_et p (f n) In1 y e Ae) as (_ & Oy).
  assert (Eh : eh e = false) by (destruct (j_ew p (f n) Jn _ e _ Ae eq_refl) as [W1 _]; rewrite We in W1; destruct (eh e); [discriminate|reflexivity]).
  rewrite Eh in Oy.
  pose proof (x_ocb _ _ X _ _ _ Oy Ly) as Om.
  destruct (i_oc p (f m) Im1 _ _ _ Om) as (e' & Ae' & Xe & Ke).
  pose proof (x_ent _ _ X _ _ Ae') as Ae''. rewrite Ae in Ae''. injection Ae'' as <-.
  exists e. split; [exact Ae'|]. split; [exact Ae|]. split; [exact We|].
  destruct (j_ew p (f m) Jm y e _ Ae' eq_refl) as [_ W2]. apply (W2 We).
  unfold einstr. rewrite <- Ei in Ix. unfold einstr in Ix.
  destruct (Nat.lt_ge_cases (ek e) (pcs (f m) (ec e))) as [Lk|Gk].
  - rewrite <- (x_ai _ _ X _ _ Lk). exact Ix.
  - assert (Tg : gtrace (STEP (Model := dqmodel) p) f n) by exact T.
    rewrite (i_pending_cellsQ p W f n Tg m (ec e) (ek e) Lm Gk ltac:(rewrite Om; discriminate)). exact Ix.
Qed.

Theorem wbc_wbE : forall p Fk Good sw s1 sA c k t1 xs x u eu,
  wf p -> cellful p -> race_free_g p -> run p sA ->
  rel sw s1 sA -> KR Fk Good sw s1 sA -> runWB p s1 -> evok sA ->
  (exists sAf, star p sA sAf /\ done p sAf) ->
  oh (cs sA c) k = Some t1 -> pcs sA c < k -> casx (ai (cs sA c) k) = Some (Plain, xs) -> In x xs ->
  (forall z, vR (cs s1 c) z -> wc s1 t1 z) ->
  ent s1 u = Some eu -> ew eu = true -> In (u, false) (hs s1 x) -> u < t1 ->
  forall z, wc s1 u z -> z = u \/ wc s1 t1 z \/ vG s1 z.
Proof.
  intros p Fk Good sw s1 sA c k t1 xs x u eu W Wc RF RA Rl K RW EV Fut Oh Pk Cx Ix Rt Eu Ewu Iu Lut z Z.
  pose proof (WK_run p W s1 RW) as Wk.
  destruct (Nat.eq_dec (ec eu) c) as [Ec|Nc].
  { destruct (wk_R s1 Wk u eu Eu Ewu z Z) as [Z1|Z1]; [|left; exact Z1].
    right; left. apply Rt. rewrite <- Ec. exact Z1. }
  destruct (run_trace p sA RA) as (f & n & T & En).
  rewrite <- En in Oh, Pk, Cx.
  destruct (early_of_hpending p f n T n c k t1 (le_n n) Oh) as (ih & xs' & Bd & ud & Ea & Lih & Ti).
  destruct (early_postR p f n c k ih xs' Bd ud Ea) as (OhS & AiS & PcS & _).
  pose proof (tr_ext p f n T (S ih) n ltac:(lia) (le_n n)) as X.
  assert (Exs : xs' = xs).
  { pose proof (x_cash _ _ X c k ltac:(rewrite OhS; discriminate) ltac:(lia)) as Cs.
    rewrite Cx, AiS in Cs. cbn in Cs. injection Cs as <-. reflexivity. }
  subst xs'.
  (* the run cut just after the read half *)
  assert (T' : trace p f (S ih)) by exact (trace_le p f n (S ih) T Lih).
  assert (Ea' : early_atR p f (S ih) c k ih xs Bd ud) by (destruct Ea as (_ & Ea); split; [lia|exact Ea]).
  assert (Tg : gtrace (STEP (Model := dqmodel) p) f n) by exact T.
  assert (EVS : evok (f (S ih))) by (apply (evok_gtr (IFM := dqmodel) p f n Tg); [rewrite En; exact EV|lia]).
  assert (RS : run p (f (S ih))) by (apply (tr_run p f n T); lia).
  destruct (drf_prefix_m2 (IFM := dqmodel) p (f (S ih)) W Wc RF (proj2 (reach_runQ p _) RS) EVS) as (lb & gb & Bsr & Bsp & Brg & Bgo & Bco).
  assert (B : base p (f (S ih)) lb gb) by (split; [exact Bsr|]; split; [exact Bsp|]; split; [exact Brg|]; split; [exact Bgo|exact Bco]).
  assert (PkS : pcs (f (S ih)) c <= k) by (rewrite PcS; destruct Ea as (_ & P & _); exact P).
  (* u in the image, and in the cut run *)
  assert (IuA : In u (ids (hs (f n) x))).
  { rewrite En, (r_hs sw s1 sA Rl x). apply (in_ids_of _ u false). apply in_hers. auto. }
  assert (LuS : u < tm (f (S ih))) by (pose proof (x_tm _ _ (tr_ext p f n T ih (S ih) ltac:(lia) ltac:(lia))); lia).
  destruct (w_back p f n (S ih) x u W T Lih LuS IuA) as (EY & AYS & AY & WY & IYS).
  rewrite En in AY.
  destruct (k_ent Fk Good sw s1 sA K u EY AY) as (eu' & Eu' & (_ & S2 & S3 & _)).
  rewrite Eu in Eu'. injection Eu' as <-.
  destruct (early_half_sync p W Wc RF f (S ih) T' lb gb B EVS ih k c xs Bd ud x u EY Ea' eq_refl PkS Ix AYS WY IYS
              ltac:(rewrite S2; exact Nc) ltac:(rewrite Ti; exact Lut))
    as (Lu & [(k1 & k2 & F1 & F2 & L1 & P1 & (EF1 & C1 & D1) & I1' & H1 & O1 &
              P2 & (EF2 & C2 & D2) & I2' & H2 & O2 & T1 & T2)|Fa]).
  - (* the guard() pair, kept by sA *)
    assert (Bt : forall c0 j, oc (cs (f (S ih)) c0) j = Some (bt (f (S ih)) c0 j) ->
               bt (f n) c0 j = bt (f (S ih)) c0 j /\ oc (cs (f n) c0) j = Some (bt (f n) c0 j)).
    { intros c0 j O. pose proof (x_oc _ _ X _ _ _ O) as O'.
      assert (E : bt (f n) c0 j = bt (f (S ih)) c0 j) by (unfold bt at 1, tmo; rewrite O'; reflexivity).
      split; [exact E|rewrite E; exact O']. }
    destruct (Bt _ _ O1) as (B1 & O1'). destruct (Bt _ _ O2) as (B2 & O2').
    assert (RE1 : ent (f n) (bt (f n) (ec EY) k1) = Some F1) by (rewrite B1; exact (x_ent _ _ X _ _ EF1)).
    assert (RE2 : ent (f n) (bt (f n) c k2) = Some F2) by (rewrite B2; exact (x_ent _ _ X _ _ EF2)).
    assert (P1' : k1 < pcs (f n) (ec EY)) by (pose proof (x_pcs _ _ X (ec EY)); lia).
    assert (P2' : k2 < pcs (f n) c) by (pose proof (x_pcs _ _ X c); lia).
    assert (I1n : einstr p (f n) F1 = IFn FFull) by (unfold einstr in *; rewrite C1, D1 in *; rewrite (x_ai _ _ X _ _ P1); exact I1').
    assert (I2n : einstr p (f n) F2 = IFn FFull) by (unfold einstr in *; rewrite C2, D2 in *; rewrite (x_ai _ _ X _ _ P2); exact I2').
    rewrite En in RE1, RE2, P1', P2', I1n, I2n, O1', O2', B1, B2.
    destruct (isFF_AW p Fk Good sw s1 sA RA Rl K _ _ _ F1 RE1 C1 D1 I1n P1' O1') as (G1 & EG1 & FF1 & GC1 & _).
    destruct (isFF_AW p Fk Good sw s1 sA RA Rl K _ _ _ F2 RE2 C2 D2 I2n P2' O2') as (G2 & EG2 & FF2 & GC2 & _).
    rewrite S2 in GC1. rewrite B1 in EG1, FF1. rewrite B2 in EG2, FF2.
    destruct (wk_ug s1 Wk u eu _ G1 x Eu Ewu Iu EG1 FF1 ltac:(congruence) T1 z Z) as [Z1|Z1]; [|left; exact Z1].
    right; left. apply Rt. pose proof (wk_gg s1 Wk _ G1 _ G2 EG1 FF1 EG2 FF2 T2 z Z1) as Z2.
    pose proof (wk_Rg s1 Wk _ G2 EG2 FF2 z Z2) as Z3. rewrite GC2 in Z3. exact Z3.
  - rewrite S2, S3 in Fa, Lu.
    assert (Lu' : ek eu < pcs s1 (ec eu)).
    { rewrite <- (r_pcs sw s1 sA Rl), <- En. pose proof (x_pcs _ _ X (ec eu)). lia. }
    destruct (kept_slot p Fk Good sw s1 sA u eu x RA Rl K Eu Iu Lu') as (Ou & Ex).
    destruct (fa_wb_all p Fk Good sw s1 sA (ec eu) (ek eu) u eu x W RA Rl K RW Fa Lu' (or_intror Fut) Ou Ex Eu Ewu Iu z Z)
      as [Zg|Zu]; [right; right; exact Zg|left; exact Zu].
Qed.

Print Assumptions trace_le.
Print Assumptions w_back.
Print Assumptions wbc_wbE.
