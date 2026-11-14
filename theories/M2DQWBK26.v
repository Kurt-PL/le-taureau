(* Part 26: the bridge from an interleaving of the A image to sync_wc.
   In an interleaving l that replays the passed slots of an A run (MIPSync.WIT: faithful registers,
   guard() events in birth order), a guard() pair between an access e1 of c1 and a later event e2 of
   c2 (gsync) gives guard() slots k1 of c1 and k2 of c2 with
       bt (e1) < bt (k1) < bt (k2) < bt (e2)
   in the A run (sync_times; the template is MIPSync.sync_knowQ, without its end).  Through the
   structural part of KR, the two guard() events are guard() events of the write-back state at the
   same times (isFF_AW), so sync_wc applies there: a store u of c1 that is not written back and a
   store w of c2 at e2's time (e.g. a write-back) satisfy wc u <= {u} u wc w (sync_wb).  No image
   knowledge (k_eQ ..) is used: only k_ent, crel_eq, r_pcs, and the A run's slot facts. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO M2SC MIPComp MIPNeg M2Iface MIPSync.
Require Import M2IfaceInst M2DQIfaceInst M2WBRel M2DQWB M2DQWBK1 M2DQWBK3 M2DQWBK22.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

(* ---------- the A side: the times of a guard() pair ---------- *)
Section Iface.
Context `{IFM : Model}.
Set Default Proof Using "All".
Variables (p : prog) (s : st) (R : reach (STEP p) s) (W : wf p).
Variables (l : list sev) (g : sst) (Rl : srun p l g).
Hypothesis Fa : forall c j, j < sp g c -> j < pcs s c -> sr g c j = MIPComp.rrg s c j.

Lemma cfail_fn : forall f r k, cfail (IFn f) r k = false.
Proof. reflexivity. Qed.

(* a guard() at a passed slot with an entry at its time: the entry is the guard()'s, it happened then *)
Lemma guard_RE : forall c k E, RE s c k E -> k < pcs s c -> ins p c k (MIPComp.rrg s c) = IFn FFull ->
  eh E = false /\ oc (cs s c) k = Some (MIPComp.bt s c k).
Proof.
  intros c k E RE0 L I. assert (Eh : eh E = false).
  { destruct (eh E) eqn:H; [|reflexivity]. pose proof (RE_ehc p s R W c k E RE0 L H) as C.
    rewrite I, cfail_fn in C. discriminate. }
  split; [exact Eh|]. destruct RE0 as (A & B & C).
  destruct (i_et p s (nI1 p s R W) _ E A) as (Et & X). rewrite Eh, B, C in X. exact X.
Qed.

Theorem sync_times : forall q1 q2 e1 e2 y1 w1 E2,
  (forall q e, nth_error l q = Some e -> sk e < pcs s (sx e)) -> gordS s l ->
  nth_error l q1 = Some e1 -> nth_error l q2 = Some e2 -> q1 < q2 -> sx e1 <> sx e2 ->
  sacc e1 = Some (y1, w1) -> sg e2 = false ->
  gsync l q1 q2 (sx e1) (sx e2) -> RE s (sx e2) (sk e2) E2 ->
  exists k1 k2 F1 F2,
    sk e1 < k1 /\ k1 < pcs s (sx e1) /\ RE s (sx e1) k1 F1 /\ einstr p s F1 = IFn FFull /\
    eh F1 = false /\ oc (cs s (sx e1)) k1 = Some (MIPComp.bt s (sx e1) k1) /\
    k2 < sk e2 /\ k2 < pcs s (sx e2) /\ RE s (sx e2) k2 F2 /\ einstr p s F2 = IFn FFull /\
    eh F2 = false /\ oc (cs s (sx e2)) k2 = Some (MIPComp.bt s (sx e2) k2) /\
    MIPComp.bt s (sx e1) (sk e1) < MIPComp.bt s (sx e1) k1 /\
    MIPComp.bt s (sx e1) k1 < MIPComp.bt s (sx e2) k2 /\
    MIPComp.bt s (sx e2) k2 < MIPComp.bt s (sx e2) (sk e2).
Proof.
  intros q1 q2 e1 e2 y1 w1 E2 AllP Go Q1 Q2 L N A1 S2 G RE2.
  destruct G as (a & b & f1 & f2 & La & Lab & Lb & F1 & F2 & Sg1 & Sg2 & X1 & X2).
  destruct (acc_cond p s R W l g Rl Fa q1 e1 y1 w1 Q1 (AllP _ _ Q1) A1) as [Ex1 Sg1'].
  assert (Na : a <> q1) by (intros ->; rewrite Q1 in F1; injection F1 as <-; congruence).
  assert (Nb : b <> q2) by (intros ->; rewrite Q2 in F2; injection F2 as <-; congruence).
  assert (K1 : sk e1 < sk f1) by (apply (srun_order p W l g Rl q1 a e1 f1); auto; lia).
  assert (K2 : sk f2 < sk e2) by (apply (srun_order p W l g Rl b q2 f2 e2); auto; lia).
  pose proof (AllP _ _ F1) as P1. pose proof (AllP _ _ F2) as P2. pose proof (AllP _ _ Q2) as Pe2.
  pose proof (sg_ffull p s R W l g Rl Fa a f1 F1 P1 Sg1) as I1.
  pose proof (sg_ffull p s R W l g Rl Fa b f2 F2 P2 Sg2) as I2.
  rewrite X1 in I1, P1. rewrite X2 in I2, P2.
  destruct (n_ent p s R W (sx e1) (sk f1) _ I1 P1 eq_refl) as (F1E & RF1 & EF1).
  destruct (n_ent p s R W (sx e2) (sk f2) _ I2 P2 eq_refl) as (F2E & RF2 & EF2).
  destruct (guard_RE _ _ _ RF1 P1 I1) as [H1 O1]. destruct (guard_RE _ _ _ RF2 P2 I2) as [H2 O2].
  assert (Bt : MIPComp.bt s (sx e1) (sk f1) < MIPComp.bt s (sx e2) (sk f2)).
  { destruct (Nat.lt_ge_cases a b) as [Ab|Ab].
    - pose proof (Go a b f1 f2 Ab F1 F2 Sg1 Sg2 ltac:(congruence)) as T. rewrite X1, X2 in T. exact T.
    - assert (a = b) by lia. subst b. rewrite F1 in F2. injection F2 as <-. congruence. }
  assert (T1 : MIPComp.bt s (sx e1) (sk e1) < MIPComp.bt s (sx e1) (sk f1)).
  { apply (n_tie p s R W (sx e1) (sk e1) (sk f1) _ _ K1 eq_refl I1 Ex1 eq_refl
             ltac:(right; right; left; reflexivity) P1). }
  assert (T2 : MIPComp.bt s (sx e2) (sk f2) < MIPComp.bt s (sx e2) (sk e2)).
  { apply (n_tieE p s R W (sx e2) (sk f2) (sk e2) _ _ E2 K2 I2 eq_refl eq_refl
             ltac:(right; left; reflexivity) Pe2 RE2). }
  exists (sk f1), (sk f2), F1E, F2E.
  exact (conj K1 (conj P1 (conj RF1 (conj EF1 (conj H1 (conj O1 (conj K2 (conj P2 (conj RF2 (conj EF2 (conj H2 (conj O2
    (conj T1 (conj Bt T2)))))))))))))).
Qed.
End Iface.

(* ---------- the state side ---------- *)
Section Tr.
Set Default Proof Using "All".
Variables (p : prog) (Fk : Prop) (Good : nat -> Prop) (sw : nat -> option (cell -> option nat)) (sW sA : st).
Hypothesis RA : run p sA.
Hypothesis Rl : rel sw sW sA.
Hypothesis K : KR Fk Good sw sW sA.

(* a guard() event of the image at a passed slot is one of the state, at the same time *)
Lemma isFF_AW : forall c k t F, ent sA t = Some F -> ec F = c -> ek F = k -> einstr p sA F = IFn FFull ->
  k < pcs sA c -> oc (cs sA c) k = Some t ->
  exists FW, ent sW t = Some FW /\ isFF sW t FW /\ ec FW = c /\ ek FW = k.
Proof.
  intros c k t F E C Kk I L O. destruct (k_ent Fk Good sw sW sA K t F E) as (FW & EW & (_ & S2 & S3 & _)).
  exists FW. split; [exact EW|]. destruct (crel_eq p Fk Good sw sW sA RA Rl K c) as (Oc & _ & Ai & _).
  unfold einstr in I. rewrite C, Kk in I.
  split; [|split; congruence]. unfold isFF. rewrite <- S2, <- S3, C, Kk.
  rewrite <- Ai, <- Oc, <- (r_pcs sw sW sA Rl). auto.
Qed.

(* the entry of the state at an image entry's time has the image entry's context *)
Lemma ent_ec : forall t F FW, ent sA t = Some F -> ent sW t = Some FW -> ec FW = ec F.
Proof.
  intros t F FW E EW. destruct (k_ent Fk Good sw sW sA K t F E) as (FW' & EW' & (_ & S2 & _)).
  rewrite EW in EW'. injection EW' as <-. symmetry. exact S2.
Qed.
End Tr.

(* ---------- the bridge: (WBC'') in the synced case, from an interleaving of the image ---------- *)
Theorem sync_wb : forall p Fk Good sw sW sA, wf p -> run p sA -> rel sw sW sA -> KR Fk Good sw sW sA -> WK sW ->
  forall l g, srun p l g ->
  (forall c j, j < sp g c -> j < pcs sA c -> sr g c j = MIPComp.rrg sA c j) ->
  (forall q e, nth_error l q = Some e -> sk e < pcs sA (sx e)) -> gordS sA l ->
  forall q1 q2 e1 e2 y1 w1 E1 E2 x eu ew0,
  nth_error l q1 = Some e1 -> nth_error l q2 = Some e2 -> q1 < q2 -> sx e1 <> sx e2 ->
  sacc e1 = Some (y1, w1) -> sg e2 = false -> gsync l q1 q2 (sx e1) (sx e2) ->
  RE sA (sx e1) (sk e1) E1 -> RE sA (sx e2) (sk e2) E2 ->
  ent sW (MIPComp.bt sA (sx e1) (sk e1)) = Some eu -> ew eu = true ->
  In (MIPComp.bt sA (sx e1) (sk e1), false) (hs sW x) ->
  ent sW (MIPComp.bt sA (sx e2) (sk e2)) = Some ew0 -> ew ew0 = true ->
  forall z, wc sW (MIPComp.bt sA (sx e1) (sk e1)) z ->
    z = MIPComp.bt sA (sx e1) (sk e1) \/ wc sW (MIPComp.bt sA (sx e2) (sk e2)) z.
Proof.
  intros p Fk Good sw sW sA W RA Rl K Wk l g Sl Fa AllP Go q1 q2 e1 e2 y1 w1 E1 E2 x eu ew0
    Q1 Q2 L N A1 S2 G RE1 RE2 Eu Ewu Iu Ew Eww z Z.
  pose proof (proj2 (reach_runQ p sA) RA) as R.
  destruct (sync_times (IFM := dqmodel) p sA R W l g Sl Fa q1 q2 e1 e2 y1 w1 E2 AllP Go Q1 Q2 L N A1 S2 G RE2)
    as (k1 & k2 & F1 & F2 & _ & P1 & (EF1 & C1 & D1) & I1 & _ & O1 & _ & P2 & (EF2 & C2 & D2) & I2 & _ & O2 & T1 & T2 & T3).
  destruct (isFF_AW p Fk Good sw sW sA RA Rl K _ _ _ F1 EF1 C1 D1 I1 P1 O1) as (G1 & EG1 & FF1 & GC1 & _).
  destruct (isFF_AW p Fk Good sw sW sA RA Rl K _ _ _ F2 EF2 C2 D2 I2 P2 O2) as (G2 & EG2 & FF2 & GC2 & _).
  destruct RE1 as (EA1 & CA1 & _). destruct RE2 as (EA2 & CA2 & _).
  pose proof (ent_ec p Fk Good sw sW sA RA Rl K _ _ _ EA1 Eu) as Cu.
  pose proof (ent_ec p Fk Good sw sW sA RA Rl K _ _ _ EA2 Ew) as Cw.
  apply (sync_wc sW Wk _ eu _ G1 _ G2 _ ew0 x Eu Ewu Iu EG1 FF1 ltac:(congruence) T1 EG2 FF2 T2 Ew Eww
           ltac:(congruence) T3 z Z).
Qed.

Print Assumptions sync_times.
Print Assumptions sync_wb.
