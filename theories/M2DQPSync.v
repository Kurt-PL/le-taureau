(* M2PSync.v re-checked on M2DQ (stepQ) through M2DQShim; scripts as in M2PSync.v except where marked DQ. *)
(* Model2: interleavings that replay passed slots of a run faithfully, and
   what guard() synchronisation in them says about the run's knowledge. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO M2SC M2DQPComp M2DQPNeg M2DA M2DP M2DQ M2DQInv M2DQIface M2DQShim.

(* guard() events of different contexts stand in the order they were made *)
Definition gordS (s : st) (l : list sev) : Prop :=
  forall a b f1 f2, a < b -> nth_error l a = Some f1 -> nth_error l b = Some f2 ->
  sg f1 = true -> sg f2 = true -> sx f1 <> sx f2 -> bt s (sx f1) (sk f1) < bt s (sx f2) (sk f2).

(* per cell, the interleaving's write order is the history order *)
Definition cohS (s : st) (l : list sev) : Prop :=
  forall a b e1 e2 x, a < b -> nth_error l a = Some e1 -> nth_error l b = Some e2 ->
  writes_x e1 x = true -> writes_x e2 x = true ->
  older (hs s x) (bt s (sx e1) (sk e1)) (bt s (sx e2) (sk e2)).

(* an interleaving of the passed slots of s, with their registers *)
Definition WIT (p : prog) (s : st) : Prop :=
  exists l g, srun p l g /\ (forall c, sp g c = pcs s c) /\
    (forall c j, j < pcs s c -> sr g c j = rg (cs s c) j) /\ gordS s l /\ cohS s l.

Lemma evshape_sg' : forall i r k, snd (evshape i r k) = xgop i r.
Proof.
  intros [md x c|md x c v|md x c e n|f|] r k; unfold xgop, icond, ieval; simpl;
  try (destruct f; reflexivity); try reflexivity; destruct (c r); simpl; reflexivity.
Qed.

Set Default Proof Using "All".
Section S.
Variable p : prog.
Variable s : st.
Hypothesis R : run p s.
Hypothesis W : wf p.

Local Abbreviation bt := (bt s).
Local Abbreviation rrg := (rrg s).

(* an interleaving event at a passed slot, with the run's earlier registers *)
Section Ev.
Variables (l : list sev) (g : sst).
Hypothesis Rl : srun p l g.
Hypothesis Fa : forall c j, j < sp g c -> j < pcs s c -> sr g c j = rrg c j.

Lemma ev_faith : forall q e, nth_error l q = Some e -> sk e < pcs s (sx e) ->
  (sacc e, sg e) = evshape (ins p (sx e) (sk e) (rrg (sx e))) (rrg (sx e)) (sk e).
Proof.
  intros q e Q P. destruct (srun_ev p W l g Rl q e Q) as (i & Hi & Lt & Sh).
  assert (AG : forall j, j < sk e -> sr g (sx e) j = rrg (sx e) j) by (intros j Lj; apply Fa; lia).
  destruct (W (sx e) (sk e) (sr g (sx e)) (rrg (sx e)) AG) as [E1 E2].
  rewrite Hi in E1, E2. rewrite <- E1.
  rewrite Sh. apply evshape_ext; [exact E2|]. apply Fa; auto.
Qed.

Lemma sg_ffull : forall q e, nth_error l q = Some e -> sk e < pcs s (sx e) -> sg e = true ->
  ins p (sx e) (sk e) (rrg (sx e)) = IFn FFull.
Proof.
  intros q e Q P G. pose proof (ev_faith q e Q P) as Sh.
  assert (X : xgop (ins p (sx e) (sk e) (rrg (sx e))) (rrg (sx e)) = true)
    by (rewrite <- (evshape_sg' _ _ (sk e)), <- Sh; exact G).
  unfold xgop in X. destruct (ins p (sx e) (sk e) (rrg (sx e))) as [| | |[]|]; simpl in X; try discriminate; reflexivity.
Qed.

Lemma acc_cond : forall q e y w, nth_error l q = Some e -> sk e < pcs s (sx e) -> sacc e = Some (y, w) ->
  executes (ins p (sx e) (sk e) (rrg (sx e))) (rrg (sx e)) = true /\ sg e = false.
Proof.
  intros q e y w Q P A. pose proof (ev_faith q e Q P) as Sh. rewrite A in Sh.
  destruct (ins p (sx e) (sk e) (rrg (sx e))) as [md x c|md x c v|md x c e0 n|f|]; simpl in Sh;
    [| | |destruct f; inversion Sh|inversion Sh];
  destruct (c (rrg (sx e))) eqn:C; inversion Sh; unfold executes, icond, ieval; simpl; rewrite C; auto.
Qed.

(* guard synchronisation between two passed accesses gives knowledge in the run *)
Lemma sync_know : forall q1 q2 e1 e2 y1 w1 E1 E2,
  (forall q e, nth_error l q = Some e -> sk e < pcs s (sx e)) -> gordS s l ->
  nth_error l q1 = Some e1 -> nth_error l q2 = Some e2 -> q1 < q2 -> sx e1 <> sx e2 ->
  sacc e1 = Some (y1, w1) -> sg e2 = false ->
  gsync l q1 q2 (sx e1) (sx e2) -> RE s (sx e1) (sk e1) E1 -> RE s (sx e2) (sk e2) E2 ->
  vsub (esrc E1) (eP E2).
Proof.
  intros q1 q2 e1 e2 y1 w1 E1 E2 AllP Go Q1 Q2 L N A1 S2 G RE1 RE2.
  destruct G as (a & b & f1 & f2 & La & Lab & Lb & F1 & F2 & Sg1 & Sg2 & X1 & X2).
  destruct (acc_cond q1 e1 y1 w1 Q1 (AllP _ _ Q1) A1) as [Ex1 Sg1'].
  assert (Na : a <> q1) by (intros ->; rewrite Q1 in F1; injection F1 as <-; congruence).
  assert (Nb : b <> q2) by (intros ->; rewrite Q2 in F2; injection F2 as <-; congruence).
  assert (K1 : sk e1 < sk f1) by (apply (srun_order p W l g Rl q1 a e1 f1); auto; lia).
  assert (K2 : sk f2 < sk e2) by (apply (srun_order p W l g Rl b q2 f2 e2); auto; lia).
  pose proof (AllP _ _ F1) as P1. pose proof (AllP _ _ F2) as P2. pose proof (AllP _ _ Q2) as Pe2.
  pose proof (sg_ffull a f1 F1 P1 Sg1) as I1. pose proof (sg_ffull b f2 F2 P2 Sg2) as I2.
  rewrite X1 in I1, P1. rewrite X2 in I2, P2.
  destruct (n_ent p s R W (sx e1) (sk f1) _ I1 P1 eq_refl) as (F1E & RF1 & EF1).
  destruct (n_ent p s R W (sx e2) (sk f2) _ I2 P2 eq_refl) as (F2E & RF2 & EF2).
  destruct (n_po p s R W (sx e1) (sk e1) (sk f1) _ _ E1 F1E K1 eq_refl I1 Ex1
              ltac:(right; right; left; reflexivity) P1 RE1 RF1) as [_ St1].
  destruct (n_po p s R W (sx e2) (sk f2) (sk e2) _ _ F2E E2 K2 I2 eq_refl eq_refl
              ltac:(right; left; reflexivity) Pe2 RF2 RE2) as [St3 _].
  assert (Bt : bt (sx e1) (sk f1) < bt (sx e2) (sk f2)).
  { destruct (Nat.lt_ge_cases a b) as [Ab|Ab].
    - pose proof (Go a b f1 f2 Ab F1 F2 Sg1 Sg2 ltac:(congruence)) as T. rewrite X1, X2 in T. exact T.
    - assert (a = b) by lia. subst b. rewrite F1 in F2. injection F2 as <-. congruence. }
  assert (G1 : xg p s F1E) by (apply (n_xg p s R W _ _ _ _ RF1 EF1); reflexivity).
  assert (G2 : xg p s F2E) by (apply (n_xg p s R W _ _ _ _ RF2 EF2); reflexivity).
  destruct (n_G p s R W _ _ _ _ F1E F2E RF1 RF2 G1 G2 Bt) as [K3 K4].
  intros v Hv. apply St3. apply K3. apply St1. exact Hv.
Qed.

(* the same, as knowledge in order of an access after the second guard() *)
Lemma sync_knowQ : forall q1 q2 e1 e2 y1 w1 E1 E2,
  (forall q e, nth_error l q = Some e -> sk e < pcs s (sx e)) -> gordS s l ->
  nth_error l q1 = Some e1 -> nth_error l q2 = Some e2 -> q1 < q2 -> sx e1 <> sx e2 ->
  sacc e1 = Some (y1, w1) -> sg e2 = false ->
  gsync l q1 q2 (sx e1) (sx e2) -> RE s (sx e1) (sk e1) E1 -> RE s (sx e2) (sk e2) E2 -> xacc p s E2 ->
  vsub (esrc E1) (eQ E2).
Proof.
  intros q1 q2 e1 e2 y1 w1 E1 E2 AllP Go Q1 Q2 L N A1 S2 G RE1 RE2 Xa.
  destruct G as (a & b & f1 & f2 & La & Lab & Lb & F1 & F2 & Sg1 & Sg2 & X1 & X2).
  destruct (acc_cond q1 e1 y1 w1 Q1 (AllP _ _ Q1) A1) as [Ex1 Sg1'].
  assert (Na : a <> q1) by (intros ->; rewrite Q1 in F1; injection F1 as <-; congruence).
  assert (Nb : b <> q2) by (intros ->; rewrite Q2 in F2; injection F2 as <-; congruence).
  assert (K1 : sk e1 < sk f1) by (apply (srun_order p W l g Rl q1 a e1 f1); auto; lia).
  assert (K2 : sk f2 < sk e2) by (apply (srun_order p W l g Rl b q2 f2 e2); auto; lia).
  pose proof (AllP _ _ F1) as P1. pose proof (AllP _ _ F2) as P2. pose proof (AllP _ _ Q2) as Pe2.
  pose proof (sg_ffull a f1 F1 P1 Sg1) as I1. pose proof (sg_ffull b f2 F2 P2 Sg2) as I2.
  rewrite X1 in I1, P1. rewrite X2 in I2, P2.
  destruct (n_ent p s R W (sx e1) (sk f1) _ I1 P1 eq_refl) as (F1E & RF1 & EF1).
  destruct (n_ent p s R W (sx e2) (sk f2) _ I2 P2 eq_refl) as (F2E & RF2 & EF2).
  destruct (n_po p s R W (sx e1) (sk e1) (sk f1) _ _ E1 F1E K1 eq_refl I1 Ex1
              ltac:(right; right; left; reflexivity) P1 RE1 RF1) as [_ St1].
  assert (Bt : bt (sx e1) (sk f1) < bt (sx e2) (sk f2)).
  { destruct (Nat.lt_ge_cases a b) as [Ab|Ab].
    - pose proof (Go a b f1 f2 Ab F1 F2 Sg1 Sg2 ltac:(congruence)) as T. rewrite X1, X2 in T. exact T.
    - assert (a = b) by lia. subst b. rewrite F1 in F2. injection F2 as <-. congruence. }
  assert (G1 : xg p s F1E) by (apply (n_xg p s R W _ _ _ _ RF1 EF1); reflexivity).
  assert (G2 : xg p s F2E) by (apply (n_xg p s R W _ _ _ _ RF2 EF2); reflexivity).
  destruct (n_G p s R W _ _ _ _ F1E F2E RF1 RF2 G1 G2 Bt) as [K3 _].
  assert (Bt2 : bt (sx e2) (sk f2) < bt (sx e2) (sk e2)).
  { apply (n_tieE p s R W (sx e2) (sk f2) (sk e2) _ _ E2 K2 I2 eq_refl eq_refl ltac:(right; left; reflexivity) Pe2 RE2). }
  destruct RF2 as (A2 & B2 & C2). destruct RE2 as (A3 & B3 & C3).
  pose proof (o_gpair p s (iaoO p s (InvO_run p s R)) _ F2E _ E2 A2 A3 ltac:(congruence) Bt2 G2 Xa) as K4.
  intros v Hv. apply K4. apply K3. apply St1. exact Hv.
Qed.

End Ev.
End S.
