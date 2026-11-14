(* Part 27: race-freedom at a context's next access (the in-order case).
   Given an interleaving l of the passed slots of an A run (as MIPSync.WIT), the next instruction
   of context c2 can be appended to l (one SC step, M2SCx.snext).  If it is an access of a cell x
   that a store e1 of l (another context) also covers, race_free_g on the extended interleaving
   leaves two cases (next_sync):
     - a guard() pair: guard() slots k1 of e1's context after e1, and k2 of c2 (passed), with
       bt e1 < bt k1 < bt k2 in the run (so every later time, e.g. a write-back made at this
       step, is after both); or
     - both accesses are fenced (fa).
   fa is recovered from its double negation (fa_nn: its parts are decidable per register file),
   so the case split needs no axiom. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO M2SC M2SCx MIPComp MIPNeg M2Iface MIPSync.
Require Import M2DQWBK26.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

Lemma ffull_dec : forall i : instr, i = IFn FFull \/ i <> IFn FFull.
Proof. intros [| | |[]|]; first [left; reflexivity | right; discriminate]. Qed.

(* a fenced slot, from its double negation *)
Lemma fa_nn : forall p c k, ~ ~ fa p c k -> fa p c k.
Proof.
  intros p c k NN. split.
  - destruct (Nat.le_gt_cases 1 k) as [L|L]; [exact L|]. exfalso. apply NN. intros [H _]. lia.
  - intros r. destruct (ffull_dec (ins p c (k - 1) r)) as [A|A]; [|exfalso; apply NN; intros [_ H]; exact (A (proj1 (H r)))].
    destruct (ffull_dec (ins p c (S k) r)) as [B|B]; [|exfalso; apply NN; intros [_ H]; exact (B (proj2 (H r)))].
    auto.
Qed.

Lemma fa2_nn : forall p c1 k1 c2 k2, ~ ~ (fa p c1 k1 /\ fa p c2 k2) -> fa p c1 k1 /\ fa p c2 k2.
Proof.
  intros p c1 k1 c2 k2 NN. split; apply fa_nn; intros N; apply NN; intros [A B]; auto.
Qed.

Section Iface.
Context `{IFM : Model}.
Set Default Proof Using "All".
Variables (p : prog) (s : st) (R : reach (STEP p) s) (W : wf p).
Variables (l : list sev) (g : sst) (Rl : srun p l g).
Hypothesis Fa : forall c j, j < sp g c -> j < pcs s c -> sr g c j = MIPComp.rrg s c j.
Hypothesis AllP : forall q e, nth_error l q = Some e -> sk e < pcs s (sx e).
Hypothesis Go : gordS s l.
Hypothesis RF : race_free_g p.

Theorem next_sync : forall bs q1 e1 xs1 c2 d x,
  nth_error l q1 = Some e1 -> sacc e1 = Some (xs1, true) -> In x xs1 -> sx e1 <> c2 ->
  dof (ins p c2 (sp g c2) (sr g c2)) (sr g c2) = Some d -> In x (icells (inst_of d)) ->
  (exists k1 k2 F1 F2,
    sk e1 < k1 /\ k1 < pcs s (sx e1) /\ RE s (sx e1) k1 F1 /\ einstr p s F1 = IFn FFull /\
    eh F1 = false /\ oc (cs s (sx e1)) k1 = Some (MIPComp.bt s (sx e1) k1) /\
    k2 < pcs s c2 /\ RE s c2 k2 F2 /\ einstr p s F2 = IFn FFull /\
    eh F2 = false /\ oc (cs s c2) k2 = Some (MIPComp.bt s c2 k2) /\
    MIPComp.bt s (sx e1) (sk e1) < MIPComp.bt s (sx e1) k1 /\
    MIPComp.bt s (sx e1) k1 < MIPComp.bt s c2 k2 /\
    sk (fst (snext p bs g c2)) = sp g c2)
  \/ (fa p (sx e1) (sk e1) /\ fa p c2 (sp g c2)).
Proof.
  intros bs q1 e1 xs1 c2 d x Q1 A1 Ix N Dg Id.
  destruct (snext_acc p bs g c2 d Dg) as (wh & Ah & Gh).
  set (eh := fst (snext p bs g c2)) in *. set (gh := snd (snext p bs g c2)).
  assert (St : sstep p g eh gh) by apply snext_step.
  assert (Xe : sx eh = c2) by apply snext_x.
  assert (Ke : sk eh = sp g c2) by (destruct (sstep_shape p W _ _ _ St) as (? & _ & _ & Hk & _); rewrite Hk, Xe; reflexivity).
  assert (Rl' : srun p (l ++ [eh]) gh) by (econstructor; eauto).
  assert (Lq : q1 < length l) by (apply nth_error_Some; congruence).
  assert (Q1' : nth_error (l ++ [eh]) q1 = Some e1) by (rewrite nth_app_old' by exact Lq; exact Q1).
  destruct (gsync_dec (l ++ [eh]) q1 (length l) (sx e1) c2) as [G|NG].
  - left. destruct G as (a & b & f1 & f2 & La & Lab & Lb & F1 & F2 & Sg1 & Sg2 & X1 & X2).
    assert (Nb : b <> length l) by (intros ->; rewrite nth_app_last' in F2; injection F2 as <-; congruence).
    assert (F2' : nth_error l b = Some f2) by (rewrite nth_app_old' in F2 by lia; exact F2).
    assert (F1' : nth_error l a = Some f1) by (rewrite nth_app_old' in F1 by lia; exact F1).
    assert (Sge1 : sg e1 = false) by exact (acc_nog p l g q1 e1 xs1 true W Rl Q1 A1).
    assert (Na : a <> q1) by (intros ->; rewrite Q1 in F1'; injection F1' as <-; congruence).
    assert (K1 : sk e1 < sk f1) by (apply (srun_order p W l g Rl q1 a e1 f1); auto; lia).
    pose proof (AllP _ _ F1') as P1. pose proof (AllP _ _ F2') as P2.
    pose proof (sg_ffull p s R W l g Rl Fa a f1 F1' P1 Sg1) as I1.
    pose proof (sg_ffull p s R W l g Rl Fa b f2 F2' P2 Sg2) as I2.
    rewrite X1 in I1, P1. rewrite X2 in I2, P2.
    destruct (acc_cond p s R W l g Rl Fa q1 e1 xs1 true Q1 (AllP _ _ Q1) A1) as [Ex1 _].
    destruct (n_ent p s R W (sx e1) (sk f1) _ I1 P1 eq_refl) as (F1E & RF1 & EF1).
    destruct (n_ent p s R W c2 (sk f2) _ I2 P2 eq_refl) as (F2E & RF2 & EF2).
    destruct (guard_RE p s R W l g Rl Fa _ _ _ RF1 P1 I1) as [H1 O1].
    destruct (guard_RE p s R W l g Rl Fa _ _ _ RF2 P2 I2) as [H2 O2].
    assert (Bt : MIPComp.bt s (sx e1) (sk f1) < MIPComp.bt s c2 (sk f2)).
    { destruct (Nat.lt_ge_cases a b) as [Ab|Ab].
      - pose proof (Go a b f1 f2 Ab F1' F2' Sg1 Sg2 ltac:(congruence)) as T. rewrite X1, X2 in T. exact T.
      - assert (a = b) by lia. subst b. rewrite F1' in F2'. injection F2' as <-. congruence. }
    assert (T1 : MIPComp.bt s (sx e1) (sk e1) < MIPComp.bt s (sx e1) (sk f1)).
    { apply (n_tie p s R W (sx e1) (sk e1) (sk f1) _ _ K1 eq_refl I1 Ex1 eq_refl
               ltac:(right; right; left; reflexivity) P1). }
    exists (sk f1), (sk f2), F1E, F2E.
    exact (conj K1 (conj P1 (conj RF1 (conj EF1 (conj H1 (conj O1 (conj P2 (conj RF2 (conj EF2 (conj H2
      (conj O2 (conj T1 (conj Bt Ke))))))))))))).
  - right. apply fa2_nn. intros NF.
    apply (RF (l ++ [eh]) gh Rl').
    apply (racy_g_mk p (l ++ [eh]) q1 (length l) e1 eh x xs1 (icells (inst_of d)) true wh).
    + exact Lq.
    + exact Q1'.
    + apply nth_app_last'.
    + congruence.
    + exact A1.
    + exact Ah.
    + exact Ix.
    + exact Id.
    + reflexivity.
    + rewrite Xe. exact NG.
    + rewrite Xe, Ke. exact NF.
Qed.
End Iface.

Print Assumptions fa_nn.
Print Assumptions next_sync.
