(* Part 35: a trace of A extended by one step (trace_snoc), and a trace ending in every run of A
   (run_trace). *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO M2SC M2SCx M2Trace M2DQTrace M2DQMono M2DQPCore.
Require Import MIPComp MIPNeg M2Iface MIPSync MIBase MIPDrf M2IfaceInst M2DQIfaceInst M2Lit.
Require Import M2WBRel M2DQWBPatch M2DQWB M2DQWBK1 M2DQWBK3 M2DQWBK13 M2DQWBK15 M2DQWBK20 M2DQWBK21 M2DQWBK22 M2DQWBK26 M2DQWBK32 M2DQWBK33 M2DQWBK34.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim M2DQTr.

(* a trace of A extended by one step *)
Lemma trace_snoc : forall p f n s', trace p f n -> step p (f n) s' ->
  trace p (fun j => if Nat.leb j n then f j else s') (S n).
Proof.
  intros p f n s' (F0 & Fs) St. split.
  - cbn. exact F0.
  - intros i Li. destruct (Nat.eq_dec i n) as [->|Ni].
    + rewrite Nat.leb_refl. replace (Nat.leb (S n) n) with false by (symmetry; apply Nat.leb_gt; lia). exact St.
    + replace (Nat.leb i n) with true by (symmetry; apply Nat.leb_le; lia).
      replace (Nat.leb (S i) n) with true by (symmetry; apply Nat.leb_le; lia). apply Fs. lia.
Qed.

(* every A run has a trace ending in it *)
Lemma run_trace : forall p s, run p s -> exists f n, trace p f n /\ f n = s.
Proof.
  intros p s R. destruct (reach_gtrace (IFM := dqmodel) p s (proj2 (reach_runQ p s) R)) as (f & n & T & E).
  exists f, n. split; [exact T|exact E].
Qed.

Print Assumptions trace_snoc.
Print Assumptions run_trace.
