(* Fenced code over the write-back model, reduced to one open goal.
   WB_sc_of_image: a finished runWB whose A image (runWB_sim / rel) has no cycle of programme order
   and coherence between its accesses (MIFSC's acyclic Rb) has an interleaving with the same
   registers, passed slots and final storage.  The A image is an A-run, so MIFSC's replay applies
   to it unchanged; only its acyclicity is open (MIFSC.acyc derives it from evok of the image,
   and evok does not carry from a write-back state to its image: MPwb). *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Iface M2IfaceInst M2DQIfaceInst MIFSC Topo M2WBRel M2DQWB.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQShim.

Lemma rel_done : forall p sw s sA, rel sw s sA -> done p s -> done p sA.
Proof.
  intros p sw s sA Rl (n & F & Cp). exists n. split; [exact F|]. intros c Hc. destruct (Cp c Hc) as [L1 K].
  rewrite (r_pcs sw s sA Rl). split; [exact L1|]. intros k Hk.
  destruct (r_cr sw s sA Rl c) as ((rv' & rw' & P & A & R' & O & Og & E) & _). rewrite E. exact (K k Hk).
Qed.

Lemma rel_rg : forall sw s sA, rel sw s sA -> forall c k, rg (cs sA c) k = rg (cs s c) k.
Proof.
  intros sw s sA Rl c k. destruct (r_cr sw s sA Rl c) as ((rv' & rw' & P & A & R' & O & Og & E) & _). rewrite E. reflexivity.
Qed.

Theorem WB_sc_of_image : forall p s, wf p -> runWB p s -> done p s ->
  (forall sw sA, run p sA -> rel sw s sA -> acyclic node (Rb p sA) (L sA)) ->
  exists l g, srun p l g /\ (forall c, sp g c = pcs s c) /\
    (forall c j, j < pcs s c -> sr g c j = rg (cs s c) j) /\ (forall x, sm g x = final s x).
Proof.
  intros p s W RW D AC. destruct (runWB_sim p W s RW) as (sw & sA & RA & Rl).
  assert (R : reach (STEP (Model := dqmodel) p) sA) by (apply (proj2 (reach_runQ p sA)); exact RA).
  assert (DA : done p sA) by exact (rel_done p sw s sA Rl D).
  destruct (topo node (node_eq_dec (IFM := dqmodel) p sA R DA W) (Rb p sA) (L sA) (L_nodup (IFM := dqmodel) p sA R DA W) (AC sw sA RA Rl)) as (ord & P & O).
  set (CP0 := fun _ : cell => true).
  assert (OP : forall i j a b, nth_error ord i = Some a -> nth_error ord j = Some b -> pob a b = true -> i < j).
  { intros i j a b Qa Qb H. apply (O i j a b Qa Qb). unfold Rb. rewrite H. reflexivity. }
  assert (OC : forall i j a b x, nth_error ord i = Some a -> nth_error ord j = Some b -> combx p sA x a b = true ->
            CP0 x = true -> i < j).
  { intros i j a b x Qa Qb H _. apply (O i j a b Qa Qb). unfold Rb.
    assert (comb p sA a b = true) by (apply comb_x; eauto). rewrite H0, orb_true_r. reflexivity. }
  destruct (full' (IFM := dqmodel) p sA R DA W ord P CP0 OP OC (fun _ => eq_refl)) as (l & g & Co).
  exists l, g. split; [apply Co|].
  pose proof (sp_full' (IFM := dqmodel) p sA R DA W ord P CP0 OP OC l g Co) as Sp.
  split; [intros c; rewrite Sp; exact (f_equal (fun f => f c) (r_pcs sw s sA Rl))|].
  split.
  - intros c j Lj. rewrite <- (rel_rg sw s sA Rl).
    assert (Lj' : j < sp g c) by (rewrite Sp, (r_pcs sw s sA Rl); exact Lj).
    destruct Co as (_ & _ & _ & Dd). apply Dd. auto.
  - intros x. rewrite (mem_full' (IFM := dqmodel) p sA R DA W ord P CP0 OP OC l g Co x eq_refl).
    exact (final_rel sw s sA Rl x).
Qed.

(* the A image of a WB state that is evok has the conclusion: the base theorem, through the image *)
Theorem WB_fenced_of_image_evok : forall p s, wf p -> fenced p -> runWB p s -> done p s ->
  (forall sw sA, run p sA -> rel sw s sA -> evok sA) ->
  exists l g, srun p l g /\ (forall c, sp g c = pcs s c) /\
    (forall c j, j < pcs s c -> sr g c j = rg (cs s c) j) /\ (forall x, sm g x = final s x).
Proof.
  intros p s W F RW D EV. apply (WB_sc_of_image p s W RW D). intros sw sA RA Rl.
  apply (acyc (IFM := dqmodel) p sA (proj2 (reach_runQ p sA) RA) (rel_done p sw s sA Rl D) W F (EV sw sA RA Rl)).
Qed.

Print Assumptions WB_sc_of_image.
Print Assumptions WB_fenced_of_image_evok.
