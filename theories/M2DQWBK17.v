(* Part 17: race-free code over the write-back model (G2), reduced to the knowledge edges.
   Every edge of the A image's event graphs (gedge, and cedge per cell) that is not a knowledge
   edge (eQ / eQc) is a path of the state's graphs, for every runWB (no premise on the programme):
   history order, reads before newer writes, reads-from (through the write the written-back store
   stands for), a context's own order on a cell.  So the image is evok when the state is and the
   image's knowledge edges are paths of the state (KG, KC); then the base DRF theorem on the image
   gives drf_sc over stepWB (drf_sc_WB_of_knowledge). *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2InvO M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB.
Require Import M2DQWBK1 M2DQWBK3 M2DQWBK13 M2DQWBK15.
Require Import M2Iface M2IfaceInst M2DQIfaceInst M2DQIfaceUse M2DQWBFsc.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

Section E.
Set Default Proof Using "All".
Variables (Fk : Prop) (Good : nat -> Prop) (sw : nat -> option (cell -> option nat)) (s sA : st).
Hypothesis Rl : rel sw s sA.
Hypothesis K : KR Fk Good sw s sA.

(* a read before a newer write, in the image, is one in the state *)
Lemma fr_W : forall e x a b, nth_error (lg sA) a = Some e -> In x (eR e) -> In b (ids (hs sA x)) -> b <> a ->
  match erf e x with None => True | Some u => older (hs sA x) u b end ->
  exists eW, nth_error (lg s) a = Some eW /\ In x (eR eW) /\ In b (ids (hs s x)) /\ b <> a /\
    match erf eW x with None => True | Some u => older (hs s x) u b end.
Proof.
  intros e x a b Ea Ix Ib Nb M. destruct (k_ent Fk Good sw s sA K a e Ea) as (eW & EW & Se).
  pose proof Se as (_ & _ & _ & _ & S5 & _ & S7 & S8 & _).
  rewrite (r_hs sw s sA Rl x) in Ib, M.
  assert (Ibf : In (b, false) (hs s x)).
  { unfold ids in Ib. apply in_map_iff in Ib. destruct Ib as ([b' f] & Eb & Ib). cbn in Eb. subst b'.
    apply in_hers in Ib. destruct Ib as [Ib Ef]. cbn in Ef. subst f. exact Ib. }
  exists eW. split; [exact EW|]. split; [rewrite <- S5; exact Ix|].
  split; [exact (in_ids_of _ _ _ Ibf)|]. split; [exact Nb|].
  destruct (erf eW x) as [w0|] eqn:Ew; [|exact Logic.I].
  pose proof (S8 x w0 Ew) as Iw. rewrite S7, Ew in M. cbn [pi] in M.
  pose proof (w_nodup Fk Good sw s sA K x) as N.
  destruct (in_ids_fl _ _ Iw) as [[|] Iwf].
  - destruct (w_bet Fk Good sw s sA K x w0 Iwf) as (f & Sf & Sg). rewrite Sf in M.
    exact (fr_seg (hs s x) w0 (f x) b N Sg Ibf M).
  - destruct (r_kept sw s sA Rl x w0 Iwf) as [Sn _]. rewrite Sn in M. exact (older_hers _ _ _ M).
Qed.

(* the write a read of the image took is the one the state's read took, or older in the cell *)
Lemma rf_W : forall e x a b, nth_error (lg sA) b = Some e -> erf e x = Some a ->
  exists eW w0, nth_error (lg s) b = Some eW /\ erf eW x = Some w0 /\ eR eW = eR e /\ (a = w0 \/ older (hs s x) a w0).
Proof.
  intros e x a b Eb Ea. destruct (k_ent Fk Good sw s sA K b e Eb) as (eW & EW & Se).
  pose proof Se as (_ & _ & _ & _ & S5 & _ & S7 & S8 & _).
  rewrite S7 in Ea. destruct (erf eW x) as [w0|] eqn:Ew; [|discriminate Ea].
  exists eW, w0. split; [exact EW|]. split; [exact Ew|]. split; [symmetry; exact S5|].
  pose proof (S8 x w0 Ew) as Iw. cbn [pi] in Ea. destruct (sw w0) as [f|] eqn:Sw.
  - right. destruct (in_ids_fl _ _ Iw) as [[|] Iwf].
    + destruct (w_bet Fk Good sw s sA K x w0 Iwf) as (f' & Sf & Sg). rewrite Sw in Sf. injection Sf as <-.
      rewrite Ea in Sg. destruct Sg as (h0 & h1 & h2 & E & _). rewrite E.
      exists (h0 ++ [(a, false)]), (h1 ++ (w0, true) :: h2). split; [rewrite <- app_assoc; reflexivity|].
      split; rewrite ids_app, in_app_iff; [right; left; reflexivity|right; left; reflexivity].
    + destruct (r_kept sw s sA Rl x w0 Iwf) as [Sn _]. congruence.
  - left. injection Ea as ->. reflexivity.
Qed.

(* ---------- the edges of the image ---------- *)
(* KG: a knowledge edge of the image's event graph is a path of the state's *)
Definition KG : Prop := forall a b e, nth_error (lg sA) b = Some e -> eQ e a -> a <> b -> Pth s a b.
(* KC: a knowledge edge of the image's graph of cell x is a path of the state's *)
Definition KC : Prop := forall x a b e, nth_error (lg sA) b = Some e -> In x (eC e) -> (eQ e a \/ eQc e a) ->
  In a (ids (hs sA x)) -> a <> b -> clos_trans nat (cedge s x) a b.

Lemma gedge_W : KG -> forall a b, gedge sA a b -> Pth s a b.
Proof.
  intros HG a b [(x & O)|[(e & x & Ea & Ix & Ib & Nb & M)|(e & Eb & Q & Nab)]].
  - constructor. left. exists x. rewrite (r_hs sw s sA Rl x) in O. exact (older_hers _ _ _ O).
  - constructor. right; left. destruct (fr_W e x a b Ea Ix Ib Nb M) as (eW & H). exists eW, x. exact H.
  - exact (HG a b e Eb Q Nab).
Qed.

Lemma cedge_W : KC -> forall x a b, cedge sA x a b -> clos_trans nat (cedge s x) a b.
Proof.
  intros HC x a b [O|[(e & Ea & Ix & Ib & Nb & M)|[(e & Eb & Ix & Ef & Nab)|[(e & Eb & Ix & Q & Ia & Nab)|(ea & eb & Ea & Eb & C & Lk & Xa & Xb)]]]].
  - constructor. left. rewrite (r_hs sw s sA Rl x) in O. exact (older_hers _ _ _ O).
  - constructor. right; left. exact (fr_W e x a b Ea Ix Ib Nb M).
  - destruct (rf_W e x a b Eb Ef) as (eW & w0 & EW & Ew & ER & [<-|O]).
    + constructor. right; right; left. exists eW. split; [exact EW|]. split; [rewrite ER; exact Ix|]. auto.
    + destruct (Nat.eq_dec w0 b) as [->|Nw]; [constructor; left; exact O|].
      apply (t_trans _ _ _ w0); constructor; [left; exact O|].
      right; right; left. exists eW. split; [exact EW|]. split; [rewrite ER; exact Ix|]. auto.
  - exact (HC x a b e Eb Ix Q Ia Nab).
  - destruct (k_ent Fk Good sw s sA K a ea Ea) as (fa & Fa & (_ & A2 & A3 & A4 & _)).
    destruct (k_ent Fk Good sw s sA K b eb Eb) as (fb & Fb & (_ & B2 & B3 & B4 & _)).
    constructor. right; right; right; right. exists fa, fb. split; [exact Fa|]. split; [exact Fb|].
    rewrite <- A2, <- B2, <- A3, <- B3, <- A4, <- B4. auto.
Qed.

(* the image is evok when the state is and its knowledge edges are paths of the state *)
Theorem evok_image : KG -> KC -> evok s -> evok sA.
Proof.
  intros HG HC (EG & EC). split.
  - intros a C. apply (EG a).
    assert (G : forall a b, clos_trans nat (gedge sA) a b -> clos_trans nat (gedge s) a b).
    { intros a0 b0 H. induction H as [a0 b0 H|a0 b0 c' _ IH1 _ IH2]; [exact (gedge_W HG a0 b0 H)|exact (t_trans _ _ a0 b0 c' IH1 IH2)]. }
    exact (G a a C).
  - intros x a C. apply (EC x a).
    assert (G : forall a b, clos_trans nat (cedge sA x) a b -> clos_trans nat (cedge s x) a b).
    { intros a0 b0 H. induction H as [a0 b0 H|a0 b0 c' _ IH1 _ IH2]; [exact (cedge_W HC x a0 b0 H)|exact (t_trans _ _ a0 b0 c' IH1 IH2)]. }
    exact (G a a C).
Qed.
End E.

(* ---------- G2, reduced ---------- *)
(* the conclusion through one image that is evok: the base DRF theorem on the image *)
Theorem drf_sc_WB_of_image : forall p s sw sA, wf p -> cellful p -> race_free_g p -> done p s ->
  run p sA -> rel sw s sA -> evok sA ->
  exists l g, srun p l g /\ (forall c, sp g c = pcs s c) /\
    (forall c j, j < pcs s c -> sr g c j = rg (cs s c) j) /\ (forall x, sm g x = final s x).
Proof.
  intros p s sw sA W Wc RF D RA Rl EV.
  destruct (drf_sc_dq p sA W Wc RF RA (rel_done p sw s sA Rl D) EV) as (l & g & Sr & Sp & Sg & Sm).
  exists l, g. split; [exact Sr|]. split; [intros c; rewrite Sp; exact (f_equal (fun f => f c) (r_pcs sw s sA Rl))|].
  split.
  - intros c j Lj. rewrite <- (rel_rg sw s sA Rl). apply Sg. rewrite (r_pcs sw s sA Rl). exact Lj.
  - intros x. rewrite Sm. exact (final_rel sw s sA Rl x).
Qed.

(* G2 holds for every finished runWB with an image (runWBK, any Fk/Good) whose knowledge edges are
   paths of the state *)
Theorem drf_sc_WB_of_knowledge : forall p s, wf p -> cellful p -> race_free_g p -> runWB p s -> done p s -> evok s ->
  (exists Fk Good sw sA, run p sA /\ rel sw s sA /\ KR Fk Good sw s sA /\ KG s sA /\ KC s sA) ->
  exists l g, srun p l g /\ (forall c, sp g c = pcs s c) /\
    (forall c j, j < pcs s c -> sr g c j = rg (cs s c) j) /\ (forall x, sm g x = final s x).
Proof.
  intros p s W Wc RF RW D EV (Fk & Good & sw & sA & RA & Rl & K & HG & HC).
  exact (drf_sc_WB_of_image p s sw sA W Wc RF D RA Rl (evok_image Fk Good sw s sA Rl K HG HC EV)).
Qed.

Print Assumptions evok_image.
Print Assumptions drf_sc_WB_of_knowledge.
