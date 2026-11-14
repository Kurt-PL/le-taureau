(* Part 49: the knowledge edges up to a double negation, and G2 from one obligation
   per link.  KGn / KCn: every knowledge edge of the image is, up to a double negation, a path of
   the state's graphs: what the image knows in order holds only under a
   double negation).  evok_image_nn: the image is evok when the state is (the goal of evok is a
   negation, so the double negation costs nothing).
   LinkK p: at every link of a chain, the knowledge edges of the new image are paths of the new
   state, given everything known at the earlier node (UK, WBCall, KGn, KCn, evok of the earlier
   image) and the accumulator from the end (evok of the new state, a finished future of the new
   image).  drf_sc_WB_of_link: LinkK gives G2 (drf_sc over stepWB) by a forward induction along
   the chain of M2DQWBK45 (UK, WBCall, KGn, KCn at every node). *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Lit.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2InvO M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB.
Require Import M2DQWBK1 M2DQWBK3 M2DQWBK13 M2DQWBK15 M2DQWBK17 M2DQWBK37 M2DQWBK39 M2DQWBK40 M2DQWBK45 M2DQWBK48.
Require Import M2Iface M2IfaceInst M2DQIfaceInst M2DQIfaceUse M2DQWBFsc.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

Definition KGn (s sA : st) : Prop :=
  forall a b e, nth_error (lg sA) b = Some e -> eQ e a -> a <> b -> ~ ~ Pth s a b.
Definition KCn (s sA : st) : Prop :=
  forall x a b e, nth_error (lg sA) b = Some e -> In x (eC e) -> (eQ e a \/ eQc e a) ->
    In a (ids (hs sA x)) -> a <> b -> ~ ~ clos_trans nat (cedge s x) a b.

Lemma KG_KGn : forall s sA, KG s sA -> KGn s sA.
Proof. intros s sA H a b e E Q N NP. exact (NP (H a b e E Q N)). Qed.
Lemma KC_KCn : forall s sA, KC s sA -> KCn s sA.
Proof. intros s sA H x a b e E I Q Ia N NP. exact (NP (H x a b e E I Q Ia N)). Qed.

(* double negation along a transitive closure *)
Lemma ct_nn : forall (R1 R2 : nat -> nat -> Prop), (forall a b, R1 a b -> ~ ~ clos_trans nat R2 a b) ->
  forall a b, clos_trans nat R1 a b -> ~ ~ clos_trans nat R2 a b.
Proof.
  intros R1 R2 H a b T. induction T as [a b E|a b c _ IH1 _ IH2]; [exact (H a b E)|].
  intros N. apply IH1. intros P1. apply IH2. intros P2. exact (N (t_trans _ _ a b c P1 P2)).
Qed.

Section E.
Set Default Proof Using "All".
Variables (Fk : Prop) (Good : nat -> Prop) (sw : nat -> option (cell -> option nat)) (s sA : st).
Hypothesis Rl : rel sw s sA.
Hypothesis K : KR Fk Good sw s sA.

Lemma gedge_Wn : KGn s sA -> forall a b, gedge sA a b -> ~ ~ Pth s a b.
Proof.
  intros HG a b [(x & O)|[(e & x & Ea & Ix & Ib & Nb & M)|(e & Eb & Q & Nab)]].
  - intros N. apply N. constructor. left. exists x. rewrite (r_hs sw s sA Rl x) in O. exact (older_hers _ _ _ O).
  - intros N. apply N. constructor. right; left. destruct (fr_W Fk Good sw s sA Rl K e x a b Ea Ix Ib Nb M) as (eW & H).
    exists eW, x. exact H.
  - exact (HG a b e Eb Q Nab).
Qed.

Lemma cedge_Wn : KCn s sA -> forall x a b, cedge sA x a b -> ~ ~ clos_trans nat (cedge s x) a b.
Proof.
  intros HC x a b [O|[(e & Ea & Ix & Ib & Nb & M)|[(e & Eb & Ix & Ef & Nab)|[(e & Eb & Ix & Q & Ia & Nab)|(ea & eb & Ea & Eb & C & Lk & Xa & Xb)]]]].
  - intros N. apply N. constructor. left. rewrite (r_hs sw s sA Rl x) in O. exact (older_hers _ _ _ O).
  - intros N. apply N. constructor. right; left. exact (fr_W Fk Good sw s sA Rl K e x a b Ea Ix Ib Nb M).
  - intros N. apply N. destruct (rf_W Fk Good sw s sA Rl K e x a b Eb Ef) as (eW & w0 & EW & Ew & ER & [<-|O]).
    + constructor. right; right; left. exists eW. split; [exact EW|]. split; [rewrite ER; exact Ix|]. auto.
    + destruct (Nat.eq_dec w0 b) as [->|Nw]; [constructor; left; exact O|].
      apply (t_trans _ _ _ w0); constructor; [left; exact O|].
      right; right; left. exists eW. split; [exact EW|]. split; [rewrite ER; exact Ix|]. auto.
  - exact (HC x a b e Eb Ix Q Ia Nab).
  - intros N. apply N. destruct (k_ent Fk Good sw s sA K a ea Ea) as (fa & Fa & (_ & A2 & A3 & A4 & _)).
    destruct (k_ent Fk Good sw s sA K b eb Eb) as (fb & Fb & (_ & B2 & B3 & B4 & _)).
    constructor. right; right; right; right. exists fa, fb. split; [exact Fa|]. split; [exact Fb|].
    rewrite <- A2, <- B2, <- A3, <- B3, <- A4, <- B4. auto.
Qed.

Theorem evok_image_nn : KGn s sA -> KCn s sA -> evok s -> evok sA.
Proof.
  intros HG HC (EG & EC). split.
  - intros a C. exact (ct_nn _ _ (gedge_Wn HG) a a C (EG a)).
  - intros x a C. exact (ct_nn _ _ (cedge_Wn HC x) a a C (EC x a)).
Qed.
End E.

(* ---------- G2 from one obligation per link ---------- *)
Definition G0 : nat -> Prop := fun _ => False.

Definition LinkK (p : prog) : Prop := forall sW sw sA sw' sW' sA',
  wch p False G0 sW sw sA -> wlink p False G0 sw sW sA sw' sW' sA' ->
  run p sA' -> rel sw' sW' sA' -> KR False G0 sw' sW' sA' ->
  UK sw sW sA -> WBCall sW -> UK sw' sW' sA' ->
  KGn sW sA -> KCn sW sA -> evok sA -> evok sW' -> (exists sAf, star p sA' sAf /\ done p sAf) ->
  KGn sW' sA' /\ KCn sW' sA'.

Lemma KGn_init : KGn sinit sinit.
Proof. intros a b e E. destruct b; discriminate. Qed.
Lemma KCn_init : KCn sinit sinit.
Proof. intros x a b e E. destruct b; discriminate. Qed.

Section Fw.
Variables (p : prog) (W : wf p) (Wc : cellful p) (RF : race_free_g p) (LK : LinkK p).

(* UK, WBCall, KGn, KCn at every node, given the accumulator from the end *)
Lemma chain_fwd : forall sW sw sA, wchU p False G0 sW sw sA ->
  (exists sAf, star p sA sAf /\ done p sAf) -> evok sW ->
  UK sw sW sA /\ WBCall sW /\ KGn sW sA /\ KCn sW sA.
Proof.
  intros sW sw sA Ch. induction Ch as [|sW sw sA sW' sw' sA' Ch IH L RA' R' K' KU']; intros Fut' EV'.
  - exact (conj UK_init (conj WBCall_init (conj KGn_init KCn_init))).
  - destruct (wlink_back p False G0 sw sW sA sw' sW' sA' L Fut' EV') as [Fut EV].
    destruct (IH Fut EV) as (U0 & WB & G & C).
    pose proof (wchU_wch p False G0 sW sw sA Ch) as Ch'.
    pose proof (evok_image_nn False G0 sw sW sA (wch_rel p False G0 sW sw sA Ch') (wch_KR p False G0 sW sw sA Ch') G C EV) as EVA.
    pose proof (KU' U0 WB) as U1.
    destruct (LK sW sw sA sw' sW' sA' Ch' L RA' R' K' U0 WB U1 G C EVA EV' Fut') as [G' C'].
    pose proof (evok_image_nn False G0 sw' sW' sA' R' K' G' C' EV') as EVA'.
    pose proof (WBCall_link p W False G0 sW sw sA sw' sW' sA' Wc RF Ch' L RA' R' K' EVA EVA' Fut' WB) as WB'.
    exact (conj U1 (conj WB' (conj G' C'))).
Qed.

(* G2, given the obligation at every link *)
Theorem drf_sc_WB_of_link : forall s, runWB p s -> done p s -> evok s ->
  exists l g, srun p l g /\ (forall c, sp g c = pcs s c) /\
    (forall c j, j < pcs s c -> sr g c j = rg (cs s c) j) /\ (forall x, sm g x = final s x).
Proof.
  intros s RW D EV.
  destruct (runWBU_chain p W False G0 s RW (fun F => False_ind _ F) (fun F => False_ind _ F)) as (sw & sA & Ch).
  pose proof (wchU_wch p False G0 s sw sA Ch) as Ch'.
  destruct (chain_fwd s sw sA Ch (wch_done p False G0 s sw sA Ch' D) EV) as (_ & _ & G & C).
  exact (drf_sc_WB_of_image p s sw sA W Wc RF D (wch_run p False G0 s sw sA Ch') (wch_rel p False G0 s sw sA Ch')
           (evok_image_nn False G0 sw s sA (wch_rel p False G0 s sw sA Ch') (wch_KR p False G0 s sw sA Ch') G C EV)).
Qed.
End Fw.

Print Assumptions evok_image_nn.
Print Assumptions chain_fwd.
Print Assumptions drf_sc_WB_of_link.
