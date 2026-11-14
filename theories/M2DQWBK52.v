(* Part 52: NewK (M2DQWBK50) from its residue.  At a link whose step of A logs an entry
   t in the image and in the state (wbA; wbP and wbE log none in the image), a knowledge edge
   a -> t of the image is a path of the state when the state's entry knows a too (an edge), or
   knows a written-back store standing for a (an edge of the history order, then an edge); per
   cell the same with the stand-for pair in that cell.  NewKr is what is left: the items of the
   image's entry that the state's entry neither knows nor knows through such a store. *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Lit.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB.
Require Import M2DQWBK1 M2DQWBK2 M2DQWBK3 M2DQWBK17 M2DQWBK19 M2DQWBK20 M2DQWBK21 M2DQWBK37 M2DQWBK38 M2DQWBK40 M2DQWBK44 M2DQWBK49 M2DQWBK50.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

Definition Res (s1 sA' : st) (t : nat) (e eW : oev) : Prop :=
  (forall a, eQ e a -> a <> t -> ~ eQ eW a -> ~ (exists w x, eQ eW w /\ seg (hs s1 x) w (Some a)) ->
     ~ ~ Pth s1 a t) /\
  (forall x a, In x (eC e) -> (eQ e a \/ eQc e a) -> In a (ids (hs sA' x)) -> a <> t ->
     ~ ((eQ eW a \/ eQc eW a) /\ In a (ids (hs s1 x))) ->
     ~ (exists w, (eQ eW w \/ eQc eW w) /\ seg (hs s1 x) w (Some a)) ->
     ~ ~ clos_trans nat (cedge s1 x) a t).

Section R.
Variable p : prog.

Definition NewKr : Prop := forall sW sw sA sw' sW' sA' s1,
  wch p False G0 sW sw sA -> wlink p False G0 sw sW sA sw' sW' sA' ->
  run p sA' -> rel sw' sW' sA' -> KR False G0 sw' sW' sA' ->
  UK sw sW sA -> WBCall sW -> UK sw' sW' sA' ->
  KGn sW sA -> KCn sW sA -> evok sA -> evok sW' -> (exists sAf, star p sA' sAf /\ done p sAf) ->
  step p sW s1 -> step p sA sA' -> rel sw s1 sA' -> KR False G0 sw s1 sA' ->
  s1 = sW' ->
  forall e eW, ent sA' (tm sA) = Some e -> ent s1 (tm sA) = Some eW -> Res s1 sA' (tm sA) e eW.

Lemma nn_or : forall (A B : Prop), (A -> B) -> (~ A -> ~ ~ B) -> ~ ~ B.
Proof. intros A B F G N. apply (G (fun a => N (F a))). exact N. Qed.

(* the direct cases: the residue gives the whole obligation at the new entry *)
Lemma new_of_res : forall s1 sA' t e eW sw, ent s1 t = Some eW -> ksame sw s1 t e eW -> Res s1 sA' t e eW ->
  (forall a, eQ e a -> a <> t -> ~ ~ Pth s1 a t) /\
  (forall x a, In x (eC e) -> (eQ e a \/ eQc e a) -> In a (ids (hs sA' x)) -> a <> t ->
     ~ ~ clos_trans nat (cedge s1 x) a t).
Proof.
  intros s1 sA' t e eW sw EW Ks [RG RC]. pose proof Ks as (_ & _ & _ & KC & _).
  split.
  - intros a Q N. apply (nn_or (eQ eW a)); [intros Q'; constructor; right; right; exists eW; auto|intros NQ].
    apply (nn_or (exists w x, eQ eW w /\ seg (hs s1 x) w (Some a))); [|exact (RG a Q N NQ)].
    intros (w & x & Qw & Sg). destruct (Nat.eq_dec w t) as [->|Nw].
    + constructor. left. exists x. exact (seg_old _ _ _ Sg).
    + apply (t_trans _ _ a w t); constructor; [left; exists x; exact (seg_old _ _ _ Sg)|].
      right; right. exists eW. auto.
  - intros x a Ix Q Ia N.
    apply (nn_or ((eQ eW a \/ eQc eW a) /\ In a (ids (hs s1 x)))).
    { intros (Q' & Ia'). constructor. right; right; right; left. exists eW. rewrite <- KC. auto. }
    intros ND. apply (nn_or (exists w, (eQ eW w \/ eQc eW w) /\ seg (hs s1 x) w (Some a))); [|exact (RC x a Ix Q Ia N ND)].
    intros (w & Qw & Sg). destruct (Nat.eq_dec w t) as [->|Nw].
    + constructor. left. exact (seg_old _ _ _ Sg).
    + apply (t_trans _ _ a w t); constructor; [left; exact (seg_old _ _ _ Sg)|].
      right; right; right; left. exists eW. rewrite <- KC. split; [exact EW|]. split; [exact Ix|].
      split; [exact Qw|]. split; [exact (seg_in_l _ _ _ Sg)|exact Nw].
Qed.

Lemma Tl_run : forall s, run p s -> tm s = length (lg s).
Proof. intros s R. exact (i_tm p s (Inv1_run p s R)). Qed.

(* the image logs nothing at a step whose time stays *)
Lemma step_nolog : forall s s', run p s -> step p s s' -> tm s' = tm s -> ent s' (tm s) = None.
Proof.
  intros s s' R H E. pose proof (Tl_run s R) as Tl.
  destruct (sh_lg p s s' H Tl) as [(_ & El)|(E1 & _)]; [|lia].
  unfold ent. rewrite El, Tl. apply nth_error_None. lia.
Qed.

Theorem NewK_of_NewKr : NewKr -> NewK p.
Proof.
  intros NR sW sw sA sw' sW' sA' Ch L RA' R' K' U0 WB U1 G C EVA EV' Fut e Ee.
  pose proof (wch_run p False G0 sW sw sA Ch) as RA. pose proof (wch_rel p False G0 sW sw sA Ch) as Rl.
  pose proof (wch_KR p False G0 sW sw sA Ch) as K.
  pose proof (Tl_run sA RA) as TlA. pose proof (r_tm sw sW sA Rl) as Et.
  pose proof L as L0.
  destruct L as [(St & Fh & StA & ->)
    |[(s1 & c & k & t1 & H'' & St & Ps & Fr & Ok & -> & StA & R1 & K1 & ->)
    |(c & k & t1 & xs & H'' & Lk & Oc & Oh & Ai & Vk & Eo & Fr & Ok & -> & -> & ->)]].
  - destruct (k_ent False G0 sw sW' sA' K' (tm sA) e Ee) as (eW & EW & Ks).
    exact (new_of_res sW' sA' (tm sA) e eW sw EW Ks
             (NR sW sw sA sw sW' sA' sW' Ch L0 RA' R' K' U0 WB U1 G C EVA EV' Fut St StA R' K' eq_refl e eW Ee EW)).
  - exfalso. destruct Ps as (_ & T1 & _).
    rewrite (step_nolog sA sA' RA StA) in Ee; [discriminate|].
    rewrite (r_tm sw s1 sA' R1), T1. symmetry. exact Et.
  - exfalso. unfold ent in Ee. rewrite TlA in Ee. assert (Hn := nth_error_None (lg sA) (length (lg sA))).
    rewrite (proj2 Hn (le_n _)) in Ee. discriminate.
Qed.
End R.

Print Assumptions new_of_res.
Print Assumptions NewK_of_NewKr.
