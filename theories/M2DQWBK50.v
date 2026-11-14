(* Part 50: LinkK (M2DQWBK49) reduced to the new entry of a link.
   run_kq_lt (any A-run): what an entry knows in order (eQ, eQc) is a write made no later than
   the entry.  So at a link the old entries of the image keep their knowledge edges (paths only
   grow along stepWB), and only the entry the link's step of A adds needs an argument (NewK). *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Lit.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB.
Require Import M2DQWBK1 M2DQWBK2 M2DQWBK3 M2DQWBK17 M2DQWBK19 M2DQWBK20 M2DQWBK21 M2DQWBK37 M2DQWBK40 M2DQWBK49.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBQb M2DQWBK1Q M2DQShim.

(* the in-order knowledge of an entry is written no later than the entry *)
Lemma run_kq_lt : forall p s, run p s -> forall t e a, ent s t = Some e -> (eQ e a \/ eQc e a) -> a <= t.
Proof.
  intros p s R. induction R as [|s s' R IH H]; intros t e a E Q.
  - unfold ent in E. destruct t; discriminate.
  - destruct (InvO_run p s R) as [I J L O].
    destruct (InvO_run p s' (rS p s s' R H)) as [I' J' L' O'].
    assert (Old : forall t e, ent s t = Some e -> forall a, (eQ e a \/ eQc e a) -> a <= t) by (intros; eapply IH; eauto).
    assert (Vb : forall c a, vO (cs s c) a -> a < tm s).
    { intros c0 a0 Oa. destruct (o_sub_PG p s O c0 a0 Oa) as [Pa|Ga];
        apply (isw_lt p s a0 I); apply (j_views p s J c0); tauto. }
    destruct Q as [Q|Q].
    + destruct (o_QP_G p s' O' t e E a Q) as [[Pa|Sa]|(La & _)]; [| |lia].
      * destruct (j_eP p s' J' t e a E Pa) as [_ La]. lia.
      * destruct (i_et p s' I' t e E) as (Et & _). unfold esrc, srcv in Sa.
        destruct Sa as [(x & Ex)|Ea].
        -- destruct (j_rf p s' J' t e x a E Ex) as (La & _). lia.
        -- destruct (ew e); [unfold vone in Ea; lia|contradiction].
    + destruct (stepQ_split p s s' H) as [[HA _]|RF]; [|unfold ent in E; rewrite (rfx_lg _ _ RF) in E; exact (Old t e E a (or_intror Q))].
  destruct (step_cases p s s' HA) as
        [(c & i & m' & a0 & K & u & w & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ->)
        |[(c & k & d & B & m' & a0 & K & u & w & _ & _ & _ & _ & _ & _ & _ & _ & ->)
        |[(c & d & _ & _ & _ & _ & _ & _ & ->)
        |[(c & k & xs & B & m' & a0 & K & u & w & bv & _ & _ & _ & _ & _ & _ & _ & ->)
        |[(c & _ & _ & _ & _ & _ & _ & _ & ->)
        |(cX & jX & bX & BX & oX & _ & _ & _ & ->)]]]]].
      3, 5: exact (Old t e E a (or_intror Q)).
      4: unfold ent, scfix0 in E; cbn [lg] in E; rewrite lg_flp in E; exact (Old t e E a (or_intror Q)).
      all: unfold sord, searly, set_es, searly0, evs, sread, ent in E; cbn [lg] in E;
           destruct (ent_app _ _ _ _ E) as [(E0 & _)|(Et & ->)]; [exact (Old t e E0 a (or_intror Q))|];
           cbn [eQc] in Q; unfold evQc in Q;
           destruct (_ && _) in Q; [|contradiction];
           rewrite Et, <- (i_tm p s I); pose proof (Vb c a Q); lia.
Qed.

Section Red.
Variable p : prog.

(* the obligation at the entry a link's step of A adds *)
Definition NewK : Prop := forall sW sw sA sw' sW' sA',
  wch p False G0 sW sw sA -> wlink p False G0 sw sW sA sw' sW' sA' ->
  run p sA' -> rel sw' sW' sA' -> KR False G0 sw' sW' sA' ->
  UK sw sW sA -> WBCall sW -> UK sw' sW' sA' ->
  KGn sW sA -> KCn sW sA -> evok sA -> evok sW' -> (exists sAf, star p sA' sAf /\ done p sAf) ->
  forall e, ent sA' (tm sA) = Some e ->
    (forall a, eQ e a -> a <> tm sA -> ~ ~ Pth sW' a (tm sA)) /\
    (forall x a, In x (eC e) -> (eQ e a \/ eQc e a) -> In a (ids (hs sA' x)) -> a <> tm sA ->
       ~ ~ clos_trans nat (cedge sW' x) a (tm sA)).

Lemma wlink_A : forall sw sW sA sw' sW' sA', wlink p False G0 sw sW sA sw' sW' sA' -> sA' = sA \/ step p sA sA'.
Proof.
  intros sw sW sA sw' sW' sA'
    [(_ & _ & St & _)|[(s' & c & k & t1 & H'' & _ & _ & _ & _ & _ & St & _)
    |(c & k & t1 & xs & H'' & _ & _ & _ & _ & _ & _ & _ & _ & _ & -> & _)]]; auto.
Qed.

Lemma nn_map : forall (A B : Prop), (A -> B) -> ~ ~ A -> ~ ~ B.
Proof. intros A B F N NB. apply N. intros X. exact (NB (F X)). Qed.

Theorem LinkK_of_NewK : NewK -> LinkK p.
Proof.
  intros NK sW sw sA sw' sW' sA' Ch L RA' R' K' U0 WB U1 G C EVA EV' Fut.
  pose proof (wch_run p False G0 sW sw sA Ch) as RA.
  pose proof (i_tm p sA (Inv1_run p sA RA)) as Tl.
  pose proof (wlink_stepWB p False G0 sw sW sA sw' sW' sA' L) as SW.
  pose proof (NK sW sw sA sw' sW' sA' Ch L RA' R' K' U0 WB U1 G C EVA EV' Fut) as NKe.
  assert (LiftG : forall a b, ~ ~ Pth sW a b -> ~ ~ Pth sW' a b)
    by (intros a b; apply nn_map; exact (stepWB_pth p sW sW' SW a b)).
  assert (LiftC : forall x a b, ~ ~ clos_trans nat (cedge sW x) a b -> ~ ~ clos_trans nat (cedge sW' x) a b)
    by (intros x a b; apply nn_map; exact (ct_mono _ _ (stepWB_cedge p sW sW' SW x) a b)).
  (* an entry of the new image is an old one or the new one *)
  assert (Ent : forall b e, ent sA' b = Some e -> (b < tm sA /\ ent sA b = Some e /\ forall x a, In a (ids (hs sA' x)) -> In a (ids (hs sA x)) \/ a = tm sA) \/ b = tm sA).
  { intros b e E. destruct (wlink_A sw sW sA sw' sW' sA' L) as [->|St].
    - left. split; [|split; [exact E|intros x a Ia; left; exact Ia]].
      rewrite Tl. apply nth_error_Some. unfold ent in E. congruence.
    - pose proof (sh_ent_lt p sA sA' St Tl b e E) as Lb.
      destruct (Nat.eq_dec b (tm sA)) as [Eb|Nb]; [right; exact Eb|left].
      split; [lia|]. split; [rewrite <- (sh_old p sA sA' St Tl b ltac:(lia)); exact E|].
      intros x a Ia. apply in_map_iff in Ia. destruct Ia as ([a' f] & Ea & Ia). cbn in Ea. subst a'.
      pose proof (runQ_flagsF p sA' RA' x a f Ia) as Ff. subst f.
      destruct (sh_hs p sA sA' St Tl x a Ia) as [I0|E0]; [left|right; exact E0].
      apply in_map_iff. exists (a, false). auto. }
  split.
  - intros a b e Eb Q Nab. destruct (Ent b e Eb) as [(Lb & Eb0 & _)| ->].
    + exact (LiftG a b (G a b e Eb0 Q Nab)).
    + exact (proj1 (NKe e Eb) a Q Nab).
  - intros x a b e Eb Ix Q Ia Nab. destruct (Ent b e Eb) as [(Lb & Eb0 & Hs)| ->].
    + destruct (Hs x a Ia) as [Ia0|Ea].
      * exact (LiftC x a b (C x a b e Eb0 Ix Q Ia0 Nab)).
      * exfalso. pose proof (run_kq_lt p sA' RA' b e a Eb Q). lia.
    + exact (proj2 (NKe e Eb) x a Ix Q Ia Nab).
Qed.
End Red.

Print Assumptions run_kq_lt.
Print Assumptions LinkK_of_NewK.
