(* Part 48: WBCall goes along every link of the chain whose images (before and after)
   are evok and have a finished future (WBCall_link): a step of A by WBCall_stepA; a write-back
   by WBCall_wb with (WBC'') from wch_wbc2.  The kept store a new written-back store t stands for
   is below t (it is what the CAS's load took, or what that stands for: the image's read took it,
   M2Inv.i_rw and j_rf), by the uniqueness of stand-for pairs (seg_uniq). *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Lit.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB.
Require Import M2Iface M2IfaceInst M2DQIfaceInst M2DQIfaceUse.
Require Import M2DQWBK1 M2DQWBK2 M2DQWBK3 M2DQWBK4 M2DQWBK13 M2DQWBK15 M2DQWBK19 M2DQWBK20 M2DQWBK30 M2DQWBK37 M2DQWBK38 M2DQWBK40 M2DQWBK44 M2DQWBK46.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

Lemma last_kept : forall X X' a b Y Y', allt X -> allt X' -> X ++ (a, false) :: Y = X' ++ (b, false) :: Y' -> a = b.
Proof.
  induction X as [|e X IH]; intros X' a b Y Y' A1 A2 E; destruct X' as [|e' X']; cbn in E.
  - injection E as -> _. reflexivity.
  - injection E as <- _. inversion A2. discriminate.
  - injection E as -> _. inversion A1. discriminate.
  - injection E as _ E. inversion A1. inversion A2. exact (IH X' a b Y Y' H2 H6 E).
Qed.

Lemma nodup_split : forall X Y (v : nat) b, NoDup (ids (X ++ (v, b) :: Y)) -> ~ In v (ids X) /\ ~ In v (ids Y).
Proof.
  intros X Y v b N. rewrite ids_app in N. cbn in N. apply NoDup_remove_2 in N. rewrite in_app_iff in N. tauto.
Qed.

Lemma seg_uniq : forall h w a o, NoDup (ids h) -> seg h w (Some a) -> seg h w o -> o = Some a.
Proof.
  intros h w a o N (A & B & C & E & Al) S2.
  replace (A ++ (a, false) :: B ++ (w, true) :: C) with ((A ++ (a, false) :: B) ++ (w, true) :: C) in E by (rewrite <- app_assoc; reflexivity).
  destruct o as [b|].
  - destruct S2 as (A' & B' & C' & E' & Al').
    replace (A' ++ (b, false) :: B' ++ (w, true) :: C') with ((A' ++ (b, false) :: B') ++ (w, true) :: C') in E' by (rewrite <- app_assoc; reflexivity).
    rewrite E in N. destruct (nodup_split _ _ _ _ N) as [N1 N2].
    destruct (uniq_place _ _ _ _ w true true N1 N2 (eq_trans (eq_sym E') E)) as [EX _].
    f_equal. apply (last_kept (rev B') (rev B) b a (rev A') (rev A)).
    + unfold allt. apply Forall_rev. exact Al'.
    + unfold allt. apply Forall_rev. exact Al.
    + apply (f_equal (@rev _)) in EX. rewrite !rev_app_distr in EX. cbn in EX. rewrite <- !app_assoc in EX. cbn in EX.
      exact EX.
  - exfalso. destruct S2 as (h1 & h2 & E' & Al').
    rewrite E in N. destruct (nodup_split _ _ _ _ N) as [N1 N2].
    destruct (uniq_place _ _ _ _ w true true N1 N2 (eq_trans (eq_sym E') E)) as [EX _].
    rewrite EX in Al'. apply allt_app in Al'. destruct Al' as [_ Al']. inversion Al'. discriminate.
Qed.

(* the stood-for store of a written-back store with the id of a read half is below it *)
Lemma half_lt : forall p Fk Good sw s sA c k t1 H'' x z, run p sA -> rel sw s sA -> KR Fk Good sw s sA ->
  oh (cs s c) k = Some t1 -> oc (cs s c) k = None -> (forall x, ~ In t1 (ids (hs s x))) -> wbok s c k t1 H'' ->
  seg (H'' x) t1 (Some z) -> z < t1.
Proof.
  intros p Fk Good sw s sA c k t1 H'' x z RA Rl K Oh Oc Fr Ok Sg.
  destruct (enters_tied_cell _ _ _ _ _ x Ok) as [E|(h1 & h2 & E1 & E2 & _ & Mt)];
    [rewrite E in Sg; exfalso; exact (Fr x (seg_in_l _ _ _ Sg))|].
  rewrite E2 in Sg.
  assert (N1 : ~ In t1 (ids h1)) by (intros I; apply (Fr x); rewrite E1, ids_app; apply in_or_app; left; exact I).
  assert (N2 : ~ In t1 (ids h2)) by (intros I; apply (Fr x); rewrite E1, ids_app; apply in_or_app; right; exact I).
  destruct (seg_at_new h1 h2 t1 z (rw (cs s c) k x) Mt N1 N2 Sg) as (w1 & Rw & Cz). rewrite <- E1 in Cz.
  assert (Pz : pi sw x (Some w1) = Some z).
  { destruct Cz as [(Iw & ->)|Sg1].
    - unfold pi. rewrite (proj1 (r_kept sw s sA Rl x w1 Iw)). reflexivity.
    - assert (Iw : In (w1, true) (hs s x)).
      { destruct Sg1 as (h0 & h3 & h4 & E & _). rewrite E. apply in_or_app. right. right. apply in_or_app. right. left. reflexivity. }
      destruct (w_bet Fk Good sw s sA K x w1 Iw) as (f & Sf & Sg2). unfold pi. rewrite Sf.
      exact (seg_uniq _ _ _ _ (w_nodup Fk Good sw s sA K x) Sg1 Sg2). }
  destruct (r_cr sw s sA Rl c) as (_ & _ & Hrw). specialize (Hrw k x). rewrite Rw, Pz in Hrw.
  destruct (crel_eq p Fk Good sw s sA RA Rl K c) as (OcE & OhE & _).
  destruct (M2Inv.i_rw p sA (Inv1_run p sA RA) c k t1) as (e & Ee & Erw); [right; rewrite OcE, OhE; auto|].
  rewrite Erw in Hrw. destruct (M2Inv.i_oh p sA (Inv1_run p sA RA) c k t1) as (e' & Ee' & _ & _ & Eh); [rewrite OhE; exact Oh|].
  rewrite Ee in Ee'. injection Ee' as <-.
  destruct (j_ew p sA (proj2 (Inv2_run p sA RA)) t1 e _ Ee eq_refl) as [J _]. rewrite Eh in J. cbn in J.
  unfold wrote in Hrw. rewrite J in Hrw.
  exact (proj1 (j_rf p sA (proj2 (Inv2_run p sA RA)) t1 e x z Ee Hrw)).
Qed.

Lemma kept_back : forall s c k t H'' x z, wbok s c k t H'' -> seg (H'' x) t (Some z) -> In (z, false) (hs s x).
Proof.
  intros s c k t H'' x z Ok Sg. pose proof (stands_kept _ _ _ Sg) as Kz.
  destruct (enters_tied_cell _ _ _ _ _ x Ok) as [E|(h1 & h2 & E1 & E2 & _)]; [rewrite <- E; exact Kz|].
  rewrite E2 in Kz. rewrite E1. apply in_app_iff in Kz. apply in_app_iff.
  destruct Kz as [K1|[K1|K1]]; [left; exact K1|discriminate|right; exact K1].
Qed.

Section Link.
Variables (p : prog) (W : wf p) (Fk : Prop) (Good : nat -> Prop).

Theorem WBCall_link : forall sW sw sA sw' sW' sA', cellful p -> race_free_g p ->
  wch p Fk Good sW sw sA -> wlink p Fk Good sw sW sA sw' sW' sA' ->
  run p sA' -> rel sw' sW' sA' -> KR Fk Good sw' sW' sA' ->
  evok sA -> evok sA' -> (exists sAf, star p sA' sAf /\ done p sAf) ->
  WBCall sW -> WBCall sW'.
Proof.
  intros sW sw sA sw' sW' sA' Wc RF Ch L RA' Rl' K' EV EV' Fut WB.
  destruct (wch_inv p Fk Good sW sw sA Ch) as (RA & Rl & K & RW).
  pose proof (tmW p Fk Good sw sW sA RA Rl K) as Tl. pose proof (runWB_KM p sW RW) as Km.
  pose proof (i_ids sw sW sA Rl) as Ii.
  destruct (wch_wbc2 p W Fk Good sW sw sA sw' sW' sA' Wc RF Ch L RA' Rl' K' EV EV' Fut)
    as [(St & FH & _)|(s' & c & k & t & H'' & E & D & Hw)].
  - exact (WBCall_stepA p sW sW' St FH Tl Km Ii WB).
  - subst sW'. destruct D as [(St & Ps & Fr & Ok & Rl0 & K0)|(Es & EsA & Lk & Oh & Oc & Fr & Ok)].
    + pose proof Ps as (NW & _ & _ & _ & Oc0 & _ & Oh1 & _).
      assert (Fr' : forall x, ~ In t (ids (hs s' x))) by (intros x; rewrite (NW x); exact (Fr x)).
      assert (Oc1 : oc (cs s' c) k = None).
      { rewrite (partskip_form p sW s' c k t St Ps). unfold sskip. cbn [cs]. rewrite upd_eq. cbn [oc]. exact Oc0. }
      apply (WBCall_wb s' c k t H'' Fr' Ok).
      * exact (WBCall_stepA p sW s' St (nowrite_fhsafe _ _ NW) Tl Km Ii WB).
      * exact Hw.
      * intros x u Iu. exact (kept_ent p Fk Good sw s' sA' x u RA' Rl0 K0 Iu).
      * intros x z Sg. exact (half_lt p Fk Good sw s' sA' c k t H'' x z RA' Rl0 K0 Oh1 Oc1 Fr' Ok Sg).
    + subst s'. apply (WBCall_wb sW c k t H'' Fr Ok WB Hw).
      * intros x u Iu. exact (kept_ent p Fk Good sw sW sA x u RA Rl K Iu).
      * intros x z Sg. exact (half_lt p Fk Good sw sW sA c k t H'' x z RA Rl K Oh Oc Fr Ok Sg).
Qed.
End Link.

Print Assumptions seg_uniq.
Print Assumptions half_lt.
Print Assumptions WBCall_link.
