(* Part 37: the images of a runWB as one chain.
   runWBK (M2DQWBK13) gives an image of the last state only.  Here every step of the run gets its
   image, linked to the image of the step before: a step of A or a write-back by a CAS failing
   in parts when its context passes it goes with one step of A (the image of the state before the write-back patch
   is kept in the link, with rel and KR), an early store part (wbE) with no step of A.
   wch s sw sA: sA is the image of s at the end of such a chain.  From it: the image of every
   earlier state reaches the image of the last (wlink_star), so a finished last state gives every
   image a finished future; evok goes back along the run (M2DQWBK19).
   wch_wbc: (WBC'') at the step of every write-back of the chain, from evok of the image before
   and of the image after the step (the base interleaving of the image before comes from
   drf_prefix): wbP (M2DQWBK33), wbE (M2DQWBK36). *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Lit.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB.
Require Import M2Iface M2IfaceInst M2DQIfaceInst M2DQIfaceUse.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB.
Require Import M2DQWBK1 M2DQWBK2 M2DQWBK3 M2DQWBK4 M2DQWBK7 M2DQWBK9 M2DQWBK10 M2DQWBK11 M2DQWBK12 M2DQWBK13 M2DQWBK19 M2DQWBFsc.
Require Import M2DQWBK21 M2DQWBK22 M2DQWBK33 M2DQWBK36.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

Section Ch.
Variables (p : prog) (W : wf p) (Fk : Prop) (Good : nat -> Prop).

(* one step of the run and its image: the three kinds of stepWB *)
Definition wlink (sw : nat -> option (cell -> option nat)) (sW sA : st)
                 (sw' : nat -> option (cell -> option nat)) (sW' sA' : st) : Prop :=
  (step p sW sW' /\ fhsafe sW sW' /\ step p sA sA' /\ sw' = sw)
  \/ (exists s' c k t1 H'', step p sW s' /\ partskip sW s' c k t1 /\ (forall x, ~ In t1 (ids (hs sW x))) /\
        wbok s' c k t1 H'' /\ sW' = wbst s' c k t1 H'' /\ step p sA sA' /\ rel sw s' sA' /\
        KR Fk Good sw s' sA' /\ sw' = upd sw t1 (Some (fun x => pi sw x (rw (cs s' c) k x))))
  \/ (exists c k t1 xs H'', pcs sW c < k /\ oc (cs sW c) k = None /\ oh (cs sW c) k = Some t1 /\
        ai (cs sW c) k = crd Plain xs /\ vok (rg (cs sW c) k) = false /\
        early_okWB p c (cs sW c) (pcs sW c) (tp sW c) (tm sW) t1 xs /\
        (forall x, ~ In t1 (ids (hs sW x))) /\ wbok sW c k t1 H'' /\ sW' = wbst sW c k t1 H'' /\
        sA' = sA /\ sw' = upd sw t1 (Some (fun x => pi sw x (rw (cs sW c) k x)))).

Lemma wlink_stepWB : forall sw sW sA sw' sW' sA', wlink sw sW sA sw' sW' sA' -> stepWB p sW sW'.
Proof.
  intros sw sW sA sw' sW' sA'
    [(St & Fh & _)|[(s' & c & k & t1 & H'' & St & Ps & Fr & Ok & -> & _)
    |(c & k & t1 & xs & H'' & Lk & Oc & Oh & Ai & Vk & Eo & Fr & Ok & -> & _)]].
  - exact (wbA p sW sW' St Fh).
  - exact (wbP p sW s' c k t1 H'' St Ps Fr Ok).
  - exact (wbE p sW c k t1 xs H'' Lk Oc Oh Ai Vk Eo Fr Ok).
Qed.

(* the image of the earlier state reaches the image of the later one *)
Lemma wlink_starA : forall sw sW sA sw' sW' sA', wlink sw sW sA sw' sW' sA' -> star p sA sA'.
Proof.
  intros sw sW sA sw' sW' sA'
    [(_ & _ & St & _)|[(s' & c & k & t1 & H'' & _ & _ & _ & _ & _ & St & _)
    |(c & k & t1 & xs & H'' & _ & _ & _ & _ & _ & _ & _ & _ & _ & -> & _)]].
  1-2: exact (stS p sA sA' sA' St (st0 p sA')).
  constructor.
Qed.

Lemma star_trans : forall a b c, star p a b -> star p b c -> star p a c.
Proof. intros a b c H. induction H as [|s s1 t St _ IH]; intros H2; [exact H2|exact (stS p s s1 c St (IH H2))]. Qed.

Lemma wlink_star : forall sw sW sA sw' sW' sA' sAf, wlink sw sW sA sw' sW' sA' -> star p sA' sAf -> star p sA sAf.
Proof. intros sw sW sA sw' sW' sA' sAf L S. exact (star_trans sA sA' sAf (wlink_starA sw sW sA sw' sW' sA' L) S). Qed.

(* ---------- the chain ---------- *)
Inductive wch : st -> (nat -> option (cell -> option nat)) -> st -> Prop :=
| wch0 : wch sinit sw0 sinit
| wchS : forall sW sw sA sW' sw' sA', wch sW sw sA -> wlink sw sW sA sw' sW' sA' ->
    run p sA' -> rel sw' sW' sA' -> KR Fk Good sw' sW' sA' -> wch sW' sw' sA'.

Lemma wch_inv : forall sW sw sA, wch sW sw sA -> run p sA /\ rel sw sW sA /\ KR Fk Good sw sW sA /\ runWB p sW.
Proof.
  intros sW sw sA H. induction H as [|sW sw sA sW' sw' sA' _ IH L RA R K].
  - split; [constructor|split; [exact rel_init|split; [exact (KR_init Fk Good)|constructor]]].
  - split; [exact RA|split; [exact R|split; [exact K|]]].
    exact (wrS p sW sW' (proj2 (proj2 (proj2 IH))) (wlink_stepWB sw sW sA sw' sW' sA' L)).
Qed.

Lemma wch_run : forall sW sw sA, wch sW sw sA -> run p sA.
Proof. intros sW sw sA H. exact (proj1 (wch_inv sW sw sA H)). Qed.
Lemma wch_rel : forall sW sw sA, wch sW sw sA -> rel sw sW sA.
Proof. intros sW sw sA H. exact (proj1 (proj2 (wch_inv sW sw sA H))). Qed.
Lemma wch_KR : forall sW sw sA, wch sW sw sA -> KR Fk Good sw sW sA.
Proof. intros sW sw sA H. exact (proj1 (proj2 (proj2 (wch_inv sW sw sA H)))). Qed.
Lemma wch_runWB : forall sW sw sA, wch sW sw sA -> runWB p sW.
Proof. intros sW sw sA H. exact (proj2 (proj2 (proj2 (wch_inv sW sw sA H)))). Qed.

(* a finished state: its image is finished *)
Lemma wch_done : forall sW sw sA, wch sW sw sA -> done p sW -> exists sAf, star p sA sAf /\ done p sAf.
Proof. intros sW sw sA H D. exists sA. split; [constructor|exact (rel_done p sw sW sA (wch_rel sW sw sA H) D)]. Qed.

(* the accumulator of an induction on the chain goes back one link: a finished future of the
   later image is one of the earlier image, and evok of the later state gives evok of the earlier *)
Lemma wlink_back : forall sw sW sA sw' sW' sA', wlink sw sW sA sw' sW' sA' ->
  (exists sAf, star p sA' sAf /\ done p sAf) -> evok sW' ->
  (exists sAf, star p sA sAf /\ done p sAf) /\ evok sW.
Proof.
  intros sw sW sA sw' sW' sA' L (sAf & S & D) EV. split.
  - exists sAf. split; [exact (wlink_star sw sW sA sw' sW' sA' sAf L S)|exact D].
  - exact (stepWB_evok_back p sW sW' (wlink_stepWB sw sW sA sw' sW' sA' L) EV).
Qed.

(* ---------- every runWB has a chain (simWBK_step, keeping the link) ---------- *)
Theorem simWBK_link : forall sw sW sA sW', run p sA -> rel sw sW sA -> KR Fk Good sw sW sA -> stepWB p sW sW' ->
  (Fk -> HB1 Good sW') -> (Fk -> HB2 Good sW') ->
  exists sw' sA', run p sA' /\ rel sw' sW' sA' /\ KR Fk Good sw' sW' sA' /\ wlink sw sW sA sw' sW' sA'.
Proof.
  intros sw sW sA sW' RA R K H H1 H2. pose proof (tmW p Fk Good sw sW sA RA R K) as TL.
  inversion H as [s0 s1 St FHs | s0 s1 c k t1 H'' St Ps Fr Ok | s0 c k t1 xs H'' Lk Oc Oh Ai Vk Eo Fr Ok]; subst.
  - destruct (sim_stepK p W sw sW sA RA R Fk Good K sW' St FHs H1 H2) as (sA' & St' & R' & K').
    exists sw, sA'. split; [econstructor; eauto|]. split; [exact R'|]. split; [exact K'|].
    left. auto.
  - assert (C1 : Fk -> HB1 Good s1) by (intros HF; exact (proj1 (wb_HB_back Good s1 c k t1 H'' (H1 HF) (H2 HF)))).
    assert (C2 : Fk -> HB2 Good s1) by (intros HF; exact (proj2 (wb_HB_back Good s1 c k t1 H'' (H1 HF) (H2 HF)))).
    pose proof (partskip_form p sW s1 c k t1 St Ps) as Es1.
    pose proof Ps as Ps0. destruct Ps as (NW & T1 & Pk & Pk' & Oc0 & Oh0 & Oh1 & Cc & Vk).
    destruct (sim_stepK p W sw sW sA RA R Fk Good K s1 St (nowrite_fhsafe _ _ NW) C1 C2) as (sA' & St' & R' & K').
    assert (RA' : run p sA') by (econstructor; eauto).
    assert (Fr' : forall x, ~ In t1 (ids (hs s1 x))) by (intros x; rewrite (NW x); exact (Fr x)).
    assert (Oc1 : oc (cs s1 c) k = None) by (rewrite Es1; unfold sskip; cbn [cs]; rewrite upd_eq; cbn [oc]; exact Oc0).
    exists (upd sw t1 (Some (fun x => pi sw x (rw (cs s1 c) k x)))), sA'.
    split; [exact RA'|]. split; [|split].
    + apply (rel_wb sw s1 sA' c k t1 H'' R'); [exact (i_oh sw s1 sA' R' c k t1 Oh1)|exact Fr'|exact Ok].
    + apply (KR_wb p Fk Good sw s1 sA' c k t1 H'' RA' R' K'); [exact (i_oh sw s1 sA' R' c k t1 Oh1)|exact Fr'|exact Ok| | | | | | ].
      * destruct (i_ohW p Fk Good sw s1 sA' RA' R' K' c k t1 Oh1) as (e & E & Ec & Ek & _). eauto.
      * exact Cc.
      * unfold tmo. rewrite Oc1. exact Oh1.
      * intros c' j Oh'. destruct (i_ohW p Fk Good sw s1 sA' RA' R' K' c' j t1 Oh') as (e & E & Ec & Ek & _).
        destruct (i_ohW p Fk Good sw s1 sA' RA' R' K' c k t1 Oh1) as (e' & E' & Ec' & Ek' & _).
        rewrite E in E'. injection E' as <-. split; [congruence|split; [congruence|split; [exact Oc1|left; lia]]].
      * intros tf g Eg (Fa & Fp & Fo) Ec. rewrite Ec in Fa, Fp, Fo. rewrite Pk' in Fp.
        assert (Nk : ek g <> k) by (intros Z; rewrite Z in Fa; rewrite Fa in Cc; discriminate).
        rewrite Es1 in Fa, Fo. unfold sskip in Fa, Fo. cbn [cs] in Fa, Fo. rewrite upd_eq in Fa, Fo. cbn [ai oc] in Fa, Fo.
        rewrite Pk in Fa. rewrite upd_neq in Fa by exact Nk.
        destruct (crel_eq p Fk Good sw sW sA RA R K c) as (Oca & Oha & Aia & _).
        apply (ff_before_half p sA c k t1 (ek g) tf RA).
        -- rewrite Oha. exact Oh0.
        -- rewrite Oca. exact Oc0.
        -- rewrite (r_pcs sw sW sA R). lia.
        -- rewrite (r_pcs sw sW sA R). lia.
        -- rewrite Aia. exact Fa.
        -- rewrite Oca. exact Fo.
      * intros eA EA. destruct (M2Inv.i_oh p sA' (Inv1_run p sA' RA') c k t1) as (e & E & _ & _ & Eh).
        { destruct (crel_eq p Fk Good sw s1 sA' RA' R' K' c) as (_ & Oha & _). rewrite Oha. exact Oh1. }
        rewrite EA in E. injection E as <-.
        destruct (j_ew p sA' (proj2 (Inv2_run p sA' RA')) t1 eA _ EA eq_refl) as [J _]. rewrite J, Eh. reflexivity.
    + right; left. exists s1, c, k, t1, H''. auto 12.
  - exists (upd sw t1 (Some (fun x => pi sw x (rw (cs sW c) k x)))), sA.
    split; [exact RA|]. split; [|split].
    + apply (rel_wb sw sW sA c k t1 H'' R); [exact (i_oh sw sW sA R c k t1 Oh)|exact Fr|exact Ok].
    + apply (KR_wb p Fk Good sw sW sA c k t1 H'' RA R K); [exact (i_oh sw sW sA R c k t1 Oh)|exact Fr|exact Ok| | | | | | ].
      * destruct (i_ohW p Fk Good sw sW sA RA R K c k t1 Oh) as (e & E & Ec & Ek & _). eauto.
      * rewrite Ai. reflexivity.
      * unfold tmo. rewrite Oc. exact Oh.
      * intros c' j Oh'. destruct (i_ohW p Fk Good sw sW sA RA R K c' j t1 Oh') as (e & E & Ec & Ek & _).
        destruct (i_ohW p Fk Good sw sW sA RA R K c k t1 Oh) as (e' & E' & Ec' & Ek' & _).
        rewrite E in E'. injection E' as <-. split; [congruence|split; [congruence|split; [exact Oc|right; exact Vk]]].
      * intros tf g Eg (Fa & Fp & Fo) Ec. rewrite Ec in Fa, Fp, Fo.
        destruct (crel_eq p Fk Good sw sW sA RA R K c) as (Oca & Oha & Aia & _).
        apply (ff_before_half p sA c k t1 (ek g) tf RA).
        -- rewrite Oha. exact Oh.
        -- rewrite Oca. exact Oc.
        -- rewrite (r_pcs sw sW sA R). lia.
        -- rewrite (r_pcs sw sW sA R). exact Fp.
        -- rewrite Aia. exact Fa.
        -- rewrite Oca. exact Fo.
      * intros eA EA. destruct (M2Inv.i_oh p sA (Inv1_run p sA RA) c k t1) as (e & E & _ & _ & Eh).
        { destruct (crel_eq p Fk Good sw sW sA RA R K c) as (_ & Oha & _). rewrite Oha. exact Oh. }
        rewrite EA in E. injection E as <-.
        destruct (j_ew p sA (proj2 (Inv2_run p sA RA)) t1 eA _ EA eq_refl) as [J _]. rewrite J, Eh. reflexivity.
    + right; right. exists c, k, t1, xs, H''. auto 15.
Qed.

Theorem runWBK_chain : forall s, runWB p s -> (Fk -> HB1 Good s) -> (Fk -> HB2 Good s) ->
  exists sw sA, wch s sw sA.
Proof.
  intros s R. induction R as [|s s' R IH St]; intros H1 H2.
  - exists sw0, sinit. constructor.
  - destruct (stepWB_HB_back p Fk Good s s' R St H1 H2) as [B1 B2].
    destruct (IH B1 B2) as (sw & sA & Ch).
    destruct (wch_inv s sw sA Ch) as (RA & Rl & K & _).
    destruct (simWBK_link sw s sA s' RA Rl K St H1 H2) as (sw' & sA' & RA' & Rl' & K' & L).
    exists sw', sA'. exact (wchS s sw sA s' sw' sA' Ch L RA' Rl' K').
Qed.
End Ch.

Print Assumptions wlink_back.
Print Assumptions simWBK_link.
Print Assumptions runWBK_chain.

(* ---------- (WBC'') at each write-back of the chain ---------- *)
(* a store older than the step, other than the write-back, is a store of the state before, in the same place *)
Lemma wb_old : forall p s s' c k t H'' u eu x, WK s -> step p s s' -> nowrite s s' -> wbok s' c k t H'' ->
  u < tm s -> u <> t -> ent (wbst s' c k t H'') u = Some eu -> In (u, false) (hs (wbst s' c k t H'') x) ->
  ent s u = Some eu /\ In (u, false) (hs s x).
Proof.
  intros p s s' c k t H'' u eu x Wk St NW Ok Lu Nu E I. split.
  - unfold ent in E. cbn [wbst lg] in E. rewrite nth_setew in E.
    change (nth_error (lg s') u) with (ent s' u) in E. rewrite (sh_old p s s' St (wk_tm s Wk) u Lu) in E.
    destruct (ent s u) as [o|] eqn:E0; cbn in E; [|discriminate]. injection E as <-.
    unfold sete. rewrite (wk_et s Wk u o E0). destruct (Nat.eqb_spec u t); [congruence|reflexivity].
  - cbn [wbst hs] in I. rewrite <- (NW x). destruct (enters_tied_cell _ _ _ _ _ x Ok) as [E1|(h1 & h2 & E1 & E2 & _)].
    + rewrite E1 in I. exact I.
    + rewrite E2 in I. rewrite E1. apply in_app_iff in I. apply in_app_iff.
      destruct I as [I|[I|I]]; [left; exact I|congruence|right; exact I].
Qed.

Section Wbc.
Variables (p : prog) (W : wf p) (Fk : Prop) (Good : nat -> Prop).

(* (WBC'') of the write-back with id t by the CAS at slot k of context c: every kept store u
   placed before it in a cell of the CAS conveys only itself, what the write-back conveys, and
   what guard() has published *)
Definition WBC (s : st) (c k t : nat) : Prop :=
  forall x, In x (icells (ai (cs s c) k)) -> forall u eu, ent s u = Some eu -> ew eu = true ->
    In (u, false) (hs s x) -> u < t -> forall z, wc s u z -> z = u \/ wc s t z \/ vG s z.

Theorem wch_wbc : forall sW sw sA sw' sW' sA', cellful p -> race_free_g p ->
  wch p Fk Good sW sw sA -> wlink p Fk Good sw sW sA sw' sW' sA' ->
  run p sA' -> rel sw' sW' sA' -> KR Fk Good sw' sW' sA' ->
  evok sA -> evok sA' -> (exists sAf, star p sA' sAf /\ done p sAf) ->
  (step p sW sW' /\ fhsafe sW sW' /\ step p sA sA' /\ sw' = sw) \/
  exists s' c k t H'', sW' = wbst s' c k t H'' /\ WBC sW' c k t.
Proof.
  intros sW sw sA sw' sW' sA' Wc RF Ch L RA' Rl' K' EV EV' Fut.
  destruct (wch_inv p Fk Good sW sw sA Ch) as (RA & Rl & K & RW).
  pose proof (wrS p sW sW' RW (wlink_stepWB p Fk Good sw sW sA sw' sW' sA' L)) as RW'.
  pose proof (WK_run p W sW RW) as Wk.
  assert (FutA : exists sAf, star p sA sAf /\ done p sAf).
  { destruct Fut as (sAf & S & D). exists sAf. split; [exact (wlink_star p Fk Good sw sW sA sw' sW' sA' sAf L S)|exact D]. }
  destruct L as [LA|[(s' & c & k & t1 & H'' & St & Ps & Fr & Ok & E & StA & _)
    |(c & k & t1 & xs & H'' & Lk & Oc & Oh & Ai & Vk & Eo & Fr & Ok & E & EA & _)]].
  - left. exact LA.
  - right. exists s', c, k, t1, H''. split; [exact E|]. subst sW'.
    intros x Ix u eu Eu Ewu Iu Lu z Z.
    assert (Ix' : In x (icells (ai (cs s' c) k))) by (cbn [wbst cs] in Ix; rewrite upd_eq in Ix; exact Ix).
    pose proof Ps as (NW & _ & _ & _ & _ & Oh0 & _).
    pose proof (i_oh sw sW sA Rl c k t1 Oh0) as Lt.
    destruct (wb_old p sW s' c k t1 H'' u eu x Wk St NW Ok ltac:(lia) ltac:(lia) Eu Iu) as [Eu0 Iu0].
    destruct (drf_prefix_dq p sA W Wc RF RA EV) as (l & g & B).
    exact (wbc_full_wbP p Fk Good sw sW sA l g s' c k t1 H'' x u eu W Wc RF RA EV Rl K RW B FutA St Ps Fr Ix' Eu0 Ewu Iu0 z Z).
  - right. exists sW, c, k, t1, H''. split; [exact E|]. subst sW' sA'.
    intros x Ix u eu Eu Ewu Iu Lu z Z.
    destruct (crel_eq p Fk Good sw sW sA RA Rl K c) as (_ & OhE & AiE & _).
    apply (wbc_wbE p Fk Good sw' (wbst sW c k t1 H'') sA c k t1 xs x u eu W Wc RF RA Rl' K' RW' EV Fut).
    + rewrite OhE. exact Oh.
    + rewrite (r_pcs sw sW sA Rl). exact Lk.
    + rewrite AiE, Ai. reflexivity.
    + cbn [wbst cs] in Ix. rewrite upd_eq in Ix. cbn [ai] in Ix. rewrite Ai in Ix. cbn [icells crd] in Ix.
      exact (proj1 (dd_in x xs) Ix).
    + intros z0 Z0. cbn [wbst cs wc] in Z0 |- *. rewrite upd_eq in Z0. cbn [vR] in Z0. rewrite upd_eq. left. exact Z0.
    + exact Eu.
    + exact Ewu.
    + exact Iu.
    + exact Lu.
    + exact Z.
Qed.
End Wbc.

Print Assumptions wb_old.
Print Assumptions wch_wbc.
