(* Part 45: the chain step with UK (simWBU_link: M2DQWBK37.simWBK_link with UK added,
   given WBCall of the state before; the write-back links keep UK by M2DQWBK44.UK_wb). *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB.
Require Import M2DQWBK1 M2DQWBK2 M2DQWBK3 M2DQWBK4 M2DQWBK7 M2DQWBK9 M2DQWBK10 M2DQWBK11 M2DQWBK12 M2DQWBK13 M2DQWBK19 M2DQWBFsc.
Require Import M2DQWBK20 M2DQWBK37 M2DQWBK38 M2DQWBK39 M2DQWBK40 M2DQWBK42 M2DQWBK43 M2DQWBK44 M2DQWBK46.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

Section ChU.
Variables (p : prog) (W : wf p) (Fk : Prop) (Good : nat -> Prop).

Theorem simWBU_link : forall sw sW sA sW', run p sA -> rel sw sW sA -> KR Fk Good sw sW sA -> runWB p sW -> stepWB p sW sW' ->
  (Fk -> HB1 Good sW') -> (Fk -> HB2 Good sW') ->
  exists sw' sA', run p sA' /\ rel sw' sW' sA' /\ KR Fk Good sw' sW' sA' /\ (UK sw sW sA -> WBCall sW -> UK sw' sW' sA') /\ wlink p Fk Good sw sW sA sw' sW' sA'.
Proof.
  intros sw sW sA sW' RA R K RW H H1 H2. pose proof (runWB_KM p sW RW) as Km. pose proof (i_ids sw sW sA R) as Ii. pose proof (tmW p Fk Good sw sW sA RA R K) as TL.
  inversion H as [s0 s1 St FHs | s0 s1 c k t1 H'' St Ps Fr Ok | s0 c k t1 xs H'' Lk Oc Oh Ai Vk Eo Fr Ok]; subst.
  - destruct (sim_stepU p W sw sW sA RA R Fk Good K sW' St FHs H1 H2) as (sA' & St' & R' & K' & KU').
    exists sw, sA'. split; [econstructor; eauto|]. split; [exact R'|]. split; [exact K'|]. split; [exact KU'|].
    left. auto.
  - assert (C1 : Fk -> HB1 Good s1) by (intros HF; exact (proj1 (wb_HB_back Good s1 c k t1 H'' (H1 HF) (H2 HF)))).
    assert (C2 : Fk -> HB2 Good s1) by (intros HF; exact (proj2 (wb_HB_back Good s1 c k t1 H'' (H1 HF) (H2 HF)))).
    pose proof (partskip_form p sW s1 c k t1 St Ps) as Es1.
    pose proof Ps as Ps0. destruct Ps as (NW & T1 & Pk & Pk' & Oc0 & Oh0 & Oh1 & Cc & Vk).
    destruct (sim_stepU p W sw sW sA RA R Fk Good K s1 St (nowrite_fhsafe _ _ NW) C1 C2) as (sA' & St' & R' & K' & KU').
    assert (RA' : run p sA') by (econstructor; eauto).
    assert (Fr' : forall x, ~ In t1 (ids (hs s1 x))) by (intros x; rewrite (NW x); exact (Fr x)).
    assert (Oc1 : oc (cs s1 c) k = None) by (rewrite Es1; unfold sskip; cbn [cs]; rewrite upd_eq; cbn [oc]; exact Oc0).
    exists (upd sw t1 (Some (fun x => pi sw x (rw (cs s1 c) k x)))), sA'.
    split; [exact RA'|]. split; [|split; [|split]].
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
    + intros KU WB. apply (UK_wb p Fk Good sw s1 sA' c k t1 H'' RA' R' K' (KU' KU WB)); [exact Fr'|exact Ok|].
      destruct (i_ohW p Fk Good sw s1 sA' RA' R' K' c k t1 Oh1) as (e & E & Ec & _). exists e. auto.
    + right; left. exists s1, c, k, t1, H''. auto 12.
  - exists (upd sw t1 (Some (fun x => pi sw x (rw (cs sW c) k x)))), sA.
    split; [exact RA|]. split; [|split; [|split]].
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
    + intros KU WB. apply (UK_wb p Fk Good sw sW sA c k t1 H'' RA R K KU); [exact Fr|exact Ok|].
      destruct (i_ohW p Fk Good sw sW sA RA R K c k t1 Oh) as (e & E & Ec & _). exists e. auto.
    + right; right. exists c, k, t1, xs, H''. auto 15.
Qed.
Inductive wchU : st -> (nat -> option (cell -> option nat)) -> st -> Prop :=
| wchU0 : wchU sinit sw0 sinit
| wchUS : forall sW sw sA sW' sw' sA', wchU sW sw sA -> wlink p Fk Good sw sW sA sw' sW' sA' ->
    run p sA' -> rel sw' sW' sA' -> KR Fk Good sw' sW' sA' -> (UK sw sW sA -> WBCall sW -> UK sw' sW' sA') ->
    wchU sW' sw' sA'.

Lemma wchU_wch : forall sW sw sA, wchU sW sw sA -> wch p Fk Good sW sw sA.
Proof.
  intros sW sw sA H. induction H as [|sW sw sA sW' sw' sA' _ IH L RA R K _]; [constructor|].
  exact (wchS p Fk Good sW sw sA sW' sw' sA' IH L RA R K).
Qed.

Theorem runWBU_chain : forall s, runWB p s -> (Fk -> HB1 Good s) -> (Fk -> HB2 Good s) ->
  exists sw sA, wchU s sw sA.
Proof.
  intros s R. induction R as [|s s' R IH St]; intros H1 H2.
  - exists sw0, sinit. constructor.
  - destruct (stepWB_HB_back p Fk Good s s' R St H1 H2) as [B1 B2].
    destruct (IH B1 B2) as (sw & sA & Ch).
    destruct (wch_inv p Fk Good s sw sA (wchU_wch s sw sA Ch)) as (RA & Rl & K & _).
    destruct (simWBU_link sw s sA s' RA Rl K R St H1 H2) as (sw' & sA' & RA' & Rl' & K' & KU' & L).
    exists sw', sA'. exact (wchUS s sw sA s' sw' sA' Ch L RA' Rl' K' KU').
Qed.
End ChU.

Print Assumptions simWBU_link.
Print Assumptions runWBU_chain.
