(* Part 42: UK for each kind of step of A, and A's steps simulated keeping KR and UK
   (sim_stepU: M2DQWBK11.sim_stepK with UK added; the image's step is the one sim_stepK builds). *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB.
Require Import M2DQWBK1 M2DQWBK2 M2DQWBK3 M2DQWBK5 M2DQWBK6 M2DQWBK7 M2DQWBK15 M2DQWBK30 M2DQWBK38 M2DQWBK39 M2DQWBK40 M2DQWBK41.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

Lemma crel_rg : forall p Fk Good sw sW sA c, run p sA -> rel sw sW sA -> KR Fk Good sw sW sA -> rg (cs sA c) = rg (cs sW c).
Proof. intros p Fk Good sw sW sA c RA R K. exact (proj1 (proj2 (proj2 (proj2 (crel_eq p Fk Good sw sW sA RA R K c))))). Qed.

Lemma tmW' : forall p Fk Good sw sW sA, run p sA -> rel sw sW sA -> KR Fk Good sw sW sA -> tm sW = length (lg sW).
Proof. intros. exact (tmW p Fk Good sw sW sA H H0 H1). Qed.

Theorem UK_evs : forall p Fk Good sw sW sA c k kA i iA m' m'A a K KA u uA w B BA pc' pcA tp' tpA cm' cmA es' esA,
  run p sA -> rel sw sW sA -> KR Fk Good sw sW sA -> UK sw sW sA -> WBCall sW -> kA = k -> iA = i ->
  eff (tm sW) i (rg (cs sW c)) (mof sW c) m' a K u w -> eff (tm sA) iA (rg (cs sA c)) (mof sA c) m'A a KA uA w ->
  (forall x, uA x = pi sw x (u x)) -> (forall x w', u x = Some w' -> In w' (ids (hs sW x))) ->
  oc (cs sW c) k = None ->
  (forall x h1 h2, hs sW x = h1 ++ h2 -> mH m' x = h1 ++ (tm sW, false) :: h2 -> free_head h2) ->
  UK sw (evsx sW c k i m' a K u w B pc' tp' cm' es') (evsx sA c kA iA m'A a KA uA w BA pcA tpA cmA esA).
Proof.
  intros p Fk Good sw sW sA c k kA i iA m' m'A a K KA u uA w B BA pc' pcA tp' tpA cm' cmA es' esA RA R KK KU WB Ek Ei HW HA Hu Htk Hoc FH.
  subst kA iA. assert (HA' : eff (tm sW) i (rg (cs sW c)) (mof sA c) m'A a KA uA w).
  { rewrite <- (r_tm sw sW sA R), <- (crel_rg p Fk Good sw sW sA c RA R KK). exact HA. }
  eapply (UK_gen p Fk Good sw sW sA c i m' m'A a K KA u uA w); try eassumption; try reflexivity.
  - exact (r_tm sw sW sA R).
  - split; [reflexivity|split; [reflexivity|split; [reflexivity|split; reflexivity]]].
  - split; [reflexivity|split; [reflexivity|split; [reflexivity|split; reflexivity]]].
  - intros k0 x w0 Rw. cbn [rw] in Rw. destruct (Nat.eqb_spec k0 k) as [->|Nk].
    + rewrite upd_eq in Rw. left. exact (eff_src _ _ _ _ _ _ _ _ _ HW w0 (wrote_srcv _ _ _ _ _ _ Rw)).
    + rewrite upd_neq in Rw by exact Nk. right. exact Rw.
Qed.

Theorem UK_sread : forall p Fk Good sw sW sA c k kA xs m' m'A a K KA u uA w bv B BA,
  run p sA -> rel sw sW sA -> KR Fk Good sw sW sA -> UK sw sW sA -> WBCall sW -> kA = k ->
  eff (tm sW) (ILd Plain xs (fun _ => true)) (rg (cs sW c)) (mof sW c) m' a K u w ->
  eff (tm sA) (ILd Plain xs (fun _ => true)) (rg (cs sA c)) (mof sA c) m'A a KA uA w ->
  (forall x, uA x = pi sw x (u x)) -> (forall x w', u x = Some w' -> In w' (ids (hs sW x))) ->
  oc (cs sW c) k = None ->
  UK sw (sread sW c k Plain xs B m' a K u w bv) (sread sA c kA Plain xs BA m'A a KA uA w bv).
Proof.
  intros p Fk Good sw sW sA c k kA xs m' m'A a K KA u uA w bv B BA RA R KK KU WB Ek HW HA Hu Htk Hoc.
  subst kA. assert (HA' : eff (tm sW) (ILd Plain xs (fun _ => true)) (rg (cs sW c)) (mof sA c) m'A a KA uA w).
  { rewrite <- (r_tm sw sW sA R), <- (crel_rg p Fk Good sw sW sA c RA R KK). exact HA. }
  assert (Lw : m' = learn (mof sW c) u /\ w = false).
  { inversion HW; subst; [exfalso; unfold icond, ieval in *; cbn in *; congruence|auto]. }
  destruct Lw as [Em Ew].
  eapply (UK_gen p Fk Good sw sW sA c (ILd Plain xs (fun _ => true)) m' m'A a K KA u uA w); try eassumption; try reflexivity.
  - intros x h1 h2 E1 E2. exfalso. rewrite Em in E2. cbn [mH learn mof] in E2. rewrite E1 in E2.
    apply (f_equal (@length _)) in E2. rewrite !length_app in E2. cbn in E2. lia.
  - exact (r_tm sw sW sA R).
  - split; [reflexivity|split; [reflexivity|split; [reflexivity|split; reflexivity]]].
  - split; [reflexivity|split; [reflexivity|split; [reflexivity|split; reflexivity]]].
  - intros k0 x w0 Rw. cbn [rw] in Rw. destruct (Nat.eqb_spec k0 k) as [->|Nk].
    + rewrite upd_eq in Rw. left. exact (eff_src _ _ _ _ _ _ _ _ _ HW w0 (wrote_srcv _ _ _ _ _ _ Rw)).
    + rewrite upd_neq in Rw by exact Nk. right. exact Rw.
Qed.

Theorem UK_nolog : forall sw sW sA sW' sA', UK sw sW sA ->
  hs sW' = hs sW -> lg sW' = lg sW -> vG sW' = vG sW -> vG sA' = vG sA -> wc sW' = wc sW -> wc sA' = wc sA ->
  (forall c, vP (cs sW' c) = vP (cs sW c) /\ vA (cs sW' c) = vA (cs sW c) /\ vR (cs sW' c) = vR (cs sW c) /\
     vO (cs sW' c) = vO (cs sW c) /\ vOg (cs sW' c) = vOg (cs sW c)) ->
  (forall c, vP (cs sA' c) = vP (cs sA c) /\ vA (cs sA' c) = vA (cs sA c) /\ vR (cs sA' c) = vR (cs sA c) /\
     vO (cs sA' c) = vO (cs sA c) /\ vOg (cs sA' c) = vOg (cs sA c)) ->
  (forall c, oh (cs sW' c) = oh (cs sW c) /\ oc (cs sW' c) = oc (cs sW c) /\ rw (cs sW' c) = rw (cs sW c)) ->
  UK sw sW' sA'.
Proof.
  intros sw sW sA sW' sA' KU Eh El EG EGA Ew EwA EW EA EO.
  assert (UE : forall V, U sW' V = U sW V) by (intros V; unfold U; rewrite Eh; reflexivity).
  assert (OE : forall c z, ownw sW' c z <-> ownw sW c z) by (intros c z; unfold ownw; rewrite El; tauto).
  constructor.
  - rewrite EGA, EG, UE. exact (u_G sw sW sA KU).
  - intros c. destruct (EW c) as (P1 & _). destruct (EA c) as (P2 & _). rewrite P1, P2, EG, UE. exact (u_P sw sW sA KU c).
  - intros c. destruct (EW c) as (_ & P1 & _). destruct (EA c) as (_ & P2 & _). rewrite P1, P2, EG, UE. exact (u_A sw sW sA KU c).
  - intros c. destruct (EW c) as (_ & _ & P1 & _). destruct (EA c) as (_ & _ & P2 & _). rewrite P1, P2, EG, UE. exact (u_R sw sW sA KU c).
  - intros c. destruct (EW c) as (_ & _ & _ & P1 & _). destruct (EA c) as (_ & _ & _ & P2 & _). rewrite P1, P2, EG, UE. exact (u_O sw sW sA KU c).
  - intros c. destruct (EW c) as (_ & _ & _ & _ & P1). destruct (EA c) as (_ & _ & _ & _ & P2). rewrite P1, P2, UE. exact (u_Og sw sW sA KU c).
  - intros y Sn. rewrite Ew, EwA, EG, UE. exact (u_wc sw sW sA KU y Sn).
  - intros c x w0 z Ow Sg. rewrite Eh in Sg. apply OE in Ow. destruct (EW c) as (P1 & _). rewrite P1, Eh.
    destruct (u_wbP sw sW sA KU c x w0 z Ow Sg) as [Z|(w' & P' & N' & S')]; [left; exact Z|right].
    exists w'. split; [exact P'|split; [intros Q; apply N'; apply OE; exact Q|exact S']].
  - intros c k x w0. destruct (EO c) as (_ & _ & O3). destruct (EW c) as (P1 & _). rewrite O3, P1.
    exact (u_rwP sw sW sA KU c k x w0).
Qed.
