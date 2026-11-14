(* Part 41: one logged instruction keeps UK (UK_gen), given WBCall of the state
   before (a read of a written-back store takes, in the image, the kept store it stands for,
   whose conveyed set (WBC'') bounds).  The new states are given by what they are made of: the
   context's new views are the effect's (newO, newOg), the log gets one entry, the histories,
   conveyed sets and published view are the effect's; the write a slot records is in P.  Instances: an access or fence performed and logged (M2DQWBK7.evsx: UK_evs) and
   a CAS's read alone (M2Inv.sread: UK_sread). *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB.
Require Import M2DQWBK1 M2DQWBK2 M2DQWBK3 M2DQWBK5 M2DQWBK6 M2DQWBK7 M2DQWBK15 M2DQWBK30 M2DQWBK38 M2DQWBK39 M2DQWBK40.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

Section EvsU.
Set Default Proof Using "All".
Variables (p : prog) (Fk : Prop) (Good : nat -> Prop) (sw : nat -> option (cell -> option nat)) (sW sA : st).
Variables (c : nat) (i : instr) (m' m'A : mst) (a : val) (K KA : view) (u uA : cell -> option nat) (w : bool).
Variables (sW' sA' : st) (ccW ccA : cst) (eWn : oev).
Hypothesis RA : run p sA.
Hypothesis R : rel sw sW sA.
Hypothesis KK : KR Fk Good sw sW sA.
Hypothesis KU : UK sw sW sA.
Hypothesis WB : WBCall sW.
Hypothesis HW : eff (tm sW) i (rg (cs sW c)) (mof sW c) m' a K u w.
Hypothesis HA' : eff (tm sW) i (rg (cs sW c)) (mof sA c) m'A a KA uA w.
Hypothesis Hu : forall x, uA x = pi sw x (u x).
Hypothesis Htk : forall x w', u x = Some w' -> In w' (ids (hs sW x)).
Hypothesis FH : forall x h1 h2, hs sW x = h1 ++ h2 -> mH m' x = h1 ++ (tm sW, false) :: h2 -> free_head h2.
Hypothesis TAu : tm sA = tm sW.
Hypothesis EG : vG sW' = mG m'.
Hypothesis EGA : vG sA' = mG m'A.
Hypothesis Ewc : wc sW' = mC m'.
Hypothesis EwcA : wc sA' = mC m'A.
Hypothesis Ehs : hs sW' = mH m'.
Hypothesis Elg : lg sW' = lg sW ++ [eWn].
Hypothesis Ecs : forall c', cs sW' c' = if Nat.eqb c' c then ccW else cs sW c'.
Hypothesis EcsA : forall c', cs sA' c' = if Nat.eqb c' c then ccA else cs sA c'.
Hypothesis EccW : vP ccW = mP m' /\ vA ccW = mA m' /\ vR ccW = mR m' /\
  vO ccW = newO sW c i (mof sW c) m' (vO (cs sW c)) /\ vOg ccW = newOg i m' (vOg (cs sW c)).
Hypothesis EccA : vP ccA = mP m'A /\ vA ccA = mA m'A /\ vR ccA = mR m'A /\
  vO ccA = newO sA c i (mof sA c) m'A (vO (cs sA c)) /\ vOg ccA = newOg i m'A (vOg (cs sA c)).
Hypothesis Hrw : forall k0 x w0, rw ccW k0 x = Some w0 -> mP m' w0 \/ rw (cs sW c) k0 x = Some w0.

Lemma TWlu : tm sW = length (lg sW). Proof. exact (tmW p Fk Good sw sW sA RA R KK). Qed.

Lemma entWu : forall t e, ent sW' t = Some e -> (t < tm sW /\ ent sW t = Some e) \/ t = tm sW.
Proof.
  intros t e E. unfold ent in E. rewrite Elg in E. destruct (ent_app _ _ _ _ E) as [(E1 & L)|(E1 & E2)].
  - left. rewrite TWlu. unfold ent. auto.
  - right. rewrite TWlu. exact E1.
Qed.
Lemma entWu_old : forall t e, ent sW t = Some e -> ent sW' t = Some e.
Proof. intros t e E. unfold ent. rewrite Elg. apply app_ent. exact E. Qed.

Lemma ownw_backu : forall c' z, ownw sW' c' z -> z < tm sW -> ownw sW c' z.
Proof. intros c' z (e & E & Ec & Ew') L. destruct (entWu z e E) as [(_ & E')|Z]; [exists e; auto|lia]. Qed.
Lemma ownw_fwdu : forall c' z, ownw sW c' z -> ownw sW' c' z.
Proof. intros c' z (e & E & Ec & Ew'). exists e. split; [exact (entWu_old z e E)|auto]. Qed.

Lemma segG : forall x w0 z, seg (hs sW x) w0 (Some z) -> seg (hs sW' x) w0 (Some z).
Proof.
  intros x w0 z Sg. rewrite Ehs.
  destruct (eff_hist _ _ _ _ _ _ _ _ _ HW) as [Eh|(xs0 & P)]; cbn [mH mof] in *; [rewrite Eh; exact Sg|].
  destruct (places_cell _ _ _ _ x P) as [E|(h1 & h2 & E1 & E2)]; [rewrite E; exact Sg|].
  rewrite E2. rewrite E1 in Sg. apply seg_ins_f; [exact Sg|exact (FH x h1 h2 E1 E2)].
Qed.
Lemma Ugrow : forall V, vsub (U sW V) (U sW' V).
Proof. intros V z [Z|(w0 & x & Vw & Sg)]; [left; exact Z|right; exists w0, x; split; [exact Vw|exact (segG x w0 z Sg)]]. Qed.

Lemma segB : forall x w0 z, seg (hs sW' x) w0 (Some z) -> seg (hs sW x) w0 (Some z).
Proof.
  intros x w0 z Sg. rewrite Ehs in Sg.
  destruct (eff_hist _ _ _ _ _ _ _ _ _ HW) as [Eh|(xs0 & P)]; cbn [mH mof] in *; [rewrite Eh in Sg; exact Sg|].
  destruct (places_cell _ _ _ _ x P) as [E|(h1 & h2 & E1 & E2)]; [rewrite E in Sg; exact Sg|].
  rewrite E2 in Sg. rewrite E1. apply (seg_del_f h1 h2 (tm sW)); [exact Sg|exact (FH x h1 h2 E1 E2)|].
  intros I. rewrite <- E1 in I. pose proof (i_ids sw sW sA R x (tm sW) I). lia.
Qed.

Lemma GG : vsub (vG sW) (mG m').
Proof. exact (M2Eff.eff_G _ _ _ _ _ _ _ _ _ HW). Qed.

Lemma KWAu : forall z, (vP (cs sA c) z \/ vA (cs sA c) z) -> ownw sW c z -> ownw sA c z.
Proof.
  intros z PA (e' & E' & Ec' & _).
  destruct (j_views p sA (proj2 (Inv2_run p sA RA)) c z ltac:(tauto)) as (eA & EA & WA).
  destruct (k_ent Fk Good sw sW sA KK z eA EA) as (eW & EW & (_ & S2 & _ & _ & _ & _ & _ & _ & S9 & _)).
  unfold ent in EW. rewrite E' in EW. injection EW as <-. exists eA. split; [exact EA|]. split; [congruence|exact WA].
Qed.

Lemma KWBu : forall w0 x z, ownw sW c w0 -> seg (hs sW' x) w0 (Some z) ->
  vP (cs sW c) z \/ exists w', vP (cs sW c) w' /\ ~ ownw sW c w' /\ seg (hs sW' x) w' (Some z).
Proof.
  intros w0 x z Ow Sg. destruct (u_wbP sw sW sA KU c x w0 z Ow (segB x w0 z Sg)) as [Z|(w' & P' & N' & S')]; [left; exact Z|].
  right. exists w'. split; [exact P'|split; [exact N'|exact (segG x w' z S')]].
Qed.

Lemma lift : forall X V, vsub X (U sW (vor V (vG sW))) -> vsub X (U sW' (vor V (mG m'))).
Proof.
  intros X V H z Z. apply Ugrow. apply (Ucomb sW _ _ _ H); [|exact Z]. intros y [Y|Y]; [left; exact Y|right; exact (GG y Y)].
Qed.

Lemma effU_here : vsub (mP m'A) (U sW' (vor (mP m') (mG m'))) /\ vsub (mA m'A) (U sW' (vor (mA m') (mG m'))) /\
  vsub (mR m'A) (U sW' (vor (mR m') (mG m'))) /\ vsub (mG m'A) (U sW' (mG m')).
Proof.
  apply (effU sW' (tm sW) i (rg (cs sW c)) (mof sW c) (mof sA c) m' m'A a K KA u uA w HW HA').
  - intros z Z. apply Ugrow. exact (u_P sw sW sA KU c z Z).
  - intros z Z. apply Ugrow. exact (u_A sw sW sA KU c z Z).
  - intros z Z. apply Ugrow. exact (u_R sw sW sA KU c z Z).
  - intros z Z. apply Ugrow. exact (u_G sw sW sA KU z Z).
  - intros z Z. exact (ownw_AW p Fk Good sw sW sA RA R KK c z Z).
  - exact (w_OW Fk Good sw sW sA KK c).
  - intros z. exact (ownw_dec2 sW c z).
  - exact KWAu.
  - exact KWBu.
  - intros z Z. apply Ugrow. exact (srcsU Fk Good sw sW sA R KK u uA Hu Htk z Z).
  - intros z Z. apply Ugrow. exact (carrU Fk Good sw sW sA R KK KU WB u uA Hu Htk c z Z).
Qed.

Lemma ff_PG : i = IFn FFull -> vsub (mG m') (mP m').
Proof. intros E. pose proof HW as H. rewrite E in H. destruct (eff_ffK _ _ _ _ _ _ _ _ H) as (_ & -> & _). intros z Z. exact Z. Qed.

Theorem UK_gen : UK sw sW' sA'.
Proof.
  destruct effU_here as (EP & EA & ER & EG').
  destruct EccW as (WP & WA & WR & WO & WOg). destruct EccA as (AP & AA & AR & AO & AOg).
  constructor.
  - rewrite EGA, EG. exact EG'.
  - intros c'. rewrite Ecs, EcsA, EG. destruct (Nat.eqb_spec c' c) as [->|N]; [rewrite WP, AP; exact EP|].
    exact (lift _ _ (u_P sw sW sA KU c')).
  - intros c'. rewrite Ecs, EcsA, EG. destruct (Nat.eqb_spec c' c) as [->|N]; [rewrite WA, AA; exact EA|].
    exact (lift _ _ (u_A sw sW sA KU c')).
  - intros c'. rewrite Ecs, EcsA, EG. destruct (Nat.eqb_spec c' c) as [->|N]; [rewrite WR, AR; exact ER|].
    exact (lift _ _ (u_R sw sW sA KU c')).
  - intros c'. rewrite Ecs, EcsA, EG. destruct (Nat.eqb_spec c' c) as [->|N].
    + rewrite WO, AO. apply (newO_U sW' sW sA c (mof sW c) (mof sA c) m' m'A (vO (cs sW c)) (vO (cs sA c))).
      * apply (NN_sub _ _ _ (u_O sw sW sA KU c)). intros z Z. apply Ugrow. exact Z.
      * exact EP.
      * exact EG'.
      * exact GG.
      * intros z Z. apply Ugrow. exact (u_P sw sW sA KU c z Z).
      * intros z Z. apply Ugrow. exact (u_A sw sW sA KU c z Z).
      * intros z Z. apply Ugrow. exact (u_G sw sW sA KU z Z).
      * intros z. exact (ownw_dec2 sW c z).
      * exact KWAu.
      * exact KWBu.
      * exact ff_PG.
    + apply (NN_sub _ _ _ (u_O sw sW sA KU c')). exact (lift _ _ (fun z Z => Z)).
  - intros c'. rewrite Ecs, EcsA. destruct (Nat.eqb_spec c' c) as [->|N].
    + rewrite WOg, AOg. apply (newOg_U sW' i m' m'A); [exact EP|exact EG'| |exact ff_PG].
      intros z Z. apply Ugrow. exact (u_Og sw sW sA KU c z Z).
    + intros z Z. apply Ugrow. exact (u_Og sw sW sA KU c' z Z).
  - intros y Sn. rewrite Ewc, EwcA, EG.
    destruct (eff_C _ _ _ _ _ _ _ _ _ HA') as [CA1 CA0]. destruct (eff_C _ _ _ _ _ _ _ _ _ HW) as [CW1 CW0].
    assert (Wc : w = true \/ w = false) by (destruct w; auto). destruct Wc as [Ew|Ew].
    + rewrite (CA1 Ew), (CW1 Ew). cbn [mC mR mof]. destruct (Nat.eq_dec y (tm sW)) as [->|Ny].
      * rewrite !upd_eq. apply vsub_or.
        -- apply lift. apply (Ucomb sW _ _ _ (u_R sw sW sA KU c)). intros z [Z|Z]; [left; left; exact Z|right; exact Z].
        -- intros z Z. apply U_in. left. right. exact Z.
      * rewrite !upd_neq by exact Ny. exact (lift _ _ (u_wc sw sW sA KU y Sn)).
    + rewrite (CA0 Ew), (CW0 Ew). cbn [mC mof]. exact (lift _ _ (u_wc sw sW sA KU y Sn)).
  - intros c0 x w0 z Ow Sg. pose proof (segB x w0 z Sg) as Sg0.
    assert (Lw : w0 < tm sW).
    { apply (i_ids sw sW sA R x). destruct Sg0 as (h0 & h1 & h2 & E & _). rewrite E, ids_app. apply in_or_app. right.
      right. rewrite ids_app. apply in_or_app. right. left. reflexivity. }
    assert (PM : vsub (vP (cs sW c0)) (vP (cs sW' c0))).
    { rewrite Ecs. destruct (Nat.eqb_spec c0 c) as [->|N]; [|intros y Y; exact Y].
      rewrite WP. exact (eff_Pmono _ _ _ _ _ _ _ _ _ HW). }
    destruct (u_wbP sw sW sA KU c0 x w0 z (ownw_backu c0 w0 Ow Lw) Sg0) as [Z|(w' & P' & N' & S')]; [left; exact (PM z Z)|].
    right. exists w'. split; [exact (PM w' P')|]. split; [|exact (segG x w' z S')].
    intros O'. apply N'. apply (ownw_backu c0 w' O'). apply (i_ids sw sW sA R x).
    destruct S' as (h0 & h1 & h2 & E & _). rewrite E, ids_app. apply in_or_app. right.
    right. rewrite ids_app. apply in_or_app. right. left. reflexivity.
  - intros c0 k0 x w0. rewrite Ecs. destruct (Nat.eqb_spec c0 c) as [->|N]; intros Rw.
    + rewrite WP. destruct (Hrw k0 x w0 Rw) as [Z|Rw']; [exact Z|].
      exact (eff_Pmono _ _ _ _ _ _ _ _ _ HW w0 (u_rwP sw sW sA KU c k0 x w0 Rw')).
    + exact (u_rwP sw sW sA KU c0 k0 x w0 Rw).
Qed.
End EvsU.

Print Assumptions UK_gen.
