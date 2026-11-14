(* Part 53: the residue of NewKr (M2DQWBK52) is four corners, and nothing else.
   At the new entry t of context c (image entry e, state entry eW, the state's step sW -> s1):
   both entries are the views of c before the step under one gate (step_newQ; the gate and the
   flag "wrote" agree through crel and ksame).  An item a of e's knowledge that eW neither knows
   nor knows through a store standing for it is, up to a double negation:
   - CO1: c's own kept store, read by t, that the state's c does not know in order, while the
     image's c knows it in order through vG or a store standing for it (the "own store published
     only through a stand-for" corner);
   - CO2: t reads c's own written-back store, not known in order, standing for a (the
     own-write-back corner of tookord);
   - CO3 (per cell, eQc): an item the image's c knows in order and the state's c does not, held
     in vG or through a store standing for it;
   - CO4 (per cell, eQ): a store standing for a that eW knows is in another cell.
   NewKc: the corners have the path; with M2DQWBK49-52 it gives G2. *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Lit.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB.
Require Import M2DQWBK1 M2DQWBK2 M2DQWBK3 M2DQWBK15 M2DQWBK17 M2DQWBK20 M2DQWBK30 M2DQWBK37 M2DQWBK38 M2DQWBK39 M2DQWBK40.
Require Import M2DQWBK49 M2DQWBK50 M2DQWBK51 M2DQWBK52.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

Definition CO1 (sw : nat -> option (cell -> option nat)) (sW : st) (c : nat) (eW : oev) (a : nat) : Prop :=
  (exists x, erf eW x = Some a) /\ sw a = None /\ ownw sW c a /\ ~ vO (cs sW c) a /\
  (vG sW a \/ exists w x, (vO (cs sW c) w \/ vG sW w) /\ seg (hs sW x) w (Some a)).
Definition CO2 (sw : nat -> option (cell -> option nat)) (sW : st) (c : nat) (eW : oev) (a : nat) : Prop :=
  exists x w0 f, erf eW x = Some w0 /\ sw w0 = Some f /\ f x = Some a /\ ownw sW c w0 /\ ~ vO (cs sW c) w0.
Definition CO3 (sW : st) (c : nat) (a : nat) : Prop :=
  ~ vO (cs sW c) a /\ (vG sW a \/ exists w x, (vO (cs sW c) w \/ vG sW w) /\ seg (hs sW x) w (Some a)).
Definition CO4 (s1 : st) (eW : oev) (x a : nat) : Prop :=
  exists w x', x' <> x /\ eQ eW w /\ seg (hs s1 x') w (Some a).

Section C.
Set Default Proof Using "All".
Variables (p : prog) (sw : nat -> option (cell -> option nat)) (sW sA sA' s1 : st) (e eW : oev).
Hypothesis RA : run p sA.
Hypothesis Rl : rel sw sW sA.
Hypothesis K : KR False G0 sw sW sA.
Hypothesis UK0 : UK sw sW sA.
Hypothesis RA' : run p sA'.
Hypothesis R1 : rel sw s1 sA'.
Hypothesis K1 : KR False G0 sw s1 sA'.
Hypothesis St : step p sW s1.
Hypothesis StA : step p sA sA'.
Hypothesis SG : forall x w a, seg (hs sW x) w (Some a) -> seg (hs s1 x) w (Some a).
Hypothesis Ee : ent sA' (tm sA) = Some e.
Hypothesis EW : ent s1 (tm sA) = Some eW.

Let c := ec eW.

Lemma Ks : ksame sw s1 (tm sA) e eW.
Proof. destruct (k_ent False G0 sw s1 sA' K1 (tm sA) e Ee) as (eW' & E' & S). rewrite EW in E'. injection E' as <-. exact S. Qed.

Lemma Et : tm sA = tm sW.
Proof. exact (r_tm sw sW sA Rl). Qed.

(* the two entries: the views before the step under one gate *)
Lemma gates : exists g : bool,
  eQ e = (if g then vor (vOg (cs sA c)) (tookord sA c (vO (cs sA c)) (erf e)) else vnil) /\
  eQ eW = (if g then vor (vOg (cs sW c)) (tookord sW c (vO (cs sW c)) (erf eW)) else vnil) /\
  (exists f : bool, eQc e = (if f then vO (cs sA c) else vnil) /\ eQc eW = (if f then vO (cs sW c) else vnil)).
Proof.
  pose proof Ks as (_ & Ec & Ek & _ & _ & _ & _ & _ & _ & Ew).
  pose proof (step_newQ p sA sA' e StA (i_tm p sA (Inv1_run p sA RA)) Ee) as (QA & QcA).
  assert (EW' : ent s1 (tm sW) = Some eW) by (rewrite <- Et; exact EW).
  pose proof (step_newQ p sW s1 eW St (tmW p False G0 sw sW sA RA Rl K) EW') as (QW & QcW).
  cbv zeta in QA, QcA, QW, QcW.
  assert (Sw : sw (tm sA) = None) by (apply (i_sw sw sW sA Rl); rewrite Et; lia).
  rewrite (Ew Sw) in QW. rewrite Ec, Ek in QA, QcA.
  destruct (crel_eq p False G0 sw s1 sA' RA' R1 K1 (ec eW)) as (_ & _ & Ai & _).
  destruct (crel_eq p False G0 sw sW sA RA Rl K (ec eW)) as (_ & _ & _ & Rg & _).
  rewrite Ai, Rg in QA, QcA.
  exists (ew e || xload (ai (cs s1 (ec eW)) (ek eW)) (rg (cs sW (ec eW)))).
  split; [exact QA|]. split; [exact QW|].
  exists (xload (ai (cs s1 (ec eW)) (ek eW)) (rg (cs sW (ec eW)))). split; [exact QcA|exact QcW].
Qed.

(* a kept store the state's context owns is owned in the image *)
Lemma own_kept : forall z, ownw sW c z -> sw z = None -> ownw sA c z.
Proof.
  intros z (eW0 & E0 & C0 & W0) Sz.
  assert (L : z < length (lg sA)) by (rewrite (k_len False G0 sw sW sA K); apply nth_error_Some; congruence).
  destruct (nth_error (lg sA) z) as [eA0|] eqn:EA; [|apply nth_error_None in EA; lia].
  destruct (k_ent False G0 sw sW sA K z eA0 EA) as (eW1 & E1 & (_ & S2 & _ & _ & _ & _ & _ & _ & _ & S10)).
  unfold ent in E1. rewrite E0 in E1. injection E1 as <-. exists eA0. split; [exact EA|]. split; [congruence|].
  rewrite <- (S10 Sz). exact W0.
Qed.

(* a store the state's entry read that has an image different from itself is written back and
   stands, in s1, for what the image's entry read *)
Lemma wb_read : forall x w0 f, erf eW x = Some w0 -> sw w0 = Some f -> seg (hs s1 x) w0 (f x).
Proof.
  intros x w0 f Ew Sw. pose proof Ks as (_ & _ & _ & _ & _ & _ & _ & S8 & _).
  destruct (in_ids_fl _ _ (S8 x w0 Ew)) as [[|] I].
  - destruct (w_bet False G0 sw s1 sA' K1 x w0 I) as (f' & Sf & Sg). rewrite Sw in Sf. injection Sf as <-. exact Sg.
  - destruct (r_kept sw s1 sA' R1 x w0 I) as [Sn _]. congruence.
Qed.

(* what the image's entry knows (eQ): known by the state's entry, through a store standing for it
   that the state's entry knows, or a corner *)
Theorem core_eQ : forall a, eQ e a ->
  ~ ~ (eQ eW a \/ (exists w x, eQ eW w /\ seg (hs s1 x) w (Some a)) \/ CO1 sw sW c eW a \/ CO2 sw sW c eW a).
Proof.
  intros a Q N. destruct gates as (g & QA & QW & _).
  rewrite QA in Q. destruct g; [|contradiction].
  destruct Q as [Og|((x & Ex) & Nown)].
  - destruct (u_Og sw sW sA UK0 c a Og) as [Z|(w & x & Vw & Sg)].
    + apply N. left. rewrite QW. left. exact Z.
    + apply N. right; left. exists w, x. split; [rewrite QW; left; exact Vw|exact (SG x w a Sg)].
  - pose proof Ks as (_ & _ & _ & _ & _ & _ & S7 & _). rewrite (S7 x) in Ex.
    destruct (erf eW x) as [w0|] eqn:Ew; [|discriminate]. cbn [pi] in Ex.
    destruct (sw w0) as [f|] eqn:Sw.
    + apply N. right; left. exists w0, x. split; [|rewrite <- Ex; exact (wb_read x w0 f Ew Sw)].
      rewrite QW. right. split; [exists x; exact Ew|]. intros (Ow & NO).
      apply N. right; right; right. exists x, w0, f. auto.
    + injection Ex as <-. apply N. left. rewrite QW. right. split; [exists x; exact Ew|]. intros (Ow & NO).
      apply Nown. split; [exact (own_kept w0 Ow Sw)|]. intros OA.
      apply (u_O sw sW sA UK0 c w0 OA). intros [[Oa|Ga]|(w & x' & [Ow'|Gw] & Sg)].
      * exact (NO Oa).
      * apply N. right; right; left. split; [exists x; exact Ew|]. split; [exact Sw|]. split; [exact Ow|]. split; [exact NO|]. left; exact Ga.
      * apply N. right; right; left. split; [exists x; exact Ew|]. split; [exact Sw|]. split; [exact Ow|]. split; [exact NO|]. right. exists w, x'. auto.
      * apply N. right; right; left. split; [exists x; exact Ew|]. split; [exact Sw|]. split; [exact Ow|]. split; [exact NO|]. right. exists w, x'. auto.
Qed.

(* the residue of NewKr is the four corners *)
Theorem res_corners :
  (forall a, eQ e a -> ~ eQ eW a -> ~ (exists w x, eQ eW w /\ seg (hs s1 x) w (Some a)) ->
     ~ ~ (CO1 sw sW c eW a \/ CO2 sw sW c eW a)) /\
  (forall x a, In x (eC e) -> (eQ e a \/ eQc e a) -> In a (ids (hs sA' x)) ->
     ~ ((eQ eW a \/ eQc eW a) /\ In a (ids (hs s1 x))) ->
     ~ (exists w, (eQ eW w \/ eQc eW w) /\ seg (hs s1 x) w (Some a)) ->
     ~ ~ (CO1 sw sW c eW a \/ CO2 sw sW c eW a \/ CO3 sW c a \/ CO4 s1 eW x a)).
Proof.
  split.
  - intros a Q NQ NS N. apply (core_eQ a Q). intros [H|[H|[H|H]]]; [exact (NQ H)|exact (NS H)|apply N; left; exact H|apply N; right; exact H].
  - intros x a Ix Q Ia ND NS N.
    assert (Ia1 : In a (ids (hs s1 x))).
    { destruct (in_ids_fl _ _ Ia) as [b Ib]. rewrite (r_hs sw s1 sA' R1 x) in Ib. apply in_hers in Ib.
      exact (in_ids_of _ _ _ (proj1 Ib)). }
    destruct Q as [Q|Q].
    + apply (core_eQ a Q). intros [H|[(w & x' & Qw & Sg)|[H|H]]].
      * exact (ND (conj (or_introl H) Ia1)).
      * destruct (Nat.eq_dec x' x) as [->|Nx]; [exact (NS (ex_intro _ w (conj (or_introl Qw) Sg)))|].
        apply N. right; right; right. exists w, x'. auto.
      * apply N. left. exact H.
      * apply N. right; left. exact H.
    + destruct gates as (_ & _ & _ & f & QcA & QcW). rewrite QcA in Q. destruct f; [|contradiction].
      assert (NO : ~ vO (cs sW c) a) by (intros Oa; apply ND; split; [right; rewrite QcW; exact Oa|exact Ia1]).
      apply (u_O sw sW sA UK0 c a Q). intros [[Oa|Ga]|(w & x' & Vw & Sg)].
      * exact (NO Oa).
      * apply N. right; right; left. split; [exact NO|left; exact Ga].
      * apply N. right; right; left. split; [exact NO|right; exists w, x'; auto].
Qed.
End C.

Print Assumptions core_eQ.
Print Assumptions res_corners.
