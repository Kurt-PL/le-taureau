(* Part 38: the refined cover U of KR2, its first piece.
   U s V: V and every kept store that a written-back store in V stands for (seg: the kept store,
   then only written-back stores, then the written-back store, in one cell).  The edge from the
   kept store to the store standing for it is an edge of the history order of that cell, so U is
   finer than cov (U_cov) and lies within one cell (U_cedge).  Along every stepWB the stand-for
   pairs stay (seg_stepWB), so U only grows with the state (U_stepWB).  Under KR a kept store
   stands for nothing, so U is idempotent (U_U).
   KG_of_U: if what each event of the image knows in order (eQ) is within U of what the same
   event of the state knows (no further term), KG of M2DQWBK17 holds: an added kept store is older
   than the written-back store the state's event knows. *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB.
Require Import M2DQWBK1 M2DQWBK2 M2DQWBK3 M2DQWBK6 M2DQWBK30 M2DQWBK17.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

Definition U (s : st) (V : view) : view :=
  fun t => V t \/ exists w x, V w /\ seg (hs s x) w (Some t).

Lemma seg_old : forall h w u, seg h w (Some u) -> older h u w.
Proof.
  intros h w u (h0 & h1 & h2 & E & _). rewrite E. exists (h0 ++ [(u, false)]), (h1 ++ (w, true) :: h2). split.
  - rewrite <- app_assoc. reflexivity.
  - split; rewrite ids_app, in_app_iff; [right; left; reflexivity|right; left; reflexivity].
Qed.

Lemma U_in : forall s V, vsub V (U s V).
Proof. intros s V t H. left. exact H. Qed.

Lemma U_mono : forall s V V', vsub V V' -> vsub (U s V) (U s V').
Proof.
  intros s V V' H t [Z|(w & x & Vw & Sg)]; [left; exact (H t Z)|right]. exists w, x. split; [exact (H w Vw)|exact Sg].
Qed.

Lemma U_vor : forall s A B, vsub (U s (vor A B)) (vor (U s A) (U s B)).
Proof.
  intros s A B t [[Z|Z]|(w & x & [Vw|Vw] & Sg)].
  - left. left. exact Z.
  - right. left. exact Z.
  - left. right. exists w, x. auto.
  - right. right. exists w, x. auto.
Qed.

Lemma vor_U : forall s A B, vsub (vor (U s A) (U s B)) (U s (vor A B)).
Proof.
  intros s A B t [[Z|(w & x & Vw & Sg)]|[Z|(w & x & Vw & Sg)]].
  - left. left. exact Z.
  - right. exists w, x. split; [left; exact Vw|exact Sg].
  - left. right. exact Z.
  - right. exists w, x. split; [right; exact Vw|exact Sg].
Qed.

(* U is finer than cov, and each added store is below a store of V in the history order of one cell *)
Lemma U_cov : forall s V, vsub (U s V) (cov s V).
Proof.
  intros s V t [Z|(w & x & Vw & Sg)]; [left; exact Z|right]. exists w. split; [exact Vw|].
  constructor. left. exists x. exact (seg_old _ _ _ Sg).
Qed.

Lemma U_cedge : forall s V t, U s V t -> V t \/ exists w x, V w /\ cedge s x t w /\ In (t, false) (hs s x).
Proof.
  intros s V t [Z|(w & x & Vw & Sg)]; [left; exact Z|right]. exists w, x. split; [exact Vw|]. split.
  - left. exact (seg_old _ _ _ Sg).
  - exact (stands_kept _ _ _ Sg).
Qed.

(* one step of A on one history: as it was, or one kept store inserted *)
Lemma step_hs : forall p s s', step p s s' -> forall x,
  hs s' x = hs s x \/ exists h1 h2, hs s x = h1 ++ h2 /\ hs s' x = h1 ++ (tm s, false) :: h2.
Proof.
  intros p s s' H x.
  destruct (stepQ_split p s s' H) as [[HA _]|RF]; [|left; exact (f_equal (fun h => h x) (rfx_hs _ _ RF))].
  destruct (step_cases p s s' HA) as
    [(c & i & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & _ & _ & He & _ & ->)
    |[(c & k & d & B & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & He & _ & ->)
    |[(c & d & _ & _ & _ & _ & _ & _ & ->)
    |[(c & k & xs & B & m' & a & K & u & w & bv & _ & _ & _ & _ & _ & He & _ & ->)
    |[(c & _ & _ & _ & _ & _ & _ & _ & ->)
    |(cX & jX & bX & BX & oX & _ & _ & _ & ->)]]]]].
  1, 2, 4: destruct (eff_hist _ _ _ _ _ _ _ _ _ He) as [Eh|(xs0 & P)];
    cbn [hs lg sord searly set_es searly0 evs sread];
    [rewrite Eh; cbn [mH mof]; left; reflexivity|exact (places_cell _ _ _ _ x P)].
  1, 2: left; reflexivity.
  unfold scfix0. cbn [hs]. rewrite (hs_flp s cX oX bX). left. reflexivity.
Qed.

Lemma seg_wbst : forall s c k t H'' x w u, wbok s c k t H'' -> seg (hs s x) w (Some u) ->
  seg (hs (wbst s c k t H'') x) w (Some u).
Proof.
  intros s c k t H'' x w u Ok Sg. cbn [wbst hs].
  destruct (enters_tied_cell _ _ _ _ _ x Ok) as [E|(h1 & h2 & E1 & E2 & _)]; [rewrite E; exact Sg|].
  rewrite E2. rewrite E1 in Sg. apply seg_ins_t. exact Sg.
Qed.

Lemma seg_stepWB : forall p s s' x w u, stepWB p s s' -> seg (hs s x) w (Some u) -> seg (hs s' x) w (Some u).
Proof.
  intros p s s' x w u H Sg.
  inversion H as [s0 s1 St FHs | s0 s1 c k t1 H'' St Ps Fr Ok | s0 c k t1 xs H'' Lk Oc Oh Ai Vk Eo Fr Ok]; subst.
  - destruct (step_hs p s s' St x) as [E|(h1 & h2 & E1 & E2)]; [rewrite E; exact Sg|].
    rewrite E2. rewrite E1 in Sg. apply seg_ins_f; [exact Sg|exact (FHs x h1 h2 E1 E2)].
  - apply seg_wbst; [exact Ok|]. rewrite ((proj1 Ps) x). exact Sg.
  - apply seg_wbst; [exact Ok|exact Sg].
Qed.

Lemma U_stepWB : forall p s s' V, stepWB p s s' -> vsub (U s V) (U s' V).
Proof.
  intros p s s' V H t [Z|(w & x & Vw & Sg)]; [left; exact Z|right].
  exists w, x. split; [exact Vw|exact (seg_stepWB p s s' x w t H Sg)].
Qed.

(* under KR a kept store stands for nothing: U is idempotent *)
Lemma U_U : forall Fk Good sw s sA V, rel sw s sA -> KR Fk Good sw s sA -> vsub (U s (U s V)) (U s V).
Proof.
  intros Fk Good sw s sA V Rl K t [Z|(w & x & [Vw|(w' & x' & Vw' & Sg')] & Sg)]; [exact Z| |].
  - right. exists w, x. auto.
  - exfalso. destruct Sg as (h0 & h1 & h2 & E & _).
    assert (I : In (w, true) (hs s x)) by (rewrite E; apply in_or_app; right; right; apply in_or_app; right; left; reflexivity).
    destruct (w_bet Fk Good sw s sA K x w I) as (f & Sf & _).
    destruct (r_kept sw s sA Rl x' w (stands_kept _ _ _ Sg')) as [Sn _]. congruence.
Qed.

Theorem KG_of_U : forall Fk Good sw s sA, KR Fk Good sw s sA ->
  (forall b eA eW, ent sA b = Some eA -> ent s b = Some eW -> vsub (eQ eA) (U s (eQ eW))) -> KG s sA.
Proof.
  intros Fk Good sw s sA K HU a b e Eb Q Nab.
  destruct (k_ent Fk Good sw s sA K b e Eb) as (eW & EW & _).
  destruct (HU b e eW Eb EW a Q) as [Z|(w & x & Vw & Sg)].
  - constructor. right; right. exists eW. split; [exact EW|]. split; [exact Z|exact Nab].
  - destruct (Nat.eq_dec w b) as [->|Nw].
    + constructor. left. exists x. exact (seg_old _ _ _ Sg).
    + apply (t_trans _ _ a w b); constructor; [left; exists x; exact (seg_old _ _ _ Sg)|].
      right; right. exists eW. split; [exact EW|]. split; [exact Vw|exact Nw].
Qed.

(* instances: U adds the kept store 1 that the written-back store 5 stands for, and nothing else *)
Definition sU : st :=
  mkS 6 (fun _ => cinit) (fun _ _ => 0) (fun _ => vnil) (fun x => if Nat.eqb x 0 then [(1, false); (5, true)] else [])
      vnil (fun _ => 0) (fun _ => 0) [] [] (fun _ => None).
Lemma U_pos : U sU (vone 5) 1 /\ ~ vone 5 1.
Proof.
  split; [|intros Z; discriminate Z].
  right. exists 5, 0. split; [reflexivity|]. exists [], [], []. split; [reflexivity|constructor].
Qed.
Lemma U_neg : ~ U sU (vone 5) 2.
Proof.
  intros [Z|(w & x & Vw & Sg)]; [discriminate Z|]. cbv in Vw. subst w.
  pose proof (stands_kept _ _ _ Sg) as I. cbn in I. destruct (Nat.eqb x 0); cbn in I; intuition discriminate.
Qed.

Print Assumptions U_cov.
Print Assumptions U_cedge.
Print Assumptions seg_stepWB.
Print Assumptions U_stepWB.
Print Assumptions U_U.
Print Assumptions KG_of_U.
Print Assumptions U_pos.
Print Assumptions U_neg.
