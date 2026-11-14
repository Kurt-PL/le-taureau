(* Part 2: along a step of the write-back model the event graph only grows, every
   event keeps its context, slot and kind, and a guard() an access follows stays one. *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB M2DQWBK1.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQShim.

Lemma eff_hist : forall t i r m m' a K u w, eff t i r m m' a K u w ->
  mH m' = mH m \/ exists xs, places (mH m) xs t (mH m').
Proof. intros t i r m m' a K u w H. inversion H; subst; cbn; auto; right; eexists; eassumption. Qed.

Lemma places_older : forall H xs t H' x a b, places H xs t H' -> older (H x) a b -> older (H' x) a b.
Proof.
  intros H xs t H' x a b P O. destruct (places_cell _ _ _ _ x P) as [E|(h1 & h2 & E1 & E2)]; [rewrite E; exact O|].
  rewrite E2. rewrite E1 in O. apply older_ins. exact O.
Qed.
Lemma places_ids : forall H xs t H' x b, places H xs t H' -> In b (ids (H x)) -> In b (ids (H' x)).
Proof.
  intros H xs t H' x b P I. destruct (places_cell _ _ _ _ x P) as [E|(h1 & h2 & E1 & E2)]; [rewrite E; exact I|].
  rewrite E2. rewrite E1 in I. apply in_ids_ins. right. exact I.
Qed.

(* the shape of a step's change: histories grow by insertion, the log by appending *)
Definition grows (s s' : st) : Prop :=
  (forall x a b, older (hs s x) a b -> older (hs s' x) a b) /\
  (forall x b, In b (ids (hs s x)) -> In b (ids (hs s' x))) /\
  (forall t e, ent s t = Some e -> ent s' t = Some e).

Lemma grows_gedge : forall s s', grows s s' -> forall a b, gedge s a b -> gedge s' a b.
Proof. intros s s' (HO & HI & HL) a b G. apply (gedge_grow s s' HO HI HL a b G). Qed.

Lemma app_ent : forall (l : list oev) e t g, nth_error l t = Some g -> nth_error (l ++ [e]) t = Some g.
Proof. intros l e t g H. rewrite nth_error_app1; [exact H|apply nth_error_Some; congruence]. Qed.

Lemma step_growsA : forall p s s', M2Model.step p s s' -> grows s s'.
Proof.
  intros p s s' H.
  destruct (step_cases p s s' H) as
    [(c & i & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & _ & _ & He & _ & ->)
    |[(c & k & d & B & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & He & _ & ->)
    |[(c & d & _ & _ & _ & _ & _ & _ & ->)
    |[(c & k & xs & B & m' & a & K & u & w & bv & _ & _ & _ & _ & _ & He & _ & ->)
    |[(c & _ & _ & _ & _ & _ & _ & _ & ->)
    |(cX & jX & bX & BX & oX & _ & _ & _ & ->)]]]]].
  all: unfold grows, ent.
  1, 2, 4: destruct (eff_hist _ _ _ _ _ _ _ _ _ He) as [Eh|(xs0 & P)];
    [ cbn [hs lg sord searly set_es searly0 evs sread]; rewrite Eh; cbn [mH mof];
      split; [intros; assumption|split; [intros; assumption|intros; apply app_ent; assumption]]
    | cbn [hs lg sord searly set_es searly0 evs sread];
      split; [intros x a0 b0 O; exact (places_older _ _ _ _ x a0 b0 P O)|split; [intros x b0 I; exact (places_ids _ _ _ _ x b0 P I)|intros; apply app_ent; assumption]] ].
  1, 2: cbn [hs lg smatch sskip]; split; [intros; assumption|split; [intros; assumption|intros; assumption]].
  unfold scfix0. cbn [hs lg]. rewrite (hs_flp s cX oX bX), (lg_flp s cX oX bX).
  split; [intros; assumption|split; [intros; assumption|intros; assumption]].
Qed.

Lemma step_grows : forall p s s', step p s s' -> grows s s'.
Proof.
  intros. match goal with H : stepQ _ ?s ?s2 |- _ => destruct (stepQ_split _ s s2 H) as [[HA _]|RF]; [eapply step_growsA; eauto|] end.
  unfold grows, ent in *. rfx_rw RF. split; [intros; assumption|split; intros; assumption].
Qed.

(* ---------- the write-back patch ---------- *)
Definition sete (t : nat) (e : oev) : oev :=
  if Nat.eqb (et e) t then mkO (et e) (ec e) (ek e) (eP e) (erf e) true (eC e) (eR e) (eQ e) (eQc e) (eh e) else e.
Lemma nth_setew : forall l t a, nth_error (setew l t) a = option_map (sete t) (nth_error l a).
Proof. intros l t a. unfold setew. rewrite nth_error_map. reflexivity. Qed.

Lemma enters_tied_cell : forall u H xs t H' x, enters_tied u H xs t H' ->
  H' x = H x \/ exists h1 h2, H x = h1 ++ h2 /\ H' x = h1 ++ (t, true) :: h2 /\ free_head h2 /\
    match u x with None => h1 = [] | Some w => exists h0 g, h1 = h0 ++ [(w, g)] end.
Proof.
  intros u H xs t H' x E. destruct (E x) as [E1 E2]. destruct (in_dec Nat.eq_dec x xs) as [I|N].
  - right. destruct (E1 I) as (h1 & h2 & A & B & C & D). exists h1, h2. auto.
  - left. apply E2. exact N.
Qed.

Lemma wbst_grows : forall s c k t H'', wbok s c k t H'' ->
  (forall a b, gedge s a b -> gedge (wbst s c k t H'') a b).
Proof.
  intros s c k t H'' Ok a b [(x & O)|[(e & x & L & Ix & Ib & N & M)|(e & L & Q & N)]]; unfold gedge, wbst; cbv zeta; cbn [hs lg].
  - left. exists x. destruct (enters_tied_cell _ _ _ _ _ x Ok) as [E|(h1 & h2 & E1 & E2 & _)]; [rewrite E; exact O|].
    rewrite E2. rewrite E1 in O. apply older_ins. exact O.
  - right; left. exists (sete t e), x. rewrite nth_setew, L. cbn [option_map]. unfold sete.
    destruct (Nat.eqb (et e) t); cbn [eR erf].
    all: (split; [reflexivity|split; [exact Ix|split; [|split; [exact N|]]]]).
    all: try (destruct (enters_tied_cell _ _ _ _ _ x Ok) as [E|(h1 & h2 & E1 & E2 & _)]; [rewrite E; exact Ib|]; rewrite E2; rewrite E1 in Ib; apply in_ids_ins; right; exact Ib).
    all: destruct (erf e x) as [u0|]; [|exact I].
    all: destruct (enters_tied_cell _ _ _ _ _ x Ok) as [E|(h1 & h2 & E1 & E2 & _)]; [rewrite E; exact M|]; rewrite E2; rewrite E1 in M; apply older_ins; exact M.
  - right; right. exists (sete t e). rewrite nth_setew, L. cbn [option_map]. unfold sete.
    destruct (Nat.eqb (et e) t); cbn [eQ]; auto.
Qed.

Lemma stepWB_gedge : forall p s s', stepWB p s s' -> forall a b, gedge s a b -> gedge s' a b.
Proof.
  intros p s s' H a b G. inversion H as [s0 s1 St _ | s0 s1 c k t1 H'' St _ _ Ok | s0 c k t1 xs H'' _ _ _ _ _ _ _ Ok]; subst.
  - exact (grows_gedge _ _ (step_grows p s s' St) a b G).
  - apply (wbst_grows s1 c k t1 H'' Ok). exact (grows_gedge _ _ (step_grows p s s1 St) a b G).
  - apply (wbst_grows s c k t1 H'' Ok). exact G.
Qed.

Lemma stepWB_cov : forall p s s', stepWB p s s' -> forall V, vsub (cov s V) (cov s' V).
Proof. intros p s s' H V. apply cov_grow. exact (stepWB_gedge p s s' H). Qed.
Lemma stepWB_pth : forall p s s', stepWB p s s' -> forall a b, Pth s a b -> Pth s' a b.
Proof.
  intros p s s' H a b P. unfold Pth in *. induction P as [a b G|a b c' _ IH1 _ IH2];
    [constructor; exact (stepWB_gedge p s s' H a b G)|exact (t_trans _ _ a b c' IH1 IH2)].
Qed.
