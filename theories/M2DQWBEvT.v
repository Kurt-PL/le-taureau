(* evok by time on a run of the write-back model (M2EvTimeProof.evok_time on runWB).
   VB: every view of a state names only writes before its time, and what a log entry knows in
   order (eQ, eQc) or took (erf) is no later than the entry.  It holds on every runWB (each step
   of M2DQ adds one entry, with views built from the old ones and the new time; a write-back store
   adds its id, earlier than the state's time).  So with the rank "time" only the histories, the
   reads that missed newer writes and a context's own order on a cell are left to check, as for
   evok_time on a run of A.  The same invariant gives done by tp (done_tpWB, as done_tp). *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Inv M2Ev M2DQ M2DQWBQ M2DQWBPatch M2DQWB.
Require M2Lit.

Record VB (s : st) : Prop := {
  vb_c : forall c y, vP (cs s c) y \/ vA (cs s c) y \/ vR (cs s c) y \/ vO (cs s c) y \/ vOg (cs s c) y -> y < tm s;
  vb_G : forall y, vG s y -> y < tm s;
  vb_wc : forall w y, wc s w y -> y < tm s;
  vb_hs : forall x y, In y (ids (hs s x)) -> y < tm s;
  vb_rw : forall c k x y, rw (cs s c) k x = Some y -> y < tm s;
  vb_oh : forall c k y, oh (cs s c) k = Some y -> y < tm s;
  vb_len : tm s = length (lg s);
  vb_ent : forall b e, nth_error (lg s) b = Some e ->
    (forall a, eQ e a \/ eQc e a -> a <= b) /\ (forall x a, erf e x = Some a -> a <= b);
  vb_tp : forall c j, tp s c <= j -> oc (cs s c) j = None /\ oh (cs s c) j = None }.

Lemma VB_init : VB sinit.
Proof.
  constructor; cbn; try contradiction; try discriminate; try reflexivity.
  - intros c y H. unfold vnil in H. tauto.
  - intros b e E. destruct b; discriminate.
  - intros c j _. split; reflexivity.
Qed.

(* ---------- what an instruction does to the views ---------- *)
Definition MB (m : mst) (T : nat) : Prop :=
  (forall y, mP m y \/ mA m y \/ mR m y \/ mG m y \/ mW m y -> y < T) /\ (forall w y, mC m w y -> y < T) /\
  (forall x y, In y (ids (mH m x)) -> y < T).

Lemma takes_lt : forall H xs u T, takes H xs u -> (forall x y, In y (ids (H x)) -> y < T) ->
  forall x y, u x = Some y -> y < T.
Proof.
  intros H xs u T [A B] Hb x y E. destruct (in_dec Nat.eq_dec x xs) as [I|N].
  - specialize (A x I). rewrite E in A. exact (Hb x y A).
  - rewrite (B x N) in E. discriminate.
Qed.

Lemma places_ids : forall H xs t H', places H xs t H' -> forall x y, In y (ids (H' x)) -> y = t \/ In y (ids (H x)).
Proof.
  intros H xs t H' P x y I. destruct (P x) as [A B]. destruct (in_dec Nat.eq_dec x xs) as [Ix|N].
  - destruct (A Ix) as (h1 & h2 & E1 & E2). rewrite E2 in I. rewrite E1. unfold ids in *. rewrite map_app in *.
    cbn [map fst] in I. apply in_app_iff in I. destruct I as [I|[I|I]].
    + right. apply in_app_iff. left. exact I.
    + left. symmetry. exact I.
    + right. apply in_app_iff. right. exact I.
  - rewrite (B N) in I. right. exact I.
Qed.

Lemma enters_tied_ids : forall u H xs t H', enters_tied u H xs t H' ->
  forall x y, In y (ids (H' x)) -> y = t \/ In y (ids (H x)).
Proof.
  intros u H xs t H' P x y I. destruct (P x) as [A B]. destruct (in_dec Nat.eq_dec x xs) as [Ix|N].
  - destruct (A Ix) as (h1 & h2 & E1 & _ & _ & E2). rewrite E2 in I. rewrite E1. unfold ids in *. rewrite map_app in *.
    cbn [map fst] in I. apply in_app_iff in I. destruct I as [I|[I|I]].
    + right. apply in_app_iff. left. exact I.
    + left. symmetry. exact I.
    + right. apply in_app_iff. right. exact I.
  - rewrite (B N) in I. right. exact I.
Qed.

Ltac crush := repeat match goal with
  | H : _ \/ _ |- _ => destruct H
  | H : _ /\ _ |- _ => destruct H
  | H : exists _, _ |- _ => destruct H
  | H : vone _ _ |- _ => unfold vone in H; subst
  | H : vnil _ |- _ => destruct H
  end.

Lemma eff_MB : forall t i r m m' a K u w, eff t i r m m' a K u w -> MB m t ->
  MB m' (S t) /\ (forall x y, u x = Some y -> y < t).
Proof.
  intros t i r m m' a K u w E (V & C & Hh).
  assert (Ht : forall xs u, takes (mH m) xs u -> forall x y, u x = Some y -> y < t)
    by (intros xs u0 Tk; exact (takes_lt _ _ _ _ Tk Hh)).
  assert (Ns : forall x y, nosrc x = Some y -> y < t) by (intros x y N; discriminate).
  inversion E; subst; (split; [|first [exact Ns|eapply Ht; eassumption]]);
    unfold MB, learn, wput, gpre, gpost, vor, srcs, carrieds, upd in *; cbn [mP mA mR mG mW mC mH] in *.
  all: try match goal with Pl : places _ _ _ ?H' |- _ => pose proof (places_ids _ _ _ _ Pl) as PI end.
  all: split; [|split].
  all: intros; repeat match goal with H : context [Nat.eqb ?a ?b] |- _ => destruct (Nat.eqb a b) end; crush; try subst.
  all: try lia.
  all: try match goal with I : In ?y (ids (?H' ?x)), PI : forall x y, In y (ids (?H' x)) -> _ |- _ =>
             destruct (PI x y I) as [->|I']; [lia|pose proof (Hh x y I'); lia] end.
  all: try match goal with |- ?y < _ => first
         [ assert (y < t) by (apply V; tauto); lia
         | assert (y < t) by (eapply C; eassumption); lia
         | assert (y < t) by (eapply Hh; eassumption); lia
         | assert (y < t) by (eapply Ht; eassumption); lia ] end.
Qed.

Lemma MB_mof : forall s c, VB s -> MB (mof s c) (tm s).
Proof.
  intros s c B. unfold MB, mof. cbn [mP mA mR mG mW mC mH]. split; [|split].
  - intros y H. destruct H as [H|[H|[H|[H|(e & E & _)]]]];
      [apply (vb_c s B c y); tauto|apply (vb_c s B c y); tauto|apply (vb_c s B c y); tauto|exact (vb_G s B y H)|].
    rewrite (vb_len s B). apply nth_error_Some. congruence.
  - exact (vb_wc s B).
  - exact (vb_hs s B).
Qed.

Lemma newO_lt : forall s c i m m' O T, MB m T -> MB m' T -> (forall y, O y -> y < T) ->
  forall y, newO s c i m m' O y -> y < T.
Proof.
  intros s c i m m' O T (V & _) (V' & _) Ho y. unfold newO, vor.
  destruct i as [| | |f|]; try exact (Ho y). destruct f; try exact (Ho y); intros H; crush; auto.
  all: first [apply V'; tauto|apply V; tauto].
Qed.

Lemma newOg_lt : forall i m' O T, MB m' T -> (forall y, O y -> y < T) -> forall y, newOg i m' O y -> y < T.
Proof.
  intros i m' O T (V' & _) Ho y. unfold newOg, vor.
  destruct i as [| | |f|]; try exact (Ho y). destruct f; try exact (Ho y); intros H; crush; auto.
  all: apply V'; tauto.
Qed.

(* the entry an access adds knows in order and took only writes before the step's time *)
Lemma newent_lt : forall s c i r u w, VB s -> (forall x y, u x = Some y -> y < tm s) ->
  (forall a, evQ s c i r (mof s c) (vOg (cs s c)) (vO (cs s c)) u w a \/ evQc i r (vO (cs s c)) w a -> a < tm s).
Proof.
  intros s c i r u w B U a H. unfold evQ, evQc, tookord, vor in H.
  destruct (w || _); destruct (is_load i && icond i r); crush;
    first [apply (vb_c s B c a); tauto|eapply U; eassumption].
Qed.

Lemma ent_last : forall (l : list oev) e b e0, nth_error (l ++ [e]) b = Some e0 ->
  (b < length l /\ nth_error l b = Some e0) \/ (b = length l /\ e0 = e).
Proof.
  intros l e b e0 E. destruct (Nat.lt_ge_cases b (length l)) as [L|L].
  - left. split; [exact L|]. rewrite nth_error_app1 in E by exact L. exact E.
  - right. rewrite nth_error_app2 in E by exact L. destruct (b - length l) as [|n] eqn:D.
    + cbn in E. split; [lia|congruence].
    + destruct n; discriminate.
Qed.

Section Evs.
Variables (s : st) (c k : nat) (i : instr) (m' : mst) (a : val) (K : view) (u : cell -> option nat) (w : bool).
Hypothesis B : VB s.
Hypothesis E : eff (tm s) i (rg (cs s c)) (mof s c) m' a K u w.

Let M := eff_MB _ _ _ _ _ _ _ _ _ E (MB_mof s c B).
Let M' := proj1 M.
Let U := proj2 M.
Let Mo : MB (mof s c) (S (tm s)).
Proof. destruct (MB_mof s c B) as (V & C & Hh). split; [|split]; intros; [apply V in H|apply C in H|apply Hh in H]; lia. Qed.

Lemma VB_evs : forall B' pc' tp' cm', (forall c0, tp s c0 <= tp' c0) -> k < tp' c ->
  VB (evs s c k i m' a K u w B' pc' tp' cm').
Proof.
  intros B' pc' tp' cm' Tp Tk. destruct M' as (V' & C' & H'). constructor; unfold evs; cbn [tm cs wc hs vG lg].
  - intros c0 y H. unfold upd in H. destruct (Nat.eqb c0 c); cbn [vP vA vR vO vOg] in H.
    + destruct H as [H|[H|[H|[H|H]]]]; [apply V'; tauto|apply V'; tauto|apply V'; tauto| |].
      * apply (newO_lt s c i (mof s c) m' (vO (cs s c)) (S (tm s)) Mo M'); [|exact H].
        intros y0 Y. pose proof (vb_c s B c y0 ltac:(tauto)). lia.
      * apply (newOg_lt i m' (vOg (cs s c)) (S (tm s)) M'); [|exact H].
        intros y0 Y. pose proof (vb_c s B c y0 ltac:(tauto)). lia.
    + pose proof (vb_c s B c0 y H). lia.
  - intros y H. apply V'. tauto.
  - exact C'.
  - exact H'.
  - intros c0 k0 x y H. unfold upd in H. destruct (Nat.eqb c0 c); cbn [rw] in H; [|pose proof (vb_rw s B _ _ _ _ H); lia].
    destruct (Nat.eqb k0 k); [|pose proof (vb_rw s B _ _ _ _ H); lia].
    unfold wrote in H. destruct w; [destruct (existsb _ _); [injection H as <-; lia|discriminate]|].
    pose proof (U x y H). lia.
  - intros c0 k0 y H. unfold upd in H. destruct (Nat.eqb c0 c); cbn [oh] in H; pose proof (vb_oh s B _ _ _ H); lia.
  - rewrite length_app, <- (vb_len s B). cbn. lia.
  - intros b e Eb. destruct (ent_last _ _ _ _ Eb) as [(L & Eo)|(Lb & ->)].
    + exact (vb_ent s B b e Eo).
    + rewrite <- (vb_len s B) in Lb. subst b. cbn [eQ eQc erf]. split.
      * intros a0 Q. pose proof (newent_lt s c i (rg (cs s c)) u w B U a0 Q). lia.
      * intros x a0 F. pose proof (U x a0 F). lia.
  - intros c0 j L. cbn [tp] in L. unfold upd. destruct (Nat.eqb_spec c0 c) as [->|N]; cbn [oc oh].
    + destruct (Nat.eqb_spec j k) as [->|_]; [lia|]. apply (vb_tp s B c j). pose proof (Tp c). lia.
    + apply (vb_tp s B c0 j). pose proof (Tp c0). lia.
Qed.

End Evs.

Lemma VB_sread : forall s c k xs B' m' a K u w bv, VB s ->
  eff (tm s) (ILd Plain xs (fun _ => true)) (rg (cs s c)) (mof s c) m' a K u w ->
  VB (sread s c k Plain xs B' m' a K u w bv).
Proof.
  intros s c k xs B' m' a K u w bv B E.
  destruct (eff_MB _ _ _ _ _ _ _ _ _ E (MB_mof s c B)) as [(V' & C' & H') U].
  constructor; unfold sread; cbn [tm cs wc hs vG lg].
  - intros c0 y H. unfold upd in H. destruct (Nat.eqb c0 c); cbn [vP vA vR vO vOg newO newOg] in H.
    + destruct H as [H|[H|[H|[H|H]]]]; try (apply V'; tauto); pose proof (vb_c s B c y ltac:(tauto)); lia.
    + pose proof (vb_c s B c0 y H). lia.
  - intros y H. apply V'. tauto.
  - exact C'.
  - exact H'.
  - intros c0 k0 x y H. unfold upd in H. destruct (Nat.eqb c0 c); cbn [rw] in H; [|pose proof (vb_rw s B _ _ _ _ H); lia].
    destruct (Nat.eqb k0 k); [|pose proof (vb_rw s B _ _ _ _ H); lia].
    unfold wrote in H. destruct w; [destruct (existsb _ _); [injection H as <-; lia|discriminate]|].
    pose proof (U x y H). lia.
  - intros c0 k0 y H. unfold upd in H. destruct (Nat.eqb c0 c); cbn [oh] in H; [|pose proof (vb_oh s B _ _ _ H); lia].
    destruct (Nat.eqb k0 k); [injection H as <-; lia|pose proof (vb_oh s B _ _ _ H); lia].
  - rewrite length_app, <- (vb_len s B). cbn. lia.
  - intros b e Eb. destruct (ent_last _ _ _ _ Eb) as [(L & Eo)|(Lb & ->)].
    + exact (vb_ent s B b e Eo).
    + rewrite <- (vb_len s B) in Lb. subst b. cbn [eQ eQc erf]. split.
      * intros a0 Q. pose proof (newent_lt s c _ (rg (cs s c)) u w B U a0 Q). lia.
      * intros x a0 F. pose proof (U x a0 F). lia.
  - intros c0 j L. cbn [tp] in L. unfold upd in L |- *. destruct (Nat.eqb_spec c0 c) as [->|N]; cbn [oc oh].
    + destruct (Nat.eqb_spec j k) as [->|_]; [lia|]. apply (vb_tp s B c j). lia.
    + exact (vb_tp s B c0 j L).
Qed.

(* a step that keeps time, log, histories and every view *)
Lemma VB_keep : forall s s', VB s -> tm s' = tm s -> wc s' = wc s -> hs s' = hs s -> vG s' = vG s -> lg s' = lg s ->
  tp s' = tp s -> (forall c, oc (cs s' c) = oc (cs s c)) ->
  (forall c, vP (cs s' c) = vP (cs s c) /\ vA (cs s' c) = vA (cs s c) /\ vR (cs s' c) = vR (cs s c) /\
     vO (cs s' c) = vO (cs s c) /\ vOg (cs s' c) = vOg (cs s c) /\ rw (cs s' c) = rw (cs s c) /\ oh (cs s' c) = oh (cs s c)) ->
  VB s'.
Proof.
  intros s s' B Tm Wc Hs G Lg Tp Oc Cs. constructor; rewrite ?Tm.
  - intros c y H. destruct (Cs c) as (A1 & A2 & A3 & A4 & A5 & _). rewrite A1, A2, A3, A4, A5 in H. exact (vb_c s B c y H).
  - rewrite G. exact (vb_G s B).
  - rewrite Wc. exact (vb_wc s B).
  - rewrite Hs. exact (vb_hs s B).
  - intros c k x y H. destruct (Cs c) as (_ & _ & _ & _ & _ & A6 & _). rewrite A6 in H. exact (vb_rw s B c k x y H).
  - intros c k y H. destruct (Cs c) as (_ & _ & _ & _ & _ & _ & A7). rewrite A7 in H. exact (vb_oh s B c k y H).
  - rewrite Lg. exact (vb_len s B).
  - rewrite Lg. exact (vb_ent s B).
  - intros c j L. rewrite Tp in L. rewrite Oc. destruct (Cs c) as (_ & _ & _ & _ & _ & _ & A7). rewrite A7. exact (vb_tp s B c j L).
Qed.

Ltac keep_oc := let c0 := fresh "c0" in intros c0; unfold scfail, scfix0, smatch, sskip; cbn [cs]; unfold upd;
  match goal with |- context [Nat.eqb c0 ?c] => destruct (Nat.eqb_spec c0 c) as [->|_] end; reflexivity.
Ltac keep_cs := let c0 := fresh "c0" in intros c0; unfold scfail, scfix0, smatch, sskip; cbn [cs]; unfold upd;
  match goal with |- context [Nat.eqb c0 ?c] => destruct (Nat.eqb_spec c0 c) as [->|_] end;
  cbn [vP vA vR vO vOg rw oh]; repeat split; reflexivity.

Lemma VB_scfail : forall s c k, VB s -> VB (scfail s c k).
Proof. intros s c k B. apply (VB_keep s); auto; [keep_oc|keep_cs]. Qed.

Lemma VB_scfix0 : forall s c j b B', VB s -> VB (scfix0 s c j b B').
Proof. intros s c j b B' B. apply (VB_keep s); auto; [keep_oc|keep_cs]. Qed.

Lemma VB_step : forall p s s', step p s s' -> VB s -> VB s'.
Proof.
  intros p s s' St B.
  destruct (step_cases p s s' St) as
    [(c & i & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & _ & _ & E & _ & ->)
    |[(c & k & d & B' & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & E & _ & ->)
    |[(c & d & _ & _ & _ & _ & _ & _ & ->)
    |[(c & k & xs & B' & m' & a & K & u & w & bv & _ & _ & _ & _ & _ & E & _ & ->)
    |[(c & _ & _ & _ & _ & _ & _ & _ & ->)
    |(c & j & b & B' & o & _ & _ & _ & ->)]]]]].
  - apply (VB_evs s c _ i m' a K u w B E); unfold upd;
      [intros c0; destruct (Nat.eqb_spec c0 c) as [->|_]; lia|rewrite Nat.eqb_refl; lia].
  - pose proof (VB_evs s c k (inst_of d) m' a K u w B E (bor (bd (cs s c)) B') (pcs s)
      (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s) ltac:(intros c0; unfold upd; destruct (Nat.eqb_spec c0 c) as [->|_]; lia)
      ltac:(unfold upd; rewrite Nat.eqb_refl; lia)) as V.
    unfold searly, set_es. apply (VB_keep _ _ V); reflexivity || (intros; repeat split; reflexivity).
  - apply (VB_keep s); auto; [keep_oc|keep_cs].
  - exact (VB_sread s c k xs B' m' a K u w bv B E).
  - (* sskip: the slot passed is below the new tp *)
    constructor; unfold sskip; cbn [tm cs wc hs vG lg tp].
    all: try (intros c0; unfold upd; destruct (Nat.eqb_spec c0 c) as [->|_]; cbn [vP vA vR vO vOg rw oh]; first [exact (vb_c s B c)|exact (vb_c s B c0)|exact (vb_rw s B c)|exact (vb_rw s B c0)|exact (vb_oh s B c)|exact (vb_oh s B c0)]).
    all: try exact (vb_G s B); try exact (vb_wc s B); try exact (vb_hs s B); try exact (vb_len s B); try exact (vb_ent s B).
    intros c0 j L. unfold upd in L |- *. destruct (Nat.eqb_spec c0 c) as [->|_]; cbn [oc oh]; apply (vb_tp s B); lia.
  - apply VB_scfix0. destruct o as [k|]; [destruct b; [exact B|exact (VB_scfail s c k B)]|exact B].
Qed.

Lemma VB_stepQ : forall p s s', stepQ p s s' -> VB s -> VB s'.
Proof.
  intros p s s' St B. destruct (stepQ_split p s s' St) as [[HA _]|RF]; [exact (VB_step p s s' HA B)|].
  apply (VB_keep s s' B (rfx_tm _ _ RF) (rfx_wc _ _ RF) (rfx_hs _ _ RF) (rfx_vG _ _ RF) (rfx_lg _ _ RF) (rfx_tp _ _ RF) (rfx_oc _ _ RF)).
  intros c. destruct RF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Cs).
  destruct (Cs c) as (_ & _ & A6 & _ & A1 & A2 & A3 & A4 & A5 & A7 & _). auto 10.
Qed.

(* a write-back store, with an id before the state's time *)
Lemma VB_wbst : forall s c k t H'', VB s -> t < tm s ->
  (forall x y, In y (ids (H'' x)) -> y = t \/ In y (ids (hs s x))) -> VB (wbst s c k t H'').
Proof.
  intros s c k t H'' B Lt Hh. constructor; unfold wbst; cbn [tm cs wc hs vG lg].
  - intros c0 y H. unfold upd in H. destruct (Nat.eqb c0 c); cbn [vP vA vR vO vOg] in H; [|exact (vb_c s B c0 y H)].
    unfold vor, vone in H. destruct H as [[H| ->]|H]; [apply (vb_c s B c y); tauto|exact Lt|apply (vb_c s B c y); tauto].
  - exact (vb_G s B).
  - intros w y H. unfold upd in H. destruct (Nat.eqb w t); [|exact (vb_wc s B w y H)].
    unfold vor, vone in H. destruct H as [H| ->]; [apply (vb_c s B c y); tauto|exact Lt].
  - intros x y I. destruct (Hh x y I) as [->|I']; [exact Lt|exact (vb_hs s B x y I')].
  - intros c0 k0 x y H. unfold upd in H. destruct (Nat.eqb c0 c); cbn [rw] in H; [|exact (vb_rw s B _ _ _ _ H)].
    destruct (Nat.eqb k0 k); [unfold wbrw in H; destruct (existsb (Nat.eqb x) (icells (ai (cs s c) k))); [injection H as <-; exact Lt|]|]; exact (vb_rw s B _ _ _ _ H).
  - intros c0 k0 y H. unfold upd in H. destruct (Nat.eqb c0 c); cbn [oh] in H; exact (vb_oh s B _ _ _ H).
  - unfold setew. rewrite length_map. exact (vb_len s B).
  - intros b e Eb. unfold setew in Eb. rewrite nth_error_map in Eb.
    destruct (nth_error (lg s) b) as [e0|] eqn:E0; [|discriminate]. cbn in Eb. injection Eb as <-.
    destruct (vb_ent s B b e0 E0) as [Q F]. destruct (Nat.eqb (et e0) t); cbn [eQ eQc erf]; split; assumption.
  - intros c0 j L. cbn [tp] in L. unfold upd. destruct (Nat.eqb_spec c0 c) as [->|_]; cbn [oc oh]; exact (vb_tp s B _ j L).
Qed.

Theorem VB_runWB : forall p s, runWB p s -> VB s.
Proof.
  intros p s R. induction R as [|s s' R IH H]; [exact VB_init|].
  destruct H as [s s' St _|s s' c k t1 H'' St Ps _ Wo|s c k t1 xs H'' _ _ Oh _ _ _ _ Wo].
  - exact (VB_stepQ p s s' St IH).
  - destruct Ps as (_ & Tm & _ & _ & _ & Oh & _). apply VB_wbst; [exact (VB_stepQ p s s' St IH)| |].
    + rewrite Tm. exact (vb_oh s IH c k t1 Oh).
    + exact (enters_tied_ids _ _ _ _ _ Wo).
  - apply VB_wbst; [exact IH|exact (vb_oh s IH c k t1 Oh)|exact (enters_tied_ids _ _ _ _ _ Wo)].
Qed.

(* evok by time on a run of the write-back model *)
Theorem evok_timeWB : forall p s, runWB p s ->
  (forall x a b, older (hs s x) a b -> a < b) ->
  (forall a e x w, nth_error (lg s) a = Some e -> In x (eR e) -> In w (ids (hs s x)) -> w <> a ->
     match erf e x with None => True | Some u => older (hs s x) u w end -> a < w) ->
  (forall x a b ea eb, nth_error (lg s) a = Some ea -> nth_error (lg s) b = Some eb -> ec ea = ec eb ->
     ek ea < ek eb -> In x (eC ea) -> In x (eC eb) -> a < b) ->
  evok s.
Proof.
  intros p s R Hh Hn Hp. pose proof (VB_runWB p s R) as B.
  apply (evok_rank s (fun a => a)).
  - intros a b [(x & Ol)|[(e & x & L & Ix & Ib & N & M)|(e & L & Q & N)]].
    + exact (Hh x a b Ol).
    + exact (Hn a e x b L Ix Ib N M).
    + pose proof (proj1 (vb_ent s B b e L) a (or_introl Q)). lia.
  - intros x a b [Ol|[(e & L & Ix & Ib & N & M)|[(e & L & Ix & Ef & N)|[(e & L & Ix & Q & Ib & N)|(ea & eb & La & Lb & C & K & Xa & Xb)]]]].
    + exact (Hh x a b Ol).
    + exact (Hn a e x b L Ix Ib N M).
    + pose proof (proj2 (vb_ent s B b e L) x a Ef). lia.
    + pose proof (proj1 (vb_ent s B b e L) a Q). lia.
    + exact (Hp x a b ea eb La Lb C K Xa Xb).
Qed.

(* a finished run of the write-back model, by tp (as M2EvTimeProof.done_tp) *)
Lemma done_tpWB : forall P s, runWB (M2Lit.stat P) s ->
  (forall c, c < length P -> length (nth c P []) <= pcs s c /\ tp s c <= pcs s c) -> done (M2Lit.stat P) s.
Proof.
  intros P s R H. exists (fun c => length (nth c P [])). split; [apply M2Lit.stat_fin|].
  intros c Hc. unfold M2Lit.stat in Hc. rewrite length_map in Hc. destruct (H c Hc) as [A B]. split; [exact A|].
  intros k Hk. apply (vb_tp s (VB_runWB _ s R) c k). lia.
Qed.

Print Assumptions evok_timeWB.
Print Assumptions done_tpWB.
