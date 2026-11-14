(* Part 9: what the steps keep of the log and of guard() events, for the premises of
   KR's preservation (an access follows its guard(), and every store is at a time Good). *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB M2DQWBK1 M2DQWBK2 M2DQWBK3 M2DQWBK7.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQShim.

Definition HB1 (Good : nat -> Prop) (s : st) : Prop := forall t e, ent s t = Some e -> Good t -> LFB s (ec e) t.
Definition HB2 (Good : nat -> Prop) (s : st) : Prop := forall t e, ent s t = Some e -> ew e = true -> eC e <> [] -> Good t.

(* an LFB of a later state, for an earlier time, holds in the earlier state when the old entries
   and the old guard() events are the same *)
Lemma LFB_from : forall s s' c t, t <= tm s ->
  (forall t' e, t' < tm s -> ent s' t' = Some e -> ent s t' = Some e) ->
  (forall t' e, ent s t' = Some e -> exists e', ent s' t' = Some e' /\ ec e' = ec e /\ eh e' = eh e /\ (ew e' = false -> ew e = false)) ->
  (forall tf f, ent s tf = Some f -> isFF s' tf f -> isFF s tf f) ->
  LFB s' c t -> LFB s c t.
Proof.
  intros s s' c t Lt He Hs Hf (tg & g & L & Eg & Ec & F & Lt').
  assert (Eg' : ent s tg = Some g) by (apply He; [lia|exact Eg]).
  exists tg, g. split; [exact L|split; [exact Eg'|split; [exact Ec|split; [exact (Hf tg g Eg' F)|]]]].
  intros t' e' L1 L2 E C. destruct (Hs t' e' E) as (e2 & E2 & C2 & H2 & W2).
  destruct (Lt' t' e2 L1 L2 E2 ltac:(congruence)) as [A B]. split; [congruence|exact (W2 B)].
Qed.

Lemma ent_evsx : forall s c k i m' a K u w B pc' tp' cm' es' t, tm s = length (lg s) ->
  ent (evsx s c k i m' a K u w B pc' tp' cm' es') t =
  if Nat.ltb t (tm s) then ent s t else if Nat.eqb t (tm s) then
    Some (mkO (tm s) c k K u w (evC i (rg (cs s c))) (evR i (rg (cs s c)))
       (evQ s c i (rg (cs s c)) (mof s c) (vOg (cs s c)) (vO (cs s c)) u w) (evQc i (rg (cs s c)) (vO (cs s c)) w) false)
  else None.
Proof. intros. unfold ent, evsx. cbv zeta. cbn [lg]. rewrite nth_error_app_last. rewrite <- H. reflexivity. Qed.

Lemma ent_sread : forall s c k m xs B m' a K u w bv t, tm s = length (lg s) ->
  ent (sread s c k m xs B m' a K u w bv) t =
  if Nat.ltb t (tm s) then ent s t else if Nat.eqb t (tm s) then
    Some (mkO (tm s) c k K u w (evC (ILd m xs (fun _ => true)) (rg (cs s c))) (evR (ILd m xs (fun _ => true)) (rg (cs s c)))
       (evQ s c (ILd m xs (fun _ => true)) (rg (cs s c)) (mof s c) (vOg (cs s c)) (vO (cs s c)) u w)
       (evQc (ILd m xs (fun _ => true)) (rg (cs s c)) (vO (cs s c)) w) true)
  else None.
Proof. intros. unfold ent, sread. cbv zeta. cbn [lg]. rewrite nth_error_app_last. rewrite <- H. reflexivity. Qed.

Lemma ltb_old : forall t n, t < n -> Nat.ltb t n = true. Proof. intros. apply Nat.ltb_lt. exact H. Qed.

(* the guard() events of a logged step are the earlier state's, but for the new entry *)
Lemma isFF_evsx : forall s c k i m' a K u w B pc' tp' cm' es' tf f, tf < tm s -> oc (cs s c) k = None ->
  (forall c' j, j < pc' c' -> j < pcs s c' \/ (c' = c /\ j = k)) ->
  isFF (evsx s c k i m' a K u w B pc' tp' cm' es') tf f -> isFF s tf f.
Proof.
  intros s c k i m' a K u w B pc' tp' cm' es' tf f Lt Hoc Hpc2 (Fa & Fp & Fo). unfold evsx in Fa, Fp, Fo. cbv zeta in Fa, Fp, Fo.
  cbn [cs pcs] in Fa, Fp, Fo. rewrite cs_upd in Fa, Fo.
  destruct (Nat.eqb_spec (ec f) c) as [Ec|Nc]; cbn [oc ai] in Fa, Fo.
  - destruct (Nat.eqb_spec (ek f) k) as [Ek'|Nk].
    + exfalso. rewrite Ek', upd_eq in Fo. injection Fo as Fo. lia.
    + rewrite upd_neq in Fa by exact Nk. rewrite upd_neq in Fo by exact Nk. unfold isFF. rewrite Ec. rewrite Ec in Fp.
      destruct (Hpc2 c (ek f) Fp) as [L|[_ L]]; [|congruence]. auto.
  - unfold isFF. destruct (Hpc2 (ec f) (ek f) Fp) as [L|[L _]]; [|congruence]. auto.
Qed.

Lemma isFF_sread : forall s c k m xs B m' a K u w bv tf f, oc (cs s c) k = None ->
  isFF (sread s c k m xs B m' a K u w bv) tf f -> isFF s tf f.
Proof.
  intros s c k m xs B m' a K u w bv tf f Hoc (Fa & Fp & Fo). unfold sread in Fa, Fp, Fo. cbv zeta in Fa, Fp, Fo.
  cbn [cs pcs] in Fa, Fp, Fo. rewrite cs_upd in Fa, Fo.
  destruct (Nat.eqb_spec (ec f) c) as [Ec|Nc]; cbn [oc ai] in Fa, Fo.
  - destruct (Nat.eqb_spec (ek f) k) as [Ek'|Nk].
    + exfalso. rewrite Ek' in Fo. congruence.
    + rewrite upd_neq in Fa by exact Nk. unfold isFF. rewrite Ec. rewrite Ec in Fp. auto.
  - unfold isFF. auto.
Qed.

Lemma HB_evsx : forall Good s c k i m' a K u w B pc' tp' cm' es', tm s = length (lg s) -> oc (cs s c) k = None ->
  (forall c' j, j < pc' c' -> j < pcs s c' \/ (c' = c /\ j = k)) ->
  HB1 Good (evsx s c k i m' a K u w B pc' tp' cm' es') -> HB2 Good (evsx s c k i m' a K u w B pc' tp' cm' es') ->
  (Good (tm s) -> LFB s c (tm s)) /\ (w = true -> evC i (rg (cs s c)) <> [] -> Good (tm s)) /\ HB1 Good s /\ HB2 Good s.
Proof.
  intros Good s c k i m' a K u w B pc' tp' cm' es' Tl Hoc Hpc2 H1 H2.
  assert (Eo : forall t e, ent s t = Some e -> ent (evsx s c k i m' a K u w B pc' tp' cm' es') t = Some e).
  { intros t e E. rewrite ent_evsx by exact Tl. rewrite ltb_old; [exact E|]. rewrite Tl. unfold ent in E. apply nth_error_Some. congruence. }
  assert (Back : forall c' t, t <= tm s -> LFB (evsx s c k i m' a K u w B pc' tp' cm' es') c' t -> LFB s c' t).
  { intros c' t L B'. eapply (LFB_from s _ c' t L); [| | |exact B'].
    - intros t' e L' E. rewrite ent_evsx in E by exact Tl. rewrite (ltb_old _ _ L') in E. exact E.
    - intros t' e E. exists e. rewrite (Eo t' e E). auto.
    - intros tf f E F. apply (isFF_evsx s c k i m' a K u w B pc' tp' cm' es' tf f); auto.
      rewrite Tl. unfold ent in E. apply nth_error_Some. congruence. }
  assert (En : ent (evsx s c k i m' a K u w B pc' tp' cm' es') (tm s) = Some
    (mkO (tm s) c k K u w (evC i (rg (cs s c))) (evR i (rg (cs s c)))
       (evQ s c i (rg (cs s c)) (mof s c) (vOg (cs s c)) (vO (cs s c)) u w) (evQc i (rg (cs s c)) (vO (cs s c)) w) false)).
  { rewrite ent_evsx by exact Tl. rewrite Nat.ltb_irrefl, Nat.eqb_refl. reflexivity. }
  split; [intros G; apply Back; [lia|exact (H1 _ _ En G)]|].
  split; [intros Wt Ne; exact (H2 _ _ En Wt Ne)|].
  split.
  - intros t e E G. apply Back; [unfold ent in E; rewrite Tl; apply Nat.lt_le_incl; apply nth_error_Some; congruence|].
    exact (H1 t e (Eo t e E) G).
  - intros t e E W Ne. exact (H2 t e (Eo t e E) W Ne).
Qed.

Lemma HB_sread : forall Good s c k m xs B m' a K u w bv, tm s = length (lg s) -> oc (cs s c) k = None ->
  HB1 Good (sread s c k m xs B m' a K u w bv) -> HB2 Good (sread s c k m xs B m' a K u w bv) ->
  (Good (tm s) -> LFB s c (tm s)) /\ HB1 Good s /\ HB2 Good s.
Proof.
  intros Good s c k m xs B m' a K u w bv Tl Hoc H1 H2.
  assert (Eo : forall t e, ent s t = Some e -> ent (sread s c k m xs B m' a K u w bv) t = Some e).
  { intros t e E. rewrite ent_sread by exact Tl. rewrite ltb_old; [exact E|]. rewrite Tl. unfold ent in E. apply nth_error_Some. congruence. }
  assert (Back : forall c' t, t <= tm s -> LFB (sread s c k m xs B m' a K u w bv) c' t -> LFB s c' t).
  { intros c' t L B'. eapply (LFB_from s _ c' t L); [| | |exact B'].
    - intros t' e L' E. rewrite ent_sread in E by exact Tl. rewrite (ltb_old _ _ L') in E. exact E.
    - intros t' e E. exists e. rewrite (Eo t' e E). auto.
    - intros tf f E F. exact (isFF_sread s c k m xs B m' a K u w bv tf f Hoc F). }
  assert (En : exists e, ent (sread s c k m xs B m' a K u w bv) (tm s) = Some e /\ ec e = c).
  { rewrite ent_sread by exact Tl. rewrite Nat.ltb_irrefl, Nat.eqb_refl. eexists. split; reflexivity. }
  destruct En as (e & En & Ec).
  split; [intros G; apply Back; [lia|pose proof (H1 _ _ En G) as Q; rewrite Ec in Q; exact Q]|].
  split.
  - intros t e' E G. apply Back; [unfold ent in E; rewrite Tl; apply Nat.lt_le_incl; apply nth_error_Some; congruence|].
    exact (H1 t e' (Eo t e' E) G).
  - intros t e' E W Ne. exact (H2 t e' (Eo t e' E) W Ne).
Qed.

(* the same under a premise Fk *)
Lemma HB_evsxF : forall (Fk : Prop) Good s c k i m' a K u w B pc' tp' cm' es', tm s = length (lg s) -> oc (cs s c) k = None ->
  (forall c' j, j < pc' c' -> j < pcs s c' \/ (c' = c /\ j = k)) ->
  (Fk -> HB1 Good (evsx s c k i m' a K u w B pc' tp' cm' es')) -> (Fk -> HB2 Good (evsx s c k i m' a K u w B pc' tp' cm' es')) ->
  (Fk -> Good (tm s) -> LFB s c (tm s)) /\ (Fk -> w = true -> evC i (rg (cs s c)) <> [] -> Good (tm s)) /\ (Fk -> HB1 Good s) /\ (Fk -> HB2 Good s).
Proof.
  intros Fk Good s c k i m' a K u w B pc' tp' cm' es' T O P H1 H2.
  split; [|split; [|split]]; intros HF; destruct (HB_evsx Good s c k i m' a K u w B pc' tp' cm' es' T O P (H1 HF) (H2 HF)) as (A1 & A2 & A3 & A4); auto.
Qed.

Lemma HB_sreadF : forall (Fk : Prop) Good s c k m xs B m' a K u w bv, tm s = length (lg s) -> oc (cs s c) k = None ->
  (Fk -> HB1 Good (sread s c k m xs B m' a K u w bv)) -> (Fk -> HB2 Good (sread s c k m xs B m' a K u w bv)) ->
  (Fk -> Good (tm s) -> LFB s c (tm s)) /\ (Fk -> HB1 Good s) /\ (Fk -> HB2 Good s).
Proof.
  intros Fk Good s c k m xs B m' a K u w bv T O H1 H2.
  split; [|split]; intros HF; destruct (HB_sread Good s c k m xs B m' a K u w bv T O (H1 HF) (H2 HF)) as (A1 & A2 & A3); auto.
Qed.
