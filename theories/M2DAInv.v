(* Generic facts of M2DA's model (runD): a CAS whose slot happened (oc)
   succeeded; oc is never undone; oc times are below tm; is_cas of the
   instruction at a happened slot is kept. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Inv M2DA.

(* ---------- what s_cfix changes ---------- *)
Section Fix.
Variables (s : st) (c j : nat) (b : bool) (B : nat -> bool) (o : option nat).
Let s' := scfix0 (sflp s c o b) c j b B.

Lemma fx_cs_same : forall c' k, oc (cs s' c') k = oc (cs s c') k /\ ai (cs s' c') k = ai (cs s c') k /\
  oh (cs s' c') k = oh (cs s c') k.
Proof.
  intros c' k. unfold s', scfix0, sflp. destruct o as [k0|]; [destruct b|];
    unfold scfail; cbn [cs]; destruct (Nat.eq_dec c' c) as [->|N];
    rewrite ?upd_o, ?upd_n by exact N; cbn [oc ai oh]; rewrite ?upd_o, ?upd_n by exact N; auto.
Qed.

Lemma fx_glob : pcs s' = pcs s /\ tm s' = tm s /\ hs s' = hs s.
Proof. unfold s', scfix0, sflp. destruct o; [destruct b|]; unfold scfail; cbn; auto. Qed.

Lemma fx_rg : forall c' k, (c' <> c \/ o <> Some k \/ b = true) -> rg (cs s' c') k = rg (cs s c') k.
Proof.
  intros c' k H. unfold s', scfix0, sflp. destruct o as [k0|]; [destruct b|];
    unfold scfail; cbn [cs]; destruct (Nat.eq_dec c' c) as [->|N];
    rewrite ?upd_o, ?upd_n by exact N; cbn [rg]; rewrite ?upd_o, ?upd_n by exact N; auto.
  unfold upd. destruct (Nat.eqb_spec k k0) as [->|]; auto. exfalso. destruct H as [H|[H|H]]; congruence.
Qed.
End Fix.

(* the record a fix names has not happened (oc) *)
Lemma cfix_rec : forall p c cc pc N j b B k, cfix_ok p c cc pc N j b B (Some k) -> oc cc k = None.
Proof.
  intros p c cc pc N j b B k (v & H). destruct (H (fun _ _ => 0)) as (_ & _ & _ & Hp & _).
  unfold hpend_at in Hp. apply find_some' in Hp as (_ & F). destruct (oc cc k); [discriminate|reflexivity].
Qed.

Ltac lets := repeat match goal with x := _ |- _ => subst x end.

(* ---------- oc is kept, with its time; is_cas of a happened slot is kept ---------- *)
Lemma step_keep : forall p s s' c k t, step p s s' -> oc (cs s c) k = Some t ->
  oc (cs s' c) k = Some t /\ is_cas (ai (cs s' c) k) = is_cas (ai (cs s c) k) /\ tm s <= tm s'.
Proof.
  intros p s s' c' k' t S O. destruct S; lets.
  1-7: cbn [cs tm]; destruct (Nat.eq_dec c' c) as [->|N]; [|rewrite !upd_n by exact N; auto].
  all: try (rewrite upd_o; cbn [oc ai]).
  - (* ord *) assert (k' <> pcs s c) by congruence. rewrite !upd_n by auto. auto.
  - (* skip *) assert (k' <> pcs s c) by congruence. rewrite !upd_n by auto. auto.
  - (* early *) assert (k' <> k) by congruence. rewrite !upd_n by auto. auto.
  - (* match *) split; [auto|split; [|auto]]. unfold upd. destruct (Nat.eqb_spec k' (pcs s c)) as [->|]; [|reflexivity].
    match goal with X : eof _ _ = Some ?d, Y : ai _ _ = inst_of ?d |- _ =>
      rewrite Y; symmetry; exact (proj1 (eof_cexp _ _ _ (fun _ => 0) X)) end.
  - (* cread *) assert (k' <> k) by congruence. rewrite !upd_n by auto. split; [auto|split; [auto|lia]].
  - (* cw *) assert (k' <> pcs s c) by congruence. rewrite !upd_n by auto. auto.
  - (* cwe *) assert (k' <> k) by congruence. rewrite !upd_n by auto. auto.
  - (* cfix *) destruct (fx_cs_same s c j b B o c' k') as (A & Bq & _). destruct (fx_glob s c j b B o) as (_ & T & _).
    rewrite A, Bq, T. auto.
Qed.

(* ---------- oc times are below tm ---------- *)
Definition TB (s : st) : Prop := forall c k t, oc (cs s c) k = Some t -> t < tm s.

Lemma TB_step : forall p s s', TB s -> step p s s' -> TB s'.
Proof.
  intros p s s' I S c' k' t' O. destruct S; lets.
  1-7: cbn [cs tm] in *; destruct (Nat.eq_dec c' c) as [->|N]; [|rewrite !upd_n in O by exact N; pose proof (I c' k' t' O); lia].
  all: try (rewrite upd_o in O; cbn [oc] in O).
  all: try (match type of O with upd _ ?x _ _ = _ => unfold upd in O; destruct (Nat.eqb k' x);
              [injection O as <-; lia|pose proof (I _ _ _ O); lia] end).
  all: try (pose proof (I _ _ _ O); lia).
  destruct (fx_cs_same s c j b B o c' k') as (A & _). destruct (fx_glob s c j b B o) as (_ & T & _).
  rewrite A in O. rewrite T. exact (I _ _ _ O).
Qed.

(* ---------- a CAS whose slot happened succeeded (M2DA: in parts only) ---------- *)
Definition VK (s : st) : Prop :=
  forall c k, oc (cs s c) k <> None -> is_cas (ai (cs s c) k) = true -> vok (rg (cs s c) k) = true.

Lemma eff_cas_w : forall t i r m m' a K u, is_cas i = true -> eff t i r m m' a K u true -> vok a = true.
Proof. intros t i r m m' a K u C E. inversion E; subst; try discriminate. apply vok_vd. Qed.

Lemma VK_step : forall p s s', VK s -> step p s s' -> nowhole s s' -> VK s'.
Proof.
  intros p s s' I S NW c' k' O C. destruct S; lets.
  1-7: cbn [cs] in *; destruct (Nat.eq_dec c' c) as [->|N]; [|rewrite !upd_n in * by exact N; apply I; auto].
  all: try (rewrite upd_o in *; cbn [oc ai rg] in *).
  - (* ord: a CAS in order as a whole is not a step of M2DA *)
    destruct (Nat.eq_dec k' (pcs s c)) as [->|Nk]; [|rewrite !upd_n in * by exact Nk; apply I; auto].
    exfalso. apply (NW c (pcs s c)); auto; cbn [cs]; rewrite upd_o; cbn [oc ai]; rewrite upd_o; [discriminate|first [exact C|rewrite upd_o in C; exact C]].
  - (* skip *)
    destruct (Nat.eq_dec k' (pcs s c)) as [->|Nk]; [contradiction|rewrite !upd_n in * by exact Nk; apply I; auto].
  - (* early *)
    destruct (Nat.eq_dec k' k) as [->|Nk]; [|rewrite !upd_n in * by exact Nk; apply I; auto].
    exfalso. apply (NW c k); auto; cbn [cs]; rewrite upd_o; cbn [oc ai]; rewrite upd_o; [discriminate|first [exact C|rewrite upd_o in C; exact C]].
  - (* match *)
    destruct (Nat.eq_dec k' (pcs s c)) as [->|Nk]; [|rewrite !upd_n in * by exact Nk; apply I; auto].
    rewrite upd_o in C. apply I; auto.
    match goal with X : eof _ _ = Some ?d, Y : ai _ _ = inst_of ?d |- _ =>
      rewrite Y; rewrite (proj1 (eof_cexp _ _ _ (fun _ => 0) X)); exact C end.
  - (* cread *)
    destruct (Nat.eq_dec k' k) as [->|Nk]; [contradiction|rewrite !upd_n in * by exact Nk; apply I; auto].
  - (* cw *)
    destruct (Nat.eq_dec k' (pcs s c)) as [->|Nk]; [|rewrite !upd_n in * by exact Nk; apply I; auto].
    rewrite upd_o. subst. eapply eff_cas_w; [|eassumption]. rewrite upd_o in C. exact C.
  - (* cwe *)
    destruct (Nat.eq_dec k' k) as [->|Nk]; [|rewrite !upd_n in * by exact Nk; apply I; auto].
    rewrite upd_o. subst. eapply eff_cas_w; [|eassumption]. rewrite upd_o in C. exact C.
  - (* cfix *)
    destruct (fx_cs_same s c j b B o c' k') as (A & Bq & _). rewrite A in O. rewrite Bq in C.
    rewrite fx_rg; [apply I; auto|].
    destruct (Nat.eq_dec c' c) as [->|N]; [|left; exact N]. right.
    destruct o as [k0|]; [|left; discriminate].
    destruct (Nat.eq_dec k0 k') as [->|Nk]; [|left; congruence].
    exfalso. apply O. eapply cfix_rec. eassumption.
Qed.

Lemma VK_run : forall p s, runD p s -> VK s /\ TB s.
Proof.
  intros p s R. induction R as [|s s' R IH S NW].
  - split; [intros c k O; exfalso; apply O; reflexivity|intros c k t O; discriminate O].
  - destruct IH as [I T]. split; [eapply VK_step; eauto|eapply TB_step; eauto].
Qed.

Print Assumptions VK_run.
Print Assumptions step_keep.
