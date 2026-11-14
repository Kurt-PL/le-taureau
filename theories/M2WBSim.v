(* Write-back, part 4: every step of A, taken in sW, is taken in sA. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Cont M2WBReg M2WBRel M2WBEff.

Lemma in_ids_hers_ins : forall h1 h2 t w, In w (ids (hers (h1 ++ h2))) -> In w (ids (hers (h1 ++ (t, false) :: h2))).
Proof.
  intros h1 h2 t w I. rewrite hers_app in I. rewrite hers_ins_f. rewrite ids_app in I |- *. simpl.
  rewrite in_app_iff in I |- *. simpl. tauto.
Qed.

(* the places of a write, per cell: unchanged, or the write inserted *)
Lemma places_cell : forall H xs t H' x, places H xs t H' ->
  H' x = H x \/ exists h1 h2, H x = h1 ++ h2 /\ H' x = h1 ++ (t, false) :: h2.
Proof.
  intros H xs t H' x P. destruct (P x) as [P1 P2]. destruct (in_dec Nat.eq_dec x xs) as [I|N].
  - right. destruct (P1 I) as (h1 & h2 & E1 & E2). exists h1, h2. auto.
  - left. apply P2. exact N.
Qed.

Section Mem.
Variables (sw : nat -> option (cell -> option nat)) (sW sA : st).
Hypothesis R : rel sw sW sA.
Variables (m' m'A : mst).
Hypothesis Hh : forall x, mH m'A x = hers (mH m' x).
Hypothesis Hs : (mV m' = wv sW /\ mV m'A = wv sA /\ forall x, mH m' x = hs sW x) \/
  exists V xs, mV m' = upd (wv sW) (tm sW) V /\ mV m'A = upd (wv sA) (tm sW) V /\ places (hs sW) xs (tm sW) (mH m').
Hypothesis FH : forall x h1 h2, hs sW x = h1 ++ h2 -> mH m' x = h1 ++ (tm sW, false) :: h2 -> free_head h2.

Lemma tmA_ids : forall x w, In w (ids (hs sA x)) -> w < tm sW.
Proof.
  intros x w I. rewrite (r_hs sw sW sA R x) in I. apply (i_ids sw sW sA R x). apply in_ids_hers. exact I.
Qed.

(* the entries of the new history: the old ones, and perhaps the new write *)
Lemma new_hist : forall x e, In e (mH m' x) -> In e (hs sW x) \/ e = (tm sW, false).
Proof.
  intros x e I. destruct Hs as [(_ & _ & E)|(V & xs & _ & _ & P)].
  - left. rewrite <- E. exact I.
  - destruct (places_cell _ _ _ _ x P) as [E|(h1 & h2 & E1 & E2)].
    + left. rewrite <- E. exact I.
    + rewrite E2 in I. rewrite E1. apply in_app_iff in I. destruct I as [I|[I|I]].
      * left. apply in_app_iff. left. exact I.
      * right. symmetry. exact I.
      * left. apply in_app_iff. right. exact I.
Qed.

Lemma old_wv : forall x w, In w (ids (hs sW x)) -> mV m' w x = wv sW w x /\ mV m'A w x = wv sA w x.
Proof.
  intros x w I. pose proof (i_ids sw sW sA R x w I) as L. destruct Hs as [(E1 & E2 & _)|(V & xs & E1 & E2 & _)].
  - rewrite E1, E2. auto.
  - rewrite E1, E2. unfold upd. destruct (Nat.eqb_spec w (tm sW)); [lia|]. auto.
Qed.

Lemma mem_kept : forall x w, In (w, false) (mH m' x) -> sw w = None /\ mV m'A w x = mV m' w x.
Proof.
  intros x w I. destruct (new_hist x _ I) as [O|E].
  - assert (Iw : In w (ids (hs sW x))) by (unfold ids; apply in_map_iff; exists (w, false); auto).
    destruct (old_wv x w Iw) as [V1 V2]. destruct (r_kept sw sW sA R x w O) as [K1 K2]. rewrite V1, V2. auto.
  - injection E as ->. split; [apply (i_sw sw sW sA R); lia|].
    destruct Hs as [(E1 & E2 & E3)|(V & xs & E1 & E2 & P)].
    + exfalso. assert (Iw : In (tm sW) (ids (hs sW x))) by (rewrite <- E3; unfold ids; apply in_map_iff; exists (tm sW, false); auto).
      pose proof (i_ids sw sW sA R x _ Iw). lia.
    + rewrite E1, E2. unfold upd. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma mem_wb : forall x w, In (w, true) (mH m' x) -> exists f, sw w = Some f /\ mV m' w x = rdv (mV m'A) (f x) x /\
  (forall w', f x = Some w' -> In w' (ids (mH m'A x))).
Proof.
  intros x w I. destruct (new_hist x _ I) as [O|E]; [|discriminate].
  assert (Iw : In w (ids (hs sW x))) by (unfold ids; apply in_map_iff; exists (w, true); auto).
  destruct (r_wb sw sW sA R x w O) as (f & Sf & V & M). exists f. split; [exact Sf|].
  assert (M0 : forall w', f x = Some w' -> In w' (ids (hs sW x))) by (intros w' Ew; apply in_ids_hers; rewrite <- (r_hs sw sW sA R x); apply M; exact Ew).
  destruct (old_wv x w Iw) as [V1 _]. split.
  - rewrite V1, V. unfold rdv. cbn [wv]. destruct (f x) as [w'|] eqn:Ef; [|reflexivity].
    destruct (old_wv x w' (M0 w' eq_refl)) as [_ V2]. rewrite V2. reflexivity.
  - intros w' Ew. rewrite Hh. rewrite (r_hs sw sW sA R x) in M. specialize (M w' Ew).
    destruct Hs as [(_ & _ & E3)|(V3 & xs & _ & _ & P)].
    + rewrite E3. exact M.
    + destruct (places_cell _ _ _ _ x P) as [E4|(h1 & h2 & E1 & E2)].
      * rewrite E4. exact M.
      * rewrite E2. rewrite E1 in M. apply in_ids_hers_ins. exact M.
Qed.
Lemma mem_ids : forall x w, In w (ids (mH m' x)) -> w < S (tm sW).
Proof.
  intros x w I. unfold ids in I. apply in_map_iff in I. destruct I as ([w0 b] & E & I). simpl in E. subst w0.
  destruct (new_hist x _ I) as [O|E]; [|injection E as ->; lia].
  assert (Iw : In w (ids (hs sW x))) by (unfold ids; apply in_map_iff; exists (w, b); auto).
  pose proof (i_ids sw sW sA R x w Iw). lia.
Qed.

Lemma mem_adj : forall x, hadj (fun w => mV m' w x) 0 (mH m' x).
Proof.
  intros x. destruct Hs as [(E1 & E2 & E3)|(V & xs & E1 & E2 & P)].
  - rewrite E3, E1. apply (r_adj sw sW sA R x).
  - assert (Ext : forall w, In w (ids (hs sW x)) -> wv sW w x = mV m' w x).
    { intros w I. pose proof (i_ids sw sW sA R x w I). rewrite E1. unfold upd. destruct (Nat.eqb_spec w (tm sW)); [lia|reflexivity]. }
    destruct (places_cell _ _ _ _ x P) as [E4|(h1 & h2 & E5 & E6)].
    + rewrite E4. apply (hadj_ext (fun w => wv sW w x) (fun w => mV m' w x)); [exact Ext|apply (r_adj sw sW sA R x)].
    + rewrite E6. apply (hadj_ins (fun w => wv sW w x) (fun w => mV m' w x) h1 h2 (tm sW) false 0).
      * rewrite <- E5. exact Ext.
      * rewrite <- E5. apply (r_adj sw sW sA R x).
      * exact (FH x h1 h2 E5 E6).
      * intros Hb. discriminate.
Qed.
Lemma mem_old : forall x w, In w (ids (hs sW x)) -> In w (ids (mH m' x)).
Proof.
  intros x w I. destruct Hs as [(_ & _ & E3)|(V & xs & _ & _ & P)].
  - rewrite E3. exact I.
  - destruct (places_cell _ _ _ _ x P) as [E4|(h1 & h2 & E5 & E6)].
    + rewrite E4. exact I.
    + rewrite E6. rewrite E5 in I. apply in_ids_ins. right. exact I.
Qed.
End Mem.

Lemma upd_cs_crel : forall sw (cW cA : nat -> cst) c ccW' ccA', (forall c', crel sw (cW c') (cA c')) -> crel sw ccW' ccA' ->
  forall c', crel sw (upd cW c ccW' c') (upd cA c ccA' c').
Proof. intros sw cW cA c ccW' ccA' H H1 c'. unfold upd. destruct (Nat.eqb c' c); auto. Qed.

(* a step that changes memory: the new states are related when the new context state is *)
Lemma rel_mem : forall sw sW sA, rel sw sW sA -> forall (s' sA' : st) c ccW' ccA' (m' m'A : mst),
  (forall x, mH m'A x = hers (mH m' x)) ->
  ((mV m' = wv sW /\ mV m'A = wv sA /\ forall x, mH m' x = hs sW x) \/
    exists V xs, mV m' = upd (wv sW) (tm sW) V /\ mV m'A = upd (wv sA) (tm sW) V /\ places (hs sW) xs (tm sW) (mH m')) ->
  (forall x h1 h2, hs sW x = h1 ++ h2 -> mH m' x = h1 ++ (tm sW, false) :: h2 -> free_head h2) ->
  tm s' = S (tm sW) -> tm sA' = S (tm sA) -> pcs sA' = pcs s' -> tp sA' = tp s' -> cm sA' = cm s' ->
  cs s' = upd (cs sW) c ccW' -> cs sA' = upd (cs sA) c ccA' ->
  hs s' = mH m' -> wv s' = mV m' -> hs sA' = mH m'A -> wv sA' = mV m'A ->
  crel sw ccW' ccA' -> (forall k x w, rw ccW' k x = Some w -> In w (ids (mH m' x))) ->
  (forall k t0, oh ccW' k = Some t0 -> t0 < S (tm sW)) ->
  rel sw s' sA'.
Proof.
  intros sw sW sA R s' sA' c ccW' ccA' m' m'A Hh Hs FH Et EtA Ep Etp Ecm Ecs EcsA Ehs Ewv EhsA EwvA Cr Crw Coh.
  assert (TA : tm sA = tm sW) by exact (r_tm sw sW sA R).
  constructor.
  - rewrite Et, EtA, TA. reflexivity.
  - rewrite Ep. reflexivity.
  - rewrite Etp. reflexivity.
  - rewrite Ecm. reflexivity.
  - intros c'. rewrite Ecs, EcsA. apply upd_cs_crel; [apply (r_cr sw sW sA R)|exact Cr].
  - intros x. rewrite EhsA, Ehs. apply Hh.
  - intros x w I. rewrite Ehs in I. rewrite EwvA, Ewv. apply (mem_kept sw sW sA R m' m'A Hs x w I).
  - intros x w I. rewrite Ehs in I. destruct (mem_wb sw sW sA R m' m'A Hh Hs x w I) as (f & Sf & V & M). exists f. rewrite Ewv, EwvA, EhsA. auto.
  - intros x. rewrite Ehs, Ewv. apply (mem_adj sw sW sA R m' m'A Hs FH x).
  - intros x w I. rewrite Ehs in I. rewrite Et. apply (mem_ids sw sW sA R m' m'A Hs x w I).
  - intros c' k x w. rewrite Ecs. unfold upd. destruct (Nat.eqb c' c).
    + intros E. rewrite Ehs. apply Crw with k. exact E.
    + intros E. rewrite Ehs. pose proof (i_rw sw sW sA R c' k x w E) as I. destruct Hs as [(_ & _ & E3)|(V & xs & _ & _ & P)].
      * rewrite E3. exact I.
      * destruct (places_cell _ _ _ _ x P) as [E4|(h1 & h2 & E5 & E6)].
        -- rewrite E4. exact I.
        -- rewrite E6. rewrite E5 in I. apply in_ids_ins. right. exact I.
  - intros c' k t0. rewrite Ecs. unfold upd. destruct (Nat.eqb c' c).
    + intros E. rewrite Et. apply Coh with k. exact E.
    + intros E. rewrite Et. pose proof (i_oh sw sW sA R c' k t0 E). lia.
  - intros w L. apply (i_sw sw sW sA R). rewrite Et in L. lia.
Qed.

(* a step that changes no memory *)
Lemma rel_nomem : forall sw sW sA, rel sw sW sA -> forall (s' sA' : st) c ccW' ccA',
  tm s' = tm sW -> tm sA' = tm sA -> pcs sA' = pcs s' -> tp sA' = tp s' -> cm sA' = cm s' ->
  cs s' = upd (cs sW) c ccW' -> cs sA' = upd (cs sA) c ccA' ->
  hs s' = hs sW -> wv s' = wv sW -> hs sA' = hs sA -> wv sA' = wv sA ->
  crel sw ccW' ccA' -> (forall k x w, rw ccW' k x = Some w -> In w (ids (hs sW x))) ->
  (forall k t0, oh ccW' k = Some t0 -> t0 < tm sW) ->
  rel sw s' sA'.
Proof.
  intros sw sW sA R s' sA' c ccW' ccA' Et EtA Ep Etp Ecm Ecs EcsA Ehs Ewv EhsA EwvA Cr Crw Coh.
  constructor.
  - rewrite Et, EtA. exact (r_tm sw sW sA R).
  - rewrite Ep. reflexivity.
  - rewrite Etp. reflexivity.
  - rewrite Ecm. reflexivity.
  - intros c'. rewrite Ecs, EcsA. apply upd_cs_crel; [apply (r_cr sw sW sA R)|exact Cr].
  - intros x. rewrite EhsA, Ehs. apply (r_hs sw sW sA R).
  - intros x w I. rewrite Ehs in I. rewrite EwvA, Ewv. apply (r_kept sw sW sA R x w I).
  - intros x w I. rewrite Ehs in I. destruct (r_wb sw sW sA R x w I) as (f & Sf & V & M). exists f. rewrite Ewv, EwvA, EhsA. auto.
  - intros x. rewrite Ehs, Ewv. apply (r_adj sw sW sA R x).
  - intros x w I. rewrite Ehs in I. rewrite Et. apply (i_ids sw sW sA R x w I).
  - intros c' k x w. rewrite Ecs. unfold upd. destruct (Nat.eqb c' c).
    + intros E. rewrite Ehs. apply Crw with k. exact E.
    + intros E. rewrite Ehs. apply (i_rw sw sW sA R c' k x w E).
  - intros c' k t0. rewrite Ecs. unfold upd. destruct (Nat.eqb c' c).
    + intros E. rewrite Et. apply Coh with k. exact E.
    + intros E. rewrite Et. apply (i_oh sw sW sA R c' k t0 E).
  - intros w L. apply (i_sw sw sW sA R). rewrite Et in L. exact L.
Qed.

Lemma rel_nomem2 : forall sw sW sA, rel sw sW sA -> forall (s' sA' : st),
  tm s' = tm sW -> tm sA' = tm sA -> pcs sA' = pcs s' -> tp sA' = tp s' -> cm sA' = cm s' ->
  hs s' = hs sW -> wv s' = wv sW -> hs sA' = hs sA -> wv sA' = wv sA ->
  (forall c', crel sw (cs s' c') (cs sA' c')) ->
  (forall c' k x w, rw (cs s' c') k x = Some w -> In w (ids (hs sW x))) ->
  (forall c' k t0, oh (cs s' c') k = Some t0 -> t0 < tm sW) ->
  rel sw s' sA'.
Proof.
  intros sw sW sA R s' sA' Et EtA Ep Etp Ecm Ehs Ewv EhsA EwvA Cr Crw Coh.
  constructor.
  - rewrite Et, EtA. exact (r_tm sw sW sA R).
  - rewrite Ep. reflexivity.
  - rewrite Etp. reflexivity.
  - rewrite Ecm. reflexivity.
  - exact Cr.
  - intros x. rewrite EhsA, Ehs. apply (r_hs sw sW sA R).
  - intros x w I. rewrite Ehs in I. rewrite EwvA, Ewv. apply (r_kept sw sW sA R x w I).
  - intros x w I. rewrite Ehs in I. destruct (r_wb sw sW sA R x w I) as (f & Sf & V & M). exists f. rewrite Ewv, EwvA, EhsA. auto.
  - intros x. rewrite Ehs, Ewv. apply (r_adj sw sW sA R x).
  - intros x w I. rewrite Ehs in I. rewrite Et. apply (i_ids sw sW sA R x w I).
  - intros c' k x w E. rewrite Ehs. apply (Crw c' k x w E).
  - intros c' k t0 E. rewrite Et. apply (Coh c' k t0 E).
  - intros w L. apply (i_sw sw sW sA R). rewrite Et in L. exact L.
Qed.

(* the context state after a fixed result (and a failure that flips the record) *)
Definition scfix_cc (cc : cst) (j : nat) (b : bool) (B : nat -> bool) : cst :=
  mkC (oc cc) (rg cc) (ai cc) (rw cc) (rv cc) (bor (bd cc) B) (vP cc) (vA cc) (vR cc) (vO cc) (vOg cc) (oh cc) (upd (fx cc) j (Some b)).
Definition scfail_cc (cc : cst) (k : nat) : cst :=
  mkC (oc cc) (upd (rg cc) k (vd false (vv (rg cc k)))) (ai cc) (rw cc) (rv cc) (bd cc) (vP cc) (vA cc) (vR cc) (vO cc) (vOg cc) (oh cc) (fx cc).
Definition cfixc (cc : cst) (o : option nat) (j : nat) (b : bool) (B : nat -> bool) : cst :=
  scfix_cc (match o with Some k => if b then cc else scfail_cc cc k | None => cc end) j b B.

Lemma cs_cfix : forall s c o j b B c', cs (scfix0 (sflp s c o b) c j b B) c' = if Nat.eqb c' c then cfixc (cs s c) o j b B else cs s c'.
Proof.
  intros s c o j b B c'. destruct (Nat.eqb c' c) eqn:E.
  - apply Nat.eqb_eq in E. subst c'. unfold scfix0, sflp, scfail, cfixc, scfix_cc, scfail_cc, upd.
    destruct o as [k0|]; [destruct b|]; cbn; rewrite ?Nat.eqb_refl; reflexivity.
  - unfold scfix0, sflp, scfail, upd. destruct o as [k0|]; [destruct b|]; cbn; rewrite E; reflexivity.
Qed.

Lemma crel_cfix : forall sw ccW ccA o j b B, crel sw ccW ccA -> crel sw (cfixc ccW o j b B) (cfixc ccA o j b B).
Proof.
  intros sw ccW ccA o j b B ((rv' & rw' & P & A & R & O & Og & E) & Hv & Hw).
  assert (Hrv : forall j x, rv' j x = rv ccW j x) by (intros j0 x; specialize (Hv j0 x); rewrite E in Hv; exact Hv).
  assert (Hrw : forall j x, rw' j x = pi sw x (rw ccW j x)) by (intros j0 x; specialize (Hw j0 x); rewrite E in Hw; exact Hw).
  subst ccA. unfold cfixc. destruct o as [k0|]; [destruct b|].
  - split; [|split]; [do 7 eexists; reflexivity|intros k x; cbn; apply Hrv|intros k x; cbn; apply Hrw].
  - split; [|split]; [do 7 eexists; reflexivity|intros k x; cbn; apply Hrv|intros k x; cbn; apply Hrw].
  - split; [|split]; [do 7 eexists; reflexivity|intros k x; cbn; apply Hrv|intros k x; cbn; apply Hrw].
Qed.
