(* Model M2DP for spec 0.1 §2.3.4. A joint access happens only in
   parts (M2DA: no step makes a CAS's slot happen unless its read happened
   alone), and an outcome is counted on where a load part HAS HAPPENED: the
   fixing is keyed by the read-half record k, and the fixed outcome binds
   whichever place is that record's claim under each valuation.

   Representation in M2Model's state (which cannot be changed):
   - a failure fixed on record k is the record's register made a failure
     (srfix). slotv's read-alone branch then gives that failure at whichever
     place is the record's claim (hpend_at), and s_skip passes that place.
     This is keyed by the record, with no place.
   - where one place is the claim under every valuation, the fix is
     M2Model's s_cfix (kept from M2DA). It also records the place, and
     p_rfix is then not used (its last premise). rfix_total shows that a
     record failure is always fixable in M2DP whenever rfail_ok holds.
   - a SUCCESS fixed on a record whose claim differs between valuations is
     not in M2DP. It would need a per-record verdict field that slotv reads,
     and M2Model has no such field. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Eff M2Inv M2DA M2DAInv.

(* place j is the claim of the load part recorded at slot k, under registers
   r: a CAS that occurs there, whose place is that record (hpend_at), which
   has not happened as a whole or by another access placed there, and has no
   place-keyed fix *)
Definition rclaim (p : prog) (c : nat) (cc : cst) (pc N : nat) (r : regs) (k j : nat) : Prop :=
  pc <= j /\ hpend_at p c cc pc N r j = Some k /\ pend_at p c cc pc N r j = None /\
  is_cas (ins p c j r) = true /\ icond (ins p c j r) r = true /\ fx cc j = None.

(* the widened sentence, for the outcome "does not store" (always permitted):
   the load part recorded at k has happened, its store part has not, it is
   not already a failure, and under every valuation considered (reads B
   counted on) it has a claim, where it has one value v *)
Definition rfail_ok (p : prog) (c : nat) (cc : cst) (pc N k : nat) (B : nat -> bool) : Prop :=
  oc cc k = None /\ oh cc k <> None /\ vok (rg cc k) = true /\
  exists v, forall f, let r := creg p c cc pc N (bor (bd cc) B) f in
    exists j, rclaim p c cc pc N r k j /\ vv (r j) = v.

(* the record's register becomes a failure; the reads B are counted on *)
Definition srfix (s : st) (c k : nat) (B : nat -> bool) : st :=
  let cc := cs s c in
  mkS (tm s)
      (upd (cs s) c (mkC (oc cc) (upd (rg cc) k (vd false (vv (rg cc k)))) (ai cc) (rw cc) (rv cc) (bor (bd cc) B)
                         (vP cc) (vA cc) (vR cc) (vO cc) (vOg cc) (oh cc) (fx cc)))
      (wv s) (wc s) (hs s) (vG s)
      (pcs s) (tp s) (cm s) (lg s) (es s).

Inductive stepP (p : prog) : st -> st -> Prop :=
| p_old : forall s s', step p s s' -> nowhole s s' -> stepP p s s'
| p_rfix : forall s c k B,
    rfail_ok p c (cs s c) (pcs s c) (tp s c) k B ->
    (forall j, pcs s c <= j -> fx (cs s c) j = None ->
       ~ cfix_ok p c (cs s c) (pcs s c) (tp s c) j false B (Some k)) ->
    stepP p s (srfix s c k B).

Inductive runP (p : prog) : st -> Prop :=
| q0 : runP p sinit
| qS : forall s s', runP p s -> stepP p s s' -> runP p s'.

Lemma runD_runP : forall p s, runD p s -> runP p s.
Proof. intros p s R. induction R; [constructor|]. econstructor; [eassumption|]. apply p_old; assumption. Qed.

(* ---------- one place: the record fix is M2Model's place fix ---------- *)
Lemma rfix_one : forall p c cc pc N k B j, rfail_ok p c cc pc N k B ->
  (forall f, let r := creg p c cc pc N (bor (bd cc) B) f in rclaim p c cc pc N r k j /\ vv (r j) = vv (rg cc k)) ->
  cfix_ok p c cc pc N j false B (Some k).
Proof.
  intros p c cc pc N k B j (_ & _ & Ok & _) H. exists (vv (rg cc k)). intros f. cbv zeta.
  destruct (H f) as ((_ & Hp & Pa & Ci & Ic & _) & V). cbv zeta in V.
  split; [exact Ci|split; [exact Ic|split; [exact Pa|split; [exact Hp|split; [|split; [exact V|]]]]]].
  - intros k' E. injection E as <-. exact Ok.
  - intros E. discriminate E.
Qed.

(* a place fix of a record names one place under every valuation *)
Lemma cfix_rclaim : forall p c cc pc N j B k, pc <= j -> fx cc j = None ->
  cfix_ok p c cc pc N j false B (Some k) ->
  forall f, rclaim p c cc pc N (creg p c cc pc N (bor (bd cc) B) f) k j.
Proof.
  intros p c cc pc N j B k L Fx (v & H) f. destruct (H f) as (Ci & Ic & Pa & Hp & _).
  repeat split; assumption.
Qed.

(* ---------- what srfix changes ---------- *)
Lemma srfix_rg : forall s c k B, rg (cs (srfix s c k B) c) k = vd false (vv (rg (cs s c) k)).
Proof. intros. unfold srfix. cbn [cs]. rewrite upd_o. cbn [rg]. apply upd_o. Qed.

Lemma srfix_same : forall s c k B c' k', oc (cs (srfix s c k B) c') k' = oc (cs s c') k' /\
  oh (cs (srfix s c k B) c') k' = oh (cs s c') k' /\ ai (cs (srfix s c k B) c') k' = ai (cs s c') k' /\
  fx (cs (srfix s c k B) c') k' = fx (cs s c') k'.
Proof.
  intros s c k B c' k'. unfold srfix. cbn [cs]. destruct (Nat.eq_dec c' c) as [->|N].
  - rewrite upd_o. cbn [oc oh ai fx]. auto.
  - rewrite upd_n by exact N. auto.
Qed.

Lemma srfix_glob : forall s c k B, pcs (srfix s c k B) = pcs s /\ tm (srfix s c k B) = tm s /\
  hs (srfix s c k B) = hs s /\ tp (srfix s c k B) = tp s.
Proof. intros. unfold srfix. cbn. auto. Qed.

(* ---------- the record fix is total: wherever rfail_ok holds, M2DP can make
   the record a failure (by s_cfix where one place is the claim, else by
   p_rfix); stated constructively as a double negation ---------- *)
Lemma scfix_rec_fail : forall s c j B k,
  rg (cs (scfix0 (sflp s c (Some k) false) c j false B) c) k = vd false (vv (rg (cs s c) k)).
Proof. intros. unfold scfix0, sflp, scfail. cbn [cs]. rewrite !upd_o. cbn [rg]. rewrite !upd_o. reflexivity. Qed.

Lemma scfix_oc : forall s c j b B o c' k, oc (cs (scfix0 (sflp s c o b) c j b B) c') k = oc (cs s c') k.
Proof. intros. exact (proj1 (fx_cs_same s c j b B o c' k)). Qed.

Theorem rfix_total : forall p s c k B, rfail_ok p c (cs s c) (pcs s c) (tp s c) k B ->
  ~ ~ exists s', stepP p s s' /\ rg (cs s' c) k = vd false (vv (rg (cs s c) k)).
Proof.
  intros p s c k B Ok No. apply No. exists (srfix s c k B). split; [|apply srfix_rg].
  apply p_rfix; [exact Ok|]. intros j L Fx Cf. apply No.
  exists (scfix0 (sflp s c (Some k) false) c j false B). split; [|apply scfix_rec_fail].
  apply p_old.
  - apply s_cfix; assumption.
  - apply nowhole_oc. intros c' k'. apply scfix_oc.
Qed.

(* ---------- M2DP runs with no multi-place record fix are runD runs ---------- *)
Lemma runP_runD : forall p,
  (forall s c k B, runD p s -> rfail_ok p c (cs s c) (pcs s c) (tp s c) k B ->
     exists j, pcs s c <= j /\ fx (cs s c) j = None /\
       cfix_ok p c (cs s c) (pcs s c) (tp s c) j false B (Some k)) ->
  forall s, runP p s -> runD p s.
Proof.
  intros p H s R. induction R as [|s s' R IH S]; [constructor|].
  destruct S as [s s' S N|s c k B Ok Nf].
  - econstructor; eassumption.
  - exfalso. destruct (H s c k B IH Ok) as (j & L & Fx & Cf). exact (Nf j L Fx Cf).
Qed.

(* ---------- the claim is a CAS of the record's mode and cells ---------- *)
Lemma hpend_eofR : forall p c cc pc N r j k, hpend_at p c cc pc N r j = Some k ->
  exists m xs, casx (ai cc k) = Some (m, xs) /\ eofR (ins p c j r) r = Some (m, xs).
Proof.
  intros p c cc pc N r j k H. unfold hpend_at in H. apply find_some' in H as (_ & F).
  destruct (oc cc k); [discriminate|]. destruct (oh cc k) as [t|]; [|discriminate].
  destruct (casx (ai cc k)) as [[m xs]|] eqn:Cx; [|discriminate].
  exists m, xs. split; [reflexivity|]. cbn [fab] in F.
  repeat (apply andb_true_iff in F as [F ?]).
  match goal with X : tatb _ _ _ = true |- _ => revert X end. unfold tatb.
  destruct (eofR (ins p c j r) r) as [[m' xs']|]; [|discriminate].
  rewrite lst_eqb_eq. intros ->. destruct m, m'. reflexivity.
Qed.

(* ---------- building M2DP runs forward ---------- *)
Inductive starP (p : prog) : st -> st -> Prop :=
| sp0 : forall s, starP p s s
| spS : forall s s1 t, stepP p s s1 -> starP p s1 t -> starP p s t.

Lemma starP_run : forall p s t, runP p s -> starP p s t -> runP p t.
Proof. intros p s t R H. induction H; auto. apply IHstarP. econstructor; eauto. Qed.

Lemma startP : forall p (Q : st -> Prop), (exists t, starP p sinit t /\ Q t) -> exists t, runP p t /\ Q t.
Proof. intros p Q (t & H & q). exists t. split; auto. eapply starP_run; eauto. constructor. Qed.

Lemma fwdO : forall p s s1 (Q : st -> Prop), step p s s1 -> nowhole s s1 -> (exists t, starP p s1 t /\ Q t) ->
  exists t, starP p s t /\ Q t.
Proof. intros p s s1 Q H N (t & A & B). exists t. split; auto. econstructor; [apply p_old; eauto|exact A]. Qed.

Lemma fwdR : forall p s c k B (Q : st -> Prop), rfail_ok p c (cs s c) (pcs s c) (tp s c) k B ->
  (forall j, pcs s c <= j -> fx (cs s c) j = None -> ~ cfix_ok p c (cs s c) (pcs s c) (tp s c) j false B (Some k)) ->
  (exists t, starP p (srfix s c k B) t /\ Q t) -> exists t, starP p s t /\ Q t.
Proof. intros p s c k B Q O N (t & A & Bq). exists t. split; auto. econstructor; [apply p_rfix; eauto|exact A]. Qed.

(* nowhole for a step that changes context c only, by its oc *)
Lemma nowhole_upd : forall s s' c X, cs s' = upd (cs s) c X ->
  (forall k, oc X k <> oc (cs s c) k -> oh (cs s c) k <> None \/ is_cas (ai X k) = false) -> nowhole s s'.
Proof.
  intros s s' c X E H c' k O O' C. rewrite E in O', C. unfold upd in O', C.
  destruct (Nat.eqb_spec c' c) as [->|Nc]; [|congruence].
  destruct (H k ltac:(congruence)) as [Hh|Hc]; [exact Hh|congruence].
Qed.

Lemma nowhole_put : forall s s' c X k0 t, cs s' = upd (cs s) c X -> oc X = upd (oc (cs s c)) k0 (Some t) ->
  is_cas (ai X k0) = false -> nowhole s s'.
Proof.
  intros s s' c X k0 t E O C. apply (nowhole_upd s s' c X E). intros k Ne. right.
  rewrite O in Ne. unfold upd in Ne. destruct (Nat.eqb k k0) eqn:Ek; [apply Nat.eqb_eq in Ek; subst; exact C|congruence].
Qed.

Lemma nowhole_keep : forall s s' c X, cs s' = upd (cs s) c X -> oc X = oc (cs s c) -> nowhole s s'.
Proof. intros s s' c X E O. apply (nowhole_upd s s' c X E). intros k Ne. rewrite O in Ne. congruence. Qed.

Print Assumptions rfix_total.
Print Assumptions runP_runD.
Print Assumptions hpend_eofR.
