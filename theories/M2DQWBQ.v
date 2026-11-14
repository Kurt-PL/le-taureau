(* Write-back over M2DQ: a step of M2DQ is a step of M2Model (with nowhole) or a record fix (q_rfix,
   q_sfix), which changes nothing but the registers rg, the reads counted on bd and the fixed
   results fx of one context (rfx).  The ported step lemmas of the write-back proof take the
   M2Model step as before (their name with suffix A) and the record fix through rfx. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Inv M2Cont M2DA M2DP M2DQ.

(* s' is s up to rg, bd and fx of the contexts *)
Definition rfx (s s' : st) : Prop :=
  tm s' = tm s /\ wv s' = wv s /\ wc s' = wc s /\ hs s' = hs s /\ vG s' = vG s /\ pcs s' = pcs s /\
  tp s' = tp s /\ cm s' = cm s /\ lg s' = lg s /\ es s' = es s /\
  forall c, oc (cs s' c) = oc (cs s c) /\ ai (cs s' c) = ai (cs s c) /\ rw (cs s' c) = rw (cs s c) /\
    rv (cs s' c) = rv (cs s c) /\ vP (cs s' c) = vP (cs s c) /\ vA (cs s' c) = vA (cs s c) /\
    vR (cs s' c) = vR (cs s c) /\ vO (cs s' c) = vO (cs s c) /\ vOg (cs s' c) = vOg (cs s c) /\
    oh (cs s' c) = oh (cs s c) /\
    (forall j, rg (cs s' c) j = rg (cs s c) j \/ rg (cs s' c) j = vd false (vv (rg (cs s c) j))).

(* the two record fixes of M2DQ *)
Lemma rfx_rfix : forall s c k B, rfx s (sbd (scfail s c k) c B).
Proof.
  intros s c k B. do 10 (split; [reflexivity|]). intros c0. unfold sbd, scfail, cc_fx, upd. cbn.
  destruct (Nat.eqb_spec c0 c) as [->|_]; cbn; rewrite ?Nat.eqb_refl; cbn; (do 10 (split; [reflexivity|])); intros j.
  - destruct (Nat.eqb_spec j k) as [->|_]; [right|left]; reflexivity.
  - left. reflexivity.
Qed.

Lemma rfx_sfix : forall s c j B, rfx s (scfix0 s c j true B).
Proof.
  intros s c j B. do 10 (split; [reflexivity|]). intros c0. unfold scfix0, upd. cbn.
  destruct (Nat.eqb_spec c0 c) as [->|_]; cbn; (do 10 (split; [reflexivity|])); intros j0; left; reflexivity.
Qed.

Lemma stepQ_split : forall p s s', stepQ p s s' -> (step p s s' /\ nowhole s s') \/ rfx s s'.
Proof.
  intros p s s' H. destruct H as [s s' St V|s c k B _ _|s c j k B _ _ _].
  - left. auto.
  - right. apply rfx_rfix.
  - right. apply rfx_sfix.
Qed.

Section R.
Variables (s s' : st) (RF : rfx s s').
Lemma rfx_tm : tm s' = tm s. Proof. apply RF. Qed.
Lemma rfx_wv : wv s' = wv s. Proof. apply RF. Qed.
Lemma rfx_wc : wc s' = wc s. Proof. apply RF. Qed.
Lemma rfx_hs : hs s' = hs s. Proof. apply RF. Qed.
Lemma rfx_vG : vG s' = vG s. Proof. apply RF. Qed.
Lemma rfx_pcs : pcs s' = pcs s. Proof. apply RF. Qed.
Lemma rfx_tp : tp s' = tp s. Proof. apply RF. Qed.
Lemma rfx_cm : cm s' = cm s. Proof. apply RF. Qed.
Lemma rfx_lg : lg s' = lg s. Proof. apply RF. Qed.
Lemma rfx_es : es s' = es s. Proof. apply RF. Qed.
Lemma rfx_oc : forall c, oc (cs s' c) = oc (cs s c). Proof. intros c. apply RF. Qed.
Lemma rfx_ai : forall c, ai (cs s' c) = ai (cs s c). Proof. intros c. apply RF. Qed.
Lemma rfx_rw : forall c, rw (cs s' c) = rw (cs s c). Proof. intros c. apply RF. Qed.
Lemma rfx_rv : forall c, rv (cs s' c) = rv (cs s c). Proof. intros c. apply RF. Qed.
Lemma rfx_vP : forall c, vP (cs s' c) = vP (cs s c). Proof. intros c. apply RF. Qed.
Lemma rfx_vA : forall c, vA (cs s' c) = vA (cs s c). Proof. intros c. apply RF. Qed.
Lemma rfx_vR : forall c, vR (cs s' c) = vR (cs s c). Proof. intros c. apply RF. Qed.
Lemma rfx_vO : forall c, vO (cs s' c) = vO (cs s c). Proof. intros c. apply RF. Qed.
Lemma rfx_vOg : forall c, vOg (cs s' c) = vOg (cs s c). Proof. intros c. apply RF. Qed.
Lemma rfx_oh : forall c, oh (cs s' c) = oh (cs s c). Proof. intros c. apply RF. Qed.
Lemma rfx_rg : forall c j, rg (cs s' c) j = rg (cs s c) j \/ rg (cs s' c) j = vd false (vv (rg (cs s c) j)).
Proof. intros c. apply RF. Qed.
Lemma rfx_vv : forall c j, vv (rg (cs s' c) j) = vv (rg (cs s c) j).
Proof. intros c j. destruct (rfx_rg c j) as [E|E]; rewrite E; [reflexivity|apply vv_vd]. Qed.
Lemma rfx_fail : forall c j, vok (rg (cs s c) j) = false -> vok (rg (cs s' c) j) = false.
Proof. intros c j F. destruct (rfx_rg c j) as [E|E]; rewrite E; [exact F|apply vok_vd]. Qed.
End R.

(* rewrite every field rfx keeps, in the goal and the hypotheses *)
Ltac rfx_rw RF :=
  repeat first
    [ rewrite (rfx_tm _ _ RF) in * | rewrite (rfx_wv _ _ RF) in * | rewrite (rfx_wc _ _ RF) in *
    | rewrite (rfx_hs _ _ RF) in * | rewrite (rfx_vG _ _ RF) in * | rewrite (rfx_pcs _ _ RF) in *
    | rewrite (rfx_tp _ _ RF) in * | rewrite (rfx_cm _ _ RF) in * | rewrite (rfx_lg _ _ RF) in *
    | rewrite (rfx_es _ _ RF) in * | rewrite (rfx_oc _ _ RF) in * | rewrite (rfx_ai _ _ RF) in *
    | rewrite (rfx_rw _ _ RF) in * | rewrite (rfx_rv _ _ RF) in * | rewrite (rfx_vP _ _ RF) in *
    | rewrite (rfx_vA _ _ RF) in * | rewrite (rfx_vR _ _ RF) in * | rewrite (rfx_vO _ _ RF) in *
    | rewrite (rfx_vOg _ _ RF) in * | rewrite (rfx_oh _ _ RF) in * ].

(* rfx is reflexive *)
Lemma rfx_refl : forall s, rfx s s.
Proof. intros s. do 10 (split; [reflexivity|]). intros c. do 10 (split; [reflexivity|]). intros j. left. reflexivity. Qed.

(* the image's runs are M2DQ runs: star reads as starQ *)
Notation star := starQ (only parsing).
Notation st0 := sq0 (only parsing).
Notation stS := sqS (only parsing).
