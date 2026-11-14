(* Model M2DQ for spec 0.1 §2.3.4: M2DP with its model limit closed (a
   success counted on where the claim differs between valuations).

   Steps of M2DQ:
   - q_old: a step of M2Model that makes no CAS happen as a whole (M2DA's
     nowhole): every CAS happens in parts (s_cread, then s_cw / s_skip), as
     in M2DA.
   - q_rfix: M2DQ's record fix (a failure counted on where the claim differs
     between valuations), as M2DP.p_rfix; the new state is written as the
     failure of the record (M2Model.scfail) and the reads counted on added
     (sbd), so that the existing lemmas on scfail apply.
   - q_sfix: a success counted on, keyed by the record k: one place j
     at a time is given the fixed result success (M2Model.scfix0 ... true).
     Under every valuation considered, the record's claim jf permits
     success (the value equals the expected value), is not already fixed to
     failure, and j is either that claim or holds no executing CAS. Fixing
     every place that is a claim under some valuation gives the record the
     outcome success under every valuation; the place-keyed field fx is read
     only where an executing CAS is (cfx), so a place that is no claim under
     a valuation is not touched under it.
   What q_sfix does not cover: a success where some valuation has, at a
   place that is the claim under another valuation, an executing CAS that is
   not the record's claim. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Inv M2Cont M2DA M2DP.

(* the reads B are counted on in context c; nothing else changes *)
Definition sbd (s : st) (c : nat) (B : nat -> bool) : st :=
  let cc := cs s c in
  mkS (tm s) (upd (cs s) c (cc_fx cc (bor (bd cc) B) (fx cc)))
      (wv s) (wc s) (hs s) (vG s) (pcs s) (tp s) (cm s) (lg s) (es s).

(* success counted on for the record k, at place j *)
Definition sfix_ok (p : prog) (c : nat) (cc : cst) (pc N j k : nat) (B : nat -> bool) : Prop :=
  oc cc k = None /\ oh cc k <> None /\ vok (rg cc k) = true /\
  forall f, let r := creg p c cc pc N (bor (bd cc) B) f in
    exists jf, pc <= jf /\ hpend_at p c cc pc N r jf = Some k /\ pend_at p c cc pc N r jf = None /\
      is_cas (ins p c jf r) = true /\ icond (ins p c jf r) r = true /\
      vv (r jf) = cexp (ins p c jf r) r /\ fx cc jf <> Some false /\
      (jf = j \/ is_cas (ins p c j r) && icond (ins p c j r) r = false).

Inductive stepQ (p : prog) : st -> st -> Prop :=
| q_old : forall s s', step p s s' -> nowhole s s' -> stepQ p s s'
| q_rfix : forall s c k B,
    rfail_ok p c (cs s c) (pcs s c) (tp s c) k B ->
    (forall j, pcs s c <= j -> fx (cs s c) j = None ->
       ~ cfix_ok p c (cs s c) (pcs s c) (tp s c) j false B (Some k)) ->
    stepQ p s (sbd (scfail s c k) c B)
| q_sfix : forall s c j k B,
    pcs s c <= j -> fx (cs s c) j = None ->
    sfix_ok p c (cs s c) (pcs s c) (tp s c) j k B ->
    stepQ p s (scfix0 s c j true B).

Inductive runQ (p : prog) : st -> Prop :=
| x0 : runQ p sinit
| xS : forall s s', runQ p s -> stepQ p s s' -> runQ p s'.

Lemma runD_runQ : forall p s, runD p s -> runQ p s.
Proof.
  intros p s R. induction R as [|s s' R IH S N]; [constructor|].
  econstructor; [exact IH|]. apply q_old; [exact S|exact N].
Qed.

(* the record of a claim is at or beyond the next instruction *)
Lemma hpend_at_ge : forall p c cc pc N r j k, hpend_at p c cc pc N r j = Some k -> pc <= k.
Proof.
  intros p c cc pc N r j k H. unfold hpend_at in H. apply find_some' in H as (Hi & _).
  apply in_seq in Hi. lia.
Qed.

Lemma rfail_ge : forall p c cc pc N k B, rfail_ok p c cc pc N k B -> pc <= k.
Proof.
  intros p c cc pc N k B (_ & _ & _ & v & H). destruct (H (fun _ _ => 0)) as (j & (_ & Hp & _) & _).
  exact (hpend_at_ge _ _ _ _ _ _ _ _ Hp).
Qed.

(* a place held by a record is an executing CAS *)
Lemma hpend_at_exec : forall p c cc pc N r j k, hpend_at p c cc pc N r j = Some k ->
  is_cas (ins p c j r) && icond (ins p c j r) r = true.
Proof.
  intros p c cc pc N r j k H. destruct (hpend_eofR p c cc pc N r j k H) as (m & xs & _ & E).
  unfold eofR in E. unfold icond, ieval. destruct (ins p c j r) as [| | m1 x1 c1 e1 n1 | |]; try discriminate.
  cbn. destruct (c1 r); [reflexivity|discriminate].
Qed.

(* the condition M2Cont.INVP_cfix asks of a place fixed to success *)
Lemma sfix_hc : forall p c cc pc N j k B, sfix_ok p c cc pc N j k B ->
  forall f k', hpend_at p c cc pc N (creg p c cc pc N (bor (bd cc) B) f) j = Some k' -> vok (rg cc k') = true.
Proof.
  intros p c cc pc N j k B (_ & _ & Vk & H) f k' Hp. destruct (H f) as (jf & _ & Hk & _ & _ & _ & _ & _ & E).
  cbv zeta in *. destruct E as [<-|E].
  - rewrite Hk in Hp. injection Hp as <-. exact Vk.
  - rewrite (hpend_at_exec _ _ _ _ _ _ _ _ Hp) in E. discriminate.
Qed.

(* runs built forward *)
Inductive starQ (p : prog) : st -> st -> Prop :=
| sq0 : forall s, starQ p s s
| sqS : forall s s1 t, stepQ p s s1 -> starQ p s1 t -> starQ p s t.

Lemma starQ_run : forall p s t, runQ p s -> starQ p s t -> runQ p t.
Proof. intros p s t R H. induction H; auto. apply IHstarQ. econstructor; eauto. Qed.
