(* The shim under which the DRF core files are re-checked
   on M2DQ. Each lemma here has the name and the shape of the M2Model lemma
   it stands for, with run, step and trace read as runQ, stepQ and traceQ
   (the notations at the end). A ported file imports this module last, so
   its scripts refer to these. The step-level lemmas are proved in
   M2DQIface (SI, Ext) from the record-fix factoring F1/F2. *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO M2Oota M2Cont M2Snap M2Trace
  M2Iface M2DA M2DP M2DQ M2DQInv M2DQOota M2DQIface.

Definition traceQ (p : prog) (f : nat -> st) (n : nat) : Prop :=
  f 0 = sinit /\ forall i, i < n -> stepQ p (f i) (f (S i)).

Lemma Inv1_run : forall p s, runQ p s -> Inv1 p s.
Proof. intros p s R. exact (s1 p s (IS_run p s R)). Qed.
Lemma Inv2_run : forall p s, runQ p s -> Inv1 p s /\ Inv2 p s.
Proof. intros p s R. destruct (IS_run p s R) as [I J _ _ _]. auto. Qed.
Lemma Inv_run : forall p s, runQ p s -> InvAll p s.
Proof. intros p s R. destruct (IS_run p s R) as [I J L _ _]. constructor; auto. Qed.
Lemma InvO_run : forall p s, runQ p s -> InvAllO p s.
Proof. intros p s R. destruct (IS_run p s R) as [I J L Q _]. constructor; auto. Qed.
Lemma SI_run : forall p s, runQ p s -> SI p s.
Proof. intros p s R. exact (sS p s (IS_run p s R)). Qed.
Theorem INVPH_run : forall p s, wf p -> cellful p -> runQ p s -> INVP p s /\ INVH p s.
Proof. exact INVPH_runQ. Qed.
Theorem INVP_run : forall p s, wf p -> cellful p -> runQ p s -> INVP p s.
Proof. intros. apply INVPH_run; auto. Qed.
Theorem INVH_run : forall p s, wf p -> cellful p -> runQ p s -> INVH p s.
Proof. intros. apply INVPH_run; auto. Qed.
Lemma Ext_step : forall p s t, runQ p s -> stepQ p s t -> Ext s t.
Proof. intros p s t R S. apply (gq_keeps p); [apply reach_runQ; exact R|exact S]. Qed.
Lemma cf_regs : forall p s c k, wf p -> runQ p s -> pcs s c <= k -> oc (cs s c) k = None ->
  vok (rg (cs s c) k) = true -> forall B f, exists F, forall j,
  creg p c (cs s c) (pcs s c) (tp s c) (bor (bd (cs s c)) B) F j =
  creg p c (cc_rg (cs s c) (upd (rg (cs s c)) k (vd false (vv (rg (cs s c) k))))) (pcs s c) (tp s c) (bor (bd (cs s c)) B) f j.
Proof. intros p s c k W R Hp Ho Hv. exact (cf_regsQ p s c k W (Inv1_run p s R) Hp Ho Hv). Qed.
Lemma trace_run : forall p f n, traceQ p f n -> forall i, i <= n -> runQ p (f i).
Proof.
  intros p f n [A B] i L. induction i as [|i IH]; [rewrite A; constructor|].
  apply xS with (f i); [apply IH; lia|apply B; lia].
Qed.

Notation run := runQ (only parsing).
Notation step := stepQ (only parsing).
Notation trace := traceQ (only parsing).

Lemma cfix_pre : forall p s c j b B o, run p s -> cfix_ok p c (cs s c) (pcs s c) (tp s c) j b B o ->
  Inv1 p (sflp s c o b) /\
  forall f k, hpend_at p c (cs (sflp s c o b) c) (pcs (sflp s c o b) c) (tp (sflp s c o b) c)
                (creg p c (cs (sflp s c o b) c) (pcs (sflp s c o b) c) (tp (sflp s c o b) c)
                   (bor (bd (cs (sflp s c o b) c)) B) f) j = Some k ->
              vok (rg (cs (sflp s c o b) c) k) = true \/ b = false.
Proof.
  intros p s c j b B o R Hc. pose proof (Inv1_run p s R) as I. split.
  - destruct o as [k|]; [destruct b|]; cbn [sflp]; try exact I.
    destruct (cfix_rec _ _ _ _ _ _ _ _ _ Hc) as (Hp & Ho & Hh & _). apply Inv1_cfail; auto.
  - destruct Hc as (v & Hv). destruct o as [k0|]; [destruct b|]; cbn [sflp]; intros f k Hp.
    + left. destruct (Hv f) as (_ & _ & _ & Ho & Hk & _). cbv zeta in Ho. rewrite Hp in Ho. apply Hk. congruence.
    + right. reflexivity.
    + exfalso. destruct (Hv f) as (_ & _ & _ & Ho & _). cbv zeta in Ho. congruence.
Qed.

Lemma early_of : forall p s c j k tj tk, run p s -> j < k ->
  oc (cs s c) j = Some tj -> oc (cs s c) k = Some tk -> tk < tj ->
  exists cc0 pc0 N0 B0 d e, es s tk = Some (cc0, pc0, N0, B0) /\ ent s tk = Some e /\ ec e = c /\ ek e = k /\
    eokx p c cc0 pc0 N0 tk d (erf e) B0 /\ eof (ai (cs s c) k) (rg (cs s c)) = Some d /\
    pc0 <= j /\ oc cc0 j = None /\
    (forall i t0, oc cc0 i = Some t0 -> oc (cs s c) i = Some t0 /\ rg cc0 i = rg (cs s c) i /\ t0 < tk) /\
    (forall i t0, oc (cs s c) i = Some t0 -> t0 < tk -> oc cc0 i = Some t0) /\
    (forall i d', oc cc0 i <> None -> pc0 <= i -> ai cc0 i = inst_of d' ->
        eof (ai (cs s c) i) (rg (cs s c)) = Some d') /\
    (forall i, oc cc0 i <> None -> pc0 <= i -> exists d', ai cc0 i = inst_of d' /\ d' <> DFn FFull) /\
    (forall i t0, oh cc0 i = Some t0 -> oh (cs s c) i = Some t0 /\ t0 < tk).
Proof.
  intros p s c j k tj tk R L Oj Ok Lt. pose proof (Inv1_run p s R) as I. pose proof (SI_run p s R) as (S1 & S2 & S3).
  destruct (i_oc p s I c k tk Ok) as (e & A & B & C).
  destruct (es s tk) as [[[[cc0 pc0] N0] B0]|] eqn:Es.
  - assert (Hn : forall e0, ent s tk = Some e0 -> eh e0 = false).
    { intros e0 E0. rewrite A in E0. injection E0 as <-. destruct (i_et p s I tk e A) as (_ & X).
      destruct (eh e) eqn:Eh; [|reflexivity]. exfalso. rewrite B, C in X.
      destruct (i_hoc p s I c k tk tk X Ok) as (Z & _). lia. }
    destruct (S3 tk cc0 pc0 N0 B0 Es Hn) as (e' & d & A' & Ok' & Pk & D & E & F & G & Lp & Pn & Ph). rewrite A in A'. injection A' as <-.
    rewrite B, C in *. exists cc0, pc0, N0, B0, d, e.
    do 6 (split; [auto|]). split; [|split; [|split; [exact E|split; [exact F|split; [exact G|split; [exact Pn|exact Ph]]]]]].
    + destruct (Nat.lt_ge_cases j pc0) as [X|X]; [|lia]. exfalso. destruct Lp as (_ & Lp).
      destruct (oc cc0 j) as [t0|] eqn:Y.
      * destruct (E j t0 Y) as (Y1 & _ & Y3). rewrite Oj in Y1. injection Y1 as <-. lia.
      * rewrite (Lp j X Y) in Oj. discriminate.
    + destruct (oc cc0 j) as [t0|] eqn:Y; auto. destruct (E j t0 Y) as (Y1 & _ & Y3). rewrite Oj in Y1. injection Y1 as <-. lia.
  - exfalso. destruct (S2 tk e A Es) as [_ Q]. rewrite B, C in Q. pose proof (Q j tj L Oj). lia.
Qed.
