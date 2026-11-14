(* Oracle row OwnFuture (oracle/ORACLE.md), excluded, on M2DQ.
     T0: r1 = x; x = 1; y = r1
     T1: r3 = y; x = r3
   with r1 = 1 and r3 = 1. Cells: x = 0, y = 1.
   r1 = 1 reads a write of x with value 1 that happened before the read.
   T0's own x = 1 comes after the read (same cell). T1's x = r3 comes after
   T1's read of y (for the free value 0 it writes 0), and r3 = 1 reads T0's
   y = r1, which comes after T0's read of x (for the free value 0 it writes
   0). The four accesses would form a cycle in time.
   The programme has no CAS, so a run of M2DQ is a run of M2Model
   (M2DQOracleCoRW.runQ_cf_run). *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2Comp M2Lit M2Neg M2Oota M2Snap M2Ev M2Cont M2LitNeg M2CasFwd.
Require Import M2DA M2DP M2DQ M2DQOracleCoRW.

Definition CODEF : list (list instr) :=
  [ [ld 0; st 0 1; ISt Plain [1] T (RG 0)];
    [ld 1; ISt Plain [0] T (RG 0)] ].
Definition OWNF : prog := stat CODEF.

Lemma insF : forall c k r, ins OWNF c k r = nth k (nth c CODEF []) INop.
Proof. intros. apply ins_stat. Qed.

Lemma W_F : wf OWNF.
Proof. wf_tac. Qed.

Lemma CF_F : cas_free OWNF.
Proof.
  intros c k r. rewrite insF. destruct c as [|[|c]]; [| |destruct c; destruct k; reflexivity];
    (destruct k as [|[|[|k]]]; simpl; try reflexivity; destruct k; reflexivity).
Qed.

(* with nothing of the context happened, the mill part of a first load is its free value *)
Lemma r0_freeF : forall c cc N B f x, nth 0 (nth c CODEF []) INop = ILd Plain [x] T -> (forall k, oc cc k = None) ->
  creg OWNF c cc 0 N B f 0 = f 0 x.
Proof.
  intros c cc N B f x H Hn. rewrite creg_bl. unfold slotv. simpl. rewrite insF, H. simpl.
  rewrite (pend_none OWNF c cc N _ 0 Hn).
  rewrite (hpa_ld OWNF c cc 0 N _ 0 Plain [x] T ltac:(rewrite insF, H; reflexivity)). reflexivity.
Qed.

Section F.
Variable s : M2Model.st.
Hypothesis R : run OWNF s.
Hypothesis CP : done OWNF s.

(* a slot past the code (no instruction) happened when it was passed, after slot 0 *)
Lemma past_lateF : forall c i t0 tj, c < 2 -> length (nth c CODEF []) <= i ->
  oc (cs s c) i = Some t0 -> oc (cs s c) 0 = Some tj -> tj <= t0.
Proof.
  intros c i t0 tj Lc Li O Oj. pose proof (Inv1_run _ s R) as I. pose proof W_F as W.
  assert (Lp : i < pcs s c) by (apply (passed OWNF s R CP W c i); congruence).
  destruct (proj1 (i_cmA _ s I c i) Lp) as (tau & T0).
  assert (Ii : ins OWNF c i (rg (cs s c)) = INop).
  { rewrite insF. destruct c as [|[|c]]; [| |lia]; cbn in Li |- *;
      repeat (destruct i as [|i]; [lia|]); destruct i; reflexivity. }
  pose proof (i_cmF _ s I c i tau T0 ltac:(rewrite Ii; reflexivity) ltac:(rewrite Ii; reflexivity)) as Ot.
  rewrite O in Ot. apply some_eq in Ot. subst tau.
  destruct (i_cmD _ s I c i t0 T0 0 ltac:(lia)
    ltac:(rewrite insF; destruct c as [|[|c]]; [| |lia]; unfold xex, xexec; simpl; destruct (ohb _ _); reflexivity)) as (t' & X & Y).
  rewrite Oj in X. apply some_eq in X. subst t'. exact Y.
Qed.

End F.

(* the store of a context's last slot, which writes r = 1 read at slot 0,
   happened after slot 0: for the free value 0 it writes 0 *)
Lemma depF : forall s c k cl, run OWNF s -> done OWNF s -> (c = 0 /\ k = 2 /\ cl = 1 \/ c = 1 /\ k = 1 /\ cl = 0) ->
  rg (cs s c) 0 = 1 -> forall tj tk, oc (cs s c) 0 = Some tj -> oc (cs s c) k = Some tk -> tj < tk.
Proof.
  intros s c k cl R CP Hc A0 tj tk Oj Ok. pose proof (Inv1_run _ s R) as I. pose proof W_F as W.
  destruct (Nat.lt_trichotomy tj tk) as [L|[L|L]]; auto; exfalso.
  - subst. destruct (i_oc _ s I c 0 tk Oj) as (e1 & A1 & B1 & C1). destruct (i_oc _ s I c k tk Ok) as (e2 & A2 & B2 & C2).
    rewrite A1 in A2. apply some_eq in A2. subst. destruct Hc as [(_ & Hk & _)|(_ & Hk & _)]; lia.
  - destruct (early_of OWNF s c 0 k tj tk R ltac:(destruct Hc as [(_ & -> & _)|(_ & -> & _)]; lia) Oj Ok L)
      as (cc0 & pc0 & N0 & B0 & d & e & Es & A & Bx & C & Ok' & D & Lp & Nj & E & F & G & Pn & Phh).
    assert (P0 : pc0 = 0) by lia. subst pc0.
    assert (Lk : k < pcs s c) by (apply (passed OWNF s R CP W c k); congruence).
    destruct (proj1 (i_cmA _ s I c k) Lk) as (tau & T0).
    rewrite (proj2 (i_set _ s I c k tau T0)), insF in D.
    (* nothing of the context happened before the early store *)
    assert (Hn : forall i, oc cc0 i = None).
    { intros i. destruct (oc cc0 i) as [t0|] eqn:O; [exfalso|reflexivity].
      destruct (E i t0 O) as (O' & _ & L').
      destruct Hc as [(-> & -> & _)|(-> & -> & _)].
      - destruct i as [|[|[|i]]].
        + rewrite Oj in O'. apply some_eq in O'. subst. lia.
        + (* x = 1 is tied to r1 = x, so it is later *)
          assert (Tie : bt s 0 0 < bt s 0 1).
          { apply (n_tie OWNF s R CP W 0 0 1 _ _ ltac:(lia) eq_refl eq_refl eq_refl eq_refl
              ltac:(apply (tied_cell _ _ 0); cbn; auto) ltac:(rewrite insF; discriminate)). }
          unfold bt, tmo in Tie. rewrite Oj, O' in Tie. lia.
        + rewrite Ok in O'. apply some_eq in O'. subst. lia.
        + pose proof (past_lateF s R CP 0 (S (S (S i))) t0 tj ltac:(lia) ltac:(cbn; lia) O' Oj). lia.
      - destruct i as [|[|i]].
        + rewrite Oj in O'. apply some_eq in O'. subst. lia.
        + rewrite Ok in O'. apply some_eq in O'. subst. lia.
        + pose proof (past_lateF s R CP 1 (S (S i)) t0 tj ltac:(lia) ltac:(cbn; lia) O' Oj). lia. }
    assert (Dd : d = DSt Plain [cl] 1).
    { destruct Hc as [(-> & -> & ->)|(-> & -> & ->)]; simpl in D; cbv [RG] in D; rewrite A0 in D;
        apply some_eq in D; subst; reflexivity. }
    subst d.
    set (f0 := fun (_ : nat) (_ : cell) => 0).
    assert (Pl : exists j', eof (ins OWNF c j' (creg OWNF c cc0 0 N0 (bor (bd cc0) B0) f0))
                                (creg OWNF c cc0 0 N0 (bor (bd cc0) B0) f0) = Some (DSt Plain [cl] 1)).
    { destruct Ok' as [Ok'|(T1 & mh & xsh & Ok')].
      - destruct (Ok' f0) as (j' & _ & Fj' & _). cbv zeta in Fj'. exists j'. apply (first_at_eof _ _ _ _ _ _ _ _ Fj').
      - destruct (Ok' f0) as (j' & _ & _ & Dj & _). cbv zeta in Dj. exists j'. exact Dj. }
    destruct Pl as (j' & Dj). rewrite insF in Dj.
    destruct Hc as [(-> & -> & ->)|(-> & -> & ->)].
    + assert (R0 : creg OWNF 0 cc0 0 N0 (bor (bd cc0) B0) f0 0 = 0) by exact (r0_freeF 0 cc0 N0 _ f0 0 eq_refl Hn).
      destruct j' as [|[|[|j']]]; simpl in Dj; try discriminate.
      * cbv [RG] in Dj. rewrite R0 in Dj. discriminate.
      * destruct j'; discriminate.
    + assert (R0 : creg OWNF 1 cc0 0 N0 (bor (bd cc0) B0) f0 0 = 0) by exact (r0_freeF 1 cc0 N0 _ f0 1 eq_refl Hn).
      destruct j' as [|[|j']]; simpl in Dj; try discriminate.
      * cbv [RG] in Dj. rewrite R0 in Dj. discriminate.
      * destruct j'; discriminate.
Qed.

Lemma OwnFuture_run : forall s, run OWNF s -> done OWNF s -> ~ (rg (cs s 0) 0 = 1 /\ rg (cs s 1) 0 = 1).
Proof.
  intros s R CP (A0 & B0). pose proof W_F as W. pose proof (Inv1_run _ s R) as I.
  (* slots 0 .. 2 of T0 and 0 .. 1 of T1 happened *)
  assert (O : forall c k, k < length (nth c CODEF []) -> oc (cs s c) k = Some (bt s c k)).
  { intros c k Lk. unfold bt, tmo. destruct (oc (cs s c) k) eqn:Oc; auto. exfalso.
    assert (Lc : c < 2) by (destruct (Nat.lt_ge_cases c 2) as [Lc|Gc]; [exact Lc|rewrite nth_overflow in Lk by (cbn; lia); cbn in Lk; lia]).
    assert (X : executes (ins OWNF c k (rrg s c)) (rrg s c) = true).
    { rewrite insF. destruct c as [|[|c]]; [| |lia]; cbn in Lk; (destruct k as [|[|[|k]]]; [| | |lia]);
        try lia; reflexivity. }
    apply (happened OWNF s R CP W c k ltac:(rewrite insF; destruct c as [|[|c]]; [| |lia]; cbn in Lk;
        (destruct k as [|[|[|k]]]; [| | |lia]); try lia; discriminate) k (le_n k) X);
      [rewrite insF; destruct c as [|[|c]]; [| |lia]; cbn in Lk; (destruct k as [|[|[|k]]]; [| | |lia]); try lia; reflexivity
      |exact Oc]. }
  destruct (n_ent OWNF s R CP W 0 0 _ eq_refl ltac:(rewrite insF; discriminate) eq_refl) as (E00 & RE00 & Ei00).
  (* r1 = 1 took a write of x of value 1, earlier than the read *)
  destruct (readv OWNF s R CP W 0 0 _ 0 E00 1 eq_refl eq_refl eq_refl RE00 Ei00 A0 ltac:(lia))
    as (y & _ & Vy & Iy & Ly).
  pose proof (n_wr_of OWNF s R CP W 0 y Iy) as WO. which_writer WO.
  - (* T0's own x = 1: tied to the read, so later *)
    subst y. assert (Tie : bt s 0 0 < bt s 0 1).
    { apply (n_tie OWNF s R CP W 0 0 1 _ _ ltac:(lia) eq_refl eq_refl eq_refl eq_refl
        ltac:(apply (tied_cell _ _ 0); cbn; auto) ltac:(rewrite insF; discriminate)). }
    lia.
  - (* T1's x = r3: r3 = 1 took T0's y = r1 *)
    subst y. destruct (n_ent OWNF s R CP W 1 0 _ eq_refl ltac:(rewrite insF; discriminate) eq_refl) as (E10 & RE10 & Ei10).
    destruct (readv OWNF s R CP W 1 0 _ 1 E10 1 eq_refl eq_refl eq_refl RE10 Ei10 B0 ltac:(lia))
      as (y & _ & Vy' & Iy' & Ly').
    pose proof (n_wr_of OWNF s R CP W 1 y Iy') as WO. which_writer WO. subst y.
    pose proof (depF s 0 2 1 R CP ltac:(auto) A0 _ _ (O 0 0 ltac:(cbn; lia)) (O 0 2 ltac:(cbn; lia))) as D0.
    pose proof (depF s 1 1 0 R CP ltac:(auto) B0 _ _ (O 1 0 ltac:(cbn; lia)) (O 1 1 ltac:(cbn; lia))) as D1.
    lia.
Qed.

Theorem OwnFuture_forbidden_Q : forall s, runQ OWNF s -> done OWNF s -> ~ (rg (cs s 0) 0 = 1 /\ rg (cs s 1) 0 = 1).
Proof. intros s R CP. exact (OwnFuture_run s (runQ_cf_run OWNF s CF_F R) CP). Qed.
