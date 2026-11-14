(* Oracle rows CoRWlate and CoRWearly (oracle/ORACLE.md), excluded, on M2DQ.
     T0: r1 = x; if r1 != 0 { x = 2; y = 1 }
     T1: r2 = y; if r2 == 1 { x = 1 }; x = 3
     T2: r3 = x; r4 = x
   CoRWlate: r1 = 1, r2 = 1, r3 = 2, r4 = 3; CoRWearly: r1 = 1, r2 = 1,
   r3 = 3, r4 = 2. Cells: x = 0, y = 1. Both need r1 = 1 and r2 = 1, which
   no finished run has (CORW_r1r2):
   r1 = 1 reads T1's x = 1, which comes only when r2 = 1; r2 = 1 reads T0's
   y = 1, which comes only when r1 != 0. Neither conditional store can happen
   before the read it depends on: for the free value 0 (T0) or for some free
   value (T1) the store is not the same. The four accesses would form a cycle
   in time.
   The programme has no CAS, so a run of M2DQ is a run of M2Model
   (runQ_cf_run), and the proof is on M2Model's runs. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2Comp M2Lit M2Neg M2Oota M2Snap M2Ev M2Cont M2LitNeg M2CasFwd.
Require Import M2DA M2DP M2DQ.

(* a programme with no CAS: every step of M2DQ is a step of M2Model *)
Lemma runQ_cf_run : forall p s, cas_free p -> runQ p s -> run p s.
Proof.
  intros p s CF RQ. induction RQ as [|s t RQ IH S]; [constructor|].
  destruct S as [s t S _|s c k B Ok _|s c j k B _ _ Ok].
  - exact (rS p s t IH S).
  - exfalso. destruct Ok as (_ & Hh & _). exact (Hh (cf_noh p CF s IH c k)).
  - exfalso. destruct Ok as (_ & Hh & _). exact (Hh (cf_noh p CF s IH c k)).
Qed.

Lemma some_eq : forall A (a b : A), Some a = Some b -> a = b.
Proof. congruence. Qed.

(* no read alone is placed at a load *)
Lemma hpa_ld : forall p c cc pc N r j m xs cnd, ins p c j r = ILd m xs cnd -> hpend_at p c cc pc N r j = None.
Proof.
  intros p c cc pc N r j m xs cnd H. unfold hpend_at.
  generalize (seq pc (N - pc)). intros l0.
  match goal with |- find ?P _ = None =>
    assert (Hf : forall a, P a = false);
    [|induction l0 as [|a l0 IH]; simpl; [reflexivity|]; rewrite Hf; exact IH] end.
  intros a. cbn beta. destruct (oc cc a), (oh cc a) as [t|]; auto. destruct (casx (ai cc a)) as [[mh xh]|]; auto.
  cbn [fab]. rewrite H. simpl. rewrite andb_false_r. reflexivity.
Qed.

Definition CODEW : list (list instr) :=
  [ [ld 0; ISt Plain [0] (NE 0 0) (K 2); ISt Plain [1] (NE 0 0) (K 1)];
    [ld 1; ISt Plain [0] (EQ 0 1) (K 1); st 0 3];
    [ld 0; ld 0] ].
Definition CORWE : prog := stat CODEW.

Lemma insW : forall c k r, ins CORWE c k r = nth k (nth c CODEW []) INop.
Proof. intros. apply ins_stat. Qed.

Lemma W_W : wf CORWE.
Proof. wf_tac. Qed.

Lemma CF_W : cas_free CORWE.
Proof.
  intros c k r. rewrite insW. destruct c as [|[|[|c]]]; [| | |destruct c; destruct k; reflexivity];
    (destruct k as [|[|[|k]]]; simpl; try reflexivity; destruct k; reflexivity).
Qed.

(* with nothing of the context happened, the mill part of a first load is its free value *)
Lemma r0_freeW : forall c cc N B f x, nth 0 (nth c CODEW []) INop = ILd Plain [x] T -> (forall k, oc cc k = None) ->
  creg CORWE c cc 0 N B f 0 = f 0 x.
Proof.
  intros c cc N B f x H Hn. rewrite creg_bl. unfold slotv. simpl. rewrite insW, H. simpl.
  rewrite (pend_none CORWE c cc N _ 0 Hn).
  rewrite (hpa_ld CORWE c cc 0 N _ 0 Plain [x] T ltac:(rewrite insW, H; reflexivity)). reflexivity.
Qed.

Section W.
Variable s : M2Model.st.
Hypothesis R : run CORWE s.
Hypothesis CP : done CORWE s.
Local Abbreviation W := W_W.

(* a slot past the code of T0 or T1 (no instruction) happened when it was passed, after slot 0 *)
Lemma past_lateW : forall c i t0 tj, c < 2 -> 3 <= i -> oc (cs s c) i = Some t0 -> oc (cs s c) 0 = Some tj -> tj <= t0.
Proof.
  intros c i t0 tj Lc Li O Oj. pose proof (Inv1_run _ s R) as I.
  assert (Lp : i < pcs s c) by (apply (passed CORWE s R CP W c i); congruence).
  destruct (proj1 (i_cmA _ s I c i) Lp) as (tau & T0).
  assert (Ii : ins CORWE c i (rg (cs s c)) = INop).
  { rewrite insW. destruct c as [|[|c]]; [| |lia]; simpl; do 3 (destruct i as [|i]; [lia|]); destruct i; reflexivity. }
  pose proof (i_cmF _ s I c i tau T0 ltac:(rewrite Ii; reflexivity) ltac:(rewrite Ii; reflexivity)) as Ot.
  rewrite O in Ot. apply some_eq in Ot. subst tau.
  destruct (i_cmD _ s I c i t0 T0 0 ltac:(lia)
    ltac:(rewrite insW; destruct c as [|[|c]]; [| |lia]; unfold xex, xexec; simpl; destruct (ohb _ _); reflexivity)) as (t' & X & Y).
  rewrite Oj in X. apply some_eq in X. subst t'. exact Y.
Qed.

End W.

Ltac snap_none R CP Oj Mn E Hc :=
  let i := fresh "i" in let t0 := fresh "t0" in let O := fresh "O" in let O' := fresh "O'" in let L' := fresh "L'" in
  intros i; destruct (oc _ i) as [t0|] eqn:O; auto; exfalso;
  destruct (E i t0 O) as (O' & _ & L');
  destruct i as [|[|[|i]]];
  [rewrite Oj in O'; apply some_eq in O'; subst; lia
  |pose proof (Mn 1 t0 ltac:(auto) O'); lia
  |pose proof (Mn 2 t0 ltac:(auto) O'); lia
  |pose proof (past_lateW _ R CP _ (S (S (S i))) t0 _ Hc ltac:(lia) O' Oj); lia].

(* the first event of T0 at slot 1 or 2 happened after r1 = x: for the free
   value 0 neither store comes *)
Lemma depW0 : forall s, run CORWE s -> done CORWE s -> rg (cs s 0) 0 = 1 ->
  forall k tj tk, (k = 1 \/ k = 2) -> oc (cs s 0) 0 = Some tj -> oc (cs s 0) k = Some tk ->
  (forall k' t', (k' = 1 \/ k' = 2) -> oc (cs s 0) k' = Some t' -> tk <= t') -> tj < tk.
Proof.
  intros s R CP A0 k tj tk Hk Oj Ok Mn. pose proof (Inv1_run _ s R) as I. pose proof W_W as W.
  destruct (Nat.lt_trichotomy tj tk) as [L|[L|L]]; auto; exfalso.
  - subst. destruct (i_oc _ s I 0 0 tk Oj) as (e1 & A1 & B1 & C1). destruct (i_oc _ s I 0 k tk Ok) as (e2 & A2 & B2 & C2).
    rewrite A1 in A2. apply some_eq in A2. subst. lia.
  - destruct (early_of CORWE s 0 0 k tj tk R ltac:(lia) Oj Ok L)
      as (cc0 & pc0 & N0 & B0 & d & e & Es & A & Bx & C & Ok' & D & Lp & Nj & E & F & G & Pn & Phh).
    assert (P0 : pc0 = 0) by lia. subst pc0.
    assert (Lk : k < pcs s 0) by (apply (passed CORWE s R CP W 0 k); congruence).
    destruct (proj1 (i_cmA _ s I 0 k) Lk) as (tau & T0).
    rewrite (proj2 (i_set _ s I 0 k tau T0)), insW in D.
    assert (Hn : forall i, oc cc0 i = None) by snap_none R CP Oj Mn E (ltac:(lia) : 0 < 2).
    assert (R0 : forall N1 B1 f1, creg CORWE 0 cc0 0 N1 B1 f1 0 = f1 0 0).
    { intros N1 B1 f1. apply (r0_freeW 0 cc0 N1 B1 f1 0 eq_refl Hn). }
    assert (Dd : d = DSt Plain [0] 2 \/ d = DSt Plain [1] 1)
      by (destruct Hk as [-> | ->]; simpl in D; unfold NE, K in D; rewrite A0 in D; simpl in D; apply some_eq in D; subst; auto).
    set (f0 := fun (_ : nat) (_ : cell) => 0).
    assert (Pl : exists j', eof (ins CORWE 0 j' (creg CORWE 0 cc0 0 N0 (bor (bd cc0) B0) f0))
                                (creg CORWE 0 cc0 0 N0 (bor (bd cc0) B0) f0) = Some d).
    { destruct Ok' as [Ok'|(T1 & mh & xsh & Ok')].
      - destruct (Ok' f0) as (j' & _ & Fj' & _). cbv zeta in Fj'. exists j'. apply (first_at_eof _ _ _ _ _ _ _ _ Fj').
      - destruct (Ok' f0) as (j' & _ & _ & Dj & _). cbv zeta in Dj. exists j'. exact Dj. }
    destruct Pl as (j' & Dj). rewrite insW in Dj.
    destruct j' as [|[|[|j']]]; simpl in Dj.
    + destruct Dd as [-> | ->]; discriminate.
    + unfold NE in Dj. rewrite R0 in Dj. discriminate.
    + unfold NE in Dj. rewrite R0 in Dj. discriminate.
    + destruct j'; discriminate.
Qed.

(* the first event of T1 at slot 1 or 2 happened after r2 = y: x = 1 does
   not come for the free value 0; x = 3 is tied to x = 1, which comes for
   the free value 1 and has not happened *)
Lemma depW1 : forall s, run CORWE s -> done CORWE s -> rg (cs s 1) 0 = 1 ->
  forall k tj tk, (k = 1 \/ k = 2) -> oc (cs s 1) 0 = Some tj -> oc (cs s 1) k = Some tk ->
  (forall k' t', (k' = 1 \/ k' = 2) -> oc (cs s 1) k' = Some t' -> tk <= t') -> tj < tk.
Proof.
  intros s R CP B0 k tj tk Hk Oj Ok Mn. pose proof (Inv1_run _ s R) as I. pose proof W_W as W.
  destruct (Nat.lt_trichotomy tj tk) as [L|[L|L]]; auto; exfalso.
  - subst. destruct (i_oc _ s I 1 0 tk Oj) as (e1 & A1 & B1 & C1). destruct (i_oc _ s I 1 k tk Ok) as (e2 & A2 & B2 & C2).
    rewrite A1 in A2. apply some_eq in A2. subst. lia.
  - destruct (early_of CORWE s 1 0 k tj tk R ltac:(lia) Oj Ok L)
      as (cc0 & pc0 & N0 & Bz & d & e & Es & A & Bx & C & Ok' & D & Lp & Nj & E & F & G & Pn & Phh).
    assert (P0 : pc0 = 0) by lia. subst pc0.
    assert (Lk : k < pcs s 1) by (apply (passed CORWE s R CP W 1 k); congruence).
    destruct (proj1 (i_cmA _ s I 1 k) Lk) as (tau & T0).
    rewrite (proj2 (i_set _ s I 1 k tau T0)), insW in D.
    assert (Hn : forall i, oc cc0 i = None) by snap_none R CP Oj Mn E (ltac:(lia) : 1 < 2).
    assert (R0 : forall N1 B1 f1, creg CORWE 1 cc0 0 N1 B1 f1 0 = f1 0 1).
    { intros N1 B1 f1. apply (r0_freeW 1 cc0 N1 B1 f1 1 eq_refl Hn). }
    destruct Hk as [Hk1 | Hk1]; subst k.
    + (* x = 1: for the free value 0 it does not come *)
      simpl in D. unfold EQ, K in D. rewrite B0 in D. simpl in D. apply some_eq in D. subst d.
      set (f0 := fun (_ : nat) (_ : cell) => 0).
      assert (Pl : exists j', eof (ins CORWE 1 j' (creg CORWE 1 cc0 0 N0 (bor (bd cc0) Bz) f0))
                                  (creg CORWE 1 cc0 0 N0 (bor (bd cc0) Bz) f0) = Some (DSt Plain [0] 1)).
      { destruct Ok' as [Ok'|(T1 & mh & xsh & Ok')].
        - destruct (Ok' f0) as (j' & _ & Fj' & _). cbv zeta in Fj'. exists j'. apply (first_at_eof _ _ _ _ _ _ _ _ Fj').
        - destruct (Ok' f0) as (j' & _ & _ & Dj & _). cbv zeta in Dj. exists j'. exact Dj. }
      destruct Pl as (j' & Dj). rewrite insW in Dj.
      destruct j' as [|[|[|j']]]; simpl in Dj; try discriminate.
      * unfold EQ in Dj. rewrite R0 in Dj. discriminate.
      * destruct j'; discriminate.
    + (* x = 3: its place passes x = 1, which comes for the free value 1 *)
      simpl in D. apply some_eq in D. subst d.
      destruct Ok' as [Ok'|(T1 & mh & xsh & Ok')].
      2:{ exfalso. destruct (Ok' (fun _ _ => 0)) as (j' & _ & Fr & Dj & _). cbv zeta in Dj, Fr.
          pose proof (first_atR_eofR _ _ _ _ _ _ _ _ _ Fr) as Rj. rewrite insW in Dj, Rj.
          destruct j' as [|[|[|j']]]; simpl in Dj, Rj; try discriminate. destruct j'; discriminate. }
      set (f0 := fun (_ : nat) (_ : cell) => 1).
      destruct (Ok' f0) as (j' & _ & Fj' & _). cbv zeta in Fj'.
      set (r := creg CORWE 1 cc0 0 N0 (bor (bd cc0) Bz) f0) in *.
      pose proof (first_at_eof _ _ _ _ _ _ _ _ Fj') as Dj. rewrite insW in Dj.
      assert (Ej : j' = 2).
      { destruct j' as [|[|[|j']]]; simpl in Dj; try discriminate; [|reflexivity|destruct j'; discriminate].
        unfold EQ in Dj. destruct (Nat.eqb (r 0) 1); discriminate. }
      subst j'.
      assert (Tk : taken CORWE 1 cc0 0 r tk 1).
      { apply (first_at_before _ _ _ _ _ _ _ _ Fj' 1); [lia|lia| | |].
        - rewrite insW. simpl. unfold executes, icond, ieval, EQ. simpl. unfold r. rewrite R0. reflexivity.
        - intros v (kh & th & mh & xh & (P1 & P2 & P3) & Oh & Lt & Hl & Fh & Ev).
          exfalso. destruct (Phh kh th Oh) as (Oh' & _). rewrite (cf_noh CORWE CF_W s R 1 kh) in Oh'. discriminate.
        - rewrite insW. left. exists 0. split; left; reflexivity. }
      destruct Tk as (k3 & t3 & d3 & (_ & P3 & _) & O3 & _). rewrite Hn in O3. discriminate.
Qed.

(* the earlier of slots 1 and 2 of a context, both happened, is after slot 0 *)
Lemma min12 : forall (o : nat -> option nat) t0 t1 t2,
  o 0 = Some t0 -> o 1 = Some t1 -> o 2 = Some t2 ->
  (forall k tk, (k = 1 \/ k = 2) -> o k = Some tk ->
     (forall k' t', (k' = 1 \/ k' = 2) -> o k' = Some t' -> tk <= t') -> t0 < tk) ->
  t0 < t1 /\ t0 < t2.
Proof.
  intros o t0 t1 t2 O0 O1 O2 Dp.
  assert (Mn : forall k' t', (k' = 1 \/ k' = 2) -> o k' = Some t' -> Nat.min t1 t2 <= t').
  { intros k' t' [-> | ->] O; [rewrite O1 in O|rewrite O2 in O]; apply some_eq in O; subst; lia. }
  destruct (Nat.le_ge_cases t1 t2) as [X|X].
  - pose proof (Dp 1 t1 (or_introl eq_refl) O1 ltac:(intros k' t' Hk O; pose proof (Mn k' t' Hk O); lia)). lia.
  - pose proof (Dp 2 t2 (or_intror eq_refl) O2 ltac:(intros k' t' Hk O; pose proof (Mn k' t' Hk O); lia)). lia.
Qed.

Lemma CORW_r1r2 : forall s, run CORWE s -> done CORWE s -> ~ (rg (cs s 0) 0 = 1 /\ rg (cs s 1) 0 = 1).
Proof.
  intros s R CP (A0 & B0). pose proof W_W as W. pose proof (Inv1_run _ s R) as I.
  destruct (n_ent CORWE s R CP W 0 0 _ eq_refl ltac:(rewrite insW; discriminate) eq_refl) as (E00 & RE00 & Ei00).
  destruct (n_ent CORWE s R CP W 1 0 _ eq_refl ltac:(rewrite insW; discriminate) eq_refl) as (E10 & RE10 & Ei10).
  (* r1 = 1 took T1's x = 1; r2 = 1 took T0's y = 1 *)
  destruct (readv CORWE s R CP W 0 0 _ 0 E00 1 eq_refl eq_refl eq_refl RE00 Ei00 A0 ltac:(lia))
    as (y & _ & Vy & Iy & Ly).
  pose proof (n_wr_of CORWE s R CP W 0 y Iy) as WO. which_writer WO. subst y.
  destruct (readv CORWE s R CP W 1 0 _ 1 E10 1 eq_refl eq_refl eq_refl RE10 Ei10 B0 ltac:(lia))
    as (y & _ & Vy' & Iy' & Ly').
  pose proof (n_wr_of CORWE s R CP W 1 y Iy') as WO. which_writer WO. subst y.
  (* slots 0, 1 and 2 of T0 and T1 happened *)
  assert (O : forall c k, c < 2 -> k < 3 -> oc (cs s c) k = Some (bt s c k)).
  { intros c k Lc Lk. unfold bt, tmo. destruct (oc (cs s c) k) eqn:Oc; auto. exfalso.
    assert (X : executes (ins CORWE c k (rrg s c)) (rrg s c) = true).
    { unfold rrg. rewrite insW. destruct c as [|[|c]]; [| |lia]; (destruct k as [|[|[|k]]]; [| | |lia]);
        simpl; unfold executes, icond, ieval, NE, EQ, T; simpl; rewrite ?A0, ?B0; reflexivity. }
    apply (happened CORWE s R CP W c 2 ltac:(rewrite insW; destruct c as [|[|c]]; [discriminate|discriminate|lia]) k ltac:(lia) X);
      [rewrite insW; destruct c as [|[|c]]; [| |lia]; (destruct k as [|[|[|k]]]; [| | |lia]); reflexivity|exact Oc]. }
  destruct (min12 (oc (cs s 0)) _ _ _ (O 0 0 ltac:(lia) ltac:(lia)) (O 0 1 ltac:(lia) ltac:(lia)) (O 0 2 ltac:(lia) ltac:(lia))
              (fun k tk Hk Ok Mn => depW0 s R CP A0 k _ tk Hk (O 0 0 ltac:(lia) ltac:(lia)) Ok Mn)) as (_ & D0).
  destruct (min12 (oc (cs s 1)) _ _ _ (O 1 0 ltac:(lia) ltac:(lia)) (O 1 1 ltac:(lia) ltac:(lia)) (O 1 2 ltac:(lia) ltac:(lia))
              (fun k tk Hk Ok Mn => depW1 s R CP B0 k _ tk Hk (O 1 0 ltac:(lia) ltac:(lia)) Ok Mn)) as (D1 & _).
  lia.
Qed.

Theorem CoRWlate_forbidden_Q : forall s, runQ CORWE s -> done CORWE s ->
  ~ (rg (cs s 0) 0 = 1 /\ rg (cs s 1) 0 = 1 /\ rg (cs s 2) 0 = 2 /\ rg (cs s 2) 1 = 3).
Proof. intros s R CP (A & B & _). exact (CORW_r1r2 s (runQ_cf_run CORWE s CF_W R) CP (conj A B)). Qed.

Theorem CoRWearly_forbidden_Q : forall s, runQ CORWE s -> done CORWE s ->
  ~ (rg (cs s 0) 0 = 1 /\ rg (cs s 1) 0 = 1 /\ rg (cs s 2) 0 = 3 /\ rg (cs s 2) 1 = 2).
Proof. intros s R CP (A & B & _). exact (CORW_r1r2 s (runQ_cf_run CORWE s CF_W R) CP (conj A B)). Qed.
