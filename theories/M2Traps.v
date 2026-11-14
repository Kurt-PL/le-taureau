(* Model2: the strong-DRF traps, race-free programmes whose bad outcome is
   not SC. A store that the R1 of Model2 cannot move above the read that
   decides whether it comes. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2Comp M2Lit M2Neg M2Oota M2LitNeg M2Snap M2Ev M2NegQ M2Cont.

(* the decidable place is an instruction with that effect *)
Lemma fab_dof : forall p c cc pc N r n T d j, fab p c cc pc N r n T (TF d) j = true -> eof (ins p c j r) r = Some d.
Proof.
  intros p c cc pc N r n T d j H. destruct n as [|n]; [discriminate|]. cbn [fab] in H.
  repeat (apply andb_true_iff in H as [H ?]).
  match goal with X : tatb _ _ _ = true |- _ => revert X end. unfold tatb.
  destruct (eof (ins p c j r) r) as [d'|]; simpl; [|discriminate]. intros X. f_equal. apply desc_eqb_eq. exact X.
Qed.

Lemma fbind_none : forall p c r i x b, (forall b', b' < b -> ~ In x (icells (ins p c b' r))) ->
  fbind p c r i x b = None.
Proof.
  intros p c r i x b. induction b as [|b IH]; intros H; simpl; auto.
  destruct (executes (ins p c b r) r && tiedb (ins p c b r) i); [|apply IH; intros; apply H; lia].
  destruct (existsb (Nat.eqb x) (icells (ins p c b r))) eqn:X; [|reflexivity].
  exfalso. apply (H b ltac:(lia)). apply existsb_exists in X. destruct X as (y & Hy & Q). apply Nat.eqb_eq in Q. subst. auto.
Qed.

(* a store whose condition reads register j of a load that is the only load
   of its cell, with no access to that cell before it, happens after that
   load *)
Section Ctrl.
Variables (P : list (list instr)) (s : M2Model.st) (c j k : nat) (x y : cell) (v w : val).
Hypothesis R : run (stat P) s.
Hypothesis CP : done (stat P) s.
Hypothesis W : wf (stat P).
Local Abbreviation code := (nth c P []).
Hypothesis Hj : nth j code INop = ILd Plain [x] T.
Hypothesis Hk : nth k code INop = ISt Plain [y] (EQ j v) (K w).
Hypothesis Hv : v <> 0.
Hypothesis Uld : forall i m cnd, nth i code INop = ILd m [x] cnd -> i = j.
Hypothesis Nb : forall i, i < j -> ~ In x (icells (nth i code INop)).
(* any other store to y is behind a guard() after the load *)
Hypothesis Ust : forall i m cnd vv, nth i code INop = ISt m [y] cnd vv ->
  i = k \/ exists f, j < f < i /\ nth f code INop = IFn FFull.
Hypothesis Ljk : j < k.

Lemma ctrl_dep : oc (cs s c) j <> None -> oc (cs s c) k <> None -> bt s c j < bt s c k.
Proof.
  intros Oj Ok. destruct (oc (cs s c) j) as [tj|] eqn:Ej; [|congruence].
  destruct (oc (cs s c) k) as [tk|] eqn:Ek; [|congruence].
  unfold bt, tmo. rewrite Ej, Ek. destruct (Nat.lt_trichotomy tj tk) as [L|[L|L]]; auto; exfalso.
  - subst. pose proof (Inv1_run _ s R) as I.
    destruct (i_oc _ s I c j tk Ej) as (e1 & A1 & B1 & C1). destruct (i_oc _ s I c k tk Ek) as (e2 & A2 & B2 & C2).
    rewrite A1 in A2. injection A2 as <-. lia.
  - destruct (early_of (stat P) s c j k tj tk R Ljk Ej Ek L)
      as (cc0 & pc0 & N0 & B0 & d & e & Es & A & B & C & Ok' & D & Lp & Nj & E & F & G & Pn & Phh).
    (* the access is the store of slot k *)
    assert (Lk : k < pcs s c) by (apply (passed (stat P) s R CP W); congruence).
    destruct (proj1 (i_cmA _ s (Inv1_run _ s R) c k) Lk) as (tau & T).
    rewrite (proj2 (i_set _ s (Inv1_run _ s R) c k tau T)), ins_stat, Hk in D.
    unfold eof, dof, EQ, K in D. destruct (Nat.eqb (rg (cs s c) j) v); [|discriminate]. injection D as <-.
    (* R1 at free values 0 *)
    set (f0 := fun (_ : nat) (_ : cell) => 0).
    destruct Ok' as [Ok'|(T1 & mh & xsh & Ok')].
    2:{ (* the write of a CAS is not a store *)
        exfalso. destruct (Ok' f0) as (j' & _ & Fj' & Dj' & _). cbv zeta in Fj', Dj'.
        pose proof (first_atR_eofR _ _ _ _ _ _ _ _ _ Fj') as DR.
        destruct (ins (stat P) c j' _) as [m1 x1 c1|m1 x1 c1 v1|m1 x1 c1 e1 n1| |]; simpl in DR, Dj'; try discriminate;
          destruct (c1 _); discriminate. }
    destruct (Ok' f0) as (j' & _ & Fj' & _). cbv zeta in Fj'. apply first_at_in in Fj'.
    destruct Fj' as (Pj' & Dj' & _ & Tj').
    set (r := creg (stat P) c cc0 pc0 N0 (bor (bd cc0) B0) f0) in *.
    apply eof_acc in Dj'; [|reflexivity]. rewrite ins_stat in Dj'.
    destruct (nth j' code INop) as [m1 x1 c1|m1 x1 c1 v1|m1 x1 c1 e1 n1| |] eqn:Ej'; simpl in Dj'; try discriminate;
      destruct (c1 r) eqn:Cj; try discriminate; injection Dj' as Em Ex Ev; subst m1 x1.
    destruct (Ust j' _ _ _ Ej') as [Hj'|(f & Lf & Ef)].
    2:{ (* a guard() is tied to the store and is not the place of an access *)
        exfalso. destruct (taken_dof _ _ _ _ _ _ _ (Tj' f ltac:(lia) ltac:(lia)
          ltac:(rewrite ins_stat, Ef; reflexivity) ltac:(intros vv _; rewrite ins_stat, Ef; reflexivity)
          ltac:(rewrite ins_stat, Ef; right; left; reflexivity))) as (dd & Dd).
        rewrite ins_stat, Ef in Dd. discriminate Dd. }
    subst j'. rewrite Hk in Ej'. injection Ej' as <- _.
    unfold EQ in Cj. apply Nat.eqb_eq in Cj.
    (* register j is free in the snapshot, so it takes the free value 0 *)
    assert (Rj : r j = 0).
    { unfold r. rewrite creg_bl. unfold slotv. destruct (Nat.ltb_spec j pc0); [lia|].
      rewrite ins_stat, Hj. simpl.
      destruct (pend_at _ _ _ _ _ _ _) as [kk|] eqn:Pa.
      - exfalso. destruct (pend_at_spec _ _ _ _ _ _ _ _ Pa) as (O1 & L1 & _ & tk1 & dk & _ & D1 & F1).
        destruct (Pn kk O1 L1) as (d' & Ad & Nd'). rewrite Ad, (eof_inst _ _ Nd') in D1. injection D1 as ->.
        pose proof (fab_dof _ _ _ _ _ _ _ _ _ _ F1) as D2. rewrite ins_stat, Hj in D2. simpl in D2.
        injection D2 as <-.
        pose proof (G kk _ O1 L1 Ad) as G1.
        destruct (oc cc0 kk) as [t1|] eqn:O1'; [|congruence]. destruct (E kk t1 O1') as (X1 & _ & _).
        assert (Lkk : kk < pcs s c) by (apply (passed (stat P) s R CP W); congruence).
        destruct (proj1 (i_cmA _ s (Inv1_run _ s R) c kk) Lkk) as (tau' & T').
        rewrite (proj2 (i_set _ s (Inv1_run _ s R) c kk tau' T')), ins_stat in G1.
        apply eof_acc in G1; [|reflexivity]. destruct (nth kk code INop) as [m2 x2 c2|m2 x2 c2 v2|m2 x2 c2 e2 n2| |] eqn:Ekk; simpl in G1; try discriminate;
          destruct (c2 (rg (cs s c))); try discriminate.
        injection G1 as -> ->. pose proof (Uld kk _ _ Ekk). subst kk. congruence.
      - rewrite cfx_ncas by reflexivity. destruct (hpend_at _ _ _ _ _ _ _) as [kh|] eqn:Ph.
        { exfalso. unfold hpend_at in Ph. apply find_some in Ph as (_ & Ph).
          destruct (oc cc0 kh); [discriminate|]. destruct (oh cc0 kh) as [th|]; [|discriminate].
          destruct (casx (ai cc0 kh)) as [[mh xh]|]; [|discriminate].
          cbn [fab] in Ph. repeat (apply andb_true_iff in Ph as [Ph ?]).
          match goal with X : tatb _ _ _ = true |- _ => revert X end. rewrite ins_stat, Hj. simpl. discriminate. }
        change (cellv (stat P) c cc0 pc0 N0 (bor (bd cc0) B0) f0 (lreg (bl (stat P) c cc0 pc0 N0 (bor (bd cc0) B0) f0 j)) j j x = 0).
        rewrite cellv_unb; [reflexivity|lia|rewrite ins_stat, Hj; reflexivity|exact Pa|exact Ph|].
        intros _. unfold fbinder. rewrite ins_stat, Hj. simpl.
        rewrite Nat.eqb_refl. simpl.
        rewrite fbind_none; [reflexivity|]. intros b' Lb. rewrite ins_stat. apply Nb. auto. }
    lia.
Qed.

End Ctrl.

(* trap 1: a write justified by a branch the context did not take *)
Definition TRAP1 : prog := stat [ [ld 0; ISt Plain [1] (EQ 0 1) (K 1)]; [ld 1; ISt Plain [0] (EQ 0 1) (K 1)] ].

Ltac ctrl P s R CP W c j k x y v w :=
  let H := fresh in
  assert (H : bt s c j < bt s c k);
  [apply (ctrl_dep _ s c j k x y v w R CP W);
     [reflexivity|reflexivity|lia
     |let i := fresh in let m := fresh in let cn := fresh in let Z := fresh in
      intros i m cn Z; do 6 (destruct i as [|i]; [simpl in Z; try discriminate; reflexivity|]); simpl in Z; destruct i; discriminate
     |let i := fresh in intros i ?; do 6 (destruct i as [|i]; [simpl; try lia; intro; intuition congruence|]); lia
     |let i := fresh in let m := fresh in let cn := fresh in let vv := fresh in let Z := fresh in
      intros i m cn vv Z; do 6 (destruct i as [|i]; [simpl in Z; try discriminate;
        first [left; reflexivity|right; first [exists 1; split; [lia|reflexivity]|exists 2; split; [lia|reflexivity]|exists 3; split; [lia|reflexivity]|exists 4; split; [lia|reflexivity]]]|]); simpl in Z; destruct i; discriminate
     |lia
     |apply (happened _ s R CP W c k); [nn|lia|unfold executes; simpl; unfold icond, ieval, EQ, T, K; simpl; first [reflexivity|apply Nat.eqb_eq; unfold rrg, M2Comp.rrg in *; lia]|vm_compute; reflexivity]
     |apply (happened _ s R CP W c k); [nn|lia|unfold executes; simpl; unfold icond, ieval, EQ, T, K; simpl; first [reflexivity|apply Nat.eqb_eq; unfold rrg, M2Comp.rrg in *; lia]|vm_compute; reflexivity]]|].

Theorem TRAP1_forbidden : forall s, run TRAP1 s -> done TRAP1 s -> ~ (rg (cs s 0) 0 = 1 /\ rg (cs s 1) 0 = 1).
Proof.
  intros s R CP (A & B). assert (W : wf TRAP1) by wf_tac.
  get_ent TRAP1 s R CP W 0 0 E00. get_ent TRAP1 s R CP W 1 0 E10.
  destruct (readv TRAP1 s R CP W 0 0 _ 0 E00 1 eq_refl eq_refl eq_refl H Ei A ltac:(lia)) as (y & _ & ? & Iy & Ly).
  pose proof (n_wr_of TRAP1 s R CP W 0 y Iy) as WO. which_writer WO. subst y.
  destruct (readv TRAP1 s R CP W 1 0 _ 1 E10 1 eq_refl eq_refl eq_refl H0 Ei0 B ltac:(lia)) as (y & _ & ? & Iy' & Ly').
  pose proof (n_wr_of TRAP1 s R CP W 1 y Iy') as WO. which_writer WO. subst y.
  ctrl TRAP1 s R CP W 0 0 1 0 1 1 1. ctrl TRAP1 s R CP W 1 0 1 1 0 1 1. lia.
Qed.

(* trap 2: the same store in the other branch, behind guard() *)
Definition TRAP2 : prog :=
  stat [ [ld 0; ISt Plain [1] (EQ 0 1) (K 1); ffull; ISt Plain [1] (NE 0 1) (K 1); ffull];
         [ffull; ld 1; ffull; ISt Plain [0] (EQ 1 1) (K 1)] ].
Theorem TRAP2_forbidden : forall s, run TRAP2 s -> done TRAP2 s -> ~ (rg (cs s 0) 0 = 1 /\ rg (cs s 1) 1 = 1).
Proof.
  intros s R CP (A & B). assert (W : wf TRAP2) by wf_tac.
  get_ent TRAP2 s R CP W 0 0 E00. get_ent TRAP2 s R CP W 1 1 E11.
  destruct (readv TRAP2 s R CP W 0 0 _ 0 E00 1 eq_refl eq_refl eq_refl H Ei A ltac:(lia)) as (y & _ & ? & Iy & Ly).
  pose proof (n_wr_of TRAP2 s R CP W 0 y Iy) as WO. which_writer WO. subst y.
  destruct (readv TRAP2 s R CP W 1 1 _ 1 E11 1 eq_refl eq_refl eq_refl H0 Ei0 B ltac:(lia)) as (y & _ & ? & Iy' & Ly').
  pose proof (n_wr_of TRAP2 s R CP W 1 y Iy') as WO. which_writer WO; subst y.
  - ctrl TRAP2 s R CP W 0 0 1 0 1 1 1. ctrl TRAP2 s R CP W 1 1 3 1 0 1 1. lia.
  - (* the other branch's store did not happen: r0 = 1 *)
    exfalso. rewrite (n_ew TRAP2 s R CP W 0 3 _ E0 eq_refl RE0 ltac:(destruct RE0 as (A0 & B0 & C0); rewrite (einstr_ins TRAP2 s R CP W _ E0 A0), B0, C0; reflexivity)) in Wt0.
    unfold TRAP2 in Wt0. rewrite !ins_stat in Wt0. simpl in Wt0.
    unfold icond, ieval, NE, M2Comp.rrg in Wt0. simpl in Wt0. rewrite A in Wt0. discriminate.
Qed.

(* trap 3: an imagined run that reads a stale value over its own write *)
Definition TRAP3 : prog := stat [ [st 0 1; ld 0; ISt Plain [1] (EQ 1 0) (K 1)]; [ld 1] ].
Theorem TRAP3_forbidden : forall s, run TRAP3 s -> done TRAP3 s -> evok s -> ~ rg (cs s 1) 0 = 1.
Proof.
  intros s R CP EV A. assert (W : wf TRAP3) by wf_tac.
  get_ent TRAP3 s R CP W 0 0 E00. get_ent TRAP3 s R CP W 0 1 E01. get_ent TRAP3 s R CP W 1 0 E10. NZ TRAP3 0.
  destruct (readv TRAP3 s R CP W 1 0 _ 1 E10 1 eq_refl eq_refl eq_refl H1 Ei1 A ltac:(lia)) as (y & _ & ? & Iy & Ly).
  pose proof (n_wr_of TRAP3 s R CP W 1 y Iy) as WO. which_writer WO. subst y.
  rewrite (n_ew TRAP3 s R CP W 0 2 _ E eq_refl RE ltac:(destruct RE as (A0 & B0 & C0); rewrite (einstr_ins TRAP3 s R CP W _ E A0), B0, C0; reflexivity)) in Wt.
  unfold TRAP3 in Wt. rewrite !ins_stat in Wt. simpl in Wt.
  unfold icond, ieval, EQ, M2Comp.rrg in Wt. simpl in Wt. rewrite ?andb_true_r in Wt. apply Nat.eqb_eq in Wt.
  destruct (stw TRAP3 s R CP W 0 0 _ _ _ _ E00 eq_refl eq_refl H Ei) as (_ & I00 & S00).
  pose proof (read0 TRAP3 s R CP W 0 1 _ 0 E01 eq_refl eq_refl eq_refl H0 Ei0 Wt H2) as N1.
  apply (c2 TRAP3 s R CP W EV 0 (bt s 0 0) (bt s 0 1)).
  - apply (c_po TRAP3 s R CP W EV 0 0 1 (st 0 1) (ld 0) E00 E01 0 ltac:(lia) eq_refl eq_refl H H0 Ei Ei0 eq_refl eq_refl
             (or_introl eq_refl) (or_introl eq_refl)).
  - apply (c_missed TRAP3 s R CP W EV 0 1 (ld 0) 0 E01 (bt s 0 0) eq_refl eq_refl (or_introl eq_refl) H0 Ei0 I00);
      [apply (neq_bt TRAP3 s R CP W 0 0 0 1 _ _ eq_refl ltac:(nn) eq_refl eq_refl ltac:(nn) eq_refl); congruence|left; exact N1].
Qed.

(* trap 4: several contexts' justifications combined *)
Definition TRAP4 : prog :=
  stat [ [ld 0; ISt Plain [1] (EQ 0 1) (K 1)]; [ld 1; ISt Plain [2] (EQ 0 1) (K 1)]; [ld 2; ISt Plain [0] (EQ 0 1) (K 1)] ].
Theorem TRAP4_forbidden : forall s, run TRAP4 s -> done TRAP4 s ->
  ~ (rg (cs s 0) 0 = 1 /\ rg (cs s 1) 0 = 1 /\ rg (cs s 2) 0 = 1).
Proof.
  intros s R CP (A & B & C). assert (W : wf TRAP4) by wf_tac.
  get_ent TRAP4 s R CP W 0 0 E00. get_ent TRAP4 s R CP W 1 0 E10. get_ent TRAP4 s R CP W 2 0 E20.
  destruct (readv TRAP4 s R CP W 0 0 _ 0 E00 1 eq_refl eq_refl eq_refl H Ei A ltac:(lia)) as (y & _ & ? & Iy & Ly).
  pose proof (n_wr_of TRAP4 s R CP W 0 y Iy) as WO. which_writer WO. subst y.
  destruct (readv TRAP4 s R CP W 1 0 _ 1 E10 1 eq_refl eq_refl eq_refl H0 Ei0 B ltac:(lia)) as (y & _ & ? & Iy' & Ly').
  pose proof (n_wr_of TRAP4 s R CP W 1 y Iy') as WO. which_writer WO. subst y.
  destruct (readv TRAP4 s R CP W 2 0 _ 2 E20 1 eq_refl eq_refl eq_refl H1 Ei1 C ltac:(lia)) as (y & _ & ? & Iy'' & Ly'').
  pose proof (n_wr_of TRAP4 s R CP W 2 y Iy'') as WO. which_writer WO. subst y.
  ctrl TRAP4 s R CP W 0 0 1 0 1 1 1. ctrl TRAP4 s R CP W 1 0 1 1 2 1 1. ctrl TRAP4 s R CP W 2 0 1 2 0 1 1. lia.
Qed.
