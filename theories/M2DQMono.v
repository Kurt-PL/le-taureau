(* M2Mono.v re-checked on M2DQ (stepQ) through M2DQShim; scripts as in M2Mono.v except where marked DQ. *)
(* Model2: the registers R1 considers, constrained on a prefix of slots. A
   register function r is a continuation of a context's state up to J
   (ccJ) when it agrees with the state on the slots before the next
   instruction, leaves 0 where no read comes, gives every pending access
   placed before J its value, and every read counted on, placed before J,
   its binder's value.

   - ccJ_agree: such registers are the model's registers (creg) up to J.
   - mono_step: a continuation of a later state is a continuation of an
     earlier one (R1 only adds constraints as a run goes on). *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2Oota M2Cont M2DQEquiv M2Snap M2Trace M2DA M2DP M2DQ M2DQInv M2DQIface M2DQTrace M2DQTr M2DQShim.

Definition ccJ (p : prog) (c : nat) (cc : cst) (pc : nat) (B : nat -> bool) (r : regs) (J : nat) : Prop :=
  pc <= J /\
  (forall j, j < pc -> r j = rg cc j) /\
  (forall j, pc <= j -> j < J -> is_load (ins p c j r) && icond (ins p c j r) r = false -> r j = 0) /\
  (forall j k d, j < J -> placed p c cc pc r k d j -> is_load (inst_of d) = true -> r j = rg cc k) /\
  (forall j k m xs, j < J -> hplaced p c cc pc r k m xs j ->
     vv (r j) = vv (rg cc k) /\ (fx cc j = None -> vok (rg cc k) = false -> r j = rg cc k) /\
     (fx cc j = None -> vok (r j) = true -> vok (rg cc k) = true /\ cfailv (ins p c j r) r (rg cc k) = false)) /\
  (forall j x b, pc <= j -> j < J -> B j = true -> ~ pslot p c cc pc r j -> fbinder p c r j x = Some b ->
     dec p c r j x = bvx p c r b x (dec p c r b x)) /\
  (* a CAS still to come: a success only if its values are equal *)
  (forall j, pc <= j -> j < J -> ~ pslot p c cc pc r j -> is_cas (ins p c j r) = true -> vok (r j) = true ->
     Nat.eqb (vv (r j)) (cexp (ins p c j r) r) = true) /\
  (* a CAS whose result is fixed (S3c), not happened as a whole: that result *)
  (forall j b, pc <= j -> j < J -> (forall k d, ~ placed p c cc pc r k d j) ->
     is_load (ins p c j r) && icond (ins p c j r) r = true -> is_cas (ins p c j r) = true -> fx cc j = Some b ->
     vok (r j) = b && Nat.eqb (vv (r j)) (cexp (ins p c j r) r)) /\
  (* DQ: a read of no cell still to come: its register holds enc [] = 0 *)
  (forall j, pc <= j -> j < J -> ~ pslot p c cc pc r j -> icells (ins p c j r) = [] ->
     is_load (ins p c j r) && icond (ins p c j r) r = true -> rval (ins p c j r) (r j) = 0).

(* the free values a register function gives: its registers read back cell by cell *)
Definition Fd (p : prog) (c : nat) (r : regs) : nat -> cell -> val :=
  fun j x => if Nat.eqb x (bitc (ins p c j r)) then Nat.b2n (vok (r j)) else dec p c r j x.

Lemma placed_rg : forall p c cc g pc r k d j, placed p c (cc_rg cc g) pc r k d j <-> placed p c cc pc r k d j.
Proof.
  intros. split; intros (P & t & O & F); (split; [exact P|]); exists t; (split; [exact O|]); unfold first_at in *;
    [rewrite plc_rg in F|rewrite plc_rg]; exact F.
Qed.
Lemma hplaced_rg : forall p c cc g pc r k m xs j, hplaced p c (cc_rg cc g) pc r k m xs j <-> hplaced p c cc pc r k m xs j.
Proof.
  intros. split; intros (P & C & t & O & F); (split; [exact P|]); (split; [exact C|]); exists t; (split; [exact O|]); unfold first_atR in *;
    [rewrite plc_rg in F|rewrite plc_rg]; exact F.
Qed.
Lemma pslot_rg : forall p c cc g pc r j, pslot p c (cc_rg cc g) pc r j <-> pslot p c cc pc r j.
Proof.
  intros. unfold pslot. split; intros [(k & d & P)|(k & m & xs & P)];
    [left; exists k, d; exact (proj1 (placed_rg _ _ _ _ _ _ _ _ _) P)|right; exists k, m, xs; exact (proj1 (hplaced_rg _ _ _ _ _ _ _ _ _ _) P)|
     left; exists k, d; exact (proj2 (placed_rg _ _ _ _ _ _ _ _ _) P)|right; exists k, m, xs; exact (proj2 (hplaced_rg _ _ _ _ _ _ _ _ _ _) P)].
Qed.

Lemma placed_fx : forall p c cc b' g pc r k d j, placed p c (cc_fx cc b' g) pc r k d j <-> placed p c cc pc r k d j.
Proof.
  intros. split; intros (P & t & O & F); (split; [exact P|]); exists t; (split; [exact O|]); unfold first_at in *;
    [rewrite plc_fx in F|rewrite plc_fx]; exact F.
Qed.
Lemma hplaced_fx : forall p c cc b' g pc r k m xs j, hplaced p c (cc_fx cc b' g) pc r k m xs j <-> hplaced p c cc pc r k m xs j.
Proof.
  intros. split; intros (P & C & t & O & F); (split; [exact P|]); (split; [exact C|]); exists t; (split; [exact O|]); unfold first_atR in *;
    [rewrite plc_fx in F|rewrite plc_fx]; exact F.
Qed.
Lemma pslot_fx : forall p c cc b' g pc r j, pslot p c (cc_fx cc b' g) pc r j <-> pslot p c cc pc r j.
Proof.
  intros. unfold pslot. split; intros [(k & d & P)|(k & m & xs & P)];
    [left; exists k, d; exact (proj1 (placed_fx _ _ _ _ _ _ _ _ _ _) P)|right; exists k, m, xs; exact (proj1 (hplaced_fx _ _ _ _ _ _ _ _ _ _ _) P)|
     left; exists k, d; exact (proj2 (placed_fx _ _ _ _ _ _ _ _ _ _) P)|right; exists k, m, xs; exact (proj2 (hplaced_fx _ _ _ _ _ _ _ _ _ _ _) P)].
Qed.

Lemma ccJ_le : forall p c cc pc B r J J', ccJ p c cc pc B r J -> pc <= J' -> J' <= J -> ccJ p c cc pc B r J'.
Proof.
  intros p c cc pc B r J J' (A0 & A1 & A2 & A3 & A3h & A4 & A5 & A6 & A7) L1 L2. split; [auto|]. split; [auto|]. split; [|split; [|split; [|split; [|split; [|split]]]]].
  - intros j L L' X. apply A2; auto. lia.
  - intros j k d L. apply A3. lia.
  - intros j k m xs L. apply A3h. lia.
  - intros j x b L L'. apply A4; auto. lia.
  - intros j L L'. apply A5; auto. lia.
  - intros j b L L'. apply A6; auto. lia.
  - intros j L L'. apply A7; auto. lia.
Qed.

Lemma ccJ_B : forall p c cc pc B B' r J, (forall j, B j = true -> B' j = true) ->
  ccJ p c cc pc B' r J -> ccJ p c cc pc B r J.
Proof.
  intros p c cc pc B B' r J H (A0 & A1 & A2 & A3 & A3h & A4 & A5 & A6 & A7). split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|].
  split; [|exact (conj A5 (conj A6 A7))]. intros j x b L L' Bj. apply A4; auto.
Qed.

Lemma dof_exec_tied : forall p c j r d, cellful p -> dof (ins p c j r) r = Some d ->
  executes (ins p c j r) r = true /\ tied (ins p c j r) (inst_of d).
Proof. intros p c j r d Wc D. split; [texec|tself]. Qed.

Lemma dof_load : forall i r d, dof i r = Some d -> is_load i && icond i r = is_load (inst_of d).
Proof.
  intros i r d D. destruct (dof_shape _ _ _ D) as (_ & _ & Q3 & _ & _ & Q6 & _). rewrite Q3, Q6.
  apply andb_true_r.
Qed.

(* the constraints depend only on the registers before J *)
Lemma ccJ_agree_r : forall p c cc pc B r r' J, wf p -> agree r r' J -> ccJ p c cc pc B r J -> ccJ p c cc pc B r' J.
Proof.
  intros p c cc pc B r r' J W A (A0 & A1 & A2 & A3 & A3h & A4 & A5 & A6 & A7).
  assert (PSX : forall j, j < J -> pslot p c cc pc r j -> pslot p c cc pc r' j).
  { intros j Lj [(k & d & Pk)|(k & m & xs & (P1 & P2 & t & O & F))]; [left|right].
    + exists k, d. apply (placed_agree p W c cc pc r r' k d j); [intros i Li; apply A; lia|exact Pk].
    + exists k, m, xs. split; auto. split; auto. exists t. split; auto. unfold first_atR in *.
      apply (plc_agree p W c cc pc _ r r'); auto. intros i Li. apply A. lia. }
  split; [auto|]. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  - intros j L. rewrite <- A by lia. auto.
  - intros j L1 L2 X. rewrite <- A by auto. apply A2; auto.
    destruct (ins_agree p W c j r r' (agree_le r r' J j A ltac:(lia))) as [E1 E2].
    rewrite (ieval_cond _ _ _ E2), E1. exact X.
  - intros j k d L P Ld. rewrite <- A by auto. apply (A3 j k d); auto.
    apply (placed_agree p W c cc pc r' r k d j); auto. intros i Li. symmetry. apply A. lia.
  - intros j k m xs L (P1 & P2 & t & O & F). rewrite <- A by auto.
    rewrite <- (cfailv_agree p W c j r r' _ (agree_le r r' J j A ltac:(lia))). apply (A3h j k m xs L).
    split; auto. split; auto. exists t. split; auto. unfold first_atR in *. apply (plc_agree p W c cc pc _ r' r); auto.
    intros i Li. symmetry. apply A. lia.
  - intros j x b L1 L2 Bj Np Fb. assert (Aj : agree r r' (S j)) by (apply (agree_le r r' J); auto; lia).
    rewrite <- (fbinder_agree p W c r r' j x (agree_le _ _ _ j Aj ltac:(lia))) in Fb.
    pose proof (fbinder_lt p c r j x b Fb) as Lb.
    rewrite <- (dec_agree p c r r' j x W Aj), <- (dec_agree p c r r' b x W (agree_le _ _ _ (S b) Aj ltac:(lia))).
    rewrite <- (bvx_agree p W c r r' b j x _ Lb (agree_le _ _ _ j Aj ltac:(lia))).
    apply (A4 j x b); try (intros X; apply Np; exact (PSX j L2 X)); auto.
  - intros j L1 L2 Np Cs V. rewrite <- A in V |- * by auto.
    destruct (ins_agree p W c j r r' (agree_le r r' J j A ltac:(lia))) as [E1 E2].
    rewrite <- E1 in Cs |- *. rewrite <- (cexp_ieval _ _ _ E2). apply (A5 j L1 L2); try (intros X; apply Np; exact (PSX j L2 X)); auto.
  - intros j b L1 L2 Np X Cs Fx. rewrite <- A by auto.
    destruct (ins_agree p W c j r r' (agree_le r r' J j A ltac:(lia))) as [E1 E2].
    rewrite <- E1 in X, Cs |- *. rewrite <- (cexp_ieval _ _ _ E2). rewrite <- (ieval_cond _ _ _ E2) in X.
    apply (A6 j b L1 L2); auto. intros k d P. apply (Np k d).
    apply (placed_agree p W c cc pc r r' k d j); [intros i Li; apply A; lia|exact P].
  - intros j L1 L2 Np Ic X. rewrite <- A by auto.
    destruct (ins_agree p W c j r r' (agree_le r r' J j A ltac:(lia))) as [E1 E2]. rewrite <- E1.
    apply (A7 j L1 L2); [intros Xp; apply Np; exact (PSX j L2 Xp)|rewrite E1; exact Ic|rewrite (ieval_cond _ _ _ E2), E1; exact X].
Qed.

Lemma exec_agree' : forall i r r', ieval i r = ieval i r' -> executes i r = executes i r'.
Proof. intros i r r' H. unfold executes, icond. rewrite H. reflexivity. Qed.

(* the binder: scanning back, the first instruction that comes and is tied *)
Lemma fbind_spec : forall p c r i x b b', fbind p c r i x b = Some b' ->
  b' < b /\ executes (ins p c b' r) r = true /\ tiedb (ins p c b' r) i = true /\
  forall q, b' < q -> q < b -> executes (ins p c q r) r && tiedb (ins p c q r) i = false.
Proof.
  intros p c r i x b. induction b as [|b IH]; intros b' H; simpl in H; [discriminate|].
  destruct (executes (ins p c b r) r && tiedb (ins p c b r) i) eqn:E.
  - assert (b' = b) by (destruct (existsb _ _); [injection H as <-; auto|discriminate]).
    subst b'. apply andb_prop in E as [E1 E2]. split; [lia|]. split; [auto|]. split; [auto|]. intros; lia.
  - destruct (IH b' H) as (A & B & C & D). split; [lia|]. split; [auto|]. split; [auto|].
    intros q L1 L2. destruct (Nat.eq_dec q b) as [->|N]; [auto|]. apply D; lia.
Qed.

Lemma fbinder_spec : forall p c r j x b, fbinder p c r j x = Some b ->
  bread (ins p c j r) = true /\ icond (ins p c j r) r = true /\ In x (icells (ins p c j r)) /\
  fbind p c r (ins p c j r) x j = Some b.
Proof.
  intros p c r j x b H. pose proof (fbinder_shape _ _ _ _ _ _ H) as (_ & _ & _ & Br & Cr & Ix).
  unfold fbinder in H. rewrite Br, Cr in H. simpl in H.
  assert (X : existsb (Nat.eqb x) (icells (ins p c j r)) = true) by (apply existsb_exists; exists x; split; auto; apply Nat.eqb_refl).
  rewrite X in H. auto.
Qed.

Lemma fbinder_exec : forall p c r j x b, fbinder p c r j x = Some b -> executes (ins p c b r) r = true.
Proof. intros p c r j x b H. apply (fbinder_shape _ _ _ _ _ _ H). Qed.

(* a pending store recorded 0 *)
Lemma rg_store_of : forall p s c d, Inv1 p s -> Inv2 p s -> oc (cs s c) (pcs s c) <> None ->
  ai (cs s c) (pcs s c) = inst_of d -> eof (ins p c (pcs s c) (rg (cs s c))) (rg (cs s c)) = Some d ->
  is_load (inst_of d) = false -> rg (cs s c) (pcs s c) = 0.
Proof.
  intros p s c d I J O A D L. destruct (oc (cs s c) (pcs s c)) as [t|] eqn:Ot; [|congruence].
  destruct (i_oc p s I c _ t Ot) as (e & E1 & E2 & E3).
  assert (Ei : einstr p s e = inst_of d) by (unfold einstr; rewrite E2, E3; exact A).
  destruct (j_val p s J t e _ E1 Ei) as [_ V]. rewrite E2, E3 in V. apply V.
  unfold xload. rewrite L. reflexivity.
Qed.

(* whether some pending access has its place at j *)
Lemma pslot_or : forall p s c r j, wf p -> cellful p -> run p s ->
  pslot p c (cs s c) (pcs s c) r j \/ ~ pslot p c (cs s c) (pcs s c) r j.
Proof.
  intros p s c r j W Wc R. pose proof (Inv1_run p s R) as I.
  destruct (pend_at p c (cs s c) (pcs s c) (tp s c) r j) as [k|] eqn:Pa.
  - left. left. apply (pend_at_char_s p s c I) in Pa. destruct Pa as (d & Pa). exists k, d. exact Pa.
  - destruct (hpend_at p c (cs s c) (pcs s c) (tp s c) r j) as [k|] eqn:Ph.
    + left. right. apply (hpend_at_char_s p s c I) in Ph. destruct Ph as (m & xs & Ph). exists k, m, xs. exact Ph.
    + right. apply (pend_at_none_s p s c I) in Pa. apply (hpend_at_none_s p s c I) in Ph. intros [X|X]; auto.
Qed.

Section Run.
Variable p : prog.
Variable s : st.
Hypothesis W : wf p.
Hypothesis Wc : cellful p.
Hypothesis R : run p s.
Let I : Inv1 p s := Inv1_run p s R.
Let J2 : Inv2 p s := proj2 (Inv2_run p s R).

(* the value of a passed slot in cell x, read back from its register *)
Lemma dec_passed : forall c r j x, agree r (rg (cs s c)) (S j) -> j < pcs s c ->
  executes (ins p c j r) r = true -> In x (icells (ins p c j r)) -> dec p c r j x = rv (cs s c) j x.
Proof.
  intros c r j x A L Ex Ix.
  rewrite (exec_agree p W c j r (rg (cs s c)) (agree_le _ _ _ j A ltac:(lia))) in Ex.
  destruct (oc (cs s c) j) as [t|] eqn:O.
  2:{ (* a CAS that failed after its read: its read's value *)
      destruct (passed_fail p s c j I L Ex O) as (t1 & Oh & _ & Ai).
      assert (Ei : ins p c j r = ai (cs s c) j)
        by (rewrite Ai; apply (proj1 (ins_agree p W c j r (rg (cs s c)) (agree_le _ _ _ j A ltac:(lia))))).
      apply dec_of; [intros Z; rewrite Z in Ix; destruct Ix| |exact Ix].
      assert (Cs : is_cas (ai (cs s c) j) = true)
        by (destruct (i_halfp p s I c j t1 O Oh L) as (_ & (xs0 & Xc) & _); destruct (ai (cs s c) j); simpl in Xc; try discriminate; reflexivity).
      rewrite (A j ltac:(lia)), Ei, (rval_cas _ _ Cs), (rg_rv_h p s R c j t1 O Oh). reflexivity. }
  destruct (proj1 (i_cmA p s I c j) L) as (tau & T). pose proof (proj2 (i_set p s I c j tau T)) as Ai.
  assert (Ei : ins p c j r = ai (cs s c) j)
    by (rewrite Ai; apply (proj1 (ins_agree p W c j r (rg (cs s c)) (agree_le _ _ _ j A ltac:(lia))))).
  apply dec_of; [intros Z; rewrite Z in Ix; destruct Ix| |exact Ix].
  rewrite (A j ltac:(lia)), Ei, (rg_rv p s c j t I J2 O). reflexivity.
Qed.

(* the value of a read at the place of a pending read, in cell x *)
Lemma dec_pending : forall c r j k d x, placed p c (cs s c) (pcs s c) r k d j -> r j = rg (cs s c) k ->
  In x (icells (ins p c j r)) -> dec p c r j x = rv (cs s c) k x.
Proof.
  intros c r j k d x ((_ & Ok & Ak) & t & O & F) E Ix.
  apply dec_of; [intros Z; rewrite Z in Ix; destruct Ix| |exact Ix].
  rewrite E. rewrite (rval_iscas (ins p c j r) (ai (cs s c) k)) by (rewrite Ak; symmetry; apply (proj1 (eof_cexp _ _ _ r (first_at_eof _ _ _ _ _ _ _ _ F)))).
  rewrite (rg_rv p s c k t I J2 O), Ak, <- (eof_icells _ _ _ (first_at_eof _ _ _ _ _ _ _ _ F)). reflexivity.
Qed.

(* the value of a read at the place of a CAS's read alone, in cell x *)
Lemma dec_hpending : forall c r j k m xs x, hplaced p c (cs s c) (pcs s c) r k m xs j -> vv (r j) = vv (rg (cs s c) k) ->
  In x (icells (ins p c j r)) -> dec p c r j x = rv (cs s c) k x.
Proof.
  intros c r j k m xs x Pl E Ix. pose proof Pl as (Pk & C & t & O & F).
  destruct (hplaced_icells p s R c r k m xs j Pl) as [Ic _].
  apply dec_of; [intros Z; rewrite Z in Ix; destruct Ix| |exact Ix].
  assert (Cs : is_cas (ins p c j r) = true) by (apply (eofR_cas _ r (m, xs)); apply (first_atR_eofR _ _ _ _ _ _ _ _ _ F)).
  rewrite (rval_cas _ _ Cs), E, (rg_rv_h p s R c k t C O), Ic. reflexivity.
Qed.

Lemma ccJ_cv : forall c B r J, ccJ p c (cs s c) (pcs s c) B r J ->
  forall n b x, b < J -> In x (icells (ins p c b r)) -> executes (ins p c b r) r = true -> (b < pcs s c \/ rdat p c r b = true) ->
  cellv p c (cs s c) (pcs s c) (tp s c) B (Fd p c r) r n b x = dec p c r b x.
Proof.
  intros c B r J (A0 & C1 & C2 & C3 & C3h & C4 & C5 & C6 & C7). set (cc := cs s c) in *. set (pc := pcs s c) in *. set (N := tp s c).
  assert (Ag : forall q, q <= pc -> agree r (rg cc) q) by (intros q Lq i0 Li; apply C1; lia).
  intros n. induction n as [|n IH]; intros b x Lb Ix Ex Rb.
  all: destruct (Nat.ltb_spec b pc) as [L|L];
    [rewrite cellv_lt by auto; symmetry; apply dec_passed; auto; apply Ag; lia|].
  all: destruct Rb as [Rb|Rb]; [lia|]. all: unfold rdat in Rb.
  all: destruct (pend_at p c cc pc N r b) as [k|] eqn:Pa.
  all: try (rewrite (cellv_pd _ _ _ _ _ _ _ _ _ _ _ k) by auto;
            apply (pend_at_char_s p s c I) in Pa; destruct Pa as (d' & Pl); symmetry;
            apply (dec_pending c r b k d' x Pl); auto;
            apply (C3 b k d' Lb Pl); pose proof Pl as (_ & t & _ & Fj);
            rewrite <- (eof_load _ _ _ (first_at_eof _ _ _ _ _ _ _ _ Fj)); exact Rb).
  all: destruct (hpend_at p c cc pc N r b) as [k|] eqn:Ph.
  all: try (rewrite (cellv_hpd _ _ _ _ _ _ _ _ _ _ _ k) by auto;
            apply (hpend_at_char_s p s c I) in Ph; destruct Ph as (m & xs & Pl); symmetry;
            apply (dec_hpending c r b k m xs x Pl); auto; apply (proj1 (C3h b k m xs Lb Pl))).
  - rewrite cellv_free by auto. unfold Fd. rewrite (proj2 (Nat.eqb_neq _ _) (bitc_notin _ _ Ix)). reflexivity.
  - rewrite cellv_go by auto. destruct (B b) eqn:Bb; [|unfold Fd; rewrite (proj2 (Nat.eqb_neq _ _) (bitc_notin _ _ Ix)); reflexivity].
    destruct (fbinder p c r b x) as [b0|] eqn:Fb; [|unfold Fd; rewrite (proj2 (Nat.eqb_neq _ _) (bitc_notin _ _ Ix)); reflexivity].
    assert (Np : ~ pslot p c cc pc r b).
    { intros [(k0 & d0 & Pl)|(k0 & m & xs & Pl)].
      - assert (pend_at p c cc pc N r b = Some k0) by (apply (pend_at_char_s p s c I); eauto). congruence.
      - assert (hpend_at p c cc pc N r b = Some k0) by (apply (hpend_at_char_s p s c I); eauto). congruence. }
    rewrite (C4 b x b0 L Lb Bb Np Fb). pose proof (fbinder_lt _ _ _ _ _ _ Fb) as L0.
    destruct (binder_read p c r b x b0 Fb) as [(R0 & I0)|(m & ys & cb & v & E0)].
    + f_equal. apply IH; [lia|exact I0|exact (proj1 (fbinder_shape _ _ _ _ _ _ Fb))|]. destruct (Nat.ltb_spec b0 pc); [left|right]; auto.
    + apply (bvx_store p c r b0 x _ _ m ys cb v E0).
Qed.

(* such registers are the model's registers up to J *)
Lemma ccJ_slotv : forall c B r J, ccJ p c (cs s c) (pcs s c) B r J ->
  forall j, j < J -> slotv p c (cs s c) (pcs s c) (tp s c) B (Fd p c r) r j = r j.
Proof using W Wc R. (* DQ: Wc kept in the statement (not needed: C7) *)
  intros c B r J H j Lj. pose proof H as (A0 & C1 & C2 & C3 & C3h & C4 & C5 & C6 & C7).
  set (cc := cs s c) in *. set (pc := pcs s c) in *. set (N := tp s c).
  unfold slotv.
  destruct (Nat.ltb_spec j pc) as [L|L]; [symmetry; apply C1; auto|].
  destruct (is_load (ins p c j r) && icond (ins p c j r) r) eqn:X; [|symmetry; apply C2; auto].
  destruct (pend_at p c cc pc N r j) as [k|] eqn:Pa.
  - apply (pend_at_char_s p s c I) in Pa. destruct Pa as (d' & Pl).
    symmetry. apply (C3 j k d'); auto. pose proof Pl as (_ & t & _ & Fj).
    rewrite <- (eof_load _ _ _ (first_at_eof _ _ _ _ _ _ _ _ Fj)). auto.
  - assert (NPl : forall k d, ~ placed p c cc pc r k d j).
    { intros k0 d0 Pl0. assert (pend_at p c cc pc N r j = Some k0) by (apply (pend_at_char_s p s c I); eauto). congruence. }
    assert (FXS : forall a, (forall bx, fx cc j = Some bx -> is_cas (ins p c j r) = true -> vv a = vv (r j)) ->
                  (fx cc j = None \/ is_cas (ins p c j r) = false -> a = r j) -> cfx cc j (ins p c j r) r a = r j).
    { intros a0 H1 H2. rewrite cfx_unfold. destruct (fx cc j) as [bx|] eqn:Fxj; [|apply H2; left; reflexivity].
      destruct (is_cas (ins p c j r)) eqn:Ci; [|apply H2; right; reflexivity].
      rewrite (H1 bx eq_refl eq_refl). apply vd_eq; [rewrite vok_vd|rewrite vv_vd; reflexivity].
      symmetry. apply (C6 j bx L Lj NPl X Ci Fxj). }
    (* DQ: no slot of a read is pending here once no item is placed there *)
    assert (NpH : hpend_at p c cc pc N r j = None -> ~ pslot p c cc pc r j).
    { intros Ph0 [(k0 & d0 & Pl)|(k0 & m & xs & Pl)]; [exact (NPl k0 d0 Pl)|].
      assert (hpend_at p c cc pc N r j = Some k0) by (apply (hpend_at_char_s p s c I); eauto). congruence. }
    (* DQ: a read of no cell holds enc [] = 0 (C7) *)
    assert (EV : ~ pslot p c cc pc r j -> enc (map (cellv p c cc pc N B (Fd p c r) r j j) (icells (ins p c j r))) = rval (ins p c j r) (r j)).
    { intros Np0. destruct (icells (ins p c j r)) as [|x0 l0] eqn:Ic; [symmetry; exact (C7 j L Lj Np0 Ic X)|]. rewrite <- Ic.
      assert (Ne : icells (ins p c j r) <> []) by (rewrite Ic; discriminate).
      transitivity (enc (map (dec p c r j) (icells (ins p c j r)))); [|apply enc_dec; auto].
      f_equal. apply map_ext_in. intros x Ix.
      assert (Ex : executes (ins p c j r) r = true).
      { unfold executes. apply andb_prop in X. destruct X as [X1 X2]. destruct (ins p c j r); simpl in X1; try discriminate; exact X2. }
      pose proof (ccJ_cv c B r J H j j x Lj Ix Ex (or_intror X)) as Q. fold cc pc N in Q. exact Q. }
    apply FXS.
    { intros bx Fxj Ci. destruct (hpend_at p c cc pc N r j) as [k|] eqn:Ph.
      - apply (hpend_at_char_s p s c I) in Ph. destruct Ph as (m & xs & Pl).
        destruct (C3h j k m xs Lj Pl) as (Vv & _). rewrite Vv. destruct (vok (rg cc k)); [apply vv_vd|reflexivity].
      - cbv zeta. rewrite (EV (NpH eq_refl)), Ci, vv_vd. apply rval_cas. exact Ci. }
    intros Hn. destruct (hpend_at p c cc pc N r j) as [k|] eqn:Ph.
    { apply (hpend_at_char_s p s c I) in Ph. destruct Ph as (m & xs & Pl). symmetry.
      assert (Fn : fx cc j = None).
      { destruct Hn as [Hn|Hn]; [exact Hn|]. exfalso. pose proof Pl as (_ & _ & t0 & _ & F0).
        rewrite (eofR_cas _ r _ (first_atR_eofR _ _ _ _ _ _ _ _ _ F0)) in Hn. discriminate. }
      assert (Q : vv (r j) = vv (rg cc k) /\ (fx cc j = None -> vok (rg cc k) = false -> r j = rg cc k) /\
                  (fx cc j = None -> vok (r j) = true -> vok (rg cc k) = true /\ cfailv (ins p c j r) r (rg cc k) = false))
        by (apply (C3h j k m xs); auto).
      destruct Q as (Vv & Cm & Ok). specialize (Cm Fn). specialize (Ok Fn).
      destruct (vok (rg cc k)) eqn:Vk; [|apply Cm; reflexivity].
      unfold fbit, Fd. rewrite Nat.eqb_refl, odd_b2n, <- Vv.
      destruct (vok (r j)) eqn:Vr.
      - rewrite (proj2 (Ok eq_refl)). simpl. rewrite <- Vr. symmetry. apply vd_split.
      - rewrite andb_false_r, <- Vr. symmetry. apply vd_split. }
    assert (Np : ~ pslot p c cc pc r j).
    { intros [(k0 & d0 & Pl)|(k0 & m & xs & Pl)].
      - assert (pend_at p c cc pc N r j = Some k0) by (apply (pend_at_char_s p s c I); eauto). congruence.
      - assert (hpend_at p c cc pc N r j = Some k0) by (apply (hpend_at_char_s p s c I); eauto). congruence. }
    cbv zeta. rewrite (EV Np). destruct (is_cas (ins p c j r)) eqn:Cs.
    + unfold fbit, Fd. rewrite Nat.eqb_refl, odd_b2n, (rval_cas _ _ Cs).
      destruct (vok (r j)) eqn:Vr.
      * rewrite (C5 j L Lj Np Cs Vr). simpl. rewrite <- Vr. apply vd_split.
      * rewrite andb_false_r, <- Vr. apply vd_split.
    + destruct (ins p c j r); simpl in Cs; try discriminate; reflexivity.
Qed.

(* the binder value a constraint register function gives a leader *)
Lemma dec_lead : forall c B r j x b k', ccJ p c (cs s c) (pcs s c) B r j -> b < j ->
  executes (ins p c b r) r = true -> In x (icells (ins p c b r)) ->
  lead p c (cs s c) (pcs s c) (tp s c) r b = Some k' ->
  bvx p c r b x (dec p c r b x) = bvx p c r b x (rv (cs s c) k' x).
Proof.
  intros c B r j x b k' (A0 & A1 & A2 & A3 & A3h & _) Lbj Ex Ix Lk. unfold lead in Lk.
  destruct (Nat.ltb_spec b (pcs s c)) as [Lb|Lb].
  - injection Lk as <-.
    assert (Ab : agree r (rg (cs s c)) (S b)) by (intros i0 Li0; apply A1; lia).
    rewrite (dec_passed c r b x Ab Lb Ex Ix). reflexivity.
  - destruct (pend_at p c (cs s c) (pcs s c) (tp s c) r b) as [k1|] eqn:Pa.
    + injection Lk as ->. apply (pend_at_char_s p s c I) in Pa. destruct Pa as (d1 & Pl).
      pose proof Pl as (_ & t1 & _ & F1). pose proof (first_at_eof _ _ _ _ _ _ _ _ F1) as E.
      destruct (is_load (inst_of d1)) eqn:Ld.
      * rewrite (dec_pending c r b k' d1 x Pl (A3 b k' d1 Lbj Pl Ld) Ix). reflexivity.
      * rewrite (bvx_eof p c r b x _ d1 E), (bvx_eof p c r b x _ d1 E).
        rewrite (eof_icells _ _ _ E) in Ix. destruct d1; simpl in Ld, Ix; try discriminate; try reflexivity. destruct Ix.
    + apply (hpend_at_char_s p s c I) in Lk. destruct Lk as (m & xs & Pl).
      rewrite (dec_hpending c r b k' m xs x Pl (proj1 (A3h b k' m xs Lbj Pl)) Ix). reflexivity.
Qed.

Lemma ccJ_agree : forall c B r J, ccJ p c (cs s c) (pcs s c) B r J ->
  agree r (creg p c (cs s c) (pcs s c) (tp s c) B (Fd p c r)) J.
Proof.
  intros c B r J H. assert (PO : pend_ok (cs s c) (pcs s c)) by (apply (pend_ok_of p s c I)).
  intros j. induction j as [j IH] using lt_wf_ind. intros Lj.
  rewrite (creg_fix p W c _ _ _ B (Fd p c r) j PO).
  rewrite (slotv_agree p W c _ _ _ B (Fd p c r) _ r j PO).
  - symmetry. apply (ccJ_slotv c B r J H j Lj).
  - intros i Li. symmetry. apply IH; lia.
Qed.

End Run.

(* ---------- one step keeps the places of the accesses still pending ---------- *)
Lemma step_place_g : forall p s t c k tq r j g, wf p -> cellful p -> run p s -> step p s t ->
  ((exists d, g = TF d /\ pending (cs t c) (pcs t c) k d /\ oc (cs s c) k = Some tq) \/
   (exists m xs, g = TH m xs /\ hpending (cs t c) (pcs t c) k m xs /\ oh (cs s c) k = Some tq)) ->
  agree r (rg (cs t c)) (pcs t c) -> pcs t c <= j ->
  (plc p c (cs s c) (pcs s c) r (S tq) tq g j <-> plc p c (cs t c) (pcs t c) r (S tq) tq g j).
Proof.
  intros p s t c k tq r j g W Wc R St G Ag Lj. pose proof (Inv1_run p s R) as I. pose proof (Ext_step p s t R St) as X.
  assert (Ag' : agree r (rg (cs s c)) (pcs s c)).
  { intros q Lq. rewrite Ag by (pose proof (x_pcs _ _ X c); lia). apply (x_rg _ _ X). left. auto. }
  assert (Ltq : tq < tm s).
  { destruct G as [(d & _ & _ & O)|(m & xs & _ & _ & O)]; [apply (oc_lt_tm p s c k tq I O)|apply (oh_lt_tm p s c k tq I O)]. }
  destruct (stepQ_cases p s t St) as [St0|[(cR & kR & BR & ER & _)|(cS & jS & kS & BS & ES & _)]];
    [|(* DQ q_rfix: the places read neither bd, fx nor the record's register *)
      subst t; change (pcs (sbd (scfail s cR kR) cR BR)) with (pcs s); destruct (Nat.eq_dec c cR) as [<-|N];
      [unfold sbd at 1; cbn [cs]; rewrite upd_eq', plc_fx, (cf_cs s c kR), plc_rg; reflexivity
      |assert (Cs : cs (sbd (scfail s cR kR) cR BR) c = cs s c) by (unfold sbd, scfail; simpl; rewrite !upd_neq by auto; reflexivity);
       rewrite Cs; reflexivity]
     |(* DQ q_sfix *)
      subst t; change (pcs (scfix0 s cS jS true BS)) with (pcs s); destruct (Nat.eq_dec c cS) as [<-|N];
      [rewrite cx_cs, plc_fx; reflexivity
      |assert (Cs : cs (scfix0 s cS jS true BS) c = cs s c) by (unfold scfix0; simpl; rewrite upd_neq by auto; reflexivity);
       rewrite Cs; reflexivity]].
  destruct (step_cases p s t St0) as [(c0 & i & m' & a & K & u & w & Hi & Ho & Hd & Hb & Hbh & Hbd & _ & _ & He & _ & E)|[(c0 & k0 & d0 & B & m' & a & K & u & w & Lk & Ho & Hso & Hk & HwE & HvE & He & _ & E)|[(c0 & d0 & Ho & Ha & Hdf & Hd & Hf & Hfh & E)|[(c0 & k0 & xs0 & B & m' & a & K & u & w & bv & Lk & Ho & Hoh & Hso & Hok & He & _ & E)|[(c0 & Kx & Ko & Kh & Kv & Kf & Kd & _ & E)|(cX & jX & bX & BX & oX & HjX & HfX & HcX & E)]]]]]; subst t.
  - destruct (Nat.eq_dec c c0) as [<-|N].
    2:{ assert (Cs : cs (sord s c0 i m' a K u w) c = cs s c) by (unfold sord; apply cs_other; auto).
        assert (Pc : pcs (sord s c0 i m' a K u w) c = pcs s c) by (unfold sord, evs; simpl; apply upd_neq'; auto).
        rewrite Cs, Pc. reflexivity. }
    assert (Pc : pcs (sord s c i m' a K u w) c = S (pcs s c)) by (unfold sord, evs; simpl; apply upd_eq').
    rewrite Pc in *. destruct G as [(d & -> & Pt & O)|(m & xs & -> & Pt & O)].
    + assert (Ot : oc (cs (sord s c i m' a K u w) c) k = Some tq) by (apply (x_oc _ _ X); auto).
      apply (ord_shift p s c i m' a K u w W Wc I Hi Ho Hb Hbh Hbd r Ag' tq k d j Pt Ot Lj).
    + assert (Ot : oh (cs (sord s c i m' a K u w) c) k = Some tq) by (unfold sord; rewrite oh_s'; exact O).
      apply (ord_shiftR p s c i m' a K u w W Wc I Hi Ho Hb Hbh Hbd r Ag' tq k m xs j Pt Ot Lj).
  - destruct (Nat.eq_dec c c0) as [<-|N].
    2:{ assert (Cs : cs (searly s c0 k0 d0 B m' a K u w) c = cs s c) by (unfold searly, set_es, searly0; apply cs_other; auto).
        assert (Pc : pcs (searly s c0 k0 d0 B m' a K u w) c = pcs s c) by reflexivity.
        rewrite Cs, Pc. reflexivity. }
    assert (Pc : pcs (searly s c k0 d0 B m' a K u w) c = pcs s c) by reflexivity. rewrite Pc.
    destruct Hk as [(Z & Ok)|(t1 & xs & ev & nv & Z & -> & U & Ac & Ok)].
    + rewrite cce_eq. apply (early_same_g p s c k0 d0 B m' a u w Lk Ho Z r tq g j). lia.
    + subst u. rewrite ccw_eq. apply (cwe_same_g p s c k0 t1 xs ev nv B m' a K w I (proj2 (Inv2_run p s R)) Lk Ho Z Ac He HvE HwE r tq g j). lia.
  - destruct (Nat.eq_dec c c0) as [<-|N].
    2:{ assert (Cs : cs (smatch p s c0) c = cs s c) by (unfold smatch; simpl; apply upd_neq'; auto).
        assert (Pc : pcs (smatch p s c0) c = pcs s c) by (unfold smatch; simpl; apply upd_neq'; auto).
        rewrite Cs, Pc. reflexivity. }
    assert (Pc : pcs (smatch p s c) c = S (pcs s c)) by (unfold smatch; simpl; apply upd_eq').
    rewrite Pc, ccm_eq in *. destruct G as [(d & -> & Pt & O)|(m & xs & -> & Pt & O)].
    + assert (Ot : oc (ccm p s c) k = Some tq) by (rewrite <- ccm_eq; apply (x_oc _ _ X); auto).
      apply (match_shift p s c d0 W Wc I Ho Ha Hdf Hf Hfh r Ag' tq k d j Pt Ot Lj).
    + assert (Ot : oh (ccm p s c) k = Some tq) by exact O.
      apply (match_shiftR p s c d0 W Wc I Ho Ha Hdf Hf Hfh r Ag' tq k m xs j Pt Ot Lj).
  - destruct (Nat.eq_dec c c0) as [<-|N].
    2:{ assert (Cs : cs (sread s c0 k0 Plain xs0 B m' a K u w bv) c = cs s c) by (unfold sread; simpl; apply upd_neq'; auto).
        assert (Pc : pcs (sread s c0 k0 Plain xs0 B m' a K u w bv) c = pcs s c) by reflexivity.
        rewrite Cs, Pc. reflexivity. }
    assert (Pc : pcs (sread s c k0 Plain xs0 B m' a K u w bv) c = pcs s c) by reflexivity. rewrite Pc, ccr_eq.
    apply (read_same_g p s c k0 xs0 B m' a u w bv Lk Ho Hoh r tq g j). lia.
  - destruct (Nat.eq_dec c c0) as [<-|N].
    2:{ assert (Cs : cs (sskip p s c0) c = cs s c) by (unfold sskip; simpl; apply upd_neq'; auto).
        assert (Pc : pcs (sskip p s c0) c = pcs s c) by (unfold sskip; simpl; apply upd_neq'; auto).
        rewrite Cs, Pc. reflexivity. }
    assert (Pc : pcs (sskip p s c) c = S (pcs s c)) by (unfold sskip; simpl; apply upd_eq').
    rewrite Pc in *.
    destruct (oh (cs s c) (pcs s c)) as [t1|] eqn:Oh.
    + (* a CAS that failed after its read *)
      destruct (i_half p s I c (pcs s c) t1 Ko Oh (le_n _)) as (_ & (xs1 & Ax) & _).
      assert (Er : eofR (ins p c (pcs s c) (rg (cs s c))) (rg (cs s c)) = Some (Plain, xs1))
        by (rewrite (Kh ltac:(congruence)), Ax; reflexivity).
      assert (Cf : cfail (ins p c (pcs s c) (rg (cs s c))) (rg (cs s c)) (pcs s c) = true).
      { destruct (xex_false _ _ _ _ Kx) as [X0|(_ & X0)]; [|exact X0]. exfalso.
        destruct (eofR_exec_tied p c (pcs s c) (rg (cs s c)) Plain xs1 Wc Er) as [E0 _]. congruence. }
      assert (AgS : agree r (rg (cs s c)) (S (pcs s c))) by (intros q Lq; rewrite Ag by lia; rewrite (rg_skip p s c); reflexivity).
      destruct G as [(d & -> & Pt & O)|(m & xs & -> & Pt & O)].
      * assert (Ot : oc (cs (sskip p s c) c) k = Some tq) by (rewrite (oc_skip p s c); exact O).
        apply (skf_shift p s c t1 xs1 W Wc Ko Oh Ax Er Cf (Kv ltac:(congruence)) Kf r AgS tq k d j Pt Ot Lj).
      * assert (Ot : oh (cs (sskip p s c) c) k = Some tq) by (rewrite (oh_skip p s c); exact O).
        apply (skf_shiftR p s c t1 xs1 W Wc Ko Oh Ax Er Cf (Kv ltac:(congruence)) Kf r AgS tq k m xs j Pt Ot Lj).
    + assert (Kx' : executes (ins p c (pcs s c) (rg (cs s c))) (rg (cs s c)) = false).
      { destruct (xex_false _ _ _ _ Kx) as [X0|(Z & _)]; [exact X0|congruence]. }
      destruct G as [(d & -> & Pt & O)|(m & xs & -> & Pt & O)].
      * assert (Ot : oc (cs (sskip p s c) c) k = Some tq) by (rewrite (oc_skip p s c); exact O).
        apply (sk_shift p s c W Kx' Ko Oh r Ag' tq k d j Pt Ot Lj).
      * assert (Ot : oh (cs (sskip p s c) c) k = Some tq) by (rewrite (oh_skip p s c); exact O).
        apply (sk_shiftR p s c W Kx' Ko Oh r Ag' tq k m xs j Pt Ot Lj).
  - (* S3c: a result fixed: the places read neither bd, fx nor the record's register *)
    try subst t. change (pcs (scfix0 (sflp s cX oX bX) cX jX bX BX)) with (pcs (sflp s cX oX bX)). rewrite pcs_flp.
    destruct (Nat.eq_dec c cX) as [<-|N].
    + rewrite cx_cs, plc_fx. destruct oX as [kX|]; [destruct bX|]; cbn [sflp]; try reflexivity.
      rewrite (cf_cs s c kX), plc_rg. reflexivity.
    + assert (Cs : cs (scfix0 (sflp s cX oX bX) cX jX bX BX) c = cs s c).
      { unfold scfix0; simpl; rewrite upd_neq by auto.
        destruct oX as [kX|]; [destruct bX|]; cbn [sflp]; try reflexivity. unfold scfail; simpl; apply upd_neq; auto. }
      rewrite Cs. reflexivity.
Qed.

Lemma step_place : forall p s t c k d tq r j, wf p -> cellful p -> run p s -> step p s t ->
  pending (cs t c) (pcs t c) k d -> oc (cs s c) k = Some tq ->
  agree r (rg (cs t c)) (pcs t c) -> pcs t c <= j ->
  (first_at p c (cs s c) (pcs s c) r tq d j <-> first_at p c (cs t c) (pcs t c) r tq d j).
Proof. intros. apply (step_place_g p s t c k); auto. left. eauto. Qed.

Lemma step_placeR : forall p s t c k m xs tq r j, wf p -> cellful p -> run p s -> step p s t ->
  hpending (cs t c) (pcs t c) k m xs -> oc (cs t c) k = None -> oh (cs s c) k = Some tq ->
  agree r (rg (cs t c)) (pcs t c) -> pcs t c <= j ->
  (first_atR p c (cs s c) (pcs s c) r tq m xs j <-> first_atR p c (cs t c) (pcs t c) r tq m xs j).
Proof. intros. apply (step_place_g p s t c k); auto. right. eauto. Qed.

(* ---------- R1 only adds constraints as a run goes on ---------- *)
Section Mono.
Variable p : prog.
Variables s t : st.
Hypothesis W : wf p.
Hypothesis R : run p s.
Hypothesis St : step p s t.
Hypothesis Wc : cellful p.
Let I : Inv1 p s := Inv1_run p s R.
Let J2 : Inv2 p s := proj2 (Inv2_run p s R).

(* DQ: q_sfix at context c; the M2 s_cfix script (first part) with the record
   condition from sfix_ok (sfix_hc) *)
Lemma mono_sfix : forall c r J jX bX BX kX, runQ p t -> t = scfix0 s c jX bX BX -> pcs s c <= jX -> fx (cs s c) jX = None ->
  sfix_ok p c (cs s c) (pcs s c) (tp s c) jX kX BX ->
  ccJ p c (cs t c) (pcs t c) (bd (cs t c)) r J -> ccJ p c (cs s c) (pcs s c) (bd (cs t c)) r J.
Proof.
  intros c r J jX bX BX kX Rt E HjX HfX HsO H.
  pose proof (Inv1_run p s R) as I1.
  assert (Hc1 : forall f k, hpend_at p c (cs s c) (pcs s c) (tp s c)
      (creg p c (cs s c) (pcs s c) (tp s c) (bor (bd (cs s c)) BX) f) jX = Some k -> vok (rg (cs s c) k) = true \/ bX = false)
    by (intros f k Hk; left; exact (sfix_hc _ _ _ _ _ _ _ _ HsO f k Hk)).
  assert (Hf1 := HfX). assert (Hj1 := HjX).
    assert (H1 : ccJ p c (cs s c) (pcs s c) (bd (cs t c)) r J).
    { 
        assert (Ct : cs t c = cc_fx (cs s c) (bor (bd (cs s c)) BX) (upd (fx (cs s c)) jX (Some bX))) by (rewrite E; apply cx_cs).
        assert (Pc : pcs t c = pcs s c) by (rewrite E; reflexivity).
        assert (Rt' := Rt). rewrite E in Rt'.
        assert (AG : agree r (creg p c (cs t c) (pcs t c) (tp t c) (bd (cs t c)) (Fd p c r)) J)
          by (apply (ccJ_agree p t W Wc Rt c (bd (cs t c)) r J H)).
        set (cc := cs s c) in *.
        rewrite Ct, Pc in H. rewrite Ct.
        destruct H as (A0 & A1 & A2 & A3 & A3h & A4 & A5 & A6 & A7). cbn [fx cc_fx rg] in A1, A3, A3h, A6.
        (* the registers R1 sees before the step, under which the result was fixed *)
        assert (Vk : forall k m xs, jX < J -> hplaced p c cc (pcs s c) r k m xs jX -> vok (rg cc k) = true \/ bX = false).
        { intros k m xs LJ Pl.
          destruct (cx_regs p s c jX bX BX W I1 Hf1 Hc1 (fun _ => false) (Fd p c r)) as (F & EQ).
          set (g := creg p c cc (pcs s c) (tp s c) (bor (bd cc) BX) F).
          assert (AGg : agree r g J).
          { intros q Lq. rewrite (AG q Lq). clear AG. rewrite E, cx_cs.
            change (pcs (scfix0 s c jX bX BX) c) with (pcs s c). change (tp (scfix0 s c jX bX BX) c) with (tp s c).
            transitivity (creg p c (cc_fx cc (bor (bd cc) BX) (upd (fx cc) jX (Some bX))) (pcs s c) (tp s c)
                            (bor (bd (cc_fx cc (bor (bd cc) BX) (upd (fx cc) jX (Some bX)))) (fun _ => false)) (Fd p c r) q).
            - apply (creg_Bext p c (cc_fx cc (bor (bd cc) BX) (upd (fx cc) jX (Some bX))) _ _ _ _ _ W (pend_ok_of p s c I1)).
              intros q0. unfold bor. cbn [bd cc_fx]. unfold bor.
              unfold cc in *. destruct (bd (cs s c) q0), (BX q0); reflexivity.
            - rewrite <- EQ. unfold g. apply (creg_Bext p c _ _ _ _ _ _ W (pend_ok_of p s c I1)).
              intros q0. unfold bor. unfold cc in *. destruct (bd (cs s c) q0), (BX q0); reflexivity. }
          apply (Hc1 F k).
          apply (hpend_at_char_s p s c I1). exists m, xs.
          destruct Pl as (P1 & P2 & t0 & O & F0). split; auto. split; auto. exists t0. split; auto.
          unfold first_atR in *. apply (plc_agree p W c cc (pcs s c) _ r g _ _ jX); [intros q Lq; apply AGg; lia|exact F0]. }
        split; [exact A0|]. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
        + exact A1.
        + exact A2.
        + intros j k' d' L Pl Ld. apply (A3 j k' d' L); [exact (proj2 (placed_fx _ _ _ _ _ _ _ _ _ _) Pl)|exact Ld].
        + intros j k' m xs L Pl. destruct (A3h j k' m xs L (proj2 (hplaced_fx _ _ _ _ _ _ _ _ _ _ _) Pl)) as (Q1 & Q2 & Q3).
          unfold upd in Q2, Q3. destruct (Nat.eqb_spec j jX) as [->|Nj].
          * pose proof (Vk k' m xs L Pl) as V.
            assert (NP : forall k3 d3, ~ placed p c (cc_fx cc (bor (bd cc) BX) (upd (fx cc) jX (Some bX))) (pcs s c) r k3 d3 jX).
            { intros k3 d3 Pl3. apply (placed_hplaced p (scfix0 s c jX bX BX) Rt' c r k3 d3 k' m xs jX).
              - rewrite <- E, Ct, Pc. exact Pl3.
              - rewrite <- E, Ct, Pc. exact (proj2 (hplaced_fx _ _ _ _ _ _ _ _ _ _ _) Pl). }
            pose proof Pl as (_ & _ & t0 & _ & F0). pose proof (first_atR_eofR _ _ _ _ _ _ _ _ _ F0) as Dj.
            assert (Xl : is_load (ins p c jX r) && icond (ins p c jX r) r = true)
              by (destruct (ins p c jX r) as [| |m1 x1 c1 e1 n1| |]; simpl in Dj; try discriminate; unfold icond, ieval; simpl; destruct (c1 r); [reflexivity|discriminate]).
            assert (Ci : is_cas (ins p c jX r) = true) by (apply (eofR_cas _ r _ Dj)).
            pose proof (A6 jX bX ltac:(lia) L NP Xl Ci ltac:(unfold upd; rewrite Nat.eqb_refl; reflexivity)) as V6.
            split; [exact Q1|]. split.
            { intros _ Z. destruct V as [V|Bf]; [congruence|]. rewrite Bf in V6. simpl in V6.
              rewrite <- (vd_split (r jX)), V6, Q1, <- Z. apply vd_split. }
            intros _ Vr. rewrite Vr in V6. symmetry in V6. apply andb_prop in V6 as [Bt V6].
            assert (V' : vok (rg cc k') = true) by (destruct V as [V|Bf]; [exact V|congruence]).
            split; [exact V'|]. rewrite Q1 in V6.
            apply andb_prop in Xl as [_ Ic].
            destruct (ins p c jX r) as [| |m1 x1 c1 e1 n1| |]; simpl in Ci; try discriminate.
            unfold cfailv. unfold icond, ieval in Ic. simpl in Ic, V6 |- *. rewrite Ic, V', V6. reflexivity.
          * split; [exact Q1|]. split; [exact Q2|exact Q3].
        + intros j x b L1 L2 Bj Np Fb. apply (A4 j x b); auto.
          intros Xp. apply Np. exact (proj1 (pslot_fx _ _ _ _ _ _ _ _) Xp).
        + intros j L1 L2 Np Cs Vr. apply (A5 j); auto. intros Xp. apply Np. exact (proj1 (pslot_fx _ _ _ _ _ _ _ _) Xp).
        + intros j bx L1 L2 Np Xl Ci Fxj. destruct (Nat.eq_dec j jX) as [->|Nj]; [congruence|].
          apply (A6 j bx); auto; [|unfold upd; rewrite (proj2 (Nat.eqb_neq _ _) Nj); exact Fxj].
          intros k'' d'' Pl. apply (Np k'' d''). exact (proj1 (placed_fx _ _ _ _ _ _ _ _ _ _) Pl).
        + intros j L1 L2 Np Ic Xj. apply (A7 j); auto. intros Xp. apply Np. exact (proj1 (pslot_fx _ _ _ _ _ _ _ _) Xp). }
    exact H1.
Qed.

(* DQ: bd grows, fx unchanged *)
Lemma ccJ_fx_same : forall c cc b' pc B r J, ccJ p c (cc_fx cc b' (fx cc)) pc B r J -> ccJ p c cc pc B r J.
Proof.
  intros c cc b' pc B r J H. destruct H as (A0 & A1 & A2 & A3 & A3h & A4 & A5 & A6 & A7). cbn [fx cc_fx rg] in A1, A3, A3h, A6.
  split; [exact A0|]. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  + exact A1.
  + exact A2.
  + intros j k' d' L Pl Ld. apply (A3 j k' d' L); [exact (proj2 (placed_fx _ _ _ _ _ _ _ _ _ _) Pl)|exact Ld].
  + intros j k' m xs L Pl. exact (A3h j k' m xs L (proj2 (hplaced_fx _ _ _ _ _ _ _ _ _ _ _) Pl)).
  + intros j x b L1 L2 Bj Np Fb. apply (A4 j x b); auto. intros Xp. apply Np. exact (proj1 (pslot_fx _ _ _ _ _ _ _ _) Xp).
  + intros j L1 L2 Np Cs Vr. apply (A5 j); auto. intros Xp. apply Np. exact (proj1 (pslot_fx _ _ _ _ _ _ _ _) Xp).
  + intros j bx L1 L2 Np Xl Ci Fxj. apply (A6 j bx); auto. intros k'' d'' Pl. apply (Np k'' d''). exact (proj1 (placed_fx _ _ _ _ _ _ _ _ _ _) Pl).
  + intros j L1 L2 Np Ic Xj. apply (A7 j); auto. intros Xp. apply Np. exact (proj1 (pslot_fx _ _ _ _ _ _ _ _) Xp).
Qed.

(* DQ: q_rfix at context c: bd (ccJ_fx_same), then the M2 s_cfix script for the failure (second part) *)
Lemma mono_rfix : forall c r J kF BR, t = sbd (scfail s c kF) c BR -> rfail_ok p c (cs s c) (pcs s c) (tp s c) kF BR ->
  ccJ p c (cs t c) (pcs t c) (bd (cs t c)) r J -> ccJ p c (cs s c) (pcs s c) (bd (cs t c)) r J.
Proof.
  intros c r J kF BR ER Ok H0. set (Bt := bd (cs t c)) in *.
  pose proof (rfail_ge _ _ _ _ _ _ _ Ok) as HpF. destruct Ok as (HoF & HhF & HvF & _).
  assert (H : ccJ p c (cs (scfail s c kF) c) (pcs (scfail s c kF) c) Bt r J).
  { apply (ccJ_fx_same c _ (bor (bd (cs (scfail s c kF) c)) BR)).
    assert (Ct : cs t c = cc_fx (cs (scfail s c kF) c) (bor (bd (cs (scfail s c kF) c)) BR) (fx (cs (scfail s c kF) c)))
      by (rewrite ER; unfold sbd at 1; cbn [cs]; apply upd_eq').
    assert (Pc : pcs t c = pcs (scfail s c kF) c) by (rewrite ER; reflexivity).
    rewrite Ct, Pc in H0. exact H0. }
  clear H0.
      assert (Ct : cs (scfail s c kF) c = cc_rg (cs s c) (upd (rg (cs s c)) kF (vd false (vv (rg (cs s c) kF))))) by (apply cf_cs).
      assert (Pc : pcs (scfail s c kF) c = pcs s c) by reflexivity.
      rewrite Ct, Pc in H.
      set (cc := cs s c) in *. set (g := upd (rg cc) kF (vd false (vv (rg cc kF)))) in *.
      destruct H as (A0 & A1 & A2 & A3 & A3h & A4 & A5 & A6 & A7). cbn [fx cc_rg] in A3h, A6.
      split; [exact A0|]. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
      + intros j L. rewrite (A1 j L). cbn [rg cc_rg]. unfold g, upd. destruct (Nat.eqb_spec j kF); [lia|reflexivity].
      + exact A2.
      + intros j k' d' L Pl Ld. rewrite (A3 j k' d' L (proj2 (placed_rg _ _ _ _ _ _ _ _ _) Pl) Ld). cbn [rg cc_rg]. unfold g, upd.
        destruct (Nat.eqb_spec k' kF) as [->|]; [|reflexivity]. destruct Pl as ((_ & Q & _) & _). congruence.
      + intros j k' m xs L Pl. destruct (A3h j k' m xs L (proj2 (hplaced_rg _ _ _ _ _ _ _ _ _ _) Pl)) as (Q1 & Q2 & Q3).
        cbn [rg cc_rg] in Q1, Q2, Q3. unfold g, upd in Q1, Q2, Q3. destruct (Nat.eqb_spec k' kF) as [->|Nk].
        * rewrite vok_vd in Q2. rewrite vv_vd in Q1. split; [exact Q1|]. split; [intros _ Z; congruence|].
          intros Fn Vr. rewrite (Q2 Fn eq_refl), vok_vd in Vr. discriminate.
        * split; [exact Q1|]. split; [exact Q2|exact Q3].
      + intros j x b L1 L2 Bj Np Fb. apply (A4 j x b); auto. intros Xp. apply Np. exact (proj1 (pslot_rg _ _ _ _ _ _ _) Xp).
      + intros j L1 L2 Np Cs Vr. apply (A5 j); auto. intros Xp. apply Np. exact (proj1 (pslot_rg _ _ _ _ _ _ _) Xp).
      + intros j bx L1 L2 Np Xl Ci Fxj. apply (A6 j bx); auto. intros k'' d'' Pl. apply (Np k'' d''). exact (proj1 (placed_rg _ _ _ _ _ _ _ _ _) Pl).
      + intros j L1 L2 Np Ic Xj. apply (A7 j); auto. intros Xp. apply Np. exact (proj1 (pslot_rg _ _ _ _ _ _ _) Xp).
Qed.

Lemma mono_step : forall c r J, ccJ p c (cs t c) (pcs t c) (bd (cs t c)) r J ->
  ccJ p c (cs s c) (pcs s c) (bd (cs t c)) r J.
Proof.
  intros c r J H. pose proof (Ext_step p s t R St) as X.
  assert (SP : forall k d tq j, pending (cs t c) (pcs t c) k d -> oc (cs s c) k = Some tq ->
            agree r (rg (cs t c)) (pcs t c) -> pcs t c <= j ->
            (first_at p c (cs s c) (pcs s c) r tq d j <-> first_at p c (cs t c) (pcs t c) r tq d j))
    by (intros k0 d0 tq j P O A L; apply (step_place p s t c k0 d0 tq r j); auto).
  assert (SPh : forall k m xs tq j, hpending (cs t c) (pcs t c) k m xs -> oc (cs t c) k = None -> oh (cs s c) k = Some tq ->
            agree r (rg (cs t c)) (pcs t c) -> pcs t c <= j ->
            (first_atR p c (cs s c) (pcs s c) r tq m xs j <-> first_atR p c (cs t c) (pcs t c) r tq m xs j))
    by (intros k0 m xs tq j P C O A L; apply (step_placeR p s t c k0 m xs tq r j); auto).
  assert (Rt : run p t) by (apply xS with s; auto).
  destruct (stepQ_cases p s t St) as [St0|[(cR & kR & BR & ER & OkR)|(cS & jS & kS & BS & ES & HjS & HfS & HsS)]].
  2:{ (* DQ q_rfix *) destruct (Nat.eq_dec c cR) as [<-|N]; [exact (mono_rfix c r J kR BR ER OkR H)|].
      assert (Cs : cs t c = cs s c) by (rewrite ER; unfold sbd, scfail; simpl; rewrite !upd_neq by auto; reflexivity).
      assert (Pc : pcs t c = pcs s c) by (rewrite ER; reflexivity). rewrite Cs, Pc in *. exact H. }
  2:{ (* DQ q_sfix *) destruct (Nat.eq_dec c cS) as [<-|N]; [exact (mono_sfix c r J jS true BS kS Rt ES HjS HfS HsS H)|].
      assert (Cs : cs t c = cs s c) by (rewrite ES; unfold scfix0; simpl; rewrite upd_neq by auto; reflexivity).
      assert (Pc : pcs t c = pcs s c) by (rewrite ES; reflexivity). rewrite Cs, Pc in *. exact H. }
  destruct (step_cases p s t St0) as [(c0 & i & m' & a & K & u & w & Hi & Ho & Hd & Hb & Hbh & Hbd & HwO & HvO & He & HfO & E)|[(c0 & k & d & B & m' & a & K & u & w & Lk & Ho & Hso & Hk & HwE & HvE & He & HfE & E)|[(c0 & d & Ho & Ha & Hdf & Hd & Hf & Hfh & E)|[(c0 & k & xs & B & m' & a & K & u & w & bv & Lk & Ho & Hoh & Hso & Hok & He & _ & E)|[(c0 & Kx & Ko & Kh & Kv & Kf & Kd & HfS & E)|(cX & jX & bX & BX & oX & HjX & HfX & HcX & E)]]]]].
  - (* in order *)
    destruct (Nat.eq_dec c c0) as [<-|N].
    2:{ assert (Cs : cs t c = cs s c) by (rewrite E; unfold sord, evs; simpl; apply upd_neq'; auto).
        assert (Pc : pcs t c = pcs s c) by (rewrite E; unfold sord, evs; simpl; apply upd_neq'; auto).
        rewrite Cs, Pc in *. exact H. }
    set (cc := cs s c) in *. set (k := pcs s c) in *.
    assert (Pc : pcs t c = S k) by (rewrite E; unfold sord, evs; simpl; apply upd_eq').
    assert (Oc : forall j, oc (cs t c) j = if Nat.eqb j k then Some (tm s) else oc cc j)
      by (intros j; rewrite E; unfold sord, evs; simpl; rewrite upd_eq'; reflexivity).
    assert (Oh : forall j, oh (cs t c) j = oh cc j)
      by (intros j; rewrite E; unfold sord, evs; simpl; rewrite upd_eq'; reflexivity).
    assert (Rg : forall j, rg (cs t c) j = if Nat.eqb j k then a else rg cc j)
      by (intros j; rewrite E; unfold sord, evs; simpl; rewrite upd_eq'; reflexivity).
    assert (Ai : forall j, ai (cs t c) j = if Nat.eqb j k then i else ai cc j)
      by (intros j; rewrite E; unfold sord, evs; simpl; rewrite upd_eq'; reflexivity).
    assert (Bd : bd (cs t c) = bd cc) by (rewrite E; unfold sord, evs; simpl; rewrite upd_eq'; reflexivity).
    assert (Fx : fx (cs t c) = fx cc) by (rewrite E; unfold sord, evs; simpl; rewrite upd_eq'; reflexivity).
    rewrite Pc in SP, SPh. rewrite Pc, Bd in H. rewrite Bd. destruct H as (A0 & A1 & A2 & A3 & A3h & A4 & A5 & A6 & A7).
    rewrite Fx in A3h, A6.
    assert (AgT : agree r (rg (cs t c)) (S k)) by (intros j Lj; apply A1; auto).
    assert (Ag : agree r (rg cc) k).
    { intros j Lj. rewrite A1 by lia. rewrite Rg. destruct (Nat.eqb_spec j k); [lia|auto]. }
    assert (Ik : ins p c k r = i) by (rewrite <- Hi; apply (proj1 (ins_agree p W c k r (rg cc) Ag))).
    assert (Ev : ieval i r = ieval i (rg cc)) by (rewrite <- Ik; apply (proj2 (ins_agree p W c k r (rg cc) Ag))).
    assert (Rk : r k = a) by (rewrite A1 by lia; rewrite Rg, Nat.eqb_refl; auto).
    assert (Pt : forall k' d', pending cc k k' d' -> pending (cs t c) (S k) k' d').
    { intros k' d' (P1 & P2 & P3). assert (k' <> k) by (intros ->; congruence).
      split; [lia|]. rewrite Oc, Ai. destruct (Nat.eqb_spec k' k); [lia|]. auto. }
    assert (Pth : forall k' m xs, k' <> k -> hpending cc k k' m xs -> hpending (cs t c) (S k) k' m xs).
    { intros k' m xs Nk (P1 & P2 & P3). split; [lia|]. rewrite Oh, Ai. destruct (Nat.eqb_spec k' k); [lia|]. auto. }
    assert (EXk : executes (ins p c k r) r = true -> executes i (rg cc) = true)
      by (intros Ex; rewrite Ik in Ex; rewrite (exec_agree' i r (rg cc) Ev) in Ex; exact Ex).
    assert (Nk : forall d', (exists k', pending cc k k' d') -> executes (ins p c k r) r = true -> ~ tied (ins p c k r) (inst_of d')).
    { intros d' (k' & Pk') Ex. rewrite Ik. apply (Hb (EXk Ex) k' d' Pk'). }
    assert (Mv : forall k' d' j, placed p c cc k r k' d' j -> k < j /\ placed p c (cs t c) (S k) r k' d' j).
    { intros k' d' j (Pk & tq & O & F). assert (Lkj : k < j).
      { destruct (Nat.eq_dec j k) as [->|Nj]; [|pose proof (first_at_le _ _ _ _ _ _ _ _ F); lia].
        exfalso. destruct (eof_exec_tied _ _ _ _ _ Wc (first_at_eof _ _ _ _ _ _ _ _ F)) as [Ex Tt].
        apply (Nk d' (ex_intro _ k' Pk) Ex Tt). }
      split; [exact Lkj|]. split; [apply Pt; auto|]. exists tq. split.
      - rewrite Oc. destruct (Nat.eqb_spec k' k); [subst; destruct Pk as (_ & Pk & _); congruence|auto].
      - apply (SP k' d' tq j (Pt k' d' Pk) O AgT ltac:(lia)). exact F. }
    assert (Bk : forall k' d' j, k < j -> placed p c (cs t c) (S k) r k' d' j -> placed p c cc k r k' d' j).
    { intros k' d' j Lkj (Pk & tq & O & F). destruct Pk as (Q1 & Q2 & Q3). rewrite Oc, Ai in *.
      destruct (Nat.eqb_spec k' k); [lia|].
      assert (Pq : pending cc k k' d') by (split; [lia|split; auto]).
      split; [exact Pq|]. exists tq. split; [exact O|]. apply (SP k' d' tq j (Pt k' d' Pq) O AgT ltac:(lia)). exact F. }
    (* a CAS's read alone other than at k has its place beyond k, the same in t *)
    assert (Mvh : forall k' m xs j, k' <> k -> hplaced p c cc k r k' m xs j -> k < j /\ hplaced p c (cs t c) (S k) r k' m xs j).
    { intros k' m xs j Nk' (Pk & C & tq & O & F). assert (Lkj : k < j).
      { destruct (Nat.eq_dec j k) as [->|Nj]; [|pose proof (first_atR_le _ _ _ _ _ _ _ _ _ F); lia].
        exfalso. destruct (eofR_exec_tied _ _ _ _ _ _ Wc (first_atR_eofR _ _ _ _ _ _ _ _ _ F)) as [Ex Tt].
        rewrite Ik in Tt. apply (Hbh (EXk Ex) k' m xs Pk Nk' Tt). }
      assert (Ct : oc (cs t c) k' = None) by (rewrite Oc; destruct (Nat.eqb_spec k' k); [lia|exact C]).
      split; [exact Lkj|]. split; [apply Pth; auto|]. split; [exact Ct|]. exists tq. split; [rewrite Oh; exact O|].
      apply (SPh k' m xs tq j (Pth k' m xs Nk' Pk) Ct O AgT ltac:(lia)). exact F. }
    assert (Bkh : forall k' m xs j, hplaced p c (cs t c) (S k) r k' m xs j -> hplaced p c cc k r k' m xs j).
    { intros k' m xs j (Pk & C & tq & O & F). pose proof Pk as (Q1 & Q2 & Q3). rewrite Oh, Ai in *.
      destruct (Nat.eqb_spec k' k); [lia|].
      assert (Pq : hpending cc k k' m xs) by (split; [lia|split; auto]).
      split; [exact Pq|]. split; [first [exact C|rewrite Oc in C; destruct (Nat.eqb_spec k' k); [lia|exact C]]|].
      exists tq. split; [first [exact O|rewrite Oh in O; exact O]|]. apply (SPh k' m xs tq j Pk C O AgT); [|exact F].
      pose proof (first_atR_le _ _ _ _ _ _ _ _ _ F). lia. }
    split; [lia|]. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
    + intros j L. rewrite A1 by lia. rewrite Rg. destruct (Nat.eqb_spec j k); [lia|auto].
    + intros j L1 L2 Xl. destruct (Nat.eq_dec j k) as [->|Nj]; [|apply A2; auto; lia].
      rewrite Rk. rewrite Ik in Xl.
      assert (Xr : xload i (rg cc) = false) by (unfold xload; rewrite <- (ieval_cond i r (rg cc) Ev); exact Xl).
      apply (eff_noread _ _ _ _ _ _ _ _ _ He Xr).
    + intros j k' d' L Pl Ld. destruct (Mv k' d' j Pl) as (Lkj & Pl').
      rewrite (A3 j k' d' L Pl' Ld). rewrite Rg. destruct Pl as ((P1 & P2 & P3) & _).
      destruct (Nat.eqb_spec k' k); [subst; congruence|auto].
    + intros j k' m xs L Pl. destruct (Nat.eq_dec k' k) as [->|Nk'].
      * (* the CAS's read alone at k: its write is this step *)
        destruct Pl as (Pk & C & tq & O & F).
        assert (Ej : j = k) by (apply (ord_oldh p s c i u W Wc I Hi Ho Hb Hbh Hbd r Ag m xs tq j Pk O F)). subst j.
        rewrite Rk. destruct Hbd as [(Z & _)|(t1 & Oh1 & Ci & U & Ef)]; [congruence|].
        destruct (i_half p s I c k t1 Ho Oh1 ltac:(lia)) as (_ & (xs0 & Ax) & _). fold cc in Ax. rewrite Ax in Ef.
        destruct (eofR_half i (rg cc) xs0 Ef) as (Ic & Xi).
        pose proof (proj2 (half_vals p s c k t1 I J2 Ho Oh1)) as HV. fold cc in HV. destruct (eff_read _ _ _ _ _ _ _ _ _ He Xi) as (_ & Ea).
        assert (Vo : vok (rg cc k) = true) by (apply HvO; congruence).
        assert (Wt : w = true) by (apply HwO; congruence).
        assert (Ra : a = rg cc k).
        { rewrite Ea, (areg_cas _ _ _ Ci), Wt, <- (vd_split (rg cc k)), Vo, HV, U, Ic, Ax. reflexivity. }
        rewrite Ra. split; [reflexivity|]. split; [intros _ _; reflexivity|]. intros _ _. split; [exact Vo|].
        rewrite Ik. pose proof He as He'. rewrite Wt in He'. pose proof (eff_cas_ok_e _ _ _ _ _ _ _ _ Ci He') as Ae.
        rewrite Ra in Ae. apply (cfailv_ok i r (rg cc) _ Ci Ev Vo). rewrite Ae, vv_vd. reflexivity.
      * destruct (Mvh k' m xs j Nk' Pl) as (Lkj & Pl'). pose proof (A3h j k' m xs L Pl') as Q. rewrite Rg in Q.
        destruct (Nat.eqb_spec k' k); [lia|exact Q].
    + intros j x b L1 L2 Bj Np Fb. destruct (Nat.eq_dec j k) as [->|Nj].
      * destruct Hbd as [(Z & Hbnd)|(t1 & Oh1 & Ci & U & Ef)].
        2:{ exfalso. apply Np. right. destruct (i_half p s I c k t1 Ho Oh1 ltac:(lia)) as (_ & (xs0 & Ax) & _). fold cc in Ax.
            assert (P : hpending cc k k Plain xs0) by (split; [lia|split; [congruence|rewrite Ax; reflexivity]]).
            exists k, Plain, xs0. split; [exact P|]. split; [exact Ho|]. exists t1. split; [exact Oh1|].
            apply (ord_firstR_pc p s c i u W Wc I Hi Ho Hb Hbh (or_intror (ex_intro _ t1 (conj Oh1 (conj Ci (conj U Ef))))) r t1 Plain xs0 Ag Oh1 P). }
        assert (Fb' : fbinder p c (rg cc) k x = Some b) by (rewrite <- (fbinder_agree p W c r (rg cc) k x Ag); auto).
        pose proof (fbinder_shape _ _ _ _ _ _ Fb') as (Exb & Ixb & _ & Br & Cr & Ix).
        rewrite Hi in Ix, Br, Cr.
        pose proof (Hbnd x b Bj Ix Fb') as Ux.
        pose proof (fbinder_lt _ _ _ _ _ _ Fb') as Lb.
        assert (Xl : xload i (rg cc) = true).
        { unfold xload. rewrite Cr. destruct i as [[] | | [] | |]; simpl in Br; try discriminate; reflexivity. }
        destruct (eff_read _ _ _ _ _ _ _ _ _ He Xl) as (_ & Ea).
        assert (Dk : dec p c r k x = rdval (mof s c) u x).
        { apply dec_of; [intros Z0; rewrite Ik in Z0; rewrite Z0 in Ix; destruct Ix| |rewrite Ik; exact Ix].
          rewrite Ik, Rk, Ea. apply rval_areg. }
        rewrite Dk.
        assert (Ab : agree r (rg cc) (S b)) by (apply (agree_le _ _ k); auto; lia).
        rewrite (dec_passed p s W R c r b x Ab Lb
                   ltac:(rewrite (exec_agree p W c b r (rg cc) (agree_le _ _ _ b Ab ltac:(lia))); exact Exb))
          by (rewrite (proj1 (ins_agree p W c b r (rg cc) (agree_le _ _ _ b Ab ltac:(lia)))); exact Ixb).
        rewrite (bvx_agree p W c r (rg cc) b k x _ Lb Ag).
        fold cc. pose proof (bind_val p s c b x W I J2 Lb Exb Ixb) as BV. fold cc in BV. rewrite BV, <- Ux.
        unfold rdo, rdval. reflexivity.
      * apply (A4 j x b); auto; [lia|]. intros [(k'' & d'' & Pl)|(k'' & m & xs & Pl)]; apply Np; [left|right].
        -- exists k'', d''. apply Bk; auto. lia.
        -- exists k'', m, xs. apply Bkh. exact Pl.
    + intros j L1 L2 Np Cs Vr. destruct (Nat.eq_dec j k) as [->|Nj].
      * rewrite Rk in Vr |- *. rewrite Ik in Cs |- *.
        destruct (xload i (rg cc)) eqn:Xl.
        -- destruct (eff_read _ _ _ _ _ _ _ _ _ He Xl) as (_ & Ea). rewrite Ea, (areg_cas _ _ _ Cs) in Vr |- *.
           rewrite vok_vd in Vr. rewrite vv_vd. pose proof He as He'. rewrite Vr in He'.
           rewrite (cexp_ieval _ _ _ Ev). apply (eff_w_cas _ _ _ _ _ _ _ _ _ He' Cs eq_refl).
        -- destruct (eff_noread _ _ _ _ _ _ _ _ _ He Xl) as [Az _]. rewrite Az in Vr. discriminate.
      * apply (A5 j); auto; [lia|]. intros [(k'' & d'' & Pl)|(k'' & m & xs & Pl)]; apply Np; [left|right].
        -- exists k'', d''. apply Bk; auto. lia.
        -- exists k'', m, xs. apply Bkh. exact Pl.
    + intros j bx L1 L2 Np Xl Ci Fxj. destruct (Nat.eq_dec j k) as [->|Nj].
      * (* the slot passed: its result is the result fixed there *)
        rewrite Rk. rewrite Ik in Xl, Ci |- *. rewrite (cexp_ieval _ _ _ Ev).
        apply (HfO bx Fxj Ci). apply andb_prop in Xl as [_ Xl]. unfold icond in *. rewrite <- Ev. exact Xl.
      * apply (A6 j bx); auto; [lia|]. intros k'' d'' Pl. apply (Np k'' d''). apply Bk; auto. lia.
    + (* DQ C7: the slot read no cell, its register is enc [] *)
      intros j L1 L2 Np Ic Xj. destruct (Nat.eq_dec j k) as [->|Nj].
      * rewrite Rk. rewrite Ik in Ic, Xj |- *.
        assert (Xl : xload i (rg cc) = true) by (unfold xload; rewrite <- (ieval_cond i r (rg cc) Ev); exact Xj).
        destruct (eff_read _ _ _ _ _ _ _ _ _ He Xl) as (_ & Ea). rewrite Ea, rval_areg, Ic. reflexivity.
      * apply (A7 j); auto; [lia|]. intros [(k'' & d'' & Pl)|(k'' & m & xs & Pl)]; apply Np; [left|right].
        -- exists k'', d''. apply Bk; auto. lia.
        -- exists k'', m, xs. apply Bkh. exact Pl.
  - (* early *)
    destruct (Nat.eq_dec c c0) as [<-|N].
    2:{ assert (Cs : cs t c = cs s c) by (rewrite E; unfold searly, set_es, searly0, evs; simpl; apply upd_neq'; auto).
        assert (Pc : pcs t c = pcs s c) by (rewrite E; reflexivity).
        rewrite Cs, Pc in *. exact H. }
    set (cc := cs s c) in *. set (pc := pcs s c) in *.
    assert (Pc : pcs t c = pc) by (rewrite E; reflexivity).
    assert (Oc : forall j, oc (cs t c) j = if Nat.eqb j k then Some (tm s) else oc cc j)
      by (intros j; rewrite E; unfold searly, set_es, searly0, evs; simpl; rewrite upd_eq'; reflexivity).
    assert (Oh : forall j, oh (cs t c) j = oh cc j)
      by (intros j; rewrite E; unfold searly, set_es, searly0, evs; simpl; rewrite upd_eq'; reflexivity).
    assert (Rg : forall j, rg (cs t c) j = if Nat.eqb j k then a else rg cc j)
      by (intros j; rewrite E; unfold searly, set_es, searly0, evs; simpl; rewrite upd_eq'; reflexivity).
    assert (Ai : forall j, ai (cs t c) j = if Nat.eqb j k then inst_of d else ai cc j)
      by (intros j; rewrite E; unfold searly, set_es, searly0, evs; simpl; rewrite upd_eq'; reflexivity).
    assert (Bd : bd (cs t c) = bor (bd cc) B) by (rewrite E; unfold searly, set_es, searly0, evs; simpl; rewrite upd_eq'; reflexivity).
    assert (Fx : fx (cs t c) = fx cc) by (rewrite E; unfold searly, set_es, searly0, evs; simpl; rewrite upd_eq'; reflexivity).
    rewrite Pc in SP, SPh. rewrite Pc, Bd in H. rewrite Bd.
    assert (Pt : forall k' d', pending cc pc k' d' -> pending (cs t c) pc k' d').
    { intros k' d' (P1 & P2 & P3). assert (k' <> k) by (intros ->; congruence).
      split; [lia|]. rewrite Oc, Ai. destruct (Nat.eqb_spec k' k); [lia|]. auto. }
    assert (Rgk : forall k', k' <> k -> rg (cs t c) k' = rg cc k') by (intros k' N'; rewrite Rg; destruct (Nat.eqb_spec k' k); [lia|auto]).
    (* by induction on J *)
    revert H. induction J as [J IH] using lt_wf_ind. intros H.
    pose proof H as Hq. destruct Hq as (A0 & A1 & A2 & A3 & A3h & A4 & A5 & A6 & A7). rewrite Fx in A3h, A6.
    assert (AgT : agree r (rg (cs t c)) pc) by (intros j Lj; apply A1; auto).
    assert (Fw : forall k' d' j, placed p c cc pc r k' d' j -> placed p c (cs t c) pc r k' d' j).
    { intros k' d' j (Pk & tq & O & F). split; [apply Pt; auto|]. exists tq. split.
      - rewrite Oc. destruct (Nat.eqb_spec k' k); [subst; destruct Pk as (_ & Pk & _); congruence|auto].
      - apply (SP k' d' tq j (Pt k' d' Pk) O AgT (first_at_le _ _ _ _ _ _ _ _ F)). exact F. }
    destruct Hk as [(Zoh & Hok')|(t1 & xs & ev & nv & Zoh & -> & U & Ac & Okw)].
    + (* an access *)
      assert (Ct : cs t c = cce s c k d B m' a u w) by (rewrite E; apply cce_eq).
      assert (Ph : forall k' m xs j, hplaced p c cc pc r k' m xs j <-> hplaced p c (cs t c) pc r k' m xs j).
      { intros k' m xs j. rewrite Ct. symmetry. apply (hplaced_e p s c k d B m' a u w I Lk Ho Zoh r j k' m xs). }
      split; [lia|]. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
      * intros j L. rewrite A1 by lia. rewrite Rg. destruct (Nat.eqb_spec j k); [lia|auto].
      * auto.
      * intros j k' d' L Pl Ld. rewrite (A3 j k' d' L (Fw k' d' j Pl) Ld).
        rewrite Rg. destruct Pl as ((P1 & P2 & P3) & _). destruct (Nat.eqb_spec k' k); [subst; congruence|auto].
      * intros j k' m xs L Pl. pose proof (A3h j k' m xs L (proj1 (Ph k' m xs j) Pl)) as Q.
        rewrite Rgk in Q; [exact Q|]. intros ->. destruct Pl as ((_ & Q' & _) & _). congruence.
      * intros j x b L1 L2 Bj Np Fb.
        destruct (pslot_or p t c r j W Wc Rt) as [Ps|Ps]; rewrite Pc in Ps.
        2:{ apply (A4 j x b); auto. }
        destruct Ps as [(k'' & d'' & Pl)|(k'' & m & xs & Pl)].
        2:{ exfalso. apply Np. right. exists k'', m, xs. apply Ph. exact Pl. }
        pose proof Pl as ((Q1 & Q2 & Q3) & tq & O & Fk). rewrite Oc in Q2, O. rewrite Ai in Q3.
        destruct (Nat.eqb_spec k'' k) as [->|Nk].
        2:{ exfalso. apply Np. left. exists k'', d''. destruct Pl as (Pl & _). assert (Pq : pending cc pc k'' d'') by (split; [lia|split; auto]).
            split; [exact Pq|]. exists tq. split; [exact O|].
            apply (proj2 (SP k'' d'' tq j Pl O AgT (first_at_le _ _ _ _ _ _ _ _ Fk))). exact Fk. }
        injection O as <-. apply inst_of_inj in Q3. subst d''.
        assert (Fk0 : first_at p c cc pc r (tm s) d j).
        { rewrite Ct in Fk. apply (early_same p s c k d B m' a u w Lk Ho Zoh r (tm s) d j (le_n _)). exact Fk. }
        pose proof (fbinder_shape _ _ _ _ _ _ Fb) as (Exr & Ixr & _ & Br & Cr & Ix).
        pose proof (first_at_eof _ _ _ _ _ _ _ _ Fk0) as Dj.
        assert (Ld : is_load (inst_of d) = true).
        { rewrite <- (eof_load _ _ _ Dj), Cr. destruct (ins p c j r) as [[] | | [] | |]; simpl in Br; try discriminate; reflexivity. }
        assert (Rj : r j = a) by (rewrite (A3 j k d L2 Pl Ld), Rg, Nat.eqb_refl; reflexivity).
        assert (Hj : ccJ p c cc pc (bor (bd cc) B) r j) by (apply (IH j L2); apply (ccJ_le _ _ _ _ _ _ J j H); lia).
        pose proof (ccJ_agree p s W Wc R c (bor (bd cc) B) r j Hj) as Ag.
        destruct (Hok' (Fd p c r)) as (j0 & Lj0 & F0 & Bind).
        set (g := creg p c cc pc (tp s c) (bor (bd cc) B) (Fd p c r)) in *.
        assert (Ej0 : j0 = j).
        { apply (first_at_unique _ _ _ _ _ _ _ _ _ Wc F0). apply (first_at_agree p W c cc pc r g (tm s) d j Ag Fk0). }
        subst j0.
        assert (Fbg : fbinder p c g j x = Some b) by (rewrite <- (fbinder_agree p W c r g j x Ag); exact Fb).
        rewrite (eof_icells _ _ _ Dj) in Ix.
        destruct (Bind Ld x b Ix Bj Fbg) as (k' & Lkb & Ub).
        pose proof (fbinder_lt _ _ _ _ _ _ Fb) as Lbj.
        assert (Lk' : lead p c cc pc (tp s c) r b = Some k')
          by (rewrite <- Lkb; apply (lead_agree p c cc pc (tp s c) r g b W (pend_ok_of p s c I)); apply (agree_le r g j b Ag); lia).
        rewrite (dec_lead p s W R c (bor (bd cc) B) r j x b k' Hj Lbj Exr Ixr Lk').
        rewrite (bvx_agree p W c r g b j x _ Lbj Ag).
        pose proof (lead_read p s c _ (Fd p c r) j (tm s) d x b k' W I J2 F0 Fbg Lkb) as LR. assert (LR2 : bvx p c g b x (rv (cs s c) k' x) = rdo s (rw (cs s c) k' x) x) by exact LR. rewrite LR2. fold cc. rewrite <- Ub.
        assert (Xl : xload (inst_of d) (rg cc) = true) by (unfold xload; rewrite Ld; destruct d; reflexivity).
        destruct (eff_read _ _ _ _ _ _ _ _ _ He Xl) as (_ & Ea).
        transitivity (rdval (mof s c) u x); [|unfold rdo, rdval; reflexivity].
        apply (dec_of p c r j (rdval (mof s c) u) x).
        -- intros Z. rewrite (eof_icells _ _ _ Dj) in Z. rewrite Z in Ix. destruct Ix.
        -- rewrite Rj, Ea. rewrite (rval_iscas (ins p c j r) (inst_of d)) by (symmetry; apply (proj1 (eof_cexp _ _ _ r Dj))).
           rewrite rval_areg, (eof_icells _ _ _ Dj). reflexivity.
        -- rewrite (eof_icells _ _ _ Dj). exact Ix.
      * intros j L1 L2 Np Cs Vr.
        destruct (pslot_or p t c r j W Wc Rt) as [Ps|Ps]; rewrite Pc in Ps.
        2:{ apply (A5 j); auto. }
        destruct Ps as [(k'' & d'' & Pl)|(k'' & m & xs & Pl)].
        2:{ exfalso. apply Np. right. exists k'', m, xs. apply Ph. exact Pl. }
        pose proof Pl as ((Q1 & Q2 & Q3) & tq & O & Fk). rewrite Oc in Q2, O. rewrite Ai in Q3.
        destruct (Nat.eqb_spec k'' k) as [->|Nk].
        2:{ exfalso. apply Np. left. exists k'', d''. destruct Pl as (Pl & _). assert (Pq : pending cc pc k'' d'') by (split; [lia|split; auto]).
            split; [exact Pq|]. exists tq. split; [exact O|].
            apply (proj2 (SP k'' d'' tq j Pl O AgT (first_at_le _ _ _ _ _ _ _ _ Fk))). exact Fk. }
        injection O as <-. apply inst_of_inj in Q3. subst d''.
        assert (Fk0 : first_at p c cc pc r (tm s) d j).
        { rewrite Ct in Fk. apply (early_same p s c k d B m' a u w Lk Ho Zoh r (tm s) d j (le_n _)). exact Fk. }
        pose proof (first_at_eof _ _ _ _ _ _ _ _ Fk0) as Dj. destruct (eof_cexp _ _ _ (rg cc) Dj) as (Csd & Ce).
        rewrite Cs in Csd.
        assert (Ld : is_load (inst_of d) = true) by (destruct d; simpl in Csd; try discriminate; reflexivity).
        assert (Rj : r j = a) by (rewrite (A3 j k d L2 Pl Ld), Rg, Nat.eqb_refl; reflexivity).
        assert (Xl : xload (inst_of d) (rg cc) = true) by (unfold xload; rewrite Ld; destruct d; reflexivity).
        destruct (eff_read _ _ _ _ _ _ _ _ _ He Xl) as (_ & Ea).
        rewrite Rj, Ea, (areg_cas _ _ _ Csd) in Vr |- *. rewrite vok_vd in Vr. rewrite vv_vd, <- Ce.
        pose proof He as He'. rewrite Vr in He'. apply (eff_w_cas _ _ _ _ _ _ _ _ _ He' Csd eq_refl).
      * intros j bx L1 L2 Np Xl Ci Fxj.
        destruct (pslot_or p t c r j W Wc Rt) as [Ps|Ps].
        2:{ apply (A6 j bx); auto. intros k'' d'' Pl. apply Ps. left. rewrite Pc. eauto. }
        destruct Ps as [(k'' & d'' & Pl)|(k'' & m & xs & Pl)].
        2:{ apply (A6 j bx); auto. intros k3 d3 Pl3. apply (placed_hplaced p t Rt c r k3 d3 k'' m xs j); [rewrite Pc; exact Pl3|exact Pl]. }
        rewrite Pc in Pl.
        pose proof Pl as ((Q1 & Q2 & Q3) & tq & O & Fk). rewrite Oc in Q2, O. rewrite Ai in Q3.
        destruct (Nat.eqb_spec k'' k) as [->|Nk].
        2:{ exfalso. apply (Np k'' d''). destruct Pl as (Pl & _). assert (Pq : pending cc pc k'' d'') by (split; [lia|split; auto]).
            split; [exact Pq|]. exists tq. split; [exact O|].
            apply (proj2 (SP k'' d'' tq j Pl O AgT (first_at_le _ _ _ _ _ _ _ _ Fk))). exact Fk. }
        injection O as <-. apply inst_of_inj in Q3. subst d''.
        assert (Fk0 : first_at p c cc pc r (tm s) d j).
        { rewrite Ct in Fk. apply (early_same p s c k d B m' a u w Lk Ho Zoh r (tm s) d j (le_n _)). exact Fk. }
        pose proof (first_at_eof _ _ _ _ _ _ _ _ Fk0) as Dj. destruct (eof_cexp _ _ _ (rg cc) Dj) as (Csd & Ce).
        assert (Ld : is_load (inst_of d) = true) by (rewrite Ci in Csd; destruct d; simpl in Csd; try discriminate; reflexivity).
        assert (Rj : r j = a) by (rewrite (A3 j k d L2 Pl Ld), Rg, Nat.eqb_refl; reflexivity).
        assert (Hj : ccJ p c cc pc (bor (bd cc) B) r j) by (apply (IH j L2); apply (ccJ_le _ _ _ _ _ _ J j H); lia).
        pose proof (ccJ_agree p s W Wc R c (bor (bd cc) B) r j Hj) as Ag.
        assert (Fg : first_at p c cc pc (creg p c cc pc (tp s c) (bor (bd cc) B) (Fd p c r)) (tm s) d j)
          by (apply (first_at_agree p W c cc pc r _ (tm s) d j Ag Fk0)).
        pose proof (proj1 HfE Zoh (Fd p c r) j Fg) as Fo.
        rewrite Rj, <- Ce. apply (Fo bx Fxj); [rewrite Csd; exact Ci|destruct d; reflexivity].
      * (* DQ C7: placed early here, it read no cell *)
        intros j L1 L2 Np Ic Xj.
        destruct (pslot_or p t c r j W Wc Rt) as [Ps|Ps]; rewrite Pc in Ps.
        2:{ apply (A7 j); auto. }
        destruct Ps as [(k'' & d'' & Pl)|(k'' & m & xs & Pl)].
        2:{ exfalso. apply Np. right. exists k'', m, xs. apply Ph. exact Pl. }
        pose proof Pl as ((Q1 & Q2 & Q3) & tq & O & Fk). rewrite Oc in Q2, O. rewrite Ai in Q3.
        destruct (Nat.eqb_spec k'' k) as [->|Nk].
        2:{ exfalso. apply Np. left. exists k'', d''. destruct Pl as (Pl & _). assert (Pq : pending cc pc k'' d'') by (split; [lia|split; auto]).
            split; [exact Pq|]. exists tq. split; [exact O|].
            apply (proj2 (SP k'' d'' tq j Pl O AgT (first_at_le _ _ _ _ _ _ _ _ Fk))). exact Fk. }
        injection O as <-. apply inst_of_inj in Q3. subst d''.
        assert (Fk0 : first_at p c cc pc r (tm s) d j).
        { rewrite Ct in Fk. apply (early_same p s c k d B m' a u w Lk Ho Zoh r (tm s) d j (le_n _)). exact Fk. }
        pose proof (first_at_eof _ _ _ _ _ _ _ _ Fk0) as Dj.
        assert (Ld : is_load (inst_of d) = true) by (rewrite <- (eof_load _ _ _ Dj); exact Xj).
        assert (Rj : r j = a) by (rewrite (A3 j k d L2 Pl Ld), Rg, Nat.eqb_refl; reflexivity).
        assert (Xl : xload (inst_of d) (rg cc) = true) by (unfold xload; rewrite Ld; destruct d; reflexivity).
        destruct (eff_read _ _ _ _ _ _ _ _ _ He Xl) as (_ & Ea).
        rewrite Rj, Ea, (rval_iscas (ins p c j r) (inst_of d)) by (symmetry; apply (proj1 (eof_cexp _ _ _ r Dj))).
        rewrite rval_areg, <- (eof_icells _ _ _ Dj), Ic. reflexivity.
    + (* the write of a CAS whose read happened alone *)
      subst u. set (d := DCas Plain xs ev nv) in *.
      assert (Ct : cs t c = ccw s c k xs ev nv B m' a w) by (rewrite E; apply ccw_eq).
      assert (Ph : forall k' m0 xs0 j, k' <> k -> hplaced p c cc pc r k' m0 xs0 j -> hplaced p c (cs t c) pc r k' m0 xs0 j).
      { intros k' m0 xs0 j Nk Pl. rewrite Ct. apply (cwe_hplaced p s c k t1 xs ev nv B m' a K w I J2 Lk Ho Zoh Ac He HvE HwE r j k' m0 xs0). auto. }
      assert (Ph' : forall k' m0 xs0 j, hplaced p c (cs t c) pc r k' m0 xs0 j -> k' <> k /\ hplaced p c cc pc r k' m0 xs0 j).
      { intros k' m0 xs0 j Pl. rewrite Ct in Pl. apply (cwe_hplaced p s c k t1 xs ev nv B m' a K w I J2 Lk Ho Zoh Ac He HvE HwE r j k' m0 xs0). exact Pl. }
      (* below J, the write's place under r is its read's place *)
      assert (WP : forall j, j < J -> (first_atR p c cc pc r t1 Plain xs j <-> first_at p c (cs t c) pc r (tm s) d j)).
      { intros j L2. destruct (Nat.lt_ge_cases j pc) as [Lp|Lp].
        { split; intros F; exfalso; [pose proof (first_atR_le _ _ _ _ _ _ _ _ _ F)|pose proof (first_at_le _ _ _ _ _ _ _ _ F)]; lia. }
        assert (Hj : ccJ p c cc pc (bor (bd cc) B) r j) by (apply (IH j L2); apply (ccJ_le _ _ _ _ _ _ J j H); lia).
        pose proof (ccJ_agree p s W Wc R c (bor (bd cc) B) r j Hj) as Ag.
        set (g := creg p c cc pc (tp s c) (bor (bd cc) B) (Fd p c r)) in *.
        destruct (Okw (Fd p c r)) as (j0 & Lj0 & FR0 & ED0 & BT0). fold g in FR0, ED0, BT0.
        assert (NP0 : first_at p c (ccw s c k xs ev nv B m' a w) pc g (tm s) d j0)
          by (apply (cwe_place p s c k t1 xs ev nv B m' a K w Wc I J2 Lk Ho Zoh Ac He HvE HwE g j0 FR0 ED0 BT0)).
        rewrite Ct. split.
        - intros F. assert (FRg : first_atR p c cc pc g t1 Plain xs j)
            by (unfold first_atR in *; apply (plc_agree p W c cc pc _ r g _ _ j Ag F)).
          pose proof (first_atR_unique p c cc pc g t1 Plain xs j0 j Wc FR0 FRg) as ->.
          apply (first_at_agree p W c _ pc g r _ d j); [intros q Lq; symmetry; apply Ag; auto|exact NP0].
        - intros F. assert (Fg : first_at p c (ccw s c k xs ev nv B m' a w) pc g (tm s) d j)
            by (apply (first_at_agree p W c _ pc r g _ d j Ag F)).
          pose proof (first_at_unique p c _ pc g (tm s) d j0 j Wc NP0 Fg) as ->.
          unfold first_atR in *. apply (plc_agree p W c cc pc _ g r _ _ j); [intros q Lq; symmetry; apply Ag; auto|exact FR0]. }
      split; [lia|]. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
      * intros j L. rewrite A1 by lia. rewrite Rg. destruct (Nat.eqb_spec j k); [lia|auto].
      * auto.
      * intros j k' d' L Pl Ld. assert (Nk : k' <> k) by (intros ->; destruct Pl as ((_ & Q & _) & _); congruence).
        assert (Plt : placed p c (cs t c) pc r k' d' j) by (rewrite Ct; apply (cwe_placed p s c k t1 xs ev nv B m' a K w I J2 Lk Ho Zoh Ac He HvE HwE r j k' d'); right; auto).
        rewrite (A3 j k' d' L Plt Ld). apply Rgk. exact Nk.
      * intros j k' m0 xs0 L Pl. destruct (Nat.eq_dec k' k) as [->|Nk].
        -- destruct Pl as ((_ & _ & P3) & C & tq & O & F). rewrite Zoh in O. injection O as <-.
           rewrite Ac in P3. injection P3 as <- <-.
           assert (Plt : placed p c (cs t c) pc r k d j).
           { split; [split; [lia|split; [rewrite Oc, Nat.eqb_refl; discriminate|rewrite Ai, Nat.eqb_refl; reflexivity]]|].
             exists (tm s). split; [rewrite Oc, Nat.eqb_refl; reflexivity|]. apply WP; auto. }
           assert (Rj : r j = a) by (rewrite (A3 j k d L Plt eq_refl), Rg, Nat.eqb_refl; reflexivity).
           assert (Vo : vok (rg cc k) = true) by (apply HvE; congruence).
           assert (Wt : w = true) by (apply HwE; congruence).
           pose proof (proj2 (half_vals p s c k t1 I J2 Ho Zoh)) as HV. fold cc in HV. destruct (eff_read _ _ _ _ _ _ _ _ _ He eq_refl) as (_ & Ea).
           assert (Ra : a = rg cc k) by (rewrite Ea; simpl areg; rewrite Wt, <- (vd_split (rg cc k)), Vo, HV, Ac; reflexivity).
           rewrite Rj, Ra. split; [reflexivity|]. split; [intros _ _; reflexivity|]. intros _ _. split; [exact Vo|].
           destruct Plt as (_ & tq' & _ & Fq). pose proof (first_at_eof _ _ _ _ _ _ _ _ Fq) as Dj.
           destruct (eof_cexp _ _ _ r Dj) as (Csd & Ce).
           pose proof He as He'. rewrite Wt in He'. pose proof (eff_cas_ok_e _ (inst_of d) _ _ _ _ _ _ eq_refl He') as Ae.
           apply (cfailv_ok (ins p c j r) r r (rg cc k)); [rewrite <- Csd; reflexivity|reflexivity|exact Vo|].
           change (vv (rg cc k) = cexp (ins p c j r) r). rewrite <- Ce, <- Ra, Ae, vv_vd. reflexivity.
        -- pose proof (A3h j k' m0 xs0 L (Ph k' m0 xs0 j Nk Pl)) as Q. rewrite (Rgk k' Nk) in Q. exact Q.
      * intros j x b L1 L2 Bj Np Fb. apply (A4 j x b); auto.
        intros [(k'' & d'' & Pl)|(k'' & m0 & xs0 & Pl)]; apply Np.
        -- rewrite Ct in Pl. apply (cwe_placed p s c k t1 xs ev nv B m' a K w I J2 Lk Ho Zoh Ac He HvE HwE r j k'' d'') in Pl.
           destruct Pl as [(-> & -> & F)|(_ & Pl)]; [|left; eauto].
           right. exists k, Plain, xs. split; [split; [lia|split; [congruence|rewrite Ac; reflexivity]]|].
           split; [exact Ho|]. exists t1. split; [exact Zoh|]. apply WP; [exact L2|]. rewrite Ct. exact F.
        -- right. apply Ph' in Pl. destruct Pl as (_ & Pl). eauto.
      * intros j L1 L2 Np Cs Vr. apply (A5 j); auto.
        intros [(k'' & d'' & Pl)|(k'' & m0 & xs0 & Pl)]; apply Np.
        -- rewrite Ct in Pl. apply (cwe_placed p s c k t1 xs ev nv B m' a K w I J2 Lk Ho Zoh Ac He HvE HwE r j k'' d'') in Pl.
           destruct Pl as [(-> & -> & F)|(_ & Pl)]; [|left; eauto].
           right. exists k, Plain, xs. split; [split; [lia|split; [congruence|rewrite Ac; reflexivity]]|].
           split; [exact Ho|]. exists t1. split; [exact Zoh|]. apply WP; [exact L2|]. rewrite Ct. exact F.
        -- right. apply Ph' in Pl. destruct Pl as (_ & Pl). eauto.
      * intros j bx L1 L2 Np Xl Ci Fxj.
        destruct (pslot_or p t c r j W Wc Rt) as [Ps|Ps].
        2:{ apply (A6 j bx); auto. intros k'' d'' Pl. apply Ps. left. rewrite Pc. eauto. }
        destruct Ps as [(k'' & d'' & Pl)|(k'' & m0 & xs0 & Pl)].
        2:{ apply (A6 j bx); auto. intros k3 d3 Pl3. apply (placed_hplaced p t Rt c r k3 d3 k'' m0 xs0 j); [rewrite Pc; exact Pl3|exact Pl]. }
        rewrite Pc in Pl. pose proof Pl as Plt. rewrite Ct in Pl.
        apply (cwe_placed p s c k t1 xs ev nv B m' a K w I J2 Lk Ho Zoh Ac He HvE HwE r j k'' d'') in Pl.
        destruct Pl as [(-> & -> & F)|(_ & Pl)]; [|exfalso; apply (Np k'' d'' Pl)].
        assert (Rj : r j = a) by (rewrite (A3 j k d L2 Plt eq_refl), Rg, Nat.eqb_refl; reflexivity).
        assert (FR : first_atR p c cc pc r t1 Plain xs j) by (apply WP; [exact L2|rewrite Ct; exact F]).
        assert (Hj : ccJ p c cc pc (bor (bd cc) B) r j) by (apply (IH j L2); apply (ccJ_le _ _ _ _ _ _ J j H); lia).
        pose proof (ccJ_agree p s W Wc R c (bor (bd cc) B) r j Hj) as Ag.
        assert (FRg : first_atR p c cc pc (creg p c cc pc (tp s c) (bor (bd cc) B) (Fd p c r)) t1 Plain xs j)
          by (unfold first_atR in *; apply (plc_agree p W c cc pc _ r _ _ _ j Ag FR)).
        pose proof (proj2 HfE t1 xs ev nv (Fd p c r) j Zoh eq_refl FRg) as Fo.
        pose proof (first_at_eof _ _ _ _ _ _ _ _ F) as Dj. destruct (eof_cexp _ _ _ (rg cc) Dj) as (Csd & Ce).
        rewrite Rj, <- Ce. apply (Fo bx Fxj); reflexivity.
      * intros j L1 L2 Np Ic Xj. apply (A7 j); auto.
        intros [(k'' & d'' & Pl)|(k'' & m0 & xs0 & Pl)]; apply Np.
        -- rewrite Ct in Pl. apply (cwe_placed p s c k t1 xs ev nv B m' a K w I J2 Lk Ho Zoh Ac He HvE HwE r j k'' d'') in Pl.
           destruct Pl as [(-> & -> & F)|(_ & Pl)]; [|left; eauto].
           right. exists k, Plain, xs. split; [split; [lia|split; [congruence|rewrite Ac; reflexivity]]|].
           split; [exact Ho|]. exists t1. split; [exact Zoh|]. apply WP; [exact L2|]. rewrite Ct. exact F.
        -- right. apply Ph' in Pl. destruct Pl as (_ & Pl). eauto.
  - (* match *)
    destruct (Nat.eq_dec c c0) as [<-|N].
    2:{ assert (Cs : cs t c = cs s c) by (rewrite E; unfold smatch; simpl; apply upd_neq'; auto).
        assert (Pc : pcs t c = pcs s c) by (rewrite E; unfold smatch; simpl; apply upd_neq'; auto).
        rewrite Cs, Pc in *. exact H. }
    set (cc := cs s c) in *. set (k := pcs s c) in *.
    assert (Pc : pcs t c = S k) by (rewrite E; unfold smatch; simpl; apply upd_eq').
    assert (Oc : oc (cs t c) = oc cc) by (rewrite E; unfold smatch; simpl; rewrite upd_eq'; reflexivity).
    assert (Oh : oh (cs t c) = oh cc) by (rewrite E; unfold smatch; simpl; rewrite upd_eq'; reflexivity).
    assert (Rg : rg (cs t c) = rg cc) by (rewrite E; unfold smatch; simpl; rewrite upd_eq'; reflexivity).
    assert (Ai : forall j, ai (cs t c) j = if Nat.eqb j k then ins p c k (rg cc) else ai cc j)
      by (intros j; rewrite E; unfold smatch; simpl; rewrite upd_eq'; reflexivity).
    assert (Bd : bd (cs t c) = bd cc) by (rewrite E; unfold smatch; simpl; rewrite upd_eq'; reflexivity).
    assert (Fx : fx (cs t c) = fx cc) by (rewrite E; unfold smatch; simpl; rewrite upd_eq'; reflexivity).
    rewrite Pc in SP, SPh. rewrite Pc, Bd in H. rewrite Bd. destruct H as (A0 & A1 & A2 & A3 & A3h & A4 & A5 & A6 & A7).
    rewrite Fx in A3h, A6.
    assert (AgT : agree r (rg (cs t c)) (S k)) by (intros j Lj; apply A1; auto).
    rewrite Rg in A1, A3, A3h.
    assert (Ag : agree r (rg cc) k) by (intros j Lj; apply A1; lia).
    assert (Dk : eof (ins p c k r) r = Some d) by (rewrite (eof_agree p W c k r (rg cc) Ag); exact Hdf).
    assert (Pk : pending cc k k d) by (split; [lia|split; auto]).
    assert (Ote : exists te, oc cc k = Some te) by (destruct (oc cc k); [eauto|congruence]). destruct Ote as (te & Ote).
    assert (Fkk : first_at p c cc k r te d k) by (apply (place_pc p s c d W Wc Hdf Hf Hfh r te Ag Ote)).
    assert (Pt : forall k' d', k' <> k -> pending cc k k' d' -> pending (cs t c) (S k) k' d').
    { intros k' d' Nk (P1 & P2 & P3). split; [lia|]. rewrite Oc, Ai. destruct (Nat.eqb_spec k' k); [lia|]. auto. }
    assert (Pth : forall k' m xs, k' <> k -> hpending cc k k' m xs -> hpending (cs t c) (S k) k' m xs).
    { intros k' m xs Nk (P1 & P2 & P3). split; [lia|]. rewrite Oh, Ai. destruct (Nat.eqb_spec k' k); [lia|]. auto. }
    assert (Mv : forall k' d' j, k' <> k -> placed p c cc k r k' d' j -> k < j /\ placed p c (cs t c) (S k) r k' d' j).
    { intros k' d' j Nk (Pq & tq & O & F). assert (Lkj : k < j).
      { destruct (Nat.eq_dec j k) as [->|Nj]; [|pose proof (first_at_le _ _ _ _ _ _ _ _ F); lia].
        exfalso. pose proof (first_at_eof _ _ _ _ _ _ _ _ F) as D'. rewrite Dk in D'. injection D' as <-.
        apply (first_at_free _ _ _ _ _ _ _ _ F). exists k, te, d. split; [exact Pk|]. split; [exact Ote|]. split; [|exact Fkk].
        apply (Hf k' d te tq Pq Nk Ote O). apply (eof_tied_self p c k r d Wc Dk). }
      split; [exact Lkj|]. split; [apply Pt; auto|]. exists tq. split; [rewrite Oc; exact O|].
      apply (SP k' d' tq j (Pt k' d' Nk Pq) O AgT ltac:(lia)). exact F. }
    assert (Bk : forall k' d' j, placed p c (cs t c) (S k) r k' d' j -> placed p c cc k r k' d' j).
    { intros k' d' j (Pq & tq & O & F). destruct Pq as (Q1 & Q2 & Q3). rewrite Oc, Ai in *.
      destruct (Nat.eqb_spec k' k) as [Ek|Nk]; [lia|].
      assert (Pq : pending cc k k' d') by (split; [lia|split; auto]).
      split; [exact Pq|]. exists tq. split; [exact O|]. apply (SP k' d' tq j (Pt k' d' Nk Pq) O AgT); [|exact F].
      pose proof (first_at_le _ _ _ _ _ _ _ _ F). lia. }
    assert (Mvh : forall k' m xs j, hplaced p c cc k r k' m xs j -> k < j /\ hplaced p c (cs t c) (S k) r k' m xs j).
    { intros k' m xs j (Pq & C & tq & O & F). assert (Nk : k' <> k) by (intros ->; congruence).
      assert (Lkj : k < j).
      { destruct (Nat.eq_dec j k) as [->|Nj]; [|pose proof (first_atR_le _ _ _ _ _ _ _ _ _ F); lia].
        exfalso. pose proof (first_atR_eofR _ _ _ _ _ _ _ _ _ F) as D'.
        destruct (eofR_exec_tied _ _ _ _ _ _ Wc D') as [_ Tt]. apply (tied_eof_l _ _ _ _ Dk) in Tt.
        apply (first_atR_free _ _ _ _ _ _ _ _ _ F). exists k, te, d. split; [exact Pk|]. split; [exact Ote|]. split; [|exact Fkk].
        apply (Hfh k' m xs te tq Pq Nk Ote O Tt). }
      split; [exact Lkj|]. split; [apply Pth; auto|]. split; [rewrite Oc; exact C|]. exists tq. split; [rewrite Oh; exact O|].
      apply (SPh k' m xs tq j (Pth k' m xs Nk Pq) ltac:(rewrite Oc; exact C) O AgT ltac:(lia)). exact F. }
    assert (Bkh : forall k' m xs j, hplaced p c (cs t c) (S k) r k' m xs j -> hplaced p c cc k r k' m xs j).
    { intros k' m xs j (Pq & C & tq & O & F). pose proof Pq as (Q1 & Q2 & Q3). rewrite Oh, Ai in *.
      destruct (Nat.eqb_spec k' k) as [Ek|Nk]; [lia|].
      assert (Pq' : hpending cc k k' m xs) by (split; [lia|split; auto]).
      split; [exact Pq'|]. split; [rewrite Oc in C; exact C|]. exists tq. split; [first [exact O|rewrite Oh in O; exact O]|].
      apply (SPh k' m xs tq j Pq C O AgT); [|exact F]. pose proof (first_atR_le _ _ _ _ _ _ _ _ _ F). lia. }
    split; [lia|]. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
    + intros j L. apply A1. lia.
    + intros j L1 L2 Xl. destruct (Nat.eq_dec j k) as [->|Nj]; [|apply A2; auto; lia].
      rewrite A1 by lia. rewrite (eof_load _ _ _ Dk) in Xl. apply (rg_store_of p s c d I J2 Ho Ha Hdf Xl).
    + intros j k' d' L Pl Ld. destruct (Nat.eq_dec k' k) as [->|Nk].
      * destruct Pl as ((_ & _ & P3) & tq & O & F). rewrite Ha in P3. apply inst_of_inj in P3. subst d'.
        rewrite Ote in O. injection O as <-.
        rewrite (first_at_unique _ _ _ _ _ _ _ _ _ Wc F Fkk). apply A1. lia.
      * destruct (Mv k' d' j Nk Pl) as (Lkj & Pl'). rewrite (A3 j k' d' L Pl' Ld). reflexivity.
    + intros j k' m xs L Pl. destruct (Mvh k' m xs j Pl) as (Lkj & Pl'). pose proof (A3h j k' m xs L Pl') as Q. rewrite ?Rg in Q. exact Q.
    + intros j x b L1 L2 Bj Np Fb. destruct (Nat.eq_dec j k) as [->|Nj].
      * exfalso. apply Np. left. exists k, d. split; [exact Pk|]. exists te. split; [exact Ote|exact Fkk].
      * apply (A4 j x b); auto; [lia|]. intros [(k'' & d'' & Pq)|(k'' & m & xs & Pq)]; apply Np; [left|right].
        -- exists k'', d''. apply Bk. exact Pq.
        -- exists k'', m, xs. apply Bkh. exact Pq.
    + intros j L1 L2 Np Cs Vr. destruct (Nat.eq_dec j k) as [->|Nj].
      * exfalso. apply Np. left. exists k, d. split; [exact Pk|]. exists te. split; [exact Ote|exact Fkk].
      * apply (A5 j); auto; [lia|]. intros [(k'' & d'' & Pq)|(k'' & m & xs & Pq)]; apply Np; [left|right].
        -- exists k'', d''. apply Bk. exact Pq.
        -- exists k'', m, xs. apply Bkh. exact Pq.
    + intros j bx L1 L2 Np Xl Ci Fxj. destruct (Nat.eq_dec j k) as [->|Nj].
      * exfalso. apply (Np k d). split; [exact Pk|]. exists te. split; [exact Ote|exact Fkk].
      * apply (A6 j bx); auto; [lia|]. intros k'' d'' Pq. apply (Np k'' d''). apply Bk. exact Pq.
    + intros j L1 L2 Np Ic Xj. destruct (Nat.eq_dec j k) as [->|Nj].
      * exfalso. apply Np. left. exists k, d. split; [exact Pk|]. exists te. split; [exact Ote|exact Fkk].
      * apply (A7 j); auto; [lia|]. intros [(k'' & d'' & Pq)|(k'' & m & xs & Pq)]; apply Np; [left|right].
        -- exists k'', d''. apply Bk. exact Pq.
        -- exists k'', m, xs. apply Bkh. exact Pq.
  - (* a CAS's read alone *)
    destruct (Nat.eq_dec c c0) as [<-|N].
    2:{ assert (Cs : cs t c = cs s c) by (rewrite E; unfold sread; simpl; apply upd_neq'; auto).
        assert (Pc : pcs t c = pcs s c) by (rewrite E; reflexivity).
        rewrite Cs, Pc in *. exact H. }
    set (cc := cs s c) in *. set (pc := pcs s c) in *.
    assert (Pc : pcs t c = pc) by (rewrite E; reflexivity).
    assert (Ct : cs t c = ccr s c k xs B m' a u w bv) by (rewrite E; apply ccr_eq).
    assert (Rg : forall j, rg (cs t c) j = if Nat.eqb j k then vd bv a else rg cc j) by (intros j; rewrite Ct; reflexivity).
    assert (Bd : bd (cs t c) = bor (bd cc) B) by (rewrite Ct; reflexivity).
    assert (Fx : fx (cs t c) = fx cc) by (rewrite Ct; reflexivity).
    rewrite Pc in SP, SPh. rewrite Pc, Bd in H. rewrite Bd.
    assert (Rgk : forall k', k' <> k -> rg (cs t c) k' = rg cc k') by (intros k' N'; rewrite Rg; destruct (Nat.eqb_spec k' k); [lia|auto]).
    assert (Pl1 : forall k' d' j, placed p c cc pc r k' d' j <-> placed p c (cs t c) pc r k' d' j).
    { intros k' d' j. rewrite Ct. symmetry. apply (placed_r p s c k xs B m' a u w bv I Lk Ho Hoh r j k' d'). }
    revert H. induction J as [J IH] using lt_wf_ind. intros H.
    pose proof H as Hq. destruct Hq as (A0 & A1 & A2 & A3 & A3h & A4 & A5 & A6 & A7). rewrite Fx in A3h, A6.
    split; [lia|]. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
    + intros j L. rewrite A1 by lia. rewrite Rg. destruct (Nat.eqb_spec j k); [lia|auto].
    + auto.
    + intros j k' d' L Pl Ld. rewrite (A3 j k' d' L (proj1 (Pl1 k' d' j) Pl) Ld). apply Rgk.
      intros ->. destruct Pl as ((_ & Q & _) & _). congruence.
    + intros j k' m0 xs0 L Pl. assert (Nk : k' <> k) by (intros ->; destruct Pl as ((_ & Q & _) & _); congruence).
      assert (Plt : hplaced p c (cs t c) pc r k' m0 xs0 j)
        by (rewrite Ct; apply (hplaced_r p s c k xs B m' a u w bv I Lk Ho Hoh r j k' m0 xs0); right; auto).
      pose proof (A3h j k' m0 xs0 L Plt) as Q. rewrite (Rgk k' Nk) in Q. exact Q.
    + intros j x b L1 L2 Bj Np Fb.
      destruct (pslot_or p t c r j W Wc Rt) as [Ps|Ps]; rewrite Pc in Ps.
      2:{ apply (A4 j x b); auto. }
      destruct Ps as [(k'' & d'' & Pl)|(k'' & m0 & xs0 & Pl)].
      { exfalso. apply Np. left. exists k'', d''. apply Pl1. exact Pl. }
      pose proof Pl as Pl0. rewrite Ct in Pl0. apply (hplaced_r p s c k xs B m' a u w bv I Lk Ho Hoh r j k'' m0 xs0) in Pl0.
      destruct Pl0 as [(-> & -> & -> & Fk0)|(_ & Pl0)].
      2:{ exfalso. apply Np. right. eauto. }
      pose proof (fbinder_shape _ _ _ _ _ _ Fb) as (Exr & Ixr & _ & Br & Cr & Ix).
      pose proof (first_atR_eofR _ _ _ _ _ _ _ _ _ Fk0) as Dj.
      assert (Rj : vv (r j) = a) by (destruct (A3h j k Plain xs L2 Pl) as (Q & _); rewrite Q, Rg, Nat.eqb_refl, vv_vd; reflexivity).
      assert (Hj : ccJ p c cc pc (bor (bd cc) B) r j) by (apply (IH j L2); apply (ccJ_le _ _ _ _ _ _ J j H); lia).
      pose proof (ccJ_agree p s W Wc R c (bor (bd cc) B) r j Hj) as Ag.
      destruct (Hok (Fd p c r)) as (j0 & F0 & Bind).
      set (g := creg p c cc pc (tp s c) (bor (bd cc) B) (Fd p c r)) in *.
      assert (Ej0 : j0 = j).
      { apply (first_atR_unique _ _ _ _ _ _ _ _ _ _ Wc F0). unfold first_atR in *.
        apply (plc_agree p W c cc pc _ r g _ _ j Ag Fk0). }
      subst j0.
      assert (Fbg : fbinder p c g j x = Some b) by (rewrite <- (fbinder_agree p W c r g j x Ag); exact Fb).
      rewrite (eofR_icells _ _ _ _ Dj) in Ix.
      destruct (Bind x b Ix Bj Fbg) as (k' & Lkb & Ub).
      pose proof (fbinder_lt _ _ _ _ _ _ Fb) as Lbj.
      assert (Lk' : lead p c cc pc (tp s c) r b = Some k')
        by (rewrite <- Lkb; apply (lead_agree p c cc pc (tp s c) r g b W (pend_ok_of p s c I)); apply (agree_le r g j b Ag); lia).
      rewrite (dec_lead p s W R c (bor (bd cc) B) r j x b k' Hj Lbj Exr Ixr Lk').
      rewrite (bvx_agree p W c r g b j x _ Lbj Ag).
      pose proof (lead_readR p s c _ (Fd p c r) j (tm s) Plain xs x b k' W I J2 F0 Fbg Lkb) as LR. assert (LR2 : bvx p c g b x (rv (cs s c) k' x) = rdo s (rw (cs s c) k' x) x) by exact LR. rewrite LR2. fold cc. rewrite <- Ub.
      destruct (eff_read _ _ _ _ _ _ _ _ _ He eq_refl) as (_ & Ea).
      transitivity (rdval (mof s c) u x); [|unfold rdo, rdval; reflexivity].
      apply (dec_of p c r j (rdval (mof s c) u) x).
      * intros Z. rewrite (eofR_icells _ _ _ _ Dj) in Z. rewrite Z in Ix. destruct Ix.
      * rewrite (rval_cas _ _ (eofR_cas _ r _ Dj)), Rj, Ea, (eofR_icells _ _ _ _ Dj). reflexivity.
      * rewrite (eofR_icells _ _ _ _ Dj). exact Ix.
    + intros j L1 L2 Np Cs Vr.
      destruct (pslot_or p t c r j W Wc Rt) as [Ps|Ps]; rewrite Pc in Ps.
      2:{ apply (A5 j); auto. }
      destruct Ps as [(k'' & d'' & Pl)|(k'' & m0 & xs0 & Pl)].
      { exfalso. apply Np. left. exists k'', d''. apply Pl1. exact Pl. }
      pose proof Pl as Pl0. rewrite Ct in Pl0. apply (hplaced_r p s c k xs B m' a u w bv I Lk Ho Hoh r j k'' m0 xs0) in Pl0.
      destruct Pl0 as [(-> & -> & -> & Fk0)|(_ & Pl0)].
      2:{ exfalso. apply Np. right. eauto. }
      pose proof (first_atR_eofR _ _ _ _ _ _ _ _ _ Fk0) as Dj.
      assert (Ic : icond (ins p c j r) r = true).
      { destruct (ins p c j r) as [| |m1 x1 c1 e1 n1| |]; simpl in Dj; try discriminate. unfold icond, ieval. simpl.
        destruct (c1 r); [reflexivity|discriminate]. }
      destruct (fx cc j) as [bx|] eqn:Fxj.
      { assert (Xl : is_load (ins p c j r) && icond (ins p c j r) r = true)
          by (rewrite Ic; destruct (ins p c j r); simpl in Cs; try discriminate; reflexivity).
        assert (NP : forall k3 d3, ~ placed p c (cs t c) pc r k3 d3 j)
          by (intros k3 d3 Pl3; apply (placed_hplaced p t Rt c r k3 d3 k Plain xs j); rewrite Pc; [exact Pl3|exact Pl]).
        pose proof (A6 j bx L1 L2 NP Xl Cs Fxj) as V6. rewrite Vr in V6. symmetry in V6. apply andb_prop in V6 as [_ V6]. exact V6. }
      destruct (A3h j k Plain xs L2 Pl) as (Q1 & _ & Q3). destruct (Q3 Fxj Vr) as (_ & CF).
      rewrite Rg, Nat.eqb_refl in CF, Q1. rewrite vv_vd in Q1. rewrite Q1.
      assert (Bt : bv = true).
      { destruct bv; [reflexivity|exfalso]. revert CF Ic. unfold cfailv, icond, ieval.
        destruct (ins p c j r) as [| |m1 x1 c1 e1 n1| |]; simpl in Cs; try discriminate. simpl.
        rewrite vok_vd. intros CF Ic'. rewrite Ic' in CF. discriminate CF. }
      rewrite Bt in CF.
      pose proof (cfailv_vd_true _ r a Cs Ic) as Eq. rewrite CF in Eq. simpl in Eq. rewrite <- Eq. reflexivity.
    + intros j bx L1 L2 Np Xl Ci Fxj. apply (A6 j bx); auto. intros k'' d'' Pl. apply (Np k'' d''). apply Pl1. exact Pl.
    + (* DQ C7: the read half of a CAS of no cell read enc [] *)
      intros j L1 L2 Np Ic Xj.
      destruct (pslot_or p t c r j W Wc Rt) as [Ps|Ps]; rewrite Pc in Ps.
      2:{ apply (A7 j); auto. }
      destruct Ps as [(k'' & d'' & Pl)|(k'' & m0 & xs0 & Pl)].
      { exfalso. apply Np. left. exists k'', d''. apply Pl1. exact Pl. }
      pose proof Pl as Pl0. rewrite Ct in Pl0. apply (hplaced_r p s c k xs B m' a u w bv I Lk Ho Hoh r j k'' m0 xs0) in Pl0.
      destruct Pl0 as [(-> & -> & -> & Fk0)|(_ & Pl0)].
      2:{ exfalso. apply Np. right. eauto. }
      pose proof (first_atR_eofR _ _ _ _ _ _ _ _ _ Fk0) as Dj.
      assert (Rj : vv (r j) = a) by (destruct (A3h j k Plain xs L2 Pl) as (Q & _); rewrite Q, Rg, Nat.eqb_refl, vv_vd; reflexivity).
      destruct (eff_read _ _ _ _ _ _ _ _ _ He eq_refl) as (_ & Ea).
      rewrite (eofR_icells _ _ _ _ Dj) in Ic.
      rewrite (rval_cas _ _ (eofR_cas _ r _ Dj)), Rj, Ea. cbn [icells]. rewrite Ic. reflexivity.
  - (* passing a non-executing instruction *)
    destruct (Nat.eq_dec c c0) as [<-|N].
    2:{ assert (Cs : cs t c = cs s c) by (rewrite E; unfold sskip; simpl; apply upd_neq'; auto).
        assert (Pc : pcs t c = pcs s c) by (rewrite E; unfold sskip; simpl; apply upd_neq'; auto).
        rewrite Cs, Pc in *. exact H. }
    set (cc := cs s c) in *. set (k := pcs s c) in *.
    assert (Pc : pcs t c = S k) by (rewrite E; unfold sskip; simpl; apply upd_eq').
    assert (Oc : oc (cs t c) = oc cc) by (rewrite E; unfold sskip; simpl; rewrite upd_eq'; reflexivity).
    assert (Oh : oh (cs t c) = oh cc) by (rewrite E; unfold sskip; simpl; rewrite upd_eq'; reflexivity).
    assert (Rg : rg (cs t c) = rg cc) by (rewrite E; unfold sskip; simpl; rewrite upd_eq'; reflexivity).
    assert (Ai : forall j, ai (cs t c) j = if Nat.eqb j k then ins p c k (rg cc) else ai cc j)
      by (intros j; rewrite E; unfold sskip; simpl; rewrite upd_eq'; reflexivity).
    assert (Bd : bd (cs t c) = bd cc) by (rewrite E; unfold sskip; simpl; rewrite upd_eq'; reflexivity).
    assert (Fx : fx (cs t c) = fx cc) by (rewrite E; unfold sskip; simpl; rewrite upd_eq'; reflexivity).
    rewrite Pc in SP, SPh. rewrite Pc, Bd in H. rewrite Bd. destruct H as (A0 & A1 & A2 & A3 & A3h & A4 & A5 & A6 & A7).
    rewrite Fx in A3h, A6.
    assert (AgT : agree r (rg (cs t c)) (S k)) by (intros j Lj; apply A1; auto).
    rewrite Rg in A1, A3, A3h.
    assert (Ag : agree r (rg cc) k) by (intros j Lj; apply A1; lia).
    destruct (oh cc k) as [t1|] eqn:Ohk.
    { (* a CAS that failed after its read: its read is placed at k; the
         places beyond k stay *)
      destruct (i_half p s I c k t1 Ko Ohk (le_n _)) as (_ & (xs1 & Ax) & _). fold cc in Ax.
      assert (Er : eofR (ins p c k (rg cc)) (rg cc) = Some (Plain, xs1)) by (rewrite (Kh ltac:(congruence)), Ax; reflexivity).
      assert (Cf : cfail (ins p c k (rg cc)) (rg cc) k = true).
      { destruct (xex_false _ _ _ _ Kx) as [X0|(_ & X0)]; [|exact X0]. exfalso.
        destruct (eofR_exec_tied p c k (rg cc) Plain xs1 Wc Er) as [E0 _]. congruence. }
      assert (AgS : agree r (rg cc) (S k)) by (intros j Lj; rewrite <- Rg; apply AgT; lia).
      assert (Cs' : cs t c = cs (sskip p s c) c) by (rewrite E; reflexivity).
      assert (Pt : forall k' d', k' <> k -> pending cc k k' d' -> pending (cs t c) (S k) k' d').
      { intros k' d' Nk (P1 & P2 & P3). split; [lia|]. rewrite Oc, Ai. destruct (Nat.eqb_spec k' k); [lia|]. auto. }
      assert (Pth : forall k' m xs, k' <> k -> hpending cc k k' m xs -> hpending (cs t c) (S k) k' m xs).
      { intros k' m xs Nk (P1 & P2 & P3). split; [lia|]. rewrite Oh, Ai. destruct (Nat.eqb_spec k' k); [lia|]. auto. }
      split; [lia|]. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
      + intros j L. apply A1. lia.
      + intros j L1 L2 Xl. destruct (Nat.eq_dec j k) as [->|Nj]; [|apply A2; auto; lia].
        exfalso. assert (ER' : eofR (ins p c k r) r = Some (Plain, xs1)) by (rewrite (eofR_agree p W c k r (rg cc) Ag); exact Er).
        rewrite (eofR_ld _ _ _ ER') in Xl. discriminate.
      + intros j k' d' L Pl Ld. destruct Pl as (Pq & tq & O & F).
        destruct (Nat.eq_dec j k) as [->|Nj].
        * exfalso. apply (skf_noplace p s c t1 xs1 W Wc Ko Ohk Ax Er Kf r k' d' tq Ag Pq O F).
        * assert (Lkj : k < j) by (pose proof (first_at_le _ _ _ _ _ _ _ _ F); lia).
          assert (Nk : k' <> k) by (intros ->; destruct Pq as (_ & P2 & _); congruence).
          apply (A3 j k' d' L); [|exact Ld]. split; [apply Pt; auto|]. exists tq. split; [rewrite Oc; exact O|].
          rewrite Cs'. apply (skf_shift p s c t1 xs1 W Wc Ko Ohk Ax Er Cf (Kv ltac:(congruence)) Kf r AgS tq k' d' j); [| |lia|exact F].
          -- rewrite <- Cs'. apply Pt; auto.
          -- rewrite <- Cs', Oc. exact O.
      + intros j k' m xs L Pl. destruct Pl as (Pq & C & tq & O & F). destruct (Nat.eq_dec k' k) as [->|Nk].
        * rewrite Ohk in O. injection O as <-. pose proof Pq as (_ & _ & Cx). rewrite Ax in Cx. injection Cx as <- <-.
          assert (j = k) by (apply (first_atR_unique p c cc k r t1 Plain xs1 j k Wc F); apply (skf_place p s c t1 xs1 W Wc Ko Ohk Er Kf r Ag)).
          subst j. assert (Rk : r k = rg cc k) by (apply A1; lia). rewrite Rk. split; [reflexivity|].
          split; [intros _ _; reflexivity|]. intros _ Vr. rewrite (Kv ltac:(congruence)) in Vr. discriminate.
        * destruct (Nat.eq_dec j k) as [->|Nj]; [exfalso; apply (skf_noplaceh p s c t1 xs1 W Wc Ko Ohk Ax Er Kf r k' m xs tq Ag Pq Nk O F)|].
          assert (Lkj : k < j) by (pose proof (first_atR_le _ _ _ _ _ _ _ _ _ F); lia).
          apply (A3h j k' m xs L). split; [apply Pth; auto|]. split; [rewrite Oc; exact C|]. exists tq. split; [rewrite Oh; exact O|].
          rewrite Cs'. apply (skf_shiftR p s c t1 xs1 W Wc Ko Ohk Ax Er Cf (Kv ltac:(congruence)) Kf r AgS tq k' m xs j); [| |lia|exact F].
          -- rewrite <- Cs'. apply Pth; auto.
          -- rewrite <- Cs', Oh. exact O.
      + intros j x b L1 L2 Bj Np Fb. destruct (Nat.eq_dec j k) as [->|Nj].
        * exfalso. apply Np. right. exists k, Plain, xs1. split; [split; [lia|split; [congruence|rewrite Ax; reflexivity]]|].
          split; [exact Ko|]. exists t1. split; [exact Ohk|]. apply (skf_place p s c t1 xs1 W Wc Ko Ohk Er Kf r Ag).
        * apply (A4 j x b); auto; [lia|]. intros [(k'' & d'' & Pq)|(k'' & m & xs & Pq)]; apply Np; [left|right].
          -- exists k'', d''. destruct Pq as (Pq & tq & O & F). pose proof Pq as (Q1 & Q2 & Q3). rewrite Oc in Q2. rewrite Ai in Q3.
             rewrite Oc in O. destruct (Nat.eqb_spec k'' k) as [Ek|Nk]; [lia|].
             assert (Pq' : pending cc k k'' d'') by (split; [lia|split; auto]).
             split; [exact Pq'|]. exists tq. split; [exact O|].
             rewrite Cs' in F. apply (skf_shift p s c t1 xs1 W Wc Ko Ohk Ax Er Cf (Kv ltac:(congruence)) Kf r AgS tq k'' d'' j); [| |lia|exact F].
             ++ rewrite <- Cs'. exact Pq.
             ++ rewrite <- Cs', Oc. exact O.
          -- exists k'', m, xs. destruct Pq as (Pq & C & tq & O & F). pose proof Pq as (Q1 & Q2 & Q3). rewrite Oh in Q2. rewrite Ai in Q3.
             rewrite Oc in C. rewrite Oh in O. destruct (Nat.eqb_spec k'' k) as [Ek|Nk]; [lia|].
             assert (Pq' : hpending cc k k'' m xs) by (split; [lia|split; auto]).
             split; [exact Pq'|]. split; [exact C|]. exists tq. split; [exact O|].
             rewrite Cs' in F. apply (skf_shiftR p s c t1 xs1 W Wc Ko Ohk Ax Er Cf (Kv ltac:(congruence)) Kf r AgS tq k'' m xs j); [| |lia|exact F].
             ++ rewrite <- Cs'. exact Pq.
             ++ rewrite <- Cs', Oh. exact O.
      + intros j L1 L2 Np Cs Vr. destruct (Nat.eq_dec j k) as [->|Nj].
        * exfalso. apply Np. right. exists k, Plain, xs1. split; [split; [lia|split; [congruence|rewrite Ax; reflexivity]]|].
          split; [exact Ko|]. exists t1. split; [exact Ohk|]. apply (skf_place p s c t1 xs1 W Wc Ko Ohk Er Kf r Ag).
        * apply (A5 j); auto; [lia|]. intros [(k'' & d'' & Pq)|(k'' & m & xs & Pq)]; apply Np; [left|right].
          -- exists k'', d''. destruct Pq as (Pq & tq & O & F). pose proof Pq as (Q1 & Q2 & Q3). rewrite Oc in Q2. rewrite Ai in Q3.
             rewrite Oc in O. destruct (Nat.eqb_spec k'' k) as [Ek|Nk]; [lia|].
             assert (Pq' : pending cc k k'' d'') by (split; [lia|split; auto]).
             split; [exact Pq'|]. exists tq. split; [exact O|].
             rewrite Cs' in F. apply (skf_shift p s c t1 xs1 W Wc Ko Ohk Ax Er Cf (Kv ltac:(congruence)) Kf r AgS tq k'' d'' j); [| |lia|exact F].
             ++ rewrite <- Cs'. exact Pq.
             ++ rewrite <- Cs', Oc. exact O.
          -- exists k'', m, xs. destruct Pq as (Pq & C & tq & O & F). pose proof Pq as (Q1 & Q2 & Q3). rewrite Oh in Q2. rewrite Ai in Q3.
             rewrite Oc in C. rewrite Oh in O. destruct (Nat.eqb_spec k'' k) as [Ek|Nk]; [lia|].
             assert (Pq' : hpending cc k k'' m xs) by (split; [lia|split; auto]).
             split; [exact Pq'|]. split; [exact C|]. exists tq. split; [exact O|].
             rewrite Cs' in F. apply (skf_shiftR p s c t1 xs1 W Wc Ko Ohk Ax Er Cf (Kv ltac:(congruence)) Kf r AgS tq k'' m xs j); [| |lia|exact F].
             ++ rewrite <- Cs'. exact Pq.
             ++ rewrite <- Cs', Oh. exact O.
      + intros j bx L1 L2 Np Xl Ci Fxj. destruct (Nat.eq_dec j k) as [->|Nj].
        * (* the CAS passed: its result is the result fixed there *)
          assert (Rk : r k = rg cc k) by (apply A1; lia). rewrite Rk.
          destruct (ins_agree p W c k r (rg cc) Ag) as (E1 & E2). rewrite E1 in Ci, Xl, E2 |- *.
          rewrite (cexp_ieval _ _ _ E2). apply (HfS bx Fxj Ci).
          assert (Er' : eofR (ins p c k (rg cc)) (rg cc) = eofR (crd Plain xs1) (rg cc)) by (rewrite Er; reflexivity).
          destruct (eofR_half _ _ _ Er') as (_ & Xi). apply andb_prop in Xi as [_ Xi]. exact Xi.
        * apply (A6 j bx); auto; [lia|]. intros k'' d'' Pq. apply (Np k'' d'').
          destruct Pq as (Pq & tq & O & F). pose proof Pq as (Q1 & Q2 & Q3). rewrite Oc in Q2. rewrite Ai in Q3.
          rewrite Oc in O. destruct (Nat.eqb_spec k'' k) as [Ek|Nk]; [lia|].
          assert (Pq' : pending cc k k'' d'') by (split; [lia|split; auto]).
          split; [exact Pq'|]. exists tq. split; [exact O|].
          rewrite Cs' in F. apply (skf_shift p s c t1 xs1 W Wc Ko Ohk Ax Er Cf (Kv ltac:(congruence)) Kf r AgS tq k'' d'' j); [| |lia|exact F].
          -- rewrite <- Cs'. exact Pq.
          -- rewrite <- Cs', Oc. exact O.
      + intros j L1 L2 Np Ic Xj. destruct (Nat.eq_dec j k) as [->|Nj].
        * exfalso. apply Np. right. exists k, Plain, xs1. split; [split; [lia|split; [congruence|rewrite Ax; reflexivity]]|].
          split; [exact Ko|]. exists t1. split; [exact Ohk|]. apply (skf_place p s c t1 xs1 W Wc Ko Ohk Er Kf r Ag).
        * apply (A7 j); auto; [lia|]. intros [(k'' & d'' & Pq)|(k'' & m & xs & Pq)]; apply Np; [left|right].
          -- exists k'', d''. destruct Pq as (Pq & tq & O & F). pose proof Pq as (Q1 & Q2 & Q3). rewrite Oc in Q2. rewrite Ai in Q3.
             rewrite Oc in O. destruct (Nat.eqb_spec k'' k) as [Ek|Nk]; [lia|].
             assert (Pq' : pending cc k k'' d'') by (split; [lia|split; auto]).
             split; [exact Pq'|]. exists tq. split; [exact O|].
             rewrite Cs' in F. apply (skf_shift p s c t1 xs1 W Wc Ko Ohk Ax Er Cf (Kv ltac:(congruence)) Kf r AgS tq k'' d'' j); [| |lia|exact F].
             ++ rewrite <- Cs'. exact Pq.
             ++ rewrite <- Cs', Oc. exact O.
          -- exists k'', m, xs. destruct Pq as (Pq & C & tq & O & F). pose proof Pq as (Q1 & Q2 & Q3). rewrite Oh in Q2. rewrite Ai in Q3.
             rewrite Oc in C. rewrite Oh in O. destruct (Nat.eqb_spec k'' k) as [Ek|Nk]; [lia|].
             assert (Pq' : hpending cc k k'' m xs) by (split; [lia|split; auto]).
             split; [exact Pq'|]. split; [exact C|]. exists tq. split; [exact O|].
             rewrite Cs' in F. apply (skf_shiftR p s c t1 xs1 W Wc Ko Ohk Ax Er Cf (Kv ltac:(congruence)) Kf r AgS tq k'' m xs j); [| |lia|exact F].
             ++ rewrite <- Cs'. exact Pq.
             ++ rewrite <- Cs', Oh. exact O. }
    assert (Kx' : executes (ins p c k (rg cc)) (rg cc) = false).
    { destruct (xex_false _ _ _ _ Kx) as [X0|(Z & _)]; [exact X0|congruence]. }
    (* the slot k does not execute: it has no place, and binds no read *)
    assert (Xk : executes (ins p c k r) r = false) by (rewrite (exec_agree p W c k r (rg cc) Ag); exact Kx').
    assert (Dk : forall d', eof (ins p c k r) r <> Some d').
    { intros d' D'. destruct (eof_exec_tied p c k r d' Wc D') as [E0 _]. congruence. }
    assert (DkR : forall m xs, eofR (ins p c k r) r <> Some (m, xs)).
    { intros m xs D'. destruct (eofR_exec_tied p c k r m xs Wc D') as [E0 _]. congruence. }
    assert (Pt : forall k' d', k' <> k -> pending cc k k' d' -> pending (cs t c) (S k) k' d').
    { intros k' d' Nk (P1 & P2 & P3). split; [lia|]. rewrite Oc, Ai. destruct (Nat.eqb_spec k' k); [lia|]. auto. }
    assert (Pth : forall k' m xs, k' <> k -> hpending cc k k' m xs -> hpending (cs t c) (S k) k' m xs).
    { intros k' m xs Nk (P1 & P2 & P3). split; [lia|]. rewrite Oh, Ai. destruct (Nat.eqb_spec k' k); [lia|]. auto. }
    assert (Mv : forall k' d' j, k' <> k -> placed p c cc k r k' d' j -> k < j /\ placed p c (cs t c) (S k) r k' d' j).
    { intros k' d' j Nk (Pq & tq & O & F). assert (Lkj : k < j).
      { destruct (Nat.eq_dec j k) as [->|Nj]; [|pose proof (first_at_le _ _ _ _ _ _ _ _ F); lia].
        exfalso. exact (Dk d' (first_at_eof _ _ _ _ _ _ _ _ F)). }
      split; [exact Lkj|]. split; [apply Pt; auto|]. exists tq. split; [rewrite Oc; exact O|].
      apply (SP k' d' tq j (Pt k' d' Nk Pq) O AgT ltac:(lia)). exact F. }
    assert (Bk : forall k' d' j, placed p c (cs t c) (S k) r k' d' j -> placed p c cc k r k' d' j).
    { intros k' d' j (Pq & tq & O & F). destruct Pq as (Q1 & Q2 & Q3). rewrite Oc, Ai in *.
      destruct (Nat.eqb_spec k' k) as [Ek|Nk]; [lia|].
      assert (Pq : pending cc k k' d') by (split; [lia|split; auto]).
      split; [exact Pq|]. exists tq. split; [exact O|]. apply (SP k' d' tq j (Pt k' d' Nk Pq) O AgT); [|exact F].
      pose proof (first_at_le _ _ _ _ _ _ _ _ F). lia. }
    assert (Mvh : forall k' m xs j, hplaced p c cc k r k' m xs j -> k < j /\ hplaced p c (cs t c) (S k) r k' m xs j).
    { intros k' m xs j (Pq & C & tq & O & F). assert (Nk : k' <> k) by (intros ->; congruence).
      assert (Lkj : k < j).
      { destruct (Nat.eq_dec j k) as [->|Nj]; [|pose proof (first_atR_le _ _ _ _ _ _ _ _ _ F); lia].
        exfalso. exact (DkR m xs (first_atR_eofR _ _ _ _ _ _ _ _ _ F)). }
      split; [exact Lkj|]. split; [apply Pth; auto|]. split; [rewrite Oc; exact C|]. exists tq. split; [rewrite Oh; exact O|].
      apply (SPh k' m xs tq j (Pth k' m xs Nk Pq) ltac:(rewrite Oc; exact C) O AgT ltac:(lia)). exact F. }
    assert (Bkh : forall k' m xs j, hplaced p c (cs t c) (S k) r k' m xs j -> hplaced p c cc k r k' m xs j).
    { intros k' m xs j (Pq & C & tq & O & F). pose proof Pq as (Q1 & Q2 & Q3). rewrite Oh, Ai in *.
      destruct (Nat.eqb_spec k' k) as [Ek|Nk]; [lia|].
      assert (Pq' : hpending cc k k' m xs) by (split; [lia|split; auto]).
      split; [exact Pq'|]. split; [rewrite Oc in C; exact C|]. exists tq. split; [first [exact O|rewrite Oh in O; exact O]|].
      apply (SPh k' m xs tq j Pq C O AgT); [|exact F]. pose proof (first_atR_le _ _ _ _ _ _ _ _ _ F). lia. }
    split; [lia|]. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
    + intros j L. apply A1. lia.
    + intros j L1 L2 Xl. destruct (Nat.eq_dec j k) as [->|Nj]; [|apply A2; auto; lia].
      rewrite A1 by lia. apply (i_rg0 p s I c k Ko Ohk).
    + intros j k' d' L Pl Ld. destruct (Nat.eq_dec k' k) as [->|Nk].
      * exfalso. destruct Pl as ((_ & P2 & _) & _). congruence.
      * destruct (Mv k' d' j Nk Pl) as (Lkj & Pl'). rewrite (A3 j k' d' L Pl' Ld). reflexivity.
    + intros j k' m xs L Pl. destruct (Mvh k' m xs j Pl) as (Lkj & Pl'). apply (A3h j k' m xs L Pl').
    + intros j x b L1 L2 Bj Np Fb. destruct (Nat.eq_dec j k) as [->|Nj].
      * exfalso. pose proof (fbinder_shape _ _ _ _ _ _ Fb) as (_ & _ & _ & _ & Ck & _).
        unfold executes in Xk. destruct (isacc (ins p c k r)) eqn:Ia; [congruence|].
        destruct (ins p c k r); simpl in Ia, Ck; discriminate.
      * apply (A4 j x b); auto; [lia|]. intros [(k'' & d'' & Pq)|(k'' & m & xs & Pq)]; apply Np; [left|right].
        -- exists k'', d''. apply Bk. exact Pq.
        -- exists k'', m, xs. apply Bkh. exact Pq.
    + intros j L1 L2 Np Cs Vr. destruct (Nat.eq_dec j k) as [->|Nj].
      * exfalso. assert (Z : r k = 0) by (rewrite A1 by lia; apply (i_rg0 p s I c k Ko Ohk)). rewrite Z in Vr. discriminate.
      * apply (A5 j); auto; [lia|]. intros [(k'' & d'' & Pq)|(k'' & m & xs & Pq)]; apply Np; [left|right].
        -- exists k'', d''. apply Bk. exact Pq.
        -- exists k'', m, xs. apply Bkh. exact Pq.
    + intros j bx L1 L2 Np Xl Ci Fxj. destruct (Nat.eq_dec j k) as [->|Nj].
      * exfalso. apply andb_prop in Xl as [X1 X2]. unfold executes in Xk.
        destruct (ins p c k r); simpl in X1, Xk; try discriminate; congruence.
      * apply (A6 j bx); auto; [lia|]. intros k'' d'' Pq. apply (Np k'' d''). apply Bk. exact Pq.
    + intros j L1 L2 Np Ic Xl. destruct (Nat.eq_dec j k) as [->|Nj].
      * exfalso. apply andb_prop in Xl as [X1 X2]. unfold executes in Xk.
        destruct (ins p c k r); simpl in X1, Xk; try discriminate; congruence.
      * apply (A7 j); auto; [lia|]. intros [(k'' & d'' & Pq)|(k'' & m & xs & Pq)]; apply Np; [left|right].
        -- exists k'', d''. apply Bk. exact Pq.
        -- exists k'', m, xs. apply Bkh. exact Pq.
  - (* S3c: a result fixed. First from t to the state s1 between the register side and the fix (the
       places and reads do not change, the fixed result is the register's), then, for a failure after the
       read half, from s1 to s (only the record's register changes) *)
    destruct (Nat.eq_dec c cX) as [<-|N].
    2:{ assert (Cs : cs t c = cs s c).
        { rewrite E; unfold scfix0; simpl; rewrite upd_neq by auto.
          destruct oX as [kX|]; [destruct bX|]; cbn [sflp]; try reflexivity. unfold scfail; simpl; apply upd_neq; auto. }
        assert (Pc : pcs t c = pcs s c) by (rewrite E; unfold scfix0; cbn [pcs]; rewrite pcs_flp; reflexivity).
        rewrite Cs, Pc in *. exact H. }
    set (s1 := sflp s c oX bX) in *.
    destruct (cfix_pre p s c jX bX BX oX R HcX) as (I1 & Hc1).
    assert (Hf1 : fx (cs s1 c) jX = None) by (unfold s1; rewrite fx_flp; exact HfX).
    assert (Hj1 : pcs s1 c <= jX) by (unfold s1; rewrite pcs_flp; exact HjX).
    assert (H1 : ccJ p c (cs s1 c) (pcs s1 c) (bd (cs t c)) r J).
    { clear HcX.
        assert (Ct : cs t c = cc_fx (cs s1 c) (bor (bd (cs s1 c)) BX) (upd (fx (cs s1 c)) jX (Some bX))) by (rewrite E; apply cx_cs).
        assert (Pc : pcs t c = pcs s1 c) by (rewrite E; reflexivity).
        assert (Rt' := Rt). rewrite E in Rt'.
        assert (AG : agree r (creg p c (cs t c) (pcs t c) (tp t c) (bd (cs t c)) (Fd p c r)) J)
          by (apply (ccJ_agree p t W Wc Rt c (bd (cs t c)) r J H)).
        set (cc := cs s1 c) in *.
        rewrite Ct, Pc in H. rewrite Ct.
        destruct H as (A0 & A1 & A2 & A3 & A3h & A4 & A5 & A6 & A7). cbn [fx cc_fx rg] in A1, A3, A3h, A6.
        (* the registers R1 sees before the step, under which the result was fixed *)
        assert (Vk : forall k m xs, jX < J -> hplaced p c cc (pcs s1 c) r k m xs jX -> vok (rg cc k) = true \/ bX = false).
        { intros k m xs LJ Pl.
          destruct (cx_regs p s1 c jX bX BX W I1 Hf1 Hc1 (fun _ => false) (Fd p c r)) as (F & EQ).
          set (g := creg p c cc (pcs s1 c) (tp s1 c) (bor (bd cc) BX) F).
          assert (AGg : agree r g J).
          { intros q Lq. rewrite (AG q Lq). clear AG. rewrite E, cx_cs.
            change (pcs (scfix0 s1 c jX bX BX) c) with (pcs s1 c). change (tp (scfix0 s1 c jX bX BX) c) with (tp s1 c).
            transitivity (creg p c (cc_fx cc (bor (bd cc) BX) (upd (fx cc) jX (Some bX))) (pcs s1 c) (tp s1 c)
                            (bor (bd (cc_fx cc (bor (bd cc) BX) (upd (fx cc) jX (Some bX)))) (fun _ => false)) (Fd p c r) q).
            - apply (creg_Bext p c (cc_fx cc (bor (bd cc) BX) (upd (fx cc) jX (Some bX))) _ _ _ _ _ W (pend_ok_of p s1 c I1)).
              intros q0. unfold bor. cbn [bd cc_fx]. unfold bor.
              unfold cc in *. destruct (bd (cs s1 c) q0), (BX q0); reflexivity.
            - rewrite <- EQ. unfold g. apply (creg_Bext p c _ _ _ _ _ _ W (pend_ok_of p s1 c I1)).
              intros q0. unfold bor. unfold cc in *. destruct (bd (cs s1 c) q0), (BX q0); reflexivity. }
          apply (Hc1 F k).
          apply (hpend_at_char_s p s1 c I1). exists m, xs.
          destruct Pl as (P1 & P2 & t0 & O & F0). split; auto. split; auto. exists t0. split; auto.
          unfold first_atR in *. apply (plc_agree p W c cc (pcs s1 c) _ r g _ _ jX); [intros q Lq; apply AGg; lia|exact F0]. }
        split; [exact A0|]. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
        + exact A1.
        + exact A2.
        + intros j k' d' L Pl Ld. apply (A3 j k' d' L); [exact (proj2 (placed_fx _ _ _ _ _ _ _ _ _ _) Pl)|exact Ld].
        + intros j k' m xs L Pl. destruct (A3h j k' m xs L (proj2 (hplaced_fx _ _ _ _ _ _ _ _ _ _ _) Pl)) as (Q1 & Q2 & Q3).
          unfold upd in Q2, Q3. destruct (Nat.eqb_spec j jX) as [->|Nj].
          * pose proof (Vk k' m xs L Pl) as V.
            assert (NP : forall k3 d3, ~ placed p c (cc_fx cc (bor (bd cc) BX) (upd (fx cc) jX (Some bX))) (pcs s1 c) r k3 d3 jX).
            { intros k3 d3 Pl3. apply (placed_hplaced p (scfix0 s1 c jX bX BX) Rt' c r k3 d3 k' m xs jX).
              - rewrite <- E, Ct, Pc. exact Pl3.
              - rewrite <- E, Ct, Pc. exact (proj2 (hplaced_fx _ _ _ _ _ _ _ _ _ _ _) Pl). }
            pose proof Pl as (_ & _ & t0 & _ & F0). pose proof (first_atR_eofR _ _ _ _ _ _ _ _ _ F0) as Dj.
            assert (Xl : is_load (ins p c jX r) && icond (ins p c jX r) r = true)
              by (destruct (ins p c jX r) as [| |m1 x1 c1 e1 n1| |]; simpl in Dj; try discriminate; unfold icond, ieval; simpl; destruct (c1 r); [reflexivity|discriminate]).
            assert (Ci : is_cas (ins p c jX r) = true) by (apply (eofR_cas _ r _ Dj)).
            pose proof (A6 jX bX ltac:(lia) L NP Xl Ci ltac:(unfold upd; rewrite Nat.eqb_refl; reflexivity)) as V6.
            split; [exact Q1|]. split.
            { intros _ Z. destruct V as [V|Bf]; [congruence|]. rewrite Bf in V6. simpl in V6.
              rewrite <- (vd_split (r jX)), V6, Q1, <- Z. apply vd_split. }
            intros _ Vr. rewrite Vr in V6. symmetry in V6. apply andb_prop in V6 as [Bt V6].
            assert (V' : vok (rg cc k') = true) by (destruct V as [V|Bf]; [exact V|congruence]).
            split; [exact V'|]. rewrite Q1 in V6.
            apply andb_prop in Xl as [_ Ic].
            destruct (ins p c jX r) as [| |m1 x1 c1 e1 n1| |]; simpl in Ci; try discriminate.
            unfold cfailv. unfold icond, ieval in Ic. simpl in Ic, V6 |- *. rewrite Ic, V', V6. reflexivity.
          * split; [exact Q1|]. split; [exact Q2|exact Q3].
        + intros j x b L1 L2 Bj Np Fb. apply (A4 j x b); auto.
          intros Xp. apply Np. exact (proj1 (pslot_fx _ _ _ _ _ _ _ _) Xp).
        + intros j L1 L2 Np Cs Vr. apply (A5 j); auto. intros Xp. apply Np. exact (proj1 (pslot_fx _ _ _ _ _ _ _ _) Xp).
        + intros j bx L1 L2 Np Xl Ci Fxj. destruct (Nat.eq_dec j jX) as [->|Nj]; [congruence|].
          apply (A6 j bx); auto; [|unfold upd; rewrite (proj2 (Nat.eqb_neq _ _) Nj); exact Fxj].
          intros k'' d'' Pl. apply (Np k'' d''). exact (proj1 (placed_fx _ _ _ _ _ _ _ _ _ _) Pl).
        + intros j L1 L2 Np Ic Xj. apply (A7 j); auto. intros Xp. apply Np. exact (proj1 (pslot_fx _ _ _ _ _ _ _ _) Xp). }
    clear H. rename H1 into H. unfold s1 in H.
    destruct oX as [kF|]; [destruct bX|]; cbn [sflp] in H; try exact H.
    destruct (cfix_rec _ _ _ _ _ _ _ _ _ HcX) as (HpF & HoF & HhF & HvF).
      assert (Ct : cs (scfail s c kF) c = cc_rg (cs s c) (upd (rg (cs s c)) kF (vd false (vv (rg (cs s c) kF))))) by (apply cf_cs).
      assert (Pc : pcs (scfail s c kF) c = pcs s c) by reflexivity.
      rewrite Ct, Pc in H.
      set (cc := cs s c) in *. set (g := upd (rg cc) kF (vd false (vv (rg cc kF)))) in *.
      destruct H as (A0 & A1 & A2 & A3 & A3h & A4 & A5 & A6 & A7). cbn [fx cc_rg] in A3h, A6.
      split; [exact A0|]. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
      + intros j L. rewrite (A1 j L). cbn [rg cc_rg]. unfold g, upd. destruct (Nat.eqb_spec j kF); [lia|reflexivity].
      + exact A2.
      + intros j k' d' L Pl Ld. rewrite (A3 j k' d' L (proj2 (placed_rg _ _ _ _ _ _ _ _ _) Pl) Ld). cbn [rg cc_rg]. unfold g, upd.
        destruct (Nat.eqb_spec k' kF) as [->|]; [|reflexivity]. destruct Pl as ((_ & Q & _) & _). congruence.
      + intros j k' m xs L Pl. destruct (A3h j k' m xs L (proj2 (hplaced_rg _ _ _ _ _ _ _ _ _ _) Pl)) as (Q1 & Q2 & Q3).
        cbn [rg cc_rg] in Q1, Q2, Q3. unfold g, upd in Q1, Q2, Q3. destruct (Nat.eqb_spec k' kF) as [->|Nk].
        * rewrite vok_vd in Q2. rewrite vv_vd in Q1. split; [exact Q1|]. split; [intros _ Z; congruence|].
          intros Fn Vr. rewrite (Q2 Fn eq_refl), vok_vd in Vr. discriminate.
        * split; [exact Q1|]. split; [exact Q2|exact Q3].
      + intros j x b L1 L2 Bj Np Fb. apply (A4 j x b); auto. intros Xp. apply Np. exact (proj1 (pslot_rg _ _ _ _ _ _ _) Xp).
      + intros j L1 L2 Np Cs Vr. apply (A5 j); auto. intros Xp. apply Np. exact (proj1 (pslot_rg _ _ _ _ _ _ _) Xp).
      + intros j bx L1 L2 Np Xl Ci Fxj. apply (A6 j bx); auto. intros k'' d'' Pl. apply (Np k'' d''). exact (proj1 (placed_rg _ _ _ _ _ _ _ _ _) Pl).
      + intros j L1 L2 Np Ic Xj. apply (A7 j); auto. intros Xp. apply Np. exact (proj1 (pslot_rg _ _ _ _ _ _ _) Xp).
Qed.

End Mono.

Section MT.
Variable p : prog.
Variable f : nat -> st.
Variable n : nat.
Hypothesis T : trace p f n.
Hypothesis W : wf p.
Hypothesis Wc : cellful p.

Lemma mono_tr : forall c r J i i', i <= i' -> i' <= n ->
  ccJ p c (cs (f i') c) (pcs (f i') c) (bd (cs (f i') c)) r J ->
  ccJ p c (cs (f i) c) (pcs (f i) c) (bd (cs (f i) c)) r J.
Proof.
  intros c r J i i' L L' H. induction i' as [|i' IH].
  - assert (i = 0) by lia. subst. exact H.
  - destruct (Nat.eq_dec i (S i')) as [->|N]; [exact H|].
    apply IH; [lia|lia|].
    assert (Rm : run p (f i')) by (apply (tr_run p f n T); lia).
    pose proof (mono_step p (f i') (f (S i')) W Rm (tr_step p f n T i' ltac:(lia)) Wc c r J H) as M.
    apply (ccJ_B _ _ _ _ _ (bd (cs (f (S i')) c))); [|exact M].
    intros j Bj. apply (x_bd _ _ (Ext_step p _ _ Rm (tr_step p f n T i' ltac:(lia)))). exact Bj.
Qed.

(* the data of an early access: the step that made it, an early access or
   the early write of a CAS whose read happened alone *)
Definition early_at (c k i : nat) (d : desc) (B : nat -> bool) (u : cell -> option nat) : Prop :=
  i < n /\ pcs (f i) c < k /\ oc (cs (f i) c) k = None /\
  (forall k' d', pending (cs (f i) c) (pcs (f i) c) k' d' -> tied (inst_of d) (inst_of d') -> k' < k) /\
  ((oh (cs (f i) c) k = None /\ early_ok p c (cs (f i) c) (pcs (f i) c) (tp (f i) c) (tm (f i)) d u B) \/
   (exists t1 xs ev nv, oh (cs (f i) c) k = Some t1 /\ d = DCas Plain xs ev nv /\ u = rw (cs (f i) c) k /\
      ai (cs (f i) c) k = crd Plain xs /\
      early_okW p c (cs (f i) c) (pcs (f i) c) (tp (f i) c) (tm (f i)) t1 Plain xs d B)) /\
  exists m' a K w, (oh (cs (f i) c) k <> None -> w = true) /\ (oh (cs (f i) c) k <> None -> vok (rg (cs (f i) c) k) = true) /\
    eff (tm (f i)) (inst_of d) (rg (cs (f i) c)) (mof (f i) c) m' a K u w /\
    f (S i) = searly (f i) c k d B m' a K u w.

(* the data of a CAS's read alone *)
Definition early_atR (c k i : nat) (xs : list cell) (B : nat -> bool) (u : cell -> option nat) : Prop :=
  i < n /\ pcs (f i) c <= k /\ oc (cs (f i) c) k = None /\ oh (cs (f i) c) k = None /\
  (forall k' d', pending (cs (f i) c) (pcs (f i) c) k' d' -> tied (crd Plain xs) (inst_of d') -> k' < k) /\
  early_okR p c (cs (f i) c) (pcs (f i) c) (tp (f i) c) (tm (f i)) Plain xs u B /\
  exists m' a K w bv, eff (tm (f i)) (ILd Plain xs (fun _ => true)) (rg (cs (f i) c)) (mof (f i) c) m' a K u w /\
    f (S i) = sread (f i) c k Plain xs B m' a K u w bv.

Lemma early_of_pending : forall m c k t, m <= n -> pcs (f m) c <= k -> oc (cs (f m) c) k = Some t ->
  exists i d B u, early_at c k i d B u /\ i < m /\ tm (f i) = t.
Proof.
  intros m c k t Lm P O. destruct (early_birth p f n T m c k t Lm P O) as (i & d & B & m' & a & K & u & w & A).
  destruct A as (L1 & L2 & L3 & L4 & L45 & L5 & L5w & L5v & L6 & L7).
  exists i, d, B, u. split; [|split; auto]. split; [lia|]. repeat (split; [auto|]). exists m', a, K, w. auto.
Qed.

Lemma early_of_hpending : forall m c k t, m <= n -> oh (cs (f m) c) k = Some t ->
  exists i xs B u, early_atR c k i xs B u /\ i < m /\ tm (f i) = t.
Proof.
  intros m c k t Lm O. destruct (half_birth p f n T m c k t Lm O) as (i & xs & B & m' & a & K & u & w & bv & A).
  destruct A as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
  exists i, xs, B, u. split; [|split; auto]. split; [lia|]. repeat (split; [auto|]). exists m', a, K, w, bv. auto.
Qed.

Lemma early_post : forall c k i d B u, early_at c k i d B u ->
  oc (cs (f (S i)) c) k = Some (tm (f i)) /\ ai (cs (f (S i)) c) k = inst_of d /\
  pcs (f (S i)) c = pcs (f i) c /\ bd (cs (f (S i)) c) = bor (bd (cs (f i) c)) B /\
  (forall j, j <> k -> oc (cs (f (S i)) c) j = oc (cs (f i) c) j) /\
  (forall j, j <> k -> rg (cs (f (S i)) c) j = rg (cs (f i) c) j) /\
  (forall j, j <> k -> ai (cs (f (S i)) c) j = ai (cs (f i) c) j) /\
  (forall c', c' <> c -> cs (f (S i)) c' = cs (f i) c') /\ tp (f i) c <= tp (f (S i)) c /\
  pcs (f (S i)) = pcs (f i).
Proof.
  intros c k i d B u (_ & _ & _ & _ & _ & m' & a & K & w & _ & _ & _ & E). rewrite E.
  unfold searly, set_es, searly0, evs; simpl. rewrite !upd_eq'. simpl. rewrite !upd_eq'.
  split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [|split; [|split; [|split; [|split]]]].
  - intros j N. apply upd_neq'. auto.
  - intros j N. apply upd_neq'. auto.
  - intros j N. apply upd_neq'. auto.
  - intros c' N. apply upd_neq'. auto.
  - lia.
  - reflexivity.
Qed.

Lemma early_postR : forall c k i xs B u, early_atR c k i xs B u ->
  oh (cs (f (S i)) c) k = Some (tm (f i)) /\ ai (cs (f (S i)) c) k = crd Plain xs /\
  pcs (f (S i)) c = pcs (f i) c /\ oc (cs (f (S i)) c) = oc (cs (f i) c) /\
  (forall c', c' <> c -> cs (f (S i)) c' = cs (f i) c') /\ pcs (f (S i)) = pcs (f i).
Proof.
  intros c k i xs B u (_ & _ & _ & _ & _ & _ & m' & a & K & w & bv & _ & E). rewrite E.
  unfold sread; simpl. rewrite !upd_eq'. simpl. rewrite !upd_eq'.
  split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [|reflexivity].
  intros c' N. apply upd_neq'. auto.
Qed.

Lemma early_pending : forall c k i d B u m, early_at c k i d B u -> i < m -> m <= n -> pcs (f m) c <= k ->
  pending (cs (f m) c) (pcs (f m) c) k d /\ oc (cs (f m) c) k = Some (tm (f i)).
Proof.
  intros c k i d B u m Ea Lim Lm Pk.
  destruct (early_post c k i d B u Ea) as (O1 & A1 & P1 & _).
  pose proof Ea as (Li & Lk & _).
  assert (Om : oc (cs (f m) c) k = Some (tm (f i))) by (apply (x_oc _ _ (tr_ext p f n T (S i) m ltac:(lia) Lm)); auto).
  destruct (pend_fate p f n T (S i) m c k d ltac:(lia) Lm W ltac:(congruence) ltac:(lia) A1) as [(_ & Am)|(X & _)]; [|lia].
  split; [split; [auto|split; [congruence|auto]]|auto].
Qed.

Lemma early_pendingR : forall c k i xs B u m, early_atR c k i xs B u -> i < m -> m <= n -> pcs (f m) c <= k ->
  hpending (cs (f m) c) (pcs (f m) c) k Plain xs /\ oh (cs (f m) c) k = Some (tm (f i)).
Proof.
  intros c k i xs B u m Ea Lim Lm Pk.
  destruct (early_postR c k i xs B u Ea) as (O1 & A1 & P1 & _).
  pose proof Ea as (Li & _).
  assert (X : Ext (f (S i)) (f m)) by (apply (tr_ext p f n T); lia).
  assert (Oh : oh (cs (f m) c) k = Some (tm (f i))) by (apply (x_oh _ _ X); auto).
  split; [|exact Oh]. split; [exact Pk|]. split; [congruence|].
  rewrite (x_cash _ _ X c k ltac:(congruence) Pk), A1. reflexivity.
Qed.

(* a pending item: an early access, or a CAS's read alone, alive at m *)
Definition item (c k i : nat) (g : tgt) : Prop :=
  (exists d B u, g = TF d /\ early_at c k i d B u) \/ (exists xs B u, g = TH Plain xs /\ early_atR c k i xs B u).
Definition alive (c k : nat) (g : tgt) (m : nat) : Prop := pcs (f m) c <= k.

Lemma item_i : forall c k i g, item c k i g -> i < n.
Proof. intros c k i g [(d & B & u & _ & Ea)|(xs & B & u & _ & Ea)]; apply Ea. Qed.

Lemma item_pc : forall c k i g, item c k i g -> pcs (f (S i)) c = pcs (f i) c.
Proof.
  intros c k i g [(d & B & u & _ & Ea)|(xs & B & u & _ & Ea)];
    [apply (early_post c k i d B u Ea)|apply (early_postR c k i xs B u Ea)].
Qed.

Lemma alive_le : forall c k g m m', alive c k g m' -> m <= m' -> m' <= n -> alive c k g m.
Proof.
  intros c k g m m' P L L'. assert (X : Ext (f m) (f m')) by (apply (tr_ext p f n T); lia).
  unfold alive in *. pose proof (x_pcs _ _ X c). lia.
Qed.

(* the item at m, pending as it was born *)
Lemma item_pending : forall c k i g m, item c k i g -> i < m -> m <= n -> alive c k g m ->
  (exists d, g = TF d /\ pending (cs (f m) c) (pcs (f m) c) k d /\ oc (cs (f m) c) k = Some (tm (f i))) \/
  (exists xs, g = TH Plain xs /\ hpending (cs (f m) c) (pcs (f m) c) k Plain xs /\
     oh (cs (f m) c) k = Some (tm (f i))).
Proof.
  intros c k i g m [(d & B & u & -> & Ea)|(xs & B & u & -> & Ea)] Lim Lm P.
  - left. exists d. split; auto. apply (early_pending c k i d B u m Ea Lim Lm P).
  - right. exists xs. split; auto. apply (early_pendingR c k i xs B u m Ea Lim Lm P).
Qed.

(* the place of a pending item, under registers that continue a later state,
   is its place in the state just after it happened *)
Lemma place_trace : forall c k i g m r j, item c k i g -> S i <= m -> m <= n -> alive c k g m ->
  agree r (rg (cs (f m) c)) (pcs (f m) c) -> pcs (f m) c <= j ->
  (plc p c (cs (f m) c) (pcs (f m) c) r (S (tm (f i))) (tm (f i)) g j <->
   plc p c (cs (f (S i)) c) (pcs (f (S i)) c) r (S (tm (f i))) (tm (f i)) g j).
Proof.
  intros c k i g m r j It L1 Lm Al Ag Lj.
  revert L1 Lm Al Ag Lj. induction m as [|m IH]; intros L1 Lm Al Ag Lj; [lia|].
  destruct (Nat.eq_dec (S m) (S i)) as [E|N]; [rewrite E; reflexivity|].
  assert (Xm : Ext (f (S m)) (f (S m))) by apply Ext_refl.
  assert (Rm : run p (f m)) by (apply (tr_run p f n T); lia).
  assert (Xq : Ext (f m) (f (S m))) by (apply (tr_ext p f n T); lia).
  assert (Im : Inv1 p (f m)) by (apply Inv1_run; exact Rm).
  assert (AlM : alive c k g m) by (apply (alive_le c k g m (S m) Al); lia).
  assert (Agm : agree r (rg (cs (f m) c)) (pcs (f m) c)).
  { intros z Lz. rewrite Ag by (pose proof (x_pcs _ _ Xq c); lia). apply (x_rg _ _ Xq). left. auto. }
  rewrite <- (IH ltac:(lia) ltac:(lia) AlM Agm ltac:(pose proof (x_pcs _ _ Xq c); lia)).
  symmetry. apply (step_place_g p (f m) (f (S m)) c k (tm (f i)) r j g W Wc Rm (tr_step p f n T m ltac:(lia))); auto.
  destruct (item_pending c k i g (S m) It ltac:(lia) Lm Al) as [(d & -> & Pd & _)|(xs & -> & Ph & _)].
  - left. exists d. split; auto. split; auto.
    destruct (item_pending c k i (TF d) m It ltac:(lia) ltac:(lia) AlM) as [(d' & E' & _ & O')|(xs & E' & _)]; [|discriminate].
    injection E' as <-. exact O'.
  - right. exists Plain, xs. split; auto. split; auto.
    destruct (item_pending c k i (TH Plain xs) m It ltac:(lia) ltac:(lia) AlM) as [(d' & E' & _)|(xs' & E' & _ & O')]; [discriminate|].
    exact O'.
Qed.

(* an early access's place is after the next instruction of the state it
   happened in *)
Lemma own_lt : forall c k i d B u r j, early_at c k i d B u ->
  agree r (rg (cs (f i) c)) (pcs (f i) c) -> first_at p c (cs (f (S i)) c) (pcs (f i) c) r (tm (f i)) d j ->
  pcs (f i) c < j.
Proof.
  intros c k i d B u r j Ea Ag F. pose proof Ea as (Li & Lk & Ho & Hso & Hh & m' & a & K & w & HwE & HvE & He & E).
  assert (Ri : run p (f i)) by (apply (tr_run p f n T); lia).
  pose proof (Inv1_run p (f i) Ri) as Ii.
  pose proof (first_at_le _ _ _ _ _ _ _ _ F) as Lj.
  destruct (Nat.eq_dec j (pcs (f i) c)) as [->|N]; [exfalso|lia].
  set (g := creg p c (cs (f i) c) (pcs (f i) c) (tp (f i) c) (bor (bd (cs (f i) c)) B) (Fd p c r)).
  assert (Ag2 : agree r g (pcs (f i) c)).
  { intros q Lq. unfold g. rewrite (creg_lt_pc p c _ _ _ _ (Fd p c r) q W (pend_ok_of p (f i) c Ii) Lq). apply Ag. auto. }
  destruct Hh as [(Z & Eok)|(t1 & xs & ev & nv & Z & -> & U & Ac & Okw)].
  - assert (Ct : cs (f (S i)) c = cce (f i) c k d B m' a u w) by (rewrite E; apply cce_eq).
    rewrite Ct in F. apply (early_same p (f i) c k d B m' a u w Lk Ho Z r (tm (f i)) d _ (le_n _)) in F.
    pose proof (first_at_agree p W c _ _ r g _ d _ Ag2 F) as Fg.
    destruct (Eok (Fd p c r)) as (j0 & Lj0 & F0 & _). fold g in F0.
    pose proof (first_at_unique _ _ _ _ _ _ _ _ _ Wc F0 Fg). lia.
  - subst u. assert (Ct : cs (f (S i)) c = ccw (f i) c k xs ev nv B m' a w) by (rewrite E; apply ccw_eq).
    rewrite Ct in F. pose proof (first_at_agree p W c _ _ r g _ _ _ Ag2 F) as Fg.
    destruct (Okw (Fd p c r)) as (j0 & Lj0 & FR0 & ED0 & BT0). fold g in FR0, ED0, BT0.
    pose proof (cwe_place p (f i) c k t1 xs ev nv B m' a K w Wc Ii (proj2 (Inv2_run p (f i) Ri)) Lk Ho Z Ac He HvE HwE g j0 FR0 ED0 BT0) as F0.
    pose proof (first_at_unique _ _ _ _ _ _ _ _ _ Wc F0 Fg). lia.
Qed.

(* the place of a pending item is not before the next instruction of a
   later state it is still pending in *)
Lemma place_ge : forall c k i g m r j, item c k i g -> S i <= m -> m <= n -> alive c k g m ->
  agree r (rg (cs (f m) c)) (pcs (f m) c) ->
  plc p c (cs (f (S i)) c) (pcs (f (S i)) c) r (S (tm (f i))) (tm (f i)) g j -> pcs (f m) c <= j.
Proof.
  intros c k i g m r j It L1 Lm Al Ag F.
  destruct (Nat.lt_ge_cases j (pcs (f m) c)) as [Lt|Ge]; auto. exfalso.
  destruct (pass_birth p f n T m c j Lm Lt) as (q & Lq & Pq & PSq & Cs).
  pose proof (item_i c k i g It) as Li. pose proof (item_pc c k i g It) as Pi.
  assert (Lij : pcs (f (S i)) c <= j) by (rewrite plc_in in F; apply F).
  assert (Liq : S i <= q).
  { destruct (Nat.le_gt_cases (S i) q) as [X|X]; auto. exfalso.
    pose proof (x_pcs _ _ (tr_ext p f n T (S q) (S i) ltac:(lia) ltac:(lia)) c). lia. }
  assert (Xq : Ext (f q) (f m)) by (apply (tr_ext p f n T); lia).
  assert (Rq : run p (f q)) by (apply (tr_run p f n T); lia).
  pose proof (Inv1_run p (f q) Rq) as Iq.
  assert (Agq : agree r (rg (cs (f q) c)) (pcs (f q) c)).
  { intros z Lz. rewrite Ag by (pose proof (x_pcs _ _ Xq c); lia). apply (x_rg _ _ Xq). left. auto. }
  assert (Alq : alive c k g q) by (apply (alive_le c k g q m Al); lia).
  assert (Fq : plc p c (cs (f q) c) (pcs (f q) c) r (S (tm (f i))) (tm (f i)) g j).
  { apply (place_trace c k i g q r j It Liq ltac:(lia) Alq Agq ltac:(lia)). exact F. }
  pose proof Fq as Fq0.
  rewrite <- Pq in Fq. rewrite plc_in in Fq. destruct Fq as (_ & D & _ & _).
  assert (Lkj : j < k) by (unfold alive in Al; lia).
  destruct (item_pending c k i g q It ltac:(lia) ltac:(lia) Alq) as [(d & -> & Pend & Oq)|(xs & -> & Ph & Oq)].
  - destruct Cs as [(i0 & m' & a & K & u' & w & Hi & Ho & _ & Hb & _ & _ & _ & E)|[(d0 & Ho & Ha & Hdf & _ & Hf & Hfh & E)|(Kx & Ko & Kh & Kvv & Kf & Kd & E)]].
    3:{ (* a CAS that failed after its read: its read took the place first *)
        exfalso. cbv zeta in Kx, Ko, Kh, Kf. subst j. rewrite (eof_agree p W c _ r _ Agq) in D.
        destruct (eof_exec_tied _ _ _ _ _ Wc D) as [Ex Tt].
        destruct (xex_false _ _ _ _ Kx) as [X0|(Nh & Cf)]; [congruence|].
        destruct (oh (cs (f q) c) (pcs (f q) c)) as [t1|] eqn:Ohk; [|congruence].
        destruct (i_half p (f q) Iq c _ t1 Ko Ohk (le_n _)) as (_ & (xs1 & Ax) & _).
        assert (Er : eofR (ins p c (pcs (f q) c) (rg (cs (f q) c))) (rg (cs (f q) c)) = Some (Plain, xs1))
          by (rewrite (Kh ltac:(congruence)), Ax; reflexivity).
        assert (Nk : k <> pcs (f q) c) by (intros Ek; rewrite Ek in Oq; congruence).
        pose proof (proj1 (Kf t1 Ohk) k d (tm (f i)) Pend Nk Oq Tt) as Lt1.
        apply (plc_hfree _ _ _ _ _ _ _ _ Fq0). apply (skf_htaken p (f q) c t1 xs1 W Wc Ko Ohk Ax Er Kf r (tm (f i)) Agq Lt1). }
    + rewrite (eof_agree p W c _ r _ Agq) in D.
      destruct (eof_exec_tied _ _ _ _ _ Wc D) as [Ex Tt]. rewrite Pq in Ex, Tt. rewrite Hi in Ex, Tt.
      rewrite Pq in Pend. apply (Hb Ex k d Pend Tt).
    + rewrite <- Pq in Ho, Ha, Hdf, Hf, Hfh.
      assert (Ote : exists te, oc (cs (f q) c) (pcs (f q) c) = Some te) by (destruct (oc (cs (f q) c) (pcs (f q) c)); [eauto|congruence]).
      destruct Ote as (te & Ote).
      pose proof (place_pc p (f q) c d0 W Wc Hdf Hf Hfh r te Agq Ote) as F0.
      assert (Pl1 : placed p c (cs (f q) c) (pcs (f q) c) r k d (pcs (f q) c)).
      { split; [exact Pend|exists (tm (f i))]. split; [exact Oq|]. rewrite <- Pq in F.
        apply (place_trace c k i (TF d) q r (pcs (f q) c) It Liq ltac:(lia) Alq Agq (le_n _)). exact F. }
      assert (Pl2 : placed p c (cs (f q) c) (pcs (f q) c) r (pcs (f q) c) d0 (pcs (f q) c))
        by (split; [split; [lia|split; [congruence|exact Ha]]|exists te; auto]).
      pose proof (placed_unique p c _ _ (oc_inj p (f q) c Iq) r _ _ _ _ _ Pl1 Pl2). lia.
  - destruct Cs as [(i0 & m' & a & K & u' & w & Hi & Ho & _ & _ & Hbh & _ & _ & E)|[(d0 & Ho & Ha & Hdf & _ & Hf & Hfh & E)|(Kx & Ko & Kh & Kvv & Kf & Kd & E)]].
    3:{ exfalso. cbv zeta in Kx, Ko, Kh, Kf. subst j. rewrite (eofR_agree p W c _ r _ Agq) in D.
        destruct (eofR_exec_tied _ _ _ _ _ _ Wc D) as [Ex Tt].
        destruct (xex_false _ _ _ _ Kx) as [X0|(Nh & Cf)]; [congruence|].
        destruct (oh (cs (f q) c) (pcs (f q) c)) as [t1|] eqn:Ohk; [|congruence].
        destruct (i_half p (f q) Iq c _ t1 Ko Ohk (le_n _)) as (_ & (xs1 & Ax) & _).
        assert (Er : eofR (ins p c (pcs (f q) c) (rg (cs (f q) c))) (rg (cs (f q) c)) = Some (Plain, xs1))
          by (rewrite (Kh ltac:(congruence)), Ax; reflexivity).
        pose proof (proj2 (Kf t1 Ohk) k Plain xs (tm (f i)) Ph ltac:(lia) Oq Tt) as Lt1.
        apply (plc_hfree _ _ _ _ _ _ _ _ Fq0). apply (skf_htaken p (f q) c t1 xs1 W Wc Ko Ohk Ax Er Kf r (tm (f i)) Agq Lt1). }
    + rewrite (eofR_agree p W c _ r _ Agq) in D.
      destruct (eofR_exec_tied _ _ _ _ _ _ Wc D) as [Ex Tt]. rewrite Pq in Ex, Tt. rewrite Hi in Ex, Tt.
      rewrite Pq in Ph. apply (Hbh Ex k Plain xs Ph ltac:(lia) Tt).
    + rewrite <- Pq in Ho, Ha, Hdf, Hf, Hfh.
      assert (Ote : exists te, oc (cs (f q) c) (pcs (f q) c) = Some te) by (destruct (oc (cs (f q) c) (pcs (f q) c)); [eauto|congruence]).
      destruct Ote as (te & Ote).
      pose proof (place_pc p (f q) c d0 W Wc Hdf Hf Hfh r te Agq Ote) as F0.
      assert (Fh : first_atR p c (cs (f q) c) (pcs (f q) c) r (tm (f i)) Plain xs (pcs (f q) c)).
      { rewrite <- Pq in F. apply (place_trace c k i (TH Plain xs) q r (pcs (f q) c) It Liq ltac:(lia) Alq Agq (le_n _)). exact F. }
      pose proof (first_atR_eofR _ _ _ _ _ _ _ _ _ Fh) as DR. pose proof (first_at_eof _ _ _ _ _ _ _ _ F0) as D0.
      assert (Ne : dd xs <> []).
      { pose proof (Wc c (pcs (f q) c) r) as Q. destruct (ins p c (pcs (f q) c) r) as [m1 x1 c1|m1 x1 c1 v1|m0 x0 c0 e0 n0|f1|];
          simpl in DR; try discriminate. destruct (c0 r); [injection DR as -> ->|discriminate]. exact (Q eq_refl). }
      assert (Dc : exists e0 n0, d0 = DCas Plain xs e0 n0).
      { destruct (ins p c (pcs (f q) c) r) as [m1 x1 c1|m1 x1 c1 v1|m0 x0 c0 e0 n0|f1|]; simpl in DR, D0; try discriminate.
        destruct (c0 r); [|discriminate]. injection DR as -> ->. injection D0 as <-. eauto. }
      destruct Dc as (e0 & n0 & ->).
      destruct (Nat.lt_trichotomy te (tm (f i))) as [Lte|[Et|Gt]].
      * apply (first_atR_free _ _ _ _ _ _ _ _ _ Fh). exists (pcs (f q) c), te, (DCas Plain xs e0 n0).
        split; [split; [lia|split; [congruence|exact Ha]]|]. split; [exact Ote|]. split; [exact Lte|exact F0].
      * subst te. destruct (i_oc p (f q) Iq c _ _ Ote) as (e1 & E1 & C1 & K1).
        destruct (i_oh p (f q) Iq c k _ Oq) as (e2 & E2 & _ & _ & Eh). rewrite E1 in E2. injection E2 as <-.
        rewrite (oc_eh p (f q) c _ _ e1 Iq Ote E1 C1 K1) in Eh. discriminate.
      * apply (first_at_hfree _ _ _ _ _ _ _ _ F0). exists k, (tm (f i)), Plain, xs.
        split; [exact Ph|]. split; [exact Oq|]. split; [exact Gt|]. split; [|exact Fh].
        intros tw Ow. destruct Ph as (Ph1 & _ & Ph3).
        destruct (proj1 (i_pend p (f q) Iq c k Ph1 ltac:(rewrite Ow; discriminate))) as (dk & Ak & _).
        rewrite Ak in Ph3. destruct dk as [| |mk xk ek nk|]; simpl in Ph3; try discriminate. injection Ph3 as -> ->.
        apply (Hf k (DCas Plain xs ek nk) te tw); [split; [exact Ph1|split; [rewrite Ow; discriminate|exact Ak]]|lia|exact Ote|exact Ow|].
        left. change (exists y, In y (dd xs) /\ In y (dd xs)). destruct (dd xs) as [|x l]; [congruence|]. exists x. split; left; reflexivity.
Qed.

(* a pending access passed by a later state: its place there, under
   registers that continue that later state, is its slot *)
Lemma passed_place : forall c k i d B u m r j, early_at c k i d B u -> S i <= m -> m <= n -> k < pcs (f m) c ->
  agree r (rg (cs (f m) c)) (pcs (f m) c) ->
  first_at p c (cs (f (S i)) c) (pcs (f (S i)) c) r (tm (f i)) d j -> j = k.
Proof.
  intros c k i d B u m r j Ea Lim Lm Lk Ag F.
  assert (It : item c k i (TF d)) by (left; exists d, B, u; auto).
  pose proof Ea as (Li & Lik & _).
  destruct (pass_birth p f n T m c k Lm Lk) as (q & Lq & Pq & PSq & Cs).
  pose proof (item_pc c k i (TF d) It) as Pi.
  assert (Liq : S i <= q).
  { destruct (Nat.le_gt_cases (S i) q) as [X|X]; auto. exfalso.
    pose proof (x_pcs _ _ (tr_ext p f n T q i ltac:(lia) ltac:(lia)) c). lia. }
  assert (Xq : Ext (f q) (f m)) by (apply (tr_ext p f n T); lia).
  assert (Rq : run p (f q)) by (apply (tr_run p f n T); lia).
  pose proof (Inv1_run p (f q) Rq) as Iq.
  assert (Agq : agree r (rg (cs (f q) c)) (pcs (f q) c)).
  { intros z Lz. rewrite Ag by (pose proof (x_pcs _ _ Xq c); lia). apply (x_rg _ _ Xq). left. auto. }
  assert (Alq : alive c k (TF d) q) by (unfold alive; lia).
  destruct (early_pending c k i d B u q Ea ltac:(lia) ltac:(lia) ltac:(lia)) as (Pend & Oq).
  rewrite <- Pq in Pend, Oq.
  destruct Cs as [(i0 & m' & a & K & u' & w & Hi & Ho & _)|[(d0 & Ho & Ha & Hdf & _ & Hf & Hfh & E)|(Kx & Ko & Kh & Kvv & Kf & Kd & E)]].
  3:{ exfalso. cbv zeta in Ko. rewrite <- Pq in Ko. congruence. }
  - rewrite <- Pq in Ho. congruence.
  - rewrite <- Pq in Ho, Ha, Hdf, Hf, Hfh.
    destruct Pend as (_ & _ & Pa). rewrite Ha in Pa. apply inst_of_inj in Pa. subst d0.
    pose proof (place_pc p (f q) c d W Wc Hdf Hf Hfh r (tm (f i)) Agq Oq) as F0.
    assert (Ge : pcs (f q) c <= j) by (apply (place_ge c k i (TF d) q r j It Liq ltac:(lia) Alq Agq F)).
    assert (Fq : first_at p c (cs (f q) c) (pcs (f q) c) r (tm (f i)) d j).
    { apply (place_trace c k i (TF d) q r j It Liq ltac:(lia) Alq Agq Ge). exact F. }
    pose proof (first_at_unique _ _ _ _ _ _ _ _ _ Wc Fq F0). lia.
Qed.
(* a CAS's read alone passed by a later state: its place there is its slot *)
Lemma passed_placeR : forall c k i xs B u m r j, early_atR c k i xs B u -> S i <= m -> m <= n -> k < pcs (f m) c ->
  agree r (rg (cs (f m) c)) (pcs (f m) c) ->
  first_atR p c (cs (f (S i)) c) (pcs (f (S i)) c) r (tm (f i)) Plain xs j -> j = k.
Proof.
  intros c k i xs B u m r j Ea Lim Lm Lk Ag F.
  assert (It : item c k i (TH Plain xs)) by (right; exists xs, B, u; auto).
  pose proof Ea as (Li & Lik & _).
  destruct (pass_birth p f n T m c k Lm Lk) as (q & Lq & Pq & PSq & Cs).
  pose proof (item_pc c k i (TH Plain xs) It) as Pi.
  assert (Liq : S i <= q).
  { destruct (Nat.le_gt_cases (S i) q) as [X|X]; auto. exfalso.
    pose proof (x_pcs _ _ (tr_ext p f n T (S q) (S i) ltac:(lia) ltac:(lia)) c). lia. }
  assert (Xq : Ext (f q) (f m)) by (apply (tr_ext p f n T); lia).
  assert (Rq : run p (f q)) by (apply (tr_run p f n T); lia).
  pose proof (Inv1_run p (f q) Rq) as Iq.
  assert (Agq : agree r (rg (cs (f q) c)) (pcs (f q) c)).
  { intros z Lz. rewrite Ag by (pose proof (x_pcs _ _ Xq c); lia). apply (x_rg _ _ Xq). left. auto. }
  assert (Alq : alive c k (TH Plain xs) q) by (unfold alive; lia).
  destruct (early_pendingR c k i xs B u q Ea ltac:(lia) ltac:(lia) ltac:(lia)) as (Ph & Oh).
  assert (Ge : pcs (f q) c <= j) by (apply (place_ge c k i (TH Plain xs) q r j It Liq ltac:(lia) Alq Agq F)).
  assert (Fq : first_atR p c (cs (f q) c) (pcs (f q) c) r (tm (f i)) Plain xs j).
  { apply (place_trace c k i (TH Plain xs) q r j It Liq ltac:(lia) Alq Agq Ge). exact F. }
  rewrite <- Pq in Ph, Oh.
  destruct Cs as [(i0 & m' & a & K & u' & w & Hi & Ho & Hd & Hb & Hbh & Hhalf & He & E)|[(d0 & Ho & Ha & Hdf & _ & Hf & Hfh & E)|(Kx & Ko & Kh & Kvv & Kf & Kd & E)]].
  3:{ (* passed as a CAS that failed: its read's place is its slot *)
      cbv zeta in Kx, Ko, Kh, Kf. rewrite <- Pq in Kx, Ko, Kh, Kf.
      destruct (i_half p (f q) Iq c _ _ Ko Oh (le_n _)) as (_ & (xs1 & Ax) & _).
      pose proof Ph as (_ & _ & Cx). rewrite Ax in Cx. assert (xs1 = xs) by (cbn in Cx; congruence). subst xs1.
      assert (Er : eofR (ins p c (pcs (f q) c) (rg (cs (f q) c))) (rg (cs (f q) c)) = Some (Plain, xs))
        by (rewrite (Kh ltac:(congruence)), Ax; reflexivity).
      pose proof (skf_place p (f q) c (tm (f i)) xs W Wc Ko Oh Er Kf r Agq) as F0.
      pose proof (first_atR_unique p c _ _ r _ _ _ j (pcs (f q) c) Wc Fq F0). lia. }
  - cbv zeta in *. rewrite <- Pq in Hi, Ho, Hb, Hbh, Hhalf.
    pose proof (ord_firstR_pc p (f q) c i0 u' W Wc Iq Hi Ho Hb Hbh Hhalf r (tm (f i)) Plain xs Agq Oh Ph) as F0.
    pose proof (first_atR_unique p c _ _ r _ _ _ j (pcs (f q) c) Wc Fq F0). lia.
  - rewrite <- Pq in Ho, Ha, Hdf, Hf, Hfh.
    assert (Ote : exists te, oc (cs (f q) c) (pcs (f q) c) = Some te) by (destruct (oc (cs (f q) c) (pcs (f q) c)); [eauto|congruence]).
    destruct Ote as (te & Ote).
    pose proof (placeR_pc p (f q) c d0 W Wc Iq Ha Hdf Hf Hfh r te (tm (f i)) Plain xs Agq Ote Oh Ph) as F0.
    pose proof (first_atR_unique p c _ _ r _ _ _ j (pcs (f q) c) Wc Fq F0). lia.
Qed.

(* a CAS whose read happened alone and whose write happened: under registers
   that continue a later state, it does not fail at its read's place *)
Lemma half_wrote_ok : forall c kh ih xs B u m r J jd, early_atR c kh ih xs B u -> S ih <= m -> m <= n ->
  ccJ p c (cs (f m) c) (pcs (f m) c) (bd (cs (f m) c)) r J -> jd <= J ->
  first_atR p c (cs (f (S ih)) c) (pcs (f (S ih)) c) r (tm (f ih)) Plain xs jd ->
  oc (cs (f m) c) kh <> None -> cfailv (ins p c jd r) r (rg (cs (f m) c) kh) = false.
Proof.
  intros c kh ih xs B u m r J jd Ea Lm Lmn Cm Lj Fh Oc.
  assert (Rm : run p (f m)) by (apply (tr_run p f n T); lia).
  pose proof (Inv1_run p (f m) Rm) as Im.
  destruct (early_postR c kh ih xs B u Ea) as (Oh1 & Ah1 & _).
  assert (Xm : Ext (f (S ih)) (f m)) by (apply (tr_ext p f n T); lia).
  pose proof (x_oh _ _ Xm c kh _ Oh1) as Ohm.
  destruct (oc (cs (f m) c) kh) as [tw|] eqn:Ocm; [|congruence].
  pose proof (i_hocf p (f m) Im c kh _ tw Ohm Ocm) as Hf.
  pose proof Cm as (_ & A1 & _).
  destruct (Nat.lt_ge_cases kh (pcs (f m) c)) as [Lk|Lk].
  - (* passed: its read's place is its slot *)
    assert (Agm : agree r (rg (cs (f m) c)) (pcs (f m) c)) by (intros q Lq; apply A1; exact Lq).
    pose proof (passed_placeR c kh ih xs B u m r jd Ea Lm Lmn Lk Agm Fh) as ->.
    destruct (proj1 (i_cmA p (f m) Im c kh) Lk) as (tau & Tau). rewrite (proj2 (i_set p (f m) Im c kh tau Tau)) in Hf.
    unfold cfail in Hf. rewrite (cfailv_agree p W c kh r (rg (cs (f m) c)) _ (fun q Lq => A1 q ltac:(lia))). exact Hf.
  - (* pending: its write happened early, at its read's place *)
    destruct (early_of_pending m c kh tw Lmn Lk Ocm) as (iw & d & B2 & u2 & Eaw & Liw & Tiw).
    pose proof (i_hoc p (f m) Im c kh _ tw Ohm Ocm) as (Lth & _).
    assert (Lhw : ih < iw) by (apply (tr_tm_lt p f n T); [lia|lia|lia]).
    pose proof Eaw as (Liw' & Lkw & Ow & _ & Hw & m2 & a2 & K2 & w2 & He2 & Ew).
    assert (Xw : Ext (f (S ih)) (f iw)) by (apply (tr_ext p f n T); lia).
    pose proof (x_oh _ _ Xw c kh _ Oh1) as Ohw.
    destruct Hw as [(Z & _)|(t1 & xs1 & ev & nv & Z & -> & U & Aw & Okw)]; [congruence|].
    rewrite Ohw in Z. injection Z as <-.
    assert (Ax : xs1 = xs).
    { pose proof (x_cash _ _ Xw c kh ltac:(congruence) ltac:(lia)) as Cx. rewrite Aw, Ah1 in Cx. cbn in Cx. congruence. }
    subst xs1.
    destruct (early_post c kh iw (DCas Plain xs ev nv) B2 u2 Eaw) as (O2 & A2 & P2 & Bd2 & _).
    (* the registers continue the state before the write, counting its binders *)
    assert (Rw : run p (f iw)) by (apply (tr_run p f n T); lia).
    assert (C1 : ccJ p c (cs (f (S iw)) c) (pcs (f (S iw)) c) (bd (cs (f (S iw)) c)) r J)
      by (apply (mono_tr c r J (S iw) m); auto; lia).
    pose proof (mono_step p (f iw) (f (S iw)) W Rw (tr_step p f n T iw ltac:(lia)) Wc c r J C1) as C2.
    rewrite Bd2 in C2.
    pose proof (ccJ_agree p (f iw) W Wc Rw c _ r J C2) as Ag2.
    set (g := creg p c (cs (f iw) c) (pcs (f iw) c) (tp (f iw) c) (bor (bd (cs (f iw) c)) B2) (Fd p c r)) in *.
    destruct (Okw (Fd p c r)) as (j0 & Lj0 & FR0 & ED0 & _). fold g in FR0, ED0.
    pose proof C2 as (_ & A1w & _).
    assert (Agw : agree r (rg (cs (f iw) c)) (pcs (f iw) c)) by (intros q Lq; apply A1w; exact Lq).
    assert (Alw : alive c kh (TH Plain xs) iw) by (unfold alive; lia).
    assert (It : item c kh ih (TH Plain xs)) by (right; exists xs, B, u; auto).
    assert (Gej : pcs (f iw) c <= jd)
      by (apply (place_ge c kh ih (TH Plain xs) iw r jd It ltac:(lia) ltac:(lia) Alw Agw Fh)).
    assert (Fw : first_atR p c (cs (f iw) c) (pcs (f iw) c) r (tm (f ih)) Plain xs jd)
      by (apply (place_trace c kh ih (TH Plain xs) iw r jd It ltac:(lia) ltac:(lia) Alw Agw Gej); exact Fh).
    assert (Fg : first_atR p c (cs (f iw) c) (pcs (f iw) c) g (tm (f ih)) Plain xs jd).
    { unfold first_atR in *. apply (plc_agree p W c _ _ _ r g _ _ jd); [intros q Lq; apply Ag2; lia|exact Fw]. }
    assert (Ej : j0 = jd) by (apply (first_atR_unique p c _ _ g _ _ _ j0 jd Wc FR0 Fg)). subst j0.
    rewrite <- (eof_agree p W c jd r g (fun q Lq => Ag2 q ltac:(lia))) in ED0.
    rewrite (x_aip _ _ (tr_ext p f n T (S iw) m ltac:(lia) Lmn) c kh ltac:(congruence) Lk), A2 in Hf.
    unfold cfail in Hf. simpl in Hf.
    revert ED0. generalize (ins p c jd r). intros i0 ED0.
    destruct i0 as [m0 x0 c0|m0 x0 c0 v0|m0 x0 c0 e0 n0|f0|]; simpl in ED0; try discriminate;
      [destruct (c0 r); discriminate|destruct (c0 r); discriminate| |destruct f0; discriminate].
    destruct (c0 r) eqn:C0; [|discriminate]. injection ED0 as _ _ Ee _. simpl. rewrite C0, Ee. exact Hf.
Qed.

(* a CAS whose read happened alone and whose write happened: under registers
   that continue a later state, the write has its read's place *)
Lemma half_wrote_placed : forall c kh ih xs B u m r J jd, early_atR c kh ih xs B u -> S ih <= m -> m <= n ->
  ccJ p c (cs (f m) c) (pcs (f m) c) (bd (cs (f m) c)) r J -> jd <= J ->
  first_atR p c (cs (f (S ih)) c) (pcs (f (S ih)) c) r (tm (f ih)) Plain xs jd ->
  oc (cs (f m) c) kh <> None -> pcs (f m) c <= kh -> exists d, placed p c (cs (f m) c) (pcs (f m) c) r kh d jd.
Proof.
  intros c kh ih xs B u m r J jd Ea Lm Lmn Cm Lj Fh Oc Lk.
  assert (Rm : run p (f m)) by (apply (tr_run p f n T); lia).
  pose proof (Inv1_run p (f m) Rm) as Im.
  destruct (early_postR c kh ih xs B u Ea) as (Oh1 & Ah1 & _).
  assert (Xm : Ext (f (S ih)) (f m)) by (apply (tr_ext p f n T); lia).
  pose proof (x_oh _ _ Xm c kh _ Oh1) as Ohm.
  destruct (oc (cs (f m) c) kh) as [tw|] eqn:Ocm; [|congruence].
  destruct (early_of_pending m c kh tw Lmn Lk Ocm) as (iw & d & B2 & u2 & Eaw & Liw & Tiw).
  pose proof (i_hoc p (f m) Im c kh _ tw Ohm Ocm) as (Lth & _).
  assert (Lhw : ih < iw) by (apply (tr_tm_lt p f n T); [lia|lia|lia]).
  pose proof Eaw as (Liw' & Lkw & Ow & _ & Hw & m2 & a2 & K2 & w2 & HwE & HvE & He2 & Ew).
  assert (Xw : Ext (f (S ih)) (f iw)) by (apply (tr_ext p f n T); lia).
  pose proof (x_oh _ _ Xw c kh _ Oh1) as Ohw.
  destruct Hw as [(Z & _)|(t1 & xs1 & ev & nv & Z & -> & U & Aw & Okw)]; [congruence|].
  rewrite Ohw in Z. injection Z as <-.
  assert (Ax : xs1 = xs).
  { pose proof (x_cash _ _ Xw c kh ltac:(congruence) ltac:(lia)) as Cx. rewrite Aw, Ah1 in Cx. cbn in Cx. congruence. }
  subst xs1. subst u2.
  destruct (early_post c kh iw (DCas Plain xs ev nv) B2 (rw (cs (f iw) c) kh) Eaw) as (O2 & A2 & P2 & Bd2 & _).
  assert (Rw : run p (f iw)) by (apply (tr_run p f n T); lia).
  pose proof (Inv1_run p (f iw) Rw) as Iw. pose proof (proj2 (Inv2_run p (f iw) Rw)) as Jw.
  assert (C1 : ccJ p c (cs (f (S iw)) c) (pcs (f (S iw)) c) (bd (cs (f (S iw)) c)) r J)
    by (apply (mono_tr c r J (S iw) m); auto; lia).
  pose proof (mono_step p (f iw) (f (S iw)) W Rw (tr_step p f n T iw ltac:(lia)) Wc c r J C1) as C2.
  rewrite Bd2 in C2.
  pose proof (ccJ_agree p (f iw) W Wc Rw c _ r J C2) as Ag2.
  set (g := creg p c (cs (f iw) c) (pcs (f iw) c) (tp (f iw) c) (bor (bd (cs (f iw) c)) B2) (Fd p c r)) in *.
  destruct (Okw (Fd p c r)) as (j0 & Lj0 & FR0 & ED0 & BT0). fold g in FR0, ED0, BT0.
  pose proof C2 as (_ & A1w & _).
  assert (Agw : agree r (rg (cs (f iw) c)) (pcs (f iw) c)) by (intros q Lq; apply A1w; exact Lq).
  assert (Alw : alive c kh (TH Plain xs) iw) by (unfold alive; lia).
  assert (It : item c kh ih (TH Plain xs)) by (right; exists xs, B, u; auto).
  assert (Gej : pcs (f iw) c <= jd)
    by (apply (place_ge c kh ih (TH Plain xs) iw r jd It ltac:(lia) ltac:(lia) Alw Agw Fh)).
  assert (Fw : first_atR p c (cs (f iw) c) (pcs (f iw) c) r (tm (f ih)) Plain xs jd)
    by (apply (place_trace c kh ih (TH Plain xs) iw r jd It ltac:(lia) ltac:(lia) Alw Agw Gej); exact Fh).
  assert (Fg : first_atR p c (cs (f iw) c) (pcs (f iw) c) g (tm (f ih)) Plain xs jd).
  { unfold first_atR in *. apply (plc_agree p W c _ _ _ r g _ _ jd); [intros q Lq; apply Ag2; lia|exact Fw]. }
  assert (Ej : j0 = jd) by (apply (first_atR_unique p c _ _ g _ _ _ j0 jd Wc FR0 Fg)). subst j0.
  pose proof (cwe_place p (f iw) c kh (tm (f ih)) xs ev nv B2 m2 a2 K2 w2 Wc Iw Jw Lkw Ow Ohw Aw He2 HvE HwE g jd FR0 ED0 BT0) as NP0.
  assert (Ct : cs (f (S iw)) c = ccw (f iw) c kh xs ev nv B2 m2 a2 w2) by (rewrite Ew; apply ccw_eq). rewrite <- Ct in NP0.
  assert (NPr : first_at p c (cs (f (S iw)) c) (pcs (f (S iw)) c) r (tm (f iw)) (DCas Plain xs ev nv) jd).
  { rewrite P2. apply (first_at_agree p W c _ _ g r _ _ jd); [intros q Lq; symmetry; apply Ag2; lia|exact NP0]. }
  assert (Itw : item c kh iw (TF (DCas Plain xs ev nv))) by (left; exists (DCas Plain xs ev nv), B2, (rw (cs (f iw) c) kh); auto).
  pose proof Cm as (_ & A1m & _).
  assert (Agm : agree r (rg (cs (f m) c)) (pcs (f m) c)) by (intros q Lq; apply A1m; exact Lq).
  assert (Gem : pcs (f m) c <= jd)
    by (apply (place_ge c kh ih (TH Plain xs) m r jd It ltac:(lia) ltac:(lia) Lk Agm Fh)).
  exists (DCas Plain xs ev nv). split.
  - split; [exact Lk|]. split; [rewrite Ocm; discriminate|].
    rewrite (x_aip _ _ (tr_ext p f n T (S iw) m ltac:(lia) Lmn) c kh ltac:(rewrite O2; discriminate) Lk). exact A2.
  - exists tw. split; [exact Ocm|]. unfold first_at. rewrite <- Tiw.
    apply (place_trace c kh iw (TF (DCas Plain xs ev nv)) m r jd Itw ltac:(lia) Lmn Lk Agm Gem). exact NPr.
Qed.

End MT.


Lemma cellv_f : forall p c cc pc N B f1 f2 r n j x, (forall b y, b <= j -> f1 b y = f2 b y) ->
  cellv p c cc pc N B f1 r n j x = cellv p c cc pc N B f2 r n j x.
Proof.
  intros p c cc pc N B f1 f2 r n. induction n as [|n IH]; intros j x E; cbn [cellv];
    (destruct (Nat.ltb j pc); [reflexivity|]); (destruct (_ && _); [|reflexivity]);
    (destruct (pend_at _ _ _ _ _ _ _); [reflexivity|]); (destruct (hpend_at _ _ _ _ _ _ _); [reflexivity|]); [apply E; lia|].
  destruct (B j); [|apply E; lia]. destruct (fbinder p c r j x) as [b|] eqn:Fb; [|apply E; lia].
  pose proof (fbinder_lt _ _ _ _ _ _ Fb). f_equal. apply IH. intros b' y L. apply E. lia.
Qed.

Lemma slotv_f : forall p c cc pc N B f1 f2 r j, (forall b y, b <= j -> f1 b y = f2 b y) ->
  slotv p c cc pc N B f1 r j = slotv p c cc pc N B f2 r j.
Proof.
  intros p c cc pc N B f1 f2 r j E. unfold slotv. destruct (Nat.ltb j pc); auto. destruct (_ && _); auto.
  assert (FB : fbit f1 (ins p c j r) j = fbit f2 (ins p c j r) j) by (unfold fbit; rewrite E; auto).
  destruct (pend_at _ _ _ _ _ _ _); auto. destruct (hpend_at _ _ _ _ _ _ _); [rewrite FB; reflexivity|].
  cbv zeta. rewrite FB. erewrite map_ext; [reflexivity|]. intros x. apply cellv_f. auto.
Qed.

Lemma creg_f_agree : forall p c cc pc N B f1 f2 J, wf p -> pend_ok cc pc -> (forall b y, b < J -> f1 b y = f2 b y) ->
  agree (creg p c cc pc N B f1) (creg p c cc pc N B f2) J.
Proof.
  intros p c cc pc N B f1 f2 J W PO A j. induction j as [j IH] using lt_wf_ind. intros Lj.
  rewrite (creg_fix p W c cc pc N B f1 j PO), (creg_fix p W c cc pc N B f2 j PO).
  rewrite (slotv_agree p W c cc pc N B f1 (creg p c cc pc N B f1) (creg p c cc pc N B f2) j PO).
  - apply slotv_f. intros b y L. apply A. lia.
  - intros i Li. apply IH; lia.
Qed.
