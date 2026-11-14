(* Model2: the accesses of any run, ordered by programme order and by
   coherence in each cell, replayed as an interleaving. The general part of
   MIFSC, over the slots a reach (STEP has) passed. *)
From Stdlib Require Import Arith Lia List Bool Permutation Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO MIPComp M2Lit MIPNeg M2SC M2SCx MIReplay M2Ev Topo.
Require Import M2Iface.

Section Iface.
Context `{IFM : Model}.

Definition fenced (p : prog) : Prop :=
  forall c k r, isacc (ins p c k r) = true ->
    1 <= k /\ ins p c (k - 1) r = IFn FFull /\ ins p c (S k) r = IFn FFull.

(* ---------- positions in a history, from 1; 0 = absent ---------- *)
Fixpoint pos (y : nat) (l : list nat) : nat :=
  match l with
  | [] => 0
  | z :: t => if Nat.eqb z y then 1 else match pos y t with 0 => 0 | n => S n end
  end.

Lemma pos_in : forall l y, In y l -> 1 <= pos y l <= length l.
Proof.
  induction l as [|z t IH]; intros y I; [destruct I|]. simpl.
  destruct (Nat.eqb_spec z y); [lia|]. destruct I as [->|I]; [congruence|].
  specialize (IH y I). destruct (pos y t); lia.
Qed.

Lemma pos_app_in : forall l1 l2 y, In y l1 -> pos y (l1 ++ l2) = pos y l1.
Proof.
  induction l1 as [|z t IH]; intros l2 y I; [destruct I|]. simpl.
  destruct (Nat.eqb_spec z y); auto. destruct I as [->|I]; [congruence|]. rewrite IH; auto.
Qed.

Lemma pos_app_out : forall l1 l2 y, ~ In y l1 -> In y l2 -> pos y (l1 ++ l2) = length l1 + pos y l2.
Proof.
  induction l1 as [|z t IH]; intros l2 y N I; simpl; auto.
  destruct (Nat.eqb_spec z y) as [E|E]; [exfalso; apply N; left; auto|].
  rewrite IH by (first [exact I | intros I'; apply N; right; auto]). pose proof (pos_in l2 y I). destruct (length t + pos y l2) eqn:Z; lia.
Qed.

Lemma pos_older : forall h a b, NoDup (ids h) -> older h a b -> pos a (ids h) < pos b (ids h).
Proof.
  intros h a b N O. apply older_split in O. destruct O as (l1 & l2 & E & A & B). rewrite E in N |- *.
  assert (Nb : ~ In b l1) by (intros I; eapply nodup_app_disj; eauto).
  rewrite pos_app_in by auto. rewrite pos_app_out by auto. pose proof (pos_in l1 a A). pose proof (pos_in l2 b B). lia.
Qed.

Lemma pos_inj : forall h a b, NoDup (ids h) -> In a (ids h) -> In b (ids h) -> a <> b -> pos a (ids h) <> pos b (ids h).
Proof.
  intros h a b N A B D. destruct (older_total h a b A B D) as [O|O];
    [pose proof (pos_older h a b N O)|pose proof (pos_older h b a N O)]; lia.
Qed.

Lemma pos_lt_older : forall h a b, NoDup (ids h) -> In a (ids h) -> In b (ids h) ->
  pos a (ids h) < pos b (ids h) -> older h a b.
Proof.
  intros h a b N A B L. destruct (Nat.eq_dec a b) as [->|D]; [lia|].
  destruct (older_total h a b A B D) as [O|O]; auto. pose proof (pos_older h b a N O). lia.
Qed.

Definition inb (x : nat) (l : list nat) : bool := existsb (Nat.eqb x) l.
Lemma inb_In : forall x l, inb x l = true <-> In x l.
Proof.
  intros x l. unfold inb. rewrite existsb_exists. split.
  - intros (y & I & E). apply Nat.eqb_eq in E. subst. auto.
  - intros I. exists x. rewrite Nat.eqb_refl. auto.
Qed.

Set Default Proof Using "All".
Section F.
Variable p : prog.
Variable s : M2Model.st.
Hypothesis R : reach (STEP p) s.
Hypothesis W : wf p.

Local Abbreviation bt := (bt s).
Local Abbreviation rrg := (rrg s).

Definition node := (nat * nat)%type.
Definition iof (n : node) : instr := ins p (fst n) (snd n) (rrg (fst n)).
(* an access the reach (STEP has) passed, whose condition held *)
Definition acc (n : node) : bool := Nat.ltb (snd n) (pcs s (fst n)) && isacc (iof n) && icond (iof n) (rrg (fst n)).
Definition cells (n : node) : list cell := icells (iof n).
Definition rd (n : node) : bool := xload (iof n) (rrg (fst n)).
Definition T (n : node) : nat := bt (fst n) (snd n).
Definition eofn (n : node) : option oev := ent s (T n).
Definition wr (n : node) : bool := match eofn n with Some E => ew E | None => false end.
Definition srcx (n : node) (x : cell) : option nat := match eofn n with Some E => erf E x | None => None end.
Definition hx (x : cell) : list nat := ids (hs s x).
Definition ixs (n : node) (x : cell) : nat := match srcx n x with Some y => pos y (hx x) | None => 0 end.
Definition ixw (n : node) (x : cell) : nat := pos (T n) (hx x).

Definition neqb (a b : node) : bool := negb (Nat.eqb (fst a) (fst b) && Nat.eqb (snd a) (snd b)).
Definition rfx (x : cell) (a b : node) : bool :=
  wr a && rd b && match srcx b x with Some y => Nat.eqb y (T a) | None => false end.
Definition cox (x : cell) (a b : node) : bool := wr a && wr b && Nat.ltb (ixw a x) (ixw b x).
Definition frx (x : cell) (a b : node) : bool := rd a && wr b && neqb a b && Nat.ltb (ixs a x) (ixw b x).
Definition combx (x : cell) (a b : node) : bool :=
  acc a && acc b && inb x (cells a) && inb x (cells b) && (rfx x a b || cox x a b || frx x a b).
Definition comb (a b : node) : bool := existsb (fun x => combx x a b) (cells a).
Definition pob (a b : node) : bool := Nat.eqb (fst a) (fst b) && Nat.ltb (snd a) (snd b).
Definition Rb (a b : node) : bool := pob a b || comb a b.

Lemma comb_x : forall a b, comb a b = true <-> exists x, combx x a b = true.
Proof.
  intros a b. unfold comb. rewrite existsb_exists. split; [intros (x & _ & H); eauto|].
  intros (x & H). exists x. split; auto. unfold combx in H.
  repeat (apply andb_prop in H; destruct H as [H ?]). apply inb_In. auto.
Qed.

(* ---------- one access ---------- *)
Lemma acc_lt : forall n, acc n = true -> snd n < pcs s (fst n).
Proof. intros n A. unfold acc in A. do 2 apply andb_prop in A as [A _]. apply Nat.ltb_lt. exact A. Qed.

Lemma node_E : forall n, acc n = true -> exists E,
  isacc (iof n) = true /\ icond (iof n) (rrg (fst n)) = true /\ RE s (fst n) (snd n) E /\
  einstr p s E = iof n /\ eofn n = Some E.
Proof.
  intros [c k] A. unfold acc in A. apply andb_prop in A. destruct A as [A1 A2].
  apply andb_prop in A1. destruct A1 as [Lp A1]. apply Nat.ltb_lt in Lp. simpl in *.
  destruct (n_ent p s R W c k (iof (c, k)) eq_refl Lp ltac:(unfold executes; rewrite A1; exact A2)) as (E & RE0 & Ei).
  exists E. split; auto. split; auto. split; auto. split; auto.
  unfold eofn, T. simpl. destruct RE0 as (Ae & _). exact Ae.
Qed.

Lemma acc_rd_wr : forall n, acc n = true -> rd n = false -> wr n = true.
Proof.
  intros n A Rd. destruct (node_E n A) as (E & Ia & Co & RE0 & Ei & Eo).
  assert (Lp : snd n < pcs s (fst n)) by (unfold acc in A; apply andb_prop in A as [A _]; apply andb_prop in A as [A _]; apply Nat.ltb_lt; exact A).
  unfold wr. rewrite Eo. rewrite (n_ew p s R W _ _ _ E eq_refl RE0 Ei Lp).
  unfold rd, xload in Rd. unfold iof in *. rewrite Co in Rd |- *.
  destruct (ins p (fst n) (snd n) (rrg (fst n))); simpl in *; try discriminate; reflexivity.
Qed.

Lemma wr_hist : forall n x, acc n = true -> wr n = true -> In x (cells n) -> In (T n) (hx x).
Proof.
  intros n x A Wn Ix. destruct (node_E n A) as (E & Ia & Co & RE0 & Ei & Eo).
  unfold wr in Wn. rewrite Eo in Wn. unfold hx, cells in *.
  exact (proj1 (n_wr p s R W _ _ _ x E eq_refl RE0 Ei Wn Ix)).
Qed.

Lemma rd_src : forall n x y, acc n = true -> srcx n x = Some y -> In y (hx x) /\ In x (cells n) /\ y < T n.
Proof.
  intros n x y A Sy. destruct (node_E n A) as (E & Ia & Co & RE0 & Ei & Eo).
  unfold srcx in Sy. rewrite Eo in Sy. pose proof RE0 as (A1 & B1 & C1).
  destruct (j_rf p s (nI2 p s R W) _ E x y A1 Sy) as (Lt & _ & Ix & Hy).
  unfold hx, cells. rewrite Ei in Ix. refine (conj Hy (conj Ix _)).
  unfold T. rewrite <- (n_et p s R W _ _ E RE0). destruct (i_et p s (nI1 p s R W) _ E A1) as (Et & _). lia.
Qed.

Lemma bt_neq : forall a b, acc a = true -> acc b = true -> neqb a b = true -> T a <> T b.
Proof.
  intros [ca ka] [cb kb] A B N E. unfold T in E. simpl in *.
  destruct (node_E _ A) as (Ea & Ia & Ca & _). destruct (node_E _ B) as (Eb & Ib & Cb & _).
  assert (Xa : executes (iof (ca, ka)) (rrg ca) = true) by (unfold executes; simpl in Ia; rewrite Ia; exact Ca).
  assert (Xb : executes (iof (cb, kb)) (rrg cb) = true) by (unfold executes; simpl in Ib; rewrite Ib; exact Cb).
  destruct (bt_inj p s R W ca ka cb kb _ _ (n_insr p s R W ca ka _ eq_refl (acc_lt _ A)) (n_insr p s R W cb kb _ eq_refl (acc_lt _ B)) Xa Xb E).
  subst. unfold neqb in N. simpl in N. rewrite !Nat.eqb_refl in N. discriminate.
Qed.

(* ---------- the instructions of the run ---------- *)
Definition L : list node := map (fun t => (fst (fst t), snd (fst t))) (cm s).

Lemma L_in : forall c j, In (c, j) L <-> j < pcs s c.
Proof.
  intros c j. rewrite (i_cmA p s (nI1 p s R W) c j). unfold L. rewrite in_map_iff. split.
  - intros ([[c' j'] tau] & E & I). simpl in E. injection E as <- <-. eauto.
  - intros (tau & I). exists (c, j, tau). auto.
Qed.

Lemma L_nodup : NoDup L.
Proof.
  apply NoDup_nth_error. intros i j Li E. unfold L in *. rewrite !nth_error_map in E. rewrite length_map in Li.
  destruct (nth_error (cm s) i) as [[[c1 j1] t1]|] eqn:Q1; [|apply nth_error_None in Q1; lia].
  destruct (nth_error (cm s) j) as [[[c2 j2] t2]|] eqn:Q2; [|discriminate].
  simpl in E. injection E as <- <-.
  destruct (Nat.lt_trichotomy i j) as [Lt|[Eq|Gt]]; auto.
  - pose proof (i_cmB p s (nI1 p s R W) i j c1 j1 j1 t1 t2 Lt Q1 Q2). lia.
  - pose proof (i_cmB p s (nI1 p s R W) j i c1 j1 j1 t2 t1 Gt Q2 Q1). lia.
Qed.

Lemma node_eq_dec : forall a b : node, {a = b} + {a <> b}.
Proof. decide equality; apply Nat.eq_dec. Qed.

(* ---------- replaying an order that respects the relation ---------- *)
Section Ord.
Variable ord : list node.
Hypothesis Pord : Permutation L ord.
(* the order respects programme order, and coherence on the cells CPc picks *)
Variable CPc : cell -> bool.
Hypothesis OordP : forall i j a b, nth_error ord i = Some a -> nth_error ord j = Some b -> pob a b = true -> i < j.
Hypothesis OordC : forall i j a b x, nth_error ord i = Some a -> nth_error ord j = Some b -> combx x a b = true ->
  CPc x = true -> i < j.

Lemma ordA : forall c j, j < pcs s c <-> In (c, j) ord.
Proof.
  intros c j. rewrite <- L_in. split; intros H; [eapply Permutation_in; eauto|].
  eapply Permutation_in; [apply Permutation_sym; eauto|auto].
Qed.

Lemma ord_nodup : NoDup ord.
Proof. eapply Permutation_NoDup; [exact Pord|apply L_nodup]. Qed.

Lemma ordB : forall n1 n2 c j1 j2, n1 < n2 -> nth_error ord n1 = Some (c, j1) -> nth_error ord n2 = Some (c, j2) -> j1 < j2.
Proof.
  intros n1 n2 c j1 j2 L1 Q1 Q2. destruct (Nat.lt_trichotomy j1 j2) as [Lt|[->|Gt]]; auto.
  - exfalso. pose proof ord_nodup as N. rewrite NoDup_nth_error in N.
    assert (n1 = n2) by (apply N; [apply nth_error_Some; congruence|congruence]). lia.
  - exfalso. assert (pob (c, j2) (c, j1) = true) by (unfold pob; simpl; rewrite Nat.eqb_refl; apply Nat.ltb_lt in Gt; rewrite Gt; reflexivity).
    pose proof (OordP n2 n1 _ _ Q2 Q1 H). lia.
Qed.

Definition corr' (n : nat) (l : list sev) (g : sst) : Prop :=
  srun p l g /\ length l = n /\
  (forall q e, nth_error l q = Some e -> nth_error ord q = Some (sx e, sk e)) /\
  (forall c j, j < sp g c -> sr g c j = rrg c j).

Lemma corr_sp' : forall n l g, corr' n l g -> forall c j,
  j < sp g c <-> exists q, q < n /\ nth_error ord q = Some (c, j).
Proof.
  intros n l g (A & B & C & D) c j. rewrite (srun_pos p W l g A c j). split.
  - intros (q & e & E & <- & <-). exists q. split; [rewrite <- B; apply nth_error_Some; congruence|]. apply C. auto.
  - intros (q & Q & Tq). destruct (nth_error l q) as [e|] eqn:E.
    + exists q, e. pose proof (C q e E) as T'. rewrite Tq in T'. injection T' as <- <-. auto.
    + apply nth_error_None in E. lia.
Qed.

Lemma sp_at' : forall n l g c k, corr' n l g -> nth_error ord n = Some (c, k) -> sp g c = k.
Proof.
  intros n l g c k H Tn. apply nat_iff_eq. intros j. rewrite (corr_sp' n l g H c j). split.
  - intros (q & Q & T'). apply (ordB q n c j k Q T' Tn).
  - intros Hj.
    assert (Kp : k < pcs s c) by (apply ordA; eapply nth_error_In; eauto).
    assert (Ij : In (c, j) ord) by (apply ordA; lia).
    apply In_nth_error in Ij. destruct Ij as (q & T'). exists q. split; auto.
    destruct (Nat.lt_trichotomy q n) as [Lq|[Lq|Lq]]; auto.
    * subst q. pose proof (eq_trans (eq_sym Tn) T') as Z. injection Z as Z. lia.
    * pose proof (ordB n q c k j Lq Tn T'). lia.
Qed.

Lemma ord_insr : forall q c k, nth_error ord q = Some (c, k) -> exists i, insr p s c k = Some i.
Proof.
  intros q c k Tq. assert (Kp : k < pcs s c) by (apply ordA; eapply nth_error_In; eauto).
  exists (ins p c k (rrg c)). apply (insr_of p s R W). exact Kp.
Qed.

(* a CAS whose verdict is a success read its expected value *)
Lemma vok_val' : forall c k i, insr p s c k = Some i -> xload i (rrg c) = true -> is_cas i = true ->
  vok (rrg c k) = true -> vv (rrg c k) = cexp i (rrg c).
Proof.
  intros c k i Hi X Ci Vr. pose proof (insr_lt p s R W c k i Hi) as Lk.
  pose proof (I1 p s R W) as Ia. pose proof (I2 p s R W) as Ib.
  unfold rrg, MIPComp.rrg in *.
  destruct (oc (cs s c) k) as [tk|] eqn:Ok.
  - destruct (i_oc p s Ia c k tk Ok) as (en & E1 & E2 & E3).
    assert (E4 : einstr p s en = i)
      by (rewrite (einstr_ins p s R W _ en E1 ltac:(rewrite E2, E3; exact Lk)), E2, E3; apply (insr_ins p s R W c k i Hi)).
    pose proof (oc_eh p s c k tk en Ia Ok E1 E2 E3) as Eh.
    assert (Xe : xload (einstr p s en) (rgof s en) = true) by (rewrite E4; unfold rgof; rewrite E2; exact X).
    pose proof (j_ok p s Ib tk en E1 Eh ltac:(rewrite E4; exact Ci) Xe) as J. rewrite E2, E3, Vr in J.
    destruct (j_ew p s Ib tk en i E1 E4) as [Wq _]. rewrite <- J in Wq. symmetry in Wq.
    apply andb_prop in Wq as [_ Wq]. rewrite Ci in Wq. simpl in Wq. rewrite andb_true_r in Wq. apply Nat.eqb_eq in Wq.
    destruct (j_val p s Ib tk en i E1 E4) as [V _]. rewrite E4 in Xe. specialize (V Xe). rewrite E2, E3, (rval_cas _ _ Ci) in V.
    rewrite V, Wq. unfold rgof. rewrite E2. reflexivity.
  - exfalso. destruct (oh (cs s c) k) as [th|] eqn:Oh.
    + rewrite (i_halfv p s Ia c k th Ok Oh Lk) in Vr. discriminate.
    + rewrite (i_rg0 p s Ia c k Ok Oh) in Vr. discriminate.
Qed.

Lemma replay_step' : forall n l g c k i, corr' n l g -> nth_error ord n = Some (c, k) ->
  insr p s c k = Some i ->
  exists e g', sstep p g e g' /\ sx e = c /\ sk e = k /\
    ((xload i (rrg c) = true -> enc (map (sm g) (icells i)) = rval i (rrg c k)) -> corr' (S n) (l ++ [e]) g').
Proof.
  intros n l g c k i H Tn Hi. pose proof (sp_at' n l g c k H Tn) as Sp.
  destruct H as (A & B & C & D).
  destruct (det_bt p s R W c k i (sr g c) Hi) as [Ins Fa]. { intros j' Hj'. apply D. lia. }
  set (bs0 := fun (g0 : sst) (c0 : nat) => vok (rrg c0 (sp g0 c0))).
  set (e := fst (snext p bs0 g c)). set (g' := snd (snext p bs0 g c)).
  assert (St : sstep p g e g') by apply snext_step.
  assert (Ex : sx e = c) by apply snext_x.
  destruct (sstep_shape p W g e g' St) as (i' & Hi' & _ & Hk & Hsp & Hr & _).
  rewrite Ex in *. rewrite Sp in Hk. rewrite Hk in Hi'. rewrite Ins in Hi'. subst i'.
  assert (Xl : xload i (sr g c) = xload i (rrg c)) by (unfold xload; rewrite (ieval_cond _ _ _ Fa); auto).
  assert (Rk : sr g' c k = (if xload i (rrg c) then areg i (Nat.eqb (enc (map (sm g) (icells i))) (cexp i (rrg c)) && vok (rrg c k))
                                                     (enc (map (sm g) (icells i))) else 0)).
  { unfold g'. rewrite <- Sp. rewrite snext_reg. cbv zeta. rewrite Sp, Ins, Xl, (cexp_ieval _ _ _ Fa).
    unfold bs0. rewrite Sp. destruct (xload i (rrg c)); auto.
    apply (srun_regs0 p W l g A). lia. }
  exists e, g'. split; auto. split; auto. split; [lia|].
  intros M. split; [econstructor; eauto|]. split; [rewrite length_app; simpl; lia|]. split.
  - intros q e' E. destruct (Nat.lt_ge_cases q (length l)).
    + rewrite nth_error_app1 in E by auto. auto.
    + rewrite nth_error_app2 in E by auto. destruct (q - length l) as [|z] eqn:Z; [|destruct z; discriminate].
      simpl in E. injection E as <-. assert (q = n) by lia. subst q. rewrite Ex, Hk. auto.
  - intros c' j Hj. rewrite Hsp in Hj. unfold upd in Hj.
    destruct (Nat.eq_dec c' c) as [->|N].
    + rewrite Nat.eqb_refl in Hj. destruct (Nat.eq_dec j k) as [->|Nj].
      * rewrite Rk. destruct (xload i (rrg c)) eqn:X.
        { specialize (M eq_refl). destruct (is_cas i) eqn:Ci.
          - rewrite (areg_cas _ _ _ Ci). rewrite (rval_cas _ _ Ci) in M. rewrite M.
            destruct (vok (rrg c k)) eqn:Vr.
            + rewrite (vok_val' c k i Hi X Ci Vr), Nat.eqb_refl. simpl. rewrite <- (vok_val' c k i Hi X Ci Vr).
              rewrite <- Vr. apply vd_split.
            + rewrite andb_false_r. rewrite <- (vd_split (rrg c k)) at 2. rewrite Vr. reflexivity.
          - assert (Ar : forall b v, areg i b v = v) by (intros b v; destruct i; simpl in Ci; try discriminate; reflexivity).
            assert (Rr : forall a, rval i a = a) by (intros a; destruct i; simpl in Ci; try discriminate; reflexivity).
            rewrite Ar, M, Rr. reflexivity. }
        destruct (oc (cs s c) k) as [tk|] eqn:Ok.
        -- destruct (i_oc p s (I1 p s R W) c k tk Ok) as (en & E1 & E2 & E3).
           assert (E4 : einstr p s en = i)
             by (rewrite (einstr_ins p s R W _ en E1 ltac:(rewrite E2, E3; apply (insr_lt p s R W c k i Hi))), E2, E3;
                 apply (insr_ins p s R W c k i Hi)).
           destruct (j_val p s (I2 p s R W) tk en i E1 E4) as [_ V]. unfold rgof in V. rewrite E2, E3 in V.
           symmetry. apply (proj1 (V X)).
        -- symmetry. apply (i_rg0 p s (I1 p s R W) c k Ok). destruct (oh (cs s c) k) as [th|] eqn:Oh; [|reflexivity].
           exfalso. pose proof (insr_lt p s R W c k i Hi) as Lk. destruct (i_halfp p s (I1 p s R W) c k th Ok Oh Lk) as (F & _).
           destruct (proj1 (i_cmA p s (I1 p s R W) c k) Lk) as (tau0 & T0).
           rewrite (proj2 (i_set p s (I1 p s R W) c k tau0 T0)) in F. pose proof (insr_ins p s R W c k i Hi) as Ii.
           unfold rrg in Ii.  try unfold MIPComp.rrg in Ii. rewrite Ii in F.
           destruct i as [| |m0 x0 c0 e0 n0| |]; simpl in F; try discriminate. apply andb_true_iff in F as [C0 _].
           unfold xload, icond in X; simpl in X. try unfold rrg in X. try unfold MIPComp.rrg in X. rewrite C0 in X. discriminate.
      * rewrite Hr by (right; rewrite Hk; lia). apply D. lia.
    + apply Nat.eqb_neq in N as N'. rewrite N' in Hj. rewrite Hr by (left; auto). apply D. auto.
Qed.

Lemma replay' : forall n, n <= length ord ->
  (exists l g, corr' n l g) \/
  (exists n0 l g c k i, n0 < n /\ corr' n0 l g /\ nth_error ord n0 = Some (c, k) /\
     insr p s c k = Some i /\ xload i (rrg c) = true /\ enc (map (sm g) (icells i)) <> rval i (rrg c k)).
Proof.
  induction n as [|n IH]; intros Hn.
  - left. exists [], ssinit. split; [constructor|]. split; [reflexivity|]. split.
    + intros q e E. destruct q; discriminate.
    + intros c j Hj. simpl in Hj. lia.
  - destruct (IH ltac:(lia)) as [(l & g & H)|(n0 & l & g & c & k & i & A)].
    + destruct (nth_error ord n) as [[c k]|] eqn:Tn; [|apply nth_error_None in Tn; lia].
      destruct (ord_insr n c k Tn) as (i & Hi).
      destruct (replay_step' n l g c k i H Tn Hi) as (e & g' & St & Ex & Ek & Next).
      destruct (xload i (rrg c)) eqn:X.
      * destruct (Nat.eq_dec (enc (map (sm g) (icells i))) (rval i (rrg c k))) as [M|M].
        -- left. exists (l ++ [e]), g'. apply Next. auto.
        -- right. exists n, l, g, c, k, i. refine (conj _ (conj H (conj Tn (conj Hi (conj X M))))). lia.
      * left. exists (l ++ [e]), g'. apply Next. discriminate.
    + right. exists n0, l, g, c, k, i. destruct A as (A1 & A2). split; [lia|auto].
Qed.

(* ---------- interleaving writes are the run's writes ---------- *)
Lemma ent_iof : forall c k, k < pcs s c -> executes (iof (c, k)) (rrg c) = true -> exists E, eofn (c, k) = Some E /\
  ew E = (is_store (iof (c, k)) && icond (iof (c, k)) (rrg c) &&
          (negb (is_cas (iof (c, k))) || vok (rg (cs s c) k))).
Proof.
  intros c k NN X. destruct (n_ent p s R W c k (iof (c, k)) eq_refl NN X) as (E & RE0 & Ei).
  exists E. split; [destruct RE0 as (A1 & _); exact A1|].
  apply (n_ew p s R W c k _ E eq_refl RE0 Ei NN).
Qed.

Lemma scw_eq : forall n l g q e x, corr' n l g -> nth_error l q = Some e ->
  writes_x e x = (acc (sx e, sk e) && wr (sx e, sk e) && inb x (cells (sx e, sk e))).
Proof.
  intros n l g q e x (A & B & C & D) Q.
  destruct (srun_ev p W l g A q e Q) as (i & Hi & Lk & Sh).
  set (c := sx e) in *. set (k := sk e) in *.
  assert (AG : forall j, j < k -> sr g c j = rrg c j) by (intros j Lj; apply D; lia).
  assert (Hi' : iof (c, k) = i) by (unfold iof; simpl; rewrite <- Hi; symmetry; apply wf_ins; auto).
  assert (IEv : ieval i (sr g c) = ieval i (rrg c)) by (apply (wf_ieval p c k i (sr g c) (rrg c) W Hi); auto).
  assert (Rk : sr g c k = rrg c k) by (apply D; auto).
  rewrite (evshape_ext i (sr g c) (rrg c) k IEv Rk) in Sh.
  assert (Sa : sacc e = fst (evshape i (rrg c) k)) by (rewrite <- Sh; reflexivity).
  unfold writes_x. rewrite Sa. unfold acc, wr, cells.
  assert (Lp : k < pcs s c) by (apply ordA; eapply nth_error_In; apply C; eauto).
  cbn [fst snd]. rewrite (proj2 (Nat.ltb_lt k (pcs s c)) Lp). cbn [andb].
  assert (EI : forall i0, i = i0 -> i0 <> INop -> executes i0 (rrg c) = true -> exists E, eofn (c, k) = Some E /\
            ew E = (is_store i0 && icond i0 (rrg c) && (negb (is_cas i0) || vok (rg (cs s c) k)))).
  { intros i0 E0 NN X. subst i0. rewrite <- Hi' in *. apply ent_iof; [|exact X]. exact Lp. }
  rewrite Hi'.
  destruct i as [md y' cn|md y' cn v|md y' cn e0 n0|f|].
  - destruct (cn (rrg c)) eqn:Cn; [|simpl; unfold icond, ieval; simpl; rewrite Cn; reflexivity].
    destruct (EI _ eq_refl ltac:(discriminate) ltac:(unfold executes, icond, ieval; simpl; exact Cn)) as (E & Eo & Ew). rewrite Eo, Ew. simpl.
    unfold icond, ieval; simpl. rewrite Cn; simpl; rewrite ?andb_false_r; reflexivity.
  - destruct (cn (rrg c)) eqn:Cn; [|simpl; unfold icond, ieval; simpl; rewrite Cn; reflexivity].
    destruct (EI _ eq_refl ltac:(discriminate) ltac:(unfold executes, icond, ieval; simpl; exact Cn)) as (E & Eo & Ew). rewrite Eo, Ew. simpl.
    unfold icond, ieval; simpl. rewrite Cn; simpl; reflexivity.
  - destruct (cn (rrg c)) eqn:Cn; [|simpl; unfold icond, ieval; simpl; rewrite Cn; reflexivity].
    destruct (EI _ eq_refl ltac:(discriminate) ltac:(unfold executes, icond, ieval; simpl; exact Cn)) as (E & Eo & Ew). rewrite Eo, Ew. simpl.
    unfold icond, ieval, eval_e; simpl. rewrite Cn; simpl.
    unfold rrg, MIPComp.rrg. destruct (vok (rg (cs s c) k)); reflexivity.
  - simpl. destruct f; reflexivity.
  - reflexivity.
Qed.

Lemma node_pos : forall w, In w L -> exists q, nth_error ord q = Some w.
Proof. intros w I. apply In_nth_error. eapply Permutation_in; eauto. Qed.

Lemma ev_at : forall n l g q, corr' n l g -> q < n -> exists e, nth_error l q = Some e /\ nth_error ord q = Some (sx e, sk e).
Proof.
  intros n l g q (A & B & C & D) Lq. destruct (nth_error l q) as [e|] eqn:E; [eauto|].
  apply nth_error_None in E. lia.
Qed.

Lemma pos_unique : forall q1 q2 w, nth_error ord q1 = Some w -> nth_error ord q2 = Some w -> q1 = q2.
Proof.
  intros q1 q2 w Q1 Q2. pose proof ord_nodup as N. rewrite NoDup_nth_error in N.
  apply N; [apply nth_error_Some; congruence|congruence].
Qed.

(* the writer of a write id: a node of the order, or a pending early access *)
Lemma writer_node : forall x y, In y (ids (hs s x)) ->
  (exists w, acc w = true /\ wr w = true /\ In x (cells w) /\ T w = y /\
    wv s y x = cval (cells w) (wvals (iof w) (rrg (fst w))) x /\ In w L) \/
  (exists c k E, RE s c k E /\ ew E = true /\ pcs s c <= k).
Proof.
  intros x y Iy. destruct (n_wr_of p s R W x y Iy) as (c0 & k0 & i0 & E0 & Ei0 & RE0 & Wt0 & Ic0 & Wv0 & B0 & Pi).
  destruct (Nat.lt_ge_cases k0 (pcs s c0)) as [Lk|Lk]; [left|right; exists c0, k0, E0; split; [auto|split; [auto|lia]]].
  specialize (Pi Lk) as H0.
  pose proof (n_ew p s R W c0 k0 i0 E0 H0 RE0 Ei0 Lk) as Ew. rewrite Wt0 in Ew.
  exists (c0, k0). unfold acc, wr, cells, eofn, iof, T. simpl. rewrite H0. destruct RE0 as (A1 & _).
  rewrite A1, Wt0, (proj2 (Nat.ltb_lt _ _) Lk).
  symmetry in Ew. apply andb_prop in Ew. destruct Ew as [Ew _]. apply andb_prop in Ew. destruct Ew as [St Co].
  split; [rewrite Co, andb_true_r; destruct i0; simpl in St; try discriminate; reflexivity|].
  split; auto. split; auto. split; [exact B0|]. split; [exact Wv0|].
  destruct (cm_has p s R W c0 k0 Lk) as (q & tau & Tq).
  unfold L. apply in_map_iff. exists (c0, k0, tau). split; auto. eapply nth_error_In; eauto.
Qed.

Lemma write_value : forall n l g q e, corr' n l g -> nth_error l q = Some e ->
  forall i', ins p (sx e) (sk e) (sr g (sx e)) = i' -> wvals i' (sr g (sx e)) = wvals (iof (sx e, sk e)) (rrg (sx e)).
Proof.
  intros n l g q e (A & B & C & D) Q i' Hi.
  destruct (srun_ev p W l g A q e Q) as (i & Hi2 & Lk & _). rewrite Hi in Hi2. subst i.
  assert (AG : forall j, j < sk e -> sr g (sx e) j = rrg (sx e) j) by (intros j Lj; apply D; lia).
  assert (Hi' : iof (sx e, sk e) = i') by (unfold iof; simpl; rewrite <- Hi; symmetry; apply wf_ins; auto).
  rewrite Hi'. apply ieval_wvals. apply (wf_ieval p (sx e) (sk e) i' _ _ W Hi). auto.
Qed.

End Ord.

End F.

End Iface.
