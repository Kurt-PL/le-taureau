(* Every access between guard() fences: sequential consistency for every
   finished reach (STEP that) has no access before itself (evok). Accesses may cover
   several cells.

   Proof: the accesses of the run, ordered by programme order and by
   coherence in each cell (reads-from, write order, from-read), have no
   cycle: every such edge is a path of the run's event graph, except
   programme order out of a read, which the guard() after it replaces by
   what the read took. Any order of the instructions that respects this
   relation, replayed as an interleaving, reads what the run read. *)
From Stdlib Require Import Arith Lia List Bool Permutation Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO MIComp M2Lit MINeg M2SC M2SCx MIReplay M2Ev Topo.
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
Hypothesis CP : done p s.
Hypothesis W : wf p.

Local Abbreviation bt := (bt s).
Local Abbreviation rrg := (rrg s).

Definition node := (nat * nat)%type.
Definition iof (n : node) : instr := ins p (fst n) (snd n) (rrg (fst n)).
Definition acc (n : node) : bool := isacc (iof n) && icond (iof n) (rrg (fst n)).
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
Lemma node_E : forall n, acc n = true -> exists E,
  isacc (iof n) = true /\ icond (iof n) (rrg (fst n)) = true /\ RE s (fst n) (snd n) E /\
  einstr p s E = iof n /\ eofn n = Some E.
Proof.
  intros [c k] A. unfold acc in A. apply andb_prop in A. destruct A as [A1 A2]. simpl in *.
  assert (NN : iof (c, k) <> INop) by (intros E; rewrite E in A1; discriminate).
  destruct (n_ent p s R CP W c k (iof (c, k)) eq_refl NN ltac:(unfold executes; rewrite A1; exact A2)) as (E & RE0 & Ei).
  exists E. split; auto. split; auto. split; auto. split; auto.
  unfold eofn, T. simpl. destruct RE0 as (Ae & _). exact Ae.
Qed.

Lemma acc_rd_wr : forall n, acc n = true -> rd n = false -> wr n = true.
Proof.
  intros n A Rd. destruct (node_E n A) as (E & Ia & Co & RE0 & Ei & Eo).
  unfold wr. rewrite Eo. rewrite (n_ew p s R CP W _ _ _ E eq_refl RE0 Ei).
  unfold rd, xload in Rd. unfold iof in *. rewrite Co in Rd |- *.
  destruct (ins p (fst n) (snd n) (rrg (fst n))); simpl in *; try discriminate; reflexivity.
Qed.

Lemma wr_hist : forall n x, acc n = true -> wr n = true -> In x (cells n) -> In (T n) (hx x).
Proof.
  intros n x A Wn Ix. destruct (node_E n A) as (E & Ia & Co & RE0 & Ei & Eo).
  unfold wr in Wn. rewrite Eo in Wn. unfold hx, cells in *.
  exact (proj1 (n_wr p s R CP W _ _ _ x E eq_refl RE0 Ei Wn Ix)).
Qed.

Lemma rd_src : forall n x y, acc n = true -> srcx n x = Some y -> In y (hx x) /\ In x (cells n) /\ y < T n.
Proof.
  intros n x y A Sy. destruct (node_E n A) as (E & Ia & Co & RE0 & Ei & Eo).
  unfold srcx in Sy. rewrite Eo in Sy. pose proof RE0 as (A1 & B1 & C1).
  destruct (j_rf p s (nI2 p s R CP W) _ E x y A1 Sy) as (Lt & _ & Ix & Hy).
  unfold hx, cells. rewrite Ei in Ix. refine (conj Hy (conj Ix _)).
  unfold T. rewrite <- (n_et p s R CP W _ _ E RE0). destruct (i_et p s (nI1 p s R CP W) _ E A1) as (Et & _). lia.
Qed.

Lemma bt_neq : forall a b, acc a = true -> acc b = true -> neqb a b = true -> T a <> T b.
Proof.
  intros [ca ka] [cb kb] A B N E. unfold T in E. simpl in *.
  destruct (node_E _ A) as (Ea & Ia & Ca & _). destruct (node_E _ B) as (Eb & Ib & Cb & _).
  assert (Xa : executes (iof (ca, ka)) (rrg ca) = true) by (unfold executes; simpl in Ia; rewrite Ia; exact Ca).
  assert (Xb : executes (iof (cb, kb)) (rrg cb) = true) by (unfold executes; simpl in Ib; rewrite Ib; exact Cb).
  assert (Na : iof (ca, ka) <> INop) by (intros Z; rewrite Z in Ia; discriminate).
  assert (Nb : iof (cb, kb) <> INop) by (intros Z; rewrite Z in Ib; discriminate).
  destruct (bt_inj p s R CP W ca ka cb kb _ _ (n_insr p s R CP W ca ka _ eq_refl Na) (n_insr p s R CP W cb kb _ eq_refl Nb) Xa Xb E).
  subst. unfold neqb in N. simpl in N. rewrite !Nat.eqb_refl in N. discriminate.
Qed.

(* ---------- the instructions of the run ---------- *)
Definition L : list node := map (fun t => (fst (fst t), snd (fst t))) (cm s).

Lemma L_in : forall c j, In (c, j) L <-> j < pcs s c.
Proof.
  intros c j. rewrite (i_cmA p s (nI1 p s R CP W) c j). unfold L. rewrite in_map_iff. split.
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
  - pose proof (i_cmB p s (nI1 p s R CP W) i j c1 j1 j1 t1 t2 Lt Q1 Q2). lia.
  - pose proof (i_cmB p s (nI1 p s R CP W) j i c1 j1 j1 t2 t1 Gt Q2 Q1). lia.
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
  exists (ins p c k (rrg c)). apply (insr_pc p s R CP W). exact Kp.
Qed.

(* a CAS whose verdict is a success read its expected value *)
Lemma vok_val' : forall c k i, insr p s c k = Some i -> xload i (rrg c) = true -> is_cas i = true ->
  vok (rrg c k) = true -> vv (rrg c k) = cexp i (rrg c).
Proof.
  intros c k i Hi X Ci Vr. pose proof (insr_lt p s R CP W c k i Hi) as Lk.
  pose proof (I1 p s R CP W) as Ia. pose proof (I2 p s R CP W) as Ib.
  unfold rrg, MIComp.rrg in *.
  destruct (oc (cs s c) k) as [tk|] eqn:Ok.
  - destruct (i_oc p s Ia c k tk Ok) as (en & E1 & E2 & E3).
    assert (E4 : einstr p s en = i)
      by (rewrite (einstr_ins p s R CP W _ en E1), E2, E3; apply (insr_ins p s R CP W c k i Hi)).
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
  destruct (det_bt p s R CP W c k i (sr g c) Hi) as [Ins Fa]. { intros j' Hj'. apply D. lia. }
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
        -- destruct (i_oc p s (I1 p s R CP W) c k tk Ok) as (en & E1 & E2 & E3).
           assert (E4 : einstr p s en = i)
             by (rewrite (einstr_ins p s R CP W _ en E1), E2, E3; apply (insr_ins p s R CP W c k i Hi)).
           destruct (j_val p s (I2 p s R CP W) tk en i E1 E4) as [_ V]. unfold rgof in V. rewrite E2, E3 in V.
           symmetry. apply (proj1 (V X)).
        -- symmetry. apply (i_rg0 p s (I1 p s R CP W) c k Ok). destruct (oh (cs s c) k) as [th|] eqn:Oh; [|reflexivity].
           exfalso. pose proof (insr_lt p s R CP W c k i Hi) as Lk. destruct (i_halfp p s (I1 p s R CP W) c k th Ok Oh Lk) as (F & _).
           destruct (proj1 (i_cmA p s (I1 p s R CP W) c k) Lk) as (tau0 & T0).
           rewrite (proj2 (i_set p s (I1 p s R CP W) c k tau0 T0)) in F. pose proof (insr_ins p s R CP W c k i Hi) as Ii.
           unfold rrg in Ii. try unfold MIComp.rrg in Ii.  rewrite Ii in F.
           destruct i as [| |m0 x0 c0 e0 n0| |]; simpl in F; try discriminate. apply andb_true_iff in F as [C0 _].
           unfold xload, icond in X; simpl in X. try unfold rrg, MIComp.rrg in X. rewrite C0 in X. discriminate.
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
Lemma ent_iof : forall c k, iof (c, k) <> INop -> executes (iof (c, k)) (rrg c) = true -> exists E, eofn (c, k) = Some E /\
  ew E = (is_store (iof (c, k)) && icond (iof (c, k)) (rrg c) &&
          (negb (is_cas (iof (c, k))) || vok (rg (cs s c) k))).
Proof.
  intros c k NN X. destruct (n_ent p s R CP W c k (iof (c, k)) eq_refl NN X) as (E & RE0 & Ei).
  exists E. split; [destruct RE0 as (A1 & _); exact A1|].
  apply (n_ew p s R CP W c k _ E eq_refl RE0 Ei).
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
  assert (EI : forall i0, i = i0 -> i0 <> INop -> executes i0 (rrg c) = true -> exists E, eofn (c, k) = Some E /\
            ew E = (is_store i0 && icond i0 (rrg c) && (negb (is_cas i0) || vok (rg (cs s c) k)))).
  { intros i0 E0 NN X. subst i0. rewrite <- Hi' in *. apply ent_iof; [|exact X]. auto. }
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
    unfold rrg, MIComp.rrg. destruct (vok (rg (cs s c) k)); reflexivity.
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

(* a write of a cell's history, as a node of the order *)
Lemma writer_node : forall x y, In y (ids (hs s x)) ->
  exists w, acc w = true /\ wr w = true /\ In x (cells w) /\ T w = y /\
    wv s y x = cval (cells w) (wvals (iof w) (rrg (fst w))) x /\ In w L.
Proof.
  intros x y Iy. destruct (n_wr_of p s R CP W x y Iy) as (c0 & k0 & i0 & E0 & H0 & RE0 & Wt0 & Ic0 & Wv0 & B0).
  assert (Ei0 : einstr p s E0 = i0) by (destruct RE0 as (A' & B & C); rewrite (einstr_ins p s R CP W _ E0 A'), B, C; auto).
  pose proof (n_ew p s R CP W c0 k0 i0 E0 H0 RE0 Ei0) as Ew. rewrite Wt0 in Ew.
  exists (c0, k0). unfold acc, wr, cells, eofn, iof, T. simpl. rewrite H0. destruct RE0 as (A1 & _).
  rewrite A1, Wt0.
  symmetry in Ew. apply andb_prop in Ew. destruct Ew as [Ew _]. apply andb_prop in Ew. destruct Ew as [St Co].
  split; [rewrite Co, andb_true_r; destruct i0; simpl in St; try discriminate; reflexivity|].
  split; auto. split; auto. split; [exact B0|]. split; [exact Wv0|].
  destruct (cm_has p s R CP W c0 k0 ltac:(rewrite H0; intros Z; rewrite Z in St; discriminate)) as (q & tau & Tq).
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

Lemma nodiv_x : forall n0 l g c k i Eu x, corr' n0 l g -> nth_error ord n0 = Some (c, k) ->
  insr p s c k = Some i -> xload i (rrg c) = true -> eofn (c, k) = Some Eu -> In x (icells i) -> CPc x = true ->
  sm g x = rdv s (erf Eu) x.
Proof.
  intros n0 l g c k i Eu x Co Tn Hi X Eou Ix CPx.
  rewrite (insr_pc p s R CP W) in Hi by (apply ordA; eapply nth_error_In; eauto).
  injection Hi as Hi. set (u := (c, k)).
  assert (Iu : iof u = i) by exact Hi.
  assert (Au : acc u = true /\ rd u = true).
  { unfold acc, rd. rewrite Iu. unfold xload in X. apply andb_prop in X. destruct X as [Ld Cd].
    destruct i; simpl in Ld; try discriminate; simpl; split; auto. }
  destruct Au as [Au Ru].
  assert (Ixu : In x (cells u)) by (unfold cells; rewrite Iu; exact Ix).
  destruct Co as (A & B & C & D) eqn:Co'.
  destruct (srun_mem p W l g A x) as [M0 M1].
  assert (Su : srcx u x = erf Eu x) by (unfold srcx, u; rewrite Eou; reflexivity).
  assert (WN : forall q e, nth_error l q = Some e -> writes_x e x = true ->
            acc (sx e, sk e) = true /\ wr (sx e, sk e) = true /\ In x (cells (sx e, sk e)) /\ q < n0 /\
            nth_error ord q = Some (sx e, sk e) /\ neqb u (sx e, sk e) = true).
  { intros q e Q Wx. rewrite (scw_eq n0 l g q e x Co Q) in Wx.
    apply andb_prop in Wx. destruct Wx as [Wx Xe]. apply andb_prop in Wx. destruct Wx as [Ae We].
    apply inb_In in Xe. split; auto. split; auto. split; auto.
    assert (Lq : q < n0) by (rewrite <- B; apply nth_error_Some; congruence). split; auto.
    split; [apply C; auto|]. unfold neqb, u; simpl. destruct (Nat.eqb c (sx e) && Nat.eqb k (sk e)) eqn:Z; [|reflexivity].
    exfalso. apply andb_prop in Z. destruct Z as [Z1 Z2]. apply Nat.eqb_eq in Z1, Z2.
    assert (Eu' : (sx e, sk e) = u) by (unfold u; rewrite Z1, Z2; reflexivity).
    pose proof (pos_unique q n0 u ltac:(rewrite <- Eu'; apply C; exact Q) Tn). lia. }
  assert (NDx : NoDup (hx x)) by apply (n_nodup p s R CP W).
  unfold rdv. destruct (erf Eu x) as [y|] eqn:Ey.
  - destruct (rd_src u x y Au ltac:(rewrite Su; auto)) as (Iy & _ & _).
    destruct (writer_node x y Iy) as (w0 & Aw0 & Ww0 & Xw0 & Bw0 & Vw0 & Lw0).
    destruct (node_pos w0 Lw0) as (q0 & Q0).
    assert (Cw0 : combx x w0 u = true).
    { unfold combx, rfx. rewrite Aw0, Au, Ww0, Ru, Su, Bw0, Nat.eqb_refl.
      rewrite (proj2 (inb_In x _) Xw0), (proj2 (inb_In x _) Ixu). reflexivity. }
    pose proof (OordC q0 n0 w0 u x Q0 Tn Cw0 CPx) as L0.
    destruct (ev_at n0 l g q0 Co L0) as (e0 & E0 & O0). rewrite Q0 in O0. injection O0 as O0.
    assert (Wx0 : writes_x e0 x = true).
    { rewrite (scw_eq n0 l g q0 e0 x Co E0). rewrite <- O0, Aw0, Ww0, (proj2 (inb_In x _) Xw0). reflexivity. }
    destruct (lw l x) as [e|] eqn:LW; [|rewrite (lw_none l _ LW q0 e0 E0) in Wx0; discriminate].
    destruct (lw_spec l _ e LW) as (q & Q & Wx & Later).
    destruct (WN q e Q Wx) as (Ae & We & Xe & Lq & Oq & Ne).
    destruct (node_eq_dec (sx e, sk e) w0) as [Eq|Nq].
    + destruct (M1 e eq_refl) as (i' & Hi' & Mv). rewrite Mv.
      rewrite (write_value n0 l g q e Co Q i' Hi').
      assert (Ic' : icells i' = cells (sx e, sk e)).
      { unfold cells, iof. destruct Co as (A2 & B2 & C2 & D2).
        destruct (srun_ev p W l g A2 q e Q) as (i2 & H2 & Lk2 & _). rewrite Hi' in H2. subst i2.
        f_equal. symmetry. rewrite <- Hi'. apply wf_ins; auto. intros j Lj. simpl in *. symmetry. apply D2. lia. }
      rewrite Ic', Vw0, <- Eq. reflexivity.
    + exfalso.
      assert (D0 : ixw (sx e, sk e) x <> ixw w0 x).
      { unfold ixw. apply pos_inj; [exact NDx|apply wr_hist; auto|apply wr_hist; auto|].
        apply bt_neq; [exact Ae|exact Aw0|]. unfold neqb. destruct w0 as [c0 k0]. simpl.
        destruct (Nat.eqb_spec (sx e) c0); destruct (Nat.eqb_spec (sk e) k0); subst; simpl; first [reflexivity | congruence]. }
      assert (I0 : ixw w0 x = ixs u x) by (unfold ixs; rewrite Su; unfold ixw; rewrite Bw0; reflexivity).
      destruct (Nat.lt_ge_cases (ixw w0 x) (ixw (sx e, sk e) x)) as [Gt|Le].
      * assert (Rf : combx x u (sx e, sk e) = true).
        { unfold combx, frx. rewrite Au, Ae, Ru, We, Ne, (proj2 (inb_In x _) Ixu), (proj2 (inb_In x _) Xe).
          apply Nat.ltb_lt in Gt. rewrite <- I0, Gt. simpl. rewrite !orb_true_r. reflexivity. }
        pose proof (OordC n0 q u _ x Tn Oq Rf CPx). lia.
      * assert (Rc : combx x (sx e, sk e) w0 = true).
        { unfold combx, cox. rewrite Ae, Aw0, We, Ww0, (proj2 (inb_In x _) Xe), (proj2 (inb_In x _) Xw0).
          assert (ixw (sx e, sk e) x < ixw w0 x) by lia. apply Nat.ltb_lt in H. rewrite H. simpl. rewrite !orb_true_r. reflexivity. }
        pose proof (OordC q q0 _ w0 x Oq Q0 Rc CPx). rewrite (Later q0 e0 H E0) in Wx0. discriminate.
  - destruct (lw l x) as [e|] eqn:LW; [|apply M0; reflexivity].
    exfalso. destruct (lw_spec l _ e LW) as (q & Q & Wx & _).
    destruct (WN q e Q Wx) as (Ae & We & Xe & Lq & Oq & Ne).
    assert (Rf : combx x u (sx e, sk e) = true).
    { unfold combx, frx. rewrite Au, Ae, Ru, We, Ne, (proj2 (inb_In x _) Ixu), (proj2 (inb_In x _) Xe).
      unfold ixs. rewrite Su. simpl.
      pose proof (pos_in _ _ (wr_hist _ x Ae We Xe)) as P. unfold ixw.
      destruct (pos (T (sx e, sk e)) (hx x)) eqn:Z; [unfold hx in *; lia|].
      simpl. rewrite !orb_true_r. reflexivity. }
    pose proof (OordC n0 q u _ x Tn Oq Rf CPx). lia.
Qed.

Lemma nodiv : forall n0 l g c k i, corr' n0 l g -> nth_error ord n0 = Some (c, k) ->
  insr p s c k = Some i -> xload i (rrg c) = true -> (forall x, In x (icells i) -> CPc x = true) ->
  enc (map (sm g) (icells i)) = rval i (rrg c k).
Proof.
  intros n0 l g c k i Co Tn Hi X CPi.
  pose proof Hi as Hi0.
  rewrite (insr_pc p s R CP W) in Hi0 by (apply ordA; eapply nth_error_In; eauto).
  injection Hi0 as Hi0.
  assert (Au : acc (c, k) = true).
  { unfold acc, iof. simpl. rewrite Hi0. unfold xload in X. apply andb_prop in X. destruct X as [Ld Cd].
    rewrite Cd. destruct i; simpl in Ld; try discriminate; reflexivity. }
  destruct (node_E (c, k) Au) as (Eu & _ & _ & REu & Eiu & Eou).
  pose proof REu as (A1 & B1 & C1). simpl in B1, C1.
  assert (Ei : einstr p s Eu = i) by (rewrite Eiu; exact Hi0).
  destruct (j_val p s (nI2 p s R CP W) _ Eu i A1 Ei) as [V _]. unfold rgof in V. rewrite B1, C1 in V.
  change (MIComp.rrg s c k) with (rg (cs s c) k). rewrite (V X). f_equal. unfold rdvs.
  apply map_ext_in. intros x Ix. apply (nodiv_x n0 l g c k i Eu x Co Tn Hi X Eou Ix (CPi x Ix)).
Qed.

Lemma full' : (forall x, CPc x = true) -> exists l g, corr' (length ord) l g.
Proof.
  intros All.
  destruct (replay' (length ord) (le_n _)) as [X|(n0 & l & g & c & k & i & Ln & Co & Tn & Hi & X & M)]; auto.
  exfalso. apply M. apply (nodiv n0 l g c k i Co Tn Hi X (fun x _ => All x)).
Qed.

Section Full.
Variables (l : list sev) (g : sst).
Hypothesis Co : corr' (length ord) l g.

Lemma sp_full' : forall c, sp g c = pcs s c.
Proof.
  intros c. apply nat_iff_eq. intros j. rewrite (corr_sp' _ l g Co c j). rewrite (ordA c j). split.
  - intros (q & _ & Tq). eapply nth_error_In; eauto.
  - intros I. apply In_nth_error in I. destruct I as (q & Tq). exists q. split; auto. apply nth_error_Some. intros Z. pose proof (eq_trans (eq_sym Tq) Z). discriminate.
Qed.

Lemma mem_full' : forall x, CPc x = true -> sm g x = final s x.
Proof.
  intros x CPx. destruct Co as (A & B & C & D) eqn:Co'. destruct (srun_mem p W l g A x) as [M0 M1]. unfold final.
  assert (WN : forall q e, nth_error l q = Some e -> writes_x e x = true ->
            acc (sx e, sk e) = true /\ wr (sx e, sk e) = true /\ In x (cells (sx e, sk e))).
  { intros q e Q Wx. rewrite (scw_eq _ l g q e x Co Q) in Wx.
    apply andb_prop in Wx. destruct Wx as [Wx Xe]. apply andb_prop in Wx. destruct Wx as [Ae We]. apply inb_In in Xe. auto. }
  assert (NDx : NoDup (hx x)) by apply (n_nodup p s R CP W).
  destruct (rev (hs s x)) as [|[ym gm] rt] eqn:Er.
  - destruct (lw l x) as [e|] eqn:LW; [|apply M0; reflexivity]. exfalso.
    destruct (lw_spec l x e LW) as (q & Q & Wx & _). destruct (WN q e Q Wx) as (Ae & We & Xe).
    pose proof (wr_hist _ x Ae We Xe) as I. unfold hx in I.
    assert (hs s x = []) by (rewrite <- (rev_involutive (hs s x)), Er; reflexivity). rewrite H in I. destruct I.
  - assert (Eh : hs s x = rev rt ++ [(ym, gm)]) by (rewrite <- (rev_involutive (hs s x)), Er; reflexivity).
    assert (Iym : In ym (ids (hs s x))) by (rewrite Eh, ids_app, in_app_iff; right; left; auto).
    destruct (writer_node x ym Iym) as (wm & Aw & Ww & Xw & Bw & Vw & Lw).
    destruct (node_pos wm Lw) as (qm & Qm).
    assert (Lqm : qm < length ord) by (apply nth_error_Some; congruence).
    destruct (ev_at _ l g qm Co Lqm) as (em & Em & Om). rewrite Qm in Om. injection Om as Om.
    assert (Wxm : writes_x em x = true) by (rewrite (scw_eq _ l g qm em x Co Em), <- Om, Aw, Ww, (proj2 (inb_In x _) Xw); reflexivity).
    destruct (lw l x) as [e|] eqn:LW; [|rewrite (lw_none l x LW qm em Em) in Wxm; discriminate].
    destruct (lw_spec l x e LW) as (q & Q & Wx & Later). destruct (WN q e Q Wx) as (Ae & We & Xe).
    destruct (node_eq_dec (sx e, sk e) wm) as [Eq|Nq].
    + destruct (M1 e eq_refl) as (i' & Hi' & Mv). rewrite Mv, (write_value _ l g q e Co Q i' Hi').
      assert (Ic' : icells i' = cells (sx e, sk e)).
      { unfold cells, iof. destruct (srun_ev p W l g A q e Q) as (i2 & H2 & Lk2 & _). rewrite Hi' in H2. subst i2.
        f_equal. symmetry. rewrite <- Hi'. apply wf_ins; auto. intros j Lj. simpl in *. symmetry. apply D. lia. }
      rewrite Ic', Vw, <- Eq. reflexivity.
    + exfalso.
      assert (Ie : In (T (sx e, sk e)) (hx x)) by (apply (wr_hist _ x Ae We Xe)).
      assert (Pm : ixw wm x = length (ids (rev rt)) + 1).
      { unfold ixw, hx. rewrite Bw, Eh, ids_app. rewrite pos_app_out; [simpl; rewrite Nat.eqb_refl; reflexivity| |left; auto].
        intros I. pose proof (n_nodup p s R CP W x) as N. rewrite Eh, ids_app in N. eapply nodup_app_disj; eauto. left; auto. }
      assert (Pe : ixw (sx e, sk e) x <= length (ids (rev rt)) + 1).
      { unfold ixw. pose proof (pos_in _ _ Ie). unfold hx in *. rewrite Eh, ids_app, length_app in H. simpl in H.
        rewrite Eh, ids_app. simpl. lia. }
      assert (Ne : ixw (sx e, sk e) x <> ixw wm x).
      { unfold ixw. apply pos_inj; [exact NDx|exact Ie|apply (wr_hist _ x Aw Ww Xw)|].
        apply bt_neq; [exact Ae|exact Aw|]. unfold neqb. destruct wm as [c0 k0]. simpl.
        destruct (Nat.eqb_spec (sx e) c0); destruct (Nat.eqb_spec (sk e) k0); subst; simpl; first [reflexivity | congruence]. }
      assert (Rc : combx x (sx e, sk e) wm = true).
      { unfold combx, cox. rewrite Ae, Aw, We, Ww, (proj2 (inb_In x _) Xe), (proj2 (inb_In x _) Xw).
        assert (ixw (sx e, sk e) x < ixw wm x) by lia. apply Nat.ltb_lt in H. rewrite H. simpl. rewrite !orb_true_r. reflexivity. }
      pose proof (OordC q qm _ wm x (C q e Q) Qm Rc CPx). rewrite (Later qm em H Em) in Wxm. discriminate.
Qed.

End Full.

End Ord.

(* ---------- no cycle, for fenced programmes whose reach (STEP has) no access before itself ---------- *)
Section Acyc.
Hypothesis FN : fenced p.

Lemma IO : InvO p s. Proof. apply (iaoO p s (IAOg p s R)). Qed.
Local Abbreviation I1' := (nI1 p s R CP W).
Local Abbreviation I2' := (nI2 p s R CP W).
Local Abbreviation I3' := (nI3 p s R CP W).

Lemma fence_of : forall n, acc n = true ->
  1 <= snd n /\ ins p (fst n) (snd n - 1) (rrg (fst n)) = IFn FFull /\ ins p (fst n) (S (snd n)) (rrg (fst n)) = IFn FFull.
Proof. intros n A. unfold acc in A. apply andb_prop in A. destruct A as [A _]. apply FN. exact A. Qed.

Lemma acc_exec : forall n, acc n = true -> executes (iof n) (rrg (fst n)) = true.
Proof. intros n A. unfold acc in A. apply andb_prop in A. destruct A as [A1 A2]. unfold executes. rewrite A1. exact A2. Qed.

Lemma xacc_node : forall n E, acc n = true -> eofn n = Some E -> RE s (fst n) (snd n) E -> einstr p s E = iof n -> xacc p s E.
Proof.
  intros n E A Eo RE0 Ei. destruct (rd n) eqn:Rn.
  - right. exists (iof n). split; auto. rewrite (n_rgof p s R CP W _ _ E RE0). exact Rn.
  - left. pose proof (acc_rd_wr n A Rn) as Wn. unfold wr in Wn. rewrite Eo in Wn. exact Wn.
Qed.

(* the guard() right after an access, and what passes through it *)
Lemma through_guard : forall a b Ea Eb, acc a = true -> acc b = true -> pob a b = true ->
  eofn a = Some Ea -> eofn b = Some Eb ->
  vsub (vor (vor (eP Ea) (esrc Ea)) (gk p s (T a))) (eQ Eb) /\ T a < T b.
Proof.
  intros [c ka] [c' kb] Ea' Eb' A B Po Eao Ebo. unfold pob in Po. simpl in Po.
  apply andb_prop in Po. destruct Po as [E1 L1]. apply Nat.eqb_eq in E1. apply Nat.ltb_lt in L1. subst c'.
  destruct (node_E _ A) as (Ea & _ & _ & REa & Eia & Eoa). rewrite Eoa in Eao. injection Eao as <-.
  destruct (node_E _ B) as (Eb & _ & _ & REb & Eib & Eob). rewrite Eob in Ebo. injection Ebo as <-.
  destruct (fence_of _ A) as (_ & _ & Fa). simpl in Fa.
  assert (Nkb : S ka <> kb).
  { intros <-. destruct (node_E _ B) as (_ & Ib & _). unfold iof in Ib. simpl in Ib. rewrite Fa in Ib. discriminate. }
  destruct (n_ent p s R CP W c (S ka) _ Fa ltac:(discriminate) eq_refl) as (Ef & REf & Eif).
  assert (Taf : bt c ka < bt c (S ka)).
  { apply (n_tie p s R CP W c ka (S ka) _ _ ltac:(lia) eq_refl Fa (acc_exec _ A) eq_refl); [|discriminate].
    right; right; left; reflexivity. }
  assert (Tfb : bt c (S ka) < bt c kb).
  { apply (n_tie p s R CP W c (S ka) kb _ _ ltac:(lia) Fa eq_refl eq_refl (acc_exec _ B)); [right; left; reflexivity|].
    intros Z. destruct (node_E _ B) as (_ & Ib & _). unfold iof in Ib. simpl in Ib. rewrite Z in Ib. discriminate. }
  destruct REa as (A1 & B1 & C1). destruct REf as (A2 & B2 & C2). destruct REb as (A3 & B3 & C3). simpl in *.
  destruct (k_Ppair p s I3' _ Ea _ Ef A1 A2 ltac:(congruence) Taf) as [K1 K2].
  assert (Xg : xg p s Ef) by (exists (IFn FFull); split; [exact Eif|reflexivity]).
  assert (Xb : xacc p s Eb) by (apply (xacc_node (c, kb) Eb B Eob); [repeat split; auto|exact Eib]).
  pose proof (o_gpair p s IO _ Ef _ Eb A2 A3 ltac:(congruence) Tfb Xg Xb) as K3.
  split; [|unfold T; simpl; lia].
  intros y [[Y|Y]|(_ & _ & Fy)]; apply K3; [apply K1; exact Y|apply K2; exact Y|].
  apply (Fy _ Ef A2); [unfold T; simpl; lia|exact Xg].
Qed.

Lemma ent_lt' : forall t e y, ent s t = Some e -> vor (eP e) (esrc e) y -> ew e = false -> y < t.
Proof.
  intros t e y H Y Wf. destruct Y as [Y|Y].
  - apply (j_eP p s I2' t e y H Y).
  - unfold esrc, srcv in Y. rewrite Wf in Y. destruct Y as [(x & Y)|[]].
    apply (j_rf p s I2' t e x y H Y).
Qed.

Definition PR (t1 t2 : nat) : Prop :=
  exists a b, acc a = true /\ acc b = true /\ wr a = false /\ pob a b = true /\ T a = t1 /\ T b = t2.

Lemma pob_trans : forall a b c, pob a b = true -> pob b c = true -> pob a c = true.
Proof.
  unfold pob. intros a b c H1 H2. apply andb_prop in H1. apply andb_prop in H2.
  destruct H1 as [E1 L1]. destruct H2 as [E2 L2]. apply Nat.eqb_eq in E1, E2. apply Nat.ltb_lt in L1, L2.
  rewrite E1, E2, Nat.eqb_refl. simpl. apply Nat.ltb_lt. lia.
Qed.

Lemma T_inj : forall a b, acc a = true -> acc b = true -> T a = T b -> a = b.
Proof.
  intros [ca ka] [cb kb] A B E. unfold T in E. simpl in E.
  destruct (node_E _ A) as (Ea & Ia & Ca & _). destruct (node_E _ B) as (Eb & Ib & Cb & _).
  assert (Xa : executes (iof (ca, ka)) (rrg ca) = true) by (unfold executes; simpl in Ia; rewrite Ia; exact Ca).
  assert (Xb : executes (iof (cb, kb)) (rrg cb) = true) by (unfold executes; simpl in Ib; rewrite Ib; exact Cb).
  assert (Na : iof (ca, ka) <> INop) by (intros Z; rewrite Z in Ia; discriminate).
  assert (Nb : iof (cb, kb) <> INop) by (intros Z; rewrite Z in Ib; discriminate).
  destruct (bt_inj p s R CP W ca ka cb kb _ _ (n_insr p s R CP W ca ka _ eq_refl Na) (n_insr p s R CP W cb kb _ eq_refl Nb) Xa Xb E).
  subst. reflexivity.
Qed.

(* nothing enters a read's event but what it knows in order *)
Lemma into_read : forall t0 a, acc a = true -> wr a = false -> gedge s t0 (T a) ->
  exists Ea, eofn a = Some Ea /\ eQ Ea t0 /\ t0 <> T a.
Proof.
  intros t0 a A Wa G. destruct (node_E a A) as (Ea & _ & _ & REa & Eia & Eoa).
  assert (NH : forall x, ~ In (T a) (ids (hs s x))).
  { intros x I. destruct (j_hist p s I2' x (T a) I) as (e & i0 & H1 & H2 & _).
    assert (E' : ent s (T a) = Some Ea) by exact Eoa. rewrite E' in H1. injection H1 as <-.
    unfold wr in Wa. rewrite Eoa, H2 in Wa. discriminate. }
  destruct G as [(x & O)|[(e & x & L & Ix & Ib & N & M)|(e & L & Q & N)]].
  - exfalso. apply (NH x). apply (proj2 (older_in _ _ _ O)).
  - exfalso. apply (NH x Ib).
  - exists Ea. split; auto. unfold eofn, ent in Eoa. rewrite Eoa in L. injection L as <-. auto.
Qed.

Lemma H1_fsc : forall t0 t1 t2, gedge s t0 t1 -> PR t1 t2 -> gedge s t0 t2.
Proof.
  intros t0 t1 t2 G (a & b & A & B & Wa & Po & <- & <-).
  destruct (into_read t0 a A Wa G) as (Ea & Eoa & Q & N).
  destruct (node_E b B) as (Eb & _ & _ & REb & Eib & Eob).
  destruct (through_guard a b Ea Eb A B Po Eoa Eob) as [K Lt].
  pose proof (o_QP_G p s IO (T a) Ea Eoa t0 Q) as Y.
  assert (Wea : ew Ea = false) by (unfold wr in Wa; rewrite Eoa in Wa; exact Wa).
  assert (L0 : t0 < T a).
  { destruct Y as [Y|(Ly & _)]; [exact (ent_lt' (T a) Ea t0 Eoa Y Wea)|exact Ly]. }
  right; right. exists Eb. split; [exact Eob|]. split; [apply K; exact Y|lia].
Qed.

Lemma H2_fsc : forall t0 t1 t2, PR t0 t1 -> PR t1 t2 -> PR t0 t2.
Proof.
  intros t0 t1 t2 (a & b & A & B & Wa & P1 & <- & E1) (b' & c & B' & C & Wb & P2 & E2 & <-).
  assert (b' = b) by (apply T_inj; auto; congruence). subst b'.
  exists a, c. repeat split; auto. eapply pob_trans; eauto.
Qed.

Lemma H3_fsc : forall t, ~ PR t t.
Proof.
  intros t (a & b & A & B & Wa & Po & E1 & E2). assert (a = b) by (apply T_inj; auto; congruence). subst b.
  unfold pob in Po. apply andb_prop in Po. destruct Po as [_ L]. apply Nat.ltb_lt in L. lia.
Qed.

(* every edge between accesses is an edge of the event graph, or programme order out of a read *)
Lemma edge_S : forall a b, acc a = true -> acc b = true -> Rb a b = true -> gedge s (T a) (T b) \/ PR (T a) (T b).
Proof.
  intros a b A B H. destruct (node_E a A) as (Ea & Ia & Ca & REa & Eia & Eoa).
  destruct (node_E b B) as (Eb & Ib & Cb & REb & Eib & Eob).
  assert (Pw : pob a b = true -> wr a = true -> gedge s (T a) (T b)).
  { intros Po Wa. destruct (through_guard a b Ea Eb A B Po Eoa Eob) as [K Lt].
    right; right. exists Eb. split; [exact Eob|]. split; [|lia]. apply K. left. right.
    unfold esrc, srcv. unfold wr in Wa. rewrite Eoa in Wa. rewrite Wa. right.
    unfold vone. symmetry. rewrite (n_et p s R CP W _ _ Ea REa). reflexivity. }
  unfold Rb in H. apply orb_prop in H. destruct H as [Po|Co].
  - destruct (wr a) eqn:Wa; [left; auto|right; exists a, b; repeat split; auto].
  - left. apply comb_x in Co. destruct Co as (x & Cx). unfold combx in Cx.
    repeat (apply andb_prop in Cx; destruct Cx as [Cx ?]). rename H into Ox, H0 into Xb, H1 into Xa.
    apply inb_In in Xa, Xb.
    assert (NDx : NoDup (hx x)) by apply (n_nodup p s R CP W).
    apply orb_prop in Ox. destruct Ox as [Ox|Fr]; [apply orb_prop in Ox; destruct Ox as [Rf|Cw]|].
    + (* reads-from *)
      unfold rfx in Rf. apply andb_prop in Rf. destruct Rf as [Rf Sy]. apply andb_prop in Rf. destruct Rf as [Wa Rb'].
      destruct (srcx b x) as [y|] eqn:Sb; [|discriminate]. apply Nat.eqb_eq in Sy. subst y.
      destruct (rd_src b x (T a) B Sb) as (Iy & _ & Ly).
      destruct (Nat.eq_dec (fst a) (fst b)) as [Ec|Nc].
      * apply Pw; auto. unfold pob. rewrite Ec, Nat.eqb_refl. simpl. apply Nat.ltb_lt.
        destruct (Nat.lt_trichotomy (snd a) (snd b)) as [Lab|[Eab|Gab]]; auto.
        -- exfalso. assert (a = b) by (destruct a, b; simpl in *; congruence). subst. lia.
        -- exfalso. assert (T b < T a); [|lia]. unfold T. rewrite <- Ec.
           apply (n_tie p s R CP W (fst a) (snd b) (snd a) _ _ Gab eq_refl eq_refl); [rewrite Ec; apply (acc_exec b B)|apply (acc_exec a A)| |].
           ++ left. exists x. split; [rewrite Ec; exact Xb|exact Xa].
           ++ intros Z. unfold iof in Ia. rewrite Z in Ia. discriminate.
      * right; right. exists Eb. split; [exact Eob|]. split.
        -- unfold srcx in Sb. rewrite Eob in Sb.
           destruct REa as (A1 & B1 & C1). destruct REb as (A2 & B2 & C2).
           apply (o_rfe p s IO (T b) Eb x (T a) Ea A2 Sb A1). rewrite B1, B2. exact Nc.
        -- lia.
    + (* write order *)
      unfold cox in Cw. apply andb_prop in Cw. destruct Cw as [Cw L]. apply andb_prop in Cw. destruct Cw as [Wa Wb].
      apply Nat.ltb_lt in L. left. exists x. apply (pos_lt_older _ _ _ NDx); auto; apply wr_hist; auto.
    + (* from-read *)
      unfold frx in Fr. apply andb_prop in Fr. destruct Fr as [Fr L]. apply andb_prop in Fr. destruct Fr as [Fr Ne].
      apply andb_prop in Fr. destruct Fr as [Ra Wb]. apply Nat.ltb_lt in L.
      right; left. exists Ea, x. split; [exact Eoa|]. split.
      * destruct REa as (A1 & B1 & C1). destruct (o_eRC p s IO _ Ea A1) as [ER _]. rewrite ER.
        unfold evR. rewrite Eia. unfold rgof. rewrite B1.
        assert (Ra' : is_load (iof a) && icond (iof a) (rg (cs s (fst a))) = true) by exact Ra.
        rewrite Ra'. exact Xa.
      * split; [apply wr_hist; auto|]. split; [intros Z; apply (bt_neq a b A B Ne); congruence|].
        unfold ixs in L. unfold srcx in L. rewrite Eoa in L.
        destruct (erf Ea x) as [u|] eqn:Eu; auto.
        assert (Su : srcx a x = Some u) by (unfold srcx; rewrite Eoa; exact Eu).
        destruct (rd_src a x u A Su) as (Iu & _ & _).
        apply (pos_lt_older _ _ _ NDx); auto. apply wr_hist; auto.
Qed.

Lemma comb_nonacc_l : forall a b, acc a = false -> comb a b = false.
Proof.
  intros a b A. destruct (comb a b) eqn:C; auto. apply comb_x in C. destruct C as (x & C).
  unfold combx in C. rewrite A in C. discriminate.
Qed.
Lemma comb_nonacc_r : forall a b, acc b = false -> comb a b = false.
Proof.
  intros a b B. destruct (comb a b) eqn:C; auto. apply comb_x in C. destruct C as (x & C).
  unfold combx in C. rewrite B, andb_false_r in C. discriminate.
Qed.
Lemma Rb_nonacc_l : forall a b, acc a = false -> Rb a b = true -> pob a b = true.
Proof. intros a b A H. unfold Rb in H. rewrite comb_nonacc_l in H by auto. rewrite orb_false_r in H. auto. Qed.
Lemma Rb_nonacc_r : forall a b, acc b = false -> Rb a b = true -> pob a b = true.
Proof. intros a b B H. unfold Rb in H. rewrite comb_nonacc_r in H by auto. rewrite orb_false_r in H. auto. Qed.

Lemma chain_last_split : forall (f : node -> node -> bool) l1 b l2, chain node f (l1 ++ b :: l2) ->
  chain node f (l1 ++ [b]) /\ chain node f (b :: l2).
Proof.
  intros f l1 b l2 H. split.
  - apply (chain_prefix node f (l1 ++ [b]) l2). rewrite <- app_assoc. exact H.
  - apply (chain_suffix node f l1). exact H.
Qed.

Lemma compress : forall l x y, acc x = true -> chain node Rb (x :: l ++ [y]) -> chain node Rb (x :: filter acc l ++ [y]).
Proof.
  induction l as [|n l IH]; intros x y A H; simpl in *; auto.
  destruct H as [H1 H2]. destruct (acc n) eqn:An.
  - simpl. split; auto. apply (IH n y An H2).
  - apply IH; auto. pose proof (Rb_nonacc_r x n An H1) as P1.
    destruct (l ++ [y]) as [|m t] eqn:Et; [destruct l; discriminate|]. simpl in H2 |- *. destruct H2 as [H2 H3].
    split; auto. unfold Rb. rewrite (pob_trans x n m P1 (Rb_nonacc_l n m An H2)). reflexivity.
Qed.

Lemma pochain : forall l a b, (forall n, In n (a :: l) -> acc n = false) -> chain node Rb (a :: l ++ [b]) ->
  fst a = fst b /\ snd a < snd b.
Proof.
  induction l as [|m l IH]; intros a b Ac H; simpl in H.
  - destruct H as [H _]. apply Rb_nonacc_l in H; [|apply Ac; left; auto]. unfold pob in H.
    apply andb_prop in H. destruct H as [E Lt]. apply Nat.eqb_eq in E. apply Nat.ltb_lt in Lt. auto.
  - destruct H as [H1 H2]. apply Rb_nonacc_l in H1; [|apply Ac; left; auto].
    destruct (IH m b ltac:(intros n I; apply Ac; right; auto) H2) as [E Lt].
    unfold pob in H1. apply andb_prop in H1. destruct H1 as [E1 L1]. apply Nat.eqb_eq in E1. apply Nat.ltb_lt in L1.
    split; [congruence|lia].
Qed.

Lemma rotate : forall (f : node -> node -> bool) a l1 b l2, chain node f (a :: (l1 ++ b :: l2) ++ [a]) ->
  chain node f (b :: (l2 ++ a :: l1) ++ [b]).
Proof.
  intros f a l1 b l2 C. rewrite <- app_assoc in C. simpl in C.
  assert (C' : chain node f ((a :: l1) ++ b :: (l2 ++ [a]))) by (simpl; exact C).
  destruct (chain_last_split f (a :: l1) b (l2 ++ [a]) C') as [C1 C2].
  replace (b :: (l2 ++ a :: l1) ++ [b]) with ((b :: l2) ++ a :: (l1 ++ [b])) by (simpl; rewrite <- app_assoc; reflexivity).
  apply chain_app; auto.
Qed.

Local Abbreviation S2 := (fun x y => gedge s x y \/ PR x y).

Lemma chain_ct : forall l a b, (forall n, In n (a :: l ++ [b]) -> acc n = true) -> chain node Rb (a :: l ++ [b]) ->
  clos_trans nat S2 (T a) (T b).
Proof.
  induction l as [|m l IH]; intros a b Ac H; simpl in H.
  - destruct H as [H _]. constructor. apply edge_S; [apply Ac; simpl; auto|apply Ac; simpl; auto|exact H].
  - destruct H as [H1 H2]. apply (t_trans _ _ _ (T m)).
    + constructor. apply (edge_S a m); [apply Ac; simpl; auto|apply Ac; simpl; right; left; auto|exact H1].
    + apply IH; auto. intros n I. apply Ac. simpl in I |- *. destruct I as [<-|I]; [right; left; auto|right; right; auto].
Qed.

(* The same, with the event graph restricted to the times of accesses; its
   acyclicity is the only use of evok (acycG, for the write-back model's image) *)
Definition AT (t : nat) : Prop := exists n, acc n = true /\ T n = t.
Definition GA (x y : nat) : Prop := gedge s x y /\ AT x /\ AT y.

Section AcycG.
Hypothesis NGA : forall t, ~ clos_trans nat GA t t.

Lemma H1_ga : forall t0 t1 t2, GA t0 t1 -> PR t1 t2 -> GA t0 t2.
Proof.
  intros t0 t1 t2 (G & A0 & _) Pr. split; [exact (H1_fsc t0 t1 t2 G Pr)|split; [exact A0|]].
  destruct Pr as (a & b & _ & B & _ & _ & _ & Eb). exists b. auto.
Qed.
Lemma H2_ga : forall t0 t1 t2, PR t0 t1 -> PR t1 t2 -> PR t0 t2.
Proof. exact H2_fsc. Qed.

Lemma chain_ctG : forall l a b, (forall n, In n (a :: l ++ [b]) -> acc n = true) -> chain node Rb (a :: l ++ [b]) ->
  clos_trans nat (fun x y => GA x y \/ PR x y) (T a) (T b).
Proof.
  assert (E1 : forall a b, acc a = true -> acc b = true -> Rb a b = true -> GA (T a) (T b) \/ PR (T a) (T b)).
  { intros a b A B H. destruct (edge_S a b A B H) as [G|P]; [left|right; exact P].
    split; [exact G|split; [exists a; auto|exists b; auto]]. }
  induction l as [|m l IH]; intros a b Ac H; simpl in H.
  - destruct H as [H _]. constructor. apply E1; [apply Ac; simpl; auto|apply Ac; simpl; auto|exact H].
  - destruct H as [H1 H2]. apply (t_trans _ _ _ (T m)).
    + constructor. apply (E1 a m); [apply Ac; simpl; auto|apply Ac; simpl; right; left; auto|exact H1].
    + apply IH; auto. intros n I. apply Ac. simpl in I |- *. destruct I as [<-|I]; [right; left; auto|right; right; auto].
Qed.

Lemma access_cycleG : forall a l, acc a = true -> (forall n, In n l -> acc n = true) ->
  chain node Rb (a :: l ++ [a]) -> False.
Proof.
  intros a l A Al C.
  assert (All : forall n, In n (a :: l ++ [a]) -> acc n = true).
  { intros n I. simpl in I. destruct I as [<-|I]; auto. apply in_app_iff in I. destruct I as [I|[<-|[]]]; auto. }
  pose proof (chain_ctG l a a All C) as T0.
  exact (absorb_cycle GA PR H1_ga H2_ga H3_fsc NGA (T a) T0).
Qed.

Theorem acycG : acyclic node Rb L.
Proof.
  intros a l _ _ C.
  destruct (existsb acc (a :: l)) eqn:Ex.
  - simpl in Ex. destruct (acc a) eqn:Aa.
    + apply (access_cycleG a (filter acc l) Aa); [intros n I; apply filter_In in I; tauto|]. apply compress; auto.
    + simpl in Ex. apply existsb_exists in Ex. destruct Ex as (b & Ib & Ab).
      apply in_split in Ib. destruct Ib as (l1 & l2 & ->).
      pose proof (rotate Rb a l1 b l2 C) as C'.
      apply (access_cycleG b (filter acc (l2 ++ a :: l1)) Ab); [intros n I; apply filter_In in I; tauto|].
      apply compress; auto.
  - assert (NA : forall n, In n (a :: l) -> acc n = false).
    { intros n I. destruct (acc n) eqn:An; auto. exfalso.
      assert (existsb acc (a :: l) = true) by (apply existsb_exists; eauto). congruence. }
    destruct (pochain l a a NA C). lia.
Qed.
End AcycG.

Hypothesis EV : evok s.

Lemma access_cycle : forall a l, acc a = true -> (forall n, In n l -> acc n = true) ->
  chain node Rb (a :: l ++ [a]) -> False.
Proof.
  intros a l A Al C.
  assert (All : forall n, In n (a :: l ++ [a]) -> acc n = true).
  { intros n I. simpl in I. destruct I as [<-|I]; auto. apply in_app_iff in I. destruct I as [I|[<-|[]]]; auto. }
  pose proof (chain_ct l a a All C) as T0.
  exact (absorb_cycle (gedge s) PR H1_fsc H2_fsc H3_fsc (proj1 EV) (T a) T0).
Qed.

Theorem acyc : acyclic node Rb L.
Proof.
  intros a l _ _ C.
  destruct (existsb acc (a :: l)) eqn:Ex.
  - simpl in Ex. destruct (acc a) eqn:Aa.
    + apply (access_cycle a (filter acc l) Aa); [intros n I; apply filter_In in I; tauto|]. apply compress; auto.
    + simpl in Ex. apply existsb_exists in Ex. destruct Ex as (b & Ib & Ab).
      apply in_split in Ib. destruct Ib as (l1 & l2 & ->).
      pose proof (rotate Rb a l1 b l2 C) as C'.
      apply (access_cycle b (filter acc (l2 ++ a :: l1)) Ab); [intros n I; apply filter_In in I; tauto|].
      apply compress; auto.
  - assert (NA : forall n, In n (a :: l) -> acc n = false).
    { intros n I. destruct (acc n) eqn:An; auto. exfalso.
      assert (existsb acc (a :: l) = true) by (apply existsb_exists; eauto). congruence. }
    destruct (pochain l a a NA C). lia.
Qed.

Lemma fenced_sc_sec : exists l g, srun p l g /\ (forall c, sp g c = pcs s c) /\
  (forall c j, j < pcs s c -> sr g c j = rg (cs s c) j) /\ (forall x, sm g x = final s x).
Proof.
  destruct (topo node node_eq_dec Rb L L_nodup acyc) as (ord & P & O).
  set (CP0 := fun _ : cell => true).
  assert (OP : forall i j a b, nth_error ord i = Some a -> nth_error ord j = Some b -> pob a b = true -> i < j).
  { intros i j a b Qa Qb H. apply (O i j a b Qa Qb). unfold Rb. rewrite H. reflexivity. }
  assert (OC : forall i j a b x, nth_error ord i = Some a -> nth_error ord j = Some b -> combx x a b = true ->
            CP0 x = true -> i < j).
  { intros i j a b x Qa Qb H _. apply (O i j a b Qa Qb). unfold Rb.
    assert (comb a b = true) by (apply comb_x; eauto). rewrite H0, orb_true_r. reflexivity. }
  destruct (full' ord P CP0 OP OC (fun _ => eq_refl)) as (l & g & Co).
  exists l, g. split; [apply Co|]. split; [apply (sp_full' ord P CP0 OP OC l g Co)|].
  split; [|intros x; apply (mem_full' ord P CP0 OP OC l g Co x eq_refl)].
  intros c j Lj. rewrite <- (sp_full' ord P CP0 OP OC l g Co c) in Lj. destruct Co as (_ & _ & _ & D). apply D. auto.
Qed.

End Acyc.
End F.

(* Every access between guard() fences: sequential consistency for every
   finished reach (STEP that) has no access before itself. *)
Theorem fenced_sc : forall p s, wf p -> fenced p -> reach (STEP p) s -> done p s -> evok s ->
  exists l g, srun p l g /\ (forall c, sp g c = pcs s c) /\
    (forall c j, j < pcs s c -> sr g c j = rg (cs s c) j) /\ (forall x, sm g x = final s x).
Proof. intros p s W FN R CP EV. apply (fenced_sc_sec p s R CP W FN EV). Qed.

End Iface.
