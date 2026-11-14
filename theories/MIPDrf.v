(* Model2: DRF-SC for every run, finished or not, with fenced and plain
   accesses to the same cell and accesses of several cells, for runs that
   have no access before itself. By induction on the length of the run: the
   passed slots are replayed in a topological order of MIPOrd.Rs. At the first
   read that does not take its run value, in a cell where it differs:
   - if its source is replayed already (or is the initial value), knowledge
     and coherence in the replayed prefix give a race;
   - otherwise take the state just before the read was passed; by induction it
     has an interleaving of its passed slots. If the source was passed there,
     appending the read gives a race; if it was pending, its context runs
     forward to it and the read follows: a race (the interface field
     g_pending_source). Everything else uses the interface (M2Iface) only. *)
From Stdlib Require Import Arith Lia List Bool Permutation Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO M2SC M2SCx
  M2Trace M2Cont M2Snap MIPComp MIPNeg MIReplay M2Ev MIPFSC Topo MIPOrd MIPSync.
Require Import M2Iface MIBase.

(* a read that happened executes *)
Lemma xload_exec : forall i r, xload i r = true -> executes i r = true.
Proof.
  intros i r X. unfold xload in X. apply andb_prop in X. destruct X as [X1 X2]. unfold executes.
  destruct i; simpl in X1; try discriminate; exact X2.
Qed.

(* an access node executes *)
Lemma accn_exec : forall (pp : prog) (ss : M2Model.st) c k, MIPFSC.acc pp ss (c, k) = true ->
  executes (ins pp c k (rg (cs ss c))) (rg (cs ss c)) = true.
Proof.
  intros pp ss c k A. unfold MIPFSC.acc, MIPFSC.iof in A. simpl in A.
  apply andb_prop in A. destruct A as [A1 A2]. apply andb_prop in A1. destruct A1 as [_ A1].
  unfold executes. unfold MIPComp.rrg in *. rewrite A1. exact A2.
Qed.

Section Iface.
Context `{IFM : Model}.

Lemma wx_sacc : forall e x, writes_x e x = true -> exists ys, sacc e = Some (ys, true) /\ In x ys.
Proof.
  intros e x X. unfold writes_x in X. destruct (sacc e) as [[ys []]|]; try discriminate.
  exists ys. split; auto. apply existsb_exists in X. destruct X as (z & Z & Q). apply Nat.eqb_eq in Q. subst. auto.
Qed.


Set Default Proof Using "All".
Section Run.
Variable p : prog.
Hypothesis W : wf p.
Hypothesis Wc : cellful p.
Hypothesis RF : race_free_g p.
Variable s : st.
Hypothesis R : reach (STEP p) s.
Hypothesis EV : evok s.

Local Abbreviation bt := (MIPComp.bt s).
Local Abbreviation rrg := (MIPComp.rrg s).
Local Abbreviation L := (MIPFSC.L s).
Local Abbreviation Rs := (MIPOrd.Rs p s).
Local Abbreviation fz := (MIPOrd.fz p s).
Local Abbreviation comb := (MIPFSC.comb p s).
Local Abbreviation combx := (MIPFSC.combx p s).
Local Abbreviation acc := (MIPFSC.acc p s).
Local Abbreviation cells := (MIPFSC.cells p s).

Lemma I1s : Inv1 p s. Proof. apply I1g. auto. Qed.
Lemma I2s : Inv2 p s. Proof. apply (I2g p s R). Qed.
Lemma I3s : Inv3 p s. Proof. apply (I3 p s R W). Qed.
Lemma IOs : InvO p s. Proof. apply (iaoO p s (IAOg p s R)). Qed.

Lemma norace : forall l g, srun p l g -> racy_g p l -> False.
Proof. intros l g H X. exact (RF l g H X). Qed.

(* a write's cells are its cells in the event graph *)
Lemma ew_eCs : forall t E x, ent s t = Some E -> ew E = true -> In x (icells (einstr p s E)) -> In x (eC E).
Proof.
  intros t E x A Wt Ix. destruct (o_eRC p s IOs _ E A) as [_ EC]. rewrite EC. unfold evC.
  destruct (j_ew p s I2s _ E _ A eq_refl) as [W1 _]. rewrite Wt in W1. symmetry in W1.
  apply andb_prop in W1 as [W1 _]. apply andb_prop in W1 as [St Cd]. rewrite Cd, andb_true_r.
  destruct (einstr p s E); simpl in St; try discriminate; exact Ix.
Qed.

(* a guard() node is not a fenced access *)
Lemma ffull_nfz : forall n, insr p s (fst n) (snd n) = Some (IFn FFull) -> fz n = false.
Proof.
  intros n H. unfold MIPOrd.fz, MIPFSC.acc, MIPFSC.iof. rewrite (insr_ins p s R W _ _ _ H). simpl.
  destruct (snd n <? pcs s (fst n)); reflexivity.
Qed.

Lemma fa_fz : forall c k, fa p c k -> acc (c, k) = true -> fz (c, k) = true.
Proof. intros c k F A. unfold MIPOrd.fz. rewrite A, (fa_fnb p s R W EV c k F). reflexivity. Qed.

Lemma combx_comb : forall x a b, combx x a b = true -> comb a b = true.
Proof. intros x a b H. apply (proj2 (MIPFSC.comb_x p s R W a b)). eauto. Qed.

Section Ord.
Variable ord : list node.
Hypothesis Pord : Permutation L ord.
Hypothesis Oord : forall i j a b, nth_error ord i = Some a -> nth_error ord j = Some b -> Rs a b = true -> i < j.

Lemma OP : forall i j a b, nth_error ord i = Some a -> nth_error ord j = Some b -> pob a b = true -> i < j.
Proof. intros i j a b Qa Qb H. apply (Oord i j a b Qa Qb). unfold MIPOrd.Rs. rewrite H. reflexivity. Qed.

Lemma OC : forall i j a b x, nth_error ord i = Some a -> nth_error ord j = Some b -> combx x a b = true ->
  (fun _ : cell => false) x = true -> i < j.
Proof. intros. discriminate. Qed.

Local Abbreviation corr := (corr' p s ord).

Lemma pre_ord : forall n0 l g q e, corr n0 l g -> nth_error l q = Some e -> nth_error ord q = Some (sx e, sk e).
Proof. intros n0 l g q e (_ & _ & C & _) Q. apply C. auto. Qed.

Lemma pre_len : forall n0 l g, corr n0 l g -> length l = n0.
Proof. intros n0 l g (_ & B & _). auto. Qed.

Lemma pre_run : forall n0 l g, corr n0 l g -> srun p l g.
Proof. intros n0 l g (A & _). auto. Qed.

Lemma pre_fa : forall n0 l g, corr n0 l g -> forall c j, j < sp g c -> j < pcs s c -> sr g c j = rrg c j.
Proof. intros n0 l g (_ & _ & _ & D) c j L1 _. apply D. auto. Qed.

Lemma pre_pass : forall n0 l g q e, corr n0 l g -> nth_error l q = Some e -> sk e < pcs s (sx e).
Proof.
  intros n0 l g q e Co Q. apply (proj2 (ordA p s R W ord Pord _ OP OC (sx e) (sk e))).
  eapply nth_error_In. apply (pre_ord n0 l g q e Co Q).
Qed.

Lemma pre_inL : forall n0 l g q e, corr n0 l g -> nth_error l q = Some e -> In (sx e, sk e) L.
Proof. intros n0 l g q e Co Q. apply (inL_of p s R W EV). apply (pre_pass n0 l g q e Co Q). Qed.

Lemma pos_uniq : forall q1 q2 a, nth_error ord q1 = Some a -> nth_error ord q2 = Some a -> q1 = q2.
Proof. apply (pos_unique p s R W ord Pord _ OP OC). Qed.

(* guard() events stand in the order they were made *)
Lemma pre_gord : forall n0 l g, corr n0 l g -> gordS s l.
Proof.
  intros n0 l g Co a b f1 f2 Lab Qa Qb S1 S2 Nx.
  pose proof (pre_run n0 l g Co) as Rl.
  pose proof (pre_pass n0 l g a f1 Co Qa) as P1. pose proof (pre_pass n0 l g b f2 Co Qb) as P2.
  assert (F1 : insr p s (sx f1) (sk f1) = Some (IFn FFull)).
  { rewrite (insr_of p s R W _ _ P1). f_equal. apply (sg_ffull p s R W l g Rl (pre_fa n0 l g Co) a f1 Qa P1 S1). }
  assert (F2 : insr p s (sx f2) (sk f2) = Some (IFn FFull)).
  { rewrite (insr_of p s R W _ _ P2). f_equal. apply (sg_ffull p s R W l g Rl (pre_fa n0 l g Co) b f2 Qb P2 S2). }
  destruct (Nat.lt_trichotomy (bt (sx f1) (sk f1)) (bt (sx f2) (sk f2))) as [X|[X|X]]; auto; exfalso.
  - destruct (bt_inj p s R W _ _ _ _ _ _ F1 F2 eq_refl eq_refl X). auto.
  - pose proof (cmi_ff p s R W EV (sx f2, sk f2) (sx f1, sk f1) (pre_inL n0 l g b f2 Co Qb) (pre_inL n0 l g a f1 Co Qa) F2 F1 X) as Ci.
    assert (Rr : Rs (sx f2, sk f2) (sx f1, sk f1) = true).
    { unfold MIPOrd.Rs, MIPOrd.cmNb. rewrite (ffull_nfz (sx f1, sk f1) F1), (ffull_nfz (sx f2, sk f2) F2).
      apply Nat.ltb_lt in Ci. simpl. rewrite Ci. rewrite orb_true_r. reflexivity. }
    pose proof (Oord b a _ _ (pre_ord n0 l g b f2 Co Qb) (pre_ord n0 l g a f1 Co Qa) Rr). lia.
Qed.

(* an event of the prefix is the run's event, and its write is the run's write *)
Lemma pre_ent : forall n0 l g q e, corr n0 l g -> nth_error l q = Some e ->
  executes (ins p (sx e) (sk e) (rrg (sx e))) (rrg (sx e)) = true ->
  exists E, RE s (sx e) (sk e) E /\ einstr p s E = ins p (sx e) (sk e) (rrg (sx e)).
Proof.
  intros n0 l g q e Co Q X. apply (n_ent p s R W (sx e) (sk e) _ eq_refl); [apply (pre_pass n0 l g q e Co Q)|exact X].
Qed.

Lemma pre_write : forall n0 l g q e x, corr n0 l g -> nth_error l q = Some e -> writes_x e x = true ->
  acc (sx e, sk e) = true /\ MIPFSC.wr s (sx e, sk e) = true /\ In x (cells (sx e, sk e)).
Proof.
  intros n0 l g q e x Co Q X.
  rewrite (scw_eq p s R W ord Pord _ OP OC n0 l g q e x Co Q) in X.
  apply andb_prop in X as [X X3]. apply andb_prop in X as [X1 X2]. apply inb_In in X3. auto.
Qed.

Lemma pre_wfacts : forall n0 l g q e x, corr n0 l g -> nth_error l q = Some e -> writes_x e x = true ->
  exists E, RE s (sx e) (sk e) E /\ ew E = true /\ In x (icells (einstr p s E)) /\ In (bt (sx e) (sk e)) (ids (hs s x)).
Proof.
  intros n0 l g q e x Co Q X. destruct (pre_write n0 l g q e x Co Q X) as (A & Wr & Xc).
  destruct (pre_ent n0 l g q e Co Q (accn_exec p s _ _ A)) as (E & RE0 & Ei).
  exists E. split; [auto|]. split.
  - unfold MIPFSC.wr, MIPFSC.eofn, MIPFSC.T in Wr. destruct RE0 as (B1 & _). simpl in Wr. rewrite B1 in Wr. exact Wr.
  - split; [rewrite Ei; exact Xc|]. pose proof (wr_hist p s R W _ x A Wr Xc) as H. exact H.
Qed.

(* writes of a cell stand in the order of its history *)
Lemma pre_coh : forall n0 l g, corr n0 l g -> cohS s l.
Proof.
  intros n0 l g Co a b e1 e2 x Lab Qa Qb W1 W2.
  pose proof (pre_run n0 l g Co) as Rl.
  destruct (pre_write n0 l g a e1 x Co Qa W1) as (A1 & Wr1 & X1).
  destruct (pre_write n0 l g b e2 x Co Qb W2) as (A2 & Wr2 & X2).
  destruct (pre_wfacts n0 l g a e1 x Co Qa W1) as (E1 & RE1 & We1 & Ic1 & H1).
  destruct (pre_wfacts n0 l g b e2 x Co Qb W2) as (E2 & RE2 & We2 & Ic2 & H2).
  pose proof (pre_ord n0 l g a e1 Co Qa) as Oa. pose proof (pre_ord n0 l g b e2 Co Qb) as Ob.
  assert (Nn : (sx e1, sk e1) <> (sx e2, sk e2)) by (intros E; rewrite E in Oa; pose proof (pos_uniq a b _ Oa Ob); lia).
  assert (Nb : bt (sx e1) (sk e1) <> bt (sx e2) (sk e2)).
  { intros E. apply Nn. pose proof (pre_pass n0 l g a e1 Co Qa) as P1. pose proof (pre_pass n0 l g b e2 Co Qb) as P2.
    destruct (bt_inj p s R W _ _ _ _ _ _ (insr_of p s R W _ _ P1) (insr_of p s R W _ _ P2) (accn_exec p s _ _ A1) (accn_exec p s _ _ A2) E) as [E1' E2']. rewrite E1', E2'. auto. }
  destruct (older_total _ _ _ H1 H2 Nb) as [Ol|Ol]; [exact Ol|exfalso].
  pose proof (j_nodup p s I2s x) as ND.
  pose proof RE1 as (B1 & C1 & D1). pose proof RE2 as (B2 & C2 & D2).
  destruct (Nat.eq_dec (sx e1) (sx e2)) as [Ex|Nx].
  - (* the same context: e1 before e2 in the cell, and e2 older in the history *)
    pose proof (srun_order p W l g Rl a b e1 e2 Lab Qa Qb Ex) as Lk.
    apply (proj2 EV x (bt (sx e1) (sk e1))). apply t_trans with (bt (sx e2) (sk e2)).
    + constructor. right; right; right; right. exists E1, E2. split; [exact B1|]. split; [exact B2|].
      split; [congruence|]. split; [lia|]. split; [exact (ew_eCs _ E1 x B1 We1 Ic1)|exact (ew_eCs _ E2 x B2 We2 Ic2)].
    + constructor. left. exact Ol.
  - destruct (gsync_dec l a b (sx e1) (sx e2)) as [G|Ng].
    + (* e2 knows e1 in order *)
      destruct (wx_sacc e1 x W1) as (ys1 & Ae1 & _).
      destruct (wx_sacc e2 x W2) as (ys2 & Ae2 & _).
      assert (Kn : eQ E2 (bt (sx e1) (sk e1))).
      { apply (sync_knowQ p s R W l g Rl (pre_fa n0 l g Co) a b e1 e2 ys1 true E1 E2
                 (fun q e Q => pre_pass n0 l g q e Co Q) (pre_gord n0 l g Co) Qa Qb Lab Nx Ae1
                 (acc_nog p l g b e2 _ _ W Rl Qb Ae2) G RE1 RE2 (or_introl We2)).
        unfold esrc, srcv, vor. right. rewrite We1, (n_et p s R W _ _ _ RE1). reflexivity. }
      apply (proj1 EV (bt (sx e1) (sk e1))). apply t_trans with (bt (sx e2) (sk e2)).
      * constructor. right; right. exists E2. split; [exact B2|]. split; [exact Kn|exact Nb].
      * constructor. left. exists x. exact Ol.
    + (* no knowledge: both fenced, or a race *)
      destruct (fz (sx e1, sk e1) && fz (sx e2, sk e2)) eqn:Z.
      * apply andb_prop in Z as [Z1 Z2].
        assert (Cb : comb (sx e2, sk e2) (sx e1, sk e1) = true).
        { apply (combx_comb x). unfold MIPFSC.combx. rewrite A1, A2, (proj2 (inb_In x _) X1), (proj2 (inb_In x _) X2). simpl.
          unfold MIPFSC.cox. rewrite Wr1, Wr2. simpl.
          unfold MIPFSC.ixw, MIPFSC.hx, MIPFSC.T. cbn [fst snd].
          pose proof (pos_older _ _ _ ND Ol) as Po. apply Nat.ltb_lt in Po. rewrite Po. rewrite !orb_true_r. reflexivity. }
        assert (Rr : Rs (sx e2, sk e2) (sx e1, sk e1) = true).
        { unfold MIPOrd.Rs, MIPOrd.comF. fold fz. rewrite Z1, Z2, Cb. simpl. rewrite !orb_true_r. reflexivity. }
        pose proof (Oord b a _ _ Ob Oa Rr). lia.
      * apply (norace l g Rl).
        destruct (wx_sacc e1 x W1) as (ys1 & Ae1 & I1).
        destruct (wx_sacc e2 x W2) as (ys2 & Ae2 & I2).
        apply (racy_g_mk p l a b e1 e2 x ys1 ys2 true true Lab Qa Qb Nx Ae1 Ae2 I1 I2 eq_refl Ng).
        intros (F1 & F2). rewrite (fa_fz _ _ F1 A1), (fa_fz _ _ F2 A2) in Z. discriminate.
Qed.

(* the value the prefix leaves in a cell *)
Lemma pre_sm : forall n0 l g q w x, corr n0 l g -> lw l x = Some w -> nth_error l q = Some w ->
  sm g x = wv s (bt (sx w) (sk w)) x.
Proof.
  intros n0 l g q w x Co Lw Q.
  pose proof (pre_run n0 l g Co) as Rl.
  destruct (lw_spec l x w Lw) as (q' & Q' & X & _).
  destruct (proj2 (srun_mem p W l g Rl x) w Lw) as (i & Hi & M). rewrite M.
  destruct (pre_wfacts n0 l g q' w x Co Q' X) as (E & (A1 & B1 & C1) & We & _).
  destruct (pre_write n0 l g q' w x Co Q' X) as (Aw & _ & _).
  destruct (pre_ent n0 l g q w Co Q (accn_exec p s _ _ Aw)) as (E' & (A1' & _) & Ei).
  assert (E' = E) by congruence. subst E'.
  destruct (j_ew p s I2s _ E _ A1 Ei) as [_ W2]. destruct (W2 We) as [V _]. unfold rgof in V. rewrite B1 in V.
  rewrite V.
  assert (Ag : forall j, j < sk w -> sr g (sx w) j = rrg (sx w) j) by (intros j L0; apply (pre_fa n0 l g Co); [|pose proof (pre_pass n0 l g q w Co Q); lia];
    destruct (srun_ev p W l g Rl q w Q) as (_ & _ & Lt & _); lia).
  assert (Hi2 : ins p (sx w) (sk w) (rrg (sx w)) = i) by (rewrite <- Hi; symmetry; apply wf_ins; auto).
  rewrite Hi2. rewrite (ieval_wvals i _ _ (wf_ieval p (sx w) (sk w) i _ _ W Hi Ag)). reflexivity.
Qed.

Lemma xload_dof : forall i r, xload i r = true -> exists d, dof i r = Some d /\ icells (inst_of d) = icells i /\ is_load (inst_of d) = true.
Proof.
  intros i r X. destruct i as [m x c|m x c v|m x c e n'|fk|]; unfold xload, icond, ieval in X; simpl in X; try discriminate.
  - simpl. rewrite X. eexists. split; [reflexivity|split; reflexivity].
  - simpl. rewrite X. eexists. split; [reflexivity|split; reflexivity].
Qed.

Lemma xload_cell : forall i r, xload i r = true -> isacc i = true /\ icond i r = true /\ is_load i = true.
Proof.
  intros i r X. destruct i as [m x c|m x c v|m x c e n'|fk|]; unfold xload in X; simpl in X; try discriminate;
    unfold icond, ieval in *; simpl in *; auto.
Qed.

(* the run, as a trace, and the claim for its shorter prefixes *)
Variable f : nat -> st.
Variable n : nat.
Hypothesis T : gtrace (STEP p) f n.
Hypothesis Es : f n = s.
Hypothesis IH : forall m, m < n -> WIT p (f m).

(* the read reaching its slot, after the prefix *)
Section Read.
Variables (n0 : nat) (l : list sev) (g : sst) (c k : nat) (i : instr).
Hypothesis Co : corr n0 l g.
Hypothesis On : nth_error ord n0 = Some (c, k).
Hypothesis Hi : insr p s c k = Some i.
Hypothesis Xl : xload i (rrg c) = true.

Lemma rd_lt : k < pcs s c.
Proof. apply (proj2 (ordA p s R W ord Pord _ OP OC c k)). eapply nth_error_In. exact On. Qed.

Lemma rd_sp : sp g c = k.
Proof. apply (sp_at' p s R W ord Pord _ OP OC n0 l g c k Co On). Qed.

Lemma rd_ag : forall j, j < k -> sr g c j = rrg c j.
Proof. intros j L0. apply (pre_fa n0 l g Co); [rewrite rd_sp; auto|pose proof rd_lt; lia]. Qed.

Lemma rd_ins : ins p c k (sr g c) = i.
Proof. rewrite <- (insr_ins p s R W _ _ _ Hi). apply wf_ins; auto. apply rd_ag. Qed.

Lemma rd_ev : ieval i (sr g c) = ieval i (rrg c).
Proof. apply (wf_ieval p c k i (sr g c) (rrg c) W rd_ins). apply rd_ag. Qed.

(* an access of the prefix is the run's access *)
Lemma pre_acc : forall q w ys w0, nth_error l q = Some w -> sacc w = Some (ys, w0) ->
  icells (ins p (sx w) (sk w) (rrg (sx w))) = ys /\ executes (ins p (sx w) (sk w) (rrg (sx w))) (rrg (sx w)) = true.
Proof.
  intros q w ys w0 Q Aw. pose proof (pre_run n0 l g Co) as Rl.
  destruct (acc_ev p l g q w ys w0 W Rl Q Aw) as [Ic Ex].
  destruct (srun_ev p W l g Rl q w Q) as (_ & _ & Lt & _).
  assert (Ag : agree (sr g (sx w)) (rrg (sx w)) (sk w)) by (intros j L0; apply (pre_fa n0 l g Co); [lia|pose proof (pre_pass n0 l g q w Co Q); lia]).
  rewrite (proj1 (ins_agree p W (sx w) (sk w) _ _ Ag)) in Ic. rewrite (exec_agree p W (sx w) (sk w) _ _ Ag) in Ex. auto.
Qed.

(* ---------- the facts about the read ---------- *)
Lemma rd_facts : exists Eh dh, RE s c k Eh /\ einstr p s Eh = i /\
  rval i (rrg c k) = enc (rdvs s (icells i) (erf Eh)) /\
  dof i (rrg c) = Some dh /\ icells (inst_of dh) = icells i /\ is_load (inst_of dh) = true /\
  dof (ins p c (sp g c) (sr g c)) (sr g c) = Some dh /\
  acc (c, k) = true /\ MIPFSC.rd p s (c, k) = true /\ (forall x, MIPFSC.srcx s (c, k) x = erf Eh x) /\
  cells (c, k) = icells i /\ xacc p s Eh /\ (forall x, In x (icells i) -> In x (eR Eh) /\ In x (eC Eh)).
Proof.
  pose proof rd_lt as Lk.
  destruct (xload_cell i (rrg c) Xl) as (Ici & Cdi & Ldi).
  destruct (n_ent p s R W c k i (insr_ins p s R W _ _ _ Hi) Lk (xload_exec _ _ Xl)) as (Eh & REh & Eih).
  pose proof REh as (AH & XH & KH).
  destruct (j_val p s I2s _ Eh i AH Eih) as [V _]. unfold rgof in V. rewrite XH in V.
  specialize (V Xl). rewrite KH in V.
  destruct (xload_dof i (rrg c) Xl) as (dh & Dh & Cdh & Ldh).
  assert (Dg : dof (ins p c (sp g c) (sr g c)) (sr g c) = Some dh).
  { rewrite rd_sp, rd_ins. rewrite (dof_ieval _ _ _ rd_ev). exact Dh. }
  assert (Iof : MIPFSC.iof p s (c, k) = i) by (unfold MIPFSC.iof; simpl; apply (insr_ins p s R W _ _ _ Hi)).
  exists Eh, dh. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|].
  split; [auto|]. split; [auto|]. split; [|split; [|split; [|split; [|split]]]].
  - unfold MIPFSC.acc. rewrite Iof. simpl. rewrite (proj2 (Nat.ltb_lt _ _) Lk). rewrite Ici, Cdi. reflexivity.
  - unfold MIPFSC.rd. rewrite Iof. auto.
  - intros x. unfold MIPFSC.srcx, MIPFSC.eofn, MIPFSC.T. simpl. rewrite AH. reflexivity.
  - unfold MIPFSC.cells. rewrite Iof. reflexivity.
  - right. exists i. split; [exact Eih|]. unfold rgof. rewrite XH. exact Xl.
  - intros x Ix. destruct (o_eRC p s IOs _ Eh AH) as [ER EC]. rewrite ER, EC. unfold evR, evC. rewrite Eih.
    unfold rgof. rewrite XH.
    assert (Xl' : is_load i && icond i (rg (cs s c)) = true) by exact Xl.
    assert (Cdi' : icond i (rg (cs s c)) = true) by exact Cdi.
    rewrite Xl', Ici, Cdi'. simpl. auto.
Qed.

(* a write of the prefix synchronised with the read is known to it in order *)
Lemma pre_knowQ : forall q w EW Eh eh ys w0, nth_error l q = Some w -> sacc w = Some (ys, w0) ->
  RE s (sx w) (sk w) EW -> RE s c k Eh -> xacc p s Eh -> sg eh = false -> sx w <> c ->
  gsync (l ++ [eh]) q n0 (sx w) c -> vsub (esrc EW) (eQ Eh).
Proof.
  intros q w EW Eh eh ys w0 Q Aw REW REh XaH Gh Nc G.
  pose proof (pre_run n0 l g Co) as Rl. pose proof (pre_len n0 l g Co) as Ll.
  pose proof (pre_pass n0 l g q w Co Q) as Pw. pose proof rd_lt as Lk.
  destruct (pre_acc q w _ _ Q Aw) as [Icw Exw].
  destruct (srun_ev p W l g Rl q w Q) as (_ & _ & Lsw & _).
  pose proof REW as (AW & XW & KW). pose proof REh as (AH & XH & KH).
  destruct G as (a & b & f1 & f2 & La & Lab & Lb & F1 & F2 & S1 & S2 & X1 & X2).
  assert (Lb' : b < n0).
  { destruct (Nat.eq_dec b n0) as [->|N]; [|lia]. rewrite <- Ll, nth_app_last' in F2. injection F2 as <-. congruence. }
  rewrite nth_app_old' in F2 by lia. rewrite nth_app_old' in F1 by lia.
  assert (Nab : a <> b) by (intros ->; rewrite F1 in F2; injection F2 as <-; congruence).
  assert (Qa : a <> q) by (intros ->; rewrite Q in F1; injection F1 as <-; rewrite (acc_nog p l g q w _ _ W Rl Q Aw) in S1; discriminate).
  pose proof (pre_pass n0 l g a f1 Co F1) as P1. pose proof (pre_pass n0 l g b f2 Co F2) as P2.
  pose proof (sg_ffull p s R W l g Rl (pre_fa n0 l g Co) a f1 F1 P1 S1) as Ff1.
  pose proof (sg_ffull p s R W l g Rl (pre_fa n0 l g Co) b f2 F2 P2 S2) as Ff2.
  assert (Kw1 : sk w < sk f1) by (apply (srun_order p W l g Rl q a w f1 ltac:(lia) Q F1); congruence).
  assert (Kf2 : sk f2 < k).
  { destruct (srun_ev p W l g Rl b f2 F2) as (_ & _ & L2 & _). rewrite X2, rd_sp in L2. exact L2. }
  rewrite X1 in Ff1, P1. rewrite X2 in Ff2, P2.
  destruct (n_ent p s R W (sx w) (sk f1) _ Ff1 P1 eq_refl) as (F1E & RF1 & EF1).
  destruct (n_ent p s R W c (sk f2) _ Ff2 P2 eq_refl) as (F2E & RF2 & EF2).
  pose proof (tie_bt p s R W (sx w) (sk w) (sk f1) _ (IFn FFull) Kw1 (insr_of p s R W _ _ Pw)
                (eq_trans (insr_of p s R W _ _ P1) (f_equal Some Ff1)) Exw eq_refl ltac:(right; right; left; reflexivity)) as Bt1.
  pose proof RF1 as (A1 & _ & _). pose proof RF2 as (A2 & Y2 & _).
  destruct (k_Ppair p s I3s _ EW _ F1E AW A1 ltac:(destruct RF1 as (_ & Y1 & _); congruence) Bt1) as [_ St1].
  pose proof (pre_gord n0 l g Co a b f1 f2 ltac:(lia) F1 F2 S1 S2 ltac:(congruence)) as Bg. rewrite X1, X2 in Bg.
  assert (G1 : xg p s F1E) by (apply (n_xg p s R W _ _ _ _ RF1 EF1); reflexivity).
  assert (G2 : xg p s F2E) by (apply (n_xg p s R W _ _ _ _ RF2 EF2); reflexivity).
  destruct (k_Gpair p s I3s _ F1E _ F2E A1 A2 G1 G2 Bg) as [K2 _].
  pose proof (tie_bt p s R W c (sk f2) k (IFn FFull) i Kf2 (eq_trans (insr_of p s R W _ _ P2) (f_equal Some Ff2)) Hi
                eq_refl (xload_exec _ _ Xl) ltac:(right; left; reflexivity)) as Bt2.
  pose proof (o_gpair p s IOs _ F2E _ Eh A2 AH ltac:(congruence) Bt2 G2 XaH) as K3.
  intros v Hv. apply K3. apply K2. apply St1. exact Hv.
Qed.

(* the read cannot miss a write of its cell it knows in order, or that its own context wrote before it *)
Lemma miss_contra : forall x q w, In x (icells i) -> nth_error l q = Some w -> writes_x w x = true ->
  (sx w = c \/ exists eh, sg eh = false /\ gsync (l ++ [eh]) q n0 (sx w) c) ->
  forall Eh, RE s c k Eh -> (erf Eh x = None \/ exists y, erf Eh x = Some y /\ older (hs s x) y (bt (sx w) (sk w))) -> False.
Proof.
  intros x q w Ix Q Ww K Eh0 RE0 M.
  destruct rd_facts as (Eh & dh & REh & Eih & V & Dh & Cdh & Ldh & Dg & Ah & Rh & Sh & Xh & XaH & Gr).
  assert (Eh = Eh0) by (destruct REh as (A1 & _); destruct RE0 as (A2 & _); congruence). subst Eh0.
  destruct (Gr x Ix) as [RdR CR].
  pose proof (pre_run n0 l g Co) as Rl. pose proof (pre_len n0 l g Co) as Ll.
  destruct (pre_wfacts n0 l g q w x Co Q Ww) as (EW & REW & We & IcW & InW).
  pose proof REW as (AW & XW & KW). pose proof REh as (AH & XH & KH).
  destruct (srun_ev p W l g Rl q w Q) as (_ & _ & Lsw & _).
  assert (Nt : bt (sx w) (sk w) <> bt c k).
  { intros Z. pose proof (pre_pass n0 l g q w Co Q) as Pw.
    destruct (pre_write n0 l g q w x Co Q Ww) as (Aw0 & _ & _).
    destruct (bt_inj p s R W _ _ _ _ _ _ (insr_of p s R W _ _ Pw) Hi (accn_exec p s _ _ Aw0) (xload_exec _ _ Xl) Z) as [E1 E2].
    rewrite E1, rd_sp, E2 in Lsw. lia. }
  assert (MG : gedge s (bt c k) (bt (sx w) (sk w))).
  { right; left. exists Eh, x. split; [exact AH|]. split; [exact RdR|]. split; [exact InW|]. split; [auto|].
    destruct M as [M|(y & M1 & M2)]; rewrite ?M, ?M1; auto. }
  assert (MC : cedge s x (bt c k) (bt (sx w) (sk w))).
  { right; left. exists Eh. split; [exact AH|]. split; [exact RdR|]. split; [exact InW|]. split; [auto|].
    destruct M as [M|(y & M1 & M2)]; rewrite ?M, ?M1; auto. }
  destruct (Nat.eq_dec (sx w) c) as [Ec|Nc].
  - apply (proj2 EV x (bt (sx w) (sk w))). apply t_trans with (bt c k); [|constructor; exact MC].
    constructor. right; right; right; right. exists EW, Eh. split; [exact AW|]. split; [exact AH|].
    split; [congruence|]. split; [rewrite KW, KH; rewrite Ec, rd_sp in Lsw; exact Lsw|].
    split; [exact (ew_eCs _ EW x AW We IcW)|exact CR].
  - destruct K as [K|(eh & Gh & G)]; [congruence|].
    destruct (wx_sacc w x Ww) as (ys & Aw & _).
    pose proof (pre_knowQ q w EW Eh eh ys true Q Aw REW REh XaH Gh Nc G) as Kn.
    assert (PW : eQ Eh (bt (sx w) (sk w))).
    { apply Kn. unfold esrc, srcv, vor. right. rewrite We, (n_et p s R W _ _ _ REW). reflexivity. }
    apply (proj1 EV (bt (sx w) (sk w))). apply t_trans with (bt c k); [|constructor; exact MG].
    constructor. right; right. exists Eh. split; [exact AH|]. split; [exact PW|exact Nt].
Qed.

(* the read cannot be ordered after a later fenced write it reads before *)
Lemma fr_contra : forall nd q, nth_error ord q = Some nd -> q < n0 -> fz nd = true -> fz (c, k) = true ->
  comb (c, k) nd = true -> False.
Proof.
  intros nd q Q L0 Z1 Z2 Cb. assert (Rr : Rs (c, k) nd = true).
  { unfold MIPOrd.Rs, MIPOrd.comF. fold fz. rewrite Z1, Z2, Cb. simpl. rewrite !orb_true_r. reflexivity. }
  pose proof (Oord n0 q _ _ On Q Rr). lia.
Qed.

(* the read's step after the prefix, and a race with a write of the prefix *)
Lemma rd_race : forall dh x q w ys, dof (ins p c (sp g c) (sr g c)) (sr g c) = Some dh -> icells (inst_of dh) = icells i ->
  In x (icells i) -> nth_error l q = Some w -> sacc w = Some (ys, true) -> In x ys -> sx w <> c ->
  (forall eh, sx eh = c -> sk eh = k -> sg eh = false -> ~ gsync (l ++ [eh]) q n0 (sx w) c) ->
  ~ (fa p (sx w) (sk w) /\ fa p c k) -> False.
Proof.
  intros dh x q w ys Dg Cdh Ix Q Aw Iy Nc Ng Nf.
  pose proof (pre_run n0 l g Co) as Rl. pose proof (pre_len n0 l g Co) as Ll.
  destruct (snext_acc p (fun _ _ => true) g c dh Dg) as (wh & Ah & Gh). rewrite Cdh in Ah.
  set (eh := fst (snext p (fun _ _ => true) g c)) in *. set (gh := snd (snext p (fun _ _ => true) g c)).
  assert (St : sstep p g eh gh) by apply snext_step.
  assert (Xe : sx eh = c) by apply snext_x.
  assert (Ke : sk eh = k) by (destruct (sstep_shape p W _ _ _ St) as (? & _ & _ & Hk & _); rewrite Hk, Xe; apply rd_sp).
  apply (norace (l ++ [eh]) gh ltac:(econstructor; eauto)).
  apply (racy_g_mk p (l ++ [eh]) q n0 w eh x ys (icells i) true wh).
  - rewrite <- Ll. apply nth_error_Some. congruence.
  - rewrite nth_app_old' by (apply (proj1 (nth_error_Some l q)); congruence). auto.
  - rewrite <- Ll. apply nth_app_last'.
  - congruence.
  - auto.
  - auto.
  - exact Iy.
  - exact Ix.
  - reflexivity.
  - rewrite Xe. apply (Ng eh Xe Ke Gh).
  - rewrite Xe, Ke. auto.
Qed.

(* the from-read edge from the read to a later write of its cell *)
Lemma fr_edge : forall x q w Eh, In x (icells i) -> nth_error l q = Some w -> writes_x w x = true -> sx w <> c ->
  RE s c k Eh -> (erf Eh x = None \/ exists y, erf Eh x = Some y /\ older (hs s x) y (bt (sx w) (sk w))) ->
  combx x (c, k) (sx w, sk w) = true.
Proof.
  intros x q w Eh0 Ix Q Ww Nc RE0 M.
  destruct rd_facts as (Eh & dh & REh & Eih & V & Dh & Cdh & Ldh & Dg & Ah & Rh & Sh & Xh & XaH & Gr).
  assert (Eh = Eh0) by (destruct REh as (A1 & _); destruct RE0 as (A2 & _); congruence). subst Eh0.
  destruct (pre_write n0 l g q w x Co Q Ww) as (AW & WrW & XW).
  destruct (pre_wfacts n0 l g q w x Co Q Ww) as (_ & _ & _ & _ & InW).
  unfold MIPFSC.combx. rewrite Ah, AW, (proj2 (inb_In x _) XW). rewrite Xh, (proj2 (inb_In x _) Ix). simpl.
  unfold MIPFSC.frx. rewrite Rh, WrW. simpl.
  assert (Nq : MIPFSC.neqb (c, k) (sx w, sk w) = true).
  { unfold MIPFSC.neqb. simpl. destruct (Nat.eqb_spec c (sx w)); [congruence|reflexivity]. }
  rewrite Nq. unfold MIPFSC.ixs. rewrite Sh. unfold MIPFSC.ixw, MIPFSC.hx, MIPFSC.T. cbn [fst snd].
  pose proof (pos_in _ _ InW) as Pi.
  destruct M as [M|(y & M1 & M2)]; rewrite ?M, ?M1.
  - assert (Pi' : 0 < pos (bt (sx w) (sk w)) (ids (hs s x))) by lia.
    apply Nat.ltb_lt in Pi'. rewrite Pi'. rewrite !orb_true_r. reflexivity.
  - pose proof (pos_older _ _ _ (j_nodup p s I2s x) M2) as Po. apply Nat.ltb_lt in Po. rewrite Po. rewrite !orb_true_r. reflexivity.
Qed.

(* the read misses the last prefix write of its cell: a race, or a cycle *)
Lemma miss_last : forall x q w Eh, In x (icells i) -> nth_error l q = Some w -> writes_x w x = true ->
  RE s c k Eh -> (erf Eh x = None \/ exists y, erf Eh x = Some y /\ older (hs s x) y (bt (sx w) (sk w))) -> False.
Proof.
  intros x q w Eh0 Ix Q Ww RE0 M.
  destruct rd_facts as (Eh & dh & REh & Eih & V & Dh & Cdh & Ldh & Dg & Ah & Rh & Sh & Xh & XaH & Gr).
  assert (Eh = Eh0) by (destruct REh as (A1 & _); destruct RE0 as (A2 & _); congruence). subst Eh0.
  pose proof (pre_len n0 l g Co) as Ll.
  assert (Lq : q < n0) by (rewrite <- Ll; apply nth_error_Some; congruence).
  destruct (pre_write n0 l g q w x Co Q Ww) as (AW & WrW & XW).
  destruct (wx_sacc w x Ww) as (ys & Aw & Iy).
  assert (Kn : (sx w = c \/ exists eh, sg eh = false /\ gsync (l ++ [eh]) q n0 (sx w) c) -> False)
    by (intros K; apply (miss_contra x q w Ix Q Ww K Eh REh M)).
  destruct (Nat.eq_dec (sx w) c) as [Xc|Nc]; [apply Kn; left; auto|].
  apply (rd_race dh x q w ys Dg Cdh Ix Q Aw Iy Nc).
  - intros eh Xe Ke Ge G. apply Kn. right. exists eh. auto.
  - intros (F1 & F2).
    pose proof (fa_fz _ _ F1 AW) as Z1. pose proof (fa_fz _ _ F2 Ah) as Z2.
    apply (fr_contra (sx w, sk w) q (pre_ord n0 l g q w Co Q) Lq Z1 Z2).
    apply (combx_comb x). apply (fr_edge x q w Eh Ix Q Ww Nc REh M).
Qed.

(* ---------- the source is the initial value ---------- *)
Lemma nd_none : forall x Eh, In x (icells i) -> RE s c k Eh -> erf Eh x = None -> sm g x <> rdv s (erf Eh) x -> False.
Proof.
  intros x Eh Ix REh E0 Mis.
  pose proof (pre_run n0 l g Co) as Rl.
  destruct (lw l x) as [w|] eqn:Lw.
  2:{ apply Mis. rewrite (proj1 (srun_mem p W l g Rl x) Lw). unfold rdv. rewrite E0. reflexivity. }
  destruct (lw_spec l x w Lw) as (qw & Qw & Ww & After).
  apply (miss_last x qw w Eh Ix Qw Ww REh (or_introl E0)).
Qed.

(* the writer of a source, as a run event *)
Lemma src_writer : forall x Eh y, RE s c k Eh -> erf Eh x = Some y ->
  exists EY, ent s y = Some EY /\ ew EY = true /\ In x (icells (einstr p s EY)) /\
    oc (cs s (ec EY)) (ek EY) = Some y /\ y < bt c k.
Proof.
  intros x Eh y (AH & XH & KH) Ey.
  destruct (j_rf p s I2s _ Eh x y AH Ey) as (Ly & _ & _ & Hy).
  destruct (j_hist p s I2s _ y Hy) as (EY & iy0 & AY & WY & EIY & ICY).
  destruct (i_et p s I1s y EY AY) as (_ & OY).
  assert (EhY : eh EY = false) by (destruct (j_ew p s I2s _ EY _ AY eq_refl) as [W1 _]; rewrite WY in W1; destruct (eh EY); [discriminate|reflexivity]). rewrite EhY in OY.
  exists EY. split; [auto|]. split; [auto|]. split; [rewrite EIY; auto|]. split; auto.
Qed.

(* the writer's node, once passed *)
Lemma writer_node' : forall EY y x, ent s y = Some EY -> ew EY = true -> In x (icells (einstr p s EY)) ->
  ek EY < pcs s (ec EY) ->
  acc (ec EY, ek EY) = true /\ MIPFSC.wr s (ec EY, ek EY) = true /\ In x (cells (ec EY, ek EY)) /\
  bt (ec EY) (ek EY) = y.
Proof.
  intros EY y x AY WY IY L0. destruct (i_et p s I1s y EY AY) as (_ & OY).
  assert (EhY : eh EY = false) by (destruct (j_ew p s I2s _ EY _ AY eq_refl) as [W1 _]; rewrite WY in W1; destruct (eh EY); [discriminate|reflexivity]). rewrite EhY in OY.
  assert (By : bt (ec EY) (ek EY) = y) by (unfold MIPComp.bt, tmo; rewrite OY; reflexivity).
  pose proof (einstr_ins p s R W y EY AY L0) as Ei.
  destruct (j_ew p s I2s _ EY _ AY eq_refl) as [Ew _]. rewrite WY in Ew. symmetry in Ew.
  apply andb_prop in Ew as [Ew _]. apply andb_prop in Ew as [St Cd]. apply andb_prop in St as [_ St]. unfold rgof in Cd.
  rewrite Ei in Cd, IY, St.
  split; [|split; [|split; [|exact By]]].
  - unfold MIPFSC.acc, MIPFSC.iof. cbn [fst snd]. rewrite (proj2 (Nat.ltb_lt _ _) L0).
    assert (Cd' : icond (ins p (ec EY) (ek EY) (rrg (ec EY))) (rrg (ec EY)) = true) by exact Cd. rewrite Cd', andb_true_r.
    destruct (ins p (ec EY) (ek EY) (rrg (ec EY))); simpl in St; try discriminate; reflexivity.
  - unfold MIPFSC.wr, MIPFSC.eofn, MIPFSC.T. cbn [fst snd]. rewrite By, AY. exact WY.
  - unfold MIPFSC.cells, MIPFSC.iof. cbn [fst snd]. exact IY.
Qed.

(* ---------- the source is replayed already ---------- *)
Lemma nd_pre : forall x Eh y pu, In x (icells i) -> RE s c k Eh -> erf Eh x = Some y ->
  forall EY, ent s y = Some EY -> ew EY = true -> In x (icells (einstr p s EY)) ->
  ek EY < pcs s (ec EY) -> nth_error ord pu = Some (ec EY, ek EY) -> pu < n0 ->
  sm g x <> rdv s (erf Eh) x -> False.
Proof.
  intros x Eh y pu Ix REh E0 EY AY WY IY LY Pu Lpu Mis.
  pose proof (pre_run n0 l g Co) as Rl. pose proof (pre_len n0 l g Co) as Ll.
  destruct (writer_node' EY y x AY WY IY LY) as (AU & WrU & XoU & BU).
  destruct (ev_at p s R W ord Pord _ OP OC n0 l g pu Co Lpu) as (eu & Qu & Ou).
  rewrite Pu in Ou. injection Ou as Xu Ku.
  assert (Wu : writes_x eu x = true).
  { rewrite (scw_eq p s R W ord Pord _ OP OC n0 l g pu eu x Co Qu). rewrite <- Xu, <- Ku, AU, WrU, (proj2 (inb_In x _) XoU). reflexivity. }
  destruct (lw l x) as [w|] eqn:Lw; [|rewrite (lw_none l x Lw pu eu Qu) in Wu; discriminate].
  destruct (lw_spec l x w Lw) as (qw & Qw & Ww & After).
  destruct (Nat.lt_trichotomy qw pu) as [Lt|[Eq|Gt]].
  - rewrite (After pu eu Lt Qu) in Wu. discriminate.
  - subst qw. rewrite Qu in Qw. injection Qw as <-.
    apply Mis. rewrite (pre_sm n0 l g pu eu x Co Lw Qu). unfold rdv. rewrite E0. rewrite <- Xu, <- Ku, BU. reflexivity.
  - pose proof (pre_coh n0 l g Co pu qw eu w x Gt Qu Qw Wu Ww) as Ol. rewrite <- Xu, <- Ku, BU in Ol.
    apply (miss_last x qw w Eh Ix Qw Ww REh). right. exists y. auto.
Qed.


(* ---------- the source is not replayed yet: the state before the read was passed ---------- *)
Lemma nd_post : forall x Eh y EY, In x (icells i) -> RE s c k Eh -> erf Eh x = Some y -> ent s y = Some EY -> ew EY = true ->
  In x (icells (einstr p s EY)) -> oc (cs s (ec EY)) (ek EY) = Some y -> y < bt c k ->
  ~ (ek EY < pcs s (ec EY) /\ exists pu, nth_error ord pu = Some (ec EY, ek EY) /\ pu < n0) -> False.
Proof.
  intros x Eh0 y EY Ix RE0 E0 AY WY IY OY Ly NotPre.
  destruct rd_facts as (Eh & dh & REh & Eih & V & Dh & Cdh & Ldh & Dg & Ah & Rh & Sh & Xh & XaH & Gr).
  assert (Eh = Eh0) by (destruct REh as (A1 & _); destruct RE0 as (A2 & _); congruence). subst Eh0.
  pose proof rd_lt as Lk.
  destruct (g_birth p _ (GG p) W f n T c k ltac:(rewrite Es; exact Lk)) as (ih & Lih & Pih & Thb).
  rewrite Es in Thb. change (M2PComp.bt s c k) with (MIPComp.bt s c k) in Thb.
  assert (Rsb : reach (STEP p) (f ih)) by (apply (gtrace_reach p f n T); lia).
  pose proof (I1g p (f ih) Rsb) as Isb.
  assert (X : Ext (f ih) s) by (rewrite <- Es; apply (gtr_ext p f n T); lia).
  assert (OYb : oc (cs (f ih) (ec EY)) (ek EY) = Some y) by (apply (x_ocb _ _ X); [exact OY|lia]).
  destruct (IH ih Lih) as (lb & gb & Bsr & Bsp & Brg & Bgo & Bco).
  assert (Tih : gtrace (STEP p) f ih) by (apply (gtrace_le p f n); auto; lia).
  assert (EVih : evok (f ih)) by (apply (evok_gtr p f n T ltac:(rewrite Es; exact EV)); lia).
  (* the base's registers of the read's context *)
  assert (Agb : agree (sr gb c) (rrg c) k).
  { intros j Lj. rewrite Brg by lia. symmetry. apply (x_rg _ _ X). left. lia. }
  assert (Spb : sp gb c = k) by (rewrite Bsp; auto).
  assert (Dgb : dof (ins p c (sp gb c) (sr gb c)) (sr gb c) = Some dh).
  { rewrite Spb. rewrite (dof_agree p W c k (sr gb c) (rrg c) Agb). rewrite (insr_ins p s R W _ _ _ Hi). exact Dh. }
  (* the source's context is another one *)
  assert (Nc : (ec EY) <> c).
  { intros Ec.
    destruct (Nat.lt_trichotomy (ek EY) k) as [Lt|[Eq|Gt]].
    - apply NotPre. split; [rewrite Ec; lia|].
      assert (Lc : ek EY < pcs s c) by lia.
      destruct (node_pos p s R W ord Pord _ OP OC (c, (ek EY)) (inL_of p s R W EV c (ek EY) Lc)) as (pu & Pu).
      exists pu. split; [rewrite Ec; exact Pu|].
      assert (Pb : pob (c, (ek EY)) (c, k) = true) by (unfold pob; simpl; rewrite Nat.eqb_refl; apply Nat.ltb_lt in Lt; rewrite Lt; reflexivity).
      apply (OP pu n0 _ _ Pu On Pb).
    - rewrite Ec, Eq in OY. unfold MIPComp.bt, tmo in Ly. rewrite OY in Ly. lia.
    - (* a later slot of the read's context, tied to it by the cell x, happened after it *)
      pose proof (I1g p s R) as Is.
      destruct (xload_cell i (rrg c) Xl) as (I0 & C0 & _).
      assert (Ex : executes (ins p c k (rg (cs s c))) (rg (cs s c)) = true).
      { change (rg (cs s c)) with (rrg c). rewrite (insr_ins p s R W _ _ _ Hi). unfold executes. rewrite I0. exact C0. }
      assert (Ixk : In x (icells (ins p c k (rg (cs s c))))).
      { change (rg (cs s c)) with (rrg c). rewrite (insr_ins p s R W _ _ _ Hi). exact Ix. }
      unfold einstr in IY. rewrite Ec in IY, OY.
      assert (Bk : bt c k = match tmo (cs s c) k with Some t => t | None => 0 end) by reflexivity.
      destruct (Nat.lt_ge_cases (ek EY) (pcs s c)) as [Lp|Gp].
      + destruct (proj1 (i_cmA p s Is c (ek EY)) Lp) as (tau & Tc).
        rewrite (proj2 (i_set p s Is c (ek EY) tau Tc)) in IY.
        destruct (i_pot p s Is c k (ek EY) y Gt Lp ltac:(unfold tmo; rewrite OY; reflexivity) Ex ltac:(left; exists x; split; auto)) as (tj & Oj & Lj).
        rewrite Bk, Oj in Ly. lia.
      + destruct (i_pend p s Is c (ek EY) Gp ltac:(congruence)) as ((du & Adu & _) & _).
        rewrite Adu in IY.
        assert (Pu : pending (cs s c) (pcs s c) (ek EY) du) by (split; [auto|split; [congruence|auto]]).
        destruct (i_ptiet p s Is c (ek EY) y du k Pu OY Lk Ex ltac:(left; exists x; split; auto)) as (tj & Oj & Lj).
        rewrite Bk, Oj in Ly. lia. }
  (* the source written by then *)
  assert (AYb : ent (f ih) y = Some EY).
  { assert (Ly' : y < length (lg (f ih))) by (rewrite <- (i_tm p (f ih) Isb); lia).
    destruct (nth_error (lg (f ih)) y) as [E'|] eqn:N; [|apply nth_error_None in N; lia].
    pose proof (x_ent _ _ X y E' N) as N2. rewrite AY in N2. injection N2 as ->. exact N. }
  destruct (Nat.lt_ge_cases (ek EY) (pcs (f ih) (ec EY))) as [Lpb|Gpb].
  - (* passed by then: in the base; appending the read is a race *)
    assert (Lps : (ek EY) < pcs s (ec EY)) by (pose proof (x_pcs _ _ X (ec EY)); lia).
    destruct (node_pos p s R W ord Pord _ OP OC ((ec EY), (ek EY)) (inL_of p s R W EV (ec EY) (ek EY) Lps)) as (pu & Pu).
    assert (Gp : n0 < pu).
    { destruct (Nat.lt_ge_cases pu n0) as [Lp|Gp]; [exfalso; apply NotPre; split; [auto|exists pu; auto]|].
      destruct (Nat.eq_dec pu n0) as [->|Np]; [|lia]. rewrite On in Pu. injection Pu as E1 _. congruence. }
    assert (REYb : RE (f ih) (ec EY) (ek EY) EY).
    { split; [unfold MIPComp.bt, tmo; rewrite OYb; exact AYb|split; reflexivity]. }
    assert (Iyb : In x (icells (einstr p (f ih) EY))).
    { unfold einstr. rewrite <- (x_ai _ _ X (ec EY) (ek EY) Lpb). exact IY. }
    destruct (lb_has_write p W (f ih) Rsb lb gb Bsr Bsp Brg (ec EY) (ek EY) EY x Lpb REYb WY Iyb) as (qu & eu & Qu & Xu & Ku & Wu).
    destruct (snext_acc p (fun _ _ => true) gb c dh Dgb) as (wb & Ab & Gb). rewrite Cdh in Ab.
    set (eb := fst (snext p (fun _ _ => true) gb c)) in *. set (gb' := snd (snext p (fun _ _ => true) gb c)).
    assert (Stb : sstep p gb eb gb') by apply snext_step.
    assert (Xeb : sx eb = c) by apply snext_x.
    assert (Keb : sk eb = k).
    { destruct (sstep_shape p W _ _ _ Stb) as (i1 & _ & _ & Hk & _). rewrite Hk. rewrite Xeb. exact Spb. }
    destruct (wx_sacc eu x Wu) as (ys & Au & Iu').
    assert (Lqu : qu < length lb) by (apply nth_error_Some; congruence).
    apply (norace (lb ++ [eb]) gb' ltac:(econstructor; eauto)).
    apply (racy_g_mk p (lb ++ [eb]) qu (length lb) eu eb x ys (icells i) true wb Lqu
             ltac:(rewrite nth_app_old' by auto; exact Qu) (nth_app_last' lb eb) ltac:(congruence) Au Ab Iu' Ix eq_refl).
    + (* a guard() pair would have put the source before the read *)
      intros (a & b & f1 & f2 & L1 & L2 & L3 & F1 & F2 & S1 & S2 & X1 & X2).
      rewrite Xu in X1. rewrite Xeb in X2.
      assert (Lb : b < length lb).
      { destruct (Nat.eq_dec b (length lb)) as [->|N]; [|lia]. rewrite nth_app_last' in F2. injection F2 as <-. congruence. }
      rewrite nth_app_old' in F2 by auto. rewrite nth_app_old' in F1 by lia.
      assert (Nab : a <> b) by (intros ->; rewrite F1 in F2; injection F2 as <-; congruence).
      assert (Qa : a <> qu) by (intros ->; rewrite Qu in F1; injection F1 as <-; rewrite (acc_nog p lb gb qu eu _ _ W Bsr Qu Au) in S1; discriminate).
      pose proof (lb_pass p W (f ih) lb gb Bsr Bsp a f1 F1) as P1. pose proof (lb_pass p W (f ih) lb gb Bsr Bsp b f2 F2) as P2.
      assert (Fab : forall z fz, nth_error lb z = Some fz -> sg fz = true -> sk fz < pcs (f ih) (sx fz) ->
                  insr p s (sx fz) (sk fz) = Some (IFn FFull)).
      { intros z fz Z Sz Pz.
        pose proof (sg_ffull p (f ih) Rsb W lb gb Bsr (fun c0 j0 _ L0 => Brg c0 j0 L0) z fz Z Pz Sz) as F0.
        assert (Ps : sk fz < pcs s (sx fz)) by (pose proof (x_pcs _ _ X (sx fz)); lia).
        rewrite (insr_of p s R W _ _ Ps). f_equal. rewrite <- F0. apply wf_ins; auto.
        intros j Lj. unfold MIPComp.rrg. apply (x_rg _ _ X). left. lia. }
      pose proof (Fab a f1 F1 S1 P1) as Ff1. pose proof (Fab b f2 F2 S2 P2) as Ff2.
      assert (Kw1 : (ek EY) < sk f1) by (rewrite <- Ku; apply (srun_order p W lb gb Bsr qu a eu f1 ltac:(lia) Qu F1); congruence).
      assert (Kf2 : sk f2 < k) by (rewrite <- Spb; destruct (srun_ev p W lb gb Bsr b f2 F2) as (_ & _ & L0 & _); rewrite X2 in L0; exact L0).
      pose proof (Bgo a b f1 f2 ltac:(lia) F1 F2 S1 S2 ltac:(congruence)) as Bg.
      (* the times are the same in s *)
      assert (Bts : forall cz kz, kz < pcs (f ih) cz -> executes (ins p cz kz (rg (cs (f ih) cz))) (rg (cs (f ih) cz)) = true ->
                MIPComp.bt s cz kz = MIPComp.bt (f ih) cz kz).
      { intros cz kz Lz Ez. unfold MIPComp.bt. destruct (tmo_passed p (f ih) cz kz Isb Lz Ez) as (t0 & O0 & _).
        rewrite (x_tmo _ _ cz kz t0 X Lz O0), O0. reflexivity. }
      assert (Eg : forall z fz, nth_error lb z = Some fz -> sg fz = true -> sk fz < pcs (f ih) (sx fz) ->
                executes (ins p (sx fz) (sk fz) (rg (cs (f ih) (sx fz)))) (rg (cs (f ih) (sx fz))) = true).
      { intros z fz Z Sz Pz.
        pose proof (sg_ffull p (f ih) Rsb W lb gb Bsr (fun c0 j0 _ L0 => Brg c0 j0 L0) z fz Z Pz Sz) as Q.
        unfold MIPComp.rrg in Q. rewrite Q. reflexivity. }
      rewrite <- (Bts (sx f1) (sk f1) P1 (Eg a f1 F1 S1 P1)), <- (Bts (sx f2) (sk f2) P2 (Eg b f2 F2 S2 P2)) in Bg.
      assert (Ps1 : sk f1 < pcs s (sx f1)) by (pose proof (x_pcs _ _ X (sx f1)); lia).
      assert (Ps2 : sk f2 < pcs s (sx f2)) by (pose proof (x_pcs _ _ X (sx f2)); lia).
      pose proof (cmi_ff p s R W EV (sx f1, sk f1) (sx f2, sk f2) (inL_of p s R W EV _ _ Ps1) (inL_of p s R W EV _ _ Ps2) Ff1 Ff2 Bg) as Ci.
      destruct (node_pos p s R W ord Pord _ OP OC (sx f1, sk f1) (inL_of p s R W EV _ _ Ps1)) as (p1 & Q1).
      destruct (node_pos p s R W ord Pord _ OP OC (sx f2, sk f2) (inL_of p s R W EV _ _ Ps2)) as (p2 & Q2).
      assert (R12 : Rs (sx f1, sk f1) (sx f2, sk f2) = true).
      { unfold MIPOrd.Rs, MIPOrd.cmNb. rewrite (ffull_nfz (sx f1, sk f1) Ff1), (ffull_nfz (sx f2, sk f2) Ff2).
        apply Nat.ltb_lt in Ci. simpl. rewrite Ci. rewrite orb_true_r. reflexivity. }
      assert (Pu1 : pob ((ec EY), (ek EY)) (sx f1, sk f1) = true) by (unfold pob; simpl; rewrite X1, Nat.eqb_refl; apply Nat.ltb_lt in Kw1; rewrite Kw1; reflexivity).
      assert (P2h : pob (sx f2, sk f2) (c, k) = true) by (unfold pob; simpl; rewrite X2, Nat.eqb_refl; apply Nat.ltb_lt in Kf2; rewrite Kf2; reflexivity).
      pose proof (OP pu p1 _ _ Pu Q1 Pu1). pose proof (Oord p1 p2 _ _ Q1 Q2 R12). pose proof (OP p2 n0 _ _ Q2 On P2h). lia.
    + (* a fenced pair: coherence would have put the source before the read *)
      intros (F1 & F2). rewrite Xu, Ku in F1. rewrite Xeb, Keb in F2.
      destruct (writer_node' EY y x AY WY IY Lps) as (AU & WrU & XoU & BU).
      pose proof (fa_fz _ _ F1 AU) as Z1. pose proof (fa_fz _ _ F2 Ah) as Z2.
      assert (Cb : comb ((ec EY), (ek EY)) (c, k) = true).
      { apply (combx_comb x). unfold MIPFSC.combx. rewrite AU, Ah, (proj2 (inb_In x _) XoU), Xh, (proj2 (inb_In x _) Ix). simpl.
        unfold MIPFSC.rfx. rewrite WrU, Rh, Sh, E0. unfold MIPFSC.T. cbn [fst snd]. rewrite BU, Nat.eqb_refl. reflexivity. }
      assert (Rr : Rs ((ec EY), (ek EY)) (c, k) = true).
      { unfold MIPOrd.Rs, MIPOrd.comF. fold fz. rewrite Z1, Z2, Cb. simpl. rewrite !orb_true_r. reflexivity. }
      pose proof (Oord pu n0 _ _ Pu On Rr). lia.
  - (* pending then: the source's context runs forward to it, then the read: a race *)
    assert (Iyb : In x (icells (einstr p (f ih) EY))).
    { unfold einstr. rewrite (g_pending_cells p _ (GG p) W f n T ih (ec EY) (ek EY) ltac:(lia) Gpb ltac:(congruence)), Es.
      exact IY. }
    assert (Ixd : In x (icells (inst_of dh))) by (rewrite Cdh; exact Ix).
    destruct (g_pending_source p _ (GG p) W Wc f ih Tih EVih lb gb (conj Bsr (conj Bsp (conj Brg (conj Bgo Bco))))
                c dh x y EY Dgb Ixd AYb WY Iyb Nc OYb Gpb) as (l' & g' & H' & Xr).
    exact (norace l' g' H' Xr).
Qed.

End Read.

(* ---------- no divergence: the whole replay is faithful ---------- *)
Lemma no_div : forall n0 l g c k i, corr n0 l g -> nth_error ord n0 = Some (c, k) -> insr p s c k = Some i ->
  xload i (rrg c) = true -> enc (map (sm g) (icells i)) <> rval i (rrg c k) -> False.
Proof.
  intros n0 l g c k i Co On Hi Xl Mis.
  destruct (rd_facts n0 l g c k i Co On Hi Xl) as (Eh & dh & REh & Eih & V & _).
  assert (Ex : exists x, In x (icells i) /\ sm g x <> rdv s (erf Eh) x).
  { destruct (existsb (fun x => negb (Nat.eqb (sm g x) (rdv s (erf Eh) x))) (icells i)) eqn:Eb.
    - apply existsb_exists in Eb. destruct Eb as (x & Ix & Nx). exists x. split; auto.
      apply negb_true_iff in Nx. apply Nat.eqb_neq in Nx. exact Nx.
    - exfalso. apply Mis. rewrite V. f_equal. unfold rdvs. apply map_ext_in. intros x Ix.
      destruct (Nat.eqb_spec (sm g x) (rdv s (erf Eh) x)) as [E|N]; auto. exfalso.
      assert (existsb (fun x => negb (Nat.eqb (sm g x) (rdv s (erf Eh) x))) (icells i) = true).
      { apply existsb_exists. exists x. split; auto. apply negb_true_iff. apply Nat.eqb_neq. auto. }
      congruence. }
  destruct Ex as (x & Ix & Misx).
  destruct (erf Eh x) as [y|] eqn:Ey; [|exact (nd_none n0 l g c k i Co On Hi Xl x Eh Ix REh Ey Misx)].
  destruct (src_writer n0 l g c k i Co On Hi Xl x Eh y REh Ey) as (EY & AY & WY & IY & OY & Ly).
  assert (Dec : (ek EY < pcs s (ec EY) /\ exists pu, nth_error ord pu = Some (ec EY, ek EY) /\ pu < n0) \/
                ~ (ek EY < pcs s (ec EY) /\ exists pu, nth_error ord pu = Some (ec EY, ek EY) /\ pu < n0)).
  { destruct (Nat.lt_ge_cases (ek EY) (pcs s (ec EY))) as [Lp|Gp]; [|right; intros (X & _); lia].
    destruct (node_pos p s R W ord Pord _ OP OC (ec EY, ek EY) (inL_of p s R W EV _ _ Lp)) as (pu & Pu).
    destruct (Nat.lt_ge_cases pu n0) as [L0|G]; [left; split; [auto|exists pu; auto]|right].
    intros (_ & pu' & Pu' & L'). pose proof (pos_uniq pu pu' _ Pu Pu'). lia. }
  destruct Dec as [(Lp & pu & Pu & Lpu)|ND].
  - exact (nd_pre n0 l g c k i Co On Hi Xl x Eh y pu Ix REh Ey EY AY WY IY Lp Pu Lpu Misx).
  - exact (nd_post n0 l g c k i Co On Hi Xl x Eh y EY Ix REh Ey AY WY IY OY Ly ND).
Qed.

Lemma full : exists l g, corr (length ord) l g.
Proof.
  destruct (replay' p s R W ord Pord (fun _ => false) OP OC (length ord) (le_n _))
    as [X|(n0 & l & g & c & k & i & Ln & Co & On & Hi & Xl & M)]; auto.
  exfalso. apply (no_div n0 l g c k i Co On Hi Xl M).
Qed.

Lemma full_sp : forall l g, corr (length ord) l g -> forall c, sp g c = pcs s c.
Proof.
  intros l g Co c. apply nat_iff_eq. intros j.
  rewrite (corr_sp' p s R W ord Pord _ OP OC _ l g Co c j). rewrite (ordA p s R W ord Pord _ OP OC c j). split.
  - intros (q & _ & Q). eapply nth_error_In; eauto.
  - intros I. apply In_nth_error in I. destruct I as (q & Q). exists q. split; auto. assert (Hn : @nth_error (nat * nat) ord q <> None) by (rewrite Q; discriminate). apply nth_error_Some in Hn. exact Hn.
Qed.

Lemma wit_s : WIT p s.
Proof.
  destruct full as (l & g & Co). exists l, g.
  split; [apply (pre_run _ _ _ Co)|]. split; [apply (full_sp l g Co)|]. split; [|split; [apply (pre_gord _ _ _ Co)|apply (pre_coh _ _ _ Co)]].
  intros c j Lj. apply (pre_fa _ _ _ Co); [rewrite (full_sp l g Co); auto|auto].
Qed.

End Ord.
End Run.

(* ---------- every run ---------- *)
Theorem wit_tr : forall p, wf p -> cellful p -> race_free_g p -> forall n f, gtrace (STEP p) f n -> evok (f n) -> WIT p (f n).
Proof.
  intros p W Wc RF n. induction n as [n IHn] using lt_wf_ind. intros f T E.
  assert (R : reach (STEP p) (f n)) by (apply (gtrace_reach p f n T); lia).
  destruct (topo node (node_eq_dec p (f n) R W) (MIPOrd.Rs p (f n)) (MIPFSC.L (f n))
              (L_nodup p (f n) R W) (acyc_s p (f n) R W E)) as (ord & P & O).
  apply (wit_s p W Wc RF (f n) R E ord P O f n T eq_refl).
  intros m L. apply (IHn m L f); [apply (gtrace_le p f n m T); lia|apply (evok_gtr p f n T E m); lia].
Qed.

(* DRF-SC for every run, finished or not, that has no access before itself:
   an interleaving of the slots it has passed, with their registers, guard()
   events in the order they were made, and each cell's writes in the order of
   its history *)
Theorem drf_prefix_m2 : forall p s, wf p -> cellful p -> race_free_g p -> reach (STEP p) s -> evok s -> WIT p s.
Proof.
  intros p s W Wc RF R EVs. destruct (reach_gtrace p s R) as (f & n & T & E). rewrite <- E.
  apply (wit_tr p W Wc RF n f T). rewrite E. exact EVs.
Qed.

(* ---------- finished runs: the final storage too ---------- *)
Theorem drf_sc_m2 : forall p s, wf p -> cellful p -> race_free_g p -> reach (STEP p) s -> done p s -> evok s ->
  exists l g, srun p l g /\ (forall c, sp g c = pcs s c) /\
    (forall c j, j < pcs s c -> sr g c j = rg (cs s c) j) /\ (forall x, sm g x = final s x).
Proof.
  intros p s W Wc RF R (nn & Fn & Cn) EVs.
  destruct (drf_prefix_m2 p s W Wc RF R EVs) as (l & g & Rl & Sp & Sr & Go & Ch).
  exists l, g. split; [auto|]. split; [auto|]. split; [auto|].
  pose proof (I1g p s R) as I. pose proof (I2g p s R) as J.
  (* every write of the history is a slot the run has passed, so it is in l *)
  assert (Wl : forall x y, In y (ids (hs s x)) ->
            exists q e, nth_error l q = Some e /\ writes_x e x = true /\ MIPComp.bt s (sx e) (sk e) = y).
  { intros x y Hy. destruct (j_hist p s J x y Hy) as (EY & iy & AY & WY & EIY & ICY).
    destruct (i_et p s I y EY AY) as (_ & OY).
    assert (EhY : eh EY = false) by (destruct (j_ew p s J _ EY _ AY eq_refl) as [W1 _]; rewrite WY in W1; destruct (eh EY); [discriminate|reflexivity]). rewrite EhY in OY.
    assert (Lp : ek EY < pcs s (ec EY)).
    { destruct (Nat.lt_ge_cases (ek EY) (pcs s (ec EY))) as [L|G]; auto. exfalso.
      destruct (i_pend p s I (ec EY) (ek EY) G ltac:(congruence)) as (_ & Lc).
      rewrite (proj1 (proj2 (Cn (ec EY) Lc) (ek EY) G)) in OY. discriminate. }
    assert (REY : MIPNeg.RE s (ec EY) (ek EY) EY) by (unfold MIPNeg.RE, MIPComp.bt, tmo; rewrite OY; auto).
    destruct (lb_has_write p W s R l g Rl Sp Sr (ec EY) (ek EY) EY x Lp REY WY ltac:(rewrite EIY; auto))
      as (q & e & Q & Xe & Ke & We).
    exists q, e. split; [auto|]. split; [auto|]. rewrite Xe, Ke. unfold MIPComp.bt, tmo. rewrite OY. reflexivity. }
  intros x. unfold final.
  destruct (lw l x) as [w|] eqn:Lw.
  - destruct (lw_spec l x w Lw) as (q & Q & Ww & After).
    assert (Lq : q < length l) by (apply nth_error_Some; congruence).
    rewrite (base_sm p W s R l g Rl Sp Sr q w x Lw Q).
    destruct (lb_write p W s R l g Rl Sp Sr q w x Q Ww) as (_ & _ & _ & _ & InW & _).
    destruct (last_older (hs s x) (MIPComp.bt s (sx w) (sk w)) (j_nodup p s J x) InW) as (gf & r & Er).
    + intros z Iz Nz. destruct (Wl x z Iz) as (q' & e' & Q' & W' & B').
      destruct (Nat.lt_trichotomy q' q) as [L'|[Eq'|G']].
      * rewrite <- B'. apply (Ch q' q e' w x L' Q' Q W' Ww).
      * subst q'. rewrite Q in Q'. injection Q' as <-. congruence.
      * rewrite (After q' e' G' Q') in W'. discriminate.
    + rewrite Er. reflexivity.
  - rewrite (proj1 (srun_mem p W l g Rl x) Lw).
    destruct (rev (hs s x)) as [|[w0 g0] r] eqn:Er; [reflexivity|].
    exfalso. assert (I0 : In w0 (ids (hs s x))).
    { rewrite <- (rev_involutive (hs s x)), Er. unfold ids. rewrite map_rev. apply in_rev.
      rewrite rev_involutive. simpl. left. reflexivity. }
    destruct (Wl x w0 I0) as (q & e & Q & We & _). rewrite (lw_none l x Lw q e Q) in We. discriminate.
Qed.

End Iface.
