(* The trace fields g_birth and g_pending_cells of
   M2Iface.M2Guarantees for M2DQ (stepQ). The record fixes q_rfix and q_sfix
   change neither pcs nor ai, so in M2Trace.pass_birth and M2Trace.pend_fate
   they are the cases "no slot passed" and "the pending access stays";
   q_old runs the old scripts. *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO M2Oota M2Cont M2Snap M2Trace M2PComp
  M2Iface M2DA M2DP M2DQ M2DQInv M2DQIface.

Lemma stepQ_cases : forall p s t, stepQ p s t -> step p s t \/
  (exists c k B, t = sbd (scfail s c k) c B /\ rfail_ok p c (cs s c) (pcs s c) (tp s c) k B) \/
  (exists c j k B, t = scfix0 s c j true B /\ pcs s c <= j /\ fx (cs s c) j = None /\
     sfix_ok p c (cs s c) (pcs s c) (tp s c) j k B).
Proof.
  intros p s t S. destruct S as [s t S _|s c k B Ok _|s c j k B Hj Hf Ok].
  - left. exact S.
  - right; left. exists c, k, B. split; [reflexivity|exact Ok].
  - right; right. exists c, j, k, B. auto.
Qed.

Section TrQ.
Variables (p : prog) (f : nat -> st) (n : nat).
Hypothesis T : gtrace (stepQ p) f n.

Lemma trq_reach : forall i, i <= n -> reach (stepQ p) (f i).
Proof.
  intros i L. induction i as [|i IH]; [rewrite (proj1 T); constructor|].
  apply reS with (f i); [apply IH; lia|apply (proj2 T); lia].
Qed.
Lemma trq_run : forall i, i <= n -> runQ p (f i).
Proof. intros i L. apply reach_runQ. apply trq_reach. exact L. Qed.
Lemma trq_step : forall i, i < n -> stepQ p (f i) (f (S i)).
Proof. intros i L. apply (proj2 T). exact L. Qed.
Lemma trq_keep : forall i, i < n -> Ext (f i) (f (S i)).
Proof. intros i L. apply (gq_keeps p); [apply trq_reach; lia|apply trq_step; exact L]. Qed.
Lemma trq_ext : forall i j, i <= j -> j <= n -> Ext (f i) (f j).
Proof.
  intros i j L Lj. induction j as [|j IH].
  - assert (i = 0) by lia. subst. apply Ext_refl.
  - destruct (Nat.eq_dec i (S j)) as [->|N]; [apply Ext_refl|].
    apply Ext_trans with (f j); [apply IH; lia|apply trq_keep; lia].
Qed.

Lemma pass_birthQ : forall m c k, m <= n -> k < pcs (f m) c ->
  exists i, i < m /\ pcs (f i) c = k /\ pcs (f (S i)) c = S k /\
    ((exists i0 m' a K u w, let cc := cs (f i) c in
       ins p c k (rg cc) = i0 /\ oc cc k = None /\ determined p cc c k i0 /\
       (executes i0 (rg cc) = true -> forall k' d, pending cc k k' d -> ~ tied i0 (inst_of d)) /\
       (executes i0 (rg cc) = true -> forall k' m xs, hpending cc k k' m xs -> k' <> k -> ~ tied i0 (crd m xs)) /\
       ((oh cc k = None /\
         forall x b, bd cc k = true -> In x (icells i0) -> fbinder p c (rg cc) k x = Some b -> u x = rw cc b x) \/
        (exists t1, oh cc k = Some t1 /\ is_cas i0 = true /\ u = rw cc k /\ eofR i0 (rg cc) = eofR (ai cc k) (rg cc))) /\
       (oh cc k <> None -> vok (rg cc k) = true) /\
       eff (tm (f i)) i0 (rg cc) (mof (f i) c) m' a K u w /\ f (S i) = sord (f i) c i0 m' a K u w) \/
     (exists d, let cc := cs (f i) c in
       oc cc k <> None /\ ai cc k = inst_of d /\ eof (ins p c k (rg cc)) (rg cc) = Some d /\
       determined p cc c k (ins p c k (rg cc)) /\
       (forall k' d' t t', pending cc k k' d' -> k' <> k -> oc cc k = Some t -> oc cc k' = Some t' ->
          tied (inst_of d) (inst_of d') -> t < t') /\
       (forall k' m xs t t', hpending cc k k' m xs -> k' <> k -> oc cc k = Some t -> oh cc k' = Some t' ->
          tied (inst_of d) (crd m xs) -> t < t') /\ f (S i) = smatch p (f i) c) \/
     (let cc := cs (f i) c in
       xex cc (ins p c k (rg cc)) (rg cc) k = false /\ oc cc k = None /\
       (oh cc k <> None -> eofR (ins p c k (rg cc)) (rg cc) = eofR (ai cc k) (rg cc)) /\
       (oh cc k <> None -> vok (rg cc k) = false) /\
       hfirst cc k (ins p c k (rg cc)) /\
       determined p cc c k (ins p c k (rg cc)) /\ f (S i) = sskip p (f i) c)).
Proof.
  induction m as [|m IH]; intros c k Lm P.
  - rewrite (proj1 T) in P. simpl in P. lia.
  - destruct (Nat.lt_ge_cases k (pcs (f m) c)) as [Q|Q].
    + destruct (IH c k ltac:(lia) Q) as (i & A). exists i. split; [lia|apply A].
    + exists m. split; [lia|].
      destruct (stepQ_cases p _ _ (trq_step m ltac:(lia))) as [St|[(cR & kR & BR & ER & _)|(cS & jS & kS & BS & ES & _)]];
        [|exfalso; rewrite ER in P; simpl in P; lia|exfalso; rewrite ES in P; simpl in P; lia].
      destruct (step_cases p _ _ St) as [(c0 & i0 & m0 & a0 & K0 & u0 & w0 & Hi & Ho & Hd & Hb & Hbh & Hbd & _ & HvO & He & _ & E)|[(c0 & k0 & d0 & B0 & m0 & a0 & K0 & u0 & w0 & Lk & Ho & Hso & Hk & _ & _ & He & _ & E)|[(c0 & d0 & Ho & Ha & Hdf & Hd & Hfm & Hfh & E)|[(c0 & k0 & xs0 & B0 & m0 & a0 & K0 & u0 & w0 & bv0 & Lk & Ho & _ & _ & _ & He & _ & E)|[(c0 & K1 & K2 & K3 & K6 & K5 & K4 & _ & E)|(cX & jX & bX & BX & oX & HjX & HfX & HcX & E)]]]]].
      * assert (Pc : pcs (f (S m)) c = upd (pcs (f m)) c0 (S (pcs (f m) c0)) c) by (rewrite E; reflexivity).
        rewrite Pc in P |- *. unfold upd in P |- *.
        destruct (Nat.eqb_spec c c0); [subst c0|lia].
        assert (k = pcs (f m) c) by lia. subst k. split; auto. split; auto.
        left. exists i0, m0, a0, K0, u0, w0. cbv zeta. exact (conj Hi (conj Ho (conj Hd (conj Hb (conj Hbh (conj Hbd (conj HvO (conj He E)))))))).
      * exfalso. rewrite E in P. unfold searly, set_es, searly0, evs in P. simpl in P. lia.
      * assert (Pc : pcs (f (S m)) c = upd (pcs (f m)) c0 (S (pcs (f m) c0)) c) by (rewrite E; reflexivity).
        rewrite Pc in P |- *. unfold upd in P |- *.
        destruct (Nat.eqb_spec c c0); [subst c0|lia].
        assert (k = pcs (f m) c) by lia. subst k. split; auto. split; auto.
        right; left. exists d0. cbv zeta. exact (conj Ho (conj Ha (conj Hdf (conj Hd (conj Hfm (conj Hfh E)))))).
      * exfalso. rewrite E in P. unfold sread in P. simpl in P. lia.
      * assert (Pc : pcs (f (S m)) c = upd (pcs (f m)) c0 (S (pcs (f m) c0)) c) by (rewrite E; reflexivity).
        rewrite Pc in P |- *. unfold upd in P |- *.
        destruct (Nat.eqb_spec c c0); [subst c0|lia].
        assert (k = pcs (f m) c) by lia. subst k. split; auto. split; auto.
        right; right. cbv zeta. exact (conj K1 (conj K2 (conj K3 (conj K6 (conj K5 (conj K4 E)))))).
      * exfalso. assert (Pc : pcs (f (S m)) c = pcs (f m) c) by (rewrite E; unfold scfix0; cbn [pcs]; rewrite pcs_flp; reflexivity). lia.
Qed.


Lemma pend_fateQ : forall i m c j d, i <= m -> m <= n -> wf p ->
  oc (cs (f i) c) j <> None -> pcs (f i) c <= j -> ai (cs (f i) c) j = inst_of d ->
  (pcs (f m) c <= j /\ ai (cs (f m) c) j = inst_of d) \/
  (j < pcs (f m) c /\ eof (ins p c j (rg (cs (f m) c))) (rg (cs (f m) c)) = Some d).
Proof.
  intros i m c j d Lim Lm W O P A. induction m as [|m IH].
  - assert (i = 0) by lia. subst. left. auto.
  - destruct (Nat.eq_dec i (S m)) as [->|Ni]; [left; auto|].
    pose proof (trq_keep m ltac:(lia)) as X.
    assert (Om : oc (cs (f m) c) j <> None).
    { destruct (oc (cs (f i) c) j) eqn:E; [|congruence].
      rewrite (x_oc _ _ (trq_ext i m ltac:(lia) ltac:(lia)) c j n0 E). discriminate. }
    destruct (IH ltac:(lia) ltac:(lia)) as [(Q1 & Q2)|(Q1 & Q2)].
    + destruct (stepQ_cases p _ _ (trq_step m ltac:(lia))) as [St|[(cR & kR & BR & ER & _)|(cS & jS & kS & BS & ES & _)]];
        [|left; split; [rewrite ER; simpl; lia|rewrite ER, ai_bd, ai_cf; exact Q2]
         |left; split; [rewrite ES; simpl; lia|rewrite ES, ai_cx; exact Q2]].
      destruct (step_cases p _ _ St) as [(c0 & i0 & m0 & a0 & K0 & u0 & w0 & Hi & Ho & _ & _ & _ & _ & _ & _ & He & _ & E)|[(c0 & k0 & d0 & B0 & m0 & a0 & K0 & u0 & w0 & Lk & Ho & _ & _ & _ & _ & He & _ & E)|[(c0 & d0 & Ho & Ha & Hdf & Hd & _ & _ & E)|[(c0 & k0 & xs0 & B0 & m0 & a0 & K0 & u0 & w0 & bv0 & Lk & Ho & _ & _ & _ & He & _ & E)|[(c0 & K1 & K2 & K3 & _ & K5 & K4 & _ & E)|(cX & jX & bX & BX & oX & HjX & HfX & HcX & E)]]]]].
      * left. split.
        -- assert (Pc : pcs (f (S m)) c = upd (pcs (f m)) c0 (S (pcs (f m) c0)) c) by (rewrite E; reflexivity).
           rewrite Pc. unfold upd. destruct (Nat.eqb_spec c c0); [subst c0|lia].
           destruct (Nat.eq_dec j (pcs (f m) c)) as [->|Nj]; [congruence|lia].
        -- rewrite (x_aip _ _ X c j Om); auto.
           assert (Pc : pcs (f (S m)) c = upd (pcs (f m)) c0 (S (pcs (f m) c0)) c) by (rewrite E; reflexivity).
           rewrite Pc. unfold upd. destruct (Nat.eqb_spec c c0); [subst c0|lia].
           destruct (Nat.eq_dec j (pcs (f m) c)) as [->|Nj]; [congruence|lia].
      * left. assert (Pc : pcs (f (S m)) c = pcs (f m) c) by (rewrite E; reflexivity).
        split; [lia|]. rewrite (x_aip _ _ X c j Om); [auto|lia].
      * assert (Pc : pcs (f (S m)) c = upd (pcs (f m)) c0 (S (pcs (f m) c0)) c) by (rewrite E; reflexivity).
        destruct (Nat.eq_dec c c0) as [<-|Nc].
        -- destruct (Nat.eq_dec j (pcs (f m) c)) as [->|Nj].
           ++ right. rewrite Pc, upd_eq'. split; [lia|].
              assert (Rg : rg (cs (f (S m)) c) = rg (cs (f m) c)) by (rewrite E; unfold smatch; simpl; rewrite upd_eq'; reflexivity).
              rewrite Rg. rewrite Q2 in Ha. apply inst_of_inj in Ha. subst d0. exact Hdf.
           ++ left. rewrite Pc, upd_eq'. split; [lia|]. rewrite (x_aip _ _ X c j Om); [auto|]. rewrite Pc, upd_eq'. lia.
        -- left. rewrite Pc. unfold upd. destruct (Nat.eqb_spec c c0); [congruence|].
           split; [auto|]. rewrite (x_aip _ _ X c j Om); [auto|]. rewrite Pc. unfold upd.
           destruct (Nat.eqb_spec c c0); [congruence|auto].
      * left. assert (Pc : pcs (f (S m)) c = pcs (f m) c) by (rewrite E; reflexivity).
        split; [lia|]. rewrite (x_aip _ _ X c j Om); [auto|lia].
      * left. assert (Pc : pcs (f (S m)) c = upd (pcs (f m)) c0 (S (pcs (f m) c0)) c) by (rewrite E; reflexivity).
        assert (Nj : c <> c0 \/ j <> pcs (f m) c0).
        { destruct (Nat.eq_dec c c0) as [<-|Nc]; [right; intros Z; rewrite Z in Om; congruence|left; exact Nc]. }
        split.
        -- rewrite Pc. unfold upd. destruct (Nat.eqb_spec c c0); [subst c0|lia]. destruct Nj as [Nj|Nj]; [congruence|lia].
        -- rewrite (x_aip _ _ X c j Om); [auto|]. rewrite Pc. unfold upd. destruct (Nat.eqb_spec c c0); [subst c0|lia].
           destruct Nj as [Nj|Nj]; [congruence|lia].
      * left. assert (Pc : pcs (f (S m)) c = pcs (f m) c) by (rewrite E; unfold scfix0; cbn [pcs]; rewrite pcs_flp; reflexivity).
        split; [lia|]. rewrite (x_aip _ _ X c j Om); [auto|lia].
    + right. split; [pose proof (x_pcs _ _ X c); lia|].
      assert (Ag : forall j', j' < j -> rg (cs (f (S m)) c) j' = rg (cs (f m) c) j').
      { intros j' L. apply (x_rg _ _ X). left. lia. }
      destruct (W c j (rg (cs (f (S m)) c)) (rg (cs (f m) c)) Ag) as [E1 E2].
      rewrite E1 in E2 |- *. rewrite (eof_ieval _ _ _ E2). exact Q2.
Qed.

End TrQ.

Section IQ.
Variable p : prog.
Lemma i_birthQ : wf p -> forall f n, gtrace (stepQ p) f n -> forall c k, k < pcs (f n) c ->
  exists ih, ih < n /\ pcs (f ih) c = k /\ M2PComp.bt (f n) c k <= tm (f ih).
Proof.
  intros W f n T c k Lk.
  destruct (pass_birthQ p f n T n c k (le_n n) Lk) as (ih & Lih & Pih & PSih & Cs).
  assert (Rsb : runQ p (f ih)) by (apply (trq_run p f n T); lia).
  pose proof (s1 p _ (IS_run p _ Rsb)) as Isb.
  assert (X : Ext (f ih) (f n)) by (apply (trq_ext p f n T); lia).
  exists ih. split; [exact Lih|]. split; [exact Pih|].
  destruct Cs as [(i0 & m' & a & K & u & w & _ & Ho & _ & _ & _ & _ & _ & _ & E)|[(d & Ho & _ & _ & _ & _ & _ & E)|(Kx & Ko & Kh & Kv & Kf & Kd & E)]].
  - assert (O1 : oc (cs (f (S ih)) c) k = Some (tm (f ih))).
    { rewrite E. unfold sord, evs. simpl. rewrite upd_eq'. simpl. rewrite Pih, upd_eq'. reflexivity. }
    assert (X1 : Ext (f (S ih)) (f n)) by (apply (trq_ext p f n T); lia).
    pose proof (x_oc _ _ X1 c k _ O1) as O2. unfold M2PComp.bt, tmo. rewrite O2. lia.
  - cbv zeta in Ho. destruct (oc (cs (f ih) c) k) as [t0|] eqn:O0; [|congruence].
    pose proof (oc_lt_tm p (f ih) c k t0 Isb O0) as Lt0. pose proof (x_oc _ _ X c k t0 O0) as O2.
    unfold M2PComp.bt, tmo. rewrite O2. lia.
  - (* passed without happening: it never happens; a CAS that failed keeps its read's time *)
    cbv zeta in Ko. try rewrite Pih in Ko.
    assert (O1 : oc (cs (f (S ih)) c) k = None) by (rewrite E, (oc_skip p (f ih) c); exact Ko).
    assert (P1 : k < pcs (f (S ih)) c) by (rewrite E, (pcs_skip p (f ih) c), Nat.eqb_refl; lia).
    assert (X1 : Ext (f (S ih)) (f n)) by (apply (trq_ext p f n T); lia).
    pose proof (x_ocp _ _ X1 c k P1 O1) as O2. unfold M2PComp.bt, tmo. rewrite O2.
    destruct (oh (cs (f (S ih)) c) k) as [t0|] eqn:Oh1.
    + rewrite (x_oh _ _ X1 c k t0 Oh1). rewrite E, (oh_skip p (f ih) c) in Oh1.
      pose proof (oh_lt_tm p (f ih) c k t0 Isb Oh1). lia.
    + rewrite (x_ohp _ _ X1 c k P1 Oh1). lia.
Qed.

Lemma i_pending_cellsQ : wf p -> forall f n, gtrace (stepQ p) f n -> forall ih cu ku, ih <= n -> pcs (f ih) cu <= ku ->
  oc (cs (f ih) cu) ku <> None -> icells (ai (cs (f ih) cu) ku) = icells (ai (cs (f n) cu) ku).
Proof.
  intros W f n T ih cu ku L P O.
  assert (Ri : runQ p (f ih)) by (apply (trq_run p f n T); lia).
  assert (Rn : runQ p (f n)) by (apply (trq_run p f n T); lia).
  destruct (i_pend p (f ih) (s1 p _ (IS_run p _ Ri)) cu ku P O) as ((d & Ad & _) & _).
  destruct (pend_fateQ p f n T ih n cu ku d L (le_n n) W O P Ad) as [(_ & An)|(Ln & Dn)].
  - rewrite Ad, An. reflexivity.
  - destruct (proj1 (i_cmA p (f n) (s1 p _ (IS_run p _ Rn)) cu ku) Ln) as (tau & Tc).
    rewrite (proj2 (i_set p (f n) (s1 p _ (IS_run p _ Rn)) cu ku tau Tc)). rewrite Ad.
    rewrite (eof_icells _ _ _ Dn). reflexivity.
Qed.

End IQ.

Print Assumptions i_birthQ.
Print Assumptions i_pending_cellsQ.
