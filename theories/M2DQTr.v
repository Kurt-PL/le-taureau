(* M2Trace's Section Tr re-checked on M2DQ (traces of stepQ, via
   M2DQShim). DQ marks the step case analyses: q_rfix and q_sfix change
   neither pcs, ai, oc nor oh, so they are the cases "nothing recorded,
   nothing passed". *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2Snap M2Oota M2Cont M2Trace
  M2DQ M2DQInv M2DQIface M2DQTrace M2DQShim.

Section Tr.
Variable p : prog.
Variable f : nat -> st.
Variable n : nat.
Hypothesis T : trace p f n.

Lemma tr_run : forall i, i <= n -> run p (f i).
Proof. intros i L. apply (trace_run p f n T i L). Qed.

Lemma tr_step : forall i, i < n -> step p (f i) (f (S i)).
Proof. intros i L. apply (proj2 T). auto. Qed.

Lemma tr_ext : forall i j, i <= j -> j <= n -> Ext (f i) (f j).
Proof.
  intros i j L Lj. induction j as [|j IH].
  - assert (i = 0) by lia. subst. apply Ext_refl.
  - destruct (Nat.eq_dec i (S j)) as [->|N]; [apply Ext_refl|].
    apply Ext_trans with (f j); [apply IH; lia|]. apply (Ext_step p); [apply tr_run; lia|apply tr_step; lia].
Qed.

Lemma tr_tm_lt : forall i j, i <= n -> j <= n -> tm (f i) < tm (f j) -> i < j.
Proof.
  intros i j Li Lj H. destruct (Nat.lt_ge_cases i j) as [X|X]; auto.
  pose proof (x_tm _ _ (tr_ext j i X Li)). lia.
Qed.

(* the step that recorded a pending access *)
Lemma early_birth : forall m c k t, m <= n -> pcs (f m) c <= k -> oc (cs (f m) c) k = Some t ->
  exists i d B m' a K u w, i < m /\ tm (f i) = t /\
    pcs (f i) c < k /\ oc (cs (f i) c) k = None /\
    (forall k' d', pending (cs (f i) c) (pcs (f i) c) k' d' -> tied (inst_of d) (inst_of d') -> k' < k) /\
    ((oh (cs (f i) c) k = None /\ early_ok p c (cs (f i) c) (pcs (f i) c) (tp (f i) c) (tm (f i)) d u B) \/
     (exists t1 xs ev nv, oh (cs (f i) c) k = Some t1 /\ d = DCas Plain xs ev nv /\ u = rw (cs (f i) c) k /\
        ai (cs (f i) c) k = crd Plain xs /\
        early_okW p c (cs (f i) c) (pcs (f i) c) (tp (f i) c) (tm (f i)) t1 Plain xs d B)) /\
    (oh (cs (f i) c) k <> None -> w = true) /\ (oh (cs (f i) c) k <> None -> vok (rg (cs (f i) c) k) = true) /\
    eff (tm (f i)) (inst_of d) (rg (cs (f i) c)) (mof (f i) c) m' a K u w /\
    f (S i) = searly (f i) c k d B m' a K u w.
Proof.
  induction m as [|m IH]; intros c k t Lm P O.
  - rewrite (proj1 T) in O. simpl in O. discriminate.
  - destruct (oc (cs (f m) c) k) as [t'|] eqn:Om.
    + pose proof (x_oc _ _ (tr_ext m (S m) ltac:(lia) Lm) c k t' Om) as X. rewrite O in X. injection X as <-.
      pose proof (x_pcs _ _ (tr_ext m (S m) ltac:(lia) Lm) c) as Pc.
      destruct (IH c k t ltac:(lia) ltac:(lia) Om) as (i & d & B & m' & a & K & u & w & A).
      exists i, d, B, m', a, K, u, w. split; [lia|apply A].
    + pose proof (tr_step m ltac:(lia)) as St.
      destruct (stepQ_cases p _ _ St) as [St0|[(cR & kR & BR & ER & _)|(cS & jS & kS & BS & ES & _)]];
        [|exfalso; rewrite ER in O; rewrite oc_bd, oc_cf in O; congruence|exfalso; rewrite ES in O; rewrite oc_cx in O; congruence].
      (* DQ *) destruct (step_cases p _ _ St0) as [(c0 & i0 & m0 & a0 & K0 & u0 & w0 & Hi & Ho & _ & _ & _ & _ & _ & _ & He & _ & E)|[(c0 & k0 & d0 & B0 & m0 & a0 & K0 & u0 & w0 & Lk & Ho & Hso & Hk & HwE & HvE & He & _ & E)|[(c0 & d0 & Ho & _ & _ & _ & _ & _ & E)|[(c0 & k0 & xs0 & B0 & m0 & a0 & K0 & u0 & w0 & bv0 & Lk & Ho & _ & _ & _ & He & _ & E)|[(c0 & K1 & K2 & K3 & _ & K5 & K4 & _ & E)|(cX & jX & bX & BX & oX & HjX & HfX & HcX & E)]]]]].
      * exfalso. rewrite E in O, P. unfold sord, evs in O, P. simpl in O, P. unfold upd in O, P.
        destruct (Nat.eqb_spec c c0); [subst c0|congruence]. simpl in O.
        destruct (Nat.eqb_spec k (pcs (f m) c)) as [X|X]; [lia|congruence].
      * rewrite E in O. unfold searly, set_es, searly0, evs in O. simpl in O. unfold upd in O.
        destruct (Nat.eqb_spec c c0); [subst c0|congruence]. simpl in O.
        destruct (Nat.eqb_spec k k0); [subst k0|congruence]. injection O as <-.
        exists m, d0, B0, m0, a0, K0, u0, w0. repeat split; auto.
      * exfalso. rewrite E in O. unfold smatch in O. simpl in O. unfold upd in O.
        destruct (Nat.eqb_spec c c0); [subst c0|congruence]. simpl in O. congruence.
      * exfalso. rewrite E in O. unfold sread in O. simpl in O. unfold upd in O.
        destruct (Nat.eqb_spec c c0); [subst c0|congruence]. simpl in O. congruence.
      * exfalso. rewrite E in O. rewrite (oc_skip p (f m) c0) in O. congruence.
      * exfalso. rewrite E in O. rewrite oc_cx, oc_flp in O. congruence.
Qed.

(* the step that recorded a CAS's read alone *)
Lemma half_birth : forall m c k t, m <= n -> oh (cs (f m) c) k = Some t ->
  exists i xs B m' a K u w bv, i < m /\ tm (f i) = t /\
    pcs (f i) c <= k /\ oc (cs (f i) c) k = None /\ oh (cs (f i) c) k = None /\
    (forall k' d', pending (cs (f i) c) (pcs (f i) c) k' d' -> tied (crd Plain xs) (inst_of d') -> k' < k) /\
    early_okR p c (cs (f i) c) (pcs (f i) c) (tp (f i) c) (tm (f i)) Plain xs u B /\
    eff (tm (f i)) (ILd Plain xs (fun _ => true)) (rg (cs (f i) c)) (mof (f i) c) m' a K u w /\
    f (S i) = sread (f i) c k Plain xs B m' a K u w bv.
Proof.
  induction m as [|m IH]; intros c k t Lm O.
  - rewrite (proj1 T) in O. simpl in O. discriminate.
  - destruct (oh (cs (f m) c) k) as [t'|] eqn:Om.
    + pose proof (x_oh _ _ (tr_ext m (S m) ltac:(lia) Lm) c k t' Om) as X. rewrite O in X. injection X as <-.
      destruct (IH c k t ltac:(lia) Om) as (i & xs & B & m' & a & K & u & w & bv & A).
      exists i, xs, B, m', a, K, u, w, bv. split; [lia|apply A].
    + pose proof (tr_step m ltac:(lia)) as St.
      destruct (stepQ_cases p _ _ St) as [St0|[(cR & kR & BR & ER & _)|(cS & jS & kS & BS & ES & _)]];
        [|exfalso; rewrite ER in O; rewrite oh_bd, oh_cf in O; congruence|exfalso; rewrite ES in O; rewrite oh_cx in O; congruence].
      (* DQ *) destruct (step_cases p _ _ St0) as [(c0 & i0 & m0 & a0 & K0 & u0 & w0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E)|[(c0 & k0 & d0 & B0 & m0 & a0 & K0 & u0 & w0 & _ & _ & _ & _ & _ & _ & _ & _ & E)|[(c0 & d0 & _ & _ & _ & _ & _ & _ & E)|[(c0 & k0 & xs0 & B0 & m0 & a0 & K0 & u0 & w0 & bv0 & Lk & Ho & Hoh & Hso & Hok & He & _ & E)|[(c0 & K1 & K2 & K3 & _ & K5 & K4 & _ & E)|(cX & jX & bX & BX & oX & HjX & HfX & HcX & E)]]]]].
      * exfalso. rewrite E in O. unfold sord in O. rewrite oh_s' in O. congruence.
      * exfalso. rewrite E in O. unfold searly, set_es, searly0, evs in O. simpl in O. unfold upd in O.
        destruct (Nat.eqb_spec c c0); [subst; simpl in O; congruence|congruence].
      * exfalso. rewrite E in O. rewrite oh_match in O. congruence.
      * rewrite E in O. unfold sread in O. simpl in O. unfold upd in O.
        destruct (Nat.eqb_spec c c0); [subst c0|congruence]. simpl in O.
        destruct (Nat.eqb_spec k k0); [subst k0|congruence]. injection O as <-.
        exists m, xs0, B0, m0, a0, K0, u0, w0, bv0. repeat split; auto.
      * exfalso. rewrite E in O. rewrite (oh_skip p (f m) c0) in O. congruence.
      * exfalso. rewrite E in O. rewrite oh_cx, oh_flp in O. congruence.
Qed.

(* the step that passed a slot *)
Lemma pass_birth : forall m c k, m <= n -> k < pcs (f m) c ->
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
    + pose proof (tr_step m ltac:(lia)) as St. exists m. split; [lia|].
      destruct (stepQ_cases p _ _ St) as [St'|[(cR & kR & BR & ER & _)|(cS & jS & kS & BS & ES & _)]];
        [|exfalso; rewrite ER in P; simpl in P; lia|exfalso; rewrite ES in P; simpl in P; lia].
      (* DQ *) destruct (step_cases p _ _ St') as [(c0 & i0 & m0 & a0 & K0 & u0 & w0 & Hi & Ho & Hd & Hb & Hbh & Hbd & _ & HvO & He & _ & E)|[(c0 & k0 & d0 & B0 & m0 & a0 & K0 & u0 & w0 & Lk & Ho & Hso & Hk & _ & _ & He & _ & E)|[(c0 & d0 & Ho & Ha & Hdf & Hd & Hfm & Hfh & E)|[(c0 & k0 & xs0 & B0 & m0 & a0 & K0 & u0 & w0 & bv0 & Lk & Ho & _ & _ & _ & He & _ & E)|[(c0 & K1 & K2 & K3 & K6 & K5 & K4 & _ & E)|(cX & jX & bX & BX & oX & HjX & HfX & HcX & E)]]]]].
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

(* a CAS whose read happened alone and which committed to failure never
   writes, and keeps its verdict *)
Lemma half_fail_stays : forall m m' c k t, m <= m' -> m' <= n -> oh (cs (f m) c) k = Some t ->
  oc (cs (f m) c) k = None -> pcs (f m) c <= k -> vok (rg (cs (f m) c) k) = false ->
  oc (cs (f m') c) k = None.
Proof.
  intros m m' c k t L1 L2 Oh Oc Pk Vk.
  assert (Ea : forall m1, m <= m1 -> m1 <= n -> pcs (f m1) c <= k -> oc (cs (f m1) c) k = None).
  { intros m1 La Lb Pm. destruct (oc (cs (f m1) c) k) as [y|] eqn:Oy; [|reflexivity]. exfalso.
    destruct (early_birth m1 c k y Lb Pm Oy) as (i & d & B & m2 & a & K & u & w & Li & Ti & Pi & Oi & _ & _ & _ & Vi & _ & E).
    destruct (Nat.lt_ge_cases i m) as [Lim|Lim].
    - assert (O1 : oc (cs (f (S i)) c) k = Some (tm (f i))).
      { rewrite E. unfold searly, set_es, searly0, evs; simpl. rewrite !upd_eq'. simpl. rewrite !upd_eq'. reflexivity. }
      rewrite (x_oc _ _ (tr_ext (S i) m ltac:(lia) ltac:(lia)) c k _ O1) in Oc. discriminate.
    - assert (Xi : Ext (f m) (f i)) by (apply tr_ext; lia).
      pose proof (x_oh _ _ Xi c k t Oh) as Ohi.
      destruct (x_rgh _ _ Xi c k ltac:(congruence) ltac:(lia)) as [R|(R & _)]; [|congruence].
      rewrite R, Vk in Vi. specialize (Vi ltac:(congruence)). discriminate. }
  destruct (Nat.le_gt_cases (pcs (f m') c) k) as [Pm|Pm]; [apply Ea; lia|].
  destruct (pass_birth m' c k L2 Pm) as (q & Lq & Pq & PSq & Cs).
  assert (Lmq : m <= q).
  { destruct (Nat.le_gt_cases m q) as [X|X]; auto. exfalso.
    pose proof (x_pcs _ _ (tr_ext (S q) m ltac:(lia) ltac:(lia)) c). lia. }
  assert (Xq : Ext (f m) (f q)) by (apply tr_ext; lia).
  assert (Oq : oc (cs (f q) c) k = None) by (apply Ea; lia).
  destruct Cs as [(i0 & m1 & a & K & u & w & _ & _ & _ & _ & _ & _ & Hv & _ & E)|[(d & Ho & _)|(_ & _ & _ & _ & _ & _ & E)]].
  - exfalso. cbv zeta in Hv. pose proof (x_oh _ _ Xq c k t Oh) as Ohq.
    destruct (x_rgh _ _ Xq c k ltac:(congruence) ltac:(lia)) as [R|(R & _)]; [|congruence].
    rewrite R, Vk in Hv. specialize (Hv ltac:(congruence)). discriminate.
  - exfalso. cbv zeta in Ho. congruence.
  - assert (O1 : oc (cs (f (S q)) c) k = None) by (rewrite E; rewrite (oc_skip p (f q) c); exact Oq).
    apply (x_ocp _ _ (tr_ext (S q) m' ltac:(lia) L2) c k ltac:(lia) O1).
Qed.

Lemma half_fail_vok : forall m m' c k t, m <= m' -> m' <= n -> oh (cs (f m) c) k = Some t ->
  oc (cs (f m) c) k = None -> pcs (f m) c <= k -> vok (rg (cs (f m) c) k) = false ->
  vok (rg (cs (f m') c) k) = false.
Proof.
  intros m m' c k t L1 L2 Oh Oc Pk Vk.
  assert (Xm : Ext (f m) (f m')) by (apply tr_ext; lia).
  destruct (Nat.le_gt_cases (pcs (f m') c) k) as [Pm|Pm].
  - destruct (x_rgh _ _ Xm c k ltac:(congruence) Pm) as [R|(R & _)]; [rewrite R; exact Vk|congruence].
  - apply (i_halfv p (f m') (Inv1_run p (f m') (tr_run m' L2)) c k t); [|apply (x_oh _ _ Xm c k t Oh)|exact Pm].
    apply (half_fail_stays m m' c k t L1 L2 Oh Oc Pk Vk).
Qed.

(* a pending access stays pending with its effect, or is passed by the
   programme's instruction, which does the same *)
Lemma pend_fate : forall i m c j d, i <= m -> m <= n -> wf p ->
  oc (cs (f i) c) j <> None -> pcs (f i) c <= j -> ai (cs (f i) c) j = inst_of d ->
  (pcs (f m) c <= j /\ ai (cs (f m) c) j = inst_of d) \/
  (j < pcs (f m) c /\ eof (ins p c j (rg (cs (f m) c))) (rg (cs (f m) c)) = Some d).
Proof.
  intros i m c j d Lim Lm W O P A. induction m as [|m IH].
  - assert (i = 0) by lia. subst. left. auto.
  - destruct (Nat.eq_dec i (S m)) as [->|Ni]; [left; auto|].
    assert (Rm : run p (f m)) by (apply tr_run; lia).
    pose proof (Inv1_run p (f m) Rm) as I.
    pose proof (Ext_step p (f m) (f (S m)) Rm (tr_step m ltac:(lia))) as X.
    assert (Om : oc (cs (f m) c) j <> None).
    { destruct (oc (cs (f i) c) j) eqn:E; [|congruence].
      rewrite (x_oc _ _ (tr_ext i m ltac:(lia) ltac:(lia)) c j n0 E). discriminate. }
    destruct (IH ltac:(lia) ltac:(lia)) as [(Q1 & Q2)|(Q1 & Q2)].
    + destruct (stepQ_cases p _ _ (tr_step m ltac:(lia))) as [St0|[(cR & kR & BR & ER & _)|(cS & jS & kS & BS & ES & _)]];
        [|left; split; [rewrite ER; simpl; lia|rewrite ER, ai_bd, ai_cf; exact Q2]
         |left; split; [rewrite ES; simpl; lia|rewrite ES, ai_cx; exact Q2]].
      (* DQ *) destruct (step_cases p _ _ St0) as [(c0 & i0 & m0 & a0 & K0 & u0 & w0 & Hi & Ho & _ & _ & _ & _ & _ & _ & He & _ & E)|[(c0 & k0 & d0 & B0 & m0 & a0 & K0 & u0 & w0 & Lk & Ho & _ & _ & _ & _ & He & _ & E)|[(c0 & d0 & Ho & Ha & Hdf & Hd & _ & _ & E)|[(c0 & k0 & xs0 & B0 & m0 & a0 & K0 & u0 & w0 & bv0 & Lk & Ho & _ & _ & _ & He & _ & E)|[(c0 & K1 & K2 & K3 & _ & K5 & K4 & _ & E)|(cX & jX & bX & BX & oX & HjX & HfX & HcX & E)]]]]].
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

End Tr.
