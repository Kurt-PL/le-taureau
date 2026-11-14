(* CASHoistX stays excluded on model M2DQ (stepQ).
     r0 = y; if r0 == 5 { r1 = CAS(x, 0, 5) } else { r2 = CAS(w, 0, 7) }; z = r1 + r2
       || r = z; y = r || x = 5
   with r0 = 5 and r1 = 5 (M2CasHoistXNeg). The M2 proof carries over: its
   generic lemmas are re-checked on runQ through M2DQShim (M2DQComp, M2DQNeg,
   ported unchanged; readv, neq_bt, inop_after, ai_passed copied unchanged),
   the trace lemmas are M2DQTr's, and the one step induction (inv_q) gains the
   two record fixes q_rfix and q_sfix. Both change neither pcs, oc, oh nor ai
   (sbd, scfail, scfix0), so "before r0 is read, context 0 has no read alone
   and only z = 0 early" holds along runQ as along run. The programme-level
   lemmas (early_q, read_q, val_r0X, ...) are M2CasHoistXNeg's: they speak of
   one context state, not of runs. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2Lit M2Oota M2Snap M2Ev M2Cont M2Trace M2CasFwd M2CasHoistXNeg
  M2DQComp M2DQNeg M2DA M2DP M2DQ M2DQInv M2DQIface M2DQTrace M2DQTr M2DQShim.

(* ---------- generic lemmas on runQ, scripts as in M2LitNeg / M2CasFwd ---------- *)
Lemma readv : forall (p : prog) (s : M2Model.st) (R : run p s) (CP : done p s) (W : wf p) c k i x E v, ins p c k (rrg s c) = i -> xload i (rrg s c) = true ->
  icells i = [x] -> RE s c k E -> einstr p s E = i -> rval i (rg (cs s c) k) = v -> v <> 0 ->
  exists y, erf E x = Some y /\ wv s y x = v /\ In y (ids (hs s x)) /\ y < bt s c k.
Proof.
  intros p s R CP W c k i x E v H X Ic RE0 Ei Rv N.
  destruct (n_rd p s R CP W c k i x E H X (one_in _ _ Ic) RE0 Ei) as (V & Rf).
  rewrite Ic in V. rewrite Rv in V. unfold rdvs, rdv in V. simpl in V.
  destruct (erf E x) as [y|] eqn:Ey; [|congruence].
  destruct (Rf y eq_refl). exists y. repeat split; auto; congruence.
Qed.

Lemma neq_bt : forall (p : prog) (s : M2Model.st) (R : run p s) (CP : done p s) (W : wf p) c1 k1 c2 k2 i1 i2,
  ins p c1 k1 (rrg s c1) = i1 -> i1 <> INop -> executes i1 (rrg s c1) = true ->
  ins p c2 k2 (rrg s c2) = i2 -> i2 <> INop -> executes i2 (rrg s c2) = true ->
  (c1, k1) <> (c2, k2) -> bt s c1 k1 <> bt s c2 k2.
Proof.
  intros p s R CP W c1 k1 c2 k2 i1 i2 H1 N1 X1 H2 N2 X2 N E.
  destruct (bt_inj p s R CP W _ _ _ _ _ _ (n_insr p s R CP W _ _ _ H1 N1) (n_insr p s R CP W _ _ _ H2 N2) X1 X2 E).
  congruence.
Qed.

Lemma inop_after : forall p s c i ti j tj, run p s -> done p s -> wf p -> oc (cs s c) i = Some ti ->
  ins p c i (rg (cs s c)) = INop -> j <= i -> executes (ins p c j (rg (cs s c))) (rg (cs s c)) = true ->
  oc (cs s c) j = Some tj -> tj <= ti.
Proof.
  intros p s c i ti j tj R CP W Oi Ii L Xj Oj. pose proof (Inv1_run p s R) as I.
  assert (Lp : i < pcs s c) by (apply (passed p s R CP W); congruence).
  destruct (proj1 (i_cmA p s I c i) Lp) as (tau & T0).
  pose proof (i_cmF p s I c i tau T0 ltac:(rewrite Ii; reflexivity) ltac:(rewrite Ii; reflexivity)) as Ot. assert (ti = tau) by congruence. subst ti.
  destruct (i_cmDt p s I c i tau T0 j L Xj) as (t' & Oj' & Le). unfold tmo in Oj'. rewrite Oj in Oj'. injection Oj' as <-. exact Le.
Qed.

(* the instruction that acted at a slot passed *)
Lemma ai_passed : forall p s c k, run p s -> done p s -> wf p -> oc (cs s c) k <> None ->
  ai (cs s c) k = ins p c k (rg (cs s c)).
Proof.
  intros p s c k R CP W O. pose proof (Inv1_run p s R) as I.
  destruct (proj1 (i_cmA p s I c k) (passed p s R CP W c k O)) as (tau & T0).
  apply (proj2 (i_set p s I c k tau T0)).
Qed.


Lemma run_traceQ : forall p s, runQ p s -> exists f n, traceQ p f n /\ f n = s.
Proof.
  intros p s R. induction R as [|s s' R IH St].
  - exists (fun _ => sinit), 0. split; [split; [auto|intros; lia]|auto].
  - destruct IH as (f & n & [A B] & E).
    exists (fun i => if Nat.leb i n then f i else s'), (S n). split; [split|].
    + simpl. auto.
    + intros i Li. destruct (Nat.leb_spec i n); [|lia].
      destruct (Nat.leb_spec (S i) n).
      * apply B. lia.
      * assert (i = n) by lia. subst i. rewrite E. auto.
    + destruct (Nat.leb_spec (S n) n); [lia|auto].
Qed.

(* ---------- context 0 before its first read, along runQ ---------- *)
Lemma inv_qQ : forall s, runQ CASHoistX s -> pcs s 0 = 0 -> Q (cs s 0).
Proof.
  intros s R. induction R as [|s t R IH HQ].
  - intros _. split; [intros k; reflexivity|intros k t O; discriminate O].
  - intros Pt. assert (Ps : pcs s 0 = 0) by (pose proof (x_pcs _ _ (Ext_step CASHoistX s t R HQ) 0); lia).
    specialize (IH Ps). destruct IH as [Ih Io].
    destruct (stepQ_cases _ _ _ HQ) as [H|[(cR & kR & BR & ER & _)|(cS & jS & kS & BS & ES & _)]].
    2: { (* DQ: q_rfix changes neither oc, oh nor ai *)
         subst t. split; [intros k; rewrite oh_bd, oh_cf; apply Ih|intros k t0 O; rewrite oc_bd, oc_cf in O; rewrite ai_bd, ai_cf; apply (Io k t0 O)]. }
    2: { (* DQ: q_sfix changes neither oc, oh nor ai *)
         subst t. split; [intros k; rewrite oh_cx; apply Ih|intros k t0 O; rewrite oc_cx in O; rewrite ai_cx; apply (Io k t0 O)]. }
    destruct (step_cases _ _ _ H) as [(c & i & m' & a & K & u & w & X)|[(c & k & d & B & m' & a & K & u & w & X)|[(c & d & H1 & H2 & H3 & H4 & H4m & Hfh & ->)|[(c & k & xs & B & m' & a & K & u & w & bv & X)|[(c & S1 & S2 & S3 & _ & S5 & S4 & _ & ->)|(cX & jX & bX & BX & oX & HjX & HfX & HcX & ->)]]]]].
    + destruct X as (H1 & H2 & H3 & H4 & H4h & Hh & _ & _ & H5 & _ & ->).
      destruct (Nat.eq_dec c 0) as [->|Nc].
      * exfalso. unfold sord, evs in Pt; simpl in Pt. unfold upd in Pt. simpl in Pt. lia.
      * unfold sord, evs; simpl. rewrite upd_neq by auto. split; auto.
    + destruct X as (H1 & H2 & Hso & Hh & _ & _ & H5 & _ & ->).
      destruct (Nat.eq_dec c 0) as [->|Nc].
      * destruct Hh as [(Oh & Ok)|(t1 & xs & ev & nv & Oh & _)]; [|rewrite Ih in Oh; discriminate].
        rewrite Ps in Ok. pose proof (early_q _ _ _ _ _ _ (conj Ih Io) Ok) as ->.
        unfold searly, set_es, searly0, evs; simpl. unfold upd at 1. rewrite Nat.eqb_refl. cbn.
        split; [exact Ih|]. intros k' t' O. cbn in O |- *. unfold upd in O |- *.
        destruct (Nat.eqb k' k); [reflexivity|exact (Io k' t' O)].
      * unfold searly, set_es, searly0, evs; simpl. rewrite upd_neq by auto. split; auto.
    + destruct (Nat.eq_dec c 0) as [->|Nc].
      * exfalso. unfold smatch in Pt; simpl in Pt. unfold upd in Pt. simpl in Pt. lia.
      * unfold smatch; simpl. rewrite upd_neq by auto. split; auto.
    + destruct X as (H1 & H2 & H2h & Hso & Ok & H5 & _ & ->).
      destruct (Nat.eq_dec c 0) as [->|Nc].
      * exfalso. rewrite Ps in Ok. apply (read_q _ _ _ _ _ _ (conj Ih Io) Ok).
      * unfold sread; simpl. rewrite upd_neq by auto. split; auto.
    + destruct (Nat.eq_dec c 0) as [->|Nc].
      * exfalso. unfold sskip in Pt; simpl in Pt. unfold upd in Pt. simpl in Pt. lia.
      * unfold sskip; simpl. rewrite upd_neq by auto. split; auto.
    + split; [intros k; rewrite oh_cx, oh_flp; apply Ih|intros k t0 O; rewrite oc_cx, oc_flp in O; rewrite ai_cx, ai_flp; apply (Io k t0 O)].
Qed.

Lemma early_placeQ : forall s c k tj tk, run CASHoistX s -> 0 < k ->
  oc (cs s c) 0 = Some tj -> oc (cs s c) k = Some tk -> tk < tj ->
  (forall i ti, i <> k -> oc (cs s c) i = Some ti -> tj <= ti) ->
  (forall i th, oh (cs s c) i = Some th -> tk <= th) ->
  exists B N F, forall g, exists j',
    eof (ins CASHoistX c j' (creg CASHoistX c (cfr F) 0 N B g)) (creg CASHoistX c (cfr F) 0 N B g) =
    eof (ai (cs s c) k) (rg (cs s c)).
Proof.
  intros s c k tj tk R Ljk Oj Ok Lt After AfterH.
  destruct (early_of CASHoistX s c 0 k tj tk R Ljk Oj Ok Lt)
    as (cc0 & pc0 & N0 & B0 & d & e & Es & A & B & C & X).
  destruct X as (Ok' & D & Lp & Nj & E & F & G & Pn & Ph).
  assert (Hn : forall i, oc cc0 i = None).
  { intros i. destruct (oc cc0 i) as [t0|] eqn:O; auto. exfalso. destruct (E i t0 O) as (O' & _ & L).
    destruct (Nat.eq_dec i k) as [->|Ni]; [rewrite Ok in O'; injection O' as <-; lia|].
    pose proof (After i t0 Ni O'). lia. }
  assert (Hh : forall i, oh cc0 i = None).
  { intros i. destruct (oh cc0 i) as [t0|] eqn:O; auto. exfalso. destruct (Ph i t0 O) as (O' & L).
    pose proof (AfterH i t0 O'). lia. }
  assert (P0 : pc0 = 0) by lia. subst pc0.
  exists (bor (bd cc0) B0), N0, (fx cc0). intros g.
  assert (Ej : exists j', eof (ins CASHoistX c j' (creg CASHoistX c cc0 0 N0 (bor (bd cc0) B0) g))
                              (creg CASHoistX c cc0 0 N0 (bor (bd cc0) B0) g) = Some d).
  { destruct Ok' as [Ok'|(T1 & mh & xsh & Ok')].
    - destruct (Ok' g) as (j' & _ & Fj & _). cbv zeta in Fj. exists j'. apply (first_at_eof _ _ _ _ _ _ _ _ Fj).
    - destruct (Ok' g) as (j' & _ & _ & Dj & _). cbv zeta in Dj. exists j'. exact Dj. }
  destruct Ej as (j' & Ej).
  exists j'. rewrite D. rewrite <- Ej.
  apply (eof_agree CASHoistX W_X c j'). intros i _. symmetry.
  apply (creg_fresh CASHoistX c g cc0 N0 N0 _ _ i Hn Hh). auto.
Qed.

Lemma oh_casQ : forall s c i th, run CASHoistX s -> done CASHoistX s -> oh (cs s c) i = Some th -> c = 0.
Proof.
  intros s c i th R CP Oh. pose proof (Inv1_run _ s R) as I.
  assert (L : i < pcs s c) by (apply (passed_h CASHoistX s R CP W_X c i); congruence).
  assert (Cx : is_cas (ai (cs s c) i) = true).
  { destruct (oc (cs s c) i) as [t2|] eqn:O; [exact (proj2 (i_hoc _ s I c i th t2 Oh O))|].
    destruct (i_halfp _ s I c i th O Oh L) as (F & _). apply (cfail_cas _ _ _ F). }
  destruct (cm_set _ s c i I L) as (tau0 & T0). rewrite (proj2 (i_set _ s I c i tau0 T0)), insX in Cx.
  destruct c as [|[|[|c]]]; auto; destruct i as [|[|i]]; simpl in Cx; try discriminate;
    try (destruct i; simpl in Cx; discriminate); destruct c; simpl in Cx; discriminate.
Qed.

Theorem CASHoistX_forbidden_Q : forall s, run CASHoistX s -> done CASHoistX s ->
  ~ (rg (cs s 0) 0 = 5 /\ vv (rg (cs s 0) 1) = 5).
Proof.
  intros s R CP (A0 & A1). pose proof W_X as W.
  get_ent CASHoistX s R CP W 0 0 E00. get_ent CASHoistX s R CP W 1 0 E10.
  (* the slots that execute whatever was read happened (the CASes at 1 and 2
     execute one of them) *)
  assert (O : forall c k, (c = 0 /\ (k = 0 \/ k = 3)) \/ (c = 1 /\ k < 2) -> oc (cs s c) k = Some (bt s c k)).
  { intros c k Hc. unfold bt, tmo. destruct (oc (cs s c) k) eqn:Oc; auto. exfalso.
    destruct Hc as [(-> & [-> | ->])|(-> & L)];
      [apply (happened CASHoistX s R CP W 0 3 ltac:(vm_compute; discriminate) 0 ltac:(lia)); [vm_compute; reflexivity|vm_compute; reflexivity|exact Oc]
      |apply (happened CASHoistX s R CP W 0 3 ltac:(vm_compute; discriminate) 3 ltac:(lia)); [vm_compute; reflexivity|vm_compute; reflexivity|exact Oc]
      |destruct k as [|[|k]];
       [apply (happened CASHoistX s R CP W 1 1 ltac:(vm_compute; discriminate) 0 ltac:(lia)); [vm_compute; reflexivity|vm_compute; reflexivity|exact Oc]
       |apply (happened CASHoistX s R CP W 1 1 ltac:(vm_compute; discriminate) 1 ltac:(lia)); [vm_compute; reflexivity|vm_compute; reflexivity|exact Oc]
       |lia]]. }
  (* r0 = y took y = r of context 1, so r = 5 *)
  destruct (readv CASHoistX s R CP W 0 0 _ 1 E00 5 eq_refl eq_refl eq_refl ltac:(eassumption) ltac:(eassumption) A0 ltac:(lia))
    as (y & _ & Vy & Iy & Ly).
  pose proof (n_wr_of CASHoistX s R CP W 1 y Iy) as WO.
  assert (L1 : bt s 1 1 < bt s 0 0 /\ rg (cs s 1) 0 = 5).
  { which_writer WO; subst y. split; [lia|]. simpl in V. unfold RG in V. rewrite Vy in V. symmetry. exact V. }
  destruct L1 as (L1 & B0).
  (* r = z took z = r1 + r2 *)
  destruct (readv CASHoistX s R CP W 1 0 _ 2 E10 5 eq_refl eq_refl eq_refl ltac:(eassumption) ltac:(eassumption) B0 ltac:(lia))
    as (y' & _ & Vy' & Iy' & Ly').
  assert (L3 : bt s 0 3 < bt s 1 0).
  { pose proof (n_wr_of CASHoistX s R CP W 2 y' Iy') as WO'. which_writer WO'; subst y'; lia. }
  (* y = r happened after its read of z *)
  assert (L2 : bt s 1 0 < bt s 1 1).
  { destruct (Nat.lt_trichotomy (bt s 1 0) (bt s 1 1)) as [L|[L|L]]; auto; exfalso.
    - apply (neq_bt CASHoistX s R CP W 1 0 1 1 _ _ eq_refl ltac:(nn) eq_refl eq_refl ltac:(nn) eq_refl); [congruence|exact L].
    - destruct (early_placeQ s 1 1 _ _ R ltac:(lia) (O 1 0 ltac:(lia)) (O 1 1 ltac:(lia)) L) as (B & N & Fx & HP).
      { intros i ti Ni Oi. destruct i as [|[|i]]; [rewrite (O 1 0 ltac:(lia)) in Oi; injection Oi as <-; lia|congruence|].
        apply (inop_after CASHoistX s 1 (S (S i)) ti 0 _ R CP W Oi); [rewrite insX; simpl; destruct i; reflexivity|lia|vm_compute; reflexivity|apply O; lia]. }
      { intros i th Oh. pose proof (oh_casQ s 1 i th R CP Oh). discriminate. }
      destruct (HP f0) as (j' & Hj). rewrite (ai_passed CASHoistX s 1 1 R CP W ltac:(rewrite (O 1 1 ltac:(lia)); discriminate)) in Hj.
      remember (creg CASHoistX 1 (cfr Fx) 0 N B f0) as r eqn:Er. assert (R0 : r 0 = 0) by (subst r; apply val_r0X).
      rewrite !insX in Hj. cbn -[creg CASHoistX] in Hj. unfold RG in Hj. rewrite B0 in Hj.
      destruct j' as [|[|[|j']]]; cbn -[creg CASHoistX] in Hj; try discriminate; unfold RG in Hj; rewrite R0 in Hj; discriminate. }
  (* z = r1 + r2 happened after r0 = y *)
  assert (L4 : bt s 0 0 < bt s 0 3).
  { destruct (Nat.lt_trichotomy (bt s 0 0) (bt s 0 3)) as [L|[L|L]]; auto; exfalso.
    - apply (neq_bt CASHoistX s R CP W 0 0 0 3 _ _ eq_refl ltac:(nn) eq_refl eq_refl ltac:(nn) eq_refl); [congruence|exact L].
    - destruct (run_traceQ CASHoistX s R) as (f & n & T & Fn). subst s.
      assert (Lp : 0 < pcs (f n) 0) by (apply (passed CASHoistX (f n) R CP W 0 0); rewrite (O 0 0 ltac:(lia)); discriminate).
      destruct (pass_birth CASHoistX f n T n 0 0 (le_n n) Lp) as (ih & Lih & Pih & _ & Cs).
      assert (Tj : bt (f n) 0 0 <= tm (f ih)).
      { destruct Cs as [(i0 & m' & a & K & u & w & _ & Ho & _ & _ & _ & _ & _ & _ & E)|[(d & Ho & _ & _ & _ & _ & _ & E)|(Kx & _)]];
          [| |exfalso; cbv zeta in Kx; rewrite exec_xex_ncas in Kx; [discriminate Kx|vm_compute; reflexivity|vm_compute; reflexivity]].
        - assert (O1 : oc (cs (f (S ih)) 0) 0 = Some (tm (f ih))).
          { rewrite E. unfold sord, evs, upd. cbn. rewrite Pih. cbn. reflexivity. }
          pose proof (x_oc _ _ (tr_ext CASHoistX f n T (S ih) n ltac:(lia) (le_n n)) 0 0 _ O1) as O2.
          unfold bt, tmo. rewrite O2. lia.
        - cbv zeta in Ho. destruct (oc (cs (f ih) 0) 0) as [t0|] eqn:O0; [|congruence].
          pose proof (oc_lt_tm CASHoistX (f ih) 0 0 t0 (Inv1_run _ _ (tr_run CASHoistX f n T ih ltac:(lia))) O0) as Lt0.
          pose proof (x_oc _ _ (tr_ext CASHoistX f n T ih n ltac:(lia) (le_n n)) 0 0 t0 O0) as O2.
          unfold bt, tmo. rewrite O2. lia. }
      assert (O3 : oc (cs (f ih) 0) 3 = Some (bt (f n) 0 3)).
      { apply (x_ocb _ _ (tr_ext CASHoistX f n T ih n ltac:(lia) (le_n n))); [apply O; lia|lia]. }
      destruct (inv_qQ (f ih) (tr_run CASHoistX f n T ih ltac:(lia)) Pih) as (_ & Io).
      pose proof (Io 3 _ O3) as A3.
      destruct (pend_fate CASHoistX f n T ih n 0 3 (DSt Plain [2] 0) ltac:(lia) (le_n n) W ltac:(congruence) ltac:(lia) A3)
        as [(Pn & _)|(_ & Dn)].
      + assert (3 < pcs (f n) 0) by (apply (passed CASHoistX (f n) R CP W 0 3); rewrite (O 0 3 ltac:(lia)); discriminate). lia.
      + rewrite insX in Dn. simpl in Dn. injection Dn as Dn. rewrite A1 in Dn. lia. }
  lia.
Qed.

Print Assumptions CASHoistX_forbidden_Q.
