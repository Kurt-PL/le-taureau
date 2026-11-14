(* Model2, a CAS in two parts: the CASHoist variant whose branches CAS different
   cells stays excluded.
     r0 = y; if r0 == 5 { r1 = CAS(x, 0, 5) } else { r2 = CAS(w, 0, 7) }; z = r1 + r2
       || r = z; y = r || x = 5
   with r0 = 5 and r1 = 5. A CAS's read may happen alone only where every way
   the context may go on has a CAS of its mode and cells there; before r0 is
   read, one way has the CAS of x and the other the CAS of w, so no read
   happens alone, and z = r1 + r2 can only take the value 0. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2Comp M2Lit M2Neg M2Oota M2Snap M2Ev M2Cont M2LitNeg M2CasFwd M2Trace.

Definition CODEX : list (list instr) :=
  [ [ld 1; ICas Plain [0] (EQ 0 5) (K 0) (K 5); ICas Plain [3] (NE 0 5) (K 0) (K 7);
     ISt Plain [2] T (fun r => vv (r 1) + vv (r 2))];
    [ld 2; ISt Plain [1] T (RG 0)];
    [st 0 5] ].
Definition CASHoistX : prog := stat CODEX.

Lemma insX : forall c k r, ins CASHoistX c k r = nth k (nth c CODEX []) INop.
Proof. intros. apply ins_stat. Qed.

Lemma W_X : wf CASHoistX.
Proof. wf_tac. Qed.

(* ---------- context 0 before its first read: only z = 0 can happen early ---------- *)
Definition Q (cc : cst) : Prop :=
  (forall k, oh cc k = None) /\ (forall k t, oc cc k = Some t -> ai cc k = inst_of (DSt Plain [2] 0)).

Lemma fab_eof : forall p c cc pc N r n T d j, fab p c cc pc N r n T (TF d) j = true -> eof (ins p c j r) r = Some d.
Proof.
  intros p c cc pc N r n T d j H. destruct n as [|n]; [discriminate|]. cbn [fab] in H.
  repeat (apply andb_true_iff in H as [H ?]).
  match goal with X : tatb _ _ _ = true |- _ => revert X end. unfold tatb.
  destruct (eof (ins p c j r) r) as [d'|]; simpl; [|discriminate]. intros X. f_equal. apply desc_eqb_eq. exact X.
Qed.

Lemma pa_none : forall cc N r j, Q cc -> j < 3 -> pend_at CASHoistX 0 cc 0 N r j = None.
Proof.
  intros cc N r j [Hh Ho] L. unfold pend_at. destruct (find _ _) as [k|] eqn:F; [|reflexivity]. exfalso.
  apply find_some in F as (_ & F). destruct (oc cc k) as [t|] eqn:O; [|discriminate].
  rewrite (Ho k t O), eof_inst in F by discriminate. unfold first_atb in F. apply fab_eof in F.
  rewrite insX in F. destruct j as [|[|[|j]]]; [discriminate| | |lia]; simpl in F;
    unfold EQ, NE in F; destruct (Nat.eqb (r 0) 5); discriminate.
Qed.

Lemma ha_none : forall cc N r j, Q cc -> hpend_at CASHoistX 0 cc 0 N r j = None.
Proof.
  intros cc N r j [Hh _]. unfold hpend_at. induction (seq 0 (N - 0)) as [|a l IH]; simpl; [reflexivity|].
  rewrite Hh. destruct (oc cc a); exact IH.
Qed.

Section Gen.
Variables (f : nat -> cell -> val).

Lemma cellv_q : forall g cc N N' B B' r n j x, Q cc -> j < 3 -> (forall i, i <= j -> B i = B' i) ->
  cellv CASHoistX 0 cc 0 N B f r n j x = cellv CASHoistX 0 (cfr g) 0 N' B' f r n j x.
Proof.
  intros g cc N N' B B' r n. induction n as [|n IH]; intros j x Hq Lj E; cbn [cellv];
    (destruct (Nat.ltb_spec j 0) as [L|_]; [lia|]);
    rewrite (pa_none cc N r j Hq Lj), (pend_none CASHoistX 0 (cfr g) N' r j (fun _ => eq_refl));
    rewrite (ha_none cc N r j Hq), (hpend_none CASHoistX 0 (cfr g) N' r j (fun _ => eq_refl)); auto.
  all: destruct (_ && _); auto. rewrite (E j (le_n _)). destruct (B' j); auto.
  destruct (fbinder CASHoistX 0 r j x) as [b|] eqn:Fb; auto. pose proof (fbinder_lt _ _ _ _ _ _ Fb).
  f_equal. apply IH; auto; [lia|]. intros i L. apply E. lia.
Qed.

Lemma bl_q : forall cc N N' B B' n, Q cc -> n <= 3 -> (forall i, i < n -> B i = B' i) ->
  bl CASHoistX 0 cc 0 N B f n = bl CASHoistX 0 (cfr (fx cc)) 0 N' B' f n.
Proof.
  intros cc N N' B B' n Hq Ln E. induction n as [|n IH]; [reflexivity|]. cbn [bl].
  rewrite IH by (try lia; intros i L; apply E; lia). f_equal. f_equal.
  unfold slotv. destruct (Nat.ltb_spec n 0) as [L|_]; [lia|]. destruct (_ && _); [|reflexivity].
  rewrite (pa_none cc N _ n Hq ltac:(lia)), (pend_none CASHoistX 0 (cfr (fx cc)) N' _ n (fun _ => eq_refl)).
  rewrite (ha_none cc N _ n Hq), (hpend_none CASHoistX 0 (cfr (fx cc)) N' _ n (fun _ => eq_refl)).
  change (cfx (cfr (fx cc))) with (cfx cc). f_equal.
  cbv zeta.
  rewrite (map_ext (cellv CASHoistX 0 cc 0 N B f (lreg (bl CASHoistX 0 (cfr (fx cc)) 0 N' B' f n)) n n)
                   (cellv CASHoistX 0 (cfr (fx cc)) 0 N' B' f (lreg (bl CASHoistX 0 (cfr (fx cc)) 0 N' B' f n)) n n)); [reflexivity|].
  intros x. apply cellv_q; [exact Hq|lia|intros i L; apply E; lia].
Qed.

Lemma creg_q : forall cc N N' B B' j, Q cc -> j < 3 -> (forall i, i <= j -> B i = B' i) ->
  creg CASHoistX 0 cc 0 N B f j = creg CASHoistX 0 (cfr (fx cc)) 0 N' B' f j.
Proof. intros cc N N' B B' j Hq L E. unfold creg. rewrite (bl_q cc N N' B B' (S j) Hq ltac:(lia)); auto. intros i L'. apply E. lia. Qed.

End Gen.

Definition B3 (B : nat -> bool) : nat -> bool := fun i => match i with 0 => B 0 | 1 => B 1 | 2 => B 2 | _ => false end.

Lemma agree_q : forall cc N B f, Q cc ->
  agree (creg CASHoistX 0 cc 0 N B f) (creg CASHoistX 0 (cfr (fx cc)) 0 0 (B3 B) f) 3.
Proof.
  intros cc N B f Hq j L. apply (creg_q f cc N 0 B (B3 B) j Hq L).
  intros i Li. destruct i as [|[|[|i]]]; try reflexivity; lia.
Qed.

Definition fv (v : val) : nat -> cell -> val := fun _ _ => v.

(* the effect at slot j <= 3, as R1 sees it before anything of context 0 *)
Lemma eof_q : forall cc N B v j, Q cc -> j <= 3 ->
  eof (ins CASHoistX 0 j (creg CASHoistX 0 cc 0 N B (fv v))) (creg CASHoistX 0 cc 0 N B (fv v)) =
  eof (ins CASHoistX 0 j (creg CASHoistX 0 (cfr (fx cc)) 0 0 (B3 B) (fv v))) (creg CASHoistX 0 (cfr (fx cc)) 0 0 (B3 B) (fv v)).
Proof.
  intros cc N B v j Hq L. apply (eof_agree CASHoistX W_X 0 j). intros i Li. apply (agree_q cc N B (fv v) Hq). lia.
Qed.

Lemma eofR_q : forall cc N B v j, Q cc -> j <= 3 ->
  eofR (ins CASHoistX 0 j (creg CASHoistX 0 cc 0 N B (fv v))) (creg CASHoistX 0 cc 0 N B (fv v)) =
  eofR (ins CASHoistX 0 j (creg CASHoistX 0 (cfr (fx cc)) 0 0 (B3 B) (fv v))) (creg CASHoistX 0 (cfr (fx cc)) 0 0 (B3 B) (fv v)).
Proof.
  intros cc N B v j Hq L. apply (eofR_agree CASHoistX W_X 0 j). intros i Li. apply (agree_q cc N B (fv v) Hq). lia.
Qed.

Lemma eof_big : forall r j, 4 <= j -> eof (ins CASHoistX 0 j r) r = None /\ eofR (ins CASHoistX 0 j r) r = None.
Proof. intros r j L. rewrite insX. do 4 (destruct j as [|j]; [lia|]). destruct j; split; reflexivity. Qed.

(* an early access of context 0 before its first read is z = 0 *)
Lemma early_q : forall cc N T d u B, Q cc -> early_ok CASHoistX 0 cc 0 N T d u B -> d = DSt Plain [2] 0.
Proof.
  intros cc N T d u B Hq Ok.
  destruct (Ok (fv 0)) as (j0 & L0 & F0 & _). destruct (Ok (fv 5)) as (j5 & L5 & F5 & _). cbv zeta in F0, F5.
  apply first_at_eof in F0. apply first_at_eof in F5.
  destruct (Nat.le_gt_cases j0 3) as [J0|J0]; [|rewrite (proj1 (eof_big _ j0 ltac:(lia))) in F0; discriminate].
  destruct (Nat.le_gt_cases j5 3) as [J5|J5]; [|rewrite (proj1 (eof_big _ j5 ltac:(lia))) in F5; discriminate].
  rewrite eof_q in F0, F5 by auto. unfold B3 in F0, F5. remember (fx cc) as g eqn:Eg. clear Eg.
  destruct (bor (bd cc) B 0), (bor (bd cc) B 1), (bor (bd cc) B 2);
    (destruct j0 as [|[|[|[|j0]]]]; [lia| | | |lia]); (destruct j5 as [|[|[|[|j5]]]]; [lia| | | |lia]);
    vm_compute in F0, F5; revert F0 F5; destruct (g 1) as [[]|], (g 2) as [[]|]; intros F0 F5;
    vm_compute in F0, F5; try discriminate F0; try discriminate F5;
    injection F0 as <-; try injection F5 as F5; try discriminate F5; reflexivity.
Qed.

(* no CAS's read of context 0 happens alone before its first read *)
Lemma read_q : forall cc N T xs u B, Q cc -> early_okR CASHoistX 0 cc 0 N T Plain xs u B -> False.
Proof.
  intros cc N T xs u B Hq Ok.
  destruct (Ok (fv 0)) as (j0 & F0 & _). destruct (Ok (fv 5)) as (j5 & F5 & _). cbv zeta in F0, F5.
  apply first_atR_eofR in F0. apply first_atR_eofR in F5.
  destruct (Nat.le_gt_cases j0 3) as [J0|J0]; [|rewrite (proj2 (eof_big _ j0 ltac:(lia))) in F0; discriminate].
  destruct (Nat.le_gt_cases j5 3) as [J5|J5]; [|rewrite (proj2 (eof_big _ j5 ltac:(lia))) in F5; discriminate].
  rewrite eofR_q in F0, F5 by auto. unfold B3 in F0, F5. remember (fx cc) as g eqn:Eg. clear Eg.
  destruct (bor (bd cc) B 0), (bor (bd cc) B 1), (bor (bd cc) B 2);
    (destruct j0 as [|[|[|[|j0]]]]; [| | | |lia]); (destruct j5 as [|[|[|[|j5]]]]; [| | | |lia]);
    vm_compute in F0, F5; revert F0 F5; destruct (g 1) as [[]|], (g 2) as [[]|]; intros F0 F5;
    vm_compute in F0, F5; try discriminate F0; try discriminate F5;
    rewrite <- F0 in F5; discriminate F5.
Qed.

Lemma inv_q : forall s, run CASHoistX s -> pcs s 0 = 0 -> Q (cs s 0).
Proof.
  intros s R. induction R as [|s t R IH H].
  - intros _. split; [intros k; reflexivity|intros k t O; discriminate O].
  - intros Pt. assert (Ps : pcs s 0 = 0) by (pose proof (x_pcs _ _ (Ext_step CASHoistX s t R H) 0); lia).
    specialize (IH Ps). destruct IH as [Ih Io].
    destruct (step_cases _ _ _ H) as [(c & i & m' & a & K & u & w & H1 & H2 & H3 & H4 & H4h & Hh & _ & _ & H5 & _ & ->)|[(c & k & d & B & m' & a & K & u & w & H1 & H2 & Hso & Hh & _ & _ & H5 & _ & ->)|[(c & d & H1 & H2 & H3 & H4 & H4m & Hfh & ->)|[(c & k & xs & B & m' & a & K & u & w & bv & H1 & H2 & H2h & Hso & Ok & H5 & _ & ->)|[(c & S1 & S2 & S3 & _ & S5 & S4 & _ & ->)|(cX & jX & bX & BX & oX & HjX & HfX & HcX & ->)]]]]].
    + destruct (Nat.eq_dec c 0) as [->|Nc].
      * exfalso. unfold sord, evs in Pt; simpl in Pt. unfold upd in Pt. simpl in Pt. lia.
      * unfold sord, evs; simpl. rewrite upd_neq by auto. split; auto.
    + destruct (Nat.eq_dec c 0) as [->|Nc].
      * destruct Hh as [(Oh & Ok)|(t1 & xs & ev & nv & Oh & _)]; [|rewrite Ih in Oh; discriminate].
        rewrite Ps in Ok. pose proof (early_q _ _ _ _ _ _ (conj Ih Io) Ok) as ->.
        unfold searly, set_es, searly0, evs; simpl. unfold upd at 1. rewrite Nat.eqb_refl. cbn.
        split; [exact Ih|]. intros k' t' O. cbn in O |- *. unfold upd in O |- *.
        destruct (Nat.eqb k' k); [reflexivity|exact (Io k' t' O)].
      * unfold searly, set_es, searly0, evs; simpl. rewrite upd_neq by auto. split; auto.
    + destruct (Nat.eq_dec c 0) as [->|Nc].
      * exfalso. unfold smatch in Pt; simpl in Pt. unfold upd in Pt. simpl in Pt. lia.
      * unfold smatch; simpl. rewrite upd_neq by auto. split; auto.
    + destruct (Nat.eq_dec c 0) as [->|Nc].
      * exfalso. rewrite Ps in Ok. apply (read_q _ _ _ _ _ _ (conj Ih Io) Ok).
      * unfold sread; simpl. rewrite upd_neq by auto. split; auto.
    + destruct (Nat.eq_dec c 0) as [->|Nc].
      * exfalso. unfold sskip in Pt; simpl in Pt. unfold upd in Pt. simpl in Pt. lia.
      * unfold sskip; simpl. rewrite upd_neq by auto. split; auto.
    + split; [intros k; rewrite oh_cx, oh_flp; apply Ih|intros k t0 O; rewrite oc_cx, oc_flp in O; rewrite ai_cx, ai_flp; apply (Io k t0 O)].
Qed.

(* ---------- context 1: y = r after its read of z ---------- *)
Lemma early_placeX : forall s c k tj tk, run CASHoistX s -> 0 < k ->
  oc (cs s c) 0 = Some tj -> oc (cs s c) k = Some tk -> tk < tj ->
  (forall i ti, i <> k -> oc (cs s c) i = Some ti -> tj <= ti) ->
  (forall i th, oh (cs s c) i = Some th -> tk <= th) ->
  exists B N F, forall g, exists j',
    eof (ins CASHoistX c j' (creg CASHoistX c (cfr F) 0 N B g)) (creg CASHoistX c (cfr F) 0 N B g) =
    eof (ai (cs s c) k) (rg (cs s c)).
Proof.
  intros s c k tj tk R Ljk Oj Ok Lt After AfterH.
  destruct (early_of CASHoistX s c 0 k tj tk R Ljk Oj Ok Lt)
    as (cc0 & pc0 & N0 & B0 & d & e & Es & A & B & C & Ok' & D & Lp & Nj & E & F & G & Pn & Ph).
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

Lemma oh_casX : forall s c i th, run CASHoistX s -> done CASHoistX s -> oh (cs s c) i = Some th -> c = 0.
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

Lemma val_r0X : forall N B F, creg CASHoistX 1 (cfr F) 0 N B f0 0 = 0.
Proof.
  intros N B F. rewrite (creg_fresh CASHoistX 1 f0 (cfr F) N 0 B (fun i => match i with 0 => B 0 | _ => false end) 0)
    ; [|intros k; reflexivity|intros k; reflexivity|intros i L; destruct i as [|i]; [reflexivity|lia]].
  destruct (B 0); vm_compute; fx3 F; reflexivity.
Qed.

Theorem CASHoistX_forbidden : forall s, run CASHoistX s -> done CASHoistX s ->
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
    - destruct (early_placeX s 1 1 _ _ R ltac:(lia) (O 1 0 ltac:(lia)) (O 1 1 ltac:(lia)) L) as (B & N & Fx & HP).
      { intros i ti Ni Oi. destruct i as [|[|i]]; [rewrite (O 1 0 ltac:(lia)) in Oi; injection Oi as <-; lia|congruence|].
        apply (inop_after CASHoistX s 1 (S (S i)) ti 0 _ R CP W Oi); [rewrite insX; simpl; destruct i; reflexivity|lia|vm_compute; reflexivity|apply O; lia]. }
      { intros i th Oh. pose proof (oh_casX s 1 i th R CP Oh). discriminate. }
      destruct (HP f0) as (j' & Hj). rewrite (ai_passed CASHoistX s 1 1 R CP W ltac:(rewrite (O 1 1 ltac:(lia)); discriminate)) in Hj.
      remember (creg CASHoistX 1 (cfr Fx) 0 N B f0) as r eqn:Er. assert (R0 : r 0 = 0) by (subst r; apply val_r0X).
      rewrite !insX in Hj. cbn -[creg CASHoistX] in Hj. unfold RG in Hj. rewrite B0 in Hj.
      destruct j' as [|[|[|j']]]; cbn -[creg CASHoistX] in Hj; try discriminate; unfold RG in Hj; rewrite R0 in Hj; discriminate. }
  (* z = r1 + r2 happened after r0 = y *)
  assert (L4 : bt s 0 0 < bt s 0 3).
  { destruct (Nat.lt_trichotomy (bt s 0 0) (bt s 0 3)) as [L|[L|L]]; auto; exfalso.
    - apply (neq_bt CASHoistX s R CP W 0 0 0 3 _ _ eq_refl ltac:(nn) eq_refl eq_refl ltac:(nn) eq_refl); [congruence|exact L].
    - destruct (run_trace CASHoistX s R) as (f & n & T & Fn). subst s.
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
      destruct (inv_q (f ih) (tr_run CASHoistX f n T ih ltac:(lia)) Pih) as (_ & Io).
      pose proof (Io 3 _ O3) as A3.
      destruct (pend_fate CASHoistX f n T ih n 0 3 (DSt Plain [2] 0) ltac:(lia) (le_n n) W ltac:(congruence) ltac:(lia) A3)
        as [(Pn & _)|(_ & Dn)].
      + assert (3 < pcs (f n) 0) by (apply (passed CASHoistX (f n) R CP W 0 3); rewrite (O 0 3 ltac:(lia)); discriminate). lia.
      + rewrite insX in Dn. simpl in Dn. injection Dn as Dn. rewrite A1 in Dn. lia. }
  lia.
Qed.
