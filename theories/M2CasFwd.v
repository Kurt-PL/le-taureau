(* Model2: CASFWD stays excluded.
     r0 = x; c = CAS(x, 2, 3); r2 = x; y = r2  ||  r1 = y; x = r1 - 1
   with r0 = 2, the CAS reading 2, r2 = 3, r1 = 3. The value of y = r2 depends
   on what the first read of x takes (through the CAS's success), so y = r2
   cannot happen before it; x = r1 - 1 cannot happen before its read of y;
   and the four accesses would form a cycle in time. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2Comp M2Lit M2Neg M2Oota M2Snap M2Ev M2Cont M2LitNeg.

(* ---------- registers R1 considers when nothing of the context has happened ---------- *)
(* the initial context state with the results fixed g (S3c) *)
Definition cfr (g : nat -> option bool) : cst :=
  mkC (oc cinit) (rg cinit) (ai cinit) (rw cinit) (rv cinit) (bd cinit) (vP cinit) (vA cinit) (vR cinit)
      (vO cinit) (vOg cinit) (oh cinit) g.

Section Fresh.
Variables (p : prog) (c : nat) (f : nat -> cell -> val).

Lemma pend_none : forall cc N r j, (forall k, oc cc k = None) -> pend_at p c cc 0 N r j = None.
Proof.
  intros cc N r j Hn. unfold pend_at. induction (seq 0 (N - 0)) as [|a l IH]; simpl; [reflexivity|].
  rewrite Hn. exact IH.
Qed.

Lemma hpend_none : forall cc N r j, (forall k, oh cc k = None) -> hpend_at p c cc 0 N r j = None.
Proof.
  intros cc N r j Hn. unfold hpend_at. induction (seq 0 (N - 0)) as [|a l IH]; simpl; [reflexivity|].
  rewrite Hn. destruct (oc cc a); exact IH.
Qed.

Lemma cellv_fresh : forall g cc N N' B B' r n j x, (forall k, oc cc k = None) -> (forall k, oh cc k = None) ->
  (forall i, i <= j -> B i = B' i) ->
  cellv p c cc 0 N B f r n j x = cellv p c (cfr g) 0 N' B' f r n j x.
Proof.
  intros g cc N N' B B' r n. induction n as [|n IH]; intros j x Hn Hh E; cbn [cellv];
    (destruct (Nat.ltb_spec j 0) as [L|_]; [lia|]);
    rewrite (pend_none cc N r j Hn), (pend_none (cfr g) N' r j (fun _ => eq_refl));
    rewrite (hpend_none cc N r j Hh), (hpend_none (cfr g) N' r j (fun _ => eq_refl)); auto.
  all: destruct (_ && _); auto. rewrite (E j (le_n _)). destruct (B' j); auto.
  destruct (fbinder p c r j x) as [b|] eqn:Fb; auto. pose proof (fbinder_lt _ _ _ _ _ _ Fb).
  f_equal. apply IH; auto. intros i L. apply E. lia.
Qed.

Lemma bl_fresh : forall cc N N' B B' n, (forall k, oc cc k = None) -> (forall k, oh cc k = None) ->
  (forall i, i < n -> B i = B' i) ->
  bl p c cc 0 N B f n = bl p c (cfr (fx cc)) 0 N' B' f n.
Proof.
  intros cc N N' B B' n Hn Hh E. induction n as [|n IH]; [reflexivity|]. cbn [bl].
  rewrite IH by (intros i L; apply E; lia). f_equal. f_equal.
  unfold slotv. destruct (Nat.ltb_spec n 0) as [L|_]; [lia|]. destruct (_ && _); [|reflexivity].
  rewrite (pend_none cc N _ n Hn), (pend_none (cfr (fx cc)) N' _ n (fun _ => eq_refl)).
  rewrite (hpend_none cc N _ n Hh), (hpend_none (cfr (fx cc)) N' _ n (fun _ => eq_refl)).
  change (cfx (cfr (fx cc))) with (cfx cc). f_equal.
  cbv zeta.
  rewrite (map_ext (cellv p c cc 0 N B f (lreg (bl p c (cfr (fx cc)) 0 N' B' f n)) n n) (cellv p c (cfr (fx cc)) 0 N' B' f (lreg (bl p c (cfr (fx cc)) 0 N' B' f n)) n n));
    [reflexivity|].
  intros x. apply cellv_fresh; auto. intros i L. apply E. lia.
Qed.

Lemma creg_fresh : forall cc N N' B B' j, (forall k, oc cc k = None) -> (forall k, oh cc k = None) ->
  (forall i, i <= j -> B i = B' i) ->
  creg p c cc 0 N B f j = creg p c (cfr (fx cc)) 0 N' B' f j.
Proof. intros cc N N' B B' j Hn Hh E. unfold creg. rewrite (bl_fresh cc N N' B B' (S j) Hn Hh); auto. intros i L. apply E. lia. Qed.

End Fresh.

Definition CODE : list (list instr) :=
  [ [ld 0; ICas Plain [0] T (K 2) (K 3); ld 0; ISt Plain [1] T (RG 2)];
    [ld 1; ISt Plain [0] T (fun r => r 0 - 1)] ].
Definition CASFWD : prog := stat CODE.

Lemma insC : forall c k r, ins CASFWD c k r = nth k (nth c CODE []) INop.
Proof. intros. apply ins_stat. Qed.

Lemma W_CASFWD : wf CASFWD.
Proof. wf_tac. Qed.

(* an early store: its place under any free values, with nothing of the
   context happened before it *)
Lemma early_place : forall s c k tj tk, run CASFWD s -> 0 < k ->
  oc (cs s c) 0 = Some tj -> oc (cs s c) k = Some tk -> tk < tj ->
  (forall i ti, i <> k -> oc (cs s c) i = Some ti -> tj <= ti) ->
  (forall i th, oh (cs s c) i = Some th -> tk <= th) ->
  exists B N F, forall g, exists j',
    eof (ins CASFWD c j' (creg CASFWD c (cfr F) 0 N B g)) (creg CASFWD c (cfr F) 0 N B g) =
    eof (ai (cs s c) k) (rg (cs s c)).
Proof.
  intros s c k tj tk R Ljk Oj Ok Lt After AfterH.
  destruct (early_of CASFWD s c 0 k tj tk R Ljk Oj Ok Lt)
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
  assert (Ej : exists j', eof (ins CASFWD c j' (creg CASFWD c cc0 0 N0 (bor (bd cc0) B0) g))
                              (creg CASFWD c cc0 0 N0 (bor (bd cc0) B0) g) = Some d).
  { destruct Ok' as [Ok'|(T1 & mh & xsh & Ok')].
    - destruct (Ok' g) as (j' & _ & Fj & _). cbv zeta in Fj. exists j'. apply (first_at_eof _ _ _ _ _ _ _ _ Fj).
    - destruct (Ok' g) as (j' & _ & _ & Dj & _). cbv zeta in Dj. exists j'. exact Dj. }
  destruct Ej as (j' & Ej).
  exists j'. rewrite D. rewrite <- Ej.
  apply (eof_agree CASFWD W_CASFWD c j'). intros i _. symmetry.
  apply (creg_fresh CASFWD c g cc0 N0 N0 _ _ i Hn Hh). auto.
Qed.

(* a slot with no instruction happens in order, after every slot before it *)
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

(* only the CAS's read can happen alone *)
Lemma oh_cas : forall s c i th, run CASFWD s -> done CASFWD s -> oh (cs s c) i = Some th -> c = 0 /\ i = 1.
Proof.
  intros s c i th R CP Oh. pose proof (Inv1_run _ s R) as I.
  assert (L : i < pcs s c) by (apply (passed_h CASFWD s R CP W_CASFWD c i); congruence).
  assert (Cx : is_cas (ai (cs s c) i) = true).
  { destruct (oc (cs s c) i) as [t2|] eqn:O; [exact (proj2 (i_hoc _ s I c i th t2 Oh O))|].
    destruct (i_halfp _ s I c i th O Oh L) as (F & _). apply (cfail_cas _ _ _ F). }
  destruct (cm_set _ s c i I L) as (tau0 & T0). rewrite (proj2 (i_set _ s I c i tau0 T0)), insC in Cx.
  destruct c as [|[|c]]; destruct i as [|[|[|[|i]]]]; simpl in Cx; try discriminate; auto;
    try (destruct i; simpl in Cx; discriminate); destruct c; simpl in Cx; discriminate.
Qed.

Definition f0 : nat -> cell -> val := fun _ _ => 0.

(* the results fixed (S3c) at slots 0..2 are all a slot below 3 consults *)
Ltac fx3 F := destruct (F 0) as [[]|], (F 1) as [[]|], (F 2) as [[]|].

Lemma val_r0 : forall N B F, creg CASFWD 1 (cfr F) 0 N B f0 0 = 0.
Proof.
  intros N B F. rewrite (creg_fresh CASFWD 1 f0 (cfr F) N 0 B (fun i => match i with 0 => B 0 | _ => false end) 0)
    ; [|intros k; reflexivity|intros k; reflexivity|intros i L; destruct i as [|i]; [reflexivity|lia]].
  destruct (B 0); vm_compute; fx3 F; reflexivity.
Qed.

Lemma val_r2 : forall N B F, creg CASFWD 0 (cfr F) 0 N B f0 2 = 0.
Proof.
  intros N B F.
  rewrite (creg_fresh CASFWD 0 f0 (cfr F) N 0 B (fun i => match i with 0 => B 0 | 1 => B 1 | 2 => B 2 | _ => false end) 2)
    ; [|intros k; reflexivity|intros k; reflexivity|intros i L; destruct i as [|[|[|i]]]; try reflexivity; lia].
  destruct (B 0), (B 1), (B 2); vm_compute; fx3 F; reflexivity.
Qed.

Theorem CASFWD_forbidden : forall s, run CASFWD s -> done CASFWD s ->
  ~ (rg (cs s 0) 0 = 2 /\ rg (cs s 0) 1 = vd true 2 /\ rg (cs s 0) 2 = 3 /\ rg (cs s 1) 0 = 3).
Proof.
  intros s R CP (A0 & A1 & A2 & B0). pose proof W_CASFWD as W.
  get_ent CASFWD s R CP W 0 0 E00. get_ent CASFWD s R CP W 1 0 E10.
  (* the slots happened *)
  assert (O : forall c k, (c = 0 /\ k < 4) \/ (c = 1 /\ k < 2) -> oc (cs s c) k = Some (bt s c k)).
  { intros c k Hc. unfold bt, tmo. destruct (oc (cs s c) k) eqn:Oc; auto. exfalso.
    destruct Hc as [(-> & L)|(-> & L)];
      [apply (happened CASFWD s R CP W 0 3 ltac:(vm_compute; discriminate) k ltac:(lia))
      |apply (happened CASFWD s R CP W 1 1 ltac:(vm_compute; discriminate) k ltac:(lia))]; auto;
      (destruct k as [|[|[|[|k]]]]; [..|lia]; first [vm_compute; reflexivity|cbn; unfold rrg, M2Comp.rrg; rewrite A1; reflexivity]). }
  (* the reads and the writes they took *)
  destruct (readv CASFWD s R CP W 1 0 _ 1 E10 3 eq_refl eq_refl eq_refl ltac:(eassumption) ltac:(eassumption) B0 ltac:(lia))
    as (y & _ & Vy & Iy & Ly).
  assert (L1 : bt s 0 3 < bt s 1 0).
  { pose proof (n_wr_of CASFWD s R CP W 1 y Iy) as WO. which_writer WO; subst y; lia. }
  destruct (readv CASFWD s R CP W 0 0 _ 0 E00 2 eq_refl eq_refl eq_refl ltac:(eassumption) ltac:(eassumption) A0 ltac:(lia))
    as (y' & _ & Vy' & Iy' & Ly').
  assert (L3 : bt s 1 1 < bt s 0 0).
  { pose proof (n_wr_of CASFWD s R CP W 0 y' Iy') as WO. which_writer WO; subst y'; lia. }
  (* the CAS and the second read of x come after the first read of x *)
  pose proof (n_tie CASFWD s R CP W 0 0 1 _ _ ltac:(lia) eq_refl eq_refl eq_refl eq_refl ltac:(tie) ltac:(nn)) as T01.
  pose proof (n_tie CASFWD s R CP W 0 1 2 _ _ ltac:(lia) eq_refl eq_refl eq_refl eq_refl ltac:(tie) ltac:(nn)) as T12.
  (* x = r1 - 1 happened after its read of y *)
  assert (L2 : bt s 1 0 < bt s 1 1).
  { destruct (Nat.lt_trichotomy (bt s 1 0) (bt s 1 1)) as [L|[L|L]]; auto; exfalso.
    - apply (neq_bt CASFWD s R CP W 1 0 1 1 _ _ eq_refl ltac:(nn) eq_refl eq_refl ltac:(nn) eq_refl); [congruence|exact L].
    - destruct (early_place s 1 1 _ _ R ltac:(lia) (O 1 0 ltac:(lia)) (O 1 1 ltac:(lia)) L) as (B & N & Fx & HP).
      { intros i ti Ni Oi. destruct i as [|[|i]]; [rewrite (O 1 0 ltac:(lia)) in Oi; injection Oi as <-; lia|congruence|].
        apply (inop_after CASFWD s 1 (S (S i)) ti 0 _ R CP W Oi); [rewrite insC; simpl; destruct i; reflexivity|lia|vm_compute; reflexivity|apply O; lia]. }
      { intros i th Oh. destruct (oh_cas s 1 i th R CP Oh) as [Z _]. discriminate. }
      destruct (HP f0) as (j' & Hj). rewrite (ai_passed CASFWD s 1 1 R CP W ltac:(rewrite (O 1 1 ltac:(lia)); discriminate)) in Hj.
      remember (creg CASFWD 1 (cfr Fx) 0 N B f0) as r eqn:Er. assert (R0 : r 0 = 0) by (subst r; apply val_r0).
      rewrite !insC in Hj. cbn -[creg CASFWD] in Hj. rewrite B0 in Hj.
      destruct j' as [|[|[|j']]]; cbn -[creg CASFWD] in Hj; try discriminate; rewrite R0 in Hj; discriminate. }
  (* a CAS's read alone took x = r1 - 1 *)
  assert (HS : forall th, oh (cs s 0) 1 = Some th -> bt s 1 1 < th).
  { intros th Oh. destruct (Inv2_run _ s R) as (I1 & I2).
    destruct (i_oh _ s I1 0 1 th Oh) as (Eh & Ah & Ch & Kh & _).
    assert (Eih : einstr CASFWD s Eh = ICas Plain [0] T (K 2) (K 3)).
    { unfold einstr. rewrite Ch, Kh. rewrite (ai_passed CASFWD s 0 1 R CP W ltac:(rewrite (O 0 1 ltac:(lia)); discriminate)).
      rewrite insC. reflexivity. }
    destruct (j_val _ s I2 _ Eh _ Ah Eih) as [V _]. specialize (V eq_refl). rewrite Ch, Kh, A1 in V.
    unfold rdvs, rdv in V. simpl in V.
    destruct (erf Eh 0) as [yh|] eqn:Eyh; [|discriminate].
    destruct (j_rf _ s I2 _ Eh 0 yh Ah Eyh) as (Lyh & _ & _ & Iyh).
    pose proof (n_wr_of CASFWD s R CP W 0 yh Iyh) as WO. which_writer WO; subst yh; lia. }
  (* y = r2 happened after the first read of x *)
  assert (L4 : bt s 0 0 < bt s 0 3).
  { destruct (Nat.lt_trichotomy (bt s 0 0) (bt s 0 3)) as [L|[L|L]]; auto; exfalso.
    - apply (neq_bt CASFWD s R CP W 0 0 0 3 _ _ eq_refl ltac:(nn) eq_refl eq_refl ltac:(nn) eq_refl); [congruence|exact L].
    - destruct (early_place s 0 3 _ _ R ltac:(lia) (O 0 0 ltac:(lia)) (O 0 3 ltac:(lia)) L) as (B & N & Fx & HP).
      { intros i ti Ni Oi. destruct i as [|[|[|[|i]]]].
        - rewrite (O 0 0 ltac:(lia)) in Oi. injection Oi as <-. lia.
        - rewrite (O 0 1 ltac:(lia)) in Oi. injection Oi as <-. lia.
        - rewrite (O 0 2 ltac:(lia)) in Oi. injection Oi as <-. lia.
        - congruence.
        - apply (inop_after CASFWD s 0 (S (S (S (S i)))) ti 0 _ R CP W Oi); [rewrite insC; simpl; destruct i; reflexivity|lia|vm_compute; reflexivity|apply O; lia]. }
      { intros i th Oh. destruct (oh_cas s 0 i th R CP Oh) as [_ ->]. pose proof (HS th Oh). lia. }
      destruct (HP f0) as (j' & Hj). rewrite (ai_passed CASFWD s 0 3 R CP W ltac:(rewrite (O 0 3 ltac:(lia)); discriminate)) in Hj.
      remember (creg CASFWD 0 (cfr Fx) 0 N B f0) as r eqn:Er. assert (R2 : r 2 = 0) by (subst r; apply val_r2).
      rewrite !insC in Hj. cbn -[creg CASFWD] in Hj. unfold RG in Hj. rewrite A2 in Hj.
      destruct j' as [|[|[|[|[|j']]]]]; cbn -[creg CASFWD] in Hj; try discriminate; unfold RG in Hj; rewrite R2 in Hj; discriminate. }
  lia.
Qed.
