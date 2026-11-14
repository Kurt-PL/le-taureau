(* Model2: litmus programmes, forbidden outcomes. Cells: x = 0, y = 1, z = 2. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO MIComp M2Lit MINeg M2Oota M2Ev MINegQ.
Require Import M2Iface.

Section Iface.
Context `{IFM : Model}.

(* reading 0 from a cell whose stores are all non-zero: the read took the initial value *)
Lemma read0 : forall (p : prog) (s : M2Model.st) (R : reach (STEP p) s) (CP : done p s) (W : wf p) c k i x E, ins p c k (rrg s c) = i -> xload i (rrg s c) = true ->
  icells i = [x] -> RE s c k E -> einstr p s E = i -> rg (cs s c) k = 0 ->
  (forall c' k' r i', ins p c' k' r = i' -> In x (icells i') -> is_store i' = true -> forall r, cval (icells i') (wvals i' r) x <> 0) ->
  erf E x = None.
Proof.
  intros p s R CP W c k i x E H X Ic RE0 Ei Z NZ.
  destruct (n_rd p s R CP W c k i x E H X (one_in _ _ Ic) RE0 Ei) as (V & Rf).
  rewrite Ic in V. rewrite Z in V. replace (rval i 0) with 0 in V by (destruct i; reflexivity). unfold rdvs, rdv in V. simpl in V.
  destruct (erf E x) as [y|] eqn:Ey; auto.
  exfalso. destruct (Rf y eq_refl) as [Iy _].
  destruct (n_wr_of p s R CP W x y Iy) as (c' & k' & i' & E' & H' & RE' & Wt' & Ic' & Wv & _).
  assert (Ei2 : einstr p s E' = i') by (destruct RE' as (A' & B' & C'); rewrite (einstr_ins p s R CP W _ E' A'), B', C'; auto).
  rewrite (n_ew p s R CP W c' k' i' E' H' RE' Ei2) in Wt'.
  apply andb_prop in Wt'. destruct Wt' as [Wt' _]. apply andb_prop in Wt'. destruct Wt' as [St _].
  rewrite Wv in V. apply (NZ c' k' _ i' H' Ic' St (rrg s c')). congruence.
Qed.

(* a load that read 0 from such a cell knew in order none of its writes *)
Lemma read0Q : forall (p : prog) (s : M2Model.st) (R : reach (STEP p) s) (CP : done p s) (W : wf p) (EV : evok s) c k i x E,
  ins p c k (rrg s c) = i -> xload i (rrg s c) = true -> is_store i = false ->
  icells i = [x] -> RE s c k E -> einstr p s E = i -> rg (cs s c) k = 0 ->
  (forall c' k' r i', ins p c' k' r = i' -> In x (icells i') -> is_store i' = true -> forall r, cval (icells i') (wvals i' r) x <> 0) ->
  forall w, eQ E w -> In w (ids (hs s x)) -> False.
Proof.
  intros p s R CP W EV c k i x E H X St Ic RE0 Ei Z NZ w Q Iw.
  pose proof (read0 p s R CP W c k i x E H X Ic RE0 Ei Z NZ) as N0.
  apply (read_known p s R CP W EV c k i x E w H X (one_in _ _ Ic) RE0 Ei Q Iw); [|left; exact N0].
  intros ->. destruct (j_hist p s (nI2 p s R CP W) x _ Iw) as (e & i0 & A1 & A2 & A3 & _).
  pose proof RE0 as (A & B & C). rewrite A in A1. injection A1 as <-.
  rewrite (n_ew p s R CP W c k i E H RE0 Ei), St in A2. discriminate.
Qed.

(* the same for what it knew in order within the cell *)
Lemma read0Qc : forall (p : prog) (s : M2Model.st) (R : reach (STEP p) s) (CP : done p s) (W : wf p) (EV : evok s) c k i x E,
  ins p c k (rrg s c) = i -> xload i (rrg s c) = true -> is_store i = false ->
  icells i = [x] -> RE s c k E -> einstr p s E = i -> rg (cs s c) k = 0 ->
  (forall c' k' r i', ins p c' k' r = i' -> In x (icells i') -> is_store i' = true -> forall r, cval (icells i') (wvals i' r) x <> 0) ->
  forall w, eQc E w -> In w (ids (hs s x)) -> False.
Proof.
  intros p s R CP W EV c k i x E H X St Ic RE0 Ei Z NZ w Q Iw.
  pose proof (read0 p s R CP W c k i x E H X Ic RE0 Ei Z NZ) as N0.
  apply (read_knownc p s R CP W EV c k i x E w H X (one_in _ _ Ic) RE0 Ei Q Iw); [|left; exact N0].
  intros ->. destruct (j_hist p s (nI2 p s R CP W) x _ Iw) as (e & i0 & A1 & A2 & A3 & _).
  pose proof RE0 as (A & B & C). rewrite A in A1. injection A1 as <-.
  rewrite (n_ew p s R CP W c k i E H RE0 Ei), St in A2. discriminate.
Qed.

(* reading v <> 0 gives the write read *)
Lemma readv : forall (p : prog) (s : M2Model.st) (R : reach (STEP p) s) (CP : done p s) (W : wf p) c k i x E v, ins p c k (rrg s c) = i -> xload i (rrg s c) = true ->
  icells i = [x] -> RE s c k E -> einstr p s E = i -> rval i (rg (cs s c) k) = v -> v <> 0 ->
  exists y, erf E x = Some y /\ wv s y x = v /\ In y (ids (hs s x)) /\ y < bt s c k.
Proof.
  intros p s R CP W c k i x E v H X Ic RE0 Ei Rv N.
  destruct (n_rd p s R CP W c k i x E H X (one_in _ _ Ic) RE0 Ei) as (V & Rf).
  rewrite Ic in V. rewrite Rv in V. unfold rdvs, rdv in V. simpl in V.
  destruct (erf E x) as [y|] eqn:Ey; [|congruence].
  destruct (Rf y eq_refl). exists y. repeat split; auto; congruence.
Qed.

Lemma neq_bt : forall (p : prog) (s : M2Model.st) (R : reach (STEP p) s) (CP : done p s) (W : wf p) c1 k1 c2 k2 i1 i2,
  ins p c1 k1 (rrg s c1) = i1 -> i1 <> INop -> executes i1 (rrg s c1) = true ->
  ins p c2 k2 (rrg s c2) = i2 -> i2 <> INop -> executes i2 (rrg s c2) = true ->
  (c1, k1) <> (c2, k2) -> bt s c1 k1 <> bt s c2 k2.
Proof.
  intros p s R CP W c1 k1 c2 k2 i1 i2 H1 N1 X1 H2 N2 X2 N E.
  destruct (bt_inj p s R CP W _ _ _ _ _ _ (n_insr p s R CP W _ _ _ H1 N1) (n_insr p s R CP W _ _ _ H2 N2) X1 X2 E).
  congruence.
Qed.

Lemma bt_inj' : forall (p : prog) (s : M2Model.st) (R : reach (STEP p) s) (CP : done p s) (W : wf p) c1 k1 c2 k2 i1 i2,
  ins p c1 k1 (rrg s c1) = i1 -> i1 <> INop -> executes i1 (rrg s c1) = true ->
  ins p c2 k2 (rrg s c2) = i2 -> i2 <> INop -> executes i2 (rrg s c2) = true ->
  bt s c1 k1 = bt s c2 k2 -> c1 = c2 /\ k1 = k2.
Proof.
  intros p s R CP W c1 k1 c2 k2 i1 i2 H1 N1 X1 H2 N2 X2 E.
  apply (bt_inj p s R CP W _ _ _ _ _ _ (n_insr p s R CP W _ _ _ H1 N1) (n_insr p s R CP W _ _ _ H2 N2) X1 X2 E).
Qed.

End Iface.
Ltac nz := intros c' k' ? i' H' Ic'; destruct c' as [|[|[|[|[|c']]]]]; destruct k' as [|[|[|[|[|k']]]]];
  vm_compute in H'; subst i'; vm_compute in Ic';
  repeat match type of Ic' with _ \/ _ => destruct Ic' as [Ic'|Ic'] | False => destruct Ic' end; try discriminate;
  let S := fresh "S" in let r := fresh "r" in let Z := fresh "Z" in intros S r Z; vm_compute in S, Z; discriminate.
Section Iface.
Context `{IFM : Model}.



Lemma stw : forall (p : prog) (s : M2Model.st) (R : reach (STEP p) s) (CP : done p s) (W : wf p) c k m x cnd v E,
  ins p c k (rrg s c) = ISt m [x] cnd v -> cnd (rrg s c) = true -> RE s c k E ->
  einstr p s E = ISt m [x] cnd v ->
  ew E = true /\ In (bt s c k) (ids (hs s x)) /\ esrc E (bt s c k).
Proof.
  intros p s R CP W c k m x cnd v E H Cn RE0 Ei.
  assert (Wt : ew E = true).
  { rewrite (n_ew p s R CP W c k _ E H RE0 Ei). unfold icond, ieval. simpl. rewrite Cn. reflexivity. }
  destruct (n_wr1 p s R CP W c k _ x E H RE0 Ei Wt eq_refl) as (A & B & _). auto.
Qed.

Lemma esrc_rf : forall E x y, erf E x = Some y -> esrc E y.
Proof. intros E x y H. unfold esrc, srcv. left. exists x. exact H. Qed.

End Iface.
Ltac ord P s R CP W c j k := pose proof (n_tie P s R CP W c j k _ _ ltac:(lia) eq_refl eq_refl eq_refl eq_refl ltac:(tie) ltac:(nn)).
Section Iface.
Context `{IFM : Model}.

Lemma xg_of_ins : forall (p : prog) (s : M2Model.st) c k i E, RE s c k E -> einstr p s E = i ->
  xgop i (rrg s c) = true -> xg p s E.
Proof. intros p s c k i E (A & B & C) Ei X. exists i. split; auto. Qed.

(* ---------- MP with guard.store / guard.load ---------- *)
Definition MPra : prog := stat [ [st 0 1; fss; st 1 1]; [ld 1; fll; ld 0] ].

Theorem MPra_forbidden : forall s, reach (STEP MPra) s -> done MPra s -> evok s ->
  ~ (rg (cs s 1) 0 = 1 /\ rg (cs s 1) 2 = 0).
Proof.
  intros s R CP EV [A B]. assert (W : wf MPra) by wf_tac.
  get_ent MPra s R CP W 0 0 E00. get_ent MPra s R CP W 0 1 E01. get_ent MPra s R CP W 0 2 E02.
  get_ent MPra s R CP W 1 0 E10. get_ent MPra s R CP W 1 1 E11. get_ent MPra s R CP W 1 2 E12.
  destruct (readv MPra s R CP W 1 0 _ 1 E10 1 eq_refl eq_refl eq_refl H2 Ei2 A ltac:(lia)) as (y & Ey & Vy & Iy & Ly).
  pose proof (n_wr_of MPra s R CP W 1 y Iy) as WO. which_writer WO. subst y.
  assert (W0 : ew E00 = true) by (rewrite (n_ew MPra s R CP W 0 0 _ E00 eq_refl H Ei); reflexivity).
  assert (W2 : ew E02 = true) by (rewrite (n_ew MPra s R CP W 0 2 _ E02 eq_refl H1 Ei1); reflexivity).
  ord MPra s R CP W 0 0 1. ord MPra s R CP W 0 1 2.
  assert (NR : forall tg g, ent s tg = Some g -> ec g = 0 -> bt s 0 1 < tg -> tg < bt s 0 2 -> ~ xss MPra s g).
  { intros tg g Hg Eg L1 L2 Xg. destruct (i_et MPra s (nI1 MPra s R CP W) tg g Hg) as [_ Og].
    assert (Eh : eh g = false).
    { destruct (eh g) eqn:Z; auto. pose proof (eh_cas MPra s R CP W tg g Hg Z) as Q. unfold xss in Xg. rewrite Xg in Q. discriminate. }
    rewrite Eh in Og.
    unfold xss in Xg. rewrite (einstr_ins MPra s R CP W tg g Hg), Eg in Xg. rewrite Eg in Og.
    remember (ek g) as kg eqn:Ek. clear Ek.
    destruct kg as [|[|[|[|kg]]]]; vm_compute in Xg; try discriminate Xg.
    unfold bt, tmo in L1. rewrite Og in L1. lia. }
  pose proof (n_rel MPra s R CP W 0 0 1 2 E00 E01 E02 H H0 H1 ltac:(lia) ltac:(lia) ltac:(lia)
              (or_introl Ei0) W2 NR) as Rl.
  assert (Ow : ownw s 0 (bt s 0 0)) by (destruct H as (Ah & Bh & _); exists E00; auto).
  destruct (n_wr1 MPra s R CP W 0 0 _ 0 E00 eq_refl H Ei W0 eq_refl) as (Ix & Sx & _).
  assert (Q : eQc E12 (bt s 0 0)).
  { apply (Q_ll MPra s R CP W EV 1 0 1 2 E10 E11 E12 ltac:(lia) ltac:(lia) eq_refl H2 H3 H4).
    - exists (ld 1). split; [exact Ei2|reflexivity].
    - exists (ld 0). split; [exact Ei4|reflexivity].
    - nn.
    - exists 1, (bt s 0 2). split; [exact Ey|]. left. apply Rl; [right; exact Sx|right; exact Ow].
    - destruct H as (Ah & Bh & _). apply (ownw_other MPra s R CP W EV 1 _ E00 Ah). rewrite Bh. discriminate. }
  assert (NZ : forall c' k' r i', ins MPra c' k' r = i' -> In 0 (icells i') -> is_store i' = true ->
                 forall r, cval (icells i') (wvals i' r) 0 <> 0) by nz.
  apply (read0Qc MPra s R CP W EV 1 2 _ 0 E12 eq_refl eq_refl eq_refl eq_refl H4 Ei4 B NZ _ Q Ix).
Qed.

(* ---------- SB with guard() ---------- *)
Definition SBf : prog := stat [ [st 0 1; ffull; ld 1]; [st 1 1; ffull; ld 0] ].

Theorem SBf_forbidden : forall s, reach (STEP SBf) s -> done SBf s -> evok s -> ~ (rg (cs s 0) 2 = 0 /\ rg (cs s 1) 2 = 0).
Proof.
  intros s R CP EV [A B]. assert (W : wf SBf) by wf_tac.
  get_ent SBf s R CP W 0 0 E00. get_ent SBf s R CP W 0 1 E01. get_ent SBf s R CP W 0 2 E02.
  get_ent SBf s R CP W 1 0 E10. get_ent SBf s R CP W 1 1 E11. get_ent SBf s R CP W 1 2 E12.
  assert (NZ0 : forall c' k' r i', ins SBf c' k' r = i' -> In 0 (icells i') -> is_store i' = true ->
                  forall r, cval (icells i') (wvals i' r) 0 <> 0) by nz.
  assert (NZ1 : forall c' k' r i', ins SBf c' k' r = i' -> In 1 (icells i') -> is_store i' = true ->
                  forall r, cval (icells i') (wvals i' r) 1 <> 0) by nz.
  destruct (stw SBf s R CP W 0 0 _ _ _ _ E00 eq_refl eq_refl H Ei) as (_ & Ix & Sx).
  destruct (stw SBf s R CP W 1 0 _ _ _ _ E10 eq_refl eq_refl H2 Ei2) as (_ & Iy & Sy).
  destruct (n_po SBf s R CP W 0 0 1 _ _ E00 E01 ltac:(lia) eq_refl eq_refl eq_refl ltac:(tie) H H0) as [_ P0].
  destruct (n_po SBf s R CP W 1 0 1 _ _ E10 E11 ltac:(lia) eq_refl eq_refl eq_refl ltac:(tie) H2 H3) as [_ P1].
  assert (G0 : xg SBf s E01) by (eapply xg_of_ins; eauto; reflexivity).
  assert (G1 : xg SBf s E11) by (eapply xg_of_ins; eauto; reflexivity).
  destruct (Nat.lt_trichotomy (bt s 0 1) (bt s 1 1)) as [L|[L|L]].
  - destruct (n_G SBf s R CP W 0 1 1 1 E01 E11 H0 H3 G0 G1 L) as [K1 _].
    assert (Q : eQ E12 (bt s 0 0)).
    { apply (Q_guard SBf s R CP W EV 1 1 2 E11 E12 ltac:(lia) eq_refl H3 H4 ltac:(nn)).
      - right. exists (ld 0). split; [exact Ei4|reflexivity].
      - apply K1, P0, Sx. }
    apply (read0Q SBf s R CP W EV 1 2 _ 0 E12 eq_refl eq_refl eq_refl eq_refl H4 Ei4 B NZ0 _ Q Ix).
  - destruct (bt_inj' SBf s R CP W 0 1 1 1 _ _ eq_refl ltac:(nn) eq_refl eq_refl ltac:(nn) eq_refl L). discriminate.
  - destruct (n_G SBf s R CP W 1 1 0 1 E11 E01 H3 H0 G1 G0 L) as [K1 _].
    assert (Q : eQ E02 (bt s 1 0)).
    { apply (Q_guard SBf s R CP W EV 0 1 2 E01 E02 ltac:(lia) eq_refl H0 H1 ltac:(nn)).
      - right. exists (ld 1). split; [exact Ei1|reflexivity].
      - apply K1, P1, Sy. }
    apply (read0Q SBf s R CP W EV 0 2 _ 1 E02 eq_refl eq_refl eq_refl eq_refl H1 Ei1 A NZ1 _ Q Iy).
Qed.

End Iface.
Ltac NZ P x := assert (forall c' k' r i', ins P c' k' r = i' -> In x (icells i') -> is_store i' = true ->
                  forall r, cval (icells i') (wvals i' r) x <> 0) by nz.
Section Iface.
Context `{IFM : Model}.

End Iface.
Ltac ents P s R CP W :=
  repeat match goal with
  | |- _ => fail
  end.
Section Iface.
Context `{IFM : Model}.

(* ---------- LB with guard() (with guard.load or guard.store it is allowed) ---------- *)
Definition LBx (f : instr) : prog := stat [ [ld 0; f; st 1 1]; [ld 1; f; st 0 1] ].

End Iface.
Ltac lb_proof P :=
  let s := fresh "s" in let R := fresh "R" in let CP := fresh "CP" in let A := fresh "A" in let B := fresh "B" in
  let W := fresh "W" in let E00 := fresh "E00" in let E10 := fresh "E10" in
  intros s R CP [A B]; assert (W : wf P) by wf_tac;
  get_ent P s R CP W 0 0 E00; get_ent P s R CP W 1 0 E10;
  ord P s R CP W 0 0 1; ord P s R CP W 0 1 2; ord P s R CP W 1 0 1; ord P s R CP W 1 1 2;
  let y := fresh "y" in let Iy := fresh "Iy" in let Ly := fresh "Ly" in
  destruct (readv P s R CP W 0 0 _ 0 E00 1 eq_refl eq_refl eq_refl ltac:(eassumption) ltac:(eassumption) A ltac:(lia))
    as (y & _ & _ & Iy & Ly);
  let WO := fresh "WO" in pose proof (n_wr_of P s R CP W 0 y Iy) as WO; which_writer WO; subst y;
  let y' := fresh "y" in let Iy' := fresh "Iy" in let Ly' := fresh "Ly" in
  destruct (readv P s R CP W 1 0 _ 1 E10 1 eq_refl eq_refl eq_refl ltac:(eassumption) ltac:(eassumption) B ltac:(lia))
    as (y' & _ & _ & Iy' & Ly');
  let WO' := fresh "WO" in pose proof (n_wr_of P s R CP W 1 y' Iy') as WO'; which_writer WO'; subst y'; lia.
Section Iface.
Context `{IFM : Model}.

Theorem LBfull_forbidden : forall s, reach (STEP (LBx ffull)) s -> done (LBx ffull) s ->
  ~ (rg (cs s 0) 0 = 1 /\ rg (cs s 1) 0 = 1).
Proof. lb_proof (LBx ffull). Qed.

(* ---------- OOTA: r0 = x; y = r0 || r1 = y; x = r1  with 42 ---------- *)
Definition OOTA : prog := stat [ [ld 0; ISt Plain [1] T (RG 0)]; [ld 1; ISt Plain [0] T (RG 0)] ].
Lemma OOTA_cf : cas_free OOTA.
Proof. intros c k r. unfold OOTA. rewrite ins_stat. destruct c as [|[|[|c]]]; destruct k as [|[|[|k]]]; simpl; try reflexivity; try (destruct c; reflexivity); try (destruct k; reflexivity). Qed.
Theorem OOTA_forbidden : forall s, reach (STEP OOTA) s -> ~ (rg (cs s 0) 0 = 42 /\ rg (cs s 1) 0 = 42).
Proof.
  intros s R [A B].
  assert (Cl : tclosed OOTA (fun v => v = 0 \/ v = 1)).
  { intros c k r Hr. apply (cl_one1 _ _ _ (or_intror eq_refl)); [| left; reflexivity |]; unfold OOTA; rewrite ins_stat;
    destruct c as [|[|c]]; destruct k as [|[|k]]; simpl; try lia; try (left; reflexivity);
    try (pose proof (Hr 0 ltac:(lia)) as H0; unfold OOTA in H0; rewrite ins_stat in H0; simpl in H0; exact (kV_ld1 _ _ _ _ _ H0));
    repeat match goal with |- context [match ?z with _ => _ end] => destruct z end; simpl; try lia; left; reflexivity. }
  assert (Wf : wf OOTA) by wf_tac.
  destruct (g_no_thin_air OOTA _ (GG OOTA) Wf _ (or_introl eq_refl) Cl s R) as [_ Rg].
  (* slot 0 not yet passed: it did not happen (it happens only once passed,
     and nothing is a CAS's read alone), so its register is 0 *)
  destruct (Nat.eq_dec (pcs s 0) 0) as [Z|NZ].
  { assert (O0 : oc (cs s 0) 0 = None) by (destruct (oc (cs s 0) 0) eqn:E; [exfalso; pose proof (g_slot0 OOTA _ (GG OOTA) s R 0 ltac:(rewrite E; discriminate)); lia|reflexivity]).
    rewrite (i_rg0 OOTA s (I1g _ s R) 0 0 O0 (g_no_half OOTA _ (GG OOTA) OOTA_cf s R 0 0)) in A. discriminate. }
  assert (L0 : 0 < pcs s 0) by lia.
  pose proof (Rg 0 0) as Q. rewrite (passed_ai OOTA s 0 0 (I1g _ s R) L0) in Q.
  unfold OOTA in Q. rewrite ins_stat in Q. simpl in Q. apply kV_ld1 in Q. rewrite A in Q. lia.
Qed.






(* ---------- 2+2W with guard() ---------- *)
Definition W22f : prog := stat [ [st 0 1; ffull; st 1 2]; [st 1 1; ffull; st 0 2] ].
Theorem W22f_forbidden : forall s, reach (STEP W22f) s -> done W22f s -> evok s -> ~ (final s 0 = 1 /\ final s 1 = 1).
Proof.
  intros s R CP EV (A & B). assert (W : wf W22f) by wf_tac.
  get_ent W22f s R CP W 0 0 E00. get_ent W22f s R CP W 0 1 E01. get_ent W22f s R CP W 0 2 E02.
  get_ent W22f s R CP W 1 0 E10. get_ent W22f s R CP W 1 1 E11. get_ent W22f s R CP W 1 2 E12.
  destruct (n_final W22f s R CP W 0 1 A ltac:(lia)) as (z & Iz & Vz & Lx).
  pose proof (n_wr_of W22f s R CP W 0 z Iz) as WO. which_writer WO. subst z.
  destruct (n_final W22f s R CP W 1 1 B ltac:(lia)) as (z & Iz2 & Vz2 & Ly).
  pose proof (n_wr_of W22f s R CP W 1 z Iz2) as WO. which_writer WO. subst z.
  destruct (stw W22f s R CP W 0 0 _ _ _ _ E00 eq_refl eq_refl H Ei) as (W00 & I00 & S00).
  destruct (stw W22f s R CP W 0 2 _ _ _ _ E02 eq_refl eq_refl H1 Ei1) as (W02 & I02 & S02).
  destruct (stw W22f s R CP W 1 0 _ _ _ _ E10 eq_refl eq_refl H2 Ei2) as (W10 & I10 & S10).
  destruct (stw W22f s R CP W 1 2 _ _ _ _ E12 eq_refl eq_refl H4 Ei4) as (W12 & I12 & S12).
  destruct (n_po W22f s R CP W 0 0 1 _ _ E00 E01 ltac:(lia) eq_refl eq_refl eq_refl ltac:(tie) H H0) as [_ P0].
  destruct (n_po W22f s R CP W 1 0 1 _ _ E10 E11 ltac:(lia) eq_refl eq_refl eq_refl ltac:(tie) H2 H3) as [_ P1].
  assert (G0 : xg W22f s E01) by (eapply xg_of_ins; eauto; reflexivity).
  assert (G1 : xg W22f s E11) by (eapply xg_of_ins; eauto; reflexivity).
  destruct (Nat.lt_trichotomy (bt s 0 1) (bt s 1 1)) as [L|[L|L]].
  - destruct (n_G W22f s R CP W 0 1 1 1 E01 E11 H0 H3 G0 G1 L) as [K1 _].
    assert (Q : eQ E12 (bt s 0 0)).
    { apply (Q_guard W22f s R CP W EV 1 1 2 E11 E12 ltac:(lia) eq_refl H3 H4 ltac:(nn)); [left; exact W12|].
      apply K1, P0, S00. }
    exact (write_known W22f s R CP W EV 1 2 E12 0 (bt s 0 0) H4 Q
             (Lx _ I12 (neq_bt W22f s R CP W 1 2 0 0 _ _ eq_refl ltac:(nn) eq_refl eq_refl ltac:(nn) eq_refl ltac:(congruence)))).
  - destruct (bt_inj' W22f s R CP W 0 1 1 1 _ _ eq_refl ltac:(nn) eq_refl eq_refl ltac:(nn) eq_refl L). discriminate.
  - destruct (n_G W22f s R CP W 1 1 0 1 E11 E01 H3 H0 G1 G0 L) as [K1 _].
    assert (Q : eQ E02 (bt s 1 0)).
    { apply (Q_guard W22f s R CP W EV 0 1 2 E01 E02 ltac:(lia) eq_refl H0 H1 ltac:(nn)); [left; exact W02|].
      apply K1, P1, S10. }
    exact (write_known W22f s R CP W EV 0 2 E02 1 (bt s 1 0) H1 Q
             (Ly _ I02 (neq_bt W22f s R CP W 0 2 1 0 _ _ eq_refl ltac:(nn) eq_refl eq_refl ltac:(nn) eq_refl ltac:(congruence)))).
Qed.

(* ---------- R with guard() ---------- *)
Definition Rf : prog := stat [ [st 0 1; ffull; st 1 1]; [st 1 2; ffull; ld 0] ].
Theorem Rf_forbidden : forall s, reach (STEP Rf) s -> done Rf s -> evok s -> ~ (final s 1 = 2 /\ rg (cs s 1) 2 = 0).
Proof.
  intros s R CP EV (A & B). assert (W : wf Rf) by wf_tac.
  get_ent Rf s R CP W 0 0 E00. get_ent Rf s R CP W 0 1 E01. get_ent Rf s R CP W 0 2 E02.
  get_ent Rf s R CP W 1 0 E10. get_ent Rf s R CP W 1 1 E11. get_ent Rf s R CP W 1 2 E12. NZ Rf 0.
  destruct (n_final Rf s R CP W 1 2 A ltac:(lia)) as (z & Iz & Vz & Ly).
  pose proof (n_wr_of Rf s R CP W 1 z Iz) as WO. which_writer WO. subst z.
  destruct (stw Rf s R CP W 0 0 _ _ _ _ E00 eq_refl eq_refl H Ei) as (W00 & I00 & S00).
  destruct (stw Rf s R CP W 0 2 _ _ _ _ E02 eq_refl eq_refl H1 Ei1) as (W02 & I02 & S02).
  destruct (stw Rf s R CP W 1 0 _ _ _ _ E10 eq_refl eq_refl H2 Ei2) as (W10 & I10 & S10).
  destruct (n_po Rf s R CP W 0 0 1 _ _ E00 E01 ltac:(lia) eq_refl eq_refl eq_refl ltac:(tie) H H0) as [_ P0].
  destruct (n_po Rf s R CP W 1 0 1 _ _ E10 E11 ltac:(lia) eq_refl eq_refl eq_refl ltac:(tie) H2 H3) as [_ P1].
  assert (G0 : xg Rf s E01) by (eapply xg_of_ins; eauto; reflexivity).
  assert (G1 : xg Rf s E11) by (eapply xg_of_ins; eauto; reflexivity).
  destruct (Nat.lt_trichotomy (bt s 0 1) (bt s 1 1)) as [L|[L|L]].
  - destruct (n_G Rf s R CP W 0 1 1 1 E01 E11 H0 H3 G0 G1 L) as [K1 _].
    assert (Q : eQ E12 (bt s 0 0)).
    { apply (Q_guard Rf s R CP W EV 1 1 2 E11 E12 ltac:(lia) eq_refl H3 H4 ltac:(nn)).
      - right. exists (ld 0). split; [exact Ei4|reflexivity].
      - apply K1, P0, S00. }
    apply (read0Q Rf s R CP W EV 1 2 _ 0 E12 eq_refl eq_refl eq_refl eq_refl H4 Ei4 B H5 _ Q I00).
  - destruct (bt_inj' Rf s R CP W 0 1 1 1 _ _ eq_refl ltac:(nn) eq_refl eq_refl ltac:(nn) eq_refl L). discriminate.
  - destruct (n_G Rf s R CP W 1 1 0 1 E11 E01 H3 H0 G1 G0 L) as [K1 _].
    assert (Q : eQ E02 (bt s 1 0)).
    { apply (Q_guard Rf s R CP W EV 0 1 2 E01 E02 ltac:(lia) eq_refl H0 H1 ltac:(nn)); [left; exact W02|].
      apply K1, P1, S10. }
    exact (write_known Rf s R CP W EV 0 2 E02 1 (bt s 1 0) H1 Q
             (Ly _ I02 (neq_bt Rf s R CP W 0 2 1 0 _ _ eq_refl ltac:(nn) eq_refl eq_refl ltac:(nn) eq_refl ltac:(congruence)))).
Qed.

(* ---------- IRIW with guard() between the reads ---------- *)
Definition IRIWf : prog := stat [ [st 0 1]; [st 1 1]; [ld 0; ffull; ld 1]; [ld 1; ffull; ld 0] ].
Theorem IRIWf_forbidden : forall s, reach (STEP IRIWf) s -> done IRIWf s -> evok s ->
  ~ (rg (cs s 2) 0 = 1 /\ rg (cs s 2) 2 = 0 /\ rg (cs s 3) 0 = 1 /\ rg (cs s 3) 2 = 0).
Proof.
  intros s R CP EV (A & B & C & D). assert (W : wf IRIWf) by wf_tac.
  get_ent IRIWf s R CP W 2 0 E20. get_ent IRIWf s R CP W 2 1 E21. get_ent IRIWf s R CP W 2 2 E22.
  get_ent IRIWf s R CP W 3 0 E30. get_ent IRIWf s R CP W 3 1 E31. get_ent IRIWf s R CP W 3 2 E32.
  NZ IRIWf 0. NZ IRIWf 1.
  destruct (readv IRIWf s R CP W 2 0 _ 0 E20 1 eq_refl eq_refl eq_refl H Ei A ltac:(lia)) as (y & Ey & ? & Iy & _).
  destruct (readv IRIWf s R CP W 3 0 _ 1 E30 1 eq_refl eq_refl eq_refl H2 Ei2 C ltac:(lia)) as (y' & Ey' & ? & Iy' & _).
  destruct (n_po IRIWf s R CP W 2 0 1 _ _ E20 E21 ltac:(lia) eq_refl eq_refl eq_refl ltac:(tie) H H0) as [_ P2].
  destruct (n_po IRIWf s R CP W 3 0 1 _ _ E30 E31 ltac:(lia) eq_refl eq_refl eq_refl ltac:(tie) H2 H3) as [_ P3].
  assert (G2 : xg IRIWf s E21) by (eapply xg_of_ins; eauto; reflexivity).
  assert (G3 : xg IRIWf s E31) by (eapply xg_of_ins; eauto; reflexivity).
  destruct (Nat.lt_trichotomy (bt s 2 1) (bt s 3 1)) as [L|[L|L]].
  - destruct (n_G IRIWf s R CP W 2 1 3 1 E21 E31 H0 H3 G2 G3 L) as [K _].
    assert (Q : eQ E32 y).
    { apply (Q_guard IRIWf s R CP W EV 3 1 2 E31 E32 ltac:(lia) eq_refl H3 H4 ltac:(nn)).
      - right. exists (ld 0). split; [exact Ei4|reflexivity].
      - apply K, P2. eapply esrc_rf. eauto. }
    apply (read0Q IRIWf s R CP W EV 3 2 _ 0 E32 eq_refl eq_refl eq_refl eq_refl H4 Ei4 D H5 _ Q Iy).
  - destruct (bt_inj' IRIWf s R CP W 2 1 3 1 _ _ eq_refl ltac:(nn) eq_refl eq_refl ltac:(nn) eq_refl L). discriminate.
  - destruct (n_G IRIWf s R CP W 3 1 2 1 E31 E21 H3 H0 G3 G2 L) as [K _].
    assert (Q : eQ E22 y').
    { apply (Q_guard IRIWf s R CP W EV 2 1 2 E21 E22 ltac:(lia) eq_refl H0 H1 ltac:(nn)).
      - right. exists (ld 1). split; [exact Ei1|reflexivity].
      - apply K, P3. eapply esrc_rf. eauto. }
    apply (read0Q IRIWf s R CP W EV 2 2 _ 1 E22 eq_refl eq_refl eq_refl eq_refl H1 Ei1 B H6 _ Q Iy').
Qed.

(* ---------- coherence ---------- *)
Definition CoRR : prog := stat [ [st 0 1]; [ld 0; ld 0] ].
Theorem CoRR_forbidden : forall s, reach (STEP CoRR) s -> done CoRR s -> evok s -> ~ (rg (cs s 1) 0 = 1 /\ rg (cs s 1) 1 = 0).
Proof.
  intros s R CP EV (A & B). assert (W : wf CoRR) by wf_tac.
  get_ent CoRR s R CP W 1 0 E10. get_ent CoRR s R CP W 1 1 E11. NZ CoRR 0.
  destruct (readv CoRR s R CP W 1 0 _ 0 E10 1 eq_refl eq_refl eq_refl H Ei A ltac:(lia)) as (y & Ey & ? & Iy & Ly).
  pose proof (read0 CoRR s R CP W 1 1 _ 0 E11 eq_refl eq_refl eq_refl H0 Ei0 B H1) as N1.
  ord CoRR s R CP W 1 0 1.
  apply (c3 CoRR s R CP W EV 0 y (bt s 1 0) (bt s 1 1)).
  - apply (c_took CoRR s R CP W EV 1 0 (ld 0) 0 E10 y eq_refl eq_refl (or_introl eq_refl) H Ei Ey). lia.
  - apply (c_po CoRR s R CP W EV 1 0 1 (ld 0) (ld 0) E10 E11 0 ltac:(lia) eq_refl eq_refl H H0 Ei Ei0 eq_refl eq_refl
             (or_introl eq_refl) (or_introl eq_refl)).
  - apply (c_missed CoRR s R CP W EV 1 1 (ld 0) 0 E11 y eq_refl eq_refl (or_introl eq_refl) H0 Ei0 Iy); [lia|left; exact N1].
Qed.

Definition CoWW : prog := stat [ [st 0 1; st 0 2] ].
Theorem CoWW_forbidden : forall s, reach (STEP CoWW) s -> done CoWW s -> evok s -> ~ final s 0 = 1.
Proof.
  intros s R CP EV A. assert (W : wf CoWW) by wf_tac.
  get_ent CoWW s R CP W 0 0 E00. get_ent CoWW s R CP W 0 1 E01.
  destruct (n_final CoWW s R CP W 0 1 A ltac:(lia)) as (z & Iz & Vz & Lx).
  pose proof (n_wr_of CoWW s R CP W 0 z Iz) as WO. which_writer WO. subst z.
  destruct (stw CoWW s R CP W 0 1 _ _ _ _ E01 eq_refl eq_refl H0 Ei0) as (W01 & I01 & _).
  apply (c2 CoWW s R CP W EV 0 (bt s 0 0) (bt s 0 1)).
  - apply (c_po CoWW s R CP W EV 0 0 1 (st 0 1) (st 0 2) E00 E01 0 ltac:(lia) eq_refl eq_refl H H0 Ei Ei0 eq_refl eq_refl
             (or_introl eq_refl) (or_introl eq_refl)).
  - apply (c_hist CoWW s R CP W EV). apply Lx; auto. apply (neq_bt CoWW s R CP W 0 1 0 0 _ _ eq_refl ltac:(nn) eq_refl eq_refl ltac:(nn) eq_refl). congruence.
Qed.

(* a read never takes its own context's later write *)
Definition CoRW1 : prog := stat [ [ld 0; st 0 1] ].
Theorem CoRW1_forbidden : forall s, reach (STEP CoRW1) s -> done CoRW1 s -> ~ rg (cs s 0) 0 = 1.
Proof.
  intros s R CP A. assert (W : wf CoRW1) by wf_tac.
  get_ent CoRW1 s R CP W 0 0 E00.
  destruct (readv CoRW1 s R CP W 0 0 _ 0 E00 1 eq_refl eq_refl eq_refl H Ei A ltac:(lia)) as (y & Ey & ? & Iy & Ly).
  pose proof (n_wr_of CoRW1 s R CP W 0 y Iy) as WO. which_writer WO. subst y.
  ord CoRW1 s R CP W 0 0 1. lia.
Qed.

Definition CoRW2 : prog := stat [ [ld 0; st 0 1]; [st 0 2] ].
Theorem CoRW2_forbidden : forall s, reach (STEP CoRW2) s -> done CoRW2 s -> evok s -> ~ (rg (cs s 0) 0 = 2 /\ final s 0 = 2).
Proof.
  intros s R CP EV (A & B). assert (W : wf CoRW2) by wf_tac.
  get_ent CoRW2 s R CP W 0 0 E00. get_ent CoRW2 s R CP W 0 1 E01.
  destruct (readv CoRW2 s R CP W 0 0 _ 0 E00 2 eq_refl eq_refl eq_refl H Ei A ltac:(lia)) as (y & Ey & ? & Iy & Ly).
  pose proof (n_wr_of CoRW2 s R CP W 0 y Iy) as WO. which_writer WO. subst y.
  destruct (n_final CoRW2 s R CP W 0 2 B ltac:(lia)) as (z & Iz & Vz & Lx).
  pose proof (n_wr_of CoRW2 s R CP W 0 z Iz) as WO. which_writer WO. subst z.
  destruct (stw CoRW2 s R CP W 0 1 _ _ _ _ E01 eq_refl eq_refl H0 Ei0) as (W01 & I01 & _).
  apply (c3 CoRW2 s R CP W EV 0 (bt s 0 1) (bt s 1 0) (bt s 0 0)).
  - apply (c_hist CoRW2 s R CP W EV). apply Lx; auto. apply (neq_bt CoRW2 s R CP W 0 1 1 0 _ _ eq_refl ltac:(nn) eq_refl eq_refl ltac:(nn) eq_refl). congruence.
  - apply (c_took CoRW2 s R CP W EV 0 0 (ld 0) 0 E00 (bt s 1 0) eq_refl eq_refl (or_introl eq_refl) H Ei Ey). lia.
  - apply (c_po CoRW2 s R CP W EV 0 0 1 (ld 0) (st 0 1) E00 E01 0 ltac:(lia) eq_refl eq_refl H H0 Ei Ei0 eq_refl eq_refl
             (or_introl eq_refl) (or_introl eq_refl)).
Qed.

Definition CoWR : prog := stat [ [st 0 1; ld 0]; [st 0 2] ].
Theorem CoWR_forbidden : forall s, reach (STEP CoWR) s -> done CoWR s -> evok s -> ~ (rg (cs s 0) 1 = 2 /\ final s 0 = 1).
Proof.
  intros s R CP EV (A & B). assert (W : wf CoWR) by wf_tac.
  get_ent CoWR s R CP W 0 0 E00. get_ent CoWR s R CP W 0 1 E01.
  destruct (readv CoWR s R CP W 0 1 _ 0 E01 2 eq_refl eq_refl eq_refl H0 Ei0 A ltac:(lia)) as (y & Ey & ? & Iy & Ly).
  pose proof (n_wr_of CoWR s R CP W 0 y Iy) as WO. which_writer WO. subst y.
  destruct (n_final CoWR s R CP W 0 1 B ltac:(lia)) as (z & Iz & Vz & Lx).
  pose proof (n_wr_of CoWR s R CP W 0 z Iz) as WO. which_writer WO. subst z.
  destruct (stw CoWR s R CP W 0 0 _ _ _ _ E00 eq_refl eq_refl H Ei) as (_ & I00 & S00).
  assert (O : older (hs s 0) (bt s 1 0) (bt s 0 0)).
  { apply Lx; auto. apply (neq_bt CoWR s R CP W 1 0 0 0 _ _ eq_refl ltac:(nn) eq_refl eq_refl ltac:(nn) eq_refl). congruence. }
  apply (c2 CoWR s R CP W EV 0 (bt s 0 0) (bt s 0 1)).
  - apply (c_po CoWR s R CP W EV 0 0 1 (st 0 1) (ld 0) E00 E01 0 ltac:(lia) eq_refl eq_refl H H0 Ei Ei0 eq_refl eq_refl
             (or_introl eq_refl) (or_introl eq_refl)).
  - apply (c_missed CoWR s R CP W EV 0 1 (ld 0) 0 E01 (bt s 0 0) eq_refl eq_refl (or_introl eq_refl) H0 Ei0 I00).
    + apply (neq_bt CoWR s R CP W 0 0 0 1 _ _ eq_refl ltac:(nn) eq_refl eq_refl ltac:(nn) eq_refl). congruence.
    + right. exists (bt s 1 0). auto.
Qed.

End Iface.
