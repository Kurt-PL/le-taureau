(* Model2: the two readings of R1's "for every value the loads not yet done
   could return" agree on every reachable state of a well-formed programme.

   - Constraint form (ccont): registers r with the slots before pc as they
     are, register 0 where no read comes, every pending access the first
     coming instruction tied to it with its value, and every read R1 counts
     on, not a pending read, taking its binder's value.
   - Definitional form (creg, the model's): registers built slot by slot
     from free values f.

   Theorem cont_equiv: a register function is in the constraint form iff it
   is the definitional registers of some free values. Hence the two forms of
   early_ok agree (early_ok_equiv). *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2Oota M2Cont.

Definition pslot (p : prog) (c : nat) (cc : cst) (pc : nat) (r : regs) (j : nat) : Prop :=
  (exists k d, placed p c cc pc r k d j) \/ (exists k m xs, hplaced p c cc pc r k m xs j).

Definition rdat (p : prog) (c : nat) (r : regs) (j : nat) : bool := is_load (ins p c j r) && icond (ins p c j r) r.

(* registers r and, in each cell, the values V the reads take *)
Definition ccont (p : prog) (c : nat) (cc : cst) (pc : nat) (B : nat -> bool) (r : regs) (V : nat -> cell -> val)
  : Prop :=
  (forall j, j < pc -> r j = rg cc j /\ forall x, V j x = rv cc j x) /\
  (forall j, pc <= j -> rdat p c r j = false -> r j = 0) /\
  (forall j, pc <= j -> rdat p c r j = true -> rval (ins p c j r) (r j) = enc (map (V j) (icells (ins p c j r)))) /\
  (* the verdict of a CAS: that of its access if it happened; the result fixed there (S3c), a success only
     where its values are equal; a failure if its read half committed to one; a success only if its values
     are equal (free otherwise: failure is always possible) *)
  (forall j, pc <= j -> rdat p c r j = true -> is_cas (ins p c j r) = true ->
     (forall k d, placed p c cc pc r k d j -> vok (r j) = vok (rg cc k)) /\
     (forall k m xs, hplaced p c cc pc r k m xs j -> oc cc k = None -> vok (rg cc k) = false -> fx cc j = None ->
        vok (r j) = false) /\
     (vok (r j) = true -> Nat.eqb (vv (r j)) (cexp (ins p c j r) r) = true) /\
     (forall b, fx cc j = Some b -> (forall k d, ~ placed p c cc pc r k d j) ->
        vok (r j) = b && Nat.eqb (vv (r j)) (cexp (ins p c j r) r))) /\
  (forall k d, pending cc pc k d ->
     exists j, placed p c cc pc r k d j /\
       (is_load (inst_of d) = true -> forall x, In x (icells (inst_of d)) -> V j x = rv cc k x)) /\
  (forall k m xs, hpending cc pc k m xs -> oc cc k = None ->
     exists j, hplaced p c cc pc r k m xs j /\ forall x, In x (icells (ins p c j r)) -> V j x = rv cc k x) /\
  (forall j x b, pc <= j -> B j = true -> ~ pslot p c cc pc r j -> fbinder p c r j x = Some b ->
     V j x = bvx p c r b x (V b x)).

Section Eq.
Variables (p : prog) (s : st).
Hypothesis W : wf p.
Hypothesis Wc : cellful p.
Hypothesis R : run p s.
Let I : Inv1 p s := Inv1_run p s R.
Let J : Inv2 p s := proj2 (Inv2_run p s R).

Lemma placed_ext : forall c r r' k d j, (forall i, r i = r' i) ->
  placed p c (cs s c) (pcs s c) r k d j -> placed p c (cs s c) (pcs s c) r' k d j.
Proof.
  intros c r r' k d j E (Pk & t & O & F). split; auto. exists t. split; auto. apply (first_at_ext p c _ _ r r' t d j W E F).
Qed.

(* a binder in cell x: an access to x that comes; a load and a CAS read there *)
Lemma binder_read : forall c r j x b, fbinder p c r j x = Some b ->
  (rdat p c r b = true /\ In x (icells (ins p c b r))) \/ (exists m ys cb v, ins p c b r = ISt m ys cb v).
Proof.
  intros c r j x b Fb. destruct (fbinder_shape _ _ _ _ _ _ Fb) as (Ex & Ix & _).
  unfold rdat. unfold executes in Ex.
  destruct (ins p c b r) as [m ys cb|m ys cb v|m ys cb e n| |]; simpl in *; auto; try (right; eauto; fail);
    try (destruct Ix; fail); left; split; auto.
Qed.

Lemma bvx_store : forall c r b x v1 v2 m ys cb v, ins p c b r = ISt m ys cb v -> bvx p c r b x v1 = bvx p c r b x v2.
Proof. intros c r b x v1 v2 m ys cb v E. unfold bvx. rewrite E. reflexivity. Qed.

Lemma hplaced_same : forall c r k m1 m2 xs1 xs2 j1 j2,
  hplaced p c (cs s c) (pcs s c) r k m1 xs1 j1 -> hplaced p c (cs s c) (pcs s c) r k m2 xs2 j2 -> j1 = j2.
Proof.
  intros c r k m1 m2 xs1 xs2 j1 j2 ((_ & _ & P1) & _ & t1 & O1 & F1) ((_ & _ & P2) & _ & t2 & O2 & F2).
  rewrite P1 in P2. injection P2 as <- <-. rewrite O1 in O2. injection O2 as <-.
  apply (first_atR_unique p c _ _ r t1 m1 xs1 j1 j2 Wc F1 F2).
Qed.

Lemma rg_rv_h : forall c k t, oc (cs s c) k = None -> oh (cs s c) k = Some t ->
  vv (rg (cs s c) k) = enc (map (rv (cs s c) k) (icells (ai (cs s c) k))).
Proof.
  intros c k t O Oh. destruct (half_vals p s c k t I J O Oh) as [Rv Rg]. rewrite Rg. f_equal.
  unfold rdvals. apply map_ext. intros x. symmetry. apply Rv.
Qed.

Lemma hplaced_icells : forall c r k m xs j, hplaced p c (cs s c) (pcs s c) r k m xs j ->
  icells (ins p c j r) = icells (ai (cs s c) k) /\ is_load (ins p c j r) && icond (ins p c j r) r = true.
Proof.
  intros c r k m xs j ((P1 & _ & P3) & C & t & O & F). pose proof (first_atR_eofR _ _ _ _ _ _ _ _ _ F) as D.
  destruct (i_half p s I c k t C O P1) as (_ & (xs0 & Ax) & _). rewrite Ax in P3 |- *. injection P3 as <- <-.
  destruct (ins p c j r) as [m1 x1 c1|m1 x1 c1 v1|m0 x0 c0 e0 n0|f1|]; simpl in D; try discriminate.
  destruct (c0 r) eqn:C0; [injection D as -> ->|discriminate]. unfold icond, ieval. simpl. rewrite C0. split; reflexivity.
Qed.

(* a pending access and a CAS's read alone do not share a place *)
Lemma placed_hplaced : forall c r k1 d k2 m xs j,
  placed p c (cs s c) (pcs s c) r k1 d j -> hplaced p c (cs s c) (pcs s c) r k2 m xs j -> False.
Proof.
  intros c r k1 d k2 m xs j (P1 & t1 & O1 & F1) (P2 & C2 & t2 & O2 & F2).
  destruct (Nat.lt_trichotomy t1 t2) as [L|[L|L]].
  - apply (first_atR_free _ _ _ _ _ _ _ _ _ F2). exists k1, t1, d. auto.
  - subst t2. destruct (i_oc p s I c k1 t1 O1) as (e1 & E1 & Ca & Ka).
    destruct (i_oh p s I c k2 t1 O2) as (e2 & E2 & _ & _ & Eh). rewrite E1 in E2. injection E2 as <-.
    rewrite (oc_eh p s c k1 t1 e1 I O1 E1 Ca Ka) in Eh. discriminate.
  - apply (first_at_hfree _ _ _ _ _ _ _ _ F1). exists k2, t2, m, xs. split; [exact P2|]. split; [exact O2|].
    split; [exact L|]. split; [intros t3 E; congruence|exact F2].
Qed.

(* a pending CAS that happened with a success read its expected value *)
Lemma cas_ok_s : forall c k t d r', oc (cs s c) k = Some t -> ai (cs s c) k = inst_of d -> is_cas (inst_of d) = true ->
  vok (rg (cs s c) k) = true -> vv (rg (cs s c) k) = cexp (inst_of d) r'.
Proof.
  intros c k t d r' O A Ca V.
  destruct (i_oc p s I c k t O) as (e & E & Xe & Ke).
  assert (Ei : einstr p s e = inst_of d) by (unfold einstr; rewrite Xe, Ke; exact A).
  pose proof (oc_eh p s c k t e I O E Xe Ke) as Eh.
  assert (Xl : xload (inst_of d) (rgof s e) = true) by (unfold xload; destruct d; simpl in Ca |- *; try discriminate; reflexivity).
  pose proof (j_ok p s J t e E Eh ltac:(rewrite Ei; exact Ca) ltac:(rewrite Ei; exact Xl)) as Jk. rewrite Xe, Ke, V in Jk.
  destruct (j_ew p s J t e _ E Ei) as [Wq _]. rewrite <- Jk in Wq. symmetry in Wq.
  apply andb_prop in Wq as [_ Wq]. rewrite Ca in Wq. simpl in Wq. rewrite andb_true_r in Wq. apply Nat.eqb_eq in Wq.
  destruct (j_val p s J t e _ E Ei) as [Vl _]. specialize (Vl Xl). rewrite Xe, Ke, (rval_cas _ _ Ca) in Vl.
  rewrite Vl, Wq. change (cexp (inst_of d) (rgof s e) = cexp (inst_of d) r'). apply cexp_ieval. apply ieval_inst.
Qed.

Lemma rval_ncas : forall i a, is_cas i = false -> rval i a = a.
Proof. intros i a H. destruct i; simpl in H; try discriminate; reflexivity. Qed.

Lemma rval_slot : forall i b v, rval i (if is_cas i then vd b v else v) = v.
Proof.
  intros i b v. destruct (is_cas i) eqn:C; [rewrite (rval_cas _ _ C); apply vv_vd|apply rval_ncas; exact C].
Qed.

(* two registers with the same verdict and the same value are equal *)
Lemma vd_eq : forall a b, vok a = vok b -> vv a = vv b -> a = b.
Proof. intros a b E1 E2. rewrite <- (vd_split a), <- (vd_split b), E1, E2. reflexivity. Qed.

(* S3c: a fixed result keeps the value *)
Lemma rval_cfx : forall cc j i r a, rval i (cfx cc j i r a) = rval i a.
Proof.
  intros cc j i r a. rewrite !cfx_unfold. destruct (fx cc j); [|reflexivity]. destruct (is_cas i) eqn:C; [|reflexivity].
  rewrite !(rval_cas _ _ C). apply vv_vd.
Qed.
Lemma cfx_cmp : forall cc j i r a, (vok a = true -> Nat.eqb (vv a) (cexp i r) = true) ->
  vok (cfx cc j i r a) = true -> Nat.eqb (vv (cfx cc j i r a)) (cexp i r) = true.
Proof.
  intros cc j i r a H V. rewrite !cfx_unfold in *. destruct (fx cc j); [|auto]. destruct (is_cas i); [|auto].
  rewrite vok_vd in V. rewrite vv_vd. apply andb_prop in V as [_ V]. exact V.
Qed.

Theorem cont_equiv : forall c B r V,
  ccont p c (cs s c) (pcs s c) (bor (bd (cs s c)) B) r V <->
  exists f, (forall j, r j = creg p c (cs s c) (pcs s c) (tp s c) (bor (bd (cs s c)) B) f j) /\
    (forall j x, j < pcs s c \/ (rdat p c r j = true /\ In x (icells (ins p c j r))) ->
       V j x = cellv p c (cs s c) (pcs s c) (tp s c) (bor (bd (cs s c)) B) f r j j x).
Proof.
  intros c B r V. set (cc := cs s c). set (pc := pcs s c). set (N := tp s c). set (Bo := bor (bd cc) B).
  assert (PO : pend_ok cc pc) by (apply (pend_ok_of p s c I)).
  split.
  - intros (C1 & C2 & C3 & C3v & C4 & C4h & C5).
    set (f := fun j x => if Nat.eqb x (bitc (ins p c j r)) then Nat.b2n (vok (r j)) else V j x).
    assert (FV : forall j x, x <> bitc (ins p c j r) -> f j x = V j x).
    { intros j x Hx. unfold f. rewrite (proj2 (Nat.eqb_neq _ _) Hx). reflexivity. }
    assert (FB : forall j, fbit f (ins p c j r) j = vok (r j)).
    { intros j. unfold fbit, f. rewrite Nat.eqb_refl. apply odd_b2n. }
    assert (CV : forall n b x, b <= n -> b < pc \/ (rdat p c r b = true /\ In x (icells (ins p c b r))) ->
                 cellv p c cc pc N Bo f r n b x = V b x).
    { intros n. induction n as [|n IH]; intros b x Lb Rb.
      all: destruct (Nat.ltb_spec b pc) as [L|L]; [rewrite cellv_lt by auto; symmetry; apply (proj2 (C1 b L))|].
      all: destruct Rb as [Rb|(Rb & Ixb)]; [lia|]; unfold rdat in Rb.
      all: destruct (pend_at p c cc pc N r b) as [k|] eqn:Pa.
      all: try (rewrite (cellv_pd _ _ _ _ _ _ _ _ _ _ _ k) by auto;
                apply (pend_at_char_s p s c I) in Pa; destruct Pa as (d' & Pl);
                destruct (C4 k d' (proj1 Pl)) as (j' & Pl' & Vk);
                destruct Pl as (Pk & t & O & Fj); destruct Pl' as (_ & t' & O' & Fj');
                assert (Et : t' = t) by (unfold cc in *; congruence); subst t';
                rewrite <- (first_at_unique _ _ _ _ _ _ _ _ _ Wc Fj Fj') in Vk;
                symmetry; apply Vk; [rewrite <- (eof_load _ _ _ (first_at_eof _ _ _ _ _ _ _ _ Fj)); exact Rb|];
                rewrite <- (eof_icells _ _ _ (first_at_eof _ _ _ _ _ _ _ _ Fj)); exact Ixb).
      all: destruct (hpend_at p c cc pc N r b) as [k|] eqn:Ph.
      all: try (rewrite (cellv_hpd _ _ _ _ _ _ _ _ _ _ _ k) by auto;
                apply (hpend_at_char_s p s c I) in Ph; destruct Ph as (m0 & xs0 & Pl);
                destruct (C4h k m0 xs0 (proj1 Pl) (proj1 (proj2 Pl))) as (j' & Pl' & Vk);
                rewrite <- (hplaced_same c r k _ _ _ _ _ _ Pl Pl') in Vk; symmetry; apply Vk; exact Ixb).
      - rewrite cellv_free by auto. apply FV. apply bitc_notin. exact Ixb.
      - rewrite cellv_go by auto. destruct (Bo b) eqn:Bb; [|apply FV; apply bitc_notin; exact Ixb].
        destruct (fbinder p c r b x) as [b0|] eqn:Fb; [|apply FV; apply bitc_notin; exact Ixb].
        assert (Np : ~ pslot p c cc pc r b).
        { intros [(k0 & d0 & Pl)|(k0 & m0 & xs0 & Pl)].
          - assert (pend_at p c cc pc N r b = Some k0) by (apply (pend_at_char_s p s c I); eauto). congruence.
          - assert (hpend_at p c cc pc N r b = Some k0) by (apply (hpend_at_char_s p s c I); eauto). congruence. }
        rewrite (C5 b x b0 L Bb Np Fb). pose proof (fbinder_lt _ _ _ _ _ _ Fb) as L0.
        destruct (binder_read c r b x b0 Fb) as [(R0 & Ix0)|(m & ys & cb & v & E0)].
        + f_equal. apply IH; [lia|right; split; [exact R0|exact Ix0]].
        + apply (bvx_store c r b0 x _ _ m ys cb v E0). }
    exists f. split.
    + intros j. symmetry. revert j. apply (creg_ext p W c cc pc N Bo f r PO). intros j. unfold slotv.
      destruct (Nat.ltb_spec j pc) as [L|L]; [symmetry; apply (C1 j L)|].
      destruct (is_load (ins p c j r) && icond (ins p c j r) r) eqn:X; [|symmetry; apply C2; auto].
      destruct (pend_at p c cc pc N r j) as [k|] eqn:Pa.
      * apply (pend_at_char_s p s c I) in Pa. destruct Pa as (d' & Pl).
        destruct (C4 k d' (proj1 Pl)) as (j' & Pl' & Vk).
        pose proof Pl as (Pk & t & O & Fj). destruct Pl' as (_ & t' & O' & Fj'). assert (Et : t' = t) by (unfold cc in *; congruence). subst t'.
        rewrite <- (first_at_unique _ _ _ _ _ _ _ _ _ Wc Fj Fj') in Vk.
        pose proof (first_at_eof _ _ _ _ _ _ _ _ Fj) as D.
        assert (Ld : is_load (inst_of d') = true) by (rewrite <- (eof_load _ _ _ D); exact X).
        pose proof (rg_rv p s c k t I J O) as Rv. fold cc in Rv. destruct Pk as (_ & _ & Ak). fold cc in Ak. rewrite Ak in Rv.
        pose proof (C3 j L X) as Q. rewrite (eof_icells _ _ _ D) in Q.
        assert (Q' : rval (ins p c j r) (r j) = rval (inst_of d') (rg cc k)).
        { rewrite Q, Rv. f_equal. apply map_ext_in. intros x Ix. apply (Vk Ld x Ix). }
        destruct (eof_cexp _ _ _ r D) as (Csd & _).
        destruct (is_cas (ins p c j r)) eqn:Ci.
        -- rewrite (rval_cas _ _ Ci), (rval_cas _ _ Csd) in Q'.
           destruct (C3v j L X Ci) as (V1 & _ & _). symmetry. apply vd_eq; [apply (V1 k d' Pl)|exact Q'].
        -- rewrite (rval_ncas _ _ Ci), (rval_ncas _ _ Csd) in Q'. symmetry. exact Q'.
      * assert (NPl : forall k d, ~ placed p c cc pc r k d j).
        { intros k0 d0 Pl0. assert (pend_at p c cc pc N r j = Some k0) by (apply (pend_at_char_s p s c I); eauto). congruence. }
        assert (FXS : forall a, (forall bx, fx cc j = Some bx -> is_cas (ins p c j r) = true -> vv a = vv (r j)) ->
                      (fx cc j = None \/ is_cas (ins p c j r) = false -> a = r j) -> cfx cc j (ins p c j r) r a = r j).
        { intros a0 H1 H2. rewrite !cfx_unfold. destruct (fx cc j) as [bx|] eqn:Fxj; [|apply H2; left; reflexivity].
          destruct (is_cas (ins p c j r)) eqn:Ci; [|apply H2; right; reflexivity].
          rewrite (H1 bx eq_refl eq_refl). symmetry. apply vd_eq; [rewrite vok_vd|rewrite vv_vd; reflexivity].
          destruct (C3v j L X Ci) as (_ & _ & _ & V4). apply (V4 bx Fxj NPl). }
        apply FXS.
        { intros bx Fxj Ci0. destruct (hpend_at p c cc pc N r j) as [k|] eqn:Ph.
          - apply (hpend_at_char_s p s c I) in Ph. destruct Ph as (m0 & xs0 & Pl).
            destruct (C4h k m0 xs0 (proj1 Pl) (proj1 (proj2 Pl))) as (j' & Pl' & Vk).
            rewrite <- (hplaced_same c r k _ _ _ _ _ _ Pl Pl') in Vk.
            pose proof Pl as (Pk & C & t & O & Fj).
            pose proof (rg_rv_h c k t C O) as Rh. fold cc in Rh.
            destruct (hplaced_icells c r k m0 xs0 j Pl) as [Ic _]. fold cc in Ic.
            pose proof (C3 j L X) as Q. rewrite (rval_cas _ _ Ci0) in Q.
            assert (Vv : vv (r j) = vv (rg cc k)) by (rewrite Q, Rh, <- Ic; f_equal; apply map_ext_in; intros x Ix; apply (Vk x Ix)).
            rewrite Vv. destruct (vok (rg cc k)); [apply vv_vd|reflexivity].
          - cbv zeta. rewrite Ci0, vv_vd, <- (rval_cas _ _ Ci0), (C3 j L X). f_equal. apply map_ext_in. intros x Ix.
            apply CV; [lia|right; split; [exact X|exact Ix]]. }
        intros Hn. destruct (hpend_at p c cc pc N r j) as [k|] eqn:Ph.
        -- apply (hpend_at_char_s p s c I) in Ph. destruct Ph as (m0 & xs0 & Pl).
           destruct (C4h k m0 xs0 (proj1 Pl) (proj1 (proj2 Pl))) as (j' & Pl' & Vk).
           rewrite <- (hplaced_same c r k _ _ _ _ _ _ Pl Pl') in Vk.
           pose proof Pl as (Pk & C & t & O & Fj).
           pose proof (rg_rv_h c k t C O) as Rh. fold cc in Rh.
           destruct (hplaced_icells c r k m0 xs0 j Pl) as [Ic _]. fold cc in Ic.
           assert (Ci : is_cas (ins p c j r) = true) by (apply (eofR_cas _ r _ (first_atR_eofR _ _ _ _ _ _ _ _ _ Fj))).
           assert (Fn : fx cc j = None) by (destruct Hn as [Hn|Hn]; [exact Hn|congruence]).
           pose proof (C3 j L X) as Q. rewrite (rval_cas _ _ Ci) in Q.
           assert (Vv : vv (r j) = vv (rg cc k)) by (rewrite Q, Rh, <- Ic; f_equal; apply map_ext_in; intros x Ix; apply (Vk x Ix)).
           destruct (C3v j L X Ci) as (_ & V2 & V3 & _).
           destruct (vok (rg cc k)) eqn:Vg.
           ++ rewrite FB. destruct (vok (r j)) eqn:Vr.
              ** pose proof (V3 eq_refl) as Eb. apply Nat.eqb_eq in Eb.
                 rewrite (cfailv_ok (ins p c j r) r r (rg cc k) Ci eq_refl Vg) by (rewrite <- Vv, Eb; destruct (ins p c j r); reflexivity).
                 simpl. symmetry. apply vd_eq; [rewrite vok_vd; exact Vr|rewrite vv_vd; exact Vv].
              ** rewrite andb_false_r. symmetry. apply vd_eq; [rewrite vok_vd; exact Vr|rewrite vv_vd; exact Vv].
           ++ symmetry. apply vd_eq; [rewrite Vg; apply (V2 k m0 xs0 Pl C Vg Fn)|exact Vv].
        -- cbv zeta.
           assert (Ev : enc (map (cellv p c cc pc N Bo f r j j) (icells (ins p c j r))) = rval (ins p c j r) (r j)).
           { rewrite (C3 j L X). f_equal. apply map_ext_in. intros x Ix. apply CV; [lia|right; split; [exact X|exact Ix]]. }
           rewrite Ev. destruct (is_cas (ins p c j r)) eqn:Ci.
           ++ rewrite FB. rewrite (rval_cas _ _ Ci). destruct (vok (r j)) eqn:Vr.
              ** destruct (C3v j L X Ci) as (_ & _ & V3 & _). rewrite (V3 Vr). simpl. rewrite <- Vr. apply vd_split.
              ** rewrite andb_false_r. rewrite <- Vr. apply vd_split.
           ++ apply rval_ncas. exact Ci.
    + intros j x Hj. symmetry. apply CV; [lia|]. exact Hj.
  - intros (f & E & EV). set (g := creg p c cc pc N Bo f) in *.
    assert (AG : forall j, agree r g j) by (intros j i _; apply E).
    assert (Gfix : forall j, g j = slotv p c cc pc N Bo f g j) by (intros j; apply creg_fix; auto).
    assert (CE : forall n j x, cellv p c cc pc N Bo f r n j x = cellv p c cc pc N Bo f g n j x)
      by (intros n j x; apply cellv_agree; auto).
    assert (RE : forall j, rdat p c r j = rdat p c g j).
    { intros j. unfold rdat. rewrite <- (proj1 (ins_agree p W c j r g (AG j))).
      unfold icond. rewrite (proj2 (ins_agree p W c j r g (AG j))). reflexivity. }
    assert (IE : forall j, ins p c j r = ins p c j g) by (intros j; apply (proj1 (ins_agree p W c j r g (AG j)))).
    assert (EE : forall j, ieval (ins p c j r) r = ieval (ins p c j r) g) by (intros j; apply (proj2 (ins_agree p W c j r g (AG j)))).
    (* the register at j: the slot value under g *)
    assert (SV : forall j, pc <= j -> rdat p c r j = true -> r j =
              match pend_at p c cc pc N g j with
              | Some k => rg cc k
              | None => cfx cc j (ins p c j g) g (match hpend_at p c cc pc N g j with
                        | Some k => if vok (rg cc k) then vd (negb (cfailv (ins p c j g) g (rg cc k)) && fbit f (ins p c j g) j) (vv (rg cc k)) else rg cc k
                        | None => let v := enc (map (cellv p c cc pc N Bo f g j j) (icells (ins p c j g))) in
                                  if is_cas (ins p c j g) then vd (Nat.eqb v (cexp (ins p c j g) g) && fbit f (ins p c j g) j) v else v
                        end) end).
    { intros j L X. rewrite E, Gfix. unfold slotv. rewrite (proj2 (Nat.ltb_ge j pc) L).
      rewrite RE in X. unfold rdat in X. rewrite X. reflexivity. }
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    + intros j L. split; [rewrite E; apply creg_lt_pc; auto|]. intros x. rewrite (EV j x (or_introl L)).
      apply cellv_lt. auto.
    + intros j L X. rewrite E, Gfix. unfold slotv. rewrite (proj2 (Nat.ltb_ge j pc) L).
      rewrite RE in X. unfold rdat in X. rewrite X. reflexivity.
    + intros j L X. rewrite (SV j L X). rewrite IE.
      destruct (pend_at p c cc pc N g j) as [k|] eqn:Pa.
      * pose proof Pa as Pa'. apply (pend_at_char_s p s c I) in Pa'. destruct Pa' as (d' & (Pk & t & O & Fj)).
        pose proof (first_at_eof _ _ _ _ _ _ _ _ Fj) as D.
        pose proof (rg_rv p s c k t I J O) as Rv. fold cc in Rv. destruct Pk as (_ & _ & Ak). fold cc in Ak. rewrite Ak in Rv.
        destruct (eof_cexp _ _ _ g D) as (Csd & _).
        rewrite (rval_iscas (ins p c j g) (inst_of d') _ (eq_sym Csd)), Rv, (eof_icells _ _ _ D).
        f_equal. apply map_ext_in. intros x Ix. rewrite <- (eof_icells _ _ _ D) in Ix. rewrite <- IE in Ix.
        rewrite (EV j x (or_intror (conj X Ix))), CE.
        symmetry. apply (cellv_pd _ _ _ _ _ _ _ _ _ _ _ k); auto. change (rdat p c g j = true). rewrite <- RE. exact X.
      * rewrite rval_cfx. destruct (hpend_at p c cc pc N g j) as [k|] eqn:Ph.
        -- pose proof Ph as Ph'. apply (hpend_at_char_s p s c I) in Ph'. destruct Ph' as (m0 & xs0 & Pl).
           pose proof Pl as (Pk & C & t & O & Fj). pose proof (rg_rv_h c k t C O) as Rh. fold cc in Rh.
           destruct (hplaced_icells c g k m0 xs0 j Pl) as [Ic _]. fold cc in Ic.
           assert (Ci : is_cas (ins p c j g) = true) by (apply (eofR_cas _ g _ (first_atR_eofR _ _ _ _ _ _ _ _ _ Fj))).
           rewrite (rval_cas _ _ Ci).
           assert (Hv : vv (if vok (rg cc k) then vd (negb (cfailv (ins p c j g) g (rg cc k)) && fbit f (ins p c j g) j) (vv (rg cc k))
                            else rg cc k) = vv (rg cc k)) by (destruct (vok (rg cc k)); [apply vv_vd|reflexivity]).
           rewrite Hv, Rh, <- Ic. f_equal. apply map_ext_in. intros x Ix. rewrite <- IE in Ix.
           rewrite (EV j x (or_intror (conj X Ix))), CE.
           symmetry. apply (cellv_hpd _ _ _ _ _ _ _ _ _ _ _ k); auto. change (rdat p c g j = true). rewrite <- RE. exact X.
        -- cbv zeta. rewrite rval_slot. f_equal. apply map_ext_in. intros x Ix. rewrite <- IE in Ix.
           rewrite (EV j x (or_intror (conj X Ix))), CE. reflexivity.
    + intros j L X Ci. rewrite IE in Ci.
      assert (Xg : rdat p c g j = true) by (rewrite <- RE; exact X).
      split; [|split; [|split]].
      * intros k d Pl. assert (Pg : placed p c cc pc g k d j) by (apply (placed_ext c r g k d j); [intros i; apply E|exact Pl]).
        assert (Pa : pend_at p c cc pc N g j = Some k) by (apply (pend_at_char_s p s c I); eauto).
        rewrite (SV j L X), Pa. reflexivity.
      * intros k m xs Pl C Vg Fn.
        assert (Pg : hplaced p c cc pc g k m xs j).
        { destruct Pl as (P1 & P2 & t & O & F). split; auto. split; auto. exists t. split; auto.
          apply (first_atR_ext p c _ _ r g t m xs j W); [intros i; apply E|exact F]. }
        assert (Pa : pend_at p c cc pc N g j = None).
        { destruct (pend_at p c cc pc N g j) as [k'|] eqn:Pa; auto. exfalso.
          apply (pend_at_char_s p s c I) in Pa. destruct Pa as (d' & Pd). apply (placed_hplaced c g k' d' k m xs j Pd Pg). }
        assert (Ph : hpend_at p c cc pc N g j = Some k) by (apply (hpend_at_char_s p s c I); eauto).
        rewrite (SV j L X), Pa, Ph, Vg, (cfx_none _ _ _ _ _ Fn). exact Vg.
      * intros Vr. rewrite IE. rewrite (cexp_ieval _ r g) by (rewrite <- IE; apply EE).
        rewrite (SV j L X) in Vr |- *.
        destruct (pend_at p c cc pc N g j) as [k|] eqn:Pa.
        -- pose proof Pa as Pa'. apply (pend_at_char_s p s c I) in Pa'. destruct Pa' as (d' & (Pk & t & O & Fj)).
           pose proof (first_at_eof _ _ _ _ _ _ _ _ Fj) as D. destruct (eof_cexp _ _ _ g D) as (Csd & Ced).
           destruct Pk as (_ & _ & Ak). fold cc in Ak.
           pose proof (cas_ok_s c k t d' g O Ak ltac:(rewrite Csd; exact Ci) Vr) as Q0. fold cc in Q0. rewrite Q0, Ced. apply Nat.eqb_refl.
        -- apply cfx_cmp; [|exact Vr]. clear Vr. intros Vr.
           destruct (hpend_at p c cc pc N g j) as [k|] eqn:Ph.
           ++ destruct (vok (rg cc k)) eqn:Vg; [|congruence].
              rewrite vok_vd in Vr. apply andb_prop in Vr as [Nf _]. apply negb_true_iff in Nf.
              rewrite vv_vd. apply Nat.eqb_eq.
              assert (Xg' := Xg). unfold rdat in Xg'.
              destruct (ins p c j g) as [| |m0 x0 c0 e0 n0| |]; simpl in Ci; try discriminate.
              unfold cfailv in Nf. unfold icond, ieval in Xg'. simpl in Xg'. rewrite Xg', Vg in Nf. simpl in Nf.
              apply negb_false_iff in Nf. apply Nat.eqb_eq in Nf. exact Nf.
           ++ cbv zeta in Vr |- *. destruct (is_cas (ins p c j g)); [|discriminate].
              rewrite vok_vd in Vr. apply andb_prop in Vr as [Eq _]. rewrite vv_vd. exact Eq.
      * intros bx Fx NP. rewrite IE. rewrite (cexp_ieval _ r g) by (rewrite <- IE; apply EE).
        assert (Pa : pend_at p c cc pc N g j = None).
        { destruct (pend_at p c cc pc N g j) as [k|] eqn:Pa; auto. exfalso.
          apply (pend_at_char_s p s c I) in Pa. destruct Pa as (d' & Pl).
          apply (NP k d'). apply (placed_ext c g r k d' j); [intros i; symmetry; apply E|exact Pl]. }
        rewrite (SV j L X), Pa. rewrite !cfx_unfold. rewrite Fx, Ci, vok_vd, vv_vd. reflexivity.
    + intros k d Pk. destruct (INVP_run p s W Wc R c k d B f Pk) as (j & Pl). fold cc pc N Bo g in Pl.
      exists j. split; [apply (placed_ext c g r k d j); [intros i; symmetry; apply E|exact Pl]|].
      intros Ld x Ix. pose proof Pl as (Pk' & t & O & Fj).
      assert (Lj : pc <= j) by apply (first_at_le _ _ _ _ _ _ _ _ Fj).
      assert (Xg : rdat p c g j = true) by (unfold rdat; rewrite (eof_load _ _ _ (first_at_eof _ _ _ _ _ _ _ _ Fj)); exact Ld).
      assert (Xr : rdat p c r j = true) by (rewrite RE; exact Xg).
      assert (Ixr : In x (icells (ins p c j r))) by (rewrite IE, (eof_icells _ _ _ (first_at_eof _ _ _ _ _ _ _ _ Fj)); exact Ix).
      rewrite (EV j x (or_intror (conj Xr Ixr))), CE.
      apply (cellv_pd _ _ _ _ _ _ _ _ _ _ _ k); auto.
      apply (pend_at_char_s p s c I). exists d. exact Pl.
    + intros k m xs Pk C. destruct (INVH_run p s W Wc R c k m xs B f Pk C) as (j & Pl). fold cc pc N Bo g in Pl.
      assert (Pl' : hplaced p c cc pc r k m xs j).
      { destruct Pl as (P1 & P2 & t & O & F). split; auto. split; auto. exists t. split; auto.
        apply (first_atR_ext p c _ _ g r t m xs j W); [intros i; symmetry; apply E|exact F]. }
      exists j. split; [exact Pl'|]. intros x Ix.
      destruct (hplaced_icells c g k m xs j Pl) as [_ Xg].
      assert (Xr : rdat p c r j = true) by (rewrite RE; exact Xg).
      rewrite (EV j x (or_intror (conj Xr Ix))), CE.
      assert (Lj : pc <= j) by (destruct Pl as (_ & _ & t & _ & F); apply (first_atR_le _ _ _ _ _ _ _ _ _ F)).
      assert (Pa : pend_at p c cc pc N g j = None).
      { destruct (pend_at p c cc pc N g j) as [k'|] eqn:Pa; auto. exfalso.
        apply (pend_at_char_s p s c I) in Pa. destruct Pa as (d' & Pd). apply (placed_hplaced c g k' d' k m xs j Pd Pl). }
      apply (cellv_hpd _ _ _ _ _ _ _ _ _ _ _ k); auto.
      apply (hpend_at_char_s p s c I). eauto.
    + intros j x b L Bj Np Fb.
      destruct (fbinder_shape _ _ _ _ _ _ Fb) as (_ & _ & _ & Br & Cr & Ixj).
      assert (Xr : rdat p c r j = true).
      { unfold rdat. rewrite Cr. destruct (ins p c j r) as [[] | | [] | |]; simpl in Br; try discriminate; reflexivity. }
      rewrite (EV j x (or_intror (conj Xr Ixj))), CE.
      assert (Pa : pend_at p c cc pc N g j = None).
      { destruct (pend_at p c cc pc N g j) as [k|] eqn:Pa; auto. exfalso. apply Np. left.
        apply (pend_at_char_s p s c I) in Pa. destruct Pa as (d' & Pl).
        exists k, d'. apply (placed_ext c g r k d' j); [intros i; symmetry; apply E|exact Pl]. }
      assert (Ph : hpend_at p c cc pc N g j = None).
      { destruct (hpend_at p c cc pc N g j) as [k|] eqn:Ph; auto. exfalso. apply Np. right.
        apply (hpend_at_char_s p s c I) in Ph. destruct Ph as (m0 & xs0 & Pk & C & t & O & F).
        exists k, m0, xs0. split; auto. split; auto. exists t. split; auto.
        apply (first_atR_ext p c _ _ g r t m0 xs0 j W); [intros i; symmetry; apply E|exact F]. }
      pose proof (fbinder_lt _ _ _ _ _ _ Fb) as Lb.
      destruct j as [|j]; [lia|].
      rewrite (cellv_go _ _ _ _ _ _ _ _ j) by (auto; pose proof (RE (S j)) as Q; unfold rdat in Q; rewrite <- Q; exact Xr).
      rewrite Bj, <- (fbinder_agree p W c r g (S j) x (AG (S j))), Fb.
      rewrite (bvx_agree p W c g r b (S j) x _ Lb) by (intros i _; symmetry; apply E).
      destruct (binder_read c r (S j) x b Fb) as [(R0 & Ix0)|(m & ys & cb & v & E0)].
      * f_equal. rewrite (EV b x (or_intror (conj R0 Ix0))), CE. apply cellv_fuel. lia.
      * apply (bvx_store c r b x _ _ m ys cb v E0).
Qed.

Lemma hplaced_ext : forall c r r' k m xs j, (forall i, r i = r' i) ->
  hplaced p c (cs s c) (pcs s c) r k m xs j -> hplaced p c (cs s c) (pcs s c) r' k m xs j.
Proof.
  intros c r r' k m xs j E (P1 & P2 & t & O & F). split; auto. split; auto. exists t. split; auto.
  apply (first_atR_ext p c _ _ r r' t m xs j W); [exact E|exact F].
Qed.

Lemma pend_at_ext : forall c r r' j, (forall i, r i = r' i) ->
  pend_at p c (cs s c) (pcs s c) (tp s c) r j = pend_at p c (cs s c) (pcs s c) (tp s c) r' j.
Proof.
  intros c r r' j E.
  destruct (pend_at p c (cs s c) (pcs s c) (tp s c) r j) as [k|] eqn:P1;
  destruct (pend_at p c (cs s c) (pcs s c) (tp s c) r' j) as [k'|] eqn:P2; auto.
  - apply (pend_at_char_s p s c I) in P1 as (d1 & Q1). apply (placed_ext c r r' k d1 j E) in Q1.
    assert (pend_at p c (cs s c) (pcs s c) (tp s c) r' j = Some k) by (apply (pend_at_char_s p s c I); eauto). congruence.
  - apply (pend_at_char_s p s c I) in P1 as (d1 & Q1). apply (placed_ext c r r' k d1 j E) in Q1.
    assert (pend_at p c (cs s c) (pcs s c) (tp s c) r' j = Some k) by (apply (pend_at_char_s p s c I); eauto). congruence.
  - apply (pend_at_char_s p s c I) in P2 as (d2 & Q2). apply (placed_ext c r' r k' d2 j (fun i => eq_sym (E i))) in Q2.
    assert (pend_at p c (cs s c) (pcs s c) (tp s c) r j = Some k') by (apply (pend_at_char_s p s c I); eauto). congruence.
Qed.

Lemma hpend_at_ext : forall c r r' j, (forall i, r i = r' i) ->
  hpend_at p c (cs s c) (pcs s c) (tp s c) r j = hpend_at p c (cs s c) (pcs s c) (tp s c) r' j.
Proof.
  intros c r r' j E.
  destruct (hpend_at p c (cs s c) (pcs s c) (tp s c) r j) as [k|] eqn:P1;
  destruct (hpend_at p c (cs s c) (pcs s c) (tp s c) r' j) as [k'|] eqn:P2; auto.
  - apply (hpend_at_char_s p s c I) in P1 as (m1 & x1 & Q1). apply (hplaced_ext c r r' k m1 x1 j E) in Q1.
    assert (hpend_at p c (cs s c) (pcs s c) (tp s c) r' j = Some k) by (apply (hpend_at_char_s p s c I); eauto). congruence.
  - apply (hpend_at_char_s p s c I) in P1 as (m1 & x1 & Q1). apply (hplaced_ext c r r' k m1 x1 j E) in Q1.
    assert (hpend_at p c (cs s c) (pcs s c) (tp s c) r' j = Some k) by (apply (hpend_at_char_s p s c I); eauto). congruence.
  - apply (hpend_at_char_s p s c I) in P2 as (m2 & x2 & Q2). apply (hplaced_ext c r' r k' m2 x2 j (fun i => eq_sym (E i))) in Q2.
    assert (hpend_at p c (cs s c) (pcs s c) (tp s c) r j = Some k') by (apply (hpend_at_char_s p s c I); eauto). congruence.
Qed.

Lemma lead_ext : forall c r r' b, (forall i, r i = r' i) ->
  lead p c (cs s c) (pcs s c) (tp s c) r b = lead p c (cs s c) (pcs s c) (tp s c) r' b.
Proof. intros c r r' b E. unfold lead. rewrite (pend_at_ext c r r' b E), (hpend_at_ext c r r' b E). reflexivity. Qed.

(* hence the two forms of R1 for an early access agree *)
Definition early_ok_c (p : prog) (c : nat) (cc : cst) (pc N T : nat) (d : desc) (u : cell -> option nat) (B : nat -> bool) : Prop :=
  forall r V, ccont p c cc pc (bor (bd cc) B) r V ->
    exists j, pc < j /\ first_at p c cc pc r T d j /\
      (is_load (inst_of d) = true -> forall x b, In x (icells (inst_of d)) -> bor (bd cc) B j = true ->
         fbinder p c r j x = Some b -> exists k, lead p c cc pc N r b = Some k /\ u x = rw cc k x).

Theorem early_ok_equiv : forall c T d u B,
  early_ok p c (cs s c) (pcs s c) (tp s c) T d u B <-> early_ok_c p c (cs s c) (pcs s c) (tp s c) T d u B.
Proof.
  intros c T d u B. split.
  - intros H r V Cr. destruct (proj1 (cont_equiv c B r V) Cr) as (f & E & _).
    destruct (H f) as (j & Lj & Fj & Fx). cbv zeta in Fj, Fx. exists j. split; [exact Lj|]. split.
    + eapply first_at_ext; [exact W| |exact Fj]. intros i; symmetry; apply E.
    + intros Ld x b Ix Bj Fb. rewrite (lead_ext c r _ b E). apply (Fx Ld x b Ix Bj). rewrite <- Fb. apply fbinder_agree; auto. intros i _. symmetry. apply E.
  - intros H f. cbv zeta. set (g := creg p c (cs s c) (pcs s c) (tp s c) (bor (bd (cs s c)) B) f).
    destruct (H g (fun j x => cellv p c (cs s c) (pcs s c) (tp s c) (bor (bd (cs s c)) B) f g j j x)) as (j & Lj & Fj & Fx).
    { apply (proj2 (cont_equiv c B g _)). exists f. split; [intros j; reflexivity|]. intros j x _. reflexivity. }
    exists j. split; [exact Lj|]. split; auto.
Qed.

End Eq.
