(* The fields of M2Iface.M2Guarantees that hold
   step by step, for M2DQ (stepQ). The trace fields (g_birth,
   g_pending_cells, g_pending_source) are not proved here.
   The record-fix obligations factor in two shapes:
   - F1 (scfail): a record k of context c with pcs <= k, oc k = None,
     oh k <> None, vok (rg k) = true gets the register of a failure. This is
     M2Model's s_cfix with a failure after the read half; its scripts are
     reused (SI_cfail, Ext_cfail).
   - F2 (sbd / scfix0): bd grows and fx changes at one place; nothing else.
   q_rfix = F1 then F2 (sbd), q_sfix = F2 (scfix0 ... true). The step
   scripts of M2Snap.SI_step, M2Trace.Ext_step and M2Ev.evok_step are
   reused for q_old with run p s replaced by the invariants they took from
   it (Inv1, Inv2, SI). *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO M2Oota M2Cont M2Snap M2Trace M2Ev M2Timeline2
  M2Iface M2DA M2DP M2DQ M2DQInv M2DQOota.

Lemma SI_st : forall p s t, Inv1 p s -> step p s t -> SI p s -> SI p t.
Proof.
  intros p s t I H Sv. pose proof Sv as (S1 & S2 & S3).
  destruct (step_cases p s t H) as [(c & i & m' & a & K & u & w & H1 & H2 & H3 & H4 & Hbh & Hh & _ & _ & H6 & _ & ->)|[(c & k & d & B & m' & a & K & u & w & H1 & H2 & Hso & Hh & _ & _ & H5 & _ & ->)|[(c & d & H1 & H2 & H3 & H4 & H4m & Hfh & ->)|[(c & k & xs & B & m' & a & K & u & w & bv & H1 & H2 & Hh & Hso & H4 & H5 & _ & ->)|[(c & K1 & K2 & K3 & _ & K5 & K4 & _ & ->)|(cX & jX & bX & BX & oX & HjX & HfX & HcX & ->)]]]]].
  - (* in order *)
    unfold sord. set (k := pcs s c). split; [|split].
    + intros t0 L. unfold evs; simpl in *. apply S1. lia.
    + intros t0 e He N. unfold evs in N; simpl in N.
      rewrite (ent_s' p s c k i m' a K u w _ _ _ _ I) in He.
      destruct (Nat.ltb_spec t0 (tm s)).
      * destruct (S2 t0 e He N) as [Lk Q]. split.
        -- unfold evs; simpl. unfold upd. destruct (Nat.eqb_spec (ec e) c); [subst k; rewrite e0 in *|]; lia.
        -- intros j t1 Lj Oj. unfold evs in Oj; simpl in Oj. unfold upd in Oj.
           destruct (Nat.eqb_spec (ec e) c); [|exact (Q j t1 Lj Oj)]. simpl in Oj. rewrite <- e0 in Oj.
           destruct (Nat.eqb_spec j k); [subst k; rewrite e0 in Lk; lia|exact (Q j t1 Lj Oj)].
      * destruct (Nat.eqb_spec t0 (tm s)); [|discriminate]. injection He as <-. subst t0. cbn [ec ek] in *.
        split; [unfold evs; simpl; unfold upd; rewrite Nat.eqb_refl; lia|].
        intros j t1 Lj Oj. unfold evs in Oj; simpl in Oj. unfold upd in Oj. rewrite Nat.eqb_refl in Oj. simpl in Oj.
        destruct (Nat.eqb_spec j k); [lia|]. apply (oc_lt_tm p s c j t1 I Oj).
    + intros t0 cc0 pc0 N0 B0 He Hn. unfold evs in He; simpl in He.
      assert (HPC : forall c', pcs s c' <= upd (pcs s) c (S k) c') by (intros c'; unfold upd; destruct (Nat.eqb_spec c' c); [subst; unfold k; lia|lia]).
      apply (snap_old p s c k i m' a K u w _ _ _ _ I Sv H2 (le_n _) HPC t0 cc0 pc0 N0 B0 He Hn).
  - (* early *)
    unfold searly, set_es, searly0. split; [|split].
    + intros t0 L. simpl in *. unfold upd. destruct (Nat.eqb_spec t0 (tm s)); [lia|]. apply S1. lia.
    + intros t0 e He N. simpl in N. unfold upd in N. destruct (Nat.eqb_spec t0 (tm s)); [discriminate|].
      change (ent (evs s c k (inst_of d) m' a K u w (bor (bd (cs s c)) B) (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s)) t0 = Some e) in He.
      rewrite (ent_s' p s c k _ m' a K u w _ _ _ _ I) in He.
      destruct (Nat.ltb_spec t0 (tm s)); [|destruct (Nat.eqb_spec t0 (tm s)); [lia|discriminate]].
      destruct (S2 t0 e He N) as [Lk Q]. split; [exact Lk|].
      intros j t1 Lj Oj.
      change (oc (cs (evs s c k (inst_of d) m' a K u w (bor (bd (cs s c)) B) (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s)) (ec e)) j = Some t1) in Oj.
      rewrite oc_s' in Oj. destruct (Nat.eqb_spec (ec e) c); [destruct (Nat.eqb_spec j k)|]; [|apply (Q j t1 Lj); rewrite e0; exact Oj|exact (Q j t1 Lj Oj)].
      exfalso. rewrite e0 in Lk. lia.
    + intros t0 cc0 pc0 N0 B0 He Hn. simpl in He. unfold upd in He. destruct (Nat.eqb_spec t0 (tm s)).
      * subst t0. injection He as <- <- <- <-.
        set (t1 := evs s c k (inst_of d) m' a K u w (bor (bd (cs s c)) B) (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s)).
        exists (newev s c k (inst_of d) K u w), d. cbn [ec ek erf].
        change (ent t1 (tm s) = Some (newev s c k (inst_of d) K u w) /\ eokx p c (cs s c) (pcs s c) (tp s c) (tm s) d u B /\
          pcs s c < k /\ eof (ai (cs t1 c) k) (rg (cs t1 c)) = Some d /\
          (forall j t0, oc (cs s c) j = Some t0 -> oc (cs t1 c) j = Some t0 /\ rg (cs s c) j = rg (cs t1 c) j /\ t0 < tm s) /\
          (forall j t0, oc (cs t1 c) j = Some t0 -> t0 < tm s -> oc (cs s c) j = Some t0) /\
          (forall j d', oc (cs s c) j <> None -> pcs s c <= j -> ai (cs s c) j = inst_of d' ->
             eof (ai (cs t1 c) j) (rg (cs t1 c)) = Some d') /\
          (pcs s c <= pcs s c /\ forall j, j < pcs s c -> oc (cs s c) j = None -> oc (cs t1 c) j = None) /\
          (forall j, oc (cs s c) j <> None -> pcs s c <= j -> exists d', ai (cs s c) j = inst_of d' /\ d' <> DFn FFull) /\
          (forall j t0, oh (cs s c) j = Some t0 -> oh (cs t1 c) j = Some t0 /\ t0 < tm s)).
        split; [unfold t1; rewrite (ent_s' p s c k _ m' a K u w _ _ _ _ I), Nat.ltb_irrefl, Nat.eqb_refl; reflexivity|].
        assert (EK : eokx p c (cs s c) (pcs s c) (tp s c) (tm s) d u B).
        { destruct Hh as [(_ & Ok)|(t2 & xs & ev & nv & _ & _ & _ & _ & Ok)]; [left; exact Ok|right; eauto]. }
        assert (NF : d <> DFn FFull).
        { destruct Hh as [(_ & Ok)|(t2 & xs & ev & nv & _ & -> & _ & _ & _)]; [apply (early_nofull _ _ _ _ _ _ _ _ _ Ok)|discriminate]. }
        split; [exact EK|]. split; auto. split; [|split; [|split; [|split]]].
        -- unfold t1. rewrite ai_s', !Nat.eqb_refl. apply eof_inst. exact NF.
        -- intros j t0 X. unfold t1. split; [apply oc_old_s'; auto|]. split; [symmetry; apply rg_old_s'; auto; congruence|].
           apply (oc_lt_tm p s c j t0 I X).
        -- intros j t0 X Y. unfold t1 in X. rewrite oc_s', Nat.eqb_refl in X. destruct (Nat.eqb_spec j k); [injection X; lia|auto].
        -- intros j d' X Y Z. unfold t1. rewrite ai_s', Nat.eqb_refl. destruct (Nat.eqb_spec j k); [subst; congruence|].
           rewrite Z. apply eof_inst. destruct (proj1 (i_pend p s I c j Y X)) as (d0 & A0 & N0').
           rewrite Z in A0. apply inst_of_inj in A0. subst d0. exact N0'.
        -- split; [split; [lia|intros j Lj Oj; unfold t1; rewrite oc_s', Nat.eqb_refl; destruct (Nat.eqb_spec j k); [lia|exact Oj]]|
              split; [intros j X Y; apply (proj1 (i_pend p s I c j Y X))|]].
           intros j t0 X. unfold t1. rewrite (oh_s' s c k (inst_of d) m' a K u w _ _ _ _). split; [exact X|apply (oh_lt_tm p s c j t0 I X)].
      * change (exists e d0, ent (evs s c k (inst_of d) m' a K u w (bor (bd (cs s c)) B) (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s)) t0 = Some e /\
          eokx p (ec e) cc0 pc0 N0 t0 d0 (erf e) B0 /\ pc0 < ek e /\
          eof (ai (cs (evs s c k (inst_of d) m' a K u w (bor (bd (cs s c)) B) (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s)) (ec e)) (ek e))
              (rg (cs (evs s c k (inst_of d) m' a K u w (bor (bd (cs s c)) B) (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s)) (ec e))) = Some d0 /\
          (forall j t1, oc cc0 j = Some t1 -> oc (cs (evs s c k (inst_of d) m' a K u w (bor (bd (cs s c)) B) (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s)) (ec e)) j = Some t1 /\
             rg cc0 j = rg (cs (evs s c k (inst_of d) m' a K u w (bor (bd (cs s c)) B) (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s)) (ec e)) j /\ t1 < t0) /\
          (forall j t1, oc (cs (evs s c k (inst_of d) m' a K u w (bor (bd (cs s c)) B) (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s)) (ec e)) j = Some t1 -> t1 < t0 -> oc cc0 j = Some t1) /\
          (forall j d', oc cc0 j <> None -> pc0 <= j -> ai cc0 j = inst_of d' ->
             eof (ai (cs (evs s c k (inst_of d) m' a K u w (bor (bd (cs s c)) B) (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s)) (ec e)) j)
                 (rg (cs (evs s c k (inst_of d) m' a K u w (bor (bd (cs s c)) B) (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s)) (ec e))) = Some d') /\
          (pc0 <= pcs s (ec e) /\ forall j, j < pc0 -> oc cc0 j = None -> oc (cs (evs s c k (inst_of d) m' a K u w (bor (bd (cs s c)) B) (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s)) (ec e)) j = None) /\
          (forall j, oc cc0 j <> None -> pc0 <= j -> exists d', ai cc0 j = inst_of d' /\ d' <> DFn FFull) /\
          (forall j t1, oh cc0 j = Some t1 -> oh (cs (evs s c k (inst_of d) m' a K u w (bor (bd (cs s c)) B) (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s)) (ec e)) j = Some t1 /\ t1 < t0)).
        apply (snap_old p s c k _ m' a K u w _ _ _ _ I Sv H2 ltac:(lia) (fun _ => le_n _) t0 cc0 pc0 N0 B0 He Hn).
  - (* match *)
    split; [|split].
    + apply S1.
    + intros t0 e He N. destruct (S2 t0 e He N) as [Lk Q]. split.
      * rewrite pcs_match. destruct (Nat.eqb_spec (ec e) c); [rewrite e0 in *|]; lia.
      * intros j t1 Lj Oj. rewrite oc_match in Oj. exact (Q j t1 Lj Oj).
    + intros t0 cc0 pc0 N0 B0 He Hn. destruct (S3 t0 cc0 pc0 N0 B0 He Hn) as (e & d0 & A & Bk & C & D & E & F & G & L & Pn & Ph).
      exists e, d0. split; auto. split; auto. split; auto.
      destruct (proj1 (i_pend p s I c (pcs s c) (le_n _) H1)) as (d1 & A1 & N1).
      rewrite H2 in A1. apply inst_of_inj in A1. subst d1.
      assert (AIM : forall j d', eof (ai (cs s (ec e)) j) (rg (cs s (ec e))) = Some d' ->
                eof (ai (cs (smatch p s c) (ec e)) j) (rg (cs (smatch p s c) (ec e))) = Some d').
      { intros j d' X. rewrite rg_match, ai_match. destruct (Nat.eqb_spec (ec e) c), (Nat.eqb_spec j (pcs s c)); simpl; auto.
        subst. rewrite H2, (eof_inst d _ N1) in X. injection X as <-. exact H3. }
      split; [apply AIM; auto|]. split; [|split; [|split]].
      * intros j t1 X. rewrite oc_match, rg_match. auto.
      * intros j t1 X. rewrite oc_match in X. auto.
      * intros j d' X Y Z. apply AIM. auto.
      * split; [|split; [exact Pn|]].
        -- destruct L as (L1 & L2). split; [rewrite pcs_match; destruct (Nat.eqb_spec (ec e) c); [rewrite e0 in *|]; lia|].
           intros j Lj Oj. rewrite oc_match. auto.
        -- intros j t1 X. rewrite oh_match. auto.
  - (* a CAS's read alone *)
    split; [|split].
    + intros t0 L. unfold sread in L |- *; simpl in L |- *. unfold upd. destruct (Nat.eqb_spec t0 (tm s)); [lia|]. apply S1. lia.
    + intros t0 e He N. unfold sread in N; simpl in N. unfold upd in N. destruct (Nat.eqb_spec t0 (tm s)); [discriminate|].
      assert (Lt : t0 < tm s).
      { unfold ent, sread in He; simpl in He. destruct (Nat.lt_ge_cases t0 (tm s)) as [X|X]; auto.
        rewrite nth_error_app2 in He by (rewrite <- (i_tm p s I); lia).
        destruct (t0 - length (lg s)) as [|n0] eqn:Z; [pose proof (i_tm p s I); lia|destruct n0; discriminate]. }
      rewrite (rd_ent_old p s c k xs B m' a K u w bv I t0 Lt) in He.
      destruct (S2 t0 e He N) as [Lk Q]. split; [exact Lk|]. intros j t1 Lj Oj.
      rewrite (rd_oc s c k xs B m' a K u w bv) in Oj. exact (Q j t1 Lj Oj).
    + intros t0 cc0 pc0 N0 B0 He Hn. unfold sread in He; simpl in He. unfold upd in He. destruct (Nat.eqb_spec t0 (tm s)).
      * subst t0. exfalso. assert (E : ent (sread s c k Plain xs B m' a K u w bv) (tm s) = Some (newevh s c k (ILd Plain xs (fun _ => true)) K u w)).
        { unfold ent, sread; simpl. rewrite (i_tm p s I), nth_error_app2, Nat.sub_diag by lia. reflexivity. }
        specialize (Hn _ E). discriminate.
      * apply (snap_old_rd p s c k xs B m' a K u w bv I Sv H2 H1 Hh t0 cc0 pc0 N0 B0 He Hn).
  - (* passing a non-executing instruction *)
    split; [|split].
    + apply S1.
    + intros t0 e He N. destruct (S2 t0 e He N) as [Lk Q]. split.
      * rewrite (pcs_skip p s c). destruct (Nat.eqb_spec (ec e) c); [rewrite e0 in *|]; lia.
      * intros j t1 Lj Oj. rewrite (oc_skip p s c) in Oj. exact (Q j t1 Lj Oj).
    + intros t0 cc0 pc0 N0 B0 He Hn. destruct (S3 t0 cc0 pc0 N0 B0 He Hn) as (e & d0 & A & Bk & C & D & E & F & G & L & Pn & Ph).
      assert (AIS : forall j, oc (cs s (ec e)) j <> None -> ai (cs (sskip p s c) (ec e)) j = ai (cs s (ec e)) j).
      { intros j X. rewrite (ai_skip p s c). destruct (Nat.eqb_spec (ec e) c), (Nat.eqb_spec j (pcs s c)); simpl; auto.
        exfalso. apply X. rewrite e0, e1. exact K2. }
      assert (OK : oc (cs s (ec e)) (ek e) <> None)
        by (destruct (i_et p s I t0 e A) as (_ & O); rewrite (Hn e A) in O; congruence).
      exists e, d0. split; auto. split; auto. split; auto.
      split; [rewrite (AIS _ OK), (rg_skip p s c); exact D|]. split; [|split; [|split]].
      * intros j t1 X. rewrite (oc_skip p s c), (rg_skip p s c). auto.
      * intros j t1 X. rewrite (oc_skip p s c) in X. auto.
      * intros j d' X Y Z. destruct (oc cc0 j) as [tj|] eqn:Oj; [|congruence].
        destruct (E j tj Oj) as (X1 & _ & _). rewrite (AIS j ltac:(congruence)), (rg_skip p s c). apply G; [congruence|exact Y|exact Z].
      * split; [|split; [exact Pn|]].
        -- destruct L as (L1 & L2). split; [rewrite (pcs_skip p s c); destruct (Nat.eqb_spec (ec e) c); [rewrite e0 in *|]; lia|].
           intros j Lj Oj. rewrite (oc_skip p s c). auto.
        -- intros j t1 X. rewrite (oh_skip p s c). auto.
  - (* S3c: a result fixed: a failure after the read half changes the record's register, of a slot that did not happen *)
    assert (SF : SI p (sflp s cX oX bX)).
    { destruct oX as [kF|]; [destruct bX|]; cbn [sflp]; try exact Sv.
      destruct (cfix_rec _ _ _ _ _ _ _ _ _ HcX) as (HpF & HoF & HhF & HvF).
        assert (EV : forall c' j t1, oc (cs s c') j = Some t1 -> forall d1,
                   eof (ai (cs s c') j) (rg (cs s c')) = Some d1 -> eof (ai (cs (scfail s cX kF) c') j) (rg (cs (scfail s cX kF) c')) = Some d1).
        { intros c' j t1 O d1 D1. rewrite ai_cf. rewrite <- D1. apply eof_ieval. apply (ieval_slot_cf p s cX kF I HpF HoF c' j t1 O). }
        split; [|split].
        + intros t0 L. apply S1. exact L.
        + intros t0 e He N. rewrite oc_cf. exact (S2 t0 e He N).
        + intros t0 cc0 pc0 N0 B0 He Hn. destruct (S3 t0 cc0 pc0 N0 B0 He Hn) as (e & d0 & A & Bk & C & D & E & F & G & L & Pn & Ph).
          assert (OK : oc (cs s (ec e)) (ek e) <> None)
            by (destruct (i_et p s I t0 e A) as (_ & O); rewrite (Hn e A) in O; congruence).
          exists e, d0. split; auto. split; auto. split; auto.
          split; [destruct (oc (cs s (ec e)) (ek e)) as [te|] eqn:Oe; [exact (EV _ _ te Oe d0 D)|congruence]|].
          split; [|split; [|split; [|split]]].
          * intros j t1 X. destruct (E j t1 X) as (X1 & X2 & X3). rewrite oc_cf. split; [exact X1|split; [|exact X3]].
            rewrite rg_cf; [exact X2|]. destruct (Nat.eq_dec (ec e) cX) as [Ec|Nc]; [right; intros Ej; rewrite Ec, Ej in X1; congruence|left; exact Nc].
          * intros j t1 X. rewrite oc_cf in X. auto.
          * intros j d' X Y Z. destruct (oc cc0 j) as [tj|] eqn:Oj; [|congruence].
            destruct (E j tj Oj) as (X1 & _ & _). apply (EV _ _ tj X1). apply G; [congruence|exact Y|exact Z].
          * destruct L as (L1 & L2). split; [exact L1|]. intros j Lj Oj. rewrite oc_cf. auto.
          * split; [exact Pn|]. intros j t1 X. rewrite oh_cf. auto. }
    destruct SF as (S1' & S2' & S3').
    split; [|split].
    + intros t0 L. apply S1'. exact L.
    + intros t0 e He N. change (pcs (scfix0 (sflp s cX oX bX) cX jX bX BX)) with (pcs (sflp s cX oX bX)). rewrite oc_cx. exact (S2' t0 e He N).
    + intros t0 cc0 pc0 N0 B0 He Hn. destruct (S3' t0 cc0 pc0 N0 B0 He Hn) as (e & d0 & X). exists e, d0.
      change (pcs (scfix0 (sflp s cX oX bX) cX jX bX BX)) with (pcs (sflp s cX oX bX)). rewrite !ai_cx, !rg_cx, !oc_cx, !oh_cx. exact X.
Qed.


Lemma SI_cfail : forall p s cX kF, Inv1 p s -> SI p s -> pcs s cX <= kF -> oc (cs s cX) kF = None ->
  SI p (scfail s cX kF).
Proof.
  intros p s cX kF I Sv HpF HoF. pose proof Sv as (S1 & S2 & S3).
        assert (EV : forall c' j t1, oc (cs s c') j = Some t1 -> forall d1,
                   eof (ai (cs s c') j) (rg (cs s c')) = Some d1 -> eof (ai (cs (scfail s cX kF) c') j) (rg (cs (scfail s cX kF) c')) = Some d1).
        { intros c' j t1 O d1 D1. rewrite ai_cf. rewrite <- D1. apply eof_ieval. apply (ieval_slot_cf p s cX kF I HpF HoF c' j t1 O). }
        split; [|split].
        + intros t0 L. apply S1. exact L.
        + intros t0 e He N. rewrite oc_cf. exact (S2 t0 e He N).
        + intros t0 cc0 pc0 N0 B0 He Hn. destruct (S3 t0 cc0 pc0 N0 B0 He Hn) as (e & d0 & A & Bk & C & D & E & F & G & L & Pn & Ph).
          assert (OK : oc (cs s (ec e)) (ek e) <> None)
            by (destruct (i_et p s I t0 e A) as (_ & O); rewrite (Hn e A) in O; congruence).
          exists e, d0. split; auto. split; auto. split; auto.
          split; [destruct (oc (cs s (ec e)) (ek e)) as [te|] eqn:Oe; [exact (EV _ _ te Oe d0 D)|congruence]|].
          split; [|split; [|split; [|split]]].
          * intros j t1 X. destruct (E j t1 X) as (X1 & X2 & X3). rewrite oc_cf. split; [exact X1|split; [|exact X3]].
            rewrite rg_cf; [exact X2|]. destruct (Nat.eq_dec (ec e) cX) as [Ec|Nc]; [right; intros Ej; rewrite Ec, Ej in X1; congruence|left; exact Nc].
          * intros j t1 X. rewrite oc_cf in X. auto.
          * intros j d' X Y Z. destruct (oc cc0 j) as [tj|] eqn:Oj; [|congruence].
            destruct (E j tj Oj) as (X1 & _ & _). apply (EV _ _ tj X1). apply G; [congruence|exact Y|exact Z].
          * destruct L as (L1 & L2). split; [exact L1|]. intros j Lj Oj. rewrite oc_cf. auto.
          * split; [exact Pn|]. intros j t1 X. rewrite oh_cf. auto.
Qed.

Lemma Ext_st : forall p s t, Inv1 p s -> Inv2 p s -> SI p s -> step p s t -> Ext s t.
Proof.
  intros p s t I J Sv St.
  destruct (step_cases p s t St) as [(c & i & m' & a & K & u & w & Hi & Ho & _ & _ & _ & Hhalf & HwO & HvO & He & _ & ->)|[(c & k & d & B & m' & a & K & u & w & Lk & Ho & _ & Hh & HwE & HvE & He & _ & ->)|[(c & d & Ho & Ha & Hd & _ & _ & _ & ->)|[(c & k & xs & B & m' & a & K & u & w & bv & Lk & Ho & Hoh & _ & _ & He & _ & ->)|[(c & K1 & K2 & K3 & _ & K5 & K4 & _ & ->)|(cX & jX & bX & BX & oX & HjX & HfX & HcX & ->)]]]]].
  - destruct (eff_hist _ _ _ _ _ _ _ _ _ He) as (H1 & H2 & H3). unfold sord.
    set (k := pcs s c) in *.
    constructor; unfold evs; simpl.
    + lia.
    + intros c' j y E. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; congruence|auto].
    + intros c' j y E L. unfold upd in E. destruct (Nat.eqb_spec c' c); [subst c'|auto].
      simpl in E. destruct (Nat.eqb_spec j k); [injection E as <-; lia|auto].
    + intros c' j N. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; destruct N as [N|N]; [try unfold k in N; lia|congruence]|auto].
    + intros c'. unfold upd. destruct (Nat.eqb_spec c' c); [subst; lia|lia].
    + intros c' j L. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; lia|auto].
    + intros c' j E. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl. auto.
    + intros y e E. unfold ent in *. simpl. rewrite nth_error_app1; auto. apply nth_error_Some. congruence.
    + intros x a0 b0 O. apply H1. auto.
    + intros x a0 In0. apply H2. auto.
    + intros y L. apply H3. lia.
    + intros q z E. rewrite nth_error_app1; auto. apply nth_error_Some. congruence.
    + intros c'. unfold upd. destruct (Nat.eqb_spec c' c); [subst; lia|lia].
    + intros c' j N. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; congruence|auto].
    + auto.
    + intros c' j N L. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; congruence|auto].
    + intros c' j y E. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl. auto.
    + intros c' j N L. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *.
      destruct (Nat.eqb_spec j k); [subst; lia|auto].
    + intros c' j N L; left. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *.
      destruct (Nat.eqb_spec j k); [subst; lia|auto].
    + intros c' j L O. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *.
      destruct (Nat.eqb_spec j k); [subst; lia|auto].
    + intros c' j N. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *.
      destruct (Nat.eqb_spec j k); [subst j|auto].
      destruct Hhalf as [(Z & _)|(t1 & Z & Ci & U & Ef)]; [congruence|].
      destruct (i_half p s I c k t1 Ho Z (le_n _)) as (_ & (xs & Ax) & _). rewrite Ax in Ef.
      destruct (eofR_half _ _ _ Ef) as (Ic & Xl).
      rewrite (proj2 (half_vals p s c k t1 I J Ho Z)). destruct (eff_read _ _ _ _ _ _ _ _ _ He Xl) as (_ & Ea).
      rewrite Ea, (areg_cas _ _ _ Ci), vv_vd, U, Ic, Ax. reflexivity.
    + intros c' j L O. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *. auto.
  - destruct (eff_hist _ _ _ _ _ _ _ _ _ He) as (H1 & H2 & H3). unfold searly, set_es, searly0.
    constructor; unfold evs; simpl.
    + lia.
    + intros c' j y E. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; congruence|auto].
    + intros c' j y E L. unfold upd in E. destruct (Nat.eqb_spec c' c); [subst c'|auto].
      simpl in E. destruct (Nat.eqb_spec j k); [injection E as <-; lia|auto].
    + intros c' j N. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; destruct N as [N|N]; [try unfold k in N; lia|congruence]|auto].
    + intros c'. lia.
    + intros c' j L. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; lia|auto].
    + intros c' j E. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl. unfold bor. rewrite E. auto.
    + intros y e E. unfold ent in *. simpl. rewrite nth_error_app1; auto. apply nth_error_Some. congruence.
    + intros x a0 b0 O. apply H1. auto.
    + intros x a0 In0. apply H2. auto.
    + intros y L. apply H3. lia.
    + auto.
    + intros c'. unfold upd. destruct (Nat.eqb_spec c' c); [subst; lia|lia].
    + intros c' j N. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; congruence|auto].
    + intros y z E. unfold upd. destruct (Nat.eqb_spec y (tm s)); [|auto].
      subst. exfalso. destruct Sv as (F & _). rewrite (F (tm s) (le_n _)) in E. discriminate.
    + intros c' j N L. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; congruence|auto].
    + intros c' j y E. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl. auto.
    + intros c' j N L. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *.
      destruct (Nat.eqb_spec j k); [subst|auto].
      destruct Hh as [(Z & _)|(t1 & xs & ev & nv & Z & -> & _ & Ac & _)]; [congruence|]. rewrite Ac. reflexivity.
    + intros c' j N L; left. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *.
      destruct (Nat.eqb_spec j k); [subst|auto].
      destruct Hh as [(Z & _)|(t1 & xs & ev & nv & Z & -> & U & Ac & _)]; [congruence|].
      assert (Vo : vok (rg (cs s c) k) = true) by (apply HvE; congruence).
      assert (Wt : w = true) by (apply HwE; congruence).
      rewrite <- (vd_split (rg (cs s c) k)), Vo, (proj2 (half_vals p s c k t1 I J Ho Z)).
      destruct (eff_read _ _ _ _ _ _ _ _ _ He eq_refl) as (_ & Ea).
      rewrite Ea. simpl areg. rewrite Wt, U, Ac. reflexivity.
    + intros c' j L O. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *.
      destruct (Nat.eqb_spec j k); [subst; lia|auto].
    + intros c' j N. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *.
      destruct (Nat.eqb_spec j k); [subst|auto].
      destruct Hh as [(Z & _)|(t1 & xs & ev & nv & Z & -> & U & Ac & _)]; [congruence|].
      rewrite (proj2 (half_vals p s c k t1 I J Ho Z)). destruct (eff_read _ _ _ _ _ _ _ _ _ He eq_refl) as (_ & Ea).
      rewrite Ea. simpl areg. rewrite vv_vd, U, Ac. reflexivity.
    + intros c' j L O. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *. auto.
  - unfold smatch. set (k := pcs s c) in *. constructor; simpl; auto.
    + intros c' j y E. unfold upd. destruct (Nat.eqb_spec c' c); [subst; auto|auto].
    + intros c' j y E L. unfold upd in E. destruct (Nat.eqb_spec c' c); [subst; auto|auto].
    + intros c' j N. unfold upd. destruct (Nat.eqb_spec c' c); [subst; auto|auto].
    + intros c'. unfold upd. destruct (Nat.eqb_spec c' c); [subst; lia|lia].
    + intros c' j L. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; lia|auto].
    + intros c' j E. unfold upd. destruct (Nat.eqb_spec c' c); [subst; auto|auto].
    + intros q z E. rewrite nth_error_app1; auto. apply nth_error_Some. congruence.
    + intros c' j N. unfold upd. destruct (Nat.eqb_spec c' c); [subst; auto|auto].
    + intros c' j N L. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; lia|auto].
    + intros c' j y E. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl. auto.
    + intros c' j N L. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *.
      destruct (Nat.eqb_spec j k); [subst; lia|auto].
    + intros c' j N L. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *. auto.
    + intros c' j L O. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *. auto.
    + intros c' j N. unfold upd. destruct (Nat.eqb_spec c' c); [subst; auto|auto].
    + intros c' j L O. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst; auto|auto].
  - destruct (eff_hist _ _ _ _ _ _ _ _ _ He) as (H1 & H2 & H3). unfold sread.
    constructor; simpl.
    + lia.
    + intros c' j y E. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl. auto.
    + intros c' j y E L. unfold upd in E. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in E. auto.
    + intros c' j N. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; destruct N as [N|N]; [try unfold k in N; lia|congruence]|auto].
    + intros c'. lia.
    + intros c' j L. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; lia|auto].
    + intros c' j E. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl. unfold bor. rewrite E. auto.
    + intros y e E. unfold ent in *. simpl. rewrite nth_error_app1; auto. apply nth_error_Some. congruence.
    + intros x a0 b0 O. apply H1. auto.
    + intros x a0 In0. apply H2. auto.
    + intros y L. apply H3. lia.
    + auto.
    + intros c'. unfold upd. destruct (Nat.eqb_spec c' c); [subst; lia|lia].
    + intros c' j N. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; congruence|auto].
    + intros y z E. unfold upd. destruct (Nat.eqb_spec y (tm s)); [|auto].
      subst. exfalso. destruct Sv as (F & _). rewrite (F (tm s) (le_n _)) in E. discriminate.
    + intros c' j N L. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; congruence|auto].
    + intros c' j y E. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; congruence|auto].
    + intros c' j N L. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *.
      destruct (Nat.eqb_spec j k); [subst; congruence|auto].
    + intros c' j N L; left. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *.
      destruct (Nat.eqb_spec j k); [subst; congruence|auto].
    + intros c' j L O. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *. auto.
    + intros c' j N. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *.
      destruct (Nat.eqb_spec j k); [subst; congruence|auto].
    + intros c' j L O. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *.
      destruct (Nat.eqb_spec j k); [subst; lia|auto].
  - unfold sskip. set (k := pcs s c) in *. constructor; simpl; auto.
    + intros c' j y E. unfold upd. destruct (Nat.eqb_spec c' c); [subst; auto|auto].
    + intros c' j y E L. unfold upd in E. destruct (Nat.eqb_spec c' c); [subst; auto|auto].
    + intros c' j N. unfold upd. destruct (Nat.eqb_spec c' c); [subst; auto|auto].
    + intros c'. unfold upd. destruct (Nat.eqb_spec c' c); [subst; lia|lia].
    + intros c' j L. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; lia|auto].
    + intros c' j E. unfold upd. destruct (Nat.eqb_spec c' c); [subst; auto|auto].
    + intros q z E. rewrite nth_error_app1; auto. apply nth_error_Some. congruence.
    + intros c'. unfold upd. destruct (Nat.eqb_spec c' c); [subst; lia|lia].
    + intros c' j N. unfold upd. destruct (Nat.eqb_spec c' c); [subst; auto|auto].
    + intros c' j N L. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; lia|auto].
    + intros c' j y E. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl. auto.
    + intros c' j N L. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *.
      destruct (Nat.eqb_spec j k); [subst; lia|auto].
    + intros c' j N L. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *. auto.
    + intros c' j L O. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *. auto.
    + intros c' j N. unfold upd. destruct (Nat.eqb_spec c' c); [subst; auto|auto].
    + intros c' j L O. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst; auto|auto].
  - (* S3c: a result fixed; a failure after the read half changes only the record's bit *)
    apply (Ext_trans s (sflp s cX oX bX)).
    + destruct oX as [kX|]; [destruct bX|]; cbn [sflp]; try apply Ext_refl.
      destruct (cfix_rec _ _ _ _ _ _ _ _ _ HcX) as (HpF & HoF & HhF & HvF).
        unfold scfail. constructor; simpl; auto; intros; unfold upd in *;
          repeat match goal with |- context [Nat.eqb ?x cX] => destruct (Nat.eqb_spec x cX); [subst x|] end; simpl in *;
          repeat match goal with |- context [Nat.eqb ?x kX] => destruct (Nat.eqb_spec x kX); [subst x|] end; simpl in *;
          auto; try lia; try congruence.
        all: try (right; split; [exact HvF|reflexivity]).
        all: try (rewrite vv_vd; reflexivity).
        all: try (left; reflexivity).
        all: try (match goal with H : context [Nat.eqb ?x ?y] |- _ => destruct (Nat.eqb_spec x y); [subst x|]; simpl in H; exact H end).
        all: try (exfalso; match goal with H : _ \/ _ |- _ => destruct H; [lia|congruence] end).
    + generalize (sflp s cX oX bX); intros s0.
      constructor; intros; rewrite ?oc_cx, ?oh_cx, ?ai_cx, ?rw_cx, ?rg_cx in *; auto;
        try (change (pcs (scfix0 s0 cX jX bX BX)) with (pcs s0) in *; auto; fail);
        try (left; reflexivity).
      unfold scfix0; simpl; unfold upd. destruct (Nat.eqb_spec c cX); [subst c|auto]. simpl. unfold bor.
      match goal with H : bd _ _ = true |- _ => rewrite H; reflexivity end.
Qed.


Lemma Ext_cfail : forall s cX kX, pcs s cX <= kX -> oc (cs s cX) kX = None -> oh (cs s cX) kX <> None ->
  vok (rg (cs s cX) kX) = true -> Ext s (scfail s cX kX).
Proof.
  intros s cX kX HpF HoF HhF HvF.
        unfold scfail. constructor; simpl; auto; intros; unfold upd in *;
          repeat match goal with |- context [Nat.eqb ?x cX] => destruct (Nat.eqb_spec x cX); [subst x|] end; simpl in *;
          repeat match goal with |- context [Nat.eqb ?x kX] => destruct (Nat.eqb_spec x kX); [subst x|] end; simpl in *;
          auto; try lia; try congruence.
        all: try (right; split; [exact HvF|reflexivity]).
        all: try (rewrite vv_vd; reflexivity).
        all: try (left; reflexivity).
        all: try (match goal with H : context [Nat.eqb ?x ?y] |- _ => destruct (Nat.eqb_spec x y); [subst x|]; simpl in H; exact H end).
        all: try (exfalso; match goal with H : _ \/ _ |- _ => destruct H; [lia|congruence] end).
Qed.

Lemma evok_st : forall p s t, Inv1 p s -> Inv2 p s -> step p s t -> evok t -> evok s.
Proof.
  intros p s t I J H.
  destruct (step_cases p s t H) as [(c & i & m' & a & K & u & w & H1 & H2 & H3 & H4 & Hbh & Hh & _ & _ & H6 & _ & ->)|[(c & k & d & B & m' & a & K & u & w & H1 & H2 & Hso & Hh & _ & _ & H5 & _ & ->)|[(c & d & H1 & H2 & H3 & H4 & H4m & Hfh & ->)|[(c & k & xs & B & m' & a & K & u & w & bv & H1 & H2 & Hh & Hso & H4 & H5 & _ & ->)|[(c & S1 & S2 & S3 & _ & S5 & S4 & _ & ->)|(cX & jX & bX & BX & oX & HjX & HfX & HcX & ->)]]]]].
  - assert (Hst : forall r, settled (cs s c) (pcs s c) r -> ieval i r = ieval i (rg (cs s c))) by (intros r Sr; apply (proj2 (H3 r Sr))).
    assert (Hhk : oh (cs s c) (pcs s c) = None \/
      (u = rw (cs s c) (pcs s c) /\ eofR i (rg (cs s c)) = eofR (ai (cs s c) (pcs s c)) (rg (cs s c))))
      by (destruct Hh as [(Z & _)|(t1 & Z & Ci & U & Ef)]; [left; exact Z|right; split; [exact U|exact Ef]]).
    apply evok_back.
    + intros x y z. apply (older_new_old p s c (pcs s c) i m' a K u w _ _ _ _ I J H2 (le_n _) Hst H6 Hhk).
    + intros x y. apply (in_hs_new p s c (pcs s c) i m' a K u w _ _ _ _ I J H2 (le_n _) Hst H6 Hhk).
    + intros a0 e E. unfold sord, evs; simpl. apply lg_app_nth. exact E.
  - assert (Hst : forall r, settled (cs s c) (pcs s c) r -> ieval (inst_of d) r = ieval (inst_of d) (rg (cs s c)))
      by (intros r _; apply ieval_inst).
    assert (Hhk : oh (cs s c) k = None \/
      (u = rw (cs s c) k /\ eofR (inst_of d) (rg (cs s c)) = eofR (ai (cs s c) k) (rg (cs s c)))).
    { destruct Hh as [(Z & _)|(t1 & xs & ev & nv & Z & -> & U & Ac & _)]; [left; exact Z|right].
      split; [exact U|]. rewrite Ac. reflexivity. }
    apply evok_back.
    + intros x y z. apply (older_new_old p s c k (inst_of d) m' a K u w (bor (bd (cs s c)) B) (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s) I J H2 (Nat.lt_le_incl _ _ H1) Hst H5 Hhk).
    + intros x y. apply (in_hs_new p s c k (inst_of d) m' a K u w (bor (bd (cs s c)) B) (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s) I J H2 (Nat.lt_le_incl _ _ H1) Hst H5 Hhk).
    + intros a0 e E. unfold searly, set_es, searly0, evs; simpl. apply lg_app_nth. exact E.
  - apply evok_back; auto.
  - destruct (rd_mem p s c k xs B m' a K u w bv I J H2 H1 Hh H5) as (Mh & _).
    apply evok_back.
    + intros x y z. rewrite Mh. auto.
    + intros x y. rewrite Mh. auto.
    + intros a0 e E. unfold sread; simpl. apply lg_app_nth. exact E.
  - apply evok_back; auto.
  - unfold scfix0. rewrite hs_flp, lg_flp. apply evok_back; auto.
Qed.


(* ---------- SI and Ext under F2 ---------- *)
Lemma SI_bd : forall p s c B, SI p s -> SI p (sbd s c B).
Proof.
  intros p s c B (S1 & S2 & S3). split; [|split].
  - intros t0 L. apply S1. exact L.
  - intros t0 e He N. change (pcs (sbd s c B)) with (pcs s). rewrite oc_bd. exact (S2 t0 e He N).
  - intros t0 cc0 pc0 N0 B0 He Hn. destruct (S3 t0 cc0 pc0 N0 B0 He Hn) as (e & d0 & X). exists e, d0.
    change (pcs (sbd s c B)) with (pcs s). rewrite !ai_bd, !rg_bd, !oc_bd, !oh_bd. exact X.
Qed.

Lemma SI_cx : forall p s c j b B, SI p s -> SI p (scfix0 s c j b B).
Proof.
  intros p s c j b B (S1 & S2 & S3). split; [|split].
  - intros t0 L. apply S1. exact L.
  - intros t0 e He N. change (pcs (scfix0 s c j b B)) with (pcs s). rewrite oc_cx. exact (S2 t0 e He N).
  - intros t0 cc0 pc0 N0 B0 He Hn. destruct (S3 t0 cc0 pc0 N0 B0 He Hn) as (e & d0 & X). exists e, d0.
    change (pcs (scfix0 s c j b B)) with (pcs s). rewrite !ai_cx, !rg_cx, !oc_cx, !oh_cx. exact X.
Qed.

Lemma Ext_bd : forall s c B, Ext s (sbd s c B).
Proof.
  intros s c B. constructor; intros; rewrite ?oc_bd, ?oh_bd, ?ai_bd, ?rw_bd, ?rg_bd in *; auto;
    try (change (pcs (sbd s c B)) with (pcs s) in *; auto; fail); try (left; reflexivity).
  unfold sbd; simpl; unfold upd. destruct (Nat.eqb_spec c0 c); [subst c0|auto]. simpl. unfold bor.
  match goal with H : bd _ _ = true |- _ => rewrite H; reflexivity end.
Qed.

Lemma Ext_cx : forall s c j b B, Ext s (scfix0 s c j b B).
Proof.
  intros s c j b B. constructor; intros; rewrite ?oc_cx, ?oh_cx, ?ai_cx, ?rw_cx, ?rg_cx in *; auto;
    try (change (pcs (scfix0 s c j b B)) with (pcs s) in *; auto; fail); try (left; reflexivity).
  unfold scfix0; simpl; unfold upd. destruct (Nat.eqb_spec c0 c); [subst c0|auto]. simpl. unfold bor.
  match goal with H : bd _ _ = true |- _ => rewrite H; reflexivity end.
Qed.

(* evok reads hs and lg only *)
Lemma evok_hl : forall s t, hs t = hs s -> lg t = lg s -> evok t -> evok s.
Proof. intros s t H L E. unfold evok, gedge, cedge in *. rewrite H, L in E. exact E. Qed.

(* ---------- the invariants along runQ, without cellful ---------- *)
Record IS (p : prog) (s : st) : Prop := { s1 : Inv1 p s; s2 : Inv2 p s; s3 : Inv3 p s; sO : InvO p s; sS : SI p s }.

Lemma IS_step : forall p s t, IS p s -> stepQ p s t -> IS p t.
Proof.
  intros p s t [I J L Q Sv] S. destruct S as [s t S _|s c k B Ok _|s c j k B _ Hf Ok].
  - pose proof (Inv1_st p s t I S) as I'. pose proof (Inv2_st p s t I J S) as J'. pose proof (Inv3_st p s t I J L S) as L'.
    constructor; auto; [exact (InvO_st p s t I J L Q I' J' L' S)|exact (SI_st p s t I S Sv)].
  - pose proof (rfail_ge _ _ _ _ _ _ _ Ok) as Hp. destruct Ok as (Ho & Hh & _).
    constructor; [apply Inv1_bd; apply Inv1_cfail|apply Inv2_bd; apply Inv2_cfail|apply Inv3_bd; apply Inv3_cfail
      |apply InvO_bd; apply InvO_cfail|apply SI_bd; apply SI_cfail]; auto.
  - constructor; [apply Inv1_cfix|apply Inv2_cfix|apply Inv3_cfix|apply InvO_cfix|apply SI_cx]; auto.
Qed.

Lemma IS_run : forall p s, runQ p s -> IS p s.
Proof.
  intros p s R. induction R as [|s t R IH S].
  - constructor; [apply Inv1_init|apply Inv2_init|apply Inv3_init|apply InvO_init|apply SI_init].
  - exact (IS_step p s t IH S).
Qed.

Lemma reach_runQ : forall p s, reach (stepQ p) s <-> runQ p s.
Proof. intros p s. split; intros H; induction H; try constructor; econstructor; eauto. Qed.

(* ---------- the fields ---------- *)
Section G.
Variable p : prog.
Local Notation RQ s := (reach (stepQ p) s).

Theorem gq_slots : forall s, RQ s -> Inv1 p s.
Proof. intros s R. apply (s1 p s (IS_run p s (proj1 (reach_runQ p s) R))). Qed.
Theorem gq_values : forall s, RQ s -> Inv2 p s.
Proof. intros s R. apply (s2 p s (IS_run p s (proj1 (reach_runQ p s) R))). Qed.
Theorem gq_knowledge : forall s, RQ s -> Inv3 p s.
Proof. intros s R. apply (s3 p s (IS_run p s (proj1 (reach_runQ p s) R))). Qed.
Theorem gq_in_order : forall s, RQ s -> InvO p s.
Proof. intros s R. apply (sO p s (IS_run p s (proj1 (reach_runQ p s) R))). Qed.

Theorem gq_keeps : forall s t, RQ s -> stepQ p s t -> Ext s t.
Proof.
  intros s t R S. destruct (IS_run p s (proj1 (reach_runQ p s) R)) as [I J _ _ Sv].
  destruct S as [s t S _|s c k B Ok _|s c j k B _ _ _].
  - exact (Ext_st p s t I J Sv S).
  - pose proof (rfail_ge _ _ _ _ _ _ _ Ok) as Hp. destruct Ok as (Ho & Hh & Hv & _).
    apply (Ext_trans s (scfail s c k)); [exact (Ext_cfail s c k Hp Ho Hh Hv)|apply Ext_bd].
  - apply Ext_cx.
Qed.

Theorem gq_rule_back : forall s t, RQ s -> stepQ p s t -> evok t -> evok s.
Proof.
  intros s t R S. destruct (IS_run p s (proj1 (reach_runQ p s) R)) as [I J _ _ _].
  destruct S as [s t S _|s c k B _ _|s c j k B _ _ _].
  - exact (evok_st p s t I J S).
  - apply evok_hl; reflexivity.
  - apply evok_hl; reflexivity.
Qed.

Theorem gq_two_level : forall s, tl2ok s <-> evok s.
Proof. exact tl2ok_iff_evok. Qed.

Theorem gq_no_thin_air : wf p -> forall (V : val -> Prop), V 0 -> tclosed p V -> forall s, RQ s ->
  (forall y x, isw s y -> V (wv s y x)) /\ (forall c j, kV V (ai (cs s c) j) (rg (cs s c) j)).
Proof. intros W V V0 Cl s R. exact (no_thin_air_Q p V W V0 Cl s (proj1 (reach_runQ p s) R)). Qed.

Theorem gq_slot0 : forall s, RQ s -> forall c, oc (cs s c) 0 <> None -> 0 < pcs s c.
Proof.
  intros s R. apply reach_runQ in R. induction R as [|s t R IH S]; intros c' O; [simpl in O; congruence|].
  destruct S as [s t S _|s c k B _ _|s c j k B _ _ _].
  - inversion S; subst; repeat match goal with x := _ |- _ => subst x end.
    all: try (rewrite oc_cx, oc_flp in O; match goal with |- 0 < pcs (scfix0 ?X _ _ _ _) _ =>
                change (pcs (scfix0 X _ _ _ _)) with (pcs X) end; rewrite pcs_flp; apply IH; exact O).
    all: cbn [cs pcs] in *;
      unfold upd in *; destruct (Nat.eqb c' c) eqn:E; try (apply Nat.eqb_eq in E; subst c'); cbn in *.
    all: try lia. all: try (apply IH; exact O). all: (destruct k as [|k0]; [lia|apply IH; exact O]).
  - rewrite oc_bd, oc_cf in O. exact (IH c' O).
  - rewrite oc_cx in O. exact (IH c' O).
Qed.

Theorem gq_no_half : cas_free p -> forall s, RQ s -> forall c k, oh (cs s c) k = None.
Proof.
  intros CF s R. apply reach_runQ in R. induction R as [|s t R IH S]; intros c' k'; [reflexivity|].
  destruct S as [s t S _|s c k B Ok _|s c j k B _ _ _].
  - destruct (step_cases p s t S) as [(c & i & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ->)|[(c & k & d & B & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & _ & _ & ->)|[(c & d & _ & _ & _ & _ & _ & _ & ->)|[(c & k & xs & B & m' & a & K & u & w & bv & _ & _ & _ & _ & H4 & _ & _ & ->)|[(c & _ & _ & _ & _ & _ & _ & _ & ->)|(cX & jX & bX & BX & oX & HjX & HfX & HcX & ->)]]]]].
    + unfold sord. rewrite oh_s'. apply IH.
    + unfold searly, set_es, searly0. cbn [cs]. rewrite oh_s'. apply IH.
    + rewrite oh_match. apply IH.
    + exfalso. destruct (H4 (fun _ _ => 0)) as (j & F0 & _). cbv zeta in F0.
      pose proof (eofR_cas _ _ _ (first_atR_eofR _ _ _ _ _ _ _ _ _ F0)) as Ca. rewrite CF in Ca. discriminate.
    + rewrite oh_skip. apply IH.
    + rewrite oh_cx, oh_flp. apply IH.
  - exfalso. destruct Ok as (_ & Hh & _). exact (Hh (IH c k)).
  - rewrite oh_cx. apply IH.
Qed.
End G.

Print Assumptions gq_keeps.
Print Assumptions gq_rule_back.
Print Assumptions gq_slot0.
Print Assumptions gq_no_half.
Print Assumptions gq_in_order.
