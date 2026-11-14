(* Model2: replaying the settle order of a complete reach (STEP as) an interleaving. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2SC M2SCx MIComp.
Require Import M2Iface.

Section Iface.
Context `{IFM : Model}.

Lemma nat_iff_eq : forall a b, (forall j, j < a <-> j < b) -> a = b.
Proof.
  intros a b H. destruct (Nat.lt_trichotomy a b) as [L|[L|L]]; auto.
  - apply H in L. lia.
  - apply H in L. lia.
Qed.

Set Default Proof Using "All".
Section Rp.
Variable p : prog.
Variable s : st.
Hypothesis R : reach (STEP p) s.
Hypothesis CP : done p s.
Hypothesis W : wf p.

Local Abbreviation rrg := (rrg s).
Local Abbreviation bt := (bt s).
Local Abbreviation I1 := (I1 p s R CP W).
Local Abbreviation I2 := (I2 p s R CP W).

Definition corr (n : nat) (l : list sev) (sg0 : sst) : Prop :=
  srun p l sg0 /\ length l = n /\
  (forall q e, nth_error l q = Some e -> exists tau, nth_error (cm s) q = Some (sx e, sk e, tau)) /\
  (forall c j, j < sp sg0 c -> sr sg0 c j = rrg c j).

Lemma corr_sp : forall n l g, corr n l g -> forall c j,
  j < sp g c <-> exists q tau, q < n /\ nth_error (cm s) q = Some (c, j, tau).
Proof.
  intros n l g (A & B & C & D) c j. rewrite (srun_pos p W l g A c j). split.
  - intros (q & e & E & <- & <-). destruct (C q e E) as (tau & T). exists q, tau. split; auto.
    rewrite <- B. apply nth_error_Some. congruence.
  - intros (q & tau & Q & T). destruct (nth_error l q) as [e|] eqn:E.
    + exists q, e. destruct (C q e E) as (tau' & T'). rewrite T in T'. injection T' as <- <- <-. auto.
    + apply nth_error_None in E. lia.
Qed.

Lemma sp_at : forall n l g c k tau, corr n l g -> nth_error (cm s) n = Some (c, k, tau) -> sp g c = k.
Proof.
  intros n l g c k tau H T. apply nat_iff_eq. intros j. rewrite (corr_sp n l g H c j). split.
  - intros (q & t' & Q & T'). apply (i_cmB p s I1 q n c j k t' tau Q T' T).
  - intros Hj.
    assert (Kp : k < pcs s c) by (apply (i_cmA p s I1 c k); exists tau; eapply nth_error_In; eauto).
    destruct (proj1 (i_cmA p s I1 c j) ltac:(lia)) as (t' & T').
    apply In_nth_error in T'. destruct T' as (q & T'). exists q, t'. split; auto.
    destruct (Nat.lt_trichotomy q n) as [L|[L|L]]; auto.
    * subst. rewrite T in T'. injection T' as <- <-. lia.
    * pose proof (i_cmB p s I1 n q c k j tau t' L T T'). lia.
Qed.

Lemma regs_after : forall l g e g', srun p l g -> sstep p g e g' ->
  forall c j, j < sp g c -> sr g' c j = sr g c j.
Proof.
  intros l g e g' Rl H c j Hj. destruct (sstep_shape p W g e g' H) as (i & Hi & _ & Hk & Hsp & Hr & _).
  apply Hr. destruct (Nat.eq_dec c (sx e)) as [->|N]; [right; lia|left; auto].
Qed.

(* a CAS whose verdict is a success read its expected value *)
Lemma vok_val : forall c k i, insr p s c k = Some i -> xload i (rrg c) = true -> is_cas i = true ->
  vok (rrg c k) = true -> vv (rrg c k) = cexp i (rrg c).
Proof.
  intros c k i Hi X Ci Vr. pose proof (insr_lt p s R CP W c k i Hi) as Lk.
  unfold rrg, MIComp.rrg in *.
  destruct (oc (cs s c) k) as [tk|] eqn:Ok.
  - destruct (i_oc p s I1 c k tk Ok) as (en & E1 & E2 & E3).
    assert (E4 : einstr p s en = i)
      by (rewrite (einstr_ins p s R CP W _ en E1), E2, E3; apply (insr_ins p s R CP W c k i Hi)).
    pose proof (oc_eh p s c k tk en I1 Ok E1 E2 E3) as Eh.
    assert (Xe : xload (einstr p s en) (rgof s en) = true) by (rewrite E4; unfold rgof; rewrite E2; exact X).
    pose proof (j_ok p s I2 tk en E1 Eh ltac:(rewrite E4; exact Ci) Xe) as J. rewrite E2, E3, Vr in J.
    destruct (j_ew p s I2 tk en i E1 E4) as [Wq _]. rewrite <- J in Wq. symmetry in Wq.
    apply andb_prop in Wq as [_ Wq]. rewrite Ci in Wq. simpl in Wq. rewrite andb_true_r in Wq. apply Nat.eqb_eq in Wq.
    destruct (j_val p s I2 tk en i E1 E4) as [V _]. rewrite E4 in Xe. specialize (V Xe). rewrite E2, E3, (rval_cas _ _ Ci) in V.
    rewrite V, Wq. unfold rgof. rewrite E2. reflexivity.
  - exfalso. destruct (oh (cs s c) k) as [th|] eqn:Oh.
    + rewrite (i_halfv p s I1 c k th Ok Oh Lk) in Vr. discriminate.
    + rewrite (i_rg0 p s I1 c k Ok Oh) in Vr. discriminate.
Qed.

Lemma replay_step : forall n l g c k tau i, corr n l g -> nth_error (cm s) n = Some (c, k, tau) ->
  insr p s c k = Some i ->
  exists e g', sstep p g e g' /\ sx e = c /\ sk e = k /\
    sr g' c k = (if xload i (rrg c) then areg i (Nat.eqb (enc (map (sm g) (icells i))) (cexp i (rrg c)) && vok (rrg c k))
                                            (enc (map (sm g) (icells i))) else 0) /\
    ((xload i (rrg c) = true -> enc (map (sm g) (icells i)) = rval i (rrg c k)) -> corr (S n) (l ++ [e]) g').
Proof.
  intros n l g c k tau i H T Hi. pose proof (sp_at n l g c k tau H T) as Sp.
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
  exists e, g'. split; auto. split; auto. split; [lia|]. split; auto.
  intros M. split; [econstructor; eauto|]. split; [rewrite length_app; simpl; lia|]. split.
  - intros q e' E. destruct (Nat.lt_ge_cases q (length l)).
    + rewrite nth_error_app1 in E by auto. auto.
    + rewrite nth_error_app2 in E by auto. destruct (q - length l) as [|z] eqn:Z; [|destruct z; discriminate].
      simpl in E. injection E as <-. assert (q = n) by lia. subst q. exists tau. rewrite Ex, Hk. auto.
  - intros c' j Hj. rewrite Hsp in Hj. unfold upd in Hj.
    destruct (Nat.eq_dec c' c) as [->|N].
    + rewrite Nat.eqb_refl in Hj. destruct (Nat.eq_dec j k) as [->|Nj].
      * rewrite Rk. destruct (xload i (rrg c)) eqn:X.
        { specialize (M eq_refl). destruct (is_cas i) eqn:Ci.
          - rewrite (areg_cas _ _ _ Ci). rewrite (rval_cas _ _ Ci) in M. rewrite M.
            destruct (vok (rrg c k)) eqn:Vr.
            + rewrite (vok_val c k i Hi X Ci Vr), Nat.eqb_refl. simpl. rewrite <- (vok_val c k i Hi X Ci Vr).
              rewrite <- Vr. apply vd_split.
            + rewrite andb_false_r. rewrite <- (vd_split (rrg c k)) at 2. rewrite Vr. reflexivity.
          - assert (Ar : forall b v, areg i b v = v) by (intros b v; destruct i; simpl in Ci; try discriminate; reflexivity).
            assert (Rr : forall a, rval i a = a) by (intros a; destruct i; simpl in Ci; try discriminate; reflexivity).
            rewrite Ar, M, Rr. reflexivity. }
        destruct (oc (cs s c) k) as [tk|] eqn:Ok.
        -- destruct (i_oc p s I1 c k tk Ok) as (en & E1 & E2 & E3).
           assert (E4 : einstr p s en = i)
             by (rewrite (einstr_ins p s R CP W _ en E1), E2, E3; apply (insr_ins p s R CP W c k i Hi)).
           destruct (j_val p s I2 tk en i E1 E4) as [_ V]. unfold rgof in V. rewrite E2, E3 in V.
           symmetry. apply (V X).
        -- symmetry. apply (i_rg0 p s I1 c k Ok). destruct (oh (cs s c) k) as [th|] eqn:Oh; [|reflexivity].
           exfalso. pose proof (insr_lt p s R CP W c k i Hi) as Lk. destruct (i_halfp p s I1 c k th Ok Oh Lk) as (F & _).
           destruct (proj1 (i_cmA p s I1 c k) Lk) as (tau0 & T0).
           rewrite (proj2 (i_set p s I1 c k tau0 T0)) in F. pose proof (insr_ins p s R CP W c k i Hi) as Ii. unfold rrg, MIComp.rrg in Ii. rewrite Ii in F.
           destruct i as [| |m0 x0 c0 e0 n0| |]; simpl in F; try discriminate. apply andb_true_iff in F as [C0 _].
           unfold xload, icond, rrg in X; simpl in X. rewrite C0 in X. discriminate.
      * rewrite Hr by (right; rewrite Hk; lia). apply D. lia.
    + apply Nat.eqb_neq in N as N'. rewrite N' in Hj. rewrite Hr by (left; auto). apply D. auto.
Qed.

Lemma replay : forall n, n <= length (cm s) ->
  (exists l g, corr n l g) \/
  (exists n0 l g c k tau i, n0 < n /\ corr n0 l g /\ nth_error (cm s) n0 = Some (c, k, tau) /\
     insr p s c k = Some i /\ xload i (rrg c) = true /\ enc (map (sm g) (icells i)) <> rval i (rrg c k)).
Proof.
  induction n as [|n IH]; intros Hn.
  - left. exists [], ssinit. split; [constructor|]. split; [reflexivity|]. split.
    + intros q e E. destruct q; discriminate.
    + intros c j Hj. simpl in Hj. lia.
  - destruct (IH ltac:(lia)) as [(l & g & H)|(n0 & l & g & c & k & tau & i & A)].
    + destruct (nth_error (cm s) n) as [[[c k] tau]|] eqn:T; [|apply nth_error_None in T; lia].
      destruct (cm_ins p s R CP W n c k tau T) as (i & Hi).
      destruct (replay_step n l g c k tau i H T Hi) as (e & g' & St & Ex & Ek & Rk & Next).
      destruct (xload i (rrg c)) eqn:X.
      * destruct (Nat.eq_dec (enc (map (sm g) (icells i))) (rval i (rrg c k))) as [M|M].
        -- left. exists (l ++ [e]), g'. apply Next. auto.
        -- right. exists n, l, g, c, k, tau, i. refine (conj _ (conj H (conj T (conj Hi (conj X M))))). lia.
      * left. exists (l ++ [e]), g'. apply Next. discriminate.
    + right. exists n0, l, g, c, k, tau, i. destruct A as (A1 & A2). split; [lia|auto].
Qed.

End Rp.

End Iface.
