(* M2PFix.v re-checked on M2DQ (stepQ) through M2DQShim; scripts as in M2PFix.v except where marked DQ. *)
(* Model2, S3c in the DRF core: the verdict the SC replay takes at a place
   whose result a step of the run fixed. A fix is made at one step m, under
   the registers R1 considers then; it is the replay's verdict at the place
   exactly when the replay's registers below the place are among those
   (they continue the state after m there). This file: a result fixed stays,
   the step that fixed it, the test, and what a fix that applies says. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO M2Cont M2DQEquiv M2Trace M2DQMono M2DA M2DP M2DQ M2DQInv M2DQIface M2DQTrace M2DQTr M2DQShim.

(* a step changes the result fixed at a place only by fixing it there *)
Lemma fx_step : forall p s t c j, step p s t ->
  fx (cs t c) j = fx (cs s c) j \/
  (fx (cs s c) j = None /\ exists b B o, t = scfix0 (sflp s c o b) c j b B /\ pcs s c <= j /\
     (cfix_ok p c (cs s c) (pcs s c) (tp s c) j b B o \/
      (* DQ: q_sfix *) (b = true /\ o = None /\ exists k, sfix_ok p c (cs s c) (pcs s c) (tp s c) j k B))).
Proof.
  intros p s t c j St.
  destruct (stepQ_cases p s t St) as [St0|[(cR & kR & BR & ER & _)|(cS & jS & kS & BS & ES & HjS & HfS & HsS)]].
  2:{ left. rewrite ER, fx_bd. change (scfail s cR kR) with (sflp s cR (Some kR) false). rewrite fx_flp. reflexivity. }
  2:{ change (scfix0 s cS jS true BS) with (scfix0 (sflp s cS None true) cS jS true BS) in ES. rewrite ES.
      assert (Ef : fx (cs (scfix0 (sflp s cS None true) cS jS true BS) c) j =
                   if Nat.eqb c cS then (if Nat.eqb j jS then Some true else fx (cs s c) j) else fx (cs s c) j).
      { unfold scfix0. cbn [cs]. unfold upd at 1. cbv beta. destruct (Nat.eqb_spec c cS) as [->|N].
        - cbn [fx]. unfold upd. rewrite fx_flp. reflexivity.
        - rewrite fx_flp. reflexivity. }
      rewrite Ef. destruct (Nat.eqb_spec c cS) as [->|N]; [|left; reflexivity].
      destruct (Nat.eqb_spec j jS) as [->|N]; [|left; reflexivity].
      right. split; [exact HfS|]. exists true, BS, None. split; [reflexivity|]. split; [exact HjS|].
      right. split; [reflexivity|]. split; [reflexivity|]. exists kS. exact HsS. }
  destruct (step_cases p s t St0) as [(c0 & i & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ->)|[(c0 & k & d & B & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & _ & _ & ->)|[(c0 & d & _ & _ & _ & _ & _ & _ & ->)|[(c0 & k & xs & B & m' & a & K & u & w & bv & _ & _ & _ & _ & _ & _ & _ & ->)|[(c0 & _ & _ & _ & _ & _ & _ & _ & ->)|(cX & jX & bX & BX & oX & HjX & HfX & HcX & ->)]]]]].
  1-5: left; unfold searly, set_es, searly0, sord, evs, smatch, sskip, sread; cbn [cs]; cbv zeta; unfold upd at 1; cbv beta;
       destruct (Nat.eqb_spec c c0) as [->|N]; reflexivity.
  assert (Ef : fx (cs (scfix0 (sflp s cX oX bX) cX jX bX BX) c) j =
               if Nat.eqb c cX then (if Nat.eqb j jX then Some bX else fx (cs s c) j) else fx (cs s c) j).
  { unfold scfix0. cbn [cs]. unfold upd at 1. cbv beta. destruct (Nat.eqb_spec c cX) as [->|N].
    - cbn [fx]. unfold upd. rewrite fx_flp. reflexivity.
    - rewrite fx_flp. reflexivity. }
  rewrite Ef. destruct (Nat.eqb_spec c cX) as [->|N]; [|left; reflexivity].
  destruct (Nat.eqb_spec j jX) as [->|N]; [|left; reflexivity].
  right. split; [exact HfX|]. exists bX, BX, oX. split; [reflexivity|]. split; [assumption|left; assumption].
Qed.

(* DQ: an executing CAS, from its description or its load part *)
Lemma eof_cas_x : forall i r d, eof i r = Some d -> is_cas (inst_of d) = true -> is_cas i && icond i r = true.
Proof.
  intros [m x c0|m x c0 v|m x c0 e n0|f0|] r d H C; simpl in H; try discriminate.
  - destruct (c0 r); [injection H as <-; discriminate C|discriminate].
  - destruct (c0 r); [injection H as <-; discriminate C|discriminate].
  - destruct (c0 r) eqn:E; [|discriminate]. unfold icond, ieval. cbn. rewrite E. reflexivity.
  - destruct f0; try discriminate; injection H as <-; discriminate C.
Qed.
Lemma eofR_x : forall i r m xs, eofR i r = Some (m, xs) -> is_cas i && icond i r = true.
Proof.
  intros i r m xs E. unfold icond, ieval. destruct i as [| |m1 x1 c1 e1 n1| |]; try discriminate.
  cbn in E |- *. destruct (c1 r); [reflexivity|discriminate].
Qed.

Lemma fx_keep_step : forall p s t c j b, step p s t -> fx (cs s c) j = Some b -> fx (cs t c) j = Some b.
Proof.
  intros p s t c j b St F. destruct (fx_step p s t c j St) as [E|(E & _)]; [rewrite E; exact F|congruence].
Qed.

Section FT.
Variable p : prog.
Variable f : nat -> st.
Variable n : nat.
Hypothesis T : trace p f n.
Hypothesis W : wf p.
Hypothesis Wc : cellful p.

Lemma fx_keep : forall i i' c j b, i <= i' -> i' <= n -> fx (cs (f i) c) j = Some b -> fx (cs (f i') c) j = Some b.
Proof.
  intros i i' c j b L L' F. induction i' as [|i' IH].
  - assert (i = 0) by lia. subst. exact F.
  - destruct (Nat.eq_dec i (S i')) as [->|N]; [exact F|].
    apply (fx_keep_step p (f i') (f (S i'))); [apply (tr_step p f n T); lia|]. apply IH; lia.
Qed.

Lemma fx_birth : forall i c j b, i <= n -> fx (cs (f i) c) j = Some b ->
  exists m, m < i /\ fx (cs (f m) c) j = None /\ fx (cs (f (S m)) c) j = Some b.
Proof.
  induction i as [|i IH]; intros c j b L F.
  - rewrite (proj1 T) in F. simpl in F. discriminate.
  - destruct (fx (cs (f i) c) j) as [b'|] eqn:E.
    + assert (Eb : b' = b).
      { pose proof (fx_keep i (S i) c j b' ltac:(lia) L E) as Z. rewrite F in Z. injection Z as ->. reflexivity. }
      subst b'. destruct (IH c j b ltac:(lia) E) as (m & Lm & E1 & E2). exists m. split; [lia|]. split; assumption.
    + exists i. split; [lia|]. split; assumption.
Qed.

(* the step m fixed the result at place j *)
Definition fxm (c j m : nat) : bool :=
  match fx (cs (f m) c) j, fx (cs (f (S m)) c) j with None, Some _ => true | _, _ => false end.

Lemma fxm_true : forall c j m, fxm c j m = true -> fx (cs (f m) c) j = None /\ exists b, fx (cs (f (S m)) c) j = Some b.
Proof.
  intros c j m E. unfold fxm in E. destruct (fx (cs (f m) c) j), (fx (cs (f (S m)) c) j) as [b0|]; try discriminate.
  split; [reflexivity|]. exists b0. reflexivity.
Qed.

Lemma fxm_unique : forall c j m1 m2, m1 < n -> m2 < n -> fxm c j m1 = true -> fxm c j m2 = true -> m1 = m2.
Proof.
  assert (H : forall c j m1 m2, m1 < m2 -> m2 < n -> fxm c j m1 = true -> fxm c j m2 = true -> False).
  { intros c j m1 m2 L L2 F1 F2. destruct (fxm_true c j m1 F1) as (_ & b & E1). destruct (fxm_true c j m2 F2) as (E2 & _).
    pose proof (fx_keep (S m1) m2 c j b ltac:(lia) ltac:(lia) E1) as Z. congruence. }
  intros c j m1 m2 L1 L2 F1 F2. destruct (Nat.lt_trichotomy m1 m2) as [L|[L|L]]; [exfalso; eauto|exact L|exfalso; eauto].
Qed.

(* the registers continue, below j, the state after step m (R1's registers there) *)
Definition fxreg (c m : nat) (r : regs) : regs :=
  creg p c (cs (f (S m)) c) (pcs (f (S m)) c) (tp (f (S m)) c) (bd (cs (f (S m)) c)) (Fd p c r).

Definition fxt (c j m : nat) (r : regs) : bool := forallb (fun q => Nat.eqb (r q) (fxreg c m r q)) (seq 0 j).

Lemma fxt_spec : forall c j m r, fxt c j m r = true <-> agree r (fxreg c m r) j.
Proof.
  intros c j m r. unfold fxt. rewrite forallb_forall. split.
  - intros H q Lq. apply Nat.eqb_eq. apply H. apply in_seq. lia.
  - intros H q Iq. apply in_seq in Iq. apply Nat.eqb_eq. apply H. lia.
Qed.

(* the verdict a fix gives the replay at place j of context c, with registers r *)
Definition fxv (c j : nat) (r : regs) : option bool :=
  match find (fxm c j) (seq 0 n) with
  | Some m => if fxt c j m r then fx (cs (f (S m)) c) j else None
  | None => None
  end.

Lemma fxv_spec : forall c j r b, fxv c j r = Some b ->
  exists m, m < n /\ fx (cs (f m) c) j = None /\ fx (cs (f (S m)) c) j = Some b /\ agree r (fxreg c m r) j.
Proof.
  intros c j r b E. unfold fxv in E. destruct (find (fxm c j) (seq 0 n)) as [m|] eqn:Fi; [|discriminate].
  apply find_some in Fi as (Im & Fm). apply in_seq in Im.
  destruct (fxt c j m r) eqn:Ft; [|discriminate]. apply fxt_spec in Ft.
  destruct (fxm_true c j m Fm) as (E0 & _). exists m. split; [lia|]. split; [exact E0|]. split; assumption.
Qed.

(* registers that continue a state where the result at j is fixed get that result *)
Lemma fxv_ccJ : forall i c j r J b, i <= n -> ccJ p c (cs (f i) c) (pcs (f i) c) (bd (cs (f i) c)) r J -> j <= J ->
  fx (cs (f i) c) j = Some b -> fxv c j r = Some b.
Proof.
  intros i c j r J b Li C Lj F. destruct (fx_birth i c j b Li F) as (m & Lm & E0 & E1).
  assert (Fm : fxm c j m = true) by (unfold fxm; rewrite E0, E1; reflexivity).
  unfold fxv. destruct (find (fxm c j) (seq 0 n)) as [m'|] eqn:Fi.
  2:{ exfalso. pose proof (find_none _ _ Fi m ltac:(apply in_seq; lia)) as Z. congruence. }
  apply find_some in Fi as (Im & Fm'). apply in_seq in Im.
  assert (m' = m) by (apply (fxm_unique c j m' m); auto; lia). subst m'.
  assert (Ft : fxt c j m r = true).
  { apply fxt_spec. assert (Rm : run p (f (S m))) by (apply (tr_run p f n T); lia).
    pose proof (mono_tr p f n T W Wc c r J (S m) i ltac:(lia) Li C) as C'.
    pose proof (ccJ_agree p (f (S m)) W Wc Rm c _ r J C') as A. intros q Lq. unfold fxreg. apply A. lia. }
  rewrite Ft. exact E1.
Qed.

Lemma Fd_agree : forall c r r' J, agree r r' J -> forall b y, b < J -> Fd p c r b y = Fd p c r' b y.
Proof.
  intros c r r' J A b y Lb. assert (Ab : agree r r' (S b)) by (apply (agree_le _ _ _ _ A); lia).
  unfold Fd. rewrite (proj1 (ins_agree p W c b r r' (agree_le _ _ _ b Ab ltac:(lia)))), (Ab b ltac:(lia)).
  rewrite (dec_agree p c r r' b y W Ab). reflexivity.
Qed.

Lemma fxv_agree : forall c j r r', agree r r' j -> fxv c j r = fxv c j r'.
Proof.
  intros c j r r' A. unfold fxv. destruct (find (fxm c j) (seq 0 n)) as [m|] eqn:Fi; [|reflexivity].
  apply find_some in Fi as (Im & _). apply in_seq in Im.
  assert (Rm : run p (f (S m))) by (apply (tr_run p f n T); lia).
  assert (G : agree (fxreg c m r) (fxreg c m r') j).
  { unfold fxreg. apply (creg_f_agree p c _ _ _ _ _ _ j W (pend_ok_of p (f (S m)) c (Inv1_run p _ Rm))).
    apply (Fd_agree c r r' j A). }
  assert (E : fxt c j m r = fxt c j m r').
  { destruct (fxt c j m r) eqn:E1, (fxt c j m r') eqn:E2; try reflexivity.
    - exfalso. apply fxt_spec in E1. assert (fxt c j m r' = true) by (apply fxt_spec; intros q Lq; rewrite <- (A q Lq), <- (G q Lq); apply E1; exact Lq). congruence.
    - exfalso. apply fxt_spec in E2. assert (fxt c j m r = true) by (apply fxt_spec; intros q Lq; rewrite (A q Lq), (G q Lq); apply E2; exact Lq). congruence. }
  rewrite E. reflexivity.
Qed.

(* what the fix at step m says about registers that continue the state after m below its place *)
Lemma fix_facts : forall m c j b r, m < n -> fx (cs (f m) c) j = None -> fx (cs (f (S m)) c) j = Some b ->
  agree r (fxreg c m r) j -> (* DQ *) is_cas (ins p c j r) && icond (ins p c j r) r = true ->
  pcs (f m) c <= j /\ pcs (f (S m)) c = pcs (f m) c /\ is_cas (ins p c j r) = true /\ icond (ins p c j r) r = true /\
  pend_at p c (cs (f m) c) (pcs (f m) c) (tp (f m) c) r j = None /\
  (forall k, hpend_at p c (cs (f m) c) (pcs (f m) c) (tp (f m) c) r j = Some k ->
     vok (rg (cs (f m) c) k) = true /\ (b = false -> vok (rg (cs (f (S m)) c) k) = false)) /\
  (forall k d, placed p c (cs (f (S m)) c) (pcs (f (S m)) c) r k d j -> placed p c (cs (f m) c) (pcs (f m) c) r k d j) /\
  (forall q, q < pcs (f m) c -> rg (cs (f (S m)) c) q = rg (cs (f m) c) q).
Proof.
  intros m c j b r Lm F0 F1 Ag Xc.
  assert (Rs : run p (f m)) by (apply (tr_run p f n T); lia).
  set (s := f m) in *.
  destruct (fx_step p s (f (S m)) c j (tr_step p f n T m Lm)) as [E|(_ & b' & B & o & Et & Hj & HcQ)]; [congruence|].
  assert (Eb : b' = b).
  { rewrite Et in F1. unfold scfix0 in F1. cbn [cs] in F1. unfold upd at 1 in F1. rewrite Nat.eqb_refl in F1.
    cbn [fx] in F1. unfold upd in F1. rewrite Nat.eqb_refl in F1. injection F1 as ->. reflexivity. }
  subst b'.
  destruct HcQ as [Hc|(Bt & Eo & kS & Hs)].
  2:{ (* DQ q_sfix: the claim under the valuation of r is j, since j holds an executing CAS there *)
    subst b o. cbn [sflp] in Et. pose proof (Inv1_run p s Rs) as I.
    assert (Hc1 : forall F k, hpend_at p c (cs s c) (pcs s c) (tp s c)
        (creg p c (cs s c) (pcs s c) (tp s c) (bor (bd (cs s c)) B) F) j = Some k -> vok (rg (cs s c) k) = true \/ true = false)
      by (intros F k Hk; left; exact (sfix_hc _ _ _ _ _ _ _ _ Hs F k Hk)).
    assert (Ct : cs (f (S m)) c = cc_fx (cs s c) (bor (bd (cs s c)) B) (upd (fx (cs s c)) j (Some true)))
      by (rewrite Et; unfold scfix0; cbn [cs]; unfold upd at 1; rewrite Nat.eqb_refl; reflexivity).
    assert (Pt : pcs (f (S m)) = pcs s) by (rewrite Et; reflexivity).
    assert (Tt : tp (f (S m)) = tp s) by (rewrite Et; reflexivity).
    assert (Fam : exists F, forall q, creg p c (cs s c) (pcs s c) (tp s c) (bor (bd (cs s c)) B) F q = fxreg c m r q).
    { destruct (cx_regs p s c j true B W I F0 Hc1 (fun _ => false) (Fd p c r)) as (F1' & EQ1).
      exists F1'. intros q. unfold fxreg. rewrite Ct, Pt, Tt.
      transitivity (creg p c (cs s c) (pcs s c) (tp s c) (bor (bd (cs s c)) (bor B (fun _ => false))) F1' q).
      - apply (creg_Bext p c _ _ _ _ _ _ W (pend_ok_of p s c I)). intros q0. unfold bor. destruct (bd (cs s c) q0), (B q0); reflexivity.
      - rewrite EQ1. apply (creg_Bext p c (cc_fx (cs s c) (bor (bd (cs s c)) B) (upd (fx (cs s c)) j (Some true))) _ _ _ _ _ W (pend_ok_of p s c I)).
        intros q0. cbn [bd cc_fx]. unfold bor. destruct (bd (cs s c) q0), (B q0); reflexivity. }
    destruct Fam as (F & EF).
    set (g := creg p c (cs s c) (pcs s c) (tp s c) (bor (bd (cs s c)) B) F) in *.
    assert (Agg : agree r g j) by (intros q Lq; rewrite (EF q); apply Ag; exact Lq).
    pose proof (pend_ok_of p s c I) as PO.
    destruct (ins_agree p W c j r g Agg) as [Ei Ee].
    destruct Hs as (_ & _ & Vk & Hs). destruct (Hs F) as (jf & _ & Hjf & Pjf & _ & _ & _ & _ & Ejf). fold g in Hjf, Pjf, Ejf.
    assert (Jf : jf = j).
    { destruct Ejf as [Ejf|Ejf]; [exact Ejf|]. exfalso. rewrite (ieval_cond _ _ _ Ee), Ei in Xc. congruence. }
    subst jf.
    assert (Pr : pend_at p c (cs s c) (pcs s c) (tp s c) r j = None) by (rewrite (pend_at_agree p W c _ _ _ r g j PO Agg); exact Pjf).
    assert (Hr : hpend_at p c (cs s c) (pcs s c) (tp s c) r j = Some kS) by (rewrite (hpend_at_agree p W c _ _ _ r g j PO Agg); exact Hjf).
    apply andb_prop in Xc as [Ci Co].
    split; [exact Hj|]. split; [rewrite Pt; reflexivity|]. split; [exact Ci|]. split; [exact Co|]. split; [exact Pr|]. split; [|split].
    - intros k Hk'. rewrite Hr in Hk'. injection Hk' as <-. split; [exact Vk|intros Z; discriminate Z].
    - intros k d Pl. rewrite Ct, Pt in Pl. exact (proj1 (placed_fx _ _ _ _ _ _ _ _ _ _) Pl).
    - intros q Lq. apply (x_rg _ _ (Ext_step p s (f (S m)) Rs (tr_step p f n T m Lm))). left. exact Lq. }
  assert (Ecf : forall k', cs (scfail s c k') c = cc_rg (cs s c) (upd (rg (cs s c)) k' (vd false (vv (rg (cs s c) k')))))
    by (intros k'; unfold scfail; cbn [cs]; unfold upd at 1; rewrite Nat.eqb_refl; reflexivity).
  set (s1 := sflp s c o b) in *.
  pose proof (Inv1_run p s Rs) as I.
  destruct (cfix_pre p s c j b B o Rs Hc) as (I1 & Hc1).
  assert (Hf1 : fx (cs s1 c) j = None) by (unfold s1; rewrite fx_flp; exact F0).
  assert (Ct : cs (f (S m)) c = cc_fx (cs s1 c) (bor (bd (cs s1 c)) B) (upd (fx (cs s1 c)) j (Some b)))
    by (rewrite Et; unfold scfix0; cbn [cs]; unfold upd at 1; rewrite Nat.eqb_refl; reflexivity).
  assert (Pt : pcs (f (S m)) = pcs s) by (rewrite Et; unfold scfix0; cbn [pcs]; unfold s1; apply pcs_flp).
  assert (Tt : tp (f (S m)) = tp s) by (rewrite Et; unfold scfix0; cbn [tp]; unfold s1; apply tp_flp).
  assert (P1 : pcs s1 = pcs s) by (unfold s1; apply pcs_flp).
  assert (T1 : tp s1 = tp s) by (unfold s1; apply tp_flp).
  assert (Bd1 : bd (cs s1 c) = bd (cs s c)) by (unfold s1; apply bd_flp).
  (* the old state's free values giving the same registers *)
  assert (Fam : exists F, forall q, creg p c (cs s c) (pcs s c) (tp s c) (bor (bd (cs s c)) B) F q = fxreg c m r q).
  { destruct (cx_regs p s1 c j b B W I1 Hf1 Hc1 (fun _ => false) (Fd p c r)) as (F1' & EQ1).
    assert (EQ1' : forall q, creg p c (cs s1 c) (pcs s c) (tp s c) (bor (bd (cs s c)) B) F1' q = fxreg c m r q).
    { intros q. unfold fxreg. rewrite Ct, Pt, Tt.
      rewrite <- P1, <- T1.
      transitivity (creg p c (cs s1 c) (pcs s1 c) (tp s1 c) (bor (bd (cs s1 c)) (bor B (fun _ => false))) F1' q).
      - apply (creg_Bext p c _ _ _ _ _ _ W (pend_ok_of p s1 c I1)). intros q0. rewrite Bd1. unfold bor. destruct (bd (cs s c) q0), (B q0); reflexivity.
      - rewrite EQ1. apply (creg_Bext p c (cc_fx (cs s1 c) (bor (bd (cs s1 c)) B) (upd (fx (cs s1 c)) j (Some b))) _ _ _ _ _ W (pend_ok_of p s1 c I1)).
        intros q0. cbn [bd cc_fx]. unfold bor. destruct (bd (cs s1 c) q0), (B q0); reflexivity. }
    unfold s1 in EQ1'. destruct o as [kX|]; [destruct b|]; cbn [sflp] in EQ1'; try (exists F1'; exact EQ1').
    destruct (cfix_rec _ _ _ _ _ _ _ _ _ Hc) as (HpF & HoF & HhF & HvF).
    destruct (cf_regs p s c kX W Rs HpF HoF HvF B F1') as (F2 & EQ2).
    exists F2. intros q. rewrite EQ2. rewrite <- (EQ1' q). rewrite Ecf. reflexivity. }
  destruct Fam as (F & EF).
  set (g := creg p c (cs s c) (pcs s c) (tp s c) (bor (bd (cs s c)) B) F) in *.
  assert (Agg : agree r g j) by (intros q Lq; rewrite (EF q); apply Ag; exact Lq).
  destruct Hc as (v & Hv). pose proof (Hv F) as HF. cbv zeta in HF. fold g in HF. destruct HF as (Ci & Co & Pn & Ho & Hk & _).
  pose proof (pend_ok_of p s c I) as PO.
  destruct (ins_agree p W c j r g Agg) as [Ei Ee].
  assert (Pr : pend_at p c (cs s c) (pcs s c) (tp s c) r j = None) by (rewrite (pend_at_agree p W c _ _ _ r g j PO Agg); exact Pn).
  assert (Hr : hpend_at p c (cs s c) (pcs s c) (tp s c) r j = o) by (rewrite (hpend_at_agree p W c _ _ _ r g j PO Agg); exact Ho).
  split; [exact Hj|]. split; [rewrite Pt; reflexivity|]. split; [rewrite Ei; exact Ci|].
  split; [rewrite (ieval_cond _ _ _ Ee), Ei; exact Co|]. split; [exact Pr|]. split; [|split].
  - intros k Hk'. rewrite Hr in Hk'. split; [apply Hk; exact Hk'|].
    intros Eb. rewrite Ct. cbn [rg cc_fx]. unfold s1. rewrite Hk', Eb. cbn [sflp]. rewrite Ecf. cbn [rg cc_rg].
    unfold upd. rewrite Nat.eqb_refl. apply vok_vd.
  - intros k d Pl. rewrite Ct, Pt in Pl. apply (proj1 (placed_fx _ _ _ _ _ _ _ _ _ _)) in Pl.
    unfold s1 in Pl. destruct o as [kX|]; [destruct b|]; cbn [sflp] in Pl; try exact Pl.
    rewrite Ecf in Pl. exact (proj1 (placed_rg _ _ _ _ _ _ _ _ _) Pl).
  - intros q Lq. apply (x_rg _ _ (Ext_step p s (f (S m)) Rs (tr_step p f n T m Lm))). left. exact Lq.
Qed.

(* the replay's register at the place j, from registers that continue a state no older than the fix *)
Lemma fix_A6 : forall m c j b r i r', m < n -> fx (cs (f m) c) j = None -> fx (cs (f (S m)) c) j = Some b ->
  agree r (fxreg c m r) j -> S m <= i -> i <= n ->
  ccJ p c (cs (f i) c) (pcs (f i) c) (bd (cs (f i) c)) r' (S j) -> agree r r' j ->
  is_load (ins p c j r') && icond (ins p c j r') r' = true -> (* DQ *) is_cas (ins p c j r') = true ->
  vok (r' j) = b && Nat.eqb (vv (r' j)) (cexp (ins p c j r') r').
Proof.
  intros m c j b r i r' Lm F0 F1 Ag L1 L2 C Ar X Cr.
  assert (Xc : is_cas (ins p c j r) && icond (ins p c j r) r = true).
  { destruct (ins_agree p W c j r r' Ar) as [E1 E2]. rewrite (ieval_cond _ _ _ E2), E1. apply andb_prop in X as [_ X]. rewrite Cr, X. reflexivity. }
  destruct (fix_facts m c j b r Lm F0 F1 Ag Xc) as (Hj & Pe & Ci & _ & Pn & _ & Pl & _).
  pose proof (mono_tr p f n T W Wc c r' (S j) (S m) i L1 L2 C) as (_ & _ & _ & _ & _ & _ & _ & A6 & _).
  apply (A6 j b); [rewrite Pe; exact Hj|lia| |exact X| |exact F1].
  - intros k d P. assert (Pr : placed p c (cs (f (S m)) c) (pcs (f (S m)) c) r k d j)
      by (apply (placed_agree p W c _ _ r' r k d j); [intros q Lq; symmetry; apply Ar; exact Lq|exact P]).
    apply Pl in Pr. assert (Rs : run p (f m)) by (apply (tr_run p f n T); lia).
    assert (Z : pend_at p c (cs (f m) c) (pcs (f m) c) (tp (f m) c) r j = Some k)
      by (apply (pend_at_char_s p (f m) c (Inv1_run p _ Rs)); exists d; exact Pr).
    congruence.
  - rewrite <- (proj1 (ins_agree p W c j r r' Ar)). exact Ci.
Qed.

(* one more slot: the place of a pending read, its register the access's *)
Lemma ccJ_succ_pl : forall s c B r J k d, run p s -> ccJ p c (cs s c) (pcs s c) B r J ->
  placed p c (cs s c) (pcs s c) r k d J -> is_load (inst_of d) = true -> r J = rg (cs s c) k ->
  ccJ p c (cs s c) (pcs s c) B r (S J).
Proof.
  intros s c B r J k d R C Pl Ld Rj. pose proof (Inv1_run p s R) as I.
  destruct C as (A0 & A1 & A2 & A3 & A3h & A4 & A5 & A6 & A7).
  assert (Ps : pslot p c (cs s c) (pcs s c) r J) by (left; exists k, d; exact Pl).
  split; [lia|]. split; [exact A1|]. split; [|split; [|split; [|split; [|split; [|split]]]]].
  - intros q L1 L2 X. destruct (Nat.eq_dec q J) as [->|Nq]; [|apply A2; auto; lia].
    exfalso. pose proof Pl as (_ & t & _ & F).
    rewrite (dof_load _ _ _ (first_at_dof _ _ _ _ _ _ _ _ F (load_accd _ Ld))) in X. congruence.
  - intros q k2 d2 L P2 L2. destruct (Nat.eq_dec q J) as [->|Nq]; [|apply (A3 q k2 d2); auto; lia].
    rewrite (placed_unique p c _ _ (oc_inj p s c I) r J k2 k d2 d P2 Pl). exact Rj.
  - intros q k2 m2 xs2 L P2. destruct (Nat.eq_dec q J) as [->|Nq]; [|apply (A3h q k2 m2 xs2); auto; lia].
    exfalso. apply (placed_hplaced p s R c r k d k2 m2 xs2 J Pl P2).
  - intros q x b L1 L2 Bq Np Fb. destruct (Nat.eq_dec q J) as [->|Nq]; [contradiction|apply (A4 q x b); auto; lia].
  - intros q L1 L2 Np Cs Vr. destruct (Nat.eq_dec q J) as [->|Nq]; [contradiction|apply (A5 q); auto; lia].
  - intros q b L1 L2 Np Xl Cs Fx. destruct (Nat.eq_dec q J) as [->|Nq]; [exfalso; apply (Np k d Pl)|apply (A6 q b); auto; lia].
  - intros q L1 L2 Np Ic Xl. destruct (Nat.eq_dec q J) as [->|Nq]; [contradiction|apply (A7 q); auto; lia].
Qed.

(* a pending CAS placed at j under registers that continue the state after its
   step: the replay's verdict from a fix there is its own *)
Lemma fix_whole : forall c k ik d B u r j b, early_at p f n c k ik d B u ->
  ccJ p c (cs (f (S ik)) c) (pcs (f (S ik)) c) (bd (cs (f (S ik)) c)) r j ->
  first_at p c (cs (f (S ik)) c) (pcs (f (S ik)) c) r (tm (f ik)) d j -> pcs (f n) c <= k ->
  is_cas (inst_of d) = true -> fxv c j r = Some b ->
  vok (rg (cs (f (S ik)) c) k) = b && Nat.eqb (vv (rg (cs (f (S ik)) c) k)) (cexp (inst_of d) r).
Proof.
  intros c k ik d B u r j b Ea C Fo Pk Cd Fv.
  pose proof Ea as (Lik & _).
  assert (It : item p f n c k ik (TF d)) by (left; exists d, B, u; auto).
  destruct (early_post p f n c k ik d B u Ea) as (Ok & Ak & _).
  assert (R1 : run p (f (S ik))) by (apply (tr_run p f n T); lia).
  destruct (fxv_spec c j r b Fv) as (m & Lm & F0 & F1 & Ag).
  pose proof (first_at_eof _ _ _ _ _ _ _ _ Fo) as De.
  pose proof (eof_cas_x _ _ _ De Cd) as Xc.
  destruct (fix_facts m c j b r Lm F0 F1 Ag Xc) as (Hj & Pe & Ci & _ & Pn & _ & _ & Rgm). destruct (eof_cexp _ _ _ r De) as (_ & Ce).
  destruct (Nat.le_gt_cases (S m) (S ik)) as [L|L].
  - (* fixed before the access happened *)
    set (r' := fun q => if Nat.eqb q j then rg (cs (f (S ik)) c) k else r q).
    assert (Ar : agree r r' j) by (intros q Lq; unfold r'; rewrite (proj2 (Nat.eqb_neq q j) ltac:(lia)); reflexivity).
    assert (Ld : is_load (inst_of d) = true) by (destruct d; simpl in Cd; try discriminate; reflexivity).
    assert (Pl : placed p c (cs (f (S ik)) c) (pcs (f (S ik)) c) r' k d j).
    { split; [split; [|split]|].
      - pose proof (x_pcs _ _ (tr_ext p f n T (S ik) n ltac:(lia) (le_n _)) c). lia.
      - rewrite Ok. discriminate.
      - exact Ak.
      - exists (tm (f ik)). split; [exact Ok|]. apply (first_at_agree p W c _ _ r r' _ d j Ar Fo). }
    assert (C' : ccJ p c (cs (f (S ik)) c) (pcs (f (S ik)) c) (bd (cs (f (S ik)) c)) r' (S j)).
    { apply (ccJ_succ_pl (f (S ik)) c _ r' j k d R1); [|exact Pl|exact Ld|unfold r'; rewrite Nat.eqb_refl; reflexivity].
      apply (ccJ_agree_r p c _ _ _ r r' j W Ar C). }
    assert (X : is_load (ins p c j r') && icond (ins p c j r') r' = true).
    { pose proof Pl as (_ & t0 & _ & F'). rewrite (dof_load _ _ _ (first_at_dof _ _ _ _ _ _ _ _ F' (load_accd _ Ld))). exact Ld. }
    pose proof (fix_A6 m c j b r (S ik) r' Lm F0 F1 Ag L ltac:(lia) C' Ar X
      ltac:(rewrite <- (proj1 (ins_agree p W c j r r' Ar)); exact Ci)) as V.
    assert (Rj : r' j = rg (cs (f (S ik)) c) k) by (unfold r'; rewrite Nat.eqb_refl; reflexivity).
    rewrite Rj in V. rewrite V. f_equal. f_equal.
    destruct (ins_agree p W c j r r' Ar) as [E1 E2]. rewrite <- E1. rewrite <- (cexp_ieval _ _ _ E2). symmetry. exact Ce.
  - (* fixed after: the access was pending and placed there, which the fix excludes *)
    exfalso.
    assert (Rs : run p (f m)) by (apply (tr_run p f n T); lia).
    assert (Xm : Ext (f (S ik)) (f m)) by (apply (tr_ext p f n T); lia).
    assert (Pkm : pcs (f m) c <= k) by (pose proof (x_pcs _ _ (tr_ext p f n T m n ltac:(lia) (le_n _)) c); lia).
    assert (Agm : agree r (rg (cs (f m) c)) (pcs (f m) c)).
    { intros q Lq. rewrite (Ag q ltac:(lia)). unfold fxreg.
      rewrite (creg_lt_pc p c _ _ _ _ _ q W (pend_ok_of p _ c (Inv1_run p _ (tr_run p f n T (S m) ltac:(lia))))) by (rewrite Pe; exact Lq).
      apply Rgm. exact Lq. }
    assert (Fm : first_at p c (cs (f m) c) (pcs (f m) c) r (tm (f ik)) d j).
    { unfold first_at in *. apply (proj2 (place_trace p f n T W Wc c k ik (TF d) m r j It ltac:(lia) ltac:(lia) Pkm Agm Hj)). exact Fo. }
    assert (Z : pend_at p c (cs (f m) c) (pcs (f m) c) (tp (f m) c) r j = Some k).
    { apply (pend_at_char_s p (f m) c (Inv1_run p _ Rs)). exists d. split; [split; [exact Pkm|split]|].
      - rewrite (x_oc _ _ Xm c k _ Ok). discriminate.
      - rewrite (x_aip _ _ Xm c k ltac:(rewrite Ok; discriminate) Pkm). exact Ak.
      - exists (tm (f ik)). split; [apply (x_oc _ _ Xm c k _ Ok)|exact Fm]. }
    congruence.
Qed.

(* a CAS whose read happened alone, placed at j at a state where no result is
   fixed there: a fix there later, applying to the registers, finds its read
   not failed *)
Lemma fix_half : forall c k ih xs B u i r j b, early_atR p f n c k ih xs B u -> ih <= i -> i < n ->
  hplaced p c (cs (f (S i)) c) (pcs (f (S i)) c) r k Plain xs j -> pcs (f n) c <= k ->
  fx (cs (f (S i)) c) j = None -> fxv c j r = Some b ->
  vok (rg (cs (f (S i)) c) k) = true.
Proof.
  intros c k ih xs B u i r j b Ea L1 L2 Pl Pk Fn Fv.
  assert (It : item p f n c k ih (TH Plain xs)) by (right; exists xs, B, u; auto).
  destruct (fxv_spec c j r b Fv) as (m & Lm & F0 & F1 & Ag).
  assert (Xc : is_cas (ins p c j r) && icond (ins p c j r) r = true)
    by (destruct Pl as (_ & _ & t0 & _ & F0'); exact (eofR_x _ _ _ _ (first_atR_eofR _ _ _ _ _ _ _ _ _ F0'))).
  destruct (fix_facts m c j b r Lm F0 F1 Ag Xc) as (Hj & Pe & _ & _ & _ & Hh & _ & Rgm).
  assert (Lim : S i <= m).
  { destruct (Nat.le_gt_cases (S i) m) as [X|X]; auto. exfalso.
    pose proof (fx_keep (S m) (S i) c j b ltac:(lia) ltac:(lia) F1). congruence. }
  destruct (vok (rg (cs (f (S i)) c) k)) eqn:V; [reflexivity|exfalso].
  pose proof Pl as ((Q1 & Q2 & Q3) & Oc & t & Oh & F).
  assert (Rs : run p (f m)) by (apply (tr_run p f n T); lia).
  assert (Xm : Ext (f (S i)) (f m)) by (apply (tr_ext p f n T); lia).
  pose proof (half_fail_stays p f n T (S i) m c k t Lim ltac:(lia) Oh Oc Q1 V) as Ocm.
  pose proof (half_fail_vok p f n T (S i) m c k t Lim ltac:(lia) Oh Oc Q1 V) as Vm.
  assert (Pkm : pcs (f m) c <= k) by (pose proof (x_pcs _ _ (tr_ext p f n T m n ltac:(lia) (le_n _)) c); lia).
  assert (Agm : agree r (rg (cs (f m) c)) (pcs (f m) c)).
  { intros q Lq. rewrite (Ag q ltac:(lia)). unfold fxreg.
    rewrite (creg_lt_pc p c _ _ _ _ _ q W (pend_ok_of p _ c (Inv1_run p _ (tr_run p f n T (S m) ltac:(lia))))) by (rewrite Pe; exact Lq).
    apply Rgm. exact Lq. }
  destruct (early_postR p f n c k ih xs B u Ea) as (Oh1 & _).
  assert (Et : t = tm (f ih)).
  { pose proof (x_oh _ _ (tr_ext p f n T (S ih) (S i) ltac:(lia) ltac:(lia)) c k _ Oh1) as Z. rewrite Oh in Z. injection Z as ->. reflexivity. }
  subst t.
  assert (Fm : first_atR p c (cs (f m) c) (pcs (f m) c) r (tm (f ih)) Plain xs j).
  { unfold first_atR in *.
    assert (Ag1 : agree r (rg (cs (f (S i)) c)) (pcs (f (S i)) c)).
    { intros q Lq. rewrite (Agm q ltac:(pose proof (x_pcs _ _ Xm c); lia)). apply (x_rg _ _ Xm). left. exact Lq. }
    pose proof (proj1 (place_trace p f n T W Wc c k ih (TH Plain xs) (S i) r j It ltac:(lia) ltac:(lia) Q1 Ag1
                  (first_atR_le _ _ _ _ _ _ _ _ _ F)) F) as Fi.
    apply (proj2 (place_trace p f n T W Wc c k ih (TH Plain xs) m r j It ltac:(lia) ltac:(lia) Pkm Agm Hj)). exact Fi. }
  assert (Z : hpend_at p c (cs (f m) c) (pcs (f m) c) (tp (f m) c) r j = Some k).
  { apply (hpend_at_char_s p (f m) c (Inv1_run p _ Rs)). exists Plain, xs.
    split; [split; [exact Pkm|split]|].
    - rewrite (x_oh _ _ Xm c k _ Oh). discriminate.
    - rewrite (x_cash _ _ Xm c k ltac:(rewrite Oh; discriminate) Pkm). exact Q3.
    - split; [exact Ocm|]. exists (tm (f ih)). split; [apply (x_oh _ _ Xm c k _ Oh)|exact Fm]. }
  destruct (Hh k Z) as (Vt & _). congruence.
Qed.

End FT.
