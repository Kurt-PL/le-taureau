(* Write-back (spec 0.1 §8.6) over model M2DQ (stepQ).  As M2WB (the write-back layer on A), with
   every step of A read as a step of M2DQ: stepWB = M2DQ's step plus the write-back alternatives.
   A write-back store is an entry (t, true) of its cells' histories; every other entry has the flag
   false.  Placement and the store itself (wbst, wbok, early_okWB) are those of M2WB / M2DQWBPatch.

   Main results: every finished runWB has a finished runQ with the same registers and the same
   final storage (WB_sim), and every runQ is a runWB (Q_in_WB).  The simulation of M2DQ's two
   record-fix steps (q_rfix, q_sfix) is new here; the steps of M2Model are simulated by
   M2DQWBStep.sim_step (M2WBStep with the image run a runQ). *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Cont M2DA M2DP M2DQ M2WBReg M2WBRel M2WBEff M2WBSim M2DQWBStep M2DQWBPatch.
Require M2DQShim.

(* a step that leaves the histories as they are *)
Definition nowrite (s s' : st) : Prop := forall x, hs s' x = hs s x.

(* the context passes, in this step, the CAS at slot k whose read half (time t1) happened and
   whose result is a failure *)
Definition partskip (s s' : st) (c k t1 : nat) : Prop :=
  nowrite s s' /\ tm s' = tm s /\ pcs s c = k /\ pcs s' c = S k /\ oc (cs s c) k = None /\
  oh (cs s c) k = Some t1 /\ oh (cs s' c) k = Some t1 /\ is_cas (ai (cs s' c) k) = true /\
  vok (rg (cs s' c) k) = false.

(* an early write-back needs no operand (spec 0.1 §2.3.4 store-part condition, spec 0.1 §8.6) *)
Definition early_okWB (p : prog) (c : nat) (cc : cst) (pc N T T1 : nat) (xs : list cell) : Prop :=
  forall f, let r := creg p c cc pc N (bor (bd cc) (fun _ => false)) f in
    exists j ev nv, pc < j /\ first_atR p c cc pc r T1 Plain xs j /\ eof (ins p c j r) r = Some (DCas Plain xs ev nv) /\
      forall j', pc <= j' -> j' < j -> executes (ins p c j' r) r = true ->
        (forall v, htakenv p c cc pc r T j' v -> cfailv (ins p c j' r) r v = false) ->
        tied (ins p c j' r) (inst_of (DCas Plain xs ev nv)) -> taken p c cc pc r T j'.

Lemma early_okW_WB : forall p c cc pc N T T1 xs ev nv,
  early_okW p c cc pc N T T1 Plain xs (DCas Plain xs ev nv) (fun _ => false) -> early_okWB p c cc pc N T T1 xs.
Proof.
  intros p c cc pc N T T1 xs ev nv H f. specialize (H f). cbv zeta in H |- *.
  destruct H as (j & L & F & D & T'). exists j, ev, nv. auto.
Qed.

Inductive stepWB (p : prog) : st -> st -> Prop :=
(* a step of M2DQ (a write is not placed between a write-back store and the write it follows) *)
| wbA : forall s s', stepQ p s s' -> fhsafe s s' -> stepWB p s s'
(* a CAS fails in parts: when the context passes it, it also stores the value its load took *)
| wbP : forall s s' c k t1 H'', stepQ p s s' -> partskip s s' c k t1 -> (forall x, ~ In t1 (ids (hs s x))) ->
    wbok s' c k t1 H'' -> stepWB p s (wbst s' c k t1 H'')
(* the store part of a CAS that fails in parts happens early *)
| wbE : forall s c k t1 xs H'', pcs s c < k -> oc (cs s c) k = None -> oh (cs s c) k = Some t1 ->
    ai (cs s c) k = crd Plain xs -> vok (rg (cs s c) k) = false ->
    early_okWB p c (cs s c) (pcs s c) (tp s c) (tm s) t1 xs ->
    (forall x, ~ In t1 (ids (hs s x))) -> wbok s c k t1 H'' -> stepWB p s (wbst s c k t1 H'').

Inductive runWB (p : prog) : st -> Prop :=
| wr0 : runWB p sinit
| wrS : forall s s', runWB p s -> stepWB p s s' -> runWB p s'.

(* ---------- every runQ is a runWB ---------- *)
Definition flagsF (s : st) : Prop := forall x w b, In (w, b) (hs s x) -> b = false.

Lemma eff_flagsF : forall t i r m m' a K u w, eff t i r m m' a K u w ->
  (forall x w0 b, In (w0, b) (mH m x) -> b = false) -> forall x w0 b, In (w0, b) (mH m' x) -> b = false.
Proof.
  intros t i r m m' a K u w H F. inversion H; subst; auto.
  - intros x w0 b I. cbn [mH wput] in I. destruct (places_cell _ _ _ _ x H1) as [E|(h1 & h2 & E1 & E2)].
    + rewrite E in I. exact (F x w0 b I).
    + rewrite E2 in I. apply in_app_iff in I. destruct I as [I|[I|I]].
      * apply (F x w0 b). rewrite E1. apply in_app_iff. left. exact I.
      * injection I as _ <-. reflexivity.
      * apply (F x w0 b). rewrite E1. apply in_app_iff. right. exact I.
  - intros x w0 b I. cbn [mH wput] in I. destruct (places_cell _ _ _ _ x H3) as [E|(h1 & h2 & E1 & E2)].
    + rewrite E in I. exact (F x w0 b I).
    + rewrite E2 in I. apply in_app_iff in I. destruct I as [I|[I|I]].
      * apply (F x w0 b). rewrite E1. apply in_app_iff. left. exact I.
      * injection I as _ <-. reflexivity.
      * apply (F x w0 b). rewrite E1. apply in_app_iff. right. exact I.
Qed.

Lemma step_flagsF : forall p s s', step p s s' -> flagsF s -> flagsF s'.
Proof.
  intros p s s' H F. inversion H; subst; cbv zeta in *; unfold flagsF in *; cbn [hs].
  all: first [exact F | (destruct o as [k0|]; [destruct b|]; exact F) | (intros x w0 b0 I; refine (eff_flagsF _ _ _ (mof s c) _ _ _ _ _ ?[He] F x w0 b0 I); eassumption)].
Qed.

Lemma stepQ_flagsF : forall p s s', stepQ p s s' -> flagsF s -> flagsF s'.
Proof.
  intros p s s' H F. destruct H as [s s' St _|s c k B _ _|s c j k B _ _ _].
  - exact (step_flagsF p s s' St F).
  - exact F.
  - exact F.
Qed.

Lemma runQ_flagsF : forall p s, runQ p s -> flagsF s.
Proof.
  intros p s R. induction R as [|s s' R IH St].
  - intros x w b I. destruct I.
  - exact (stepQ_flagsF p s s' St IH).
Qed.

Lemma flagsF_fhsafe : forall s s', flagsF s -> fhsafe s s'.
Proof.
  intros s s' F x h1 h2 E1 E2 w g h' E3. apply (F x w g). rewrite E1, E3. apply in_app_iff. right. left. reflexivity.
Qed.

Theorem Q_in_WB : forall p s, runQ p s -> runWB p s.
Proof.
  intros p s R. induction R as [|s s' R IH St].
  - constructor.
  - eapply wrS; [exact IH|]. apply wbA; [exact St|]. apply flagsF_fhsafe. exact (runQ_flagsF p s R).
Qed.

(* ---------- M2DQ's record-fix premises carry over to a context state with other rv (pointwise
   equal), rw and views ---------- *)
Section X.
Variables (p : prog) (W : wf p) (c : nat) (cc : cst) (pc N : nat) (PO : pend_ok cc pc).
Variables (rv' : nat -> cell -> val) (rw' : nat -> cell -> option nat) (P A R O Og : view).
Hypothesis Hrv : forall j x, rv' j x = rv cc j x.

Lemma rclaim_x : forall B f k j,
  rclaim p c cc pc N (creg p c cc pc N B f) k j ->
  rclaim p c (cc_x cc rv' rw' P A R O Og) pc N (creg p c (cc_x cc rv' rw' P A R O Og) pc N B f) k j.
Proof.
  intros B f k j (C0 & C1 & C2 & C3 & C4 & C5).
  set (rW := creg p c cc pc N B f) in *. set (rA := creg p c (cc_x cc rv' rw' P A R O Og) pc N B f).
  assert (Aj : agree rW rA j) by apply (agX p c cc pc N rv' rw' P A R O Og Hrv).
  destruct (ins_agree p W c j rW rA Aj) as [Ei Ev].
  assert (Ic : icond (ins p c j rW) rA = icond (ins p c j rW) rW) by (unfold icond; rewrite Ev; reflexivity).
  unfold rclaim. rewrite <- Ei. refine (conj C0 (conj _ (conj _ (conj C3 (conj _ C5))))).
  - rewrite hpend_at_x. rewrite <- C1. symmetry. apply (hpend_at_agree p W c cc pc N rW rA j PO Aj).
  - rewrite pend_at_x. rewrite <- C2. symmetry. apply (pend_at_agree p W c cc pc N rW rA j PO Aj).
  - rewrite Ic. exact C4.
Qed.

Lemma rfail_ok_x : forall k B, rfail_ok p c cc pc N k B -> rfail_ok p c (cc_x cc rv' rw' P A R O Og) pc N k B.
Proof.
  intros k B (O1 & O2 & O3 & v & H). refine (conj O1 (conj O2 (conj O3 _))). exists v. intros f.
  specialize (H f). cbv zeta in H |- *. cbn [bd cc_x]. destruct H as (j & Cl & V). exists j. split.
  - exact (rclaim_x (bor (bd cc) B) f k j Cl).
  - rewrite (creg_x rv' rw' P A R O Og cc Hrv). exact V.
Qed.

Lemma sfix_ok_x : forall j k B, sfix_ok p c cc pc N j k B -> sfix_ok p c (cc_x cc rv' rw' P A R O Og) pc N j k B.
Proof.
  intros j k B (O1 & O2 & O3 & H). refine (conj O1 (conj O2 (conj O3 _))). intros f.
  specialize (H f). cbv zeta in H |- *. cbn [bd cc_x fx].
  set (rW := creg p c cc pc N (bor (bd cc) B) f) in *.
  set (rA := creg p c (cc_x cc rv' rw' P A R O Og) pc N (bor (bd cc) B) f).
  destruct H as (jf & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7). exists jf.
  assert (Aj : forall i, agree rW rA i) by (intros i; apply (agX p c cc pc N rv' rw' P A R O Og Hrv)).
  assert (Ej : rW jf = rA jf) by (symmetry; apply (creg_x rv' rw' P A R O Og cc Hrv)).
  destruct (ins_agree p W c jf rW rA (Aj jf)) as [Ei Ev].
  destruct (ins_agree p W c j rW rA (Aj j)) as [Ei' Ev'].
  assert (Ic : icond (ins p c jf rW) rA = icond (ins p c jf rW) rW) by (unfold icond; rewrite Ev; reflexivity).
  assert (Ic' : icond (ins p c j rW) rA = icond (ins p c j rW) rW) by (unfold icond; rewrite Ev'; reflexivity).
  assert (Ce : cexp (ins p c jf rW) rA = cexp (ins p c jf rW) rW) by (symmetry; apply cexp_ieval; exact Ev).
  rewrite <- Ei, <- Ei'. rewrite Ic, Ic', Ce.
  refine (conj C0 (conj _ (conj _ (conj C3 (conj C4 (conj _ (conj C6 C7))))))).
  - rewrite hpend_at_x. rewrite <- C1. symmetry. apply (hpend_at_agree p W c cc pc N rW rA jf PO (Aj jf)).
  - rewrite pend_at_x. rewrite <- C2. symmetry. apply (pend_at_agree p W c cc pc N rW rA jf PO (Aj jf)).
  - rewrite <- Ej. exact C5.
Qed.
End X.

(* the back direction for the negated premise of q_rfix: a context state is cc_x of its image *)
Lemma cc_x_back : forall cW rv' rw' P A R O Og,
  cc_x (cc_x cW rv' rw' P A R O Og) (rv cW) (rw cW) (vP cW) (vA cW) (vR cW) (vO cW) (vOg cW) = cW.
Proof. intros cW rv' rw' P A R O Og. destruct cW. reflexivity. Qed.

(* ---------- the relation through the record-fix steps ---------- *)
Definition rfixc (cc : cst) (k : nat) (B : nat -> bool) : cst :=
  mkC (oc cc) (upd (rg cc) k (vd false (vv (rg cc k)))) (ai cc) (rw cc) (rv cc) (bor (bd cc) B)
      (vP cc) (vA cc) (vR cc) (vO cc) (vOg cc) (oh cc) (fx cc).

Lemma cs_rfix : forall s c k B c', cs (sbd (scfail s c k) c B) c' = if Nat.eqb c' c then rfixc (cs s c) k B else cs s c'.
Proof.
  intros s c k B c'. destruct (Nat.eqb c' c) eqn:E.
  - apply Nat.eqb_eq in E. subst c'. unfold sbd, scfail, rfixc, cc_fx, upd. cbn. rewrite !Nat.eqb_refl. reflexivity.
  - unfold sbd, scfail, upd. cbn. rewrite E. reflexivity.
Qed.

Lemma crel_rfix : forall sw ccW ccA k B, crel sw ccW ccA -> crel sw (rfixc ccW k B) (rfixc ccA k B).
Proof.
  intros sw ccW ccA k B ((rv' & rw' & P & A & R & O & Og & E) & Hv & Hw).
  assert (Hrv : forall j x, rv' j x = rv ccW j x) by (intros j0 x; specialize (Hv j0 x); rewrite E in Hv; exact Hv).
  assert (Hrw : forall j x, rw' j x = pi sw x (rw ccW j x)) by (intros j0 x; specialize (Hw j0 x); rewrite E in Hw; exact Hw).
  subst ccA. unfold rfixc.
  split; [|split]; [do 7 eexists; reflexivity|intros k0 x; cbn; apply Hrv|intros k0 x; cbn; apply Hrw].
Qed.

Lemma rel_rfix : forall sw sW sA c k B, rel sw sW sA -> rel sw (sbd (scfail sW c k) c B) (sbd (scfail sA c k) c B).
Proof.
  intros sw sW sA c k B R. apply (rel_nomem2 sw sW sA R); try reflexivity.
  - exact (r_pcs sw sW sA R).
  - exact (r_tp sw sW sA R).
  - exact (r_cm sw sW sA R).
  - intros c'. rewrite !cs_rfix. destruct (Nat.eqb c' c); [apply crel_rfix|]; apply (r_cr sw sW sA R).
  - intros c' k0 x w E. rewrite cs_rfix in E. destruct (Nat.eqb c' c); [|apply (i_rw sw sW sA R c' k0 x w E)].
    apply (i_rw sw sW sA R c k0 x w E).
  - intros c' k0 t0 E. rewrite cs_rfix in E. destruct (Nat.eqb c' c); [|apply (i_oh sw sW sA R c' k0 t0 E)].
    apply (i_oh sw sW sA R c k0 t0 E).
Qed.

(* the fields a step reads of a context are those of the image *)
Lemma rel_cc : forall sw sW sA, rel sw sW sA -> forall c,
  oc (cs sA c) = oc (cs sW c) /\ oh (cs sA c) = oh (cs sW c) /\ rg (cs sA c) = rg (cs sW c) /\
  ai (cs sA c) = ai (cs sW c) /\ bd (cs sA c) = bd (cs sW c) /\ fx (cs sA c) = fx (cs sW c).
Proof.
  intros sw sW sA R c. destruct (r_cr sw sW sA R c) as ((rv' & rw' & P & A & R' & O & Og & E) & _).
  rewrite E. cbn. auto 7.
Qed.

Lemma nowhole_rel : forall sw sW sA sw' sW' sA', rel sw sW sA -> rel sw' sW' sA' -> nowhole sW sW' -> nowhole sA sA'.
Proof.
  intros sw sW sA sw' sW' sA' R R' V c k O O' C.
  destruct (rel_cc sw sW sA R c) as (E1 & E2 & _). destruct (rel_cc sw' sW' sA' R' c) as (E1' & _ & _ & E4' & _).
  rewrite E1 in O. rewrite E1' in O'. rewrite E4' in C. rewrite E2. exact (V c k O O' C).
Qed.

Section Sim.
Variables (p : prog) (W : wf p).

(* the record fixes of a state are record fixes of its image *)
Lemma simQ_rfix : forall sw s sA c k B, runQ p sA -> rel sw s sA ->
  rfail_ok p c (cs s c) (pcs s c) (tp s c) k B ->
  (forall j, pcs s c <= j -> fx (cs s c) j = None -> ~ cfix_ok p c (cs s c) (pcs s c) (tp s c) j false B (Some k)) ->
  stepQ p sA (sbd (scfail sA c k) c B).
Proof.
  intros sw s sA c k B RA R Rf Nc. pose proof (M2DQShim.Inv1_run p sA RA) as I1.
  destruct (r_cr sw s sA R c) as ((rv' & rw' & P & A & R' & O & Og & E) & Hv & _).
  assert (Hrv : forall j x, rv' j x = rv (cs s c) j x) by (intros j0 x; specialize (Hv j0 x); rewrite E in Hv; exact Hv).
  pose proof (pend_ok_of p sA c I1) as POA. rewrite E, (r_pcs sw s sA R) in POA.
  assert (POW : pend_ok (cs s c) (pcs s c)) by (destruct (cs s c); exact POA).
  apply q_rfix.
  - rewrite E, (r_pcs sw s sA R), (r_tp sw s sA R).
    exact (rfail_ok_x p W c (cs s c) (pcs s c) (tp s c) POW rv' rw' P A R' O Og Hrv k B Rf).
  - intros j Lj Fj Cf. rewrite E, (r_pcs sw s sA R), (r_tp sw s sA R) in *. apply (Nc j Lj Fj).
    rewrite <- (cc_x_back (cs s c) rv' rw' P A R' O Og).
    apply (cfix_ok_x p c _ (pcs s c) (tp s c) j false B (Some k) (rv (cs s c)) (rw (cs s c)) (vP (cs s c)) (vA (cs s c))
             (vR (cs s c)) (vO (cs s c)) (vOg (cs s c)) W POA); [|exact Cf].
    intros j0 x. symmetry. exact (Hrv j0 x).
Qed.

Lemma simQ_sfix : forall sw s sA c j k B, runQ p sA -> rel sw s sA ->
  pcs s c <= j -> fx (cs s c) j = None -> sfix_ok p c (cs s c) (pcs s c) (tp s c) j k B ->
  stepQ p sA (scfix0 sA c j true B).
Proof.
  intros sw s sA c j k B RA R Lj Fj Sf. pose proof (M2DQShim.Inv1_run p sA RA) as I1.
  destruct (r_cr sw s sA R c) as ((rv' & rw' & P & A & R' & O & Og & E) & Hv & _).
  assert (Hrv : forall j x, rv' j x = rv (cs s c) j x) by (intros j0 x; specialize (Hv j0 x); rewrite E in Hv; exact Hv).
  pose proof (pend_ok_of p sA c I1) as POA. rewrite E, (r_pcs sw s sA R) in POA.
  assert (POW : pend_ok (cs s c) (pcs s c)) by (destruct (cs s c); exact POA).
  apply (q_sfix p sA c j k B); rewrite ?E, ?(r_pcs sw s sA R), ?(r_tp sw s sA R); [exact Lj|exact Fj|].
  exact (sfix_ok_x p W c (cs s c) (pcs s c) (tp s c) POW rv' rw' P A R' O Og Hrv j k B Sf).
Qed.

(* a step of M2DQ is simulated by a step of M2DQ *)
Theorem sim_stepQ : forall sw sW sA s', runQ p sA -> rel sw sW sA -> stepQ p sW s' -> fhsafe sW s' ->
  exists sA', stepQ p sA sA' /\ rel sw s' sA'.
Proof.
  intros sw sW sA s' RA R H FH.
  destruct H as [s s' St V|s c k B Rf Nc|s c j k B Lj Fj Sf].
  - destruct (sim_step p W sw s sA RA R s' St FH) as (sA' & St' & R').
    exists sA'. split; [apply q_old; [exact St'|exact (nowhole_rel sw s sA sw s' sA' R R' V)]|exact R'].
  - exists (sbd (scfail sA c k) c B). split; [exact (simQ_rfix sw s sA c k B RA R Rf Nc)|exact (rel_rfix sw s sA c k B R)].
  - exists (scfix0 sA c j true B). split; [exact (simQ_sfix sw s sA c j k B RA R Lj Fj Sf)|exact (rel_cfix sw s sA R c None j true B)].
Qed.

Lemma nowrite_fhsafe : forall s s', nowrite s s' -> fhsafe s s'.
Proof.
  intros s s' N x h1 h2 E1 E2. exfalso. pose proof (N x) as E. rewrite E2, E1 in E.
  apply (f_equal (@length (nat * bool))) in E. rewrite !length_app in E. simpl in E. lia.
Qed.

Lemma sim_wb : forall sw sW sA sW', runQ p sA -> rel sw sW sA -> stepWB p sW sW' ->
  exists sA' sw', (sA' = sA \/ stepQ p sA sA') /\ rel sw' sW' sA'.
Proof.
  intros sw sW sA sW' RA R H.
  destruct H as [s0 s1 St FHs | s0 s1 c k t1 H'' St Ps Fr Ok | s0 c k t1 xs H'' _ _ Oh _ _ _ Fr Ok].
  - destruct (sim_stepQ sw s0 sA s1 RA R St FHs) as (sA' & St' & R'). exists sA', sw. auto.
  - destruct Ps as (NW & T1 & _ & _ & _ & _ & Oh' & _). destruct (sim_stepQ sw s0 sA s1 RA R St (nowrite_fhsafe _ _ NW)) as (sA' & St' & R').
    exists sA'. eexists. split; [right; exact St'|].
    apply (rel_wb sw s1 sA' c k t1 H'' R').
    + exact (i_oh sw s1 sA' R' c k t1 Oh').
    + intros x I. apply (Fr x). rewrite <- (NW x). exact I.
    + exact Ok.
  - exists sA. eexists. split.
    + left. reflexivity.
    + apply (rel_wb sw s0 sA c k t1 H'' R).
      * exact (i_oh sw s0 sA R c k t1 Oh).
      * exact Fr.
      * exact Ok.
Qed.

Theorem runWB_sim : forall s, runWB p s -> exists sw sA, runQ p sA /\ rel sw s sA.
Proof.
  intros s R. induction R as [|s s' R IH St].
  - exists sw0, sinit. split; [constructor|exact rel_init].
  - destruct IH as (sw & sA & RA & Rl). destruct (sim_wb sw s sA s' RA Rl St) as (sA' & sw' & St' & Rl').
    exists sw', sA'. split; [destruct St' as [->|St']; [exact RA|econstructor; eauto]|exact Rl'].
Qed.

Theorem final_rel : forall sw sW sA, rel sw sW sA -> forall x, final sA x = final sW x.
Proof.
  intros sw sW sA R x. rewrite !final_lastv. unfold final_at.
  rewrite (lastv_hers (fun w => wv sW w x) (fun w => wv sA w x) (hs sW x) 0 (r_adj sw sW sA R x)).
  - rewrite (r_hs sw sW sA R x). reflexivity.
  - intros w I. destruct (r_kept sw sW sA R x w I) as [_ E]. symmetry. exact E.
Qed.

(* every finished write-back run of M2DQ has a finished run of M2DQ with the same registers and the
   same final storage *)
Theorem WB_sim : forall s, runWB p s -> done p s ->
  exists sA, runQ p sA /\ done p sA /\ (forall c k, rg (cs sA c) k = rg (cs s c) k) /\ (forall x, final sA x = final s x).
Proof.
  intros s R D. destruct (runWB_sim s R) as (sw & sA & RA & Rl). exists sA. split; [exact RA|].
  assert (Cc : forall c, oc (cs sA c) = oc (cs s c) /\ oh (cs sA c) = oh (cs s c) /\ rg (cs sA c) = rg (cs s c)).
  { intros c. destruct (rel_cc sw s sA Rl c) as (E1 & E2 & E3 & _). auto. }
  split; [|split].
  - destruct D as (n & F & Cp). exists n. split; [exact F|]. intros c Hc. destruct (Cp c Hc) as [L K]. rewrite (r_pcs sw s sA Rl).
    split; [exact L|]. intros k Hk. destruct (Cc c) as (E1 & E2 & _). rewrite E1, E2. exact (K k Hk).
  - intros c k. destruct (Cc c) as (_ & _ & E). rewrite E. reflexivity.
  - exact (final_rel sw s sA Rl).
Qed.
End Sim.
