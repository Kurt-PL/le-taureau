(* Write-back (spec 0.1 §8.6), part 1: a context state that differs from another only in its
   value holders rv (pointwise equal), rw and its views is the same to R1.
   cc_x replaces rv, rw and the knowledge sets; every premise of A's step that R1
   builds is transferred to it (rv through cellv, hence creg, pointwise). *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2Oota M2Cont.

Definition cc_x (cc : cst) (rv' : nat -> cell -> val) (rw' : nat -> cell -> option nat) (P A R O Og : view) : cst :=
  mkC (oc cc) (rg cc) (ai cc) rw' rv' (bd cc) P A R O Og (oh cc) (fx cc).

Section X.
Variables (rv' : nat -> cell -> val) (rw' : nat -> cell -> option nat) (P A R O Og : view).

Lemma fab_x : forall p c cc pc N r n, fab p c (cc_x cc rv' rw' P A R O Og) pc N r n = fab p c cc pc N r n.
Proof. intros p c cc pc N r n. induction n as [|n IH]; [reflexivity|]. cbn [fab]. rewrite IH. reflexivity. Qed.

Lemma plc_x : forall p c cc pc r n, plc p c (cc_x cc rv' rw' P A R O Og) pc r n = plc p c cc pc r n.
Proof. intros p c cc pc r n. induction n as [|n IH]; [reflexivity|]. cbn [plc]. rewrite IH. reflexivity. Qed.

Lemma pend_at_x : forall p c cc pc N r j, pend_at p c (cc_x cc rv' rw' P A R O Og) pc N r j = pend_at p c cc pc N r j.
Proof.
  intros. unfold pend_at, first_atb. apply find_ext_in. intros k _. cbn [oc ai cc_x].
  destruct (oc cc k); [|reflexivity]. destruct (eof (ai cc k) r); [|reflexivity]. rewrite fab_x. reflexivity.
Qed.

Lemma hpend_at_x : forall p c cc pc N r j, hpend_at p c (cc_x cc rv' rw' P A R O Og) pc N r j = hpend_at p c cc pc N r j.
Proof.
  intros. unfold hpend_at. apply find_ext_in. intros k _. cbn [oc oh ai cc_x].
  destruct (oc cc k); [reflexivity|]. destruct (oh cc k); [|reflexivity]. destruct (casx (ai cc k)) as [[m xs]|]; [|reflexivity].
  rewrite fab_x. reflexivity.
Qed.

Lemma cellv_x : forall cc, (forall j x, rv' j x = rv cc j x) -> forall p c pc N B f r n j x,
  cellv p c (cc_x cc rv' rw' P A R O Og) pc N B f r n j x = cellv p c cc pc N B f r n j x.
Proof.
  intros cc Hrv p c pc N B f r n. induction n as [|n IH]; intros j x; cbn [cellv];
    rewrite ?pend_at_x, ?hpend_at_x; (destruct (Nat.ltb j pc); [cbn [rv cc_x]; apply Hrv|]);
    (destruct (_ && _); [|reflexivity]); (destruct (pend_at _ _ _ _ _ _ _); [cbn [rv cc_x]; apply Hrv|]);
    (destruct (hpend_at _ _ _ _ _ _ _); [cbn [rv cc_x]; apply Hrv|]); [reflexivity|].
  destruct (B j); [|reflexivity]. destruct (fbinder p c r j x) as [b|]; [|reflexivity]. rewrite IH. reflexivity.
Qed.

Lemma slotv_x : forall cc, (forall j x, rv' j x = rv cc j x) -> forall p c pc N B f r j,
  slotv p c (cc_x cc rv' rw' P A R O Og) pc N B f r j = slotv p c cc pc N B f r j.
Proof.
  intros cc Hrv p c pc N B f r j. unfold slotv. cbn [rg fx cc_x]. rewrite ?pend_at_x, ?hpend_at_x.
  destruct (Nat.ltb j pc); [reflexivity|]. destruct (_ && _); [|reflexivity].
  destruct (pend_at _ _ _ _ _ _ _); [reflexivity|]. unfold cfx. cbn [fx cc_x].
  destruct (hpend_at _ _ _ _ _ _ _); [reflexivity|].
  cbv zeta. erewrite map_ext; [reflexivity|]. intros x. apply cellv_x. exact Hrv.
Qed.

Lemma bl_x : forall cc, (forall j x, rv' j x = rv cc j x) -> forall p c pc N B f n,
  bl p c (cc_x cc rv' rw' P A R O Og) pc N B f n = bl p c cc pc N B f n.
Proof.
  intros cc Hrv p c pc N B f n. induction n as [|n IH]; [reflexivity|]. cbn [bl]. rewrite IH. f_equal. f_equal.
  apply slotv_x. exact Hrv.
Qed.

Lemma creg_x : forall cc, (forall j x, rv' j x = rv cc j x) -> forall p c pc N B f j,
  creg p c (cc_x cc rv' rw' P A R O Og) pc N B f j = creg p c cc pc N B f j.
Proof. intros cc Hrv p c pc N B f j. unfold creg. rewrite bl_x; [reflexivity|exact Hrv]. Qed.

End X.

Section Tr.
Variables (p : prog) (W : wf p) (c : nat) (cc : cst) (pc N : nat) (PO : pend_ok cc pc).
Variables (rv' : nat -> cell -> val) (rw' : nat -> cell -> option nat) (P A R O Og : view).
Variable pi : cell -> option nat -> option nat.
Hypothesis Hrv : forall j x, rv' j x = rv cc j x.
Hypothesis Hrw : forall k x, rw' k x = pi x (rw cc k x).
Let X := cc_x cc rv' rw' P A R O Og.

Lemma agX : forall B f j, agree (creg p c cc pc N B f) (creg p c X pc N B f) j.
Proof. intros B f j i _. symmetry. apply (creg_x rv' rw' P A R O Og cc Hrv). Qed.
Lemma agX' : forall B f j, agree (creg p c X pc N B f) (creg p c cc pc N B f) j.
Proof. intros B f j i _. apply (creg_x rv' rw' P A R O Og cc Hrv). Qed.

Lemma lead_X : forall r b, lead p c X pc N r b = lead p c cc pc N r b.
Proof. intros. unfold lead, X. rewrite pend_at_x, hpend_at_x. reflexivity. Qed.

Lemma first_at_X : forall r T d j, first_at p c X pc r T d j <-> first_at p c cc pc r T d j.
Proof. intros. unfold first_at, X. rewrite plc_x. tauto. Qed.
Lemma first_atR_X : forall r T m xs j, first_atR p c X pc r T m xs j <-> first_atR p c cc pc r T m xs j.
Proof. intros. unfold first_atR, X. rewrite plc_x. tauto. Qed.

Lemma early_ok_x : forall T d u uA B, (forall x, uA x = pi x (u x)) ->
  early_ok p c cc pc N T d u B -> early_ok p c X pc N T d uA B.
Proof.
  intros T d u uA B Hu E f. specialize (E f). cbv zeta in E |- *. cbn [bd X cc_x]. cbn [bd] in E.
  destruct E as (j & L & Fj & Bd). exists j. split; [exact L|]. split.
  - apply first_at_X. exact (first_at_agree p W c cc pc _ _ T d j (agX _ _ j) Fj).
  - intros Ld x b Ix Bj Fb.
    rewrite <- (fbinder_agree p W c _ _ j x (agX _ _ j)) in Fb.
    destruct (Bd Ld x b Ix Bj Fb) as (k & Lk & Ex). exists k. split.
    + rewrite lead_X. rewrite <- Lk. symmetry. apply (lead_agree p c cc pc N _ _ b W PO).
      intros i Li. apply (agX _ _ b i Li).
    + rewrite Hu, Ex. cbn [X cc_x rw]. rewrite Hrw. reflexivity.
Qed.

Lemma early_okR_x : forall T m xs u uA B, (forall x, uA x = pi x (u x)) ->
  early_okR p c cc pc N T m xs u B -> early_okR p c X pc N T m xs uA B.
Proof.
  intros T m xs u uA B Hu E f. specialize (E f). cbv zeta in E |- *. cbn [bd X cc_x]. cbn [bd] in E.
  destruct E as (j & Fj & Bd). exists j. split.
  - apply first_atR_X. unfold first_atR in *. exact (plc_agree p W c cc pc (S T) _ _ T (TH m xs) j (agX _ _ j) Fj).
  - intros x b Ix Bj Fb.
    rewrite <- (fbinder_agree p W c _ _ j x (agX _ _ j)) in Fb.
    destruct (Bd x b Ix Bj Fb) as (k & Lk & Ex). exists k. split.
    + rewrite lead_X. rewrite <- Lk. symmetry. apply (lead_agree p c cc pc N _ _ b W PO).
      intros i Li. apply (agX _ _ b i Li).
    + rewrite Hu, Ex. cbn [X cc_x rw]. rewrite Hrw. reflexivity.
Qed.

End Tr.

Lemma taken_agree : forall p c cc pc r r' T j, wf p -> agree r r' j -> taken p c cc pc r T j -> taken p c cc pc r' T j.
Proof.
  intros p c cc pc r r' T j W A (k & t & d & P & O & L & F). exists k, t, d. split; [exact P|]. split; [exact O|]. split; [exact L|].
  exact (first_at_agree p W c cc pc r r' t d j A F).
Qed.

Lemma htakenv_agree : forall p c cc pc r r' T j v, wf p -> agree r r' (S j) -> htakenv p c cc pc r T j v -> htakenv p c cc pc r' T j v.
Proof.
  intros p c cc pc r r' T j v W A (k & t & m & xs & P & O & L & Hl & F & E). exists k, t, m, xs. split; [exact P|]. split; [exact O|]. split; [exact L|]. split; [exact Hl|]. split.
  - unfold first_atR in *. exact (plc_agree p W c cc pc (S t) r r' t (TH m xs) j (agree_le r r' (S j) j A (Nat.le_succ_diag_r j)) F).
  - rewrite E. apply A. lia.
Qed.

Section Tr2.
Variables (p : prog) (W : wf p) (c : nat) (cc : cst) (pc N : nat) (PO : pend_ok cc pc).
Variables (rv' : nat -> cell -> val) (rw' : nat -> cell -> option nat) (P A R O Og : view).
Hypothesis Hrv : forall j x, rv' j x = rv cc j x.
Let X := cc_x cc rv' rw' P A R O Og.

Lemma taken_X : forall r T j, taken p c X pc r T j <-> taken p c cc pc r T j.
Proof.
  intros r T j. split; intros (k & t & d & P1 & O1 & L1 & F); exists k, t, d; refine (conj P1 (conj O1 (conj L1 _)));
    apply (first_at_X p c cc pc rv' rw' P A R O Og); exact F.
Qed.

Lemma htakenv_X : forall r T j v, htakenv p c X pc r T j v <-> htakenv p c cc pc r T j v.
Proof.
  intros r T j v. split; intros (k & t & m & xs & P1 & O1 & L1 & Hl & F & E); exists k, t, m, xs;
    refine (conj P1 (conj O1 (conj L1 (conj Hl (conj _ E))))); apply (first_atR_X p c cc pc rv' rw' P A R O Og); exact F.
Qed.

Lemma early_okW_x : forall T T1 m xs d B, early_okW p c cc pc N T T1 m xs d B -> early_okW p c X pc N T T1 m xs d B.
Proof.
  intros T T1 m xs d B E f. specialize (E f). cbv zeta in E |- *. cbn [bd X cc_x]. cbn [bd] in E.
  destruct E as (j & L & Fj & Ed & Tk). exists j. split; [exact L|]. split; [|split].
  - apply (first_atR_X p c cc pc rv' rw' P A R O Og).
    unfold first_atR in *. exact (plc_agree p W c cc pc (S T1) _ _ T1 (TH m xs) j (agX p c cc pc N rv' rw' P A R O Og Hrv _ _ j) Fj).
  - rewrite <- (eof_agree p W c j _ _ (agX p c cc pc N rv' rw' P A R O Og Hrv _ _ j)). exact Ed.
  - intros j' L1 L2 Ex Fx Td.
    set (rW := creg p c cc pc N (bor (bd cc) B) f) in *. set (rA := creg p c X pc N (bor (bd cc) B) f) in *.
    assert (Aj : agree rW rA j) by apply (agX p c cc pc N rv' rw' P A R O Og Hrv).
    assert (Aj' : agree rW rA j') by (apply (agree_le rW rA j); [exact Aj|lia]).
    assert (Aj'' : agree rW rA (S j')) by (apply (agree_le rW rA j); [exact Aj|lia]).
    assert (Bj'' : agree rA rW (S j')) by (intros i Li; symmetry; apply Aj''; exact Li).
    destruct (ins_agree p W c j' rW rA Aj') as [Ei _].
    rewrite <- (exec_agree p W c j' rW rA Aj') in Ex.
    rewrite <- Ei in Td.
    apply taken_X. apply (taken_agree p c cc pc rW rA T j' W Aj').
    apply Tk; [exact L1|exact L2|exact Ex| |exact Td].
    intros v Hv. rewrite (cfailv_agree p W c j' rW rA v Aj'). apply Fx.
    apply htakenv_X. apply (htakenv_agree p c cc pc rW rA T j' v W Aj'' Hv).
Qed.

End Tr2.

Lemma fxok_ieval : forall cc k i r r' a, ieval i r = ieval i r' -> fxok cc k i r a -> fxok cc k i r' a.
Proof.
  intros cc k i r r' a E H b Fb Ci Ic. assert (Ic' : icond i r = true) by (unfold icond; rewrite E; exact Ic).
  rewrite <- (cexp_ieval _ _ _ E). apply (H b Fb Ci Ic').
Qed.

Lemma cfix_ok_x : forall p c cc pc N j b B o rv' rw' P A R O Og, wf p -> pend_ok cc pc ->
  (forall j x, rv' j x = rv cc j x) ->
  cfix_ok p c cc pc N j b B o -> cfix_ok p c (cc_x cc rv' rw' P A R O Og) pc N j b B o.
Proof.
  intros p c cc pc N j b B o rv' rw' P A R O Og W PO Hrv (v & H). exists v. intros f. specialize (H f). cbv zeta in H |- *.
  cbn [bd cc_x rg]. cbn [bd] in H.
  set (rW := creg p c cc pc N (bor (bd cc) B) f) in *. set (rA := creg p c (cc_x cc rv' rw' P A R O Og) pc N (bor (bd cc) B) f) in *.
  assert (Aj : agree rW rA j) by apply (agX p c cc pc N rv' rw' P A R O Og Hrv).
  assert (Ej : rW j = rA j) by (apply (agX p c cc pc N rv' rw' P A R O Og Hrv _ _ (S j)); lia).
  destruct (ins_agree p W c j rW rA Aj) as [Ei Ev]. rewrite <- Ei.
  destruct H as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
  assert (Ic : icond (ins p c j rW) rA = icond (ins p c j rW) rW) by (unfold icond; rewrite Ev; reflexivity).
  assert (Ce : cexp (ins p c j rW) rA = cexp (ins p c j rW) rW) by (symmetry; apply cexp_ieval; exact Ev).
  rewrite Ic, Ce.
  refine (conj C1 (conj C2 (conj _ (conj _ (conj C5 (conj _ _)))))).
  - rewrite pend_at_x. rewrite <- C3. symmetry. apply (pend_at_agree p W c cc pc N rW rA j PO Aj).
  - rewrite hpend_at_x. rewrite <- C4. symmetry. apply (hpend_at_agree p W c cc pc N rW rA j PO Aj).
  - exact (eq_trans (f_equal vv (eq_sym Ej)) C6).
  - exact C7.
Qed.
