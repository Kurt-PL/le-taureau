(* The invariants of M2Model's runs (Inv1, Inv2, Inv3,
   InvO, and M2Cont's INVP/INVH) hold on every run of M2DQ (runQ).
   - an M2Model step: the step cases of Inv1_run, Inv2_run, Inv_run,
     InvO_run and INVPH_run, restated with the invariants of the state
     before (they were stated over run); the section lemmas are reused;
   - q_rfix: M2Model.scfail (the existing *_cfail lemmas; M2Cont's CfailP
     took run p s only to get Inv1, so it is restated with Inv1), then sbd
     (new lemmas, the *_cfix proofs without the fixed result);
   - q_sfix: M2Model.scfix0 with success (the existing *_cfix lemmas; the
     record condition of INVP_cfix from sfix_ok: DQ.sfix_hc). *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO M2Cont M2DA M2DP M2DQ.

(* ---------- sbd changes only bd ---------- *)
Section Bd.
Variables (s : st) (c : nat) (B0 : nat -> bool).
Local Abbreviation s' := (sbd s c B0).
Ltac bxx := let c0 := fresh "c0" in intros c0; unfold sbd; simpl; unfold upd at 1; destruct (Nat.eqb_spec c0 c); [subst; reflexivity|reflexivity].
Lemma oc_bd : forall c', oc (cs s' c') = oc (cs s c'). Proof. bxx. Qed.
Lemma oh_bd : forall c', oh (cs s' c') = oh (cs s c'). Proof. bxx. Qed.
Lemma ai_bd : forall c', ai (cs s' c') = ai (cs s c'). Proof. bxx. Qed.
Lemma rw_bd : forall c', rw (cs s' c') = rw (cs s c'). Proof. bxx. Qed.
Lemma rv_bd : forall c', rv (cs s' c') = rv (cs s c'). Proof. bxx. Qed.
Lemma rg_bd : forall c', rg (cs s' c') = rg (cs s c'). Proof. bxx. Qed.
Lemma fx_bd : forall c', fx (cs s' c') = fx (cs s c'). Proof. bxx. Qed.
Lemma vP_bd : forall c', vP (cs s' c') = vP (cs s c'). Proof. bxx. Qed.
Lemma vA_bd : forall c', vA (cs s' c') = vA (cs s c'). Proof. bxx. Qed.
Lemma vR_bd : forall c', vR (cs s' c') = vR (cs s c'). Proof. bxx. Qed.
Lemma vO_bd : forall c', vO (cs s' c') = vO (cs s c'). Proof. bxx. Qed.
Lemma vOg_bd : forall c', vOg (cs s' c') = vOg (cs s c'). Proof. bxx. Qed.
Lemma ent_bd : forall t, ent s' t = ent s t. Proof. reflexivity. Qed.
Lemma einstr_bd : forall p e, einstr p s' e = einstr p s e. Proof. intros p e. unfold einstr. rewrite ai_bd. reflexivity. Qed.
Lemma rgof_bd : forall e, rgof s' e = rgof s e. Proof. intros e. unfold rgof. rewrite rg_bd. reflexivity. Qed.

Lemma Inv1_bd : forall p, Inv1 p s -> Inv1 p s'.
Proof.
  intros p I. destruct I; constructor; change (pcs s') with (pcs s) in *; change (tp s') with (tp s) in *;
    change (cm s') with (cm s) in *; change (tm s') with (tm s) in *; change (lg s') with (lg s) in *;
    unfold xex, ohb, pending, hpending, tmo, settled, ent in *; intros;
    rewrite ?oc_bd, ?oh_bd, ?ai_bd, ?rw_bd, ?rg_bd in *; eauto.
Qed.

Lemma Inv2_bd : forall p, Inv2 p s -> Inv2 p s'.
Proof.
  intros p J. pose proof J as J0. destruct J; constructor; unfold einstr, rgof, isw, rdvs, rdv in *;
    change (tm s') with (tm s) in *; change (hs s') with (hs s) in *;
    change (wv s') with (wv s) in *; change (wc s') with (wc s) in *;
    change (vG s') with (vG s) in *; intros;
    rewrite ?ent_bd, ?ai_bd, ?rg_bd, ?rv_bd, ?vP_bd, ?vA_bd, ?vR_bd in *; eauto.
  all: match goal with |- exists e i, ent _ ?y = _ /\ _ /\ _ /\ In ?x _ =>
    destruct (j_hist x y ltac:(assumption)) as (e & i & ?); exists e, i; rewrite ?ai_bd; assumption end.
Qed.

Lemma Inv3_bd : forall p, Inv3 p s -> Inv3 p s'.
Proof.
  intros p L.
  assert (XG : forall e, xg p s' e <-> xg p s e) by (intros e; unfold xg; rewrite einstr_bd, rgof_bd; tauto).
  assert (XL : forall e, xl p s' e <-> xl p s e) by (intros e; unfold xl; rewrite einstr_bd, rgof_bd; tauto).
  assert (XLL : forall e, xll p s' e <-> xll p s e) by (intros e; unfold xll; rewrite einstr_bd; tauto).
  assert (XSS : forall e, xss p s' e <-> xss p s e) by (intros e; unfold xss; rewrite einstr_bd; tauto).
  assert (CP : forall c', vP (cs s' c') = vP (cs s c') /\ vA (cs s' c') = vA (cs s c') /\ vR (cs s' c') = vR (cs s c'))
    by (intros c'; rewrite vP_bd, vA_bd, vR_bd; repeat split).
  destruct L. constructor; cbn [vG wc hs wv sbd].
  - intros c'. rewrite (proj1 (CP c')), (proj1 (proj2 (CP c'))), (proj2 (proj2 (CP c'))). apply k_RP.
  - intros t e E. rewrite (proj1 (CP _)). exact (k_Pcur t e E).
  - exact k_Ppair.
  - intros t e E X. apply XG in X. exact (k_Gcur t e E X).
  - intros t e t' e' E E' X X'. apply XG in X. apply XG in X'. exact (k_Gpair t e t' e' E E' X X').
  - intros t e t' f E F Ec Lt Xf NS v Hv Hw. rewrite (proj2 (proj2 (CP _))).
    rewrite XSS, XG in Xf. rewrite XG in Hw.
    apply (k_Rcur t e t' f E F Ec Lt Xf); auto. intros tg g G Eg Lg. rewrite <- XSS. apply (NS tg g G Eg Lg).
  - intros te e tf f tw w' E F Wn Ec1 Ec2 L1 L2 L3 Xf Ew NS v Hv Hw.
    rewrite XSS, XG in Xf. rewrite XG in Hw.
    apply (k_Rpair te e tf f tw w' E F Wn Ec1 Ec2 L1 L2 L3 Xf Ew); auto. intros tg g G Eg Lg Lg2. rewrite <- XSS. apply (NS tg g G Eg Lg Lg2).
  - intros t l E X. apply XL in X. rewrite (proj1 (proj2 (CP _))). exact (k_Acur t l E X).
  - intros tl l tf f E F Ec Lt X Y. apply XL in X. rewrite XLL, XG in Y. rewrite (proj1 (CP _)). exact (k_Acq tl l tf f E F Ec Lt X Y).
  - intros t l E X Y. apply XL in X. apply XG in Y. rewrite (proj1 (CP _)). exact (k_Aselfc t l E X Y).
  - intros tl l te e E E' Ec Lt X Y. apply XL in X. apply XG in Y. exact (k_Aself tl l te e E E' Ec Lt X Y).
  - intros tl l tf f te e E F E' Ec1 Ec2 Lt X Y. apply XL in X. rewrite XLL, XG in Y. exact (k_Apair tl l tf f te e E F E' Ec1 Ec2 Lt X Y).
Qed.

Lemma InvO_bd : forall p, InvO p s -> InvO p s'.
Proof.
  intros p Q.
  assert (XG : forall e, xg p s' e <-> xg p s e) by (intros e; unfold xg; rewrite einstr_bd, rgof_bd; tauto).
  assert (XL : forall e, xl p s' e <-> xl p s e) by (intros e; unfold xl; rewrite einstr_bd, rgof_bd; tauto).
  assert (XLL : forall e, xll p s' e <-> xll p s e) by (intros e; unfold xll; rewrite einstr_bd; tauto).
  assert (XA : forall e, xacc p s' e <-> xacc p s e) by (intros e; unfold xacc; rewrite XL; tauto).
  destruct Q. constructor.
  - intros c'. rewrite vO_bd, vP_bd. exact (o_sub_PG c').
  - intros c'. rewrite vO_bd, vOg_bd. exact (o_gsub c').
  - intros t f H X. rewrite XG in X. rewrite vOg_bd. exact (o_gcur t f H X).
  - intros tf f te e Hf He E T X Y. rewrite XG in X. rewrite XA in Y. exact (o_gpair tf f te e Hf He E T X Y).
  - exact o_rfe.
  - intros tl l tf f Hl Hf E T X Y w0 Cw Nw. rewrite XL in X. rewrite XLL in Y.
    rewrite vO_bd. exact (o_acur tl l tf f Hl Hf E T X Y w0 Cw Nw).
  - intros tl l tf f te e Hl Hf He E1 E2 T1 T2 X Y Z w0 Cw Nw. rewrite XL in X. rewrite XLL in Y. rewrite XL in Z.
    exact (o_apair tl l tf f te e Hl Hf He E1 E2 T1 T2 X Y Z w0 Cw Nw).
  - intros t e H y Yq. destruct (o_QP_G t e H y Yq) as [A|(Ly & Gy & Fy)]; [left; exact A|right].
    split; [exact Ly|]. split; [exact Gy|]. intros tf f Hf T X. rewrite XG in X. exact (Fy tf f Hf T X).
  - intros t e H. rewrite einstr_bd, rgof_bd. exact (o_eRC t e H).
Qed.
End Bd.

(* ---------- INVP / INVH after sbd ---------- *)
Section BdP.
Variables (p : prog) (s : st) (c : nat) (B0 : nat -> bool).
Hypothesis W : wf p.
Hypothesis I : Inv1 p s.
Hypothesis IP : INVP p s.
Hypothesis IPh : INVH p s.
Local Abbreviation cc := (cs s c).
Local Abbreviation pc := (pcs s c).
Local Abbreviation N := (tp s c).
Local Abbreviation cc' := (cc_fx cc (bor (bd cc) B0) (fx cc)).

Lemma bd_cs : cs (sbd s c B0) c = cc'.
Proof. unfold sbd. simpl. unfold upd at 1. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma bd_regs : forall B f j,
  creg p c cc pc N (bor (bd cc) (bor B0 B)) f j = creg p c cc' pc N (bor (bd cc') B) f j.
Proof.
  intros B f. set (rt := creg p c cc' pc N (bor (bd cc') B) f).
  assert (PO : pend_ok cc pc) by (apply (pend_ok_of p s c I)).
  assert (PO' : pend_ok cc' pc) by exact PO.
  apply (creg_ext p W c cc pc N _ f rt PO). intros j.
  transitivity (slotv p c cc' pc N (bor (bd cc') B) f rt j); [|symmetry; apply (creg_fix p W c cc' pc N _ f j PO')].
  unfold slotv. rewrite !pend_at_fx, !hpend_at_fx. change (rg cc') with (rg cc). change (cfx cc') with (cfx cc).
  destruct (Nat.ltb j pc); [reflexivity|]. destruct (_ && _); [|reflexivity].
  destruct (pend_at p c cc pc N rt j); [reflexivity|].
  f_equal. destruct (hpend_at p c cc pc N rt j); [reflexivity|].
  cbv zeta. erewrite map_ext; [reflexivity|]. intros x. rewrite cellv_fx. apply cellv_Bext.
  intros q. unfold bor. cbn [bd cc_fx]. destruct (bd cc q), (B0 q), (B q); reflexivity.
Qed.

Lemma INVP_bd : INVP p (sbd s c B0).
Proof.
  intros c0 kk d B f P. destruct (Nat.eq_dec c0 c) as [->|N0].
  2:{ assert (E : cs (sbd s c B0) c0 = cs s c0) by (unfold sbd; simpl; apply upd_neq; auto).
      change (pcs (sbd s c B0)) with (pcs s) in *. change (tp (sbd s c B0)) with (tp s) in *.
      rewrite E in *. apply (IP c0 kk d B f P). }
  change (pcs (sbd s c B0)) with (pcs s) in *. change (tp (sbd s c B0)) with (tp s) in *.
  rewrite bd_cs in *.
  destruct (IP c kk d (bor B0 B) f P) as (j & (Pk & t & O & Fj)). exists j. split; [exact P|]. exists t. split; [exact O|].
  unfold first_at in *. rewrite plc_fx. apply (first_at_ext p c cc pc _ _ t d j W (bd_regs B f) Fj).
Qed.

Lemma INVH_bd : INVH p (sbd s c B0).
Proof.
  intros c0 kk m xs B f P C. destruct (Nat.eq_dec c0 c) as [->|N0].
  2:{ assert (E : cs (sbd s c B0) c0 = cs s c0) by (unfold sbd; simpl; apply upd_neq; auto).
      change (pcs (sbd s c B0)) with (pcs s) in *. change (tp (sbd s c B0)) with (tp s) in *.
      rewrite E in *. apply (IPh c0 kk m xs B f P C). }
  change (pcs (sbd s c B0)) with (pcs s) in *. change (tp (sbd s c B0)) with (tp s) in *.
  rewrite bd_cs in *.
  destruct (IPh c kk m xs (bor B0 B) f P C) as (j & (Pk & C' & t & O & Fj)). exists j. split; [exact P|]. split; [exact C|].
  exists t. split; [exact O|]. unfold first_atR in *. rewrite plc_fx. apply (first_atR_ext p c cc pc _ _ t m xs j W (bd_regs B f) Fj).
Qed.
End BdP.

(* ---------- M2Cont.CfailP with Inv1 for run (re-proof, same script) ---------- *)
Section CfailQ.
Variables (p : prog) (s : st) (c k : nat).
Hypothesis W : wf p.
Hypothesis I : Inv1 p s.
Hypothesis IP : INVP p s.
Hypothesis IPh : INVH p s.
Hypothesis Hp : pcs s c <= k.
Hypothesis Ho : oc (cs s c) k = None.
Hypothesis Hh : oh (cs s c) k <> None.
Hypothesis Hv : vok (rg (cs s c) k) = true.
Local Abbreviation cc := (cs s c).
Local Abbreviation g := (upd (rg (cs s c)) k (vd false (vv (rg (cs s c) k)))).
Local Abbreviation pc := (pcs s c).
Local Abbreviation N := (tp s c).

Lemma cf_csQ : cs (scfail s c k) c = cc_rg cc g.
Proof. unfold scfail. simpl. unfold upd at 1. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma cf_regsQ : forall B f, exists F, forall j,
  creg p c cc pc N (bor (bd cc) B) F j = creg p c (cc_rg cc g) pc N (bor (bd cc) B) f j.
Proof.
  intros B f. set (rt := creg p c (cc_rg cc g) pc N (bor (bd cc) B) f).
  set (F := fun j x => if Nat.eqb x (bitc (ins p c j rt))
                       then match hpend_at p c cc pc N rt j with Some k' => if Nat.eqb k' k then 0 else f j x | None => f j x end
                       else f j x).
  assert (PO : pend_ok cc pc) by (apply (pend_ok_of p s c I)).
  assert (FX : forall j x, x <> bitc (ins p c j rt) -> F j x = f j x)
    by (intros j x Hx; unfold F; rewrite (proj2 (Nat.eqb_neq _ _) Hx); reflexivity).
  exists F. apply (creg_ext p W); [exact PO|]. intros j.
  unfold rt at 2. rewrite (creg_fix p W c (cc_rg cc g) pc N (bor (bd cc) B) f j PO). fold rt.
  unfold slotv. rewrite pend_at_rg, hpend_at_rg. cbn [rg cc_rg].
  destruct (Nat.ltb_spec j pc) as [L|L].
  { unfold upd. destruct (Nat.eqb_spec j k); [lia|reflexivity]. }
  destruct (_ && _); [|reflexivity].
  destruct (pend_at p c cc pc N rt j) as [k'|] eqn:Pa.
  { destruct (pend_at_spec _ _ _ _ _ _ _ _ Pa) as (Ok & _). unfold upd. destruct (Nat.eqb_spec k' k); [subst; congruence|reflexivity]. }
  destruct (hpend_at p c cc pc N rt j) as [k'|] eqn:Ph.
  - unfold fbit, F. rewrite Nat.eqb_refl, Ph. unfold upd. destruct (Nat.eqb_spec k' k) as [->|Nk].
    + rewrite Hv, vok_vd. simpl. rewrite andb_false_r. reflexivity.
    + reflexivity.
  - assert (FB : fbit F (ins p c j rt) j = fbit f (ins p c j rt) j) by (unfold fbit, F; rewrite Nat.eqb_refl, Ph; reflexivity).
    cbv zeta. rewrite FB. erewrite map_ext_in; [reflexivity|]. intros x Ix. rewrite cellv_rg.
    apply (cellv_fbits p c cc pc N _ F f rt FX). apply bitc_notin. exact Ix.
Qed.

Lemma INVP_cfailQ : INVP p (scfail s c k).
Proof.
  intros c0 kk d B f P. destruct (Nat.eq_dec c0 c) as [->|N0].
  2:{ assert (E : cs (scfail s c k) c0 = cs s c0) by (unfold scfail; simpl; apply upd_neq; auto).
      change (pcs (scfail s c k)) with (pcs s) in *. change (tp (scfail s c k)) with (tp s) in *.
      rewrite E in *. apply (IP c0 kk d B f P). }
  change (pcs (scfail s c k)) with (pcs s) in *. change (tp (scfail s c k)) with (tp s) in *.
  rewrite cf_csQ in *. change (bd (cc_rg cc g)) with (bd cc). destruct (cf_regsQ B f) as (F & EQ).
  destruct (IP c kk d B F P) as (j & (Pk & t & O & Fj)). exists j. split; [exact P|]. exists t. split; [exact O|].
  unfold first_at in *. rewrite plc_rg. apply (first_at_ext p c cc pc _ _ t d j W EQ Fj).
Qed.

Lemma INVH_cfailQ : INVH p (scfail s c k).
Proof.
  intros c0 kk m xs B f P C. destruct (Nat.eq_dec c0 c) as [->|N0].
  2:{ assert (E : cs (scfail s c k) c0 = cs s c0) by (unfold scfail; simpl; apply upd_neq; auto).
      change (pcs (scfail s c k)) with (pcs s) in *. change (tp (scfail s c k)) with (tp s) in *.
      rewrite E in *. apply (IPh c0 kk m xs B f P C). }
  change (pcs (scfail s c k)) with (pcs s) in *. change (tp (scfail s c k)) with (tp s) in *.
  rewrite cf_csQ in *. change (bd (cc_rg cc g)) with (bd cc). destruct (cf_regsQ B f) as (F & EQ).
  destruct (IPh c kk m xs B F P C) as (j & (Pk & C' & t & O & Fj)). exists j. split; [exact P|]. split; [exact C|].
  exists t. split; [exact O|]. unfold first_atR in *. rewrite plc_rg. apply (first_atR_ext p c cc pc _ _ t m xs j W EQ Fj).
Qed.
End CfailQ.

(* ---------- the invariants together ---------- *)
Record IQ (p : prog) (s : st) : Prop := { q1 : Inv1 p s; q2 : Inv2 p s; q3 : Inv3 p s; qO : InvO p s;
  qP : INVP p s; qH : INVH p s }.

Lemma IQ_init : forall p, IQ p sinit.
Proof.
  intros p. constructor; [apply Inv1_init|apply Inv2_init|apply Inv3_init|apply InvO_init|apply INVP_init|apply INVH_init].
Qed.

(* ---------- an M2Model step (the step cases of the run lemmas, re-stated) ---------- *)
Lemma Inv1_st : forall p s t, Inv1 p s -> step p s t -> Inv1 p t.
Proof.
  intros p s t IH H.
  destruct (step_cases p s t H) as [(c & i & m' & a & K & u & w & H1 & H2 & H3 & H4 & Hbh & Hh & Hwt & Hvo & H6 & _ & ->)
      |[(c & k & d & B & m' & a & K & u & w & H1 & H2 & H5 & Hh & Hwe & Hve & H4 & _ & ->)
      |[(c & d & H1 & H2 & H3 & H4 & H5 & Hfh & ->)|[(c & k & xs & B & m' & a & K & u & w & bv & H1 & H2 & H3 & H5 & H4 & H6 & _ & ->)
      |[(c & H1 & H2 & H3 & Hvk & Hf & H4 & _ & ->)|(c & j & b & B & oX & Hj & Hf & Hc & ->)]]]]].
  + eapply Inv1_ord; eauto. destruct Hh as [(Z & _)|(t1 & Z & Ci & _)]; [left; exact Z|right; eauto].
  + apply Inv1_es. destruct Hh as [(Z & Ok)|(t1 & xs & ev & nv & Z & -> & _ & Ac & Ok)].
    * pose proof (early_nofull _ _ _ _ _ _ _ _ _ Ok). pose proof (early_len _ _ _ _ _ _ _ _ _ Ok).
      eapply Inv1_early; eauto.
    * assert (DCas Plain xs ev nv <> DFn FFull) by discriminate. pose proof (earlyW_len _ _ _ _ _ _ _ _ _ _ _ Ok).
      eapply Inv1_early; eauto. right. exists t1. split; [exact Z|split; [reflexivity|rewrite Ac; reflexivity]].
  + eapply Inv1_match; eauto.
  + apply Inv1_read; auto.
  + apply Inv1_skip; auto.
  + destruct oX as [k|]; [destruct b|]; cbn [sflp]; apply Inv1_cfix; [exact IH| |exact IH].
    destruct (cfix_rec _ _ _ _ _ _ _ _ _ Hc) as (Hp & Ho & Hh & _). apply Inv1_cfail; auto.
Qed.

Lemma Inv2_st : forall p s t, Inv1 p s -> Inv2 p s -> step p s t -> Inv2 p t.
Proof.
  intros p s t I J H.
  destruct (step_cases p s t H) as [(c & i & m' & a & K & u & w & H1 & H2 & H3 & H4 & Hbh & Hh & _ & _ & H6 & _ & ->)
      |[(c & k & d & B & m' & a & K & u & w & H1 & H2 & Hso & Hh & _ & _ & H5 & _ & ->)
      |[(c & d & H1 & H2 & H3 & H4 & H4m & Hfh & ->)|[(c & k & xs & B & m' & a & K & u & w & bv & H1 & H2 & Hh & Hso & H4 & H5 & _ & ->)
      |[(c & S1 & S2 & S3 & S6 & S5 & S4 & _ & ->)|(cX & jX & bX & BX & oX & HjX & HfX & HcX & ->)]]]]].
  + eapply Inv2_step; eauto; [intros r Sr; apply (proj2 (H3 r Sr))|].
    destruct Hh as [(Z & _)|(t1 & Z & Ci & U & Ef)]; [left; exact Z|right].
    split; [exact U|exact Ef].
  + apply Inv2_es. eapply Inv2_step; eauto; [lia|intros r Sr; apply ieval_inst|].
    destruct Hh as [(Z & _)|(t1 & xs & ev & nv & Z & -> & U & Ac & _)]; [left; exact Z|right].
    split; [exact U|]. rewrite Ac. reflexivity.
  + eapply Inv2_match; eauto.
  + apply Inv2_read; auto.
  + apply Inv2_skip; auto.
  + destruct oX as [kX|]; [destruct bX|]; cbn [sflp]; apply Inv2_cfix; [auto| |auto].
    destruct (cfix_rec _ _ _ _ _ _ _ _ _ HcX) as (HpX & HoX & HhX & _). apply Inv2_cfail; auto.
Qed.

Lemma Inv3_st : forall p s t, Inv1 p s -> Inv2 p s -> Inv3 p s -> step p s t -> Inv3 p t.
Proof.
  intros p s t I J L H.
  destruct (step_cases p s t H) as [(c & i & m' & a & K & u & w & H1 & H2 & H3 & H4 & Hbh & Hh & _ & _ & H6 & _ & ->)|[(c & k & d & B & m' & a & K & u & w & H1 & H2 & Hso & Hh & _ & _ & H5 & _ & ->)|[(c & d & H1 & H2 & H3 & H4 & H4m & Hfh & ->)|[(c & k & xs & B & m' & a & K & u & w & bv & H1 & H2 & Hh & Hso & H4 & H5 & _ & ->)|[(c & S1 & S2 & S3 & _ & S5 & S4 & _ & ->)|(cX & jX & bX & BX & oX & HjX & HfX & HcX & ->)]]]]].
  + eapply Inv3_step; eauto; [intros r Sr; apply (proj2 (H3 r Sr))|].
    destruct Hh as [(Z & _)|(t1 & Z & Ci & U & Ef)]; [left; exact Z|right; split; [exact U|exact Ef]].
  + apply Inv3_es. eapply Inv3_step; eauto; [lia|intros r Sr; apply ieval_inst|].
    destruct Hh as [(Z & _)|(t1 & xs & ev & nv & Z & -> & U & Ac & _)]; [left; exact Z|right].
    split; [exact U|]. rewrite Ac. reflexivity.
  + eapply Inv3_match; eauto.
  + apply Inv3_read; auto.
  + apply Inv3_skip; auto.
  + destruct oX as [kX|]; [destruct bX|]; cbn [sflp]; apply Inv3_cfix; [auto| |auto].
    destruct (cfix_rec _ _ _ _ _ _ _ _ _ HcX) as (HpX & HoX & HhX & _). apply Inv3_cfail; auto.
Qed.

Lemma InvO_st : forall p s t, Inv1 p s -> Inv2 p s -> Inv3 p s -> InvO p s ->
  Inv1 p t -> Inv2 p t -> Inv3 p t -> step p s t -> InvO p t.
Proof.
  intros p s t I J L Q I' J' L' H.
  destruct (step_cases p s t H) as [(c & i & m' & a & K & u & w & H1 & H2 & H3 & H4 & Hbh & Hh & _ & _ & H6 & _ & ->)|[(c & k & d & B & m' & a & K & u & w & H1 & H2 & Hso & Hh & _ & _ & H5 & _ & ->)|[(c & d & H1 & H2 & H3 & H4 & H4m & Hfh & ->)|[(c & k & xs & B & m' & a & K & u & w & bv & H1 & H2 & Hh & Hso & H4 & H5 & _ & ->)|[(c & S1 & S2 & S3 & _ & S5 & S4 & _ & ->)|(cX & jX & bX & BX & oX & HjX & HfX & HcX & ->)]]]]].
  + eapply InvO_step; eauto; [intros r Sr; apply (proj2 (H3 r Sr))|].
    destruct Hh as [(Z & _)|(t1 & Z & Ci & U & Ef)]; [left; exact Z|right; split; [exact U|exact Ef]].
  + apply InvO_es. eapply InvO_step; eauto; [lia|intros r Sr; apply ieval_inst|].
    destruct Hh as [(Z & _)|(t1 & xs & ev & nv & Z & -> & U & Ac & _)]; [left; exact Z|right].
    split; [exact U|]. rewrite Ac. reflexivity.
  + eapply InvO_match; eauto.
  + apply InvO_read; auto.
  + apply InvO_skip; auto.
  + destruct oX as [kX|]; [destruct bX|]; cbn [sflp]; apply InvO_cfix; [auto| |auto].
    destruct (cfix_rec _ _ _ _ _ _ _ _ _ HcX) as (HpX & HoX & HhX & _). apply InvO_cfail; auto.
Qed.

Lemma INVPH_st : forall p s t, wf p -> cellful p -> Inv1 p s -> Inv2 p s -> INVP p s -> INVH p s ->
  Inv1 p t -> step p s t -> INVP p t /\ INVH p t.
Proof.
  intros p s t W Wc I J IP IPh I' H.
  destruct (step_cases p s t H) as [(c & i & m' & a & K & u & w & H1 & H2 & H3 & H4 & Hbh & Hh & HwO & HvO & H6 & HfO & ->)|[(c & k & d & B & m' & a & K & u & w & H1 & H2 & Hso & Hh & HwE & HvE & H5 & (HfE1 & HfE2) & ->)|[(c & d & H1 & H2 & H3 & H4 & H5 & Hfh & ->)|[(c & k & xs & B & m' & a & K & u & w & bv & H1 & H2 & Hoh & Hso & H4 & H5 & HfR & ->)|[(c & K1 & K2 & K3 & Kv & K5 & K4 & HfS & ->)|(cX & jX & bX & BX & oX & HjX & HfX & HcX & ->)]]]]].
  + split; [eapply (INVP_ord p s c i m' a K u w)|eapply (INVH_ord p s c i m' a K u w)]; eauto.
  + destruct Hh as [(Z & Ok)|(t1 & xs & ev & nv & Z & -> & U & Ac & Ok)].
    * split; [eapply (INVP_early p s c k d B m' a K u w)|eapply (INVH_early p s c k d B m' a K u w)]; eauto;
        intros f0 j0 F0; exact (HfE1 Z f0 j0 F0).
    * subst u. assert (Vo : vok (rg (cs s c) k) = true) by (apply HvE; congruence).
      assert (Wt : w = true) by (apply HwE; congruence).
      split; [eapply (INVP_cwe p s c k t1 xs ev nv B m' a K w)|eapply (INVH_cwe p s c k t1 xs ev nv B m' a K w)]; eauto;
        intros f0 j0 F0; exact (HfE2 t1 xs ev nv f0 j0 Z eq_refl F0).
  + split; [eapply (INVP_match p s c d)|eapply (INVH_match p s c d)]; eauto.
  + split; [eapply (INVP_read p s c k xs B m' a K u w bv)|eapply (INVH_read p s c k xs B m' a K u w bv)]; eauto;
      intros g j0 F0; exact (proj1 (HfR g j0 F0)).
  + destruct (oh (cs s c) (pcs s c)) as [t1|] eqn:Oh.
    * destruct (i_half p s I c (pcs s c) t1 K2 Oh (le_n _)) as (_ & (xs & Ax) & _).
      assert (Er : eofR (ins p c (pcs s c) (rg (cs s c))) (rg (cs s c)) = Some (Plain, xs))
        by (rewrite (K3 ltac:(congruence)), Ax; reflexivity).
      assert (Cf : cfail (ins p c (pcs s c) (rg (cs s c))) (rg (cs s c)) (pcs s c) = true).
      { destruct (xex_false _ _ _ _ K1) as [X|(_ & X)]; [|exact X]. exfalso.
        destruct (eofR_exec_tied p c (pcs s c) (rg (cs s c)) Plain xs Wc Er) as [E0 _]. congruence. }
      assert (Vk : vok (rg (cs s c) (pcs s c)) = false) by (apply Kv; congruence).
      split; [eapply (INVP_skipf p s c t1 xs)|eapply (INVH_skipf p s c t1 xs)]; eauto.
    * assert (X : executes (ins p c (pcs s c) (rg (cs s c))) (rg (cs s c)) = false).
      { destruct (xex_false _ _ _ _ K1) as [X|(Z & _)]; [exact X|congruence]. }
      split; [eapply (INVP_skip p s c)|eapply (INVH_skip p s c)]; eauto.
  + assert (Pre : Inv1 p (sflp s cX oX bX) /\ INVP p (sflp s cX oX bX) /\ INVH p (sflp s cX oX bX)).
    { destruct oX as [kX|]; [destruct bX|]; cbn [sflp]; try (split; [exact I|split; assumption]).
      destruct (cfix_rec _ _ _ _ _ _ _ _ _ HcX) as (HpF & HoF & HhF & HvF).
      split; [apply Inv1_cfail; auto|split; [apply (INVP_cfailQ p s cX kX)|apply (INVH_cfailQ p s cX kX)]; auto]. }
    destruct Pre as (I0 & P0 & H0).
    assert (Hc0 : forall f k, hpend_at p cX (cs (sflp s cX oX bX) cX) (pcs (sflp s cX oX bX) cX) (tp (sflp s cX oX bX) cX)
                (creg p cX (cs (sflp s cX oX bX) cX) (pcs (sflp s cX oX bX) cX) (tp (sflp s cX oX bX) cX)
                   (bor (bd (cs (sflp s cX oX bX) cX)) BX) f) jX = Some k ->
                vok (rg (cs (sflp s cX oX bX) cX) k) = true \/ bX = false).
    { destruct HcX as (v & Hv). destruct oX as [kX|]; [destruct bX|]; cbn [sflp]; intros f k Hp.
      - left. destruct (Hv f) as (_ & _ & _ & Ho & Hk & _). cbv zeta in Ho. rewrite Hp in Ho. apply Hk. congruence.
      - right. reflexivity.
      - exfalso. destruct (Hv f) as (_ & _ & _ & Ho & _). cbv zeta in Ho. congruence. }
    assert (Hf0 : fx (cs (sflp s cX oX bX) cX) jX = None) by (rewrite fx_flp; exact HfX).
    split; [apply (INVP_cfix p (sflp s cX oX bX) cX jX bX BX)|apply (INVH_cfix p (sflp s cX oX bX) cX jX bX BX)]; assumption.
Qed.

Lemma IQ_old : forall p s t, wf p -> cellful p -> IQ p s -> step p s t -> IQ p t.
Proof.
  intros p s t W Wc [I J L Q P Ph] H.
  assert (I' : Inv1 p t) by (apply (Inv1_st p s t I H)).
  assert (J' : Inv2 p t) by (apply (Inv2_st p s t I J H)).
  assert (L' : Inv3 p t) by (apply (Inv3_st p s t I J L H)).
  destruct (INVPH_st p s t W Wc I J P Ph I' H) as [P' Ph'].
  constructor; auto. apply (InvO_st p s t I J L Q I' J' L' H).
Qed.

(* ---------- q_rfix ---------- *)
Lemma IQ_rfix : forall p s c k B, wf p -> IQ p s -> rfail_ok p c (cs s c) (pcs s c) (tp s c) k B ->
  IQ p (sbd (scfail s c k) c B).
Proof.
  intros p s c k B W [I J L Q P Ph] Ok.
  pose proof (rfail_ge _ _ _ _ _ _ _ Ok) as Hp. destruct Ok as (Ho & Hh & Hv & _).
  assert (I0 : Inv1 p (scfail s c k)) by (apply Inv1_cfail; auto).
  constructor.
  - apply Inv1_bd. exact I0.
  - apply Inv2_bd. apply Inv2_cfail; auto.
  - apply Inv3_bd. apply Inv3_cfail; auto.
  - apply InvO_bd. apply InvO_cfail; auto.
  - apply INVP_bd; [exact W|exact I0|]. apply INVP_cfailQ; auto.
  - apply INVH_bd; [exact W|exact I0|]. apply INVH_cfailQ; auto.
Qed.

(* ---------- q_sfix ---------- *)
Lemma IQ_sfix : forall p s c j k B, wf p -> IQ p s -> fx (cs s c) j = None ->
  sfix_ok p c (cs s c) (pcs s c) (tp s c) j k B -> IQ p (scfix0 s c j true B).
Proof.
  intros p s c j k B W [I J L Q P Ph] Hf Ok.
  assert (Hc : forall f k', hpend_at p c (cs s c) (pcs s c) (tp s c)
      (creg p c (cs s c) (pcs s c) (tp s c) (bor (bd (cs s c)) B) f) j = Some k' -> vok (rg (cs s c) k') = true \/ true = false)
    by (intros f k' Hk; left; exact (sfix_hc _ _ _ _ _ _ _ _ Ok f k' Hk)).
  constructor.
  - apply Inv1_cfix. exact I.
  - apply Inv2_cfix. exact J.
  - apply Inv3_cfix. exact L.
  - apply InvO_cfix. exact Q.
  - apply (INVP_cfix p s c j true B); assumption.
  - apply (INVH_cfix p s c j true B); assumption.
Qed.

Lemma IQ_step : forall p s t, wf p -> cellful p -> IQ p s -> stepQ p s t -> IQ p t.
Proof.
  intros p s t W Wc Q S. destruct S as [s t S _|s c k B Ok _|s c j k B _ Hf Ok].
  - exact (IQ_old p s t W Wc Q S).
  - exact (IQ_rfix p s c k B W Q Ok).
  - exact (IQ_sfix p s c j k B W Q Hf Ok).
Qed.

Theorem IQ_run : forall p s, wf p -> cellful p -> runQ p s -> IQ p s.
Proof.
  intros p s W Wc R. induction R as [|s t R IH S]; [apply IQ_init|]. exact (IQ_step p s t W Wc IH S).
Qed.

Corollary INVPH_runQ : forall p s, wf p -> cellful p -> runQ p s -> INVP p s /\ INVH p s.
Proof. intros p s W Wc R. destruct (IQ_run p s W Wc R) as [_ _ _ _ P H]. auto. Qed.

Corollary InvAllO_runQ : forall p s, wf p -> cellful p -> runQ p s -> InvAllO p s.
Proof. intros p s W Wc R. destruct (IQ_run p s W Wc R) as [I J L Q _ _]. constructor; auto. Qed.

Print Assumptions IQ_run.
