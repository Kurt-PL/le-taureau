(* Part 14: in a fenced programme every access of a finished write-back run comes after
   a guard() of its context with only reads of CASes that store nothing in between (LFB).
   JE (A-runs): an entry of slot j happened before every later slot of its context was passed.
   FC: the access of node n (acc in the A image) has LFB at its time.
   FC_store: so has every entry of the state that stores into some cell. *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2InvO M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB M2DQWBK1 M2DQWBK3.
Require Import M2Iface M2IfaceInst M2DQIfaceInst MIComp MINeg MIFSC M2DQWBFsc.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

(* ---------- JE: an entry happened before every later slot of its context was passed ---------- *)
Definition JE (s : st) : Prop :=
  forall t e j tau, ent s t = Some e -> In (ec e, j, tau) (cm s) -> ek e < j -> t < tau.

Lemma JE_init : JE sinit.
Proof. intros t e j tau E. unfold ent in E. destruct t; discriminate. Qed.

Lemma in_cm_app : forall (l : list (nat * nat * nat)) a b, In a (l ++ [b]) -> In a l \/ a = b.
Proof. intros l a b I. apply in_app_iff in I. destruct I as [I|[I|[]]]; auto. Qed.

Section JE.
Variable p : prog.

Lemma JE_stepA : forall s s', M2Model.step p s s' -> Inv1 p s -> JE s -> JE s'.
Proof.
  intros s s' H I J t e j tau Ee Ic Lj. pose proof (i_tm p s I) as Tl.
  assert (Old : forall c, In (c, j, tau) (cm s) -> j < pcs s c).
  { intros c X. apply (proj2 (i_cmA p s I c j)). eauto. }
  destruct (step_cases p s s' H) as
    [(c & i & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ->)
    |[(c & k & d & B & m' & a & K & u & w & L1 & _ & _ & _ & _ & _ & _ & _ & ->)
    |[(c & d & _ & _ & _ & _ & _ & _ & ->)
    |[(c & k & xs & B & m' & a & K & u & w & bv & L1 & _ & _ & _ & _ & _ & _ & ->)
    |[(c & _ & _ & _ & _ & _ & _ & _ & ->)
    |(cX & jX & bX & BX & oX & _ & _ & _ & ->)]]]]].
  - unfold sord, evs, ent in *; cbn [lg cm] in *.
    destruct (ent_app _ _ _ _ Ee) as [(Ee' & Lt)|(-> & ->)].
    + destruct (in_cm_app _ _ _ Ic) as [Ic'|Ic']; [exact (J t e j tau Ee' Ic' Lj)|]. inversion Ic'; subst; lia.
    + cbn [ec ek] in *. destruct (in_cm_app _ _ _ Ic) as [Ic'|Ic']; [pose proof (Old c Ic'); lia|]. inversion Ic'; subst; lia.
  - unfold searly, set_es, searly0, evs, ent in *; cbn [lg cm] in *.
    destruct (ent_app _ _ _ _ Ee) as [(Ee' & Lt)|(-> & ->)]; [exact (J t e j tau Ee' Ic Lj)|].
    cbn [ec ek] in *. pose proof (Old c Ic). lia.
  - unfold smatch, ent in *; cbn [lg cm] in *.
    destruct (in_cm_app _ _ _ Ic) as [Ic'|Ic']; [exact (J t e j tau Ee Ic' Lj)|]. inversion Ic'; subst. rewrite Tl. apply nth_error_Some. congruence.
  - unfold sread, ent in *; cbn [lg cm] in *.
    destruct (ent_app _ _ _ _ Ee) as [(Ee' & Lt)|(-> & ->)]; [exact (J t e j tau Ee' Ic Lj)|].
    cbn [ec ek] in *. pose proof (Old c Ic). lia.
  - unfold sskip, ent in *; cbn [lg cm] in *.
    destruct (in_cm_app _ _ _ Ic) as [Ic'|Ic']; [exact (J t e j tau Ee Ic' Lj)|]. inversion Ic'; subst. rewrite Tl. apply nth_error_Some. congruence.
  - unfold ent, scfix0 in *. cbn [lg cm] in *. rewrite lg_flp in Ee. rewrite cm_flp in Ic.
    exact (J t e j tau Ee Ic Lj).
Qed.

Lemma JE_step : forall s s', step p s s' -> Inv1 p s -> JE s -> JE s'.
Proof.
  intros. match goal with H : stepQ _ ?s ?s2 |- _ => destruct (stepQ_split _ s s2 H) as [[HA _]|RF]; [eapply JE_stepA; eauto|] end.
  unfold JE, ent in *. rfx_rw RF. assumption.
Qed.

Lemma JE_run : forall s, run p s -> JE s.
Proof.
  intros s R. induction R as [|s s' R IH St]; [exact JE_init|].
  exact (JE_step s s' St (Inv1_run p s R) IH).
Qed.
End JE.

(* ---------- FC ---------- *)
Section FC.
Set Default Proof Using "All".
Variables (p : prog) (W : wf p) (FN : fenced p).
Variables (Fk : Prop) (Good : nat -> Prop) (sw : nat -> option (cell -> option nat)) (s sA : st).
Hypothesis RA : run p sA.
Hypothesis Rl : rel sw s sA.
Hypothesis K : KR Fk Good sw s sA.
Hypothesis D : done p s.

Lemma RAr : reach (STEP (Model := dqmodel) p) sA.
Proof. exact (proj2 (reach_runQ p sA) RA). Qed.
Lemma DA : done p sA.
Proof. exact (rel_done p sw s sA Rl D). Qed.
Local Abbreviation I1 := (Inv1_run p sA RA).

Lemma tmo_bt : forall c j t, tmo (cs sA c) j = Some t -> bt sA c j = t.
Proof. intros c j t H. unfold bt. rewrite H. reflexivity. Qed.

(* a passed guard() was recorded as the slot's event, at the time it was passed *)
Lemma guard_oc : forall c j E, RE sA c j E -> ai (cs sA c) j = IFn FFull -> oc (cs sA c) j = Some (bt sA c j).
Proof.
  intros c j E RE0 Aj. pose proof (RE_tmo (IFM := dqmodel) p sA RAr DA W c j E RE0) as Tm.
  unfold tmo in Tm. destruct (oc (cs sA c) j) as [t|] eqn:Oc; [exact Tm|].
  exfalso. assert (Lj : j < pcs sA c) by (apply (passed_h (IFM := dqmodel) p sA RAr DA W); congruence).
  destruct (i_halfp p sA I1 c j _ Oc Tm Lj) as (_ & (xs & Cx) & _). rewrite Aj in Cx. discriminate.
Qed.

Theorem FC : forall n, acc p sA n = true -> LFB s (fst n) (T sA n).
Proof.
  intros [c k] A. cbn [fst].
  destruct (fence_of (IFM := dqmodel) p sA RAr DA W FN (c, k) A) as (L1 & Fb & Fa). cbn [fst snd] in *.
  destruct (node_E (IFM := dqmodel) p sA RAr DA W (c, k) A) as (E & Ia & Ic & REk & Eik & Eok).
  destruct (n_ent (IFM := dqmodel) p sA RAr DA W c (k - 1) _ Fb ltac:(discriminate) eq_refl) as (Eg & REg & Eig).
  set (tg := bt sA c (k - 1)). set (t := T sA (c, k)).
  assert (Ni : iof p sA (c, k) <> INop) by (intros Z; rewrite Z in Ia; discriminate).
  assert (Xk : executes (iof p sA (c, k)) (rrg sA c) = true) by (unfold executes; rewrite Ia; exact Ic).
  assert (Lgt : tg < t).
  { apply (n_tie (IFM := dqmodel) p sA RAr DA W c (k - 1) k _ _ ltac:(lia) Fb eq_refl eq_refl Xk); [apply tied_gop_l; reflexivity|exact Ni]. }
  assert (Ltk : t < bt sA c (S k)).
  { apply (n_tie (IFM := dqmodel) p sA RAr DA W c k (S k) _ _ ltac:(lia) eq_refl Fa Xk eq_refl); [apply tied_gop_r; reflexivity|discriminate]. }
  destruct REg as (Ag & Bg & Cg).
  assert (Aig : ai (cs sA c) (k - 1) = IFn FFull) by (unfold einstr in Eig; rewrite Bg, Cg in Eig; exact Eig).
  pose proof (guard_oc c (k - 1) Eg (conj Ag (conj Bg Cg)) Aig) as Ocg.
  destruct (k_ent Fk Good sw s sA K tg Eg Ag) as (g & Eg' & Sg). pose proof Sg as (_ & Sg2 & Sg3 & _ & _ & _).
  assert (Lpg : k - 1 < pcs sA c) by (apply (passed (IFM := dqmodel) p sA RAr DA W); congruence).
  destruct (crel_eq p Fk Good sw s sA RA Rl K c) as (Oca & Oha & Aia & _).
  exists tg, g. split; [exact Lgt|]. split; [exact Eg'|]. split; [congruence|]. split.
  { unfold isFF. rewrite <- Sg2, <- Sg3, Bg, Cg, <- Oca, <- Aia, <- (r_pcs sw s sA Rl). auto. }
  intros t' e' L2 L3 E' Ec'.
  destruct (entW p Fk Good sw s sA RA Rl K t' e' E') as (eA & EA & Se). pose proof Se as (_ & Se2 & Se3 & _ & _ & Se6 & _ & _ & _ & Se10).
  destruct (i_et p sA I1 t' eA EA) as (_ & Xo).
  set (j := ek eA) in *. assert (Ce : ec eA = c) by congruence. rewrite Ce in Xo.
  (* a slot whose time is t' cannot lie between the guard() and the access *)
  assert (Z : tmo (cs sA c) j = Some t' -> False).
  { intros Tj. pose proof (tmo_bt c j t' Tj) as Bj.
    assert (REj : RE sA c j eA) by (split; [rewrite Bj; exact EA|split; [exact Ce|reflexivity]]).
    destruct (Nat.lt_trichotomy j (k - 1)) as [Lj|[Ej|Gj]].
    - destruct (proj1 (i_cmA p sA I1 c (k - 1)) Lpg) as (tau & In').
      assert (Xf : executes (ins p c (k - 1) (rg (cs sA c))) (rg (cs sA c)) = true) by (unfold rrg in Fb; rewrite Fb; reflexivity).
      assert (Ef : eof (ins p c (k - 1) (rg (cs sA c))) (rg (cs sA c)) = None) by (unfold rrg in Fb; rewrite Fb; reflexivity).
      pose proof (i_cmF p sA I1 c (k - 1) tau In' Xf Ef) as Oct. rewrite Ocg in Oct. injection Oct as Et.
      rewrite <- Ce in In'. pose proof (JE_run p sA RA t' eA (k - 1) tau EA In' Lj). unfold tg in L2. lia.
    - subst j. rewrite Ej in Bj. unfold tg in L2. lia.
    - destruct (Nat.lt_trichotomy j (S k)) as [Lj|[Ej|Gj']].
      + assert (j = k) by lia. unfold t, T in L3. cbn [fst snd] in L3. rewrite <- H, Bj in L3. lia.
      + rewrite <- Ej, Bj in Ltk. lia.
      + assert (Lt' : bt sA c (S k) < bt sA c j).
        { apply (n_tieE (IFM := dqmodel) p sA RAr DA W c (S k) j _ _ eA Gj' Fa eq_refl eq_refl); [apply tied_gop_l; reflexivity|exact REj]. }
        rewrite Bj in Lt'. lia. }
  destruct (eh eA) eqn:Eh.
  - destruct (sw t') as [f|] eqn:Sw.
    + exfalso. apply Z. rewrite Oha in Xo.
      destruct (w_WBOC Fk Good sw s sA K c j t' Xo ltac:(congruence)) as [Oc' _].
      unfold tmo. rewrite Oca, Oc', Oha. exact Xo.
    + split; [congruence|]. rewrite (Se10 eq_refl).
      destruct (j_ew p sA (proj2 (Inv2_run p sA RA)) t' eA _ EA eq_refl) as [J _]. rewrite J, Eh. reflexivity.
  - exfalso. apply Z. unfold tmo. rewrite Xo. reflexivity.
Qed.

(* every entry of the state that stores into some cell comes after a guard() so *)
Theorem FC_store : forall t e, ent s t = Some e -> ew e = true -> eC e <> [] -> LFB s (ec e) t.
Proof.
  intros t e E Ew Cn. destruct (entW p Fk Good sw s sA RA Rl K t e E) as (eA & EA & Se).
  pose proof Se as (_ & Se2 & Se3 & Se4 & _).
  set (c := ec eA) in *. set (k := ek eA) in *.
  destruct (o_eRC p sA (iaoO p sA (InvO_run p sA RA)) t eA EA) as [_ Ce].
  rewrite <- Se4 in Cn. rewrite Ce in Cn. unfold evC in Cn.
  destruct (isacc (einstr p sA eA) && icond (einstr p sA eA) (rgof sA eA)) eqn:Ac; [|exfalso; exact (Cn eq_refl)].
  destruct (i_et p sA I1 t eA EA) as (_ & Xo). fold c k in Xo.
  assert (Tm : tmo (cs sA c) k = Some t).
  { unfold tmo. destruct (eh eA) eqn:Eh; [|rewrite Xo; reflexivity].
    destruct (oc (cs sA c) k) as [t2|] eqn:Oc; [|exact Xo]. exfalso.
    destruct (crel_eq p Fk Good sw s sA RA Rl K c) as (Oca & Oha & _).
    destruct (sw t) as [f|] eqn:Sw.
    - rewrite Oha in Xo. destruct (w_WBOC Fk Good sw s sA K c k t Xo ltac:(congruence)) as [Oc' _].
      rewrite Oca in Oc. congruence.
    - pose proof Se as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Se10).
      destruct (j_ew p sA (proj2 (Inv2_run p sA RA)) t eA _ EA eq_refl) as [J _].
      rewrite Eh in J. cbn in J. rewrite <- (Se10 Sw), Ew in J. discriminate. }
  assert (Lk : k < pcs sA c).
  { unfold tmo in Tm. destruct (oc (cs sA c) k) eqn:Oc.
    - apply (passed (IFM := dqmodel) p sA RAr DA W). congruence.
    - apply (passed_h (IFM := dqmodel) p sA RAr DA W). congruence. }
  destruct (proj1 (i_cmA p sA I1 c k) Lk) as (tau & In').
  pose proof (proj2 (i_set p sA I1 c k tau In')) as Ai.
  assert (Acc : acc p sA (c, k) = true).
  { unfold acc, iof, rrg. cbn [fst snd]. unfold einstr, rgof in Ac. fold c k in Ac. rewrite Ai in Ac. exact Ac. }
  pose proof (FC (c, k) Acc) as F. cbn [fst] in F. unfold T in F. cbn [fst snd] in F.
  rewrite (tmo_bt c k t Tm) in F. rewrite <- Se2. exact F.
Qed.
End FC.
