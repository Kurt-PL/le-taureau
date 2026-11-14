(* Part 68: the facts CO2nK (M2DQWBK62) needs, each of one run or one chain.
   - INVF (wch_INVF): along a chain of images, a written-back store w standing for a in cell x
     (sw w = Some f, f x = Some a) has an image entry at time w that read a in x.  The image entry at
     w is the CAS's own entry: its read half (wbP, wbE); the slot's rw in
     the image is pi sw of the state's (crel), and the CAS's entry stores nothing (ew_fail).
   - no_past_guard_h: the read half of a CAS is never recorded at or beyond a guard() its context has
     not passed, in a run with a finished future (as M2DQWBK32.no_past_guard for oc).
   - pcs_step_le: one step moves a context's next instruction by at most one.
   - new_slot: the new entry of a step is at or beyond its context's next instruction.
   - ent_new_pcs: a step that logs an entry and moves the entry's context's next instruction is the
     in-order step: the entry is at that instruction, and the slot records it. *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Lit.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Trace M2DQTrace M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB.
Require Import M2DQWBK1 M2DQWBK3 M2DQWBK13 M2DQWBK32 M2DQWBK37.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBQb M2DQWBK1Q M2DQShim M2DQTr.

Definition INVF (sw : nat -> option (cell -> option nat)) (sA : st) : Prop :=
  forall w f x a, sw w = Some f -> f x = Some a -> exists e0, ent sA w = Some e0 /\ erf e0 x = Some a.

Section F.
Variable p : prog.

(* the image entry of a CAS slot that failed (whole) or whose read happened alone *)
Lemma rw_ent : forall Fk Good sw sW sA c k t x a, run p sA -> rel sw sW sA -> KR Fk Good sw sW sA ->
  oc (cs sW c) k = None -> oh (cs sW c) k = Some t ->
  is_cas (ai (cs sW c) k) = true -> pi sw x (rw (cs sW c) k x) = Some a ->
  exists e, ent sA t = Some e /\ erf e x = Some a.
Proof.
  intros Fk Good sw sW sA c k t x a RA R K O Oh Cc Pa.
  destruct (crel_eq p Fk Good sw sW sA RA R K c) as (Eoc & Eoh & Eai & Erg & _).
  destruct (r_cr sw sW sA R c) as (_ & _ & RW).
  pose proof (Inv1_run p sA RA) as I.
  assert (H' : oc (cs sA c) k = Some t \/ (oc (cs sA c) k = None /\ oh (cs sA c) k = Some t)).
  { rewrite Eoc, Eoh. right. split; [exact O|exact Oh]. }
  destruct (M2Inv.i_rw p sA I c k t H') as (e & E & Rw).
  assert (Ce : ec e = c /\ ek e = k /\ (eh e = true \/ vok (rg (cs sA (ec e)) (ek e)) = false)).
  { rewrite <- Eoh in Oh. destruct (M2Inv.i_oh p sA I c k t Oh) as (e' & E' & C' & K' & H1).
    rewrite E in E'. injection E' as <-. split; [exact C'|]. split; [exact K'|]. left. exact H1. }
  destruct Ce as (Ce & Ke & Hf).
  assert (Ew : ew e = false).
  { apply (ew_fail p sA t e RA E); [|exact Hf]. unfold einstr. rewrite Ce, Ke, Eai. exact Cc. }
  exists e. split; [exact E|]. rewrite <- Pa, <- RW, Rw. unfold wrote. rewrite Ew. reflexivity.
Qed.

Lemma wch_INVF : forall Fk Good sW sw sA, wch p Fk Good sW sw sA -> INVF sw sA.
Proof.
  intros Fk Good sW sw sA Ch. induction Ch as [|sW sw sA sW' sw' sA' Ch IH L RA' R' K'].
  - intros w f x a S. discriminate.
  - pose proof (wch_run p Fk Good sW sw sA Ch) as RA. pose proof (wch_rel p Fk Good sW sw sA Ch) as Rl.
    pose proof (wch_KR p Fk Good sW sw sA Ch) as K.
    assert (Old : step p sA sA' -> forall w f x a, sw w = Some f -> f x = Some a ->
              exists e0, ent sA' w = Some e0 /\ erf e0 x = Some a).
    { intros StA w f x a S F. destruct (IH w f x a S F) as (e0 & E0 & R0). exists e0. split; [|exact R0].
      exact (x_ent _ _ (Ext_step p sA sA' RA StA) w e0 E0). }
    destruct L as [(St & Fh & StA & ->)
      |[(s' & c & k & t1 & H'' & St & Ps & Fr & Ok & -> & StA & Rl' & K1 & ->)
      |(c & k & t1 & xs & H'' & Lk & Oc & Oh & Ai & Vk & Eo & Fr & Ok & -> & -> & ->)]].
    + exact (Old StA).
    + intros w f x a S F. unfold upd in S. destruct (Nat.eqb_spec w t1) as [->|N]; [|exact (Old StA w f x a S F)].
      injection S as <-. pose proof Ps as (_ & _ & Pk & _ & Oc0 & _ & Oh1 & Cc & _).
      assert (Oc1 : oc (cs s' c) k = None).
      { rewrite (partskip_form p sW s' c k t1 St Ps). unfold sskip. cbn [cs]. rewrite upd_eq. cbn [oc]. exact Oc0. }
      exact (rw_ent Fk Good sw s' sA' c k t1 x a RA' Rl' K1 Oc1 Oh1 Cc F).
    + intros w f x a S F. unfold upd in S. destruct (Nat.eqb_spec w t1) as [->|N]; [|exact (IH w f x a S F)].
      injection S as <-.
      exact (rw_ent Fk Good sw sW sA c k t1 x a RA Rl K Oc Oh ltac:(rewrite Ai; reflexivity) F).
Qed.

(* ---------- slots of an A run ---------- *)
Lemma pcs_step_le : forall s s' c, step p s s' -> pcs s' c <= S (pcs s c).
Proof.
  intros s s' c St.
  destruct (stepQ_split p s s' St) as [[HA _]|RF]; [|rewrite (rfx_pcs _ _ RF); lia].
  destruct (step_cases p s s' HA) as
    [(c0 & i & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ->)
    |[(c0 & k0 & d & B & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & _ & _ & ->)
    |[(c0 & d & _ & _ & _ & _ & _ & _ & ->)
    |[(c0 & k0 & xs0 & B & m' & a & K & u & w & bv & _ & _ & _ & _ & _ & _ & _ & ->)
    |[(c0 & _ & _ & _ & _ & _ & _ & _ & ->)
    |(cX & jX & bX & BX & oX & _ & _ & _ & ->)]]]]].
  all: try (unfold sord, evs; cbn [pcs]).
  all: try (unfold searly, set_es, searly0, evs; cbn [pcs]).
  all: try (unfold smatch; cbn [pcs]).
  all: try (unfold sread; cbn [pcs]).
  all: try (unfold sskip; cbn [pcs]).
  all: try (unfold scfix0; cbn [pcs]; rewrite pcs_flp).
  all: try lia.
  all: unfold upd; destruct (Nat.eqb_spec c c0) as [->|N]; lia.
Qed.

Lemma new_slot : forall s s' e, run p s -> step p s s' -> ent s' (tm s) = Some e ->
  pcs s (ec e) <= ek e /\ (if eh e then oh (cs s' (ec e)) (ek e) else oc (cs s' (ec e)) (ek e)) = Some (tm s).
Proof.
  intros s s' e R St E. pose proof (rS p s s' R St) as R'. pose proof (Inv1_run p s R) as I.
  pose proof (Inv1_run p s' R') as I'. pose proof (Ext_step p s s' R St) as X.
  destruct (i_et p s' I' (tm s) e E) as (_ & F). split; [|exact F].
  destruct (Nat.lt_ge_cases (ek e) (pcs s (ec e))) as [L|L]; [exfalso|exact L].
  destruct (eh e).
  - destruct (oh (cs s (ec e)) (ek e)) as [y|] eqn:O.
    + pose proof (x_oh _ _ X _ _ _ O) as O'. rewrite O' in F. injection F as ->.
      pose proof (oh_lt_tm p s _ _ _ I O). lia.
    + rewrite (x_ohp _ _ X _ _ L O) in F. discriminate.
  - destruct (oc (cs s (ec e)) (ek e)) as [y|] eqn:O.
    + pose proof (x_oc _ _ X _ _ _ O) as O'. rewrite O' in F. injection F as ->.
      pose proof (oc_lt_tm p s _ _ _ I O). lia.
    + rewrite (x_ocp _ _ X _ _ L O) in F. discriminate.
Qed.

Lemma ent_new_pcs : forall s s' e, run p s -> step p s s' -> ent s' (tm s) = Some e ->
  pcs s' (ec e) <> pcs s (ec e) ->
  ek e = pcs s (ec e) /\ ai (cs s' (ec e)) (ek e) = ins p (ec e) (pcs s (ec e)) (rg (cs s (ec e))).
Proof.
  intros s s' e R St Ee Np. pose proof (Inv1_run p s R) as I.
  destruct (stepQ_split p s s' St) as [[HA _]|RF]; [|exfalso; apply Np; rewrite (rfx_pcs _ _ RF); reflexivity].
  destruct (step_cases p s s' HA) as
    [(c & i & m' & a & K & u & w & Hi & _ & _ & _ & _ & _ & _ & _ & _ & _ & ->)
    |[(c & k & d & B & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & _ & _ & ->)
    |[(c & d & _ & _ & _ & _ & _ & _ & ->)
    |[(c & k & xs & B & m' & a & K & u & w & bv & _ & _ & _ & _ & _ & _ & _ & ->)
    |[(c & _ & _ & _ & _ & _ & _ & _ & ->)
    |(cX & jX & bX & BX & oX & _ & _ & _ & ->)]]]]].
  - unfold sord, evs, ent in Ee. cbn [lg] in Ee. rewrite nth_error_app_last, <- (i_tm p s I), Nat.ltb_irrefl, Nat.eqb_refl in Ee.
    injection Ee as <-. cbn [ec ek]. split; [reflexivity|]. unfold sord, evs. cbn [cs]. rewrite !upd_eq. cbn [ai].
    rewrite upd_eq. exact (eq_sym Hi).
  - exfalso. apply Np. unfold searly, set_es, searly0, evs. reflexivity.
  - exfalso. unfold smatch, ent in Ee. cbn [lg] in Ee. rewrite (i_tm p s I) in Ee. rewrite (proj2 (nth_error_None _ _) (le_n _)) in Ee. discriminate.
  - exfalso. apply Np. unfold sread. reflexivity.
  - exfalso. unfold sskip, ent in Ee. cbn [lg] in Ee. rewrite (i_tm p s I) in Ee. rewrite (proj2 (nth_error_None _ _) (le_n _)) in Ee. discriminate.
  - exfalso. unfold scfix0, ent in Ee. cbn [lg] in Ee. rewrite (lg_flp s cX oX bX), (i_tm p s I) in Ee.
    rewrite (proj2 (nth_error_None _ _) (le_n _)) in Ee. discriminate.
Qed.
End F.

(* the read half of a CAS is not recorded at or beyond a guard() not yet passed, in a run that
   ends finished: passing that guard() (s_ord) requires that no CAS whose read happened alone is
   tied to it, and guard() is tied to everything *)
Lemma no_past_guard_h : forall p s sf c jg k, wf p -> run p s -> star p s sf -> done p sf ->
  (forall r, ins p c jg r = IFn FFull) -> pcs s c <= jg -> jg <= k -> oh (cs s c) k = None.
Proof.
  intros p s sf c jg k W R S D G.
  induction S as [s|s s1 sf St S IH]; intros L1 L2.
  - destruct (oh (cs s c) k) as [t|] eqn:O; [exfalso|reflexivity].
    pose proof (Inv1_run p s R) as I.
    assert (Cl : c < length p).
    { destruct (oc (cs s c) k) as [t'|] eqn:Oc.
      - exact (proj2 (i_pend p s I c k ltac:(lia) ltac:(congruence))).
      - destruct (i_half p s I c k t Oc O ltac:(lia)) as (_ & _ & Cl). exact Cl. }
    destruct D as (n & Fn & Cp). destruct (Cp c Cl) as [_ Hk].
    rewrite (proj2 (Hk k ltac:(lia))) in O. discriminate.
  - pose proof (Inv1_run p s R) as I. pose proof (Ext_step p s s1 R St) as X.
    destruct (oh (cs s c) k) as [t|] eqn:O; [exfalso|reflexivity].
    assert (O1 : oh (cs s1 c) k = Some t) by exact (x_oh s s1 X c k t O).
    destruct (Nat.le_gt_cases (pcs s1 c) jg) as [L1'|G1].
    + rewrite (IH (rS p s s1 R St) D L1' L2) in O1. discriminate.
    + assert (Pj : pcs s c = jg) by (pose proof (pcs_step_le p s s1 c St); lia).
      subst jg.
      assert (Oc : oc (cs s c) k = None) by exact (no_past_guard p s sf c (pcs s c) k W R (stS p s s1 sf St S) D G L1 L2).
      destruct (i_half p s I c k t Oc O L2) as (_ & (xs & Ax) & _).
      assert (Hp : hpending (cs s c) (pcs s c) k Plain xs) by (split; [exact L2|split; [congruence|rewrite Ax; reflexivity]]).
      destruct (stepQ_split p s s1 St) as [[HA _]|RF]; [|exfalso; rewrite (rfx_pcs _ _ RF) in G1; lia].
  destruct (step_cases p s s1 HA) as
          [(c0 & i & m' & a & K & u & w & Hi & _ & _ & _ & Hh & Hor & _ & _ & _ & _ & ->)
          |[(c0 & k0 & d0 & B & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & _ & _ & ->)
          |[(c0 & d0 & S1 & _ & E0 & _ & _ & _ & ->)
          |[(c0 & k0 & xs0 & B & m' & a & K & u & w & bv & _ & _ & _ & _ & _ & _ & _ & ->)
          |[(c0 & X0 & _ & _ & _ & _ & _ & _ & ->)
          |(cX & jX & bX & BX & oX & _ & _ & _ & ->)]]]]].
      * unfold sord, evs in G1; cbn [pcs] in G1. unfold upd in G1. destruct (Nat.eqb_spec c c0) as [<-|N]; [|lia].
        rewrite G in Hi. subst i.
        destruct (Nat.eq_dec k (pcs s c)) as [Ek|Nk].
        -- destruct Hor as [(Z & _)|(t1 & _ & Ci & _)]; [rewrite <- Ek in Z; congruence|discriminate].
        -- apply (Hh eq_refl k Plain xs Hp Nk). apply guard_tied.
      * unfold searly, set_es, searly0, evs in G1; cbn [pcs] in G1. lia.
      * unfold smatch in G1; cbn [pcs] in G1. unfold upd in G1. destruct (Nat.eqb_spec c c0) as [<-|N]; [|lia].
        rewrite G in E0. discriminate.
      * unfold sread in G1; cbn [pcs] in G1. lia.
      * unfold sskip in G1; cbn [pcs] in G1. unfold upd in G1. destruct (Nat.eqb_spec c c0) as [<-|N]; [|lia].
        rewrite G, xex_guard in X0. discriminate.
      * unfold scfix0 in G1; cbn [pcs] in G1; rewrite pcs_flp in G1. lia.
Qed.

Print Assumptions rw_ent.
Print Assumptions wch_INVF.
Print Assumptions pcs_step_le.
Print Assumptions new_slot.
Print Assumptions ent_new_pcs.
Print Assumptions no_past_guard_h.
