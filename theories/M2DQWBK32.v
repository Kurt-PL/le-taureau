(* Part 32: the both-fenced case of (WBC'') on the state side, from the A image.  A store u at a fenced slot ku of context c (fa p c ku) whose
   following guard() (slot ku+1) has been passed: in the A run, every event of c strictly between
   the guard() at ku-1 (time g) and u is a CAS's read alone (fa_quietA):
     - slots below ku-1 happened before the guard() at ku-1 was passed (M2DQWBK14.JE_run);
     - slots above ku+1 happened after the guard() at ku+1 (i_pot if passed, i_ptiet if pending),
       which happened after u (i_pot);
   through the structural part of KR this is quietH in the write-back state (quietH_AW), the guard()
   at ku-1 is a guard() event there (M2DQWBK26.isFF_AW), and M2DQWBK31.faH_wc gives
       wc u <= vG u {u}      (fa_wb). *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO M2SC MIPComp MIPNeg M2Iface MIPSync.
Require Import M2Lit M2Trace M2DQTrace M2IfaceInst M2DQIfaceInst M2WBRel M2DQWB M2DQWBK1 M2DQWBK3 M2DQWBK14 M2DQWBK22 M2DQWBK24 M2DQWBK26 M2DQWBK31.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBQb M2DQWBK1Q M2DQShim M2DQTr.

Lemma tmo_oc : forall cc j t, oc cc j = Some t -> tmo cc j = Some t.
Proof. intros cc j t O. unfold tmo. rewrite O. reflexivity. Qed.

Lemma guard_tied : forall i, tied (IFn FFull) i.
Proof. intros i. right. left. reflexivity. Qed.

Lemma guard_oc : forall p s c j, Inv1 p s -> j < pcs s c -> (forall r, ins p c j r = IFn FFull) ->
  oc (cs s c) j <> None /\ exists t, oc (cs s c) j = Some t.
Proof.
  intros p s c j I L G. destruct (proj1 (i_cmA p s I c j) L) as (tau & In').
  assert (O : oc (cs s c) j = Some tau) by (apply (i_cmF p s I c j tau In'); rewrite G; reflexivity).
  split; [congruence|eauto].
Qed.

Theorem fa_quietA : forall p s c ku u, wf p -> run p s -> fa p c ku -> S ku < pcs s c ->
  oc (cs s c) ku = Some u -> executes (ins p c ku (rg (cs s c))) (rg (cs s c)) = true ->
  exists g, oc (cs s c) (ku - 1) = Some g /\ g < u /\
    forall t e, g < t -> t < u -> ent s t = Some e -> ec e = c -> eh e = true.
Proof.
  intros p s c ku u W R (L1 & Fa) Lk Ou Ex. pose proof (Inv1_run p s R) as I.
  assert (Gm : forall r, ins p c (ku - 1) r = IFn FFull) by (intros r; exact (proj1 (Fa r))).
  assert (Gp : forall r, ins p c (S ku) r = IFn FFull) by (intros r; exact (proj2 (Fa r))).
  destruct (proj1 (i_cmA p s I c (ku - 1)) ltac:(lia)) as (tau & Inm).
  assert (Og : oc (cs s c) (ku - 1) = Some tau) by (apply (i_cmF p s I c (ku - 1) tau Inm); rewrite Gm; reflexivity).
  destruct (guard_oc p s c (S ku) I Lk Gp) as (_ & tg & Ogp).
  (* u < tg *)
  assert (Utg : u < tg).
  { destruct (i_pot p s I c ku (S ku) tg ltac:(lia) Lk (tmo_oc _ _ _ Ogp) Ex
       ltac:(rewrite (Gp (rg (cs s c))); right; right; left; reflexivity)) as (tj & Tj & Lt).
    rewrite (tmo_oc _ _ _ Ou) in Tj. injection Tj as <-. exact Lt. }
  (* g < u *)
  assert (Gu : tau < u).
  { destruct (i_pot p s I c (ku - 1) ku u ltac:(lia) ltac:(lia) (tmo_oc _ _ _ Ou)
       ltac:(rewrite (Gm (rg (cs s c))); reflexivity) ltac:(rewrite (Gm (rg (cs s c))); apply guard_tied)) as (tj & Tj & Lt).
    rewrite (tmo_oc _ _ _ Og) in Tj. injection Tj as <-. exact Lt. }
  exists tau. split; [exact Og|]. split; [exact Gu|].
  intros t e L2 L3 E C. destruct (eh e) eqn:Eh; [reflexivity|exfalso].
  destruct (i_et p s I t e E) as (Et & Oe). rewrite Eh, C in Oe.
  destruct (Nat.lt_trichotomy (ek e) (ku - 1)) as [Lj|[Ej|Gj]].
  - (* an earlier slot: before the guard() at ku-1 was passed *)
    pose proof (JE_run p s R t e (ku - 1) tau E ltac:(rewrite C; exact Inm) Lj). lia.
  - rewrite Ej, Og in Oe. injection Oe as <-. lia.
  - destruct (Nat.eq_dec (ek e) ku) as [Ek|Nk]; [rewrite Ek, Ou in Oe; injection Oe as <-; lia|].
    destruct (Nat.eq_dec (ek e) (S ku)) as [Ek|Nk2]; [rewrite Ek, Ogp in Oe; injection Oe as <-; lia|].
    assert (Tg : tg < t).
    { destruct (Nat.lt_ge_cases (ek e) (pcs s c)) as [Lp|Gp'].
      - destruct (i_pot p s I c (S ku) (ek e) t ltac:(lia) Lp (tmo_oc _ _ _ Oe)
           ltac:(rewrite (Gp (rg (cs s c))); reflexivity) ltac:(rewrite (Gp (rg (cs s c))); apply guard_tied)) as (tj & Tj & Lt).
        rewrite (tmo_oc _ _ _ Ogp) in Tj. injection Tj as <-. exact Lt.
      - destruct (proj1 (i_pend p s I c (ek e) Gp' ltac:(congruence))) as (d & Ad & _).
        destruct (i_ptiet p s I c (ek e) t d (S ku) ltac:(split; [exact Gp'|split; [congruence|exact Ad]]) Oe Lk
           ltac:(rewrite (Gp (rg (cs s c))); reflexivity) ltac:(rewrite (Gp (rg (cs s c))); apply guard_tied)) as (tj & Tj & Lt).
        rewrite (tmo_oc _ _ _ Ogp) in Tj. injection Tj as <-. exact Lt. }
    lia.
Qed.

(* a run that ends finished never records an event at or beyond a guard() its context has not
   passed: that guard() must be passed later (it is before the end), by s_ord, which requires that
   no pending access is tied to it, and guard() is tied to every access *)
Lemma xex_guard : forall cc r k, xex cc (IFn FFull) r k = true.
Proof. intros. unfold xex, xexec. cbn. rewrite andb_false_r. reflexivity. Qed.

Lemma no_past_guard : forall p s sf c jg k, wf p -> run p s -> star p s sf -> done p sf ->
  (forall r, ins p c jg r = IFn FFull) -> pcs s c <= jg -> jg <= k -> oc (cs s c) k = None.
Proof.
  intros p s sf c jg k W R S D G.
  induction S as [s|s s1 sf St S IH]; intros L1 L2.
  - destruct (oc (cs s c) k) as [t|] eqn:O; [exfalso|reflexivity].
    pose proof (Inv1_run p s R) as I.
    assert (Cl : c < length p) by (exact (proj2 (i_pend p s I c k ltac:(lia) ltac:(congruence)))).
    destruct D as (n & Fn & Cp). destruct (Cp c Cl) as [Ln _].
    destruct (Nat.lt_ge_cases jg (n c)) as [Lj|Gj]; [lia|].
    specialize (Fn c jg (rg (cs s c)) Gj). rewrite G in Fn. discriminate.
  - pose proof (Inv1_run p s R) as I. pose proof (Ext_step p s s1 R St) as X.
    destruct (oc (cs s c) k) as [t|] eqn:O; [exfalso|reflexivity].
    assert (O1 : oc (cs s1 c) k = Some t) by exact (x_oc s s1 X c k t O).
    destruct (Nat.le_gt_cases (pcs s1 c) jg) as [L1'|G1].
    + rewrite (IH (rS p s s1 R St) D L1' L2) in O1. discriminate.
    + (* the step passes jg *)
      destruct (stepQ_split p s s1 St) as [[StA _]|RF]; [|exfalso; rewrite (rfx_pcs _ _ RF) in G1; lia].
      assert (Pj : pcs s c = jg).
      { destruct (step_cases p s s1 StA) as
          [(c0 & i & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ->)
          |[(c0 & k0 & d & B & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & _ & _ & ->)
          |[(c0 & d & _ & _ & _ & _ & _ & _ & ->)
          |[(c0 & k0 & xs0 & B & m' & a & K & u & w & bv & _ & _ & _ & _ & _ & _ & _ & ->)
          |[(c0 & _ & _ & _ & _ & _ & _ & _ & ->)
          |(cX & jX & bX & BX & oX & _ & _ & _ & ->)]]]]].
        all: try (unfold sord, evs in G1; cbn [pcs] in G1).
        all: try (unfold searly, set_es, searly0, evs in G1; cbn [pcs] in G1).
        all: try (unfold smatch in G1; cbn [pcs] in G1).
        all: try (unfold sread in G1; cbn [pcs] in G1).
        all: try (unfold sskip in G1; cbn [pcs] in G1).
        all: try (unfold scfix0 in G1; cbn [pcs] in G1; rewrite pcs_flp in G1).
        all: try lia.
        all: unfold upd in G1; destruct (Nat.eqb_spec c c0) as [->|N]; lia. }
      subst jg.
      destruct (proj1 (i_pend p s I c k L2 ltac:(congruence))) as (d & Ad & _).
      assert (Pd : pending (cs s c) (pcs s c) k d) by (split; [exact L2|split; [congruence|exact Ad]]).
      destruct (step_cases p s s1 StA) as
          [(c0 & i & m' & a & K & u & w & Hi & _ & _ & Hp & _ & _ & _ & _ & _ & _ & ->)
          |[(c0 & k0 & d0 & B & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & _ & _ & ->)
          |[(c0 & d0 & S1 & _ & E0 & _ & _ & _ & ->)
          |[(c0 & k0 & xs0 & B & m' & a & K & u & w & bv & _ & _ & _ & _ & _ & _ & _ & ->)
          |[(c0 & X0 & _ & _ & _ & _ & _ & _ & ->)
          |(cX & jX & bX & BX & oX & _ & _ & _ & ->)]]]]].
      * unfold sord, evs in G1; cbn [pcs] in G1. unfold upd in G1. destruct (Nat.eqb_spec c c0) as [<-|N]; [|lia].
        rewrite G in Hi. subst i. apply (Hp eq_refl k d Pd). apply guard_tied.
      * unfold searly, set_es, searly0, evs in G1; cbn [pcs] in G1. lia.
      * unfold smatch in G1; cbn [pcs] in G1. unfold upd in G1. destruct (Nat.eqb_spec c c0) as [<-|N]; [|lia].
        rewrite G in E0. discriminate.
      * unfold sread in G1; cbn [pcs] in G1. lia.
      * unfold sskip in G1; cbn [pcs] in G1. unfold upd in G1. destruct (Nat.eqb_spec c c0) as [<-|N]; [|lia].
        rewrite G, xex_guard in X0. discriminate.
      * unfold scfix0 in G1; cbn [pcs] in G1; rewrite pcs_flp in G1. lia.
Qed.

(* fa_quietA when the guard() after u has not been passed, given that nothing is recorded at or
   beyond it (no_past_guard) *)
Theorem fa_quietA0 : forall p s c ku u, wf p -> run p s -> fa p c ku -> S ku = pcs s c ->
  (forall k, S ku <= k -> oc (cs s c) k = None) -> oc (cs s c) ku = Some u ->
  executes (ins p c ku (rg (cs s c))) (rg (cs s c)) = true ->
  exists g, oc (cs s c) (ku - 1) = Some g /\ g < u /\
    forall t e, g < t -> t < u -> ent s t = Some e -> ec e = c -> eh e = true.
Proof.
  intros p s c ku u W R (L1 & Fa) Lk NP Ou Ex. pose proof (Inv1_run p s R) as I.
  assert (Gm : forall r, ins p c (ku - 1) r = IFn FFull) by (intros r; exact (proj1 (Fa r))).
  destruct (proj1 (i_cmA p s I c (ku - 1)) ltac:(lia)) as (tau & Inm).
  assert (Og : oc (cs s c) (ku - 1) = Some tau) by (apply (i_cmF p s I c (ku - 1) tau Inm); rewrite Gm; reflexivity).
  assert (Gu : tau < u).
  { destruct (i_pot p s I c (ku - 1) ku u ltac:(lia) ltac:(lia) (tmo_oc _ _ _ Ou)
       ltac:(rewrite (Gm (rg (cs s c))); reflexivity) ltac:(rewrite (Gm (rg (cs s c))); apply guard_tied)) as (tj & Tj & Lt).
    rewrite (tmo_oc _ _ _ Og) in Tj. injection Tj as <-. exact Lt. }
  exists tau. split; [exact Og|]. split; [exact Gu|].
  intros t e L2 L3 E C. destruct (eh e) eqn:Eh; [reflexivity|exfalso].
  destruct (i_et p s I t e E) as (Et & Oe). rewrite Eh, C in Oe.
  destruct (Nat.lt_trichotomy (ek e) (ku - 1)) as [Lj|[Ej|Gj]].
  - pose proof (JE_run p s R t e (ku - 1) tau E ltac:(rewrite C; exact Inm) Lj). lia.
  - rewrite Ej, Og in Oe. injection Oe as <-. lia.
  - destruct (Nat.eq_dec (ek e) ku) as [Ek|Nk]; [rewrite Ek, Ou in Oe; injection Oe as <-; lia|].
    rewrite (NP (ek e) ltac:(lia)) in Oe. discriminate.
Qed.

(* the same in a write-back state with an image (structural KR: entries keep context and eh) *)
Lemma quietH_AW : forall Fk Good sw sW sA c a b, rel sw sW sA -> KR Fk Good sw sW sA ->
  (forall t e, a < t -> t < b -> ent sA t = Some e -> ec e = c -> eh e = true) -> quietH sW c a b.
Proof.
  intros Fk Good sw sW sA c a b Rl K Q t eW L1 L2 EW C.
  assert (EA : exists eA, ent sA t = Some eA).
  { destruct (ent sA t) as [eA|] eqn:H; [eauto|]. exfalso. unfold ent in H, EW.
    apply nth_error_None in H. rewrite (k_len Fk Good sw sW sA K) in H.
    assert (Lt : t < length (lg sW)) by (apply nth_error_Some; congruence). lia. }
  destruct EA as (eA & EA). destruct (k_ent Fk Good sw sW sA K t eA EA) as (eW' & EW' & (_ & S2 & _ & _ & _ & S6 & _)).
  rewrite EW in EW'. injection EW' as <-. rewrite <- S6. apply (Q t eA L1 L2 EA). rewrite S2. exact C.
Qed.

(* (WBC'') in the both-fenced case, the guard() after u passed: wc u <= vG u {u} *)
Theorem fa_wb : forall p Fk Good sw sW sA c ku u eu x, wf p -> run p sA -> rel sw sW sA -> KR Fk Good sw sW sA ->
  runWB p sW -> fa p c ku -> S ku < pcs sW c ->
  oc (cs sW c) ku = Some u -> executes (ins p c ku (rg (cs sW c))) (rg (cs sW c)) = true ->
  ent sW u = Some eu -> ew eu = true -> In (u, false) (hs sW x) ->
  vsub (wc sW u) (vor (vG sW) (vone u)).
Proof.
  intros p Fk Good sw sW sA c ku u eu x W RA Rl K RW Fa Lk Ou Ex Eu Ew Iu.
  destruct (crel_eq p Fk Good sw sW sA RA Rl K c) as (OcE & _ & AiE & RgE & _).
  assert (LkA : S ku < pcs sA c) by (rewrite (r_pcs sw sW sA Rl); exact Lk).
  assert (OuA : oc (cs sA c) ku = Some u) by (rewrite OcE; exact Ou).
  assert (ExA : executes (ins p c ku (rg (cs sA c))) (rg (cs sA c)) = true) by (rewrite RgE; exact Ex).
  destruct (fa_quietA p sA c ku u W RA Fa LkA OuA ExA) as (g & Og & Lg & Q).
  pose proof (Inv1_run p sA RA) as I.
  destruct (i_oc p sA I c (ku - 1) g Og) as (F & EF & CF & KF).
  destruct Fa as (L1 & Fa).
  assert (IF : einstr p sA F = IFn FFull).
  { unfold einstr. rewrite CF, KF. destruct (proj1 (i_cmA p sA I c (ku - 1)) ltac:(lia)) as (tau & Inm).
    rewrite (proj2 (i_set p sA I c (ku - 1) tau Inm)). exact (proj1 (Fa _)). }
  destruct (isFF_AW p Fk Good sw sW sA RA Rl K c (ku - 1) g F EF CF KF IF ltac:(lia) Og) as (FW & EW & FF & CW & _).
  assert (Cu : ec eu = c).
  { destruct (i_oc p sA I c ku u OuA) as (U & EU & CU & _). rewrite <- CU.
    exact (ent_ec p Fk Good sw sW sA RA Rl K u U eu EU Eu). }
  apply (faH_wc p W sW RW g FW u eu x EW FF Eu Ew Iu ltac:(congruence) Lg).
  rewrite CW. exact (quietH_AW Fk Good sw sW sA c g u Rl K Q).
Qed.

(* the tail of fa_wb, from the A-side quiet fact *)
Lemma fa_wb_of_quiet : forall p Fk Good sw sW sA c ku u eu x g, wf p -> run p sA -> rel sw sW sA -> KR Fk Good sw sW sA ->
  runWB p sW -> fa p c ku -> ku - 1 < pcs sA c -> oc (cs sA c) ku = Some u ->
  oc (cs sA c) (ku - 1) = Some g -> g < u -> (forall t e, g < t -> t < u -> ent sA t = Some e -> ec e = c -> eh e = true) ->
  ent sW u = Some eu -> ew eu = true -> In (u, false) (hs sW x) ->
  vsub (wc sW u) (vor (vG sW) (vone u)).
Proof.
  intros p Fk Good sw sW sA c ku u eu x g W RA Rl K RW Fa Lg1 OuA Og Lg Q Eu Ew Iu.
  pose proof (Inv1_run p sA RA) as I.
  destruct (i_oc p sA I c (ku - 1) g Og) as (F & EF & CF & KF).
  destruct Fa as (L1 & Fa).
  assert (IF : einstr p sA F = IFn FFull).
  { unfold einstr. rewrite CF, KF. destruct (proj1 (i_cmA p sA I c (ku - 1)) Lg1) as (tau & Inm).
    rewrite (proj2 (i_set p sA I c (ku - 1) tau Inm)). exact (proj1 (Fa _)). }
  destruct (isFF_AW p Fk Good sw sW sA RA Rl K c (ku - 1) g F EF CF KF IF Lg1 Og) as (FW & EW & FF & CW & _).
  assert (Cu : ec eu = c).
  { destruct (i_oc p sA I c ku u OuA) as (U & EU & CU & _). rewrite <- CU.
    exact (ent_ec p Fk Good sw sW sA RA Rl K u U eu EU Eu). }
  apply (faH_wc p W sW RW g FW u eu x EW FF Eu Ew Iu ltac:(congruence) Lg).
  rewrite CW. exact (quietH_AW Fk Good sw sW sA c g u Rl K Q).
Qed.

(* (WBC'') both-fenced case for a passed store u: the guard() after it passed, or the image's run
   goes on to a finished state *)
Theorem fa_wb_all : forall p Fk Good sw sW sA c ku u eu x, wf p -> run p sA -> rel sw sW sA -> KR Fk Good sw sW sA ->
  runWB p sW -> fa p c ku -> ku < pcs sW c ->
  (S ku < pcs sW c \/ exists sAf, star p sA sAf /\ done p sAf) ->
  oc (cs sW c) ku = Some u -> executes (ins p c ku (rg (cs sW c))) (rg (cs sW c)) = true ->
  ent sW u = Some eu -> ew eu = true -> In (u, false) (hs sW x) ->
  vsub (wc sW u) (vor (vG sW) (vone u)).
Proof.
  intros p Fk Good sw sW sA c ku u eu x W RA Rl K RW Fa Lk Fut Ou Ex Eu Ew Iu.
  destruct (Nat.lt_ge_cases (S ku) (pcs sW c)) as [Lt|Ge]; [exact (fa_wb p Fk Good sw sW sA c ku u eu x W RA Rl K RW Fa Lt Ou Ex Eu Ew Iu)|].
  destruct Fut as [Lt|(sAf & Sf & D)]; [lia|].
  destruct (crel_eq p Fk Good sw sW sA RA Rl K c) as (OcE & _ & AiE & RgE & _).
  assert (Pk : S ku = pcs sA c) by (rewrite (r_pcs sw sW sA Rl); lia).
  assert (OuA : oc (cs sA c) ku = Some u) by (rewrite OcE; exact Ou).
  assert (ExA : executes (ins p c ku (rg (cs sA c))) (rg (cs sA c)) = true) by (rewrite RgE; exact Ex).
  assert (NP : forall k, S ku <= k -> oc (cs sA c) k = None).
  { intros k Lk'. apply (no_past_guard p sA sAf c (S ku) k W RA Sf D (fun r => proj2 (proj2 Fa r)) ltac:(lia) Lk'). }
  destruct (fa_quietA0 p sA c ku u W RA Fa Pk NP OuA ExA) as (g & Og & Lg & Q).
  exact (fa_wb_of_quiet p Fk Good sw sW sA c ku u eu x g W RA Rl K RW Fa ltac:(lia) OuA Og Lg Q Eu Ew Iu).
Qed.

Print Assumptions fa_quietA.
Print Assumptions fa_wb.
Print Assumptions no_past_guard.
Print Assumptions fa_quietA0.
Print Assumptions fa_wb_all.
