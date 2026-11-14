(* Part 58: the guard() invariant J of an A run, one step at a time.
   J s:
   - j1: an item c knows (P, A) that is not c's own store is OK (in vOg(c), or c's next step is
     a guard() or a fenced access: M2DQWBK57.NF);
   - j2: c's own store that guard() has published (G) or another context knows (P, A) is OK;
   - j3: what c knows in order (vO) it knows in order through guard() (vOg), up to a double
     negation (guard.rl() adds an own store only if G holds it, which is not decidable).
   RaceStep s s': at the step's new entry, a store y of another context that the entry read is
   ordered by a guard() pair (a guard() of y's context after y, then a guard() of the reader
   before the step, both events of s), or y's slot is fenced and passed and the reader is in
   NF after the step.  J_step: J goes along a step that satisfies RaceStep. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO.
Require Import M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB.
Require Import M2DQWBK1 M2DQWBK3 M2DQWBK15 M2DQWBK20 M2DQWBK22 M2DQWBK29 M2DQWBK32 M2DQWBK33 M2DQWBK57.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

Section J.
Variable p : prog.
Hypothesis W : wf p.

Definition G1' : nat -> Prop := fun _ => False.

Definition Kn (s : st) (c a : nat) : Prop :=
  vG s a \/ exists d, d <> c /\ (vP (cs s d) a \/ vA (cs s d) a).

Record J (s : st) : Prop := {
  j1 : forall c a, ~ ownw s c a -> (vP (cs s c) a \/ vA (cs s c) a) -> OK p s c a;
  j2 : forall c a, ownw s c a -> Kn s c a -> OK p s c a;
  j3 : forall c a, vO (cs s c) a -> ~ ~ vOg (cs s c) a
}.

Definition SyncY (s s' : st) (c d y : nat) (ey : oev) : Prop :=
  (exists t1 F1 t2 F2, ent s t1 = Some F1 /\ isFF s t1 F1 /\ ec F1 = c /\ y < t1 /\
     ent s t2 = Some F2 /\ isFF s t2 F2 /\ ec F2 = d /\ t1 < t2) \/
  (fa p c (ek ey) /\ ek ey < pcs s c /\ NF p s' d).

Definition RaceStep (s s' : st) : Prop :=
  forall e x y ey, ent s' (tm s) = Some e -> erf e x = Some y -> ent s y = Some ey -> ec ey <> ec e ->
    SyncY s s' (ec ey) (ec e) y ey.

Lemma J_init : J sinit.
Proof.
  constructor; intros c a; cbn; unfold vnil.
  - intros _ [Z|Z]; contradiction.
  - intros (e & E & _). destruct a; discriminate.
  - intros Z; contradiction.
Qed.

Lemma ownw_uniq : forall s c c' z, ownw s c z -> ownw s c' z -> c = c'.
Proof. intros s c c' z (e & E & C & _) (e' & E' & C' & _). rewrite E in E'. injection E' as <-. congruence. Qed.

(* ---------- what a run state gives through its self image ---------- *)
Section Run.
Variable s : st.
Hypothesis R : run p s.

Let SI := self_image p G1' s W R.
Let Rl := proj1 SI.
Let K := proj2 SI.
Let Wk := WK_run p W s (Q_in_WB p s R).
Let I := Inv1_run p s R.

Lemma A_flag : forall x y, In y (ids (hs s x)) -> In (y, false) (hs s x).
Proof.
  intros x y Iy. destruct (in_ids_fl _ _ Iy) as [[|] H]; [|exact H].
  destruct (w_bet False G1' sw0 s s K x y H) as (f & Sf & _). discriminate.
Qed.

(* what a store conveys, and the store itself, is in what a later guard() of its context knew *)
Lemma zin_eP : forall c y ey x z t1 F1, ent s y = Some ey -> ec ey = c -> ew ey = true ->
  In y (ids (hs s x)) -> ent s t1 = Some F1 -> isFF s t1 F1 -> ec F1 = c -> y < t1 ->
  (z = y \/ wc s y z) -> eP F1 z.
Proof.
  intros c y ey x z t1 F1 Ey Cy Wy Iy E1 FF C1 Ly Z.
  assert (Oy : ownw s (ec F1) y) by (exists ey; unfold ent in Ey; rewrite C1; auto).
  destruct Z as [->|Z]; [exact (w_OWG False G1' sw0 s s K t1 F1 y E1 FF Oy Ly)|].
  destruct (wk_ug s Wk y ey t1 F1 x Ey Wy (A_flag x y Iy) E1 FF ltac:(congruence) Ly z Z) as [Z1|Z1]; [exact Z1|].
  rewrite Z1. exact (w_OWG False G1' sw0 s s K t1 F1 y E1 FF Oy Ly).
Qed.

(* a fenced store whose guard() after it was passed: that guard() is an event after it *)
Lemma guard_after : forall c ky y ey x, fa p c ky -> S ky < pcs s c -> ent s y = Some ey -> ec ey = c ->
  ek ey = ky -> ew ey = true -> In y (ids (hs s x)) ->
  exists tg F, ent s tg = Some F /\ isFF s tg F /\ ec F = c /\ y < tg.
Proof.
  intros c ky y ey x (L1 & Fa) Lk Ey Cy Ky Wy Iy.
  assert (Lu : ek ey < pcs s (ec ey)) by (rewrite Cy, Ky; lia).
  destruct (kept_slot p False G1' sw0 s s y ey x R Rl K Ey (A_flag x y Iy) Lu) as (Ou & Ex).
  rewrite Cy, Ky in Ou, Ex.
  assert (Gp : forall r, ins p c (S ky) r = IFn FFull) by (intros r; exact (proj2 (Fa r))).
  destruct (guard_oc p s c (S ky) I Lk Gp) as (_ & tg & Og).
  destruct (i_oc p s I c (S ky) tg Og) as (F & EF & CF & KF).
  destruct (proj1 (i_cmA p s I c (S ky)) Lk) as (tau & Inm).
  assert (Ai : ai (cs s c) (S ky) = IFn FFull) by (rewrite (proj2 (i_set p s I c (S ky) tau Inm)); exact (Gp _)).
  destruct (i_pot p s I c ky (S ky) tg ltac:(lia) Lk (tmo_oc _ _ _ Og) Ex
              ltac:(rewrite (Gp (rg (cs s c))); right; right; left; reflexivity)) as (tj & Tj & Lt).
  rewrite (tmo_oc _ _ _ Ou) in Tj. injection Tj as <-.
  exists tg, F. split; [exact EF|]. split; [|split; [exact CF|exact Lt]].
  unfold isFF. rewrite CF, KF. auto.
Qed.
End Run.

(* ---------- what a step does to P, A and G ---------- *)
Lemma eff_PA : forall t i r m m' a K u w z, eff t i r m m' a K u w ->
  (mP m' z -> mP m z \/ mA m z \/ (i = IFn FFull /\ mG m z) \/ (exists x, u x = Some z) \/ (w = true /\ z = t)) /\
  (mA m' z -> mA m z \/ (exists x y, u x = Some y /\ (mC m y z \/ z = y))) /\
  (mG m' z -> mG m z \/ (i = IFn FFull /\ (mP m z \/ mA m z)) \/ (i = IFn FSl /\ mW m z)) /\
  (i = IFn FFull -> w = false /\ vsub (mA m') (mP m') /\ vsub (mG m') (mP m')) /\
  (i = IFn FSl -> w = false).
Proof.
  intros t i r m m' a K u w z H. inversion H; subst; cbn [mP mA mG mW learn wput gpre gpost]; unfold vor, vone, srcs, carrieds, vsub.
  - split; [tauto|]. split; [tauto|]. split; [tauto|]. split; intros E; subst; discriminate.
  - split; [intros [Z|Z]; tauto|]. split; [intros [Z|Z]; [tauto|right; destruct Z as (x & y & U & C); eauto]|].
    split; [tauto|]. split; intros E; discriminate.
  - split; [intros [Z|Z]; [tauto|right; right; right; right; auto]|]. split; [tauto|]. split; [tauto|]. split; intros E; discriminate.
  - split; [intros [[Z|Z]|Z]; [tauto|right; right; right; left; exact Z|right; right; right; right; auto]|].
    split; [intros [Z|Z]; [tauto|right; destruct Z as (x & y & U & C); eauto]|].
    split; [tauto|]. split; intros E; discriminate.
  - split; [intros [Z|Z]; tauto|]. split; [intros [Z|Z]; [tauto|right; destruct Z as (x & y & U & C); eauto]|].
    split; [tauto|]. split; intros E; discriminate.
  - split; [intros [Z|Z]; tauto|]. split; [tauto|]. split; [tauto|]. split; intros E; discriminate.
  - split; [tauto|]. split; [tauto|]. split; [tauto|]. split; intros E; discriminate.
  - split; [tauto|]. split; [tauto|]. split; [tauto|]. split; intros E; discriminate.
  - split; [tauto|]. split; [tauto|]. split; [intros [Z|Z]; tauto|]. split; intros E; [discriminate|reflexivity].
  - split; [intros [[[Z|Z]|Z]|Z]; tauto|]. split; [tauto|]. split; [intros [[[Z|Z]|Z]|Z]; tauto|].
    split; [intros _; split; [reflexivity|split; intros q Q; tauto]|intros E; discriminate].
  - split; [tauto|]. split; [tauto|]. split; [tauto|]. split; intros E; discriminate.
Qed.

(* ---------- learning from a read ---------- *)
Section Learn.
Variables (s s' : st).
Hypothesis R : run p s.
Hypothesis St : step p s s'.
Hypothesis Js : J s.
Hypothesis RS : RaceStep s s'.

Let SI := self_image p G1' s W R.
Let K := proj2 SI.
Let Wk := WK_run p W s (Q_in_WB p s R).
Let I3 := iao3 p s (InvO_run p s R).

(* an item the reader c learns from a store y it read, not its own store *)
Lemma learn_ok : forall e x y ey z, ent s' (tm s) = Some e -> erf e x = Some y -> ent s y = Some ey ->
  ew ey = true -> In y (ids (hs s x)) -> (z = y \/ wc s y z) -> ~ ownw s (ec e) z ->
  (forall q, vOg (cs s (ec e)) q -> vOg (cs s' (ec e)) q) -> OK p s' (ec e) z.
Proof.
  intros e x y ey z Ee Ex Ey Wy Iy Z Nz Og.
  destruct (Nat.eq_dec (ec ey) (ec e)) as [Ce|Ce].
  - assert (Nzy : z <> y) by (intros ->; apply Nz; exists ey; unfold ent in Ey; auto).
    destruct Z as [Z|Z]; [contradiction|].
    destruct (wk_R s Wk y ey Ey Wy z Z) as [Zr|Zr]; [|contradiction].
    rewrite Ce in Zr. destruct (k_RP p s I3 (ec e) z Zr) as [Zp|Za].
    + apply (OK_step p W s s' R St (ec e) z (j1 s Js (ec e) z Nz (or_introl Zp))). left. exact Zp.
    + apply (OK_step p W s s' R St (ec e) z (j1 s Js (ec e) z Nz (or_intror Za))). right; left. exact Za.
  - destruct (RS e x y ey Ee Ex Ey Ce) as [(t1 & F1 & t2 & F2 & E1 & FF1 & C1 & L1 & E2 & FF2 & C2 & L2)|(_ & _ & Nf)].
    + left. apply Og. pose proof (zin_eP s R (ec ey) y ey x z t1 F1 Ey eq_refl Wy Iy E1 FF1 C1 L1 Z) as Z1.
      pose proof (wk_gg s Wk t1 F1 t2 F2 E1 FF1 E2 FF2 L2 z Z1) as Z2.
      pose proof (proj1 (w_OGP False G1' sw0 s s K t2 F2 E2 FF2) z Z2) as Z3. rewrite C2 in Z3. exact Z3.
    + right. exact Nf.
Qed.

(* a store of c0 that another context c learns from a store y it read *)
Lemma learn_own : forall e x y ey z c0, ent s' (tm s) = Some e -> erf e x = Some y -> ent s y = Some ey ->
  ew ey = true -> In y (ids (hs s x)) -> (z = y \/ wc s y z) -> ownw s c0 z -> c0 <> ec e ->
  cs s' c0 = cs s c0 -> pcs s' c0 = pcs s c0 -> OK p s' c0 z.
Proof.
  intros e x y ey z c0 Ee Ex Ey Wy Iy Z Oz Nc Cs Pc.
  assert (OKs : OK p s c0 z -> OK p s' c0 z).
  { intros Ok. apply (OK_step p W s s' R St c0 z Ok). left. exact (w_OW False G1' sw0 s s K c0 z Oz). }
  destruct (Nat.eq_dec (ec ey) c0) as [Cy|Cy].
  - assert (Ce : ec ey <> ec e) by congruence.
    destruct (RS e x y ey Ee Ex Ey Ce) as [(t1 & F1 & t2 & F2 & E1 & FF1 & C1 & L1 & _)|(Fa & Lk & _)].
    + apply OKs. left. pose proof (zin_eP s R (ec ey) y ey x z t1 F1 Ey eq_refl Wy Iy E1 FF1 C1 L1 Z) as Z1.
      pose proof (proj1 (w_OGP False G1' sw0 s s K t1 F1 E1 FF1) z Z1) as Z3. rewrite C1, Cy in Z3. exact Z3.
    + destruct (Nat.lt_ge_cases (S (ek ey)) (pcs s (ec ey))) as [Lg|Lg].
      * destruct (guard_after s R (ec ey) (ek ey) y ey x Fa Lg Ey eq_refl eq_refl Wy Iy) as (tg & Fg & Eg & FFg & Cg & Ltg).
        apply OKs. left. pose proof (zin_eP s R (ec ey) y ey x z tg Fg Ey eq_refl Wy Iy Eg FFg Cg Ltg Z) as Z1.
        pose proof (proj1 (w_OGP False G1' sw0 s s K tg Fg Eg FFg) z Z1) as Z3. rewrite Cg, Cy in Z3. exact Z3.
      * right. left. intros r. rewrite Pc, <- Cy. replace (pcs s (ec ey)) with (S (ek ey)) by lia.
        exact (proj2 ((proj2 Fa) r)).
  - assert (Nzy : z <> y) by (intros ->; apply Cy; exact (ownw_uniq s (ec ey) c0 y (ex_intro _ ey (conj Ey (conj eq_refl Wy))) Oz)).
    destruct Z as [Z|Z]; [contradiction|].
    destruct (wk_R s Wk y ey Ey Wy z Z) as [Zr|Zr]; [|contradiction].
    apply OKs. apply (j2 s Js c0 z Oz). right. exists (ec ey). split; [exact Cy|].
    exact (k_RP p s I3 (ec ey) z Zr).
Qed.
End Learn.

End J.

Print Assumptions learn_ok.
Print Assumptions learn_own.
