(* Part 10: the steps that log nothing keep KR (reaching an access performed early,
   passing an instruction that does not execute, fixing a CAS's result). *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB M2DQWBK1 M2DQWBK2 M2DQWBK3 M2DQWBK7 M2DQWBK8.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQShim.

Lemma eof_iscas : forall i r d, eof i r = Some d -> is_cas (inst_of d) = is_cas i.
Proof.
  intros [m x c0|m x c0 v|m x c0 e n|f|] r d H; simpl in H; try discriminate.
  all: try (destruct f; [injection H as <-| injection H as <-| injection H as <-| injection H as <-|discriminate]; reflexivity).
  all: unfold dof in H; destruct (c0 r); [|discriminate]; injection H as <-; reflexivity.
Qed.

Lemma xex_FF : forall cc r k, xex cc (IFn FFull) r k = true.
Proof. intros. unfold xex, xexec, executes, cfail, cfailv. cbn. destruct (ohb cc k); reflexivity. Qed.

Section NL.
Set Default Proof Using "All".
Variables (p : prog) (Fk : Prop) (Good : nat -> Prop) (sw : nat -> option (cell -> option nat)) (sW sA : st) (c : nat).
Hypothesis RA : run p sA.
Hypothesis R : rel sw sW sA.
Hypothesis KK : KR Fk Good sw sW sA.

(* the context state after reaching or passing slot pcs with instruction ins *)
Lemma KR_pass : forall i, i <> IFn FFull ->
  (forall t f e, sw t = Some f -> ent sW t = Some e -> ec e = c -> ek e = pcs sW c -> is_cas i = true) ->
  forall tpW tpA cmW cmA iA kA pcA esA,
  KR Fk Good sw
    (mkS (tm sW) (upd (cs sW) c (mkC (oc (cs sW c)) (rg (cs sW c)) (upd (ai (cs sW c)) (pcs sW c) i) (rw (cs sW c)) (rv (cs sW c)) (bd (cs sW c))
                  (vP (cs sW c)) (vA (cs sW c)) (vR (cs sW c)) (vO (cs sW c)) (vOg (cs sW c)) (oh (cs sW c)) (fx (cs sW c))))
       (wv sW) (wc sW) (hs sW) (vG sW) (upd (pcs sW) c (S (pcs sW c))) tpW cmW (lg sW) (es sW))
    (mkS (tm sA) (upd (cs sA) c (mkC (oc (cs sA c)) (rg (cs sA c)) (upd (ai (cs sA c)) kA iA) (rw (cs sA c)) (rv (cs sA c)) (bd (cs sA c))
                  (vP (cs sA c)) (vA (cs sA c)) (vR (cs sA c)) (vO (cs sA c)) (vOg (cs sA c)) (oh (cs sA c)) (fx (cs sA c))))
       (wv sA) (wc sA) (hs sA) (vG sA) pcA tpA cmA (lg sA) esA).
Proof.
  intros i Ni Hc tpW tpA cmW cmA iA kA pcA esA.
  apply (KR_nolog p Fk Good sw sW sA _ _ RA R KK); try reflexivity.
  - intros c'. cbn [cs]. rewrite cs_upd. destruct (Nat.eqb_spec c' c) as [->|]; cbn; repeat split.
  - intros c'. cbn [cs]. rewrite cs_upd. destruct (Nat.eqb_spec c' c) as [->|]; cbn; repeat split.
  - intros c'. cbn [cs]. rewrite cs_upd. destruct (Nat.eqb_spec c' c) as [->|]; cbn; repeat split.
  - intros c'. cbn [pcs]. unfold upd. destruct (Nat.eqb_spec c' c) as [->|]; lia.
  - intros c' j. cbn [cs]. rewrite cs_upd. destruct (Nat.eqb_spec c' c) as [->|]; cbn; auto.
  - intros tf f E (Fa & Fp & Fo). cbn [cs pcs] in Fa, Fp, Fo. rewrite cs_upd in Fa, Fo.
    destruct (Nat.eqb_spec (ec f) c) as [Ec|Nc]; cbn [ai oc] in Fa, Fo.
    + rewrite Ec in Fp. rewrite upd_eq in Fp. destruct (Nat.eqb_spec (ek f) (pcs sW c)) as [Ek|Nk].
      * exfalso. rewrite Ek, upd_eq in Fa. exact (Ni Fa).
      * rewrite upd_neq in Fa by exact Nk. unfold isFF. rewrite Ec. split; [exact Fa|split; [lia|exact Fo]].
    + rewrite upd_neq in Fp by exact Nc. unfold isFF. auto.
  - intros t f e Sw E Cc. cbn [cs]. rewrite cs_upd. destruct (Nat.eqb_spec (ec e) c) as [Ec|Nc]; cbn [ai]; [|exact Cc].
    destruct (Nat.eqb_spec (ek e) (pcs sW c)) as [Ek|Nk].
    + rewrite Ek, upd_eq. exact (Hc t f e Sw E Ec Ek).
    + rewrite upd_neq by exact Nk. rewrite <- Ec. exact Cc.
Qed.
End NL.

Section CF.
Set Default Proof Using "All".
Variables (p : prog) (Fk : Prop) (Good : nat -> Prop) (sw : nat -> option (cell -> option nat)) (sW sA : st) (c j : nat) (b : bool) (B : nat -> bool) (o : option nat).
Hypothesis RA : run p sA.
Hypothesis R : rel sw sW sA.
Hypothesis KK : KR Fk Good sw sW sA.

Lemma cfixc_f : forall cc, oc (cfixc cc o j b B) = oc cc /\ oh (cfixc cc o j b B) = oh cc /\ ai (cfixc cc o j b B) = ai cc /\
  vP (cfixc cc o j b B) = vP cc /\ vA (cfixc cc o j b B) = vA cc /\ vOg (cfixc cc o j b B) = vOg cc /\
  forall j', rg (cfixc cc o j b B) j' = rg cc j' \/ vok (rg (cfixc cc o j b B) j') = false.
Proof.
  intros cc. unfold cfixc, scfix_cc, scfail_cc. destruct o as [k|]; [destruct b|]; cbn [oc oh ai vP vA vOg rg]; (split; [reflexivity|]);
    repeat (split; [reflexivity|]); intros j'; [left; reflexivity| |left; reflexivity].
  unfold upd. destruct (Nat.eqb j' k); [right; apply vok_vd|left; reflexivity].
Qed.

Theorem KR_cfix : KR Fk Good sw (scfix0 (sflp sW c o b) c j b B) (scfix0 (sflp sA c o b) c j b B).
Proof.
  assert (V : forall s c', vP (cs (scfix0 (sflp s c o b) c j b B) c') = vP (cs s c') /\ vA (cs (scfix0 (sflp s c o b) c j b B) c') = vA (cs s c') /\ vOg (cs (scfix0 (sflp s c o b) c j b B) c') = vOg (cs s c')).
  { intros s0 c'. rewrite cs_cfix. destruct (Nat.eqb_spec c' c) as [->|]; [|auto].
    destruct (cfixc_f (cs s0 c)) as (_ & _ & _ & E4 & E5 & E6 & _). auto. }
  apply (KR_nolog p Fk Good sw sW sA _ _ RA R KK).
  - unfold scfix0. cbn [lg]. apply lg_flp.
  - unfold scfix0. cbn [hs]. apply hs_flp.
  - unfold scfix0. cbn [lg]. apply lg_flp.
  - unfold scfix0. cbn [hs]. apply hs_flp.
  - unfold scfix0. cbn [wc]. apply wc_flp.
  - unfold scfix0. cbn [vG]. apply vG_flp.
  - unfold scfix0. cbn [vG]. apply vG_flp.
  - intros c'. exact (V sW c').
  - intros c'. exact (V sA c').
  - intros c'. rewrite cs_cfix. destruct (Nat.eqb_spec c' c) as [->|]; [|auto].
    destruct (cfixc_f (cs sW c)) as (E1 & E2 & _). auto.
  - intros c'. unfold scfix0. cbn [pcs]. rewrite pcs_flp. lia.
  - intros c' j'. rewrite cs_cfix. destruct (Nat.eqb_spec c' c) as [->|]; [|left; reflexivity].
    exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (cfixc_f (cs sW c))))))) j').
  - intros tf f E (Fa & Fp & Fo). rewrite cs_cfix in Fa, Fo. unfold scfix0 in Fp. cbn [pcs] in Fp. rewrite pcs_flp in Fp.
    destruct (Nat.eqb_spec (ec f) c) as [Ec|]; [|unfold isFF; auto].
    destruct (cfixc_f (cs sW c)) as (E1 & _ & E3 & _). rewrite E1 in Fo. rewrite E3 in Fa. unfold isFF. rewrite Ec. rewrite Ec in Fp. auto.
  - intros t f e Sw E Cc. rewrite cs_cfix. destruct (Nat.eqb_spec (ec e) c) as [Ec|]; [|auto].
    destruct (cfixc_f (cs sW c)) as (_ & _ & E3 & _). rewrite E3. rewrite <- Ec. exact Cc.
Qed.
End CF.

Lemma pc1_upd : forall (f : nat -> nat) c c', f c' <= upd f c (S (f c)) c'.
Proof. intros f c c'. unfold upd. destruct (Nat.eqb_spec c' c) as [->|]; lia. Qed.
Lemma pc2_upd : forall (f : nat -> nat) c c' j, j < upd f c (S (f c)) c' -> j < f c' \/ (c' = c /\ j = f c).
Proof. intros f c c' j. unfold upd. destruct (Nat.eqb_spec c' c) as [->|]; [|auto]. intros L. destruct (Nat.eq_dec j (f c)); [right|left]; auto; lia. Qed.
Lemma pc1_id : forall (f : nat -> nat) c', f c' <= f c'. Proof. auto. Qed.
Lemma pc2_id : forall (f : nat -> nat) (c k : nat) c' j, j < f c' -> j < f c' \/ (c' = c /\ j = k). Proof. auto. Qed.
