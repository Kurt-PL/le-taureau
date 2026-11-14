(* Part 19: along a step of the write-back model the event graph of each cell only
   grows (as the whole graph does, M2DQWBK2.stepWB_gedge), so a state whose graphs have no cycle
   has acyclic graphs at every earlier state of its run (evok goes backward along stepWB). *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB M2DQWBK1 M2DQWBK2.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

Lemma grows_cedge : forall s s', grows s s' -> forall x a b, cedge s x a b -> cedge s' x a b.
Proof. intros s s' (HO & HI & HL) x a b C. apply (cedge_grow s s' HO HI HL x a b C). Qed.

Lemma wbst_cgrows : forall s c k t H'', wbok s c k t H'' ->
  (forall x a b, cedge s x a b -> cedge (wbst s c k t H'') x a b).
Proof.
  intros s c k t H'' Ok x a b C.
  assert (HO : forall a0 b0, older (hs s x) a0 b0 -> older (H'' x) a0 b0).
  { intros a0 b0 O. destruct (enters_tied_cell _ _ _ _ _ x Ok) as [E|(h1 & h2 & E1 & E2 & _)]; [rewrite E; exact O|].
    rewrite E2. rewrite E1 in O. apply older_ins. exact O. }
  assert (HI : forall b0, In b0 (ids (hs s x)) -> In b0 (ids (H'' x))).
  { intros b0 I. destruct (enters_tied_cell _ _ _ _ _ x Ok) as [E|(h1 & h2 & E1 & E2 & _)]; [rewrite E; exact I|].
    rewrite E2. rewrite E1 in I. apply in_ids_ins. right. exact I. }
  assert (HL : forall a0 e, nth_error (lg s) a0 = Some e -> nth_error (setew (lg s) t) a0 = Some (sete t e)).
  { intros a0 e L. rewrite nth_setew, L. reflexivity. }
  assert (S : forall e, eR (sete t e) = eR e /\ erf (sete t e) = erf e /\ eC (sete t e) = eC e /\
                        eQ (sete t e) = eQ e /\ eQc (sete t e) = eQc e /\ ec (sete t e) = ec e /\ ek (sete t e) = ek e).
  { intros e. unfold sete. destruct (Nat.eqb (et e) t); cbn; auto 10. }
  unfold cedge, wbst; cbv zeta; cbn [hs lg].
  destruct C as [O|[(e & L & Ix & Ib & N & M)|[(e & L & Ix & Ex & N)|[(e & L & Ix & Q & Ia & N)|(ea & eb & La & Lb & Cc & K & Ia & Ib)]]]].
  - left. exact (HO a b O).
  - right; left. exists (sete t e). destruct (S e) as (S1 & S2 & _). rewrite S1, S2.
    split; [exact (HL a e L)|]. split; [exact Ix|]. split; [exact (HI b Ib)|]. split; [exact N|].
    destruct (erf e x) as [u0|]; [exact (HO u0 b M)|exact I].
  - right; right; left. exists (sete t e). destruct (S e) as (S1 & S2 & _). rewrite S1, S2. auto.
  - right; right; right; left. exists (sete t e). destruct (S e) as (_ & _ & S3 & S4 & S5 & _). rewrite S3, S4, S5.
    split; [exact (HL b e L)|]. split; [exact Ix|]. split; [exact Q|]. split; [exact (HI a Ia)|exact N].
  - right; right; right; right. exists (sete t ea), (sete t eb).
    destruct (S ea) as (_ & _ & A3 & _ & _ & A6 & A7). destruct (S eb) as (_ & _ & B3 & _ & _ & B6 & B7).
    rewrite A3, B3, A6, B6, A7, B7. split; [exact (HL a ea La)|]. split; [exact (HL b eb Lb)|]. auto.
Qed.

Lemma stepWB_cedge : forall p s s', stepWB p s s' -> forall x a b, cedge s x a b -> cedge s' x a b.
Proof.
  intros p s s' H x a b G. inversion H as [s0 s1 St _ | s0 s1 c k t1 H'' St _ _ Ok | s0 c k t1 xs H'' _ _ _ _ _ _ _ Ok]; subst.
  - exact (grows_cedge _ _ (step_grows p s s' St) x a b G).
  - apply (wbst_cgrows s1 c k t1 H'' Ok). exact (grows_cedge _ _ (step_grows p s s1 St) x a b G).
  - apply (wbst_cgrows s c k t1 H'' Ok). exact G.
Qed.

(* evok goes backward along a step of the write-back model *)
Theorem stepWB_evok_back : forall p s s', stepWB p s s' -> evok s' -> evok s.
Proof.
  intros p s s' H [G C]. split.
  - intros a T. apply (G a). exact (ct_mono _ _ (stepWB_gedge p s s' H) a a T).
  - intros x a T. apply (C x a). exact (ct_mono _ _ (stepWB_cedge p s s' H x) a a T).
Qed.

Print Assumptions stepWB_evok_back.
