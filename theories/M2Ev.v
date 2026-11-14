(* Model2, one event: the run so far has no access before itself. Edges only
   grow along a run, so a state without such a cycle has none before it
   either: requiring it of the final state requires it of every state. *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2.

Section Grow.
Variables s t : st.
Hypothesis HO : forall x a b, older (hs s x) a b -> older (hs t x) a b.
Hypothesis HI : forall x b, In b (ids (hs s x)) -> In b (ids (hs t x)).
Hypothesis HL : forall a e, nth_error (lg s) a = Some e -> nth_error (lg t) a = Some e.

Lemma gedge_grow : forall a b, gedge s a b -> gedge t a b.
Proof.
  intros a b [(x & O)|[(e & x & L & Ix & Ib & N & M)|(e & L & Q & N)]].
  - left. exists x. auto.
  - right; left. exists e, x. split; [apply HL; exact L|]. split; [exact Ix|]. split; [apply HI; exact Ib|]. split; [exact N|].
    destruct (erf e x); auto.
  - right; right. exists e. repeat split; auto.
Qed.

Lemma cedge_grow : forall x a b, cedge s x a b -> cedge t x a b.
Proof.
  intros x a b [O|[(e & L & Ix & Ib & N & M)|[(e & L & Ix & Ex & N)|[(e & L & Ix & Q & Ia & N)|(ea & eb & La & Lb & C & K & Ia & Ib)]]]].
  - left. auto.
  - right; left. exists e. split; [apply HL; exact L|]. split; [exact Ix|]. split; [apply HI; exact Ib|]. split; [exact N|].
    destruct (erf e x); auto.
  - right; right; left. exists e. repeat split; auto.
  - right; right; right; left. exists e. repeat split; auto.
  - right; right; right; right. exists ea, eb. repeat split; auto.
Qed.

Lemma ct_mono : forall (R1 R2 : nat -> nat -> Prop), (forall a b, R1 a b -> R2 a b) ->
  forall a b, clos_trans nat R1 a b -> clos_trans nat R2 a b.
Proof.
  intros R1 R2 M a b T. induction T as [a b H|a b c _ IH1 _ IH2]; [constructor; auto|econstructor 2; eauto].
Qed.

Lemma evok_back : evok t -> evok s.
Proof.
  intros [G C]. split.
  - intros a T. apply (G a). exact (ct_mono _ _ gedge_grow a a T).
  - intros x a T. apply (C x a). exact (ct_mono _ _ (cedge_grow x) a a T).
Qed.
End Grow.

Lemma lg_app_nth : forall (l : list oev) e a e', nth_error l a = Some e' -> nth_error (l ++ [e]) a = Some e'.
Proof. intros l e a e' H. rewrite nth_error_app1; auto. apply nth_error_Some. congruence. Qed.

(* a step keeps every edge *)
Lemma evok_step : forall p s t, run p s -> step p s t -> evok t -> evok s.
Proof.
  intros p s t R H. destruct (Inv2_run p s R) as [I J].
  destruct (step_cases p s t H) as [(c & i & m' & a & K & u & w & H1 & H2 & H3 & H4 & Hbh & Hh & _ & _ & H6 & _ & ->)|[(c & k & d & B & m' & a & K & u & w & H1 & H2 & Hso & Hh & _ & _ & H5 & _ & ->)|[(c & d & H1 & H2 & H3 & H4 & H4m & Hfh & ->)|[(c & k & xs & B & m' & a & K & u & w & bv & H1 & H2 & Hh & Hso & H4 & H5 & _ & ->)|[(c & S1 & S2 & S3 & _ & S5 & S4 & _ & ->)|(cX & jX & bX & BX & oX & HjX & HfX & HcX & ->)]]]]].
  - assert (Hst : forall r, settled (cs s c) (pcs s c) r -> ieval i r = ieval i (rg (cs s c))) by (intros r Sr; apply (proj2 (H3 r Sr))).
    assert (Hhk : oh (cs s c) (pcs s c) = None \/
      (u = rw (cs s c) (pcs s c) /\ eofR i (rg (cs s c)) = eofR (ai (cs s c) (pcs s c)) (rg (cs s c))))
      by (destruct Hh as [(Z & _)|(t1 & Z & Ci & U & Ef)]; [left; exact Z|right; split; [exact U|exact Ef]]).
    apply evok_back.
    + intros x y z. apply (older_new_old p s c (pcs s c) i m' a K u w _ _ _ _ I J H2 (le_n _) Hst H6 Hhk).
    + intros x y. apply (in_hs_new p s c (pcs s c) i m' a K u w _ _ _ _ I J H2 (le_n _) Hst H6 Hhk).
    + intros a0 e E. unfold sord, evs; simpl. apply lg_app_nth. exact E.
  - assert (Hst : forall r, settled (cs s c) (pcs s c) r -> ieval (inst_of d) r = ieval (inst_of d) (rg (cs s c)))
      by (intros r _; apply ieval_inst).
    assert (Hhk : oh (cs s c) k = None \/
      (u = rw (cs s c) k /\ eofR (inst_of d) (rg (cs s c)) = eofR (ai (cs s c) k) (rg (cs s c)))).
    { destruct Hh as [(Z & _)|(t1 & xs & ev & nv & Z & -> & U & Ac & _)]; [left; exact Z|right].
      split; [exact U|]. rewrite Ac. reflexivity. }
    apply evok_back.
    + intros x y z. apply (older_new_old p s c k (inst_of d) m' a K u w (bor (bd (cs s c)) B) (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s) I J H2 (Nat.lt_le_incl _ _ H1) Hst H5 Hhk).
    + intros x y. apply (in_hs_new p s c k (inst_of d) m' a K u w (bor (bd (cs s c)) B) (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s) I J H2 (Nat.lt_le_incl _ _ H1) Hst H5 Hhk).
    + intros a0 e E. unfold searly, set_es, searly0, evs; simpl. apply lg_app_nth. exact E.
  - apply evok_back; auto.
  - destruct (rd_mem p s c k xs B m' a K u w bv I J H2 H1 Hh H5) as (Mh & _).
    apply evok_back.
    + intros x y z. rewrite Mh. auto.
    + intros x y. rewrite Mh. auto.
    + intros a0 e E. unfold sread; simpl. apply lg_app_nth. exact E.
  - apply evok_back; auto.
  - unfold scfix0. rewrite hs_flp, lg_flp. apply evok_back; auto.
Qed.

(* ---------- deciding it on a concrete state: a rank that grows along every edge ---------- *)
Lemma evok_rank : forall s (rk : nat -> nat),
  (forall a b, gedge s a b -> rk a < rk b) -> (forall x a b, cedge s x a b -> rk a < rk b) -> evok s.
Proof.
  intros s rk G C. split.
  - intros a T. assert (Q : forall a b, clos_trans nat (gedge s) a b -> rk a < rk b)
      by (intros a0 b0 T0; induction T0; [apply G; auto|lia]). specialize (Q a a T). lia.
  - intros x a T. assert (Q : forall a b, clos_trans nat (cedge s x) a b -> rk a < rk b)
      by (intros a0 b0 T0; induction T0; [apply (C x); auto|lia]). specialize (Q a a T). lia.
Qed.

(* the ordered pairs of a list *)
Fixpoint pairs (l : list nat) : list (nat * nat) :=
  match l with [] => [] | a :: l' => map (fun b => (a, b)) l' ++ pairs l' end.

Lemma older_pairs : forall h a b, older h a b -> In (a, b) (pairs (ids h)).
Proof.
  intros h a b O. apply older_split in O. destruct O as (l1 & l2 & E & A & B). rewrite E. clear E.
  induction l1 as [|c l1 IH]; [destruct A|]. simpl. apply in_app_iff. destruct A as [<-|A].
  - left. apply in_map_iff. exists b. split; auto. apply in_app_iff. right. auto.
  - right. auto.
Qed.

(* ---------- removing edges that a G edge absorbs ---------- *)
Section Absorb.
Variables G P : nat -> nat -> Prop.
Hypothesis H1 : forall a b c, G a b -> P b c -> G a c.
Hypothesis H2 : forall a b c, P a b -> P b c -> P a c.
Hypothesis H3 : forall a, ~ P a a.

Lemma gplus_p : forall a b c, clos_trans nat G a b -> P b c -> clos_trans nat G a c.
Proof.
  intros a b c T Pbc. apply clos_trans_tn1 in T. destruct T as [b Gab|b b' Gbb T'].
  - constructor. eapply H1; eauto.
  - apply clos_tn1_trans in T'. apply clos_trans_tn1_iff. apply clos_trans_tn1_iff in T'.
    econstructor 2; [eapply H1; eauto|exact T'].
Qed.

Lemma absorb : forall a b, clos_trans nat (fun x y => G x y \/ P x y) a b ->
  clos_trans nat G a b \/ P a b \/ exists d, P a d /\ clos_trans nat G d b.
Proof.
  intros a b T. apply clos_trans_tn1 in T. induction T as [b [Gab|Pab]|b c [Gbc|Pbc] T IH].
  - left. constructor. auto.
  - right; left. auto.
  - destruct IH as [IH|[IH|(d & Pad & Gdb)]].
    + left. econstructor 2; eauto. constructor; auto.
    + right; right. exists b. split; auto. constructor; auto.
    + right; right. exists d. split; auto. econstructor 2; eauto. constructor; auto.
  - destruct IH as [IH|[IH|(d & Pad & Gdb)]].
    + left. eapply gplus_p; eauto.
    + right; left. eauto.
    + right; right. exists d. split; auto. eapply gplus_p; eauto.
Qed.

Lemma absorb_cycle : (forall a, ~ clos_trans nat G a a) ->
  forall a, ~ clos_trans nat (fun x y => G x y \/ P x y) a a.
Proof.
  intros NG a T. destruct (absorb a a T) as [C|[C|(d & Pad & Gda)]].
  - exact (NG a C).
  - exact (H3 a C).
  - apply (NG d). eapply gplus_p; eauto.
Qed.
End Absorb.
