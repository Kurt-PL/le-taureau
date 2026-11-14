(* Model2: the timeline wording of the rule (M2Timeline.tlok) against the
   event graph (M2Model.evok).

   - tlok_evok: no cycle through the timelines and knowledge implies no
     cycle in gedge and none in cedge x. *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Timeline.

(* ---------- double negation, for choosing places ---------- *)
Definition NN (P : Prop) : Prop := ~ ~ P.
Lemma nn_ret : forall P : Prop, P -> NN P.
Proof. intros P H N. exact (N H). Qed.
Lemma nn_bind : forall P Q : Prop, NN P -> (P -> NN Q) -> NN Q.
Proof. intros P Q H F N. apply H. intros p. exact (F p N). Qed.
Lemma nn_em : forall P : Prop, NN (P \/ ~ P).
Proof. intros P N. apply N. right. intros p. apply N. left. exact p. Qed.

Set Default Proof Using "All".
Section E.
Variable p : prog.
Variable s : st.
Hypothesis J : Inv2 p s.

Lemma hs_write : forall x a, In a (ids (hs s x)) -> exists e, nth_error (lg s) a = Some e /\ ew e = true.
Proof. intros x a H. destruct (j_hist p s J x a H) as (e & i & A & Wt & _). exists e. auto. Qed.

Lemma write_not_apart : forall x a y, In a (ids (hs s x)) -> ~ apart s a y.
Proof.
  intros x a y H (e & u & A & Wf & _). destruct (hs_write x a H) as (e' & A' & W'). congruence.
Qed.

Lemma pl_write : forall x a n, In a (ids (hs s x)) -> pl s a x n -> n = (a, None).
Proof.
  intros x a n H [(-> & Ap)|(-> & _)]; auto. exfalso. exact (write_not_apart x a x H Ap).
Qed.

Lemma pl_write' : forall x a, In a (ids (hs s x)) -> pl s a x (a, None).
Proof. intros x a H. right. split; auto. exact (write_not_apart x a x H). Qed.

Lemma pl_nn : forall t x, NN (exists n, pl s t x n).
Proof.
  intros t x. apply (nn_bind _ _ (nn_em (apart s t x))). intros [A|A]; apply nn_ret.
  - exists (t, Some x). left. auto.
  - exists (t, None). right. auto.
Qed.

(* ---------- gedge ---------- *)
Lemma gedge_tl : forall a b, gedge s a b -> tl s (a, None) (b, None).
Proof.
  intros a b [(x & O)|[(e & x & L & Ix & Ib & N & M)|(e & L & Q & N)]].
  - destruct (older_in _ _ _ O) as [Ia Ib].
    apply (tl_hist s x a b); auto; apply pl_write'; auto.
  - apply (tl_miss s x a e b (a, None) L Ix Ib N M). right. reflexivity.
  - apply (tl_know s b e a L Q N).
Qed.

Lemma ct_gedge_tl : forall a b, clos_trans nat (gedge s) a b -> clos_trans tnode (tl s) (a, None) (b, None).
Proof.
  intros a b H. induction H as [a b H|a c b _ IH1 _ IH2].
  - constructor. apply gedge_tl. exact H.
  - apply t_trans with (c, None); auto.
Qed.

(* ---------- cedge ---------- *)
Hypothesis TL : tlok s.

Lemma cedge_tl : forall x a b na nb, cedge s x a b -> pl s a x na -> pl s b x nb -> clos_trans tnode (tl s) na nb.
Proof.
  intros x a b na nb H Pa Pb.
  destruct H as [O|[(e & L & Ix & Ib & N & M)|[(e & L & Ix & M & N)|[(e & L & Ix & Q & Ia & N)|(ea & eb & La & Lb & C & K & Xa & Xb)]]]].
  - constructor. apply (tl_hist s x a b); auto.
  - rewrite (pl_write x b nb Ib Pb). constructor. apply (tl_miss s x a e b na L Ix Ib N M). left. exact Pa.
  - destruct (j_rf p s J _ e x a L M) as (_ & _ & _ & Ia).
    rewrite (pl_write x a na Ia Pa). constructor. apply (tl_took s x b e a nb L Ix M N Pb).
  - destruct Q as [Q|Q]; [|constructor; apply (tl_knowc s x b e a na nb L Ix Q Ia N Pa Pb)].
    rewrite (pl_write x a na Ia Pa).
    destruct Pb as [(-> & Ap)|(-> & _)]; [|constructor; apply (tl_know s b e a L Q N)].
    (* the knower stands apart in x: it took its own store u there *)
    destruct Ap as (e' & u & L' & Wf & Ln & Rx & Eu & Ow & Nq). rewrite L in L'. injection L' as <-.
    destruct (j_rf p s J _ e x u L Eu) as (_ & _ & _ & Iu).
    assert (Nau : a <> u) by (intros ->; exact (Nq Q)).
    destruct (older_total _ _ _ Ia Iu Nau) as [O|O].
    + apply t_trans with (u, None).
      * constructor. apply (tl_hist s x a u); auto; apply pl_write'; auto.
      * constructor. apply (tl_took s x b e u (b, Some x) L Rx Eu).
        -- intros E. rewrite <- E in L. destruct (hs_write x u Iu) as (e2 & L2 & W2). rewrite L2 in L.
           injection L as <-. congruence.
        -- left. split; [reflexivity|]. exists e, u. repeat split; auto.
    + exfalso. apply (TL (a, None)). apply t_trans with (b, None).
      * constructor. apply (tl_know s b e a L Q N).
      * constructor. apply (tl_miss s x b e a (b, None) L Rx Ia ltac:(auto)); [rewrite Eu; exact O|]. right. reflexivity.
  - constructor. apply (tl_po s x a b ea eb na nb La Lb C K Xa Xb Pa Pb).
Qed.

Lemma ct_cedge_tl : forall x a b, clos_trans nat (cedge s x) a b ->
  forall na nb, pl s a x na -> pl s b x nb -> NN (clos_trans tnode (tl s) na nb).
Proof.
  intros x a b H. induction H as [a b H|a c b _ IH1 _ IH2]; intros na nb Pa Pb.
  - apply nn_ret. apply (cedge_tl x a b); auto.
  - apply (nn_bind _ _ (pl_nn c x)). intros (nc & Pc).
    apply (nn_bind _ _ (IH1 na nc Pa Pc)). intros T1.
    apply (nn_bind _ _ (IH2 nc nb Pc Pb)). intros T2.
    apply nn_ret. apply t_trans with nc; auto.
Qed.

End E.

Theorem tlok_evok : forall p s, run p s -> tlok s -> evok s.
Proof.
  intros p s R TL. destruct (Inv2_run p s R) as [_ J]. split.
  - intros a C. apply (TL (a, None)). apply (ct_gedge_tl p s J). exact C.
  - intros x a C. apply (pl_nn p s J a x). intros (na & Pa).
    apply (ct_cedge_tl p s J TL x a a C na na Pa Pa). apply TL.
Qed.
