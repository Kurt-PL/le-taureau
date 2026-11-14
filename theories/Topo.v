(* A finite list with a decidable relation that has no cycle can be ordered
   so that every related pair comes in order. *)
From Stdlib Require Import Arith Lia List Bool Permutation.
Import ListNotations.

Section TopoS.
Variable A : Type.
Variable eqd : forall a b : A, {a = b} + {a <> b}.
Variable Rb : A -> A -> bool.

(* a chain a0 -> a1 -> ... *)
Fixpoint chain (l : list A) : Prop :=
  match l with
  | a :: ((b :: _) as t) => Rb a b = true /\ chain t
  | _ => True
  end.

Lemma chain_app : forall l1 a l2, chain (l1 ++ [a]) -> chain (a :: l2) -> chain (l1 ++ a :: l2).
Proof.
  induction l1 as [|x l1 IH]; intros a l2 H1 H2; simpl in *; auto.
  destruct l1 as [|y l1']; simpl in *.
  - destruct H1 as [H _]. split; auto.
  - destruct H1 as [H H1]. split; auto. apply (IH a l2 H1 H2).
Qed.

Lemma chain_prefix : forall l m, chain (l ++ m) -> chain l.
Proof.
  induction l as [|x l IH]; intros m H; simpl in *; auto.
  destruct l as [|y l']; simpl in *; auto. destruct H as [H1 H2]. split; auto. apply (IH m H2).
Qed.

Lemma chain_suffix : forall l m, chain (l ++ m) -> chain m.
Proof.
  induction l as [|x l IH]; intros m H; simpl in *; auto. apply IH.
  destruct (l ++ m) as [|y t]; simpl in *; tauto.
Qed.

Lemma chain_sub : forall l1 l2 l3, chain (l1 ++ l2 ++ l3) -> chain l2.
Proof. intros l1 l2 l3 H. apply chain_suffix in H. apply chain_prefix in H. exact H. Qed.

(* a cycle: a chain that ends where it starts *)
Definition acyclic (L : list A) : Prop :=
  forall a l, In a L -> (forall b, In b l -> In b L) -> chain (a :: l ++ [a]) -> False.

Lemma dup_split : forall l : list A, ~ NoDup l -> exists a l1 l2 l3, l = l1 ++ a :: l2 ++ a :: l3.
Proof.
  induction l as [|x l IH]; intros H; [exfalso; apply H; constructor|].
  destruct (in_dec eqd x l) as [I|I].
  - apply in_split in I. destruct I as (l2 & l3 & E). exists x, [], l2, l3. rewrite E. reflexivity.
  - destruct IH as (a & l1 & l2 & l3 & E).
    + intros N. apply H. constructor; auto.
    + exists a, (x :: l1), l2, l3. rewrite E. reflexivity.
Qed.

(* iterate a predecessor function: x_{i+1} -> x_i *)
Fixpoint back (f : A -> A) (n : nat) (a : A) : list A :=
  match n with 0 => [a] | S n' => back f n' (f a) ++ [a] end.

Lemma back_last : forall f m b, exists l', back f m b = l' ++ [b].
Proof.
  intros f. induction m as [|m IHm]; intros b; simpl; [exists []; reflexivity|].
  destruct (IHm (f b)) as (l' & E). rewrite E. exists (l' ++ [f b]). rewrite <- app_assoc. reflexivity.
Qed.

Lemma back_chain : forall (L : list A) f, (forall a, In a L -> In (f a) L /\ Rb (f a) a = true) ->
  forall n a, In a L -> chain (back f n a).
Proof.
  intros L f F. induction n as [|n IH]; intros a I; simpl; auto.
  destruct (back_last f n (f a)) as (l' & E). rewrite E. rewrite <- app_assoc. simpl.
  apply chain_app; [rewrite <- E; apply IH; apply F; auto|]. simpl. split; auto. apply F; auto.
Qed.

Lemma back_len : forall f n a, length (back f n a) = S n.
Proof. intros f. induction n; intros a; simpl; auto. rewrite length_app, IHn. simpl. lia. Qed.

Lemma back_in : forall (L : list A) f, (forall a, In a L -> In (f a) L) -> forall n a, In a L -> forall b, In b (back f n a) -> In b L.
Proof.
  intros L f F. induction n as [|n IH]; intros a I b Ib; simpl in *.
  - destruct Ib as [<-|[]]; auto.
  - apply in_app_iff in Ib. destruct Ib as [Ib|[<-|[]]]; auto. apply (IH (f a)); auto.
Qed.

Lemma remove_in : forall (L : list A) m b, In b (remove eqd m L) -> In b L.
Proof. intros L m b H. apply in_remove in H. tauto. Qed.

Lemma acyclic_remove : forall L m, acyclic L -> acyclic (remove eqd m L).
Proof.
  intros L m H a l I Il C. apply (H a l); auto.
  - eapply remove_in; eauto.
  - intros b Ib. eapply remove_in; eauto.
Qed.

Lemma remove_len : forall L m, In m L -> length (remove eqd m L) < length L.
Proof.
  induction L as [|x L IH]; intros m I; [destruct I|]. simpl.
  destruct (eqd m x) as [->|N].
  - pose proof (remove_length_le eqd L x). lia.
  - simpl. destruct I as [->|I]; [congruence|]. specialize (IH m I). lia.
Qed.

Lemma perm_remove : forall L m, NoDup L -> In m L -> Permutation L (m :: remove eqd m L).
Proof.
  induction L as [|x L IH]; intros m N I; [destruct I|]. simpl.
  inversion N as [|? ? Nx NL]; subst.
  destruct (eqd m x) as [->|Nm].
  - rewrite notin_remove by auto. reflexivity.
  - destruct I as [->|I]; [congruence|]. eapply perm_trans; [apply perm_skip; apply (IH m NL I)|].
    apply perm_swap.
Qed.

Theorem topo : forall L, NoDup L -> acyclic L ->
  exists sg, Permutation L sg /\
    (forall i j a b, nth_error sg i = Some a -> nth_error sg j = Some b -> Rb a b = true -> i < j).
Proof.
  intros L. remember (length L) as n eqn:E. revert L E.
  induction n as [n IH] using lt_wf_ind. intros L E N Ac.
  destruct L as [|a0 L0] eqn:EL.
  { exists []. split; [constructor|]. intros i j a b Qa. destruct i; discriminate. }
  rewrite <- EL in *.
  destruct (find (fun m => negb (existsb (fun b => Rb b m) L)) L) as [m|] eqn:F.
  - (* a minimal element *)
    apply find_some in F. destruct F as [Im Fm]. apply negb_true_iff in Fm.
    assert (NR : NoDup (remove eqd m L)).
    { clear -N. induction L; simpl; [constructor|]. inversion N; subst. destruct (eqd m a); auto. constructor; auto.
      intros I. apply in_remove in I. tauto. }
    destruct (IH (length (remove eqd m L)) ltac:(rewrite E; apply remove_len; auto) (remove eqd m L) eq_refl
               NR (acyclic_remove L m Ac)) as (sg & P & O).
    exists (m :: sg). split; [eapply perm_trans; [apply (perm_remove L m N Im)|apply perm_skip; auto]|].
    intros i j a b Qa Qb Rab. destruct j as [|j].
    + simpl in Qb. injection Qb as <-. exfalso.
      assert (Ia : In a L).
      { destruct i as [|i]; simpl in Qa; [injection Qa as <-; auto|].
        apply nth_error_In in Qa. eapply Permutation_in in Qa; [|apply Permutation_sym; exact P]. eapply remove_in; eauto. }
      assert (existsb (fun b => Rb b m) L = true) by (apply existsb_exists; eauto). congruence.
    + destruct i as [|i]; [lia|]. simpl in Qa, Qb. specialize (O i j a b Qa Qb Rab). lia.
  - (* no minimal element: following predecessors gives a cycle *)
    exfalso.
    assert (Pred : forall m, In m L -> exists b, In b L /\ Rb b m = true).
    { intros m Im. pose proof (find_none _ _ F m Im) as H. apply negb_false_iff in H.
      apply existsb_exists in H. exact H. }
    set (f := fun m => match find (fun b => Rb b m) L with Some b => b | None => m end).
    assert (Ff : forall m, In m L -> In (f m) L /\ Rb (f m) m = true).
    { intros m Im. unfold f. destruct (find (fun b => Rb b m) L) as [b|] eqn:G.
      - apply find_some in G. tauto.
      - destruct (Pred m Im) as (b & Ib & Rb').
        pose proof (find_none _ _ G b Ib). simpl in H. congruence. }
    assert (I0 : In a0 L) by (rewrite EL; left; auto).
    set (bl := back f (length L) a0).
    assert (Ib : forall b, In b bl -> In b L).
    { apply (back_in L f); [intros; apply Ff; auto|exact I0]. }
    assert (ND : ~ NoDup bl).
    { intros ND. pose proof (NoDup_incl_length ND Ib) as Le. unfold bl in Le. rewrite back_len in Le. lia. }
    destruct (dup_split bl ND) as (a & l1 & l2 & l3 & Eb).
    assert (C0 : chain bl) by (apply (back_chain L f Ff); auto).
    rewrite Eb in C0.
    assert (C1 : chain (l1 ++ (a :: l2 ++ [a]) ++ l3)) by (replace ((a :: l2 ++ [a]) ++ l3) with (a :: l2 ++ a :: l3) by (simpl; rewrite <- app_assoc; reflexivity); exact C0).
    apply (Ac a l2).
    + apply Ib. rewrite Eb. apply in_app_iff. right. left. auto.
    + intros b I. apply Ib. rewrite Eb. apply in_app_iff. right. right. apply in_app_iff. left. auto.
    + exact (chain_sub l1 _ l3 C1).
Qed.

End TopoS.
