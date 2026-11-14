(* Deciding that a finite relation has no cycle: a rank that grows along
   every edge is a certificate; Kahn's algorithm finds one by computation,
   and only the check is trusted. *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.

Lemma rank_acyclic : forall (E : nat -> nat -> Prop) (rk : nat -> nat),
  (forall a b, E a b -> rk a < rk b) -> forall a, ~ clos_trans nat E a a.
Proof.
  intros E rk R a C.
  assert (T : forall a b, clos_trans nat E a b -> rk a < rk b).
  { intros a0 b0 T. induction T; [apply R; auto|lia]. }
  specialize (T a a C). lia.
Qed.

(* the position of a in a list, as a rank *)
Fixpoint idx (a : nat) (l : list nat) : nat :=
  match l with [] => 0 | b :: l' => if Nat.eqb a b then 0 else S (idx a l') end.

(* edges as a boolean function on nodes below n *)
Definition rank_ok (n : nat) (Eb : nat -> nat -> bool) (ord : list nat) : bool :=
  forallb (fun a => forallb (fun b => negb (Eb a b) || Nat.ltb (idx a ord) (idx b ord)) (seq 0 n)) (seq 0 n).

Lemma rank_ok_sound : forall n Eb ord, rank_ok n Eb ord = true ->
  forall a b, a < n -> b < n -> Eb a b = true -> idx a ord < idx b ord.
Proof.
  intros n Eb ord H a b La Lb E. unfold rank_ok in H. rewrite forallb_forall in H.
  specialize (H a (proj2 (in_seq n 0 a) (conj (Nat.le_0_l _) La))). rewrite forallb_forall in H.
  specialize (H b (proj2 (in_seq n 0 b) (conj (Nat.le_0_l _) Lb))). rewrite E in H. simpl in H.
  apply Nat.ltb_lt. exact H.
Qed.

(* Kahn: repeatedly take a node with no incoming edge from the nodes left *)
Fixpoint kahn (fuel : nat) (Eb : nat -> nat -> bool) (left : list nat) : list nat :=
  match fuel with
  | 0 => left
  | S f =>
      match find (fun a => negb (existsb (fun b => Eb b a) left)) left with
      | Some a => a :: kahn f Eb (remove Nat.eq_dec a left)
      | None => left
      end
  end.

Definition acyc_b (n : nat) (Eb : nat -> nat -> bool) : bool := rank_ok n Eb (kahn n Eb (seq 0 n)).

Lemma acyc_b_sound : forall n (E : nat -> nat -> Prop) Eb,
  (forall a b, E a b -> a < n /\ b < n /\ Eb a b = true) ->
  acyc_b n Eb = true -> forall a, ~ clos_trans nat E a a.
Proof.
  intros n E Eb R H. apply (rank_acyclic E (fun a => idx a (kahn n Eb (seq 0 n)))).
  intros a b Ea. destruct (R a b Ea) as (La & Lb & Eab). exact (rank_ok_sound n Eb _ H a b La Lb Eab).
Qed.

(* positive and negative instances *)
Example acyc_line : acyc_b 3 (fun a b => (Nat.eqb a 0 && Nat.eqb b 1) || (Nat.eqb a 1 && Nat.eqb b 2)) = true.
Proof. vm_compute. reflexivity. Qed.
Example acyc_cycle : acyc_b 3 (fun a b => (Nat.eqb a 0 && Nat.eqb b 1) || (Nat.eqb a 1 && Nat.eqb b 0)) = false.
Proof. vm_compute. reflexivity. Qed.
