(* Runs that avoid a stable bad set. If a set of states, once entered, is
   never left (bad_stable), then a property that every step into a state
   outside the set preserves holds of every reachable state outside it; and
   when no finished state is bad, of every finished state. Shared by
   M2SlotOrder (the slot-order condition) and the guard() bridge. *)
From Stdlib Require Import Arith Lia.

Section Avoid.
Variables (S : Type) (step : S -> S -> Prop) (reach : S -> Prop) (Bad P : S -> Prop) (s0 : S).
(* reach is the runs from s0: its two constructors as hypotheses *)
Hypothesis reach_ind' : forall Q : S -> Prop, Q s0 -> (forall s t, reach s -> Q s -> step s t -> Q t) ->
  forall s, reach s -> Q s.
Hypothesis bad_stable : forall s t, reach s -> Bad s -> step s t -> Bad t.
Hypothesis P0 : P s0.
Hypothesis Pstep : forall s t, reach s -> P s -> step s t -> ~ Bad t -> P t.

Lemma avoid_run : forall s, reach s -> ~ Bad s -> P s.
Proof.
  apply (reach_ind' (fun s => ~ Bad s -> P s)); [intros _; exact P0|].
  intros s t R IH St Nb. apply (Pstep s t R); auto. apply IH. intros B. apply Nb. apply (bad_stable s t R B St).
Qed.

Lemma avoid_done : forall (done : S -> Prop), (forall s, done s -> ~ Bad s) ->
  forall s, reach s -> done s -> P s.
Proof. intros done ND s R D. apply avoid_run; auto. Qed.
End Avoid.

(* a positive and a negative instance: on nat with the successor step from
   0, the bad set "at least 3" is stable; P "below 3" holds of every state
   outside it, and fails at 3 *)
Inductive rnat : nat -> Prop := rn0 : rnat 0 | rnS : forall n, rnat n -> rnat (S n).

Lemma avoidInst : forall n, rnat n -> ~ 3 <= n -> n < 3.
Proof.
  apply (avoid_run nat (fun a b => b = S a) rnat (fun n => 3 <= n) (fun n => n < 3) 0).
  - intros Q Q0 QS n R. induction R as [|n R IH]; [exact Q0|]. apply (QS n (S n) R IH eq_refl).
  - intros s t _ B ->. auto.
  - auto.
  - intros s t _ _ -> Nb. lia.
Qed.

Lemma avoidNeg : ~ (forall n, rnat n -> n < 3).
Proof. intros H. assert (R : rnat 3) by repeat constructor. specialize (H 3 R). lia. Qed.
