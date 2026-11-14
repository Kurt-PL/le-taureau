(* Oracle rows IRIW.weak and 2+2W.weak (oracle/ORACLE.md), admitted, on M2DQ.
   In these runs a write's place in its history, or a read that missed a
   newer write, goes against time: evok_time (rank = time) does not apply.
   evok_first: evok with a rank that is time except that one event m comes
   first. Every edge out of m then grows; an edge into m must not exist, and
   for what m knows, took or knows in order within a cell that is a fact
   about m's own log entry. The remaining edges are those of evok_time, with
   the rank in place of time; closed deciders check them on a concrete run. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO M2Lit M2Ev M2EvLit M2Acyc M2Timeline2 M2Oota M2CasSplitProof M2EvTimeProof M2DA M2DP M2DQ M2DQDec.
Require Import M2DQSTWLOCKRELInst M2DQOracleRows.

(* ---------- evok by a rank ---------- *)
Lemma evok_rk : forall p s (rk : nat -> nat) m, run p s ->
  (forall x a b, older (hs s x) a b -> rk a < rk b) ->
  (forall a e x w, nth_error (lg s) a = Some e -> In x (eR e) -> In w (ids (hs s x)) -> w <> a ->
     match erf e x with None => True | Some u => older (hs s x) u w end -> rk a < rk w) ->
  (forall x a b ea eb, nth_error (lg s) a = Some ea -> nth_error (lg s) b = Some eb -> ec ea = ec eb ->
     ek ea < ek eb -> In x (eC ea) -> In x (eC eb) -> rk a < rk b) ->
  (forall a b, a < b -> b <> m -> rk a < rk b) ->
  match nth_error (lg s) m with
  | Some e => (forall a, eQ e a -> a = m) /\ (forall x a, erf e x = Some a -> False) /\
              (forall x, In x (eC e) -> forall a, eQc e a -> In a (ids (hs s x)) -> False)
  | None => True
  end ->
  evok s.
Proof.
  intros p s rk m R Hh Hn Hp Hm He. destruct (InvO_run p s R) as [I J _ O].
  assert (Hm' : forall e, nth_error (lg s) m = Some e ->
    (forall a, eQ e a -> a = m) /\ (forall x a, erf e x = Some a -> False) /\
    (forall x, In x (eC e) -> forall a, eQc e a -> In a (ids (hs s x)) -> False))
    by (intros e L; rewrite L in He; exact He).
  apply (evok_rank s rk).
  - intros a b [(x & Ol)|[(e & x & L & Ix & Ib & N & M)|(e & L & Q & N)]].
    + exact (Hh x a b Ol).
    + exact (Hn a e x b L Ix Ib N M).
    + destruct (Nat.eq_dec b m) as [->|Nb].
      * destruct (Hm' e L) as (Q0 & _). pose proof (Q0 a Q). congruence.
      * pose proof (eQ_le p s R b e a L Q). apply Hm; [lia|exact Nb].
  - intros x a b [Ol|[(e & L & Ix & Ib & N & M)|[(e & L & Ix & Ef & N)|[(e & L & Ix & Q & Ib & N)|(ea & eb & La & Lb & C & K & Xa & Xb)]]]].
    + exact (Hh x a b Ol).
    + exact (Hn a e x b L Ix Ib N M).
    + destruct (Nat.eq_dec b m) as [->|Nb].
      * destruct (Hm' e L) as (_ & F & _). destruct (F x a Ef).
      * destruct (j_rf p s J b e x a L Ef) as (Lt & _). apply Hm; [exact Lt|exact Nb].
    + destruct (Nat.eq_dec b m) as [->|Nb].
      * destruct (Hm' e L) as (Q0 & _ & F). destruct Q as [Q|Q];
          [pose proof (Q0 a Q); congruence|destruct (F x Ix a Q Ib)].
      * apply Hm; [|exact Nb]. destruct Q as [Q|Q];
          [pose proof (eQ_le p s R b e a L Q); lia|exact (eQc_lt p s R b e a L Q)].
    + exact (Hp x a b ea eb La Lb C K Xa Xb).
Qed.

(* the rank: time, except that m comes first *)
Definition rkm (m a : nat) : nat := if Nat.eqb a m then 0 else S a.

Lemma rkm_mono : forall m a b, a < b -> b <> m -> rkm m a < rkm m b.
Proof.
  intros m a b L N. unfold rkm. destruct (Nat.eqb_spec a m); destruct (Nat.eqb_spec b m); lia.
Qed.

(* ---------- closed deciders, with a rank ---------- *)
Definition hist_rb (rk : nat -> nat) (n : nat) (s : M2Model.st) : bool :=
  forallb (fun x => forallb (fun ab => rk (fst ab) <? rk (snd ab)) (pairs (ids (hs s x)))) (seq 0 n).

Lemma hist_rdec : forall rk n s, hist_rb rk n s = true -> (forall x, n <= x -> hs s x = []) ->
  forall x a b, older (hs s x) a b -> rk a < rk b.
Proof.
  intros rk n s B Z x a b O. apply older_pairs in O.
  destruct (Nat.lt_ge_cases x n) as [L|G]; [|rewrite (Z x G) in O; destruct O].
  unfold hist_rb in B. rewrite forallb_forall in B. specialize (B x ltac:(apply in_seq; lia)).
  rewrite forallb_forall in B. specialize (B (a, b) O). apply Nat.ltb_lt. exact B.
Qed.

Definition newer_rb (rk : nat -> nat) (s : M2Model.st) : bool :=
  forallb (fun a => match nth_error (lg s) a with None => true | Some e =>
    forallb (fun x => forallb (fun w => (w =? a) || (rk a <? rk w) ||
        match erf e x with None => false | Some u => negb (olderb (hs s x) u w) end)
      (ids (hs s x))) (eR e) end) (seq 0 (length (lg s))).

Lemma newer_rdec : forall rk s, newer_rb rk s = true ->
  forall a e x w, nth_error (lg s) a = Some e -> In x (eR e) -> In w (ids (hs s x)) -> w <> a ->
     match erf e x with None => True | Some u => older (hs s x) u w end -> rk a < rk w.
Proof.
  intros rk s B a e x w L Ix Iw N M. unfold newer_rb in B. rewrite forallb_forall in B.
  assert (Ha : a < length (lg s)) by (apply nth_error_Some; rewrite L; discriminate).
  specialize (B a ltac:(apply in_seq; lia)). rewrite L in B.
  rewrite forallb_forall in B. specialize (B x Ix). rewrite forallb_forall in B. specialize (B w Iw).
  apply orb_true_iff in B. destruct B as [B|B]; [apply orb_true_iff in B; destruct B as [B|B]|].
  - apply Nat.eqb_eq in B. exfalso. exact (N B).
  - apply Nat.ltb_lt. exact B.
  - destruct (erf e x) as [u|]; [|discriminate B].
    apply older_b in M. rewrite M in B. discriminate B.
Qed.

Definition po_rb (rk : nat -> nat) (s : M2Model.st) : bool :=
  forallb (fun a => match nth_error (lg s) a with None => true | Some ea =>
    forallb (fun b => match nth_error (lg s) b with None => true | Some eb =>
      negb (ec ea =? ec eb) || negb (ek ea <? ek eb) || negb (meetb (eC ea) (eC eb)) || (rk a <? rk b) end)
    (seq 0 (length (lg s))) end) (seq 0 (length (lg s))).

Lemma po_rdec : forall rk s, po_rb rk s = true ->
  forall x a b ea eb, nth_error (lg s) a = Some ea -> nth_error (lg s) b = Some eb -> ec ea = ec eb ->
    ek ea < ek eb -> In x (eC ea) -> In x (eC eb) -> rk a < rk b.
Proof.
  intros rk s B x a b ea eb La Lb C K Xa Xb. unfold po_rb in B. rewrite forallb_forall in B.
  assert (Ha : a < length (lg s)) by (apply nth_error_Some; rewrite La; discriminate).
  assert (Hb : b < length (lg s)) by (apply nth_error_Some; rewrite Lb; discriminate).
  specialize (B a ltac:(apply in_seq; lia)). rewrite La in B. rewrite forallb_forall in B.
  specialize (B b ltac:(apply in_seq; lia)). rewrite Lb in B.
  assert (Mt : meetb (eC ea) (eC eb) = true) by (apply meetb_spec; exists x; split; assumption).
  rewrite Mt, C, Nat.eqb_refl in B. apply Nat.ltb_lt in K. rewrite K in B. simpl in B.
  apply Nat.ltb_lt. exact B.
Qed.

(* the facts about m's entry: computed in the goal, then taken apart *)
Lemma some_eq' : forall A (a b : A), Some a = Some b -> a = b.
Proof. congruence. Qed.
Ltac kill := repeat match goal with
  | H : _ -> False |- _ => clear H
  | H : False |- _ => destruct H
  | H : _ \/ _ |- _ => destruct H
  | H : _ /\ _ |- _ => destruct H
  | H : exists _, _ |- _ => destruct H
  | H : None = Some _ |- _ => discriminate H
  | H : Some _ = None |- _ => discriminate H
  | H : Some _ = Some _ |- _ => apply some_eq' in H
  | H : ?a = ?b |- _ => first [is_var a | is_var b]; subst
  | H : ?P |- _ => match type of P with Prop => progress (cbv beta iota in H) end
  | H : context [match ?t with _ => _ end] |- _ => is_var t; destruct t
  | H : true = false |- _ => discriminate H
  | H : false = true |- _ => discriminate H
  | H : context [if ?b then _ else _] |- _ => destruct b eqn:?
  end; try congruence.
Ltac MFACT := vm_compute;
  split; [intros ? ?; kill|split; [intros ? ? ?; kill|intros ? ?; kill; vm_compute; intros ? ? ?; kill]].
Ltac EVOKm R m n := apply (evok_rk _ _ (rkm m) m R);
  [apply (hist_rdec _ n); [vm_compute; reflexivity|let x := fresh "x" in let L := fresh "L" in
     intros x L; repeat (destruct x as [|x]; [lia|]); reflexivity]
  |refine (newer_rdec _ _ _); vm_compute; reflexivity
  |refine (po_rdec _ _ _); vm_compute; reflexivity
  |exact (rkm_mono m)
  |MFACT].
Ltac FINm m n := finV; let R := fresh "R" in intros R; split; [DONE R|split; [EVOKm R m n|OUT]].

(* ---------- IRIW.weak: the second reader's read of x (time 7) first ---------- *)
Definition IRIWw : prog := stat [ [st 0 1]; [ld 0; fll; ld 1]; [st 1 1]; [ld 1; fll; ld 0] ].
Theorem IRIW_weak_allowed : exists s, runQ IRIWw s /\ done IRIWw s /\ evok s /\
  rg (cs s 1) 0 = 1 /\ rg (cs s 1) 2 = 0 /\ rg (cs s 3) 0 = 1 /\ rg (cs s 3) 2 = 0.
Proof.
  apply startV.
  eapply fwdV. { ord 0. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 1. LDw 0. } { nwP. } nameV.
  eapply fwdV. { ord 1. apply e_ll. } { nwP. } nameV.
  eapply fwdV. { ord 1. LD0. } { nwP. } nameV.
  eapply fwdV. { ord 2. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 3. LDw 4. } { nwP. } nameV.
  eapply fwdV. { ord 3. apply e_ll. } { nwP. } nameV.
  eapply fwdV. { ord 3. LD0. } { nwP. } nameV.
  FINm 7 2.
Qed.

(* ---------- 2+2W.weak: the second writer's x = 2 (time 5) first, placed before x = 1 ---------- *)
Definition W22w : prog := stat [ [st 0 1; fss; st 1 2]; [st 1 1; fss; st 0 2] ].
Theorem W22_weak_allowed : exists s, runQ W22w s /\ done W22w s /\ evok s /\
  final s 0 = 1 /\ final s 1 = 1.
Proof.
  apply startV.
  eapply fwdV. { ord 0. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 0. apply e_ss. } { nwP. } nameV.
  eapply fwdV. { ord 0. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 1. STa 2. } { nwP. } nameV.
  eapply fwdV. { ord 1. apply e_ss. } { nwP. } nameV.
  eapply fwdV. { ord 1. ST. enter_at (@nil (nat * bool)) [(0, false)]. } { nwP. } nameV.
  FINm 5 2.
Qed.
