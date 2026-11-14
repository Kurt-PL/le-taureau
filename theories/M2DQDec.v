(* Closed deciders for the last checks of a concrete run.
   done (by done_tp) and the two log premises of evok_time (missed newer
   writes; a context's own order on a cell) each become one boolean over
   the final state, so a concrete run is checked by one computation per
   premise instead of one per log entry or pair of entries. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Lit.

(* done_tp's premise *)
Definition done_b {A} (P : list (list A)) (s : M2Model.st) : bool :=
  forallb (fun c => (length (nth c P []) <=? pcs s c) && (tp s c <=? pcs s c)) (seq 0 (length P)).

Lemma done_dec : forall A (P : list (list A)) s, done_b P s = true ->
  forall c, c < length P -> length (nth c P []) <= pcs s c /\ tp s c <= pcs s c.
Proof.
  intros A P s B c Hc. unfold done_b in B. rewrite forallb_forall in B.
  specialize (B c ltac:(apply in_seq; lia)). apply andb_true_iff in B. destruct B as [B1 B2].
  apply Nat.leb_le in B1. apply Nat.leb_le in B2. split; assumption.
Qed.

(* evok_time's second premise: a read that missed a newer write is earlier *)
Definition newer_b (s : M2Model.st) : bool :=
  forallb (fun a => match nth_error (lg s) a with None => true | Some e =>
    forallb (fun x => forallb (fun w => (w =? a) || (a <? w) ||
        match erf e x with None => false | Some u => negb (olderb (hs s x) u w) end)
      (ids (hs s x))) (eR e) end) (seq 0 (length (lg s))).

Lemma newer_dec : forall s, newer_b s = true ->
  forall a e x w, nth_error (lg s) a = Some e -> In x (eR e) -> In w (ids (hs s x)) -> w <> a ->
     match erf e x with None => True | Some u => older (hs s x) u w end -> a < w.
Proof.
  intros s B a e x w L Ix Iw N M. unfold newer_b in B. rewrite forallb_forall in B.
  assert (Ha : a < length (lg s)) by (apply nth_error_Some; rewrite L; discriminate).
  specialize (B a ltac:(apply in_seq; lia)). rewrite L in B.
  rewrite forallb_forall in B. specialize (B x Ix). rewrite forallb_forall in B. specialize (B w Iw).
  apply orb_true_iff in B. destruct B as [B|B]; [apply orb_true_iff in B; destruct B as [B|B]|].
  - apply Nat.eqb_eq in B. exfalso. exact (N B).
  - apply Nat.ltb_lt in B. exact B.
  - destruct (erf e x) as [u|]; [|discriminate B].
    apply older_b in M. rewrite M in B. discriminate B.
Qed.

(* evok_time's third premise: a context's own order on a cell *)
Definition po_b (s : M2Model.st) : bool :=
  forallb (fun a => match nth_error (lg s) a with None => true | Some ea =>
    forallb (fun b => match nth_error (lg s) b with None => true | Some eb =>
      negb (ec ea =? ec eb) || negb (ek ea <? ek eb) || negb (meetb (eC ea) (eC eb)) || (a <? b) end)
    (seq 0 (length (lg s))) end) (seq 0 (length (lg s))).

Lemma po_dec : forall s, po_b s = true ->
  forall x a b ea eb, nth_error (lg s) a = Some ea -> nth_error (lg s) b = Some eb -> ec ea = ec eb ->
    ek ea < ek eb -> In x (eC ea) -> In x (eC eb) -> a < b.
Proof.
  intros s B x a b ea eb La Lb C K Xa Xb. unfold po_b in B. rewrite forallb_forall in B.
  assert (Ha : a < length (lg s)) by (apply nth_error_Some; rewrite La; discriminate).
  assert (Hb : b < length (lg s)) by (apply nth_error_Some; rewrite Lb; discriminate).
  specialize (B a ltac:(apply in_seq; lia)). rewrite La in B. rewrite forallb_forall in B.
  specialize (B b ltac:(apply in_seq; lia)). rewrite Lb in B.
  assert (M : meetb (eC ea) (eC eb) = true) by (apply meetb_spec; exists x; split; assumption).
  rewrite M, C, Nat.eqb_refl in B. apply Nat.ltb_lt in K. rewrite K in B. simpl in B.
  apply Nat.ltb_lt in B. exact B.
Qed.

Print Assumptions done_dec.
Print Assumptions newer_dec.
Print Assumptions po_dec.
