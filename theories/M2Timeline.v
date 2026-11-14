(* Model2: the rule in its timeline wording.

   R2. Every cell has a timeline. On it, every access to the cell stands at
   a place: writes in their history's order, a read right after the write
   it took and before the newer writes, and a context's accesses to the
   cell in their own order. An indivisible access stands at one place in
   all its cells; where one that writes nothing takes its context's own
   store not known in order, it stands there apart, right after that
   store, and its common place stays only before the newer writes. No
   access comes before itself through the timelines and what it knows in
   order.

   A node is an access's common place (t, None) or its place apart in a
   cell (t, Some x). `tlok` is the rule; `M2TimelineEq` proves it the same
   as `evok`. *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model.

Definition tnode : Type := (nat * option cell)%type.

(* an access that writes nothing and takes, in one of its several cells,
   its context's own store that it does not know in order *)
Definition apart (s : st) (t : nat) (x : cell) : Prop :=
  exists e u, nth_error (lg s) t = Some e /\ ew e = false /\ 2 <= length (eC e) /\ In x (eR e) /\
    erf e x = Some u /\ ownw s (ec e) u /\ ~ eQ e u.

(* where access t stands on the timeline of cell x *)
Definition pl (s : st) (t : nat) (x : cell) (n : tnode) : Prop :=
  (n = (t, Some x) /\ apart s t x) \/ (n = (t, None) /\ ~ apart s t x).

Inductive tl (s : st) : tnode -> tnode -> Prop :=
(* writes in their history's order *)
| tl_hist : forall x a b na nb, older (hs s x) a b -> pl s a x na -> pl s b x nb -> tl s na nb
(* a read right after the write it took *)
| tl_took : forall x b e u nb, nth_error (lg s) b = Some e -> In x (eR e) -> erf e x = Some u -> u <> b ->
    pl s b x nb -> tl s (u, None) nb
(* and before the newer writes, from where it stands and from its common place *)
| tl_miss : forall x a e w na, nth_error (lg s) a = Some e -> In x (eR e) -> In w (ids (hs s x)) -> w <> a ->
    match erf e x with None => True | Some u => older (hs s x) u w end ->
    (pl s a x na \/ na = (a, None)) -> tl s na (w, None)
(* a context's accesses to the cell in their own order *)
| tl_po : forall x a b ea eb na nb, nth_error (lg s) a = Some ea -> nth_error (lg s) b = Some eb ->
    ec ea = ec eb -> ek ea < ek eb -> In x (eC ea) -> In x (eC eb) -> pl s a x na -> pl s b x nb -> tl s na nb
(* an access after what it knows in order *)
| tl_know : forall b e w, nth_error (lg s) b = Some e -> eQ e w -> w <> b -> tl s (w, None) (b, None)
(* within a cell, an access after the writes there it knows in order, guard.rl() included *)
| tl_knowc : forall x b e w nw nb, nth_error (lg s) b = Some e -> In x (eC e) -> eQc e w -> In w (ids (hs s x)) ->
    w <> b -> pl s w x nw -> pl s b x nb -> tl s nw nb.

Definition tlok (s : st) : Prop := forall n, ~ clos_trans tnode (tl s) n n.
