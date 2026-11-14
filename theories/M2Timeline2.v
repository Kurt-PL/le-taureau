(* Model2: the rule in its two-level timeline wording, and its equivalence
   with the event graph (tl2ok_iff_evok).

   Per cell. Every cell has a timeline. On it stand the accesses to the
   cell: writes in their history's order (ctl_hist); a read right after
   the write it took (ctl_took) and before the newer writes (ctl_newer); a
   context's accesses to the cell in their own order (ctl_po); and an
   access after the writes of the cell that it knows in order, guard.rl()
   included (ctl_know). No access comes before itself on any cell's
   timeline.

   Across cells. No access comes before itself through the histories
   (gtl_hist), the writes a read missed (gtl_newer) and what each access
   knows in order through guard() and the writes it took in order
   (gtl_know); what guard.rl() adds does not count across cells.

   A context's own order and a read's take count on the cell's timeline
   only; across cells, a read is after the write it took only if it knows
   that write in order (R3), which excludes the context's own stores not
   known in order (forwarding). *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO M2Comp M2Lit M2Neg M2LitNeg
  M2Ev M2Acyc M2EvLit M2NegQ M2Timeline M2TimelineEq M2Parade.

(* the write a read took in x is older than w, or it took the initial value *)
Definition newer_than (h : hist) (o : option nat) (w : nat) : Prop :=
  match o with None => True | Some u => older h u w end.

Inductive ctl (s : M2Model.st) (x : cell) : nat -> nat -> Prop :=
| ctl_hist : forall a b, older (hs s x) a b -> ctl s x a b
| ctl_took : forall b e u, nth_error (lg s) b = Some e -> In x (eR e) -> erf e x = Some u -> u <> b -> ctl s x u b
| ctl_newer : forall a e w, nth_error (lg s) a = Some e -> In x (eR e) -> In w (ids (hs s x)) -> w <> a ->
    newer_than (hs s x) (erf e x) w -> ctl s x a w
| ctl_po : forall a b ea eb, nth_error (lg s) a = Some ea -> nth_error (lg s) b = Some eb ->
    ec ea = ec eb -> ek ea < ek eb -> In x (eC ea) -> In x (eC eb) -> ctl s x a b
| ctl_know : forall b e w, nth_error (lg s) b = Some e -> In x (eC e) -> (eQ e w \/ eQc e w) -> In w (ids (hs s x)) -> w <> b ->
    ctl s x w b.

Inductive gtl (s : M2Model.st) : nat -> nat -> Prop :=
| gtl_hist : forall x a b, older (hs s x) a b -> gtl s a b
| gtl_newer : forall x a e w, nth_error (lg s) a = Some e -> In x (eR e) -> In w (ids (hs s x)) -> w <> a ->
    newer_than (hs s x) (erf e x) w -> gtl s a w
| gtl_know : forall b e w, nth_error (lg s) b = Some e -> eQ e w -> w <> b -> gtl s w b.

Definition tl2ok (s : M2Model.st) : Prop :=
  (forall x a, ~ clos_trans nat (ctl s x) a a) /\ (forall a, ~ clos_trans nat (gtl s) a a).

Lemma ctl_cedge : forall s x a b, ctl s x a b <-> cedge s x a b.
Proof.
  intros s x a b. split.
  - intros [a0 b0 O|b0 e u L I E N|a0 e w L I Iw N M|a0 b0 ea eb La Lb C K Xa Xb|b0 e w L I Q Iw N].
    + left. exact O.
    + right; right; left. exists e. repeat split; auto.
    + right; left. exists e. split; [exact L|]. split; [exact I|]. split; [exact Iw|]. split; [exact N|exact M].
    + right; right; right; right. exists ea, eb. repeat split; auto.
    + right; right; right; left. exists e. repeat split; auto.
  - intros [O|[(e & L & I & Iw & N & M)|[(e & L & I & E & N)|[(e & L & I & Q & Iw & N)|(ea & eb & La & Lb & C & K & Xa & Xb)]]]].
    + apply ctl_hist. exact O.
    + apply (ctl_newer s x a e b L I Iw N M).
    + apply (ctl_took s x b e a L I E N).
    + apply (ctl_know s x b e a L I Q Iw N).
    + apply (ctl_po s x a b ea eb La Lb C K Xa Xb).
Qed.

Lemma gtl_gedge : forall s a b, gtl s a b <-> gedge s a b.
Proof.
  intros s a b. split.
  - intros [x a0 b0 O|x a0 e w L I Iw N M|b0 e w L Q N].
    + left. exists x. exact O.
    + right; left. exists e, x. split; [exact L|]. split; [exact I|]. split; [exact Iw|]. split; [exact N|exact M].
    + right; right. exists e. repeat split; auto.
  - intros [(x & O)|[(e & x & L & I & Iw & N & M)|(e & L & Q & N)]].
    + apply (gtl_hist s x a b O).
    + apply (gtl_newer s x a e b L I Iw N M).
    + apply (gtl_know s b e a L Q N).
Qed.

Lemma ct_iff : forall (R1 R2 : nat -> nat -> Prop), (forall a b, R1 a b <-> R2 a b) ->
  forall a b, clos_trans nat R1 a b <-> clos_trans nat R2 a b.
Proof.
  intros R1 R2 E a b. split; intros H; induction H as [a b H|a c b _ IH1 _ IH2];
    try (constructor; apply E; exact H); apply t_trans with c; auto.
Qed.

Theorem tl2ok_iff_evok : forall s, tl2ok s <-> evok s.
Proof.
  intros s. unfold tl2ok, evok. split.
  - intros [C G]. split.
    + intros a T. apply (G a). apply (proj2 (ct_iff _ _ (gtl_gedge s) a a)). exact T.
    + intros x a T. apply (C x a). apply (proj2 (ct_iff _ _ (ctl_cedge s x) a a)). exact T.
  - intros [G C]. split.
    + intros x a T. apply (C x a). apply (proj1 (ct_iff _ _ (ctl_cedge s x) a a)). exact T.
    + intros a T. apply (G a). apply (proj1 (ct_iff _ _ (gtl_gedge s) a a)). exact T.
Qed.

(* ---------- separate ranks for the two levels ---------- *)
Lemma tl2ok_rank : forall s (rg rc : nat -> nat),
  (forall a b, gtl s a b -> rg a < rg b) -> (forall x a b, ctl s x a b -> rc a < rc b) -> tl2ok s.
Proof.
  intros s rg rc G C. split.
  - intros x a T. assert (Q : forall a b, clos_trans nat (ctl s x) a b -> rc a < rc b)
      by (intros a0 b0 T0; induction T0; [apply (C x); auto|lia]). specialize (Q a a T). lia.
  - intros a T. assert (Q : forall a b, clos_trans nat (gtl s) a b -> rg a < rg b)
      by (intros a0 b0 T0; induction T0; [apply G; auto|lia]). specialize (Q a a T). lia.
Qed.

Lemma evok_rank2 : forall s (rg rc : nat -> nat),
  (forall a b, gedge s a b -> rg a < rg b) -> (forall x a b, cedge s x a b -> rc a < rc b) -> evok s.
Proof.
  intros s rg rc G C. apply (proj1 (tl2ok_iff_evok s)). apply (tl2ok_rank s rg rc).
  - intros a b H. apply G. apply gtl_gedge. exact H.
  - intros x a b H. apply (C x). apply ctl_cedge. exact H.
Qed.


(* the per-cell edges, with knowledge counted only for writes of the cell *)
Ltac ev_cedge2 :=
  let x := fresh "x" in let a := fresh "a" in let b := fresh "b" in let E := fresh "E" in
  let O := fresh "O" in let e := fresh "e" in let e2 := fresh "e" in
  let L := fresh "L" in let L2 := fresh "L" in let Ix := fresh "Ix" in let Ib := fresh "Ib" in
  let N := fresh "N" in let M := fresh "M" in let Q := fresh "Q" in let C := fresh "C" in let K := fresh "K" in
  intros x a b E;
  destruct E as [O|[(e & L & Ix & Ib & N & M)|[(e & L & Ix & M & N)|[(e & L & Ix & Q & Ib & N)|(e & e2 & L & L2 & C & K & Ix & Ib)]]]];
  [ apply older_pairs in O; cell4 x; inlist O; try (injection O as <- <-); rk_close
  | at_ent L a; inlist Ix; subst x; inlist Ib; subst b; vm_compute in M;
    try (apply older_b in M; vm_compute in M; discriminate); rk_close
  | at_ent L b; inlist Ix; subst x; vm_compute in M; first [discriminate M | injection M as <-]; rk_close
  | at_ent L b; inlist Ix; subst x; inlist Ib; subst a; vm_compute in Q;
    first [rk_close | (kn' Q; try discriminate; try (exfalso; lia); try refute_neg; rk_close)]
  | at_ent L a; at_ent L2 b; vm_compute in C, K; try discriminate; try lia;
    inlist Ix; subst x; inlist Ib; rk_close ].

Ltac evok_tac2 ordg ordc := apply (evok_rank2 _ (fun a => idx a ordg) (fun a => idx a ordc)); [ev_gedge|ev_cedge2].

(* ---------- reads of several cells on concrete runs ---------- *)
Definition srcl (l : list (cell * option nat)) : cell -> option nat :=
  fun z => match find (fun q => Nat.eqb (fst q) z) l with Some q => snd q | None => None end.

Lemma srcl_out : forall l z, ~ In z (map fst l) -> srcl l z = None.
Proof.
  intros l z. unfold srcl. induction l as [|[y o] l IH]; intros N; simpl; auto.
  destruct (Nat.eqb_spec y z) as [E|E]; [exfalso; apply N; left; simpl; auto|].
  apply IH. intros I. apply N. right. auto.
Qed.

Lemma takesl : forall H l, Forall (fun q => inhist (H (fst q)) (srcl l (fst q))) l -> takes H (map fst l) (srcl l).
Proof.
  intros H l F. split.
  - intros x I. apply in_map_iff in I. destruct I as (q & <- & I). rewrite Forall_forall in F. exact (F q I).
  - intros x N. apply srcl_out. exact N.
Qed.

Ltac LDL l := eapply (e_ld _ _ _ _ _ _ (srcl l)); [reflexivity|];
  match goal with |- takes ?H (dd ?xs) _ => replace (dd xs) with (map fst l) by (vm_compute; reflexivity) end;
  apply takesl; repeat constructor; vm_compute; first [exact I | tauto].


(* knowledge in order on a concrete state: the take, not the context's own unpublished store *)
Ltac know_took := vm_compute; right; split;
  [first [exists 0; reflexivity|exists 1; reflexivity|exists 2; reflexivity|exists 3; reflexivity]|];
  let H := fresh "H" in intros [H _]; kn' H; try discriminate; subst; cbn in *; discriminate.
(* knowledge in order on a concrete state: the in-order view *)
Ltac know_ord := vm_compute; left; firstorder.
(* an access that took nothing in the cell does not stand apart *)
Ltac not_apart := right; split; [reflexivity|];
  let e0 := fresh "e" in let u0 := fresh "u" in let L0 := fresh "L" in let Eu := fresh "Eu" in
  intros (e0 & u0 & L0 & _ & _ & _ & Eu & _); vm_compute in L0; injection L0 as <-; vm_compute in Eu; discriminate.

