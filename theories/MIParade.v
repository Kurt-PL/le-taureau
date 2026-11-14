(* Model2, the parade: two-cell accesses as litmus instances. Cells: the low
   half 0 and the high half 1 of one `ui8` value; one-cell accesses are its
   `ui4` halves, seen through `%` casts in airside. *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO MIComp M2Lit MINeg MILitNeg M2Ev M2Acyc M2EvLit MINegQ.
Require Import M2Iface.

Section Iface.
Context `{IFM : Model}.

(* ---------- two cells ---------- *)
Lemma dd2 : forall x y, x <> y -> dd [x; y] = [x; y].
Proof.
  intros x y N. unfold dd. cbn [nodup].
  destruct (in_dec Nat.eq_dec y []) as [[]|_].
  destruct (in_dec Nat.eq_dec x [y]) as [[E|[]]|_]; [congruence|reflexivity].
Qed.

Lemma places2 : forall H x y t hx hy, x <> y -> place1 (H x) t hx -> place1 (H y) t hy ->
  places H [x; y] t (upd (upd H x hx) y hy).
Proof.
  intros H x y t hx hy N Ex Ey z. split; intros Z.
  - destruct Z as [<-|[<-|[]]]; unfold upd.
    + destruct (Nat.eqb_spec x y); [congruence|]. rewrite Nat.eqb_refl. exact Ex.
    + rewrite Nat.eqb_refl. exact Ey.
  - unfold upd. destruct (Nat.eqb_spec z y); [subst; exfalso; apply Z; right; left; auto|].
    destruct (Nat.eqb_spec z x); [subst; exfalso; apply Z; left; auto|auto].
Qed.

(* the source of a two-cell read *)
Definition src2 (x : cell) (ox : option nat) (y : cell) (oy : option nat) : cell -> option nat :=
  fun z => if Nat.eqb z x then ox else if Nat.eqb z y then oy else None.

Lemma takes2 : forall H x y ox oy, x <> y -> inhist (H x) ox -> inhist (H y) oy ->
  takes H [x; y] (src2 x ox y oy).
Proof.
  intros H x y ox oy N Vx Vy. split.
  - intros z [<-|[<-|[]]]; unfold src2; [rewrite Nat.eqb_refl; exact Vx|].
    destruct (Nat.eqb_spec y x); [congruence|]. rewrite Nat.eqb_refl. exact Vy.
  - intros z Z. unfold src2. destruct (Nat.eqb_spec z x); [subst; exfalso; apply Z; left; auto|].
    destruct (Nat.eqb_spec z y); [subst; exfalso; apply Z; right; left; auto|auto].
Qed.

Lemma e_st2 : forall t md x y c v r m hx hy, x <> y -> c r = true ->
  place1 (mH m x) t hx -> place1 (mH m y) t hy ->
  eff t (ISt md [x; y] c v) r m
      (wput m (dd [x; y]) t (projs (length (dd [x; y])) (v r)) (upd (upd (mH m) x hx) y hy)) 0 (mP m) nosrc true.
Proof.
  intros t md x y c v r m hx hy N C Ex Ey. apply e_st; [exact C|].
  rewrite (dd2 x y N). apply places2; auto.
Qed.

Lemma e_ld2 : forall t md x y c r m ox oy, x <> y -> c r = true ->
  inhist (mH m x) ox -> inhist (mH m y) oy ->
  eff t (ILd md [x; y] c) r m (learn m (src2 x ox y oy)) (enc (rdvals m (dd [x; y]) (src2 x ox y oy)))
      (mP m) (src2 x ox y oy) false.
Proof.
  intros t md x y c r m ox oy N C Vx Vy. apply e_ld; [exact C|]. rewrite (dd2 x y N). apply takes2; auto.
Qed.

End Iface.
Ltac nz7 := intros c' k' ? i' H' Ic'; destruct c' as [|[|[|[|[|c']]]]]; destruct k' as [|[|[|[|[|[|[|k']]]]]]];
  vm_compute in H'; subst i'; vm_compute in Ic';
  repeat match type of Ic' with _ \/ _ => destruct Ic' as [Ic'|Ic'] | False => destruct Ic' end; try discriminate;
  let S := fresh "S" in let r := fresh "r" in let Z := fresh "Z" in intros S r Z; vm_compute in S, Z; discriminate.
Section Iface.
Context `{IFM : Model}.
End Iface.
Ltac NZ7 P x := assert (forall c' k' r i', ins P c' k' r = i' -> In x (icells i') -> is_store i' = true ->
                  forall r, cval (icells i') (wvals i' r) x <> 0) by nz7.
Section Iface.
Context `{IFM : Model}.

End Iface.
Ltac W0 := enter_at (@nil (nat * bool)) (@nil (nat * bool)).
Section Iface.
Context `{IFM : Model}.
End Iface.
Ltac ST := eapply e_st1; [reflexivity|].
Section Iface.
Context `{IFM : Model}.

(* ---------- Rmc: fenced code stays SC ----------
   M: guard(); ui8 store (1, 1); guard()
   E: guard(); high half = 2; guard(); r = low half; guard()
   r = 0 with the high half finally 2 would need M's store after E's load
   (the load missed it in the low half), before E's store (the high half),
   and E's store before E's load (the load knows it in order, through the
   guard()). The ui8 store is one event, so that is a cycle. *)
Definition Rmc : prog := stat [ [ffull; ISt Plain [0; 1] T (K (enc [1; 1])); ffull]; [ffull; st 1 2; ffull; ld 0; ffull] ].

Theorem Rmc_forbidden : forall s, reach (STEP Rmc) s -> done Rmc s -> evok s -> ~ (rg (cs s 1) 3 = 0 /\ final s 1 = 2).
Proof.
  intros s R CP EV (A & B). assert (W : wf Rmc) by wf_tac.
  get_ent Rmc s R CP W 0 1 E01. get_ent Rmc s R CP W 1 1 E11. get_ent Rmc s R CP W 1 2 E12.
  get_ent Rmc s R CP W 1 3 E13. NZ7 Rmc 0.
  pose proof (read0 Rmc s R CP W 1 3 _ 0 E13 eq_refl eq_refl eq_refl H2 Ei2 A H3) as N0.
  destruct (n_final Rmc s R CP W 1 2 B ltac:(lia)) as (z & Iz & Vz & Last).
  pose proof (n_wr_of Rmc s R CP W 1 z Iz) as WO. which_writer WO. subst z.
  assert (Wm : ew E01 = true) by (rewrite (n_ew Rmc s R CP W 0 1 _ E01 eq_refl H Ei); reflexivity).
  destruct (n_wr Rmc s R CP W 0 1 _ 0 E01 eq_refl H Ei Wm (or_introl eq_refl)) as (I0m & _).
  destruct (n_wr Rmc s R CP W 0 1 _ 1 E01 eq_refl H Ei Wm (or_intror (or_introl eq_refl))) as (I1m & _).
  destruct (stw Rmc s R CP W 1 1 _ _ _ _ E11 eq_refl eq_refl H0 Ei0) as (_ & _ & S11).
  destruct (n_po Rmc s R CP W 1 1 2 _ _ E11 E12 ltac:(lia) eq_refl eq_refl eq_refl ltac:(tie) H0 H1) as [_ P].
  assert (Q : eQ E13 (bt s 1 1)).
  { apply (Q_guard Rmc s R CP W EV 1 2 3 E12 E13 ltac:(lia) eq_refl H1 H2 ltac:(nn)).
    - right. exists (ld 0). split; [exact Ei2|reflexivity].
    - apply P, S11. }
  apply (g3 Rmc s R CP W EV (bt s 0 1) (bt s 1 1) (bt s 1 3)).
  - apply (g_hist Rmc s R CP W EV 1). apply Last; [exact I1m|].
    apply (neq_bt Rmc s R CP W 0 1 1 1 _ _ eq_refl ltac:(nn) eq_refl eq_refl ltac:(nn) eq_refl). congruence.
  - apply (g_known Rmc s R CP W EV 1 3 E13); [exact H2|exact Q|].
    apply (neq_bt Rmc s R CP W 1 1 1 3 _ _ eq_refl ltac:(nn) eq_refl eq_refl ltac:(nn) eq_refl). congruence.
  - apply (g_missed Rmc s R CP W EV 1 3 (ld 0) 0 E13 (bt s 0 1) eq_refl eq_refl (or_introl eq_refl) H2 Ei2 I0m);
      [|left; exact N0].
    apply (neq_bt Rmc s R CP W 0 1 1 3 _ _ eq_refl ltac:(nn) eq_refl eq_refl ltac:(nn) eq_refl). congruence.
Qed.

(* the same with the halves' roles exchanged: E stores the low half and reads the high half *)
Definition RmcM : prog := stat [ [ffull; ISt Plain [0; 1] T (K (enc [1; 1])); ffull]; [ffull; st 0 2; ffull; ld 1; ffull] ].

Theorem RmcM_forbidden : forall s, reach (STEP RmcM) s -> done RmcM s -> evok s -> ~ (rg (cs s 1) 3 = 0 /\ final s 0 = 2).
Proof.
  intros s R CP EV (A & B). assert (W : wf RmcM) by wf_tac.
  get_ent RmcM s R CP W 0 1 E01. get_ent RmcM s R CP W 1 1 E11. get_ent RmcM s R CP W 1 2 E12.
  get_ent RmcM s R CP W 1 3 E13. NZ7 RmcM 1.
  pose proof (read0 RmcM s R CP W 1 3 _ 1 E13 eq_refl eq_refl eq_refl H2 Ei2 A H3) as N0.
  destruct (n_final RmcM s R CP W 0 2 B ltac:(lia)) as (z & Iz & Vz & Last).
  pose proof (n_wr_of RmcM s R CP W 0 z Iz) as WO. which_writer WO. subst z.
  assert (Wm : ew E01 = true) by (rewrite (n_ew RmcM s R CP W 0 1 _ E01 eq_refl H Ei); reflexivity).
  destruct (n_wr RmcM s R CP W 0 1 _ 0 E01 eq_refl H Ei Wm (or_introl eq_refl)) as (I0m & _).
  destruct (n_wr RmcM s R CP W 0 1 _ 1 E01 eq_refl H Ei Wm (or_intror (or_introl eq_refl))) as (I1m & _).
  destruct (stw RmcM s R CP W 1 1 _ _ _ _ E11 eq_refl eq_refl H0 Ei0) as (_ & _ & S11).
  destruct (n_po RmcM s R CP W 1 1 2 _ _ E11 E12 ltac:(lia) eq_refl eq_refl eq_refl ltac:(tie) H0 H1) as [_ P].
  assert (Q : eQ E13 (bt s 1 1)).
  { apply (Q_guard RmcM s R CP W EV 1 2 3 E12 E13 ltac:(lia) eq_refl H1 H2 ltac:(nn)).
    - right. exists (ld 1). split; [exact Ei2|reflexivity].
    - apply P, S11. }
  apply (g3 RmcM s R CP W EV (bt s 0 1) (bt s 1 1) (bt s 1 3)).
  - apply (g_hist RmcM s R CP W EV 0). apply Last; [exact I0m|].
    apply (neq_bt RmcM s R CP W 0 1 1 1 _ _ eq_refl ltac:(nn) eq_refl eq_refl ltac:(nn) eq_refl). congruence.
  - apply (g_known RmcM s R CP W EV 1 3 E13); [exact H2|exact Q|].
    apply (neq_bt RmcM s R CP W 1 1 1 3 _ _ eq_refl ltac:(nn) eq_refl eq_refl ltac:(nn) eq_refl). congruence.
  - apply (g_missed RmcM s R CP W EV 1 3 (ld 1) 1 E13 (bt s 0 1) eq_refl eq_refl (or_introl eq_refl) H2 Ei2 I1m);
      [|left; exact N0].
    apply (neq_bt RmcM s R CP W 0 1 1 3 _ _ eq_refl ltac:(nn) eq_refl eq_refl ltac:(nn) eq_refl). congruence.
Qed.

(* ---------- Overlap: three ui8 stores over three ui4 cells, each pair
   sharing one; the finals cannot go round ---------- *)
Definition Ovl : prog := stat [ [ISt Plain [0; 1] T (K (enc [1; 1]))]; [ISt Plain [1; 2] T (K (enc [2; 2]))]; [ISt Plain [2; 0] T (K (enc [3; 3]))] ].

Theorem Ovl_forbidden : forall s, reach (STEP Ovl) s -> done Ovl s -> evok s -> ~ (final s 0 = 1 /\ final s 1 = 2 /\ final s 2 = 3).
Proof.
  intros s R CP EV (A & B & C). assert (W : wf Ovl) by wf_tac.
  get_ent Ovl s R CP W 0 0 E0. get_ent Ovl s R CP W 1 0 E1. get_ent Ovl s R CP W 2 0 E2.
  destruct (n_final Ovl s R CP W 0 1 A ltac:(lia)) as (z & Iz & Vz & L0).
  pose proof (n_wr_of Ovl s R CP W 0 z Iz) as WO. which_writer WO. subst z.
  destruct (n_final Ovl s R CP W 1 2 B ltac:(lia)) as (z & Iz1 & Vz1 & L1).
  pose proof (n_wr_of Ovl s R CP W 1 z Iz1) as WO. which_writer WO. subst z.
  destruct (n_final Ovl s R CP W 2 3 C ltac:(lia)) as (z & Iz2 & Vz2 & L2).
  pose proof (n_wr_of Ovl s R CP W 2 z Iz2) as WO. which_writer WO. subst z.
  assert (W0 : ew E0 = true) by (rewrite (n_ew Ovl s R CP W 0 0 _ E0 eq_refl H Ei); reflexivity).
  assert (W1 : ew E1 = true) by (rewrite (n_ew Ovl s R CP W 1 0 _ E1 eq_refl H0 Ei0); reflexivity).
  assert (W2 : ew E2 = true) by (rewrite (n_ew Ovl s R CP W 2 0 _ E2 eq_refl H1 Ei1); reflexivity).
  destruct (n_wr Ovl s R CP W 0 0 _ 1 E0 eq_refl H Ei W0 (or_intror (or_introl eq_refl))) as (I01 & _).
  destruct (n_wr Ovl s R CP W 1 0 _ 2 E1 eq_refl H0 Ei0 W1 (or_intror (or_introl eq_refl))) as (I12 & _).
  destruct (n_wr Ovl s R CP W 2 0 _ 0 E2 eq_refl H1 Ei1 W2 (or_intror (or_introl eq_refl))) as (I20 & _).
  apply (g3 Ovl s R CP W EV (bt s 0 0) (bt s 1 0) (bt s 2 0)).
  - apply (g_hist Ovl s R CP W EV 1). apply L1; [exact I01|].
    apply (neq_bt Ovl s R CP W 0 0 1 0 _ _ eq_refl ltac:(nn) eq_refl eq_refl ltac:(nn) eq_refl). congruence.
  - apply (g_hist Ovl s R CP W EV 2). apply L2; [exact I12|].
    apply (neq_bt Ovl s R CP W 1 0 2 0 _ _ eq_refl ltac:(nn) eq_refl eq_refl ltac:(nn) eq_refl). congruence.
  - apply (g_hist Ovl s R CP W EV 0). apply L0; [exact I20|].
    apply (neq_bt Ovl s R CP W 2 0 0 0 _ _ eq_refl ltac:(nn) eq_refl eq_refl ltac:(nn) eq_refl). congruence.
Qed.

(* the allowed instance P1p_torn exhibits a run of the model itself: see M2Parade *)

End Iface.
