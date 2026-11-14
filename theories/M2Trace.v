(* Model2: runs as traces of states, and what stays fixed from a state of a
   trace to a later one. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2Snap M2Oota M2Cont.

(* f 0 .. f n, each a step from the one before *)
Definition trace (p : prog) (f : nat -> st) (n : nat) : Prop :=
  f 0 = sinit /\ forall i, i < n -> step p (f i) (f (S i)).

Lemma trace_le : forall p f n m, trace p f n -> m <= n -> trace p f m.
Proof. intros p f n m [A B] L. split; auto. intros i Li. apply B. lia. Qed.

Lemma trace_run : forall p f n, trace p f n -> forall i, i <= n -> run p (f i).
Proof.
  intros p f n [A B] i L. induction i as [|i IH]; [rewrite A; constructor|].
  apply rS with (f i); [apply IH; lia|apply B; lia].
Qed.

Lemma run_trace : forall p s, run p s -> exists f n, trace p f n /\ f n = s.
Proof.
  intros p s R. induction R as [|s s' R IH St].
  - exists (fun _ => sinit), 0. split; [split; [auto|intros; lia]|auto].
  - destruct IH as (f & n & [A B] & E).
    exists (fun i => if Nat.leb i n then f i else s'), (S n). split; [split|].
    + simpl. auto.
    + intros i Li. destruct (Nat.leb_spec i n); [|lia].
      destruct (Nat.leb_spec (S i) n).
      * apply B. lia.
      * assert (i = n) by lia. subst i. rewrite E. auto.
    + destruct (Nat.leb_spec (S n) n); [lia|auto].
Qed.

(* ---------- what a later state keeps ---------- *)
Record Ext (s t : st) : Prop := {
  x_tm : tm s <= tm t;
  x_oc : forall c j y, oc (cs s c) j = Some y -> oc (cs t c) j = Some y;
  x_ocb : forall c j y, oc (cs t c) j = Some y -> y < tm s -> oc (cs s c) j = Some y;
  x_rg : forall c j, j < pcs s c \/ oc (cs s c) j <> None -> rg (cs t c) j = rg (cs s c) j;
  x_pcs : forall c, pcs s c <= pcs t c;
  x_ai : forall c j, j < pcs s c -> ai (cs t c) j = ai (cs s c) j;
  x_bd : forall c j, bd (cs s c) j = true -> bd (cs t c) j = true;
  x_ent : forall y e, ent s y = Some e -> ent t y = Some e;
  x_old : forall x a b, older (hs s x) a b -> older (hs t x) a b;
  x_ids : forall x a, In a (ids (hs s x)) -> In a (ids (hs t x));
  x_wv : forall y, y < tm s -> wv t y = wv s y;
  x_cm : forall q z, nth_error (cm s) q = Some z -> nth_error (cm t) q = Some z;
  x_tp : forall c, tp s c <= tp t c;
  x_rw : forall c j, oc (cs s c) j <> None -> rw (cs t c) j = rw (cs s c) j;
  x_es : forall y z, es s y = Some z -> es t y = Some z;
  x_aip : forall c j, oc (cs s c) j <> None -> pcs t c <= j -> ai (cs t c) j = ai (cs s c) j;
  x_oh : forall c j y, oh (cs s c) j = Some y -> oh (cs t c) j = Some y;
  x_cash : forall c j, oh (cs s c) j <> None -> pcs t c <= j -> casx (ai (cs t c) j) = casx (ai (cs s c) j);
  x_rgh : forall c j, oh (cs s c) j <> None -> pcs t c <= j ->
    rg (cs t c) j = rg (cs s c) j \/ (vok (rg (cs s c) j) = true /\ rg (cs t c) j = vd false (vv (rg (cs s c) j)));
  (* a passed slot that has not happened never will *)
  x_ocp : forall c j, j < pcs s c -> oc (cs s c) j = None -> oc (cs t c) j = None;
  (* what a CAS's read alone took stays in its register *)
  x_rgo : forall c j, oh (cs s c) j <> None -> vv (rg (cs t c) j) = vv (rg (cs s c) j);
  (* a passed slot whose CAS read never happened alone never will *)
  x_ohp : forall c j, j < pcs s c -> oh (cs s c) j = None -> oh (cs t c) j = None
}.

Lemma Ext_refl : forall s, Ext s s.
Proof. intros s. constructor; auto. Qed.

Lemma Ext_trans : forall a b c, Ext a b -> Ext b c -> Ext a c.
Proof.
  intros a b c [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22]
                [B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 B11 B12 B13 B14 B15 B16 B17 B18 B19 B20 B21 B22].
  constructor; auto.
  - lia.
  - intros c' j y H L. apply A3; auto. apply B3; auto. lia.
  - intros c' j N. rewrite B4; [auto|]. destruct N as [N|N]; [left; specialize (A5 c'); lia|right].
    destruct (oc (cs a c') j) eqn:E; [|congruence]. rewrite (A2 _ _ _ E). discriminate.
  - intros c'. specialize (A5 c'). specialize (B5 c'). lia.
  - intros c' j L. rewrite B6; [auto|]. specialize (A5 c'). lia.
  - intros y L. rewrite B11; [auto|lia].
  - intros c'. specialize (A13 c'). specialize (B13 c'). lia.
  - intros c' j N. rewrite B14; auto. destruct (oc (cs a c') j) eqn:E; [|congruence].
    rewrite (A2 _ _ _ E). discriminate.
  - intros c' j N L. assert (Nb : oc (cs b c') j <> None).
    { destruct (oc (cs a c') j) eqn:E; [|congruence]. rewrite (A2 _ _ _ E). discriminate. }
    rewrite (B16 c' j Nb L). apply A16; auto. specialize (B5 c'). lia.
  - intros c' j N L.
    assert (Nb : oh (cs b c') j <> None).
    { destruct (oh (cs a c') j) as [y|] eqn:E; [|congruence]. rewrite (A17 _ _ _ E). discriminate. }
    specialize (B5 c'). rewrite (B18 c' j Nb L). apply A18; auto. lia.
  - intros c' j N L.
    assert (Nb : oh (cs b c') j <> None).
    { destruct (oh (cs a c') j) as [y|] eqn:E; [|congruence]. rewrite (A17 _ _ _ E). discriminate. }
    specialize (B5 c'). destruct (B19 c' j Nb L) as [E1|(V1 & E1)]; destruct (A19 c' j N ltac:(lia)) as [E2|(V2 & E2)].
    + left. congruence.
    + right. rewrite E1. split; auto.
    + right. rewrite E2 in V1, E1. split; auto.
    + exfalso. rewrite E2, vok_vd in V1. discriminate.
  - intros c' j L O. apply B20; [specialize (A5 c'); lia|]. apply A20; auto.
  - intros c' j N. assert (Nb : oh (cs b c') j <> None).
    { destruct (oh (cs a c') j) as [y|] eqn:E; [|congruence]. rewrite (A17 _ _ _ E). discriminate. }
    rewrite (B21 c' j Nb). apply A21; auto.
  - intros c' j L O. apply B22; [specialize (A5 c'); lia|]. apply A22; auto.
Qed.

(* the time of a passed slot's event stays *)
Lemma x_tmo : forall s t c j y, Ext s t -> j < pcs s c -> tmo (cs s c) j = Some y -> tmo (cs t c) j = Some y.
Proof.
  intros s t c j y X L H. unfold tmo in *. destruct (oc (cs s c) j) as [y'|] eqn:O.
  - rewrite (x_oc _ _ X c j y' O). exact H.
  - rewrite (x_ocp _ _ X c j L O). apply (x_oh _ _ X). exact H.
Qed.

Lemma upd_eq' : forall {A} (f : nat -> A) k v, upd f k v k = v.
Proof. intros. unfold upd. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma upd_neq' : forall {A} (f : nat -> A) k k' v, k' <> k -> upd f k v k' = f k'.
Proof. intros. unfold upd. apply Nat.eqb_neq in H. rewrite H. reflexivity. Qed.

(* the history after an event step keeps the old order *)
Lemma eff_hist : forall t i r m m' a K u w, eff t i r m m' a K u w ->
  (forall x a0 b0, older (mH m x) a0 b0 -> older (mH m' x) a0 b0) /\
  (forall x a0, In a0 (ids (mH m x)) -> In a0 (ids (mH m' x))) /\
  (forall y, y <> t -> mV m' y = mV m y).
Proof.
  intros t i r m m' a K u w H. destruct w eqn:Ew; rewrite <- Ew in H.
  - destruct (eff_write t i r m m' a K u w H Ew) as (H' & R0 & _ & _ & E1 & Eo & Ei & E2 & _).
    rewrite E1, E2. split; [|split].
    + intros x' a0 b0 O. destruct (in_dec Nat.eq_dec x' (icells i)) as [I|N].
      * destruct (Ei x' I) as (h1 & h2 & F1 & F2). rewrite F2. rewrite F1 in O. apply older_ins. auto.
      * rewrite Eo; auto.
    + intros x' a0 I. destruct (in_dec Nat.eq_dec x' (icells i)) as [Ix|N].
      * destruct (Ei x' Ix) as (h1 & h2 & F1 & F2). rewrite F2. rewrite F1 in I. apply in_ids_ins. auto.
      * rewrite Eo; auto.
    + intros y N. rewrite upd_neq'; auto.
  - destruct (eff_nowrite t i r m m' a K u w H Ew) as (E1 & E2 & _). rewrite E1, E2. auto.
Qed.

Section St.
Variable p : prog.

Lemma Ext_step : forall s t, run p s -> step p s t -> Ext s t.
Proof.
  intros s t R St. pose proof (Inv1_run p s R) as I. pose proof (proj2 (Inv2_run p s R)) as J.
  destruct (step_cases p s t St) as [(c & i & m' & a & K & u & w & Hi & Ho & _ & _ & _ & Hhalf & HwO & HvO & He & _ & ->)|[(c & k & d & B & m' & a & K & u & w & Lk & Ho & _ & Hh & HwE & HvE & He & _ & ->)|[(c & d & Ho & Ha & Hd & _ & _ & _ & ->)|[(c & k & xs & B & m' & a & K & u & w & bv & Lk & Ho & Hoh & _ & _ & He & _ & ->)|[(c & K1 & K2 & K3 & _ & K5 & K4 & _ & ->)|(cX & jX & bX & BX & oX & HjX & HfX & HcX & ->)]]]]].
  - destruct (eff_hist _ _ _ _ _ _ _ _ _ He) as (H1 & H2 & H3). unfold sord.
    set (k := pcs s c) in *.
    constructor; unfold evs; simpl.
    + lia.
    + intros c' j y E. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; congruence|auto].
    + intros c' j y E L. unfold upd in E. destruct (Nat.eqb_spec c' c); [subst c'|auto].
      simpl in E. destruct (Nat.eqb_spec j k); [injection E as <-; lia|auto].
    + intros c' j N. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; destruct N as [N|N]; [try unfold k in N; lia|congruence]|auto].
    + intros c'. unfold upd. destruct (Nat.eqb_spec c' c); [subst; lia|lia].
    + intros c' j L. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; lia|auto].
    + intros c' j E. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl. auto.
    + intros y e E. unfold ent in *. simpl. rewrite nth_error_app1; auto. apply nth_error_Some. congruence.
    + intros x a0 b0 O. apply H1. auto.
    + intros x a0 In0. apply H2. auto.
    + intros y L. apply H3. lia.
    + intros q z E. rewrite nth_error_app1; auto. apply nth_error_Some. congruence.
    + intros c'. unfold upd. destruct (Nat.eqb_spec c' c); [subst; lia|lia].
    + intros c' j N. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; congruence|auto].
    + auto.
    + intros c' j N L. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; congruence|auto].
    + intros c' j y E. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl. auto.
    + intros c' j N L. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *.
      destruct (Nat.eqb_spec j k); [subst; lia|auto].
    + intros c' j N L; left. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *.
      destruct (Nat.eqb_spec j k); [subst; lia|auto].
    + intros c' j L O. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *.
      destruct (Nat.eqb_spec j k); [subst; lia|auto].
    + intros c' j N. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *.
      destruct (Nat.eqb_spec j k); [subst j|auto].
      destruct Hhalf as [(Z & _)|(t1 & Z & Ci & U & Ef)]; [congruence|].
      destruct (i_half p s I c k t1 Ho Z (le_n _)) as (_ & (xs & Ax) & _). rewrite Ax in Ef.
      destruct (eofR_half _ _ _ Ef) as (Ic & Xl).
      rewrite (proj2 (half_vals p s c k t1 I J Ho Z)). destruct (eff_read _ _ _ _ _ _ _ _ _ He Xl) as (_ & Ea).
      rewrite Ea, (areg_cas _ _ _ Ci), vv_vd, U, Ic, Ax. reflexivity.
    + intros c' j L O. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *. auto.
  - destruct (eff_hist _ _ _ _ _ _ _ _ _ He) as (H1 & H2 & H3). unfold searly, set_es, searly0.
    constructor; unfold evs; simpl.
    + lia.
    + intros c' j y E. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; congruence|auto].
    + intros c' j y E L. unfold upd in E. destruct (Nat.eqb_spec c' c); [subst c'|auto].
      simpl in E. destruct (Nat.eqb_spec j k); [injection E as <-; lia|auto].
    + intros c' j N. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; destruct N as [N|N]; [try unfold k in N; lia|congruence]|auto].
    + intros c'. lia.
    + intros c' j L. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; lia|auto].
    + intros c' j E. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl. unfold bor. rewrite E. auto.
    + intros y e E. unfold ent in *. simpl. rewrite nth_error_app1; auto. apply nth_error_Some. congruence.
    + intros x a0 b0 O. apply H1. auto.
    + intros x a0 In0. apply H2. auto.
    + intros y L. apply H3. lia.
    + auto.
    + intros c'. unfold upd. destruct (Nat.eqb_spec c' c); [subst; lia|lia].
    + intros c' j N. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; congruence|auto].
    + intros y z E. unfold upd. destruct (Nat.eqb_spec y (tm s)); [|auto].
      subst. exfalso. destruct (SI_run p s R) as (F & _). rewrite (F (tm s) (le_n _)) in E. discriminate.
    + intros c' j N L. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; congruence|auto].
    + intros c' j y E. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl. auto.
    + intros c' j N L. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *.
      destruct (Nat.eqb_spec j k); [subst|auto].
      destruct Hh as [(Z & _)|(t1 & xs & ev & nv & Z & -> & _ & Ac & _)]; [congruence|]. rewrite Ac. reflexivity.
    + intros c' j N L; left. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *.
      destruct (Nat.eqb_spec j k); [subst|auto].
      destruct Hh as [(Z & _)|(t1 & xs & ev & nv & Z & -> & U & Ac & _)]; [congruence|].
      assert (Vo : vok (rg (cs s c) k) = true) by (apply HvE; congruence).
      assert (Wt : w = true) by (apply HwE; congruence).
      rewrite <- (vd_split (rg (cs s c) k)), Vo, (proj2 (half_vals p s c k t1 I J Ho Z)).
      destruct (eff_read _ _ _ _ _ _ _ _ _ He eq_refl) as (_ & Ea).
      rewrite Ea. simpl areg. rewrite Wt, U, Ac. reflexivity.
    + intros c' j L O. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *.
      destruct (Nat.eqb_spec j k); [subst; lia|auto].
    + intros c' j N. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *.
      destruct (Nat.eqb_spec j k); [subst|auto].
      destruct Hh as [(Z & _)|(t1 & xs & ev & nv & Z & -> & U & Ac & _)]; [congruence|].
      rewrite (proj2 (half_vals p s c k t1 I J Ho Z)). destruct (eff_read _ _ _ _ _ _ _ _ _ He eq_refl) as (_ & Ea).
      rewrite Ea. simpl areg. rewrite vv_vd, U, Ac. reflexivity.
    + intros c' j L O. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *. auto.
  - unfold smatch. set (k := pcs s c) in *. constructor; simpl; auto.
    + intros c' j y E. unfold upd. destruct (Nat.eqb_spec c' c); [subst; auto|auto].
    + intros c' j y E L. unfold upd in E. destruct (Nat.eqb_spec c' c); [subst; auto|auto].
    + intros c' j N. unfold upd. destruct (Nat.eqb_spec c' c); [subst; auto|auto].
    + intros c'. unfold upd. destruct (Nat.eqb_spec c' c); [subst; lia|lia].
    + intros c' j L. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; lia|auto].
    + intros c' j E. unfold upd. destruct (Nat.eqb_spec c' c); [subst; auto|auto].
    + intros q z E. rewrite nth_error_app1; auto. apply nth_error_Some. congruence.
    + intros c' j N. unfold upd. destruct (Nat.eqb_spec c' c); [subst; auto|auto].
    + intros c' j N L. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; lia|auto].
    + intros c' j y E. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl. auto.
    + intros c' j N L. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *.
      destruct (Nat.eqb_spec j k); [subst; lia|auto].
    + intros c' j N L. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *. auto.
    + intros c' j L O. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *. auto.
    + intros c' j N. unfold upd. destruct (Nat.eqb_spec c' c); [subst; auto|auto].
    + intros c' j L O. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst; auto|auto].
  - destruct (eff_hist _ _ _ _ _ _ _ _ _ He) as (H1 & H2 & H3). unfold sread.
    constructor; simpl.
    + lia.
    + intros c' j y E. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl. auto.
    + intros c' j y E L. unfold upd in E. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in E. auto.
    + intros c' j N. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; destruct N as [N|N]; [try unfold k in N; lia|congruence]|auto].
    + intros c'. lia.
    + intros c' j L. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; lia|auto].
    + intros c' j E. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl. unfold bor. rewrite E. auto.
    + intros y e E. unfold ent in *. simpl. rewrite nth_error_app1; auto. apply nth_error_Some. congruence.
    + intros x a0 b0 O. apply H1. auto.
    + intros x a0 In0. apply H2. auto.
    + intros y L. apply H3. lia.
    + auto.
    + intros c'. unfold upd. destruct (Nat.eqb_spec c' c); [subst; lia|lia].
    + intros c' j N. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; congruence|auto].
    + intros y z E. unfold upd. destruct (Nat.eqb_spec y (tm s)); [|auto].
      subst. exfalso. destruct (SI_run p s R) as (F & _). rewrite (F (tm s) (le_n _)) in E. discriminate.
    + intros c' j N L. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; congruence|auto].
    + intros c' j y E. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; congruence|auto].
    + intros c' j N L. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *.
      destruct (Nat.eqb_spec j k); [subst; congruence|auto].
    + intros c' j N L; left. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *.
      destruct (Nat.eqb_spec j k); [subst; congruence|auto].
    + intros c' j L O. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *. auto.
    + intros c' j N. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *.
      destruct (Nat.eqb_spec j k); [subst; congruence|auto].
    + intros c' j L O. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *.
      destruct (Nat.eqb_spec j k); [subst; lia|auto].
  - unfold sskip. set (k := pcs s c) in *. constructor; simpl; auto.
    + intros c' j y E. unfold upd. destruct (Nat.eqb_spec c' c); [subst; auto|auto].
    + intros c' j y E L. unfold upd in E. destruct (Nat.eqb_spec c' c); [subst; auto|auto].
    + intros c' j N. unfold upd. destruct (Nat.eqb_spec c' c); [subst; auto|auto].
    + intros c'. unfold upd. destruct (Nat.eqb_spec c' c); [subst; lia|lia].
    + intros c' j L. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; lia|auto].
    + intros c' j E. unfold upd. destruct (Nat.eqb_spec c' c); [subst; auto|auto].
    + intros q z E. rewrite nth_error_app1; auto. apply nth_error_Some. congruence.
    + intros c'. unfold upd. destruct (Nat.eqb_spec c' c); [subst; lia|lia].
    + intros c' j N. unfold upd. destruct (Nat.eqb_spec c' c); [subst; auto|auto].
    + intros c' j N L. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl.
      destruct (Nat.eqb_spec j k); [subst; lia|auto].
    + intros c' j y E. unfold upd. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl. auto.
    + intros c' j N L. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *.
      destruct (Nat.eqb_spec j k); [subst; lia|auto].
    + intros c' j N L. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *. auto.
    + intros c' j L O. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst c'|auto]. simpl in *. auto.
    + intros c' j N. unfold upd. destruct (Nat.eqb_spec c' c); [subst; auto|auto].
    + intros c' j L O. unfold upd in *. destruct (Nat.eqb_spec c' c); [subst; auto|auto].
  - (* S3c: a result fixed; a failure after the read half changes only the record's bit *)
    apply (Ext_trans s (sflp s cX oX bX)).
    + destruct oX as [kX|]; [destruct bX|]; cbn [sflp]; try apply Ext_refl.
      destruct (cfix_rec _ _ _ _ _ _ _ _ _ HcX) as (HpF & HoF & HhF & HvF).
        unfold scfail. constructor; simpl; auto; intros; unfold upd in *;
          repeat match goal with |- context [Nat.eqb ?x cX] => destruct (Nat.eqb_spec x cX); [subst x|] end; simpl in *;
          repeat match goal with |- context [Nat.eqb ?x kX] => destruct (Nat.eqb_spec x kX); [subst x|] end; simpl in *;
          auto; try lia; try congruence.
        all: try (right; split; [exact HvF|reflexivity]).
        all: try (rewrite vv_vd; reflexivity).
        all: try (left; reflexivity).
        all: try (match goal with H : context [Nat.eqb ?x ?y] |- _ => destruct (Nat.eqb_spec x y); [subst x|]; simpl in H; exact H end).
        all: try (exfalso; match goal with H : _ \/ _ |- _ => destruct H; [lia|congruence] end).
    + generalize (sflp s cX oX bX); intros s0.
      constructor; intros; rewrite ?oc_cx, ?oh_cx, ?ai_cx, ?rw_cx, ?rg_cx in *; auto;
        try (change (pcs (scfix0 s0 cX jX bX BX)) with (pcs s0) in *; auto; fail);
        try (left; reflexivity).
      unfold scfix0; simpl; unfold upd. destruct (Nat.eqb_spec c cX); [subst c|auto]. simpl. unfold bor.
      match goal with H : bd _ _ = true |- _ => rewrite H; reflexivity end.
Qed.

End St.

Section Tr.
Variable p : prog.
Variable f : nat -> st.
Variable n : nat.
Hypothesis T : trace p f n.

Lemma tr_run : forall i, i <= n -> run p (f i).
Proof. intros i L. apply (trace_run p f n T i L). Qed.

Lemma tr_step : forall i, i < n -> step p (f i) (f (S i)).
Proof. intros i L. apply (proj2 T). auto. Qed.

Lemma tr_ext : forall i j, i <= j -> j <= n -> Ext (f i) (f j).
Proof.
  intros i j L Lj. induction j as [|j IH].
  - assert (i = 0) by lia. subst. apply Ext_refl.
  - destruct (Nat.eq_dec i (S j)) as [->|N]; [apply Ext_refl|].
    apply Ext_trans with (f j); [apply IH; lia|]. apply (Ext_step p); [apply tr_run; lia|apply tr_step; lia].
Qed.

Lemma tr_tm_lt : forall i j, i <= n -> j <= n -> tm (f i) < tm (f j) -> i < j.
Proof.
  intros i j Li Lj H. destruct (Nat.lt_ge_cases i j) as [X|X]; auto.
  pose proof (x_tm _ _ (tr_ext j i X Li)). lia.
Qed.

(* the step that recorded a pending access *)
Lemma early_birth : forall m c k t, m <= n -> pcs (f m) c <= k -> oc (cs (f m) c) k = Some t ->
  exists i d B m' a K u w, i < m /\ tm (f i) = t /\
    pcs (f i) c < k /\ oc (cs (f i) c) k = None /\
    (forall k' d', pending (cs (f i) c) (pcs (f i) c) k' d' -> tied (inst_of d) (inst_of d') -> k' < k) /\
    ((oh (cs (f i) c) k = None /\ early_ok p c (cs (f i) c) (pcs (f i) c) (tp (f i) c) (tm (f i)) d u B) \/
     (exists t1 xs ev nv, oh (cs (f i) c) k = Some t1 /\ d = DCas Plain xs ev nv /\ u = rw (cs (f i) c) k /\
        ai (cs (f i) c) k = crd Plain xs /\
        early_okW p c (cs (f i) c) (pcs (f i) c) (tp (f i) c) (tm (f i)) t1 Plain xs d B)) /\
    (oh (cs (f i) c) k <> None -> w = true) /\ (oh (cs (f i) c) k <> None -> vok (rg (cs (f i) c) k) = true) /\
    eff (tm (f i)) (inst_of d) (rg (cs (f i) c)) (mof (f i) c) m' a K u w /\
    f (S i) = searly (f i) c k d B m' a K u w.
Proof.
  induction m as [|m IH]; intros c k t Lm P O.
  - rewrite (proj1 T) in O. simpl in O. discriminate.
  - destruct (oc (cs (f m) c) k) as [t'|] eqn:Om.
    + pose proof (x_oc _ _ (tr_ext m (S m) ltac:(lia) Lm) c k t' Om) as X. rewrite O in X. injection X as <-.
      pose proof (x_pcs _ _ (tr_ext m (S m) ltac:(lia) Lm) c) as Pc.
      destruct (IH c k t ltac:(lia) ltac:(lia) Om) as (i & d & B & m' & a & K & u & w & A).
      exists i, d, B, m', a, K, u, w. split; [lia|apply A].
    + pose proof (tr_step m ltac:(lia)) as St.
      destruct (step_cases p _ _ St) as [(c0 & i0 & m0 & a0 & K0 & u0 & w0 & Hi & Ho & _ & _ & _ & _ & _ & _ & He & _ & E)|[(c0 & k0 & d0 & B0 & m0 & a0 & K0 & u0 & w0 & Lk & Ho & Hso & Hk & HwE & HvE & He & _ & E)|[(c0 & d0 & Ho & _ & _ & _ & _ & _ & E)|[(c0 & k0 & xs0 & B0 & m0 & a0 & K0 & u0 & w0 & bv0 & Lk & Ho & _ & _ & _ & He & _ & E)|[(c0 & K1 & K2 & K3 & _ & K5 & K4 & _ & E)|(cX & jX & bX & BX & oX & HjX & HfX & HcX & E)]]]]].
      * exfalso. rewrite E in O, P. unfold sord, evs in O, P. simpl in O, P. unfold upd in O, P.
        destruct (Nat.eqb_spec c c0); [subst c0|congruence]. simpl in O.
        destruct (Nat.eqb_spec k (pcs (f m) c)) as [X|X]; [lia|congruence].
      * rewrite E in O. unfold searly, set_es, searly0, evs in O. simpl in O. unfold upd in O.
        destruct (Nat.eqb_spec c c0); [subst c0|congruence]. simpl in O.
        destruct (Nat.eqb_spec k k0); [subst k0|congruence]. injection O as <-.
        exists m, d0, B0, m0, a0, K0, u0, w0. repeat split; auto.
      * exfalso. rewrite E in O. unfold smatch in O. simpl in O. unfold upd in O.
        destruct (Nat.eqb_spec c c0); [subst c0|congruence]. simpl in O. congruence.
      * exfalso. rewrite E in O. unfold sread in O. simpl in O. unfold upd in O.
        destruct (Nat.eqb_spec c c0); [subst c0|congruence]. simpl in O. congruence.
      * exfalso. rewrite E in O. rewrite (oc_skip p (f m) c0) in O. congruence.
      * exfalso. rewrite E in O. rewrite oc_cx, oc_flp in O. congruence.
Qed.

(* the step that recorded a CAS's read alone *)
Lemma half_birth : forall m c k t, m <= n -> oh (cs (f m) c) k = Some t ->
  exists i xs B m' a K u w bv, i < m /\ tm (f i) = t /\
    pcs (f i) c <= k /\ oc (cs (f i) c) k = None /\ oh (cs (f i) c) k = None /\
    (forall k' d', pending (cs (f i) c) (pcs (f i) c) k' d' -> tied (crd Plain xs) (inst_of d') -> k' < k) /\
    early_okR p c (cs (f i) c) (pcs (f i) c) (tp (f i) c) (tm (f i)) Plain xs u B /\
    eff (tm (f i)) (ILd Plain xs (fun _ => true)) (rg (cs (f i) c)) (mof (f i) c) m' a K u w /\
    f (S i) = sread (f i) c k Plain xs B m' a K u w bv.
Proof.
  induction m as [|m IH]; intros c k t Lm O.
  - rewrite (proj1 T) in O. simpl in O. discriminate.
  - destruct (oh (cs (f m) c) k) as [t'|] eqn:Om.
    + pose proof (x_oh _ _ (tr_ext m (S m) ltac:(lia) Lm) c k t' Om) as X. rewrite O in X. injection X as <-.
      destruct (IH c k t ltac:(lia) Om) as (i & xs & B & m' & a & K & u & w & bv & A).
      exists i, xs, B, m', a, K, u, w, bv. split; [lia|apply A].
    + pose proof (tr_step m ltac:(lia)) as St.
      destruct (step_cases p _ _ St) as [(c0 & i0 & m0 & a0 & K0 & u0 & w0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E)|[(c0 & k0 & d0 & B0 & m0 & a0 & K0 & u0 & w0 & _ & _ & _ & _ & _ & _ & _ & _ & E)|[(c0 & d0 & _ & _ & _ & _ & _ & _ & E)|[(c0 & k0 & xs0 & B0 & m0 & a0 & K0 & u0 & w0 & bv0 & Lk & Ho & Hoh & Hso & Hok & He & _ & E)|[(c0 & K1 & K2 & K3 & _ & K5 & K4 & _ & E)|(cX & jX & bX & BX & oX & HjX & HfX & HcX & E)]]]]].
      * exfalso. rewrite E in O. unfold sord in O. rewrite oh_s' in O. congruence.
      * exfalso. rewrite E in O. unfold searly, set_es, searly0, evs in O. simpl in O. unfold upd in O.
        destruct (Nat.eqb_spec c c0); [subst; simpl in O; congruence|congruence].
      * exfalso. rewrite E in O. rewrite oh_match in O. congruence.
      * rewrite E in O. unfold sread in O. simpl in O. unfold upd in O.
        destruct (Nat.eqb_spec c c0); [subst c0|congruence]. simpl in O.
        destruct (Nat.eqb_spec k k0); [subst k0|congruence]. injection O as <-.
        exists m, xs0, B0, m0, a0, K0, u0, w0, bv0. repeat split; auto.
      * exfalso. rewrite E in O. rewrite (oh_skip p (f m) c0) in O. congruence.
      * exfalso. rewrite E in O. rewrite oh_cx, oh_flp in O. congruence.
Qed.

(* the step that passed a slot *)
Lemma pass_birth : forall m c k, m <= n -> k < pcs (f m) c ->
  exists i, i < m /\ pcs (f i) c = k /\ pcs (f (S i)) c = S k /\
    ((exists i0 m' a K u w, let cc := cs (f i) c in
       ins p c k (rg cc) = i0 /\ oc cc k = None /\ determined p cc c k i0 /\
       (executes i0 (rg cc) = true -> forall k' d, pending cc k k' d -> ~ tied i0 (inst_of d)) /\
       (executes i0 (rg cc) = true -> forall k' m xs, hpending cc k k' m xs -> k' <> k -> ~ tied i0 (crd m xs)) /\
       ((oh cc k = None /\
         forall x b, bd cc k = true -> In x (icells i0) -> fbinder p c (rg cc) k x = Some b -> u x = rw cc b x) \/
        (exists t1, oh cc k = Some t1 /\ is_cas i0 = true /\ u = rw cc k /\ eofR i0 (rg cc) = eofR (ai cc k) (rg cc))) /\
       (oh cc k <> None -> vok (rg cc k) = true) /\
       eff (tm (f i)) i0 (rg cc) (mof (f i) c) m' a K u w /\ f (S i) = sord (f i) c i0 m' a K u w) \/
     (exists d, let cc := cs (f i) c in
       oc cc k <> None /\ ai cc k = inst_of d /\ eof (ins p c k (rg cc)) (rg cc) = Some d /\
       determined p cc c k (ins p c k (rg cc)) /\
       (forall k' d' t t', pending cc k k' d' -> k' <> k -> oc cc k = Some t -> oc cc k' = Some t' ->
          tied (inst_of d) (inst_of d') -> t < t') /\
       (forall k' m xs t t', hpending cc k k' m xs -> k' <> k -> oc cc k = Some t -> oh cc k' = Some t' ->
          tied (inst_of d) (crd m xs) -> t < t') /\ f (S i) = smatch p (f i) c) \/
     (let cc := cs (f i) c in
       xex cc (ins p c k (rg cc)) (rg cc) k = false /\ oc cc k = None /\
       (oh cc k <> None -> eofR (ins p c k (rg cc)) (rg cc) = eofR (ai cc k) (rg cc)) /\
       (oh cc k <> None -> vok (rg cc k) = false) /\
       hfirst cc k (ins p c k (rg cc)) /\
       determined p cc c k (ins p c k (rg cc)) /\ f (S i) = sskip p (f i) c)).
Proof.
  induction m as [|m IH]; intros c k Lm P.
  - rewrite (proj1 T) in P. simpl in P. lia.
  - destruct (Nat.lt_ge_cases k (pcs (f m) c)) as [Q|Q].
    + destruct (IH c k ltac:(lia) Q) as (i & A). exists i. split; [lia|apply A].
    + pose proof (tr_step m ltac:(lia)) as St. exists m. split; [lia|].
      destruct (step_cases p _ _ St) as [(c0 & i0 & m0 & a0 & K0 & u0 & w0 & Hi & Ho & Hd & Hb & Hbh & Hbd & _ & HvO & He & _ & E)|[(c0 & k0 & d0 & B0 & m0 & a0 & K0 & u0 & w0 & Lk & Ho & Hso & Hk & _ & _ & He & _ & E)|[(c0 & d0 & Ho & Ha & Hdf & Hd & Hfm & Hfh & E)|[(c0 & k0 & xs0 & B0 & m0 & a0 & K0 & u0 & w0 & bv0 & Lk & Ho & _ & _ & _ & He & _ & E)|[(c0 & K1 & K2 & K3 & K6 & K5 & K4 & _ & E)|(cX & jX & bX & BX & oX & HjX & HfX & HcX & E)]]]]].
      * assert (Pc : pcs (f (S m)) c = upd (pcs (f m)) c0 (S (pcs (f m) c0)) c) by (rewrite E; reflexivity).
        rewrite Pc in P |- *. unfold upd in P |- *.
        destruct (Nat.eqb_spec c c0); [subst c0|lia].
        assert (k = pcs (f m) c) by lia. subst k. split; auto. split; auto.
        left. exists i0, m0, a0, K0, u0, w0. cbv zeta. exact (conj Hi (conj Ho (conj Hd (conj Hb (conj Hbh (conj Hbd (conj HvO (conj He E)))))))).
      * exfalso. rewrite E in P. unfold searly, set_es, searly0, evs in P. simpl in P. lia.
      * assert (Pc : pcs (f (S m)) c = upd (pcs (f m)) c0 (S (pcs (f m) c0)) c) by (rewrite E; reflexivity).
        rewrite Pc in P |- *. unfold upd in P |- *.
        destruct (Nat.eqb_spec c c0); [subst c0|lia].
        assert (k = pcs (f m) c) by lia. subst k. split; auto. split; auto.
        right; left. exists d0. cbv zeta. exact (conj Ho (conj Ha (conj Hdf (conj Hd (conj Hfm (conj Hfh E)))))).
      * exfalso. rewrite E in P. unfold sread in P. simpl in P. lia.
      * assert (Pc : pcs (f (S m)) c = upd (pcs (f m)) c0 (S (pcs (f m) c0)) c) by (rewrite E; reflexivity).
        rewrite Pc in P |- *. unfold upd in P |- *.
        destruct (Nat.eqb_spec c c0); [subst c0|lia].
        assert (k = pcs (f m) c) by lia. subst k. split; auto. split; auto.
        right; right. cbv zeta. exact (conj K1 (conj K2 (conj K3 (conj K6 (conj K5 (conj K4 E)))))).
      * exfalso. assert (Pc : pcs (f (S m)) c = pcs (f m) c) by (rewrite E; unfold scfix0; cbn [pcs]; rewrite pcs_flp; reflexivity). lia.
Qed.

(* a CAS whose read happened alone and which committed to failure never
   writes, and keeps its verdict *)
Lemma half_fail_stays : forall m m' c k t, m <= m' -> m' <= n -> oh (cs (f m) c) k = Some t ->
  oc (cs (f m) c) k = None -> pcs (f m) c <= k -> vok (rg (cs (f m) c) k) = false ->
  oc (cs (f m') c) k = None.
Proof.
  intros m m' c k t L1 L2 Oh Oc Pk Vk.
  assert (Ea : forall m1, m <= m1 -> m1 <= n -> pcs (f m1) c <= k -> oc (cs (f m1) c) k = None).
  { intros m1 La Lb Pm. destruct (oc (cs (f m1) c) k) as [y|] eqn:Oy; [|reflexivity]. exfalso.
    destruct (early_birth m1 c k y Lb Pm Oy) as (i & d & B & m2 & a & K & u & w & Li & Ti & Pi & Oi & _ & _ & _ & Vi & _ & E).
    destruct (Nat.lt_ge_cases i m) as [Lim|Lim].
    - assert (O1 : oc (cs (f (S i)) c) k = Some (tm (f i))).
      { rewrite E. unfold searly, set_es, searly0, evs; simpl. rewrite !upd_eq'. simpl. rewrite !upd_eq'. reflexivity. }
      rewrite (x_oc _ _ (tr_ext (S i) m ltac:(lia) ltac:(lia)) c k _ O1) in Oc. discriminate.
    - assert (Xi : Ext (f m) (f i)) by (apply tr_ext; lia).
      pose proof (x_oh _ _ Xi c k t Oh) as Ohi.
      destruct (x_rgh _ _ Xi c k ltac:(congruence) ltac:(lia)) as [R|(R & _)]; [|congruence].
      rewrite R, Vk in Vi. specialize (Vi ltac:(congruence)). discriminate. }
  destruct (Nat.le_gt_cases (pcs (f m') c) k) as [Pm|Pm]; [apply Ea; lia|].
  destruct (pass_birth m' c k L2 Pm) as (q & Lq & Pq & PSq & Cs).
  assert (Lmq : m <= q).
  { destruct (Nat.le_gt_cases m q) as [X|X]; auto. exfalso.
    pose proof (x_pcs _ _ (tr_ext (S q) m ltac:(lia) ltac:(lia)) c). lia. }
  assert (Xq : Ext (f m) (f q)) by (apply tr_ext; lia).
  assert (Oq : oc (cs (f q) c) k = None) by (apply Ea; lia).
  destruct Cs as [(i0 & m1 & a & K & u & w & _ & _ & _ & _ & _ & _ & Hv & _ & E)|[(d & Ho & _)|(_ & _ & _ & _ & _ & _ & E)]].
  - exfalso. cbv zeta in Hv. pose proof (x_oh _ _ Xq c k t Oh) as Ohq.
    destruct (x_rgh _ _ Xq c k ltac:(congruence) ltac:(lia)) as [R|(R & _)]; [|congruence].
    rewrite R, Vk in Hv. specialize (Hv ltac:(congruence)). discriminate.
  - exfalso. cbv zeta in Ho. congruence.
  - assert (O1 : oc (cs (f (S q)) c) k = None) by (rewrite E; rewrite (oc_skip p (f q) c); exact Oq).
    apply (x_ocp _ _ (tr_ext (S q) m' ltac:(lia) L2) c k ltac:(lia) O1).
Qed.

Lemma half_fail_vok : forall m m' c k t, m <= m' -> m' <= n -> oh (cs (f m) c) k = Some t ->
  oc (cs (f m) c) k = None -> pcs (f m) c <= k -> vok (rg (cs (f m) c) k) = false ->
  vok (rg (cs (f m') c) k) = false.
Proof.
  intros m m' c k t L1 L2 Oh Oc Pk Vk.
  assert (Xm : Ext (f m) (f m')) by (apply tr_ext; lia).
  destruct (Nat.le_gt_cases (pcs (f m') c) k) as [Pm|Pm].
  - destruct (x_rgh _ _ Xm c k ltac:(congruence) Pm) as [R|(R & _)]; [rewrite R; exact Vk|congruence].
  - apply (i_halfv p (f m') (Inv1_run p (f m') (tr_run m' L2)) c k t); [|apply (x_oh _ _ Xm c k t Oh)|exact Pm].
    apply (half_fail_stays m m' c k t L1 L2 Oh Oc Pk Vk).
Qed.

(* a pending access stays pending with its effect, or is passed by the
   programme's instruction, which does the same *)
Lemma pend_fate : forall i m c j d, i <= m -> m <= n -> wf p ->
  oc (cs (f i) c) j <> None -> pcs (f i) c <= j -> ai (cs (f i) c) j = inst_of d ->
  (pcs (f m) c <= j /\ ai (cs (f m) c) j = inst_of d) \/
  (j < pcs (f m) c /\ eof (ins p c j (rg (cs (f m) c))) (rg (cs (f m) c)) = Some d).
Proof.
  intros i m c j d Lim Lm W O P A. induction m as [|m IH].
  - assert (i = 0) by lia. subst. left. auto.
  - destruct (Nat.eq_dec i (S m)) as [->|Ni]; [left; auto|].
    assert (Rm : run p (f m)) by (apply tr_run; lia).
    pose proof (Inv1_run p (f m) Rm) as I.
    pose proof (Ext_step p (f m) (f (S m)) Rm (tr_step m ltac:(lia))) as X.
    assert (Om : oc (cs (f m) c) j <> None).
    { destruct (oc (cs (f i) c) j) eqn:E; [|congruence].
      rewrite (x_oc _ _ (tr_ext i m ltac:(lia) ltac:(lia)) c j n0 E). discriminate. }
    destruct (IH ltac:(lia) ltac:(lia)) as [(Q1 & Q2)|(Q1 & Q2)].
    + destruct (step_cases p _ _ (tr_step m ltac:(lia))) as [(c0 & i0 & m0 & a0 & K0 & u0 & w0 & Hi & Ho & _ & _ & _ & _ & _ & _ & He & _ & E)|[(c0 & k0 & d0 & B0 & m0 & a0 & K0 & u0 & w0 & Lk & Ho & _ & _ & _ & _ & He & _ & E)|[(c0 & d0 & Ho & Ha & Hdf & Hd & _ & _ & E)|[(c0 & k0 & xs0 & B0 & m0 & a0 & K0 & u0 & w0 & bv0 & Lk & Ho & _ & _ & _ & He & _ & E)|[(c0 & K1 & K2 & K3 & _ & K5 & K4 & _ & E)|(cX & jX & bX & BX & oX & HjX & HfX & HcX & E)]]]]].
      * left. split.
        -- assert (Pc : pcs (f (S m)) c = upd (pcs (f m)) c0 (S (pcs (f m) c0)) c) by (rewrite E; reflexivity).
           rewrite Pc. unfold upd. destruct (Nat.eqb_spec c c0); [subst c0|lia].
           destruct (Nat.eq_dec j (pcs (f m) c)) as [->|Nj]; [congruence|lia].
        -- rewrite (x_aip _ _ X c j Om); auto.
           assert (Pc : pcs (f (S m)) c = upd (pcs (f m)) c0 (S (pcs (f m) c0)) c) by (rewrite E; reflexivity).
           rewrite Pc. unfold upd. destruct (Nat.eqb_spec c c0); [subst c0|lia].
           destruct (Nat.eq_dec j (pcs (f m) c)) as [->|Nj]; [congruence|lia].
      * left. assert (Pc : pcs (f (S m)) c = pcs (f m) c) by (rewrite E; reflexivity).
        split; [lia|]. rewrite (x_aip _ _ X c j Om); [auto|lia].
      * assert (Pc : pcs (f (S m)) c = upd (pcs (f m)) c0 (S (pcs (f m) c0)) c) by (rewrite E; reflexivity).
        destruct (Nat.eq_dec c c0) as [<-|Nc].
        -- destruct (Nat.eq_dec j (pcs (f m) c)) as [->|Nj].
           ++ right. rewrite Pc, upd_eq'. split; [lia|].
              assert (Rg : rg (cs (f (S m)) c) = rg (cs (f m) c)) by (rewrite E; unfold smatch; simpl; rewrite upd_eq'; reflexivity).
              rewrite Rg. rewrite Q2 in Ha. apply inst_of_inj in Ha. subst d0. exact Hdf.
           ++ left. rewrite Pc, upd_eq'. split; [lia|]. rewrite (x_aip _ _ X c j Om); [auto|]. rewrite Pc, upd_eq'. lia.
        -- left. rewrite Pc. unfold upd. destruct (Nat.eqb_spec c c0); [congruence|].
           split; [auto|]. rewrite (x_aip _ _ X c j Om); [auto|]. rewrite Pc. unfold upd.
           destruct (Nat.eqb_spec c c0); [congruence|auto].
      * left. assert (Pc : pcs (f (S m)) c = pcs (f m) c) by (rewrite E; reflexivity).
        split; [lia|]. rewrite (x_aip _ _ X c j Om); [auto|lia].
      * left. assert (Pc : pcs (f (S m)) c = upd (pcs (f m)) c0 (S (pcs (f m) c0)) c) by (rewrite E; reflexivity).
        assert (Nj : c <> c0 \/ j <> pcs (f m) c0).
        { destruct (Nat.eq_dec c c0) as [<-|Nc]; [right; intros Z; rewrite Z in Om; congruence|left; exact Nc]. }
        split.
        -- rewrite Pc. unfold upd. destruct (Nat.eqb_spec c c0); [subst c0|lia]. destruct Nj as [Nj|Nj]; [congruence|lia].
        -- rewrite (x_aip _ _ X c j Om); [auto|]. rewrite Pc. unfold upd. destruct (Nat.eqb_spec c c0); [subst c0|lia].
           destruct Nj as [Nj|Nj]; [congruence|lia].
      * left. assert (Pc : pcs (f (S m)) c = pcs (f m) c) by (rewrite E; unfold scfix0; cbn [pcs]; rewrite pcs_flp; reflexivity).
        split; [lia|]. rewrite (x_aip _ _ X c j Om); [auto|lia].
    + right. split; [pose proof (x_pcs _ _ X c); lia|].
      assert (Ag : forall j', j' < j -> rg (cs (f (S m)) c) j' = rg (cs (f m) c) j').
      { intros j' L. apply (x_rg _ _ X). left. lia. }
      destruct (W c j (rg (cs (f (S m)) c)) (rg (cs (f m) c)) Ag) as [E1 E2].
      rewrite E1 in E2 |- *. rewrite (eof_ieval _ _ _ E2). exact Q2.
Qed.

End Tr.
