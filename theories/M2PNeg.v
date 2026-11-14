(* Model2: facts about any run, stated per passed instruction. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2PComp M2Lit.

Set Default Proof Using "All".
Section N.
Variable p : prog.
Variable s : M2Model.st.
Hypothesis R : run p s.
Hypothesis W : wf p.

Local Abbreviation bt := (bt s).
Local Abbreviation rrg := (rrg s).
Lemma nI1 : Inv1 p s. Proof. apply (I1 p s R W). Qed.
Lemma nI2 : Inv2 p s. Proof. apply (I2 p s R W). Qed.
Lemma nI3 : Inv3 p s. Proof. apply (I3 p s R W). Qed.

Definition RE (c k : nat) (E : oev) : Prop := ent s (bt c k) = Some E /\ ec E = c /\ ek E = k.

Lemma n_insr : forall c k i, ins p c k (rrg c) = i -> k < pcs s c -> insr p s c k = Some i.
Proof. intros c k i H N. rewrite (insr_of p s R W) by auto. congruence. Qed.

Lemma n_ent : forall c k i, ins p c k (rrg c) = i -> k < pcs s c -> executes i (rrg c) = true ->
  exists E, RE c k E /\ einstr p s E = i.
Proof.
  intros c k i H N X. destruct (ent_of p s R W c k i (n_insr c k i H N) X) as (E & A & B & C & D).
  exists E. repeat split; auto.
Qed.

Lemma RE_insr : forall c k E, RE c k E -> k < pcs s c -> insr p s c k = Some (ins p c k (rrg c)).
Proof. intros c k E _ L. apply (insr_of p s R W). auto. Qed.

(* the entry at a passed slot's time is the slot's access, not a CAS's read alone *)


(* a passed slot with an entry at its time happened then *)
Lemma RE_tmo : forall c k E, RE c k E -> k < pcs s c -> tmo (cs s c) k = Some (bt c k).
Proof.
  intros c k E (A & B & C) L. unfold M2PComp.bt in *. destruct (tmo (cs s c) k) as [t|] eqn:T; [reflexivity|]. exfalso.
  destruct (i_et p s nI1 _ E A) as (_ & X). rewrite B, C in X. unfold tmo in T.
  destruct (oc (cs s c) k) eqn:O; [discriminate|]. destruct (eh E); congruence.
Qed.

(* an entry at a slot's time that is a CAS's read alone: the CAS failed *)
Lemma RE_ehc : forall c k E, RE c k E -> k < pcs s c -> eh E = true -> cfail (ins p c k (rrg c)) (rrg c) k = true.
Proof.
  intros c k E RE0 L Eh. pose proof (RE_tmo c k E RE0 L) as Tm. destruct RE0 as (A & B & C).
  destruct (i_et p s nI1 _ E A) as (_ & X). rewrite Eh, B, C in X.
  destruct (oc (cs s c) k) as [t2|] eqn:O2.
  - exfalso. assert (O3 : oc (cs s c) k = Some (bt c k)) by (unfold tmo in Tm; rewrite O2 in Tm |- *; exact Tm).
    rewrite (oc_eh p s c k _ E nI1 O3 A B C) in Eh. discriminate.
  - destruct (i_halfp p s nI1 c k _ O2 X L) as (F & _). destruct (cm_set p s c k nI1 L) as (tau & T0).
    rewrite (proj2 (i_set p s nI1 c k tau T0)) in F. exact F.
Qed.

Lemma n_rgof : forall c k E, RE c k E -> rgof s E = rrg c.
Proof. intros c k E (_ & B & _). unfold rgof. rewrite B. reflexivity. Qed.

Lemma n_et : forall c k E, RE c k E -> et E = bt c k.
Proof. intros c k E (A & _). apply (i_et p s nI1 _ _ A). Qed.

Lemma n_rd : forall c k i x E, ins p c k (rrg c) = i -> xload i (rrg c) = true -> In x (icells i) ->
  RE c k E -> einstr p s E = i ->
  rval i (rg (cs s c) k) = enc (rdvs s (icells i) (erf E)) /\
  (forall y, erf E x = Some y -> In y (ids (hs s x)) /\ y < bt c k).
Proof.
  intros c k i x E H X Ic RE0 Ei. pose proof RE0 as (A & B & C).
  destruct (j_val p s nI2 _ E i A Ei) as [V _]. rewrite B, C in V. split; [apply V; rewrite (n_rgof c k E RE0) in *; auto|].
  intros y Ey. destruct (j_rf p s nI2 _ E x y A Ey) as (L & _ & _ & Hy). auto.
Qed.

(* the writer of a write id of a cell: a passed instruction or a pending early access *)
Lemma n_wr_of : forall x y, In y (ids (hs s x)) ->
  exists c k i E, einstr p s E = i /\ RE c k E /\ ew E = true /\ In x (icells i) /\
    wv s y x = cval (icells i) (wvals i (rrg c)) x /\ bt c k = y /\ (k < pcs s c -> ins p c k (rrg c) = i).
Proof.
  intros x y H. destruct (j_hist p s nI2 x y H) as (E & i & A & Wy & Ei & Ic).
  destruct (i_et p s nI1 y E A) as (_ & O).
  assert (Eh : eh E = false) by (destruct (j_ew p s nI2 y E i A Ei) as [W1 _]; rewrite Wy in W1; destruct (eh E); [discriminate|reflexivity]).
  rewrite Eh in O.
  assert (Bt : bt (ec E) (ek E) = y) by (unfold M2PComp.bt, tmo; rewrite O; auto).
  destruct (j_ew p s nI2 y E i A Ei) as [_ W2]. destruct (W2 Wy) as [V _].
  exists (ec E), (ek E), i, E. split; [auto|]. split; [unfold RE; rewrite Bt; auto|].
  split; [auto|]. split; [auto|]. split; [rewrite V; unfold rgof; reflexivity|]. split; [auto|].
  intros L. rewrite <- Ei. symmetry. apply (einstr_ins p s R W y E A L).
Qed.

Lemma n_wr : forall c k i x E, ins p c k (rrg c) = i -> RE c k E -> einstr p s E = i -> ew E = true ->
  In x (icells i) -> In (bt c k) (ids (hs s x)) /\ esrc E (bt c k) /\
  wv s (bt c k) x = cval (icells i) (wvals i (rrg c)) x.
Proof.
  intros c k i x E H RE0 Ei Wt Ic. pose proof RE0 as (A & B & C).
  destruct (j_ew p s nI2 _ E i A Ei) as [_ W2]. destruct (W2 Wt) as [V Hh].
  split; [apply Hh; auto|]. split.
  - rewrite <- (n_et c k E RE0). unfold esrc, srcv. rewrite Wt. right. reflexivity.
  - rewrite V. rewrite (n_rgof c k E RE0). auto.
Qed.

Lemma n_ew : forall c k i E, ins p c k (rrg c) = i -> RE c k E -> einstr p s E = i -> k < pcs s c ->
  ew E = (is_store i && icond i (rrg c) && (negb (is_cas i) || vok (rg (cs s c) k))).
Proof.
  intros c k i E H RE0 Ei L. pose proof RE0 as (A & B & C).
  destruct (j_ew p s nI2 _ E i A Ei) as [W1 _]. rewrite (n_rgof c k E RE0) in W1.
  destruct (eh E) eqn:Eh.
  - cbn [negb andb] in W1. rewrite W1. pose proof (RE_ehc c k E RE0 L Eh) as F. rewrite H in F.
    pose proof (RE_tmo c k E RE0 L) as Tm.
    destruct (i_et p s nI1 _ E A) as (_ & X). rewrite Eh, B, C in X.
    destruct (oc (cs s c) k) as [t2|] eqn:O2.
    { exfalso. assert (O3 : oc (cs s c) k = Some (bt c k)) by (unfold tmo in Tm; rewrite O2 in Tm |- *; exact Tm).
      rewrite (oc_eh p s c k _ E nI1 O3 A B C) in Eh. discriminate. }
    pose proof (i_halfv p s nI1 c k _ O2 X L) as VK. unfold M2PComp.rrg in *.
    destruct i as [| |md x cn ee n| |]; simpl in F; try discriminate. apply andb_true_iff in F as [CN _].
    unfold icond, ieval; simpl. rewrite CN, VK. reflexivity.
  - cbn [negb andb] in W1. destruct (is_cas i) eqn:Ca.
    + pose proof (j_ok p s nI2 _ E A Eh) as OK. unfold rgof in OK. rewrite Ei, B, C in OK.
      unfold M2PComp.rrg in *. destruct (icond i (rg (cs s c))) eqn:Ic.
      * rewrite (OK Ca) by (unfold xload; rewrite Ic; destruct i; simpl in Ca; try discriminate; reflexivity).
        rewrite andb_true_r. destruct i; simpl in Ca; try discriminate. reflexivity.
      * rewrite W1. rewrite !andb_false_r. reflexivity.
    + rewrite W1. reflexivity.
Qed.

Lemma n_po : forall c j k ij ik Ej Ek, j < k -> ins p c j (rrg c) = ij -> ins p c k (rrg c) = ik ->
  executes ij (rrg c) = true -> tied ij ik -> k < pcs s c ->
  RE c j Ej -> RE c k Ek -> vsub (eP Ej) (eP Ek) /\ vsub (esrc Ej) (eP Ek).
Proof.
  intros c j k ij ik Ej Ek L Hj Hk Ex T Lk RE1 RE2.
  pose proof (RE_tmo c j Ej RE1 ltac:(lia)) as Oj. pose proof (RE_tmo c k Ek RE2 Lk) as Ok.
  destruct RE1 as (A1 & B1 & C1). destruct RE2 as (A2 & B2 & C2).
  apply (k_Ppair p s nI3 _ Ej _ Ek A1 A2 ltac:(congruence)).
  rewrite <- Hj in Ex, T. rewrite <- Hk in T.
  destruct (i_pot p s nI1 c j k (bt c k) L Lk Ok Ex T) as (tj & X1 & X2). rewrite Oj in X1. injection X1 as <-. exact X2.
Qed.

Lemma n_xg : forall c k i E, RE c k E -> einstr p s E = i -> xgop i (rrg c) = true -> xg p s E.
Proof. intros c k i E RE0 Ei X. exists i. split; auto. Qed.

Lemma n_G : forall c1 k1 c2 k2 E1 E2, RE c1 k1 E1 -> RE c2 k2 E2 -> xg p s E1 -> xg p s E2 ->
  bt c1 k1 < bt c2 k2 -> vsub (eP E1) (eP E2) /\ vsub (esrc E1) (eP E2).
Proof. intros c1 k1 c2 k2 E1 E2 (A1 & _) (A2 & _) X1 X2 L. apply (k_Gpair p s nI3 _ E1 _ E2 A1 A2 X1 X2 L). Qed.

Lemma n_rel : forall c e f w Ee Ef Ew, RE c e Ee -> RE c f Ef -> RE c w Ew ->
  bt c e <= bt c f -> bt c f <= bt c w -> bt c e < bt c w -> (xss p s Ef \/ xg p s Ef) -> ew Ew = true ->
  (forall tg g, ent s tg = Some g -> ec g = c -> bt c f < tg -> tg < bt c w -> ~ xss p s g) ->
  forall v, (eP Ee v \/ esrc Ee v) -> (xg p s Ef \/ ownw s c v) -> wc s (bt c w) v.
Proof.
  intros c e f w Ee Ef Ew (A1 & B1 & _) (A2 & B2 & _) (A3 & B3 & _) L1 L2 L3 X Wt NR v Hv Ov.
  apply (k_Rpair p s nI3 _ Ee _ Ef _ Ew A1 A2 A3 ltac:(congruence) ltac:(congruence) L1 L2 L3 X Wt); auto.
  - intros tg g Hg Eg. apply (NR tg g Hg). congruence.
  - rewrite B2. exact Ov.
Qed.

Lemma n_acq : forall c l f e El Ef Ee, RE c l El -> RE c f Ef -> RE c e Ee ->
  bt c l < bt c f -> xl p s El -> ((xll p s Ef /\ bt c f < bt c e) \/ (xg p s Ef /\ bt c f <= bt c e)) ->
  vsub (carr s (erf El)) (eP Ee).
Proof.
  intros c l f e El Ef Ee (A1 & B1 & _) (A2 & B2 & _) (A3 & B3 & _) L X Y.
  apply (k_Apair p s nI3 _ El _ Ef _ Ee A1 A2 A3 ltac:(congruence) ltac:(congruence) L X Y).
Qed.

Lemma n_aself : forall c l e El Ee, RE c l El -> RE c e Ee -> bt c l < bt c e -> xl p s El -> xg p s El ->
  vsub (carr s (erf El)) (eP Ee).
Proof.
  intros c l e El Ee (A1 & B1 & _) (A2 & B2 & _) L X G.
  apply (k_Aself p s nI3 _ El _ Ee A1 A2 ltac:(congruence) L X G).
Qed.

Lemma n_tie : forall c j k ij ik, j < k -> ins p c j (rrg c) = ij -> ins p c k (rrg c) = ik ->
  executes ij (rrg c) = true -> executes ik (rrg c) = true -> tied ij ik -> k < pcs s c -> bt c j < bt c k.
Proof.
  intros c j k ij ik L Hj Hk Ex Ek T N.
  pose proof (insr_of p s R W c j ltac:(lia)) as I1'. rewrite Hj in I1'.
  apply (tie_bt p s R W c j k ij ik L I1' (n_insr c k ik Hk N) Ex Ek T).
Qed.

(* the same, the later slot given by its entry *)
Lemma n_tieE : forall c j k ij ik Ek, j < k -> ins p c j (rrg c) = ij -> ins p c k (rrg c) = ik ->
  executes ij (rrg c) = true -> tied ij ik -> k < pcs s c -> RE c k Ek -> bt c j < bt c k.
Proof.
  intros c j k ij ik Ek L Hj Hk Ex T Lk RE2. pose proof (RE_tmo c k Ek RE2 Lk) as Ok.
  rewrite <- Hj in Ex, T. rewrite <- Hk in T.
  destruct (i_pot p s nI1 c j k (bt c k) L Lk Ok Ex T) as (tj & X1 & X2).
  unfold M2PComp.bt at 1. rewrite X1. exact X2.
Qed.

Lemma n_final : forall x v, final s x = v -> v <> 0 ->
  exists y, In y (ids (hs s x)) /\ wv s y x = v /\ forall z, In z (ids (hs s x)) -> z <> y -> older (hs s x) z y.
Proof.
  intros x v F N. unfold final in F. destruct (rev (hs s x)) as [|[y gf] r] eqn:E; [congruence|].
  assert (Eh : hs s x = rev r ++ [(y, gf)]) by (rewrite <- (rev_involutive (hs s x)), E; reflexivity).
  exists y. split; [rewrite Eh, ids_app, in_app_iff; right; left; reflexivity|]. split; auto.
  intros z Hz Nz. rewrite Eh in Hz |- *. rewrite ids_app, in_app_iff in Hz. destruct Hz as [Hz|[Hz|[]]];
    [|simpl in Hz; congruence].
  exists (rev r), [(y, gf)]. split; auto. split; auto. left; auto.
Qed.

Lemma n_nodup : forall x, NoDup (ids (hs s x)). Proof. apply (j_nodup p s nI2). Qed.

End N.

(* ---------- tactics ---------- *)
Ltac nn := let Z := fresh in intro Z; vm_compute in Z; discriminate.

Ltac get_ent p s R W c k E :=
  let Ei := fresh "Ei" in
  destruct (n_ent p s R W c k (ins p c k (rrg s c)) eq_refl ltac:(lia) ltac:(vm_compute; reflexivity)) as (E & ? & Ei);
  vm_compute in Ei.

(* a write id of a given cell is one of the program's stores to that cell *)
Ltac which_writer H :=
  let c := fresh "c" in let k := fresh "k" in let i := fresh "i" in let E := fresh "E" in
  let Hi := fresh "Hi" in let RE0 := fresh "RE" in let Wt := fresh "Wt" in let Ic := fresh "Ic" in
  let V := fresh "V" in let B := fresh "B" in
  destruct H as (c & k & i & E & Hi & RE0 & Wt & Ic & V & B);
  destruct c as [|[|[|[|[|c]]]]]; destruct k as [|[|[|[|[|[|[|k]]]]]]];
  vm_compute in Hi; subst i; vm_compute in Ic;
  repeat match type of Ic with _ \/ _ => destruct Ic as [Ic|Ic] | False => destruct Ic end;
  try discriminate;
  try (exfalso; simpl in V; unfold K in V; lia).
