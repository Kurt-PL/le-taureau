(* Model2, one event: tools for forbidding outcomes of finished runs that
   have no access before itself. *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO M2Comp M2Lit M2Neg M2Ev.

Set Default Proof Using "All".
Section Q.
Variable p : prog.
Variable s : M2Model.st.
Hypothesis R : run p s.
Hypothesis CP : done p s.
Hypothesis W : wf p.
Hypothesis EV : evok s.

Local Abbreviation bt := (bt s).
Local Abbreviation rrg := (rrg s).
Lemma qIO : InvO p s. Proof. apply (iaoO p s (InvO_run p s R)). Qed.

(* ---------- cycles ---------- *)
Lemma g2 : forall a b, gedge s a b -> gedge s b a -> False.
Proof. intros a b A B. apply (proj1 EV a). econstructor 2; constructor; eauto. Qed.
Lemma g3 : forall a b c, gedge s a b -> gedge s b c -> gedge s c a -> False.
Proof. intros a b c A B C. apply (proj1 EV a). econstructor 2; [constructor; eauto|econstructor 2; constructor; eauto]. Qed.
Lemma g4 : forall a b c d, gedge s a b -> gedge s b c -> gedge s c d -> gedge s d a -> False.
Proof.
  intros a b c d A B C D. apply (proj1 EV a).
  econstructor 2; [constructor; eauto|econstructor 2; [constructor; eauto|econstructor 2; constructor; eauto]].
Qed.
Lemma c2 : forall x a b, cedge s x a b -> cedge s x b a -> False.
Proof. intros x a b A B. apply (proj2 EV x a). econstructor 2; constructor; eauto. Qed.
Lemma c3 : forall x a b c, cedge s x a b -> cedge s x b c -> cedge s x c a -> False.
Proof. intros x a b c A B C. apply (proj2 EV x a). econstructor 2; [constructor; eauto|econstructor 2; constructor; eauto]. Qed.

(* ---------- what an entry records ---------- *)
Lemma eR_of : forall c k i E, ins p c k (rrg c) = i -> RE s c k E -> einstr p s E = i ->
  eR E = if xload i (rrg c) then icells i else [].
Proof.
  intros c k i E H (A & B & C) Ei. destruct (o_eRC p s qIO _ E A) as [ER _]. rewrite ER.
  unfold evR, rgof. rewrite Ei, B. reflexivity.
Qed.

Lemma eC_of : forall c k i E, ins p c k (rrg c) = i -> RE s c k E -> einstr p s E = i ->
  eC E = if isacc i && icond i (rrg c) then icells i else [].
Proof.
  intros c k i E H (A & B & C) Ei. destruct (o_eRC p s qIO _ E A) as [_ EC]. rewrite EC.
  unfold evC, rgof. rewrite Ei, B. reflexivity.
Qed.

Lemma ownw_other : forall c w Ew, ent s w = Some Ew -> ec Ew <> c -> ~ ownw s c w.
Proof. intros c w Ew H N (e & E & C & _). unfold ent in H. rewrite E in H. injection H as <-. auto. Qed.

(* ---------- what an access knows in order ---------- *)
Lemma Q_guard : forall c kf ke Ef Ee, kf < ke -> ins p c kf (rrg c) = IFn FFull ->
  RE s c kf Ef -> RE s c ke Ee -> ins p c ke (rrg c) <> INop -> xacc p s Ee -> vsub (eP Ef) (eQ Ee).
Proof.
  intros c kf ke Ef Ee L Hf REf REe N X.
  pose proof (n_tieE p s R CP W c kf ke _ _ Ee L Hf eq_refl eq_refl ltac:(right; left; reflexivity) REe) as T.
  pose proof REf as (A1 & B1 & C1). pose proof REe as (A2 & B2 & C2).
  assert (G : xg p s Ef).
  { exists (IFn FFull). split; [|reflexivity]. rewrite (einstr_ins p s R CP W _ Ef A1), B1, C1. exact Hf. }
  apply (o_gpair p s qIO _ Ef _ Ee A1 A2 ltac:(congruence) T G X).
Qed.

Lemma Q_ll : forall c kl kf ke El Ef Ee, kl < kf -> kf < ke -> ins p c kf (rrg c) = IFn FLl ->
  RE s c kl El -> RE s c kf Ef -> RE s c ke Ee -> xl p s El -> xl p s Ee ->
  ins p c ke (rrg c) <> INop -> forall w, carr s (erf El) w -> ~ ownw s c w -> eQc Ee w.
Proof.
  intros c kl kf ke El Ef Ee L1 L2 Hf REl REf REe X Y N w Cw Nw.
  pose proof REl as (A1 & B1 & C1). pose proof REf as (A2 & B2 & C2). pose proof REe as (A3 & B3 & C3).
  assert (Il : ins p c kl (rrg c) <> INop).
  { intros Z. destruct X as (i0 & Ei & Xl). rewrite (einstr_ins p s R CP W _ El A1), B1, C1, Z in Ei. subst i0.
    discriminate. }
  assert (Xl' : is_load (ins p c kl (rrg c)) && icond (ins p c kl (rrg c)) (rrg c) = true).
  { destruct X as (i0 & Ei & Xl). rewrite (einstr_ins p s R CP W _ El A1), B1, C1 in Ei. subst i0.
    unfold rgof in Xl. rewrite B1 in Xl. exact Xl. }
  assert (T1 : bt c kl < bt c kf).
  { apply andb_prop in Xl'. destruct Xl' as [Ld Cd].
    apply (n_tie p s R CP W c kl kf _ _ L1 eq_refl Hf); [|reflexivity| |discriminate].
    - unfold executes. destruct (ins p c kl (rrg c)); simpl in Ld; try discriminate; exact Cd.
    - apply tied_ld_l; [exact Ld|left; reflexivity]. }
  assert (Lde : is_load (ins p c ke (rrg c)) = true).
  { destruct Y as (i0 & Ei & Xl). rewrite (einstr_ins p s R CP W _ Ee A3), B3, C3 in Ei. subst i0.
    unfold xload in Xl. apply andb_prop in Xl. tauto. }
  assert (T2 : bt c kf < bt c ke) by (apply (n_tieE p s R CP W c kf ke _ _ Ee L2 Hf eq_refl eq_refl ltac:(apply tied_l_ld; [left; reflexivity|exact Lde]) REe)).
  assert (Ya : xll p s Ef) by (unfold xll; rewrite (einstr_ins p s R CP W _ Ef A2), B2, C2; exact Hf).
  apply (o_apair p s qIO _ El _ Ef _ Ee A1 A2 A3 ltac:(congruence) ltac:(congruence) T1 T2 X Ya Y w Cw).
  rewrite B1. exact Nw.
Qed.

(* ---------- a read cannot miss what it knows in order; a write cannot enter
   before what it knows in order ---------- *)
Lemma read_known : forall c k i x E w, ins p c k (rrg c) = i -> xload i (rrg c) = true -> In x (icells i) ->
  RE s c k E -> einstr p s E = i -> eQ E w -> In w (ids (hs s x)) -> w <> bt c k ->
  (erf E x = None \/ exists u, erf E x = Some u /\ older (hs s x) u w) -> False.
Proof.
  intros c k i x E w H X Ix RE0 Ei Q Iw N M.
  pose proof RE0 as (A & B & C).
  apply (g2 (bt c k) w).
  - right; left. exists E, x. split; [exact A|]. split; [rewrite (eR_of c k i E H RE0 Ei), X; exact Ix|].
    split; [exact Iw|]. split; [auto|]. destruct M as [M|(u & M1 & M2)]; rewrite ?M, ?M1; auto.
  - right; right. exists E. split; [exact A|]. auto.
Qed.

Lemma write_known : forall c k E x w, RE s c k E -> eQ E w -> older (hs s x) (bt c k) w -> False.
Proof.
  intros c k E x w (A & B & C) Q O.
  apply (g2 (bt c k) w).
  - left. exists x. exact O.
  - right; right. exists E. split; [exact A|]. split; [exact Q|].
    intros Z. subst w. apply (older_irrefl _ _ (n_nodup p s R CP W x) O).
Qed.

(* ---------- one cell: an access after its context's earlier accesses there ---------- *)
Lemma c_po : forall c j k ij ik Ej Ek x, j < k -> ins p c j (rrg c) = ij -> ins p c k (rrg c) = ik ->
  RE s c j Ej -> RE s c k Ek -> einstr p s Ej = ij -> einstr p s Ek = ik ->
  isacc ij && icond ij (rrg c) = true -> isacc ik && icond ik (rrg c) = true ->
  In x (icells ij) -> In x (icells ik) -> cedge s x (bt c j) (bt c k).
Proof.
  intros c j k ij ik Ej Ek x L Hj Hk REj REk Eij Eik Aj Ak Ij Ik.
  right; right; right; right. pose proof REj as (A1 & B1 & C1). pose proof REk as (A2 & B2 & C2).
  exists Ej, Ek. split; [exact A1|]. split; [exact A2|]. split; [congruence|]. split; [lia|].
  rewrite (eC_of c j ij Ej Hj REj Eij), Aj, (eC_of c k ik Ek Hk REk Eik), Ak. auto.
Qed.

Lemma c_took : forall c k i x E u, ins p c k (rrg c) = i -> xload i (rrg c) = true -> In x (icells i) ->
  RE s c k E -> einstr p s E = i -> erf E x = Some u -> u <> bt c k -> cedge s x u (bt c k).
Proof.
  intros c k i x E u H X Ix RE0 Ei Eu N. pose proof RE0 as (A & B & C).
  right; right; left. exists E. split; [exact A|]. split; [rewrite (eR_of c k i E H RE0 Ei), X; exact Ix|]. auto.
Qed.

Lemma c_missed : forall c k i x E w, ins p c k (rrg c) = i -> xload i (rrg c) = true -> In x (icells i) ->
  RE s c k E -> einstr p s E = i -> In w (ids (hs s x)) -> w <> bt c k ->
  (erf E x = None \/ exists u, erf E x = Some u /\ older (hs s x) u w) -> cedge s x (bt c k) w.
Proof.
  intros c k i x E w H X Ix RE0 Ei Iw N M. pose proof RE0 as (A & B & C).
  right; left. exists E. split; [exact A|]. split; [rewrite (eR_of c k i E H RE0 Ei), X; exact Ix|].
  split; [exact Iw|]. split; [auto|]. destruct M as [M|(u & M1 & M2)]; rewrite ?M, ?M1; auto.
Qed.

Lemma c_hist : forall x a b, older (hs s x) a b -> cedge s x a b.
Proof. intros. left. auto. Qed.

(* the same within one cell, for what an access knows in order there
   (guard.rl() included) *)
Lemma read_knownc : forall c k i x E w, ins p c k (rrg c) = i -> xload i (rrg c) = true -> In x (icells i) ->
  RE s c k E -> einstr p s E = i -> eQc E w -> In w (ids (hs s x)) -> w <> bt c k ->
  (erf E x = None \/ exists u, erf E x = Some u /\ older (hs s x) u w) -> False.
Proof.
  intros c k i x E w H X Ix RE0 Ei Q Iw N M.
  pose proof RE0 as (A & B & C).
  assert (Ac : isacc i && icond i (rrg c) = true).
  { unfold xload in X. apply andb_prop in X as [L Cd]. rewrite Cd, andb_true_r.
    destruct i; simpl in L; try discriminate; reflexivity. }
  apply (c2 x (bt c k) w).
  - apply (c_missed c k i x E w H X Ix RE0 Ei Iw N M).
  - right; right; right; left. exists E. split; [exact A|].
    split; [rewrite (eC_of c k i E H RE0 Ei), Ac; exact Ix|]. split; [right; exact Q|]. auto.
Qed.

Lemma write_knownc : forall c k E x w, RE s c k E -> In x (eC E) -> eQc E w -> older (hs s x) (bt c k) w -> False.
Proof.
  intros c k E x w (A & B & C) Cx Q O.
  apply (c2 x (bt c k) w).
  - left. exact O.
  - right; right; right; left. exists E. split; [exact A|]. split; [exact Cx|]. split; [right; exact Q|].
    split; [apply (older_in _ _ _ O)|].
    intros Z. subst w. apply (older_irrefl _ _ (n_nodup p s R CP W x) O).
Qed.

(* ---------- the same edges with no cell named ---------- *)
Lemma g_hist : forall x a b, older (hs s x) a b -> gedge s a b.
Proof. intros x a b O. left. exists x. exact O. Qed.

Lemma g_known : forall c k E w, RE s c k E -> eQ E w -> w <> bt c k -> gedge s w (bt c k).
Proof. intros c k E w (A & B & C) Q N. right; right. exists E. split; [exact A|]. auto. Qed.

Lemma g_missed : forall c k i x E w, ins p c k (rrg c) = i -> xload i (rrg c) = true -> In x (icells i) ->
  RE s c k E -> einstr p s E = i -> In w (ids (hs s x)) -> w <> bt c k ->
  (erf E x = None \/ exists u, erf E x = Some u /\ older (hs s x) u w) -> gedge s (bt c k) w.
Proof.
  intros c k i x E w H X Ix RE0 Ei Iw N M. pose proof RE0 as (A & B & C).
  right; left. exists E, x. split; [exact A|]. split; [rewrite (eR_of c k i E H RE0 Ei), X; exact Ix|].
  split; [exact Iw|]. split; [auto|]. destruct M as [M|(u & M1 & M2)]; rewrite ?M, ?M1; auto.
Qed.

End Q.
