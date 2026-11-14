(* M2PCore.v re-checked on M2DQ (stepQ) through M2DQShim; scripts as in M2PCore.v except where marked DQ. *)
(* Model2: the core of DRF-SC. A base is an interleaving of the slots that
   a state of a run has passed, faithful to the run. On top of it, contexts
   run alone in SC, each segment within the registers R1 considered for an
   early access (CONS). Then:
   - bind_race: a read R1 counted on that does not take its binder's value
     in SC is a race;
   - fwd: a context runs forward in SC to the place of one of its pending
     accesses, or a race appears;
   - core: a pending read placed in SC that does not take its value is a
     race (by induction on its birth time). *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
From Stdlib Require Import Relations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO M2Oota M2Cont M2DQEquiv M2Snap M2SC M2SCx M2SlotOrder M2Trace M2DQMono M2DQPComp M2DQPNeg M2DQPSync M2DQPFix M2DA M2DP M2DQ M2DQInv M2DQIface M2DQTrace M2DQTr M2DQShim.

Definition RACY (p : prog) : Prop := exists l g, srun p l g /\ racy_g p l.

Lemma sg_ffull_ev : forall p l g q e, wf p -> srun p l g -> nth_error l q = Some e -> sg e = true ->
  ins p (sx e) (sk e) (sr g (sx e)) = IFn FFull.
Proof.
  intros p l g q e W R Q S. destruct (srun_ev p W l g R q e Q) as (i & Hi & _ & Sh). rewrite Hi.
  destruct i as [md x c|md x c v|md x c e0 n|fk|]; simpl in Sh;
    try (destruct (c (sr g (sx e))); injection Sh; intros; congruence).
  - destruct fk; injection Sh; intros; congruence.
  - injection Sh; intros; congruence.
Qed.

Lemma acc_ev : forall p l g q e xs w, wf p -> srun p l g -> nth_error l q = Some e -> sacc e = Some (xs, w) ->
  icells (ins p (sx e) (sk e) (sr g (sx e))) = xs /\
  executes (ins p (sx e) (sk e) (sr g (sx e))) (sr g (sx e)) = true.
Proof.
  intros p l g q e xs w W R Q A. destruct (srun_ev p W l g R q e Q) as (i & Hi & _ & Sh). rewrite Hi.
  rewrite A in Sh. unfold executes, icond.
  destruct i as [md y c|md y c u|md y c e0 n|fk|]; simpl in Sh |- *;
    try (destruct (c (sr g (sx e))) eqn:C; injection Sh; intros; subst; auto; discriminate);
    try (destruct fk; discriminate); discriminate.
Qed.

(* a fence accesses no cell *)
Lemma cells_accd : forall x d, In x (icells (inst_of d)) -> isaccd d = true.
Proof. intros x [| | |f] H; auto. Qed.

Ltac acc_tac := first [ apply load_accd; assumption | apply store_accd; assumption
  | eapply cells_accd; eassumption | reflexivity ].

Lemma meet_in : forall x xs ys, In x xs -> In x ys -> meetb xs ys = true.
Proof. intros x xs ys A B. apply meetb_spec. eauto. Qed.

(* ---------- a read counted on that misses its binder's value ---------- *)
Section Bind.
Variable p : prog.
Hypothesis W : wf p.
Variable bs : sst -> nat -> bool.

Lemma classic_write : forall l x qb, (exists q e, nth_error l q = Some e /\ qb < q /\ writes_x e x = true) \/
  (forall q e, qb < q -> nth_error l q = Some e -> writes_x e x = false).
Proof.
  intros l x qb. destruct (lw l x) as [w|] eqn:Lw.
  - destruct (lw_spec l x w Lw) as (qw & Qw & Ww & After).
    destruct (Nat.lt_ge_cases qb qw) as [L|L]; [left; exists qw, w; auto|right].
    intros q e Lq Q. apply (After q e); [lia|exact Q].
  - right. intros q e _ Q. apply (lw_none l x Lw q e Q).
Qed.

Lemma forallb_false : forall {A} (f : A -> bool) l, forallb f l = false -> exists x, In x l /\ f x = false.
Proof.
  intros A f l. induction l as [|a l IH]; intros H; simpl in H; [discriminate|].
  destruct (f a) eqn:Fa; simpl in H; [destruct (IH H) as (x & I & F); exists x; split; [right|]; auto|exists a; split; [left|]; auto].
Qed.

Lemma meetb_tiedb : forall a b, meetb (icells a) (icells b) = true -> tiedb a b = true.
Proof. intros a b M. unfold tiedb. rewrite M. reflexivity. Qed.

Lemma bind_race : forall l g c x b, srun p l g ->
  bread (ins p c (sp g c) (sr g c)) = true -> icond (ins p c (sp g c) (sr g c)) (sr g c) = true ->
  In x (icells (ins p c (sp g c) (sr g c))) -> fbinder p c (sr g c) (sp g c) x = Some b ->
  sm g x <> bvx p c (sr g c) b x (dec p c (sr g c) b x) -> RACY p.
Proof.
  intros l g c x b R Br Cr Ix Fb Ne. set (j := sp g c) in *. set (r := sr g c) in *.
  destruct (fbinder_spec p c r j x b Fb) as (_ & _ & _ & Fd).
  destruct (fbind_spec p c r _ _ _ _ Fd) as (Lb & Exb & Tb & Nb).
  destruct (fbinder_shape _ _ _ _ _ _ Fb) as (_ & Ixb & _).
  destruct (proj1 (srun_pos p W l g R c b) Lb) as (qb & eb & Qb & Xb & Kb).
  (* the read's step *)
  set (eR := fst (snext p bs g c)). set (gR := snd (snext p bs g c)).
  assert (StR : sstep p g eR gR) by apply snext_step.
  assert (XR : sx eR = c) by apply snext_x.
  assert (AR : exists w2, sacc eR = Some (icells (ins p c j r), w2) /\ sk eR = j /\ sg eR = false).
  { unfold eR, snext. fold j r.
    destruct (ins p c j r) as [[] xs cj|m xs cj v|[] xs cj e n| |]; simpl in Br; try discriminate;
      unfold icond, ieval in Cr; simpl in Cr; rewrite Cr; simpl; eauto. }
  destruct AR as (w2 & AR & KR & GR).
  assert (RR : srun p (l ++ [eR]) gR) by (econstructor; eauto).
  assert (QR : nth_error (l ++ [eR]) (length l) = Some eR) by apply nth_app_last'.
  (* the slots between the binder and the read do not come or are not tied *)
  assert (Mid : forall q e, nth_error l q = Some e -> sx e = c -> qb < q ->
             executes (ins p c (sk e) r) r && tiedb (ins p c (sk e) r) (ins p c j r) = false).
  { intros q e Q X L. apply Nb.
    - rewrite <- Kb. apply (srun_order p W l g R qb q eb e L Qb Q). congruence.
    - destruct (srun_ev p W l g R q e Q) as (_ & _ & Lt & _). rewrite X in Lt. exact Lt. }
  assert (Lsp : qb < length l) by (apply nth_error_Some; congruence).
  (* a write to x after the binder races with the read *)
  destruct (classic_write l x qb) as [(qw & w & Qw & Lq & Ww)|Nw].
  - assert (Aw : exists ys, sacc w = Some (ys, true) /\ In x ys).
    { unfold writes_x in Ww. destruct (sacc w) as [[ys []]|]; try discriminate.
      exists ys. split; auto. apply existsb_exists in Ww. destruct Ww as (z & Z & Q). apply Nat.eqb_eq in Q. subst. auto. }
    destruct Aw as (ys & Aw & Ixw).
    assert (Nx : sx w <> c).
    { intros Xw. pose proof (Mid qw w Qw Xw Lq) as M.
      destruct (acc_ev p l g qw w ys true W R Qw Aw) as [Ic Ex]. rewrite Xw in Ic, Ex. fold r in Ic, Ex.
      rewrite Ex, meetb_tiedb in M; [discriminate|]. rewrite Ic. apply (meet_in x); auto. }
    exists (l ++ [eR]), gR. split; [auto|].
    apply (racy_g_mk p (l ++ [eR]) qw (length l) w eR x ys (icells (ins p c j r)) true w2).
    + apply nth_error_Some. congruence.
    + rewrite nth_app_old'; auto. apply nth_error_Some. congruence.
    + auto.
    + congruence.
    + auto.
    + auto.
    + exact Ixw.
    + exact Ix.
    + reflexivity.
    + intros (a & b' & f1 & f2 & L1 & L2 & L3 & F1 & F2 & S1 & S2 & X1 & X2).
      rewrite XR in X2. destruct (Nat.eq_dec b' (length l)) as [->|Nb'].
      { rewrite QR in F2. injection F2 as <-. congruence. }
      assert (Lb' : b' < length l) by lia. rewrite nth_app_old' in F2 by auto.
      assert (Ff : ins p c (sk f2) r = IFn FFull).
      { pose proof (sg_ffull_ev p l g b' f2 W R F2 S2) as Q. rewrite X2 in Q. exact Q. }
      pose proof (Mid b' f2 F2 X2 ltac:(lia)) as M. rewrite Ff in M. simpl in M. discriminate.
    + intros (_ & Fa). rewrite XR, KR in Fa. destruct Fa as (_ & Fa). destruct (Fa r) as [Fj _].
      destruct (Nat.eq_dec (j - 1) b) as [Ej|Nj].
      * rewrite Ej in Fj. rewrite Fj in Ixb. destruct Ixb.
      * pose proof (Nb (j - 1) ltac:(lia) ltac:(lia)) as M. rewrite Fj in M. simpl in M. discriminate.
  - (* no write to x after the binder: the read takes the binder's value *)
    exfalso. apply Ne.
    pose proof R as R'. rewrite <- (firstn_skipn (S qb) l) in R'.
    destruct (srun_split p _ _ _ R') as (g2 & R2 & S2).
    assert (E2 : firstn (S qb) l = firstn qb l ++ [eb]) by (rewrite (firstn_S_nth l qb eb Qb); reflexivity).
    rewrite E2 in R2. inversion R2 as [Z|l1 g1 e1 g2' R1 St1 Z]; [destruct (firstn qb l); discriminate|].
    apply app_inj_tail in Z as [Z1 Z2]. subst l1 e1 g2'.
    assert (Nw' : forall e, In e (skipn (S qb) l) -> writes_x e x = false).
    { intros e I. apply In_nth_error in I. destruct I as (q' & Q').
      rewrite nth_error_skipn in Q'. apply (Nw (S qb + q') e); [lia|exact Q']. }
    rewrite (sruns_nowrite p W _ _ _ x S2 Nw').
    assert (Sb : sp g1 c = b).
    { destruct (sstep_shape p W _ _ _ St1) as (i & _ & _ & Hk & _). rewrite Xb in Hk. congruence. }
    assert (Lb2 : b < sp g2 c).
    { destruct (sstep_shape p W _ _ _ St1) as (i & _ & _ & _ & Hsp & _). rewrite Hsp, Xb. unfold upd. rewrite Nat.eqb_refl. lia. }
    assert (Rb : forall j', j' < b -> sr g c j' = sr g1 c j').
    { intros j' L. rewrite (sruns_regs p W _ _ _ S2 c j') by lia.
      destruct (sstep_shape p W _ _ _ St1) as (i & _ & _ & _ & _ & Hr & _). apply Hr. right. lia. }
    assert (Rbb : r b = sr g2 c b) by (unfold r; apply (sruns_regs p W _ _ _ S2 c b Lb2)).
    assert (Ib : ins p c b (sr g1 c) = ins p c b r) by (apply (wf_ins p c b); auto; intros; symmetry; apply Rb; auto).
    assert (Evb : ieval (ins p c b r) (sr g1 c) = ieval (ins p c b r) r).
    { apply (wf_ieval p c b (ins p c b r) (sr g1 c) r W Ib). intros; symmetry; apply Rb; auto. }
    assert (Ibx : ins p (sx eb) (sk eb) (sr g1 (sx eb)) = ins p c b r) by (rewrite Xb, Kb; exact Ib).
    (* the value of the read the binder made, cell by cell *)
    assert (DV : xload (ins p c b r) (sr g1 c) = true -> dec p c r b x = sm g1 x).
    { intros Xl. pose proof (sstep_load p W _ _ _ _ St1 Ibx ltac:(rewrite Xb; exact Xl)) as Lv.
      rewrite Xb, Kb in Lv. apply (dec_of p c r b (sm g1) x); [intros Z; rewrite Z in Ixb; destruct Ixb| |exact Ixb].
      rewrite Rbb, Lv. reflexivity. }
    destruct (srun_ev p W l g R qb eb Qb) as (i' & Hi' & _ & Sh). rewrite Xb, Kb in Hi', Sh. fold r in Hi', Sh.
    subst i'. unfold executes, icond in Exb.
    unfold bvx. destruct (ins p c b r) as [m ys cb|m ys cb v|m ys cb ex nv| |] eqn:Q; simpl in Ixb;
      try (destruct Ixb; fail); simpl in Exb, Sh |- *; rewrite Exb in Sh.
    + (* a load binder *)
      assert (Nwb : writes_x eb x = false) by (unfold writes_x; injection Sh as Sa _; rewrite Sa; reflexivity).
      rewrite (sruns_nowrite p W g1 [eb] g2 x (sruns_one p g1 eb g2 St1)) by (intros e [<-|[]]; auto).
      symmetry. apply DV. unfold xload. simpl. injection Evb as Ec. unfold icond, ieval. simpl. rewrite Ec. auto.
    + (* a store binder *)
      assert (Wb : writes_x eb x = true).
      { unfold writes_x. injection Sh as Sa _. rewrite Sa. apply existsb_exists. exists x. split; auto. apply Nat.eqb_refl. }
      rewrite (sstep_store p W _ _ _ (ISt m ys cb v) x St1 Ibx Wb).
      rewrite Xb. unfold wvals, wval. injection Evb as _ Ev. simpl. rewrite Ev. reflexivity.
    + (* a CAS binder *)
      assert (Xl : xload (ICas m ys cb ex nv) (sr g1 c) = true).
      { unfold xload. simpl. injection Evb as Ec _ _. unfold icond, ieval. simpl. rewrite Ec. auto. }
      pose proof (DV Xl) as D1.
      destruct (vok (r b)) eqn:Ok.
      * assert (Wb : writes_x eb x = true).
        { unfold writes_x. injection Sh as Sa _. rewrite Sa. rewrite ?Ok. apply existsb_exists. exists x. split; auto. apply Nat.eqb_refl. }
        rewrite (sstep_store p W _ _ _ (ICas m ys cb ex nv) x St1 Ibx Wb).
        rewrite Xb. unfold wvals, wval. injection Evb as _ _ Ev. simpl. rewrite Ev. reflexivity.
      * assert (Nwb : writes_x eb x = false) by (unfold writes_x; injection Sh as Sa _; rewrite Sa, ?Ok; reflexivity).
        rewrite (sruns_nowrite p W g1 [eb] g2 x (sruns_one p g1 eb g2 St1)) by (intros e [<-|[]]; auto).
        symmetry. exact D1.
Qed.
End Bind.

(* ---------- the base and the segments ---------- *)
Section Core.
Variable p : prog.
Hypothesis W : wf p.
Hypothesis Wc : cellful p.
Variable f : nat -> st.
Variable nb : nat.
Hypothesis T : trace p f nb.
Variables (lb : list sev) (gb : sst).
Hypothesis Bsr : srun p lb gb.
Hypothesis Bsp : forall c, sp gb c = pcs (f nb) c.
Hypothesis Brg : forall c j, j < pcs (f nb) c -> sr gb c j = rg (cs (f nb) c) j.
(* the SC replay takes the CAS outcomes the model's last state shows: at a passed slot its register's; where a
   step of the run fixed the result (S3c) for registers these continue below the place, that result; at the
   place of an access still pending, that access's *)
Let bs : sst -> nat -> bool := fun g c =>
  let cc := cs (f nb) c in let k := sp g c in let r := sr g c in
  if Nat.ltb k (pcs (f nb) c) then vok (rg cc k)
  else match fxv p f nb c k r with Some b => b | None =>
       match pend_at p c cc (pcs (f nb) c) (tp (f nb) c) r k with
       | Some k' => vok (rg cc k')
       | None => match hpend_at p c cc (pcs (f nb) c) (tp (f nb) c) r k with Some k' => vok (rg cc k') | None => true end
       end end.

Local Abbreviation sb := (f nb).

(* the registers of a context continue the context of a state of the run,
   no older than tau *)
Definition gov (g : sst) (tau c : nat) : Prop :=
  exists i, i <= nb /\ tau <= tm (f i) /\ ccJ p c (cs (f i) c) (pcs (f i) c) (bd (cs (f i) c)) (sr g c) (sp g c).

Definition CONS (l : list sev) (g : sst) (tau : nat) : Prop :=
  exists F, l = lb ++ F /\ nruns p bs gb F g /\ (forall e, In e F -> sg e = false) /\ forall c, gov g tau c.

Lemma CONS_run : forall l g tau, CONS l g tau -> srun p l g.
Proof. intros l g tau (F & -> & S & _ & _). apply (sruns_app p lb gb Bsr F g (nruns_sruns p bs _ _ _ S)). Qed.

Lemma CONS_sp : forall l g tau, CONS l g tau -> forall c, pcs sb c <= sp g c.
Proof. intros l g tau (F & -> & S & _ & _) c. rewrite <- Bsp. apply (sruns_sp p W _ _ _ (nruns_sruns p bs _ _ _ S)). Qed.

Lemma CONS_rg : forall l g tau, CONS l g tau -> forall c j, j < pcs sb c -> sr g c j = rg (cs sb c) j.
Proof.
  intros l g tau (F & -> & S & _ & _) c j L. rewrite (sruns_regs p W _ _ _ (nruns_sruns p bs _ _ _ S) c j) by (rewrite Bsp; auto). apply Brg; auto.
Qed.

Lemma CONS_base : CONS lb gb (tm sb).
Proof.
  exists []. split; [rewrite app_nil_r; auto|]. split; [constructor|]. split; [intros e []|].
  intros c. exists nb. split; [auto|]. split; [auto|]. rewrite Bsp.
  split; [auto|]. split; [intros j L; apply Brg; auto|]. split; [intros; lia|]. split; [|split; [|split; [|split; [|split]]]].
  - intros j k d L (_ & t & _ & F) _. pose proof (first_at_le _ _ _ _ _ _ _ _ F). lia.
  - intros j k m xs L (_ & _ & t & _ & F). pose proof (first_atR_le _ _ _ _ _ _ _ _ _ F). lia.
  - intros; lia.
  - intros; lia.
  - intros; lia.
  - intros; lia.
Qed.

Lemma CONS_mono : forall l g tau tau', tau' <= tau -> CONS l g tau -> CONS l g tau'.
Proof.
  intros l g tau tau' L (F & E & S & G & Gv). exists F. split; [auto|]. split; [auto|]. split; [auto|].
  intros c. destruct (Gv c) as (i & A & B & C). exists i. split; [auto|]. split; [lia|auto].
Qed.

Lemma CONS_ext : forall l g tau F' g' c' tau', CONS l g tau -> nruns p bs g F' g' ->
  (forall e, In e F' -> sx e = c' /\ sg e = false) -> gov g' tau' c' -> tau' <= tau -> CONS (l ++ F') g' tau'.
Proof.
  intros l g tau F' g' c' tau' (F & -> & S & G & Gv) S' X Gc L.
  exists (F ++ F'). split; [rewrite app_assoc; auto|]. split; [apply (nruns_trans p bs _ _ _ _ _ S S')|]. split.
  - intros e I. apply in_app_or in I. destruct I as [I|I]; [auto|apply X; auto].
  - intros c. destruct (Nat.eq_dec c c') as [->|N]; [auto|].
    destruct (sruns_other p W _ _ _ c (nruns_sruns p bs _ _ _ S') ltac:(intros e I; destruct (X e I); congruence)) as [Sp Sr].
    destruct (Gv c) as (i & A & B & C). exists i. split; [auto|]. split; [lia|]. rewrite Sp.
    apply (ccJ_agree_r p c _ _ _ (sr g c) (sr g' c) (sp g c) W); [intros j _; symmetry; apply Sr|exact C].
Qed.

Lemma CONS_prefix : forall l g tau q, CONS l g tau -> length lb <= q -> q <= length l ->
  exists g', CONS (firstn q l) g' tau /\ nruns p bs g' (skipn q l) g.
Proof.
  intros l g tau q (F & -> & S & G & Gv) L1 L2.
  assert (Eq : q = length lb + (q - length lb)) by lia.
  assert (E1 : firstn q (lb ++ F) = lb ++ firstn (q - length lb) F).
  { rewrite Eq at 1. rewrite firstn_app_2. reflexivity. }
  assert (E2 : skipn q (lb ++ F) = skipn (q - length lb) F).
  { rewrite skipn_app. rewrite skipn_all2 by lia. simpl. f_equal. }
  rewrite <- (firstn_skipn (q - length lb) F) in S.
  destruct (nruns_split p bs _ _ _ _ S) as (g1 & S1 & S2).
  exists g1. rewrite E1, E2. split; [|exact S2].
  exists (firstn (q - length lb) F). split; [auto|]. split; [auto|]. split.
  - intros e I. apply G. rewrite <- (firstn_skipn (q - length lb) F). apply in_or_app. left. exact I.
  - intros c. destruct (Gv c) as (i & A & B & C). exists i. split; [auto|]. split; [auto|].
    pose proof (sruns_sp p W _ _ _ (nruns_sruns p bs _ _ _ S2) c) as Sp2.
    apply (ccJ_agree_r p c _ _ _ (sr g c) (sr g1 c) (sp g1 c) W).
    + intros j Lj. apply (sruns_regs p W _ _ _ (nruns_sruns p bs _ _ _ S2) c j Lj).
    + apply (ccJ_le _ _ _ _ _ _ (sp g c)); [exact C| |exact Sp2].
      destruct C as (C0 & _). pose proof (sruns_sp p W _ _ _ (nruns_sruns p bs _ _ _ S1) c) as Sp1. rewrite Bsp in Sp1.
      pose proof (x_pcs _ _ (tr_ext p f nb T i nb A ltac:(lia)) c). lia.
Qed.

(* the core claim at birth times up to tau, for pending accesses and CASes
   whose read happened alone *)
Definition ldg (gt : tgt) : bool := match gt with TF d => is_load (inst_of d) | TH _ _ => true end.

Definition HC (tau : nat) : Prop := forall l g c k i gt, CONS l g tau -> item p f nb c k i gt ->
  pcs sb c <= k -> tm (f i) <= tau -> ldg gt = true ->
  plc p c (cs (f (S i)) c) (pcs (f (S i)) c) (sr g c) (S (tm (f i))) (tm (f i)) gt (sp g c) ->
  ~ fa p c (sp g c) ->
  ccJ p c (cs (f (S i)) c) (pcs (f (S i)) c) (bd (cs (f (S i)) c)) (sr g c) (sp g c) ->
  enc (map (sm g) (icells (tinst gt))) <> rval (tinst gt) (rg (cs sb c) k) -> RACY p.

(* an instruction before a place is not fenced on both sides: the guard()
   after it would be the place or have to be taken *)
Lemma plc_nofa : forall c cc pc r Tq gt j js, plc p c cc pc r (S Tq) Tq gt js -> pc <= j -> j < js -> ~ fa p c j.
Proof.
  intros c cc pc r Tq gt j js F L1 L2 (_ & Fa). destruct (Fa r) as [_ F2].
  destruct (Nat.eq_dec (S j) js) as [E|N].
  - subst js. pose proof (plc_tat _ _ _ _ _ _ _ _ F) as D. rewrite F2 in D. destruct gt; simpl in D; discriminate.
  - assert (Tk : taken p c cc pc r Tq (S j)).
    { apply (plc_before _ _ _ _ _ _ _ _ F (S j)); [lia|lia| | |].
      - rewrite F2. reflexivity.
      - intros v0 _. rewrite F2. reflexivity.
      - rewrite F2. right. left. reflexivity. }
    destruct (taken_dof _ _ _ _ _ _ _ Tk) as (d0 & D0). rewrite F2 in D0. discriminate.
Qed.

(* the value a CAS whose read happened alone took *)
Lemma half_rg_sb : forall c k i xs B u m, early_atR p f nb c k i xs B u -> S i <= m -> m <= nb -> pcs (f m) c <= k ->
  rg (cs (f m) c) k = rg (cs (f (S i)) c) k \/
  (vok (rg (cs (f (S i)) c) k) = true /\ rg (cs (f m) c) k = vd false (vv (rg (cs (f (S i)) c) k))).
Proof.
  intros c k i xs B u m Ea L1 L2 Pk.
  destruct (early_postR p f nb c k i xs B u Ea) as (Oh1 & _).
  apply (x_rgh _ _ (tr_ext p f nb T (S i) m L1 L2) c k ltac:(congruence) Pk).
Qed.

Lemma half_vv_sb : forall c k i xs B u m, early_atR p f nb c k i xs B u -> S i <= m -> m <= nb -> pcs (f m) c <= k ->
  vv (rg (cs (f m) c) k) = vv (rg (cs (f (S i)) c) k).
Proof.
  intros c k i xs B u m Ea L1 L2 Pk. destruct (half_rg_sb c k i xs B u m Ea L1 L2 Pk) as [E|(_ & E)]; rewrite E; [reflexivity|apply vv_vd].
Qed.

(* the replay's verdict at a place, read off the registers before it *)
Definition bsr (c j : nat) (r : regs) : bool :=
  let cc := cs (f nb) c in
  if Nat.ltb j (pcs (f nb) c) then vok (rg cc j)
  else match fxv p f nb c j r with Some b => b | None =>
       match pend_at p c cc (pcs (f nb) c) (tp (f nb) c) r j with
       | Some k' => vok (rg cc k')
       | None => match hpend_at p c cc (pcs (f nb) c) (tp (f nb) c) r j with Some k' => vok (rg cc k') | None => true end
       end end.

Lemma bs_bsr : forall g c, bs g c = bsr c (sp g c) (sr g c).
Proof. reflexivity. Qed.

Lemma bsr_agree : forall c j r r', agree r r' j -> bsr c j r = bsr c j r'.
Proof.
  intros c j r r' A. pose proof (Inv1_run p sb (tr_run p f nb T nb (le_n _))) as I1.
  assert (A' : agree r' r j) by (intros q Lq; symmetry; apply A; exact Lq).
  unfold bsr. destruct (Nat.ltb j (pcs (f nb) c)); [reflexivity|].
  rewrite (fxv_agree p f nb T W c j r r' A). destruct (fxv p f nb c j r'); [reflexivity|].
  assert (Pe : pend_at p c (cs sb c) (pcs sb c) (tp sb c) r j = pend_at p c (cs sb c) (pcs sb c) (tp sb c) r' j).
  { destruct (pend_at p c (cs sb c) (pcs sb c) (tp sb c) r j) as [k1|] eqn:E1.
    - apply (pend_at_char_s p sb c I1) in E1. destruct E1 as (d1 & P1). symmetry. apply (pend_at_char_s p sb c I1).
      exists d1. apply (placed_agree p W c _ _ r r' k1 d1 j A P1).
    - symmetry. apply (pend_at_none_s p sb c I1). intros (k1 & d1 & P1). apply (proj1 (pend_at_none_s p sb c I1 r j) E1).
      exists k1, d1. apply (placed_agree p W c _ _ r' r k1 d1 j A' P1). }
  assert (He : hpend_at p c (cs sb c) (pcs sb c) (tp sb c) r j = hpend_at p c (cs sb c) (pcs sb c) (tp sb c) r' j).
  { assert (HA : forall r1 r2 k1 m1 xs1, agree r1 r2 j -> hplaced p c (cs sb c) (pcs sb c) r1 k1 m1 xs1 j ->
                   hplaced p c (cs sb c) (pcs sb c) r2 k1 m1 xs1 j).
    { intros r1 r2 k1 m1 xs1 Ag (P1 & P2 & t1 & O1 & F1). split; [exact P1|]. split; [exact P2|]. exists t1. split; [exact O1|].
      unfold first_atR in *. apply (plc_agree p W c _ _ _ r1 r2 _ _ j Ag F1). }
    destruct (hpend_at p c (cs sb c) (pcs sb c) (tp sb c) r j) as [k1|] eqn:E1.
    - apply (hpend_at_char_s p sb c I1) in E1. destruct E1 as (m1 & xs1 & P1). symmetry. apply (hpend_at_char_s p sb c I1).
      exists m1, xs1. apply (HA r r' k1 m1 xs1 A P1).
    - symmetry. apply (hpend_at_none_s p sb c I1). intros (k1 & m1 & xs1 & P1). apply (proj1 (hpend_at_none_s p sb c I1 r j) E1).
      exists k1, m1, xs1. apply (HA r' r k1 m1 xs1 A' P1). }
  rewrite Pe, He. reflexivity.
Qed.

(* the replay's CAS verdicts: a success only with the values equal and the
   verdict the replay takes there *)
Definition scv (g : sst) : Prop := forall c j, pcs sb c <= j -> j < sp g c ->
  xload (ins p c j (sr g c)) (sr g c) = true -> is_cas (ins p c j (sr g c)) = true ->
  vok (sr g c j) = Nat.eqb (vv (sr g c j)) (cexp (ins p c j (sr g c)) (sr g c)) && bsr c j (sr g c).

Lemma scv_run : forall F g, nruns p bs gb F g -> scv g.
Proof.
  intros F g N. remember gb as g00 eqn:Eg. induction N as [g0|g0 l g1 c0 N IH].
  - subst g0. intros c j L1 L2. rewrite Bsp in L2. lia.
  - intros c j L1 L2 Xl Cs.
    set (g2 := snd (snext p bs g1 c0)) in *.
    pose proof (snext_step p bs g1 c0) as St. fold g2 in St.
    destruct (sstep_shape p W _ _ _ St) as (i0 & Hi0 & _ & Hk & Hsp & Hr & _).
    rewrite snext_x in Hi0, Hk, Hr, Hsp.
    assert (Ag : forall z, z < sp g1 c -> sr g2 c z = sr g1 c z).
    { intros z Lz. apply Hr. destruct (Nat.eq_dec c c0) as [->|N0]; [right; rewrite Hk; lia|left; exact N0]. }
    destruct (Nat.lt_ge_cases j (sp g1 c)) as [Lj|Lj].
    + assert (Aj : agree (sr g2 c) (sr g1 c) j) by (intros z Lz; apply Ag; lia).
      destruct (ins_agree p W c j (sr g2 c) (sr g1 c) Aj) as [E1 E2]. rewrite E1 in Xl, Cs, E2 |- *.
      assert (Xl1 : xload (ins p c j (sr g1 c)) (sr g1 c) = true)
        by (unfold xload in *; rewrite (ieval_cond _ _ _ E2) in Xl; exact Xl).
      rewrite (Ag j Lj), (cexp_ieval _ _ _ E2), (bsr_agree c j _ _ Aj).
      apply IH; auto.
    + assert (Ec : c = c0).
      { destruct (Nat.eq_dec c c0) as [->|N0]; [reflexivity|exfalso].
        rewrite Hsp in L2. unfold upd in L2. destruct (Nat.eqb_spec c c0); [congruence|lia]. }
      subst c0.
      assert (Ej : j = sp g1 c) by (rewrite Hsp in L2; unfold upd in L2; rewrite Nat.eqb_refl in L2; lia). subst j.
      assert (Aj : agree (sr g2 c) (sr g1 c) (sp g1 c)) by (intros z Lz; apply Ag; lia).
      destruct (ins_agree p W c (sp g1 c) (sr g2 c) (sr g1 c) Aj) as [E1 E2]. rewrite E1 in Xl, Cs, E2 |- *.
      assert (Xl1 : xload (ins p c (sp g1 c) (sr g1 c)) (sr g1 c) = true)
        by (unfold xload in *; rewrite (ieval_cond _ _ _ E2) in Xl; exact Xl).
      rewrite (cexp_ieval _ _ _ E2), (bsr_agree c _ _ _ Aj).
      unfold g2. rewrite snext_reg. cbv zeta. rewrite Xl1, (areg_cas _ _ _ Cs), vok_vd, vv_vd. reflexivity.
Qed.

Lemma CONS_scv : forall l g tau, CONS l g tau -> scv g.
Proof. intros l g tau (F & _ & N & _). apply (scv_run F g N). Qed.

(* a CAS that happened and wrote read its expected value *)
Lemma cas_ok_val : forall c k t d, oc (cs sb c) k = Some t -> ai (cs sb c) k = inst_of d -> is_cas (inst_of d) = true ->
  vok (rg (cs sb c) k) = true -> forall r, vv (rg (cs sb c) k) = cexp (inst_of d) r.
Proof.
  intros c k t d O A Ca V r.
  pose proof (Inv1_run p sb (tr_run p f nb T nb (le_n _))) as I1. pose proof (proj2 (Inv2_run p sb (tr_run p f nb T nb (le_n _)))) as I2.
  destruct (i_oc p sb I1 c k t O) as (e & E & Xe & Ke).
  assert (Ei : einstr p sb e = inst_of d) by (unfold einstr; rewrite Xe, Ke; exact A).
  pose proof (oc_eh p sb c k t e I1 O E Xe Ke) as Eh.
  assert (Xl : xload (inst_of d) (rgof sb e) = true) by (unfold xload; destruct d; simpl in Ca |- *; try discriminate; reflexivity).
  pose proof (j_ok p sb I2 t e E Eh ltac:(rewrite Ei; exact Ca) ltac:(rewrite Ei; exact Xl)) as J. rewrite Xe, Ke, V in J.
  destruct (j_ew p sb I2 t e _ E Ei) as [Wq _]. rewrite <- J in Wq. symmetry in Wq.
  apply andb_prop in Wq as [_ Wq]. rewrite Ca in Wq. simpl in Wq. rewrite andb_true_r in Wq. apply Nat.eqb_eq in Wq.
  destruct (j_val p sb I2 t e _ E Ei) as [Vl _]. specialize (Vl Xl). rewrite Xe, Ke, (rval_cas _ _ Ca) in Vl.
  rewrite Vl, Wq. change (cexp (inst_of d) (rgof sb e) = cexp (inst_of d) r). apply cexp_ieval. apply ieval_inst.
Qed.

(* a context runs forward, alone, to the place of one of its pending items *)
Lemma fwd : forall l g tau c k i gt, HC (tm (f i)) -> CONS l g tau -> item p f nb c k i gt ->
  pcs sb c <= k -> tm (f i) < tau ->
  RACY p \/
  (exists j, j < sp g c /\ plc p c (cs (f (S i)) c) (pcs (f (S i)) c) (sr g c) (S (tm (f i))) (tm (f i)) gt j) \/
  (exists F' g', sruns p g F' g' /\ (forall e, In e F' -> sx e = c) /\ CONS (l ++ F') g' (tm (f i)) /\
     plc p c (cs (f (S i)) c) (pcs (f (S i)) c) (sr g' c) (S (tm (f i))) (tm (f i)) gt (sp g' c) /\
     ccJ p c (cs (f (S i)) c) (pcs (f (S i)) c) (bd (cs (f (S i)) c)) (sr g' c) (sp g' c)).
Proof.
  intros l g tau c k i gt IH Co It Pk Lt.
  pose proof (item_i p f nb c k i gt It) as Li.
  assert (R1 : run p (f (S i))) by (apply (tr_run p f nb T); lia).
  pose proof (Inv1_run p (f (S i)) R1) as I1.
  assert (X1b : Ext (f (S i)) sb) by (apply (tr_ext p f nb T); lia).
  set (cc := cs (f (S i)) c) in *. set (pc := pcs (f (S i)) c) in *. set (N := tp (f (S i)) c) in *.
  set (Bs := bd cc) in *. set (Tt := tm (f i)) in *.
  assert (PO : pend_ok cc pc) by (apply (pend_ok_of p (f (S i)) c I1)).
  pose proof Co as (F & EF & SF & GF & Gv).
  assert (Al1 : alive f c k gt (S i)) by (unfold alive; pose proof (x_pcs _ _ X1b c); lia).
  (* the registers continue the state just after the item's step *)
  assert (C0 : ccJ p c cc pc Bs (sr g c) (sp g c)).
  { destruct (Gv c) as (ig & Lig & Tig & Cg).
    assert (Lii : i < ig) by (apply (tr_tm_lt p f nb T); lia).
    apply (mono_tr p f nb T W Wc c (sr g c) (sp g c) (S i) ig ltac:(lia) Lig Cg). }
  set (s0 := sp g c) in *. set (rr := rinf p bs g c).
  set (r := fun m => sr (snd (solo p bs g c m)) c).
  assert (Rr : forall m, agree (r m) rr (s0 + m)).
  { intros m j L. unfold r, rr. symmetry. apply (rinf_agree p W bs g c m j L). }
  set (G := creg p c cc pc N Bs (Fd p c rr)).
  assert (GB : forall j, creg p c cc pc N (bor Bs (fun _ => false)) (Fd p c rr) j = G j).
  { apply (creg_Bext p c cc pc N _ _ _ W PO). intros j. unfold bor. apply orb_false_r. }
  (* the item's place under these registers *)
  assert (Fs0 : exists js, plc p c cc pc G (S Tt) Tt gt js).
  { destruct (item_pending p f nb T W c k i gt (S i) It ltac:(lia) ltac:(lia) Al1) as [(d & -> & Pd & Od)|(xs & -> & Ph & Oh)].
    - destruct (INVP_run p (f (S i)) W Wc R1 c k d (fun _ => false) (Fd p c rr) Pd) as (js & _ & t & O & Fj).
      fold cc pc N in O, Fj, Od. rewrite Od in O. injection O as <-. exists js.
      apply (first_at_ext p c cc pc _ G Tt d js W GB Fj).
    - assert (Ch : oc cc k = None).
      { destruct It as [(d & B & u & E & _)|(xs' & B & u & E & Ea)]; [discriminate|].
        destruct (early_postR p f nb c k i xs' B u Ea) as (_ & _ & _ & Oc & _). unfold cc. rewrite Oc. apply Ea. }
      destruct (INVH_run p (f (S i)) W Wc R1 c k Plain xs (fun _ => false) (Fd p c rr) Ph Ch) as (js & _ & _ & t & O & Fj).
      fold cc pc N in O, Fj, Oh. rewrite Oh in O. injection O as <-. exists js.
      apply (first_atR_ext p c cc pc _ G Tt Plain xs js W GB Fj). }
  destruct Fs0 as (js & Fs).
  assert (Key : forall r0 J, ccJ p c cc pc Bs r0 J -> agree r0 rr J -> agree r0 G J).
  { intros r0 J C A j Lj. rewrite (ccJ_agree p (f (S i)) W Wc R1 c Bs r0 J C j Lj).
    apply (creg_f_agree p c cc pc N Bs (Fd p c r0) (Fd p c rr) J W PO); [|exact Lj].
    intros b y Lb. assert (Ab : agree r0 rr (S b)) by (apply (agree_le _ _ _ _ A); lia).
    unfold Fd. rewrite (proj1 (ins_agree p W c b r0 rr (agree_le _ _ _ b Ab ltac:(lia)))), (Ab b ltac:(lia)).
    rewrite (dec_agree p c r0 rr b y W Ab). reflexivity. }
  (* past the place already *)
  destruct (Nat.lt_ge_cases js s0) as [Bey|Ahead].
  { right. left. exists js. split; [auto|].
    assert (A0 : agree (sr g c) G s0) by (apply Key; [exact C0|intros j L; apply (Rr 0 j); lia]).
    apply (plc_agree p W c cc pc _ G (sr g c) Tt gt js); [intros j L; symmetry; apply A0; lia|exact Fs]. }
  (* the solo run, up to before the place, keeps the constraints, or a race appears *)
  assert (NoPl : forall r0 j', agree r0 G (S j') -> j' < js -> ~ plc p c cc pc r0 (S Tt) Tt gt j').
  { intros r0 j' A L F0. assert (F1 : plc p c cc pc G (S Tt) Tt gt j').
    { apply (plc_agree p W c cc pc _ r0 G Tt gt j'); [intros q Lq; apply A; lia|exact F0]. }
    pose proof (plc_unique _ _ _ _ _ _ _ _ _ Wc F1 Fs). lia. }
  assert (Seg : forall m, s0 + m <= js -> ccJ p c cc pc Bs (r m) (s0 + m) ->
            CONS (l ++ fst (solo p bs g c m)) (snd (solo p bs g c m)) Tt /\ agree (r m) G (s0 + m)).
  { intros m L C. assert (A : agree (r m) G (s0 + m)) by (apply Key; auto).
    split; [|exact A].
    apply (CONS_ext l g tau (fst (solo p bs g c m)) (snd (solo p bs g c m)) c Tt); [exact Co|apply solo_nruns| | |lia].
    - intros e I. split; [apply (solo_x p bs g c m e I)|].
      destruct (sg e) eqn:Sg; [|reflexivity]. exfalso.
      assert (Rl : srun p (l ++ fst (solo p bs g c m)) (snd (solo p bs g c m))) by (apply (sruns_app p l g (CONS_run _ _ _ Co)); apply solo_runs).
      apply In_nth_error in I. destruct I as (q & Q).
      assert (Q' : nth_error (l ++ fst (solo p bs g c m)) (length l + q) = Some e) by (rewrite nth_error_app2 by lia; rewrite Nat.add_comm, Nat.add_sub; auto).
      pose proof (sg_ffull_ev p _ _ _ e W Rl Q' Sg) as Ff. rewrite (solo_x p bs g c m e (nth_error_In _ _ Q)) in Ff.
      destruct (sruns_pos p W _ _ _ (solo_runs p bs g c m) e (nth_error_In _ _ Q)) as [P1' P2'].
      rewrite (solo_x p bs g c m e (nth_error_In _ _ Q)) in P1', P2'. rewrite (solo_sp p W bs) in P2'. fold s0 in P1', P2'.
      assert (Ae : agree (r m) G (sk e)) by (apply (agree_le _ _ _ _ A); lia).
      assert (Tk : taken p c cc pc G Tt (sk e)).
      { apply (plc_before _ _ _ _ _ _ _ _ Fs (sk e)).
        + pose proof C0 as (C00 & _). lia.
        + lia.
        + rewrite <- (exec_agree p W c (sk e) (r m) G Ae). unfold r. rewrite Ff. reflexivity.
        + intros v0 _. rewrite <- (proj1 (ins_agree p W c (sk e) (r m) G Ae)). unfold r. rewrite Ff. reflexivity.
        + rewrite <- (proj1 (ins_agree p W c (sk e) (r m) G Ae)). unfold r. rewrite Ff.
          right. left. reflexivity. }
      destruct (taken_dof _ _ _ _ _ _ _ Tk) as (d0 & D0).
      rewrite <- (eof_agree p W c (sk e) (r m) G Ae) in D0. unfold r in D0. rewrite Ff in D0. discriminate.
    - exists (S i). split; [lia|]. split; [unfold Tt; pose proof (x_tm _ _ (tr_ext p f nb T i (S i) ltac:(lia) ltac:(lia))); lia|].
      rewrite (solo_sp p W bs). exact C. }
  assert (IT : forall m, s0 + m <= js -> RACY p \/ ccJ p c cc pc Bs (r m) (s0 + m)).
  { induction m as [|m IHm]; intros L.
    - right. rewrite Nat.add_0_r. exact C0.
    - destruct (IHm ltac:(lia)) as [Rc|Cm]; [left; exact Rc|].
      destruct (Seg m ltac:(lia) Cm) as (Com & Am).
      set (j := s0 + m) in *. set (gm := snd (solo p bs g c m)) in *.
      assert (Jd : j = s0 + m) by reflexivity.
      assert (Spm : sp gm c = j) by (unfold gm, j; rewrite (solo_sp p W bs); reflexivity).
      assert (Srm : sr gm c = r m) by reflexivity.
      assert (St : sstep p gm (fst (snext p bs gm c)) (snd (snext p bs gm c))) by apply snext_step.
      assert (Ar : agree (r m) (r (S m)) j).
      { intros q Lq. unfold r. symmetry. apply (solo_stable p W bs g c m (S m) q); lia. }
      assert (Lm : forall q, q < j -> r (S m) q = r m q) by (intros q Lq; symmetry; apply Ar; auto).
      assert (Ij : ins p c j (r (S m)) = ins p c j (r m)) by (symmetry; apply (proj1 (ins_agree p W c j _ _ Ar))).
      assert (Ej : ieval (ins p c j (r m)) (r (S m)) = ieval (ins p c j (r m)) (r m)).
      { symmetry. apply (proj2 (ins_agree p W c j (r m) (r (S m)) Ar)). }
      destruct (sstep_shape p W _ _ _ St) as (i0 & Hi0 & _ & Hk & _ & _ & Hrk & _).
      rewrite snext_x in Hi0, Hk, Hrk. rewrite Hk in Hi0, Hrk. rewrite Spm in Hi0, Hrk.
      assert (Rj : r (S m) j = (if xload (ins p c j (r m)) (r m)
                                then areg (ins p c j (r m)) (Nat.eqb (enc (map (sm gm) (icells (ins p c j (r m))))) (cexp (ins p c j (r m)) (r m)) && bs gm c)
                                       (enc (map (sm gm) (icells (ins p c j (r m)))))
                                else 0)).
      { unfold r at 1. simpl. fold gm. rewrite <- Spm at 1. rewrite snext_reg. cbv zeta. rewrite Spm, Srm.
        destruct (xload (ins p c j (r m)) (r m)); auto. rewrite <- Srm.
        apply (srun_regs0 p W _ _ (CONS_run _ _ _ Com)). lia. }
      assert (RjV : xload (ins p c j (r m)) (r m) = true -> rval (ins p c j (r m)) (r (S m) j) = enc (map (sm gm) (icells (ins p c j (r m))))).
      { intros Xl. rewrite Rj, Xl. apply rval_areg. }
      pose proof Cm as Cm0. destruct Cm as (D0 & D1 & D2 & D3 & D3h & D4 & D5 & D6 & D7).
      assert (Ag1 : agree (r m) (rg cc) pc) by (intros q Lq; apply D1; auto).
      (* the slot's constraints: a pending access placed there *)
      assert (K3 : forall k' d', placed p c cc pc (r (S m)) k' d' j -> is_load (inst_of d') = true ->
                   RACY p \/ r (S m) j = rg cc k').
      { intros k' d' Pl Ld.
        destruct Pl as (Pd & t' & Ot & Fd).
        assert (Fd' : first_at p c cc pc (r m) t' d' j) by (apply (first_at_agree p W c cc pc (r (S m)) (r m) t' d' j); [intros q Lq; symmetry; apply Ar; auto|exact Fd]).
        pose proof (first_at_dof _ _ _ _ _ _ _ _ Fd' (load_accd _ Ld)) as Dd.
        pose proof (first_at_eof _ _ _ _ _ _ _ _ Fd') as De.
        destruct Pd as (Q1 & Q2 & Q3).
        destruct (early_of_pending p f nb T (S i) c k' t' ltac:(lia) Q1 Ot) as (ik & d'' & B'' & u'' & Eak & Lik & Tik).
        destruct (early_post p f nb c k' ik d'' B'' u'' Eak) as (Ok1 & Ak1 & Pk1 & _).
        assert (Dq : d'' = d').
        { destruct (pend_fate p f nb T (S ik) (S i) c k' d'' ltac:(lia) ltac:(lia) W ltac:(congruence) ltac:(rewrite Pk1; fold pc in Q1; pose proof (x_pcs _ _ (tr_ext p f nb T (S ik) (S i) ltac:(lia) ltac:(lia)) c); lia) Ak1)
            as [(_ & Aq)|(X1 & _)]; [|fold pc in X1; lia].
          fold cc in Aq. rewrite Q3 in Aq. apply inst_of_inj in Aq. auto. }
        subst d''.
        assert (Itk : item p f nb c k' ik (TF d')) by (left; exists d', B'', u''; auto).
        rewrite <- Tik in Fd'.
        assert (Fo : first_at p c (cs (f (S ik)) c) (pcs (f (S ik)) c) (r m) (tm (f ik)) d' j).
        { apply (place_trace p f nb T W Wc c k' ik (TF d') (S i) (r m) j Itk ltac:(lia) ltac:(lia) Q1 Ag1 ltac:(lia)). exact Fd'. }
        assert (Ab : agree (r m) (rg (cs sb c)) (pcs sb c)).
        { intros q Lq. rewrite <- Srm. apply (CONS_rg _ _ _ Com). auto. }
        assert (Pb : pcs sb c <= k').
        { destruct (Nat.lt_ge_cases k' (pcs sb c)) as [X1|X1]; auto. exfalso.
          pose proof (passed_place p f nb T W Wc c k' ik d' B'' u'' nb (r m) j Eak ltac:(lia) (le_n _) X1 Ab Fo) as Ejk.
          pose proof (CONS_sp _ _ _ Com c). rewrite Spm in H. lia. }
        assert (Jb : pcs sb c <= j) by (pose proof (CONS_sp _ _ _ Com c) as H; rewrite Spm in H; lia).
        assert (Xl : xload (ins p c j (r m)) (r m) = true).
        { destruct (dof_shape _ _ _ Dd) as (_ & _ & Il & _ & _ & Co' & _). unfold xload. rewrite Il, Ld, Co'. reflexivity. }
        destruct (eof_cexp _ _ _ (r m) De) as (Csd & Ced).
        assert (Rgsb : rg (cs sb c) k' = rg cc k')
          by (apply (x_rg _ _ (tr_ext p f nb T (S i) nb ltac:(lia) ltac:(lia)) c k'); right; change (oc cc k' <> None); rewrite Ot; discriminate).
        destruct (Nat.eq_dec (rval (inst_of d') (r (S m) j)) (rval (inst_of d') (rg cc k'))) as [Eq|Ne]; [right|left].
        2:{ apply (IH (l ++ fst (solo p bs g c m)) gm c k' ik (TF d')); auto.
            - pose proof (x_tm _ _ (tr_ext p f nb T ik i ltac:(lia) ltac:(lia))). unfold Tt in *. lia.
            - rewrite Spm, Srm. exact Fo.
            - rewrite Spm. apply (plc_nofa c cc pc G Tt gt j js Fs); [pose proof C0 as (C00 & _); lia|lia].
            - rewrite Spm, Srm. apply (mono_tr p f nb T W Wc c (r m) j (S ik) (S i) ltac:(lia) ltac:(lia)). exact Cm0.
            - cbn [tinst]. rewrite Rgsb. intros Z. apply Ne. rewrite <- Z.
              rewrite (rval_iscas (inst_of d') (ins p c j (r m))) by exact Csd. rewrite (RjV Xl).
              destruct (dof_shape _ _ _ Dd) as (Ic & _). rewrite Ic. reflexivity. }
        (* the verdict: the SC replay takes the model's at the place *)
        destruct (is_cas (inst_of d')) eqn:Cd.
        2:{ destruct d'; simpl in Cd; try discriminate; simpl in Eq; exact Eq. }
        destruct (fxv p f nb c j (r m)) as [bx|] eqn:Fv.
        { (* a result fixed at the place, for registers that continue the fix's state: the access's own *)
          assert (Bs1 : bs gm c = bx).
          { unfold bs. rewrite Spm, Srm. replace (Nat.ltb j (pcs (f nb) c)) with false by (symmetry; apply Nat.ltb_ge; exact Jb). rewrite Fv. reflexivity. }
          assert (Ck : ccJ p c (cs (f (S ik)) c) (pcs (f (S ik)) c) (bd (cs (f (S ik)) c)) (r m) j)
            by (apply (mono_tr p f nb T W Wc c (r m) j (S ik) (S i) ltac:(lia) ltac:(lia)); exact Cm0).
          pose proof (fix_whole p f nb T W Wc c k' ik d' B'' u'' (r m) j bx Eak Ck Fo Pb Cd Fv) as V.
          assert (Rik : rg (cs (f (S ik)) c) k' = rg cc k').
          { symmetry. apply (x_rg _ _ (tr_ext p f nb T (S ik) (S i) ltac:(lia) ltac:(lia)) c k'). right.
            destruct (early_post p f nb c k' ik d' B'' u'' Eak) as (Ok' & _). rewrite Ok'. discriminate. }
          rewrite Rik in V.
          assert (Vk : vv (rg cc k') = enc (map (sm gm) (icells (ins p c j (r m))))).
          { rewrite !(rval_cas _ _ Cd) in Eq. rewrite <- Eq. rewrite <- (rval_cas (ins p c j (r m))) by (rewrite <- Csd; reflexivity). apply (RjV Xl). }
          rewrite Rj, Xl. rewrite (areg_cas _ _ _ ltac:(rewrite <- Csd; reflexivity)).
          rewrite <- (vd_split (rg cc k')). rewrite Bs1, V, Vk, Ced. f_equal. apply andb_comm. }
        assert (Bs1 : bs gm c = vok (rg cc k')).
        { unfold bs. rewrite Spm, Srm. replace (Nat.ltb j (pcs (f nb) c)) with false by (symmetry; apply Nat.ltb_ge; exact Jb).
          rewrite Fv.
          assert (Pkb : pend_at p c (cs sb c) (pcs sb c) (tp sb c) (r m) j = Some k').
          { apply (pend_at_char_s p sb c (Inv1_run p sb (tr_run p f nb T nb (le_n _)))). exists d'. split.
            - split; [exact Pb|]. split; [rewrite (x_oc _ _ (tr_ext p f nb T (S i) nb ltac:(lia) ltac:(lia)) c k' t' Ot); discriminate|].
              rewrite (x_aip _ _ (tr_ext p f nb T (S i) nb ltac:(lia) ltac:(lia)) c k' ltac:(change (oc cc k' <> None); rewrite Ot; discriminate) Pb). exact Q3.
            - exists t'. split; [apply (x_oc _ _ (tr_ext p f nb T (S i) nb ltac:(lia) ltac:(lia)) c k' t' Ot)|].
              unfold first_at. rewrite <- Tik. apply (place_trace p f nb T W Wc c k' ik (TF d') nb (r m) j Itk ltac:(lia) (le_n _) Pb Ab Jb). exact Fo. }
          rewrite Pkb. rewrite Rgsb. reflexivity. }
        rewrite Rj, Xl. rewrite (areg_cas _ _ _ ltac:(rewrite <- Csd; reflexivity)).
        rewrite <- (vd_split (rg cc k')). rewrite Bs1. f_equal.
        - destruct (vok (rg cc k')) eqn:Vk; [|apply andb_false_r]. rewrite andb_true_r.
          (* a CAS that succeeded: the value it read is its expected value *)
          apply Nat.eqb_eq.
          assert (Vr : vv (r (S m) j) = enc (map (sm gm) (icells (ins p c j (r m))))).
          { rewrite <- (rval_cas (ins p c j (r m))) by (rewrite <- Csd; reflexivity). apply (RjV Xl). }
          rewrite <- Vr. rewrite !(rval_cas _ _ Cd) in Eq. rewrite Eq. rewrite <- Rgsb.
          rewrite (cas_ok_val c k' t' d' (x_oc _ _ (tr_ext p f nb T (S i) nb ltac:(lia) ltac:(lia)) c k' t' Ot)
                     ltac:(rewrite (x_aip _ _ (tr_ext p f nb T (S i) nb ltac:(lia) ltac:(lia)) c k' ltac:(change (oc cc k' <> None); rewrite Ot; discriminate) Pb); exact Q3)
                     Cd ltac:(rewrite Rgsb; exact Vk) (r m)).
          exact Ced.
        - rewrite !(rval_cas _ _ Cd) in Eq. rewrite <- Eq. rewrite <- (rval_cas (ins p c j (r m))) by (rewrite <- Csd; reflexivity).
          rewrite (RjV Xl). reflexivity. }
      (* a CAS whose read happened alone placed there *)
      assert (K3h : forall k' m0 xs0, hplaced p c cc pc (r (S m)) k' m0 xs0 j -> RACY p \/
                    (vv (r (S m) j) = vv (rg cc k') /\ (fx cc j = None -> vok (rg cc k') = false -> r (S m) j = rg cc k') /\
                     (fx cc j = None -> vok (r (S m) j) = true -> vok (rg cc k') = true /\ cfailv (ins p c j (r (S m))) (r (S m)) (rg cc k') = false))).
      { intros k' m0 xs0 Pl.
        destruct (Nat.eq_dec (vv (r (S m) j)) (vv (rg cc k'))) as [Eq|Ne].
        { right. split; [exact Eq|].
          (* the verdict bits: the SC replay takes, at the place j, the bit the model's final state shows for
             k', and a commit to failure stays *)
          pose proof Pl as (Ph & Ch & t' & Ot & Fd).
          assert (Fd' : first_atR p c cc pc (r m) t' m0 xs0 j) by (unfold first_atR in *; apply (plc_agree p W c cc pc _ (r (S m)) (r m) t' _ j); [intros q Lq; symmetry; apply Ar; auto|exact Fd]).
          pose proof Ph as (Q1 & _ & Q3).
          destruct (early_of_hpending p f nb T (S i) c k' t' ltac:(lia) Ot) as (ik & xs' & B'' & u'' & Eak & Lik & Tik).
          destruct (early_pendingR p f nb T c k' ik xs' B'' u'' (S i) Eak ltac:(lia) ltac:(lia) ltac:(fold pc; lia)) as ((_ & _ & Q3') & _).
          fold cc in Q3'. rewrite Q3 in Q3'. injection Q3' as -> <-.
          assert (Hpm : hplaced p c cc pc (r m) k' Plain xs0 j).
          { split; [exact Ph|]. split; [exact Ch|]. exists t'. split; [exact Ot|exact Fd']. }
          assert (Itk : item p f nb c k' ik (TH Plain xs0)) by (right; exists xs0, B'', u''; auto).
          rewrite <- Tik in Fd'.
          assert (Fo : first_atR p c (cs (f (S ik)) c) (pcs (f (S ik)) c) (r m) (tm (f ik)) Plain xs0 j).
          { apply (place_trace p f nb T W Wc c k' ik (TH Plain xs0) (S i) (r m) j Itk ltac:(lia) ltac:(lia) Q1 Ag1 ltac:(lia)). exact Fd'. }
          pose proof (first_atR_eofR _ _ _ _ _ _ _ _ _ Fd') as DR.
          assert (Cas : is_cas (ins p c j (r m)) = true) by (apply (eofR_cas _ (r m) _ DR)).
          assert (Xr : xload (ins p c j (r m)) (r m) = true).
          { destruct (ins p c j (r m)) as [m1 x1 c1|m1 x1 c1 v1|m2 x2 c2 e2 n2|f1|]; simpl in DR; try discriminate.
            unfold xload, icond. simpl. destruct (c2 (r m)); [reflexivity|discriminate]. }
          assert (Ab : agree (r m) (rg (cs sb c)) (pcs sb c)).
          { intros q Lq. rewrite <- Srm. apply (CONS_rg _ _ _ Com). auto. }
          assert (Rsb : run p sb) by (apply (tr_run p f nb T); lia).
          pose proof (Inv1_run p sb Rsb) as Isb.
          assert (BsX : fx cc j = None -> (vok (rg cc k') = false -> bs gm c = false) /\ (bs gm c = true -> vok (rg cc k') = true)).
          { intros Fn. destruct (fxv p f nb c j (r m)) as [bx|] eqn:Fv.
            { (* a result fixed there later, for these registers: the read half had not failed *)
              assert (Pb : pcs sb c <= k').
              { destruct (Nat.lt_ge_cases k' (pcs sb c)) as [X1|X1]; auto. exfalso.
                pose proof (passed_placeR p f nb T W Wc c k' ik xs0 B'' u'' nb (r m) j Eak ltac:(lia) (le_n _) X1 Ab Fo) as Ejk.
                pose proof (CONS_sp _ _ _ Com c). rewrite Spm in H. lia. }
              pose proof (fix_half p f nb T W Wc c k' ik xs0 B'' u'' i (r m) j bx Eak ltac:(lia) Li Hpm Pb Fn Fv) as Vt.
              change (vok (rg cc k') = true) in Vt. split; [intros V; congruence|intros _; exact Vt]. }
          assert (BsF : vok (rg cc k') = false -> bs gm c = false).
          { intros Vf.
            assert (Vsb : vok (rg (cs sb c) k') = false) by (apply (half_fail_vok p f nb T (S i) nb c k' t' ltac:(lia) (le_n _) Ot Ch Q1 Vf)).
            assert (Osb : oc (cs sb c) k' = None) by (apply (half_fail_stays p f nb T (S i) nb c k' t' ltac:(lia) (le_n _) Ot Ch Q1 Vf)).
            unfold bs. rewrite Spm, Srm.
            destruct (Nat.lt_ge_cases k' (pcs sb c)) as [X1|X1].
            - pose proof (passed_placeR p f nb T W Wc c k' ik xs0 B'' u'' nb (r m) j Eak ltac:(lia) (le_n _) X1 Ab Fo) as Ejk.
              rewrite Ejk. replace (Nat.ltb k' (pcs (f nb) c)) with true by (symmetry; apply Nat.ltb_lt; exact X1). exact Vsb.
            - assert (Jb : pcs sb c <= j) by (pose proof (CONS_sp _ _ _ Com c) as H; rewrite Spm in H; lia).
              replace (Nat.ltb j (pcs (f nb) c)) with false by (symmetry; apply Nat.ltb_ge; exact Jb).
              rewrite Fv.
              assert (Hpl : hplaced p c (cs sb c) (pcs sb c) (r m) k' Plain xs0 j).
              { split; [split; [exact X1|split]|].
                - rewrite (x_oh _ _ X1b c k' t' Ot). discriminate.
                - rewrite (x_cash _ _ X1b c k' ltac:(fold cc; rewrite Ot; discriminate) X1). exact Q3.
                - split; [exact Osb|]. exists t'. split; [apply (x_oh _ _ X1b c k' t' Ot)|].
                  unfold first_atR. rewrite <- Tik.
                  apply (place_trace p f nb T W Wc c k' ik (TH Plain xs0) nb (r m) j Itk ltac:(lia) (le_n _) X1 Ab Jb). exact Fo. }
              assert (Pn : pend_at p c (cs sb c) (pcs sb c) (tp sb c) (r m) j = None).
              { apply (pend_at_none_s p sb c Isb). intros (k2 & d2 & P2). apply (placed_hplaced p sb Rsb c (r m) k2 d2 k' Plain xs0 j P2 Hpl). }
              assert (Hp : hpend_at p c (cs sb c) (pcs sb c) (tp sb c) (r m) j = Some k').
              { apply (hpend_at_char_s p sb c Isb). exists Plain, xs0. exact Hpl. }
              rewrite Pn, Hp. exact Vsb. }
          split; [exact BsF|]. intros Bt. apply not_false_iff_true. intros V. rewrite (BsF V) in Bt. discriminate. }
          assert (Ve : vv (r (S m) j) = enc (map (sm gm) (icells (ins p c j (r m))))).
          { rewrite <- (rval_cas _ _ Cas). apply (RjV Xr). }
          split.
          - intros Fn Vf. rewrite Rj, Xr, (areg_cas _ _ _ Cas), (proj1 (BsX Fn) Vf), andb_false_r.
            rewrite <- (vd_split (rg cc k')), Vf, <- Eq, Ve. reflexivity.
          - intros Fn Vt. pose proof Vt as Vt'. rewrite Rj, Xr, (areg_cas _ _ _ Cas), vok_vd in Vt'. apply andb_prop in Vt' as [Eb Bt].
            assert (Vc : vok (rg cc k') = true) by (apply (proj2 (BsX Fn)); exact Bt).
            split; [exact Vc|]. apply Nat.eqb_eq in Eb. rewrite Ij.
            apply (cfailv_ok (ins p c j (r m)) (r (S m)) (r m) (rg cc k') Cas Ej Vc).
            rewrite <- Eq, Ve, Eb. clear -Cas. revert Cas. destruct (ins p c j (r m)); simpl; intros Cas; try discriminate; reflexivity. }
        left.
        destruct Pl as (Ph & Ch & t' & Ot & Fd).
        assert (Fd' : first_atR p c cc pc (r m) t' m0 xs0 j) by (unfold first_atR in *; apply (plc_agree p W c cc pc _ (r (S m)) (r m) t' _ j); [intros q Lq; symmetry; apply Ar; auto|exact Fd]).
        pose proof Ph as (Q1 & _ & Q3).
        destruct (early_of_hpending p f nb T (S i) c k' t' ltac:(lia) Ot) as (ik & xs' & B'' & u'' & Eak & Lik & Tik).
        destruct (early_pendingR p f nb T c k' ik xs' B'' u'' (S i) Eak ltac:(lia) ltac:(lia) ltac:(fold pc; lia)) as ((_ & _ & Q3') & _).
        fold cc in Q3'. rewrite Q3 in Q3'. injection Q3' as -> <-.
        assert (Itk : item p f nb c k' ik (TH Plain xs0)) by (right; exists xs0, B'', u''; auto).
        rewrite <- Tik in Fd'.
        assert (Fo : first_atR p c (cs (f (S ik)) c) (pcs (f (S ik)) c) (r m) (tm (f ik)) Plain xs0 j).
        { apply (place_trace p f nb T W Wc c k' ik (TH Plain xs0) (S i) (r m) j Itk ltac:(lia) ltac:(lia) Q1 Ag1 ltac:(lia)). exact Fd'. }
        assert (Pb : pcs sb c <= k').
        { destruct (Nat.lt_ge_cases k' (pcs sb c)) as [X1|X1]; auto. exfalso.
          assert (Ab : agree (r m) (rg (cs sb c)) (pcs sb c)).
          { intros q Lq. rewrite <- Srm. apply (CONS_rg _ _ _ Com). auto. }
          pose proof (passed_placeR p f nb T W Wc c k' ik xs0 B'' u'' nb (r m) j Eak ltac:(lia) (le_n _) X1 Ab Fo) as Ejk.
          pose proof (CONS_sp _ _ _ Com c). rewrite Spm in H. lia. }
        pose proof (first_atR_eofR _ _ _ _ _ _ _ _ _ Fd') as DR.
        apply (IH (l ++ fst (solo p bs g c m)) gm c k' ik (TH Plain xs0)); auto.
        - pose proof (x_tm _ _ (tr_ext p f nb T ik i ltac:(lia) ltac:(lia))). unfold Tt in *. lia.
        - rewrite Spm, Srm. exact Fo.
        - rewrite Spm. apply (plc_nofa c cc pc G Tt gt j js Fs); [pose proof C0 as (C00 & _); lia|lia].
        - rewrite Spm, Srm. apply (mono_tr p f nb T W Wc c (r m) j (S ik) (S i) ltac:(lia) ltac:(lia)). exact Cm0.
        - cbn [tinst rval crd]. rewrite (half_vv_sb c k' ik xs0 B'' u'' nb Eak ltac:(lia) (le_n _) Pb).
          rewrite <- (half_vv_sb c k' ik xs0 B'' u'' (S i) Eak ltac:(lia) ltac:(lia) ltac:(fold pc; lia)).
          fold cc. intros Z. apply Ne.
          assert (Xr : xload (ins p c j (r m)) (r m) = true).
          { destruct (ins p c j (r m)) as [m1 x1 c1|m1 x1 c1 v1|m2 x2 c2 e2 n2|f1|]; simpl in DR; try discriminate.
            unfold xload, icond. simpl. destruct (c2 (r m)); [reflexivity|discriminate]. }
          rewrite <- (rval_cas (ins p c j (r m)) _ (eofR_cas _ (r m) _ DR)), (RjV Xr), (eofR_icells _ _ _ _ DR). exact Z. }
      assert (K4 : forall x b, Bs j = true -> ~ pslot p c cc pc (r (S m)) j -> fbinder p c (r (S m)) j x = Some b ->
                   RACY p \/ dec p c (r (S m)) j x = bvx p c (r (S m)) b x (dec p c (r (S m)) b x)).
      { intros x b Bj Np Fb.
        assert (Fb' : fbinder p c (r m) j x = Some b)
          by (rewrite <- (fbinder_agree p W c (r (S m)) (r m) j x); [exact Fb|intros q Lq; symmetry; apply Ar; auto]).
        pose proof (fbinder_lt _ _ _ _ _ _ Fb') as Lb.
        destruct (fbinder_spec p c (r m) j x b Fb') as (Brm & Crm & Ixm & _).
        assert (Xlj : xload (ins p c j (r m)) (r m) = true).
        { unfold xload. rewrite Crm. destruct (ins p c j (r m)) as [[] | | [] | |]; simpl in Brm; try discriminate; reflexivity. }
        assert (Dj : dec p c (r (S m)) j x = sm gm x).
        { apply (dec_of p c (r (S m)) j (sm gm) x).
          - rewrite Ij. intros Z. rewrite Z in Ixm. destruct Ixm.
          - rewrite Ij, Rj, Xlj. apply rval_areg.
          - rewrite Ij. exact Ixm. }
        assert (Ab : agree (r m) (r (S m)) (S b)) by (apply (agree_le _ _ _ _ Ar); lia).
        assert (Eb : bvx p c (r (S m)) b x (dec p c (r (S m)) b x) = bvx p c (r m) b x (dec p c (r m) b x)).
        { rewrite (dec_agree p c (r (S m)) (r m) b x W) by (intros q Lq; symmetry; apply Ab; auto).
          apply (bvx_agree p W c (r (S m)) (r m) b j x _ Lb). intros q Lq; symmetry; apply Ar; auto. }
        rewrite Dj, Eb.
        destruct (Nat.eq_dec (sm gm x) (bvx p c (r m) b x (dec p c (r m) b x))) as [Eq|Ne]; [right; exact Eq|left].
        apply (bind_race p W bs (l ++ fst (solo p bs g c m)) gm c x b (CONS_run _ _ _ Com)); rewrite ?Spm, ?Srm; auto. }
      (* the earlier slots keep their constraints *)
      assert (Old3 : forall q k2 d2, q < j -> placed p c cc pc (r (S m)) k2 d2 q -> is_load (inst_of d2) = true -> r (S m) q = rg cc k2).
      { intros q k2 d2 L1 P2 L2. rewrite Lm by lia. apply (D3 q k2 d2); [lia| |auto].
        apply (placed_agree p W c cc pc (r (S m)) (r m) k2 d2 q); [intros z Lz; symmetry; apply Ar; lia|exact P2]. }
      assert (Old3h : forall q k2 m2 xs2, q < j -> hplaced p c cc pc (r (S m)) k2 m2 xs2 q ->
                vv (r (S m) q) = vv (rg cc k2) /\ (fx cc q = None -> vok (rg cc k2) = false -> r (S m) q = rg cc k2) /\
                (fx cc q = None -> vok (r (S m) q) = true -> vok (rg cc k2) = true /\ cfailv (ins p c q (r (S m))) (r (S m)) (rg cc k2) = false)).
      { intros q k2 m2 xs2 L1 (P1 & P2 & t2 & O2 & F2). rewrite Lm by lia.
        rewrite (cfailv_agree p W c q (r (S m)) (r m) _ (fun z Lz => eq_sym (Ar z ltac:(lia)))).
        apply (D3h q k2 m2 xs2); [lia|].
        split; [exact P1|]. split; [exact P2|]. exists t2. split; [exact O2|]. unfold first_atR in *.
        apply (plc_agree p W c cc pc _ (r (S m)) (r m) t2 _ q); [intros z Lz; symmetry; apply Ar; lia|exact F2]. }
      assert (Npq : forall q, q < j -> ~ pslot p c cc pc (r (S m)) q -> ~ pslot p c cc pc (r m) q).
      { intros q Lq Np [(k3 & d3 & P3)|(k3 & m3 & xs3 & (P1 & P2 & t3 & O3 & F3))]; apply Np; [left|right].
        - exists k3, d3. apply (placed_agree p W c cc pc (r m) (r (S m)) k3 d3 q); [intros z Lz; apply Ar; lia|exact P3].
        - exists k3, m3, xs3. split; [exact P1|]. split; [exact P2|]. exists t3. split; [exact O3|]. unfold first_atR in *.
          apply (plc_agree p W c cc pc _ (r m) (r (S m)) t3 _ q); [intros z Lz; apply Ar; lia|exact F3]. }
      assert (Old5 : forall q, pc <= q -> q < j -> ~ pslot p c cc pc (r (S m)) q -> is_cas (ins p c q (r (S m))) = true ->
                vok (r (S m) q) = true -> Nat.eqb (vv (r (S m) q)) (cexp (ins p c q (r (S m))) (r (S m))) = true).
      { intros q L0 L1 Np Cs Vr. assert (Aq : agree (r (S m)) (r m) q) by (intros z Lz; symmetry; apply Ar; lia).
        destruct (ins_agree p W c q (r (S m)) (r m) Aq) as [E1 E2].
        rewrite E1 in Cs, E2 |- *. rewrite (cexp_ieval _ _ _ E2). rewrite (Lm q L1) in Vr |- *.
        apply (D5 q L0 ltac:(lia) (Npq q L1 Np) Cs Vr). }
      assert (Old4 : forall q x b, pc <= q -> q < j -> Bs q = true -> ~ pslot p c cc pc (r (S m)) q ->
                     fbinder p c (r (S m)) q x = Some b ->
                     dec p c (r (S m)) q x = bvx p c (r (S m)) b x (dec p c (r (S m)) b x)).
      { intros q x b L1 L2 Bq Np Fb.
        assert (Aq : agree (r m) (r (S m)) (S q)) by (apply (agree_le _ _ _ _ Ar); lia).
        assert (Fbm : fbinder p c (r m) q x = Some b)
          by (rewrite <- (fbinder_agree p W c (r (S m)) (r m) q x); [exact Fb|intros z Lz; symmetry; apply Aq; lia]).
        pose proof (fbinder_lt _ _ _ _ _ _ Fbm) as Lb.
        rewrite <- (dec_agree p c (r m) (r (S m)) q x W Aq).
        rewrite <- (dec_agree p c (r m) (r (S m)) b x W (agree_le _ _ (S q) (S b) Aq ltac:(lia))).
        rewrite <- (bvx_agree p W c (r m) (r (S m)) b q x _ Lb (agree_le _ _ (S q) q Aq ltac:(lia))).
        apply (D4 q x b); [auto|lia|auto| |exact Fbm]. apply Npq; auto. }
      assert (Old2 : forall q, pc <= q -> q < j -> is_load (ins p c q (r (S m))) && icond (ins p c q (r (S m))) (r (S m)) = false -> r (S m) q = 0).
      { intros q L1 L2 X. assert (Aq : agree (r m) (r (S m)) q) by (apply (agree_le _ _ _ _ Ar); lia).
        destruct (ins_agree p W c q (r m) (r (S m)) Aq) as [E1 E2].
        rewrite Lm by lia. apply D2; [auto|lia|]. rewrite (ieval_cond _ _ _ E2), E1. exact X. }
      assert (Old6 : forall q bq, pc <= q -> q < j -> (forall k2 d2, ~ placed p c cc pc (r (S m)) k2 d2 q) ->
                is_load (ins p c q (r (S m))) && icond (ins p c q (r (S m))) (r (S m)) = true -> is_cas (ins p c q (r (S m))) = true ->
                fx cc q = Some bq -> vok (r (S m) q) = bq && Nat.eqb (vv (r (S m) q)) (cexp (ins p c q (r (S m))) (r (S m)))).
      { intros q bq L0 L1 Np X Cs Fx. assert (Aq : agree (r (S m)) (r m) q) by (intros z Lz; symmetry; apply Ar; lia).
        destruct (ins_agree p W c q (r (S m)) (r m) Aq) as [E1 E2].
        rewrite E1 in X, Cs, E2 |- *. rewrite (cexp_ieval _ _ _ E2). rewrite (ieval_cond _ _ _ E2) in X. rewrite (Lm q L1).
        apply (D6 q bq L0 ltac:(lia)); auto. intros k2 d2 P2. apply (Np k2 d2).
        apply (placed_agree p W c cc pc (r m) (r (S m)) k2 d2 q); [intros z Lz; apply Ar; lia|exact P2]. }
      (* DQ: a read of no cell before j keeps its register enc [] *)
      assert (Old7 : forall q, pc <= q -> q < j -> ~ pslot p c cc pc (r (S m)) q -> icells (ins p c q (r (S m))) = [] ->
                is_load (ins p c q (r (S m))) && icond (ins p c q (r (S m))) (r (S m)) = true -> rval (ins p c q (r (S m))) (r (S m) q) = 0).
      { intros q L0 L1 Np Ic X. assert (Aq : agree (r (S m)) (r m) q) by (intros z Lz; symmetry; apply Ar; lia).
        destruct (ins_agree p W c q (r (S m)) (r m) Aq) as [E1 E2].
        rewrite E1, (Lm q L1). apply (D7 q L0 ltac:(lia) (Npq q L1 Np)); [rewrite <- E1; exact Ic|rewrite <- E1, <- (ieval_cond _ _ _ E2); exact X]. }
      (* a result fixed at j: the replay's verdict there is it *)
      assert (A6j : forall bq, (forall k2 d2, ~ placed p c cc pc (r (S m)) k2 d2 j) ->
                is_load (ins p c j (r (S m))) && icond (ins p c j (r (S m))) (r (S m)) = true -> is_cas (ins p c j (r (S m))) = true ->
                fx cc j = Some bq -> vok (r (S m) j) = bq && Nat.eqb (vv (r (S m) j)) (cexp (ins p c j (r (S m))) (r (S m)))).
      { intros bq _ X Cs Fx.
        assert (Fv : fxv p f nb c j (r m) = Some bq) by (apply (fxv_ccJ p f nb T W Wc (S i) c j (r m) j bq ltac:(lia) Cm0 (le_n _) Fx)).
        assert (Jb : pcs sb c <= j) by (pose proof (CONS_sp _ _ _ Com c) as H; rewrite Spm in H; lia).
        assert (Bs1 : bs gm c = bq).
        { unfold bs. rewrite Spm, Srm. replace (Nat.ltb j (pcs (f nb) c)) with false by (symmetry; apply Nat.ltb_ge; exact Jb). rewrite Fv. reflexivity. }
        rewrite Ij in X, Cs |- *. rewrite (cexp_ieval _ _ _ Ej). rewrite (ieval_cond _ _ _ Ej) in X.
        assert (Xl : xload (ins p c j (r m)) (r m) = true) by (unfold xload; exact X).
        rewrite Rj, Xl, (areg_cas _ _ _ Cs), vok_vd, vv_vd, Bs1. apply andb_comm. }
      destruct (Nat.lt_ge_cases j pc) as [Jp|Jp]; [destruct D0; exfalso; pose proof (CONS_sp _ _ _ Co c); fold s0 in H; destruct C0 as (C00 & _); lia|].
      assert (PlH : forall k2 d2 k3 m3 xs3, placed p c cc pc (r (S m)) k2 d2 j -> hplaced p c cc pc (r (S m)) k3 m3 xs3 j -> False)
        by (intros; eapply (placed_hplaced p (f (S i)) R1 c); eauto).
      (* the pending access placed at j, if any *)
      destruct (pend_at p c cc pc N (r (S m)) j) as [k'|] eqn:Pa.
      + apply (pend_at_char_s p (f (S i)) c I1) in Pa. fold cc pc in Pa. destruct Pa as (d' & Pl).
        pose proof Pl as ((Ok' & Lk' & Ad') & t' & Ot' & Fk').
        destruct (is_load (inst_of d')) eqn:Ld.
        * destruct (K3 k' d' Pl Ld) as [Rc|V]; [left; exact Rc|]. right.
          split; [lia|]. split; [intros q Lq; rewrite Lm by lia; auto|]. split; [|split; [|split; [|split; [|split; [|split]]]]].
          -- intros q L1 L2 X. destruct (Nat.eq_dec q j) as [->|Nq].
             ++ exfalso. rewrite <- (dof_load _ _ _ (first_at_dof _ _ _ _ _ _ _ _ Fk' (load_accd _ Ld))) in Ld. congruence.
             ++ apply Old2; auto; lia.
          -- intros q k2 d2 L1 P2 L2. destruct (Nat.eq_dec q j) as [->|Nq].
             ++ assert (k2 = k') by (apply (placed_unique p c cc pc (oc_inj p (f (S i)) c I1) (r (S m)) j k2 k' d2 d'); auto).
                subst k2. destruct P2 as ((_ & _ & P3) & _). rewrite Ad' in P3. apply inst_of_inj in P3. subst d2. exact V.
             ++ apply (Old3 q k2 d2); auto; lia.
          -- intros q k2 m2 xs2 L1 P2. destruct (Nat.eq_dec q j) as [->|Nq]; [exfalso; apply (PlH k' d' k2 m2 xs2 Pl P2)|].
             apply (Old3h q k2 m2 xs2); auto; lia.
          -- intros q x b L1 L2 Bq Np Fb. destruct (Nat.eq_dec q j) as [->|Nq].
             ++ exfalso. apply Np. left. exists k', d'. auto.
             ++ apply Old4; auto; lia.
          -- intros q L1 L2 Np Cs Vr. destruct (Nat.eq_dec q j) as [->|Nq].
             ++ exfalso. apply Np. left. exists k', d'. auto.
             ++ apply Old5; auto; lia.
          -- intros q bq L1 L2 Np X Cs Fx. destruct (Nat.eq_dec q j) as [->|Nq]; [exfalso; apply (Np k' d' Pl)|apply (Old6 q bq); auto; lia].
          -- intros q L1 L2 Np Ic X. destruct (Nat.eq_dec q j) as [->|Nq]; [exfalso; apply Np; left; exists k', d'; auto|apply Old7; auto; lia].
        * (* a pending store placed at j: its register is 0 *)
          right. split; [lia|]. split; [intros q Lq; rewrite Lm by lia; auto|]. split; [|split; [|split; [|split; [|split; [|split]]]]].
          -- intros q L1 L2 X. destruct (Nat.eq_dec q j) as [->|Nq].
             ++ rewrite Rj. rewrite <- Ij in *. unfold xload. rewrite Ij in X |- *.
                destruct (ins_agree p W c j (r m) (r (S m)) Ar) as [_ E2]. rewrite <- (ieval_cond _ _ _ E2) in X. rewrite X. reflexivity.
             ++ apply Old2; auto; lia.
          -- intros q k2 d2 L1 P2 L2. destruct (Nat.eq_dec q j) as [->|Nq].
             ++ assert (k2 = k') by (apply (placed_unique p c cc pc (oc_inj p (f (S i)) c I1) (r (S m)) j k2 k' d2 d'); auto).
                subst k2. destruct P2 as ((_ & _ & P3) & _). rewrite Ad' in P3. apply inst_of_inj in P3. subst d2. congruence.
             ++ apply (Old3 q k2 d2); auto; lia.
          -- intros q k2 m2 xs2 L1 P2. destruct (Nat.eq_dec q j) as [->|Nq]; [exfalso; apply (PlH k' d' k2 m2 xs2 Pl P2)|].
             apply (Old3h q k2 m2 xs2); auto; lia.
          -- intros q x b L1 L2 Bq Np Fb. destruct (Nat.eq_dec q j) as [->|Nq].
             ++ exfalso. apply Np. left. exists k', d'. auto.
             ++ apply Old4; auto; lia.
          -- intros q L1 L2 Np Cs Vr. destruct (Nat.eq_dec q j) as [->|Nq].
             ++ exfalso. apply Np. left. exists k', d'. auto.
             ++ apply Old5; auto; lia.
          -- intros q bq L1 L2 Np X Cs Fx. destruct (Nat.eq_dec q j) as [->|Nq]; [exfalso; apply (Np k' d' Pl)|apply (Old6 q bq); auto; lia].
          -- intros q L1 L2 Np Ic X. destruct (Nat.eq_dec q j) as [->|Nq]; [exfalso; apply Np; left; exists k', d'; auto|apply Old7; auto; lia].
      + destruct (hpend_at p c cc pc N (r (S m)) j) as [k'|] eqn:Ph.
        * (* a CAS whose read happened alone placed at j *)
          apply (hpend_at_char_s p (f (S i)) c I1) in Ph. fold cc pc in Ph. destruct Ph as (m' & xs' & Pl).
          destruct (K3h k' m' xs' Pl) as [Rc|V]; [left; exact Rc|]. right.
          assert (Pnj : ~ exists k2 d2, placed p c cc pc (r (S m)) k2 d2 j).
          { apply (pend_at_none_s p (f (S i)) c I1). exact Pa. }
          split; [lia|]. split; [intros q Lq; rewrite Lm by lia; auto|]. split; [|split; [|split; [|split; [|split; [|split]]]]].
          -- intros q L1 L2 X. destruct (Nat.eq_dec q j) as [->|Nq].
             ++ exfalso. pose proof Pl as (_ & _ & t2 & _ & F2). pose proof (first_atR_eofR _ _ _ _ _ _ _ _ _ F2) as DR.
                destruct (ins p c j (r (S m))) as [m1 x1 c1|m1 x1 c1 v1|m2 x2 c2 e2 n2|f1|]; simpl in DR; try discriminate.
                unfold icond in X. simpl in X. destruct (c2 (r (S m))); [discriminate|discriminate].
             ++ apply Old2; auto; lia.
          -- intros q k2 d2 L1 P2 L2. destruct (Nat.eq_dec q j) as [->|Nq]; [exfalso; apply Pnj; eauto|].
             apply (Old3 q k2 d2); auto; lia.
          -- intros q k2 m2 xs2 L1 P2. destruct (Nat.eq_dec q j) as [->|Nq].
             ++ assert (k2 = k') by (apply (hplaced_unique p c cc pc (oh_inj p (f (S i)) c I1) (r (S m)) j k2 k' m2 m' xs2 xs'); auto).
                subst k2. exact V.
             ++ apply (Old3h q k2 m2 xs2); auto; lia.
          -- intros q x b L1 L2 Bq Np Fb. destruct (Nat.eq_dec q j) as [->|Nq].
             ++ exfalso. apply Np. right. exists k', m', xs'. auto.
             ++ apply Old4; auto; lia.
          -- intros q L1 L2 Np Cs Vr. destruct (Nat.eq_dec q j) as [->|Nq].
             ++ exfalso. apply Np. right. exists k', m', xs'. auto.
             ++ apply Old5; auto; lia.
          -- intros q bq L1 L2 Np X Cs Fx. destruct (Nat.eq_dec q j) as [->|Nq]; [apply (A6j bq); auto|apply (Old6 q bq); auto; lia].
          -- intros q L1 L2 Np Ic X. destruct (Nat.eq_dec q j) as [->|Nq]; [exfalso; apply Np; right; exists k', m', xs'; auto|apply Old7; auto; lia].
        * (* nothing pending at j *)
          assert (Npj : ~ pslot p c cc pc (r (S m)) j).
          { intros [X|X]; [apply (pend_at_none_s p (f (S i)) c I1) in Pa; exact (Pa X)|apply (hpend_at_none_s p (f (S i)) c I1) in Ph; exact (Ph X)]. }
          assert (V4 : RACY p \/ (forall x b, Bs j = true -> fbinder p c (r (S m)) j x = Some b ->
                         dec p c (r (S m)) j x = bvx p c (r (S m)) b x (dec p c (r (S m)) b x))).
          { destruct (Bs j) eqn:Bj; [|right; intros; discriminate].
            set (ok := fun x => match fbinder p c (r (S m)) j x with
                                | Some b => Nat.eqb (dec p c (r (S m)) j x) (bvx p c (r (S m)) b x (dec p c (r (S m)) b x))
                                | None => true end).
            destruct (forallb ok (icells (ins p c j (r (S m))))) eqn:FA.
            - right. intros x b _ Fb. pose proof (fbinder_shape _ _ _ _ _ _ Fb) as (_ & _ & _ & _ & _ & Ix).
              rewrite forallb_forall in FA. specialize (FA x Ix). unfold ok in FA. rewrite Fb in FA. apply Nat.eqb_eq. exact FA.
            - destruct (forallb_false ok _ FA) as (x & _ & Ox). unfold ok in Ox.
              destruct (fbinder p c (r (S m)) j x) as [b|] eqn:Fb; [|discriminate].
              destruct (K4 x b eq_refl Npj Fb) as [Rc|V]; [left; exact Rc|]. rewrite V, Nat.eqb_refl in Ox. discriminate. }
          destruct V4 as [Rc|V4]; [left; exact Rc|]. right.
          split; [lia|]. split; [intros q Lq; rewrite Lm by lia; auto|]. split; [|split; [|split; [|split; [|split; [|split]]]]].
          -- intros q L1 L2 X. destruct (Nat.eq_dec q j) as [->|Nq].
             ++ rewrite Rj. unfold xload. destruct (ins_agree p W c j (r m) (r (S m)) Ar) as [E1 E2].
                rewrite <- E1 in X. rewrite <- (ieval_cond _ _ _ E2) in X. rewrite X. reflexivity.
             ++ apply Old2; auto; lia.
          -- intros q k2 d2 L1 P2 L2. destruct (Nat.eq_dec q j) as [->|Nq].
             ++ exfalso. apply Npj. left. exists k2, d2. auto.
             ++ apply (Old3 q k2 d2); auto; lia.
          -- intros q k2 m2 xs2 L1 P2. destruct (Nat.eq_dec q j) as [->|Nq].
             ++ exfalso. apply Npj. right. exists k2, m2, xs2. auto.
             ++ apply (Old3h q k2 m2 xs2); auto; lia.
          -- intros q x b L1 L2 Bq Np Fb. destruct (Nat.eq_dec q j) as [->|Nq].
             ++ apply V4; auto.
             ++ apply Old4; auto; lia.
          -- intros q L1 L2 Np Cs Vr. destruct (Nat.eq_dec q j) as [->|Nq].
             ++ rewrite Ij in Cs |- *. rewrite (cexp_ieval _ _ _ Ej). rewrite Rj in Vr |- *.
                destruct (xload (ins p c j (r m)) (r m)) eqn:Xl.
                ** rewrite (areg_cas _ _ _ Cs) in Vr |- *. rewrite vok_vd in Vr. rewrite vv_vd.
                   apply andb_true_iff in Vr as [Vr _]. exact Vr.
                ** discriminate.
             ++ apply Old5; auto; lia.
          -- intros q bq L1 L2 Np X Cs Fx. destruct (Nat.eq_dec q j) as [->|Nq]; [apply (A6j bq); auto|apply (Old6 q bq); auto; lia].
          -- (* DQ C7 at j: the solo step read no cell *)
             intros q L1 L2 Np Ic X. destruct (Nat.eq_dec q j) as [->|Nq].
             ++ rewrite Ij in Ic, X |- *. rewrite (ieval_cond _ _ _ Ej) in X.
                assert (Xl : xload (ins p c j (r m)) (r m) = true) by (unfold xload; exact X).
                rewrite Rj, Xl, rval_areg, Ic. reflexivity.
             ++ apply Old7; auto; lia. }
  (* at the place *)
  set (ms := js - s0).
  destruct (IT ms ltac:(unfold ms; lia)) as [Rc|Cm]; [left; exact Rc|].
  right. right. destruct (Seg ms ltac:(unfold ms; lia) Cm) as (Com & Am).
  exists (fst (solo p bs g c ms)), (snd (solo p bs g c ms)). split; [apply solo_runs|]. split; [intros e I; apply (solo_x p bs g c ms e I)|].
  split; [exact Com|]. rewrite (solo_sp p W bs). fold s0. split; [|exact Cm].
  replace (s0 + ms) with js by (unfold ms; lia).
  apply (plc_agree p W c cc pc _ G _ Tt gt js); [|exact Fs].
  intros q Lq. symmetry. apply Am. unfold ms. lia.
Qed.

(* ---------- the base: facts about its events ---------- *)
Hypothesis Bgo : gordS sb lb.
Hypothesis Bco : cohS sb lb.
Hypothesis EVb : evok sb.

Lemma Rb : run p sb. Proof. apply (tr_run p f nb T). lia. Qed.
Lemma Ib1 : Inv1 p sb. Proof. apply Inv1_run. apply Rb. Qed.
Lemma Ib2 : Inv2 p sb. Proof. apply (proj2 (Inv2_run p sb Rb)). Qed.
Lemma Ib3 : Inv3 p sb. Proof. apply (I3 p sb Rb W). Qed.
Lemma IOb : InvO p sb. Proof. apply (iaoO p sb (InvO_run p sb Rb)). Qed.

(* a write's cells are its cells in the event graph *)
Lemma ew_eC : forall t E x, ent sb t = Some E -> ew E = true -> In x (icells (einstr p sb E)) -> In x (eC E).
Proof.
  intros t E x A Wt Ix. destruct (o_eRC p sb IOb _ E A) as [_ EC]. rewrite EC. unfold evC.
  destruct (j_ew p sb Ib2 _ E _ A eq_refl) as [W1 _]. rewrite Wt in W1. symmetry in W1.
  apply andb_prop in W1 as [W1 _]. apply andb_prop in W1 as [St Cd]. apply andb_prop in St as [_ St]. rewrite Cd, andb_true_r.
  destruct (einstr p sb E); simpl in St; try discriminate; exact Ix.
Qed.

Lemma lb_fa : forall c j, j < sp gb c -> j < pcs sb c -> sr gb c j = rrg sb c j.
Proof. intros c j _ L. apply Brg. auto. Qed.

Lemma lb_pass : forall q e, nth_error lb q = Some e -> sk e < pcs sb (sx e).
Proof. intros q e Q. destruct (srun_ev p W lb gb Bsr q e Q) as (_ & _ & L & _). rewrite Bsp in L. auto. Qed.

(* a sequential event that accesses comes from an instruction that executes *)
Lemma lb_exec : forall q e, nth_error lb q = Some e -> sacc e <> None ->
  executes (ins p (sx e) (sk e) (rrg sb (sx e))) (rrg sb (sx e)) = true.
Proof.
  intros q e Q N. pose proof (lb_pass q e Q) as P.
  pose proof (ev_faith p sb Rb W lb gb Bsr lb_fa q e Q P) as Sh.
  revert Sh. unfold executes. destruct (ins p (sx e) (sk e) (rrg sb (sx e))) as [m0 x0 c0|m0 x0 c0 v0|m0 x0 c0 e0 n0|f0|];
    intros Sh; unfold evshape in Sh; simpl; try reflexivity;
    unfold icond, ieval; simpl; destruct (c0 (rrg sb (sx e))); try reflexivity; exfalso; apply N;
    injection Sh as S1 _; exact S1.
Qed.

Lemma lb_ev : forall q e, nth_error lb q = Some e ->
  executes (ins p (sx e) (sk e) (rrg sb (sx e))) (rrg sb (sx e)) = true ->
  exists E, RE sb (sx e) (sk e) E /\ einstr p sb E = ins p (sx e) (sk e) (rrg sb (sx e)) /\
    sacc e = (if icond (ins p (sx e) (sk e) (rrg sb (sx e))) (rrg sb (sx e)) && isacc (ins p (sx e) (sk e) (rrg sb (sx e)))
              then Some (icells (ins p (sx e) (sk e) (rrg sb (sx e))), ew E)
              else None) /\
    sg e = xgop (ins p (sx e) (sk e) (rrg sb (sx e))) (rrg sb (sx e)).
Proof.
  intros q e Q Xe. pose proof (lb_pass q e Q) as P.
  destruct (n_ent p sb Rb W (sx e) (sk e) _ eq_refl P Xe) as (E & RE0 & Ei).
  exists E. split; [auto|]. split; [auto|].
  pose proof (ev_faith p sb Rb W lb gb Bsr lb_fa q e Q P) as Sh.
  destruct RE0 as (A & B & C).
  rewrite (ev_rel p sb Rb W (sx e) (sk e) _ E (insr_of p sb Rb W _ _ P) Xe A B C) in Sh.
  injection Sh as S1 S2. split; auto.
Qed.

(* a write of the base is a write of the run *)
Lemma lb_write : forall q e x, nth_error lb q = Some e -> writes_x e x = true ->
  exists E, RE sb (sx e) (sk e) E /\ ew E = true /\ In x (icells (einstr p sb E)) /\
    In (bt sb (sx e) (sk e)) (ids (hs sb x)) /\
    wv sb (bt sb (sx e) (sk e)) x = cval (icells (ins p (sx e) (sk e) (rrg sb (sx e)))) (wvals (ins p (sx e) (sk e) (rrg sb (sx e))) (rrg sb (sx e))) x.
Proof.
  intros q e x Q X.
  assert (Xe : executes (ins p (sx e) (sk e) (rrg sb (sx e))) (rrg sb (sx e)) = true).
  { apply (lb_exec q e Q). unfold writes_x in X. destruct (sacc e); [discriminate|discriminate X]. }
  destruct (lb_ev q e Q Xe) as (E & RE0 & Ei & Sa & _).
  unfold writes_x in X. rewrite Sa in X.
  destruct (icond _ _ && isacc _) eqn:Cd; [|discriminate].
  destruct (ew E) eqn:Ew; [|discriminate].
  apply existsb_exists in X. destruct X as (z & Iz & Z). apply Nat.eqb_eq in Z. subst z.
  destruct RE0 as (A & B & C).
  destruct (j_ew p sb Ib2 _ E _ A Ei) as [_ W2]. destruct (W2 Ew) as [V Hh].
  unfold rgof in V. rewrite B in V.
  exists E. split; [split; auto|]. split; [auto|]. split; [rewrite Ei; auto|]. split.
  - apply Hh. auto.
  - rewrite V. reflexivity.
Qed.

(* the value the base leaves in a cell it wrote last *)
Lemma sm_base : forall l g tau q w x, CONS l g tau -> lw l x = Some w -> nth_error l q = Some w -> q < length lb ->
  sm g x = wv sb (bt sb (sx w) (sk w)) x.
Proof.
  intros l g tau q w x Co Lw Q Lq.
  assert (Qb : nth_error lb q = Some w).
  { destruct Co as (F & E & _). subst l. rewrite nth_error_app1 in Q by auto. auto. }
  destruct (lw_spec l x w Lw) as (q' & Q' & X & _).
  destruct (lb_write q w x Qb X) as (E & _ & _ & _ & _ & V). rewrite V.
  destruct (proj2 (srun_mem p W l g (CONS_run _ _ _ Co) x) w Lw) as (i & Hi & M). rewrite M.
  pose proof (lb_pass q w Qb) as P.
  assert (Ag : forall j, j < sk w -> sr g (sx w) j = rrg sb (sx w) j) by (intros j L; apply (CONS_rg _ _ _ Co); lia).
  assert (Hi' : ins p (sx w) (sk w) (rrg sb (sx w)) = i) by (rewrite <- Hi; symmetry; apply wf_ins; auto).
  rewrite Hi'. rewrite (ieval_wvals i _ _ (wf_ieval p (sx w) (sk w) i _ _ W Hi Ag)). reflexivity.
Qed.

(* the step of an item is an event step *)
Lemma item_tm : forall c k i gt, item p f nb c k i gt -> tm (f (S i)) = S (tm (f i)).
Proof.
  intros c k i gt [(d & B & u & _ & Ea)|(xs & B & u & _ & Ea)].
  - destruct Ea as (_ & _ & _ & _ & _ & m' & a & K & w & _ & _ & _ & E). rewrite E. reflexivity.
  - destruct Ea as (_ & _ & _ & _ & _ & _ & m' & a & K & w & bv & _ & E). rewrite E. reflexivity.
Qed.

(* the item's entry *)
Lemma item_ent : forall c k i gt, item p f nb c k i gt ->
  exists e, ent (f (S i)) (tm (f i)) = Some e /\ ec e = c /\ ek e = k.
Proof.
  intros c k i gt [(d & B & u & _ & Ea)|(xs & B & u & _ & Ea)].
  - destruct Ea as (Li & _ & _ & _ & _ & m' & a & K & w & _ & _ & _ & E).
    assert (Ri : run p (f i)) by (apply (tr_run p f nb T); lia).
    rewrite E. unfold ent, searly, set_es, searly0, evs; simpl. rewrite (i_tm p (f i) (Inv1_run p (f i) Ri)).
    rewrite nth_error_app2, Nat.sub_diag by lia. simpl. eexists; split; [reflexivity|split; reflexivity].
  - destruct Ea as (Li & _ & _ & _ & _ & _ & m' & a & K & w & bv & _ & E).
    assert (Ri : run p (f i)) by (apply (tr_run p f nb T); lia).
    rewrite E. unfold ent, sread; simpl. rewrite (i_tm p (f i) (Inv1_run p (f i) Ri)).
    rewrite nth_error_app2, Nat.sub_diag by lia. simpl. eexists; split; [reflexivity|split; reflexivity].
Qed.

(* a slot of a pending read's context that the base passed and that is tied
   to the read happened before the read: passed before it happened, or the
   place of an access that happened before it *)
Lemma tied_before : forall l g tau c k i gt j0, CONS l g tau -> item p f nb c k i gt -> pcs sb c <= k ->
  plc p c (cs (f (S i)) c) (pcs (f (S i)) c) (sr g c) (S (tm (f i))) (tm (f i)) gt (sp g c) -> j0 < pcs sb c ->
  executes (ins p c j0 (rrg sb c)) (rrg sb c) = true -> tied (ins p c j0 (rrg sb c)) (tinst gt) ->
  bt sb c j0 < tm (f i).
Proof.
  intros l g tau c k i gt j0 Co It Pk Fpl L Ex Tt. pose proof (item_i p f nb c k i gt It) as Li.
  assert (R1 : run p (f (S i))) by (apply (tr_run p f nb T); lia).
  pose proof (Inv1_run p (f (S i)) R1) as I1.
  assert (X1b : Ext (f (S i)) sb) by (apply (tr_ext p f nb T); lia).
  assert (Ag : agree (sr g c) (rrg sb c) (pcs sb c)) by (intros q Lq; apply (CONS_rg _ _ _ Co); lia).
  assert (Tm : tm (f (S i)) = S (tm (f i))) by (apply (item_tm c k i gt It)).
  destruct (Nat.lt_ge_cases j0 (pcs (f (S i)) c)) as [Lj|Lj].
  - assert (Exf : executes (ins p c j0 (rg (cs (f (S i)) c))) (rg (cs (f (S i)) c)) = true).
    { rewrite (exec_agree p W c j0 (rg (cs (f (S i)) c)) (rrg sb c)); [exact Ex|].
      intros q Lq. unfold rrg, M2DQPComp.rrg. symmetry. apply (x_rg _ _ X1b). left. lia. }
    destruct (tmo_passed p (f (S i)) c j0 I1 Lj Exf) as (t0 & O & Lt).
    pose proof (x_tmo _ _ c j0 t0 X1b Lj O) as Ob.
    unfold bt. rewrite Ob.
    destruct (Nat.eq_dec t0 (tm (f i))) as [Et|Nt]; [|lia]. exfalso. subst t0.
    destruct (tmo_ent_s p (f (S i)) c j0 _ I1 O) as (e & E1 & C1 & K1).
    pose proof (item_ent c k i gt It) as (e' & E' & C' & K'). rewrite E1 in E'. injection E' as <-. lia.
  - (* the place of an earlier pending access, or of a CAS's read alone that failed *)
    assert (Aj : agree (sr g c) (rrg sb c) j0) by (apply (agree_le _ _ _ _ Ag); lia).
    assert (Agi : agree (sr g c) (rg (cs (f (S i)) c)) (pcs (f (S i)) c)).
    { intros q Lq. rewrite (Ag q) by (pose proof (x_pcs _ _ X1b c); lia). unfold rrg, M2DQPComp.rrg. apply (x_rg _ _ X1b). left; auto. }
    destruct (Nat.lt_ge_cases (bt sb c j0) (tm (f i))) as [Done|Ge]; [exact Done|exfalso].
    assert (HB : forall v, htakenv p c (cs (f (S i)) c) (pcs (f (S i)) c) (sr g c) (tm (f i)) j0 v ->
                 cfailv (ins p c j0 (sr g c)) (sr g c) v = false).
    { intros v (kh & th & mh & xh & Ph & Oh & Lth & Hl & Fh & Ev). destruct (cfailv (ins p c j0 (sr g c)) (sr g c) v) eqn:CF; [|reflexivity].
      exfalso. destruct (early_of_hpending p f nb T (S i) c kh th ltac:(lia) Oh) as (ih & xs & Bh & uh & Eah & Lih & Tih).
      assert (Itkh : item p f nb c kh ih (TH Plain xs)) by (right; exists xs, Bh, uh; auto).
      pose proof Ph as (Ph1 & _ & Ph3).
      destruct (early_pendingR p f nb T c kh ih xs Bh uh (S i) Eah ltac:(lia) ltac:(lia) Ph1) as (Ph' & _).
      pose proof Ph' as (_ & _ & Ph3'). rewrite Ph3 in Ph3'. injection Ph3' as -> ->. subst th.
      assert (Fo : first_atR p c (cs (f (S ih)) c) (pcs (f (S ih)) c) (sr g c) (tm (f ih)) Plain xs j0).
      { apply (place_trace p f nb T W Wc c kh ih (TH Plain xs) (S i) (sr g c) j0 Itkh ltac:(lia) ltac:(lia) Ph1 Agi Lj). exact Fh. }
      assert (Lkh : kh < pcs sb c).
      { destruct (Nat.lt_ge_cases kh (pcs sb c)) as [X|X]; auto. exfalso.
        pose proof (place_ge p f nb T W Wc c kh ih (TH Plain xs) nb (sr g c) j0 Itkh ltac:(lia) (le_n _) X Ag Fo). lia. }
      pose proof (passed_placeR p f nb T W Wc c kh ih xs Bh uh nb (sr g c) j0 Eah ltac:(lia) (le_n _) Lkh Ag Fo) as Ekh.
      subst kh. pose proof (x_oh _ _ X1b c j0 _ Oh) as Ohb.
      destruct (oc (cs sb c) j0) as [tw|] eqn:Ocb.
      - pose proof (i_hocf p sb Ib1 c j0 _ tw Ohb Ocb) as Hf.
        destruct (proj1 (i_cmA p sb Ib1 c j0) Lkh) as (tau0 & Tau). rewrite (proj2 (i_set p sb Ib1 c j0 tau0 Tau)) in Hf.
        unfold cfail in Hf. assert (Rv : rg (cs sb c) j0 = v) by (rewrite Ev; symmetry; apply (Ag j0); lia).
        rewrite Rv in Hf.
        rewrite <- (cfailv_agree p W c j0 (sr g c) (rg (cs sb c)) v Aj) in Hf. congruence.
      - unfold bt, tmo in Ge. rewrite Ocb, Ohb in Ge. lia. }
    assert (TB : taken p c (cs (f (S i)) c) (pcs (f (S i)) c) (sr g c) (tm (f i)) j0 -> bt sb c j0 < tm (f i)).
    2:{ apply (Nat.lt_irrefl (tm (f i))). eapply Nat.le_lt_trans; [exact Ge|]. apply TB.
        apply (plc_before _ _ _ _ _ _ _ _ Fpl j0 Lj).
        - pose proof (CONS_sp _ _ _ Co c). lia.
        - rewrite (exec_agree p W c j0 _ _ Aj). exact Ex.
        - exact HB.
        - rewrite (proj1 (ins_agree p W c j0 _ _ Aj)). exact Tt. }
    intros Tk. clear Ge HB.
    destruct Tk as (kz & tz & dz & (Pz1 & Pz2 & Pz3) & Oz & Lz & Fz).
    destruct (early_of_pending p f nb T (S i) c kz tz ltac:(lia) Pz1 Oz) as (iz & dz' & Bz & uz & Eaz & Liz & Tiz).
    destruct (early_post p f nb c kz iz dz' Bz uz Eaz) as (_ & Az1 & Pz1' & _).
    pose proof Eaz as (Liz' & Lkz0 & _).
    assert (Dq : dz' = dz).
    { destruct (pend_fate p f nb T (S iz) (S i) c kz dz' ltac:(lia) ltac:(lia) W ltac:(rewrite (proj1 (early_post p f nb c kz iz dz' Bz uz Eaz)); discriminate) ltac:(rewrite Pz1'; pose proof (x_pcs _ _ (tr_ext p f nb T (S iz) (S i) ltac:(lia) ltac:(lia)) c); lia) Az1)
        as [(_ & Aq)|(X1 & _)]; [|lia].
      rewrite Pz3 in Aq. apply inst_of_inj in Aq. auto. }
    subst dz'. rewrite <- Tiz in Fz.
    assert (Itz : item p f nb c kz iz (TF dz)) by (left; exists dz, Bz, uz; auto).
    assert (Fo : first_at p c (cs (f (S iz)) c) (pcs (f (S iz)) c) (sr g c) (tm (f iz)) dz j0).
    { apply (place_trace p f nb T W Wc c kz iz (TF dz) (S i) (sr g c) j0 Itz ltac:(lia) ltac:(lia) Pz1 Agi Lj). exact Fz. }
    assert (Lkz : kz < pcs sb c).
    { destruct (Nat.lt_ge_cases kz (pcs sb c)) as [X|X]; auto. exfalso.
      pose proof (place_ge p f nb T W Wc c kz iz (TF dz) nb (sr g c) j0 Itz ltac:(lia) (le_n _) X Ag Fo). lia. }
    pose proof (passed_place p f nb T W Wc c kz iz dz Bz uz nb (sr g c) j0 Eaz ltac:(lia) (le_n _) Lkz Ag Fo) as Ekz.
    subst j0. pose proof (x_oc _ _ X1b c kz tz Oz) as Ob. unfold bt, tmo. rewrite Ob. lia.
Qed.

(* what the read learnt from a base write it is synchronised with *)
Lemma know_base : forall l g tau c k i gt q w EW ER eR,
  CONS l g tau -> item p f nb c k i gt -> pcs sb c <= k ->
  plc p c (cs (f (S i)) c) (pcs (f (S i)) c) (sr g c) (S (tm (f i))) (tm (f i)) gt (sp g c) ->
  q < length lb -> nth_error l q = Some w -> (exists ys w0, sacc w = Some (ys, w0)) ->
  RE sb (sx w) (sk w) EW -> ent sb (tm (f i)) = Some ER -> ec ER = c -> xacc p sb ER -> sg eR = false ->
  sx w <> c -> gsync (l ++ [eR]) q (length l) (sx w) c -> vsub (esrc EW) (eQ ER).
Proof.
  intros l g tau c k i gt q w EW ER eR Co It Pk Fpl Lq Q Aw REW AR XR XaR GR Nc G.
  assert (Qb : nth_error lb q = Some w) by (destruct Co as (F & E & _); subst l; rewrite nth_error_app1 in Q by auto; auto).
  pose proof (lb_pass q w Qb) as Pw.
  destruct (lb_ev q w Qb ltac:(apply (lb_exec q w Qb); destruct Aw as (? & ? & Aw'); rewrite Aw'; discriminate))
    as (EW' & REW' & Eiw & Saw & Sgw).
  assert (EW' = EW) by (destruct REW as (A1 & _); destruct REW' as (A2 & _); congruence). subst EW'.
  destruct Aw as (ys & w0 & Aw). rewrite Aw in Saw.
  set (iw := ins p (sx w) (sk w) (rrg sb (sx w))) in *.
  destruct (icond iw (rrg sb (sx w)) && isacc iw) eqn:Cw; [|discriminate].
  apply andb_prop in Cw as [Cw1 Cw2].
  assert (Exw : executes iw (rrg sb (sx w)) = true) by (unfold executes; rewrite Cw2; exact Cw1).
  pose proof REW as (AW & XW & KW).
  destruct G as (a & b & f1 & f2 & La & Lab & Lb & F1 & F2 & S1 & S2 & X1 & X2).
  pose proof Co as (F & El & SF & GF & Gv).
  (* the guards are in the base *)
  assert (InB : forall z fz, nth_error (l ++ [eR]) z = Some fz -> sg fz = true -> z < length lb /\ nth_error lb z = Some fz).
  { intros z fz Z Sz. destruct (Nat.lt_ge_cases z (length l)) as [Lz|Lz].
    - rewrite nth_app_old' in Z by auto. rewrite El in Z, Lz.
      destruct (Nat.lt_ge_cases z (length lb)) as [Lz'|Lz'].
      + rewrite nth_error_app1 in Z by auto. auto.
      + exfalso. rewrite nth_error_app2 in Z by auto. apply nth_error_In in Z. rewrite (GF fz Z) in Sz. discriminate.
    - exfalso. assert (z = length l).
      { assert (z < length (l ++ [eR])) by (apply nth_error_Some; congruence). rewrite length_app in H. simpl in H. lia. }
      subst z. rewrite nth_app_last' in Z. injection Z as <-. congruence. }
  destruct (InB a f1 F1 S1) as [La' F1b]. destruct (InB b f2 F2 S2) as [Lb' F2b].
  assert (Nab : a <> b) by (intros ->; rewrite F1b in F2b; injection F2b as <-; congruence).
  assert (Qw : a <> q).
  { intros ->. rewrite Qb in F1b. injection F1b as <-. rewrite (acc_nog p lb gb q w _ _ W Bsr Qb Aw) in S1. discriminate. }
  (* w happened before the guard after it *)
  pose proof (lb_pass a f1 F1b) as P1. pose proof (lb_pass b f2 F2b) as P2.
  assert (Ff1 : ins p (sx f1) (sk f1) (rrg sb (sx f1)) = IFn FFull) by (apply (sg_ffull p sb Rb W lb gb Bsr lb_fa a f1 F1b P1 S1)).
  assert (Ff2 : ins p (sx f2) (sk f2) (rrg sb (sx f2)) = IFn FFull) by (apply (sg_ffull p sb Rb W lb gb Bsr lb_fa b f2 F2b P2 S2)).
  assert (Kw1 : sk w < sk f1) by (apply (srun_order p W lb gb Bsr q a w f1 ltac:(lia) Qb F1b); congruence).
  rewrite X1 in Ff1, P1. rewrite X2 in Ff2, P2.
  destruct (n_ent p sb Rb W (sx w) (sk f1) _ Ff1 P1 eq_refl) as (F1E & RF1 & EF1).
  destruct (n_ent p sb Rb W c (sk f2) _ Ff2 P2 eq_refl) as (F2E & RF2 & EF2).
  pose proof (tie_bt p sb Rb W (sx w) (sk w) (sk f1) iw (IFn FFull) Kw1 (insr_of p sb Rb W _ _ Pw)
                (eq_trans (insr_of p sb Rb W _ _ P1) (f_equal Some Ff1)) Exw eq_refl ltac:(right; right; left; reflexivity)) as Bt1.
  pose proof RF1 as (A1 & Xf1 & Kf1).
  destruct (k_Ppair p sb Ib3 _ EW _ F1E AW A1 ltac:(congruence) Bt1) as [_ St1].
  (* the two guards are in birth order *)
  assert (Lab' : a < b) by lia.
  pose proof (Bgo a b f1 f2 Lab' F1b F2b S1 S2 ltac:(congruence)) as Bg. rewrite X1, X2 in Bg.
  assert (G1 : xg p sb F1E) by (apply (n_xg p sb Rb W _ _ _ _ RF1 EF1); reflexivity).
  assert (G2 : xg p sb F2E) by (apply (n_xg p sb Rb W _ _ _ _ RF2 EF2); reflexivity).
  pose proof RF2 as (A2 & Xf2 & Kf2).
  destruct (k_Gpair p sb Ib3 _ F1E _ F2E A1 A2 G1 G2 Bg) as [K2 _].
  (* the guard before the read *)
  assert (Tt2 : tied (ins p c (sk f2) (rrg sb c)) (tinst gt)) by (rewrite Ff2; right; left; reflexivity).
  assert (Ex2 : executes (ins p c (sk f2) (rrg sb c)) (rrg sb c) = true) by (rewrite Ff2; reflexivity).
  pose proof (tied_before l g tau c k i gt (sk f2) Co It Pk Fpl P2 Ex2 Tt2) as L2.
  pose proof (o_gpair p sb IOb _ F2E _ ER A2 AR ltac:(congruence) L2 G2 XaR) as K3.
  intros v Hv. apply K3. apply K2. apply St1. exact Hv.
Qed.

(* an early access's place is after the next instruction of its step *)
Lemma own_lt' : forall cy ky iy dy By uy r j, early_at p f nb cy ky iy dy By uy ->
  (forall q, q < pcs sb cy -> r q = rg (cs sb cy) q) ->
  first_at p cy (cs (f (S iy)) cy) (pcs (f (S iy)) cy) r (tm (f iy)) dy j -> pcs (f (S iy)) cy < j.
Proof.
  intros cy ky iy dy By uy r j Ea Ag F. pose proof Ea as (Li & _).
  assert (Ri : run p (f iy)) by (apply (tr_run p f nb T); lia).
  pose proof (Inv1_run p (f iy) Ri) as Ii.
  assert (Xib : Ext (f iy) sb) by (apply (tr_ext p f nb T); lia).
  destruct (early_post p f nb cy ky iy dy By uy Ea) as (_ & _ & P1 & _). rewrite P1 in F |- *.
  apply (own_lt p f nb T W Wc cy ky iy dy By uy r j Ea); [|exact F].
  intros q Lq. rewrite Ag by (pose proof (x_pcs _ _ Xib cy); lia). apply (x_rg _ _ Xib). left. auto.
Qed.

(* an early access's place is not fenced on both sides *)
Lemma nofa_tf : forall l g tau cy ky iy dy By uy, CONS l g tau -> early_at p f nb cy ky iy dy By uy ->
  first_at p cy (cs (f (S iy)) cy) (pcs (f (S iy)) cy) (sr g cy) (tm (f iy)) dy (sp g cy) -> ~ fa p cy (sp g cy).
Proof.
  intros l g tau cy ky iy dy By uy Co Ea F (_ & Fa). destruct (Fa (sr g cy)) as [F1 _].
  pose proof (own_lt' cy ky iy dy By uy (sr g cy) (sp g cy) Ea (fun q Lq => CONS_rg _ _ _ Co cy q Lq) F) as L.
  unfold first_at in F.
  assert (Tk : taken p cy (cs (f (S iy)) cy) (pcs (f (S iy)) cy) (sr g cy) (tm (f iy)) (sp g cy - 1)).
  { apply (plc_before _ _ _ _ _ _ _ _ F (sp g cy - 1)); [lia|lia| | |].
    - rewrite F1. reflexivity.
    - intros v0 _. rewrite F1. reflexivity.
    - rewrite F1. right. left. reflexivity. }
  destruct (taken_dof _ _ _ _ _ _ _ Tk) as (d0 & D0). rewrite F1 in D0. discriminate.
Qed.


(* a pending write whose place the SC run has already passed, with no SC
   write of its cell beyond the base: a CAS that failed in the SC run *)
Lemma pend_passed : forall tau l g cy ky iy dy By uy Ey x j',
  HC (tm (f iy)) -> CONS l g tau ->
  early_at p f nb cy ky iy dy By uy -> pcs sb cy <= ky -> tm (f iy) < tau ->
  ent sb (tm (f iy)) = Some Ey -> ew Ey = true -> In x (icells (einstr p sb Ey)) ->
  (forall q e, length lb <= q -> nth_error l q = Some e -> sx e = cy -> sk e = j' -> writes_x e x = false) ->
  j' < sp g cy -> first_at p cy (cs (f (S iy)) cy) (pcs (f (S iy)) cy) (sr g cy) (tm (f iy)) dy j' ->
  RACY p.
Proof.
  intros tau l g cy ky iy dy By uy Ey x j' IH Co Eay Pky Lty AEy Wy Iy NoW Lj' Fj'.
  pose proof Eay as (Liy & _).
  assert (Ity : item p f nb cy ky iy (TF dy)) by (left; exists dy, By, uy; auto).
  destruct (early_pending p f nb T W cy ky iy dy By uy nb Eay Liy ltac:(lia) Pky) as (Py & Oy).
  destruct (i_oc p sb Ib1 cy ky _ Oy) as (Ey' & AEy' & Xy & Ky). rewrite AEy in AEy'. injection AEy' as <-.
  assert (Eiy : einstr p sb Ey = inst_of dy) by (unfold einstr; rewrite Xy, Ky; destruct Py as (_ & _ & P3); exact P3).
  rewrite Eiy in Iy.
  assert (Xin : existsb (Nat.eqb x) (icells (inst_of dy)) = true) by (apply existsb_exists; exists x; split; [exact Iy|apply Nat.eqb_refl]).
  destruct (j_ew p sb Ib2 _ Ey _ AEy Eiy) as [Ew _]. rewrite Wy in Ew. symmetry in Ew.
  apply andb_prop in Ew as [Ew1 Ew2]. apply andb_prop in Ew1 as [Ew1 _]. apply andb_prop in Ew1 as [Ehy Ew1].
  unfold rgof in Ew2. rewrite Xy in Ew2.
  (* the value the CAS compared, if it is one *)
  assert (Ew3 : is_cas (inst_of dy) = true -> rval (inst_of dy) (rg (cs sb cy) ky) = eval_e (inst_of dy) (rg (cs sb cy))).
  { intros Ca. rewrite Ca in Ew2. simpl in Ew2. rewrite andb_true_r in Ew2. apply Nat.eqb_eq in Ew2.
    destruct (j_val p sb Ib2 _ Ey _ AEy Eiy) as [V _]. unfold rgof in V. rewrite Xy, Ky in V.
    rewrite V; [exact Ew2|]. unfold xload. destruct dy; simpl in Ca; try discriminate; reflexivity. }
  (* its verdict: it wrote, so its bit is set *)
  assert (Vky : is_cas (inst_of dy) = true -> vok (rg (cs sb cy) ky) = true).
  { intros Ca. pose proof (j_ok p sb Ib2 _ Ey AEy) as J. rewrite Eiy, Xy, Ky, Wy in J.
    apply J; [apply negb_true_iff; exact Ehy|exact Ca|]. unfold xload. destruct dy; simpl in Ca; try discriminate; reflexivity. }
  (* the writer's place is already in l *)
  destruct (proj1 (srun_pos p W l g (CONS_run _ _ _ Co) cy j') Lj') as (q' & e' & Q' & X'' & K'').
  assert (Ge : pcs sb cy <= j').
  { apply (place_ge p f nb T W Wc cy ky iy (TF dy) nb (sr g cy) j' Ity ltac:(lia) (le_n _) Pky); [|exact Fj'].
    intros z Lz. apply (CONS_rg _ _ _ Co). auto. }
  assert (Lq : length lb <= q').
  { destruct (Nat.lt_ge_cases q' (length lb)) as [X1|X1]; auto. exfalso.
    pose proof Co as (F & El & _). rewrite El in Q'. rewrite nth_error_app1 in Q' by auto.
    pose proof (lb_pass q' e' Q') as P'. rewrite X'', K'' in P'. lia. }
  pose proof (NoW q' e' Lq Q' X'' K'') as Nw.
  destruct (srun_ev p W l g (CONS_run _ _ _ Co) q' e' Q') as (i' & Hi' & _ & Sh).
  rewrite X'', K'' in Hi', Sh. pose proof (first_at_dof _ _ _ _ _ _ _ _ Fj' ltac:(acc_tac)) as Dy. rewrite Hi' in Dy.
  pose proof (evshape_wflag i' (sr g cy) j' dy Dy Ew1) as Fl.
  assert (Sa : sacc e' = Some (icells (inst_of dy), negb (is_cas (inst_of dy)) || vok (sr g cy j')))
    by (rewrite <- Fl, <- Sh; reflexivity).
  unfold writes_x in Nw. rewrite Sa in Nw.
  destruct (negb (is_cas (inst_of dy)) || vok (sr g cy j')) eqn:Fw;
    [rewrite Xin in Nw; discriminate|].
  apply orb_false_iff in Fw as [Fw1 Fw2]. apply negb_false_iff in Fw1.
  pose proof (Ew3 Fw1) as Ew2'. pose proof (Vky Fw1) as Vk.
  assert (Ldy : is_load (inst_of dy) = true) by (destruct dy; simpl in *; congruence).
  (* the prefix up to the CAS *)
  destruct (CONS_prefix l g tau q' Co Lq ltac:(apply Nat.lt_le_incl; apply nth_error_Some; congruence)) as (gq & Coq & Sq).
  assert (Sk : skipn q' l = e' :: skipn (S q') l).
  { clear -Q'. revert q' Q'. induction l as [|a0 l IH]; intros [|q] Q; simpl in *; try discriminate.
    - injection Q as <-. reflexivity.
    - apply IH. auto. }
  rewrite Sk in Sq.
  destruct (nruns_head p bs _ _ _ Sq e' _ eq_refl) as (c0 & E0 & N1).
  assert (C0 : c0 = cy) by (rewrite <- X'', E0; symmetry; apply snext_x). subst c0.
  set (g1 := snd (snext p bs gq cy)) in *.
  assert (S2 : sruns p g1 (skipn (S q') l) g) by (apply (nruns_sruns p bs); exact N1).
  assert (St : sstep p gq e' g1) by (rewrite E0; apply snext_step).
  destruct (sstep_shape p W _ _ _ St) as (i2 & Hi2 & _ & Hk2 & Hsp2 & Hr2 & Hrk2 & _).
  rewrite X'', K'' in Hi2, Hk2, Hrk2.
  assert (Spg1 : j' < sp g1 cy) by (rewrite Hsp2, X''; unfold upd; rewrite Nat.eqb_refl; lia).
  assert (Agq : agree (sr gq cy) (sr g cy) j').
  { intros z Lz. rewrite (sruns_regs p W _ _ _ S2 cy z) by lia. symmetry. apply Hr2. right. lia. }
  assert (Agq' : agree (sr g cy) (sr gq cy) j') by (intros z Lz; symmetry; apply Agq; auto).
  assert (Hi2' : i2 = i').
  { rewrite <- Hi2, <- Hi'. symmetry. apply (proj1 (ins_agree p W cy j' (sr g cy) (sr gq cy) Agq')). }
  rewrite Hi2' in Hi2, Hrk2.
  (* the registers continue the state after the write's step *)
  assert (Cq : ccJ p cy (cs (f (S iy)) cy) (pcs (f (S iy)) cy) (bd (cs (f (S iy)) cy)) (sr gq cy) j').
  { pose proof Co as (F0 & _ & _ & _ & Gv0). destruct (Gv0 cy) as (ig & Lig & Tig & Cg).
    assert (Liyg : iy < ig) by (apply (tr_tm_lt p f nb T); lia).
    apply (ccJ_agree_r p cy _ _ _ (sr g cy) (sr gq cy) j' W Agq').
    apply (ccJ_le _ _ _ _ _ _ (sp g cy)); [apply (mono_tr p f nb T W Wc cy (sr g cy) (sp g cy) (S iy) ig ltac:(lia) Lig Cg)| |lia].
    apply (first_at_le _ _ _ _ _ _ _ _ Fj'). }
  apply (IH (firstn q' l) gq cy ky iy (TF dy) (CONS_mono (firstn q' l) gq tau (tm (f iy)) ltac:(lia) Coq) Ity Pky ltac:(lia) Ldy).
  + rewrite <- Hk2. apply (first_at_agree p W cy _ _ (sr g cy) (sr gq cy) _ _ j' Agq' Fj').
  + apply (nofa_tf _ _ _ cy ky iy dy By uy Coq Eay). rewrite <- Hk2. apply (first_at_agree p W cy _ _ (sr g cy) (sr gq cy) _ _ j' Agq' Fj').
  + rewrite <- Hk2. exact Cq.
  + (* the SC value is not the value the CAS expected *)
    assert (Xl : xload i' (sr gq cy) = true).
    { unfold xload. destruct (dof_shape _ _ _ Dy) as (_ & _ & Q3 & _ & _ & Q6 & Q7).
      rewrite Q3, Ldy. simpl.
      rewrite <- (ieval_cond i' (sr g cy) (sr gq cy)); [exact Q6|].
      rewrite <- Hi'. apply (proj2 (ins_agree p W cy j' (sr g cy) (sr gq cy) Agq')). }
    assert (Bs1 : bs gq cy = true).
    { destruct (fxv p f nb cy j' (sr gq cy)) as [bx|] eqn:Fv.
      { assert (Fq : first_at p cy (cs (f (S iy)) cy) (pcs (f (S iy)) cy) (sr gq cy) (tm (f iy)) dy j')
          by (apply (first_at_agree p W cy _ _ (sr g cy) (sr gq cy) _ _ j' Agq' Fj')).
        pose proof (fix_whole p f nb T W Wc cy ky iy dy By uy (sr gq cy) j' bx Eay Cq Fq Pky Fw1 Fv) as V.
        destruct (early_post p f nb cy ky iy dy By uy Eay) as (Oky & _).
        rewrite <- (x_rg _ _ (tr_ext p f nb T (S iy) nb ltac:(lia) (le_n _)) cy ky ltac:(right; rewrite Oky; discriminate)), Vk in V.
        unfold bs. rewrite <- Hk2. replace (Nat.ltb j' (pcs (f nb) cy)) with false by (symmetry; apply Nat.ltb_ge; exact Ge). rewrite Fv.
        destruct bx; [reflexivity|simpl in V; discriminate]. }
      unfold bs. rewrite <- Hk2. replace (Nat.ltb j' (pcs (f nb) cy)) with false by (symmetry; apply Nat.ltb_ge; exact Ge).
      rewrite Fv.
      assert (Pkb : pend_at p cy (cs sb cy) (pcs sb cy) (tp sb cy) (sr gq cy) j' = Some ky).
      { apply (pend_at_char_s p sb cy (Inv1_run p sb (tr_run p f nb T nb (le_n _)))). exists dy. split; [exact Py|].
        exists (tm (f iy)). split; [exact Oy|]. unfold first_at.
        apply (proj2 (place_trace p f nb T W Wc cy ky iy (TF dy) nb (sr gq cy) j' Ity ltac:(lia) (le_n _) Pky
          ltac:(intros z Lz; apply (CONS_rg _ _ _ Coq); exact Lz) Ge)).
        apply (first_at_agree p W cy _ _ (sr g cy) (sr gq cy) _ _ j' Agq' Fj'). }
      rewrite Pkb. exact Vk. }
    (* the SC CAS failed: its verdict bit is clear *)
    assert (Rb : vok (sr g1 cy j') = false).
    { rewrite <- (sruns_regs p W _ _ _ S2 cy j' Spg1). exact Fw2. }
    unfold g1 in Rb. rewrite Hk2 in Rb. rewrite snext_reg in Rb. cbv zeta in Rb. rewrite <- Hk2 in Rb.
    destruct (eof_cexp _ _ _ (rg (cs sb cy)) (dof_eof _ _ _ Dy)) as (Csd & Ced).
    rewrite Hi2, Xl, Bs1, andb_true_r in Rb. rewrite (areg_cas _ _ _ ltac:(rewrite <- Csd; exact Fw1)) in Rb.
    rewrite vok_vd in Rb. apply Nat.eqb_neq in Rb.
    destruct (dof_shape _ _ _ Dy) as (Q1 & _).
    intros Z. apply Rb. cbn [tinst] in Z. rewrite Q1, Z, (rval_cas _ _ Fw1).
    rewrite (rval_cas _ _ Fw1) in Ew2'. rewrite Ew2'. change (cexp (inst_of dy) (rg (cs sb cy)) = cexp i' (sr gq cy)).
    rewrite Ced. apply cexp_ieval. rewrite <- Hi'. apply (proj2 (ins_agree p W cy j' (sr g cy) (sr gq cy) Agq')).
Qed.

(* a pending write whose context, run forward alone, reaches its place, while
   another context waits at a read of the cell: they race *)
Lemma pend_reached : forall tau l g c d x cy ky iy dy By uy Ey F' g',
  HC (tm (f iy)) -> CONS l g tau -> dof (ins p c (sp g c) (sr g c)) (sr g c) = Some d -> cy <> c ->
  In x (icells (inst_of d)) ->
  early_at p f nb cy ky iy dy By uy -> pcs sb cy <= ky -> tm (f iy) < tau ->
  ent sb (tm (f iy)) = Some Ey -> ew Ey = true -> In x (icells (einstr p sb Ey)) ->
  sruns p g F' g' -> (forall e, In e F' -> sx e = cy) -> CONS (l ++ F') g' (tm (f iy)) ->
  first_at p cy (cs (f (S iy)) cy) (pcs (f (S iy)) cy) (sr g' cy) (tm (f iy)) dy (sp g' cy) ->
  ccJ p cy (cs (f (S iy)) cy) (pcs (f (S iy)) cy) (bd (cs (f (S iy)) cy)) (sr g' cy) (sp g' cy) ->
  RACY p.
Proof.
  intros tau l g c d x cy ky iy dy By uy Ey F' g' IH Co Dd Nc Ixd Eay Pky Lty AEy Wy Iy S' X' Co' Fp Cg'.
  pose proof Eay as (Liy & _).
  assert (Ity : item p f nb cy ky iy (TF dy)) by (left; exists dy, By, uy; auto).
  destruct (early_pending p f nb T W cy ky iy dy By uy nb Eay Liy ltac:(lia) Pky) as (Py & Oy).
  destruct (i_oc p sb Ib1 cy ky _ Oy) as (Ey' & AEy' & Xy & Ky). rewrite AEy in AEy'. injection AEy' as <-.
  assert (Eiy : einstr p sb Ey = inst_of dy) by (unfold einstr; rewrite Xy, Ky; destruct Py as (_ & _ & P3); exact P3).
  rewrite Eiy in Iy.
  assert (Xin : existsb (Nat.eqb x) (icells (inst_of dy)) = true) by (apply existsb_exists; exists x; split; [exact Iy|apply Nat.eqb_refl]).
  destruct (j_ew p sb Ib2 _ Ey _ AEy Eiy) as [Ew _]. rewrite Wy in Ew. symmetry in Ew.
  apply andb_prop in Ew as [Ew1 Ew2]. apply andb_prop in Ew1 as [Ew1 _]. apply andb_prop in Ew1 as [Ehy Ew1].
  unfold rgof in Ew2. rewrite Xy in Ew2.
  (* the value the CAS compared, if it is one *)
  assert (Ew3 : is_cas (inst_of dy) = true -> rval (inst_of dy) (rg (cs sb cy) ky) = eval_e (inst_of dy) (rg (cs sb cy))).
  { intros Ca. rewrite Ca in Ew2. simpl in Ew2. rewrite andb_true_r in Ew2. apply Nat.eqb_eq in Ew2.
    destruct (j_val p sb Ib2 _ Ey _ AEy Eiy) as [V _]. unfold rgof in V. rewrite Xy, Ky in V.
    rewrite V; [exact Ew2|]. unfold xload. destruct dy; simpl in Ca; try discriminate; reflexivity. }
  (* its verdict: it wrote, so its bit is set *)
  assert (Vky : is_cas (inst_of dy) = true -> vok (rg (cs sb cy) ky) = true).
  { intros Ca. pose proof (j_ok p sb Ib2 _ Ey AEy) as J. rewrite Eiy, Xy, Ky, Wy in J.
    apply J; [apply negb_true_iff; exact Ehy|exact Ca|]. unfold xload. destruct dy; simpl in Ca; try discriminate; reflexivity. }
  (* the writer reaches its place *)
  set (jy := sp g' cy) in *. set (ry := sr g' cy) in *.
  pose proof (first_at_dof _ _ _ _ _ _ _ _ Fp ltac:(acc_tac)) as Dy. fold jy ry in Dy.
  set (ey := fst (snext p bs g' cy)). set (g2 := snd (snext p bs g' cy)).
  assert (Sty : sstep p g' ey g2) by apply snext_step.
  assert (Xey : sx ey = cy) by apply snext_x.
  pose proof (snext_wflag p bs g' cy dy Dy Ew1) as Say. fold ey in Say.
  destruct (negb (is_cas (inst_of dy)) || (Nat.eqb (enc (map (sm g') (icells (inst_of dy)))) (eval_e (inst_of dy) ry) && bs g' cy)) eqn:Fl.
  2:{ (* a CAS that takes another value than in the run diverges *)
    apply orb_false_iff in Fl as [Fl1 Fl2]. apply negb_false_iff in Fl1.
    pose proof (Ew3 Fl1) as Ew2'. pose proof (Vky Fl1) as Vk.
    assert (Ge : pcs sb cy <= jy).
    { apply (place_ge p f nb T W Wc cy ky iy (TF dy) nb ry jy Ity ltac:(lia) (le_n _) Pky); [|exact Fp].
      intros z Lz. apply (CONS_rg _ _ _ Co'). auto. }
    assert (Bs1 : bs g' cy = true).
    { destruct (fxv p f nb cy jy ry) as [bx|] eqn:Fv.
      { pose proof (fix_whole p f nb T W Wc cy ky iy dy By uy ry jy bx Eay Cg' Fp Pky Fl1 Fv) as V.
        destruct (early_post p f nb cy ky iy dy By uy Eay) as (Oky & _).
        rewrite <- (x_rg _ _ (tr_ext p f nb T (S iy) nb ltac:(lia) (le_n _)) cy ky ltac:(right; rewrite Oky; discriminate)), Vk in V.
        unfold bs. cbv beta zeta. fold jy ry. replace (Nat.ltb jy (pcs (f nb) cy)) with false by (symmetry; apply Nat.ltb_ge; exact Ge).
        rewrite Fv. destruct bx; [reflexivity|simpl in V; discriminate]. }
      unfold bs. cbv beta zeta. fold jy ry. replace (Nat.ltb jy (pcs (f nb) cy)) with false by (symmetry; apply Nat.ltb_ge; exact Ge).
      rewrite Fv.
      assert (Pkb : pend_at p cy (cs sb cy) (pcs sb cy) (tp sb cy) ry jy = Some ky).
      { apply (pend_at_char_s p sb cy (Inv1_run p sb (tr_run p f nb T nb (le_n _)))). exists dy. split; [exact Py|].
        exists (tm (f iy)). split; [exact Oy|]. unfold first_at.
        apply (proj2 (place_trace p f nb T W Wc cy ky iy (TF dy) nb ry jy Ity ltac:(lia) (le_n _) Pky
          ltac:(intros z Lz; apply (CONS_rg _ _ _ Co'); exact Lz) Ge)).
        exact Fp. }
      rewrite Pkb. exact Vk. }
    rewrite Bs1, andb_true_r in Fl2.
    assert (Ldy : is_load (inst_of dy) = true) by (destruct dy; simpl in *; congruence).
    apply (IH (l ++ F') g' cy ky iy (TF dy) Co' Ity Pky ltac:(lia) Ldy Fp (nofa_tf _ _ _ cy ky iy dy By uy Co' Eay Fp) Cg').
    intros Z. cbn [tinst] in Z. rewrite Z, Ew2' in Fl2.
    rewrite (ieval_e (inst_of dy) (rg (cs sb cy)) ry (ieval_inst dy _ _)), Nat.eqb_refl in Fl2. discriminate. }
  (* the read, still at its place *)
  assert (Oc : sp g2 c = sp g c /\ forall z, sr g2 c z = sr g c z).
  { assert (Sa : sruns p g (F' ++ [ey]) g2) by (econstructor; eauto).
    apply (sruns_other p W _ _ _ c Sa). intros e I. apply in_app_or in I. destruct I as [I|[<-|[]]].
    - rewrite (X' e I). auto.
    - rewrite Xey. auto. }
  destruct Oc as [Osp Osr].
  set (eS := fst (snext p bs g2 c)). set (gR := snd (snext p bs g2 c)).
  assert (StR : sstep p g2 eS gR) by apply snext_step.
  assert (XR : sx eS = c) by apply snext_x.
  assert (Dd2 : dof (ins p c (sp g2 c) (sr g2 c)) (sr g2 c) = Some d).
  { rewrite Osp. rewrite <- (dof_agree p W c (sp g c) (sr g c) (sr g2 c)); [exact Dd|intros z _; symmetry; apply Osr]. }
  destruct (snext_acc p bs g2 c d Dd2) as (wR & AR & GR). fold eS in AR, GR.
  assert (Gy : sg ey = false) by (destruct (snext_acc p bs g' cy dy Dy) as (? & _ & G0); exact G0).
  set (l2 := ((l ++ F') ++ [ey]) ++ [eS]).
  assert (Lx : length ((l ++ F') ++ [ey]) = S (length (l ++ F'))) by (rewrite (length_app (l ++ F') [ey]); simpl; lia).
  assert (R2 : srun p l2 gR) by (unfold l2; econstructor; [econstructor; [apply (CONS_run _ _ _ Co')|exact Sty]|exact StR]).
  exists l2, gR. split; [exact R2|].
  apply (racy_g_mk p l2 (length (l ++ F')) (length ((l ++ F') ++ [ey])) ey eS x (icells (inst_of dy)) (icells (inst_of d)) true wR).
  + rewrite (length_app (l ++ F') [ey]). simpl. lia.
  + unfold l2. rewrite nth_app_old' by (rewrite (length_app (l ++ F') [ey]); simpl; lia). apply nth_app_last'.
  + unfold l2. apply nth_app_last'.
  + congruence.
  + rewrite Say. unfold ry in Fl. rewrite Fl. reflexivity.
  + exact AR.
  + exact Iy.
  + exact Ixd.
  + reflexivity.
  + intros (a & b & f1 & f2 & L1 & L2 & L3 & F1 & F2 & S1 & S2 & _ & _).
    assert (Ha : a = length (l ++ F') \/ a = length ((l ++ F') ++ [ey])) by lia.
    destruct Ha as [Eqa|Eqa]; subst a.
    * unfold l2 in F1. rewrite nth_app_old' in F1 by lia. rewrite nth_app_last' in F1.
      injection F1 as <-. congruence.
    * unfold l2 in F1. rewrite nth_app_last' in F1. injection F1 as <-. congruence.
  + intros ((_ & Fa) & _). rewrite Xey in Fa.
    destruct (sstep_shape p W _ _ _ Sty) as (? & _ & _ & Hk & _). rewrite Xey in Hk. rewrite Hk in Fa. fold jy in Fa.
    destruct (Fa ry) as [F1 _].
    assert (Pp : pcs (f (S iy)) cy < jy) by (apply (own_lt' cy ky iy dy By uy ry jy Eay); [intros q Lq; apply (CONS_rg _ _ _ Co' cy q Lq)|exact Fp]).
    assert (Tk : taken p cy (cs (f (S iy)) cy) (pcs (f (S iy)) cy) ry (tm (f iy)) (jy - 1)).
    { apply (first_at_before _ _ _ _ _ _ _ _ Fp (jy - 1)); [lia|lia| | |].
      - fold jy ry. rewrite F1. reflexivity.
      - intros v0 _. fold jy ry. rewrite F1. reflexivity.
      - fold jy ry. rewrite F1. right. left. reflexivity. }
    destruct (taken_dof _ _ _ _ _ _ _ Tk) as (d0 & D0). fold jy ry in D0. rewrite F1 in D0. discriminate.
Qed.

(* a pending write, with no later SC write of its cell: run its context
   forward to it and meet an access of another context to the cell *)
Lemma pend_meet : forall tau l g c d x cy ky iy dy By uy Ey,
  HC (tm (f iy)) -> CONS l g tau -> dof (ins p c (sp g c) (sr g c)) (sr g c) = Some d -> cy <> c ->
  In x (icells (inst_of d)) ->
  early_at p f nb cy ky iy dy By uy -> pcs sb cy <= ky -> tm (f iy) < tau ->
  ent sb (tm (f iy)) = Some Ey -> ew Ey = true -> In x (icells (einstr p sb Ey)) ->
  (forall q e, length lb <= q -> nth_error l q = Some e -> writes_x e x = false) ->
  RACY p.
Proof.
  intros tau l g c d x cy ky iy dy By uy Ey IH Co Dd Nc Ixd Eay Pky Lty AEy Wy Iy NoW.
  pose proof Eay as (Liy & _).
  destruct (early_pending p f nb T W cy ky iy dy By uy nb Eay Liy ltac:(lia) Pky) as (Py & Oy).
  destruct (i_oc p sb Ib1 cy ky _ Oy) as (Ey' & AEy' & Xy & Ky). rewrite AEy in AEy'. injection AEy' as <-.
  assert (Eiy : einstr p sb Ey = inst_of dy) by (unfold einstr; rewrite Xy, Ky; destruct Py as (_ & _ & P3); exact P3).
  rewrite Eiy in Iy.
  assert (Xin : existsb (Nat.eqb x) (icells (inst_of dy)) = true) by (apply existsb_exists; exists x; split; [exact Iy|apply Nat.eqb_refl]).
  assert (Ity : item p f nb cy ky iy (TF dy)) by (left; exists dy, By, uy; auto).
  destruct (fwd l g tau cy ky iy (TF dy) IH Co Ity Pky ltac:(lia)) as [Rc|[(j' & Lj' & Fj')|(F' & g' & S' & X' & Co' & Fp & Cg')]].
  - exact Rc.
  - (* the writer's place is already in l *)
    apply (pend_passed tau l g cy ky iy dy By uy Ey x j' IH Co Eay Pky Lty AEy Wy ltac:(rewrite Eiy; exact Iy) (fun q e L Q _ _ => NoW q e L Q) Lj' Fj').
  - (* the writer reaches its place *)
    apply (pend_reached tau l g c d x cy ky iy dy By uy Ey F' g' IH Co Dd Nc Ixd Eay Pky Lty AEy Wy ltac:(rewrite Eiy; exact Iy) S' X' Co' Fp Cg').
Qed.

(* the read item's place, reached by an SC run of its context: a CAS whose
   read took that place earlier, and is live at the write's time, wrote at
   the item's time, and the replay's verdict there is its success *)
Lemma fx_read : forall l g tau l' g' tau' c k i gt iy,
  CONS l g tau -> CONS l' g' tau' -> item p f nb c k i gt -> pcs sb c <= k -> tm (f i) <= tau ->
  tm (f iy) < tm (f i) -> iy < nb -> agree (sr g c) (sr g' c) (sp g c) -> sp g c < sp g' c ->
  agree (sr g' c) (rg (cs (f (S i)) c)) (pcs (f (S i)) c) ->
  ccJ p c (cs (f (S iy)) c) (pcs (f (S iy)) c) (bd (cs (f (S iy)) c)) (sr g' c) (sp g' c) ->
  plc p c (cs (f (S i)) c) (pcs (f (S i)) c) (sr g' c) (S (tm (f i))) (tm (f i)) gt (sp g c) ->
  ccJ p c (cs (f (S i)) c) (pcs (f (S i)) c) (bd (cs (f (S i)) c)) (sr g c) (sp g c) ->
  forall v, htakenv p c (cs (f (S i)) c) (pcs (f (S i)) c) (sr g' c) (tm (f iy)) (sp g c) v ->
    cfailv (ins p c (sp g c) (sr g' c)) (sr g' c) v = false.
Proof.
  intros l g tau l' g' tau' c k i gt iy Co Co' It Pk Lt Lty Lyn Agd Ljs Ag' Cg' Fd Cj.
  pose proof (item_i p f nb c k i gt It) as Li.
  assert (Liy : iy < i) by (apply (tr_tm_lt p f nb T); lia).
  assert (R1 : run p (f (S i))) by (apply (tr_run p f nb T); lia).
  pose proof (Inv1_run p (f (S i)) R1) as I1.
  assert (X1b : Ext (f (S i)) sb) by (apply (tr_ext p f nb T); lia).
  assert (Ab : agree (sr g' c) (rg (cs sb c)) (pcs sb c)) by (intros q Lq; apply (CONS_rg _ _ _ Co'); exact Lq).
  set (r' := sr g' c) in *. set (jd := sp g c) in *.
  intros v (kh & th & mh & xh & Ph & Oh & Lth & Hl & Fh & Ev). subst v.
  destruct (cfailv (ins p c jd r') r' (r' jd)) eqn:CF; [|reflexivity]. exfalso.
  destruct (oc (cs (f (S i)) c) kh) as [tw|] eqn:Ow.
  2:{ apply (plc_hfree _ _ _ _ _ _ _ _ Fd). exists kh, th, mh, xh. split; [exact Ph|]. split; [exact Oh|].
      split; [lia|]. split; [intros t2 E; congruence|exact Fh]. }
  destruct (Nat.lt_ge_cases (tm (f i)) tw) as [Gw|Lw].
  { apply (plc_hfree _ _ _ _ _ _ _ _ Fd). exists kh, th, mh, xh. split; [exact Ph|]. split; [exact Oh|].
    split; [lia|]. split; [intros t2 E; rewrite Ow in E; injection E as <-; exact Gw|exact Fh]. }
  (* the CAS's read *)
  destruct (early_of_hpending p f nb T (S i) c kh th ltac:(lia) Oh) as (ih & xs & Bh & uh & Eah & Lih & Tih).
  assert (Itkh : item p f nb c kh ih (TH Plain xs)) by (right; exists xs, Bh, uh; auto).
  pose proof Ph as (Ph1 & _ & Ph3).
  destruct (early_pendingR p f nb T c kh ih xs Bh uh (S i) Eah ltac:(lia) ltac:(lia) Ph1) as (Ph' & _).
  pose proof Ph' as (_ & _ & Ph3'). rewrite Ph3 in Ph3'. injection Ph3' as -> ->. subst th.
  assert (Lhy : ih < iy) by (apply (tr_tm_lt p f nb T); lia).
  pose proof (first_atR_le _ _ _ _ _ _ _ _ _ Fh) as Lpj.
  assert (Fo : first_atR p c (cs (f (S ih)) c) (pcs (f (S ih)) c) r' (tm (f ih)) Plain xs jd).
  { apply (place_trace p f nb T W Wc c kh ih (TH Plain xs) (S i) r' jd Itkh ltac:(lia) ltac:(lia) Ph1 Ag' Lpj). exact Fh. }
  destruct (Nat.eq_dec tw (tm (f i))) as [Ew|Nw].
  - (* the read item is that write *)
    subst tw. destruct (i_oc p (f (S i)) I1 c kh _ Ow) as (e1 & E1 & C1 & K1).
    destruct (item_ent c k i gt It) as (e2 & E2 & C2 & K2). rewrite E1 in E2. injection E2 as <-.
    assert (Ek : kh = k) by congruence. clear K1 K2. subst kh.
    destruct It as [(d0 & B0 & u0 & -> & Ea0)|(xs0 & B0 & u0 & -> & Ea0)].
    2:{ destruct (early_postR p f nb c k i xs0 B0 u0 Ea0) as (Oh0 & _). rewrite Oh in Oh0. injection Oh0 as E0. lia. }
    assert (It : item p f nb c k i (TF d0)) by (left; exists d0, B0, u0; auto).
    destruct (early_post p f nb c k i d0 B0 u0 Ea0) as (_ & A0 & _).
    pose proof (i_hocf p (f (S i)) I1 c k (tm (f ih)) (tm (f i)) Oh Ow) as Hf. rewrite A0 in Hf. unfold cfail in Hf.
    assert (Cd : is_cas (inst_of d0) = true) by (rewrite A0 in Ph3; destruct d0; simpl in Ph3; try discriminate; reflexivity).
    (* the model's verdict: a success, at its expected value *)
    assert (Hv : vok (rg (cs (f (S i)) c) k) = true /\ forall r0, vv (rg (cs (f (S i)) c) k) = cexp (inst_of d0) r0).
    { clear -Hf Cd. destruct d0; simpl in Cd; try discriminate. unfold cfailv in Hf. simpl in Hf |- *.
      destruct (vok (rg (cs (f (S i)) c) k)); simpl in Hf; [|discriminate]. split; [reflexivity|].
      intros _. apply negb_false_iff in Hf. apply Nat.eqb_eq in Hf. exact Hf. }
    pose proof (plc_tat _ _ _ _ _ _ _ _ Fd) as D. cbn [tatp] in D.
    destruct (eof_cexp _ _ _ r' D) as (Csd & Ced).
    assert (Cs : is_cas (ins p c jd r') = true) by (rewrite <- Csd; exact Cd).
    assert (Xl : xload (ins p c jd r') r' = true).
    { clear -D Cs. revert D Cs. destruct (ins p c jd r') as [m1 x1 c1|m1 x1 c1 v1|m2 x2 c2 e2 n2|f1|]; intros D Cs;
        simpl in Cs; try discriminate. unfold xload, icond. simpl in D |- *. destruct (c2 r'); [reflexivity|discriminate]. }
    (* the replay read the model's value there *)
    assert (Vv : vv (r' jd) = vv (rg (cs (f (S i)) c) k)).
    { assert (Xyi : Ext (f (S iy)) (f (S i))) by (apply (tr_ext p f nb T); lia).
      assert (Xhy : Ext (f (S ih)) (f (S iy))) by (apply (tr_ext p f nb T); lia).
      destruct (early_postR p f nb c k ih xs Bh uh Eah) as (Oh1 & _).
      pose proof (x_oh _ _ Xhy c k _ Oh1) as Ohy.
      assert (Ocy : oc (cs (f (S iy)) c) k = None).
      { destruct (oc (cs (f (S iy)) c) k) as [y|] eqn:Oy; [|reflexivity]. exfalso.
        pose proof (x_oc _ _ Xyi c k y Oy) as Z. rewrite Ow in Z. injection Z as <-.
        pose proof (oc_lt_tm p (f (S iy)) c k _ (Inv1_run p (f (S iy)) (tr_run p f nb T (S iy) ltac:(lia))) Oy) as Lz.
        pose proof (x_tm _ _ (tr_ext p f nb T (S iy) i ltac:(lia) ltac:(lia))). lia. }
      pose proof Cg' as (_ & A1y & _ & _ & A3hy & _).
      assert (Agy : agree r' (rg (cs (f (S iy)) c)) (pcs (f (S iy)) c)) by (intros q Lq; apply A1y; exact Lq).
      assert (Pky : pcs (f (S iy)) c <= k) by (pose proof (x_pcs _ _ Xyi c); lia).
      assert (Hpy : hplaced p c (cs (f (S iy)) c) (pcs (f (S iy)) c) r' k Plain xs jd).
      { split; [split; [exact Pky|split; [rewrite Ohy; discriminate|]]|].
        - rewrite <- (x_cash _ _ Xyi c k ltac:(rewrite Ohy; discriminate) Ph1). exact Ph3.
        - split; [exact Ocy|]. exists (tm (f ih)). split; [exact Ohy|]. unfold first_atR.
          apply (place_trace p f nb T W Wc c k ih (TH Plain xs) (S iy) r' jd Itkh ltac:(lia) ltac:(lia) Pky Agy
                   ltac:(pose proof (x_pcs _ _ Xyi c); lia)). exact Fo. }
      destruct (A3hy jd k Plain xs Ljs Hpy) as (Vq & _).
      rewrite Vq. symmetry. apply (x_rgo _ _ Xyi c k). rewrite Ohy. discriminate. }
    (* the replay's register there is the model's *)
    assert (Rgsb : rg (cs sb c) k = rg (cs (f (S i)) c) k) by (apply (x_rg _ _ X1b); right; rewrite Ow; discriminate).
    assert (Lp : pcs sb c <= jd).
    { apply (place_ge p f nb T W Wc c k i (TF d0) nb r' jd It ltac:(lia) (le_n _) Pk Ab). exact Fd. }
    assert (Rq : r' jd = rg (cs (f (S i)) c) k).
    { rewrite <- (vd_split (r' jd)), <- (vd_split (rg (cs (f (S i)) c) k)). f_equal; [|exact Vv].
      unfold r'. rewrite (CONS_scv _ _ _ Co' c jd Lp Ljs Xl Cs). fold r'.
      rewrite Vv, ((proj2 Hv) r'), Ced, Nat.eqb_refl, (proj1 Hv). simpl.
      unfold bsr. replace (Nat.ltb jd (pcs (f nb) c)) with false by (symmetry; apply Nat.ltb_ge; exact Lp).
      destruct (fxv p f nb c jd r') as [bx|] eqn:Fv.
      { assert (Cj' : ccJ p c (cs (f (S i)) c) (pcs (f (S i)) c) (bd (cs (f (S i)) c)) r' jd) by (apply (ccJ_agree_r p c _ _ _ (sr g c) r' jd W Agd Cj)).
        pose proof (fix_whole p f nb T W Wc c k i d0 B0 u0 r' jd bx Ea0 Cj' Fd Pk Cd Fv) as V.
        rewrite (proj1 Hv) in V. destruct bx; [reflexivity|simpl in V; discriminate]. }
      assert (Pkb : pend_at p c (cs sb c) (pcs sb c) (tp sb c) r' jd = Some k).
      { apply (pend_at_char_s p sb c (Inv1_run p sb (tr_run p f nb T nb (le_n _)))). exists d0. split.
        - split; [exact Pk|]. split; [rewrite (x_oc _ _ X1b c k _ Ow); discriminate|].
          rewrite (x_aip _ _ X1b c k ltac:(rewrite Ow; discriminate) Pk). exact A0.
        - exists (tm (f i)). split; [apply (x_oc _ _ X1b c k _ Ow)|]. unfold first_at.
          apply (proj2 (place_trace p f nb T W Wc c k i (TF d0) nb r' jd It ltac:(lia) (le_n _) Pk Ab Lp)). exact Fd. }
      rewrite Pkb, Rgsb, (proj1 Hv). reflexivity. }
    rewrite Rq in CF. rewrite (cfailv_eof _ _ _ _ D), (cfailv_inst d0 r' (rg (cs (f (S i)) c))) in CF. congruence.
  - (* earlier: its write took the read's place, which the read item has too *)
    pose proof Co as (F0 & El0 & SF0 & GF0 & Gv0). destruct (Gv0 c) as (ig & Lig & Tig & Cg).
    assert (Lhg : ih < ig) by (apply (tr_tm_lt p f nb T); lia).
    assert (Agd' : agree r' (sr g c) jd) by (intros q Lq; symmetry; apply Agd; exact Lq).
    assert (Fog : first_atR p c (cs (f (S ih)) c) (pcs (f (S ih)) c) (sr g c) (tm (f ih)) Plain xs jd).
    { unfold first_atR in *. apply (plc_agree p W c _ _ _ r' (sr g c) _ _ jd Agd'). exact Fo. }
    assert (Ocg : oc (cs (f ig) c) kh = Some tw).
    { destruct (Nat.le_gt_cases ig (S i)) as [Lg|Lg].
      - apply (x_ocb _ _ (tr_ext p f nb T ig (S i) Lg ltac:(lia)) c kh tw Ow). lia.
      - apply (x_oc _ _ (tr_ext p f nb T (S i) ig ltac:(lia) Lig) c kh tw Ow). }
    pose proof Cg as (_ & A1g & _).
    assert (Agg : agree (sr g c) (rg (cs (f ig) c)) (pcs (f ig) c)) by (intros q Lq; apply A1g; exact Lq).
    assert (Pkg : pcs (f ig) c <= kh).
    { destruct (Nat.le_gt_cases (pcs (f ig) c) kh) as [X|X]; auto. exfalso.
      pose proof (passed_placeR p f nb T W Wc c kh ih xs Bh uh ig (sr g c) jd Eah ltac:(lia) Lig X Agg Fog) as Ej.
      pose proof (CONS_sp _ _ _ Co c) as Z. pose proof (x_pcs _ _ (tr_ext p f nb T ig nb Lig (le_n _)) c). fold jd in Z. lia. }
    destruct (half_wrote_placed p f nb T W Wc c kh ih xs Bh uh ig (sr g c) jd jd Eah ltac:(lia) Lig Cg (le_n _) Fog
                ltac:(rewrite Ocg; discriminate) Pkg) as (dw & (Pw1 & Pw2 & Pw3) & tw' & Ow' & Fw').
    rewrite Ocg in Ow'. injection Ow' as <-.
    destruct (early_of_pending p f nb T ig c kh tw Lig Pkg Ocg) as (iw & dw' & Bw & uw & Eaw & Liw & Tiw).
    assert (Itw : item p f nb c kh iw (TF dw')) by (left; exists dw', Bw, uw; auto).
    destruct (early_post p f nb c kh iw dw' Bw uw Eaw) as (Ow2 & Aw2 & _).
    assert (Ed : dw' = dw).
    { rewrite (x_aip _ _ (tr_ext p f nb T (S iw) ig ltac:(lia) Lig) c kh ltac:(rewrite Ow2; discriminate) Pkg), Aw2 in Pw3.
      apply inst_of_inj in Pw3. exact Pw3. }
    subst dw'.
    assert (Lwi : iw < i) by (apply (tr_tm_lt p f nb T); lia).
    rewrite <- Tiw in Fw'.
    assert (Fw1 : plc p c (cs (f (S iw)) c) (pcs (f (S iw)) c) r' (S (tm (f iw))) (tm (f iw)) (TF dw) jd).
    { apply (plc_agree p W c _ _ _ (sr g c) r' _ _ jd Agd).
      apply (place_trace p f nb T W Wc c kh iw (TF dw) ig (sr g c) jd Itw ltac:(lia) Lig Pkg Agg
               ltac:(apply (first_at_le _ _ _ _ _ _ _ _ Fw'))). exact Fw'. }
    assert (Fw2 : plc p c (cs (f (S i)) c) (pcs (f (S i)) c) r' (S (tm (f iw))) (tm (f iw)) (TF dw) jd).
    { apply (place_trace p f nb T W Wc c kh iw (TF dw) (S i) r' jd Itw ltac:(lia) ltac:(lia) Ph1 Ag' Lpj). exact Fw1. }
    assert (Pkw : placed p c (cs (f (S i)) c) (pcs (f (S i)) c) r' kh dw jd).
    { split; [split; [exact Ph1|split; [rewrite Ow; discriminate|]]|].
      - rewrite (x_aip _ _ (tr_ext p f nb T (S iw) (S i) ltac:(lia) ltac:(lia)) c kh ltac:(rewrite Ow2; discriminate) Ph1). exact Aw2.
      - exists tw. split; [exact Ow|]. unfold first_at. rewrite <- Tiw. exact Fw2. }
    assert (Al : alive f c k gt (S i)) by (unfold alive; pose proof (x_pcs _ _ X1b c); lia).
    destruct (item_pending p f nb T W c k i gt (S i) It ltac:(lia) ltac:(lia) Al) as [(d & -> & Pd & Od)|(xs1 & -> & Phk & Ohk)].
    + assert (Pk2 : placed p c (cs (f (S i)) c) (pcs (f (S i)) c) r' k d jd) by (split; [exact Pd|]; exists (tm (f i)); split; [exact Od|exact Fd]).
      pose proof (placed_unique p c _ _ (oc_inj p (f (S i)) c I1) r' jd kh k dw d Pkw Pk2) as Ekk. subst kh.
      rewrite Od in Ow. injection Ow as E0. lia.
    + assert (Ock : oc (cs (f (S i)) c) k = None).
      { destruct It as [(d1 & B1 & u1 & E1 & Ea1)|(xs2 & B1 & u1 & E1 & Ea1)]; [discriminate E1|].
        destruct (early_postR p f nb c k i xs2 B1 u1 Ea1) as (_ & _ & _ & Oc0 & _). rewrite Oc0.
        pose proof Ea1 as (_ & _ & Oc1 & _). exact Oc1. }
      apply (placed_hplaced p (f (S i)) R1 c r' kh dw k Plain xs1 jd Pkw).
      split; [exact Phk|]. split; [exact Ock|]. exists (tm (f i)). split; [exact Ohk|]. exact Fd.
Qed.

(* the write a pending read took is pending too, and no later SC write: run
   its context forward and meet the read *)
Lemma pend_src : forall tau l g c k i gt x cy ky iy dy By uy Ey,
  HC (tm (f iy)) -> CONS l g tau -> item p f nb c k i gt -> pcs sb c <= k -> tm (f i) <= tau ->
  plc p c (cs (f (S i)) c) (pcs (f (S i)) c) (sr g c) (S (tm (f i))) (tm (f i)) gt (sp g c) ->
  ccJ p c (cs (f (S i)) c) (pcs (f (S i)) c) (bd (cs (f (S i)) c)) (sr g c) (sp g c) ->
  early_at p f nb cy ky iy dy By uy -> pcs sb cy <= ky -> tm (f iy) < tm (f i) ->
  ent sb (tm (f iy)) = Some Ey -> ew Ey = true -> In x (icells (einstr p sb Ey)) -> In x (icells (tinst gt)) ->
  (forall q e, length lb <= q -> nth_error l q = Some e -> writes_x e x = false) ->
  RACY p.
Proof.
  intros tau l g c k i gt x cy ky iy dy By uy Ey IH Co It Pk Lt Fpl Cj Eay Pky Lty AEy Wy Iy Ixd NoW.
  pose proof (item_i p f nb c k i gt It) as Li. pose proof Eay as (Liy & _).
  assert (Liiy : iy < i) by (apply (tr_tm_lt p f nb T); lia).
  assert (Ity : item p f nb cy ky iy (TF dy)) by (left; exists dy, By, uy; auto).
  destruct (early_pending p f nb T W cy ky iy dy By uy nb Eay Liy ltac:(lia) Pky) as (Py & Oy).
  destruct (i_oc p sb Ib1 cy ky _ Oy) as (Ey' & AEy' & Xy & Ky). rewrite AEy in AEy'. injection AEy' as <-.
  assert (Eiy : einstr p sb Ey = inst_of dy) by (unfold einstr; rewrite Xy, Ky; destruct Py as (_ & _ & P3); exact P3).
  (* the read's access in SC *)
  assert (Acc : match gt with TF d => isaccd d = true | TH _ _ => True end).
  { destruct gt as [d|m xs]; [|exact I]. apply (cells_accd x). exact Ixd. }
  destruct (tat_dof _ _ _ (plc_tat _ _ _ _ _ _ _ _ Fpl) Acc) as (dr & Dd & Icd & _).
  assert (Ixr : In x (icells (inst_of dr))) by (rewrite Icd; exact Ixd).
  destruct (Nat.eq_dec cy c) as [->|Nc].
  2:{ apply (pend_meet tau l g c dr x cy ky iy dy By uy Ey IH Co Dd Nc Ixr Eay Pky ltac:(lia) AEy Wy Iy NoW). }
  (* the same context: the write is placed before the read, so the SC run passed it *)
  rewrite Eiy in Iy.
  destruct (fwd l g tau c ky iy (TF dy) IH Co Ity Pky ltac:(lia)) as [Rc|[(j' & Lj' & Fj')|(F' & g' & S' & X' & Co' & Fp & Cg')]].
  - exact Rc.
  - apply (pend_passed tau l g c ky iy dy By uy Ey x j' IH Co Eay Pky ltac:(lia) AEy Wy ltac:(rewrite Eiy; exact Iy) (fun q e L Q _ _ => NoW q e L Q) Lj' Fj').
  - exfalso.
    assert (R1 : run p (f (S i))) by (apply (tr_run p f nb T); lia).
    pose proof (Inv1_run p (f (S i)) R1) as I1.
    assert (X1b : Ext (f (S i)) sb) by (apply (tr_ext p f nb T); lia).
    pose proof (sruns_sp p W _ _ _ S' c) as Lsp.
    set (r' := sr g' c) in *. set (jd := sp g c) in *. set (js := sp g' c) in *.
    assert (Agd : agree (sr g c) r' jd) by (intros q Lq; symmetry; apply (sruns_regs p W _ _ _ S' c q Lq)).
    assert (Fd : plc p c (cs (f (S i)) c) (pcs (f (S i)) c) r' (S (tm (f i))) (tm (f i)) gt jd)
      by (apply (plc_agree p W c _ _ _ (sr g c) r' _ gt jd Agd Fpl)).
    assert (Ag' : agree r' (rg (cs (f (S i)) c)) (pcs (f (S i)) c)).
    { intros q Lq. unfold r'. rewrite (CONS_rg _ _ _ Co') by (pose proof (x_pcs _ _ X1b c); lia).
      apply (x_rg _ _ X1b). left. auto. }
    pose proof (plc_le _ _ _ _ _ _ _ _ Fd) as Lpd.
    destruct (early_pending p f nb T W c ky iy dy By uy (S i) Eay ltac:(lia) ltac:(lia)
                ltac:(pose proof (x_pcs _ _ X1b c); lia)) as (Pyi & Oyi).
    assert (Fy : first_at p c (cs (f (S i)) c) (pcs (f (S i)) c) r' (tm (f iy)) dy js).
    { apply (place_trace p f nb T W Wc c ky iy (TF dy) (S i) r' js Ity ltac:(lia) ltac:(lia) ltac:(unfold alive; pose proof (x_pcs _ _ X1b c); lia) Ag' ltac:(lia)). exact Fp. }
    (* the read's instruction is tied to the write *)
    destruct (tat_dof _ _ _ (plc_tat _ _ _ _ _ _ _ _ Fd) Acc) as (dr' & Dd' & Icd' & _).
    assert (Td : tied (ins p c jd r') (inst_of dy)).
    { apply (proj2 (tied_dof_l _ _ _ _ Dd')). left. exists x. split; [rewrite Icd'; exact Ixd|exact Iy]. }
    assert (Lyi : tm (f iy) < tm (f i)) by lia.
    destruct (Nat.eq_dec jd js) as [Ej|Nj].
    + (* the same place: the write has it *)
      apply (plc_free _ _ _ _ _ _ _ _ Fd). exists ky, (tm (f iy)), dy. split; [exact Pyi|]. split; [exact Oyi|].
      split; [exact Lyi|]. rewrite Ej. exact Fy.
    + (* the write's place is beyond the read's: the read's instruction is the place of an earlier access *)
      (* a CAS whose read took jd before the write: it wrote (or still holds jd), so it does not fail there *)
      assert (FxD := fx_read l g tau (l ++ F') g' (tm (f iy)) c k i gt iy Co Co' It Pk Lt ltac:(lia) Liy Agd ltac:(lia) Ag' Cg' Fd Cj).
      destruct (first_at_before _ _ _ _ _ _ _ _ Fy jd Lpd ltac:(lia) (dof_exec _ _ _ Dd') FxD Td) as (kz & tz & dz & Pz & Oz & Lz & Fz).
      apply (plc_free _ _ _ _ _ _ _ _ Fd). exists kz, tz, dz. split; [exact Pz|]. split; [exact Oz|]. split; [lia|exact Fz].
Qed.

(* a write the base passed shows up in it *)
Lemma lb_has_write : forall cy ky Ey x, ky < pcs sb cy -> RE sb cy ky Ey -> ew Ey = true ->
  In x (icells (einstr p sb Ey)) ->
  exists q e, nth_error lb q = Some e /\ sx e = cy /\ sk e = ky /\ writes_x e x = true.
Proof.
  intros cy ky Ey x L REy Wy Iy.
  destruct (proj1 (srun_pos p W lb gb Bsr cy ky) ltac:(rewrite Bsp; auto)) as (q & e & Q & Xe & Ke).
  exists q, e. split; [auto|]. split; [auto|]. split; [auto|].
  assert (Xq : executes (ins p (sx e) (sk e) (rrg sb (sx e))) (rrg sb (sx e)) = true).
  { rewrite Xe, Ke. pose proof REy as (A0 & B0 & C0).
    destruct (j_ew p sb Ib2 _ Ey _ A0 eq_refl) as [Ew0 _]. rewrite Wy in Ew0. symmetry in Ew0.
    rewrite (einstr_ins p sb Rb W _ Ey A0 ltac:(rewrite B0, C0; exact L)), B0, C0 in Ew0. unfold rgof in Ew0. rewrite B0 in Ew0.
    apply andb_prop in Ew0 as [Ew0 _]. apply andb_prop in Ew0 as [St0 Cd0]. apply andb_prop in St0 as [_ St0].
    unfold executes, M2DQPComp.rrg in *. rewrite Cd0. destruct (isacc _); reflexivity. }
  destruct (lb_ev q e Q Xq) as (E' & RE' & Ei' & Sa & _). rewrite Xe, Ke in RE', Ei', Sa.
  assert (E' = Ey) by (destruct RE' as (A1 & _); destruct REy as (A2 & _); congruence). subst E'.
  rewrite Ei' in Iy.
  destruct REy as (A & B & C).
  destruct (j_ew p sb Ib2 _ Ey _ A Ei') as [Ew _]. rewrite Wy in Ew. symmetry in Ew.
  apply andb_prop in Ew as [Ew _]. apply andb_prop in Ew as [St Cd]. apply andb_prop in St as [_ St]. unfold rgof in Cd. rewrite B in Cd.
  unfold writes_x. rewrite Sa. unfold rrg, M2DQPComp.rrg in *. rewrite Cd. simpl.
  assert (Ia : isacc (ins p cy ky (rg (cs sb cy))) = true) by (destruct (ins p cy ky (rg (cs sb cy))); simpl in St; try discriminate; reflexivity).
  rewrite Ia, Wy. apply existsb_exists. exists x. split; [exact Iy|apply Nat.eqb_refl].
Qed.

(* ---------- the core: a pending read placed in SC takes its value, or there is a race ---------- *)
(* what an access writes is what its effect writes *)
Lemma dof_wvals : forall i r r' d, dof i r = Some d -> wvals i r = wvals (inst_of d) r'.
Proof.
  intros [m0 y0 c0|m0 y0 c0 u0|m0 y0 c0 e0 n0| |] r r' d D; simpl in D; try discriminate;
    destruct (c0 r); try discriminate; injection D as <-; reflexivity.
Qed.

(* two events of a context at the same slot are one *)
Lemma srun_slot_unique : forall l g q1 q2 e1 e2, srun p l g -> nth_error l q1 = Some e1 -> nth_error l q2 = Some e2 ->
  sx e1 = sx e2 -> sk e1 = sk e2 -> q1 = q2.
Proof.
  intros l g q1 q2 e1 e2 R Q1 Q2 X K. destruct (Nat.lt_trichotomy q1 q2) as [L|[L|L]]; auto; exfalso.
  - pose proof (srun_order p W l g R q1 q2 e1 e2 L Q1 Q2 X). lia.
  - pose proof (srun_order p W l g R q2 q1 e2 e1 L Q2 Q1 (eq_sym X)). lia.
Qed.

(* no guard pair between positions where no event is a guard *)
Lemma no_gsync : forall L a b ci cj, (forall z e, a <= z -> z <= b -> nth_error L z = Some e -> sg e = false) ->
  ~ gsync L a b ci cj.
Proof.
  intros L a b ci cj H (a' & b' & f1 & f2 & L1 & L2 & L3 & F1 & F2 & S1 & _).
  rewrite (H a' f1 ltac:(lia) ltac:(lia) F1) in S1. discriminate.
Qed.

(* the item's slot just after it: happened as an access, or only its read *)
Lemma item_oc : forall c k i gt, item p f nb c k i gt ->
  oc (cs (f (S i)) c) k = Some (tm (f i)) \/ oc (cs (f (S i)) c) k = None.
Proof.
  intros c k i gt [(d & B & u & _ & Ea)|(xs & B & u & _ & Ea)].
  - left. apply (early_post p f nb c k i d B u Ea).
  - right. destruct (early_postR p f nb c k i xs B u Ea) as (_ & _ & _ & Oc & _). rewrite Oc. apply Ea.
Qed.

(* the slot order of an item, in the state just after it *)
Lemma item_so : forall c k i gt, item p f nb c k i gt -> forall k' d',
  pending (cs (f (S i)) c) (pcs (f (S i)) c) k' d' -> k' <> k -> tied (tinst gt) (inst_of d') -> k' < k.
Proof.
  intros c k i gt It k' d' (P1 & P2 & P3) N Ti. destruct It as [(d & B & u & -> & Ea)|(xs & B & u & -> & Ea)].
  - destruct (early_post p f nb c k i d B u Ea) as (_ & _ & Pc & _ & Oo & _ & Ao & _).
    pose proof Ea as (_ & _ & _ & Hso & _). apply (Hso k' d'); [|exact Ti].
    split; [rewrite <- Pc; exact P1|]. rewrite <- (Oo k' N), <- (Ao k' N). auto.
  - destruct (early_postR p f nb c k i xs B u Ea) as (_ & _ & Pc & Oc & _).
    pose proof Ea as (_ & _ & _ & _ & Hso & _). apply (Hso k' d'); [|exact Ti].
    destruct Ea as (_ & _ & _ & _ & _ & _ & m' & a & K & w & bv & _ & E).
    assert (Ai : ai (cs (f (S i)) c) k' = ai (cs (f i) c) k') by (rewrite E; unfold sread; simpl; rewrite upd_eq'; simpl; apply upd_neq'; auto).
    split; [rewrite <- Pc; exact P1|]. rewrite <- Oc, <- Ai. auto.
Qed.

(* the last SC write of the read's cell in the segments is its own context's:
   the place of an earlier pending access of the context that writes the
   cell (own-context forwarding) *)
Lemma own_fwd : forall tau l g c k i gt d x ER qw w ys,
  (forall tau', tau' < tau -> HC tau') ->
  CONS l g tau -> item p f nb c k i gt -> pcs sb c <= k -> tm (f i) <= tau ->
  plc p c (cs (f (S i)) c) (pcs (f (S i)) c) (sr g c) (S (tm (f i))) (tm (f i)) gt (sp g c) ->
  ccJ p c (cs (f (S i)) c) (pcs (f (S i)) c) (bd (cs (f (S i)) c)) (sr g c) (sp g c) ->
  ent sb (tm (f i)) = Some ER -> ec ER = c -> ek ER = k ->
  In x (icells (tinst gt)) -> In x (icells (inst_of d)) -> In x (eC ER) ->
  dof (ins p c (sp g c) (sr g c)) (sr g c) = Some d ->
  sm g x <> rdv sb (erf ER) x ->
  (forall w, In w (ids (hs sb x)) -> w <> tm (f i) ->
     (erf ER x = None \/ exists y, erf ER x = Some y /\ older (hs sb x) y w) ->
     gedge sb (tm (f i)) w /\ cedge sb x (tm (f i)) w) ->
  lw l x = Some w -> nth_error l qw = Some w ->
  (forall q e, qw < q -> nth_error l q = Some e -> writes_x e x = false) -> length lb <= qw ->
  sacc w = Some (ys, true) -> In x ys -> sx w = c ->
  RACY p.
Proof.
  intros tau l g c k i gt d x ER qw w ys IHt Co It Pk Lt Fpl Cj AR XR KR Ixg Ix CR Dd Misx MissE Lw Qw After Gq Aw Ixw Ec.
  pose proof (item_i p f nb c k i gt It) as Li.
  assert (Ri : run p (f (S i))) by (apply (tr_run p f nb T); lia).
  pose proof (Inv1_run p (f (S i)) Ri) as Ii.
  assert (Xib : Ext (f (S i)) sb) by (apply (tr_ext p f nb T); lia).
  pose proof Co as (F & El & SF & GF & Gv).
  assert (Rl : srun p l g) by apply (CONS_run _ _ _ Co).
  assert (Lql : qw < length l) by (apply nth_error_Some; congruence).
  assert (IF : In w F).
  { rewrite El in Qw. rewrite nth_error_app2 in Qw by lia. apply nth_error_In in Qw. exact Qw. }
  assert (Gw : sg w = false) by (apply (acc_nog p l g qw w ys true W Rl Qw Aw)).
  destruct (sruns_pos p W _ _ _ (nruns_sruns p bs _ _ _ SF) w IF) as [Pw1 _]. rewrite Bsp, Ec in Pw1.
  destruct (srun_ev p W l g Rl qw w Qw) as (iw & Hiw & Lw' & Shw).
  destruct (acc_ev p l g qw w ys true W Rl Qw Aw) as [Icw Exw]. rewrite Ec in Icw, Exw, Lw', Hiw, Shw.
  set (jw := sk w) in *.
  assert (Lpw : pcs (f (S i)) c <= jw) by (pose proof (x_pcs _ _ Xib c); lia).
  (* the write's instruction is the place of an earlier pending access *)
  assert (Tw : tied (ins p c jw (sr g c)) (tinst gt)) by (left; exists x; split; [rewrite Icw; exact Ixw|exact Ixg]).
  destruct (plc_before_dec p c (cs (f (S i)) c) (pcs (f (S i)) c) (tp (f (S i)) c) (sr g c) (tm (f i)) gt (sp g c) jw
              (pend_ok_of p (f (S i)) c Ii) (bn_of p (f (S i)) c Ii) (bnh_of p (f (S i)) c Ii) Fpl Lpw Lw' Exw Tw)
    as [Tk|(v & (kh & th & mh & xh & Ph & Oh & Lth & Hl & Fh & Ev) & CF)].
  2:{ (* jw is the place of a CAS's read alone that fails under these registers, while the SC run wrote
         there: that read did not get its value in SC, an earlier race *)
      destruct (early_of_hpending p f nb T (S i) c kh th ltac:(lia) Oh) as (ih & xs & Bh & uh & Eah & Lih & Tih).
      assert (Itkh : item p f nb c kh ih (TH Plain xs)) by (right; exists xs, Bh, uh; auto).
      pose proof Ph as (Ph1 & _ & Ph3).
      destruct (early_pendingR p f nb T c kh ih xs Bh uh (S i) Eah ltac:(lia) ltac:(lia) Ph1) as (Ph' & _).
      pose proof Ph' as (_ & _ & Ph3'). rewrite Ph3 in Ph3'. injection Ph3' as -> ->. subst th.
      assert (Ag : agree (sr g c) (rrg sb c) (pcs sb c)) by (intros q Lq; apply (CONS_rg _ _ _ Co); lia).
      assert (Agi : agree (sr g c) (rg (cs (f (S i)) c)) (pcs (f (S i)) c)).
      { intros q Lq. rewrite (Ag q) by (pose proof (x_pcs _ _ Xib c); lia). unfold rrg, M2DQPComp.rrg. apply (x_rg _ _ Xib). left; auto. }
      assert (Fo : first_atR p c (cs (f (S ih)) c) (pcs (f (S ih)) c) (sr g c) (tm (f ih)) Plain xs jw).
      { apply (place_trace p f nb T W Wc c kh ih (TH Plain xs) (S i) (sr g c) jw Itkh ltac:(lia) ltac:(lia) Ph1 Agi Lpw). exact Fh. }
      assert (Lkh : pcs sb c <= kh).
      { destruct (Nat.lt_ge_cases kh (pcs sb c)) as [X|X]; auto. exfalso.
        pose proof (passed_placeR p f nb T W Wc c kh ih xs Bh uh nb (sr g c) jw Eah ltac:(lia) (le_n _) X Ag Fo). lia. }
      (* the instruction at jw: a CAS of xs; the SC run's CAS there succeeded, so its verdict is a success *)
      assert (Lpb : pcs sb c <= jw) by (apply (place_ge p f nb T W Wc c kh ih (TH Plain xs) nb (sr g c) jw Itkh ltac:(lia) (le_n _) Lkh Ag); exact Fo).
      subst v. pose proof (first_atR_eofR _ _ _ _ _ _ _ _ _ Fh) as Er.
      pose proof (CONS_scv _ _ _ Co c jw Lpb Lw') as Sv.
      rewrite Hiw in Er, CF, Sv.
      destruct iw as [| |m0 x0 cn ee nn| |]; simpl in Er; try discriminate.
      destruct (cn (sr g c)) eqn:Cn; [|discriminate].
      rewrite Aw in Shw. cbn [evshape] in Shw. rewrite Cn in Shw. injection Shw as _ Ok _.
      unfold xload, icond in Sv. cbn [is_load is_cas ieval cexp] in Sv. rewrite Cn in Sv. specialize (Sv eq_refl eq_refl).
      rewrite <- Ok in Sv. symmetry in Sv. apply andb_prop in Sv as [Sv _].
      cbn [cfailv] in CF. rewrite Cn, <- Ok, Sv in CF. discriminate. }
  destruct Tk as (kz & tz & dz & Pz & Oz & Ltz & Fz).
  pose proof Pz as (Pz1 & Pz2 & Pz3).
  destruct (early_of_pending p f nb T (S i) c kz tz ltac:(lia) Pz1 Oz) as (iz & dz' & Bz & uz & Eaz & Liz & Tiz).
  destruct (early_post p f nb c kz iz dz' Bz uz Eaz) as (Oz1 & Az1 & Pz1' & _).
  pose proof Eaz as (Liz' & Lkz0 & _ & _).
  assert (Dq : dz' = dz).
  { destruct (pend_fate p f nb T (S iz) (S i) c kz dz' ltac:(lia) ltac:(lia) W ltac:(rewrite Oz1; discriminate) ltac:(rewrite Pz1'; pose proof (x_pcs _ _ (tr_ext p f nb T (S iz) (S i) ltac:(lia) ltac:(lia)) c); lia) Az1)
      as [(_ & Aq)|(X1 & _)]; [|lia].
    rewrite Pz3 in Aq. apply inst_of_inj in Aq. auto. }
  subst dz'. subst tz.
  assert (Agi : agree (sr g c) (rg (cs (f (S i)) c)) (pcs (f (S i)) c)).
  { intros q Lq. rewrite (CONS_rg _ _ _ Co) by (pose proof (x_pcs _ _ Xib c); lia).
    unfold rrg, M2DQPComp.rrg. apply (x_rg _ _ Xib). left. auto. }
  assert (Itz : item p f nb c kz iz (TF dz)) by (left; exists dz, Bz, uz; auto).
  assert (Fzo : first_at p c (cs (f (S iz)) c) (pcs (f (S iz)) c) (sr g c) (tm (f iz)) dz jw).
  { apply (place_trace p f nb T W Wc c kz iz (TF dz) (S i) (sr g c) jw Itz ltac:(lia) ltac:(lia) Pz1 Agi Lpw). exact Fz. }
  pose proof (own_lt' c kz iz dz Bz uz (sr g c) jw Eaz ltac:(intros q Lq; apply (CONS_rg _ _ _ Co c q Lq)) Fzo) as Lzo.
  assert (Agb : agree (sr g c) (rg (cs sb c)) (pcs sb c)) by (intros q Lq; apply (CONS_rg _ _ _ Co); auto).
  assert (Pkz : pcs sb c <= kz).
  { destruct (Nat.lt_ge_cases kz (pcs sb c)) as [X|X]; auto. exfalso.
    pose proof (passed_place p f nb T W Wc c kz iz dz Bz uz nb (sr g c) jw Eaz ltac:(lia) (le_n _) X Agb Fzo). lia. }
  destruct (early_pending p f nb T W c kz iz dz Bz uz nb Eaz ltac:(lia) (le_n _) Pkz) as (Pzb & Ozb).
  destruct (i_oc p sb Ib1 c kz _ Ozb) as (Ez & AEz & XEz & KEz).
  assert (Eiz : einstr p sb Ez = inst_of dz) by (unfold einstr; rewrite XEz, KEz; destruct Pzb as (_ & _ & P3); exact P3).
  assert (Ixz0 : In x (icells (inst_of dz))).
  { rewrite <- (eof_icells _ _ _ (first_at_eof _ _ _ _ _ _ _ _ Fz)), Icw. exact Ixw. }
  pose proof (first_at_dof _ _ _ _ _ _ _ _ Fz (cells_accd _ _ Ixz0)) as Dz.
  destruct (dof_shape _ _ _ Dz) as (Qc & _ & Ql & Qs & _ & Qco & Qev).
  assert (Ixz : In x (icells (inst_of dz))) by (rewrite <- Qc, Icw; exact Ixw).
  (* the write is recorded at an earlier slot than the read *)
  assert (Lkk : kz < k).
  { apply (item_so c k i gt It kz dz Pz); [intros ->; destruct (item_oc c k i gt It) as [Ok|Ok]; rewrite Ok in Oz; [injection Oz as Eqz; lia|discriminate]|]. left. exists x. split; [exact Ixg|exact Ixz]. }
  (* it is not fenced: a fence before its place would be tied to it *)
  assert (NoFa : ~ fa p c jw).
  { intros (_ & Fa). destruct (Fa (sr g c)) as [F1 _].
    assert (Tk : taken p c (cs (f (S iz)) c) (pcs (f (S iz)) c) (sr g c) (tm (f iz)) (jw - 1)).
    { apply (first_at_before _ _ _ _ _ _ _ _ Fzo (jw - 1)); [lia|lia| | |].
      - rewrite F1. reflexivity.
      - intros vv _. rewrite F1. reflexivity.
      - rewrite F1. right. left. reflexivity. }
    destruct (taken_dof _ _ _ _ _ _ _ Tk) as (d0 & D0). rewrite F1 in D0. discriminate. }
  (* the SC write flag of w *)
  rewrite <- Hiw in Shw. rewrite Aw in Shw.
  assert (Wfl : is_store (inst_of dz) = true /\
                (is_cas (inst_of dz) = true -> vok (sr g c jw) = true)).
  { clear -Dz Shw. destruct (ins p c jw (sr g c)) as [m0 y0 c0|m0 y0 c0 u0|m0 y0 c0 e0 n0| |];
      simpl in Dz, Shw; try discriminate; destruct (c0 (sr g c)) eqn:C0; try (rewrite C0 in Shw); try discriminate;
      injection Dz as <-; simpl.
    - split; [reflexivity|discriminate].
    - split; [reflexivity|]. intros _. injection Shw; intros.
      first [reflexivity|assumption|symmetry; assumption]. }
  destruct Wfl as [Wst Wcas].
  (* the SC step of w, from the prefix before it *)
  destruct (CONS_prefix l g tau qw Co Gq ltac:(lia)) as (gq & Coq & Sq).
  assert (Sk : skipn qw l = w :: skipn (S qw) l).
  { clear -Qw. revert qw Qw. induction l as [|a0 l IH]; intros [|q] Q; simpl in *; try discriminate.
    - injection Q as <-. reflexivity.
    - apply IH. auto. }
  rewrite Sk in Sq. apply (nruns_sruns p bs) in Sq. change (w :: skipn (S qw) l) with ([w] ++ skipn (S qw) l) in Sq.
  destruct (sruns_split p _ _ _ _ Sq) as (g1 & S1 & S2).
  assert (St : sstep p gq w g1) by (apply sruns_single; exact S1).
  destruct (sstep_shape p W _ _ _ St) as (i2 & Hi2 & _ & Hk2 & Hsp2 & Hr2 & Hrk2 & _).
  rewrite Ec in Hi2, Hk2, Hrk2, Hsp2. fold jw in Hi2, Hk2, Hrk2.
  assert (Spg1 : jw < sp g1 c) by (rewrite Hsp2; unfold upd; rewrite Nat.eqb_refl; lia).
  assert (Agq : agree (sr g c) (sr gq c) jw).
  { intros z Lz. rewrite (sruns_regs p W _ _ _ S2 c z) by lia. apply Hr2. right. lia. }
  assert (Hi2' : i2 = ins p c jw (sr g c)).
  { rewrite <- Hi2. symmetry. apply (proj1 (ins_agree p W c jw (sr g c) (sr gq c) Agq)). }
  assert (Fzq : first_at p c (cs (f (S iz)) c) (pcs (f (S iz)) c) (sr gq c) (tm (f iz)) dz (sp gq c)).
  { rewrite <- Hk2. apply (first_at_agree p W c _ _ (sr g c) (sr gq c) _ _ jw Agq Fzo). }
  assert (Coz : CONS (firstn qw l) gq (tm (f iz))) by (apply (CONS_mono (firstn qw l) gq tau (tm (f iz)) ltac:(lia) Coq)).
  assert (Lfq : length (firstn qw l) = qw) by (rewrite length_firstn; lia).
  assert (Rl1 : srun p (firstn qw l ++ [w]) g1) by (econstructor; [apply (CONS_run _ _ _ Coq)|exact St]).
  assert (Qw1 : nth_error (firstn qw l ++ [w]) qw = Some w) by (pose proof (nth_app_last' (firstn qw l) w) as Z; rewrite Lfq in Z; exact Z).
  assert (Qlo : forall z, z < qw -> nth_error (firstn qw l ++ [w]) z = nth_error l z).
  { intros z Lz. rewrite nth_app_old' by lia. apply firstn_nth'. auto. }
  (* no guard in the segments up to w *)
  assert (NoG : forall a ci cj, length lb <= a -> ~ gsync (firstn qw l ++ [w]) a qw ci cj).
  { intros a ci cj La. apply no_gsync. intros z e L1 L2 Z. destruct (Nat.eq_dec z qw) as [->|Nz].
    - rewrite Qw1 in Z. injection Z as <-. exact Gw.
    - rewrite Qlo in Z by lia. rewrite El in Z. rewrite nth_error_app2 in Z by lia. apply nth_error_In in Z. apply GF. exact Z. }
  (* the run's write flag and register of the pending write *)
  destruct (j_ew p sb Ib2 _ Ez _ AEz Eiz) as [EwZ EwV].
  rewrite (oc_eh p sb c kz _ Ez Ib1 Ozb AEz XEz KEz) in EwZ. cbn [negb andb] in EwZ.
  destruct (j_val p sb Ib2 _ Ez _ AEz Eiz) as [VZ _]. unfold rgof in EwZ, VZ, EwV. rewrite XEz in EwZ, EwV. rewrite XEz, KEz in VZ.
  assert (Cz : icond (inst_of dz) (rg (cs sb c)) = true) by (destruct dz; reflexivity).
  assert (Ltz' : tm (f iz) < tau) by lia.
  destruct (ew Ez) eqn:WEz.
  2:{ (* the run's CAS failed where the SC one succeeded: a pending read of
         an earlier time sees another value *)
    rewrite Wst, Cz in EwZ. simpl in EwZ. symmetry in EwZ. rewrite andb_false_r, orb_false_r in EwZ. apply negb_false_iff in EwZ as Ca.
    assert (Ldz : is_load (inst_of dz) = true) by (destruct dz; simpl in Ca; try discriminate; reflexivity).
    assert (Xz : xload (inst_of dz) (rg (cs sb c)) = true) by (unfold xload; rewrite Ldz, Cz; reflexivity).
    (* the run's verdict is a failure, and the replay took it at jw *)
    assert (Vz : vok (rg (cs sb c) kz) = false).
    { pose proof (j_ok p sb Ib2 _ Ez AEz (oc_eh p sb c kz _ Ez Ib1 Ozb AEz XEz KEz) ltac:(rewrite Eiz; exact Ca)
                    ltac:(rewrite Eiz; unfold rgof; rewrite XEz; exact Xz)) as J.
      rewrite XEz, KEz, WEz in J. exact J. }
    assert (Lpb : pcs sb c <= jw) by (apply (place_ge p f nb T W Wc c kz iz (TF dz) nb (sr g c) jw Itz ltac:(lia) (le_n _) Pkz Agb); exact Fzo).
    assert (Pkb : pend_at p c (cs sb c) (pcs sb c) (tp sb c) (sr g c) jw = Some kz).
    { apply (pend_at_char_s p sb c Ib1). exists dz. split; [exact Pzb|].
      exists (tm (f iz)). split; [exact Ozb|]. unfold first_at.
      apply (proj2 (place_trace p f nb T W Wc c kz iz (TF dz) nb (sr g c) jw Itz ltac:(lia) (le_n _) Pkz Agb Lpb)). exact Fzo. }
    pose proof (CONS_scv _ _ _ Co c jw Lpb Lw') as Sv.
    rewrite Hiw in Sv. pose proof (dof_eof _ _ _ Dz) as Ez'. rewrite Hiw in Ez'.
    destruct (eof_cexp _ _ _ (sr g c) Ez') as (Csd & Cez).
    assert (Xw : xload iw (sr g c) = true) by (unfold xload; rewrite <- Hiw, Ql, Ldz; simpl; exact Qco).
    specialize (Sv Xw ltac:(rewrite <- Csd; exact Ca)).
    unfold bsr in Sv. replace (Nat.ltb jw (pcs (f nb) c)) with false in Sv by (symmetry; apply Nat.ltb_ge; exact Lpb).
    destruct (fxv p f nb c jw (sr g c)) as [bx|] eqn:Fv; try rewrite Fv in Sv.
    2:{ rewrite Pkb, Vz, andb_false_r in Sv. rewrite (Wcas Ca) in Sv. discriminate. }
    (* a result fixed at jw for these registers: the run's CAS took another value than the replay's, which
       is the pending CAS's read of an earlier time not getting its value *)
    rewrite (Wcas Ca) in Sv. symmetry in Sv. apply andb_prop in Sv as [SqE Bx]. subst bx.
    assert (Czj : ccJ p c (cs (f (S iz)) c) (pcs (f (S iz)) c) (bd (cs (f (S iz)) c)) (sr g c) jw).
    { apply (ccJ_le _ _ _ _ _ _ (sp g c)); [apply (mono_tr p f nb T W Wc c (sr g c) (sp g c) (S iz) (S i) ltac:(lia) ltac:(lia) Cj)| |lia].
      apply (first_at_le _ _ _ _ _ _ _ _ Fzo). }
    pose proof (fix_whole p f nb T W Wc c kz iz dz Bz uz (sr g c) jw true Eaz Czj Fzo Pkz Ca Fv) as V.
    destruct (early_post p f nb c kz iz dz Bz uz Eaz) as (Okz & _).
    rewrite <- (x_rg _ _ (tr_ext p f nb T (S iz) nb ltac:(lia) (le_n _)) c kz ltac:(right; rewrite Okz; discriminate)), Vz in V.
    simpl in V. symmetry in V. apply Nat.eqb_neq in V.
    apply (IHt (tm (f iz)) Ltz' (firstn qw l) gq c kz iz (TF dz) Coz Itz Pkz (le_n _) Ldz Fzq).
    - rewrite <- Hk2. exact NoFa.
    - rewrite <- Hk2. apply (ccJ_agree_r p c _ _ _ (sr g c) (sr gq c) jw W Agq Czj).
    - cbn [tinst]. intros Z. apply V.
      pose proof (proj2 (ins_agree p W c jw (sr g c) (sr gq c) Agq)) as Ag2.
      assert (Xq : xload i2 (sr gq c) = true).
      { rewrite Hi2'. unfold xload in *. rewrite <- (ieval_cond _ _ _ Ag2). rewrite Hiw. exact Xw. }
      rewrite Xq in Hrk2.
      assert (Vg : vv (sr g c jw) = enc (map (sm gq) (icells (inst_of dz)))).
      { rewrite (sruns_regs p W _ _ _ S2 c jw Spg1). rewrite <- (rval_cas i2) by (rewrite Hi2', Hiw, <- Csd; exact Ca).
        rewrite Hrk2. rewrite Hi2', Qc. reflexivity. }
      rewrite <- (rval_cas (inst_of dz) (rg (cs sb c) kz) Ca), <- Z, <- Vg.
      apply Nat.eqb_eq in SqE. rewrite SqE, Cez. reflexivity. }
  destruct (EwV eq_refl) as [Wv Hh]. pose proof (Hh x Ixz) as Inz.
  assert (CZ : In x (eC Ez)) by (apply (ew_eC _ Ez x AEz WEz); rewrite Eiz; exact Ixz).
  assert (Po : cedge sb x (tm (f iz)) (tm (f i))).
  { right; right; right; right. exists Ez, ER. split; [exact AEz|]. split; [exact AR|].
    split; [congruence|]. split; [rewrite KEz, KR; exact Lkk|]. split; [exact CZ|exact CR]. }
  assert (Nti : tm (f iz) <> tm (f i)) by lia.
  destruct (erf ER x) as [y|] eqn:Ey.
  2:{ exfalso. destruct (MissE (tm (f iz)) Inz Nti (or_introl eq_refl)) as [_ MC].
      apply (proj2 EVb x (tm (f iz))). apply t_trans with (tm (f i)); constructor; auto. }
  destruct (j_rf p sb Ib2 _ ER x y AR Ey) as (Ly & _ & _ & Iny).
  destruct (Nat.eq_dec y (tm (f iz))) as [Eyz|Nyz].
  { (* the read took the pending write: the SC run has its value *)
    exfalso. apply Misx. unfold rdv. rewrite Ey, Eyz, Wv.
    destruct (proj2 (srun_mem p W l g Rl x) w Lw) as (iw' & Hiw' & M). rewrite Ec in Hiw', M. rewrite M.
    fold jw in Hiw'. rewrite <- Hiw', Qc. rewrite (dof_wvals _ _ (rg (cs sb c)) _ Dz). reflexivity. }
  destruct (older_total (hs sb x) y (tm (f iz)) Iny Inz Nyz) as [Ol|Ol].
  { (* an older write: the read missed the pending write before it *)
    exfalso. destruct (MissE (tm (f iz)) Inz Nti (or_intror (ex_intro _ y (conj eq_refl Ol)))) as [_ MC].
    apply (proj2 EVb x (tm (f iz))). apply t_trans with (tm (f i)); constructor; auto. }
  (* a write newer than the pending write *)
  destruct (j_hist p sb Ib2 x y Iny) as (EY & iY & AY & WY & EIY & ICY).
  destruct (i_et p sb Ib1 y EY AY) as (TY & OY). assert (EhY : eh EY = false) by (destruct (j_ew p sb Ib2 _ EY _ AY eq_refl) as [W1 _]; rewrite WY in W1; destruct (eh EY); [discriminate|reflexivity]). rewrite EhY in OY.
  assert (CY : In x (eC EY)) by (apply (ew_eC y EY x AY WY); rewrite EIY; exact ICY).
  destruct (Nat.lt_ge_cases (ek EY) (pcs sb (ec EY))) as [Lp|Gp].
  - (* a base write *)
    destruct (Nat.eq_dec (ec EY) c) as [Ecy|Ncy].
    + exfalso. apply (proj2 EVb x (tm (f iz))). apply t_trans with y; constructor.
      * left. exact Ol.
      * right; right; right; right. exists EY, Ez. split; [exact AY|]. split; [exact AEz|].
        split; [congruence|]. split; [rewrite KEz; rewrite Ecy in Lp; lia|]. split; [exact CY|exact CZ].
    + assert (REY : RE sb (ec EY) (ek EY) EY) by (unfold RE, bt, tmo; rewrite OY; auto).
      destruct (lb_has_write (ec EY) (ek EY) EY x Lp REY WY ltac:(rewrite EIY; auto)) as (qy & ey & Qy & Xey & Key & Wey).
      assert (Lqy : qy < length lb) by (apply nth_error_Some; congruence).
      assert (Qyl : nth_error (firstn qw l ++ [w]) qy = Some ey).
      { rewrite Qlo by lia. rewrite El. rewrite nth_error_app1 by auto. exact Qy. }
      unfold writes_x in Wey. destruct (sacc ey) as [[ys1 wy1]|] eqn:Say; [|discriminate]. destruct wy1; [|discriminate].
      apply existsb_exists in Wey. destruct Wey as (z & Iz & Z). apply Nat.eqb_eq in Z. subst z.
      destruct (gsync_dec (firstn qw l ++ [w]) qy qw (ec EY) c) as [G|Ng].
      * (* synchronised: the pending write knew y *)
        exfalso.
        assert (Kn : vsub (esrc EY) (eQ Ez)).
        { apply (know_base (firstn qw l) gq tau c kz iz (TF dz) qy ey EY Ez w Coq Itz Pkz Fzq Lqy).
          - rewrite firstn_nth' by lia. rewrite El. rewrite nth_error_app1 by auto. exact Qy.
          - exists ys1, true. exact Say.
          - rewrite Xey, Key. exact REY.
          - exact AEz.
          - exact XEz.
          - left. exact WEz.
          - exact Gw.
          - rewrite Xey. exact Ncy.
          - rewrite Lfq, Xey. exact G. }
        assert (Qy' : eQ Ez y) by (apply Kn; unfold esrc, srcv, vor; right; rewrite WY; simpl; congruence).
        apply (proj1 EVb (tm (f iz))). apply t_trans with y; constructor.
        -- left. exists x. exact Ol.
        -- right; right. exists Ez. split; [exact AEz|]. split; [exact Qy'|lia].
      * (* a race between y's write and w *)
        exists (firstn qw l ++ [w]), g1. split; [exact Rl1|].
        apply (racy_g_mk p _ qy qw ey w x ys1 ys true true ltac:(lia) Qyl Qw1 ltac:(rewrite Xey, Ec; exact Ncy) Say Aw Iz Ixw eq_refl
                 ltac:(rewrite Xey, Ec; exact Ng)).
        intros (_ & Fw). apply NoFa. rewrite Ec in Fw. exact Fw.
  - (* a pending write *)
    destruct (early_of_pending p f nb T nb (ec EY) (ek EY) y ltac:(lia) Gp OY) as (iy & dy & By & uy & Eay & Liy & Tiy).
    assert (AEY : ent sb (tm (f iy)) = Some EY) by (rewrite Tiy; exact AY).
    assert (IHy : HC (tm (f iy))) by (apply IHt; lia).
    destruct (early_pending p f nb T W (ec EY) (ek EY) iy dy By uy nb Eay Liy ltac:(lia) Gp) as (Pyb & Oyb).
    assert (Eiy : einstr p sb EY = inst_of dy) by (unfold einstr; destruct Pyb as (_ & _ & P3); exact P3).
    assert (Ixy : In x (icells (inst_of dy))) by (rewrite <- Eiy, EIY; exact ICY).
    assert (Liyi : iy < i) by (apply (tr_tm_lt p f nb T); lia).
    assert (Ity : item p f nb (ec EY) (ek EY) iy (TF dy)) by (left; exists dy, By, uy; auto).
    destruct (Nat.eq_dec (ec EY) c) as [Ecy|Ncy].
    + (* the same context *)
      rewrite Ecy in Gp, OY, Eay, Pyb, Oyb.
      destruct (Nat.lt_trichotomy y (tm (f iz))) as [Lyz|[Lyz|Lyz]]; [|congruence|].
      * (* y happened first: recorded at an earlier slot than the pending write *)
        exfalso.
        assert (Liyz : iy < iz) by (apply (tr_tm_lt p f nb T); lia).
        destruct (early_pending p f nb T W c (ek EY) iy dy By uy iz Eay Liyz ltac:(lia)
                    ltac:(pose proof (x_pcs _ _ (tr_ext p f nb T iz nb ltac:(lia) ltac:(lia)) c); lia)) as (Pyz & _).
        pose proof Eaz as (_ & _ & _ & Hsoz & _).
        assert (Lky : ek EY < kz) by (apply (Hsoz (ek EY) dy Pyz); left; exists x; auto).
        apply (proj2 EVb x (tm (f iz))). apply t_trans with y; constructor.
        -- left. exact Ol.
        -- right; right; right; right. exists EY, Ez. split; [exact AY|]. split; [exact AEz|].
           split; [congruence|]. split; [rewrite KEz; exact Lky|]. split; [exact CY|exact CZ].
      * (* the pending write first: y's place is beyond w's *)
        destruct (early_pending p f nb T W c (ek EY) iy dy By uy (S i) Eay ltac:(lia) ltac:(lia)
                    ltac:(pose proof (x_pcs _ _ Xib c); lia)) as (Pyi & Oyi).
        rewrite Ecy in Ity.
        destruct (fwd l g tau c (ek EY) iy (TF dy) IHy Co Ity Gp ltac:(lia)) as [Rc|[(j' & Lj' & Fj')|(F' & g' & S' & X' & Co' & Fp & Cg')]].
        -- exact Rc.
        -- assert (Gej : pcs (f (S i)) c <= j').
           { apply (place_ge p f nb T W Wc c (ek EY) iy (TF dy) (S i) (sr g c) j' Ity ltac:(lia) ltac:(lia)
                      ltac:(unfold alive; pose proof (x_pcs _ _ Xib c); lia) Agi Fj'). }
           assert (Fyi : first_at p c (cs (f (S i)) c) (pcs (f (S i)) c) (sr g c) (tm (f iy)) dy j').
           { apply (place_trace p f nb T W Wc c (ek EY) iy (TF dy) (S i) (sr g c) j' Ity ltac:(lia) ltac:(lia)
                      ltac:(unfold alive; pose proof (x_pcs _ _ Xib c); lia) Agi Gej). exact Fj'. }
           assert (Ljj : jw < j').
           { apply (placed_tied_order p c (cs (f (S i)) c) (pcs (f (S i)) c) (sr g c) kz (ek EY) dz dy jw j' (tm (f iz)) (tm (f iy)) Wc (oc_inj p (f (S i)) c Ii)).
             - split; [exact Pz|exists (tm (f iz)); split; [exact Oz|exact Fz]].
             - split; [exact Pyi|exists (tm (f iy)); split; [exact Oyi|exact Fyi]].
             - exact Oz.
             - exact Oyi.
             - left. exists x. split; [exact Ixy|exact Ixz].
             - lia.
             - (* the replay's register at y's place is the model's at y, which wrote: no failure there *)
               intros v (kh & th & mh & xh & Ph & Oh & Lth & Hl & Fh & Ev). subst v.
               pose proof (first_at_eof _ _ _ _ _ _ _ _ Fyi) as Dy. rewrite (cfailv_eof _ _ _ _ Dy).
               destruct (is_cas (inst_of dy)) eqn:Cy; [|destruct dy; simpl in Cy |- *; try discriminate; reflexivity].
               pose proof Co as (F0 & El0 & SF0 & GF0 & Gv0). destruct (Gv0 c) as (ig & Lig & Tig & Cg).
               assert (Liyg : iy < ig) by (apply (tr_tm_lt p f nb T); lia).
               pose proof Cg as (_ & A1g & _ & A3g & _).
               assert (Agg : agree (sr g c) (rg (cs (f ig) c)) (pcs (f ig) c)) by (intros q Lq; apply A1g; exact Lq).
               assert (Xgb : Ext (f ig) sb) by (apply (tr_ext p f nb T); lia).
               assert (Pkg : pcs (f ig) c <= ek EY) by (pose proof (x_pcs _ _ Xgb c); lia).
               assert (Lpg : pcs (f ig) c <= j') by (apply (place_ge p f nb T W Wc c (ek EY) iy (TF dy) ig (sr g c) j' Ity ltac:(lia) Lig Pkg Agg Fj')).
               destruct (early_post p f nb c (ek EY) iy dy By uy Eay) as (Oy1 & Ay1 & _).
               assert (Pyg : placed p c (cs (f ig) c) (pcs (f ig) c) (sr g c) (ek EY) dy j').
               { split; [split; [exact Pkg|split]|].
                 - rewrite (x_oc _ _ (tr_ext p f nb T (S iy) ig ltac:(lia) Lig) c _ _ Oy1). discriminate.
                 - rewrite (x_aip _ _ (tr_ext p f nb T (S iy) ig ltac:(lia) Lig) c _ ltac:(rewrite Oy1; discriminate) Pkg). exact Ay1.
                 - exists (tm (f iy)). split; [apply (x_oc _ _ (tr_ext p f nb T (S iy) ig ltac:(lia) Lig) c _ _ Oy1)|].
                   unfold first_at. apply (proj2 (place_trace p f nb T W Wc c (ek EY) iy (TF dy) ig (sr g c) j' Ity ltac:(lia) Lig Pkg Agg Lpg)). exact Fj'. }
               assert (Ldy : is_load (inst_of dy) = true) by (destruct dy; simpl in Cy; try discriminate; reflexivity).
               rewrite (A3g j' (ek EY) dy Lj' Pyg Ldy).
               rewrite <- (x_rg _ _ Xgb c (ek EY) ltac:(right; rewrite (x_oc _ _ (tr_ext p f nb T (S iy) ig ltac:(lia) Lig) c _ _ Oy1); discriminate)).
               assert (Vy : vok (rg (cs sb c) (ek EY)) = true).
               { assert (Xy : xload (inst_of dy) (rgof sb EY) = true) by (unfold xload; rewrite Ldy; destruct dy; reflexivity).
                 pose proof (j_ok p sb Ib2 y EY AY EhY ltac:(rewrite Eiy; exact Cy) ltac:(rewrite Eiy; exact Xy)) as J.
                 rewrite Ecy, WY in J. exact J. }
               apply (cfailv_ok (inst_of dy) (sr g c) (sr g c) _ Cy eq_refl Vy).
               rewrite (cas_ok_val c (ek EY) _ dy Oyb ltac:(destruct Pyb as (_ & _ & P3); exact P3) Cy Vy (sr g c)).
               destruct dy; simpl in Cy; try discriminate; reflexivity. }
           apply (pend_passed tau l g c (ek EY) iy dy By uy EY x j' IHy Co Eay Gp ltac:(lia) AEY WY ltac:(rewrite EIY; exact ICY)).
           ++ intros q e _ Q Xe Ke. apply (After q e); [|exact Q].
              destruct (Nat.lt_trichotomy q qw) as [X1|[X1|X1]]; auto; exfalso.
              ** pose proof (srun_order p W l g Rl q qw e w X1 Q Qw ltac:(rewrite Xe, Ec; reflexivity)). fold jw in H. lia.
              ** subst q. rewrite Q in Qw. injection Qw as <-. fold jw in Ke. lia.
           ++ exact Lj'.
           ++ exact Fj'.
        -- (* running the context forward to y's place passes the read's place *)
           exfalso.
           pose proof (sruns_sp p W _ _ _ S' c) as Lsp.
           assert (Agd : agree (sr g c) (sr g' c) (sp g c)) by (intros q Lq; symmetry; apply (sruns_regs p W _ _ _ S' c q Lq)).
           assert (Fd : plc p c (cs (f (S i)) c) (pcs (f (S i)) c) (sr g' c) (S (tm (f i))) (tm (f i)) gt (sp g c))
             by (apply (plc_agree p W c _ _ _ (sr g c) (sr g' c) _ gt (sp g c) Agd Fpl)).
           assert (Ag' : agree (sr g' c) (rg (cs (f (S i)) c)) (pcs (f (S i)) c)).
           { intros q Lq. rewrite (CONS_rg _ _ _ Co') by (pose proof (x_pcs _ _ Xib c); lia).
             unfold rrg, M2DQPComp.rrg. apply (x_rg _ _ Xib). left. auto. }
           pose proof (plc_le _ _ _ _ _ _ _ _ Fd) as Lpd.
           assert (Fy : first_at p c (cs (f (S i)) c) (pcs (f (S i)) c) (sr g' c) (tm (f iy)) dy (sp g' c)).
           { apply (place_trace p f nb T W Wc c (ek EY) iy (TF dy) (S i) (sr g' c) (sp g' c) Ity ltac:(lia) ltac:(lia)
                      ltac:(unfold alive; pose proof (x_pcs _ _ Xib c); lia) Ag' ltac:(lia)). exact Fp. }
           assert (Acc : match gt with TF d => isaccd d = true | TH _ _ => True end).
           { destruct gt as [d0|m0 xs0]; [|exact I]. apply (cells_accd x). exact Ixg. }
           destruct (tat_dof _ _ _ (plc_tat _ _ _ _ _ _ _ _ Fd) Acc) as (dr' & Ddd & Icd' & _).
           assert (Td : tied (ins p c (sp g c) (sr g' c)) (inst_of dy)).
           { apply (proj2 (tied_dof_l _ _ _ _ Ddd)). left. exists x. split; [rewrite Icd'; exact Ixg|exact Ixy]. }
           destruct (Nat.eq_dec (sp g c) (sp g' c)) as [Ej|Nj].
           ++ apply (plc_free _ _ _ _ _ _ _ _ Fd). exists (ek EY), (tm (f iy)), dy. split; [exact Pyi|].
              split; [exact Oyi|]. split; [lia|]. rewrite Ej. exact Fy.
           ++ pose proof (fx_read l g tau (l ++ F') g' (tm (f iy)) c k i gt iy Co Co' It Pk Lt ltac:(lia) Liy Agd ltac:(lia) Ag' Cg' Fd Cj) as FxD.
              destruct (first_at_before _ _ _ _ _ _ _ _ Fy (sp g c) Lpd ltac:(lia) (dof_exec _ _ _ Ddd) FxD Td) as (kq & tq & dq & Pq & Oq & Lq & Fq).
              apply (plc_free _ _ _ _ _ _ _ _ Fd). exists kq, tq, dq. split; [exact Pq|]. split; [exact Oq|]. split; [lia|exact Fq].
    + (* another context *)
      destruct (fwd l g tau (ec EY) (ek EY) iy (TF dy) IHy Co Ity Gp ltac:(lia)) as [Rc|[(j' & Lj' & Fj')|(F' & g' & S' & X' & Co' & Fp & Cg')]].
      * exact Rc.
      * destruct (proj1 (srun_pos p W l g Rl (ec EY) j') Lj') as (q' & e' & Q' & X'' & K'').
        destruct (writes_x e' x) eqn:We'.
        -- (* y's SC write comes before w: they race *)
           assert (Lq'w : q' < qw).
           { destruct (Nat.lt_trichotomy q' qw) as [X1|[X1|X1]]; auto.
             - subst q'. rewrite Q' in Qw. injection Qw as <-. congruence.
             - rewrite (After q' e' X1 Q') in We'. discriminate. }
           assert (Ge : pcs sb (ec EY) <= j').
           { apply (place_ge p f nb T W Wc (ec EY) (ek EY) iy (TF dy) nb (sr g (ec EY)) j' Ity ltac:(lia) (le_n _) Gp); [|exact Fj'].
             intros z Lz. apply (CONS_rg _ _ _ Co). auto. }
           assert (Lq' : length lb <= q').
           { destruct (Nat.lt_ge_cases q' (length lb)) as [X1|X1]; auto. exfalso.
             rewrite El in Q'. rewrite nth_error_app1 in Q' by auto.
             pose proof (lb_pass q' e' Q') as P'. rewrite X'', K'' in P'. lia. }
           unfold writes_x in We'. destruct (sacc e') as [[ys1 wy1]|] eqn:Sae; [|discriminate]. destruct wy1; [|discriminate].
           apply existsb_exists in We'. destruct We' as (z & Iz & Z). apply Nat.eqb_eq in Z. subst z.
           exists (firstn qw l ++ [w]), g1. split; [exact Rl1|].
           apply (racy_g_mk p _ q' qw e' w x ys1 ys true true Lq'w ltac:(rewrite Qlo by lia; exact Q') Qw1
                    ltac:(rewrite X'', Ec; exact Ncy) Sae Aw Iz Ixw eq_refl (NoG q' _ _ Lq')).
           intros (_ & Fw). apply NoFa. rewrite Ec in Fw. exact Fw.
        -- (* y's SC instruction did not write: a CAS that failed in the SC run *)
           apply (pend_passed tau l g (ec EY) (ek EY) iy dy By uy EY x j' IHy Co Eay Gp ltac:(lia) AEY WY ltac:(rewrite EIY; exact ICY)).
           ++ intros q e _ Q Xe Ke.
              rewrite (srun_slot_unique l g q q' e e' Rl Q Q' ltac:(congruence) ltac:(congruence)) in Q.
              rewrite Q in Q'. injection Q' as <-. exact We'.
           ++ exact Lj'.
           ++ exact Fj'.
      * apply (pend_reached tau l g c d x (ec EY) (ek EY) iy dy By uy EY F' g' IHy Co Dd Ncy Ix Eay Gp ltac:(lia) AEY WY
                 ltac:(rewrite EIY; exact ICY) S' X' Co' Fp Cg').
Qed.

Theorem core : forall tau, HC tau.
Proof.
  intros tau. induction tau as [tau IHt] using lt_wf_ind.
  intros l g c k i gt Co It Pk Lt Ld Fpl NoFa Cj Mis.
  pose proof (item_i p f nb c k i gt It) as Li.
  assert (X1b : Ext (f (S i)) sb) by (apply (tr_ext p f nb T); lia).
  destruct (item_ent c k i gt It) as (ER & AR1 & XR & KR).
  pose proof (x_ent _ _ X1b _ _ AR1) as AR.
  (* the read's instruction in the run *)
  assert (IR : exists iR, einstr p sb ER = iR /\ xload iR (rgof sb ER) = true /\ icells iR = icells (tinst gt) /\ is_cas iR = is_cas (tinst gt)).
  { unfold einstr, rgof. rewrite XR, KR.
    destruct (item_pending p f nb T W c k i gt nb It Li (le_n _) Pk) as [(d & -> & (_ & _ & P3) & _)|(xs & -> & (_ & Ph & Cx) & _)].
    - exists (inst_of d). rewrite P3. split; [reflexivity|]. split; [|split; reflexivity]. unfold xload.
      simpl in Ld. rewrite Ld. destruct d; reflexivity.
    - destruct (oc (cs sb c) k) as [t2|] eqn:O2.
      + destruct (proj1 (i_pend p sb Ib1 c k Pk ltac:(rewrite O2; discriminate))) as (dk & Ak & _).
        rewrite Ak in Cx |- *. destruct dk as [| |mk xk ek nk|]; simpl in Cx; try discriminate. injection Cx as -> ->.
        exists (inst_of (DCas Plain xs ek nk)). split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
      + destruct (oh (cs sb c) k) as [t1|] eqn:O1; [|congruence].
        destruct (i_half p sb Ib1 c k t1 O2 O1 Pk) as (_ & (xs' & Ax) & _). rewrite Ax in Cx |- *. injection Cx as <-.
        exists (crd Plain xs'). split; [reflexivity|]. split; [reflexivity|]. split; reflexivity. }
  destruct IR as (iR & EiR & XlR & IcR & CsR).
  assert (XaR : xacc p sb ER) by (right; exists iR; split; auto).
  destruct (j_val p sb Ib2 _ ER _ AR EiR) as [V _]. specialize (V XlR). rewrite XR, KR in V.
  (* a cell where the SC value and the run's value differ *)
  assert (Ex : exists x, In x (icells iR) /\ sm g x <> rdv sb (erf ER) x).
  { destruct (existsb (fun x => negb (Nat.eqb (sm g x) (rdv sb (erf ER) x))) (icells iR)) eqn:Eb.
    - apply existsb_exists in Eb. destruct Eb as (x & Ix & Nx). exists x. split; auto.
      apply negb_true_iff in Nx. apply Nat.eqb_neq in Nx. exact Nx.
    - exfalso. apply Mis. rewrite (rval_iscas (tinst gt) iR (rg (cs sb c) k) (eq_sym CsR)), V, <- IcR. f_equal. unfold rdvs. apply map_ext_in. intros x Ix.
      destruct (Nat.eqb_spec (sm g x) (rdv sb (erf ER) x)) as [E|N]; auto. exfalso.
      assert (existsb (fun x => negb (Nat.eqb (sm g x) (rdv sb (erf ER) x))) (icells iR) = true).
      { apply existsb_exists. exists x. split; auto. apply negb_true_iff. apply Nat.eqb_neq. auto. }
      congruence. }
  destruct Ex as (x & Ix0 & Misx).
  assert (Ixg : In x (icells (tinst gt))) by (rewrite <- IcR; exact Ix0).
  (* the read in the event graph *)
  destruct (o_eRC p sb IOb _ ER AR) as [ERr ECr].
  assert (RdR : In x (eR ER)).
  { rewrite ERr. unfold evR. rewrite EiR. change (is_load iR && icond iR (rgof sb ER)) with (xload iR (rgof sb ER)).
    rewrite XlR. exact Ix0. }
  assert (CR : In x (eC ER)).
  { rewrite ECr. unfold evC. rewrite EiR. unfold xload in XlR. apply andb_prop in XlR as [Lr Cd].
    rewrite Cd. destruct iR; simpl in Lr; try discriminate; exact Ix0. }
  assert (MissE : forall w, In w (ids (hs sb x)) -> w <> tm (f i) ->
            (erf ER x = None \/ exists y, erf ER x = Some y /\ older (hs sb x) y w) ->
            gedge sb (tm (f i)) w /\ cedge sb x (tm (f i)) w).
  { intros w Iw N M. split.
    - right; left. exists ER, x. split; [exact AR|]. split; [exact RdR|]. split; [exact Iw|]. split; [auto|].
      destruct M as [M|(y & M1 & M2)]; rewrite ?M, ?M1; auto.
    - right; left. exists ER. split; [exact AR|]. split; [exact RdR|]. split; [exact Iw|]. split; [auto|].
      destruct M as [M|(y & M1 & M2)]; rewrite ?M, ?M1; auto. }
  assert (Acc : match gt with TF d => isaccd d = true | TH _ _ => True end).
  { destruct gt as [d0|m0 xs0]; [|exact I]. apply (cells_accd x). exact Ixg. }
  destruct (tat_dof _ _ _ (plc_tat _ _ _ _ _ _ _ _ Fpl) Acc) as (d & Dd & Icd & _).
  assert (Ix : In x (icells (inst_of d))) by (rewrite Icd; exact Ixg).
  set (eS := fst (snext p bs g c)). set (gR := snd (snext p bs g c)).
  assert (StR : sstep p g eS gR) by apply snext_step.
  assert (XeR : sx eS = c) by apply snext_x.
  destruct (snext_acc p bs g c d Dd) as (wR & AR' & GR). fold eS in AR', GR.
  assert (KeR : sk eS = sp g c) by (destruct (sstep_shape p W _ _ _ StR) as (? & _ & _ & Hk & _); rewrite Hk, XeR; auto).
  assert (Rl : srun p l g) by apply (CONS_run _ _ _ Co).
  assert (R2 : srun p (l ++ [eS]) gR) by (econstructor; eauto).
  assert (QR : nth_error (l ++ [eS]) (length l) = Some eS) by apply nth_app_last'.
  (* a race between a write of l and the read *)
  assert (Race : forall q w ys, nth_error l q = Some w -> sacc w = Some (ys, true) -> In x ys -> sx w <> c ->
            ~ gsync (l ++ [eS]) q (length l) (sx w) c -> RACY p).
  { intros q w ys Q Aw Ixw Nc Ng. exists (l ++ [eS]), gR. split; [auto|].
    apply (racy_g_mk p (l ++ [eS]) q (length l) w eS x ys (icells (inst_of d)) true wR).
    - apply nth_error_Some. congruence.
    - rewrite nth_app_old' by (apply nth_error_Some; congruence). auto.
    - auto.
    - congruence.
    - auto.
    - auto.
    - exact Ixw.
    - exact Ix.
    - reflexivity.
    - rewrite XeR. auto.
    - intros (_ & Fa). rewrite XeR, KeR in Fa. apply NoFa. exact Fa. }
  (* the source *)
  assert (Src : forall y, erf ER x = Some y ->
            (forall q e, length lb <= q -> nth_error l q = Some e -> writes_x e x = false) ->
            (forall q e, nth_error lb q = Some e -> writes_x e x = true -> bt sb (sx e) (sk e) = y -> RACY p) ->
            RACY p).
  { intros y Ey NoW InB.
    destruct (j_rf p sb Ib2 _ ER x y AR Ey) as (Ly & _ & _ & Hy).
    destruct (j_hist p sb Ib2 x y Hy) as (EY & iy0 & AY & WY & EIY & ICY).
    destruct (i_et p sb Ib1 y EY AY) as (_ & OY). assert (EhY : eh EY = false) by (destruct (j_ew p sb Ib2 _ EY _ AY eq_refl) as [W1 _]; rewrite WY in W1; destruct (eh EY); [discriminate|reflexivity]). rewrite EhY in OY.
    destruct (Nat.lt_ge_cases (ek EY) (pcs sb (ec EY))) as [Lp|Gp].
    - assert (REY : RE sb (ec EY) (ek EY) EY) by (unfold RE, bt, tmo; rewrite OY; auto).
      destruct (lb_has_write (ec EY) (ek EY) EY x Lp REY WY ltac:(rewrite EIY; auto)) as (q & e & Q & Xe & Ke & We).
      apply (InB q e Q We). rewrite Xe, Ke. unfold bt, tmo. rewrite OY. reflexivity.
    - destruct (early_of_pending p f nb T nb (ec EY) (ek EY) y ltac:(lia) Gp OY) as (iy & dy & By & uy & Eay & Liy & Tiy).
      assert (Lty : tm (f iy) < tm (f i)) by (rewrite Tiy; exact Ly).
      apply (pend_src tau l g c k i gt x (ec EY) (ek EY) iy dy By uy EY (IHt (tm (f iy)) ltac:(lia)) Co It Pk Lt Fpl Cj Eay Gp Lty);
        [rewrite Tiy; exact AY|exact WY|rewrite EIY; exact ICY|exact Ixg|exact NoW]. }
  destruct (lw l x) as [w|] eqn:Lw.
  - destruct (lw_spec l x w Lw) as (qw & Qw & Ww & After).
    assert (Aw : exists ys, sacc w = Some (ys, true) /\ In x ys).
    { unfold writes_x in Ww. destruct (sacc w) as [[ys []]|]; try discriminate.
      exists ys. split; auto. apply existsb_exists in Ww. destruct Ww as (z & Z & Q). apply Nat.eqb_eq in Q. subst. auto. }
    destruct Aw as (ys & Aw & Ixw).
    destruct (Nat.lt_ge_cases qw (length lb)) as [Lq|Gq].
    + (* a base write *)
      assert (Qb : nth_error lb qw = Some w) by (pose proof Co as (F & El & _); rewrite El in Qw; rewrite nth_error_app1 in Qw by auto; auto).
      pose proof (sm_base l g tau qw w x Co Lw Qw Lq) as SV.
      destruct (lb_write qw w x Qb Ww) as (EW & REW & WEW & IcW & InW & VW).
      (* the read cannot miss w *)
      assert (Key : (erf ER x = None \/ exists y, erf ER x = Some y /\ older (hs sb x) y (bt sb (sx w) (sk w))) -> RACY p).
      { intros M. pose proof REW as (AW & XW & KW).
        assert (Nt : bt sb (sx w) (sk w) <> tm (f i)).
        { intros Z. rewrite Z in AW. rewrite AR in AW. injection AW as <-.
          pose proof (lb_pass qw w Qb) as Pw. rewrite XR in XW. rewrite KR in KW. rewrite <- XW, <- KW in Pw. lia. }
        destruct (MissE _ InW Nt M) as [MG MC].
        destruct (Nat.eq_dec (sx w) c) as [Ec|Nc].
        - (* the same context: the read comes after the write in the cell *)
          exfalso.
          destruct (lb_ev qw w Qb ltac:(apply (lb_exec qw w Qb); rewrite Aw; discriminate)) as (EW' & REW' & Eiw & Saw & _).
          assert (EW' = EW) by (destruct REW as (A1 & _); destruct REW' as (A2 & _); congruence). subst EW'.
          rewrite Aw in Saw. destruct (icond _ _ && isacc _) eqn:Cw; [|discriminate].
          apply andb_prop in Cw as [Cw1 Cw2]. injection Saw as Ys _.
          assert (Exw : executes (ins p c (sk w) (rrg sb c)) (rrg sb c) = true) by (rewrite <- Ec; unfold executes; rewrite Cw2; exact Cw1).
          assert (Tt : tied (ins p c (sk w) (rrg sb c)) (tinst gt)).
          { left. exists x. split; [rewrite <- Ec; first [rewrite <- Ys | rewrite Ys]; exact Ixw|exact Ixg]. }
          pose proof (lb_pass qw w Qb) as Pw. rewrite Ec in Pw.
          pose proof (tied_before l g tau c k i gt (sk w) Co It Pk Fpl Pw Exw Tt) as Lw'.
          assert (CW : In x (eC EW)) by (apply (ew_eC _ EW x AW WEW IcW)).
          apply (proj2 EVb x (bt sb (sx w) (sk w))). apply t_trans with (tm (f i)); [|constructor; exact MC].
          constructor. right; right; right; right. exists EW, ER. split; [exact AW|]. split; [exact AR|].
          split; [congruence|]. split; [lia|]. split; [exact CW|exact CR].
        - destruct (gsync_dec (l ++ [eS]) qw (length l) (sx w) c) as [G|Ng]; [|exact (Race qw w ys Qw Aw Ixw Nc Ng)].
          exfalso.
          pose proof (know_base l g tau c k i gt qw w EW ER eS Co It Pk Fpl Lq Qw ltac:(exists ys, true; exact Aw)
                        REW AR XR XaR GR Nc G) as Kn.
          assert (PW : eQ ER (bt sb (sx w) (sk w)))
            by (apply Kn; unfold esrc, srcv, vor; right; rewrite WEW; rewrite (n_et p sb Rb W _ _ _ REW); reflexivity).
          apply (proj1 EVb (bt sb (sx w) (sk w))). apply t_trans with (tm (f i)); [|constructor; exact MG].
          constructor. right; right. exists ER. split; [exact AR|]. split; [exact PW|exact Nt]. }
      destruct (erf ER x) as [y|] eqn:Ey; [|apply Key; left; reflexivity].
      destruct (Nat.eq_dec y (bt sb (sx w) (sk w))) as [Eqy|Ney].
      { exfalso. apply Misx. rewrite SV. unfold rdv. rewrite Ey, Eqy. reflexivity. }
      destruct (j_rf p sb Ib2 _ ER x y AR Ey) as (_ & _ & _ & Iny).
      destruct (older_total (hs sb x) y (bt sb (sx w) (sk w)) Iny InW Ney) as [Ol|Ol];
        [apply Key; right; exists y; auto|].
      apply (Src y eq_refl).
      * intros q e Lq' Q'. apply (After q e); [lia|auto].
      * intros q e Q We By0. exfalso.
        assert (Ql : nth_error l q = Some e) by (pose proof Co as (F & El & _); rewrite El; rewrite nth_error_app1; [auto|apply nth_error_Some; congruence]).
        destruct (Nat.lt_trichotomy q qw) as [Lt'|[Eq'|Gt']].
        -- pose proof (Bco q qw e w x Lt' Q Qb We Ww) as Co'. rewrite By0 in Co'.
           apply (older_asym _ _ _ (j_nodup p sb Ib2 x) Ol Co').
        -- subst q. rewrite Q in Qb. injection Qb as <-. rewrite By0 in Ney. congruence.
        -- rewrite (After q e Gt' Ql) in We. discriminate.
    + (* a write of the segments *)
      assert (Iw : In w (skipn (length lb) l)).
      { pose proof Co as (F & El & _). rewrite El, skipn_app, skipn_all2 by lia. rewrite Nat.sub_diag. simpl.
        rewrite El in Qw. rewrite nth_error_app2 in Qw by auto. apply nth_error_In in Qw. auto. }
      destruct (Nat.eq_dec (sx w) c) as [Ec|Nc].
      { (* the read's own context: forwarding from an earlier pending write *)
        apply (own_fwd tau l g c k i gt d x ER qw w ys IHt Co It Pk Lt Fpl Cj AR XR KR Ixg Ix CR Dd Misx MissE Lw Qw
                 After ltac:(lia) Aw Ixw Ec). }
      apply (Race qw w ys Qw Aw Ixw Nc).
      intros (a & b & f1 & f2 & L1 & L2 & L3 & F1 & F2 & S1 & S2 & X1 & X2).
      destruct (Nat.eq_dec a (length l)) as [Ea'|Na].
      * subst a. rewrite QR in F1. injection F1 as <-. congruence.
      * assert (La : a < length l) by lia. rewrite nth_app_old' in F1 by auto.
        pose proof Co as (F & El & SF & GF & _). rewrite El in F1, La.
        rewrite nth_error_app2 in F1 by lia. apply nth_error_In in F1. rewrite (GF f1 F1) in S1. discriminate.
  - (* no SC write: the read takes the initial value, or its source is pending *)
    pose proof (lw_none l x Lw) as Nw.
    rewrite (proj1 (srun_mem p W l g Rl x) Lw) in Misx.
    destruct (erf ER x) as [y|] eqn:Ey; [|exfalso; apply Misx; unfold rdv; rewrite Ey; reflexivity].
    apply (Src y eq_refl).
    + intros q e _ Q. apply (Nw q e Q).
    + intros q e Q We _. exfalso. pose proof Co as (F & El & _).
      assert (Ql : nth_error l q = Some e) by (rewrite El; rewrite nth_error_app1; [auto|apply nth_error_Some; congruence]).
      rewrite (Nw q e Ql) in We. discriminate.
Qed.

End Core.
