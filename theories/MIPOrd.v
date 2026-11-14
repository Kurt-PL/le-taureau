(* Model2: the replay order for mixed cells over the slots a run has
   passed, and that it has no cycle when the reach (STEP has) no access before itself.
   An access is fenced in the reach (STEP (fz)) when the instructions just before and
   just after it are guard(); every fenced access slot (fa) is fenced in the
   run. The order relation:
   - programme order;
   - settle order between nodes that are not fenced accesses;
   - coherence in a cell (reads-from, write order, from-read) between fenced
     accesses. *)
From Stdlib Require Import Arith Lia List Bool Permutation Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO MIPComp M2Lit MIPNeg M2SC MIReplay M2Ev Topo MIPFSC.
Require Import M2Iface.

Section Iface.
Context `{IFM : Model}.

Set Default Proof Using "All".
Section MXO.
Variable p : prog.
Variable s : M2Model.st.
Hypothesis R : reach (STEP p) s.
Hypothesis W : wf p.
Hypothesis EV : evok s.

Local Abbreviation bt := (bt s).
Local Abbreviation rrg := (rrg s).
Local Abbreviation iof := (MIPFSC.iof p s).
Local Abbreviation acc := (MIPFSC.acc p s).
Local Abbreviation cells := (MIPFSC.cells p s).
Local Abbreviation rd := (MIPFSC.rd p s).
Local Abbreviation T := (MIPFSC.T s).
Local Abbreviation eofn := (MIPFSC.eofn s).
Local Abbreviation wr := (MIPFSC.wr s).
Local Abbreviation srcx := (MIPFSC.srcx s).
Local Abbreviation hx := (MIPFSC.hx s).
Local Abbreviation ixs := (MIPFSC.ixs s).
Local Abbreviation ixw := (MIPFSC.ixw s).
Local Abbreviation combx := (MIPFSC.combx p s).
Local Abbreviation comb := (MIPFSC.comb p s).
Local Abbreviation L := (MIPFSC.L s).
Local Abbreviation node_E := (MIPFSC.node_E p s R W).
Local Abbreviation acc_rd_wr := (MIPFSC.acc_rd_wr p s R W).
Local Abbreviation wr_hist := (MIPFSC.wr_hist p s R W).
Local Abbreviation rd_src := (MIPFSC.rd_src p s R W).
Local Abbreviation acc_lt := (MIPFSC.acc_lt p s R W).

Lemma IO : InvO p s. Proof. apply (iaoO p s (IAOg p s R)). Qed.
Local Abbreviation I2' := (nI2 p s R W).
Local Abbreviation I3' := (nI3 p s R W).

(* the fences around an access *)
Definition fnode (n : node) : Prop :=
  1 <= snd n /\ ins p (fst n) (snd n - 1) (rrg (fst n)) = IFn FFull /\ ins p (fst n) (S (snd n)) (rrg (fst n)) = IFn FFull.

(* the node's guard() after it has been passed *)
Definition closed (n : node) : Prop := S (snd n) < pcs s (fst n).
Definition pt (n : node) : nat := bt (fst n) (snd n - 1).
Definition qt (n : node) : nat := bt (fst n) (S (snd n)).

Lemma acc_exec : forall n, acc n = true -> executes (iof n) (rrg (fst n)) = true.
Proof.
  intros n A. unfold MIPFSC.acc in A. apply andb_prop in A. destruct A as [A1 A2].
  apply andb_prop in A1. destruct A1 as [_ A1]. unfold executes. fold (iof n). rewrite A1. exact A2.
Qed.

Lemma acc_isacc : forall n, acc n = true -> isacc (iof n) = true.
Proof. intros n A. destruct (node_E n A) as (E & Ia & _). exact Ia. Qed.

Lemma xacc_node : forall n E, acc n = true -> eofn n = Some E -> RE s (fst n) (snd n) E -> einstr p s E = iof n -> xacc p s E.
Proof.
  intros n E A Eo RE0 Ei. destruct (rd n) eqn:Rn.
  - right. exists (iof n). split; auto. rewrite (n_rgof p s R W _ _ E RE0). exact Rn.
  - left. pose proof (acc_rd_wr n A Rn) as Wn. unfold MIPFSC.wr in Wn. rewrite Eo in Wn. exact Wn.
Qed.

Lemma pt_lt_qt_z : forall n, acc n = true -> fnode n -> closed n -> pt n < qt n.
Proof.
  intros n A FNn Cl. destruct FNn as (L & F1 & F2). pose proof (acc_lt n A) as Ln.
  unfold pt, qt.
  assert (T1 : bt (fst n) (snd n - 1) < bt (fst n) (snd n)).
  { apply (n_tie p s R W (fst n) (snd n - 1) (snd n) _ _ ltac:(lia) F1 eq_refl eq_refl (acc_exec n A)); auto.
    right; left; reflexivity. }
  assert (T2 : bt (fst n) (snd n) < bt (fst n) (S (snd n))).
  { apply (n_tie p s R W (fst n) (snd n) (S (snd n)) _ _ ltac:(lia) eq_refl F2 (acc_exec n A) eq_refl); auto.
    right; right; left; reflexivity. }
  lia.
Qed.

Lemma po_time_z : forall a b, acc a = true -> acc b = true -> fnode a -> fnode b -> fst a = fst b -> snd a < snd b -> qt a <= pt b.
Proof.
  intros [c ka] [c' kb] A B FA FB E L. simpl in *. subst c'.
  pose proof (acc_lt _ B) as Lb'. simpl in Lb'.
  destruct FA as (La & Fa1 & Fa2). destruct FB as (Lb & Fb1 & Fb2). simpl in *.
  unfold qt, pt. simpl.
  assert (Nk : kb <> S ka).
  { intros ->. pose proof (acc_isacc _ B) as Ia. unfold MIPFSC.iof in Ia. simpl in Ia. rewrite Fa2 in Ia. discriminate. }
  destruct (Nat.eq_dec (S ka) (kb - 1)) as [Q|Q]; [rewrite Q; lia|].
  apply Nat.lt_le_incl. apply (n_tie p s R W c (S ka) (kb - 1) _ _ ltac:(lia) Fa2 Fb1 eq_refl eq_refl); [|lia].
  right; left; reflexivity.
Qed.

(* the guard() right after an access, and what passes through it *)
Lemma through_guard : forall a b Ea Eb, acc a = true -> acc b = true -> fnode a -> MIPFSC.pob a b = true ->
  eofn a = Some Ea -> eofn b = Some Eb ->
  vsub (vor (eP Ea) (esrc Ea)) (eQ Eb) /\ T a < T b.
Proof.
  intros [c ka] [c' kb] Ea' Eb' A B FA Po Eao Ebo. unfold MIPFSC.pob in Po. simpl in Po.
  apply andb_prop in Po. destruct Po as [E1 L1]. apply Nat.eqb_eq in E1. apply Nat.ltb_lt in L1. subst c'.
  destruct (node_E _ A) as (Ea & _ & _ & REa & Eia & Eoa). rewrite Eoa in Eao. injection Eao as <-.
  destruct (node_E _ B) as (Eb & Ib & _ & REb & Eib & Eob). rewrite Eob in Ebo. injection Ebo as <-.
  destruct FA as (_ & _ & Fa). simpl in Fa. pose proof (acc_lt _ B) as Lb. simpl in Lb.
  assert (Nkb : S ka <> kb).
  { intros <-. unfold MIPFSC.iof in Ib. simpl in Ib. rewrite Fa in Ib. discriminate. }
  destruct (n_ent p s R W c (S ka) _ Fa ltac:(lia) eq_refl) as (Ef & REf & Eif).
  assert (Taf : bt c ka < bt c (S ka)).
  { apply (n_tie p s R W c ka (S ka) _ _ ltac:(lia) eq_refl Fa (acc_exec _ A) eq_refl); [|lia].
    right; right; left; reflexivity. }
  assert (Tfb : bt c (S ka) < bt c kb).
  { apply (n_tie p s R W c (S ka) kb _ _ ltac:(lia) Fa eq_refl eq_refl (acc_exec _ B)); [right; left; reflexivity|lia]. }
  destruct REa as (A1 & B1 & C1). destruct REf as (A2 & B2 & C2). destruct REb as (A3 & B3 & C3). simpl in *.
  destruct (k_Ppair p s I3' _ Ea _ Ef A1 A2 ltac:(congruence) Taf) as [K1 K2].
  assert (Xg : xg p s Ef) by (exists (IFn FFull); split; [exact Eif|reflexivity]).
  assert (Xb : xacc p s Eb) by (apply (xacc_node (c, kb) Eb B Eob); [repeat split; auto|exact Eib]).
  pose proof (o_gpair p s IO _ Ef _ Eb A2 A3 ltac:(congruence) Tfb Xg Xb) as K3.
  split; [|unfold MIPFSC.T; simpl; lia].
  intros y [Y|Y]; apply K3; [apply K1|apply K2]; exact Y.
Qed.

(* what a fenced access knows in order of a fenced access whose guard() after
   it comes no later than its own guard() before it *)
Lemma back_z : forall a b Ea Eb, acc a = true -> acc b = true -> fnode a -> fnode b -> closed b ->
  eofn a = Some Ea -> eofn b = Some Eb -> qt b <= pt a ->
  forall y, vor (vor (eP Eb) (esrc Eb)) (gk p s (T b)) y -> eQ Ea y /\ y < T a.
Proof.
  intros a b Ea' Eb' A B FA FB Clb Ea0 Eb0 L.
  pose proof (acc_lt a A) as La'. pose proof (acc_lt b B) as Lb'.
  destruct (node_E a A) as (Ea & _ & _ & REa & Eia & Eoa). rewrite Eoa in Ea0. injection Ea0 as <-.
  destruct (node_E b B) as (Eb & _ & _ & REb & Eib & Eob). rewrite Eob in Eb0. injection Eb0 as <-.
  destruct FA as (La & Fa1 & _). destruct FB as (_ & _ & Fb2).
  destruct (n_ent p s R W (fst a) (snd a - 1) _ Fa1 ltac:(lia) eq_refl) as (Fa & REFa & EiFa).
  destruct (n_ent p s R W (fst b) (S (snd b)) _ Fb2 Clb eq_refl) as (Fb & REFb & EiFb).
  destruct (n_po p s R W (fst b) (snd b) (S (snd b)) _ _ Eb Fb ltac:(lia) eq_refl Fb2 (acc_exec b B)
              ltac:(right; right; left; reflexivity) Clb REb REFb) as [K0 K1].
  assert (PFb : forall y, vor (vor (eP Eb) (esrc Eb)) (gk p s (T b)) y -> eP Fb y).
  { intros y [[Y|Y]|(_ & _ & Fy)]; [apply K0; exact Y|apply K1; exact Y|].
    pose proof REFb as (Ab & _ & _). apply (Fy _ Fb Ab).
    - unfold MIPFSC.T. apply (n_tie p s R W (fst b) (snd b) (S (snd b)) _ _ ltac:(lia) eq_refl Fb2 (acc_exec b B) eq_refl
        ltac:(right; right; left; reflexivity) Clb).
    - apply (n_xg p s R W _ _ _ _ REFb EiFb); reflexivity. }
  assert (KF : vsub (eP Fb) (eP Fa)).
  { unfold qt, pt in L.
    destruct (Nat.eq_dec (bt (fst b) (S (snd b))) (bt (fst a) (snd a - 1))) as [Eq|Lt].
    - destruct (bt_inj p s R W _ _ _ _ _ _ (insr_of p s R W _ _ Clb) (insr_of p s R W (fst a) (snd a - 1) ltac:(lia)) ltac:(rewrite Fb2; reflexivity) ltac:(rewrite Fa1; reflexivity) Eq) as [E1 E2].
      assert (Fb = Fa).
      { destruct REFb as (A1 & _). destruct REFa as (A2 & _). rewrite E1, E2 in A1. congruence. }
      subst Fb. intros w Hw. exact Hw.
    - assert (G1 : xg p s Fb) by (apply (n_xg p s R W _ _ _ _ REFb EiFb); reflexivity).
      assert (G2 : xg p s Fa) by (apply (n_xg p s R W _ _ _ _ REFa EiFa); reflexivity).
      destruct (n_G p s R W _ _ _ _ Fb Fa REFb REFa G1 G2 ltac:(lia)) as [K2 _]. exact K2. }
  assert (Tfa : bt (fst a) (snd a - 1) < bt (fst a) (snd a)).
  { apply (n_tie p s R W (fst a) (snd a - 1) (snd a) _ _ ltac:(lia) Fa1 eq_refl eq_refl (acc_exec a A)); [right; left; reflexivity|auto]. }
  destruct REFa as (A2 & B2 & C2). destruct REa as (A3 & B3 & C3).
  assert (Xg : xg p s Fa) by (exists (IFn FFull); split; [exact EiFa|reflexivity]).
  assert (Xa : xacc p s Ea) by (apply (xacc_node a Ea A Eoa); [repeat split; auto|exact Eia]).
  pose proof (o_gpair p s IO _ Fa _ Ea A2 A3 ltac:(congruence) Tfa Xg Xa) as K3.
  intros y Y. assert (Py : eP Fa y) by (apply KF; apply PFb; exact Y).
  split; [apply K3; exact Py|]. pose proof (proj2 (j_eP p s I2' _ Fa y A2 Py)). unfold MIPFSC.T. lia.
Qed.

(* nothing enters a read's event but what it knows in order *)
Lemma into_read : forall t0 a, acc a = true -> wr a = false -> gedge s t0 (T a) ->
  exists Ea, eofn a = Some Ea /\ eQ Ea t0 /\ t0 <> T a.
Proof.
  intros t0 a A Wa G. destruct (node_E a A) as (Ea & _ & _ & REa & Eia & Eoa).
  assert (NH : forall x, ~ In (T a) (ids (hs s x))).
  { intros x I. destruct (j_hist p s I2' x (T a) I) as (e & i0 & H1 & H2 & _).
    assert (E' : ent s (T a) = Some Ea) by exact Eoa. rewrite E' in H1. injection H1 as <-.
    unfold MIPFSC.wr in Wa. rewrite Eoa, H2 in Wa. discriminate. }
  destruct G as [(x & O)|[(e & x & L & Ix & Ib & N & M)|(e & L & Q & N)]].
  - exfalso. apply (NH x). apply (proj2 (older_in _ _ _ O)).
  - exfalso. apply (NH x Ib).
  - exists Ea. split; auto. unfold MIPFSC.eofn, ent in Eoa. rewrite Eoa in L. injection L as <-. auto.
Qed.

(* a coherence edge between fenced accesses is an edge of the event graph *)
Lemma edge_com : forall a b, acc a = true -> acc b = true -> fnode a -> comb a b = true -> gedge s (T a) (T b).
Proof.
  intros a b A B FA Co. destruct (node_E a A) as (Ea & Ia & Ca & REa & Eia & Eoa).
  destruct (node_E b B) as (Eb & Ib & Cb & REb & Eib & Eob).
  apply (proj1 (MIPFSC.comb_x p s R W a b)) in Co. destruct Co as (x & Cx). unfold MIPFSC.combx in Cx.
  repeat (apply andb_prop in Cx; destruct Cx as [Cx ?]). rename H into Ox, H0 into Xb, H1 into Xa.
  apply inb_In in Xa, Xb.
  assert (NDx : NoDup (hx x)) by apply (n_nodup p s R W).
  apply orb_prop in Ox. destruct Ox as [Ox|Fr]; [apply orb_prop in Ox; destruct Ox as [Rf|Cw]|].
  - unfold MIPFSC.rfx in Rf. apply andb_prop in Rf. destruct Rf as [Rf Sy]. apply andb_prop in Rf. destruct Rf as [Wa Rb'].
    destruct (srcx b x) as [y|] eqn:Sb; [|discriminate]. apply Nat.eqb_eq in Sy. subst y.
    destruct (rd_src b x (T a) B Sb) as (Iy & _ & Ly).
    destruct (Nat.eq_dec (fst a) (fst b)) as [Ec|Nc].
    + assert (Po : MIPFSC.pob a b = true).
      { unfold MIPFSC.pob. rewrite Ec, Nat.eqb_refl. simpl. apply Nat.ltb_lt.
        destruct (Nat.lt_trichotomy (snd a) (snd b)) as [Lab|[Eab|Gab]]; auto.
        - exfalso. assert (a = b) by (destruct a, b; simpl in *; congruence). subst. lia.
        - exfalso. assert (T b < T a); [|lia]. unfold MIPFSC.T. rewrite <- Ec.
          apply (n_tie p s R W (fst a) (snd b) (snd a) _ _ Gab eq_refl eq_refl); [rewrite Ec; apply (acc_exec b B)|apply (acc_exec a A)| |].
          + left. exists x. split; [rewrite Ec; exact Xb|exact Xa].
          + apply (acc_lt a A). }
      destruct (through_guard a b Ea Eb A B FA Po Eoa Eob) as [K Lt].
      right; right. exists Eb. split; [exact Eob|]. split; [|lia]. apply K. right.
      unfold esrc, srcv. unfold MIPFSC.wr in Wa. rewrite Eoa in Wa. rewrite Wa. right.
      unfold vone. symmetry. rewrite (n_et p s R W _ _ Ea REa). reflexivity.
    + right; right. exists Eb. split; [exact Eob|]. split.
      * unfold MIPFSC.srcx in Sb. rewrite Eob in Sb.
        destruct REa as (A1 & B1 & C1). destruct REb as (A2 & B2 & C2).
        apply (o_rfe p s IO (T b) Eb x (T a) Ea A2 Sb A1). rewrite B1, B2. exact Nc.
      * lia.
  - unfold MIPFSC.cox in Cw. apply andb_prop in Cw. destruct Cw as [Cw L]. apply andb_prop in Cw. destruct Cw as [Wa Wb].
    apply Nat.ltb_lt in L. left. exists x. apply (pos_lt_older _ _ _ NDx); auto; apply wr_hist; auto.
  - unfold MIPFSC.frx in Fr. apply andb_prop in Fr. destruct Fr as [Fr L]. apply andb_prop in Fr. destruct Fr as [Fr Ne].
    apply andb_prop in Fr. destruct Fr as [Ra Wb]. apply Nat.ltb_lt in L.
    right; left. exists Ea, x. split; [exact Eoa|]. split.
    + destruct REa as (A1 & B1 & C1). destruct (o_eRC p s IO _ Ea A1) as [ER _]. rewrite ER.
      unfold evR. rewrite Eia. unfold rgof. rewrite B1.
      assert (Ra' : is_load (iof a) && icond (iof a) (rg (cs s (fst a))) = true) by exact Ra.
      rewrite Ra'. exact Xa.
    + split; [apply wr_hist; auto|]. split; [intros Z; apply (MIPFSC.bt_neq p s R W a b A B Ne); congruence|].
      unfold MIPFSC.ixs in L. unfold MIPFSC.srcx in L. rewrite Eoa in L.
      destruct (erf Ea x) as [u|] eqn:Eu; auto.
      assert (Su : srcx a x = Some u) by (unfold MIPFSC.srcx; rewrite Eoa; exact Eu).
      destruct (rd_src a x u A Su) as (Iu & _ & _).
      apply (pos_lt_older _ _ _ NDx); auto. apply wr_hist; auto.
Qed.

Definition isffull (i : instr) : bool := isfn FFull i.

(* the node is an access with guard() just before and just after it, in the run *)
Definition fnb (n : node) : bool :=
  Nat.leb 1 (snd n) && isffull (ins p (fst n) (snd n - 1) (rrg (fst n))) &&
  isffull (ins p (fst n) (S (snd n)) (rrg (fst n))).
Definition fz (n : node) : bool := acc n && fnb n.

Lemma isffull_eq : forall i, isffull i = true -> i = IFn FFull.
Proof. intros [| | |[| | | |]|] H; simpl in H; try discriminate; reflexivity. Qed.

Lemma fnb_fnode : forall n, fnb n = true -> fnode n.
Proof.
  intros n H. unfold fnb in H. apply andb_prop in H. destruct H as [H F2]. apply andb_prop in H. destruct H as [L1 F1].
  apply Nat.leb_le in L1. split; [exact L1|]. split; apply isffull_eq; auto.
Qed.

Lemma fa_fnb : forall c k, fa p c k -> fnb (c, k) = true.
Proof.
  intros c k (L1 & FF). destruct (FF (rrg c)) as [F1 F2]. unfold fnb. simpl. rewrite F1, F2.
  destruct k; [lia|reflexivity].
Qed.

Lemma fz_acc : forall n, fz n = true -> acc n = true.
Proof. intros n H. unfold fz in H. apply andb_prop in H. tauto. Qed.

Lemma fz_fnode : forall n, fz n = true -> fnode n.
Proof. intros n H. unfold fz in H. apply andb_prop in H. apply fnb_fnode. tauto. Qed.

Lemma chain_last_split : forall (f : node -> node -> bool) l1 b l2, chain node f (l1 ++ b :: l2) ->
  chain node f (l1 ++ [b]) /\ chain node f (b :: l2).
Proof.
  intros f l1 b l2 H. split.
  - apply (chain_prefix node f (l1 ++ [b]) l2). rewrite <- app_assoc. exact H.
  - apply (chain_suffix node f l1). exact H.
Qed.

Lemma chain_join : forall (f : node -> node -> bool) l1 b l2, chain node f (l1 ++ [b]) -> chain node f (b :: l2) ->
  chain node f (l1 ++ b :: l2).
Proof. intros. apply chain_app; auto. Qed.

Lemma cyc_path : forall (f : node -> node -> bool) a l, chain node f (a :: l ++ [a]) ->
  forall u x y v, a :: l ++ [a] = u ++ x :: y :: v ->
  y = x \/ exists q, chain node f (y :: q ++ [x]) /\ (forall n, In n q -> In n (a :: l ++ [a])).
Proof.
  intros f a l C u x y v E. rewrite E in C.
  destruct v as [|v0 v1] using rev_ind.
  - (* y is the last element, so y = a *)
    assert (Ya : y = a).
    { assert (G : last (a :: l ++ [a]) a = last (u ++ [x; y]) a) by (rewrite E; reflexivity).
      rewrite app_comm_cons, last_last in G. replace (u ++ [x; y]) with ((u ++ [x]) ++ [y]) in G by (rewrite <- app_assoc; reflexivity).
      rewrite last_last in G. auto. }
    subst y. destruct u as [|u0 u1].
    + simpl in E. injection E as Ex _. left. auto.
    + simpl in E. injection E as E0 E1. subst u0. right. exists u1. split.
      * apply (chain_prefix node f (a :: u1 ++ [x]) [a]).
        replace ((a :: u1 ++ [x]) ++ [a]) with ((a :: u1) ++ [x; a]) by (simpl; rewrite <- app_assoc; reflexivity). exact C.
      * intros n I. right. rewrite E1. apply in_app_iff. left. auto.
  - assert (Va : v0 = a).
    { assert (G : last (a :: l ++ [a]) a = last (u ++ x :: y :: v1 ++ [v0]) a) by (rewrite E; reflexivity).
      rewrite app_comm_cons, last_last in G. replace (u ++ x :: y :: v1 ++ [v0]) with ((u ++ x :: y :: v1) ++ [v0]) in G
        by (rewrite <- app_assoc; reflexivity). rewrite last_last in G. auto. }
    subst v0.
    assert (Cy : chain node f (y :: v1 ++ [a])).
    { apply (chain_suffix node f (u ++ [x])). replace ((u ++ [x]) ++ y :: v1 ++ [a]) with (u ++ x :: y :: v1 ++ [a])
        by (rewrite <- app_assoc; reflexivity). exact C. }
    destruct u as [|u0 u1].
    + simpl in E. injection E as Ex E1. subst x. right. exists v1. split; [exact Cy|].
      intros n I. right. rewrite E1. right. apply in_app_iff. left. auto.
    + simpl in E. injection E as E0 E1. subst u0. right. exists (v1 ++ a :: u1). split.
      2:{ intros n I. apply in_app_iff in I. destruct I as [I|[<-|I]]; [|left; auto|].
          - right. rewrite E1. apply in_app_iff. right. right. right. apply in_app_iff. left. auto.
          - right. rewrite E1. apply in_app_iff. left. auto. }
      assert (Cu : chain node f (a :: u1 ++ [x])).
      { apply (chain_prefix node f (a :: u1 ++ [x]) (y :: v1 ++ [a])).
        replace ((a :: u1 ++ [x]) ++ y :: v1 ++ [a]) with ((a :: u1) ++ x :: y :: v1 ++ [a])
          by (simpl; rewrite <- app_assoc; reflexivity). exact C. }
      replace (y :: (v1 ++ a :: u1) ++ [x]) with ((y :: v1) ++ a :: (u1 ++ [x])) by (simpl; rewrite <- app_assoc; reflexivity).
      apply chain_join; auto.
Qed.

Lemma esrc_rf : forall E x y, erf E x = Some y -> esrc E y.
Proof. intros E x y H. unfold esrc, srcv. left. exists x. exact H. Qed.

(* ---------- positions in the settle order ---------- *)
Fixpoint nidx (n : node) (l : list node) : nat :=
  match l with [] => 0 | x :: t => if Nat.eqb (fst n) (fst x) && Nat.eqb (snd n) (snd x) then 0 else S (nidx n t) end.

Lemma nidx_nth : forall l n, In n l -> nth_error l (nidx n l) = Some n.
Proof.
  induction l as [|x t IH]; intros [c k] I; [destruct I|]. simpl.
  destruct (Nat.eqb_spec c (fst x)); destruct (Nat.eqb_spec k (snd x)); simpl.
  - destruct x; simpl in *; subst; reflexivity.
  - destruct I as [->|I]; [simpl in *; congruence|]. apply IH; auto.
  - destruct I as [->|I]; [simpl in *; congruence|]. apply IH; auto.
  - destruct I as [->|I]; [simpl in *; congruence|]. apply IH; auto.
Qed.

Definition cmi (n : node) : nat := nidx n L.

Lemma cmi_entry : forall n, In n L -> exists tau, nth_error (cm s) (cmi n) = Some (fst n, snd n, tau).
Proof.
  intros n I. pose proof (nidx_nth L n I) as Q. unfold cmi. change (MIPFSC.L s) with (map (fun t => (fst (fst t), snd (fst t))) (cm s)) in Q |- *.
  rewrite nth_error_map in Q.
  destruct (nth_error (cm s) (nidx n (map (fun t => (fst (fst t), snd (fst t))) (cm s)))) as [[[c j] t]|] eqn:E;
    simpl in Q; [|discriminate].
  inversion Q. subst n. exists t. reflexivity.
Qed.

Lemma inL_of : forall c j, j < pcs s c -> In (c, j) L.
Proof.
  intros c j H. destruct (cm_has p s R W c j H) as (q & tau & T). unfold MIPFSC.L. apply in_map_iff.
  exists (c, j, tau). split; auto. eapply nth_error_In; eauto.
Qed.

Lemma cmi_po : forall a b, In a L -> In b L -> fst a = fst b -> snd a < snd b -> cmi a < cmi b.
Proof.
  intros [c ka] [c' kb] A B E Lt. simpl in *. subst c'.
  destruct (cmi_entry _ A) as (ta & Ta). destruct (cmi_entry _ B) as (tb & Tb). simpl in *.
  destruct (Nat.lt_trichotomy (cmi (c, ka)) (cmi (c, kb))) as [X|[X|X]]; auto.
  - rewrite X in Ta. rewrite Ta in Tb. injection Tb. lia.
  - pose proof (i_cmB p s (nI1 p s R W) _ _ c kb ka tb ta X Tb Ta). lia.
Qed.

Lemma cmi_po_le : forall a b, In a L -> In b L -> fst a = fst b -> snd a <= snd b -> cmi a <= cmi b.
Proof.
  intros a b A B E Le. destruct (Nat.eq_dec (snd a) (snd b)) as [Q|Q].
  - destruct a, b; simpl in *; subst; lia.
  - apply Nat.lt_le_incl. apply cmi_po; auto. lia.
Qed.

(* guard() slots are passed when they happen, so their settle order is their birth order *)
Lemma cmi_ff : forall a b, In a L -> In b L -> insr p s (fst a) (snd a) = Some (IFn FFull) ->
  insr p s (fst b) (snd b) = Some (IFn FFull) -> bt (fst a) (snd a) < bt (fst b) (snd b) -> cmi a < cmi b.
Proof.
  intros a b A B Ha Hb Lt.
  destruct (cmi_entry _ A) as (ta & Ta). destruct (cmi_entry _ B) as (tb & Tb).
  pose proof (cm_noacc p s R W _ _ _ ta _ Ta Ha eq_refl eq_refl) as Ea.
  pose proof (cm_noacc p s R W _ _ _ tb _ Tb Hb eq_refl eq_refl) as Eb.
  destruct (Nat.lt_trichotomy (cmi a) (cmi b)) as [X|[X|X]]; auto.
  - rewrite X in Ta. rewrite Ta in Tb. injection Tb. intros. subst. lia.
  - pose proof (i_cmC p s (nI1 p s R W) _ _ _ _ _ _ tb ta X Tb Ta). lia.
Qed.

(* ---------- keys: three slots per settle position ---------- *)
Definition fpre (n : node) : node := (fst n, snd n - 1).
Definition fpost (n : node) : node := (fst n, S (snd n)).
Definition closedb (n : node) : bool := Nat.ltb (S (snd n)) (pcs s (fst n)).
Definition key_in (n : node) : nat := if fz n then 3 * cmi (fpre n) + 2 else 3 * cmi n + 1.
(* a fenced access whose guard() after it is not yet passed has only coherence edges out *)
Definition key_out (n : node) : nat :=
  if fz n then (if closedb n then 3 * cmi (fpost n) else 3 * cmi n + 2) else 3 * cmi n + 1.

Lemma closedb_iff : forall n, closedb n = true <-> closed n.
Proof. intros n. unfold closedb, closed. apply Nat.ltb_lt. Qed.

Lemma fence_pre : forall n, fz n = true -> In (fpre n) L /\ insr p s (fst n) (snd n - 1) = Some (IFn FFull).
Proof.
  intros n Z. destruct (fz_fnode n Z) as (L1 & F1 & F2). pose proof (MIPFSC.acc_lt p s R W n (fz_acc n Z)) as Ln.
  split; [apply inL_of; unfold fpre; simpl; lia|]. rewrite (insr_of p s R W) by lia. rewrite F1. reflexivity.
Qed.

Lemma fence_post : forall n, fz n = true -> closed n -> In (fpost n) L /\ insr p s (fst n) (S (snd n)) = Some (IFn FFull).
Proof.
  intros n Z Cl. destruct (fz_fnode n Z) as (L1 & F1 & F2).
  split; [apply inL_of; exact Cl|]. rewrite (insr_of p s R W) by exact Cl. rewrite F2. reflexivity.
Qed.

Lemma key_node : forall n, In n L -> key_in n <= key_out n.
Proof.
  intros n I. unfold key_in, key_out. destruct (fz n) eqn:Z; [|lia].
  destruct (fence_pre n Z) as (I1 & _). destruct (fz_fnode n Z) as (L1 & _).
  destruct (closedb n) eqn:Cb.
  - destruct (fence_post n Z (proj1 (closedb_iff n) Cb)) as (I2 & _).
    pose proof (cmi_po (fpre n) (fpost n) I1 I2 eq_refl ltac:(unfold fpre, fpost; simpl; lia)). lia.
  - pose proof (cmi_po (fpre n) n I1 I eq_refl ltac:(unfold fpre; simpl; lia)). lia.
Qed.

(* programme order out of a fenced access passes its guard() after it *)
Lemma pob_closed : forall a b, In b L -> MIPFSC.pob a b = true -> fz a = true -> closed a.
Proof.
  intros a b B P Z. unfold MIPFSC.pob in P. apply andb_prop in P as [E Lt].
  apply Nat.eqb_eq in E. apply Nat.ltb_lt in Lt. destruct b as [cb kb]. simpl in *. subst cb.
  apply (proj1 (L_in p s R W (fst a) kb)) in B. unfold closed. lia.
Qed.

Lemma key_po : forall a b, In a L -> In b L -> pob a b = true -> key_out a < key_in b.
Proof.
  intros a b A B P. pose proof P as P0. unfold pob in P. apply andb_prop in P. destruct P as [E Lt].
  apply Nat.eqb_eq in E. apply Nat.ltb_lt in Lt. unfold key_out, key_in.
  destruct (fz a) eqn:Za; destruct (fz b) eqn:Zb.
  - pose proof (pob_closed a b B P0 Za) as Cl. rewrite (proj2 (closedb_iff a) Cl).
    destruct (fence_post a Za Cl) as (Ia & _). destruct (fence_pre b Zb) as (Ib & _).
    destruct (fz_fnode a Za) as (_ & _ & Fa2). destruct (fz_fnode b Zb) as (Lb & _).
    assert (Nk : snd b <> S (snd a)).
    { intros Q. pose proof (acc_isacc b (fz_acc b Zb)) as Ic. unfold MIPFSC.iof in Ic.
      rewrite Q, <- E in Ic. rewrite Fa2 in Ic. discriminate. }
    pose proof (cmi_po_le (fpost a) (fpre b) Ia Ib ltac:(unfold fpost, fpre; simpl; auto)
                  ltac:(unfold fpost, fpre; simpl; lia)). lia.
  - pose proof (pob_closed a b B P0 Za) as Cl. rewrite (proj2 (closedb_iff a) Cl).
    destruct (fence_post a Za Cl) as (Ia & _).
    pose proof (cmi_po_le (fpost a) b Ia B ltac:(unfold fpost; simpl; auto) ltac:(unfold fpost; simpl; lia)). lia.
  - destruct (fence_pre b Zb) as (Ib & _).
    pose proof (cmi_po_le a (fpre b) A Ib ltac:(unfold fpre; simpl; auto) ltac:(unfold fpre; simpl; lia)). lia.
  - pose proof (cmi_po a b A B E Lt). lia.
Qed.

Definition cmNb (a b : node) : bool := negb (fz a) && negb (fz b) && Nat.ltb (cmi a) (cmi b).
Definition comF (a b : node) : bool := fz a && fz b && comb a b.
Definition Rs (a b : node) : bool := MIPFSC.pob a b || cmNb a b || comF a b.

Lemma key_cmN : forall a b, cmNb a b = true -> key_out a < key_in b.
Proof.
  intros a b H. unfold cmNb in H. apply andb_prop in H. destruct H as [H L1]. apply andb_prop in H.
  destruct H as [Za Zb]. apply negb_true_iff in Za, Zb. apply Nat.ltb_lt in L1.
  unfold key_out, key_in. rewrite Za, Zb. lia.
Qed.

Lemma comF_comb : forall l, chain node comF l -> chain node comb l.
Proof.
  induction l as [|a l IH]; simpl; auto. destruct l as [|b l']; auto. intros [H1 H2]. split; auto.
  unfold comF in H1. apply andb_prop in H1. tauto.
Qed.

Lemma comF_ends : forall m a b, chain node comF (a :: m ++ [b]) -> fz a = true /\ fz b = true.
Proof.
  induction m as [|x m IH]; intros a b H.
  - destruct H as [H _]. unfold comF in H. apply andb_prop in H. destruct H as [H _]. apply andb_prop in H. exact H.
  - destruct H as [H1 H2]. destruct (IH x b H2) as [_ Zb]. unfold comF in H1.
    apply andb_prop in H1. destruct H1 as [H1 _]. apply andb_prop in H1. destruct H1 as [Za _]. split; [exact Za|exact Zb].
Qed.

Lemma comF_path : forall m a b, chain node comF (a :: m ++ [b]) -> clos_trans nat (gedge s) (T a) (T b).
Proof.
  assert (E1 : forall a b, comF a b = true -> gedge s (T a) (T b)).
  { intros a b H. unfold comF in H. apply andb_prop in H. destruct H as [H Cb]. apply andb_prop in H. destruct H as [Za Zb].
    apply (edge_com a b (fz_acc a Za) (fz_acc b Zb) (fz_fnode a Za) Cb). }
  induction m as [|x m IH]; intros a b H; simpl in H.
  - destruct H as [H _]. constructor. apply E1. exact H.
  - destruct H as [H1 H2]. apply t_trans with (T x); [constructor; apply E1; exact H1|]. apply IH. exact H2.
Qed.

Lemma key_time : forall m a b, chain node comF (a :: m ++ [b]) -> closed b -> pt a < qt b.
Proof.
  intros m a b H Clb. destruct (comF_ends m a b H) as [Za Zb].
  destruct (Nat.lt_ge_cases (pt a) (qt b)) as [Lt|Le]; auto. exfalso.
  pose proof (comF_path m a b H) as P.
  pose proof (fz_acc a Za) as A. pose proof (fz_acc b Zb) as B.
  destruct (node_E a A) as (Ea & _ & _ & REa & Eia & Eoa).
  destruct (node_E b B) as (Eb & _ & _ & REb & Eib & Eob).
  pose proof (back_z a b Ea Eb A B (fz_fnode a Za) (fz_fnode b Zb) Clb Eoa Eob Le) as BK.
  assert (KE : forall t0, eQ Ea t0 -> t0 < T a -> gedge s t0 (T a)).
  { intros t0 Q L0. right; right. exists Ea. split; [exact Eoa|]. split; [exact Q|lia]. }
  destruct (wr b) eqn:Wb.
  - assert (Y : vor (vor (eP Eb) (esrc Eb)) (gk p s (T b)) (T b)).
    { left. right. unfold esrc, srcv. unfold MIPFSC.wr in Wb. rewrite Eob in Wb. rewrite Wb. right.
      unfold vone. symmetry. rewrite (n_et p s R W _ _ Eb REb). reflexivity. }
    destruct (BK _ Y) as [Q L0].
    apply (proj1 EV (T a)). apply t_trans with (T b); [exact P|]. constructor. apply KE; auto.
  - apply clos_trans_tn1 in P. remember (T b) as tb eqn:Etb.
    destruct P as [tb' G|t0 tb' G P0]; subst tb'.
    + destruct (into_read (T a) b B Wb G) as (Eb' & Eo' & Q & N). rewrite Eob in Eo'. injection Eo' as <-.
      destruct (BK _ (o_QP_G p s IO _ Eb Eob (T a) Q)) as [_ L0]. lia.
    + destruct (into_read t0 b B Wb G) as (Eb' & Eo' & Q & N). rewrite Eob in Eo'. injection Eo' as <-.
      destruct (BK _ (o_QP_G p s IO _ Eb Eob t0 Q)) as [Qa L0].
      apply (proj1 EV (T a)). apply t_trans with t0; [apply clos_tn1_trans; exact P0|]. constructor. apply KE; auto.
Qed.

Lemma key_comF : forall m a b, chain node comF (a :: m ++ [b]) -> closed b -> key_in a < key_out b.
Proof.
  intros m a b H Clb. destruct (comF_ends m a b H) as [Za Zb].
  pose proof (key_time m a b H Clb) as Tm.
  destruct (fence_pre a Za) as (Ia & Ha). destruct (fence_post b Zb Clb) as (Ib & Hb).
  pose proof (cmi_ff (fpre a) (fpost b) Ia Ib Ha Hb Tm) as C.
  unfold key_in, key_out. rewrite Za, Zb, (proj2 (closedb_iff b) Clb). lia.
Qed.

Definition INV (a b : node) : Prop :=
  exists a', key_in a <= key_in a' /\ In a' L /\ (a' = b \/ exists m, chain node comF (a' :: m ++ [b])).

Lemma INV_key : forall a b, In b L -> (fz b = true -> closed b) -> INV a b -> key_in a <= key_out b.
Proof.
  intros a b B Cb (a' & Le & I & [->|(m & C)]).
  - pose proof (key_node b B). lia.
  - destruct (comF_ends m a' b C) as [_ Zb]. pose proof (key_comF m a' b C (Cb Zb)). lia.
Qed.

(* an edge of programme or settle order leaves a node that is closed if fenced *)
Lemma pc_closed : forall a b, In b L -> (MIPFSC.pob a b || cmNb a b) = true -> fz a = true -> closed a.
Proof.
  intros a b B P Z. apply orb_prop in P. destruct P as [P|P]; [apply (pob_closed a b B P Z)|].
  unfold cmNb in P. rewrite Z in P. discriminate.
Qed.

Lemma path_INV : forall l a b, (forall n, In n (a :: l ++ [b]) -> In n L) -> chain node Rs (a :: l ++ [b]) -> INV a b.
Proof.
  intros l. induction l as [|m l IH] using rev_ind; intros a b InL H.
  - simpl in H. destruct H as [H _].
    assert (Ia : In a L) by (apply InL; simpl; auto). assert (Ib : In b L) by (apply InL; simpl; auto).
    unfold Rs in H. apply orb_prop in H. destruct H as [H|H]; [apply orb_prop in H; destruct H as [H|H]|].
    + exists b. split; [|split; auto]. pose proof (key_node a Ia). pose proof (key_po a b Ia Ib H). lia.
    + exists b. split; [|split; auto]. pose proof (key_node a Ia). pose proof (key_cmN a b H). lia.
    + exists a. split; [lia|]. split; auto. right. exists []. simpl. auto.
  - assert (H' : chain node Rs ((a :: l) ++ m :: [b])) by (rewrite <- app_assoc in H; exact H).
    destruct (chain_last_split Rs (a :: l) m [b] H') as [H1 H2]. simpl in H2. destruct H2 as [E _].
    assert (Im : In m L) by (apply InL; simpl; right; apply in_app_iff; left; apply in_app_iff; right; left; auto).
    assert (Ib : In b L) by (apply InL; simpl; right; apply in_app_iff; right; left; auto).
    destruct (IH a m ltac:(intros n I; apply InL; simpl in I |- *; destruct I as [I|I]; [left; auto|right];
                            rewrite <- app_assoc; apply in_app_iff in I; destruct I as [I|[I|[]]];
                            apply in_app_iff; [left; auto|right; left; auto]) H1) as (a' & Le & Ia' & Hm).
    unfold Rs in E. apply orb_prop in E. destruct E as [E|E]; [apply orb_prop in E; destruct E as [E|E]|].
    + pose proof (INV_key a m Im (fun Z => pc_closed m b Ib ltac:(rewrite E; reflexivity) Z) (ex_intro _ a' (conj Le (conj Ia' Hm)))) as Km.
      exists b. split; [|split; auto]. pose proof (key_po m b Im Ib E). lia.
    + pose proof (INV_key a m Im (fun Z => pc_closed m b Ib ltac:(rewrite E, orb_true_r; reflexivity) Z) (ex_intro _ a' (conj Le (conj Ia' Hm)))) as Km.
      exists b. split; [|split; auto]. pose proof (key_cmN m b E). lia.
    + exists a'. split; auto. split; auto. right. destruct Hm as [->|(q & Q)].
      * exists []. simpl. auto.
      * exists (q ++ [m]). rewrite <- app_assoc. change (chain node comF ((a' :: q) ++ m :: [b])).
        apply (chain_join); [exact Q|]. simpl. auto.
Qed.

Fixpoint has_pc (l : list node) : bool :=
  match l with a :: ((b :: _) as t) => (MIPFSC.pob a b || cmNb a b) || has_pc t | _ => false end.

Lemma has_pc_split : forall l, has_pc l = true -> exists u x y v, l = u ++ x :: y :: v /\ (MIPFSC.pob x y || cmNb x y) = true.
Proof.
  induction l as [|a l IH]; intros H; [discriminate|]. destruct l as [|b l']; [discriminate|].
  simpl in H. destruct (MIPFSC.pob a b || cmNb a b) eqn:P.
  - exists [], a, b, l'. auto.
  - destruct (IH H) as (u & x & y & v & E & Q). exists (a :: u), x, y, v. rewrite E. auto.
Qed.

Lemma no_pc_comF : forall l, has_pc l = false -> chain node Rs l -> chain node comF l.
Proof.
  induction l as [|a l IH]; intros H C; simpl; auto. destruct l as [|b l']; auto.
  simpl in H, C. apply orb_false_elim in H. destruct H as [H1 H2]. destruct C as [C1 C2].
  split; [unfold Rs in C1; rewrite H1 in C1; exact C1|apply IH; auto].
Qed.

Theorem acyc_s : acyclic node Rs L.
Proof.
  intros a l Ia Il C.
  assert (All : forall n, In n (a :: l ++ [a]) -> In n L).
  { intros n I. simpl in I. destruct I as [<-|I]; auto. apply in_app_iff in I. destruct I as [I|[<-|[]]]; auto. }
  destruct (has_pc (a :: l ++ [a])) eqn:Hp.
  - destruct (has_pc_split _ Hp) as (u & x & y & v & E & P).
    assert (Ix : In x L) by (apply All; rewrite E; apply in_app_iff; right; left; auto).
    assert (Iy : In y L) by (apply All; rewrite E; apply in_app_iff; right; right; left; auto).
    assert (Kxy : key_out x < key_in y).
    { apply orb_prop in P. destruct P as [P|P]; [apply (key_po x y Ix Iy P)|apply (key_cmN x y P)]. }
    destruct (cyc_path Rs a l C u x y v E) as [Exy|(q & Q & Iq)].
    + subst. pose proof (key_node x Ix). lia.
    + assert (Aq : forall n, In n (y :: q ++ [x]) -> In n L).
      { intros n I. destruct I as [<-|I]; [auto|]. apply in_app_iff in I. destruct I as [I|[<-|[]]]; auto. }
      pose proof (INV_key y x Ix (fun Z => pc_closed x y Iy P Z) (path_INV q y x Aq Q)). lia.
  - pose proof (no_pc_comF _ Hp C) as Cc.
    exact (proj1 EV (T a) (comF_path l a a Cc)).
Qed.

End MXO.

End Iface.
