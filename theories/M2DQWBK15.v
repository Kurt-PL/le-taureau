(* Part 15: fenced code over the write-back model (G1).
   KT: an edge of the A image's event graph between the times of two accesses is a path of the
   state's event graph (the image is the one of runWBK with Fk := True and Good := "LFB at t").
   fenced_sc_WB: every finished runWB of a fenced programme whose event graph has no cycle (evok)
   has an interleaving with the same passed slots, registers and final storage. *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2InvO M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB.
Require Import M2DQWBK1 M2DQWBK3 M2DQWBK9 M2DQWBK13 M2DQWBK14.
Require Import M2Iface M2IfaceInst M2DQIfaceInst MIComp MINeg MIFSC Topo M2DQWBFsc.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

(* ---------- histories ---------- *)
Lemma older_cons_inv : forall (y : nat * bool) h a b, older (y :: h) a b -> (fst y = a /\ In b (ids h)) \/ older h a b.
Proof.
  intros y h a b (h1 & h2 & E & A & B). destruct h1 as [|y' h1]; [destruct A|].
  cbn in E. injection E as <- E. subst h. destruct A as [A|A].
  - left. split; [exact A|]. rewrite ids_app. apply in_app_iff. right. exact B.
  - right. exists h1, h2. auto.
Qed.
Lemma older_cons : forall (y : nat * bool) h a b, older h a b -> older (y :: h) a b.
Proof. intros y h a b (h1 & h2 & E & A & B). exists (y :: h1), h2. subst h. split; [reflexivity|]. split; [right; exact A|exact B]. Qed.

Lemma older_hers : forall h a b, older (hers h) a b -> older h a b.
Proof.
  induction h as [|[w f] h IH]; intros a b O.
  - destruct O as (h1 & h2 & E & A & B). destruct h1; [destruct A|discriminate].
  - destruct f; cbn in O; [apply older_cons; exact (IH a b O)|].
    destruct (older_cons_inv _ _ _ _ O) as [(Ea & Ib)|O'].
    + cbn in Ea. subst a. exists [(w, false)], h. split; [reflexivity|]. split; [left; reflexivity|exact (in_ids_hers h b Ib)].
    + apply older_cons. exact (IH a b O').
Qed.

Lemma nodup_hers : forall h, NoDup (ids h) -> NoDup (ids (hers h)).
Proof.
  induction h as [|[w f] h IH]; intros N; [constructor|]. inversion N as [|? ? Nw N']; subst.
  destruct f; cbn; [exact (IH N')|]. constructor; [|exact (IH N')]. intros I. apply Nw. exact (in_ids_hers h w I).
Qed.

Lemma in_ids_of : forall (h : hist) w f, In (w, f) h -> In w (ids h).
Proof. intros h w f I. unfold ids. apply in_map_iff. exists (w, f). auto. Qed.

Lemma in_ids_fl : forall h w, In w (ids h) -> exists b, In (w, b) h.
Proof.
  intros h w I. unfold ids in I. apply in_map_iff in I. destruct I as ([w' b] & E & I). simpl in E. subst. eauto.
Qed.

(* a read of the image that took u (what the written-back store w0 stands for) reads before b,
   so the state's read of w0 reads before b *)
Lemma fr_seg : forall h w0 o b, NoDup (ids h) -> seg h w0 o -> In (b, false) h ->
  match o with Some u => older (hers h) u b | None => True end -> older h w0 b.
Proof.
  intros h w0 [u|] b N S Ib O.
  - destruct S as (h0 & h1 & h2 & E & Al). subst h.
    assert (Ib2 : In (b, false) h2).
    { apply in_app_iff in Ib. destruct Ib as [Ib|[Ib|Ib]].
      - exfalso. assert (Ob : older (hers (h0 ++ (u, false) :: h1 ++ (w0, true) :: h2)) b u).
        { rewrite hers_ins_f. exists (hers h0), ((u, false) :: hers (h1 ++ (w0, true) :: h2)). split; [reflexivity|].
          split; [apply (in_ids_of _ _ false); apply in_hers; auto|left; reflexivity]. }
        exact (older_asym _ _ _ (nodup_hers _ N) O Ob).
      - injection Ib as ->. exfalso. exact (older_irrefl _ _ (nodup_hers _ N) O).
      - apply in_app_iff in Ib. destruct Ib as [Ib|[Ib|Ib]]; [|discriminate|exact Ib].
        exfalso. unfold allt in Al. rewrite Forall_forall in Al. pose proof (Al _ Ib). discriminate. }
    exists (h0 ++ (u, false) :: h1 ++ [(w0, true)]), h2. split; [repeat (rewrite <- app_assoc; cbn); reflexivity|].
    split; [rewrite !ids_app; cbn; rewrite ids_app; cbn; apply in_app_iff; right; right; apply in_app_iff; right; left; reflexivity|].
    exact (in_ids_of _ _ _ Ib2).
  - destruct S as (h1 & h2 & E & Al). subst h.
    assert (Ib2 : In (b, false) h2).
    { apply in_app_iff in Ib. destruct Ib as [Ib|[Ib|Ib]]; [|discriminate|exact Ib].
      exfalso. unfold allt in Al. rewrite Forall_forall in Al. pose proof (Al _ Ib). discriminate. }
    exists (h1 ++ [(w0, true)]), h2. split; [rewrite <- app_assoc; reflexivity|].
    split; [rewrite ids_app; apply in_app_iff; right; left; reflexivity|exact (in_ids_of _ _ _ Ib2)].
Qed.

(* ---------- KT ---------- *)
Definition GoodL (s : st) (t : nat) : Prop := forall e, ent s t = Some e -> LFB s (ec e) t.

Section KT.
Set Default Proof Using "All".
Variables (p : prog) (W : wf p) (FN : fenced p) (sw : nat -> option (cell -> option nat)) (s sA : st).
Hypothesis RA : run p sA.
Hypothesis Rl : rel sw s sA.
Hypothesis K : KR True (GoodL s) sw s sA.
Hypothesis D : done p s.

Lemma KT_fr : forall e x a b, nth_error (lg sA) a = Some e -> In x (eR e) -> In b (ids (hs sA x)) -> b <> a ->
  match erf e x with None => True | Some u => older (hs sA x) u b end -> gedge s a b.
Proof.
  intros e x a b Ea Ix Ib Nb M. destruct (k_ent True (GoodL s) sw s sA K a e Ea) as (eW & EW & Se).
  pose proof Se as (_ & _ & _ & _ & S5 & _ & S7 & S8 & _).
  rewrite (r_hs sw s sA Rl x) in Ib, M.
  assert (Ibf : In (b, false) (hs s x)).
  { unfold ids in Ib. apply in_map_iff in Ib. destruct Ib as ([b' f] & Eb & Ib). cbn in Eb. subst b'.
    apply in_hers in Ib. destruct Ib as [Ib Ef]. cbn in Ef. subst f. exact Ib. }
  right; left. exists eW, x. split; [exact EW|]. split; [rewrite <- S5; exact Ix|].
  split; [exact (in_ids_of _ _ _ Ibf)|]. split; [exact Nb|].
  destruct (erf eW x) as [w0|] eqn:Ew; [|exact Logic.I].
  pose proof (S8 x w0 Ew) as Iw. rewrite S7, Ew in M. cbn [pi] in M.
  pose proof (w_nodup True (GoodL s) sw s sA K x) as N.
  destruct (in_ids_fl _ _ Iw) as [[|] Iwf].
  - destruct (w_bet True (GoodL s) sw s sA K x w0 Iwf) as (f & Sf & Sg). rewrite Sf in M.
    exact (fr_seg (hs s x) w0 (f x) b N Sg Ibf M).
  - destruct (r_kept sw s sA Rl x w0 Iwf) as [Sn _]. rewrite Sn in M. exact (older_hers _ _ _ M).
Qed.

Lemma Good_acc : forall n, acc p sA n = true -> GoodL s (T sA n).
Proof.
  intros n A e E. pose proof (FC p W FN True (GoodL s) sw s sA RA Rl K D n A) as F.
  assert (RAr : reach (STEP (Model := dqmodel) p) sA) by exact (proj2 (reach_runQ p sA) RA).
  destruct (node_E (IFM := dqmodel) p sA RAr (rel_done p sw s sA Rl D) W n A) as (E0 & _ & _ & (A1 & B1 & _) & _ & _).
  destruct (k_ent True (GoodL s) sw s sA K _ E0 A1) as (eW & EW & (_ & S2 & _)).
  unfold T in E. rewrite E in EW. injection EW as <-. rewrite <- S2, B1. exact F.
Qed.

Theorem KT : forall a b, gedge sA a b -> AT p sA b -> Pth s a b.
Proof.
  intros a b G (nb & Ab & <-). destruct G as [(x & O)|[(e & x & Ea & Ix & Ib & Nb & M)|(e & Eb & Q & Nab)]].
  - constructor. left. exists x. rewrite (r_hs sw s sA Rl x) in O. exact (older_hers _ _ _ O).
  - constructor. exact (KT_fr e x a (T sA nb) Ea Ix Ib Nb M).
  - destruct (k_ent True (GoodL s) sw s sA K _ e Eb) as (eW & EW & _).
    pose proof (k_eQ True (GoodL s) sw s sA K Logic.I (T sA nb) e eW Eb EW (Good_acc nb Ab) a Q) as [Q'|(y & Q' & P)].
    + constructor. right; right. exists eW. auto.
    + destruct (Nat.eq_dec y (T sA nb)) as [->|Ny]; [exact P|].
      apply (t_trans _ _ _ y _ P). constructor. right; right. exists eW. auto.
Qed.

Lemma NGA_of : evok s -> forall t, ~ clos_trans nat (GA p sA) t t.
Proof.
  intros EV t C. apply (proj1 EV t).
  assert (G : forall a b, clos_trans nat (GA p sA) a b -> clos_trans nat (gedge s) a b).
  { intros a b H. induction H as [a b (G & _ & Bt)|a b c' _ IH1 _ IH2]; [exact (KT a b G Bt)|exact (t_trans _ _ a b c' IH1 IH2)]. }
  exact (G t t C).
Qed.
End KT.

(* ---------- the conclusion through one image ---------- *)
Theorem WB_sc_of_image1 : forall p s sw sA, wf p -> done p s -> run p sA -> rel sw s sA ->
  acyclic node (Rb p sA) (L sA) ->
  exists l g, srun p l g /\ (forall c, sp g c = pcs s c) /\
    (forall c j, j < pcs s c -> sr g c j = rg (cs s c) j) /\ (forall x, sm g x = final s x).
Proof.
  intros p s sw sA W D RA Rl AC.
  assert (R : reach (STEP (Model := dqmodel) p) sA) by (apply (proj2 (reach_runQ p sA)); exact RA).
  assert (DA : done p sA) by exact (rel_done p sw s sA Rl D).
  destruct (topo node (node_eq_dec (IFM := dqmodel) p sA R DA W) (Rb p sA) (L sA) (L_nodup (IFM := dqmodel) p sA R DA W) AC) as (ord & P & O).
  set (CP0 := fun _ : cell => true).
  assert (OP : forall i j a b, nth_error ord i = Some a -> nth_error ord j = Some b -> pob a b = true -> i < j).
  { intros i j a b Qa Qb H. apply (O i j a b Qa Qb). unfold Rb. rewrite H. reflexivity. }
  assert (OC : forall i j a b x, nth_error ord i = Some a -> nth_error ord j = Some b -> combx p sA x a b = true ->
            CP0 x = true -> i < j).
  { intros i j a b x Qa Qb H _. apply (O i j a b Qa Qb). unfold Rb.
    assert (comb p sA a b = true) by (apply comb_x; eauto). rewrite H0, orb_true_r. reflexivity. }
  destruct (full' (IFM := dqmodel) p sA R DA W ord P CP0 OP OC (fun _ => eq_refl)) as (l & g & Co).
  exists l, g. split; [apply Co|].
  pose proof (sp_full' (IFM := dqmodel) p sA R DA W ord P CP0 OP OC l g Co) as Sp.
  split; [intros c; rewrite Sp; exact (f_equal (fun f => f c) (r_pcs sw s sA Rl))|].
  split.
  - intros c j Lj. rewrite <- (rel_rg sw s sA Rl).
    assert (Lj' : j < sp g c) by (rewrite Sp, (r_pcs sw s sA Rl); exact Lj).
    destruct Co as (_ & _ & _ & Dd). apply Dd. auto.
  - intros x. rewrite (mem_full' (IFM := dqmodel) p sA R DA W ord P CP0 OP OC l g Co x eq_refl).
    exact (final_rel sw s sA Rl x).
Qed.

(* G1: every access between guard() fences, over the write-back model *)
Theorem fenced_sc_WB : forall p s, wf p -> fenced p -> runWB p s -> done p s -> evok s ->
  exists l g, srun p l g /\ (forall c, sp g c = pcs s c) /\
    (forall c j, j < pcs s c -> sr g c j = rg (cs s c) j) /\ (forall x, sm g x = final s x).
Proof.
  intros p s W FN RW D EV.
  (* pass 1: the structural part of KR *)
  destruct (runWBK p W False (fun _ => False) s RW (fun F => match F with end) (fun F => match F with end))
    as (sw1 & sA1 & RA1 & Rl1 & K1).
  assert (H2 : HB2 (GoodL s) s).
  { intros t e E Ew Cn e' E'. rewrite E in E'. injection E' as <-.
    exact (FC_store p W FN False (fun _ => False) sw1 s sA1 RA1 Rl1 K1 D t e E Ew Cn). }
  (* pass 2: the knowledge part, for the times that have LFB *)
  destruct (runWBK p W True (GoodL s) s RW (fun _ t e E G => G e E) (fun _ => H2)) as (sw & sA & RA & Rl & K).
  assert (RAr : reach (STEP (Model := dqmodel) p) sA) by exact (proj2 (reach_runQ p sA) RA).
  apply (WB_sc_of_image1 p s sw sA W D RA Rl).
  exact (acycG (IFM := dqmodel) p sA RAr (rel_done p sw s sA Rl D) W FN (NGA_of p W FN sw s sA RA Rl K D EV)).
Qed.

Print Assumptions fenced_sc_WB.
