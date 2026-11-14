(* Model2: what R1 was checked against at each early access, kept for
   proofs. An access that happened before an earlier instruction of its
   context happened early, and R1 held for it against a snapshot whose past
   is the run's past before it. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3.

Lemma dof_ieval : forall i r r', ieval i r = ieval i r' -> dof i r = dof i r'.
Proof.
  intros [m x c|m x c v|m x c e n| |] r r' H; simpl in *; auto; injection H; intros;
  repeat match goal with Hx : _ = _ |- _ => rewrite Hx end; reflexivity.
Qed.

(* R1 held for an early access, or for the early write of a CAS whose read
   happened alone *)
Definition eokx (p : prog) (c : nat) (cc : cst) (pc N T : nat) (d : desc) (u : cell -> option nat) (B : nat -> bool) : Prop :=
  early_ok p c cc pc N T d u B \/ exists T1 m xs, early_okW p c cc pc N T T1 m xs d B.

Definition SI (p : prog) (s : st) : Prop :=
  (forall t, tm s <= t -> es s t = None) /\
  (forall t e, ent s t = Some e -> es s t = None ->
     ek e < pcs s (ec e) /\ forall j t', j < ek e -> oc (cs s (ec e)) j = Some t' -> t' < t) /\
  (forall t cc0 pc0 N0 B0, es s t = Some (cc0, pc0, N0, B0) -> (forall e, ent s t = Some e -> eh e = false) ->
     exists e d, ent s t = Some e /\
     eokx p (ec e) cc0 pc0 N0 t d (erf e) B0 /\ pc0 < ek e /\
     eof (ai (cs s (ec e)) (ek e)) (rg (cs s (ec e))) = Some d /\
     (forall j t', oc cc0 j = Some t' -> oc (cs s (ec e)) j = Some t' /\ rg cc0 j = rg (cs s (ec e)) j /\ t' < t) /\
     (forall j t', oc (cs s (ec e)) j = Some t' -> t' < t -> oc cc0 j = Some t') /\
     (forall j d', oc cc0 j <> None -> pc0 <= j -> ai cc0 j = inst_of d' ->
        eof (ai (cs s (ec e)) j) (rg (cs s (ec e))) = Some d') /\
     (pc0 <= pcs s (ec e) /\ forall j, j < pc0 -> oc cc0 j = None -> oc (cs s (ec e)) j = None) /\
     (forall j, oc cc0 j <> None -> pc0 <= j -> exists d', ai cc0 j = inst_of d' /\ d' <> DFn FFull) /\
     (forall j t', oh cc0 j = Some t' -> oh (cs s (ec e)) j = Some t' /\ t' < t)).

Lemma SI_init : forall p, SI p sinit.
Proof.
  intros p. split; [|split]; simpl; auto; [intros t e H; unfold ent in H; destruct t; discriminate|discriminate].
Qed.

(* what an access at a recorded slot does is fixed by what has happened *)
Lemma eof_ieval : forall i r r', ieval i r = ieval i r' -> eof i r = eof i r'.
Proof.
  intros i r r' H. destruct i as [m x c0|m x c0 v|m x c0 e n|[]|]; try reflexivity;
  apply (dof_ieval _ _ _ H).
Qed.

Lemma dof_rec : forall p s c j, Inv1 p s -> oc (cs s c) j <> None ->
  forall r, settled (cs s c) (pcs s c) r -> eof (ai (cs s c) j) r = eof (ai (cs s c) j) (rg (cs s c)).
Proof.
  intros p s c j I O r Sr. destruct (oc (cs s c) j) as [t|] eqn:E; [|congruence].
  destruct (i_oc p s I c j t E) as (e & A & B & C). apply eof_ieval.
  pose proof (i_det p s I t e A r) as Q. rewrite B, C in Q. apply Q. exact Sr.
Qed.

Section Ev.
Variables (p : prog) (s : st) (c k : nat) (i : instr) (m' : mst) (a : val) (K : view)
          (u : cell -> option nat) (w : bool) (Bd : nat -> bool) (pc' tp' : nat -> nat)
          (cm' : list (nat * nat * nat)).
Hypothesis I : Inv1 p s.
Hypothesis Sv : SI p s.
Hypothesis Ho : oc (cs s c) k = None.
Hypothesis Hk : pcs s c <= k.
Hypothesis Hpc : forall c', pcs s c' <= pc' c'.
Local Abbreviation t' := (evs s c k i m' a K u w Bd pc' tp' cm').

(* an old snapshot stays valid after an event step *)
Lemma snap_old : forall t cc0 pc0 N0 B0, es s t = Some (cc0, pc0, N0, B0) ->
     (forall e, ent t' t = Some e -> eh e = false) -> exists e d, ent t' t = Some e /\
     eokx p (ec e) cc0 pc0 N0 t d (erf e) B0 /\ pc0 < ek e /\
     eof (ai (cs t' (ec e)) (ek e)) (rg (cs t' (ec e))) = Some d /\
     (forall j t0, oc cc0 j = Some t0 -> oc (cs t' (ec e)) j = Some t0 /\ rg cc0 j = rg (cs t' (ec e)) j /\ t0 < t) /\
     (forall j t0, oc (cs t' (ec e)) j = Some t0 -> t0 < t -> oc cc0 j = Some t0) /\
     (forall j d', oc cc0 j <> None -> pc0 <= j -> ai cc0 j = inst_of d' ->
        eof (ai (cs t' (ec e)) j) (rg (cs t' (ec e))) = Some d') /\
     (pc0 <= pc' (ec e) /\ forall j, j < pc0 -> oc cc0 j = None -> oc (cs t' (ec e)) j = None) /\
     (forall j, oc cc0 j <> None -> pc0 <= j -> exists d', ai cc0 j = inst_of d' /\ d' <> DFn FFull) /\
     (forall j t0, oh cc0 j = Some t0 -> oh (cs t' (ec e)) j = Some t0 /\ t0 < t).
Proof.
  intros t cc0 pc0 N0 B0 H Hn. destruct Sv as (S1 & S2 & S3).
  assert (Lt : t < tm s) by (destruct (Nat.lt_ge_cases t (tm s)); auto; rewrite S1 in H by auto; discriminate).
  assert (Hn' : forall e, ent s t = Some e -> eh e = false).
  { intros e0 E0. apply Hn. rewrite (ent_s' p s c k i m' a K u w Bd pc' tp' cm' I), (proj2 (Nat.ltb_lt _ _) Lt). exact E0. }
  destruct (S3 t cc0 pc0 N0 B0 H Hn') as (e & d & A & B & C & D & E & F & G & L & Pn & Ph).
  set (ce := ec e).
  assert (SET : settled (cs s ce) (pcs s ce) (rg (cs t' ce))) by (eapply settled_s'; eauto).
  assert (NEW : forall j t0, oc (cs t' ce) j = Some t0 -> t0 < tm s -> oc (cs s ce) j = Some t0).
  { intros j t0 X Y. rewrite oc_s' in X. revert X.
    destruct (Nat.eqb_spec ce c); [destruct (Nat.eqb_spec j k)|]; intros X; [injection X; lia|congruence|exact X]. }
  exists e, d. split; [rewrite (ent_s' p s c k i m' a K u w Bd pc' tp' cm' I), (proj2 (Nat.ltb_lt _ _) Lt); auto|].
  split; auto. split; auto. fold ce in D, E, F, G |- *.
  assert (OK : oc (cs s ce) (ek e) <> None)
    by (destruct (i_et p s I t e A) as (_ & O); rewrite (Hn' e A) in O; fold ce in O; congruence).
  split.
  - rewrite (ai_old_s' s c k i m' a K u w Bd pc' tp' cm' Ho _ _ OK).
    rewrite (dof_rec p s ce (ek e) I OK _ SET). exact D.
  - split; [|split; [|split]].
    + intros j t0 X. destruct (E j t0 X) as (X1 & X2 & X3). split; [apply oc_old_s'; auto|]. split; auto.
      rewrite X2. symmetry. apply rg_old_s'; auto. congruence.
    + intros j t0 X Y. apply F; auto. apply NEW; auto. lia.
    + intros j d' X Y Z. destruct (oc cc0 j) as [tj|] eqn:Oj; [|congruence].
      destruct (E j tj Oj) as (X1 & _ & _). assert (O' : oc (cs s ce) j <> None) by congruence.
      rewrite (ai_old_s' s c k i m' a K u w Bd pc' tp' cm' Ho _ _ O').
      rewrite (dof_rec p s ce j I O' _ SET). apply G; auto. congruence.
    + split; [|split; [exact Pn|]].
      * destruct L as (L1 & L2). split; [pose proof (Hpc ce); unfold ce in *; lia|].
        intros j Lj Oj. rewrite oc_s'. destruct (Nat.eqb_spec ce c); [destruct (Nat.eqb_spec j k)|]; [|subst ce; rewrite <- e0; apply L2; auto|apply L2; auto].
        exfalso. unfold ce in *. rewrite e0 in L1. lia.
      * intros j t0 X. rewrite (oh_s' s c k i m' a K u w Bd pc' tp' cm'). apply Ph. exact X.
Qed.

End Ev.

Section Rd.
Variables (p : prog) (s : st) (c k : nat) (xs : list cell) (B : nat -> bool) (m' : mst) (a : val) (K : view)
          (u : cell -> option nat) (w : bool) (bv : bool).
Hypothesis I : Inv1 p s.
Hypothesis Sv : SI p s.
Hypothesis Ho : oc (cs s c) k = None.
Hypothesis Hk : pcs s c <= k.
Hypothesis Hoh : oh (cs s c) k = None.
Local Abbreviation t' := (sread s c k Plain xs B m' a K u w bv).

Lemma rd_oh_old : forall c' j t0, oh (cs s c') j = Some t0 -> oh (cs t' c') j = Some t0.
Proof.
  intros c' j t0 X. unfold sread; simpl. unfold upd. destruct (Nat.eqb_spec c' c); [subst; simpl|exact X].
  destruct (Nat.eqb_spec j k); [subst; congruence|exact X].
Qed.

Lemma rd_oc : forall c' j, oc (cs t' c') j = oc (cs s c') j.
Proof. intros c' j. unfold sread; simpl. unfold upd. destruct (Nat.eqb c' c) eqn:E; [apply Nat.eqb_eq in E; subst|]; reflexivity. Qed.

Lemma rd_rg_old : forall c' j, oc (cs s c') j <> None -> rg (cs t' c') j = rg (cs s c') j.
Proof.
  intros c' j X. unfold sread; simpl. unfold upd. destruct (Nat.eqb_spec c' c); [subst; simpl|reflexivity].
  destruct (Nat.eqb_spec j k); [subst; congruence|reflexivity].
Qed.

Lemma rd_ai_old : forall c' j, oc (cs s c') j <> None -> ai (cs t' c') j = ai (cs s c') j.
Proof.
  intros c' j X. unfold sread; simpl. unfold upd. destruct (Nat.eqb_spec c' c); [subst; simpl|reflexivity].
  destruct (Nat.eqb_spec j k); [subst; congruence|reflexivity].
Qed.

Lemma rd_settled : forall c', settled (cs s c') (pcs s c') (rg (cs t' c')).
Proof.
  intros c' j [L|X]; [|apply rd_rg_old; exact X].
  unfold sread; simpl. unfold upd. destruct (Nat.eqb_spec c' c); [subst; simpl|reflexivity].
  destruct (Nat.eqb_spec j k); [lia|reflexivity].
Qed.

Lemma rd_ent_old : forall t, t < tm s -> ent t' t = ent s t.
Proof. intros t L. unfold ent, sread; simpl. apply nth_error_app1. rewrite <- (i_tm p s I). exact L. Qed.

Lemma snap_old_rd : forall t cc0 pc0 N0 B0, es s t = Some (cc0, pc0, N0, B0) ->
     (forall e, ent t' t = Some e -> eh e = false) -> exists e d, ent t' t = Some e /\
     eokx p (ec e) cc0 pc0 N0 t d (erf e) B0 /\ pc0 < ek e /\
     eof (ai (cs t' (ec e)) (ek e)) (rg (cs t' (ec e))) = Some d /\
     (forall j t0, oc cc0 j = Some t0 -> oc (cs t' (ec e)) j = Some t0 /\ rg cc0 j = rg (cs t' (ec e)) j /\ t0 < t) /\
     (forall j t0, oc (cs t' (ec e)) j = Some t0 -> t0 < t -> oc cc0 j = Some t0) /\
     (forall j d', oc cc0 j <> None -> pc0 <= j -> ai cc0 j = inst_of d' ->
        eof (ai (cs t' (ec e)) j) (rg (cs t' (ec e))) = Some d') /\
     (pc0 <= pcs s (ec e) /\ forall j, j < pc0 -> oc cc0 j = None -> oc (cs t' (ec e)) j = None) /\
     (forall j, oc cc0 j <> None -> pc0 <= j -> exists d', ai cc0 j = inst_of d' /\ d' <> DFn FFull) /\
     (forall j t0, oh cc0 j = Some t0 -> oh (cs t' (ec e)) j = Some t0 /\ t0 < t).
Proof.
  intros t cc0 pc0 N0 B0 H Hn. destruct Sv as (S1 & S2 & S3).
  assert (Lt : t < tm s) by (destruct (Nat.lt_ge_cases t (tm s)); auto; rewrite S1 in H by auto; discriminate).
  assert (Hn' : forall e, ent s t = Some e -> eh e = false) by (intros e0 E0; apply Hn; rewrite rd_ent_old by exact Lt; exact E0).
  destruct (S3 t cc0 pc0 N0 B0 H Hn') as (e & d & A & Bk & C & D & E & F & G & L & Pn & Ph).
  set (ce := ec e).
  assert (SET : settled (cs s ce) (pcs s ce) (rg (cs t' ce))) by (apply rd_settled).
  exists e, d. split; [rewrite rd_ent_old by exact Lt; exact A|].
  split; auto. split; auto. fold ce in D, E, F, G |- *.
  assert (OK : oc (cs s ce) (ek e) <> None)
    by (destruct (i_et p s I t e A) as (_ & O); rewrite (Hn' e A) in O; fold ce in O; congruence).
  split.
  - rewrite (rd_ai_old _ _ OK). rewrite (dof_rec p s ce (ek e) I OK _ SET). exact D.
  - split; [|split; [|split]].
    + intros j t0 X. destruct (E j t0 X) as (X1 & X2 & X3). rewrite rd_oc. split; [exact X1|]. split; auto.
      rewrite X2. symmetry. apply rd_rg_old. congruence.
    + intros j t0 X Y. rewrite rd_oc in X. apply F; auto.
    + intros j d' X Y Z. destruct (oc cc0 j) as [tj|] eqn:Oj; [|congruence].
      destruct (E j tj Oj) as (X1 & _ & _). assert (O' : oc (cs s ce) j <> None) by congruence.
      rewrite (rd_ai_old _ _ O'). rewrite (dof_rec p s ce j I O' _ SET). apply G; auto. congruence.
    + split; [|split; [exact Pn|]].
      * destruct L as (L1 & L2). split; [exact L1|]. intros j Lj Oj. rewrite rd_oc. apply L2; auto.
      * intros j t0 X. destruct (Ph j t0 X) as (X1 & X2). split; [apply rd_oh_old; exact X1|exact X2].
Qed.

End Rd.

Lemma SI_es_none : forall p s t e, SI p s -> es s t = None -> ent s t = Some e ->
  forall j t', j < ek e -> oc (cs s (ec e)) j = Some t' -> t' < t.
Proof. intros p s t e (_ & S2 & _) N H. apply (S2 t e H N). Qed.

Lemma SI_step : forall p s t, run p s -> step p s t -> SI p s -> SI p t.
Proof.
  intros p s t R H Sv. pose proof (Inv1_run p s R) as I. pose proof Sv as (S1 & S2 & S3).
  destruct (step_cases p s t H) as [(c & i & m' & a & K & u & w & H1 & H2 & H3 & H4 & Hbh & Hh & _ & _ & H6 & _ & ->)|[(c & k & d & B & m' & a & K & u & w & H1 & H2 & Hso & Hh & _ & _ & H5 & _ & ->)|[(c & d & H1 & H2 & H3 & H4 & H4m & Hfh & ->)|[(c & k & xs & B & m' & a & K & u & w & bv & H1 & H2 & Hh & Hso & H4 & H5 & _ & ->)|[(c & K1 & K2 & K3 & _ & K5 & K4 & _ & ->)|(cX & jX & bX & BX & oX & HjX & HfX & HcX & ->)]]]]].
  - (* in order *)
    unfold sord. set (k := pcs s c). split; [|split].
    + intros t0 L. unfold evs; simpl in *. apply S1. lia.
    + intros t0 e He N. unfold evs in N; simpl in N.
      rewrite (ent_s' p s c k i m' a K u w _ _ _ _ I) in He.
      destruct (Nat.ltb_spec t0 (tm s)).
      * destruct (S2 t0 e He N) as [Lk Q]. split.
        -- unfold evs; simpl. unfold upd. destruct (Nat.eqb_spec (ec e) c); [subst k; rewrite e0 in *|]; lia.
        -- intros j t1 Lj Oj. unfold evs in Oj; simpl in Oj. unfold upd in Oj.
           destruct (Nat.eqb_spec (ec e) c); [|exact (Q j t1 Lj Oj)]. simpl in Oj. rewrite <- e0 in Oj.
           destruct (Nat.eqb_spec j k); [subst k; rewrite e0 in Lk; lia|exact (Q j t1 Lj Oj)].
      * destruct (Nat.eqb_spec t0 (tm s)); [|discriminate]. injection He as <-. subst t0. cbn [ec ek] in *.
        split; [unfold evs; simpl; unfold upd; rewrite Nat.eqb_refl; lia|].
        intros j t1 Lj Oj. unfold evs in Oj; simpl in Oj. unfold upd in Oj. rewrite Nat.eqb_refl in Oj. simpl in Oj.
        destruct (Nat.eqb_spec j k); [lia|]. apply (oc_lt_tm p s c j t1 I Oj).
    + intros t0 cc0 pc0 N0 B0 He Hn. unfold evs in He; simpl in He.
      assert (HPC : forall c', pcs s c' <= upd (pcs s) c (S k) c') by (intros c'; unfold upd; destruct (Nat.eqb_spec c' c); [subst; unfold k; lia|lia]).
      apply (snap_old p s c k i m' a K u w _ _ _ _ I Sv H2 (le_n _) HPC t0 cc0 pc0 N0 B0 He Hn).
  - (* early *)
    unfold searly, set_es, searly0. split; [|split].
    + intros t0 L. simpl in *. unfold upd. destruct (Nat.eqb_spec t0 (tm s)); [lia|]. apply S1. lia.
    + intros t0 e He N. simpl in N. unfold upd in N. destruct (Nat.eqb_spec t0 (tm s)); [discriminate|].
      change (ent (evs s c k (inst_of d) m' a K u w (bor (bd (cs s c)) B) (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s)) t0 = Some e) in He.
      rewrite (ent_s' p s c k _ m' a K u w _ _ _ _ I) in He.
      destruct (Nat.ltb_spec t0 (tm s)); [|destruct (Nat.eqb_spec t0 (tm s)); [lia|discriminate]].
      destruct (S2 t0 e He N) as [Lk Q]. split; [exact Lk|].
      intros j t1 Lj Oj.
      change (oc (cs (evs s c k (inst_of d) m' a K u w (bor (bd (cs s c)) B) (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s)) (ec e)) j = Some t1) in Oj.
      rewrite oc_s' in Oj. destruct (Nat.eqb_spec (ec e) c); [destruct (Nat.eqb_spec j k)|]; [|apply (Q j t1 Lj); rewrite e0; exact Oj|exact (Q j t1 Lj Oj)].
      exfalso. rewrite e0 in Lk. lia.
    + intros t0 cc0 pc0 N0 B0 He Hn. simpl in He. unfold upd in He. destruct (Nat.eqb_spec t0 (tm s)).
      * subst t0. injection He as <- <- <- <-.
        set (t1 := evs s c k (inst_of d) m' a K u w (bor (bd (cs s c)) B) (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s)).
        exists (newev s c k (inst_of d) K u w), d. cbn [ec ek erf].
        change (ent t1 (tm s) = Some (newev s c k (inst_of d) K u w) /\ eokx p c (cs s c) (pcs s c) (tp s c) (tm s) d u B /\
          pcs s c < k /\ eof (ai (cs t1 c) k) (rg (cs t1 c)) = Some d /\
          (forall j t0, oc (cs s c) j = Some t0 -> oc (cs t1 c) j = Some t0 /\ rg (cs s c) j = rg (cs t1 c) j /\ t0 < tm s) /\
          (forall j t0, oc (cs t1 c) j = Some t0 -> t0 < tm s -> oc (cs s c) j = Some t0) /\
          (forall j d', oc (cs s c) j <> None -> pcs s c <= j -> ai (cs s c) j = inst_of d' ->
             eof (ai (cs t1 c) j) (rg (cs t1 c)) = Some d') /\
          (pcs s c <= pcs s c /\ forall j, j < pcs s c -> oc (cs s c) j = None -> oc (cs t1 c) j = None) /\
          (forall j, oc (cs s c) j <> None -> pcs s c <= j -> exists d', ai (cs s c) j = inst_of d' /\ d' <> DFn FFull) /\
          (forall j t0, oh (cs s c) j = Some t0 -> oh (cs t1 c) j = Some t0 /\ t0 < tm s)).
        split; [unfold t1; rewrite (ent_s' p s c k _ m' a K u w _ _ _ _ I), Nat.ltb_irrefl, Nat.eqb_refl; reflexivity|].
        assert (EK : eokx p c (cs s c) (pcs s c) (tp s c) (tm s) d u B).
        { destruct Hh as [(_ & Ok)|(t2 & xs & ev & nv & _ & _ & _ & _ & Ok)]; [left; exact Ok|right; eauto]. }
        assert (NF : d <> DFn FFull).
        { destruct Hh as [(_ & Ok)|(t2 & xs & ev & nv & _ & -> & _ & _ & _)]; [apply (early_nofull _ _ _ _ _ _ _ _ _ Ok)|discriminate]. }
        split; [exact EK|]. split; auto. split; [|split; [|split; [|split]]].
        -- unfold t1. rewrite ai_s', !Nat.eqb_refl. apply eof_inst. exact NF.
        -- intros j t0 X. unfold t1. split; [apply oc_old_s'; auto|]. split; [symmetry; apply rg_old_s'; auto; congruence|].
           apply (oc_lt_tm p s c j t0 I X).
        -- intros j t0 X Y. unfold t1 in X. rewrite oc_s', Nat.eqb_refl in X. destruct (Nat.eqb_spec j k); [injection X; lia|auto].
        -- intros j d' X Y Z. unfold t1. rewrite ai_s', Nat.eqb_refl. destruct (Nat.eqb_spec j k); [subst; congruence|].
           rewrite Z. apply eof_inst. destruct (proj1 (i_pend p s I c j Y X)) as (d0 & A0 & N0').
           rewrite Z in A0. apply inst_of_inj in A0. subst d0. exact N0'.
        -- split; [split; [lia|intros j Lj Oj; unfold t1; rewrite oc_s', Nat.eqb_refl; destruct (Nat.eqb_spec j k); [lia|exact Oj]]|
              split; [intros j X Y; apply (proj1 (i_pend p s I c j Y X))|]].
           intros j t0 X. unfold t1. rewrite (oh_s' s c k (inst_of d) m' a K u w _ _ _ _). split; [exact X|apply (oh_lt_tm p s c j t0 I X)].
      * change (exists e d0, ent (evs s c k (inst_of d) m' a K u w (bor (bd (cs s c)) B) (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s)) t0 = Some e /\
          eokx p (ec e) cc0 pc0 N0 t0 d0 (erf e) B0 /\ pc0 < ek e /\
          eof (ai (cs (evs s c k (inst_of d) m' a K u w (bor (bd (cs s c)) B) (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s)) (ec e)) (ek e))
              (rg (cs (evs s c k (inst_of d) m' a K u w (bor (bd (cs s c)) B) (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s)) (ec e))) = Some d0 /\
          (forall j t1, oc cc0 j = Some t1 -> oc (cs (evs s c k (inst_of d) m' a K u w (bor (bd (cs s c)) B) (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s)) (ec e)) j = Some t1 /\
             rg cc0 j = rg (cs (evs s c k (inst_of d) m' a K u w (bor (bd (cs s c)) B) (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s)) (ec e)) j /\ t1 < t0) /\
          (forall j t1, oc (cs (evs s c k (inst_of d) m' a K u w (bor (bd (cs s c)) B) (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s)) (ec e)) j = Some t1 -> t1 < t0 -> oc cc0 j = Some t1) /\
          (forall j d', oc cc0 j <> None -> pc0 <= j -> ai cc0 j = inst_of d' ->
             eof (ai (cs (evs s c k (inst_of d) m' a K u w (bor (bd (cs s c)) B) (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s)) (ec e)) j)
                 (rg (cs (evs s c k (inst_of d) m' a K u w (bor (bd (cs s c)) B) (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s)) (ec e))) = Some d') /\
          (pc0 <= pcs s (ec e) /\ forall j, j < pc0 -> oc cc0 j = None -> oc (cs (evs s c k (inst_of d) m' a K u w (bor (bd (cs s c)) B) (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s)) (ec e)) j = None) /\
          (forall j, oc cc0 j <> None -> pc0 <= j -> exists d', ai cc0 j = inst_of d' /\ d' <> DFn FFull) /\
          (forall j t1, oh cc0 j = Some t1 -> oh (cs (evs s c k (inst_of d) m' a K u w (bor (bd (cs s c)) B) (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s)) (ec e)) j = Some t1 /\ t1 < t0)).
        apply (snap_old p s c k _ m' a K u w _ _ _ _ I Sv H2 ltac:(lia) (fun _ => le_n _) t0 cc0 pc0 N0 B0 He Hn).
  - (* match *)
    split; [|split].
    + apply S1.
    + intros t0 e He N. destruct (S2 t0 e He N) as [Lk Q]. split.
      * rewrite pcs_match. destruct (Nat.eqb_spec (ec e) c); [rewrite e0 in *|]; lia.
      * intros j t1 Lj Oj. rewrite oc_match in Oj. exact (Q j t1 Lj Oj).
    + intros t0 cc0 pc0 N0 B0 He Hn. destruct (S3 t0 cc0 pc0 N0 B0 He Hn) as (e & d0 & A & Bk & C & D & E & F & G & L & Pn & Ph).
      exists e, d0. split; auto. split; auto. split; auto.
      destruct (proj1 (i_pend p s I c (pcs s c) (le_n _) H1)) as (d1 & A1 & N1).
      rewrite H2 in A1. apply inst_of_inj in A1. subst d1.
      assert (AIM : forall j d', eof (ai (cs s (ec e)) j) (rg (cs s (ec e))) = Some d' ->
                eof (ai (cs (smatch p s c) (ec e)) j) (rg (cs (smatch p s c) (ec e))) = Some d').
      { intros j d' X. rewrite rg_match, ai_match. destruct (Nat.eqb_spec (ec e) c), (Nat.eqb_spec j (pcs s c)); simpl; auto.
        subst. rewrite H2, (eof_inst d _ N1) in X. injection X as <-. exact H3. }
      split; [apply AIM; auto|]. split; [|split; [|split]].
      * intros j t1 X. rewrite oc_match, rg_match. auto.
      * intros j t1 X. rewrite oc_match in X. auto.
      * intros j d' X Y Z. apply AIM. auto.
      * split; [|split; [exact Pn|]].
        -- destruct L as (L1 & L2). split; [rewrite pcs_match; destruct (Nat.eqb_spec (ec e) c); [rewrite e0 in *|]; lia|].
           intros j Lj Oj. rewrite oc_match. auto.
        -- intros j t1 X. rewrite oh_match. auto.
  - (* a CAS's read alone *)
    split; [|split].
    + intros t0 L. unfold sread in L |- *; simpl in L |- *. unfold upd. destruct (Nat.eqb_spec t0 (tm s)); [lia|]. apply S1. lia.
    + intros t0 e He N. unfold sread in N; simpl in N. unfold upd in N. destruct (Nat.eqb_spec t0 (tm s)); [discriminate|].
      assert (Lt : t0 < tm s).
      { unfold ent, sread in He; simpl in He. destruct (Nat.lt_ge_cases t0 (tm s)) as [X|X]; auto.
        rewrite nth_error_app2 in He by (rewrite <- (i_tm p s I); lia).
        destruct (t0 - length (lg s)) as [|n0] eqn:Z; [pose proof (i_tm p s I); lia|destruct n0; discriminate]. }
      rewrite (rd_ent_old p s c k xs B m' a K u w bv I t0 Lt) in He.
      destruct (S2 t0 e He N) as [Lk Q]. split; [exact Lk|]. intros j t1 Lj Oj.
      rewrite (rd_oc s c k xs B m' a K u w bv) in Oj. exact (Q j t1 Lj Oj).
    + intros t0 cc0 pc0 N0 B0 He Hn. unfold sread in He; simpl in He. unfold upd in He. destruct (Nat.eqb_spec t0 (tm s)).
      * subst t0. exfalso. assert (E : ent (sread s c k Plain xs B m' a K u w bv) (tm s) = Some (newevh s c k (ILd Plain xs (fun _ => true)) K u w)).
        { unfold ent, sread; simpl. rewrite (i_tm p s I), nth_error_app2, Nat.sub_diag by lia. reflexivity. }
        specialize (Hn _ E). discriminate.
      * apply (snap_old_rd p s c k xs B m' a K u w bv I Sv H2 H1 Hh t0 cc0 pc0 N0 B0 He Hn).
  - (* passing a non-executing instruction *)
    split; [|split].
    + apply S1.
    + intros t0 e He N. destruct (S2 t0 e He N) as [Lk Q]. split.
      * rewrite (pcs_skip p s c). destruct (Nat.eqb_spec (ec e) c); [rewrite e0 in *|]; lia.
      * intros j t1 Lj Oj. rewrite (oc_skip p s c) in Oj. exact (Q j t1 Lj Oj).
    + intros t0 cc0 pc0 N0 B0 He Hn. destruct (S3 t0 cc0 pc0 N0 B0 He Hn) as (e & d0 & A & Bk & C & D & E & F & G & L & Pn & Ph).
      assert (AIS : forall j, oc (cs s (ec e)) j <> None -> ai (cs (sskip p s c) (ec e)) j = ai (cs s (ec e)) j).
      { intros j X. rewrite (ai_skip p s c). destruct (Nat.eqb_spec (ec e) c), (Nat.eqb_spec j (pcs s c)); simpl; auto.
        exfalso. apply X. rewrite e0, e1. exact K2. }
      assert (OK : oc (cs s (ec e)) (ek e) <> None)
        by (destruct (i_et p s I t0 e A) as (_ & O); rewrite (Hn e A) in O; congruence).
      exists e, d0. split; auto. split; auto. split; auto.
      split; [rewrite (AIS _ OK), (rg_skip p s c); exact D|]. split; [|split; [|split]].
      * intros j t1 X. rewrite (oc_skip p s c), (rg_skip p s c). auto.
      * intros j t1 X. rewrite (oc_skip p s c) in X. auto.
      * intros j d' X Y Z. destruct (oc cc0 j) as [tj|] eqn:Oj; [|congruence].
        destruct (E j tj Oj) as (X1 & _ & _). rewrite (AIS j ltac:(congruence)), (rg_skip p s c). apply G; [congruence|exact Y|exact Z].
      * split; [|split; [exact Pn|]].
        -- destruct L as (L1 & L2). split; [rewrite (pcs_skip p s c); destruct (Nat.eqb_spec (ec e) c); [rewrite e0 in *|]; lia|].
           intros j Lj Oj. rewrite (oc_skip p s c). auto.
        -- intros j t1 X. rewrite (oh_skip p s c). auto.
  - (* S3c: a result fixed: a failure after the read half changes the record's register, of a slot that did not happen *)
    assert (SF : SI p (sflp s cX oX bX)).
    { destruct oX as [kF|]; [destruct bX|]; cbn [sflp]; try exact Sv.
      destruct (cfix_rec _ _ _ _ _ _ _ _ _ HcX) as (HpF & HoF & HhF & HvF).
        assert (EV : forall c' j t1, oc (cs s c') j = Some t1 -> forall d1,
                   eof (ai (cs s c') j) (rg (cs s c')) = Some d1 -> eof (ai (cs (scfail s cX kF) c') j) (rg (cs (scfail s cX kF) c')) = Some d1).
        { intros c' j t1 O d1 D1. rewrite ai_cf. rewrite <- D1. apply eof_ieval. apply (ieval_slot_cf p s cX kF I HpF HoF c' j t1 O). }
        split; [|split].
        + intros t0 L. apply S1. exact L.
        + intros t0 e He N. rewrite oc_cf. exact (S2 t0 e He N).
        + intros t0 cc0 pc0 N0 B0 He Hn. destruct (S3 t0 cc0 pc0 N0 B0 He Hn) as (e & d0 & A & Bk & C & D & E & F & G & L & Pn & Ph).
          assert (OK : oc (cs s (ec e)) (ek e) <> None)
            by (destruct (i_et p s I t0 e A) as (_ & O); rewrite (Hn e A) in O; congruence).
          exists e, d0. split; auto. split; auto. split; auto.
          split; [destruct (oc (cs s (ec e)) (ek e)) as [te|] eqn:Oe; [exact (EV _ _ te Oe d0 D)|congruence]|].
          split; [|split; [|split; [|split]]].
          * intros j t1 X. destruct (E j t1 X) as (X1 & X2 & X3). rewrite oc_cf. split; [exact X1|split; [|exact X3]].
            rewrite rg_cf; [exact X2|]. destruct (Nat.eq_dec (ec e) cX) as [Ec|Nc]; [right; intros Ej; rewrite Ec, Ej in X1; congruence|left; exact Nc].
          * intros j t1 X. rewrite oc_cf in X. auto.
          * intros j d' X Y Z. destruct (oc cc0 j) as [tj|] eqn:Oj; [|congruence].
            destruct (E j tj Oj) as (X1 & _ & _). apply (EV _ _ tj X1). apply G; [congruence|exact Y|exact Z].
          * destruct L as (L1 & L2). split; [exact L1|]. intros j Lj Oj. rewrite oc_cf. auto.
          * split; [exact Pn|]. intros j t1 X. rewrite oh_cf. auto. }
    destruct SF as (S1' & S2' & S3').
    split; [|split].
    + intros t0 L. apply S1'. exact L.
    + intros t0 e He N. change (pcs (scfix0 (sflp s cX oX bX) cX jX bX BX)) with (pcs (sflp s cX oX bX)). rewrite oc_cx. exact (S2' t0 e He N).
    + intros t0 cc0 pc0 N0 B0 He Hn. destruct (S3' t0 cc0 pc0 N0 B0 He Hn) as (e & d0 & X). exists e, d0.
      change (pcs (scfix0 (sflp s cX oX bX) cX jX bX BX)) with (pcs (sflp s cX oX bX)). rewrite !ai_cx, !rg_cx, !oc_cx, !oh_cx. exact X.
Qed.

Lemma SI_run : forall p s, run p s -> SI p s.
Proof.
  intros p s R. induction R as [|s t R IH H].
  - apply SI_init.
  - apply (SI_step p s t R H IH).
Qed.

(* in a finished run, an access that happened before an earlier instruction
   j of its context happened early, against a snapshot in which j had not
   happened *)
Lemma early_of : forall p s c j k tj tk, run p s -> j < k ->
  oc (cs s c) j = Some tj -> oc (cs s c) k = Some tk -> tk < tj ->
  exists cc0 pc0 N0 B0 d e, es s tk = Some (cc0, pc0, N0, B0) /\ ent s tk = Some e /\ ec e = c /\ ek e = k /\
    eokx p c cc0 pc0 N0 tk d (erf e) B0 /\ eof (ai (cs s c) k) (rg (cs s c)) = Some d /\
    pc0 <= j /\ oc cc0 j = None /\
    (forall i t0, oc cc0 i = Some t0 -> oc (cs s c) i = Some t0 /\ rg cc0 i = rg (cs s c) i /\ t0 < tk) /\
    (forall i t0, oc (cs s c) i = Some t0 -> t0 < tk -> oc cc0 i = Some t0) /\
    (forall i d', oc cc0 i <> None -> pc0 <= i -> ai cc0 i = inst_of d' ->
        eof (ai (cs s c) i) (rg (cs s c)) = Some d') /\
    (forall i, oc cc0 i <> None -> pc0 <= i -> exists d', ai cc0 i = inst_of d' /\ d' <> DFn FFull) /\
    (forall i t0, oh cc0 i = Some t0 -> oh (cs s c) i = Some t0 /\ t0 < tk).
Proof.
  intros p s c j k tj tk R L Oj Ok Lt. pose proof (Inv1_run p s R) as I. pose proof (SI_run p s R) as (S1 & S2 & S3).
  destruct (i_oc p s I c k tk Ok) as (e & A & B & C).
  destruct (es s tk) as [[[[cc0 pc0] N0] B0]|] eqn:Es.
  - assert (Hn : forall e0, ent s tk = Some e0 -> eh e0 = false).
    { intros e0 E0. rewrite A in E0. injection E0 as <-. destruct (i_et p s I tk e A) as (_ & X).
      destruct (eh e) eqn:Eh; [|reflexivity]. exfalso. rewrite B, C in X.
      destruct (i_hoc p s I c k tk tk X Ok) as (Z & _). lia. }
    destruct (S3 tk cc0 pc0 N0 B0 Es Hn) as (e' & d & A' & Ok' & Pk & D & E & F & G & Lp & Pn & Ph). rewrite A in A'. injection A' as <-.
    rewrite B, C in *. exists cc0, pc0, N0, B0, d, e.
    do 6 (split; [auto|]). split; [|split; [|split; [exact E|split; [exact F|split; [exact G|split; [exact Pn|exact Ph]]]]]].
    + destruct (Nat.lt_ge_cases j pc0) as [X|X]; [|lia]. exfalso. destruct Lp as (_ & Lp).
      destruct (oc cc0 j) as [t0|] eqn:Y.
      * destruct (E j t0 Y) as (Y1 & _ & Y3). rewrite Oj in Y1. injection Y1 as <-. lia.
      * rewrite (Lp j X Y) in Oj. discriminate.
    + destruct (oc cc0 j) as [t0|] eqn:Y; auto. destruct (E j t0 Y) as (Y1 & _ & Y3). rewrite Oj in Y1. injection Y1 as <-. lia.
  - exfalso. destruct (S2 tk e A Es) as [_ Q]. rewrite B, C in Q. pose proof (Q j tj L Oj). lia.
Qed.
