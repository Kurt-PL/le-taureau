(* Model2: more facts about sequential interleavings: continuing a run,
   splitting it, running one context alone, and making a race. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2SC.

(* steps from a given sequential state *)
Inductive sruns (p : prog) : sst -> list sev -> sst -> Prop :=
| srs0 : forall g, sruns p g [] g
| srsS : forall g l g' e g'', sruns p g l g' -> sstep p g' e g'' -> sruns p g (l ++ [e]) g''.

Lemma racy_g_mk : forall p l i j e1 e2 x xs1 xs2 w1 w2,
  i < j -> nth_error l i = Some e1 -> nth_error l j = Some e2 -> sx e1 <> sx e2 ->
  sacc e1 = Some (xs1, w1) -> sacc e2 = Some (xs2, w2) -> In x xs1 -> In x xs2 -> orb w1 w2 = true ->
  ~ gsync l i j (sx e1) (sx e2) -> ~ (fa p (sx e1) (sk e1) /\ fa p (sx e2) (sk e2)) -> racy_g p l.
Proof. intros. exists i, j, e1, e2, x, xs1, xs2, w1, w2. repeat split; auto. Qed.

Lemma nth_app_last' : forall {A} (l : list A) e, nth_error (l ++ [e]) (length l) = Some e.
Proof. intros. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.

Lemma nth_app_old' : forall {A} (l : list A) e q, q < length l -> nth_error (l ++ [e]) q = nth_error l q.
Proof. intros. apply nth_error_app1. auto. Qed.

Lemma firstn_S_nth : forall {A} (l : list A) q e, nth_error l q = Some e -> firstn (S q) l = firstn q l ++ [e].
Proof.
  intros A l. induction l as [|a l IH]; intros q e H; [destruct q; discriminate|].
  destruct q as [|q]; simpl in *; [injection H as <-; reflexivity|]. rewrite (IH q e H). reflexivity.
Qed.

Lemma firstn_nth' : forall {A} (l : list A) n q, q < n -> nth_error (firstn n l) q = nth_error l q.
Proof.
  intros A l. induction l as [|a l IH]; intros n q L; destruct n as [|n]; try lia.
  - destruct q; reflexivity.
  - destruct q as [|q]; [reflexivity|]. simpl. apply IH. lia.
Qed.

Lemma firstn_nth_lt : forall {A} (l : list A) n q e, nth_error (firstn n l) q = Some e -> q < n /\ nth_error l q = Some e.
Proof.
  intros A l n q e H. assert (L : q < length (firstn n l)) by (apply nth_error_Some; congruence).
  rewrite length_firstn in L. split; [lia|]. rewrite <- (firstn_nth' l n q) by lia. auto.
Qed.

Lemma upd_eq_m : forall {A} (f : nat -> A) k v, upd f k v k = v.
Proof. intros. unfold upd. rewrite Nat.eqb_refl. reflexivity. Qed.

Section S.
Variable p : prog.
Hypothesis W : wf p.
(* the choice of the CAS outcomes whose values are equal (spurious failure), from the SC state *)
Variable bs : sst -> nat -> bool.

Lemma sruns_app : forall l g, srun p l g -> forall l2 g2, sruns p g l2 g2 -> srun p (l ++ l2) g2.
Proof.
  intros l g R l2 g2 H. induction H as [g0|g0 l0 g' e g'' H IH St].
  - rewrite app_nil_r. auto.
  - rewrite app_assoc. econstructor; eauto.
Qed.

Lemma sruns_trans : forall g1 l1 g2 l2 g3, sruns p g1 l1 g2 -> sruns p g2 l2 g3 -> sruns p g1 (l1 ++ l2) g3.
Proof.
  intros g1 l1 g2 l2 g3 H1 H2. induction H2 as [g0|g0 l0 g' e g'' H IH St].
  - rewrite app_nil_r. auto.
  - rewrite app_assoc. econstructor; eauto.
Qed.

Lemma sruns_one : forall g e g', sstep p g e g' -> sruns p g [e] g'.
Proof. intros g e g' H. change [e] with ([] ++ [e]). econstructor; [constructor|eauto]. Qed.

Lemma srun_split : forall l1 l2 g, srun p (l1 ++ l2) g -> exists g1, srun p l1 g1 /\ sruns p g1 l2 g.
Proof.
  intros l1 l2. revert l1. induction l2 as [|e l2 IH] using rev_ind; intros l1 g H.
  - rewrite app_nil_r in H. exists g. split; [auto|constructor].
  - rewrite app_assoc in H. inversion H as [E|l0 g0 e0 g' R0 St E].
    + destruct (l1 ++ l2); discriminate.
    + apply app_inj_tail in E as [E1 E2]. subst l0 e0.
      destruct (IH l1 g0 R0) as (g1 & A & B). exists g1. split; [auto|]. econstructor; eauto.
Qed.

Lemma sruns_sp : forall g l g', sruns p g l g' -> forall c, sp g c <= sp g' c.
Proof.
  intros g l g' H. induction H as [g0|g0 l0 g1 e g2 H IH St]; intros c; auto.
  destruct (sstep_shape p W g1 e g2 St) as (i & _ & _ & _ & Hsp & _). rewrite Hsp. unfold upd.
  specialize (IH c). destruct (Nat.eqb_spec c (sx e)) as [->|]; lia.
Qed.

Lemma sruns_split : forall g l1 l2 g', sruns p g (l1 ++ l2) g' -> exists g1, sruns p g l1 g1 /\ sruns p g1 l2 g'.
Proof.
  intros g l1 l2. revert l1. induction l2 as [|e l2 IH] using rev_ind; intros l1 g' H.
  - rewrite app_nil_r in H. exists g'. split; [auto|constructor].
  - rewrite app_assoc in H. inversion H as [|g0 l0 g1 e0 g2 R0 St]; subst.
    + exfalso. match goal with Hx : [] = _ |- _ => destruct (l1 ++ l2); discriminate end.
    + match goal with Hx : l0 ++ [e0] = (l1 ++ l2) ++ [e] |- _ => apply app_inj_tail in Hx as [E1 E2] end. subst.
      destruct (IH l1 g1 R0) as (g3 & A & B). exists g3. split; [auto|]. econstructor; eauto.
Qed.

(* the events of a continuation are at slots between the two positions *)
Lemma sruns_pos : forall g l g', sruns p g l g' -> forall e, In e l -> sp g (sx e) <= sk e /\ sk e < sp g' (sx e).
Proof.
  intros g l g' H. induction H as [g0|g0 l0 g1 e g2 H IH St]; intros e' I; [destruct I|].
  destruct (sstep_shape p W g1 e g2 St) as (i & _ & _ & Hk & Hsp & _).
  apply in_app_or in I. destruct I as [I|[<-|[]]].
  - destruct (IH e' I) as [A B]. split; [auto|]. rewrite Hsp. unfold upd. destruct (Nat.eqb_spec (sx e') (sx e)) as [E|]; [rewrite E in *|]; lia.
  - pose proof (sruns_sp g0 l0 g1 H (sx e)). rewrite Hsp, upd_eq_m. lia.
Qed.

(* registers of slots already passed do not change *)
Lemma sruns_regs : forall g l g', sruns p g l g' -> forall c j, j < sp g c -> sr g' c j = sr g c j.
Proof.
  intros g l g' H. induction H as [g0|g0 l0 g1 e g2 H IH St]; intros c j L; auto.
  destruct (sstep_shape p W g1 e g2 St) as (i & _ & _ & Hk & Hsp & Hr & _).
  rewrite Hr; [apply IH; auto|].
  destruct (Nat.eq_dec c (sx e)) as [->|N]; [right|left; auto].
  pose proof (sruns_sp g0 l0 g1 H (sx e)). lia.
Qed.

(* the steps of other contexts leave a context alone *)
Lemma sruns_other : forall g l g' c, sruns p g l g' -> (forall e, In e l -> sx e <> c) ->
  sp g' c = sp g c /\ forall j, sr g' c j = sr g c j.
Proof.
  intros g l g' c H. induction H as [g0|g0 l0 g1 e g2 H IH St]; intros N; [auto|].
  destruct IH as [A B]; [intros e' I; apply N; apply in_or_app; auto|].
  assert (Ne : sx e <> c) by (apply N; apply in_or_app; right; left; auto).
  destruct (sstep_shape p W g1 e g2 St) as (i & _ & _ & _ & Hsp & Hr & _).
  rewrite Hsp. unfold upd. destruct (Nat.eqb_spec c (sx e)); [congruence|]. split; [congruence|].
  intros j. rewrite <- B. apply Hr. left. auto.
Qed.

(* ---------- one context alone ---------- *)
Definition snext (g : sst) (c : nat) : sev * sst :=
  let k := sp g c in let r := sr g c in
  let sp' := upd (sp g) c (S k) in
  match ins p c k r with
  | ILd md xs cnd => if cnd r then (mkE c k (Some (dd xs, false)) false,
                                    mkSS sp' (upd (sr g) c (upd r k (enc (map (sm g) (dd xs))))) (sm g))
                    else (mkE c k None false, mkSS sp' (sr g) (sm g))
  | ISt md xs cnd v => if cnd r then (mkE c k (Some (dd xs, true)) false,
                                      mkSS sp' (sr g) (mupd (sm g) (dd xs) (projs (length (dd xs)) (v r))))
                    else (mkE c k None false, mkSS sp' (sr g) (sm g))
  | ICas md xs cnd e nv => if cnd r then
        (mkE c k (Some (dd xs, (Nat.eqb (enc (map (sm g) (dd xs))) (e r) && bs g c))) false,
         mkSS sp' (upd (sr g) c (upd r k (vd ((Nat.eqb (enc (map (sm g) (dd xs))) (e r) && bs g c)) (enc (map (sm g) (dd xs))))))
              (if (Nat.eqb (enc (map (sm g) (dd xs))) (e r) && bs g c) then mupd (sm g) (dd xs) (projs (length (dd xs)) (nv r)) else sm g)
             )
        else (mkE c k None false, mkSS sp' (sr g) (sm g))
  | IFn fk => (mkE c k None (match fk with FFull => true | _ => false end), mkSS sp' (sr g) (sm g))
  | INop => (mkE c k None false, mkSS sp' (sr g) (sm g))
  end.

(* the register the step leaves at its slot *)
Lemma snext_reg : forall g c, sr (snd (snext g c)) c (sp g c) =
  (let i := ins p c (sp g c) (sr g c) in
   if xload i (sr g c)
   then areg i (Nat.eqb (enc (map (sm g) (icells i))) (cexp i (sr g c)) && bs g c) (enc (map (sm g) (icells i)))
   else sr g c (sp g c)).
Proof.
  intros g c. unfold snext. cbv zeta. destruct (ins p c (sp g c) (sr g c)) as [m xs cnd|m xs cnd v|m xs cnd e nv|fk|];
    unfold xload, icond, ieval; simpl; try reflexivity; destruct (cnd (sr g c)); simpl; try reflexivity;
    unfold upd; rewrite !Nat.eqb_refl; reflexivity.
Qed.

Lemma snext_step : forall g c, sstep p g (fst (snext g c)) (snd (snext g c)).
Proof.
  intros g c. unfold snext. destruct (ins p c (sp g c) (sr g c)) eqn:E.
  - destruct (c0 (sr g c)) eqn:C; simpl.
    + eapply ss_ld; eauto.
    + eapply ss_skip; [exact E|reflexivity|unfold icond, ieval; simpl; auto].
  - destruct (c0 (sr g c)) eqn:C; simpl.
    + eapply ss_st; eauto.
    + eapply ss_skip; [exact E|reflexivity|unfold icond, ieval; simpl; auto].
  - destruct (c0 (sr g c)) eqn:C; simpl.
    + eapply ss_cas; eauto.
    + eapply ss_skip; [exact E|reflexivity|unfold icond, ieval; simpl; auto].
  - simpl. eapply ss_fn; eauto.
  - simpl. eapply ss_nop; eauto.
  Unshelve. all: exact true.
Qed.

Lemma snext_x : forall g c, sx (fst (snext g c)) = c.
Proof.
  intros g c. unfold snext. destruct (ins p c (sp g c) (sr g c)); try reflexivity;
  match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.

Fixpoint solo (g : sst) (c : nat) (m : nat) : list sev * sst :=
  match m with
  | 0 => ([], g)
  | S m' => let lg := solo g c m' in (fst lg ++ [fst (snext (snd lg) c)], snd (snext (snd lg) c))
  end.

Lemma solo_runs : forall g c m, sruns p g (fst (solo g c m)) (snd (solo g c m)).
Proof. intros g c m. induction m as [|m IH]; simpl; [constructor|]. econstructor; [exact IH|apply snext_step]. Qed.

(* runs whose steps are the replay's own steps *)
Inductive nruns : sst -> list sev -> sst -> Prop :=
| nrs0 : forall g, nruns g [] g
| nrsS : forall g l g' c, nruns g l g' -> nruns g (l ++ [fst (snext g' c)]) (snd (snext g' c)).

Lemma nruns_sruns : forall g l g', nruns g l g' -> sruns p g l g'.
Proof. intros g l g' H. induction H; [constructor|]. econstructor; [exact IHnruns|apply snext_step]. Qed.

Lemma solo_nruns : forall g c m, nruns g (fst (solo g c m)) (snd (solo g c m)).
Proof. intros g c m. induction m as [|m IH]; simpl; [constructor|]. apply nrsS. exact IH. Qed.

Lemma nruns_trans : forall g1 l1 g2 l2 g3, nruns g1 l1 g2 -> nruns g2 l2 g3 -> nruns g1 (l1 ++ l2) g3.
Proof.
  intros g1 l1 g2 l2 g3 H1 H2. revert H1. induction H2 as [|g l g' c H IH]; intros H1; [rewrite app_nil_r; exact H1|].
  rewrite app_assoc. apply nrsS. exact (IH H1).
Qed.

Lemma nruns_split : forall g l1 l2 g', nruns g (l1 ++ l2) g' -> exists g1, nruns g l1 g1 /\ nruns g1 l2 g'.
Proof.
  intros g l1 l2. revert l1. induction l2 as [|e l2 IH] using rev_ind; intros l1 g' H.
  - rewrite app_nil_r in H. exists g'. split; [auto|constructor].
  - rewrite app_assoc in H. inversion H as [|g0 l0 g1 c0 R0]; subst.
    + exfalso. match goal with Hx : [] = _ |- _ => destruct (l1 ++ l2); discriminate end.
    + match goal with Hx : l0 ++ [_] = (l1 ++ l2) ++ [e] |- _ => apply app_inj_tail in Hx as [E1 E2] end. subst.
      destruct (IH l1 g1 R0) as (g3 & A & B). exists g3. split; [auto|]. apply nrsS. exact B.
Qed.

Lemma nruns_g0 : forall g g', nruns g [] g' -> g' = g.
Proof.
  intros g g' H. remember [] as l eqn:El. destruct H as [g0|g0 l0 g1 c0 H]; [reflexivity|].
  exfalso. destruct l0; discriminate.
Qed.

Lemma nruns_head : forall g l g', nruns g l g' -> forall e l', l = e :: l' ->
  exists c, e = fst (snext g c) /\ nruns (snd (snext g c)) l' g'.
Proof.
  intros g l g' H. induction H as [g0|g0 l0 g1 c0 H IH]; intros e l' E; [discriminate|].
  destruct l0 as [|a l0].
  - simpl in E. injection E as <- <-. rewrite (nruns_g0 _ _ H). exists c0. split; [reflexivity|constructor].
  - simpl in E. injection E as <- <-. destruct (IH a l0 eq_refl) as (c1 & E1 & N1). exists c1. split; [exact E1|].
    apply nrsS. exact N1.
Qed.

Lemma solo_x : forall g c m e, In e (fst (solo g c m)) -> sx e = c.
Proof.
  intros g c m. induction m as [|m IH]; intros e I; simpl in I; [destruct I|].
  apply in_app_or in I. destruct I as [I|[<-|[]]]; [auto|apply snext_x].
Qed.

Lemma solo_sp : forall g c m, sp (snd (solo g c m)) c = sp g c + m.
Proof.
  intros g c m. induction m as [|m IH]; simpl; [lia|].
  destruct (sstep_shape p W _ _ _ (snext_step (snd (solo g c m)) c)) as (i & _ & _ & _ & Hsp & _).
  rewrite Hsp, snext_x. unfold upd. rewrite Nat.eqb_refl. lia.
Qed.

Lemma solo_len : forall g c m, length (fst (solo g c m)) = m.
Proof. intros g c m. induction m as [|m IH]; simpl; auto. rewrite length_app. simpl. lia. Qed.

Lemma solo_stable : forall g c m m' j, m <= m' -> j < sp g c + m ->
  sr (snd (solo g c m')) c j = sr (snd (solo g c m)) c j.
Proof.
  intros g c m m' j L Lj. induction m' as [|m' IH].
  - assert (m = 0) by lia. subst. reflexivity.
  - destruct (Nat.eq_dec m (S m')) as [->|N]; [reflexivity|]. simpl.
    destruct (sstep_shape p W _ _ _ (snext_step (snd (solo g c m')) c)) as (i & _ & _ & Hk & _ & Hr & _).
    rewrite Hr; [apply IH; lia|]. right. rewrite Hk, snext_x, solo_sp. lia.
Qed.

Lemma solo_prefix : forall g c m m', m <= m' -> exists l2, fst (solo g c m') = fst (solo g c m) ++ l2 /\
  sruns p (snd (solo g c m)) l2 (snd (solo g c m')).
Proof.
  intros g c m m' L. induction m' as [|m' IH].
  - assert (m = 0) by lia. subst. exists []. split; [reflexivity|constructor].
  - destruct (Nat.eq_dec m (S m')) as [->|N]; [exists []; split; [rewrite app_nil_r; auto|constructor]|].
    destruct (IH ltac:(lia)) as (l2 & E & H). exists (l2 ++ [fst (snext (snd (solo g c m')) c)]). simpl. split.
    + rewrite E, app_assoc. reflexivity.
    + econstructor; [exact H|apply snext_step].
Qed.

(* the solo run's registers, as one function *)
Definition rinf (g : sst) (c : nat) : regs := fun j => sr (snd (solo g c (S j))) c j.

Lemma rinf_agree : forall g c m j, j < sp g c + m -> rinf g c j = sr (snd (solo g c m)) c j.
Proof.
  intros g c m j L. unfold rinf. destruct (Nat.le_ge_cases (S j) m) as [A|A].
  - symmetry. apply solo_stable; [auto|]. lia.
  - apply solo_stable; [auto|]. lia.
Qed.

(* ---------- memory ---------- *)
Lemma sruns_nowrite : forall g l g' x, sruns p g l g' -> (forall e, In e l -> writes_x e x = false) -> sm g' x = sm g x.
Proof.
  intros g l g' x H. induction H as [g0|g0 l0 g1 e g2 H IH St]; intros N; auto.
  destruct (sstep_shape p W g1 e g2 St) as (i & _ & _ & _ & _ & _ & _ & Hm & _).
  rewrite Hm. rewrite <- IH by (intros e' I; apply N; apply in_or_app; auto).
  rewrite (N e ltac:(apply in_or_app; right; left; auto)). reflexivity.
Qed.

Lemma sstep_load : forall g e g' i, sstep p g e g' -> ins p (sx e) (sk e) (sr g (sx e)) = i ->
  xload i (sr g (sx e)) = true -> rval i (sr g' (sx e) (sk e)) = enc (map (sm g) (icells i)).
Proof.
  intros g e g' i St Hi X. destruct (sstep_shape p W g e g' St) as (i' & Hi' & _ & _ & _ & _ & Hrk & _).
  rewrite Hi in Hi'. subst i'. rewrite X in Hrk. exact Hrk.
Qed.

Lemma sstep_store : forall g e g' i x, sstep p g e g' -> ins p (sx e) (sk e) (sr g (sx e)) = i ->
  writes_x e x = true -> sm g' x = cval (icells i) (wvals i (sr g (sx e))) x.
Proof.
  intros g e g' i x St Hi X. destruct (sstep_shape p W g e g' St) as (i' & Hi' & _ & _ & _ & _ & _ & Hm & _).
  rewrite Hi in Hi'. subst i'. rewrite Hm, X. reflexivity.
Qed.

End S.

(* ---------- deciding guard synchronisation ---------- *)
Definition gat (l : list sev) (q c : nat) : bool :=
  match nth_error l q with Some f => sg f && Nat.eqb (sx f) c | None => false end.

Definition gsyncb (l : list sev) (i j ci cj : nat) : bool :=
  existsb (fun i' => gat l i' ci && existsb (fun j' => gat l j' cj) (seq i' (S j - i'))) (seq i (S j - i)).

Lemma gsync_b : forall l i j ci cj, gsync l i j ci cj <-> gsyncb l i j ci cj = true.
Proof.
  intros l i j ci cj. unfold gsync, gsyncb. rewrite existsb_exists. split.
  - intros (i' & j' & f1 & f2 & A & B & C & D & E & F & G & H & K).
    exists i'. split; [apply in_seq; lia|]. apply andb_true_intro. split.
    + unfold gat. rewrite D, F. simpl. apply Nat.eqb_eq. auto.
    + apply existsb_exists. exists j'. split; [apply in_seq; lia|]. unfold gat. rewrite E, G.
      simpl. apply Nat.eqb_eq. auto.
  - intros (i' & Hi & X). apply in_seq in Hi. apply andb_prop in X. destruct X as [X Y].
    apply existsb_exists in Y. destruct Y as (j' & Hj & Y). apply in_seq in Hj.
    unfold gat in X, Y. destruct (nth_error l i') as [f1|] eqn:F1; [|discriminate].
    destruct (nth_error l j') as [f2|] eqn:F2; [|discriminate].
    apply andb_prop in X, Y. destruct X as [X1 X2]. destruct Y as [Y1 Y2].
    apply Nat.eqb_eq in X2, Y2. exists i', j', f1, f2. repeat split; auto; lia.
Qed.

Lemma gsync_dec : forall l i j ci cj, gsync l i j ci cj \/ ~ gsync l i j ci cj.
Proof. intros. rewrite gsync_b. destruct (gsyncb l i j ci cj); auto. Qed.

Lemma acc_nog : forall p l g q e x w, wf p -> srun p l g -> nth_error l q = Some e -> sacc e = Some (x, w) -> sg e = false.
Proof.
  intros p l g q e x w W R Q A. destruct (srun_ev p W l g R q e Q) as (i & _ & _ & Sh). rewrite A in Sh.
  destruct i as [md y c|md y c u|md y c e0 n|fk|]; simpl in Sh;
    try (destruct (c (sr g (sx e))); injection Sh; intros; subst; auto; discriminate); try discriminate;
    try (destruct fk; discriminate).
Qed.

(* ---------- the shape of an access's event ---------- *)
Lemma evshape_wflag : forall i r k d, dof i r = Some d -> is_store (inst_of d) = true ->
  fst (evshape i r k) = Some (icells (inst_of d), negb (is_cas (inst_of d)) || vok (r k)).
Proof.
  intros [m y c|m y c u|m y c e n| |] r k d D S; simpl in D; try discriminate;
    destruct (c r) eqn:C; try discriminate; injection D as <-; simpl in *; try discriminate;
    rewrite C; reflexivity.
Qed.

Lemma evshape_acc : forall i r k d, dof i r = Some d ->
  exists w, fst (evshape i r k) = Some (icells (inst_of d), w) /\ snd (evshape i r k) = false.
Proof.
  intros [m y c|m y c u|m y c e n| |] r k d D; simpl in D; try discriminate;
    destruct (c r) eqn:C; try discriminate; injection D as <-; simpl; rewrite C; eexists; split; reflexivity.
Qed.

Lemma snext_wflag : forall p bs g c d, dof (ins p c (sp g c) (sr g c)) (sr g c) = Some d ->
  is_store (inst_of d) = true ->
  sacc (fst (snext p bs g c)) = Some (icells (inst_of d),
    negb (is_cas (inst_of d)) || (Nat.eqb (enc (map (sm g) (icells (inst_of d)))) (eval_e (inst_of d) (sr g c)) && bs g c)).
Proof.
  intros p bs g c d D S. unfold snext.
  destruct (ins p c (sp g c) (sr g c)) as [m y c0|m y c0 u|m y c0 e n| |]; simpl in D; try discriminate;
    destruct (c0 (sr g c)) eqn:C; try discriminate; injection D as <-; simpl in *; try discriminate;
    rewrite ?andb_true_r; reflexivity.
Qed.

Lemma snext_acc : forall p bs g c d, dof (ins p c (sp g c) (sr g c)) (sr g c) = Some d ->
  exists w, sacc (fst (snext p bs g c)) = Some (icells (inst_of d), w) /\ sg (fst (snext p bs g c)) = false.
Proof.
  intros p bs g c d D. unfold snext.
  destruct (ins p c (sp g c) (sr g c)) as [m y c0|m y c0 u|m y c0 e n| |]; simpl in D; try discriminate;
    destruct (c0 (sr g c)) eqn:C; try discriminate; injection D as <-; simpl; eexists; split; reflexivity.
Qed.

Lemma sruns_single : forall p g e g', sruns p g [e] g' -> sstep p g e g'.
Proof.
  intros p g e g' H. remember [e] as L eqn:EL. destruct H as [g0|g0 l0 g1 e0 g2 H0 St].
  - discriminate.
  - destruct l0 as [|z l0]; [|destruct l0; discriminate]. injection EL as <-.
    remember [] as L0 eqn:E0. destruct H0; [exact St|]. destruct l; discriminate.
Qed.
