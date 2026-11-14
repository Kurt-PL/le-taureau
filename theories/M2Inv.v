(* Model2: structural invariants of runs: the log, the times, the slots
   passed and pending, the ties. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff.

Lemma upd_eq : forall {A} (f : nat -> A) k v, upd f k v k = v.
Proof. intros. unfold upd. rewrite Nat.eqb_refl. reflexivity. Qed.
Lemma upd_neq : forall {A} (f : nat -> A) k v k', k' <> k -> upd f k v k' = f k'.
Proof. intros. unfold upd. apply Nat.eqb_neq in H. rewrite H. reflexivity. Qed.
Lemma upd_case : forall {A} (f : nat -> A) k v k', upd f k v k' = if Nat.eqb k' k then v else f k'.
Proof. reflexivity. Qed.

Definition ent (s : st) (t : nat) : option oev := nth_error (lg s) t.

Lemma nth_error_app_last : forall {A} (l : list A) x n,
  nth_error (l ++ [x]) n = if Nat.ltb n (length l) then nth_error l n
                           else if Nat.eqb n (length l) then Some x else None.
Proof.
  intros. destruct (Nat.ltb_spec n (length l)).
  - apply nth_error_app1; auto.
  - rewrite nth_error_app2 by auto. destruct (Nat.eqb_spec n (length l)).
    + subst. rewrite Nat.sub_diag. reflexivity.
    + destruct (n - length l) as [|q] eqn:E; [lia|]. destruct q; reflexivity.
Qed.

(* ---------- an access and the instruction it is ---------- *)
Lemma dd_nodup : forall xs, NoDup (dd xs).
Proof. intros xs. apply NoDup_nodup. Qed.

Lemma dd_dd : forall xs, dd (dd xs) = dd xs.
Proof. intros xs. apply nodup_fixed_point. apply dd_nodup. Qed.

Lemma dd_in : forall x xs, In x (dd xs) <-> In x xs.
Proof. intros x xs. apply nodup_In. Qed.

Lemma icells_nodup : forall i, NoDup (icells i).
Proof. intros [| | | |]; simpl; try apply dd_nodup; constructor. Qed.

Lemma dof_shape : forall i r d, dof i r = Some d ->
  icells i = icells (inst_of d) /\ gop i = gop (inst_of d) /\ is_load i = is_load (inst_of d) /\
  is_store i = is_store (inst_of d) /\ (forall f, isfn f i = isfn f (inst_of d)) /\
  icond i r = true /\ ieval i r = ieval (inst_of d) r.
Proof.
  intros i r d H. destruct i as [m x c|m x c v|m x c e n| |]; simpl in H; try discriminate;
  destruct (c r) eqn:C; try discriminate; injection H as <-; simpl;
  unfold icond; simpl; rewrite C, ?dd_dd; repeat split; intros [| |]; reflexivity.
Qed.

Lemma dof_isfence : forall i r d, dof i r = Some d -> isfence i = isfence (inst_of d).
Proof.
  intros i r d H. destruct i as [m x c|m x c v|m x c e n| |]; simpl in H; try discriminate;
  destruct (c r); try discriminate; injection H as <-; reflexivity.
Qed.

(* an access is no atom fence *)
Lemma sameatom_dof : forall a i r d, dof i r = Some d -> sameatom a i = false /\ sameatom a (inst_of d) = false /\
  sameatom i a = false /\ sameatom (inst_of d) a = false.
Proof.
  intros a i r d H. destruct i as [m x c|m x c v|m x c e n| |]; simpl in H; try discriminate;
  destruct (c r); try discriminate; injection H as <-; destruct a as [| | |[]|]; repeat split; reflexivity.
Qed.

Lemma tiedb_dof_r : forall a i r d, dof i r = Some d -> tiedb a i = tiedb a (inst_of d).
Proof.
  intros a i r d H. destruct (dof_shape i r d H) as (E1 & E2 & E3 & E4 & E5 & _).
  destruct (sameatom_dof a i r d H) as (S1 & S2 & _).
  unfold tiedb. rewrite E1, E2, E3, E4, (E5 FLl), (E5 FSs), (E5 FLs), (E5 FSl), S1, S2. reflexivity.
Qed.

Lemma tiedb_dof_l : forall a i r d, dof i r = Some d -> tiedb i a = tiedb (inst_of d) a.
Proof.
  intros a i r d H. destruct (dof_shape i r d H) as (E1 & E2 & E3 & E4 & E5 & _).
  destruct (sameatom_dof a i r d H) as (_ & _ & S3 & S4).
  unfold tiedb. rewrite E1, E2, E3, E4, (E5 FLl), (E5 FSs), (E5 FLs), (E5 FSl), S3, S4. reflexivity.
Qed.

Lemma tied_dof_r : forall a i r d, dof i r = Some d -> (tied a i <-> tied a (inst_of d)).
Proof.
  intros a i r d H. split; intros T; apply b_tied; apply tied_b in T;
  [rewrite <- (tiedb_dof_r a i r d H)|rewrite (tiedb_dof_r a i r d H)]; auto.
Qed.

Lemma tied_dof_l : forall a i r d, dof i r = Some d -> (tied i a <-> tied (inst_of d) a).
Proof.
  intros a i r d H. split; intros T; apply b_tied; apply tied_b in T;
  [rewrite <- (tiedb_dof_l a i r d H)|rewrite (tiedb_dof_l a i r d H)]; auto.
Qed.

(* an access of some cell is tied to itself *)
Lemma tied_self_d : forall d, icells (inst_of d) <> [] -> tied (inst_of d) (inst_of d).
Proof. intros d H. left. destruct (icells (inst_of d)) as [|x l]; [congruence|]. exists x. simpl. auto. Qed.

Lemma tied_dof_self : forall i r d, dof i r = Some d -> icells i <> [] -> tied i (inst_of d).
Proof.
  intros i r d H N. apply (proj2 (tied_dof_l _ _ _ _ H)). apply tied_self_d.
  destruct (dof_shape _ _ _ H) as (Q1 & _). congruence.
Qed.

(* cellful: every access names at least one cell. An access of a zero-size
   referent covers no cell, and is modelled as INop *)
Definition cellful (p : prog) : Prop := forall c k r, isacc (ins p c k r) = true ->
  icells (ins p c k r) <> [].

(* a programme whose every access names a cell is cellful *)
Lemma cellful_of : forall p, (forall c k r, isacc (ins p c k r) = true -> icells (ins p c k r) <> []) -> cellful p.
Proof. intros p H. exact H. Qed.

Lemma dof_isacc : forall i r d, dof i r = Some d -> isacc i = true.
Proof.
  intros i r d H. destruct i as [m x c|m x c v|m x c e n| |]; simpl in H; try discriminate; reflexivity.
Qed.

Lemma cellful_dof : forall p c j r d, cellful p -> dof (ins p c j r) r = Some d ->
  icells (inst_of d) <> [].
Proof.
  intros p c j r d W D. destruct (dof_shape _ _ _ D) as (Q1 & Q2 & _). rewrite <- Q1.
  apply (W c j r). eapply dof_isacc; eauto.
Qed.

Lemma dof_exec : forall i r d, dof i r = Some d -> executes i r = true.
Proof.
  intros i r d H. destruct i as [m x c|m x c v|m x c e n| |]; simpl in H; try discriminate;
  destruct (c r) eqn:C; try discriminate; unfold executes; simpl; auto.
Qed.

Ltac texec := match goal with D : dof ?X ?r = Some _ |- executes ?X ?r = true => exact (dof_exec X r _ D) end.

Ltac tcell := match goal with
  | Wc : cellful ?p, D : dof (ins ?p ?c ?j ?r) ?r = Some ?d |- icells (inst_of ?d) <> [] =>
      exact (cellful_dof p c j r d Wc D)
  end.

Ltac tself := match goal with D : dof ?X ?r = Some ?d |- tied ?X (inst_of ?d) =>
  apply (proj2 (tied_dof_l _ _ _ _ D)); apply tied_self_d; try tcell end.


(* an access's effect (not a fence) *)
Definition isaccd (d : desc) : bool := match d with DFn _ => false | _ => true end.

Lemma dof_inst : forall d r, isaccd d = true -> dof (inst_of d) r = Some d.
Proof. intros [| | |f] r H; try reflexivity. discriminate. Qed.

Lemma inst_of_inj : forall d1 d2, inst_of d1 = inst_of d2 -> d1 = d2.
Proof.
  intros [m1 x1|m1 x1 v1|m1 x1 e1 n1|f1] [m2 x2|m2 x2 v2|m2 x2 e2 n2|f2]; simpl; intros H; try discriminate;
  injection H; intros; subst; auto.
  - assert (v1 = v2) by (apply (f_equal (fun g => g (fun _ => 0))) in H0; exact H0). subst. auto.
  - assert (e1 = e2) by (apply (f_equal (fun g => g (fun _ => 0))) in H1; exact H1).
    assert (n1 = n2) by (apply (f_equal (fun g => g (fun _ => 0))) in H0; exact H0). subst. auto.
Qed.

(* every well-formed programme is determined at every slot, in every
   context state: the instruction and its operands at slot k depend only on
   the registers before k, which settled registers keep (cited by
   M2Model.determined) *)
Lemma ord_determined : forall p cc c k, wf p -> determined p cc c k (ins p c k (rg cc)).
Proof.
  intros p cc c k W r S.
  destruct (W c k r (rg cc) (fun j L => S j (or_introl L))) as [E1 E2].
  split; [exact E1|]. rewrite <- E1. exact E2.
Qed.

(* ---------- what an instruction does, for R1 ---------- *)

Lemma eof_inst : forall d r, d <> DFn FFull -> eof (inst_of d) r = Some d.
Proof. intros [| | |[]] r N; try reflexivity. exfalso. apply N. reflexivity. Qed.

Lemma eof_cases : forall i r d, eof i r = Some d ->
  dof i r = Some d \/ (exists f, i = IFn f /\ d = DFn f /\ f <> FFull).
Proof.
  intros [m x c0|m x c0 v|m x c0 e n|[]|] r d H; simpl in H; auto; try discriminate; injection H as <-; right; eexists; repeat split; discriminate.
Qed.

Lemma eof_nofull : forall i r, eof i r <> Some (DFn FFull).
Proof.
  intros [m x c0|m x c0 v|m x c0 e n|[]|] r H; simpl in H; try discriminate;
  destruct (c0 r); discriminate.
Qed.

Lemma eof_acc : forall i r d, eof i r = Some d -> isaccd d = true -> dof i r = Some d.
Proof. intros i r d H A. destruct (eof_cases i r d H) as [D|(f & _ & -> & _)]; auto; discriminate. Qed.

Lemma dof_eof : forall i r d, dof i r = Some d -> eof i r = Some d.
Proof. intros [m x c0|m x c0 v|m x c0 e n|[]|] r d H; simpl in *; auto; discriminate. Qed.

Lemma dof_accd : forall i r d, dof i r = Some d -> isaccd d = true.
Proof.
  intros [m x c0|m x c0 v|m x c0 e n|[]|] r d H; simpl in H; try discriminate; destruct (c0 r); try discriminate;
  injection H as <-; reflexivity.
Qed.

Lemma eof_same : forall i r d, eof i r = Some d -> dof i r = Some d \/ i = inst_of d.
Proof. intros i r d H. destruct (eof_cases i r d H) as [D|(f & -> & -> & _)]; auto. Qed.

Lemma eof_icells : forall i r d, eof i r = Some d -> icells i = icells (inst_of d).
Proof. intros i r d H. destruct (eof_same i r d H) as [D| ->]; [apply (proj1 (dof_shape _ _ _ D))|reflexivity]. Qed.

Lemma tied_eof_l : forall a i r d, eof i r = Some d -> (tied i a <-> tied (inst_of d) a).
Proof. intros a i r d H. destruct (eof_same i r d H) as [D| ->]; [apply (tied_dof_l _ _ _ _ D)|tauto]. Qed.

Lemma tied_eof_r : forall a i r d, eof i r = Some d -> (tied a i <-> tied a (inst_of d)).
Proof. intros a i r d H. destruct (eof_same i r d H) as [D| ->]; [apply (tied_dof_r _ _ _ _ D)|tauto]. Qed.

Lemma eof_load : forall i r d, eof i r = Some d -> is_load i && icond i r = is_load (inst_of d).
Proof.
  intros i r d H. destruct (eof_same i r d H) as [D| ->].
  - destruct (dof_shape _ _ _ D) as (_ & _ & Q3 & _ & _ & Q6 & _). rewrite Q3, Q6. apply andb_true_r.
  - destruct d as [| | |[]]; simpl in H; try discriminate; reflexivity.
Qed.

Lemma load_accd : forall d, is_load (inst_of d) = true -> isaccd d = true.
Proof. intros [| | |f] H; auto. Qed.

Lemma store_accd : forall d, is_store (inst_of d) = true -> isaccd d = true.
Proof. intros [| | |f] H; auto. Qed.

Lemma eof_exec_tied : forall p c j r d, cellful p -> eof (ins p c j r) r = Some d ->
  executes (ins p c j r) r = true /\ tied (ins p c j r) (inst_of d).
Proof.
  intros p c j r d Wc H. destruct (eof_cases _ _ _ H) as [D|(f & E & -> & N)].
  - split; [texec|tself].
  - rewrite E. split; [reflexivity|]. do 7 right. destruct f; try reflexivity. contradiction.
Qed.

Lemma eof_tied_self : forall p c j r d, cellful p -> eof (ins p c j r) r = Some d -> tied (inst_of d) (inst_of d).
Proof.
  intros p c j r d Wc H. destruct (eof_exec_tied p c j r d Wc H) as [_ T].
  apply (proj1 (tied_eof_l _ _ _ _ H)) in T. exact T.
Qed.


Lemma eof_cas : forall i r d, eof i r = Some d -> is_cas i = is_cas (inst_of d).
Proof.
  intros [m x c|m x c v|m x c e n|[]|] r d H; simpl in H; try discriminate;
    try (destruct (c r); [injection H as <-|discriminate]); try (injection H as <-); reflexivity.
Qed.

Lemma ieval_inst : forall d r r', ieval (inst_of d) r = ieval (inst_of d) r'.
Proof. intros [] r r'; reflexivity. Qed.

(* ---------- the execution test ---------- *)
Lemma xex_exec : forall cc i r k, xex cc i r k = true -> executes i r = true.
Proof. intros cc i r k H. unfold xex, xexec in H. apply andb_prop in H. tauto. Qed.

Lemma exec_xex : forall cc i r k, executes i r = true -> (oh cc k <> None -> cfail i r k = false) ->
  xex cc i r k = true.
Proof.
  intros cc i r k E F. unfold xex, xexec, ohb. rewrite E. simpl.
  destruct (oh cc k); [rewrite F by discriminate; reflexivity|reflexivity].
Qed.

Lemma exec_xex_oh : forall cc i r k, executes i r = true -> oh cc k = None -> xex cc i r k = true.
Proof. intros cc i r k E O. apply exec_xex; auto. congruence. Qed.

Lemma cfail_cas : forall i r k, cfail i r k = true -> is_cas i = true.
Proof. intros [] r k H; simpl in H; try discriminate; reflexivity. Qed.

Lemma cfail_ncas : forall i r k, is_cas i = false -> cfail i r k = false.
Proof. intros [] r k H; simpl in H; try discriminate; reflexivity. Qed.

Lemma exec_xex_ncas : forall cc i r k, executes i r = true -> is_cas i = false -> xex cc i r k = true.
Proof. intros cc i r k E C. apply exec_xex; auto. intros _. apply cfail_ncas; auto. Qed.

Lemma xex_false : forall cc i r k, xex cc i r k = false ->
  executes i r = false \/ (oh cc k <> None /\ cfail i r k = true).
Proof.
  intros cc i r k H. unfold xex, xexec, ohb in H. destruct (executes i r); [right|left; reflexivity].
  destruct (oh cc k); simpl in H; [|discriminate]. destruct (cfail i r k); [|discriminate]. split; [discriminate|reflexivity].
Qed.

Lemma cfail_eval : forall i r r' j, ieval i r' = ieval i r -> r' j = r j -> cfail i r' j = cfail i r j.
Proof.
  intros [m x c|m x c v|m x c e n| |] r r' j E R; simpl in *; auto.
  injection E as E1 E2 E3. rewrite E1, E2, R. reflexivity.
Qed.

Lemma exec_eval : forall i r r', ieval i r' = ieval i r -> executes i r' = executes i r.
Proof. intros i r r' E. unfold executes, icond. rewrite E. reflexivity. Qed.

Lemma xex_eval : forall cc cc' i r r' j, oh cc' j = oh cc j -> ieval i r' = ieval i r -> r' j = r j ->
  xex cc' i r' j = xex cc i r j.
Proof.
  intros cc cc' i r r' j O E R. unfold xex, xexec, ohb. rewrite O, (exec_eval i r r' E), (cfail_eval i r r' j E R).
  reflexivity.
Qed.

(* the test depends on the state only through oh *)
Lemma xex_oh : forall cc cc' i r k, oh cc' k = oh cc k -> xex cc' i r k = xex cc i r k.
Proof. intros cc cc' i r k H. unfold xex, ohb. rewrite H. reflexivity. Qed.

(* when the slot's access happened: its event, or the read alone of a CAS
   that failed (its only event) *)
Definition tmo (cc : cst) (j : nat) : option nat :=
  match oc cc j with Some t => Some t | None => oh cc j end.

(* a CAS's read alone is tied as the CAS *)
Lemma tiedb_crd : forall a m xs c e n, tiedb a (ICas m xs c e n) = tiedb a (crd m xs).
Proof. intros a m xs c e n. destruct a as [| | | [] |]; reflexivity. Qed.

Lemma eofR_exec_tied_i : forall i r m xs, eofR i r = Some (m, xs) -> executes i r = true /\ is_cas i = true.
Proof.
  intros i r m xs H. destruct i as [| |m0 x0 c0 e0 n0| |]; simpl in H; try discriminate.
  unfold executes, icond; simpl. destruct (c0 r); [split; reflexivity|discriminate].
Qed.

Lemma tied_crd : forall a i r m xs, eofR i r = Some (m, xs) -> (tied a i <-> tied a (crd m xs)).
Proof.
  intros a i r m xs H. destruct i as [| |m0 x0 c0 e0 n0| |]; simpl in H; try discriminate.
  destruct (c0 r); [injection H as E1 E2; subst|discriminate].
  split; intros X; apply b_tied; apply tied_b in X; [rewrite <- (tiedb_crd a _ _ c0 e0 n0)|rewrite (tiedb_crd a _ _ c0 e0 n0)]; exact X.
Qed.

Lemma cfail_eq : forall i r k, is_cas i = true -> r k = vd true (eval_e i r) -> cfail i r k = false.
Proof.
  intros i r k C E. destruct i as [| |m0 x0 c0 e0 n0| |]; simpl in C; try discriminate. unfold cfail, cfailv.
  rewrite E, vok_vd, vv_vd. simpl. rewrite Nat.eqb_refl. apply andb_false_r.
Qed.

Lemma eval_e_ieval : forall i r r', ieval i r = ieval i r' -> eval_e i r = eval_e i r'.
Proof. intros [| |m0 x0 c0 e0 n0| |] r r' H; simpl in *; auto. injection H as _ E _. exact E. Qed.

Lemma eff_cas_ok_e : forall t i r m0 m' a K u, is_cas i = true -> eff t i r m0 m' a K u true -> a = vd true (eval_e i r).
Proof.
  intros t i r m0 m' a K u C H. inversion H; subst; simpl in C; try discriminate. simpl. f_equal. assumption.
Qed.

Lemma cfailv_eof : forall i r w d, eof i r = Some d -> cfailv i r w = cfailv (inst_of d) r w.
Proof.
  intros i r w d H. destruct i as [m0 x0 c0|m0 x0 c0 v0|m0 x0 c0 e0 n0|f0|]; simpl in H; try discriminate;
    try (destruct (c0 r) eqn:C; [injection H as <-|discriminate]); try (destruct f0; try discriminate; injection H as <-);
    simpl; rewrite ?C; reflexivity.
Qed.

Lemma cfailv_inst : forall d r r' v, cfailv (inst_of d) r v = cfailv (inst_of d) r' v.
Proof. intros d r r' w. destruct d; reflexivity. Qed.

Lemma cfail_eof : forall i r k d, eof i r = Some d -> cfail i r k = cfail (inst_of d) r k.
Proof.
  intros i r k d H. destruct i as [m0 x0 c0|m0 x0 c0 v0|m0 x0 c0 e0 n0|f0|]; simpl in H; try discriminate;
    try (destruct (c0 r) eqn:C; [injection H as <-|discriminate]); try (destruct f0; try discriminate; injection H as <-);
    simpl; rewrite ?C; reflexivity.
Qed.

(* ---------- the structural invariant ---------- *)
Record Inv1 (p : prog) (s : st) : Prop := {
  i_tm : tm s = length (lg s);
  i_et : forall t e, ent s t = Some e ->
           et e = t /\ (if eh e then oh (cs s (ec e)) (ek e) else oc (cs s (ec e)) (ek e)) = Some t;
  i_oc : forall c k t, oc (cs s c) k = Some t ->
           exists e, ent s t = Some e /\ ec e = c /\ ek e = k;
  i_oh : forall c k t, oh (cs s c) k = Some t ->
           exists e, ent s t = Some e /\ ec e = c /\ ek e = k /\ eh e = true;
  i_rg0 : forall c k, oc (cs s c) k = None -> oh (cs s c) k = None -> rg (cs s c) k = 0;
  (* the write a slot read or made is the one its entry records; a CAS's
     read alone: the writes it took *)
  i_rw : forall c k t, oc (cs s c) k = Some t \/ (oc (cs s c) k = None /\ oh (cs s c) k = Some t) ->
           exists e, ent s t = Some e /\ rw (cs s c) k = wrote t (icells (ai (cs s c) k)) (erf e) (ew e);
  (* a CAS whose read happened alone: not yet passed, recorded as a CAS's
     read; once its write happened, after its read, as a CAS *)
  i_half : forall c k t, oc (cs s c) k = None -> oh (cs s c) k = Some t -> pcs s c <= k ->
           pcs s c <= k /\ (exists xs, ai (cs s c) k = crd Plain xs) /\ c < length p;
  (* a CAS whose read happened alone and that was passed: it failed (its
     write half was nothing) *)
  i_halfp : forall c k t, oc (cs s c) k = None -> oh (cs s c) k = Some t -> k < pcs s c ->
           cfail (ai (cs s c) k) (rg (cs s c)) k = true /\ (exists xs, casx (ai (cs s c) k) = Some (Plain, xs)) /\
           c < length p;
  i_hoc : forall c k t1 t2, oh (cs s c) k = Some t1 -> oc (cs s c) k = Some t2 -> t1 < t2 /\ is_cas (ai (cs s c) k) = true;
  (* what an access did depends only on what happened before it *)
  i_det : forall t e, ent s t = Some e ->
           forall r, settled (cs s (ec e)) (pcs s (ec e)) r ->
           ieval (ai (cs s (ec e)) (ek e)) r = ieval (ai (cs s (ec e)) (ek e)) (rg (cs s (ec e)));
  (* a passed instruction that executes has happened *)
  i_pc : forall c j, j < pcs s c -> xex (cs s c) (ins p c j (rg (cs s c))) (rg (cs s c)) j = true -> oc (cs s c) j <> None;
  i_pend : forall c k, pcs s c <= k -> oc (cs s c) k <> None ->
           (exists d, ai (cs s c) k = inst_of d /\ d <> DFn FFull) /\ c < length p;
  (* a passed instruction tied to a pending access happened before it *)
  i_ptie : forall c k tk d j, pending (cs s c) (pcs s c) k d -> oc (cs s c) k = Some tk -> j < pcs s c ->
           xex (cs s c) (ins p c j (rg (cs s c))) (rg (cs s c)) j = true ->
           tied (ins p c j (rg (cs s c))) (inst_of d) ->
           exists tj, oc (cs s c) j = Some tj /\ tj < tk;
  (* of two passed instructions tied to each other, the earlier happened first *)
  i_po : forall c j k tk, j < k -> k < pcs s c -> oc (cs s c) k = Some tk ->
           xex (cs s c) (ins p c j (rg (cs s c))) (rg (cs s c)) j = true ->
           tied (ins p c j (rg (cs s c))) (ins p c k (rg (cs s c))) ->
           exists tj, oc (cs s c) j = Some tj /\ tj < tk;
  i_tp : forall c j, tp s c <= j -> oc (cs s c) j = None /\ oh (cs s c) j = None;
  i_cmA : forall c j, j < pcs s c <-> exists tau, In (c, j, tau) (cm s);
  i_cmB : forall n1 n2 c j1 j2 t1 t2, n1 < n2 -> nth_error (cm s) n1 = Some (c, j1, t1) ->
           nth_error (cm s) n2 = Some (c, j2, t2) -> j1 < j2;
  i_cmC : forall n1 n2 c1 c2 j1 j2 t1 t2, n1 < n2 -> nth_error (cm s) n1 = Some (c1, j1, t1) ->
           nth_error (cm s) n2 = Some (c2, j2, t2) -> t1 <= t2;
  i_cmD : forall c j tau, In (c, j, tau) (cm s) ->
           forall j', j' <= j -> xex (cs s c) (ins p c j' (rg (cs s c))) (rg (cs s c)) j' = true ->
           exists t', oc (cs s c) j' = Some t' /\ t' <= tau;
  i_cmE : forall c j tau, In (c, j, tau) (cm s) -> tau <= tm s;
  (* a passed slot: its instruction is fixed by what happened before it was
     passed, and what acted there is that instruction *)
  i_set : forall c j tau, In (c, j, tau) (cm s) ->
           (forall r, (forall j', j' < j \/ (exists t', oc (cs s c) j' = Some t' /\ t' < tau) -> r j' = rg (cs s c) j') ->
              ins p c j r = ins p c j (rg (cs s c)) /\
              ieval (ins p c j (rg (cs s c))) r = ieval (ins p c j (rg (cs s c))) (rg (cs s c))) /\
           ai (cs s c) j = ins p c j (rg (cs s c));
  (* a passed slot that is no access was passed when it happened *)
  i_cmF : forall c j tau, In (c, j, tau) (cm s) -> executes (ins p c j (rg (cs s c))) (rg (cs s c)) = true ->
           eof (ins p c j (rg (cs s c))) (rg (cs s c)) = None -> oc (cs s c) j = Some tau;
  (* the recorded slots reach past the next instruction *)
  i_pctp : forall c, pcs s c <= tp s c;
  (* the same, with the time of a slot (its event, or the read of a CAS that
     failed): a passed instruction tied to a pending access, or to a CAS whose
     read happened alone, happened before it; of two passed instructions tied
     to each other, the earlier happened first; a passed instruction that
     executes happened before it was passed *)
  i_ptiet : forall c k tk d j, pending (cs s c) (pcs s c) k d -> oc (cs s c) k = Some tk -> j < pcs s c ->
           executes (ins p c j (rg (cs s c))) (rg (cs s c)) = true ->
           tied (ins p c j (rg (cs s c))) (inst_of d) ->
           exists tj, tmo (cs s c) j = Some tj /\ tj < tk;
  i_ptieh : forall c k tk m xs j, hpending (cs s c) (pcs s c) k m xs -> oh (cs s c) k = Some tk -> j < pcs s c ->
           executes (ins p c j (rg (cs s c))) (rg (cs s c)) = true ->
           tied (ins p c j (rg (cs s c))) (crd m xs) ->
           exists tj, tmo (cs s c) j = Some tj /\ tj < tk;
  i_pot : forall c j k tk, j < k -> k < pcs s c -> tmo (cs s c) k = Some tk ->
           executes (ins p c j (rg (cs s c))) (rg (cs s c)) = true ->
           tied (ins p c j (rg (cs s c))) (ins p c k (rg (cs s c))) ->
           exists tj, tmo (cs s c) j = Some tj /\ tj < tk;
  i_cmDt : forall c j tau, In (c, j, tau) (cm s) ->
           forall j', j' <= j -> executes (ins p c j' (rg (cs s c))) (rg (cs s c)) = true ->
           exists t', tmo (cs s c) j' = Some t' /\ t' <= tau;
  (* a CAS whose read happened alone and whose write happened succeeded *)
  i_hocf : forall c k t1 t2, oh (cs s c) k = Some t1 -> oc (cs s c) k = Some t2 ->
           cfail (ai (cs s c) k) (rg (cs s c)) k = false;
  (* a passed CAS whose read happened alone committed to failure *)
  i_halfv : forall c k t, oc (cs s c) k = None -> oh (cs s c) k = Some t -> k < pcs s c ->
           vok (rg (cs s c) k) = false
}.

Lemma Inv1_init : forall p, Inv1 p sinit.
Proof.
  intros p. constructor; unfold ent, pending; simpl; intros.
  all: try (match goal with H : nth_error [] ?t = Some _ |- _ => destruct t; discriminate end).
  all: try discriminate.
  all: try (match goal with H : In _ [] |- _ => destruct H end).
  all: try lia.
  all: try tauto.
  all: try reflexivity.
  all: try (split; reflexivity).
  all: try (match goal with H : _ \/ _ |- _ => destruct H as [H|[_ H]]; discriminate end).
  all: split; [lia|intros (? & [])].
Qed.

Lemma oh_lt_tm : forall p s c k t, Inv1 p s -> oh (cs s c) k = Some t -> t < tm s.
Proof.
  intros p s c k t I H. destruct (i_oh p s I c k t H) as (e & He & _).
  rewrite (i_tm p s I). unfold ent in He. apply nth_error_Some. congruence.
Qed.

(* the entry of a slot that happened is no CAS's read alone *)
Lemma oc_eh : forall p s c k t e, Inv1 p s -> oc (cs s c) k = Some t -> ent s t = Some e -> ec e = c -> ek e = k ->
  eh e = false.
Proof.
  intros p s c k t e I O H E1 E2. destruct (eh e) eqn:Eh; auto. exfalso.
  destruct (i_et p s I t e H) as (_ & X). rewrite Eh, E1, E2 in X.
  destruct (i_hoc p s I c k t t X O) as (L & _). lia.
Qed.

Lemma oc_lt_tm : forall p s c k t, Inv1 p s -> oc (cs s c) k = Some t -> t < tm s.
Proof.
  intros p s c k t I H. destruct (i_oc p s I c k t H) as (e & He & _).
  rewrite (i_tm p s I). unfold ent in He. apply nth_error_Some. congruence.
Qed.

Lemma cm_set : forall p s c j, Inv1 p s -> j < pcs s c ->
  exists tau, In (c, j, tau) (cm s).
Proof. intros p s c j I H. apply (i_cmA p s I). auto. Qed.

(* the instruction at a passed slot is fixed: registers of later events do
   not change it *)
Lemma set_stable : forall p s c j r, Inv1 p s -> j < pcs s c ->
  settled (cs s c) (pcs s c) r ->
  ins p c j r = ins p c j (rg (cs s c)) /\
  ieval (ins p c j (rg (cs s c))) r = ieval (ins p c j (rg (cs s c))) (rg (cs s c)).
Proof.
  intros p s c j r I H Hr. destruct (cm_set p s c j I H) as (tau & T).
  apply (proj1 (i_set p s I c j tau T)). intros j' [L|(t' & X & _)]; apply Hr; [left; lia|right; congruence].
Qed.

(* a passed CAS's comparison does not change under settled registers *)
Lemma cfail_passed : forall p s c j r, Inv1 p s -> j < pcs s c -> settled (cs s c) (pcs s c) r ->
  cfail (ai (cs s c) j) r j = cfail (ai (cs s c) j) (rg (cs s c)) j.
Proof.
  intros p s c j r I L Hr. destruct (cm_set p s c j I L) as (tau & T). rewrite (proj2 (i_set p s I c j tau T)).
  destruct (set_stable p s c j r I L Hr) as [_ E2]. apply cfail_eval; [exact E2|]. apply Hr. left. exact L.
Qed.

(* a CAS whose read happened alone and that has not written reads: as a CAS's
   read, or as the CAS it was passed as *)
Lemma half_xload : forall p s c k t, Inv1 p s -> oc (cs s c) k = None -> oh (cs s c) k = Some t ->
  xload (ai (cs s c) k) (rg (cs s c)) = true /\ is_cas (ai (cs s c) k) = true.
Proof.
  intros p s c k t I O Oh. destruct (Nat.le_gt_cases (pcs s c) k) as [L|L].
  - destruct (i_half p s I c k t O Oh L) as (_ & (xs & A) & _). rewrite A. split; reflexivity.
  - destruct (i_halfp p s I c k t O Oh L) as (F & _). revert F. generalize (ai (cs s c) k). intros i F.
    destruct i as [| |m0 x0 c0 e0 n0| |]; simpl in F; try discriminate. apply andb_true_iff in F as [F _].
    unfold xload, icond; simpl. rewrite F. split; reflexivity.
Qed.

(* a passed slot that does not execute in the widened sense but executes:
   a CAS whose read happened alone and whose comparison fails *)
Lemma passed_fail : forall p s c j, Inv1 p s -> j < pcs s c ->
  executes (ins p c j (rg (cs s c))) (rg (cs s c)) = true -> oc (cs s c) j = None ->
  exists t, oh (cs s c) j = Some t /\ cfail (ins p c j (rg (cs s c))) (rg (cs s c)) j = true /\
    ai (cs s c) j = ins p c j (rg (cs s c)).
Proof.
  intros p s c j I L E O. destruct (xex (cs s c) (ins p c j (rg (cs s c))) (rg (cs s c)) j) eqn:X.
  - exfalso. apply (i_pc p s I c j L X O).
  - destruct (xex_false _ _ _ _ X) as [N|(Oh & F)]; [congruence|].
    destruct (oh (cs s c) j) as [t|] eqn:Ot; [|congruence]. exists t. split; [reflexivity|]. split; [exact F|].
    destruct (cm_set p s c j I L) as (tau & T). apply (proj2 (i_set p s I c j tau T)).
Qed.

(* a passed instruction that executes happened (or, a CAS that failed, its
   read did) *)
Lemma tmo_passed : forall p s c j, Inv1 p s -> j < pcs s c ->
  executes (ins p c j (rg (cs s c))) (rg (cs s c)) = true -> exists t, tmo (cs s c) j = Some t /\ t < tm s.
Proof.
  intros p s c j I L E. unfold tmo. destruct (oc (cs s c) j) as [t|] eqn:O.
  - exists t. split; [reflexivity|apply (oc_lt_tm p s c j t I O)].
  - destruct (passed_fail p s c j I L E O) as (t & Oh & _). exists t. rewrite Oh. split; [reflexivity|].
    apply (oh_lt_tm p s c j t I Oh).
Qed.

Lemma tmo_ent_s : forall p s c j t, Inv1 p s -> tmo (cs s c) j = Some t -> exists e, ent s t = Some e /\ ec e = c /\ ek e = j.
Proof.
  intros p s c j t I H. unfold tmo in H. destruct (oc (cs s c) j) as [t'|] eqn:O.
  - injection H as <-. apply (i_oc p s I c j t' O).
  - destruct (i_oh p s I c j t H) as (e & A & B & C & _). eauto.
Qed.

(* the comparison at a slot that happened, under registers that keep the
   passed and happened slots *)
Lemma cfail_keep : forall p s c j r, Inv1 p s -> oc (cs s c) j <> None -> settled (cs s c) (pcs s c) r ->
  cfail (ai (cs s c) j) r j = cfail (ai (cs s c) j) (rg (cs s c)) j.
Proof.
  intros p s c j r I O Hr. destruct (Nat.lt_ge_cases j (pcs s c)) as [L|L].
  - apply (cfail_passed p s c j r I L Hr).
  - destruct (proj1 (i_pend p s I c j L O)) as (d & A & _). rewrite A.
    destruct d; simpl; try reflexivity. rewrite (Hr j (or_intror O)). reflexivity.
Qed.

(* ---------- the three steps, named ---------- *)
(* the log entry of an access at slot k *)
Abbreviation newev s c k i K u w :=
  (mkO (tm s) c k K u w (evC i (rg (cs s c))) (evR i (rg (cs s c)))
       (evQ s c i (rg (cs s c)) (mof s c) (vOg (cs s c)) (vO (cs s c)) u w) (evQc i (rg (cs s c)) (vO (cs s c)) w) false).
Abbreviation newevh s c k i K u w :=
  (mkO (tm s) c k K u w (evC i (rg (cs s c))) (evR i (rg (cs s c)))
       (evQ s c i (rg (cs s c)) (mof s c) (vOg (cs s c)) (vO (cs s c)) u w) (evQc i (rg (cs s c)) (vO (cs s c)) w) true).

Definition evs (s : st) (c k : nat) (i : instr) (m' : mst) (a : val) (K : view) (u : cell -> option nat)
    (w : bool) (B : nat -> bool) (pc' tp' : nat -> nat) (cm' : list (nat * nat * nat)) : st :=
  let cc := cs s c in
  mkS (S (tm s))
      (upd (cs s) c (mkC (upd (oc cc) k (Some (tm s))) (upd (rg cc) k a) (upd (ai cc) k i)
                         (upd (rw cc) k (wrote (tm s) (icells i) u w)) (upd (rv cc) k (rdval (mof s c) u)) B
                         (mP m') (mA m') (mR m')
                         (newO s c i (mof s c) m' (vO cc)) (newOg i m' (vOg cc)) (oh cc) (fx cc)))
      (mV m') (mC m') (mH m') (mG m') pc' tp' cm'
      (lg s ++ [newev s c k i K u w]) (es s).

Definition sord (s : st) (c : nat) (i : instr) (m' : mst) (a : val) (K : view) (u : cell -> option nat)
    (w : bool) : st :=
  let k := pcs s c in
  evs s c k i m' a K u w (bd (cs s c)) (upd (pcs s) c (S k)) (upd (tp s) c (Nat.max (tp s c) (S k)))
      (cm s ++ [(c, k, tm s)]).

Definition set_es (t : st) (e : nat -> option (cst * nat * nat * (nat -> bool))) : st :=
  mkS (tm t) (cs t) (wv t) (wc t) (hs t) (vG t) (pcs t) (tp t) (cm t) (lg t) e.

Definition searly0 (s : st) (c k : nat) (d : desc) (B : nat -> bool) (m' : mst) (a : val) (K : view)
    (u : cell -> option nat) (w : bool) : st :=
  evs s c k (inst_of d) m' a K u w (bor (bd (cs s c)) B) (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k)))
      (cm s).

Definition searly (s : st) (c k : nat) (d : desc) (B : nat -> bool) (m' : mst) (a : val) (K : view)
    (u : cell -> option nat) (w : bool) : st :=
  set_es (searly0 s c k d B m' a K u w) (upd (es s) (tm s) (Some (cs s c, pcs s c, tp s c, B))).

Definition smatch (p : prog) (s : st) (c : nat) : st :=
  let cc := cs s c in let k := pcs s c in
  mkS (tm s)
      (upd (cs s) c (mkC (oc cc) (rg cc) (upd (ai cc) k (ins p c k (rg cc))) (rw cc) (rv cc) (bd cc)
                         (vP cc) (vA cc) (vR cc) (vO cc) (vOg cc) (oh cc) (fx cc)))
      (wv s) (wc s) (hs s) (vG s)
      (upd (pcs s) c (S k)) (tp s) (cm s ++ [(c, k, tm s)]) (lg s) (es s).

(* passing a non-executing instruction: nothing logged, no time *)
Definition sskip (p : prog) (s : st) (c : nat) : st :=
  let cc := cs s c in let k := pcs s c in
  mkS (tm s)
      (upd (cs s) c (mkC (oc cc) (rg cc) (upd (ai cc) k (ins p c k (rg cc))) (rw cc) (rv cc) (bd cc)
                         (vP cc) (vA cc) (vR cc) (vO cc) (vOg cc) (oh cc) (fx cc)))
      (wv s) (wc s) (hs s) (vG s)
      (upd (pcs s) c (S k)) (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s ++ [(c, k, tm s)]) (lg s) (es s).

(* a CAS's read alone at slot k *)
Definition sread (s : st) (c k : nat) (m : mode) (xs : list cell) (B : nat -> bool) (m' : mst) (a : val)
    (K : view) (u : cell -> option nat) (w : bool) (bv : bool) : st :=
  let cc := cs s c in let i := ILd m xs (fun _ => true) in
  mkS (S (tm s))
      (upd (cs s) c (mkC (oc cc) (upd (rg cc) k (vd bv a)) (upd (ai cc) k (crd m xs))
                         (upd (rw cc) k (wrote (tm s) (icells i) u w)) (upd (rv cc) k (rdval (mof s c) u))
                         (bor (bd cc) B) (mP m') (mA m') (mR m')
                         (newO s c i (mof s c) m' (vO cc)) (newOg i m' (vOg cc))
                         (upd (oh cc) k (Some (tm s))) (fx cc)))
      (mV m') (mC m') (mH m') (mG m')
      (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s)
      (lg s ++ [newevh s c k i K u w])
      (upd (es s) (tm s) (Some (cc, pcs s c, tp s c, B))).

Lemma step_cases : forall p s t, step p s t ->
  (exists c i m' a K u w, let cc := cs s c in let k := pcs s c in
     ins p c k (rg cc) = i /\ oc cc k = None /\ determined p cc c k i /\
     (executes i (rg cc) = true -> forall k' d, pending cc k k' d -> ~ tied i (inst_of d)) /\
     (executes i (rg cc) = true -> forall k' m xs, hpending cc k k' m xs -> k' <> k -> ~ tied i (crd m xs)) /\
     ((oh cc k = None /\
       forall x b, bd cc k = true -> In x (icells i) -> fbinder p c (rg cc) k x = Some b -> u x = rw cc b x) \/
      (exists t1, oh cc k = Some t1 /\ is_cas i = true /\ u = rw cc k /\ eofR i (rg cc) = eofR (ai cc k) (rg cc))) /\
     (oh cc k <> None -> w = true) /\ (oh cc k <> None -> vok (rg cc k) = true) /\
     eff (tm s) i (rg cc) (mof s c) m' a K u w /\ fxok cc k i (rg cc) a /\ t = sord s c i m' a K u w) \/
  (exists c k d B m' a K u w, let cc := cs s c in
     pcs s c < k /\ oc cc k = None /\
     (forall k' d', pending cc (pcs s c) k' d' -> tied (inst_of d) (inst_of d') -> k' < k) /\
     ((oh cc k = None /\ early_ok p c cc (pcs s c) (tp s c) (tm s) d u B) \/
      (exists t1 xs ev nv, oh cc k = Some t1 /\ d = DCas Plain xs ev nv /\ u = rw cc k /\
         ai cc k = crd Plain xs /\ early_okW p c cc (pcs s c) (tp s c) (tm s) t1 Plain xs d B)) /\
     (oh cc k <> None -> w = true) /\ (oh cc k <> None -> vok (rg cc k) = true) /\
     eff (tm s) (inst_of d) (rg cc) (mof s c) m' a K u w /\
     ((oh cc k = None -> forall f j, first_at p c cc (pcs s c) (creg p c cc (pcs s c) (tp s c) (bor (bd cc) B) f) (tm s) d j ->
         fxok cc j (inst_of d) (rg cc) a) /\
      (forall t1 xs ev nv f j, oh cc k = Some t1 -> d = DCas Plain xs ev nv ->
         first_atR p c cc (pcs s c) (creg p c cc (pcs s c) (tp s c) (bor (bd cc) B) f) t1 Plain xs j ->
         fxok cc j (inst_of d) (rg cc) a)) /\ t = searly s c k d B m' a K u w) \/
  (exists c d, let cc := cs s c in let k := pcs s c in
     oc cc k <> None /\ ai cc k = inst_of d /\ eof (ins p c k (rg cc)) (rg cc) = Some d /\
     determined p cc c k (ins p c k (rg cc)) /\
     (forall k' d' t t', pending cc k k' d' -> k' <> k -> oc cc k = Some t -> oc cc k' = Some t' ->
        tied (inst_of d) (inst_of d') -> t < t') /\
     (forall k' m xs t t', hpending cc k k' m xs -> k' <> k -> oc cc k = Some t -> oh cc k' = Some t' ->
        tied (inst_of d) (crd m xs) -> t < t') /\ t = smatch p s c) \/
  (exists c k xs B m' a K u w bv, let cc := cs s c in
     pcs s c <= k /\ oc cc k = None /\ oh cc k = None /\
     (forall k' d', pending cc (pcs s c) k' d' -> tied (crd Plain xs) (inst_of d') -> k' < k) /\
     early_okR p c cc (pcs s c) (tp s c) (tm s) Plain xs u B /\
     eff (tm s) (ILd Plain xs (fun _ => true)) (rg cc) (mof s c) m' a K u w /\
     (forall f j, first_atR p c cc (pcs s c) (creg p c cc (pcs s c) (tp s c) (bor (bd cc) B) f) (tm s) Plain xs j ->
        match fx cc j with Some b => b = bv | None => bv = true end /\
        fxok cc j (ins p c j (creg p c cc (pcs s c) (tp s c) (bor (bd cc) B) f))
          (creg p c cc (pcs s c) (tp s c) (bor (bd cc) B) f) (vd bv a)) /\
     t = sread s c k Plain xs B m' a K u w bv) \/
  (exists c, let cc := cs s c in let k := pcs s c in
     xex cc (ins p c k (rg cc)) (rg cc) k = false /\ oc cc k = None /\
     (oh cc k <> None -> eofR (ins p c k (rg cc)) (rg cc) = eofR (ai cc k) (rg cc)) /\
     (oh cc k <> None -> vok (rg cc k) = false) /\
     hfirst cc k (ins p c k (rg cc)) /\
     determined p cc c k (ins p c k (rg cc)) /\ fxok cc k (ins p c k (rg cc)) (rg cc) (rg cc k) /\ t = sskip p s c) \/
  (exists c j b B o, let cc := cs s c in
     pcs s c <= j /\ fx cc j = None /\ cfix_ok p c cc (pcs s c) (tp s c) j b B o /\ t = scfix0 (sflp s c o b) c j b B).
Proof.
  intros p s t H. inversion H; subst; repeat match goal with x := _ |- _ => subst x end.
  - left. do 7 eexists. cbv zeta. repeat (split; [first [eassumption|reflexivity]|]).
    split; [intros X k' m xs P' _; match goal with H : executes _ _ = true -> forall k'' m' xs', hpending _ _ k'' m' xs' -> ~ _ |- _ => exact (H X k' m xs P') end|].
    split; [left; split; eassumption|]. split; [intros N; exfalso; apply N; assumption|]. split; [intros N; exfalso; apply N; assumption|]. split; [eassumption|split; [eassumption|reflexivity]].
  - right; right; right; right; left. eexists. cbv zeta. repeat (split; [first [eassumption|reflexivity]|]). reflexivity.
  - right; left. do 9 eexists. cbv zeta. repeat (split; [first [eassumption|reflexivity]|]).
    split; [left; split; eassumption|]. split; [intros N; exfalso; apply N; assumption|]. split; [intros N; exfalso; apply N; assumption|].
    split; [eassumption|split; [split; [intros _; eassumption|intros t1' xs' ev' nv' f j O; congruence]|reflexivity]].
  - right; right; left. do 2 eexists. cbv zeta. repeat (split; [first [eassumption|reflexivity]|]). reflexivity.
  - right; right; right; left. repeat match goal with m : mode |- _ => destruct m end.
    do 10 eexists. cbv zeta. repeat (split; [first [eassumption|reflexivity]|]). reflexivity.
  - left. do 7 eexists. cbv zeta. repeat (split; [first [eassumption|reflexivity]|]).
    split; [intros _ k' d' P' T'; match goal with H : forall k'' d'', pending _ _ k'' d'' -> ~ _ |- _ => exact (H k' d' P' T') end|].
    split; [intros _ k' m xs P' N'; match goal with H : forall k'' m' xs', hpending _ _ k'' m' xs' -> _ <> _ -> ~ _ |- _ => exact (H k' m xs P' N') end|].
    split; [right; eexists; split; [eassumption|split; [assumption|split; [reflexivity|assumption]]]|].
    split; [intros _; first [assumption|reflexivity]|]. split; [intros _; assumption|]. split; [eassumption|split; [eassumption|reflexivity]].
  - right; left. do 9 eexists. cbv zeta. repeat (split; [first [eassumption|reflexivity]|]).
    split; [right; do 4 eexists; split; [eassumption|split; [reflexivity|split; [reflexivity|split; [eassumption|eassumption]]]]|].
    split; [intros _; first [assumption|reflexivity]|]. split; [intros _; assumption|].
    split; [eassumption|split; [split; [intros O; congruence|]|reflexivity]].
    intros t1' xs' ev' nv' f j O E F. injection E as -> -> ->.
    match goal with Hh : oh _ _ = Some ?t0 |- _ => tryif constr_eq t0 t1' then fail else assert (t1' = t0) by congruence end.
    subst. eauto.
  - right; right; right; right; right. do 5 eexists. cbv zeta. repeat (split; [eassumption|]). reflexivity.
Qed.

(* S3c: the record a fix names is a CAS's read alone, not yet reached, not failed *)
Lemma cfix_rec : forall p c cc pc N j b B k, cfix_ok p c cc pc N j b B (Some k) ->
  pc <= k /\ oc cc k = None /\ oh cc k <> None /\ vok (rg cc k) = true.
Proof.
  intros p c cc pc N j b B k (v & H). destruct (H (fun _ _ => 0)) as (_ & _ & _ & Hp & Vk & _). cbv zeta in Hp.
  split; [|split; [|split]]; [| | |exact (Vk k eq_refl)].
  all: unfold hpend_at in Hp; apply find_some in Hp as (Ik & Hk); apply in_seq in Ik.
  - lia.
  - destruct (oc cc k); [discriminate|reflexivity].
  - destruct (oc cc k); [discriminate|]. destruct (oh cc k); discriminate.
Qed.

(* ---------- facts on an event step ---------- *)
Section Ev.
Variables (p : prog) (s : st) (c k : nat) (i : instr) (m' : mst) (a : val) (K : view)
          (u : cell -> option nat) (w : bool) (B : nat -> bool) (pc' tp' : nat -> nat)
          (cm' : list (nat * nat * nat)).
Hypothesis I : Inv1 p s.
Hypothesis Ho : oc (cs s c) k = None.
Local Abbreviation s' := (evs s c k i m' a K u w B pc' tp' cm').

Lemma ent_s' : forall t, ent s' t =
  if Nat.ltb t (tm s) then ent s t else if Nat.eqb t (tm s) then Some (newev s c k i K u w) else None.
Proof. intros t. unfold ent, evs. simpl. rewrite nth_error_app_last, (i_tm p s I). reflexivity. Qed.

Lemma oc_s' : forall c' j, oc (cs s' c') j =
  if Nat.eqb c' c then (if Nat.eqb j k then Some (tm s) else oc (cs s c) j) else oc (cs s c') j.
Proof.
  intros c' j. unfold evs; simpl. unfold upd at 1. destruct (Nat.eqb c' c) eqn:E; simpl; auto.
Qed.

Lemma rg_s' : forall c' j, rg (cs s' c') j =
  if Nat.eqb c' c then (if Nat.eqb j k then a else rg (cs s c) j) else rg (cs s c') j.
Proof.
  intros c' j. unfold evs; simpl. unfold upd at 1. destruct (Nat.eqb c' c) eqn:E; simpl; auto.
Qed.

Lemma ai_s' : forall c' j, ai (cs s' c') j =
  if Nat.eqb c' c then (if Nat.eqb j k then i else ai (cs s c) j) else ai (cs s c') j.
Proof.
  intros c' j. unfold evs; simpl. unfold upd at 1. destruct (Nat.eqb c' c) eqn:E; simpl; auto.
Qed.

Lemma rw_s' : forall c' j, rw (cs s' c') j =
  if Nat.eqb c' c then (if Nat.eqb j k then wrote (tm s) (icells i) u w else rw (cs s c) j) else rw (cs s c') j.
Proof.
  intros c' j. unfold evs; simpl. unfold upd at 1. destruct (Nat.eqb c' c) eqn:E; simpl; auto.
Qed.

Lemma rv_s' : forall c' j, rv (cs s' c') j =
  if Nat.eqb c' c then (if Nat.eqb j k then rdval (mof s c) u else rv (cs s c) j) else rv (cs s c') j.
Proof.
  intros c' j. unfold evs; simpl. unfold upd at 1. destruct (Nat.eqb c' c) eqn:E; simpl; auto.
Qed.

Lemma oh_s' : forall c', oh (cs s' c') = oh (cs s c').
Proof. intros c'. unfold evs; simpl. unfold upd at 1. destruct (Nat.eqb c' c) eqn:E; simpl; auto. apply Nat.eqb_eq in E. subst. reflexivity. Qed.

Lemma cs_other : forall c', c' <> c -> cs s' c' = cs s c'.
Proof. intros c' N. unfold evs; simpl. apply upd_neq. auto. Qed.

(* a register of something that had happened keeps its value *)
Lemma rg_old_s' : forall c' j, oc (cs s c') j <> None -> rg (cs s' c') j = rg (cs s c') j.
Proof.
  intros c' j X. rewrite rg_s'. destruct (Nat.eqb_spec c' c); auto. subst.
  destruct (Nat.eqb_spec j k); auto. subst. congruence.
Qed.

Lemma ai_old_s' : forall c' j, oc (cs s c') j <> None -> ai (cs s' c') j = ai (cs s c') j.
Proof.
  intros c' j X. rewrite ai_s'. destruct (Nat.eqb_spec c' c); auto. subst.
  destruct (Nat.eqb_spec j k); auto. subst. congruence.
Qed.

Lemma oc_old_s' : forall c' j t, oc (cs s c') j = Some t -> oc (cs s' c') j = Some t.
Proof.
  intros c' j t X. rewrite oc_s'. destruct (Nat.eqb_spec c' c); auto. subst.
  destruct (Nat.eqb_spec j k); auto. subst. congruence.
Qed.

(* a register below the next instruction keeps its value: the event's slot
   is not below it *)
Lemma settled_s' : pcs s c <= k -> forall c', settled (cs s c') (pcs s c') (rg (cs s' c')).
Proof.
  intros Hk c' j [L|X]; [|apply rg_old_s'; exact X].
  rewrite rg_s'. destruct (Nat.eqb_spec c' c); auto. subst. destruct (Nat.eqb_spec j k); auto. lia.
Qed.

(* the instruction at a passed slot, under the new registers *)
Lemma ins_set_s' : pcs s c <= k -> forall c' j, j < pcs s c' ->
  ins p c' j (rg (cs s' c')) = ins p c' j (rg (cs s c')) /\
  ieval (ins p c' j (rg (cs s c'))) (rg (cs s' c')) = ieval (ins p c' j (rg (cs s c'))) (rg (cs s c')).
Proof. intros Hk c' j H. apply (set_stable p s c' j); auto. apply settled_s'. exact Hk. Qed.

Lemma executes_set_s' : pcs s c <= k -> forall c' j, j < pcs s c' ->
  executes (ins p c' j (rg (cs s' c'))) (rg (cs s' c')) = executes (ins p c' j (rg (cs s c'))) (rg (cs s c')).
Proof.
  intros Hk c' j H. destruct (ins_set_s' Hk c' j H) as [E1 E2]. rewrite E1. unfold executes, icond. rewrite E2. reflexivity.
Qed.

Lemma xex_set_s' : pcs s c <= k -> forall c' j, j < pcs s c' ->
  xex (cs s' c') (ins p c' j (rg (cs s' c'))) (rg (cs s' c')) j = xex (cs s c') (ins p c' j (rg (cs s c'))) (rg (cs s c')) j.
Proof.
  intros Hk c' j H. destruct (ins_set_s' Hk c' j H) as [E1 E2]. rewrite E1.
  apply xex_eval; [rewrite oh_s'; reflexivity|exact E2|]. apply (settled_s' Hk c'). left. exact H.
Qed.

Lemma cfail_set_s' : pcs s c <= k -> forall c' j, j < pcs s c' ->
  cfail (ai (cs s c') j) (rg (cs s' c')) j = cfail (ai (cs s c') j) (rg (cs s c')) j.
Proof.
  intros Hk c' j H. destruct (cm_set p s c' j I H) as (tau & T). rewrite (proj2 (i_set p s I c' j tau T)).
  destruct (ins_set_s' Hk c' j H) as [_ E2].
  apply cfail_eval; [exact E2|]. apply (settled_s' Hk c'). left. exact H.
Qed.

Lemma dof_set_s' : pcs s c <= k -> forall c' j, j < pcs s c' ->
  dof (ins p c' j (rg (cs s' c'))) (rg (cs s' c')) = dof (ins p c' j (rg (cs s c'))) (rg (cs s c')).
Proof.
  intros Hk c' j H. destruct (ins_set_s' Hk c' j H) as [E1 E2]. rewrite E1.
  destruct (ins p c' j (rg (cs s c'))); simpl in *; auto; injection E2; intros; subst;
  repeat match goal with Hx : _ = _ |- _ => rewrite Hx end; reflexivity.
Qed.

Lemma eof_set_s' : pcs s c <= k -> forall c' j, j < pcs s c' ->
  eof (ins p c' j (rg (cs s' c'))) (rg (cs s' c')) = eof (ins p c' j (rg (cs s c'))) (rg (cs s c')).
Proof.
  intros Hk c' j H. destruct (ins_set_s' Hk c' j H) as [E1 E2]. rewrite E1.
  destruct (ins p c' j (rg (cs s c'))) as [| | |[]|]; simpl in *; auto; injection E2; intros; subst;
  repeat match goal with Hx : _ = _ |- _ => rewrite Hx end; reflexivity.
Qed.

Lemma pend_old : forall c' j, pcs s c' <= j -> oc (cs s c') j <> None -> j <> k \/ c' <> c.
Proof. intros c' j _ X. destruct (Nat.eq_dec c' c); [left; subst; congruence|auto]. Qed.

End Ev.

Lemma tm_pos_of_oc : forall p s c k t, Inv1 p s -> oc (cs s c) k = Some t -> 0 < tm s.
Proof. intros p s c k t I H. pose proof (oc_lt_tm p s c k t I H). lia. Qed.

Ltac oc_t p s I :=
  repeat match goal with
  | H : oc (cs s ?c) ?j = Some ?t |- _ =>
      match goal with _ : t < tm s |- _ => fail 1 | _ => pose proof (oc_lt_tm p s c j t I H) end
  end.

(* ---------- R1 in programme order ---------- *)
Section Ord.
Variables (p : prog) (s : st) (c : nat) (i : instr) (m' : mst) (a : val) (K : view)
          (u : cell -> option nat) (w : bool).
Hypothesis I : Inv1 p s.
Local Abbreviation cc := (cs s c).
Local Abbreviation k := (pcs s c).
Hypothesis Hi : ins p c k (rg cc) = i.
Hypothesis Ho : oc cc k = None.
Hypothesis Hd : determined p cc c k i.
Hypothesis Hb : executes i (rg cc) = true -> forall k' d, pending cc k k' d -> ~ tied i (inst_of d).
Hypothesis Hbh : executes i (rg cc) = true -> forall k' m xs, hpending cc k k' m xs -> k' <> k -> ~ tied i (crd m xs).
Hypothesis He : eff (tm s) i (rg cc) (mof s c) m' a K u w.
Hypothesis Hoh : oh cc k = None \/ (exists t1, oh cc k = Some t1 /\ is_cas i = true).
Hypothesis Hw : oh cc k <> None -> w = true.
Local Abbreviation s' := (sord s c i m' a K u w).

Lemma ord_settled : forall r, (forall j, j < k \/ (exists t', oc (cs s' c) j = Some t' /\ t' < tm s) -> r j = rg (cs s' c) j) ->
  settled cc k r.
Proof.
  intros r H j [Lj|Hj].
  { rewrite (H j (or_introl Lj)). unfold sord. rewrite rg_s', Nat.eqb_refl. destruct (Nat.eqb_spec j k); [lia|reflexivity]. }
  destruct (oc cc j) as [t|] eqn:E; [|congruence].
  assert (j <> k) by congruence. unfold sord in *.
  rewrite <- (rg_old_s' s c k i m' a K u w (bd cc) (upd (pcs s) c (S k)) (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s ++ [(c, k, tm s)]) Ho c j) by congruence.
  apply H. right. exists t. split; [apply oc_old_s'; auto|]. apply (oc_lt_tm p s c j t I E).
Qed.

Lemma ord_settled_new : settled cc k (rg (cs s' c)).
Proof. unfold sord. eapply settled_s'; eauto. Qed.

Lemma ord_ins_new : ins p c k (rg (cs s' c)) = i /\ ieval i (rg (cs s' c)) = ieval i (rg cc).
Proof. apply Hd. apply ord_settled_new. Qed.

Lemma pcs_ord : forall c', pcs s' c' = if Nat.eqb c' c then S k else pcs s c'.
Proof. intros c'. reflexivity. Qed.

Lemma Inv1_ord : Inv1 p s'.
Proof.
  pose proof (ent_s' p s c k i m' a K u w (bd cc) (upd (pcs s) c (S k)) (upd (tp s) c (Nat.max (tp s c) (S k)))
    (cm s ++ [(c, k, tm s)]) I) as ENT.
  pose proof (oc_s' s c k i m' a K u w (bd cc) (upd (pcs s) c (S k)) (upd (tp s) c (Nat.max (tp s c) (S k)))
    (cm s ++ [(c, k, tm s)])) as OC.
  pose proof (ai_s' s c k i m' a K u w (bd cc) (upd (pcs s) c (S k)) (upd (tp s) c (Nat.max (tp s c) (S k)))
    (cm s ++ [(c, k, tm s)])) as AI.
  pose proof (rg_s' s c k i m' a K u w (bd cc) (upd (pcs s) c (S k)) (upd (tp s) c (Nat.max (tp s c) (S k)))
    (cm s ++ [(c, k, tm s)])) as RG.
  pose proof (rw_s' s c k i m' a K u w (bd cc) (upd (pcs s) c (S k)) (upd (tp s) c (Nat.max (tp s c) (S k)))
    (cm s ++ [(c, k, tm s)])) as RW.
  pose proof (oh_s' s c k i m' a K u w (bd cc) (upd (pcs s) c (S k)) (upd (tp s) c (Nat.max (tp s c) (S k)))
    (cm s ++ [(c, k, tm s)])) as OH.
  fold s' in ENT, OC, AI, RG, RW, OH.
  assert (ROLD : forall c' j, oc (cs s c') j <> None -> rg (cs s' c') j = rg (cs s c') j).
  { intros. unfold sord. apply rg_old_s'; auto. }
  assert (AOLD : forall c' j, oc (cs s c') j <> None -> ai (cs s' c') j = ai (cs s c') j).
  { intros. unfold sord. apply ai_old_s'; auto. }
  assert (OOLD : forall c' j t, oc (cs s c') j = Some t -> oc (cs s' c') j = Some t).
  { intros. unfold sord. apply oc_old_s'; auto. }
  assert (SET : forall c' j, j < pcs s c' ->
    ins p c' j (rg (cs s' c')) = ins p c' j (rg (cs s c')) /\
    ieval (ins p c' j (rg (cs s c'))) (rg (cs s' c')) = ieval (ins p c' j (rg (cs s c'))) (rg (cs s c'))).
  { intros. unfold sord. apply ins_set_s'; auto; lia. }
  assert (EXS : forall c' j, j < pcs s c' ->
    executes (ins p c' j (rg (cs s' c'))) (rg (cs s' c')) = executes (ins p c' j (rg (cs s c'))) (rg (cs s c'))).
  { intros. unfold sord. apply executes_set_s'; auto; lia. }
  assert (XXS : forall c' j, j < pcs s c' ->
    xex (cs s' c') (ins p c' j (rg (cs s' c'))) (rg (cs s' c')) j = xex (cs s c') (ins p c' j (rg (cs s c'))) (rg (cs s c')) j).
  { intros. unfold sord. apply xex_set_s'; auto; lia. }
  assert (CSO : forall c', c' <> c -> cs s' c' = cs s c').
  { intros. unfold sord. apply cs_other; auto. }
  (* registers of passed or happened slots keep their values *)
  assert (RS : forall c' j, j < pcs s c' \/ oc (cs s c') j <> None -> rg (cs s' c') j = rg (cs s c') j).
  { intros c' j X. rewrite RG. destruct (Nat.eqb_spec c' c); auto. subst. destruct (Nat.eqb_spec j k); auto.
    subst. destruct X; [lia|congruence]. }
  assert (AIP : forall c' j, j < pcs s c' -> ai (cs s' c') j = ai (cs s c') j).
  { intros c' j L. rewrite AI. destruct (Nat.eqb_spec c' c); auto. subst. destruct (Nat.eqb_spec j k); auto. lia. }
  assert (STL : forall c' r, settled (cs s' c') (pcs s' c') r -> settled (cs s c') (pcs s c') r).
  { intros c' r Hr j X. rewrite <- (RS c' j X). apply Hr. rewrite pcs_ord, OC.
    destruct (Nat.eqb_spec c' c); [subst|]; [destruct (Nat.eqb_spec j k)|]; destruct X as [X|X]; auto; try (left; lia);
    right; discriminate. }
  destruct ord_ins_new as [IN IE].
  assert (TMO : forall c' j, (c' <> c \/ j <> k) -> tmo (cs s' c') j = tmo (cs s c') j).
  { intros c' j Nj. unfold tmo. rewrite OC, OH. destruct (Nat.eqb_spec c' c); [subst; destruct (Nat.eqb_spec j k)|];
      [destruct Nj; congruence|reflexivity|reflexivity]. }
  constructor.
  - unfold sord, evs; simpl. rewrite length_app, (i_tm p s I). simpl. lia.
  - intros t e H. rewrite ENT in H. destruct (Nat.ltb_spec t (tm s)).
    + destruct (i_et p s I t e H) as (E1 & E2). split; auto. destruct (eh e).
      * rewrite OH. exact E2.
      * apply OOLD. exact E2.
    + destruct (Nat.eqb_spec t (tm s)); [|discriminate]. injection H as <-. subst. cbn [et ec ek eh].
      rewrite OC, !Nat.eqb_refl. split; auto.
  - intros c' j t H. rewrite OC in H. rewrite ENT.
    destruct (Nat.eqb_spec c' c).
    + subst. destruct (Nat.eqb_spec j k).
      * injection H as <-. subst. rewrite Nat.ltb_irrefl, Nat.eqb_refl. eauto.
      * pose proof (oc_lt_tm p s c j t I H). apply Nat.ltb_lt in H0. rewrite H0. apply (i_oc p s I _ _ _ H).
    + pose proof (oc_lt_tm p s c' j t I H). apply Nat.ltb_lt in H0. rewrite H0. apply (i_oc p s I _ _ _ H).
  - intros c' j t H. rewrite OH in H. rewrite ENT. pose proof (oh_lt_tm p s c' j t I H) as L.
    apply Nat.ltb_lt in L. rewrite L. apply (i_oh p s I _ _ _ H).
  - intros c' j H H'. rewrite OC in H. rewrite OH in H'. rewrite RG.
    destruct (Nat.eqb_spec c' c); [subst; destruct (Nat.eqb_spec j k); [discriminate|]|];
    apply (i_rg0 p s I); auto.
  - intros c' j t H. rewrite OC, OH in H. rewrite ENT, RW, AI.
    destruct (Nat.eqb_spec c' c).
    + subst. destruct (Nat.eqb_spec j k).
      * destruct H as [H|[H _]]; [|discriminate]. injection H as <-. rewrite Nat.ltb_irrefl, Nat.eqb_refl. eexists; split; reflexivity.
      * assert (L : t < tm s) by (destruct H as [H|[_ H]]; [apply (oc_lt_tm p s c j t I H)|apply (oh_lt_tm p s c j t I H)]).
        apply Nat.ltb_lt in L. rewrite L. apply (i_rw p s I _ _ _ H).
    + assert (L : t < tm s) by (destruct H as [H|[_ H]]; [apply (oc_lt_tm p s c' j t I H)|apply (oh_lt_tm p s c' j t I H)]).
      apply Nat.ltb_lt in L. rewrite L. apply (i_rw p s I _ _ _ H).
  - intros c' j t H H' L. rewrite OC in H. rewrite OH in H'. rewrite pcs_ord in L |- *. rewrite AI.
    destruct (Nat.eqb_spec c' c).
    + subst. destruct (Nat.eqb_spec j k); [discriminate|].
      destruct (i_half p s I c j t H H' ltac:(lia)) as (L' & A & Lc). split; [lia|auto].
    + apply (i_half p s I c' j t H H' L).
  - intros c' j t H H' L. rewrite OC in H. rewrite OH in H'. rewrite pcs_ord in L.
    destruct (Nat.eqb_spec c' c).
    + subst c'. destruct (Nat.eqb_spec j k); [discriminate|]. assert (Lj : j < k) by lia.
      rewrite (AIP c j Lj). unfold sord. rewrite (cfail_set_s' p s c k i m' a K u w (bd cc) (upd (pcs s) c (S k))
        (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s ++ [(c, k, tm s)]) I Ho ltac:(lia) c j Lj).
      apply (i_halfp p s I c j t H H' Lj).
    + rewrite (CSO c' n). apply (i_halfp p s I c' j t H H' L).
  - intros c' j t1 t2 H H'. rewrite OH in H. rewrite OC in H'. rewrite AI.
    destruct (Nat.eqb_spec c' c).
    + subst. destruct (Nat.eqb_spec j k).
      * subst j. injection H' as <-. destruct Hoh as [Z|(t0 & Z & Ci)]; [congruence|].
        assert (t1 = t0) by congruence. subst t1. split; [apply (oh_lt_tm p s c k t0 I Z)|exact Ci].
      * apply (i_hoc p s I c j t1 t2 H H').
    + apply (i_hoc p s I c' j t1 t2 H H').
  - intros t e H r Hr. rewrite ENT in H. apply STL in Hr.
    destruct (Nat.eq_dec (ec e) c) as [Ec|Ec]; [destruct (Nat.eq_dec (ek e) k) as [Ek|Ek]|].
    + rewrite Ec, Ek in *. rewrite AI, !Nat.eqb_refl. rewrite (proj2 (Hd r Hr)). symmetry. exact IE.
    + destruct (Nat.ltb_spec t (tm s)).
      * rewrite Ec in *. rewrite !AI, (proj2 (Nat.eqb_eq c c) eq_refl). destruct (Nat.eqb_spec (ek e) k); [contradiction|].
        pose proof (i_det p s I t e H) as D. rewrite Ec in D. rewrite (D r Hr). symmetry. apply D.
        intros j X. apply RS. exact X.
      * destruct (Nat.eqb_spec t (tm s)); [|discriminate]. injection H as <-. cbn [ec ek] in *. contradiction.
    + destruct (Nat.ltb_spec t (tm s)).
      * rewrite (CSO (ec e) Ec). apply (i_det p s I t e H). exact Hr.
      * destruct (Nat.eqb_spec t (tm s)); [|discriminate]. injection H as <-. cbn [ec ek] in *. contradiction.
  - intros c' j H Ex. rewrite pcs_ord in H. rewrite OC. destruct (Nat.eqb_spec c' c).
    + subst. destruct (Nat.eqb_spec j k); [discriminate|]. apply (i_pc p s I); [lia|].
      rewrite <- (XXS c j ltac:(lia)). exact Ex.
    + rewrite (CSO c' n) in Ex. apply (i_pc p s I); auto.
  - intros c' k' H X. rewrite pcs_ord in H. rewrite OC in X. rewrite AI. destruct (Nat.eqb_spec c' c).
    + subst. destruct (Nat.eqb_spec k' k); [lia|]. apply (i_pend p s I); auto. lia.
    + apply (i_pend p s I); auto.
  - intros c' k' tk d j P X Lj Ex T. unfold pending in P. rewrite pcs_ord in P, Lj. rewrite OC in X, P. rewrite AI in P.
    destruct (Nat.eqb_spec c' c).
    + subst c'. destruct (Nat.eqb_spec k' k); [lia|]. destruct P as (P1 & P2 & P3).
      assert (PO : pending cc k k' d) by (unfold pending; repeat split; auto; lia).
      destruct (Nat.eq_dec j k).
      * subst j. exfalso. apply xex_exec in Ex. rewrite IN in Ex, T. apply (Hb ltac:(unfold executes, icond in *; rewrite <- IE; auto) k' d PO T).
      * assert (j < k) by lia. rewrite (proj1 (SET c j H)) in T. rewrite (XXS c j H) in Ex.
        destruct (i_ptie p s I c k' tk d j PO X H Ex T) as (tj & A1 & A2). eauto.
    + rewrite (CSO c' n) in *. apply (i_ptie p s I c' k' tk d j); auto.
  - intros c' j k2 tk Ljk Lk X Ex T. rewrite pcs_ord in Lk. rewrite OC in X. destruct (Nat.eqb_spec c' c).
    + subst c'. destruct (Nat.eqb_spec k2 k).
      * subst k2. injection X as <-. assert (Lj : j < k) by lia.
        destruct (oc cc j) as [tj|] eqn:Oj; [|exfalso; apply (i_pc p s I c j Lj); [rewrite <- (XXS c j Lj); exact Ex|exact Oj]].
        exists tj. split; [apply OOLD; auto|]. apply (oc_lt_tm p s c j tj I Oj).
      * assert (L2 : k2 < k) by lia. assert (Lj : j < k) by lia.
        rewrite (proj1 (SET c j Lj)), (proj1 (SET c k2 L2)) in T. rewrite (XXS c j Lj) in Ex.
        destruct (i_po p s I c j k2 tk Ljk L2 X Ex T) as (tj & A1 & A2). eauto.
    + rewrite (CSO c' n) in *. apply (i_po p s I c' j k2 tk); auto.
  - intros c' j Hj. unfold sord, evs in Hj; simpl in Hj. rewrite OC, OH. unfold upd in Hj. destruct (Nat.eqb_spec c' c).
    + subst. destruct (Nat.eqb_spec j k); [lia|]. apply (i_tp p s I). lia.
    + apply (i_tp p s I). auto.
  - intros c' j. rewrite pcs_ord. unfold sord, evs; cbn [cm]. setoid_rewrite in_app_iff. simpl.
    destruct (Nat.eqb_spec c' c).
    + subst c'. split.
      * intros Hj. destruct (Nat.lt_ge_cases j k).
        -- destruct (proj1 (i_cmA p s I c j) H) as (tau & Ht). eauto.
        -- exists (tm s). right. left. f_equal. f_equal. lia.
      * intros (tau & [Ht|[E|[]]]).
        -- assert (j < k) by (apply (i_cmA p s I c j); eauto). lia.
        -- injection E as E1 E2. lia.
    + rewrite (i_cmA p s I c' j). split.
      * intros (tau & Ht); eauto.
      * intros (tau & [Ht|[E|[]]]); eauto. injection E as E; congruence.
  - intros n1 n2 c' j1 j2 t1 t2 Hn H1 H2. unfold sord, evs in H1, H2; cbn [cm] in H1, H2.
    rewrite nth_error_app_last in H1, H2.
    destruct (Nat.ltb_spec n1 (length (cm s))), (Nat.ltb_spec n2 (length (cm s))).
    + exact (i_cmB p s I n1 n2 c' j1 j2 t1 t2 Hn H1 H2).
    + destruct (Nat.eqb_spec n2 (length (cm s))); [|discriminate]. injection H2 as E1 E2 E3. subst c' j2 t2.
      assert (j1 < pcs s c) by (apply (i_cmA p s I c j1); eauto using nth_error_In). lia.
    + lia.
    + destruct (Nat.eqb_spec n1 (length (cm s))), (Nat.eqb_spec n2 (length (cm s))); try discriminate; lia.
  - intros n1 n2 c1 c2 j1 j2 t1 t2 Hn H1 H2. unfold sord, evs in H1, H2; cbn [cm] in H1, H2.
    rewrite nth_error_app_last in H1, H2.
    destruct (Nat.ltb_spec n1 (length (cm s))), (Nat.ltb_spec n2 (length (cm s))).
    + exact (i_cmC p s I n1 n2 c1 c2 j1 j2 t1 t2 Hn H1 H2).
    + destruct (Nat.eqb_spec n2 (length (cm s))); [|discriminate]. injection H2 as E1 E2 E3. subst c2 j2 t2.
      apply nth_error_In in H1. apply (i_cmE p s I) in H1. lia.
    + lia.
    + destruct (Nat.eqb_spec n1 (length (cm s))), (Nat.eqb_spec n2 (length (cm s))); try discriminate; lia.
  - intros c' j tau H j' Hj' Ex. unfold sord, evs in H; cbn [cm] in H. apply in_app_iff in H.
    destruct H as [H|[E|[]]].
    + assert (Lj : j < pcs s c') by (apply (i_cmA p s I c' j); eauto).
      rewrite (XXS c' j' ltac:(lia)) in Ex.
      destruct (i_cmD p s I c' j tau H j' Hj' Ex) as (t' & X & Y). eauto.
    + injection E as E1 E2 E3. subst c' j tau. rewrite OC, Nat.eqb_refl.
      destruct (Nat.eqb_spec j' k); [eexists; split; [reflexivity|lia]|].
      assert (Lj : j' < k) by lia.
      destruct (oc cc j') as [t'|] eqn:X; [|exfalso; apply (i_pc p s I c j' Lj); [rewrite <- (XXS c j' Lj); exact Ex|exact X]].
      exists t'. split; auto. pose proof (oc_lt_tm p s c j' t' I X). lia.
  - intros c' j tau H. unfold sord, evs in H; cbn [cm] in H. apply in_app_iff in H. simpl.
    destruct H as [H|[E|[]]].
    + apply (i_cmE p s I) in H. lia.
    + injection E as E1 E2 E3. subst c' j tau. lia.
  - intros c' j tau H. unfold sord, evs in H; cbn [cm] in H. apply in_app_iff in H.
    destruct H as [H|[E|[]]].
    + assert (Lj : j < pcs s c') by (apply (i_cmA p s I c' j); eauto).
      destruct (i_set p s I c' j tau H) as (S1 & S2). split.
      * intros r Hr. rewrite (proj1 (SET c' j Lj)), (proj2 (SET c' j Lj)).
        apply S1. intros j' [L|(t' & X & Lt)].
        -- rewrite (Hr j' (or_introl L)). apply RS. left. lia.
        -- rewrite (Hr j' (or_intror (ex_intro _ t' (conj (OOLD _ _ _ X) Lt)))). apply RS. right. congruence.
      * rewrite (AIP c' j Lj). rewrite (proj1 (SET c' j Lj)). exact S2.
    + injection E as E1 E2 E3. subst c' j tau. split.
      * intros r Hr. rewrite IN. assert (S1 : settled cc k r) by (apply ord_settled; exact Hr).
        destruct (Hd r S1) as [D1 D2]. rewrite D1. split; auto. rewrite D2. symmetry. exact IE.
      * rewrite AI, !Nat.eqb_refl. symmetry. exact IN.
  - intros c' j tau H Ex D. unfold sord, evs in H; cbn [cm] in H. apply in_app_iff in H.
    destruct H as [H|[E|[]]].
    + assert (Lj : j < pcs s c') by (apply (i_cmA p s I c' j); eauto).
      apply OOLD. apply (i_cmF p s I c' j tau H); [rewrite <- (EXS c' j Lj); exact Ex|].
      rewrite <- D. symmetry. unfold sord. apply eof_set_s'; auto; lia.
    + injection E as E1 E2 E3. subst c' j tau. rewrite OC, !Nat.eqb_refl. reflexivity.
  - intros c'. rewrite pcs_ord. unfold sord, evs; simpl. unfold upd. pose proof (i_pctp p s I c').
    destruct (Nat.eqb_spec c' c); [subst|]; lia.
  - intros c' k' tk d j P X Lj Ex T. unfold pending in P. rewrite pcs_ord in P, Lj. rewrite OC in X, P. rewrite AI in P.
    destruct (Nat.eqb_spec c' c).
    + subst c'. destruct (Nat.eqb_spec k' k); [lia|]. destruct P as (P1 & P2 & P3).
      assert (PO : pending cc k k' d) by (unfold pending; repeat split; auto; lia).
      destruct (Nat.eq_dec j k).
      * subst j. exfalso. rewrite IN in Ex, T. apply (Hb ltac:(unfold executes, icond in *; rewrite <- IE; auto) k' d PO T).
      * assert (j < k) by lia. rewrite (proj1 (SET c j H)) in T. rewrite (EXS c j H) in Ex.
        destruct (i_ptiet p s I c k' tk d j PO X H Ex T) as (tj & A1 & A2). exists tj. split; [rewrite TMO by (right; lia); exact A1|exact A2].
    + rewrite (CSO c' n) in *. apply (i_ptiet p s I c' k' tk d j); auto.
  - intros c' k' tk m0 xs0 j P X Lj Ex T. destruct P as (P1 & P2 & P3). rewrite pcs_ord in P1, Lj. rewrite OH in P2, X. rewrite AI in P3.
    destruct (Nat.eqb_spec c' c).
    + subst c'. destruct (Nat.eqb_spec k' k); [lia|].
      assert (PO : hpending cc k k' m0 xs0) by (unfold hpending; repeat split; auto; lia).
      destruct (Nat.eq_dec j k).
      * subst j. exfalso. rewrite IN in Ex, T. apply (Hbh ltac:(unfold executes, icond in *; rewrite <- IE; auto) k' m0 xs0 PO ltac:(lia) T).
      * assert (j < k) by lia. rewrite (proj1 (SET c j H)) in T. rewrite (EXS c j H) in Ex.
        destruct (i_ptieh p s I c k' tk m0 xs0 j PO X H Ex T) as (tj & A1 & A2). exists tj. split; [rewrite TMO by (right; lia); exact A1|exact A2].
    + rewrite (CSO c' n) in *. apply (i_ptieh p s I c' k' tk m0 xs0 j); auto. split; [exact P1|split; [exact P2|exact P3]].
  - intros c' j k2 tk Ljk Lk X Ex T. rewrite pcs_ord in Lk. destruct (Nat.eqb_spec c' c).
    + subst c'. destruct (Nat.eq_dec k2 k).
      * subst k2. assert (Lj : j < k) by lia. rewrite (EXS c j Lj) in Ex.
        destruct (tmo_passed p s c j I Lj Ex) as (tj & A1 & A2). exists tj. split; [rewrite TMO by (right; lia); exact A1|].
        unfold tmo in X. rewrite OC, !Nat.eqb_refl in X. injection X as <-. exact A2.
      * assert (L2 : k2 < k) by lia. assert (Lj : j < k) by lia. rewrite TMO in X by (right; lia).
        rewrite (proj1 (SET c j Lj)), (proj1 (SET c k2 L2)) in T. rewrite (EXS c j Lj) in Ex.
        destruct (i_pot p s I c j k2 tk Ljk L2 X Ex T) as (tj & A1 & A2). exists tj. split; [rewrite TMO by (right; lia); exact A1|exact A2].
    + rewrite (CSO c' n) in *. apply (i_pot p s I c' j k2 tk); auto.
  - intros c' j tau H j' Hj' Ex. unfold sord, evs in H; cbn [cm] in H. apply in_app_iff in H.
    destruct H as [H|[E|[]]].
    + assert (Lj : j < pcs s c') by (apply (i_cmA p s I c' j); eauto).
      rewrite (EXS c' j' ltac:(lia)) in Ex. destruct (i_cmDt p s I c' j tau H j' Hj' Ex) as (t' & X & Y).
      exists t'. split; [|exact Y]. rewrite TMO; [exact X|]. destruct (Nat.eq_dec c' c); [right; subst; lia|left; auto].
    + injection E as E1 E2 E3. subst c' j tau. destruct (Nat.eq_dec j' k) as [->|Nj].
      * exists (tm s). split; [unfold tmo; rewrite OC, !Nat.eqb_refl; reflexivity|lia].
      * assert (Lj : j' < k) by lia. rewrite (EXS c j' Lj) in Ex.
        destruct (tmo_passed p s c j' I Lj Ex) as (t' & X & Y). exists t'. split; [rewrite TMO by (right; lia); exact X|lia].
  - intros c' j t1 t2 H H'. rewrite OH in H. rewrite OC in H'. destruct (Nat.eqb_spec c' c).
    + subst c'. destruct (Nat.eqb_spec j k).
      * subst j. rewrite AI, !Nat.eqb_refl. destruct Hoh as [Z|(t0 & Z & Ci)]; [congruence|].
        pose proof (Hw ltac:(congruence)) as Wt. subst w.
        apply cfail_eq; [exact Ci|]. rewrite RG, !Nat.eqb_refl. rewrite (eval_e_ieval i _ _ IE).
        apply (eff_cas_ok_e _ _ _ _ _ _ _ _ Ci He).
      * rewrite AI, Nat.eqb_refl. destruct (Nat.eqb_spec j k); [lia|].
        rewrite (cfail_keep p s c j _ I ltac:(congruence) ord_settled_new). apply (i_hocf p s I c j t1 t2 H H').
    + rewrite (CSO c' n). apply (i_hocf p s I c' j t1 t2 H H').
  - intros c' j t H H' L. rewrite OC in H. rewrite OH in H'. rewrite pcs_ord in L. rewrite RG.
    destruct (Nat.eqb_spec c' c).
    + subst c'. destruct (Nat.eqb_spec j k); [discriminate|]. assert (Lj : j < k) by lia.
      apply (i_halfv p s I c j t H H' Lj).
    + apply (i_halfv p s I c' j t H H' L).
Qed.

End Ord.

(* an early access is an access of the programme, so its context has code *)
Lemma early_len : forall p c cc pc N T d u B, early_ok p c cc pc N T d u B -> c < length p.
Proof.
  intros p c cc pc N T d u B H. destruct (H (fun _ _ => 0)) as (j & _ & F & _).
  assert (D : exists d', eof (ins p c j (creg p c cc pc N (bor (bd cc) B) (fun _ _ => 0))) (creg p c cc pc N (bor (bd cc) B) (fun _ _ => 0)) = Some d')
    by (unfold first_at in F; simpl in F; destruct F as (_ & D & _); eauto). destruct D as (d' & D).
  destruct (Nat.lt_ge_cases c (length p)) as [L|L]; auto. exfalso.
  unfold ins, code in D. rewrite nth_overflow in D by auto. discriminate.
Qed.

(* an early access is not a guard() *)
Lemma early_nofull : forall p c cc pc N T d u B, early_ok p c cc pc N T d u B -> d <> DFn FFull.
Proof.
  intros p c cc pc N T d u B H E. destruct (H (fun _ _ => 0)) as (j & _ & F & _).
  unfold first_at in F; simpl in F; destruct F as (_ & D & _). subst d. apply (eof_nofull _ _ D).
Qed.

Lemma earlyW_len : forall p c cc pc N T T1 m xs d B, early_okW p c cc pc N T T1 m xs d B -> c < length p.
Proof.
  intros p c cc pc N T T1 m xs d B H. destruct (H (fun _ _ => 0)) as (j & _ & _ & D & _).
  destruct (Nat.lt_ge_cases c (length p)) as [L|L]; auto. exfalso.
  unfold ins, code in D. rewrite nth_overflow in D by auto. discriminate.
Qed.

(* ---------- R1 early ---------- *)
Section Early.
Variables (p : prog) (s : st) (c k : nat) (d : desc) (B : nat -> bool) (m' : mst) (a : val) (K : view)
          (u : cell -> option nat) (w : bool).
Hypothesis I : Inv1 p s.
Local Abbreviation cc := (cs s c).
Hypothesis Hk : pcs s c < k.
Hypothesis Ho : oc cc k = None.
Hypothesis Hnf : d <> DFn FFull.
Hypothesis Hlen : c < length p.
Hypothesis Hoh : oh cc k = None \/
  (exists t1, oh cc k = Some t1 /\ is_cas (inst_of d) = true /\ casx (ai cc k) = casx (inst_of d)).
Hypothesis Hw : oh cc k <> None -> w = true.
Hypothesis He : eff (tm s) (inst_of d) (rg cc) (mof s c) m' a K u w.
Local Abbreviation s' := (searly0 s c k d B m' a K u w).
Local Abbreviation TP := (upd (tp s) c (Nat.max (tp s c) (S k))).

Lemma Inv1_early : Inv1 p s'.
Proof.
  pose proof (ent_s' p s c k (inst_of d) m' a K u w (bor (bd cc) B) (pcs s) TP (cm s) I) as ENT.
  pose proof (oc_s' s c k (inst_of d) m' a K u w (bor (bd cc) B) (pcs s) TP (cm s)) as OC.
  pose proof (ai_s' s c k (inst_of d) m' a K u w (bor (bd cc) B) (pcs s) TP (cm s)) as AI.
  pose proof (rg_s' s c k (inst_of d) m' a K u w (bor (bd cc) B) (pcs s) TP (cm s)) as RG.
  pose proof (rw_s' s c k (inst_of d) m' a K u w (bor (bd cc) B) (pcs s) TP (cm s)) as RW.
  pose proof (oh_s' s c k (inst_of d) m' a K u w (bor (bd cc) B) (pcs s) TP (cm s)) as OH.
  fold s' in ENT, OC, AI, RG, RW, OH.
  assert (ROLD : forall c' j, oc (cs s c') j <> None -> rg (cs s' c') j = rg (cs s c') j).
  { intros. unfold searly0. apply rg_old_s'; auto. }
  assert (AOLD : forall c' j, oc (cs s c') j <> None -> ai (cs s' c') j = ai (cs s c') j).
  { intros. unfold searly0. apply ai_old_s'; auto. }
  assert (OOLD : forall c' j t, oc (cs s c') j = Some t -> oc (cs s' c') j = Some t).
  { intros. unfold searly0. apply oc_old_s'; auto. }
  assert (SET : forall c' j, j < pcs s c' ->
    ins p c' j (rg (cs s' c')) = ins p c' j (rg (cs s c')) /\
    ieval (ins p c' j (rg (cs s c'))) (rg (cs s' c')) = ieval (ins p c' j (rg (cs s c'))) (rg (cs s c'))).
  { intros. unfold searly0. apply ins_set_s'; auto; lia. }
  assert (EXS : forall c' j, j < pcs s c' ->
    executes (ins p c' j (rg (cs s' c'))) (rg (cs s' c')) = executes (ins p c' j (rg (cs s c'))) (rg (cs s c'))).
  { intros. unfold searly0. apply executes_set_s'; auto; lia. }
  assert (XXS : forall c' j, j < pcs s c' ->
    xex (cs s' c') (ins p c' j (rg (cs s' c'))) (rg (cs s' c')) j = xex (cs s c') (ins p c' j (rg (cs s c'))) (rg (cs s c')) j).
  { intros. unfold searly0. apply xex_set_s'; auto; lia. }
  assert (CSO : forall c', c' <> c -> cs s' c' = cs s c').
  { intros. unfold searly0. apply cs_other; auto. }
  assert (PCS : pcs s' = pcs s) by reflexivity.
  assert (RS : forall c' j, j < pcs s c' \/ oc (cs s c') j <> None -> rg (cs s' c') j = rg (cs s c') j).
  { intros c' j X. rewrite RG. destruct (Nat.eqb_spec c' c); auto. subst. destruct (Nat.eqb_spec j k); auto.
    subst. destruct X; [lia|congruence]. }
  assert (AIP : forall c' j, j < pcs s c' -> ai (cs s' c') j = ai (cs s c') j).
  { intros c' j L. rewrite AI. destruct (Nat.eqb_spec c' c); auto. subst. destruct (Nat.eqb_spec j k); auto. lia. }
  assert (STL : forall c' r, settled (cs s' c') (pcs s' c') r -> settled (cs s c') (pcs s c') r).
  { intros c' r Hr j X. rewrite <- (RS c' j X). apply Hr. rewrite PCS, OC.
    destruct (Nat.eqb_spec c' c); [subst|]; [destruct (Nat.eqb_spec j k)|]; destruct X as [X|X]; auto; try (left; lia);
    right; discriminate. }
  assert (PEND : forall c' k' d', pending (cs s' c') (pcs s c') k' d' ->
    (c' = c /\ k' = k /\ d' = d) \/ pending (cs s c') (pcs s c') k' d').
  { intros c' k' d' (P1 & P2 & P3). rewrite OC in P2. rewrite AI in P3. destruct (Nat.eqb_spec c' c).
    - subst c'. destruct (Nat.eqb_spec k' k).
      + subst. left. split; auto. split; auto. symmetry. apply inst_of_inj. auto.
      + right. unfold pending. auto.
    - right. unfold pending. auto. }
  assert (TMO : forall c' j, (c' <> c \/ j <> k) -> tmo (cs s' c') j = tmo (cs s c') j).
  { intros c' j Nj. unfold tmo. rewrite OC, OH. destruct (Nat.eqb_spec c' c); [subst; destruct (Nat.eqb_spec j k)|];
      [destruct Nj; congruence|reflexivity|reflexivity]. }
  assert (TMOp : forall c' j, j < pcs s c' -> tmo (cs s' c') j = tmo (cs s c') j).
  { intros c' j L. apply TMO. destruct (Nat.eq_dec c' c) as [->|Nc]; [right; lia|left; exact Nc]. }
  assert (HPD : forall c' k' m0 xs0, hpending (cs s' c') (pcs s' c') k' m0 xs0 -> hpending (cs s c') (pcs s c') k' m0 xs0).
  { intros c' k' m0 xs0 (P1 & P2 & P3). rewrite PCS in P1. rewrite OH in P2. rewrite AI in P3.
    split; [exact P1|split; [exact P2|]]. destruct (Nat.eqb_spec c' c); [subst c'; destruct (Nat.eqb_spec k' k)|]; auto.
    subst k'. destruct Hoh as [Z|(t0 & Z & Ci & Cx)]; [congruence|]. rewrite Cx. exact P3. }
  constructor.
  - unfold searly0, evs; simpl. rewrite length_app, (i_tm p s I). simpl. lia.
  - intros t e H. rewrite ENT in H. destruct (Nat.ltb_spec t (tm s)).
    + destruct (i_et p s I t e H) as (E1 & E2). split; auto. destruct (eh e).
      * rewrite OH. exact E2.
      * apply OOLD. exact E2.
    + destruct (Nat.eqb_spec t (tm s)); [|discriminate]. injection H as <-. subst. cbn [et ec ek eh].
      rewrite OC, !Nat.eqb_refl. split; auto.
  - intros c' j t H. rewrite OC in H. rewrite ENT.
    destruct (Nat.eqb_spec c' c).
    + subst. destruct (Nat.eqb_spec j k).
      * injection H as <-. subst. rewrite Nat.ltb_irrefl, Nat.eqb_refl. eauto.
      * pose proof (oc_lt_tm p s c j t I H). apply Nat.ltb_lt in H0. rewrite H0. apply (i_oc p s I _ _ _ H).
    + pose proof (oc_lt_tm p s c' j t I H). apply Nat.ltb_lt in H0. rewrite H0. apply (i_oc p s I _ _ _ H).
  - intros c' j t H. rewrite OH in H. rewrite ENT. pose proof (oh_lt_tm p s c' j t I H) as L.
    apply Nat.ltb_lt in L. rewrite L. apply (i_oh p s I _ _ _ H).
  - intros c' j H H'. rewrite OC in H. rewrite OH in H'. rewrite RG.
    destruct (Nat.eqb_spec c' c); [subst; destruct (Nat.eqb_spec j k); [discriminate|]|];
    apply (i_rg0 p s I); auto.
  - intros c' j t H. rewrite OC, OH in H. rewrite ENT, RW, AI.
    destruct (Nat.eqb_spec c' c).
    + subst. destruct (Nat.eqb_spec j k).
      * destruct H as [H|[H _]]; [|discriminate]. injection H as <-. rewrite Nat.ltb_irrefl, Nat.eqb_refl. eexists; split; reflexivity.
      * assert (L : t < tm s) by (destruct H as [H|[_ H]]; [apply (oc_lt_tm p s c j t I H)|apply (oh_lt_tm p s c j t I H)]).
        apply Nat.ltb_lt in L. rewrite L. apply (i_rw p s I _ _ _ H).
    + assert (L : t < tm s) by (destruct H as [H|[_ H]]; [apply (oc_lt_tm p s c' j t I H)|apply (oh_lt_tm p s c' j t I H)]).
      apply Nat.ltb_lt in L. rewrite L. apply (i_rw p s I _ _ _ H).
  - intros c' j t H H' L. rewrite OC in H. rewrite OH in H'. rewrite PCS in L |- *. rewrite AI.
    destruct (Nat.eqb_spec c' c).
    + subst. destruct (Nat.eqb_spec j k); [discriminate|]. apply (i_half p s I c j t H H' L).
    + apply (i_half p s I c' j t H H' L).
  - intros c' j t H H' L. rewrite OC in H. rewrite OH in H'. rewrite PCS in L.
    destruct (Nat.eqb_spec c' c).
    + subst c'. destruct (Nat.eqb_spec j k); [discriminate|].
      rewrite (AIP c j L). unfold searly0. rewrite (cfail_set_s' p s c k (inst_of d) m' a K u w (bor (bd cc) B) (pcs s) TP (cm s)
        I Ho ltac:(lia) c j L).
      apply (i_halfp p s I c j t H H' L).
    + rewrite (CSO c' n). apply (i_halfp p s I c' j t H H' L).
  - intros c' j t1 t2 H H'. rewrite OH in H. rewrite OC in H'. rewrite AI.
    destruct (Nat.eqb_spec c' c).
    + subst. destruct (Nat.eqb_spec j k).
      * subst j. injection H' as <-. destruct Hoh as [Z|(t0 & Z & Ci & _)]; [congruence|].
        assert (t1 = t0) by congruence. subst t1. split; [apply (oh_lt_tm p s c k t0 I Z)|exact Ci].
      * apply (i_hoc p s I c j t1 t2 H H').
    + apply (i_hoc p s I c' j t1 t2 H H').
  - intros t e H r Hr. rewrite ENT in H. apply STL in Hr.
    destruct (Nat.eq_dec (ec e) c) as [Ec|Ec]; [destruct (Nat.eq_dec (ek e) k) as [Ek|Ek]|].
    + rewrite Ec, Ek in *. rewrite AI, !Nat.eqb_refl. apply ieval_inst.
    + destruct (Nat.ltb_spec t (tm s)).
      * rewrite Ec in *. rewrite !AI, (proj2 (Nat.eqb_eq c c) eq_refl). destruct (Nat.eqb_spec (ek e) k); [contradiction|].
        pose proof (i_det p s I t e H) as D. rewrite Ec in D. rewrite (D r Hr). symmetry. apply D.
        intros j X. apply RS. exact X.
      * destruct (Nat.eqb_spec t (tm s)); [|discriminate]. injection H as <-. cbn [ec ek] in *. contradiction.
    + destruct (Nat.ltb_spec t (tm s)).
      * rewrite (CSO (ec e) Ec). apply (i_det p s I t e H). exact Hr.
      * destruct (Nat.eqb_spec t (tm s)); [|discriminate]. injection H as <-. cbn [ec ek] in *. contradiction.
  - intros c' j H Ex. rewrite PCS in H. rewrite OC. rewrite (XXS c' j H) in Ex. destruct (Nat.eqb_spec c' c).
    + subst. destruct (Nat.eqb_spec j k); [discriminate|]. apply (i_pc p s I); auto.
    + apply (i_pc p s I); auto.
  - intros c' k' H X. rewrite PCS in H. rewrite OC in X. rewrite AI. destruct (Nat.eqb_spec c' c).
    + subst. destruct (Nat.eqb_spec k' k); [split; [exists d; split; [reflexivity|exact Hnf]|exact Hlen]|]. apply (i_pend p s I); auto.
    + apply (i_pend p s I); auto.
  - intros c' k' tk d' j P X Lj Ex T. rewrite PCS in P, Lj.
    destruct (PEND c' k' d' P) as [(E1 & E2 & E3)|Q].
    + subst c' k' d'. rewrite OC, !Nat.eqb_refl in X. injection X as <-.
      destruct (oc cc j) as [tj|] eqn:Oj; [|exfalso; apply (i_pc p s I c j Lj); [rewrite <- (XXS c j Lj); exact Ex|exact Oj]].
      exists tj. split; [apply OOLD; auto|apply (oc_lt_tm p s c j tj I Oj)].
    + rewrite (proj1 (SET c' j Lj)) in T. rewrite (XXS c' j Lj) in Ex.
      assert (X' : oc (cs s c') k' = Some tk).
      { rewrite OC in X. destruct (Nat.eqb_spec c' c) as [E|E]; [|exact X]. subst c'.
        destruct (Nat.eqb_spec k' k) as [E'|E']; [|exact X]. subst k'.
        destruct Q as (_ & Q & _). exfalso. apply Q. exact Ho. }
      destruct (i_ptie p s I c' k' tk d' j Q X' Lj Ex T) as (tj & A1 & A2). eauto.
  - intros c' j k2 tk Ljk Lk X Ex T. rewrite PCS in Lk.
    assert (X' : oc (cs s c') k2 = Some tk).
    { rewrite OC in X. destruct (Nat.eqb_spec c' c) as [E|E]; [|exact X]. subst c'.
      destruct (Nat.eqb_spec k2 k) as [E'|E']; [lia|exact X]. }
    assert (Lj : j < pcs s c') by lia.
    rewrite (proj1 (SET c' j Lj)), (proj1 (SET c' k2 Lk)) in T. rewrite (XXS c' j Lj) in Ex.
    destruct (i_po p s I c' j k2 tk Ljk Lk X' Ex T) as (tj & A1 & A2). eauto.
  - intros c' j Hj. unfold searly0, evs in Hj; simpl in Hj. rewrite OC, OH. unfold upd in Hj. destruct (Nat.eqb_spec c' c).
    + subst. destruct (Nat.eqb_spec j k); [lia|]. apply (i_tp p s I). lia.
    + apply (i_tp p s I). auto.
  - intros c' j. rewrite PCS. apply (i_cmA p s I c' j).
  - intros. apply (i_cmB p s I n1 n2 c0 j1 j2 t1 t2); auto.
  - intros. apply (i_cmC p s I n1 n2 c1 c2 j1 j2 t1 t2); auto.
  - intros c' j tau H j' Hj' Ex.
    assert (Lj : j < pcs s c') by (apply (i_cmA p s I c' j); eauto).
    rewrite (XXS c' j' ltac:(lia)) in Ex. destruct (i_cmD p s I c' j tau H j' Hj' Ex) as (t' & X & Y). eauto.
  - intros c' j tau H. apply (i_cmE p s I) in H. simpl. lia.
  - intros c' j tau H.
    assert (Lj : j < pcs s c') by (apply (i_cmA p s I c' j); eauto).
    destruct (i_set p s I c' j tau H) as (S1 & S2). split.
    + intros r Hr. rewrite (proj1 (SET c' j Lj)), (proj2 (SET c' j Lj)).
      apply S1. intros j' [L|(t' & X & Lt)].
      * rewrite (Hr j' (or_introl L)). apply RS. left. lia.
      * rewrite (Hr j' (or_intror (ex_intro _ t' (conj (OOLD _ _ _ X) Lt)))). apply RS. right. congruence.
    + rewrite (AIP c' j Lj), (proj1 (SET c' j Lj)). exact S2.
  - intros c' j tau H Ex D.
    assert (Lj : j < pcs s c') by (apply (i_cmA p s I c' j); eauto).
    apply OOLD. apply (i_cmF p s I c' j tau H); [rewrite <- (EXS c' j Lj); exact Ex|].
    rewrite <- D. symmetry. unfold searly0. apply eof_set_s'; auto; lia.
  - intros c'. rewrite PCS. unfold searly0, evs; simpl. unfold upd. pose proof (i_pctp p s I c').
    destruct (Nat.eqb_spec c' c); [subst|]; lia.
  - intros c' k' tk d' j P X Lj Ex T. rewrite PCS in P, Lj.
    rewrite (EXS c' j Lj) in Ex. rewrite (TMOp c' j Lj).
    destruct (PEND c' k' d' P) as [(E1 & E2 & E3)|Q].
    + subst c' k' d'. rewrite OC, !Nat.eqb_refl in X. injection X as <-.
      apply (tmo_passed p s c j I Lj Ex).
    + rewrite (proj1 (SET c' j Lj)) in T.
      assert (X' : oc (cs s c') k' = Some tk).
      { rewrite OC in X. destruct (Nat.eqb_spec c' c) as [E|E]; [|exact X]. subst c'.
        destruct (Nat.eqb_spec k' k) as [E'|E']; [|exact X]. subst k'.
        destruct Q as (_ & Q & _). exfalso. apply Q. exact Ho. }
      apply (i_ptiet p s I c' k' tk d' j Q X' Lj Ex T).
  - intros c' k' tk m0 xs0 j P X Lj Ex T. rewrite PCS in Lj. rewrite (EXS c' j Lj) in Ex. rewrite (TMOp c' j Lj).
    rewrite (proj1 (SET c' j Lj)) in T. rewrite OH in X. apply (i_ptieh p s I c' k' tk m0 xs0 j (HPD c' k' m0 xs0 P) X Lj Ex T).
  - intros c' j k2 tk Ljk Lk X Ex T. rewrite PCS in Lk. assert (Lj : j < pcs s c') by lia.
    rewrite (TMOp c' k2 Lk) in X. rewrite (TMOp c' j Lj).
    rewrite (proj1 (SET c' j Lj)), (proj1 (SET c' k2 Lk)) in T. rewrite (EXS c' j Lj) in Ex.
    apply (i_pot p s I c' j k2 tk Ljk Lk X Ex T).
  - intros c' j tau H j' Hj' Ex.
    assert (Lj : j < pcs s c') by (apply (i_cmA p s I c' j); eauto).
    rewrite (EXS c' j' ltac:(lia)) in Ex. rewrite (TMOp c' j' ltac:(lia)). apply (i_cmDt p s I c' j tau H j' Hj' Ex).
  - intros c' j t1 t2 H H'. rewrite OH in H. rewrite OC in H'. destruct (Nat.eqb_spec c' c).
    + subst c'. destruct (Nat.eqb_spec j k).
      * subst j. rewrite AI, !Nat.eqb_refl. destruct Hoh as [Z|(t0 & Z & Ci & _)]; [congruence|].
        pose proof (Hw ltac:(congruence)) as Wt. subst w.
        apply cfail_eq; [exact Ci|]. rewrite RG, !Nat.eqb_refl. rewrite (eval_e_ieval _ _ (rg cc) (ieval_inst d _ _)).
        apply (eff_cas_ok_e _ _ _ _ _ _ _ _ Ci He).
      * rewrite AI, Nat.eqb_refl. destruct (Nat.eqb_spec j k); [lia|]. unfold searly0.
        rewrite (cfail_keep p s c j _ I ltac:(congruence)
                   (settled_s' s c k (inst_of d) m' a K u w (bor (bd cc) B) (pcs s) TP (cm s) Ho ltac:(lia) c)).
        apply (i_hocf p s I c j t1 t2 H H').
    + rewrite (CSO c' n). apply (i_hocf p s I c' j t1 t2 H H').
  - intros c' j t H H' L. rewrite OC in H. rewrite OH in H'. rewrite PCS in L. rewrite RG.
    destruct (Nat.eqb_spec c' c).
    + subst c'. destruct (Nat.eqb_spec j k); [discriminate|]. apply (i_halfv p s I c j t H H' L).
    + apply (i_halfv p s I c' j t H H' L).
Qed.

End Early.

(* ---------- reaching an early access ---------- *)
Section Match.
Variables (p : prog) (s : st) (c : nat) (d : desc).
Hypothesis I : Inv1 p s.
Local Abbreviation cc := (cs s c).
Local Abbreviation k := (pcs s c).
Hypothesis Ho : oc cc k <> None.
Hypothesis Ha : ai cc k = inst_of d.
Hypothesis Hdf : eof (ins p c k (rg cc)) (rg cc) = Some d.
Hypothesis Hd : determined p cc c k (ins p c k (rg cc)).
Hypothesis Hf : forall k' d' t t', pending cc k k' d' -> k' <> k -> oc cc k = Some t -> oc cc k' = Some t' ->
  tied (inst_of d) (inst_of d') -> t < t'.
Hypothesis Hfh : forall k' m xs t t', hpending cc k k' m xs -> k' <> k -> oc cc k = Some t -> oh cc k' = Some t' ->
  tied (inst_of d) (crd m xs) -> t < t'.
Local Abbreviation s' := (smatch p s c).

Lemma pcs_match : forall c', pcs s' c' = if Nat.eqb c' c then S k else pcs s c'.
Proof. intros c'. reflexivity. Qed.

Lemma oc_match : forall c', oc (cs s' c') = oc (cs s c').
Proof. intros c'. unfold smatch; simpl. unfold upd at 1. destruct (Nat.eqb_spec c' c); subst; reflexivity. Qed.

Lemma rg_match : forall c', rg (cs s' c') = rg (cs s c').
Proof. intros c'. unfold smatch; simpl. unfold upd at 1. destruct (Nat.eqb_spec c' c); subst; reflexivity. Qed.

Lemma rw_match : forall c', rw (cs s' c') = rw (cs s c').
Proof. intros c'. unfold smatch; simpl. unfold upd at 1. destruct (Nat.eqb_spec c' c); subst; reflexivity. Qed.

Lemma rv_match : forall c', rv (cs s' c') = rv (cs s c').
Proof. intros c'. unfold smatch; simpl. unfold upd at 1. destruct (Nat.eqb_spec c' c); subst; reflexivity. Qed.

Lemma oh_match : forall c', oh (cs s' c') = oh (cs s c').
Proof. intros c'. unfold smatch; simpl. unfold upd at 1. destruct (Nat.eqb_spec c' c); subst; reflexivity. Qed.

Lemma ai_match : forall c' j, ai (cs s' c') j =
  if Nat.eqb c' c && Nat.eqb j k then ins p c k (rg cc) else ai (cs s c') j.
Proof.
  intros c' j. unfold smatch; simpl. unfold upd at 1. destruct (Nat.eqb_spec c' c); subst; simpl; auto.
Qed.

Lemma ai_match_old : forall c' j, c' <> c \/ j <> k -> ai (cs s' c') j = ai (cs s c') j.
Proof.
  intros c' j H. rewrite ai_match. destruct (Nat.eqb_spec c' c), (Nat.eqb_spec j k); simpl; auto.
  destruct H; congruence.
Qed.

Lemma Inv1_match : Inv1 p s'.
Proof.
  assert (PK : pending cc k k d) by (unfold pending; repeat split; auto).
  assert (PEND : forall c' k' d', pending (cs s' c') (pcs s' c') k' d' -> pending (cs s c') (pcs s c') k' d' /\ (c' = c -> k < k')).
  { intros c' k' d' (P1 & P2 & P3). rewrite pcs_match in P1. rewrite oc_match in P2.
    destruct (Nat.eqb_spec c' c).
    - subst. rewrite ai_match_old in P3 by (right; lia). split; [unfold pending; repeat split; auto; lia|intros; lia].
    - rewrite ai_match_old in P3 by auto. split; [unfold pending; auto|intros; congruence]. }
  assert (STL : forall c' r, settled (cs s' c') (pcs s' c') r -> settled (cs s c') (pcs s c') r).
  { intros c' r Hr j X. rewrite <- (rg_match c'). apply Hr. rewrite pcs_match, oc_match.
    destruct (Nat.eqb_spec c' c); [subst|]; destruct X; auto; left; lia. }
  assert (TMOm : forall c' j, tmo (cs s' c') j = tmo (cs s c') j).
  { intros c' j. unfold tmo. rewrite oc_match, oh_match. reflexivity. }
  assert (XO : forall c', xex (cs s' c') = xex (cs s c')).
  { intros c'. unfold xex, ohb. rewrite oh_match. reflexivity. }
  constructor; try rewrite !oc_match; try rewrite !rg_match.
  - apply (i_tm p s I).
  - intros t e H. rewrite oc_match, oh_match. apply (i_et p s I t e H).
  - intros c' j t H. rewrite oc_match in H. apply (i_oc p s I c' j t H).
  - intros c' j t H. rewrite oh_match in H. apply (i_oh p s I c' j t H).
  - intros c' j H H'. rewrite oc_match in H. rewrite oh_match in H'. rewrite rg_match. apply (i_rg0 p s I c' j H H').
  - intros c' j t H. rewrite oc_match, oh_match in H. rewrite rw_match.
    assert (Ic : icells (ai (cs s' c') j) = icells (ai (cs s c') j)).
    { rewrite ai_match. destruct (Nat.eqb_spec c' c), (Nat.eqb_spec j k); simpl; auto. subst.
      rewrite Ha. apply (eof_icells _ _ _ Hdf). }
    rewrite Ic. apply (i_rw p s I c' j t H).
  - intros c' j t H H' L. rewrite oc_match in H. rewrite oh_match in H'. rewrite pcs_match in L |- *.
    destruct (Nat.eqb_spec c' c).
    + subst. assert (j <> k) by (intros ->; congruence). rewrite ai_match_old by auto.
      destruct (i_half p s I c j t H H' ltac:(lia)) as (L' & A & Lc). split; [lia|auto].
    + rewrite ai_match_old by auto. apply (i_half p s I c' j t H H' L).
  - intros c' j t H H' L. rewrite oc_match in H. rewrite oh_match in H'. rewrite pcs_match in L. try rewrite rg_match.
    destruct (Nat.eqb_spec c' c).
    + subst. assert (j <> k) by (intros ->; congruence). rewrite ai_match_old by auto.
      apply (i_halfp p s I c j t H H'). lia.
    + rewrite ai_match_old by auto. apply (i_halfp p s I c' j t H H' L).
  - intros c' j t1 t2 H H'. rewrite oh_match in H. rewrite oc_match in H'.
    destruct (i_hoc p s I c' j t1 t2 H H') as (L & Ci). split; auto. rewrite ai_match.
    destruct (Nat.eqb_spec c' c), (Nat.eqb_spec j k); simpl; auto. subst.
    rewrite Ha in Ci. rewrite (eof_cas _ _ _ Hdf). exact Ci.
  - intros t e H r Hr. apply STL in Hr. rewrite rg_match.
    destruct (Nat.eqb_spec (ec e) c), (Nat.eqb_spec (ek e) k).
    + rewrite ai_match. rewrite e0, e1, !Nat.eqb_refl. simpl. rewrite e0 in Hr.
      apply (proj2 (Hd r Hr)).
    + rewrite ai_match_old by auto. apply (i_det p s I t e H r Hr).
    + rewrite ai_match_old by auto. apply (i_det p s I t e H r Hr).
    + rewrite ai_match_old by auto. apply (i_det p s I t e H r Hr).
  - intros c' j H Ex. rewrite pcs_match in H. rewrite oc_match. rewrite rg_match, XO in Ex. destruct (Nat.eqb_spec c' c).
    + subst. destruct (Nat.eq_dec j k); [subst; auto|]. apply (i_pc p s I); auto. lia.
    + apply (i_pc p s I); auto.
  - intros c' k' H X. rewrite pcs_match in H. rewrite oc_match in X.
    assert (L : pcs s c' <= k' /\ (c' = c -> k < k')) by (revert H; destruct (Nat.eqb_spec c' c); intros H; subst; split; intros; lia).
    rewrite ai_match_old by (destruct (Nat.eq_dec c' c); [right; destruct L as [_ L]; specialize (L e); lia|left; auto]).
    apply (i_pend p s I); auto. tauto.
  - intros c' k' tk d' j P X Lj Ex T. destruct (PEND c' k' d' P) as [Q Qk]. rewrite pcs_match in Lj.
    rewrite oc_match in X. rewrite rg_match in Ex, T. rewrite XO in Ex.
    enough (exists tj, oc (cs s c') j = Some tj /\ tj < tk) as (tj & A1 & A2) by (exists tj; rewrite oc_match; auto).
    destruct (Nat.eqb_spec c' c).
    + subst c'. specialize (Qk eq_refl). destruct (Nat.eq_dec j k).
      * subst j. apply (proj1 (tied_eof_l _ _ _ _ Hdf)) in T.
        destruct (oc cc k) as [t0|] eqn:O0; [|congruence]. exists t0. split; [reflexivity|].
        apply (Hf k' d' t0 tk Q ltac:(lia) eq_refl X T).
      * apply (i_ptie p s I c k' tk d' j Q X); auto. lia.
    + apply (i_ptie p s I c' k' tk d' j Q X); auto.
  - intros c' j k2 tk Ljk Lk X Ex T. rewrite pcs_match in Lk. rewrite oc_match in X. rewrite rg_match in Ex, T. rewrite XO in Ex.
    enough (exists tj, oc (cs s c') j = Some tj /\ tj < tk) as (tj & A1 & A2) by (exists tj; rewrite oc_match; auto).
    destruct (Nat.eqb_spec c' c).
    + subst c'. destruct (Nat.eq_dec k2 k).
      * subst k2. apply (proj1 (tied_eof_r _ _ _ _ Hdf)) in T.
        apply (i_ptie p s I c k tk d j PK X); auto.
      * apply (i_po p s I c j k2 tk); auto. lia.
    + apply (i_po p s I c' j k2 tk); auto.
  - intros c' j H. rewrite oc_match, oh_match. apply (i_tp p s I c' j H).
  - intros c' j. rewrite pcs_match. unfold smatch; cbn [cm]. setoid_rewrite in_app_iff. simpl.
    destruct (Nat.eqb_spec c' c).
    + subst c'. split.
      * intros Hj. destruct (Nat.lt_ge_cases j k).
        -- destruct (proj1 (i_cmA p s I c j) H) as (tau & Ht). eauto.
        -- exists (tm s). right. left. f_equal. f_equal. lia.
      * intros (tau & [Ht|[E|[]]]).
        -- assert (j < k) by (apply (i_cmA p s I c j); eauto). lia.
        -- injection E as E1 E2. lia.
    + rewrite (i_cmA p s I c' j). split.
      * intros (tau & Ht); eauto.
      * intros (tau & [Ht|[E|[]]]); eauto. injection E as E; congruence.
  - intros n1 n2 c' j1 j2 t1 t2 Hn H1 H2. unfold smatch in H1, H2; cbn [cm] in H1, H2.
    rewrite nth_error_app_last in H1, H2.
    destruct (Nat.ltb_spec n1 (length (cm s))), (Nat.ltb_spec n2 (length (cm s))).
    + exact (i_cmB p s I n1 n2 c' j1 j2 t1 t2 Hn H1 H2).
    + destruct (Nat.eqb_spec n2 (length (cm s))); [|discriminate]. injection H2 as E1 E2 E3. subst c' j2 t2.
      assert (j1 < pcs s c) by (apply (i_cmA p s I c j1); eauto using nth_error_In). lia.
    + lia.
    + destruct (Nat.eqb_spec n1 (length (cm s))), (Nat.eqb_spec n2 (length (cm s))); try discriminate; lia.
  - intros n1 n2 c1 c2 j1 j2 t1 t2 Hn H1 H2. unfold smatch in H1, H2; cbn [cm] in H1, H2.
    rewrite nth_error_app_last in H1, H2.
    destruct (Nat.ltb_spec n1 (length (cm s))), (Nat.ltb_spec n2 (length (cm s))).
    + exact (i_cmC p s I n1 n2 c1 c2 j1 j2 t1 t2 Hn H1 H2).
    + destruct (Nat.eqb_spec n2 (length (cm s))); [|discriminate]. injection H2 as E1 E2 E3. subst c2 j2 t2.
      apply nth_error_In in H1. apply (i_cmE p s I) in H1. lia.
    + lia.
    + destruct (Nat.eqb_spec n1 (length (cm s))), (Nat.eqb_spec n2 (length (cm s))); try discriminate; lia.
  - intros c' j tau H j' Hj' Ex. rewrite oc_match. rewrite rg_match, XO in Ex. unfold smatch in H; cbn [cm] in H. apply in_app_iff in H.
    destruct H as [H|[E|[]]].
    + apply (i_cmD p s I c' j tau H j' Hj' Ex).
    + injection E as E1 E2 E3. subst c' j tau.
      destruct (oc cc j') as [t'|] eqn:X.
      * exists t'. split; auto. pose proof (oc_lt_tm p s c j' t' I X). lia.
      * exfalso. destruct (Nat.eq_dec j' k); [subst; congruence|]. apply (i_pc p s I c j'); auto. lia.
  - intros c' j tau H. unfold smatch in H; cbn [cm] in H. apply in_app_iff in H. simpl.
    destruct H as [H|[E|[]]].
    + apply (i_cmE p s I) in H. auto.
    + injection E as E1 E2 E3. subst. lia.
  - intros c' j tau H. rewrite oc_match, rg_match. unfold smatch in H; cbn [cm] in H. apply in_app_iff in H.
    destruct H as [H|[E|[]]].
    + assert (Lj : j < pcs s c') by (apply (i_cmA p s I c' j); eauto).
      rewrite ai_match_old by (destruct (Nat.eq_dec c' c); [right; subst; lia|left; auto]).
      apply (i_set p s I c' j tau H).
    + injection E as E1 E2 E3. subst c' j tau. split.
      * intros r Hr. apply Hd. intros j' [L|X]; [apply Hr; left; exact L|].
        destruct (oc cc j') as [t'|] eqn:Y; [|congruence].
        apply Hr. right. exists t'. split; [exact Y|apply (oc_lt_tm p s c j' t' I Y)].
      * rewrite ai_match, !Nat.eqb_refl. reflexivity.
  - intros c' j tau H Ex D. rewrite oc_match. rewrite rg_match in D, Ex. unfold smatch in H; cbn [cm] in H. apply in_app_iff in H.
    destruct H as [H|[E|[]]].
    + apply (i_cmF p s I c' j tau H Ex D).
    + injection E as E1 E2 E3. subst c' j tau. rewrite Hdf in D. discriminate.
  - intros c'. rewrite pcs_match. change (tp s' c') with (tp s c'). pose proof (i_pctp p s I c'). destruct (Nat.eqb_spec c' c); [subst|lia].
    destruct (Nat.le_gt_cases (tp s c) k) as [X|X]; [|lia]. exfalso. apply Ho. apply (proj1 (i_tp p s I c k X)).
  - intros c' k' tk d' j P X Lj Ex T. destruct (PEND c' k' d' P) as [Q Qk]. rewrite pcs_match in Lj.
    rewrite oc_match in X. rewrite rg_match in Ex, T. rewrite TMOm.
    destruct (Nat.eqb_spec c' c).
    + subst c'. specialize (Qk eq_refl). destruct (Nat.eq_dec j k).
      * subst j. apply (proj1 (tied_eof_l _ _ _ _ Hdf)) in T.
        destruct (oc cc k) as [t0|] eqn:O0; [|congruence]. exists t0. split; [unfold tmo; rewrite O0; reflexivity|].
        apply (Hf k' d' t0 tk Q ltac:(lia) eq_refl X T).
      * apply (i_ptiet p s I c k' tk d' j Q X); auto. lia.
    + apply (i_ptiet p s I c' k' tk d' j Q X); auto.
  - intros c' k' tk m0 xs0 j P X Lj Ex T. rewrite rg_match in Ex, T. rewrite oh_match in X. rewrite TMOm.
    destruct P as (P1 & P2 & P3). rewrite pcs_match in P1, Lj. rewrite oh_match in P2.
    destruct (Nat.eqb_spec c' c).
    + subst c'. rewrite ai_match_old in P3 by (right; lia).
      assert (PO : hpending cc k k' m0 xs0) by (split; [lia|split; auto]).
      destruct (Nat.eq_dec j k).
      * subst j. apply (proj1 (tied_eof_l _ _ _ _ Hdf)) in T.
        destruct (oc cc k) as [t0|] eqn:O0; [|congruence]. exists t0. split; [unfold tmo; rewrite O0; reflexivity|].
        apply (Hfh k' m0 xs0 t0 tk PO ltac:(lia) eq_refl X T).
      * apply (i_ptieh p s I c k' tk m0 xs0 j PO X); auto. lia.
    + rewrite ai_match_old in P3 by auto. apply (i_ptieh p s I c' k' tk m0 xs0 j); auto. split; [exact P1|split; [exact P2|exact P3]].
  - intros c' j k2 tk Ljk Lk X Ex T. rewrite pcs_match in Lk. rewrite TMOm in X |- *. rewrite rg_match in Ex, T.
    destruct (Nat.eqb_spec c' c).
    + subst c'. destruct (Nat.eq_dec k2 k).
      * subst k2. unfold tmo in X. destruct (oc cc k) as [t0|] eqn:O0; [|congruence]. injection X as <-.
        apply (proj1 (tied_eof_r _ _ _ _ Hdf)) in T. apply (i_ptiet p s I c k t0 d j PK O0); auto; lia.
      * apply (i_pot p s I c j k2 tk); auto. lia.
    + apply (i_pot p s I c' j k2 tk); auto.
  - intros c' j tau H j' Hj' Ex. rewrite TMOm. rewrite rg_match in Ex. unfold smatch in H; cbn [cm] in H. apply in_app_iff in H.
    destruct H as [H|[E|[]]].
    + apply (i_cmDt p s I c' j tau H j' Hj' Ex).
    + injection E as E1 E2 E3. subst c' j tau. destruct (Nat.eq_dec j' k) as [->|Nj].
      * destruct (oc cc k) as [t'|] eqn:X; [|congruence]. exists t'. split; [unfold tmo; rewrite X; reflexivity|].
        pose proof (oc_lt_tm p s c k t' I X). lia.
      * destruct (tmo_passed p s c j' I ltac:(lia) Ex) as (t' & A & B). exists t'. split; [exact A|lia].
  - intros c' j t1 t2 H H'. rewrite oh_match in H. rewrite oc_match in H'. rewrite rg_match. rewrite ai_match.
    destruct (Nat.eqb_spec c' c), (Nat.eqb_spec j k); simpl; try (apply (i_hocf p s I c' j t1 t2 H H')).
    subst. rewrite (cfail_eof _ _ _ _ Hdf), <- Ha. exact (i_hocf p s I c k t1 t2 H H').
  - intros c' j t H H' L. rewrite oc_match in H. rewrite oh_match in H'. rewrite pcs_match in L. rewrite rg_match.
    destruct (Nat.eqb_spec c' c).
    + subst. assert (j <> k) by (intros ->; congruence). apply (i_halfv p s I c j t H H'). lia.
    + apply (i_halfv p s I c' j t H H' L).
Qed.

End Match.

(* ---------- a CAS's read alone ---------- *)
Lemma earlyR_len : forall p c cc pc N T m xs u B, early_okR p c cc pc N T m xs u B -> c < length p.
Proof.
  intros p c cc pc N T m xs u B H. destruct (H (fun _ _ => 0)) as (j & (_ & D & _) & _).
  destruct (Nat.lt_ge_cases c (length p)) as [L|L]; auto. exfalso.
  unfold ins, code in D. rewrite nth_overflow in D by auto. discriminate.
Qed.

Section Read.
Variables (p : prog) (s : st) (c k : nat) (xs : list cell) (B : nat -> bool) (m' : mst) (a : val) (K : view)
          (u : cell -> option nat) (w : bool) (bv : bool).
Hypothesis I : Inv1 p s.
Local Abbreviation cc := (cs s c).
Hypothesis Hk : pcs s c <= k.
Hypothesis Ho : oc cc k = None.
Hypothesis Hh : oh cc k = None.
Hypothesis Hok : early_okR p c cc (pcs s c) (tp s c) (tm s) Plain xs u B.
Local Abbreviation s' := (sread s c k Plain xs B m' a K u w bv).
Local Abbreviation i := (ILd Plain xs (fun _ => true)).

Lemma ent_r : forall t, ent s' t =
  if Nat.ltb t (tm s) then ent s t else if Nat.eqb t (tm s) then Some (newevh s c k i K u w) else None.
Proof. intros t. unfold ent, sread. simpl. rewrite nth_error_app_last, (i_tm p s I). reflexivity. Qed.

Lemma cs_r : forall c', cs s' c' = if Nat.eqb c' c then
  mkC (oc cc) (upd (rg cc) k (vd bv a)) (upd (ai cc) k (crd Plain xs))
      (upd (rw cc) k (wrote (tm s) (icells i) u w)) (upd (rv cc) k (rdval (mof s c) u))
      (bor (bd cc) B) (mP m') (mA m') (mR m')
      (newO s c i (mof s c) m' (vO cc)) (newOg i m' (vOg cc)) (upd (oh cc) k (Some (tm s))) (fx cc)
  else cs s c'.
Proof. intros c'. unfold sread. simpl. unfold upd at 1. reflexivity. Qed.

Lemma oc_r : forall c', oc (cs s' c') = oc (cs s c').
Proof. intros c'. rewrite cs_r. destruct (Nat.eqb_spec c' c); subst; reflexivity. Qed.

Lemma field_r : forall c' j,
  rg (cs s' c') j = (if Nat.eqb c' c && Nat.eqb j k then vd bv a else rg (cs s c') j) /\
  ai (cs s' c') j = (if Nat.eqb c' c && Nat.eqb j k then crd Plain xs else ai (cs s c') j) /\
  rw (cs s' c') j = (if Nat.eqb c' c && Nat.eqb j k then wrote (tm s) (icells i) u w else rw (cs s c') j) /\
  oh (cs s' c') j = (if Nat.eqb c' c && Nat.eqb j k then Some (tm s) else oh (cs s c') j).
Proof.
  intros c' j. rewrite cs_r. destruct (Nat.eqb_spec c' c); simpl; [subst|repeat split; reflexivity].
  unfold upd. repeat split; reflexivity.
Qed.

Lemma rg_r_old : forall c' j, oc (cs s c') j <> None -> rg (cs s' c') j = rg (cs s c') j.
Proof.
  intros c' j X. rewrite (proj1 (field_r c' j)). destruct (Nat.eqb_spec c' c), (Nat.eqb_spec j k); simpl; auto.
  subst. congruence.
Qed.

Lemma Inv1_read : Inv1 p s'.
Proof.
  assert (ENT := ent_r). assert (OC := oc_r).
  assert (RG : forall c' j, rg (cs s' c') j = (if Nat.eqb c' c && Nat.eqb j k then vd bv a else rg (cs s c') j))
    by (intros; apply field_r).
  assert (AI : forall c' j, ai (cs s' c') j = (if Nat.eqb c' c && Nat.eqb j k then crd Plain xs else ai (cs s c') j))
    by (intros; apply field_r).
  assert (RW : forall c' j, rw (cs s' c') j = (if Nat.eqb c' c && Nat.eqb j k then wrote (tm s) (icells i) u w else rw (cs s c') j))
    by (intros; apply field_r).
  assert (OH : forall c' j, oh (cs s' c') j = (if Nat.eqb c' c && Nat.eqb j k then Some (tm s) else oh (cs s c') j))
    by (intros; apply field_r).
  assert (PCS : pcs s' = pcs s) by reflexivity.
  assert (ROLD := rg_r_old).
  assert (RS : forall c' j, j < pcs s c' \/ oc (cs s c') j <> None -> rg (cs s' c') j = rg (cs s c') j).
  { intros c' j X. rewrite RG. destruct (Nat.eqb_spec c' c), (Nat.eqb_spec j k); simpl; auto.
    subst. destruct X; [lia|congruence]. }
  assert (STL : forall c' r, settled (cs s' c') (pcs s' c') r -> settled (cs s c') (pcs s c') r).
  { intros c' r Hr j X. rewrite <- (RS c' j X). apply Hr. rewrite PCS, OC. exact X. }
  assert (SET : forall c' j, j < pcs s c' ->
    ins p c' j (rg (cs s' c')) = ins p c' j (rg (cs s c')) /\
    ieval (ins p c' j (rg (cs s c'))) (rg (cs s' c')) = ieval (ins p c' j (rg (cs s c'))) (rg (cs s c'))).
  { intros c' j H. apply (set_stable p s c' j); auto. intros j' X. apply RS. exact X. }
  assert (EXS : forall c' j, j < pcs s c' ->
    executes (ins p c' j (rg (cs s' c'))) (rg (cs s' c')) = executes (ins p c' j (rg (cs s c'))) (rg (cs s c'))).
  { intros c' j H. destruct (SET c' j H) as [E1 E2]. rewrite E1. unfold executes, icond. rewrite E2. reflexivity. }
  assert (XXS : forall c' j, j < pcs s c' ->
    xex (cs s' c') (ins p c' j (rg (cs s' c'))) (rg (cs s' c')) j = xex (cs s c') (ins p c' j (rg (cs s c'))) (rg (cs s c')) j).
  { intros c' j H. destruct (SET c' j H) as [E1 E2]. rewrite E1. apply xex_eval; [|exact E2|apply RS; left; exact H].
    rewrite OH. destruct (Nat.eqb_spec c' c), (Nat.eqb_spec j k); simpl; auto. subst. lia. }
  assert (AOLD : forall c' j, (c' <> c \/ j <> k) -> ai (cs s' c') j = ai (cs s c') j).
  { intros c' j N. rewrite AI. destruct (Nat.eqb_spec c' c), (Nat.eqb_spec j k); simpl; auto. destruct N; congruence. }
  assert (PEND : forall c' pc k' d', pending (cs s' c') pc k' d' <-> pending (cs s c') pc k' d').
  { intros c' pc k' d'. unfold pending. rewrite OC. split; intros (P1 & P2 & P3); repeat split; auto;
      (rewrite AOLD in P3 || rewrite AOLD); auto; (destruct (Nat.eq_dec c' c); [right; intros ->; subst; congruence|left; auto]). }
  assert (NOOLD : forall t e, ent s t = Some e -> ec e = c -> ek e <> k).
  { intros t e H E1 E2. destruct (i_et p s I t e H) as (_ & E). rewrite E1, E2 in E. destruct (eh e); congruence. }
  assert (TMO : forall c' j, (c' <> c \/ j <> k) -> tmo (cs s' c') j = tmo (cs s c') j).
  { intros c' j Nj. unfold tmo. rewrite OC, OH. destruct (Nat.eqb_spec c' c), (Nat.eqb_spec j k); simpl; auto.
    destruct Nj; congruence. }
  assert (TMOp : forall c' j, j < pcs s c' -> tmo (cs s' c') j = tmo (cs s c') j).
  { intros c' j L. apply TMO. destruct (Nat.eq_dec c' c) as [->|Nc]; [right; lia|left; exact Nc]. }
  constructor.
  - unfold sread; simpl. rewrite length_app, (i_tm p s I). simpl. lia.
  - intros t e H. rewrite ENT in H. destruct (Nat.ltb_spec t (tm s)).
    + destruct (i_et p s I t e H) as (E1 & E2). split; auto. destruct (eh e).
      * rewrite OH. destruct (Nat.eqb_spec (ec e) c), (Nat.eqb_spec (ek e) k); simpl; auto.
        exfalso. apply (NOOLD t e H); auto.
      * rewrite OC. exact E2.
    + destruct (Nat.eqb_spec t (tm s)); [|discriminate]. injection H as <-. subst. cbn [et ec ek eh].
      rewrite OH, !Nat.eqb_refl. split; reflexivity.
  - intros c' j t H. rewrite OC in H. rewrite ENT. pose proof (oc_lt_tm p s c' j t I H) as L.
    apply Nat.ltb_lt in L. rewrite L. apply (i_oc p s I _ _ _ H).
  - intros c' j t H. rewrite OH in H. rewrite ENT.
    destruct (Nat.eqb_spec c' c), (Nat.eqb_spec j k); simpl in H.
    + subst. injection H as <-. rewrite Nat.ltb_irrefl, Nat.eqb_refl. eexists; repeat split; reflexivity.
    + pose proof (oh_lt_tm p s c' j t I H) as L. apply Nat.ltb_lt in L. rewrite L. apply (i_oh p s I _ _ _ H).
    + pose proof (oh_lt_tm p s c' j t I H) as L. apply Nat.ltb_lt in L. rewrite L. apply (i_oh p s I _ _ _ H).
    + pose proof (oh_lt_tm p s c' j t I H) as L. apply Nat.ltb_lt in L. rewrite L. apply (i_oh p s I _ _ _ H).
  - intros c' j H H'. rewrite OC in H. rewrite OH in H'. rewrite RG.
    destruct (Nat.eqb_spec c' c), (Nat.eqb_spec j k); simpl in *; try discriminate; apply (i_rg0 p s I); auto.
  - intros c' j t H. rewrite OC, OH in H. rewrite ENT, RW, AI.
    destruct (Nat.eqb_spec c' c), (Nat.eqb_spec j k); simpl in *.
    + subst. destruct H as [H|[_ H]]; [congruence|]. injection H as <-. rewrite Nat.ltb_irrefl, Nat.eqb_refl.
      eexists; split; reflexivity.
    + assert (L : t < tm s) by (destruct H as [H|[_ H]]; [apply (oc_lt_tm p s c' j t I H)|apply (oh_lt_tm p s c' j t I H)]).
      apply Nat.ltb_lt in L. rewrite L. apply (i_rw p s I _ _ _ H).
    + assert (L : t < tm s) by (destruct H as [H|[_ H]]; [apply (oc_lt_tm p s c' j t I H)|apply (oh_lt_tm p s c' j t I H)]).
      apply Nat.ltb_lt in L. rewrite L. apply (i_rw p s I _ _ _ H).
    + assert (L : t < tm s) by (destruct H as [H|[_ H]]; [apply (oc_lt_tm p s c' j t I H)|apply (oh_lt_tm p s c' j t I H)]).
      apply Nat.ltb_lt in L. rewrite L. apply (i_rw p s I _ _ _ H).
  - intros c' j t H H' L. rewrite OC in H. rewrite OH in H'. rewrite PCS in L |- *. rewrite AI.
    destruct (Nat.eqb_spec c' c), (Nat.eqb_spec j k); simpl in *.
    + subst. split; [auto|]. split; [eauto|]. apply (earlyR_len _ _ _ _ _ _ _ _ _ _ Hok).
    + apply (i_half p s I c' j t H H' L).
    + apply (i_half p s I c' j t H H' L).
    + apply (i_half p s I c' j t H H' L).
  - intros c' j t H H' L. rewrite OC in H. rewrite OH in H'. rewrite PCS in L. rewrite AI.
    destruct (Nat.eqb_spec c' c), (Nat.eqb_spec j k); simpl in *.
    + subst. lia.
    + rewrite (cfail_passed p s c' j _ I L (fun j0 X => RS c' j0 X)). apply (i_halfp p s I c' j t H H' L).
    + rewrite (cfail_passed p s c' j _ I L (fun j0 X => RS c' j0 X)). apply (i_halfp p s I c' j t H H' L).
    + rewrite (cfail_passed p s c' j _ I L (fun j0 X => RS c' j0 X)). apply (i_halfp p s I c' j t H H' L).
  - intros c' j t1 t2 H H'. rewrite OH in H. rewrite OC in H'. rewrite AI.
    destruct (Nat.eqb_spec c' c), (Nat.eqb_spec j k); simpl in *; try (subst; congruence);
      apply (i_hoc p s I c' j t1 t2 H H').
  - intros t e H r Hr. rewrite ENT in H. destruct (Nat.ltb_spec t (tm s)).
    + assert (Nk : ec e <> c \/ ek e <> k) by (destruct (Nat.eq_dec (ec e) c); [right; apply (NOOLD t e H); auto|left; auto]).
      rewrite (AOLD _ _ Nk).
      rewrite (i_det p s I t e H r (STL _ r Hr)).
      pose proof (i_det p s I t e H (rg (cs s' (ec e)))) as D. rewrite D; [reflexivity|].
      intros j X. apply RS. exact X.
    + destruct (Nat.eqb_spec t (tm s)); [|discriminate]. injection H as <-. cbn [ec ek] in *.
      rewrite AI, !Nat.eqb_refl. reflexivity.
  - intros c' j H Ex. rewrite PCS in H. rewrite OC. rewrite (XXS c' j H) in Ex. apply (i_pc p s I c' j H Ex).
  - intros c' k' H X. rewrite PCS in H. rewrite OC in X.
    rewrite AOLD by (destruct (Nat.eq_dec c' c); [right; intros ->; subst; congruence|left; auto]).
    apply (i_pend p s I); auto.
  - intros c' k' tk d' j P X Lj Ex T. rewrite PCS in P, Lj. rewrite PEND in P. rewrite OC in X.
    rewrite (proj1 (SET c' j Lj)) in T. rewrite (XXS c' j Lj) in Ex.
    destruct (i_ptie p s I c' k' tk d' j P X Lj Ex T) as (tj & A1 & A2). exists tj. rewrite OC. auto.
  - intros c' j k2 tk Ljk Lk X Ex T. rewrite PCS in Lk. rewrite OC in X.
    assert (Lj : j < pcs s c') by lia.
    rewrite (proj1 (SET c' j Lj)), (proj1 (SET c' k2 Lk)) in T. rewrite (XXS c' j Lj) in Ex.
    destruct (i_po p s I c' j k2 tk Ljk Lk X Ex T) as (tj & A1 & A2). exists tj. rewrite OC. auto.
  - intros c' j Hj. unfold sread in Hj; simpl in Hj. rewrite OC, OH. unfold upd in Hj.
    destruct (Nat.eqb_spec c' c), (Nat.eqb_spec j k); simpl.
    + lia.
    + subst. apply (i_tp p s I). lia.
    + apply (i_tp p s I). auto.
    + apply (i_tp p s I). auto.
  - intros c' j. rewrite PCS. apply (i_cmA p s I c' j).
  - intros. apply (i_cmB p s I n1 n2 c0 j1 j2 t1 t2); auto.
  - intros. apply (i_cmC p s I n1 n2 c1 c2 j1 j2 t1 t2); auto.
  - intros c' j tau H j' Hj' Ex.
    assert (Lj : j < pcs s c') by (apply (i_cmA p s I c' j); eauto).
    rewrite (XXS c' j' ltac:(lia)) in Ex. destruct (i_cmD p s I c' j tau H j' Hj' Ex) as (t' & X & Y). rewrite OC. eauto.
  - intros c' j tau H. apply (i_cmE p s I) in H. simpl. lia.
  - intros c' j tau H.
    assert (Lj : j < pcs s c') by (apply (i_cmA p s I c' j); eauto).
    destruct (i_set p s I c' j tau H) as (S1 & S2). split.
    + intros r Hr. rewrite (proj1 (SET c' j Lj)), (proj2 (SET c' j Lj)).
      apply S1. intros j' [L|(t' & X & Lt)].
      * rewrite (Hr j' (or_introl L)). apply RS. left. lia.
      * rewrite (Hr j' (or_intror (ex_intro _ t' (conj (eq_trans (f_equal (fun f => f j') (OC c')) X) Lt)))). apply RS. right. congruence.
    + rewrite AOLD by (destruct (Nat.eq_dec c' c); [right; subst; lia|left; auto]). rewrite (proj1 (SET c' j Lj)). exact S2.
  - intros c' j tau H Ex D. rewrite OC.
    assert (Lj : j < pcs s c') by (apply (i_cmA p s I c' j); eauto).
    apply (i_cmF p s I c' j tau H); [rewrite <- (EXS c' j Lj); exact Ex|]. rewrite <- D. destruct (SET c' j Lj) as [E1 E2]. rewrite E1.
    destruct (ins p c' j (rg (cs s c'))) as [| | |[]|]; simpl in *; auto; injection E2; intros;
    repeat match goal with Hx : _ = _ |- _ => rewrite Hx end; reflexivity.
  - intros c'. rewrite PCS. unfold sread; simpl. unfold upd. pose proof (i_pctp p s I c').
    destruct (Nat.eqb_spec c' c); [subst|]; lia.
  - intros c' k' tk d' j P X Lj Ex T. rewrite PCS in P, Lj. rewrite PEND in P. rewrite OC in X.
    rewrite (proj1 (SET c' j Lj)) in T. rewrite (EXS c' j Lj) in Ex. rewrite (TMOp c' j Lj).
    apply (i_ptiet p s I c' k' tk d' j P X Lj Ex T).
  - intros c' k' tk m0 xs0 j P X Lj Ex T. rewrite PCS in Lj. rewrite (proj1 (SET c' j Lj)) in T.
    rewrite (EXS c' j Lj) in Ex. rewrite (TMOp c' j Lj).
    destruct (Nat.eq_dec c' c) as [->|Nc]; [destruct (Nat.eq_dec k' k) as [->|Nk]|].
    + rewrite OH, !Nat.eqb_refl in X. simpl in X. injection X as <-. apply (tmo_passed p s c j I Lj Ex).
    + destruct P as (P1 & P2 & P3). rewrite PCS in P1. rewrite OH in P2, X. rewrite AI in P3.
      rewrite Nat.eqb_refl, (proj2 (Nat.eqb_neq k' k) Nk) in P2, X, P3. simpl in P2, X, P3.
      apply (i_ptieh p s I c k' tk m0 xs0 j); auto. split; [exact P1|split; [exact P2|exact P3]].
    + destruct P as (P1 & P2 & P3). rewrite PCS in P1. rewrite OH in P2, X. rewrite AI in P3.
      rewrite (proj2 (Nat.eqb_neq c' c) Nc) in P2, X, P3. simpl in P2, X, P3.
      apply (i_ptieh p s I c' k' tk m0 xs0 j); auto. split; [exact P1|split; [exact P2|exact P3]].
  - intros c' j k2 tk Ljk Lk X Ex T. rewrite PCS in Lk. assert (Lj : j < pcs s c') by lia.
    rewrite (TMOp c' k2 Lk) in X. rewrite (TMOp c' j Lj).
    rewrite (proj1 (SET c' j Lj)), (proj1 (SET c' k2 Lk)) in T. rewrite (EXS c' j Lj) in Ex.
    apply (i_pot p s I c' j k2 tk Ljk Lk X Ex T).
  - intros c' j tau H j' Hj' Ex.
    assert (Lj : j < pcs s c') by (apply (i_cmA p s I c' j); eauto).
    rewrite (EXS c' j' ltac:(lia)) in Ex. rewrite (TMOp c' j' ltac:(lia)). apply (i_cmDt p s I c' j tau H j' Hj' Ex).
  - intros c' j t1 t2 H H'. rewrite OC in H'. rewrite OH in H.
    destruct (Nat.eqb_spec c' c), (Nat.eqb_spec j k); simpl in H.
    + subst. congruence.
    + rewrite AOLD by (right; auto). rewrite (cfail_keep p s c' j _ I ltac:(congruence) (fun j0 X => RS c' j0 X)).
      apply (i_hocf p s I c' j t1 t2 H H').
    + rewrite AOLD by (left; auto). rewrite (cfail_keep p s c' j _ I ltac:(congruence) (fun j0 X => RS c' j0 X)).
      apply (i_hocf p s I c' j t1 t2 H H').
    + rewrite AOLD by (left; auto). rewrite (cfail_keep p s c' j _ I ltac:(congruence) (fun j0 X => RS c' j0 X)).
      apply (i_hocf p s I c' j t1 t2 H H').
  - intros c' j t H H' L. rewrite OC in H. rewrite PCS in L. rewrite (RS c' j (or_introl L)).
    rewrite OH in H'. destruct (Nat.eqb_spec c' c), (Nat.eqb_spec j k); simpl in H'; [subst; lia| | |];
      apply (i_halfv p s I c' j t H H' L).
Qed.

End Read.

(* ---------- passing a non-executing instruction ---------- *)
Section Skip.
Variables (p : prog) (s : st) (c : nat).
Hypothesis I : Inv1 p s.
Local Abbreviation cc := (cs s c).
Local Abbreviation k := (pcs s c).
Hypothesis Hx : xex cc (ins p c k (rg cc)) (rg cc) k = false.
Hypothesis Ho : oc cc k = None.
Hypothesis Hh : oh cc k <> None -> eofR (ins p c k (rg cc)) (rg cc) = eofR (ai cc k) (rg cc).
Hypothesis Hvk : oh cc k <> None -> vok (rg cc k) = false.
Hypothesis Hd : determined p cc c k (ins p c k (rg cc)).
Hypothesis Hf : hfirst cc k (ins p c k (rg cc)).
Local Abbreviation s' := (sskip p s c).

Lemma pcs_skip : forall c', pcs s' c' = if Nat.eqb c' c then S k else pcs s c'.
Proof. intros c'. reflexivity. Qed.

Lemma oc_skip : forall c', oc (cs s' c') = oc (cs s c').
Proof. intros c'. unfold sskip; simpl. unfold upd at 1. destruct (Nat.eqb_spec c' c); subst; reflexivity. Qed.

Lemma rg_skip : forall c', rg (cs s' c') = rg (cs s c').
Proof. intros c'. unfold sskip; simpl. unfold upd at 1. destruct (Nat.eqb_spec c' c); subst; reflexivity. Qed.

Lemma rw_skip : forall c', rw (cs s' c') = rw (cs s c').
Proof. intros c'. unfold sskip; simpl. unfold upd at 1. destruct (Nat.eqb_spec c' c); subst; reflexivity. Qed.

Lemma rv_skip : forall c', rv (cs s' c') = rv (cs s c').
Proof. intros c'. unfold sskip; simpl. unfold upd at 1. destruct (Nat.eqb_spec c' c); subst; reflexivity. Qed.

Lemma oh_skip : forall c', oh (cs s' c') = oh (cs s c').
Proof. intros c'. unfold sskip; simpl. unfold upd at 1. destruct (Nat.eqb_spec c' c); subst; reflexivity. Qed.

Lemma ai_skip : forall c' j, ai (cs s' c') j =
  if Nat.eqb c' c && Nat.eqb j k then ins p c k (rg cc) else ai (cs s c') j.
Proof.
  intros c' j. unfold sskip; simpl. unfold upd at 1. destruct (Nat.eqb_spec c' c); subst; simpl; auto.
Qed.

Lemma ai_skip_old : forall c' j, c' <> c \/ j <> k -> ai (cs s' c') j = ai (cs s c') j.
Proof.
  intros c' j H. rewrite ai_skip. destruct (Nat.eqb_spec c' c), (Nat.eqb_spec j k); simpl; auto.
  destruct H; congruence.
Qed.

(* a slot that happened is not the one passed *)
Lemma skip_other : forall c' j, oc (cs s c') j <> None -> c' <> c \/ j <> k.
Proof. intros c' j X; (destruct (Nat.eq_dec c' c); [right; intros ->; subst; congruence|left; auto]). Qed.

(* the slot passed: an instruction that does not execute, or a CAS whose read
   happened alone and whose comparison fails *)
Lemma skip_cases : (oh cc k = None /\ executes (ins p c k (rg cc)) (rg cc) = false) \/
  (exists t xs, oh cc k = Some t /\ ai cc k = crd Plain xs /\ eofR (ins p c k (rg cc)) (rg cc) = Some (Plain, xs) /\
     cfail (ins p c k (rg cc)) (rg cc) k = true /\ c < length p).
Proof.
  destruct (oh cc k) as [t|] eqn:O.
  - right. destruct (i_half p s I c k t Ho O (le_n _)) as (_ & (xs & A) & Lc).
    assert (E : eofR (ins p c k (rg cc)) (rg cc) = Some (Plain, xs)) by (rewrite (Hh ltac:(congruence)), A; reflexivity).
    exists t, xs. repeat split; auto.
    destruct (xex_false _ _ _ _ Hx) as [X|(_ & F)]; auto. exfalso.
    destruct (ins p c k (rg cc)) as [| |m0 x0 c0 e0 n0| |]; simpl in E; try discriminate.
    unfold executes, icond in X; simpl in X. rewrite X in E. discriminate.
  - left. split; auto. destruct (xex_false _ _ _ _ Hx) as [X|(N & _)]; auto. exfalso. apply N. exact O.
Qed.

Lemma eofR_cells : forall i r m xs, eofR i r = Some (m, xs) -> icells i = dd xs /\ casx i = Some (m, xs).
Proof.
  intros i r m xs H. destruct i as [| |m0 x0 c0 e0 n0| |]; simpl in H; try discriminate.
  destruct (c0 r); [injection H as <- <-|discriminate]. split; reflexivity.
Qed.

Lemma Inv1_skip : Inv1 p s'.
Proof.
  assert (STL : forall c' r, settled (cs s' c') (pcs s' c') r -> settled (cs s c') (pcs s c') r).
  { intros c' r Hr j X. rewrite <- (rg_skip c'). apply Hr. rewrite pcs_skip, oc_skip.
    destruct (Nat.eqb_spec c' c); [subst|]; destruct X; auto; left; lia. }
  assert (EXk : forall j, j < S k -> xex cc (ins p c j (rg cc)) (rg cc) j = true -> j < k).
  { intros j L E. destruct (Nat.eq_dec j k); [subst; congruence|lia]. }
  assert (XO : forall c', xex (cs s' c') = xex (cs s c')).
  { intros c'. unfold xex, ohb. rewrite oh_skip. reflexivity. }
  assert (TMOs : forall c' j, tmo (cs s' c') j = tmo (cs s c') j).
  { intros c' j. unfold tmo. rewrite oc_skip, oh_skip. reflexivity. }
  (* the slot passed, if it executes: a CAS that failed, its read before it *)
  assert (SKX : executes (ins p c k (rg cc)) (rg cc) = true ->
     exists t0 xs1, oh cc k = Some t0 /\ tmo cc k = Some t0 /\ ai cc k = crd Plain xs1 /\
       eofR (ins p c k (rg cc)) (rg cc) = Some (Plain, xs1) /\ hpending cc k k Plain xs1).
  { intros E. destruct skip_cases as [(_ & Z)|(t0 & xs1 & Z & A & Er & _ & _)]; [congruence|].
    exists t0, xs1. split; [exact Z|]. split; [unfold tmo; rewrite Ho; exact Z|]. split; [exact A|]. split; [exact Er|].
    split; [lia|split; [congruence|rewrite A; reflexivity]]. }
  constructor; try rewrite !oc_skip; try rewrite !rg_skip.
  - apply (i_tm p s I).
  - intros t e H. rewrite oc_skip, oh_skip. apply (i_et p s I t e H).
  - intros c' j t H. rewrite oc_skip in H. apply (i_oc p s I c' j t H).
  - intros c' j t H. rewrite oh_skip in H. apply (i_oh p s I c' j t H).
  - intros c' j H H'. rewrite oc_skip in H. rewrite oh_skip in H'. rewrite rg_skip. apply (i_rg0 p s I c' j H H').
  - intros c' j t H. rewrite oc_skip, oh_skip in H. rewrite rw_skip.
    destruct (Nat.eq_dec c' c) as [->|N]; [destruct (Nat.eq_dec j k) as [->|N]|].
    + destruct H as [H|(_ & H)]; [congruence|].
      destruct skip_cases as [(Z & _)|(t0 & xs & Z & A & E & _ & _)]; [congruence|].
      rewrite ai_skip, !Nat.eqb_refl. simpl. rewrite (proj1 (eofR_cells _ _ _ _ E)).
      destruct (i_rw p s I c k t (or_intror (conj Ho H))) as (e & He & R). rewrite A in R. exists e. split; auto.
    + rewrite ai_skip_old by auto. apply (i_rw p s I c j t H).
    + rewrite ai_skip_old by auto. apply (i_rw p s I c' j t H).
  - intros c' j t H H' L. rewrite oc_skip in H. rewrite oh_skip in H'. rewrite pcs_skip in L |- *.
    destruct (Nat.eqb_spec c' c).
    + subst. assert (j <> k) by lia. rewrite ai_skip_old by auto.
      destruct (i_half p s I c j t H H' ltac:(lia)) as (L' & A & Lc). split; [lia|auto].
    + rewrite ai_skip_old by auto. apply (i_half p s I c' j t H H' L).
  - intros c' j t H H' L. rewrite oc_skip in H. rewrite oh_skip in H'. rewrite pcs_skip in L. rewrite rg_skip.
    destruct (Nat.eqb_spec c' c).
    + subst. destruct (Nat.eq_dec j k) as [->|N].
      * rewrite ai_skip, !Nat.eqb_refl. simpl.
        destruct skip_cases as [(Z & _)|(t0 & xs & Z & A & E & F & Lc)]; [congruence|].
        split; [exact F|]. split; [|exact Lc]. exists xs. apply (eofR_cells _ _ _ _ E).
      * rewrite ai_skip_old by auto. apply (i_halfp p s I c j t H H'). lia.
    + rewrite ai_skip_old by auto. apply (i_halfp p s I c' j t H H' L).
  - intros c' j t1 t2 H H'. rewrite oh_skip in H. rewrite oc_skip in H'.
    rewrite ai_skip_old by (apply skip_other; congruence). apply (i_hoc p s I c' j t1 t2 H H').
  - intros t e H r Hr. apply STL in Hr. rewrite rg_skip.
    destruct (Nat.eq_dec (ec e) c) as [Ec|Ec]; [destruct (Nat.eq_dec (ek e) k) as [Ek|Ek]|].
    + rewrite Ec, Ek in *. rewrite ai_skip, !Nat.eqb_refl. simpl. apply (proj2 (Hd r Hr)).
    + rewrite ai_skip_old by auto. apply (i_det p s I t e H r Hr).
    + rewrite ai_skip_old by auto. apply (i_det p s I t e H r Hr).
  - intros c' j H Ex. rewrite pcs_skip in H. rewrite rg_skip, XO in Ex. rewrite oc_skip. destruct (Nat.eqb_spec c' c).
    + subst. apply (i_pc p s I); [apply EXk; auto|exact Ex].
    + apply (i_pc p s I); auto.
  - intros c' k' H X. rewrite pcs_skip in H. rewrite oc_skip in X.
    rewrite ai_skip_old by (apply skip_other; exact X).
    apply (i_pend p s I); auto. destruct (Nat.eqb_spec c' c); [subst|]; lia.
  - intros c' k' tk d j P X Lj Ex T. rewrite oc_skip in X. rewrite rg_skip in Ex, T. rewrite XO in Ex.
    assert (P' : pending (cs s c') (pcs s c') k' d).
    { destruct P as (P1 & P2 & P3). rewrite oc_skip in P2. rewrite pcs_skip in P1.
      rewrite ai_skip_old in P3 by (apply skip_other; exact P2).
      unfold pending. repeat split; auto. destruct (Nat.eqb_spec c' c); [subst|]; lia. }
    rewrite pcs_skip in Lj.
    enough (exists tj, oc (cs s c') j = Some tj /\ tj < tk) as (tj & A1 & A2) by (exists tj; rewrite oc_skip; auto).
    destruct (Nat.eqb_spec c' c).
    + subst c'. apply (i_ptie p s I c k' tk d j P' X); auto.
    + apply (i_ptie p s I c' k' tk d j P' X); auto.
  - intros c' j k2 tk Ljk Lk X Ex T. rewrite pcs_skip in Lk. rewrite oc_skip in X. rewrite rg_skip in Ex, T. rewrite XO in Ex.
    enough (exists tj, oc (cs s c') j = Some tj /\ tj < tk) as (tj & A1 & A2) by (exists tj; rewrite oc_skip; auto).
    destruct (Nat.eqb_spec c' c).
    + subst c'. assert (k2 <> k) by (intros ->; congruence). apply (i_po p s I c j k2 tk); auto. lia.
    + apply (i_po p s I c' j k2 tk); auto.
  - intros c' j Hj. rewrite oc_skip, oh_skip. apply (i_tp p s I c' j).
    unfold sskip in Hj; simpl in Hj. unfold upd in Hj. destruct (Nat.eqb_spec c' c); [subst|]; lia.
  - intros c' j. rewrite pcs_skip. unfold sskip; cbn [cm]. setoid_rewrite in_app_iff. simpl.
    destruct (Nat.eqb_spec c' c).
    + subst c'. split.
      * intros Hj. destruct (Nat.lt_ge_cases j k).
        -- destruct (proj1 (i_cmA p s I c j) H) as (tau & Ht). eauto.
        -- exists (tm s). right. left. f_equal. f_equal. lia.
      * intros (tau & [Ht|[E|[]]]).
        -- assert (j < k) by (apply (i_cmA p s I c j); eauto). lia.
        -- injection E as E1 E2. lia.
    + rewrite (i_cmA p s I c' j). split.
      * intros (tau & Ht); eauto.
      * intros (tau & [Ht|[E|[]]]); eauto. injection E as E; congruence.
  - intros n1 n2 c' j1 j2 t1 t2 Hn H1 H2. unfold sskip in H1, H2; cbn [cm] in H1, H2.
    rewrite nth_error_app_last in H1, H2.
    destruct (Nat.ltb_spec n1 (length (cm s))), (Nat.ltb_spec n2 (length (cm s))).
    + exact (i_cmB p s I n1 n2 c' j1 j2 t1 t2 Hn H1 H2).
    + destruct (Nat.eqb_spec n2 (length (cm s))); [|discriminate]. injection H2 as E1 E2 E3. subst c' j2 t2.
      assert (j1 < pcs s c) by (apply (i_cmA p s I c j1); eauto using nth_error_In). lia.
    + lia.
    + destruct (Nat.eqb_spec n1 (length (cm s))), (Nat.eqb_spec n2 (length (cm s))); try discriminate; lia.
  - intros n1 n2 c1 c2 j1 j2 t1 t2 Hn H1 H2. unfold sskip in H1, H2; cbn [cm] in H1, H2.
    rewrite nth_error_app_last in H1, H2.
    destruct (Nat.ltb_spec n1 (length (cm s))), (Nat.ltb_spec n2 (length (cm s))).
    + exact (i_cmC p s I n1 n2 c1 c2 j1 j2 t1 t2 Hn H1 H2).
    + destruct (Nat.eqb_spec n2 (length (cm s))); [|discriminate]. injection H2 as E1 E2 E3. subst c2 j2 t2.
      apply nth_error_In in H1. apply (i_cmE p s I) in H1. lia.
    + lia.
    + destruct (Nat.eqb_spec n1 (length (cm s))), (Nat.eqb_spec n2 (length (cm s))); try discriminate; lia.
  - intros c' j tau H j' Hj' Ex. rewrite oc_skip. rewrite rg_skip, XO in Ex. unfold sskip in H; cbn [cm] in H.
    apply in_app_iff in H. destruct H as [H|[E|[]]].
    + apply (i_cmD p s I c' j tau H j' Hj' Ex).
    + injection E as E1 E2 E3. subst c' j tau. assert (Lj : j' < k) by (apply EXk; [lia|exact Ex]).
      destruct (oc cc j') as [t'|] eqn:X.
      * exists t'. split; auto. pose proof (oc_lt_tm p s c j' t' I X). lia.
      * exfalso. apply (i_pc p s I c j' Lj Ex X).
  - intros c' j tau H. unfold sskip in H; cbn [cm] in H. apply in_app_iff in H. simpl.
    destruct H as [H|[E|[]]].
    + apply (i_cmE p s I) in H. auto.
    + injection E as E1 E2 E3. subst. lia.
  - intros c' j tau H. rewrite oc_skip, rg_skip. unfold sskip in H; cbn [cm] in H. apply in_app_iff in H.
    destruct H as [H|[E|[]]].
    + assert (Lj : j < pcs s c') by (apply (i_cmA p s I c' j); eauto).
      rewrite ai_skip_old by (destruct (Nat.eq_dec c' c); [right; subst; lia|left; auto]).
      apply (i_set p s I c' j tau H).
    + injection E as E1 E2 E3. subst c' j tau. split.
      * intros r Hr. apply Hd. intros j' [L|X]; [apply Hr; left; exact L|].
        destruct (oc cc j') as [t'|] eqn:Y; [|congruence].
        apply Hr. right. exists t'. split; [exact Y|apply (oc_lt_tm p s c j' t' I Y)].
      * rewrite ai_skip, !Nat.eqb_refl. reflexivity.
  - intros c' j tau H Ex D. rewrite oc_skip. rewrite rg_skip in D, Ex. unfold sskip in H; cbn [cm] in H.
    apply in_app_iff in H. destruct H as [H|[E|[]]].
    + apply (i_cmF p s I c' j tau H Ex D).
    + injection E as E1 E2 E3. subst c' j tau. exfalso.
      destruct skip_cases as [(_ & Z)|(t0 & xs & _ & _ & E & _ & _)]; [congruence|].
      destruct (ins p c k (rg cc)) as [| |m0 x0 c0 e0 n0| |]; simpl in E, D; try discriminate.
      destruct (c0 (rg cc)); discriminate.
  - intros c'. rewrite pcs_skip. unfold sskip; simpl. unfold upd. pose proof (i_pctp p s I c').
    destruct (Nat.eqb_spec c' c); [subst|]; lia.
  - intros c' k' tk d j P X Lj Ex T. rewrite oc_skip in X. rewrite rg_skip in Ex, T. rewrite TMOs.
    assert (P' : pending (cs s c') (pcs s c') k' d).
    { destruct P as (P1 & P2 & P3). rewrite oc_skip in P2. rewrite pcs_skip in P1.
      rewrite ai_skip_old in P3 by (apply skip_other; exact P2).
      unfold pending. repeat split; auto. destruct (Nat.eqb_spec c' c); [subst|]; lia. }
    rewrite pcs_skip in Lj. destruct (Nat.eqb_spec c' c).
    + subst c'. destruct (Nat.eq_dec j k) as [->|Nj].
      * destruct (SKX Ex) as (t0 & xs1 & Z & Tm & _ & _ & _). exists t0. split; [exact Tm|].
        assert (Nk : k' <> k) by (intros ->; destruct P' as (_ & P2 & _); congruence).
        apply (proj1 (Hf t0 Z) k' d tk P' Nk X T).
      * apply (i_ptiet p s I c k' tk d j P' X); auto. lia.
    + apply (i_ptiet p s I c' k' tk d j P' X); auto.
  - intros c' k' tk m0 xs0 j P X Lj Ex T. rewrite oh_skip in X. rewrite rg_skip in Ex, T. rewrite TMOs.
    destruct P as (P1 & P2 & P3). rewrite pcs_skip in P1, Lj. rewrite oh_skip in P2.
    destruct (Nat.eqb_spec c' c).
    + subst c'. rewrite ai_skip_old in P3 by (right; lia).
      assert (PO : hpending cc k k' m0 xs0) by (split; [lia|split; auto]).
      destruct (Nat.eq_dec j k) as [->|Nj].
      * destruct (SKX Ex) as (t0 & xs1 & Z & Tm & _ & _ & _). exists t0. split; [exact Tm|].
        apply (proj2 (Hf t0 Z) k' m0 xs0 tk PO ltac:(lia) X T).
      * apply (i_ptieh p s I c k' tk m0 xs0 j PO X); auto. lia.
    + rewrite ai_skip_old in P3 by auto. apply (i_ptieh p s I c' k' tk m0 xs0 j); auto. split; [exact P1|split; [exact P2|exact P3]].
  - intros c' j k2 tk Ljk Lk X Ex T. rewrite pcs_skip in Lk. rewrite TMOs in X |- *. rewrite rg_skip in Ex, T.
    destruct (Nat.eqb_spec c' c).
    + subst c'. destruct (Nat.eq_dec k2 k) as [->|Nk].
      * assert (Ek : executes (ins p c k (rg cc)) (rg cc) = true).
        { assert (Z : oh cc k = Some tk) by (unfold tmo in X; rewrite Ho in X; exact X).
          destruct skip_cases as [(Z' & _)|(t0 & xs1 & _ & _ & Er & _ & _)]; [congruence|].
          destruct (eofR_exec_tied_i _ _ _ _ Er) as [E0 _]. exact E0. }
        destruct (SKX Ek) as (t0 & xs1 & Z & Tm & _ & Er & HP). rewrite Tm in X. injection X as <-.
        apply (proj1 (tied_crd _ _ _ _ _ Er)) in T. apply (i_ptieh p s I c k t0 Plain xs1 j HP Z); auto.
      * apply (i_pot p s I c j k2 tk); auto. lia.
    + apply (i_pot p s I c' j k2 tk); auto.
  - intros c' j tau H j' Hj' Ex. rewrite TMOs. rewrite rg_skip in Ex. unfold sskip in H; cbn [cm] in H.
    apply in_app_iff in H. destruct H as [H|[E|[]]].
    + apply (i_cmDt p s I c' j tau H j' Hj' Ex).
    + injection E as E1 E2 E3. subst c' j tau. destruct (Nat.eq_dec j' k) as [->|Nj].
      * destruct (SKX Ex) as (t0 & xs1 & Z & Tm & _). exists t0. split; [exact Tm|].
        pose proof (oh_lt_tm p s c k t0 I Z). lia.
      * destruct (tmo_passed p s c j' I ltac:(lia) Ex) as (t' & A & B). exists t'. split; [exact A|lia].
  - intros c' j t1 t2 H H'. rewrite oh_skip in H. rewrite oc_skip in H'. rewrite rg_skip.
    rewrite ai_skip_old by (apply skip_other; congruence). apply (i_hocf p s I c' j t1 t2 H H').
  - intros c' j t H H' L. rewrite oc_skip in H. rewrite oh_skip in H'. rewrite pcs_skip in L. rewrite rg_skip.
    destruct (Nat.eqb_spec c' c).
    + subst. destruct (Nat.eq_dec j k) as [->|N]; [apply Hvk; congruence|]. apply (i_halfv p s I c j t H H'). lia.
    + apply (i_halfv p s I c' j t H H' L).
Qed.

End Skip.

(* ---------- a CAS whose read happened alone commits to failure ---------- *)
Section Cfail.
Variables (p : prog) (s : st) (c k : nat).
Hypothesis I : Inv1 p s.
Hypothesis Hp : pcs s c <= k.
Hypothesis Ho : oc (cs s c) k = None.
Hypothesis Hh : oh (cs s c) k <> None.
Local Abbreviation cc := (cs s c).
Local Abbreviation s' := (scfail s c k).

Lemma cs_cf : forall c', cs s' c' = if Nat.eqb c' c then
  mkC (oc cc) (upd (rg cc) k (vd false (vv (rg cc k)))) (ai cc) (rw cc) (rv cc) (bd cc)
      (vP cc) (vA cc) (vR cc) (vO cc) (vOg cc) (oh cc) (fx cc) else cs s c'.
Proof. intros c'. unfold scfail. simpl. unfold upd at 1. reflexivity. Qed.

Ltac cff := let c0 := fresh "c0" in intros c0; rewrite cs_cf; destruct (Nat.eqb_spec c0 c); subst; reflexivity.
Lemma oc_cf : forall c', oc (cs s' c') = oc (cs s c'). Proof. cff. Qed.
Lemma oh_cf : forall c', oh (cs s' c') = oh (cs s c'). Proof. cff. Qed.
Lemma ai_cf : forall c', ai (cs s' c') = ai (cs s c'). Proof. cff. Qed.
Lemma rw_cf : forall c', rw (cs s' c') = rw (cs s c'). Proof. cff. Qed.
Lemma rv_cf : forall c', rv (cs s' c') = rv (cs s c'). Proof. cff. Qed.
Lemma bd_cf : forall c', bd (cs s' c') = bd (cs s c'). Proof. cff. Qed.

Lemma rg_cf : forall c' j, (c' <> c \/ j <> k) -> rg (cs s' c') j = rg (cs s c') j.
Proof.
  intros c' j H. rewrite cs_cf. destruct (Nat.eqb_spec c' c); [subst|reflexivity]. simpl.
  unfold upd. destruct (Nat.eqb_spec j k); [destruct H; congruence|reflexivity].
Qed.

Lemma ent_cf : forall t, ent s' t = ent s t.
Proof. reflexivity. Qed.

(* the new registers are settled for the old state, and conversely *)
Lemma set_cf : forall c' r, settled (cs s' c') (pcs s c') r <-> settled (cs s c') (pcs s c') r.
Proof.
  intros c' r. unfold settled. rewrite oc_cf. split; intros H j X; specialize (H j X);
    (assert (N : c' <> c \/ j <> k) by (destruct (Nat.eq_dec c' c) as [->|N]; [right; intros ->; destruct X; [lia|congruence]|left; exact N]));
    rewrite H; [apply rg_cf; exact N|symmetry; apply rg_cf; exact N].
Qed.

Lemma rg_settled : forall c', settled (cs s c') (pcs s c') (rg (cs s' c')).
Proof. intros c'. apply set_cf. intros j _. reflexivity. Qed.

Lemma ieval_cf : forall t e, ent s t = Some e ->
  ieval (ai (cs s (ec e)) (ek e)) (rg (cs s' (ec e))) = ieval (ai (cs s (ec e)) (ek e)) (rg (cs s (ec e))).
Proof. intros t e E. apply (i_det p s I t e E). apply rg_settled. Qed.

Lemma ieval_slot_cf : forall c' j t, oc (cs s c') j = Some t ->
  ieval (ai (cs s c') j) (rg (cs s' c')) = ieval (ai (cs s c') j) (rg (cs s c')).
Proof.
  intros c' j t O. destruct (i_oc p s I c' j t O) as (e & E & Ec & Ek). rewrite <- Ec, <- Ek. apply (ieval_cf t e E).
Qed.

(* a passed slot: same instruction, same evaluation *)
Lemma ins_cf : forall c' j, j < pcs s c' ->
  ins p c' j (rg (cs s' c')) = ins p c' j (rg (cs s c')) /\
  ieval (ins p c' j (rg (cs s c'))) (rg (cs s' c')) = ieval (ins p c' j (rg (cs s c'))) (rg (cs s c')).
Proof.
  intros c' j L. destruct (proj1 (i_cmA p s I c' j) L) as (tau & T).
  apply (proj1 (i_set p s I c' j tau T)). intros j' X. apply rg_cf.
  destruct (Nat.eq_dec c' c) as [->|N]; [right|left; exact N]. intros ->.
  destruct X as [X|(t' & X & _)]; [lia|congruence].
Qed.

Lemma xex_cf : forall c' j, j < pcs s c' ->
  xex (cs s' c') (ins p c' j (rg (cs s' c'))) (rg (cs s' c')) j = xex (cs s c') (ins p c' j (rg (cs s c'))) (rg (cs s c')) j.
Proof.
  intros c' j L. destruct (ins_cf c' j L) as (E1 & E2). rewrite E1. apply xex_eval; [rewrite oh_cf; reflexivity|exact E2|].
  apply rg_cf. destruct (Nat.eq_dec c' c) as [->|N]; [right; lia|left; exact N].
Qed.

Lemma exec_cf : forall c' j, j < pcs s c' ->
  executes (ins p c' j (rg (cs s' c'))) (rg (cs s' c')) = executes (ins p c' j (rg (cs s c'))) (rg (cs s c')).
Proof. intros c' j L. destruct (ins_cf c' j L) as (E1 & E2). rewrite E1. apply exec_eval. exact E2. Qed.

Lemma tmo_cf : forall c' j, tmo (cs s' c') j = tmo (cs s c') j.
Proof. intros c' j. unfold tmo. rewrite oc_cf, oh_cf. reflexivity. Qed.

Lemma eof_cf : forall c' j, j < pcs s c' ->
  eof (ins p c' j (rg (cs s' c'))) (rg (cs s' c')) = eof (ins p c' j (rg (cs s c'))) (rg (cs s c')).
Proof.
  intros c' j L. destruct (ins_cf c' j L) as (E1 & E2). rewrite E1.
  destruct (ins p c' j (rg (cs s c'))) as [m x c0|m x c0 v|m x c0 e n|[]|]; simpl in *; auto; injection E2; intros;
  repeat match goal with Hx : _ = _ |- _ => rewrite Hx end; reflexivity.
Qed.

Lemma cfail_cf : forall t e, ent s t = Some e ->
  cfail (ai (cs s (ec e)) (ek e)) (rg (cs s' (ec e))) (ek e) = cfail (ai (cs s (ec e)) (ek e)) (rg (cs s (ec e))) (ek e) \/
  (ec e = c /\ ek e = k).
Proof.
  intros t e E. destruct (Nat.eq_dec (ec e) c) as [Ec|N]; [destruct (Nat.eq_dec (ek e) k) as [Ek|Nk]; [right; auto|]|]; left;
    apply cfail_eval; try apply (ieval_cf t e E); apply rg_cf; auto.
Qed.

Lemma Inv1_cfail : Inv1 p s'.
Proof.
  assert (NK : forall c' j, j < pcs s c' \/ oc (cs s c') j <> None -> c' <> c \/ j <> k).
  { intros c' j X. destruct (Nat.eq_dec c' c) as [->|N]; [right|left; exact N]. intros ->. destruct X; [lia|congruence]. }
  assert (LT : forall c' j tau, In (c', j, tau) (cm s) -> j < pcs s c').
  { intros c' j tau T. apply (proj2 (i_cmA p s I c' j)). eauto. }
  constructor; cbn [tm lg cm pcs tp es].
  - exact (i_tm p s I).
  - intros t e E; change (pcs (scfail s c k)) with (pcs s) in *. rewrite oh_cf, oc_cf. exact (i_et p s I t e E).
  - intros c' j t O; change (pcs (scfail s c k)) with (pcs s) in *. rewrite oc_cf in O. exact (i_oc p s I c' j t O).
  - intros c' j t O; change (pcs (scfail s c k)) with (pcs s) in *. rewrite oh_cf in O. exact (i_oh p s I c' j t O).
  - intros c' j O H; change (pcs (scfail s c k)) with (pcs s) in *. rewrite oc_cf in O. rewrite oh_cf in H. rewrite rg_cf; [exact (i_rg0 p s I c' j O H)|].
    destruct (Nat.eq_dec c' c) as [->|N]; [right; intros ->; congruence|left; exact N].
  - intros c' j t X; change (pcs (scfail s c k)) with (pcs s) in *. rewrite oc_cf, oh_cf in X. rewrite rw_cf, ai_cf. exact (i_rw p s I c' j t X).
  - intros c' j t O H L; change (pcs (scfail s c k)) with (pcs s) in *. rewrite oc_cf in O. rewrite oh_cf in H. rewrite ai_cf. exact (i_half p s I c' j t O H L).
  - intros c' j t O H L; change (pcs (scfail s c k)) with (pcs s) in *. rewrite oc_cf in O. rewrite oh_cf in H. rewrite ai_cf.
    destruct (i_halfp p s I c' j t O H L) as (Cf & X & Y). split; [|split; assumption].
    destruct (i_oh p s I c' j t H) as (e & E & <- & <- & _).
    destruct (cfail_cf t e E) as [->|(Ec & Ek)]; [exact Cf|change (pcs s') with (pcs s) in L; rewrite Ec, Ek in L; lia].
  - intros c' j t1 t2 H O; change (pcs (scfail s c k)) with (pcs s) in *. rewrite oh_cf in H. rewrite oc_cf in O. rewrite ai_cf. exact (i_hoc p s I c' j t1 t2 H O).
  - intros t e E r Hr; change (pcs (scfail s c k)) with (pcs s) in *. rewrite ai_cf. apply set_cf in Hr. rewrite (i_det p s I t e E r Hr), (ieval_cf t e E). reflexivity.
  - intros c' j L X; change (pcs (scfail s c k)) with (pcs s) in *. rewrite xex_cf in X by exact L. rewrite oc_cf. exact (i_pc p s I c' j L X).
  - intros c' j L O; change (pcs (scfail s c k)) with (pcs s) in *. rewrite oc_cf in O. rewrite ai_cf. exact (i_pend p s I c' j L O).
  - intros c' k' tk d j P O L X T; change (pcs (scfail s c k)) with (pcs s) in *. unfold pending in P. rewrite oc_cf, ai_cf in P. rewrite oc_cf in O |- *.
    rewrite xex_cf in X by exact L. rewrite (proj1 (ins_cf c' j L)) in T. exact (i_ptie p s I c' k' tk d j P O L X T).
  - intros c' j k' tk L1 L2 O X T; change (pcs (scfail s c k)) with (pcs s) in *. rewrite oc_cf in O |- *. rewrite xex_cf in X by lia.
    rewrite (proj1 (ins_cf c' j ltac:(lia))), (proj1 (ins_cf c' k' L2)) in T. exact (i_po p s I c' j k' tk L1 L2 O X T).
  - intros c' j L; change (pcs (scfail s c k)) with (pcs s) in *. rewrite oc_cf, oh_cf. exact (i_tp p s I c' j L).
  - exact (i_cmA p s I).
  - exact (i_cmB p s I).
  - exact (i_cmC p s I).
  - intros c' j tau T j' L X; change (pcs (scfail s c k)) with (pcs s) in *. pose proof (LT c' j tau T). rewrite xex_cf in X by lia. rewrite oc_cf.
    exact (i_cmD p s I c' j tau T j' L X).
  - exact (i_cmE p s I).
  - intros c' j tau T; change (pcs (scfail s c k)) with (pcs s) in *. pose proof (LT c' j tau T) as L. destruct (i_set p s I c' j tau T) as (A & B).
    destruct (ins_cf c' j L) as (E1 & E2). rewrite ai_cf, E1. split; [|exact B].
    intros r Hr. rewrite E2. apply A. intros j' X. rewrite <- (rg_cf c' j'); [apply Hr; rewrite oc_cf; exact X|].
    apply NK. destruct X as [X|(t' & X & _)]; [left; lia|right; congruence].
  - intros c' j tau T X E; change (pcs (scfail s c k)) with (pcs s) in *. pose proof (LT c' j tau T) as L. rewrite exec_cf in X by exact L. rewrite eof_cf in E by exact L.
    rewrite oc_cf. exact (i_cmF p s I c' j tau T X E).
  - exact (i_pctp p s I).
  - intros c' k' tk d j P O L X T; change (pcs (scfail s c k)) with (pcs s) in *. unfold pending in P. rewrite oc_cf, ai_cf in P. rewrite oc_cf in O. rewrite tmo_cf.
    rewrite exec_cf in X by exact L. rewrite (proj1 (ins_cf c' j L)) in T. exact (i_ptiet p s I c' k' tk d j P O L X T).
  - intros c' k' tk m xs j P O L X T; change (pcs (scfail s c k)) with (pcs s) in *. unfold hpending in P. rewrite oh_cf, ai_cf in P. rewrite oh_cf in O. rewrite tmo_cf.
    rewrite exec_cf in X by exact L. rewrite (proj1 (ins_cf c' j L)) in T. exact (i_ptieh p s I c' k' tk m xs j P O L X T).
  - intros c' j k' tk L1 L2 O X T; change (pcs (scfail s c k)) with (pcs s) in *. rewrite tmo_cf in O |- *. rewrite exec_cf in X by lia.
    rewrite (proj1 (ins_cf c' j ltac:(lia))), (proj1 (ins_cf c' k' L2)) in T. exact (i_pot p s I c' j k' tk L1 L2 O X T).
  - intros c' j tau T j' L X; change (pcs (scfail s c k)) with (pcs s) in *. pose proof (LT c' j tau T). rewrite exec_cf in X by lia. rewrite tmo_cf.
    exact (i_cmDt p s I c' j tau T j' L X).
  - intros c' j t1 t2 H O; change (pcs (scfail s c k)) with (pcs s) in *. rewrite oh_cf in H. rewrite oc_cf in O. rewrite ai_cf.
    destruct (i_oc p s I c' j t2 O) as (e & E & <- & <-).
    destruct (cfail_cf t2 e E) as [->|(Ec & Ek)]; [exact (i_hocf p s I _ _ t1 t2 H O)|rewrite Ec, Ek in O; congruence].
  - intros c' j t H H' L; change (pcs (scfail s c k)) with (pcs s) in *. rewrite oc_cf in H. rewrite oh_cf in H'.
    rewrite rg_cf by (apply NK; left; exact L). exact (i_halfv p s I c' j t H H' L).
Qed.

End Cfail.

Lemma Inv1_es : forall p t e, Inv1 p t -> Inv1 p (set_es t e).
Proof. intros p t e I. destruct I; constructor; auto. Qed.

(* ---------- S3c: a result fixed changes only bd and fx ---------- *)
Section Cfix.
Variables (p : prog) (s : st) (c j : nat) (b : bool) (B : nat -> bool).
Local Abbreviation s' := (scfix0 s c j b B).
Ltac cxx := let c0 := fresh "c0" in intros c0; unfold scfix0; simpl; unfold upd at 1; destruct (Nat.eqb_spec c0 c); [subst; reflexivity|reflexivity].
Lemma oc_cx : forall c', oc (cs s' c') = oc (cs s c'). Proof. cxx. Qed.
Lemma oh_cx : forall c', oh (cs s' c') = oh (cs s c'). Proof. cxx. Qed.
Lemma ai_cx : forall c', ai (cs s' c') = ai (cs s c'). Proof. cxx. Qed.
Lemma rw_cx : forall c', rw (cs s' c') = rw (cs s c'). Proof. cxx. Qed.
Lemma rv_cx : forall c', rv (cs s' c') = rv (cs s c'). Proof. cxx. Qed.
Lemma rg_cx : forall c', rg (cs s' c') = rg (cs s c'). Proof. cxx. Qed.
Lemma vP_cx : forall c', vP (cs s' c') = vP (cs s c'). Proof. cxx. Qed.
Lemma vA_cx : forall c', vA (cs s' c') = vA (cs s c'). Proof. cxx. Qed.
Lemma vR_cx : forall c', vR (cs s' c') = vR (cs s c'). Proof. cxx. Qed.
Lemma vO_cx : forall c', vO (cs s' c') = vO (cs s c'). Proof. cxx. Qed.
Lemma vOg_cx : forall c', vOg (cs s' c') = vOg (cs s c'). Proof. cxx. Qed.
Lemma ent_cx : forall t, ent s' t = ent s t. Proof. reflexivity. Qed.

Lemma Inv1_cfix : Inv1 p s -> Inv1 p s'.
Proof.
  intros I. destruct I; constructor; change (pcs s') with (pcs s) in *; change (tp s') with (tp s) in *;
    change (cm s') with (cm s) in *; change (tm s') with (tm s) in *; change (lg s') with (lg s) in *;
    unfold xex, ohb, pending, hpending, tmo, settled, ent in *; intros;
    rewrite ?oc_cx, ?oh_cx, ?ai_cx, ?rw_cx, ?rg_cx in *; eauto.
Qed.
End Cfix.

(* ---------- S3c: the register side of a fix (sflp) changes one register ---------- *)
Section Flp.
Variables (s : st) (c : nat) (o : option nat) (b : bool).
Local Abbreviation s' := (sflp s c o b).
Ltac flpx := let c0 := fresh "c0" in intros c0; destruct o as [k|]; [destruct b|]; cbn [sflp]; try reflexivity;
  unfold scfail; simpl; unfold upd at 1; destruct (Nat.eqb_spec c0 c); [subst; reflexivity|reflexivity].
Lemma oc_flp : forall c', oc (cs s' c') = oc (cs s c'). Proof. flpx. Qed.
Lemma oh_flp : forall c', oh (cs s' c') = oh (cs s c'). Proof. flpx. Qed.
Lemma ai_flp : forall c', ai (cs s' c') = ai (cs s c'). Proof. flpx. Qed.
Lemma rw_flp : forall c', rw (cs s' c') = rw (cs s c'). Proof. flpx. Qed.
Lemma rv_flp : forall c', rv (cs s' c') = rv (cs s c'). Proof. flpx. Qed.
Lemma bd_flp : forall c', bd (cs s' c') = bd (cs s c'). Proof. flpx. Qed.
Lemma fx_flp : forall c', fx (cs s' c') = fx (cs s c'). Proof. flpx. Qed.
Lemma vP_flp : forall c', vP (cs s' c') = vP (cs s c'). Proof. flpx. Qed.
Lemma vA_flp : forall c', vA (cs s' c') = vA (cs s c'). Proof. flpx. Qed.
Lemma vR_flp : forall c', vR (cs s' c') = vR (cs s c'). Proof. flpx. Qed.
Lemma vO_flp : forall c', vO (cs s' c') = vO (cs s c'). Proof. flpx. Qed.
Lemma vOg_flp : forall c', vOg (cs s' c') = vOg (cs s c'). Proof. flpx. Qed.
Ltac flps := destruct o as [k|]; [destruct b|]; reflexivity.
Lemma tm_flp : tm s' = tm s. Proof. flps. Qed.
Lemma pcs_flp : pcs s' = pcs s. Proof. flps. Qed.
Lemma tp_flp : tp s' = tp s. Proof. flps. Qed.
Lemma cm_flp : cm s' = cm s. Proof. flps. Qed.
Lemma lg_flp : lg s' = lg s. Proof. flps. Qed.
Lemma es_flp : es s' = es s. Proof. flps. Qed.
Lemma wv_flp : wv s' = wv s. Proof. flps. Qed.
Lemma wc_flp : wc s' = wc s. Proof. flps. Qed.
Lemma hs_flp : hs s' = hs s. Proof. flps. Qed.
Lemma vG_flp : vG s' = vG s. Proof. flps. Qed.
Lemma ent_flp : forall t, ent s' t = ent s t. Proof. intros t. unfold ent. rewrite lg_flp. reflexivity. Qed.
(* the register that changes: the record's, a failure *)
Lemma rg_flp : forall c' j, rg (cs s' c') j = rg (cs s c') j \/
  (c' = c /\ o = Some j /\ b = false /\ rg (cs s' c') j = vd false (vv (rg (cs s c') j))).
Proof.
  intros c' j. destruct o as [k|]; [destruct b|]; cbn [sflp]; try (left; reflexivity).
  destruct (Nat.eqb_spec c' c) as [->|Nc].
  - destruct (Nat.eqb_spec j k) as [->|Nj].
    + right. split; [reflexivity|split; [reflexivity|split; [reflexivity|]]].
      unfold scfail, upd; simpl; rewrite Nat.eqb_refl; simpl; rewrite Nat.eqb_refl; reflexivity.
    + left. unfold scfail, upd; simpl; rewrite Nat.eqb_refl; simpl; rewrite (proj2 (Nat.eqb_neq _ _) Nj). reflexivity.
  - left. unfold scfail, upd; simpl; rewrite (proj2 (Nat.eqb_neq _ _) Nc). reflexivity.
Qed.
End Flp.

Lemma Inv1_run : forall p s, run p s -> Inv1 p s.
Proof.
  intros p s R. induction R as [|s t R IH H].
  - apply Inv1_init.
  - destruct (step_cases p s t H) as [(c & i & m' & a & K & u & w & H1 & H2 & H3 & H4 & Hbh & Hh & Hwt & Hvo & H6 & _ & ->)
      |[(c & k & d & B & m' & a & K & u & w & H1 & H2 & H5 & Hh & Hwe & Hve & H4 & _ & ->)
      |[(c & d & H1 & H2 & H3 & H4 & H5 & Hfh & ->)|[(c & k & xs & B & m' & a & K & u & w & bv & H1 & H2 & H3 & H5 & H4 & H6 & _ & ->)
      |[(c & H1 & H2 & H3 & Hvk & Hf & H4 & _ & ->)|(c & j & b & B & oX & Hj & Hf & Hc & ->)]]]]].
    + eapply Inv1_ord; eauto. destruct Hh as [(Z & _)|(t1 & Z & Ci & _)]; [left; exact Z|right; eauto].
    + apply Inv1_es. destruct Hh as [(Z & Ok)|(t1 & xs & ev & nv & Z & -> & _ & Ac & Ok)].
      * pose proof (early_nofull _ _ _ _ _ _ _ _ _ Ok). pose proof (early_len _ _ _ _ _ _ _ _ _ Ok).
        eapply Inv1_early; eauto.
      * assert (DCas Plain xs ev nv <> DFn FFull) by discriminate. pose proof (earlyW_len _ _ _ _ _ _ _ _ _ _ _ Ok).
        eapply Inv1_early; eauto. right. exists t1. split; [exact Z|split; [reflexivity|rewrite Ac; reflexivity]].
    + eapply Inv1_match; eauto.
    + apply Inv1_read; auto.
    + apply Inv1_skip; auto.
    + destruct oX as [k|]; [destruct b|]; cbn [sflp]; apply Inv1_cfix; [exact IH| |exact IH].
      destruct (cfix_rec _ _ _ _ _ _ _ _ _ Hc) as (Hp & Ho & Hh & _). apply Inv1_cfail; auto.
Qed.

(* ---------- places ---------- *)
Lemma find_some' : forall {A} (f : A -> bool) l x, find f l = Some x -> In x l /\ f x = true.
Proof.
  intros A f l x. induction l as [|a l IH]; simpl; [discriminate|].
  destruct (f a) eqn:E; [intros H; injection H as <-; auto|intros H; destruct (IH H); auto].
Qed.

Lemma existsb_ext_in : forall {A} (f g : A -> bool) l, (forall x, In x l -> f x = g x) -> existsb f l = existsb g l.
Proof.
  intros A f g l. induction l as [|a l IH]; intros H; simpl; auto.
  rewrite (H a (or_introl eq_refl)). f_equal. apply IH. intros x X. apply H. right. auto.
Qed.

Lemma existsb_seq : forall (f : nat -> bool) a n, existsb f (seq a n) = true <-> exists k, a <= k < a + n /\ f k = true.
Proof.
  intros f a n. rewrite existsb_exists. split.
  - intros (k & I & F). apply in_seq in I. eauto.
  - intros (k & I & F). exists k. split; auto. apply in_seq. lia.
Qed.

Lemma allin_iff : forall f a n, allin f a n = true <-> forall q, a <= q < a + n -> f q = true.
Proof.
  intros f a n. revert a. induction n as [|n IH]; intros a; simpl.
  - split; auto. intros _ q Q. lia.
  - rewrite andb_true_iff, IH. split.
    + intros [H1 H2] q Q. destruct (Nat.eq_dec q a) as [->|N]; auto. apply H2. lia.
    + intros H. split; [apply H; lia|]. intros q Q. apply H. lia.
Qed.

(* the pending accesses are recorded as their effects *)
Definition pend_ok (cc : cst) (pc : nat) : Prop :=
  forall k, oc cc k <> None -> pc <= k -> exists d, ai cc k = inst_of d /\ d <> DFn FFull.

Lemma desc_eqb_refl : forall d, desc_eqb d d = true.
Proof. intros [[] x|[] x v|[] x e n|[]]; simpl; rewrite ?Nat.eqb_refl, ?(proj2 (lst_eqb_eq x x) eq_refl); reflexivity. Qed.

Lemma desc_eqb_eq : forall d1 d2, desc_eqb d1 d2 = true -> d1 = d2.
Proof.
  intros [m1 x1|m1 x1 v1|m1 x1 e1 n1|[]] [m2 x2|m2 x2 v2|m2 x2 e2 n2|[]]; simpl; intros H; try discriminate; try reflexivity;
  repeat (apply andb_true_iff in H as [H ?]);
  repeat match goal with Hx : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in Hx end;
  repeat match goal with Hx : lst_eqb _ _ = true |- _ => apply lst_eqb_eq in Hx end;
  destruct m1, m2; subst; reflexivity.
Qed.

Lemma pend_at_spec : forall p c cc pc N r j k, pend_at p c cc pc N r j = Some k ->
  oc cc k <> None /\ pc <= k /\ k < N /\ exists t d, oc cc k = Some t /\ eof (ai cc k) r = Some d /\
    first_atb p c cc pc N r t d j = true.
Proof.
  intros p c cc pc N r j k H. unfold pend_at in H. apply find_some' in H as [Hin Hf].
  apply in_seq in Hin. destruct (oc cc k) as [t|] eqn:O; [|discriminate].
  destruct (eof (ai cc k) r) as [d|] eqn:D; [|discriminate]. split; [discriminate|]. split; [lia|]. split; [lia|]. eauto.
Qed.

(* ---------- places ---------- *)
Lemma first_in_iff : forall p c pc r (H H' X X' : nat -> Prop) (V V' : nat -> val -> Prop) g j,
  (forall j', pc <= j' <= j -> (H j' <-> H' j') /\ (X j' <-> X' j') /\ (forall v, V j' v <-> V' j' v)) ->
  (first_in p c pc r H X V g j <-> first_in p c pc r H' X' V' g j).
Proof.
  intros p c pc r H H' X X' V V' g j E. unfold first_in. split; intros (A & B & C & D); (split; [exact A|]); (split; [exact B|]); split.
  - intros Y. apply C. apply (E j); [lia|exact Y].
  - intros j' L1 L2 Ex F T. apply (E j'); [lia|]. apply D; auto. intros v Y. apply F. apply (E j'); [lia|exact Y].
  - intros Y. apply C. apply (E j); [lia|exact Y].
  - intros j' L1 L2 Ex F T. apply (E j'); [lia|]. apply D; auto. intros v Y. apply F. apply (E j'); [lia|exact Y].
Qed.

(* the bound on the nesting is any number past the time *)
Lemma plc_fuel : forall p c cc pc r T n g j, T < n ->
  (plc p c cc pc r n T g j <-> plc p c cc pc r (S T) T g j).
Proof.
  intros p c cc pc r T. induction T as [T IH] using lt_wf_ind. intros n g j L.
  destruct n as [|n]; [lia|]. cbn [plc]. apply first_in_iff. intros j' _.
  assert (F : forall t' g' j0, t' < T -> (plc p c cc pc r n t' g' j0 <-> plc p c cc pc r T t' g' j0)).
  { intros t' g' j0 Lt. rewrite (IH t' Lt n) by lia. rewrite (IH t' Lt T) by lia. tauto. }
  assert (A : (exists k' t' d', pending cc pc k' d' /\ oc cc k' = Some t' /\ t' < T /\ plc p c cc pc r n t' (TF d') j') <->
              (exists k' t' d', pending cc pc k' d' /\ oc cc k' = Some t' /\ t' < T /\ plc p c cc pc r T t' (TF d') j')).
  { split; intros (k' & t' & d' & P & O & Lt & Q); exists k', t', d'; (split; [exact P|]); (split; [exact O|]); (split; [exact Lt|]);
      [apply (proj1 (F t' _ _ Lt))|apply (proj2 (F t' _ _ Lt))]; exact Q. }
  assert (B : (exists k' t' m' xs', hpending cc pc k' m' xs' /\ oh cc k' = Some t' /\ t' < T /\ hlive cc k' T /\ plc p c cc pc r n t' (TH m' xs') j') <->
              (exists k' t' m' xs', hpending cc pc k' m' xs' /\ oh cc k' = Some t' /\ t' < T /\ hlive cc k' T /\ plc p c cc pc r T t' (TH m' xs') j')).
  { split; intros (k' & t' & m' & xs' & P & O & Lt & Hl & Q); exists k', t', m', xs'; (split; [exact P|]); (split; [exact O|]); (split; [exact Lt|]);
      (split; [exact Hl|]); [apply (proj1 (F t' _ _ Lt))|apply (proj2 (F t' _ _ Lt))]; exact Q. }
  assert (C : forall v, (exists k' t' m' xs', hpending cc pc k' m' xs' /\ oh cc k' = Some t' /\ t' < T /\ hlive cc k' T /\
                 plc p c cc pc r n t' (TH m' xs') j' /\ v = r j') <->
              (exists k' t' m' xs', hpending cc pc k' m' xs' /\ oh cc k' = Some t' /\ t' < T /\ hlive cc k' T /\
                 plc p c cc pc r T t' (TH m' xs') j' /\ v = r j')).
  { intros v. split; intros (k' & t' & m' & xs' & P & O & Lt & Hl & Q & Ev); exists k', t', m', xs'; (split; [exact P|]); (split; [exact O|]);
      (split; [exact Lt|]); (split; [exact Hl|]); (split; [|exact Ev]);
      [apply (proj1 (F t' _ _ Lt))|apply (proj2 (F t' _ _ Lt))]; exact Q. }
  split; [exact A|]. split; [rewrite A, B; tauto|exact C].
Qed.

Lemma plc_in : forall p c cc pc r T g j,
  plc p c cc pc r (S T) T g j <->
  first_in p c pc r (taken p c cc pc r T) (fun j' => taken p c cc pc r T j' \/ htaken p c cc pc r T j')
    (htakenv p c cc pc r T) g j.
Proof.
  intros p c cc pc r T g j. cbn [plc]. apply first_in_iff. intros j' _. unfold taken, htaken, htakenv, first_at, first_atR.
  assert (A : (exists k' t' d', pending cc pc k' d' /\ oc cc k' = Some t' /\ t' < T /\ plc p c cc pc r T t' (TF d') j') <->
              (exists k' t' d', pending cc pc k' d' /\ oc cc k' = Some t' /\ t' < T /\ plc p c cc pc r (S t') t' (TF d') j')).
  { split; intros (k' & t' & d' & P & O & Lt & Q); exists k', t', d'; (split; [exact P|]); (split; [exact O|]); (split; [exact Lt|]);
      [apply (proj1 (plc_fuel p c cc pc r t' T _ _ Lt))|apply (proj2 (plc_fuel p c cc pc r t' T _ _ Lt))]; exact Q. }
  assert (B : (exists k' t' m' xs', hpending cc pc k' m' xs' /\ oh cc k' = Some t' /\ t' < T /\ hlive cc k' T /\ plc p c cc pc r T t' (TH m' xs') j') <->
              (exists k' t' m' xs', hpending cc pc k' m' xs' /\ oh cc k' = Some t' /\ t' < T /\ hlive cc k' T /\ plc p c cc pc r (S t') t' (TH m' xs') j')).
  { split; intros (k' & t' & m' & xs' & P & O & Lt & Hl & Q); exists k', t', m', xs'; (split; [exact P|]); (split; [exact O|]); (split; [exact Lt|]);
      (split; [exact Hl|]); [apply (proj1 (plc_fuel p c cc pc r t' T _ _ Lt))|apply (proj2 (plc_fuel p c cc pc r t' T _ _ Lt))]; exact Q. }
  assert (C : forall v, (exists k' t' m' xs', hpending cc pc k' m' xs' /\ oh cc k' = Some t' /\ t' < T /\ hlive cc k' T /\
                 plc p c cc pc r T t' (TH m' xs') j' /\ v = r j') <->
              (exists k' t' m' xs', hpending cc pc k' m' xs' /\ oh cc k' = Some t' /\ t' < T /\ hlive cc k' T /\
                 plc p c cc pc r (S t') t' (TH m' xs') j' /\ v = r j')).
  { intros v. split; intros (k' & t' & m' & xs' & P & O & Lt & Hl & Q & Ev); exists k', t', m', xs'; (split; [exact P|]); (split; [exact O|]);
      (split; [exact Lt|]); (split; [exact Hl|]); (split; [|exact Ev]);
      [apply (proj1 (plc_fuel p c cc pc r t' T _ _ Lt))|apply (proj2 (plc_fuel p c cc pc r t' T _ _ Lt))]; exact Q. }
  split; [exact A|]. split; [rewrite A, B; tauto|exact C].
Qed.

Lemma first_at_in : forall p c cc pc r T d j,
  first_at p c cc pc r T d j <->
  first_in p c pc r (taken p c cc pc r T) (fun j' => taken p c cc pc r T j' \/ htaken p c cc pc r T j')
    (htakenv p c cc pc r T) (TF d) j.
Proof. intros. apply plc_in. Qed.

Lemma first_atR_in : forall p c cc pc r T m xs j,
  first_atR p c cc pc r T m xs j <->
  first_in p c pc r (taken p c cc pc r T) (fun j' => taken p c cc pc r T j' \/ htaken p c cc pc r T j')
    (htakenv p c cc pc r T) (TH m xs) j.
Proof. intros. apply plc_in. Qed.

Lemma htakenv_htaken : forall p c cc pc r T j v, htakenv p c cc pc r T j v -> htaken p c cc pc r T j.
Proof. intros p c cc pc r T j v (k & t & m & xs & A & B & C & D & E & _). exists k, t, m, xs. auto. Qed.

Lemma first_at_eof : forall p c cc pc r T d j, first_at p c cc pc r T d j -> eof (ins p c j r) r = Some d.
Proof. intros p c cc pc r T d j F. apply first_at_in in F. apply F. Qed.

Lemma first_at_le : forall p c cc pc r T d j, first_at p c cc pc r T d j -> pc <= j.
Proof. intros p c cc pc r T d j F. apply first_at_in in F. apply F. Qed.

Lemma first_at_free : forall p c cc pc r T d j, first_at p c cc pc r T d j -> ~ taken p c cc pc r T j.
Proof. intros p c cc pc r T d j F X. apply first_at_in in F. apply F. left. exact X. Qed.

Lemma first_at_hfree : forall p c cc pc r T d j, first_at p c cc pc r T d j -> ~ htaken p c cc pc r T j.
Proof. intros p c cc pc r T d j F X. apply first_at_in in F. apply F. right. exact X. Qed.

Lemma first_at_before : forall p c cc pc r T d j, first_at p c cc pc r T d j ->
  forall j', pc <= j' -> j' < j -> executes (ins p c j' r) r = true ->
  (forall v, htakenv p c cc pc r T j' v -> cfailv (ins p c j' r) r v = false) ->
  tied (ins p c j' r) (inst_of d) -> taken p c cc pc r T j'.
Proof. intros p c cc pc r T d j F. apply first_at_in in F. apply F. Qed.

Lemma first_at_mk : forall p c cc pc r T d j, pc <= j -> eof (ins p c j r) r = Some d -> ~ taken p c cc pc r T j ->
  ~ htaken p c cc pc r T j ->
  (forall j', pc <= j' -> j' < j -> executes (ins p c j' r) r = true ->
     (forall v, htakenv p c cc pc r T j' v -> cfailv (ins p c j' r) r v = false) ->
     tied (ins p c j' r) (inst_of d) -> taken p c cc pc r T j') -> first_at p c cc pc r T d j.
Proof. intros. apply first_at_in. repeat split; auto. intros [X|X]; auto. Qed.

Lemma first_atR_eofR : forall p c cc pc r T m xs j, first_atR p c cc pc r T m xs j -> eofR (ins p c j r) r = Some (m, xs).
Proof. intros p c cc pc r T m xs j F. apply first_atR_in in F. apply F. Qed.

Lemma first_atR_le : forall p c cc pc r T m xs j, first_atR p c cc pc r T m xs j -> pc <= j.
Proof. intros p c cc pc r T m xs j F. apply first_atR_in in F. apply F. Qed.

Lemma first_atR_free : forall p c cc pc r T m xs j, first_atR p c cc pc r T m xs j -> ~ taken p c cc pc r T j.
Proof. intros p c cc pc r T m xs j F X. apply first_atR_in in F. apply F. left. exact X. Qed.

Lemma first_atR_hfree : forall p c cc pc r T m xs j, first_atR p c cc pc r T m xs j -> ~ htaken p c cc pc r T j.
Proof. intros p c cc pc r T m xs j F X. apply first_atR_in in F. apply F. right. exact X. Qed.

Lemma first_atR_before : forall p c cc pc r T m xs j, first_atR p c cc pc r T m xs j ->
  forall j', pc <= j' -> j' < j -> executes (ins p c j' r) r = true ->
  (forall v, htakenv p c cc pc r T j' v -> cfailv (ins p c j' r) r v = false) ->
  tied (ins p c j' r) (crd m xs) -> taken p c cc pc r T j'.
Proof. intros p c cc pc r T m xs j F. apply first_atR_in in F. apply F. Qed.

Lemma first_atR_mk : forall p c cc pc r T m xs j, pc <= j -> eofR (ins p c j r) r = Some (m, xs) ->
  ~ taken p c cc pc r T j -> ~ htaken p c cc pc r T j ->
  (forall j', pc <= j' -> j' < j -> executes (ins p c j' r) r = true ->
     (forall v, htakenv p c cc pc r T j' v -> cfailv (ins p c j' r) r v = false) ->
     tied (ins p c j' r) (crd m xs) -> taken p c cc pc r T j') -> first_atR p c cc pc r T m xs j.
Proof. intros. apply first_atR_in. repeat split; auto. intros [X|X]; auto. Qed.

(* a CAS's read alone, at a CAS of its mode and cells, is tied to it *)
Lemma eofR_exec_tied : forall p c j r m xs, cellful p -> eofR (ins p c j r) r = Some (m, xs) ->
  executes (ins p c j r) r = true /\ tied (ins p c j r) (crd m xs).
Proof.
  intros p c j r m xs Wc H. pose proof (Wc c j r) as N.
  destruct (ins p c j r) as [| |m' xs' cb e n| |] eqn:E; cbn in H; try discriminate.
  destruct (cb r) eqn:Cb; [injection H as <- <-|discriminate].
  split; [unfold executes, icond; cbn; rewrite Cb; reflexivity|].
  specialize (N eq_refl).
  left. change (icells (crd m' xs')) with (icells (ICas m' xs' cb e n)).
  destruct (icells (ICas m' xs' cb e n)) as [|x l]; [congruence|]. exists x. split; left; reflexivity.
Qed.

(* an access has one place *)
Lemma first_at_unique : forall p c cc pc r T d j1 j2, cellful p ->
  first_at p c cc pc r T d j1 -> first_at p c cc pc r T d j2 -> j1 = j2.
Proof.
  intros p c cc pc r T d j1 j2 Wc F1 F2.
  assert (Tj : forall j, eof (ins p c j r) r = Some d -> executes (ins p c j r) r = true /\ tied (ins p c j r) (inst_of d)).
  { intros j D. apply (eof_exec_tied p c j r d Wc D). }
  destruct (Nat.lt_trichotomy j1 j2) as [L|[L|L]]; auto; exfalso.
  - destruct (Tj j1 (first_at_eof _ _ _ _ _ _ _ _ F1)) as [E Ti].
    apply (first_at_free _ _ _ _ _ _ _ _ F1). apply (first_at_before _ _ _ _ _ _ _ _ F2); auto. apply (first_at_le _ _ _ _ _ _ _ _ F1).
    intros v X; exfalso; apply (first_at_hfree _ _ _ _ _ _ _ _ F1); exact (htakenv_htaken _ _ _ _ _ _ _ _ X).
  - destruct (Tj j2 (first_at_eof _ _ _ _ _ _ _ _ F2)) as [E Ti].
    apply (first_at_free _ _ _ _ _ _ _ _ F2). apply (first_at_before _ _ _ _ _ _ _ _ F1); auto. apply (first_at_le _ _ _ _ _ _ _ _ F2).
    intros v X; exfalso; apply (first_at_hfree _ _ _ _ _ _ _ _ F2); exact (htakenv_htaken _ _ _ _ _ _ _ _ X).
Qed.

Lemma first_atR_unique : forall p c cc pc r T m xs j1 j2, cellful p ->
  first_atR p c cc pc r T m xs j1 -> first_atR p c cc pc r T m xs j2 -> j1 = j2.
Proof.
  intros p c cc pc r T m xs j1 j2 Wc F1 F2.
  destruct (Nat.lt_trichotomy j1 j2) as [L|[L|L]]; auto; exfalso.
  - destruct (eofR_exec_tied p c j1 r m xs Wc (first_atR_eofR _ _ _ _ _ _ _ _ _ F1)) as [E Ti].
    apply (first_atR_free _ _ _ _ _ _ _ _ _ F1). apply (first_atR_before _ _ _ _ _ _ _ _ _ F2); auto.
    apply (first_atR_le _ _ _ _ _ _ _ _ _ F1).
    intros v X; exfalso; apply (first_atR_hfree _ _ _ _ _ _ _ _ _ F1); exact (htakenv_htaken _ _ _ _ _ _ _ _ X).
  - destruct (eofR_exec_tied p c j2 r m xs Wc (first_atR_eofR _ _ _ _ _ _ _ _ _ F2)) as [E Ti].
    apply (first_atR_free _ _ _ _ _ _ _ _ _ F2). apply (first_atR_before _ _ _ _ _ _ _ _ _ F1); auto.
    apply (first_atR_le _ _ _ _ _ _ _ _ _ F2).
    intros v X; exfalso; apply (first_atR_hfree _ _ _ _ _ _ _ _ _ F2); exact (htakenv_htaken _ _ _ _ _ _ _ _ X).
Qed.

(* ---------- places of either kind ---------- *)
Definition tatp (i : instr) (r : regs) (g : tgt) : Prop :=
  match g with TF d => eof i r = Some d | TH m xs => eofR i r = Some (m, xs) end.

Lemma plc_le : forall p c cc pc r T g j, plc p c cc pc r (S T) T g j -> pc <= j.
Proof. intros p c cc pc r T g j F. apply plc_in in F. apply F. Qed.

Lemma plc_tat : forall p c cc pc r T g j, plc p c cc pc r (S T) T g j -> tatp (ins p c j r) r g.
Proof. intros p c cc pc r T g j F. apply plc_in in F. destruct F as (_ & D & _). destruct g; exact D. Qed.

Lemma plc_free : forall p c cc pc r T g j, plc p c cc pc r (S T) T g j -> ~ taken p c cc pc r T j.
Proof. intros p c cc pc r T g j F X. apply plc_in in F. apply F. left. exact X. Qed.

Lemma plc_hfree : forall p c cc pc r T g j, plc p c cc pc r (S T) T g j -> ~ htaken p c cc pc r T j.
Proof. intros p c cc pc r T g j F X. apply plc_in in F. apply F. right. exact X. Qed.

Lemma plc_before : forall p c cc pc r T g j, plc p c cc pc r (S T) T g j ->
  forall j', pc <= j' -> j' < j -> executes (ins p c j' r) r = true ->
  (forall v, htakenv p c cc pc r T j' v -> cfailv (ins p c j' r) r v = false) ->
  tied (ins p c j' r) (tinst g) -> taken p c cc pc r T j'.
Proof. intros p c cc pc r T g j F. apply plc_in in F. apply F. Qed.

Lemma tat_exec_tied : forall p c j r g, cellful p -> tatp (ins p c j r) r g ->
  executes (ins p c j r) r = true /\ tied (ins p c j r) (tinst g).
Proof.
  intros p c j r [d|m xs] Wc D; [apply (eof_exec_tied p c j r d Wc D)|apply (eofR_exec_tied p c j r m xs Wc D)].
Qed.

Lemma plc_unique : forall p c cc pc r T g j1 j2, cellful p ->
  plc p c cc pc r (S T) T g j1 -> plc p c cc pc r (S T) T g j2 -> j1 = j2.
Proof.
  intros p c cc pc r T g j1 j2 Wc F1 F2.
  destruct (Nat.lt_trichotomy j1 j2) as [L|[L|L]]; auto; exfalso.
  - destruct (tat_exec_tied p c j1 r g Wc (plc_tat _ _ _ _ _ _ _ _ F1)) as [E Ti].
    apply (plc_free _ _ _ _ _ _ _ _ F1). apply (plc_before _ _ _ _ _ _ _ _ F2); auto. apply (plc_le _ _ _ _ _ _ _ _ F1).
    intros v X; exfalso; apply (plc_hfree _ _ _ _ _ _ _ _ F1); exact (htakenv_htaken _ _ _ _ _ _ _ _ X).
  - destruct (tat_exec_tied p c j2 r g Wc (plc_tat _ _ _ _ _ _ _ _ F2)) as [E Ti].
    apply (plc_free _ _ _ _ _ _ _ _ F2). apply (plc_before _ _ _ _ _ _ _ _ F1); auto. apply (plc_le _ _ _ _ _ _ _ _ F2).
    intros v X; exfalso; apply (plc_hfree _ _ _ _ _ _ _ _ F2); exact (htakenv_htaken _ _ _ _ _ _ _ _ X).
Qed.

(* the access at a place: an access with the target's cells *)
Lemma tat_dof : forall i r g, tatp i r g -> (match g with TF d => isaccd d = true | TH _ _ => True end) ->
  exists d, dof i r = Some d /\ icells (inst_of d) = icells (tinst g) /\ is_load (inst_of d) = (match g with TF d => is_load (inst_of d) | TH _ _ => true end).
Proof.
  intros i r [d|m xs] D A.
  - exists d. split; [apply (eof_acc _ _ _ D A)|split; reflexivity].
  - destruct i as [m1 x1 c1|m1 x1 c1 v1|m0 x0 c0 e0 n0|f1|]; simpl in D; try discriminate.
    destruct (c0 r) eqn:C0; [injection D as <- <-|discriminate].
    exists (DCas m0 x0 (e0 r) (n0 r)). simpl. rewrite C0. split; [reflexivity|split; reflexivity].
Qed.

Lemma tatb_iff : forall i r g, tatb i r g = true <->
  match g with TF d => eof i r = Some d | TH m xs => eofR i r = Some (m, xs) end.
Proof.
  intros i r [d|m xs]; unfold tatb.
  - destruct (eof i r) as [d'|]; simpl; [|split; discriminate].
    split; [intros D; apply desc_eqb_eq in D; congruence|intros E; injection E as ->; apply desc_eqb_refl].
  - destruct (eofR i r) as [[m' xs']|]; [|split; discriminate].
    rewrite lst_eqb_eq. split.
    + intros ->. destruct m, m'. reflexivity.
    + intros E. injection E as -> ->. reflexivity.
Qed.

(* the decidable form: with the pending accesses recorded as their effects
   and below N, it is the place *)
Lemma fab_plc : forall p c cc pc N r, pend_ok cc pc -> (forall k, oc cc k <> None -> pc <= k -> k < N) ->
  (forall k, oh cc k <> None -> pc <= k -> k < N) ->
  forall n T g j, fab p c cc pc N r n T g j = true <-> plc p c cc pc r n T g j.
Proof.
  intros p c cc pc N r PO BN BNh n. induction n as [|n IH]; intros T g j; [split; [discriminate|intros []]|].
  cbn [fab plc].
  assert (TK : forall j', existsb (fun k' => match oc cc k' with
                       | Some t' => Nat.ltb t' T && match eof (ai cc k') r with Some d' => fab p c cc pc N r n t' (TF d') j' | None => false end
                       | None => false end) (seq pc (N - pc)) = true <->
     exists k' t' d', pending cc pc k' d' /\ oc cc k' = Some t' /\ t' < T /\ plc p c cc pc r n t' (TF d') j').
  { intros j'. rewrite existsb_seq. split.
    - intros (k' & Lk & Q). destruct (oc cc k') as [t'|] eqn:O; [|discriminate].
      destruct (PO k' ltac:(congruence) ltac:(lia)) as (d' & Ad & Nd). rewrite Ad, (eof_inst d' r Nd) in Q.
      apply andb_true_iff in Q as [Q1 Q2]. apply Nat.ltb_lt in Q1. apply IH in Q2.
      exists k', t', d'. repeat split; auto; [lia|congruence].
    - intros (k' & t' & d' & (P1 & P2 & P3) & O & Lt & Q). exists k'. split; [split; [lia|]; pose proof (BN k' P2 P1); lia|].
      destruct (PO k' P2 P1) as (d'' & Ad'' & Nd''). rewrite P3 in Ad''. apply inst_of_inj in Ad''. subst d''.
      rewrite O, P3, (eof_inst d' r Nd''). apply andb_true_iff. split; [apply Nat.ltb_lt; auto|]. apply IH. exact Q. }
  assert (TH : forall j', existsb (fun k' => match oh cc k' with
                       | Some t' => Nat.ltb t' T && hliveb cc k' T && match casx (ai cc k') with
                                              | Some (m', xs') => fab p c cc pc N r n t' (TH m' xs') j'
                                              | None => false end
                       | None => false end) (seq pc (N - pc)) = true <->
     exists k' t' m' xs', hpending cc pc k' m' xs' /\ oh cc k' = Some t' /\ t' < T /\ hlive cc k' T /\
       plc p c cc pc r n t' (TH m' xs') j').
  { assert (HL : forall k', hliveb cc k' T = true <-> hlive cc k' T).
    { intros k'. unfold hliveb, hlive. destruct (oc cc k') as [t2|]; split.
      - intros X t3 E. injection E as <-. apply Nat.ltb_lt. exact X.
      - intros X. apply Nat.ltb_lt. apply X. reflexivity.
      - intros _ t3 E. discriminate.
      - intros _. reflexivity. }
    intros j'. rewrite existsb_seq. split.
    - intros (k' & Lk & Q). destruct (oh cc k') as [t'|] eqn:Oh; [|discriminate].
      destruct (casx (ai cc k')) as [[m' xs']|] eqn:Cx; [|rewrite andb_false_r in Q; discriminate].
      apply andb_true_iff in Q as [Q1 Q2]. apply andb_true_iff in Q1 as [Q1 Q3]. apply Nat.ltb_lt in Q1. apply IH in Q2.
      apply HL in Q3. exists k', t', m', xs'. repeat split; auto; [lia|congruence].
    - intros (k' & t' & m' & xs' & (P1 & P3 & P4) & O & Lt & Hl & Q). exists k'.
      split; [split; [lia|]; pose proof (BNh k' P3 P1); lia|].
      rewrite O, P4. apply andb_true_iff. split; [apply andb_true_iff; split; [apply Nat.ltb_lt; auto|apply HL; exact Hl]|]. apply IH. exact Q. }
  assert (HL : forall k', hliveb cc k' T = true <-> hlive cc k' T).
  { intros k'. unfold hliveb, hlive. destruct (oc cc k') as [t2|]; split.
    - intros X t3 E. injection E as <-. apply Nat.ltb_lt. exact X.
    - intros X. apply Nat.ltb_lt. apply X. reflexivity.
    - intros _ t3 E. discriminate.
    - intros _. reflexivity. }
  assert (THF : forall j', existsb (fun k' => match oh cc k' with
                       | Some t' => Nat.ltb t' T && hliveb cc k' T && match casx (ai cc k') with
                                              | Some (m', xs') => fab p c cc pc N r n t' (M2Model.TH m' xs') j' &&
                                                                  cfailv (ins p c j' r) r (r j')
                                              | None => false end
                       | None => false end) (seq pc (N - pc)) = true <->
     exists v, (exists k' t' m' xs', hpending cc pc k' m' xs' /\ oh cc k' = Some t' /\ t' < T /\ hlive cc k' T /\
       plc p c cc pc r n t' (M2Model.TH m' xs') j' /\ v = r j') /\ cfailv (ins p c j' r) r v = true).
  { intros j'. rewrite existsb_seq. split.
    - intros (k' & Lk & Q). destruct (oh cc k') as [t'|] eqn:Oh; [|discriminate].
      destruct (casx (ai cc k')) as [[m' xs']|] eqn:Cx; [|rewrite andb_false_r in Q; discriminate].
      apply andb_true_iff in Q as [Q1 Q2]. apply andb_true_iff in Q1 as [Q1 Q3]. apply Nat.ltb_lt in Q1.
      apply andb_true_iff in Q2 as [Q2 Q4]. apply IH in Q2.
      apply HL in Q3. exists (r j'). split; [|exact Q4]. exists k', t', m', xs'. repeat split; auto; [lia|congruence].
    - intros (v & (k' & t' & m' & xs' & (P1 & P3 & P4) & O & Lt & Hl & Q & ->) & Cf). exists k'.
      split; [split; [lia|]; pose proof (BNh k' P3 P1); lia|].
      rewrite O, P4. apply andb_true_iff. split; [apply andb_true_iff; split; [apply Nat.ltb_lt; auto|apply HL; exact Hl]|].
      apply andb_true_iff. split; [apply IH; exact Q|exact Cf]. }
  unfold first_in. rewrite !andb_true_iff, Nat.leb_le, negb_true_iff, orb_false_iff, allin_iff, tatb_iff. split.
  - intros (((L & D) & NT1 & NT2) & AL). split; [exact L|]. split; [exact D|]. split.
    + intros [X|X]; [apply TK in X|apply TH in X]; congruence.
    + intros j' L1 L2 Ex F Tt. specialize (AL j' ltac:(lia)). apply orb_true_iff in AL as [AL|AL].
      * apply TK. exact AL.
      * exfalso. rewrite Ex, (tied_b _ _ Tt) in AL. cbn [andb] in AL. rewrite negb_involutive in AL.
        apply THF in AL. destruct AL as (v & X & Cf). rewrite (F v X) in Cf. discriminate.
  - intros (L & D & NT & AL). split; [split; [split; [exact L|exact D]|]|].
    + split; [destruct (existsb _ _) eqn:X; auto; exfalso; apply NT; left; apply TK; exact X|].
      destruct (existsb _ _) eqn:X; auto; exfalso; apply NT; right; apply TH; exact X.
    + intros q Q. apply orb_true_iff. destruct (tiedb (ins p c q r) (tinst g)) eqn:Tq; [|right; reflexivity].
      destruct (executes (ins p c q r) r) eqn:Ex; [|right; reflexivity].
      destruct (existsb _ (seq pc (N - pc))) eqn:Tf at 2; [right; reflexivity|].
      left. apply TK. apply AL; [lia|lia|exact Ex| |apply b_tied; exact Tq].
      intros v X. destruct (cfailv (ins p c q r) r v) eqn:Cf; [|reflexivity]. exfalso.
      assert (Z : _ = true) by (apply (proj2 (THF q)); exists v; split; [exact X|exact Cf]). congruence.
Qed.

(* the before-clause of a place, decided: an instruction before the place,
   tied to the target, is taken, or is the place of a read alone whose CAS
   fails under r *)
Lemma plc_before_dec : forall p c cc pc N r T g j j', pend_ok cc pc -> (forall k, oc cc k <> None -> pc <= k -> k < N) ->
  (forall k, oh cc k <> None -> pc <= k -> k < N) ->
  plc p c cc pc r (S T) T g j -> pc <= j' -> j' < j -> executes (ins p c j' r) r = true ->
  tied (ins p c j' r) (tinst g) ->
  taken p c cc pc r T j' \/ exists v, htakenv p c cc pc r T j' v /\ cfailv (ins p c j' r) r v = true.
Proof.
  intros p c cc pc N r T g j j' PO BN BNh F L1 L2 Ex Ti.
  apply (proj2 (fab_plc p c cc pc N r PO BN BNh (S T) T g j)) in F. cbn [fab] in F.
  apply andb_true_iff in F as [_ AL]. rewrite allin_iff in AL. specialize (AL j' ltac:(lia)).
  rewrite (tied_b _ _ Ti), Ex in AL. cbn [andb] in AL. apply orb_true_iff in AL as [AL|AL].
  - left. apply existsb_seq in AL. destruct AL as (k' & Lk & Q). destruct (oc cc k') as [t'|] eqn:O; [|discriminate].
    destruct (PO k' ltac:(congruence) ltac:(lia)) as (d' & Ad & Nd). rewrite Ad, (eof_inst d' r Nd) in Q.
    apply andb_true_iff in Q as [Q1 Q2]. apply Nat.ltb_lt in Q1.
    apply (proj1 (fab_plc p c cc pc N r PO BN BNh T t' (TF d') j')) in Q2.
    exists k', t', d'. split; [split; [lia|split; [congruence|exact Ad]]|]. split; [exact O|]. split; [exact Q1|].
    unfold first_at. apply (proj1 (plc_fuel p c cc pc r t' T _ _ Q1)). exact Q2.
  - right. rewrite negb_involutive in AL. apply existsb_seq in AL. destruct AL as (k' & Lk & Q).
    destruct (oh cc k') as [t'|] eqn:Oh; [|discriminate].
    destruct (casx (ai cc k')) as [[m' xs']|] eqn:Cx; [|rewrite andb_false_r in Q; discriminate].
    apply andb_true_iff in Q as [Q1 Q2]. apply andb_true_iff in Q1 as [Q1 Q3]. apply Nat.ltb_lt in Q1.
    apply andb_true_iff in Q2 as [Q2 Q4].
    apply (proj1 (fab_plc p c cc pc N r PO BN BNh T t' (M2Model.TH m' xs') j')) in Q2.
    exists (r j'). split; [|exact Q4]. exists k', t', m', xs'.
    split; [split; [lia|split; [congruence|exact Cx]]|]. split; [exact Oh|]. split; [exact Q1|].
    split; [unfold hliveb, hlive in *; destruct (oc cc k') as [t2|]; [intros t3 E; injection E as <-; apply Nat.ltb_lt; exact Q3|intros t3 E; discriminate]|].
    split; [|reflexivity]. unfold first_atR. apply (proj1 (plc_fuel p c cc pc r t' T _ _ Q1)). exact Q2.
Qed.

Lemma first_atb_iff : forall p c cc pc N r T d j, pend_ok cc pc -> (forall k, oc cc k <> None -> pc <= k -> k < N) ->
  (forall k, oh cc k <> None -> pc <= k -> k < N) ->
  (first_atb p c cc pc N r T d j = true <-> first_at p c cc pc r T d j).
Proof. intros. unfold first_atb, first_at. apply fab_plc; auto. Qed.

(* the place of a pending access *)
Definition placed (p : prog) (c : nat) (cc : cst) (pc : nat) (r : regs) (k : nat) (d : desc) (j : nat) : Prop :=
  pending cc pc k d /\ exists t, oc cc k = Some t /\ first_at p c cc pc r t d j.

(* a taken instruction is an access *)
Lemma taken_dof : forall p c cc pc r T j, taken p c cc pc r T j -> exists d, eof (ins p c j r) r = Some d.
Proof. intros p c cc pc r T j (k & t & d & _ & _ & _ & F). exists d. apply (first_at_eof _ _ _ _ _ _ _ _ F). Qed.

(* a place of an access: its effect *)
Lemma first_at_dof : forall p c cc pc r T d j, first_at p c cc pc r T d j -> isaccd d = true -> dof (ins p c j r) r = Some d.
Proof. intros p c cc pc r T d j F A. apply (eof_acc _ _ _ (first_at_eof _ _ _ _ _ _ _ _ F) A). Qed.
