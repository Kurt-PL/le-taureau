(* Model2: the trap programmes are race-free under racy_g (checked
   enumeration, M2EnumG), so DRF-SC (M2PDrf) applies to them and agrees with
   their forbidden outcomes in M2Traps. *)
From Stdlib Require Import Arith Lia List Bool PArith.
Import ListNotations.
Require Import M2Model M2SC M2Lit M2Traps M2EnumG.

Lemma stat_fin' : forall P c k r, nth c (map (@length instr) P) 0 <= k -> ins (stat P) c k r = INop.
Proof.
  intros P c k r L. rewrite ins_stat. destruct (Nat.lt_ge_cases c (length P)) as [Lc|Lc].
  - rewrite (nth_indep _ _ (length (@nil instr))) in L by (rewrite length_map; auto).
    rewrite map_nth in L. apply nth_overflow. auto.
  - rewrite (nth_overflow P) by auto. destruct k; reflexivity.
Qed.

Lemma stat_out : forall P c k r, length (map (@length instr) P) <= c -> ins (stat P) c k r = INop.
Proof.
  intros P c k r L. rewrite length_map in L. rewrite ins_stat, (nth_overflow P) by auto. destruct k; reflexivity.
Qed.

Definition sfut (P : list (list instr)) (c k : nat) : list cell := concat (map icells (skipn k (nth c P []))).

Lemma sfut_spec : forall P c k r x, In x (icells (ins (stat P) c k r)) -> In x (sfut P c k).
Proof.
  intros P c k r x H. rewrite ins_stat in H. unfold sfut.
  destruct (Nat.lt_ge_cases k (length (nth c P []))) as [L|L]; [|rewrite nth_overflow in H by auto; destruct H].
  rewrite <- (firstn_skipn k (nth c P [])) in H. rewrite app_nth2 in H by (rewrite length_firstn; lia).
  rewrite length_firstn, Nat.min_l, Nat.sub_diag in H by lia.
  destruct (skipn k (nth c P [])) as [|s t'] eqn:E; [destruct H|]. simpl in H |- *.
  apply in_or_app. left. exact H.
Qed.

(* every access names one cell *)
Definition onecellb (i : instr) : bool :=
  match i with
  | ILd _ xs _ | ISt _ xs _ _ | ICas _ xs _ _ _ => match dd xs with [_] => true | _ => false end
  | _ => true
  end.

Lemma stat_one : forall P, forallb (forallb onecellb) P = true ->
  forall c k r, isacc (ins (stat P) c k r) = true -> exists x, icells (ins (stat P) c k r) = [x].
Proof.
  intros P F c k r H. rewrite ins_stat in *.
  destruct (Nat.lt_ge_cases c (length P)) as [Lc|Lc]; [|rewrite (nth_overflow P) in H |- * by auto; destruct k; discriminate].
  destruct (Nat.lt_ge_cases k (length (nth c P []))) as [Lk|Lk]; [|rewrite nth_overflow in H by auto; discriminate].
  rewrite forallb_forall in F. specialize (F _ (nth_In _ [] Lc)). rewrite forallb_forall in F.
  specialize (F _ (nth_In _ INop Lk)).
  destruct (nth k (nth c P []) INop) as [m xs cn|m xs cn v|m xs cn e n| |]; simpl in *; try discriminate;
    destruct (dd xs) as [|y [|z t]]; try discriminate; exists y; reflexivity.
Qed.

Lemma sfut_mono : forall P c k x, In x (sfut P c (S k)) -> In x (sfut P c k).
Proof.
  intros P c k x H. unfold sfut in *. rewrite <- (skipn_skipn 1 k) in H.
  destruct (skipn k (nth c P [])) as [|s t']; simpl in *; auto. apply in_or_app. right. auto.
Qed.

(* fenced slots read off the data *)
Definition iff' (i : instr) : bool := match i with IFn FFull => true | _ => false end.
Definition sex (P : list (list instr)) (c k : nat) : bool :=
  Nat.leb 1 k && iff' (nth (k - 1) (nth c P []) INop) && iff' (nth (S k) (nth c P []) INop).

Lemma sex_fa : forall P c k, sex P c k = true -> fa (stat P) c k.
Proof.
  intros P c k H. unfold sex in H. apply andb_prop in H as [H H2]. apply andb_prop in H as [H1 H0].
  apply Nat.leb_le in H1. split; [auto|]. intros r. rewrite !ins_stat.
  split; [destruct (nth (k - 1) (nth c P []) INop) as [| | |[| | | |]|]|destruct (nth (S k) (nth c P []) INop) as [| | |[| | | |]|]];
    simpl in *; try discriminate; reflexivity.
Qed.

Theorem stat_race_free_g : forall P M fuel, wf (stat P) -> forallb (forallb onecellb) P = true ->
  closed2 (stat P) (map (@length instr) P) M (sfut P) (sex P) (reach (stat P) (map (@length instr) P) M (sfut P) (sex P) fuel) = true ->
  race_free_g (stat P).
Proof.
  intros P M fuel W O C.
  apply (enum_race_free (stat P) (map (@length instr) P) M W (stat_fin' P) (stat_out P) (sfut P) (sfut_spec P) (stat_one P O) (sfut_mono P)
    (sex P) (sex_fa P) _ (closed2_closed _ _ _ _ _ _ C)).
Qed.

Theorem TRAP1_race_free : race_free_g TRAP1.
Proof. apply (stat_race_free_g _ 2 1000%positive); [wf_tac|vm_compute; reflexivity|vm_compute; reflexivity]. Qed.
Theorem TRAP2_race_free : race_free_g TRAP2.
Proof. apply (stat_race_free_g _ 2 1000%positive); [wf_tac|vm_compute; reflexivity|vm_compute; reflexivity]. Qed.
Theorem TRAP3_race_free : race_free_g TRAP3.
Proof. apply (stat_race_free_g _ 2 1000%positive); [wf_tac|vm_compute; reflexivity|vm_compute; reflexivity]. Qed.
Theorem TRAP4_race_free : race_free_g TRAP4.
Proof. apply (stat_race_free_g _ 3 1000%positive); [wf_tac|vm_compute; reflexivity|vm_compute; reflexivity]. Qed.
