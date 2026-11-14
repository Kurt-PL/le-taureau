(* Model2: tools for litmus programmes. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2.

Definition T : regs -> bool := fun _ => true.
Definition K (v : val) : regs -> val := fun _ => v.
Definition RG (j : nat) : regs -> val := fun r => r j.
Definition EQ (j : nat) (v : val) : regs -> bool := fun r => Nat.eqb (r j) v.
Definition NE (j : nat) (v : val) : regs -> bool := fun r => negb (Nat.eqb (r j) v).

Definition ld (x : cell) := ILd Plain [x] T.
Definition st (x : cell) v := ISt Plain [x] T (K v).

(* one-cell accesses: the source of the cell, and the history of the cell *)
Definition src1 (x : cell) (o : option nat) : cell -> option nat :=
  fun y => if Nat.eqb y x then o else None.

(* a one-cell read takes a write of the cell's history or the initial value;
   a one-cell write enters the history at some place *)
Definition inhist (h : hist) (o : option nat) : Prop := match o with None => True | Some w => In w (ids h) end.
Definition place1 (h : hist) (t : nat) (h' : hist) : Prop := exists h1 h2, h = h1 ++ h2 /\ h' = h1 ++ (t, false) :: h2.

Lemma takes1 : forall H x o, inhist (H x) o -> takes H [x] (src1 x o).
Proof.
  intros H x o V. split.
  - intros y [<-|[]]. unfold src1. rewrite Nat.eqb_refl. exact V.
  - intros y N. unfold src1. destruct (Nat.eqb_spec y x); auto. subst. exfalso. apply N. left. auto.
Qed.

Lemma places1 : forall H x t h', place1 (H x) t h' -> places H [x] t (upd H x h').
Proof.
  intros H x t h' E y. split; intros Y.
  - destruct Y as [<-|[]]. unfold upd. rewrite Nat.eqb_refl. exact E.
  - unfold upd. destruct (Nat.eqb_spec y x); auto. subst. exfalso. apply Y. left. auto.
Qed.

Lemma e_ld1 : forall t md x c r m o, c r = true -> inhist (mH m x) o ->
  eff t (ILd md [x] c) r m (learn m (src1 x o)) (enc (rdvals m [x] (src1 x o))) (mP m) (src1 x o) false.
Proof. intros. apply e_ld; auto. apply takes1. auto. Qed.

Lemma e_st1 : forall t md x c v r m h', c r = true -> place1 (mH m x) t h' ->
  eff t (ISt md [x] c v) r m (wput m [x] t [v r] (upd (mH m) x h')) 0 (mP m) nosrc true.
Proof. intros. apply e_st; auto. apply places1. auto. Qed.

Lemma e_cas_ok1 : forall t md x c e n r m o h', c r = true -> inhist (mH m x) o ->
  enc (rdvals m [x] (src1 x o)) = e r -> place1 (mH m x) t h' ->
  eff t (ICas md [x] c e n) r m (wput (learn m (src1 x o)) [x] t [n r] (upd (mH m) x h'))
      (vd true (enc (rdvals m [x] (src1 x o)))) (mP m) (src1 x o) true.
Proof. intros. apply e_cas_ok; auto. - apply takes1. auto. - apply places1. auto. Qed.

Lemma e_cas_no1 : forall t md x c e n r m o, c r = true -> inhist (mH m x) o ->
  enc (rdvals m [x] (src1 x o)) <> e r ->
  eff t (ICas md [x] c e n) r m (learn m (src1 x o)) (vd false (enc (rdvals m [x] (src1 x o)))) (mP m) (src1 x o) false.
Proof. intros. apply e_cas_no; auto. apply takes1. auto. Qed.
Definition fll := IFn FLl.
Definition fss := IFn FSs.
Definition ffull := IFn FFull.

(* a programme with no branches: each context a list of instructions *)
Definition stat (P : list (list instr)) : prog := map (fun code => fun k (_ : regs) => nth k code INop) P.

Lemma ins_stat : forall P c k r, ins (stat P) c k r = nth k (nth c P []) INop.
Proof.
  intros P c k r. unfold ins, code, stat. revert c. induction P as [|a P IH]; intros c.
  - destruct c, k; reflexivity.
  - destruct c; simpl; auto.
Qed.

Lemma stat_fin : forall P, fin (stat P) (fun c => length (nth c P [])).
Proof. intros P c k r H. rewrite ins_stat. apply nth_overflow. auto. Qed.

(* deciding older on a concrete history *)
Definition olderb (h : hist) (a b : nat) : bool :=
  existsb (fun n => existsb (Nat.eqb a) (firstn n (ids h)) && existsb (Nat.eqb b) (skipn n (ids h)))
          (seq 0 (S (length h))).

Lemma existsb_eqb : forall l a, existsb (Nat.eqb a) l = true <-> In a l.
Proof.
  intros l a. rewrite existsb_exists. split.
  - intros (y & H & E). apply Nat.eqb_eq in E. subst. auto.
  - intros H. exists a. rewrite Nat.eqb_refl. auto.
Qed.

Lemma older_b : forall h a b, older h a b -> olderb h a b = true.
Proof.
  intros h a b H. apply older_split in H. destruct H as (l1 & l2 & E & A & B).
  unfold olderb. apply existsb_exists. exists (length l1). split.
  - apply in_seq. assert (length (ids h) = length h) by (unfold ids; apply length_map).
    rewrite E, length_app in H. lia.
  - rewrite E, firstn_app, Nat.sub_diag, firstn_all, skipn_app, Nat.sub_diag, skipn_all. simpl.
    rewrite app_nil_r. apply andb_true_intro. split; apply existsb_eqb; auto.
Qed.

Lemma not_older : forall h a b, olderb h a b = false -> ~ older h a b.
Proof. intros h a b H O. apply older_b in O. congruence. Qed.

Ltac det_tac := let r := fresh "r" in let Hs := fresh "Hs" in
  intros r Hs; split; [vm_compute; reflexivity|]; vm_compute;
  first [ reflexivity
        | repeat (rewrite Hs by (first [left; vm_compute; lia | right; let Z := fresh in intro Z; vm_compute in Z; discriminate])); vm_compute; reflexivity ].

(* no pending access is tied to the instruction i (the pending ones are
   among the first slots) *)
Ltac pend_tac := let k' := fresh "k'" in let d := fresh "d" in
  let P1 := fresh "P1" in let P2 := fresh "P2" in let P3 := fresh "P3" in
  intros k' d (P1 & P2 & P3);
  do 8 (destruct k' as [|k']; [try (exfalso; vm_compute in P1; lia); vm_compute in P2; try (exfalso; apply P2; reflexivity);
            rewrite <- P3; first [apply untied_b | split; apply untied_b]; vm_compute; reflexivity|]);
  exfalso; apply P2; vm_compute; reflexivity.

Ltac blk_tac := intros _; pend_tac.

(* no read counted on in these programmes *)
Ltac bnd_tac := intros;
  match goal with
  | H : bor _ _ _ = true |- _ => vm_compute in H; discriminate H
  | H : bd _ _ = true |- _ => vm_compute in H; discriminate H
  end.

(* R1 for an early access, at slot j in every way the context may go on *)
(* the effect an instruction records (constant parts only) *)
Definition dget (i : instr) : desc := match eof i (fun _ => 0) with Some d => d | None => DLd Plain [] end.

(* the pending accesses (among the first slots) are recorded as their
   effects, and lie below the bound N *)
Ltac pok_tac := let k := fresh "k" in let O := fresh "O" in let L := fresh "L" in
  intros k O L;
  do 8 (destruct k as [|k]; [first [exfalso; vm_compute in L; lia
                                  | exfalso; apply O; vm_compute; reflexivity
                                  | match goal with |- exists d, ?a = inst_of d /\ _ => exists (dget a); split; [vm_compute; reflexivity|discriminate] end]|]);
  exfalso; apply O; vm_compute; reflexivity.
Ltac nbd_tac := let k := fresh "k" in let O := fresh "O" in let L := fresh "L" in
  intros k O L;
  do 8 (destruct k as [|k]; [first [exfalso; vm_compute in L; lia
                                  | exfalso; apply O; vm_compute; reflexivity
                                  | vm_compute; lia]|]);
  exfalso; apply O; vm_compute; reflexivity.

(* the place, by the decidable form *)
(* the free verdict bits a computed check still depends on: split on each *)
Ltac has_fv t := match t with context [?F ?a ?b] => is_var F end.
Ltac bitsplit := repeat match goal with |- context [if ?c then _ else _] =>
  has_fv c;
  first [ match c with context [if ?c' then _ else _] => has_fv c'; fail 2 end
        | destruct c; vm_compute ] end.
Ltac fat_tac := match goal with |- first_at ?p ?c ?cc ?pc ?r ?T ?d ?j =>
  match r with creg _ _ _ _ ?N _ _ =>
    apply (proj1 (first_atb_iff p c cc pc N r T d j ltac:(pok_tac) ltac:(nbd_tac) ltac:(nbd_tac))); vm_compute; bitsplit; reflexivity end end.

Ltac eok_tac j := let f := fresh "f" in intros f; cbv zeta; exists j; split; [vm_compute; lia|]; split;
  [fat_tac
  |let X := fresh "X" in intros X; first [discriminate X | bnd_tac]].

(* the access reached is the first, in time, of the pending accesses tied to it *)
Ltac first_tac := let k' := fresh "k'" in let d' := fresh "d'" in let t := fresh "t" in let t' := fresh "t'" in
  let P1 := fresh "P1" in let P2 := fresh "P2" in let P3 := fresh "P3" in
  let Ne := fresh "Ne" in let O := fresh "O" in let O' := fresh "O'" in let Ti := fresh "Ti" in
  intros k' d' t t' (P1 & P2 & P3) Ne O O' Ti;
  do 8 (destruct k' as [|k']; [vm_compute in P1, P2, Ne, O, O';
     first [exfalso; lia
           | exfalso; apply Ne; reflexivity
           | exfalso; apply P2; reflexivity
           | injection O as <-; injection O' as <-; first [lia | rewrite <- P3 in Ti; apply tied_b in Ti; vm_compute in Ti; discriminate Ti]]|]);
  exfalso; apply P2; vm_compute; reflexivity.

(* the place, by the decidable form, the bound N given (when the registers
   are abstracted) *)
Ltac fatN N := match goal with |- first_at ?p ?c ?cc ?pc ?r ?T ?d ?j =>
  apply (proj1 (first_atb_iff p c cc pc N r T d j ltac:(pok_tac) ltac:(nbd_tac) ltac:(nbd_tac))) end.

(* the pending accesses tied to the early access are recorded at earlier
   slots than k *)
Ltac slot_tac := let k' := fresh "k'" in let d' := fresh "d'" in
  let P1 := fresh "P1" in let P2 := fresh "P2" in let P3 := fresh "P3" in let Ti := fresh "Ti" in
  intros k' d' (P1 & P2 & P3) Ti;
  do 8 (destruct k' as [|k']; [vm_compute in P1, P2;
     first [exfalso; lia
           | exfalso; apply P2; reflexivity
           | vm_compute; lia
           | rewrite <- P3 in Ti; apply tied_b in Ti; vm_compute in Ti; discriminate Ti]|]);
  exfalso; apply P2; vm_compute; reflexivity.

(* no CAS's read happened alone *)
Ltac hblk_tac := let k' := fresh "k'" in let m := fresh "m" in let xs := fresh "xs" in
  let P1 := fresh "P1" in let P2 := fresh "P2" in let P3 := fresh "P3" in let P4 := fresh "P4" in
  intros _ k' m xs (P1 & P2 & P3); exfalso; apply P2; vm_compute; reflexivity.
Ltac hfirst_tac := let k' := fresh "k'" in let m := fresh "m" in let xs := fresh "xs" in
  let t := fresh "t" in let t' := fresh "t'" in
  let P1 := fresh "P1" in let P2 := fresh "P2" in let P3 := fresh "P3" in let P4 := fresh "P4" in
  intros k' m xs t t' (P1 & P2 & P3) _; exfalso; apply P2; vm_compute; reflexivity.
(* no result fixed (S3c) at the slot passed *)
Ltac fx_tac := let b := fresh "b" in let E := fresh "E" in intros b E; vm_compute in E; discriminate E.
(* a result fixed (S3c) at the slot passed, or none: the register agrees *)
Ltac fxk_tac := let b := fresh "b" in let E := fresh "E" in
  intros b E; vm_compute in E; first [discriminate E | injection E as <-; intros; vm_compute; reflexivity].
Ltac fxe_tac := let f := fresh "f" in let j := fresh "j" in let F := fresh "F" in let b := fresh "b" in
  let E := fresh "E" in let Ci := fresh "Ci" in
  intros f j F b E Ci; first [vm_compute in E; discriminate E | vm_compute in Ci; discriminate Ci].
(* s_cread with no result fixed at its place: the record is a success *)
Ltac fxr_tac := let f := fresh "f" in let j := fresh "j" in let F := fresh "F" in
  intros f j F; split; [vm_compute; reflexivity|
    let b := fresh "b" in let E := fresh "E" in let Ci := fresh "Ci" in
    intros b E Ci; first [vm_compute in E; discriminate E | vm_compute in Ci; discriminate Ci]].
Ltac ord c := eapply (s_ord _ _ c); [vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; reflexivity|det_tac|blk_tac|hblk_tac|bnd_tac| |fx_tac].
(* pass a non-executing instruction: nothing logged *)
Ltac skip c := eapply (s_skip _ _ c); [vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; reflexivity
  |let Z := fresh in intro Z; exfalso; apply Z; vm_compute; reflexivity
  |let Z := fresh in intro Z; exfalso; apply Z; vm_compute; reflexivity
  |let t1 := fresh "t1" in let O := fresh "O" in intros t1 O; exfalso; vm_compute in O; discriminate O|det_tac|fx_tac].
(* no CAS's read happened alone *)
Ltac hp_tac := let f := fresh "f" in let j := fresh "j" in let X := fresh "X" in
  intros f j X; vm_compute; reflexivity.
Ltac early c k d j := eapply (s_early _ _ c k d (fun _ => false));
  [vm_compute; lia|vm_compute; reflexivity|vm_compute; reflexivity|slot_tac|eok_tac j| |fxe_tac].
Ltac mtch c d := eapply (s_match _ _ c d);
  [let H := fresh in intro H; vm_compute in H; discriminate H|vm_compute; reflexivity|vm_compute; reflexivity|det_tac|first_tac|hfirst_tac|fx_tac].

(* knowledge hypotheses become equalities *)
Ltac kn' H :=
  match type of H with
  | _ \/ _ => let H1 := fresh "H" in destruct H as [H1|H1]; kn' H1
  | False => destruct H
  | exists _, _ => let z := fresh "z" in let H1 := fresh "H" in destruct H as [z H1]; kn' H1
  | _ /\ _ => let H1 := fresh "H" in let H2 := fresh "H" in destruct H as [H1 H2]; kn' H1; kn' H2
  | context [if ?b then _ else _] => destruct b; vm_compute in H; kn' H
  | Some _ = Some _ => injection H as H; kn' H
  | None = Some _ => discriminate H
  | Some _ = None => discriminate H
  | _ => idtac
  end.
Ltac kn H := vm_compute in H; kn' H.

Ltac vis_some := vm_compute; tauto.
Ltac vis_none := exact I.
Ltac enter_at h1 h2 := exists h1, h2; split; vm_compute; reflexivity.

(* building runs forward, keeping the state in normal form *)
Inductive star (p : prog) : M2Model.st -> M2Model.st -> Prop :=
| st0 : forall s, star p s s
| stS : forall s s1 t, step p s s1 -> star p s1 t -> star p s t.

Lemma star_run : forall p s t, run p s -> star p s t -> run p t.
Proof. intros p s t R H. induction H; auto. apply IHstar. econstructor; eauto. Qed.

Lemma start : forall p (Q : M2Model.st -> Prop), (exists t, star p sinit t /\ Q t) -> exists t, run p t /\ Q t.
Proof. intros p Q (t & H & q). exists t. split; auto. eapply star_run; eauto. constructor. Qed.

Lemma fwd : forall p s s1 (Q : M2Model.st -> Prop), step p s s1 -> (exists t, star p s1 t /\ Q t) ->
  exists t, star p s t /\ Q t.
Proof. intros p s s1 Q H (t & A & B). exists t. split; auto. econstructor; eauto. Qed.

Ltac norm := match goal with |- exists t, star _ ?S t /\ _ =>
  let S' := eval vm_compute in S in change S with S' end.

Ltac finish := eexists; split; [apply st0|].

Ltac tie := apply b_tied; vm_compute; reflexivity.

Lemma wf_stat : forall P, (forall c k r r', (forall j, j < k -> r j = r' j) ->
  ieval (nth k (nth c P []) INop) r = ieval (nth k (nth c P []) INop) r') -> wf (stat P).
Proof. intros P H c k r r' E. rewrite !ins_stat. split; auto. Qed.

Ltac wf_tac := let c := fresh "c" in let k := fresh "k" in
  let r := fresh "r" in let r' := fresh "r'" in let E := fresh "E" in
  apply wf_stat; intros c k r r' E;
  destruct c as [|[|[|[|[|c]]]]]; destruct k as [|[|[|[|[|[|k]]]]]]; simpl;
  unfold ieval, T, K, RG, EQ, NE; try reflexivity;
  repeat (rewrite E by lia); try reflexivity;
  destruct (nth c _ _); simpl; try reflexivity; destruct k; reflexivity.

Ltac done_tac := eexists; split; [apply stat_fin|];
  let c := fresh "c" in let Hc := fresh "Hc" in let k := fresh "k" in let Hk := fresh "Hk" in
  intros c Hc; destruct c as [|[|[|[|[|]]]]]; cbn in *; try lia;
  (split; [lia|intros k Hk;
    do 8 (destruct k as [|k]; [vm_compute in Hk; try lia; vm_compute; split; reflexivity|]); vm_compute; split; reflexivity]).
