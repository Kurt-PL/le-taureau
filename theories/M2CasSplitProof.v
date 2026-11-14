(* Model2, a CAS in two parts: tactics and lemmas for runs whose CAS's read happens
   alone. Runs are built with every state named (no state is normalised);
   places and registers that depend on free values are built by hand. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Lit M2Ev M2EvLit M2Oota.

Ltac W0 := enter_at (@nil (nat * bool)) (@nil (nat * bool)).
Ltac LD u := eapply (e_ld1 _ _ _ _ _ _ u); [reflexivity|].
Ltac ST := eapply e_st1; [reflexivity|].
Ltac SKIP := apply e_skip; reflexivity.
(* the state after a step, named: the run stays a chain of small terms and
   no whole state is normalised *)
Ltac nameS := match goal with |- exists t, star _ ?S t /\ _ =>
  let s := fresh "s" in set (s := S) end.

(* the CASes whose read happened alone are not tied to the instruction *)
Ltac hblk_gen := let k' := fresh "k'" in let m := fresh "m" in let xs := fresh "xs" in
  let P1 := fresh "P1" in let P2 := fresh "P2" in let P3 := fresh "P3" in
  intros k' m xs (P1 & P2 & P3);
  do 8 (destruct k' as [|k']; [vm_compute in P1, P2;
     first [exfalso; lia
           | exfalso; apply P2; reflexivity
           | vm_compute in P3; injection P3 as <- <-; apply untied_b; vm_compute; reflexivity]|]);
  exfalso; apply P2; vm_compute; reflexivity.
Ltac hblk_ne := let k' := fresh "k'" in let m := fresh "m" in let xs := fresh "xs" in
  let P1 := fresh "P1" in let P2 := fresh "P2" in let P3 := fresh "P3" in let Ne := fresh "Ne" in
  intros k' m xs (P1 & P2 & P3) Ne;
  do 8 (destruct k' as [|k']; [vm_compute in P1, P2, Ne;
     first [exfalso; lia
           | exfalso; apply Ne; reflexivity
           | exfalso; apply P2; reflexivity
           | vm_compute in P3; injection P3 as <- <-; apply untied_b; vm_compute; reflexivity]|]);
  exfalso; apply P2; vm_compute; reflexivity.
(* the access reached happened before the CASes' reads tied to it *)
Ltac hfirst_gen := let k' := fresh "k'" in let m := fresh "m" in let xs := fresh "xs" in
  let t := fresh "t" in let t' := fresh "t'" in
  let P1 := fresh "P1" in let P2 := fresh "P2" in let P3 := fresh "P3" in
  let Ne := fresh "Ne" in let O := fresh "O" in let O' := fresh "O'" in let Ti := fresh "Ti" in
  intros k' m xs t t' (P1 & P2 & P3) Ne O O' Ti;
  do 8 (destruct k' as [|k']; [vm_compute in P1, P2, Ne, O, O';
     first [exfalso; lia
           | exfalso; apply Ne; reflexivity
           | exfalso; apply P2; reflexivity
           | injection O as <-; injection O' as <-;
             first [lia | vm_compute in P3; injection P3 as <- <-; apply tied_b in Ti; vm_compute in Ti; discriminate Ti]]|]);
  exfalso; apply P2; vm_compute; reflexivity.

(* the instruction is determined: computed lazily once the passed
   registers are put in *)
Ltac detH := let r := fresh "r" in let Hs := fresh "Hs" in
  intros r Hs; split; [vm_compute; reflexivity|]; vm_compute;
  first [ reflexivity
        | repeat (rewrite Hs by (first [left; vm_compute; lia | right; let Z := fresh in intro Z; vm_compute in Z; discriminate])); reflexivity ].

Ltac ordH c := eapply (s_ord _ _ c);
  [vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; reflexivity|detH|blk_tac|intros _; hblk_gen|bnd_tac| |fx_tac].
Ltac skipH c := eapply (s_skip _ _ c); [vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; reflexivity
  |first [let Z := fresh in intro Z; exfalso; apply Z; vm_compute; reflexivity|intros _; vm_compute; reflexivity]
  |first [let Z := fresh in intro Z; exfalso; apply Z; vm_compute; reflexivity|intros _; vm_compute; reflexivity]
  |let t1 := fresh "t1" in let O := fresh "O" in intros t1 O; exfalso; vm_compute in O; discriminate O|detH|fx_tac].
(* passing a CAS whose read happened alone and whose comparison fails: the
   pending accesses and reads alone tied to it happened after its read *)
Ltac hfirstF := let t1 := fresh "t1" in let O := fresh "O" in intros t1 O; vm_compute in O; injection O as <-; split;
  [ let k' := fresh "k'" in let d' := fresh "d'" in let t' := fresh "t'" in let P1 := fresh "P1" in
    let P2 := fresh "P2" in let P3 := fresh "P3" in let Ne := fresh "Ne" in let O' := fresh "O'" in let Ti := fresh "Ti" in
    intros k' d' t' (P1 & P2 & P3) Ne O' Ti;
    do 8 (destruct k' as [|k']; [vm_compute in P1, P2, Ne, O';
       first [exfalso; lia | exfalso; apply Ne; reflexivity | exfalso; apply P2; reflexivity
             | injection O' as <-; lia]|]);
    exfalso; apply P2; vm_compute; reflexivity
  | let k' := fresh "k'" in let m := fresh "m" in let xs := fresh "xs" in let t' := fresh "t'" in let P1 := fresh "P1" in
    let P2 := fresh "P2" in let P3 := fresh "P3" in let Ne := fresh "Ne" in let O' := fresh "O'" in let Ti := fresh "Ti" in
    intros k' m xs t' (P1 & P2 & P3) Ne O' Ti;
    do 8 (destruct k' as [|k']; [vm_compute in P1, P2, Ne, O';
       first [exfalso; lia | exfalso; apply Ne; reflexivity | exfalso; apply P2; reflexivity
             | injection O' as <-; lia]|]);
    exfalso; apply P2; vm_compute; reflexivity ].
(* a CAS whose read happened alone (record k, place j, value read v) fixes its
   result to failure (S3c): the record's register becomes a failure *)
Ltac cfailH c k j v := eapply (s_cfix _ _ c j false (fun _ => false) (Some k));
  [vm_compute; lia|vm_compute; reflexivity
  |exists v; let f := fresh "f" in intros f; cbv zeta; vm_compute; bitsplit;
   repeat split; first [reflexivity|let k := fresh "k" in let E := fresh "E" in intros k E; injection E as <-; reflexivity
                       |let E := fresh "E" in intros E; discriminate E]].
Ltac skipF c := eapply (s_skip _ _ c);
  [vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; reflexivity|intros _; vm_compute; reflexivity
  |intros _; vm_compute; reflexivity|hfirstF|detH|fxk_tac].
Ltac mtchH c d := eapply (s_match _ _ c d);
  [let H := fresh in intro H; vm_compute in H; discriminate H|vm_compute; reflexivity|vm_compute; reflexivity|detH|first_tac|hfirst_gen|fx_tac].
Ltac earlyH c k d j := eapply (s_early _ _ c k d (fun _ => false));
  [vm_compute; lia|vm_compute; reflexivity|vm_compute; reflexivity|slot_tac|eok_tac j| |fxe_tac].

(* the place of a CAS's read alone, by the decidable form *)
Ltac fatR_tac := match goal with |- first_atR ?p ?c ?cc ?pc ?r ?T ?m ?xs ?j =>
  match r with creg _ _ _ _ ?N _ _ =>
    apply (proj1 (fab_plc p c cc pc N r ltac:(pok_tac) ltac:(nbd_tac) ltac:(nbd_tac) (S T) T (TH m xs) j));
    vm_compute; bitsplit; reflexivity end end.
Ltac fatRN N := match goal with |- first_atR ?p ?c ?cc ?pc ?r ?T ?m ?xs ?j =>
  apply (proj1 (fab_plc p c cc pc N r ltac:(pok_tac) ltac:(nbd_tac) ltac:(nbd_tac) (S T) T (TH m xs) j)) end.
Ltac eokR_tac j := let f := fresh "f" in intros f; cbv zeta; exists j; split;
  [fatR_tac
  |let x := fresh "x" in let b := fresh "b" in let X := fresh "X" in intros x b _ X; vm_compute in X; discriminate X].
(* a CAS's read alone, at slot k, its place j *)
Ltac cread c k xs j := eapply (s_cread _ _ c k Plain xs (fun _ => false) _ _ _ _ _ true);
  [vm_compute; lia|vm_compute; reflexivity|vm_compute; reflexivity|slot_tac|eokR_tac j| |fxr_tac].
(* the write of a CAS whose read happened alone, in order *)
Ltac cw c := eapply (s_cw _ _ c);
  [vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; reflexivity
  |vm_compute; reflexivity|detH|pend_tac|hblk_ne|vm_compute; reflexivity| |reflexivity|fx_tac].

(* ---------- two cells ---------- *)
Lemma dd2 : forall x y, x <> y -> dd [x; y] = [x; y].
Proof.
  intros x y N. unfold dd. cbn [nodup].
  destruct (in_dec Nat.eq_dec y []) as [[]|_].
  destruct (in_dec Nat.eq_dec x [y]) as [[E|[]]|_]; [congruence|reflexivity].
Qed.

Lemma places2 : forall H x y t hx hy, x <> y -> place1 (H x) t hx -> place1 (H y) t hy ->
  places H [x; y] t (upd (upd H x hx) y hy).
Proof.
  intros H x y t hx hy N Ex Ey z. split; intros Z.
  - destruct Z as [<-|[<-|[]]]; unfold upd.
    + destruct (Nat.eqb_spec x y); [congruence|]. rewrite Nat.eqb_refl. exact Ex.
    + rewrite Nat.eqb_refl. exact Ey.
  - unfold upd. destruct (Nat.eqb_spec z y); [subst; exfalso; apply Z; right; left; auto|].
    destruct (Nat.eqb_spec z x); [subst; exfalso; apply Z; left; auto|auto].
Qed.

Definition src2 (x : cell) (ox : option nat) (y : cell) (oy : option nat) : cell -> option nat :=
  fun z => if Nat.eqb z x then ox else if Nat.eqb z y then oy else None.

Lemma takes2 : forall H x y ox oy, x <> y -> inhist (H x) ox -> inhist (H y) oy ->
  takes H [x; y] (src2 x ox y oy).
Proof.
  intros H x y ox oy N Vx Vy. split.
  - intros z [<-|[<-|[]]]; unfold src2; [rewrite Nat.eqb_refl; exact Vx|].
    destruct (Nat.eqb_spec y x); [congruence|]. rewrite Nat.eqb_refl. exact Vy.
  - intros z Z. unfold src2. destruct (Nat.eqb_spec z x); [subst; exfalso; apply Z; left; auto|].
    destruct (Nat.eqb_spec z y); [subst; exfalso; apply Z; right; left; auto|auto].
Qed.

Lemma e_st2 : forall t md x y c v r m hx hy, x <> y -> c r = true ->
  place1 (mH m x) t hx -> place1 (mH m y) t hy ->
  eff t (ISt md [x; y] c v) r m
      (wput m (dd [x; y]) t (projs (length (dd [x; y])) (v r)) (upd (upd (mH m) x hx) y hy)) 0 (mP m) nosrc true.
Proof.
  intros t md x y c v r m hx hy N C Ex Ey. apply e_st; [exact C|].
  rewrite (dd2 x y N). apply places2; auto.
Qed.

Lemma e_ld2 : forall t md x y c r m ox oy, x <> y -> c r = true ->
  inhist (mH m x) ox -> inhist (mH m y) oy ->
  eff t (ILd md [x; y] c) r m (learn m (src2 x ox y oy)) (enc (rdvals m (dd [x; y]) (src2 x ox y oy)))
      (mP m) (src2 x ox y oy) false.
Proof.
  intros t md x y c r m ox oy N C Vx Vy. apply e_ld; [exact C|]. rewrite (dd2 x y N). apply takes2; auto.
Qed.

Lemma e_cas_ok2 : forall t md x y c e n r m ox oy hx hy, x <> y -> c r = true ->
  inhist (mH m x) ox -> inhist (mH m y) oy ->
  enc (rdvals m (dd [x; y]) (src2 x ox y oy)) = e r ->
  place1 (mH m x) t hx -> place1 (mH m y) t hy ->
  eff t (ICas md [x; y] c e n) r m
      (wput (learn m (src2 x ox y oy)) (dd [x; y]) t (projs (length (dd [x; y])) (n r)) (upd (upd (mH m) x hx) y hy))
      (vd true (enc (rdvals m (dd [x; y]) (src2 x ox y oy)))) (mP m) (src2 x ox y oy) true.
Proof.
  intros t md x y c e n r m ox oy hx hy N C Vx Vy E Ex Ey. apply e_cas_ok; auto.
  - rewrite (dd2 x y N). apply takes2; auto.
  - rewrite (dd2 x y N). apply places2; auto.
Qed.

(* the write of a CAS whose read happened alone, early *)
Ltac cwe c k t1 xs ev nv := eapply (s_cwe _ _ c k t1 xs ev nv (fun _ => false));
  [vm_compute; lia|vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; reflexivity|slot_tac| |vm_compute; reflexivity| |reflexivity|fxe_tac].
(* ---------- places and registers without normalising free values ---------- *)
Lemma no_taken : forall p c cc pc r T j, (forall k, oc cc k = None) -> ~ taken p c cc pc r T j.
Proof. intros p c cc pc r T j H (k & t & d & (_ & O & _) & _). apply O. apply H. Qed.

Lemma no_htaken_at : forall p c cc pc r T j, eofR (ins p c j r) r = None -> ~ htaken p c cc pc r T j.
Proof.
  intros p c cc pc r T j E (k & t & m & xs & _ & _ & _ & _ & F). apply first_atR_eofR in F. congruence.
Qed.

Lemma no_htaken_before : forall p c cc pc r T j, (forall k t, oh cc k = Some t -> T <= t) -> ~ htaken p c cc pc r T j.
Proof. intros p c cc pc r T j H (k & t & m & xs & _ & O & L & _). pose proof (H k t O). lia. Qed.

Lemma fatR_by : forall p c cc pc r T m xs j, pc <= j -> eofR (ins p c j r) r = Some (m, xs) ->
  ~ taken p c cc pc r T j -> ~ htaken p c cc pc r T j ->
  (forall j', pc <= j' -> j' < j -> executes (ins p c j' r) r = true ->
     (forall v, htakenv p c cc pc r T j' v -> cfailv (ins p c j' r) r v = false) ->
     tied (ins p c j' r) (crd m xs) -> taken p c cc pc r T j') ->
  first_atR p c cc pc r T m xs j.
Proof.
  intros p c cc pc r T m xs j L E N1 N2 B. unfold first_atR. apply plc_in.
  split; [exact L|]. split; [exact E|]. split; [intros [X|X]; auto|exact B].
Qed.

Lemma fat_by : forall p c cc pc r T d j, pc <= j -> eof (ins p c j r) r = Some d ->
  ~ taken p c cc pc r T j -> ~ htaken p c cc pc r T j ->
  (forall j', pc <= j' -> j' < j -> executes (ins p c j' r) r = true ->
     (forall v, htakenv p c cc pc r T j' v -> cfailv (ins p c j' r) r v = false) ->
     tied (ins p c j' r) (inst_of d) -> taken p c cc pc r T j') ->
  first_at p c cc pc r T d j.
Proof.
  intros p c cc pc r T d j L E N1 N2 B. unfold first_at. apply plc_in.
  split; [exact L|]. split; [exact E|]. split; [intros [X|X]; auto|exact B].
Qed.

Lemma pend_none0 : forall p c cc N r j, (forall k, oc cc k = None) -> pend_at p c cc 0 N r j = None.
Proof.
  intros p c cc N r j Hn. unfold pend_at. induction (seq 0 (N - 0)) as [|a l IH]; simpl; [reflexivity|].
  rewrite Hn. exact IH.
Qed.

Lemma find_app_none : forall {A} (g : A -> bool) l1 l2, find g l1 = None -> find g (l1 ++ l2) = find g l2.
Proof. intros A g l1 l2. induction l1 as [|a l1 IH]; simpl; [auto|]. destruct (g a); [discriminate|exact IH]. Qed.

Lemma find_cons_true : forall {A} (g : A -> bool) a l, g a = true -> find g (a :: l) = Some a.
Proof. intros A g a l H. simpl. rewrite H. reflexivity. Qed.

(* the CAS whose read happened alone at slot k, the only one, is placed at j *)
Lemma hpend_one : forall p c cc N r j k t m xs, (forall k', oc cc k' = None) ->
  (forall k' t', oh cc k' = Some t' -> k' = k) -> k < N -> oh cc k = Some t -> casx (ai cc k) = Some (m, xs) ->
  plc p c cc 0 r (S t) t (TH m xs) j -> hpend_at p c cc 0 N r j = Some k.
Proof.
  intros p c cc N r j k t m xs Hc Hh Lk Ok Cx P.
  assert (F : fab p c cc 0 N r (S t) t (TH m xs) j = true).
  { apply (proj2 (fab_plc p c cc 0 N r ltac:(intros k' O; exfalso; apply O; apply Hc)
                          ltac:(intros k' O; exfalso; apply O; apply Hc)
                          ltac:(intros k' O _; destruct (oh cc k') as [t'|] eqn:E; [rewrite (Hh k' t' E); exact Lk|congruence])
                          (S t) t (TH m xs) j)).
    exact P. }
  unfold hpend_at. rewrite Nat.sub_0_r.
  assert (Q : forall l, (forall a, In a l -> a <> k) -> find (fun k0 => match oc cc k0, oh cc k0 with
                 | None, Some t0 => match casx (ai cc k0) with
                                    | Some (m0, xs0) => fab p c cc 0 N r (S t0) t0 (TH m0 xs0) j
                                    | None => false end
                 | _, _ => false end) l = None).
  { induction l as [|a l IH]; intros A; [reflexivity|]. simpl. rewrite Hc.
    destruct (oh cc a) as [ta|] eqn:Ea; [exfalso; apply (A a (or_introl eq_refl)); apply (Hh a ta Ea)|].
    apply IH. intros b Ib. apply A. right. exact Ib. }
  assert (Sq : seq 0 N = seq 0 k ++ k :: seq (S k) (N - S k)).
  { replace N with (k + S (N - S k)) at 1 by lia. rewrite seq_app. reflexivity. }
  rewrite Sq.
  rewrite find_app_none.
  - apply find_cons_true. cbv beta. rewrite Hc, Ok, Cx. exact F.
  - apply Q. intros a Ia. apply in_seq in Ia. lia.
Qed.

Lemma creg_h : forall p c cc pc N B f j k, pc <= j ->
  is_load (ins p c j (lreg (bl p c cc pc N B f j))) && icond (ins p c j (lreg (bl p c cc pc N B f j))) (lreg (bl p c cc pc N B f j)) = true ->
  pend_at p c cc pc N (lreg (bl p c cc pc N B f j)) j = None ->
  hpend_at p c cc pc N (lreg (bl p c cc pc N B f j)) j = Some k ->
  fx cc j = None ->
  creg p c cc pc N B f j =
  (let r := lreg (bl p c cc pc N B f j) in
   if vok (rg cc k) then vd (negb (cfailv (ins p c j r) r (rg cc k)) && fbit f (ins p c j r) j) (vv (rg cc k)) else rg cc k).
Proof.
  intros p c cc pc N B f j k L X P H Fx. rewrite creg_bl. unfold slotv.
  destruct (Nat.ltb_spec j pc); [lia|]. rewrite X, P, H. rewrite !cfx_unfold. rewrite Fx. reflexivity.
Qed.

Lemma creg_off : forall p c cc pc N B f j, pc <= j ->
  is_load (ins p c j (lreg (bl p c cc pc N B f j))) && icond (ins p c j (lreg (bl p c cc pc N B f j))) (lreg (bl p c cc pc N B f j)) = false ->
  creg p c cc pc N B f j = 0.
Proof.
  intros p c cc pc N B f j L X. rewrite creg_bl. unfold slotv.
  destruct (Nat.ltb_spec j pc); [lia|]. rewrite X. reflexivity.
Qed.

