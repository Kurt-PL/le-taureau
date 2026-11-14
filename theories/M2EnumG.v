(* EnumG: Enum.v with races in the sense of racy_g: a race record carries
   whether its access is a fenced access, and a pair of fenced accesses is
   not a race.
   A checked enumeration of the interleavings of a programme with a bounded
   number of instructions per context: a finite set S of abstract states,
   closed under every step, proves the programme race-free and bounds the
   registers its interleavings can produce. S is computed by an unverified
   search; only the closure check is trusted, and it is proved sound here. *)
From Stdlib Require Import Arith Lia List Bool PArith.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2SC.

(* ---------- lists as finite maps ---------- *)
Fixpoint lset {A} (d : A) (l : list A) (i : nat) (v : A) : list A :=
  match i, l with
  | 0, [] => [v]
  | 0, _ :: t => v :: t
  | S i', [] => d :: lset d [] i' v
  | S i', h :: t => h :: lset d t i' v
  end.

Lemma nth_nil_d : forall A k (d : A), nth k [] d = d.
Proof. intros A [|k] d; reflexivity. Qed.

Lemma nth_lset : forall A (d : A) i l v k, nth k (lset d l i v) d = if Nat.eqb k i then v else nth k l d.
Proof.
  intros A d i. induction i as [|i IH]; intros [|h t] v [|k]; simpl; try reflexivity.
  - apply nth_nil_d.
  - rewrite IH. destruct (Nat.eqb k i); auto. rewrite !nth_nil_d. reflexivity.
  - apply IH.
Qed.

Definition bget (b : list bool) (i : nat) : bool := nth i b false.
Definition bset (b : list bool) (i : nat) : list bool := lset false b i true.
Fixpoint bor (a b : list bool) : list bool :=
  match a, b with
  | [], _ => b
  | _, [] => a
  | x :: a', y :: b' => (x || y) :: bor a' b'
  end.

Lemma bget_bset : forall b i j, bget (bset b i) j = if Nat.eqb j i then true else bget b j.
Proof. intros. unfold bget, bset. apply nth_lset. Qed.

Lemma bget_bset_mono : forall b i j, bget b j = true -> bget (bset b i) j = true.
Proof. intros b i j H. rewrite bget_bset. destruct (Nat.eqb j i); auto. Qed.

Lemma bget_bor : forall a b i, bget (bor a b) i = bget a i || bget b i.
Proof.
  unfold bget. induction a as [|x a IH]; intros [|y b] [|i]; simpl; auto;
    try (rewrite orb_false_r; reflexivity); rewrite ?nth_nil_d, ?orb_false_r; reflexivity.
Qed.

Lemma bget_nil : forall i, bget [] i = false.
Proof. intros. apply nth_nil_d. Qed.

Lemma nth_map_seq : forall A (f : nat -> A) n k d, k < n -> nth k (map f (seq 0 n)) d = f k.
Proof.
  intros A f n k d L. rewrite (nth_indep _ _ (f 0)) by (rewrite length_map, length_seq; auto).
  rewrite map_nth, seq_nth by auto. reflexivity.
Qed.

Fixpoint leqb {A} (f : A -> A -> bool) (a b : list A) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => f x y && leqb f a' b'
  | _, _ => false
  end.

Lemma leqb_eq : forall A (f : A -> A -> bool), (forall x y, f x y = true -> x = y) ->
  forall a b, leqb f a b = true -> a = b.
Proof.
  intros A f F. induction a as [|x a IH]; intros [|y b] H; simpl in H; try discriminate; auto.
  apply andb_prop in H. destruct H as [H1 H2]. f_equal; auto.
Qed.

Lemma beq_eq : forall x y, Bool.eqb x y = true -> x = y.
Proof. intros. apply Bool.eqb_prop. auto. Qed.
Lemma neq_eq : forall x y, Nat.eqb x y = true -> x = y.
Proof. intros. apply Nat.eqb_eq. auto. Qed.

(* the cell of a one-cell access event; the last component, whether the access slot is fenced,
   is set by accx *)
Definition sacc1 (e : sev) : option (cell * bool * bool) :=
  match sacc e with Some (xs, w) => match xs with [x] => Some (x, w, false) | _ => None end | None => None end.

(* ---------- the bound on the programme ---------- *)
Section En.
Variable p : prog.
Variable lens : list nat.
Variable M : nat.
Hypothesis W : wf p.
Hypothesis Hfin : forall c k r, nth c lens 0 <= k -> ins p c k r = INop.
Hypothesis Hout : forall c k r, length lens <= c -> ins p c k r = INop.
(* cells a context may still access from instruction k on: race records of
   cells nobody can access any more are dropped *)
Variable fut : nat -> nat -> list cell.
Hypothesis Hfut : forall c k r x, In x (icells (ins p c k r)) -> In x (fut c k).
(* every access names one cell: the checker handles one-cell programmes *)
Hypothesis Hone : forall c k r, isacc (ins p c k r) = true -> exists x, icells (ins p c k r) = [x].
Hypothesis Hmono : forall c k x, In x (fut c (S k)) -> In x (fut c k).
(* a decided under-approximation of fenced access slots *)
Variable ex : nat -> nat -> bool.
Hypothesis Hex : forall c k, ex c k = true -> fa p c k.
Definition accx (acc : option (cell * bool * bool)) (c k : nat) : option (cell * bool * bool) :=
  match acc with Some (x, w, _) => Some (x, w, ex c k) | None => None end.

Local Abbreviation N := (length lens).
Local Abbreviation len c := (nth c lens 0).

Record ast := mkA { apc : list nat; arg : list (list nat); amem : list nat;
                    aA : list (list bool); aB : list (list (list bool)) }.

Definition ast_eqb (a b : ast) : bool :=
  leqb Nat.eqb (apc a) (apc b) && leqb (leqb Nat.eqb) (arg a) (arg b) && leqb Nat.eqb (amem a) (amem b)
  && leqb (leqb Bool.eqb) (aA a) (aA b) && leqb (leqb (leqb Bool.eqb)) (aB a) (aB b).

Lemma ast_eqb_eq : forall a b, ast_eqb a b = true -> a = b.
Proof.
  intros [a1 a2 a3 a4 a5] [b1 b2 b3 b4 b5] H. unfold ast_eqb in H. simpl in H.
  repeat (apply andb_prop in H; destruct H as [H ?]).
  repeat match goal with
  | H : leqb _ _ _ = true |- _ => apply leqb_eq in H;
      [|first [exact neq_eq | exact beq_eq | apply leqb_eq; first [exact neq_eq | exact beq_eq | apply leqb_eq; exact beq_eq]]]
  end. subst. reflexivity.
Qed.

Definition amemb (S : list ast) (a : ast) : bool := existsb (ast_eqb a) S.
Lemma amemb_in : forall S a, amemb S a = true -> In a S.
Proof.
  intros S a H. apply existsb_exists in H. destruct H as (b & I & E). apply ast_eqb_eq in E. subst. auto.
Qed.

Definition rl (l : list nat) : regs := fun j => nth j l 0.
Definition bidx (x : cell) (w g : bool) : nat := x * 4 + (if w then 2 else 0) + (if g then 1 else 0).

Definition aget (a : ast) (c : nat) : list bool := nth c (aA a) [].
Definition bgt (a : ast) (c1 c2 : nat) : list bool := nth c2 (nth c1 (aB a) []) [].

Definition accbits (acc : option (cell * bool * bool)) (b : list bool) : list bool :=
  match acc with Some (x, w, g) => bset b (bidx x w g) | None => b end.

(* accesses since the last guard operation of c1; released accesses of c1
   that c2 has not yet taken *)
Definition newA (a : ast) (c : nat) acc (g : bool) (c1 : nat) : list bool :=
  if Nat.eqb c1 c then (if g then [] else accbits acc (aget a c)) else aget a c1.
Definition newB (a : ast) (c : nat) acc (g : bool) (c1 c2 : nat) : list bool :=
  if g then (if Nat.eqb c1 c then bor (bgt a c c2) (accbits acc (aget a c))
             else if Nat.eqb c2 c then [] else bgt a c1 c2)
  else bgt a c1 c2.

Definition hit (b : list bool) (x : cell) (w g : bool) : bool :=
  existsb (fun wg => let '(w1, g1) := wg in bget b (bidx x w1 g1) && (w1 || w) && negb (g1 && g))
    [(false, false); (false, true); (true, false); (true, true)].

Lemma hit_of : forall b x w g w1 g1, bget b (bidx x w1 g1) = true -> (w1 || w) = true -> (g1 && g) = false ->
  hit b x w g = true.
Proof.
  intros b x w g w1 g1 H1 H2 H3. unfold hit. apply existsb_exists. exists (w1, g1).
  split; [destruct w1, g1; simpl; tauto|]. rewrite H1, H2, H3. reflexivity.
Qed.

Definition race_hit (a : ast) (c : nat) acc (g : bool) : bool :=
  match acc with
  | Some (x, w, gg) => existsb (fun c1 => negb (Nat.eqb c1 c) &&
                         (hit (aget a c1) x w gg || (negb g && hit (bgt a c1 c) x w gg))) (seq 0 N)
  | None => false
  end.

(* the abstract event of an instruction; the last component of the access, whether its slot is
   fenced, is set by accx *)
Definition aev (i : instr) (r : regs) (mem : list nat) (sb : bool) :
  option (cell * bool * bool) * bool * option nat * option (cell * nat) :=
  match i with
  | ILd md xs cn => let x := hd 0 (dd xs) in
      if cn r then (Some (x, false, false), false, Some (nth x mem 0), None) else (None, false, None, None)
  | ISt md xs cn v => let x := hd 0 (dd xs) in
      if cn r then (Some (x, true, false), false, None, Some (x, v r)) else (None, false, None, None)
  | ICas md xs cn e n => let x := hd 0 (dd xs) in
      if cn r then let ok := Nat.eqb (nth x mem 0) (e r) && sb in
        (Some (x, ok, false), false, Some (vd ok (nth x mem 0)), if ok then Some (x, n r) else None)
      else (None, false, None, None)
  | IFn f => (None, match f with FFull => true | _ => false end, None, None)
  | INop => (None, false, None, None)
  end.

Definition cellbad (acc : option (cell * bool * bool)) : bool :=
  match acc with Some (x, _, _) => negb (Nat.ltb x M) | None => false end.

Fixpoint bfilt (f : cell -> bool) (i : nat) (b : list bool) : list bool :=
  match b with [] => [] | h :: t => (h && f (Nat.div i 4)) :: bfilt f (S i) t end.

(* drop trailing unset bits, so that equal sets are equal lists *)
Fixpoint trim (b : list bool) : list bool :=
  match b with
  | [] => []
  | h :: t => match h, trim t with false, [] => [] | _, t' => h :: t' end
  end.

Lemma bget_trim : forall b i, bget (trim b) i = bget b i.
Proof.
  unfold bget. induction b as [|h t IH]; intros i; [reflexivity|]. simpl.
  destruct h; [destruct i; simpl; auto|].
  specialize (IH (pred i)). destruct (trim t) as [|h' t'];
    destruct i; simpl in *; auto; rewrite <- IH; destruct i; reflexivity.
Qed.

Definition inq (a : ast) (c2 : nat) (x : cell) : bool := existsb (Nat.eqb x) (fut c2 (nth c2 (apc a) 0)).

Definition prune (a : ast) : ast :=
  mkA (apc a) (arg a) (amem a)
    (map (fun c1 => trim (bfilt (fun x => existsb (fun c2 => negb (Nat.eqb c2 c1) && inq a c2 x) (seq 0 N)) 0 (nth c1 (aA a) []))) (seq 0 N))
    (map (fun c1 => map (fun c2 => trim (bfilt (inq a c2) 0 (nth c2 (nth c1 (aB a) []) []))) (seq 0 N)) (seq 0 N)).

(* sb: the free choice of a CAS whose values are equal (spurious failure) *)
Definition sbw (e : sev) : bool := match sacc e with Some (_, w) => w | None => true end.

Definition astep (c : nat) (sb : bool) (a : ast) : ast * bool :=
  let k := nth c (apc a) 0 in
  let rs := nth c (arg a) [] in
  match aev (ins p c k (rl rs)) (rl rs) (amem a) sb with
  | (acc0, g, rw, mw) =>
    let acc := accx acc0 c k in
    (prune (mkA (lset 0 (apc a) c (S k))
         (match rw with Some v => lset [] (arg a) c (lset 0 rs k v) | None => arg a end)
         (match mw with Some (x, v) => lset 0 (amem a) x v | None => amem a end)
         (map (newA a c acc g) (seq 0 N))
         (map (fun c1 => map (newB a c acc g c1) (seq 0 N)) (seq 0 N))),
     race_hit a c acc g || cellbad acc0)
  end.

Definition active (a : ast) (c : nat) : bool := Nat.ltb c N && Nat.ltb (nth c (apc a) 0) (len c).

Definition ainit : ast :=
  mkA (repeat 0 N) (repeat [] N) [] (repeat [] N) (map (fun _ => map (fun _ => []) (seq 0 N)) (seq 0 N)).

Definition closed (S : list ast) : bool :=
  amemb S ainit &&
  forallb (fun a => forallb (fun c => if active a c then
                                        forallb (fun sb => match astep c sb a with (b, bad) => negb bad && amemb S b end) [true; false]
                                      else true) (seq 0 N)) S.

(* the unverified search *)
Definition succs (a : ast) : list ast :=
  flat_map (fun c => if active a c then [fst (astep c true a); fst (astep c false a)] else []) (seq 0 N).
Fixpoint explore (fuel : nat) (todo seen : list ast) : list ast :=
  match fuel with
  | 0 => seen
  | S f => match todo with
           | [] => seen
           | a :: t => if amemb seen a then explore f t seen else explore f (succs a ++ t) (a :: seen)
           end
  end.

(* ---------- what an abstract state says about an interleaving ---------- *)
Definition hasg (l : list sev) (i c1 : nat) : Prop :=
  exists i' f1, i <= i' /\ i' < length l /\ nth_error l i' = Some f1 /\ sg f1 = true /\ sx f1 = c1.
Definition gsb (l : list sev) (i c1 c2 : nat) : Prop :=
  exists i' j' f1 f2, i <= i' /\ i' <= j' /\ j' < length l /\
    nth_error l i' = Some f1 /\ nth_error l j' = Some f2 /\
    sg f1 = true /\ sg f2 = true /\ sx f1 = c1 /\ sx f2 = c2.

Definition hasgb (l : list sev) (i c1 : nat) : bool :=
  existsb (fun i' => match nth_error l i' with Some f => sg f && Nat.eqb (sx f) c1 | None => false end)
    (seq i (length l - i)).

Lemma hasgb_spec : forall l i c1, hasgb l i c1 = true <-> hasg l i c1.
Proof.
  intros l i c1. unfold hasgb, hasg. rewrite existsb_exists. split.
  - intros (i' & I & E). apply in_seq in I. destruct (nth_error l i') as [f|] eqn:Q; [|discriminate].
    apply andb_prop in E. destruct E as [E1 E2]. apply Nat.eqb_eq in E2. exists i', f. repeat split; auto; lia.
  - intros (i' & f & L1 & L2 & Q & S1 & S2). exists i'. split; [apply in_seq; lia|]. rewrite Q, S1, S2, Nat.eqb_refl. reflexivity.
Qed.

Definition RIq (Q : nat -> cell -> bool) (l : list sev) (a : ast) : Prop :=
  forall i e1 x w gg c2, nth_error l i = Some e1 -> sacc1 e1 = Some (x, w, gg) -> sx e1 < N -> c2 < N -> c2 <> sx e1 ->
    Q c2 x = true ->
    (~ hasg l i (sx e1) -> bget (aget a (sx e1)) (bidx x w (ex (sx e1) (sk e1))) = true) /\
    (~ gsb l i (sx e1) c2 -> bget (aget a (sx e1)) (bidx x w (ex (sx e1) (sk e1))) || bget (bgt a (sx e1) c2) (bidx x w (ex (sx e1) (sk e1))) = true).
Definition RI (l : list sev) (a : ast) : Prop := RIq (inq a) l a.

Record abs (l : list sev) (g : sst) (a : ast) : Prop := {
  a_pc : forall c, c < N -> nth c (apc a) 0 = Nat.min (sp g c) (len c);
  a_rg : forall c j, c < N -> j < len c -> nth j (nth c (arg a) []) 0 = sr g c j;
  a_mem : forall x, x < M -> nth x (amem a) 0 = sm g x;
  a_ri : RI l a }.

(* ---------- appending an event ---------- *)
Lemma nth_error_snoc : forall (l : list sev) e i x, nth_error (l ++ [e]) i = Some x ->
  (i < length l /\ nth_error l i = Some x) \/ (i = length l /\ x = e).
Proof.
  intros l e i x H. destruct (Nat.lt_ge_cases i (length l)) as [L|L].
  - left. rewrite nth_error_app1 in H by auto. auto.
  - right. rewrite nth_error_app2 in H by auto. destruct (i - length l) as [|z] eqn:Z; [|destruct z; discriminate].
    simpl in H. injection H as <-. split; auto. lia.
Qed.

Lemma nth_error_last : forall (l : list sev) e, nth_error (l ++ [e]) (length l) = Some e.
Proof. intros. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. Qed.

Lemma hasg_snoc : forall l e i c1, i <= length l -> hasg (l ++ [e]) i c1 ->
  hasg l i c1 \/ (sg e = true /\ sx e = c1).
Proof.
  intros l e i c1 L (i' & f & L1 & L2 & Q & S1 & S2). rewrite length_app in L2. simpl in L2.
  apply nth_error_snoc in Q. destruct Q as [[A B]|[A B]].
  - left. exists i', f. auto.
  - right. subst. auto.
Qed.

Lemma hasg_mono : forall l e i c1, hasg l i c1 -> hasg (l ++ [e]) i c1.
Proof.
  intros l e i c1 (i' & f & L1 & L2 & Q & S1 & S2). exists i', f. rewrite length_app. simpl.
  rewrite nth_error_app1 by auto. repeat split; auto; lia.
Qed.

Lemma hasg_last : forall l e i c1, i <= length l -> sg e = true -> sx e = c1 -> hasg (l ++ [e]) i c1.
Proof.
  intros l e i c1 L S X. exists (length l), e. rewrite length_app. simpl. rewrite nth_error_last. repeat split; auto; lia.
Qed.

Lemma gsb_mono : forall l e i c1 c2, gsb l i c1 c2 -> gsb (l ++ [e]) i c1 c2.
Proof.
  intros l e i c1 c2 (i' & j' & f1 & f2 & L1 & L2 & L3 & Q1 & Q2 & S1 & S2 & X1 & X2).
  exists i', j', f1, f2. rewrite length_app, !nth_error_app1 by lia. simpl. repeat split; auto; lia.
Qed.

Lemma gsb_last : forall l e i c1 c2, hasg l i c1 -> sg e = true -> sx e = c2 -> gsb (l ++ [e]) i c1 c2.
Proof.
  intros l e i c1 c2 (i' & f & L1 & L2 & Q & S1 & S2) G X.
  exists i', (length l), f, e. rewrite length_app, nth_error_app1, nth_error_last by auto. simpl.
  repeat split; auto; lia.
Qed.

Lemma gsb_self : forall l e c c2, c2 <> c -> sx e = c -> ~ gsb (l ++ [e]) (length l) c c2.
Proof.
  intros l e c c2 N X (i' & j' & f1 & f2 & L1 & L2 & L3 & Q1 & Q2 & S1 & S2 & X1 & X2).
  rewrite length_app in L3. simpl in L3. assert (j' = length l) by lia. subst j'.
  rewrite nth_error_last in Q2. injection Q2 as <-. congruence.
Qed.

Lemma hasg_silent : forall l e i c1, sg e = false -> hasg (l ++ [e]) i c1 -> i <= length l -> hasg l i c1.
Proof. intros l e i c1 S H L. destruct (hasg_snoc l e i c1 L H) as [A|[A _]]; [auto|congruence]. Qed.

Lemma gsb_silent : forall l e i c1 c2, sg e = false -> gsb (l ++ [e]) i c1 c2 -> gsb l i c1 c2.
Proof.
  intros l e i c1 c2 S (i' & j' & f1 & f2 & L1 & L2 & L3 & Q1 & Q2 & S1 & S2 & X1 & X2).
  rewrite length_app in L3. simpl in L3.
  destruct (Nat.eq_dec j' (length l)) as [->|Nj].
  - rewrite nth_error_last in Q2. injection Q2 as <-. congruence.
  - exists i', j', f1, f2. rewrite nth_error_app1 in Q1, Q2 by lia. repeat split; auto; lia.
Qed.

Lemma RI_silent : forall Q l a e, RIq Q l a -> sacc1 e = None -> sg e = false -> RIq Q (l ++ [e]) a.
Proof.
  intros Qf l a e R A G i e1 x w gg c2 Q A1 L1 L2 N12 Iq.
  apply nth_error_snoc in Q. destruct Q as [[Li Q]|[Li ->]]; [|congruence].
  destruct (R i e1 x w gg c2 Q A1 L1 L2 N12 Iq) as [P1 P2]. split.
  - intros H. apply P1. intros H'. apply H. apply hasg_mono. auto.
  - intros H. apply P2. intros H'. apply H. apply gsb_mono. auto.
Qed.

Lemma aget_new : forall a c acc g c1, c1 < N ->
  nth c1 (map (newA a c acc g) (seq 0 N)) [] = newA a c acc g c1.
Proof. intros. apply nth_map_seq. auto. Qed.

Lemma bgt_new : forall a c acc g c1 c2, c1 < N -> c2 < N ->
  nth c2 (nth c1 (map (fun c1 => map (newB a c acc g c1) (seq 0 N)) (seq 0 N)) []) [] = newB a c acc g c1 c2.
Proof. intros. rewrite nth_map_seq by auto. apply nth_map_seq. auto. Qed.

Definition upd_race (a : ast) (c : nat) acc (g : bool) (pc' : list nat) rg' mem' : ast :=
  mkA pc' rg' mem' (map (newA a c acc g) (seq 0 N)) (map (fun c1 => map (newB a c acc g c1) (seq 0 N)) (seq 0 N)).

Lemma aget_upd : forall a c acc g pc' rg' mem' c1, c1 < N ->
  aget (upd_race a c acc g pc' rg' mem') c1 = newA a c acc g c1.
Proof. intros. unfold aget, upd_race. simpl. apply aget_new. auto. Qed.

Lemma bgt_upd : forall a c acc g pc' rg' mem' c1 c2, c1 < N -> c2 < N ->
  bgt (upd_race a c acc g pc' rg' mem') c1 c2 = newB a c acc g c1 c2.
Proof. intros. unfold bgt, upd_race. simpl. apply bgt_new; auto. Qed.

Lemma bget_acc_mono : forall acc b j, bget b j = true -> bget (accbits acc b) j = true.
Proof. intros [[[y w] g]|] b j H; simpl; auto. apply bget_bset_mono. auto. Qed.

Ltac bfin O := cbv beta iota; rewrite ?bget_bor; first [rewrite (bget_acc_mono _ _ _ O) | rewrite O]; rewrite ?orb_true_r, ?orb_true_l; reflexivity.

Lemma RI_step : forall Qf l a e pc' rg' mem', RIq Qf l a -> sx e < N ->
  RIq Qf (l ++ [e]) (upd_race a (sx e) (accx (sacc1 e) (sx e) (sk e)) (sg e) pc' rg' mem').
Proof.
  intros Qf l a e pc' rg' mem' R Lc i e1 x w gg c2 Q A1 L1 L2 N12 Iq.
  rewrite aget_upd, bgt_upd by auto.
  apply nth_error_snoc in Q. destruct Q as [[Li Q]|[Li ->]].
  - (* an earlier access *)
    destruct (R i e1 x w gg c2 Q A1 L1 L2 N12 Iq) as [OA OAB].
    split.
    + intros H. assert (H1 : ~ hasg l i (sx e1)) by (intros H'; apply H; apply hasg_mono; auto).
      specialize (OA H1). unfold newA.
      destruct (Nat.eqb_spec (sx e1) (sx e)) as [E|E]; [|exact OA].
      destruct (sg e) eqn:G.
      * exfalso. apply H. apply hasg_last; auto. lia.
      * rewrite E in OA. rewrite ?E. bfin OA.
    + intros H. assert (H1 : ~ gsb l i (sx e1) c2) by (intros H'; apply H; apply gsb_mono; auto).
      specialize (OAB H1). unfold newA, newB.
      destruct (hasgb l i (sx e1)) eqn:HB.
      * apply hasgb_spec in HB.
        destruct (sg e) eqn:G.
        -- assert (Nc : sx e <> c2) by (intros E; apply H; apply gsb_last; auto).
           destruct (Nat.eqb_spec (sx e1) (sx e)) as [E|E].
           ++ rewrite E in OAB. apply orb_prop in OAB. destruct OAB as [O|O]; rewrite ?E; bfin O.
           ++ destruct (Nat.eqb_spec c2 (sx e)) as [E2|E2]; [congruence|]. exact OAB.
        -- destruct (Nat.eqb_spec (sx e1) (sx e)) as [E|E]; [|exact OAB].
           rewrite E in OAB. apply orb_prop in OAB. destruct OAB as [O|O]; rewrite ?E; bfin O.
      * assert (H2 : ~ hasg l i (sx e1)) by (intros H'; apply hasgb_spec in H'; congruence).
        specialize (OA H2).
        destruct (sg e) eqn:G.
        -- destruct (Nat.eqb_spec (sx e1) (sx e)) as [E|E]; [|bfin OA].
           rewrite E in OA. rewrite ?E. bfin OA.
        -- destruct (Nat.eqb_spec (sx e1) (sx e)) as [E|E]; [|bfin OA].
           rewrite E in OA. rewrite ?E. bfin OA.
  - (* the new access itself *)
    unfold newA, newB. rewrite A1, Nat.eqb_refl. simpl accx.
    assert (B : bget (accbits (Some (x, w, ex (sx e) (sk e))) (aget a (sx e))) (bidx x w (ex (sx e) (sk e))) = true)
      by (simpl; rewrite bget_bset, Nat.eqb_refl; reflexivity).
    split.
    + intros H. destruct (sg e) eqn:G.
      * exfalso. apply H. apply hasg_last; auto. lia.
      * exact B.
    + intros _. destruct (sg e); bfin B.
Qed.

Lemma gsync_mono : forall l e i j c1 c2, gsync l i j c1 c2 -> gsync (l ++ [e]) i j c1 c2.
Proof.
  intros l e i j c1 c2 (i' & j' & f1 & f2 & L1 & L2 & L3 & Q1 & Q2 & S1 & S2 & X1 & X2).
  exists i', j', f1, f2.
  rewrite (nth_error_app1 l [e] (proj1 (nth_error_Some l i') ltac:(congruence))).
  rewrite (nth_error_app1 l [e] (proj1 (nth_error_Some l j') ltac:(congruence))).
  repeat split; auto.
Qed.

(* the check made at each access finds every race *)
Lemma race_step : forall l a e, RI l a -> ~ racy_g p l -> sx e < N ->
  (forall q e1 y w g, nth_error l q = Some e1 -> sacc1 e1 = Some (y, w, g) -> sx e1 < N) ->
  (forall q e1 xs w, nth_error (l ++ [e]) q = Some e1 -> sacc e1 = Some (xs, w) -> exists x, xs = [x]) ->
  (forall y w g, sacc1 e = Some (y, w, g) -> inq a (sx e) y = true) ->
  race_hit a (sx e) (accx (sacc1 e) (sx e) (sk e)) (sg e) = false -> ~ racy_g p (l ++ [e]).
Proof.
  intros l a e R NR Le CX One IQ H (i & j & e1 & e2 & x & xs1 & xs2 & w1 & w2 & L & Q1 & Q2 & Nx & A1' & A2' & I1 & I2 & Wr & Gd & Ns).
  destruct (One i e1 xs1 w1 Q1 A1') as (x1 & ->). destruct (One j e2 xs2 w2 Q2 A2') as (x2 & ->).
  destruct I1 as [E1|[]]. destruct I2 as [E2|[]]. subst x1 x2.
  assert (A1 : sacc1 e1 = Some (x, w1, false)) by (unfold sacc1; rewrite A1'; reflexivity).
  assert (A2 : sacc1 e2 = Some (x, w2, false)) by (unfold sacc1; rewrite A2'; reflexivity).
  apply nth_error_snoc in Q2. destruct Q2 as [[Lj Q2]|[Lj ->]].
  - apply NR. assert (Q1' : nth_error l i = Some e1) by (rewrite nth_error_app1 in Q1 by lia; auto).
    exists i, j, e1, e2, x, [x], [x], w1, w2. repeat split; auto; try (left; reflexivity).
    intros G. apply Ns. apply gsync_mono. auto.
  - assert (Q1' : nth_error l i = Some e1) by (rewrite nth_error_app1 in Q1 by lia; auto).
    pose proof (CX i e1 x w1 false Q1' A1) as L1.
    destruct (R i e1 x w1 false (sx e) Q1' A1 L1 Le (fun E => Nx (eq_sym E)) (IQ _ _ _ A2)) as [OA OAB].
    rewrite A2 in H. unfold accx, race_hit in H.
    assert (Gd' : (ex (sx e1) (sk e1) && ex (sx e) (sk e)) = false).
    { destruct (ex (sx e1) (sk e1)) eqn:X1; destruct (ex (sx e) (sk e)) eqn:X2; auto.
      exfalso. apply Gd. split; apply Hex; auto. }
    rewrite <- not_true_iff_false in H. apply H. apply existsb_exists. exists (sx e1).
    split; [apply in_seq; lia|]. rewrite (proj2 (Nat.eqb_neq _ _) Nx). simpl.
    destruct (sg e) eqn:G.
    + assert (NH : ~ hasg l i (sx e1)).
      { intros (i' & f & M1 & M2 & M3 & M4 & M5). apply Ns. exists i', (length l), f, e.
        rewrite nth_error_app1 by auto. rewrite nth_error_last. repeat split; auto; lia. }
      rewrite (hit_of _ x w2 _ w1 _ (OA NH) Wr Gd'). reflexivity.
    + assert (NG : ~ gsb l i (sx e1) (sx e)).
      { intros (i' & j' & f1 & f2 & M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9). apply Ns.
        exists i', j', f1, f2. rewrite !nth_error_app1 by lia. repeat split; auto; lia. }
      specialize (OAB NG). apply orb_prop in OAB. destruct OAB as [O|O].
      * rewrite (hit_of _ x w2 _ w1 _ O Wr Gd'). reflexivity.
      * rewrite (hit_of _ x w2 _ w1 _ O Wr Gd'). rewrite orb_true_r. reflexivity.
Qed.

(* ---------- the machine part of a step ---------- *)
Lemma pc_step : forall g g2 a c, (forall c, c < N -> nth c (apc a) 0 = Nat.min (sp g c) (len c)) ->
  sp g2 = upd (sp g) c (S (sp g c)) -> sp g c < len c ->
  forall c', c' < N -> nth c' (lset 0 (apc a) c (S (sp g c))) 0 = Nat.min (sp g2 c') (len c').
Proof.
  intros g g2 a c P E L c' L'. rewrite nth_lset, E. unfold upd.
  destruct (Nat.eqb_spec c' c) as [->|Nc]; [lia|]. apply P. auto.
Qed.

Lemma rg_set : forall g a c v, (forall c j, c < N -> j < len c -> nth j (nth c (arg a) []) 0 = sr g c j) ->
  forall c' j, c' < N -> j < len c' ->
  nth j (nth c' (lset [] (arg a) c (lset 0 (nth c (arg a) []) (sp g c) v)) []) 0 =
  upd (sr g) c (upd (sr g c) (sp g c) v) c' j.
Proof.
  intros g a c v P c' j L1 L2. rewrite nth_lset. unfold upd.
  destruct (Nat.eqb_spec c' c) as [->|Nc]; [|apply P; auto].
  rewrite nth_lset. destruct (Nat.eqb j (sp g c)); auto.
Qed.

Lemma mem_set : forall g a x v, (forall x, x < M -> nth x (amem a) 0 = sm g x) ->
  forall y, y < M -> nth y (lset 0 (amem a) x v) 0 = upd (sm g) x v y.
Proof. intros g a x v P y L. rewrite nth_lset. unfold upd. destruct (Nat.eqb y x); auto. Qed.

Lemma bfilt_nth : forall f b i j, nth j (bfilt f i b) false = nth j b false && f (Nat.div (i + j) 4).
Proof.
  intros f. induction b as [|h t IH]; intros i [|j]; simpl; auto.
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite IH. rewrite Nat.add_succ_r. reflexivity.
Qed.

Lemma bidx_div : forall x w g, Nat.div (bidx x w g) 4 = x.
Proof.
  intros x w g. unfold bidx. rewrite <- Nat.add_assoc.
  rewrite Nat.div_add_l by lia. destruct w, g; simpl; lia.
Qed.

Lemma bget_bfilt : forall f b x w g, bget (bfilt f 0 b) (bidx x w g) = bget b (bidx x w g) && f x.
Proof. intros. unfold bget. rewrite bfilt_nth, Nat.add_0_l, bidx_div. reflexivity. Qed.

Lemma RI_prune : forall l a, RIq (inq a) l a -> RIq (inq a) l (prune a).
Proof.
  intros l a R i e1 x w gg c2 Q A1 L1 L2 N12 Iq.
  destruct (R i e1 x w gg c2 Q A1 L1 L2 N12 Iq) as [OA OAB].
  assert (EX : existsb (fun c3 => negb (Nat.eqb c3 (sx e1)) && inq a c3 x) (seq 0 N) = true).
  { apply existsb_exists. exists c2. split; [apply in_seq; lia|]. rewrite (proj2 (Nat.eqb_neq _ _) N12), Iq. reflexivity. }
  unfold aget, bgt, prune. simpl. rewrite !nth_map_seq by auto. rewrite !bget_trim, !bget_bfilt.
  split.
  - intros H. unfold aget in OA. rewrite (OA H), EX. reflexivity.
  - intros H. unfold aget, bgt in OAB. specialize (OAB H). rewrite EX, Iq, !andb_true_r. exact OAB.
Qed.

Lemma RIq_mono : forall (Q Q' : nat -> cell -> bool) l a, (forall c x, Q' c x = true -> Q c x = true) ->
  RIq Q l a -> RIq Q' l a.
Proof. intros Q Q' l a H R i e1 x w gg c2 Qe A1 L1 L2 N12 Iq. apply (R i e1 x w gg c2 Qe A1 L1 L2 N12 (H _ _ Iq)). Qed.

Lemma inq_step : forall a c k rg' mem' A' B', nth c (apc a) 0 = k ->
  forall c2 x, inq (mkA (lset 0 (apc a) c (S k)) rg' mem' A' B') c2 x = true -> inq a c2 x = true.
Proof.
  intros a c k rg' mem' A' B' Hk c2 x H. unfold inq in *. simpl in H. rewrite nth_lset in H.
  destruct (Nat.eqb_spec c2 c) as [->|N']; [|exact H].
  apply existsb_exists in H. destruct H as (y & I & E). apply Nat.eqb_eq in E. subst y.
  apply existsb_exists. exists x. split; [rewrite Hk; apply Hmono; auto|apply Nat.eqb_refl].
Qed.

Lemma abs_prune_of : forall l g X,
  (forall c, c < N -> nth c (apc X) 0 = Nat.min (sp g c) (len c)) ->
  (forall c j, c < N -> j < len c -> nth j (nth c (arg X) []) 0 = sr g c j) ->
  (forall x, x < M -> nth x (amem X) 0 = sm g x) ->
  RIq (inq X) l X -> abs l g (prune X).
Proof. intros l g X A B C D. constructor; auto. exact (RI_prune l X D). Qed.

Lemma acc_cell : forall g e g2 xs w, sstep p g e g2 -> sacc e = Some (xs, w) ->
  icells (ins p (sx e) (sp g (sx e)) (sr g (sx e))) = xs.
Proof.
  intros g e g2 xs w St A.
  destruct St; simpl in *; try discriminate; injection A; intros; subst; rewrite H; reflexivity.
Qed.

Lemma acc_one : forall l g, srun p l g -> forall q e xs w, nth_error l q = Some e -> sacc e = Some (xs, w) ->
  exists x, xs = [x].
Proof.
  intros l g R q e xs w Q A. destruct (srun_ev p W l g R q e Q) as (i & Hi & _ & Sh). rewrite A in Sh.
  assert (Ia : isacc i = true /\ icells i = xs).
  { destruct i as [md y c|md y c v|md y c e0 n|fk|]; simpl in Sh;
      try (destruct (c (sr g (sx e))); injection Sh; intros; subst; auto; discriminate);
      try (destruct fk; discriminate); discriminate. }
  destruct Ia as [Ia Ic]. rewrite <- Hi in Ia. destruct (Hone _ _ _ Ia) as (x & Ex). exists x. rewrite <- Ic, <- Hi. exact Ex.
Qed.

Lemma mem_set1 : forall g a x v, (forall x, x < M -> nth x (amem a) 0 = sm g x) ->
  forall y, y < M -> nth y (lset 0 (amem a) x v) 0 = mupd (sm g) [x] [v] y.
Proof. intros g a x v P y L. rewrite nth_lset. unfold mupd. simpl. destruct (Nat.eqb y x); simpl; auto. Qed.

Lemma step_active : forall l g e g2 a b, abs l g a -> sstep p g e g2 -> active a (sx e) = true ->
  astep (sx e) (sbw e) a = (b, false) -> race_hit a (sx e) (accx (sacc1 e) (sx e) (sk e)) (sg e) = false /\ abs (l ++ [e]) g2 b.
Proof.
  intros l g e g2 a b Ab St Ac Ast.
  apply andb_prop in Ac. destruct Ac as [Lc Lk]. apply Nat.ltb_lt in Lc, Lk.
  assert (Hk : nth (sx e) (apc a) 0 = sp g (sx e)) by (rewrite (a_pc _ _ _ Ab _ Lc) in Lk |- *; lia).
  assert (Lt : sp g (sx e) < len (sx e)) by (rewrite <- Hk; auto).
  assert (AG : forall j, j < sp g (sx e) -> rl (nth (sx e) (arg a) []) j = sr g (sx e) j).
  { intros j Lj. unfold rl. apply (a_rg _ _ _ Ab); auto. lia. }
  assert (HI : forall i, ins p (sx e) (sp g (sx e)) (sr g (sx e)) = i -> ins p (sx e) (sp g (sx e)) (rl (nth (sx e) (arg a) [])) = i).
  { intros i Hi. rewrite <- Hi. apply wf_ins; auto. }
  assert (HE : forall i, ins p (sx e) (sp g (sx e)) (sr g (sx e)) = i ->
            ieval i (rl (nth (sx e) (arg a) [])) = ieval i (sr g (sx e))).
  { intros i Hi. apply (wf_ieval p (sx e) (sp g (sx e)) i); auto. }
  revert Ast. cbv beta zeta delta [astep]. rewrite Hk.
  pose proof (a_ri _ _ _ Ab) as RIa.
  assert (ONE : forall i, ins p (sx e) (sp g (sx e)) (sr g (sx e)) = i -> isacc i = true -> exists x, icells i = [x]).
  { intros i Hi Ia. rewrite <- Hi in Ia |- *. apply Hone. exact Ia. }
  destruct St as [s c i Hi Hf Hc | s c md xs cnd Hi Hc | s c md xs cnd v Hi Hc | s c md xs cnd e0 n0 bb Hi Hc | s c f Hi | s c Hi];
    simpl sx in *; simpl sp in *; simpl sg; simpl sm; simpl sr;
    rewrite (HI _ Hi); pose proof (HE _ Hi) as HEi; intros Ast;
    try (destruct (ONE _ Hi eq_refl) as (x & Dx); simpl in Dx);
    unfold sacc1; simpl sacc.
  - (* skipped access *)
    destruct i as [md x cnd|md x cnd v|md x cnd e0 n0|f|]; try (simpl in Hf; congruence);
      unfold icond, ieval in Hc, HEi; simpl in Hc, HEi;
      (assert (Hc' : cnd (rl (nth c (arg a) [])) = false) by (injection HEi; intros; congruence));
      simpl in Ast; rewrite Hc' in Ast;
      injection Ast as <-; (split; [reflexivity|]); apply abs_prune_of.
    all: first [ (eapply pc_step; [exact (a_pc _ _ _ Ab)|reflexivity|exact Lt])
               | exact (a_rg _ _ _ Ab)
               | exact (a_mem _ _ _ Ab)
               | (eapply RIq_mono; [|eapply RI_step; [exact RIa|exact Lc]]; eapply inq_step; exact Hk) ].
  - (* load *)
    simpl in Ast. rewrite Dx in Ast |- *. simpl in Ast |- *. injection HEi as HEi. rewrite HEi, Hc in Ast.
    injection Ast as <- Bd. apply orb_false_elim in Bd. destruct Bd as [Bd Cb].
    simpl in Cb. apply negb_false_iff, Nat.ltb_lt in Cb.
    split; [exact Bd|]. apply abs_prune_of.
    + (eapply pc_step; [exact (a_pc _ _ _ Ab)|reflexivity|exact Lt]).
    + simpl. rewrite (a_mem _ _ _ Ab x Cb). apply rg_set. exact (a_rg _ _ _ Ab).
    + exact (a_mem _ _ _ Ab).
    + (eapply RIq_mono; [|eapply RI_step; [exact RIa|exact Lc]]; eapply inq_step; exact Hk).
  - (* store *)
    simpl in Ast. rewrite Dx in Ast |- *. simpl in Ast |- *. injection HEi as HEc HEv. rewrite HEc, Hc, HEv in Ast.
    injection Ast as <- Bd. apply orb_false_elim in Bd. destruct Bd as [Bd Cb].
    simpl in Cb. apply negb_false_iff, Nat.ltb_lt in Cb.
    split; [exact Bd|]. apply abs_prune_of.
    + (eapply pc_step; [exact (a_pc _ _ _ Ab)|reflexivity|exact Lt]).
    + exact (a_rg _ _ _ Ab).
    + apply mem_set1. exact (a_mem _ _ _ Ab).
    + (eapply RIq_mono; [|eapply RI_step; [exact RIa|exact Lc]]; eapply inq_step; exact Hk).
  - (* transaction *)
    subst ok. simpl in Ast. rewrite Dx in Ast |- *. simpl in Ast |- *. injection HEi as HEc HEe HEn. rewrite HEc, Hc, HEe, HEn in Ast.
    destruct (Nat.ltb_spec x M) as [Cb|Cb].
    2:{ exfalso. destruct (Nat.eqb (nth x (amem a) 0) (e0 (sr s c))), bb; injection Ast as _ Bd;
        apply orb_false_elim in Bd; destruct Bd as [_ Bd]; simpl in Bd; apply negb_false_iff, Nat.ltb_lt in Bd; lia. }
    rewrite (a_mem _ _ _ Ab x Cb) in Ast.
    destruct (Nat.eqb (sm s x) (e0 (sr s c))) eqn:OK, bb;
      injection Ast as <- Bd; apply orb_false_elim in Bd; destruct Bd as [Bd _];
      (split; [exact Bd|]); apply abs_prune_of.
    all: first [ (eapply pc_step; [exact (a_pc _ _ _ Ab)|reflexivity|exact Lt])
               | (simpl; apply rg_set; exact (a_rg _ _ _ Ab))
               | (simpl; apply mem_set1; exact (a_mem _ _ _ Ab))
               | exact (a_mem _ _ _ Ab)
               | (eapply RIq_mono; [|eapply RI_step; [exact RIa|exact Lc]]; eapply inq_step; exact Hk) ].
  - (* fence *)
    simpl in Ast. injection Ast as <-. split; [reflexivity|]. apply abs_prune_of.
    + (eapply pc_step; [exact (a_pc _ _ _ Ab)|reflexivity|exact Lt]).
    + exact (a_rg _ _ _ Ab).
    + exact (a_mem _ _ _ Ab).
    + (eapply RIq_mono; [|eapply RI_step; [exact RIa|exact Lc]]; eapply inq_step; exact Hk).
  - (* nothing *)
    simpl in Ast. injection Ast as <-. split; [reflexivity|]. apply abs_prune_of.
    + (eapply pc_step; [exact (a_pc _ _ _ Ab)|reflexivity|exact Lt]).
    + exact (a_rg _ _ _ Ab).
    + exact (a_mem _ _ _ Ab).
    + (eapply RIq_mono; [|eapply RI_step; [exact RIa|exact Lc]]; eapply inq_step; exact Hk).
Qed.

(* a context that has run out of instructions, or does not exist, does nothing *)
Lemma step_inactive : forall l g e g2 a, abs l g a -> sstep p g e g2 -> active a (sx e) = false ->
  abs (l ++ [e]) g2 a /\ sacc e = None /\ sacc1 e = None.
Proof.
  intros l g e g2 a Ab St Ac.
  assert (Nop : forall r, ins p (sx e) (sp g (sx e)) r = INop).
  { intros r. unfold active in Ac. destruct (Nat.ltb_spec (sx e) N) as [L|L]; [|apply Hout; auto].
    simpl in Ac. apply Nat.ltb_ge in Ac. rewrite (a_pc _ _ _ Ab _ L) in Ac. apply Hfin. lia. }
  destruct St as [s c i Hi Hf Hc | s c md x cnd Hi Hc | s c md x cnd v Hi Hc | s c md x cnd e0 n0 bb Hi Hc | s c f Hi | s c Hi];
    simpl in Nop, Ac |- *; rewrite Nop in Hi; try discriminate.
  - subst i. simpl in Hf. congruence.
  - split; [|split; reflexivity]. constructor.
    + intros c' L. simpl. unfold upd. destruct (Nat.eqb_spec c' c) as [->|N']; [|apply (a_pc _ _ _ Ab); auto].
      rewrite (a_pc _ _ _ Ab _ L). unfold active in Ac. rewrite (proj2 (Nat.ltb_lt _ _) L) in Ac. simpl in Ac.
      apply Nat.ltb_ge in Ac. rewrite (a_pc _ _ _ Ab _ L) in Ac. lia.
    + exact (a_rg _ _ _ Ab).
    + exact (a_mem _ _ _ Ab).
    + apply RI_silent; auto. exact (a_ri _ _ _ Ab).
Qed.

Lemma acc_ctx : forall l g, srun p l g -> forall q e1 y w gg, nth_error l q = Some e1 -> sacc1 e1 = Some (y, w, gg) -> sx e1 < N.
Proof.
  intros l g R q e1 y w gg Q A. destruct (Nat.lt_ge_cases (sx e1) N) as [L|L]; auto. exfalso.
  destruct (srun_ev p W l g R q e1 Q) as (i & Hi & _ & Sh). rewrite Hout in Hi by auto. subst i.
  simpl in Sh. unfold sacc1 in A. destruct (sacc e1); [|discriminate]. injection Sh as Sh. discriminate.
Qed.

Lemma abs_init : abs [] ssinit ainit.
Proof.
  constructor.
  - intros c L. simpl. rewrite nth_repeat. reflexivity.
  - intros c j L1 L2. simpl. rewrite nth_repeat. apply nth_nil_d.
  - intros x L. simpl. apply nth_nil_d.
  - intros i e1 x w gg c2 Q. destruct i; discriminate.
Qed.

Theorem enum_sound : forall S, closed S = true -> forall l g, srun p l g ->
  ~ racy_g p l /\ exists a, In a S /\ abs l g a.
Proof.
  intros S C. unfold closed in C. apply andb_prop in C. destruct C as [C0 C1]. rewrite forallb_forall in C1.
  intros l g R. induction R as [|l g e g2 R IH St].
  - split.
    + intros (i & j & e1 & e2 & x & xs1 & xs2 & w1 & w2 & L & Q1 & _). destruct i; discriminate.
    + exists ainit. split; [apply amemb_in; auto|apply abs_init].
  - destruct IH as (NR & a & Ia & Ab). pose proof (C1 a Ia) as Ca. rewrite forallb_forall in Ca.
    destruct (active a (sx e)) eqn:Ac.
    + assert (Lc : sx e < N) by (unfold active in Ac; apply andb_prop in Ac; apply Nat.ltb_lt; tauto).
      specialize (Ca (sx e) ltac:(apply in_seq; lia)). rewrite Ac in Ca.
      rewrite forallb_forall in Ca. specialize (Ca (sbw e) ltac:(destruct (sbw e); simpl; auto)).
      destruct (astep (sx e) (sbw e) a) as [b bad] eqn:Ast. apply andb_prop in Ca. destruct Ca as [Bd Mb].
      apply negb_true_iff in Bd. subst bad.
      destruct (step_active l g e g2 a b Ab St Ac Ast) as [RH Ab2].
      split; [|exists b; split; [apply amemb_in; auto|exact Ab2]].
      assert (IQ : forall y w gg, sacc1 e = Some (y, w, gg) -> inq a (sx e) y = true).
      { intros y w gg A. unfold inq. apply existsb_exists. exists y. split; [|apply Nat.eqb_refl].
        unfold sacc1 in A. destruct (sacc e) as [[xs w0]|] eqn:A0; [|discriminate].
        destruct xs as [|y0 [|y1 xs]]; try discriminate. injection A as <- _ _.
        assert (Lt : sp g (sx e) < len (sx e)).
        { unfold active in Ac. apply andb_prop in Ac. destruct Ac as [_ Ac]. apply Nat.ltb_lt in Ac.
          rewrite (a_pc _ _ _ Ab _ Lc) in Ac. lia. }
        rewrite (a_pc _ _ _ Ab _ Lc). replace (Nat.min (sp g (sx e)) (len (sx e))) with (sp g (sx e)) by lia.
        apply Hfut with (r := sr g (sx e)). rewrite (acc_cell g e g2 _ _ St A0). left. reflexivity. }
      apply (race_step l a e (a_ri _ _ _ Ab) NR Lc (acc_ctx l g R) (acc_one (l ++ [e]) g2 (srS p l g e g2 R St)) IQ). exact RH.
    + destruct (step_inactive l g e g2 a Ab St Ac) as [Ab2 [Ae _]].
      split; [|exists a; split; auto].
      intros (i & j & e1 & e2 & x & xs1 & xs2 & w1 & w2 & L & Q1 & Q2 & Nx & A1 & A2 & I1 & I2 & Wr & Gd & Ns).
      apply nth_error_snoc in Q2. destruct Q2 as [[Lj Q2]|[Lj ->]]; [|congruence].
      apply NR. exists i, j, e1, e2, x, xs1, xs2, w1, w2.
      rewrite nth_error_app1 in Q1 by lia. repeat split; auto. intros G. apply Ns. apply gsync_mono. auto.
Qed.

Corollary enum_race_free : forall S, closed S = true -> race_free_g p.
Proof. intros S C l g R. apply (enum_sound S C l g R). Qed.

(* registers the interleavings can show: obs lists (context, register, value) *)
Definition obs_ok (obs : list (nat * nat * nat)) : bool :=
  forallb (fun o => let '(c, j, v) := o in Nat.ltb c N && Nat.ltb j (len c)) obs.

Definition out_ok (S : list ast) (obs : list (nat * nat * nat)) : bool :=
  forallb (fun a => if forallb (fun o => let '(c, j, v) := o in Nat.ltb j (nth c (apc a) 0)) obs
                    then negb (forallb (fun o => let '(c, j, v) := o in Nat.eqb (nth j (nth c (arg a) []) 0) v) obs)
                    else true) S.

(* no interleaving shows the outcome *)
Theorem enum_sc_outcome : forall S obs, closed S = true -> out_ok S obs = true -> obs_ok obs = true ->
  forall l g, srun p l g -> (forall c j v, In (c, j, v) obs -> j < sp g c) ->
  ~ (forall c j v, In (c, j, v) obs -> sr g c j = v).
Proof.
  intros S obs C O K l g R Hj Hv.
  destruct (enum_sound S C l g R) as (_ & a & Ia & Ab).
  unfold out_ok in O. rewrite forallb_forall in O. specialize (O a Ia).
  unfold obs_ok in K. rewrite forallb_forall in K.
  assert (T1 : forallb (fun o => let '(c, j, v) := o in Nat.ltb j (nth c (apc a) 0)) obs = true).
  { apply forallb_forall. intros [[c j] v] I. specialize (K _ I). simpl in K. apply andb_prop in K.
    destruct K as [K1 K2]. apply Nat.ltb_lt in K1, K2. apply Nat.ltb_lt.
    rewrite (a_pc _ _ _ Ab _ K1). specialize (Hj c j v I). lia. }
  rewrite T1 in O. apply negb_true_iff in O. rewrite <- not_true_iff_false in O. apply O.
  apply forallb_forall. intros [[c j] v] I. specialize (K _ I). simpl in K. apply andb_prop in K.
  destruct K as [K1 K2]. apply Nat.ltb_lt in K1, K2. apply Nat.eqb_eq.
  rewrite (a_rg _ _ _ Ab c j K1 K2). apply Hv. auto.
Qed.

(* ---------- a trie for fast membership ---------- *)
Local Set Warnings "-register-all".
Inductive trie := TN (vs : list ast) (ks : list (nat * trie)).

Fixpoint kfind (x : nat) (ks : list (nat * trie)) : option trie :=
  match ks with [] => None | (y, t) :: r => if Nat.eqb x y then Some t else kfind x r end.

Fixpoint kins (x : nat) (f : trie -> trie) (ks : list (nat * trie)) : list (nat * trie) :=
  match ks with
  | [] => [(x, f (TN [] []))]
  | (y, t) :: r => if Nat.eqb x y then (y, f t) :: r else (y, t) :: kins x f r
  end.

Fixpoint tlookup (k : list nat) (t : trie) : list ast :=
  match t with
  | TN vs ks => match k with [] => vs | x :: k' => match kfind x ks with Some t' => tlookup k' t' | None => [] end end
  end.

Fixpoint tinsert (k : list nat) (a : ast) (t : trie) {struct k} : trie :=
  match t with
  | TN vs ks => match k with [] => TN (a :: vs) ks | x :: k' => TN vs (kins x (tinsert k' a) ks) end
  end.

Lemma kfind_kins : forall x x' f ks, kfind x' (kins x f ks) =
  if Nat.eqb x' x then Some (f (match kfind x ks with Some t => t | None => TN [] [] end)) else kfind x' ks.
Proof.
  intros x x' f. induction ks as [|[y t] r IH]; simpl.
  - destruct (Nat.eqb x' x); reflexivity.
  - destruct (Nat.eqb_spec x y) as [->|N]; simpl.
    + destruct (Nat.eqb_spec x' y); reflexivity.
    + rewrite IH. destruct (Nat.eqb_spec x' x) as [->|N']; [|reflexivity].
      destruct (Nat.eqb_spec x y); [congruence|reflexivity].
Qed.

Lemma tlookup_empty : forall k, tlookup k (TN [] []) = [].
Proof. intros [|x k]; reflexivity. Qed.

Lemma tlookup_insert : forall k a t k' b, In b (tlookup k' (tinsert k a t)) -> b = a \/ In b (tlookup k' t).
Proof.
  induction k as [|x k IH]; intros a [vs ks] k' b H.
  - simpl in H. destruct k' as [|x' k']; simpl in H |- *.
    + destruct H; auto.
    + auto.
  - simpl in H. destruct k' as [|x' k']; simpl in H |- *; auto.
    rewrite kfind_kins in H. destruct (Nat.eqb_spec x' x) as [->|N].
    + destruct (IH a _ k' b H) as [E|E]; auto. right.
      destruct (kfind x ks); auto. rewrite tlookup_empty in E. destruct E.
    + auto.
Qed.

Fixpoint sparse (i : nat) (b : list bool) : list nat :=
  match b with [] => [0] | true :: b' => S i :: sparse (S i) b' | false :: b' => sparse (S i) b' end.
Definition enc (a : ast) : list nat :=
  apc a ++ amem a ++ concat (arg a) ++ concat (map (sparse 0) (aA a)) ++ concat (map (sparse 0) (concat (aB a))).

Definition tbuild (S : list ast) : trie := fold_left (fun t a => tinsert (enc a) a t) S (TN [] []).

Lemma tbuild_in : forall S k b, In b (tlookup k (tbuild S)) -> In b S.
Proof.
  intros S. unfold tbuild.
  assert (G : forall S0 t k b, In b (tlookup k (fold_left (fun t a => tinsert (enc a) a t) S0 t)) ->
            In b S0 \/ In b (tlookup k t)).
  { induction S0 as [|a S0 IH]; intros t k b H; simpl in H; auto.
    destruct (IH _ _ _ H) as [E|E]; [left; right; auto|].
    destruct (tlookup_insert _ _ _ _ _ E) as [E'|E']; [left; left; auto|right; auto]. }
  intros k b H. destruct (G S _ k b H) as [E|E]; auto. rewrite tlookup_empty in E. destruct E.
Qed.

Definition tmem (t : trie) (a : ast) : bool := existsb (ast_eqb a) (tlookup (enc a) t).

Lemma tmem_in : forall S a, tmem (tbuild S) a = true -> In a S.
Proof.
  intros S a H. apply existsb_exists in H. destruct H as (b & I & E). apply ast_eqb_eq in E. subst.
  eapply tbuild_in; eauto.
Qed.

Lemma leqb_refl : forall A (f : A -> A -> bool), (forall x, f x x = true) -> forall l, leqb f l l = true.
Proof. intros A f F. induction l; simpl; auto. rewrite F, IHl. reflexivity. Qed.

Lemma ast_eqb_refl : forall a, ast_eqb a a = true.
Proof.
  intros [a1 a2 a3 a4 a5]. unfold ast_eqb. simpl.
  assert (F1 : forall x, Nat.eqb x x = true) by apply Nat.eqb_refl.
  assert (F2 : forall x, Bool.eqb x x = true) by (intros []; reflexivity).
  rewrite !(leqb_refl _ _ F1), !(leqb_refl _ _ (leqb_refl _ _ F1)), !(leqb_refl _ _ (leqb_refl _ _ F2)),
    !(leqb_refl _ _ (leqb_refl _ _ (leqb_refl _ _ F2))). reflexivity.
Qed.

Lemma amemb_of : forall S a, In a S -> amemb S a = true.
Proof. intros S a I. apply existsb_exists. exists a. split; auto. apply ast_eqb_refl. Qed.

Definition closed2 (S : list ast) : bool :=
  let t := tbuild S in
  tmem t ainit &&
  forallb (fun a => forallb (fun c => if active a c then
                                        forallb (fun sb => match astep c sb a with (b, bad) => negb bad && tmem t b end) [true; false]
                                      else true) (seq 0 N)) S.

Lemma closed2_closed : forall S, closed2 S = true -> closed S = true.
Proof.
  intros S C. unfold closed2 in C. apply andb_prop in C. destruct C as [C0 C1]. unfold closed.
  rewrite (amemb_of _ _ (tmem_in _ _ C0)). simpl. rewrite forallb_forall in C1 |- *.
  intros a I. specialize (C1 a I). rewrite forallb_forall in C1 |- *. intros c Ic. specialize (C1 c Ic).
  destruct (active a c); auto. simpl in C1.
  destruct (astep c true a) as [b1 bad1], (astep c false a) as [b2 bad2].
  apply andb_prop in C1 as [C1 C2]. apply andb_prop in C2 as [C2 _].
  apply andb_prop in C1 as [B1 B2]. apply andb_prop in C2 as [B3 B4].
  rewrite B1, B3. simpl. rewrite (amemb_of _ _ (tmem_in _ _ B2)), (amemb_of _ _ (tmem_in _ _ B4)). reflexivity.
Qed.

Fixpoint explore2 (fuel : nat) (todo : list ast) (t : trie) (seen : list ast) : list ast :=
  match fuel with
  | 0 => seen
  | S f => match todo with
           | [] => seen
           | a :: r => if tmem t a then explore2 f r t seen
                       else explore2 f (succs a ++ r) (tinsert (enc a) a t) (a :: seen)
           end
  end.

Definition xstep (st : list ast * trie * list ast) : list ast * trie * list ast :=
  match st with
  | (a :: r, t, seen) => if tmem t a then (r, t, seen) else (succs a ++ r, tinsert (enc a) a t, a :: seen)
  | ([], t, seen) => ([], t, seen)
  end.

(* fuel in binary: the search runs at most fuel steps *)
Definition reach (fuel : positive) : list ast :=
  match Pos.iter xstep ([ainit], TN [] [], []) fuel with (_, _, seen) => seen end.

End En.
