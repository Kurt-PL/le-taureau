(* Model2: no value from nowhere. Every value a run produces is in any set
   of values that holds 0 and is closed under what the programme computes.

   The early access is the new case. R1 holds for every free values of the
   loads not yet done, so in particular for the free values 0; the
   registers R1 then considers take values only from what has happened,
   from 0, and from what the programme computes, and the early access's
   values are computed from them. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3.

(* the type of an access read backwards. A mill part (spec 0.1 clause 6: the part of a
   machine's state other than its storage) holds one number; dec reads it
   back into the symbols of the cells the access spanned, by the access
   type's interpretation (spec 0.1 §2.2.4). A load's type is the sequence of the
   cells it spans; a CAS's is a verdict (spec 0.1 clause 5: a ui1 discriminant, then the
   payload, the sequence of its cells); an instruction that reads nothing
   stands for no symbol *)
Definition dec (i : instr) (a : val) : list val :=
  match i with
  | ILd _ xs _ => projs (length (dd xs)) a
  | ICas _ xs _ _ _ => Nat.b2n (vok a) :: projs (length (dd xs)) (vv a)
  | ISt _ _ _ _ | IFn _ | INop => []
  end.
(* a mill part: its number decodes, by the type of its slot, to symbols in V *)
Definition kV (V : val -> Prop) (i : instr) (a : val) : Prop := Forall V (dec i a).
(* what an instruction puts in its mill part, from symbols in V read at its
   cells, decodes to symbols in V: for a load, the symbols it read; for a
   CAS, also its discriminant, 0 or 1 *)
Definition clr (V : val -> Prop) (i : instr) : Prop :=
  forall w l, length l = length (icells i) -> Forall V l -> kV V i (areg i w (enc l)).
(* what an instruction computes from mill parts typed in V is in V: the symbol it
   writes at each of its cells, and what it puts in its mill part. A cell
   holds one symbol (spec 0.1 §2.2.1): only symbols are written, never a packed
   value, so a store of a verdict writes its two symbols at two cells (vst
   below) *)
Definition cl (V : val -> Prop) (i : instr) (r : regs) : Prop := Forall V (wvals i r) /\ clr V i.
(* what each instruction computes from the mill parts before it, each read
   by its type, is in V *)
Definition tclosed (p : prog) (V : val -> Prop) : Prop :=
  forall c k r, (forall j, j < k -> kV V (ins p c j r) (r j)) -> cl V (ins p c k r) r.

Definition cas_free (p : prog) : Prop := forall c k r, is_cas (ins p c k r) = false.

Lemma projs_0 : forall n, Forall (fun v => v = 0) (projs n 0).
Proof.
  induction n as [|[|n] IH]; [constructor|constructor; auto|].
  change (projs (S (S n)) 0) with (fst (Cantor.of_nat 0) :: projs (S n) (snd (Cantor.of_nat 0))).
  replace (Cantor.of_nat 0) with (0, 0) by reflexivity. constructor; [reflexivity|exact IH].
Qed.
Lemma Forall_projs_0 : forall (V : val -> Prop) n, V 0 -> Forall V (projs n 0).
Proof. intros V n V0. eapply Forall_impl; [|apply projs_0]. intros a ->. exact V0. Qed.
Lemma Forall_projs_enc : forall (V : val -> Prop) l n, n = length l -> Forall V l -> Forall V (projs n (enc l)).
Proof. intros V [|v l] n -> F; [constructor|]. rewrite projs_enc by discriminate. exact F. Qed.
Lemma V_b2n : forall (V : val -> Prop) b, V 0 -> V 1 -> V (Nat.b2n b).
Proof. intros V [] V0 V1; assumption. Qed.

Lemma kV_0 : forall (V : val -> Prop) i, V 0 -> kV V i 0.
Proof.
  intros V i V0. unfold kV. destruct i; simpl; try constructor; auto; apply Forall_projs_0; exact V0.
Qed.
(* the mill part of an access whose read took the symbols l of its cells: in
   V when V holds 0 and, for a CAS, 1 *)
Lemma clr_ok : forall (V : val -> Prop) i, V 0 -> (is_cas i = true -> V 1) -> clr V i.
Proof.
  intros V i V0 V1 w l Ln F. unfold kV, areg. destruct i; simpl in *; try constructor.
  - apply Forall_projs_enc; auto.
  - rewrite vok_vd. apply V_b2n; auto.
  - rewrite vv_vd. apply Forall_projs_enc; auto.
Qed.
(* a CAS's closure holds the discriminant 1 *)
Lemma clr_V1 : forall (V : val -> Prop) i, V 0 -> is_cas i = true -> clr V i -> V 1.
Proof.
  intros V i V0 C H. specialize (H true (repeat 0 (length (icells i))) (repeat_length _ _)).
  assert (F : Forall V (repeat 0 (length (icells i)))) by (apply Forall_forall; intros v Hv; apply repeat_spec in Hv; subst; exact V0).
  specialize (H F). unfold kV, areg in H. destruct i; simpl in C; try discriminate.
  simpl in H. rewrite vok_vd in H. inversion H. assumption.
Qed.
(* a CAS's read alone: its closure is its place's *)
Lemma clr_eofR : forall (V : val -> Prop) i r m xs, eofR i r = Some (m, xs) -> clr V i -> clr V (crd m xs).
Proof.
  intros V i r m xs E H. destruct i as [| |m0 x c e n| |]; simpl in E; try discriminate.
  destruct (c r); [injection E as <- <-|discriminate]. exact H.
Qed.
(* a verdict of a payload whose symbols are in V *)
Lemma kV_vd : forall (V : val -> Prop) i b a, is_cas i = true -> V (Nat.b2n b) -> kV V i a -> kV V i (vd b (vv a)).
Proof.
  intros V i b a C Vb H. unfold kV in *. destruct i; simpl in *; try discriminate.
  inversion H; subst. rewrite vok_vd, vv_vd. constructor; assumption.
Qed.
(* S3c: a fixed result keeps the type *)
Lemma kV_cfx : forall (V : val -> Prop) cc j i r a, V 0 -> (is_cas i = true -> V 1) -> kV V i a -> kV V i (cfx cc j i r a).
Proof.
  intros V cc j i r a V0 V1 H. rewrite !cfx_unfold. destruct (fx cc j) as [b|]; [|exact H].
  destruct (is_cas i) eqn:C; [|exact H]. apply kV_vd; auto. destruct (_ && _); simpl; auto.
Qed.
(* two slots of one type *)
Lemma kV_dec : forall (V : val -> Prop) i i' a, dec i = dec i' -> kV V i a -> kV V i' a.
Proof. intros V i i' a E H. unfold kV in *. rewrite <- E. exact H. Qed.
Lemma dec_eof : forall i r d, eof i r = Some d -> dec (inst_of d) = dec i.
Proof.
  intros [m x c|m x c v|m x c e n|f|] r d H; simpl in H; try discriminate;
    [destruct (c r); [injection H as <-; reflexivity|discriminate]..|].
  destruct f; try discriminate; injection H as <-; reflexivity.
Qed.
Lemma dec_eofR : forall i r m xs, eofR i r = Some (m, xs) -> dec (crd m xs) = dec i.
Proof.
  intros i r m1 xs1 H; destruct i as [| |m0 x c e n| |]; simpl in H; try discriminate.
  destruct (c r); [injection H as <- <-; reflexivity|discriminate].
Qed.
(* the mill part of a one-cell load is the symbol it read; a one-cell CAS's
   payload is the symbol it read *)
Lemma kV_ld1 : forall (V : val -> Prop) m x c a, kV V (ILd m [x] c) a -> V a.
Proof. intros V m x c a H. unfold kV in H. simpl in H. inversion H. assumption. Qed.
Lemma kV_cas1 : forall (V : val -> Prop) m x c e n a, kV V (ICas m [x] c e n) a -> V (vv a).
Proof. intros V m x c e n a H. unfold kV in H. simpl in H. inversion H as [|? ? _ H2]. inversion H2. assumption. Qed.

Lemma fab_eof' : forall p c cc pc N r n T d j, fab p c cc pc N r n T (TF d) j = true -> eof (ins p c j r) r = Some d.
Proof.
  intros p c cc pc N r n T d j H. destruct n as [|n]; [discriminate|]. cbn [fab] in H.
  repeat (apply andb_true_iff in H as [H ?]).
  match goal with X : tatb _ _ _ = true |- _ => revert X end. unfold tatb.
  destruct (eof (ins p c j r) r) as [d'|]; simpl; [|discriminate]. intros X. f_equal. apply desc_eqb_eq. exact X.
Qed.

Lemma fab_cas : forall p c cc pc N r n T m xs j, fab p c cc pc N r n T (TH m xs) j = true -> is_cas (ins p c j r) = true.
Proof.
  intros p c cc pc N r n T m xs j H. destruct n as [|n]; cbn [fab] in H; [discriminate|].
  destruct (tatb (ins p c j r) r (TH m xs)) eqn:Tb.
  - unfold tatb in Tb. destruct (eofR (ins p c j r) r) as [[m' xs']|] eqn:E; [|discriminate]. apply (eofR_cas _ r _ E).
  - rewrite andb_false_r in H. discriminate.
Qed.

Lemma hpend_at_cas : forall p c cc pc N r j k, hpend_at p c cc pc N r j = Some k -> is_cas (ins p c j r) = true.
Proof.
  intros p c cc pc N r j k H. unfold hpend_at in H. apply find_some in H as [_ H].
  destruct (oc cc k), (oh cc k); try discriminate. destruct (casx (ai cc k)) as [[m xs]|]; [|discriminate].
  apply (fab_cas _ _ _ _ _ _ _ _ _ _ _ H).
Qed.

(* a programme with no CAS has no CAS's read alone *)
Lemma cf_noh : forall p, cas_free p -> forall s, run p s -> forall c k, oh (cs s c) k = None.
Proof.
  intros p CF s R. induction R as [|s t R IH H]; intros c' k'; [reflexivity|].
  destruct (step_cases p s t H) as [(c & i & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ->)|[(c & k & d & B & m' & a & K & u & w & _ & _ & _ & _ & _ & _ & _ & _ & ->)|[(c & d & _ & _ & _ & _ & _ & _ & ->)|[(c & k & xs & B & m' & a & K & u & w & bv & _ & _ & _ & _ & H4 & _ & _ & ->)|[(c & _ & _ & _ & _ & _ & _ & _ & ->)|(cX & jX & bX & BX & oX & HjX & HfX & HcX & ->)]]]]].
  - unfold sord. rewrite oh_s'. apply IH.
  - unfold searly, set_es, searly0. cbn [cs]. rewrite oh_s'. apply IH.
  - rewrite oh_match. apply IH.
  - exfalso. destruct (H4 (fun _ _ => 0)) as (j & F0 & _). cbv zeta in F0.
    pose proof (eofR_cas _ _ _ (first_atR_eofR _ _ _ _ _ _ _ _ _ F0)) as Ca. rewrite CF in Ca. discriminate.
  - rewrite oh_skip. apply IH.
  - rewrite oh_cx, oh_flp. apply IH.
Qed.

(* slot 0 happened only once the context passed beyond it: an access early
   is placed beyond the next instruction when it happens, so beyond 0 when
   the context is at 0, and the next instruction is passed when it happens *)
Lemma slot0_oc : forall p s, run p s -> forall c, oc (cs s c) 0 <> None -> 0 < pcs s c.
Proof.
  intros p s R. induction R as [|s t R IH H]; intros c' O.
  - simpl in O. congruence.
  - inversion H; subst; repeat match goal with x := _ |- _ => subst x end.
    all: try (rewrite oc_cx, oc_flp in O; match goal with |- 0 < pcs (scfix0 ?X _ _ _ _) _ =>
                change (pcs (scfix0 X _ _ _ _)) with (pcs X) end; rewrite pcs_flp; apply IH; exact O).
    all: cbn [cs pcs] in *;
      unfold upd in *; destruct (Nat.eqb c' c) eqn:E; try (apply Nat.eqb_eq in E; subst c'); cbn in *.
    all: try lia. all: try (apply IH; exact O). all: (destruct k as [|k0]; [lia|apply IH; exact O]).
Qed.

(* for an instruction of at most one cell, cl says only that the value
   written is in V *)
Lemma cl_one : forall (V : val -> Prop) i r, length (icells i) <= 1 -> V 0 -> V (wval i r) ->
  (is_cas i = true -> V 1) -> cl V i r.
Proof.
  intros V i r Ln V0 Vw V1. split; [|apply clr_ok; auto]. unfold wvals.
  destruct (icells i) as [|x [|y xs]]; simpl in *; try lia; constructor; auto.
Qed.

Lemma cl_one1 : forall (V : val -> Prop) i r, V 1 -> length (icells i) <= 1 -> V 0 -> V (wval i r) -> cl V i r.
Proof. intros V i r V1 Ln V0 Vw. apply cl_one; auto. Qed.

(* a store of the verdict in mill part k: one store over the discriminant
   cell yd and the payload cell yp (spec 0.1 clause 5: the discriminant is a ui1, Pass =
   1, Fail = 0; the payload is placed apart); at each cell it writes that
   cell's symbol *)
Definition vst (m : mode) (yd yp : cell) (c : regs -> bool) (k : nat) : instr :=
  ISt m [yd; yp] c (fun r => enc [Nat.b2n (vok (r k)); vv (r k)]).

Lemma vst_wvals : forall m yd yp c k r, yd <> yp -> wvals (vst m yd yp c k) r = [Nat.b2n (vok (r k)); vv (r k)].
Proof.
  intros m yd yp c k r N. unfold wvals, vst, wval, icells, dd.
  rewrite nodup_fixed_point by (constructor; [intros [E|[]]; congruence|constructor; [intros []|constructor]]).
  change (projs (length [Nat.b2n (vok (r k)); vv (r k)]) (enc [Nat.b2n (vok (r k)); vv (r k)]) = [Nat.b2n (vok (r k)); vv (r k)]).
  apply projs_enc. discriminate.
Qed.

(* the mill part of a CAS whose read value is in V: its store is closed *)
Lemma cl_vst : forall (V : val -> Prop) m yd yp c k r, V 0 -> V 1 -> yd <> yp -> V (vv (r k)) -> cl V (vst m yd yp c k) r.
Proof.
  intros V m yd yp c k r V0 V1 N Hk. split; [|intros w l _ _; constructor].
  rewrite (vst_wvals _ _ _ _ _ _ N). constructor; [apply V_b2n; auto|].
  constructor; [exact Hk|constructor].
Qed.

Lemma cl_inst : forall V i r d, dof i r = Some d -> cl V i r -> forall r', cl V (inst_of d) r'.
Proof.
  intros V [m x c|m x c v|m x c e n| |] r d D Q r'; simpl in D; try discriminate;
  destruct (c r); try discriminate; injection D as <-; exact Q.
Qed.

Lemma cl_inst_eof : forall V i r d, eof i r = Some d -> cl V i r -> forall r', cl V (inst_of d) r'.
Proof.
  intros V i r d D Q r'. destruct (eof_cases _ _ _ D) as [D'|(f & -> & -> & _)].
  - apply (cl_inst V i r d D' Q).
  - exact Q.
Qed.

Lemma cval_V : forall (V : val -> Prop) xs vs x, V 0 -> Forall V vs -> V (cval xs vs x).
Proof.
  intros V xs. induction xs as [|y xs IH]; intros vs x V0 F; simpl; auto.
  destruct vs as [|v vs]; auto. inversion F; subst. destruct (Nat.eqb x y); auto.
Qed.

(* ---------- the registers R1 considers ---------- *)
Lemma bl_len : forall p c cc pc N B f n, length (bl p c cc pc N B f n) = n.
Proof. intros. induction n; simpl; [reflexivity|]. rewrite length_app, IHn. simpl. lia. Qed.

Lemma bl_prefix : forall p c cc pc N B f n m i, i < n -> n <= m ->
  nth i (bl p c cc pc N B f n) 0 = nth i (bl p c cc pc N B f m) 0.
Proof.
  intros p c cc pc N B f n m i L. induction m as [|m IH]; intros H; [lia|].
  destruct (Nat.eq_dec n (S m)) as [E|E]; [subst; reflexivity|].
  rewrite IH by lia. simpl. rewrite app_nth1; [reflexivity|]. rewrite bl_len. lia.
Qed.

Lemma creg_bl : forall p c cc pc N B f j,
  creg p c cc pc N B f j = slotv p c cc pc N B f (lreg (bl p c cc pc N B f j)) j.
Proof.
  intros. unfold creg. simpl. rewrite app_nth2 by (rewrite bl_len; lia). rewrite bl_len, Nat.sub_diag. reflexivity.
Qed.

Lemma lreg_bl : forall p c cc pc N B f j i,
  lreg (bl p c cc pc N B f j) i = if Nat.ltb i j then creg p c cc pc N B f i else 0.
Proof.
  intros. unfold lreg. destruct (Nat.ltb_spec i j).
  - unfold creg. symmetry. apply bl_prefix; lia.
  - apply nth_overflow. rewrite bl_len. lia.
Qed.

(* a CAS whose read happened alone, whose place is j: its slot is a CAS's *)
Lemma hpend_at_ai : forall p c cc pc N r j k, hpend_at p c cc pc N r j = Some k -> is_cas (ai cc k) = true.
Proof.
  intros p c cc pc N r j k H. unfold hpend_at in H. apply find_some in H as [_ H].
  destruct (oc cc k), (oh cc k); try discriminate. destruct (ai cc k); simpl in H |- *; try discriminate; reflexivity.
Qed.

(* a pending access whose place is j: its slot is of j's type *)
Lemma pend_at_dec : forall p c cc pc N r j k, pend_at p c cc pc N r j = Some k ->
  dec (ai cc k) = dec (ins p c j r).
Proof.
  intros p c cc pc N r j k H. destruct (pend_at_spec _ _ _ _ _ _ _ _ H) as (_ & _ & _ & t & d & _ & E & F).
  pose proof (fab_eof' _ _ _ _ _ _ _ _ _ _ F) as Ej.
  rewrite <- (dec_eof _ _ _ E), (dec_eof _ _ _ Ej). reflexivity.
Qed.

(* a CAS whose read happened alone, whose place is j: its slot is of j's type *)
Lemma hpend_at_dec : forall p c cc pc N r j k, hpend_at p c cc pc N r j = Some k ->
  dec (ai cc k) = dec (ins p c j r).
Proof.
  intros p c cc pc N r j k H. unfold hpend_at in H. apply find_some in H as [_ H].
  destruct (oc cc k), (oh cc k); try discriminate. destruct (casx (ai cc k)) as [[m xs]|] eqn:Ca; [|discriminate].
  cbn [fab] in H.
  destruct (tatb (ins p c j r) r (TH m xs)) eqn:Tb; [|rewrite andb_false_r in H; discriminate].
  unfold tatb in Tb. destruct (eofR (ins p c j r) r) as [[m' xs']|] eqn:E; [|discriminate].
  apply lst_eqb_eq in Tb. subst xs'.
  rewrite <- (dec_eofR _ _ _ _ E). destruct (ai cc k); simpl in Ca; try discriminate.
  injection Ca as -> ->. reflexivity.
Qed.

(* a binder comes before the read *)
Lemma fbind_lt : forall p c r i x b b', fbind p c r i x b = Some b' -> b' < b.
Proof.
  intros p c r i x b. induction b as [|b IH]; intros b' H; simpl in H; [discriminate|].
  destruct (executes (ins p c b r) r && tiedb (ins p c b r) i).
  - destruct (existsb (Nat.eqb x) (icells (ins p c b r))); [injection H as <-; lia|discriminate].
  - specialize (IH b' H). lia.
Qed.

Lemma fbinder_lt : forall p c r j x b, fbinder p c r j x = Some b -> b < j.
Proof.
  intros p c r j x b H. unfold fbinder in H. destruct (_ && _ && _); [|discriminate]. eapply fbind_lt; eauto.
Qed.

Lemma cellv_V : forall p (V : val -> Prop) c cc pc N B f r J, V 0 -> tclosed p V ->
  (forall i, i < J -> kV V (ins p c i r) (r i)) ->
  (forall j x, V (rv cc j x)) -> (forall j x, V (f j x)) -> forall n j x, j <= J -> V (cellv p c cc pc N B f r n j x).
Proof.
  intros p V c cc pc N B f r J V0 Cl Vr Vv Vf n. induction n as [|n IH]; intros j x Lj; simpl;
    (destruct (Nat.ltb j pc); [auto|]); (destruct (is_load _ && icond _ _); [|auto]);
    (destruct (pend_at _ _ _ _ _ _ _); [auto|]); (destruct (hpend_at _ _); [auto|]); auto.
  destruct (B j); auto. destruct (fbinder p c r j x) as [b|] eqn:Fb; auto.
  pose proof (fbinder_lt _ _ _ _ _ _ Fb) as Lb.
  assert (IHb : V (cellv p c cc pc N B f r n b x)) by (apply IH; lia).
  pose proof (Cl c b r (fun i Li => Vr i ltac:(lia))) as (Q & _). unfold bvx.
  destruct (ins p c b r) as [m ys cb|m ys cb v|m ys cb e nv| |] eqn:E; auto;
    try (destruct (vok (r b))); auto; apply cval_V; auto; unfold wvals in Q; rewrite E in Q; exact Q.
Qed.

Lemma creg_V : forall p (V : val -> Prop) c cc pc N B f, wf p -> V 0 -> tclosed p V ->
  (forall j, j < pc -> ai cc j = ins p c j (rg cc)) ->
  (forall j, kV V (ai cc j) (rg cc j)) -> (forall j x, V (rv cc j x)) -> (forall j x, V (f j x)) ->
  forall j, kV V (ins p c j (creg p c cc pc N B f)) (creg p c cc pc N B f j).
Proof.
  intros p V c cc pc N B f W V0 Cl Ap Vr Vv Vf j. induction j as [j IH] using lt_wf_ind.
  set (g := creg p c cc pc N B f) in *.
  set (r := lreg (bl p c cc pc N B f j)).
  assert (Ag : forall i, i < j -> r i = g i)
    by (intros i Li; unfold r, g; rewrite lreg_bl; apply Nat.ltb_lt in Li; rewrite Li; reflexivity).
  assert (Ins : forall i, i <= j -> ins p c i r = ins p c i g)
    by (intros i Li; apply (proj1 (W c i r g (fun q Lq => Ag q ltac:(lia))))).
  assert (VL : forall i, i < j -> kV V (ins p c i r) (r i))
    by (intros i Li; rewrite (Ins i ltac:(lia)), (Ag i Li); apply IH; exact Li).
  rewrite <- (Ins j (le_n j)). unfold g. rewrite creg_bl. fold r. unfold slotv.
  destruct (Nat.ltb_spec j pc) as [L|L].
  - assert (Gr : forall i, i < j -> r i = rg cc i).
    { intros i Li. rewrite (Ag i Li). unfold g. rewrite creg_bl. unfold slotv.
      rewrite (proj2 (Nat.ltb_lt i pc) ltac:(lia)). reflexivity. }
    rewrite (proj1 (W c j r (rg cc) Gr)), <- (Ap j L). apply Vr.
  - destruct (is_load _ && icond _ _) eqn:Ld; [|apply kV_0; exact V0].
    apply andb_prop in Ld as [Ld _].
    destruct (pend_at p c cc pc N r j) as [k|] eqn:Pa.
    { apply (kV_dec V (ai cc k)); [apply (pend_at_dec _ _ _ _ _ _ _ _ Pa)|apply Vr]. }
    apply kV_cfx; [exact V0|intros Ci; apply (clr_V1 V _ V0 Ci (proj2 (Cl c j r VL)))|].
    destruct (hpend_at p c cc pc N r j) as [k|] eqn:Hp.
    { pose proof (hpend_at_cas _ _ _ _ _ _ _ _ Hp) as Ci.
      pose proof (kV_dec V _ _ _ (hpend_at_dec _ _ _ _ _ _ _ _ Hp) (Vr k)) as Vk.
      destruct (vok _); [|exact Vk].
      apply kV_vd; auto. apply V_b2n; auto. apply (clr_V1 V _ V0 Ci (proj2 (Cl c j r VL))). }
    cbv zeta. set (l := map (cellv p c cc pc N B f r j j) (icells (ins p c j r))).
    replace (if is_cas (ins p c j r) then vd (Nat.eqb (enc l) (cexp (ins p c j r) r) && fbit f (ins p c j r) j) (enc l) else enc l)
      with (areg (ins p c j r) (Nat.eqb (enc l) (cexp (ins p c j r) r) && fbit f (ins p c j r) j) (enc l))
      by (destruct (ins p c j r); reflexivity).
    apply (proj2 (Cl c j r VL)); [unfold l; rewrite length_map; reflexivity|].
    apply Forall_forall. intros v Hv. unfold l in Hv. apply in_map_iff in Hv. destruct Hv as (x & <- & _).
    apply (cellv_V p V c cc pc N B f r j); auto.
Qed.

(* ---------- the theorem ---------- *)
Section Thm.
Variables (p : prog) (V : val -> Prop).
Hypothesis W : wf p.
Hypothesis V0 : V 0.
Hypothesis Cl : tclosed p V.

Definition OV (s : st) : Prop := (forall y x, isw s y -> V (wv s y x)) /\
  (forall c j, kV V (ai (cs s c) j) (rg (cs s c) j)) /\ (forall c j x, V (rv (cs s c) j x)).

(* a passed slot holds the instruction there *)
Lemma passed_ai : forall s c j, Inv1 p s -> j < pcs s c -> ai (cs s c) j = ins p c j (rg (cs s c)).
Proof. intros s c j I L. destruct (cm_set p s c j I L) as (tau & T). apply (proj2 (i_set p s I c j tau T)). Qed.

Lemma OV_passed : forall s c, Inv1 p s -> OV s -> forall j, j < pcs s c -> kV V (ins p c j (rg (cs s c))) (rg (cs s c) j).
Proof. intros s c I (_ & O & _) j L. rewrite <- (passed_ai s c j I L). apply O. Qed.

(* what an event step reads and writes is in V *)
Lemma ev_V : forall s c k i m' a K u w Bd pc' tp' cm',
  InvAll p s -> OV s -> oc (cs s c) k = None ->
  eff (tm s) i (rg (cs s c)) (mof s c) m' a K u w ->
  cl V i (rg (cs s c)) ->
  OV (evs s c k i m' a K u w Bd pc' tp' cm').
Proof.
  intros s c k i m' a K u w Bd pc' tp' cm' [I J L] [OW [OR ORv]] Ho He [CW CE].
  assert (VA : kV V i a).
  { destruct (xload i (rg (cs s c))) eqn:X.
    - destruct (eff_read _ _ _ _ _ _ _ _ _ He X) as ((R1 & _) & Ea). subst a.
      apply CE; [unfold rdvals; rewrite length_map; reflexivity|].
      apply Forall_forall. intros v Hv. apply in_map_iff in Hv. destruct Hv as (x & <- & Hx).
      unfold rdval. destruct (u x) as [y|] eqn:Ey; auto.
      pose proof (R1 x Hx) as Hin. rewrite Ey in Hin. simpl in Hin.
      destruct (j_hist p s J x y Hin) as (e & i0 & A1 & A2 & _). apply (OW y x). exists e. auto.
    - destruct (eff_noread _ _ _ _ _ _ _ _ _ He X) as [-> _]. apply kV_0. exact V0. }
  split.
  - intros y x (e & He' & Ew). unfold ent, evs in He'; cbn [lg] in He'.
    rewrite nth_error_app_last, <- (i_tm p s I) in He'.
    destruct (Nat.ltb_spec y (tm s)) as [Ly|Ly].
    + assert (isw s y) as Q by (exists e; auto). specialize (OW y x Q). unfold evs; cbn [wv].
      destruct w eqn:Ew0.
      * destruct (eff_write _ _ _ _ _ _ _ _ _ He eq_refl) as (H' & R0 & _ & _ & _ & _ & _ & Q6 & _).
        rewrite Q6. rewrite upd_neq by lia. exact OW.
      * destruct (eff_nowrite _ _ _ _ _ _ _ _ _ He eq_refl) as (_ & Q2 & _). rewrite Q2. exact OW.
    + destruct (Nat.eqb_spec y (tm s)); [|discriminate]. injection He' as <-. cbn [ew] in Ew. subst y w.
      destruct (eff_write _ _ _ _ _ _ _ _ _ He eq_refl) as (H' & R0 & _ & _ & _ & _ & _ & Q6 & _).
      unfold evs; cbn [wv]. rewrite Q6, upd_eq. apply cval_V; auto.
  - split.
    + intros c' j. rewrite rg_s', ai_s'. destruct (Nat.eqb c' c); [destruct (Nat.eqb j k)|]; auto.
    + intros c' j x. rewrite rv_s'. destruct (Nat.eqb c' c); [destruct (Nat.eqb j k)|]; auto.
      unfold rdval. destruct (u x) as [y|] eqn:Ey; auto.
      assert (Xl : xload i (rg (cs s c)) = true) by (apply (eff_u _ _ _ _ _ _ _ _ _ He x y Ey)).
      destruct (eff_read _ _ _ _ _ _ _ _ _ He Xl) as ((R1 & R2) & _).
      destruct (in_dec Nat.eq_dec x (icells i)) as [Hx|Hx]; [|rewrite (R2 x Hx) in Ey; discriminate].
      pose proof (R1 x Hx) as Hin. rewrite Ey in Hin. simpl in Hin.
      destruct (j_hist p s J x y Hin) as (e & i0 & A1 & A2 & _). apply (OW y x). exists e. auto.
Qed.

(* a CAS's read alone: what it reads is in V *)
Lemma rd_V : forall s c k xs B m' a K u w bv,
  InvAll p s -> OV s -> oc (cs s c) k = None -> pcs s c <= k -> oh (cs s c) k = None ->
  eff (tm s) (ILd Plain xs (fun _ => true)) (rg (cs s c)) (mof s c) m' a K u w ->
  clr V (crd Plain xs) ->
  OV (sread s c k Plain xs B m' a K u w bv).
Proof.
  intros s c k xs B m' a K u w bv [I J L] [OW [OR ORv]] Ho Hk Hh He CR.
  assert (Rv : forall x, V (rdval (mof s c) u x)).
  { intros x. unfold rdval. destruct (u x) as [y|] eqn:Ey; auto.
    destruct (rd_u p s c k xs B m' a K u w bv I J Ho Hk Hh He x y Ey) as (Q & _). apply (OW y x Q). }
  assert (VA : kV V (crd Plain xs) (vd bv a)).
  { destruct (eff_read _ _ _ _ _ _ _ _ _ He eq_refl) as (_ & Ea). subst a.
    apply (CR bv); [unfold rdvals; rewrite length_map; reflexivity|].
    apply Forall_forall. intros v Hv. apply in_map_iff in Hv. destruct Hv as (x & <- & _). apply Rv. }
  destruct (rd_mem p s c k xs B m' a K u w bv I J Ho Hk Hh He) as (_ & Mv & _).
  split; [|split].
  - intros y x Q. rewrite Mv. apply OW. apply (rd_isw p s c k xs B m' a K u w bv I J Ho Hk Hh He). exact Q.
  - intros c' j. unfold sread; simpl. unfold upd. destruct (Nat.eqb c' c); [simpl; destruct (Nat.eqb j k)|]; auto.
  - intros c' j x. unfold sread; simpl. unfold upd. destruct (Nat.eqb c' c); [simpl; destruct (Nat.eqb j k)|]; auto.
Qed.

Lemma OV_es : forall t e, OV t -> OV (set_es t e).
Proof. intros t e O. exact O. Qed.

Lemma OV_step : forall s t, run p s -> InvAll p s -> OV s -> step p s t -> OV t.
Proof.
  intros s t R0 IA O H. destruct IA as [I J L].
  destruct (step_cases p s t H) as [(c & i & m' & a & K & u & w & H1 & H2 & H3 & H4 & Hbh & Hh & _ & _ & H6 & _ & ->)|[(c & k & d & B & m' & a & K & u & w & H1 & H2 & Hso & Hh & _ & _ & H5 & _ & ->)|[(c & d & H1 & H2 & H3 & H4 & H4m & Hfh & ->)|[(c & k & xs & B & m' & a & K & u & w & bv & H1 & H2 & Hh & Hso & H4 & H5 & _ & ->)|[(c & S1 & S2 & S3 & S6 & S5 & S4 & _ & ->)|(cX & jX & bX & BX & oX & HjX & HfX & HcX & ->)]]]]].
  - apply ev_V; auto; [constructor; auto|]. rewrite <- H1. apply Cl. intros j Lj. apply (OV_passed s c I O j Lj).
  - apply OV_es.
    set (f0 := fun (_ : nat) (_ : cell) => 0).
    set (r0 := creg p c (cs s c) (pcs s c) (tp s c) (bor (bd (cs s c)) B) f0) in *.
    assert (Dj' : exists j, eof (ins p c j r0) r0 = Some d).
    { destruct Hh as [(_ & Ok)|(t1 & xs & ev & nv & _ & _ & _ & _ & Ok)].
      - destruct (Ok f0) as (j & _ & F & _). exists j. exact (first_at_eof _ _ _ _ _ _ _ _ F).
      - destruct (Ok f0) as (j & _ & _ & D & _). exists j. exact D. }
    destruct Dj' as (j & Dj).
    assert (VR : forall j, kV V (ins p c j r0) (r0 j))
      by (apply (creg_V p V); auto; [intros q Lq; apply (passed_ai s c q I Lq)|apply (proj1 (proj2 O))|apply (proj2 (proj2 O))]).
    apply ev_V; auto; [constructor; auto|]. exact (cl_inst_eof V _ _ _ Dj (Cl c j r0 (fun q _ => VR q)) _).
  - destruct O as [OW [OR ORv]]. split; [exact OW|split; [intros c0 j|]].
    + rewrite (rg_match p s c c0), (ai_match p s c c0). destruct (Nat.eqb c0 c && Nat.eqb j (pcs s c)) eqn:E; [|apply OR].
      apply andb_prop in E as [E1 E2]. apply Nat.eqb_eq in E1, E2. subst c0 j.
      apply (kV_dec V (ai (cs s c) (pcs s c))); [|apply OR]. rewrite H2. apply (dec_eof _ _ _ H3).
    + intros c0 j x. rewrite (rv_match p s c c0). auto.
  - set (f0 := fun (_ : nat) (_ : cell) => 0).
    destruct (H4 f0) as (j & F0 & _).
    set (r0 := creg p c (cs s c) (pcs s c) (tp s c) (bor (bd (cs s c)) B) f0) in *.
    pose proof (first_atR_eofR _ _ _ _ _ _ _ _ _ F0) as Dj.
    apply rd_V; auto; [constructor; auto|].
    assert (VR : forall j, kV V (ins p c j r0) (r0 j))
      by (apply (creg_V p V); auto; [intros q Lq; apply (passed_ai s c q I Lq)|apply (proj1 (proj2 O))|apply (proj2 (proj2 O))]).
    apply (clr_eofR V _ r0 _ _ Dj (proj2 (Cl c j r0 (fun q _ => VR q)))).
  - destruct O as [OW [OR ORv]]. split; [exact OW|split; [intros c0 j|]].
    + rewrite (rg_skip p s c c0), (ai_skip p s c c0). destruct (Nat.eqb c0 c && Nat.eqb j (pcs s c)) eqn:E; [|apply OR].
      apply andb_prop in E as [E1 E2]. apply Nat.eqb_eq in E1, E2. subst c0 j.
      destruct (oh (cs s c) (pcs s c)) as [t1|] eqn:Oh.
      * apply (kV_dec V (ai (cs s c) (pcs s c))); [|apply OR].
        destruct (i_half p s I c (pcs s c) t1 S2 Oh (le_n _)) as (_ & (xs0 & Ax) & _).
        pose proof (S3 ltac:(congruence)) as Er. rewrite Ax in Er |- *. simpl in Er.
        apply (dec_eofR _ _ _ _ Er).
      * rewrite (i_rg0 p s I c _ S2 Oh). apply kV_0. exact V0.
    + intros c0 j x. rewrite (rv_skip p s c c0). auto.
  - assert (OF : OV (sflp s cX oX bX)).
    { destruct O as [OW [OR ORv]]. destruct oX as [kF|]; [destruct bX|]; cbn [sflp]; try (split; [exact OW|split; [exact OR|exact ORv]]).
      destruct (cfix_rec _ _ _ _ _ _ _ _ _ HcX) as (HpF & HoF & HhF & HvF).
      split; [exact OW|split].
      + intros c0 j. rewrite cs_cf. destruct (Nat.eqb c0 cX) eqn:Ec; [|apply OR]. apply Nat.eqb_eq in Ec. subst c0.
        cbn [rg ai]. unfold upd. destruct (Nat.eqb j kF) eqn:Ej; [|apply OR]. apply Nat.eqb_eq in Ej. subst j.
        destruct (oh (cs s cX) kF) as [t1|] eqn:Oh; [|congruence].
        destruct (half_xload p s cX kF t1 I HoF Oh) as (_ & Ca). apply kV_vd; auto.
      + intros c0 j x. rewrite rv_cf. auto. }
    destruct OF as [OW [OR ORv]]. split; [exact OW|split; [intros c0 j; rewrite ai_cx, rg_cx; apply OR|intros c0 j x; rewrite rv_cx; apply ORv]].
Qed.

Lemma OV_run : forall s, run p s -> OV s.
Proof.
  intros s R. induction R as [|s t R IH H].
  - split; [intros y x (e & He & _); unfold ent in He; simpl in He; destruct y; discriminate|split; intros; simpl; [apply kV_0; exact V0|auto]].
  - apply (OV_step s t R); auto. apply Inv_run. auto.
Qed.

Theorem no_thin_air : forall s, run p s ->
  (forall y x, isw s y -> V (wv s y x)) /\ (forall c j, kV V (ai (cs s c) j) (rg (cs s c) j)).
Proof. intros s R. destruct (OV_run s R) as (A & B & _). auto. Qed.

End Thm.
