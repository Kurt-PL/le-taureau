(* Model2: the registers R1 considers, for a well-formed programme. Part 1:
   register j depends only on the registers before it. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2Oota.

Definition agree (r r' : regs) (j : nat) : Prop := forall i, i < j -> r i = r' i.

(* S3c: the fixed verdict depends on the registers only through the expected value *)
Lemma cfx_ext : forall cc j i r r' a, cexp i r = cexp i r' -> cfx cc j i r a = cfx cc j i r' a.
Proof. intros cc j i r r' a E. rewrite !cfx_unfold. rewrite E. reflexivity. Qed.
Lemma cfx_ncas : forall cc j i r a, is_cas i = false -> cfx cc j i r a = a.
Proof. intros cc j i r a E. rewrite !cfx_unfold. rewrite E. destruct (fx cc j); reflexivity. Qed.
Lemma cfx_none : forall cc j i r a, fx cc j = None -> cfx cc j i r a = a.
Proof. intros cc j i r a E. rewrite !cfx_unfold. rewrite E. reflexivity. Qed.
Lemma cfx_fx : forall cc cc' j i r a, fx cc j = fx cc' j -> cfx cc j i r a = cfx cc' j i r a.
Proof. intros cc cc' j i r a E. rewrite !cfx_unfold. rewrite E. reflexivity. Qed.

Lemma cfx_ok : forall cc k i r a, fxok cc k i r a -> icond i r = true -> cfx cc k i r a = a.
Proof.
  intros cc k i r a H C. rewrite !cfx_unfold. destruct (fx cc k) as [b|] eqn:E; [|reflexivity].
  destruct (is_cas i) eqn:Ci; [|reflexivity]. rewrite <- (H b E Ci C). apply vd_split.
Qed.

Lemma cfx_ok_x : forall cc k i r r0 a, fxok cc k i r0 a -> ieval i r = ieval i r0 -> executes i r = true ->
  cfx cc k i r a = a.
Proof.
  intros cc k i r r0 a H E X. rewrite !cfx_unfold. destruct (fx cc k) as [b|] eqn:Fe; [|reflexivity].
  destruct (is_cas i) eqn:Ci; [|reflexivity].
  assert (Ic : icond i r0 = true).
  { destruct i; simpl in Ci; try discriminate. unfold executes in X; simpl in X. unfold icond in *. rewrite <- E. exact X. }
  rewrite (cexp_ieval _ _ _ E), <- (H b Fe Ci Ic). apply vd_split.
Qed.

Lemma cfx_cfail : forall cc j i r a, (vok a = true -> cfailv i r a = false) ->
  vok (cfx cc j i r a) = true -> cfailv i r (cfx cc j i r a) = false.
Proof.
  intros cc j i r a H V. rewrite !cfx_unfold in *. destruct (fx cc j) as [b|]; [|auto].
  destruct (is_cas i) eqn:Ci; [|auto]. rewrite vok_vd in V. apply andb_prop in V as [Bt E].
  destruct i; simpl in Ci; try discriminate. unfold cfailv. rewrite vok_vd, vv_vd. simpl in E. rewrite Bt, E. simpl. rewrite E. apply andb_false_r.
Qed.

Lemma hp_cfail : forall i r a bit, vok (if vok a then vd (negb (cfailv i r a) && bit) (vv a) else a) = true ->
  cfailv i r (if vok a then vd (negb (cfailv i r a) && bit) (vv a) else a) = false.
Proof.
  intros i r a bit V. destruct (vok a) eqn:Va; [|congruence].
  rewrite vok_vd in V. apply andb_prop in V as [N0 Bt]. pose proof N0 as N. apply negb_true_iff in N.
  rewrite N0, Bt. simpl andb.
  unfold cfailv in *. destruct i; try reflexivity. rewrite vok_vd, vv_vd. rewrite Va in N. simpl in N |- *. exact N.
Qed.

Lemma cfx_eof : forall cc j i r d r0 a, eof i r = Some d -> fxok cc j (inst_of d) r0 a -> cfx cc j i r a = a.
Proof.
  intros cc j i r d r0 a D H. rewrite !cfx_unfold. destruct (fx cc j) as [b|] eqn:Fe; [|reflexivity].
  destruct (eof_cexp i r d r0 D) as (C & E). destruct (is_cas i) eqn:Ci; [|reflexivity].
  assert (Ic : icond (inst_of d) r0 = true) by (destruct d; reflexivity).
  rewrite <- E, <- (H b Fe C Ic). apply vd_split.
Qed.

Lemma agree_le : forall r r' j j', agree r r' j -> j' <= j -> agree r r' j'.
Proof. intros r r' j j' H L i Li. apply H. lia. Qed.

Lemma find_ext_in : forall {A} (f g : A -> bool) l, (forall x, In x l -> f x = g x) -> find f l = find g l.
Proof.
  intros A f g l. induction l as [|a l IH]; intros H; simpl; auto.
  rewrite (H a (or_introl eq_refl)). destruct (g a); auto. apply IH. intros x X. apply H. right. auto.
Qed.

Lemma allin_ext : forall f g a n, (forall q, a <= q < a + n -> f q = g q) -> allin f a n = allin g a n.
Proof.
  intros f g a n. revert a. induction n as [|n IH]; intros a H; simpl; auto.
  rewrite (H a ltac:(lia)). f_equal. apply IH. intros q Q. apply H. lia.
Qed.


Section Loc.
Variable p : prog.
Hypothesis W : wf p.

Lemma ins_agree : forall c j r r', agree r r' j ->
  ins p c j r = ins p c j r' /\ ieval (ins p c j r) r = ieval (ins p c j r) r'.
Proof. intros c j r r' A. apply W. exact A. Qed.

Lemma exec_agree : forall c j r r', agree r r' j -> executes (ins p c j r) r = executes (ins p c j r') r'.
Proof.
  intros c j r r' A. destruct (ins_agree c j r r' A) as [E1 E2]. rewrite <- E1.
  unfold executes, icond. rewrite E2. reflexivity.
Qed.

(* a CAS's comparison at j depends on the registers up to j, its own included *)
Lemma cfail_agree : forall c j r r', agree r r' (S j) -> cfail (ins p c j r) r j = cfail (ins p c j r') r' j.
Proof.
  intros c j r r' A. assert (A' : agree r r' j) by (apply (agree_le r r' (S j)); auto).
  destruct (ins_agree c j r r' A') as [E1 E2]. rewrite <- E1. symmetry. apply cfail_eval; [symmetry; exact E2|].
  symmetry. apply A. lia.
Qed.

Lemma cfailv_agree : forall c j r r' v, agree r r' j -> cfailv (ins p c j r) r v = cfailv (ins p c j r') r' v.
Proof.
  intros c j r r' v A. destruct (ins_agree c j r r' A) as [E1 E2]. rewrite <- E1.
  destruct (ins p c j r) as [| |m0 x0 c0 e0 n0| |]; simpl in *; auto. injection E2 as C1 C2 C3. rewrite C1, C2. reflexivity.
Qed.

Lemma eof_agree : forall c j r r', agree r r' j -> eof (ins p c j r) r = eof (ins p c j r') r'.
Proof.
  intros c j r r' A. destruct (ins_agree c j r r' A) as [E1 E2]. rewrite <- E1.
  destruct (ins p c j r) as [| | |[]|]; simpl in *; auto; injection E2; intros; rewrite ?H, ?H0, ?H1; reflexivity.
Qed.

Lemma dof_agree : forall c j r r', agree r r' j -> dof (ins p c j r) r = dof (ins p c j r') r'.
Proof.
  intros c j r r' A. destruct (ins_agree c j r r' A) as [E1 E2]. rewrite <- E1.
  destruct (ins p c j r); simpl in *; auto; injection E2; intros; rewrite ?H, ?H0, ?H1; reflexivity.
Qed.

Lemma eofR_agree : forall c j r r', agree r r' j -> eofR (ins p c j r) r = eofR (ins p c j r') r'.
Proof.
  intros c j r r' A. destruct (ins_agree c j r r' A) as [E1 E2]. rewrite <- E1.
  destruct (ins p c j r); simpl in *; auto; injection E2; intros; rewrite ?H, ?H0, ?H1; reflexivity.
Qed.

Lemma tatb_agree : forall c j r r' g, agree r r' j -> tatb (ins p c j r) r g = tatb (ins p c j r') r' g.
Proof. intros c j r r' [d|m xs] A; unfold tatb; [rewrite (eof_agree c j r r' A)|rewrite (eofR_agree c j r r' A)]; reflexivity. Qed.

(* the place of an access depends only on the registers before it *)
Lemma fab_agree : forall c cc pc N r r', pend_ok cc pc -> forall n T g j, agree r r' j ->
  fab p c cc pc N r n T g j = fab p c cc pc N r' n T g j.
Proof.
  intros c cc pc N r r' PO n. induction n as [|n IH]; intros T g j A; [reflexivity|]. cbn [fab].
  assert (TK : forall j', j' <= j ->
    existsb (fun k' => match oc cc k' with
                       | Some t' => Nat.ltb t' T && match eof (ai cc k') r with Some d' => fab p c cc pc N r n t' (TF d') j' | None => false end
                       | None => false end) (seq pc (N - pc)) =
    existsb (fun k' => match oc cc k' with
                       | Some t' => Nat.ltb t' T && match eof (ai cc k') r' with Some d' => fab p c cc pc N r' n t' (TF d') j' | None => false end
                       | None => false end) (seq pc (N - pc))).
  { intros j' L. apply existsb_ext_in. intros k' Hk. apply in_seq in Hk.
    destruct (oc cc k') as [t'|] eqn:O; auto. destruct (PO k' ltac:(congruence) ltac:(lia)) as (d' & Ad & Nd).
    rewrite Ad, !(eof_inst d' _ Nd). f_equal. apply IH. apply (agree_le r r' j); auto. }
  assert (TH : forall j', j' <= j ->
    existsb (fun k' => match oh cc k' with
                       | Some t' => Nat.ltb t' T && hliveb cc k' T && match casx (ai cc k') with
                                              | Some (m', xs') => fab p c cc pc N r n t' (TH m' xs') j'
                                              | None => false end
                       | None => false end) (seq pc (N - pc)) =
    existsb (fun k' => match oh cc k' with
                       | Some t' => Nat.ltb t' T && hliveb cc k' T && match casx (ai cc k') with
                                              | Some (m', xs') => fab p c cc pc N r' n t' (TH m' xs') j'
                                              | None => false end
                       | None => false end) (seq pc (N - pc))).
  { intros j' L. apply existsb_ext_in. intros k' Hk.
    destruct (oh cc k'); auto. destruct (casx (ai cc k')) as [[m' xs']|]; auto.
    f_equal. apply IH. apply (agree_le r r' j); auto. }
  rewrite (tatb_agree c j r r' g A), (TK j (le_n j)), (TH j (le_n j)). f_equal.
  assert (TF : forall j', j' < j ->
    existsb (fun k' => match oh cc k' with
                       | Some t' => Nat.ltb t' T && hliveb cc k' T && match casx (ai cc k') with
                                              | Some (m', xs') => fab p c cc pc N r n t' (M2Model.TH m' xs') j' &&
                                                                  cfailv (ins p c j' r) r (r j')
                                              | None => false end
                       | None => false end) (seq pc (N - pc)) =
    existsb (fun k' => match oh cc k' with
                       | Some t' => Nat.ltb t' T && hliveb cc k' T && match casx (ai cc k') with
                                              | Some (m', xs') => fab p c cc pc N r' n t' (M2Model.TH m' xs') j' &&
                                                                  cfailv (ins p c j' r') r' (r' j')
                                              | None => false end
                       | None => false end) (seq pc (N - pc))).
  { intros j' L. apply existsb_ext_in. intros k' Hk.
    destruct (oh cc k'); auto. destruct (casx (ai cc k')) as [[m' xs']|]; auto.
    rewrite (IH _ _ _ (agree_le r r' j j' A (Nat.lt_le_incl _ _ L))), (cfailv_agree c j' r r' _ (agree_le r r' j j' A (Nat.lt_le_incl _ _ L))), (A j' L). reflexivity. }
  apply allin_ext. intros q Q. assert (Aq : agree r r' q) by (apply (agree_le r r' j); auto; lia).
  rewrite (TF q ltac:(lia)), (exec_agree c q r r' Aq), (proj1 (ins_agree c q r r' Aq)), (TK q ltac:(lia)). reflexivity.
Qed.

Lemma first_atb_agree : forall c cc pc N r r' T d j, pend_ok cc pc -> agree r r' j ->
  first_atb p c cc pc N r T d j = first_atb p c cc pc N r' T d j.
Proof. intros. unfold first_atb. apply fab_agree; auto. Qed.

Lemma hpend_at_agree : forall c cc pc N r r' j, pend_ok cc pc -> agree r r' j ->
  hpend_at p c cc pc N r j = hpend_at p c cc pc N r' j.
Proof.
  intros c cc pc N r r' j PO A. unfold hpend_at. apply find_ext_in. intros k Hk.
  destruct (oc cc k), (oh cc k); auto. destruct (casx (ai cc k)) as [[m xs]|]; auto. apply fab_agree; auto.
Qed.

(* the same for the place itself *)
Lemma plc_agree : forall c cc pc n r r' T g j, agree r r' j ->
  plc p c cc pc r n T g j -> plc p c cc pc r' n T g j.
Proof.
  intros c cc pc n. induction n as [|n IH]; intros r r' T g j A H; [destruct H|]. cbn [plc] in H |- *.
  assert (Asym : forall q, q <= j -> agree r' r q) by (intros q L i Li; symmetry; apply A; lia).
  destruct H as (F1 & F2 & F3 & F4). split; [exact F1|]. split; [|split].
  - destruct g; [rewrite <- (eof_agree c j r r' A)|rewrite <- (eofR_agree c j r r' A)]; exact F2.
  - intros [(k' & t' & d' & P & O & L & Q)|(k' & t' & m' & xs' & P & O & L & Hl & Q)]; apply F3; [left|right].
    + exists k', t', d'. split; [exact P|]. split; [exact O|]. split; [exact L|]. apply (IH r' r); auto.
    + exists k', t', m', xs'. split; [exact P|]. split; [exact O|]. split; [exact L|]. split; [exact Hl|]. apply (IH r' r); auto.
  - intros j' L1 L2 Ex Fx T0. assert (Aj : agree r r' j') by (apply (agree_le r r' j); auto; lia).
    assert (Aj' : agree r r' (S j')) by (apply (agree_le r r' j); auto; lia).
    rewrite <- (exec_agree c j' r r' Aj) in Ex. rewrite <- (proj1 (ins_agree c j' r r' Aj)) in T0.
    specialize (F4 j' L1 L2 Ex). lapply F4; [clear F4; intros F4|].
    2:{ intros v X. rewrite (cfailv_agree c j' r r' v Aj). apply (Fx v).
        destruct X as (k' & t' & m' & xs' & P & O & L & Hl & Q & Ev).
        exists k', t', m', xs'. split; [exact P|]. split; [exact O|]. split; [exact L|]. split; [exact Hl|].
        split; [apply (IH r r'); auto|rewrite Ev; apply A; lia]. }
    destruct (F4 T0) as (k' & t' & d' & P & O & L & Q). exists k', t', d'.
    split; [exact P|]. split; [exact O|]. split; [exact L|]. apply (IH r r'); auto.
Qed.

Lemma first_at_agree : forall c cc pc r r' T d j, agree r r' j ->
  first_at p c cc pc r T d j -> first_at p c cc pc r' T d j.
Proof. intros. unfold first_at in *. apply (plc_agree c cc pc (S T) r r'); auto. Qed.

Lemma placed_agree : forall c cc pc r r' k d j, agree r r' j ->
  placed p c cc pc r k d j -> placed p c cc pc r' k d j.
Proof. intros c cc pc r r' k d j A (P & t & O & F). split; auto. exists t. split; auto. apply (first_at_agree c cc pc r r'); auto. Qed.

Lemma fbind_agree : forall c r r' i x b, agree r r' b -> fbind p c r i x b = fbind p c r' i x b.
Proof.
  intros c r r' i x b. induction b as [|b IH]; intros A; simpl; auto.
  assert (Ab : agree r r' b) by (apply (agree_le r r' (S b)); auto).
  rewrite (exec_agree c b r r' Ab), (proj1 (ins_agree c b r r' Ab)).
  destruct (executes (ins p c b r') r' && tiedb (ins p c b r') i); auto.
Qed.

Lemma fbinder_agree : forall c r r' j x, agree r r' j -> fbinder p c r j x = fbinder p c r' j x.
Proof.
  intros c r r' j x A. unfold fbinder. destruct (ins_agree c j r r' A) as [E1 E2].
  rewrite <- E1. assert (Ic : icond (ins p c j r) r = icond (ins p c j r) r') by (unfold icond; rewrite E2; auto).
  rewrite <- Ic. destruct (bread _ && _ && _); auto. apply fbind_agree. auto.
Qed.

Lemma bvx_agree : forall c r r' b j x v, b < j -> agree r r' j -> bvx p c r b x v = bvx p c r' b x v.
Proof.
  intros c r r' b j x v L A. assert (Ab : agree r r' b) by (apply (agree_le r r' j); auto; lia).
  unfold bvx. destruct (ins_agree c b r r' Ab) as [E1 E2]. rewrite <- E1.
  destruct (ins p c b r) as [m ys cb|m ys cb w|m ys cb e nv| |]; simpl in E2; try reflexivity.
  - injection E2 as _ E2. rewrite E2. reflexivity.
  - injection E2 as _ E2 E3. rewrite (A b L), E3. reflexivity.
Qed.

Lemma pend_at_agree : forall c cc pc N r r' j, pend_ok cc pc -> agree r r' j ->
  pend_at p c cc pc N r j = pend_at p c cc pc N r' j.
Proof.
  intros c cc pc N r r' j PO A. unfold pend_at. apply find_ext_in. intros k Hk. apply in_seq in Hk.
  destruct (oc cc k) as [t|] eqn:O; auto. destruct (PO k ltac:(congruence) ltac:(lia)) as (d & Ad & Nd).
  rewrite Ad, !(eof_inst d _ Nd). apply first_atb_agree; auto.
Qed.

Lemma cellv_agree : forall c cc pc N B f r r', pend_ok cc pc -> forall n j x, agree r r' j ->
  cellv p c cc pc N B f r n j x = cellv p c cc pc N B f r' n j x.
Proof.
  intros c cc pc N B f r r' PO n. induction n as [|n IH]; intros j x A; cbn [cellv];
    (destruct (Nat.ltb j pc); [reflexivity|]);
    destruct (ins_agree c j r r' A) as [E1 E2]; rewrite <- E1;
    (assert (Ic : icond (ins p c j r) r = icond (ins p c j r) r') by (unfold icond; rewrite E2; auto)); rewrite <- Ic;
    (destruct (is_load (ins p c j r) && icond (ins p c j r) r); [|reflexivity]);
    rewrite (pend_at_agree c cc pc N r r' j PO A); (destruct (pend_at p c cc pc N r' j); [reflexivity|]);
    rewrite (hpend_at_agree c cc pc N r r' j PO A); (destruct (hpend_at p c cc pc N r' j); [reflexivity|]); [reflexivity|].
  destruct (B j); [|reflexivity]. rewrite (fbinder_agree c r r' j x A).
  destruct (fbinder p c r' j x) as [b|] eqn:Fb; [|reflexivity].
  pose proof (fbinder_lt p c r' j x b Fb) as Lb.
  rewrite (bvx_agree c r r' b j x _ Lb A). f_equal. apply IH. apply (agree_le r r' j); auto; lia.
Qed.

Lemma slotv_agree : forall c cc pc N B f r r' j, pend_ok cc pc -> agree r r' j ->
  slotv p c cc pc N B f r j = slotv p c cc pc N B f r' j.
Proof.
  intros c cc pc N B f r r' j PO A. unfold slotv. destruct (Nat.ltb j pc); auto.
  destruct (ins_agree c j r r' A) as [E1 E2]. rewrite <- E1.
  assert (Ic : icond (ins p c j r) r = icond (ins p c j r) r') by (unfold icond; rewrite E2; auto).
  assert (CE : cexp (ins p c j r) r = cexp (ins p c j r) r').
  { destruct (ins p c j r); simpl in *; auto. injection E2 as _ E3 _. exact E3. }
  rewrite <- Ic. destruct (is_load (ins p c j r) && icond (ins p c j r) r); auto.
  rewrite (pend_at_agree c cc pc N r r' j PO A). destruct (pend_at p c cc pc N r' j); auto.
  rewrite (cfx_ext cc j _ r r' _ CE). f_equal.
  rewrite (hpend_at_agree c cc pc N r r' j PO A). destruct (hpend_at p c cc pc N r' j).
  { rewrite (cfailv_agree c j r r' _ A), E1. reflexivity. }
  assert (EV : enc (map (cellv p c cc pc N B f r j j) (icells (ins p c j r))) = enc (map (cellv p c cc pc N B f r' j j) (icells (ins p c j r)))).
  { cbv zeta. erewrite map_ext; [reflexivity|]. intros x. apply cellv_agree; auto. }
  cbv zeta. rewrite EV. rewrite CE. reflexivity.
Qed.

Lemma creg_fix : forall c cc pc N B f j, pend_ok cc pc ->
  creg p c cc pc N B f j = slotv p c cc pc N B f (creg p c cc pc N B f) j.
Proof.
  intros c cc pc N B f j PO. rewrite creg_bl. apply slotv_agree; auto.
  intros i Li. rewrite lreg_bl. apply Nat.ltb_lt in Li. rewrite Li. reflexivity.
Qed.

(* two ways of building the registers agree when each slot of one, computed
   on the other's registers, gives the other's value *)
Lemma creg_ext : forall c cc pc N B g (r : regs), pend_ok cc pc ->
  (forall j, slotv p c cc pc N B g r j = r j) -> forall j, creg p c cc pc N B g j = r j.
Proof.
  intros c cc pc N B g r PO H j. induction j as [j IH] using lt_wf_ind.
  rewrite creg_fix by auto. rewrite <- (H j). apply slotv_agree; [exact PO|].
  intros i Li. apply IH. exact Li.
Qed.

End Loc.

(* ---------- Part 2: tools ---------- *)

(* a find over an interval of naturals sees only the elements where the test holds *)
Lemma find_seq_sub : forall (P : nat -> bool) a n lo hi, a <= lo -> hi <= a + n -> lo <= hi ->
  (forall k, a <= k < a + n -> P k = true -> lo <= k < hi) -> find P (seq a n) = find P (seq lo (hi - lo)).
Proof.
  intros P a n. revert a. induction n as [|n IH]; intros a lo hi L1 L2 L3 H.
  - assert (hi = lo) by lia. subst. rewrite Nat.sub_diag. reflexivity.
  - simpl. destruct (P a) eqn:Pa.
    + destruct (H a ltac:(lia) Pa). assert (lo = a) by lia. subst lo.
      destruct (hi - a) as [|m] eqn:E; [lia|]. simpl. rewrite Pa. reflexivity.
    + destruct (Nat.eq_dec a lo) as [->|Nl].
      * destruct (hi - lo) as [|m] eqn:E.
        -- simpl. assert (hi = lo) by lia. subst hi.
           rewrite (IH (S lo) (S lo) (S lo)) by (try lia; intros k Hk Pk; destruct (H k ltac:(lia) Pk); lia).
           rewrite Nat.sub_diag. reflexivity.
        -- simpl. rewrite Pa. replace m with (hi - S lo) by lia. apply IH; try lia.
           intros k Hk Pk. destruct (H k ltac:(lia) Pk). destruct (Nat.eq_dec k lo); [subst; congruence|lia].
      * apply IH; try lia. intros k Hk Pk. apply H; auto. lia.
Qed.

Lemma first_at_ext : forall p c cc pc r r' T d j, wf p -> (forall i, r i = r' i) ->
  first_at p c cc pc r T d j -> first_at p c cc pc r' T d j.
Proof. intros p c cc pc r r' T d j W E. apply (first_at_agree p W). intros i _. apply E. Qed.

Lemma first_atR_ext : forall p c cc pc r r' T m xs j, wf p -> (forall i, r i = r' i) ->
  first_atR p c cc pc r T m xs j -> first_atR p c cc pc r' T m xs j.
Proof. intros p c cc pc r r' T m xs j W E. unfold first_atR. apply (plc_agree p W). intros i _. apply E. Qed.

Lemma one_dd : forall xs x, one xs = Some x -> dd xs = [x].
Proof. intros xs x H. unfold one in H. destruct (dd xs) as [|y [|z l]]; try discriminate. injection H as <-. auto. Qed.

(* the value of cell x a slot read or made, given the write *)
Definition rdo (s : st) (o : option nat) (x : cell) : val := match o with None => 0 | Some y => wv s y x end.

Lemma fbind_shape : forall p c r i x b b', fbind p c r i x b = Some b' ->
  executes (ins p c b' r) r = true /\ In x (icells (ins p c b' r)) /\ tied (ins p c b' r) i.
Proof.
  intros p c r i x b. induction b as [|b IH]; intros b' H; simpl in H; [discriminate|].
  destruct (executes (ins p c b r) r && tiedb (ins p c b r) i) eqn:E.
  - apply andb_true_iff in E as [E T].
    destruct (existsb (Nat.eqb x) (icells (ins p c b r))) eqn:X; [|discriminate]. injection H as <-.
    split; [auto|]. split; [|apply b_tied; auto].
    apply existsb_exists in X. destruct X as (y & Hy & Q). apply Nat.eqb_eq in Q. subst. auto.
  - apply IH. auto.
Qed.

Lemma fbinder_shape : forall p c r j x b, fbinder p c r j x = Some b ->
  executes (ins p c b r) r = true /\ In x (icells (ins p c b r)) /\ tied (ins p c b r) (ins p c j r) /\
  bread (ins p c j r) = true /\ icond (ins p c j r) r = true /\ In x (icells (ins p c j r)).
Proof.
  intros p c r j x b H. unfold fbinder in H.
  destruct (bread (ins p c j r) && icond (ins p c j r) r && existsb (Nat.eqb x) (icells (ins p c j r))) eqn:E;
    [|discriminate].
  apply andb_true_iff in E as [E X]. apply andb_true_iff in E as [E1 E2].
  destruct (fbind_shape p c r _ x j b H) as (A & B & T). repeat split; auto.
  apply existsb_exists in X. destruct X as (y & Hy & Q). apply Nat.eqb_eq in Q. subst. auto.
Qed.

(* the value of cell x a binder already passed gives: the value of the write
   it read or made there *)
(* a CAS whose read happened alone: its register and values are what the
   writes it took give *)
Lemma half_vals : forall p s c k t, Inv1 p s -> Inv2 p s -> oc (cs s c) k = None -> oh (cs s c) k = Some t ->
  (forall x, rv (cs s c) k x = rdval (mof s c) (rw (cs s c) k) x) /\
  vv (rg (cs s c) k) = enc (rdvals (mof s c) (icells (ai (cs s c) k)) (rw (cs s c) k)).
Proof.
  intros p s c k t I J O Oh. destruct (i_oh p s I c k t Oh) as (e & A & B & C & Eh).
  destruct (i_rw p s I c k t (or_intror (conj O Oh))) as (e' & A' & Rw). rewrite A in A'. injection A' as <-.
  assert (Ei : einstr p s e = ai (cs s c) k) by (unfold einstr; rewrite B, C; reflexivity).
  destruct (j_ew p s J t e _ A Ei) as [W1 _]. rewrite Eh in W1. cbn [negb andb] in W1.
  assert (RW : forall x, rw (cs s c) k x = erf e x) by (intros x; rewrite Rw; unfold wrote; rewrite W1; reflexivity).
  split.
  - intros x. pose proof (j_rv p s J t e x A) as Q. rewrite B, C in Q. rewrite Q. unfold rdv, rdval. rewrite RW. reflexivity.
  - destruct (j_val p s J t e _ A Ei) as [V1 _]. unfold rgof in V1. rewrite B, C in V1.
    assert (Ci : is_cas (ai (cs s c) k) = true).
    { destruct (le_lt_dec (pcs s c) k) as [Lk|Lk].
      - destruct (i_half p s I c k t O Oh Lk) as (_ & (xs & ->) & _). reflexivity.
      - destruct (i_halfp p s I c k t O Oh Lk) as (_ & (xs & X) & _). destruct (ai (cs s c) k); simpl in X; try discriminate; reflexivity. }
    rewrite (rval_cas _ _ Ci) in V1.
    rewrite V1 by (apply (half_xload p s c k t I O Oh)). rewrite rdvals_mof. f_equal. unfold rdvs. apply map_ext. intros x.
    unfold rdv. rewrite RW. reflexivity.
Qed.

Lemma bind_val : forall p s c b x, wf p -> Inv1 p s -> Inv2 p s -> b < pcs s c ->
  executes (ins p c b (rg (cs s c))) (rg (cs s c)) = true -> In x (icells (ins p c b (rg (cs s c)))) ->
  bvx p c (rg (cs s c)) b x (rv (cs s c) b x) = rdo s (rw (cs s c) b x) x.
Proof.
  intros p s c b x W I J L Ex Ix.
  destruct (oc (cs s c) b) as [t|] eqn:Ot.
  2:{ (* a CAS whose read happened alone and that failed: it gives what it read *)
      destruct (passed_fail p s c b I L Ex Ot) as (t1 & Oh & F & Ai).
      destruct (half_vals p s c b t1 I J Ot Oh) as (Rv & _). rewrite Rv. unfold bvx, rdval, rdo.
      pose proof (i_halfv p s I c b t1 Ot Oh L) as VK.
      revert F. destruct (ins p c b (rg (cs s c))) as [| |m0 x0 c0 e0 n0| |]; intros F; simpl in F; try discriminate.
      rewrite VK. reflexivity. }
  destruct (i_rw p s I c b t (or_introl Ot)) as (e & A & Rw). destruct (i_oc p s I c b t Ot) as (e' & A' & B' & C').
  rewrite A in A'. injection A' as <-. pose proof (oc_eh p s c b t e I Ot A B' C') as Eh.
  destruct (proj1 (i_cmA p s I c b) L) as (tau & T). pose proof (proj2 (i_set p s I c b tau T)) as Ai.
  assert (Ei : einstr p s e = ins p c b (rg (cs s c))) by (unfold einstr; rewrite B', C'; exact Ai).
  pose proof (j_rv p s J t e x A) as Rv. rewrite B', C' in Rv.
  destruct (j_ew p s J t e _ A Ei) as [W1 W2]. unfold rgof in W1, W2. rewrite B' in W1, W2.
  rewrite Eh in W1. cbn [negb andb] in W1.
  rewrite Ai in Rw. rewrite Rw. unfold wrote, bvx, rdo. rewrite Rv.
  assert (Xi : existsb (Nat.eqb x) (icells (ins p c b (rg (cs s c)))) = true)
    by (apply existsb_exists; exists x; split; [auto|apply Nat.eqb_refl]).
  rewrite Xi.
  destruct (ins p c b (rg (cs s c))) as [m ys cb|m ys cb v|m ys cb ex nv| |] eqn:E;
    unfold executes, icond in Ex; simpl in Ex, W1 |- *.
  - rewrite W1. reflexivity.
  - unfold icond in W1. simpl in W1. rewrite Ex in W1. simpl in W1.
    destruct (W2 W1) as [V _]. rewrite W1, V. unfold wvals. simpl. reflexivity.
  - pose proof (j_ok p s J t e A Eh) as OK. unfold rgof in OK. rewrite Ei, B', C' in OK.
    rewrite (OK eq_refl ltac:(unfold xload, icond; simpl; rewrite Ex; reflexivity)).
    destruct (ew e) eqn:Ew.
    + destruct (W2 eq_refl) as [V2 _]. rewrite V2. unfold wvals. simpl. reflexivity.
    + reflexivity.
  - simpl in Ix. destruct Ix.
  - simpl in Ix. destruct Ix.
Qed.

(* the binder value at a place b whose instruction is an access d: as the
   access d reads it *)
Lemma bvx_eof : forall p c R b x rd d, eof (ins p c b R) R = Some d ->
  bvx p c R b x rd = match d with
    | DSt _ ys v => cval (dd ys) (projs (length (dd ys)) v) x
    | DCas _ ys _ nv => if vok (R b) then cval (dd ys) (projs (length (dd ys)) nv) x else rd
    | _ => rd end.
Proof.
  intros p c R b x rd d E. unfold bvx.
  destruct (ins p c b R) as [m ys cb|m ys cb v|m ys cb e nv|[]|]; simpl in E; try discriminate;
    try (destruct (cb R); [injection E as <-|discriminate]); try (injection E as <-); reflexivity.
Qed.

(* a leader that is a pending access k': the read takes what k' wrote or read *)
Lemma pend_bvx : forall p s c b x k' d R, Inv1 p s -> Inv2 p s -> oc (cs s c) k' <> None ->
  ai (cs s c) k' = inst_of d -> eof (ins p c b R) R = Some d ->
  (is_cas (inst_of d) = true -> R b = rg (cs s c) k') -> In x (icells (inst_of d)) ->
  bvx p c R b x (rv (cs s c) k' x) = rdo s (rw (cs s c) k' x) x.
Proof.
  intros p s c b x k' d R I J Oc Ad E Rb Ix.
  destruct (oc (cs s c) k') as [t|] eqn:Ot; [|congruence].
  rewrite (bvx_eof p c R b x _ d E).
  destruct (i_rw p s I c k' t (or_introl Ot)) as (e & A & Rw). destruct (i_oc p s I c k' t Ot) as (e' & A' & B' & C').
  rewrite A in A'. injection A' as <-. pose proof (oc_eh p s c k' t e I Ot A B' C') as Eh.
  assert (Ei : einstr p s e = inst_of d) by (unfold einstr; rewrite B', C'; exact Ad).
  pose proof (j_rv p s J t e x A) as Rv. rewrite B', C' in Rv.
  destruct (j_ew p s J t e _ A Ei) as [W1 W2]. unfold rgof in W1, W2. rewrite B' in W1, W2.
  rewrite Eh in W1. cbn [negb andb] in W1.
  rewrite Ad in Rw. rewrite Rw. unfold wrote, rdo. rewrite Rv.
  assert (Xi : existsb (Nat.eqb x) (icells (inst_of d)) = true)
    by (apply existsb_exists; exists x; split; [auto|apply Nat.eqb_refl]).
  rewrite Xi.
  destruct d as [m ys|m ys v|m ys ex nv|f]; simpl in W1, Ix |- *.
  - rewrite W1. reflexivity.
  - unfold icond in W1. simpl in W1.
    destruct (W2 W1) as [V _]. rewrite W1, V. unfold wvals. simpl. reflexivity.
  - pose proof (j_ok p s J t e A Eh) as OK. unfold rgof in OK. rewrite Ei, B', C' in OK.
    rewrite (Rb eq_refl), (OK eq_refl ltac:(unfold xload, icond; simpl; reflexivity)).
    destruct (ew e) eqn:Ew.
    + destruct (W2 eq_refl) as [V2 _]. rewrite V2. unfold wvals. simpl. reflexivity.
    + reflexivity.
  - destruct Ix.
Qed.

Lemma enc_zeros : forall xs : list cell, enc (map (fun _ => 0) xs) = 0.
Proof. induction xs as [|x [|y xs] IH]; simpl in *; auto. rewrite IH. reflexivity. Qed.

(* a slot's register is its cells' values packed *)
Lemma rg_rv : forall p s c k t, Inv1 p s -> Inv2 p s -> oc (cs s c) k = Some t ->
  rval (ai (cs s c) k) (rg (cs s c) k) = enc (map (rv (cs s c) k) (icells (ai (cs s c) k))).
Proof.
  intros p s c k t I J O. destruct (i_oc p s I c k t O) as (e & A & B & C).
  assert (Ei : einstr p s e = ai (cs s c) k) by (unfold einstr; rewrite B, C; reflexivity).
  destruct (j_val p s J t e _ A Ei) as [V1 V2]. unfold rgof in V1, V2. rewrite B, C in V1, V2.
  assert (Rv : forall x, rv (cs s c) k x = rdv s (erf e) x) by (intros x; pose proof (j_rv p s J t e x A) as Q; rewrite B, C in Q; exact Q).
  destruct (xload (ai (cs s c) k) (rg (cs s c))) eqn:X.
  - rewrite (V1 eq_refl). f_equal. unfold rdvs. apply map_ext. intros x. symmetry. apply Rv.
  - destruct (V2 eq_refl) as [-> U]. rewrite (map_ext _ (fun _ => 0)); [destruct (ai (cs s c) k); symmetry; apply enc_zeros|].
    intros x. rewrite Rv. unfold rdv. rewrite U. reflexivity.
Qed.

(* ---------- a register read back cell by cell ---------- *)
Lemma cval_map : forall xs (v : cell -> val) x, NoDup xs -> In x xs -> cval xs (map v xs) x = v x.
Proof.
  induction xs as [|a xs IH]; intros v x N I; [destruct I|]. simpl.
  destruct (Nat.eqb_spec x a) as [->|Ne]; [reflexivity|]. inversion N; subst.
  apply IH; auto. destruct I as [->|I]; [congruence|auto].
Qed.

Lemma map_cval : forall xs vs, NoDup xs -> length vs = length xs -> map (cval xs vs) xs = vs.
Proof.
  induction xs as [|a xs IH]; intros vs N L; destruct vs as [|v vs]; simpl in *; try lia; auto.
  rewrite Nat.eqb_refl. f_equal. inversion N; subst.
  rewrite (map_ext_in _ (cval xs vs)); [apply IH; auto|].
  intros y Hy. destruct (Nat.eqb_spec y a) as [->|]; [contradiction|reflexivity].
Qed.

Lemma icells_nodup : forall i, NoDup (icells i).
Proof. intros [m xs c|m xs c v|m xs c e n| |]; simpl; try constructor; apply NoDup_nodup. Qed.

(* the value of cell x a register of a read at j holds *)
Definition dec (p : prog) (c : nat) (r : regs) (j : nat) (x : cell) : val :=
  cval (icells (ins p c j r)) (projs (length (icells (ins p c j r))) (rval (ins p c j r) (r j))) x.

Lemma enc_dec : forall p c r j, icells (ins p c j r) <> [] ->
  enc (map (dec p c r j) (icells (ins p c j r))) = rval (ins p c j r) (r j).
Proof.
  intros p c r j N. unfold dec. rewrite map_cval; [|apply icells_nodup|apply projs_length].
  apply enc_projs. destruct (icells (ins p c j r)); simpl; [congruence|lia].
Qed.

Lemma dec_of : forall p c r j (v : cell -> val) x, icells (ins p c j r) <> [] ->
  rval (ins p c j r) (r j) = enc (map v (icells (ins p c j r))) -> In x (icells (ins p c j r)) -> dec p c r j x = v x.
Proof.
  intros p c r j v x N E I. unfold dec. rewrite E.
  replace (length (icells (ins p c j r))) with (length (map v (icells (ins p c j r)))) by apply length_map.
  rewrite projs_enc; [apply cval_map; auto; apply icells_nodup|].
  intros Z. apply map_eq_nil in Z. contradiction.
Qed.

Lemma dec_agree : forall p c r r' j x, wf p -> agree r r' (S j) -> dec p c r j x = dec p c r' j x.
Proof.
  intros p c r r' j x W A. unfold dec. rewrite (proj1 (ins_agree p W c j r r' (agree_le r r' (S j) j A ltac:(lia)))).
  rewrite (A j ltac:(lia)). reflexivity.
Qed.

(* ---------- Part 3: every pending access finds its place, whatever the
   free values and whatever further reads are counted on ---------- *)

Lemma creg_lt_pc : forall p c cc pc N B f i, wf p -> pend_ok cc pc -> i < pc ->
  creg p c cc pc N B f i = rg cc i.
Proof.
  intros p c cc pc N B f i W PO L. rewrite (creg_fix p W c cc pc N B f i PO). unfold slotv.
  rewrite (proj2 (Nat.ltb_lt i pc) L). reflexivity.
Qed.

(* the values R1 takes, read back as free values *)
Definition fof (p : prog) (c : nat) (cc : cst) (pc N : nat) (B : nat -> bool) (f : nat -> cell -> val) (r : regs)
  : nat -> cell -> val := fun j x =>
  if Nat.eqb x (bitc (ins p c j r))
  then (if Nat.ltb j pc then Nat.b2n (vok (r j))
        else match pend_at p c cc pc N r j with Some k => Nat.b2n (vok (rg cc k)) | None => f j x end)
  else cellv p c cc pc N B f r j j x.

(* the free values of slots J and beyond do not reach the registers below J *)
Lemma cellv_fagree : forall p c cc pc N B f g r J, (forall j x, j < J -> f j x = g j x) ->
  forall n j x, j < J -> cellv p c cc pc N B f r n j x = cellv p c cc pc N B g r n j x.
Proof.
  intros p c cc pc N B f g r J H n. induction n as [|n IH]; intros j x L; simpl;
    (destruct (Nat.ltb j pc); [reflexivity|]); (destruct (_ && _); [|reflexivity]);
    (destruct (pend_at _ _ _ _ _ _ _); [reflexivity|]); (destruct (hpend_at _ _ _ _ _ _ _); [reflexivity|]).
  - apply H. exact L.
  - destruct (B j); [|apply H; exact L]. destruct (fbinder p c r j x) as [b|] eqn:Fb; [|apply H; exact L].
    pose proof (fbinder_lt _ _ _ _ _ _ Fb). rewrite IH by lia. reflexivity.
Qed.

Lemma creg_fagree : forall p c cc pc N B f g J, wf p -> pend_ok cc pc -> (forall j x, j < J -> f j x = g j x) ->
  forall j, j < J -> creg p c cc pc N B f j = creg p c cc pc N B g j.
Proof.
  intros p c cc pc N B f g J W PO H j. induction j as [j IH] using lt_wf_ind. intros L.
  rewrite (creg_fix p W c cc pc N B f j PO), (creg_fix p W c cc pc N B g j PO).
  rewrite (slotv_agree p W c cc pc N B f _ (creg p c cc pc N B g) j PO) by (intros i Li; apply IH; lia).
  unfold slotv. destruct (Nat.ltb j pc); [reflexivity|]. destruct (_ && _); [|reflexivity].
  destruct (pend_at _ _ _ _ _ _ _); [reflexivity|].
  unfold fbit. rewrite (H j _ L). destruct (hpend_at _ _ _ _ _ _ _); [reflexivity|].
  cbv zeta. erewrite map_ext; [reflexivity|]. intros x. apply (cellv_fagree p c cc pc N B f g _ J H j j x L).
Qed.

(* free values that differ only in the verdict bit of a slot whose register is fixed *)
Lemma cellv_fone : forall p c cc pc N B f g r j0, (forall j x, j <> j0 \/ x <> bitc (ins p c j0 r) -> f j x = g j x) ->
  forall n j x, x <> bitc (ins p c j r) -> cellv p c cc pc N B f r n j x = cellv p c cc pc N B g r n j x.
Proof.
  intros p c cc pc N B f g r j0 H n. induction n as [|n IH]; intros j x Hx; simpl;
    (destruct (Nat.ltb j pc); [reflexivity|]); (destruct (_ && _); [|reflexivity]);
    (destruct (pend_at _ _ _ _ _ _ _); [reflexivity|]); (destruct (hpend_at _ _ _ _ _ _ _); [reflexivity|]);
    try (apply H; destruct (Nat.eq_dec j j0) as [->|Nj]; [right; exact Hx|left; exact Nj]).
  destruct (B j); [|apply H; destruct (Nat.eq_dec j j0) as [->|Nj]; [right; exact Hx|left; exact Nj]].
  destruct (fbinder p c r j x) as [b|] eqn:Fb; [|apply H; destruct (Nat.eq_dec j j0) as [->|Nj]; [right; exact Hx|left; exact Nj]].
  rewrite IH; [reflexivity|]. apply bitc_notin. apply (fbinder_shape _ _ _ _ _ _ Fb).
Qed.

Lemma creg_fone : forall p c cc pc N B f g j0, wf p -> pend_ok cc pc ->
  (forall j x, j <> j0 \/ x <> bitc (ins p c j0 (creg p c cc pc N B f)) -> f j x = g j x) ->
  pend_at p c cc pc N (creg p c cc pc N B f) j0 <> None ->
  forall j, creg p c cc pc N B g j = creg p c cc pc N B f j.
Proof.
  intros p c cc pc N B f g j0 W PO H Pj. apply (creg_ext p W); [exact PO|]. intros j.
  rewrite (creg_fix p W c cc pc N B f j PO). unfold slotv.
  destruct (Nat.ltb j pc); [reflexivity|]. destruct (_ && _); [|reflexivity].
  destruct (pend_at _ _ _ _ _ _ j) eqn:Pe; [reflexivity|].
  assert (Nj : j <> j0) by (intros ->; congruence).
  assert (FB : fbit g (ins p c j (creg p c cc pc N B f)) j = fbit f (ins p c j (creg p c cc pc N B f)) j)
    by (unfold fbit; rewrite (H j _ (or_introl Nj)); reflexivity).
  rewrite FB. destruct (hpend_at _ _ _ _ _ _ _); [reflexivity|].
  cbv zeta. erewrite map_ext_in; [reflexivity|]. intros x Ix. symmetry. apply (cellv_fone p c cc pc N B f g _ j0 H).
  apply bitc_notin. exact Ix.
Qed.

Lemma fof_bit : forall p c cc pc N B f r j, pc <= j -> pend_at p c cc pc N r j = None ->
  fbit (fof p c cc pc N B f r) (ins p c j r) j = fbit f (ins p c j r) j.
Proof.
  intros p c cc pc N B f r j L P. unfold fbit, fof. rewrite Nat.eqb_refl.
  replace (Nat.ltb j pc) with false by (symmetry; apply Nat.ltb_ge; lia). rewrite P. reflexivity.
Qed.

Lemma fbinder_0 : forall p c r x, fbinder p c r 0 x = None.
Proof. intros p c r x. unfold fbinder. destruct (_ && _ && _); reflexivity. Qed.

Lemma cellv_S : forall p c cc pc N B f r n j x, j <= n ->
  cellv p c cc pc N B f r (S n) j x = cellv p c cc pc N B f r n j x.
Proof.
  intros p c cc pc N B f r n. induction n as [|n IH]; intros j x L.
  - assert (j = 0) by lia. subst j. cbn [cellv].
    destruct (Nat.ltb 0 pc); auto. destruct (_ && _); auto. destruct (pend_at _ _ _ _ _ _ _); auto.
    destruct (hpend_at _ _ _ _ _ _ _); auto.
    destruct (B 0); auto. rewrite fbinder_0. reflexivity.
  - cbn [cellv] in *. destruct (Nat.ltb j pc); auto. destruct (_ && _); auto. destruct (pend_at _ _ _ _ _ _ _); auto.
    destruct (hpend_at _ _ _ _ _ _ _); auto.
    destruct (B j); auto. destruct (fbinder p c r j x) as [b|] eqn:Fb; auto.
    pose proof (fbinder_lt p c r j x b Fb). f_equal. apply IH. lia.
Qed.

Lemma cellv_fuel : forall p c cc pc N B f r n j x, j <= n ->
  cellv p c cc pc N B f r n j x = cellv p c cc pc N B f r j j x.
Proof.
  intros p c cc pc N B f r n j x L. induction n as [|n IH].
  - assert (j = 0) by lia. subst. reflexivity.
  - destruct (Nat.eq_dec j (S n)) as [->|N0]; [reflexivity|]. rewrite cellv_S by lia. apply IH. lia.
Qed.

Section CV.
Variables (p : prog) (c : nat) (cc : cst) (pc N : nat) (B : nat -> bool) (f : nat -> cell -> val) (r : regs).

Lemma cellv_lt : forall n j x, j < pc -> cellv p c cc pc N B f r n j x = rv cc j x.
Proof. intros n j x L. destruct n; cbn [cellv]; rewrite (proj2 (Nat.ltb_lt j pc) L); reflexivity. Qed.

Lemma cellv_nl : forall n j x, pc <= j -> is_load (ins p c j r) && icond (ins p c j r) r = false ->
  cellv p c cc pc N B f r n j x = 0.
Proof. intros n j x L X. destruct n; cbn [cellv]; rewrite (proj2 (Nat.ltb_ge j pc) L), X; reflexivity. Qed.

Lemma cellv_pd : forall n j x k, pc <= j -> is_load (ins p c j r) && icond (ins p c j r) r = true ->
  pend_at p c cc pc N r j = Some k -> cellv p c cc pc N B f r n j x = rv cc k x.
Proof. intros n j x k L X P. destruct n; cbn [cellv]; rewrite (proj2 (Nat.ltb_ge j pc) L), X, P; reflexivity. Qed.

Lemma cellv_hpd : forall n j x k, pc <= j -> is_load (ins p c j r) && icond (ins p c j r) r = true ->
  pend_at p c cc pc N r j = None -> hpend_at p c cc pc N r j = Some k -> cellv p c cc pc N B f r n j x = rv cc k x.
Proof. intros n j x k L X P H. destruct n; cbn [cellv]; rewrite (proj2 (Nat.ltb_ge j pc) L), X, P, H; reflexivity. Qed.

(* the value when nothing is pending there: bound, or free *)
Lemma cellv_go : forall n j x, pc <= j -> is_load (ins p c j r) && icond (ins p c j r) r = true ->
  pend_at p c cc pc N r j = None -> hpend_at p c cc pc N r j = None ->
  cellv p c cc pc N B f r (S n) j x =
    if B j then match fbinder p c r j x with
                | Some b => bvx p c r b x (cellv p c cc pc N B f r n b x) | None => f j x end
    else f j x.
Proof. intros n j x L X P H. cbn [cellv]. rewrite (proj2 (Nat.ltb_ge j pc) L), X, P, H. reflexivity. Qed.

Lemma cellv_free : forall j x, pc <= j -> is_load (ins p c j r) && icond (ins p c j r) r = true ->
  pend_at p c cc pc N r j = None -> hpend_at p c cc pc N r j = None -> cellv p c cc pc N B f r 0 j x = f j x.
Proof. intros j x L X P H. cbn [cellv]. rewrite (proj2 (Nat.ltb_ge j pc) L), X, P, H. reflexivity. Qed.

(* a read with no binder counted on in cell x takes its free value there *)
Lemma cellv_unb : forall n j x, pc <= j -> is_load (ins p c j r) && icond (ins p c j r) r = true ->
  pend_at p c cc pc N r j = None -> hpend_at p c cc pc N r j = None -> (B j = true -> fbinder p c r j x = None) ->
  cellv p c cc pc N B f r n j x = f j x.
Proof.
  intros [|n] j x L X P Hh H; [apply cellv_free; auto|]. rewrite cellv_go by auto.
  destruct (B j) eqn:Bj; [rewrite H; auto|reflexivity].
Qed.

End CV.

Lemma cellv_fof : forall p c cc pc N B f r n j x, x <> bitc (ins p c j r) ->
  cellv p c cc pc N B (fof p c cc pc N B f r) r n j x = cellv p c cc pc N B f r j j x.
Proof.
  intros p c cc pc N B f r n. induction n as [|n IH]; intros j x Hx.
  all: destruct (Nat.ltb_spec j pc) as [L|L]; [rewrite !cellv_lt by auto; reflexivity|].
  all: destruct (is_load (ins p c j r) && icond (ins p c j r) r) eqn:X; [|rewrite !cellv_nl by auto; reflexivity].
  all: destruct (pend_at p c cc pc N r j) as [k|] eqn:P; [rewrite !(cellv_pd _ _ _ _ _ _ _ _ _ _ _ k) by auto; reflexivity|].
  all: destruct (hpend_at p c cc pc N r j) as [k|] eqn:Hp; [rewrite !(cellv_hpd _ _ _ _ _ _ _ _ _ _ _ k) by auto; reflexivity|].
  - rewrite cellv_free by auto. unfold fof. rewrite (proj2 (Nat.eqb_neq _ _) Hx). reflexivity.
  - rewrite cellv_go by auto. destruct j as [|j].
    + unfold fof. rewrite (proj2 (Nat.eqb_neq _ _) Hx). destruct (B 0); [rewrite fbinder_0|]; reflexivity.
    + destruct (B (S j)) eqn:Bj; [|unfold fof; rewrite (proj2 (Nat.eqb_neq _ _) Hx); reflexivity].
      destruct (fbinder p c r (S j) x) as [b|] eqn:Fb; [|unfold fof; rewrite (proj2 (Nat.eqb_neq _ _) Hx); reflexivity].
      rewrite (cellv_go _ _ _ _ _ _ f _ j) by auto. rewrite Bj, Fb.
      pose proof (fbinder_lt p c r (S j) x b Fb). f_equal. rewrite IH; [symmetry; apply cellv_fuel; lia|].
      apply bitc_notin. apply (fbinder_shape _ _ _ _ _ _ Fb).
Qed.


(* fewer reads counted on, with the values counted on as free values *)
Lemma cellv_sub : forall p c cc pc N Bs Bb f r, (forall j, Bs j = true -> Bb j = true) -> forall n j x,
  x <> bitc (ins p c j r) ->
  cellv p c cc pc N Bs (fof p c cc pc N Bb f r) r n j x = cellv p c cc pc N Bb f r j j x.
Proof.
  intros p c cc pc N Bs Bb f r Sub n. induction n as [|n IH]; intros j x Hx.
  all: destruct (Nat.ltb_spec j pc) as [L|L]; [rewrite !cellv_lt by auto; reflexivity|].
  all: destruct (is_load (ins p c j r) && icond (ins p c j r) r) eqn:X; [|rewrite !cellv_nl by auto; reflexivity].
  all: destruct (pend_at p c cc pc N r j) as [k|] eqn:P; [rewrite !(cellv_pd _ _ _ _ _ _ _ _ _ _ _ k) by auto; reflexivity|].
  all: destruct (hpend_at p c cc pc N r j) as [k|] eqn:Ph; [rewrite !(cellv_hpd _ _ _ _ _ _ _ _ _ _ _ k) by auto; reflexivity|].
  - rewrite cellv_free by auto. unfold fof. rewrite (proj2 (Nat.eqb_neq _ _) Hx). reflexivity.
  - rewrite cellv_go by auto. destruct (Bs j) eqn:Bj; [|unfold fof; rewrite (proj2 (Nat.eqb_neq _ _) Hx); reflexivity].
    destruct (fbinder p c r j x) as [b|] eqn:Fb; [|unfold fof; rewrite (proj2 (Nat.eqb_neq _ _) Hx); reflexivity].
    destruct j as [|j]; [rewrite fbinder_0 in Fb; discriminate|].
    rewrite (cellv_go _ _ _ _ _ _ f _ j) by auto. rewrite (Sub _ Bj), Fb.
    pose proof (fbinder_lt p c r (S j) x b Fb). f_equal. rewrite IH; [symmetry; apply cellv_fuel; lia|].
    apply bitc_notin. apply (fbinder_shape _ _ _ _ _ _ Fb).
Qed.

Lemma creg_sub : forall p c cc pc N Bs Bb f, wf p -> pend_ok cc pc -> (forall j, Bs j = true -> Bb j = true) ->
  forall j, creg p c cc pc N Bs (fof p c cc pc N Bb f (creg p c cc pc N Bb f)) j = creg p c cc pc N Bb f j.
Proof.
  intros p c cc pc N Bs Bb f W PO Sub. apply (creg_ext p W); auto. intros j.
  rewrite (creg_fix p W c cc pc N Bb f j PO). unfold slotv.
  destruct (Nat.ltb_spec j pc) as [Lj|Lj]; auto. destruct (_ && _); auto.
  destruct (pend_at _ _ _ _ _ _ _) eqn:Pj; auto. rewrite fof_bit by first [lia|assumption|(rewrite pend_new_r; assumption)|(rewrite pend_new_old by auto; assumption)].
  destruct (hpend_at _ _ _ _ _ _ _); [reflexivity|].
  cbv zeta. erewrite map_ext_in; [reflexivity|]. intros x Ix. apply cellv_sub; auto. apply bitc_notin. exact Ix.
Qed.

(* the reads counted on matter only through which they are *)
Lemma cellv_Bext : forall p c cc pc N B B' f r, (forall j, B j = B' j) -> forall n j x,
  cellv p c cc pc N B f r n j x = cellv p c cc pc N B' f r n j x.
Proof.
  intros p c cc pc N B B' f r E n. induction n as [|n IH]; intros j x; cbn [cellv]; [reflexivity|].
  rewrite (E j). destruct (Nat.ltb j pc); auto. destruct (_ && _); auto.
  destruct (pend_at _ _ _ _ _ _ _); auto. destruct (hpend_at _ _ _ _ _ _ _); auto.
  try (destruct (B' j); auto; destruct (fbinder p c r j x); auto; rewrite IH; reflexivity).
Qed.

Lemma creg_Bext : forall p c cc pc N B B' f, wf p -> pend_ok cc pc -> (forall j, B j = B' j) ->
  forall j, creg p c cc pc N B f j = creg p c cc pc N B' f j.
Proof.
  intros p c cc pc N B B' f W PO E. apply (creg_ext p W); auto. intros j.
  rewrite (creg_fix p W c cc pc N B' f j PO). unfold slotv.
  destruct (Nat.ltb j pc); auto. destruct (_ && _); auto.
  destruct (pend_at _ _ _ _ _ _ _); auto. destruct (hpend_at _ _ _ _ _ _ _); auto.
  cbv zeta. erewrite map_ext; [reflexivity|]. intros x. apply cellv_Bext; auto.
Qed.

(* every pending access has its place, whatever the free values and whatever
   further reads are counted on *)
Definition INVP (p : prog) (s : st) : Prop :=
  forall c k d B f, pending (cs s c) (pcs s c) k d ->
    exists j, placed p c (cs s c) (pcs s c) (creg p c (cs s c) (pcs s c) (tp s c) (bor (bd (cs s c)) B) f) k d j.

Lemma pend_ok_of : forall p s c, Inv1 p s -> pend_ok (cs s c) (pcs s c).
Proof. intros p s c I k O L. apply (proj1 (i_pend p s I c k L O)). Qed.

Lemma pc_le_tp : forall p s c, Inv1 p s -> pcs s c <= tp s c.
Proof. intros p s c I. apply (i_pctp p s I). Qed.

Lemma bn_of : forall p s c, Inv1 p s -> forall k, oc (cs s c) k <> None -> pcs s c <= k -> k < tp s c.
Proof.
  intros p s c I k O _. destruct (Nat.lt_ge_cases k (tp s c)) as [L|L]; auto. exfalso. apply O. apply (i_tp p s I). auto.
Qed.

Lemma bnh_of : forall p s c, Inv1 p s -> forall k, oh (cs s c) k <> None -> pcs s c <= k -> k < tp s c.
Proof.
  intros p s c I k O _. destruct (Nat.lt_ge_cases k (tp s c)) as [L|L]; auto. exfalso. apply O. apply (i_tp p s I). auto.
Qed.

(* one time, one read alone *)
Lemma oh_inj : forall p s c, Inv1 p s -> forall k1 k2 t, oh (cs s c) k1 = Some t -> oh (cs s c) k2 = Some t -> k1 = k2.
Proof.
  intros p s c I k1 k2 t O1 O2. destruct (i_oh p s I c k1 t O1) as (e1 & E1 & _ & K1 & _).
  destruct (i_oh p s I c k2 t O2) as (e2 & E2 & _ & K2 & _). rewrite E1 in E2. injection E2 as <-. congruence.
Qed.

(* one time, one slot *)
Lemma oc_inj : forall p s c, Inv1 p s -> forall k1 k2 t, oc (cs s c) k1 = Some t -> oc (cs s c) k2 = Some t -> k1 = k2.
Proof.
  intros p s c I k1 k2 t O1 O2. destruct (i_oc p s I c k1 t O1) as (e1 & E1 & _ & K1).
  destruct (i_oc p s I c k2 t O2) as (e2 & E2 & _ & K2). rewrite E1 in E2. injection E2 as <-. congruence.
Qed.

Lemma seq_cons_pc : forall a n, a < n -> seq a (n - a) = a :: seq (S a) (n - S a).
Proof. intros a n L. destruct (n - a) as [|m] eqn:E; [lia|]. simpl. f_equal. f_equal. lia. Qed.

Lemma allin_cons : forall f a n, allin f a (S n) = f a && allin f (S a) n.
Proof. reflexivity. Qed.

Lemma find_unique : forall (P : nat -> bool) l n, In n l -> P n = true ->
  (forall m, In m l -> P m = true -> m = n) -> find P l = Some n.
Proof.
  intros P l n. induction l as [|a l IH]; intros H Pn U; [destruct H|]. simpl.
  destruct (P a) eqn:Pa.
  - f_equal. apply U; [left; auto|auto].
  - destruct H as [->|H]; [congruence|]. apply IH; auto. intros m Hm Pm. apply U; [right|]; auto.
Qed.

Lemma tiedb_self : forall d, icells (inst_of d) <> [] -> tiedb (inst_of d) (inst_of d) = true.
Proof. intros d N. apply tied_b. apply tied_self_d. exact N. Qed.

(* ---------- the pending access at a place ---------- *)
Section PendAt.
Variables (p : prog) (c : nat) (cc : cst) (pc N : nat).
Hypothesis PO : pend_ok cc pc.
Hypothesis BN : forall k, oc cc k <> None -> pc <= k -> k < N.
Hypothesis BNh : forall k, oh cc k <> None -> pc <= k -> k < N.
Hypothesis OI : forall k1 k2 t, oc cc k1 = Some t -> oc cc k2 = Some t -> k1 = k2.
Hypothesis OIh : forall k1 k2 t, oh cc k1 = Some t -> oh cc k2 = Some t -> k1 = k2.

(* two pending accesses do not share a place *)
Lemma placed_unique : forall r j k1 k2 d1 d2, placed p c cc pc r k1 d1 j -> placed p c cc pc r k2 d2 j -> k1 = k2.
Proof.
  intros r j k1 k2 d1 d2 (P1 & t1 & O1 & F1) (P2 & t2 & O2 & F2).
  destruct (Nat.lt_trichotomy t1 t2) as [L|[L|L]].
  - exfalso. apply (first_at_free _ _ _ _ _ _ _ _ F2). exists k1, t1, d1. auto.
  - subst. apply (OI k1 k2 t2); auto.
  - exfalso. apply (first_at_free _ _ _ _ _ _ _ _ F1). exists k2, t2, d2. auto.
Qed.

Lemma pend_test : forall r j k, In k (seq pc (N - pc)) ->
  (match oc cc k with
   | Some t => match eof (ai cc k) r with Some d => first_atb p c cc pc N r t d j | None => false end
   | None => false end = true <-> exists d, placed p c cc pc r k d j).
Proof.
  intros r j k Hk. apply in_seq in Hk. split.
  - destruct (oc cc k) as [t|] eqn:O; [|discriminate].
    destruct (PO k ltac:(congruence) ltac:(lia)) as (d & Ad & Nd). rewrite Ad, (eof_inst d _ Nd). intros F.
    apply (first_atb_iff p c cc pc N r t d j PO BN BNh) in F. exists d. split; [repeat split; auto; [lia|congruence]|]. eauto.
  - intros (d & (P1 & P2 & P3) & t & O & F). destruct (PO k P2 P1) as (d0 & A0 & N0). rewrite P3 in A0. apply inst_of_inj in A0. subst d0.
    rewrite O, P3, (eof_inst d _ N0). apply (first_atb_iff p c cc pc N r t d j PO BN BNh). exact F.
Qed.

Lemma pend_at_char : forall r j k, pend_at p c cc pc N r j = Some k <-> exists d, placed p c cc pc r k d j.
Proof.
  intros r j k. unfold pend_at. split.
  - intros H. apply find_some' in H as [Hin Hf]. apply (pend_test r j k Hin). exact Hf.
  - intros (d & Pl). apply find_unique.
    + destruct Pl as ((P1 & P2 & _) & _). apply in_seq. pose proof (BN k P2 P1). lia.
    + apply pend_test; [|eauto]. destruct Pl as ((P1 & P2 & _) & _). apply in_seq. pose proof (BN k P2 P1). lia.
    + intros m Hm Pm. apply (pend_test r j m Hm) in Pm. destruct Pm as (d' & Pm). apply (placed_unique r j m k d' d); auto.
Qed.

Lemma pend_at_none : forall r j, pend_at p c cc pc N r j = None <-> ~ exists k d, placed p c cc pc r k d j.
Proof.
  intros r j. split.
  - intros H (k & d & Pl). assert (X : pend_at p c cc pc N r j = Some k) by (apply pend_at_char; eauto). congruence.
  - intros H. destruct (pend_at p c cc pc N r j) as [k|] eqn:E; auto. exfalso. apply H.
    apply pend_at_char in E. destruct E as (d & E). eauto.
Qed.

(* the place of a CAS whose read happened alone *)
Definition hplaced (r : regs) (k : nat) (m : mode) (xs : list cell) (j : nat) : Prop :=
  hpending cc pc k m xs /\ oc cc k = None /\ exists t, oh cc k = Some t /\ first_atR p c cc pc r t m xs j.

Lemma hplaced_unique : forall r j k1 k2 m1 m2 xs1 xs2, hplaced r k1 m1 xs1 j -> hplaced r k2 m2 xs2 j -> k1 = k2.
Proof.
  intros r j k1 k2 m1 m2 xs1 xs2 (P1 & C1 & t1 & O1 & F1) (P2 & C2 & t2 & O2 & F2).
  destruct (Nat.lt_trichotomy t1 t2) as [L|[L|L]].
  - exfalso. apply (first_atR_hfree _ _ _ _ _ _ _ _ _ F2). exists k1, t1, m1, xs1.
    split; [exact P1|]. split; [exact O1|]. split; [exact L|]. split; [intros t3 E; congruence|exact F1].
  - subst. apply (OIh k1 k2 t2); auto.
  - exfalso. apply (first_atR_hfree _ _ _ _ _ _ _ _ _ F1). exists k2, t2, m2, xs2.
    split; [exact P2|]. split; [exact O2|]. split; [exact L|]. split; [intros t3 E; congruence|exact F2].
Qed.

Lemma hpend_test : forall r j k, In k (seq pc (N - pc)) ->
  (match oc cc k, oh cc k with
   | None, Some t => match casx (ai cc k) with
                     | Some (m, xs) => fab p c cc pc N r (S t) t (TH m xs) j
                     | None => false end
   | _, _ => false end = true <-> exists m xs, hplaced r k m xs j).
Proof.
  intros r j k Hk. apply in_seq in Hk. split.
  - destruct (oc cc k) as [t0|] eqn:O; [discriminate|]. destruct (oh cc k) as [t|] eqn:Oh; [|discriminate].
    destruct (casx (ai cc k)) as [[m xs]|] eqn:Cx; [|discriminate]. intros F.
    apply (fab_plc p c cc pc N r PO BN BNh) in F. exists m, xs. split; [repeat split; auto; [lia|congruence]|]. eauto.
  - intros (m & xs & (P1 & P3 & P4) & P2 & t & O & F). rewrite P2, O, P4.
    apply (fab_plc p c cc pc N r PO BN BNh). exact F.
Qed.

Lemma hpend_at_char : forall r j k, hpend_at p c cc pc N r j = Some k <-> exists m xs, hplaced r k m xs j.
Proof.
  intros r j k. unfold hpend_at. split.
  - intros H. apply find_some' in H as [Hin Hf]. apply (hpend_test r j k Hin). exact Hf.
  - intros (m & xs & Pl). apply find_unique.
    + destruct Pl as ((P1 & P3 & _) & _). apply in_seq. pose proof (BNh k P3 P1). lia.
    + apply hpend_test; [|eauto]. destruct Pl as ((P1 & P3 & _) & _). apply in_seq. pose proof (BNh k P3 P1). lia.
    + intros k' Hm Pm. apply (hpend_test r j k' Hm) in Pm. destruct Pm as (m' & xs' & Pm).
      apply (hplaced_unique r j k' k m' m xs' xs); auto.
Qed.

Lemma hpend_at_none : forall r j, hpend_at p c cc pc N r j = None <-> ~ exists k m xs, hplaced r k m xs j.
Proof.
  intros r j. split.
  - intros H (k & m & xs & Pl). assert (X : hpend_at p c cc pc N r j = Some k) by (apply hpend_at_char; eauto). congruence.
  - intros H. destruct (hpend_at p c cc pc N r j) as [k|] eqn:E; auto. exfalso. apply H.
    apply hpend_at_char in E. destruct E as (m & xs & E). eauto.
Qed.

End PendAt.

Lemma pend_at_char_s : forall p s c, Inv1 p s -> forall r j k,
  pend_at p c (cs s c) (pcs s c) (tp s c) r j = Some k <-> exists d, placed p c (cs s c) (pcs s c) r k d j.
Proof.
  intros p s c I. apply pend_at_char; first [apply (pend_ok_of p s c I)|apply (bn_of p s c I)|apply (bnh_of p s c I)|apply (oc_inj p s c I)|apply (oh_inj p s c I)].
Qed.

Lemma pend_at_none_s : forall p s c, Inv1 p s -> forall r j,
  pend_at p c (cs s c) (pcs s c) (tp s c) r j = None <-> ~ exists k d, placed p c (cs s c) (pcs s c) r k d j.
Proof.
  intros p s c I. apply pend_at_none; first [apply (pend_ok_of p s c I)|apply (bn_of p s c I)|apply (bnh_of p s c I)|apply (oc_inj p s c I)|apply (oh_inj p s c I)].
Qed.

Lemma pend_at_eq_s : forall p s s' c c' r j,
  Inv1 p s -> Inv1 p s' ->
  (forall k, (exists d, placed p c (cs s c) (pcs s c) r k d j) <-> (exists d, placed p c' (cs s' c') (pcs s' c') r k d j)) ->
  c = c' ->
  pend_at p c (cs s c) (pcs s c) (tp s c) r j = pend_at p c' (cs s' c') (pcs s' c') (tp s' c') r j.
Proof.
  intros p s s' c c' r j I I' E <-. destruct (pend_at p c (cs s' c) (pcs s' c) (tp s' c) r j) as [k|] eqn:Pk.
  - apply (pend_at_char_s p s c I). apply E. apply (pend_at_char_s p s' c I'). exact Pk.
  - apply (pend_at_none_s p s c I). intros (k & d & Pl). assert (X : exists d, placed p c (cs s' c) (pcs s' c) r k d j) by (apply E; eauto).
    assert (Y : pend_at p c (cs s' c) (pcs s' c) (tp s' c) r j = Some k) by (apply (pend_at_char_s p s' c I'); exact X). congruence.
Qed.

Lemma hpend_at_char_s : forall p s c, Inv1 p s -> forall r j k,
  hpend_at p c (cs s c) (pcs s c) (tp s c) r j = Some k <-> exists m xs, hplaced p c (cs s c) (pcs s c) r k m xs j.
Proof.
  intros p s c I. apply hpend_at_char;
    first [apply (pend_ok_of p s c I)|apply (bn_of p s c I)|apply (bnh_of p s c I)|apply (oc_inj p s c I)|apply (oh_inj p s c I)].
Qed.

Lemma hpend_at_none_s : forall p s c, Inv1 p s -> forall r j,
  hpend_at p c (cs s c) (pcs s c) (tp s c) r j = None <-> ~ exists k m xs, hplaced p c (cs s c) (pcs s c) r k m xs j.
Proof.
  intros p s c I. apply hpend_at_none;
    first [apply (pend_ok_of p s c I)|apply (bn_of p s c I)|apply (bnh_of p s c I)|apply (oc_inj p s c I)|apply (oh_inj p s c I)].
Qed.

Lemma hpend_at_eq_s : forall p s s' c r j, Inv1 p s -> Inv1 p s' ->
  (forall k, (exists m xs, hplaced p c (cs s c) (pcs s c) r k m xs j) <-> (exists m xs, hplaced p c (cs s' c) (pcs s' c) r k m xs j)) ->
  hpend_at p c (cs s c) (pcs s c) (tp s c) r j = hpend_at p c (cs s' c) (pcs s' c) (tp s' c) r j.
Proof.
  intros p s s' c r j I I' E. destruct (hpend_at p c (cs s' c) (pcs s' c) (tp s' c) r j) as [k|] eqn:Pk.
  - apply (hpend_at_char_s p s c I). apply E. apply (hpend_at_char_s p s' c I'). exact Pk.
  - apply (hpend_at_none_s p s c I). intros (k & m & xs & Pl).
    assert (X : exists m xs, hplaced p c (cs s' c) (pcs s' c) r k m xs j) by (apply E; eauto).
    assert (Y : hpend_at p c (cs s' c) (pcs s' c) (tp s' c) r j = Some k) by (apply (hpend_at_char_s p s' c I'); exact X). congruence.
Qed.

(* every CAS whose read happened alone has its place, whatever the free values
   and whatever further reads are counted on *)
Definition INVH (p : prog) (s : st) : Prop :=
  forall c k m xs B f, hpending (cs s c) (pcs s c) k m xs -> oc (cs s c) k = None ->
    exists j, hplaced p c (cs s c) (pcs s c) (creg p c (cs s c) (pcs s c) (tp s c) (bor (bd (cs s c)) B) f) k m xs j.

(* ---------- moving the next instruction past one slot ---------- *)
(* With the slot pc passed, the places beyond pc stay, when the passed
   slot's own access (if pending) had its place at pc, and an instruction at
   pc tied to an access still pending is the place of one that happened
   before it. *)
Section Shift.
Variables (p : prog) (c : nat) (cc cc' : cst) (pc : nat) (r : regs).
Hypothesis PEQ : forall k d t, (pending cc' (S pc) k d /\ oc cc' k = Some t) <->
  (pending cc pc k d /\ oc cc k = Some t /\ pc < k).
Hypothesis OLD : forall d t j, pending cc pc pc d -> oc cc pc = Some t -> first_at p c cc pc r t d j -> j = pc.
Hypothesis BLK : forall k d t, pending cc' (S pc) k d -> oc cc' k = Some t ->
  executes (ins p c pc r) r = true -> (forall v, htakenv p c cc pc r t pc v -> cfailv (ins p c pc r) r v = false) ->
  tied (ins p c pc r) (inst_of d) -> taken p c cc pc r t pc.

Hypothesis PEQh : forall k m xs t, (hpending cc' (S pc) k m xs /\ oh cc' k = Some t) <->
  (hpending cc pc k m xs /\ oh cc k = Some t /\ pc < k).
Hypothesis HLV : forall k T, pc < k -> (hlive cc' k T <-> hlive cc k T).
Hypothesis OLDh : forall m xs t j, hpending cc pc pc m xs -> oh cc pc = Some t -> first_atR p c cc pc r t m xs j -> j = pc.
Hypothesis BLKh : forall k m xs t, hpending cc' (S pc) k m xs -> oh cc' k = Some t ->
  executes (ins p c pc r) r = true -> (forall v, htakenv p c cc pc r t pc v -> cfailv (ins p c pc r) r v = false) ->
  tied (ins p c pc r) (crd m xs) -> taken p c cc pc r t pc.

Lemma place_shift_g : forall t g j, S pc <= j ->
  (executes (ins p c pc r) r = true -> (forall v, htakenv p c cc pc r t pc v -> cfailv (ins p c pc r) r v = false) ->
   tied (ins p c pc r) (tinst g) -> taken p c cc pc r t pc) ->
  (plc p c cc pc r (S t) t g j <-> plc p c cc' (S pc) r (S t) t g j).
Proof.
  intros t. induction t as [t IH] using lt_wf_ind. intros g j L BL.
  assert (TK : forall j', S pc <= j' -> (taken p c cc pc r t j' <-> taken p c cc' (S pc) r t j')).
  { intros j' Lj. split.
    - intros (k' & t' & d' & P' & O' & Lt & F). destruct (Nat.eq_dec k' pc) as [->|Nk].
      + pose proof (OLD d' t' j' P' O' F). lia.
      + assert (Q : pending cc' (S pc) k' d' /\ oc cc' k' = Some t') by (apply PEQ; split; [exact P'|split; [exact O'|]]; destruct P' as (? & _); lia).
        destruct Q as [Q1 Q2]. exists k', t', d'. split; [exact Q1|]. split; [exact Q2|]. split; [exact Lt|].
        apply (IH t' Lt (TF d') j' Lj); [|exact F]. intros Ex Fx Ti. apply (BLK k' d' t' Q1 Q2 Ex Fx Ti).
    - intros (k' & t' & d' & P' & O' & Lt & F). destruct (proj1 (PEQ k' d' t') (conj P' O')) as (Q1 & Q2 & Q3).
      exists k', t', d'. split; [exact Q1|]. split; [exact Q2|]. split; [exact Lt|].
      apply (IH t' Lt (TF d') j' Lj); [|exact F]. intros Ex Fx Ti. apply (BLK k' d' t' P' O' Ex Fx Ti). }
  assert (THK : forall j', S pc <= j' -> (htaken p c cc pc r t j' <-> htaken p c cc' (S pc) r t j')).
  { intros j' Lj. split.
    - intros (k' & t' & m' & xs' & P' & O' & Lt & Hl & F). destruct (Nat.eq_dec k' pc) as [->|Nk].
      + pose proof (OLDh m' xs' t' j' P' O' F). lia.
      + assert (Lk : pc < k') by (destruct P' as (? & _); lia).
        assert (Q : hpending cc' (S pc) k' m' xs' /\ oh cc' k' = Some t')
          by (apply PEQh; split; [exact P'|split; [exact O'|exact Lk]]).
        destruct Q as [Q1 Q2]. exists k', t', m', xs'. split; [exact Q1|]. split; [exact Q2|]. split; [exact Lt|].
        split; [apply HLV; auto|].
        apply (IH t' Lt (TH m' xs') j' Lj); [|exact F]. intros Ex Fx Ti. apply (BLKh k' m' xs' t' Q1 Q2 Ex Fx Ti).
    - intros (k' & t' & m' & xs' & P' & O' & Lt & Hl & F). destruct (proj1 (PEQh k' m' xs' t') (conj P' O')) as (Q1 & Q2 & Q3).
      exists k', t', m', xs'. split; [exact Q1|]. split; [exact Q2|]. split; [exact Lt|]. split; [apply HLV; auto|].
      apply (IH t' Lt (TH m' xs') j' Lj); [|exact F]. intros Ex Fx Ti. apply (BLKh k' m' xs' t' P' O' Ex Fx Ti). }
  assert (THV : forall j' v, S pc <= j' -> (htakenv p c cc pc r t j' v <-> htakenv p c cc' (S pc) r t j' v)).
  { intros j' v Lj. split.
    - intros (k' & t' & m' & xs' & P' & O' & Lt & Hl & F & Ev). destruct (Nat.eq_dec k' pc) as [->|Nk].
      + pose proof (OLDh m' xs' t' j' P' O' F). lia.
      + assert (Lk : pc < k') by (destruct P' as (? & _); lia).
        assert (Q : hpending cc' (S pc) k' m' xs' /\ oh cc' k' = Some t')
          by (apply PEQh; split; [exact P'|split; [exact O'|exact Lk]]).
        destruct Q as [Q1 Q2]. exists k', t', m', xs'. split; [exact Q1|]. split; [exact Q2|]. split; [exact Lt|].
        split; [apply HLV; auto|]. split; [|exact Ev].
        apply (IH t' Lt (TH m' xs') j' Lj); [|exact F]. intros Ex Fx Ti. apply (BLKh k' m' xs' t' Q1 Q2 Ex Fx Ti).
    - intros (k' & t' & m' & xs' & P' & O' & Lt & Hl & F & Ev). destruct (proj1 (PEQh k' m' xs' t') (conj P' O')) as (Q1 & Q2 & Q3).
      exists k', t', m', xs'. split; [exact Q1|]. split; [exact Q2|]. split; [exact Lt|]. split; [apply HLV; auto|].
      split; [|exact Ev].
      apply (IH t' Lt (TH m' xs') j' Lj); [|exact F]. intros Ex Fx Ti. apply (BLKh k' m' xs' t' P' O' Ex Fx Ti). }
  rewrite !plc_in. split.
  - intros (A & B & C & D). split; [lia|]. split; [exact B|]. split.
    + intros [X|X]; apply C; [left; apply TK|right; apply THK]; auto.
    + intros j' L1 L2 Ex Fx Ti. apply TK; [lia|]. apply D; auto; [lia|].
      intros v X; apply Fx; apply THV; auto; lia.
  - intros (A & B & C & D). split; [lia|]. split; [exact B|]. split.
    + intros [X|X]; apply C; [left; apply TK|right; apply THK]; auto.
    + intros j' L1 L2 Ex Fx Ti. destruct (Nat.eq_dec j' pc) as [->|Nj].
      * apply (BL Ex Fx Ti).
      * apply TK; [lia|]. apply D; auto; [lia|].
        intros v X; apply Fx; apply THV; auto; lia.
Qed.

Lemma place_shift : forall t k d j, pending cc' (S pc) k d -> oc cc' k = Some t -> S pc <= j ->
  (first_at p c cc pc r t d j <-> first_at p c cc' (S pc) r t d j).
Proof. intros t k d j P O L. apply place_shift_g; auto. intros Ex Fx Ti. apply (BLK k d t P O Ex Fx Ti). Qed.

Lemma place_shiftR : forall t k m xs j, hpending cc' (S pc) k m xs -> oh cc' k = Some t -> S pc <= j ->
  (first_atR p c cc pc r t m xs j <-> first_atR p c cc' (S pc) r t m xs j).
Proof. intros t k m xs j P O L. apply place_shift_g; auto. intros Ex Fx Ti. apply (BLKh k m xs t P O Ex Fx Ti). Qed.

End Shift.

(* ---------- the next instruction, in order ---------- *)
Section OrdP.
Variables (p : prog) (s : st) (c : nat) (i : instr) (m' : mst) (a : val) (K : view)
          (u : cell -> option nat) (w : bool).
Hypothesis W : wf p.
Hypothesis Wc : cellful p.
Hypothesis I : Inv1 p s.
Hypothesis J : Inv2 p s.
Hypothesis IP : INVP p s.
Hypothesis IPh : INVH p s.
Local Abbreviation cc := (cs s c).
Local Abbreviation pc := (pcs s c).
Hypothesis Hi : ins p c pc (rg cc) = i.
Hypothesis Ho : oc cc pc = None.
Hypothesis Hb : executes i (rg cc) = true -> forall k' d, pending cc pc k' d -> ~ tied i (inst_of d).
Hypothesis Hbh : executes i (rg cc) = true -> forall k' m xs, hpending cc pc k' m xs -> k' <> pc -> ~ tied i (crd m xs).
(* in order, or the write of a CAS whose read happened alone *)
Hypothesis Hhalf : (oh cc pc = None /\
    forall x b, bd cc pc = true -> In x (icells i) -> fbinder p c (rg cc) pc x = Some b -> u x = rw cc b x) \/
  (exists t1, oh cc pc = Some t1 /\ is_cas i = true /\ u = rw cc pc /\ eofR i (rg cc) = eofR (ai cc pc) (rg cc)).
Hypothesis He : eff (tm s) i (rg cc) (mof s c) m' a K u w.
Hypothesis Hvo : oh cc pc <> None -> vok (rg cc pc) = true.
Hypothesis Hwo : oh cc pc <> None -> w = true.
Hypothesis Hfx : fxok cc pc i (rg cc) a.
Local Abbreviation s' := (sord s c i m' a K u w).
Hypothesis I' : Inv1 p s'.
Local Abbreviation cc' := (cs s' c).
Local Abbreviation N := (tp s c).

Lemma cc'_oc : forall j, oc cc' j = if Nat.eqb j pc then Some (tm s) else oc cc j.
Proof. intros j. unfold sord. rewrite oc_s', Nat.eqb_refl. reflexivity. Qed.
Lemma cc'_rg : forall j, rg cc' j = if Nat.eqb j pc then a else rg cc j.
Proof. intros j. unfold sord. rewrite rg_s', Nat.eqb_refl. reflexivity. Qed.
Lemma cc'_ai : forall j, ai cc' j = if Nat.eqb j pc then i else ai cc j.
Proof. intros j. unfold sord. rewrite ai_s', Nat.eqb_refl. reflexivity. Qed.
Lemma cc'_rv : forall j, rv cc' j = if Nat.eqb j pc then rdval (mof s c) u else rv cc j.
Proof. intros j. unfold sord. rewrite rv_s', Nat.eqb_refl. reflexivity. Qed.
Lemma cc'_bd : bd cc' = bd cc.
Proof. unfold sord, evs; simpl. rewrite upd_eq. reflexivity. Qed.
Lemma cc'_fx : fx cc' = fx cc.
Proof. unfold sord, evs; simpl. rewrite upd_eq. reflexivity. Qed.
Lemma ord_pc : pcs s' c = S pc.
Proof. unfold sord, evs; simpl. apply upd_eq. Qed.

Lemma ord_peq : forall k d t, (pending cc' (S pc) k d /\ oc cc' k = Some t) <->
  (pending cc pc k d /\ oc cc k = Some t /\ pc < k).
Proof.
  intros k d t. unfold pending. rewrite !cc'_oc, cc'_ai. split.
  - intros ((P1 & P2 & P3) & O). destruct (Nat.eqb_spec k pc); [lia|]. repeat split; auto; lia.
  - intros ((P1 & P2 & P3) & O & L). destruct (Nat.eqb_spec k pc); [lia|]. repeat split; auto; lia.
Qed.

Lemma cc'_oh : forall j, oh cc' j = oh cc j.
Proof. intros j. unfold sord. rewrite oh_s'. reflexivity. Qed.

Lemma ord_peqh : forall k m xs t, (hpending cc' (S pc) k m xs /\ oh cc' k = Some t) <->
  (hpending cc pc k m xs /\ oh cc k = Some t /\ pc < k).
Proof.
  intros k m xs t. unfold hpending. rewrite !cc'_oh, cc'_ai. split.
  - intros ((P1 & P2 & P3) & O). destruct (Nat.eqb_spec k pc); [lia|]. repeat split; auto; lia.
  - intros ((P1 & P2 & P3) & O & L). destruct (Nat.eqb_spec k pc); [lia|]. repeat split; auto; lia.
Qed.

Lemma ord_hlv : forall k T, pc < k -> (hlive cc' k T <-> hlive cc k T).
Proof.
  intros k T L. unfold hlive. rewrite cc'_oc. destruct (Nat.eqb_spec k pc); [lia|]. tauto.
Qed.

Lemma eofR_ieval : forall i0 r r', ieval i0 r = ieval i0 r' -> eofR i0 r = eofR i0 r'.
Proof. intros [| |m0 x0 c0 e0 n0| |] r r' H; simpl in *; auto. injection H as H. rewrite H. reflexivity. Qed.

Lemma ord_Ii : forall r, agree r (rg cc) pc -> ins p c pc r = i /\ ieval i r = ieval i (rg cc).
Proof.
  intros r Ag. destruct (ins_agree p W c pc r (rg cc) Ag) as [E1 E2]. rewrite Hi in E1. rewrite E1 in E2. auto.
Qed.

(* the CAS whose read happened alone at pc has its place at pc *)
Lemma ord_firstR_pc : forall r t1 m xs, agree r (rg cc) pc -> oh cc pc = Some t1 -> hpending cc pc pc m xs ->
  first_atR p c cc pc r t1 m xs pc.
Proof.
  intros r t1 m xs Ag Oh (_ & _ & Cx).
  destruct (ord_Ii r Ag) as [Ii' Ie].
  destruct Hhalf as [(Z & _)|(t1' & Oh' & Ci & U & Ef)]; [congruence|]. rewrite Oh in Oh'. injection Oh' as <-.
  destruct (i_half p s I c pc t1 Ho Oh (le_n _)) as (_ & (xs0 & Ax) & _). rewrite Ax in Cx. injection Cx as <- <-.
  assert (ER : eofR (ins p c pc r) r = Some (Plain, xs0)) by (rewrite Ii', (eofR_ieval i r (rg cc) Ie), Ef, Ax; reflexivity).
  assert (Ex : executes i (rg cc) = true).
  { pose proof (exec_agree p W c pc r (rg cc) Ag) as Q. rewrite Ii', Hi in Q. rewrite <- Q.
    destruct (eofR_exec_tied p c pc r Plain xs0 Wc ER) as [E0 _]. rewrite Ii' in E0. exact E0. }
  apply first_atR_mk; [lia|exact ER| | |intros; lia].
  - intros (k' & t' & d' & P' & O' & Lt & F). pose proof (first_at_eof _ _ _ _ _ _ _ _ F) as D.
    destruct (eof_exec_tied p c pc r d' Wc D) as [_ T0]. rewrite Ii' in T0. apply (Hb Ex k' d' P' T0).
  - intros (k' & t' & m0 & xs' & P' & O' & Lt & Hl & F). pose proof (first_atR_eofR _ _ _ _ _ _ _ _ _ F) as D.
    destruct (eofR_exec_tied p c pc r m0 xs' Wc D) as [_ T0]. rewrite Ii' in T0.
    assert (Nk : k' <> pc) by (intros ->; rewrite Oh in O'; injection O' as ->; lia).
    apply (Hbh Ex k' m0 xs' P' Nk T0).
Qed.

Lemma ord_oldh : forall r, agree r (rg cc) pc -> forall m xs t j, hpending cc pc pc m xs -> oh cc pc = Some t ->
  first_atR p c cc pc r t m xs j -> j = pc.
Proof.
  intros r Ag m xs t j P O F. apply (first_atR_unique p c cc pc r t m xs j pc Wc F). apply ord_firstR_pc; auto.
Qed.

(* with the registers before pc as they are, the slot pc blocks nothing *)
Lemma ord_shift : forall r, agree r (rg cc) pc -> forall t k d j, pending cc' (S pc) k d -> oc cc' k = Some t -> S pc <= j ->
  (first_at p c cc pc r t d j <-> first_at p c cc' (S pc) r t d j).
Proof.
  intros r Ag. destruct (ord_Ii r Ag) as [Ii' _].
  assert (EX : executes (ins p c pc r) r = true -> executes i (rg cc) = true)
    by (rewrite (exec_agree p W c pc r (rg cc) Ag), Hi; auto).
  apply place_shift.
  - apply ord_peq.
  - intros d t j (_ & P2 & _) O. congruence.
  - intros k d t P O Ex _ Ti. exfalso. rewrite Ii' in Ti.
    destruct (proj1 (ord_peq k d t) (conj P O)) as (Pk & _). apply (Hb (EX Ex) k d Pk Ti).
  - apply ord_peqh.
  - apply ord_hlv.
  - intros m xs t j P O F. apply (ord_oldh r Ag m xs t j P O F).
  - intros k m xs t P O Ex _ Ti. exfalso. rewrite Ii' in Ti.
    destruct (proj1 (ord_peqh k m xs t) (conj P O)) as (Pk & _ & Lk). apply (Hbh (EX Ex) k m xs Pk ltac:(lia) Ti).
Qed.

Lemma ord_shiftR : forall r, agree r (rg cc) pc -> forall t k m xs j, hpending cc' (S pc) k m xs -> oh cc' k = Some t -> S pc <= j ->
  (first_atR p c cc pc r t m xs j <-> first_atR p c cc' (S pc) r t m xs j).
Proof.
  intros r Ag. destruct (ord_Ii r Ag) as [Ii' _].
  assert (EX : executes (ins p c pc r) r = true -> executes i (rg cc) = true)
    by (rewrite (exec_agree p W c pc r (rg cc) Ag), Hi; auto).
  apply place_shiftR.
  - apply ord_peq.
  - intros d t j (_ & P2 & _) O. congruence.
  - intros k d t P O Ex _ Ti. exfalso. rewrite Ii' in Ti.
    destruct (proj1 (ord_peq k d t) (conj P O)) as (Pk & _). apply (Hb (EX Ex) k d Pk Ti).
  - apply ord_peqh.
  - apply ord_hlv.
  - intros m xs t j P O F. apply (ord_oldh r Ag m xs t j P O F).
  - intros k m xs t P O Ex _ Ti. exfalso. rewrite Ii' in Ti.
    destruct (proj1 (ord_peqh k m xs t) (conj P O)) as (Pk & _ & Lk). apply (Hbh (EX Ex) k m xs Pk ltac:(lia) Ti).
Qed.

Definition Bm (B : nat -> bool) : nat -> bool := fun j => B j && negb (Nat.eqb j pc).

Section OrdR.
Variables (B : nat -> bool) (f : nat -> cell -> val).
Local Abbreviation r := (creg p c cc' (S pc) (tp s' c) (bor (bd cc') B) f).
Local Abbreviation F := (fof p c cc' (S pc) (tp s' c) (bor (bd cc') B) f r).

Lemma PO' : pend_ok cc' (S pc).
Proof. rewrite <- ord_pc; apply (pend_ok_of p s' c I'). Qed.

Lemma Ag : forall q, q <= pc -> agree r (rg cc) q.
Proof.
  intros q Lq i0 Li. transitivity (rg cc' i0).
  - apply creg_lt_pc; auto; [apply PO'|lia].
  - rewrite cc'_rg. destruct (Nat.eqb_spec i0 pc); [lia|auto].
Qed.

Lemma Ii : ins p c pc r = i.
Proof. transitivity (ins p c pc (rg cc)); [apply (proj1 (ins_agree p W c pc r (rg cc) (Ag pc (le_n pc))))|exact Hi]. Qed.

Lemma Xl : xload i (rg cc) = is_load i && icond i r.
Proof.
  unfold xload. f_equal. unfold icond. rewrite <- Ii at 1.
  rewrite <- (proj2 (ins_agree p W c pc r (rg cc) (Ag pc (le_n pc)))), Ii. reflexivity.
Qed.

Lemma pa_pc : is_load i && icond i r = true -> pend_at p c cc pc N r pc = None.
Proof.
  intros X. destruct (pend_at p c cc pc N r pc) as [kk|] eqn:Pa; auto.
  exfalso. apply (pend_at_char_s p s c I) in Pa. destruct Pa as (d' & Pk & t & _ & F0).
  pose proof (first_at_eof _ _ _ _ _ _ _ _ F0) as D2.
  destruct (eof_exec_tied p c pc r d' Wc D2) as [E0 T0]. rewrite Ii in E0, T0.
  assert (E1 : executes i (rg cc) = true).
  { pose proof (exec_agree p W c pc r (rg cc) (Ag pc (le_n pc))) as Q. rewrite Ii, Hi in Q. congruence. }
  apply (Hb E1 kk d' Pk T0).
Qed.

Lemma pa_gt : forall j, S pc <= j -> pend_at p c cc pc N r j = pend_at p c cc' (S pc) (tp s' c) r j.
Proof.
  intros j L. pose proof (pend_at_eq_s p s s' c c r j I I') as QE. rewrite ord_pc in QE. apply QE; [|reflexivity].
  intros k. split.
  - intros (d & Pk & t & O & F0). destruct (Nat.eq_dec k pc) as [->|Nk].
    + exfalso. destruct Pk as (_ & Pk & _). congruence.
    + assert (Q : pending cc' (S pc) k d /\ oc cc' k = Some t) by (apply ord_peq; split; [exact Pk|split; [exact O|]]; destruct Pk as (? & _); lia).
      destruct Q as [Q1 Q2]. exists d. split; auto. exists t. split; auto.
      apply (ord_shift r (Ag pc (le_n pc)) t k d j Q1 Q2 ltac:(lia)). exact F0.
  - intros (d & Pk & t & O & F0). destruct (proj1 (ord_peq k d t) (conj Pk O)) as (Q1 & Q2 & Q3).
    exists d. split; auto. exists t. split; auto. apply (ord_shift r (Ag pc (le_n pc)) t k d j Pk O ltac:(lia)). exact F0.
Qed.

Lemma hpa_gt : forall j, S pc <= j -> hpend_at p c cc pc N r j = hpend_at p c cc' (S pc) (tp s' c) r j.
Proof.
  intros j L. pose proof (hpend_at_eq_s p s s' c r j I I') as QE. rewrite ord_pc in QE. apply QE.
  intros k. split.
  - intros (m & xs & Pk & C & t & O & F0). destruct (Nat.eq_dec k pc) as [->|Nk].
    + exfalso. pose proof (ord_oldh r (Ag pc (le_n pc)) m xs t j Pk O F0). lia.
    + assert (Lk : pc < k) by (destruct Pk as (? & _); lia).
      assert (Q : hpending cc' (S pc) k m xs /\ oh cc' k = Some t) by (apply ord_peqh; auto).
      destruct Q as [Q1 Q2]. exists m, xs. split; [exact Q1|]. split; [rewrite cc'_oc; destruct (Nat.eqb_spec k pc); [lia|exact C]|].
      exists t. split; auto. apply (ord_shiftR r (Ag pc (le_n pc)) t k m xs j Q1 Q2 ltac:(lia)). exact F0.
  - intros (m & xs & Pk & C & t & O & F0). destruct (proj1 (ord_peqh k m xs t) (conj Pk O)) as (Q1 & Q2 & Q3).
    exists m, xs. split; [exact Q1|]. split; [rewrite cc'_oc in C; destruct (Nat.eqb_spec k pc); [lia|exact C]|].
    exists t. split; auto. apply (ord_shiftR r (Ag pc (le_n pc)) t k m xs j Pk O ltac:(lia)). exact F0.
Qed.

Lemma hpa_pc_none : oh cc pc = None -> is_load i && icond i r = true -> hpend_at p c cc pc N r pc = None.
Proof.
  intros Z X. apply (hpend_at_none_s p s c I). intros (k & m & xs & Pk & C & t & O & F0).
  pose proof (first_atR_eofR _ _ _ _ _ _ _ _ _ F0) as D.
  destruct (eofR_exec_tied p c pc r m xs Wc D) as [E0 T0]. rewrite Ii in E0, T0.
  assert (E1 : executes i (rg cc) = true).
  { pose proof (exec_agree p W c pc r (rg cc) (Ag pc (le_n pc))) as Q. rewrite Ii, Hi in Q. congruence. }
  assert (Nk : k <> pc) by (intros ->; congruence).
  apply (Hbh E1 k m xs Pk Nk T0).
Qed.

Lemma hpa_pc_some : forall t1, oh cc pc = Some t1 -> hpend_at p c cc pc N r pc = Some pc.
Proof.
  intros t1 Oh. apply (hpend_at_char_s p s c I).
  destruct (i_half p s I c pc t1 Ho Oh (le_n _)) as (_ & (xs & Ax) & _).
  assert (P : hpending cc pc pc Plain xs) by (split; [lia|split; [congruence|rewrite Ax; reflexivity]]).
  exists Plain, xs. split; [exact P|]. split; [exact Ho|]. exists t1. split; [exact Oh|].
  apply ord_firstR_pc; auto. apply Ag. lia.
Qed.

(* the value the slot pc read in cell x, counted as R1 counted it before the step *)
Lemma bound_pc : (forall x b, bd cc pc = true -> In x (icells i) -> fbinder p c (rg cc) pc x = Some b -> u x = rw cc b x) ->
  forall x b, In x (icells i) -> bd cc pc = true -> fbinder p c r pc x = Some b ->
  bvx p c r b x (rv cc b x) = rdval (mof s c) u x.
Proof.
  intros Hbnd x b Ix Bd Fb.
  rewrite (fbinder_agree p W c r (rg cc) pc x (Ag pc (le_n pc))) in Fb.
  pose proof (fbinder_shape _ _ _ _ _ _ Fb) as (Exb & Ixb & _).
  pose proof (fbinder_lt _ _ _ _ _ _ Fb) as Lb.
  rewrite (bvx_agree p W c r (rg cc) b pc x _ Lb (Ag pc (le_n pc))).
  rewrite (bind_val p s c b x W I J Lb Exb Ixb). rewrite <- (Hbnd x b Bd Ix Fb).
  unfold rdo, rdval. reflexivity.
Qed.

Local Abbreviation Bo := (bor (bd cc) (Bm B)).
Local Abbreviation Bn := (bor (bd cc') B).

Lemma ord_cv_lt : forall n b x, b < pc -> cellv p c cc pc N Bo F r n b x = cellv p c cc' (S pc) (tp s' c) Bn f r b b x.
Proof.
  intros n b x L. rewrite cellv_lt by auto. rewrite cellv_lt by lia. rewrite cc'_rv.
  destruct (Nat.eqb_spec b pc); [lia|reflexivity].
Qed.

Lemma ord_cv_pc : forall n x, x <> bitc (ins p c pc r) ->
  cellv p c cc pc N Bo F r n pc x = cellv p c cc' (S pc) (tp s' c) Bn f r pc pc x.
Proof.
  intros n x Hx. rewrite (cellv_lt _ _ cc' (S pc)) by lia. rewrite cc'_rv, Nat.eqb_refl.
  destruct Hhalf as [(Hoh & Hbnd)|(t1 & Oh & Ci & U & Ef)].
  2:{ destruct (i_half p s I c pc t1 Ho Oh (le_n _)) as (_ & (xs & Ax) & _). rewrite Ax in Ef.
      destruct (eofR_half i (rg cc) xs Ef) as (_ & Xi).
      assert (X : is_load (ins p c pc r) && icond (ins p c pc r) r = true) by (rewrite Ii, <- Xl; exact Xi).
      assert (P0 : pend_at p c cc pc N r pc = None) by (apply pa_pc; rewrite Ii in X; exact X).
      rewrite (cellv_hpd _ _ _ _ _ _ _ _ _ _ _ pc) by (auto; apply (hpa_pc_some t1 Oh)).
      rewrite U. apply (proj1 (half_vals p s c pc t1 I J Ho Oh)). }
  destruct (is_load (ins p c pc r) && icond (ins p c pc r) r) eqn:X.
  2:{ rewrite cellv_nl by auto. rewrite Ii in X.
      destruct (eff_noread _ _ _ _ _ _ _ _ _ He (eq_trans Xl X)) as [_ U]. unfold rdval. rewrite U. reflexivity. }
  assert (P0 : pend_at p c cc pc N r pc = None) by (apply pa_pc; rewrite Ii in X; exact X).
  assert (H0 : hpend_at p c cc pc N r pc = None) by (apply hpa_pc_none; auto; rewrite Ii in X; exact X).
  destruct n as [|n].
  - rewrite cellv_free by auto. unfold fof; rewrite (proj2 (Nat.eqb_neq _ _) Hx). rewrite cellv_lt by lia. rewrite cc'_rv, Nat.eqb_refl. reflexivity.
  - rewrite cellv_go by auto. unfold bor at 1, Bm. rewrite Nat.eqb_refl, andb_false_r, orb_false_r.
    destruct (Bool.bool_dec (bd cc pc) true) as [Bd|Bd]; [rewrite Bd|].
    2:{ apply not_true_is_false in Bd. rewrite Bd. unfold fof; rewrite (proj2 (Nat.eqb_neq _ _) Hx). rewrite cellv_lt by lia. rewrite cc'_rv, Nat.eqb_refl. reflexivity. }
    destruct (fbinder p c r pc x) as [b|] eqn:Fb.
    2:{ unfold fof; rewrite (proj2 (Nat.eqb_neq _ _) Hx). rewrite cellv_lt by lia. rewrite cc'_rv, Nat.eqb_refl. reflexivity. }
    pose proof (fbinder_lt _ _ _ _ _ _ Fb) as Lb.
    pose proof (fbinder_shape _ _ _ _ _ _ Fb) as (_ & _ & _ & _ & _ & Ix). rewrite Ii in Ix.
    rewrite ord_cv_lt by auto. rewrite cellv_lt by lia. rewrite cc'_rv.
    destruct (Nat.eqb_spec b pc); [lia|]. apply bound_pc; auto.
Qed.

Lemma ord_cv : forall n b x, x <> bitc (ins p c b r) ->
  cellv p c cc pc N Bo F r n b x = cellv p c cc' (S pc) (tp s' c) Bn f r b b x.
Proof.
  intros n. induction n as [|n IH]; intros b x Hx.
  all: destruct (Nat.lt_trichotomy b pc) as [L|[L|L]]; [apply ord_cv_lt; auto|subst b; apply ord_cv_pc; exact Hx|].
  all: destruct (is_load (ins p c b r) && icond (ins p c b r) r) eqn:X;
         [|rewrite cellv_nl by (auto; lia); rewrite cellv_nl by (auto; lia); reflexivity].
  all: destruct (pend_at p c cc' (S pc) (tp s' c) r b) as [n0|] eqn:P.
  all: try (rewrite (cellv_pd _ _ cc pc N _ _ _ _ _ _ n0) by (auto; try lia; rewrite pa_gt by lia; exact P);
            rewrite (cellv_pd _ _ cc' (S pc)) with (k := n0) by (auto; lia); rewrite cc'_rv;
            destruct (pend_at_spec _ _ _ _ _ _ _ _ P) as (_ & Ln & _);
            destruct (Nat.eqb_spec n0 pc); [lia|reflexivity]).
  all: destruct (hpend_at p c cc' (S pc) (tp s' c) r b) as [n0|] eqn:Ph.
  all: try (assert (Ln : S pc <= n0) by (rewrite <- ord_pc in Ph; apply (hpend_at_char_s p s' c I') in Ph; rewrite ord_pc in Ph;
                                         destruct Ph as (? & ? & (? & _) & _); auto);
            rewrite (cellv_hpd _ _ cc pc N _ _ _ _ _ _ n0) by first [lia|assumption|(rewrite pa_gt by lia; exact P)|(rewrite hpa_gt by lia; exact Ph)];
            rewrite (cellv_hpd _ _ cc' (S pc)) with (k := n0) by (auto; lia); rewrite cc'_rv;
            destruct (Nat.eqb_spec n0 pc); [lia|reflexivity]).
  - rewrite cellv_free by first [lia|assumption|(rewrite pa_gt by lia; exact P)|(rewrite hpa_gt by lia; exact Ph)]. unfold fof; rewrite (proj2 (Nat.eqb_neq _ _) Hx). reflexivity.
  - rewrite cellv_go by first [lia|assumption|(rewrite pa_gt by lia; exact P)|(rewrite hpa_gt by lia; exact Ph)].
    assert (BB : Bo b = Bn b).
    { unfold bor, Bm. rewrite cc'_bd. replace (negb (Nat.eqb b pc)) with true
        by (destruct (Nat.eqb_spec b pc); [lia|reflexivity]). rewrite andb_true_r. reflexivity. }
    rewrite BB. destruct (Bn b) eqn:Bb; [|unfold fof; rewrite (proj2 (Nat.eqb_neq _ _) Hx); reflexivity].
    destruct (fbinder p c r b x) as [b0|] eqn:Fb; [|unfold fof; rewrite (proj2 (Nat.eqb_neq _ _) Hx); reflexivity].
    destruct b as [|b']; [lia|].
    rewrite (cellv_go _ _ cc' (S pc) _ Bn f r b') by (auto; lia). rewrite Bb, Fb.
    pose proof (fbinder_lt _ _ _ _ _ _ Fb). f_equal. rewrite IH; [symmetry; apply cellv_fuel; lia|].
    apply bitc_notin. apply (fbinder_shape _ _ _ _ _ _ Fb).
Qed.


(* a result fixed at pc is the result of the step *)
Lemma ord_cfx : forall X, is_load i && icond i r = true -> X = a -> cfx cc pc i r X = a.
Proof.
  intros X L ->. destruct (ins_agree p W c pc r (rg cc) (Ag pc (le_n _))) as (_ & E2). rewrite Ii in E2.
  rewrite (cfx_ext cc pc i r (rg cc) a (cexp_ieval _ _ _ E2)). apply cfx_ok; [exact Hfx|].
  apply andb_prop in L as [_ L]. unfold icond in *. rewrite <- E2. exact L.
Qed.

(* the registers after the step are registers the context could have taken
   before it *)
Lemma ord_pt : forall j, slotv p c cc pc N Bo F r j = r j.
Proof.
  intros j.
  assert (Rfix : r j = slotv p c cc' (S pc) (tp s' c) Bn f r j) by (apply creg_fix; auto; apply PO').
  rewrite Rfix. unfold slotv.
  destruct (Nat.lt_trichotomy j pc) as [L|[L|L]].
  - rewrite (proj2 (Nat.ltb_lt j pc) L), (proj2 (Nat.ltb_lt j (S pc))) by lia. rewrite cc'_rg.
    destruct (Nat.eqb_spec j pc); [lia|reflexivity].
  - subst j. rewrite Nat.ltb_irrefl, (proj2 (Nat.ltb_lt pc (S pc))) by lia. rewrite cc'_rg, Nat.eqb_refl, Ii.
    destruct (is_load i && icond i r) eqn:X0; [rewrite pa_pc by exact X0; apply ord_cfx; [exact X0|]|].
    2:{ destruct (eff_noread _ _ _ _ _ _ _ _ _ He (eq_trans Xl X0)) as [A0 _]. symmetry. exact A0. }
    destruct Hhalf as [(Hoh & Hbnd)|(t1 & Oh & Ci & U & Ef)].
    2:{ destruct (i_half p s I c pc t1 Ho Oh (le_n _)) as (_ & (xs & Ax) & _). rewrite Ax in Ef.
        destruct (eofR_half i (rg cc) xs Ef) as (Ic & Xi). rewrite Xl in Xi.
        rewrite (hpa_pc_some t1 Oh).
        assert (Vo : vok (rg cc pc) = true) by (apply Hvo; congruence).
        assert (Wt : w = true) by (apply Hwo; congruence). pose proof He as He'. rewrite Wt in He'.
        destruct (ins_agree p W c pc r (rg cc) (Ag pc (le_n _))) as (_ & E2). rewrite Ii in E2.
        pose proof (eff_cas_ok_e _ _ _ _ _ _ _ _ Ci He') as Ae.
        destruct (eff_read _ _ _ _ _ _ _ _ _ He' (eq_trans Xl Xi)) as (_ & Ea).
        pose proof (proj2 (half_vals p s c pc t1 I J Ho Oh)) as HV. rewrite Ax, <- Ic, <- U in HV.
        rewrite (areg_cas _ _ _ Ci) in Ea. rewrite Ea in Ae. apply vd_inj in Ae as (_ & Ae).
        assert (CF : cfailv i r (rg cc pc) = false).
        { apply (cfailv_ok i r (rg cc) _ Ci E2 Vo). rewrite HV, Ae. unfold eval_e. reflexivity. }
        assert (Rp : r pc = a) by (rewrite (creg_lt_pc p c cc' (S pc) (tp s' c) _ f pc W PO' ltac:(lia)), cc'_rg, Nat.eqb_refl; reflexivity).
        assert (FBt : fbit F i pc = true).
        { unfold fbit, fof. rewrite Ii, Nat.eqb_refl, (proj2 (Nat.ltb_lt pc (S pc)) ltac:(lia)), Rp, odd_b2n, Ea. apply vok_vd. }
        rewrite Vo, CF, FBt, HV, Ea. reflexivity. }
    rename X0 into X.
    + rewrite hpa_pc_none by auto. destruct (eff_read _ _ _ _ _ _ _ _ _ He (eq_trans Xl X)) as (_ & Ea).
      assert (EV : enc (map (cellv p c cc pc N Bo F r pc pc) (icells i)) = enc (rdvals (mof s c) (icells i) u)).
      { f_equal. unfold rdvals. apply map_ext_in. intros x Ix. rewrite ord_cv by (rewrite Ii; apply bitc_notin; exact Ix). rewrite cellv_lt by lia.
        rewrite cc'_rv, Nat.eqb_refl. reflexivity. }
      cbv zeta. rewrite EV. transitivity (areg i w (enc (rdvals (mof s c) (icells i) u))); [|symmetry; exact Ea].
      destruct (is_cas i) eqn:Ci'.
      * rewrite (areg_cas _ _ _ Ci'). f_equal. rewrite ?Ii. destruct (ins_agree p W c pc r (rg cc) (Ag pc (le_n _))) as (_ & E2). rewrite Ii in E2.
        rewrite (cexp_ieval _ _ _ E2).
        assert (Rp : r pc = a) by (rewrite (creg_lt_pc p c cc' (S pc) (tp s' c) _ f pc W PO' ltac:(lia)), cc'_rg, Nat.eqb_refl; reflexivity).
        assert (FBw : fbit F i pc = w).
        { unfold fbit, fof. rewrite Ii, Nat.eqb_refl, (proj2 (Nat.ltb_lt pc (S pc)) ltac:(lia)), Rp, odd_b2n, Ea, (areg_cas _ _ _ Ci'). apply vok_vd. }
        rewrite FBw. destruct (Bool.bool_dec w true) as [Wt|Wf].
        -- pose proof He as He'. rewrite Wt in He' |- *. rewrite (eff_w_cas _ _ _ _ _ _ _ _ _ He' Ci' eq_refl). reflexivity.
        -- apply not_true_is_false in Wf. rewrite Wf, andb_false_r. reflexivity.
      * destruct i; simpl in Ci'; try discriminate; reflexivity.
  - rewrite (proj2 (Nat.ltb_ge j pc)), (proj2 (Nat.ltb_ge j (S pc))) by lia.
    destruct (is_load (ins p c j r) && icond (ins p c j r) r); [|reflexivity].
    rewrite pa_gt by lia. destruct (pend_at p c cc' (S pc) (tp s' c) r j) as [n|] eqn:Pn.
    + rewrite cc'_rg. destruct (Nat.eqb_spec n pc); [|reflexivity].
      exfalso. destruct (pend_at_spec _ _ _ _ _ _ _ _ Pn) as (_ & Ln & _). lia.
    + rewrite (cfx_fx cc cc' j) by (rewrite cc'_fx; reflexivity). f_equal.
      rewrite hpa_gt by lia. destruct (hpend_at p c cc' (S pc) (tp s' c) r j) as [n|] eqn:Ph.
      * rewrite cc'_rg. destruct (Nat.eqb_spec n pc); [|rewrite fof_bit by first [lia|assumption|(rewrite pend_new_r; assumption)|(rewrite pend_new_old by auto; assumption)]; reflexivity].
        exfalso. rewrite <- ord_pc in Ph. apply (hpend_at_char_s p s' c I') in Ph. rewrite ord_pc in Ph. destruct Ph as (? & ? & (? & _) & _). lia.
      * cbv zeta. rewrite fof_bit by first [lia|assumption|(rewrite pend_new_r; assumption)|(rewrite pend_new_old by auto; assumption)]. erewrite map_ext_in; [reflexivity|]. intros x Ix. apply ord_cv. apply bitc_notin. exact Ix.
Qed.

End OrdR.


Lemma INVP_ord : INVP p s'.
Proof.
  intros c0 k d B f P. destruct (Nat.eq_dec c0 c) as [->|N0].
  2:{ assert (E : cs s' c0 = cs s c0) by (unfold sord; apply cs_other; auto).
      assert (E2 : pcs s' c0 = pcs s c0) by (unfold sord, evs; simpl; apply upd_neq; auto).
      assert (E3 : tp s' c0 = tp s c0) by (unfold sord, evs; simpl; apply upd_neq; auto).
      rewrite E, E2, E3 in *. apply (IP c0 k d B f P). }
  rewrite ord_pc in *. destruct P as (P1 & P2 & P3).
  destruct (oc cc' k) as [t|] eqn:Ot; [|congruence].
  assert (Pk' : pending cc' (S pc) k d) by (split; [exact P1|split; [congruence|exact P3]]).
  destruct (proj1 (ord_peq k d t) (conj Pk' Ot)) as (Po & Ot' & Lk).
  set (r := creg p c cc' (S pc) (tp s' c) (bor (bd cc') B) f).
  set (F := fof p c cc' (S pc) (tp s' c) (bor (bd cc') B) f r).
  assert (EQ : forall j, creg p c cc pc N (bor (bd cc) (Bm B)) F j = r j).
  { apply creg_ext; [exact W|apply (pend_ok_of p s c I)|]. intros j. apply ord_pt. }
  destruct (IP c k d (Bm B) F Po) as (j' & _ & t0 & O0 & Fj). rewrite Ot' in O0. injection O0 as <-.
  apply (first_at_ext p c cc pc _ r t d j' W EQ) in Fj.
  assert (PO' : pend_ok cc' (S pc)) by (rewrite <- ord_pc; apply (pend_ok_of p s' c I')).
  assert (Ag : agree r (rg cc) pc).
  { intros i0 Li. transitivity (rg cc' i0).
    - unfold r. apply (creg_lt_pc p c cc' (S pc) _ _ f i0 W PO'). lia.
    - rewrite cc'_rg. destruct (Nat.eqb_spec i0 pc); [lia|auto]. }
  destruct (Nat.eq_dec j' pc) as [->|Nj].
  - exfalso. pose proof (first_at_eof _ _ _ _ _ _ _ _ Fj) as F2.
    assert (F2' : eof (ins p c pc (rg cc)) (rg cc) = Some d) by (rewrite <- (eof_agree p W c pc r (rg cc) Ag); exact F2).
    destruct (eof_exec_tied p c pc (rg cc) d Wc F2') as [Ex T0]. rewrite Hi in Ex, T0.
    apply (Hb Ex k d Po T0).
  - exists j'. split; auto. exists t. split; auto. apply (ord_shift r Ag t k d j' Pk' Ot).
    + pose proof (first_at_le _ _ _ _ _ _ _ _ Fj). lia.
    + exact Fj.
Qed.

Lemma INVH_ord : INVH p s'.
Proof.
  intros c0 k m xs B f P C. destruct (Nat.eq_dec c0 c) as [->|N0].
  2:{ assert (E : cs s' c0 = cs s c0) by (unfold sord; apply cs_other; auto).
      assert (E2 : pcs s' c0 = pcs s c0) by (unfold sord, evs; simpl; apply upd_neq; auto).
      assert (E3 : tp s' c0 = tp s c0) by (unfold sord, evs; simpl; apply upd_neq; auto).
      rewrite E, E2, E3 in *. apply (IPh c0 k m xs B f P C). }
  rewrite ord_pc in *.
  destruct (oh cc' k) as [t|] eqn:Ot; [|destruct P as (_ & P & _); congruence].
  destruct (proj1 (ord_peqh k m xs t) (conj P Ot)) as (Po & Ot' & Lk).
  assert (C0 : oc cc k = None) by (rewrite cc'_oc in C; destruct (Nat.eqb_spec k pc); [lia|exact C]).
  set (r := creg p c cc' (S pc) (tp s' c) (bor (bd cc') B) f).
  set (F := fof p c cc' (S pc) (tp s' c) (bor (bd cc') B) f r).
  assert (EQ : forall j, creg p c cc pc N (bor (bd cc) (Bm B)) F j = r j).
  { apply creg_ext; [exact W|apply (pend_ok_of p s c I)|]. intros j. apply ord_pt. }
  destruct (IPh c k m xs (Bm B) F Po C0) as (j' & _ & _ & t0 & O0 & Fj). rewrite Ot' in O0. injection O0 as <-.
  apply (first_atR_ext p c cc pc _ r t m xs j' W EQ) in Fj.
  assert (PO' : pend_ok cc' (S pc)) by (rewrite <- ord_pc; apply (pend_ok_of p s' c I')).
  assert (Ag : agree r (rg cc) pc).
  { intros i0 Li. transitivity (rg cc' i0).
    - unfold r. apply (creg_lt_pc p c cc' (S pc) _ _ f i0 W PO'). lia.
    - rewrite cc'_rg. destruct (Nat.eqb_spec i0 pc); [lia|auto]. }
  destruct (Nat.eq_dec j' pc) as [->|Nj].
  - exfalso. pose proof (first_atR_eofR _ _ _ _ _ _ _ _ _ Fj) as F2.
    destruct (ord_Ii r Ag) as [Ii' _].
    destruct (eofR_exec_tied p c pc r m xs Wc F2) as [Ex T0]. rewrite Ii' in T0.
    assert (Ex' : executes i (rg cc) = true) by (rewrite (exec_agree p W c pc r (rg cc) Ag), Hi in Ex; exact Ex).
    apply (Hbh Ex' k m xs Po ltac:(lia) T0).
  - exists j'. split; [exact P|]. split; [exact C|]. exists t. split; auto. apply (ord_shiftR r Ag t k m xs j' P Ot).
    + pose proof (first_atR_le _ _ _ _ _ _ _ _ _ Fj). lia.
    + exact Fj.
Qed.

End OrdP.

(* ---------- passing a non-executing instruction ---------- *)
Section SkipP.
Variables (p : prog) (s : st) (c : nat).
Hypothesis W : wf p.
Hypothesis Wc : cellful p.
Hypothesis I : Inv1 p s.
Hypothesis J : Inv2 p s.
Hypothesis IP : INVP p s.
Hypothesis IPh : INVH p s.
Local Abbreviation cc := (cs s c).
Local Abbreviation pc := (pcs s c).
Hypothesis Hx : executes (ins p c pc (rg cc)) (rg cc) = false.
Hypothesis Ho : oc cc pc = None.
Hypothesis Hh : oh cc pc = None.
Local Abbreviation s' := (sskip p s c).
Hypothesis I' : Inv1 p s'.
Local Abbreviation cc' := (cs s' c).
Local Abbreviation N := (tp s c).

Lemma sk_cc : cc' = mkC (oc cc) (rg cc) (upd (ai cc) pc (ins p c pc (rg cc))) (rw cc) (rv cc) (bd cc)
  (vP cc) (vA cc) (vR cc) (vO cc) (vOg cc) (oh cc) (fx cc).
Proof. unfold sskip; simpl. apply upd_eq. Qed.
Lemma sk_pc : pcs s' c = S pc.
Proof. unfold sskip; simpl. apply upd_eq. Qed.

Lemma sk_peq : forall k d t, (pending cc' (S pc) k d /\ oc cc' k = Some t) <->
  (pending cc pc k d /\ oc cc k = Some t /\ pc < k).
Proof.
  intros k d t. unfold pending. rewrite sk_cc; cbn [oc ai]. unfold upd. split.
  - intros ((P1 & P2 & P3) & O). destruct (Nat.eqb_spec k pc); [lia|]. repeat split; auto; lia.
  - intros ((P1 & P2 & P3) & O & L). destruct (Nat.eqb_spec k pc); [lia|]. repeat split; auto; lia.
Qed.

Lemma sk_peqh : forall k m xs t, (hpending cc' (S pc) k m xs /\ oh cc' k = Some t) <->
  (hpending cc pc k m xs /\ oh cc k = Some t /\ pc < k).
Proof.
  intros k m xs t. unfold hpending. rewrite sk_cc; cbn [oh ai]. unfold upd. split.
  - intros ((P1 & P2 & P3) & O). destruct (Nat.eqb_spec k pc); [lia|]. repeat split; auto; lia.
  - intros ((P1 & P2 & P3) & O & L). destruct (Nat.eqb_spec k pc); [lia|]. repeat split; auto; lia.
Qed.

Lemma sk_hlv : forall k T, pc < k -> (hlive cc' k T <-> hlive cc k T).
Proof. intros k T L. unfold hlive. rewrite sk_cc; cbn [oc]. tauto. Qed.

(* under registers that agree before pc, the slot pc does not execute *)
Lemma sk_nx : forall r, agree r (rg cc) pc -> executes (ins p c pc r) r = false.
Proof. intros r Ag. rewrite (exec_agree p W c pc r (rg cc) Ag). exact Hx. Qed.

Lemma sk_shift : forall r, agree r (rg cc) pc -> forall t k d j, pending cc' (S pc) k d -> oc cc' k = Some t -> S pc <= j ->
  (first_at p c cc pc r t d j <-> first_at p c cc' (S pc) r t d j).
Proof.
  intros r Ag. pose proof (sk_nx r Ag) as NX. apply place_shift.
  - apply sk_peq.
  - intros d t j (_ & P2 & _) O. congruence.
  - intros k d t P O Ex _ Ti. congruence.
  - apply sk_peqh.
  - apply sk_hlv.
  - intros m xs t j (_ & P2 & _) O. congruence.
  - intros k m xs t P O Ex _ Ti. congruence.
Qed.

Lemma sk_shiftR : forall r, agree r (rg cc) pc -> forall t k m xs j, hpending cc' (S pc) k m xs -> oh cc' k = Some t -> S pc <= j ->
  (first_atR p c cc pc r t m xs j <-> first_atR p c cc' (S pc) r t m xs j).
Proof.
  intros r Ag. pose proof (sk_nx r Ag) as NX. apply place_shiftR.
  - apply sk_peq.
  - intros d t j (_ & P2 & _) O. congruence.
  - intros k d t P O Ex _ Ti. congruence.
  - apply sk_peqh.
  - apply sk_hlv.
  - intros m xs t j (_ & P2 & _) O. congruence.
  - intros k m xs t P O Ex _ Ti. congruence.
Qed.

Section SkipR.
Variables (B : nat -> bool) (f : nat -> cell -> val).
Local Abbreviation r := (creg p c cc' (S pc) (tp s' c) (bor (bd cc') B) f).
Local Abbreviation F := (fof p c cc' (S pc) (tp s' c) (bor (bd cc') B) f r).

Lemma sPO' : pend_ok cc' (S pc).
Proof. rewrite <- sk_pc; apply (pend_ok_of p s' c I'). Qed.

Lemma sAg : agree r (rg cc) pc.
Proof.
  intros i0 Li. transitivity (rg cc' i0).
  - apply (creg_lt_pc p c cc' (S pc) _ _ f i0 W sPO'). lia.
  - rewrite sk_cc. reflexivity.
Qed.

Lemma sk_nl : is_load (ins p c pc r) && icond (ins p c pc r) r = false.
Proof.
  pose proof (sk_nx r sAg) as NX. unfold executes in NX.
  destruct (isacc (ins p c pc r)) eqn:A; [|destruct (ins p c pc r); simpl in A; try discriminate; reflexivity].
  rewrite NX. apply andb_false_r.
Qed.

Lemma s_pa_gt : forall j, S pc <= j -> pend_at p c cc pc N r j = pend_at p c cc' (S pc) (tp s' c) r j.
Proof.
  intros j L. pose proof (pend_at_eq_s p s s' c c r j I I') as QE. rewrite sk_pc in QE. apply QE; [|reflexivity].
  intros k. split.
  - intros (d & Pk & t & O & F0). destruct (Nat.eq_dec k pc) as [->|Nk].
    + exfalso. destruct Pk as (_ & Pk & _). congruence.
    + assert (Q : pending cc' (S pc) k d /\ oc cc' k = Some t) by (apply sk_peq; split; [exact Pk|split; [exact O|]]; destruct Pk as (? & _); lia).
      destruct Q as [Q1 Q2]. exists d. split; auto. exists t. split; auto.
      apply (sk_shift r sAg t k d j Q1 Q2 ltac:(lia)). exact F0.
  - intros (d & Pk & t & O & F0). destruct (proj1 (sk_peq k d t) (conj Pk O)) as (Q1 & Q2 & Q3).
    exists d. split; auto. exists t. split; auto. apply (sk_shift r sAg t k d j Pk O ltac:(lia)). exact F0.
Qed.

Lemma s_hpa_gt : forall j, S pc <= j -> hpend_at p c cc pc N r j = hpend_at p c cc' (S pc) (tp s' c) r j.
Proof.
  intros j L. pose proof (hpend_at_eq_s p s s' c r j I I') as QE. rewrite sk_pc in QE. apply QE.
  intros k. split.
  - intros (m & xs & Pk & C & t & O & F0). destruct (Nat.eq_dec k pc) as [->|Nk].
    + exfalso. congruence.
    + assert (Lk : pc < k) by (destruct Pk as (? & _); lia).
      assert (Q : hpending cc' (S pc) k m xs /\ oh cc' k = Some t) by (apply sk_peqh; auto).
      destruct Q as [Q1 Q2]. exists m, xs. split; [exact Q1|]. split; [rewrite sk_cc; exact C|].
      exists t. split; auto. apply (sk_shiftR r sAg t k m xs j Q1 Q2 ltac:(lia)). exact F0.
  - intros (m & xs & Pk & C & t & O & F0). destruct (proj1 (sk_peqh k m xs t) (conj Pk O)) as (Q1 & Q2 & Q3).
    exists m, xs. split; [exact Q1|]. split; [rewrite sk_cc in C; exact C|].
    exists t. split; auto. apply (sk_shiftR r sAg t k m xs j Pk O ltac:(lia)). exact F0.
Qed.

Local Abbreviation Bo := (bor (bd cc) B).
Local Abbreviation Bn := (bor (bd cc') B).

(* a cell's value is the same before and after, at every slot but pc (which
   reads nothing) *)
Lemma sk_cv : forall n b x, b <> pc ->
  x <> bitc (ins p c b r) ->
  cellv p c cc pc N Bo F r n b x = cellv p c cc' (S pc) (tp s' c) Bn f r b b x.
Proof.
  intros n. induction n as [|n IH]; intros b x Nb Hbx.
  all: destruct (Nat.lt_ge_cases b pc) as [L|L];
         [rewrite cellv_lt by auto; rewrite cellv_lt by lia; rewrite sk_cc; reflexivity|].
  all: assert (L' : S pc <= b) by lia.
  all: destruct (is_load (ins p c b r) && icond (ins p c b r) r) eqn:X;
         [|rewrite cellv_nl by (auto; lia); rewrite cellv_nl by (auto; lia); reflexivity].
  all: destruct (pend_at p c cc' (S pc) (tp s' c) r b) as [n0|] eqn:P.
  all: try (rewrite (cellv_pd _ _ cc pc N _ _ _ _ _ _ n0) by (auto; try lia; rewrite s_pa_gt by lia; exact P);
            rewrite (cellv_pd _ _ cc' (S pc)) with (k := n0) by (auto; lia); rewrite sk_cc; reflexivity).
  all: destruct (hpend_at p c cc' (S pc) (tp s' c) r b) as [n0|] eqn:Ph.
  all: try (rewrite (cellv_hpd _ _ cc pc N _ _ _ _ _ _ n0) by first [lia|assumption|(rewrite s_pa_gt by lia; exact P)|(rewrite s_hpa_gt by lia; exact Ph)];
            rewrite (cellv_hpd _ _ cc' (S pc)) with (k := n0) by (auto; lia); rewrite sk_cc; reflexivity).
  - rewrite cellv_free by first [lia|assumption|(rewrite s_pa_gt by lia; exact P)|(rewrite s_hpa_gt by lia; exact Ph)]. unfold fof; rewrite (proj2 (Nat.eqb_neq _ _) Hbx). reflexivity.
  - rewrite cellv_go by first [lia|assumption|(rewrite s_pa_gt by lia; exact P)|(rewrite s_hpa_gt by lia; exact Ph)].
    assert (BB : Bo b = Bn b) by (rewrite sk_cc; reflexivity).
    rewrite BB. destruct (Bn b) eqn:Bb; [|unfold fof; rewrite (proj2 (Nat.eqb_neq _ _) Hbx); reflexivity].
    destruct (fbinder p c r b x) as [b0|] eqn:Fb; [|unfold fof; rewrite (proj2 (Nat.eqb_neq _ _) Hbx); reflexivity].
    destruct b as [|b']; [lia|].
    rewrite (cellv_go _ _ cc' (S pc) _ Bn f r b') by (auto; lia). rewrite Bb, Fb.
    pose proof (fbinder_lt _ _ _ _ _ _ Fb). pose proof (fbinder_shape _ _ _ _ _ _ Fb) as (Exb & _).
    assert (Nb0 : b0 <> pc) by (intros ->; rewrite (sk_nx r sAg) in Exb; discriminate).
    f_equal. rewrite (IH b0 x Nb0); [symmetry; apply cellv_fuel; lia|]. apply bitc_notin. apply (fbinder_shape _ _ _ _ _ _ Fb).
Qed.

(* the registers after the step are registers the context could have taken
   before it *)
Lemma sk_pt : forall j, slotv p c cc pc N Bo F r j = r j.
Proof.
  intros j.
  assert (Rfix : r j = slotv p c cc' (S pc) (tp s' c) Bn f r j) by (apply creg_fix; auto; apply sPO').
  rewrite Rfix. unfold slotv.
  destruct (Nat.lt_trichotomy j pc) as [L|[L|L]].
  - rewrite (proj2 (Nat.ltb_lt j pc) L), (proj2 (Nat.ltb_lt j (S pc))) by lia. rewrite sk_cc. reflexivity.
  - subst j. rewrite Nat.ltb_irrefl, (proj2 (Nat.ltb_lt pc (S pc))) by lia. rewrite sk_nl. rewrite sk_cc; cbn [rg].
    symmetry. apply (i_rg0 p s I c pc Ho Hh).
  - rewrite (proj2 (Nat.ltb_ge j pc)), (proj2 (Nat.ltb_ge j (S pc))) by lia.
    destruct (is_load (ins p c j r) && icond (ins p c j r) r); [|reflexivity].
    rewrite s_pa_gt by lia. destruct (pend_at p c cc' (S pc) (tp s' c) r j) as [n|] eqn:Pn; [rewrite sk_cc; reflexivity|].
    rewrite (cfx_fx cc cc' j) by (rewrite sk_cc; reflexivity). f_equal.
    rewrite s_hpa_gt by lia. destruct (hpend_at p c cc' (S pc) (tp s' c) r j) as [n|] eqn:Ph; [rewrite fof_bit by first [lia|assumption|(rewrite pend_new_r; assumption)|(rewrite pend_new_old by auto; assumption)]; rewrite sk_cc; reflexivity|].
    cbv zeta. rewrite fof_bit by first [lia|assumption|(rewrite pend_new_r; assumption)|(rewrite pend_new_old by auto; assumption)]. erewrite map_ext_in; [reflexivity|]. intros x Ix. apply sk_cv; [lia|apply bitc_notin; exact Ix].
Qed.

End SkipR.

Lemma INVP_skip : INVP p s'.
Proof.
  intros c0 k d B f P. destruct (Nat.eq_dec c0 c) as [->|N0].
  2:{ assert (E : cs s' c0 = cs s c0) by (unfold sskip; simpl; apply upd_neq; auto).
      assert (E2 : pcs s' c0 = pcs s c0) by (unfold sskip; simpl; apply upd_neq; auto).
      assert (E3 : tp s' c0 = tp s c0) by (unfold sskip; simpl; apply upd_neq; auto).
      rewrite E, E2, E3 in *. apply (IP c0 k d B f P). }
  rewrite sk_pc in *. destruct P as (P1 & P2 & P3).
  destruct (oc cc' k) as [t|] eqn:Ot; [|congruence].
  assert (Pk' : pending cc' (S pc) k d) by (split; [exact P1|split; [congruence|exact P3]]).
  destruct (proj1 (sk_peq k d t) (conj Pk' Ot)) as (Po & Ot' & Lk).
  set (r := creg p c cc' (S pc) (tp s' c) (bor (bd cc') B) f).
  set (F := fof p c cc' (S pc) (tp s' c) (bor (bd cc') B) f r).
  assert (EQ : forall j, creg p c cc pc N (bor (bd cc) B) F j = r j).
  { apply creg_ext; [exact W|apply (pend_ok_of p s c I)|]. intros j. apply sk_pt. }
  destruct (IP c k d B F Po) as (j' & _ & t0 & O0 & Fj). rewrite Ot' in O0. injection O0 as <-.
  apply (first_at_ext p c cc pc _ r t d j' W EQ) in Fj.
  pose proof (sAg B f) as Ag. fold r in Ag.
  destruct (Nat.eq_dec j' pc) as [->|Nj].
  - exfalso. pose proof (first_at_eof _ _ _ _ _ _ _ _ Fj) as F2.
    destruct (eof_exec_tied p c pc r d Wc F2) as [Ex _]. rewrite (sk_nx r Ag) in Ex. discriminate.
  - exists j'. split; auto. exists t. split; auto. apply (sk_shift r Ag t k d j' Pk' Ot).
    + pose proof (first_at_le _ _ _ _ _ _ _ _ Fj). lia.
    + exact Fj.
Qed.

Lemma INVH_skip : INVH p s'.
Proof.
  intros c0 k m xs B f P C. destruct (Nat.eq_dec c0 c) as [->|N0].
  2:{ assert (E : cs s' c0 = cs s c0) by (unfold sskip; simpl; apply upd_neq; auto).
      assert (E2 : pcs s' c0 = pcs s c0) by (unfold sskip; simpl; apply upd_neq; auto).
      assert (E3 : tp s' c0 = tp s c0) by (unfold sskip; simpl; apply upd_neq; auto).
      rewrite E, E2, E3 in *. apply (IPh c0 k m xs B f P C). }
  rewrite sk_pc in *.
  destruct (oh cc' k) as [t|] eqn:Ot; [|destruct P as (_ & P & _); congruence].
  destruct (proj1 (sk_peqh k m xs t) (conj P Ot)) as (Po & Ot' & Lk).
  assert (C0 : oc cc k = None) by (rewrite sk_cc in C; exact C).
  set (r := creg p c cc' (S pc) (tp s' c) (bor (bd cc') B) f).
  set (F := fof p c cc' (S pc) (tp s' c) (bor (bd cc') B) f r).
  assert (EQ : forall j, creg p c cc pc N (bor (bd cc) B) F j = r j).
  { apply creg_ext; [exact W|apply (pend_ok_of p s c I)|]. intros j. apply sk_pt. }
  destruct (IPh c k m xs B F Po C0) as (j' & _ & _ & t0 & O0 & Fj). rewrite Ot' in O0. injection O0 as <-.
  apply (first_atR_ext p c cc pc _ r t m xs j' W EQ) in Fj.
  pose proof (sAg B f) as Ag. fold r in Ag.
  destruct (Nat.eq_dec j' pc) as [->|Nj].
  - exfalso. pose proof (first_atR_eofR _ _ _ _ _ _ _ _ _ Fj) as F2.
    destruct (eofR_exec_tied p c pc r m xs Wc F2) as [Ex _]. rewrite (sk_nx r Ag) in Ex. discriminate.
  - exists j'. split; [exact P|]. split; [exact C|]. exists t. split; auto. apply (sk_shiftR r Ag t k m xs j' P Ot).
    + pose proof (first_atR_le _ _ _ _ _ _ _ _ _ Fj). lia.
    + exact Fj.
Qed.

End SkipP.

Lemma eff_cas_a : forall t m xs c0 e n r m0 m' a K u w, c0 r = true -> eff t (ICas m xs c0 e n) r m0 m' a K u w ->
  a = vd w (enc (rdvals m0 (dd xs) u)).
Proof. intros t m xs c0 e n r m0 m' a K u w C H. inversion H; subst; auto. unfold icond in *; simpl in *. congruence. Qed.

Lemma eofR_ld : forall i0 r0 mx, eofR i0 r0 = Some mx -> is_load i0 && icond i0 r0 = true.
Proof.
  intros i0 r0 mx ER. destruct i0 as [| |m0 x0 c0 e0 n0| |]; simpl in ER; try discriminate.
  unfold icond; simpl. destruct (c0 r0); [reflexivity|discriminate ER].
Qed.

(* ---------- passing a CAS whose read happened alone and whose comparison
   fails (its write half is nothing) ---------- *)
Section SkipF.
Variables (p : prog) (s : st) (c t1 : nat) (xs : list cell).
Hypothesis W : wf p.
Hypothesis Wc : cellful p.
Hypothesis I : Inv1 p s.
Hypothesis J : Inv2 p s.
Hypothesis IP : INVP p s.
Hypothesis IPh : INVH p s.
Local Abbreviation cc := (cs s c).
Local Abbreviation pc := (pcs s c).
Hypothesis Ho : oc cc pc = None.
Hypothesis Oh : oh cc pc = Some t1.
Hypothesis Ax : ai cc pc = crd Plain xs.
Hypothesis Er : eofR (ins p c pc (rg cc)) (rg cc) = Some (Plain, xs).
Hypothesis Hcf : cfail (ins p c pc (rg cc)) (rg cc) pc = true.
Hypothesis Hvk : vok (rg cc pc) = false.
Hypothesis Hf : hfirst cc pc (ins p c pc (rg cc)).
Hypothesis Hfx : fxok cc pc (ins p c pc (rg cc)) (rg cc) (rg cc pc).
Local Abbreviation s' := (sskip p s c).
Hypothesis I' : Inv1 p s'.
Local Abbreviation cc' := (cs s' c).
Local Abbreviation N := (tp s c).

Lemma skf_cc : cc' = mkC (oc cc) (rg cc) (upd (ai cc) pc (ins p c pc (rg cc))) (rw cc) (rv cc) (bd cc)
  (vP cc) (vA cc) (vR cc) (vO cc) (vOg cc) (oh cc) (fx cc).
Proof. unfold sskip; simpl. apply upd_eq. Qed.
Lemma skf_pc : pcs s' c = S pc.
Proof. unfold sskip; simpl. apply upd_eq. Qed.

Lemma skf_peq : forall k d t, (pending cc' (S pc) k d /\ oc cc' k = Some t) <->
  (pending cc pc k d /\ oc cc k = Some t /\ pc < k).
Proof.
  intros k d t. unfold pending. rewrite skf_cc; cbn [oc ai]. unfold upd. split.
  - intros ((P1 & P2 & P3) & O). destruct (Nat.eqb_spec k pc); [lia|]. repeat split; auto; lia.
  - intros ((P1 & P2 & P3) & O & L). destruct (Nat.eqb_spec k pc); [lia|]. repeat split; auto; lia.
Qed.

Lemma skf_peqh : forall k m xs0 t, (hpending cc' (S pc) k m xs0 /\ oh cc' k = Some t) <->
  (hpending cc pc k m xs0 /\ oh cc k = Some t /\ pc < k).
Proof.
  intros k m xs0 t. unfold hpending. rewrite skf_cc; cbn [oh ai]. unfold upd. split.
  - intros ((P1 & P2 & P3) & O). destruct (Nat.eqb_spec k pc); [lia|]. repeat split; auto; lia.
  - intros ((P1 & P2 & P3) & O & L). destruct (Nat.eqb_spec k pc); [lia|]. repeat split; auto; lia.
Qed.

Lemma skf_hlv : forall k T, pc < k -> (hlive cc' k T <-> hlive cc k T).
Proof. intros k T L. unfold hlive. rewrite skf_cc; cbn [oc]. tauto. Qed.

Lemma skf_hpend : hpending cc pc pc Plain xs.
Proof. split; [lia|split; [congruence|rewrite Ax; reflexivity]]. Qed.

Lemma skf_tied : forall r a, agree r (rg cc) pc -> tied (ins p c pc r) a -> tied (ins p c pc (rg cc)) a.
Proof. intros r a Ag T. rewrite <- (proj1 (ins_agree p W c pc r (rg cc) Ag)). exact T. Qed.

(* the CAS's read has its place at pc *)
Lemma skf_place : forall r, agree r (rg cc) pc -> first_atR p c cc pc r t1 Plain xs pc.
Proof.
  intros r Ag.
  assert (ER : eofR (ins p c pc r) r = Some (Plain, xs)) by (rewrite (eofR_agree p W c pc r (rg cc) Ag); exact Er).
  apply first_atR_mk; [lia|exact ER| | |intros; lia].
  - intros (k' & t' & d' & P' & O' & Lt & F). pose proof (first_at_eof _ _ _ _ _ _ _ _ F) as D.
    destruct (eof_exec_tied p c pc r d' Wc D) as [_ T0]. apply (skf_tied r _ Ag) in T0.
    assert (Nk : k' <> pc) by (intros ->; congruence).
    pose proof (proj1 (Hf t1 Oh) k' d' t' P' Nk O' T0). lia.
  - intros (k' & t' & m0 & xs0 & P' & O' & Lt & Hl & F). pose proof (first_atR_eofR _ _ _ _ _ _ _ _ _ F) as D.
    destruct (eofR_exec_tied p c pc r m0 xs0 Wc D) as [_ T0]. apply (skf_tied r _ Ag) in T0.
    assert (Nk : k' <> pc) by (intros ->; rewrite Oh in O'; injection O' as <-; lia).
    pose proof (proj2 (Hf t1 Oh) k' m0 xs0 t' P' Nk O' T0). lia.
Qed.

(* after the read, the CAS's place is taken by its read *)
Lemma skf_htaken : forall r t, agree r (rg cc) pc -> t1 < t -> htaken p c cc pc r t pc.
Proof.
  intros r t Ag L. exists pc, t1, Plain, xs. split; [exact skf_hpend|]. split; [exact Oh|]. split; [exact L|].
  split; [intros t2 E; congruence|]. apply skf_place. exact Ag.
Qed.

Lemma skf_oldh : forall r, agree r (rg cc) pc -> forall m xs0 t j, hpending cc pc pc m xs0 -> oh cc pc = Some t ->
  first_atR p c cc pc r t m xs0 j -> j = pc.
Proof.
  intros r Ag m xs0 t j (_ & _ & Cx) O F. rewrite Ax in Cx. injection Cx as <- <-. rewrite Oh in O. injection O as <-.
  apply (first_atR_unique p c cc pc r t1 Plain xs j pc Wc F). apply skf_place. exact Ag.
Qed.

(* nothing tied to the CAS that happened after its read needs it: the read
   took its place and the comparison fails *)
Lemma skf_nofx : forall r t, agree r (rg cc) (S pc) -> t1 < t ->
  (forall v, htakenv p c cc pc r t pc v -> cfailv (ins p c pc r) r v = false) -> False.
Proof.
  intros r t Ag L Fx. assert (Ag0 : agree r (rg cc) pc) by (apply (agree_le r (rg cc) (S pc)); auto).
  assert (X : htakenv p c cc pc r t pc (rg cc pc)).
  { exists pc, t1, Plain, xs. split; [exact skf_hpend|]. split; [exact Oh|]. split; [exact L|].
    split; [intros t2 E; congruence|]. split; [apply skf_place; exact Ag0|symmetry; apply Ag; lia]. }
  specialize (Fx _ X). rewrite (cfailv_agree p W c pc r (rg cc) _ Ag0) in Fx. unfold cfail in Hcf. congruence.
Qed.

Lemma skf_blk : forall r, agree r (rg cc) (S pc) -> forall k d t, pending cc' (S pc) k d -> oc cc' k = Some t ->
  executes (ins p c pc r) r = true ->
  (forall v, htakenv p c cc pc r t pc v -> cfailv (ins p c pc r) r v = false) ->
  tied (ins p c pc r) (inst_of d) -> taken p c cc pc r t pc.
Proof.
  intros r Ag k d t P O _ Fx Ti. exfalso. destruct (proj1 (skf_peq k d t) (conj P O)) as (Pk & Ok & Lk).
  assert (Ag0 : agree r (rg cc) pc) by (apply (agree_le r (rg cc) (S pc)); auto).
  apply (skf_tied r _ Ag0) in Ti. pose proof (proj1 (Hf t1 Oh) k d t Pk ltac:(lia) Ok Ti).
  apply (skf_nofx r t Ag); auto.
Qed.

Lemma skf_blkh : forall r, agree r (rg cc) (S pc) -> forall k m xs0 t, hpending cc' (S pc) k m xs0 -> oh cc' k = Some t ->
  executes (ins p c pc r) r = true ->
  (forall v, htakenv p c cc pc r t pc v -> cfailv (ins p c pc r) r v = false) ->
  tied (ins p c pc r) (crd m xs0) -> taken p c cc pc r t pc.
Proof.
  intros r Ag k m xs0 t P O _ Fx Ti. exfalso. destruct (proj1 (skf_peqh k m xs0 t) (conj P O)) as (Pk & Ok & Lk).
  assert (Ag0 : agree r (rg cc) pc) by (apply (agree_le r (rg cc) (S pc)); auto).
  apply (skf_tied r _ Ag0) in Ti. pose proof (proj2 (Hf t1 Oh) k m xs0 t Pk ltac:(lia) Ok Ti).
  apply (skf_nofx r t Ag); auto.
Qed.

Lemma skf_shift : forall r, agree r (rg cc) (S pc) -> forall t k d j, pending cc' (S pc) k d -> oc cc' k = Some t -> S pc <= j ->
  (first_at p c cc pc r t d j <-> first_at p c cc' (S pc) r t d j).
Proof.
  intros r Ag. assert (Ag0 : agree r (rg cc) pc) by (apply (agree_le r (rg cc) (S pc)); auto).
  apply place_shift.
  - apply skf_peq.
  - intros d t j (_ & P2 & _) O. congruence.
  - apply (skf_blk r Ag).
  - apply skf_peqh.
  - apply skf_hlv.
  - apply (skf_oldh r Ag0).
  - apply (skf_blkh r Ag).
Qed.

Lemma skf_shiftR : forall r, agree r (rg cc) (S pc) -> forall t k m xs0 j, hpending cc' (S pc) k m xs0 -> oh cc' k = Some t ->
  S pc <= j -> (first_atR p c cc pc r t m xs0 j <-> first_atR p c cc' (S pc) r t m xs0 j).
Proof.
  intros r Ag. assert (Ag0 : agree r (rg cc) pc) by (apply (agree_le r (rg cc) (S pc)); auto).
  apply place_shiftR.
  - apply skf_peq.
  - intros d t j (_ & P2 & _) O. congruence.
  - apply (skf_blk r Ag).
  - apply skf_peqh.
  - apply skf_hlv.
  - apply (skf_oldh r Ag0).
  - apply (skf_blkh r Ag).
Qed.

(* no access that happened early has its place at pc *)
Lemma skf_noplace : forall r k d t, agree r (rg cc) pc -> pending cc pc k d -> oc cc k = Some t ->
  first_at p c cc pc r t d pc -> False.
Proof.
  intros r k d t Ag P O F. pose proof (first_at_eof _ _ _ _ _ _ _ _ F) as D.
  destruct (eof_exec_tied p c pc r d Wc D) as [_ T0]. apply (skf_tied r _ Ag) in T0.
  assert (Nk : k <> pc) by (intros ->; congruence).
  pose proof (proj1 (Hf t1 Oh) k d t P Nk O T0) as L.
  apply (first_at_hfree _ _ _ _ _ _ _ _ F). apply (skf_htaken r t Ag L).
Qed.

Lemma skf_noplaceh : forall r k m xs0 t, agree r (rg cc) pc -> hpending cc pc k m xs0 -> k <> pc -> oh cc k = Some t ->
  first_atR p c cc pc r t m xs0 pc -> False.
Proof.
  intros r k m xs0 t Ag P Nk O F. pose proof (first_atR_eofR _ _ _ _ _ _ _ _ _ F) as D.
  destruct (eofR_exec_tied p c pc r m xs0 Wc D) as [_ T0]. apply (skf_tied r _ Ag) in T0.
  pose proof (proj2 (Hf t1 Oh) k m xs0 t P Nk O T0) as L.
  apply (first_atR_hfree _ _ _ _ _ _ _ _ _ F). apply (skf_htaken r t Ag L).
Qed.

Section SkipFR.
Variables (B : nat -> bool) (f : nat -> cell -> val).
Local Abbreviation r := (creg p c cc' (S pc) (tp s' c) (bor (bd cc') B) f).
Local Abbreviation F := (fof p c cc' (S pc) (tp s' c) (bor (bd cc') B) f r).

Lemma fPO' : pend_ok cc' (S pc).
Proof. rewrite <- skf_pc; apply (pend_ok_of p s' c I'). Qed.

Lemma fAg : agree r (rg cc) (S pc).
Proof.
  intros i0 Li. transitivity (rg cc' i0).
  - apply (creg_lt_pc p c cc' (S pc) _ _ f i0 W fPO'). lia.
  - rewrite skf_cc. reflexivity.
Qed.

Lemma fAg0 : agree r (rg cc) pc.
Proof. apply (agree_le r (rg cc) (S pc)); [apply fAg|lia]. Qed.

Lemma skf_ld : is_load (ins p c pc r) && icond (ins p c pc r) r = true.
Proof.
  assert (ER : eofR (ins p c pc r) r = Some (Plain, xs)) by (rewrite (eofR_agree p W c pc r (rg cc) fAg0); exact Er).
  apply (eofR_ld _ _ _ ER).
Qed.

Lemma skf_pa_pc : pend_at p c cc pc N r pc = None.
Proof.
  apply (pend_at_none_s p s c I). intros (k & d & Pk & t & O & F0). apply (skf_noplace r k d t fAg0 Pk O F0).
Qed.

Lemma skf_hpa_pc : hpend_at p c cc pc N r pc = Some pc.
Proof.
  apply (hpend_at_char_s p s c I). exists Plain, xs. split; [exact skf_hpend|]. split; [exact Ho|].
  exists t1. split; [exact Oh|]. apply skf_place. exact fAg0.
Qed.

Lemma skf_pa_gt : forall j, S pc <= j -> pend_at p c cc pc N r j = pend_at p c cc' (S pc) (tp s' c) r j.
Proof.
  intros j L. pose proof (pend_at_eq_s p s s' c c r j I I') as QE. rewrite skf_pc in QE. apply QE; [|reflexivity].
  intros k. split.
  - intros (d & Pk & t & O & F0). destruct (Nat.eq_dec k pc) as [->|Nk].
    + exfalso. destruct Pk as (_ & Pk & _). congruence.
    + assert (Q : pending cc' (S pc) k d /\ oc cc' k = Some t) by (apply skf_peq; split; [exact Pk|split; [exact O|]]; destruct Pk as (? & _); lia).
      destruct Q as [Q1 Q2]. exists d. split; auto. exists t. split; auto.
      apply (skf_shift r fAg t k d j Q1 Q2 ltac:(lia)). exact F0.
  - intros (d & Pk & t & O & F0). destruct (proj1 (skf_peq k d t) (conj Pk O)) as (Q1 & Q2 & Q3).
    exists d. split; auto. exists t. split; auto. apply (skf_shift r fAg t k d j Pk O ltac:(lia)). exact F0.
Qed.

Lemma skf_hpa_gt : forall j, S pc <= j -> hpend_at p c cc pc N r j = hpend_at p c cc' (S pc) (tp s' c) r j.
Proof.
  intros j L. pose proof (hpend_at_eq_s p s s' c r j I I') as QE. rewrite skf_pc in QE. apply QE.
  intros k. split.
  - intros (m & xs0 & Pk & C & t & O & F0). destruct (Nat.eq_dec k pc) as [->|Nk].
    + exfalso. pose proof (skf_oldh r fAg0 m xs0 t j Pk O F0). lia.
    + assert (Lk : pc < k) by (destruct Pk as (? & _); lia).
      assert (Q : hpending cc' (S pc) k m xs0 /\ oh cc' k = Some t) by (apply skf_peqh; auto).
      destruct Q as [Q1 Q2]. exists m, xs0. split; [exact Q1|]. split; [rewrite skf_cc; exact C|].
      exists t. split; auto. apply (skf_shiftR r fAg t k m xs0 j Q1 Q2 ltac:(lia)). exact F0.
  - intros (m & xs0 & Pk & C & t & O & F0). destruct (proj1 (skf_peqh k m xs0 t) (conj Pk O)) as (Q1 & Q2 & Q3).
    exists m, xs0. split; [exact Q1|]. split; [rewrite skf_cc in C; exact C|].
    exists t. split; auto. apply (skf_shiftR r fAg t k m xs0 j Pk O ltac:(lia)). exact F0.
Qed.

Local Abbreviation Bo := (bor (bd cc) B).
Local Abbreviation Bn := (bor (bd cc') B).

Lemma skf_cv_pc : forall n x, x <> bitc (ins p c pc r) -> cellv p c cc pc N Bo F r n pc x = cellv p c cc' (S pc) (tp s' c) Bn f r pc pc x.
Proof.
  intros n x Hbx. rewrite (cellv_lt _ _ cc' (S pc)) by lia.
  transitivity (rv cc pc x); [|rewrite skf_cc; reflexivity].
  apply (cellv_hpd _ _ _ _ _ _ _ _ _ _ _ pc); [lia|exact skf_ld|exact skf_pa_pc|exact skf_hpa_pc].
Qed.

Lemma skf_cv : forall n b x,
  x <> bitc (ins p c b r) ->
  cellv p c cc pc N Bo F r n b x = cellv p c cc' (S pc) (tp s' c) Bn f r b b x.
Proof.
  intros n. induction n as [|n IH]; intros b x Hbx.
  all: destruct (Nat.lt_trichotomy b pc) as [L|[L|L]];
         [rewrite cellv_lt by auto; rewrite cellv_lt by lia; rewrite skf_cc; reflexivity|subst b; apply skf_cv_pc; exact Hbx|].
  all: assert (L' : S pc <= b) by lia.
  all: destruct (is_load (ins p c b r) && icond (ins p c b r) r) eqn:X;
         [|rewrite cellv_nl by (auto; lia); rewrite cellv_nl by (auto; lia); reflexivity].
  all: destruct (pend_at p c cc' (S pc) (tp s' c) r b) as [n0|] eqn:P.
  all: try (rewrite (cellv_pd _ _ cc pc N _ _ _ _ _ _ n0) by (auto; try lia; rewrite skf_pa_gt by lia; exact P);
            rewrite (cellv_pd _ _ cc' (S pc)) with (k := n0) by (auto; lia); rewrite skf_cc; reflexivity).
  all: destruct (hpend_at p c cc' (S pc) (tp s' c) r b) as [n0|] eqn:Ph.
  all: try (rewrite (cellv_hpd _ _ cc pc N _ _ _ _ _ _ n0) by first [lia|assumption|(rewrite skf_pa_gt by lia; exact P)|(rewrite skf_hpa_gt by lia; exact Ph)];
            rewrite (cellv_hpd _ _ cc' (S pc)) with (k := n0) by (auto; lia); rewrite skf_cc; reflexivity).
  - rewrite cellv_free by first [lia|assumption|(rewrite skf_pa_gt by lia; exact P)|(rewrite skf_hpa_gt by lia; exact Ph)]. unfold fof; rewrite (proj2 (Nat.eqb_neq _ _) Hbx). reflexivity.
  - rewrite cellv_go by first [lia|assumption|(rewrite skf_pa_gt by lia; exact P)|(rewrite skf_hpa_gt by lia; exact Ph)].
    assert (BB : Bo b = Bn b) by (rewrite skf_cc; reflexivity).
    rewrite BB. destruct (Bn b) eqn:Bb; [|unfold fof; rewrite (proj2 (Nat.eqb_neq _ _) Hbx); reflexivity].
    destruct (fbinder p c r b x) as [b0|] eqn:Fb; [|unfold fof; rewrite (proj2 (Nat.eqb_neq _ _) Hbx); reflexivity].
    destruct b as [|b']; [lia|].
    rewrite (cellv_go _ _ cc' (S pc) _ Bn f r b') by (auto; lia). rewrite Bb, Fb.
    pose proof (fbinder_lt _ _ _ _ _ _ Fb). f_equal. rewrite IH; try (apply bitc_notin; apply (fbinder_shape _ _ _ _ _ _ Fb)). symmetry. apply cellv_fuel. lia.
Qed.

Lemma skf_pt : forall j, slotv p c cc pc N Bo F r j = r j.
Proof.
  intros j.
  assert (Rfix : r j = slotv p c cc' (S pc) (tp s' c) Bn f r j) by (apply creg_fix; auto; apply fPO').
  rewrite Rfix. unfold slotv.
  destruct (Nat.lt_trichotomy j pc) as [L|[L|L]].
  - rewrite (proj2 (Nat.ltb_lt j pc) L), (proj2 (Nat.ltb_lt j (S pc))) by lia. rewrite skf_cc. reflexivity.
  - subst j. rewrite Nat.ltb_irrefl, (proj2 (Nat.ltb_lt pc (S pc))) by lia. rewrite skf_ld, skf_pa_pc, skf_hpa_pc.
    assert (CF : cfailv (ins p c pc r) r (rg cc pc) = true).
    { rewrite <- (fAg pc ltac:(lia)). change (cfail (ins p c pc r) r pc = true).
      rewrite (cfail_agree p W c pc r (rg cc) fAg). exact Hcf. }
    clear CF. rewrite Hvk.
    destruct (ins_agree p W c pc r (rg cc) fAg0) as (E1 & E2).
    rewrite (cfx_ext cc pc _ r (rg cc) _ (cexp_ieval _ _ _ E2)). rewrite E1. rewrite cfx_ok; [rewrite skf_cc; reflexivity|exact Hfx|].
    assert (Er' : eofR (ins p c pc (rg cc)) (rg cc) = eofR (crd Plain xs) (rg cc)) by (rewrite Er; reflexivity).
    destruct (eofR_half _ _ _ Er') as (_ & Xi). apply andb_prop in Xi as [_ Xi]. exact Xi.
  - rewrite (proj2 (Nat.ltb_ge j pc)), (proj2 (Nat.ltb_ge j (S pc))) by lia.
    destruct (is_load (ins p c j r) && icond (ins p c j r) r); [|reflexivity].
    rewrite skf_pa_gt by lia. destruct (pend_at p c cc' (S pc) (tp s' c) r j) as [n|] eqn:Pn; [rewrite skf_cc; reflexivity|].
    rewrite (cfx_fx cc cc' j) by (rewrite skf_cc; reflexivity). f_equal.
    rewrite skf_hpa_gt by lia. destruct (hpend_at p c cc' (S pc) (tp s' c) r j) as [n|] eqn:Ph; [rewrite fof_bit by first [lia|assumption|(rewrite pend_new_r; assumption)|(rewrite pend_new_old by auto; assumption)]; rewrite skf_cc; reflexivity|].
    cbv zeta. rewrite fof_bit by first [lia|assumption|(rewrite pend_new_r; assumption)|(rewrite pend_new_old by auto; assumption)]. erewrite map_ext_in; [reflexivity|]. intros x Ix. apply skf_cv; apply bitc_notin; exact Ix.
Qed.

End SkipFR.

Lemma INVP_skipf : INVP p s'.
Proof.
  intros c0 k d B f P. destruct (Nat.eq_dec c0 c) as [->|N0].
  2:{ assert (E : cs s' c0 = cs s c0) by (unfold sskip; simpl; apply upd_neq; auto).
      assert (E2 : pcs s' c0 = pcs s c0) by (unfold sskip; simpl; apply upd_neq; auto).
      assert (E3 : tp s' c0 = tp s c0) by (unfold sskip; simpl; apply upd_neq; auto).
      rewrite E, E2, E3 in *. apply (IP c0 k d B f P). }
  rewrite skf_pc in *. destruct P as (P1 & P2 & P3).
  destruct (oc cc' k) as [t|] eqn:Ot; [|congruence].
  assert (Pk' : pending cc' (S pc) k d) by (split; [exact P1|split; [congruence|exact P3]]).
  destruct (proj1 (skf_peq k d t) (conj Pk' Ot)) as (Po & Ot' & Lk).
  set (r := creg p c cc' (S pc) (tp s' c) (bor (bd cc') B) f).
  set (F := fof p c cc' (S pc) (tp s' c) (bor (bd cc') B) f r).
  assert (EQ : forall j, creg p c cc pc N (bor (bd cc) B) F j = r j).
  { apply creg_ext; [exact W|apply (pend_ok_of p s c I)|]. intros j. apply skf_pt. }
  destruct (IP c k d B F Po) as (j' & _ & t0 & O0 & Fj). rewrite Ot' in O0. injection O0 as <-.
  apply (first_at_ext p c cc pc _ r t d j' W EQ) in Fj.
  pose proof (fAg B f) as Ag. fold r in Ag. pose proof (fAg0 B f) as Ag0. fold r in Ag0.
  destruct (Nat.eq_dec j' pc) as [->|Nj].
  - exfalso. apply (skf_noplace r k d t Ag0 Po Ot' Fj).
  - exists j'. split; auto. exists t. split; auto. apply (skf_shift r Ag t k d j' Pk' Ot).
    + pose proof (first_at_le _ _ _ _ _ _ _ _ Fj). lia.
    + exact Fj.
Qed.

Lemma INVH_skipf : INVH p s'.
Proof.
  intros c0 k m xs0 B f P C. destruct (Nat.eq_dec c0 c) as [->|N0].
  2:{ assert (E : cs s' c0 = cs s c0) by (unfold sskip; simpl; apply upd_neq; auto).
      assert (E2 : pcs s' c0 = pcs s c0) by (unfold sskip; simpl; apply upd_neq; auto).
      assert (E3 : tp s' c0 = tp s c0) by (unfold sskip; simpl; apply upd_neq; auto).
      rewrite E, E2, E3 in *. apply (IPh c0 k m xs0 B f P C). }
  rewrite skf_pc in *.
  destruct (oh cc' k) as [t|] eqn:Ot; [|destruct P as (_ & P & _); congruence].
  destruct (proj1 (skf_peqh k m xs0 t) (conj P Ot)) as (Po & Ot' & Lk).
  assert (C0 : oc cc k = None) by (rewrite skf_cc in C; exact C).
  set (r := creg p c cc' (S pc) (tp s' c) (bor (bd cc') B) f).
  set (F := fof p c cc' (S pc) (tp s' c) (bor (bd cc') B) f r).
  assert (EQ : forall j, creg p c cc pc N (bor (bd cc) B) F j = r j).
  { apply creg_ext; [exact W|apply (pend_ok_of p s c I)|]. intros j. apply skf_pt. }
  destruct (IPh c k m xs0 B F Po C0) as (j' & _ & _ & t0 & O0 & Fj). rewrite Ot' in O0. injection O0 as <-.
  apply (first_atR_ext p c cc pc _ r t m xs0 j' W EQ) in Fj.
  pose proof (fAg B f) as Ag. fold r in Ag. pose proof (fAg0 B f) as Ag0. fold r in Ag0.
  destruct (Nat.eq_dec j' pc) as [->|Nj].
  - exfalso. apply (skf_noplaceh r k m xs0 t Ag0 Po ltac:(lia) Ot' Fj).
  - exists j'. split; [exact P|]. split; [exact C|]. exists t. split; auto. apply (skf_shiftR r Ag t k m xs0 j' P Ot).
    + pose proof (first_atR_le _ _ _ _ _ _ _ _ _ Fj). lia.
    + exact Fj.
Qed.

End SkipF.

(* ---------- reaching an early access ---------- *)
Section MatchP.
Variables (p : prog) (s : st) (c : nat) (d : desc).
Hypothesis W : wf p.
Hypothesis Wc : cellful p.
Hypothesis I : Inv1 p s.
Hypothesis J : Inv2 p s.
Hypothesis IP : INVP p s.
Hypothesis IPh : INVH p s.
Local Abbreviation cc := (cs s c).
Local Abbreviation pc := (pcs s c).
Hypothesis Ho : oc cc pc <> None.
Hypothesis Ha : ai cc pc = inst_of d.
Hypothesis Hdf : eof (ins p c pc (rg cc)) (rg cc) = Some d.
Hypothesis Hf : forall k' d' t t', pending cc pc k' d' -> k' <> pc -> oc cc pc = Some t -> oc cc k' = Some t' ->
  tied (inst_of d) (inst_of d') -> t < t'.
Hypothesis Hfh : forall k' m xs t t', hpending cc pc k' m xs -> k' <> pc -> oc cc pc = Some t -> oh cc k' = Some t' ->
  tied (inst_of d) (crd m xs) -> t < t'.
Local Abbreviation s' := (smatch p s c).
Hypothesis I' : Inv1 p s'.
Local Abbreviation N := (tp s c).
Definition ccm : cst := mkC (oc cc) (rg cc) (upd (ai cc) pc (ins p c pc (rg cc))) (rw cc) (rv cc) (bd cc) (vP cc) (vA cc) (vR cc) (vO cc) (vOg cc) (oh cc) (fx cc).
Local Abbreviation cc' := ccm.

Lemma ccm_eq : cs s' c = ccm.
Proof. unfold smatch, ccm; simpl. apply upd_eq. Qed.

Lemma match_pc : pcs s' c = S pc.
Proof. unfold smatch; simpl. apply upd_eq. Qed.

Lemma ccm_ai : forall j, ai cc' j = if Nat.eqb j pc then ins p c pc (rg cc) else ai cc j.
Proof. intros j. reflexivity. Qed.

Lemma pk_pending : pending cc pc pc d.
Proof. repeat split; auto. Qed.

Lemma tm_pc : exists te, oc cc pc = Some te.
Proof. destruct (oc cc pc) as [te|]; [eauto|congruence]. Qed.

(* the access reached has its place at pc *)
Lemma place_pc : forall r te, agree r (rg cc) pc -> oc cc pc = Some te -> first_at p c cc pc r te d pc.
Proof.
  intros r te Ag Ote. apply first_at_mk.
  - lia.
  - rewrite (eof_agree p W c pc r (rg cc) Ag). exact Hdf.
  - intros (k' & t' & d' & P' & O' & Lt & F). pose proof (first_at_eof _ _ _ _ _ _ _ _ F) as D.
    rewrite (eof_agree p W c pc r (rg cc) Ag), Hdf in D. injection D as <-.
    destruct (Nat.eq_dec k' pc) as [->|Nk]; [rewrite Ote in O'; injection O' as <-; lia|].
    pose proof (Hf k' d te t' P' Nk Ote O' (eof_tied_self p c pc (rg cc) d Wc Hdf)). lia.
  - intros (k' & t' & m' & xs' & P' & O' & Lt & Hl & F). pose proof (first_atR_eofR _ _ _ _ _ _ _ _ _ F) as D.
    destruct (eofR_exec_tied p c pc r m' xs' Wc D) as [_ T0].
    assert (Dr : eof (ins p c pc r) r = Some d) by (rewrite (eof_agree p W c pc r (rg cc) Ag); exact Hdf).
    apply (tied_eof_l _ _ _ _ Dr) in T0.
    destruct (Nat.eq_dec k' pc) as [->|Nk]; [specialize (Hl te Ote); lia|].
    pose proof (Hfh k' m' xs' te t' P' Nk Ote O' T0). lia.
  - intros j' L1 L2. lia.
Qed.

Lemma eof_eofR : forall i0 r m xs e n, eof i0 r = Some (DCas m xs e n) -> eofR i0 r = Some (m, xs).
Proof.
  intros [m0 x0 c0|m0 x0 c0 v0|m0 x0 c0 e0 n0|[]|] r m xs e n H; simpl in H; try discriminate.
  - destruct (c0 r); discriminate.
  - destruct (c0 r); discriminate.
  - simpl. destruct (c0 r); [injection H as -> -> _ _; reflexivity|discriminate].
Qed.

(* the CAS reached, if its read happened alone, has that read's place at pc *)
Lemma placeR_pc : forall r te t1 m xs, agree r (rg cc) pc -> oc cc pc = Some te -> oh cc pc = Some t1 ->
  hpending cc pc pc m xs -> first_atR p c cc pc r t1 m xs pc.
Proof.
  intros r te t1 m xs Ag Ote Oh (_ & _ & Cx). destruct (i_hoc p s I c pc t1 te Oh Ote) as [Lt1 _].
  rewrite Ha in Cx. destruct d as [| |m0 x0 e0 n0|]; simpl in Cx; try discriminate. injection Cx as <- <-.
  assert (Dr : eof (ins p c pc r) r = Some (DCas m0 x0 e0 n0)) by (rewrite (eof_agree p W c pc r (rg cc) Ag); exact Hdf).
  apply first_atR_mk; [lia|apply (eof_eofR _ _ _ _ _ _ Dr)| | |intros; lia].
  - intros (k' & t' & d' & P' & O' & Lt & F). pose proof (first_at_eof _ _ _ _ _ _ _ _ F) as D.
    rewrite Dr in D. injection D as <-.
    destruct (Nat.eq_dec k' pc) as [->|Nk]; [rewrite Ote in O'; injection O' as <-; lia|].
    pose proof (Hf k' (DCas m0 x0 e0 n0) te t' P' Nk Ote O' (eof_tied_self p c pc (rg cc) _ Wc Hdf)). lia.
  - intros (k' & t' & m' & xs' & P' & O' & Lt & Hl & F). pose proof (first_atR_eofR _ _ _ _ _ _ _ _ _ F) as D.
    destruct (eofR_exec_tied p c pc r m' xs' Wc D) as [_ T0]. apply (tied_eof_l _ _ _ _ Dr) in T0.
    destruct (Nat.eq_dec k' pc) as [->|Nk]; [rewrite Oh in O'; injection O' as <-; lia|].
    pose proof (Hfh k' m' xs' te t' P' Nk Ote O' T0). lia.
Qed.

Lemma match_peq : forall k d0 t, (pending cc' (S pc) k d0 /\ oc cc' k = Some t) <->
  (pending cc pc k d0 /\ oc cc k = Some t /\ pc < k).
Proof.
  intros k d0 t. unfold pending. cbn [oc ai ccm]. unfold upd. split.
  - intros ((P1 & P2 & P3) & O). destruct (Nat.eqb_spec k pc); [lia|]. repeat split; auto; lia.
  - intros ((P1 & P2 & P3) & O & L). destruct (Nat.eqb_spec k pc); [lia|]. repeat split; auto; lia.
Qed.

Lemma match_peqh : forall k m xs t, (hpending cc' (S pc) k m xs /\ oh cc' k = Some t) <->
  (hpending cc pc k m xs /\ oh cc k = Some t /\ pc < k).
Proof.
  intros k m xs t. unfold hpending. cbn [oh ai ccm]. unfold upd. split.
  - intros ((P1 & P2 & P3) & O). destruct (Nat.eqb_spec k pc); [lia|]. repeat split; auto; lia.
  - intros ((P1 & P2 & P3) & O & L). destruct (Nat.eqb_spec k pc); [lia|]. repeat split; auto; lia.
Qed.

Lemma match_oldh : forall r, agree r (rg cc) pc -> forall m xs t j, hpending cc pc pc m xs -> oh cc pc = Some t ->
  first_atR p c cc pc r t m xs j -> j = pc.
Proof.
  intros r Ag m xs t j P O F. destruct tm_pc as (te & Ote).
  apply (first_atR_unique p c cc pc r t m xs j pc Wc F). apply (placeR_pc r te); auto.
Qed.

Lemma match_blk : forall r, agree r (rg cc) pc -> forall k m xs t, hpending cc' (S pc) k m xs -> oh cc' k = Some t ->
  executes (ins p c pc r) r = true ->
  (forall v, htakenv p c cc pc r t pc v -> cfailv (ins p c pc r) r v = false) ->
  tied (ins p c pc r) (crd m xs) -> taken p c cc pc r t pc.
Proof.
  intros r Ag k m xs t P O Ex _ Ti. destruct (proj1 (match_peqh k m xs t) (conj P O)) as (Pk & Ok & Lk).
  destruct tm_pc as (te & Ote). exists pc, te, d. split; [apply pk_pending|]. split; [exact Ote|]. split.
  + apply (Hfh k m xs te t Pk ltac:(lia) Ote Ok). apply (proj1 (tied_eof_l _ _ _ _ Hdf)).
    rewrite <- (proj1 (ins_agree p W c pc r (rg cc) Ag)). exact Ti.
  + apply place_pc; auto.
Qed.

Lemma match_shift : forall r, agree r (rg cc) pc -> forall t k d0 j, pending cc' (S pc) k d0 -> oc cc' k = Some t -> S pc <= j ->
  (first_at p c cc pc r t d0 j <-> first_at p c cc' (S pc) r t d0 j).
Proof.
  intros r Ag. apply place_shift; [apply match_peq| | |apply match_peqh|intros; tauto|apply (match_oldh r Ag)|apply (match_blk r Ag)].
  - intros d0 t j P O F. destruct P as (_ & _ & P3). rewrite Ha in P3. apply inst_of_inj in P3. subst d0.
    apply (first_at_unique p c cc pc r t d j pc Wc F). apply place_pc; auto.
  - intros k d0 t P O Ex _ Ti. destruct (proj1 (match_peq k d0 t) (conj P O)) as (Pk & Ok & Lk).
    destruct tm_pc as (te & Ote). exists pc, te, d. split; [apply pk_pending|]. split; [exact Ote|]. split.
    + apply (Hf k d0 te t Pk ltac:(lia) Ote Ok). apply (proj1 (tied_eof_l _ _ _ _ Hdf)).
      rewrite <- (proj1 (ins_agree p W c pc r (rg cc) Ag)). exact Ti.
    + apply place_pc; auto.
Qed.

Lemma match_shiftR : forall r, agree r (rg cc) pc -> forall t k m xs j, hpending cc' (S pc) k m xs -> oh cc' k = Some t -> S pc <= j ->
  (first_atR p c cc pc r t m xs j <-> first_atR p c cc' (S pc) r t m xs j).
Proof.
  intros r Ag. apply place_shiftR; [apply match_peq| | |apply match_peqh|intros; tauto|apply (match_oldh r Ag)|apply (match_blk r Ag)].
  - intros d0 t j P O F. destruct P as (_ & _ & P3). rewrite Ha in P3. apply inst_of_inj in P3. subst d0.
    apply (first_at_unique p c cc pc r t d j pc Wc F). apply place_pc; auto.
  - intros k d0 t P O Ex _ Ti. destruct (proj1 (match_peq k d0 t) (conj P O)) as (Pk & Ok & Lk).
    destruct tm_pc as (te & Ote). exists pc, te, d. split; [apply pk_pending|]. split; [exact Ote|]. split.
    + apply (Hf k d0 te t Pk ltac:(lia) Ote Ok). apply (proj1 (tied_eof_l _ _ _ _ Hdf)).
      rewrite <- (proj1 (ins_agree p W c pc r (rg cc) Ag)). exact Ti.
    + apply place_pc; auto.
Qed.

(* the value recorded for the early access *)
Lemma rg_store : is_load (inst_of d) = false -> rg cc pc = 0.
Proof.
  intros L. destruct (oc cc pc) as [t|] eqn:O; [|congruence].
  destruct (i_oc p s I c pc t O) as (e & A & B & C).
  assert (Ei : einstr p s e = inst_of d) by (unfold einstr; rewrite B, C; exact Ha).
  destruct (j_val p s J t e _ A Ei) as [_ V]. unfold xload in V. rewrite L in V. simpl in V.
  unfold rgof in V. rewrite B, C in V. apply (proj1 (V eq_refl)).
Qed.

Lemma rv_store : is_load (inst_of d) = false -> forall x, rv cc pc x = 0.
Proof.
  intros L x. destruct (oc cc pc) as [t|] eqn:O; [|congruence].
  destruct (i_oc p s I c pc t O) as (e & A & B & C).
  assert (Ei : einstr p s e = inst_of d) by (unfold einstr; rewrite B, C; exact Ha).
  destruct (j_val p s J t e _ A Ei) as [_ V]. unfold xload in V. rewrite L in V. simpl in V.
  pose proof (j_rv p s J t e x A) as Rv. rewrite B, C in Rv. rewrite Rv. unfold rdv.
  rewrite (proj2 (V eq_refl) x). reflexivity.
Qed.

Section MatchR.
Variables (B : nat -> bool) (f : nat -> cell -> val).
Local Abbreviation r := (creg p c cc' (S pc) N (bor (bd cc) B) f).
Local Abbreviation F := (fof p c cc' (S pc) N (bor (bd cc) B) f r).

Lemma POm : pend_ok cc' (S pc).
Proof. rewrite <- ccm_eq, <- match_pc; apply (pend_ok_of p s' c I'). Qed.

Lemma Agm : agree r (rg cc) pc.
Proof. intros i0 Li. apply (creg_lt_pc p c cc' (S pc) N _ f i0 W POm). lia. Qed.

Lemma Drm : eof (ins p c pc r) r = Some d.
Proof. rewrite (eof_agree p W c pc r (rg cc) Agm); exact Hdf. Qed.

Lemma pam_gt : forall j, S pc <= j -> pend_at p c cc pc N r j = pend_at p c cc' (S pc) N r j.
Proof.
  intros j L. destruct tm_pc as (te & Ote).
  pose proof (pend_at_eq_s p s s' c c r j I I') as QE. rewrite ccm_eq, match_pc in QE. apply QE; [|reflexivity].
  intros k. split.
  - intros (d0 & Pk & t & O & F0). destruct (Nat.eq_dec k pc) as [->|Nk].
    + exfalso. rewrite Ote in O. injection O as <-. destruct Pk as (_ & _ & Pk). rewrite Ha in Pk. apply inst_of_inj in Pk. subst d0.
      pose proof (first_at_unique p c cc pc r te d j pc Wc F0 (place_pc r te Agm Ote)). lia.
    + assert (Q : pending cc' (S pc) k d0 /\ oc cc' k = Some t) by (apply match_peq; split; [exact Pk|split; [exact O|]]; destruct Pk as (? & _); lia).
      destruct Q as [Q1 Q2]. exists d0. split; auto. exists t. split; auto.
      apply (match_shift r Agm t k d0 j Q1 Q2 ltac:(lia)). exact F0.
  - intros (d0 & Pk & t & O & F0). destruct (proj1 (match_peq k d0 t) (conj Pk O)) as (Q1 & Q2 & Q3).
    exists d0. split; auto. exists t. split; auto. apply (match_shift r Agm t k d0 j Pk O ltac:(lia)). exact F0.
Qed.

Lemma hpam_gt : forall j, S pc <= j -> hpend_at p c cc pc N r j = hpend_at p c cc' (S pc) N r j.
Proof.
  intros j L. pose proof (hpend_at_eq_s p s s' c r j I I') as QE. rewrite ccm_eq, match_pc in QE. apply QE.
  intros k. split.
  - intros (m & xs & Pk & C & t & O & F0). destruct (Nat.eq_dec k pc) as [->|Nk]; [congruence|].
    assert (Lk : pc < k) by (destruct Pk as (? & _); lia).
    assert (Q : hpending cc' (S pc) k m xs /\ oh cc' k = Some t) by (apply match_peqh; auto).
    destruct Q as [Q1 Q2]. exists m, xs. split; [exact Q1|]. split; [exact C|].
    exists t. split; auto. apply (match_shiftR r Agm t k m xs j Q1 Q2 ltac:(lia)). exact F0.
  - intros (m & xs & Pk & C & t & O & F0). destruct (proj1 (match_peqh k m xs t) (conj Pk O)) as (Q1 & Q2 & Q3).
    exists m, xs. split; [exact Q1|]. split; [exact C|].
    exists t. split; auto. apply (match_shiftR r Agm t k m xs j Pk O ltac:(lia)). exact F0.
Qed.

Lemma pam_pc : is_load (inst_of d) = true -> pend_at p c cc pc N r pc = Some pc.
Proof.
  intros Ld. destruct tm_pc as (te & Ote). apply (pend_at_char_s p s c I). exists d. split; [apply pk_pending|].
  exists te. split; auto. apply place_pc; auto. apply Agm.
Qed.

Lemma match_cv : forall n b x,
  x <> bitc (ins p c b r) ->
  cellv p c cc pc N (bor (bd cc) B) F r n b x = cellv p c cc' (S pc) N (bor (bd cc) B) f r b b x.
Proof.
  intros n. induction n as [|n IH]; intros b x Hbx.
  all: destruct (Nat.lt_trichotomy b pc) as [L|[L|L]];
    [rewrite cellv_lt by auto; rewrite cellv_lt by lia; reflexivity| |].
  1,3: subst b; rewrite (cellv_lt _ _ cc' (S pc)) by lia; cbn [rv ccm];
       pose proof (eof_load _ _ _ Drm) as EL;
       destruct (is_load (inst_of d)) eqn:Ld;
       [rewrite (cellv_pd _ _ cc pc N _ _ _ _ _ _ pc) by (auto; apply pam_pc; auto); reflexivity
       |rewrite cellv_nl by auto; symmetry; apply rv_store; auto].
  all: destruct (is_load (ins p c b r) && icond (ins p c b r) r) eqn:X;
         [|rewrite cellv_nl by (auto; lia); rewrite cellv_nl by (auto; lia); reflexivity].
  all: destruct (pend_at p c cc' (S pc) N r b) as [n0|] eqn:P.
  all: try (rewrite (cellv_pd _ _ cc pc N _ _ _ _ _ _ n0) by (auto; try lia; rewrite pam_gt by lia; exact P);
            rewrite (cellv_pd _ _ cc' (S pc)) with (k := n0) by (auto; lia); reflexivity).
  all: destruct (hpend_at p c cc' (S pc) N r b) as [n0|] eqn:Ph.
  all: try (rewrite (cellv_hpd _ _ cc pc N _ _ _ _ _ _ n0) by first [lia|assumption|(rewrite pam_gt by lia; exact P)|(rewrite hpam_gt by lia; exact Ph)];
            rewrite (cellv_hpd _ _ cc' (S pc)) with (k := n0) by (auto; lia); reflexivity).
  - rewrite cellv_free by first [lia|assumption|(rewrite pam_gt by lia; exact P)|(rewrite hpam_gt by lia; exact Ph)]. unfold fof; rewrite (proj2 (Nat.eqb_neq _ _) Hbx). reflexivity.
  - rewrite cellv_go by first [lia|assumption|(rewrite pam_gt by lia; exact P)|(rewrite hpam_gt by lia; exact Ph)].
    destruct (bor (bd cc) B b) eqn:Bb; [|unfold fof; rewrite (proj2 (Nat.eqb_neq _ _) Hbx); reflexivity].
    destruct (fbinder p c r b x) as [b0|] eqn:Fb; [|unfold fof; rewrite (proj2 (Nat.eqb_neq _ _) Hbx); reflexivity].
    destruct b as [|b']; [lia|].
    rewrite (cellv_go _ _ cc' (S pc) _ _ f r b') by (auto; lia). rewrite Bb, Fb.
    pose proof (fbinder_lt _ _ _ _ _ _ Fb). f_equal. rewrite IH; try (apply bitc_notin; apply (fbinder_shape _ _ _ _ _ _ Fb)). symmetry. apply cellv_fuel. lia.
Qed.

Lemma match_pt : forall j, slotv p c cc pc N (bor (bd cc) B) F r j = r j.
Proof.
  intros j.
  assert (Rfix : r j = slotv p c cc' (S pc) N (bor (bd cc) B) f r j) by (apply creg_fix; auto; apply POm).
  rewrite Rfix. unfold slotv.
  destruct (Nat.lt_trichotomy j pc) as [L|[L|L]].
  - rewrite (proj2 (Nat.ltb_lt j pc) L), (proj2 (Nat.ltb_lt j (S pc))) by lia. reflexivity.
  - subst j. rewrite Nat.ltb_irrefl, (proj2 (Nat.ltb_lt pc (S pc))) by lia. cbn [rg ccm].
    rewrite (eof_load _ _ _ Drm).
    destruct (is_load (inst_of d)) eqn:Ld.
    + rewrite pam_pc by auto. reflexivity.
    + symmetry. apply rg_store. auto.
  - rewrite (proj2 (Nat.ltb_ge j pc)), (proj2 (Nat.ltb_ge j (S pc))) by lia.
    destruct (is_load (ins p c j r) && icond (ins p c j r) r); [|reflexivity].
    rewrite pam_gt by lia. destruct (pend_at p c cc' (S pc) N r j) as [n|] eqn:Pn; [reflexivity|].
    rewrite hpam_gt by lia. destruct (hpend_at p c cc' (S pc) N r j) as [n|] eqn:Ph; [rewrite fof_bit by first [lia|assumption|(rewrite pend_new_r; assumption)|(rewrite pend_new_old by auto; assumption)]; reflexivity|].
    cbv zeta. rewrite fof_bit by first [lia|assumption|(rewrite pend_new_r; assumption)|(rewrite pend_new_old by auto; assumption)]. erewrite map_ext_in; [reflexivity|]. intros x Ix. apply match_cv. apply bitc_notin. exact Ix.
Qed.

End MatchR.

Lemma INVP_match : INVP p s'.
Proof.
  intros c0 k d0 B f P. destruct (Nat.eq_dec c0 c) as [->|N0].
  2:{ assert (E : cs s' c0 = cs s c0) by (unfold smatch; simpl; apply upd_neq; auto).
      assert (E2 : pcs s' c0 = pcs s c0) by (unfold smatch; simpl; apply upd_neq; auto).
      assert (E3 : tp s' c0 = tp s c0) by reflexivity.
      rewrite E, E2, E3 in *. apply (IP c0 k d0 B f P). }
  assert (Tp : tp s' c = N) by reflexivity.
  rewrite match_pc, Tp, ccm_eq in *.
  destruct (oc cc' k) as [t|] eqn:Ot; [|destruct P as (_ & P & _); congruence].
  destruct (proj1 (match_peq k d0 t) (conj P Ot)) as (Po & Ot' & Lk).
  set (r := creg p c cc' (S pc) N (bor (bd cc) B) f).
  set (F := fof p c cc' (S pc) N (bor (bd cc) B) f r).
  assert (EQ : forall j, creg p c cc pc N (bor (bd cc) B) F j = r j).
  { apply creg_ext; [exact W|apply (pend_ok_of p s c I)|]. intros j. apply match_pt. }
  destruct (IP c k d0 B F Po) as (j' & _ & t0 & O0 & Fj). rewrite Ot' in O0. injection O0 as <-.
  apply (first_at_ext p c cc pc _ r t d0 j' W EQ) in Fj.
  assert (PO' : pend_ok cc' (S pc)) by (rewrite <- ccm_eq, <- match_pc; apply (pend_ok_of p s' c I')).
  assert (Ag : agree r (rg cc) pc).
  { intros i0 Li. unfold r. apply (creg_lt_pc p c cc' (S pc) N _ f i0 W PO'). lia. }
  destruct tm_pc as (te & Ote).
  destruct (Nat.eq_dec j' pc) as [->|Nj].
  - exfalso. pose proof (first_at_eof _ _ _ _ _ _ _ _ Fj) as F2.
    rewrite (eof_agree p W c pc r (rg cc) Ag), Hdf in F2. injection F2 as <-.
    apply (first_at_free _ _ _ _ _ _ _ _ Fj). exists pc, te, d. split; [apply pk_pending|]. split; [exact Ote|]. split.
    + apply (Hf k d te t Po ltac:(lia) Ote Ot'). apply (eof_tied_self p c pc (rg cc) d Wc Hdf).
    + apply place_pc; auto.
  - exists j'. split; auto. exists t. split; auto. apply (match_shift r Ag t k d0 j' P Ot).
    + pose proof (first_at_le _ _ _ _ _ _ _ _ Fj). lia.
    + exact Fj.
Qed.

Lemma INVH_match : INVH p s'.
Proof.
  intros c0 k m xs B f P C. destruct (Nat.eq_dec c0 c) as [->|N0].
  2:{ assert (E : cs s' c0 = cs s c0) by (unfold smatch; simpl; apply upd_neq; auto).
      assert (E2 : pcs s' c0 = pcs s c0) by (unfold smatch; simpl; apply upd_neq; auto).
      assert (E3 : tp s' c0 = tp s c0) by reflexivity.
      rewrite E, E2, E3 in *. apply (IPh c0 k m xs B f P C). }
  assert (Tp : tp s' c = N) by reflexivity.
  rewrite match_pc, Tp, ccm_eq in *.
  destruct (oh cc' k) as [t|] eqn:Ot; [|destruct P as (_ & P & _); congruence].
  destruct (proj1 (match_peqh k m xs t) (conj P Ot)) as (Po & Ot' & Lk).
  set (r := creg p c cc' (S pc) N (bor (bd cc) B) f).
  set (F := fof p c cc' (S pc) N (bor (bd cc) B) f r).
  assert (EQ : forall j, creg p c cc pc N (bor (bd cc) B) F j = r j).
  { apply creg_ext; [exact W|apply (pend_ok_of p s c I)|]. intros j. apply match_pt. }
  destruct (IPh c k m xs B F Po C) as (j' & _ & _ & t0 & O0 & Fj). rewrite Ot' in O0. injection O0 as <-.
  apply (first_atR_ext p c cc pc _ r t m xs j' W EQ) in Fj.
  assert (PO' : pend_ok cc' (S pc)) by (rewrite <- ccm_eq, <- match_pc; apply (pend_ok_of p s' c I')).
  assert (Ag : agree r (rg cc) pc).
  { intros i0 Li. unfold r. apply (creg_lt_pc p c cc' (S pc) N _ f i0 W PO'). lia. }
  destruct tm_pc as (te & Ote).
  destruct (Nat.eq_dec j' pc) as [->|Nj].
  - exfalso. apply (first_atR_free _ _ _ _ _ _ _ _ _ Fj).
    pose proof (first_atR_eofR _ _ _ _ _ _ _ _ _ Fj) as D.
    destruct (eofR_exec_tied p c pc r m xs Wc D) as [_ T0].
    assert (Dr : eof (ins p c pc r) r = Some d) by (rewrite (eof_agree p W c pc r (rg cc) Ag); exact Hdf).
    apply (tied_eof_l _ _ _ _ Dr) in T0.
    exists pc, te, d. split; [apply pk_pending|]. split; [exact Ote|]. split.
    + apply (Hfh k m xs te t Po ltac:(lia) Ote Ot' T0).
    + apply place_pc; auto.
  - exists j'. split; [exact P|]. split; [exact C|]. exists t. split; auto. apply (match_shiftR r Ag t k m xs j' P Ot).
    + pose proof (first_atR_le _ _ _ _ _ _ _ _ _ Fj). lia.
    + exact Fj.
Qed.

End MatchP.

(* ---------- the leader of a read counted on (change C) ---------- *)
Lemma lead_agree : forall p c cc pc N r r' b, wf p -> pend_ok cc pc -> agree r r' b ->
  lead p c cc pc N r b = lead p c cc pc N r' b.
Proof.
  intros p c cc pc N r r' b W PO A. unfold lead.
  rewrite (pend_at_agree p W c cc pc N r r' b PO A), (hpend_at_agree p W c cc pc N r r' b PO A). reflexivity.
Qed.

(* the value R1 gives the leader's cell, seen through the binder value *)
Lemma cellv_lead : forall p c cc pc N Bo F r n b x k', lead p c cc pc N r b = Some k' ->
  executes (ins p c b r) r = true -> In x (icells (ins p c b r)) ->
  bvx p c r b x (cellv p c cc pc N Bo F r n b x) = bvx p c r b x (rv cc k' x).
Proof.
  intros p c cc pc N Bo F r n b x k' Lk Ex Ix. unfold lead in Lk.
  destruct (Nat.ltb_spec b pc) as [L|L].
  - injection Lk as <-. rewrite cellv_lt by exact L. reflexivity.
  - destruct (is_load (ins p c b r) && icond (ins p c b r) r) eqn:X.
    + destruct (pend_at p c cc pc N r b) as [k1|] eqn:Pa.
      * injection Lk as <-. rewrite (cellv_pd p c cc pc N Bo F r n b x k1 L X Pa). reflexivity.
      * rewrite (cellv_hpd p c cc pc N Bo F r n b x k' L X Pa Lk). reflexivity.
    + unfold bvx. unfold executes in Ex.
      destruct (ins p c b r) as [m ys cb|m ys cb v|m ys cb e nv| |]; simpl in X, Ex, Ix |- *;
        try reflexivity; try (destruct Ix; fail); unfold icond, ieval in X, Ex; simpl in X, Ex; congruence.
Qed.

(* the leader's write: what the read takes *)
Lemma lead_bvx : forall p s c Bx g b x k' T, wf p -> Inv1 p s -> Inv2 p s ->
  let cc := cs s c in let R := creg p c cc (pcs s c) (tp s c) Bx g in
  executes (ins p c b R) R = true -> In x (icells (ins p c b R)) ->
  lead p c cc (pcs s c) (tp s c) R b = Some k' ->
  (pcs s c <= b -> pend_at p c cc (pcs s c) (tp s c) R b = None ->
     cfailv (ins p c b R) R (R b) = false -> taken p c cc (pcs s c) R T b) ->
  bvx p c R b x (rv cc k' x) = rdo s (rw cc k' x) x.
Proof.
  intros p s c Bx g b x k' T W I J cc R Ex Ix Lk HB.
  assert (PO : pend_ok cc (pcs s c)) by apply (pend_ok_of p s c I).
  unfold lead in Lk. destruct (Nat.ltb_spec b (pcs s c)) as [Lb|Lb].
  - injection Lk as <-.
    assert (Ap : agree R (rg cc) (pcs s c)) by (intros i0 L0; apply (creg_lt_pc p c cc (pcs s c) (tp s c) _ g i0 W PO L0)).
    assert (Ab : agree R (rg cc) b) by (apply (agree_le _ _ (pcs s c)); auto; lia).
    rewrite (bvx_agree p W c R (rg cc) b (pcs s c) x _ Lb Ap).
    apply (bind_val p s c b x W I J Lb).
    + rewrite (exec_agree p W c b R (rg cc) Ab) in Ex. exact Ex.
    + rewrite (proj1 (ins_agree p W c b R (rg cc) Ab)) in Ix. exact Ix.
  - assert (Rb : R b = slotv p c cc (pcs s c) (tp s c) Bx g R b) by (apply (creg_fix p W c cc (pcs s c) (tp s c) Bx g b PO)).
    unfold slotv in Rb. rewrite (proj2 (Nat.ltb_ge _ _) Lb) in Rb.
    destruct (pend_at p c cc (pcs s c) (tp s c) R b) as [k1|] eqn:Pa.
    + injection Lk as <-. pose proof Pa as Pa'. apply (pend_at_char_s p s c I) in Pa'.
      destruct Pa' as (d' & (_ & Oc & Ad) & t & O & Fb). pose proof (first_at_eof _ _ _ _ _ _ _ _ Fb) as E.
      apply (pend_bvx p s c b x k1 d' R I J Oc Ad E).
      * intros Ci. rewrite Rb. replace (is_load (ins p c b R) && icond (ins p c b R) R) with true; [reflexivity|].
        destruct d' as [| |m' xs' e' n'|]; simpl in Ci; try discriminate.
        destruct (ins p c b R) as [m0 x0 c0|m0 x0 c0 v0|m0 x0 c0 e0 n0|[]|]; simpl in E; try discriminate;
          destruct (c0 R) eqn:C0; try discriminate.
        unfold icond, ieval. simpl. rewrite C0. reflexivity.
      * rewrite <- (eof_icells _ _ _ E). exact Ix.
    + pose proof Lk as Lk'. apply (hpend_at_char_s p s c I) in Lk'. destruct Lk' as (m0 & xs0 & _ & C & t & O & Fr).
      pose proof (first_atR_eofR _ _ _ _ _ _ _ _ _ Fr) as Er.
      destruct (ins p c b R) as [| |m1 x1 c1 e1 n1| |] eqn:Ei; simpl in Er; try discriminate.
      destruct (c1 R) eqn:C1; [|discriminate].
      assert (Xb : is_load (ICas m1 x1 c1 e1 n1) && icond (ICas m1 x1 c1 e1 n1) R = true) by (unfold icond, ieval; simpl; rewrite C1; reflexivity).
      rewrite Xb, Lk in Rb. cbv iota in Rb.
      assert (Vf : vok (R b) = false).
      { destruct (vok (R b)) eqn:Vr; [|reflexivity]. exfalso.
        assert (Tk : taken p c cc (pcs s c) R T b).
        { apply HB; [exact Lb|reflexivity|]. rewrite Rb in Vr |- *. apply cfx_cfail; [|exact Vr]. apply hp_cfail. }
        destruct Tk as (k2 & t2 & d2 & Pk2 & O2 & _ & F2).
        assert (pend_at p c cc (pcs s c) (tp s c) R b = Some k2) by (apply (pend_at_char_s p s c I); exists d2; split; [exact Pk2|exists t2; auto]).
        congruence. }
      unfold bvx. rewrite Ei, Vf.
      destruct (half_vals p s c k' t I J C O) as (Rv & _). rewrite Rv. reflexivity.
Qed.

Lemma lead_read : forall p s c Bx g j T d x b k', wf p -> Inv1 p s -> Inv2 p s ->
  let R := creg p c (cs s c) (pcs s c) (tp s c) Bx g in
  first_at p c (cs s c) (pcs s c) R T d j -> fbinder p c R j x = Some b ->
  lead p c (cs s c) (pcs s c) (tp s c) R b = Some k' ->
  bvx p c R b x (rv (cs s c) k' x) = rdo s (rw (cs s c) k' x) x.
Proof.
  intros p s c Bx g j T d x b k' W I J R F Fb Lk.
  pose proof (fbinder_shape _ _ _ _ _ _ Fb) as (Exb & Ixb & Tb & _).
  pose proof (fbinder_lt _ _ _ _ _ _ Fb) as Lbj.
  apply (lead_bvx p s c Bx g b x k' T W I J Exb Ixb Lk).
  intros Lb _ Cf. apply (first_at_before _ _ _ _ _ _ _ _ F b Lb Lbj Exb).
  - intros v (k0 & t0 & m0 & xs0 & _ & _ & _ & _ & _ & ->). exact Cf.
  - apply (proj1 (tied_eof_r _ _ _ _ (first_at_eof _ _ _ _ _ _ _ _ F))). exact Tb.
Qed.

Lemma lead_readR : forall p s c Bx g j T m xs x b k', wf p -> Inv1 p s -> Inv2 p s ->
  let R := creg p c (cs s c) (pcs s c) (tp s c) Bx g in
  first_atR p c (cs s c) (pcs s c) R T m xs j -> fbinder p c R j x = Some b ->
  lead p c (cs s c) (pcs s c) (tp s c) R b = Some k' ->
  bvx p c R b x (rv (cs s c) k' x) = rdo s (rw (cs s c) k' x) x.
Proof.
  intros p s c Bx g j T m xs x b k' W I J R F Fb Lk.
  pose proof (fbinder_shape _ _ _ _ _ _ Fb) as (Exb & Ixb & Tb & _).
  pose proof (fbinder_lt _ _ _ _ _ _ Fb) as Lbj.
  apply (lead_bvx p s c Bx g b x k' T W I J Exb Ixb Lk).
  intros Lb _ Cf. apply (first_atR_before _ _ _ _ _ _ _ _ _ F b Lb Lbj Exb).
  - intros v (k0 & t0 & m0 & xs0 & _ & _ & _ & _ & _ & ->). exact Cf.
  - apply (proj1 (tied_crd _ _ _ _ _ (first_atR_eofR _ _ _ _ _ _ _ _ _ F))). exact Tb.
Qed.

(* ---------- an early access ---------- *)
Section EarlyP.
Variables (p : prog) (s : st) (c k : nat) (d : desc) (B2 : nat -> bool) (m' : mst) (a : val) (K : view)
          (u : cell -> option nat) (w : bool).
Hypothesis W : wf p.
Hypothesis Wc : cellful p.
Hypothesis I : Inv1 p s.
Hypothesis J : Inv2 p s.
Hypothesis IP : INVP p s.
Hypothesis IPh : INVH p s.
Local Abbreviation cc := (cs s c).
Local Abbreviation pc := (pcs s c).
Local Abbreviation N := (tp s c).
Local Abbreviation T := (tm s).
Hypothesis Hk : pc < k.
Hypothesis Ho : oc cc k = None.
Hypothesis Hoh : oh cc k = None.
Hypothesis Hok : early_ok p c cc pc N T d u B2.
Hypothesis He : eff (tm s) (inst_of d) (rg cc) (mof s c) m' a K u w.
Hypothesis Hvo : oh cc k <> None -> vok (rg cc k) = true.
Hypothesis Hwt : oh cc k <> None -> w = true.
Hypothesis Hfx : forall f j, first_at p c cc pc (creg p c cc pc N (bor (bd cc) B2) f) T d j -> fxok cc j (inst_of d) (rg cc) a.
Local Abbreviation s' := (searly s c k d B2 m' a K u w).
Hypothesis I' : Inv1 p s'.
Definition cce : cst := mkC (upd (oc cc) k (Some (tm s))) (upd (rg cc) k a) (upd (ai cc) k (inst_of d))
  (upd (rw cc) k (wrote (tm s) (icells (inst_of d)) u w)) (upd (rv cc) k (rdval (mof s c) u))
  (bor (bd cc) B2) (mP m') (mA m') (mR m')
  (newO s c (inst_of d) (mof s c) m' (vO cc)) (newOg (inst_of d) m' (vOg cc)) (oh cc) (fx cc).
Local Abbreviation N' := (Nat.max N (S k)).

Lemma cce_eq : cs s' c = cce.
Proof. unfold searly, set_es, searly0, evs, cce; simpl. apply upd_eq. Qed.

Lemma early_pc : pcs s' c = pc.
Proof. reflexivity. Qed.

Lemma early_tp : tp s' c = N'.
Proof. unfold searly, set_es, searly0, evs; simpl. apply upd_eq. Qed.

Lemma pend_ok_e : pend_ok cce pc.
Proof. rewrite <- cce_eq, <- early_pc. apply (pend_ok_of p s' c I'). Qed.

(* the accesses that happened before T have the same places with the new
   one recorded *)
Lemma early_same_g : forall r t g j, t <= T -> (plc p c cc pc r (S t) t g j <-> plc p c cce pc r (S t) t g j).
Proof.
  intros r t. induction t as [t IH] using lt_wf_ind. intros g j Lt. rewrite !plc_in. apply first_in_iff.
  intros j' _.
  assert (TK : taken p c cc pc r t j' <-> taken p c cce pc r t j').
  { unfold taken. split.
    - intros (k' & t' & d' & (P1 & P2 & P3) & O & L & F). assert (Nk : k' <> k) by congruence.
      exists k', t', d'. unfold pending. cbn [oc ai cce]. unfold upd.
      destruct (Nat.eqb_spec k' k); [congruence|]. split; [split; [exact P1|split; [exact P2|exact P3]]|].
      split; [exact O|]. split; [exact L|]. apply (IH t' L); [lia|exact F].
    - intros (k' & t' & d' & (P1 & P2 & P3) & O & L & F). cbn [oc ai cce] in P2, P3, O. unfold upd in P2, P3, O.
      destruct (Nat.eqb_spec k' k).
      + injection O as <-. lia.
      + exists k', t', d'. split; [split; [exact P1|split; [exact P2|exact P3]]|].
        split; [exact O|]. split; [exact L|]. apply (IH t' L); [lia|exact F]. }
  assert (THK : htaken p c cc pc r t j' <-> htaken p c cce pc r t j').
  { unfold htaken, hpending, hlive. split.
    - intros (k' & t' & m0 & xs0 & (P1 & P2 & P3) & O & L & Hl & F). assert (Nk : k' <> k) by congruence.
      exists k', t', m0, xs0. cbn [oc oh ai cce]. unfold upd.
      destruct (Nat.eqb_spec k' k); [congruence|]. split; [split; [exact P1|split; [exact P2|exact P3]]|].
      split; [exact O|]. split; [exact L|]. split; [exact Hl|]. apply (IH t' L); [lia|exact F].
    - intros (k' & t' & m0 & xs0 & (P1 & P2 & P3) & O & L & Hl & F). cbn [oc oh ai cce] in P2, P3, O, Hl. unfold upd in P3, Hl.
      destruct (Nat.eqb_spec k' k); [subst; congruence|].
      exists k', t', m0, xs0. split; [split; [exact P1|split; [exact P2|exact P3]]|].
      split; [exact O|]. split; [exact L|]. split; [exact Hl|]. apply (IH t' L); [lia|exact F]. }
  assert (RGX : forall k', oh cc k' <> None -> rg cce k' = rg cc k')
    by (intros k' N; cbn [rg cce]; unfold upd; destruct (Nat.eqb_spec k' k); [subst; congruence|reflexivity]).
  assert (THV : forall v, htakenv p c cc pc r t j' v <-> htakenv p c cce pc r t j' v).
  { intros v. unfold htakenv, hpending, hlive. split.
    - intros (k' & t' & m0 & xs0 & (P1 & P2 & P3) & O & L & Hl & F & Ev). assert (Nk : k' <> k) by congruence.
      exists k', t', m0, xs0. cbn [oc oh ai cce]. unfold upd.
      destruct (Nat.eqb_spec k' k); [congruence|]. split; [split; [exact P1|split; [exact P2|exact P3]]|].
      split; [exact O|]. split; [exact L|]. split; [exact Hl|]. split; [apply (IH t' L); [lia|exact F]|exact Ev].
    - intros (k' & t' & m0 & xs0 & (P1 & P2 & P3) & O & L & Hl & F & Ev). cbn [oc oh ai cce] in P2, P3, O, Hl. unfold upd in P3, Hl.
      destruct (Nat.eqb_spec k' k); [subst; congruence|].
      exists k', t', m0, xs0. split; [split; [exact P1|split; [exact P2|exact P3]]|].
      split; [exact O|]. split; [exact L|]. split; [exact Hl|]. split; [apply (IH t' L); [lia|exact F]|exact Ev]. }

  split; [exact TK|]. split; [rewrite TK, THK; tauto|exact THV].
Qed.

Lemma early_same : forall r t d0 j, t <= T -> (first_at p c cc pc r t d0 j <-> first_at p c cce pc r t d0 j).
Proof. intros. apply early_same_g; auto. Qed.

Lemma early_sameR : forall r t m xs j, t <= T -> (first_atR p c cc pc r t m xs j <-> first_atR p c cce pc r t m xs j).
Proof. intros. apply early_same_g; auto. Qed.

Lemma early_old_lt : forall k0 t0, oc cc k0 = Some t0 -> t0 < T.
Proof. intros k0 t0 O. apply (oc_lt_tm p s c k0 t0 I O). Qed.

(* the new access's place is no old pending access's place *)
Lemma old_not_there : forall r j n, pend_at p c cc pc N r j = Some n -> ~ first_at p c cc pc r T d j.
Proof.
  intros r j n Pa F. apply (pend_at_char_s p s c I) in Pa. destruct Pa as (d' & Pk & t & O & Fn).
  apply (first_at_free _ _ _ _ _ _ _ _ F). exists n, t, d'. split; [exact Pk|]. split; [exact O|].
  split; [apply (early_old_lt n t O)|exact Fn].
Qed.

Lemma placed_e : forall r j n d0, placed p c cce pc r n d0 j <->
  (n = k /\ d0 = d /\ first_at p c cc pc r T d j) \/ (n <> k /\ placed p c cc pc r n d0 j).
Proof.
  intros r j n d0. unfold placed, pending. cbn [oc ai cce]. unfold upd. destruct (Nat.eqb_spec n k) as [->|Nk].
  - split.
    + intros ((P1 & P2 & P3) & t & O & F). injection O as <-. apply inst_of_inj in P3. subst d0. left.
      split; [reflexivity|]. split; [reflexivity|]. apply (early_same r T d j (le_n _)). exact F.
    + intros [(_ & -> & F)|(Nk & _)]; [|congruence]. split; [split; [lia|split; [discriminate|reflexivity]]|].
      exists T. split; [reflexivity|]. apply (early_same r T d j (le_n _)). exact F.
  - split.
    + intros ((P1 & P2 & P3) & t & O & F). right. split; [exact Nk|]. split; [split; [exact P1|split; [exact P2|exact P3]]|].
      exists t. split; [exact O|]. apply (early_same r t d0 j); [pose proof (early_old_lt n t O) as X; lia|exact F].
    + intros [(E & _)|(_ & (P1 & P2 & P3) & t & O & F)]; [congruence|]. split; [split; [exact P1|split; [exact P2|exact P3]]|].
      exists t. split; [exact O|]. apply (early_same r t d0 j); [pose proof (early_old_lt n t O); lia|exact F].
Qed.

Lemma pend_new_k : forall r j, first_at p c cc pc r T d j -> pend_at p c cce pc N' r j = Some k.
Proof.
  intros r j F. rewrite <- cce_eq, <- early_tp. change pc with (pcs s' c).
  apply (pend_at_char_s p s' c I'). exists d. rewrite cce_eq. apply placed_e. left. auto.
Qed.

Lemma pend_new_old : forall r j, ~ first_at p c cc pc r T d j ->
  pend_at p c cce pc N' r j = pend_at p c cc pc N r j.
Proof.
  intros r j F. rewrite <- cce_eq, <- early_tp. change pc with (pcs s' c). symmetry.
  apply (pend_at_eq_s p s s' c c r j I I'); [|reflexivity]. intros n. rewrite early_pc, cce_eq. split.
  - intros (d0 & Pl). exists d0. apply placed_e. right. split; auto. intros ->. destruct Pl as ((_ & Pl & _) & _). congruence.
  - intros (d0 & Pl). apply placed_e in Pl. destruct Pl as [(_ & _ & X)|(_ & X)]; [contradiction|eauto].
Qed.

Lemma hplaced_e : forall r j n m xs, hplaced p c cce pc r n m xs j <-> hplaced p c cc pc r n m xs j.
Proof.
  intros r j n m xs. unfold hplaced, hpending. cbn [oc oh ai cce]. unfold upd. destruct (Nat.eqb_spec n k) as [->|Nk].
  - split; intros ((_ & P2 & _) & _); congruence.
  - split; intros ((P1 & P2 & P3) & C & t & O & F); (split; [split; [exact P1|split; [exact P2|exact P3]]|]);
      (split; [exact C|]); exists t; (split; [exact O|]);
      (apply (early_sameR r t m xs j); [pose proof (oh_lt_tm p s c n t I O); lia|exact F]).
Qed.

Lemma hpend_new : forall r j, hpend_at p c cce pc N' r j = hpend_at p c cc pc N r j.
Proof.
  intros r j. rewrite <- cce_eq, <- early_tp. change pc with (pcs s' c). symmetry.
  apply (hpend_at_eq_s p s s' c r j I I'). intros n. rewrite early_pc, cce_eq.
  split; intros (m & xs & Pl); exists m, xs; apply hplaced_e; exact Pl.
Qed.

Lemma hpend_ne_k : forall r j n, hpend_at p c cc pc N r j = Some n -> n <> k.
Proof.
  intros r j n H ->. apply (hpend_at_char_s p s c I) in H. destruct H as (m & xs & (_ & P2 & _) & _). congruence.
Qed.

(* the new access's place is no CAS's read's place *)
Lemma hold_not_there : forall r j n, hpend_at p c cc pc N r j = Some n -> ~ first_at p c cc pc r T d j.
Proof.
  intros r j n Pa F. apply (hpend_at_char_s p s c I) in Pa. destruct Pa as (m & xs & Pk & C & t & O & Fn).
  apply (first_at_hfree _ _ _ _ _ _ _ _ F). exists n, t, m, xs. split; [exact Pk|]. split; [exact O|].
  split; [apply (oh_lt_tm p s c n t I O)|]. split; [intros t2 E; congruence|exact Fn].
Qed.

Lemma first_atb_e : forall r j, first_atb p c cc pc N r T d j = true <-> first_at p c cc pc r T d j.
Proof. intros r j. apply first_atb_iff; [apply (pend_ok_of p s c I)|apply (bn_of p s c I)|apply (bnh_of p s c I)]. Qed.

Local Abbreviation rnew := (fun (f : nat -> cell -> val) (B : nat -> bool) => creg p c cce pc N' (bor (bd cce) B) f).
Local Abbreviation Fn := (fun (f : nat -> cell -> val) (B : nat -> bool) =>
  fof p c cce pc N' (bor (bd cce) B) f (rnew f B)).
Local Abbreviation mid := (fun (g : nat -> cell -> val) => creg p c cc pc N (bor (bd cc) B2) g).

(* a place tied to the access is not passed over *)
Lemma first_place : forall r j, first_at p c cc pc r T d j -> forall i, pc <= i < j -> ~ first_at p c cc pc r T d i.
Proof.
  intros r j F i Li Fi. pose proof (first_at_unique p c cc pc r T d j i Wc F Fi). lia.
Qed.

Lemma rnew_lt_pc : forall f B i, i < pc -> rnew f B i = rg cc i.
Proof.
  intros f B i L. simpl. rewrite (creg_lt_pc p c cce pc N' _ f i W pend_ok_e L). simpl. unfold upd.
  destruct (Nat.eqb_spec i k); [lia|reflexivity].
Qed.

Lemma rv_cce : forall j, rv cce j = if Nat.eqb j k then rdval (mof s c) u else rv cc j.
Proof. intros j. reflexivity. Qed.

(* the value the new access read in cell x, through a binder R1 counted on *)
Lemma bound_new : forall g j x b, first_at p c cc pc (mid g) T d j -> In x (icells (inst_of d)) ->
  is_load (inst_of d) = true -> bor (bd cc) B2 j = true -> fbinder p c (mid g) j x = Some b ->
  exists k', lead p c cc pc N (mid g) b = Some k' /\ bvx p c (mid g) b x (rv cc k' x) = rdval (mof s c) u x.
Proof.
  intros g j x b F Ix Ld Bj Fb.
  destruct (Hok g) as (j2 & _ & G & FX). cbv zeta in FX. fold (mid g) in G, FX.
  assert (Ej : j2 = j) by (apply (first_at_unique p c cc pc (mid g) T d j2 j Wc G F)). subst j2.
  destruct (FX Ld x b Ix Bj Fb) as (k' & Lk & Ub). exists k'. split; [exact Lk|].
  pose proof (fbinder_shape _ _ _ _ _ _ Fb) as (Exb & Ixb & Tb & _).
  pose proof (fbinder_lt _ _ _ _ _ _ Fb) as Lbj.
  rewrite (lead_bvx p s c (bor (bd cc) B2) g b x k' T W I J Exb Ixb Lk).
  - rewrite <- Ub. reflexivity.
  - intros Lb _ Cf. apply (first_at_before _ _ _ _ _ _ _ _ F b Lb Lbj Exb).
    + intros v (k0 & t0 & m0 & xs0 & _ & _ & _ & _ & _ & ->). exact Cf.
    + apply (proj1 (tied_eof_r _ _ _ _ (first_at_eof _ _ _ _ _ _ _ _ F))). exact Tb.
Qed.

(* the registers after the step, read with the values R1 took after it as
   free values, are the registers before it (Bo: the reads counted on before
   the step, a subset of those after it), given the new access's place *)
Section Back.
Variables (B : nat -> bool) (f : nat -> cell -> val) (Bo : nat -> bool).
Local Abbreviation r := (rnew f B).
Local Abbreviation F := (Fn f B).
Hypothesis Bsub : forall j, Bo j = true -> bor (bd cce) B j = true.

Lemma back_cv : forall n b x,
  (forall j0 n0 x0, j0 <= b -> first_at p c cc pc r T d j0 -> x0 <> bitc (ins p c j0 r) ->
     cellv p c cc pc N Bo F r n0 j0 x0 = cellv p c cce pc N' (bor (bd cce) B) f r j0 j0 x0) ->
  x <> bitc (ins p c b r) ->
  cellv p c cc pc N Bo F r n b x = cellv p c cce pc N' (bor (bd cce) B) f r b b x.
Proof.
  intros n. induction n as [|n IH]; intros b x HP Hbx.
  all: destruct (first_atb p c cc pc N r T d b) eqn:FB; [apply HP; [lia|apply first_atb_e; exact FB|exact Hbx]|].
  all: assert (Nb : ~ first_at p c cc pc r T d b) by (intros X0; apply first_atb_e in X0; congruence).
  all: destruct (Nat.ltb_spec b pc) as [L|L];
    [rewrite cellv_lt by auto; rewrite cellv_lt by auto; rewrite rv_cce;
     destruct (Nat.eqb_spec b k); [lia|reflexivity]|].
  all: destruct (is_load (ins p c b r) && icond (ins p c b r) r) eqn:X;
         [|rewrite cellv_nl by auto; rewrite cellv_nl by auto; reflexivity].
  all: pose proof (pend_new_old r b Nb) as PE.
  all: destruct (pend_at p c cc pc N r b) as [n0|] eqn:P.
  all: try (rewrite (cellv_pd _ _ cc pc N _ _ _ _ _ _ n0) by auto;
            rewrite (cellv_pd _ _ cce pc N') with (k := n0) by (auto; rewrite PE; exact P); rewrite rv_cce;
            destruct (pend_at_spec _ _ _ _ _ _ _ _ P) as (On & _);
            destruct (Nat.eqb_spec n0 k); [subst; congruence|reflexivity]).
  all: pose proof (hpend_new r b) as PH.
  all: destruct (hpend_at p c cc pc N r b) as [n0|] eqn:Ph.
  all: try (rewrite (cellv_hpd _ _ cc pc N _ _ _ _ _ _ n0) by auto;
            rewrite (cellv_hpd _ _ cce pc N') with (k := n0) by first [assumption|lia|(rewrite PE; exact P)|(rewrite PH; exact Ph)];
            rewrite rv_cce; destruct (Nat.eqb_spec n0 k); [exfalso; apply (hpend_ne_k r b n0 Ph); auto|reflexivity]).
  - rewrite cellv_free by auto. unfold fof; rewrite (proj2 (Nat.eqb_neq _ _) Hbx). reflexivity.
  - rewrite cellv_go by auto.
    destruct (Bo b) eqn:Bb; [|unfold fof; rewrite (proj2 (Nat.eqb_neq _ _) Hbx); reflexivity].
    destruct (fbinder p c r b x) as [b0|] eqn:Fb; [|unfold fof; rewrite (proj2 (Nat.eqb_neq _ _) Hbx); reflexivity].
    destruct b as [|b']; [rewrite fbinder_0 in Fb; discriminate|].
    rewrite (cellv_go _ _ cce pc _ _ f r b') by first [assumption|lia|(rewrite PE; exact P)|(rewrite PH; exact Ph)]. rewrite (Bsub _ Bb), Fb.
    pose proof (fbinder_lt _ _ _ _ _ _ Fb). f_equal. rewrite IH; try (apply bitc_notin; apply (fbinder_shape _ _ _ _ _ _ Fb)).
    + symmetry. apply cellv_fuel. lia.
    + intros j0 n1 x1 L1 F1 X1. apply HP; [lia|exact F1|exact X1].
Qed.

End Back.

Lemma mid_agree : forall B f J0, (forall i, pc <= i < J0 -> ~ first_at p c cc pc (rnew f B) T d i) ->
  agree (mid (Fn f B)) (rnew f B) J0.
Proof.
  intros B f J0 Fx i. induction i as [i IH] using lt_wf_ind. intros Li. simpl.
  set (r := rnew f B) in *.
  assert (Nf : forall b, b < J0 -> ~ first_at p c cc pc r T d b).
  { intros b Lb Fb. destruct (Nat.ltb_spec b pc) as [L|L]; [pose proof (first_at_le _ _ _ _ _ _ _ _ Fb); lia|].
    apply (Fx b); auto. }
  rewrite (creg_fix p W c cc pc N _ _ i (pend_ok_of p s c I)).
  rewrite (slotv_agree p W c cc pc N _ _ _ r i (pend_ok_of p s c I)) by (intros i0 L0; apply IH; lia).
  transitivity (slotv p c cce pc N' (bor (bd cce) B) f r i); [|symmetry; apply creg_fix; auto; apply pend_ok_e].
  unfold slotv. destruct (Nat.ltb_spec i pc) as [L|L].
  - simpl. unfold upd. destruct (Nat.eqb_spec i k); [lia|reflexivity].
  - destruct (is_load (ins p c i r) && icond (ins p c i r) r) eqn:X; [|reflexivity].
    rewrite <- (pend_new_old r i (Nf i Li)).
    destruct (pend_at p c cce pc N' r i) as [n|] eqn:Pn.
    + simpl. unfold upd. destruct (Nat.eqb_spec n k); [|reflexivity]. subst n.
      exfalso. rewrite (pend_new_old r i (Nf i Li)) in Pn. destruct (pend_at_spec _ _ _ _ _ _ _ _ Pn) as (O1 & _). congruence.
    + rewrite hpend_new. destruct (hpend_at p c cc pc N r i) as [n|] eqn:Ph.
      { simpl. unfold upd. destruct (Nat.eqb_spec n k); [|try rewrite fof_bit by first [lia|assumption|(rewrite pend_new_r; assumption)|(rewrite pend_new_old by auto; assumption)]; reflexivity]. exfalso. apply (hpend_ne_k r i n Ph); auto. }
      cbv zeta. try rewrite fof_bit by first [lia|assumption|(rewrite pend_new_r; assumption)|(rewrite pend_new_old by auto; assumption)]. erewrite map_ext_in; [reflexivity|]. intros x Ix. apply back_cv; try (apply bitc_notin; exact Ix).
      * intros j Bj. cbn [bd cce]. unfold bor in *. rewrite Bj. reflexivity.
      * intros j0 n0 x0 L0 F0. exfalso. apply (Nf j0); [lia|exact F0].
Qed.

Definition Bx (f : nat -> cell -> val) (B : nat -> bool) : nat -> bool :=
  fun i => B2 i || (B i && negb (first_atb p c cc pc N (rnew f B) T d i)).

(* at the new access's place, the values before the step are the values it read *)
Lemma place_cv : forall B f Bo j0 n x, first_at p c cc pc (rnew f B) T d j0 ->
  (Bo j0 = true -> bor (bd cc) B2 j0 = true) -> x <> bitc (ins p c j0 (rnew f B)) ->
  cellv p c cc pc N Bo (Fn f B) (rnew f B) n j0 x = cellv p c cce pc N' (bor (bd cce) B) f (rnew f B) j0 j0 x.
Proof.
  intros B f Bo j0 n x Fj BB Hbx. cbv beta in Hbx. set (r := rnew f B) in *.
  assert (L : pc <= j0) by (apply (first_at_le _ _ _ _ _ _ _ _ Fj)).
  assert (PN : pend_at p c cce pc N' r j0 = Some k) by (apply pend_new_k; exact Fj).
  assert (PO : pend_at p c cc pc N r j0 = None).
  { destruct (pend_at p c cc pc N r j0) as [n0|] eqn:P; auto. exfalso. apply (old_not_there r j0 n0 P Fj). }
  assert (HO : hpend_at p c cc pc N r j0 = None).
  { destruct (hpend_at p c cc pc N r j0) as [n0|] eqn:P; auto. exfalso. apply (hold_not_there r j0 n0 P Fj). }
  pose proof (first_at_eof _ _ _ _ _ _ _ _ Fj) as D.
  destruct (is_load (ins p c j0 r) && icond (ins p c j0 r) r) eqn:X.
  2:{ rewrite cellv_nl by auto. rewrite cellv_nl by auto. reflexivity. }
  rewrite (cellv_pd _ _ cce pc N' _ _ _ _ _ _ k) by auto. rewrite rv_cce, Nat.eqb_refl.
  destruct n as [|n]; [rewrite cellv_free by auto; unfold fof; cbv beta; rewrite (proj2 (Nat.eqb_neq x (bitc (ins p c j0 (creg p c cce pc N' (bor (bd cce) B) f)))) Hbx); rewrite (cellv_pd _ _ cce pc N' _ _ _ _ _ _ k) by auto;
                       rewrite rv_cce, Nat.eqb_refl; reflexivity|].
  rewrite cellv_go by auto.
  destruct (Bo j0) eqn:Bj; [|unfold fof; cbv beta; rewrite (proj2 (Nat.eqb_neq x (bitc (ins p c j0 (creg p c cce pc N' (bor (bd cce) B) f)))) Hbx); rewrite (cellv_pd _ _ cce pc N' _ _ _ _ _ _ k) by auto;
                              rewrite rv_cce, Nat.eqb_refl; reflexivity].
  destruct (fbinder p c r j0 x) as [b|] eqn:Fb; [|unfold fof; cbv beta; rewrite (proj2 (Nat.eqb_neq x (bitc (ins p c j0 (creg p c cce pc N' (bor (bd cce) B) f)))) Hbx); rewrite (cellv_pd _ _ cce pc N' _ _ _ _ _ _ k) by auto;
                              rewrite rv_cce, Nat.eqb_refl; reflexivity].
  pose proof (fbinder_lt _ _ _ _ _ _ Fb) as Lb0.
  pose proof (fbinder_shape _ _ _ _ _ _ Fb) as (_ & _ & _ & _ & _ & Ix).
  rewrite (eof_icells _ _ _ D) in Ix.
  assert (Ld : is_load (inst_of d) = true) by (rewrite <- (eof_load _ _ _ D); exact X).
  assert (AG : agree (mid (Fn f B)) r j0) by (apply mid_agree; intros i Li; apply (first_place r j0 Fj); lia).
  assert (Fm : first_at p c cc pc (mid (Fn f B)) T d j0)
    by (apply (first_at_agree p W c cc pc r _ T d j0); [intros q Lq; symmetry; apply AG; auto|exact Fj]).
  assert (Fbm : fbinder p c (mid (Fn f B)) j0 x = Some b) by (rewrite (fbinder_agree p W c _ _ j0 x AG); exact Fb).
  destruct (bound_new (Fn f B) j0 x b Fm Ix Ld (BB eq_refl) Fbm) as (k' & Lk & BV).
  pose proof (fbinder_shape _ _ _ _ _ _ Fb) as (Exb & Ixb & _).
  assert (Lk' : lead p c cc pc N r b = Some k').
  { rewrite <- Lk. apply (lead_agree p c cc pc N r _ b W (pend_ok_of p s c I)). intros q Lq. symmetry. apply AG. lia. }
  erewrite (cellv_lead p c cc pc N _ _ r _ b x k' Lk' Exb Ixb).
  rewrite (bvx_agree p W c r (mid (Fn f B)) b j0 x _ Lb0) by (intros q Lq; symmetry; apply AG; auto).
  exact BV.
Qed.

Lemma early_pt : forall B f j,
  slotv p c cc pc N (bor (bd cc) (Bx f B)) (Fn f B) (rnew f B) j = rnew f B j.
Proof.
  intros B f j. set (r := rnew f B).
  transitivity (slotv p c cce pc N' (bor (bd cce) B) f r j); [|symmetry; apply creg_fix; auto; apply pend_ok_e].
  assert (Bsub : forall j, bor (bd cc) (Bx f B) j = true -> bor (bd cce) B j = true).
  { intros j0 Bj. cbn [bd cce]. unfold bor, Bx in *. destruct (bd cc j0), (B2 j0), (B j0); simpl in *; auto. }
  assert (HP : forall j0 n0 x0, first_at p c cc pc r T d j0 -> x0 <> bitc (ins p c j0 r) ->
            cellv p c cc pc N (bor (bd cc) (Bx f B)) (Fn f B) r n0 j0 x0 = cellv p c cce pc N' (bor (bd cce) B) f r j0 j0 x0).
  { intros j0 n0 x0 F0 X0. apply place_cv; auto. intros Bj. unfold bor, Bx in *.
    cbv beta in Bj. rewrite (proj2 (first_atb_e (rnew f B) j0) F0) in Bj. simpl in Bj. rewrite andb_false_r, orb_false_r in Bj. exact Bj. }
  unfold slotv. destruct (Nat.ltb_spec j pc) as [L|L].
  - simpl. unfold upd. destruct (Nat.eqb_spec j k); [lia|reflexivity].
  - destruct (is_load (ins p c j r) && icond (ins p c j r) r) eqn:X; [|reflexivity].
    destruct (first_atb p c cc pc N r T d j) eqn:FB.
    + apply first_atb_e in FB.
      rewrite (pend_new_k r j FB).
      destruct (pend_at p c cc pc N r j) as [n|] eqn:Pa; [exfalso; apply (old_not_there r j n Pa FB)|].
      destruct (hpend_at p c cc pc N r j) as [n|] eqn:Ha; [exfalso; apply (hold_not_there r j n Ha FB)|].
      simpl. rewrite upd_eq.
      assert (CFa : cfx cc j (ins p c j r) r a = a).
      { pose proof (first_at_eof _ _ _ _ _ _ _ _ FB) as D0.
        assert (AG : agree (mid (Fn f B)) r j) by (apply mid_agree; intros i0 Li0; apply (first_place r j FB); lia).
        assert (Fm : first_at p c cc pc (mid (Fn f B)) T d j)
          by (apply (first_at_agree p W c cc pc r _ T d j); [intros q Lq; symmetry; apply AG; auto|exact FB]).
        apply (cfx_eof cc j _ r d (rg cc) a D0 (Hfx _ j Fm)). }
      match goal with |- cfx _ _ _ _ ?X = _ => enough (EX : X = a) by (rewrite EX; exact CFa) end.
      assert (Xl : xload (inst_of d) (rg cc) = true).
      { pose proof (first_at_eof _ _ _ _ _ _ _ _ FB) as D. unfold xload. rewrite <- (eof_load _ _ _ D), X.
        destruct d; reflexivity. }
      destruct (eff_read _ _ _ _ _ _ _ _ _ He Xl) as (_ & Ea).
      pose proof (first_at_eof _ _ _ _ _ _ _ _ FB) as D.
      cbv zeta. match goal with |- context [enc (map ?g (icells (ins p c j r)))] =>
        assert (EV : enc (map g (icells (ins p c j r))) = enc (rdvals (mof s c) (icells (inst_of d)) u)) end.
      { rewrite (eof_icells _ _ _ D). f_equal. unfold rdvals. rewrite <- (eof_icells _ _ _ D). apply map_ext_in. intros x Ix.
        rewrite HP by (auto; apply bitc_notin; exact Ix). rewrite (eof_icells _ _ _ D) in Ix.
        rewrite (cellv_pd _ _ cce pc N' _ _ _ _ _ _ k) by (auto; apply pend_new_k; auto). rewrite rv_cce, Nat.eqb_refl. reflexivity. }
      cbv zeta. rewrite EV. transitivity (areg (inst_of d) w (enc (rdvals (mof s c) (icells (inst_of d)) u))); [|symmetry; exact Ea].
      destruct (eof_cexp _ _ _ (rg cc) D) as (Cs & Ce). destruct (is_cas (ins p c j r)) eqn:Ci.
      * rewrite (areg_cas _ _ _ Cs). f_equal. rewrite <- Ce.
        match goal with |- context [fbit ?F0 (ins p c j r) j] => assert (FBw : fbit F0 (ins p c j r) j = w) end.
        { unfold fbit, fof. rewrite Nat.eqb_refl. replace (Nat.ltb j pc) with false by (symmetry; apply Nat.ltb_ge; lia).
          match goal with |- context [pend_at ?a ?b ?cc0 ?d ?e ?g j] =>
            replace (pend_at a b cc0 d e g j) with (Some k) by (symmetry; exact (pend_new_k r j FB)) end. cbn [rg cce]. rewrite upd_eq, odd_b2n, Ea, (areg_cas _ _ _ Cs). apply vok_vd. }
        rewrite FBw. destruct (Bool.bool_dec w true) as [Wt|Wf].
        -- pose proof He as He'. rewrite Wt in He' |- *. rewrite (eff_w_cas _ _ _ _ _ _ _ _ _ He' Cs eq_refl). reflexivity.
        -- apply not_true_is_false in Wf. rewrite Wf, andb_false_r. reflexivity.
      * destruct d; simpl in Cs; try discriminate; reflexivity.
    + assert (F' : ~ first_at p c cc pc r T d j) by (intros X'; apply first_atb_e in X'; congruence).
      rewrite <- (pend_new_old r j F').
      destruct (pend_at p c cce pc N' r j) as [n|] eqn:Pn.
      * simpl. unfold upd. destruct (Nat.eqb_spec n k); [|reflexivity]. subst n.
        exfalso. rewrite (pend_new_old r j F') in Pn. destruct (pend_at_spec _ _ _ _ _ _ _ _ Pn) as (O1 & _). congruence.
      * rewrite hpend_new. destruct (hpend_at p c cc pc N r j) as [n|] eqn:Ph.
        { simpl. unfold upd. destruct (Nat.eqb_spec n k); [|try rewrite fof_bit by first [lia|assumption|(rewrite pend_new_r; assumption)|(rewrite pend_new_old by auto; assumption)]; reflexivity]. exfalso. apply (hpend_ne_k r j n Ph); auto. }
        cbv zeta. try rewrite fof_bit by first [lia|assumption|(rewrite pend_new_r; assumption)|(rewrite pend_new_old by auto; assumption)]. erewrite map_ext_in; [reflexivity|]. intros x Ix. apply back_cv; try (apply bitc_notin; exact Ix); auto.
Qed.

Lemma INVP_early : INVP p s'.
Proof.
  intros c0 kk d' B f P. destruct (Nat.eq_dec c0 c) as [->|N0].
  2:{ assert (E : cs s' c0 = cs s c0) by (unfold searly, set_es, searly0; apply cs_other; auto).
      assert (E2 : pcs s' c0 = pcs s c0) by reflexivity.
      assert (E3 : tp s' c0 = tp s c0) by (unfold searly, set_es, searly0, evs; simpl; apply upd_neq; auto).
      rewrite E, E2, E3 in *. apply (IP c0 kk d' B f P). }
  rewrite cce_eq, early_pc, early_tp in *. set (r := rnew f B).
  destruct (Nat.eq_dec kk k) as [->|Nk].
  - destruct P as (_ & _ & P3). simpl in P3. rewrite upd_eq in P3. apply inst_of_inj in P3. subst d'.
    destruct (Hok (Fn f B)) as (j2 & _ & G & _). cbv zeta in G. fold (mid (Fn f B)) in G.
    assert (Fj : exists j, first_at p c cc pc r T d j).
    { destruct (existsb (first_atb p c cc pc N r T d) (seq pc (j2 - pc))) eqn:Ex.
      - apply existsb_exists in Ex. destruct Ex as (i & Hi & Fi). exists i. apply first_atb_e. exact Fi.
      - exists j2. apply (first_at_agree p W c cc pc (mid (Fn f B)) r T d j2); [|exact G].
        apply mid_agree. intros i Li Fi. apply first_atb_e in Fi.
        assert (In i (seq pc (j2 - pc))) by (apply in_seq; lia).
        assert (existsb (first_atb p c cc pc N r T d) (seq pc (j2 - pc)) = true) by (apply existsb_exists; eauto). congruence. }
    destruct Fj as (j & Fj). exists j. apply placed_e. left. auto.
  - assert (Po : pending cc pc kk d').
    { destruct P as (P1 & P2 & P3). simpl in P2, P3. unfold upd in P2, P3. destruct (Nat.eqb_spec kk k); [congruence|]. repeat split; auto. }
    assert (EQ : forall j, creg p c cc pc N (bor (bd cc) (Bx f B)) (Fn f B) j = r j).
    { apply creg_ext; [exact W|apply (pend_ok_of p s c I)|]. intros j. apply early_pt. }
    destruct (IP c kk d' (Bx f B) (Fn f B) Po) as (j' & Pl).
    exists j'. apply placed_e. right. split; auto.
    destruct Pl as (Pl1 & t & O & F). split; auto. exists t. split; auto. apply (first_at_ext p c cc pc _ r t d' j' W EQ). exact F.
Qed.


Lemma INVH_early : INVH p s'.
Proof.
  intros c0 kk m xs B f P C. destruct (Nat.eq_dec c0 c) as [->|N0].
  2:{ assert (E : cs s' c0 = cs s c0) by (unfold searly, set_es, searly0; apply cs_other; auto).
      assert (E2 : pcs s' c0 = pcs s c0) by reflexivity.
      assert (E3 : tp s' c0 = tp s c0) by (unfold searly, set_es, searly0, evs; simpl; apply upd_neq; auto).
      rewrite E, E2, E3 in *. apply (IPh c0 kk m xs B f P C). }
  rewrite cce_eq, early_pc, early_tp in *. set (r := rnew f B).
  assert (Nk : kk <> k) by (intros ->; destruct P as (_ & P2 & _); cbn [oh cce] in P2; congruence).
  assert (Po : hpending cc pc kk m xs).
  { destruct P as (P1 & P2 & P3). cbn [oh ai cce] in P2, P3. unfold upd in P3. destruct (Nat.eqb_spec kk k); [congruence|]. repeat split; auto. }
  assert (C0 : oc cc kk = None) by (cbn [oc cce] in C; unfold upd in C; destruct (Nat.eqb_spec kk k); [congruence|exact C]).
  assert (EQ : forall j, creg p c cc pc N (bor (bd cc) (Bx f B)) (Fn f B) j = r j).
  { apply creg_ext; [exact W|apply (pend_ok_of p s c I)|]. intros j. apply early_pt. }
  destruct (IPh c kk m xs (Bx f B) (Fn f B) Po C0) as (j' & Pl).
  exists j'. apply hplaced_e. destruct Pl as (Pl1 & Pl2 & t & O & F). split; auto. split; auto. exists t. split; auto.
  apply (first_atR_ext p c cc pc _ r t m xs j' W EQ). exact F.
Qed.

End EarlyP.

(* ---------- the write of a CAS whose read happened alone, early ---------- *)
Section CweP.
Variables (p : prog) (s : st) (c k t1 : nat) (xs : list cell) (ev nv : val) (B2 : nat -> bool) (m' : mst) (a : val)
          (K : view) (w : bool).
Hypothesis W : wf p.
Hypothesis Wc : cellful p.
Hypothesis I : Inv1 p s.
Hypothesis J : Inv2 p s.
Hypothesis IP : INVP p s.
Hypothesis IPh : INVH p s.
Local Abbreviation cc := (cs s c).
Local Abbreviation pc := (pcs s c).
Local Abbreviation N := (tp s c).
Local Abbreviation T := (tm s).
Local Abbreviation d := (DCas Plain xs ev nv).
Local Abbreviation u := (rw cc k).
Hypothesis Hk : pc < k.
Hypothesis Ho : oc cc k = None.
Hypothesis Oh : oh cc k = Some t1.
Hypothesis Ha : ai cc k = crd Plain xs.
Hypothesis Hok : early_okW p c cc pc N T t1 Plain xs d B2.
Hypothesis He : eff T (inst_of d) (rg cc) (mof s c) m' a K u w.
Hypothesis Hvo : oh cc k <> None -> vok (rg cc k) = true.
Hypothesis Hwt : oh cc k <> None -> w = true.
Hypothesis Hfx : forall f j, first_atR p c cc pc (creg p c cc pc N (bor (bd cc) B2) f) t1 Plain xs j -> fxok cc j (inst_of d) (rg cc) a.
Local Abbreviation s' := (searly s c k d B2 m' a K u w).
Hypothesis I' : Inv1 p s'.
Definition ccw : cst := mkC (upd (oc cc) k (Some T)) (upd (rg cc) k a) (upd (ai cc) k (inst_of d))
  (upd (rw cc) k (wrote T (icells (inst_of d)) u w)) (upd (rv cc) k (rdval (mof s c) u))
  (bor (bd cc) B2) (mP m') (mA m') (mR m')
  (newO s c (inst_of d) (mof s c) m' (vO cc)) (newOg (inst_of d) m' (vOg cc)) (oh cc) (fx cc).
Local Abbreviation N' := (Nat.max N (S k)).

Lemma ccw_eq : cs s' c = ccw.
Proof. unfold searly, set_es, searly0, evs, ccw; simpl. apply upd_eq. Qed.

Lemma cwe_tp : tp s' c = N'.
Proof. unfold searly, set_es, searly0, evs; simpl. apply upd_eq. Qed.

Lemma t1_lt : t1 < T.
Proof. apply (oh_lt_tm p s c k t1 I Oh). Qed.

Lemma pend_ok_w : pend_ok ccw pc.
Proof. rewrite <- ccw_eq. change pc with (pcs s' c). apply (pend_ok_of p s' c I'). Qed.

Lemma hpend_k : hpending cc pc k Plain xs.
Proof. split; [lia|split; [congruence|rewrite Ha; reflexivity]]. Qed.

(* one time, one event *)
Lemma oc_oh_ne : forall k' t, oc cc k' = Some t -> oh cc k = Some t -> False.
Proof.
  intros k' t O1 O2. destruct (i_oc p s I c k' t O1) as (e1 & E1 & C1 & K1).
  destruct (i_oh p s I c k t O2) as (e2 & E2 & _ & _ & Eh). rewrite E1 in E2. injection E2 as <-.
  rewrite (oc_eh p s c k' t e1 I O1 E1 C1 K1) in Eh. discriminate.
Qed.

(* before T, the places are the same with the write recorded *)
Lemma cwe_same_g : forall r t g j, t < T -> (plc p c cc pc r (S t) t g j <-> plc p c ccw pc r (S t) t g j).
Proof.
  intros r t. induction t as [t IH] using lt_wf_ind. intros g j Lt. rewrite !plc_in. apply first_in_iff.
  intros j' _.
  assert (TK : taken p c cc pc r t j' <-> taken p c ccw pc r t j').
  { unfold taken. split.
    - intros (k' & t' & d' & (P1 & P2 & P3) & O & L & F). assert (Nk : k' <> k) by congruence.
      exists k', t', d'. unfold pending. cbn [oc ai ccw]. unfold upd.
      destruct (Nat.eqb_spec k' k); [congruence|]. split; [split; [exact P1|split; [exact P2|exact P3]]|].
      split; [exact O|]. split; [exact L|]. apply (IH t' L); [lia|exact F].
    - intros (k' & t' & d' & (P1 & P2 & P3) & O & L & F). cbn [oc ai ccw] in P2, P3, O. unfold upd in P2, P3, O.
      destruct (Nat.eqb_spec k' k).
      + injection O as <-. lia.
      + exists k', t', d'. split; [split; [exact P1|split; [exact P2|exact P3]]|].
        split; [exact O|]. split; [exact L|]. apply (IH t' L); [lia|exact F]. }
  assert (THK : htaken p c cc pc r t j' <-> htaken p c ccw pc r t j').
  { unfold htaken, hpending, hlive. split.
    - intros (k' & t' & m0 & xs0 & (P1 & P2 & P3) & O & L & Hl & F).
      exists k', t', m0, xs0. cbn [oc oh ai ccw]. unfold upd.
      destruct (Nat.eqb_spec k' k) as [->|Nk].
      + rewrite Ha in P3. split; [split; [exact P1|split; [exact P2|exact P3]]|].
        split; [exact O|]. split; [exact L|]. split; [intros t2 E; injection E as <-; lia|]. apply (IH t' L); [lia|exact F].
      + split; [split; [exact P1|split; [exact P2|exact P3]]|].
        split; [exact O|]. split; [exact L|]. split; [exact Hl|]. apply (IH t' L); [lia|exact F].
    - intros (k' & t' & m0 & xs0 & (P1 & P2 & P3) & O & L & Hl & F). cbn [oc oh ai ccw] in P2, P3, O, Hl. unfold upd in P3, Hl.
      exists k', t', m0, xs0. destruct (Nat.eqb_spec k' k) as [->|Nk].
      + split; [split; [exact P1|split; [exact P2|rewrite Ha; exact P3]]|].
        split; [exact O|]. split; [exact L|]. split; [intros t2 E; congruence|]. apply (IH t' L); [lia|exact F].
      + split; [split; [exact P1|split; [exact P2|exact P3]]|].
        split; [exact O|]. split; [exact L|]. split; [exact Hl|]. apply (IH t' L); [lia|exact F]. }
  assert (RGX : forall k', oh cc k' <> None -> rg ccw k' = rg cc k').
  { intros k' N. cbn [rg ccw]. unfold upd. destruct (Nat.eqb_spec k' k) as [->|]; [|reflexivity].
    rewrite (eff_cas_a _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl He), (Hwt ltac:(congruence)).
    rewrite <- (vd_split (rg cc k)), (Hvo ltac:(congruence)), (proj2 (half_vals p s c k t1 I J Ho Oh)), Ha. reflexivity. }
  assert (THV : forall v, htakenv p c cc pc r t j' v <-> htakenv p c ccw pc r t j' v).
  { intros v. unfold htakenv, hpending, hlive. split.
    - intros (k' & t' & m0 & xs0 & (P1 & P2 & P3) & O & L & Hl & F & Ev).
      exists k', t', m0, xs0. cbn [oc oh ai ccw]. unfold upd.
      destruct (Nat.eqb_spec k' k) as [->|Nk].
      + rewrite Ha in P3. split; [split; [exact P1|split; [exact P2|exact P3]]|].
        split; [exact O|]. split; [exact L|]. split; [intros t2 E; injection E as <-; lia|]. split; [apply (IH t' L); [lia|exact F]|exact Ev].
      + split; [split; [exact P1|split; [exact P2|exact P3]]|].
        split; [exact O|]. split; [exact L|]. split; [exact Hl|]. split; [apply (IH t' L); [lia|exact F]|exact Ev].
    - intros (k' & t' & m0 & xs0 & (P1 & P2 & P3) & O & L & Hl & F & Ev). cbn [oc oh ai ccw] in P2, P3, O, Hl. unfold upd in P3, Hl.
      exists k', t', m0, xs0. destruct (Nat.eqb_spec k' k) as [->|Nk].
      + split; [split; [exact P1|split; [exact P2|rewrite Ha; exact P3]]|].
        split; [exact O|]. split; [exact L|]. split; [intros t2 E; congruence|]. split; [apply (IH t' L); [lia|exact F]|exact Ev].
      + split; [split; [exact P1|split; [exact P2|exact P3]]|].
        split; [exact O|]. split; [exact L|]. split; [exact Hl|]. split; [apply (IH t' L); [lia|exact F]|exact Ev]. }

  split; [exact TK|]. split; [rewrite TK, THK; tauto|exact THV].
Qed.

Lemma cwe_taken : forall r j, taken p c cc pc r T j <-> taken p c ccw pc r T j.
Proof.
  intros r j. unfold taken. split.
  - intros (k' & t' & d' & (P1 & P2 & P3) & O & L & F). assert (Nk : k' <> k) by congruence.
    exists k', t', d'. unfold pending. cbn [oc ai ccw]. unfold upd.
    destruct (Nat.eqb_spec k' k); [congruence|]. split; [split; [exact P1|split; [exact P2|exact P3]]|].
    split; [exact O|]. split; [exact L|]. apply (cwe_same_g r t' (TF d') j L). exact F.
  - intros (k' & t' & d' & (P1 & P2 & P3) & O & L & F). cbn [oc ai ccw] in P2, P3, O. unfold upd in P2, P3, O.
    destruct (Nat.eqb_spec k' k).
    + injection O as <-. lia.
    + exists k', t', d'. split; [split; [exact P1|split; [exact P2|exact P3]]|].
      split; [exact O|]. split; [exact L|]. apply (cwe_same_g r t' (TF d') j L). exact F.
Qed.

(* a read alone placed before the write's place stays placed *)
Lemma cwe_htaken : forall r j' j v, first_atR p c cc pc r t1 Plain xs j -> j' < j ->
  htakenv p c cc pc r T j' v -> htakenv p c ccw pc r T j' v.
Proof.
  intros r j' j v FR Lj (k' & t' & m0 & xs0 & (P1 & P2 & P3) & O & L & Hl & F & Ev).
  destruct (Nat.eq_dec k' k) as [->|Nk].
  - exfalso. rewrite Oh in O. injection O as <-. rewrite Ha in P3. injection P3 as <- <-.
    pose proof (first_atR_unique p c cc pc r t1 Plain xs j' j Wc F FR). lia.
  - exists k', t', m0, xs0. unfold hpending, hlive in *. cbn [oc oh ai rg ccw]. unfold upd.
    destruct (Nat.eqb_spec k' k); [congruence|].
    split; [split; [exact P1|split; [exact P2|exact P3]]|]. split; [exact O|]. split; [exact L|]. split; [exact Hl|].
    split; [apply (cwe_same_g r t' (TH m0 xs0) j' L); exact F|exact Ev].
Qed.

(* the write's place: its read's place *)
Lemma cwe_place : forall r j, first_atR p c cc pc r t1 Plain xs j -> eof (ins p c j r) r = Some d ->
  (forall j', pc <= j' -> j' < j -> executes (ins p c j' r) r = true ->
     (forall v, htakenv p c cc pc r T j' v -> cfailv (ins p c j' r) r v = false) ->
     tied (ins p c j' r) (inst_of d) -> taken p c cc pc r T j') -> first_at p c ccw pc r T d j.
Proof.
  intros r j FR ED BT. apply first_at_mk; [apply (first_atR_le _ _ _ _ _ _ _ _ _ FR)|exact ED| | |].
  - intros (k' & t' & d' & (P1 & P2 & P3) & O & L & F). cbn [oc ai ccw] in P2, P3, O. unfold upd in P2, P3, O.
    destruct (Nat.eqb_spec k' k); [injection O as <-; lia|].
    apply (cwe_same_g r t' (TF d') j L) in F.
    destruct (Nat.lt_trichotomy t' t1) as [Lt|[Et|Gt]].
    + apply (first_atR_free _ _ _ _ _ _ _ _ _ FR). exists k', t', d'.
      split; [split; [exact P1|split; [exact P2|exact P3]]|]. split; [exact O|]. split; [exact Lt|exact F].
    + subst t'. apply (oc_oh_ne k' t1 O Oh).
    + apply (first_at_hfree _ _ _ _ _ _ _ _ F). exists k, t1, Plain, xs.
      split; [exact hpend_k|]. split; [exact Oh|]. split; [exact Gt|]. split; [intros t2 E; congruence|exact FR].
  - intros (k' & t' & m0 & xs0 & (P1 & P2 & P3) & O & L & Hl & F). unfold hlive in Hl.
    cbn [oc oh ai ccw] in P2, P3, O, Hl. unfold upd in P3, Hl.
    destruct (Nat.eqb_spec k' k) as [->|Nk]; [specialize (Hl T eq_refl); lia|].
    apply (cwe_same_g r t' (TH m0 xs0) j L) in F.
    destruct (Nat.lt_trichotomy t' t1) as [Lt|[Et|Gt]].
    + apply (first_atR_hfree _ _ _ _ _ _ _ _ _ FR). exists k', t', m0, xs0.
      split; [split; [exact P1|split; [exact P2|exact P3]]|]. split; [exact O|]. split; [exact Lt|].
      split; [intros t2 E; specialize (Hl t2 E); pose proof t1_lt; lia|exact F].
    + subst t'. apply Nk. apply (oh_inj p s c I k' k t1 O Oh).
    + apply (first_atR_hfree _ _ _ _ _ _ _ _ _ F). exists k, t1, Plain, xs.
      split; [exact hpend_k|]. split; [exact Oh|]. split; [exact Gt|]. split; [intros t2 E; congruence|exact FR].
  - intros j' L1 L2 Ex Fx Ti. apply cwe_taken. apply BT; auto.
    intros v X; apply Fx; apply (cwe_htaken r j' j v FR L2 X).
Qed.

Lemma cwe_placed : forall r j n d0, placed p c ccw pc r n d0 j <->
  (n = k /\ d0 = d /\ first_at p c ccw pc r T d j) \/ (n <> k /\ placed p c cc pc r n d0 j).
Proof.
  intros r j n d0. unfold placed, pending. cbn [oc ai ccw]. unfold upd. destruct (Nat.eqb_spec n k) as [->|Nk].
  - split.
    + intros ((P1 & P2 & P3) & t & O & F). injection O as <-. apply inst_of_inj in P3. subst d0. left. auto.
    + intros [(_ & -> & F)|(Nk & _)]; [|congruence]. split; [split; [lia|split; [discriminate|reflexivity]]|].
      exists T. split; [reflexivity|exact F].
  - split.
    + intros ((P1 & P2 & P3) & t & O & F). right. split; [exact Nk|]. split; [split; [exact P1|split; [exact P2|exact P3]]|].
      exists t. split; [exact O|]. apply (cwe_same_g r t (TF d0) j); [apply (oc_lt_tm p s c n t I O)|exact F].
    + intros [(E & _)|(_ & (P1 & P2 & P3) & t & O & F)]; [congruence|]. split; [split; [exact P1|split; [exact P2|exact P3]]|].
      exists t. split; [exact O|]. apply (cwe_same_g r t (TF d0) j); [apply (oc_lt_tm p s c n t I O)|exact F].
Qed.

Lemma cwe_hplaced : forall r j n m0 xs0, hplaced p c ccw pc r n m0 xs0 j <-> n <> k /\ hplaced p c cc pc r n m0 xs0 j.
Proof.
  intros r j n m0 xs0. unfold hplaced, hpending. cbn [oc oh ai ccw]. unfold upd. destruct (Nat.eqb_spec n k) as [->|Nk].
  - split; [intros (_ & C & _); discriminate|intros (X & _); congruence].
  - split.
    + intros ((P1 & P2 & P3) & C & t & O & F). split; [exact Nk|]. split; [split; [exact P1|split; [exact P2|exact P3]]|].
      split; [exact C|]. exists t. split; [exact O|]. apply (cwe_same_g r t (TH m0 xs0) j); [apply (oh_lt_tm p s c n t I O)|exact F].
    + intros (_ & (P1 & P2 & P3) & C & t & O & F). split; [split; [exact P1|split; [exact P2|exact P3]]|].
      split; [exact C|]. exists t. split; [exact O|]. apply (cwe_same_g r t (TH m0 xs0) j); [apply (oh_lt_tm p s c n t I O)|exact F].
Qed.

Section CwR.
Variables (B : nat -> bool) (f : nat -> cell -> val).
Local Abbreviation Bo := (bor (bd cc) (bor B2 B)).
Local Abbreviation Bn := (bor (bd ccw) B).
Local Abbreviation r0 := (creg p c cc pc N Bo f).

Lemma BoBn : forall j, Bo j = Bn j.
Proof. intros j. unfold bor. cbn [bd ccw]. unfold bor. rewrite orb_assoc. reflexivity. Qed.

(* R1 for the write, read on these registers *)
Lemma cwe_ok : exists j0, pc < j0 /\ first_atR p c cc pc r0 t1 Plain xs j0 /\ eof (ins p c j0 r0) r0 = Some d /\
  forall j', pc <= j' -> j' < j0 -> executes (ins p c j' r0) r0 = true ->
    (forall v, htakenv p c cc pc r0 T j' v -> cfailv (ins p c j' r0) r0 v = false) ->
    tied (ins p c j' r0) (inst_of d) -> taken p c cc pc r0 T j'.
Proof.
  set (g := fof p c cc pc N Bo f r0).
  assert (E : forall j, creg p c cc pc N (bor (bd cc) B2) g j = r0 j).
  { apply (creg_sub p c cc pc N _ _ f W (pend_ok_of p s c I)). intros j X. unfold bor in *.
    apply orb_true_iff in X as [X|X]; rewrite X; [reflexivity|]. rewrite orb_true_r. reflexivity. }
  destruct (Hok g) as (j0 & L & FR & ED & BT). cbv zeta in FR, ED, BT.
  set (rg0 := creg p c cc pc N (bor (bd cc) B2) g) in *.
  assert (A : forall q, agree rg0 r0 q) by (intros q i0 _; apply E).
  exists j0. split; [exact L|]. split; [apply (first_atR_ext p c cc pc rg0 r0 t1 Plain xs j0 W E FR)|]. split.
  - rewrite <- (eof_agree p W c j0 rg0 r0 (A j0)). exact ED.
  - intros j' L1 L2 Ex Fx Ti. rewrite <- (exec_agree p W c j' rg0 r0 (A j')) in Ex.
    rewrite <- (proj1 (ins_agree p W c j' rg0 r0 (A j'))) in Ti.
    assert (E' : forall j, r0 j = rg0 j) by (intros; symmetry; apply E).
    lapply (BT j' L1 L2 Ex); [intros BT'|].
    2:{ intros v X. rewrite (cfailv_agree p W c j' rg0 r0 v (A j')). apply Fx.
        destruct X as (k' & t' & m0 & xs0 & P' & O' & Lt & Hl & F & Ev).
        exists k', t', m0, xs0. split; [exact P'|]. split; [exact O'|]. split; [exact Lt|]. split; [exact Hl|].
        split; [apply (first_atR_ext p c cc pc rg0 r0 t' m0 xs0 j' W E F)|rewrite Ev; apply E]. }
    destruct (BT' Ti) as (k' & t' & d' & P' & O' & Lt & F). exists k', t', d'.
    split; [exact P'|]. split; [exact O'|]. split; [exact Lt|]. apply (first_at_ext p c cc pc rg0 r0 t' d' j' W E F).
Qed.

Lemma cwe_j0 : exists j0, first_atR p c cc pc r0 t1 Plain xs j0 /\ first_at p c ccw pc r0 T d j0.
Proof.
  destruct cwe_ok as (j0 & _ & FR & ED & BT). exists j0. split; [exact FR|]. apply cwe_place; auto.
Qed.

Variable j0 : nat.
Hypothesis FR0 : first_atR p c cc pc r0 t1 Plain xs j0.
Hypothesis NP0 : first_at p c ccw pc r0 T d j0.
Hypothesis Hbit0 : fbit f (ins p c j0 r0) j0 = true.

Lemma cw_pend_old_j0 : pend_at p c cc pc N r0 j0 = None.
Proof.
  apply (pend_at_none_s p s c I). intros (n & d0 & Pl).
  assert (Nk : n <> k) by (intros ->; destruct Pl as ((_ & P2 & _) & _); congruence).
  assert (Pl' : placed p c ccw pc r0 n d0 j0) by (apply cwe_placed; right; auto).
  apply (first_at_free _ _ _ _ _ _ _ _ NP0). destruct Pl' as (Pk & t & O & F). exists n, t, d0.
  split; [exact Pk|]. split; [exact O|]. split; [|exact F].
  cbn [oc ccw] in O. unfold upd in O. destruct (Nat.eqb_spec n k); [congruence|]. apply (oc_lt_tm p s c n t I O).
Qed.

Lemma cw_hpend_old_j0 : hpend_at p c cc pc N r0 j0 = Some k.
Proof.
  apply (hpend_at_char_s p s c I). exists Plain, xs. split; [exact hpend_k|]. split; [exact Ho|]. exists t1. auto.
Qed.

Lemma cw_pend : forall j, pend_at p c ccw pc N' r0 j = if Nat.eqb j j0 then Some k else pend_at p c cc pc N r0 j.
Proof.
  intros j. destruct (Nat.eqb_spec j j0) as [->|Nj].
  - rewrite <- ccw_eq, <- cwe_tp. change pc with (pcs s' c). apply (pend_at_char_s p s' c I').
    exists d. rewrite ccw_eq. apply cwe_placed. left. auto.
  - rewrite <- ccw_eq, <- cwe_tp. change pc with (pcs s' c). symmetry.
    apply (pend_at_eq_s p s s' c c r0 j I I'); [|reflexivity]. intros n. rewrite ccw_eq. change (pcs s' c) with pc. split.
    + intros (d0 & Pl). exists d0. apply cwe_placed. right. split; auto. intros ->. destruct Pl as ((_ & P2 & _) & _). congruence.
    + intros (d0 & Pl). apply cwe_placed in Pl. destruct Pl as [(-> & -> & F)|(_ & X)]; [|eauto].
      exfalso. apply Nj. apply (first_at_unique p c ccw pc r0 T d j j0 Wc F NP0).
Qed.

Lemma cw_hpend : forall j, hpend_at p c ccw pc N' r0 j = if Nat.eqb j j0 then None else hpend_at p c cc pc N r0 j.
Proof.
  intros j. destruct (Nat.eqb_spec j j0) as [->|Nj].
  - rewrite <- ccw_eq, <- cwe_tp. change pc with (pcs s' c). apply (hpend_at_none_s p s' c I').
    intros (n & m0 & xs0 & Pl). rewrite ccw_eq in Pl. apply cwe_hplaced in Pl. destruct Pl as (Nk & Pl).
    apply Nk. pose proof cw_hpend_old_j0 as Q. apply (hpend_at_char_s p s c I) in Q. destruct Q as (m1 & xs1 & Pk).
    exact (hplaced_unique p c cc pc (oh_inj p s c I) r0 j0 n k m0 m1 xs0 xs1 Pl Pk).
  - rewrite <- ccw_eq, <- cwe_tp. change pc with (pcs s' c). symmetry.
    apply (hpend_at_eq_s p s s' c r0 j I I'). intros n. rewrite ccw_eq. change (pcs s' c) with pc. split.
    + intros (m0 & xs0 & Pl). exists m0, xs0. apply cwe_hplaced. split; auto. intros ->.
      destruct Pl as ((_ & _ & P3) & _ & t & O & F). rewrite Oh in O. injection O as <-. rewrite Ha in P3. injection P3 as <- <-.
      apply Nj. apply (first_atR_unique p c cc pc r0 t1 Plain xs j j0 Wc F FR0).
    + intros (m0 & xs0 & Pl). apply cwe_hplaced in Pl. destruct Pl as (_ & Pl). eauto.
Qed.

Lemma cw_hpend_ne : forall j n, j <> j0 -> hpend_at p c cc pc N r0 j = Some n -> n <> k.
Proof.
  intros j n Nj H ->. apply (hpend_at_char_s p s c I) in H. destruct H as (m0 & xs0 & (_ & _ & P3) & _ & t & O & F).
  rewrite Oh in O. injection O as <-. rewrite Ha in P3. injection P3 as <- <-.
  apply Nj. apply (first_atR_unique p c cc pc r0 t1 Plain xs j j0 Wc F FR0).
Qed.

Lemma cw_cv : forall n j x, cellv p c cc pc N Bo f r0 n j x = cellv p c ccw pc N' Bn f r0 n j x.
Proof.
  intros n. induction n as [|n IH]; intros j x; cbn [cellv].
  all: destruct (Nat.ltb_spec j pc) as [L|L]; [cbn [rv ccw]; unfold upd; destruct (Nat.eqb_spec j k); [lia|reflexivity]|].
  all: destruct (is_load (ins p c j r0) && icond (ins p c j r0) r0); [|reflexivity].
  all: rewrite cw_pend, cw_hpend; destruct (Nat.eqb_spec j j0) as [->|Nj];
       [rewrite cw_pend_old_j0, cw_hpend_old_j0; cbn [rv ccw]; rewrite upd_eq;
        first [apply (proj1 (half_vals p s c k t1 I J Ho Oh))|symmetry; apply (proj1 (half_vals p s c k t1 I J Ho Oh))]|].
  all: destruct (pend_at p c cc pc N r0 j) as [n0|] eqn:P;
       [destruct (pend_at_spec _ _ _ _ _ _ _ _ P) as (On & _); cbn [rv ccw]; unfold upd;
        destruct (Nat.eqb_spec n0 k); [subst; congruence|reflexivity]|].
  all: destruct (hpend_at p c cc pc N r0 j) as [n0|] eqn:Ph;
       [pose proof (cw_hpend_ne j n0 Nj Ph); cbn [rv ccw]; unfold upd; destruct (Nat.eqb_spec n0 k); [congruence|reflexivity]|].
  - reflexivity.
  - rewrite BoBn. destruct (Bn j); [|reflexivity]. destruct (fbinder p c r0 j x); [|reflexivity]. rewrite IH. reflexivity.
Qed.

Lemma cw_rg : rg cc k = a.
Proof.
  rewrite <- (vd_split (rg cc k)), (Hvo ltac:(congruence)), (proj2 (half_vals p s c k t1 I J Ho Oh)).
  destruct (eff_read _ _ _ _ _ _ _ _ _ He eq_refl) as (_ & Ea).
  rewrite Ea, (Hwt ltac:(congruence)), Ha. reflexivity.
Qed.

Lemma cw_pt : forall j, slotv p c ccw pc N' Bn f r0 j = r0 j.
Proof.
  intros j. rewrite (creg_fix p W c cc pc N Bo f j (pend_ok_of p s c I)). unfold slotv.
  destruct (Nat.ltb_spec j pc) as [L|L]; [cbn [rg ccw]; unfold upd; destruct (Nat.eqb_spec j k); [lia|reflexivity]|].
  destruct (is_load (ins p c j r0) && icond (ins p c j r0) r0); [|reflexivity].
  rewrite cw_pend, cw_hpend. destruct (Nat.eqb_spec j j0) as [->|Nj].
  - rewrite cw_pend_old_j0, cw_hpend_old_j0. cbn [rg ccw]. rewrite upd_eq. symmetry.
    assert (Ra : rg cc k = vd true ev).
    { rewrite cw_rg. pose proof He as He'. rewrite (Hwt ltac:(congruence)) in He'. exact (eff_cas_ok_e _ (inst_of d) _ _ _ _ _ _ eq_refl He'). }
    pose proof (first_at_eof _ _ _ _ _ _ _ _ NP0) as D. destruct (eof_cexp _ _ _ r0 D) as (Cs & Ce).
    assert (CFa : cfx cc j0 (ins p c j0 r0) r0 a = a).
    { apply (cfx_eof cc j0 _ r0 d (rg cc) a D). apply (Hfx (fof p c cc pc N Bo f r0) j0).
      apply (first_atR_ext p c cc pc r0 _ t1 Plain xs j0 W); [|exact FR0].
      intros q. symmetry. apply (creg_sub p c cc pc N _ Bo f W (pend_ok_of p s c I)).
      intros q0 Q0. unfold bor in *. destruct (bd cc q0), (B2 q0); simpl in *; auto; discriminate. }
    match goal with |- cfx _ _ _ _ ?X = _ => enough (EX : X = a) by (rewrite EX; exact CFa) end.
    rewrite (cfailv_ok (ins p c j0 r0) r0 r0 (rg cc k)).
    + simpl negb. rewrite (Hvo ltac:(congruence)), Hbit0. simpl andb. rewrite Ra, vv_vd, <- Ra. exact cw_rg.
    + rewrite <- Cs. reflexivity.
    + reflexivity.
    + exact (Hvo ltac:(congruence)).
    + change (vv (rg cc k) = cexp (ins p c j0 r0) r0). rewrite <- Ce, Ra, vv_vd. reflexivity.
  - destruct (pend_at p c cc pc N r0 j) as [n0|] eqn:P.
    + destruct (pend_at_spec _ _ _ _ _ _ _ _ P) as (On & _). cbn [rg ccw]; unfold upd.
      destruct (Nat.eqb_spec n0 k); [subst; congruence|reflexivity].
    + destruct (hpend_at p c cc pc N r0 j) as [n0|] eqn:Ph.
      * pose proof (cw_hpend_ne j n0 Nj Ph). cbn [rg ccw]; unfold upd. destruct (Nat.eqb_spec n0 k); [congruence|reflexivity].
      * cbv zeta. erewrite map_ext; [reflexivity|]. intros x. symmetry. apply cw_cv.
Qed.

Lemma cw_regs : forall j, creg p c ccw pc N' Bn f j = r0 j.
Proof. apply (creg_ext p W); [exact pend_ok_w|]. exact cw_pt. Qed.

End CwR.

(* the old state's free values: those of the new one, with the CAS's verdict
   bit at its place set to success *)
Lemma cw_regsF : forall B f, exists F j0,
  (forall j, creg p c cc pc N (bor (bd cc) (bor B2 B)) F j = creg p c ccw pc N' (bor (bd ccw) B) f j) /\
  first_atR p c cc pc (creg p c cc pc N (bor (bd cc) (bor B2 B)) F) t1 Plain xs j0 /\
  first_at p c ccw pc (creg p c cc pc N (bor (bd cc) (bor B2 B)) F) T d j0.
Proof.
  intros B f. destruct (cwe_j0 B f) as (j0 & FR & NP).
  set (r0 := creg p c cc pc N (bor (bd cc) (bor B2 B)) f) in *.
  set (F := fun j x => if Nat.eqb j j0 && Nat.eqb x (bitc (ins p c j0 r0)) then 1 else f j x).
  assert (AG : agree (creg p c cc pc N (bor (bd cc) (bor B2 B)) F) r0 j0).
  { intros i Li. apply (creg_fagree p c cc pc N _ F f j0 W (pend_ok_of p s c I)); [|exact Li].
    intros j x Lj. unfold F. rewrite (proj2 (Nat.eqb_neq j j0)) by lia. reflexivity. }
  assert (AG' : agree r0 (creg p c cc pc N (bor (bd cc) (bor B2 B)) F) j0) by (intros i Li; symmetry; apply AG; exact Li).
  assert (FR' : first_atR p c cc pc (creg p c cc pc N (bor (bd cc) (bor B2 B)) F) t1 Plain xs j0)
    by (apply (plc_agree p W c cc pc _ r0); auto).
  assert (NP' : first_at p c ccw pc (creg p c cc pc N (bor (bd cc) (bor B2 B)) F) T d j0)
    by (apply (first_at_agree p W c ccw pc r0); auto).
  assert (IJ : ins p c j0 (creg p c cc pc N (bor (bd cc) (bor B2 B)) F) = ins p c j0 r0) by (apply (ins_agree p W); exact AG).
  assert (Hb : fbit F (ins p c j0 (creg p c cc pc N (bor (bd cc) (bor B2 B)) F)) j0 = true).
  { unfold fbit. rewrite IJ. unfold F at 1. rewrite !Nat.eqb_refl. reflexivity. }
  pose proof (cw_regs B F j0 FR' NP' Hb) as EQ.
  exists F, j0. split; [|split; assumption].
  intros j. rewrite <- EQ. symmetry. apply (creg_fone p c ccw pc N' _ F f j0 W pend_ok_w).
  - intros j1 x H1. rewrite (proj1 (ins_agree p W c j0 _ _ (fun i _ => EQ i))), IJ in H1. unfold F at 1.
    destruct H1 as [H1|H1]; [rewrite (proj2 (Nat.eqb_neq _ _) H1); reflexivity|].
    rewrite (proj2 (Nat.eqb_neq x _) H1), andb_false_r. reflexivity.
  - assert (Pk : pend_at p c ccw pc N' (creg p c cc pc N (bor (bd cc) (bor B2 B)) F) j0 = Some k)
      by (rewrite (cw_pend B F j0 NP' j0), Nat.eqb_refl; reflexivity).
    intros Z. assert (E2 : forall i, creg p c ccw pc N' (bor (bd ccw) B) F i = creg p c cc pc N (bor (bd cc) (bor B2 B)) F i) by exact EQ.
    rewrite (pend_at_agree p W c ccw pc N' _ (creg p c cc pc N (bor (bd cc) (bor B2 B)) F) j0 pend_ok_w) in Z
      by (intros i _; apply E2). congruence.
Qed.

Lemma INVP_cwe : INVP p s'.
Proof.
  intros c0 kk d' B f P. destruct (Nat.eq_dec c0 c) as [->|N0].
  2:{ assert (E : cs s' c0 = cs s c0) by (unfold searly, set_es, searly0; apply cs_other; auto).
      assert (E2 : pcs s' c0 = pcs s c0) by reflexivity.
      assert (E3 : tp s' c0 = tp s c0) by (unfold searly, set_es, searly0, evs; simpl; apply upd_neq; auto).
      rewrite E, E2, E3 in *. apply (IP c0 kk d' B f P). }
  change (pcs s' c) with pc in *. rewrite ccw_eq, cwe_tp in *.
  destruct (cw_regsF B f) as (Fo & j0 & EQ' & FR & NP).
  destruct (Nat.eq_dec kk k) as [->|Nk].
  - destruct P as (_ & _ & P3). cbn [ai ccw] in P3. rewrite upd_eq in P3. apply inst_of_inj in P3. subst d'.
    exists j0. apply cwe_placed. left. split; [reflexivity|]. split; [reflexivity|].
    apply (first_at_ext p c ccw pc _ _ T d j0 W EQ'). exact NP.
  - assert (Po : pending cc pc kk d').
    { destruct P as (P1 & P2 & P3). cbn [oc ai ccw] in P2, P3. unfold upd in P2, P3. destruct (Nat.eqb_spec kk k); [congruence|]. repeat split; auto. }
    destruct (IP c kk d' (bor B2 B) Fo Po) as (j' & Pl). exists j'. apply cwe_placed. right. split; auto.
    destruct Pl as (Pl1 & t & O & F). split; auto. exists t. split; auto. apply (first_at_ext p c cc pc _ _ t d' j' W EQ'). exact F.
Qed.

Lemma INVH_cwe : INVH p s'.
Proof.
  intros c0 kk m xs0 B f P C. destruct (Nat.eq_dec c0 c) as [->|N0].
  2:{ assert (E : cs s' c0 = cs s c0) by (unfold searly, set_es, searly0; apply cs_other; auto).
      assert (E2 : pcs s' c0 = pcs s c0) by reflexivity.
      assert (E3 : tp s' c0 = tp s c0) by (unfold searly, set_es, searly0, evs; simpl; apply upd_neq; auto).
      rewrite E, E2, E3 in *. apply (IPh c0 kk m xs0 B f P C). }
  change (pcs s' c) with pc in *. rewrite ccw_eq, cwe_tp in *.
  assert (Nk : kk <> k) by (intros ->; cbn [oc ccw] in C; rewrite upd_eq in C; discriminate).
  destruct (cw_regsF B f) as (Fo & j0 & EQ' & FR & NP).
  assert (Po : hpending cc pc kk m xs0).
  { destruct P as (P1 & P2 & P3). cbn [oh ai ccw] in P2, P3. unfold upd in P3. destruct (Nat.eqb_spec kk k); [congruence|]. repeat split; auto. }
  assert (C0 : oc cc kk = None) by (cbn [oc ccw] in C; unfold upd in C; destruct (Nat.eqb_spec kk k); [congruence|exact C]).
  destruct (IPh c kk m xs0 (bor B2 B) Fo Po C0) as (j' & Pl). exists j'. apply cwe_hplaced. split; auto.
  destruct Pl as (Pl1 & Pl2 & t & O & F). split; auto. split; auto. exists t. split; auto.
  apply (first_atR_ext p c cc pc _ _ t m xs0 j' W EQ'). exact F.
Qed.

End CweP.

(* ---------- a CAS's read alone ---------- *)
Lemma eofR_icells : forall i r m xs, eofR i r = Some (m, xs) -> icells i = dd xs.
Proof.
  intros [m1 x1 c1|m1 x1 c1 v1|m0 x0 c0 e0 n0|f1|] r m xs H; simpl in H; try discriminate.
  destruct (c0 r); [injection H as <- <-; reflexivity|discriminate].
Qed.

Section ReadP.
Variables (p : prog) (s : st) (c k : nat) (xs : list cell) (B2 : nat -> bool) (m' : mst) (a : val) (K : view)
          (u : cell -> option nat) (w : bool) (bv : bool).
Hypothesis W : wf p.
Hypothesis Wc : cellful p.
Hypothesis I : Inv1 p s.
Hypothesis J : Inv2 p s.
Hypothesis IP : INVP p s.
Hypothesis IPh : INVH p s.
Local Abbreviation cc := (cs s c).
Local Abbreviation pc := (pcs s c).
Local Abbreviation N := (tp s c).
Local Abbreviation T := (tm s).
Local Abbreviation i := (ILd Plain xs (fun _ => true)).
Hypothesis Hk : pc <= k.
Hypothesis Ho : oc cc k = None.
Hypothesis Hoh : oh cc k = None.
Hypothesis Hok : early_okR p c cc pc N T Plain xs u B2.
Hypothesis He : eff T i (rg cc) (mof s c) m' a K u w.
Local Abbreviation s' := (sread s c k Plain xs B2 m' a K u w bv).
Hypothesis I' : Inv1 p s'.
(* the record carries the result fixed at the read's place (s_cread) *)
Hypothesis Hfx : forall g j, first_atR p c cc pc (creg p c cc pc N (bor (bd cc) B2) g) T Plain xs j ->
  match fx cc j with Some b => b = bv | None => bv = true end.
Definition ccr : cst := mkC (oc cc) (upd (rg cc) k (vd bv a)) (upd (ai cc) k (crd Plain xs))
  (upd (rw cc) k (wrote T (icells i) u w)) (upd (rv cc) k (rdval (mof s c) u))
  (bor (bd cc) B2) (mP m') (mA m') (mR m')
  (newO s c i (mof s c) m' (vO cc)) (newOg i m' (vOg cc)) (upd (oh cc) k (Some T)) (fx cc).
Local Abbreviation N' := (Nat.max N (S k)).

Lemma ccr_eq : cs s' c = ccr.
Proof. unfold sread, ccr; simpl. apply upd_eq. Qed.

Lemma read_tp : tp s' c = N'.
Proof. unfold sread; simpl. apply upd_eq. Qed.

Lemma pend_ok_r : pend_ok ccr pc.
Proof. rewrite <- ccr_eq. change pc with (pcs s' c). apply (pend_ok_of p s' c I'). Qed.

Lemma read_same_g : forall r t g j, t <= T -> (plc p c cc pc r (S t) t g j <-> plc p c ccr pc r (S t) t g j).
Proof.
  intros r t. induction t as [t IH] using lt_wf_ind. intros g j Lt. rewrite !plc_in. apply first_in_iff.
  intros j' _.
  assert (TK : taken p c cc pc r t j' <-> taken p c ccr pc r t j').
  { unfold taken. split.
    - intros (k' & t' & d' & (P1 & P2 & P3) & O & L & F). assert (Nk : k' <> k) by congruence.
      exists k', t', d'. unfold pending. cbn [oc ai ccr]. unfold upd.
      destruct (Nat.eqb_spec k' k); [congruence|]. split; [split; [exact P1|split; [exact P2|exact P3]]|].
      split; [exact O|]. split; [exact L|]. apply (IH t' L); [lia|exact F].
    - intros (k' & t' & d' & (P1 & P2 & P3) & O & L & F). cbn [oc ai ccr] in P2, P3, O. unfold upd in P3.
      destruct (Nat.eqb_spec k' k); [congruence|].
      exists k', t', d'. split; [split; [exact P1|split; [exact P2|exact P3]]|].
      split; [exact O|]. split; [exact L|]. apply (IH t' L); [lia|exact F]. }
  assert (THK : htaken p c cc pc r t j' <-> htaken p c ccr pc r t j').
  { unfold htaken, hpending, hlive. split.
    - intros (k' & t' & m0 & xs0 & (P1 & P2 & P3) & O & L & Hl & F). assert (Nk : k' <> k) by congruence.
      exists k', t', m0, xs0. cbn [oc oh ai ccr]. unfold upd.
      destruct (Nat.eqb_spec k' k); [congruence|]. split; [split; [exact P1|split; [exact P2|exact P3]]|].
      split; [exact O|]. split; [exact L|]. split; [exact Hl|]. apply (IH t' L); [lia|exact F].
    - intros (k' & t' & m0 & xs0 & (P1 & P2 & P3) & O & L & Hl & F). cbn [oc oh ai ccr] in P2, P3, O, Hl. unfold upd in P2, P3, O.
      destruct (Nat.eqb_spec k' k); [injection O as <-; lia|].
      exists k', t', m0, xs0. split; [split; [exact P1|split; [exact P2|exact P3]]|].
      split; [exact O|]. split; [exact L|]. split; [exact Hl|]. apply (IH t' L); [lia|exact F]. }
  assert (RGX : forall k', oh cc k' <> None -> rg ccr k' = rg cc k')
    by (intros k' N; cbn [rg ccr]; unfold upd; destruct (Nat.eqb_spec k' k); [subst; congruence|reflexivity]).
  assert (THV : forall v, htakenv p c cc pc r t j' v <-> htakenv p c ccr pc r t j' v).
  { intros v. unfold htakenv, hpending, hlive. split.
    - intros (k' & t' & m0 & xs0 & (P1 & P2 & P3) & O & L & Hl & F & Ev). assert (Nk : k' <> k) by congruence.
      exists k', t', m0, xs0. cbn [oc oh ai ccr]. unfold upd.
      destruct (Nat.eqb_spec k' k); [congruence|]. split; [split; [exact P1|split; [exact P2|exact P3]]|].
      split; [exact O|]. split; [exact L|]. split; [exact Hl|]. split; [apply (IH t' L); [lia|exact F]|exact Ev].
    - intros (k' & t' & m0 & xs0 & (P1 & P2 & P3) & O & L & Hl & F & Ev). cbn [oc oh ai ccr] in P2, P3, O, Hl. unfold upd in P2, P3, O.
      destruct (Nat.eqb_spec k' k); [injection O as <-; lia|].
      exists k', t', m0, xs0. split; [split; [exact P1|split; [exact P2|exact P3]]|].
      split; [exact O|]. split; [exact L|]. split; [exact Hl|]. split; [apply (IH t' L); [lia|exact F]|exact Ev]. }

  split; [exact TK|]. split; [rewrite TK, THK; tauto|exact THV].
Qed.

Lemma read_sameR : forall r t m xs0 j, t <= T -> (first_atR p c cc pc r t m xs0 j <-> first_atR p c ccr pc r t m xs0 j).
Proof. intros. apply read_same_g; auto. Qed.

Lemma placed_r : forall r j n d0, placed p c ccr pc r n d0 j <-> placed p c cc pc r n d0 j.
Proof.
  intros r j n d0. unfold placed, pending. cbn [oc ai ccr]. unfold upd. destruct (Nat.eqb_spec n k) as [->|Nk].
  - split; intros ((_ & P2 & _) & _); congruence.
  - split; intros ((P1 & P2 & P3) & t & O & F); (split; [split; [exact P1|split; [exact P2|exact P3]]|]);
      exists t; (split; [exact O|]);
      (apply (read_same_g r t (TF d0) j); [pose proof (oc_lt_tm p s c n t I O); lia|exact F]).
Qed.

Lemma pend_new_r : forall r j, pend_at p c ccr pc N' r j = pend_at p c cc pc N r j.
Proof.
  intros r j. rewrite <- ccr_eq, <- read_tp. change pc with (pcs s' c). symmetry.
  apply (pend_at_eq_s p s s' c c r j I I'); [|reflexivity]. intros n. rewrite ccr_eq. change (pcs s' c) with pc.
  split; intros (d0 & Pl); exists d0; apply placed_r; exact Pl.
Qed.

Lemma hplaced_r : forall r j n m0 xs0, hplaced p c ccr pc r n m0 xs0 j <->
  (n = k /\ m0 = Plain /\ xs0 = xs /\ first_atR p c cc pc r T Plain xs j) \/ (n <> k /\ hplaced p c cc pc r n m0 xs0 j).
Proof.
  intros r j n m0 xs0. unfold hplaced, hpending. cbn [oc oh ai ccr]. unfold upd. destruct (Nat.eqb_spec n k) as [->|Nk].
  - split.
    + intros ((P1 & P2 & P3) & C & t & O & F). injection O as <-. injection P3 as <- <-. left.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. apply (read_sameR r T Plain xs j (le_n _)). exact F.
    + intros [(_ & -> & -> & F)|(Nk & _)]; [|congruence]. split; [split; [lia|split; [discriminate|reflexivity]]|].
      split; [exact Ho|]. exists T. split; [reflexivity|]. apply (read_sameR r T Plain xs j (le_n _)). exact F.
  - split.
    + intros ((P1 & P2 & P3) & C & t & O & F). right. split; [exact Nk|]. split; [split; [exact P1|split; [exact P2|exact P3]]|].
      split; [exact C|]. exists t. split; [exact O|].
      apply (read_sameR r t m0 xs0 j); [pose proof (oh_lt_tm p s c n t I O); lia|exact F].
    + intros [(E & _)|(_ & (P1 & P2 & P3) & C & t & O & F)]; [congruence|].
      split; [split; [exact P1|split; [exact P2|exact P3]]|]. split; [exact C|]. exists t. split; [exact O|].
      apply (read_sameR r t m0 xs0 j); [pose proof (oh_lt_tm p s c n t I O); lia|exact F].
Qed.

Lemma hpend_new_k : forall r j, first_atR p c cc pc r T Plain xs j -> hpend_at p c ccr pc N' r j = Some k.
Proof.
  intros r j F. rewrite <- ccr_eq, <- read_tp. change pc with (pcs s' c).
  apply (hpend_at_char_s p s' c I'). exists Plain, xs. rewrite ccr_eq. apply hplaced_r. left. auto.
Qed.

Lemma hpend_new_old : forall r j, ~ first_atR p c cc pc r T Plain xs j ->
  hpend_at p c ccr pc N' r j = hpend_at p c cc pc N r j.
Proof.
  intros r j F. rewrite <- ccr_eq, <- read_tp. change pc with (pcs s' c). symmetry.
  apply (hpend_at_eq_s p s s' c r j I I'). intros n. rewrite ccr_eq. change (pcs s' c) with pc. split.
  - intros (m0 & xs0 & Pl). exists m0, xs0. apply hplaced_r. right. split; auto. intros ->.
    destruct Pl as ((_ & P2 & _) & _). congruence.
  - intros (m0 & xs0 & Pl). apply hplaced_r in Pl. destruct Pl as [(_ & _ & _ & X)|(_ & X)]; [contradiction|eauto].
Qed.

Lemma pend_ne_k : forall r j n, pend_at p c cc pc N r j = Some n -> n <> k.
Proof. intros r j n H ->. destruct (pend_at_spec _ _ _ _ _ _ _ _ H) as (On & _). congruence. Qed.

Lemma hpend_ne_kr : forall r j n, hpend_at p c cc pc N r j = Some n -> n <> k.
Proof.
  intros r j n H ->. apply (hpend_at_char_s p s c I) in H. destruct H as (m0 & xs0 & (_ & P2 & _) & _). congruence.
Qed.

Lemma old_not_thereR : forall r j n, pend_at p c cc pc N r j = Some n -> ~ first_atR p c cc pc r T Plain xs j.
Proof.
  intros r j n Pa F. apply (pend_at_char_s p s c I) in Pa. destruct Pa as (d' & Pk & t & O & Fn).
  apply (first_atR_free _ _ _ _ _ _ _ _ _ F). exists n, t, d'. split; [exact Pk|]. split; [exact O|].
  split; [apply (oc_lt_tm p s c n t I O)|exact Fn].
Qed.

Lemma hold_not_thereR : forall r j n, hpend_at p c cc pc N r j = Some n -> ~ first_atR p c cc pc r T Plain xs j.
Proof.
  intros r j n Pa F. apply (hpend_at_char_s p s c I) in Pa. destruct Pa as (m0 & xs0 & Pk & C & t & O & Fn).
  apply (first_atR_hfree _ _ _ _ _ _ _ _ _ F). exists n, t, m0, xs0. split; [exact Pk|]. split; [exact O|].
  split; [apply (oh_lt_tm p s c n t I O)|]. split; [intros t2 E; congruence|exact Fn].
Qed.

Lemma first_atb_r : forall r j, fab p c cc pc N r (S T) T (TH Plain xs) j = true <-> first_atR p c cc pc r T Plain xs j.
Proof. intros r j. apply fab_plc; [apply (pend_ok_of p s c I)|apply (bn_of p s c I)|apply (bnh_of p s c I)]. Qed.

Local Abbreviation rnew := (fun (f : nat -> cell -> val) (B : nat -> bool) => creg p c ccr pc N' (bor (bd ccr) B) f).
Local Abbreviation Fn := (fun (f : nat -> cell -> val) (B : nat -> bool) =>
  fof p c ccr pc N' (bor (bd ccr) B) f (rnew f B)).
Local Abbreviation mid := (fun (g : nat -> cell -> val) => creg p c cc pc N (bor (bd cc) B2) g).

Lemma first_placeR : forall r j, first_atR p c cc pc r T Plain xs j -> forall q, pc <= q < j -> ~ first_atR p c cc pc r T Plain xs q.
Proof. intros r j F q Lq Fq. pose proof (first_atR_unique p c cc pc r T Plain xs j q Wc F Fq). lia. Qed.

Lemma rv_ccr : forall j, rv ccr j = if Nat.eqb j k then rdval (mof s c) u else rv cc j.
Proof. intros j. reflexivity. Qed.

(* the value the read took in cell x, through a binder R1 counted on *)
Lemma bound_newR : forall g j x b, first_atR p c cc pc (mid g) T Plain xs j -> In x (dd xs) ->
  bor (bd cc) B2 j = true -> fbinder p c (mid g) j x = Some b ->
  exists k', lead p c cc pc N (mid g) b = Some k' /\ bvx p c (mid g) b x (rv cc k' x) = rdval (mof s c) u x.
Proof.
  intros g j x b F Ix Bj Fb.
  destruct (Hok g) as (j2 & G & FX). cbv zeta in FX. fold (mid g) in G, FX.
  assert (Ej : j2 = j) by (apply (first_atR_unique p c cc pc (mid g) T Plain xs j2 j Wc G F)). subst j2.
  destruct (FX x b Ix Bj Fb) as (k' & Lk & Ub). exists k'. split; [exact Lk|].
  pose proof (fbinder_shape _ _ _ _ _ _ Fb) as (Exb & Ixb & Tb & _).
  pose proof (fbinder_lt _ _ _ _ _ _ Fb) as Lbj.
  rewrite (lead_bvx p s c (bor (bd cc) B2) g b x k' T W I J Exb Ixb Lk).
  - rewrite <- Ub. reflexivity.
  - intros Lb _ Cf. apply (first_atR_before _ _ _ _ _ _ _ _ _ F b Lb Lbj Exb).
    + intros v (k0 & t0 & m0 & xs0 & _ & _ & _ & _ & _ & ->). exact Cf.
    + apply (proj1 (tied_crd _ _ _ _ _ (first_atR_eofR _ _ _ _ _ _ _ _ _ F))). exact Tb.
Qed.

Section BackR.
Variables (B : nat -> bool) (f : nat -> cell -> val) (Bo : nat -> bool).
Local Abbreviation r := (rnew f B).
Local Abbreviation F := (Fn f B).
Hypothesis Bsub : forall j, Bo j = true -> bor (bd ccr) B j = true.

Lemma back_cvR : forall n b x,
  (forall j0 n0 x0, j0 <= b -> first_atR p c cc pc r T Plain xs j0 -> x0 <> bitc (ins p c j0 r) ->
     cellv p c cc pc N Bo F r n0 j0 x0 = cellv p c ccr pc N' (bor (bd ccr) B) f r j0 j0 x0) ->
  x <> bitc (ins p c b r) ->
  cellv p c cc pc N Bo F r n b x = cellv p c ccr pc N' (bor (bd ccr) B) f r b b x.
Proof.
  intros n. induction n as [|n IH]; intros b x HP Hbx.
  all: destruct (fab p c cc pc N r (S T) T (TH Plain xs) b) eqn:FB; [apply HP; [lia|apply first_atb_r; exact FB|exact Hbx]|].
  all: assert (Nb : ~ first_atR p c cc pc r T Plain xs b) by (intros X0; apply first_atb_r in X0; congruence).
  all: destruct (Nat.ltb_spec b pc) as [L|L];
    [rewrite cellv_lt by auto; rewrite cellv_lt by auto; rewrite rv_ccr;
     destruct (Nat.eqb_spec b k); [lia|reflexivity]|].
  all: destruct (is_load (ins p c b r) && icond (ins p c b r) r) eqn:X;
         [|rewrite cellv_nl by auto; rewrite cellv_nl by auto; reflexivity].
  all: pose proof (pend_new_r r b) as PE.
  all: destruct (pend_at p c cc pc N r b) as [n0|] eqn:P.
  all: try (rewrite (cellv_pd _ _ cc pc N _ _ _ _ _ _ n0) by auto;
            rewrite (cellv_pd _ _ ccr pc N') with (k := n0) by (auto; rewrite PE; exact P); rewrite rv_ccr;
            destruct (Nat.eqb_spec n0 k); [exfalso; apply (pend_ne_k r b n0 P); auto|reflexivity]).
  all: pose proof (hpend_new_old r b Nb) as PH.
  all: destruct (hpend_at p c cc pc N r b) as [n0|] eqn:Ph.
  all: try (rewrite (cellv_hpd _ _ cc pc N _ _ _ _ _ _ n0) by auto;
            rewrite (cellv_hpd _ _ ccr pc N') with (k := n0) by first [assumption|lia|(rewrite PE; exact P)|(rewrite PH; exact Ph)];
            rewrite rv_ccr; destruct (Nat.eqb_spec n0 k); [exfalso; apply (hpend_ne_kr r b n0 Ph); auto|reflexivity]).
  - rewrite cellv_free by auto. unfold fof; rewrite (proj2 (Nat.eqb_neq _ _) Hbx). reflexivity.
  - rewrite cellv_go by auto.
    destruct (Bo b) eqn:Bb; [|unfold fof; rewrite (proj2 (Nat.eqb_neq _ _) Hbx); reflexivity].
    destruct (fbinder p c r b x) as [b0|] eqn:Fb; [|unfold fof; rewrite (proj2 (Nat.eqb_neq _ _) Hbx); reflexivity].
    destruct b as [|b']; [rewrite fbinder_0 in Fb; discriminate|].
    rewrite (cellv_go _ _ ccr pc _ _ f r b') by first [assumption|lia|(rewrite PE; exact P)|(rewrite PH; exact Ph)]. rewrite (Bsub _ Bb), Fb.
    pose proof (fbinder_lt _ _ _ _ _ _ Fb). f_equal. rewrite IH; try (apply bitc_notin; apply (fbinder_shape _ _ _ _ _ _ Fb)).
    + symmetry. apply cellv_fuel. lia.
    + intros j0 n1 x1 L1 F1 X1. apply HP; [lia|exact F1|exact X1].
Qed.

End BackR.

Lemma mid_agreeR : forall B f J0, (forall q, pc <= q < J0 -> ~ first_atR p c cc pc (rnew f B) T Plain xs q) ->
  agree (mid (Fn f B)) (rnew f B) J0.
Proof.
  intros B f J0 Fx q. induction q as [q IH] using lt_wf_ind. intros Lq. simpl.
  set (r := rnew f B) in *.
  assert (Nf : forall b, b < J0 -> ~ first_atR p c cc pc r T Plain xs b).
  { intros b Lb Fb. destruct (Nat.ltb_spec b pc) as [L|L]; [pose proof (first_atR_le _ _ _ _ _ _ _ _ _ Fb); lia|].
    apply (Fx b); auto. }
  rewrite (creg_fix p W c cc pc N _ _ q (pend_ok_of p s c I)).
  rewrite (slotv_agree p W c cc pc N _ _ _ r q (pend_ok_of p s c I)) by (intros i0 L0; apply IH; lia).
  transitivity (slotv p c ccr pc N' (bor (bd ccr) B) f r q); [|symmetry; apply creg_fix; auto; apply pend_ok_r].
  unfold slotv. destruct (Nat.ltb_spec q pc) as [L|L].
  - simpl. unfold upd. destruct (Nat.eqb_spec q k); [lia|reflexivity].
  - destruct (is_load (ins p c q r) && icond (ins p c q r) r) eqn:X; [|reflexivity].
    rewrite pend_new_r. destruct (pend_at p c cc pc N r q) as [n|] eqn:Pn.
    + simpl. unfold upd. destruct (Nat.eqb_spec n k); [|reflexivity]. exfalso. apply (pend_ne_k r q n Pn); auto.
    + rewrite (hpend_new_old r q (Nf q Lq)). destruct (hpend_at p c cc pc N r q) as [n|] eqn:Ph.
      { simpl. unfold upd. destruct (Nat.eqb_spec n k); [|try rewrite fof_bit by first [lia|assumption|(rewrite pend_new_r; assumption)|(rewrite pend_new_old by auto; assumption)]; reflexivity]. exfalso. apply (hpend_ne_kr r q n Ph); auto. }
      cbv zeta. try rewrite fof_bit by first [lia|assumption|(rewrite pend_new_r; assumption)|(rewrite pend_new_old by auto; assumption)]. erewrite map_ext_in; [reflexivity|]. intros x Ix. apply back_cvR; try (apply bitc_notin; exact Ix).
      * intros j Bj. cbn [bd ccr]. unfold bor in *. rewrite Bj. reflexivity.
      * intros j0 n0 x0 L0 F0. exfalso. apply (Nf j0); [lia|exact F0].
Qed.

Definition BxR (f : nat -> cell -> val) (B : nat -> bool) : nat -> bool :=
  fun q => B2 q || (B q && negb (fab p c cc pc N (rnew f B) (S T) T (TH Plain xs) q)).

(* at the read's place, the values before the step are the values it read *)
Lemma place_cvR : forall B f Bo j0 n x, first_atR p c cc pc (rnew f B) T Plain xs j0 ->
  (Bo j0 = true -> bor (bd cc) B2 j0 = true) -> x <> bitc (ins p c j0 (rnew f B)) ->
  cellv p c cc pc N Bo (Fn f B) (rnew f B) n j0 x = cellv p c ccr pc N' (bor (bd ccr) B) f (rnew f B) j0 j0 x.
Proof.
  intros B f Bo j0 n x Fj BB Hbx. cbv beta in Hbx. set (r := rnew f B) in *.
  assert (L : pc <= j0) by (apply (first_atR_le _ _ _ _ _ _ _ _ _ Fj)).
  assert (HN : hpend_at p c ccr pc N' r j0 = Some k) by (apply hpend_new_k; exact Fj).
  assert (PO : pend_at p c cc pc N r j0 = None).
  { destruct (pend_at p c cc pc N r j0) as [n0|] eqn:P; auto. exfalso. apply (old_not_thereR r j0 n0 P Fj). }
  assert (HO : hpend_at p c cc pc N r j0 = None).
  { destruct (hpend_at p c cc pc N r j0) as [n0|] eqn:P; auto. exfalso. apply (hold_not_thereR r j0 n0 P Fj). }
  assert (PN : pend_at p c ccr pc N' r j0 = None) by (rewrite pend_new_r; exact PO).
  pose proof (first_atR_eofR _ _ _ _ _ _ _ _ _ Fj) as D.
  destruct (eofR_exec_tied p c j0 r Plain xs Wc D) as [Ex _].
  assert (X : is_load (ins p c j0 r) && icond (ins p c j0 r) r = true).
  { destruct (ins p c j0 r) as [m1 x1 c1|m1 x1 c1 v1|m0 x0 c0 e0 n0|f1|]; simpl in D; try discriminate.
    unfold executes in Ex. simpl in *. exact Ex. }
  rewrite (cellv_hpd _ _ ccr pc N' _ _ _ _ _ _ k) by auto. rewrite rv_ccr, Nat.eqb_refl.
  destruct n as [|n]; [rewrite cellv_free by auto; unfold fof; cbv beta; rewrite (proj2 (Nat.eqb_neq x (bitc (ins p c j0 (creg p c ccr pc N' (bor (bd ccr) B) f)))) Hbx); rewrite (cellv_hpd _ _ ccr pc N' _ _ _ _ _ _ k) by auto;
                       rewrite rv_ccr, Nat.eqb_refl; reflexivity|].
  rewrite cellv_go by auto.
  destruct (Bo j0) eqn:Bj; [|unfold fof; cbv beta; rewrite (proj2 (Nat.eqb_neq x (bitc (ins p c j0 (creg p c ccr pc N' (bor (bd ccr) B) f)))) Hbx); rewrite (cellv_hpd _ _ ccr pc N' _ _ _ _ _ _ k) by auto;
                              rewrite rv_ccr, Nat.eqb_refl; reflexivity].
  destruct (fbinder p c r j0 x) as [b|] eqn:Fb; [|unfold fof; cbv beta; rewrite (proj2 (Nat.eqb_neq x (bitc (ins p c j0 (creg p c ccr pc N' (bor (bd ccr) B) f)))) Hbx); rewrite (cellv_hpd _ _ ccr pc N' _ _ _ _ _ _ k) by auto;
                              rewrite rv_ccr, Nat.eqb_refl; reflexivity].
  pose proof (fbinder_lt _ _ _ _ _ _ Fb) as Lb0.
  pose proof (fbinder_shape _ _ _ _ _ _ Fb) as (_ & _ & _ & _ & _ & Ix).
  rewrite (eofR_icells _ _ _ _ D) in Ix.
  assert (AG : agree (mid (Fn f B)) r j0) by (apply mid_agreeR; intros q Lq; apply (first_placeR r j0 Fj); lia).
  assert (Fm : first_atR p c cc pc (mid (Fn f B)) T Plain xs j0)
    by (unfold first_atR; apply (plc_agree p W c cc pc _ r _ T _ j0); [intros q Lq; symmetry; apply AG; auto|exact Fj]).
  assert (Fbm : fbinder p c (mid (Fn f B)) j0 x = Some b) by (rewrite (fbinder_agree p W c _ _ j0 x AG); exact Fb).
  destruct (bound_newR (Fn f B) j0 x b Fm Ix (BB eq_refl) Fbm) as (k' & Lk & BV).
  pose proof (fbinder_shape _ _ _ _ _ _ Fb) as (Exb & Ixb & _).
  assert (Lk' : lead p c cc pc N r b = Some k').
  { rewrite <- Lk. apply (lead_agree p c cc pc N r _ b W (pend_ok_of p s c I)). intros q Lq. symmetry. apply AG. lia. }
  erewrite (cellv_lead p c cc pc N _ _ r _ b x k' Lk' Exb Ixb).
  rewrite (bvx_agree p W c r (mid (Fn f B)) b j0 x _ Lb0) by (intros q Lq; symmetry; apply AG; auto).
  exact BV.
Qed.

Lemma read_pt : forall B f j,
  slotv p c cc pc N (bor (bd cc) (BxR f B)) (Fn f B) (rnew f B) j = rnew f B j.
Proof.
  intros B f j. set (r := rnew f B).
  transitivity (slotv p c ccr pc N' (bor (bd ccr) B) f r j); [|symmetry; apply creg_fix; auto; apply pend_ok_r].
  assert (Bsub : forall j, bor (bd cc) (BxR f B) j = true -> bor (bd ccr) B j = true).
  { intros j0 Bj. cbn [bd ccr]. unfold bor, BxR in *. destruct (bd cc j0), (B2 j0), (B j0); simpl in *; auto. }
  assert (HP : forall j0 n0 x0, first_atR p c cc pc r T Plain xs j0 -> x0 <> bitc (ins p c j0 r) ->
            cellv p c cc pc N (bor (bd cc) (BxR f B)) (Fn f B) r n0 j0 x0 = cellv p c ccr pc N' (bor (bd ccr) B) f r j0 j0 x0).
  { intros j0 n0 x0 F0 X0. apply place_cvR; auto. intros Bj. unfold bor, BxR in *.
    cbv beta in Bj. rewrite (proj2 (first_atb_r (rnew f B) j0) F0) in Bj. simpl in Bj. rewrite andb_false_r, orb_false_r in Bj. exact Bj. }
  unfold slotv. destruct (Nat.ltb_spec j pc) as [L|L].
  - simpl. unfold upd. destruct (Nat.eqb_spec j k); [lia|reflexivity].
  - destruct (is_load (ins p c j r) && icond (ins p c j r) r) eqn:X; [|reflexivity].
    rewrite pend_new_r. destruct (pend_at p c cc pc N r j) as [n|] eqn:Pa.
    + simpl. unfold upd. destruct (Nat.eqb_spec n k); [|reflexivity]. exfalso. apply (pend_ne_k r j n Pa); auto.
    + destruct (fab p c cc pc N r (S T) T (TH Plain xs) j) eqn:FB.
      * apply first_atb_r in FB. rewrite (hpend_new_k r j FB).
        destruct (hpend_at p c cc pc N r j) as [n|] eqn:Ha; [exfalso; apply (hold_not_thereR r j n Ha FB)|].
        simpl. rewrite upd_eq.
        destruct (eff_read _ _ _ _ _ _ _ _ _ He eq_refl) as (_ & Ea). simpl areg in Ea.
        pose proof (first_atR_eofR _ _ _ _ _ _ _ _ _ FB) as D.
        cbv zeta. match goal with |- context [enc (map ?g (icells (ins p c j r)))] =>
          assert (EV : enc (map g (icells (ins p c j r))) = a) end.
        { rewrite Ea. pose proof (eofR_icells _ _ _ _ D) as IC. rewrite IC.
          f_equal. unfold rdvals. apply map_ext_in. intros x Ix. rewrite HP by (auto; apply bitc_notin; rewrite IC; exact Ix).
          rewrite (cellv_hpd _ _ ccr pc N' _ _ _ _ _ _ k) by first [assumption|lia|(rewrite pend_new_r; exact Pa)|(apply hpend_new_k; auto)].
          rewrite rv_ccr, Nat.eqb_refl. reflexivity. }
        assert (Ci : is_cas (ins p c j r) = true) by (destruct (ins p c j r); simpl in D; try discriminate; reflexivity).
        assert (AG : agree (mid (Fn f B)) r j) by (apply mid_agreeR; intros q Lq; apply (first_placeR r j FB); lia).
        assert (Fm : first_atR p c cc pc (mid (Fn f B)) T Plain xs j)
          by (unfold first_atR; apply (plc_agree p W c cc pc _ r _ T _ j); [intros q Lq; symmetry; apply AG; auto|exact FB]).
        assert (Hb : bv = true \/ (bv = false /\ fx cc j = Some false)).
        { pose proof (Hfx (Fn f B) j Fm) as Fx. destruct (fx cc j) as [b0|]; [subst b0|]; destruct bv; auto. }
        destruct Hb as [Bt|(Bf & Fj)].
        2:{ (* a failure fixed at the place: both sides are that failure *)
          rewrite Bf, EV, vok_vd. unfold cfx. cbn [fx ccr]. rewrite Ci, Fj. cbn [andb]. rewrite !vv_vd. reflexivity. }
        rewrite Bt.
        rewrite EV, Ci, vv_vd, cfailv_vd_true; [rewrite vok_vd; try rewrite fof_bit by first [lia|assumption|(rewrite pend_new_r; assumption)]; reflexivity|exact Ci|].
        apply andb_true_iff in X as [_ X]. exact X.
      * assert (F' : ~ first_atR p c cc pc r T Plain xs j) by (intros X'; apply first_atb_r in X'; congruence).
        rewrite (hpend_new_old r j F'). destruct (hpend_at p c cc pc N r j) as [n|] eqn:Ph.
        { simpl. unfold upd. destruct (Nat.eqb_spec n k); [|try rewrite fof_bit by first [lia|assumption|(rewrite pend_new_r; assumption)|(rewrite pend_new_old by auto; assumption)]; reflexivity]. exfalso. apply (hpend_ne_kr r j n Ph); auto. }
        cbv zeta. try rewrite fof_bit by first [lia|assumption|(rewrite pend_new_r; assumption)|(rewrite pend_new_old by auto; assumption)]. erewrite map_ext_in; [reflexivity|]. intros x Ix. apply back_cvR; try (apply bitc_notin; exact Ix); auto.
Qed.

Lemma INVP_read : INVP p s'.
Proof.
  intros c0 kk d' B f P. destruct (Nat.eq_dec c0 c) as [->|N0].
  2:{ assert (E : cs s' c0 = cs s c0) by (unfold sread; simpl; apply upd_neq; auto).
      assert (E2 : pcs s' c0 = pcs s c0) by reflexivity.
      assert (E3 : tp s' c0 = tp s c0) by (unfold sread; simpl; apply upd_neq; auto).
      rewrite E, E2, E3 in *. apply (IP c0 kk d' B f P). }
  change (pcs s' c) with pc in *. rewrite ccr_eq, read_tp in *. set (r := rnew f B).
  assert (Po : pending cc pc kk d').
  { destruct P as (P1 & P2 & P3). cbn [oc ai ccr] in P2, P3. unfold upd in P3. destruct (Nat.eqb_spec kk k); [congruence|]. repeat split; auto. }
  assert (EQ : forall j, creg p c cc pc N (bor (bd cc) (BxR f B)) (Fn f B) j = r j).
  { apply creg_ext; [exact W|apply (pend_ok_of p s c I)|]. intros j. apply read_pt. }
  destruct (IP c kk d' (BxR f B) (Fn f B) Po) as (j' & Pl).
  exists j'. apply placed_r. destruct Pl as (Pl1 & t & O & F). split; auto. exists t. split; auto.
  apply (first_at_ext p c cc pc _ r t d' j' W EQ). exact F.
Qed.

Lemma INVH_read : INVH p s'.
Proof.
  intros c0 kk m xs0 B f P C. destruct (Nat.eq_dec c0 c) as [->|N0].
  2:{ assert (E : cs s' c0 = cs s c0) by (unfold sread; simpl; apply upd_neq; auto).
      assert (E2 : pcs s' c0 = pcs s c0) by reflexivity.
      assert (E3 : tp s' c0 = tp s c0) by (unfold sread; simpl; apply upd_neq; auto).
      rewrite E, E2, E3 in *. apply (IPh c0 kk m xs0 B f P C). }
  change (pcs s' c) with pc in *. rewrite ccr_eq, read_tp in *. set (r := rnew f B).
  destruct (Nat.eq_dec kk k) as [->|Nk].
  - destruct P as (_ & _ & P3). cbn [ai ccr] in P3. rewrite upd_eq in P3. injection P3 as <- <-.
    destruct (Hok (Fn f B)) as (j2 & G & _). cbv zeta in G. fold (mid (Fn f B)) in G.
    assert (Fj : exists j, first_atR p c cc pc r T Plain xs j).
    { destruct (existsb (fab p c cc pc N r (S T) T (TH Plain xs)) (seq pc (j2 - pc))) eqn:Ex.
      - apply existsb_exists in Ex. destruct Ex as (q & Hq & Fq). exists q. apply first_atb_r. exact Fq.
      - exists j2. unfold first_atR. apply (plc_agree p W c cc pc _ (mid (Fn f B)) r T _ j2); [|exact G].
        apply mid_agreeR. intros q Lq Fq. apply first_atb_r in Fq.
        assert (In q (seq pc (j2 - pc))) by (apply in_seq; pose proof (first_atR_le _ _ _ _ _ _ _ _ _ G); lia).
        assert (existsb (fab p c cc pc N r (S T) T (TH Plain xs)) (seq pc (j2 - pc)) = true) by (apply existsb_exists; eauto). congruence. }
    destruct Fj as (j & Fj). exists j. apply hplaced_r. left. auto.
  - assert (Po : hpending cc pc kk m xs0).
    { destruct P as (P1 & P2 & P3). cbn [oh ai ccr] in P2, P3. unfold upd in P2, P3. destruct (Nat.eqb_spec kk k); [congruence|]. repeat split; auto. }
    assert (EQ : forall j, creg p c cc pc N (bor (bd cc) (BxR f B)) (Fn f B) j = r j).
    { apply creg_ext; [exact W|apply (pend_ok_of p s c I)|]. intros j. apply read_pt. }
    destruct (IPh c kk m xs0 (BxR f B) (Fn f B) Po C) as (j' & Pl).
    exists j'. apply hplaced_r. right. split; auto.
    destruct Pl as (Pl1 & Pl2 & t & O & F). split; auto. split; auto. exists t. split; auto.
    apply (first_atR_ext p c cc pc _ r t m xs0 j' W EQ). exact F.
Qed.

End ReadP.

(* ---------- a commit to failure ---------- *)
(* a context state with other registers: nothing that places accesses reads them *)
Definition cc_rg (cc : cst) (g : regs) : cst :=
  mkC (oc cc) g (ai cc) (rw cc) (rv cc) (bd cc) (vP cc) (vA cc) (vR cc) (vO cc) (vOg cc) (oh cc) (fx cc).

Lemma fab_rg : forall p c cc g pc N r n, fab p c (cc_rg cc g) pc N r n = fab p c cc pc N r n.
Proof. intros p c cc g pc N r n. induction n as [|n IH]; [reflexivity|]. cbn [fab]. rewrite IH. reflexivity. Qed.

Lemma plc_rg : forall p c cc g pc r n, plc p c (cc_rg cc g) pc r n = plc p c cc pc r n.
Proof. intros p c cc g pc r n. induction n as [|n IH]; [reflexivity|]. cbn [plc]. rewrite IH. reflexivity. Qed.

Lemma pend_at_rg : forall p c cc g pc N r j, pend_at p c (cc_rg cc g) pc N r j = pend_at p c cc pc N r j.
Proof.
  intros. unfold pend_at, first_atb. apply find_ext_in. intros k _. cbn [oc ai cc_rg].
  destruct (oc cc k); [|reflexivity]. destruct (eof (ai cc k) r); [|reflexivity]. rewrite fab_rg. reflexivity.
Qed.

Lemma hpend_at_rg : forall p c cc g pc N r j, hpend_at p c (cc_rg cc g) pc N r j = hpend_at p c cc pc N r j.
Proof.
  intros. unfold hpend_at. apply find_ext_in. intros k _. cbn [oc oh ai cc_rg].
  destruct (oc cc k); [reflexivity|]. destruct (oh cc k); [|reflexivity]. destruct (casx (ai cc k)) as [[m xs]|]; [|reflexivity].
  rewrite fab_rg. reflexivity.
Qed.

Lemma cellv_rg : forall p c cc g pc N B f r n j x, cellv p c (cc_rg cc g) pc N B f r n j x = cellv p c cc pc N B f r n j x.
Proof.
  intros p c cc g pc N B f r n. induction n as [|n IH]; intros j x; cbn [cellv];
    rewrite pend_at_rg, hpend_at_rg; cbn [rv cc_rg]; [reflexivity|].
  destruct (Nat.ltb j pc); [reflexivity|]. destruct (_ && _); [|reflexivity].
  destruct (pend_at _ _ _ _ _ _ _); [reflexivity|]. destruct (hpend_at _ _ _ _ _ _ _); [reflexivity|].
  destruct (B j); [|reflexivity]. destruct (fbinder p c r j x); [|reflexivity]. rewrite IH. reflexivity.
Qed.

(* free values that differ only in verdict bits do not change the reads *)
Lemma cellv_fbits : forall p c cc pc N B f g r, (forall j x, x <> bitc (ins p c j r) -> f j x = g j x) ->
  forall n j x, x <> bitc (ins p c j r) -> cellv p c cc pc N B f r n j x = cellv p c cc pc N B g r n j x.
Proof.
  intros p c cc pc N B f g r H n. induction n as [|n IH]; intros j x Hx; cbn [cellv];
    (destruct (Nat.ltb j pc); [reflexivity|]); (destruct (_ && _); [|reflexivity]);
    (destruct (pend_at _ _ _ _ _ _ _); [reflexivity|]); (destruct (hpend_at _ _ _ _ _ _ _); [reflexivity|]);
    try (apply H; exact Hx).
  destruct (B j); [|apply H; exact Hx]. destruct (fbinder p c r j x) as [b|] eqn:Fb; [|apply H; exact Hx].
  rewrite IH; [reflexivity|]. apply bitc_notin. apply (fbinder_shape _ _ _ _ _ _ Fb).
Qed.

Section CfailP.
Variables (p : prog) (s : st) (c k : nat).
Hypothesis W : wf p.
Hypothesis Wc : cellful p.
Hypothesis R : run p s.
Hypothesis IP : INVP p s.
Hypothesis IPh : INVH p s.
Hypothesis Hp : pcs s c <= k.
Hypothesis Ho : oc (cs s c) k = None.
Hypothesis Hh : oh (cs s c) k <> None.
Hypothesis Hv : vok (rg (cs s c) k) = true.
Let I : Inv1 p s := Inv1_run p s R.
Local Abbreviation cc := (cs s c).
Local Abbreviation g := (upd (rg (cs s c)) k (vd false (vv (rg (cs s c) k)))).
Local Abbreviation pc := (pcs s c).
Local Abbreviation N := (tp s c).

Lemma cf_cs : cs (scfail s c k) c = cc_rg cc g.
Proof. unfold scfail. simpl. unfold upd at 1. rewrite Nat.eqb_refl. reflexivity. Qed.

(* the old state's free values: the new ones, with the verdict bit of the committed CAS's place set to failure *)
Lemma cf_regs : forall B f, exists F, forall j,
  creg p c cc pc N (bor (bd cc) B) F j = creg p c (cc_rg cc g) pc N (bor (bd cc) B) f j.
Proof.
  intros B f. set (rt := creg p c (cc_rg cc g) pc N (bor (bd cc) B) f).
  set (F := fun j x => if Nat.eqb x (bitc (ins p c j rt))
                       then match hpend_at p c cc pc N rt j with Some k' => if Nat.eqb k' k then 0 else f j x | None => f j x end
                       else f j x).
  assert (PO : pend_ok cc pc) by (apply (pend_ok_of p s c I)).
  assert (FX : forall j x, x <> bitc (ins p c j rt) -> F j x = f j x)
    by (intros j x Hx; unfold F; rewrite (proj2 (Nat.eqb_neq _ _) Hx); reflexivity).
  exists F. apply (creg_ext p W); [exact PO|]. intros j.
  unfold rt at 2. rewrite (creg_fix p W c (cc_rg cc g) pc N (bor (bd cc) B) f j PO). fold rt.
  unfold slotv. rewrite pend_at_rg, hpend_at_rg. cbn [rg cc_rg].
  destruct (Nat.ltb_spec j pc) as [L|L].
  { unfold upd. destruct (Nat.eqb_spec j k); [lia|reflexivity]. }
  destruct (_ && _); [|reflexivity].
  destruct (pend_at p c cc pc N rt j) as [k'|] eqn:Pa.
  { destruct (pend_at_spec _ _ _ _ _ _ _ _ Pa) as (Ok & _). unfold upd. destruct (Nat.eqb_spec k' k); [subst; congruence|reflexivity]. }
  destruct (hpend_at p c cc pc N rt j) as [k'|] eqn:Ph.
  - unfold fbit, F. rewrite Nat.eqb_refl, Ph. unfold upd. destruct (Nat.eqb_spec k' k) as [->|Nk].
    + rewrite Hv, vok_vd. simpl. rewrite andb_false_r. reflexivity.
    + reflexivity.
  - assert (FB : fbit F (ins p c j rt) j = fbit f (ins p c j rt) j) by (unfold fbit, F; rewrite Nat.eqb_refl, Ph; reflexivity).
    cbv zeta. rewrite FB. erewrite map_ext_in; [reflexivity|]. intros x Ix. rewrite cellv_rg.
    apply (cellv_fbits p c cc pc N _ F f rt FX). apply bitc_notin. exact Ix.
Qed.

Lemma INVP_cfail0 : INVP p (scfail s c k).
Proof.
  intros c0 kk d B f P. destruct (Nat.eq_dec c0 c) as [->|N0].
  2:{ assert (E : cs (scfail s c k) c0 = cs s c0) by (unfold scfail; simpl; apply upd_neq; auto).
      change (pcs (scfail s c k)) with (pcs s) in *. change (tp (scfail s c k)) with (tp s) in *.
      rewrite E in *. apply (IP c0 kk d B f P). }
  change (pcs (scfail s c k)) with (pcs s) in *. change (tp (scfail s c k)) with (tp s) in *.
  rewrite cf_cs in *. change (bd (cc_rg cc g)) with (bd cc). destruct (cf_regs B f) as (F & EQ).
  destruct (IP c kk d B F P) as (j & (Pk & t & O & Fj)). exists j. split; [exact P|]. exists t. split; [exact O|].
  unfold first_at in *. rewrite plc_rg. apply (first_at_ext p c cc pc _ _ t d j W EQ Fj).
Qed.

Lemma INVH_cfail0 : INVH p (scfail s c k).
Proof.
  intros c0 kk m xs B f P C. destruct (Nat.eq_dec c0 c) as [->|N0].
  2:{ assert (E : cs (scfail s c k) c0 = cs s c0) by (unfold scfail; simpl; apply upd_neq; auto).
      change (pcs (scfail s c k)) with (pcs s) in *. change (tp (scfail s c k)) with (tp s) in *.
      rewrite E in *. apply (IPh c0 kk m xs B f P C). }
  change (pcs (scfail s c k)) with (pcs s) in *. change (tp (scfail s c k)) with (tp s) in *.
  rewrite cf_cs in *. change (bd (cc_rg cc g)) with (bd cc). destruct (cf_regs B f) as (F & EQ).
  destruct (IPh c kk m xs B F P C) as (j & (Pk & C' & t & O & Fj)). exists j. split; [exact P|]. split; [exact C|].
  exists t. split; [exact O|]. unfold first_atR in *. rewrite plc_rg. apply (first_atR_ext p c cc pc _ _ t m xs j W EQ Fj).
Qed.

End CfailP.

Lemma INVP_cfail : forall p s c k, wf p -> cellful p -> run p s -> INVP p s -> INVH p s ->
  pcs s c <= k -> oc (cs s c) k = None -> oh (cs s c) k <> None -> vok (rg (cs s c) k) = true -> INVP p (scfail s c k).
Proof. intros. eapply INVP_cfail0; eauto. Qed.
Lemma INVH_cfail : forall p s c k, wf p -> cellful p -> run p s -> INVP p s -> INVH p s ->
  pcs s c <= k -> oc (cs s c) k = None -> oh (cs s c) k <> None -> vok (rg (cs s c) k) = true -> INVH p (scfail s c k).
Proof. intros. eapply INVH_cfail0; eauto. Qed.

(* ---------- S3c: a result fixed ---------- *)
(* a context state with other reads counted on and other results fixed *)
Definition cc_fx (cc : cst) (bd' : nat -> bool) (fx' : nat -> option bool) : cst :=
  mkC (oc cc) (rg cc) (ai cc) (rw cc) (rv cc) bd' (vP cc) (vA cc) (vR cc) (vO cc) (vOg cc) (oh cc) fx'.

Lemma fab_fx : forall p c cc b' g pc N r n, fab p c (cc_fx cc b' g) pc N r n = fab p c cc pc N r n.
Proof. intros p c cc b' g pc N r n. induction n as [|n IH]; [reflexivity|]. cbn [fab]. rewrite IH. reflexivity. Qed.

Lemma plc_fx : forall p c cc b' g pc r n, plc p c (cc_fx cc b' g) pc r n = plc p c cc pc r n.
Proof. intros p c cc b' g pc r n. induction n as [|n IH]; [reflexivity|]. cbn [plc]. rewrite IH. reflexivity. Qed.

Lemma pend_at_fx : forall p c cc b' g pc N r j, pend_at p c (cc_fx cc b' g) pc N r j = pend_at p c cc pc N r j.
Proof.
  intros. unfold pend_at, first_atb. apply find_ext_in. intros k _. cbn [oc ai cc_fx].
  destruct (oc cc k); [|reflexivity]. destruct (eof (ai cc k) r); [|reflexivity]. rewrite fab_fx. reflexivity.
Qed.

Lemma hpend_at_fx : forall p c cc b' g pc N r j, hpend_at p c (cc_fx cc b' g) pc N r j = hpend_at p c cc pc N r j.
Proof.
  intros. unfold hpend_at. apply find_ext_in. intros k _. cbn [oc oh ai cc_fx].
  destruct (oc cc k); [reflexivity|]. destruct (oh cc k); [|reflexivity]. destruct (casx (ai cc k)) as [[m xs]|]; [|reflexivity].
  rewrite fab_fx. reflexivity.
Qed.

Lemma cellv_fx : forall p c cc b' g pc N B f r n j x, cellv p c (cc_fx cc b' g) pc N B f r n j x = cellv p c cc pc N B f r n j x.
Proof.
  intros p c cc b' g pc N B f r n. induction n as [|n IH]; intros j x; cbn [cellv];
    rewrite pend_at_fx, hpend_at_fx; cbn [rv cc_fx]; [reflexivity|].
  destruct (Nat.ltb j pc); [reflexivity|]. destruct (_ && _); [|reflexivity].
  destruct (pend_at _ _ _ _ _ _ _); [reflexivity|]. destruct (hpend_at _ _ _ _ _ _ _); [reflexivity|].
  destruct (B j); [|reflexivity]. destruct (fbinder p c r j x); [|reflexivity]. rewrite IH. reflexivity.
Qed.

Section CfixP.
Variables (p : prog) (s : st) (c j0 : nat) (b : bool) (B0 : nat -> bool).
Hypothesis W : wf p.
Hypothesis I : Inv1 p s.
Hypothesis IP : INVP p s.
Hypothesis IPh : INVH p s.
Hypothesis Hf : fx (cs s c) j0 = None.
(* the record of the place, if any, has not failed, or the result fixed is a failure *)
Hypothesis Hc : forall f k, hpend_at p c (cs s c) (pcs s c) (tp s c)
  (creg p c (cs s c) (pcs s c) (tp s c) (bor (bd (cs s c)) B0) f) j0 = Some k -> vok (rg (cs s c) k) = true \/ b = false.
Local Abbreviation cc := (cs s c).
Local Abbreviation pc := (pcs s c).
Local Abbreviation N := (tp s c).
Local Abbreviation cc' := (cc_fx cc (bor (bd cc) B0) (upd (fx cc) j0 (Some b))).

Lemma cx_cs : cs (scfix0 s c j0 b B0) c = cc'.
Proof. unfold scfix0. simpl. unfold upd at 1. rewrite Nat.eqb_refl. reflexivity. Qed.

(* the old state's free values: the new ones, with the verdict bit of the
   place fixed set to the result fixed *)
Lemma cx_regs : forall B f, exists F, forall j,
  creg p c cc pc N (bor (bd cc) (bor B0 B)) F j = creg p c cc' pc N (bor (bd cc') B) f j.
Proof.
  intros B f. set (rt := creg p c cc' pc N (bor (bd cc') B) f).
  set (F := fun j x => if Nat.eqb j j0 && Nat.eqb x (bitc (ins p c j0 rt)) then Nat.b2n b else f j x).
  set (Bo := bor (bd cc) (bor B0 B)).
  assert (PO : pend_ok cc pc) by (apply (pend_ok_of p s c I)).
  assert (PO' : pend_ok cc' pc) by exact PO.
  assert (BE : forall q, bor (bd cc') B q = Bo q)
    by (intros q; unfold Bo, bor; cbn [bd cc_fx]; unfold bor; destruct (bd cc q), (B0 q), (B q); reflexivity).
  exists F. intros j. induction j as [j IH] using lt_wf_ind.
  rewrite (creg_fix p W c cc pc N Bo F j PO).
  rewrite (slotv_agree p W c cc pc N Bo F _ rt j PO) by (intros q Lq; apply IH; exact Lq).
  unfold rt at 2. rewrite (creg_fix p W c cc' pc N _ f j PO'). fold rt.
  unfold slotv. destruct (Nat.ltb j pc) eqn:Lj; [reflexivity|].
  destruct (is_load (ins p c j rt) && icond (ins p c j rt) rt) eqn:X; [|reflexivity].
  rewrite pend_at_fx. destruct (pend_at p c cc pc N rt j) as [k|] eqn:Pa; [reflexivity|].
  rewrite hpend_at_fx.
  assert (CV : forall x, x <> bitc (ins p c j rt) ->
    cellv p c cc' pc N (bor (bd cc') B) f rt j j x = cellv p c cc pc N Bo F rt j j x).
  { intros x Hx. rewrite cellv_fx. rewrite (cellv_Bext p c cc pc N _ Bo f rt BE). symmetry.
    apply (cellv_fone p c cc pc N Bo F f rt j0); [|exact Hx].
    intros j1 x1 H1. unfold F. destruct (Nat.eqb_spec j1 j0) as [->|N1]; [|reflexivity].
    destruct H1 as [H1|H1]; [congruence|]. rewrite (proj2 (Nat.eqb_neq _ _) H1). reflexivity. }
  assert (MV : enc (map (cellv p c cc' pc N (bor (bd cc') B) f rt j j) (icells (ins p c j rt))) =
               enc (map (cellv p c cc pc N Bo F rt j j) (icells (ins p c j rt)))).
  { f_equal. apply map_ext_in. intros x Ix. apply CV. apply bitc_notin. exact Ix. }
  destruct (Nat.eq_dec j j0) as [->|Nj].
  - (* the place fixed *)
    rewrite (cfx_none cc j0 _ _ _ Hf). rewrite !cfx_unfold. cbn [fx cc_fx]. unfold upd at 1. rewrite Nat.eqb_refl.
    assert (FB : fbit F (ins p c j0 rt) j0 = b) by (unfold fbit, F; rewrite !Nat.eqb_refl; simpl; apply odd_b2n).
    rewrite FB. apply andb_prop in X as [Xl Xc].
    destruct (hpend_at p c cc pc N rt j0) as [k|] eqn:Ph.
    + (* its read half was performed: it has not failed, or the result fixed is a failure *)
      assert (Vk : vok (rg cc k) = true \/ b = false).
      { set (ro := creg p c cc pc N Bo F).
        set (f2 := fof p c cc pc N Bo F ro).
        assert (EQo : forall q, creg p c cc pc N (bor (bd cc) B0) f2 q = ro q).
        { apply (creg_sub p c cc pc N _ Bo F W PO). intros q Q. unfold Bo, bor in *.
          destruct (bd cc q), (B0 q); simpl in *; auto; discriminate. }
        apply (Hc f2 k). rewrite <- Ph.
        apply (hpend_at_agree p W c cc pc N _ rt j0 PO). intros q Lq. rewrite EQo. unfold ro. apply IH. exact Lq. }
      pose proof (hpend_at_cas _ _ _ _ _ _ _ _ Ph) as Ci. change (rg cc') with (rg cc). rewrite Ci.
      destruct (vok (rg cc k)) eqn:Vk'.
      2:{ destruct Vk as [Vk|Bf]; [congruence|]. rewrite Bf. simpl. rewrite <- (vd_split (rg cc k)) at 1. rewrite Vk'. reflexivity. }
      clear Vk. rename Vk' into Vk. rewrite vv_vd.
      destruct (ins p c j0 rt) as [| |m1 x1 c1 e1 n1| |]; simpl in Ci; try discriminate.
      unfold icond, ieval in Xc. simpl in Xc. unfold cfailv, cexp. rewrite Xc, Vk. simpl. rewrite negb_involutive, andb_comm. reflexivity.
    + (* its read is led: the value it takes *)
      cbv zeta. rewrite MV. destruct (is_cas (ins p c j0 rt)); [|reflexivity].
      rewrite vv_vd, andb_comm. reflexivity.
  - (* another place *)
    rewrite !cfx_unfold. cbn [fx cc_fx]. unfold upd at 1. rewrite (proj2 (Nat.eqb_neq _ _) Nj).
    assert (FB : fbit F (ins p c j rt) j = fbit f (ins p c j rt) j) by (unfold fbit, F; rewrite (proj2 (Nat.eqb_neq _ _) Nj); reflexivity).
    rewrite FB. destruct (hpend_at p c cc pc N rt j); [reflexivity|]. cbv zeta. rewrite MV. reflexivity.
Qed.

Lemma INVP_cfix : INVP p (scfix0 s c j0 b B0).
Proof.
  intros c0 kk d B f P. destruct (Nat.eq_dec c0 c) as [->|N0].
  2:{ assert (E : cs (scfix0 s c j0 b B0) c0 = cs s c0) by (unfold scfix0; simpl; apply upd_neq; auto).
      change (pcs (scfix0 s c j0 b B0)) with (pcs s) in *. change (tp (scfix0 s c j0 b B0)) with (tp s) in *.
      rewrite E in *. apply (IP c0 kk d B f P). }
  change (pcs (scfix0 s c j0 b B0)) with (pcs s) in *. change (tp (scfix0 s c j0 b B0)) with (tp s) in *.
  rewrite cx_cs in *. destruct (cx_regs B f) as (F & EQ).
  destruct (IP c kk d (bor B0 B) F P) as (j & (Pk & t & O & Fj)). exists j. split; [exact P|]. exists t. split; [exact O|].
  unfold first_at in *. rewrite plc_fx. apply (first_at_ext p c cc pc _ _ t d j W EQ Fj).
Qed.

Lemma INVH_cfix : INVH p (scfix0 s c j0 b B0).
Proof.
  intros c0 kk m xs B f P C. destruct (Nat.eq_dec c0 c) as [->|N0].
  2:{ assert (E : cs (scfix0 s c j0 b B0) c0 = cs s c0) by (unfold scfix0; simpl; apply upd_neq; auto).
      change (pcs (scfix0 s c j0 b B0)) with (pcs s) in *. change (tp (scfix0 s c j0 b B0)) with (tp s) in *.
      rewrite E in *. apply (IPh c0 kk m xs B f P C). }
  change (pcs (scfix0 s c j0 b B0)) with (pcs s) in *. change (tp (scfix0 s c j0 b B0)) with (tp s) in *.
  rewrite cx_cs in *. destruct (cx_regs B f) as (F & EQ).
  destruct (IPh c kk m xs (bor B0 B) F P C) as (j & (Pk & C' & t & O & Fj)). exists j. split; [exact P|]. split; [exact C|].
  exists t. split; [exact O|]. unfold first_atR in *. rewrite plc_fx. apply (first_atR_ext p c cc pc _ _ t m xs j W EQ Fj).
Qed.

End CfixP.

(* the state between the register side of a fix and the fix itself *)
Lemma cfix_pre : forall p s c j b B o, run p s -> cfix_ok p c (cs s c) (pcs s c) (tp s c) j b B o ->
  Inv1 p (sflp s c o b) /\
  forall f k, hpend_at p c (cs (sflp s c o b) c) (pcs (sflp s c o b) c) (tp (sflp s c o b) c)
                (creg p c (cs (sflp s c o b) c) (pcs (sflp s c o b) c) (tp (sflp s c o b) c)
                   (bor (bd (cs (sflp s c o b) c)) B) f) j = Some k ->
              vok (rg (cs (sflp s c o b) c) k) = true \/ b = false.
Proof.
  intros p s c j b B o R Hc. pose proof (Inv1_run p s R) as I. split.
  - destruct o as [k|]; [destruct b|]; cbn [sflp]; try exact I.
    destruct (cfix_rec _ _ _ _ _ _ _ _ _ Hc) as (Hp & Ho & Hh & _). apply Inv1_cfail; auto.
  - destruct Hc as (v & Hv). destruct o as [k0|]; [destruct b|]; cbn [sflp]; intros f k Hp.
    + left. destruct (Hv f) as (_ & _ & _ & Ho & Hk & _). cbv zeta in Ho. rewrite Hp in Ho. apply Hk. congruence.
    + right. reflexivity.
    + exfalso. destruct (Hv f) as (_ & _ & _ & Ho & _). cbv zeta in Ho. congruence.
Qed.

(* ---------- every reachable state ---------- *)
Lemma INVP_init : forall p, INVP p sinit.
Proof. intros p c k d B f (_ & O & _). simpl in O. congruence. Qed.

Lemma INVH_init : forall p, INVH p sinit.
Proof. intros p c k m xs B f (_ & O & _). simpl in O. congruence. Qed.

Theorem INVPH_run : forall p s, wf p -> cellful p -> run p s -> INVP p s /\ INVH p s.
Proof.
  intros p s W Wc R. induction R as [|s t R IH H].
  - split; [apply INVP_init|apply INVH_init].
  - destruct IH as [IP IPh].
    pose proof (Inv2_run p s R) as [I J]. pose proof (Inv1_run p t (rS p s t R H)) as I'.
    destruct (step_cases p s t H) as [(c & i & m' & a & K & u & w & H1 & H2 & H3 & H4 & Hbh & Hh & HwO & HvO & H6 & HfO & ->)|[(c & k & d & B & m' & a & K & u & w & H1 & H2 & Hso & Hh & HwE & HvE & H5 & (HfE1 & HfE2) & ->)|[(c & d & H1 & H2 & H3 & H4 & H5 & Hfh & ->)|[(c & k & xs & B & m' & a & K & u & w & bv & H1 & H2 & Hoh & Hso & H4 & H5 & HfR & ->)|[(c & K1 & K2 & K3 & Kv & K5 & K4 & HfS & ->)|(cX & jX & bX & BX & oX & HjX & HfX & HcX & ->)]]]]].
    + split; [eapply (INVP_ord p s c i m' a K u w)|eapply (INVH_ord p s c i m' a K u w)]; eauto.
    + destruct Hh as [(Z & Ok)|(t1 & xs & ev & nv & Z & -> & U & Ac & Ok)].
      * split; [eapply (INVP_early p s c k d B m' a K u w)|eapply (INVH_early p s c k d B m' a K u w)]; eauto;
          intros f0 j0 F0; exact (HfE1 Z f0 j0 F0).
      * subst u. assert (Vo : vok (rg (cs s c) k) = true) by (apply HvE; congruence).
        assert (Wt : w = true) by (apply HwE; congruence).
        split; [eapply (INVP_cwe p s c k t1 xs ev nv B m' a K w)|eapply (INVH_cwe p s c k t1 xs ev nv B m' a K w)]; eauto;
          intros f0 j0 F0; exact (HfE2 t1 xs ev nv f0 j0 Z eq_refl F0).
    + split; [eapply (INVP_match p s c d)|eapply (INVH_match p s c d)]; eauto.
    + split; [eapply (INVP_read p s c k xs B m' a K u w bv)|eapply (INVH_read p s c k xs B m' a K u w bv)]; eauto;
        intros g j0 F0; exact (proj1 (HfR g j0 F0)).
    + destruct (oh (cs s c) (pcs s c)) as [t1|] eqn:Oh.
      * (* a CAS whose read happened alone and whose comparison fails *)
        destruct (i_half p s I c (pcs s c) t1 K2 Oh (le_n _)) as (_ & (xs & Ax) & _).
        assert (Er : eofR (ins p c (pcs s c) (rg (cs s c))) (rg (cs s c)) = Some (Plain, xs))
          by (rewrite (K3 ltac:(congruence)), Ax; reflexivity).
        assert (Cf : cfail (ins p c (pcs s c) (rg (cs s c))) (rg (cs s c)) (pcs s c) = true).
        { destruct (xex_false _ _ _ _ K1) as [X|(_ & X)]; [|exact X]. exfalso.
          destruct (eofR_exec_tied p c (pcs s c) (rg (cs s c)) Plain xs Wc Er) as [E0 _]. congruence. }
        assert (Vk : vok (rg (cs s c) (pcs s c)) = false) by (apply Kv; congruence).
        split; [eapply (INVP_skipf p s c t1 xs)|eapply (INVH_skipf p s c t1 xs)]; eauto.
      * assert (X : executes (ins p c (pcs s c) (rg (cs s c))) (rg (cs s c)) = false).
        { destruct (xex_false _ _ _ _ K1) as [X|(Z & _)]; [exact X|congruence]. }
        split; [eapply (INVP_skip p s c)|eapply (INVH_skip p s c)]; eauto.
    + (* S3c: the register side first (a failure after the read half), then the result fixed *)
      assert (Pre : Inv1 p (sflp s cX oX bX) /\ INVP p (sflp s cX oX bX) /\ INVH p (sflp s cX oX bX)).
      { destruct oX as [kX|]; [destruct bX|]; cbn [sflp]; try (split; [exact I|split; assumption]).
        destruct (cfix_rec _ _ _ _ _ _ _ _ _ HcX) as (HpF & HoF & HhF & HvF).
        split; [apply Inv1_cfail; auto|split; [apply (INVP_cfail p s cX kX)|apply (INVH_cfail p s cX kX)]; auto]. }
      destruct Pre as (I0 & P0 & H0).
      assert (Hc0 : forall f k, hpend_at p cX (cs (sflp s cX oX bX) cX) (pcs (sflp s cX oX bX) cX) (tp (sflp s cX oX bX) cX)
                  (creg p cX (cs (sflp s cX oX bX) cX) (pcs (sflp s cX oX bX) cX) (tp (sflp s cX oX bX) cX)
                     (bor (bd (cs (sflp s cX oX bX) cX)) BX) f) jX = Some k ->
                  vok (rg (cs (sflp s cX oX bX) cX) k) = true \/ bX = false).
      { destruct HcX as (v & Hv). destruct oX as [kX|]; [destruct bX|]; cbn [sflp]; intros f k Hp.
        - left. destruct (Hv f) as (_ & _ & _ & Ho & Hk & _). cbv zeta in Ho. rewrite Hp in Ho. apply Hk. congruence.
        - right. reflexivity.
        - exfalso. destruct (Hv f) as (_ & _ & _ & Ho & _). cbv zeta in Ho. congruence. }
      assert (Hf0 : fx (cs (sflp s cX oX bX) cX) jX = None) by (rewrite fx_flp; exact HfX).
      split; [apply (INVP_cfix p (sflp s cX oX bX) cX jX bX BX)|apply (INVH_cfix p (sflp s cX oX bX) cX jX bX BX)]; assumption.
Qed.

Theorem INVP_run : forall p s, wf p -> cellful p -> run p s -> INVP p s.
Proof. intros. apply INVPH_run; auto. Qed.

Theorem INVH_run : forall p s, wf p -> cellful p -> run p s -> INVH p s.
Proof. intros. apply INVPH_run; auto. Qed.
