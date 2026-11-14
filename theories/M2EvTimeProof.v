(* Model2: one event, checked by time. What an event knows (eQ, eQc) and the
   write a read takes are always earlier in time, so with the rank "time"
   only the histories, the reads that missed newer writes and a context's
   own order on a cell are left to check, and those are small facts about a
   run's histories and log. *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO M2Ev M2Trace M2Lit M2EvLit.

Section T.
Variable p : prog.

(* a new log entry knows in order only writes known before it *)
Lemma eQc_lt : forall s, run p s -> forall b e w, ent s b = Some e -> eQc e w -> w < b.
Proof.
  intros s R. induction R as [|s t R IH H]; intros b e w E Q.
  - unfold ent in E. destruct b; discriminate.
  - destruct (InvO_run p s R) as [I J _ O].
    pose proof (Ext_step p s t R H) as X.
    destruct (Nat.lt_ge_cases b (tm s)) as [Lb|Gb].
    + destruct (ent s b) as [e'|] eqn:E'.
      * pose proof (x_ent _ _ X b e' E') as E2. rewrite E in E2. injection E2 as <-. exact (IH b e w E' Q).
      * exfalso. unfold ent in E'. apply nth_error_None in E'. rewrite <- (i_tm p s I) in E'. lia.
    + assert (NEW : forall c i k K u w0 h, e = mkO (tm s) c k K u w0 (evC i (rg (cs s c))) (evR i (rg (cs s c)))
                  (evQ s c i (rg (cs s c)) (mof s c) (vOg (cs s c)) (vO (cs s c)) u w0)
                  (evQc i (rg (cs s c)) (vO (cs s c)) w0) h -> b = tm s -> w < b).
      { intros c i k K u w0 h -> ->. cbn [eQc] in Q. unfold evQc in Q.
        destruct (is_load i && icond i (rg (cs s c))); [|destruct Q].
        apply (isw_lt p s w I). apply (j_views p s J c).
        destruct (o_sub_PG p s O c w Q) as [Pw|Gw]; tauto. }
      destruct (step_cases p s t H) as [(c & i & m' & a & K & u & w0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ->)|[(c & k & d & B & m' & a & K & u & w0 & _ & _ & _ & _ & _ & _ & _ & _ & ->)|[(c & d & _ & _ & _ & _ & _ & _ & ->)|[(c & k & xs & B & m' & a & K & u & w0 & bv & _ & _ & _ & _ & _ & _ & _ & ->)|[(c & _ & _ & _ & _ & _ & _ & _ & ->)|(cX & jX & bX & BX & oX & HjX & HfX & HcX & ->)]]]]].
      * unfold sord in E. rewrite (ent_s' p s c (pcs s c) i m' a K u w0 _ _ _ _ I) in E.
        rewrite (proj2 (Nat.ltb_ge _ _) Gb) in E. destruct (Nat.eqb_spec b (tm s)); [|discriminate].
        injection E as <-. apply (NEW c i (pcs s c) K u w0 false eq_refl). auto.
      * unfold searly, set_es, searly0 in E.
        change (ent (evs s c k (inst_of d) m' a K u w0 (bor (bd (cs s c)) B) (pcs s)
                  (upd (tp s) c (Nat.max (tp s c) (S k))) (cm s)) b = Some e) in E.
        rewrite (ent_s' p s c k (inst_of d) m' a K u w0 _ _ _ _ I) in E.
        rewrite (proj2 (Nat.ltb_ge _ _) Gb) in E. destruct (Nat.eqb_spec b (tm s)); [|discriminate].
        injection E as <-. apply (NEW c (inst_of d) k K u w0 false eq_refl). auto.
      * exfalso. unfold ent, smatch in E. simpl in E. assert (Lb : b < length (lg s)) by (apply nth_error_Some; congruence).
        rewrite <- (i_tm p s I) in Lb. lia.
      * unfold ent, sread in E. simpl in E. rewrite nth_error_app_last, <- (i_tm p s I) in E.
        rewrite (proj2 (Nat.ltb_ge _ _) Gb) in E. destruct (Nat.eqb_spec b (tm s)); [|discriminate].
        injection E as <-. apply (NEW c (ILd Plain xs (fun _ => true)) k K u w0 true eq_refl). auto.
      * exfalso. unfold ent, sskip in E. simpl in E. assert (Lb : b < length (lg s)) by (apply nth_error_Some; congruence).
        rewrite <- (i_tm p s I) in Lb. lia.
      * exfalso. unfold ent, scfix0 in E. cbn [lg] in E. rewrite lg_flp in E. assert (Lb : b < length (lg s)) by (apply nth_error_Some; congruence).
        rewrite <- (i_tm p s I) in Lb. lia.
Qed.

(* what an event knows is earlier, or its own write *)
Lemma eQ_le : forall s, run p s -> forall b e w, ent s b = Some e -> eQ e w -> w <= b.
Proof.
  intros s R b e w E Q. destruct (InvO_run p s R) as [I J _ O].
  destruct (o_QP_G p s O b e E w Q) as [[P|S]|(Lg & _)]; [| |lia].
  - destruct (j_eP p s J b e w E P) as (_ & L). lia.
  - unfold esrc, srcv, vor in S. destruct S as [(x & U)|S].
    + destruct (j_rf p s J b e x w E U) as (L & _). lia.
    + destruct (ew e); [|destruct S]. unfold vone in S. subst w.
      destruct (i_et p s I b e E) as (Et & _). lia.
Qed.

(* evok by time: only histories, missed newer writes and a context's own
   order on a cell need checking *)
Lemma evok_time : forall s, run p s ->
  (forall x a b, older (hs s x) a b -> a < b) ->
  (forall a e x w, nth_error (lg s) a = Some e -> In x (eR e) -> In w (ids (hs s x)) -> w <> a ->
     match erf e x with None => True | Some u => older (hs s x) u w end -> a < w) ->
  (forall x a b ea eb, nth_error (lg s) a = Some ea -> nth_error (lg s) b = Some eb -> ec ea = ec eb ->
     ek ea < ek eb -> In x (eC ea) -> In x (eC eb) -> a < b) ->
  evok s.
Proof.
  intros s R Hh Hn Hp. destruct (InvO_run p s R) as [I J _ O].
  apply (evok_rank s (fun a => a)).
  - intros a b [(x & Ol)|[(e & x & L & Ix & Ib & N & M)|(e & L & Q & N)]].
    + exact (Hh x a b Ol).
    + exact (Hn a e x b L Ix Ib N M).
    + pose proof (eQ_le s R b e a L Q). lia.
  - intros x a b [Ol|[(e & L & Ix & Ib & N & M)|[(e & L & Ix & Ef & N)|[(e & L & Ix & Q & Ib & N)|(ea & eb & La & Lb & C & K & Xa & Xb)]]]].
    + exact (Hh x a b Ol).
    + exact (Hn a e x b L Ix Ib N M).
    + destruct (j_rf p s J b e x a L Ef) as (Lt & _). exact Lt.
    + destruct Q as [Q|Q]; [pose proof (eQ_le s R b e a L Q); lia|exact (eQc_lt s R b e a L Q)].
    + exact (Hp x a b ea eb La Lb C K Xa Xb).
Qed.

End T.

(* ---------- on a concrete run ---------- *)
(* the run reached is a run: kept for the last check *)
Lemma startR : forall p (Q : M2Model.st -> Prop), (exists t, star p sinit t /\ (run p t -> Q t)) -> exists t, run p t /\ Q t.
Proof.
  intros p Q (t & H & q). assert (R : run p t) by (eapply star_run; [constructor|exact H]). exists t. split; auto.
Qed.

(* the three premises of evok_time, by projections of the log: no entry is
   normalised as a whole *)
Ltac et_hist := let x := fresh "x" in let a := fresh "a" in let b := fresh "b" in let O := fresh "O" in
  intros x a b O; apply older_pairs in O; cell4 x; inlist O; try (injection O as <- <-); lia.
(* a projection of the entry at a concrete time, the log computed, the
   entry's own fields left as they are *)
Ltac proj_ent L F P := match type of L with nth_error ?Lg ?a = Some ?e =>
  assert (P : option_map F (nth_error Lg a) = Some (F e)) by (rewrite L; reflexivity);
  let v := eval vm_compute in (option_map F (nth_error Lg a)) in
  change (option_map F (nth_error Lg a)) with v in P; cbv beta in P end.
Ltac et_newer := let a := fresh "a" in let e := fresh "e" in let x := fresh "x" in let w := fresh "w" in
  let L := fresh "L" in let Ix := fresh "Ix" in let Iw := fresh "Iw" in let N := fresh "N" in let M := fresh "M" in
  let P := fresh "P" in let R := fresh "R" in let F0 := fresh "F" in let F1 := fresh "F" in
  let F2 := fresh "F" in let F3 := fresh "F" in
  intros a e x w L Ix Iw N M; nat12 a;
  proj_ent L (fun e => (eR e, erf e 0, erf e 1, erf e 2, erf e 3)) P;
  try discriminate P; injection P as R F0 F1 F2 F3;
  rewrite <- R in Ix; inlist Ix; subst x;
  first [rewrite <- F0 in M|rewrite <- F1 in M|rewrite <- F2 in M|rewrite <- F3 in M];
  vm_compute in Iw; inlist Iw; subst w; try lia;
  first [ exact I | apply older_b in M; vm_compute in M; discriminate M | lia ].
Ltac et_po := let x := fresh "x" in let a := fresh "a" in let b := fresh "b" in
  let ea := fresh "ea" in let eb := fresh "eb" in let La := fresh "La" in let Lb := fresh "Lb" in
  let C := fresh "C" in let K := fresh "K" in let Xa := fresh "Xa" in let Xb := fresh "Xb" in
  let Pa := fresh "Pa" in let Pb := fresh "Pb" in
  let Ca := fresh "C" in let Ka := fresh "K" in let Ea := fresh "E" in
  let Cb := fresh "C" in let Kb := fresh "K" in let Eb := fresh "E" in
  intros x a b ea eb La Lb C K Xa Xb;
  nat12 a; proj_ent La (fun e => (ec e, ek e, eC e)) Pa; try discriminate Pa; injection Pa as Ca Ka Ea;
  rewrite <- Ea in Xa; inlist Xa; subst x; rewrite <- Ca in C; rewrite <- Ka in K;
  nat12 b; proj_ent Lb (fun e => (ec e, ek e, eC e)) Pb; try discriminate Pb; injection Pb as Cb Kb Eb;
  rewrite <- Cb in C; rewrite <- Kb in K; rewrite <- Eb in Xb; inlist Xb; try discriminate C; try lia.
Ltac evok_time_tac R := apply (evok_time _ _ R); [et_hist|et_newer|et_po].

(* a finished run: every context past its code, and no slot recorded at or
   beyond its next instruction (tp bounds the recorded slots) *)
Lemma done_tp : forall P s, run (stat P) s ->
  (forall c, c < length P -> length (nth c P []) <= pcs s c /\ tp s c <= pcs s c) -> done (stat P) s.
Proof.
  intros P s R H. exists (fun c => length (nth c P [])). split; [apply stat_fin|].
  intros c Hc. unfold stat in Hc. rewrite length_map in Hc. destruct (H c Hc) as [A B]. split; [exact A|].
  intros k Hk. apply (i_tp _ s (Inv1_run _ s R) c k). lia.
Qed.
Ltac done_tp_tac R := apply (done_tp _ _ R);
  let c := fresh "c" in let Hc := fresh "Hc" in
  intros c Hc; destruct c as [|[|[|[|[|c]]]]]; simpl in Hc; try lia; split; vm_compute; lia.
