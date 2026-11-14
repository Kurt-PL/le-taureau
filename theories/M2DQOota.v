(* No value from nowhere (M2Oota.no_thin_air) on M2DQ.
   - an M2Model step: M2Oota.OV_step without its unused hypothesis run p s
     (same script, OV_stQ);
   - q_rfix: the record's register becomes a failure (as OV_step's record
     fix by failure), then sbd changes only bd;
   - q_sfix: scfix0 changes only bd and fx; OV reads wv, ai, rg, rv only.
   The invariants used (InvAll: Inv1, Inv2, Inv3) are carried along runQ
   without cellful p, so the theorem has M2Oota.no_thin_air's hypotheses. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2Oota M2DA M2DP M2DQ M2DQInv.

(* ---------- InvAll along runQ, without cellful ---------- *)
Lemma InvAll_stQ : forall p s t, InvAll p s -> stepQ p s t -> InvAll p t.
Proof.
  intros p s t [I J L] S. destruct S as [s t S _|s c k B Ok _|s c j k B _ Hf Ok].
  - constructor; [exact (Inv1_st p s t I S)|exact (Inv2_st p s t I J S)|exact (Inv3_st p s t I J L S)].
  - pose proof (rfail_ge _ _ _ _ _ _ _ Ok) as Hp. destruct Ok as (Ho & Hh & _).
    constructor; [apply Inv1_bd; apply Inv1_cfail|apply Inv2_bd; apply Inv2_cfail|apply Inv3_bd; apply Inv3_cfail]; auto.
  - constructor; [apply Inv1_cfix|apply Inv2_cfix|apply Inv3_cfix]; auto.
Qed.

Lemma InvAll_runQ : forall p s, runQ p s -> InvAll p s.
Proof.
  intros p s R. induction R as [|s t R IH S]; [constructor; [apply Inv1_init|apply Inv2_init|apply Inv3_init]|].
  exact (InvAll_stQ p s t IH S).
Qed.

Section ThmQ.
Variables (p : prog) (V : val -> Prop).
Hypothesis W : wf p.
Hypothesis V0 : V 0.
Hypothesis Cl : tclosed p V.

Lemma OV_stQ : forall s t, InvAll p s -> OV V s -> step p s t -> OV V t.
Proof.
  intros s t IA O H. destruct IA as [I J L].
  destruct (step_cases p s t H) as [(c & i & m' & a & K & u & w & H1 & H2 & H3 & H4 & Hbh & Hh & _ & _ & H6 & _ & ->)|[(c & k & d & B & m' & a & K & u & w & H1 & H2 & Hso & Hh & _ & _ & H5 & _ & ->)|[(c & d & H1 & H2 & H3 & H4 & H4m & Hfh & ->)|[(c & k & xs & B & m' & a & K & u & w & bv & H1 & H2 & Hh & Hso & H4 & H5 & _ & ->)|[(c & S1 & S2 & S3 & S6 & S5 & S4 & _ & ->)|(cX & jX & bX & BX & oX & HjX & HfX & HcX & ->)]]]]].
  - apply (ev_V p V V0); auto; [constructor; auto|]. rewrite <- H1. apply Cl. intros j Lj. apply (OV_passed p V s c I O j Lj).
  - apply (OV_es V).
    set (f0 := fun (_ : nat) (_ : cell) => 0).
    set (r0 := creg p c (cs s c) (pcs s c) (tp s c) (bor (bd (cs s c)) B) f0) in *.
    assert (Dj' : exists j, eof (ins p c j r0) r0 = Some d).
    { destruct Hh as [(_ & Ok)|(t1 & xs & ev & nv & _ & _ & _ & _ & Ok)].
      - destruct (Ok f0) as (j & _ & F & _). exists j. exact (first_at_eof _ _ _ _ _ _ _ _ F).
      - destruct (Ok f0) as (j & _ & _ & D & _). exists j. exact D. }
    destruct Dj' as (j & Dj).
    assert (VR : forall j, kV V (ins p c j r0) (r0 j))
      by (apply (creg_V p V); auto; [intros q Lq; apply (passed_ai p s c q I Lq)|apply (proj1 (proj2 O))|apply (proj2 (proj2 O))]).
    apply (ev_V p V V0); auto; [constructor; auto|]. exact (cl_inst_eof V _ _ _ Dj (Cl c j r0 (fun q _ => VR q)) _).
  - destruct O as [OW [OR ORv]]. split; [exact OW|split; [intros c0 j|]].
    + rewrite (rg_match p s c c0), (ai_match p s c c0). destruct (Nat.eqb c0 c && Nat.eqb j (pcs s c)) eqn:E; [|apply OR].
      apply andb_prop in E as [E1 E2]. apply Nat.eqb_eq in E1, E2. subst c0 j.
      apply (kV_dec V (ai (cs s c) (pcs s c))); [|apply OR]. rewrite H2. apply (dec_eof _ _ _ H3).
    + intros c0 j x. rewrite (rv_match p s c c0). auto.
  - set (f0 := fun (_ : nat) (_ : cell) => 0).
    destruct (H4 f0) as (j & F0 & _).
    set (r0 := creg p c (cs s c) (pcs s c) (tp s c) (bor (bd (cs s c)) B) f0) in *.
    pose proof (first_atR_eofR _ _ _ _ _ _ _ _ _ F0) as Dj.
    apply (rd_V p V V0); auto; [constructor; auto|].
    assert (VR : forall j, kV V (ins p c j r0) (r0 j))
      by (apply (creg_V p V); auto; [intros q Lq; apply (passed_ai p s c q I Lq)|apply (proj1 (proj2 O))|apply (proj2 (proj2 O))]).
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
  - assert (OF : OV V (sflp s cX oX bX)).
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

(* q_rfix: the failure of the record k, then the reads B counted on *)
Lemma OV_rfixQ : forall s c k B, InvAll p s -> OV V s -> rfail_ok p c (cs s c) (pcs s c) (tp s c) k B ->
  OV V (sbd (scfail s c k) c B).
Proof.
  intros s c k B [I _ _] [OW [OR ORv]] (HoF & HhF & _).
  split; [exact OW|split].
  - intros c0 j. rewrite ai_bd, rg_bd, cs_cf. destruct (Nat.eqb c0 c) eqn:Ec; [|apply OR]. apply Nat.eqb_eq in Ec. subst c0.
    cbn [rg ai]. unfold upd. destruct (Nat.eqb j k) eqn:Ej; [|apply OR]. apply Nat.eqb_eq in Ej. subst j.
    destruct (oh (cs s c) k) as [t1|] eqn:Oh; [|congruence].
    destruct (half_xload p s c k t1 I HoF Oh) as (_ & Ca). apply kV_vd; auto.
  - intros c0 j x. rewrite rv_bd, rv_cf. auto.
Qed.

(* q_sfix: scfix0 changes only bd and fx *)
Lemma OV_sfixQ : forall s c j B, OV V s -> OV V (scfix0 s c j true B).
Proof.
  intros s c j B [OW [OR ORv]]. split; [exact OW|split; [intros c0 j0; rewrite ai_cx, rg_cx; apply OR|intros c0 j0 x; rewrite rv_cx; apply ORv]].
Qed.

Lemma OV_stepQ : forall s t, InvAll p s -> OV V s -> stepQ p s t -> OV V t.
Proof.
  intros s t IA O S. destruct S as [s t S _|s c k B Ok _|s c j k B _ _ _].
  - exact (OV_stQ s t IA O S).
  - exact (OV_rfixQ s c k B IA O Ok).
  - exact (OV_sfixQ s c j B O).
Qed.

Lemma OV_runQ : forall s, runQ p s -> OV V s.
Proof.
  intros s R. induction R as [|s t R IH H].
  - split; [intros y x (e & He & _); unfold ent in He; simpl in He; destruct y; discriminate|split; intros; simpl; [apply kV_0; exact V0|auto]].
  - apply (OV_stepQ s t); auto. apply InvAll_runQ. exact R.
Qed.

Theorem no_thin_air_Q : forall s, runQ p s ->
  (forall y x, isw s y -> V (wv s y x)) /\ (forall c j, kV V (ai (cs s c) j) (rg (cs s c) j)).
Proof. intros s R. destruct (OV_runQ s R) as (A & B & _). auto. Qed.

End ThmQ.

Print Assumptions no_thin_air_Q.
