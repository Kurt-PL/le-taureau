(* T1 counter-run, run level, invariants of M2DA's runs of SPFH:
   while context 0 has not read y (pc 0) and no CAS slot of it has happened,
   nothing of it has happened, no result is fixed at slot 2, every read alone
   took 0 and is a success, and x has no write (Q); hence x = 1 happens only
   after r0 = y (F). *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Inv M2Lit M2Cont M2CasSplitProof M2DA M2DAInv M2DASpfhInst M2DASpfhStep.

Lemma fx_fx : forall s c j b B o c', c' <> c -> fx (cs (scfix0 (sflp s c o b) c j b B) c') = fx (cs s c').
Proof.
  intros s c j b B o c' N. unfold scfix0, sflp. destruct o; [destruct b|]; unfold scfail; cbn [cs];
    rewrite ?upd_n by exact N; cbn [fx]; rewrite ?upd_n by exact N; reflexivity.
Qed.

Lemma eff_hs : forall t i r m m' a K u w, eff t i r m m' a K u w ->
  forall x, (is_store i = false \/ ~ In x (icells i)) -> mH m' x = mH m x.
Proof.
  intros t i r m m' a K u w E x H. destruct E; cbn [mH learn wput gpre gpost]; auto.
  - destruct H as [H|H]; [discriminate|]. match goal with P : places _ _ _ _ |- _ => apply (proj2 (P x)); exact H end.
  - destruct H as [H|H]; [discriminate|]. match goal with P : places _ _ _ _ |- _ => apply (proj2 (P x)); exact H end.
Qed.

Lemma eff_ld0 : forall t m xs r mm m' a K u w, eff t (ILd m xs (fun _ => true)) r mm m' a K u w ->
  mH mm 0 = [] -> dd xs = [0] -> a = 0.
Proof.
  intros t m xs r mm m' a K u w E H D. inversion E; subst.
  - discriminate.
  - match goal with X : takes _ _ _ |- _ => destruct X as (Tk & _) end. rewrite D in *.
    specialize (Tk 0 (or_introl eq_refl)). rewrite H in Tk.
    unfold rdvals, rdval. cbn [map enc]. destruct (u 0); [destruct Tk|reflexivity].
Qed.

Lemma eof_shape : forall i r d, eof i r = Some d -> is_store (inst_of d) = is_store i /\ icells (inst_of d) = icells i.
Proof.
  intros i r d E. destruct i as [m x c0|m x c0 v|m x c0 e n|f|]; cbn in E; try discriminate;
    try (destruct (c0 r); [injection E as <-; split; reflexivity|discriminate]).
  destruct f; try discriminate; injection E as <-; split; reflexivity.
Qed.

(* the other contexts write no x; they have no CAS *)
Lemma insc : forall c k r, c <> 0 -> (is_store (ins SPFH c k r) = false \/ ~ In 0 (icells (ins SPFH c k r))) /\
  is_cas (ins SPFH c k r) = false.
Proof.
  intros c k r N. unfold SPFH. rewrite ins_stat. destruct c as [|[|c]]; [congruence| |].
  - destruct k as [|[|k]]; cbn.
    + split; [left|]; reflexivity.
    + split; [right; intros [H|[]]; discriminate H|reflexivity].
    + destruct k; cbn; (split; [left|]); reflexivity.
  - destruct c, k; cbn; (split; [left|]); reflexivity.
Qed.

Lemma isc0 : forall j r, is_cas (ins SPFH 0 j r) = true -> j = 1 \/ j = 2.
Proof. intros j r C. rewrite insS in C. destruct j as [|[|[|[|j]]]]; cbn in C; try discriminate; auto. destruct j; discriminate. Qed.

Lemma eofj : forall j r d, r 0 = 7 -> eof (ins SPFH 0 j r) r = Some d ->
  (j = 0 /\ d = DLd Plain [1]) \/ (j = 2 /\ d = DCas Plain [0] 0 5) \/ (j = 3 /\ d = DSt Plain [0] 1).
Proof.
  intros j r d R0 E. rewrite insS in E. destruct j as [|[|[|[|j]]]]; cbn [nth SPFHc] in E.
  - injection E as <-. auto.
  - unfold eof, dof, EQ in E. rewrite R0 in E. discriminate E.
  - unfold eof, dof, NE in E. rewrite R0 in E. injection E as <-. auto.
  - injection E as <-. auto.
  - destruct j; discriminate E.
Qed.

Lemma eofRj : forall j r m xs, r 0 = 7 -> eofR (ins SPFH 0 j r) r = Some (m, xs) -> j = 2 /\ m = Plain /\ xs = [0].
Proof.
  intros j r m xs R0 E. rewrite insS in E. destruct j as [|[|[|[|j]]]]; cbn [nth SPFHc] in E.
  - discriminate E.
  - unfold eofR, EQ in E. rewrite R0 in E. discriminate E.
  - unfold eofR, NE in E. rewrite R0 in E. injection E as <- <-. auto.
  - discriminate E.
  - destruct j; discriminate E.
Qed.

Definition NoCAS (s : M2Model.st) : Prop := forall k, oc (cs s 0) k <> None -> is_cas (ai (cs s 0) k) = false.

Lemma NoCAS_back : forall p s s', step p s s' -> NoCAS s' -> NoCAS s.
Proof.
  intros p s s' S N k O. destruct (oc (cs s 0) k) as [t|] eqn:E; [|congruence].
  destruct (step_keep p s s' 0 k t S E) as (O' & C & _). rewrite <- C. apply N. congruence.
Qed.

Definition Qc (s : M2Model.st) : Prop :=
  (forall k, oc (cs s 0) k = None) /\ fx (cs s 0) 2 = None /\
  (forall k, oh (cs s 0) k <> None -> rg (cs s 0) k = vd true 0) /\ hs s 0 = [].
Definition Q (s : M2Model.st) : Prop := pcs s 0 = 0 -> NoCAS s -> Qc s.

(* at such a state an access of context 0 that happens early is the CAS as a whole *)
Lemma early0 : forall s N T d u B, Qc s -> early_ok SPFH 0 (cs s 0) 0 N T d u B -> d = DCas Plain [0] 0 5.
Proof.
  intros s N T d u B (P & Fx & Hr & _) H.
  pose proof H as H'. destruct (H f7) as (j & Lj & F & _). cbv zeta in F.
  assert (R0 : creg SPFH 0 (cs s 0) 0 N (bor (bd (cs s 0)) B) f7 0 = 7) by (rewrite creg0S by exact P; reflexivity).
  destruct (eofj _ _ _ R0 (first_at_eof _ _ _ _ _ _ _ _ F)) as [(-> & _)|[(_ & ->)|(_ & ->)]]; [lia|reflexivity|].
  exfalso. exact (SPFH_noearly (cs s 0) N T u B P Fx Hr H').
Qed.

Ltac lets := repeat match goal with x := _ |- _ => subst x end.

Lemma Q_step : forall s s', Q s -> step SPFH s s' -> nowhole s s' -> Q s'.
Proof.
  intros s s' I S NW P0 NC. pose proof (NoCAS_back _ _ _ S NC) as NC0.
  destruct S; lets; cbn [pcs cs hs] in *.
  - (* ord *) destruct (Nat.eq_dec c 0) as [->|N]; [rewrite upd_o in P0; discriminate|].
    rewrite upd_n in P0 by congruence. destruct (I P0 NC0) as (A & Bf & C & D).
    split; [intros k0|split; [|split; [intros k0 O0|]]]; cbn [cs hs] in *; rewrite ?upd_n in * by congruence; auto.
    rewrite (eff_hs _ _ _ _ _ _ _ _ _ ltac:(eassumption)); [exact D|]. subst. apply insc; auto.
  - (* skip *) destruct (Nat.eq_dec c 0) as [->|N]; [rewrite upd_o in P0; discriminate|].
    rewrite upd_n in P0 by congruence. destruct (I P0 NC0) as (A & Bf & C & D).
    split; [intros k0|split; [|split; [intros k0 O0|]]]; cbn [cs hs] in *; rewrite ?upd_n in * by congruence; auto.
  - (* early *) destruct (Nat.eq_dec c 0) as [->|N].
    + exfalso. pose proof (I P0 NC0) as Qs. pose proof Qs as (A & _).
      match goal with X : early_ok _ _ _ _ _ _ _ _ _ |- _ => rewrite P0 in X; pose proof (early0 s _ _ _ _ _ Qs X) as -> end.
      apply (NW 0 k); auto; cbn [cs]; rewrite upd_o; cbn [oc ai]; rewrite upd_o; [discriminate|reflexivity].
    + destruct (I P0 NC0) as (A & Bf & C & D).
      split; [intros k0|split; [|split; [intros k0 O0|]]]; cbn [cs hs] in *; rewrite ?upd_n in * by congruence; auto.
      match goal with X : early_ok _ _ _ _ _ _ _ _ _ |- _ => destruct (X (fun _ _ => 0)) as (j & _ & F & _) end.
      cbv zeta in F. pose proof (first_at_eof _ _ _ _ _ _ _ _ F) as E. apply eof_shape in E as (E1 & E2).
      rewrite (eff_hs _ _ _ _ _ _ _ _ _ ltac:(eassumption)); [exact D|]. rewrite E1, E2. apply insc; auto.
  - (* match *) destruct (Nat.eq_dec c 0) as [->|N]; [rewrite upd_o in P0; discriminate|].
    rewrite upd_n in P0 by congruence. destruct (I P0 NC0) as (A & Bf & C & D).
    split; [intros k0|split; [|split; [intros k0 O0|]]]; cbn [cs hs] in *; rewrite ?upd_n in * by congruence; auto.
  - (* cread *) destruct (I P0 NC0) as (A & Bf & C & D). destruct (Nat.eq_dec c 0) as [->|N].
    + unfold Qc. cbn [cs hs]. rewrite !upd_o. cbn [oc fx oh rg]. rewrite P0 in *.
      match goal with X : early_okR _ _ _ _ _ _ _ _ _ _ |- _ => destruct (X f7) as (j & F & _) end. cbv zeta in F.
      assert (R0 : creg SPFH 0 (cs s 0) 0 (tp s 0) (bor (bd (cs s 0)) B) f7 0 = 7) by (rewrite creg0S by exact A; reflexivity).
      assert (E := F). unfold first_atR in E. cbn [plc first_in] in E. destruct E as (_ & E & _).
      destruct (eofRj _ _ _ _ R0 E) as (-> & -> & ->).
      match goal with X : forall f j, first_atR _ _ _ _ _ _ _ _ _ -> _ |- _ => destruct (X f7 2 F) as (Bv & _) end.
      rewrite Bf in Bv. subst bv.
      assert (Az : a = 0).
      { eapply eff_ld0; [eassumption| |reflexivity]. cbn [mof mH]. exact D. }
      subst a. split; [|split; [|split]]; auto.
      * intros k0 O. unfold upd. destruct (Nat.eqb_spec k0 k) as [->|Nk]; [reflexivity|]. apply C. rewrite upd_n in O by exact Nk. exact O.
      * rewrite (eff_hs _ _ _ _ _ _ _ _ _ ltac:(eassumption)); [exact D|left; reflexivity].
    + unfold Qc. cbn [cs hs]. rewrite !upd_n by congruence. split; [|split; [|split]]; auto.
      rewrite (eff_hs _ _ _ _ _ _ _ _ _ ltac:(eassumption)); [exact D|left; reflexivity].
  - (* cw *) destruct (Nat.eq_dec c 0) as [->|N]; [rewrite upd_o in P0; discriminate|].
    exfalso. subst. match goal with X : is_cas (ins _ _ _ _) = true |- _ => rewrite (proj2 (insc _ _ _ N)) in X; discriminate X end.
  - (* cwe *) destruct (Nat.eq_dec c 0) as [->|N].
    + exfalso. specialize (NC k). cbn [cs] in NC. rewrite upd_o in NC. cbn [oc ai] in NC. rewrite !upd_o in NC.
      discriminate (NC ltac:(discriminate)).
    + exfalso. match goal with X : early_okW _ _ _ _ _ _ _ _ _ _ _ |- _ => destruct (X (fun _ _ => 0)) as (j & _ & _ & E & _) end.
      cbv zeta in E. pose proof (proj1 (eof_cexp _ _ _ (fun _ => 0) E)) as Ce. rewrite (proj2 (insc _ _ _ N)) in Ce. discriminate Ce.
  - (* cfix *) destruct (fx_glob s c j b B o) as (Pc & _ & Hs). rewrite Pc in P0.
    destruct (I P0 NC0) as (A & Bf & C & D). destruct (Nat.eq_dec c 0) as [->|N].
    + exfalso. match goal with X : cfix_ok _ _ _ _ _ _ _ _ _ |- _ => pose proof X as Xc; destruct X as (v & Xv) end.
      destruct (Xv f7) as (Ci & _). cbv zeta in Ci. apply isc0 in Ci.
      rewrite P0 in Xc. exact (SPFH_nofix (cs s 0) _ j b B o Ci A Xc).
    + split; [|split; [|split]].
      * intros k. rewrite (proj1 (fx_cs_same s c j b B o 0 k)). apply A.
      * rewrite fx_fx by congruence. exact Bf.
      * intros k O. rewrite (proj2 (proj2 (fx_cs_same s c j b B o 0 k))) in O.
        rewrite fx_rg by (left; congruence). apply C. exact O.
      * rewrite Hs. exact D.
Qed.

Lemma Q_run : forall s, runD SPFH s -> Q s.
Proof.
  intros s R. induction R as [|s s' R IH S NW].
  - intros _ _. split; [intros k; reflexivity|split; [reflexivity|split; [intros k O; exfalso; apply O; reflexivity|reflexivity]]].
  - eapply Q_step; eauto.
Qed.

Print Assumptions Q_run.
