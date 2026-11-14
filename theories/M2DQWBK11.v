(* Part 11: A's steps are simulated, keeping KR (a copy of M2DQWBStep.sim_step with
   the knowledge relation added). *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Cont M2WBReg M2WBRel M2WBEff M2WBSim M2DQWBK1 M2DQWBK2 M2DQWBK3 M2DQWBK7 M2DQWBK8 M2DQWBK9 M2DQWBK10.
Require Import M2DQWB M2DQWBStep M2DQWBK3Q.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQShim.

Section Step.
Variables (p : prog) (W : wf p) (sw : nat -> option (cell -> option nat)) (sW sA : st).
Hypothesis RA : run p sA.
Hypothesis R : rel sw sW sA.
Variable Fk : Prop.
Variable Good : nat -> Prop.
Hypothesis KK : KR Fk Good sw sW sA.

Lemma POW : forall c, pend_ok (cs sW c) (pcs sW c).
Proof.
  intros c. pose proof (pend_ok_of p sA c (Inv1_run p sA RA)) as H.
  destruct (r_cr sw sW sA R c) as ((rv' & rw' & P & A & R' & O & Og & E) & _). rewrite E, (r_pcs sw sW sA R) in H.
  exact H.
Qed.


Lemma rel_cfix : forall c o j b B, rel sw (scfix0 (sflp sW c o b) c j b B) (scfix0 (sflp sA c o b) c j b B).
Proof.
  intros c o j b B. apply (rel_nomem2 sw sW sA R).
  - destruct o as [k0|]; [destruct b|]; reflexivity.
  - destruct o as [k0|]; [destruct b|]; reflexivity.
  - destruct o as [k0|]; [destruct b|]; exact (r_pcs sw sW sA R).
  - destruct o as [k0|]; [destruct b|]; exact (r_tp sw sW sA R).
  - destruct o as [k0|]; [destruct b|]; exact (r_cm sw sW sA R).
  - destruct o as [k0|]; [destruct b|]; reflexivity.
  - destruct o as [k0|]; [destruct b|]; reflexivity.
  - destruct o as [k0|]; [destruct b|]; reflexivity.
  - destruct o as [k0|]; [destruct b|]; reflexivity.
  - intros c'. rewrite !cs_cfix. destruct (Nat.eqb c' c); [apply crel_cfix|]; apply (r_cr sw sW sA R).
  - intros c' k x w E. rewrite cs_cfix in E. destruct (Nat.eqb c' c); [|apply (i_rw sw sW sA R c' k x w E)].
    destruct o as [k0|]; [destruct b|]; apply (i_rw sw sW sA R c k x w E).
  - intros c' k t0 E. rewrite cs_cfix in E. destruct (Nat.eqb c' c); [|apply (i_oh sw sW sA R c' k t0 E)].
    destruct o as [k0|]; [destruct b|]; apply (i_oh sw sW sA R c k t0 E).
Qed.

Lemma wrote_pi : forall t xs u uA w x, sw t = None -> (forall x, uA x = pi sw x (u x)) ->
  wrote t xs uA w x = pi sw x (wrote t xs u w x).
Proof.
  intros t xs u uA w x St Hu. unfold wrote. destruct w; [|apply Hu].
  destruct (existsb (Nat.eqb x) xs); [simpl; rewrite St; reflexivity|reflexivity].
Qed.

Lemma wrote_in : forall t xs u w x w0,
  wrote t xs u w x = Some w0 -> (w = true /\ w0 = t /\ In x xs) \/ (w = false /\ u x = Some w0).
Proof.
  intros t xs u w x w0 E. unfold wrote in E. destruct w.
  - destruct (existsb (Nat.eqb x) xs) eqn:Ex; [|discriminate]. injection E as <-. left. split; [reflexivity|split; [reflexivity|]].
    apply existsb_exists in Ex. destruct Ex as (y & Iy & Ey). apply Nat.eqb_eq in Ey. subst. exact Iy.
  - right. split; [reflexivity|exact E].
Qed.


Ltac aprem Ecs Ep :=
  cbv zeta; try (rewrite ?Ecs; rewrite ?Ep; cbn [rg oc oh ai bd fx rw rv vP vA vR vO vOg cc_x]; first [reflexivity|assumption]).

Theorem sim_stepKA : forall s', M2Model.step p sW s' -> fhsafe sW s' -> (Fk -> HB1 Good s') -> (Fk -> HB2 Good s') ->
  exists sA', M2Model.step p sA sA' /\ rel sw s' sA' /\ KR Fk Good sw s' sA'.
Proof.
  intros s' H FH HB1s HB2s. pose proof (tmW p Fk Good sw sW sA RA R KK) as TL. inversion H; subst; cbv zeta in *.
  - (* s_ord *)
    destruct (r_cr sw sW sA R c) as ((rv' & rw' & P & A & R' & O & Og & Ecs) & Hrv & Hrw).
    destruct (eff_transfer sw sW sA c R _ _ _ _ _ _ _ _ H8) as (m'A & KA & uA & Ea & Hu & Hh & Htk & Hs & Hrd & Hwr).
    assert (Ea' : eff (tm sA) (ins p c k (rg cc)) (rg (cs sA c)) (mof sA c) m'A a KA uA w)
      by (rewrite (r_tm sw sW sA R), Ecs; exact Ea).
    eexists; split; [|split].
    + refine (s_ord p sA c (ins p c k (rg cc)) m'A a KA uA w _ _ _ _ _ _ _ _ Ea' _);
        cbv zeta; try (rewrite ?Ecs; rewrite ?(r_pcs sw sW sA R); cbn [rg oc oh bd cc_x]; first [reflexivity|assumption]).
      * intros x b Hb Ix Fb. rewrite Ecs, (r_pcs sw sW sA R) in Hb, Fb. cbn [bd rg cc_x] in Hb, Fb.
        rewrite (Hrw b x), (Hu x), (H7 x b Hb Ix Fb). reflexivity.
    + assert (Hs' : (mV m' = wv sW /\ mV m'A = wv sA /\ forall x, mH m' x = hs sW x) \/
        exists V xs, mV m' = upd (wv sW) (tm sW) V /\ mV m'A = upd (wv sA) (tm sW) V /\ places (hs sW) xs (tm sW) (mH m')) by exact Hs.
      eapply (rel_mem sw sW sA R _ _ c _ _ m' m'A Hh Hs' FH);
        [ reflexivity | reflexivity
        | cbn [pcs]; rewrite (r_pcs sw sW sA R); reflexivity
        | cbn [tp]; rewrite (r_tp sw sW sA R), (r_pcs sw sW sA R); reflexivity
        | cbn [cm]; rewrite (r_cm sw sW sA R), (r_pcs sw sW sA R), (r_tm sw sW sA R); reflexivity
        | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | | | ].
      * split; [|split].
        -- rewrite ?Ecs. rewrite (r_pcs sw sW sA R), (r_tm sw sW sA R). do 7 eexists. reflexivity.
        -- intros k' x. cbn [rv]. rewrite (r_pcs sw sW sA R). fold k. unfold upd. destruct (Nat.eqb k' k) eqn:E1; cbv iota beta.
           ++ apply Hrd.
           ++ apply Hrv.
        -- intros k' x. cbn [rw]. rewrite (r_pcs sw sW sA R), (r_tm sw sW sA R). fold k. unfold upd. destruct (Nat.eqb k' k) eqn:E1; cbv iota beta.
           ++ apply (wrote_pi _ _ _ _ _ _ (i_sw sw sW sA R _ (le_n _)) Hu).
           ++ apply Hrw.
      * intros k' x w0 E. cbn [rw] in E. unfold upd in E. destruct (Nat.eqb k' k) eqn:E1; cbv iota beta in E.
        -- destruct (wrote_in _ _ _ _ _ _ E) as [(Hw & -> & Ix)|(Hw & Eu)].
           ++ apply (Hwr Hw x Ix).
           ++ apply (mem_old sW sA m' m'A Hs' x). apply (Htk x w0 Eu).
        -- apply (mem_old sW sA m' m'A Hs' x). apply (i_rw sw sW sA R c k' x w0 E).
      * intros k' t0 E. cbn [oh] in E. pose proof (i_oh sw sW sA R c k' t0 E). lia.
    + destruct (HB_evsxF Fk Good sW c (pcs sW c) _ m' a K _ _ _ _ _ _ _ TL ltac:(eassumption) (pc2_upd (pcs sW) c) HB1s HB2s) as (HG1 & HG2 & _).
      eapply (KR_evs p Fk Good sw sW sA); first [exact RA|exact R|exact KK|exact (f_equal (fun f => f c) (r_pcs sw sW sA R))|reflexivity|eassumption|exact (le_n _)
        |exact (pc1_upd (pcs sW) c)|exact (pc2_upd (pcs sW) c)|exact FH|exact HG1|exact HG2|(intros Z; exfalso; apply Z; assumption)|(intros _; assumption)|idtac].
  - (* s_skip *)
    destruct (r_cr sw sW sA R c) as ((rv' & rw' & P & A & R' & O & Og & Ecs) & Hrv & Hrw).
    eexists; split; [|split].
    + refine (s_skip p sA c (ins p c k (rg cc)) _ _ _ _ _ _ _ _); aprem Ecs (r_pcs sw sW sA R).
    + eapply (rel_nomem sw sW sA R _ _ c _ _);
        [ reflexivity | reflexivity
        | cbn [pcs]; rewrite (r_pcs sw sW sA R); reflexivity
        | cbn [tp]; rewrite (r_tp sw sW sA R), (r_pcs sw sW sA R); reflexivity
        | cbn [cm]; rewrite (r_cm sw sW sA R), (r_pcs sw sW sA R), (r_tm sw sW sA R); reflexivity
        | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | | | ].
      * split; [|split].
        -- rewrite ?Ecs. rewrite (r_pcs sw sW sA R). do 7 eexists. reflexivity.
        -- intros k' x. cbn [rv]. apply Hrv.
        -- intros k' x. cbn [rw]. apply Hrw.
      * intros k' x w0 E. cbn [rw] in E. apply (i_rw sw sW sA R c k' x w0 E).
      * intros k' t0 E. cbn [oh] in E. exact (i_oh sw sW sA R c k' t0 E).
    + eapply (KR_pass p Fk Good sw sW sA c RA R KK).
      * intros Z. pose proof (xex_FF cc (rg cc) k) as X. rewrite <- Z in X. congruence.
      * intros t f e Sw E Ec Ek'. destruct (i_etW p Fk Good sw sW sA RA R KK t e E) as [_ Ot]. rewrite Ec, Ek' in Ot.
        assert (Oc0 : oc (cs sW c) (pcs sW c) = None) by assumption.
        destruct (eh e) eqn:Eh; [|congruence].
        destruct (crel_eq p Fk Good sw sW sA RA R KK c) as (Oc & Oh & Ai & _).
        assert (Oh' : oh (cs sA c) (pcs sA c) = Some t) by (rewrite Oh, (r_pcs sw sW sA R); exact Ot).
        assert (Oc' : oc (cs sA c) (pcs sA c) = None) by (rewrite Oc, (r_pcs sw sW sA R); assumption).
        destruct (i_half p sA (Inv1_run p sA RA) c (pcs sA c) t Oc' Oh' (le_n _)) as (_ & (xs0 & Ax) & _).
        rewrite Ai, (r_pcs sw sW sA R) in Ax.
        assert (Er : eofR (ins p c k (rg cc)) (rg cc) = eofR (ai (cs sW c) (pcs sW c)) (rg cc)) by (match goal with Hq : oh _ _ <> None -> eofR _ _ = _ |- _ => apply Hq; change (oh (cs sW c) (pcs sW c) <> None); rewrite Ot; discriminate end).
        rewrite Ax in Er. cbn in Er. exact (proj2 (eofR_exec_tied_i _ _ _ _ Er)).
  - (* s_early *)
    destruct (r_cr sw sW sA R c) as ((rv' & rw' & P & A & R' & O & Og & Ecs) & Hrv & Hrw).
    assert (Hrv' : forall j0 x, rv' j0 x = rv (cs sW c) j0 x) by (intros j0 x; specialize (Hrv j0 x); rewrite Ecs in Hrv; exact Hrv).
    assert (Hrw' : forall k0 x, rw' k0 x = pi sw x (rw (cs sW c) k0 x)) by (intros k0 x; specialize (Hrw k0 x); rewrite Ecs in Hrw; exact Hrw).
    destruct (eff_transfer sw sW sA c R _ _ _ _ _ _ _ _ H5) as (m'A & KA & uA & Ea & Hu & Hh & Htk & Hs & Hrd & Hwr).
    assert (Ea' : eff (tm sA) (inst_of d) (rg (cs sA c)) (mof sA c) m'A a KA uA w)
      by (rewrite (r_tm sw sW sA R), Ecs; exact Ea).
    eexists; split; [|split].
    + refine (s_early p sA c k d B m'A a KA uA w _ _ _ _ _ Ea' _); cbv zeta;
        try (rewrite ?Ecs; rewrite ?(r_pcs sw sW sA R); cbn [rg oc oh bd cc_x]; first [reflexivity|assumption]).
      * rewrite Ecs, (r_pcs sw sW sA R), (r_tp sw sW sA R), (r_tm sw sW sA R). cbn [bd cc_x].
        exact (early_ok_x p W c (cs sW c) (pcs sW c) (tp sW c) (POW c) rv' rw' P A R' O Og (pi sw) Hrv' Hrw' (tm sW) d u uA B Hu H4).
      * intros f j0 Fj. rewrite Ecs, (r_pcs sw sW sA R), (r_tp sw sW sA R), (r_tm sw sW sA R) in Fj. cbn [bd cc_x] in Fj.
        apply (first_at_X p c (cs sW c) (pcs sW c) rv' rw' P A R' O Og) in Fj.
        apply (first_at_agree p W c (cs sW c) (pcs sW c) _ _ (tm sW) d j0 (agX' p c (cs sW c) (pcs sW c) (tp sW c) rv' rw' P A R' O Og Hrv' _ _ j0)) in Fj.
        rewrite Ecs. cbn [fx rg cc_x]. exact (H6 f j0 Fj).
    + assert (Hs' : (mV m' = wv sW /\ mV m'A = wv sA /\ forall x, mH m' x = hs sW x) \/
        exists V xs, mV m' = upd (wv sW) (tm sW) V /\ mV m'A = upd (wv sA) (tm sW) V /\ places (hs sW) xs (tm sW) (mH m')) by exact Hs.
      eapply (rel_mem sw sW sA R _ _ c _ _ m' m'A Hh Hs' FH);
        [ reflexivity | reflexivity
        | cbn [pcs]; exact (r_pcs sw sW sA R)
        | cbn [tp]; rewrite (r_tp sw sW sA R); reflexivity
        | cbn [cm]; exact (r_cm sw sW sA R)
        | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | | | ].
      * split; [|split].
        -- rewrite ?Ecs. rewrite (r_tm sw sW sA R). do 7 eexists. reflexivity.
        -- intros k' x. cbn [rv]. unfold upd. destruct (Nat.eqb k' k) eqn:E1; cbv iota beta.
           ++ apply Hrd.
           ++ apply Hrv.
        -- intros k' x. cbn [rw]. rewrite (r_tm sw sW sA R). unfold upd. destruct (Nat.eqb k' k) eqn:E1; cbv iota beta.
           ++ apply (wrote_pi _ _ _ _ _ _ (i_sw sw sW sA R _ (le_n _)) Hu).
           ++ apply Hrw.
      * intros k' x w0 E. cbn [rw] in E. unfold upd in E. destruct (Nat.eqb k' k) eqn:E1; cbv iota beta in E.
        -- destruct (wrote_in _ _ _ _ _ _ E) as [(Hw & -> & Ix)|(Hw & Eu)].
           ++ apply (Hwr Hw x Ix).
           ++ apply (mem_old sW sA m' m'A Hs' x). apply (Htk x w0 Eu).
        -- apply (mem_old sW sA m' m'A Hs' x). apply (i_rw sw sW sA R c k' x w0 E).
      * intros k' t0 E. cbn [oh] in E. pose proof (i_oh sw sW sA R c k' t0 E). lia.
    + destruct (HB_evsxF Fk Good sW c k _ m' a K _ _ _ _ _ _ _ TL ltac:(eassumption) (pc2_id (pcs sW) c k) HB1s HB2s) as (HG1 & HG2 & _).
      eapply (KR_evs p Fk Good sw sW sA); first [exact RA|exact R|exact KK|reflexivity|eassumption|lia
        |exact (pc1_id (pcs sW))|exact (pc2_id (pcs sW) c k)|exact FH|exact HG1|exact HG2|(intros Z; exfalso; apply Z; assumption)|(intros _; assumption)|idtac].
  - (* s_match *)
    destruct (r_cr sw sW sA R c) as ((rv' & rw' & P & A & R' & O & Og & Ecs) & Hrv & Hrw).
    eexists; split; [|split].
    + refine (s_match p sA c d _ _ _ _ _ _ _); aprem Ecs (r_pcs sw sW sA R).
    + eapply (rel_nomem sw sW sA R _ _ c _ _);
        [ reflexivity | reflexivity
        | cbn [pcs]; rewrite (r_pcs sw sW sA R); reflexivity
        | cbn [tp]; exact (r_tp sw sW sA R)
        | cbn [cm]; rewrite (r_cm sw sW sA R), (r_pcs sw sW sA R), (r_tm sw sW sA R); reflexivity
        | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | | | ].
      * split; [|split].
        -- rewrite ?Ecs. rewrite (r_pcs sw sW sA R). do 7 eexists. reflexivity.
        -- intros k' x. cbn [rv]. apply Hrv.
        -- intros k' x. cbn [rw]. apply Hrw.
      * intros k' x w0 E. cbn [rw] in E. apply (i_rw sw sW sA R c k' x w0 E).
      * intros k' t0 E. cbn [oh] in E. exact (i_oh sw sW sA R c k' t0 E).
    + eapply (KR_pass p Fk Good sw sW sA c RA R KK).
      * exact (eof_notFF _ _ _ ltac:(eassumption)).
      * intros t f e Sw E Ec Ek'. destruct (w_swc Fk Good sw sW sA KK t f Sw) as (e' & E' & Cc). rewrite E in E'. injection E' as <-.
        rewrite Ec, Ek' in Cc. assert (Hd : ai (cs sW c) (pcs sW c) = inst_of d) by assumption. rewrite Hd in Cc.
        assert (He : eof (ins p c (pcs sW c) (rg (cs sW c))) (rg (cs sW c)) = Some d) by assumption.
        change (is_cas (ins p c (pcs sW c) (rg (cs sW c))) = true). rewrite <- (eof_iscas _ _ _ He). exact Cc.
  - (* s_cread *)
    destruct m.
    destruct (r_cr sw sW sA R c) as ((rv' & rw' & P & A & R' & O & Og & Ecs) & Hrv & Hrw).
    assert (Hrv' : forall j0 x, rv' j0 x = rv (cs sW c) j0 x) by (intros j0 x; specialize (Hrv j0 x); rewrite Ecs in Hrv; exact Hrv).
    assert (Hrw' : forall k0 x, rw' k0 x = pi sw x (rw (cs sW c) k0 x)) by (intros k0 x; specialize (Hrw k0 x); rewrite Ecs in Hrw; exact Hrw).
    destruct (eff_transfer sw sW sA c R _ _ _ _ _ _ _ _ H5) as (m'A & KA & uA & Ea & Hu & Hh & Htk & Hs & Hrd & Hwr).
    assert (Ea' : eff (tm sA) (ILd Plain xs (fun _ => true)) (rg (cs sA c)) (mof sA c) m'A a KA uA w)
      by (rewrite (r_tm sw sW sA R), Ecs; exact Ea).
    eexists; split; [|split].
    + refine (s_cread p sA c k Plain xs B m'A a KA uA w bv _ _ _ _ _ Ea' _); cbv zeta;
        try (rewrite ?Ecs; rewrite ?(r_pcs sw sW sA R); cbn [rg oc oh bd cc_x]; first [reflexivity|assumption]).
      * rewrite Ecs, (r_pcs sw sW sA R), (r_tp sw sW sA R), (r_tm sw sW sA R). cbn [bd cc_x].
        exact (early_okR_x p W c (cs sW c) (pcs sW c) (tp sW c) (POW c) rv' rw' P A R' O Og (pi sw) Hrv' Hrw' (tm sW) Plain xs u uA B Hu H4).
      * intros f j0 Fj. rewrite Ecs, (r_pcs sw sW sA R), (r_tp sw sW sA R), (r_tm sw sW sA R) in Fj. cbn [bd cc_x] in Fj.
        apply (first_atR_X p c (cs sW c) (pcs sW c) rv' rw' P A R' O Og) in Fj.
        unfold first_atR in Fj.
        apply (plc_agree p W c (cs sW c) (pcs sW c) _ _ _ (tm sW) (TH Plain xs) j0 (agX' p c (cs sW c) (pcs sW c) (tp sW c) rv' rw' P A R' O Og Hrv' _ _ j0)) in Fj.
        destruct (H6 f j0 Fj) as [Hm Hx]. split.
        -- rewrite Ecs. cbn [fx cc_x]. exact Hm.
        -- destruct (ins_agree p W c j0 (creg p c (cs sW c) (pcs sW c) (tp sW c) (bor (bd (cs sW c)) B) f)
             (creg p c (cc_x (cs sW c) rv' rw' P A R' O Og) (pcs sW c) (tp sW c) (bor (bd (cs sW c)) B) f)
             (agX p c (cs sW c) (pcs sW c) (tp sW c) rv' rw' P A R' O Og Hrv' _ _ j0)) as [Ei Ev].
           pose proof (fxok_ieval _ _ _ _ _ _ Ev Hx) as Hx'. rewrite Ei in Hx'. rewrite Ecs, (r_pcs sw sW sA R), (r_tp sw sW sA R). cbn [bd cc_x]. exact Hx'.
    + assert (Hs' : (mV m' = wv sW /\ mV m'A = wv sA /\ forall x, mH m' x = hs sW x) \/
        exists V xs0, mV m' = upd (wv sW) (tm sW) V /\ mV m'A = upd (wv sA) (tm sW) V /\ places (hs sW) xs0 (tm sW) (mH m')) by exact Hs.
      eapply (rel_mem sw sW sA R _ _ c _ _ m' m'A Hh Hs' FH);
        [ reflexivity | reflexivity
        | cbn [pcs]; exact (r_pcs sw sW sA R)
        | cbn [tp]; rewrite (r_tp sw sW sA R); reflexivity
        | cbn [cm]; exact (r_cm sw sW sA R)
        | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | | | ].
      * split; [|split].
        -- rewrite ?Ecs. rewrite (r_tm sw sW sA R). do 7 eexists. reflexivity.
        -- intros k' x. cbn [rv]. unfold upd. destruct (Nat.eqb k' k) eqn:E1; cbv iota beta.
           ++ apply Hrd.
           ++ apply Hrv.
        -- intros k' x. cbn [rw]. rewrite (r_tm sw sW sA R). unfold upd. destruct (Nat.eqb k' k) eqn:E1; cbv iota beta.
           ++ apply (wrote_pi _ _ _ _ _ _ (i_sw sw sW sA R _ (le_n _)) Hu).
           ++ apply Hrw.
      * intros k' x w0 E. cbn [rw] in E. unfold upd in E. destruct (Nat.eqb k' k) eqn:E1; cbv iota beta in E.
        -- destruct (wrote_in _ _ _ _ _ _ E) as [(Hw & -> & Ix)|(Hw & Eu)].
           ++ apply (Hwr Hw x Ix).
           ++ apply (mem_old sW sA m' m'A Hs' x). apply (Htk x w0 Eu).
        -- apply (mem_old sW sA m' m'A Hs' x). apply (i_rw sw sW sA R c k' x w0 E).
      * intros k' t0 E. cbn [oh] in E. unfold upd in E. destruct (Nat.eqb k' k) eqn:E1; cbv iota beta in E.
        -- injection E as <-. lia.
        -- pose proof (i_oh sw sW sA R c k' t0 E). lia.
    + destruct (HB_sreadF Fk Good sW c k Plain xs B m' a K u w bv TL ltac:(eassumption) HB1s HB2s) as (HG1 & _).
      eapply (KR_sread p Fk Good sw sW sA); first [exact RA|exact R|exact KK|reflexivity|eassumption|exact HG1|idtac].
  - (* s_cw *)
    destruct (r_cr sw sW sA R c) as ((rv' & rw' & P & A & R' & O & Og & Ecs) & Hrv & Hrw).
    assert (Hu0 : forall x, rw (cs sA c) (pcs sA c) x = pi sw x (u x))
      by (intros x; rewrite (r_pcs sw sW sA R); apply Hrw).
    destruct (eff_transfer_cas sw sW sA c R _ _ _ _ _ _ _ H9 H1 _ Hu0) as (m'A & KA & Ea & Hu & Hh & Htk & Hs & Hrd & Hwr).
    assert (Ea' : eff (tm sA) (ins p c k0 (rg cc0)) (rg (cs sA c)) (mof sA c) m'A a KA (rw (cs sA c) (pcs sA c)) true)
      by (rewrite (r_tm sw sW sA R); assert (Er : rg (cs sA c) = rg (cs sW c)) by (rewrite Ecs; reflexivity); rewrite Er; exact Ea).
    assert (Hrd' := Hrd). assert (Hu' := Hu). rewrite (r_pcs sw sW sA R) in Hrd', Hu'.
    eexists; split; [|split].
    + refine (s_cw p sA c t1 (ins p c k0 (rg cc0)) m'A a KA true _ _ _ _ _ _ _ _ _ Ea' eq_refl _); cbv zeta;
        try (rewrite ?Ecs; rewrite ?(r_pcs sw sW sA R); cbn [rg oc oh ai bd fx cc_x]; first [reflexivity|assumption]).
    + assert (Hs' : (mV m' = wv sW /\ mV m'A = wv sA /\ forall x, mH m' x = hs sW x) \/
        exists V xs0, mV m' = upd (wv sW) (tm sW) V /\ mV m'A = upd (wv sA) (tm sW) V /\ places (hs sW) xs0 (tm sW) (mH m')) by exact Hs.
      eapply (rel_mem sw sW sA R _ _ c _ _ m' m'A Hh Hs' FH);
        [ reflexivity | reflexivity
        | cbn [pcs]; rewrite (r_pcs sw sW sA R); reflexivity
        | cbn [tp]; rewrite (r_tp sw sW sA R), (r_pcs sw sW sA R); reflexivity
        | cbn [cm]; rewrite (r_cm sw sW sA R), (r_pcs sw sW sA R), (r_tm sw sW sA R); reflexivity
        | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | | | ].
      * split; [|split].
        -- rewrite ?Ecs. rewrite (r_pcs sw sW sA R), (r_tm sw sW sA R). do 7 eexists. reflexivity.
        -- intros k' x. cbn [rv]. rewrite (r_pcs sw sW sA R). fold k0. unfold upd. destruct (Nat.eqb k' k0) eqn:E1; cbv iota beta.
           ++ apply Hrd'.
           ++ apply Hrv.
        -- intros k' x. cbn [rw]. rewrite (r_pcs sw sW sA R), (r_tm sw sW sA R). fold k0. unfold upd. destruct (Nat.eqb k' k0) eqn:E1; cbv iota beta.
           ++ apply (wrote_pi _ _ _ _ _ _ (i_sw sw sW sA R _ (le_n _)) Hu').
           ++ apply Hrw.
      * intros k' x w0 E. cbn [rw] in E. unfold upd in E. destruct (Nat.eqb k' k0) eqn:E1; cbv iota beta in E.
        -- destruct (wrote_in _ _ _ _ _ _ E) as [(Hw & -> & Ix)|(Hw & Eu)].
           ++ apply (Hwr Hw x Ix).
           ++ discriminate.
        -- apply (mem_old sW sA m' m'A Hs' x). apply (i_rw sw sW sA R c k' x w0 E).
      * intros k' t0 E. cbn [oh] in E. pose proof (i_oh sw sW sA R c k' t0 E). lia.
    + destruct (HB_evsxF Fk Good sW c (pcs sW c) _ m' a K _ _ _ _ _ _ _ TL ltac:(eassumption) (pc2_upd (pcs sW) c) HB1s HB2s) as (HG1 & HG2 & _).
      eapply (KR_evs p Fk Good sw sW sA); first [exact RA|exact R|exact KK|exact (f_equal (fun f => f c) (r_pcs sw sW sA R))|reflexivity|eassumption|exact (le_n _)
        |exact (pc1_upd (pcs sW) c)|exact (pc2_upd (pcs sW) c)|exact FH|exact HG1|exact HG2|(intros Z; exfalso; apply Z; assumption)|(intros _; assumption)|idtac].
  - (* s_cwe *)
    destruct (r_cr sw sW sA R c) as ((rv' & rw' & P & A & R' & O & Og & Ecs) & Hrv & Hrw).
    assert (Hrv' : forall j0 x, rv' j0 x = rv (cs sW c) j0 x) by (intros j0 x; specialize (Hrv j0 x); rewrite Ecs in Hrv; exact Hrv).
    assert (Hu0 : forall x, rw (cs sA c) k x = pi sw x (u x)) by (intros x; apply Hrw).
    destruct (eff_transfer_cas sw sW sA c R _ _ _ _ _ _ _ H7 eq_refl _ Hu0) as (m'A & KA & Ea & Hu & Hh & Htk & Hs & Hrd & Hwr).
    assert (Ea' : eff (tm sA) (inst_of d) (rg (cs sA c)) (mof sA c) m'A a KA (rw (cs sA c) k) true)
      by (rewrite (r_tm sw sW sA R); assert (Er : rg (cs sA c) = rg (cs sW c)) by (rewrite Ecs; reflexivity); rewrite Er; exact Ea).
    eexists; split; [|split].
    + refine (s_cwe p sA c k t1 xs ev nv B m'A a KA true _ _ _ _ _ _ _ Ea' eq_refl _); cbv zeta;
        try (rewrite ?Ecs; rewrite ?(r_pcs sw sW sA R); cbn [rg oc oh ai bd fx cc_x]; first [reflexivity|assumption]).
      * rewrite Ecs, (r_pcs sw sW sA R), (r_tp sw sW sA R), (r_tm sw sW sA R). cbn [bd cc_x].
        exact (early_okW_x p W c (cs sW c) (pcs sW c) (tp sW c) rv' rw' P A R' O Og Hrv' (tm sW) t1 Plain xs d B H5).
      * intros f j0 Fj. rewrite Ecs, (r_pcs sw sW sA R), (r_tp sw sW sA R) in Fj. cbn [bd cc_x] in Fj.
        apply (first_atR_X p c (cs sW c) (pcs sW c) rv' rw' P A R' O Og) in Fj.
        unfold first_atR in Fj.
        apply (plc_agree p W c (cs sW c) (pcs sW c) _ _ _ t1 (TH Plain xs) j0 (agX' p c (cs sW c) (pcs sW c) (tp sW c) rv' rw' P A R' O Og Hrv' _ _ j0)) in Fj.
        rewrite Ecs. cbn [fx rg cc_x]. exact (H9 f j0 Fj).
    + assert (Hs' : (mV m' = wv sW /\ mV m'A = wv sA /\ forall x, mH m' x = hs sW x) \/
        exists V xs0, mV m' = upd (wv sW) (tm sW) V /\ mV m'A = upd (wv sA) (tm sW) V /\ places (hs sW) xs0 (tm sW) (mH m')) by exact Hs.
      eapply (rel_mem sw sW sA R _ _ c _ _ m' m'A Hh Hs' FH);
        [ reflexivity | reflexivity
        | cbn [pcs]; exact (r_pcs sw sW sA R)
        | cbn [tp]; rewrite (r_tp sw sW sA R); reflexivity
        | cbn [cm]; exact (r_cm sw sW sA R)
        | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | | | ].
      * split; [|split].
        -- rewrite ?Ecs. rewrite (r_tm sw sW sA R). do 7 eexists. reflexivity.
        -- intros k' x. cbn [rv]. unfold upd. destruct (Nat.eqb k' k) eqn:E1; cbv iota beta.
           ++ apply Hrd.
           ++ apply Hrv.
        -- intros k' x. cbn [rw]. rewrite (r_tm sw sW sA R). unfold upd. destruct (Nat.eqb k' k) eqn:E1; cbv iota beta.
           ++ apply (wrote_pi _ _ _ _ _ _ (i_sw sw sW sA R _ (le_n _)) Hu).
           ++ apply Hrw.
      * intros k' x w0 E. cbn [rw] in E. unfold upd in E. destruct (Nat.eqb k' k) eqn:E1; cbv iota beta in E.
        -- destruct (wrote_in _ _ _ _ _ _ E) as [(Hw & -> & Ix)|(Hw & Eu)].
           ++ apply (Hwr Hw x Ix).
           ++ discriminate.
        -- apply (mem_old sW sA m' m'A Hs' x). apply (i_rw sw sW sA R c k' x w0 E).
      * intros k' t0 E. cbn [oh] in E. pose proof (i_oh sw sW sA R c k' t0 E). lia.
    + destruct (HB_evsxF Fk Good sW c k _ m' a K _ _ _ _ _ _ _ TL ltac:(eassumption) (pc2_id (pcs sW) c k) HB1s HB2s) as (HG1 & HG2 & _).
      eapply (KR_evs p Fk Good sw sW sA); first [exact RA|exact R|exact KK|reflexivity|eassumption|lia
        |exact (pc1_id (pcs sW))|exact (pc2_id (pcs sW) c k)|exact FH|exact HG1|exact HG2|(intros Z; exfalso; apply Z; assumption)|(intros _; assumption)|idtac].
  - (* s_cfix *)
    destruct (r_cr sw sW sA R c) as ((rv' & rw' & P & A & R' & O & Og & Ecs) & Hrv & Hrw).
    assert (Hrv' : forall j0 x, rv' j0 x = rv (cs sW c) j0 x) by (intros j0 x; specialize (Hrv j0 x); rewrite Ecs in Hrv; exact Hrv).
    eexists; split; [|split].
    + refine (s_cfix p sA c j b B o _ _ _); cbv zeta.
      * rewrite (r_pcs sw sW sA R). assumption.
      * rewrite Ecs. cbn [fx cc_x]. assumption.
      * rewrite Ecs, (r_pcs sw sW sA R), (r_tp sw sW sA R).
        exact (cfix_ok_x p c (cs sW c) (pcs sW c) (tp sW c) j b B o rv' rw' P A R' O Og W (POW c) Hrv' H2).
    + apply rel_cfix.
    + apply (KR_cfix p Fk Good sw sW sA c j b B o RA R KK).
Qed.
(* M2DQ: the steps of M2Model by sim_stepKA, the record fixes by the same fix of the image *)
Theorem sim_stepK : forall s', step p sW s' -> fhsafe sW s' -> (Fk -> HB1 Good s') -> (Fk -> HB2 Good s') ->
  exists sA', step p sA sA' /\ rel sw s' sA' /\ KR Fk Good sw s' sA'.
Proof.
  intros s' H FH HB1s HB2s. pose proof sim_stepKA as SK. destruct H as [s0 s1 St V|s0 c k B Rf Nc|s0 c j k B Lj Fj Sf].
  - destruct (SK s1 St FH HB1s HB2s) as (sA' & StA & Rl & K'). exists sA'.
    split; [apply q_old; [exact StA|exact (nowhole_rel sw s0 sA sw s1 sA' R Rl V)]|auto].
  - exists (sbd (scfail sA c k) c B). split; [exact (simQ_rfix p W sw s0 sA c k B RA R Rf Nc)|].
    split; [exact (rel_rfix sw s0 sA c k B R)|exact (KR_rfx Fk Good sw s0 sA _ _ KK (rfx_rfix s0 c k B) (rfx_rfix sA c k B))].
  - exists (scfix0 sA c j true B). split; [exact (simQ_sfix p W sw s0 sA c j k B RA R Lj Fj Sf)|].
    split; [exact (M2DQWBStep.rel_cfix sw s0 sA R c None j true B)|exact (KR_rfx Fk Good sw s0 sA _ _ KK (rfx_sfix s0 c j B) (rfx_sfix sA c j B))].
Qed.
End Step.
