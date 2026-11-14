(* CASPDEP on M2DQ (port of M2CasPDepInst.v).
     CASPDEP: r0 = y; r1 = CAS((x, w), (7, 7), (r0, r0)); z = r1 || r = z; y = r || (x, w) = (7, 7)
   The original run already splits the CAS (s_cread, then s_cw): every step
   is a q_old step. Same outcome: CASPDEP_allowed_Q. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Lit M2Ev M2EvLit M2Oota M2CasSplitProof M2EvTimeProof M2DA M2DP M2DQ M2DQDec.
Require M2CasPDepInst.

(* runs of M2DQ built forward from q_old steps only (an M2Model step that
   satisfies nowhole); such a run is a runQ, and also a run of M2Model, which
   the evok and done tactics of the original script take *)
Inductive starV (p : prog) : M2Model.st -> M2Model.st -> Prop :=
| sv0 : forall s, starV p s s
| svS : forall s s1 t, step p s s1 -> nowhole s s1 -> starV p s1 t -> starV p s t.

Lemma starV_both : forall p s t, starV p s t -> star p s t /\ starQ p s t.
Proof.
  intros p s t H. induction H as [s|s s1 t S V _ [A B]].
  - split; [apply st0|apply sq0].
  - split; [exact (stS p s s1 t S A)|exact (sqS p s s1 t (q_old p s s1 S V) B)].
Qed.

Lemma startV : forall p (Q : M2Model.st -> Prop), (exists t, starV p sinit t /\ (run p t -> Q t)) ->
  exists t, runQ p t /\ Q t.
Proof.
  intros p Q (t & H & q). destruct (starV_both p sinit t H) as [A B]. exists t. split.
  - exact (starQ_run p sinit t (x0 p) B).
  - apply q. exact (star_run p sinit t (r0 p) A).
Qed.

Lemma fwdV : forall p s s1 (Q : M2Model.st -> Prop), step p s s1 -> nowhole s s1 ->
  (exists t, starV p s1 t /\ Q t) -> exists t, starV p s t /\ Q t.
Proof. intros p s s1 Q S V (t & H & q). exists t. split; [exact (svS p s s1 t S V H)|exact q]. Qed.

(* a slot whose CAS completes only where its load part already happened *)
Lemma nowhole_puth : forall s s' c X k0 t, cs s' = upd (cs s) c X -> oc X = upd (oc (cs s c)) k0 (Some t) ->
  oh (cs s c) k0 <> None -> nowhole s s'.
Proof.
  intros s s' c X k0 t E O H. apply (nowhole_upd s s' c X E). intros k Ne. left.
  rewrite O in Ne. unfold upd in Ne. destruct (Nat.eqb_spec k k0) as [Ek|Nk]; [rewrite Ek; exact H|congruence].
Qed.

Ltac nameV := match goal with |- exists t, starV _ ?S t /\ _ => let s := fresh "s" in set (s := S) end.
(* nowhole, by the shape of the step: a slot put that is no CAS (nwP); no slot
   put (nwK); a CAS slot put after its load part (nwH) *)
Ltac nwP := eapply nowhole_put; [reflexivity|reflexivity|vm_compute; reflexivity].
Ltac nwK := eapply nowhole_keep; [reflexivity|reflexivity].
Ltac nwH := eapply nowhole_puth; [reflexivity|reflexivity|let H := fresh in intro H; vm_compute in H; discriminate H].
Ltac finV := eexists; split; [apply sv0|].

Notation CASPDEP := M2CasPDepInst.CASPDEP.
Notation V77 := M2CasPDepInst.V77.

(* the original file's local tactics, unchanged *)
Local Ltac detH := let r := fresh "r" in let Hs := fresh "Hs" in
  intros r Hs; split; [vm_compute; reflexivity|]; vm_compute;
  first [ reflexivity
        | repeat match goal with |- context [r ?j] =>
            let H0 := fresh in
            assert (H0 := Hs j ltac:(first [left; vm_compute; lia
                                           | right; let Z := fresh in intro Z; vm_compute in Z; discriminate]));
            rewrite H0; clear H0 end;
          vm_compute; reflexivity ].
Local Ltac cw c := eapply (s_cw _ _ c);
  [vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; reflexivity
  |vm_compute; reflexivity|detH|pend_tac|hblk_ne|vm_compute; reflexivity| |reflexivity|fx_tac].

Theorem CASPDEP_allowed_Q : exists s, runQ CASPDEP s /\ done CASPDEP s /\ evok s /\
  rg (cs s 0) 0 = V77 /\ vv (rg (cs s 0) 1) = V77.
Proof.
  apply startV.
  eapply fwdV. { ord 2. eapply (e_st2 _ _ 0 3); [lia|reflexivity|W0|W0]. } { nwP. } nameV.
  eapply fwdV. { cread 0 1 [0; 3] 1. eapply (e_ld2 _ _ 0 3 _ _ _ (Some 0) (Some 0)); [lia|reflexivity|vis_some|vis_some]. } { nwK. } nameV.
  eapply fwdV. { earlyH 0 2 (DSt Plain [2] V77) 2. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 1. LD (Some 2). vis_some. } { nwP. } nameV.
  eapply fwdV. { ord 1. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ordH 0. LD (Some 4). vis_some. } { nwP. } nameV.
  eapply fwdV. { cw 0. eapply (e_cas_ok2 _ _ 0 3 _ _ _ _ _ (Some 0) (Some 0));
    [lia|reflexivity|vis_some|vis_some|vm_compute; reflexivity
    |enter_at [(0, false)] (@nil (nat * bool))|enter_at [(0, false)] (@nil (nat * bool))]. } { nwH. } nameV.
  eapply fwdV. { mtchH 0 (DSt Plain [2] V77). } { nwK. } nameV.
  finV. intros RUN. split.
  { apply (done_tp _ _ RUN). refine (done_dec _ _ _ _). vm_compute; reflexivity. }
  split.
  { apply (evok_time _ _ RUN); [et_hist|refine (newer_dec _ _); vm_compute; reflexivity
                                     |refine (po_dec _ _); vm_compute; reflexivity]. }
  split; reflexivity.
Qed.

Print Assumptions CASPDEP_allowed_Q.
