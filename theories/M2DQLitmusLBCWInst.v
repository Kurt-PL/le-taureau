(* LBCW on M2DQ (port of M2LitmusLBCWInst.v).
     LBCW: r0 = z; r1 = cas(x, 0, 1); x = 2 || r2 = x; z = r2
   with r0 = r2 = 2, the CAS succeeding (r1 = 0), final x = 2.
   Split: the original's early whole CAS (one s_early step) becomes the load
   part alone, early (s_cread at slot 1), then the store part, early (s_cwe);
   both are q_old steps (nowhole: the slot completes after its load part).
   Times shift by one after the load part. Same outcome: LBCW_allowed_Q. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Lit M2Ev M2EvLit M2Oota M2CasSplitProof M2EvTimeProof M2DA M2DP M2DQ.
Require M2LitmusLBCWInst.

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
(* early_okW for the write part at place j, every coming instruction before it
   either untied to the CAS or taken *)
Ltac untied_tac := let Ti := fresh "Ti" in intros Ti; apply tied_b in Ti; vm_compute in Ti; discriminate Ti.

Notation LBCW := M2LitmusLBCWInst.LBCW.

Theorem LBCW_allowed_Q : exists s, runQ LBCW s /\ done LBCW s /\ evok s /\
  rg (cs s 0) 0 = 2 /\ vv (rg (cs s 0) 1) = 0 /\ rg (cs s 1) 0 = 2 /\ final s 0 = 2.
Proof.
  apply startV.
  eapply fwdV. { cread 0 1 [0] 1. LD (@None nat). vis_none. } { nwK. } nameV.
  eapply fwdV.
  { cwe 0 1 0 [0] 0 1.
    - intros f. cbv zeta. exists 1. split; [vm_compute; lia|]. split; [fatR_tac|]. split; [vm_compute; reflexivity|].
      intros j' L1 L2 _ _. vm_compute in L1, L2. assert (j' = 0) by lia. subst j'. untied_tac.
    - eapply (e_cas_ok1 _ _ _ _ _ _ _ _ None); [reflexivity|vis_none|vm_compute; reflexivity|W0]. }
  { nwH. } nameV.
  eapply fwdV. { early 0 2 (DSt Plain [0] 2) 2. ST. enter_at [(1, false)] (@nil (nat * bool)). } { nwP. } nameV.
  eapply fwdV. { ord 1. LD (Some 2). vis_some. } { nwP. } nameV.
  eapply fwdV. { ord 1. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ordH 0. LD (Some 4). vis_some. } { nwP. } nameV.
  eapply fwdV. { mtchH 0 (DCas Plain [0] 0 1). } { nwK. } nameV.
  eapply fwdV. { mtchH 0 (DSt Plain [0] 2). } { nwK. } nameV.
  finV. intros RUN. split; [done_tac|split; [evok_time_tac RUN|]].
  split; [reflexivity|split; [reflexivity|split; [reflexivity|reflexivity]]].
Qed.

Print Assumptions LBCW_allowed_Q.
