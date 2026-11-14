(* LOCKREL on M2DQ (port of M2STWLOCKRELInst.v).
     LOCKREL: r0 = x; guard.rs(); y = 5 || r1 = cas(y, 5, 1); guard.rl(); x = 9
   with r0 = 9 and the CAS reading 5.
   Split: the original's whole CAS in order (s_ord) becomes the load part
   alone, in order (s_cread at slot 0), then the store part (s_cw); both are
   q_old steps. Times shift by one after the load part. evok by
   M2EvTimeProof.evok_time (rank = time) in place of the original evok_tac3.
   Same outcome: LOCKREL_allowed_Q. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Lit M2Ev M2EvLit M2Acyc M2Timeline2 M2Oota M2CasSplitProof M2EvTimeProof M2DA M2DP M2DQ.
Require M2STWLOCKRELInst.

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

Notation LOCKREL := M2STWLOCKRELInst.LOCKREL.

Theorem LOCKREL_allowed_Q : exists s, runQ LOCKREL s /\ done LOCKREL s /\ evok s /\
  rg (cs s 0) 0 = 9 /\ vv (rg (cs s 1) 0) = 5.
Proof.
  apply startV.
  eapply fwdV. { early 0 1 (DFn FSs) 1. apply e_ss. } { nwP. } nameV.
  eapply fwdV. { early 0 2 (DSt Plain [1] 5) 2. ST. W0. } { nwP. } nameV.
  eapply fwdV. { cread 1 0 [1] 0. LD (Some 1). vis_some. } { nwK. } nameV.
  eapply fwdV. { cw 1. eapply (e_cas_ok1 _ _ _ _ _ _ _ _ (Some 1));
    [reflexivity|vis_some|vm_compute; reflexivity|enter_at [(1, false)] (@nil (nat * bool))]. } { nwH. } nameV.
  eapply fwdV. { ordH 1. apply e_ll. } { nwP. } nameV.
  eapply fwdV. { ordH 1. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 0. LD (Some 5). vis_some. } { nwP. } nameV.
  eapply fwdV. { mtch 0 (DFn FSs). } { nwK. } nameV.
  eapply fwdV. { mtch 0 (DSt Plain [1] 5). } { nwK. } nameV.
  finV. intros RUN. split; [done_tac|split; [evok_time_tac RUN|split; reflexivity]].
Qed.

Print Assumptions LOCKREL_allowed_Q.
