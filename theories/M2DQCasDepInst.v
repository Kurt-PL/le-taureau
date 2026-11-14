(* CASDEP on M2DQ (port of M2CasDepInst.v).
     CASDEP: r0 = y; r1 = CAS(x, 7, r0); z = r1 || r = z; y = r || x = 7
   The original run already splits the CAS (s_cread, then s_cw): every step
   is a q_old step; nowhole holds at each (the CAS slot completes only after
   its load part). Same outcome: CASDEP_allowed_Q. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Lit M2Ev M2EvLit M2Oota M2CasSplitProof M2EvTimeProof M2DA M2DP M2DQ.
Require M2CasDepInst.

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
Ltac nwV :=   first [eapply nowhole_put; [reflexivity|reflexivity|vm_compute; reflexivity]
        |eapply nowhole_keep; [reflexivity|reflexivity]
        |eapply nowhole_puth; [reflexivity|reflexivity|let H := fresh in intro H; vm_compute in H; discriminate H]].
Ltac nwP := eapply nowhole_put; [reflexivity|reflexivity|vm_compute; reflexivity].
Ltac nwK := eapply nowhole_keep; [reflexivity|reflexivity].
Ltac nwH := eapply nowhole_puth; [reflexivity|reflexivity|let H := fresh in intro H; vm_compute in H; discriminate H].
Ltac finV := eexists; split; [apply sv0|].

Notation CASDEP := M2CasDepInst.CASDEP.

Theorem CASDEP_allowed_Q : exists s, runQ CASDEP s /\ done CASDEP s /\ evok s /\
  rg (cs s 0) 0 = 7 /\ vv (rg (cs s 0) 1) = 7.
Proof.
  apply startV.
  eapply fwdV. { ord 2. ST. W0. } { nwP. } nameV.
  eapply fwdV. { cread 0 1 [0] 1. LD (Some 0). vis_some. } { nwK. } nameV.
  eapply fwdV. { earlyH 0 2 (DSt Plain [2] 7) 2. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 1. LD (Some 2). vis_some. } { nwP. } nameV.
  eapply fwdV. { ord 1. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ordH 0. LD (Some 4). vis_some. } { nwP. } nameV.
  eapply fwdV. { cw 0. eapply (e_cas_ok1 _ _ _ _ _ _ _ _ (Some 0));
    [reflexivity|vis_some|vm_compute; reflexivity|enter_at [(0, false)] (@nil (nat * bool))]. } { nwH. } nameV.
  eapply fwdV. { mtchH 0 (DSt Plain [2] 7). } { nwK. } nameV.
  finV. intros RUN. split; [done_tac|split; [evok_time_tac RUN|split; reflexivity]].
Qed.

Print Assumptions CASDEP_allowed_Q.
