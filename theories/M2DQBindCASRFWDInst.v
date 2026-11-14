(* CASRFWD on M2DQ (port of M2BindCASRFWDInst.v).
     CASRFWD: r0 = x; x = 1; c = CAS(x, 1, 2); y = c || r1 = y; x = r1
   with r0 = 1, c = 1, r1 = 1: the CAS's read is counted on taking x = 1.
   Split: the original's whole CAS in order (s_ord) becomes the load part
   alone, in order (s_cread at slot 2; R1 counts on it, so it takes its
   binder's write, x = 1 at slot 1), then the store part (s_cw). Both are
   q_old steps. Same outcome: CASRFWD_allowed_Q. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Lit M2Ev M2EvLit M2Oota M2CasSplitProof M2EvTimeProof M2DA M2DP M2DQ.
Require Import M2BindCASRFWDInst.

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

(* a CAS's load part, R1 counting on it: its place j, and the binder's write *)
Ltac creadB c k xs := eapply (s_cread _ _ c k Plain xs (fun _ => false) _ _ _ _ _ true);
  [vm_compute; lia|vm_compute; reflexivity|vm_compute; reflexivity|slot_tac|shelve| |fxr_tac].
Ltac eokB j := let f := fresh "f" in intros f; cbv zeta; exists j; split; [fatR_tac|];
  let x := fresh "x" in let b := fresh "b" in let Hx := fresh "Hx" in let H := fresh "H" in
  intros x b Hx _ H; vm_compute in Hx; destruct Hx as [Ex|[]]; subst x; vm_compute in H;
  apply (f_equal (fun o => match o with Some n => n | None => 0 end)) in H; cbn in H; subst b;
  eexists; split; [vm_compute; reflexivity|vm_compute; reflexivity].

Theorem CASRFWD_allowed_Q : exists s, runQ CASRFWD s /\ done CASRFWD s /\ evok s /\
  rg (cs s 0) 0 = 1 /\ vv (rg (cs s 0) 2) = 1 /\ rg (cs s 1) 0 = 1.
Proof.
  apply startV.
  eapply fwdV. { earlyB 0 3 (DSt Plain [1] 1) 3 (fun j => Nat.eqb j 2). ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 1. LD (Some 0). vis_some. } { nwP. } nameV.
  eapply fwdV. { ord 1. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 0. LD (Some 2). vis_some. } { nwP. } nameV.
  eapply fwdV. { ord 0. ST. enter_at [(2, false)] (@nil (nat * bool)). } { nwP. } nameV.
  eapply fwdV. { creadB 0 2 [0]. LD (Some 4). vis_some. Unshelve. eokB 2. } { nwK. } nameV.
  eapply fwdV. { cw 0. eapply (e_cas_ok1 _ _ _ _ _ _ _ _ (Some 4));
    [reflexivity|vis_some|vm_compute; reflexivity|enter_at [(2, false); (4, false)] (@nil (nat * bool))]. } { nwH. } nameV.
  eapply fwdV. { mtchH 0 (DSt Plain [1] 1). } { nwK. } nameV.
  finV. intros RUN. split; [done_tac|split; [evok_time_tac RUN|]].
  split; [reflexivity|split; [reflexivity|reflexivity]].
Qed.

Print Assumptions CASRFWD_allowed_Q.
