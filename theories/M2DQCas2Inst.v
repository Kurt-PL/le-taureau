(* CAS2 on M2DQ (port of M2Cas2Inst.v).
     CAS2: r0 = y; r1 = q; r2 = CAS(x, r0, 7); z = r2 || r = z; y = r || s = x; q = s || x = 5
   The original run already splits the CAS (s_cread, then the early store
   part s_cwe): every step is a q_old step, each state named by set. Same
   outcome, and the M2 run with both halves of slot 2 recorded (for CasErf). *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Lit M2Ev M2EvLit M2Oota M2CasSplitProof M2EvTimeProof M2DA M2DP M2DQ M2DQDec.
Require M2Cas2Inst.

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
Ltac nwV :=   first [eapply nowhole_put; [reflexivity|reflexivity|vm_compute; reflexivity]
        |eapply nowhole_keep; [reflexivity|reflexivity]
        |eapply nowhole_puth; [reflexivity|reflexivity|let H := fresh in intro H; vm_compute in H; discriminate H]].

Notation CAS2 := M2Cas2Inst.CAS2.

Theorem CAS2_allowed_Q : exists s, runQ CAS2 s /\ run CAS2 s /\ done CAS2 s /\ evok s /\
  rg (cs s 0) 0 = 5 /\ rg (cs s 0) 1 = 7 /\ rg (cs s 2) 0 = 7 /\
  oh (cs s 0) 2 <> None /\ oc (cs s 0) 2 <> None.
Proof.
  apply startV.
  eapply fwdV. { ord 3. ST. W0. } { nwP. } nameV.
  eapply fwdV. { cread 0 2 [0] 2. LD (Some 0). vis_some. } { nwK. } nameV.
  eapply fwdV. { earlyH 0 3 (DSt Plain [2] 5) 3. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 1. LD (Some 2). vis_some. } { nwP. } nameV.
  eapply fwdV. { ord 1. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ordH 0. LD (Some 4). vis_some. } { nwP. } nameV.
  eapply fwdV.
  { cwe 0 2 1 [0] 5 7.
    - intros f. cbv zeta. exists 2. split; [vm_compute; lia|]. split; [fatR_tac|]. split; [vm_compute; reflexivity|].
      intros j' L1 L2 _ _ Ti. vm_compute in L1. assert (j' = 1) by lia. subst j'.
      apply tied_b in Ti. vm_compute in Ti. discriminate Ti.
    - eapply (e_cas_ok1 _ _ _ _ _ _ _ _ (Some 0));
        [reflexivity|vis_some|vm_compute; reflexivity|enter_at [(0, false)] (@nil (nat * bool))]. }
  { nwV. } nameV.
  eapply fwdV. { ord 2. LD (Some 6). vis_some. } { nwP. } nameV.
  eapply fwdV. { ord 2. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ordH 0. LD (Some 8). vis_some. } { nwP. } nameV.
  eapply fwdV. { mtchH 0 (DCas Plain [0] 5 7). } { nwV. } nameV.
  eapply fwdV. { mtchH 0 (DSt Plain [2] 5). } { nwV. } nameV.
  finV. intros RUN. split; [exact RUN|]. split.
  { apply (done_tp _ _ RUN). refine (done_dec _ _ _ _). vm_compute; reflexivity. }
  split.
  { apply (evok_time _ _ RUN); [et_hist|refine (newer_dec _ _); vm_compute; reflexivity
                                     |refine (po_dec _ _); vm_compute; reflexivity]. }
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; intros H; vm_compute in H; discriminate H.
Qed.

Print Assumptions CAS2_allowed_Q.
