(* CASLBW_succ on M2DQ (port of M2S3cLBWInst.v).
     CASLBW: r0 = f; x = r0; x = 1; r3 = CAS(x, 1, 7); r4 = x; z = r4  ||  r1 = z; f = r1
   with r0 = 7, the CAS reading 1 and succeeding, r4 = r1 = 7.
   The S3c fix of success before the read (s_cfix, record None) changes no
   slot, so it is a q_old step. Split: the original's whole CAS in order
   (s_ord) becomes the load part alone, in order (s_cread at slot 3, carrying
   the fixed success; R1 counts on it, so it takes its binder's write x = 1),
   then the store part (s_cw). Same outcome: CASLBW_succ_Q. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Lit M2Ev M2EvLit M2Oota M2CasSplitProof M2EvTimeProof M2DA M2DP M2DQ.
Require Import M2S3cLit.

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

(* the original M2PFixInst.LBW_cellful, re-proved here (no import of M2PFix) *)
Lemma LBW_cellful_Q : cellful CASLBW.
Proof.
  apply cellful_of. intros c k r. unfold CASLBW. rewrite ins_stat. destruct c as [|[|c]]; simpl.
  - destruct k as [|[|[|[|[|[|k]]]]]]; simpl; try discriminate. destruct k; discriminate.
  - destruct k as [|[|k]]; simpl; try discriminate. destruct k; discriminate.
  - destruct c; destruct k; discriminate.
Qed.

(* the fix step changes no slot *)
Ltac nwC := apply nowhole_oc; let c' := fresh "c'" in let k := fresh "k" in
  intros c' k; rewrite oc_cx, oc_flp; reflexivity.
(* the CAS's load part at slot k, in order, R1 counting on it; its fixed
   result is checked after its value is known *)
Ltac creadS c k xs := eapply (s_cread _ _ c k Plain xs (fun _ => false) _ _ _ _ _ true);
  [vm_compute; lia|vm_compute; reflexivity|vm_compute; reflexivity|slot_tac|shelve| |shelve].
Ltac eokB j := let f := fresh "f" in intros f; cbv zeta; exists j; split; [fatR_tac|];
  let x := fresh "x" in let b := fresh "b" in let Hx := fresh "Hx" in let H := fresh "H" in
  intros x b Hx _ H; vm_compute in Hx; destruct Hx as [Ex|[]]; subst x; vm_compute in H;
  apply (f_equal (fun o => match o with Some n => n | None => 0 end)) in H; cbn in H; subst b;
  eexists; split; [vm_compute; reflexivity|vm_compute; reflexivity].
(* the place is j0 under every free values (first_atR_unique), and the
   fixed success there agrees with the record *)
Ltac fxrJ W j0 := let f := fresh "f" in let j := fresh "j" in let F := fresh "F" in
  intros f j F;
  match type of F with first_atR ?p ?c ?cc ?pc ?r ?T ?m ?xs _ =>
    let F3 := fresh "F3" in assert (F3 : first_atR p c cc pc r T m xs j0) by fatR_tac;
    let J := fresh "J" in pose proof (first_atR_unique p c cc pc r T m xs j j0 W F F3) as J; subst j end;
  split; [vm_compute; reflexivity|fxk_tac].
(* the store part in order, its fixed result checked after the effect *)
Ltac cwK c := eapply (s_cw _ _ c);
  [vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; reflexivity
  |vm_compute; reflexivity|detH|pend_tac|hblk_ne|vm_compute; reflexivity| |reflexivity| ].
(* ordX where a load part happened alone earlier in the context *)
Ltac ordXH c := eapply (s_ord _ _ c);
  [vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; reflexivity|det_tac|blk_tac
  |intros _; hblk_gen|first [bnd_tac|shelve]| |].

Theorem CASLBW_succ_Q : exists s, runQ CASLBW s /\ done CASLBW s /\ evok s /\
  rg (cs s 0) 0 = 7 /\ rg (cs s 0) 3 = vd true 1 /\ rg (cs s 0) 4 = 7 /\ rg (cs s 1) 0 = 7.
Proof.
  apply startV.
  eapply fwdV. { cfix 0 3 true (fun j => Nat.eqb j 3) 1. } { nwC. } nameV.
  eapply fwdV. { earlyB 0 5 (DSt Plain [2] 7) 5 (fun j => Nat.eqb j 4). ST. W0. } { nwP. } nameV.
  eapply fwdV. { ordX 1. LD (Some 0). vis_some. fxk_tac. Unshelve. all: bnd2_tac. } { nwP. } nameV.
  eapply fwdV. { ordX 1. ST. W0. fxk_tac. Unshelve. all: bnd2_tac. } { nwP. } nameV.
  eapply fwdV. { ordX 0. LD (Some 2). vis_some. fxk_tac. Unshelve. all: bnd2_tac. } { nwP. } nameV.
  eapply fwdV. { ordX 0. ST. W0. fxk_tac. Unshelve. all: bnd2_tac. } { nwP. } nameV.
  eapply fwdV. { ordX 0. ST. enter_at [(4, false)] (@nil (nat * bool)). fxk_tac. Unshelve. all: bnd2_tac. } { nwP. } nameV.
  eapply fwdV. { creadS 0 3 [0]. LD (Some 5). vis_some. Unshelve. eokB 3. fxrJ LBW_cellful_Q 3. } { nwK. } nameV.
  eapply fwdV. { cwK 0. eapply (e_cas_ok1 _ _ _ _ _ _ _ _ (Some 5));
    [reflexivity|vis_some|vm_compute; reflexivity|enter_at [(4, false); (5, false)] (@nil (nat * bool))]. fxk_tac. } { nwH. } nameV.
  eapply fwdV. { ordXH 0. LD (Some 7). vis_some. fxk_tac. Unshelve. all: bnd2_tac. } { nwP. } nameV.
  eapply fwdV. { mtchH 0 (DSt Plain [2] 7). } { nwK. } nameV.
  finV. intros RUN. split; [done_tp_tac RUN|split; [evok_time_tac RUN|]].
  split; [reflexivity|split; [reflexivity|split; [reflexivity|reflexivity]]].
Qed.

Print Assumptions CASLBW_succ_Q.
