(* Part 16: a fenced write-back run in which a read takes the write-back store, and
   fenced_sc_WB on it; instances of LFB, isFF, HB1, HB2, KR.
     FWB:  F; r0 = CAS(x, 1, 2); F  ||  F; r1 = x; F       (x = cell 0, initially 0)
   The CAS fails in parts (its load at time 1, its failure fixed, then the context passes it)
   and writes back (id 1, after nothing: the value 0 it loaded); the read of context 1 takes
   that store (erf = Some 1). *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Iface MIFSC.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Lit M2Ev M2EvLit M2Acyc M2CasSplitProof M2WBRel M2DQWBPatch M2DQWB.
Require Import M2DQWBK1 M2DQWBK3 M2DQWBK9 M2DQWBK13 M2DQWBK14 M2DQWBK15.
Require Import M2EvTimeProof M2DA M2DP M2DQDec M2DQWBEvT.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

Definition FWB : prog := stat
  [ [IFn FFull; ICas Plain [0] T (K 1) (K 2); IFn FFull];
    [IFn FFull; ld 0; IFn FFull] ].

Lemma FWB_wf : wf FWB.
Proof. unfold FWB. wf_tac. Qed.

Lemma FWB_fenced : fenced FWB.
Proof.
  intros c k r A. unfold FWB in *. rewrite ins_stat in A |- *. rewrite !ins_stat.
  destruct c as [|[|c]]; [| |destruct k; destruct c; cbn in A; try discriminate; destruct k; discriminate].
  all: destruct k as [|[|[|k]]]; cbn in A; try discriminate; [split; [lia|split; reflexivity]|destruct k; discriminate].
Qed.

(* ---------- runs of the write-back model, built forward ---------- *)
Inductive wstar (p : prog) : M2Model.st -> M2Model.st -> Prop :=
| ws0 : forall s, wstar p s s
| wsS : forall s s1 t, stepWB p s s1 -> wstar p s1 t -> wstar p s t.

Lemma wstar_run : forall p s t, runWB p s -> wstar p s t -> runWB p t.
Proof. intros p s t R H. induction H; auto. apply IHwstar. econstructor; eauto. Qed.

Lemma wstart : forall p (Q : M2Model.st -> Prop), (exists t, wstar p sinit t /\ (runWB p t -> Q t)) -> exists t, runWB p t /\ Q t.
Proof.
  intros p Q (t & H & q). assert (R : runWB p t) by (eapply wstar_run; [constructor|exact H]). exists t. auto.
Qed.

Lemma wfwd : forall p s s1 (Q : M2Model.st -> Prop), stepWB p s s1 -> (exists t, wstar p s1 t /\ Q t) ->
  exists t, wstar p s t /\ Q t.
Proof. intros p s s1 Q H (t & A & B). exists t. split; auto. econstructor; eauto. Qed.

Ltac nameW := match goal with |- exists t, wstar _ ?S t /\ _ => let s := fresh "s" in set (s := S) end.
Ltac wfin := eexists; split; [apply ws0|].
(* a step of M2DQ that is a step of A with nowhole, by the shape of the step: a slot put that is
   no CAS (nwP); no slot put (nwK); a result fixed (nwF, no slot put either) *)
Lemma nowhole_same : forall s s', (forall c, oc (cs s' c) = oc (cs s c)) -> nowhole s s'.
Proof. intros s s' E c k O O' _. rewrite E in O'. contradiction. Qed.
Lemma oc_cfix : forall s c j b B o c0, oc (cs (scfix0 (sflp s c o b) c j b B) c0) = oc (cs s c0).
Proof.
  intros s c j b B o c0. unfold scfix0, sflp. destruct o as [k|]; [destruct b|]; unfold scfail; cbn [cs]; unfold upd;
    repeat match goal with |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b) end; subst; first [reflexivity|congruence].
Qed.
Ltac nwP := eapply nowhole_put; [reflexivity|reflexivity|vm_compute; reflexivity].
Ltac nwK := eapply nowhole_keep; [reflexivity|reflexivity].
Ltac nwF := apply nowhole_same; intros ?c; apply oc_cfix.
Ltac qA t := apply q_old; [t|first [nwP|nwK|nwF]].
(* a step of M2DQ that leaves the histories as they are *)
Ltac wA t := eapply wbA; [qA t|apply nowrite_fhsafe; intros ?x; vm_compute; reflexivity].

Definition FWB_H (x : cell) : hist := if Nat.eqb x 0 then [(1, true)] else [].

Definition FWBQ (s : M2Model.st) : Prop :=
  done FWB s /\ evok s /\ hs s 0 = [(1, true)] /\ option_map (fun e => (ec e, erf e 0)) (ent s 4) = Some (1, Some 1) /\
  rg (cs s 0) 1 = vd false 0 /\ rg (cs s 1) 1 = 0 /\
  (* LFB / isFF, positive and negative *)
  LFB s 1 4 /\ ~ LFB s 1 3 /\ (exists g, ent s 3 = Some g /\ isFF s 3 g) /\ (forall e, ent s 4 = Some e -> ~ isFF s 4 e) /\
  (* the write-back store is a store of context 0 into cell 0 *)
  option_map (fun e => (ec e, ew e, eC e)) (ent s 1) = Some (0, true, [0]) /\
  (* no guard() before the first event *)
  ~ LFB s 0 0 /\ option_map ec (ent s 0) = Some 0 /\ length (lg s) = 6 /\
  (* the read knows in order the write-back store it took *)
  (exists e4, ent s 4 = Some e4 /\ eQ e4 1 /\ In 0 (eC e4)) /\ In 1 (ids (hs s 0)).

Lemma FWB_run : exists s, runWB FWB s /\ FWBQ s.
Proof.
  apply wstart.
  eapply wfwd. { wA ltac:(ord 0; apply e_full). } nameW.
  (* the CAS fails in parts: its load (time 1, the initial value), its failure fixed, then the
     context passes it and writes back (id 1) *)
  eapply wfwd. { wA ltac:(cread 0 1 [0] 1; LD (@None nat); vis_none). } nameW.
  eapply wfwd. { wA ltac:(cfailH 0 1 1 0). } nameW.
  eapply wfwd.
  { eapply (wbP _ _ _ 0 1 1 FWB_H).
    - qA ltac:(skipF 0).
    - unfold partskip, nowrite. split; [intros x; vm_compute; reflexivity|].
      do 7 (split; [vm_compute; reflexivity|]). vm_compute; reflexivity.
    - intros x. vm_compute. intros [].
    - match goal with |- wbok ?S _ _ _ _ => set (s' := S) end. unfold wbok.
      replace (icells (ai (cs s' 0) 1)) with [0] by (vm_compute; reflexivity).
      intros x. split.
      + intros [<-|[]]. vm_compute. exists [], []. split; [reflexivity|].
        split; [reflexivity|]. split; [intros w g h' E; discriminate|reflexivity].
      + intros Nx. unfold FWB_H. destruct (Nat.eqb_spec x 0) as [->|N]; [exfalso; apply Nx; left; reflexivity|].
        vm_compute. reflexivity. }
  nameW.
  eapply wfwd. { wA ltac:(ordH 0; apply e_full). } nameW.
  eapply wfwd. { wA ltac:(ord 1; apply e_full). } nameW.
  eapply wfwd. { wA ltac:(ord 1; LD (Some 1); vis_some). } nameW.
  eapply wfwd. { wA ltac:(ord 1; apply e_full). } nameW.
  wfin. intros RUN. match type of RUN with runWB _ ?S => set (sF := S) in * end. split.
  { apply (done_tpWB _ _ RUN). refine (done_dec _ _ _ _). vm_compute; reflexivity. }
  split.
  { apply (evok_timeWB _ _ RUN); [et_hist|refine (newer_dec _ _); vm_compute; reflexivity
                                     |refine (po_dec _ _); vm_compute; reflexivity]. }
  split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  split.
  { exists 3. eexists. split; [lia|]. split; [vm_compute; reflexivity|]. split; [reflexivity|].
    split; [unfold isFF; vm_compute; split; [reflexivity|split; [lia|reflexivity]]|].
    intros t' e' L1 L2. lia. }
  split.
  { intros (tg & g & L & E & C & _).
    assert (Ec : option_map ec (ent sF tg) = Some 0) by (destruct tg as [|[|[|tg]]]; [| | |lia]; vm_compute; reflexivity).
    rewrite E in Ec. cbn in Ec. congruence. }
  split.
  { eexists. split; [vm_compute; reflexivity|]. unfold isFF; vm_compute; split; [reflexivity|split; [lia|reflexivity]]. }
  split.
  { intros e E (Fa & _).
    assert (P : option_map (fun e => (ec e, ek e)) (ent sF 4) = Some (1, 1)) by (vm_compute; reflexivity).
    rewrite E in P. cbn in P. assert (Ce : ec e = 1) by congruence. assert (Ke : ek e = 1) by congruence.
    rewrite Ce, Ke in Fa.
    assert (Ai : isfn FFull (ai (cs sF 1) 1) = false) by (vm_compute; reflexivity).
    rewrite Fa in Ai. discriminate Ai. }
  split; [vm_compute; reflexivity|].
  split; [intros (tg & _ & L & _); lia|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  split; [|vm_compute; auto].
  eexists. split; [vm_compute; reflexivity|]. split; [|vm_compute; auto].
  vm_compute. right. split; [exists 0; reflexivity|]. intros (Z & _). destruct Z as (e & E & C & _).
  change (ec e = 1) in C. apply (f_equal (fun o => match o with Some e => ec e | None => 1 end)) in E. cbn in E. congruence.
Qed.

(* ---------- the theorem on this run ---------- *)
(* G1 applies: the run, with a read of a write-back store, has an interleaving with the same
   registers; in it the read reads 0 *)
Corollary FWB_sc : exists s, runWB FWB s /\ hs s 0 = [(1, true)] /\
  option_map (fun e => (ec e, erf e 0)) (ent s 4) = Some (1, Some 1) /\
  exists l g, srun FWB l g /\ sr g 1 1 = 0 /\ sr g 0 1 = vd false 0.
Proof.
  destruct FWB_run as (s & R & D & EV & H & E4 & R0 & R1 & _).
  exists s. split; [exact R|]. split; [exact H|]. split; [exact E4|].
  destruct (fenced_sc_WB FWB s FWB_wf FWB_fenced R D EV) as (l & g & Sr & Sp & Sg & _).
  exists l, g. split; [exact Sr|].
  assert (P : forall c, c < 2 -> 1 < pcs s c).
  { intros c Hc. destruct D as (n & F & Cp). destruct (Cp c ltac:(vm_compute; lia)) as [L _].
    destruct (Nat.lt_ge_cases 1 (n c)) as [N|N]; [lia|]. exfalso. pose proof (F c 1 (fun _ => 0) N) as Z.
    unfold FWB in Z. rewrite ins_stat in Z. destruct c as [|[|c]]; [discriminate|discriminate|lia]. }
  pose proof (P 0 ltac:(lia)) as P0. pose proof (P 1 ltac:(lia)) as P1.
  rewrite (Sg 1 1 P1), (Sg 0 1 P0). auto.
Qed.

(* ---------- HB1 / HB2 / KR ---------- *)
Lemma HB1_GoodL : forall s, HB1 (GoodL s) s.
Proof. intros s t e E G. exact (G e E). Qed.

(* HB2 with Good := GoodL holds on every finished fenced runWB (FC_store, through pass 1) *)
Lemma HB2_GoodL : forall p s, wf p -> fenced p -> runWB p s -> done p s -> HB2 (GoodL s) s.
Proof.
  intros p s W FN R D t e E Ew Cn e' E'. rewrite E in E'. injection E' as <-.
  destruct (runWBK p W False (fun _ => False) s R (fun F => match F with end) (fun F => match F with end))
    as (sw1 & sA1 & RA1 & Rl1 & K1).
  exact (FC_store p W FN False (fun _ => False) sw1 s sA1 RA1 Rl1 K1 D t e E Ew Cn).
Qed.

Corollary FWB_inst : exists s, runWB FWB s /\
  HB1 (GoodL s) s /\ HB2 (GoodL s) s /\
  ~ HB1 (fun _ => True) s /\ ~ HB2 (fun _ => False) s /\
  (exists sw sA, run FWB sA /\ rel sw s sA /\ KR True (GoodL s) sw s sA) /\
  ~ KR True (GoodL s) sw0 s sinit.
Proof.
  destruct FWB_run as (s & R & D & EV & H & E4 & R0 & R1 & L4 & NL3 & FF3 & NF4 & E1 & NL0 & C0 & Ln & _).
  exists s. split; [exact R|]. split; [exact (HB1_GoodL s)|].
  split; [exact (HB2_GoodL FWB s FWB_wf FWB_fenced R D)|].
  split.
  { intros H1. destruct (ent s 0) as [e0|] eqn:E0; [|discriminate C0]. cbn in C0. injection C0 as C0.
    pose proof (H1 0 e0 E0 Logic.I) as L. rewrite C0 in L. exact (NL0 L). }
  split.
  { intros H2. destruct (ent s 1) as [e1|] eqn:Ee; [|discriminate E1]. cbn in E1. injection E1 as C1 W1 X1.
    exact (H2 1 e1 Ee W1 ltac:(rewrite X1; discriminate)). }
  split.
  { apply (runWBK FWB FWB_wf True (GoodL s) s R (fun _ => HB1_GoodL s) (fun _ => HB2_GoodL FWB s FWB_wf FWB_fenced R D)). }
  intros K. pose proof (k_len True (GoodL s) sw0 s sinit K) as Lk. rewrite Ln in Lk. discriminate.
Qed.

Print Assumptions FWB_sc.
Print Assumptions FWB_inst.
