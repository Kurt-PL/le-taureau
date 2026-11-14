(* The leader rule with the write-back store as a write the CAS made (spec 0.1 §2.3, "the write
   its leader made there"; §2.3.4).
     WBL:  r0 = CAS(x, 1, 2); r1 = x; y = r1  ||  x = 3        (x = cell 0, y = cell 1)
   Context 1 stores x = 3 (time 0).  The CAS's load part happens alone (time 1, observing that
   store), its failure is fixed, and the store y = r1 happens early (time 2), counting on the read
   r1 = x, which is led in x by the CAS (fbinder): its value is the one the CAS observed, 3.  The
   context passes the CAS and writes back (id 1, right after the store 0).  The read r1 = x,
   counted on, then happens in order (time 3): it observes the write-back store 1, the write its
   leader made there, whose value is that of the observed write 0 (WBL_led).
   Negative (WBL_neg): at the state after the write-back, the leader's record in x is the
   write-back 1, not the observed write 0; a counted-on read observing 0 fails the leader premise
   of s_ord; and 0 is no longer visible to context 0 (so with a record rw = 0 the read could not
   happen at all). *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Lit M2Ev M2EvLit M2CasSplitProof M2WBRel M2DQWBPatch M2DQWB.
Require Import M2EvTimeProof M2DP M2DQDec M2DQWBEvT M2DQWBK16.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

Ltac W0 := enter_at (@nil (nat * bool)) (@nil (nat * bool)).
Ltac LD u := eapply (e_ld1 _ _ _ _ _ _ u); [reflexivity|].
Ltac ST := eapply e_st1; [reflexivity|].

Definition WBL : prog := stat
  [ [ICas Plain [0] T (K 1) (K 2); ld 0; ISt Plain [1] T (RG 1)];
    [st 0 3] ].

Lemma WBL_wf : wf WBL.
Proof. unfold WBL. wf_tac. Qed.

(* an early store whose value R1 knows through the reads B counts on *)
Ltac earlyB c k d j B := eapply (s_early _ _ c k d B);
  [vm_compute; lia|vm_compute; reflexivity|vm_compute; reflexivity|slot_tac
  |let f := fresh "f" in intros f; cbv zeta; exists j; split; [vm_compute; lia|];
   split; [fat_tac|let X := fresh "X" in intros X; discriminate X]
  | |fxe_tac].
(* the next instruction in order, after a CAS's read alone; its leader premise left for later *)
Ltac ordHB c := eapply (s_ord _ _ c);
  [vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; reflexivity|detH|blk_tac|intros _; hblk_gen|shelve| |fx_tac].
(* a read counted on takes its leader's record *)
Ltac bnd2_tac := let x := fresh "x" in let b := fresh "b" in let Hx := fresh "Hx" in let H := fresh "H" in
  intros x b _ Hx H; vm_compute in Hx; destruct Hx as [<-|[]]; vm_compute in H; injection H as <-;
  vm_compute; reflexivity.
Ltac wAF t := eapply wbA; [qA t|apply flagsF_fhsafe; let x := fresh "x" in let w := fresh "w" in let b := fresh "b" in
  intros x w b; destruct x; vm_compute; intuition congruence].

Definition WBL_H (x : cell) : hist :=
  match x with 0 => [(0, false); (1, true)] | 1 => [(2, false)] | _ => [] end.

(* the run up to and including the write-back *)
Definition WBLB (s : M2Model.st) : Prop :=
  hs s 0 = [(0, false); (1, true)] /\ rw (cs s 0) 0 0 = Some 1 /\ bd (cs s 0) 1 = true /\
  fbinder WBL 0 (rg (cs s 0)) 1 0 = Some 0 /\ vP (cs s 0) 1 /\ pcs s 0 = 1.

Lemma WBL_pre : exists s, runWB WBL s /\ WBLB s.
Proof.
  apply wstart.
  eapply wfwd. { wAF ltac:(ord 1; ST; W0). } nameW.
  eapply wfwd. { wA ltac:(cread 0 0 [0] 0; LD (Some 0); vis_some). } nameW.
  eapply wfwd. { wA ltac:(cfailH 0 0 0 3). } nameW.
  eapply wfwd. { wAF ltac:(earlyB 0 2 (DSt Plain [1] 3) 2 (fun j => Nat.eqb j 1); ST; W0). } nameW.
  eapply wfwd.
  { eapply (wbP _ _ _ 0 0 1 WBL_H).
    - qA ltac:(skipF 0).
    - unfold partskip, nowrite. split; [intros x; vm_compute; reflexivity|].
      do 7 (split; [vm_compute; reflexivity|]). vm_compute; reflexivity.
    - intros y. destruct y as [|[|y]]; vm_compute; intuition lia.
    - match goal with |- wbok ?S _ _ _ _ => set (s' := S) end. unfold wbok.
      replace (icells (ai (cs s' 0) 0)) with [0] by (vm_compute; reflexivity).
      intros x. split.
      + intros [<-|[]]. vm_compute. exists [(0, false)], []. split; [reflexivity|].
        split; [exists [], false; reflexivity|]. split; [intros w g h' E; discriminate|reflexivity].
      + intros Nx. unfold WBL_H. destruct x as [|[|x]]; [exfalso; apply Nx; left; reflexivity|vm_compute; reflexivity|vm_compute; reflexivity]. }
  nameW.
  wfin. intros RW. unfold WBLB. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  split; [vm_compute; first [right; reflexivity|tauto]|vm_compute; reflexivity].
Qed.

Theorem WBL_led : exists s, runWB WBL s /\ done WBL s /\ evok s /\
  hs s 0 = [(0, false); (1, true)] /\
  (* the read r1 = x (context 0, slot 1, time 3) observes the write-back store 1 *)
  option_map (fun e => (ec e, ek e, erf e 0)) (ent s 3) = Some (0, 1, Some 1) /\
  (* it was counted on, and its leader in x is the CAS at slot 0, whose record in x is 1 *)
  bd (cs s 0) 1 = true /\ fbinder WBL 0 (rg (cs s 0)) 1 0 = Some 0 /\ rw (cs s 0) 0 0 = Some 1 /\
  (* the value of the write-back store is that of the write 0 the CAS observed, 3, and r1 has it *)
  wv s 1 0 = wv s 0 0 /\ wv s 0 0 = 3 /\ rg (cs s 0) 1 = 3 /\ vv (rg (cs s 0) 0) = 3 /\ vok (rg (cs s 0) 0) = false /\
  (* the store counted on stored 3 *)
  final s 1 = 3.
Proof.
  apply wstart.
  eapply wfwd. { wAF ltac:(ord 1; ST; W0). } nameW.
  eapply wfwd. { wA ltac:(cread 0 0 [0] 0; LD (Some 0); vis_some). } nameW.
  eapply wfwd. { wA ltac:(cfailH 0 0 0 3). } nameW.
  eapply wfwd. { wAF ltac:(earlyB 0 2 (DSt Plain [1] 3) 2 (fun j => Nat.eqb j 1); ST; W0). } nameW.
  eapply wfwd.
  { eapply (wbP _ _ _ 0 0 1 WBL_H).
    - qA ltac:(skipF 0).
    - unfold partskip, nowrite. split; [intros x; vm_compute; reflexivity|].
      do 7 (split; [vm_compute; reflexivity|]). vm_compute; reflexivity.
    - intros y. destruct y as [|[|y]]; vm_compute; intuition lia.
    - match goal with |- wbok ?S _ _ _ _ => set (s' := S) end. unfold wbok.
      replace (icells (ai (cs s' 0) 0)) with [0] by (vm_compute; reflexivity).
      intros x. split.
      + intros [<-|[]]. vm_compute. exists [(0, false)], []. split; [reflexivity|].
        split; [exists [], false; reflexivity|]. split; [intros w g h' E; discriminate|reflexivity].
      + intros Nx. unfold WBL_H. destruct x as [|[|x]]; [exfalso; apply Nx; left; reflexivity|vm_compute; reflexivity|vm_compute; reflexivity]. }
  nameW.
  eapply wfwd.
  { eapply wbA; [apply q_old; [ordHB 0; [LD (Some 1); vis_some|..]|nwP]|apply nowrite_fhsafe; intros ?x; vm_compute; reflexivity].
    Unshelve. bnd2_tac. }
  nameW.
  eapply wfwd. { wA ltac:(mtchH 0 (DSt Plain [1] 3)). } nameW.
  wfin. intros RUN. match type of RUN with runWB _ ?S => set (sF := S) in * end. split.
  { apply (done_tpWB _ _ RUN). refine (done_dec _ _ _ _). vm_compute; reflexivity. }
  split.
  { apply (evok_timeWB _ _ RUN); [et_hist|refine (newer_dec _ _); vm_compute; reflexivity
                                     |refine (po_dec _ _); vm_compute; reflexivity]. }
  vm_compute. repeat split; reflexivity.
Qed.

(* the leader premise of s_ord, for slot k of context c reading u *)
Definition ledok (p : prog) (cc : cst) (c k : nat) (i : instr) (u : cell -> option nat) : Prop :=
  forall x b, bd cc k = true -> In x (icells i) -> fbinder p c (rg cc) k x = Some b -> u x = rw cc b x.

Theorem WBL_neg : exists s, runWB WBL s /\ WBLB s /\
  (* reading the write-back store meets the leader premise *)
  ledok WBL (cs s 0) 0 1 (ld 0) (fun x => if Nat.eqb x 0 then Some 1 else None) /\
  (* reading the observed write 0 does not *)
  ~ ledok WBL (cs s 0) 0 1 (ld 0) (fun x => if Nat.eqb x 0 then Some 0 else None) /\
  (* and the observed write 0 is no longer visible to context 0 *)
  ~ visible (vP (cs s 0)) (hs s 0) (Some 0) /\ visible (vP (cs s 0)) (hs s 0) (Some 1).
Proof.
  destruct WBL_pre as (s & R & (H0 & Rw & Bd & Fb & P1 & Pc)). exists s. split; [exact R|].
  split; [exact (conj H0 (conj Rw (conj Bd (conj Fb (conj P1 Pc)))))|].
  split.
  { intros x b _ Ix Fx. cbn in Ix. destruct Ix as [<-|[]]. rewrite Fb in Fx. injection Fx as <-. rewrite Rw. reflexivity. }
  split.
  { intros L. specialize (L 0 0 Bd (or_introl eq_refl) Fb). rewrite Rw in L. cbn in L. discriminate. }
  split.
  { intros (_ & V). apply (V 1 P1). rewrite H0. exists [(0, false)], [(1, true)]. split; [reflexivity|].
    split; [left; reflexivity|left; reflexivity]. }
  { rewrite H0. split; [right; left; reflexivity|]. intros w' Pw (a1 & a2 & Eh & Ia & Ib).
    destruct a1 as [|e1 [|e2 [|e3 a1]]]; cbn in Eh, Ia.
    - destruct Ia.
    - injection Eh as <- Eh. destruct Ia as [Ia|[]]. discriminate.
    - injection Eh as <- <- Eh. subst a2. destruct Ib.
    - discriminate. }
Qed.

Print Assumptions WBL_led.
Print Assumptions WBL_neg.
