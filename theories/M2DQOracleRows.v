(* Oracle rows (oracle/ORACLE.md), admitted outcomes: for each row, a run of
   M2DQ that ends with the row's outcome. Cells: x = 0, y = 1, z = 2. The
   register of a load is its slot in its context. guard.rl() is FLl (fll),
   guard.rs() is FSs (fss), guard() is FFull.
   Each run is built forward from q_old steps (M2DQSTWLOCKRELInst.starV); done
   by the closed decider done_dec, evok by evok_time with the closed deciders
   newer_dec and po_dec (the history premise by et_hist). *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Lit M2Ev M2EvLit M2Acyc M2Timeline2 M2Oota M2CasSplitProof M2EvTimeProof M2DA M2DP M2DQ M2DQDec.
Require Import M2DQSTWLOCKRELInst.

Ltac DONE R := apply (done_tp _ _ R); apply done_dec; vm_compute; reflexivity.
Ltac EVOK R := apply (evok_time _ _ R);
  [et_hist|refine (newer_dec _ _); vm_compute; reflexivity|refine (po_dec _ _); vm_compute; reflexivity].
Ltac OUT := match goal with |- _ /\ _ => split; [reflexivity|OUT] | _ => reflexivity end.
Ltac FIN := finV; let R := fresh "R" in intros R; split; [DONE R|split; [EVOK R|OUT]].
Ltac LD0 := LD (@None nat); vis_none.
Ltac LDw w := LD (Some w); vis_some.
Ltac STa w := ST; enter_at [(w, false)] (@nil (nat * bool)).

(* ---------- plain: no ordering (decision 1) ---------- *)
Definition MPp : prog := stat [ [st 0 1; st 1 1]; [ld 1; ld 0] ].
Theorem MP_plain_allowed : exists s, runQ MPp s /\ done MPp s /\ evok s /\
  rg (cs s 1) 0 = 1 /\ rg (cs s 1) 1 = 0.
Proof.
  apply startV.
  eapply fwdV. { early 1 1 (DLd Plain [0]) 1. LD0. } { nwP. } nameV.
  eapply fwdV. { ord 0. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 0. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 1. LDw 2. } { nwP. } nameV.
  eapply fwdV. { mtch 1 (DLd Plain [0]). } { nwK. } nameV.
  FIN.
Qed.

Definition SBp : prog := stat [ [st 0 1; ld 1]; [st 1 1; ld 0] ].
Theorem SB_plain_allowed : exists s, runQ SBp s /\ done SBp s /\ evok s /\
  rg (cs s 0) 1 = 0 /\ rg (cs s 1) 1 = 0.
Proof.
  apply startV.
  eapply fwdV. { early 0 1 (DLd Plain [1]) 1. LD0. } { nwP. } nameV.
  eapply fwdV. { early 1 1 (DLd Plain [0]) 1. LD0. } { nwP. } nameV.
  eapply fwdV. { ord 0. ST. W0. } { nwP. } nameV.
  eapply fwdV. { mtch 0 (DLd Plain [1]). } { nwK. } nameV.
  eapply fwdV. { ord 1. ST. W0. } { nwP. } nameV.
  eapply fwdV. { mtch 1 (DLd Plain [0]). } { nwK. } nameV.
  FIN.
Qed.

Definition LBp : prog := stat [ [ld 0; st 1 1]; [ld 1; st 0 1] ].
Theorem LB_plain_allowed : exists s, runQ LBp s /\ done LBp s /\ evok s /\
  rg (cs s 0) 0 = 1 /\ rg (cs s 1) 0 = 1.
Proof.
  apply startV.
  eapply fwdV. { early 0 1 (DSt Plain [1] 1) 1. ST. W0. } { nwP. } nameV.
  eapply fwdV. { early 1 1 (DSt Plain [0] 1) 1. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 0. LDw 1. } { nwP. } nameV.
  eapply fwdV. { mtch 0 (DSt Plain [1] 1). } { nwK. } nameV.
  eapply fwdV. { ord 1. LDw 0. } { nwP. } nameV.
  eapply fwdV. { mtch 1 (DSt Plain [0] 1). } { nwK. } nameV.
  FIN.
Qed.

Definition WRCp : prog := stat [ [st 0 1]; [ld 0; st 1 1]; [ld 1; ld 0] ].
Theorem WRC_plain_allowed : exists s, runQ WRCp s /\ done WRCp s /\ evok s /\
  rg (cs s 1) 0 = 1 /\ rg (cs s 2) 0 = 1 /\ rg (cs s 2) 1 = 0.
Proof.
  apply startV.
  eapply fwdV. { early 2 1 (DLd Plain [0]) 1. LD0. } { nwP. } nameV.
  eapply fwdV. { ord 0. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 1. LDw 1. } { nwP. } nameV.
  eapply fwdV. { ord 1. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 2. LDw 3. } { nwP. } nameV.
  eapply fwdV. { mtch 2 (DLd Plain [0]). } { nwK. } nameV.
  FIN.
Qed.

Definition IRIWp : prog := stat [ [st 0 1]; [ld 0; ld 1]; [st 1 1]; [ld 1; ld 0] ].
Theorem IRIW_plain_allowed : exists s, runQ IRIWp s /\ done IRIWp s /\ evok s /\
  rg (cs s 1) 0 = 1 /\ rg (cs s 1) 1 = 0 /\ rg (cs s 3) 0 = 1 /\ rg (cs s 3) 1 = 0.
Proof.
  apply startV.
  eapply fwdV. { early 1 1 (DLd Plain [1]) 1. LD0. } { nwP. } nameV.
  eapply fwdV. { early 3 1 (DLd Plain [0]) 1. LD0. } { nwP. } nameV.
  eapply fwdV. { ord 0. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 2. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 1. LDw 2. } { nwP. } nameV.
  eapply fwdV. { mtch 1 (DLd Plain [1]). } { nwK. } nameV.
  eapply fwdV. { ord 3. LDw 3. } { nwP. } nameV.
  eapply fwdV. { mtch 3 (DLd Plain [0]). } { nwK. } nameV.
  FIN.
Qed.

Definition ISA2p : prog := stat [ [st 0 1; st 1 1]; [ld 1; st 2 1]; [ld 2; ld 0] ].
Theorem ISA2_plain_allowed : exists s, runQ ISA2p s /\ done ISA2p s /\ evok s /\
  rg (cs s 1) 0 = 1 /\ rg (cs s 2) 0 = 1 /\ rg (cs s 2) 1 = 0.
Proof.
  apply startV.
  eapply fwdV. { early 2 1 (DLd Plain [0]) 1. LD0. } { nwP. } nameV.
  eapply fwdV. { ord 0. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 0. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 1. LDw 2. } { nwP. } nameV.
  eapply fwdV. { ord 1. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 2. LDw 4. } { nwP. } nameV.
  eapply fwdV. { mtch 2 (DLd Plain [0]). } { nwK. } nameV.
  FIN.
Qed.

Definition W22p : prog := stat [ [st 0 1; st 1 2]; [st 1 1; st 0 2] ].
Theorem W22_plain_allowed : exists s, runQ W22p s /\ done W22p s /\ evok s /\
  final s 0 = 1 /\ final s 1 = 1.
Proof.
  apply startV.
  eapply fwdV. { early 0 1 (DSt Plain [1] 2) 1. ST. W0. } { nwP. } nameV.
  eapply fwdV. { early 1 1 (DSt Plain [0] 2) 1. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 0. STa 1. } { nwP. } nameV.
  eapply fwdV. { mtch 0 (DSt Plain [1] 2). } { nwK. } nameV.
  eapply fwdV. { ord 1. STa 0. } { nwP. } nameV.
  eapply fwdV. { mtch 1 (DSt Plain [0] 2). } { nwK. } nameV.
  FIN.
Qed.

Definition Rp : prog := stat [ [st 0 1; st 1 1]; [st 1 2; ld 0] ].
Theorem R_plain_allowed : exists s, runQ Rp s /\ done Rp s /\ evok s /\
  final s 1 = 2 /\ rg (cs s 1) 1 = 0.
Proof.
  apply startV.
  eapply fwdV. { early 1 1 (DLd Plain [0]) 1. LD0. } { nwP. } nameV.
  eapply fwdV. { ord 0. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 0. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 1. STa 2. } { nwP. } nameV.
  eapply fwdV. { mtch 1 (DLd Plain [0]). } { nwK. } nameV.
  FIN.
Qed.

Definition Sp : prog := stat [ [st 0 2; st 1 1]; [ld 1; st 0 1] ].
Theorem S_plain_allowed : exists s, runQ Sp s /\ done Sp s /\ evok s /\
  final s 0 = 2 /\ rg (cs s 1) 0 = 1.
Proof.
  apply startV.
  eapply fwdV. { early 1 1 (DSt Plain [0] 1) 1. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 0. STa 0. } { nwP. } nameV.
  eapply fwdV. { ord 0. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 1. LDw 2. } { nwP. } nameV.
  eapply fwdV. { mtch 1 (DSt Plain [0] 1). } { nwK. } nameV.
  FIN.
Qed.

(* ---------- weak fences: guard.rl() after a load, guard.rs() after a store ---------- *)
Definition SBw : prog := stat [ [st 0 1; fss; ld 1]; [st 1 1; fss; ld 0] ].
Theorem SB_weak_allowed : exists s, runQ SBw s /\ done SBw s /\ evok s /\
  rg (cs s 0) 2 = 0 /\ rg (cs s 1) 2 = 0.
Proof.
  apply startV.
  eapply fwdV. { early 0 2 (DLd Plain [1]) 2. LD0. } { nwP. } nameV.
  eapply fwdV. { early 1 2 (DLd Plain [0]) 2. LD0. } { nwP. } nameV.
  eapply fwdV. { ord 0. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 0. apply e_ss. } { nwP. } nameV.
  eapply fwdV. { mtch 0 (DLd Plain [1]). } { nwK. } nameV.
  eapply fwdV. { ord 1. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 1. apply e_ss. } { nwP. } nameV.
  eapply fwdV. { mtch 1 (DLd Plain [0]). } { nwK. } nameV.
  FIN.
Qed.

Definition LBw : prog := stat [ [ld 0; fll; st 1 1]; [ld 1; fll; st 0 1] ].
Theorem LB_weak_allowed : exists s, runQ LBw s /\ done LBw s /\ evok s /\
  rg (cs s 0) 0 = 1 /\ rg (cs s 1) 0 = 1.
Proof.
  apply startV.
  eapply fwdV. { early 0 2 (DSt Plain [1] 1) 2. ST. W0. } { nwP. } nameV.
  eapply fwdV. { early 1 2 (DSt Plain [0] 1) 2. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 0. LDw 1. } { nwP. } nameV.
  eapply fwdV. { ord 0. apply e_ll. } { nwP. } nameV.
  eapply fwdV. { mtch 0 (DSt Plain [1] 1). } { nwK. } nameV.
  eapply fwdV. { ord 1. LDw 0. } { nwP. } nameV.
  eapply fwdV. { ord 1. apply e_ll. } { nwP. } nameV.
  eapply fwdV. { mtch 1 (DSt Plain [0] 1). } { nwK. } nameV.
  FIN.
Qed.

Definition WRCw : prog := stat [ [st 0 1]; [ld 0; fll; st 1 1]; [ld 1; fll; ld 0] ].
Theorem WRC_weak_allowed : exists s, runQ WRCw s /\ done WRCw s /\ evok s /\
  rg (cs s 1) 0 = 1 /\ rg (cs s 2) 0 = 1 /\ rg (cs s 2) 2 = 0.
Proof.
  apply startV.
  eapply fwdV. { early 1 2 (DSt Plain [1] 1) 2. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 2. LDw 0. } { nwP. } nameV.
  eapply fwdV. { ord 2. apply e_ll. } { nwP. } nameV.
  eapply fwdV. { ord 2. LD0. } { nwP. } nameV.
  eapply fwdV. { ord 0. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 1. LDw 4. } { nwP. } nameV.
  eapply fwdV. { ord 1. apply e_ll. } { nwP. } nameV.
  eapply fwdV. { mtch 1 (DSt Plain [1] 1). } { nwK. } nameV.
  FIN.
Qed.

Definition ISA2w : prog := stat [ [st 0 1; fss; st 1 1]; [ld 1; fll; st 2 1]; [ld 2; fll; ld 0] ].
Theorem ISA2_weak_allowed : exists s, runQ ISA2w s /\ done ISA2w s /\ evok s /\
  rg (cs s 1) 0 = 1 /\ rg (cs s 2) 0 = 1 /\ rg (cs s 2) 2 = 0.
Proof.
  apply startV.
  eapply fwdV. { early 1 2 (DSt Plain [2] 1) 2. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 2. LDw 0. } { nwP. } nameV.
  eapply fwdV. { ord 2. apply e_ll. } { nwP. } nameV.
  eapply fwdV. { ord 2. LD0. } { nwP. } nameV.
  eapply fwdV. { ord 0. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 0. apply e_ss. } { nwP. } nameV.
  eapply fwdV. { ord 0. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 1. LDw 6. } { nwP. } nameV.
  eapply fwdV. { ord 1. apply e_ll. } { nwP. } nameV.
  eapply fwdV. { mtch 1 (DSt Plain [2] 1). } { nwK. } nameV.
  FIN.
Qed.

Definition Rw : prog := stat [ [st 0 1; fss; st 1 1]; [st 1 2; fss; ld 0] ].
Theorem R_weak_allowed : exists s, runQ Rw s /\ done Rw s /\ evok s /\
  final s 1 = 2 /\ rg (cs s 1) 2 = 0.
Proof.
  apply startV.
  eapply fwdV. { early 1 2 (DLd Plain [0]) 2. LD0. } { nwP. } nameV.
  eapply fwdV. { ord 0. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 0. apply e_ss. } { nwP. } nameV.
  eapply fwdV. { ord 0. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 1. STa 3. } { nwP. } nameV.
  eapply fwdV. { ord 1. apply e_ss. } { nwP. } nameV.
  eapply fwdV. { mtch 1 (DLd Plain [0]). } { nwK. } nameV.
  FIN.
Qed.

Definition Sw : prog := stat [ [st 0 2; fss; st 1 1]; [ld 1; fll; st 0 1] ].
Theorem S_weak_allowed : exists s, runQ Sw s /\ done Sw s /\ evok s /\
  final s 0 = 2 /\ rg (cs s 1) 0 = 1.
Proof.
  apply startV.
  eapply fwdV. { early 1 2 (DSt Plain [0] 1) 2. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 0. STa 0. } { nwP. } nameV.
  eapply fwdV. { ord 0. apply e_ss. } { nwP. } nameV.
  eapply fwdV. { ord 0. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 1. LDw 3. } { nwP. } nameV.
  eapply fwdV. { ord 1. apply e_ll. } { nwP. } nameV.
  eapply fwdV. { mtch 1 (DSt Plain [0] 1). } { nwK. } nameV.
  FIN.
Qed.

(* ---------- guard.rs() between every pair (LBweakS, SweakS) ---------- *)
Definition LBs : prog := stat [ [ld 0; fss; st 1 1]; [ld 1; fss; st 0 1] ].
Theorem LBweakS_allowed : exists s, runQ LBs s /\ done LBs s /\ evok s /\
  rg (cs s 0) 0 = 1 /\ rg (cs s 1) 0 = 1.
Proof.
  apply startV.
  eapply fwdV. { early 0 1 (DFn FSs) 1. apply e_ss. } { nwP. } nameV.
  eapply fwdV. { early 0 2 (DSt Plain [1] 1) 2. ST. W0. } { nwP. } nameV.
  eapply fwdV. { early 1 1 (DFn FSs) 1. apply e_ss. } { nwP. } nameV.
  eapply fwdV. { early 1 2 (DSt Plain [0] 1) 2. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 0. LDw 3. } { nwP. } nameV.
  eapply fwdV. { mtch 0 (DFn FSs). } { nwK. } nameV.
  eapply fwdV. { mtch 0 (DSt Plain [1] 1). } { nwK. } nameV.
  eapply fwdV. { ord 1. LDw 1. } { nwP. } nameV.
  eapply fwdV. { mtch 1 (DFn FSs). } { nwK. } nameV.
  eapply fwdV. { mtch 1 (DSt Plain [0] 1). } { nwK. } nameV.
  FIN.
Qed.

Definition Ss : prog := stat [ [st 0 2; fss; st 1 1]; [ld 1; fss; st 0 1] ].
Theorem SweakS_allowed : exists s, runQ Ss s /\ done Ss s /\ evok s /\
  final s 0 = 2 /\ rg (cs s 1) 0 = 1.
Proof.
  apply startV.
  eapply fwdV. { early 1 1 (DFn FSs) 1. apply e_ss. } { nwP. } nameV.
  eapply fwdV. { early 1 2 (DSt Plain [0] 1) 2. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 0. STa 1. } { nwP. } nameV.
  eapply fwdV. { ord 0. apply e_ss. } { nwP. } nameV.
  eapply fwdV. { ord 0. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 1. LDw 4. } { nwP. } nameV.
  eapply fwdV. { mtch 1 (DFn FSs). } { nwK. } nameV.
  eapply fwdV. { mtch 1 (DSt Plain [0] 1). } { nwK. } nameV.
  FIN.
Qed.

(* ---------- own read, dependencies ---------- *)
Definition FWDLDp : prog := stat [ [st 0 1; ld 0; fll; st 1 1]; [ld 1; ffull; ld 0] ].
Theorem FWDLD_allowed : exists s, runQ FWDLDp s /\ done FWDLDp s /\ evok s /\
  rg (cs s 0) 1 = 1 /\ rg (cs s 1) 0 = 1 /\ rg (cs s 1) 2 = 0.
Proof.
  apply startV.
  eapply fwdV. { early 0 3 (DSt Plain [1] 1) 3. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 1. LDw 0. } { nwP. } nameV.
  eapply fwdV. { ord 1. apply e_full. } { nwP. } nameV.
  eapply fwdV. { ord 1. LD0. } { nwP. } nameV.
  eapply fwdV. { ord 0. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 0. LDw 4. } { nwP. } nameV.
  eapply fwdV. { ord 0. apply e_ll. } { nwP. } nameV.
  eapply fwdV. { mtch 0 (DSt Plain [1] 1). } { nwK. } nameV.
  FIN.
Qed.

Definition LBdata1p : prog := stat [ [ld 0; ISt Plain [1] T (RG 0)]; [ld 1; st 0 1] ].
Theorem LBdata1_allowed : exists s, runQ LBdata1p s /\ done LBdata1p s /\ evok s /\
  rg (cs s 0) 0 = 1 /\ rg (cs s 1) 0 = 1.
Proof.
  apply startV.
  eapply fwdV. { early 1 1 (DSt Plain [0] 1) 1. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 0. LDw 0. } { nwP. } nameV.
  eapply fwdV. { ord 0. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 1. LDw 2. } { nwP. } nameV.
  eapply fwdV. { mtch 1 (DSt Plain [0] 1). } { nwK. } nameV.
  FIN.
Qed.

(* a false dependency: the stored value is 0 * r + 1 *)
Definition FD (j : nat) : regs -> val := fun r => 0 * r j + 1.
Definition LBfalsep : prog := stat [ [ld 0; ISt Plain [1] T (FD 0)]; [ld 1; ISt Plain [0] T (FD 0)] ].
Theorem LBfalse_allowed : exists s, runQ LBfalsep s /\ done LBfalsep s /\ evok s /\
  rg (cs s 0) 0 = 1 /\ rg (cs s 1) 0 = 1.
Proof.
  apply startV.
  eapply fwdV. { early 1 1 (DSt Plain [0] 1) 1. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 0. LDw 0. } { nwP. } nameV.
  eapply fwdV. { ord 0. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 1. LDw 2. } { nwP. } nameV.
  eapply fwdV. { mtch 1 (DSt Plain [0] 1). } { nwK. } nameV.
  FIN.
Qed.

Definition LBfdp : prog := stat [ [ld 1; ISt Plain [0] (EQ 0 1) (K 1)]; [ld 0; fll; st 1 1] ].
Theorem LBfd_allowed : exists s, runQ LBfdp s /\ done LBfdp s /\ evok s /\
  rg (cs s 0) 0 = 1 /\ rg (cs s 1) 0 = 1.
Proof.
  apply startV.
  eapply fwdV. { early 1 2 (DSt Plain [1] 1) 2. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 0. LDw 0. } { nwP. } nameV.
  eapply fwdV. { ord 0. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 1. LDw 2. } { nwP. } nameV.
  eapply fwdV. { ord 1. apply e_ll. } { nwP. } nameV.
  eapply fwdV. { mtch 1 (DSt Plain [1] 1). } { nwK. } nameV.
  FIN.
Qed.

Definition LBctrl1p : prog := stat [ [ld 0; ISt Plain [1] (EQ 0 1) (K 1)]; [ld 1; st 0 1] ].
Theorem LBctrl1_allowed : exists s, runQ LBctrl1p s /\ done LBctrl1p s /\ evok s /\
  rg (cs s 0) 0 = 1 /\ rg (cs s 1) 0 = 1.
Proof.
  apply startV.
  eapply fwdV. { early 1 1 (DSt Plain [0] 1) 1. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 0. LDw 0. } { nwP. } nameV.
  eapply fwdV. { ord 0. ST. W0. } { nwP. } nameV.
  eapply fwdV. { ord 1. LDw 2. } { nwP. } nameV.
  eapply fwdV. { mtch 1 (DSt Plain [0] 1). } { nwK. } nameV.
  FIN.
Qed.
