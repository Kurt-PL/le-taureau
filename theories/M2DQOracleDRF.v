(* Oracle rows (oracle/ORACLE.md), excluded outcomes of race-free programmes
   and out of thin air, on M2DQ.
   - DRF.C3Cex and OOTActrl: race-free (M2Trap's checked enumeration), so
     every finished run is an SC interleaving (M2DQIfaceUse.drf_sc_dq), and
     the checked enumeration (M2EnumG.enum_sc_outcome) shows that no
     interleaving has the outcome.
   - OOTA: every value written or read is 0 (M2DQOota.no_thin_air_Q with
     V = {0}), so no load reads 1.
   Cells: x = 0, y = 1, c = 2. A branch is the condition of the
   instructions in it. *)
From Stdlib Require Import Arith Lia List Bool PArith.
Import ListNotations.
Require Import M2Model M2Inv M2SC M2Lit M2Oota M2EnumG M2Trap M2DQ M2DQOota M2DQIfaceUse M2DQShim.

(* a finished run has passed every instruction of the code *)
Lemma done_lt : forall P s c j, done (stat P) s -> c < length P -> nth j (nth c P []) INop <> INop -> j < pcs s c.
Proof.
  intros P s c j (n & F & Cm) Lc Nj. destruct (Cm c ltac:(unfold stat; rewrite length_map; exact Lc)) as [Le _].
  destruct (Nat.lt_ge_cases j (pcs s c)) as [L|G]; [exact L|].
  exfalso. apply Nj. rewrite <- (ins_stat P c j (fun _ => 0)). apply F. lia.
Qed.

(* no SC interleaving of a one-cell programme shows the outcome obs *)
Lemma stat_sc_outcome : forall P M fuel obs, wf (stat P) -> forallb (forallb onecellb) P = true ->
  closed2 (stat P) (map (@length instr) P) M (sfut P) (sex P) (reach (stat P) (map (@length instr) P) M (sfut P) (sex P) fuel) = true ->
  out_ok (reach (stat P) (map (@length instr) P) M (sfut P) (sex P) fuel) obs = true ->
  obs_ok (map (@length instr) P) obs = true ->
  forall l g, srun (stat P) l g -> (forall c j v, In (c, j, v) obs -> j < sp g c) ->
  ~ (forall c j v, In (c, j, v) obs -> sr g c j = v).
Proof.
  intros P M fuel obs W O C Ok Ob.
  exact (enum_sc_outcome (stat P) (map (@length instr) P) M W (stat_fin' P) (stat_out P) (sfut P) (sfut_spec P)
    (stat_one P O) (sfut_mono P) (sex P) (sex_fa P) _ obs (closed2_closed _ _ _ _ _ _ C) Ok Ob).
Qed.

(* ---------- DRF.C3Cex ----------
     E1: u = y; if u == 1 { x = 1 } else { c = 1; r = c; if r == 0 { x = 1 } }
     E2: t = x; if t == 1 { y = 1 }
   outcome u = 1, t = 1 *)
Definition C3c : list (list instr) :=
  [ [ld 1; ISt Plain [0] (EQ 0 1) (K 1); ISt Plain [2] (NE 0 1) (K 1); ILd Plain [2] (NE 0 1);
     ISt Plain [0] (fun r => negb (Nat.eqb (r 0) 1) && Nat.eqb (r 3) 0) (K 1)];
    [ld 0; ISt Plain [1] (EQ 0 1) (K 1)] ].
Definition C3 : prog := stat C3c.

Lemma C3_wf : wf C3.
Proof. unfold C3, C3c. wf_tac. Qed.

Lemma C3_cellful : cellful C3.
Proof.
  apply cellful_of. intros c k r A. unfold C3, C3c in *. rewrite ins_stat in *.
  destruct c as [|[|c]]; [| |destruct c]; destruct k as [|[|[|[|[|k]]]]]; try destruct k; cbn in A |- *; discriminate.
Qed.

Lemma C3_race_free : race_free_g C3.
Proof. unfold C3. apply (stat_race_free_g _ 3 1000%positive); [exact C3_wf|vm_compute; reflexivity|vm_compute; reflexivity]. Qed.

Theorem C3Cex_forbidden_Q : forall s, runQ C3 s -> done C3 s -> evok s -> ~ (rg (cs s 0) 0 = 1 /\ rg (cs s 1) 0 = 1).
Proof.
  intros s R D E [A B].
  destruct (drf_sc_dq C3 s C3_wf C3_cellful C3_race_free R D E) as (l & g & SR & Hp & Hr & _).
  assert (L0 : 0 < pcs s 0) by (apply (done_lt C3c s 0 0 D); [vm_compute; lia|discriminate]).
  assert (L1 : 0 < pcs s 1) by (apply (done_lt C3c s 1 0 D); [vm_compute; lia|discriminate]).
  apply (stat_sc_outcome C3c 3 1000%positive [(0, 0, 1); (1, 0, 1)] C3_wf ltac:(vm_compute; reflexivity)
           ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) l g SR).
  - intros c j v [H|[H|[]]]; inversion H; subst; rewrite Hp; assumption.
  - intros c j v [H|[H|[]]]; inversion H; subst; rewrite Hr by assumption; assumption.
Qed.

(* ---------- OOTActrl ----------
     r1 = x; if r1 == 1 { y = 1 }  ||  r3 = y; if r3 == 1 { x = 1 }
   outcome r1 = 1, r3 = 1 *)
Definition OCc : list (list instr) :=
  [ [ld 0; ISt Plain [1] (EQ 0 1) (K 1)]; [ld 1; ISt Plain [0] (EQ 0 1) (K 1)] ].
Definition OC : prog := stat OCc.

Lemma OC_wf : wf OC.
Proof. unfold OC, OCc. wf_tac. Qed.

Lemma OC_cellful : cellful OC.
Proof.
  apply cellful_of. intros c k r A. unfold OC, OCc in *. rewrite ins_stat in *.
  destruct c as [|[|c]]; [| |destruct c]; destruct k as [|[|k]]; try destruct k; cbn in A |- *; discriminate.
Qed.

Lemma OC_race_free : race_free_g OC.
Proof. unfold OC. apply (stat_race_free_g _ 2 1000%positive); [exact OC_wf|vm_compute; reflexivity|vm_compute; reflexivity]. Qed.

Theorem OOTActrl_forbidden_Q : forall s, runQ OC s -> done OC s -> evok s -> ~ (rg (cs s 0) 0 = 1 /\ rg (cs s 1) 0 = 1).
Proof.
  intros s R D E [A B].
  destruct (drf_sc_dq OC s OC_wf OC_cellful OC_race_free R D E) as (l & g & SR & Hp & Hr & _).
  assert (L0 : 0 < pcs s 0) by (apply (done_lt OCc s 0 0 D); [vm_compute; lia|discriminate]).
  assert (L1 : 0 < pcs s 1) by (apply (done_lt OCc s 1 0 D); [vm_compute; lia|discriminate]).
  apply (stat_sc_outcome OCc 2 1000%positive [(0, 0, 1); (1, 0, 1)] OC_wf ltac:(vm_compute; reflexivity)
           ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) l g SR).
  - intros c j v [H|[H|[]]]; inversion H; subst; rewrite Hp; assumption.
  - intros c j v [H|[H|[]]]; inversion H; subst; rewrite Hr by assumption; assumption.
Qed.

(* ---------- OOTA ----------
     r1 = x; y = r1  ||  r3 = y; x = r3
   outcome r1 = 1, r3 = 1 *)
Definition OTc : list (list instr) := [ [ld 0; ISt Plain [1] T (RG 0)]; [ld 1; ISt Plain [0] T (RG 0)] ].
Definition OT : prog := stat OTc.

Lemma OT_wf : wf OT.
Proof. unfold OT, OTc. wf_tac. Qed.

(* every value is 0: a store writes the register of the load before it *)
Lemma OT_closed : tclosed OT (fun v => v = 0).
Proof.
  intros c k r Hr. unfold OT, OTc in *. rewrite ins_stat.
  destruct c as [|[|c]]; [| |destruct c]; destruct k as [|[|k]]; try destruct k;
    cbn; (apply cl_one; [cbn; lia|reflexivity| |discriminate]);
    first [reflexivity | specialize (Hr 0 ltac:(lia)); rewrite ins_stat in Hr; exact (kV_ld1 _ _ _ _ _ Hr)].
Qed.

(* the register of a passed load is in V *)
Lemma OT_reg0 : forall s c, runQ OT s -> done OT s -> c < 2 -> rg (cs s c) 0 = 0.
Proof.
  intros s c R D Lc. destruct (no_thin_air_Q OT (fun v => v = 0) OT_wf eq_refl OT_closed s R) as [_ K].
  assert (L : 0 < pcs s c) by (apply (done_lt OTc s c 0 D); [exact Lc|destruct c as [|[|c]]; [discriminate|discriminate|lia]]).
  pose proof (Inv1_run OT s R) as I. destruct (proj1 (i_cmA _ s I c 0) L) as (tau & T0).
  specialize (K c 0). rewrite (proj2 (i_set _ s I c 0 tau T0)) in K. unfold OT in K. rewrite ins_stat in K.
  destruct c as [|[|c]]; [| |lia]; exact (kV_ld1 _ _ _ _ _ K).
Qed.

Theorem OOTA_forbidden_Q : forall s, runQ OT s -> done OT s -> ~ (rg (cs s 0) 0 = 1 /\ rg (cs s 1) 0 = 1).
Proof. intros s R D [A _]. rewrite (OT_reg0 s 0 R D ltac:(lia)) in A. discriminate. Qed.
