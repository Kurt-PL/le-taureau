(* The counter-run to "M2DP within M2Model". SPFD is SPFH with the
   expected value of the second CAS changed (7 for 0):
     SPFD: r0 = y; [r0 = 0] CAS(x, 0, 5); [r0 <> 0] CAS(x, 7, 5); x = 1  ||  r1 = x; y = r1
   Step-level facts of M2Model (whole CAS steps included) while nothing of
   context 0 has happened and pc 0 = 0:
   - SPFD_nofix_any: s_cfix is enabled at no place;
   - SPFD_noearly: no access of context 0 can happen early. The two claims
     of a hoisted CAS differ in their expected value, so no one description
     is the place under every valuation; x = 1 is blocked by place 1, whose
     CAS may succeed when y is 0;
   - SPFD_nocwe: no store part of context 0 can happen early. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Inv M2Lit M2Cont M2CasSplitProof M2DASpfhStep.

Definition SPFDc : list (list instr) :=
  [ [ld 1; ICas Plain [0] (EQ 0 0) (K 0) (K 5); ICas Plain [0] (NE 0 0) (K 7) (K 5); st 0 1];
    [ld 0; ISt Plain [1] T (RG 0)] ].
Definition SPFD : prog := stat SPFDc.

Lemma insD : forall k r, ins SPFD 0 k r = nth k (nth 0 SPFDc []) INop.
Proof. intros k r. unfold SPFD. apply ins_stat. Qed.

Lemma W_D : wf SPFD.
Proof. unfold SPFD, SPFDc. wf_tac. Qed.

Lemma hpend0D : forall cc N r, hpend_at SPFD 0 cc 0 N r 0 = None.
Proof.
  intros cc N r. unfold hpend_at.
  assert (A : forall l, find (fun k => match oc cc k, oh cc k with
                 | None, Some t => match casx (ai cc k) with
                                   | Some (m, xs) => fab SPFD 0 cc 0 N r (S t) t (TH m xs) 0
                                   | None => false end
                 | _, _ => false end) l = None).
  { induction l as [|k l IH]; [reflexivity|]. simpl.
    destruct (oc cc k), (oh cc k); auto. destruct (casx (ai cc k)) as [[m xs]|]; auto. }
  apply A.
Qed.

(* register 0 is the free value of y *)
Lemma creg0D : forall cc N B f, (forall k, oc cc k = None) -> creg SPFD 0 cc 0 N B f 0 = f 0 1.
Proof.
  intros cc N B f P. unfold creg. simpl. unfold slotv. simpl.
  rewrite (pend_none0 SPFD 0 cc N _ 0 P), hpend0D. reflexivity.
Qed.

Lemma iscD : forall j r, is_cas (ins SPFD 0 j r) = true -> j = 1 \/ j = 2.
Proof. intros j r C. rewrite insD in C. destruct j as [|[|[|[|j]]]]; cbn in C; try discriminate; auto. destruct j; discriminate. Qed.

Theorem SPFD_nofix_any : forall cc N j b B o, (forall k, oc cc k = None) -> ~ cfix_ok SPFD 0 cc 0 N j b B o.
Proof.
  intros cc N j b B o P (v & H).
  destruct (H (fun _ _ => 0)) as (Ci & _). cbv zeta in Ci. apply iscD in Ci.
  destruct Ci as [->| ->].
  - destruct (H (fun _ _ => 1)) as (_ & Ic & _). cbv zeta in Ic.
    change (Nat.eqb (creg SPFD 0 cc 0 N (bor (bd cc) B) (fun _ _ => 1) 0) 0 = true) in Ic.
    rewrite creg0D in Ic by exact P. discriminate Ic.
  - destruct (H (fun _ _ => 0)) as (_ & Ic & _). cbv zeta in Ic.
    change (negb (Nat.eqb (creg SPFD 0 cc 0 N (bor (bd cc) B) (fun _ _ => 0) 0) 0) = true) in Ic.
    rewrite creg0D in Ic by exact P. discriminate Ic.
Qed.

(* the descriptions under y = 7 and under y = 0 *)
Lemma eofD7 : forall j r d, r 0 = 7 -> eof (ins SPFD 0 j r) r = Some d ->
  (j = 0 /\ d = DLd Plain [1]) \/ (j = 2 /\ d = DCas Plain [0] 7 5) \/ (j = 3 /\ d = DSt Plain [0] 1).
Proof.
  intros j r d R0 E. rewrite insD in E. destruct j as [|[|[|[|j]]]]; cbn [nth SPFDc] in E.
  - injection E as <-. auto.
  - unfold eof, dof, EQ in E. rewrite R0 in E. discriminate E.
  - unfold eof, dof, NE in E. rewrite R0 in E. injection E as <-. auto.
  - injection E as <-. auto.
  - destruct j; discriminate E.
Qed.

Lemma eofD0 : forall j r d, r 0 = 0 -> eof (ins SPFD 0 j r) r = Some d ->
  (j = 0 /\ d = DLd Plain [1]) \/ (j = 1 /\ d = DCas Plain [0] 0 5) \/ (j = 3 /\ d = DSt Plain [0] 1).
Proof.
  intros j r d R0 E. rewrite insD in E. destruct j as [|[|[|[|j]]]]; cbn [nth SPFDc] in E.
  - injection E as <-. auto.
  - unfold eof, dof, EQ in E. rewrite R0 in E. injection E as <-. auto.
  - unfold eof, dof, NE in E. rewrite R0 in E. discriminate E.
  - injection E as <-. auto.
  - destruct j; discriminate E.
Qed.

Lemma eofRD7 : forall j r m xs, r 0 = 7 -> eofR (ins SPFD 0 j r) r = Some (m, xs) -> j = 2 /\ m = Plain /\ xs = [0].
Proof.
  intros j r m xs R0 E. rewrite insD in E. destruct j as [|[|[|[|j]]]]; cbn [nth SPFDc] in E.
  - discriminate E.
  - unfold eofR, EQ in E. rewrite R0 in E. discriminate E.
  - unfold eofR, NE in E. rewrite R0 in E. injection E as <- <-. auto.
  - discriminate E.
  - destruct j; discriminate E.
Qed.

(* the free values: y is 0 for slot 0, every bit a success, x is 0 *)
Definition fz : nat -> cell -> val := fun j x => if Nat.eqb x 0 then 0 else if Nat.eqb j 0 then 0 else 7.

Lemma slot1D : forall cc N B r, (forall k, oc cc k = None) -> fx cc 1 = None ->
  (forall k, oh cc k <> None -> rg cc k = vd true 0) -> r 0 = 0 ->
  slotv SPFD 0 cc 0 N B fz r 1 = vd true 0.
Proof.
  intros cc N B r P Fx Hr R0. unfold slotv. cbn [Nat.ltb Nat.leb].
  rewrite !insD. change (nth 1 (nth 0 SPFDc []) INop) with (ICas Plain [0] (EQ 0 0) (K 0) (K 5)).
  assert (C : icond (ICas Plain [0] (EQ 0 0) (K 0) (K 5)) r = true) by (unfold icond, ieval, EQ; rewrite R0; reflexivity).
  rewrite C. cbn [is_load andb]. rewrite (pend_none0 SPFD 0 cc N r 1 P).
  unfold cfx. rewrite Fx. cbn [is_cas].
  assert (Fb : fbit fz (ICas Plain [0] (EQ 0 0) (K 0) (K 5)) 1 = true) by reflexivity.
  rewrite Fb.
  destruct (hpend_at SPFD 0 cc 0 N r 1) as [k|] eqn:Hk.
  - rewrite (Hr k (hpend_oh _ _ _ _ _ _ _ _ Hk)). rewrite vok_vd, vv_vd.
    unfold cfailv. rewrite vok_vd, vv_vd. unfold EQ, K. rewrite R0. reflexivity.
  - change (icells (ICas Plain [0] (EQ 0 0) (K 0) (K 5))) with [0]. cbn [map enc].
    assert (V : cellv SPFD 0 cc 0 N B fz r 1 1 0 = 0).
    { cbn [cellv Nat.ltb]. rewrite insD. change (nth 1 (nth 0 SPFDc []) INop) with (ICas Plain [0] (EQ 0 0) (K 0) (K 5)).
      rewrite C. cbn [is_load andb]. rewrite (pend_none0 SPFD 0 cc N r 1 P), Hk.
      destruct (B 1); [|reflexivity].
      unfold fbinder. rewrite insD. change (nth 1 (nth 0 SPFDc []) INop) with (ICas Plain [0] (EQ 0 0) (K 0) (K 5)).
      rewrite C. cbn [bread andb icells dd nodup existsb Nat.eqb orb].
      match goal with |- context [fbind ?p ?c ?r ?i ?x ?b] =>
        assert (Fn : fbind p c r i x b = None) end.
      { cbn [fbind]. rewrite !insD. reflexivity. }
      rewrite Fn. reflexivity. }
    rewrite V. reflexivity.
Qed.

Lemma eof_j3D : forall j r, r 0 = 0 -> eof (ins SPFD 0 j r) r = Some (DSt Plain [0] 1) -> j = 3.
Proof.
  intros j r R0 E. destruct (eofD0 j r _ R0 E) as [(_ & X)|[(_ & X)|(-> & _)]]; [discriminate X|discriminate X|reflexivity].
Qed.

(* x = 1 cannot happen early: under fz the CAS at place 1 may succeed *)
Theorem SPFD_noearly_st : forall cc N T u B, (forall k, oc cc k = None) -> fx cc 1 = None ->
  (forall k, oh cc k <> None -> rg cc k = vd true 0) ->
  ~ early_ok SPFD 0 cc 0 N T (DSt Plain [0] 1) u B.
Proof.
  intros cc N T u B P Fx Hr H.
  destruct (H fz) as (j & Lj & F & _). cbv zeta in F.
  set (r := creg SPFD 0 cc 0 N (bor (bd cc) B) fz) in F.
  assert (R0 : r 0 = 0) by (unfold r; rewrite creg0D by exact P; reflexivity).
  assert (R1 : r 1 = vd true 0).
  { unfold r. rewrite (creg_fix SPFD W_D 0 cc 0 N _ fz 1 (pok0 cc P)). fold r. apply slot1D; auto. }
  unfold first_at in F. cbn [plc first_in] in F. destruct F as (_ & E & _ & All).
  pose proof (eof_j3D j r R0 E) as ->.
  assert (I1 : ins SPFD 0 1 r = ICas Plain [0] (EQ 0 0) (K 0) (K 5)) by (rewrite insD; reflexivity).
  destruct (All 1 ltac:(lia) ltac:(lia)) as (k' & t' & d' & (_ & Ok & _) & Oc & _).
  - rewrite I1. unfold executes, icond, ieval, EQ. rewrite R0. reflexivity.
  - intros v (k' & t' & m' & xs' & _ & _ & _ & _ & _ & ->). rewrite R1, I1.
    unfold cfailv. rewrite vok_vd, vv_vd. unfold EQ, K. rewrite R0. reflexivity.
  - rewrite I1. apply (tied_cell _ _ 0); simpl; auto.
  - rewrite (P k') in Ok. apply Ok. reflexivity.
Qed.

(* no access of context 0 can happen early *)
Theorem SPFD_noearly : forall cc N T d u B, (forall k, oc cc k = None) -> fx cc 1 = None ->
  (forall k, oh cc k <> None -> rg cc k = vd true 0) ->
  ~ early_ok SPFD 0 cc 0 N T d u B.
Proof.
  intros cc N T d u B P Fx Hr H. pose proof H as H'.
  destruct (H f7) as (j & Lj & F & _). destruct (H fz) as (j' & Lj' & F' & _). cbv zeta in F, F'.
  apply first_at_eof in F. apply first_at_eof in F'.
  assert (R7 : creg SPFD 0 cc 0 N (bor (bd cc) B) f7 0 = 7) by (rewrite creg0D by exact P; reflexivity).
  assert (R0 : creg SPFD 0 cc 0 N (bor (bd cc) B) fz 0 = 0) by (rewrite creg0D by exact P; reflexivity).
  destruct (eofD7 _ _ _ R7 F) as [(-> & _)|[(_ & ->)|(_ & ->)]]; [lia| |exact (SPFD_noearly_st cc N T u B P Fx Hr H')].
  destruct (eofD0 _ _ _ R0 F') as [(_ & X)|[(_ & X)|(_ & X)]]; discriminate X.
Qed.

(* no store part of context 0 can happen early: its claim would carry
   expected value 7 under y = 7 and 0 under y = 0 *)
Theorem SPFD_nocwe : forall cc N T T1 xs ev nv B, (forall k, oc cc k = None) ->
  ~ early_okW SPFD 0 cc 0 N T T1 Plain xs (DCas Plain xs ev nv) B.
Proof.
  intros cc N T T1 xs ev nv B P H.
  destruct (H f7) as (j & _ & _ & E & _). destruct (H fz) as (j' & _ & _ & E' & _). cbv zeta in E, E'.
  assert (R7 : creg SPFD 0 cc 0 N (bor (bd cc) B) f7 0 = 7) by (rewrite creg0D by exact P; reflexivity).
  assert (R0 : creg SPFD 0 cc 0 N (bor (bd cc) B) fz 0 = 0) by (rewrite creg0D by exact P; reflexivity).
  destruct (eofD7 _ _ _ R7 E) as [(_ & X)|[(_ & X)|(_ & X)]]; try discriminate X.
  injection X as -> -> ->.
  destruct (eofD0 _ _ _ R0 E') as [(_ & X)|[(_ & X)|(_ & X)]]; discriminate X.
Qed.

Print Assumptions SPFD_nofix_any.
Print Assumptions SPFD_noearly.
Print Assumptions SPFD_nocwe.
