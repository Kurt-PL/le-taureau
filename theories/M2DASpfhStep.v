(* T1 counter-run, step level (M2DA's model): while nothing of context 0 of
   SPFH has happened as an access (only CAS reads alone), no result is fixed at
   slot 2, and every read alone took 0 and is not a failure:
   - SPFH_nofix: s_cfix is enabled at neither place 1 nor place 2;
   - SPFH_noearly: x = 1 cannot happen early. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Inv M2Lit M2Cont M2CasSplitProof M2DASpfhInst.

Lemma insS : forall k r, ins SPFH 0 k r = nth k (nth 0 SPFHc []) INop.
Proof. intros k r. unfold SPFH. apply ins_stat. Qed.

Lemma W_S : wf SPFH.
Proof. unfold SPFH, SPFHc. wf_tac. Qed.

Lemma pend_none0' : forall cc N r j, (forall k, oc cc k = None) -> pend_at SPFH 0 cc 0 N r j = None.
Proof. intros. apply pend_none0. auto. Qed.

(* nothing is placed at slot 0 as a CAS's read alone: slot 0 is a load *)
Lemma hpend0S : forall cc N r, hpend_at SPFH 0 cc 0 N r 0 = None.
Proof.
  intros cc N r. unfold hpend_at.
  assert (A : forall l, find (fun k => match oc cc k, oh cc k with
                 | None, Some t => match casx (ai cc k) with
                                   | Some (m, xs) => fab SPFH 0 cc 0 N r (S t) t (TH m xs) 0
                                   | None => false end
                 | _, _ => false end) l = None).
  { induction l as [|k l IH]; [reflexivity|]. simpl.
    destruct (oc cc k), (oh cc k); auto. destruct (casx (ai cc k)) as [[m xs]|]; auto. }
  apply A.
Qed.

Lemma pok0 : forall cc, (forall k, oc cc k = None) -> pend_ok cc 0.
Proof. intros cc H k O. exfalso. apply O. apply H. Qed.

(* register 0 is the free value of y *)
Lemma creg0S : forall cc N B f, (forall k, oc cc k = None) -> creg SPFH 0 cc 0 N B f 0 = f 0 1.
Proof.
  intros cc N B f P. unfold creg. simpl. unfold slotv. simpl.
  rewrite (pend_none0' cc N _ 0 P), hpend0S. reflexivity.
Qed.

Theorem SPFH_nofix : forall cc N j b B o, (j = 1 \/ j = 2) -> (forall k, oc cc k = None) ->
  ~ cfix_ok SPFH 0 cc 0 N j b B o.
Proof.
  intros cc N j b B o J P (v & H).
  destruct J as [->| ->].
  - destruct (H (fun _ _ => 1)) as (_ & Ic & _). cbv zeta in Ic.
    change (Nat.eqb (creg SPFH 0 cc 0 N (bor (bd cc) B) (fun _ _ => 1) 0) 0 = true) in Ic.
    rewrite creg0S in Ic by exact P. discriminate Ic.
  - destruct (H (fun _ _ => 0)) as (_ & Ic & _). cbv zeta in Ic.
    change (negb (Nat.eqb (creg SPFH 0 cc 0 N (bor (bd cc) B) (fun _ _ => 0) 0) 0) = true) in Ic.
    rewrite creg0S in Ic by exact P. discriminate Ic.
Qed.

(* the free values R1 is checked against below: y is 7, every bit a success,
   x is 0 *)
Definition f7 : nat -> cell -> val := fun _ x => if Nat.eqb x 0 then 0 else 7.

Lemma hpend_oh : forall p c cc pc N r j k, hpend_at p c cc pc N r j = Some k -> oh cc k <> None.
Proof.
  intros p c cc pc N r j k H. unfold hpend_at in H. apply find_some' in H as (_ & F).
  destruct (oc cc k), (oh cc k); congruence.
Qed.

Lemma slot2 : forall cc N B r, (forall k, oc cc k = None) -> fx cc 2 = None ->
  (forall k, oh cc k <> None -> rg cc k = vd true 0) -> r 0 = 7 ->
  slotv SPFH 0 cc 0 N B f7 r 2 = vd true 0.
Proof.
  intros cc N B r P Fx Hr R0. unfold slotv. cbn [Nat.ltb Nat.leb].
  rewrite !insS. change (nth 2 (nth 0 SPFHc []) INop) with (ICas Plain [0] (NE 0 0) (K 0) (K 5)).
  assert (C : icond (ICas Plain [0] (NE 0 0) (K 0) (K 5)) r = true) by (unfold icond, ieval, NE; rewrite R0; reflexivity).
  rewrite C. cbn [is_load andb]. rewrite (pend_none0' cc N r 2 P).
  unfold cfx. rewrite Fx. cbn [is_cas].
  assert (Fb : fbit f7 (ICas Plain [0] (NE 0 0) (K 0) (K 5)) 2 = true) by reflexivity.
  rewrite Fb.
  destruct (hpend_at SPFH 0 cc 0 N r 2) as [k|] eqn:Hk.
  - rewrite (Hr k (hpend_oh _ _ _ _ _ _ _ _ Hk)). rewrite vok_vd, vv_vd.
    unfold cfailv. rewrite vok_vd, vv_vd. unfold NE, K. rewrite R0. reflexivity.
  - change (icells (ICas Plain [0] (NE 0 0) (K 0) (K 5))) with [0]. cbn [map enc].
    assert (V : cellv SPFH 0 cc 0 N B f7 r 2 2 0 = 0).
    { cbn [cellv Nat.ltb]. rewrite insS. change (nth 2 (nth 0 SPFHc []) INop) with (ICas Plain [0] (NE 0 0) (K 0) (K 5)).
      rewrite C. cbn [is_load andb]. rewrite (pend_none0' cc N r 2 P), Hk.
      destruct (B 2); [|reflexivity].
      unfold fbinder. rewrite insS. change (nth 2 (nth 0 SPFHc []) INop) with (ICas Plain [0] (NE 0 0) (K 0) (K 5)).
      rewrite C. cbn [bread andb icells dd nodup existsb Nat.eqb orb].
      match goal with |- context [fbind ?p ?c ?r ?i ?x ?b] =>
        assert (Fn : fbind p c r i x b = None) end.
      { cbn [fbind]. rewrite !insS. cbn [nth SPFHc]. unfold executes, icond, ieval, EQ. rewrite R0. reflexivity. }
      rewrite Fn. reflexivity. }
    rewrite V. reflexivity.
Qed.

Lemma eof_j3 : forall j r, r 0 = 7 -> eof (ins SPFH 0 j r) r = Some (DSt Plain [0] 1) -> j = 3.
Proof.
  intros j r R0 E. rewrite insS in E. destruct j as [|[|[|[|j]]]]; cbn [nth SPFHc] in E.
  - discriminate E.
  - unfold eof, dof, EQ in E. rewrite R0 in E. discriminate E.
  - unfold eof, dof, NE in E. rewrite R0 in E. discriminate E.
  - reflexivity.
  - destruct j; discriminate E.
Qed.

Theorem SPFH_noearly : forall cc N T u B, (forall k, oc cc k = None) -> fx cc 2 = None ->
  (forall k, oh cc k <> None -> rg cc k = vd true 0) ->
  ~ early_ok SPFH 0 cc 0 N T (DSt Plain [0] 1) u B.
Proof.
  intros cc N T u B P Fx Hr H.
  destruct (H f7) as (j & Lj & F & _). cbv zeta in F.
  set (r := creg SPFH 0 cc 0 N (bor (bd cc) B) f7) in F.
  assert (R0 : r 0 = 7) by (unfold r; rewrite creg0S by exact P; reflexivity).
  assert (R2 : r 2 = vd true 0).
  { unfold r. rewrite (creg_fix SPFH W_S 0 cc 0 N _ f7 2 (pok0 cc P)). fold r. apply slot2; auto. }
  unfold first_at in F. cbn [plc first_in] in F. destruct F as (_ & E & _ & All).
  pose proof (eof_j3 j r R0 E) as ->.
  assert (I2 : ins SPFH 0 2 r = ICas Plain [0] (NE 0 0) (K 0) (K 5)) by (rewrite insS; reflexivity).
  destruct (All 2 ltac:(lia) ltac:(lia)) as (k' & t' & d' & (_ & Ok & _) & Oc & _).
  - rewrite I2. unfold executes, icond, ieval, NE. rewrite R0. reflexivity.
  - intros v (k' & t' & m' & xs' & _ & _ & _ & _ & _ & ->). rewrite R2, I2.
    unfold cfailv. rewrite vok_vd, vv_vd. unfold NE, K. rewrite R0. reflexivity.
  - rewrite I2. apply (tied_cell _ _ 0); simpl; auto.
  - rewrite (P k') in Ok. apply Ok. reflexivity.
Qed.

Print Assumptions SPFH_nofix.
Print Assumptions SPFH_noearly.
