(* Part 61: NewKc3 from the guard() invariant J of the earlier image, except one
   corner (CO2n).
   At the new entry t of context c (image entry e, state entry eW), an item a of eQ e or eQc e
   is, up to a double negation (Og_cases):
   - in vOg(c) of the image: then, by UK's u_Og, in eQ eW or stood for by a store in eQ eW;
     the image's vOg(c) holds a whenever c knows a in order (j3), or a is c's own store taken in
     order (tookord), by J at the earlier image;
   - known by eW, or stood for by a store eW knows;
   - CO2n: t takes in the image a store a that is not c's, while the state's entry takes c's own
     written-back store w0 standing for a, which c does not know in order.
   NewKc3_of_J: if J holds at every evok image and CO2n has its path, NewKc3 holds; the
   per-cell paths come from the global one (path_cell, the tail of M2DQWBK55.co4_path). *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Lit.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB.
Require Import M2DQWBK1 M2DQWBK2 M2DQWBK3 M2DQWBK15 M2DQWBK17 M2DQWBK19 M2DQWBK20 M2DQWBK30 M2DQWBK37 M2DQWBK38 M2DQWBK39 M2DQWBK40.
Require Import M2DQWBK49 M2DQWBK50 M2DQWBK51 M2DQWBK52 M2DQWBK53 M2DQWBK54 M2DQWBK55 M2DQWBK57 M2DQWBK58.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

(* a gedge path into the entry gives the per-cell path in every cell it accesses *)
Section PC.
Variables (p : prog) (sw : nat -> option (cell -> option nat)) (s1 sA' : st) (t : nat) (e eW : oev).
Hypothesis RA' : run p sA'.
Hypothesis R1 : rel sw s1 sA'.
Hypothesis K1 : KR False G0 sw s1 sA'.
Hypothesis Ee : ent sA' t = Some e.
Hypothesis EW : ent s1 t = Some eW.
Hypothesis Ks : ksame sw s1 t e eW.
Hypothesis EV1 : evok s1.

Theorem path_cell : forall x a, Pth s1 a t -> In x (eC e) -> In a (ids (hs s1 x)) -> a <> t ->
  clos_trans nat (cedge s1 x) a t.
Proof.
  intros x a P Ix Ia N.
  pose proof Ks as (_ & _ & _ & KC & KR' & _ & _ & S8 & S9 & _).
  assert (cyc : forall a, Pth s1 a t -> gedge s1 t a -> False).
  { intros a0 P0 G0'. apply (proj1 EV1 t). apply (t_trans _ _ t a0 t); [constructor; exact G0'|exact P0]. }
  destruct (acc_cell p sA' t e x RA' Ee Ix) as [Ir|(We & It)].
  - rewrite KR' in Ir. destruct (erf eW x) as [u|] eqn:Eu.
    + destruct (Nat.eq_dec u a) as [->|Nu].
      * constructor. right; right; left. exists eW. auto.
      * pose proof (S8 x u Eu) as Iu.
        destruct (older_total (hs s1 x) a u Ia Iu (fun Z => Nu (eq_sym Z))) as [O|O].
        -- destruct (Nat.eq_dec u t) as [->|Nt]; [constructor; left; exact O|].
           apply (t_trans _ _ a u t); constructor; [left; exact O|]. right; right; left. exists eW. auto.
        -- exfalso. apply (cyc a P). right; left. exists eW, x. split; [exact EW|]. split; [exact Ir|].
           split; [exact Ia|]. split; [exact N|]. rewrite Eu. exact O.
    + exfalso. apply (cyc a P). right; left. exists eW, x. split; [exact EW|]. split; [exact Ir|].
      split; [exact Ia|]. split; [exact N|]. rewrite Eu. exact Logic.I.
  - assert (It1 : In t (ids (hs s1 x))).
    { destruct (in_ids_fl _ _ It) as [b Ib]. rewrite (r_hs sw s1 sA' R1 x) in Ib. apply in_hers in Ib.
      exact (in_ids_of _ _ _ (proj1 Ib)). }
    destruct (older_total (hs s1 x) a t Ia It1 N) as [O|O].
    + constructor. left. exact O.
    + exfalso. apply (cyc a P). left. exists x. exact O.
Qed.
End PC.

Section C.
Set Default Proof Using "All".
Variables (p : prog) (sw : nat -> option (cell -> option nat)) (sW sA sA' s1 : st) (e eW : oev).
Hypothesis RA : run p sA.
Hypothesis Rl : rel sw sW sA.
Hypothesis K : KR False G0 sw sW sA.
Hypothesis UK0 : UK sw sW sA.
Hypothesis RA' : run p sA'.
Hypothesis R1 : rel sw s1 sA'.
Hypothesis K1 : KR False G0 sw s1 sA'.
Hypothesis St : step p sW s1.
Hypothesis StA : step p sA sA'.
Hypothesis SG : forall x w a, seg (hs sW x) w (Some a) -> seg (hs s1 x) w (Some a).
Hypothesis Ee : ent sA' (tm sA) = Some e.
Hypothesis EW : ent s1 (tm sA) = Some eW.
Hypothesis Js : J p sA.

Let c := ec eW.

(* the two gates, with g = ew e || f *)
Lemma gates2 : exists f : bool,
  eQ e = (if ew e || f then vor (vOg (cs sA c)) (tookord sA c (vO (cs sA c)) (erf e)) else vnil) /\
  eQ eW = (if ew e || f then vor (vOg (cs sW c)) (tookord sW c (vO (cs sW c)) (erf eW)) else vnil) /\
  eQc e = (if f then vO (cs sA c) else vnil) /\ eQc eW = (if f then vO (cs sW c) else vnil).
Proof.
  pose proof (Ks p sw sW sA sA' s1 e eW RA Rl K UK0 RA' R1 K1 St StA SG Ee EW) as (_ & Ec & Ek & _ & _ & _ & _ & _ & _ & Ew).
  pose proof (step_newQ p sA sA' e StA (i_tm p sA (Inv1_run p sA RA)) Ee) as (QA & QcA).
  assert (EW' : ent s1 (tm sW) = Some eW) by (rewrite <- (Et p sw sW sA sA' s1 e eW RA Rl K UK0 RA' R1 K1 St StA SG Ee EW); exact EW).
  pose proof (step_newQ p sW s1 eW St (tmW p False G0 sw sW sA RA Rl K) EW') as (QW & QcW).
  cbv zeta in QA, QcA, QW, QcW.
  assert (Sw : sw (tm sA) = None) by (apply (i_sw sw sW sA Rl); rewrite (Et p sw sW sA sA' s1 e eW RA Rl K UK0 RA' R1 K1 St StA SG Ee EW); lia).
  rewrite (Ew Sw) in QW. rewrite Ec, Ek in QA, QcA.
  destruct (crel_eq p False G0 sw s1 sA' RA' R1 K1 (ec eW)) as (_ & _ & Ai & _).
  destruct (crel_eq p False G0 sw sW sA RA Rl K (ec eW)) as (_ & _ & _ & Rg & _).
  rewrite Ai, Rg in QA, QcA.
  exists (xload (ai (cs s1 (ec eW)) (ek eW)) (rg (cs sW (ec eW)))).
  auto.
Qed.

Definition CO2n (a : nat) : Prop :=
  exists x w0 f, erf e x = Some a /\ erf eW x = Some w0 /\ sw w0 = Some f /\ f x = Some a /\
    ownw sW c w0 /\ ~ vO (cs sW c) w0 /\ ~ ownw sA c a.

(* what the image's entry knows: in the image's vOg, known by eW, stood for by a store eW knows, or CO2n *)
Theorem Og_cases : forall a, (eQ e a \/ eQc e a) ->
  ~ ~ (vOg (cs sA c) a \/ eQ eW a \/ (exists w x, eQ eW w /\ seg (hs s1 x) w (Some a)) \/ CO2n a).
Proof.
  intros a Q N. destruct gates2 as (f & QA & QW & QcA & QcW).
  destruct Q as [Q|Q].
  - rewrite QA in Q. destruct (ew e || f) eqn:G; [|contradiction].
    destruct Q as [Og|((x & Ex) & Nown)].
    + apply N. left. exact Og.
    + destruct (ownw_dec2 sA c a) as [Oa|Na].
      * apply Nown. split; [exact Oa|]. intros OA. apply (j3 p sA Js c a OA). intros Og. apply N. left. exact Og.
      * pose proof (Ks p sw sW sA sA' s1 e eW RA Rl K UK0 RA' R1 K1 St StA SG Ee EW) as (_ & _ & _ & _ & _ & _ & S7 & _).
        rewrite (S7 x) in Ex. destruct (erf eW x) as [w0|] eqn:Ew0; [|discriminate]. cbn [pi] in Ex.
        destruct (sw w0) as [g|] eqn:Sw.
        -- destruct (ownw_dec2 sW c w0) as [Ow|Nw].
           ++ apply N. right; right; right. exists x, w0, g. split; [rewrite (S7 x), Ew0; cbn [pi]; rewrite Sw; exact Ex|].
              split; [exact Ew0|]. split; [exact Sw|]. split; [exact Ex|]. split; [exact Ow|]. split; [|exact Na].
              intros Ov. apply N. right; right; left. exists w0, x. split.
              ** rewrite QW; try rewrite G. right. split; [exists x; exact Ew0|]. intros (_ & NO). exact (NO Ov).
              ** rewrite <- Ex. exact (wb_read p sw sW sA sA' s1 e eW RA Rl K UK0 RA' R1 K1 St StA SG Ee EW x w0 g Ew0 Sw).
           ++ apply N. right; right; left. exists w0, x. split.
              ** rewrite QW; try rewrite G. right. split; [exists x; exact Ew0|]. intros (Ow & _). exact (Nw Ow).
              ** rewrite <- Ex. exact (wb_read p sw sW sA sA' s1 e eW RA Rl K UK0 RA' R1 K1 St StA SG Ee EW x w0 g Ew0 Sw).
        -- injection Ex as <-. apply N. right; left. rewrite QW; try rewrite G. right. split; [exists x; exact Ew0|].
           intros (Ow & _). apply Na. exact (own_kept p sw sW sA sA' s1 e eW RA Rl K UK0 RA' R1 K1 St StA SG Ee EW w0 Ow Sw).
  - rewrite QcA in Q. destruct f; [|contradiction].
    apply (j3 p sA Js c a Q). intros Og. apply N. left. exact Og.
Qed.

(* from the image's vOg: known by eW or stood for by a store eW knows *)
Lemma Og_up : forall a, vOg (cs sA c) a -> (eQ e a \/ eQc e a) ->
  ~ ~ (eQ eW a \/ exists w x, eQ eW w /\ seg (hs s1 x) w (Some a)).
Proof.
  intros a Og Q N. destruct gates2 as (f & QA & QW & QcA & QcW).
  assert (G : ew e || f = true).
  { destruct Q as [Q|Q]; [rewrite QA in Q; destruct (ew e || f); [reflexivity|contradiction]|].
    rewrite QcA in Q. destruct f; [apply orb_true_r|contradiction]. }
  rewrite G in QW.
  destruct (u_Og sw sW sA UK0 c a Og) as [Z|(w & x & Vw & Sg)].
  - apply N. left. rewrite QW. left. exact Z.
  - apply N. right. exists w, x. split; [rewrite QW; left; exact Vw|exact (SG x w a Sg)].
Qed.
End C.

Print Assumptions path_cell.
Print Assumptions Og_cases.
Print Assumptions Og_up.
