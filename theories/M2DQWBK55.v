(* Part 55: corner CO4 of M2DQWBK53 has its path, from evok of the state alone.
   The state's entry t knows a written-back store w standing for a in another cell x', so a -> w
   -> t is a path of the event graph (an edge of the history order, then a knowledge edge).  The
   entry accesses the cell x of a: if it writes x, a is older than t in x (else t -> a -> w -> t
   is a cycle); if it reads x, what it took there is a or newer (else t -> a is a from-read edge
   and again a cycle), so a -> (older) -> what it took -> (reads-from) -> t in the graph of x.
   NewKc3 / drf_sc_WB_of_corners3: G2 from the three corners CO1, CO2, CO3. *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Lit.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB.
Require Import M2DQWBK1 M2DQWBK2 M2DQWBK3 M2DQWBK15 M2DQWBK17 M2DQWBK19 M2DQWBK37 M2DQWBK38 M2DQWBK40.
Require Import M2DQWBK49 M2DQWBK50 M2DQWBK52 M2DQWBK53 M2DQWBK54.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

(* an access to a cell reads it, or writes it (and its store is in the cell's history) *)
Lemma acc_cell : forall p s t e x, run p s -> ent s t = Some e -> In x (eC e) ->
  In x (eR e) \/ (ew e = true /\ In t (ids (hs s x))).
Proof.
  intros p s t e x R E Ix. destruct (InvO_run p s R) as [I J L O].
  destruct (o_eRC p s O t e E) as [ER EC]. rewrite EC in Ix. unfold evC in Ix.
  destruct (isacc (einstr p s e) && icond (einstr p s e) (rgof s e)) eqn:A; [|contradiction].
  apply andb_true_iff in A. destruct A as [Ac Co].
  destruct (is_load (einstr p s e)) eqn:Ld.
  - left. rewrite ER. unfold evR. rewrite Ld, Co. exact Ix.
  - right. destruct (j_ew p s J t e (einstr p s e) E eq_refl) as [Ew Hs].
    assert (Eh : eh e = false).
    { destruct (eh e) eqn:Eh; [exfalso|reflexivity]. destruct (i_et p s I t e E) as [_ Oh]. rewrite Eh in Oh.
      unfold einstr in Ld. destruct (oc (cs s (ec e)) (ek e)) as [t2|] eqn:Oc.
      - destruct (i_hoc p s I (ec e) (ek e) t t2 Oh Oc) as [_ Cs]. destruct (ai (cs s (ec e)) (ek e)); discriminate.
      - destruct (le_lt_dec (pcs s (ec e)) (ek e)) as [Lk|Lk].
        + destruct (i_half p s I (ec e) (ek e) t Oc Oh Lk) as (_ & (xs & Ai) & _). rewrite Ai in Ld. discriminate.
        + destruct (i_halfp p s I (ec e) (ek e) t Oc Oh Lk) as (_ & (xs & Cx) & _).
          destruct (ai (cs s (ec e)) (ek e)); discriminate. }
    destruct (einstr p s e) as [m xs cd|m xs cd v|m xs cd ev nv|f|] eqn:Ei; cbn in Ld, Ac; try discriminate.
    unfold rgof in Co. cbn [icond ieval fst] in Co.
    assert (W1 : ew e = true) by (rewrite Ew, Eh; cbn [negb is_store is_cas icond ieval fst andb orb]; unfold rgof; rewrite Co; reflexivity).
    split; [exact W1|]. apply (proj2 (Hs W1) x). exact Ix.
Qed.

Section C4.
Set Default Proof Using "All".
Variables (p : prog) (sw : nat -> option (cell -> option nat)) (s1 sA' : st) (t : nat) (e eW : oev).
Hypothesis RA' : run p sA'.
Hypothesis R1 : rel sw s1 sA'.
Hypothesis K1 : KR False G0 sw s1 sA'.
Hypothesis Ee : ent sA' t = Some e.
Hypothesis EW : ent s1 t = Some eW.
Hypothesis Ks : ksame sw s1 t e eW.
Hypothesis EV1 : evok s1.

Lemma cyc : forall a, Pth s1 a t -> gedge s1 t a -> False.
Proof. intros a P G. apply (proj1 EV1 t). apply (t_trans _ _ t a t); [constructor; exact G|exact P]. Qed.

Theorem co4_path : forall x a, In x (eC e) -> In a (ids (hs s1 x)) -> a <> t -> CO4 s1 eW x a ->
  clos_trans nat (cedge s1 x) a t.
Proof.
  intros x a Ix Ia N (w & x' & _ & Qw & Sg).
  pose proof Ks as (_ & _ & _ & KC & KR' & _ & _ & S8 & S9 & _).
  assert (P : Pth s1 a t).
  { destruct (Nat.eq_dec w t) as [->|Nw]; [constructor; left; exists x'; exact (seg_old _ _ _ Sg)|].
    apply (t_trans _ _ a w t); constructor; [left; exists x'; exact (seg_old _ _ _ Sg)|].
    right; right. exists eW. auto. }
  pose proof (w_nodup False G0 sw s1 sA' K1 x) as ND.
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
End C4.

Section G3.
Variable p : prog.

(* the obligation with the three corners that need the programme's race-freedom *)
Definition NewKc3 : Prop := forall sW sw sA sw' sW' sA' s1,
  wch p False G0 sW sw sA -> wlink p False G0 sw sW sA sw' sW' sA' ->
  run p sA' -> rel sw' sW' sA' -> KR False G0 sw' sW' sA' ->
  UK sw sW sA -> WBCall sW -> UK sw' sW' sA' ->
  KGn sW sA -> KCn sW sA -> evok sA -> evok sW' -> (exists sAf, star p sA' sAf /\ done p sAf) ->
  step p sW s1 -> step p sA sA' -> rel sw s1 sA' -> KR False G0 sw s1 sA' ->
  s1 = sW' ->
  forall e eW, ent sA' (tm sA) = Some e -> ent s1 (tm sA) = Some eW ->
  (forall a, eQ e a -> a <> tm sA -> ~ eQ eW a -> ~ (exists w x, eQ eW w /\ seg (hs s1 x) w (Some a)) ->
     (CO1 sw sW (ec eW) eW a \/ CO2 sw sW (ec eW) eW a) -> ~ ~ Pth s1 a (tm sA)) /\
  (forall x a, In x (eC e) -> (eQ e a \/ eQc e a) -> In a (ids (hs sA' x)) -> a <> tm sA ->
     ~ ((eQ eW a \/ eQc eW a) /\ In a (ids (hs s1 x))) ->
     ~ (exists w, (eQ eW w \/ eQc eW w) /\ seg (hs s1 x) w (Some a)) ->
     (CO1 sw sW (ec eW) eW a \/ CO2 sw sW (ec eW) eW a \/ CO3 sW (ec eW) a) ->
     ~ ~ clos_trans nat (cedge s1 x) a (tm sA)).

Theorem NewKc_of_NewKc3 : NewKc3 -> NewKc p.
Proof.
  intros N3 sW sw sA sw' sW' sA' s1 Ch L RA' R' K' U0 WB U1 G C EVA EV' Fut St StA R1 K1 Hs1 e eW Ee EW.
  destruct (N3 sW sw sA sw' sW' sA' s1 Ch L RA' R' K' U0 WB U1 G C EVA EV' Fut St StA R1 K1 Hs1 e eW Ee EW) as [NG NC].
  assert (EV1 : evok s1).
  { rewrite Hs1. exact EV'. }
  destruct (k_ent False G0 sw s1 sA' K1 (tm sA) e Ee) as (eW' & E' & Ks). rewrite EW in E'. injection E' as <-.
  split; [exact NG|].
  intros x a Ix Q Ia N ND NS [Co|[Co|[Co|Co]]].
  - exact (NC x a Ix Q Ia N ND NS (or_introl Co)).
  - exact (NC x a Ix Q Ia N ND NS (or_intror (or_introl Co))).
  - exact (NC x a Ix Q Ia N ND NS (or_intror (or_intror Co))).
  - intros NP. apply NP. apply (co4_path p sw s1 sA' (tm sA) e eW RA' R1 K1 Ee EW Ks EV1 x a Ix); [|exact N|exact Co].
    destruct (in_ids_fl _ _ Ia) as [b Ib]. rewrite (r_hs sw s1 sA' R1 x) in Ib. apply in_hers in Ib.
    exact (in_ids_of _ _ _ (proj1 Ib)).
Qed.

Theorem drf_sc_WB_of_corners3 : wf p -> cellful p -> race_free_g p -> NewKc3 ->
  forall s, runWB p s -> done p s -> evok s ->
  exists l g, srun p l g /\ (forall c, sp g c = pcs s c) /\
    (forall c j, j < pcs s c -> sr g c j = rg (cs s c) j) /\ (forall x, sm g x = final s x).
Proof. intros W Wc RF N3. exact (drf_sc_WB_of_corners p W Wc RF (NewKc_of_NewKc3 N3)). Qed.
End G3.

Print Assumptions acc_cell.
Print Assumptions co4_path.
Print Assumptions drf_sc_WB_of_corners3.
