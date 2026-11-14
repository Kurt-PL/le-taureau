(* Every CAS happens in two parts, and instances of M2DQ's definitions at
   real reachable states (positive and negative).
     CAS1: CAS(x, 0, 5)
   - cas_in_parts: in M2DQ a CAS slot happens (oc) only after its load part
     happened alone (oh): a CAS always happens as a load part and then a store
     part, never as a whole.
   - sfix_ok / q_sfix: positive at CAS1 after its load part (the claim is
     place 0, read 0 = expected 0); negative at the initial state (no load
     part happened).
   Concrete facts are deciders closed by vm_compute; reflexivity, used
   through the soundness lemmas below. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Cont M2Lit M2Ev M2EvLit M2Oota M2CasSplitProof
  M2DA M2DAInst M2DP M2DQ M2DQInv M2DQIface.

(* ---------- every CAS happens in two parts ---------- *)
Theorem cas_in_parts : forall p s t c k, stepQ p s t -> oc (cs s c) k = None -> oc (cs t c) k <> None ->
  is_cas (ai (cs t c) k) = true -> oh (cs s c) k <> None.
Proof.
  intros p s t c k S O O' C. destruct S as [s t _ V|s c0 k0 B _ _|s c0 j0 k0 B _ _ _].
  - exact (V c k O O' C).
  - exfalso. apply O'. rewrite oc_bd, oc_cf. exact O.
  - exfalso. apply O'. rewrite oc_cx. exact O.
Qed.

(* ---------- runs built forward ---------- *)
Lemma startQ : forall p (Q : M2Model.st -> Prop), (exists t, starQ p sinit t /\ Q t) -> exists t, runQ p t /\ Q t.
Proof. intros p Q (t & H & Qt). exists t. split; [apply (starQ_run p sinit t); [constructor|exact H]|exact Qt]. Qed.
Lemma fwdQ : forall p s s1 (Q : M2Model.st -> Prop), step p s s1 -> nowhole s s1 -> (exists t, starQ p s1 t /\ Q t) ->
  exists t, starQ p s t /\ Q t.
Proof. intros p s s1 Q S V (t & H & Qt). exists t. split; [eapply sqS; [apply q_old; eauto|exact H]|exact Qt]. Qed.

Definition oNone {A} (o : option A) : bool := match o with None => true | Some _ => false end.

(* ---------- sfix_ok ---------- *)
(* "one value under every valuation": at a place held by a happened load part
   (record k) the register's payload is the record's, whatever the free values *)
Lemma hpend_one_value : forall p c cc pc N B f j k, wf p -> pend_ok cc pc -> pc <= j ->
  let r := creg p c cc pc N B f in
  is_cas (ins p c j r) && icond (ins p c j r) r = true -> pend_at p c cc pc N r j = None ->
  hpend_at p c cc pc N r j = Some k -> vv (r j) = vv (rg cc k).
Proof.
  intros p c cc pc N B f j k W PO L r X Pn Hp. unfold r. rewrite (creg_fix p W c cc pc N B f j PO). fold r.
  unfold slotv. destruct (Nat.ltb_spec j pc) as [Lt|_]; [lia|]. cbv zeta.
  assert (Ld : is_load (ins p c j r) && icond (ins p c j r) r = true).
  { apply andb_prop in X as [Ci Co]. rewrite Co, andb_true_r. destruct (ins p c j r); try discriminate; reflexivity. }
  rewrite Ld, Pn, Hp, cfx_unfold.
  destruct (fx cc j) as [b|]; [destruct (is_cas (ins p c j r))|];
    destruct (vok (rg cc k)); rewrite ?vv_vd; reflexivity.
Qed.

(* so sfix_ok's claims all carry the record's value: one value under every valuation *)
Lemma sfix_one_value : forall p s c j k B, wf p -> Inv1 p s -> sfix_ok p c (cs s c) (pcs s c) (tp s c) j k B ->
  forall f, exists jf, let r := creg p c (cs s c) (pcs s c) (tp s c) (bor (bd (cs s c)) B) f in
    hpend_at p c (cs s c) (pcs s c) (tp s c) r jf = Some k /\ vv (r jf) = vv (rg (cs s c) k).
Proof.
  intros p s c j k B W I (_ & _ & _ & H) f. destruct (H f) as (jf & L & Hp & Pn & Ci & Co & _).
  exists jf. cbv zeta in *. split; [exact Hp|].
  apply (hpend_one_value p c _ _ _ _ f jf k W (pend_ok_of p s c I) L); [rewrite Ci, Co; reflexivity|exact Pn|exact Hp].
Qed.

Definition sfix_dec (p : prog) (c : nat) (cc : cst) (pc N j k : nat) (B : nat -> bool) (jf : nat)
    (f : nat -> cell -> val) : bool :=
  let r := creg p c cc pc N (bor (bd cc) B) f in
  oNone (oc cc k) && negb (oNone (oh cc k)) && vok (rg cc k) && Nat.leb pc jf &&
  match hpend_at p c cc pc N r jf with Some k' => Nat.eqb k' k | None => false end &&
  oNone (pend_at p c cc pc N r jf) && is_cas (ins p c jf r) && icond (ins p c jf r) r &&
  Nat.eqb (vv (rg cc k)) (cexp (ins p c jf r) r) &&
  match fx cc jf with Some false => false | _ => true end &&
  (Nat.eqb jf j || negb (is_cas (ins p c j r) && icond (ins p c j r) r)).

Lemma sfix_dec_sound : forall p c cc pc N j k B jf, wf p -> pend_ok cc pc ->
  (forall f, sfix_dec p c cc pc N j k B jf f = true) -> sfix_ok p c cc pc N j k B.
Proof.
  intros p c cc pc N j k B jf W PO H.
  assert (G : forall f, let r := creg p c cc pc N (bor (bd cc) B) f in
    oc cc k = None /\ oh cc k <> None /\ vok (rg cc k) = true /\ pc <= jf /\ hpend_at p c cc pc N r jf = Some k /\
    pend_at p c cc pc N r jf = None /\ is_cas (ins p c jf r) = true /\ icond (ins p c jf r) r = true /\
    vv (rg cc k) = cexp (ins p c jf r) r /\ fx cc jf <> Some false /\
    (jf = j \/ is_cas (ins p c j r) && icond (ins p c j r) r = false)).
  { intros f r. specialize (H f). unfold sfix_dec in H. fold r in H.
    repeat (apply andb_prop in H as [H ?]).
    repeat match goal with Hb : _ = true |- _ => revert Hb end. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11.
    split; [destruct (oc cc k); [discriminate|reflexivity]|].
    split; [destruct (oh cc k); [discriminate|discriminate]|].
    split; [exact A3|]. split; [apply Nat.leb_le; exact A4|].
    split; [destruct (hpend_at p c cc pc N r jf) as [k'|]; [apply Nat.eqb_eq in A5; congruence|discriminate]|].
    split; [destruct (pend_at p c cc pc N r jf); [discriminate|reflexivity]|].
    split; [exact A7|]. split; [exact A8|]. split; [apply Nat.eqb_eq; exact A9|].
    split; [destruct (fx cc jf) as [[]|]; [discriminate|discriminate|discriminate]|].
    apply orb_prop in A11 as [E|E]; [left; apply Nat.eqb_eq; exact E|right; apply negb_true_iff; exact E]. }
  destruct (G (fun _ _ => 0)) as (O & Oh & V & _).
  split; [exact O|split; [exact Oh|split; [exact V|]]].
  intros f. destruct (G f) as (_ & _ & _ & L & Hp & Pn & Ci & Co & Ev & Fx & Ej). exists jf. cbv zeta in *.
  rewrite (hpend_one_value p c cc pc N _ f jf k W PO L) by (rewrite ?Ci, ?Co; auto). auto 10.
Qed.

(* positive: CAS1 after its load part is read alone *)
Theorem sfix_pos_CAS1 : exists s1, step CAS1 sinit s1 /\ nowhole sinit s1 /\
  Nat.eqb (pcs s1 0) 0 = true /\ oNone (fx (cs s1 0) 0) = true /\
  (forall f, sfix_dec CAS1 0 (cs s1 0) (pcs s1 0) (tp s1 0) 0 0 (fun _ => false) 0 f = true).
Proof.
  eexists. split; [cread 0 0 [0] 0; LD (@None nat); vis_none|]. split.
  - apply nowhole_oc. intros c k. cbn [cs]. unfold upd. destruct (Nat.eqb c 0); reflexivity.
  - split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. intros f. vm_compute. reflexivity.
Qed.

Corollary sfix_step_CAS1 : exists s1, runQ CAS1 s1 /\
  sfix_ok CAS1 0 (cs s1 0) (pcs s1 0) (tp s1 0) 0 0 (fun _ => false) /\
  runQ CAS1 (scfix0 s1 0 0 true (fun _ => false)).
Proof.
  destruct sfix_pos_CAS1 as (s1 & S & V & P & F & D).
  assert (R : runQ CAS1 s1) by (eapply xS; [constructor|apply q_old; assumption]).
  assert (W : wf CAS1) by (apply wf_stat; intros c k r r' _; destruct c as [|c]; [destruct k as [|[|k]]|destruct c; destruct k]; reflexivity).
  assert (Ok := sfix_dec_sound _ _ _ _ _ _ _ _ _ W (pend_ok_of _ _ 0 (M2DQIface.s1 _ _ (IS_run _ _ R))) D).
  exists s1. split; [exact R|split; [exact Ok|]].
  eapply xS; [exact R|]. apply (q_sfix CAS1 s1 0 0 0 (fun _ => false)); [apply Nat.eqb_eq in P; lia| |exact Ok].
  destruct (fx (cs s1 0) 0); [discriminate|reflexivity].
Qed.

(* negative: no success is counted on before a load part happened *)
Theorem sfix_neg_init : forall p c j k B, ~ sfix_ok p c (cs sinit c) (pcs sinit c) (tp sinit c) j k B.
Proof. intros p c j k B (_ & Hh & _). apply Hh. reflexivity. Qed.


Print Assumptions cas_in_parts.
Print Assumptions sfix_step_CAS1.
Print Assumptions sfix_one_value.
