(* Part 57: the next-guard() condition NF of an A run, and what a step keeps of it.
   NF s c: the context's next instruction is a guard() (for every register file), or the next
   instruction is a fenced access (fa) that is an access under the context's registers.  From
   either form every step of c up to its next guard() leaves vOg as it was and comes back to NF
   (an access at a fenced slot is followed by a guard()), and the guard() itself puts into vOg
   everything the context knows (P, A) and what guard() has published (G).
   OK s c a := vOg(c) a \/ NF s c.  OK_step: OK goes along every step for an item c knows (P, A)
   or that guard() has published (G). *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO.
Require Import M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB M2DQWBK1 M2DQWBK20 M2DQWBK32.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBQb M2DQWBK1Q M2DQShim.

Section NF.
Variable p : prog.
Hypothesis W : wf p.

Definition NF (s : st) (c : nat) : Prop :=
  (forall r, ins p c (pcs s c) r = IFn FFull) \/
  (fa p c (pcs s c) /\ isacc (ins p c (pcs s c) (rg (cs s c))) = true).

Definition OK (s : st) (c a : nat) : Prop := vOg (cs s c) a \/ NF s c.

(* the instruction at a slot depends only on the registers below it *)
Lemma ins_below : forall c k r r', (forall j, j < k -> r j = r' j) -> ins p c k r = ins p c k r'.
Proof. intros c k r r' H. exact (proj1 (W c k r r' H)). Qed.

(* NF depends only on the slot and the registers below it *)
Lemma NF_same : forall s s' c, pcs s' c = pcs s c -> (forall j, j < pcs s c -> rg (cs s' c) j = rg (cs s c) j) ->
  NF s c -> NF s' c.
Proof.
  intros s s' c Pc Rg [N1|(Fa & Ac)]; [left; rewrite Pc; exact N1|right].
  rewrite Pc. split; [exact Fa|]. rewrite (ins_below c (pcs s c) (rg (cs s' c)) (rg (cs s c)) Rg). exact Ac.
Qed.

(* after the fenced access, the guard() *)
Lemma NF_after : forall s s' c, fa p c (pcs s c) -> pcs s' c = S (pcs s c) -> NF s' c.
Proof. intros s s' c (_ & Fa) Pc. left. intros r. rewrite Pc. exact (proj2 (Fa r)). Qed.

(* the in-order guard() puts what the context knows and G into vOg *)
Lemma eff_full_P : forall t r m m' a K u w z, eff t (IFn FFull) r m m' a K u w ->
  (mP m z \/ mA m z \/ mG m z) -> mP m' z.
Proof.
  intros t r m m' a K u w z H Z. destruct (eff_full _ _ _ _ _ _ _ _ H) as [-> _]. cbn. unfold vor.
  destruct Z as [Z|[Z|Z]]; auto.
Qed.

(* vOg only grows *)
Lemma newOg_grow : forall t i r m m' a K u w Og, eff t i r m m' a K u w -> vsub Og (vor (mP m) (mG m)) ->
  vsub Og (newOg i m' Og).
Proof.
  intros t i r m m' a K u w Og H Sub z Z. destruct i as [| | |f|]; cbn [newOg]; try exact Z.
  destruct f; try exact Z; [left; exact Z|].
  destruct (eff_full _ _ _ _ _ _ _ _ H) as [-> _]. cbn. unfold vor. destruct (Sub z Z) as [Z1|Z1]; auto.
Qed.

Lemma find_seq_ge : forall (g : nat -> bool) a n k, find g (seq a n) = Some k -> a <= k.
Proof.
  intros g a n k F. apply find_some in F. destruct F as [I _]. apply in_seq in I. lia.
Qed.

Section Step.
Variables (s s' : st).
Hypothesis R : run p s.
Hypothesis St : step p s s'.

Let I := Inv1_run p s R.
Let Km := runWB_KM p s (Q_in_WB p s R).

(* OK goes along a step, for an item the context knows or G holds *)
Theorem OK_step : forall c a, OK s c a -> (vP (cs s c) a \/ vA (cs s c) a \/ vG s a) -> OK s' c a.
Proof.
  intros c0 a Ok Ka.
  assert (Sub : vsub (vOg (cs s c0)) (vor (mP (mof s c0)) (mG (mof s c0)))) by (intros z Z; exact (proj2 (Km c0) z Z)).
  destruct (stepQ_split_rg p s s' St) as [[HA _]|[RF Rb]]; [|destruct Ok as [O|N]; [left; rewrite (rfx_vOg _ _ RF); exact O|right; exact (NF_same s s' c0 (f_equal (fun f => f c0) (rfx_pcs _ _ RF)) (Rb c0) N)]].
  destruct (step_cases p s s' HA) as
    [(c & i & m' & a0 & K & u & w & Hi & Hoc & _ & _ & _ & Hh & _ & _ & He & _ & ->)
    |[(c & k & d & B & m' & a0 & K & u & w & L1 & Hoc & _ & Hd & _ & _ & He & _ & ->)
    |[(c & d & H1 & H2 & H3 & _ & _ & _ & ->)
    |[(c & k & xs & B & m' & a0 & K & u & w & bv & L1 & Hoc & Hoh & _ & _ & He & _ & ->)
    |[(c & S1 & S2 & _ & _ & _ & _ & _ & ->)
    |(cX & jX & bX & BX & oX & HjX & HfX & HcX & ->)]]]]].
  - (* in order *)
    unfold sord, evs, OK, NF in *; cbn [cs pcs vOg rg] in *.
    destruct (Nat.eqb_spec c0 c) as [->|N]; [|unfold NF in *; cbn [cs pcs vOg rg] in *; rewrite !upd_neq by exact N; exact Ok].
    rewrite !upd_eq. cbn [vOg rg].
    destruct Ok as [Og|[N1|(Fa & Ac)]].
    + left. exact (newOg_grow _ _ _ _ _ _ _ _ _ _ He Sub a Og).
    + left. rewrite (N1 (rg (cs s c))) in Hi. subst i. cbn [newOg].
      apply (eff_full_P _ _ _ _ _ _ _ _ _ He). cbn [mof mP mA mG]. destruct Ka as [Z|[Z|Z]]; auto.
    + right. left. intros r. try rewrite upd_eq. exact (proj2 ((proj2 Fa) r)).
  - (* early *)
    unfold searly, set_es, searly0, evs, OK in *; cbn [cs pcs vOg rg] in *.
    destruct (Nat.eqb_spec c0 c) as [->|N]; [|unfold NF in *; cbn [cs pcs vOg rg] in *; rewrite !upd_neq by exact N; exact Ok].
    rewrite !upd_eq. cbn [vOg rg].
    destruct Ok as [Og|Nf]; [left; exact (newOg_grow _ _ _ _ _ _ _ _ _ _ He Sub a Og)|right].
    apply (NF_same s); [cbn [pcs]; reflexivity| |exact Nf].
    intros j Lj. cbn [cs]. rewrite upd_eq. cbn [rg]. rewrite upd_neq by lia. reflexivity.
  - (* the context reaches an access that happened early *)
    unfold smatch, OK, NF in *; cbn [cs pcs vOg rg] in *.
    destruct (Nat.eqb_spec c0 c) as [->|N]; [|unfold NF in *; cbn [cs pcs vOg rg] in *; rewrite !upd_neq by exact N; exact Ok].
    rewrite !upd_eq. cbn [vOg rg].
    destruct Ok as [Og|[N1|(Fa & _)]]; [left; exact Og| |].
    + exfalso. exact (eof_notFF _ _ _ H3 (N1 _)).
    + right. left. intros r. try rewrite upd_eq. exact (proj2 ((proj2 Fa) r)).
  - (* a CAS's read alone *)
    unfold sread, OK in *; cbn [cs pcs vOg rg] in *.
    destruct (Nat.eqb_spec c0 c) as [->|N]; [|unfold NF in *; cbn [cs pcs vOg rg] in *; rewrite !upd_neq by exact N; exact Ok].
    rewrite !upd_eq. cbn [vOg rg newOg].
    destruct Ok as [Og|Nf]; [left; exact Og|right].
    apply (NF_same s); [cbn [pcs]; reflexivity| |exact Nf].
    intros j Lj. cbn [cs]. rewrite upd_eq. cbn [rg]. rewrite upd_neq by lia. reflexivity.
  - (* passing an instruction that does not execute *)
    unfold sskip, OK, NF in *; cbn [cs pcs vOg rg] in *.
    destruct (Nat.eqb_spec c0 c) as [->|N]; [|unfold NF in *; cbn [cs pcs vOg rg] in *; rewrite !upd_neq by exact N; exact Ok].
    rewrite !upd_eq. cbn [vOg rg].
    destruct Ok as [Og|[N1|(Fa & _)]]; [left; exact Og| |].
    + exfalso. rewrite (N1 _) in S1. rewrite xex_guard in S1. discriminate.
    + right. left. intros r. try rewrite upd_eq. exact (proj2 ((proj2 Fa) r)).
  - (* a result fixed *)
    unfold OK in *. unfold scfix0. cbn [cs pcs vOg rg].
    destruct (Nat.eqb_spec c0 cX) as [->|N].
    + rewrite upd_eq. cbn [vOg rg]. rewrite (vOg_flp s cX oX bX).
      destruct Ok as [Og|Nf]; [left; exact Og|right].
      apply (NF_same s); [unfold scfix0; cbn [pcs]; rewrite (pcs_flp s cX oX bX); reflexivity| |exact Nf].
      intros j Lj. unfold scfix0. cbn [cs]. rewrite upd_eq. cbn [rg].
      destruct (rg_flp s cX oX bX cX j) as [E|(_ & Eo & _)]; [exact E|exfalso].
      destruct HcX as (v & Hv). destruct (Hv (fun _ _ => 0)) as (_ & _ & _ & Hh & _).
      rewrite Eo in Hh. unfold hpend_at in Hh. apply find_seq_ge in Hh. lia.
    + rewrite upd_neq by exact N. rewrite (vOg_flp s cX oX bX).
      destruct Ok as [Og|Nf]; [left; exact Og|right].
      apply (NF_same s); [unfold scfix0; cbn [pcs]; rewrite (pcs_flp s cX oX bX); reflexivity| |exact Nf].
      intros j Lj. unfold scfix0. cbn [cs]. rewrite upd_neq by exact N.
      destruct (rg_flp s cX oX bX c0 j) as [E|(Ec & _)]; [exact E|congruence].
Qed.
End Step.
End NF.

Print Assumptions OK_step.
