(* Part 44: the write-back patch keeps UK.  The image is the same; the state gains the
   written-back store t in P of its context and in the histories of the CAS's cells, right after
   the write the CAS's load observed.  What t stands for in a cell is that write when it is kept,
   or what that written-back write stands for (seg_at_new); either way the context's P holds it
   or a store of another context in P stands for it (u_wbP, through u_rwP).  Every other
   stand-for pair is one of the state before (seg_del_t). *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB.
Require Import M2DQWBK1 M2DQWBK2 M2DQWBK3 M2DQWBK4 M2DQWBK15 M2DQWBK30 M2DQWBK38 M2DQWBK39 M2DQWBK40.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

(* removing a written-back store that is not the one standing keeps a stand-for pair *)
Lemma seg_del_t : forall h1 h2 t w z, seg (h1 ++ (t, true) :: h2) w (Some z) -> w <> t -> seg (h1 ++ h2) w (Some z).
Proof.
  intros h1 h2 t w z (A & B & C & E & Al) Nw.
  destruct (split3 h1 ((t, true) :: h2) A (B ++ (w, true) :: C) (z, false) E) as [(A2 & E1 & E2)|(A1 & E1 & E2)].
  - destruct (split3 A2 ((t, true) :: h2) B C (w, true) (eq_sym E2)) as [(A3 & E3 & E4)|(A3 & E3 & E4)].
    + exists A, B, (A3 ++ h2). split; [|exact Al]. rewrite E1, E3. repeat (rewrite <- app_assoc; simpl). reflexivity.
    + destruct A3 as [|e A3]; simpl in E4; [injection E4 as Et _; exfalso; exact (Nw (eq_sym Et))|].
      injection E4 as <- E4. exists A, (A2 ++ A3), C. split.
      * rewrite E1, E4. repeat (rewrite <- app_assoc; simpl). reflexivity.
      * rewrite E3 in Al. apply allt_app in Al. destruct Al as [Al1 Al2]. apply allt_app. split; [exact Al1|].
        inversion Al2. exact H2.
  - destruct A1 as [|e A1]; simpl in E2; [inversion E2|]. injection E2 as <- E2.
    exists (h1 ++ A1), B, C. split; [|exact Al]. rewrite E2. rewrite <- app_assoc. reflexivity.
Qed.

(* one occurrence: its place is fixed *)
Lemma uniq_place : forall X Y X' Y' (v : nat) (b b' : bool), ~ In v (ids X') -> ~ In v (ids Y') ->
  X ++ (v, b) :: Y = X' ++ (v, b') :: Y' -> X = X' /\ Y = Y'.
Proof.
  induction X as [|e X IH]; intros Y X' Y' v b b' N1 N2 E; destruct X' as [|e' X']; simpl in E.
  - injection E as _ ->. auto.
  - injection E as <- E. exfalso. apply N1. left. reflexivity.
  - injection E as -> E. exfalso. apply N2. rewrite <- E. rewrite ids_app. apply in_or_app. right. left. reflexivity.
  - injection E as <- E. assert (N1' : ~ In v (ids X')) by (intros I; apply N1; right; exact I).
    destruct (IH Y X' Y' v b b' N1' N2 E) as [-> ->]. auto.
Qed.

Lemma last_or_nil : forall {X} (l : list X), l = [] \/ exists l' a, l = l' ++ [a].
Proof.
  intros X l. destruct l as [|a l]; [left; reflexivity|right].
  destruct (exists_last (l := a :: l) ltac:(discriminate)) as (l' & b & E). exists l', b. exact E.
Qed.

(* what the new written-back store stands for *)
Lemma seg_at_new : forall h1 h2 t z (o : option nat),
  match o with None => h1 = [] | Some w1 => exists h0 g, h1 = h0 ++ [(w1, g)] end ->
  ~ In t (ids h1) -> ~ In t (ids h2) -> seg (h1 ++ (t, true) :: h2) t (Some z) ->
  exists w1, o = Some w1 /\ ((In (w1, false) (h1 ++ h2) /\ z = w1) \/ seg (h1 ++ h2) w1 (Some z)).
Proof.
  intros h1 h2 t z o Ho N1 N2 (A & B & C & E & Al).
  replace (A ++ (z, false) :: B ++ (t, true) :: C) with ((A ++ (z, false) :: B) ++ (t, true) :: C) in E
    by (rewrite <- app_assoc; reflexivity).
  destruct (uniq_place _ _ _ _ t true true N1 N2 (eq_sym E)) as [Eh1 ->].
  destruct o as [w1|].
  - exists w1. split; [reflexivity|]. destruct Ho as (h0 & g & Eh0). pose proof (eq_trans Eh1 Eh0) as Eh2.
    destruct (last_or_nil B) as [->|(B' & b0 & ->)].
    + left. apply app_inj_tail in Eh2. destruct Eh2 as [_ Ew]. injection Ew as Ez Eg.
      split; [|exact Ez]. rewrite <- Eh1. apply in_or_app. left. apply in_or_app. right. left. rewrite Ez. reflexivity.
    + right. replace (A ++ (z, false) :: B' ++ [b0]) with ((A ++ (z, false) :: B') ++ [b0]) in Eh2
        by (rewrite <- app_assoc; reflexivity).
      apply app_inj_tail in Eh2. destruct Eh2 as [_ Eb]. subst b0.
      apply allt_app in Al. destruct Al as [Al1 Al2]. pose proof (Forall_inv Al2) as Hg. cbn in Hg. subst g.
      exists A, B', h2. split; [|exact Al1]. rewrite <- Eh1. rewrite <- app_assoc. cbn. rewrite <- app_assoc. reflexivity.
  - exfalso. rewrite Ho in Eh1. destruct A; discriminate.
Qed.

Section WbU.
Variables (p : prog) (Fk : Prop) (Good : nat -> Prop) (sw : nat -> option (cell -> option nat)) (s sA : st) (c k t : nat) (H'' : cell -> hist).
Hypothesis RA : run p sA.
Hypothesis R : rel sw s sA.
Hypothesis K : KR Fk Good sw s sA.
Hypothesis KU : UK sw s sA.
Hypothesis Hfresh : forall x, ~ In t (ids (hs s x)).
Hypothesis Hok : wbok s c k t H''.
Hypothesis Hent : exists e, ent s t = Some e /\ ec e = c.

Local Abbreviation s' := (wbst s c k t H'').
Local Abbreviation sw' := (upd sw t (Some (fun x => pi sw x (rw (cs s c) k x)))).

Lemma Ugw : forall V, vsub (U s V) (U s' V).
Proof. intros V z [Z|(w0 & x & Vw & Sg)]; [left; exact Z|right; exists w0, x; split; [exact Vw|exact (seg_wbst s c k t H'' x w0 z Hok Sg)]]. Qed.

Lemma cs_wb2 : forall c', cs s' c' = if Nat.eqb c' c then
  mkC (oc (cs s c)) (rg (cs s c)) (ai (cs s c)) (upd (rw (cs s c)) k (wbrw (cs s c) k (icells (ai (cs s c) k)) t)) (rv (cs s c)) (bd (cs s c))
      (vor (vP (cs s c)) (vone t)) (vA (cs s c)) (vR (cs s c)) (vO (cs s c)) (vOg (cs s c)) (oh (cs s c)) (fx (cs s c))
  else cs s c'.
Proof. intros c'. reflexivity. Qed.

Lemma views_wb : forall c', vsub (vP (cs s c')) (vP (cs s' c')) /\ vA (cs s' c') = vA (cs s c') /\ vR (cs s' c') = vR (cs s c') /\
  vO (cs s' c') = vO (cs s c') /\ vOg (cs s' c') = vOg (cs s c').
Proof.
  intros c'. rewrite cs_wb2. destruct (Nat.eqb_spec c' c) as [->|N]; cbn [vP vA vR vO vOg]; [|repeat split; intros z Z; exact Z].
  repeat split. intros z Z. left. exact Z.
Qed.

Lemma ownw_wb2 : forall c' z, ownw s' c' z -> ownw s c' z \/ (z = t /\ c' = c).
Proof.
  intros c' z (e' & E' & Ec & Ew). cbn [lg wbst] in E'. rewrite nth_setew in E'.
  destruct (nth_error (lg s) z) as [e0|] eqn:E0; [|discriminate]. cbn in E'. injection E' as <-.
  unfold sete in Ec, Ew. destruct (Nat.eqb_spec (et e0) t) as [Et|Nt]; cbn [ec ew] in Ec, Ew.
  - right. destruct (i_etW p Fk Good sw s sA RA R K z e0 E0) as [Ez _]. rewrite Ez in Et. subst z. split; [reflexivity|].
    destruct Hent as (e & Ee & Ece). unfold ent in Ee. rewrite E0 in Ee. injection Ee as ->. congruence.
  - left. exists e0. auto.
Qed.

Lemma ownw_wb_old : forall c' z, z <> t -> ownw s' c' z -> ownw s c' z.
Proof. intros c' z N O. destruct (ownw_wb2 c' z O) as [O'|[E _]]; [exact O'|congruence]. Qed.

Lemma in_hs_t : forall x w0, In w0 (ids (hs s x)) -> w0 <> t.
Proof. intros x w0 I E. subst. exact (Hfresh x I). Qed.

Lemma seg_in_l : forall h w0 z, seg h w0 (Some z) -> In w0 (ids h).
Proof.
  intros h w0 z (h0 & h1 & h2 & E & _). rewrite E, ids_app. apply in_or_app. right. right.
  rewrite ids_app. apply in_or_app. right. left. reflexivity.
Qed.

Theorem UK_wb : UK sw' s' sA.
Proof.
  constructor.
  - intros z Z. apply Ugw. exact (u_G sw s sA KU z Z).
  - intros c0 z Z. apply Ugw. apply (Ucomb s _ _ _ (u_P sw s sA KU c0)); [|exact Z].
    intros y [Y|Y]; [left; exact (proj1 (views_wb c0) y Y)|right; exact Y].
  - intros c0. destruct (views_wb c0) as (_ & E & _). rewrite E. intros z Z. apply Ugw. exact (u_A sw s sA KU c0 z Z).
  - intros c0. destruct (views_wb c0) as (_ & _ & E & _). rewrite E. intros z Z. apply Ugw. exact (u_R sw s sA KU c0 z Z).
  - intros c0. destruct (views_wb c0) as (_ & _ & _ & E & _). rewrite E. apply (NN_sub _ _ _ (u_O sw s sA KU c0)). exact (Ugw _).
  - intros c0. destruct (views_wb c0) as (_ & _ & _ & _ & E). rewrite E. intros z Z. apply Ugw. exact (u_Og sw s sA KU c0 z Z).
  - intros y Sn. destruct (Nat.eq_dec y t) as [->|Ny]; [rewrite upd_eq in Sn; discriminate|]. rewrite upd_neq in Sn by exact Ny.
    cbn [wc wbst vG]. rewrite upd_neq by exact Ny. intros z Z. apply Ugw. exact (u_wc sw s sA KU y Sn z Z).
  - intros c0 x w0 z Ow Sg. cbn [hs wbst] in Sg.
    destruct (enters_tied_cell _ _ _ _ _ x Hok) as [Eh|(h1 & h2 & E1 & E2 & Fh & Mt)].
    + rewrite Eh in Sg. pose proof (in_hs_t x w0 (seg_in_l _ _ _ Sg)) as Nw.
      destruct (u_wbP sw s sA KU c0 x w0 z (ownw_wb_old c0 w0 Nw Ow) Sg) as [Z|(w' & P' & N' & S')].
      * left. exact (proj1 (views_wb c0) z Z).
      * right. exists w'. split; [exact (proj1 (views_wb c0) w' P')|]. split.
        -- intros O'. apply N'. exact (ownw_wb_old c0 w' (in_hs_t x w' (seg_in_l _ _ _ S')) O').
        -- exact (seg_wbst s c k t H'' x w' z Hok S').
    + rewrite E2 in Sg. destruct (Nat.eq_dec w0 t) as [->|Nw].
      * assert (Ec0 : c0 = c).
        { destruct (ownw_wb2 c0 t Ow) as [(e0 & E0 & Ec0 & _)|[_ Ec0]]; [|exact Ec0].
          destruct Hent as (e & Ee & Ece). unfold ent in Ee. rewrite E0 in Ee. injection Ee as ->. congruence. }
        subst c0.
        assert (N1 : ~ In t (ids h1)) by (intros I; apply (Hfresh x); rewrite E1, ids_app; apply in_or_app; left; exact I).
        assert (N2 : ~ In t (ids h2)) by (intros I; apply (Hfresh x); rewrite E1, ids_app; apply in_or_app; right; exact I).
        destruct (seg_at_new h1 h2 t z (rw (cs s c) k x) Mt N1 N2 Sg) as (w1 & Rw & [(Iw & ->)|Sg1]); rewrite <- E1 in *.
        -- left. exact (proj1 (views_wb c) w1 (u_rwP sw s sA KU c k x w1 Rw)).
        -- pose proof (u_rwP sw s sA KU c k x w1 Rw) as Pw1.
           assert (Nw1 : w1 <> t) by exact (in_hs_t x w1 (seg_in_l _ _ _ Sg1)).
           destruct (ownw_dec2 s c w1) as [Ow1|Nw1'].
           ++ destruct (u_wbP sw s sA KU c x w1 z Ow1 Sg1) as [Z|(w' & P' & N' & S')].
              ** left. exact (proj1 (views_wb c) z Z).
              ** right. exists w'. split; [exact (proj1 (views_wb c) w' P')|]. split.
                 --- intros O'. apply N'. exact (ownw_wb_old c w' (in_hs_t x w' (seg_in_l _ _ _ S')) O').
                 --- exact (seg_wbst s c k t H'' x w' z Hok S').
           ++ right. exists w1. split; [exact (proj1 (views_wb c) w1 Pw1)|]. split.
              ** intros O'. apply Nw1'. exact (ownw_wb_old c w1 Nw1 O').
              ** exact (seg_wbst s c k t H'' x w1 z Hok Sg1).
      * pose proof (seg_del_t h1 h2 t w0 z Sg Nw) as Sg0. rewrite <- E1 in Sg0.
        destruct (u_wbP sw s sA KU c0 x w0 z (ownw_wb_old c0 w0 Nw Ow) Sg0) as [Z|(w' & P' & N' & S')].
        -- left. exact (proj1 (views_wb c0) z Z).
        -- right. exists w'. split; [exact (proj1 (views_wb c0) w' P')|]. split.
           ++ intros O'. apply N'. exact (ownw_wb_old c0 w' (in_hs_t x w' (seg_in_l _ _ _ S')) O').
           ++ exact (seg_wbst s c k t H'' x w' z Hok S').
  - intros c0 k0 x w0 Rw. rewrite cs_wb2 in Rw |- *. destruct (Nat.eqb_spec c0 c) as [->|N]; cbn [rw vP] in *.
    + destruct (Nat.eqb_spec k0 k) as [->|Nk].
      * rewrite upd_eq in Rw. unfold wbrw in Rw. destruct (existsb (Nat.eqb x) (icells (ai (cs s c) k))).
        -- injection Rw as <-. right. reflexivity.
        -- left. exact (u_rwP sw s sA KU c k x w0 Rw).
      * left. apply (u_rwP sw s sA KU c k0 x w0). rewrite upd_neq in Rw by exact Nk. exact Rw.
    + exact (u_rwP sw s sA KU c0 k0 x w0 Rw).
Qed.
End WbU.

Print Assumptions UK_wb.
