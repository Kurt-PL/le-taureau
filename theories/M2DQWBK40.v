(* Part 40: KR2's U part (UK), and what a read of the image takes.
   UK sw sW sA: the image's views are within U of the state's views and what guard() has
   published in the state (vG); what it knows in order through guard() exactly; what it knows in
   order up to a double negation (M2DQWBK39); what a kept store conveys in the image within U of
   what it conveys in the state and vG; and two facts of the state alone: an own written-back
   store stands for a store P holds or that a store of another context in P stands for (u_wbP),
   and the write a slot read or made is in P (u_rwP).
   WBCall s: every kept store that a written-back store stands for conveys only itself, what
   the written-back store conveys, and vG (the (WBC'') of M2DQWBK37.WBC, for all write-backs).
   srcsU / carrU: under WBCall, what the image's read takes, and what that conveys, is within U
   of what the state's read takes (and conveys, and vG). *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB.
Require Import M2DQWBK1 M2DQWBK2 M2DQWBK3 M2DQWBK5 M2DQWBK6 M2DQWBK15 M2DQWBK30 M2DQWBK38 M2DQWBK39.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

Definition WBCall (s : st) : Prop :=
  forall x w z, seg (hs s x) w (Some z) -> forall y, wc s z y -> y = z \/ wc s w y \/ vG s y.

Record UK (sw : nat -> option (cell -> option nat)) (sW sA : st) : Prop := {
  u_G : vsub (vG sA) (U sW (vG sW));
  u_P : forall c, vsub (vP (cs sA c)) (U sW (vor (vP (cs sW c)) (vG sW)));
  u_A : forall c, vsub (vA (cs sA c)) (U sW (vor (vA (cs sW c)) (vG sW)));
  u_R : forall c, vsub (vR (cs sA c)) (U sW (vor (vR (cs sW c)) (vG sW)));
  u_O : forall c, vsub (vO (cs sA c)) (NN (U sW (vor (vO (cs sW c)) (vG sW))));
  u_Og : forall c, vsub (vOg (cs sA c)) (U sW (vOg (cs sW c)));
  u_wc : forall y, sw y = None -> vsub (wc sA y) (U sW (vor (wc sW y) (vG sW)));
  u_wbP : forall c x w z, ownw sW c w -> seg (hs sW x) w (Some z) ->
    vP (cs sW c) z \/ exists w', vP (cs sW c) w' /\ ~ ownw sW c w' /\ seg (hs sW x) w' (Some z);
  u_rwP : forall c k x w0, rw (cs sW c) k x = Some w0 -> vP (cs sW c) w0
}.

Lemma ownw_dec2 : forall s c z, ownw s c z \/ ~ ownw s c z.
Proof.
  intros s c z. destruct (nth_error (lg s) z) as [e|] eqn:E; unfold ownw.
  - destruct (Nat.eq_dec (ec e) c) as [Ec|Nc]; destruct (ew e) eqn:W.
    + left. exists e. auto.
    + right. intros (e' & E' & _ & W'). rewrite E in E'. injection E' as <-. congruence.
    + right. intros (e' & E' & C' & _). rewrite E in E'. injection E' as <-. congruence.
    + right. intros (e' & E' & C' & _). rewrite E in E'. injection E' as <-. congruence.
  - right. intros (e' & E' & _). congruence.
Qed.

Lemma wrote_srcv : forall t xs u w x w0, wrote t xs u w x = Some w0 -> srcv u w t w0.
Proof.
  intros t xs u w x w0 E. unfold wrote, srcv in *. destruct w.
  - destruct (existsb (Nat.eqb x) xs); [injection E as <-; right; reflexivity|discriminate].
  - left. exists x. exact E.
Qed.

Lemma UK_init : UK sw0 sinit sinit.
Proof.
  constructor; cbn; intros.
  all: try (intros z Z; contradiction).
  - destruct H0 as (h0 & h1 & h2 & E & _). destruct h0; discriminate.
  - congruence.
Qed.

Lemma WBCall_init : WBCall sinit.
Proof. intros x w z (h0 & h1 & h2 & E & _). destruct h0; discriminate. Qed.

(* a kept store, inserted before nothing written-back, is not inside a stand-for pair *)
Lemma seg_del_f : forall h1 h2 t w z, seg (h1 ++ (t, false) :: h2) w (Some z) -> free_head h2 ->
  ~ In t (ids (h1 ++ h2)) -> seg (h1 ++ h2) w (Some z).
Proof.
  intros h1 h2 t w z (A & B & C & E & Al) F Nt.
  destruct (split3 h1 ((t, false) :: h2) A (B ++ (w, true) :: C) (z, false) E) as [(A2 & E1 & E2)|(A1 & E1 & E2)].
  - (* z is in h1 *)
    destruct (split3 A2 ((t, false) :: h2) B C (w, true) (eq_sym E2)) as [(A3 & E3 & E4)|(A3 & E3 & E4)].
    + exists A, B, (A3 ++ h2). split; [|exact Al]. rewrite E1, E3. repeat (rewrite <- app_assoc; simpl). reflexivity.
    + exfalso. destruct A3 as [|[y b] A3].
      * simpl in E4. inversion E4.
      * simpl in E4. inversion E4; subst. try (rewrite E3 in Al). apply allt_app in Al. destruct Al as [_ Al].
        pose proof (Forall_inv Al) as Hy. cbn in Hy. discriminate.
  - destruct A1 as [|[y b] A1].
    + (* z is t *)
      simpl in E2. inversion E2; subst. exfalso. destruct B as [|[y b] B].
      * simpl in F. pose proof (F w true C eq_refl). discriminate.
      * simpl in F. pose proof (F y b _ eq_refl) as Fb. subst b.
        pose proof (Forall_inv Al) as Hy. cbn in Hy. discriminate.
    + simpl in E2. inversion E2; subst. exists (h1 ++ A1), B, C. split; [|exact Al].
      rewrite <- app_assoc. reflexivity.
Qed.

Section Rd.
Variables (Fk : Prop) (Good : nat -> Prop) (sw : nat -> option (cell -> option nat)) (sW sA : st).
Hypothesis Rl : rel sw sW sA.
Hypothesis K : KR Fk Good sw sW sA.
Hypothesis KU : UK sw sW sA.
Hypothesis WB : WBCall sW.
Variables (u uA : cell -> option nat).
Hypothesis Hu : forall x, uA x = pi sw x (u x).
Hypothesis Hk : forall x w', u x = Some w' -> In w' (ids (hs sW x)).

(* what the image's read took in a cell: the state's write, or the kept store it stands for *)
Lemma took_cases : forall x y, uA x = Some y ->
  exists w0, u x = Some w0 /\ ((y = w0 /\ sw w0 = None) \/ seg (hs sW x) w0 (Some y)).
Proof.
  intros x y E. rewrite Hu in E. destruct (u x) as [w0|] eqn:Eu; [|discriminate]. exists w0. split; [reflexivity|].
  unfold pi in E. destruct (sw w0) as [f|] eqn:Sw.
  - right. destruct (in_ids_fl _ _ (Hk x w0 Eu)) as [[|] I].
    + destruct (w_bet Fk Good sw sW sA K x w0 I) as (f' & Sf & Sg). rewrite Sw in Sf. injection Sf as <-. rewrite E in Sg. exact Sg.
    + destruct (r_kept sw sW sA Rl x w0 I) as [Sn _]. congruence.
  - left. injection E as <-. auto.
Qed.

Lemma srcsU : vsub (srcs uA) (U sW (srcs u)).
Proof.
  intros y (x & E). destruct (took_cases x y E) as (w0 & Eu & [(-> & _)|Sg]).
  - left. exists x. exact Eu.
  - apply (U_seg sW _ x w0 y); [exists x; exact Eu|exact Sg].
Qed.

(* a kept store is not written back anywhere *)
Lemma kept_not_wb : forall x x' y v, In (y, false) (hs sW x) -> ~ seg (hs sW x') y (Some v).
Proof.
  intros x x' y v I (h0 & h1 & h2 & E & _).
  assert (I' : In (y, true) (hs sW x')) by (rewrite E; apply in_or_app; right; right; apply in_or_app; right; left; reflexivity).
  destruct (w_bet Fk Good sw sW sA K x' y I') as (f & Sf & _). destruct (r_kept sw sW sA Rl x y I) as [Sn _]. congruence.
Qed.

Lemma carrU : forall c, vsub (carrieds (mof sA c) uA) (U sW (vor (carrieds (mof sW c) u) (vG sW))).
Proof.
  intros c v (x & y & Ey & Hv). destruct (took_cases x y Ey) as (w0 & Eu & [(-> & Sn)|Sg]).
  - destruct Hv as [Hv| ->].
    + cbn [mC mof] in Hv. apply (Ucomb sW _ _ _ (u_wc sw sW sA KU w0 Sn)); [|exact Hv].
      intros z [Z|Z]; [left; exists x, w0; split; [exact Eu|left; exact Z]|right; exact Z].
    + left. left. eexists x, _. split; [exact Eu|right; reflexivity].
  - assert (Cw : carrieds (mof sW c) u w0) by (exists x, w0; split; [exact Eu|right; reflexivity]).
    destruct Hv as [Hv| ->]; [|apply (U_seg sW _ x w0 y); [left; exact Cw|exact Sg]].
    cbn [mC mof] in Hv. pose proof (stands_kept _ _ _ Sg) as Ky.
    destruct (r_kept sw sW sA Rl x y Ky) as [Sn _].
    destruct (u_wc sw sW sA KU y Sn v Hv) as [[Z|Z]|(w'' & x'' & [Z|Z] & Sg'')].
    + destruct (WB x w0 y Sg v Z) as [Ev|[Z'|Z']].
      * rewrite Ev. apply (U_seg sW _ x w0 y); [left; exact Cw|exact Sg].
      * left. left. exists x, w0. split; [exact Eu|left; exact Z'].
      * left. right. exact Z'.
    + left. right. exact Z.
    + destruct (WB x w0 y Sg w'' Z) as [->|[Z'|Z']].
      * exfalso. exact (kept_not_wb x x'' y v Ky Sg'').
      * apply (U_seg sW _ x'' w'' v); [left; exists x, w0; split; [exact Eu|left; exact Z']|exact Sg''].
      * apply (U_seg sW _ x'' w'' v); [right; exact Z'|exact Sg''].
    + apply (U_seg sW _ x'' w'' v); [right; exact Z|exact Sg''].
Qed.
End Rd.
