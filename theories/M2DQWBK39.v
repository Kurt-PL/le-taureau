(* Part 39: one instruction's effect, in the write-back state and in its A image,
   keeps the refined cover U with the published view as the only
   further term:
       P_A <= U(P_W u G_W),  A_A <= U(A_W u G_W),  R_A <= U(R_W u G_W),  G_A <= U(G_W)
   (effU), and what the context knows in order through guard() exactly (newOg_U), what it knows
   in order up to a double negation (newO_U: the filter of own stores at FLl asks whether a store
   is published, which is not decidable; every later use is a proof of a negation).
   Premises: the image's own stores are the state's, the state's own stores are in its P, a store
   the image knows that the state owns is owned by the image too (KWA), and an own written-back
   store of the context stands for a store its P holds, or that a store of another context in its
   P stands for (KWB).  The read part: what the image's read takes and what that conveys
   (KS, KC) is the state-level lemma of M2DQWBK40. *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB.
Require Import M2DQWBK1 M2DQWBK2 M2DQWBK3 M2DQWBK5 M2DQWBK6 M2DQWBK30 M2DQWBK38.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

Definition NN (V : view) : view := fun z => ~ ~ V z.

Lemma Ucomb : forall S X Y Z, vsub X (U S Y) -> vsub Y Z -> vsub X (U S Z).
Proof. intros S X Y Z H1 H2 z Hz. exact (U_mono S Y Z H2 z (H1 z Hz)). Qed.
Lemma vsub_or : forall A B Z, vsub A Z -> vsub B Z -> vsub (vor A B) Z.
Proof. intros A B Z H1 H2 z [Hz|Hz]; auto. Qed.
Lemma U_seg : forall S V x w z, V w -> seg (hs S x) w (Some z) -> U S V z.
Proof. intros S V x w z Vw Sg. right. exists w, x. auto. Qed.
Lemma NN_in : forall V z, V z -> NN V z.
Proof. intros V z H N. exact (N H). Qed.

Section EffU.
Variable S : st.
Variables (t : nat) (i : instr) (r : regs) (mw ma m' m'A : mst) (a : val) (K KA : view) (u uA : cell -> option nat) (w : bool).
Hypothesis HW : eff t i r mw m' a K u w.
Hypothesis HA : eff t i r ma m'A a KA uA w.
Hypothesis KP : vsub (mP ma) (U S (vor (mP mw) (mG mw))).
Hypothesis KA' : vsub (mA ma) (U S (vor (mA mw) (mG mw))).
Hypothesis KR : vsub (mR ma) (U S (vor (mR mw) (mG mw))).
Hypothesis KG : vsub (mG ma) (U S (mG mw)).
Hypothesis KW : vsub (mW ma) (mW mw).
Hypothesis KOW : vsub (mW mw) (mP mw).
Hypothesis KWd : forall z, mW mw z \/ ~ mW mw z.
Hypothesis KWA : forall z, (mP ma z \/ mA ma z) -> mW mw z -> mW ma z.
Hypothesis KWB : forall w0 x z, mW mw w0 -> seg (hs S x) w0 (Some z) ->
  mP mw z \/ exists w', mP mw w' /\ ~ mW mw w' /\ seg (hs S x) w' (Some z).
Hypothesis KS : vsub (srcs uA) (U S (srcs u)).
Hypothesis KC : vsub (carrieds ma uA) (U S (vor (carrieds mw u) (mG mw))).

(* FLs: what the image releases besides its own stores *)
Lemma fls_piece : vsub (fun z => (mP ma z \/ mA ma z) /\ ~ mW ma z)
  (U S (vor (fun z => mR mw z \/ ((mP mw z \/ mA mw z) /\ ~ mW mw z)) (mG mw))).
Proof.
  intros z (PA & NW).
  assert (Q : U S (vor (vor (mP mw) (mA mw)) (mG mw)) z).
  { destruct PA as [PA|PA].
    - apply (Ucomb S (mP ma) (vor (mP mw) (mG mw))); [exact KP| |exact PA]. intros y [Y|Y]; [left; left; exact Y|right; exact Y].
    - apply (Ucomb S (mA ma) (vor (mA mw) (mG mw))); [exact KA'| |exact PA]. intros y [Y|Y]; [left; right; exact Y|right; exact Y]. }
  destruct Q as [[PW|GW]|(w0 & x & [PW|GW] & Sg)].
  - destruct (KWd z) as [Wz|Wz]; [exfalso; exact (NW (KWA z PA Wz))|].
    left. left. right. split; [exact PW|exact Wz].
  - left. right. exact GW.
  - destruct (KWd w0) as [Ww|Ww].
    + destruct (KWB w0 x z Ww Sg) as [Pz|(w' & Pw' & Nw' & Sg')].
      * destruct (KWd z) as [Wz|Wz]; [exfalso; exact (NW (KWA z PA Wz))|].
        left. left. right. split; [left; exact Pz|exact Wz].
      * apply (U_seg S _ x w' z); [left; right; split; [left; exact Pw'|exact Nw']|exact Sg'].
    + apply (U_seg S _ x w0 z); [left; right; split; [exact PW|exact Ww]|exact Sg].
  - apply (U_seg S _ x w0 z); [right; exact GW|exact Sg].
Qed.

Lemma U_inv : forall V, vsub V (U S V). Proof. exact (U_in S). Qed.

Lemma fss_piece : vsub (fun z => mR ma z \/ mP ma z /\ mW ma z) (U S (vor (fun z => mR mw z \/ mP mw z /\ mW mw z) (mG mw))).
Proof.
  intros z [Z|[_ Z]].
  - apply (Ucomb S (mR ma) (vor (mR mw) (mG mw))); [exact KR| |exact Z]. intros y [Y|Y]; [left; left; exact Y|right; exact Y].
  - apply U_inv. left. right. split; [exact (KOW z (KW z Z))|exact (KW z Z)].
Qed.

Ltac sub_tac := intros z0 Z0; cbv [vor vone] in *; cbn [mP mA mR mG mW learn wput gpre gpost] in *; tauto.
Ltac piece :=
  first
  [ eapply (Ucomb S _ _ _ KP); sub_tac
  | eapply (Ucomb S _ _ _ KA'); sub_tac
  | eapply (Ucomb S _ _ _ KR); sub_tac
  | eapply (Ucomb S _ _ _ KG); sub_tac
  | eapply (Ucomb S _ _ _ KS); sub_tac
  | eapply (Ucomb S _ _ _ KC); sub_tac
  | eapply (Ucomb S _ _ _ (U_inv _)); sub_tac
  | eapply (Ucomb S _ _ _ (fun z Z => U_inv _ z (KW z Z))); sub_tac
  | eapply (Ucomb S _ _ _ fls_piece); sub_tac
  ].
Ltac pieces := first [exact fss_piece | repeat (apply vsub_or); piece].

Theorem effU : vsub (mP m'A) (U S (vor (mP m') (mG m'))) /\ vsub (mA m'A) (U S (vor (mA m') (mG m'))) /\
  vsub (mR m'A) (U S (vor (mR m') (mG m'))) /\ vsub (mG m'A) (U S (mG m')).
Proof.
  inversion HW; subst; inversion HA; subst; cbn [mP mA mR mG mW learn wput gpre gpost]; try discriminate; try congruence.
  all: repeat match goal with H : ?f _ = ?f _ |- _ => injection H; clear H; intros; subst end.
  all: try (exfalso; unfold icond, ieval in *; cbn in *; congruence).
  all: split; [|split; [|split]]; try pieces.
Qed.
End EffU.

Lemma newOg_U : forall S i m' m'A OgA OgW, vsub (mP m'A) (U S (vor (mP m') (mG m'))) -> vsub (mG m'A) (U S (mG m')) ->
  vsub OgA (U S OgW) -> (i = IFn FFull -> vsub (mG m') (mP m')) -> vsub (newOg i m'A OgA) (U S (newOg i m' OgW)).
Proof.
  intros S i m' m'A OgA OgW HP HG HO HF. destruct i as [| | |[]|]; cbn; auto.
  - apply vsub_or; [apply (Ucomb S _ _ _ HO); intros z Z; left; exact Z|apply (Ucomb S _ _ _ HG); intros z Z; right; exact Z].
  - apply (Ucomb S _ _ _ HP). intros z [Z|Z]; [exact Z|exact (HF eq_refl z Z)].
Qed.

Lemma NN_bind : forall (A B : view) z, NN A z -> (A z -> NN B z) -> NN B z.
Proof. intros A B z H F N. apply H. intros Az. exact (F Az N). Qed.
Lemma NN_sub : forall X Y Z, vsub X (NN Y) -> vsub Y Z -> vsub X (NN Z).
Proof. intros X Y Z H1 H2 z Hz. apply (NN_bind Y Z z (H1 z Hz)). intros Y'. apply NN_in. exact (H2 z Y'). Qed.

Section NewO.
Variables (S sW sA : st) (c : nat) (mw ma m' m'A : mst) (OW OA : view).
Hypothesis HO : vsub OA (NN (U S (vor OW (mG mw)))).
Hypothesis HP' : vsub (mP m'A) (U S (vor (mP m') (mG m'))).
Hypothesis HG' : vsub (mG m'A) (U S (mG m')).
Hypothesis HGG : vsub (mG mw) (mG m').
Hypothesis KP : vsub (mP ma) (U S (vor (mP mw) (mG mw))).
Hypothesis KA' : vsub (mA ma) (U S (vor (mA mw) (mG mw))).
Hypothesis KG : vsub (mG ma) (U S (mG mw)).
Hypothesis KWd : forall z, ownw sW c z \/ ~ ownw sW c z.
Hypothesis KWA : forall z, (mP ma z \/ mA ma z) -> ownw sW c z -> ownw sA c z.
Hypothesis KWB : forall w0 x z, ownw sW c w0 -> seg (hs S x) w0 (Some z) ->
  mP mw z \/ exists w', mP mw w' /\ ~ ownw sW c w' /\ seg (hs S x) w' (Some z).

Let OL := vor OW (fun w => (mP mw w \/ mA mw w) /\ ~ (ownw sW c w /\ ~ mG mw w)).

(* a store of P or A of the state that the image may add at FLl *)
Lemma fll_direct : forall z, (mP ma z \/ mA ma z) -> ~ (ownw sA c z /\ ~ mG ma z) -> (mP mw z \/ mA mw z) ->
  NN (U S (vor OL (mG m'))) z.
Proof.
  intros z PA NC PW N. destruct (KWd z) as [Wz|Wz].
  - apply NC. split; [exact (KWA z PA Wz)|]. intros Gz. apply N.
    apply (Ucomb S _ _ _ KG); [intros y Y; right; exact (HGG y Y)|exact Gz].
  - apply N. apply U_in. left. right. split; [exact PW|]. intros (Wz' & _). exact (Wz Wz').
Qed.

Lemma fll_piece : vsub (fun w => (mP ma w \/ mA ma w) /\ ~ (ownw sA c w /\ ~ mG ma w)) (NN (U S (vor OL (mG m')))).
Proof.
  intros z (PA & NC).
  assert (Q : U S (vor (vor (mP mw) (mA mw)) (mG mw)) z).
  { destruct PA as [PA|PA].
    - apply (Ucomb S (mP ma) (vor (mP mw) (mG mw))); [exact KP| |exact PA]. intros y [Y|Y]; [left; left; exact Y|right; exact Y].
    - apply (Ucomb S (mA ma) (vor (mA mw) (mG mw))); [exact KA'| |exact PA]. intros y [Y|Y]; [left; right; exact Y|right; exact Y]. }
  destruct Q as [[PW|GW]|(w0 & x & [PW|GW] & Sg)].
  - exact (fll_direct z PA NC PW).
  - apply NN_in. apply U_in. right. exact (HGG z GW).
  - destruct (KWd w0) as [Ww|Ww].
    + destruct (KWB w0 x z Ww Sg) as [Pz|(w' & Pw' & Nw' & Sg')].
      * exact (fll_direct z PA NC (or_introl Pz)).
      * apply NN_in. apply (U_seg S _ x w' z); [left; right; split; [left; exact Pw'|intros (Q & _); exact (Nw' Q)]|exact Sg'].
    + apply NN_in. apply (U_seg S _ x w0 z); [left; right; split; [exact PW|intros (Q & _); exact (Ww Q)]|exact Sg].
  - apply NN_in. apply (U_seg S _ x w0 z); [right; exact (HGG w0 GW)|exact Sg].
Qed.

Theorem newO_U : forall i, (i = IFn FFull -> vsub (mG m') (mP m')) ->
  vsub (newO sA c i ma m'A OA) (NN (U S (vor (newO sW c i mw m' OW) (mG m')))).
Proof.
  intros i HF. assert (HOx : vsub OA (NN (U S (vor OW (mG m'))))).
  { apply (NN_sub _ _ _ HO). apply U_mono. intros y [Y|Y]; [left; exact Y|right; exact (HGG y Y)]. }
  destruct i as [| | |[]|]; cbn; try exact HOx.
  - apply vsub_or; [apply (NN_sub _ _ _ HOx); apply U_mono; intros y [Y|Y]; [left; left; exact Y|right; exact Y]|].
    exact fll_piece.
  - apply vsub_or; [apply (NN_sub _ _ _ HOx); apply U_mono; intros y [Y|Y]; [left; left; exact Y|right; exact Y]|].
    intros z Z. apply NN_in. apply (Ucomb S _ _ _ HG'); [intros y Y; right; exact Y|exact Z].
  - intros z Z. apply NN_in. apply (Ucomb S _ _ _ HP'); [|exact Z]. intros y [Y|Y]; [left; exact Y|left; exact (HF eq_refl y Y)].
Qed.
End NewO.
