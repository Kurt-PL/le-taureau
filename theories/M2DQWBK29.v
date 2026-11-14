(* Part 29: an A run is its own image.  For a run of A (no write-back store anywhere),
   rel sw0 s s and KR False Good sw0 s s hold (self_image): the structural fields that concern only
   the write-back state (w_* and the invariants of rel) are taken from the image M2DQWBK13.runWBK gives
   through M2DQWB.Q_in_WB; the rest is reflexivity, hers being the identity on a history with no flag.
   Used to instantiate the premises of the KR lemmas (M2DQWBK26, M2DQWBK28) on litmus runs. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2WBRel M2WBReg M2DQWB M2DQWBK1 M2DQWBK3 M2DQWBK13.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBK1Q M2DQShim.

Lemma hers_noflag : forall h, (forall w b, In (w, b) h -> b = false) -> hers h = h.
Proof.
  induction h as [|[w b] h IH]; intros F; [reflexivity|].
  rewrite (F w b (or_introl eq_refl)). cbn. f_equal. apply IH. intros w' b' I. exact (F w' b' (or_intror I)).
Qed.

Lemma crel_self : forall c, crel sw0 c c.
Proof.
  intros c. split; [|split; [intros; reflexivity|]].
  - exists (rv c), (rw c), (vP c), (vA c), (vR c), (vO c), (vOg c). destruct c; reflexivity.
  - intros k x. unfold pi, sw0. destruct (rw c k x); reflexivity.
Qed.

Theorem self_image : forall p (Good : nat -> Prop) s, wf p -> run p s -> rel sw0 s s /\ KR False Good sw0 s s.
Proof.
  intros p Good s W R.
  destruct (runWBK p W False Good s (Q_in_WB p s R) (fun F => False_ind _ F) (fun F => False_ind _ F))
    as (sw & sA & RA & Rl & K).
  pose proof (runQ_flagsF p s R) as Fl.
  assert (Rs : rel sw0 s s).
  { constructor.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - intros c. apply crel_self.
    - intros x. symmetry. apply hers_noflag. intros w b I. exact (Fl x w b I).
    - intros x w _. split; reflexivity.
    - intros x w I. pose proof (Fl x w true I). discriminate.
    - exact (r_adj sw s sA Rl).
    - exact (i_ids sw s sA Rl).
    - exact (i_rw sw s sA Rl).
    - exact (i_oh sw s sA Rl).
    - intros w _. reflexivity. }
  split; [exact Rs|]. constructor; try (match goal with |- False -> _ => intros [] end).
  - reflexivity.
  - intros t eA E. exists eA. split; [exact E|].
    assert (EA : exists eA', ent sA t = Some eA').
    { destruct (ent sA t) as [eA'|] eqn:H; [eauto|]. exfalso. unfold ent in H, E.
      apply nth_error_None in H. rewrite (k_len False Good sw s sA K) in H.
      assert (Lt : t < length (lg s)) by (apply nth_error_Some; congruence). lia. }
    destruct EA as (eA' & EA). destruct (k_ent False Good sw s sA K t eA' EA) as (eW & EW & KS).
    rewrite E in EW. injection EW as <-. destruct KS as (_ & _ & _ & _ & _ & _ & _ & Hrf & _).
    repeat split; try reflexivity; auto.
    intros x. unfold pi, sw0. destruct (erf eA x); reflexivity.
  - intros x w I. pose proof (Fl x w true I). discriminate.
  - exact (w_nodup False Good sw s sA K).
  - exact (w_OW False Good sw s sA K).
  - exact (w_OGP False Good sw s sA K).
  - exact (w_OWG False Good sw s sA K).
  - intros c j t1 _ N. exfalso. apply N. reflexivity.
  - intros t f N. discriminate.
  - exact (w_tmo False Good sw s sA K).
Qed.

Print Assumptions self_image.
