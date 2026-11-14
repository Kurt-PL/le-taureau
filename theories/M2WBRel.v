(* Write-back (spec 0.1 §8.6), part 2: the relation between a state with write-backs (sW) and
   the A state with the load alone (sA), and what the write-back patch does to it.

   A write-back store is an entry (t, true) of its cells' histories (the flag of a store tied to
   the write its load observed); every other entry has the flag false.  hers drops the flagged
   entries.  sw t says, per cell, which write the entry t stands for in A (the write its
   load observed, resolved through earlier write-backs). *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2WBReg.

Definition hers (h : hist) : hist := filter (fun e => negb (snd e)) h.

Lemma hers_app : forall a b, hers (a ++ b) = hers a ++ hers b.
Proof. intros. unfold hers. apply filter_app. Qed.
Lemma hers_f : forall w h, hers ((w, false) :: h) = (w, false) :: hers h.
Proof. reflexivity. Qed.
Lemma hers_t : forall w h, hers ((w, true) :: h) = hers h.
Proof. reflexivity. Qed.
Lemma hers_ins_f : forall h1 h2 t, hers (h1 ++ (t, false) :: h2) = hers h1 ++ (t, false) :: hers h2.
Proof. intros. rewrite hers_app, hers_f. reflexivity. Qed.
Lemma hers_ins_t : forall h1 h2 t, hers (h1 ++ (t, true) :: h2) = hers h1 ++ hers h2.
Proof. intros. rewrite hers_app, hers_t. reflexivity. Qed.

Lemma in_hers : forall h e, In e (hers h) <-> In e h /\ snd e = false.
Proof.
  intros h e. unfold hers. rewrite filter_In. split; intros [A B]; split; auto; [apply negb_true_iff in B|apply negb_true_iff]; auto.
Qed.
Lemma in_ids_hers : forall h w, In w (ids (hers h)) -> In w (ids h).
Proof.
  intros h w. unfold ids. rewrite !in_map_iff. intros (e & E & I). apply in_hers in I. exists e. tauto.
Qed.

(* the value of the write a read took *)
Definition rdv (V : nat -> cell -> val) (o : option nat) (x : cell) : val := match o with None => 0 | Some w => V w x end.
Lemma rdval_rdv : forall s c u x, rdval (mof s c) u x = rdv (wv s) (u x) x.
Proof. intros. reflexivity. Qed.

(* the write in A a read of the write-back store w, in cell x, stands for *)
Definition pi (sw : nat -> option (cell -> option nat)) (x : cell) (o : option nat) : option nat :=
  match o with None => None | Some w => match sw w with None => Some w | Some f => f x end end.

(* a flagged entry has the value of the entry before it (0 at the head) *)
Fixpoint hadj (V : nat -> val) (lv : val) (h : hist) : Prop :=
  match h with [] => True | (w, b) :: h' => (b = true -> V w = lv) /\ hadj V (V w) h' end.
Fixpoint lastv (V : nat -> val) (lv : val) (h : hist) : val :=
  match h with [] => lv | (w, _) :: h' => lastv V (V w) h' end.

Lemma hadj_app : forall V h1 h2 lv, hadj V lv (h1 ++ h2) <-> hadj V lv h1 /\ hadj V (lastv V lv h1) h2.
Proof.
  intros V h1. induction h1 as [|[w b] h1 IH]; intros h2 lv; simpl.
  - tauto.
  - rewrite IH. tauto.
Qed.

Lemma hadj_ext : forall V V' h lv, (forall w, In w (ids h) -> V w = V' w) -> hadj V lv h -> hadj V' lv h.
Proof.
  intros V V' h. induction h as [|[w b] h IH]; intros lv E H; simpl in *; auto.
  destruct H as [H1 H2]. assert (Ew : V w = V' w) by (apply E; left; reflexivity).
  split; [intros Hb; rewrite <- Ew; apply H1; auto|]. rewrite <- Ew. apply (IH (V w)); [|exact H2].
  intros w' I. apply E. right. exact I.
Qed.

Lemma hadj_head : forall V h lv lv', free_head h -> hadj V lv h -> hadj V lv' h.
Proof.
  intros V h lv lv' F H. destruct h as [|[w b] h]; simpl in *; auto.
  destruct H as [H1 H2]. assert (b = false) by (apply (F w b h); reflexivity). subst b.
  split; [intros; discriminate|exact H2].
Qed.

Lemma hadj_ins : forall V V' h1 h2 t b lv, (forall w, In w (ids (h1 ++ h2)) -> V w = V' w) ->
  hadj V lv (h1 ++ h2) -> free_head h2 -> (b = true -> V' t = lastv V' lv h1) ->
  hadj V' lv (h1 ++ (t, b) :: h2).
Proof.
  intros V V' h1 h2 t b lv E H F T. pose proof (hadj_ext V V' _ _ E H) as H'.
  rewrite hadj_app in H' |- *. destruct H' as [A B]. split; [exact A|]. simpl. split; [exact T|].
  apply (hadj_head V' h2 (lastv V' lv h1)); auto.
Qed.

Lemma lastv_app : forall V h1 h2 lv, lastv V lv (h1 ++ h2) = lastv V (lastv V lv h1) h2.
Proof. intros V h1. induction h1 as [|[w b] h1 IH]; intros; simpl; auto. Qed.

(* the value at the end of a history agrees with the end of its erasure *)
Lemma lastv_hers : forall V V' h lv, hadj V lv h -> (forall w, In (w, false) h -> V w = V' w) ->
  lastv V lv h = lastv V' lv (hers h).
Proof.
  intros V V' h. induction h as [|[w b] h IH]; intros lv H E; simpl; auto.
  destruct H as [H1 H2]. destruct b.
  - simpl. rewrite (IH (V w)); auto; [|intros w' I; apply E; right; exact I]. rewrite (H1 eq_refl). reflexivity.
  - simpl. rewrite <- (E w (or_introl eq_refl)). apply IH; auto. intros w' I. apply E. right. exact I.
Qed.

Definition final_at (s : st) (x : cell) : val := lastv (fun w => wv s w x) 0 (hs s x).
Lemma final_lastv : forall s x, final s x = final_at s x.
Proof.
  intros s x. unfold final, final_at. rewrite <- (rev_involutive (hs s x)) at 2.
  destruct (rev (hs s x)) as [|[w b] r] eqn:E.
  - simpl. reflexivity.
  - simpl. rewrite lastv_app. simpl. reflexivity.
Qed.

(* ---------- the relation ---------- *)
(* a context state of sA is the one of sW with other rv (pointwise equal), rw (through pi) and
   views *)
Definition crel (sw : nat -> option (cell -> option nat)) (cW cA : cst) : Prop :=
  (exists rv' rw' P A R O Og, cA = cc_x cW rv' rw' P A R O Og) /\ (forall k x, rv cA k x = rv cW k x) /\ (forall k x, rw cA k x = pi sw x (rw cW k x)).

Record rel (sw : nat -> option (cell -> option nat)) (sW sA : st) : Prop := mkRel {
  r_tm : tm sA = tm sW;
  r_pcs : pcs sA = pcs sW;
  r_tp : tp sA = tp sW;
  r_cm : cm sA = cm sW;
  r_cr : forall c, crel sw (cs sW c) (cs sA c);
  r_hs : forall x, hs sA x = hers (hs sW x);
  r_kept : forall x w, In (w, false) (hs sW x) -> sw w = None /\ wv sA w x = wv sW w x;
  r_wb : forall x w, In (w, true) (hs sW x) -> exists f, sw w = Some f /\ wv sW w x = rdv (wv sA) (f x) x /\
           (forall w', f x = Some w' -> In w' (ids (hs sA x)));
  r_adj : forall x, hadj (fun w => wv sW w x) 0 (hs sW x);
  i_ids : forall x w, In w (ids (hs sW x)) -> w < tm sW;
  i_rw : forall c k x w, rw (cs sW c) k x = Some w -> In w (ids (hs sW x));
  i_oh : forall c k t, oh (cs sW c) k = Some t -> t < tm sW;
  i_sw : forall w, tm sW <= w -> sw w = None }.

Definition sw0 : nat -> option (cell -> option nat) := fun _ => None.

Lemma rel_init : rel sw0 sinit sinit.
Proof.
  constructor; try reflexivity; simpl.
  { intros c. split; [exists (rv cinit), (rw cinit), vnil, vnil, vnil, vnil, vnil; reflexivity|split; intros k x; reflexivity]. }
  all: intros; try contradiction; try discriminate; try exact I; try reflexivity.
Qed.

(* every history entry stands for a write A has *)
Lemma pi_hist : forall sw sW sA x w b, rel sw sW sA -> In (w, b) (hs sW x) ->
  wv sW w x = rdv (wv sA) (pi sw x (Some w)) x /\ (forall w', pi sw x (Some w) = Some w' -> In w' (ids (hs sA x))).
Proof.
  intros sw sW sA x w b R I. destruct b.
  - destruct (r_wb sw sW sA R x w I) as (f & Sf & V & M). unfold pi. rewrite Sf. split; auto.
  - destruct (r_kept sw sW sA R x w I) as [Sn V]. unfold pi. rewrite Sn. split; [simpl; symmetry; exact V|].
    intros w' E. injection E as <-. rewrite (r_hs sw sW sA R x). unfold ids. apply in_map_iff.
    exists (w, false). split; [reflexivity|]. apply in_hers. split; auto.
Qed.

(* a read of a write in the history of sW: the same value in A, the write there *)
Lemma pi_in : forall sw sW sA x w, rel sw sW sA -> In w (ids (hs sW x)) ->
  wv sW w x = rdv (wv sA) (pi sw x (Some w)) x /\ (forall w', pi sw x (Some w) = Some w' -> In w' (ids (hs sA x))).
Proof.
  intros sw sW sA x w R I. unfold ids in I. apply in_map_iff in I. destruct I as ([w0 b] & E & I). simpl in E. subst w0.
  apply (pi_hist sw sW sA x w b R I).
Qed.

Lemma pi_inm : forall sw sW sA x w, rel sw sW sA -> In w (ids (hs sW x)) ->
  match pi sw x (Some w) with Some w' => In w' (ids (hs sA x)) | None => True end.
Proof.
  intros sw sW sA x w R I. destruct (pi_in sw sW sA x w R I) as [_ M].
  destruct (pi sw x (Some w)) as [w'|] eqn:E; [|exact Logic.I]. apply M. reflexivity.
Qed.

(* a write placed in a history is not placed before a write-back store *)
Definition fhsafe (s s' : st) : Prop :=
  forall x h1 h2, hs s x = h1 ++ h2 -> hs s' x = h1 ++ (tm s, false) :: h2 -> free_head h2.
