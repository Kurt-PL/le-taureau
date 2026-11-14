(* Part 3: the knowledge relation between a write-back state and its A image.
   KR: the image's log entries are the state's (same context, slot, cells, kind; the writes they
   took through pi), and what the image knows is covered (cov) by what the state knows: an item of
   the image's view is in the state's view or has a path of the state's event graph into it.
   For the entries of the times Good, what they knew in order through guard() is covered too.
   A write the image holds conveys nothing that has no path into it in the state (k_wc).
   The rest are facts of the state alone that the cover needs (WI). *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Ev M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB M2DQWBK1 M2DQWBK2.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQShim.

(* ---------- a written-back store and the write it stands for ---------- *)
Definition allt (h : hist) : Prop := Forall (fun e => snd e = true) h.
(* the store w stands for u (in A): u, then only written-back stores, then w; for nothing: only
   written-back stores before w *)
Definition seg (h : hist) (w : nat) (o : option nat) : Prop :=
  match o with
  | None => exists h1 h2, h = h1 ++ (w, true) :: h2 /\ allt h1
  | Some u => exists h0 h1 h2, h = h0 ++ (u, false) :: h1 ++ (w, true) :: h2 /\ allt h1
  end.

Lemma split3 : forall {X} (h1 h2 A B : list X) (e : X), h1 ++ h2 = A ++ e :: B ->
  (exists A2, h1 = A ++ e :: A2 /\ B = A2 ++ h2) \/ (exists A1, A = h1 ++ A1 /\ h2 = A1 ++ e :: B).
Proof.
  intros X h1 h2 A B e E. apply app_eq_app in E. destruct E as (l & [(E1 & E2)|(E1 & E2)]).
  - destruct l as [|y l].
    + rewrite app_nil_r in E1. subst h1. right. exists []. rewrite app_nil_r. split; [reflexivity|exact (eq_sym E2)].
    + injection E2 as <- E2. left. exists l. split; [exact E1|exact E2].
  - right. exists l. split; [exact E1|exact E2].
Qed.

Lemma allt_app : forall a b, allt (a ++ b) <-> allt a /\ allt b.
Proof. intros. unfold allt. rewrite Forall_app. tauto. Qed.

(* a store that is not written-back, placed before nothing written-back, keeps every segment *)
Lemma seg_ins_f : forall h1 h2 t w o, seg (h1 ++ h2) w o -> free_head h2 -> seg (h1 ++ (t, false) :: h2) w o.
Proof.
  intros h1 h2 t w [u|] S F; cbn in S |- *.
  - destruct S as (A & B & C & E & Al).
    destruct (split3 h1 h2 A (B ++ (w, true) :: C) (u, false) E) as [(A2 & E1 & E2)|(A1 & E1 & E2)].
    + destruct (split3 A2 h2 B C (w, true) (eq_sym E2)) as [(A3 & E3 & E4)|(A3 & E3 & E4)].
      * exists A, B, (A3 ++ (t, false) :: h2). split; [|exact Al]. rewrite E1, E3. repeat (rewrite <- app_assoc; simpl). reflexivity.
      * exfalso. destruct A3 as [|[y b] A3].
        -- simpl in E4. rewrite E4 in F. pose proof (F w true C eq_refl). discriminate.
        -- rewrite E3 in Al. apply allt_app in Al. destruct Al as [_ Al]. pose proof (Forall_inv Al) as Hy. simpl in Hy. subst b.
           rewrite E4 in F. simpl in F. pose proof (F y true _ eq_refl). discriminate.
    + exists (h1 ++ (t, false) :: A1), B, C. split; [|exact Al]. rewrite E2. rewrite <- app_assoc. reflexivity.
  - destruct S as (B & C & E & Al).
    destruct (split3 h1 h2 B C (w, true) E) as [(A3 & E3 & E4)|(A3 & E3 & E4)].
    + exists B, (A3 ++ (t, false) :: h2). split; [|exact Al]. rewrite E3. rewrite <- app_assoc. reflexivity.
    + exfalso. destruct A3 as [|[y b] A3].
      * simpl in E4. rewrite E4 in F. pose proof (F w true C eq_refl). discriminate.
      * rewrite E3 in Al. apply allt_app in Al. destruct Al as [_ Al]. pose proof (Forall_inv Al) as Hy. simpl in Hy. subst b.
        rewrite E4 in F. simpl in F. pose proof (F y true _ eq_refl). discriminate.
Qed.
Lemma eq_sym_app : forall {X} (a b : list X), a = b -> b = a. Proof. intros; subst; reflexivity. Qed.

(* a written-back store placed anywhere keeps every segment *)
Lemma seg_ins_t : forall h1 h2 t w o, seg (h1 ++ h2) w o -> seg (h1 ++ (t, true) :: h2) w o.
Proof.
  intros h1 h2 t w [u|] S; cbn in S |- *.
  - destruct S as (A & B & C & E & Al).
    destruct (split3 h1 h2 A (B ++ (w, true) :: C) (u, false) E) as [(A2 & E1 & E2)|(A1 & E1 & E2)].
    + destruct (split3 A2 h2 B C (w, true) (eq_sym E2)) as [(A3 & E3 & E4)|(A3 & E3 & E4)].
      * exists A, B, (A3 ++ (t, true) :: h2). split; [|exact Al]. rewrite E1, E3. repeat (rewrite <- app_assoc; simpl). reflexivity.
      * exists A, (A2 ++ (t, true) :: A3), C. split.
        -- rewrite E1, E4. repeat (rewrite <- app_assoc; simpl). reflexivity.
        -- rewrite E3 in Al. apply allt_app in Al. apply allt_app. destruct Al as [A' B']. split; [exact A'|constructor; [reflexivity|exact B']].
    + exists (h1 ++ (t, true) :: A1), B, C. split; [|exact Al]. rewrite E2. rewrite <- app_assoc. reflexivity.
  - destruct S as (B & C & E & Al).
    destruct (split3 h1 h2 B C (w, true) E) as [(A3 & E3 & E4)|(A3 & E3 & E4)].
    + exists B, (A3 ++ (t, true) :: h2). split; [|exact Al]. rewrite E3. rewrite <- app_assoc. reflexivity.
    + exists (h1 ++ (t, true) :: A3), C. split.
      * rewrite E4. rewrite <- app_assoc. reflexivity.
      * rewrite E3 in Al. apply allt_app in Al. apply allt_app. destruct Al as [A' B']. split; [exact A'|constructor; [reflexivity|exact B']].
Qed.

(* with distinct ids, an id has one place *)
Lemma nodup_place : forall (X Y X' Y' : hist) v b b', NoDup (ids (X ++ (v, b) :: Y)) -> X ++ (v, b) :: Y = X' ++ (v, b') :: Y' ->
  X = X' /\ b = b' /\ Y = Y'.
Proof.
  induction X as [|z X IH]; intros Y X' Y' v b b' N E; destruct X' as [|z' X']; simpl in *.
  - injection E as -> ->. auto.
  - exfalso. injection E as <- E. inversion N as [|? ? H1 _]. apply H1. rewrite E. rewrite ids_app. apply in_app_iff. right. left. reflexivity.
  - exfalso. injection E as -> E. inversion N as [|? ? H1 _]. apply H1. rewrite ids_app. apply in_app_iff. right. left. reflexivity.
  - injection E as <- E. inversion N as [|? ? _ N']. destruct (IH Y X' Y' v b b' N' E) as (-> & -> & ->). auto.
Qed.

(* ---------- the relation ---------- *)
Definition ksame (sw : nat -> option (cell -> option nat)) (sW : st) (t : nat) (eA eW : oev) : Prop :=
  et eA = et eW /\ ec eA = ec eW /\ ek eA = ek eW /\ eC eA = eC eW /\ eR eA = eR eW /\ eh eA = eh eW /\
  (forall x, erf eA x = pi sw x (erf eW x)) /\ (forall x w0, erf eW x = Some w0 -> In w0 (ids (hs sW x))) /\
  (ew eA = true -> ew eW = true /\ sw t = None) /\ (sw t = None -> ew eW = ew eA).

Record KR (Fk : Prop) (Good : nat -> Prop) (sw : nat -> option (cell -> option nat)) (sW sA : st) : Prop := {
  k_len : length (lg sA) = length (lg sW);
  k_ent : forall t eA, ent sA t = Some eA -> exists eW, ent sW t = Some eW /\ ksame sw sW t eA eW;
  k_eQ : Fk -> forall t eA eW, ent sA t = Some eA -> ent sW t = Some eW -> Good t -> vsub (eQ eA) (cov sW (eQ eW));
  k_P : Fk -> forall c, vsub (vP (cs sA c)) (cov sW (vP (cs sW c)));
  k_A : Fk -> forall c, vsub (vA (cs sA c)) (cov sW (vA (cs sW c)));
  k_Og : Fk -> forall c, vsub (vOg (cs sA c)) (cov sW (vOg (cs sW c)));
  k_G : Fk -> vsub (vG sA) (cov sW (vG sW));
  k_wc : Fk -> forall y x, In y (ids (hs sA x)) -> forall z, wc sA y z -> z = y \/ Pth sW z y;
  w_bet : forall x w, In (w, true) (hs sW x) -> exists f, sw w = Some f /\ seg (hs sW x) w (f x);
  w_nodup : forall x, NoDup (ids (hs sW x));
  w_OW : forall c, vsub (ownw sW c) (vP (cs sW c));
  w_OGP : forall tf f, ent sW tf = Some f -> isFF sW tf f ->
    vsub (eP f) (vOg (cs sW (ec f))) /\ vsub (eP f) (vP (cs sW (ec f)));
  w_OWG : forall tf f z, ent sW tf = Some f -> isFF sW tf f -> ownw sW (ec f) z -> z < tf -> eP f z;
  w_WBOC : forall c j t1, oh (cs sW c) j = Some t1 -> sw t1 <> None ->
    oc (cs sW c) j = None /\ (j < pcs sW c \/ vok (rg (cs sW c) j) = false);
  w_swc : forall t f, sw t = Some f -> exists e, ent sW t = Some e /\ is_cas (ai (cs sW (ec e)) (ek e)) = true;
  w_tmo : forall t e, ent sW t = Some e -> ew e = true -> tmo (cs sW (ec e)) (ek e) = Some t
}.

Lemma KR_init : forall Fk Good, KR Fk Good sw0 sinit sinit.
Proof.
  intros Fk Good. constructor; unfold ent, sw0; cbn; intros.
  all: try (match goal with H : nth_error [] ?t = Some _ |- _ => destruct t; discriminate end).
  all: try contradiction; try discriminate; try reflexivity.
  all: try (intros z Z; contradiction).
  all: try (intros; constructor).
  all: try (match goal with H : ownw _ _ _ |- _ => destruct H as (e & E & _); destruct z; discriminate end).
  intros z (e & E & _). destruct z; discriminate.
Qed.

(* ---------- what the A image's invariants say of the state ---------- *)
Section Tr.
Set Default Proof Using "All".
Variables (p : prog) (Fk : Prop) (Good : nat -> Prop) (sw : nat -> option (cell -> option nat)) (sW sA : st).
Hypothesis RA : run p sA.
Hypothesis R : rel sw sW sA.
Hypothesis K : KR Fk Good sw sW sA.

Lemma crel_eq : forall c, oc (cs sA c) = oc (cs sW c) /\ oh (cs sA c) = oh (cs sW c) /\ ai (cs sA c) = ai (cs sW c) /\
  rg (cs sA c) = rg (cs sW c) /\ fx (cs sA c) = fx (cs sW c) /\ bd (cs sA c) = bd (cs sW c).
Proof.
  intros c. destruct (r_cr sw sW sA R c) as ((rv' & rw' & P & A & R' & O & Og & E) & _). rewrite E. cbn. auto 10.
Qed.

Lemma tmW : tm sW = length (lg sW).
Proof. rewrite <- (r_tm sw sW sA R), <- (k_len Fk Good sw sW sA K). exact (i_tm p sA (Inv1_run p sA RA)). Qed.

Lemma entW : forall t eW, ent sW t = Some eW -> exists eA, ent sA t = Some eA /\ ksame sw sW t eA eW.
Proof.
  intros t eW E. destruct (nth_error (lg sA) t) as [eA|] eqn:EA.
  - destruct (k_ent Fk Good sw sW sA K t eA EA) as (eW' & E' & S). unfold ent in *. rewrite E in E'. injection E' as <-. eauto.
  - exfalso. apply nth_error_None in EA. rewrite (k_len Fk Good sw sW sA K) in EA. unfold ent in E.
    assert (t < length (lg sW)) by (apply nth_error_Some; congruence). lia.
Qed.

Lemma i_etW : forall t e, ent sW t = Some e ->
  et e = t /\ (if eh e then oh (cs sW (ec e)) (ek e) else oc (cs sW (ec e)) (ek e)) = Some t.
Proof.
  intros t e E. destruct (entW t e E) as (eA & EA & (E1 & E2 & E3 & _ & _ & E6 & _)).
  destruct (i_et p sA (Inv1_run p sA RA) t eA EA) as [Et Eo]. rewrite <- E1, <- E2, <- E3, <- E6.
  split; [exact Et|]. destruct (crel_eq (ec eA)) as (Oc & Oh & _). rewrite <- Oc, <- Oh. exact Eo.
Qed.

Lemma i_ohW : forall c k t, oh (cs sW c) k = Some t -> exists e, ent sW t = Some e /\ ec e = c /\ ek e = k /\ eh e = true.
Proof.
  intros c k t H. destruct (crel_eq c) as (_ & Oh & _). rewrite <- Oh in H.
  destruct (M2Inv.i_oh p sA (Inv1_run p sA RA) c k t H) as (eA & EA & E1 & E2 & E3).
  destruct (k_ent Fk Good sw sW sA K t eA EA) as (eW & EW & (_ & F2 & F3 & _ & _ & F6 & _)). exists eW. split; [exact EW|]. 
  split; [congruence|split; congruence].
Qed.

Lemma i_ocW : forall c k t, oc (cs sW c) k = Some t -> exists e, ent sW t = Some e /\ ec e = c /\ ek e = k.
Proof.
  intros c k t H. destruct (crel_eq c) as (Oc & _). rewrite <- Oc in H.
  destruct (i_oc p sA (Inv1_run p sA RA) c k t H) as (eA & EA & E1 & E2).
  destruct (k_ent Fk Good sw sW sA K t eA EA) as (eW & EW & (_ & F2 & F3 & _)). exists eW. split; [exact EW|]. split; congruence.
Qed.

Lemma ent_ltW : forall t e, ent sW t = Some e -> t < tm sW.
Proof. intros t e E. rewrite tmW. unfold ent in E. apply nth_error_Some. congruence. Qed.

(* the ownership of a write in the image is the state's *)
Lemma ownw_AW : forall c z, ownw sA c z -> ownw sW c z.
Proof.
  intros c z (e & E & Ec & Ew). destruct (k_ent Fk Good sw sW sA K z e E) as (eW & EW & (_ & F2 & _ & _ & _ & _ & _ & _ & F9 & _)).
  exists eW. split; [exact EW|]. split; [congruence|]. exact (proj1 (F9 Ew)).
Qed.

(* a guard() event of the state is one of the image *)
Lemma isFF_WA : forall tg g gA, isFF sW tg g -> ksame sw sW tg gA g -> isFF sA tg gA.
Proof.
  intros tg g gA (Fa & Fp & Fo) (_ & E2 & E3 & _). unfold isFF. rewrite E2, E3.
  destruct (crel_eq (ec g)) as (Oc & _ & Ai & _). rewrite Oc, Ai, (r_pcs sw sW sA R). auto.
Qed.

(* the entry of a guard() stores nothing *)
Lemma ffew : forall tg g, ent sW tg = Some g -> isFF sW tg g -> ew g = false.
Proof.
  intros tg g E (Fa & _). destruct (entW tg g E) as (eA & EA & S). pose proof S as (_ & E2 & E3 & _ & _ & _ & _ & _ & _ & F10).
  destruct (sw tg) as [f|] eqn:Sw.
  - destruct (w_swc Fk Good sw sW sA K tg f Sw) as (e' & E' & C). rewrite E in E'. injection E' as <-. rewrite Fa in C. discriminate.
  - rewrite (F10 eq_refl). destruct (j_ew p sA (proj2 (Inv2_run p sA RA)) tg eA _ EA eq_refl) as [J _].
    rewrite J. unfold einstr. rewrite E2, E3. destruct (crel_eq (ec g)) as (_ & _ & Ai & _). rewrite Ai, Fa.
    cbn. rewrite andb_false_r. destruct (negb (eh eA)); reflexivity.
Qed.
End Tr.

