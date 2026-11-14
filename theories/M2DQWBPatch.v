(* Write-back, part 6: the write-back store (the patch) and what it does to the relation. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2WBReg M2WBRel M2WBEff M2WBSim.

(* the log entry of time t becomes a store's *)
Definition setew (l : list oev) (t : nat) : list oev :=
  map (fun e => if Nat.eqb (et e) t then mkO (et e) (ec e) (ek e) (eP e) (erf e) true (eC e) (eR e) (eQ e) (eQc e) (eh e) else e) l.

(* the write-back store of the CAS recorded at slot k of context c, with the id t: it stores
   in each cell of the CAS the value of the write the CAS's load observed there (rw), and is a
   write of the context for fences (own writes), for publication (knowledge) and for the writes
   it conveys (wc).
   The write-back store is a write the CAS made (spec 0.1 §2.3.4), so in each of its cells slot k
   records t (spec 0.1 §2.3 "the write its leader made there"): a read counted on with this CAS as
   its leader takes the write-back t, whose value is that of the observed write. *)
Definition wbrw (cc : cst) (k : nat) (xs : list cell) (t : nat) : cell -> option nat :=
  fun x => if existsb (Nat.eqb x) xs then Some t else rw cc k x.

Definition wbst (s : st) (c k t : nat) (H'' : cell -> hist) : st :=
  let cc := cs s c in
  mkS (tm s)
    (upd (cs s) c (mkC (oc cc) (rg cc) (ai cc) (upd (rw cc) k (wbrw cc k (icells (ai cc k)) t)) (rv cc) (bd cc)
                       (vor (vP cc) (vone t)) (vA cc) (vR cc) (vO cc) (vOg cc) (oh cc) (fx cc)))
    (upd (wv s) t (fun x => rdv (wv s) (rw cc k x) x))
    (upd (wc s) t (vor (vR cc) (vone t)))
    H'' (vG s) (pcs s) (tp s) (cm s) (setew (lg s) t) (es s).

(* placed in each of its cells immediately after the write its load observed there, and
   before nothing that is itself such a store *)
Definition wbok (s : st) (c k t : nat) (H'' : cell -> hist) : Prop :=
  enters_tied (rw (cs s c) k) (hs s) (icells (ai (cs s c) k)) t H''.

Lemma pi_upd : forall (sw : nat -> option (cell -> option nat)) t g x w0, w0 <> t ->
  pi (upd sw t g) x (Some w0) = pi sw x (Some w0).
Proof. intros sw t g x w0 N. unfold pi, upd. destruct (Nat.eqb_spec w0 t); [congruence|reflexivity]. Qed.

Section P.
Variables (sw : nat -> option (cell -> option nat)) (s sA : st) (c k t : nat) (H'' : cell -> hist).
Hypothesis R : rel sw s sA.
Hypothesis Ht : t < tm s.
Hypothesis Hfresh : forall x, ~ In t (ids (hs s x)).
Hypothesis Hok : wbok s c k t H''.
Let xs := icells (ai (cs s c) k).
Let u := rw (cs s c) k.
Let f : cell -> option nat := fun x => pi sw x (u x).
Let sw' := upd sw t (Some f).

Lemma ne_t : forall x w0, In w0 (ids (hs s x)) -> w0 <> t.
Proof. intros x w0 I E. subst. apply (Hfresh x). exact I. Qed.

Lemma H''_cell : forall x, (H'' x = hs s x /\ ~ In x xs) \/
  exists h1 h2, hs s x = h1 ++ h2 /\ free_head h2 /\ H'' x = h1 ++ (t, true) :: h2 /\ In x xs /\
    match u x with None => h1 = [] | Some w => exists h0 g, h1 = h0 ++ [(w, g)] end.
Proof.
  intros x. destruct (Hok x) as [H1 H2]. destruct (in_dec Nat.eq_dec x xs) as [I|N].
  - right. destruct (H1 I) as (h1 & h2 & E1 & E2 & F & E3). exists h1, h2. repeat split; auto.
  - left. split; [apply H2; exact N|exact N].
Qed.

Lemma hers_H'' : forall x, hers (H'' x) = hers (hs s x).
Proof.
  intros x. destruct (H''_cell x) as [(E & _)|(h1 & h2 & E1 & _ & E3 & _)].
  - rewrite E. reflexivity.
  - rewrite E3, E1. rewrite hers_ins_t, hers_app. reflexivity.
Qed.

Lemma old_in : forall x e, In e (hs s x) -> In e (H'' x).
Proof.
  intros x e I. destruct (H''_cell x) as [(E & _)|(h1 & h2 & E1 & _ & E3 & _)].
  - rewrite E. exact I.
  - rewrite E3. rewrite E1 in I. apply in_app_iff in I. apply in_app_iff. destruct I as [I|I]; [left; exact I|right; right; exact I].
Qed.

Lemma new_in : forall x e, In e (H'' x) -> In e (hs s x) \/ e = (t, true).
Proof.
  intros x e I. destruct (H''_cell x) as [(E & _)|(h1 & h2 & E1 & _ & E3 & _)].
  - left. rewrite <- E. exact I.
  - rewrite E3 in I. rewrite E1. apply in_app_iff in I. destruct I as [I|[I|I]].
    + left. apply in_app_iff. left. exact I.
    + right. symmetry. exact I.
    + left. apply in_app_iff. right. exact I.
Qed.

Lemma t_in : forall x, In x xs -> In (t, true) (H'' x).
Proof.
  intros x Ix. destruct (H''_cell x) as [(_ & N)|(h1 & h2 & E1 & _ & E3 & _)]; [contradiction|].
  rewrite E3. apply in_app_iff. right. left. reflexivity.
Qed.

Lemma ids_new : forall x w0, In w0 (ids (H'' x)) -> In w0 (ids (hs s x)) \/ w0 = t.
Proof.
  intros x w0 I. unfold ids in I. apply in_map_iff in I. destruct I as ([w1 b] & E & I). simpl in E. subst w1.
  destruct (new_in x _ I) as [O|E].
  - left. unfold ids. apply in_map_iff. exists (w0, b). auto.
  - right. injection E as ->. reflexivity.
Qed.

(* the value of the observed write, per cell, is what A holds *)
Lemma val_obs : forall x, rdv (wv s) (u x) x = rdv (wv sA) (f x) x /\ (forall w', f x = Some w' -> In w' (ids (hs sA x))).
Proof.
  intros x. unfold f. destruct (u x) as [w0|] eqn:E.
  - assert (I : In w0 (ids (hs s x))) by exact (i_rw sw s sA R c k x w0 E).
    destruct (pi_in sw s sA x w0 R I) as [V M]. simpl. split; [exact V|exact M].
  - simpl. split; [reflexivity|intros w' E1; discriminate].
Qed.

Lemma rel_wb : rel sw' (wbst s c k t H'') sA.
Proof.
  assert (TA : tm sA = tm s) by exact (r_tm sw s sA R).
  assert (Nrw : forall c' k' x w0, rw (cs s c') k' x = Some w0 -> w0 <> t).
  { intros c' k' x w0 E. apply (ne_t x). exact (i_rw sw s sA R c' k' x w0 E). }
  assert (Cr : forall c', crel sw' (cs s c') (cs sA c')).
  { intros c'. destruct (r_cr sw s sA R c') as (Ex & Hv & Hw). split; [exact Ex|split; [exact Hv|]].
    intros k' x. rewrite (Hw k' x). destruct (rw (cs s c') k' x) as [w0|] eqn:E; [|reflexivity].
    symmetry. apply pi_upd. exact (Nrw c' k' x w0 E). }
  constructor.
  - exact TA.
  - exact (r_pcs sw s sA R).
  - exact (r_tp sw s sA R).
  - exact (r_cm sw s sA R).
  - { intros c'. unfold wbst at 1. cbn [cs]. unfold upd at 1. destruct (Nat.eqb c' c) eqn:E1; [|apply Cr].
    apply Nat.eqb_eq in E1. subst c'. destruct (r_cr sw s sA R c) as ((rv' & rw' & P & A & R' & O & Og & Ecs) & Hv & Hw).
    split; [|split].
    + exists rv', rw', (vP (cs sA c)), (vA (cs sA c)), (vR (cs sA c)), (vO (cs sA c)), (vOg (cs sA c)). rewrite Ecs. reflexivity.
    + cbn [rv]. exact Hv.
    + cbn [rw]. intros k' x. unfold upd. destruct (Nat.eqb k' k) eqn:E2; cbv iota beta.
      * unfold wbrw. apply Nat.eqb_eq in E2. subst k'. rewrite (Hw k x).
        destruct (existsb (Nat.eqb x) (icells (ai (cs s c) k))).
        { unfold pi at 2. unfold sw', upd. rewrite Nat.eqb_refl. unfold f, u. reflexivity. }
        destruct (rw (cs s c) k x) as [w0|] eqn:E4; [|reflexivity].
        symmetry. apply pi_upd. exact (Nrw c k x w0 E4).
      * rewrite (Hw k' x). destruct (rw (cs s c) k' x) as [w0|] eqn:E4; [|reflexivity].
        symmetry. apply pi_upd. exact (Nrw c k' x w0 E4). }
  - intros x. cbn [hs wbst]. rewrite hers_H''. exact (r_hs sw s sA R x).
  - intros x w0 I. cbn [hs wbst] in I. destruct (new_in x _ I) as [O|E]; [|discriminate]. cbn [hs wv wbst].
    destruct (r_kept sw s sA R x w0 O) as [K1 K2]. assert (Nw : w0 <> t) by (apply (ne_t x); unfold ids; apply in_map_iff; exists (w0, false); auto).
    unfold sw', upd. destruct (Nat.eqb_spec w0 t); [congruence|]. unfold upd. destruct (Nat.eqb_spec w0 t); [congruence|]. split; [exact K1|exact K2].
  - intros x w0 I. cbn [hs wbst] in I. destruct (new_in x _ I) as [O|E].
    + cbn [hs wv wbst]. destruct (r_wb sw s sA R x w0 O) as (g & Sg & V & M). assert (Nw : w0 <> t) by (apply (ne_t x); unfold ids; apply in_map_iff; exists (w0, true); auto).
      exists g. unfold sw', upd. destruct (Nat.eqb_spec w0 t); [congruence|]. unfold upd. destruct (Nat.eqb_spec w0 t); [congruence|]. split; [exact Sg|split; [exact V|exact M]].
    + cbn [hs wv wbst]. injection E as ->. exists f. split; [unfold sw', upd; rewrite Nat.eqb_refl; reflexivity|].
      unfold upd. rewrite Nat.eqb_refl. exact (val_obs x).
  - intros x. cbn [hs wv wbst]. destruct (H''_cell x) as [(E & N)|(h1 & h2 & E1 & F & E3 & Ix & E4)].
    + rewrite E. apply (hadj_ext (fun w => wv s w x) (fun w => upd (wv s) t (fun x0 => rdv (wv s) (rw (cs s c) k x0) x0) w x)); [|apply (r_adj sw s sA R x)].
      intros w0 I. unfold upd. destruct (Nat.eqb_spec w0 t); [exfalso; exact (ne_t x w0 I e)|reflexivity].
    + rewrite E3. apply (hadj_ins (fun w => wv s w x) (fun w => upd (wv s) t (fun x0 => rdv (wv s) (rw (cs s c) k x0) x0) w x) h1 h2 t true 0).
      * intros w0 I. rewrite <- E1 in I. unfold upd. destruct (Nat.eqb_spec w0 t); [exfalso; exact (ne_t x w0 I e)|reflexivity].
      * rewrite <- E1. apply (r_adj sw s sA R x).
      * exact F.
      * intros _. unfold upd at 1. rewrite Nat.eqb_refl. fold u. destruct (u x) as [w0|] eqn:Eu.
        -- destruct E4 as (h0 & g & E5). rewrite E5. rewrite lastv_app. simpl. unfold upd. destruct (Nat.eqb_spec w0 t).
           ++ exfalso. apply (ne_t x w0); [|exact e]. exact (i_rw sw s sA R c k x w0 Eu).
           ++ reflexivity.
        -- rewrite E4. reflexivity.
  - intros x w0 I. cbn [hs tm wbst] in *. destruct (ids_new x w0 I) as [O|E]; [exact (i_ids sw s sA R x w0 O)|subst; exact Ht].
  - intros c' k' x w0. cbn [cs hs wbst]. unfold upd at 1. destruct (Nat.eqb c' c) eqn:E1.
    + apply Nat.eqb_eq in E1. subst c'. cbn [rw]. unfold upd at 1. destruct (Nat.eqb k' k) eqn:E2; cbv iota beta.
      * unfold wbrw. intros E. apply Nat.eqb_eq in E2. subst k'.
        destruct (existsb (Nat.eqb x) (icells (ai (cs s c) k))) eqn:Ex.
        { injection E as <-. apply existsb_exists in Ex. destruct Ex as (y & Iy & Ey). apply Nat.eqb_eq in Ey. subst y.
          unfold ids. apply in_map_iff. exists (t, true). split; [reflexivity|apply t_in; exact Iy]. }
        pose proof (i_rw sw s sA R c k x w0 E) as I. unfold ids in I |- *.
        apply in_map_iff in I. destruct I as (e & Ee & Ie). apply in_map_iff. exists e. split; [exact Ee|apply old_in; exact Ie].
      * intros E. pose proof (i_rw sw s sA R c k' x w0 E) as I. unfold ids in I |- *.
        apply in_map_iff in I. destruct I as (e & Ee & Ie). apply in_map_iff. exists e. split; [exact Ee|apply old_in; exact Ie].
    + intros E. pose proof (i_rw sw s sA R c' k' x w0 E) as I. unfold ids in I |- *.
      apply in_map_iff in I. destruct I as (e & Ee & Ie). apply in_map_iff. exists e. split; [exact Ee|apply old_in; exact Ie].
  - intros c' k' t0. cbn [cs wbst]. unfold upd at 1. destruct (Nat.eqb c' c) eqn:E1.
    + apply Nat.eqb_eq in E1. subst c'. cbn [oh]. exact (i_oh sw s sA R c k' t0).
    + exact (i_oh sw s sA R c' k' t0).
  - intros w0 L. cbn [tm wbst] in L. unfold sw', upd. destruct (Nat.eqb_spec w0 t); [lia|]. exact (i_sw sw s sA R w0 L).
Qed.
End P.
