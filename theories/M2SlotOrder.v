(* Model2: the slot-order condition of s_early costs no finished run.

   s_early records an early access at a free slot and asks that the pending
   accesses tied to it are recorded at earlier slots. step0 is the model
   without that condition. Every finished run of step0 is a run of the
   model (run0_done_run): a run that records a tied pair in the other order
   can never reach the earlier slot, because s_match there asks that the
   access reached happened first among the pending accesses tied to it.

   Also: under any registers, the places of two tied pending accesses come
   in the order they happened (placed_tied_order). *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Eff M2Inv M2Inv2 M2Cont M2Avoid.

Inductive step0 (p : prog) : st -> st -> Prop :=
(* the next instruction, in programme order *)
| s0_ord : forall s c i m' a K u w,
    let cc := cs s c in
    let k := pcs s c in
    ins p c k (rg cc) = i ->
    executes i (rg cc) = true ->
    oc cc k = None ->
    oh cc k = None ->
    determined p cc c k i ->
    (executes i (rg cc) = true -> forall k' d, pending cc k k' d -> ~ tied i (inst_of d)) ->
    (executes i (rg cc) = true -> forall k' m xs, hpending cc k k' m xs -> ~ tied i (crd m xs)) ->
    (forall x b, bd cc k = true -> In x (icells i) -> fbinder p c (rg cc) k x = Some b -> u x = rw cc b x) ->
    eff (tm s) i (rg cc) (mof s c) m' a K u w ->
    (* a result fixed there (S3c) is the result *)
    fxok cc k i (rg cc) a ->
    step0 p s
      (mkS (S (tm s))
           (upd (cs s) c (mkC (upd (oc cc) k (Some (tm s))) (upd (rg cc) k a) (upd (ai cc) k i)
                              (upd (rw cc) k (wrote (tm s) (icells i) u w)) (upd (rv cc) k (rdval (mof s c) u))
                              (bd cc) (mP m') (mA m') (mR m')
                              (newO s c i (mof s c) m' (vO cc)) (newOg i m' (vOg cc)) (oh cc) (fx cc)))
           (mV m') (mC m') (mH m') (mG m')
           (upd (pcs s) c (S k)) (upd (tp s) c (Nat.max (tp s c) (S k)))
           (cm s ++ [(c, k, tm s)])
           (lg s ++ [mkO (tm s) c k K u w (evC i (rg cc)) (evR i (rg cc)) (evQ s c i (rg cc) (mof s c) (vOg cc) (vO cc) u w) (evQc i (rg cc) (vO cc) w) false])
           (es s))
(* the next instruction, when it does not execute (an access whose condition
   is false, or a CAS whose read happened and whose comparison fails): the
   context passes it; it performs nothing, so nothing is logged and no time
   passes *)
| s0_skip : forall s c i,
    let cc := cs s c in
    let k := pcs s c in
    ins p c k (rg cc) = i ->
    xex cc i (rg cc) k = false ->
    oc cc k = None ->
    (* a CAS whose read happened: the instruction reached is that CAS *)
    (oh cc k <> None -> eofR i (rg cc) = eofR (ai cc k) (rg cc)) ->
    (* it has committed to failure *)
    (oh cc k <> None -> vok (rg cc k) = false) ->
    hfirst cc k i ->
    determined p cc c k i ->
    fxok cc k i (rg cc) (rg cc k) ->
    step0 p s
      (mkS (tm s)
           (upd (cs s) c (mkC (oc cc) (rg cc) (upd (ai cc) k i) (rw cc) (rv cc) (bd cc)
                              (vP cc) (vA cc) (vR cc) (vO cc) (vOg cc) (oh cc) (fx cc)))
           (wv s) (wc s) (hs s) (vG s)
           (upd (pcs s) c (S k)) (upd (tp s) c (Nat.max (tp s c) (S k)))
           (cm s ++ [(c, k, tm s)]) (lg s) (es s))
(* an access early, recorded at slot k *)
| s0_early : forall s c k d (B : nat -> bool) m' a K u w,
    let cc := cs s c in
    pcs s c < k ->
    oc cc k = None ->
    oh cc k = None ->
    early_ok p c cc (pcs s c) (tp s c) (tm s) d u B ->
    eff (tm s) (inst_of d) (rg cc) (mof s c) m' a K u w ->
    (* a result fixed at its place (S3c) is its result *)
    (forall f j, first_at p c cc (pcs s c) (creg p c cc (pcs s c) (tp s c) (bor (bd cc) B) f) (tm s) d j ->
       fxok cc j (inst_of d) (rg cc) a) ->
    step0 p s
      (mkS (S (tm s))
           (upd (cs s) c (mkC (upd (oc cc) k (Some (tm s))) (upd (rg cc) k a) (upd (ai cc) k (inst_of d))
                              (upd (rw cc) k (wrote (tm s) (icells (inst_of d)) u w)) (upd (rv cc) k (rdval (mof s c) u))
                              (bor (bd cc) B) (mP m') (mA m') (mR m')
                              (newO s c (inst_of d) (mof s c) m' (vO cc)) (newOg (inst_of d) m' (vOg cc)) (oh cc) (fx cc)))
           (mV m') (mC m') (mH m') (mG m')
           (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k)))
           (cm s)
           (lg s ++ [mkO (tm s) c k K u w (evC (inst_of d) (rg cc)) (evR (inst_of d) (rg cc))
                         (evQ s c (inst_of d) (rg cc) (mof s c) (vOg cc) (vO cc) u w)
                         (evQc (inst_of d) (rg cc) (vO cc) w) false])
           (upd (es s) (tm s) (Some (cc, pcs s c, tp s c, B))))
(* the context reaches an access that happened early; from now on the slot
   records the programme's instruction, which does the same *)
| s0_match : forall s c d,
    let cc := cs s c in
    let k := pcs s c in
    oc cc k <> None ->
    ai cc k = inst_of d ->
    eof (ins p c k (rg cc)) (rg cc) = Some d ->
    determined p cc c k (ins p c k (rg cc)) ->
    (* the access is the place reached: of the pending accesses tied to it,
       it happened first *)
    (forall k' d' t t', pending cc k k' d' -> k' <> k -> oc cc k = Some t -> oc cc k' = Some t' ->
       tied (inst_of d) (inst_of d') -> t < t') ->
    (forall k' m xs t t', hpending cc k k' m xs -> k' <> k -> oc cc k = Some t -> oh cc k' = Some t' ->
       tied (inst_of d) (crd m xs) -> t < t') ->
    fxok cc k (ins p c k (rg cc)) (rg cc) (rg cc k) ->
    step0 p s
      (mkS (tm s)
           (upd (cs s) c (mkC (oc cc) (rg cc) (upd (ai cc) k (ins p c k (rg cc))) (rw cc) (rv cc) (bd cc)
                              (vP cc) (vA cc) (vR cc) (vO cc) (vOg cc) (oh cc) (fx cc)))
           (wv s) (wc s) (hs s) (vG s)
           (upd (pcs s) c (S k)) (tp s) (cm s ++ [(c, k, tm s)]) (lg s) (es s))
(* a CAS's read alone, early or in order, recorded at slot k *)
| s0_cread : forall s c k m xs (B : nat -> bool) m' a K u w (bv : bool),
    let cc := cs s c in
    let i := ILd m xs (fun _ => true) in
    pcs s c <= k ->
    oc cc k = None ->
    oh cc k = None ->
    early_okR p c cc (pcs s c) (tp s c) (tm s) m xs u B ->
    eff (tm s) i (rg cc) (mof s c) m' a K u w ->
    (forall f j, first_atR p c cc (pcs s c) (creg p c cc (pcs s c) (tp s c) (bor (bd cc) B) f) (tm s) m xs j ->
       match fx cc j with Some b => b = bv | None => bv = true end /\
       fxok cc j (ins p c j (creg p c cc (pcs s c) (tp s c) (bor (bd cc) B) f))
         (creg p c cc (pcs s c) (tp s c) (bor (bd cc) B) f) (vd bv a)) ->
    step0 p s
      (mkS (S (tm s))
           (upd (cs s) c (mkC (oc cc) (upd (rg cc) k (vd bv a)) (upd (ai cc) k (crd m xs))
                              (upd (rw cc) k (wrote (tm s) (icells i) u w)) (upd (rv cc) k (rdval (mof s c) u))
                              (bor (bd cc) B) (mP m') (mA m') (mR m')
                              (newO s c i (mof s c) m' (vO cc)) (newOg i m' (vOg cc))
                              (upd (oh cc) k (Some (tm s))) (fx cc)))
           (mV m') (mC m') (mH m') (mG m')
           (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k)))
           (cm s)
           (lg s ++ [mkO (tm s) c k K u w (evC i (rg cc)) (evR i (rg cc))
                         (evQ s c i (rg cc) (mof s c) (vOg cc) (vO cc) u w)
                         (evQc i (rg cc) (vO cc) w) true])
           (upd (es s) (tm s) (Some (cc, pcs s c, tp s c, B))))
(* the write of a CAS whose read happened alone, in order (it succeeds, with
   the writes the read took; a CAS that fails writes nothing and is passed by
   s_skip) *)
| s0_cw : forall s c t1 i m' a K w,
    let cc := cs s c in
    let k := pcs s c in
    let u := rw cc k in
    ins p c k (rg cc) = i ->
    is_cas i = true ->
    oc cc k = None ->
    oh cc k = Some t1 ->
    (* the instruction reached is the CAS whose read happened *)
    eofR i (rg cc) = eofR (ai cc k) (rg cc) ->
    determined p cc c k i ->
    (forall k' d, pending cc k k' d -> ~ tied i (inst_of d)) ->
    (forall k' m xs, hpending cc k k' m xs -> k' <> k -> ~ tied i (crd m xs)) ->
    vok (rg cc k) = true ->
    eff (tm s) i (rg cc) (mof s c) m' a K u w ->
    w = true ->
    fxok cc k i (rg cc) a ->
    step0 p s
      (mkS (S (tm s))
           (upd (cs s) c (mkC (upd (oc cc) k (Some (tm s))) (upd (rg cc) k a) (upd (ai cc) k i)
                              (upd (rw cc) k (wrote (tm s) (icells i) u w)) (upd (rv cc) k (rdval (mof s c) u))
                              (bd cc) (mP m') (mA m') (mR m')
                              (newO s c i (mof s c) m' (vO cc)) (newOg i m' (vOg cc)) (oh cc) (fx cc)))
           (mV m') (mC m') (mH m') (mG m')
           (upd (pcs s) c (S k)) (upd (tp s) c (Nat.max (tp s c) (S k)))
           (cm s ++ [(c, k, tm s)])
           (lg s ++ [mkO (tm s) c k K u w (evC i (rg cc)) (evR i (rg cc)) (evQ s c i (rg cc) (mof s c) (vOg cc) (vO cc) u w) (evQc i (rg cc) (vO cc) w) false])
           (es s))
(* the write of a CAS whose read happened alone, early (it succeeds) *)
| s0_cwe : forall s c k t1 xs ev nv (B : nat -> bool) m' a K w,
    let cc := cs s c in
    let u := rw cc k in
    let d := DCas Plain xs ev nv in
    pcs s c < k ->
    oc cc k = None ->
    oh cc k = Some t1 ->
    ai cc k = crd Plain xs ->
    early_okW p c cc (pcs s c) (tp s c) (tm s) t1 Plain xs d B ->
    vok (rg cc k) = true ->
    eff (tm s) (inst_of d) (rg cc) (mof s c) m' a K u w ->
    w = true ->
    (forall f j, first_atR p c cc (pcs s c) (creg p c cc (pcs s c) (tp s c) (bor (bd cc) B) f) t1 Plain xs j ->
       fxok cc j (inst_of d) (rg cc) a) ->
    step0 p s
      (mkS (S (tm s))
           (upd (cs s) c (mkC (upd (oc cc) k (Some (tm s))) (upd (rg cc) k a) (upd (ai cc) k (inst_of d))
                              (upd (rw cc) k (wrote (tm s) (icells (inst_of d)) u w)) (upd (rv cc) k (rdval (mof s c) u))
                              (bor (bd cc) B) (mP m') (mA m') (mR m')
                              (newO s c (inst_of d) (mof s c) m' (vO cc)) (newOg (inst_of d) m' (vOg cc)) (oh cc) (fx cc)))
           (mV m') (mC m') (mH m') (mG m')
           (pcs s) (upd (tp s) c (Nat.max (tp s c) (S k)))
           (cm s)
           (lg s ++ [mkO (tm s) c k K u w (evC (inst_of d) (rg cc)) (evR (inst_of d) (rg cc))
                         (evQ s c (inst_of d) (rg cc) (mof s c) (vOg cc) (vO cc) u w)
                         (evQc (inst_of d) (rg cc) (vO cc) w) false])
           (upd (es s) (tm s) (Some (cc, pcs s c, tp s c, B))))
(* S3c (one rule, one step): the CAS at place j
   fixes its result b (cfix_ok); when its read half was performed (record o),
   a failure makes the record's register a failure (spurious failure, spec 0.1
   §8.6), and from then on its write half is nothing; nothing is performed,
   logged or timed. The result is the result when the CAS is reached (fxok). *)
| s0_cfix : forall s c j b (B : nat -> bool) o,
    let cc := cs s c in
    pcs s c <= j ->
    fx cc j = None ->
    cfix_ok p c cc (pcs s c) (tp s c) j b B o ->
    step0 p s (scfix0 (sflp s c o b) c j b B).

Inductive run0 (p : prog) : st -> Prop :=
| r00 : run0 p sinit
| rS0 : forall s s', run0 p s -> step0 p s s' -> run0 p s'.

(* ---------- places of tied pending accesses come in time order ---------- *)
Lemma placed_tied_order : forall p c cc pc r k1 k2 d1 d2 j1 j2 t1 t2, cellful p ->
  (forall k1 k2 t, oc cc k1 = Some t -> oc cc k2 = Some t -> k1 = k2) ->
  placed p c cc pc r k1 d1 j1 -> placed p c cc pc r k2 d2 j2 -> oc cc k1 = Some t1 -> oc cc k2 = Some t2 ->
  tied (inst_of d2) (inst_of d1) -> t1 < t2 ->
  (* the later place, if a CAS's read alone took it first, is no CAS that fails under r *)
  (forall v, htakenv p c cc pc r t1 j2 v -> cfailv (ins p c j2 r) r v = false) -> j1 < j2.
Proof.
  intros p c cc pc r k1 k2 d1 d2 j1 j2 t1 t2 Wc OI P1 P2 O1 O2 Ti Lt HX.
  destruct (Nat.lt_trichotomy j1 j2) as [L|[L|L]]; auto; exfalso.
  - subst j2. pose proof (placed_unique p c cc pc OI r j1 k1 k2 d1 d2 P1 P2). subst k2. rewrite O1 in O2. injection O2 as <-. lia.
  - destruct P1 as (Pk1 & t1' & O1' & F1). rewrite O1 in O1'. injection O1' as <-.
    destruct P2 as (Pk2 & t2' & O2' & F2). rewrite O2 in O2'. injection O2' as <-.
    pose proof (first_at_eof _ _ _ _ _ _ _ _ F2) as D2.
    assert (Tj : tied (ins p c j2 r) (inst_of d1)).
    { apply (proj2 (tied_eof_l _ _ _ _ D2)). exact Ti. }
    assert (NT : ~ taken p c cc pc r t1 j2).
    { intros (k3 & t3 & d3 & P3 & O3 & L3 & F3).
      assert (E : k3 = k2) by (apply (placed_unique p c cc pc OI r j2 k3 k2 d3 d2); [split; [auto|exists t3; auto]|split; [auto|exists t2; auto]]).
      subst k3. rewrite O2 in O3. injection O3 as <-. lia. }
    apply NT. apply (first_at_before _ _ _ _ _ _ _ _ F1 j2 (first_at_le _ _ _ _ _ _ _ _ F2) L (proj1 (eof_exec_tied _ _ _ _ _ Wc D2))); [|exact Tj].
    intros v X; exact (HX v X).
Qed.

(* ---------- no finished run is lost ---------- *)
(* a later access recorded at an earlier slot than a tied one still pending:
   an access, or a CAS's read alone *)
Definition Bad (p : prog) (s : st) : Prop :=
  exists c ke kd dd te td, c < length p /\
    ((exists de, pending (cs s c) (pcs s c) ke de /\ oc (cs s c) ke = Some te /\ tied (inst_of de) (inst_of dd)) \/
     (exists xs, pcs s c <= ke /\ oc (cs s c) ke = None /\ oh (cs s c) ke = Some te /\ ai (cs s c) ke = crd Plain xs /\
        tied (crd Plain xs) (inst_of dd))) /\
    pending (cs s c) (pcs s c) kd dd /\ ke < kd /\ oc (cs s c) kd = Some td /\ td <= te.

(* times of recorded slots are in the past *)
Definition TI (s : st) : Prop := forall c k t, oc (cs s c) k = Some t -> t < tm s.

Lemma step0_TI : forall p s t, TI s -> step0 p s t -> TI t.
Proof.
  intros p s t H St c k u O. inversion St; subst; repeat match goal with x := _ |- _ => subst x end.
  all: try (rewrite oc_cx, oc_flp in O; unfold scfix0; cbn [tm]; rewrite tm_flp; apply H in O; exact O).
  all: simpl in *; unfold upd in O; destruct (Nat.eqb_spec c c0); [subst c0; simpl in O|apply H in O; lia].
  all: try (apply H in O; lia).
  all: match type of O with
       | (if Nat.eqb ?k ?k0 then _ else _) = _ => destruct (Nat.eqb_spec k k0); [injection O as <-; lia|apply H in O; lia]
       end.
Qed.

Lemma run0_TI : forall p s, run0 p s -> TI s.
Proof.
  intros p s R. induction R as [|s t R IH St].
  - intros c k u O. simpl in O. discriminate.
  - apply (step0_TI p s t IH St).
Qed.

(* the tie of a CAS read alone is the tie of the CAS *)
Lemma tied_cas_same : forall a b x, is_cas a = true -> is_cas b = true -> icells a = icells b -> gop a = gop b ->
  tied a x -> tied b x.
Proof.
  intros [| |ma xa ca ea na| |] [| |mb xb cb eb nb| |] x A B E Eg T; simpl in A, B; try discriminate.
  destruct T as [(y & Y1 & Y2)|[G|[G|[(_ & G')|[(_ & G')|[([G|G] & _)|[([G|G] & _)|G]]]]]]];
    try discriminate.
  - apply (tied_cell _ _ y); [rewrite <- E; exact Y1|exact Y2].
  - apply tied_gop_r. exact G.
  - destruct G' as [-> | ->]; [apply tied_ld_l; [reflexivity|left; reflexivity]|apply tied_ld_l; [reflexivity|right; reflexivity]].
  - destruct G' as [-> | ->]; [apply tied_st_s; [reflexivity|left; reflexivity]|apply tied_st_s; [reflexivity|right; reflexivity]].
Qed.

Ltac keep_half Ke := let de := fresh "de" in let E1 := fresh "E1" in let E2 := fresh "E2" in let E3 := fresh "E3" in
  let Oe := fresh "Oe" in let Ti := fresh "Ti" in let xs0 := fresh "xs0" in let Lp := fresh "Lp" in
  let Oh := fresh "Oh" in let Ae := fresh "Ae" in
  destruct Ke as [(de & (E1 & E2 & E3) & Oe & Ti)|(xs0 & Lp & Oe & Oh & Ae & Ti)];
  [left; exists de; repeat split; auto; lia|right; exists xs0; repeat split; auto; lia].

Lemma bad_step0 : forall p s t, TI s -> Bad p s -> step0 p s t -> Bad p t.
Proof.
  intros p s t TIs (c & ke & kd & dd & te & td & Lc & Ke & (D1 & D2 & D3) & Lk & Od & Lt) St.
  assert (Lpk : pcs s c <= ke) by (destruct Ke as [(de & (E1 & _) & _)|(xs0 & Lp & _)]; auto).
  inversion St; subst; repeat match goal with x := _ |- _ => subst x end.
  - (* in order *)
    exists c, ke, kd, dd, te, td. unfold sord, evs, pending; simpl. unfold upd. split; [auto|].
    destruct (Nat.eqb_spec c c0) as [<-|N]; simpl.
    + destruct (Nat.eqb_spec kd (pcs s c)); [subst; congruence|].
      assert (Nke : ke <> pcs s c).
      { intros X. rewrite X in *. destruct Ke as [(de & _ & Oe & _)|(xs0 & _ & _ & Oh & _)]; congruence. }
      destruct (Nat.eqb_spec ke (pcs s c)); [lia|].
      split; [keep_half Ke|]. repeat split; auto; lia.
    + split; [destruct Ke as [(de & Pe & Oe & Ti)|(xs0 & Ke)]; [left; exists de|right; exists xs0]; auto|].
      repeat split; auto.
  - (* passing a non-executing instruction *)
    exists c, ke, kd, dd, te, td. unfold pending; simpl. unfold upd. split; [auto|].
    destruct (Nat.eqb_spec c c0) as [<-|N]; simpl.
    + destruct (Nat.eqb_spec kd (pcs s c)); [subst; congruence|].
      assert (Nke : ke <> pcs s c).
      { intros X. rewrite X in *. destruct Ke as [(de & _ & Oe & _)|(xs0 & _ & _ & Oh & Ae & Ti)]; [congruence|].
        (* a CAS that failed after its read: what is tied to it happened after its read *)
        assert (Pd : pending (cs s c) (pcs s c) kd dd) by (repeat split; auto; lia).
        revert H2 H4 Ti. generalize (ins p c (pcs s c) (rg (cs s c))). intros i0 H2 H4 Ti.
        assert (Ei : eofR i0 (rg (cs s c)) = Some (Plain, xs0)) by (rewrite H2 by congruence; rewrite Ae; reflexivity).
        destruct i0 as [| |mi xi ci ei ni| |]; simpl in Ei; try discriminate.
        destruct (ci (rg (cs s c))); [|discriminate]. injection Ei as -> ->.
        apply (tied_cas_same (crd Plain xs0) (ICas Plain xs0 ci ei ni)) in Ti; try reflexivity.
        pose proof (proj1 (H4 te Oh) kd dd td Pd ltac:(lia) Od Ti). lia. }
      destruct (Nat.eqb_spec ke (pcs s c)); [lia|].
      split; [keep_half Ke|]. repeat split; auto; lia.
    + split; [destruct Ke as [(de & Pe & Oe & Ti)|(xs0 & Ke)]; [left; exists de|right; exists xs0]; auto|].
      repeat split; auto.
  - (* early *)
    exists c, ke, kd, dd, te, td. unfold searly, set_es, searly0, evs, pending; simpl. unfold upd. split; [auto|].
    destruct (Nat.eqb_spec c c0) as [<-|N]; simpl.
    + destruct (Nat.eqb_spec kd k); [subst; congruence|].
      destruct (Nat.eqb_spec ke k); [subst; destruct Ke as [(de & _ & Oe & _)|(xs0 & _ & _ & Oh & _)]; congruence|].
      split; [keep_half Ke|]. repeat split; auto.
    + split; [destruct Ke as [(de & Pe & Oe & Ti)|(xs0 & Ke)]; [left; exists de|right; exists xs0]; auto|].
      repeat split; auto.
  - (* reaching an early access: not the later one of the pair *)
    destruct (Nat.eq_dec c c0) as [<-|N].
    + assert (Ne : ke <> pcs s c).
      { intros X. rewrite X in *. destruct Ke as [(de & (E1 & E2 & E3) & Oe & Ti)|(xs0 & _ & Oe & _)]; [|congruence].
        rewrite H0 in E3. apply inst_of_inj in E3. subst d.
        assert (Pd : pending (cs s c) (pcs s c) kd dd) by (repeat split; auto; lia).
        pose proof (H3 kd dd te td Pd ltac:(lia) Oe Od Ti). lia. }
      exists c, ke, kd, dd, te, td. unfold smatch, pending; simpl. unfold upd. rewrite Nat.eqb_refl. simpl. split; [auto|].
      destruct (Nat.eqb_spec ke (pcs s c)); [lia|]. destruct (Nat.eqb_spec kd (pcs s c)); [lia|].
      split; [keep_half Ke|]. repeat split; auto; lia.
    + exists c, ke, kd, dd, te, td. unfold smatch, pending; simpl. unfold upd. split; [auto|].
      destruct (Nat.eqb_spec c c0); [congruence|].
      split; [destruct Ke as [(de & Pe & Oe & Ti)|(xs0 & Ke)]; [left; exists de|right; exists xs0]; auto|].
      repeat split; auto.
  - (* a CAS's read alone *)
    exists c, ke, kd, dd, te, td. unfold sread, pending; simpl. unfold upd. split; [auto|].
    destruct (Nat.eqb_spec c c0) as [<-|N]; simpl.
    + destruct (Nat.eqb_spec kd k); [subst; congruence|].
      destruct (Nat.eqb_spec ke k); [subst; destruct Ke as [(de & _ & Oe & _)|(xs0 & _ & _ & Oh & _)]; congruence|].
      split; [keep_half Ke|]. repeat split; auto.
    + split; [destruct Ke as [(de & Pe & Oe & Ti)|(xs0 & Ke)]; [left; exists de|right; exists xs0]; auto|].
      repeat split; auto.
  - (* the write of a CAS whose read happened alone, in order: not with a tied pending access *)
    destruct (Nat.eq_dec c c0) as [<-|N].
    + assert (Ne : ke <> pcs s c).
      { intros X. rewrite X in *. destruct Ke as [(de & _ & Oe & _)|(xs0 & _ & _ & Oh & Ae & Ti)]; [congruence|].
        assert (Pd : pending (cs s c) (pcs s c) kd dd) by (repeat split; auto; lia).
        match goal with
        | Hb : forall k' d, pending _ _ k' d -> ~ tied ?i (inst_of d), Ci : is_cas ?i = true,
          Ef : eofR ?i _ = eofR (ai _ _) _ |- _ =>
          apply (Hb kd dd Pd); rewrite Ae in Ef; destruct (eofR_half _ _ _ Ef) as [Ic _];
          apply (tied_cas_same (crd Plain xs0) i (inst_of dd) eq_refl Ci (eq_sym Ic) ltac:(destruct i as [| |mi xi ci ei ni| |]; simpl in Ef; try discriminate; destruct (ci (rg (cs s c))); [injection Ef as -> _; reflexivity|discriminate]) Ti)
        end. }
      exists c, ke, kd, dd, te, td. unfold pending; simpl. unfold upd. rewrite Nat.eqb_refl. simpl. split; [auto|].
      destruct (Nat.eqb_spec ke (pcs s c)); [lia|]. destruct (Nat.eqb_spec kd (pcs s c)); [subst; congruence|].
      split; [keep_half Ke|]. repeat split; auto; lia.
    + exists c, ke, kd, dd, te, td. unfold pending; simpl. unfold upd. split; [auto|].
      destruct (Nat.eqb_spec c c0); [congruence|].
      split; [destruct Ke as [(de & Pe & Oe & Ti)|(xs0 & Ke)]; [left; exists de|right; exists xs0]; auto|].
      repeat split; auto.
  - (* the write of a CAS whose read happened alone, early *)
    destruct (Nat.eq_dec c c0) as [<-|N].
    + destruct (Nat.eq_dec ke k) as [->|Nk].
      * destruct Ke as [(de & _ & Oe & _)|(xs0 & Lp & Oe & Oh & Ae & Ti)]; [congruence|].
        rewrite Ae in H2. injection H2 as <-.
        exists c, k, kd, dd, (tm s), td. unfold pending; simpl. unfold upd. rewrite !Nat.eqb_refl. simpl. split; [auto|].
        destruct (Nat.eqb_spec kd k); [subst; congruence|]. rewrite Nat.eqb_refl.
        split; [left; exists (DCas Plain xs0 ev nv); split; [split; [exact Lp|split; [discriminate|reflexivity]]|split; [reflexivity|]]|].
        { apply (tied_cas_same (crd Plain xs0) (inst_of (DCas Plain xs0 ev nv)) (inst_of dd) eq_refl eq_refl eq_refl eq_refl Ti). }
        split; [repeat split; auto|]. split; [lia|]. split; [auto|]. pose proof (TIs c kd td Od). lia.
      * exists c, ke, kd, dd, te, td. unfold pending; simpl. unfold upd. rewrite Nat.eqb_refl. simpl. split; [auto|].
        destruct (Nat.eqb_spec kd k); [subst; congruence|]. destruct (Nat.eqb_spec ke k); [lia|].
        split; [keep_half Ke|]. repeat split; auto.
    + exists c, ke, kd, dd, te, td. unfold pending; simpl. unfold upd. split; [auto|].
      destruct (Nat.eqb_spec c c0); [congruence|].
      split; [destruct Ke as [(de & Pe & Oe & Ti)|(xs0 & Ke)]; [left; exists de|right; exists xs0]; auto|].
      repeat split; auto.
  - (* S3c: a result fixed: no record, place or pending access changes *)
    exists c, ke, kd, dd, te, td. unfold pending in *.
    rewrite !oc_cx, !oh_cx, !ai_cx, !oc_flp, !oh_flp, !ai_flp. unfold scfix0; cbn [pcs]; rewrite pcs_flp.
    split; [auto|]. split; [exact Ke|]. split; [exact (conj D1 (conj D2 D3))|]. auto.
Qed.

Lemma bad_run0 : forall p s t, run0 p s -> Bad p s -> step0 p s t -> Bad p t.
Proof. intros p s t R. apply bad_step0. apply (run0_TI p s R). Qed.

Lemma done_not_bad : forall p s, done p s -> ~ Bad p s.
Proof.
  intros p s (n & _ & Cp) (c & ke & kd & dd & te & td & Lc & _ & (D1 & D2 & D3) & _).
  destruct (Cp c Lc) as [_ Z]. apply D2. apply Z. exact D1.
Qed.

(* a step of step0 into a state that is not bad is a step of the model *)
Lemma step0_step : forall p s t, TI s -> step0 p s t -> ~ Bad p t -> step p s t.
Proof.
  intros p s t Ts St Nb. inversion St; subst; repeat match goal with x := _ |- _ => subst x end.
  - eapply s_ord; eauto.
  - eapply s_skip; eauto.
  - eapply s_early; eauto. intros k' d' P Ti.
    destruct (Nat.lt_ge_cases k' k) as [L|L]; auto. exfalso. apply Nb.
    destruct P as (P1 & P2 & P3). destruct (oc (cs s c) k') as [t'|] eqn:O'; [|congruence].
    assert (Nk : k' <> k) by (intros ->; congruence).
    exists c, k, k', d', (tm s), t'. split; [apply (early_len p c (cs s c) (pcs s c) (tp s c) (tm s) d u B); auto|].
    unfold searly, set_es, searly0, evs, pending; simpl. rewrite upd_eq. simpl. unfold upd.
    rewrite Nat.eqb_refl. destruct (Nat.eqb_spec k' k); [congruence|].
    split; [left; exists d; split; [split; [lia|split; [discriminate|reflexivity]]|split; [reflexivity|exact Ti]]|].
    split; [split; [exact P1|split; [rewrite O'; discriminate|exact P3]]|].
    split; [lia|]. split; [exact O'|]. pose proof (Ts c k' t' O'); lia.
  - eapply s_match; eauto.
  - destruct m. eapply s_cread; eauto. intros k' d' P Ti.
    destruct (Nat.lt_ge_cases k' k) as [L|L]; auto. exfalso. apply Nb.
    destruct P as (P1 & P2 & P3). destruct (oc (cs s c) k') as [t'|] eqn:O'; [|congruence].
    assert (Nk : k' <> k) by (intros ->; congruence).
    exists c, k, k', d', (tm s), t'. split; [eapply earlyR_len; eauto|].
    unfold sread, pending; simpl. rewrite upd_eq. simpl. unfold upd.
    rewrite !Nat.eqb_refl. destruct (Nat.eqb_spec k' k); [congruence|].
    split; [right; exists xs; repeat split; auto|].
    split; [split; [exact P1|split; [rewrite O'; discriminate|exact P3]]|].
    split; [lia|]. split; [exact O'|]. pose proof (Ts c k' t' O'); lia.
  - eapply s_cw; eauto.
  - eapply s_cwe; eauto. intros k' d' P Ti.
    destruct (Nat.lt_ge_cases k' k) as [L|L]; auto. exfalso. apply Nb.
    destruct P as (P1 & P2 & P3). destruct (oc (cs s c) k') as [t'|] eqn:O'; [|congruence].
    assert (Nk : k' <> k) by (intros ->; congruence).
    exists c, k, k', d', (tm s), t'. split; [eapply earlyW_len; eauto|].
    unfold searly, set_es, searly0, evs, pending; simpl. rewrite upd_eq. simpl. unfold upd.
    rewrite Nat.eqb_refl. destruct (Nat.eqb_spec k' k); [congruence|].
    split; [left; exists (DCas Plain xs ev nv); split; [split; [lia|split; [discriminate|reflexivity]]|split; [reflexivity|exact Ti]]|].
    split; [split; [exact P1|split; [rewrite O'; discriminate|exact P3]]|].
    split; [lia|]. split; [exact O'|]. pose proof (Ts c k' t' O'); lia.
  - eapply s_cfix; eauto.
Qed.

Lemma run0_run : forall p s, run0 p s -> ~ Bad p s -> run p s.
Proof.
  intros p. apply (avoid_run st (step0 p) (run0 p) (Bad p) (run p) sinit).
  - intros Q Q0 QS s R. induction R as [|s t R IH St]; [exact Q0|]. apply (QS s t R IH St).
  - apply bad_run0.
  - constructor.
  - intros s t R Rs St Nb. apply rS with s; [exact Rs|]. apply (step0_step p s t (run0_TI p s R) St Nb).
Qed.

(* every finished run without the condition is a run of the model *)
Theorem run0_done_run : forall p s, run0 p s -> done p s -> run p s.
Proof. intros p s R D. apply (run0_run p s R). apply done_not_bad. exact D. Qed.

(* and the model's runs are runs without the condition *)
Lemma step_step0 : forall p s t, step p s t -> step0 p s t.
Proof.
  intros p s t St. inversion St; subst; repeat match goal with x := _ |- _ => subst x end.
  - eapply s0_ord; eauto.
  - eapply s0_skip; eauto.
  - eapply s0_early; eauto.
  - eapply s0_match; eauto.
  - eapply s0_cread; eauto.
  - eapply s0_cw; eauto.
  - eapply s0_cwe; eauto.
  - eapply s0_cfix; eauto.
Qed.

Theorem run_run0 : forall p s, run p s -> run0 p s.
Proof.
  intros p s R. induction R as [|s t R IH St]; [constructor|]. apply rS0 with s; auto. apply step_step0. exact St.
Qed.
