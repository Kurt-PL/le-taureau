(* Model2: the current step relation has the guarantees of M2Iface. This
   file is what a rule change re-proves. *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO M2Oota M2Cont M2Equiv M2Snap M2SC M2SCx
  M2Trace M2Mono M2PComp M2PNeg M2PSync M2PCore M2Ev M2Timeline2 M2Iface.

Section I.
Variable p : prog.

Lemma i_run : forall s, reach (step p) s -> run p s.
Proof. intros s R. apply reach_run. exact R. Qed.

Lemma i_birth : wf p -> forall f n, gtrace (step p) f n -> forall c k, k < pcs (f n) c ->
  exists ih, ih < n /\ pcs (f ih) c = k /\ M2PComp.bt (f n) c k <= tm (f ih).
Proof.
  intros W f n T c k Lk.
  destruct (pass_birth p f n T n c k (le_n n) Lk) as (ih & Lih & Pih & PSih & Cs).
  assert (Rsb : run p (f ih)) by (apply (tr_run p f n T); lia).
  pose proof (Inv1_run p (f ih) Rsb) as Isb.
  assert (X : Ext (f ih) (f n)) by (apply (tr_ext p f n T); lia).
  exists ih. split; [exact Lih|]. split; [exact Pih|].
  destruct Cs as [(i0 & m' & a & K & u & w & _ & Ho & _ & _ & _ & _ & _ & _ & E)|[(d & Ho & _ & _ & _ & _ & _ & E)|(Kx & Ko & Kh & Kv & Kf & Kd & E)]].
  - assert (O1 : oc (cs (f (S ih)) c) k = Some (tm (f ih))).
    { rewrite E. unfold sord, evs. simpl. rewrite upd_eq'. simpl. rewrite Pih, upd_eq'. reflexivity. }
    assert (X1 : Ext (f (S ih)) (f n)) by (apply (tr_ext p f n T); lia).
    pose proof (x_oc _ _ X1 c k _ O1) as O2. unfold M2PComp.bt, tmo. rewrite O2. lia.
  - cbv zeta in Ho. destruct (oc (cs (f ih) c) k) as [t0|] eqn:O0; [|congruence].
    pose proof (oc_lt_tm p (f ih) c k t0 Isb O0) as Lt0. pose proof (x_oc _ _ X c k t0 O0) as O2.
    unfold M2PComp.bt, tmo. rewrite O2. lia.
  - (* passed without happening: it never happens; a CAS that failed keeps its read's time *)
    cbv zeta in Ko. try rewrite Pih in Ko.
    assert (O1 : oc (cs (f (S ih)) c) k = None) by (rewrite E, (oc_skip p (f ih) c); exact Ko).
    assert (P1 : k < pcs (f (S ih)) c) by (rewrite E, (pcs_skip p (f ih) c), Nat.eqb_refl; lia).
    assert (X1 : Ext (f (S ih)) (f n)) by (apply (tr_ext p f n T); lia).
    pose proof (x_ocp _ _ X1 c k P1 O1) as O2. unfold M2PComp.bt, tmo. rewrite O2.
    destruct (oh (cs (f (S ih)) c) k) as [t0|] eqn:Oh1.
    + rewrite (x_oh _ _ X1 c k t0 Oh1). rewrite E, (oh_skip p (f ih) c) in Oh1.
      pose proof (oh_lt_tm p (f ih) c k t0 Isb Oh1). lia.
    + rewrite (x_ohp _ _ X1 c k P1 Oh1). lia.
Qed.

Lemma i_pending_cells : wf p -> forall f n, gtrace (step p) f n -> forall ih cu ku, ih <= n -> pcs (f ih) cu <= ku ->
  oc (cs (f ih) cu) ku <> None -> icells (ai (cs (f ih) cu) ku) = icells (ai (cs (f n) cu) ku).
Proof.
  intros W f n T ih cu ku L P O.
  assert (Ri : run p (f ih)) by (apply (tr_run p f n T); lia).
  assert (Rn : run p (f n)) by (apply (tr_run p f n T); lia).
  destruct (i_pend p (f ih) (Inv1_run p (f ih) Ri) cu ku P O) as ((d & Ad & _) & _).
  destruct (pend_fate p f n T ih n cu ku d L (le_n n) W O P Ad) as [(_ & An)|(Ln & Dn)].
  - rewrite Ad, An. reflexivity.
  - destruct (proj1 (i_cmA p (f n) (Inv1_run p (f n) Rn) cu ku) Ln) as (tau & Tc).
    rewrite (proj2 (i_set p (f n) (Inv1_run p (f n) Rn) cu ku tau Tc)). rewrite Ad.
    rewrite (eof_icells _ _ _ Dn). reflexivity.
Qed.

Lemma i_pending_source : wf p -> cellful p -> forall f nb, gtrace (step p) f nb -> evok (f nb) ->
  forall lb gb, base p (f nb) lb gb ->
  forall c dh x y EY, dof (ins p c (sp gb c) (sr gb c)) (sr gb c) = Some dh -> In x (icells (inst_of dh)) ->
  ent (f nb) y = Some EY -> ew EY = true -> In x (icells (einstr p (f nb) EY)) -> ec EY <> c ->
  oc (cs (f nb) (ec EY)) (ek EY) = Some y -> pcs (f nb) (ec EY) <= ek EY ->
  RACY p.
Proof.
  intros W Wc f nb T EVb lb gb (Bsr & Bsp & Brg & Bgo & Bco) c dh x y EY Dgb Ixd AY WY IY Nc OY Gp.
  destruct (early_of_pending p f nb T nb (ec EY) (ek EY) y (le_n nb) Gp OY) as (iy & dy & By & uy & Eay & Liy & Tiy).
  destruct (pend_meet p W Wc f nb T lb gb Bsr Bsp Brg (tm (f nb)) lb gb c dh x (ec EY) (ek EY) iy dy By uy EY
              (core p W Wc f nb T lb gb Bsr Bsp Brg Bgo Bco EVb (tm (f iy))) (CONS_base p f nb lb gb Bsp Brg)
              Dgb Nc Ixd Eay Gp ltac:(rewrite Tiy; pose proof (oc_lt_tm p (f nb) _ _ _ (Inv1_run p (f nb) (tr_run p f nb T nb (le_n nb))) OY); lia)
              ltac:(rewrite Tiy; exact AY) WY IY) as (l' & g' & H' & Xr).
  - intros q e Lq Q. exfalso. assert (q < length lb) by (apply nth_error_Some; congruence). lia.
  - exists l', g'. auto.
Qed.

Theorem m2_guarantees : M2Guarantees p (step p).
Proof.
  constructor.
  - intros s R. apply Inv1_run. apply i_run. exact R.
  - intros s R. apply (proj2 (Inv2_run p s (i_run s R))).
  - intros s R. apply (ia3 p s (Inv_run p s (i_run s R))).
  - intros s R. apply (iaoO p s (InvO_run p s (i_run s R))).
  - intros s t R St. apply (Ext_step p s t (i_run s R) St).
  - intros s t R St E. apply (evok_step p s t (i_run s R) St E).
  - apply tl2ok_iff_evok.
  - intros W V V0 Cl s R. apply (no_thin_air p V W V0 Cl s (i_run s R)).
  - intros s R c. apply (slot0_oc p s (i_run s R)).
  - intros CF s R. apply (cf_noh p CF s (i_run s R)).
  - exact i_birth.
  - exact i_pending_cells.
  - exact i_pending_source.
Qed.

End I.

Instance m2model : Model := {| STEP := step; GG := m2_guarantees |}.
