(* Part 59: J goes along every step of an A run that satisfies RaceStep (J_step).
   - an event step (in order, early, a CAS's read alone): the acting context's views are the
     effect's, G is the effect's (J_evs);
   - a step that logs nothing (reaching an early access, passing a non-executing instruction,
     fixing a CAS's result): no view changes (J_same).
   NF_no_early: in NF a context has no early access (the guard() at its next slot, or the one
   after its fenced next slot, is tied to it and not taken). *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO.
Require Import M2WBReg M2WBRel M2WBSim M2DQWBPatch M2DQWB.
Require Import M2DQWBK1 M2DQWBK3 M2DQWBK15 M2DQWBK20 M2DQWBK22 M2DQWBK29 M2DQWBK32 M2DQWBK33 M2DQWBK40 M2DQWBK57 M2DQWBK58.
Require Import M2DQ M2DQInv M2DQIface M2DQWBQ M2DQWBQb M2DQWBK1Q M2DQShim.

Section S.
Variable p : prog.
Hypothesis W : wf p.

Lemma NF_no_early : forall s c N T d u B, NF p s c -> early_ok p c (cs s c) (pcs s c) N T d u B -> False.
Proof.
  intros s c N T d u B Nf Eo.
  destruct (Eo (fun _ _ => 0)) as (j & Lj & F & _). cbv zeta in F.
  set (r := creg p c (cs s c) (pcs s c) N (bor (bd (cs s c)) B) (fun _ _ => 0)) in F.
  unfold first_at in F.
  assert (G : forall j', pcs s c <= j' -> j' < j -> ins p c j' r = IFn FFull -> False).
  { intros j' L1 L2 E. assert (Tk : taken p c (cs s c) (pcs s c) r T j').
    { apply (plc_before _ _ _ _ _ _ _ _ F j' L1 L2); rewrite E; [reflexivity|intros v _; reflexivity|right; left; reflexivity]. }
    destruct (taken_dof _ _ _ _ _ _ _ Tk) as (d0 & D0). rewrite E in D0. discriminate. }
  destruct Nf as [N1|((_ & Fa) & _)].
  - exact (G (pcs s c) (le_n _) Lj (N1 r)).
  - destruct (Nat.eq_dec j (S (pcs s c))) as [Ej|Nj].
    + pose proof (plc_tat _ _ _ _ _ _ _ _ F) as D. rewrite Ej, (proj2 (Fa r)) in D. discriminate.
    + exact (G (S (pcs s c)) ltac:(lia) ltac:(lia) (proj2 (Fa r))).
Qed.

Lemma eff_takes : forall t i r m m' a K u w x y, eff t i r m m' a K u w -> u x = Some y -> In y (ids (mH m x)).
Proof.
  intros t i r m m' a K u w x y H U. inversion H; subst; try discriminate.
  all: match goal with Tk : takes _ _ _ |- _ => destruct Tk as [T1 T2] end.
  all: destruct (in_dec Nat.eq_dec x (dd xs)) as [Ix|Nx]; [pose proof (T1 x Ix) as Z; rewrite U in Z; exact Z|rewrite (T2 x Nx) in U; discriminate].
Qed.

Let G1' := M2DQWBK58.G1'.

Lemma ffull_dec' : forall i : instr, i = IFn FFull \/ i <> IFn FFull.
Proof. intros [| | |[]|]; first [left; reflexivity | right; discriminate]. Qed.

(* ---------- an event step ---------- *)
Section Evs.
Variables (s s' : st) (c : nat) (i : instr) (m' : mst) (a0 : val) (K : view) (u : cell -> option nat) (w : bool) (e0 : oev).
Hypothesis R : run p s.
Hypothesis St : step p s s'.
Hypothesis Js : J p s.
Hypothesis RS : RaceStep p s s'.
Hypothesis Cs : forall c', c' <> c -> cs s' c' = cs s c'.
Hypothesis Pc : forall c', c' <> c -> pcs s' c' = pcs s c'.
Hypothesis VP : vP (cs s' c) = mP m'.
Hypothesis VA : vA (cs s' c) = mA m'.
Hypothesis VO : vO (cs s' c) = newO s c i (mof s c) m' (vO (cs s c)).
Hypothesis VOg : vOg (cs s' c) = newOg i m' (vOg (cs s c)).
Hypothesis VG : vG s' = mG m'.
Hypothesis Lg : lg s' = lg s ++ [e0].
Hypothesis Ec : ec e0 = c.
Hypothesis Ew : ew e0 = w.
Hypothesis Eu : erf e0 = u.
Hypothesis He : eff (tm s) i (rg (cs s c)) (mof s c) m' a0 K u w.
Hypothesis HL : i = IFn FLl -> ~ NF p s c.

Let R' : run p s' := rS p s s' R St.
Let I := Inv1_run p s R.
Let J2 := proj2 (Inv2_run p s R).
Let J2' := proj2 (Inv2_run p s' R').
Let SI := self_image p G1' s W R.
Let Kr := proj2 SI.
Let Km := runWB_KM p s (Q_in_WB p s R).

Lemma E0 : ent s' (tm s) = Some e0.
Proof. unfold ent. rewrite Lg, nth_error_app_last, (i_tm p s I), Nat.ltb_irrefl, Nat.eqb_refl. reflexivity. Qed.

Lemma ent_old : forall t, t < tm s -> ent s' t = ent s t.
Proof. intros t L. unfold ent. rewrite Lg, nth_error_app1; [reflexivity|rewrite <- (i_tm p s I); exact L]. Qed.

Lemma own_new : forall c' z, ownw s' c' z -> ownw s c' z \/ (z = tm s /\ c' = c /\ w = true).
Proof.
  intros c' z (e & E & C & Wz). unfold ownw. rewrite Lg, nth_error_app_last, <- (i_tm p s I) in E.
  destruct (Nat.ltb_spec z (tm s)) as [L|L]; [left; exists e; auto|].
  destruct (Nat.eqb_spec z (tm s)) as [->|N]; [|discriminate]. injection E as <-. right. split; [reflexivity|]. split; congruence.
Qed.

Lemma own_old : forall c' z, ownw s c' z -> ownw s' c' z.
Proof.
  intros c' z (e & E & C & Wz). exists e. split; [|auto]. rewrite Lg. rewrite nth_error_app1; [exact E|].
  apply nth_error_Some. congruence.
Qed.

Lemma src_ent : forall x y, u x = Some y -> exists ey, ent s y = Some ey /\ ew ey = true /\ y < tm s.
Proof.
  intros x y U. rewrite <- Eu in U. destruct (j_rf p s' J2' (tm s) e0 x y E0 U) as (Ly & (ey & Ey & Wy) & _).
  exists ey. rewrite (ent_old y Ly) in Ey. auto.
Qed.

Lemma Og_post : forall q, vOg (cs s c) q -> vOg (cs s' c) q.
Proof. intros q Q. rewrite VOg. apply (newOg_grow _ _ _ _ _ _ _ _ _ _ He); [|exact Q]. intros z Z. exact (proj2 (Km c) z Z). Qed.

Lemma views_fresh : forall c' z, (vP (cs s c') z \/ vA (cs s c') z \/ vG s z) -> z < tm s.
Proof. intros c' z Z. apply (isw_lt p s z I). apply (j_views p s J2 c'). tauto. Qed.

Lemma ok_old : forall c0 z, OK p s c0 z -> (vP (cs s c0) z \/ vA (cs s c0) z \/ vG s z) -> OK p s' c0 z.
Proof. intros c0 z Ok Z. exact (OK_step p W s s' R St c0 z Ok Z). Qed.

Theorem J_evs : J p s'.
Proof.
  constructor.
  - (* j1 *)
    intros c0 z Nz Kz.
    assert (Nz0 : ~ ownw s c0 z) by (intros O; exact (Nz (own_old c0 z O))).
    destruct (Nat.eq_dec c0 c) as [->|N].
    + destruct (ffull_dec' i) as [Fi|Fi].
      * left. rewrite VOg, Fi. cbn [newOg]. rewrite VP, VA in Kz. destruct Kz as [Z|Z]; [exact Z|].
        rewrite Fi in He. exact (proj1 (proj2 ((proj1 (proj2 (proj2 (proj2 (eff_PA _ _ _ _ _ _ _ _ _ z He))))) eq_refl)) z Z).
      * destruct (eff_PA _ _ _ _ _ _ _ _ _ z He) as (EP & EA & _).
        rewrite VP, VA in Kz.
        assert (Src : forall x y, u x = Some y -> (z = y \/ wc s y z) -> OK p s' c z).
        { intros x y U Z. destruct (src_ent x y U) as (ey & Ey & Wy & _).
          pose proof (eff_takes _ _ _ _ _ _ _ _ _ x y He U) as Iy. cbn [mof mH] in Iy.
          pose proof (learn_ok p W s s' R St Js RS e0 x y ey z E0 ltac:(rewrite Eu; exact U) Ey Wy Iy Z) as L.
          rewrite Ec in L. exact (L Nz0 Og_post). }
        destruct Kz as [Z|Z].
        -- destruct (EP Z) as [Zp|[Za|[(F & _)|[(x & U)|(Wt & ->)]]]].
           ++ exact (ok_old c z (j1 p s Js c z Nz0 (or_introl Zp)) (or_introl Zp)).
           ++ exact (ok_old c z (j1 p s Js c z Nz0 (or_intror Za)) (or_intror (or_introl Za))).
           ++ contradiction.
           ++ exact (Src x z U (or_introl eq_refl)).
           ++ exfalso. apply Nz. exists e0. split; [rewrite Lg, nth_error_app_last, <- (i_tm p s I), Nat.ltb_irrefl, Nat.eqb_refl; reflexivity|]. split; congruence.
        -- destruct (EA Z) as [Za|(x & y & U & Zc)].
           ++ exact (ok_old c z (j1 p s Js c z Nz0 (or_intror Za)) (or_intror (or_introl Za))).
           ++ apply (Src x y U). destruct Zc as [Zc|Zc]; [right; exact Zc|left; exact Zc].
    + rewrite (Cs c0 N) in Kz. apply ok_old; [exact (j1 p s Js c0 z Nz0 Kz)|tauto].
  - (* j2 *)
    intros c0 z Oz Kz.
    destruct (own_new c0 z Oz) as [Oz0|(-> & -> & Wt)].
    2:{ exfalso. destruct Kz as [Zg|(d & Nd & Zd)].
        - rewrite VG in Zg. destruct (eff_PA _ _ _ _ _ _ _ _ _ (tm s) He) as (_ & _ & EG & EF & ES).
          destruct (EG Zg) as [Z|[(F & _)|(F & _)]].
          + pose proof (views_fresh c (tm s) (or_intror (or_intror Z))). lia.
          + rewrite (proj1 (EF F)) in Wt. discriminate.
          + rewrite (ES F) in Wt. discriminate.
        - rewrite (Cs d Nd) in Zd. pose proof (views_fresh d (tm s) ltac:(tauto)). lia. }
    assert (Pz : vP (cs s c0) z) by exact (w_OW False G1' sw0 s s Kr c0 z Oz0).
    assert (OKs : OK p s c0 z -> OK p s' c0 z) by (intros Ok; exact (ok_old c0 z Ok (or_introl Pz))).
    assert (Lz : z < tm s) by exact (views_fresh c0 z (or_introl Pz)).
    destruct Kz as [Zg|(d & Nd & Zd)].
    + rewrite VG in Zg. destruct (eff_PA _ _ _ _ _ _ _ _ _ z He) as (_ & _ & EG & EF & _).
      destruct (EG Zg) as [Z|[(F & Zpa)|(F & Zw)]].
      * apply OKs. apply (j2 p s Js c0 z Oz0). left. exact Z.
      * destruct (Nat.eq_dec c0 c) as [->|N].
        -- left. rewrite VOg, F. cbn [newOg]. rewrite F in He. apply (eff_full_P _ _ _ _ _ _ _ _ _ He). tauto.
        -- apply OKs. apply (j2 p s Js c0 z Oz0). right. exists c. split; [congruence|exact Zpa].
      * assert (Cc : c = c0) by exact (ownw_uniq s c c0 z Zw Oz0). subst c0.
        left. rewrite VOg, F. cbn [newOg]. right. exact Zg.
    + destruct (Nat.eq_dec d c) as [->|Ndc].
      * destruct (eff_PA _ _ _ _ _ _ _ _ _ z He) as (EP & EA & _).
        rewrite VP, VA in Zd.
        assert (Src : forall x y, u x = Some y -> (z = y \/ wc s y z) -> OK p s' c0 z).
        { intros x y U Z. destruct (src_ent x y U) as (ey & Ey & Wy & _).
          pose proof (eff_takes _ _ _ _ _ _ _ _ _ x y He U) as Iy. cbn [mof mH] in Iy.
          apply (learn_own p W s s' R St Js RS e0 x y ey z c0 E0 ltac:(rewrite Eu; exact U) Ey Wy Iy Z Oz0);
            [rewrite Ec; intros E; exact (Nd (eq_sym E))|exact (Cs c0 (fun E => Nd (eq_sym E)))|exact (Pc c0 (fun E => Nd (eq_sym E)))]. }
        destruct Zd as [Z|Z].
        -- destruct (EP Z) as [Zp|[Za|[(F & Zg)|[(x & U)|(Wt & Et)]]]].
           ++ apply OKs. apply (j2 p s Js c0 z Oz0). right. exists c. auto.
           ++ apply OKs. apply (j2 p s Js c0 z Oz0). right. exists c. auto.
           ++ apply OKs. apply (j2 p s Js c0 z Oz0). left. exact Zg.
           ++ exact (Src x z U (or_introl eq_refl)).
           ++ lia.
        -- destruct (EA Z) as [Za|(x & y & U & Zc)].
           ++ apply OKs. apply (j2 p s Js c0 z Oz0). right. exists c. auto.
           ++ apply (Src x y U). destruct Zc as [Zc|Zc]; [right; exact Zc|left; exact Zc].
      * rewrite (Cs d Ndc) in Zd. apply OKs. apply (j2 p s Js c0 z Oz0). right. exists d. auto.
  - (* j3 *)
    intros c0 z Z.
    destruct (Nat.eq_dec c0 c) as [->|N]; [|rewrite (Cs c0 N) in Z |- *; exact (j3 p s Js c0 z Z)].
    rewrite VO in Z. rewrite VOg.
    destruct i as [m0 xs cd|m0 xs cd v|m0 xs cd ev nv|f|]; cbn [newO newOg] in Z |- *;
      try exact (j3 p s Js c z Z).
    destruct f; cbn [newO newOg] in Z |- *.
    + (* guard.rl() *)
      destruct Z as [Z|(Zpa & Nown)]; [exact (j3 p s Js c z Z)|].
      cbn [mof mP mA mG] in Zpa, Nown.
      assert (Nf : ~ NF p s c) by exact (HL eq_refl).
      destruct (ownw_dec2 s c z) as [Oz|Nz].
      * intros NO. apply Nown. split; [exact Oz|]. intros Gz.
        destruct (j2 p s Js c z Oz (or_introl Gz)) as [Og|Nf']; [exact (NO Og)|exact (Nf Nf')].
      * intros NO. destruct (j1 p s Js c z Nz Zpa) as [Og|Nf']; [exact (NO Og)|exact (Nf Nf')].
    + exact (j3 p s Js c z Z).
    + exact (j3 p s Js c z Z).
    + destruct Z as [Z|Z]; [intros NO; apply (j3 p s Js c z Z); intros Og; apply NO; left; exact Og|].
      intros NO. apply NO. right. exact Z.
    + intros NO. apply NO. exact Z.
Qed.
End Evs.

(* ---------- a step that changes no view ---------- *)
Section Same.
Variables (s s' : st).
Hypothesis R : run p s.
Hypothesis St : step p s s'.
Hypothesis Js : J p s.
Hypothesis Vw : forall c, vP (cs s' c) = vP (cs s c) /\ vA (cs s' c) = vA (cs s c) /\ vO (cs s' c) = vO (cs s c) /\
  vOg (cs s' c) = vOg (cs s c).
Hypothesis VG : vG s' = vG s.
Hypothesis Lg : lg s' = lg s.

Let SI := self_image p G1' s W R.
Let Kr := proj2 SI.

Theorem J_same : J p s'.
Proof.
  assert (Ow : forall c z, ownw s' c z <-> ownw s c z) by (intros c z; unfold ownw; rewrite Lg; tauto).
  constructor.
  - intros c z Nz Kz. destruct (Vw c) as (EP & EA & _). rewrite EP, EA in Kz.
    assert (Nz0 : ~ ownw s c z) by (intros O; apply Nz; apply Ow; exact O).
    apply (OK_step p W s s' R St c z (j1 p s Js c z Nz0 Kz)). tauto.
  - intros c z Oz Kz. apply Ow in Oz.
    assert (Kz0 : Kn s c z).
    { destruct Kz as [Zg|(d & Nd & Zd)]; [left; rewrite <- VG; exact Zg|right; exists d; split; [exact Nd|]].
      destruct (Vw d) as (EP & EA & _). rewrite EP, EA in Zd. exact Zd. }
    apply (OK_step p W s s' R St c z (j2 p s Js c z Oz Kz0)). left. exact (w_OW False G1' sw0 s s Kr c z Oz).
  - intros c z Z. destruct (Vw c) as (_ & _ & EO & EOg). rewrite EO in Z. rewrite EOg. exact (j3 p s Js c z Z).
Qed.
End Same.
End S.

Print Assumptions NF_no_early.
Print Assumptions J_evs.
Print Assumptions J_same.
