(* Model2, a CAS in two parts, allowed: CAS2. *)
From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Lit M2Ev M2EvLit M2Oota M2CasSplitProof M2EvTimeProof.

(* CAS2 (the seed of case 2: the write early):
     r0 = y; r1 = q; r2 = CAS(x, r0, 7); z = r2 || r = z; y = r || s = x; q = s || x = 5
   with r0 = 5, r1 = 7, s = 7: the CAS's read takes x = 5 alone, z = 5
   follows it, y = 5 comes back to r0; the CAS's write then happens early,
   before r1 = q, and q = 7 comes back to r1 *)
Definition CAS2 : prog := stat
  [ [ld 1; ld 3; ICas Plain [0] T (RG 0) (K 7); ISt Plain [2] T (fun r => vv (r 2))];
    [ld 2; ISt Plain [1] T (RG 0)];
    [ld 0; ISt Plain [3] T (RG 0)];
    [st 0 5] ].

Lemma CAS2_allowed : exists s, run CAS2 s /\ done CAS2 s /\ evok s /\
  rg (cs s 0) 0 = 5 /\ rg (cs s 0) 1 = 7 /\ rg (cs s 2) 0 = 7.
Proof.
  apply startR.
  eapply fwd. { ord 3. ST. W0. } nameS.
  eapply fwd. { cread 0 2 [0] 2. LD (Some 0). vis_some. } nameS.
  eapply fwd. { earlyH 0 3 (DSt Plain [2] 5) 3. ST. W0. } nameS.
  eapply fwd. { ord 1. LD (Some 2). vis_some. } nameS.
  eapply fwd. { ord 1. ST. W0. } nameS.
  eapply fwd. { ordH 0. LD (Some 4). vis_some. } nameS.
  eapply fwd.
  { cwe 0 2 1 [0] 5 7.
    - intros f. cbv zeta. exists 2. split; [vm_compute; lia|]. split; [fatR_tac|]. split; [vm_compute; reflexivity|].
      intros j' L1 L2 _ _ Ti. vm_compute in L1. assert (j' = 1) by lia. subst j'.
      apply tied_b in Ti. vm_compute in Ti. discriminate Ti.
    - eapply (e_cas_ok1 _ _ _ _ _ _ _ _ (Some 0));
        [reflexivity|vis_some|vm_compute; reflexivity|enter_at [(0, false)] (@nil (nat * bool))]. }
  nameS.
  eapply fwd. { ord 2. LD (Some 6). vis_some. } nameS.
  eapply fwd. { ord 2. ST. W0. } nameS.
  eapply fwd. { ordH 0. LD (Some 8). vis_some. } nameS.
  eapply fwd. { mtchH 0 (DCas Plain [0] 5 7). } nameS.
  eapply fwd. { mtchH 0 (DSt Plain [2] 5). } nameS.
  finish. intros RUN. split; [done_tac|split; [evok_time_tac RUN|repeat split; reflexivity]].
Qed.


