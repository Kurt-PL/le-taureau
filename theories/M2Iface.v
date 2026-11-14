(* Model2: what the memory model guarantees, as one record (the interface
   layer). The results above it (fenced code is SC, the forbidden litmus
   outcomes, the parade, the DRF replay) are proved from these fields only,
   for any step relation that has them. A change of the rules re-proves the
   instance (M2IfaceInst) and leaves the results alone.

   The fields, in plain words:
   - g_slots (Inv1): a run is a log of entries, one per executed slot, at
     the time it happened; each context passes its slots in order (the
     settle order); of two passed instructions tied to each other, the
     earlier happened first; pending early accesses are never tied to each
     other.
   - g_values (Inv2): what a read put in its register is what it took; a
     write enters the histories of its cells; histories hold writes only,
     once each; what an access knew happened before it.
   - g_knowledge (Inv3): knowledge travels along programme order, through
     guard() pairs in time order, through guard.store into what a write
     carries, and through guard.load from what a read received.
   - g_in_order (InvO): what an access knows in order: its context's
     knowledge at its last guard(), and what it read or received by its
     last guard.load, except its own stores not yet published; and the
     write it takes, unless that is such a store.
   - g_keeps: a step keeps everything earlier (log, histories, registers of
     passed and recorded slots).
   - g_rule_back: the rule holds at every earlier state if it holds now.
   - g_two_level: the rule (evok) is the two-level timeline rule (tl2ok):
     no cycle on any cell's timeline, and none across cells through the
     histories, the writes a read missed and what each access knows in
     order.
   - g_no_thin_air: no value appears that no instruction could write.
   - g_slot0: slot 0 happened only once its context passed beyond it (an
     access early is placed beyond the next instruction when it happens).
   - g_no_half: a programme with no CAS has no CAS's read alone.
   The R1 part, which depends on how early accesses are placed:
   - g_birth: a slot passed by a run was passed by one step of it, at a time
     no earlier than its entry.
   - g_pending_cells: an access pending at some state keeps its cells: when
     it is later passed, the instruction there names the same cells.
   - g_pending_source: a read that took a write still pending when the read
     was passed, in a cell the read's instruction names, gives a race in some
     interleaving of a race-free programme. *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Inv3 M2InvO M2Oota M2Snap M2Trace M2Timeline2 M2SC M2PComp M2PSync.

(* the states reachable by a step relation *)
Inductive reach (STEP : st -> st -> Prop) : st -> Prop :=
| re0 : reach STEP sinit
| reS : forall s t, reach STEP s -> STEP s t -> reach STEP t.

Lemma reach_run : forall p s, reach (step p) s <-> run p s.
Proof.
  intros p s. split; intros H; induction H; try constructor; econstructor; eauto.
Qed.

(* f 0 .. f n, each a step from the one before *)
Definition gtrace (STEP : st -> st -> Prop) (f : nat -> st) (n : nat) : Prop :=
  f 0 = sinit /\ forall i, i < n -> STEP (f i) (f (S i)).

(* an interleaving with a race *)
Definition RACY (p : prog) : Prop := exists l g, srun p l g /\ racy_g p l.

(* a base: an interleaving of the slots a state has passed, faithful to it *)
Definition base (p : prog) (sb : st) (lb : list sev) (gb : sst) : Prop :=
  srun p lb gb /\ (forall c, sp gb c = pcs sb c) /\ (forall c j, j < pcs sb c -> sr gb c j = rg (cs sb c) j) /\
  gordS sb lb /\ cohS sb lb.

Record M2Guarantees (p : prog) (STEP : st -> st -> Prop) : Prop := {
  g_slots : forall s, reach STEP s -> Inv1 p s;
  g_values : forall s, reach STEP s -> Inv2 p s;
  g_knowledge : forall s, reach STEP s -> Inv3 p s;
  g_in_order : forall s, reach STEP s -> InvO p s;
  g_keeps : forall s t, reach STEP s -> STEP s t -> Ext s t;
  g_rule_back : forall s t, reach STEP s -> STEP s t -> evok t -> evok s;
  g_two_level : forall s, tl2ok s <-> evok s;
  g_no_thin_air : wf p -> forall (V : val -> Prop), V 0 -> tclosed p V -> forall s, reach STEP s ->
    (forall y x, isw s y -> V (wv s y x)) /\ (forall c j, kV V (ai (cs s c) j) (rg (cs s c) j));
  g_slot0 : forall s, reach STEP s -> forall c, oc (cs s c) 0 <> None -> 0 < pcs s c;
  g_no_half : cas_free p -> forall s, reach STEP s -> forall c k, oh (cs s c) k = None;
  g_birth : wf p -> forall f n, gtrace STEP f n -> forall c k, k < pcs (f n) c ->
    exists ih, ih < n /\ pcs (f ih) c = k /\ bt (f n) c k <= tm (f ih);
  g_pending_cells : wf p -> forall f n, gtrace STEP f n -> forall i c k, i <= n -> pcs (f i) c <= k ->
    oc (cs (f i) c) k <> None -> icells (ai (cs (f i) c) k) = icells (ai (cs (f n) c) k);
  g_pending_source : wf p -> cellful p -> forall f nb, gtrace STEP f nb -> evok (f nb) ->
    forall lb gb, base p (f nb) lb gb ->
    forall c dh x y EY, dof (ins p c (sp gb c) (sr gb c)) (sr gb c) = Some dh -> In x (icells (inst_of dh)) ->
    ent (f nb) y = Some EY -> ew EY = true -> In x (icells (einstr p (f nb) EY)) -> ec EY <> c ->
    oc (cs (f nb) (ec EY)) (ek EY) = Some y -> pcs (f nb) (ec EY) <= ek EY ->
    RACY p
}.

(* the model the results above are proved for: a step relation per programme
   with the guarantees for every well-formed programme *)
Class Model := {
  STEP : prog -> st -> st -> Prop;
  GG : forall p, M2Guarantees p (STEP p)
}.

Section Get.
Context `{M : Model}.
Lemma I1g : forall p s, reach (STEP p) s -> Inv1 p s. Proof. intros p s R. apply (g_slots p _ (GG p) s R). Qed.
Lemma I2g : forall p s, reach (STEP p) s -> Inv2 p s. Proof. intros p s R. apply (g_values p _ (GG p) s R). Qed.
Lemma I3g : forall p s, reach (STEP p) s -> Inv3 p s. Proof. intros p s R. apply (g_knowledge p _ (GG p) s R). Qed.
Lemma IOg : forall p s, reach (STEP p) s -> InvO p s. Proof. intros p s R. apply (g_in_order p _ (GG p) s R). Qed.
Lemma IAg : forall p s, reach (STEP p) s -> InvAll p s.
Proof. intros p s R. constructor; [apply I1g|apply I2g|apply I3g]; exact R. Qed.
Lemma IAOg : forall p s, reach (STEP p) s -> InvAllO p s.
Proof. intros p s R. constructor; [apply I1g|apply I2g|apply I3g|apply IOg]; exact R. Qed.
End Get.
