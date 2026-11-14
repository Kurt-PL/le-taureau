(* Model2, one event, on litmus runs: a rank given as a list of times, checked
   edge by edge on the concrete final state. *)
From Stdlib Require Import Arith Lia List Bool Relations.
Import ListNotations.
Require Import M2Model M2Hist M2Eff M2Inv M2Inv2 M2Lit M2Ev M2Acyc.

Ltac inlist H := vm_compute in H;
  repeat match type of H with _ \/ _ => destruct H as [H|H] | False => destruct H end.

Ltac nat12 a := destruct a as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|a]]]]]]]]]]]]]]]].
Ltac cell4 x := destruct x as [|[|[|[|x]]]].

(* an entry of the log at an unknown time *)
Ltac at_ent L a := nat12 a; vm_compute in L; try discriminate; injection L as <-.

Ltac rk_close := vm_compute; lia.

(* a knowledge edge that is not there: its view, decomposed, is contradictory;
   a taken write that is the context's own store not known in order is not known in order *)
Ltac refute_neg := match goal with Hn : _ -> False |- _ =>
  exfalso; apply Hn; clear Hn;
  first [ (eexists; split; [reflexivity|repeat split; reflexivity])
        | (split; [eexists; split; [reflexivity|repeat split; reflexivity]
                  |let Z := fresh in intro Z; kn' Z; try discriminate]) ] end.
Ltac know_edge Q a := nat12 a; vm_compute in Q;
  first [ rk_close
        | (kn' Q; try discriminate; try (exfalso; lia); try refute_neg; rk_close) ].

(* the write is newer than the source: otherwise the edge is not there *)
Ltac newer_or_not M :=
  vm_compute in M;
  first [ exact I | (apply older_b in M; vm_compute in M; discriminate) | idtac ].

Ltac ev_gedge :=
  let a := fresh "a" in let b := fresh "b" in let E := fresh "E" in
  let x := fresh "x" in let O := fresh "O" in let e := fresh "e" in
  let L := fresh "L" in let Ix := fresh "Ix" in let Ib := fresh "Ib" in let N := fresh "N" in
  let M := fresh "M" in let Q := fresh "Q" in
  intros a b E; destruct E as [(x & O)|[(e & x & L & Ix & Ib & N & M)|(e & L & Q & N)]];
  [ apply older_pairs in O; cell4 x; inlist O; try (injection O as <- <-); rk_close
  | at_ent L a; inlist Ix; subst x; inlist Ib; subst b; vm_compute in M;
    try (apply older_b in M; vm_compute in M; discriminate); rk_close
  | at_ent L b; know_edge Q a ].

Ltac ev_cedge :=
  let x := fresh "x" in let a := fresh "a" in let b := fresh "b" in let E := fresh "E" in
  let O := fresh "O" in let e := fresh "e" in let e2 := fresh "e" in
  let L := fresh "L" in let L2 := fresh "L" in let Ix := fresh "Ix" in let Ib := fresh "Ib" in
  let N := fresh "N" in let M := fresh "M" in let Q := fresh "Q" in let C := fresh "C" in let K := fresh "K" in
  intros x a b E;
  destruct E as [O|[(e & L & Ix & Ib & N & M)|[(e & L & Ix & M & N)|[(e & L & Ix & Q & Ib & N)|(e & e2 & L & L2 & C & K & Ix & Ib)]]]];
  [ apply older_pairs in O; cell4 x; inlist O; try (injection O as <- <-); rk_close
  | at_ent L a; inlist Ix; subst x; inlist Ib; subst b; vm_compute in M;
    try (apply older_b in M; vm_compute in M; discriminate); rk_close
  | at_ent L b; inlist Ix; subst x; vm_compute in M; first [discriminate M | injection M as <-]; rk_close
  | at_ent L b; know_edge Q a
  | at_ent L a; at_ent L2 b; vm_compute in C, K; try discriminate; try lia;
    inlist Ix; subst x; inlist Ib; rk_close ].

Ltac evok_tac ord := apply (evok_rank _ (fun a => idx a ord)); [ev_gedge|ev_cedge].

