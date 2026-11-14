# Le τ-reau

Le τ-reau is a model of the τ ordering rules of the Kurt programming
language, stated and proved in Rocq. The rules are those of the Kurt
specification 0.1, §2.3 ("The ordering of τ"): they say which executions of
a programme are admissible. The model is a step relation, `stepQ`, and its
runs, `runQ` (`theories/M2DQ.v`). An admissible execution is a run whose
events form no cycle (`evok`). The store that a failed compare-and-swap may
perform (write-back, §2.3.4 and §8.6) is a layer on top (`runWB`,
`theories/M2DQWB.v`).

Volatility plays no part in τ: only `guard()` is tied to every evaluation
(§2.3.1), and two operations are the same where their kinds, cells and operand
values agree. Volatility is a σ matter (§2.5). The model accordingly has no
volatile access: every access is tied by its cells and by fences alone, every
load may be led, and every compare-and-swap happens in two parts. Its results
hold for every programme, and a volatile access of a Kurt programme is modelled
as the access it performs.

What is proved, for every programme of the model:

- No value out of thin air: every value written or read lies in any set of
  values that holds 0 and is closed under the programme's operations.
- Fenced code is sequentially consistent: when every access stands between
  two `guard()` fences, each finished admissible run has an interleaving with
  the same registers and the same final storage.
- DRF-SC: the same holds for every programme that is race-free in every
  interleaving and whose every access names a cell.
- Both results hold also with write-back, and write-back adds no outcome.
- A compare-and-swap always happens in two parts, a load part and a store
  part.
- The verdicts of a litmus suite (`oracle/`): every admitted outcome has a
  run, and every excluded outcome has none. The rows LB.plain (admitted) and
  LB.full (excluded) show what an access orders without fences and with
  them, a volatile one included.

Zero axioms. No file of `theories/` declares an axiom or admits a proof
(`grep -nwE 'Axiom|Parameter|Admitted|admit' theories/*.v` prints nothing).
Every headline theorem is closed under the global context, and `rocqchk`
accepts every module. `./check` checks both.

## Build and check

Requires the Rocq Prover 9.3.0 (compiled with OCaml 5.4.1) and its standard
library (`Stdlib`).

    ./build          # rocq makefile, then make -j4 (about 7 CPU minutes)
    ./check PART     # one part of the checks; ./check alone lists the parts

Run `./build` first. Each part is one job of under 30 CPU seconds, and exits
with status 0 only if it passes. The eleven parts together are the whole check.

| Part | What it does |
|---|---|
| `pa-core` | Compiles `theories/HeadlineCore.v`; each of its 6 `Print Assumptions` must print "Closed under the global context". |
| `pa-cas1`, `pa-cas2` | The same for `theories/HeadlineCas1.v` (7 theorems) and `theories/HeadlineCas2.v` (6). |
| `pa-wbdq` | The same for `theories/HeadlineWBDQ.v` (11 theorems). |
| `pa-oracle1` … `pa-oracle4` | The same for `theories/HeadlineOracle1.v` … `HeadlineOracle4.v` (9, 8, 7 and 6 theorems). |
| `chk-1`, `chk-2`, `chk-3` | `rocqchk -norec` on one third each of the modules of `theories/`. |

## Layout

`theories/`: 203 Rocq files, one project with the logical name `LeTaureau`
(`_CoqProject`). By module-name prefix:

- `M2Model`, `M2Inv*`, `M2Eff`, `M2Hist`, `M2Ev*`, `M2Oota`, `M2SC*` and the
  other `M2*` files: the base step relation (an evaluation happens in order or
  early, as a whole), its invariants, the event graph, and the lemmas the later
  models reuse.
- `M2DA*`, `M2DP*`: two intermediate models. In `M2DA` a compare-and-swap
  happens only in parts; `M2DP` adds outcomes counted on.
- `M2DQ*`: the model. `M2DQ.v` defines it; the others prove its invariants,
  its headline results and its litmus runs.
- `MI*`, `M2Iface*`: results proved for every model with the guarantees of
  `M2Iface` (fenced SC, DRF-SC, forbidden litmus shapes).
- `M2WB*`, `M2DQWB*`: write-back, and the proof of DRF-SC with it in numbered
  parts (`M2DQWBK*`).
- `M2DQOracle*`: the theorems that decide the litmus rows.
- `Headline*`: `Print Assumptions` on the headline theorems.
- `Topo.v`: a topological order of a finite acyclic relation.

`oracle/`: the litmus suite. `oracle.py` compiles each test to POWER, ARMv8
and C11 litmus files (`litmus/`) and runs herd7 7.58 on them. `ORACLE.md`
states the required verdicts and the decisions behind them; `table.txt` and
`table.md` give each row's verdicts and the theorem that decides it.

`LICENCE`: the Non-assertion pledge.

## Theorems and the specification

§ numbers are those of the specification 0.1. The quotations are exact; the
middle column is a summary. Every theorem below is stated for `M2DQ`, and the
general ones hold for every programme.

| Theorem | File | What it states | Spec sentence |
|---|---|---|---|
| `IQ_run` | `M2DQInv.v` | The model's state invariants hold on every run. | — |
| `no_thin_air_Q` | `M2DQOota.v` | For a set of values that holds 0 and is closed under the programme's operations, every value written and every register lies in it. | §2.3: "A read **observes**, at each cell it reads, one write to that cell: the initial write of the cell, or a write to the cell that has happened before the read happens." |
| `m2dq_guarantees` | `M2DQIfaceInst.v` | `M2DQ` has the guarantees of the interface `M2Iface`, so the `MI*` results apply to it. | — |
| `fenced_sc_dq` | `M2DQIfaceUse.v` | A finished admissible run of a programme whose every access stands between two `guard()` has an interleaving with the same registers and final storage. | Property of §2.3 as a whole. Depends most on §2.3.2: "A fence other than `guard()` consists of one **component** for each ordering property it has, and `guard()` of one component with all four."; §2.3.1: "Either is a `guard()`."; §2.3: "No event is ordered before itself across cells, through one or more steps." |
| `drf_sc_dq` | `M2DQIfaceUse.v` | The same for every programme that is race-free in every interleaving and whose every access names a cell (`cellful`). | Property of §2.3 as a whole. Depends most on §2.3: "A read **observes**, at each cell it reads, one write to that cell: the initial write of the cell, or a write to the cell that has happened before the read happens."; "An evaluation that happens as a whole is, under every valuation, its own claim when it happens early, and has the operation it happened with when its execution context reaches it."; "No event is ordered before itself across cells, through one or more steps." |
| `cas_in_parts` | `M2DQInst.v` | A step completes a compare-and-swap only where its load part has happened before: every compare-and-swap happens in two parts, a load part and a store part, never as a whole. | §2.3.4: "Each part is an evaluation." |
| `CASHoistX_forbidden_Q` | `M2DQCasHoistX.v` | `r0 = y; if r0 == 5 { r1 = CAS(x, 0, 5) } else { r2 = CAS(w, 0, 7) }; z = r1 + r2 ‖ r = z; y = r ‖ x = 5`: no finished run has r0 = 5 with the CAS reading 5. | §2.3: "An evaluation that happens as a whole is, under every valuation, its own claim when it happens early, and has the operation it happened with when its execution context reaches it." |
| `CASHoistX_runs` | `M2DQCasHoistXRun.v` | CASHoistX has a finished run, so the theorem above is not vacuous. | — |
| `SPFH_Q` | `M2DQSpfhInst.v` | `r0 = y; [r0 = 0] CAS(x, 0, 5); [r0 ≠ 0] CAS(x, 0, 5); x = 1 ‖ r1 = x; y = r1`: r0 = 1 with the CAS failing on 0 is admitted. | §2.3.4: "A joint access with one fails where the value does not satisfy the condition, and succeeds or fails where the value satisfies it."; "Under a valuation, a load part that has happened stands for the joint access whose load part is its claim under that valuation at the point at which it happened." |
| `SPFD_Q` | `M2DQSpfdInst.v` | As SPFH, with the second CAS expecting 7: admitted. | §2.3.4: "Under a valuation, a load part that has happened stands for the joint access whose load part is its claim under that valuation at the point at which it happened."; "An evaluation that happens early may count on an outcome where a load part has happened, has one value under every valuation considered for it, and every such valuation permits the outcome to the joint access that load part stands for under that valuation." |
| `CASDEP_allowed_Q` | `M2DQCasDepInst.v` | `r0 = y; r1 = CAS(x, 7, r0); z = r1 ‖ r = z; y = r ‖ x = 7`: r0 = 7 with the CAS reading 7 is admitted. | §2.3.4: "The operands of the store part are the object, the type, and the value that its store names, and, where the joint access succeeds, every operand of the operation that performs the joint access."; §2.3.1: "Where an evaluation *x* has happened with one of them as its claim under *V*, that one has, in each cell, the symbol that the write *x* observed there places." |
| `LBCW_allowed_Q` | `M2DQLitmusLBCWInst.v` | `r0 = z; r1 = CAS(x, 0, 1); x = 2 ‖ r2 = x; z = r2`: r0 = r2 = 2, the CAS succeeding, is admitted. | §2.3.4: "Each part is an evaluation."; §2.3: "An evaluation is **early** where it happens while it is not the next evaluation of its context." |
| `LBWC_allowed_Q` | `M2DQLitmusLBWCInst.v` | `r0 = z; x = 1; r1 = CAS(x, 1, 2) ‖ r2 = x; z = r2`: r0 = r2 = 2, the CAS reading its own context's x = 1, is admitted. | §2.3.4: "Each part is an evaluation."; §2.3: "A read **observes**, at each cell it reads, one write to that cell: the initial write of the cell, or a write to the cell that has happened before the read happens." |
| `CASRFWD_allowed_Q` | `M2DQBindCASRFWDInst.v` | `r0 = x; x = 1; c = CAS(x, 1, 2); y = c ‖ r1 = y; x = r1`: r0 = 1 with the CAS reading 1 is admitted; the CAS's read is counted on. | §2.3: "An evaluation counted on observes, in each cell it is led in, the write its leader made there or, where its leader made none, the write its leader observed there, under every valuation when its execution context reaches it."; §2.3.1: "An evaluation of a load is **led in** each cell its leader accesses and it reads." |
| `LOCKREL_allowed_Q` | `M2DQSTWLOCKRELInst.v` | `r0 = x; guard.rs(); y = 5 ‖ r1 = CAS(y, 5, 1); guard.rl(); x = 9`: r0 = 9 with the CAS reading 5 is admitted. | §2.3.1: "One is a component with the kind pair (*k*<sub>1</sub>, *k*<sub>2</sub>), and the other an earlier evaluation of the kind *k*<sub>1</sub> or a later evaluation of the kind *k*<sub>2</sub>." |
| `CASLBW_succ_Q` | `M2DQS3cLBWInst.v` | `r0 = f; x = r0; x = 1; r3 = CAS(x, 1, 7); r4 = x; z = r4 ‖ r1 = z; f = r1`: r0 = 7, the CAS reading 1 and succeeding, is admitted. | §2.3.4: "An evaluation that happens early may count on an outcome where a load part has happened, has one value under every valuation considered for it, and every such valuation permits the outcome to the joint access that load part stands for under that valuation."; §2.3: "An evaluation counted on observes, in each cell it is led in, the write its leader made there or, where its leader made none, the write its leader observed there, under every valuation when its execution context reaches it." |
| `CASPDEP_allowed_Q` | `M2DQCasPDepInst.v` | CASDEP with a two-cell CAS on (x, w): admitted. | §2.3.4: "The operands of the store part are the object, the type, and the value that its store names, and, where the joint access succeeds, every operand of the operation that performs the joint access."; §2.3.1: "Where an evaluation *x* has happened with one of them as its claim under *V*, that one has, in each cell, the symbol that the write *x* observed there places." |
| `CAS2_allowed_Q` | `M2DQCas2Inst.v` | `r0 = y; r1 = q; r2 = CAS(x, r0, 7); z = r2 ‖ r = z; y = r ‖ s = x; q = s ‖ x = 5`: r0 = 5, r1 = 7, s = 7 is admitted; the store part happens early. | §2.3.4: "An evaluation that happens early may count on an outcome where a load part has happened, has one value under every valuation considered for it, and every such valuation permits the outcome to the joint access that load part stands for under that valuation."; §2.3.1: "Where an evaluation *x* has happened with one of them as its claim under *V*, that one has, in each cell, the symbol that the write *x* observed there places." |
| `CAS2_erf_Q` | `M2DQCasErfInst.v` | In that run, the load part and the store part of the CAS observe the same write. | §2.3.4: "The store part happens after its load part, reads the cells its load part read, observing at each the write its load part observed there, and then writes." |
| `fenced_sc_WB` | `M2DQWBK15.v` | `fenced_sc_dq` with write-back. | Property of §2.3 as a whole (as `fenced_sc_dq`), with §2.3.4: "Where its rule permits, a joint access that fails may perform a store of the value its load part observed." |
| `drf_sc_WB` | `M2DQWBK69.v` | `drf_sc_dq` with write-back. | Property of §2.3 as a whole (as `drf_sc_dq`), with §2.3.4: "Where its rule permits, a joint access that fails may perform a store of the value its load part observed." |
| `FWB_G2` | `M2DQWBK70Inst.v` | `guard(); CAS(x, 1, 2); guard() ‖ guard(); r1 = x; guard()`: a finished run in which the read takes the write-back store, and its interleaving by `drf_sc_WB`. | §8.6: "Where that joint access fails, it may perform a store of the value its load part observes." |
| `WB_sim` | `M2DQWB.v` | Every finished write-back run has a finished run without write-back with the same registers and final storage. | §8.6: "Whether the joint access performs a store where it fails is implementation defined." |
| `Q_in_WB` | `M2DQWB.v` | Every run without write-back is a write-back run. | §8.6: "Whether the joint access performs a store where it fails is implementation defined." |
| `sim_stepQ` | `M2DQWB.v` | The step case of `WB_sim`. | — |
| `lzp_not_tied` | `M2DQWBZero.v` | A zero-size load is not tied to a load of a cell. | §2.3.1: "Both access a common cell." |
| `LZP_not_cellful` | `M2DQWBZero.v` | An access of no cell does not meet `cellful`. | — |
| `wbc_wbP` | `M2DQWBK30.v` | After a write-back by a CAS that fails and is passed by its context, a write in one of its cells conveys at most itself and what the write-back store conveys, or it is of another context and both accesses stand between `guard()` fences. | §2.3.2: "A write **conveys** itself and the conveyed writes of its context at the time it happens." |
| `WBL_led` | `M2DQWBLeadInst.v` | `r0 = CAS(x, 1, 2); r1 = x; y = r1 ‖ x = 3`: the CAS reads 3, fails and writes back; `y = r1` happens early, counting on `r1 = x`, which is led in x by the CAS; that read then observes the write-back store, and r1 = y = 3. A finished admissible write-back run. | §2.3: "An evaluation counted on observes, in each cell it is led in, the write its leader made there or, where its leader made none, the write its leader observed there, under every valuation when its execution context reaches it."; §2.3.4: "Where its rule permits, a joint access that fails may perform a store of the value its load part observed." |
| `WBL_neg` | `M2DQWBLeadInst.v` | A write-back run of the same programme up to the write-back, after which the CAS's record in x is the write-back store: the read counted on meets the leader premise when it observes the write-back store and not when it observes the write the CAS's load part observed, and that write is no longer visible to the CAS's context. | §2.3.1: "The **symbol of the leader** in a cell is the symbol that the write the leader made there places or, where it made none, that the write it observed there places." |
| 30 theorems `*_allowed`, `*_forbidden_Q` | `M2DQOracle{Rows,Rank,DRF,CoRW,Own}.v` | The verdict of each litmus row that cites them. | Property of §2.3 as a whole, row by row. Each row of `oracle/table.md` names its theorem; `oracle/ORACLE.md` states the decision behind each verdict. |

The first 6 theorems are printed by `HeadlineCore.v`, the next 13 by
`HeadlineCas1.v` (7) and `HeadlineCas2.v` (6), the next 11 by
`HeadlineWBDQ.v`, and the last 30 by `HeadlineOracle1.v` to
`HeadlineOracle4.v`. The rows of `oracle/table.md` also cite
`MPra_forbidden_dq` (`M2DQIfaceUse.v`) and the shapes of `MILitNeg.v`, which
hold for every model with the guarantees of `M2Iface`.

## Model vs spec

The model's names are not the specification's defined terms. The main
correspondences:

| Model | Specification |
|---|---|
| `runQ p s`, `stepQ`; time `tm`, log entry `ent s t` | an execution so far, in the order of happening; an evaluation happening, at its place in that order |
| `pcs s c`; a slot recorded at or after it (`oc`) | the next evaluation of context `c`; an evaluation that has happened early |
| `tied`; `pend_at` (the place of a pending access); `fbinder` | tied; the claim; the leader |
| the free values `f` of `creg`; `bd` and the `B` arguments | a valuation; the evaluations counted on |
| `ICas`; `s_cread`; `s_cw`, `s_cwe`; `fx`, `q_rfix`, `q_sfix` | a joint access by compare-and-swap; its load part; its store part; an outcome counted on |
| the field `mode` of an access, whose one value is `Plain` | no counterpart: an access is ordered by its cells and by fences alone |
| `hs s x`; `erf` | the settlement order of cell `x`; the write an evaluation observes at each cell it reads |
| `vP`, `vA`, `vR`, `vG`, `vO`, `vOg`; `mW`; `wc` | the sets *P*, *A*, *R*, *G*, *O*, *O*<sub>g</sub>; *W*; the writes a write conveys |
| `FFull`, `FLl`, `FSs`, `FLs`, `FSl` | `guard()`, and the components that relay loads, relay stores, withhold stores, withhold loads |
| `gedge`, `cedge x`; `evok` | ordered before across cells, and on cell `x`; the first two conditions of admissibility (the other two are conditions of the steps) |
| `srun`; `race_free_g`; `fenced` | an interleaving of the contexts; race-free in every interleaving; every access between two `guard()` |
