# ORACLE: requirements for the τ ordering model (spec 0.1 §2.3)

The requirements the model of spec 0.1 §2.3 must meet, in a form that can be checked by machine. The column **source** names the theorem in `theories/` that decides the row for the model.

How to check:
- `python3 oracle.py all` compiles every test to POWER, ARMv8 and C11 litmus files (in `litmus/{ppc,arm,c11}/`).
- It runs herd7 7.58 with `ppc.cat`, `aarch64.cat` and `rc11.cat`, and writes `table.txt`.
- `python3 oracle.py armalt` runs the ARM alternatives for guard.rs() and writes `run-armalt.log`.
- The column **required** is the Kurt verdict the model must give for the outcome in the `exists` clause.
  - excluded: no admissible execution has that outcome.
  - admitted: some admissible execution has it.
- The hardware cells of LBctrl1, OOTA and OOTActrl are `–`: herd7 has not been run on them. Their litmus files are in `litmus/`.

## Decisions encoded

1. Plain and atomic accesses order nothing. Every basic shape is admitted in its plain and atomic variants, LB included.
2. No value out of thin air: OOTA, OOTActrl and OwnFuture are excluded.
3. Dependencies do not order: LBdata1, LBfalse, LBctrl1 and LBfd are admitted.
4. guard() between every pair of operations gives SC. Every non-SC outcome is excluded.
5. A context's read of its own write is not a signal. FWDLD is admitted.
6. Every outcome that POWER or ARM admits under the cheap mappings must be admitted. No row breaks this.
7. Coherence (sc-per-location) holds: the CoRR, CoWW, CoRW1, CoRW2, CoWR, CoRWlate and CoRWearly shapes are excluded.
8. Weak fences. Here guard.rl() comes after a load and guard.rs() after a store, between consecutive operations:
   - excluded: MP;
   - admitted: SB, LB, WRC, IRIW, ISA2, 2+2W, R and S.
   guard.rs() between every pair of operations orders no read before a later write: LBweakS and SweakS are admitted.
9. A programme that is race-free in every interleaving is SC: DRF.C3Cex is excluded.

## Mappings (cheap)

| Kurt | POWER | ARMv8 | C11 analogue |
|---|---|---|---|
| plain, atomic load / store | lwz / stw | LDR / STR | relaxed |
| guard() | sync | DMB ISH | fence(seq_cst) |
| guard.rl() | lwsync | DMB ISHLD | fence(acquire) |
| guard.rs() | lwsync | DMB ISHLD; DMB ISHST | fence(release) |
| volatile load / store | lwz / stw | LDR / STR | relaxed |

- The hardware columns use these sequences.
- A volatile access lowers to the plain instruction of its row: no fence, no barrier, no fake dependency. Volatility is a σ matter (§2.5: the implementation performs the access exactly once, does not widen it or coalesce it with any other operation, and arranges no other operation within it). The ordering is carried by guard() and its components, as for any other access; no litmus row depends on volatility.
- The C11 analogue maps plain to relaxed, because Kurt gives a racy plain access a defined result where C11 would have undefined behaviour.

## Mapping requirements

- **Plain accesses cost zero** on POWER and ARMv8: a bare load or store, with no fence and no fake dependency. The model must keep every plain-variant row admitted where the hardware admits it.
- **Fences as cheap as herd7 allows.**
  - guard(): each cheaper sequence fails a required exclusion. POWER: lwsync fails SB, IRIW and R. ARMv8: DMB ISHLD; DMB ISHST fails SB and R.
  - guard.rl(): DMB ISHLD on ARM. FWDLD is admitted, and herd7 admits it on ARM.
  - guard.rs(): under the cheaper sequences herd7 was run on (eieio on POWER; DMB ISHST alone on ARM; `python3 oracle.py armalt` reruns them), no row whose outcome is excluded is admitted.

## Flags

- **UNSAFE**: Kurt must exclude the outcome but POWER or ARM admits it under the mapping, so the mapping would be unsound. **There is no such row.**
- **hw-stronger**: Kurt must admit the outcome and some target forbids it. This is harmless; the target is stronger than Kurt.
  - Rows: LB and LBdata1 under C11 (RC11 forbids po ∪ rf cycles); LBfalse and LBfd (the hardware respects dependencies); LB, WRC, IRIW, ISA2, 2+2W and S with weak fences; LBweakS and SweakS; FWDLD on POWER.
- **c11-weaker**: Kurt must exclude the outcome and C11 admits it. There is no such row.

## Required exclusion: a strong DRF-SC counterexample

The programme is race-free in every interleaving. The racy, non-SC execution must be **excluded** by the model. It is the DRF.C3Cex row, and herd7 forbids it on every target.

**DRF.C3Cex**
- E1: u = y; if u == 1 { x = 1 } else { c = 1; r = c; if r == 0 { x = 1 } }
- E2: t = x; if t == 1 { y = 1 }
- Racy outcome: u=1, t=1.

**Further requirements not in the herd7 table** (they need read-modify-write accesses):
- **Beaten**: a transactional CAS on x reads 0 and writes 2, and a plain x = 1 settles between them. Required: excluded.
- **TornCas**: a two-cell transactional CAS against a two-cell plain store. Outcome x: 1<2, y: 2<1. Required: admitted.

## Notes on sources

- The atomic variant of each basic shape is the plain variant on every target: word-sized accesses are single-copy atomic. In the model it is the plain programme, so its row cites the theorem of the plain row. The row is kept so the model states it.
- The tests here are self-contained in oracle.py.
- Admitted rows: a run of the model that ends with the outcome (`M2DQOracleRows.v`; IRIW.weak and 2+2W.weak in `M2DQOracleRank.v`, whose runs place a write, or a read that missed a newer write, against time).
- Excluded rows: `M2DQIfaceUse.v` states the fenced and race-free SC results for this model; `MILitNeg.v` proves its shapes for every model with the guarantees of `M2Iface`, and `M2DQIfaceInst.v` (`m2dq_guarantees`) gives this model those guarantees; `M2DQOracleDRF.v` (DRF.C3Cex, OOTActrl, OOTA), `M2DQOracleCoRW.v` (CoRWlate, CoRWearly) and `M2DQOracleOwn.v` (OwnFuture) decide the remaining excluded rows.

## Table

| test | required | POWER | ARMv8 | C11 (rc11) | flag | source |
|---|---|---|---|---|---|---|
| MP.plain | admitted | S | S | S |  | M2DQOracleRows.v MP_plain_allowed |
| MP.atomic | admitted | S | S | S |  | M2DQOracleRows.v MP_plain_allowed |
| MP.full | excluded | N | N | N |  | M2DQIfaceUse.v fenced_sc_dq |
| MP.weak | excluded | N | N | N |  | M2DQIfaceUse.v MPra_forbidden_dq |
| SB.plain | admitted | S | S | S |  | M2DQOracleRows.v SB_plain_allowed |
| SB.atomic | admitted | S | S | S |  | M2DQOracleRows.v SB_plain_allowed |
| SB.full | excluded | N | N | N |  | M2DQIfaceUse.v fenced_sc_dq; MILitNeg.v SBf_forbidden |
| SB.weak | admitted | S | S | S |  | M2DQOracleRows.v SB_weak_allowed |
| LB.plain | admitted | S | S | N | hw-stronger | M2DQOracleRows.v LB_plain_allowed |
| LB.atomic | admitted | S | S | N | hw-stronger | M2DQOracleRows.v LB_plain_allowed |
| LB.full | excluded | N | N | N |  | M2DQIfaceUse.v fenced_sc_dq; MILitNeg.v LBfull_forbidden |
| LB.weak | admitted | N | N | N | hw-stronger | M2DQOracleRows.v LB_weak_allowed |
| WRC.plain | admitted | S | S | S |  | M2DQOracleRows.v WRC_plain_allowed |
| WRC.atomic | admitted | S | S | S |  | M2DQOracleRows.v WRC_plain_allowed |
| WRC.full | excluded | N | N | N |  | M2DQIfaceUse.v fenced_sc_dq |
| WRC.weak | admitted | N | N | S | hw-stronger | M2DQOracleRows.v WRC_weak_allowed |
| IRIW.plain | admitted | S | S | S |  | M2DQOracleRows.v IRIW_plain_allowed |
| IRIW.atomic | admitted | S | S | S |  | M2DQOracleRows.v IRIW_plain_allowed |
| IRIW.full | excluded | N | N | N |  | M2DQIfaceUse.v fenced_sc_dq; MILitNeg.v IRIWf_forbidden |
| IRIW.weak | admitted | S | N | S | hw-stronger | M2DQOracleRank.v IRIW_weak_allowed |
| ISA2.plain | admitted | S | S | S |  | M2DQOracleRows.v ISA2_plain_allowed |
| ISA2.atomic | admitted | S | S | S |  | M2DQOracleRows.v ISA2_plain_allowed |
| ISA2.full | excluded | N | N | N |  | M2DQIfaceUse.v fenced_sc_dq |
| ISA2.weak | admitted | N | N | S | hw-stronger | M2DQOracleRows.v ISA2_weak_allowed |
| 2+2W.plain | admitted | S | S | S |  | M2DQOracleRows.v W22_plain_allowed |
| 2+2W.atomic | admitted | S | S | S |  | M2DQOracleRows.v W22_plain_allowed |
| 2+2W.full | excluded | N | N | N |  | M2DQIfaceUse.v fenced_sc_dq; MILitNeg.v W22f_forbidden |
| 2+2W.weak | admitted | N | N | S | hw-stronger | M2DQOracleRank.v W22_weak_allowed |
| R.plain | admitted | S | S | S |  | M2DQOracleRows.v R_plain_allowed |
| R.atomic | admitted | S | S | S |  | M2DQOracleRows.v R_plain_allowed |
| R.full | excluded | N | N | N |  | M2DQIfaceUse.v fenced_sc_dq; MILitNeg.v Rf_forbidden |
| R.weak | admitted | S | S | S |  | M2DQOracleRows.v R_weak_allowed |
| S.plain | admitted | S | S | S |  | M2DQOracleRows.v S_plain_allowed |
| S.atomic | admitted | S | S | S |  | M2DQOracleRows.v S_plain_allowed |
| S.full | excluded | N | N | N |  | M2DQIfaceUse.v fenced_sc_dq |
| S.weak | admitted | N | N | N | hw-stronger | M2DQOracleRows.v S_weak_allowed |
| LBweakS | admitted | N | N | N | hw-stronger | M2DQOracleRows.v LBweakS_allowed |
| SweakS | admitted | N | N | S | hw-stronger | M2DQOracleRows.v SweakS_allowed |
| FWDLD | admitted | N | S | S | hw-stronger | M2DQOracleRows.v FWDLD_allowed |
| CoRR.plain | excluded | N | N | N |  | MILitNeg.v CoRR_forbidden |
| CoWW.plain | excluded | N | N | N |  | MILitNeg.v CoWW_forbidden |
| CoRW1.plain | excluded | N | N | N |  | MILitNeg.v CoRW1_forbidden |
| CoRW2.plain | excluded | N | N | N |  | MILitNeg.v CoRW2_forbidden |
| CoWR.plain | excluded | N | N | N |  | MILitNeg.v CoWR_forbidden |
| LBdata1 | admitted | S | S | N | hw-stronger | M2DQOracleRows.v LBdata1_allowed |
| LBfalse | admitted | N | N | N | hw-stronger | M2DQOracleRows.v LBfalse_allowed |
| LBfd | admitted | N | N | N | hw-stronger | M2DQOracleRows.v LBfd_allowed |
| OwnFuture | excluded | N | N | N |  | M2DQOracleOwn.v OwnFuture_forbidden_Q |
| CoRWlate | excluded | N | N | N |  | M2DQOracleCoRW.v CoRWlate_forbidden_Q |
| CoRWearly | excluded | N | N | N |  | M2DQOracleCoRW.v CoRWearly_forbidden_Q |
| DRF.C3Cex | excluded | N | N | N |  | M2DQOracleDRF.v C3Cex_forbidden_Q |
| LBctrl1 | admitted | – | – | – |  | M2DQOracleRows.v LBctrl1_allowed |
| OOTA | excluded | – | – | – |  | M2DQOracleDRF.v OOTA_forbidden_Q |
| OOTActrl | excluded | – | – | – |  | M2DQOracleDRF.v OOTActrl_forbidden_Q |
