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
