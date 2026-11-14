(* Headline: the theorems that decide the oracle rows (oracle/ORACLE.md, column source) for M2DQ,
   apart from those printed in HeadlineCore.v, HeadlineCas1.v, HeadlineCas2.v and the interface
   theorems of MILitNeg.v. Part 4 of 4: the excluded rows. *)
Require Import M2DQOracleDRF M2DQOracleCoRW M2DQOracleOwn.
Require Import M2DQOracleRows M2DQOracleRank M2DQOracleDRF M2DQOracleCoRW M2DQOracleOwn.
Print Assumptions M2DQOracleDRF.C3Cex_forbidden_Q.
Print Assumptions M2DQOracleDRF.OOTActrl_forbidden_Q.
Print Assumptions M2DQOracleDRF.OOTA_forbidden_Q.
Print Assumptions M2DQOracleCoRW.CoRWlate_forbidden_Q.
Print Assumptions M2DQOracleCoRW.CoRWearly_forbidden_Q.
Print Assumptions M2DQOracleOwn.OwnFuture_forbidden_Q.
