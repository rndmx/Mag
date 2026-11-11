# Check of unrestrict-g4-prop144.md (Prop 14.4, first and second assertions)

Adversarial check, 2026-11-07. Pure math only, nothing compiled, no existing file edited.

## Verified
- Lean names exist with the stated shapes: `prop144_general` (FinalNonQCGeneral.lean:138), `prop144_rep_general` (FinalNonQCClauses.lean:105), `prop144_scheme_general` (:135), `attP_alg` (FinalNonQCAttAlg.lean:163, `hZ` a section variable), `isClosedImm_repAttractorMap` (Sec12Topology.lean:1007), `isIndAlgebraicSpace_attractor` (Sec14Ind.lean:327), `indAttractorMap_rep_nat` (Sec14Strong.lean:177), `contains_zmon_of_countable` (AppendixA.lean:194), `countable_of_fg83` (Sec8Theorem83.lean:94), `B.contains_terminal` (used as a term in ChartQSAsm.lean:417 and elsewhere).
- Read the body of `prop144_rep_general` and `prop144_scheme_general`: the only hypotheses are `hZ hM hX hsep hfp` (+ `hS'`), with `N` arbitrary; `r`, `j`, `hj` are instantiated canonically by `attPRep`, `attToX`, `rfl`, and the representability input by `attP_alg`. Matches the note.
- `hZ := B.contains_terminal`, `hM := contains_zmon_of_countable hS M` (with `Countable M` from `countable_of_fg83`): types agree by signature inspection. Grade 1, correct.

## Mathematical check
- Reading "X separated" as "terms separated": the note hedges for non-quasi-compact terms. The hedge is unnecessary. Each X_i -> X is a monomorphism, so Delta_{X_i} is the base change of Delta_X along X_i x X_i -> X x X; hence X separated (diagonal a closed immersion, tested on affines) forces every term of ANY presentation separated, for any presentation, quasi-compact or not. So `hsep` is implied by the printed hypothesis; no restriction.
- Steps 2-5 (closed transition maps via base change, ind-assembly, fibre over affine T, scheme clause) use only representability of each X_i^N: consistent with the Lean bodies read.
- Case (*) "N f.g., terms quasi-separated not separated": correctly identified as the agreed Thm 8.3 (b) gap (STATUS Agreed list). Claim "printed proof incomplete when M/N^x has torsion" is plausible (Thm 6.8 (ii) supplies the atlas only for M/Z torsion-free) but is a REMARKS observation, not verified as a paper error; no counterexample claimed, correctly. Doubled-origin remark concerns only the last assertion, already agreed.
- Not verified: compilation of the proposed new-file code (argument order of `prop144_general`); stub `sorryAx` dependence is a build matter.

## Verdicts
- Prop 14.4 first assertion: ACCEPTED (UNRESTRICTED under "X separated", strengthened: hsep follows from X separated for every presentation; WALL in case (*) = agreed Thm 8.3 (b) gap).
- Prop 14.4 second assertion: ACCEPTED (same split, same wall).
