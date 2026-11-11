# Left at end of the 2026-11-06 pass

New files AlgMag/Final*.lean. Compile: scratchpad/fin/k.sh Module (real), cma/k.sh (chart stubs), b2/k.sh (b2 stubs).

Not done, exact reason:
- Thm 6.8 (ii), X not separated: chart lemma exists only for X separated; printed input AHR Cor 20.2.
- Lem A.5, general G: SGA3 VII_B 5.5.1, EGA IV 18.12.1, no general G in the tree.
- Lem A.3, general F on a space: no pointed F-action on spaces in the tree; affine dual step is `lemA3_affine`.
- Rem A.6: Sym^n of finite projective not in Mathlib.
- Rem 11.12: CM of the complete intersection example not written (example in the row).
- §9 bridge from `Space.Modules`: needs SmallEtaleModulePullback*, not in the build; not attempted.
- Rem 5.1 (i) double scalar: `hW` hypothesis not derived from coordinates.
- Fact 3.34 infinite families: open, notes/fact334-attempt.md.
- Fact 3.34 (ii), Thm 15.3, Prop 14.4: atlas-free corollaries not written, same pattern as FinalAtlasFree (X qc only, since prop332-type results want an affine U).

## Author decisions 2026-11-06
- Thm 6.8, S-affine form: official statement assumes S separated.
- Corrigendum: actual errors only. Strengthenings stay in REMARKS.md.
- Alternative hypotheses: state as "if one of the following holds, then the conclusion holds". Prop 14.4 last clause: (a) X separated, or (b) X has an FPR atlas.
- arXiv:2509.04274 out of scope from 2026-11-06: not to be published; a new paper generalizing it becomes its v4. No further work on DoubleScalar*.lean.
- The formalization paper (formalization + a few other statements) will be posted as v4 of arXiv:2509.04274, replacing the P^2 note. It must state the generalization of the P^2 result.

## FinalMisc, 2026-11-06, later
- Prop 9.1 as sheaves: `prop91_sheaf` FinalMiscProp91Sheaf.lean, on the two b2 stubs.
- Thm 12.4 global, printed route: `thm124_attP_printed` FinalMiscThm124Face.lean, axioms clean, q124 overlay.
- Lem A.5, general G, read of the printed proof: it shows cofinality of I_n with powers of I_1, not with the augmentation ideal J. J^k <= I_n needs F supported on the unit section, and the D(M) form already carries `TorsionResidue` for this reason. Check this before formalizing.
