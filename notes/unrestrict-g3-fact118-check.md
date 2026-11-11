# Check of unrestrict-g3-fact118.md (Fact 11.8)

Verdict: ACCEPTED (UNRESTRICTED), with the wall unchanged: the 07SY stub (sorry).

## What I verified, by reading
- fidelity-grades.md:76: the grade-3 reason is "the universal property for spaces and the equivariant clause are not stated". This is a missing statement, not an added hypothesis. The prover's reading is right.
- These lemma names exist with the signatures the note gives: `pushoutRing` (Sec11Formal:553), `pushoutMap_surjective` (:580), `milnor_pushout` (Sec11SchemesFace:97), `pSnd_surjective` (:104), `pFst_ker` (:108), `milnorPushout` (:116), `milnor_map` (:126), `coactP` (:200), `coactP_fst` (:212), `coactP_snd` (:219), `isPushout_of_milnor` (Sec11SpacesBase:118), `glue` (Sec11SpacesBase:132), `isAlgebraicSpace_yoneda` (used in ChartEffectiveAlg:130 and elsewhere).
- `glue` has the hypotheses `[SR B _]` (size cutoff), `hqs`, `hker` and `hiq` (square-zero kernel). For this square, the last three are discharged at Sec11SpacesFace:143-144 by `pSnd_surjective`, `pFst_ker` and `magnetAlgebra_mul_eq_zero ι hi.sq_zero`. `hiq` is the printed "first order thickening", so it is not a restriction. Its proof goes through `Space.existsUnique_section_of_isThickening_of_isAffineHom`, which is the 07SY stub.
- The `ha` block (Sec11SpacesFace:179-219) uses the specific sections yF and x₀U only in three places: `hpFa'`/`hpSa'` (lines 204, 217) and `equiv_of_attPtS` (lines 206, 219). Everything else is generic: `pb_sq`, `pb_ss`, `res_eS`, `eS_congr`, `coactP_fst`/`coactP_snd`, and the uniqueness part of `glue HM`. Replacing those uses by hypotheses gives the general clause (D). The claim is confirmed.
- The "over T" step is correct. Uniqueness of `glue` with P = yoneda.obj T (an algebraic space by `isAlgebraicSpace_yoneda`) forces the two maps Spec Pu → T to agree. This uses only that f₁ and f₂ are T-morphisms.

## Not verified
- The body of 07SY (sorry). I did not re-fetch the Stacks statement of 07SY or 0ET0; I relied on the prover's live check and on corrections-verified.md.
- Coassociativity and counit of `coactP` (plan item 3). These are not in the repo yet. The argument via surjectivity of π₁ is sound but has not been written.

## Small caveat
In Lean, clause (D) will be stated with the action written through the universal point (the `ss aX (eS ...)` form), as in `ha`. That matches the printed meaning of "D(M)_T-equivariant", but the restatement should keep this exact form.

Per statement: Fact 11.8 is ACCEPTED: UNRESTRICTED, no added hypothesis; the only remaining defect is that clauses (A, spaces), (C) and (D) are not yet stated as separate lemmas.
