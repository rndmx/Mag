# Lemma 4.2 (`AffineStratum`): state

Target: `AffineStratum X act` (AlgMag/ChartEffectiveMain.lean:857), as needed by `effective_of_noetherian_atlas` (AlgMag/ChartStrata.lean:1040), with hypotheses: algebraic space, `Space.IsSeparatedOver`, `AddMonoid.FG M`, noetherian. Goes in `AlgMag/ChartStratum.lean` (not yet created).

Route: quotient by bootstrap 04S6, not gerbe 06RC. Reason: the bootstrap statement is on presheaves and needs few stubs; 06RC needs `AlgebraicStacks`, a reduced `[X'/G]` and a way back to `X`. This is unproved mathematics until formalized; steps 1 and 2 depart from the note (reported).

## Done, compiled, axioms [propext, Classical.choice, Quot.sound]
- Step 2, ring: `AlgMag.ChartStratum.exists_stab_subgroup`, AlgMag/ChartStratumRing.lean.
- Step 2, geometry: `exists_stabIdeal`, `hmul_of_stabIdeal`, `exists_generic_stabilizer`, AlgMag/ChartStratumStab.lean. For `p : X.obj (op V)`, `V` affine with `Γ(V)` a noetherian domain, `X` separated, `M` f.g.: there are `s ≠ 0` and `Z ≤ M` such that for `t : T ⟶ V` with `s` a unit on `T` and `h` a point of `D(M)`: `h • p|T = p|T` iff `h` is trivial on `Z`.

- Step 3, stabilizer half: `OrbitLocal`, `smul_eq_iff_of_orbitLocal`, AlgMag/ChartStratumOrbit.lean. `OrbitLocal` is the fppf-local orbit of `p`; not yet identified with the open image.
- Step 4: `descAction`, `descAction_toMagnet`, `descAction_free` (same file), from `existsUnique_glue`, `extSieve_mem` (Sec8Representability). Needs `AddGroup.FG M`. `hfree` of step 5 (`a•x = b•x → a = b`) is not yet derived from `descAction_free`: use `zInv`.
- Step 5, formal half: `relP`, `relSrc`, `relTgt`, `relJ`, `relJ_isEquivalenceRelation`, AlgMag/ChartStratumRelation.lean; `dZ`, `relP_isPullback`, `relP_isAlgebraicSpace`, AlgMag/ChartStratumQuotient.lean. Base is the terminal presheaf.

## Not done
Next, in order:
a. `IsFlat`/`IsLocallyOfFinitePresentation` of `(relJ β).source.left`, `.target.left`. Write `terminal.from (yoneda D(Z)) = yoneda.map _ ≫ (Space.yonedaTerminalIso).hom`; scheme flatness from `flat_terminal_AZ` (Sec13General.lean:1011) by base change; the yoneda criterion is the private `flat_yoneda_map` (Spaces/Pushouts/FormalGlueingCovering.lean:327, via `holdsOnEveryEtaleChart_iff_representable`); base change as in `isFppfCovering_fibreProduct` (CoveringComparison.lean:145). Target: `(a,x) ↦ (a, a•x)` is an automorphism of `relP`, then `relSrc`.
b. Open image: `flatImage` (Spaces/FlatImageOpenSubspace.lean, real, compiled in cs/stub/out), plus `surjectiveFlatLfp_pullback_snd_of_fac` to show its points are `OrbitLocal`.
c. Step 7: `exists_fppf_isPullback_pullback_toQuotientSheaf` (Spaces/Bootstrap04S6Carriers.lean:340) gives exactly the fppf-local triviality of `Y -> Q`; closure 2616 modules, so stub it, together with `isPullback_toQuotientSheaf`.
d. Step 6 noetherian descent (the hard part: quasi-separatedness of `Q`, via `R -> Y x Y`), then 8, then 1. Original list:
1. Reduce to reduced `X` with `D(M')` smooth. If `X[1/n]` is nonempty (`n` the torsion order of `M`) take it, `M' = M`. Otherwise pick `p | n` with `X[1/(n/p^a)]` nonempty; `p` is nilpotent there; `M' = M/M[p^oo]`. `D(M')` acts on `X_red`: `D(M') x V` is reduced for reduced charts `V` and lands set-theoretically in `X_red`. Stability under all of `D(M)` comes from field-valued points, since a character on a characteristic `p` field kills `p`-torsion. Return with `exists_isOpenSubspace_isAffineSpace_of_reduction` (Spaces/CodimensionOneSchematicLocusByFlattening.lean:128). `reduction`: Spaces/Reduction.lean:162.
3. Saturate: `X_0` = open image of `G x V'` (`V' = D(s)` of an integral chart). On `X_0`, `h • x = x` iff `h` is trivial on `Z`, fppf-locally from step 2 since `G` is commutative.
4. Descend the action to a free `D(Z)` action on `X_0` along the fppf cover `T x_{D(Z)} D(M) -> T`; two lifts differ by a point killing `Z`, which fixes `x`.
5. `bootstrap04S6QuotientSheaf` (Spaces/Representable/Bootstrap/FlatRelationQuotient.lean:3731; the Prop is `Bootstrap04S6QuotientSheaf`, Spaces/EtaleSheafSpaceCoverCriterion.lean:595) with `R = D(Z) x X_0`, gives `Q`. Check the source's `PreRelation`: Spaces/EquivalenceRelations.lean:64.
6. Affine open of `Q`: `exists_dense_affine_openImmersion_self` (Spaces/AffineEtaleEnlargementOfOpen/Enlargement.lean:409), which needs `IsNoetherian` for `Q` (Spaces/NoetherianSpaces.lean:56). This requires descending quasi-compact, quasi-separated and locally noetherian along `X_0 -> Q`. Alternative without noetherian: `DenseSchematicLocusDecent` / `exists_denseRange_isRepresentable_isOpenSubspace_of_isAlgebraicSpace` (Spaces/DenseSchematicLocus.lean:881).
7. Affineness along the torsor `U -> W`, base changed to an atlas it is `D(Z) x V -> V`: `isAffineHom_isLocalAtTarget_fpqc` (Spaces/Descent/Fpqc/Integral.lean).
8. Assemble.

## Practical
- Current compile: `bash scratchpad/cs/run.sh Module [lines]` prints errors only (full log `cm2/out/AlgMag/Module.olean.log`). Stub-tree modules: `bash scratchpad/cs/bs.sh Dotted.Module`; extract real unbuilt modules with `cs/ext.py`, closure sizes with `cs/clo.py`. `cs/stub/out` is a hard-linked copy of `ef/stub/out`. Do not call `python3` (Store alias, hangs); use `python` with `cygpath -w`.
- A `variable (s : Γ(...))` bound silently elaborated to `sorry` with no error message: bind such terms in the signature, and check `#print axioms`.
- Compile: `bash scratchpad/cm2/c.sh Module`; with stubs `scratchpad/ef/sc.sh file out`. Lean resolves `AlgMag.*` only in the first path holding `AlgMag`, so every dependency olean must be in `cm2/out`. I hard-linked those of `fprn/ol` there.
- Almost all of Spaces/ above is unbuilt (e.g. `FlatRelationQuotient` has 2,508 unbuilt modules in its closure), so stubs must be handwritten.
- No bare heredocs containing apostrophes: use files. `/tmp` is not visible to Windows python.

## Progress 2026-11-06 (am), second session (all compiled)
- a: `relJ_flat_lfp`, `quotient_isAlgebraicSpace` (ChartStratumFlat.lean). axioms clean except the bootstrap stub.
- b: `orbMap`, `orbSub`, `orbSub_isOpen`, `exists_lift_of_mem_orbSub`, `smul_mem_orbSub` (ChartStratumImage.lean).
- c: `exists_affine_preimage_gen`, `relJ_source_isAffineHom` (ChartStratumAffine.lean). Stubs: cs/stub Bootstrap04S6Carriers, Descent/IndQuasiAffineFpqcSheaf.
- d: `isQuasiSeparated_quotient` (ChartStratumQS.lean). Route: not IsNoetherian; Q abs. qs (via map to an AFFINE OPEN A of S, since S need not be qs: the orbit lies over A) -> decent (`isDecentSpace_of_isAbsolutelyQuasiSeparated`) -> `exists_denseRange_..._of_isDecentSpace` (086U). `exists_affine_open_of_absQS`, `isQuasiSeparated_of_mono` (ChartStratumDecent.lean).
- Next: ChartStratumCore (step 8 on an integral etale chart), then step 1.
- Step 8 (on integral chart): `exists_stable_affine_of_orbit` (ChartStratumCore.lean), `exists_stable_affine_of_chart` (ChartStratumChart.lean): etale chart V affine domain noetherian over an affine open A of S gives the nonempty affine stable open. Compiled.
- Remaining: step 1. Plan: R1 ring lemma R[M'] reduced (torsion killed by a unit); R2 MonAff reduced; R3 x in X(T), T reduced => x in X_red(T); R4 action of D(M') on X_red; R5 integral chart over affine open; R6 X[1/n'] open stable; R7 back to X (open with same points, affine by isAffineSpace_of_isClosedImmersion_of_isSurjective, stable on field points).
- Step 1 progress: `isReduced_addMonoidAlgebra` (ChartStratumReduced.lean), `isReduced_monAff`, `isReduced_top`, `mem_of_isReduced`, `smul_mem_reduction` (ChartStratumRedAction.lean, axioms clean). Still: R5 chart, R6 X[1/N], R7 return.
- R6 `invSub`, `mem_invSub_iff`, `invSub_isOpen` (ChartStratumInv.lean); R5 `exists_integral_chart` (ChartStratumIntegral.lean). Next: R7 (ChartStratumBack.lean: G' = openSubspaceOfPoints of image of U' in Z), exists N,K, final AffineStratum in ChartStratum.lean.
- R7 `exists_stable_open_of_reduction` (ChartStratumBack.lean) compiled. Next: `exists_unit_data` (ChartStratumData.lean), then AlgMag/ChartStratum.lean.

## DONE 2026-11-06: `AlgMag.ChartStratum.affineStratum`, AlgMag/ChartStratum.lean
Statement: `IsAlgebraicSpace X`, `IsSeparatedOver X`, X locally noetherian (etale local), `AddMonoid.FG M` give `ChartMain.AffineStratum X act`. Corollary `affineStratum_closedStable` is the form `effective_of_noetherian(_atlas)` needs (h42).
Axioms: propext, Classical.choice, Quot.sound, plus sorryAx ONLY through 14 stubs in scratchpad cs/stub (checked with cs/W.lean, which lists constants directly using sorryAx). The repo files contain no sorry. Stubbed Stacks results (real file):
- Spaces/Representable/Bootstrap/FlatRelationQuotient.lean:3731 bootstrap04S6QuotientSheaf; Spaces/ChangeOfBigSite.lean:157 hasSheafify_bigFppfOver
- Spaces/Bootstrap04S6Carriers.lean: of_isPullback_yoneda_map_of_fppf (243), exists_single_fppf_lift_of_isLocallySurjective (130), exists_fppf_isPullback_pullback_toQuotientSheaf (340)
- Spaces/Quotients/CoveringMap.lean: isLocallySurjective_toQuotientSheaf (141), isPullback_toQuotientSheaf (231)
- Descent/IndQuasiAffineFpqcSheaf.lean:86 isLocalAtTarget_isAffineHom_fpqc
- Spaces/Morphisms/QuasiCompact.lean:139 isQuasiCompact_of_comp_of_isQuasiSeparated
- Spaces/SpectralPoints.lean:112 isDecentSpace_of_isAbsolutelyQuasiSeparated; Spaces/DenseSchematicLocusDecent.lean:322 086U
- Spaces/FpqcOpenSubspaceDescent.lean:184 isOpenSubspace_preimage; Spaces/QuasiFiniteLocusOnCharts.lean:131 pointsRange_preimage
- Spaces/Thickenings/AffineOfAffineClosedSubspace.lean:142 isAffineSpace_of_isClosedImmersion_of_isSurjective
Repo imports name the real modules; check once the sparse build has them. Real extracted (not stubs): FlatImageOpenSubspace, Reduction, Affine, AbsolutelyQuasiSeparatedAffine, FiniteEtaleAtlasQuasiSeparated, QuasiCompactEtaleLocalTarget, Descent/LocalProperties/Noetherian, LocallyNoetherianFiniteType, UniversallyClosedPermanence.
Route of the proof (departs from the gerbe of the printed proof): reduce to X[1/N]_red with D(M/K) (`exists_unit_data`, `smul_mem_reduction`); integral chart over affine open A of S (`exists_integral_chart`); generic stabilizer Z; open orbit Y; free D(Z) on Y; Q=Y/D(Z) algebraic by 04S6; Q -> A quasi-separated (`isQuasiSeparated_quotient`), so Q absolutely qs, decent, has an affine open (086U); preimage in Y affine (041Z); back to X via 07VT (`exists_stable_open_of_reduction`).
