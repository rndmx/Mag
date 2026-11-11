# State: descent of X + D(M)-action to a stage (AlgMag/SpacesLimitAction.lean)

Compile: scratchpad/lma/k.sh (ROOT=repo ./k.sh AlgMag/SpacesLimitAction <file>); overlay lma/ov is hard links of cma/ov plus a stub of Spaces/Limits/FinitePresentationDescent (lma/src/StacksFrontier/...). Not for AlgMag.lean until a full-Stacks compile.

Done: exists_action_model (07SK on action and axioms), Model.restrict, actGood_of_representable, exists_stage, Model.closed_of_stage, strongAtlas_of_limit, closed_of_limit_torsionFree.

Open:
1. Discharge LimitData for L = yoneda T over Spec Z: stageSystem_* and stageLimitIso (Quot/CoherentStackAffineApproximation), hpi by Space.presheaf_yoneda_map_iff, sepDesc by MorphismDescentSituation.exists_isSeparated_mapAt_of_siteContainsBaseChangeLimits as in exists_stageModelSE; stageSep/stageFT/stageCharts by composition.
2. ActGood input over Spec Z: G0 = Spec Z[M] (SecFinal1316.cU), finite presentation of yoneda.map.
3. Transport S-site <-> Z-site: action on viewOverIntegers X (points (psi, s), Gamma is the same), and an atlas of the view gives an atlas of X over S (etale/surjective: presheaf_relocalizeMap; FPR pointwise).
4. General S: affine cover of S, coproduct of atlases.
5. A.1 (ii) with torsion: TorsionResidue fails over Spec Z, so run thmA1_closed on the site of the stage T_k; connected fibres at the stage: p nilpotent in R gives p nilpotent in the f.g. subring. FPR clause needs descent of U -> X (orbit opens D(M)V). 'Of finite presentation' clause not started.

## AlgMag/SpacesLimitFinal.lean (2026-11-06)
Compile: scratchpad/lmf/fin.sh SpacesLimitFinal (k.sh there; oleans into lma/ov; stubs and real copies in lmf/src, compile with lmf/k.sh <path>). Stubs: Quot/CoherentStackAffineApproximation, Spaces/DescendingProperties/SeparatedMorphismDiagonalDescent, Spaces/Limits/QuasiAffineClosedInFinitePresentation; Spaces/Limits/DescendingMorphisms is verbatim.
Done: steps 1-2: limitDataZ, actGoodZ.

## AlgMag/SpacesLimitOrbit.lean (2026-11-06)
Compile: lmf/fin.sh SpacesLimitOrbit. Done, for arbitrary S: actGood_of_fg, flat_actSnd (G0 = monAffObj over T1), exists_orbit (W' = orbit act W, also keeps LiesOver), exists_cover. No new stubs. sorryAx in #print axioms comes only through the existing stub of Limits/QuasiAffineClosedInFinitePresentation (isFinitePresentation_yoneda_map, public in Stacks); exists_cover is axiom-clean.

## AlgMag/SpacesLimitView.lean (2026-11-06)
Compile: scratchpad/lmf/fin.sh SpacesLimitView. Compiled, no sorry in the file. Step 3 of Open done: viewAct, exists_chart_of_view (chartObj/chartAct/chartMap, map_chartMap, chartMap_etale/surjective, chart_isZFPR/StronglyFPR, chart_isStableOpen, chart_isAffineHom), isFinitePresentation_viewMap, view_isAlgebraicSpace, viewMap_invariant, closed_of_view, isFinitePresentation_of_view.
New stubs in lmf/src: Spaces/ProperSmallerBase (presheaf_relocalizeMap_of, isQuasiCompact_relocalize_iff, isQuasiSeparated_relocalize_iff), Spaces/FinitePresentationSliceGlueing/FppfMayerVietoris (isFinitePresentation_of_arrowIso). Not for AlgMag.lean until a full-Stacks compile.
Not done: the covers field of EtaleChartFamily for chartMap (only the presheaf Surjective comes back).

## AlgMag/SpacesLimitStage.lean (2026-11-06)
Compile: scratchpad/lmf/fin.sh SpacesLimitStage. Done, no sorry in the file: torsionResidue_of_nilpotent, torsionResidue_of_injective, exists_stage_torsion (i0 = empty: every subring works), Fib/descAct/mem_fix_iff (action on the fibre of p over T0), closed_of_site_stage, isFPR_of_site_stage, fp_of_closed_noetherian, fixedPoints_fp_of_site_stage; stated for any site base S, T0 any object.
New stubs in lmf/src (sorryAx until a full-Stacks compile): Stacks/PresheafRepresentability, Spaces/ProperSmallerBase, Spaces/ClosedImmersionSmallerBase, Spaces/Morphisms/ClosedImmersionFinitePresentation, Spaces/EtaleChartEquivalence; CategoryTheory/Sites/Localization/RelocalizeFibre is verbatim.
Open: wire to limitDataZ stage (T0 = Spec Z[i], with the model action; isFPR needs U descended to the stage); steps 3-4.

## AlgMag/SpacesLimitLocal.lean (2026-11-06)
Compile: scratchpad/lmf/fin.sh SpacesLimitLocal. Compiled. Shared lemmas for A.1/A.2: restrictAct, toBase, isFinitePresentation_toBase, isSeparated_toBase, viewBase, isSeparated_viewBase, isStronglyFPR_comp_mono, isEtale_comp_ι, exists_atlas_of_fp. New stub: FormalSpace/ModificationOutputQuasiCompact (isQuasiCompact_of_isQuasiCompactSpace_of_isAffine).

## AlgMag/SpacesLimitThm68.lean (2026-11-06)
Compile: scratchpad/lmf/fin.sh SpacesLimitThm68. Compiled, no sorry in the file, h5 (chart lemma over Spec Z) and hM (Spec Z[M] in the site) explicit. Done: exists_stable_open, ChartFamily, exists_charts (S arbitrary), thm68_family (S separated), thm68_qc (S separated, X qc), thm11_affine (S affine), thm68_ii_of_charts, thm68_ii_qc (given charts). Steps 3-4 of Open are done modulo h5.
Open: h5; coproduct of an infinite family in the site (size bound); AHR charts for non-separated X in (ii); A.1 wiring (later agent, use SpacesLimitLocal).

## AlgMag/SpacesLimitA1.lean (2026-11-06)
Compile: scratchpad/lmf/fin.sh SpacesLimitA1. Compiled, no sorry in the file. Done: mem_fixed_of_site_stage, exists_stage_local, mem_fixed_of_fnAll_local, a1_closed_local, exists_cover_point, mem_fixed_of_fnAll, fixedPoints_eq_fnAll, a1_isClosedImmersion, a1_closed, a1_isFPR, a1_isZFPR, chartsOfFiniteType_of_lfp, a1_closed_noetherian, a1_isFPR_noetherian. Theorem A.1 for D(M), TorsionResidue M S, S arbitrary; hZ : B.Contains (⊤_ Scheme) explicit in case (ii). Route: X^G = X_0 pointwise (locally on T in a stable W, at the stage of W); closedness is then presheaf_fnAll_ι, which needs no noetherian hypothesis, so no gluing of closed subspaces. FPR needs only U lfp qs: mem_fnFixed_of_etale plus X^G = X_0 on U; no descent of U -> X.
New stub: Spaces/FinitePresentationLocalAtTarget (isFinitePresentation_of_zariskiCover), used for the fp clause of a1_closed. a1_isFPR_noetherian is axiom-clean.
