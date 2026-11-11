# AlgMag code metrics

Generated 2026-11-06 by a static text scan of the working tree (git HEAD 7e79b27 plus uncommitted changes). Nothing was compiled.

Method limits: declarations are found by line-anchored regex after removing comments. Declarations produced by macros or `to_additive`, and uses produced by `simp` attributes or instance search, are not seen. Proof length means lines from the declaration keyword to the next declaration, so it includes the statement.

## Totals

| Measure | Count |
|---|---|
| Lean files | 343 |
| Total lines | 128559 |
| Non-blank code lines (comments removed) | 102524 |
| theorem + lemma | 5066 |
| def + abbrev | 2262 |
| instance | 170 |
| structure + class + inductive | 145 |
| axiom | 0 |
| example | 3 |
| `sorry` tokens | 1 |
| Files containing `sorry` | 1 |

## Largest 20 files

| File | Lines | Theorems | Defs | Longest proof | sorry |
|---|---:|---:|---:|---:|---:|
| AlgMag.ChartGraded | 2473 | 106 | 30 | 207 | 0 |
| AlgMag.Sec5Etale | 2317 | 102 | 25 | 235 | 0 |
| AlgMag.SecFinal1316 | 2248 | 61 | 24 | 210 | 0 |
| AlgMag.Sec9General | 2206 | 128 | 68 | 65 | 0 |
| AlgMag.AppendixA3 | 2093 | 71 | 20 | 276 | 0 |
| AlgMag.Sec8Theorem83 | 1764 | 46 | 16 | 194 | 0 |
| AlgMag.Sec3SchemeQuotient | 1736 | 84 | 21 | 106 | 0 |
| AlgMag.Sec9OverB | 1727 | 108 | 61 | 62 | 0 |
| AlgMag.Sec13Spaces | 1593 | 53 | 25 | 173 | 0 |
| AlgMag.Sec3Remaining | 1560 | 48 | 47 | 142 | 0 |
| AlgMag.ChartAlgebraize | 1548 | 46 | 14 | 117 | 0 |
| AlgMag.Sec13General | 1512 | 76 | 41 | 59 | 0 |
| AlgMag.Sec8Limits | 1462 | 57 | 20 | 107 | 0 |
| AlgMag.Sec12Final | 1416 | 29 | 4 | 174 | 0 |
| AlgMag.Sec12Topology | 1371 | 44 | 32 | 164 | 0 |
| AlgMag.Sec8Representability | 1341 | 48 | 22 | 176 | 0 |
| AlgMag.Sec3Final | 1291 | 57 | 16 | 112 | 0 |
| AlgMag.SelfActionsExamples | 1217 | 60 | 18 | 80 | 0 |
| AlgMag.Sec16Remaining | 1138 | 29 | 36 | 105 | 0 |
| AlgMag.AppendixRemaining | 1091 | 29 | 16 | 186 | 0 |

## Roots and files outside any root

Roots from lakefile.toml: `AlgMag`, `AlgMagBuilt`. Reachable by import from `AlgMag`: 340 files. From `AlgMagBuilt`: 232 files. In `AlgMag` only: 109. In `AlgMagBuilt` only: 1.

Outside both roots: 2 files, 288 lines.

- AlgMag.FinalMiscProp91 (125 lines, 1 sorry)
- AlgMag.FinalNonQCAtlas (163 lines, 0 sorry)

## Import depth

Maximum internal import depth: 42. Deepest file: `AlgMag.FinalNonQCAtlas`. Internal edges: 1134. External import roots: Mathlib (360), StacksFrontier (232), SZ (1).

Longest chain, top first:

FinalNonQCAtlas -> FinalCorAtlas -> FinalCorBridge -> FinalAtlasFree -> FinalThm68Single -> ChartFinalSpaces -> SpacesLimitThm68 -> SpacesLimitLocal -> SpacesLimitView -> SpacesLimitFinal -> SpacesLimitAction -> ChartThm68 -> ChartMain -> ChartStratum -> ChartStratumData -> ChartStratumBack -> ChartStratumIntegral -> ChartStratumInv -> ChartStratumRedAction -> ChartStratumChart -> ChartStratumCore -> ChartStratumDecent -> ChartStratumQS -> ChartStratumAffine -> ChartStratumImage -> ChartStratumFlat -> ChartStratumQuotient -> ChartStratumRelation -> ChartStratumOrbit -> ChartStratumStab -> StronglyFPRStab -> Sec8Representability -> GeneralBaseCor -> GeneralBaseThm320 -> GeneralBaseAttractor -> GeneralBaseLocal -> GeneralBaseGrading -> Sec3Affine -> Affine.Naturality -> Affine.Representability -> Affine.Attractor -> Affine.MagnetAlgebra -> Affine.Magnet

Most imported files:

- AlgMag.Sec3Functorial: 12
- AlgMag.GeneralBase: 12
- AlgMag.Sec12Topology: 11
- AlgMag.Representation: 11
- AlgMag.Foundations: 10
- AlgMag.Sec8Representability: 10
- AlgMag.GeneralBaseCore: 9
- AlgMag.Sec6FPR: 9
- AlgMag.AlgebraicSpace: 9
- AlgMag.ChartConclude: 9

Files imported by no Lean file, other than the two roots: 2.

- AlgMag.FinalMiscProp91
- AlgMag.FinalNonQCAtlas

## Duplicated declarations

- Same fully qualified name in two or more files: 0 names (0 with at least one non-private copy). Non-private copies would clash if both files were imported together.
- Same last name component in two or more files: 446 names.
- Declarations with identical text up to their own name, at least 2 lines: 52 groups, 51 of them across files; redundant lines about 818.
- Theorems with identical statements but different proofs: 22 groups.

Top groups with identical text:

| Lines | Copies | Name | Locations |
|---:|---:|---|---|
| 140 | 2 | eq_on_overlap | ChartInputs; ChartSplit |
| 79 | 2 | bhatt14 | ChartInputs; ChartSplit |
| 78 | 2 | eq_zero_of_flat_of_annihilated_of_mem_pow | ChartInputs; ChartSplit |
| 52 | 2 | isIso_of_isClosedImmersion_of_factors | ChartInputs; ChartSplit |
| 44 | 2 | decompOf | Sec9General; Sec9OverB |
| 32 | 2 | existsUnique_glue_of_fpqc | ChartInputs; ChartSplit |
| 32 | 2 | actSnd | Sec16Gm; Sec16Remaining |
| 31 | 2 | exists_closed_equalizer | ChartInputs; ChartSplit |
| 26 | 2 | adicFibreMap_eq_sectionFibreMap_iff | ChartInputs; ChartSplit |
| 22 | 2 | glue | Sec16Gm; Sec16Remaining |
| 18 | 2 | piP_mul | ChartConclude; ChartS5Graded |
| 17 | 2 | theta_basis | Sec9General; Sec9OverB |
| 16 | 2 | map_eq_zero_of_factor | ChartInputs; ChartSplit |
| 14 | 2 | suppHom | Sec12Final; Sec12GenericSmall |
| 8 | 3 | val_predAbove' | Sec9General; Sec9Hochschild; Sec9OverB |
| 11 | 2 | ofArrows_two_mem_fpqcPrecoverage | ChartInputs; ChartSplit |
| 11 | 2 | sectionFibreMap_succ | ChartInputs; ChartSplit |
| 10 | 2 | exists_lift_sch_pullback | ChartInputs; ChartSplit |
| 10 | 2 | val_succAbove' | Sec9General; Sec9OverB |
| 9 | 2 | retrP | DoubleScalarSpaces; PrintedSec164 |
| 9 | 2 | secP | DoubleScalarSpaces; PrintedSec164 |
| 8 | 2 | phiN_bijective | Sec9General; Sec9OverB |
| 7 | 2 | etale_comp_of_range | ChartEtaleLocus; ChartS5Chart |
| 7 | 2 | sectionFibreMap | ChartInputs; ChartSplit |
| 7 | 2 | suppHom_single | Sec12Final; Sec12GenericSmall |

Repeated fully qualified names, most copies first (first 30):


Same statement, different proof (first 15):

- FixesSec14:remark142_apply, FixesSec14:indHomEquiv_eq_canon, Sec12Final:exists_indHom_term, Sec14Strong:indHomCanon_eval, Sec14Strong:indHomCanon_eq_mk, Sec14Strong:indHomCanon_bijective
- ChartEtaleLocus:etale_of_forall_open, ChartS5Chart:etale_of_forall_open'
- ChartInputs:existsUnique_section_of_algebraization, ChartSplit:existsUnique_section_of_algebraization
- ChartMain:isAlgebraicSpace_terminal, Sec11SpacesCor:isAlgebraicSpace_top
- ChartPoint:exists_orbit, ChartPoint:orbit_injective
- ChartQSStab:closedι_appTop_eq_zero_of_mem, ChartS5Chart:closedι_appTop_of_mem
- DoubleScalar:three_le_card_filter, PrintedDoubleScalar:three_le_card_filter_printed
- DoubleScalarChartAttr:chart_attr_iff, PrintedDoubleScalar:chart_attr_iff_lem42
- DoubleScalarChartAttr:gm_unit, Sec3Remaining:apt_unit
- FixesThm124:thm124_induced_face, Sec12SpacesThm:thm124_spaces_face
- PrintedProp85:prop85_printed, Sec8Limits:prop85
- PrintedSelfActions:prop42_printed, SelfActionsMain:prop42_scheme
- Sec10LiftsCor:exists_equivariant_lift_spec, Sec10PrintedCor:exists_equivariant_lift_spec
- Sec11PrintedFace:smooth_repFace, Sec11SchemesRep:smooth_repFace
- Sec11PrintedProps:isFormallySmooth_attractorMap_scheme, Sec11Schemes:isFormallySmooth_attractorMap_scheme

## Near-duplicate proof blocks

Window test: 12 consecutive normalized code lines repeated anywhere. 1687 repeated windows. Lines covered by a repeated window: 4853 of 102524 (4.7%).

File pairs sharing the most windows:

| Shared windows | File A | File B |
|---:|---|---|
| 487 | ChartInputs | ChartSplit |
| 206 | Sec16Gm | Sec16Remaining |
| 171 | Sec9General | Sec9OverB |
| 146 | Sec11PrintedProps | Sec11SchemesFace |
| 115 | Sec12Final | Sec12GenericSmall |
| 61 | ChartMain | ChartPointOrbitInput |
| 56 | Sec10LiftsCor | Sec10PrintedCor |
| 48 | Sec12Final | Sec12PrintedThm |
| 42 | Sec11PrintedProps | Sec11Schemes |
| 39 | Sec8Representability | Sec8Theorem83 |
| 37 | Sec14Ind | Sec14Remaining |
| 33 | Sec12PrintedRing | Sec12SymRing |
| 27 | PrintedProp85 | Sec8Limits |
| 24 | ChartAtlas | Sec6Atlas |
| 19 | ChartDeligne | ChartDeligneLim |
| 17 | Sec16Remaining | SecFinal1316 |
| 16 | Sec12Final | Sec12PrintedLocal |
| 15 | Sec12Final | Sec12Spaces |
| 14 | ChartPoint | ChartQSStab |
| 13 | AppendixA3 | AppendixRemaining |

Files with most lines covered:

- AlgMag.ChartSplit: 498 of 527
- AlgMag.ChartInputs: 498 of 546
- AlgMag.Sec9General: 313 of 1687
- AlgMag.Sec9OverB: 292 of 1317
- AlgMag.Sec12Final: 282 of 1201
- AlgMag.Sec16Remaining: 278 of 889
- AlgMag.Sec16Gm: 250 of 460
- AlgMag.Sec11PrintedProps: 232 of 261
- AlgMag.Sec11SchemesFace: 168 of 388
- AlgMag.Sec12GenericSmall: 148 of 178
- AlgMag.Sec10LiftsCor: 100 of 224
- AlgMag.Sec10PrintedCor: 100 of 223
- AlgMag.PrintedSec164: 79 of 247
- AlgMag.ChartPointOrbitInput: 72 of 207
- AlgMag.ChartMain: 72 of 384

Identifier-abstracted test: theorems of at least 8 lines with the same shape after replacing every identifier, but different text: 22 groups. Top 15:

- 43 lines x2: Sec9General:toPt_dup, Sec9OverB:toPt_dup
- 23 lines x2: Sec9General:delta_phiC_single, Sec9OverB:delta_phiC_single
- 23 lines x2: Sec9General:exists_delta_eq, Sec9OverB:exists_delta_eq
- 18 lines x2: Sec9General:evalE_tval_mul, Sec9OverB:evalE_tval_mul
- 17 lines x2: Sec9General:dsmul_one, Sec9OverB:dsmul_one
- 15 lines x2: Sec11PrintedFace:smooth_repFace, Sec11SchemesRep:smooth_repFace
- 15 lines x2: Sec9General:coef_finite, Sec9OverB:coef_finite
- 14 lines x2: Sec9General:dsmul_smul, Sec9OverB:dsmul_smul
- 13 lines x2: Sec9General:phiN_bijective_compact, Sec9OverB:phiN_bijective_compact
- 12 lines x2: Sec9General:evalE_resF, Sec9OverB:evalE_resF
- 12 lines x2: Sec9General:comp_evalE_tval, Sec9OverB:comp_evalE_tval
- 10 lines x2: Sec9General:ofPt_toPt, Sec9OverB:ofPt_toPt
- 9 lines x2: FinalRem158:rem158, SecLeftover158:rem158_printed
- 9 lines x2: Sec12PrintedSchemes:isFace_unitsOf, Sec8Theorem83:isFace_unitsSub
- 9 lines x2: Sec9General:evalE_res, Sec9OverB:evalE_res

## Leftover-style names

File names matching a provisional pattern: 98 of 343.

| Pattern | Files | Examples |
|---|---:|---|
| digits/numbered suffix | 48 | AppendixA3, ChartFormal2, ChartPointLemma11, ChartS5Step6, ChartSection5, ChartThm68 |
| Leftover | 36 | Sec3Leftover, Sec3Leftover12, Sec3Leftover2, Sec3Leftover221, Sec3Leftover221Act, Sec3Leftover221Eq |
| Final | 31 | ChartEffectiveFinal, ChartFinal, ChartFinalSpaces, ChartPointFinal, ChartS5Final, FinalAtlasFree |
| Fixes | 6 | FixesEx333, FixesFact26, FixesFact26ii, FixesSec14, FixesSec16, FixesThm124 |
| Remain | 4 | AppendixRemaining, Sec14Remaining, Sec16Remaining, Sec3Remaining |
| Misc | 2 | FinalMisc164, FinalMiscProp91 |
| Stub | 1 | ChartStubs |
| Rest | 1 | Sec3Rest |

Declarations with such names: 37. First 20: `mem_fixedPoints_of_cover`, `mem_fixedPoints_of_fnAll`, `oAct_fix`, `thm11_ft_final`, `col_fixed`, `rng_eq_span_of_fixed`, `isFixedPoint_iff_mem_fixedPoints`, `exists_fixed_of_H1_eq_zero`, `twist_of_fixed`, `tangentFinalIso`, `mem_fixed_of_bi`, `mem_fixedPoints_inf`, `mem_fixed_piece`, `AttractorPt.toPoint_mem_fixedPoints`, `mem_fixedPoints_quotient_iff`, `smul_eq_of_fixed`, `overSmul_eq_of_fixed`, `exists_att_of_fixed`, `exists_closed_fixed_open`, `exists_closed_fixed`.

## Long proofs

Theorems and lemmas: 5066. Median length 8 lines.

| Length at least | Count |
|---:|---:|
| 50 | 363 |
| 100 | 87 |
| 200 | 8 |
| 500 | 0 |
| 1000 | 0 |

Longest 15:

| Lines | Name | File |
|---:|---|---|
| 278 | exists_stab_subgroup | ChartStratumRing |
| 276 | eqNear_unit | AppendixA3 |
| 235 | faceComparison_surjective_affine | Sec5Etale |
| 231 | exists_eqLocus_gluing | Sec14Glue |
| 230 | lemma11 | ChartPointLemma11 |
| 210 | exists_good_basicOpen | ChartPointL11Generic |
| 210 | exists_pres_of_conormal | SecFinal1316 |
| 207 | exists_gens | ChartGraded |
| 199 | mem_range_field | Sec12PrintedLocal |
| 194 | thm83_core | Sec8Theorem83 |
| 193 | exists_affineTower | ChartTower |
| 189 | isFormallySmooth_faceMap_spaces | Sec11SpacesFace |
| 186 | step_free | AppendixRemaining |
| 180 | rem66 | DoubleScalar |
| 178 | exists_ofLE_of_chart_03I2 | PrintedProp85 |

## Unused lemmas, by grep

Theorems, lemmas and defs whose last name component never occurs anywhere else in the Lean sources: 295, about 2785 lines; 293 of them lie in files under a root.

This overcounts true dead code: final results of the formalization, attributes such as `simp`, dot notation and generated uses all look unused here. It undercounts when a name also appears as an unrelated token, and it does not chase chains of lemmas used only by unused lemmas.

Files with the most such declarations:

- AlgMag.Sec3Functorial: 17
- AlgMag.Sec3Affine: 14
- AlgMag.Sec2Monoids: 13
- AlgMag.Sec15PureMagnets: 12
- AlgMag.Sec3Remaining: 12
- AlgMag.Sec2OverB: 9
- AlgMag.Sec9General: 8
- AlgMag.ChartGraded: 7
- AlgMag.SelfActionsMain: 7
- AlgMag.DoubleScalarCombi: 6
- AlgMag.GeneralBase: 6
- AlgMag.ChartAlgebraize: 5
- AlgMag.ChartEffective: 5
- AlgMag.ChartS5Graded: 5
- AlgMag.Sec16Lie: 5
- AlgMag.Sec16Remaining: 5
- AlgMag.SpacesLimitAction: 5
- AlgMag.SpacesLimitView: 5
- AlgMag.Sec10PrintedLifts: 4
- AlgMag.Sec14Remaining: 4

Largest such declarations:

- sym_lift_injective (Sec12SymRing, 93 lines)
- lemma_3_4_unique (ChartGraded, 84 lines)
- monoidRank_int_pi (Sec15PureMagnets, 83 lines)
- exists_equivariant_lift_scheme (Sec10LiftsCor, 76 lines)
- rem323 (Sec3Remaining, 73 lines)
- rem325 (Sec3Remaining, 71 lines)
- exists_fixed_of_H1_eq_zero (Sec10Deformations, 63 lines)
- retractFixedEquiv (Sec16Gm, 58 lines)
- pureMagnets_two_three (Sec15PureMagnets, 56 lines)
- isIndScheme_attractor (Sec14Remaining, 52 lines)
- exists_local_lift (Sec10Schemes, 50 lines)
- attractor_face_formallySmooth_affine (Sec11Formal, 46 lines)
- lemma_3_4_family_of_hom (ChartGraded, 38 lines)
- map_J_eq (Sec12PrintedRing, 37 lines)
- coactionEquivDecomposition (Sec9Hochschild, 37 lines)
- exists_limit_lift (ChartDeligne, 31 lines)
- lemma_3_4_hom_of_family (ChartGraded, 29 lines)
- attractor_formallyEtale_affine (Sec11Formal, 27 lines)
- not_isFreeAction_natNeOne (Sec2Monoids, 27 lines)
- toLine_smul (DoubleScalarChartAttr, 26 lines)
- attractorBotEquiv (Sec3Functorial, 26 lines)
- hModuleEquivCoaction_symm_smul (Sec9General, 26 lines)
- isEtaleAt_of_presentations (ChartAlgebraize, 25 lines)
- etale_chart (ChartAlgebraize, 24 lines)
- graded_nakayama (ChartGraded, 23 lines)

## Per file

| File | Lines | Thm | Def | Inst | Imports (internal) | Imported by | Depth | sorry | Root |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---|
| AlgMag | 339 | 0 | 0 | 0 | 339 | 0 | 42 | 0 | A |
| AlgMag.Affine.Attractor | 37 | 0 | 1 | 0 | 2 | 4 | 2 | 0 | AB |
| AlgMag.Affine.GradedHom | 161 | 11 | 3 | 4 | 0 | 3 | 0 | 0 | AB |
| AlgMag.Affine.Magnet | 44 | 2 | 2 | 0 | 0 | 3 | 0 | 0 | AB |
| AlgMag.Affine.MagnetAlgebra | 72 | 4 | 2 | 0 | 1 | 4 | 1 | 0 | AB |
| AlgMag.Affine.Naturality | 79 | 3 | 2 | 0 | 1 | 5 | 4 | 0 | AB |
| AlgMag.Affine.Representability | 215 | 10 | 6 | 0 | 1 | 5 | 3 | 0 | AB |
| AlgMag.AffineComparison | 330 | 11 | 15 | 0 | 2 | 5 | 5 | 0 | AB |
| AlgMag.AlgebraicSpace | 36 | 1 | 1 | 0 | 1 | 9 | 1 | 0 | AB |
| AlgMag.AppendixA | 561 | 18 | 9 | 1 | 1 | 9 | 4 | 0 | AB |
| AlgMag.AppendixA3 | 2093 | 71 | 20 | 1 | 3 | 6 | 13 | 0 | AB |
| AlgMag.AppendixRemaining | 1091 | 29 | 16 | 0 | 2 | 3 | 6 | 0 | AB |
| AlgMag.ChartActionGrading | 341 | 22 | 16 | 1 | 2 | 5 | 9 | 0 | AB |
| AlgMag.ChartAlgebraize | 1548 | 46 | 14 | 0 | 0 | 5 | 0 | 0 | AB |
| AlgMag.ChartArtin | 187 | 3 | 5 | 0 | 0 | 2 | 0 | 0 | A |
| AlgMag.ChartArtinFP | 192 | 7 | 2 | 0 | 3 | 2 | 12 | 0 | A |
| AlgMag.ChartAtlas | 233 | 5 | 0 | 0 | 1 | 4 | 6 | 0 | AB |
| AlgMag.ChartBridge | 202 | 9 | 2 | 0 | 2 | 5 | 10 | 0 | AB |
| AlgMag.ChartConclude | 488 | 16 | 10 | 2 | 3 | 9 | 11 | 0 | AB |
| AlgMag.ChartDeligne | 306 | 9 | 0 | 0 | 1 | 3 | 13 | 0 | AB |
| AlgMag.ChartDeligneCompat | 236 | 8 | 0 | 0 | 1 | 2 | 18 | 0 | A |
| AlgMag.ChartDeligneCore | 900 | 42 | 10 | 0 | 3 | 2 | 15 | 0 | A |
| AlgMag.ChartDeligneIdeal | 115 | 3 | 1 | 0 | 1 | 3 | 1 | 0 | AB |
| AlgMag.ChartDeligneInst | 355 | 10 | 1 | 0 | 1 | 2 | 20 | 0 | A |
| AlgMag.ChartDeligneLim | 453 | 22 | 4 | 0 | 1 | 2 | 16 | 0 | A |
| AlgMag.ChartDeligneOpen | 498 | 21 | 6 | 0 | 1 | 2 | 17 | 0 | A |
| AlgMag.ChartDeligneTheta | 219 | 10 | 0 | 0 | 1 | 2 | 19 | 0 | A |
| AlgMag.ChartEffective | 440 | 14 | 7 | 1 | 0 | 6 | 0 | 0 | AB |
| AlgMag.ChartEffectiveAlg | 286 | 8 | 5 | 0 | 1 | 2 | 14 | 0 | A |
| AlgMag.ChartEffectiveBridge | 127 | 2 | 0 | 1 | 2 | 3 | 11 | 0 | AB |
| AlgMag.ChartEffectiveFinal | 476 | 16 | 7 | 2 | 1 | 5 | 13 | 0 | AB |
| AlgMag.ChartEffectiveInduct | 164 | 3 | 1 | 0 | 1 | 4 | 12 | 0 | AB |
| AlgMag.ChartEffectiveMain | 871 | 26 | 4 | 0 | 4 | 4 | 10 | 0 | AB |
| AlgMag.ChartEtaleFlat | 143 | 3 | 0 | 0 | 0 | 4 | 0 | 0 | AB |
| AlgMag.ChartEtaleLocus | 695 | 28 | 8 | 2 | 2 | 4 | 12 | 0 | AB |
| AlgMag.ChartFinal | 56 | 3 | 0 | 0 | 2 | 2 | 35 | 0 | A |
| AlgMag.ChartFinalSpaces | 70 | 3 | 0 | 0 | 2 | 2 | 37 | 0 | A |
| AlgMag.ChartFormal | 184 | 11 | 7 | 0 | 2 | 2 | 31 | 0 | A |
| AlgMag.ChartFormal2 | 584 | 17 | 1 | 0 | 2 | 3 | 32 | 0 | A |
| AlgMag.ChartFormalC | 417 | 39 | 11 | 1 | 2 | 2 | 31 | 0 | A |
| AlgMag.ChartGraded | 2473 | 106 | 30 | 5 | 0 | 6 | 0 | 0 | AB |
| AlgMag.ChartGradedAction | 230 | 14 | 5 | 0 | 1 | 3 | 8 | 0 | AB |
| AlgMag.ChartIdealPow | 148 | 9 | 0 | 0 | 0 | 3 | 0 | 0 | AB |
| AlgMag.ChartInputs | 620 | 15 | 1 | 0 | 0 | 1 | 0 | 0 | A |
| AlgMag.ChartMain | 441 | 14 | 1 | 0 | 10 | 4 | 30 | 0 | A |
| AlgMag.ChartOrbit | 212 | 8 | 6 | 1 | 2 | 4 | 11 | 0 | AB |
| AlgMag.ChartPoint | 912 | 43 | 16 | 0 | 3 | 4 | 12 | 0 | AB |
| AlgMag.ChartPointAlg | 290 | 8 | 5 | 0 | 1 | 3 | 10 | 0 | AB |
| AlgMag.ChartPointAssemble | 188 | 4 | 1 | 0 | 1 | 2 | 18 | 0 | A |
| AlgMag.ChartPointFinal | 63 | 3 | 1 | 0 | 2 | 2 | 16 | 0 | A |
| AlgMag.ChartPointL11Flat | 248 | 8 | 2 | 0 | 1 | 2 | 23 | 0 | A |
| AlgMag.ChartPointL11Generic | 271 | 5 | 0 | 0 | 1 | 2 | 24 | 0 | A |
| AlgMag.ChartPointL11Image | 314 | 12 | 1 | 1 | 2 | 2 | 19 | 0 | A |
| AlgMag.ChartPointL11Local | 217 | 6 | 0 | 0 | 1 | 2 | 21 | 0 | A |
| AlgMag.ChartPointL11Ring | 304 | 4 | 0 | 0 | 1 | 3 | 14 | 0 | AB |
| AlgMag.ChartPointL11Stable | 178 | 2 | 0 | 0 | 1 | 2 | 20 | 0 | A |
| AlgMag.ChartPointL11Trans | 128 | 3 | 2 | 0 | 1 | 2 | 22 | 0 | A |
| AlgMag.ChartPointLemma11 | 347 | 2 | 1 | 0 | 1 | 2 | 25 | 0 | A |
| AlgMag.ChartPointOrbitInput | 245 | 4 | 1 | 1 | 1 | 2 | 26 | 0 | A |
| AlgMag.ChartPointReduce | 256 | 7 | 4 | 1 | 2 | 3 | 17 | 0 | A |
| AlgMag.ChartPointRing | 179 | 4 | 1 | 0 | 1 | 4 | 13 | 0 | AB |
| AlgMag.ChartQSStab | 201 | 3 | 0 | 0 | 1 | 1 | 13 | 0 | A |
| AlgMag.ChartS5Art | 72 | 3 | 0 | 0 | 1 | 3 | 20 | 0 | AB |
| AlgMag.ChartS5Build | 207 | 5 | 1 | 1 | 1 | 3 | 2 | 0 | AB |
| AlgMag.ChartS5Chart | 711 | 32 | 11 | 2 | 3 | 4 | 12 | 0 | AB |
| AlgMag.ChartS5Close | 82 | 2 | 0 | 0 | 4 | 2 | 34 | 0 | A |
| AlgMag.ChartS5Congr | 68 | 2 | 0 | 0 | 2 | 3 | 12 | 0 | AB |
| AlgMag.ChartS5EA | 75 | 1 | 0 | 0 | 2 | 3 | 13 | 0 | AB |
| AlgMag.ChartS5EB | 109 | 3 | 3 | 0 | 1 | 4 | 2 | 0 | AB |
| AlgMag.ChartS5Final | 150 | 1 | 0 | 0 | 1 | 3 | 20 | 0 | AB |
| AlgMag.ChartS5Graded | 420 | 36 | 7 | 2 | 2 | 4 | 1 | 0 | AB |
| AlgMag.ChartS5HA | 107 | 2 | 0 | 0 | 1 | 3 | 2 | 0 | AB |
| AlgMag.ChartS5Input | 206 | 4 | 0 | 0 | 2 | 3 | 26 | 0 | AB |
| AlgMag.ChartS5InputA | 178 | 11 | 6 | 0 | 2 | 3 | 21 | 0 | AB |
| AlgMag.ChartS5InputAlg | 159 | 8 | 3 | 0 | 1 | 4 | 3 | 0 | AB |
| AlgMag.ChartS5InputB | 198 | 4 | 2 | 0 | 1 | 3 | 22 | 0 | AB |
| AlgMag.ChartS5InputC | 79 | 4 | 1 | 0 | 3 | 3 | 23 | 0 | AB |
| AlgMag.ChartS5InputD | 206 | 8 | 1 | 0 | 1 | 3 | 24 | 0 | AB |
| AlgMag.ChartS5InputE | 182 | 2 | 0 | 0 | 5 | 3 | 25 | 0 | AB |
| AlgMag.ChartS5InputF | 69 | 1 | 0 | 0 | 1 | 3 | 4 | 0 | AB |
| AlgMag.ChartS5InputZ | 140 | 8 | 7 | 1 | 2 | 3 | 20 | 0 | AB |
| AlgMag.ChartS5Level | 261 | 9 | 9 | 0 | 2 | 3 | 16 | 0 | AB |
| AlgMag.ChartS5Lfp | 82 | 3 | 0 | 0 | 1 | 3 | 16 | 0 | AB |
| AlgMag.ChartS5Pt | 108 | 5 | 2 | 0 | 1 | 3 | 17 | 0 | AB |
| AlgMag.ChartS5Site | 236 | 11 | 3 | 0 | 2 | 3 | 14 | 0 | AB |
| AlgMag.ChartS5Spec | 311 | 7 | 11 | 2 | 1 | 7 | 15 | 0 | AB |
| AlgMag.ChartS5Step6 | 63 | 1 | 0 | 0 | 2 | 3 | 13 | 0 | AB |
| AlgMag.ChartS5Trunc | 1023 | 28 | 5 | 0 | 1 | 6 | 1 | 0 | AB |
| AlgMag.ChartS5W | 186 | 7 | 1 | 0 | 2 | 3 | 18 | 0 | AB |
| AlgMag.ChartSection5 | 181 | 12 | 7 | 0 | 2 | 5 | 19 | 0 | AB |
| AlgMag.ChartSplit | 591 | 14 | 1 | 0 | 0 | 4 | 0 | 0 | AB |
| AlgMag.ChartStatement | 137 | 2 | 2 | 0 | 1 | 6 | 7 | 0 | AB |
| AlgMag.ChartStrata | 1056 | 37 | 16 | 0 | 2 | 2 | 14 | 0 | A |
| AlgMag.ChartStratum | 144 | 4 | 0 | 0 | 2 | 2 | 29 | 0 | A |
| AlgMag.ChartStratumAffine | 133 | 4 | 0 | 1 | 1 | 2 | 19 | 0 | A |
| AlgMag.ChartStratumBack | 200 | 2 | 0 | 0 | 1 | 2 | 27 | 0 | A |
| AlgMag.ChartStratumChart | 110 | 2 | 0 | 0 | 1 | 2 | 23 | 0 | A |
| AlgMag.ChartStratumCore | 282 | 7 | 1 | 0 | 1 | 2 | 22 | 0 | A |
| AlgMag.ChartStratumData | 169 | 4 | 1 | 0 | 1 | 2 | 28 | 0 | A |
| AlgMag.ChartStratumDecent | 129 | 3 | 0 | 0 | 1 | 2 | 21 | 0 | A |
| AlgMag.ChartStratumFlat | 166 | 11 | 1 | 0 | 1 | 3 | 17 | 0 | A |
| AlgMag.ChartStratumImage | 261 | 14 | 6 | 1 | 1 | 3 | 18 | 0 | A |
| AlgMag.ChartStratumIntegral | 152 | 2 | 0 | 0 | 1 | 2 | 26 | 0 | A |
| AlgMag.ChartStratumInv | 105 | 4 | 6 | 0 | 1 | 2 | 25 | 0 | A |
| AlgMag.ChartStratumOrbit | 222 | 7 | 3 | 0 | 3 | 3 | 14 | 0 | AB |
| AlgMag.ChartStratumQS | 175 | 2 | 0 | 0 | 1 | 2 | 20 | 0 | A |
| AlgMag.ChartStratumQuotient | 74 | 2 | 2 | 0 | 1 | 2 | 16 | 0 | A |
| AlgMag.ChartStratumRedAction | 214 | 4 | 0 | 0 | 2 | 2 | 24 | 0 | A |
| AlgMag.ChartStratumReduced | 101 | 4 | 0 | 0 | 0 | 3 | 0 | 0 | AB |
| AlgMag.ChartStratumRelation | 157 | 4 | 6 | 0 | 1 | 2 | 15 | 0 | A |
| AlgMag.ChartStratumRing | 472 | 8 | 1 | 0 | 0 | 3 | 0 | 0 | AB |
| AlgMag.ChartStratumStab | 260 | 4 | 0 | 0 | 3 | 3 | 13 | 0 | AB |
| AlgMag.ChartStubs | 232 | 3 | 2 | 0 | 2 | 2 | 33 | 0 | A |
| AlgMag.ChartThickAffine | 506 | 17 | 3 | 1 | 1 | 2 | 12 | 0 | A |
| AlgMag.ChartThm68 | 158 | 8 | 0 | 0 | 2 | 5 | 31 | 0 | A |
| AlgMag.ChartTower | 353 | 8 | 1 | 0 | 1 | 3 | 15 | 0 | A |
| AlgMag.ChartTowerChart | 406 | 10 | 1 | 0 | 2 | 2 | 14 | 0 | A |
| AlgMag.ChartTowerPoints | 308 | 17 | 3 | 0 | 2 | 3 | 13 | 0 | A |
| AlgMag.DoubleScalar | 1017 | 36 | 10 | 0 | 4 | 4 | 16 | 0 | AB |
| AlgMag.DoubleScalarChartAttr | 365 | 8 | 9 | 0 | 2 | 3 | 9 | 0 | AB |
| AlgMag.DoubleScalarCharts | 464 | 12 | 4 | 0 | 2 | 3 | 7 | 0 | AB |
| AlgMag.DoubleScalarCombi | 290 | 17 | 14 | 2 | 0 | 3 | 0 | 0 | AB |
| AlgMag.DoubleScalarLine | 604 | 34 | 8 | 0 | 2 | 3 | 6 | 0 | AB |
| AlgMag.DoubleScalarPure | 367 | 21 | 6 | 0 | 1 | 3 | 8 | 0 | AB |
| AlgMag.DoubleScalarSpaces | 291 | 9 | 4 | 0 | 1 | 3 | 17 | 0 | AB |
| AlgMag.Fact334InfAlgebra | 56 | 2 | 0 | 0 | 0 | 1 | 0 | 0 | A |
| AlgMag.FinalAtlasFree | 82 | 4 | 0 | 0 | 2 | 3 | 39 | 0 | A |
| AlgMag.FinalCor125 | 367 | 14 | 7 | 0 | 1 | 2 | 5 | 0 | AB |
| AlgMag.FinalCorAtlas | 167 | 10 | 2 | 0 | 1 | 2 | 41 | 0 | A |
| AlgMag.FinalCorBridge | 53 | 3 | 0 | 0 | 1 | 2 | 40 | 0 | A |
| AlgMag.FinalFact26 | 90 | 5 | 2 | 0 | 2 | 2 | 22 | 0 | AB |
| AlgMag.FinalFact334 | 44 | 2 | 0 | 0 | 0 | 2 | 0 | 0 | AB |
| AlgMag.FinalLemA3 | 82 | 3 | 2 | 0 | 0 | 2 | 0 | 0 | AB |
| AlgMag.FinalLemA3General | 360 | 9 | 2 | 0 | 1 | 2 | 14 | 0 | AB |
| AlgMag.FinalMisc164 | 135 | 4 | 2 | 0 | 1 | 1 | 13 | 0 | A |
| AlgMag.FinalMiscProp91 | 125 | 3 | 5 | 1 | 1 | 0 | 16 | 1 | none |
| AlgMag.FinalNonQCAtlas | 163 | 7 | 0 | 0 | 1 | 0 | 42 | 0 | none |
| AlgMag.FinalProp91 | 83 | 1 | 3 | 0 | 1 | 2 | 15 | 0 | A |
| AlgMag.FinalRem1111 | 116 | 6 | 5 | 0 | 0 | 2 | 0 | 0 | AB |
| AlgMag.FinalRem1112 | 408 | 17 | 10 | 1 | 0 | 2 | 0 | 0 | AB |
| AlgMag.FinalRem158 | 52 | 1 | 2 | 0 | 1 | 2 | 17 | 0 | AB |
| AlgMag.FinalRem51 | 65 | 3 | 0 | 0 | 1 | 2 | 16 | 0 | AB |
| AlgMag.FinalRemA6 | 573 | 17 | 6 | 0 | 0 | 2 | 0 | 0 | AB |
| AlgMag.FinalRemA7 | 60 | 2 | 1 | 0 | 1 | 2 | 14 | 0 | AB |
| AlgMag.FinalThm68Single | 45 | 1 | 0 | 0 | 1 | 3 | 38 | 0 | A |
| AlgMag.FixesEx333 | 384 | 19 | 13 | 0 | 1 | 2 | 20 | 0 | AB |
| AlgMag.FixesFact26 | 393 | 21 | 12 | 0 | 1 | 3 | 20 | 0 | AB |
| AlgMag.FixesFact26ii | 177 | 11 | 3 | 0 | 2 | 3 | 21 | 0 | AB |
| AlgMag.FixesSec14 | 94 | 3 | 2 | 0 | 1 | 2 | 16 | 0 | AB |
| AlgMag.FixesSec16 | 118 | 4 | 5 | 0 | 1 | 2 | 20 | 0 | AB |
| AlgMag.FixesThm124 | 105 | 2 | 0 | 0 | 1 | 2 | 15 | 0 | AB |
| AlgMag.Foundations | 259 | 9 | 7 | 0 | 0 | 10 | 0 | 0 | AB |
| AlgMag.GeneralBase | 598 | 26 | 23 | 4 | 3 | 12 | 3 | 0 | AB |
| AlgMag.GeneralBaseAttractor | 358 | 19 | 10 | 2 | 1 | 4 | 8 | 0 | AB |
| AlgMag.GeneralBaseChart | 285 | 21 | 14 | 1 | 1 | 5 | 2 | 0 | AB |
| AlgMag.GeneralBaseCor | 529 | 21 | 6 | 2 | 1 | 8 | 10 | 0 | AB |
| AlgMag.GeneralBaseCore | 50 | 2 | 2 | 0 | 1 | 9 | 1 | 0 | AB |
| AlgMag.GeneralBaseGrading | 289 | 5 | 7 | 0 | 3 | 4 | 6 | 0 | AB |
| AlgMag.GeneralBaseLocal | 386 | 13 | 13 | 0 | 2 | 3 | 7 | 0 | AB |
| AlgMag.GeneralBaseMilnor | 806 | 29 | 9 | 1 | 1 | 5 | 2 | 0 | AB |
| AlgMag.GeneralBasePushout | 472 | 21 | 10 | 1 | 3 | 3 | 4 | 0 | AB |
| AlgMag.GeneralBaseSheaf | 114 | 2 | 1 | 0 | 2 | 4 | 3 | 0 | AB |
| AlgMag.GeneralBaseThm320 | 480 | 27 | 17 | 4 | 3 | 7 | 9 | 0 | AB |
| AlgMag.PrintedDoubleScalar | 205 | 8 | 3 | 0 | 1 | 2 | 17 | 0 | AB |
| AlgMag.PrintedProp122 | 69 | 1 | 0 | 0 | 1 | 1 | 13 | 0 | A |
| AlgMag.PrintedProp51 | 201 | 9 | 1 | 0 | 3 | 2 | 16 | 0 | AB |
| AlgMag.PrintedProp85 | 433 | 5 | 0 | 0 | 1 | 2 | 14 | 0 | AB |
| AlgMag.PrintedSec164 | 321 | 9 | 9 | 0 | 3 | 2 | 18 | 0 | AB |
| AlgMag.PrintedSelfActions | 58 | 1 | 1 | 0 | 2 | 2 | 13 | 0 | AB |
| AlgMag.Prop222 | 372 | 17 | 7 | 0 | 2 | 3 | 11 | 0 | AB |
| AlgMag.Representation | 98 | 3 | 1 | 0 | 1 | 11 | 1 | 0 | AB |
| AlgMag.Sec10Deformations | 280 | 3 | 2 | 0 | 0 | 3 | 0 | 0 | AB |
| AlgMag.Sec10LiftsCor | 256 | 5 | 1 | 0 | 1 | 4 | 6 | 0 | AB |
| AlgMag.Sec10LiftsCore | 527 | 41 | 13 | 0 | 3 | 4 | 4 | 0 | AB |
| AlgMag.Sec10LiftsRing | 184 | 13 | 7 | 0 | 1 | 3 | 3 | 0 | AB |
| AlgMag.Sec10PrintedAct | 367 | 29 | 9 | 0 | 1 | 3 | 7 | 0 | AB |
| AlgMag.Sec10PrintedCor | 257 | 4 | 2 | 0 | 2 | 3 | 14 | 0 | AB |
| AlgMag.Sec10PrintedCore | 160 | 7 | 3 | 0 | 1 | 3 | 5 | 0 | AB |
| AlgMag.Sec10PrintedDiff | 250 | 23 | 3 | 0 | 1 | 3 | 9 | 0 | AB |
| AlgMag.Sec10PrintedInt | 334 | 22 | 9 | 1 | 1 | 3 | 11 | 0 | AB |
| AlgMag.Sec10PrintedLifts | 412 | 45 | 13 | 2 | 2 | 3 | 6 | 0 | AB |
| AlgMag.Sec10PrintedMain | 295 | 7 | 7 | 0 | 1 | 3 | 13 | 0 | AB |
| AlgMag.Sec10PrintedPl | 289 | 30 | 10 | 0 | 1 | 3 | 10 | 0 | AB |
| AlgMag.Sec10PrintedTorsor | 304 | 32 | 18 | 0 | 1 | 3 | 8 | 0 | AB |
| AlgMag.Sec10PrintedVanish | 220 | 6 | 4 | 0 | 1 | 3 | 12 | 0 | AB |
| AlgMag.Sec10Schemes | 204 | 4 | 0 | 0 | 1 | 2 | 3 | 0 | AB |
| AlgMag.Sec11Formal | 775 | 31 | 16 | 0 | 5 | 5 | 3 | 0 | AB |
| AlgMag.Sec11PrintedFace | 50 | 2 | 0 | 0 | 3 | 2 | 16 | 0 | AB |
| AlgMag.Sec11PrintedProps | 290 | 3 | 0 | 0 | 2 | 3 | 15 | 0 | AB |
| AlgMag.Sec11Schemes | 339 | 14 | 5 | 0 | 2 | 5 | 5 | 0 | AB |
| AlgMag.Sec11SchemesFace | 449 | 19 | 4 | 0 | 1 | 5 | 6 | 0 | AB |
| AlgMag.Sec11SchemesLimit | 444 | 13 | 11 | 0 | 1 | 4 | 7 | 0 | AB |
| AlgMag.Sec11SchemesRep | 195 | 7 | 1 | 0 | 2 | 6 | 8 | 0 | AB |
| AlgMag.Sec11Spaces | 136 | 7 | 1 | 0 | 1 | 3 | 4 | 0 | AB |
| AlgMag.Sec11SpacesBase | 158 | 9 | 3 | 2 | 2 | 2 | 6 | 0 | A |
| AlgMag.Sec11SpacesCor | 191 | 10 | 2 | 0 | 1 | 3 | 12 | 0 | A |
| AlgMag.Sec11SpacesCore | 307 | 14 | 6 | 1 | 1 | 2 | 7 | 0 | A |
| AlgMag.Sec11SpacesFace | 265 | 4 | 2 | 1 | 2 | 2 | 9 | 0 | A |
| AlgMag.Sec11SpacesFact | 328 | 15 | 16 | 1 | 1 | 2 | 11 | 0 | A |
| AlgMag.Sec11SpacesLift | 284 | 11 | 4 | 0 | 1 | 2 | 8 | 0 | A |
| AlgMag.Sec11SpacesLimit | 93 | 1 | 0 | 0 | 2 | 2 | 10 | 0 | A |
| AlgMag.Sec12Final | 1416 | 29 | 4 | 0 | 4 | 3 | 13 | 0 | AB |
| AlgMag.Sec12GenericSmall | 206 | 2 | 1 | 0 | 1 | 3 | 12 | 0 | AB |
| AlgMag.Sec12PrintedAffine | 249 | 12 | 7 | 0 | 2 | 3 | 7 | 0 | AB |
| AlgMag.Sec12PrintedCor | 140 | 2 | 0 | 0 | 4 | 3 | 4 | 0 | AB |
| AlgMag.Sec12PrintedLocal | 427 | 6 | 2 | 0 | 1 | 4 | 11 | 0 | AB |
| AlgMag.Sec12PrintedRing | 655 | 24 | 6 | 0 | 1 | 4 | 1 | 0 | AB |
| AlgMag.Sec12PrintedSchemes | 405 | 20 | 5 | 1 | 4 | 4 | 10 | 0 | AB |
| AlgMag.Sec12PrintedThm | 369 | 14 | 3 | 1 | 1 | 4 | 12 | 0 | AB |
| AlgMag.Sec12Spaces | 475 | 13 | 5 | 0 | 2 | 3 | 13 | 0 | AB |
| AlgMag.Sec12SpacesThm | 366 | 17 | 11 | 1 | 4 | 3 | 14 | 0 | AB |
| AlgMag.Sec12SymRing | 265 | 9 | 2 | 0 | 0 | 3 | 0 | 0 | AB |
| AlgMag.Sec12Topology | 1371 | 44 | 32 | 2 | 3 | 11 | 2 | 0 | AB |
| AlgMag.Sec13Dilatations | 673 | 36 | 18 | 0 | 1 | 4 | 5 | 0 | AB |
| AlgMag.Sec13General | 1512 | 76 | 41 | 5 | 4 | 4 | 10 | 0 | AB |
| AlgMag.Sec13Spaces | 1593 | 53 | 25 | 3 | 3 | 2 | 11 | 0 | AB |
| AlgMag.Sec14CounterScheme | 409 | 35 | 11 | 1 | 0 | 3 | 0 | 0 | AB |
| AlgMag.Sec14Counterexample | 383 | 19 | 9 | 1 | 2 | 2 | 16 | 0 | AB |
| AlgMag.Sec14Final | 292 | 7 | 7 | 0 | 2 | 4 | 14 | 0 | AB |
| AlgMag.Sec14Glue | 720 | 15 | 10 | 1 | 1 | 1 | 15 | 0 | A |
| AlgMag.Sec14Ind | 387 | 9 | 7 | 1 | 1 | 4 | 3 | 0 | AB |
| AlgMag.Sec14Remaining | 216 | 3 | 4 | 0 | 1 | 3 | 4 | 0 | AB |
| AlgMag.Sec14Strong | 228 | 10 | 3 | 0 | 1 | 4 | 15 | 0 | AB |
| AlgMag.Sec15Final | 786 | 23 | 5 | 0 | 2 | 6 | 15 | 0 | AB |
| AlgMag.Sec15General | 814 | 32 | 8 | 0 | 3 | 7 | 12 | 0 | AB |
| AlgMag.Sec15PureMagnets | 866 | 40 | 10 | 0 | 2 | 6 | 4 | 0 | AB |
| AlgMag.Sec16Gm | 578 | 9 | 27 | 1 | 1 | 4 | 2 | 0 | AB |
| AlgMag.Sec16Lie | 516 | 18 | 38 | 0 | 2 | 4 | 3 | 0 | AB |
| AlgMag.Sec16Remaining | 1138 | 29 | 36 | 5 | 6 | 6 | 12 | 0 | AB |
| AlgMag.Sec16Scheme | 84 | 1 | 6 | 1 | 2 | 3 | 4 | 0 | AB |
| AlgMag.Sec16Tangent | 188 | 9 | 9 | 0 | 1 | 3 | 2 | 0 | AB |
| AlgMag.Sec16Toric | 261 | 13 | 9 | 0 | 1 | 3 | 3 | 0 | AB |
| AlgMag.Sec2Monoids | 652 | 33 | 14 | 0 | 1 | 8 | 2 | 0 | AB |
| AlgMag.Sec2OverB | 458 | 24 | 19 | 0 | 1 | 4 | 7 | 0 | AB |
| AlgMag.Sec3Affine | 601 | 37 | 16 | 1 | 1 | 4 | 5 | 0 | AB |
| AlgMag.Sec3Final | 1291 | 57 | 16 | 0 | 5 | 7 | 15 | 0 | AB |
| AlgMag.Sec3Functorial | 783 | 33 | 31 | 0 | 1 | 12 | 1 | 0 | AB |
| AlgMag.Sec3Intersections | 625 | 16 | 17 | 0 | 1 | 5 | 13 | 0 | AB |
| AlgMag.Sec3IntersectionsWeak | 445 | 13 | 1 | 0 | 3 | 4 | 14 | 0 | AB |
| AlgMag.Sec3Leftover | 29 | 0 | 0 | 0 | 8 | 1 | 19 | 0 | A |
| AlgMag.Sec3Leftover12 | 126 | 4 | 9 | 0 | 1 | 3 | 14 | 0 | AB |
| AlgMag.Sec3Leftover2 | 14 | 0 | 0 | 0 | 3 | 1 | 18 | 0 | A |
| AlgMag.Sec3Leftover221 | 75 | 1 | 4 | 2 | 2 | 2 | 15 | 0 | A |
| AlgMag.Sec3Leftover221Act | 184 | 12 | 6 | 1 | 2 | 2 | 16 | 0 | A |
| AlgMag.Sec3Leftover221Eq | 270 | 19 | 5 | 6 | 1 | 2 | 18 | 0 | A |
| AlgMag.Sec3Leftover221Fin | 124 | 4 | 1 | 0 | 1 | 3 | 11 | 0 | AB |
| AlgMag.Sec3Leftover221Gr | 185 | 17 | 9 | 1 | 2 | 2 | 11 | 0 | A |
| AlgMag.Sec3Leftover221Pi | 143 | 7 | 6 | 0 | 1 | 2 | 6 | 0 | A |
| AlgMag.Sec3Leftover221Rt | 137 | 9 | 1 | 1 | 1 | 2 | 17 | 0 | A |
| AlgMag.Sec3Leftover26 | 81 | 3 | 0 | 0 | 1 | 4 | 8 | 0 | AB |
| AlgMag.Sec3Leftover26Sh | 207 | 10 | 6 | 1 | 1 | 4 | 4 | 0 | AB |
| AlgMag.Sec3Leftover2A | 213 | 6 | 3 | 0 | 3 | 4 | 17 | 0 | AB |
| AlgMag.Sec3Leftover2C | 302 | 10 | 13 | 0 | 3 | 3 | 18 | 0 | AB |
| AlgMag.Sec3Leftover2D | 263 | 16 | 7 | 0 | 1 | 5 | 19 | 0 | AB |
| AlgMag.Sec3Leftover2F | 153 | 2 | 0 | 0 | 2 | 5 | 9 | 0 | AB |
| AlgMag.Sec3Leftover2W | 53 | 1 | 1 | 0 | 2 | 2 | 8 | 0 | A |
| AlgMag.Sec3Leftover313 | 85 | 4 | 4 | 1 | 1 | 3 | 16 | 0 | AB |
| AlgMag.Sec3Leftover328 | 197 | 11 | 7 | 0 | 1 | 5 | 13 | 0 | AB |
| AlgMag.Sec3Leftover328V | 146 | 5 | 6 | 0 | 2 | 2 | 14 | 0 | A |
| AlgMag.Sec3Leftover33 | 321 | 12 | 12 | 0 | 3 | 4 | 16 | 0 | AB |
| AlgMag.Sec3LeftoverAct | 101 | 6 | 4 | 0 | 1 | 5 | 10 | 0 | AB |
| AlgMag.Sec3LeftoverAttr | 100 | 3 | 0 | 0 | 1 | 3 | 12 | 0 | AB |
| AlgMag.Sec3LeftoverFace | 77 | 1 | 3 | 1 | 2 | 3 | 8 | 0 | AB |
| AlgMag.Sec3LeftoverKey | 248 | 10 | 3 | 0 | 1 | 3 | 11 | 0 | AB |
| AlgMag.Sec3LeftoverPts | 159 | 11 | 6 | 0 | 1 | 3 | 9 | 0 | AB |
| AlgMag.Sec3LeftoverW | 52 | 0 | 4 | 2 | 2 | 2 | 7 | 0 | A |
| AlgMag.Sec3Remaining | 1560 | 48 | 47 | 1 | 8 | 8 | 6 | 0 | AB |
| AlgMag.Sec3Rest | 750 | 30 | 25 | 2 | 3 | 3 | 2 | 0 | AB |
| AlgMag.Sec3SchemeQuotient | 1736 | 84 | 21 | 0 | 3 | 4 | 14 | 0 | AB |
| AlgMag.Sec4Limits | 567 | 24 | 20 | 0 | 2 | 5 | 3 | 0 | AB |
| AlgMag.Sec5Etale | 2317 | 102 | 25 | 0 | 1 | 8 | 3 | 0 | AB |
| AlgMag.Sec6Atlas | 568 | 24 | 4 | 0 | 2 | 6 | 5 | 0 | AB |
| AlgMag.Sec6FPR | 382 | 8 | 17 | 0 | 2 | 9 | 2 | 0 | AB |
| AlgMag.Sec7Linearizable | 147 | 5 | 0 | 0 | 1 | 4 | 3 | 0 | AB |
| AlgMag.Sec8Limits | 1462 | 57 | 20 | 5 | 1 | 5 | 13 | 0 | AB |
| AlgMag.Sec8Representability | 1341 | 48 | 22 | 3 | 5 | 10 | 11 | 0 | AB |
| AlgMag.Sec8Theorem83 | 1764 | 46 | 16 | 1 | 4 | 7 | 12 | 0 | AB |
| AlgMag.Sec9General | 2206 | 128 | 68 | 7 | 4 | 6 | 4 | 0 | AB |
| AlgMag.Sec9Hochschild | 631 | 37 | 18 | 0 | 0 | 3 | 0 | 0 | AB |
| AlgMag.Sec9OverB | 1727 | 108 | 61 | 2 | 1 | 5 | 5 | 0 | AB |
| AlgMag.Sec9OverBBridge | 172 | 5 | 3 | 0 | 1 | 2 | 8 | 0 | A |
| AlgMag.Sec9OverBBridge2Cart | 125 | 5 | 3 | 0 | 1 | 2 | 11 | 0 | A |
| AlgMag.Sec9OverBBridge2DX | 216 | 8 | 2 | 0 | 1 | 2 | 13 | 0 | A |
| AlgMag.Sec9OverBBridge2Flat | 236 | 9 | 0 | 0 | 1 | 2 | 12 | 0 | A |
| AlgMag.Sec9OverBBridge2Printed | 103 | 4 | 4 | 0 | 1 | 3 | 14 | 0 | A |
| AlgMag.Sec9OverBBridge3Core | 190 | 6 | 9 | 3 | 1 | 2 | 15 | 0 | A |
| AlgMag.Sec9OverBBridge3Desc | 349 | 18 | 7 | 2 | 1 | 2 | 19 | 0 | A |
| AlgMag.Sec9OverBBridge3Fam | 250 | 13 | 7 | 6 | 1 | 2 | 16 | 0 | A |
| AlgMag.Sec9OverBBridge3Geom | 255 | 12 | 2 | 0 | 1 | 2 | 18 | 0 | A |
| AlgMag.Sec9OverBBridge3Glue | 329 | 14 | 3 | 0 | 1 | 2 | 17 | 0 | A |
| AlgMag.Sec9OverBBridge3QCoh | 457 | 16 | 6 | 1 | 1 | 1 | 21 | 0 | A |
| AlgMag.Sec9OverBBridge3Sheaf | 186 | 6 | 2 | 0 | 1 | 2 | 20 | 0 | A |
| AlgMag.Sec9OverBFinal | 615 | 20 | 13 | 1 | 3 | 3 | 7 | 0 | A |
| AlgMag.Sec9OverBPrinted | 233 | 6 | 10 | 0 | 1 | 2 | 10 | 0 | A |
| AlgMag.Sec9OverBReal | 659 | 26 | 9 | 1 | 2 | 2 | 9 | 0 | A |
| AlgMag.Sec9OverBSpaces | 220 | 5 | 3 | 0 | 1 | 2 | 8 | 0 | A |
| AlgMag.SecFinal1316 | 2248 | 61 | 24 | 2 | 7 | 2 | 15 | 0 | AB |
| AlgMag.SecLeftover | 38 | 0 | 0 | 0 | 8 | 1 | 17 | 0 | A |
| AlgMag.SecLeftover1510 | 209 | 6 | 4 | 0 | 2 | 5 | 5 | 0 | AB |
| AlgMag.SecLeftover158 | 56 | 1 | 2 | 0 | 1 | 4 | 16 | 0 | AB |
| AlgMag.SecLeftover1615 | 133 | 3 | 0 | 0 | 2 | 3 | 13 | 0 | AB |
| AlgMag.SecLeftover1615Spaces | 174 | 3 | 0 | 0 | 2 | 1 | 13 | 0 | A |
| AlgMag.SecLeftoverEtale | 353 | 14 | 3 | 0 | 0 | 3 | 0 | 0 | AB |
| AlgMag.SecLeftoverFPR | 447 | 17 | 10 | 0 | 4 | 3 | 3 | 0 | AB |
| AlgMag.SecLeftoverQCoh | 105 | 3 | 1 | 0 | 1 | 5 | 5 | 0 | A |
| AlgMag.SecLeftoverQCohB | 189 | 4 | 4 | 0 | 1 | 5 | 6 | 0 | AB |
| AlgMag.SelfActionsBase | 584 | 25 | 10 | 0 | 3 | 4 | 11 | 0 | AB |
| AlgMag.SelfActionsExamples | 1217 | 60 | 18 | 0 | 1 | 2 | 13 | 0 | AB |
| AlgMag.SelfActionsMain | 340 | 25 | 3 | 0 | 1 | 4 | 12 | 0 | AB |
| AlgMag.SelfActionsMonoid | 838 | 70 | 10 | 1 | 2 | 3 | 5 | 0 | AB |
| AlgMag.SelfActionsProp21 | 201 | 10 | 5 | 1 | 1 | 2 | 12 | 0 | AB |
| AlgMag.SelfActionsRing | 208 | 8 | 5 | 0 | 2 | 3 | 6 | 0 | AB |
| AlgMag.SpacesLimit | 48 | 2 | 0 | 0 | 1 | 2 | 6 | 0 | AB |
| AlgMag.SpacesLimitA1 | 434 | 18 | 0 | 0 | 2 | 2 | 37 | 0 | A |
| AlgMag.SpacesLimitAction | 738 | 35 | 19 | 0 | 4 | 3 | 32 | 0 | A |
| AlgMag.SpacesLimitFinal | 278 | 12 | 7 | 1 | 2 | 3 | 33 | 0 | A |
| AlgMag.SpacesLimitLocal | 356 | 19 | 7 | 2 | 4 | 2 | 35 | 0 | A |
| AlgMag.SpacesLimitOrbit | 396 | 20 | 10 | 2 | 2 | 2 | 33 | 0 | A |
| AlgMag.SpacesLimitStage | 427 | 18 | 6 | 1 | 1 | 2 | 34 | 0 | A |
| AlgMag.SpacesLimitThm68 | 378 | 14 | 1 | 0 | 1 | 3 | 36 | 0 | A |
| AlgMag.SpacesLimitView | 488 | 35 | 18 | 1 | 1 | 2 | 34 | 0 | A |
| AlgMag.StronglyFPR | 296 | 11 | 1 | 2 | 1 | 5 | 13 | 0 | AB |
| AlgMag.StronglyFPRClosed | 118 | 3 | 0 | 0 | 2 | 2 | 16 | 0 | A |
| AlgMag.StronglyFPRNoteLem21 | 394 | 9 | 0 | 0 | 2 | 3 | 14 | 0 | AB |
| AlgMag.StronglyFPRNoteLem22 | 223 | 9 | 4 | 1 | 2 | 2 | 15 | 0 | AB |
| AlgMag.StronglyFPRNoteLem22Ring | 617 | 27 | 10 | 0 | 0 | 3 | 0 | 0 | AB |
| AlgMag.StronglyFPRNoteThm | 303 | 13 | 1 | 0 | 2 | 1 | 40 | 0 | A |
| AlgMag.StronglyFPRRing | 525 | 22 | 12 | 0 | 0 | 3 | 0 | 0 | AB |
| AlgMag.StronglyFPRStab | 664 | 23 | 4 | 0 | 5 | 4 | 12 | 0 | AB |
| AlgMag.XProductsAction | 424 | 27 | 15 | 1 | 3 | 3 | 5 | 0 | AB |
| AlgMag.XProductsExample | 402 | 18 | 16 | 2 | 1 | 3 | 14 | 0 | AB |
| AlgMag.XProductsExampleClass | 853 | 42 | 11 | 0 | 1 | 3 | 16 | 0 | AB |
| AlgMag.XProductsExampleCoord | 281 | 20 | 9 | 0 | 1 | 3 | 15 | 0 | AB |
| AlgMag.XProductsExampleFunctor | 784 | 43 | 18 | 4 | 1 | 2 | 17 | 0 | AB |
| AlgMag.XProductsF1 | 225 | 8 | 15 | 2 | 0 | 3 | 0 | 0 | AB |
| AlgMag.XProductsF1Base | 334 | 12 | 9 | 0 | 1 | 2 | 6 | 0 | AB |
| AlgMag.XProductsF1Glue | 561 | 27 | 21 | 1 | 2 | 3 | 5 | 0 | AB |
| AlgMag.XProductsGlue | 253 | 9 | 7 | 6 | 1 | 4 | 4 | 0 | AB |
| AlgMag.XProductsPrinted | 407 | 14 | 9 | 0 | 2 | 3 | 14 | 0 | AB |
| AlgMag.XProductsPrintedLfp | 54 | 0 | 1 | 1 | 2 | 1 | 38 | 0 | A |
| AlgMag.XProductsRep | 335 | 9 | 10 | 0 | 2 | 4 | 13 | 0 | AB |
| AlgMag.XProductsThm | 478 | 21 | 15 | 0 | 4 | 3 | 12 | 0 | AB |
| AlgMagBuilt | 232 | 0 | 0 | 0 | 231 | 0 | 27 | 0 | B |
