# Algebraic Magnetism: formalization status

Paper: A. Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026), text as in `notes/AGENT_RULES.md`. Lean: `AlgMag/*.lean`.

**Scan: 2026-11-06 20:55 (local); rows on stubs or AHR revised 2026-11-09 against the source and `#print axioms`.** Tags recomputed by script from `AlgMagBuilt.lean`, source dates and import closures. Joint build: `lake build AlgMagBuilt` covers 231 of 336 modules, every olean newer than its source; the other 105 reach a Stacks module not in the sparse build, listed in `notes/REQUIRES_FULL_STACKS.md`.

**Status.** FULL: the paper's generality, or its corrected statement where the row says so. PARTIAL: a proved restriction, stated in the row. ABSENT: conclusion not proved. NO CONTENT: nothing to prove. EXCLUDED: reductive groups, by the author's decision. **FULL does not mean built:** read it with the column "Oleans". The former tag **waits for AHR** is retired (2026-11-09): Thm 6.8 (i) is `thm68_atlas` (one strongly-FPR atlas, X separated l.f.p., S separated), axioms clean, and the rows that took the atlas as a hypothesis now have atlas-free forms.

**Oleans**, per declaration. [J] joint-build: module in `AlgMagBuilt`, compiled by lake against real Stacks oleans. [O] real, overlay: needs real Stacks modules outside the sparse build, compiled unmodified in a scratchpad overlay. [C] `#print axioms` of this declaration clean (propext, Classical.choice, Quot.sound). Re-checked 2026-11-09 on all 54 declarations formerly tagged [S] (stubs): none depends on sorryAx in `import AlgMag`.

**Conventions.** `S` is any scheme; spaces are presheaves on the big fppf site. Size hypotheses (`hN`, `hL`, `MagnetInSite`, `SM B M`, coproducts in the site) are a site cutoff. Outside this tracker: `SelfActions*`, `XProducts*`, `DoubleScalar*`, `StronglyFPR*` are other papers.

## §1 Introduction

| No. | Content | Lean | Status | How | Oleans |
|---|---|---|---|---|---|
| Def 1.1 | Attractor functor (same as Def 3.1) | `attractor` Foundations.lean:110 [J]<br>`attractorPtEquivOfUniversal` Representation.lean:67 [J] | FULL |  | joint-build |
| Ex 1.2 | A^n_S with linear action: V^N = sum of the V_n, n in N | `ex12_general` Sec3Leftover12.lean:122 [J]<br>`ex12` Sec3Remaining.lean:526 [J]<br>`vAttractorEquiv` Sec3Leftover328.lean:165 [J]<br>`ex12_sub` Ex12Rem313Final.lean:94 [J]<br>`ex12_mem_iff` Ex12Rem313Final.lean:113 [J] | FULL | Any S, any graded E (non-free weight spaces): V^N -> V injective, natural, image = points killing E_m for m not in N. | joint-build |
| Ex 1.3 | Reductive G: overview | — | NO CONTENT | Announcement of §16.5 (excluded). | — |

## §2 Rings of monoids

| No. | Content | Lean | Status | How | Oleans |
|---|---|---|---|---|---|
| Def 2.1 | Ring Z[N] | `X` Sec2Monoids.lean:57 [J]<br>`zRing` GeneralBase.lean:52 [J] | FULL |  | joint-build |
| Fact 2.2 | Z[N] bialgebra, Hopf if N is a group | `counit_X` Sec2Monoids.lean:61 [J]<br>`comul_X` Sec2Monoids.lean:65 [J]<br>`antipode_X` Sec2Monoids.lean:69 [J] | FULL | Structure from Mathlib, formulas proved. | joint-build |
| Def 2.3 | R[N], O_S[N], O_B[N] | `baseChangeEquiv` Sec2Monoids.lean:74 [J]<br>`preON` FixesFact26.lean:115 [J]<br>`fact26_i_sheafification` FixesFact26.lean:200 [J]<br>`ONB` FinalFact26.lean:37 [J] | FULL | (i), (ii) O_S[N] as sheafification. (iii) O_B[N] on the site SB of §9. | joint-build |
| Def 2.4 | A(N), A(N)_S, A(N)_B, D(M) | `AZ` GeneralBase.lean:55 [J]<br>`A` GeneralBase.lean:243 [J]<br>`monObjA` GeneralBase.lean:406 [J]<br>`AB` Sec3Remaining.lean:1491 [J]<br>`isPullback_AB` Sec2OverB.lean:142 [J]<br>`isAlgebraicSpace_AB` Sec2OverB.lean:181 [J] | FULL | Over B with site hypothesis hN. | joint-build |
| Rem 2.5 | Notation | — | NO CONTENT |  | — |
| Fact 2.6 | A(N)_S, A(N)_B affine and flat, bialgebra O_S[N], O_B[N] | `flat_str` Sec3Leftover26.lean:23 [J]<br>`isFlat_pr` Sec3Leftover26.lean:50 [J]<br>`exists_affine_chart_pr` Sec3Leftover26.lean:57 [J]<br>`fact26_i_sheafification` FixesFact26.lean:200 [J]<br>`fact26_i_comul` FixesFact26.lean:254 [J]<br>`fact26_i_counit` FixesFact26.lean:275 [J]<br>`fact26_i_tensor_bijective` FixesFact26.lean:300 [J]<br>`fact26_ii_chart` FixesFact26ii.lean:144 [J]<br>`fact26_ii_sections` Sec3Leftover2F.lean:119 [J]<br>`ONB` FinalFact26.lean:37 [J]<br>`cmpT_bijective` FinalFact26.lean:52 [J]<br>`cmpT_natural` FinalFact26.lean:56 [J]<br>`cmpT_comul` FinalFact26.lean:62 [J]<br>`cmpT_counit` FinalFact26.lean:70 [J]<br>`onb_map_single` FinalFact26.lean:78 [J] | FULL | (i) sheaf of bialgebras on S. (ii) `ONB` = O_B[N] on the site SB of §9 (printed B_{spaces,etale} replaced, as in §9): bijective with q_*O on affine objects, natural, comultiplication and counit identified. Printed route not followed (REMARKS.md). | joint-build |
| Fact 2.7 | A(N x L) = A(N) x A(L), also over S, B | `isPullback_AZ_prod` GeneralBase.lean:167 [J]<br>`isPullback_A_prod` GeneralBase.lean:306 [J]<br>`prodIso` GeneralBase.lean:427 [J]<br>`isPullback_AB_prod` Sec2OverB.lean:188 [J] | FULL | Over B with hN. | joint-build |
| Prop 2.8 | Multiplication flat when N acts freely on N x N | `flat_diag` Sec2Monoids.lean:202 [J]<br>`flat_mulZ` GeneralBase.lean:215 [J]<br>`flat_mul` GeneralBase.lean:471 [J]<br>`isFlat_mulB` Sec2OverB.lean:355 [J] | FULL | (iv) with site hypothesis hN (size cutoff). The older flat_mul_overB is not (iv). | joint-build |
| Rem 2.9 | Free for groups; not free for N minus {1} | `isFreeAction_of_group` Sec2Monoids.lean:237 [J]<br>`not_isFreeAction_natNeOne` Sec2Monoids.lean:264 [J] | FULL | Printed witness corrected. | joint-build |
| Fact 2.10 | N f.g.: f.p. statements over Z, S, B | `fact210_i` Sec3Remaining.lean:95 [J]<br>`finitePresentation` Sec2Monoids.lean:301 [J]<br>`instLFP_AZ` GeneralBase.lean:190 [J]<br>`lfp_mulZ` GeneralBase.lean:232 [J]<br>`instLFP_str` GeneralBase.lean:358 [J]<br>`lfp_mul` GeneralBase.lean:480 [J]<br>`affine_mul` GeneralBase.lean:490 [J]<br>`isFinitePresentation_mulB` Sec2OverB.lean:364 [J]<br>`isFinitePresentation_pr` Sec2OverB.lean:374 [J] | FULL | (vi) with hN. | joint-build |
| Def 2.11 | Trivial monoid schemes | `trivialGrp` Sec16Lie.lean:97 [J]<br>`eS` Sec3LeftoverFace.lean:45 [J]<br>`eB` Sec3LeftoverFace.lean:60 [J] | FULL |  | joint-build |
| Fact 2.12 | Action of A(M) on A(N) | `coact` Sec2Monoids.lean:474 [J]<br>`actMor` GeneralBase.lean:504 [J]<br>`aAction` GeneralBase.lean:518 [J]<br>`actMorB` Sec2OverB.lean:404 [J] | FULL | Over B with hN. | joint-build |
| Fact 2.13 | N <= N' gives equivariant A(N') -> A(N) | `Amap` GeneralBase.lean:276 [J]<br>`restrict` Sec3Functorial.lean:417 [J]<br>`restrictB_equivariant` Sec2OverB.lean:432 [J]<br>`restrictB_mul` Sec2OverB.lean:438 [J] | FULL | Over B with hN. | joint-build |
| Def 2.14 | Face | `IsFaceOver` Sec2Monoids.lean:380 [J] | FULL |  | joint-build |
| Fact 2.15 | A(F) -> A(N) equivariant | `faceA` GeneralBasePushout.lean:81 [J]<br>`faceExt` Sec3Functorial.lean:698 [J]<br>`faceB_equivariant` Sec2OverB.lean:451 [J] | FULL | Over B with hN. | joint-build |
| Prop 2.16 | Criterion for faces | `isFace_iff` Sec2Monoids.lean:391 [J] | FULL |  | joint-build |
| Prop 2.17 | N^x subgroup, face, largest subgroup | `unitsFace` Sec2Monoids.lean:515 [J]<br>`unitsFace_isGroup` Sec2Monoids.lean:526 [J]<br>`faceCond_unitsFace` Sec2Monoids.lean:532 [J]<br>`le_unitsFace` Sec2Monoids.lean:538 [J] | FULL |  | joint-build |
| Fact 2.18 | Every face contains N^x | `unitsFace_le_face` Sec2Monoids.lean:544 [J] | FULL |  | joint-build |
| Prop 2.19 | A(N')_S scheme push-out | `faceCond_gluedMagnet` Sec2Monoids.lean:572 [J]<br>`milnor_glued` GeneralBasePushout.lean:131 [J]<br>`isPushout_glued` GeneralBasePushout.lean:466 [J] | FULL | Tag 0ET0 replaced by GeneralBaseMilnor. | joint-build |
| Def 2.20 | A(M)_S-O_S-module | `ModuleAAction` Sec3Remaining.lean:129 [J]<br>`AModule` Sec3LeftoverW.lean:50 [O]<br>`aModuleEquiv` Sec3Leftover2W.lean:32 [C] | FULL | W(F) = p^*F; both forms compared. | joint-build / real, overlay / overlay, axioms clean |
| Prop 2.21 | Qcoh modules = qcoh M-graded modules | `prop221` Sec3Leftover221Eq.lean:268 [C]<br>`grToAct` Sec3Leftover221Eq.lean:234 [C] | FULL | Equivalence of categories, any S, any monoid M. Route through Prop 9.11 (printed only cites SGA3). `#print axioms` clean (re-check 2026-11-09). | axioms clean |
| Prop 2.22 | X affine: actions = M-gradings | `actionEquivGrading` Prop222.lean:325 [J]<br>`globalGradingOf` Prop222.lean:95 [J]<br>`actionOfGrading` Prop222.lean:246 [J] | FULL | Any S, M. | joint-build |

## §3 Attractors

| No. | Content | Lean | Status | How | Oleans |
|---|---|---|---|---|---|
| Def 3.1 | Attractor X^N | `AttractorPt` Foundations.lean:93 [J]<br>`attractor` Foundations.lean:110 [J]<br>`universalPoint` GeneralBase.lean:567 [J] | FULL |  | joint-build |
| Prop 3.2 | X^N fppf sheaf | `isSheaf_attractor` Foundations.lean:187 [J]<br>`isSheaf_attractor_of_isAlgebraicSpace` AlgebraicSpace.lean:31 [J] | FULL |  | joint-build |
| Rem 3.3 | Any functor with action | `AAction` Foundations.lean:80 [J] | NO CONTENT |  | joint-build |
| Rem 3.4 | Notation | — | NO CONTENT |  | — |
| Rem 3.5 | X^0 = fixed points | `attractorBotEquiv` Sec3Functorial.lean:661 [J] | FULL |  | joint-build |
| Fact 3.6 | X^M = X | `attractorTopEquiv` Foundations.lean:129 [J]<br>`attractorTopIso` Sec16Gm.lean:561 [J] | FULL |  | joint-build |
| Prop 3.7 | Equivariant fibre products | `fibreProductAction` Sec3Functorial.lean:142 [J]<br>`existsUnique_fibreLift` Sec3Functorial.lean:161 [J]<br>`attractorFibreProductIso` Sec3Functorial.lean:269 [J] | FULL |  | joint-build |
| Prop 3.8 | (Y x_S Z)^N | `attractorProdIso` Sec3Functorial.lean:337 [J] | FULL |  | joint-build |
| Prop 3.9 | X^N x_S T = (X_T)^N | `attractorOverIso` Sec3Functorial.lean:400 [J] | FULL |  | joint-build |
| Fact 3.10 | N <= L gives X^N -> X^L | `magnetMap` Sec3Functorial.lean:442 [J] | FULL |  | joint-build |
| Rem 3.11 | Action of A(M) on X^N | `attractorAction` Sec3Functorial.lean:490 [J] | FULL |  | joint-build |
| Rem 3.12 | Action of A(N) on X^N | `magnetAction` Sec3Functorial.lean:518 [J] | FULL |  | joint-build |
| Rem 3.13 | 3.11 from 3.12; sanity check | `attractorAction_smul_eq` Sec3Functorial.lean:550 [J]<br>`rem313` Sec3Leftover313.lean:74 [J]<br>`rem313_toPoint` Sec3Leftover313.lean:79 [J] | FULL | First assertion in full. Sanity check printed only "under some working assumptions" (no precise content); proved for X affine, on the scheme Zatt. | joint-build |
| Prop 3.14 | Monoid/group functor | `attractorMonoid` Sec3Functorial.lean:577 [J]<br>`attractor_map_mul` Sec3Functorial.lean:603 [J]<br>`attractorGroup` Sec3Functorial.lean:626 [J] | FULL |  | joint-build |
| Fact 3.15 | p_{N,F}, retraction | `faceMap` Sec3Functorial.lean:766 [J]<br>`magnetMap_comp_faceMap` Sec3Functorial.lean:772 [J] | FULL |  | joint-build |
| Fact 3.16 | X^F -> X^N closed immersion | `fact316` Sec3Remaining.lean:1083 [J]<br>`fact316_spaces` Sec3LeftoverFace.lean:35 [J] | FULL | Spaces, via Tag 03KP(3) (printed citation 0AGC). | joint-build |
| Fact 3.17 | Equivariant f gives f^N | `attractorMap` Sec3Functorial.lean:200 [J] | FULL |  | joint-build |
| Fact 3.18 | Mono gives mono | `mono_attractorMap` Sec3Functorial.lean:232 [J] | FULL |  | joint-build |
| Fact 3.19 | L.f.p. gives l.f.p. | `fact319_relativelyLimitPreserving` Final3Fact319.lean:126 [C]<br>`isLocallyOfFinitePresentation_repMap_spaces` Sec11SpacesFact.lean:239 [C] | FULL | Functor form (Stacks 049J): for an equivariant morphism f of algebraic spaces, locally of finite presentation, f^N : X^N → Y^N is limit preserving; any commutative monoid M, no representability of X^N, Y^N assumed; #M below the site cutoff. Representable spaces form: second name. | full build, axioms clean |
| Thm 3.20 | X affine: closed subscheme with ideal generated by A_m | `Zatt` GeneralBaseThm320.lean:226 [J]<br>`instClosedIAtt` GeneralBaseThm320.lean:347 [J]<br>`attEquiv` GeneralBaseThm320.lean:444 [J]<br>`representsAttractor` GeneralBaseThm320.lean:466 [J]<br>`isLeast_ker_iAtt` Prop222.lean:355 [J] | FULL | Any S; the global ideal sheaf is now proved. | joint-build |
| Ex 3.21 | A(L)^N | `instClosedIAtt` GeneralBaseThm320.lean:347 [J]<br>`ker_iAtt_self` SelfActionsBase.lean:567 [J]<br>`exists_att_A_iff` Sec3Leftover33.lean:198 [J]<br>`faceIota_closed` Sec3Leftover2D.lean:156 [J] | FULL | Printed form from Thm 3.20 + ker_iAtt_self (ideal: X^m, m in L not in N). The face case is representable by A(L meet N)_S. | joint-build |
| Cor 3.22 | X^N -> X^L closed immersion | `Zincl` GeneralBaseCor.lean:197 [J]<br>`instClosedZincl` GeneralBaseCor.lean:208 [J] | FULL |  | joint-build |
| Rem 3.23 | 3.22 fails non-affine | `rem323` Sec3Remaining.lean:697 [J] | FULL | A^2 minus 0, over nontrivial R. | joint-build |
| Prop 3.24 | Intersections, X affine | `ker_iAtt_iInf` GeneralBaseCor.lean:289 [J]<br>`exists_toPoint_iInf_iff` GeneralBaseCor.lean:258 [J] | FULL | Infinite fibre product expressed on points. | joint-build |
| Rem 3.25 | 3.24 fails non-affine | `rem325` Sec3Remaining.lean:1001 [J] | FULL | P^1 on affine R-schemes. | joint-build |
| Lem 3.26 | Z^N = Z x_Y Y^N | `isPullback_Zmap` GeneralBaseCor.lean:485 [J]<br>`Zmap` GeneralBaseCor.lean:473 [J]<br>`instClosedZmap` GeneralBaseCor.lean:523 [J] | FULL |  | joint-build |
| Rem 3.27 | 12.2 extends 3.26 | — | NO CONTENT |  | — |
| Prop 3.28 | V(E)^N = V(E_N) | `prop328_action` Sec3Leftover221.lean:71 [C]<br>`prop328` Sec3Leftover328V.lean:127 [C]<br>`vAttractorEquiv` Sec3Leftover328.lean:165 [J]<br>`linAttractorEquiv` Sec3Remaining.lean:381 [J] | FULL | Any S, qcoh E with action. V(E_N) -> V(E) not identified with vectorBundleMap. Adjoint form Hom(E, p_*O_T) (REMARKS.md). | axioms clean / joint-build |
| Prop 3.29 | X separated: X^N -> X^L mono | `attractor_ofLE_injective` Sec4Limits.lean:511 [J]<br>`ofLE_injective` Sec5Etale.lean:1747 [J] | FULL | Site hypotheses `hN`, `hL`; none for M f.g. | joint-build |
| Cor 3.30 | X separated: X^N -> X mono | `attractor_toPoint_injective` Sec4Limits.lean:543 [J]<br>`attractor_toPoint_injective_sep` Sec5Etale.lean:1754 [J] | FULL |  | joint-build |
| Prop 3.31 | X^N_M = X^Y_Z | `prop331_i` Sec3Final.lean:104 [J]<br>`prop331_ii` Sec3Final.lean:1008 [J]<br>`prop331_ii_spaces` Prop331Spaces.lean:103 [J]<br>`prop331_ii_free` Prop331Free.lean:33 [J]<br>`prop331_ii_general` Prop331Free.lean:125 [J]<br>`prop331_ii_anyS` Prop331Free.lean:197 [J]<br>`prop331_iii` Sec3Remaining.lean:1345 [J] | PARTIAL | (i) in full. (ii) X a scheme; spaces: X separated with an S-affine f^-1(Y^x)-FPR atlas, Y f.g. or X limit preserving; no atlas: `prop331_ii_anyS`, X separated l.f.p., S arbitrary (`prop331_ii_general`: S separated; `prop331_ii_free`: X also qc). (iii) Z f.g., Y <= f(M). | joint-build |
| Prop 3.32 | (X^N)^L = X^{N∩L} | `prop332_i` Sec3Final.lean:119 [J]<br>`prop332_scheme` Sec3SchemeQuotient.lean:1669 [J]<br>`prop332` Sec3Intersections.lean:463 [J]<br>`prop332_weak` Sec3IntersectionsWeak.lean:334 [J]<br>`prop332_linearizable` Sec3IntersectionsWeak.lean:417 [J]<br>`prop332_iii_scheme` Sec3Final.lean:1197 [J]<br>`prop332_iii_gp` Sec3Final.lean:1263 [J]<br>`prop332_iii_atlas` Sec3Final.lean:1228 [J]<br>`prop332_free` FinalAtlasFree.lean:41 [C]<br>`prop332_separated` SepProp33.lean:305 [C]<br>`prop332_iii_free` AtlasFree332iii.lean:36 [C] | PARTIAL | (i) in full. (ii) spaces with no atlas hypothesis: `prop332_separated`, X separated l.f.p. (not necessarily qc), S separated, M f.g., N, L arbitrary; schemes without atlas; spaces with an atlas over any S. (iii) separated schemes; spaces with no atlas: `prop332_iii_free`, X separated l.f.p. (not necessarily qc), S separated, M embedded in a f.g. abelian group, N, L arbitrary. Printed proof repaired. | joint-build / axioms clean |
| Ex 3.33 | A^2 example | `ex333_A2` FixesEx333.lean:191 [J]<br>`ex333_printed_axis` FixesEx333.lean:243 [J]<br>`ex333_printed_zero` FixesEx333.lean:331 [J]<br>`ex333_zero_unique` Sec3Leftover2A.lean:184 [J]<br>`ex333_iter` Sec3Leftover33.lean:316 [J] | FULL | Printed identification with A^1_S x_S 0 and the zero section. | joint-build |
| Fact 3.34 | Same attractors: X^{N_i} = X^{⋂ N_l} | `fact334_i` Sec3Final.lean:143 [J]<br>`fact334_finite_scheme` Sec3SchemeQuotient.lean:1699 [J]<br>`fact334_finite` Sec3Intersections.lean:528 [J]<br>`fact334_strong` Sec15Final.lean:139 [J]<br>`fact334_iii_finite_scheme` Sec3Final.lean:1208 [J]<br>`fact334_iii_atlas` Sec3Final.lean:1239 [J]<br>`fact334_free` FinalCorAtlas.lean:29 [C]<br>`fact334_nonqc` FinalNonQCFact.lean:190 [C]<br>`fact334_general` FinalNonQCLocal.lean:66 [C]<br>`fact334_iii_free` AtlasFree332iii.lean:51 [C]<br>`neg_mem_iInf_of_multiples` FinalFact334.lean:35 [J] | PARTIAL | (i) in full. (ii) arbitrary families, no atlas: `fact334_general`, X separated, l.f.p. added (not printed), not necessarily qc, S arbitrary, M f.g.; finite families for schemes. (iii) finite families for separated schemes; spaces with no atlas, arbitrary nonempty families: `fact334_iii_free`, X separated l.f.p. (not printed), not necessarily qc, S arbitrary, M embedded in a f.g. abelian group. `neg_mem_iInf_of_multiples`: a combinatorial step only. | joint-build / axioms clean |
| Prop 3.35 | M f.g.: X^Z = X^{D(M/Z)} | `attractorFixedEquivOfCover` Sec8Representability.lean:211 [J]<br>`isFreeAlong_subtype` Sec8Representability.lean:264 [J]<br>`extSieve_mem` Sec8Representability.lean:388 [J]<br>`prop335_scheme` Prop81General.lean:423 [C]<br>`prop335_of_atlas` Prop81General.lean:431 [C] | FULL | Any fppf sheaf, M f.g.: the first three names combined. M an arbitrary abelian group: schemes (`prop335_scheme`) and algebraic spaces with a Z-FPR atlas (`prop335_of_atlas`). | joint-build; Prop81General full build, axioms clean |
| Prop 3.36 | Cartesian square from faces | `isFace_inf36` Sec3Final.lean:182 [J]<br>`cart36` Sec3Final.lean:210 [J]<br>`prop336_i` Sec3Final.lean:487 [J]<br>`prop336_ii` Sec3Final.lean:546 [J] | FULL | Printed X a scheme. | joint-build |
| Prop 3.37 | X separated, l.f.p.: X^N(T) = colim | `prop337_colimit` Prop337General.lean:514 [C]<br>`prop337_exists` Prop337General.lean:428 [C]<br>`ofLE_inj` Prop337General.lean:390 [C]<br>`prop337` Sec8Limits.lean:1077 [J] | FULL | Corrected statement (see Paper corrections): T quasi-compact; M an arbitrary commutative monoid, N a directed union of the N_i; #M below the site cutoff. `prop337`: T affine, M f.g. group. | full build, axioms clean |

## §4 Prescribed limits

| No. | Content | Lean | Status | How | Oleans |
|---|---|---|---|---|---|
| Def 4.1 | Prescribed limit | `prescribedLimit` Sec4Limits.lean:44 [J] | FULL |  | joint-build |
| Prop 4.2 | X^N_{F,Z} = X^N x_{X^F} Z | `prescribedLimitIso` Sec4Limits.lean:77 [J] | FULL |  | joint-build |
| Fact 4.3 | Monos | `mono_prescribedLimit_ι` Sec4Limits.lean:100 [J]<br>`prescribedLimit_toPoint_injective` Sec4Limits.lean:553 [J] | FULL | Site hypotheses. | joint-build |

## §5 Étale base change

| No. | Content | Lean | Status | How | Oleans |
|---|---|---|---|---|---|
| Prop 5.1 | U^N = X^N x_{X^Q} U^Q | `faceComparison` Sec5Etale.lean:81 [J]<br>`IsFaceCartesian` Sec5Etale.lean:89 [J]<br>`isFaceCartesian_of_fg` Sec5Etale.lean:1609 [J]<br>`isFaceCartesian_of_separated` Sec5Etale.lean:2300 [J]<br>`prop51_ii` Sec8Limits.lean:1086 [J]<br>`prop51_i_printed` PrintedProp51.lean:175 [J] | FULL | Corrected statement: X separated added in (i), l.f.p. added in (ii). Bijection on all T. Any face directly. Printed reduction: `prop51_i_printed`, X a separated scheme, M f.g. | joint-build |

## §6 FPR atlases

| No. | Content | Lean | Status | How | Oleans |
|---|---|---|---|---|---|
| Def 6.1 | FPR notions and atlases | `IsFPR` Sec6FPR.lean:94 [J]<br>`IsZFPR` Sec6FPR.lean:168 [J]<br>`IsStronglyFPR` Sec6FPR.lean:173 [J]<br>`IsEquivariantAtlas` Sec6FPR.lean:297 [J]<br>`IsSAffineAtlas` Sec6FPR.lean:309 [J]<br>`IsZFPRAtlas` Sec6FPR.lean:314 [J]<br>`IsStronglyFPRAtlas` Sec6FPR.lean:320 [J] | FULL |  | joint-build |
| Rem 6.2 | Finite index | `hasFiniteAffineDecomposition_iff` Sec6FPR.lean:260 [J] | FULL |  | joint-build |
| Prop 6.3 | M = Z^r: étale equivariant implies FPR | `prop63` AppendixA.lean:546 [J] | FULL | Proof via A.1 FPR part. | joint-build |
| Rem 6.4 | Romagny generalizes | — | NO CONTENT |  | — |
| Rem 6.5 | Counterexample M = Z/2 | `rem65` SecLeftoverFPR.lean:304 [J]<br>`rem65_zmod2` SecLeftoverFPR.lean:323 [J]<br>`not_etale_printed_rem65` SecLeftoverFPR.lean:267 [J] | FULL | Corrected statement, see Paper corrections. | joint-build |
| Rem 6.6 | FPR not strongly-FPR | `rem66` SecLeftoverFPR.lean:375 [J]<br>`formallyEtale_incl` SecLeftoverEtale.lean:134 [J] | FULL | Corrected statement. Scheme category, not site-level atlas; M f.g. added though finite index suffices. | joint-build |
| Lem 6.7 | Base change of Z-FPR atlas | `lemma67_i` Sec6Atlas.lean:190 [J]<br>`lemma67_ii` Sec6Atlas.lean:208 [J] | FULL |  | joint-build |
| Thm 6.8 | Existence of Z-FPR atlases | `thm68` ChartFinal.lean:43 [C]<br>`thm68_i` ChartThm68.lean:133 [C]<br>`exists_charts` SpacesLimitThm68.lean:228 [C]<br>`thm68_family` SpacesLimitThm68.lean:252 [C]<br>`thm68_qc` SpacesLimitThm68.lean:274 [C]<br>`thm68_ii_of_charts` SpacesLimitThm68.lean:340 [C]<br>`isZFPRAtlas_of_family` ChartAtlas.lean:202 [J]<br>`thm68_family_spaces` ChartFinalSpaces.lean:31 [C]<br>`thm68_qc_spaces` ChartFinalSpaces.lean:44 [C]<br>`thm11_affine_spaces` ChartFinalSpaces.lean:57 [C]<br>`thm68_single` FinalThm68Single.lean:30 [C]<br>`thm68_atlas` FinalNonQCAtlas.lean:106 [C]<br>`thm68_relqc` FinalNonQCRelQC.lean:33 [C]<br>`thm68_relqc_local` FinalNonQCRelQC.lean:63 [C] | PARTIAL | (i) X separated, l.f.p., S separated, M f.g.: one strongly-FPR atlas, Z-FPR for all Z, X not necessarily qc, no site hypothesis (`thm68_atlas`). Quasi-compact clause: X -> S qc, S qc separated: S-affine strongly-FPR atlas (`thm68_relqc`); S arbitrary: an O-affine atlas over each affine open O (`thm68_relqc_local`); one global S-affine atlas for S not qc is not proved. Former chart stubs discharged. (ii) non-separated X takes the charts as hypothesis (`thm68_ii_of_charts`): printed input is AHR Cor 20.2. | axioms clean / joint-build |

## §7 Linearizable actions

| No. | Content | Lean | Status | How | Oleans |
|---|---|---|---|---|---|
| Fact 7.1 | Equivariant open immersion is Z-FPR | `isZFPR_of_mono` Sec7Linearizable.lean:29 [J]<br>`isStronglyFPR_of_mono` Sec7Linearizable.lean:42 [J] | FULL | All monos. | joint-build |
| Def 7.2 | Sumihiro action | `ZariskiLocallyLinearizable` Sec7Linearizable.lean:56 [J] | FULL |  | joint-build |
| Fact 7.3 | Sumihiro action has a strongly-FPR atlas | `fact73` Sec6Atlas.lean:420 [J] | FULL | Coproduct `hV` assumed in the site (size cutoff). | joint-build |
| Rem 7.4 | External | — | NO CONTENT |  | — |
| Rem 7.5 | External | — | NO CONTENT |  | — |

## §8 Representability

| No. | Content | Lean | Status | How | Oleans |
|---|---|---|---|---|---|
| Prop 8.1 | Z-FPR atlas: X^Z closed subspace | `prop81_general` Prop81General.lean:444 [C]<br>`prop81FG` Sec8Representability.lean:1274 [J]<br>`AttractorIsClosedSubspace` Sec6FPR.lean:341 [J] | FULL | As printed, M an arbitrary abelian group (hAZ, hM, hQ: size cutoffs of the site). `prop81FG`: M f.g. | full build, axioms clean |
| Rem 8.2 | Pointer | — | NO CONTENT |  | — |
| Thm 8.3 | Representability, (i)-(vii) | `thm83_repr` Sec8Theorem83.lean:1595 [J]<br>`thm83` Sec8Theorem83.lean:1684 [J]<br>`thm83_vii` Sec8Theorem83.lean:1707 [J]<br>`thm83_iv` Sec8Limits.lean:987 [J]<br>`thm83_vi` Sec8Limits.lean:1049 [J]<br>`thm83_of_lfp` Sec8Limits.lean:1065 [J]<br>`thm83_free` FinalCorAtlas.lean:107 [C]<br>`thm83_free_of_coproducts` FinalCorAtlas.lean:120 [C] | FULL | Corrected statement (author agreed): M f.g., X separated, N f.g. or X l.f.p. Printed case (b) without separated not covered. | joint-build / axioms clean |
| Rem 8.4 | Pointer | — | NO CONTENT |  | — |
| Prop 8.5 | X^N = X^{N_c} | `prop85` Sec8Limits.lean:1382 [J]<br>`prop85_free` FinalAtlasFree.lean:30 [C]<br>`prop85_printed` PrintedProp85.lean:361 [J]<br>`prop85_atlasFree` FinalCorAtlas.lean:62 [C]<br>`prop85_general` Prop85General.lean:33 [C] | FULL | L.f.p. and `S` qc added (author agreed). `prop85_general`: no atlas, `S` qc, NOT necessarily separated, X separated l.f.p., `X -> S` qc (as printed); local over a finite affine cover of `S`, `N_c` = sup of the local ones and `N^x`. `S` qc is necessary (S = infinite disjoint union of Spec Z, X = A^1 on the i-th copy with weight (-i,1) in Z^2, N = {b>0} u {(a,0), a>=0}). `prop85_atlasFree` (= `prop85_free`): X qc, S qc separated. `prop85`: any S, S-affine atlas as hypothesis. `prop85_printed`: printed Tag 03I2 step, same hypotheses as `prop85`. | joint-build / axioms clean |

## §9 Hochschild cohomology

| No. | Content | Lean | Status | How | Oleans |
|---|---|---|---|---|---|
| Prop 9.1 | f_*f^*F = F ⊗ A | `IsQCoh.base_change_prod` Sec9General.lean:2145 [J]<br>`prop91_canonical` Sec9OverBReal.lean:524 [C]<br>`prop91_of_local` Sec9OverBReal.lean:555 [C]<br>`prop91_printed` Sec9OverBBridge2Printed.lean:49 [C]<br>`prop91_iso` FinalProp91.lean:53 [C]<br>`fam_printed` Sec9OverBBridge3QCoh.lean:407 [C] | FULL | Printed canonical map, for `PrintedQCoh`, on all affine objects: bijective, additive, compatible with restrictions. So an isomorphism of sheaves on the base of affine objects; the sheaf tensor product is not formed as an object. The two former b2 stubs are now Stacks theorems (`fpqcDescentOfQuasicoherentHoms` FpqcHomSheafRefinement.lean:329, `exists_bijective_sectionsBaseChange` AssociatedAffineSections.lean:252). Linked to `Space.Modules` on B by `fam_printed`. | joint-build / axioms clean |
| Def 9.2 | H-O_B-module | `HModule` Sec9General.lean:259 [J] | FULL |  | joint-build |
| Rem 9.3 | Differs from 2.20 | — | NO CONTENT |  | — |
| Def 9.4 | Cochains, differential | `Cochain` Sec9General.lean:290 [J]<br>`cochainEquivNatTrans` Sec9General.lean:350 [J]<br>`delta` Sec9General.lean:388 [J] | FULL |  | joint-build |
| Def 9.5 | Sheaf of cochains | `Cochain` Sec9General.lean:290 [J] | FULL |  | joint-build |
| Rem 9.6 | delta o delta = 0 | `delta_delta` Sec9General.lean:417 [J] | FULL |  | joint-build |
| Def 9.7 | Z^n, B^n, H^n | `Zn` Sec9General.lean:423 [J]<br>`Bn` Sec9General.lean:427 [J]<br>`Hn` Sec9General.lean:439 [J] | FULL |  | joint-build |
| Rem 9.8 | Explicit Z^1, B^1 | `mem_Z1_iff` Sec9General.lean:470 [J]<br>`mem_B1_iff` Sec9General.lean:490 [J] | FULL |  | joint-build |
| Prop 9.9 | Hom(F,G)(X) = Hom(F, G ⊗ A) | `homAtEquivHomPush` Sec9General.lean:575 [J]<br>`prop99_space` Sec9OverBReal.lean:583 [C]<br>`homAtEquivHomPush` Sec9OverBFinal.lean:196 [C]<br>`prop99_printed` Sec9OverBBridge2Printed.lean:61 [C]<br>`prop99_modules` Sec9OverBBridge3QCoh.lean:417 [C]<br>`homAtEquivHomTo` Sec9Full.lean:67 [C]<br>`homAtEquivHomTo_pull` Sec9Full.lean:125 [C]<br>`prop99_full_tensor` Sec9Full.lean:140 [C] | FULL | Whole site: target `f_* f^* G` on every object of the site of B (= G ⊗ 𝒜 as a sheaf, `prop91_sheaf`), no gluing on affine objects. Flatness, finite presentation not used. | joint-build / axioms clean / overlay, axioms clean |
| Prop 9.10 | H-module = comodule | `hModuleEquivCoaction` Sec9General.lean:678 [J]<br>`prop910_space` Sec9OverBReal.lean:590 [C]<br>`hModuleEquivCoaction` Sec9OverBFinal.lean:319 [C]<br>`prop910_printed` Sec9OverBBridge2Printed.lean:67 [C]<br>`prop910_modules` Sec9OverBBridge3QCoh.lean:422 [C]<br>`hModuleEquivCoactionFull` Sec9Full.lean:173 [C]<br>`coactionEquivAff` Sec9Full.lean:224 [C] | FULL | Same form as 9.9. Whole site: target `f_* f^* G` on every object of the site of B (= G ⊗ 𝒜 as a sheaf, `prop91_sheaf`), no gluing on affine objects. | joint-build / axioms clean / overlay, axioms clean |
| Prop 9.11 | Orthogonal idempotents | `hModuleEquivDecomp` Sec9General.lean:2100 [J]<br>`hModuleEquivDecomp` Sec9OverB.lean:1474 [J]<br>`coactionEquivDecomp` Sec9OverBReal.lean:605 [C]<br>`prop911_printed` Sec9OverBBridge2Printed.lean:76 [C]<br>`prop911_modules` Sec9OverBBridge3QCoh.lean:430 [C]<br>`prop911_full` Sec9Full.lean:240 [C]<br>`prop911_full_printed` Sec9Full.lean:244 [C] | FULL | Corrected wording (finiteness at each section over affine objects, i.e. locally). Comodules on the whole site as in 9.9 (`Sec9Full.lean`). | joint-build / axioms clean / overlay, axioms clean |
| Prop 9.12 | Formula for the complex | `cochainEquivSec` Sec9OverB.lean:834 [J]<br>`cochainVEquivSec` Sec9OverB.lean:1696 [J]<br>`phiC_bijective` Sec9OverB.lean:839 [J]<br>`delta_phiC` Sec9OverB.lean:1125 [J]<br>`cochainVEquivFinsupp` Sec9OverBFinal.lean:516 [C]<br>`prop912_space` Sec9OverBReal.lean:625 [C]<br>`prop912_printed` Sec9OverBBridge2Printed.lean:81 [C]<br>`prop912_modules` Sec9OverBBridge3QCoh.lean:435 [C] | PARTIAL | Direct sum over qc V is an Equiv only; QCCover is a Lean formulation, discharged for qc spaces. Same module notion as 9.11. | joint-build / overlay, axioms clean / axioms clean |
| Prop 9.13 | H^1 = 0 | `H1_subsingleton` Sec9OverB.lean:1182 [J]<br>`H1_base` Sec9OverB.lean:1635 [J]<br>`exists_deltaV_eq` Sec9OverB.lean:1600 [J]<br>`prop913_of_coaction` Sec9OverBReal.lean:632 [C]<br>`prop913_printed` Sec9OverBBridge2Printed.lean:87 [C]<br>`prop913_modules` Sec9OverBBridge3QCoh.lean:441 [C] | PARTIAL | B a space, any V. Same module notion as 9.11. | joint-build / axioms clean / overlay, axioms clean |
| Rem 9.14 | Conjecture: H^n = 0 | `Hn_subsingleton` Sec9OverB.lean:1187 [J]<br>`Hn_base` Sec9OverB.lean:1641 [J] | PARTIAL | Printed conjecture proved for n >= 1. Same module notion as 9.11. | joint-build |

## §10 Deformations

| No. | Content | Lean | Status | How | Oleans |
|---|---|---|---|---|---|
| Prop 10.1 | Equivariant filling if H^1 = 0 | `exists_invariant_lift` Sec10PrintedMain.lean:262 [J]<br>`exists_equivariant_of_lift_printed` Sec10PrintedCor.lean:62 [J]<br>`exists_invariant` Sec10PrintedCore.lean:146 [J]<br>`prop101_general` Prop101General8.lean:96 [J] | PARTIAL | Corrected (X' affine, author agreed). General G = Spec H, H a commutative Hopf algebra: `prop101_general`, with S = Spec R affine, Y, Z schemes, H^1 = 0 in Hochschild form (`HochschildH1Vanish`, equal to the printed hypothesis for H flat), non-equivariant lift as input. D(M) forms in the printed torsor/cocycle frame. | joint-build |
| Rem 10.2 | Comparison | — | NO CONTENT |  | — |
| Cor 10.3 | Filling for D(M) | `exists_equivariant_lift_scheme` Sec10LiftsCor.lean:179 [J]<br>`exists_equivariant_lift_spec` Sec10PrintedCor.lean:117 [J]<br>`exists_equivariant_of_lift` Sec10LiftsCore.lean:466 [J]<br>`exists_equivariant_of_lift` Sec11SpacesCore.lean:239 [C]<br>`lift103` Sec11SpacesLift.lean:223 [C] | PARTIAL | Corrected (X' affine, author agreed). Schemes. Spaces: upgrade of a given lift, and lift103 on A(N)_{T0} -> A(N)_T; printed square for spaces is a short missing corollary. Integration route (REMARKS.md). | joint-build / axioms clean |

## §11 Formal smoothness

| No. | Content | Lean | Status | How | Oleans |
|---|---|---|---|---|---|
| Prop 11.1 | f smooth: f^N formally smooth | `isFormallySmooth_attractorMap_spaces` Sec11SpacesLift.lean:275 [C]<br>`isFormallySmooth_attractorMap_scheme` Sec11Schemes.lean:273 [J] | FULL | Spaces; site cutoff SM B M. Integration route for Cor 10.3 (REMARKS.md). | axioms clean / joint-build |
| Cor 11.2 | f^N smooth | `isSmooth_repMap_spaces` Sec11SpacesCor.lean:68 [C]<br>`smooth_repMap` Sec11SchemesRep.lean:84 [J] | FULL | Spaces; site cutoff SM B M. Integration route for Cor 10.3 (REMARKS.md). Attractors assumed representable by spaces, as printed. | axioms clean / joint-build |
| Prop 11.3 | Formally unramified | `formallyUnramifiedFor_attractorMap` Sec11Formal.lean:51 [J]<br>`isFormallyUnramified_attractorMap` Sec11Formal.lean:333 [J] | FULL | `MagnetInSite`. | joint-build |
| Cor 11.4 | Representable case | `isFormallyUnramified_of_represents` Sec11Formal.lean:345 [J] | FULL |  | joint-build |
| Prop 11.5 | Formally étale | `isFormallyEtale_attractorMap_spaces` Sec11SpacesCor.lean:58 [C]<br>`isFormallyEtale_attractorMap_scheme` Sec11SchemesFace.lean:74 [J] | FULL | Spaces; site cutoff SM B M. Integration route for Cor 10.3 (REMARKS.md). Printed l.f.p. unused. | axioms clean / joint-build |
| Cor 11.6 | f^N étale | `isEtale_repMap_spaces` Sec11SpacesCor.lean:80 [C]<br>`etale_repMap` Sec11SchemesRep.lean:94 [J] | FULL | Spaces; site cutoff SM B M. Integration route for Cor 10.3 (REMARKS.md). | axioms clean / joint-build |
| Prop 11.7 | X^N -> X^F formally smooth | `isFormallySmooth_faceMap_spaces` Sec11SpacesFace.lean:73 [C]<br>`isFormallySmooth_faceMap_of_isSmooth` Sec11SpacesCor.lean:159 [C]<br>`isFormallySmooth_faceMap_scheme` Sec11SchemesFace.lean:278 [J] | FULL | Spaces; site cutoff SM B M. Integration route for Cor 10.3 (REMARKS.md). | axioms clean / joint-build |
| Fact 11.8 | Push-out | `fact118_equivariant_pushout` Fact118General.lean:48 [J]<br>`fact118_affine` Fact118General.lean:35 [J]<br>`fact118_pushout_spaces`, `fact118_overT`, `fact118_equivariant_desc` Final3Fact118.lean [J]<br>`pushoutRing` Sec11Formal.lean:553 [J] | FULL | T affine, first order thickening (as printed); push-out in algebraic spaces with equivariant morphisms. | joint-build |
| Lem 11.9 | First-order thickening | `lemma119` Fact118General.lean:40 [J]<br>`pushoutMap_mul_eq_zero` Sec11Formal.lean:628 [J]<br>`pushoutMap_eq_zero_iff` Sec11Formal.lean:634 [J] | FULL | Morphism of schemes, T affine (as printed). | joint-build |
| Cor 11.10 | X^N -> X^F smooth | `isSmooth_repFace_spaces` Sec11SpacesCor.lean:168 [C]<br>`smooth_repFace` Sec11SchemesRep.lean:179 [J] | FULL | Spaces; site cutoff SM B M. Integration route for Cor 10.3 (REMARKS.md). | axioms clean / joint-build |
| Rem 11.11 | External counterexample | `rem1111_flat` FinalRem1111.lean:73 [J]<br>`rem1111_not_flat` FinalRem1111.lean:95 [J] | FULL | Printed text only cites Mathoverflow. Example constructed here: M = Z, N = 0, X = Spec k[x,y] weights 1,-1, Y = Spec k[t] trivial action, t -> xy: flat, and X^0 -> Y^0 is t -> 0 on k[x,y]/(A_m, m != 0). Ring form; the link to X^0 is Thm 3.20 (`isLeast_ker_iAtt`). | joint-build |
| Rem 11.12 | External counterexample | `rem1112_CM` FinalRem1112.lean:178 [J]<br>`rem1112_not_CM` FinalRem1112.lean:323 [J]<br>`rem1112_ideal` FinalRem1112.lean:189 [J] | FULL | Printed text only cites Mathoverflow. Example constructed here: M = Z, N = 0, k[u,v,x1,y1,x2,y2]/(u^2-x1y1, uv-x2y2), weights 0,0,1,-1,1,-1: Cohen-Macaulay at every prime; X^0 = k[u,v]/(u^2,uv) is not, at (u,v). Ring form, as Rem 11.11; the link to X^0 is Thm 3.20 (`isLeast_ker_iAtt`). | joint-build |

## §12 Topology

| No. | Content | Lean | Status | How | Oleans |
|---|---|---|---|---|---|
| Prop 12.1 | Geom. connected fibres, bijection on pi_0 | `prop121_printed` Sec12Final.lean:863 [J]<br>`prop121_of_atlas` Sec8Theorem83.lean:1728 [J] | FULL | Real topology of |X| (Tag 03BY). X separated through the agreed correction of Thm 8.3, no other addition. Geometric connectedness read as connected fibres over all field-valued points. Printed proof followed: Prop 3.31, orbit map, section. | joint-build |
| Prop 12.2 | f open/closed immersion gives same on f^N | `isOpenImmersion_repAttractorMap` Sec12Spaces.lean:411 [J]<br>`isPullback_repAttractorMap_open` Sec12Spaces.lean:379 [J]<br>`isOpenImmersion_repMap` Sec11SchemesRep.lean:120 [J]<br>`prop122_ii_printed` Sec12Final.lean:890 [J]<br>`isClosedImm_repAttractorMap` Sec12Topology.lean:1007 [J]<br>`prop122_i_printed` PrintedProp122.lean:34 [C] | FULL | (i) spaces, direct route; printed route `prop122_i_printed`, axioms clean. (ii) printed (a), (b), (c). | joint-build / axioms clean |
| Prop 12.3 | Strong deformation retract | `deformation_spec` Sec12Topology.lean:423 [J]<br>`exists_strong_deformation_retract` Sec12Topology.lean:480 [J] | FULL | N f.g. in a group, any functor. | joint-build |
| Thm 12.4 | Affine space fibration | `thm124_attP` FixesThm124.lean:75 [J]<br>`thm124_induced_face` FixesThm124.lean:39 [J]<br>`thm124_spaces` Sec12SpacesThm.lean:340 [J]<br>`thm124_general` Sec12Final.lean:542 [J]<br>`thm124_affineSpace` Sec12Final.lean:787 [J] | FULL | Spaces, M f.g. (standing in §12), N arbitrary. Fibration is Zariski-local on S; the global form of the printed proof fails (Paper corrections). | joint-build |
| Cor 12.5 | A(N)_S smooth: vector bundle | `cor125` Sec12PrintedCor.lean:74 [J]<br>`cor125_global` FinalCor125.lean:312 [J]<br>`augN` FinalCor125.lean:45 [J] | FULL | Global: S nonempty, N f.g. sharp. `gen : N^(Irr N) -> N` is bijective and A(N)_S -> A(N^(Irr N))_S is an isomorphism over S, so a trivial vector bundle: stronger than the print. Injectivity by `phi_injective`, the printed proof of Thm 12.4, section s from the irreducibles. Affine form `cor125` stays. S empty is trivial and not stated. | joint-build |

## §13 Dilatations

| No. | Content | Lean | Status | How | Oleans |
|---|---|---|---|---|---|
| Prop 13.1 | (Bl_Y^D X)^N = Bl_{Y^N}^{D^N} X^N | `prop13_1_spaces` Sec13Spaces.lean:1571 [J]<br>`blAction` Sec13Spaces.lean:1252 [J]<br>`prop13_1_printed` Sec13General.lean:1478 [J]<br>`prop13_1_of_isAffineHom` Sec13General.lean:1493 [J] | FULL | Spaces; attractors represented by sheaves; flatness as a flat etale atlas of (Bl)^N. Statement read here; no checker pass on record. | joint-build |
| Rem 13.2 | Reference | — | NO CONTENT |  | — |
| Cor 13.3 | Smooth case | `cor13_3_free` Cor133Spaces.lean:52 [C]<br>`cor13_3` SecFinal1316.lean:1178 [J]<br>`cor13_3_of_smooth` SecFinal1316.lean:987 [J]<br>`smooth_of_isDilatation` SecFinal1316.lean:1054 [J] | FULL | No representability assumed: X^N and (Bl_Y^D X)^N algebraic spaces by Thm 8.3 (`thm83_general`), Y^N the attractor functor. Hypotheses of the agreed Thm 8.3: M f.g., X separated (printed: M any abelian group). Bl_Y^D X separated (affine over X), l.f.p. from smoothness. | joint-build |
| Rem 13.4 | Use | — | NO CONTENT |  | — |

## §14 Ind-spaces

| No. | Content | Lean | Status | How | Oleans |
|---|---|---|---|---|---|
| Def 14.1 | Ind-algebraic space | `IndPresentation` Sec14Ind.lean:34 [J]<br>`IsIndAlgebraicSpace` Sec14Ind.lean:61 [J]<br>`IsIndScheme` Sec14Ind.lean:65 [J] | FULL |  | joint-build |
| Rem 14.2 | Hom, fibre products, ind-P | `remark142` FixesSec14.lean:31 [J]<br>`remark142_of_quasiCompact` FixesSec14.lean:60 [J]<br>`isIndAlgebraicSpace_fibreProduct_of_gluing` Sec14Glue.lean:675 [O]<br>`isIndScheme_fibreProduct_of_gluing` Sec14Glue.lean:691 [O]<br>`HasIndProp` Sec14Remaining.lean:34 [J] | FULL | Fibre products without quasi-compactness. Property P tested on affine T only. | joint-build / real, overlay |
| Def 14.3 | Categorical action, ind-action | `CatAction` Sec14Remaining.lean:78 [J]<br>`IndActionG` Sec14Remaining.lean:100 [J]<br>`IndActionG.toCatAction` Sec14Remaining.lean:123 [J] | FULL |  | joint-build |
| Prop 14.4 | X^N = colim X_i^N | `isIndAlgebraicSpace_attractor` Sec14Ind.lean:327 [J]<br>`isIndScheme_attractor` Sec14Remaining.lean:161 [J]<br>`prop144_of_atlas` Sec8Theorem83.lean:1743 [J]<br>`indAttractorMap_rep_nat` Sec14Strong.lean:177 [J]<br>`indAttractorMap_rep_scheme_nat` Sec14Strong.lean:191 [J]<br>`prop144_closed_corrected` FixesSec14.lean:81 [J]<br>`not_isClosedImm_polynomial` Sec14Counterexample.lean:371 [J]<br>`prop144_free` FinalCorAtlas.lean:133 [C]<br>`prop144_free_of_coproducts` FinalCorAtlas.lean:147 [C]<br>`prop144_general` FinalNonQCGeneral.lean:138 [C]<br>`prop144_rep_general` FinalNonQCClauses.lean:105 [C]<br>`prop144_closed_general` FinalNonQCClauses.lean:114 [C]<br>`prop144_scheme_general` FinalNonQCClauses.lean:135 | PARTIAL | Last assertion false as printed: counterexample in Lean. Corrected form (author agreed): Z-FPR atlas on each term. No atlas hypothesis, S arbitrary, terms separated l.f.p. (not necessarily qc): ind-algebraic space (`prop144_general`), X^N -> X representable (`prop144_rep_general`), X^Z -> X closed immersion (`prop144_closed_general`), ind-scheme variant (`prop144_scheme_general`). Remaining restriction: terms separated, l.f.p. | joint-build / axioms clean |

## §15 Pure magnets

| No. | Content | Lean | Status | How | Oleans |
|---|---|---|---|---|---|
| Prop 15.1 | Equivalent definitions of pure | `isPure_iff_lt` Sec15PureMagnets.lean:82 [J]<br>`prop151_scheme` Sec3SchemeQuotient.lean:1714 [J]<br>`prop151_of_atlas` Sec3Intersections.lean:595 [J]<br>`prop151_weak` Sec3IntersectionsWeak.lean:388 [J]<br>`prop151_free` FinalAtlasFree.lean:54 [C]<br>`attractorOrder_nonqc` FinalNonQCFact.lean:285 [C] | PARTIAL | Separated schemes without atlas; spaces with atlas. Spaces without atlas: `isPure_iff_lt` applied to `attractorOrder_nonqc`, X separated l.f.p. (not necessarily qc), S separated; for S arbitrary the same order is built inside `thm153_general`, not named. Restriction: l.f.p. added. | joint-build / axioms clean |
| Def 15.2 | Pure magnets | `IsPure` Sec15PureMagnets.lean:40 [J]<br>`pureMagnets` Sec15PureMagnets.lean:44 [J]<br>`attractorImage` Sec15PureMagnets.lean:170 [J] | FULL |  | joint-build |
| Thm 15.3 | Π(a) = attractors | `pureEquivRange` Sec15PureMagnets.lean:116 [J]<br>`thm153_strong` Sec15Final.lean:221 [J]<br>`thm153_lfp` Sec15Final.lean:520 [J]<br>`thm153_free` FinalCorAtlas.lean:53 [C]<br>`thm153_nonqc` FinalNonQCFact.lean:294 [C]<br>`thm153_general` FinalNonQCLocal.lean:121 [C] | PARTIAL | No atlas: `thm153_general`, X separated, l.f.p. added (not printed), not necessarily qc, S arbitrary, M f.g. With an S-affine atlas: X l.f.p. (or limit preserving with finite-type atlas), any S. Restriction: l.f.p. | joint-build / axioms clean |
| Thm 15.4 | Π(a) finite | `thm154_i` Sec15General.lean:715 [J]<br>`thm154_ii_lfp` Sec15Final.lean:531 [J]<br>`thm154_ii_of_linearizable` Sec15Final.lean:549 [J]<br>`thm154_ii_of_linearizable_qc` Sec15Final.lean:620 [J] | FULL | S qc added (printed false otherwise). (ii) X separated, locally of finite presentation; Zariski locally linearizable case through Fact 7.3, with X qc and finite coproducts in the site (size cutoff). | joint-build |
| Prop 15.5 | U^N = U^L implies X^N = X^L | `prop155_printed` Sec15Final.lean:493 [J]<br>`prop155_printed_pure` Sec15Final.lean:512 [J]<br>`prop155` Sec15General.lean:354 [J] | FULL | M f.g., X separated, limit preserving. Printed route: Thm 8.3, Prop 5.1, Cor 11.6 for the atlas only (`chartToAttr_etale_surjective` Sec15Final.lean:367); Tags 0AHE, 05W5 replaced by mono + locally surjective. | joint-build |
| Rem 15.6 | Set of X^{D(M/Z)} finite | `rem156_lfp` Sec15Final.lean:539 [J] | FULL | Hypotheses of 15.4 (ii). | joint-build |
| Rem 15.8 | Conj 6.9 implies Conj 15.7 | `rem158_printed` SecLeftover158.lean:48 [J]<br>`Conj69iiPrinted` SecLeftover158.lean:28 [J]<br>`Conj157Printed` SecLeftover158.lean:39 [J]<br>`rem158` Sec15General.lean:762 [J]<br>`rem158` FinalRem158.lean:44 [J]<br>`Conj69iiRel` FinalRem158.lean:25 [J]<br>`Conj157Rel` FinalRem158.lean:36 [J] | FULL | Conditional, with X quasi-compact over S as printed. M f.g. is assumed in Conj 6.9; S qc is required by Thm 15.4. The older `rem158_printed` stays, it used absolute quasi-compactness. | joint-build |
| Def 15.9 | Rank | `monoidRank` Sec15PureMagnets.lean:345 [J] | FULL |  | joint-build |
| Ex 15.10 | Trivial action; D(Z^n) on itself | `pureMagnets_trivial_action` Sec15General.lean:784 [J]<br>`ex1510_ii` SecLeftover1510.lean:165 [J]<br>`ex1510_ii_Zn` Sec3Leftover2A.lean:31 [J] | FULL | (ii) any nonempty S, G nontrivial; covers the printed S = Spec Z. | joint-build |
| Fact 15.11 | rk(Z^n) = n + 1 | `monoidRank_int_pi` Sec15PureMagnets.lean:377 [J] | FULL | n >= 1; printed formula fails at n = 0. | joint-build |

## §16 Complements

| No. | Content | Lean | Status | How | Oleans |
|---|---|---|---|---|---|
| Rem 16.1 | T(X x_Y Z), mono, TS = S | `tangentFibreProductIso` Sec16Tangent.lean:39 [J]<br>`mono_tangentMap` Sec16Tangent.lean:44 [J]<br>`tangentFinalIso` Sec16Tangent.lean:51 [J] | FULL |  | joint-build |
| Prop 16.2 | (TX)^N = T(X^N) | `tangentAttractorIso` Sec16Tangent.lean:172 [J]<br>`tangentAttractorIsoFppf` Sec16Remaining.lean:88 [J] | FULL |  | joint-build |
| Rem 16.3 | Lie of fibre product, mono, Lie(e_S) | `lieFibreIso` Sec16Lie.lean:231 [J]<br>`mono_lieMor` Sec16Lie.lean:211 [J]<br>`lieTrivialIso` Sec16Lie.lean:221 [J] | FULL |  | joint-build |
| Prop 16.4 | Lie(G)^N = Lie(G^N) | `lieAttractorIso` Sec16Lie.lean:336 [J]<br>`lieAttractorIsoFppf` Sec16Remaining.lean:94 [J] | FULL |  | joint-build |
| Prop 16.5 | Lie(G)^N_{Lie H} = Lie(G^N_H) | `lieAttractorLimitIso` Sec16Lie.lean:397 [J] | FULL | Any face. | joint-build |
| Prop 16.6 | G^N semidirect product | `attrSemidirect` Sec16Lie.lean:458 [J]<br>`attrMulIso` Sec16Lie.lean:481 [J] | FULL | Any face. | joint-build |
| Rem 16.7 | Extends a cited theorem | — | NO CONTENT |  | — |
| Prop 16.8 | Reductive | — | EXCLUDED |  | — |
| Prop 16.9 | Reductive | — | EXCLUDED |  | — |
| Prop 16.10 | Reductive | — | EXCLUDED |  | — |
| Rem 16.11 | Reductive | — | EXCLUDED |  | — |
| Prop 16.12 | Reductive | — | EXCLUDED |  | — |
| Cor 16.13 | Reductive | — | EXCLUDED |  | — |
| Def 16.14 | Root groups as attractors | `rootAttr` Sec16Lie.lean:491 [J]<br>`rootKernel` Sec16Lie.lean:496 [J] | FULL |  | joint-build |
| Prop 16.15 | (i) closed, (ii) smooth, (iii) Lie | `prop1615_i` Sec16Remaining.lean:134 [J]<br>`prop1615_ii` SecLeftover1615.lean:104 [J]<br>`prop1615_ii_spaces` SecLeftover1615Spaces.lean:147 [C]<br>`prop1615_ii_of_isAffineHom` SecFinal1316.lean:156 [J]<br>`prop1615_ii_free` Prop1615Free.lean:128 [C]<br>`prop1615_ii_general` Prop1615General.lean:32 [C]<br>`lieRootAttrIsoFppf` Sec16Remaining.lean:102 [J]<br>`lieRootKernelIsoFppf` Sec16Remaining.lean:107 [J] | PARTIAL | (i), (iii) in full. (ii) attractors assumed representable, except G affine; spaces with cutoff SM. `prop1615_ii_free`: no representability assumed, G separated, l.f.p., qc, S separated, M f.g. (Thm 8.3 via Thm 6.8 atlas). `prop1615_ii_general`: G separated, M f.g., no qc, S arbitrary, l.f.p. from smoothness (Thm 8.3 `thm83_general`). Printed (p. 193): G a scheme, M any abelian group, only G/S smooth. | joint-build / stubs |
| Prop 16.16 | Reductive | — | EXCLUDED |  | — |
| Rem 16.17 | Reductive | — | EXCLUDED |  | — |

## Appendix A (Romagny)

| No. | Content | Lean | Status | How | Oleans |
|---|---|---|---|---|---|
| Thm A.1 | Flat f.p. connected fibres: X^G closed, étale equivariant maps FPR | `a1_closed` SpacesLimitA1.lean:319 [C]<br>`a1_isFPR` SpacesLimitA1.lean:360 [C]<br>`a1_closed_noetherian` SpacesLimitA1.lean:401 [C]<br>`a1_isFPR_noetherian` SpacesLimitA1.lean:413 [C]<br>`thmA1_closed` AppendixA3.lean:2044 [J]<br>`thmA1_isFPR` AppendixA3.lean:2063 [J]<br>`isFPR_of_etale` AppendixA.lean:526 [J] | PARTIAL | G = D(M) with connected fibres only (TorsionResidue); general flat f.p. G absent. Cases (i), (ii); hZ explicit in (ii). | axioms clean / overlay, axioms clean / joint-build |
| Thm A.2 | Existence of Z-FPR atlases (= 6.8) | `thm68` ChartFinal.lean:43 [C]<br>`thm68_i` ChartThm68.lean:133 [C]<br>`thm68_ii_of_charts` SpacesLimitThm68.lean:340 [C]<br>`isSAffineAtlas_of_family` ChartAtlas.lean:210 [J]<br>`a1_isZFPR` SpacesLimitA1.lean:377 [C]<br>`thm68_family_spaces` ChartFinalSpaces.lean:31 [C]<br>`thm68_qc_spaces` ChartFinalSpaces.lean:44 [C] | PARTIAL | = Thm 6.8, same restrictions; (i) in the forms `thm68_atlas` FinalNonQCAtlas.lean:106 [C], `thm68_relqc` FinalNonQCRelQC.lean:33 [C]. | axioms clean / joint-build |
| Lem A.3 | F finite locally free infinitesimal: X^F closed | `lemmaA3` AppendixA3.lean:1214 [J]<br>`exists_ideal_chart` AppendixA3.lean:640 [J]<br>`lemmaA3_affine` AppendixRemaining.lean:1027 [J]<br>`lemA3_affine` FinalLemA3.lean:62 [J]<br>`lemA3_general` FinalLemA3General.lean:351 [J] | FULL | General F on an algebraic space, printed proof; representability is contained in the closed immersion, so the printed Weil restriction is not used. Finite locally free infinitesimal F is read by `PointedFinFlat`, on affine T: F_T affine, functions finite projective, unit section a nil-thickening, dual compatible with base change (field `bc`). Action as printed, no group law. | joint-build |
| Lem A.4 | Finiteness of A/I_n | `lemmaA4` AppendixA.lean:51 [J] | FULL | Statement matches. Route differs (REMARKS.md). | joint-build |
| Lem A.5 | Cofinal neighbourhoods | `exists_E` AppendixA3.lean:1164 [J]<br>`lemmaA5` AppendixRemaining.lean:873 [J]<br>`step_free` AppendixRemaining.lean:409 [J] | PARTIAL | G = D(M) only. Blocker for general G: SGA3 VII_B 5.5.1 (Cohen-Macaulay fibres of group schemes) and EGA IV 18.12.1 are not available in Lean for a general flat f.p. group scheme, and the tree has no such G. | joint-build |
| Rem A.6 | Smooth case of A.5 | `remA6` FinalRemA6.lean:563 [J] | PARTIAL | Local form: A smooth R-algebra (f.p.) with augmentation of kernel I; A/I^{n+1} finite projective over R. Passage to a general G -> S not stated. The truncation of Sym(I/I^2) carries all degrees at once. | joint-build |
| Rem A.7 | Infinitesimal G | `remA7` FinalRemA7.lean:52 [J]<br>`connectedFibres_of_infinitesimal` FinalRemA7.lean:27 [J] | PARTIAL | Conclusion for G = D(M) infinitesimal, from `thmA1_closed`. The second proof through the quotient X/G ([30, Th. 5.3]) is not formalized, no quotient in Lean; general infinitesimal G absent. | joint-build |

## Unnumbered statements, not counted

- **§16.4.** (i) `stage_i_fppf`, `fixedStep_fppf`; (ii) `stages_fppf`, `stagesChainIso`, `stageTopIso`, `stagesBigIso` (FixesSec16.lean), `stagesChain_toPoint`, printed route `sec164_ii_printed` (PrintedSec164.lean, X a scheme); (iii) `exists_gmTower_fppf`, `exists_gmTower`. Residual torus action on the stages not stated. `Nonempty (forall T, Y1(T) = Fix(T))` in (i), Sec16Remaining.lean, carries no naturality.
- **Conjectures 6.9, 15.7.** Definitions: `Conj69iiPrinted`, `Conj157Printed`, `Conj69ii`, `Conj69iiRel`, `Conj157Rel`. S separated, axioms clean: Conj 6.9 is `conj69_separated` Conj69Separated.lean:29 ((i) `thm68_atlas`; (ii) S qc); Conj 15.7 is `conj157_separated` Conj157Separated.lean:57 (S separated qc, M f.g., X separated f.p.), through Rem 15.8. For S not separated 6.9 fails (`not_conj69_doubledPlane`). The mathematics of `notes/ahr-specialized-proof.md` has no independent check on record.
- **List after Fact 15.11.** (i) `pureMagnets_nat_self`, (ii) `pureMagnets_int_one`, (iii) `pureMagnets_int_two`, (v) `pureMagnets_int_prod` (Sec15Final.lean), (iv) `pureMagnets_p1` (SecFinal1316.lean), (vi) `pureMagnets_zmod_six`, (vii) `pureMagnets_two_three`, (ix) `pureMagnets_self_eq` (Sec15PureMagnets.lean).

## Open flags

1. **§9 over a genuine space `B`.** `PrintedQCoh` is the printed notion read on `(Sch/T)_fppf`, T affine; `fppf03DX` (Tag 03DX (1)) is proved; its former stubs `fpqcDescentOfQuasicoherentHoms`, `exists_bijective_sectionsBaseChange` are now Stacks theorems. A quasi-coherent module of `Space.Modules` on `B` gives `IsQCoh` (`fam_isQCoh`, axioms clean) and `PrintedQCoh` (`fam_printed`, axioms clean), Sec9OverBBridge3QCoh.lean.
2. **Thm 6.8 chart assembly.** Done, axioms clean (stubs of `notes/chart-stubs.md` discharged): `chartLemma`, `thm11_ft`, `thm68`, `thm68_family_spaces`, `thm68_qc_spaces`, `thm11_affine_spaces`, `thm68_atlas`, `thm68_relqc`. No independent check on the mathematics of `notes/ahr-specialized-proof.md` on record.
3. **`rem158_printed`** uses absolute quasi-compactness; `rem158` FinalRem158.lean is the printed form.
4. **Stale compile evidence.** Closed for the 231 joint-build modules. Overlay files carry their own compile records.
5. **Stacks modules still absent from the build:** 23 of the 24 modules in `.stubtargets` (only `Descent.IndQuasiAffineFpqcSheaf` is built), plus `SmallEtaleModulePullbackComp`, `SmallEtaleModulePullbackAssoc`, `SmallEtaleModulePushforwardCompIsoAssoc`, `ChartDiagramBaseChangeComparison`.
6. **Stray files:** `AlgMag/r14.txt`, `AlgMag/r16.txt`. `SecLeftover.lean` has duplicated imports and docstring bullets. Header of `Sec3Leftover328.lean` names `vAttractorIso`, which does not exist. Header of `Sec11SpacesFact.lean` writes the representability hypothesis as if printed. Docstring of `FixesThm124`/`Sec12SpacesThm` on "M finitely generated beyond the print" should go.

## Paper corrections

"Agreed": the author agreed. "To review": found by agents, not yet confirmed by the author. Printed quotes from the paper text; other quotes from Lean docstrings or checker reports.

**Agreed**

- **Prop 5.1.** Printed: "(i) N is finitely generated as monoid, (ii) X is separated". Printed proof of (i) does not check that the filling lies over `X`. Lean: `X` separated added in (i), l.f.p. in (ii). The non-separated case is open.
- **Thm 8.3.** Printed: "(a) X is separated over S, or (b) N is finitely generated as monoid". Lean: `M` f.g., `X` separated, and `N` f.g. or `X` l.f.p. Printed case (b) without separated not covered.
- **Prop 8.5.** Printed: "Assume that X -> S is quasi-compact and separated". L.f.p. and `S` quasi-compact added. Departure in the proof: "The printed proof applies Tag 03I2 to the property "isomorphism"; here the statement is unfolded on `T`-points."
- **Prop 10.1, Cor 10.3.** Printed: "Let X', X, Y and Z be S-algebraic spaces". Needs `X'` affine: "the proof picks a global section of `P`, and formal smoothness only gives one over affines."
- **Prop 14.4, last assertion.** "If N = Z is a group the natural morphism X^Z -> X is representable by a closed immersion." False as printed: `S = Spec Q[t]`, `X` the line with doubled origin, `M = Z/2`, `Z = 0`, `mu_2` swapping the origins, `X^0` is the open `t != 0` (`not_isClosedImm_polynomial` Sec14Counterexample.lean). Corrected: assume a `Z`-FPR atlas on each `X_i`, e.g. `X_i` separated or `M/Z` torsion-free by Thm 6.8 (`prop144_closed_corrected`).

**To review**

- **Thm 12.4, proof (by hand, not in Lean).** "finite locally free hence projective" and the sections `s_n` are taken before reducing to a ring. Fails on non-affine `S`: `S = P^1`, `A` locally `O[x,y]`, degrees 1, 2, `y' = g y + c x^2`, `A_2` a non-split extension of `O(2)` by `O`. The theorem survives Zariski-locally on `S`, as proved in Lean.
- **Prop 14.4, proof.** "follows from Corollary 8.1": should be Prop 8.1. Also to check, not refuted: the first assertion cites Prop 12.2, which assumes `X^N`, `Y^N` representable, and Prop 14.4 does not.
- **Rem 6.5.** "U -> S is smooth of relative dimension zero and so it is étale": false at 2 for `D(Z/2)` over `Spec Z` (`not_etale_printed_rem65`). True over `Z[1/2]`.
- **Rem 6.6.** Needs `[M : Z]` invertible on `S` and `Z != 0`.
- **Prop 3.32 (ii).** "the antidiagonal action of `D(N^gp + L^gp)` on `A(N) x A(L)` is not free, and `A(⋂ N_l)` is not a colimit of a decreasing system."
- **Fact 3.34, proof.** "`A(⋂ N_l)_S = colim_J A(⋂_J N_l)_S` fails in schemes" (`chain_no_point`).
- **Prop 3.37.** "The statement in the paper for arbitrary `T` is false when `T` is not quasi-compact."
- **Prop 9.11.** "The printed "only finitely many of the (ρ_m) are nonzero locally" is false" (`regular_comp_ne_zero`).
- **Thm 15.4.** Needs `S` quasi-compact: `X = ⊔ A^1` over `⊔ Spec k` with weight `n` on the `n`-th copy.
- **Fact 15.11.** "`Z^0 = 0` has rank `0`", the formula fails at `n = 0`.
- **Example (vi) after Fact 15.11.** "`Π(a) = {0, Z/6}`: two elements, not the four printed."
- **Rem 2.9.** "`(4, 5)` does *not* lie in the orbit of `(3, 4)`"; witness `(5, 6)`.
- **Prop 2.19, citation.** Tag 0ET0 does not apply: "`A(L) -> A(N)` is not integral in general".
- **Prop 16.15 (ii), proof.** Attributes smoothness of `G^[α>` over `S` to Cor 11.10, which only gives `Y -> Y0`; the input is Cor 11.2 with target `S`.
- **§16.4 (i).** An attractor under `D(Zα)`, which is `G_m` only when `α` is not torsion; the paper does not state this.

**Not a correction**

- **Ex 15.10 (ii).** An agent reported "false for `S` empty" (`ex1510_ii_empty`). The checker withdrew it: by Rem 2.5, `D(Z^n)` without subscript is over `Spec Z`, and `ex1510_ii_Zn` proves the literal print. The false reading concerns only a generalization to arbitrary `S`.

Departures from printed proofs are in `REMARKS.md`.

## Counts

| Section | FULL | PARTIAL | ABSENT | NO CONTENT | EXCLUDED | Total |
|---|---|---|---|---|---|---|
| §1 | 1 | 1 | 0 | 1 | 0 | 3 |
| §2 | 21 | 0 | 0 | 1 | 0 | 22 |
| §3 | 28 | 6 | 0 | 3 | 0 | 37 |
| §4 | 3 | 0 | 0 | 0 | 0 | 3 |
| §5 | 1 | 0 | 0 | 0 | 0 | 1 |
| §6 | 6 | 1 | 0 | 1 | 0 | 8 |
| §7 | 3 | 0 | 0 | 2 | 0 | 5 |
| §8 | 2 | 1 | 0 | 2 | 0 | 5 |
| §9 | 7 | 6 | 0 | 1 | 0 | 14 |
| §10 | 0 | 2 | 0 | 1 | 0 | 3 |
| §11 | 10 | 2 | 0 | 0 | 0 | 12 |
| §12 | 5 | 0 | 0 | 0 | 0 | 5 |
| §13 | 1 | 1 | 0 | 2 | 0 | 4 |
| §14 | 3 | 1 | 0 | 0 | 0 | 4 |
| §15 | 8 | 2 | 0 | 0 | 0 | 10 |
| §16 | 7 | 1 | 0 | 1 | 8 | 17 |
| App. A | 2 | 5 | 0 | 0 | 0 | 7 |
| **All** | **108** | **29** | **0** | **15** | **8** | **160** |

Of these: 0 rows wait for AHR (tag retired 2026-11-09). No row in this tracker rests on stubs, except Prop 16.15, not revised here.
