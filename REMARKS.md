# Remarks: departures from the printed proofs

Kept aside; the formalization should follow the paper (`notes/AGENT_RULES.md`). Sources: file headers and the workflow reports of 2026-11-06.

Action: **Forced**, a printed step is wrong or unavailable, so the departure stays. **To redo**, no printed error requires it. **Add printed version**, keep this proof as a remark and add the printed route. **Keep**, same content, printed citation not usable in Lean. **Author's call**, doing it literally has a real cost. Nothing here is a change of statement unless the row says so; statements are in `STATUS.md`.

## Algebraic Magnetism

| Statement | Lean route | Printed route | Action |
|---|---|---|---|
| Fact 2.6 | Coordinates on charts: `isPullback_jS`, `sections_of_isPullback`, `cmp` (FixesFact26) | Spec Z, Tags 01ID, 01SA, 01AJ; (ii) 03M1, 081V, 03DC | To redo |
| Fact 2.6 (ii) | `ONB` on the site SB of §9; `cmpT_*` | B_{spaces,etale}, Tags 03M1, 081V, 03DC | Author's call, as §9 |
| Prop 2.8(i) | Direct freeness of R[Q] over R[P] | Ogus Prop 4.5.12 | Keep |
| Prop 2.19 | `GeneralBaseMilnor` | Tag 0ET0 | Forced: map not integral |
| Prop 2.21 | Action to decomposition by Prop 9.11, then to grading (`prop221`) | Cites SGA3 I 4.7.3 | Keep |
| Rem 3.13 | Stated on the scheme `Zatt`, because of universes; `zE_zAct`, `zE_zActM` tie it to the presheaf | Definitions | Keep |
| Fact 3.16 | Tag 03KP(3), `isClosedImmersion_of_isSeparated_of_section` | Tag 0AGC | Keep |
| Fact 3.19, spaces | Tag 049J, Tag 0CM6, limit of `A(N)_{T_i}`; port of the scheme proof | Direct | Keep |
| Prop 3.28 | Adjoint form `Hom_{O_S}(E, p_*O_T)`, graded step on affine opens | `Hom_{O_T}(p^*E, -)` | Keep: form of `vectorBundleHomEquiv` |
| Prop 3.32 (ii), Fact 3.34 | Scheme quotient replaced; family case via atlas | Free action, fpqc quotient; colimit of `A(⋂_J N_l)` | Forced |
| Prop 5.1 | All faces at once | Reduction to N^× via Prop 3.31 | Done where valid: `prop51_i_printed` (PrintedProp51), X a separated scheme, M f.g.: Prop 3.31 (ii) is formalized for schemes only, and printed only for M f.g. For X a space the direct proof stays |
| Thm 6.8 (i) | Chart lemma by `notes/ahr-specialized-proof.md`: graded completion, Artin approximation, Lemma 11; limit to `Spec ℤ` in `SpacesLimit*` | Corollary of Alper-Hall-Rydh | Forced: AHR not in Lean |
| Prop 6.3 | Through A.1, FPR part | Same, by A.1 printed proof | See Thm A.1 |
| Prop 8.5 | Statement unfolded on T-points | Tag 03I2 for "isomorphism" | Done: `prop85_printed`, `exists_ofLE_of_chart_03I2`, `isEffectiveDescent_isomorphisms` (PrintedProp85); the descent of isomorphisms, hypothesis of 03I2, is proved there. On-points proof stays |
| Props 9.9, 9.10 over B | Direct gluing over affine objects (`glueV`, `sep_affine`); flat, f.p. unused | Chain of adjunctions | To redo |
| §9.3 over B | `IsQCoh` defined by Zariski sheaf + affine base change; `QCCover` for quasi-compact `V`; `IsQCohAt` on slices | Small fppf site of B | Author's call: `SB` has no topology |
| Cor 10.3, schemes | Printed torsor/cocycle frame exists (`Sec10PrintedMain`, `LiftTorsor`, `exists_invariant_lift`), `F` = lifts on `Spec A[N][P]`, H¹ = 0 by coefficient at 0. §11 for schemes also has `Sec11Printed*` | Sheaf p_*Hom(a*Ω, C), quasi-coherent, Prop 9.13 | Author's call: literal form needs Ω bridge and `IsQCoh` |
| Cor 10.3, spaces, and §11 over spaces | Integration of g⁻¹αg over `Spec avgRing`, glued by 07SY (`Sec11SpacesCore.exists_equivariant_of_lift`). Sole source of equivariant lifts for 11.1, 11.2, 11.5, 11.6, 11.7, 11.10 | Prop 10.1, Prop 9.13 | To redo: author's decision |
| Prop 11.5 | `Space.FormallyEtale` only; l.f.p. unused | Smooth + unramified | Keep as stronger |
| Prop 12.2(i), spaces | `f^N` as base change of `f` along vertex maps, generic points (`exists_generic_point_small`) | Cor 11.2, Fact 3.18, Tags 05VH, 06LU, 05W5 | Done: `prop122_i_printed` (PrintedProp122), stubs: Tag 05W5 and those of Cor 11.2 for spaces |
| Prop 12.2(ii) | Density of the orbit; (b), (c) dropped; `prop122_ii_printed` also has them | Atlas, Lem 3.26 | Keep with the printed form |
| Thm 12.4 | Reduction to X affine by `isPullback_repFace_open` fills an unprinted step | One sentence, no citation | Keep |
| Thm 12.4 | `smooth_faceZ` (Cor 11.10), formal smoothness of B0 -> B for projectivity | Cor 11.2, Tags 067U, 063M | To redo: blocked, no bridge from the conormal sheaf of 063M to `Ideal.Cotangent`, and 063M's full iff needs 666 unbuilt modules |
| Thm 12.4 | Sym over affine opens of S | Global sections s_n | Forced: fails on non-affine S |
| Cor 12.5 | Section from the irreducibles; N free when S nonempty; global trivial bundle (`cor125_global`) | "follows from the proof of Thm 12.4" | Keep: same `phi_injective`, stronger |
| Rem 11.11 | Explicit example | Mathoverflow reference | Keep: nothing printed |
| Rem A.7 | From `thmA1_closed` | Quotient X/G | Forced: no quotient in Lean |
| Rem 14.2 | Equality locus in X_i x_S Y_j, glued on charts, no quasi-compactness | No proof printed | Keep |
| Prop 14.4 | P tested on affine T | Same in the printed proof; Rem 14.2 says all schemes T | Keep |
| Prop 15.5 | `prop155_printed` follows Thm 8.3, Prop 5.1, Cor 11.6, with Tags 0AHE, 05W5 replaced by mono + locally surjective; `prop155` is a direct lift, alternative | Same | Keep `prop155` as remark |
| Ex 15.10 (ii) | On points: universal `h`, equivariance gives m in K | No proof printed | Keep |
| §16.4 (i), (ii) | Explicit `stagesEquiv`, `stageTopEquiv`: c = (c1, c2) acts by c1 · P(chi(c2)) | Props 3.31, 3.32 | (ii) done: `sec164_ii_printed` (PrintedSec164), X a scheme, as Prop 3.32 (ii). (i) to redo: needs Prop 3.31 for `<α> → M` on X^{<α>}, not formalized |
| Prop 16.15 (ii) | Y -> S from Cor 11.2 with target S (`smooth_rep`) | Attributed to Cor 11.10 | Forced: attribution gap |
| Thm A.1, case (i) | Printed route in `AppendixA3` (`thmA1_closed`, `thmA1_isFPR`); older `isFPR_of_etale` uses open stabilizer, irreducible fibres | Lems A.3–A.5, limits, F_n | Keep both; retire the older as remark |
| Thm A.1, case (ii) | X^G = X_0 pointwise at a stage, closedness by `presheaf_fnAll_ι`, no gluing of closed subspaces; FPR via `mem_fnFixed_of_etale`, no descent of U -> X | Limit argument to noetherian | To redo where valid |
| Lem A.4 | Mathlib nil-kernel finiteness lemma | Cofinality argument | To check |

Hypotheses found unnecessary, as remarks: `M` finitely generated and quasi-compactness in Cor 10.3 for `X'` affine; flatness and finite presentation in §9.3; `M` finitely generated in Prop 3.35 for `X` affine; the printed "N f.g. or X quasi-compact" of Thm 12.4, since the proof reduces to X affine first.

## Other papers in the tree

| Statement | Lean route | Printed route | Action |
|---|---|---|---|
| Self-actions, Prop 4.2 | Ideal inclusion only (`monIdeal_mono_left`, `monIdeal_eq_of_group`) | Equivariant morphism, Lemma 4.1 | Done: `prop42_printed`, `restrictHom` (PrintedSelfActions) |
| Self-actions, Ex (v) | Height `psi5`; `ex_v_inequality` unused | Inequality | To redo |
| Self-actions, Ex (vi) | Monoid-ideal lemma; `ex_vi_singleton` unused | Hom a singleton | To redo |
| X-products, Thm 4.1 | `thm41`, `toPoint_injective_gp` as remark; printed version `thm41Printed` | Conditions 1, 2 via [4], Prop 3.35 + Thm A.1 | Done: printed version added |
| X-products, Prop 4.3 (2), Prop 4.5 | Stronger forms as remarks; printed versions in `XProductsPrinted` | With (a), (b); induction on #A | Done: printed version added |
| X-products, Prop 3.2 | `XProductsF1Base` | Gluing | Done |
| X-products, Ex 4.4 | `XProductsExampleFunctor` | [2, Ex 1.6.4] + fibre product | Done |
| Self-actions, Prop 2.1 | On `T`-points for all schemes `T`, same two maps (`toPoint_vanish`, `vanishPt`) | On `R`-points | Keep |
| Self-actions, §2 | Proofs use `IsPure`; `isPurePrinted_iff`, `isPurePrinted_scheme` compare with printed `IsPurePrinted` | Minimality | Keep |
| Self-actions, Prop 3.1 | Both `N ↦ N ∩ E` (`prop31Equiv`) and `Π(a) = {[B⟩}`; printed reduction is `pureMagnets_scheme` | "We can assume S = Spec(ℤ)" | Keep |
| Self-actions, Prop 4.2 | Printed hypothesis `M^* ≠ 0` not stated: follows from the other | With it | Keep |
| Self-actions, Thm 4.6 | Ogus 1.3.3 proved (`sharp_add_left_cancel`) | Cited | Keep |
| Self-actions, added | `S ≠ ∅` in Prop 3.1, Lem 4.1 first assertion, Prop 4.5, Thm 4.6, Exs (i)-(v): false over `∅` (`pureMagnets_empty_base`) | Absent | Forced |
| X-products, §4 base | `thm41Printed`: S locally noetherian, finite type charts; `thm41PrintedZ` is `S = Spec ℤ` with literal hypotheses (Lfp, stubs) | `S = Spec ℤ` | Keep |
| X-products, Hom | `XNPt`: values on `T'`-points, natural, equivariant; no scheme `𝔸(𝒩)_T` | Hom of spaces | Keep |
| X-products, Prop 3.3 | `prop33T`: sheaf target, cover by `𝔸(N_α)_T` | Applied to a space, though stated for schemes over ℤ | Forced: printed application outside its statement |
| X-products, Thm 4.1 condition 1 | `toPoint_injective_cond1` applies Prop 3.35 and Thm A.1 as printed; `X^{D(M/Z)}` is a subfunctor by definition, closed immersion unused | Via A.1 | Keep |
| X-products, Prop 4.5 | Tags 042P, 042O applied on points | Quoted | Keep |
| X-products, Ex 4.4 | On all schemes; `{0}`, `{∞}` are `⊤_ Scheme` | Big fppf site | Keep |
| Double scalar, Prop 4.1 surjectivity | Tangent vector test (`mem_of_tangent`) | "(A²)^N = (A²)^L", unjustified | Forced |
| Double scalar, Prop 4.1 injectivity | `isPure_iff`, projector criterion `mem_image_iff` | Lem 4.2, charts, purity | Done: `prop41_injOn_printed` (PrintedDoubleScalar) |
| Double scalar, Lem 4.2 | `chart_attr_iff` reproved | Used by Prop 4.1, Fig 2 | Done for Prop 4.1: `chart_attr_iff_lem42`, `chart_eq_of_inter` use `lem42`. Fig 2 still through `chart_attr_iff` |
| Double scalar, Rem 5.1 (i) | `rem51_*` FinalRem51: `hW` carries the linear chart input as a hypothesis | One sentence | To redo: derive `hW` from coordinates |
| Double scalar, Prop 6.5 | `three_le_card_filter`, 8-case sign analysis | Opposite pairs | Done: `three_le_card_filter_printed`, `prop65_printed` (PrintedDoubleScalar) |
