# Dilatations of algebraic spaces in algmag-stacks: plan (2026-11-08)

Read-only planning note. Nothing compiled. Approach fixed by the author:
- RING LEVEL: take the JAR ring layer as it is (Mayeux-Zhang, "Formalizing Multi-graded
  Brenner-Schroer Proj Schemes and Dilatations of Rings in Lean4", J. Autom. Reasoning (2026),
  doi 10.1007/s10817-026-09764-x; code github ProjConstruction/Proj, local copy
  C:\Users\Arnaud\Desktop\Proj, Lean v4.16), adapted to v4.34 only as needed; cite JAR as source.
- EVERYTHING ABOVE RINGS (schemes, spaces, gluing, descent, universal property, multi-centre and
  tower globally, blow-up comparison, Prop 13.1): new native work, directly for algebraic spaces on
  the big fppf site (schemes = representable case). Old SchDil (rndmx/SchDil v1.0, Lean v4.22) is
  only a source of proof ideas; no file is ported.
- Magnet language, no artificial definitions, restrict only with a counterexample.

## 0. Key finding: much of the minimum path already exists in the repo

- `AlgMag.DilSp.exists_spDilatation` (AlgMag/Sec13Spaces.lean:873, axioms printed at :1589):
  for `I : S.IdealSheafData` with `LocPrincipal I`, `X` an algebraic space, `j : Y ⟶ X` a closed
  immersion of sheaves with `Y` lying over `I`, there is an algebraic space `F`, `b : F ⟶ X`
  affine, with `IsSpDil I j b`. Proof: dilatation of an étale atlas (`exists_presentation`, :593)
  + étale descent of affine morphisms (`isEffectiveDescentAlongSurjectiveEtale_isAffineHom`) +
  `isSpDil_of_site` (:827).
- `IsSpDil` (:320) = universal property among `S'`-regular sheaves; `IsSpDil.exists_iso` (:331).
- Schemes: `IsDilOn`/`IsDilatation` (Sec13General.lean:270-280), `chart_isDilOn` (:634) on affine
  charts, `isPullback_of_isDilOn` (:654) (open restriction), `exists_lift_of_cover` (:283).
  The affine chart algebra there is built ad hoc in Sec13General (`chartA`, `chartJ`, `rho`).
- `prop13_1_spaces` (:1571) takes `hB' : IsSpDil I (jN ..) b'` for a model `B'`; the actual
  content is `attractor_isSpDil` (:1416), which needs no model.

So "existence + universal property for spaces" is DONE for the AM §13 setting (one centre `Y`,
divisor `D` = pullback of a locally principal `S' ⊂ S`). Removing the model input from Prop 13.1
is a short package (WP1). The genuinely new theory is: general centres (D a Cartier divisor on X
itself, not pulled back from S), multi-centres, flat base change, tower formula, blow-up
comparison, all on spaces.

## 1. Inventory of the old material (proof-idea source)

Paper statements: SchDil docstrings carry almost no numbered references; only section labels
`Prop224` (MulticenterTower.lean, "Prop 2.24"), `Prop52` (MulticenterShift.lean), file names
`Cor240`, `Fact51`, `Remark37`, `SchemeLemma44`, `SchemeProp317`, `SchemeProp52`,
`PolyptychAssumption31`. These refer to Mayeux's multi-centred dilatations paper; numbers NOT
verified against the published version here (rule: resolve the journal version before briefing).

| Group | JAR / SchDil content |
|---|---|
| Ring: definition | JAR `Multicenter A` (index, ideal, elem), `LargeIdeal i = I_i + (a_i)`, `A[F] := Quotient F.setoid` of `PreDil` (fractions m / a^ν), `CommRing`, `Algebra A A[F]`, `frac`, `nonzerodiv_image`, `image_elem_LargeIdeal_equal` (Multicenter.lean 17-480) |
| Ring: universal property | JAR `desc` (:584), `dsc_spec`, `lemma_exists_unique_morphism` (:662), `reciprocal_for_univ` (:690) |
| Ring: Rees algebra | JAR ReesAlgebra.lean (391 l., multigraded Rees algebra, grading, decompose) |
| Ring: commented out in the local JAR copy (lines 753-1136, 26 `sorry` inside comments) | functoriality `functo_dila_alg`, localisation embedding `dil_to_localise_*`, `monopoly`, `union_center`, `potion_Rees_dilatation_iso`, flat base change. NOT part of the compiled JAR layer. |
| Ring: beyond JAR, in SchDil (26 pure-ring files, ~4.5k l.) | flat base change `A[F]⊗B ≅ B[F_B]` (DilatationFlatBaseChange, ring half), Prop 2.24 tower `A[F] ≅ (A[F_K])[F_{K^c}]` (MulticenterTower `prop_2_24`), Prop 5.2 shift (MulticenterShift), quotient/strict transform (MulticenterQuotient), iterate (MulticenterIterate), monopoly (MulticenterMonopoly), exceptional ideal (MulticenterExceptional), single divisor (MulticenterSingleDivisor), span equivalence, Cor 2.40, Fact 5.1, polyptych kernel/panel ring files (PolyptychDatum, Expand, Kernel, KernelFormula, Panel, Restricted), Rees covering/charts (ReesCovering, ReesMu, ChartBar, ChartCover, PartitionUnity, ProjOverlap, ProjGlueCompat, HomogDecomp, IdealLocality) |
| Schemes/gluing | `PreClos`/`Clos` (closed subschemes by affine cover + quotient), `PreMultiCenter`, `GlobalDilatation.dilatation` = glue of `Spec A[F]` charts (GlueData), `dilaUnique` |
| Universal property | UniversalProperty.lean (830 l.): local uniqueness, refinement covers |
| Flat base change | BaseChange.lean `flatBaseChangeIso`, `baseChangeHom_flat` |
| Multi-centre | MultiCenter*, MonoCentered `universal_property`, Functoriality, Reindex |
| Tower / iterated | Tower.lean (`tower`, `homToBase`, `tower_isCars`), IteratedMultiple, IteratedSchemeMulti*, SchemeLemma44 (1684 l., iterated vs single), SchemeProp52, SchemeFact51 |
| Blow-up / Proj | DilToBlowup `toBlowup`, `toProjBlowup` (dilatation → blow-up of D), ProjComparison/ProjIso*/ProjMathlibIso (Proj of Rees vs Mathlib Proj) |
| Polyptych / panels | Polyptych*, RestrictedPanel*, PanelDivisorSum, PolyptychPaperForm (`Assumption31`, `panelizationIsoPaper`) |

Verdict on "does SchDil go beyond JAR at ring level": YES. The compiled JAR layer stops at the
definition, ring structure, universal property (+ Rees algebra). Flat base change, functoriality,
Prop 2.24 tower, shift, quotient, monopoly, polyptych kernels are SchDil-only (they import
`Project.Dilatation.*` from rndmx/MULTI-PROJ-BLOW rev 5a3c950, whose relation to the JAR tag must
be checked: it may be a later revision with the commented block completed).

## 2. Stacks correspondence (Stacks @ 012108f)

| Need | Stacks provides | Use |
|---|---|---|
| single-centre affine dilatation | `StacksFrontier.AlgebraicGeometry.AffineBlowupLift.Ring`: `affineBlowupAlgebra I a Rₐ` = R[I/a] inside R_a; `AffineBlowupLift.lift`, `.ext`, `.uniqueAlgHom` (universal property: a nzd in B, I·B = a·B), Tag 0806. Closure: 8 modules. | Identify with JAR `A[F]` for `F` one-index with ideal `I`, elem `a` (note JAR condition uses `LargeIdeal = I+(a)`; same since a ∈ I·B automatically). Prove `A[F] ≃ₐ[A] affineBlowupAlgebra I' a` by the two universal properties. |
| chart of blow-up | `AffineBlowupLift.Chart` (closure 37), `Blowup/AffineChart`, `AffineBlowUpIso`, `affineBlowupStandardOpenIso` | blow-up comparison WP |
| blow-up of schemes | `Blowup/Basic`, `CartierCentre` (closure 1238), `ClassifyingMorphism` | universal property of blow-up for comparison; heavy, only in WP7 |
| étale descent, atlases, quotients | already imported by Sec13Spaces: `Spaces/Presentation`, `EtaleDescent`, `AtlasMorphismDescent`, `QuotientSheafAlgebraic`, `Descent/AffineHomEffectiveDescent` (closure of EtaleDescent: 38) | reuse as in `exists_spDilatation` |
| flat base change | Mathlib `Module.Flat` + `Algebra.TensorProduct`; Stacks flat descent in `Descent/*` | ring identity from SchDil idea, global by descent |

Also needed: `@[stacks]` search for effective Cartier divisors on spaces (`git grep -n "@\[stacks 083"`
etc.) before defining "locally principal closed subspace"; do not define a new notion if one exists.

## 3. Design for algebraic spaces

Setting: `B : BigFppfSite`, `S`, `C = BigFppfOver B S hS`, `X : Cᵒᵖ ⥤ Type u` algebraic space.

Definition (general centre, matching IsSpDil): a multi-centre on `X` is a family `(Y_i ⊂ D_i ⊂ X)_{i∈ι}`
of closed subspaces with `D_i` locally principal (étale-locally cut by one equation). `T → X` is
`D`-regular if each pullback `D_i ×_X T` is an effective Cartier divisor in `T` (étale-locally
a nonzerodivisor), and factors if `Y_i ×_X T = D_i ×_X T`. `IsMultiDil (Y,D) b` := `b : F ⟶ X`,
`F` sheaf, `F` regular, factors, and the lift/uniqueness clauses among regular sheaves, copied
from `IsSpDil`. The AM §13 case `D = S' ×_S X` is a theorem (`IsSpDil ↔ IsMultiDil` for one
centre with `D` pulled back), not a second definition.

Construction: on an affine étale chart `Spec A → X`, `Spec A[F]` with JAR `A[F]`; universal
property of `Spec A[F]` among regular schemes from JAR `desc`/uniqueness; flat base change
`A[F] ⊗_A A' ≅ A'[F_{A'}]` for `A → A'` flat (ring lemma, idea in SchDil
DilatationFlatBaseChange) gives the descent datum on `R = U ×_X U`; effective by
`isEffectiveDescentAlongSurjectiveEtale_isAffineHom`; then `isSpDil_of_site` pattern. This
generalises `exists_presentation` (it replaces the ad-hoc `chartA/chartJ` algebra).

Properties: universal property (by construction), uniqueness, functoriality, flat base change
(`X' → X` flat: `Bl X ×_X X' ≅ Bl X'` by universal property + flatness preserves regularity,
`IsRegular.of_flat` already exists), tower formula (`Bl_{F} X ≅ Bl_{F_{K^c}} Bl_{F_K} X`, by
universal properties alone once both sides exist; ring Prop 2.24 not even needed globally),
multi-centre reductions (monopoly, reindexing) via universal property.

Plug into Prop 13.1: apply `exists_spDilatation` to `ZX` with centre `jN hs rX rY` to produce
`B'`, `b'`; feed into `prop13_1_spaces`. Required facts: (a) `ZX` algebraic space, (b) `ZY` sheaf,
(c) `jN` closed immersion, (d) `ZY` lies over `I`. (b) from `isSheaf_attractor_of_isAlgebraicSpace`
(AlgMag/AlgebraicSpace.lean:31) if `Y` is a space; (d) from `Y` lying over `I` and
`ZY → Y`; (a),(c) need the representability theorems of the paper (X^N algebraic space and
Y^N → X^N closed for Y closed and stable). Check whether the printed Prop 13.1 assumes them; if
X^N is only "represented by a sheaf" in the statement, (a) is an extra hypothesis to report, or must
come from the repo's representability results (ChartEffectiveFinal.lean:383/408).

## 4. Work packages (minimum path first)

MINIMUM PATH = WP1 (existence + universal property for spaces already exist; WP1 removes model B').

- WP1 Prop 13.1 without model (≈150-300 l., deps: Sec13Spaces, AlgebraicSpace.lean, attractor
  representability). New file `AlgMag/Prop131NoModel.lean`: lemmas (a)-(d) above, then
  `prop13_1_spaces'` with conclusion `∃ B' b', IsAlgebraicSpace B' ∧ IsSpDil .. b' ∧ ∃ e : ZB ≅ B', ..`.
  Risk: (c) closed-immersion stability of attractors may be the real work (~300-600 l. more) if not
  already in the repo; grep `IsClosedImmersion` near attractor files first.
- WP2 JAR ring layer on v4.34 (≈1.2-1.5k l.: Family 56, Multicenter 1-752, ReesAlgebra 391,
  lemma 27; drop the commented tail). New dir `AlgMag/DilRing/`. Deps: Mathlib only.
  Expected breakage: `Ideal`/`Submodule` power and `Finsupp` lemma renames, `DirectSum` API,
  `Quotient.mk` vs `⟦⟧` changes, `nonZeroDivisors` lemma names (`mem_nonZeroDivisors_iff` →
  `mem_nonZeroDivisors_iff_right`/`_left` split), `RingHom.Flat`, `AlgHom.commutes`/`ext`
  simp-set changes, `instance : CommRing` field set (npow/zsmul defaults), new `module` system
  (`public import`/`@[expose]`) only if the file joins a Stacks-style module; here plain AlgMag files.
  Proof style is term-heavy, expect 20-40% of proofs to need touching. Cite JAR in the module doc.
- WP3 Identification with Stacks (≈150-250 l., deps WP2 + AffineBlowupLift.Ring, closure 8):
  `A[F] ≃ₐ[A] affineBlowupAlgebra` for one index; then rewrite Sec13General's chart through it
  (optional).
- WP4 Ring flat base change + localisation (≈300-500 l., deps WP2): `A[F] ⊗ A' ≅ A'[F_{A'}]` for
  flat `A'`, and `A[F]_g ≅ A_g[F]` (open immersions). Ideas: SchDil DilatationFlatBaseChange,
  JAR commented block. These are new ring results beyond JAR (written natively).
- WP5 General multi-centre dilatation of spaces (≈1.5-2.5k l., deps WP2, WP4, Sec13Spaces
  descent pattern): `IsMultiDil`, chart regularity, `exists_multiDil`, uniqueness,
  `IsSpDil ↔ IsMultiDil` in the §13 case.
- WP6 Flat base change + tower + monopoly on spaces (≈600-1000 l., deps WP5): all via universal
  property. Tower formula statement = SchDil Tower.lean / ring Prop 2.24.
- WP7 Comparison with blow-ups (≈800-1500 l., deps WP5 + Stacks Blowup/CartierCentre, closure 1238):
  dilatation → blow-up of D (single centre: open in Bl_{Y+D}), Rees/Proj comparison (JAR Proj
  part). Schemes first; spaces only if Stacks blow-up of spaces exists (search tag 085P area).
- WP8 Polyptych/panels (≈2-4k l., deps WP5, WP6): only if the author wants it in AM; ring part from
  SchDil ideas.

## 5. Risks

- Version drift v4.16 (JAR) → v4.34: 18 minor versions; Mathlib algebra renames are the main cost
  (WP2). No Mathlib compilation allowed: everything must use the repo's existing Mathlib oleans.
- Closure sizes (scripts/closure.py on Stacks HEAD): AffineBlowupLift.Ring 8 modules,
  AffineBlowupLift.Chart 37, Spaces.EtaleDescent 38 (already in), Blowup.CartierCentre 1238
  (heavy; confine to WP7 and add to the sparse checkout only then).
- Universe: SchDil works with `Scheme.{u+1}` and `Type (u+1)` rings; repo uses `Scheme.{u}` in a
  size-bounded site (`B.Contains`); size lemmas (`Scheme.size_lt_of_isOpenImmersion`, `contains_restr`)
  needed for every new chart (Spec A[F] is affine over Spec A, so bounded).
- Prop 13.1 hypothesis (a)/(c): if the printed statement does not give X^N algebraic space, WP1
  either imports a representability theorem or reports the added hypothesis.
- Paper numbering of SchDil references unverified; resolve the published multi-centred
  dilatations paper before writing docstrings.
