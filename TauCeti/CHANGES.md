# Backport CHANGES (Tau Ceti d2083f0 -> Lean v4.34.0-rc2 / Mathlib 16edf57)

All files: mechanical conversion (drop `module`, `public/meta import` -> `import`, `public section` -> `section`, drop `public/private`/`@[expose]`). Headers and authorship untouched.

## FORCED statement changes (review)
- Order.CompactlyGenerated: `OrderIso.isCompactElement` and `OrderIso.isCompactElement_iff` hypotheses `[Preorder α] [Preorder β]` narrowed to `[PartialOrder α] [PartialOrder β]`. Forced: Mathlib 16edf57 defines `IsCompactElement` only for `PartialOrder` (1b1ccf4 generalizes to `Preorder`), so the original statement cannot be written. Conclusions unchanged.

## Compat (new files, not Tau Ceti code)
- TauCeti/Compat.lean: `TensorProduct.inductionOn` (1b1ccf4 name, no zero case) from `induction_on`, induction_eliminator.
- TauCeti/Compat/Convolution.lean: from Mathlib 1b1ccf4 RingTheory/{Coalgebra,Bialgebra}/Convolution.lean: `AlgHom.convPostcomp` (+_injective,_id,_comp, simps), `CoalgHom.convPrecomp` (+...), `CoalgHom.convPrecomp_comp_convPostcomp`, `BialgHom.convPrecomp_eq_convPostcomp`; general `LinearMap.algHom_comp_convOne` / `convOne_comp_coalgHom` renamed `_gen` (16edf57 has special cases under those names in HopfAlgebra/Quotient.lean).
- TauCeti/Compat/All.lean: umbrella importing every compat module; added as first import to every Tau Ceti file that failed or was not yet attempted (driver does it for new files).
- TauCeti/Compat/Subpath.lean: Path.Homotopic.subpath_trans_subpath, mk_subpath_trans_mk_subpath from 1b1ccf4 Topology/Subpath.lean.
- TauCeti/Compat/IsApply.lean: 16edf57 already has Mathlib/Data/FunLike/IsApply.lean (explicit alpha beta); adds the 1b1ccf4 instances IsOneApplyEqSelf/IsMulApplyEqComp for Module.End and IsZeroApply/IsAddApply/IsSMulApply for Derivation (rfl).
- TauCeti/Compat/Misc.lean: aliases LinearMap.baseChange_eq_lTensor, Abelianization.commutator_le_ker, IsConcreteLE.le_iff (:= SetLike.le_def), AlgEquiv.coe_toRingEquiv, Finsupp.mapDomain_apply_of_injective; copies of IsUnit.map_ringInverse, map_ringInverse.
- TauCeti/Compat/LinearAlgebra/Unimodular.lean: copy of Mathlib 1b1ccf4 LinearAlgebra/Unimodular.lean + Module.Basis.span_repr_one_eq_top (from 1b1ccf4 RingTheory/Flat/FaithfullyFlat/Basic.lean).
- Mathlib.LinearAlgebra.TensorProduct.Lift (1b1ccf4) = content already in 16edf57 Mathlib.RingTheory.TensorProduct.Basic: import remapped (no copy).
- TauCeti/Compat/OfClass.lean: also aliases CoalgHom.toLinearMap_eq_ofClass, coe_linearMapOfClass, linearMapOfClass_injective (1b1ccf4 renames of toLinearMap_eq_coe, coe_toLinearMap, coe_linearMap_injective).
- TauCeti/Compat/OfClass.lean: `AlgHom.ofClass` := `AlgHomClass.toAlgHom`, `CoalgHom.ofClass` := `CoalgHomClass.toCoalgHom` (abbrev), alias `AlgHomClass.linearMapOfClass_ofClass` := `AlgHomClass.toLinearMap_toAlgHom`.

## Per file
- Polynomial.Laurent.Basic: `MonoidHom.coe_ofClass` -> `MonoidHom.coe_coe`.
- (12 files, see compatusers.txt): + `import TauCeti.Compat`.
- Algebra.Coalgebra.Convolution: + imports TauCeti.Compat, TauCeti.Compat.Convolution.
- Algebra.HopfAlgebra.Basic: + imports TauCeti.Compat.OfClass, TauCeti.Compat.Convolution.
- Algebra.Coalgebra.Subcoalgebra.Basic: `.ofSetLike (Subcoalgebra R C)` -> `.ofSetLike (Subcoalgebra R C) C` (16edf57 signature takes the element type explicitly).
- Algebra.AlgebraicGroup.Dynamic.Points: unchanged (name supplied by Compat.Misc).
- Algebra.HopfAlgebra.HopfIdeal.Basic, Algebra.Coalgebra.Subcomodule.Basic: `.ofSetLike T` -> `.ofSetLike T E` (element type explicit in 16edf57).
- Algebra.Coalgebra.Comodule.Hom: `IsZeroApply (Hom R C M N)` / `IsAddApply (Hom R C M N)` -> add explicit `M N` (16edf57 class signature).
- LinearAlgebra.End.ScalarExtension, LinearAlgebra.Unimodular: import remaps (see Compat).
- Order.CompactlyGenerated: OrderIso.isCompactElement(_iff): `[Preorder α] [Preorder β]` -> `[PartialOrder α] [PartialOrder β]`. RESTRICTION FORCED: 16edf57 defines IsCompactElement only for PartialOrder (1b1ccf4 generalized to Preorder); same statement on partial orders.
- LinearAlgebra.Dimension.DirectSum (finsum_finrank_eq_finrank_of_isInternal): proof repair, `have := hV.fintype` -> `have : Fintype {i // V i ≠ ⊥} := hV.fintype` and `have : Nontrivial R := nontrivial_of_invariantBasisNumber R`.
- Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic (CommHopfAlgCat.kerOfSurjective_quotientMapOfLe): the surjectivity proof argument `(quotientMapOfLe_surjective H hIJ)` inside the statement (a Prop, proof-irrelevant) replaced by a direct proof; the original triggers a whnf timeout (even at 1e6 heartbeats) on 16edf57.
- Algebra.Coalgebra.Comodule.Hom: instance fields given explicitly (`zero_apply _ := rfl`, `add_apply _ _ _ := rfl`; 16edf57 classes have no rfl default).
- Order.CompactlyGenerated: `hc.exists_finset_of_le_iSup` -> `CompleteLattice.IsCompactElement.exists_finset_of_le_iSup _ hc` (16edf57 namespace).
- Algebra.AlgebraicGroup.Tangent.Adjoint: `Subgroup.Normal.conj_mem p.val ...` -> `(inferInstance : (tangentKer R H B).Normal).conj_mem p.val ...` (in 16edf57 the Normal proof is an explicit argument).
- LinearAlgebra.Determinant.Basic (IsAlt.compl₁₂_self_eq_det_smul): add `AlternatingMap.smul_apply` to the simp set (16edf57 lacks the IsSMulApply instance for AlternatingMap).
- TauCeti/Compat/Polynomial.lean (compat): Ring versions of le_rootMultiplicity_iff, rootMultiplicity_le_iff, rootMultiplicity_eq_natTrailingDegree' (1b1ccf4 Algebra/Polynomial/Div.lean; CommRing-only in 16edf57), suffix `_ring`.
- Algebra.Polynomial.Reverse (rootMultiplicity_reflect_zero): `rw [rootMultiplicity_eq_natTrailingDegree']` -> `..._ring` (statement unchanged, still [Ring R]).
- Topology.Homotopy.Path: unchanged (lemmas supplied by Compat.Subpath).
- Algebra.AlgebraicGroup.Dynamic.Parabolic: unchanged (name supplied by Compat.Misc).
- Algebra.Coalgebra.Comodule.Cat: homIsZeroApply/homIsAddApply: explicit `M N` arguments (16edf57 class signature).
- LinearAlgebra.Dimension.DirectSum: explicit (R := R) (M := M) (A := V) in the final rw (stuck instance problem on 16edf57).
- Algebra.AlgebraicGroup.Tangent.Naturality: `exact ...commutes _` after `congr 1` -> `all_goals exact ...` (congr 1 already closes the goal on 16edf57).
- Topology.ConnectedComponents (connectedComponentIn_compl_Icc_eq_Iio): `mem_connectedComponentIn (F := (Icc a b)ᶜ) ...` (elaboration hint).

## Session 3 (2026-11-08)
- Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic: (kerOfSurjective_quotientMapOfLe) `rw [HopfIdeal.mem_kerOfSurjective, ...]` -> `refine (HopfIdeal.mem_kerOfSurjective _ _).trans ?_` then the remaining rw (target not type-correct at instances transparency); (ker_quotientMapOfLe) `simpa only [HopfIdeal.kerOfSurjective_eq_ker] using ...` -> `exact (HopfIdeal.kerOfSurjective_eq_ker _ _).symm.trans (...)`. Proofs only.
- LinearAlgebra.Dimension.DirectSum: final `exact Fintype.sum_equiv ... _ _ fun _ ↦ rfl` -> `convert Fintype.sum_equiv ... (fun i ↦ finrank R (V i)) (fun i ↦ finrank R (V i)) fun _ ↦ rfl` (two Fintype instances on the index subtype). Proof only.
- New compat TauCeti/Compat/Contraction.lean: copy of 1b1ccf4 `toLinearMap_dualTensorHomEquiv`, `dualTensorHomEquiv_tmul`, `dualTensorHomEquiv_symm_dualTensorHom`, `dualTensorHom_dualTensorHomEquiv_symm` (Mathlib/LinearAlgebra/Contraction.lean, Apache-2.0, authors kept). Imported by Tangent.Cotangent and Comodule.LinearHom (import line added only).
- Algebra.Coalgebra.Comodule.RestrictScalars: `letI := Module.compHom X (algebraMap R A)` / `letI := IsScalarTower.of_compHom R A X` in the ComoduleCat section given explicit types `Module R X.toSemimoduleCat` / `IsScalarTower R A X.toSemimoduleCat` (let _ -> letI) so instance search sees them through the carrier coercion. Definitions unchanged in meaning.
- New compat TauCeti/Compat/Aut.lean: 1b1ccf4 has `structure Aut X where of :: asIso : X ≅ X`; 16edf57 has `def Aut X := X ≅ X`. Provides `Aut.of`, `Aut.asIso` as identity abbrevs and rfl lemmas `one_asIso`, `inv_asIso`, `mul_asIso`, `asIso_of`, `of_asIso`. Statements using `.asIso` keep their meaning (the projection is the identity).
- Algebra.Coalgebra.Comodule.Finite.ScalarExtension.Basic: imports Compat.Aut; in two proofs `apply Aut.ext; apply Iso.ext` -> `apply Aut.ext` (16edf57 Aut.ext already takes the hom equality).
- AlgebraicGroup.DiagonalizableGroup.Normalizer.Character (normalizerCharacterHom_of_comp_eq): proof term `normalizerCharacterHom_unique π hπ _ w hg` -> explicit point `⟨g, mem_normalizerPoints_of_comp_eq π hπ g w hg⟩` (whnf timeout when unifying `_`). Proof only.
- AlgebraicGroup.Tangent.Representation (pointInCounitAlgebra_comp): `erw [BialgHom.mapDomain_apply]` already closes the goal on 16edf57; the following 5 tactic lines removed. Proof only.
- New compat TauCeti/Compat/IsApplyEquiv.lean: 1b1ccf4 `IsOneApplyEqSelf`/`IsMulApplyEqComp` instances for `M ≃ₗ[R] M` (Mathlib/Algebra/Module/Equiv/Basic.lean), rfl fields. Imported by AlgebraicGroup.Hopf.Translation.
- AlgebraicGroup.HopfIdeal.BaseChange: `tensorSquareBaseChangeHom H` -> `tensorSquareBaseChangeHom (K := K) H` at two uses (lines 419, 477; K not inferred). Elaboration hint only.
- Coalgebra.Comodule.Finite.ScalarExtension.Monoidal (oplax_associativity): `erw [SemimoduleCat.comp_apply ×4]` -> `simp only [ConcreteCategory.comp_apply]`. Proof only.
- AlgebraicGroup.Tangent.Equivariance: after `congr 1` the goal is already closed on 16edf57; trailing `simpa ... using (pointInCounitAlgebra_comp ...).symm` removed. Proof only.
- New compat TauCeti/Compat/IsApplyLie.lean: 1b1ccf4 IsOneApplyEqSelf instances for LieHom/LieEquiv/LieModuleHom/LieModuleEquiv endomorphisms (Mathlib/Algebra/Lie/Basic.lean), rfl fields. Imported by Tangent.Lie.Adjoint.Cotangent.
- AlgebraicGroup.Dynamic.Levi.Centralizer: final `exact commute_pointsHom_of_mem_levi l (levi_le_comap φ hg) _` -> explicit `(Subgroup.mem_comap.mp (levi_le_comap φ hg)) (laurentEvalEquiv.symm (t.ofConv.comp e.toAlgEquiv.toAlgHom))` (isDefEq timeout). Proof only.
- AlgebraicGroup.Representation.ScalarExtension: imports Compat.Aut; `apply Aut.ext; apply Iso.ext` -> `apply Aut.ext` (twice). Proof only.
- AlgebraicGroup.Unipotent.Basic: PRUNED. Import Representation.JordanDecomposition.Basic replaced by Representation.UnipotentPoint.Basic; removed the two Jordan-part theorems (..._iff_forall_unipotentPart_eq_self, ..._iff_forall_semisimplePart_eq_one), unused by the targets. Cuts the Tannaka chain (PointFaithful failure + 10 blocked modules) out of the closure.

## Second batch (2026-11-08): smoothness of P/U/L, connectedness of U, Lie-algebra criterion
24 new modules (closure of Dynamic.Smooth, Dynamic.Unipotent.Connected, HopfIdeal.Smooth.LieAlgebra over the first batch), mechanical conversion as above. Proof-only fixes:
- Dynamic.LeviDecomposition.Naturality, mapLevi_limitToLevi: trailing steps wrapped in `all_goals (congr 1 <;> ...)` (`congr 1` closes the goal in 16edf57).
- Algebra.MonoidAlgebra.Basic: dropped instance `instHasUniqueDiv` (class `HasUniqueDiv` absent from 16edf57; unused downstream).
- Dynamic.Smooth: `Polynomial.toRingHom_mapAlgHom` -> `Polynomial.mapAlgHom_coe_ringHom`.
- CategoryTheory.Comma.Over: `simp` given `pullback.lift_fst/_snd(_assoc)` explicitly.

## Session T1-dyn (2026-11-10)
- Ported for AlgMag/Reductive/TorusConjDyn.lean (not in the Borel port list): RepresentationTheory.ToMultiplicative, Algebra.Coalgebra.Comodule.MonoidAlgebra.OneCocycle, Algebra.AlgebraicGroup.Representation.PointsAction.Semidirect, Algebra.AlgebraicGroup.DiagonalizableGroup.SemidirectProduct. Mechanical conversion only (same conv as the Borel driver); no statement or proof change. All four build.

## Third batch (2026-11-10): Borel theory from Tau Ceti 7ca783d4 (v4.36)
409 new modules (scratchpad list new-list.txt + Dynamic.Reductive closure), mechanical conversion as above, plus: `Nat.strong_induction_on` alternative `ind` -> `h`; `Subgroup.derivedSeries*` -> root `derivedSeries*`; `apply Aut.ext; apply Iso.ext` -> `apply Aut.ext`, `Aut.ext h` -> `Aut.ext (congrArg Iso.hom h)`; import remaps Mathlib.GroupTheory.QuotientGroup.Simple -> TauCeti.Compat.Solvable, Mathlib.Algebra.GroupWithZero.Action.Regular -> Action.Defs. The 246 existing copies are untouched.
New compat (imported only by the new files that need them, not via Compat.All):
- Compat/Misc2.lean: aliases MonoidHom/LinearMap.coe_ofClass, MulEquiv.toMonoidHom_{trans,comp_toMonoidHom_symm,symm_comp_toMonoidHom}; `abbrev HasUniqueRoots M := IsMulTorsionFree M` (16edf57 IsMulTorsionFree is the 1b1ccf4 HasUniqueRoots definition), IsMulTorsionFree.hasUniqueRoots.
- Compat/Solvable.lean: Group.isSimpleGroup_of_isCoatom (statement from 1b1ccf4, proof rewritten).
- Compat/Misc3.lean: Ideal.height_span_le_card_of_span_ne_top, Submodule.{eq_bot,le}_of_le_smul_of_le_jacobson, IsArtinianRing.exists_notMem_forall_mem_of_ne, QuasiFinite fibre IsArtinianRing instance, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite (1b1ccf4 copies); aliases IsLocalRing.local_hom_tfae, Scheme.Hom.closedPoints_subset_preimage_closedPoints, finrank_eq_one_iff_of_ne_zero', IsConcreteLE.{exists_of_lt,lt_iff_le_and_exists,not_le_iff_exists}, Ideal.IsIntegral.under_lt_under, Ideal.isMaximal_under_of_isIntegral_of_isMaximal; new helper Algebra.TensorProduct.map_rTensor_eq_rTensor_lTensor (proved).
- Compat/Aut.lean (from the earlier port) + End.mul_asHom (rfl).
- Algebra/AlgebraicGroup/Representation/UnipotentPoint/Upstream.lean: upstream-added theorem IsUnipotentPoint.isNilpotent_pointsRepresentation_sub_one, verbatim (kept out of the old copy so its dependents are not rebuilt).
RENAME (requested, clash with StacksFrontier.Topology.Dimension.Krull): Topology.KrullDimension.Local `Topology.IsOpenEmbedding.topologicalKrullDimAt_eq` -> `topologicalKrullDimAt_eq'` (statement unchanged; one use in the same file updated).
Proof-only repairs (statements unchanged): GroupTheory.FiniteAbelian.TorsionFree, AlgebraicGeometry.Group.Smooth, GeneralLinear.Scheme, Representation.Differential, TensorProduct.Hom, End.Basic, Topology.KrullDimension.Irreducible, ProjectiveSpectrum.Basic, NormalizerQuotient.Basic, Ideal.Cotangent.Localization, Representation.Faithful.Basic, Borel.Conjugation, Parabolic.Basic, Topology.KrullDimension.ClosedCover (+ import Mathlib.Topology.NoetherianSpace), Unramified.Normal, ProjectiveSpectrum.LinearAction, Comodule.Finite.ScalarExtension.Monoidal, Tannaka.Monoidal, Tannaka.Equivalence, LinearAlgebra.End.Aeval. Definition change: TangentSpace.Affine — `(equivQuotMaximalIdeal ..).restrictScalars k` (RingEquiv.restrictScalars absent in 16edf57) replaced by `AlgEquiv.ofRingEquiv` of the same ring equivalence (same underlying map). See C:\Users\Arnaud\Desktop\equivalence-reductive\port-log.md.

- (hdim agent, 2026-11-10) RENAMED AlgebraicGeometry.formallyUnramified_stalkMap_iff -> formallyUnramified_stalkMap_iff' in TauCeti/AlgebraicGeometry/Morphisms/StalkMap.lean (+3 uses): clashes with StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Basic.
