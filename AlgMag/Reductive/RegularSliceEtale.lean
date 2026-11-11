/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.Localization.Away.Basic
import AlgMag.Reductive.IdentityComponentRoots

/-!
# Spreading bijectivity from a fibre to a principal open (C2(d), step (b))

`f : M →ₗ[B] N` between finite free `B`-modules of equal rank. If `f` becomes bijective after
base change along `ε : B → L` (`L` a field, e.g. the residue field at `(e, e, t₀)`), there is
`s : B` with `ε s ≠ 0` such that `f` becomes bijective over `B[1/s]`; `s` is a determinant of `f`.
Applied to `f = KaehlerDifferential.mapBaseChange k (compAlg π N) B`, this is the localization
step before `flat_of_mapBaseChange_bijective`.
-/

namespace AlgMag.Reductive

open Module TensorProduct Magnetism TauCeti

universe u

variable {B M N : Type*} [CommRing B] [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
  [Module.Free B M] [Module.Finite B M] [Module.Free B N] [Module.Finite B N]

/-- Base change of a linear map is bijective iff its determinant becomes a unit, for an
endomorphism of a finite free module. -/
lemma baseChange_bijective_iff_isUnit_det (A : Type*) [CommRing A] [Algebra B A]
    (g : M →ₗ[B] M) :
    Function.Bijective (g.baseChange A) ↔ IsUnit (algebraMap B A (LinearMap.det g)) := by
  rw [← LinearMap.det_baseChange, ← LinearMap.isUnit_iff_isUnit_det, Module.End.isUnit_iff]

omit [Module.Free B M] [Module.Finite B M] [Module.Free B N] [Module.Finite B N] in
/-- Composing with an equivalence does not change bijectivity after base change. -/
lemma baseChange_comp_equiv_bijective_iff (A : Type*) [CommRing A] [Algebra B A]
    (f : M →ₗ[B] N) (e : N ≃ₗ[B] M) :
    Function.Bijective ((e.toLinearMap ∘ₗ f).baseChange A) ↔
      Function.Bijective (f.baseChange A) := by
  have he : Function.Bijective (e.toLinearMap.baseChange A) := (e.baseChange B A N M).bijective
  rw [LinearMap.baseChange_comp, LinearMap.coe_comp]
  exact ⟨fun hc => (Function.Bijective.of_comp_iff' he _).mp hc, fun hf => he.comp hf⟩

/-- **Spreading out.** -/
theorem exists_away_baseChange_bijective (f : M →ₗ[B] N) (h : finrank B M = finrank B N)
    [Nontrivial B] {L : Type*} [Field L] [Algebra B L]
    (hL : Function.Bijective (f.baseChange L)) :
    ∃ s : B, algebraMap B L s ≠ 0 ∧
      Function.Bijective (f.baseChange (Localization.Away s)) := by
  let e : N ≃ₗ[B] M := LinearEquiv.ofFinrankEq N M h.symm
  refine ⟨LinearMap.det (e.toLinearMap ∘ₗ f), ?_, ?_⟩
  · exact ((baseChange_bijective_iff_isUnit_det L _).mp
      ((baseChange_comp_equiv_bijective_iff L f e).mpr hL)).ne_zero
  · rw [← baseChange_comp_equiv_bijective_iff _ f e, baseChange_bijective_iff_isUnit_det]
    exact IsLocalization.Away.algebraMap_isUnit _

omit [Module.Finite B M] [Module.Finite B N] in
/-- Free modules whose base change to a field are isomorphic have equal rank. -/
lemma finrank_eq_of_baseChange_bijective (f : M →ₗ[B] N) [Nontrivial B] {L : Type*} [Field L]
    [Algebra B L] (hL : Function.Bijective (f.baseChange L)) :
    finrank B M = finrank B N := by
  rw [← Module.finrank_baseChange (R := L) (S := B) (M' := M),
    ← Module.finrank_baseChange (R := L) (S := B) (M' := N)]
  exact (LinearEquiv.ofBijective _ hL).finrank_eq

/-- **Spreading out**, equal rank derived from the fibre. -/
theorem exists_away_baseChange_bijective_of_fibre (f : M →ₗ[B] N) [Nontrivial B] {L : Type*}
    [Field L] [Algebra B L] (hL : Function.Bijective (f.baseChange L)) :
    ∃ s : B, algebraMap B L s ≠ 0 ∧
      Function.Bijective (f.baseChange (Localization.Away s)) :=
  exists_away_baseChange_bijective f (finrank_eq_of_baseChange_bijective f hL) hL

section Smooth

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X) [IsAlgClosed k] [Algebra.FiniteType k H]
  [Algebra.Smooth k H]

/-- `O(K) = O((G^N)°)` is smooth over `k` (this is `compAlg π N` of RegularSlice). -/
theorem smooth_compAlg (N : Magnet (Additive X)) :
    Algebra.Smooth k ((H ⧸ (magnetHopfIdeal π N).toIdeal) ⧸ (attrComp π N).toIdeal) :=
  haveI : Algebra.Smooth k (H ⧸ (magnetHopfIdeal π N).toIdeal) :=
    smooth_quotient_magnetHopfIdeal π N
  FiniteTypeCommHopfAlgCat.smooth_identityComponent
    (FiniteTypeCommHopfAlgCat.of (R := k) (H ⧸ (magnetHopfIdeal π N).toIdeal))

end Smooth

end AlgMag.Reductive
