/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The fibre of `mapBaseChange` at a point is dual to the tangent map (C2(d), part (a))

For `k → A → B` and a field `L` with `B → L` (a point of `Spec B`), the fibre
`L ⊗_B (B ⊗_A Ω_A) → L ⊗_B Ω_B` of `KaehlerDifferential.mapBaseChange k A B` is bijective iff
the tangent map `Der_k(B, L) → Der_k(A, L)`, `D ↦ D ∘ (A → B)`, is bijective
(`bijective_fibre_mapBaseChange_iff`). For the slice `A = O(K)`, `B = sliceSource`, at
`(e, e, t₀)` the tangent map is the differential of `μ` (`sliceTangentMap`).
-/

namespace AlgMag.Reductive

open TensorProduct KaehlerDifferential

variable (k A B L : Type*) [CommRing k] [CommRing A] [CommRing B] [Field L]
  [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
  [Algebra B L] [Algebra A L] [IsScalarTower A B L] [Algebra k L] [IsScalarTower k B L]
  [IsScalarTower k A L]

/-- Tangent map at the point `B → L`: pull a derivation back along `A → B`. -/
def tangentPullback (D : Derivation k B L) : Derivation k A L := D.compAlgebraMap A

/-- `Dual_L (L ⊗_B Ω_B) ≃ Der_k(B, L)`. -/
noncomputable def dualFibreEquivDer : Module.Dual L (L ⊗[B] Ω[B⁄k]) ≃ Derivation k B L :=
  ((LinearMap.liftBaseChangeEquiv L).symm.toEquiv).trans
    (KaehlerDifferential.linearMapEquivDerivation k B).toEquiv

/-- `Dual_L (L ⊗_B (B ⊗_A Ω_A)) ≃ Der_k(A, L)`. -/
noncomputable def dualFibreEquivDer' :
    Module.Dual L (L ⊗[B] (B ⊗[A] Ω[A⁄k])) ≃ Derivation k A L :=
  ((LinearMap.liftBaseChangeEquiv L).symm.toEquiv).trans
    (((LinearMap.liftBaseChangeEquiv B).symm.toEquiv).trans
      (KaehlerDifferential.linearMapEquivDerivation k A).toEquiv)

lemma dualFibreEquivDer'_dualMap (g : Module.Dual L (L ⊗[B] Ω[B⁄k])) :
    dualFibreEquivDer' k A B L (((mapBaseChange k A B).baseChange L).dualMap g) =
      tangentPullback k A B L (dualFibreEquivDer k B L g) := by
  ext a
  change g ((mapBaseChange k A B).baseChange L (1 ⊗ₜ (1 ⊗ₜ D k A a))) =
    g (1 ⊗ₜ D k B (algebraMap A B a))
  rw [LinearMap.baseChange_tmul, mapBaseChange_tmul, one_smul, map_D]

/-- **Fibre of `mapBaseChange` vs tangent map.** -/
theorem bijective_fibre_mapBaseChange_iff :
    Function.Bijective ((mapBaseChange k A B).baseChange L) ↔
      Function.Bijective (tangentPullback k A B L) := by
  set F := (mapBaseChange k A B).baseChange L
  have h1 : Function.Bijective F ↔ Function.Bijective F.dualMap := by
    rw [Function.Bijective, Function.Bijective, LinearMap.dualMap_injective_iff,
      LinearMap.dualMap_surjective_iff, and_comm]
  have h2 : tangentPullback k A B L =
      dualFibreEquivDer' k A B L ∘ F.dualMap ∘ (dualFibreEquivDer k B L).symm := by
    funext D
    simp only [Function.comp_apply, F, dualFibreEquivDer'_dualMap, Equiv.apply_symm_apply]
  rw [h1, h2, Equiv.comp_bijective, Equiv.bijective_comp]

end AlgMag.Reductive
