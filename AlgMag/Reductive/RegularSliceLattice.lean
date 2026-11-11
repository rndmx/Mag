/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.RegularSliceTangent
import AlgMag.Reductive.GluePrereqs

/-!
# The slice map for split reductive data on a lattice: `T ⊆ K` discharged

For split reductive data with `X` finitely generated and torsion free, `(G^0)° = T`
(`compIdeal_bot_iff_of_torsionFree`), and `(G^N)° ⊆ (G^0)°` is replaced by `T ⊆ (G^N)°`:
`compIdeal π N ≤ compIdeal π ⊥ = ker π`. This removes the hypothesis `hT` of `sliceMap`.

* `compIdeal_le_bot`: `T`-side monotonicity `compIdeal π N ≤ compIdeal π ⊥`;
* `compIdeal_le_ker_torus`: `T ⊆ K`;
* `sliceMap'`, `sliceMap'_comp_compMk`, `sliceMap'_tangent`.
-/

suppress_compilation

open Magnetism TauCeti WithConv TrivSqZeroExt
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)
variable [IsAlgClosed k] [Algebra.FiniteType k H]

/-- `(G^N)°` contains `(G^0)°`, on ideals: `compIdeal π N ≤ compIdeal π ⊥`. -/
lemma compIdeal_le_bot (N : Magnet (Additive X)) : compIdeal π N ≤ compIdeal π ⊥ := by
  obtain ⟨f, hf⟩ := exists_comp_compMk π (bot_le : (⊥ : Magnet (Additive X)) ≤ N)
  intro x hx
  show compMk π ⊥ x = 0
  rw [← hf, BialgHom.comp_apply]
  have : compMk π N x = 0 := hx
  rw [this, map_zero]

variable [Module.Finite k (Bialgebra.CotangentSpace k H)] [Algebra.Smooth k H]

/-- **`T ⊆ K = (G^N)°`** for split reductive data on a lattice. -/
theorem compIdeal_le_ker_torus (D : SplitReductiveData π) [Monoid.FG X] [IsMulTorsionFree X]
    (N : Magnet (Additive X)) : compIdeal π N ≤ RingHom.ker π.toAlgHom := fun x hx =>
  (compIdeal_bot_iff_of_torsionFree π D x).1 (compIdeal_le_bot π N hx)

variable (D : SplitReductiveData π) [Monoid.FG X] [IsMulTorsionFree X]
variable (N : Magnet (Additive X)) (ψ : X →* Multiplicative ℤ)

/-- **The slice map** `μ^* : O(K) → O(U⁻) ⊗ O(U⁺) ⊗ O(T)` without the hypothesis `T ⊆ K`. -/
def sliceMap' : compAlg π N →ₐ[k] sliceSource π N ψ :=
  sliceMap π N ψ (compIdeal_le_ker_torus π D N)

theorem sliceMap'_comp_compMk :
    (sliceMap' π D N ψ).comp (compMk π N : H →ₐ[k] compAlg π N) = (sliceConj π N ψ).ofConv :=
  sliceMap_comp_compMk π N ψ _

local notation "Cv" => Bialgebra.CounitAlgebra k H k

/-- **The tangent map of `μ` at `(e, e, t)`**, hypothesis-free form of `sliceMap_tangent`. -/
theorem sliceMap'_tangent (g : WithConv (H →ₐ[k] Cv)) (L₀ : Submodule k (Derivation k H Cv))
    (p : (lieSlice π N ψ⁻¹ × lieSlice π N ψ) × L₀)
    (pt : MonoidAlgebra k X →ₐ[k] DualNumber Cv)
    (hpt : toConv (pt.comp π.toAlgHom) = constPt g * tanPt (p.2 : Derivation k H Cv)) :
    (constPt g)⁻¹ * toConv ((slicePoint π N ψ p.1.1 p.1.2 pt).comp
        ((sliceMap' π D N ψ).comp (compMk π N : H →ₐ[k] compAlg π N))) =
      tanPt (sliceTangentMap (Derivation.adRepresentation k g⁻¹)
        (lieSlice π N ψ⁻¹) (lieSlice π N ψ) L₀ p) :=
  sliceMap_tangent π N ψ _ g L₀ p pt hpt

end AlgMag.Reductive
