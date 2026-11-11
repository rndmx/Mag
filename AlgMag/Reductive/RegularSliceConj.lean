/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.RegularSliceLattice
import AlgMag.Reductive.OpenImagePoints

/-!
# Points of the slice are regular conjugates in `K` (`hK`, `hconj` of C2(d))

Let `B` be a `k`-algebra with `φ : O(U⁻ × U⁺ × T) → B` (e.g. a localization), viewed as an
`H`-algebra through `μ^*`: `H → O(K) → O(U⁻ × U⁺ × T) → B`. Then every `k`-point of `G`
lifting to a `k`-point `y` of `B` is `x = (u v) t (u v)⁻¹` with `u, v` the `U^±`-coordinates of
`y` (in `K`) and `t` its torus coordinate:

* `liftPoints_subset_compSubgroup`: such `x` lie in `K = (G^N)°` (`hK`);
* `liftPoints_conj`: if `Δ = ∏_{α ∈ R} (α - 1)` (`R ⊇ N ∩ Φ`) is invertible in `B`, then `t`
  is regular (`hconj`).
-/

suppress_compilation

open Magnetism TauCeti WithConv
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)
variable [IsAlgClosed k] [Algebra.FiniteType k H]
variable [Module.Finite k (Bialgebra.CotangentSpace k H)] [Algebra.Smooth k H]
variable (D : SplitReductiveData π) [Monoid.FG X] [IsMulTorsionFree X]
variable (N : Magnet (Additive X)) (ψ : X →* Multiplicative ℤ)

/-- The torus coordinate `O(T) → O(U⁻ × U⁺ × T)`. -/
def sliceTorusIncl : MonoidAlgebra k X →ₐ[k] sliceSource π N ψ :=
  Algebra.TensorProduct.includeRight

/-- `Δ = ∏_{α ∈ R} (α - 1)` on the torus factor. -/
def sliceDelta (R : Finset (Additive X)) : sliceSource π N ψ :=
  sliceTorusIncl π N ψ (∏ α ∈ R, (MonoidAlgebra.single (Additive.toMul α) (1 : k) - 1))

variable {B : Type u} [CommRing B] [Algebra k B] [Algebra H B] [IsScalarTower k H B]
variable (φ : sliceSource π N ψ →ₐ[k] B)
variable (hB : IsScalarTower.toAlgHom k H B = φ.comp ((sliceMap' π D N ψ).comp
  (compMk π N : H →ₐ[k] compAlg π N)))

include hB in
/-- A lifted point is the conjugation formula evaluated at the slice coordinates. -/
lemma liftPoint_eq (y : B →ₐ[k] k) :
    toConv (y.comp (IsScalarTower.toAlgHom k H B)) =
      conjFormula (AlgHom.mapValue (y.comp φ) (slicePtMinus π N ψ))
        (AlgHom.mapValue (y.comp φ) (slicePtPlus π N ψ))
        (AlgHom.mapValue (y.comp φ) (slicePtTorus π N ψ)) := by
  rw [hB, sliceMap'_comp_compMk, ← AlgHom.comp_assoc]
  show AlgHom.mapValue (y.comp φ) (sliceConj π N ψ) = _
  rw [sliceConj, conjFormula, conjFormula, map_mul, map_mul, map_inv, map_mul]

lemma mapValue_slicePtMinus_mem (z : sliceSource π N ψ →ₐ[k] k) :
    AlgHom.mapValue z (slicePtMinus π N ψ) ∈ compSubgroup π N := by
  rw [mem_compSubgroup]
  intro x hx
  have h := compIdeal_le_sliceIdeal π N ψ⁻¹ hx
  rw [RingHom.mem_ker, AlgHom.mapValue_apply, ofConv_toConv, slicePtMinus, ofConv_toConv]
  change z (Algebra.TensorProduct.includeLeft (S := k) (Algebra.TensorProduct.includeLeft
    (S := k) (Ideal.Quotient.mk (sliceIdeal π N ψ⁻¹).toIdeal x))) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.2 h, map_zero, map_zero]
  exact map_zero z

lemma mapValue_slicePtPlus_mem (z : sliceSource π N ψ →ₐ[k] k) :
    AlgHom.mapValue z (slicePtPlus π N ψ) ∈ compSubgroup π N := by
  rw [mem_compSubgroup]
  intro x hx
  have h := compIdeal_le_sliceIdeal π N ψ hx
  rw [RingHom.mem_ker, AlgHom.mapValue_apply, ofConv_toConv, slicePtPlus, ofConv_toConv]
  change z (Algebra.TensorProduct.includeLeft (S := k) (Algebra.TensorProduct.includeRight
    (Ideal.Quotient.mk (sliceIdeal π N ψ).toIdeal x))) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.2 h, map_zero, map_zero]
  exact map_zero z

include D in
lemma mapValue_slicePtTorus_mem (z : sliceSource π N ψ →ₐ[k] k) :
    AlgHom.mapValue z (slicePtTorus π N ψ) ∈ compSubgroup π N := by
  rw [mem_compSubgroup]
  intro x hx
  have h : π.toAlgHom x = 0 := compIdeal_le_ker_torus π D N hx
  rw [RingHom.mem_ker, AlgHom.mapValue_apply, ofConv_toConv, slicePtTorus, ofConv_toConv]
  change z (Algebra.TensorProduct.includeRight (π.toAlgHom x)) = 0
  rw [h, map_zero]
  exact map_zero z

include hB in
/-- **`hK`**: lifted points lie in `K = (G^N)°`. -/
theorem liftPoints_subset_compSubgroup : liftPoints (k := k) (H := H) B ⊆ compSubgroup π N := by
  rintro x ⟨y, hy⟩
  have hx : x = toConv (y.comp (IsScalarTower.toAlgHom k H B)) := by rw [hy, toConv_ofConv]
  rw [hx, liftPoint_eq π D N ψ φ hB, conjFormula]
  have hm := mapValue_slicePtMinus_mem π N ψ (y.comp φ)
  have hp := mapValue_slicePtPlus_mem π N ψ (y.comp φ)
  have ht := mapValue_slicePtTorus_mem π D N ψ (y.comp φ)
  exact mul_mem (mul_mem (mul_mem hm hp) ht) (inv_mem (mul_mem hm hp))

include hB in
/-- **`hconj`**: if `Δ` is invertible in `B`, every lifted point is `g t g⁻¹` with `g ∈ K` and
`t` regular. -/
theorem liftPoints_conj (R : Finset (Additive X)) (hR : ∀ α ∈ roots π, α ∈ N → α ∈ R)
    (hΔ : IsUnit (φ (sliceDelta π N ψ R))) :
    ∀ x ∈ liftPoints (k := k) (H := H) B,
      ∃ g ∈ compSubgroup π N, ∃ t ∈ regularPoints π N, x = g * t * g⁻¹ := by
  rintro x ⟨y, hy⟩
  have hx : x = toConv (y.comp (IsScalarTower.toAlgHom k H B)) := by rw [hy, toConv_ofConv]
  refine ⟨AlgHom.mapValue (y.comp φ) (slicePtMinus π N ψ) *
      AlgHom.mapValue (y.comp φ) (slicePtPlus π N ψ),
    mul_mem (mapValue_slicePtMinus_mem π N ψ _) (mapValue_slicePtPlus_mem π N ψ _),
    AlgHom.mapValue (y.comp φ) (slicePtTorus π N ψ), ?_, by
      rw [hx, liftPoint_eq π D N ψ φ hB, conjFormula]⟩
  set τ : MonoidAlgebra k X →ₐ[k] k := (y.comp φ).comp (sliceTorusIncl π N ψ)
  refine ⟨τ, ?_, fun α hα hαN h1 => ?_⟩
  · rw [AlgHom.mapValue_apply]
    rfl
  · have hu : IsUnit (y (φ (sliceDelta π N ψ R))) := hΔ.map y
    have h0 : y (φ (sliceDelta π N ψ R)) =
        ∏ β ∈ R, (τ (MonoidAlgebra.single (Additive.toMul β) (1 : k)) - 1) := by
      simp only [sliceDelta, τ, AlgHom.comp_apply, map_prod, map_sub, map_one]
    rw [h0, Finset.prod_eq_zero (hR α hα hαN) (by rw [h1, sub_self])] at hu
    exact not_isUnit_zero hu

end AlgMag.Reductive
