/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.EtaleSliceAssembly
import AlgMag.Reductive.SliceTangentRight
import AlgMag.Reductive.SliceTangentHyps
import AlgMag.Reductive.SliceSourceSide

/-!
# The tangent hypothesis `htan` of C2(d) on a lattice, from the source parametrisation

`sliceTangentBijective_lattice`: the exact `htan` of `regularConjugatesOpen_lattice`, with the
target side (`SliceTangentRight`) and the Lie-algebra inputs (`SliceTangentHyps`: injectivity,
range `Lie K`, `Ad(t₀⁻¹) Lie K ⊆ Lie K`) discharged. The only hypothesis left is `SliceSrc`:
every point derivation of `O(U⁻ × U⁺ × T)` at `(e, e, τ)` comes from a dual-number
`slicePoint`, and every parameter `(X, Y, H)` has one.

`regularConjugatesOpen_lattice_of_src`: `RegularConjugatesOpen π` (C2(d)) from `SliceSrc`.
-/

suppress_compilation

open Magnetism TauCeti WithConv TrivSqZeroExt
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X) [Module.Finite k (Bialgebra.CotangentSpace k H)]
  [IsAlgClosed k] [Algebra.FiniteType k H] [Algebra.Smooth k H]

local notation "Cv" => Bialgebra.CounitAlgebra k H k
local notation "ev" => Bialgebra.CounitAlgebra.algEquivSelf k H k
local notation "LieG" => Derivation k H Cv

/-- The torus point `t₀ = τ ∘ π`, as a `CounitAlgebra`-valued point. -/
def torusCv (τ : MonoidAlgebra k X →ₐ[k] k) : WithConv (H →ₐ[k] Cv) := toConv (τ.comp π.toAlgHom)

lemma torusCv_apply (τ : MonoidAlgebra k X →ₐ[k] k) (x : H) :
    ev ((torusCv π τ).ofConv x) = τ (π x) := rfl

/-- **The source-side parametrisation** at `(e, e, τ)`: every point derivation of the slice
ring is the infinitesimal part of a dual-number `slicePoint` (`hsrc`), and every parameter
`(X, Y, H) ∈ Lie U⁻ × Lie U⁺ × 𝔤_0` has such a point (`hpar`). -/
def SliceSrc (N : Magnet (Additive X)) (ψ : X →* Multiplicative ℤ)
    (τ : MonoidAlgebra k X →ₐ[k] k) : Prop :=
  (∀ Dd : pointDer (sliceBasePt π N ψ τ),
    ∃ (p : (lieSlice π N ψ⁻¹ × lieSlice π N ψ) × rootSpace π 0)
      (pt : MonoidAlgebra k X →ₐ[k] DualNumber Cv)
      (_ : toConv (pt.comp π.toAlgHom) = constPt (torusCv π τ) * tanPt (p.2 : LieG))
      (hQ : ∀ b, ev (fst (slicePoint π N ψ p.1.1 p.1.2 pt b)) = sliceBasePt π N ψ τ b),
      Dd = sndDer (sliceBasePt π N ψ τ) _ hQ) ∧
  (∀ p : (lieSlice π N ψ⁻¹ × lieSlice π N ψ) × rootSpace π 0,
    ∃ (pt : MonoidAlgebra k X →ₐ[k] DualNumber Cv)
      (_ : toConv (pt.comp π.toAlgHom) = constPt (torusCv π τ) * tanPt (p.2 : LieG)),
      ∀ b, ev (fst (slicePoint π N ψ p.1.1 p.1.2 pt b)) = sliceBasePt π N ψ τ b)

variable (D : SplitReductiveData π) [Monoid.FG X] [IsMulTorsionFree X]

/-- **`htan` on a lattice**, from the source parametrisation only. -/
theorem sliceTangentBijective_lattice (N : Magnet (Additive X)) (ψ : X →* Multiplicative ℤ)
    (hψ : ∀ α ∈ roots π, α ∈ N → pairingHom ψ α ≠ 0) (τ : MonoidAlgebra k X →ₐ[k] k)
    (hτ : ∀ α ∈ roots π, α ∈ N → τ (MonoidAlgebra.single (Additive.toMul α) 1) ≠ 1)
    (hS : SliceSrc π N ψ τ) :
    SliceTangentBijective π N ψ (compIdeal_le_ker_torus π D N) (sliceBasePt π N ψ τ) := by
  have hg : ∀ x, ev ((torusCv π τ).ofConv x) = τ (π x) := torusCv_apply π τ
  have hψ' : ∀ α ∈ RK π N, pairingHom ψ α ≠ 0 := fun α h => hψ α h.1 h.2
  refine sliceTangentBijective_of_pointDerComp π N ψ _ _
    (pointDerComp_sliceMap_bijective π N ψ _ (torusCv π τ) (rootSpace π 0) _ D.surjective
      hS.1 hS.2 (sliceTangentMap_injective_G hg hτ hψ') ?_ ?_)
  · intro v hv
    have hv' : v ∈ LinearMap.range (sliceTangentMap
        (Derivation.adRepresentation k (torusCv π τ)⁻¹) (USub π N ψ⁻¹) (USub π N ψ)
        (rootSpace π 0)) := by
      rw [range_sliceTangentMap_G hg hτ hψ']; exact hv
    exact LinearMap.mem_range.1 hv'
  · intro v hv
    have hv' : v ∈ LK π N := hv
    rw [LK_eq] at hv'
    have h := adInv_mem_vanishOff hg hv'
    rw [← LK_eq, Derivation.adRepresentation_apply] at h
    exact h

open scoped AlgMag.Reductive.Zariski in
include D in
/-- **C2(d) on a lattice** (`RegularConjugatesOpen π`), from the source parametrisation. -/
theorem regularConjugatesOpen_lattice_of_src
    (hS : ∀ N : Magnet (Additive X), ∀ ψ : X →* Multiplicative ℤ,
      (∀ α ∈ roots π, α ∈ N → pairingHom ψ α ≠ 0) → ∀ τ : MonoidAlgebra k X →ₐ[k] k,
        (∀ α ∈ roots π, α ∈ N → τ (MonoidAlgebra.single (Additive.toMul α) 1) ≠ 1) →
          SliceSrc π N ψ τ) :
    ∀ N : Magnet (Additive X), ∃ U : Set (compSubgroup π N), IsOpen U ∧ U.Nonempty ∧
      ∀ x ∈ U, ∃ g ∈ compSubgroup π N, ∃ t ∈ regularPoints π N,
        (x : WithConv (H →ₐ[k] k)) = g * t * g⁻¹ :=
  regularConjugatesOpen_lattice π D fun N ψ hψ τ hτ =>
    sliceTangentBijective_lattice π D N ψ hψ τ hτ (hS N ψ hψ τ hτ)


include D in
/-- **The source parametrisation holds** (`SliceSourceSide`: `slice_hsrc`, `slice_hpar`). -/
theorem sliceSrc_lattice (N : Magnet (Additive X)) (ψ : X →* Multiplicative ℤ)
    (τ : MonoidAlgebra k X →ₐ[k] k) : SliceSrc π N ψ τ :=
  ⟨slice_hsrc π N ψ τ D (torusCv π τ) (torusCv_apply π τ),
    slice_hpar π N ψ τ D D.surjective (torusCv π τ) (torusCv_apply π τ)⟩

open scoped AlgMag.Reductive.Zariski in
include D in
/-- **Step C2(d) for split reductive data on a lattice, hypothesis-free**:
`RegularConjugatesOpen π` (by definition). -/
theorem regularConjugatesOpen_lattice_final :
    ∀ N : Magnet (Additive X), ∃ U : Set (compSubgroup π N), IsOpen U ∧ U.Nonempty ∧
      ∀ x ∈ U, ∃ g ∈ compSubgroup π N, ∃ t ∈ regularPoints π N,
        (x : WithConv (H →ₐ[k] k)) = g * t * g⁻¹ :=
  regularConjugatesOpen_lattice_of_src π D fun N ψ _ τ _ => sliceSrc_lattice π D N ψ τ

end AlgMag.Reductive
