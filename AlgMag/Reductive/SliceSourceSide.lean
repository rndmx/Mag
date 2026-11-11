/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.SliceDerivative
import AlgMag.Reductive.SliceDerivativeTorus
import AlgMag.Reductive.SliceTangentRight

/-!
# The source side of the slice tangent map (C2(d), htan: `hsrc` and `hpar`)

At `y₀ = sliceBasePt π N ψ τ`, `L₀ = rootSpace π 0` (`= Lie T`) and `g` the point `τ ∘ π`:

* `slice_hsrc`: every point derivation of the slice ring at `y₀` is `sndDer` of a dual-number
  point `slicePoint (X, Y, pt)` with `pt` over `τ` of tangent `H ∈ L₀` (`hpt`);
* `slice_hpar`: every `(X, Y, H) ∈ Lie U⁻ × Lie U⁺ × L₀` has such a `pt`.

These are the hypotheses `hsrc`, `hpar` of `pointDerComp_sliceMap_bijective`.
-/

suppress_compilation

open Magnetism TauCeti WithConv TrivSqZeroExt
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)
variable [Module.Finite k (Bialgebra.CotangentSpace k H)]
variable [IsAlgClosed k] [Algebra.FiniteType k H] [Algebra.Smooth k H]
variable (N : Magnet (Additive X)) (ψ : X →* Multiplicative ℤ) (τ : MonoidAlgebra k X →ₐ[k] k)

local notation "Cv" => Bialgebra.CounitAlgebra k H k
local notation "es" => Bialgebra.CounitAlgebra.algEquivSelf k H k
local notation "LieG" => Derivation k H Cv

lemma srcBasePt_eq_sliceBasePt : srcBasePt π N ψ τ = sliceBasePt π N ψ τ := rfl

/-- **`hpar`.** -/
theorem slice_hpar (D : SplitReductiveData π) (hπ : Function.Surjective π) (g : WithConv (H →ₐ[k] Cv))
    (hg : ∀ x, es (g.ofConv x) = τ (π x)) :
    ∀ p : (lieSlice π N ψ⁻¹ × lieSlice π N ψ) × rootSpace π 0,
      ∃ (pt : MonoidAlgebra k X →ₐ[k] DualNumber Cv)
        (_ : toConv (pt.comp π.toAlgHom) = constPt g * tanPt (p.2 : LieG)),
        ∀ b, es (fst (slicePoint π N ψ p.1.1 p.1.2 pt b)) = sliceBasePt π N ψ τ b := by
  intro p
  obtain ⟨l, hl⟩ := exists_torusTangent_eq π hπ D p.2.1 p.2.2
  refine ⟨torusDualPt H τ l, ?_, fun b => fst_slicePoint π N ψ τ p.1.1 p.1.2 l b⟩
  rw [← hl]
  exact (constPt_mul_tanPt_torusTangent π l τ g hg).symm

/-- **`hsrc`.** -/
theorem slice_hsrc (D : SplitReductiveData π) (g : WithConv (H →ₐ[k] Cv)) (hg : ∀ x, es (g.ofConv x) = τ (π x)) :
    ∀ Dd : pointDer (sliceBasePt π N ψ τ), ∃ (p : (lieSlice π N ψ⁻¹ × lieSlice π N ψ) × rootSpace π 0)
      (pt : MonoidAlgebra k X →ₐ[k] DualNumber Cv)
      (_ : toConv (pt.comp π.toAlgHom) = constPt g * tanPt (p.2 : LieG))
      (hQ : ∀ b, es (fst (slicePoint π N ψ p.1.1 p.1.2 pt b)) = sliceBasePt π N ψ τ b),
      Dd = sndDer (sliceBasePt π N ψ τ) _ hQ := by
  intro Dd
  have hτ : (sliceBasePt π N ψ τ).comp (sliceTorusHom π N ψ) = τ :=
    AlgHom.ext fun m => sliceBasePt_torus π N ψ τ m
  obtain ⟨l, hl⟩ := exists_torusDualPt_of_pointDer H τ
    (LinearEquiv.ofEq _ _ (by rw [hτ]) (pointDerComp (sliceTorusHom π N ψ) _ Dd))
  have heq := eq_sliceSndDer_of_torus π N ψ τ Dd l (fun c => hl c)
  refine ⟨((minusPart π N ψ τ Dd, plusPart π N ψ τ Dd),
    ⟨torusTangent π l, torusTangent_mem_rootSpace π l D⟩), torusDualPt H τ l,
    (constPt_mul_tanPt_torusTangent π l τ g hg).symm,
    fun b => fst_slicePoint π N ψ τ _ _ l b, ?_⟩
  exact heq.trans (Subtype.ext rfl)

end AlgMag.Reductive
