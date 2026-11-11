/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.

-/
import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.OrzechProperty
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# An étaleness criterion via the Jacobi–Zariski sequence

For `R → S → T` with `T` formally smooth over `R`, if `T ⊗[S] Ω[S⁄R] → Ω[T⁄R]` is bijective then
`T` is formally étale over `S`. Proof: Mathlib's `FormallyEtale` *is* `Ω[T⁄S] = 0 ∧ H¹(L_{T/S}) = 0`;
both follow from the exact sequences

  `T ⊗ Ω[S/R] → Ω[T/R] → Ω[T/S] → 0`                       (`exact_mapBaseChange_map`)
  `H¹(L_{T/R}) → H¹(L_{T/S}) →δ T ⊗ Ω[S/R] → Ω[T/R]`        (`exact_map_δ`, `exact_δ_mapBaseChange`)

with `H¹(L_{T/R}) = 0` (formal smoothness). Plus: a surjection between finite free modules of the
same rank is bijective (Orzech property).
-/

namespace AlgMag.OpenCellNotes

open scoped TensorProduct

universe u

section Criterion

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- **Étaleness from bijectivity of `T ⊗ Ω_S → Ω_T`**, `T` formally smooth over `R`. -/
theorem formallyEtale_of_mapBaseChange_bijective [Algebra.FormallySmooth R T]
    (h : Function.Bijective (KaehlerDifferential.mapBaseChange R S T)) :
    Algebra.FormallyEtale S T := by
  refine ⟨⟨fun x y => ?_⟩, ⟨fun x y => ?_⟩⟩
  · suffices H0 : ∀ z : Ω[T⁄S], z = 0 by rw [H0 x, H0 y]
    intro z
    obtain ⟨w, rfl⟩ := KaehlerDifferential.map_surjective R S T z
    obtain ⟨v, rfl⟩ := h.2 w
    exact (KaehlerDifferential.exact_mapBaseChange_map R S T).apply_apply_eq_zero v
  · suffices H0 : ∀ z : Algebra.H1Cotangent S T, z = 0 by rw [H0 x, H0 y]
    intro z
    have h0 : Algebra.H1Cotangent.δ R S T z = 0 := by
      apply h.1
      rw [(Algebra.H1Cotangent.exact_δ_mapBaseChange R S T).apply_apply_eq_zero, map_zero]
    obtain ⟨w, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ R S T z).mp h0
    rw [Subsingleton.elim w 0, map_zero]

/-- **Étale, hence flat.** -/
theorem flat_of_mapBaseChange_bijective [Algebra.FormallySmooth R T]
    [Algebra.FinitePresentation S T]
    (h : Function.Bijective (KaehlerDifferential.mapBaseChange R S T)) :
    Module.Flat S T := by
  have := formallyEtale_of_mapBaseChange_bijective h
  have : Algebra.Etale S T := ⟨inferInstance, inferInstance⟩
  -- `Etale → Smooth` (instance) and `Algebra.Smooth.flat` (instance).
  infer_instance

/-- If `Ω[T⁄S]` is trivial, `T ⊗ Ω_S → Ω_T` is surjective. -/
theorem mapBaseChange_surjective_of_subsingleton [Subsingleton Ω[T⁄S]] :
    Function.Surjective (KaehlerDifferential.mapBaseChange R S T) := by
  intro w
  have : KaehlerDifferential.map R S T T w = 0 := Subsingleton.elim _ _
  exact (KaehlerDifferential.exact_mapBaseChange_map R S T w).mp this

end Criterion

/-- A surjection between finite free modules of the same rank over a nontrivial commutative ring
is bijective. -/
theorem bijective_of_surjective_of_finrank_eq {A M N : Type*} [CommRing A] [Nontrivial A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Free A M] [Module.Finite A M] [Module.Free A N] [Module.Finite A N]
    (f : M →ₗ[A] N) (hf : Function.Surjective f) (h : Module.finrank A M = Module.finrank A N) :
    Function.Bijective f := by
  let e : N ≃ₗ[A] M := LinearEquiv.ofFinrankEq N M h.symm
  have hinj : Function.Injective (e.toLinearMap ∘ₗ f) :=
    OrzechProperty.injective_of_surjective_endomorphism _ (e.surjective.comp hf)
  refine ⟨fun x y hxy => hinj ?_, hf⟩
  simp [hxy]

end AlgMag.OpenCellNotes
