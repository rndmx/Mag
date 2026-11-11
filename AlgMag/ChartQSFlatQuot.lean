/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Flatness over a quotient

`R` flat over `C`, `π : R → A` surjective with kernel `I R`. Then `A` is flat over `C/I`.
-/

namespace AlgMag.ChartQS

open TensorProduct

/-- The structure map `C/I → A`. -/
noncomputable def quotHom {C R A : Type*} [CommRing C] [CommRing R] [CommRing A] [Algebra C R]
    (I : Ideal C) (π : R →+* A) (hker : RingHom.ker π = I.map (algebraMap C R)) : C ⧸ I →+* A :=
  Ideal.Quotient.lift I (π.comp (algebraMap C R)) fun a ha => by
    have : algebraMap C R a ∈ RingHom.ker π := hker ▸ Ideal.mem_map_of_mem _ ha
    exact this

theorem flat_quot {C R A : Type*} [CommRing C] [CommRing R] [CommRing A] [Algebra C R]
    [Module.Flat C R] (I : Ideal C) (π : R →+* A) (hs : Function.Surjective π)
    (hker : RingHom.ker π = I.map (algebraMap C R)) :
    @Module.Flat (C ⧸ I) A _ _ (quotHom I π hker).toAlgebra.toModule := by
  letI algA : Algebra (C ⧸ I) A := (quotHom I π hker).toAlgebra
  letI algCA : Algebra C A := (π.comp (algebraMap C R)).toAlgebra
  haveI : IsScalarTower C (C ⧸ I) A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ℓ : R →ₗ[C] A :=
    { toFun := π
      map_add' := map_add π
      map_smul' := fun c r => by
        rw [Algebra.smul_def, map_mul, Algebra.smul_def]
        rfl }
  have hle : (I • ⊤ : Submodule C R) ≤ LinearMap.ker ℓ := by
    rw [Ideal.smul_top_eq_map]
    intro r hr
    have : r ∈ RingHom.ker π := hker ▸ hr
    exact this
  let g : (R ⧸ (I • ⊤ : Submodule C R)) →ₗ[C] A := Submodule.liftQ _ ℓ hle
  have hg : Function.Bijective g := by
    constructor
    · refine (injective_iff_map_eq_zero g).2 fun x hx => ?_
      obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      have h0 : π r = 0 := hx
      have : r ∈ I.map (algebraMap C R) := hker ▸ h0
      rw [Submodule.Quotient.mk_eq_zero, Ideal.smul_top_eq_map]
      exact this
    · intro a
      obtain ⟨r, rfl⟩ := hs a
      exact ⟨Submodule.Quotient.mk r, rfl⟩
  let Φ : ((C ⧸ I) ⊗[C] R) →ₗ[C] A := g ∘ₗ (quotTensorEquivQuotSMul R I).toLinearMap
  have hΦ : Function.Bijective Φ := hg.comp (quotTensorEquivQuotSMul R I).bijective
  let Ψ : ((C ⧸ I) ⊗[C] R) →ₗ[C ⧸ I] A :=
    Φ.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  let E : ((C ⧸ I) ⊗[C] R) ≃ₗ[C ⧸ I] A := LinearEquiv.ofBijective Ψ hΦ
  exact Module.Flat.of_linearEquiv E.symm

end AlgMag.ChartQS

#print axioms AlgMag.ChartQS.flat_quot
