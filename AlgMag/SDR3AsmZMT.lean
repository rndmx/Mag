/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDR3AsmG3
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Lemma D, Step 4: `C'` from `toNormalization`

For Props. 3.31 (ii), 3.32 (ii) of `Algebraic Magnetism`. For `f : 𝒱 → Spec B` separated, quasi-finite, quasi-compact,
`𝒱 → Spec C'` is an open immersion, where `C'` is the integral closure of `B` in `Γ(𝒱, O)`; this is Mathlib's form of
Stacks 03GW, at the affine open `⊤` of `Spec B`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgMag.SD

section

variable {B₀ : Type u} [CommRing B₀] {𝒱 : Scheme.{u}} (f : 𝒱 ⟶ Spec (.of B₀))

/-- `B → Γ(𝒱, O)`. -/
noncomputable def SDR3Asm_fs : B₀ →+* Γ(𝒱, ⊤) :=
  (f.appTop.hom).comp ((Scheme.ΓSpecIso (.of B₀)).inv.hom)

/-- The integral closure of `B` in `Γ(𝒱, O)`, as a subring. -/
noncomputable def SDR3Asm_S : Subring Γ(𝒱, ⊤) :=
  letI := (SDR3Asm_fs f).toAlgebra
  (integralClosure B₀ Γ(𝒱, ⊤)).toSubring

lemma SDR3Asm_of_comp {X Y Z W : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ W) (hc : IsOpenImmersion c)
    (h : IsOpenImmersion (a ≫ b ≫ c)) : IsOpenImmersion (a ≫ b) := by
  rw [← Category.assoc] at h
  exact IsOpenImmersion.of_comp _ c

/-- **Step 4**. `𝒱 → Spec C'` is an open immersion. -/
theorem SDR3Asm_zmt [IsSeparated f] [LocallyQuasiFinite f] [LocallyOfFiniteType f] [QuasiCompact f] :
    IsOpenImmersion (𝒱.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (SDR3Asm_S f).subtype)) := by
  let U : (Spec (.of B₀)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have h := Scheme.Hom.ι_toNormalization f U
  have h2 : IsOpenImmersion ((f ⁻¹ᵁ U.1).ι ≫ Scheme.Hom.toNormalization f) := inferInstance
  rw [h] at h2
  letI i₁ := (f.app U.1).hom.toAlgebra
  have h3 : IsOpenImmersion ((f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (integralClosure Γ(Spec (.of B₀), U.1) Γ(𝒱, f ⁻¹ᵁ U.1)).val.toRingHom)) := by
    exact SDR3Asm_of_comp _ _ ((Scheme.Hom.normalizationOpenCover f).f U)
      ((Scheme.Hom.normalizationOpenCover f).map_prop U) h2
  let S₁ : Subring Γ(𝒱, ⊤) := (integralClosure Γ(Spec (.of B₀), U.1) Γ(𝒱, f ⁻¹ᵁ U.1)).toSubring
  have hS : S₁ = SDR3Asm_S f := by
    letI i₂ := (SDR3Asm_fs f).toAlgebra
    let e : B₀ ≃+* Γ(Spec (.of B₀), ⊤) := (Scheme.ΓSpecIso (.of B₀)).symm.commRingCatIsoToRingEquiv
    have hfs : ∀ b, algebraMap B₀ Γ(𝒱, ⊤) b = (f.app ⊤).hom (e b) := fun _ => rfl
    ext x
    constructor
    · rintro ⟨p, hp, h0⟩
      refine ⟨p.map (e.symm : Γ(Spec (.of B₀), ⊤) →+* B₀), hp.map _, ?_⟩
      have hc : (algebraMap B₀ Γ(𝒱, ⊤)).comp (e.symm : Γ(Spec (.of B₀), ⊤) →+* B₀) = (f.app ⊤).hom :=
        RingHom.ext fun b => congrArg (f.app ⊤).hom (e.apply_symm_apply b)
      refine (Polynomial.eval₂_map _ _ x).trans ?_
      rw [hc]
      exact h0
    · rintro ⟨p, hp, h0⟩
      refine ⟨p.map (e : B₀ →+* Γ(Spec (.of B₀), ⊤)), hp.map _, ?_⟩
      exact (Polynomial.eval₂_map (e : B₀ →+* Γ(Spec (.of B₀), ⊤)) (f.app ⊤).hom x).trans h0
  change IsOpenImmersion ((⊤ : 𝒱.Opens).toSpecΓ ≫ Spec.map (CommRingCat.ofHom S₁.subtype)) at h3
  rw [Scheme.Opens.toSpecΓ_top, Category.assoc, hS] at h3
  haveI : IsIso (⊤ : 𝒱.Opens).ι := inferInstanceAs (IsIso (𝒱.topIso).hom)
  exact (MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion _ _).1 h3

end

end AlgMag.SD
