/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDR3AsmZMT

/-!
# Lemma D, Step 4: `C_d = C'_d`

For Props. 3.31 (ii), 3.32 (ii) of `Algebraic Magnetism`: for `D(a) ⊂ 𝒱 ⊂ Spec D` a section `Spec D_a → 𝒱`, and
a function on `𝒱` vanishing on `D(a)` is `a`-torsion.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgMag.SD

open AlgMag.SQ

/-- A map to `Spec K` from its global sections. -/
lemma SDR3Asm_to_spec {X : Scheme.{u}} {K : Type u} [CommRing K] (g : X ⟶ Spec (.of K)) :
    g = X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ((g.appTop.hom).comp (Scheme.ΓSpecIso (.of K)).inv.hom)) := by
  have h := Scheme.toSpecΓ_naturality g
  have e : Spec.map (CommRingCat.ofHom ((g.appTop.hom).comp (Scheme.ΓSpecIso (.of K)).inv.hom)) =
      Spec.map g.appTop ≫ Spec.map (Scheme.ΓSpecIso (.of K)).inv := by
    rw [← Spec.map_comp]
    rfl
  rw [e, ← Category.assoc, ← h, Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- A map from `Spec K` composed with `toSpecΓ`. -/
lemma SDR3Asm_from_spec {X : Scheme.{u}} {K : Type u} [CommRing K] (g : Spec (.of K) ⟶ X) :
    g ≫ X.toSpecΓ = Spec.map (CommRingCat.ofHom (((Scheme.ΓSpecIso (.of K)).hom.hom).comp g.appTop.hom)) := by
  rw [Scheme.toSpecΓ_naturality]
  have e : Spec.map (CommRingCat.ofHom (((Scheme.ΓSpecIso (.of K)).hom.hom).comp g.appTop.hom)) =
      Spec.map (Scheme.ΓSpecIso (.of K)).hom ≫ Spec.map g.appTop := by
    rw [← Spec.map_comp]
    rfl
  rw [e, SpecMap_ΓSpecIso_hom]

variable {𝒱 : Scheme.{u}} {D : Type u} [CommRing D] (φ : D →+* Γ(𝒱, ⊤))

/-- `j = 𝒱 → Spec Γ(𝒱) → Spec D`. -/
noncomputable abbrev SDR3Asm_j : 𝒱 ⟶ Spec (.of D) := 𝒱.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)

/-- The composite of a map from `Spec K` with `j`. -/
lemma SDR3Asm_comp_j {K : Type u} [CommRing K] (g : Spec (.of K) ⟶ 𝒱) :
    g ≫ SDR3Asm_j φ = Spec.map (CommRingCat.ofHom ((((Scheme.ΓSpecIso (.of K)).hom.hom).comp g.appTop.hom).comp φ)) := by
  rw [← Category.assoc, SDR3Asm_from_spec, ← Spec.map_comp]
  rfl

/-- The lift of `D(a) ⊂ 𝒱`. -/
theorem SDR3Asm_section [hj : IsOpenImmersion (SDR3Asm_j φ)] (a : D)
    (ha : ∀ p : PrimeSpectrum D, a ∉ p.asIdeal → p ∈ Set.range (SDR3Asm_j φ)) :
    ∃ θ : Spec (.of (Localization.Away a)) ⟶ 𝒱, IsOpenImmersion θ ∧
      θ ≫ SDR3Asm_j φ = Spec.map (CommRingCat.ofHom (algebraMap D (Localization.Away a))) := by
  have hr : Set.range (Spec.map (CommRingCat.ofHom (algebraMap D (Localization.Away a)))) ⊆
      Set.range (SDR3Asm_j φ) := by
    rintro _ ⟨y, rfl⟩
    refine ha _ fun hm => ?_
    have hu : IsUnit (algebraMap D (Localization.Away a) a) := IsLocalization.Away.algebraMap_isUnit a
    exact (Ideal.IsPrime.ne_top y.2) (Ideal.eq_top_of_isUnit_mem _ hm hu)
  refine ⟨IsOpenImmersion.lift (SDR3Asm_j φ) _ hr, ?_, IsOpenImmersion.lift_fac _ _ _⟩
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap D (Localization.Away a)))) :=
    IsOpenImmersion.of_isLocalization a
  have h := IsOpenImmersion.lift_fac (SDR3Asm_j φ) _ hr
  haveI : IsOpenImmersion (IsOpenImmersion.lift (SDR3Asm_j φ) _ hr ≫ SDR3Asm_j φ) := by
    rw [h]
    infer_instance
  exact IsOpenImmersion.of_comp _ (SDR3Asm_j φ)

/-- `C_a = C'_a`: a global function vanishing on `D(a)` is `a`-torsion. -/
theorem SDR3Asm_torsion [CompactSpace 𝒱] [hj : IsOpenImmersion (SDR3Asm_j φ)] (a : D)
    {θ : Spec (.of (Localization.Away a)) ⟶ 𝒱} [hθ : IsOpenImmersion θ]
    (hθj : θ ≫ SDR3Asm_j φ = Spec.map (CommRingCat.ofHom (algebraMap D (Localization.Away a))))
    (w : Γ(𝒱, ⊤)) (hw : θ.appTop.hom w = 0) : ∃ n : ℕ, φ a ^ n * w = 0 := by
  have hle : 𝒱.basicOpen (φ a) ≤ θ.opensRange := by
    intro x hx
    have h1 : (𝒱.toSpecΓ x) ∈ PrimeSpectrum.basicOpen (φ a) := by
      have : x ∈ 𝒱.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen (φ a) := by
        rw [Scheme.toSpecΓ_preimage_basicOpen]
        exact hx
      exact this
    have h2 : (SDR3Asm_j φ x) ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap D (Localization.Away a)))) := by
      have hr := PrimeSpectrum.localization_away_comap_range (Localization.Away a) a
      have : SDR3Asm_j φ x ∈ Set.range (PrimeSpectrum.comap (algebraMap D (Localization.Away a))) := by
        rw [hr]
        exact h1
      exact this
    obtain ⟨y, hy⟩ := h2
    rw [← hθj] at hy
    have hy' : SDR3Asm_j φ (θ y) = SDR3Asm_j φ x := hy
    exact ⟨y, (SDR3Asm_j φ).isOpenEmbedding.injective hy'⟩
  let U := 𝒱.basicOpen (φ a)
  haveI hiso : IsIso (θ.app U) := Scheme.Hom.isIso_app θ U hle
  have hinj : Function.Injective (θ.app U).hom := (asIso (θ.app U)).commRingCatIsoToRingEquiv.injective
  have hn := congrArg (fun k => k.hom w) (θ.naturality (homOfLE (le_top : U ≤ ⊤)).op)
  have h0 : (𝒱.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom w = 0 := by
    apply hinj
    rw [map_zero]
    refine Eq.trans hn ?_
    change ((Spec (.of (Localization.Away a))).presheaf.map _).hom (θ.appTop.hom w) = 0
    rw [hw, map_zero]
  exact exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact 𝒱 (U := ⊤) isCompact_univ w (φ a) h0

end AlgMag.SD
