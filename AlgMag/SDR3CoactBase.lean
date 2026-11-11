/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDR3CoactAffine

/-!
# Lemma D, Step 3: `Γ(V × D(Λ)) = Γ(V)[Λ]` for a base change of `Spec A[Λ] → Spec A`
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace AlgMag.SD

variable {Y Z : Scheme.{u}} {Λ A : Type u} [AddCommGroup Λ] [CommRing A]

/-- The universal character pulled back along `g : Y → Spec A[Λ]`. -/
noncomputable def SDR3Coact_chi (g : Y ⟶ Spec (.of (AddMonoidAlgebra A Λ))) : Multiplicative Λ →* Γ(Y, ⊤) where
  toFun d := g.appTop.hom ((Scheme.ΓSpecIso (.of (AddMonoidAlgebra A Λ))).inv.hom
    (AddMonoidAlgebra.single (Multiplicative.toAdd d) 1))
  map_one' := by
    have : AddMonoidAlgebra.single (Multiplicative.toAdd (1 : Multiplicative Λ)) (1 : A) = 1 := rfl
    rw [this, map_one, map_one]
  map_mul' x y := by
    rw [← map_mul, ← map_mul, AddMonoidAlgebra.single_mul_single, mul_one]
    rfl

/-- The map `Spec A[Λ] → Spec A`. -/
noncomputable abbrev SDR3Coact_str (A Λ : Type u) [CommRing A] [AddCommGroup Λ] :
    Spec (.of (AddMonoidAlgebra A Λ)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom AddMonoidAlgebra.singleZeroRingHom)

lemma SDR3Coact_restrict_top (π : Y ⟶ Z) (U : Z.Opens) :
    (π ∣_ U).appTop ≫ (Scheme.Opens.topIso (π ⁻¹ᵁ U)).hom = (Scheme.Opens.topIso U).hom ≫ π.app U := by
  rw [morphismRestrict_appTop]
  simp only [Scheme.Opens.topIso_hom]
  have h := π.naturality (eqToHom (Scheme.Opens.ι_image_top U).symm).op
  exact (Category.assoc _ _ _).trans
    (Eq.trans (congrArg (π.app _ ≫ ·) ((Y.presheaf.map_comp _ _).symm.trans rfl)) h.symm)

lemma SDR3Coact_ι_top (U : Y.Opens) (x : Γ(Y, ⊤)) :
    (Scheme.Opens.topIso U).hom.hom (U.ι.appTop.hom x) = (Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom x := by
  have h : U.ι.appTop ≫ (Scheme.Opens.topIso U).hom = Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op := by
    simp only [Scheme.Opens.topIso_hom]
    simp
    exact (Y.presheaf.map_comp _ _).symm.trans rfl
  exact congrArg (fun k => k.hom x) h

lemma SDR3Coact_map_bijective {R R' : CommRingCat.{u}} (e : R ≅ R') :
    Function.Bijective (AddMonoidAlgebra.mapRingHom Λ e.hom.hom) := by
  refine Function.bijective_iff_has_inverse.2 ⟨AddMonoidAlgebra.mapRingHom Λ e.inv.hom, fun a => ?_, fun a => ?_⟩
  · ext d; simp
  · ext d; simp

/-- **Step 3, the affine case**: over a base change `Y` of `Spec A[Λ] → Spec A`, the comparison is bijective on affine
opens of `Z`. -/
theorem SDR3Coact_base_bijective {g : Y ⟶ Spec (.of (AddMonoidAlgebra A Λ))} {π : Y ⟶ Z} {r : Z ⟶ Spec (.of A)}
    (h : IsPullback g π (SDR3Coact_str A Λ) r) (U : Z.Opens) (hU : IsAffineOpen U) :
    Function.Bijective (SDR3Coact_φ π (SDR3Coact_chi g) U) := by
  have : IsAffine U.toScheme := hU
  have hpb : IsPullback ((π ⁻¹ᵁ U).ι ≫ g) (π ∣_ U) (SDR3Coact_str A Λ) (U.ι ≫ r) :=
    (isPullback_morphismRestrict π U).flip.paste_horiz h
  have hP := isPushout_appTop_of_isPullback hpb
  have core := SDR3Coact_pushout_bijective (Λ := Λ) hP
    (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv
    (Scheme.ΓSpecIso (.of (AddMonoidAlgebra A Λ))).symm.commRingCatIsoToRingEquiv
    (fun x => (congrArg (fun k => k.hom x)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (AddMonoidAlgebra.singleZeroRingHom : A →+* AddMonoidAlgebra A Λ)))))
    (SDR3Coact_chi ((π ⁻¹ᵁ U).ι ≫ g)) (fun d => rfl)
  have hconj : ∀ a, SDR3Coact_φ π (SDR3Coact_chi g) U
      (AddMonoidAlgebra.mapRingHom Λ (Scheme.Opens.topIso U).hom.hom a) =
      (Scheme.Opens.topIso (π ⁻¹ᵁ U)).hom.hom
        (SDR3Coact_lift (π ∣_ U).appTop.hom (SDR3Coact_chi ((π ⁻¹ᵁ U).ι ≫ g)) a) := by
    intro a
    induction a using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single d r =>
      rw [AddMonoidAlgebra.mapRingHom_single, SDR3Coact_φ_single, SDR3Coact_lift_single, map_mul]
      congr 1
      · exact (congrArg (fun k => k.hom r) (SDR3Coact_restrict_top π U)).symm
      · refine Eq.symm ?_
        exact SDR3Coact_ι_top (π ⁻¹ᵁ U) _
  have he2 := (ConcreteCategory.isIso_iff_bijective _).1
    (inferInstance : IsIso (Scheme.Opens.topIso (π ⁻¹ᵁ U)).hom)
  have hm := SDR3Coact_map_bijective (Λ := Λ) (Scheme.Opens.topIso U)
  have hcomp : (SDR3Coact_φ π (SDR3Coact_chi g) U) ∘ (AddMonoidAlgebra.mapRingHom Λ (Scheme.Opens.topIso U).hom.hom) =
      (Scheme.Opens.topIso (π ⁻¹ᵁ U)).hom.hom ∘
        (SDR3Coact_lift (π ∣_ U).appTop.hom (SDR3Coact_chi ((π ⁻¹ᵁ U).ι ≫ g))) := funext hconj
  have hb : Function.Bijective ((SDR3Coact_φ π (SDR3Coact_chi g) U) ∘
      (AddMonoidAlgebra.mapRingHom Λ (Scheme.Opens.topIso U).hom.hom)) := by
    rw [hcomp]; exact Function.Bijective.comp he2 core
  exact (Function.Bijective.of_comp_iff _ hm).1 hb

/-- `SDR3Coact_φ` on the whole scheme is the map on global sections. -/
lemma SDR3Coact_φ_top (π : Y ⟶ Z) (χ : Multiplicative Λ →* Γ(Y, ⊤)) (a : AddMonoidAlgebra Γ(Z, ⊤) Λ) :
    SDR3Coact_φ π χ ⊤ a = SDR3Coact_lift π.appTop.hom χ a := by
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | add a b ha hb => exact (map_add _ _ _).trans ((congrArg₂ _ ha hb).trans (map_add _ _ _).symm)
  | single d r =>
    rw [SDR3Coact_φ_single, SDR3Coact_lift_single]
    congr 1
    have : Y.presheaf.map (homOfLE (le_top : π ⁻¹ᵁ (⊤ : Z.Opens) ≤ ⊤)).op = 𝟙 _ := by
      exact Y.presheaf.map_id _
    exact congrArg (fun k => k.hom (χ (Multiplicative.ofAdd d))) this

end AlgMag.SD

#print axioms AlgMag.SD.SDR3Coact_base_bijective
#print axioms AlgMag.SD.SDR3Coact_φ_top
