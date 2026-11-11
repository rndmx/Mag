/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import AlgMag.Foundations

/-!
# Common preliminaries for `AlgMag.GeneralBase*`
-/

suppress_compilation

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.GB

/-- The presheaf of rings `T ↦ Γ(T, ⊤)` on schemes over `S`. -/
def overO (S : Scheme.{u}) : (Over S)ᵒᵖ ⥤ CommRingCat.{u} := (Over.forget S).op ⋙ Scheme.Γ

/-- Morphisms to an affine scheme: `Hom(T, Spec R) = Hom(R, Γ(T, ⊤))`. -/
def homSpecEquiv (T : Scheme.{u}) (R : CommRingCat.{u}) : (T ⟶ Spec R) ≃ (R ⟶ Γ(T, ⊤)) where
  toFun f := (Scheme.ΓSpecIso R).inv ≫ f.appTop
  invFun φ := T.toSpecΓ ≫ Spec.map φ
  left_inv f := by
    have := Scheme.toSpecΓ_naturality f
    simp only [Spec.map_comp, ← Category.assoc, ← this]
    rw [Category.assoc, ← ΓSpec.adjunction_unit_app, ]
    simp
  right_inv φ := by
    simp [Scheme.toSpecΓ_appTop]

lemma homSpecEquiv_comp {T T' : Scheme.{u}} (g : T' ⟶ T) {R : CommRingCat.{u}} (f : T ⟶ Spec R) :
    homSpecEquiv T' R (g ≫ f) = homSpecEquiv T R f ≫ g.appTop := by
  simp [homSpecEquiv]

lemma homSpecEquiv_map {T : Scheme.{u}} {R R' : CommRingCat.{u}} (ψ : R ⟶ R') (f : T ⟶ Spec R') :
    homSpecEquiv T R (f ≫ Spec.map ψ) = ψ ≫ homSpecEquiv T R' f := by
  simp only [homSpecEquiv, Equiv.coe_fn_mk, Scheme.Hom.comp_appTop]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  exact (Scheme.ΓSpecIso_inv_naturality ψ).symm

end AlgMag.GB
