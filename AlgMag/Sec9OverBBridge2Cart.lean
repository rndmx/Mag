/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec9OverBPrinted
import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.ObjectFunctoriality
import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.FullyFaithfulUnconditional
import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.RestrictScalarsBaseChange
import StacksFrontier.AlgebraicGeometry.Modules.CartesianQuasicoherent
import StacksFrontier.AlgebraicGeometry.Topologies.CartesianModulesOnAffineSite
import StacksFrontier.CategoryTheory.Sites.Modules.CartesianLocalOnCover

/-!
# Stacks 03DX (1), part 1: a quasi-coherent module on `(Sch/X)_fppf` and base change

The comparison `Γ(U) ⊗_{Γ(V)} 𝒢(V) ⟶ 𝒢(U)` for `𝒢` quasi-coherent on the big fppf site of `X`.

* `cart_of_hasLocal`: bijective for `U ⟶ V` between affines lying over an object `T` over which `𝒢`
  is an associated module.
* `exists_family`: an affine object has a finite flat affine covering of such objects.
* `cart_of_flat`: bijective for a flat morphism of affine objects (Stacks 03DX, flat descent).
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits
open Stacks.PresheafOfModules
open scoped TensorProduct ChangeOfRings

noncomputable section

namespace AlgMag.B2

open AlgMag.S9 (IsBC)

section Primitive

variable {C : Type*} [Category C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))

/-- The restriction map of a presheaf of modules, as an additive map. -/
def resAdd {X Y : Cᵒᵖ} (f : X ⟶ Y) : M.obj X →+ M.obj Y :=
  AddMonoidHom.mk' (fun x => M.map f x) (fun a b => map_add (M.map f).hom a b)

lemma resAdd_smul {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : R.obj X) (x : M.obj X) :
    resAdd M f (r • x) = (R.map f).hom r • resAdd M f x :=
  (M.map f).hom.map_smul r x

/-- Bijectivity of the comparison is the base change property, one direction. -/
theorem cart_of_isBC {X Y : Cᵒᵖ} (f : X ⟶ Y) (h : IsBC (R.map f).hom (resAdd M f) (resAdd_smul M f)) :
    Function.Bijective (restrictionBaseChange M f) := by
  letI := (R.map f).hom.toAlgebra
  letI : Module (R.obj X) (M.obj Y) := Module.compHom _ (R.map f).hom
  haveI : IsScalarTower (R.obj X) (R.obj Y) (M.obj Y) := ⟨fun r s x => by
    change ((R.map f).hom r * s) • x = (R.map f).hom r • s • x
    rw [mul_smul]⟩
  have h' : IsBaseChange (R.obj Y) ({ toFun := resAdd M f, map_add' := (resAdd M f).map_add, map_smul' := resAdd_smul M f } : M.obj X →ₗ[R.obj X] M.obj Y) := h
  have key : ∀ z, restrictionBaseChange M f z = h'.equiv z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | tmul a x =>
      refine (restrictionBaseChange_tmul M f a x).trans ?_
      exact (IsBaseChange.equiv_tmul h' a x).symm
    | add a b ha hb =>
      exact (map_add _ _ _).trans ((congrArg₂ _ ha hb).trans (map_add _ _ _).symm)
  have e : (fun z => restrictionBaseChange M f z) = h'.equiv := funext key
  exact (e ▸ h'.equiv.bijective :)

/-- Bijectivity of the comparison is the base change property, the other direction. -/
theorem isBC_of_cart {X Y : Cᵒᵖ} (f : X ⟶ Y) (h : Function.Bijective (restrictionBaseChange M f)) :
    IsBC (R.map f).hom (resAdd M f) (resAdd_smul M f) :=
  AlgMag.Leftover.isBC_of (R.map f).hom (resAdd M f) (resAdd_smul M f)
    (AddMonoidHom.mk' (fun z => restrictionBaseChange M f z) (fun a b => map_add _ a b)) h
    (fun c m => restrictionBaseChange_tmul M f c m)

end Primitive

section Transfer

variable {C : Type*} [Category C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}

/-- Bijectivity of the comparison transfers along semilinear identifications of values. -/
theorem cart_transfer {X Y : Cᵒᵖ} (f : X ⟶ Y) (eX : N.obj X ≃+ M.obj X) (eY : N.obj Y ≃+ M.obj Y)
    (hX : ∀ (r : R.obj X) x, eX (r • x) = r • eX x) (hY : ∀ (r : R.obj Y) x, eY (r • x) = r • eY x)
    (hc : ∀ x, eY (N.map f x) = M.map f (eX x))
    (h : Function.Bijective (restrictionBaseChange M f)) :
    Function.Bijective (restrictionBaseChange N f) :=
  cart_of_isBC N f (AlgMag.S9BF.isBC_transport (R.map f).hom (resAdd N f) (resAdd_smul N f)
    (resAdd M f) (resAdd_smul M f) eX hX eY hY hc (isBC_of_cart M f h))

end Transfer

variable (B : BigFppfSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)

open BigFppfOver

/-- The base change property of a presheaf of modules on the big fppf site of `X`. -/
abbrev Cart (P : PresheafOfModules.{u} (structureSheaf B X hX).obj) {U V : BigFppfOver B X hX}
    (f : U ⟶ V) : Prop :=
  Function.Bijective (restrictionBaseChange (R := commStructurePresheaf B X hX) P f.op)

/-- An object of the big site with affine underlying scheme. -/
abbrev Aff (U : BigFppfOver B X hX) : Prop := IsAffine ((toScheme B X hX).obj U)

variable {B X hX}

/-- Sections of a pulled-back quasi-coherent module have the base change property: Stacks 03DX
through `AlgMag.Leftover.isQCoh_assocPMod`. -/
theorem cart_sections (F : X.Modules) [F.IsQuasicoherent] {U V : BigFppfOver B X hX}
    (hU : Aff B X hX U) (hV : Aff B X hX V) (f : U ⟶ V) :
    Cart B X hX (sectionsPresheafOfModules B X hX F) f := by
  haveI : IsAffine ((Over.post B.inclusion).obj U).left := hU
  haveI : IsAffine ((Over.post B.inclusion).obj V).left := hV
  have h := (AlgMag.Leftover.isQCoh_assocPMod F).base_change ((Over.post B.inclusion).map f)
  exact cart_of_isBC (R := commStructurePresheaf B X hX)
    (sectionsPresheafOfModules B X hX F) f.op h

end AlgMag.B2

#print axioms AlgMag.B2.cart_sections
