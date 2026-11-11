/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartS5Spec
import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationCancellation
import StacksFrontier.AlgebraicGeometry.Spaces.Category
import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.Representable

/-!
# `W → X` is locally of finite presentation

Stacks 05WT (`Space.isLocallyOfFinitePresentation_of_comp`): a map from `W` locally of finite
presentation over `S` to `X` locally of finite type over `S`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartS5

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- For a map from a representable, Stacks 03MJ for "locally of finite presentation". -/
private theorem lfp_iff_presheaf {U : BigFppfOver B S hS} {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : IsAlgebraicSpace B S hS G) (f : yoneda.obj U ⟶ G) :
    Space.IsLocallyOfFinitePresentation B S hS f ↔
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f :=
  have := Stacks.Descent.isLocalAtTarget_fppfPrecoverage
    (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
  Space.holdsOnEveryEtaleChart_iff_relative B S hS
    (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
    LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget
    (isAlgebraicSpace_yoneda B S hS U) hG f
    (Space.relativelyRepresentable_of_isAlgebraicSpace B S hS hG f)

/-- **`φ̃` is locally of finite presentation.** -/
theorem lfpp_of_cancellation {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXft : Space.IsLocallyOfFiniteType B S hS (toBase X)) {W : BigFppfOver B S hS}
    (hW : LocallyOfFinitePresentation W.hom.hom) (f : yoneda.obj W ⟶ X) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f := by
  have hWa := isAlgebraicSpace_yoneda B S hS W
  have hTa := isAlgebraicSpace_yoneda B S hS (siteTop (B := B) (S := S) (hS := hS))
  have hcomp : f ≫ toBase X = yoneda.map (Over.mkIdTerminal.from W) := by
    ext T z
    exact Over.mkIdTerminal.hom_ext _ _
  have hfg : Space.IsLocallyOfFinitePresentation B S hS (f ≫ toBase X) := by
    rw [hcomp]
    refine (lfp_iff_presheaf hTa _).2 ?_
    refine Space.presheaf_yoneda_map_of_inverseImage B S hS inferInstance _ ?_
    change LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (Over.mkIdTerminal.from W))
    have e : (BigFppfOver.toScheme B S hS).map (Over.mkIdTerminal.from W) = W.hom.hom :=
      (Category.comp_id _).symm.trans (congrArg (fun z => z.hom) (Over.w (Over.mkIdTerminal.from W)))
    rw [e]
    exact hW
  exact (lfp_iff_presheaf hX f).1
    (Space.isLocallyOfFinitePresentation_of_comp B S hS hWa hX hTa f (toBase X) hfg hXft)

/-- `Spec R' → S` is locally of finite presentation, if `Γ(S) → R'` is. -/
theorem lfp_rObj [hSa : IsAffine S] {R' : Type u} [CommRing R']
    (ρ : RT (siteTop (B := B) (S := S) (hS := hS)) →+* R') (hC : B.Contains (Spec (.of R')))
    (hρ : ρ.FinitePresentation) : LocallyOfFinitePresentation (rObj ρ hC).hom.hom := by
  have h1 : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom ρ)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).2 hρ
  have e : (rObj ρ hC).hom.hom = Spec.map (CommRingCat.ofHom ρ) ≫
      ((BigFppfOver.toScheme B S hS).obj (siteTop (B := B) (S := S) (hS := hS))).isoSpec.inv ≫ 𝟙 S := rfl
  have e2 : (rObj ρ hC).hom.hom = Spec.map (CommRingCat.ofHom ρ) ≫
      ((BigFppfOver.toScheme B S hS).obj (siteTop (B := B) (S := S) (hS := hS))).isoSpec.inv :=
    e.trans (congrArg (Spec.map (CommRingCat.ofHom ρ) ≫ ·) (Category.comp_id _))
  rw [e2]
  exact MorphismProperty.comp_mem (@LocallyOfFinitePresentation.{u}) _ _ h1
    (by change LocallyOfFinitePresentation _; infer_instance)

end AlgMag.ChartS5

#print axioms AlgMag.ChartS5.lfpp_of_cancellation
#print axioms AlgMag.ChartS5.lfp_rObj
