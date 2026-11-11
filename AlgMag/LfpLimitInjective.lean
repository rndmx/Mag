/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.LimitPreservingFunctorOfPoints

/-!
# Injectivity half of limit preservation for algebraic spaces locally of finite presentation

Stacks Tags 049J / 05N0 (`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_terminal_iff_limitPreserving`)
give `X(lim W_i) = colim X(W_i)` for a cofiltered system of affine objects; the colimit is filtered, so two
sections over `W_i` with the same image over the limit already agree over some `W_j → W_i`
(`Types.FilteredColimit.isColimit_eq_iff'`).
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.LfpLim

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Injectivity half of Tag 01ZC for spaces.** `X` an algebraic space locally of finite presentation
over `S`, `W = lim W_i` a cofiltered limit of affine objects of the site (limit of schemes), `W` affine.
Two sections of `X` over `W_i` which agree over `W` agree over some `W_j → W_i`. -/
theorem exists_eq_of_limit {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ BigFppfOver B S hS) (c : Cone D)
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (hD : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj i)))
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt))
    {i : I} (x y : X.obj (op (D.obj i))) (h : X.map (c.π.app i).op x = X.map (c.π.app i).op y) :
    ∃ (j : I) (f : j ⟶ i), X.map (D.map f).op x = X.map (D.map f).op y := by
  have hL := (Space.isLocallyOfFinitePresentation_terminal_iff_limitPreserving B S hS hX).1 hfp
  obtain ⟨hcol⟩ := hL I D c hc hD hW
  obtain ⟨j, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' hcol (i := op i) x y).1 h
  exact ⟨j.unop, f.unop, hf⟩

end AlgMag.LfpLim

#print axioms AlgMag.LfpLim.exists_eq_of_limit
