/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import StacksFrontier.AlgebraicGeometry.Spaces.Basic
import AlgMag.Foundations

/-!
# Attractors of algebraic spaces

We specialize `AlgMag.Foundations` to the big fppf site of a scheme `S` and to an algebraic space
in the sense of the Stacks library (Tag 025Y).
-/

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace AlgMag

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The ring functor `T ↦ Γ(T, 𝒪_T)` on the big fppf site of `S`. -/
noncomputable def fppfO : (BigFppfOver B S hS)ᵒᵖ ⥤ CommRingCat.{u} :=
  (BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ

variable {B S hS} {M : Type*} [AddCommMonoid M]

/-- **Proposition 3.2** for an algebraic space `X` with an action of `𝔸(M)_S`: the attractor `X^N`
is an fppf sheaf. -/
theorem isSheaf_attractor_of_isAlgebraicSpace {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (act : AAction (fppfO B S hS) M X) (N : AddSubmonoid M) :
    Presieve.IsSheaf (BigFppfOver.topology B S hS) (attractor act N) :=
  isSheaf_attractor act N _ ((isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf)

end AlgMag
