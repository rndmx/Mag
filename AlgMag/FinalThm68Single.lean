/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartFinalSpaces

/-!
# Theorem 6.8 (i): a single atlas for `X` not quasi-compact, under the size cutoff

`thm68_family_spaces` gives an atlas for each coproduct of the charts lying in the site. The site `B` is a cutoff: the
hypothesis `hco`, that the coproducts of families of `B`-objects indexed by `Type u` stay in the site, is the only addition.
The atlas is `S`-affine in the sense of Definition 6.1, a disjoint union of `S`-affine schemes.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.Final

open AlgMag.ChartAssembly

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  [AddGroup.FG M] (hZ : B.Contains (⊤_ Scheme.{u}))

include hZ in
/-- **Theorem 6.8 (i)**, single atlas, `X` separated and locally of finite presentation, not necessarily quasi-compact,
with coproducts in the site. -/
theorem thm68_single [S.IsSeparated]
    (hco : ∀ (A : Type u) (U : A → BigFppfOver B S hS),
      ∃ (V : BigFppfOver B S hS) (j : ∀ a, U a ⟶ V), Nonempty (IsColimit (Cofan.mk V j)))
    (hM : B.Contains (Spec (ZMon M))) (hX : IsAlgebraicSpace B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (LimThm.toT1 X))
    (hsep : Space.IsSeparatedOver B S hS X) (act : AAction (fppfO B S hS) M X) :
    ∃ (V : BigFppfOver B S hS) (actV : AAction (fppfO B S hS) M (yoneda.obj V)) (v : yoneda.obj V ⟶ X),
      IsStronglyFPRAtlas actV act v ∧ ∀ Z : AddSubgroup M, IsZFPRAtlas actV act v Z := by
  obtain ⟨A, U, L, -, -, h⟩ := thm68_family_spaces hZ hM hX hlfp hsep act
  obtain ⟨V, j, ⟨hV⟩⟩ := hco A U
  obtain ⟨v, h1, h2⟩ := h V j hV
  exact ⟨V, _, v, h1, h2⟩

end AlgMag.Final

#print axioms AlgMag.Final.thm68_single
