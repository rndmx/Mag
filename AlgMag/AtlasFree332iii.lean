/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SepProp33
import AlgMag.FinalNonQCLocal

/-!
# Proposition 3.32 (iii) and Fact 3.34 (iii) without atlas

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, §3. `M` a monoid embedded by `f` in a finitely
generated abelian group `Z`. The reductions `prop332_iii_of`, `fact334_iii_of` to the induced `Z`-action, with the
`Z`-statements `exists_inf_of_bi_weak` (atlas of `thm68_atlas` via `existsZFPRAtlas_nonqc`) and `fact334_general`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.AtlasFree332iii

open AlgMag.Final AlgMag.SepProp33

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

variable {M Z : Type u} [AddCommMonoid M] [AddCommGroup Z] [AddMonoid.FG Z]
  {f : M →+ Z} (hf : Function.Injective f)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {aX : AAction (fppfO B S hS) M X}
  (hZ : B.Contains (⊤_ Scheme.{u}))

include hf hZ in
/-- **Proposition 3.32 (iii)**, no atlas: `X` a separated algebraic space locally of finite presentation over a separated `S`,
not necessarily quasi-compact; `f : M → Z` injective, `Z` a finitely generated abelian group; `N`, `L` arbitrary magnets of `M`. -/
theorem prop332_iii_free [S.IsSeparated] (hM : B.Contains (Spec (ZMon Z)))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (N L : AddSubmonoid M) (T : BigFppfOver B S hS) :
    Function.Bijective fun χ : AttractorPt aX (N ⊓ L) T =>
      (iterEquivBi T).symm (χ.toBi (K := N ⊓ L) (P := N.prod L) (hKinf' N L)) :=
  haveI : AddGroup.FG Z := AddGroup.fg_iff_addMonoid_fg.mpr inferInstance
  prop332_iii_of hf hX (isSeparatedOver_iff_space.1 hsep) (fun φ =>
    exists_inf_of_bi_weak hX (isSeparatedOver_iff_space.1 hsep)
      (existsZFPRAtlas_nonqc hZ hM hX hsep hfp (actAlong f aX) _)
      (Or.inr (isLimitPreserving_of_lfp hX hfp)) φ) T

include hf hZ in
/-- **Fact 3.34 (iii)**, no atlas, arbitrary nonempty family: `X` a separated algebraic space locally of finite presentation,
not necessarily quasi-compact, `S` arbitrary; `f : M → Z` injective, `Z` a finitely generated abelian group. -/
theorem fact334_iii_free (hM : B.Contains (Spec (ZMon Z)))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    {s : Set (AddSubmonoid M)} (hne : s.Nonempty) (y)
    (hy : ∀ N ∈ s, attractorImage aX N = y) : attractorImage aX (sInf s) = y :=
  haveI : AddGroup.FG Z := AddGroup.fg_iff_addMonoid_fg.mpr inferInstance
  fact334_iii_of hf hX (isSeparatedOver_iff_space.1 hsep) hne y hy fun h =>
    fact334_general hZ hM hX hsep hfp (actAlong f aX) y (hne.image _) h

end AlgMag.AtlasFree332iii

#print axioms AlgMag.AtlasFree332iii.prop332_iii_free
#print axioms AlgMag.AtlasFree332iii.fact334_iii_free
