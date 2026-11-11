/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec15Final

/-!
# Remark 15.8 of *Algebraic Magnetism*, with Conjecture 6.9 (ii) as printed

`AlgMag.Conj69ii` of `Sec15General` is stronger than the printed Conjecture 6.9 (ii): it has no
hypothesis that `X` is quasi-compact over `S`, and asks limit preservation and charts of finite type
in place of locally of finite presentation. Here `Conj69iiPrinted` is the printed statement, and
`rem158_printed` deduces the conclusion of Theorem 15.4 for `X` finitely presented, separated. `S` is
quasi-compact, as Theorem 15.4 requires (see `Sec15General`).
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.Leftover

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (M : Type u) [AddCommGroup M]

/-- **Conjecture 6.9 (ii)**, as printed: a separated algebraic space, locally of finite presentation
and quasi-compact over `S`, with an action of `D(M)_S`, has an `S`-affine strongly-FPR atlas. This is a
statement, not a theorem. -/
def Conj69iiPrinted : Prop :=
  ∀ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (aX : AAction (fppfO B S hS) M X),
    IsAlgebraicSpace B S hS X → IsSeparatedOver X →
    Space.IsLocallyOfFinitePresentation B S hS (terminal.from X) →
    Space.IsQuasiCompactSpace B S hS X →
    ∃ (U : BigFppfOver B S hS) (_ : IsAffineHom U.hom.hom)
      (aU : AAction (fppfO B S hS) M (yoneda.obj U)) (f : yoneda.obj U ⟶ X),
      IsStronglyFPRAtlas aU aX f

/-- **Conjecture 15.7**, as printed, for `S` quasi-compact: the conclusion of Theorem 15.4 holds for
every separated `X` finitely presented over `S`. This is a statement, not a theorem. -/
def Conj157Printed : Prop :=
  ∀ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (aX : AAction (fppfO B S hS) M X),
    IsAlgebraicSpace B S hS X → IsSeparatedOver X →
    Space.IsLocallyOfFinitePresentation B S hS (terminal.from X) →
    Space.IsQuasiCompactSpace B S hS X →
    (pureMagnets (attractorImage aX)).Finite

/-- **Remark 15.8.** Conjecture 6.9 implies Conjecture 15.7, with `M` finitely generated (assumed in
Conjecture 6.9) and `S` quasi-compact. -/
theorem rem158_printed [AddMonoid.FG M] [CompactSpace S] (hc : Conj69iiPrinted B S hS M) :
    Conj157Printed B S hS M := by
  intro X aX hX hsep hfp hq
  obtain ⟨U, hU, aU, f, hat⟩ := hc X aX hX hsep hfp hq
  exact (thm154_ii_lfp hat hX hsep hfp).1

end AlgMag.Leftover

#print axioms AlgMag.Leftover.rem158_printed
