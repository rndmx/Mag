/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SecLeftover158

/-!
# Remark 15.8 of *Algebraic Magnetism*, with `X` quasi-compact over `S`

Printed Conjecture 6.9 (ii) reads "If `X/S` is quasi-compact". `Conj69iiPrinted` of `SecLeftover158` uses
absolute quasi-compactness. Here `Conj69iiRel`, `Conj157Rel` use the relative notion. `S` quasi-compact and
`M` finitely generated are as in `rem158_printed`: the first is required by Theorem 15.4 (see `Sec15General`),
the second is assumed by Conjecture 6.9.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.Final

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (M : Type u) [AddCommGroup M]

/-- **Conjecture 6.9 (ii)**, as printed, `X` quasi-compact over `S`. A statement, not a theorem. -/
def Conj69iiRel : Prop :=
  ∀ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (aX : AAction (fppfO B S hS) M X),
    IsAlgebraicSpace B S hS X → IsSeparatedOver X →
    Space.IsLocallyOfFinitePresentation B S hS (terminal.from X) →
    Space.IsQuasiCompact B S hS (terminal.from X) →
    ∃ (U : BigFppfOver B S hS) (_ : IsAffineHom U.hom.hom)
      (aU : AAction (fppfO B S hS) M (yoneda.obj U)) (f : yoneda.obj U ⟶ X),
      IsStronglyFPRAtlas aU aX f

/-- **Conjecture 15.7**, as printed: the conclusion of Theorem 15.4 for `X` separated, finitely presented
over `S`. A statement, not a theorem. -/
def Conj157Rel : Prop :=
  ∀ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (aX : AAction (fppfO B S hS) M X),
    IsAlgebraicSpace B S hS X → IsSeparatedOver X →
    Space.IsLocallyOfFinitePresentation B S hS (terminal.from X) →
    Space.IsQuasiCompact B S hS (terminal.from X) →
    (pureMagnets (attractorImage aX)).Finite

/-- **Remark 15.8.** Conjecture 6.9 implies Conjecture 15.7. -/
theorem rem158 [AddMonoid.FG M] [CompactSpace S] (hc : Conj69iiRel B S hS M) :
    Conj157Rel B S hS M := by
  intro X aX hX hsep hfp hq
  obtain ⟨U, hU, aU, f, hat⟩ := hc X aX hX hsep hfp hq
  exact (thm154_ii_lfp hat hX hsep hfp).1

end AlgMag.Final

#print axioms AlgMag.Final.rem158
