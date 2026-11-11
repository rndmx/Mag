/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.FinalNonQCAtlas
import AlgMag.StronglyFPRNoteThm

/-!
# Conjecture 6.9 of *Algebraic Magnetism*, for `S` separated

Clause (i) is `AlgMag.Final.thm68_atlas`. Clause (ii) is `AlgMag.StronglyFPRNote.thm11_2`, with `S` quasi-compact.
For `S` not separated the conjecture fails, see `AlgMag.Conj69.not_conj69_doubledPlane`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgMag.Conj69

open AlgMag.ChartAssembly LimThm

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Conjecture 6.9**, for `S` separated: `M` finitely generated, `X` a separated `S`-algebraic space locally of
finite presentation with an action of `D(M)_S`. (i) There is a strongly-FPR atlas. (ii) If `X/S` is quasi-compact and
`S` is quasi-compact, there is an `S`-affine strongly-FPR atlas. -/
theorem conj69_separated [S.IsSeparated] [AddGroup.FG M] (hZ : B.Contains (⊤_ Scheme.{u}))
    (hM : B.Contains (Spec (ZMon M))) (hX : IsAlgebraicSpace B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 X))
    (hsep : Space.IsSeparatedOver B S hS X) (act : AAction (fppfO B S hS) M X) :
    (∃ (V : BigFppfOver B S hS) (actV : AAction (fppfO B S hS) M (yoneda.obj V))
      (v : yoneda.obj V ⟶ X), IsStronglyFPRAtlas actV act v) ∧
    (Space.IsQuasiCompact B S hS (toT1 X) → CompactSpace S →
      ∃ (V : BigFppfOver B S hS) (actV : AAction (fppfO B S hS) M (yoneda.obj V))
        (v : yoneda.obj V ⟶ X), IsStronglyFPRAtlas actV act v ∧ IsSAffineAtlas actV act v) := by
  refine ⟨?_, fun hq hc => StronglyFPRNote.thm11_2 hZ hM hX hlfp hq hsep act⟩
  obtain ⟨V, actV, v, h, -⟩ := Final.thm68_atlas hZ hM hX hlfp hsep act
  exact ⟨V, actV, v, h⟩

end AlgMag.Conj69

#print axioms AlgMag.Conj69.conj69_separated
