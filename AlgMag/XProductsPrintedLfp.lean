/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.XProductsPrinted
import AlgMag.SpacesLimitA1

/-!
# Theorem 4.1 with the literal hypotheses over `S = Spec ℤ`

Mayeux, *Algebraic magnetism: X-products of attractors via F₁-geometry*, Theorem 4.1. Separate from
`AlgMag.XProductsPrinted` since `AlgMag.SpacesLimitA1` is not in the default target of `AlgMag.lean`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

set_option linter.unusedSectionVars false

namespace AlgMag.XP

open GB

section OverZ

variable {B : BigFppfSite.{u}} {hS : B.Contains (⊤_ Scheme.{u})}
variable {M : Type u} [AddCommGroup M] [AddGroup.FG M]
  {X : (BigFppfOver B (⊤_ Scheme.{u}) hS)ᵒᵖ ⥤ Type u}
  (act : AAction (fppfO B (⊤_ Scheme.{u}) hS) M X)
variable {A : Type u} (𝓝 : MagnetFamily M A) [Nonempty A]

/-- `S = Spec ℤ` is locally noetherian. -/
instance : IsLocallyNoetherian (⊤_ Scheme.{u}) :=
  have : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  have : IsLocallyNoetherian (Spec (.of (ULift.{u} ℤ))) := inferInstance
  isLocallyNoetherian_of_isOpenImmersion
    (terminalIsTerminal.uniqueUpToIso specULiftZIsTerminal.{u}).hom

/-- **Theorem 4.1** over `S = Spec ℤ`, the base of §4 of the paper, with exactly the printed conditions. -/
noncomputable def thm41PrintedZ (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hS X)
    (h : (Space.IsQuasiSeparated B (⊤_ Scheme.{u}) hS (LimThm.toT1 X) ∧
        Space.IsLocallyOfFinitePresentation B (⊤_ Scheme.{u}) hS (LimThm.toT1 X) ∧
        AppR.ConnectedFibres (M ⧸ 𝓝.Z) (⊤_ Scheme.{u})) ∨ IsSeparatedOver X)
    (T : BigFppfOver B (⊤_ Scheme.{u}) hS) :
    XNPt 𝓝 (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hS) act T ≃
      XProdPt 𝓝 (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hS) act T :=
  thm41Printed act 𝓝 hX (h.imp (fun h' => ⟨inferInstance, LimThm.chartsOfFiniteType_of_lfp h'.2.1, h'.2.2⟩) id) T

end OverZ

end AlgMag.XP

#print axioms AlgMag.XP.thm41PrintedZ
