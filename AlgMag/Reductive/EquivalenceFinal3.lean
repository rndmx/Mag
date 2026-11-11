/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.EquivalenceFinal2
import AlgMag.Reductive.Step2BaseChange

/-!
# (⇒) without `Step2OverFpBar`

`condI_condII_condIII_of_reductive_final3`: `condI_condII_condIII_of_reductive_final2` with the
input `hFp` discharged by `Step2BaseChange.step2OverFpBar`. Remaining inputs: `hBruhat`,
`hBorMax`.
-/

set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory Magnetism TauCeti TauCeti.Comodule WithConv AlgMag.Weyl
  TauCeti.Cocharacter

universe u

namespace AlgMag.Reductive

open R1Opp R1Build R1Dis Final2

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable [Algebra.FiniteType k H]

/-- **(⇒) assembled, version 3**: as `condI_condII_condIII_of_reductive_final2`, without `hFp`. -/
theorem condI_condII_condIII_of_reductive_final3 [Module.IsTorsionFree ℤ (Additive X)]
    (π : H →ₐc[k] MonoidAlgebra k X)
    (hπ : Function.Surjective π)
    (hT : HopfIdeal.IsMaximalTorus k (CommHopfAlgCat.of k H) (HopfIdeal.kerOfSurjective π hπ))
    (hred : reductiveCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.of k H))
    (hBruhat : letI : Algebra.Smooth k H := hred.smooth
      haveI : IsMulTorsionFree X := ⟨fun n hn =>
        (IsAddTorsionFree.of_isTorsionFree ℤ (Additive X)).nsmul_right_injective hn⟩
      ∀ (ψ : X →* Multiplicative ℤ) (α : Additive X) (hα : 0 < pairingHom ψ α),
        α ∈ roots π → BruhatRayCore π ψ α hα)
    (hBorMax : letI : Algebra.Smooth k H := hred.smooth
      ∀ δ : Additive X, δ ≠ 0 →
        (∀ β ∈ roots π, (∃ m n : ℤ, n ≠ 0 ∧ n • β = m • δ) → β ∈ lineMagnet δ) →
        ∃ ψ : X →* Multiplicative ℤ, pairingHom ψ δ ≠ 0 ∧ BorelZMax π δ ψ) :
    CondI π ∧ CondII π ∧ CondIII π :=
  condI_condII_condIII_of_reductive_final2 π hπ hT hred hBruhat
    Step2BaseChange.step2OverFpBar hBorMax

end AlgMag.Reductive

#print axioms AlgMag.Reductive.condI_condII_condIII_of_reductive_final3
