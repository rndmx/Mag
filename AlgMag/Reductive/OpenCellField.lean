/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.OpenCellFlat

/-!
# Proposition 16.10 (ii) over a field from the open cell over `k̄`

Over any field `k`, with `K = k̄`: if `G_K` is irreducible and the open cell map of `λ_f` over
`K` is flat (then it is an open immersion, `isOpenEmbedding_openCell_of_flat`), the Levi subgroup
`Z(λ_f)` is geometrically connected, and Proposition 16.10 (ii) holds in its printed root form.
-/

suppress_compilation

open Magnetism TauCeti TauCeti.Cocharacter
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X) (ψ : X →* Multiplicative ℤ)

/-- **`Z(λ_f)` is geometrically connected** if `G_{k̄}` is irreducible and the open cell over
`k̄` is flat. -/
theorem connectedSpace_levi_baseChange_of_openCell [Algebra.Smooth k H]
    [IrreducibleSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k] H))]
    (hflat : RingHom.Flat (R := AlgebraicClosure k ⊗[k] H)
      (S := OpenCellRing ((torusBaseChange (AlgebraicClosure k) π).cocharacter ψ))
      (openCellRingHom ((torusBaseChange (AlgebraicClosure k) π).cocharacter ψ))) :
    ConnectedSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k]
      (H ⧸ (leviDefiningHopfIdeal (π.cocharacter ψ)).toIdeal))) := by
  let K := AlgebraicClosure k
  let πK := torusBaseChange K π
  have hZK := connectedSpace_levi_of_openCell (πK.cocharacter ψ)
    (isOpenEmbedding_openCell_of_flat _ hflat)
  rw [← magnetIdeal_torusGrading_comap_bot, magnetIdeal_baseChange K π _,
    magnetIdeal_torusGrading_comap_bot] at hZK
  exact (PrimeSpectrum.homeomorphOfRingEquiv
    (Algebra.TensorProduct.tensorQuotientEquiv (R := k) K H K _).toRingEquiv).connectedSpace_iff.mpr
    hZK

/-- **Proposition 16.10 (ii) of Algebraic Magnetism over a field, printed root form, from the
open cell.** `G` smooth over `k` with `G_{k̄}` irreducible, `Φ` the roots, `f` a magnet map,
`N ⊆ f⁻¹(ℕ)` with `N ∩ Φ = f⁻¹(ℕ) ∩ Φ`. If the open cell of `λ_f` over `k̄` is flat, then
`G^N = P(λ_f)`. -/
theorem magnetIdeal_eq_parabolic_of_field_of_openCell [Algebra.Smooth k H]
    [IrreducibleSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k] H))]
    {N : Magnet (Additive X)} (hN : N ≤ natMagnet.comap (pairingHom ψ))
    (hΦ : {α | α ∈ N} ∩ roots π = {α | α ∈ natMagnet.comap (pairingHom ψ)} ∩ roots π)
    (hflat : RingHom.Flat (R := AlgebraicClosure k ⊗[k] H)
      (S := OpenCellRing ((torusBaseChange (AlgebraicClosure k) π).cocharacter ψ))
      (openCellRingHom ((torusBaseChange (AlgebraicClosure k) π).cocharacter ψ))) :
    magnetIdeal (torusGrading π) N =
      (parabolicDefiningHopfIdeal (π.cocharacter ψ)).toIdeal :=
  magnetIdeal_eq_parabolic_of_field_of_levi_roots π ψ hN hΦ
    (connectedSpace_levi_baseChange_of_openCell π ψ hflat)

end AlgMag.Reductive
