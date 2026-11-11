/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.TangentRoots
import AlgMag.Reductive.OpenCellConnected
import AlgMag.Reductive.OpenCellPoints

/-!
# Proposition 16.10 (ii) from the open cell

The open cell of a cocharacter `λ` is the multiplication morphism
`U(-λ) × Z(λ) × U(λ) → G`; on coordinate rings it is
`openCellMap λ : O(G) → (O(U(-λ)) ⊗ O(Z(λ))) ⊗ O(U(λ))`, the double comultiplication followed
by the three quotient maps. On points it is the multiplication `(u, z, v) ↦ u z v`, which is
injective (`TauCeti.Cocharacter.mul_injective_openCell`).

If `G` is irreducible and the open cell is an open embedding (CGP Proposition 2.1.8 (3)), then
`Z(λ)` is irreducible, hence connected (`AlgMag.Reductive.connectedSpace_of_isOpenEmbedding_tensor`),
and Proposition 16.10 (ii) over an algebraically closed field follows with no connectedness input
on the Levi subgroup.
-/

suppress_compilation

open Magnetism TauCeti TauCeti.Cocharacter
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]

/-- The quotient by a Hopf ideal is nonzero. -/
lemma nontrivial_quotient_hopfIdeal (I : HopfIdeal k H) : Nontrivial (H ⧸ I.toIdeal) := by
  refine Ideal.Quotient.nontrivial_iff.mpr fun h => ?_
  have h1 : (1 : H) ∈ I.toIdeal := h ▸ Submodule.mem_top
  have := I.counit_eq_zero h1
  rw [Bialgebra.counit_one] at this
  exact one_ne_zero this

/-- The coordinate ring `O(U(-λ)) ⊗ O(Z(λ)) ⊗ O(U(λ))` of the open cell. -/
abbrev OpenCellRing (l : H →ₐc[k] LaurentPolynomial k) : Type u :=
  ((H ⧸ l.oppositeCocharacter.unipotentDefiningHopfIdeal.toIdeal) ⊗[k]
      (H ⧸ (leviDefiningHopfIdeal l).toIdeal)) ⊗[k] (H ⧸ l.unipotentDefiningHopfIdeal.toIdeal)

/-- The coordinate map of the open cell `U(-λ) × Z(λ) × U(λ) → G`. -/
def openCellMap (l : H →ₐc[k] LaurentPolynomial k) : H →ₐ[k] OpenCellRing l :=
  (Algebra.TensorProduct.map
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k _) (Ideal.Quotient.mkₐ k _))
      (Ideal.Quotient.mkₐ k _)).comp
    ((Algebra.TensorProduct.map (Bialgebra.comulAlgHom k H) (AlgHom.id k H)).comp
      (Bialgebra.comulAlgHom k H))

/-- `openCellMap` as a ring homomorphism between commutative rings. -/
def openCellRingHom (l : H →ₐc[k] LaurentPolynomial k) : H →+* OpenCellRing l :=
  (openCellMap l).toRingHom

/-- **The Levi subgroup is connected if the open cell is an open embedding** into an
irreducible `G`. -/
theorem connectedSpace_levi_of_openCell [IrreducibleSpace (PrimeSpectrum H)]
    (l : H →ₐc[k] LaurentPolynomial k)
    (hΩ : Topology.IsOpenEmbedding
      (PrimeSpectrum.comap (R := H) (S := OpenCellRing l) (openCellRingHom l))) :
    ConnectedSpace (PrimeSpectrum (H ⧸ (leviDefiningHopfIdeal l).toIdeal)) := by
  have := nontrivial_quotient_hopfIdeal l.oppositeCocharacter.unipotentDefiningHopfIdeal
  have := nontrivial_quotient_hopfIdeal (leviDefiningHopfIdeal l)
  have := nontrivial_quotient_hopfIdeal l.unipotentDefiningHopfIdeal
  exact connectedSpace_of_isOpenEmbedding_tensor (k := k) _ hΩ

/-- **Proposition 16.10 (ii) of Algebraic Magnetism, `k` algebraically closed, from the open
cell.** Let `G` be smooth and irreducible over `k = k̄` with an action of `D(X)`, `Φ` the roots,
`f` a magnet map and `N ⊆ f⁻¹(ℕ)` with `N ∩ Φ = f⁻¹(ℕ) ∩ Φ`. If the open cell of `λ_f` is an
open embedding, then `G^N = P(λ_f)`. -/
theorem magnetIdeal_eq_parabolic_of_openCell {X : Type u} [CommGroup X] [DecidableEq X]
    [IsAlgClosed k] [Algebra.Smooth k H] [IrreducibleSpace (PrimeSpectrum H)]
    (π : H →ₐc[k] MonoidAlgebra k X) (ψ : X →* Multiplicative ℤ)
    {N : Magnet (Additive X)} (hN : N ≤ natMagnet.comap (pairingHom ψ))
    (hΦ : {α | α ∈ N} ∩ roots π = {α | α ∈ natMagnet.comap (pairingHom ψ)} ∩ roots π)
    (hΩ : Topology.IsOpenEmbedding
      (PrimeSpectrum.comap
        (R := H) (S := OpenCellRing (π.cocharacter ψ)) (openCellRingHom (π.cocharacter ψ)))) :
    magnetIdeal (torusGrading π) N =
      (parabolicDefiningHopfIdeal (π.cocharacter ψ)).toIdeal := by
  refine magnetIdeal_eq_parabolic_of_connected_levi π ψ hN
    ((tangentWeights_condition_iff_roots ψ N).2 fun χ hχ => ?_)
    (connectedSpace_levi_of_openCell _ hΩ)
  have := congrArg (χ ∈ ·) hΦ
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hχ, and_true, eq_iff_iff] at this
  exact this

end AlgMag.Reductive
