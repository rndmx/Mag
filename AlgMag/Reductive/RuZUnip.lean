/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.T2Classical

/-!
# `RuZUnip` (proved)

`R_u(Z(μ))`, pulled back to `G` along `H → H/Z(μ)`, is geometrically connected, smooth and
unipotent: the quotient `H / Ru (Z μ)` is isomorphic (`quotientIsoOfSurjective`) to
`(H/Z(μ)) / R_u`, which has these properties by
`isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal`.
-/

open Magnetism TauCeti TauCeti.Cocharacter CategoryTheory

namespace AlgMag.Reductive.RuZUnipProof

open AlgMag.Reductive AlgMag.Reductive.BorelRoute AlgMag.Reductive.BorelRouteReal
  AlgMag.Reductive.T2Classical

universe u

variable {k : Type u} {H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]

local notation "Hf" => FiniteTypeCommHopfAlgCat.of k H

/-- Transport: for any `S`, `V(Ru S) ⊆ G` is geometrically connected, smooth, unipotent. -/
theorem ru_unip (S : HopfIdeal k H) :
    geometricallyConnectedCommHopfAlgProperty k
        (FiniteTypeCommHopfAlgCat.quotient Hf (Ru S)).obj ∧
      smoothUnipotentCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient Hf (Ru S)) := by
  have hc := FiniteTypeCommHopfAlgCat.isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal
    (FiniteTypeCommHopfAlgCat.quotient Hf S)
  let e := (FiniteTypeCommHopfAlgCat.mkQuotient Hf S).hom.quotientIsoOfSurjective
    (CommHopfAlgCat.mkQuotient_surjective _ _)
    (FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal
      (FiniteTypeCommHopfAlgCat.quotient Hf S))
  exact ⟨(geometricallyConnectedCommHopfAlgProperty k).prop_of_iso e.symm hc.2.1,
    (smoothCommHopfAlgProperty k ⊓ geometricallyUnipotentPointsCommHopfAlgProperty k).prop_of_iso
      e.symm hc.2.2⟩

theorem ruZUnip (μ : H →ₐc[k] LaurentPolynomial k) : RuZUnip (k := k) (H := H) μ :=
  ru_unip (Z μ)

end AlgMag.Reductive.RuZUnipProof

#print axioms AlgMag.Reductive.RuZUnipProof.ruZUnip
