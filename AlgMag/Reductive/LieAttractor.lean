/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.AttractorSubgroup
import AlgMag.Reductive.PushCocharacter
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Tangent

/-!
# The Lie algebra of a torus attractor (Proposition 16.4 of Algebraic Magnetism, Hopf form)

For the conjugation action of `D(X)` on an affine group `G = Spec H` and a magnet `N`, a tangent
derivation at the unit lies in `Lie(G^N)` exactly when it vanishes on every weight space
`H_χ` with `χ ∉ N`: `Lie(G^N) = Lie(G)^N`.

The *tangent weights* of `G` are the weights `χ` for which some tangent derivation does not
vanish on `H_χ` (for `G` reductive with split maximal torus these are `0` and the roots).
Consequently `Lie(G^N)` only depends on `N ∩ (tangent weights)`; in particular, if
`N ∩ W = f⁻¹(ℕ) ∩ W` for a magnet map `f`, then `Lie(G^N) = Lie(P(λ_f))`
(step "Lie(G^N) = Lie P(λ_f)" of the proof of Proposition 16.10 (ii)).
-/

suppress_compilation

open Magnetism TauCeti TauCeti.Cocharacter

namespace AlgMag.Reductive

universe u v w w'

variable {R : Type u} {H : Type v} {X : Type w}
variable [CommRing R] [CommRing H] [HopfAlgebra R H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[R] MonoidAlgebra R X)
variable (B : Type w') [CommRing B] [Algebra R B]

/-- The tangent weights of `G` for the torus `D(X)`: the weights `χ` such that some tangent
derivation at the unit (with coefficients in `B`) does not vanish on the weight space `H_χ`. -/
def tangentWeights : Set (Additive X) :=
  {χ | ∃ d : Derivation R H (Bialgebra.CounitAlgebra R H B), ∃ h ∈ torusGrading π χ, d h ≠ 0}

variable {π B}

/-- The Lie algebra of a closed subgroup only depends on its ideal. -/
lemma lieSubalgebra_eq_of_toIdeal_eq {I J : HopfIdeal R H} (h : I.toIdeal = J.toIdeal) :
    I.lieSubalgebra (B := B) = J.lieSubalgebra (B := B) := by
  ext d
  rw [HopfIdeal.mem_lieSubalgebra_iff, HopfIdeal.mem_lieSubalgebra_iff, h]

/-- **Proposition 16.4 of Algebraic Magnetism (Hopf form): `Lie(G^N) = Lie(G)^N`.** A tangent
derivation lies in the Lie algebra of the attractor `G^N` exactly when it vanishes on every
weight space `H_χ` with `χ ∉ N`. -/
theorem mem_lieSubalgebra_magnetHopfIdeal_iff (N : Magnet (Additive X))
    (d : Derivation R H (Bialgebra.CounitAlgebra R H B)) :
    d ∈ (magnetHopfIdeal π N).lieSubalgebra (B := B) ↔
      ∀ χ ∉ N, ∀ h ∈ torusGrading π χ, d h = 0 := by
  rw [HopfIdeal.mem_lieSubalgebra_iff_of_toIdeal_eq_span (magnetHopfIdeal π N)
    (S := ⋃ (m : Additive X) (_ : m ∉ N), (torusGrading π m : Set H))
    (by rw [magnetHopfIdeal_toIdeal]; rfl)]
  constructor
  · intro hd χ hχ h hh
    exact hd h (Set.mem_iUnion₂.mpr ⟨χ, hχ, hh⟩)
  · intro hd h hh
    obtain ⟨χ, hχ, hh⟩ := Set.mem_iUnion₂.mp hh
    exact hd χ hχ h hh

/-- **`Lie(G^N)` only depends on the tangent weights in `N`.** If two magnets contain the same
tangent weights, their attractors have the same Lie algebra. -/
theorem lieSubalgebra_magnetHopfIdeal_eq {N N' : Magnet (Additive X)}
    (hNN' : ∀ χ ∈ tangentWeights π B, χ ∈ N ↔ χ ∈ N') :
    (magnetHopfIdeal π N).lieSubalgebra (B := B) =
      (magnetHopfIdeal π N').lieSubalgebra (B := B) := by
  have key : ∀ {N N' : Magnet (Additive X)},
      (∀ χ ∈ tangentWeights π B, χ ∈ N ↔ χ ∈ N') →
      ∀ d : Derivation R H (Bialgebra.CounitAlgebra R H B),
        d ∈ (magnetHopfIdeal π N).lieSubalgebra (B := B) →
          d ∈ (magnetHopfIdeal π N').lieSubalgebra (B := B) := by
    intro N N' hNN' d hd
    rw [mem_lieSubalgebra_magnetHopfIdeal_iff] at hd ⊢
    intro χ hχ h hh
    by_contra hne
    have hW : χ ∈ tangentWeights π B := ⟨d, h, hh, hne⟩
    exact hne (hd χ (fun hN => hχ ((hNN' χ hW).mp hN)) h hh)
  ext d
  exact ⟨key hNN' d, key (fun χ hχ => (hNN' χ hχ).symm) d⟩

variable (ψ : X →* Multiplicative ℤ)

/-- **Lie step of Proposition 16.10 (ii) of Algebraic Magnetism.** If the magnet `N` and
`f⁻¹(ℕ)` (for the magnet map `f`) contain the same tangent weights, then
`Lie(G^N) = Lie(P(λ_f))`. -/
theorem lieSubalgebra_magnetHopfIdeal_eq_parabolic {N : Magnet (Additive X)}
    (hN : ∀ χ ∈ tangentWeights π B, χ ∈ N ↔ 0 ≤ pairingHom ψ χ) :
    (magnetHopfIdeal π N).lieSubalgebra (B := B) =
      (parabolicDefiningHopfIdeal (π.cocharacter ψ)).lieSubalgebra (B := B) := by
  rw [lieSubalgebra_magnetHopfIdeal_eq (N' := natMagnet.comap (pairingHom ψ)) (fun χ hχ => ?_)]
  · exact lieSubalgebra_eq_of_toIdeal_eq
      (by rw [magnetHopfIdeal_toIdeal, magnetIdeal_torusGrading_comap_nat])
  · rw [hN χ hχ]
    rfl

end AlgMag.Reductive
