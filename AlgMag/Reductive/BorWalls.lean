/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.Prop1610Field

/-!
# Wall steps for the gallery induction (Bor-plan §2)

* **S0.** Two cocharacters `π.cocharacter ψ`, `π.cocharacter φ` of a torus action with the same
  signs on the tangent weights have the same dynamic parabolic (both parabolics geometrically
  connected). Proof: both equal the attractor of `N = ψ⁻¹(ℕ) ∩ φ⁻¹(ℕ)` (Prop 16.10 (ii)).
-/

suppress_compilation

open Magnetism TauCeti TauCeti.Cocharacter
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type*}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)

/-- **S0.** Same signs on the tangent weights give the same dynamic parabolic. -/
theorem parabolic_eq_of_sameSigns [Algebra.Smooth k H] (ψ φ : X →* Multiplicative ℤ)
    (hs : ∀ χ ∈ tangentWeights π k, (0 ≤ pairingHom ψ χ ↔ 0 ≤ pairingHom φ χ))
    (hP : ConnectedSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k]
      (H ⧸ (parabolicDefiningHopfIdeal (π.cocharacter ψ)).toIdeal))))
    (hQ : ConnectedSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k]
      (H ⧸ (parabolicDefiningHopfIdeal (π.cocharacter φ)).toIdeal)))) :
    parabolicDefiningHopfIdeal (π.cocharacter ψ) =
      parabolicDefiningHopfIdeal (π.cocharacter φ) := by
  let N : Magnet (Additive X) :=
    natMagnet.comap (pairingHom ψ) ⊓ natMagnet.comap (pairingHom φ)
  have h1 := magnetIdeal_eq_parabolic_of_field π ψ (N := N) inf_le_left
    (fun χ hχ => by
      change (0 ≤ pairingHom ψ χ ∧ 0 ≤ pairingHom φ χ) ↔ _
      exact ⟨And.left, fun h => ⟨h, (hs χ hχ).1 h⟩⟩) hP
  have h2 := magnetIdeal_eq_parabolic_of_field π φ (N := N) inf_le_right
    (fun χ hχ => by
      change (0 ≤ pairingHom ψ χ ∧ 0 ≤ pairingHom φ χ) ↔ _
      exact ⟨And.right, fun h => ⟨(hs χ hχ).2 h, h⟩⟩) hQ
  exact SetLike.ext' (congrArg (fun I : Ideal H => (I : Set H)) (h1.symm.trans h2))

end AlgMag.Reductive
