/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.Prop1610
import AlgMag.Reductive.OpenCell.OpenCellFlatness

/-!
# Discharging `ParabolicGeneration`

1. `parabolicGeneration_iff`: for any `R`, `H`, the structure `ParabolicGeneration π ψ N` is
   inhabited iff `P(λ_f) ⊆ G^N` (as ideals: `magnetIdeal N ≤ I_{P(λ_f)}`). So the hypothesis is
   exactly the hard inclusion of Prop 16.10 (ii), not the ray-generation statement (Gen).
2. `parabolicGeneration_of_field`: over any field `k`, `G` smooth of finite type and geometrically
   connected, with the root condition `hΦ`, the structure is inhabited, from the already proved
   `OpenCell.magnetIdeal_eq_parabolic_of_field` (open cell étale, no sorry).
-/

suppress_compilation

open Magnetism TauCeti TauCeti.Cocharacter AlgMag.OpenCellNotes
open scoped TensorProduct

namespace AlgMag.Reductive

universe u v w

section General

variable {R : Type u} {H : Type v} {X : Type w}
variable [CommRing R] [CommRing H] [HopfAlgebra R H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[R] MonoidAlgebra R X) (ψ : X →* Multiplicative ℤ)

/-- From `P(λ_f) ⊆ G^N`, the one-generator family `U = P(λ_f)`. -/
def ParabolicGeneration.ofLe {N : Magnet (Additive X)}
    (h : magnetIdeal (torusGrading π) N ≤
      (parabolicDefiningHopfIdeal (π.cocharacter ψ)).toIdeal) :
    ParabolicGeneration π ψ N where
  ι := PUnit
  U := fun _ => parabolicDefiningHopfIdeal (π.cocharacter ψ)
  le_attractor := fun _ => h
  generates := fun _ hI => hI PUnit.unit

/-- `ParabolicGeneration π ψ N` is inhabited iff `P(λ_f) ⊆ G^N`. -/
theorem parabolicGeneration_iff {N : Magnet (Additive X)} :
    Nonempty (ParabolicGeneration π ψ N) ↔
      magnetIdeal (torusGrading π) N ≤
        (parabolicDefiningHopfIdeal (π.cocharacter ψ)).toIdeal := by
  constructor
  · rintro ⟨g⟩
    have := g.generates (magnetHopfIdeal π N) (fun i => by
      rw [magnetHopfIdeal_toIdeal]; exact g.le_attractor i)
    rwa [magnetHopfIdeal_toIdeal] at this
  · exact fun h => ⟨ParabolicGeneration.ofLe π ψ h⟩

end General

section Field

variable {k : Type u} {H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]

/-- **`ParabolicGeneration` holds over any field** (`G` smooth, finite type, geometrically
connected; `N ⊆ f⁻¹(ℕ)` with the same roots). -/
noncomputable def parabolicGeneration_of_field {X : Type u} [CommGroup X] [DecidableEq X]
    [Algebra.FiniteType k H] [Algebra.Smooth k H]
    [ConnectedSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k] H))]
    (π : H →ₐc[k] MonoidAlgebra k X) (ψ : X →* Multiplicative ℤ)
    {N : Magnet (Additive X)} (hN : N ≤ natMagnet.comap (pairingHom ψ))
    (hΦ : {α | α ∈ N} ∩ roots π = {α | α ∈ natMagnet.comap (pairingHom ψ)} ∩ roots π) :
    ParabolicGeneration π ψ N :=
  ParabolicGeneration.ofLe π ψ (OpenCell.magnetIdeal_eq_parabolic_of_field π ψ hN hΦ).le

end Field

end AlgMag.Reductive
