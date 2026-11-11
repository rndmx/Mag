/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.T2Classical
import AlgMag.Reductive.BorBasePair

/-!
# Step (d) from (Base±): `stepD_of_basePair`

Recreated from lean-classical.md §4 (the original text in `StepDProof.lean` was overwritten).

Idea (avoids Borel 13.17): take `ν` regular (`Z ν = Tq`) with `P(ν)` and `P(ν⁻¹)` Borel. Both
contain `T`, and `P(ν) ∩ P(ν⁻¹) = Z(ν) = T`, so `V(N) ⊆ T`. A connected smooth unipotent subgroup
of `T` is trivial (`UnipInTorus`, proved in `UnipInTorusProof`), hence `⊆ R_u(G)`.
-/

open Magnetism TauCeti TauCeti.Cocharacter

namespace AlgMag.Reductive.StepDBasePair

open AlgMag.Reductive AlgMag.Reductive.BorelRoute AlgMag.Reductive.BorelRouteReal
  AlgMag.Reductive.T2Classical AlgMag.Reductive.BorBasePair

universe u

variable {k : Type u} {H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]

local notation "Hf" => FiniteTypeCommHopfAlgCat.of k H

/-- **`UnipInTorus Tq`** (named here; proved for `Tq = ker π` in `UnipInTorusProof`): if
`V(N) ⊆ V(Tq)` is geometrically connected, smooth and unipotent, then `V(N)` is trivial. -/
def UnipInTorus (Tq : HopfIdeal k H) : Prop :=
  ∀ N : HopfIdeal k H, Tq ≤ N →
    geometricallyConnectedCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient Hf N).obj →
    smoothUnipotentCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient Hf N) →
    HopfIdeal.augmentation k H ≤ N

/-- **Step (d) from (Base±)** and `UnipInTorus`. -/
theorem stepD_of_basePair {Tq : HopfIdeal k H} (hBP : BasePair Tq) (hU : UnipInTorus Tq) :
    StepD Tq := by
  intro _ N hgc hsu hB
  obtain ⟨ν, hν, hB₁, hB₂⟩ := hBP
  have hZ : Z ν ≤ Tq := le_of_eq hν
  have h₁ : P ν ≤ N :=
    hB _ (isBorelIn_bot_iff.2 hB₁) ((le_trans (by rw [Z_eq]; exact le_sup_left) hZ))
  have h₂ : P ν.oppositeCocharacter ≤ N :=
    hB _ (isBorelIn_bot_iff.2 hB₂) ((le_trans (by rw [Z_eq]; exact le_sup_right) hZ))
  have hTN : Tq ≤ N := by rw [← hν, Z_eq]; exact sup_le h₁ h₂
  exact (HopfIdeal.le_augmentation k H (Ru ⊥)).trans (hU N hTN hgc hsu)

end AlgMag.Reductive.StepDBasePair

#print axioms AlgMag.Reductive.StepDBasePair.stepD_of_basePair
