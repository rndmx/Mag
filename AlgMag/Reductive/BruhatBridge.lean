/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.BruhatRankOneProof

/-!
# `BruhatPointEq` from the rank-one torus data

Connects the group-theoretic `bruhat_rankOne_group` (via `bruhatConvEq_of_groupEq`,
`cellPointsSurj`, `bruhatPointEq_of_convEq`, all in `BruhatRankOneProof`) to the named Prop
`BruhatPointEq`.  The only leftover is `RankOneTorusData`: a subgroup `T ≤ P(λ)(k)` acting on
`U(λ⁻)(k)` through a `G_a`-coordinate `e` with a character `χ` onto `kˣ`.

SL₂ check (`k = k̄`): `T = {diag(a, a⁻¹)}`, `e(u⁻(x)) = x`, `t(a) u⁻(x) t(a)⁻¹ = u⁻(a⁻² x)`,
so `χ(t(a)) = a⁻²`, which hits every `c ≠ 0` since `k` is algebraically closed;
`n⁻¹ t(a) n = t(a⁻¹) ∈ T`; `T ≤ B⁺ = P(λ)`.
-/

suppress_compilation

open AlgebraicGeometry CategoryTheory Magnetism TauCeti TauCeti.Cocharacter WithConv

universe u

namespace AlgMag.Reductive

variable {k : Type u} {H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
variable (l : H →ₐc[k] LaurentPolynomial k) [Algebra.FiniteType k H] [Algebra.Smooth k H]

/-- **Leftover named Prop** (true for SL₂, see module docstring; for general `G` it is
RayGa: `U(λ⁻) ≅ G_a` with a nonzero weight, `T` the torus). A subgroup `T ≤ P(λ)(k)`
normalizing `U(λ⁻)(k)`, with `n⁻¹ T n ⊆ T`, and a `G_a`-coordinate `e` on `U(λ⁻)(k)` on which `T`
acts by a character `χ` hitting all of `kˣ`. -/
def RankOneTorusData (n : WithConv (H →ₐ[k] k)) : Prop :=
  ∃ (T : Subgroup (WithConv (H →ₐ[k] k))) (e : WithConv (H →ₐ[k] k) → k)
    (χ : WithConv (H →ₐ[k] k) → k),
    T ≤ parabolic k l ∧
    (∀ t ∈ T, ∀ v ∈ unipotent k l.oppositeCocharacter,
      t * v * t⁻¹ ∈ unipotent k l.oppositeCocharacter) ∧
    (∀ t ∈ T, n⁻¹ * t * n ∈ T) ∧
    (∀ v ∈ unipotent k l.oppositeCocharacter, e v = 0 ↔ v = 1) ∧
    (∀ v ∈ unipotent k l.oppositeCocharacter, ∀ w ∈ unipotent k l.oppositeCocharacter,
      e v = e w → v = w) ∧
    (∀ c : k, c ≠ 0 → ∃ t ∈ T, χ t = c) ∧
    (∀ t ∈ T, ∀ v ∈ unipotent k l.oppositeCocharacter, e (t * v * t⁻¹) = χ t * e v)

/-- **`BruhatPointEq`** from the Weyl property of `n`, `U(λ)(k) ≠ 1`, `G` irreducible, and the
torus data. -/
theorem bruhatPointEq_of_torusData [IsAlgClosed k]
    [IrreducibleSpace (Spec (CommRingCat.of H))] (n : WithConv (H →ₐ[k] k))
    (hconj : ∀ x ∈ parabolic k l, n⁻¹ * x * n ∈ parabolic k l.oppositeCocharacter)
    (hU : ∃ u ∈ unipotent k l, u ≠ 1) (hT : RankOneTorusData l n) :
    BruhatPointEq l n (TauCeti.Bialgebra.augmentationPoint k (CellV l)) := by
  obtain ⟨T, e, χ, hTP, hTU, hnT, he0, hinj, hχ, hact⟩ := hT
  have htrans := htrans_of_coordinate (unipotent k l.oppositeCocharacter) T e he0 hinj χ hχ
    hact hTU
  exact bruhatPointEq_of_convEq l n
    (bruhatConvEq_of_groupEq l n
      (fun _ hv _ hp => bruhat_rankOne_group _ _ T n hTP hTU hnT (inv_not_mem_cell l hconj hU)
        htrans (hne_of_irreducible l n) hv hp)
      (cellPointsSurj l))

#print axioms bruhatPointEq_of_torusData

end AlgMag.Reductive
