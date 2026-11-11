/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.IdentityComponentRoots
import AlgMag.Reductive.TorusBaseChange

/-!
# `(G^N)° = K_R` over an arbitrary field, after base change to `k̄`

For `G` smooth of finite type over a field `k`, the identity component of `G^N_{k̄}` depends only
on `N ∩ Φ`, `Φ` the roots of `G` over `k` (`compIdealBar_eq_of_roots`), and
`(G^N_{k̄})° = K_{N ∩ Φ}` (`compIdealBar_eq_rootComp`). The attractor itself commutes with
`k → k̄` (`magnetIdeal_baseChange`).
-/

suppress_compilation

open Magnetism TauCeti
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)

/-- `π_{k̄}`: the torus action over `k̄`. -/
abbrev piBar : AlgebraicClosure k ⊗[k] H →ₐc[AlgebraicClosure k]
    MonoidAlgebra (AlgebraicClosure k) X :=
  torusBaseChange (AlgebraicClosure k) π

variable [Algebra.FiniteType k H]

/-- Roots of `G_{k̄}` are roots of `G`. -/
lemma roots_piBar_subset : roots (piBar π) ⊆ roots π := by
  intro α hα
  have h0 : α ≠ 0 := fun h => hα.1 (by rw [h]; rfl)
  exact (mem_tangentWeights_iff_mem_roots (π := π) h0).1
    (tangentWeights_baseChange_subset (AlgebraicClosure k) π
      ((mem_tangentWeights_iff_mem_roots h0).2 hα))

variable [Algebra.Smooth k H]

/-- **Lemma 3 (F9) over any field.** If `N ≤ N'` and `N ∩ Φ = N' ∩ Φ`, then
`(G^N_{k̄})° = (G^{N'}_{k̄})°`. -/
theorem compIdealBar_eq_of_roots {N N' : Magnet (Additive X)} (hle : N ≤ N')
    (h : ∀ α ∈ roots π, α ∈ N ↔ α ∈ N') : compIdeal (piBar π) N = compIdeal (piBar π) N' :=
  compIdeal_eq_of_roots (piBar π) hle fun α hα => h α (roots_piBar_subset π hα)

/-- **`(G^N_{k̄})° = K_{N ∩ Φ}` over any field.** -/
theorem compIdealBar_eq_rootComp (N : Magnet (Additive X)) :
    compIdeal (piBar π) N = rootComp (piBar π) ({α | α ∈ N} ∩ roots π) := by
  refine (compIdealBar_eq_of_roots π (AddSubmonoid.closure_le.2 Set.inter_subset_left)
    fun α hα => ⟨fun h => AddSubmonoid.closure_le.2 Set.inter_subset_left h,
      fun h => AddSubmonoid.subset_closure ⟨h, hα⟩⟩).symm

end AlgMag.Reductive

