/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.RootGroupGaLie
import AlgMag.Reductive.SplitReductiveRootDatum
import AlgMag.Reductive.GluePrereqs

/-!
# Root groups of split reductive groups (Proposition `prop:root-groups`)

`SplitReductiveData.WithRootSpaces`: split reductive data with a reduced root datum, `X`
torsion-free, and root spaces of dimension one (SGA 3, Exp. XIX). For such `G` and every root
`α`, `U_α = G^{[α⟩}_e` is a root group (`isRootGroup_of_withRootSpaces`), and
`G^{[α⟩}(A) = U_α(A) ⋊ T(A)` (`attractor_semidirect_torus`: `G^0 = T` by
`magnetIdeal_bot_eq_ker`).
-/

suppress_compilation

open Magnetism TauCeti WithConv

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable [Module.Finite k (Bialgebra.CotangentSpace k H)]

/-- Split reductive data with a root datum, `X` torsion-free and root spaces of dimension one. -/
structure SplitReductiveData.WithRootSpaces (π : H →ₐc[k] MonoidAlgebra k X) extends
    SplitReductiveData.WithRootDatum π where
  /-- `X` is torsion-free. -/
  torsionFree : ∀ (x : Additive X) (n : ℕ), n • x = 0 → n = 0 ∨ x = 0
  /-- The root spaces are lines (SGA 3, Exp. XIX). -/
  finrank_rootSpace : ∀ α ∈ roots π, Module.finrank k (rootSpace π α) = 1

variable {π : H →ₐc[k] MonoidAlgebra k X} (D : SplitReductiveData.WithRootSpaces π)
include D

lemma SplitReductiveData.WithRootSpaces.ne_zero {α : Additive X} (hα : α ∈ roots π) : α ≠ 0 := by
  rw [← D.range_root] at hα
  obtain ⟨i, rfl⟩ := hα
  exact D.P.ne_zero i

/-- Roots have infinite order. -/
lemma SplitReductiveData.WithRootSpaces.nsmul_root_eq_zero {α : Additive X} (hα : α ∈ roots π)
    (n : ℕ) (hn : n • α = 0) : n = 0 :=
  (D.torsionFree α n hn).resolve_right (D.ne_zero hα)

/-- The root system is reduced: `nα ∉ Φ` for `n ≥ 2`. -/
lemma SplitReductiveData.WithRootSpaces.nsmul_root_not_mem {α : Additive X} (hα : α ∈ roots π)
    (n : ℕ) (hn : 2 ≤ n) : n • α ∉ roots π := by
  intro hnα
  have hα' := hα
  rw [← D.range_root] at hα' hnα
  obtain ⟨i, hi⟩ := hα'
  obtain ⟨j, hj⟩ := hnα
  haveI := D.reduced
  have hdep : ¬ LinearIndependent ℤ ![D.P.root j, D.P.root i] := by
    rw [LinearIndependent.pair_iff]
    intro h
    have := h 1 (-(n : ℤ)) (by rw [hi, hj, one_smul, neg_smul, natCast_zsmul, add_neg_cancel])
    exact one_ne_zero this.1
  rcases RootPairing.IsReduced.eq_or_eq_neg j i hdep with h | h
  · rw [hi, hj] at h
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ n by omega)
    have : m • α = 0 := by
      rw [add_smul, one_smul, add_eq_left] at h
      exact h
    have := D.nsmul_root_eq_zero hα _ this
    omega
  · rw [hi, hj] at h
    have : (n + 1) • α = 0 := by
      rw [add_smul, h, one_smul, neg_add_cancel]
    have := D.nsmul_root_eq_zero hα _ this
    omega

/-- **Proposition `prop:root-groups`.** For a split reductive group with root spaces of dimension
one, `U_α = G^{[α⟩}_e` is a root group for every root `α`. -/
theorem isRootGroup_of_withRootSpaces [Algebra.Smooth k H] {α : Additive X} (hα : α ∈ roots π) :
    IsRootGroup π α (rootGroupIdeal π α (D.nsmul_root_eq_zero hα)) :=
  isRootGroup_rootGroupIdeal_of_finrank (D.nsmul_root_eq_zero hα) (D.nsmul_root_not_mem hα)
    (D.finrank_rootSpace α hα)

omit D in
/-- **`G^0 = T` on points**: a point lies in `G^0(A)` iff it factors through `T`. -/
lemma mem_attractorSubgroup_bot_iff [IsAlgClosed k] [Algebra.FiniteType k H] [Algebra.Smooth k H]
    (D : SplitReductiveData π) {A : Type u} [CommRing A] [Algebra k A]
    (g : WithConv (H →ₐ[k] A)) :
    g ∈ attractorSubgroup π ⊥ A ↔ RingHom.ker π.toAlgHom ≤ RingHom.ker g.ofConv := by
  rw [mem_attractorSubgroup π, magnetIdeal_bot_eq_ker π D]

omit D in
/-- **`G^{[α⟩} = U_α ⋊ T`** on points, for split reductive `G` (`G^0 = T`). -/
def attractor_semidirect_torus (α : Additive X) (hα : ∀ n : ℕ, n • α = 0 → n = 0)
    (A : Type u) [CommRing A] [Algebra k A] :
    attractorSubgroup π (rayMagnet α) A ≃*
      (limitToBot π (rayMagnet_pointed hα) A).ker ⋊[(MulAut.conjNormal
        (H := (limitToBot π (rayMagnet_pointed hα) A).ker)).comp (botToAttractor π A)]
        attractorSubgroup π ⊥ A :=
  attractor_semidirect_rootGroup α hα A

end AlgMag.Reductive
