/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Fact 3.34 for infinite families: the diagonal step

The algebra core of the diagonal step: if `τ c * Ψ = ρ` over `R[M]`, then `c * Δ Ψ = Δ ρ` over `R`.
`τ` is the universal translate `χ^n ↦ g^n χ^n`, and `Δ` keeps the coefficient of `g^s` in the coefficient of `χ^s`.
-/

namespace AlgMag.Fact334Inf

open HahnSeries

variable {M R : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M] [CommRing R]

/-- The universal translate `τ`: the coefficient `c_n` of `χ^n` becomes `c_n g^n`. -/
noncomputable def tau (c : HahnSeries M R) : HahnSeries M (AddMonoidAlgebra R M) where
  coeff n := AddMonoidAlgebra.single n (c.coeff n)
  isPWO_support' := c.isPWO_support.mono fun n hn hc => hn (by simp [hc])

/-- The diagonal `Δ`: the coefficient at `s` is the coefficient of `g^s` in the coefficient at `s`. -/
noncomputable def diag (B : HahnSeries M (AddMonoidAlgebra R M)) : HahnSeries M R where
  coeff s := (B.coeff s).coeff s
  isPWO_support' := B.isPWO_support.mono fun s hs hc => hs (by simp [hc])

/-- Diagonal step of **Fact 3.34** (infinite families): `Δ` is linear over `τ`. -/
theorem diag_tau_mul (c : HahnSeries M R) (B : HahnSeries M (AddMonoidAlgebra R M)) :
    diag (tau c * B) = c * diag B := by
  ext s
  have hsub : (diag B).support ⊆ B.support := fun t ht hc => ht (by simp [diag, hc])
  have hsubc : (tau c).support ⊆ c.support := fun t ht hc => ht (by simp [tau, hc])
  change ((tau c * B).coeff s).coeff s = (c * diag B).coeff s
  rw [coeff_mul_left' c.isPWO_support hsubc, coeff_mul_right' B.isPWO_support hsub,
    AddMonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun ij hij => ?_
  have h := (Finset.mem_addAntidiagonal.mp hij).2.2
  change ((AddMonoidAlgebra.single ij.1 (c.coeff ij.1) * B.coeff ij.2)).coeff s = _
  rw [AddMonoidAlgebra.coeff_single_mul_apply, ← h, neg_add_cancel_left]
  rfl

/-- Key step of **Fact 3.34** (infinite families): an identity `τ c * Ψ = ρ` over `R[M]` gives `c * Δ Ψ = Δ ρ` over `R`. -/
theorem mul_diag_eq_diag (c : HahnSeries M R) {Ψ ρ : HahnSeries M (AddMonoidAlgebra R M)}
    (h : tau c * Ψ = ρ) : c * diag Ψ = diag ρ := by
  rw [← h, diag_tau_mul]

/-- `Δ` of a term `g^m · d`, with `d` a series over `R`, is the single term `d_m χ^m`. -/
theorem diag_coeff_term (d : HahnSeries M R) (m s : M)
    (B : HahnSeries M (AddMonoidAlgebra R M))
    (hB : ∀ t, B.coeff t = AddMonoidAlgebra.single m (d.coeff t)) :
    (diag B).coeff s = if s = m then d.coeff m else 0 := by
  change (B.coeff s).coeff s = _
  rw [hB]
  by_cases hs : s = m
  · subst hs; simp
  · simp [hs, Finsupp.single_apply, Ne.symm hs]

end AlgMag.Fact334Inf

#print axioms AlgMag.Fact334Inf.diag_tau_mul
#print axioms AlgMag.Fact334Inf.mul_diag_eq_diag
#print axioms AlgMag.Fact334Inf.diag_coeff_term
