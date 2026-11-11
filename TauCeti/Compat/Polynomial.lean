/-
Copyright: the Mathlib contributors (see the source file named below).
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from Tau Ceti (github.com/TauCetiProject/TauCeti, commit d2083f0); see TauCeti/CHANGES.md
-/
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree

/-!
# Backport (compat, not Tau Ceti code)

Mathlib 1b1ccf4 `Mathlib/Algebra/Polynomial/Div.lean` states
`Polynomial.rootMultiplicity_eq_natTrailingDegree'` over a `Ring`; Mathlib 16edf57 only over a
`CommRing` (likewise `le_rootMultiplicity_iff`, `rootMultiplicity_le_iff`). The `Ring` versions are copied here (same proof) with suffix `_ring`
to avoid name clashes. `trailingCoeff_ne_zero.2 h` is written `trailingCoeff_eq_zero.not.2 h`.
-/

namespace Polynomial
variable {R : Type*} [Ring R] {p : R[X]}

lemma le_rootMultiplicity_iff_ring (p0 : p ≠ 0) {a : R} {n : ℕ} :
    n ≤ rootMultiplicity a p ↔ (X - C a) ^ n ∣ p := by
  simp_rw [rootMultiplicity, dite_eq_right p0, Nat.le_find_iff, not_not]
  refine ⟨fun h => ?_, fun h m hm => (pow_dvd_pow _ hm).trans h⟩
  rcases n with - | n
  · rw [pow_zero]
    apply one_dvd
  · exact h n n.lt_succ_self

lemma rootMultiplicity_le_iff_ring (p0 : p ≠ 0) (a : R) (n : ℕ) :
    rootMultiplicity a p ≤ n ↔ ¬(X - C a) ^ (n + 1) ∣ p := by
  rw [← (le_rootMultiplicity_iff_ring p0).not, not_le, Nat.lt_add_one_iff]

lemma rootMultiplicity_eq_natTrailingDegree'_ring :
    p.rootMultiplicity 0 = p.natTrailingDegree := by
  by_cases h : p = 0
  · simp only [h, rootMultiplicity_zero, natTrailingDegree_zero]
  refine le_antisymm ?_ ?_
  · rw [rootMultiplicity_le_iff_ring h, map_zero, sub_zero, X_pow_dvd_iff, not_forall]
    exact ⟨p.natTrailingDegree,
      fun h' ↦ (trailingCoeff_eq_zero.not.2 h) <| h' <| Nat.lt_add_one _⟩
  · rw [le_rootMultiplicity_iff_ring h, map_zero, sub_zero, X_pow_dvd_iff]
    exact fun _ ↦ coeff_eq_zero_of_lt_natTrailingDegree

end Polynomial
