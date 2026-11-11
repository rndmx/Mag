/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

/-!
# Fact 3.34 for infinite families: monomial denominators in the cone case

* `AlgMag.Fact334Inf.exists_common_shift`: finitely many differences of elements of `Q` are moved into `Q` by one element of `Q`.
* `AlgMag.Fact334Inf.cone_no_conductor`: for `N_1 = {a ≥ 0, b ≥ -a}` and `Q = ℕ²`, no shift moves all of `N_1` into `Q`.
-/

namespace AlgMag.Fact334Inf

/-- Cone case of **Fact 3.34**: finitely many elements of `Q - Q` have a common shift into `Q`. -/
theorem exists_common_shift {M : Type*} [AddCommGroup M] (Q : AddSubmonoid M) (s : Finset M)
    (hs : ∀ m ∈ s, ∃ a ∈ Q, ∃ b ∈ Q, m = a - b) : ∃ e ∈ Q, ∀ m ∈ s, e + m ∈ Q := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, Q.zero_mem, by simp⟩
  | insert x t _ ih =>
    obtain ⟨e, he, ht⟩ := ih fun m hm => hs m (Finset.mem_insert_of_mem hm)
    obtain ⟨a, ha, b, hb, hx⟩ := hs x (Finset.mem_insert_self x t)
    refine ⟨e + b, Q.add_mem he hb, fun m hm => ?_⟩
    rcases Finset.mem_insert.mp hm with rfl | hm
    · have : e + b + m = e + a := by rw [hx]; abel
      rw [this]; exact Q.add_mem he ha
    · have : e + b + m = (e + m) + b := by abel
      rw [this]; exact Q.add_mem (ht m hm) hb

/-- Cone case of **Fact 3.34**: `N_1 = {a ≥ 0, b ≥ -a}` has no conductor into `Q = {a ≥ 0, b ≥ 0}`. -/
theorem cone_no_conductor (e : ℤ × ℤ) :
    ∃ n : ℤ × ℤ, 0 ≤ n.1 ∧ -n.1 ≤ n.2 ∧ ¬ (0 ≤ (e + n).1 ∧ 0 ≤ (e + n).2) := by
  refine ⟨(|e.2| + 1, -(|e.2| + 1)), by have := abs_nonneg e.2; simp only; linarith, by simp, ?_⟩
  rintro ⟨-, h⟩
  have := le_abs_self e.2
  simp only [Prod.snd_add] at h
  linarith

end AlgMag.Fact334Inf

#print axioms AlgMag.Fact334Inf.exists_common_shift
#print axioms AlgMag.Fact334Inf.cone_no_conductor
