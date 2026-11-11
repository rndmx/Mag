/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Fact 3.34 for infinite families: a combinatorial lemma

One step towards the case of infinite families, `X` separated without atlas:
`M` finitely generated, `(N_k)` a decreasing sequence of submonoids. If `n ∈ ⋂ N_k` and `-n ∈ N_k` for all `k` up to multiples,
then `-n ∈ ⋂ N_k`: the point `0` of `𝔸(⋂ N_k)` lies in the image of `𝔸(N_k)` for large `k`.
-/

namespace AlgMag.Final

variable {M : Type*} [AddCommGroup M]

/-- Let `n ∈ N` where `N ≤ N_k`, and let `d > 0` with `-(d • n) ∈ N_k`. Then `-n ∈ N_k`. -/
theorem neg_mem_of_nsmul {K : AddSubmonoid M} {n : M} (hn : n ∈ K) {d : ℕ} (hd : d ≠ 0)
    (h : -(d • n) ∈ K) : -n ∈ K := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd
  have : -n = -((e + 1) • n) + e • n := by
    rw [succ_nsmul]; abel
  rw [this]
  exact K.add_mem h (K.nsmul_mem hn e)

/-- If, for each `K` of a family, a positive multiple of `-n` lies in `K`, and `n` lies in all of them, then `-n` lies in the
intersection. With `M` finitely generated, the units of `N_k` have eventually constant rank, hence finite index in a fixed lattice,
which gives such multiples: so a nonunit of `⋂ N_k` does not become a unit in all the `N_k`. -/
theorem neg_mem_iInf_of_multiples {ι : Sort*} (K : ι → AddSubmonoid M) {n : M} (hn : ∀ i, n ∈ K i)
    (h : ∀ i, ∃ d : ℕ, d ≠ 0 ∧ -(d • n) ∈ K i) : -n ∈ ⨅ i, K i := by
  rw [AddSubmonoid.mem_iInf]
  intro i
  obtain ⟨d, hd, hk⟩ := h i
  exact neg_mem_of_nsmul (hn i) hd hk

end AlgMag.Final

#print axioms AlgMag.Final.neg_mem_iInf_of_multiples
