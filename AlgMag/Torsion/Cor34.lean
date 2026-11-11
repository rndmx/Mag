/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Torsion.Prop33

/-!
# Lemma 1.2(c), Corollary 3.4, and the equivalence (1) ⇔ (2)

* `ZW w` : the subgroup `(1 - w)M` (carrier `Zset w`).
* `prim_ZW` (Lemma 1.2(c)): if `orderOf w = p^b` and `M` is torsion free, the torsion of `M/(1-w)M`
  is killed by `p^b`.
* `cor34`: for `w ∈ W(Φ)` of order `p^b`, some `w^(p^k) ∈ W(R_w)`, and `w ∈ W(R_w)` if `p` is not
  a torsion prime.
* `isTP_iff_candidate`: `IsTP p ↔ ∃ w ∈ W(Φ), b > 0, orderOf w = p^b, w ∉ W(R_w)`.
Hypotheses: `HypR1`, `HypR2`, `M` free of finite rank, `Fintype ι`.
-/

namespace AlgMag.Torsion

open Set RD Classical

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] [Fintype ι] {P : RootPairing ι ℤ M N}

namespace RD

/-- `(1 - w)M` as a subgroup. -/
def ZW (w : M ≃ₗ[ℤ] M) : AddSubgroup M where
  carrier := Zset w
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, by simp; abel⟩
  neg_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨-a, by simp; abel⟩

lemma sub_pow_mem_ZW (w : M ≃ₗ[ℤ] M) (m : M) : ∀ i : ℕ, m - (w ^ i) m ∈ ZW w
  | 0 => by simp [zero_mem]
  | i + 1 => by
    have h1 : (w ^ i) m - (w ^ (i + 1)) m ∈ ZW w :=
      ⟨(w ^ i) m, by rw [pow_succ']; rfl⟩
    have := add_mem (sub_pow_mem_ZW w m i) h1
    simpa using this

/-- Lemma 1.2(c). -/
lemma prim_ZW (htf : ∀ (n : ℤ) (m : M), n ≠ 0 → n • m = 0 → m = 0) {w : M ≃ₗ[ℤ] M} {p b : ℕ} (hw : orderOf w = p ^ b) :
    Prim p b (ZW w) := by
  intro m n hn hm
  set q := p ^ b
  let ν : M → M := fun y => ∑ i ∈ Finset.range q, (w ^ i) y
  have hν : ∀ y, ν (y - w y) = 0 := by
    intro y
    have htel : ∀ k : ℕ, ∑ i ∈ Finset.range k, (w ^ i) (y - w y) = y - (w ^ k) y := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_range_succ, ih, map_sub, pow_succ]
        simp
    show ∑ i ∈ Finset.range q, (w ^ i) (y - w y) = 0
    rw [htel, ← hw, pow_orderOf_eq_one]; simp
  have hνadd : ∀ (k : ℤ) y, ν (k • y) = k • ν y := by
    intro k y; simp [ν, Finset.smul_sum]
  obtain ⟨y, hy⟩ := hm
  have h0 : n • ν m = 0 := by rw [← hνadd, ← hy, hν]
  have hν0 : ν m = 0 := htf n _ hn h0
  have hsum : ((q : ℕ) : ℤ) • m = ∑ i ∈ Finset.range q, (m - (w ^ i) m) := by
    rw [Finset.sum_sub_distrib]
    have : ∑ i ∈ Finset.range q, (w ^ i) m = 0 := hν0
    rw [this]; simp
  rw [hsum]
  exact AddSubgroup.sum_mem _ fun i _ => sub_pow_mem_ZW w m i

lemma mem_WZ_ZW (w : M ≃ₗ[ℤ] M) : w ∈ WZ (ZW w) := fun m => ⟨m, rfl⟩

variable [Module.Free ℤ M] [Module.Finite ℤ M]

omit [Fintype ι] [Module.Finite ℤ M] in
lemma tf_of_free : ∀ (n : ℤ) (m : M), n ≠ 0 → n • m = 0 → m = 0 := by
  intro n m hn h
  let bs := Module.Free.chooseBasis ℤ M
  apply bs.repr.injective
  ext i
  have h1 : bs.repr (n • m) i = 0 := by rw [h]; simp
  rw [map_zsmul, Finsupp.smul_apply, smul_eq_mul] at h1
  simpa using (mul_eq_zero.1 h1).resolve_left hn

/-- Corollary 3.4. -/
theorem cor34 (hR1 : HypR1 P) (hR2 : HypR2 P) {p b : ℕ} (hp : p.Prime) {w : M ≃ₗ[ℤ] M}
    (hwW : w ∈ W P (range P.root)) (hw : orderOf w = p ^ b) :
    (∃ k : ℕ, w ^ (p ^ k) ∈ W P (range P.root ∩ Zset w)) ∧
      (¬ IsTP P p → w ∈ W P (range P.root ∩ Zset w)) :=
  prop33 hR1 hR2 hp (ZW w) (prim_ZW tf_of_free hw) w hwW (mem_WZ_ZW w)

end RD

/-- (1) ⇔ (2): `p` is a torsion prime iff there is a `p`-candidate. -/
theorem isTP_iff_candidate [Module.Free ℤ M] [Module.Finite ℤ M]
    (hR1 : HypR1 P) (hR2 : HypR2 P) {p : ℕ} (hp : p.Prime) :
    IsTP P p ↔ ∃ w : M ≃ₗ[ℤ] M, ∃ b : ℕ, w ∈ W P (range P.root) ∧ 0 < b ∧
      orderOf w = p ^ b ∧ w ∉ W P (range P.root ∩ Zset w) := by
  constructor
  · exact prop41' P
  · rintro ⟨w, b, hwW, -, hw, hn⟩
    by_contra h
    exact hn ((RD.cor34 hR1 hR2 hp hwW hw).2 h)

end AlgMag.Torsion
