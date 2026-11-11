/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.RingTheory.Filtration
import Mathlib.Algebra.Polynomial.Div

/-!
# Fact 3.34 for infinite families: the two algebra steps

The scheme arguments (fpqc descent) are not formalized; these two algebra steps are.

* `AlgMag.Fact334Inf.pinching_iInf_eq_zero`: the ideals `I_k` of step (b) of the pinching case have zero intersection.
* `AlgMag.Fact334Inf.krull_step`: the Krull step of the cone case, which puts the denominators in `R[⋂ N_k]`.
-/

namespace AlgMag.Fact334Inf

open Polynomial

/-- Pinching case of **Fact 3.34**. In `B[x]`, an element of every ideal `(x^k d)` is zero. With `B = R[w,w']` and `d = w - w'`,
these are the ideals of `A(N_1) ×_{A(N_k)} A(N_1)` in `A(N_1) ×_{A(N_∞)} A(N_1)`, for `N_k = cone((1,0),(k,1))`. -/
theorem pinching_iInf_eq_zero {B : Type*} [CommRing B] (d f : B[X])
    (h : ∀ k : ℕ, f ∈ Ideal.span {(X : B[X]) ^ k * d}) : f = 0 := by
  ext n
  have hk := h (n + 1)
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hk |>.imp fun g hg => hg.symm
  rw [show g * ((X : B[X]) ^ (n + 1) * d) = (X : B[X]) ^ (n + 1) * (g * d) by ring]
  simp [coeff_X_pow_mul']

/-- Cone case of **Fact 3.34**. `A` noetherian (`A = R₀[N_∞]`, `R₀` a finitely generated subring). If `e` lies in `b A + I^n` for
all `n` (that is, `e = b c` for a series `c` in the `I`-adic completion), then `(1 - i) e = b a` for some `i ∈ I`, `a ∈ A`. -/
theorem krull_step {A : Type*} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (b e : A)
    (h : ∀ n : ℕ, ∃ c : A, e - b * c ∈ I ^ n) : ∃ i ∈ I, ∃ a : A, (1 - i) * e = b * a := by
  let q : A →ₗ[A] (A ⧸ Ideal.span {b}) := Submodule.mkQ _
  have hq : ∀ c, q (b * c) = 0 := fun c => by
    exact (Submodule.Quotient.mk_eq_zero _).mpr (Ideal.mul_mem_right c _ (Ideal.mem_span_singleton_self b))
  have hmem : q e ∈ (⨅ i : ℕ, I ^ i • ⊤ : Submodule A (A ⧸ Ideal.span {b})) := by
    refine Submodule.mem_iInf _ |>.mpr fun n => ?_
    obtain ⟨c, hc⟩ := h n
    have h1 : q e = (e - b * c) • q 1 := by
      rw [← map_smul, smul_eq_mul, mul_one, map_sub, hq, sub_zero]
    rw [h1]
    exact Submodule.smul_mem_smul hc trivial
  obtain ⟨r, hr⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff I (q e)).mp hmem
  refine ⟨r, r.2, ?_⟩
  have h0 : q ((1 - (r : A)) * e) = 0 := by
    rw [sub_mul, one_mul, map_sub, ← smul_eq_mul, map_smul, hr, sub_self]
  have h2 : (1 - (r : A)) * e ∈ Ideal.span {b} := (Submodule.Quotient.mk_eq_zero _).mp h0
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h2
  exact ⟨a, by rw [← ha, mul_comm]⟩

end AlgMag.Fact334Inf

#print axioms AlgMag.Fact334Inf.pinching_iInf_eq_zero
#print axioms AlgMag.Fact334Inf.krull_step
