/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Joint rank-one argument, piece J0 (lattice part): `|W_Z| ≤ 2`

Notes: `equivalence-reductive/lean-joint.md`, Run 2, §5 J0 and §6.

A point `n` of the rank-one Levi `Z = Z_G(S_δ)` normalising `T` acts on the character lattice
`X` by some `σ`, and because `n` centralises the codimension-one torus `S_δ`, `σ` fixes the
cocharacter hyperplane `δ^⊥`; dually `σ x · x⁻¹ ∈ ℤδ` for every `x ∈ X`. This file is the pure
lattice algebra behind "the Weyl group of a rank-one group has order at most two":

* `AlongLine σ δ`: `σ x = x · δ^{m}` for some `m = m(x) ∈ ℤ`.
* `eq_one_or_reflection`: such a `σ` of finite order is `1` or an involution with `σ δ = δ⁻¹`.
* `reflection_unique`: two such involutions with a finite-order product are equal.

Hypothesis on `δ`: `δ^m = 1 → m = 0` (torsion-free `X`, `δ ≠ 1`). Finite order comes from
`finite_weylImage` (TorusRigidity). Nothing here uses Borel theory, T2, `ParabolicBorel`,
`dim U = 1` or `Z_G(T) = T`. True for `SL₂` (`W = {1, s}`) and for the rank-one Levis of `SL₃`.
-/

namespace AlgMag.Reductive.RankOneJoint

variable {X : Type*} [CommGroup X]

/-- `σ` moves every point of `X` along the line `ℤδ`. -/
def AlongLine (σ : X ≃* X) (δ : X) : Prop := ∀ x, ∃ m : ℤ, σ x = x * δ ^ m

section

variable {σ : X ≃* X} {δ : X} (hδ : ∀ m : ℤ, δ ^ m = 1 → m = 0)
include hδ

/-- Exponents along a non-torsion `δ` are unique. -/
theorem zpow_inj_of_nontorsion {m n : ℤ} (h : δ ^ m = δ ^ n) : m = n := by
  have h1 : δ ^ (m - n) = 1 := by rw [zpow_sub, h]; exact mul_inv_cancel _
  have := hδ _ h1
  omega

/-- The exponent function of an `AlongLine` automorphism is additive. -/
theorem AlongLine.exists_fun (h : AlongLine σ δ) :
    ∃ f : X → ℤ, (∀ x, σ x = x * δ ^ f x) ∧ ∀ x y, f (x * y) = f x + f y := by
  choose f hf using h
  refine ⟨f, hf, fun x y => zpow_inj_of_nontorsion hδ ?_⟩
  have h1 : σ (x * y) = x * y * δ ^ f (x * y) := hf _
  rw [map_mul, hf x, hf y] at h1
  have h2 : x * y * δ ^ (f x + f y) = x * y * δ ^ f (x * y) := by
    rw [zpow_add, mul_mul_mul_comm]; exact h1
  exact mul_left_cancel h2.symm

/-- **A finite-order automorphism moving `X` along `ℤδ` is `1` or a reflection in `δ`.** -/
theorem eq_one_or_reflection (h : AlongLine σ δ) {N : ℕ} (hN : 0 < N)
    (hfin : ∀ x, (⇑σ)^[N] x = x) :
    σ = 1 ∨ (σ δ = δ⁻¹ ∧ ∀ x, σ (σ x) = x) := by
  obtain ⟨f, hf, hadd⟩ := h.exists_fun hδ
  set c : ℤ := 1 + f δ with hc
  have hσδ : σ δ = δ ^ c := by rw [hf δ, hc, zpow_add, zpow_one]
  have hiter : ∀ j : ℕ, (⇑σ)^[j] δ = δ ^ (c ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih, map_zpow, hσδ, ← zpow_mul, pow_succ, mul_comm]
  have hcN : c ^ N = 1 := by
    have h1 := hiter N
    rw [hfin] at h1
    exact zpow_inj_of_nontorsion hδ (h1.symm.trans (zpow_one δ).symm)
  have hdvd : c ∣ 1 := ⟨c ^ (N - 1), by rw [← pow_succ', Nat.sub_add_cancel hN, hcN]⟩
  have hunit : c = 1 ∨ c = -1 := Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd)
  rcases hunit with h1 | h1
  · left
    have hit : ∀ x (j : ℕ), (⇑σ)^[j] x = x * δ ^ ((j : ℤ) * f x) := by
      intro x j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [Function.iterate_succ_apply', ih, map_mul, hf x, map_zpow, hσδ, h1, zpow_one,
          mul_assoc, ← zpow_add]
        congr 2
        push_cast
        ring
    ext x
    show σ x = x
    have h2 := hit x N
    rw [hfin] at h2
    have h3 : x * δ ^ ((N : ℤ) * f x) = x * 1 := by rw [mul_one]; exact h2.symm
    have h4 : (N : ℤ) * f x = 0 := hδ _ (mul_left_cancel h3)
    have h5 : f x = 0 := by
      rcases mul_eq_zero.mp h4 with h5 | h5
      · omega
      · exact h5
    rw [hf x, h5, zpow_zero, mul_one]
  · right
    refine ⟨by rw [hσδ, h1, zpow_neg, zpow_one], fun x => ?_⟩
    rw [hf x, map_mul, hf x, map_zpow, hσδ, h1, ← zpow_mul, mul_assoc, ← zpow_add]
    simp

/-- **Uniqueness of the reflection.** Two involutions moving `X` along `ℤδ` and inverting `δ`,
whose product has finite order, coincide. Hence a finite group of such automorphisms has order
`≤ 2`: this is `|W_Z| ≤ 2` for the rank-one Levi. -/
theorem reflection_unique {σ' : X ≃* X} (h : AlongLine σ δ) (h' : AlongLine σ' δ)
    (hσ : σ δ = δ⁻¹) (hσ' : σ' δ = δ⁻¹) (hinv : ∀ x, σ (σ x) = x)
    {N : ℕ} (hN : 0 < N) (hfin : ∀ x, (⇑(σ'.trans σ))^[N] x = x) : σ = σ' := by
  set τ : X ≃* X := σ'.trans σ with hτ
  have hτapp : ∀ x, τ x = σ (σ' x) := fun x => rfl
  have hτline : AlongLine τ δ := by
    intro x
    obtain ⟨m, hm⟩ := h' x
    obtain ⟨m', hm'⟩ := h x
    refine ⟨m' - m, ?_⟩
    rw [hτapp, hm, map_mul, hm', map_zpow, hσ, inv_zpow', mul_assoc, ← zpow_add,
      sub_eq_add_neg]
  rcases eq_one_or_reflection hδ hτline hN hfin with h1 | ⟨h1, -⟩
  · ext x
    have h2 : σ (σ' x) = x := by
      have := congrArg (fun e : X ≃* X => e x) h1
      exact this
    calc σ x = σ (σ (σ' x)) := by rw [h2]
      _ = σ' x := hinv _
  · exfalso
    have h2 : τ δ = δ := by rw [hτapp, hσ', map_inv, hσ, inv_inv]
    rw [h2] at h1
    have h3 : δ ^ (2 : ℤ) = 1 := by
      rw [zpow_two]
      nth_rw 2 [h1]
      exact mul_inv_cancel δ
    have := hδ 2 h3
    omega

end

end AlgMag.Reductive.RankOneJoint

#print axioms AlgMag.Reductive.RankOneJoint.eq_one_or_reflection
#print axioms AlgMag.Reductive.RankOneJoint.reflection_unique
