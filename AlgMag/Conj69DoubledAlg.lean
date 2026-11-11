/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

set_option linter.style.haveILetI false

/-!
# Algebra for the plane with doubled origin

`R` flat over `k[x, y]` with a prime containing `x, y`: no relation
`(xy)^K (x^n y^m - x^(n+1) b - y^(m+1) a) = 0`. This is what excludes an affine punctured neighbourhood.
-/

open MvPolynomial

universe u

namespace AlgMag.Conj69

variable {k : Type u} [Field k]

/-- The polynomial ring in two variables. -/
abbrev A2 (k : Type u) [Field k] : Type u := MvPolynomial (Fin 2) k

lemma isRelPrime_pow (a b : ℕ) :
    IsRelPrime ((X 0 : A2 k) ^ a) ((X 1 : A2 k) ^ b) := by
  have h0 : Prime (X 0 : A2 k) := X_prime
  have h1 : Prime (X 1 : A2 k) := X_prime
  have : IsRelPrime (X 0 : A2 k) (X 1 : A2 k) :=
    (h0.irreducible.isRelPrime_iff_not_dvd).2 fun h => by
      have := (X_dvd_X (R := k)).1 h
      exact absurd this (by decide)
  exact (this.pow_left).pow_right

/-- Flatness: a relation `f s = g r` with `f, g` relatively prime forces `g ∣ s`. -/
lemma flat_dvd {A L : Type u} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
    [CommRing L] [Algebra A L] [Module.Flat A L] {f g : A} (hfg : IsRelPrime f g)
    {s r : L} (h : algebraMap A L f * s = algebraMap A L g * r) :
    ∃ t, s = algebraMap A L g * t := by
  classical
  let F : Fin 2 → A := ![f, -g]
  let x : Fin 2 → L := ![s, r]
  have hrel : ∑ i, F i • x i = 0 := by
    simp [F, x, Fin.sum_univ_two, Algebra.smul_def, h]
  obtain ⟨κ, a, y, hx, hF⟩ := (Module.Flat.iff_forall_isTrivialRelation (R := A) (M := L)).1 inferInstance hrel
  have hdvd : ∀ j, g ∣ a 0 j := fun j => by
    have h2 := hF j
    simp only [Fin.sum_univ_two, F, Matrix.cons_val_zero, Matrix.cons_val_one, neg_mul] at h2
    have h3 : g ∣ f * a 0 j := ⟨a 1 j, by linear_combination h2⟩
    exact hfg.symm.dvd_of_dvd_mul_left h3
  choose c hc using hdvd
  refine ⟨∑ j, c j • y j, ?_⟩
  have := hx 0
  simp only [x, Matrix.cons_val_zero] at this
  rw [this, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hc j, ← Algebra.smul_def, smul_smul]

/-- In a flat algebra over a domain, nonzero elements act injectively. -/
lemma flat_cancel {A L : Type u} [CommRing A] [IsDomain A] [CommRing L] [Algebra A L]
    [Module.Flat A L] {f : A} (hf : f ≠ 0) {s : L} (h : algebraMap A L f * s = 0) : s = 0 := by
  have h0 : IsSMulRegular A f := fun a b hab => mul_left_cancel₀ hf hab
  have hr : IsSMulRegular L (algebraMap A L f) := h0.of_flat
  exact hr (by simpa using h)

/-- Over a flat local `k[x, y]`-algebra `L` in which `x, y` are not units, there is no relation
`(xy)^K (x^n y^m - x^(n+1) b - y^(m+1) a) = 0`. -/
theorem no_relation_local {L : Type u} [CommRing L] [IsLocalRing L] [Algebra (A2 k) L]
    [Module.Flat (A2 k) L]
    (hx : algebraMap (A2 k) L (X 0) ∈ IsLocalRing.maximalIdeal L)
    (hy : algebraMap (A2 k) L (X 1) ∈ IsLocalRing.maximalIdeal L)
    {K n m : ℕ} {a b : L}
    (h : (algebraMap (A2 k) L (X 0) * algebraMap (A2 k) L (X 1)) ^ K *
      (algebraMap (A2 k) L (X 0) ^ n * algebraMap (A2 k) L (X 1) ^ m -
        algebraMap (A2 k) L (X 0) ^ (n + 1) * b - algebraMap (A2 k) L (X 1) ^ (m + 1) * a) = 0) :
    False := by
  set x := algebraMap (A2 k) L (X 0) with hxd
  set y := algebraMap (A2 k) L (X 1) with hyd
  have h0 : ((X 0 * X 1 : A2 k) ^ K) ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (X_ne_zero 0) (X_ne_zero 1))
  have e := flat_cancel (A := A2 k) (L := L) h0 (by simpa [map_mul, map_pow, ← hxd, ← hyd] using h)
  -- `y^m (x^n - y a) = x^(n+1) b`
  have e1 : algebraMap (A2 k) L ((X 1) ^ m) * (x ^ n - y * a) =
      algebraMap (A2 k) L ((X 0) ^ (n + 1)) * b := by
    simp only [map_pow, ← hxd, ← hyd]; linear_combination e
  obtain ⟨t, ht⟩ := flat_dvd (isRelPrime_pow (n + 1) m).symm e1
  rw [map_pow, ← hxd] at ht
  have e2 : algebraMap (A2 k) L ((X 0) ^ n) * (1 - x * t) =
      algebraMap (A2 k) L ((X 1) ^ 1) * a := by
    simp only [map_pow, ← hxd, ← hyd]; linear_combination ht
  obtain ⟨c, hc⟩ := flat_dvd (isRelPrime_pow n 1) e2
  simp only [pow_one, ← hyd] at hc
  have hmem : (1 : L) ∈ IsLocalRing.maximalIdeal L := by
    have h1 : (1 : L) = x * t + y * c := by linear_combination hc
    rw [h1]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hx) (Ideal.mul_mem_right _ _ hy)
  exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal L).ne_top hmem

/-- `no_relation_local` after localizing at a prime, in tower form. -/
theorem no_relation_tower {R L : Type u} [CommRing R] [CommRing L] [Algebra (A2 k) R] [Algebra R L]
    [Algebra (A2 k) L] [IsScalarTower (A2 k) R L] [Module.Flat (A2 k) R] (q : Ideal R) [q.IsPrime]
    [IsLocalization.AtPrime L q] [IsLocalRing L]
    (hx : algebraMap (A2 k) R (X 0) ∈ q) (hy : algebraMap (A2 k) R (X 1) ∈ q) {K n m : ℕ} {a b : R}
    (h : (algebraMap (A2 k) R (X 0) * algebraMap (A2 k) R (X 1)) ^ K *
      (algebraMap (A2 k) R (X 0) ^ n * algebraMap (A2 k) R (X 1) ^ m -
        algebraMap (A2 k) R (X 0) ^ (n + 1) * b - algebraMap (A2 k) R (X 1) ^ (m + 1) * a) = 0) :
    False := by
  haveI : Module.Flat R L := IsLocalization.flat L q.primeCompl
  haveI : Module.Flat (A2 k) L := Module.Flat.trans (A2 k) R L
  have e : ∀ c, algebraMap (A2 k) L c = algebraMap R L (algebraMap (A2 k) R c) :=
    fun c => IsScalarTower.algebraMap_apply _ _ _ c
  have h' := congrArg (algebraMap R L) h
  simp only [map_mul, map_pow, map_sub, map_zero, ← e] at h'
  refine no_relation_local (k := k) (L := L) ?_ ?_ h'
  · rw [e]; exact (IsLocalization.AtPrime.to_map_mem_maximal_iff L q _).2 hx
  · rw [e]; exact (IsLocalization.AtPrime.to_map_mem_maximal_iff L q _).2 hy

/-- `no_relation_local` for a flat ring map and a prime containing `x, y`. -/
theorem no_relation {R : Type u} [CommRing R] (φ : A2 k →+* R) (hφ : φ.Flat) (q : Ideal R) [q.IsPrime]
    (hx : φ (X 0) ∈ q) (hy : φ (X 1) ∈ q) {K n m : ℕ} {a b : R}
    (h : (φ (X 0) * φ (X 1)) ^ K *
      (φ (X 0) ^ n * φ (X 1) ^ m - φ (X 0) ^ (n + 1) * b - φ (X 1) ^ (m + 1) * a) = 0) :
    False := by
  letI : Algebra (A2 k) R := φ.toAlgebra
  haveI : Module.Flat (A2 k) R := hφ
  exact no_relation_tower (k := k) (L := Localization.AtPrime q) q hx hy h

end AlgMag.Conj69
