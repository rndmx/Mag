/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDR3AsmAlg

/-!
# Lemma D, Step 7: the two idempotents agree on the fibre

For Props. 3.31 (ii), 3.32 (ii) of `Algebraic Magnetism`. The argument is run
elementwise, with an ideal `𝔍` and a multiplicative set `W`.
-/

open TensorProduct

universe u

namespace AlgMag.SD

section Star

variable {S : Type u} [CommRing S] (W : Submonoid S) (𝔍 : Ideal S)

/-- An element in all primes containing `𝔍` and missing `W` is nilpotent modulo `𝔍`, up to `W`. -/
lemma SDR3Asm_nil {x : S} (hx : ∀ Q : Ideal S, Q.IsPrime → 𝔍 ≤ Q → Disjoint (Q : Set S) (W : Set S) → x ∈ Q) :
    ∃ t ∈ W, ∃ n : ℕ, t * x ^ n ∈ 𝔍 := by
  by_contra hcon
  push Not at hcon
  have hdis : Disjoint (𝔍 : Set S) ((W ⊔ Submonoid.powers x : Submonoid S) : Set S) := by
    rw [Set.disjoint_left]
    intro y hy hyW
    obtain ⟨t, ht, p, ⟨n, rfl⟩, rfl⟩ := Submonoid.mem_sup.1 (SetLike.mem_coe.1 hyW)
    exact hcon t ht n hy
  obtain ⟨Q, hQ, hle, hd⟩ := Ideal.exists_le_prime_disjoint 𝔍 _ hdis
  have hW : Disjoint (Q : Set S) (W : Set S) :=
    hd.mono_right (fun y hy => SetLike.mem_coe.2 (Submonoid.mem_sup_left (SetLike.mem_coe.1 hy)))
  have hxQ := hx Q hQ hle hW
  exact Set.disjoint_left.1 hd hxQ (SetLike.mem_coe.2 (Submonoid.mem_sup_right (Submonoid.mem_powers x)))

lemma SDR3Asm_pow_rel {a s t : S} (h : t * (a ^ 2 - s * a) ∈ 𝔍) (n : ℕ) : t * (a ^ (n + 1) - s ^ n * a) ∈ 𝔍 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := 𝔍.add_mem (𝔍.mul_mem_left a ih) (𝔍.mul_mem_left (s ^ n) h)
    convert this using 1
    ring

/-- **Step 7**, the core. `F/s'` and `e` are the two idempotents, `D - c` cuts out the same primes. -/
theorem SDR3Asm_star {e F Dt h s' : S} (he : IsIdempotentElem e) (hh : h ∈ W) (hs : s' ∈ W)
    (hr1 : ∃ t ∈ W, t * (Dt - h * F) ∈ 𝔍) (hr2 : ∃ t ∈ W, t * (F ^ 2 - s' * F) ∈ 𝔍)
    (U1 : ∀ Q : Ideal S, Q.IsPrime → 𝔍 ≤ Q → Disjoint (Q : Set S) (W : Set S) → e ∉ Q → Dt - h * s' ∈ Q)
    (U2 : ∀ Q : Ideal S, Q.IsPrime → 𝔍 ≤ Q → Disjoint (Q : Set S) (W : Set S) → Dt - h * s' ∈ Q → e ∉ Q) :
    ∃ t ∈ W, t * (s' * e - F) ∈ 𝔍 := by
  obtain ⟨t₁, ht₁, h1⟩ := hr1
  obtain ⟨t₂, ht₂, h2⟩ := hr2
  have nW : ∀ {Q : Ideal S}, Disjoint (Q : Set S) (W : Set S) → ∀ {t}, t ∈ W → t ∉ Q := fun hd _ ht hm =>
    Set.disjoint_left.1 hd hm ht
  have hDF : ∀ Q : Ideal S, Q.IsPrime → 𝔍 ≤ Q → Disjoint (Q : Set S) (W : Set S) → Dt - h * F ∈ Q := by
    intro Q hQ hle hd
    exact (hQ.mem_or_mem (hle h1)).resolve_left (nW hd ht₁)
  have hFF : ∀ Q : Ideal S, Q.IsPrime → 𝔍 ≤ Q → Disjoint (Q : Set S) (W : Set S) → F * (F - s') ∈ Q := by
    intro Q hQ hle hd
    have : t₂ * (F * (F - s')) ∈ Q := by
      convert hle h2 using 1
      ring
    exact (hQ.mem_or_mem this).resolve_left (nW hd ht₂)
  -- first idempotent difference
  have hx1 : ∀ Q : Ideal S, Q.IsPrime → 𝔍 ≤ Q → Disjoint (Q : Set S) (W : Set S) → e * (s' - F) ∈ Q := by
    intro Q hQ hle hd
    by_cases heQ : e ∈ Q
    · exact Q.mul_mem_right _ heQ
    · have h3 := U1 Q hQ hle hd heQ
      have h4 := Q.sub_mem (hDF Q hQ hle hd) h3
      have h5 : h * (s' - F) ∈ Q := by
        convert h4 using 1
        ring
      exact Q.mul_mem_left _ ((hQ.mem_or_mem h5).resolve_left (nW hd hh))
  have hx2 : ∀ Q : Ideal S, Q.IsPrime → 𝔍 ≤ Q → Disjoint (Q : Set S) (W : Set S) → (1 - e) * F ∈ Q := by
    intro Q hQ hle hd
    by_cases hFQ : F ∈ Q
    · exact Q.mul_mem_left _ hFQ
    · have h3 := (hQ.mem_or_mem (hFF Q hQ hle hd)).resolve_left hFQ
      have h4 : Dt - h * s' ∈ Q := by
        have := Q.add_mem (hDF Q hQ hle hd) (Q.mul_mem_left h h3)
        convert this using 1
        ring
      have h5 := U2 Q hQ hle hd h4
      have h6 : e * (1 - e) ∈ Q := by
        rw [mul_sub, mul_one, he.eq, sub_self]
        exact Q.zero_mem
      exact Q.mul_mem_right _ ((hQ.mem_or_mem h6).resolve_left h5)
  obtain ⟨t₃, ht₃, n, hn⟩ := SDR3Asm_nil W 𝔍 hx1
  obtain ⟨t₄, ht₄, m, hm⟩ := SDR3Asm_nil W 𝔍 hx2
  have hpe : ∀ k : ℕ, e ^ (k + 1) = e := fun k => he.pow_succ_eq k
  have hpe' : ∀ k : ℕ, (1 - e) ^ (k + 1) = 1 - e := fun k => he.one_sub.pow_succ_eq k
  have ha : t₂ * ((s' - F) ^ 2 - s' * (s' - F)) ∈ 𝔍 := by
    convert h2 using 2
    ring
  have hA := SDR3Asm_pow_rel 𝔍 ha n
  have hB := SDR3Asm_pow_rel 𝔍 h2 m
  -- raise powers by one
  have hn' : t₃ * (e * (s' - F)) ^ (n + 1) ∈ 𝔍 := by
    rw [pow_succ, ← mul_assoc]
    exact 𝔍.mul_mem_right _ hn
  have hm' : t₄ * ((1 - e) * F) ^ (m + 1) ∈ 𝔍 := by
    rw [pow_succ, ← mul_assoc]
    exact 𝔍.mul_mem_right _ hm
  rw [mul_pow, hpe] at hn'
  rw [mul_pow, hpe'] at hm'
  have hT1 : t₂ * t₃ * s' ^ n * (e * (s' - F)) ∈ 𝔍 := by
    have := 𝔍.sub_mem (𝔍.mul_mem_left t₂ hn') (𝔍.mul_mem_left (t₃ * e) hA)
    convert this using 1
    ring
  have hT2 : t₂ * t₄ * s' ^ m * ((1 - e) * F) ∈ 𝔍 := by
    have := 𝔍.sub_mem (𝔍.mul_mem_left t₂ hm') (𝔍.mul_mem_left (t₄ * (1 - e)) hB)
    convert this using 1
    ring
  refine ⟨t₂ * t₃ * s' ^ n * (t₂ * t₄ * s' ^ m), W.mul_mem (W.mul_mem (W.mul_mem ht₂ ht₃) (W.pow_mem hs n))
    (W.mul_mem (W.mul_mem ht₂ ht₄) (W.pow_mem hs m)), ?_⟩
  have := 𝔍.sub_mem (𝔍.mul_mem_right (t₂ * t₄ * s' ^ m) hT1) (𝔍.mul_mem_left (t₂ * t₃ * s' ^ n) hT2)
  convert this using 1
  ring

end Star

end AlgMag.SD
