/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec12PrintedLocal
import Mathlib.FieldTheory.IsAlgClosed.Classification

/-!
# Generic points of `𝔸(N)` of bounded size

`exists_generic_point_small` is `AlgMag.Sec12Printed.exists_generic_point` (Sec12Final.lean) with a
bound on the field `L`, so that `Spec L` belongs to the big fppf site. Used for Proposition 12.2 (i)
for algebraic spaces, `AlgMag/Sec12Spaces.lean`.
-/

suppress_compilation

open scoped Classical

universe u

namespace AlgMag.Sec12Spaces

open AlgMag.Sec12Printed

section GenericPoint

variable {K : Type u} [Field K] {M : Type u} [AddCommGroup M] (N : AddSubmonoid M)

/-- `X^n ↦ X^n` for `a₀(n) ≠ 0`, `X^n ↦ 0` otherwise. -/
def suppHom (a₀ : Multiplicative N →* K) : AddMonoidAlgebra K N →ₐ[K] AddMonoidAlgebra K M :=
  AddMonoidAlgebra.lift K (AddMonoidAlgebra K M) N
    { toFun := fun n => if a₀ n = 0 then 0 else AddMonoidAlgebra.single ((Multiplicative.toAdd n : N) : M) 1
      map_one' := by
        rw [if_neg (by simp)]
        rfl
      map_mul' := fun a b => by
        by_cases ha : a₀ a = 0
        · simp [ha]
        by_cases hb : a₀ b = 0
        · simp [hb]
        rw [if_neg ha, if_neg hb, if_neg (by simpa [map_mul] using ⟨ha, hb⟩),
          AddMonoidAlgebra.single_mul_single]
        simp }

lemma suppHom_single (a₀ : Multiplicative N →* K) (n : N) (c : K) :
    suppHom N a₀ (AddMonoidAlgebra.single n c) =
      if a₀ (Multiplicative.ofAdd n) = 0 then 0 else AddMonoidAlgebra.single (n : M) c := by
  rw [suppHom, AddMonoidAlgebra.lift_single]
  by_cases h : a₀ (Multiplicative.ofAdd n) = 0
  · simp [h]
  · simp [h, AddMonoidAlgebra.smul_single]

/-- `AlgMag.Sec12Printed.exists_generic_point` with `#L ≤ max ℵ₀ (#K[M])`. -/
theorem exists_generic_point_small (a₀ : Multiplicative N →* K) (e : AddMonoidAlgebra K N →ₐ[K] K)
    (he : ∀ n : N, a₀ (Multiplicative.ofAdd n) = 0 → e (AddMonoidAlgebra.single n 1) = 0) :
    ∃ (L : Type u) (_ : Field L) (_ : IsAlgClosed L) (ι : K →+* L)
      (ξ : AddMonoidAlgebra K N →+* L) (χ : Multiplicative M →* Lˣ),
      Cardinal.mk L ≤ max Cardinal.aleph0 (Cardinal.mk (AddMonoidAlgebra K M)) ∧
      (∀ c, ξ (algebraMap K _ c) = ι c) ∧ (∀ t, ξ t = 0 → e t = 0) ∧
      ∀ n : N, ι (a₀ (Multiplicative.ofAdd n)) =
        (χ (Multiplicative.ofAdd (n : M)) : L) * ξ (AddMonoidAlgebra.single n 1) := by
  let B := AddMonoidAlgebra K M
  let r := suppHom N a₀
  -- a linear form on `K[M]` through which `e` factors
  let g : M → K := fun m => if h : m ∈ N then e (AddMonoidAlgebra.single ⟨m, h⟩ 1) else 0
  let e' : B →ₗ[K] K := (Finsupp.linearCombination K g).comp
    (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap
  have he' : ∀ t, e' (r t) = e t := by
    intro t
    induction t using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | single n c =>
      change e' (suppHom N a₀ _) = _
      rw [suppHom_single]
      have hs : AddMonoidAlgebra.single n c = c • AddMonoidAlgebra.single n (1 : K) := by
        simp [AddMonoidAlgebra.smul_single]
      by_cases h : a₀ (Multiplicative.ofAdd n) = 0
      · rw [if_pos h, map_zero, hs, map_smul, he n h, smul_zero]
      · rw [if_neg h, hs, map_smul]
        change Finsupp.linearCombination K g ((AddMonoidAlgebra.single (n : M) c).coeff) =
          c • e (AddMonoidAlgebra.single n 1)
        rw [AddMonoidAlgebra.coeff_single, Finsupp.linearCombination_single]
        simp [g]
  let P : Ideal (AddMonoidAlgebra K N) := RingHom.ker e.toRingHom
  have hP : P.IsPrime := RingHom.ker_isPrime _
  let Tm : Submonoid B := P.primeCompl.map (r : AddMonoidAlgebra K N →* B)
  have hdisj : Disjoint ((⊥ : Ideal B) : Set B) (Tm : Set B) := by
    rw [Set.disjoint_left]
    rintro x hx ⟨t, ht, rfl⟩
    have h0 : r t = 0 := hx
    exact ht (show e t = 0 by rw [← he', h0, map_zero])
  obtain ⟨q, hq, -, hqd⟩ := Ideal.exists_le_prime_disjoint _ _ hdisj
  let F := FractionRing (B ⧸ q)
  let L : Type u := AlgebraicClosure F
  let π : B →+* L := (algebraMap F L).comp ((algebraMap (B ⧸ q) F).comp (Ideal.Quotient.mk q))
  have hπ : ∀ b, π b = 0 → b ∈ q := by
    intro b hb
    have h1 : algebraMap (B ⧸ q) F (Ideal.Quotient.mk q b) = 0 :=
      (map_eq_zero_iff _ (algebraMap F L).injective).1 hb
    have h2 : Ideal.Quotient.mk q b = 0 :=
      (map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 h1
    exact Ideal.Quotient.eq_zero_iff_mem.1 h2
  have hunit : ∀ m : M, π (AddMonoidAlgebra.single m 1) ≠ 0 := by
    intro m h0
    have : π (AddMonoidAlgebra.single m 1) * π (AddMonoidAlgebra.single (-m) 1) = 1 := by
      rw [← map_mul, AddMonoidAlgebra.single_mul_single, add_neg_cancel, mul_one]
      exact map_one π
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  let ι : K →+* L := π.comp (algebraMap K B)
  let ξ : AddMonoidAlgebra K N →+* L := π.comp (r : AddMonoidAlgebra K N →+* B)
  have hξ : ∀ n : N, a₀ (Multiplicative.ofAdd n) ≠ 0 →
      ξ (AddMonoidAlgebra.single n 1) = π (AddMonoidAlgebra.single (n : M) 1) := by
    intro n hn
    change π (suppHom N a₀ _) = _
    rw [suppHom_single, if_neg hn]
  let G : AddSubmonoid M :=
    { carrier := {m | ∃ h : m ∈ N, a₀ (Multiplicative.ofAdd ⟨m, h⟩) ≠ 0}
      zero_mem' := ⟨N.zero_mem, by
        have : a₀ 1 = 1 := map_one a₀
        exact fun h => one_ne_zero (this.symm.trans h)⟩
      add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨N.add_mem ha hb, ?_⟩
        have : a₀ (Multiplicative.ofAdd ⟨a + b, N.add_mem ha hb⟩) =
            a₀ (Multiplicative.ofAdd ⟨a, ha⟩) * a₀ (Multiplicative.ofAdd ⟨b, hb⟩) := by
          rw [← map_mul]
          rfl
        rw [this]
        exact mul_ne_zero ha' hb' }
  have hιne : ∀ c : K, c ≠ 0 → ι c ≠ 0 := fun c hc => (map_ne_zero ι).2 hc
  let ξu : Multiplicative G →* Lˣ :=
    { toFun := fun g =>
        Units.mk0 (ι (a₀ (Multiplicative.ofAdd ⟨_, (Multiplicative.toAdd g).2.choose⟩)) /
          π (AddMonoidAlgebra.single ((Multiplicative.toAdd g : G) : M) 1))
          (div_ne_zero (hιne _ (Multiplicative.toAdd g).2.choose_spec) (hunit _))
      map_one' := by
        refine Units.ext ?_
        have e1 : a₀ (Multiplicative.ofAdd ⟨((Multiplicative.toAdd (1 : Multiplicative G) : G) : M),
            (Multiplicative.toAdd (1 : Multiplicative G)).2.choose⟩) = 1 := map_one a₀
        have e2 : π (AddMonoidAlgebra.single ((Multiplicative.toAdd (1 : Multiplicative G) : G) : M) 1) = 1 :=
          map_one π
        simp only [Units.val_mk0, Units.val_one]
        rw [e1, e2, map_one, div_one]
      map_mul' := fun a b => by
        refine Units.ext ?_
        simp only [Units.val_mk0, Units.val_mul]
        have e1 : a₀ (Multiplicative.ofAdd ⟨((Multiplicative.toAdd (a * b) : G) : M),
            (Multiplicative.toAdd (a * b)).2.choose⟩) =
            a₀ (Multiplicative.ofAdd ⟨_, (Multiplicative.toAdd a).2.choose⟩) *
            a₀ (Multiplicative.ofAdd ⟨_, (Multiplicative.toAdd b).2.choose⟩) := by
          rw [← map_mul]
          rfl
        have e2 : π (AddMonoidAlgebra.single ((Multiplicative.toAdd (a * b) : G) : M) 1) =
            π (AddMonoidAlgebra.single ((Multiplicative.toAdd a : G) : M) 1) *
            π (AddMonoidAlgebra.single ((Multiplicative.toAdd b : G) : M) 1) := by
          rw [← map_mul, AddMonoidAlgebra.single_mul_single, mul_one]
          rfl
        rw [e1, e2, map_mul, mul_div_mul_comm] }
  have hdiv : ∀ (u : Lˣ) (n : ℕ), n ≠ 0 → ∃ v : Lˣ, v ^ n = u := by
    intro u n hn
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : L) (Nat.pos_of_ne_zero hn)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hn] at hz
      exact u.ne_zero hz.symm
    exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩
  obtain ⟨χ, hχ⟩ := exists_ext_units hdiv G ξu
  obtain ⟨χ, hχ⟩ := exists_ext_units hdiv G ξu
  refine ⟨L, inferInstance, inferInstance, ι, ξ, χ, ?_, ?_, ?_, ?_⟩
  · have hF : Cardinal.mk F ≤ Cardinal.mk (B ⧸ q) :=
      IsLocalization.cardinalMk_le (nonZeroDivisors (B ⧸ q))
    have hq : Cardinal.mk (B ⧸ q) ≤ Cardinal.mk B :=
      Cardinal.mk_le_of_surjective (Ideal.Quotient.mk_surjective (I := q))
    have hL : Cardinal.mk L ≤ max (Cardinal.mk F) Cardinal.aleph0 :=
      Algebra.IsAlgebraic.cardinalMk_le_max F L
    rw [max_comm]
    exact hL.trans (max_le_max (hF.trans hq) le_rfl)
  · intro c
    change π (r (algebraMap K _ c)) = π (algebraMap K B c)
    rw [AlgHom.commutes]
  · intro t ht
    by_contra hne
    have hm : r t ∈ (Tm : Set B) := ⟨t, hne, rfl⟩
    exact Set.disjoint_left.1 hqd (hπ _ ht) hm
  · intro n
    by_cases h : a₀ (Multiplicative.ofAdd n) = 0
    · have : ξ (AddMonoidAlgebra.single n 1) = 0 := by
        change π (suppHom N a₀ _) = _
        rw [suppHom_single, if_pos h, map_zero]
      rw [h, this, map_zero, mul_zero]
    · let g : G := ⟨n, n.2, h⟩
      have e1 := hχ g
      rw [hξ n h]
      have e2 : ((χ (Multiplicative.ofAdd (n : M))) : L) =
          ι (a₀ (Multiplicative.ofAdd ⟨_, g.2.choose⟩)) / π (AddMonoidAlgebra.single (n : M) 1) :=
        congrArg Units.val e1
      rw [e2, div_mul_cancel₀ _ (hunit _)]

end GenericPoint

#print axioms exists_generic_point_small

end AlgMag.Sec12Spaces
