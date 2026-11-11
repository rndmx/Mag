/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDR3AsmFib

/-!
# Lemma D, Step 6: `SDExist_isolate` for `d - c ∈ 𝔯`, and auxiliary algebra

For Props. 3.31 (ii), 3.32 (ii) of `Algebraic Magnetism`: the element `d - c`, with `c ∉ q`.
-/

open TensorProduct

universe u

namespace AlgMag.SD

open AlgMag.SQ

section Isolate

variable {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]

/-- `SDExist_isolate`, generalized as in G2: `d - c ∈ 𝔯`, with `c ∉ q`. -/
theorem SDR3Asm_isolate {d : C} (hd : IsIntegral R d) (q : Ideal R) [q.IsPrime] (𝔯 : Ideal C) [𝔯.IsPrime]
    (h𝔯 : 𝔯.comap (algebraMap R C) = q) {c : R} (hc : c ∉ q) (hd1 : d - algebraMap R C c ∈ 𝔯) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R') (P : Ideal R') (_ : P.IsPrime)
      (_ : P.LiesOver q) (e₀ : R' ⊗[R] Algebra.adjoin R {d}) (_ : IsIdempotentElem e₀)
      (P' : Ideal (R' ⊗[R] Algebra.adjoin R {d})) (_ : P'.IsPrime) (_ : P'.LiesOver P),
      e₀ ∉ P' ∧ ((1 : R') ⊗ₜ[R] (⟨d, Algebra.self_mem_adjoin_singleton R d⟩ : Algebra.adjoin R {d}) -
          algebraMap R (R' ⊗[R] Algebra.adjoin R {d}) c) ∈ P' ∧
      (∀ P'' : Ideal (R' ⊗[R] Algebra.adjoin R {d}), P''.IsPrime → P''.LiesOver P → e₀ ∉ P'' → P'' = P') ∧
      ∃ h, h ∉ P ∧ ∃ u, (algebraMap R' _ h) * e₀ =
        u * ((1 : R') ⊗ₜ[R] (⟨d, Algebra.self_mem_adjoin_singleton R d⟩ : Algebra.adjoin R {d})) * e₀ := by
  let E := Algebra.adjoin R {d}
  let dE : E := ⟨d, Algebra.self_mem_adjoin_singleton R d⟩
  haveI : Module.Finite R E := Module.Finite.iff_fg.2 hd.fg_adjoin_singleton
  let x : Ideal E := 𝔯.comap E.val.toRingHom
  haveI : x.IsPrime := Ideal.comap_isPrime _ _
  haveI : x.LiesOver q := ⟨by
    rw [← h𝔯]
    rfl⟩
  obtain ⟨R', _, _, _, P, _, hP, e, he, P', _, hP', hP'x, heP', -, -, huniq⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq (R := R) (S := E) q x
  have hd1' : (1 : R') ⊗ₜ[R] dE - algebraMap R (R' ⊗[R] E) c ∈ P' := by
    have : dE - algebraMap R E c ∈ x := hd1
    rw [← hP'x] at this
    have e' : (1 : R') ⊗ₜ[R] dE - algebraMap R (R' ⊗[R] E) c =
        (Algebra.TensorProduct.includeRight : E →ₐ[R] R' ⊗[R] E) (dE - algebraMap R E c) := by
      rw [map_sub, AlgHom.commutes]
      rfl
    rw [e']
    exact this
  refine ⟨R', inferInstance, inferInstance, inferInstance, P, inferInstance, hP, e, he, P', inferInstance, hP', heP', hd1', huniq, ?_⟩
  let D : R' ⊗[R] E := (1 : R') ⊗ₜ[R] dE
  let J : Ideal (R' ⊗[R] E) := Ideal.span {D, 1 - e}
  have hcP' : algebraMap R (R' ⊗[R] E) c ∉ P' := by
    intro hm
    have h1 : algebraMap R' (R' ⊗[R] E) (algebraMap R R' c) ∈ P' := by
      rw [← IsScalarTower.algebraMap_apply]
      exact hm
    have h2 : algebraMap R R' c ∈ P := by
      rw [hP'.over]
      exact h1
    have h3 : c ∈ q := by
      rw [hP.over]
      exact h2
    exact hc h3
  have hle : J.comap (algebraMap R' (R' ⊗[R] E)) ≤ P → False := by
    intro hle
    obtain ⟨Q, hJQ, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P J hle
    have heQ : e ∉ Q := fun hm => (Ideal.ne_top_iff_one Q).1 hQ.ne_top (by
      have := Q.add_mem hm (hJQ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)))
      simpa using this)
    have hQe : Q = P' := huniq Q hQ ⟨hQP.symm⟩ heQ
    have hDQ : D ∈ P' := hQe ▸ hJQ (Ideal.subset_span (Set.mem_insert _ _))
    exact hcP' (by simpa [D] using P'.sub_mem hDQ hd1')
  obtain ⟨h, hhJ, hhP⟩ : ∃ h, h ∈ J.comap (algebraMap R' (R' ⊗[R] E)) ∧ h ∉ P := by
    by_contra hcon
    push Not at hcon
    exact hle hcon
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 (Ideal.mem_comap.1 hhJ)
  refine ⟨h, hhP, u, ?_⟩
  rw [← huv, add_mul, mul_assoc v, sub_mul, one_mul, he.eq, sub_self, mul_zero, add_zero]

/-- Every element of `R' ⊗ R[d]` is, modulo `1 ⊗ d - c`, in `R'`. -/
theorem SDR3Asm_generated {R' : Type u} [CommRing R'] [Algebra R R'] (d : C) (c : R)
    (w : R' ⊗[R] Algebra.adjoin R {d}) :
    ∃ r : R', w - r ⊗ₜ[R] (1 : Algebra.adjoin R {d}) ∈ Ideal.span {(1 : R') ⊗ₜ[R]
      (⟨d, Algebra.self_mem_adjoin_singleton R d⟩ : Algebra.adjoin R {d}) -
        algebraMap R (R' ⊗[R] Algebra.adjoin R {d}) c} := by
  set J := Ideal.span {(1 : R') ⊗ₜ[R] (⟨d, Algebra.self_mem_adjoin_singleton R d⟩ : Algebra.adjoin R {d}) -
        algebraMap R (R' ⊗[R] Algebra.adjoin R {d}) c} with hJ
  have key : ∀ y : Algebra.adjoin R {d}, ∃ r : R,
      (1 : R') ⊗ₜ[R] y - algebraMap R (R' ⊗[R] Algebra.adjoin R {d}) r ∈ J := by
    rintro ⟨y, hy⟩
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      obtain rfl := Set.mem_singleton_iff.1 hx
      exact ⟨c, Ideal.subset_span rfl⟩
    | algebraMap r =>
      refine ⟨r, ?_⟩
      have : (1 : R') ⊗ₜ[R] (⟨algebraMap R C r, Subalgebra.algebraMap_mem _ r⟩ : Algebra.adjoin R {d}) =
          algebraMap R (R' ⊗[R] Algebra.adjoin R {d}) r :=
        (Algebra.TensorProduct.includeRight (R := R) (A := R') (B := Algebra.adjoin R {d})).commutes r
      rw [this, sub_self]
      exact J.zero_mem
    | add x y hx hy ihx ihy =>
      obtain ⟨r, hr⟩ := ihx
      obtain ⟨s, hs⟩ := ihy
      refine ⟨r + s, ?_⟩
      have := J.add_mem hr hs
      convert this using 1
      rw [map_add, sub_add_sub_comm, ← TensorProduct.tmul_add]
      rfl
    | mul x y hx hy ihx ihy =>
      obtain ⟨r, hr⟩ := ihx
      obtain ⟨s, hs⟩ := ihy
      refine ⟨r * s, ?_⟩
      have := J.add_mem (J.mul_mem_left ((1 : R') ⊗ₜ[R] (⟨y, hy⟩ : Algebra.adjoin R {d})) hr)
        (J.mul_mem_left (algebraMap R (R' ⊗[R] Algebra.adjoin R {d}) r) hs)
      convert this using 1
      have e1 : (1 : R') ⊗ₜ[R] (⟨x * y, mul_mem hx hy⟩ : Algebra.adjoin R {d}) =
          ((1 : R') ⊗ₜ[R] (⟨x, hx⟩ : Algebra.adjoin R {d})) * ((1 : R') ⊗ₜ[R] (⟨y, hy⟩ : Algebra.adjoin R {d})) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        rfl
      rw [e1, map_mul]
      ring
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add a b ha hb =>
    obtain ⟨r, hr⟩ := ha
    obtain ⟨s, hs⟩ := hb
    refine ⟨r + s, ?_⟩
    have := J.add_mem hr hs
    convert this using 1
    rw [TensorProduct.add_tmul]
    ring
  | tmul a y =>
    obtain ⟨r, hr⟩ := key y
    refine ⟨a * algebraMap R R' r, ?_⟩
    have := J.mul_mem_left (a ⊗ₜ[R] (1 : Algebra.adjoin R {d})) hr
    convert this using 1
    rw [mul_sub, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]

end Isolate

section Zero

variable {Γ R B C : Type u} [AddCommGroup Γ] [CommRing R] [CommRing B] [CommRing C] [Algebra B C]
  {cB : Coact B Γ} {cC : Coact C Γ} {ι : R →+* B}

/-- An element of degree `0` integral over `B` is integral over `B₀ = R`. -/
theorem SDR3Asm_integral_zero (hg : SDExist_IsGraded cB cC) (hι : cB.IsInv ι) {x : C} (hx : cC.IsHom 0 x)
    (hint : IsIntegral B x) : ((algebraMap B C).comp ι).IsIntegralElem x := by
  obtain ⟨p, hp, h0⟩ := hint
  let n := p.natDegree
  let q : Polynomial R := ∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (hι.r (p.coeff i))
  have hcq : ∀ i, q.coeff i = if i ∈ Finset.range (n + 1) then hι.r (p.coeff i) else 0 := by
    intro i
    simp only [q, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
  have hr1 : hι.r 1 = 1 := hι.inj (by
    rw [hι.ι_r, map_one]
    exact cB.comp_self_of_isHom (map_one cB.σ))
  have hmonic : q.Monic := by
    refine Polynomial.monic_of_natDegree_le_of_coeff_eq_one n ?_ ?_
    · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
      exact (Polynomial.natDegree_monomial_le _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
    · rw [hcq, if_pos (Finset.self_mem_range_succ n)]
      have : p.coeff n = 1 := hp
      rw [this, hr1]
  refine ⟨q, hmonic, ?_⟩
  have hsum : Polynomial.eval₂ (algebraMap B C) x p = 0 := h0
  rw [Polynomial.eval₂_eq_sum_range] at hsum
  have hc := congrArg (cC.comp 0) hsum
  have hcomp : ∀ (b : B) (i : ℕ), cC.comp 0 (algebraMap B C b * x ^ i) = algebraMap B C (ι (hι.r b)) * x ^ i := by
    intro b i
    have hxi : cC.IsHom 0 (x ^ i) := by simpa using hx.pow i
    rw [mul_comm, cC.comp_mul_of_isHom hxi, sub_self, hg, hι.ι_r, mul_comm]
  have hadd : ∀ s : Finset ℕ, cC.comp 0 (∑ i ∈ s, algebraMap B C (p.coeff i) * x ^ i) =
      ∑ i ∈ s, algebraMap B C (ι (hι.r (p.coeff i))) * x ^ i := by
    intro s
    induction s using Finset.cons_induction with
    | empty => simp [Coact.comp]
    | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, cC.comp_add, ih, hcomp]
  rw [hadd] at hc
  have h00 : cC.comp 0 (0 : C) = 0 := by simp [Coact.comp]
  rw [h00] at hc
  rw [Polynomial.eval₂_eq_sum_range' _ (n := n + 1)]
  · rw [← hc]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hcq, if_pos hi]
    rfl
  · exact Nat.lt_succ_of_le (Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi =>
      (Polynomial.natDegree_monomial_le _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)))

end Zero

section Etale

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]

/-- `C_{ab}` is étale over `B` when `C_a` is. -/
theorem SDR3Asm_etale_mul (a b : C) [Algebra.Etale B (Localization.Away a)] :
    Algebra.Etale B (Localization.Away (a * b)) := by
  let Ca := Localization.Away a
  let L := Localization.Away (algebraMap C Ca b)
  haveI : IsLocalization.Away (a * b) L := IsLocalization.Away.mul' Ca L a b
  haveI : Algebra.Etale Ca L := Algebra.Etale.of_isLocalizationAway (algebraMap C Ca b)
  haveI : Algebra.Etale B L := Algebra.Etale.comp B Ca L
  exact Algebra.Etale.of_equiv
    ((IsLocalization.algEquiv (Submonoid.powers (a * b)) L (Localization.Away (a * b))).restrictScalars B)

end Etale

end AlgMag.SD
