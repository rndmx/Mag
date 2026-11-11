/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.RingTheory.Etale.QuasiFinite

/-!
# Lemma D, Step 3 (iv): isolating the closed orbit by an étale neighbourhood

Step 3 (iv) of the proof of Props. 3.31 (ii), 3.32 (ii) of `Algebraic Magnetism`,
at finite level: Stacks 00UJ for the finite algebra `R[d]` replaces the henselian decomposition of Stacks 04GG (10).
-/

open TensorProduct

universe u

namespace AlgMag.SD

variable {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]

/-- An element `d`, integral over `R`, equal to `1` at a prime `𝔯` over `q`: after an étale neighbourhood `(R', P)` of `q`,
an idempotent `e₀` of `R' ⊗ R[d]` isolates a prime `P'` over `P`, and `d` is a unit on `e₀` up to `h ∉ P`. -/
theorem SDExist_isolate {d : C} (hd : IsIntegral R d) (q : Ideal R) [q.IsPrime] (𝔯 : Ideal C) [𝔯.IsPrime]
    (h𝔯 : 𝔯.comap (algebraMap R C) = q) (hd1 : d - 1 ∈ 𝔯) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R') (P : Ideal R') (_ : P.IsPrime)
      (_ : P.LiesOver q) (e₀ : R' ⊗[R] Algebra.adjoin R {d}) (_ : IsIdempotentElem e₀)
      (P' : Ideal (R' ⊗[R] Algebra.adjoin R {d})) (_ : P'.IsPrime) (_ : P'.LiesOver P),
      e₀ ∉ P' ∧ ((1 : R') ⊗ₜ[R] (⟨d, Algebra.self_mem_adjoin_singleton R d⟩ : Algebra.adjoin R {d}) - 1) ∈ P' ∧
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
  have hd1' : (1 : R') ⊗ₜ[R] dE - 1 ∈ P' := by
    have : dE - 1 ∈ x := hd1
    rw [← hP'x] at this
    have e' : (1 : R') ⊗ₜ[R] dE - 1 =
        (Algebra.TensorProduct.includeRight : E →ₐ[R] R' ⊗[R] E) (dE - 1) := by
      rw [map_sub, map_one]
      rfl
    rw [e']
    exact this
  refine ⟨R', inferInstance, inferInstance, inferInstance, P, inferInstance, hP, e, he, P', inferInstance, hP', heP', hd1', huniq, ?_⟩
  let D : R' ⊗[R] E := (1 : R') ⊗ₜ[R] dE
  let J : Ideal (R' ⊗[R] E) := Ideal.span {D, 1 - e}
  have hle : J.comap (algebraMap R' (R' ⊗[R] E)) ≤ P → False := by
    intro hle
    obtain ⟨Q, hJQ, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P J hle
    have heQ : e ∉ Q := fun hm => (Ideal.ne_top_iff_one Q).1 hQ.ne_top (by
      have := Q.add_mem hm (hJQ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)))
      simpa using this)
    have hQe : Q = P' := huniq Q hQ ⟨hQP.symm⟩ heQ
    have hDQ : D ∈ P' := hQe ▸ hJQ (Ideal.subset_span (Set.mem_insert _ _))
    exact (Ideal.ne_top_iff_one P').1 (Ideal.IsPrime.ne_top ‹_›) (by simpa [D] using P'.sub_mem hDQ hd1')
  obtain ⟨h, hhJ, hhP⟩ : ∃ h, h ∈ J.comap (algebraMap R' (R' ⊗[R] E)) ∧ h ∉ P := by
    by_contra hcon
    push Not at hcon
    exact hle hcon
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 (Ideal.mem_comap.1 hhJ)
  refine ⟨h, hhP, u, ?_⟩
  rw [← huv, add_mul, mul_assoc v, sub_mul, one_mul, he.eq, sub_self, mul_zero, add_zero]

end AlgMag.SD

#print axioms AlgMag.SD.SDExist_isolate
