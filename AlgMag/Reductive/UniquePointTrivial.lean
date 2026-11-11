/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Bialgebra.Basic

/-!
# A reduced finite-type bialgebra with a single rational point is trivial

Over an algebraically closed field `K`, let `B` be a reduced finite-type commutative bialgebra
whose only `K`-point is the counit. Then the kernel of the counit is zero, i.e. `B = K`.

Nullstellensatz: every maximal ideal `m` has residue field `K`, giving a `K`-point with kernel `m`;
so `m = ker ε`, and `ker ε` is the Jacobson radical of `0`, which is the nilradical, zero.
-/

namespace AlgMag.Reductive

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {B : Type u} [CommRing B] [Bialgebra K B]
  [Algebra.FiniteType K B] [IsReduced B]

omit [IsReduced B] in
/-- Every maximal ideal of `B` is the kernel of a `K`-point. -/
theorem exists_point_ker_eq (m : Ideal B) [hm : m.IsMaximal] :
    ∃ φ : B →ₐ[K] K, RingHom.ker φ = m := by
  let : Field (B ⧸ m) := Ideal.Quotient.field m
  have : IsJacobsonRing K := inferInstance
  have : Algebra.FiniteType K (B ⧸ m) := inferInstance
  have hfin : Module.Finite K (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (B ⧸ m)
  have : Algebra.IsIntegral K (B ⧸ m) := inferInstance
  let e : K ≃ₐ[K] (B ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId K (B ⧸ m))
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨(e.symm : (B ⧸ m) →ₐ[K] K).comp (Ideal.Quotient.mkₐ K m), ?_⟩
  ext x
  rw [RingHom.mem_ker]
  change e.symm (Ideal.Quotient.mk m x) = 0 ↔ x ∈ m
  rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]

/-- **Unique rational point ⇒ trivial.** -/
theorem ker_counit_eq_bot_of_unique_point
    (huniq : ∀ φ : B →ₐ[K] K, φ = Bialgebra.counitAlgHom K B) :
    RingHom.ker (Bialgebra.counitAlgHom K B) = ⊥ := by
  have : IsJacobsonRing B := isJacobsonRing_of_finiteType (A := K)
  have hjac : (⊥ : Ideal B).jacobson = ⊥ := by
    have h := IsJacobsonRing.out' (R := B) (⊥ : Ideal B)
      (fun x hx => by
          obtain ⟨n, hn⟩ := hx
          exact Ideal.mem_bot.2 (IsReduced.eq_zero x ⟨n, Ideal.mem_bot.1 hn⟩))
    exact h
  rw [eq_bot_iff, ← hjac]
  intro x hx
  rw [Ideal.jacobson, Submodule.mem_sInf]
  rintro m ⟨-, hm⟩
  obtain ⟨φ, hφ⟩ := exists_point_ker_eq (K := K) m
  rw [← hφ, huniq φ]
  exact hx

end AlgMag.Reductive
