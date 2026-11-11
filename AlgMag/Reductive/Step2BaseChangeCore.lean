/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.CharpolyFinite
import AlgMag.Reductive.ClosurePower
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.BaseChange
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.PointAction

/-!
# Step 2 over `F̄_p` by base change to `K = (k(X))‾`: `Step2OverFpBar` is proved

`step2OverFpBar : Step2OverFpBar k Q` for every finite-type Hopf algebra `Q` over `k = k̄`.
In fact `NoNontrivialTorus k Q → CharpolyValuesFinite k Q` with no other hypothesis
(`charpolyValuesFinite_of_noNontrivialTorus`).

* (S2) `K := AlgebraicClosure (FractionRing k[X])` has an element not integral over `ℤ`
  (`exists_not_isIntegral`, `X` is transcendental). `NoNontrivialTorus K (K ⊗ Q)`
  (`TorusSpecialization.noNontrivialTorus_baseChange`), so semisimple parts of `K`-points of
  `K ⊗ Q` have finite order (`closurePower` + `exists_pow_isUnipotentPoint`), so charpoly
  coefficients at `K`-points are integral over `ℤ`.
* `finite_values_of_isIntegral`: Chevalley dichotomy applied on each irreducible component
  (minimal primes), so no connectedness of `Q` is needed.
* (S3) `charpoly_endOfPoint_baseChange`: the action of a `K`-point `f` of `K ⊗ Q` on
  `K ⊗ M` has the characteristic polynomial of the action on `M` of the `K`-valued point
  `f ∘ (1 ⊗ ·)` of `Q` (Tau Ceti `coefficientMatrix_baseChange`, `toMatrix_endOfPoint`).
  The `k`-values of a coefficient embed into its `K`-values, hence are finite.
-/

open Polynomial WithConv TauCeti TauCeti.HopfAlgebra
open scoped TensorProduct

namespace AlgMag.Reductive.Step2BaseChange

open AlgMag.Reductive.NoTorusUnipotent AlgMag.Reductive.CharpolyFinite

universe u

/-- A regular function whose values at `K`-points are all integral over `ℤ` takes finitely many
values, when `K = K̄` has a non-integral element. No irreducibility: apply the Chevalley
dichotomy on each of the finitely many irreducible components. -/
theorem finite_values_of_isIntegral {K A : Type u} [Field K] [IsAlgClosed K] [CommRing A]
    [Algebra K A] [Algebra.FiniteType K A] (hK : ∃ x : K, ¬ IsIntegral ℤ x) (c : A)
    (hint : ∀ f : A →ₐ[K] K, IsIntegral ℤ (f c)) :
    (Set.range fun f : A →ₐ[K] K ↦ f c).Finite := by
  classical
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  have hfin : (minimalPrimes A).Finite := minimalPrimes.finite_of_isNoetherianRing A
  have hP : ∀ P ∈ minimalPrimes A,
      (Set.range fun f : (A ⧸ P) →ₐ[K] K ↦ f (Ideal.Quotient.mk P c)).Finite := by
    intro P hP
    have : P.IsPrime := hP.1.1
    have : IsDomain (A ⧸ P) := Ideal.Quotient.isDomain P
    rcases eq_or_cofinite_values (k := K) (Ideal.Quotient.mk P c) with ⟨a, ha⟩ | ⟨p, hp, hsurj⟩
    · exact (Set.finite_singleton a).subset (by rintro _ ⟨f, rfl⟩; exact ha f)
    · exfalso
      have hint' : ∀ t : K, ¬ p.IsRoot t → IsIntegral ℤ t := fun t ht ↦ by
        obtain ⟨f, hf⟩ := hsurj t ht
        rw [← hf]
        exact hint (f.comp (Ideal.Quotient.mkₐ K P))
      exact infinite_setOf_not_isIntegral hK
        ((Polynomial.finite_setOfPred_isRoot hp).subset
          fun t ht ↦ by_contra fun h ↦ ht (hint' t h))
  refine (hfin.biUnion hP).subset ?_
  rintro _ ⟨f, rfl⟩
  have : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  obtain ⟨P, hPmin, hPle⟩ :=
    Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A)) (J := RingHom.ker f) bot_le
  refine Set.mem_biUnion hPmin ⟨Ideal.Quotient.liftₐ P f (fun a ha ↦ hPle ha), ?_⟩
  exact Ideal.Quotient.lift_mk _ _ _

/-- An element transcendental over a field `k` is not integral over `ℤ`. -/
theorem not_isIntegral_of_transcendental {k L : Type u} [Field k] [Field L] [Algebra k L]
    {x : L} (hx : Transcendental k x) : ¬ IsIntegral ℤ x :=
  fun h ↦ hx (h.tower_top (A := k)).isAlgebraic

/-- `X` is transcendental over `k` in `(k(X))‾`. -/
theorem transcendental_X_algebraicClosure (k : Type u) [Field k] :
    Transcendental k (algebraMap (FractionRing k[X]) (AlgebraicClosure (FractionRing k[X]))
      (algebraMap k[X] (FractionRing k[X]) Polynomial.X)) := by
  rw [transcendental_algebraMap_iff (algebraMap (FractionRing k[X]) _).injective,
    transcendental_algebraMap_iff (IsFractionRing.injective k[X] (FractionRing k[X]))]
  exact Polynomial.transcendental_X k

/-- Semisimple parts of `K`-points of `K ⊗ Q` have finite order, from `NoNontrivialTorus k Q`. -/
theorem semisimplePartsFiniteOrder_baseChange {k K Q : Type u} [Field k] [IsAlgClosed k]
    [Field K] [IsAlgClosed K] [Algebra k K] [CommRing Q] [HopfAlgebra k Q]
    [Algebra.FiniteType k Q] (htor : NoNontrivialTorus K (K ⊗[k] Q)) :
    SemisimplePartsFiniteOrder K (K ⊗[k] Q) := fun g ↦
  exists_pow_isUnipotentPoint htor g (ClosurePower.closurePower g)

/-- **(S3) descent.** The action of a `K`-point `f` of `K ⊗ Q` on `K ⊗ M` has the same
characteristic polynomial as the action on `M` of the `K`-valued point `f ∘ (1 ⊗ ·)` of `Q`. -/
theorem charpoly_endOfPoint_baseChange {k K Q : Type u} [Field k] [Field K] [Algebra k K]
    [CommRing Q] [HopfAlgebra k Q] (M : FGComoduleCat.{u, u, u} k Q)
    (f : K ⊗[k] Q →ₐ[K] K) :
    letI := Comodule.baseChange (R := k) (H := Q) (M := M) K
    (Comodule.endOfPoint (K ⊗[k] M) f).charpoly =
      (Comodule.endOfPoint M
        ((f.restrictScalars k).comp Algebra.TensorProduct.includeRight)).charpoly := by
  classical
  letI := Comodule.baseChange (R := k) (H := Q) (M := M) K
  let b := Module.Free.chooseBasis k M
  rw [← LinearMap.charpoly_toMatrix _ ((b.baseChange K).baseChange K),
    ← LinearMap.charpoly_toMatrix _ (b.baseChange K),
    Comodule.toMatrix_endOfPoint, Comodule.toMatrix_endOfPoint,
    Comodule.coefficientMatrix_baseChange, Matrix.map_map]
  congr 1

/-- **Step 2 for every `Q`**: without nontrivial torus, the characteristic-polynomial
coefficients take finitely many values at `k`-points. No connectedness, no integrality case
split. -/
theorem charpolyValuesFinite_of_baseChange {k Q : Type u} (K : Type u) [Field k] [IsAlgClosed k]
    [Field K] [IsAlgClosed K] [Algebra k K] [CommRing Q] [HopfAlgebra k Q]
    [Algebra.FiniteType k Q] (hK : ∃ x : K, ¬ IsIntegral ℤ x)
    (htor : NoNontrivialTorus K (K ⊗[k] Q)) :
    CharpolyValuesFinite k Q := by
  intro M i
  have hss := semisimplePartsFiniteOrder_baseChange (K := K) htor
  let c : Q := (Comodule.endOfPoint M (AlgHom.id k Q)).charpoly.coeff i
  have hval : ∀ φ : Q →ₐ[k] K, φ c = (Comodule.endOfPoint M φ).charpoly.coeff i := by
    intro φ
    have h := congrArg (fun p ↦ p.coeff i)
      (Comodule.charpoly_endOfPoint_comp (M := M) (AlgHom.id k Q) φ)
    simp only [AlgHom.comp_id, Polynomial.coeff_map] at h
    rw [h]
    rfl
  have hfin := finite_values_of_isIntegral (K := K) (A := K ⊗[k] Q) hK
    ((1 : K) ⊗ₜ c) (fun f ↦ by
      letI := Comodule.baseChange (R := k) (H := Q) (M := M) K
      let M' : FGComoduleCat.{u, u, u} K (K ⊗[k] Q) :=
        FGComoduleCat.of (R := K) (C := K ⊗[k] Q) (K ⊗[k] M)
      have h1 := isIntegral_charpoly_coeff hss M' (toConv f) i
      have h2 := charpoly_endOfPoint_baseChange (K := K) M f
      change IsIntegral ℤ (((f.restrictScalars k).comp Algebra.TensorProduct.includeRight) c)
      rw [hval, ← h2]
      exact h1)
  have hsub : (algebraMap k K) '' (Set.range fun g : WithConv (Q →ₐ[k] k) ↦
      (Comodule.endOfPoint M g.ofConv).charpoly.coeff i) ⊆
      Set.range fun f : K ⊗[k] Q →ₐ[K] K ↦ f ((1 : K) ⊗ₜ c) := by
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    refine ⟨Algebra.TensorProduct.lift (Algebra.ofId K K) ((Algebra.ofId k K).comp g.ofConv)
      (fun _ _ ↦ Commute.all _ _), ?_⟩
    have := (hval ((Algebra.ofId k K).comp g.ofConv)).symm
    rw [Comodule.charpoly_endOfPoint_comp] at this
    simpa [Polynomial.coeff_map] using this.symm
  exact (hfin.subset hsub).of_finite_image (algebraMap k K).injective.injOn

/-- `charpolyValuesFinite_of_baseChange` with `K = (k(X))‾`. -/
theorem charpolyValuesFinite_of_noNontrivialTorus_closure {k Q : Type u} [Field k]
    [IsAlgClosed k] [CommRing Q] [HopfAlgebra k Q] [Algebra.FiniteType k Q]
    (htor : NoNontrivialTorus (AlgebraicClosure (FractionRing k[X]))
      (AlgebraicClosure (FractionRing k[X]) ⊗[k] Q)) :
    CharpolyValuesFinite k Q :=
  charpolyValuesFinite_of_baseChange (AlgebraicClosure (FractionRing k[X]))
    ⟨_, not_isIntegral_of_transcendental (transcendental_X_algebraicClosure k)⟩ htor

end AlgMag.Reductive.Step2BaseChange

#print axioms AlgMag.Reductive.Step2BaseChange.charpolyValuesFinite_of_noNontrivialTorus_closure
