/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3SchemeQuotient

/-!
# Lemma D, Step 3 (iii): the integral closure in a graded ring is graded

Step 3 (iii) of the proof of `Algebraic Magnetism` Props. 3.31 (ii), 3.32 (ii).
The note cites Stacks 03GG for `B → B[ℤ^r]`; here the case used is proved from `Polynomial.isIntegral_iff_isIntegral_coeff`
(Stacks 00H6), by localizing at `T` and by separating a finite support with a homomorphism to `ℤ`.
-/

open Polynomial LaurentPolynomial

universe u

namespace AlgMag.SD

open AlgMag.SQ

section Laurent

variable {B C : Type u} [CommRing B] [CommRing C] (f : B →+* C)

lemma SDExist_coeff_CT (a : C) (n z : ℤ) : (LaurentPolynomial.C a * T n).coeff z = if n = z then a else 0 := by
  rw [← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

lemma SDExist_coeff_toLaurent (h : C[X]) (z : ℕ) : (toLaurent h).coeff (z : ℤ) = h.coeff z := by
  induction h using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, Polynomial.coeff_add]
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.toLaurent_C_mul_X_pow, SDExist_coeff_CT,
      Polynomial.coeff_C_mul_X_pow]
    simp only [Nat.cast_inj, eq_comm]

lemma SDExist_coeff_toLaurent_neg (h : C[X]) {z : ℤ} (hz : z < 0) : (toLaurent h).coeff z = 0 := by
  induction h using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, add_zero]
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.toLaurent_C_mul_X_pow, SDExist_coeff_CT,
      if_neg (by omega)]

lemma SDExist_toLaurent_map (p : B[X]) : toLaurent (p.map f) = AddMonoidAlgebra.mapRingHom ℤ f (toLaurent p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.map_add, map_add, hp, hq]
  | monomial n a =>
    rw [Polynomial.map_monomial, ← Polynomial.C_mul_X_pow_eq_monomial, ← Polynomial.C_mul_X_pow_eq_monomial,
      Polynomial.toLaurent_C_mul_X_pow, Polynomial.toLaurent_C_mul_X_pow, ← single_eq_C_mul_T, ← single_eq_C_mul_T,
      AddMonoidAlgebra.mapRingHom_single]

/-- A Laurent polynomial integral over `B[T,T⁻¹]` has coefficients integral over `B`. -/
theorem SDExist_coeff_integral_laurent {g : AddMonoidAlgebra C ℤ}
    (hg : (AddMonoidAlgebra.mapRingHom ℤ f).IsIntegralElem g) (z : ℤ) : f.IsIntegralElem (g.coeff z) := by
  algebraize [f]
  letI φ : AddMonoidAlgebra B ℤ →+* AddMonoidAlgebra C ℤ := AddMonoidAlgebra.mapRingHom ℤ f
  letI i1 : Algebra (AddMonoidAlgebra B ℤ) (AddMonoidAlgebra C ℤ) := φ.toAlgebra
  letI i2 : Algebra B[X] (AddMonoidAlgebra C ℤ) := (φ.comp (algebraMap B[X] B[T;T⁻¹])).toAlgebra
  haveI : IsScalarTower B[X] (AddMonoidAlgebra B ℤ) (AddMonoidAlgebra C ℤ) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hg' : IsIntegral (AddMonoidAlgebra B ℤ) g := hg
  obtain ⟨⟨_, n, rfl⟩, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (Rₘ := B[T;T⁻¹]) (Submonoid.powers (Polynomial.X : B[X])) g hg'
  obtain ⟨m, h', hh'⟩ := LaurentPolynomial.exists_T_pow g
  letI i3 : Algebra B[X] C[X] := (Polynomial.mapRingHom f).toAlgebra
  have hmap : ∀ p : B[X], algebraMap B[X] (AddMonoidAlgebra C ℤ) p = toLaurent (p.map f) := fun p =>
    (SDExist_toLaurent_map f p).symm
  let τ : C[X] →ₐ[B[X]] AddMonoidAlgebra C ℤ :=
    { toLaurent with
      commutes' := fun p => (hmap p).symm }
  have hτ : Function.Injective τ := Polynomial.toLaurent_injective
  -- `T^(n+m) g = τ (X^n h')`
  have e0 : algebraMap B[X] (AddMonoidAlgebra C ℤ) (Polynomial.X ^ n) = T (n : ℤ) := by
    rw [hmap]; simp [Polynomial.toLaurent_X_pow]
  have hint : IsIntegral B[X] (τ (Polynomial.X ^ n * h')) := by
    have e2 : τ (Polynomial.X ^ n * h') = ((Polynomial.X ^ n : B[X]) • g) * algebraMap B[X] (AddMonoidAlgebra C ℤ) (Polynomial.X ^ m) := by
      have e3 : algebraMap B[X] (AddMonoidAlgebra C ℤ) (Polynomial.X ^ m) = T (m : ℤ) := by
        rw [hmap]; simp [Polynomial.toLaurent_X_pow]
      change toLaurent (Polynomial.X ^ n * h') = _
      rw [Algebra.smul_def, e0, e3, map_mul, hh', Polynomial.toLaurent_X_pow]
      ring
    rw [e2]
    exact hm.mul isIntegral_algebraMap
  have hh : IsIntegral B[X] (Polynomial.X ^ n * h') := (isIntegral_algHom_iff τ hτ).1 hint
  have hc : ∀ i, IsIntegral B ((Polynomial.X ^ n * h').coeff i) := (Polynomial.isIntegral_iff_isIntegral_coeff).1 hh
  have hT : (toLaurent (Polynomial.X ^ n * h')).coeff (z + ((n : ℤ) + m)) = g.coeff z := by
    have : toLaurent (Polynomial.X ^ n * h') = g * AddMonoidAlgebra.single ((n : ℤ) + m) 1 := by
      rw [map_mul, hh', Polynomial.toLaurent_X_pow, ← T, T_add]
      ring
    rw [this, AddMonoidAlgebra.coeff_mul_single_apply, mul_one, add_neg_cancel_right]
  have hz : IsIntegral B (g.coeff z) := by
    rw [← hT]
    obtain hneg | hpos := lt_or_ge (z + ((n : ℤ) + m)) 0
    · rw [SDExist_coeff_toLaurent_neg _ hneg]
      exact isIntegral_zero
    · obtain ⟨i, hi⟩ := Int.eq_ofNat_of_zero_le hpos
      rw [hi, SDExist_coeff_toLaurent]
      exact hc i
  exact hz

end Laurent

section Graded

variable {Γ B C : Type u} [AddCommGroup Γ] [CommRing B] [CommRing C]

/-- **Step 3 (iii)**: for a graded map `f : B → C`, an element integral over `B` has homogeneous components
integral over `B`, provided every finite subset of `Γ` is separated by a homomorphism to `ℤ`. -/
theorem SDExist_comp_integral (hΓ : ∀ s : Finset Γ, ∃ ψ : Γ →+ ℤ, Set.InjOn ψ s)
    (cB : Coact B Γ) (cC : Coact C Γ) (f : B →+* C)
    (hf : cC.σ.comp f = (AddMonoidAlgebra.mapRingHom Γ f).comp cB.σ) {y : C} (hy : f.IsIntegralElem y) (d : Γ) :
    f.IsIntegralElem (cC.comp d y) := by
  classical
  obtain ⟨ψ, hψ⟩ := hΓ (insert d (cC.σ y).coeff.support)
  let M (D : Type u) [CommRing D] : AddMonoidAlgebra D Γ →+* AddMonoidAlgebra D ℤ :=
    AddMonoidAlgebra.mapDomainRingHom D ψ
  obtain ⟨p, hp, h0⟩ := hy
  have hint : (AddMonoidAlgebra.mapRingHom ℤ f).IsIntegralElem (M C (cC.σ y)) := by
    refine ⟨p.map ((M B).comp cB.σ), hp.map _, ?_⟩
    have e : ((M C).comp cC.σ).comp f = (AddMonoidAlgebra.mapRingHom ℤ f).comp ((M B).comp cB.σ) := by
      rw [RingHom.comp_assoc, hf, ← RingHom.comp_assoc, ← RingHom.comp_assoc]
      congr 1
      exact (AddMonoidAlgebra.mapRingHom_comp_mapDomainRingHom f ψ).symm
    have h1 := Polynomial.hom_eval₂ p f ((M C).comp cC.σ) y
    rw [h0, map_zero, e] at h1
    rw [Polynomial.eval₂_map]
    exact h1.symm
  have key := SDExist_coeff_integral_laurent f hint (ψ d)
  have ec : (M C (cC.σ y)).coeff (ψ d) = cC.comp d y := by
    change Finsupp.mapDomain ψ (cC.σ y).coeff (ψ d) = (cC.σ y).coeff d
    exact Finsupp.mapDomain_apply' _ _ (fun x hx => Finset.mem_coe.2 (Finset.mem_insert_of_mem hx)) hψ
      (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
  rwa [ec] at key

/-- Every finite subset of `ℤ^r` is separated by a homomorphism to `ℤ`. -/
theorem SDExist_separate (r : ℕ) (s : Finset (Fin r → ℤ)) : ∃ ψ : (Fin r → ℤ) →+ ℤ, Set.InjOn ψ s := by
  classical
  let pol (v : Fin r → ℤ) : ℤ[X] := ∑ i, Polynomial.C (v i) * Polynomial.X ^ (i : ℕ)
  have hcoeff : ∀ v (i : Fin r), (pol v).coeff i = v i := by
    intro v i
    simp only [pol, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [if_neg (fun e => hj (Fin.ext e.symm))]
    · simp
  let D : Finset ℤ[X] := ((s ×ˢ s).filter fun x => x.1 ≠ x.2).image fun x => pol x.1 - pol x.2
  have hD : ∀ q ∈ D, q ≠ 0 := by
    intro q hq h0
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hq
    refine (Finset.mem_filter.1 hx).2 (funext fun i => ?_)
    rw [← hcoeff x.1 i, ← hcoeff x.2 i]
    exact sub_eq_zero.1 ((Polynomial.coeff_sub _ _ _).symm.trans (by rw [h0]; simp))
  have hfin : (⋃ q ∈ D, {t : ℤ | q.IsRoot t}).Finite :=
    D.finite_toSet.biUnion fun q hq => Polynomial.finite_setOfPred_isRoot (hD q hq)
  obtain ⟨t, ht⟩ := hfin.exists_notMem
  let ψ : (Fin r → ℤ) →+ ℤ :=
    { toFun := fun v => (pol v).eval t
      map_zero' := by simp [pol]
      map_add' := fun v w => by simp [pol, add_mul, Finset.sum_add_distrib, Polynomial.eval_finsetSum] }
  refine ⟨ψ, fun v hv w hw hvw => ?_⟩
  by_contra hne
  refine ht (Set.mem_biUnion (x := pol v - pol w) (Finset.mem_coe.2 (Finset.mem_image.2
    ⟨(v, w), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hv, hw⟩, hne⟩, rfl⟩)) ?_)
  change (pol v - pol w).eval t = 0
  rw [Polynomial.eval_sub]
  exact sub_eq_zero.2 hvw

/-- **Step 3 (iii)**, for a grading by a group isomorphic to `ℤ^r`: the integral closure is graded. -/
theorem SDExist_comp_integral_free {r : ℕ} (e : Γ ≃+ (Fin r → ℤ))
    (cB : Coact B Γ) (cC : Coact C Γ) (f : B →+* C)
    (hf : cC.σ.comp f = (AddMonoidAlgebra.mapRingHom Γ f).comp cB.σ) {y : C} (hy : f.IsIntegralElem y) (d : Γ) :
    f.IsIntegralElem (cC.comp d y) := by
  refine SDExist_comp_integral (fun s => ?_) cB cC f hf hy d
  obtain ⟨ψ, hψ⟩ := SDExist_separate r (s.image e)
  classical
  refine ⟨ψ.comp e.toAddMonoidHom, fun a ha b hb hab => e.injective (hψ ?_ ?_ hab)⟩
  · exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_coe.1 ha))
  · exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_coe.1 hb))

end Graded

end AlgMag.SD

#print axioms AlgMag.SD.SDExist_comp_integral_free
