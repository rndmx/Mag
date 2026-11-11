/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
-/
import AlgMag.Sec12PrintedRing
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis

/-!
# Graded Nakayama for a grading by an arbitrary monoid with a positive weight

`B` smooth, of finite type, nontrivial, graded by `Y : Type u` (e.g. `Additive X`), with a weight
`χ : Y →+ ℤ` such that every nonzero piece of nonzero degree `y` has `0 < χ y` and `n ≤ χ y`, and
`ℬ 0 = k`. Then `B` is a polynomial ring on `ℬ`-homogeneous generators of weight `≥ n`, `> 0`.

Proof: Theorem 12.4 ring form (`AlgMag.Sec12Printed`) with `A₀ = k`, `w = toNat ∘ χ`, as in
`GradedNakayama.lean`.
-/

universe u

open AlgMag.Sec12Printed DirectSum

namespace AlgMag.Reductive.GradedNakayamaBigraded

variable {k : Type u} [Field k] {B : Type u} [CommRing B] [Algebra k B]
  {Y : Type u} [AddCommMonoid Y] [DecidableEq Y]
  (ℬ : Y → Submodule k B) [GradedAlgebra ℬ] (χ : Y →+ ℤ) (n : ℕ)

/-- The positivity hypothesis. -/
def Pos : Prop := ∀ y, ∀ b ∈ ℬ y, b ≠ 0 → y ≠ 0 → 0 < χ y ∧ (n : ℤ) ≤ χ y

variable {ℬ χ n}

omit [GradedAlgebra ℬ] in
lemma nonneg (hpos : Pos ℬ χ n) {y : Y} {b : B} (hb : b ∈ ℬ y) (hb0 : b ≠ 0) : 0 ≤ χ y := by
  by_cases hy : y = 0
  · simp [hy]
  · exact (hpos y b hb hb0 hy).1.le

omit [GradedAlgebra ℬ] in
lemma eq_zero_of_add (hpos : Pos ℬ χ n) {i j : Y} {c c' : B} (hc : c ∈ ℬ i) (hc' : c' ∈ ℬ j)
    (h0 : c ≠ 0) (h0' : c' ≠ 0) (h : i + j = 0) : i = 0 ∧ j = 0 := by
  have hs : χ i + χ j = 0 := by rw [← map_add, h, map_zero]
  have a := nonneg hpos hc h0
  have b := nonneg hpos hc' h0'
  constructor
  · by_contra hi; have := (hpos i c hc h0 hi).1; omega
  · by_contra hj; have := (hpos j c' hc' h0' hj).1; omega

/-- Projection to degree `0` is a ring hom (copy of `GradedRing.projZeroRingHom`). -/
def proj0 (hpos : Pos ℬ χ n) : B →+* B where
  toFun a := decompose ℬ a 0
  map_one' := decompose_of_mem_same ℬ SetLike.GradedOne.one_mem
  map_zero' := by rw [decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero]
  map_add' _ _ := by rw [decompose_add, DirectSum.add_apply, AddMemClass.coe_add]
  map_mul' := by
    refine DirectSum.Decomposition.inductionOn ℬ (fun x => ?_) ?_ ?_
    · simp only [zero_mul, decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero]
    · rintro i ⟨c, hc⟩
      refine DirectSum.Decomposition.inductionOn ℬ ?_ ?_ ?_
      · simp only [mul_zero, decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero]
      · rintro j ⟨c', hc'⟩
        simp only
        by_cases h : i + j = 0
        · by_cases h0 : c = 0
          · subst h0; simp
          by_cases h0' : c' = 0
          · subst h0'; simp
          obtain ⟨hi, hj⟩ := eq_zero_of_add hpos hc hc' h0 h0' h
          subst hi; subst hj
          rw [decompose_of_mem_same ℬ (show c * c' ∈ ℬ 0 from h ▸ SetLike.GradedMul.mul_mem hc hc'),
            decompose_of_mem_same ℬ hc, decompose_of_mem_same ℬ hc']
        · rw [decompose_of_mem_ne ℬ (SetLike.GradedMul.mul_mem hc hc') h]
          rcases show i ≠ 0 ∨ j ≠ 0 by
              by_contra hh; push Not at hh; exact h (by rw [hh.1, hh.2, add_zero]) with h' | h'
          · simp only [decompose_of_mem_ne ℬ hc h', zero_mul]
          · simp only [decompose_of_mem_ne ℬ hc' h', mul_zero]
      · intro _ _ hd he
        simp only [mul_add, decompose_add, DirectSum.add_apply, AddMemClass.coe_add, hd, he]
    · rintro _ _ ha hb _
      simp only [add_mul, decompose_add, DirectSum.add_apply, AddMemClass.coe_add, ha, hb]

lemma exists_proj0 (hpos : Pos ℬ χ n) (h0 : ℬ 0 = LinearMap.range (Algebra.linearMap k B)) (a : B) :
    ∃ c : k, algebraMap k B c = proj0 hpos a := by
  show ∃ c : k, algebraMap k B c = ((decompose ℬ a 0 : ℬ 0) : B)
  have : ((decompose ℬ a 0 : ℬ 0) : B) ∈ ℬ 0 := SetLike.coe_mem _
  generalize ((decompose ℬ a 0 : ℬ 0) : B) = z at this ⊢
  rw [h0] at this
  obtain ⟨c, hc⟩ := this
  exact ⟨c, hc⟩

/-- The augmentation `B → k`. -/
noncomputable def aug [Nontrivial B] (hpos : Pos ℬ χ n)
    (h0 : ℬ 0 = LinearMap.range (Algebra.linearMap k B)) : B →ₐ[k] k :=
  have inj : Function.Injective (algebraMap k B) := (algebraMap k B).injective
  have key : ∀ a, algebraMap k B (Classical.choose (exists_proj0 hpos h0 a)) = proj0 hpos a :=
    fun a => Classical.choose_spec (exists_proj0 hpos h0 a)
  { toFun := fun a => Classical.choose (exists_proj0 hpos h0 a)
    map_one' := inj (by rw [key, map_one, map_one])
    map_mul' := fun a b => inj (by rw [key, map_mul, map_mul, key, key])
    map_zero' := inj (by rw [key, map_zero, map_zero])
    map_add' := fun a b => inj (by rw [key, map_add, map_add, key, key])
    commutes' := fun c => inj (by
      rw [key]
      change (decompose ℬ (algebraMap k B c) 0 : B) = _
      rw [decompose_of_mem_same ℬ (SetLike.algebraMap_mem_graded ℬ c)]; rfl) }

lemma algebraMap_aug [Nontrivial B] (hpos : Pos ℬ χ n)
    (h0 : ℬ 0 = LinearMap.range (Algebra.linearMap k B)) (a : B) :
    algebraMap k B (aug hpos h0 a) = (decompose ℬ a 0 : B) :=
  Classical.choose_spec (exists_proj0 hpos h0 a)

lemma isAug [Nontrivial B] (hpos : Pos ℬ χ n)
    (h0 : ℬ 0 = LinearMap.range (Algebra.linearMap k B)) :
    IsAug ℬ (aug hpos h0) (fun y => (χ y).toNat) where
  hw y b hb hb0 h := by
    by_contra hy
    have := (hpos y b hb hb0 hy).1
    omega
  hadd u b hb hb0 v d hd hd0 := by
    rw [map_add]; exact Int.toNat_add (nonneg hpos hb hb0) (nonneg hpos hd hd0)
  hπ y hy b hb := (algebraMap k B).injective (by
    rw [algebraMap_aug, decompose_of_mem_ne ℬ hb hy, map_zero])
  h0 b hb := by rw [algebraMap_aug, decompose_of_mem_same ℬ hb]

/-- **Graded Nakayama, general index with a positive weight.** -/
theorem exists_mvPolynomial_equiv_of_graded_smooth_weight
    [Algebra.FiniteType k B] [Algebra.Smooth k B] [Nontrivial B]
    (hpos : Pos ℬ χ n) (h0 : ℬ 0 = LinearMap.range (Algebra.linearMap k B)) :
    ∃ (r : ℕ) (x : Fin r → B) (μ : Fin r → Y),
      (∀ i, 0 < χ (μ i) ∧ (n : ℤ) ≤ χ (μ i) ∧ x i ∈ ℬ (μ i)) ∧
      Function.Bijective (MvPolynomial.aeval (R := k) x) := by
  classical
  set π := aug hpos h0
  have H := isAug hpos h0
  have := projective_cotangent π
  have hfin := finite_cotangent π
  obtain ⟨s, hts, hπs, hg⟩ := exists_section H
  have hinj := phi_injective π hπs hts
  have hsurj := phi_surjective H hts hπs hg
  let S : Set (Conormal π) := {p | ∃ y : Y, y ≠ 0 ∧ ∃ b ∈ ℬ y, b ≠ 0 ∧ tMap π b = p}
  have hspan : Submodule.span k S = ⊤ := by
    refine eq_top_iff.2 fun p _ => ?_
    obtain ⟨a, rfl⟩ := tMap_surjective π p
    rw [← DirectSum.sum_support_decompose ℬ a, map_sum]
    refine Submodule.sum_mem _ fun y _ => ?_
    by_cases hy : y = 0
    · subst hy
      rw [tMap_of_zero H (SetLike.coe_mem _)]
      exact Submodule.zero_mem _
    · by_cases hb0 : (decompose ℬ a y : B) = 0
      · rw [hb0, map_zero]; exact Submodule.zero_mem _
      · exact Submodule.subset_span ⟨y, hy, _, SetLike.coe_mem _, hb0, rfl⟩
  obtain ⟨T, hTS, hTspan, hTli⟩ := exists_linearIndependent k S
  let bT : Module.Basis T k (Conormal π) :=
    Module.Basis.mk hTli (by rw [Subtype.range_coe, hTspan, hspan])
  have : Finite T := Module.Finite.finite_basis bT
  let _ : Fintype T := Fintype.ofFinite T
  let bas := bT.reindex (Fintype.equivFin T)
  have hbS : ∀ i, bas i ∈ S := fun i => by
    simp only [bas, Module.Basis.reindex_apply, bT, Module.Basis.mk_apply]
    exact hTS (Subtype.prop _)
  choose y hy b hb hb0 htb using hbS
  refine ⟨Fintype.card T, fun i => s (bas i), y, fun i =>
    ⟨(hpos _ _ (hb i) (hb0 i) (hy i)).1, (hpos _ _ (hb i) (hb0 i) (hy i)).2, ?_⟩, ?_⟩
  · have := hg (y i) (b i) (hb i)
    rwa [htb i] at this
  · have heq : MvPolynomial.aeval (R := k) (fun i => s (bas i)) =
        (SymmetricAlgebra.lift s).comp
          (SymmetricAlgebra.equivMvPolynomial bas).symm.toAlgHom := by
      refine MvPolynomial.algHom_ext fun i => ?_
      simp only [MvPolynomial.aeval_X, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
        SymmetricAlgebra.equivMvPolynomial_symm_X]
      exact (SymmetricAlgebra.lift_ι_apply s (bas i)).symm
    rw [heq, AlgHom.coe_comp]
    exact ⟨hinj.comp (SymmetricAlgebra.equivMvPolynomial bas).symm.injective,
      hsurj.comp (SymmetricAlgebra.equivMvPolynomial bas).symm.surjective⟩

#print axioms exists_mvPolynomial_equiv_of_graded_smooth_weight

end AlgMag.Reductive.GradedNakayamaBigraded
