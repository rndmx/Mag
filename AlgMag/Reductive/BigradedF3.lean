/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
-/
import AlgMag.Reductive.TorusConjDyn
import AlgMag.Reductive.GradedNakayamaBigraded

/-!
# (F3), bigraded polynomial quotient

`filtrationIdeal_polynomial_bigraded'` has exactly the statement of
`AlgMag.Reductive.filtrationIdeal_polynomial_bigraded` (TorusConjDyn.lean, sorried there).

* `decompose_torus_eq_zero`: the `T`-components of an element of `λ`-degree `m` vanish in
  `T`-weights `μ` with `χ μ ≠ m` (`T`-grading refines the `λ`-grading).
* `filtrationIdeal_eq_span_torus`: `J_n` is spanned by `T`-homogeneous elements, hence
  `filtrationIdeal_isHomogeneous_torus` (`U_{≥n}` is `T`-stable).
* the quotient `T`-grading of `H ⧸ J_n` satisfies `Pos` and `h0`; then
  `GradedNakayamaBigraded.exists_mvPolynomial_equiv_of_graded_smooth_weight` and lifting.
-/

suppress_compilation

open Magnetism DirectSum TensorProduct TauCeti TauCeti.Cocharacter

namespace AlgMag.Reductive

universe u

variable {k : Type u} [Field k] {H : Type u} [CommRing H] [HopfAlgebra k H] [DecidableEq H]
  [Algebra.FiniteType k H] [Algebra.Smooth k H]
variable (l : H →ₐc[k] LaurentPolynomial k)

section Refine

variable {M Y : Type*} [AddCommMonoid M] [DecidableEq M] [AddCommMonoid Y] [DecidableEq Y]
  {A : Type*} [CommRing A] [Algebra k A]
  (ℒ : M → Submodule k A) [GradedAlgebra ℒ] (𝒯 : Y → Submodule k A) [GradedAlgebra 𝒯]
  (χ : Y → M)

/-- If `𝒯` refines `ℒ` along `χ`, the `𝒯`-components of an `ℒ`-homogeneous element of degree `m`
vanish outside `χ⁻¹(m)`. -/
lemma decompose_refine_eq_zero (hχ : ∀ μ, 𝒯 μ ≤ ℒ (χ μ)) {m : M} {a : A} (ha : a ∈ ℒ m)
    {μ : Y} (hμ : χ μ ≠ m) : (decompose 𝒯 a μ : A) = 0 := by
  have key : ∀ x : A, (decompose 𝒯 (decompose ℒ x (χ μ) : A) μ : A) = decompose 𝒯 x μ := by
    intro x
    refine DirectSum.Decomposition.inductionOn 𝒯 ?_ ?_ ?_ x
    · simp
    · rintro ν ⟨x, hx⟩
      simp only
      by_cases hνμ : ν = μ
      · subst hνμ
        rw [decompose_of_mem_same ℒ (hχ ν hx)]
      · rw [decompose_of_mem_ne 𝒯 hx hνμ]
        by_cases hc : χ ν = χ μ
        · rw [decompose_of_mem_same ℒ (hc ▸ hχ ν hx), decompose_of_mem_ne 𝒯 hx hνμ]
        · rw [decompose_of_mem_ne ℒ (hχ ν hx) hc]; simp
    · intro x y hx hy
      simp only [decompose_add, DirectSum.add_apply, AddMemClass.coe_add, hx, hy]
  rw [← key, decompose_of_mem_ne ℒ ha (Ne.symm hμ)]
  simp

/-- An `ℒ`-homogeneous element of degree `m` is a sum of `𝒯`-homogeneous elements of weights in
`χ⁻¹(m)`. -/
lemma mem_span_refine (hχ : ∀ μ, 𝒯 μ ≤ ℒ (χ μ)) {m : M} {a : A} (ha : a ∈ ℒ m) (S : Set A)
    (hS : ∀ μ, χ μ = m → ∀ b ∈ 𝒯 μ, b ∈ S) : a ∈ Submodule.span k S := by
  classical
  rw [← sum_support_decompose 𝒯 a]
  refine Submodule.sum_mem _ fun μ _ => ?_
  by_cases hμ : χ μ = m
  · exact Submodule.subset_span (hS μ hμ _ (SetLike.coe_mem _))
  · rw [decompose_refine_eq_zero ℒ 𝒯 χ hχ ha hμ]; exact Submodule.zero_mem _

end Refine

section Torus

variable {X : Type u} [CommGroup X] [DecidableEq X] (π : H →ₐc[k] MonoidAlgebra k X)
  (χ : Additive X →+ ℤ)

omit [DecidableEq H] [Algebra.FiniteType k H] [Algebra.Smooth k H] [DecidableEq X] in
/-- The counit vanishes on `T`-weight spaces of nonzero weight (conjugation fixes the identity). -/
lemma counit_eq_zero_of_mem_torusGrading {μ : Additive X} (hμ : μ ≠ 0) {a : H}
    (ha : a ∈ torusGrading π μ) : Coalgebra.counit (R := k) a = 0 := by
  have hc := congrArg (fun f => f a)
    (TauCeti.HopfAlgebra.conjugationAlgHom_counit_right (R := k) (H := H))
  simp only [AlgHom.comp_apply] at hc
  change _ = algebraMap k H (Coalgebra.counit a) at hc
  let F : MonoidAlgebra k X ⊗[k] H →ₐ[k] MonoidAlgebra k X :=
    (Algebra.TensorProduct.rid k k _).toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id k _) (Bialgebra.counitAlgHom k H))
  have hF : ∀ t : H ⊗[k] H, F (Algebra.TensorProduct.map π.toAlgHom (AlgHom.id k H) t) =
      π ((Algebra.TensorProduct.rid k k H)
        (Algebra.TensorProduct.map (AlgHom.id k H) (Bialgebra.counitAlgHom k H) t)) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y =>
      simp only [F, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        AlgHom.coe_coe, Algebra.TensorProduct.rid_tmul, Bialgebra.counitAlgHom_apply]
      rw [map_smul]
      rfl
  have h1 : F (torusCoactLeft π a) = algebraMap k _ (Coalgebra.counit (R := k) a) := by
    change F (Algebra.TensorProduct.map π.toAlgHom (AlgHom.id k H)
      (HopfAlgebra.conjugationAlgHom (R := k) (H := H) a)) = _
    rw [hF]
    erw [hc]
    exact π.toAlgHom.commutes _
  have h2 : torusCoactLeft π a = MonoidAlgebra.single (Additive.toMul μ) 1 ⊗ₜ[k] a := by
    have := (mem_torusGrading (π := π)).mp ha
    have h3 : torusCoactLeft π a =
        (TensorProduct.comm k H (MonoidAlgebra k X)) (torusCoact π a) := by
      simp [torusCoact]
    rw [h3, this, TensorProduct.comm_tmul]
  rw [h2] at h1
  simp only [F, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    AlgHom.coe_coe, Algebra.TensorProduct.rid_tmul, Bialgebra.counitAlgHom_apply,
    ] at h1
  erw [Algebra.TensorProduct.rid_tmul] at h1
  rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one, MonoidAlgebra.coe_algebraMap,
    Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply] at h1
  have hne : Additive.toMul μ ≠ (1 : X) := fun h => hμ (by simpa using congrArg Additive.ofMul h)
  rcases MonoidAlgebra.single_inj.mp h1 with h | h
  · exact (hne h.1).elim
  · exact h.1
omit [Algebra.FiniteType k H] [Algebra.Smooth k H] in
/-- `T`-homogeneous generators of `J_n`. -/lemma filtrationIdeal_eq_span_torus (hχ : ∀ μ, torusGrading π μ ≤ lineGrading l (χ μ)) (n : ℕ) :
    filtrationIdeal l n = Ideal.span
      ((⋃ (μ : Additive X) (_ : χ μ < 0 ∨ (0 < χ μ ∧ χ μ < n)), (torusGrading π μ : Set H)) ∪
        {x | ∃ μ, χ μ = 0 ∧ ∃ a ∈ torusGrading π μ, a - algebraMap k H (Coalgebra.counit a) = x}) := by
  classical
  set S := ((⋃ (μ : Additive X) (_ : χ μ < 0 ∨ (0 < χ μ ∧ χ μ < n)), (torusGrading π μ : Set H)) ∪
        {x | ∃ μ, χ μ = 0 ∧ ∃ a ∈ torusGrading π μ, a - algebraMap k H (Coalgebra.counit a) = x})
  have hspan : ∀ x ∈ Submodule.span k S, x ∈ Ideal.span S := fun x hx =>
    Submodule.span_le_restrictScalars k H S hx
  -- degree-0 generators
  have h0gen : ∀ a ∈ lineGrading l 0, a - algebraMap k H (Coalgebra.counit (R := k) a) ∈ Ideal.span S := by
    intro a ha
    apply hspan
    rw [← sum_support_decompose (torusGrading π) a]
    simp only [map_sum, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun μ _ => ?_
    by_cases hμ : χ μ = 0
    · exact Submodule.subset_span (Or.inr ⟨μ, hμ, _, SetLike.coe_mem _, rfl⟩)
    · rw [decompose_refine_eq_zero (lineGrading l) (torusGrading π) χ hχ ha hμ]
      simp
  apply le_antisymm
  · rw [filtrationIdeal]
    refine sup_le ?_ ?_
    · rw [unipotentDefiningHopfIdeal_eq_span, Ideal.span_le]
      rintro x (hx | ⟨h, rfl⟩)
      · simp only [Set.mem_iUnion, SetLike.mem_coe, mem_natMagnet, not_le] at hx
        obtain ⟨m, hm, hx⟩ := hx
        exact hspan _ (mem_span_refine (lineGrading l) (torusGrading π) χ hχ hx S
          fun μ hμ b hb => Or.inl (Set.mem_biUnion (x := μ) (Or.inl (hμ ▸ hm)) hb))
      · set a := (conjugationAlgHom l h).coeff 0
        have ha : a ∈ lineGrading l 0 := coeff_mem_lineGrading h 0
        have h1 := coeff_zero_sub_mem_unip l h
        have h2 := sub_counit_mem_unip l ha
        have h3 : algebraMap k H (Coalgebra.counit (R := k) a - Coalgebra.counit h) ∈
            (BialgHom.unipotentDefiningHopfIdeal l).toIdeal := by
          have := sub_mem h1 h2
          rw [map_sub]
          convert this using 1; ring
        have h4 := counit_eq_zero_of_mem_unip l h3
        have h5 : Coalgebra.counit (R := k) a = Coalgebra.counit h := by
          have : Coalgebra.counit (R := k) (algebraMap k H (Coalgebra.counit (R := k) a -
            Coalgebra.counit h)) = Coalgebra.counit (R := k) a - Coalgebra.counit h := by
            rw [Algebra.algebraMap_eq_smul_one, map_smul, Bialgebra.counit_one]
            simp
          rw [this] at h4
          exact sub_eq_zero.mp h4
        have := h0gen a ha
        rwa [h5] at this
    · rw [Ideal.span_le]
      intro x hx
      simp only [Set.mem_iUnion, SetLike.mem_coe] at hx
      obtain ⟨m, ⟨hm0, hmn⟩, hx⟩ := hx
      exact hspan _ (mem_span_refine (lineGrading l) (torusGrading π) χ hχ hx S
        fun μ hμ b hb => Or.inl (Set.mem_biUnion (x := μ) (Or.inr (by omega)) hb))
  · rw [Ideal.span_le]
    rintro x (hx | ⟨μ, hμ, a, ha, rfl⟩)
    · simp only [Set.mem_iUnion, SetLike.mem_coe] at hx
      obtain ⟨μ, hμ, hx⟩ := hx
      have hl := hχ μ hx
      rcases hμ with hneg | ⟨hp, hlt⟩
      · exact unip_le_filtrationIdeal l n (neg_mem_unip l hneg hl)
      · lift χ μ to ℕ using hp.le with m hm
        exact mem_filtrationIdeal_of_lt l (by omega) (by omega) hl
    · have hl := hχ μ ha
      rw [hμ] at hl
      exact unip_le_filtrationIdeal l n (sub_counit_mem_unip l hl)

omit [Algebra.FiniteType k H] [Algebra.Smooth k H] in
/-- **`U_{≥n}` is `T`-stable**: `J_n` is homogeneous for the `T`-grading. -/
theorem filtrationIdeal_isHomogeneous_torus (hχ : ∀ μ, torusGrading π μ ≤ lineGrading l (χ μ))
    (n : ℕ) : (filtrationIdeal l n).IsHomogeneous (torusGrading π) := by
  rw [filtrationIdeal_eq_span_torus l π χ hχ n]
  apply Ideal.homogeneous_span
  rintro x (hx | ⟨μ, hμ, a, ha, rfl⟩)
  · simp only [Set.mem_iUnion, SetLike.mem_coe] at hx
    obtain ⟨μ, -, hx⟩ := hx
    exact ⟨μ, hx⟩
  · have hμ0 : μ = 0 ∨ μ ≠ 0 := em _
    rcases hμ0 with rfl | hμ0
    · exact ⟨0, sub_mem ha (SetLike.algebraMap_mem_graded _ _)⟩
    · exact ⟨μ, by rw [counit_eq_zero_of_mem_torusGrading π hμ0 ha, map_zero, sub_zero]; exact ha⟩

end Torus

/-- **(F3), bigraded polynomial quotient**: the statement of
`filtrationIdeal_polynomial_bigraded` (TorusConjDyn.lean). -/
theorem filtrationIdeal_polynomial_bigraded' (hP : parabolicDefiningHopfIdeal l = ⊥)
    {X : Type u} [CommGroup X] [DecidableEq X] (π : H →ₐc[k] MonoidAlgebra k X)
    (χ : Additive X →+ ℤ) (hχ : ∀ μ, torusGrading π μ ≤ lineGrading l (χ μ)) (n : ℕ) :
    ∃ (r : ℕ) (x : Fin r → H) (d : Fin r → ℕ) (μ : Fin r → Additive X),
      (∀ i, n ≤ d i ∧ 0 < d i ∧ χ (μ i) = d i ∧ x i ∈ torusGrading π (μ i) ∧
        x i ∈ lineGrading l (d i : ℤ)) ∧
      Function.Bijective (MvPolynomial.aeval (R := k)
        (fun i ↦ Ideal.Quotient.mk (filtrationIdeal l n) (x i))) := by
  classical
  set I := (BialgHom.unipotentDefiningHopfIdeal l).toIdeal
  set J := filtrationIdeal l n
  have hIJ : I ≤ J := unip_le_filtrationIdeal l n
  have hJ : J.IsHomogeneous (torusGrading π) := filtrationIdeal_isHomogeneous_torus l π χ hχ n
  -- smoothness (as in `filtrationIdeal_polynomial_graded`)
  haveI : Algebra.FormallySmooth k (H ⧸ I) := inferInstance
  haveI hsI : Algebra.Smooth k (H ⧸ I) :=
    ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  have hs : Algebra.Smooth k (H ⧸ (I ⊔ magnetIdeal (lineGrading l) (gapMagnet n))) :=
    smooth_quotient_sup_magnetIdeal (lineGrading l) (unipotent_lineGrading l).1 (gapMagnet n)
  have hJeq : J = I ⊔ magnetIdeal (lineGrading l) (gapMagnet n) :=
    filtrationIdeal_eq_sup_magnetIdeal l n
  haveI hsJ : Algebra.Smooth k (H ⧸ J) := by rw [hJeq]; exact hs
  haveI : Algebra.FiniteType k (H ⧸ J) := inferInstance
  haveI : Nontrivial (H ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr (by
    intro h
    have h1 : (1 : H) ∈ J := h ▸ Submodule.mem_top
    have := counit_eq_zero_of_mem_filtrationIdeal l h1
    rw [Bialgebra.counit_one] at this
    exact one_ne_zero this)
  -- the quotient `T`-grading
  letI := gradedAlgebraHomogQuot (torusGrading π) hJ
  set 𝒬 := homogQuotGrading (torusGrading π) J
  have h0 : 𝒬 0 = LinearMap.range (Algebra.linearMap k (H ⧸ J)) := by
    apply le_antisymm
    · intro y hy
      obtain ⟨a, ha, rfl⟩ := (mem_homogQuotGrading _ _).mp hy
      have hl := hχ 0 ha
      rw [map_zero] at hl
      refine ⟨Coalgebra.counit (R := k) a, ?_⟩
      change Ideal.Quotient.mk J (algebraMap k H _) = _
      exact (Ideal.Quotient.eq.mpr (hIJ (sub_counit_mem_unip l hl))).symm
    · rintro _ ⟨c, rfl⟩
      exact (mem_homogQuotGrading _ _).mpr
        ⟨algebraMap k H c, SetLike.algebraMap_mem_graded _ c, rfl⟩
  have hpos : GradedNakayamaBigraded.Pos 𝒬 χ n := by
    intro μ y hy hy0 hμ
    obtain ⟨a, ha, rfl⟩ := (mem_homogQuotGrading _ _).mp hy
    have hl := hχ μ ha
    have hz : ∀ b ∈ J, Ideal.Quotient.mk J b ≠ 0 → False := fun b hb h =>
      h (Ideal.Quotient.eq_zero_iff_mem.mpr hb)
    rcases lt_trichotomy (χ μ) 0 with hneg | hzero | hp
    · exact (hz a (hIJ (neg_mem_unip l hneg hl)) hy0).elim
    · rw [hzero] at hl
      have h1 := sub_counit_mem_unip l hl
      rw [counit_eq_zero_of_mem_torusGrading π hμ ha, map_zero, sub_zero] at h1
      exact (hz a (hIJ h1) hy0).elim
    · refine ⟨hp, ?_⟩
      by_contra hlt
      push Not at hlt
      lift χ μ to ℕ using hp.le with m hm
      exact hz a (mem_filtrationIdeal_of_lt l (by omega) (by omega) hl) hy0
  obtain ⟨r, x, μ, hx, hb⟩ :=
    GradedNakayamaBigraded.exists_mvPolynomial_equiv_of_graded_smooth_weight hpos h0
  have hlift : ∀ i, ∃ a ∈ torusGrading π (μ i), Ideal.Quotient.mk J a = x i :=
    fun i ↦ (mem_homogQuotGrading _ _).mp (hx i).2.2
  choose a ha hax using hlift
  have hxa : (fun i ↦ Ideal.Quotient.mk J (a i)) = x := funext hax
  refine ⟨r, a, fun i => (χ (μ i)).toNat, μ, fun i => ?_, by rw [hxa]; exact hb⟩
  have h1 := (hx i).1
  have h2 := (hx i).2.1
  have e : (((χ (μ i)).toNat : ℕ) : ℤ) = χ (μ i) := Int.toNat_of_nonneg h1.le
  dsimp only
  refine ⟨by omega, by omega, e.symm, ha i, ?_⟩
  rw [e]
  exact hχ _ (ha i)

#print axioms filtrationIdeal_polynomial_bigraded'

end AlgMag.Reductive
