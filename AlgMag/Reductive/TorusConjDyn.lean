/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.CocharacterGrading
import AlgMag.Reductive.GradedQuotient
import TauCeti.Algebra.AlgebraicGroup.Dynamic.Unipotent.Representability
import TauCeti.Algebra.AlgebraicGroup.Torus.Maximal
import TauCeti.Algebra.AlgebraicGroup.Hopf.PointConjugation
import AlgMag.Reductive.GradedNakayama
import AlgMag.Reductive.GradedComul
import AlgMag.Reductive.TorusGrading
import TauCeti.RingTheory.FiniteType.PointSeparation
import AlgMag.GeneralBaseGrading
import TauCeti.Algebra.AlgebraicGroup.Dynamic.LeviDecomposition.Coordinate
import TauCeti.Algebra.AlgebraicGroup.Dynamic.Smooth
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Basic
import TauCeti.Algebra.AlgebraicGroup.Dynamic.Levi.Representability
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.SemidirectProduct
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Torus conjugacy in a dynamic parabolic (T1-dyn) and the `λ`-filtration (F)

Notes: `equivalence-reductive/T-steps.md`, sections "T1-dyn" and "(F) λ-filtration".

Let `B = Spec H` be a smooth connected affine group over a field `k` and `λ` a cocharacter with
`B = P_B(λ)`. Write `U = U_B(λ)`, `A = k[U] = H ⧸ unipotentDefiningHopfIdeal λ`.

* (F1) `unipotent_lineGrading`: conjugation by `λ` makes `A` an `ℕ`-graded algebra with `A_0 = k`.
* (F2) `exists_mvPolynomial_equiv_of_graded_smooth`: graded Nakayama: a connected `ℕ`-graded
  finite-type smooth `k`-algebra is a polynomial ring on homogeneous generators of positive degree.
* (F4, algebraic core) `comul_eq_of_comul_mem_one_tensor_sup` and `isPrimitive_of_lowestDegree`:
  in the lowest positive degree the elements are primitive (cross terms have degree `≥ 2n`).
* T1-vec: Tau Ceti `TauCeti.Comodule.exists_splitting_eq_conj_of_naturality` (ported unchanged).
* T1-dyn `exists_unipotent_conjugate_eq_of_isMaximalTorus`.

Status: see `equivalence-reductive/lean-T1.md`.
-/

suppress_compilation

open TensorProduct Magnetism TauCeti TauCeti.Cocharacter WithConv

namespace AlgMag.Reductive

universe u

/-! ## (F4) algebraic core: primitivity in the lowest positive degree -/

section Primitive

variable {k : Type u} [Field k] {A : Type u} [CommRing A] [Bialgebra k A]

/-- If `Δ x ∈ 1 ⊗ W + W ⊗ 1` and the counit kills `W` and `x ∈ W`, then `x` is primitive. -/
theorem comul_eq_of_comul_mem_one_tensor_sup (W : Submodule k A)
    (hε : ∀ w ∈ W, Coalgebra.counit (R := k) w = 0) {x : A} (hx : x ∈ W)
    (hΔ : ∃ y ∈ W, ∃ z ∈ W, Coalgebra.comul (R := k) x = (1 : A) ⊗ₜ y + z ⊗ₜ (1 : A)) :
    Coalgebra.comul (R := k) x = x ⊗ₜ (1 : A) + (1 : A) ⊗ₜ x := by
  obtain ⟨y, hy, z, hz, h⟩ := hΔ
  have h1 := Coalgebra.rTensor_counit_comul (R := k) x
  have h2 := Coalgebra.lTensor_counit_comul (R := k) x
  rw [h] at h1 h2
  simp only [map_add, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, hε y hy, hε z hz,
    Bialgebra.counit_one, zero_tmul, tmul_zero, add_zero, zero_add] at h1 h2
  have hy' : y = x := by
    have := congrArg (TensorProduct.lid k A) h1
    simpa using this
  have hz' : z = x := by
    have := congrArg (TensorProduct.rid k A) h2
    simpa using this
  rw [h, hy', hz', add_comm]

/-- **(F4) primitivity.** Let `𝒜` be an `ℕ`-grading of the bialgebra `A` compatible with the
comultiplication, with `A_0 = k · 1`, counit zero in positive degrees, and `A_m = 0` for
`0 < m < n`. Then every element of degree `n > 0` is primitive. -/
theorem isPrimitive_of_lowestDegree (𝒜 : ℕ → Submodule k A)
    (hΔ : ∀ n, ∀ x ∈ 𝒜 n, Coalgebra.comul (R := k) x ∈
      ⨆ (i : ℕ) (j : ℕ) (_ : i + j = n), LinearMap.range (TensorProduct.map (𝒜 i).subtype (𝒜 j).subtype))
    (h0 : 𝒜 0 = LinearMap.range (Algebra.linearMap k A))
    (hε : ∀ m, 0 < m → ∀ w ∈ 𝒜 m, Coalgebra.counit (R := k) w = 0)
    {n : ℕ} (hn : 0 < n) (hlow : ∀ m, 0 < m → m < n → 𝒜 m = ⊥) {x : A} (hx : x ∈ 𝒜 n) :
    Coalgebra.comul (R := k) x = x ⊗ₜ (1 : A) + (1 : A) ⊗ₜ x := by
  refine comul_eq_of_comul_mem_one_tensor_sup (𝒜 n) (hε n hn) hx ?_
  -- Only `(i, j) = (0, n), (n, 0)` survive; `A_0 = k·1` turns them into `1 ⊗ y + z ⊗ 1`.
  set W := 𝒜 n
  let L : Submodule k (A ⊗[k] A) := LinearMap.range (TensorProduct.map (Algebra.linearMap k A) W.subtype)
  let Rr : Submodule k (A ⊗[k] A) := LinearMap.range (TensorProduct.map W.subtype (Algebra.linearMap k A))
  have hL : ∀ t ∈ L, ∃ y ∈ W, t = (1 : A) ⊗ₜ y := by
    rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, W.zero_mem, by simp⟩
    | tmul c w => exact ⟨c • (w : A), W.smul_mem c w.2, by simp [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]⟩
    | add a b ha hb =>
      obtain ⟨y₁, h₁, e₁⟩ := ha; obtain ⟨y₂, h₂, e₂⟩ := hb
      exact ⟨y₁ + y₂, W.add_mem h₁ h₂, by rw [map_add, e₁, e₂, tmul_add]⟩
  have hR : ∀ t ∈ Rr, ∃ z ∈ W, t = z ⊗ₜ (1 : A) := by
    rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, W.zero_mem, by simp⟩
    | tmul w c => exact ⟨c • (w : A), W.smul_mem c w.2, by simp [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]⟩
    | add a b ha hb =>
      obtain ⟨y₁, h₁, e₁⟩ := ha; obtain ⟨y₂, h₂, e₂⟩ := hb
      exact ⟨y₁ + y₂, W.add_mem h₁ h₂, by rw [map_add, e₁, e₂, add_tmul]⟩
  have hle : (⨆ (i : ℕ) (j : ℕ) (_ : i + j = n),
      LinearMap.range (TensorProduct.map (𝒜 i).subtype (𝒜 j).subtype)) ≤ L ⊔ Rr := by
    refine iSup_le fun i ↦ iSup_le fun j ↦ iSup_le fun hij ↦ ?_
    rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
    | tmul a b =>
      rw [TensorProduct.map_tmul]
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · obtain ⟨c, hc⟩ := (h0 ▸ a.2 : (a : A) ∈ LinearMap.range (Algebra.linearMap k A))
        have hj : j = n := by omega
        subst hj
        refine Submodule.mem_sup_left ⟨c ⊗ₜ b, ?_⟩
        simp [← hc]
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · obtain ⟨c, hc⟩ := (h0 ▸ b.2 : (b : A) ∈ LinearMap.range (Algebra.linearMap k A))
        have hi' : i = n := by omega
        subst hi'
        refine Submodule.mem_sup_right ⟨a ⊗ₜ c, ?_⟩
        simp [← hc]
      · have ha : (a : A) = 0 := by
          have h := a.2
          have h' : (a : A) ∈ (⊥ : Submodule k A) := hlow i hi (by omega) ▸ h
          exact (Submodule.mem_bot k).mp h'
        simp [ha]
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (hle (hΔ n x hx))
  obtain ⟨y, hy, rfl⟩ := hL a ha
  obtain ⟨z, hz, rfl⟩ := hR b hb
  exact ⟨y, hy, z, hz, hab.symm⟩

end Primitive

/-! ## (F2) graded Nakayama -/

/-- **(F2) graded Nakayama for smooth connected graded algebras.** A finite-type smooth
`k`-algebra with a connected `ℕ`-grading (`A_0 = k`) is a polynomial ring on finitely many
homogeneous generators of positive degree. -/
theorem exists_mvPolynomial_equiv_of_graded_smooth {k : Type u} [Field k] {A : Type u}
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [Algebra.Smooth k A] [Nontrivial A]
    (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]
    (h0 : 𝒜 0 = LinearMap.range (Algebra.linearMap k A)) :
    ∃ (n : ℕ) (x : Fin n → A) (d : Fin n → ℕ), (∀ i, 0 < d i ∧ x i ∈ 𝒜 (d i)) ∧
      Function.Bijective (MvPolynomial.aeval (R := k) x) := by
  exact GradedNakayama.exists_mvPolynomial_equiv_of_graded_smooth' 𝒜 h0

/-! ## (F1) the `λ`-grading of `k[U(λ)]` -/

section Grading

variable {k : Type u} [Field k] {H : Type u} [CommRing H] [HopfAlgebra k H] [DecidableEq H]
variable (l : H →ₐc[k] LaurentPolynomial k)

omit [DecidableEq H] in
variable {l} in
lemma algebraMap_mem_lineGrading_zero (r : k) : algebraMap k H r ∈ lineGrading l 0 := by
  rw [mem_lineGrading, AlgHom.commutes]
  rfl

omit [DecidableEq H] in
/-- The ideal of `U(λ)` as the span of the negative-degree elements and the `h₀ - ε(h)`. -/
lemma unipotentDefiningHopfIdeal_eq_span :
    (BialgHom.unipotentDefiningHopfIdeal l).toIdeal =
      Ideal.span ((⋃ (m : ℤ) (_ : m ∉ natMagnet), (lineGrading l m : Set H)) ∪
        {x | ∃ h : H, (conjugationAlgHom l h).coeff 0 -
          algebraMap k H (Coalgebra.counit h) = x}) := by
  rw [BialgHom.unipotentDefiningHopfIdeal_toIdeal, ← magnetIdeal_lineGrading_nat, magnetIdeal,
    Ideal.span_union]

/-- **(F1).** The ideal of `U(λ)` is `λ`-homogeneous, and on `k[U(λ)]` the image grading lives
in degrees `≥ 0` with degree-zero part `k · 1`. -/
theorem unipotent_lineGrading :
    (BialgHom.unipotentDefiningHopfIdeal l).toIdeal.IsHomogeneous (lineGrading l) ∧
    (∀ n : ℤ, n < 0 →
      homogQuotGrading (lineGrading l) (BialgHom.unipotentDefiningHopfIdeal l).toIdeal n = ⊥) ∧
    homogQuotGrading (lineGrading l) (BialgHom.unipotentDefiningHopfIdeal l).toIdeal 0 =
      LinearMap.range (Algebra.linearMap k (H ⧸ (BialgHom.unipotentDefiningHopfIdeal l).toIdeal)) := by
  set I := (BialgHom.unipotentDefiningHopfIdeal l).toIdeal
  have hI : I = _ := unipotentDefiningHopfIdeal_eq_span l
  have hneg : ∀ n : ℤ, n < 0 → ∀ a ∈ lineGrading l n, a ∈ I := by
    intro n hn a ha
    rw [hI]
    refine Ideal.subset_span (Or.inl ?_)
    simp only [Set.mem_iUnion, SetLike.mem_coe, mem_natMagnet, not_le]
    exact ⟨n, hn, ha⟩
  have hzero : ∀ h : H, (conjugationAlgHom l h).coeff 0 - algebraMap k H (Coalgebra.counit h) ∈ I := by
    intro h
    rw [hI]
    exact Ideal.subset_span (Or.inr ⟨h, rfl⟩)
  refine ⟨?_, ?_, ?_⟩
  · rw [hI]
    apply Ideal.homogeneous_span
    rintro x (hx | ⟨h, rfl⟩)
    · simp only [Set.mem_iUnion, SetLike.mem_coe] at hx
      obtain ⟨m, -, hm⟩ := hx
      exact ⟨m, hm⟩
    · exact ⟨0, sub_mem (coeff_mem_lineGrading h 0) (algebraMap_mem_lineGrading_zero _)⟩
  · intro n hn
    refine (Submodule.eq_bot_iff _).mpr fun y hy ↦ ?_
    obtain ⟨a, ha, rfl⟩ := (mem_homogQuotGrading _ _).mp hy
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hneg n hn a ha)
  · apply le_antisymm
    · intro y hy
      obtain ⟨a, ha, rfl⟩ := (mem_homogQuotGrading _ _).mp hy
      refine ⟨Coalgebra.counit (R := k) a, ?_⟩
      have h0 := hzero a
      rw [coeff_of_mem_lineGrading ha, if_pos rfl] at h0
      change Ideal.Quotient.mk I (algebraMap k H _) = _
      exact (Ideal.Quotient.eq.mpr h0).symm
    · rintro _ ⟨c, rfl⟩
      refine (mem_homogQuotGrading _ _).mpr ⟨algebraMap k H c, algebraMap_mem_lineGrading_zero c, ?_⟩
      rfl

end Grading

/-! ## (F3) + (F4): the filtration `U = U_{≥1} ⊇ U_{≥2} ⊇ ⋯ ⊇ U_{≥N} = 1` -/

section Filtration

variable {k : Type u} [Field k] {H : Type u} [CommRing H] [HopfAlgebra k H] [DecidableEq H]
  [Algebra.FiniteType k H] [Algebra.Smooth k H]
variable (l : H →ₐc[k] LaurentPolynomial k)

/-- The ideal `J_n` of `U_{≥n}` inside `H`: the ideal of `U(λ)` plus the elements of
`λ`-degree `m` with `0 < m < n`. -/
noncomputable def filtrationIdeal (n : ℕ) : Ideal H :=
  (BialgHom.unipotentDefiningHopfIdeal l).toIdeal ⊔
    Ideal.span (⋃ (m : ℕ) (_ : 0 < m ∧ m < n), (lineGrading l (m : ℤ) : Set H))

end Filtration

/-- Local copy of Tau Ceti `TauCeti.HopfIdeal.IsMaximalTorus.conjugate` (Torus/Conjugation.lean,
whose imports are still being ported): a conjugate of a maximal torus is a maximal torus. -/
theorem isMaximalTorus_conjugate' {k : Type u} [Field k] {H : Type u} [CommRing H] [HopfAlgebra k H]
    [Algebra.FiniteType k H] {I : HopfIdeal k H}
    (hI : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) I)
    (g : WithConv (H →ₐ[k] k)) :
    HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) (I.conjugate g) := by
  have h := hI.comapOfIso (HopfAlgebra.pointConjugationFiniteTypeIso g)
  rw [HopfIdeal.conjugate_eq_comapOfSurjective]
  simpa only [HopfAlgebra.pointConjugationFiniteTypeIso_hom] using h

/-! ## T1-dyn -/

section Dyn

variable {k : Type u} [Field k] {H : Type u} [CommRing H] [HopfAlgebra k H] [DecidableEq H]
  [Algebra.FiniteType k H] [Algebra.Smooth k H]
variable (l : H →ₐc[k] LaurentPolynomial k)

/-- The hypotheses of T1-dyn on `(l, T)`, bundled. -/
structure DynHyp (T : HopfIdeal k H) : Prop where
  hP : parabolicDefiningHopfIdeal l = ⊥
  hT : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) T
  hlT : T.toIdeal ≤ RingHom.ker (l : H →ₐ[k] LaurentPolynomial k)
  hcent : ∀ (A : Type u) [CommRing A] [Algebra k A] (g t : WithConv (H →ₐ[k] A)),
      (leviDefiningHopfIdeal l).toIdeal ≤ RingHom.ker (ofConv g) →
      T.toIdeal ≤ RingHom.ker (ofConv t) → g * t = t * g

/-- The ideal of the closed subgroup `T · U_{≥n}`: kernel of `H → H/T ⊗ H/J_n`, `h ↦ Δ h`. -/
noncomputable def tuIdeal (T : HopfIdeal k H) (n : ℕ) : Ideal H :=
  RingHom.ker ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k T.toIdeal)
    (Ideal.Quotient.mkₐ k (filtrationIdeal l n))).comp (Bialgebra.comulAlgHom k H))

omit [DecidableEq H] [Algebra.FiniteType k H] [Algebra.Smooth k H] in
lemma counit_eq_zero_of_mem_unip {x : H} (hx : x ∈ (BialgHom.unipotentDefiningHopfIdeal l).toIdeal) :
    Coalgebra.counit (R := k) x = 0 :=
  (BialgHom.unipotentDefiningHopfIdeal l).counit_eq_zero (HopfIdeal.mem_toIdeal.mp hx)

omit [DecidableEq H] [Algebra.FiniteType k H] [Algebra.Smooth k H] in
lemma coeff_zero_sub_mem_unip (h : H) :
    (conjugationAlgHom l h).coeff 0 - algebraMap k H (Coalgebra.counit h) ∈
      (BialgHom.unipotentDefiningHopfIdeal l).toIdeal := by
  rw [unipotentDefiningHopfIdeal_eq_span]
  exact Ideal.subset_span (Or.inr ⟨h, rfl⟩)

omit [DecidableEq H] [Algebra.FiniteType k H] [Algebra.Smooth k H] in
lemma neg_mem_unip {m : ℤ} (hm : m < 0) {a : H} (ha : a ∈ lineGrading l m) :
    a ∈ (BialgHom.unipotentDefiningHopfIdeal l).toIdeal := by
  rw [unipotentDefiningHopfIdeal_eq_span]
  refine Ideal.subset_span (Or.inl ?_)
  simp only [Set.mem_iUnion, SetLike.mem_coe, mem_natMagnet, not_le]
  exact ⟨m, hm, ha⟩

omit [DecidableEq H] [Algebra.FiniteType k H] [Algebra.Smooth k H] in
/-- The counit vanishes in nonzero `λ`-degree. -/
lemma counit_eq_zero_of_mem_lineGrading {m : ℤ} (hm : m ≠ 0) {a : H} (ha : a ∈ lineGrading l m) :
    Coalgebra.counit (R := k) a = 0 := by
  have h := counit_eq_zero_of_mem_unip l (coeff_zero_sub_mem_unip l a)
  have h0 : (conjugationAlgHom l a).coeff 0 = 0 := by
    rw [coeff_of_mem_lineGrading ha]; simp [Ne.symm hm]
  rw [h0, zero_sub, map_neg, neg_eq_zero] at h
  simpa using h

omit [DecidableEq H] [Algebra.FiniteType k H] [Algebra.Smooth k H] in
lemma sub_counit_mem_unip {a : H} (ha : a ∈ lineGrading l 0) :
    a - algebraMap k H (Coalgebra.counit a) ∈ (BialgHom.unipotentDefiningHopfIdeal l).toIdeal := by
  have h := coeff_zero_sub_mem_unip l a
  rwa [coeff_of_mem_lineGrading ha, if_pos rfl] at h

omit [DecidableEq H] [Algebra.FiniteType k H] [Algebra.Smooth k H] in
lemma unip_le_filtrationIdeal (n : ℕ) :
    (BialgHom.unipotentDefiningHopfIdeal l).toIdeal ≤ filtrationIdeal l n := le_sup_left

omit [DecidableEq H] [Algebra.FiniteType k H] [Algebra.Smooth k H] in
lemma mem_filtrationIdeal_of_lt {n m : ℕ} (h0 : 0 < m) (hm : m < n) {a : H}
    (ha : a ∈ lineGrading l (m : ℤ)) : a ∈ filtrationIdeal l n :=
  (le_sup_right : _ ≤ filtrationIdeal l n) (Ideal.subset_span (by
    simp only [Set.mem_iUnion, SetLike.mem_coe]
    exact ⟨m, ⟨h0, hm⟩, ha⟩))

omit [DecidableEq H] [Algebra.FiniteType k H] [Algebra.Smooth k H] in
lemma counit_eq_zero_of_mem_filtrationIdeal {n : ℕ} {x : H} (hx : x ∈ filtrationIdeal l n) :
    Coalgebra.counit (R := k) x = 0 := by
  have : filtrationIdeal l n ≤ RingHom.ker (Bialgebra.counitAlgHom k H) := by
    refine sup_le (fun y hy ↦ counit_eq_zero_of_mem_unip l hy) ?_
    rw [Ideal.span_le]
    intro y hy
    simp only [Set.mem_iUnion, SetLike.mem_coe] at hy
    obtain ⟨m, ⟨h0, -⟩, hm⟩ := hy
    exact counit_eq_zero_of_mem_lineGrading l (by exact_mod_cast h0.ne') hm
  exact this hx

omit [DecidableEq H] [Algebra.FiniteType k H] [Algebra.Smooth k H] in
lemma filtrationIdeal_mono {n m : ℕ} (h : n ≤ m) : filtrationIdeal l n ≤ filtrationIdeal l m := by
  refine sup_le_sup_left (Ideal.span_mono ?_) _
  intro x hx
  simp only [Set.mem_iUnion, SetLike.mem_coe] at hx ⊢
  obtain ⟨j, ⟨h0, hj⟩, hx⟩ := hx
  exact ⟨j, ⟨h0, by omega⟩, hx⟩

omit [DecidableEq H] [Algebra.FiniteType k H] [Algebra.Smooth k H] in
lemma filtrationIdeal_le_ker (n : ℕ) :
    filtrationIdeal l n ≤ RingHom.ker (Bialgebra.counitAlgHom k H) := fun _ hx ↦ by
  rw [RingHom.mem_ker, Bialgebra.counitAlgHom_apply]
  exact counit_eq_zero_of_mem_filtrationIdeal l hx

omit [DecidableEq H] [Algebra.Smooth k H] in
/-- **(F3), end of the filtration.** `J_n` is the augmentation ideal for `n` large: `U_{≥n} = 1`. -/
theorem filtrationIdeal_eventually :
    ∃ N, ∀ n, N ≤ n → filtrationIdeal l n = RingHom.ker (Bialgebra.counitAlgHom k H) := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra k H).FG)
  set D : ℕ := s.sup fun h ↦ (conjugationAlgHom l h).coeff.support.sup Int.toNat
  set J := filtrationIdeal l (D + 1)
  -- every homogeneous component of a generator is congruent to its counit modulo `J`
  have hA : ∀ h ∈ s, ∀ m : ℤ, (conjugationAlgHom l h).coeff m -
      algebraMap k H (Coalgebra.counit ((conjugationAlgHom l h).coeff m)) ∈ J := by
    intro h hh m
    have hc := coeff_mem_lineGrading (l := l) h m
    rcases lt_trichotomy m 0 with hm | rfl | hm
    · rw [counit_eq_zero_of_mem_lineGrading l hm.ne hc, map_zero, sub_zero]
      exact unip_le_filtrationIdeal l _ (neg_mem_unip l hm hc)
    · exact unip_le_filtrationIdeal l _ (sub_counit_mem_unip l hc)
    · rw [counit_eq_zero_of_mem_lineGrading l hm.ne' hc, map_zero, sub_zero]
      by_cases hz : (conjugationAlgHom l h).coeff m = 0
      · rw [hz]; exact zero_mem _
      · have hsupp : m ∈ (conjugationAlgHom l h).coeff.support := Finsupp.mem_support_iff.mpr hz
        have h1 : m.toNat ≤ (conjugationAlgHom l h).coeff.support.sup Int.toNat :=
          Finset.le_sup (f := Int.toNat) hsupp
        have h2 : (conjugationAlgHom l h).coeff.support.sup Int.toNat ≤ D :=
          Finset.le_sup (f := fun h ↦ (conjugationAlgHom l h).coeff.support.sup Int.toNat) hh
        have hcast : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg hm.le
        refine mem_filtrationIdeal_of_lt l (m := m.toNat) (by omega) (by omega) ?_
        rw [hcast]; exact hc
  have hB : ∀ x ∈ Algebra.adjoin k (s : Set H), x - algebraMap k H (Coalgebra.counit x) ∈ J := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem h hh =>
      have hsum := sum_coeff_conjugationAlgHom (l := l) h
      have : h - algebraMap k H (Coalgebra.counit h) =
          ∑ m ∈ (conjugationAlgHom l h).coeff.support, ((conjugationAlgHom l h).coeff m -
            algebraMap k H (Coalgebra.counit ((conjugationAlgHom l h).coeff m))) := by
        rw [Finset.sum_sub_distrib, ← map_sum (algebraMap k H),
          ← map_sum (Coalgebra.counit (R := k) (A := H)), hsum]
      rw [this]
      exact Ideal.sum_mem _ fun m _ ↦ hA h hh m
    | algebraMap r => simp
    | add x y _ _ hx hy =>
      have : x + y - algebraMap k H (Coalgebra.counit (x + y)) =
          (x - algebraMap k H (Coalgebra.counit x)) + (y - algebraMap k H (Coalgebra.counit y)) := by
        rw [map_add, map_add]; abel
      rw [this]; exact add_mem hx hy
    | mul x y _ _ hx hy =>
      have : x * y - algebraMap k H (Coalgebra.counit (x * y)) =
          (x - algebraMap k H (Coalgebra.counit x)) * y +
            algebraMap k H (Coalgebra.counit x) * (y - algebraMap k H (Coalgebra.counit y)) := by
        rw [Bialgebra.counit_mul, map_mul]; ring
      rw [this]
      exact add_mem (Ideal.mul_mem_right _ _ hx) (Ideal.mul_mem_left _ _ hy)
  refine ⟨D + 1, fun n hn ↦ le_antisymm (filtrationIdeal_le_ker l n) fun x hx ↦ ?_⟩
  rw [RingHom.mem_ker, Bialgebra.counitAlgHom_apply] at hx
  have := hB x (by rw [hs]; trivial)
  rw [hx, map_zero, sub_zero] at this
  exact filtrationIdeal_mono l hn this

/-- **(F4), group level.** Modulo `J_n`, the elements of `λ`-degree `n ≥ 1` are primitive:
`Δ w ≡ w ⊗ 1 + 1 ⊗ w` modulo `J_n ⊗ H + H ⊗ J_n`. So `Sym(W_n) → H/J_n` is a Hopf map,
giving `U_{≥n} → V_n = (W_n^∨)_a` with kernel `U_{≥n+1}` (`J_{n+1} = J_n + (W_n)` by definition),
on which `T` acts linearly through the `T`-grading of `W_n`. -/
theorem comul_sub_mem_of_mem_lineGrading (hP : parabolicDefiningHopfIdeal l = ⊥)
    {n : ℕ} (hn : 0 < n) {w : H} (hw : w ∈ lineGrading l (n : ℤ)) :
    Coalgebra.comul (R := k) w - (w ⊗ₜ (1 : H) + (1 : H) ⊗ₜ w) ∈
      Ideal.map (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := H) (B := H)) (filtrationIdeal l n) ⊔
        Ideal.map (Algebra.TensorProduct.includeRight (R := k) (A := H)) (filtrationIdeal l n) := by
  classical
  set J := filtrationIdeal l n
  set K : Ideal (H ⊗[k] H) :=
    Ideal.map (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := H) (B := H)) J ⊔
      Ideal.map (Algebra.TensorProduct.includeRight (R := k) (A := H)) J
  have hL : ∀ {a : H} (b : H), a ∈ J → a ⊗ₜ[k] b ∈ K := by
    intro a b ha
    have : a ⊗ₜ[k] b = Algebra.TensorProduct.includeLeft (R := k) (S := k) (B := H) a *
        ((1 : H) ⊗ₜ[k] b) := by
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [this]
    exact Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha))
  have hR : ∀ (a : H) {b : H}, b ∈ J → a ⊗ₜ[k] b ∈ K := by
    intro a b hb
    have : a ⊗ₜ[k] b = (a ⊗ₜ[k] (1 : H)) *
        Algebra.TensorProduct.includeRight (R := k) (A := H) b := by
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [this]
    exact Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hb))
  -- `S`: tensors congruent to some `1 ⊗ y + z ⊗ 1`, `y z ∈ H_n`, modulo `K`
  let S : Submodule k (H ⊗[k] H) :=
    { carrier := {t | ∃ y ∈ lineGrading l (n : ℤ), ∃ z ∈ lineGrading l (n : ℤ),
        t - ((1 : H) ⊗ₜ[k] y + z ⊗ₜ[k] (1 : H)) ∈ K}
      add_mem' := by
        rintro t t' ⟨y, hy, z, hz, h⟩ ⟨y', hy', z', hz', h'⟩
        refine ⟨y + y', add_mem hy hy', z + z', add_mem hz hz', ?_⟩
        convert add_mem h h' using 1
        simp only [tmul_add, add_tmul]; abel
      zero_mem' := ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
      smul_mem' := by
        rintro c t ⟨y, hy, z, hz, h⟩
        refine ⟨c • y, Submodule.smul_mem _ c hy, c • z, Submodule.smul_mem _ c hz, ?_⟩
        have e : c • t - ((1 : H) ⊗ₜ[k] (c • y) + (c • z) ⊗ₜ[k] (1 : H)) =
            c • (t - ((1 : H) ⊗ₜ[k] y + z ⊗ₜ[k] (1 : H))) := by
          simp only [smul_sub, smul_add, tmul_smul, smul_tmul']
        rw [e]
        exact Submodule.smul_mem (K.restrictScalars k) c h }
  have hGS : tensorGradingComul l (n : ℤ) ≤ S := by
    refine iSup_le fun p ↦ iSup_le fun q ↦ iSup_le fun hpq ↦ ?_
    rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => simpa using S.zero_mem
    | add t t' ht ht' => rw [map_add]; exact S.add_mem ht ht'
    | tmul a b =>
      obtain ⟨a, ha⟩ := a
      obtain ⟨b, hb⟩ := b
      simp only [TensorProduct.map_tmul, Submodule.subtype_apply]
      by_cases hp : p < 0
      · exact ⟨0, zero_mem _, 0, zero_mem _, by
          simpa using hL b (unip_le_filtrationIdeal l n (neg_mem_unip l hp ha))⟩
      by_cases hq : q < 0
      · exact ⟨0, zero_mem _, 0, zero_mem _, by
          simpa using hR a (unip_le_filtrationIdeal l n (neg_mem_unip l hq hb))⟩
      by_cases hp0 : p = 0
      · subst hp0
        have hq' : q = n := by omega
        subst hq'
        refine ⟨Coalgebra.counit (R := k) a • b, Submodule.smul_mem _ _ hb, 0, zero_mem _, ?_⟩
        have := hL b (unip_le_filtrationIdeal l n (sub_counit_mem_unip l ha))
        convert this using 1
        rw [zero_tmul, add_zero, sub_tmul, Algebra.algebraMap_eq_smul_one, smul_tmul]
      by_cases hq0 : q = 0
      · subst hq0
        have hp' : p = n := by omega
        subst hp'
        refine ⟨0, zero_mem _, Coalgebra.counit (R := k) b • a, Submodule.smul_mem _ _ ha, ?_⟩
        have := hR a (unip_le_filtrationIdeal l n (sub_counit_mem_unip l hb))
        convert this using 1
        rw [tmul_zero, zero_add, tmul_sub, Algebra.algebraMap_eq_smul_one, tmul_smul, smul_tmul']
      · lift p to ℕ using (by omega)
        refine ⟨0, zero_mem _, 0, zero_mem _, ?_⟩
        simpa using hL b (mem_filtrationIdeal_of_lt l (by omega) (by omega) ha)
  obtain ⟨y, hy, z, hz, hyz⟩ := hGS (comul_mem_tensorGradingComul hw)
  -- identify `y ≡ w ≡ z` modulo `J` with the two counit maps
  let φ : H ⊗[k] H →ₐ[k] H := Algebra.TensorProduct.lift
    ((Algebra.ofId k H).comp (Bialgebra.counitAlgHom k H)) (AlgHom.id k H) (fun _ _ ↦ .all _ _)
  let ψ : H ⊗[k] H →ₐ[k] H := Algebra.TensorProduct.lift
    (AlgHom.id k H) ((Algebra.ofId k H).comp (Bialgebra.counitAlgHom k H)) (fun _ _ ↦ .all _ _)
  have hφK : ∀ t ∈ K, φ t ∈ J := by
    intro t ht
    have : Ideal.map φ K ≤ J := by
      rw [Ideal.map_sup]
      refine sup_le ?_ ?_
      · rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
        intro x hx
        simp only [Ideal.mem_comap]
        simp [φ, counit_eq_zero_of_mem_filtrationIdeal l hx]
      · rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
        intro x hx
        simp only [Ideal.mem_comap]
        simpa [φ] using hx
    exact this (Ideal.mem_map_of_mem φ ht)
  have hψK : ∀ t ∈ K, ψ t ∈ J := by
    intro t ht
    have : Ideal.map ψ K ≤ J := by
      rw [Ideal.map_sup]
      refine sup_le ?_ ?_
      · rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
        intro x hx
        simp only [Ideal.mem_comap]
        simpa [ψ] using hx
      · rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
        intro x hx
        simp only [Ideal.mem_comap]
        simp [ψ, counit_eq_zero_of_mem_filtrationIdeal l hx]
    exact this (Ideal.mem_map_of_mem ψ ht)
  have hφΔ : ∀ x : H, φ (Coalgebra.comul (R := k) x) = x := by
    intro x
    have h1 := Coalgebra.rTensor_counit_comul (R := k) x
    have : ∀ t : H ⊗[k] H, φ t = TensorProduct.lid k H (LinearMap.rTensor H Coalgebra.counit t) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
      | tmul a b => simp [φ, Algebra.algebraMap_eq_smul_one]
    rw [this, h1]; simp
  have hψΔ : ∀ x : H, ψ (Coalgebra.comul (R := k) x) = x := by
    intro x
    have h1 := Coalgebra.lTensor_counit_comul (R := k) x
    have : ∀ t : H ⊗[k] H, ψ t = TensorProduct.rid k H (LinearMap.lTensor H Coalgebra.counit t) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
      | tmul a b => simp [ψ, Algebra.algebraMap_eq_smul_one]
    rw [this, h1]; simp
  have hεy := counit_eq_zero_of_mem_lineGrading l (by exact_mod_cast hn.ne') hy
  have hεz := counit_eq_zero_of_mem_lineGrading l (by exact_mod_cast hn.ne') hz
  have hyw : w - y ∈ J := by
    have := hφK _ hyz
    simpa [φ, hφΔ, hεy, hεz, Algebra.algebraMap_eq_smul_one] using this
  have hzw : w - z ∈ J := by
    have := hψK _ hyz
    simpa [ψ, hψΔ, hεy, hεz, Algebra.algebraMap_eq_smul_one] using this
  have e : Coalgebra.comul (R := k) w - (w ⊗ₜ[k] (1 : H) + (1 : H) ⊗ₜ[k] w) =
      (Coalgebra.comul (R := k) w - ((1 : H) ⊗ₜ[k] y + z ⊗ₜ[k] (1 : H))) -
        ((1 : H) ⊗ₜ[k] (w - y)) - ((w - z) ⊗ₜ[k] (1 : H)) := by
    simp only [tmul_sub, sub_tmul]; abel
  rw [e]
  exact sub_mem (sub_mem hyz (hR 1 hyw)) (hL 1 hzw)

omit [Algebra.FiniteType k H] [Algebra.Smooth k H] in
/-- The ideal `J ⊗ H + H ⊗ J` of `H ⊗ H`. -/
lemma tmul_one_mem_sup {J : Ideal H} {a : H} (ha : a ∈ J) (b : H) :
    a ⊗ₜ[k] b ∈ Ideal.map (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := H) (B := H)) J ⊔
      Ideal.map (Algebra.TensorProduct.includeRight (R := k) (A := H)) J := by
  have : a ⊗ₜ[k] b = Algebra.TensorProduct.includeLeft (R := k) (S := k) (B := H) a *
      ((1 : H) ⊗ₜ[k] b) := by simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [this]
  exact Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha))

omit [Algebra.FiniteType k H] [Algebra.Smooth k H] in
lemma one_tmul_mem_sup {J : Ideal H} (a : H) {b : H} (hb : b ∈ J) :
    a ⊗ₜ[k] b ∈ Ideal.map (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := H) (B := H)) J ⊔
      Ideal.map (Algebra.TensorProduct.includeRight (R := k) (A := H)) J := by
  have : a ⊗ₜ[k] b = (a ⊗ₜ[k] (1 : H)) *
      Algebra.TensorProduct.includeRight (R := k) (A := H) b := by
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [this]
  exact Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hb))

omit [Algebra.FiniteType k H] [Algebra.Smooth k H] in
lemma tensorSup_mono {J J' : Ideal H} (h : J ≤ J') :
    Ideal.map (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := H) (B := H)) J ⊔
      Ideal.map (Algebra.TensorProduct.includeRight (R := k) (A := H)) J ≤
    Ideal.map (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := H) (B := H)) J' ⊔
      Ideal.map (Algebra.TensorProduct.includeRight (R := k) (A := H)) J' :=
  sup_le_sup (Ideal.map_mono h) (Ideal.map_mono h)

/-- **(F3), Hopf part: comultiplication.** `Δ J_n ⊆ J_n ⊗ H + H ⊗ J_n`. -/
theorem comul_mem_filtrationIdeal (hP : parabolicDefiningHopfIdeal l = ⊥) (n : ℕ) {x : H}
    (hx : x ∈ filtrationIdeal l n) :
    Coalgebra.comul (R := k) x ∈
      Ideal.map (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := H) (B := H))
          (filtrationIdeal l n) ⊔
        Ideal.map (Algebra.TensorProduct.includeRight (R := k) (A := H)) (filtrationIdeal l n) := by
  set K := Ideal.map (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := H) (B := H))
          (filtrationIdeal l n) ⊔
        Ideal.map (Algebra.TensorProduct.includeRight (R := k) (A := H)) (filtrationIdeal l n)
  have hle : filtrationIdeal l n ≤ K.comap (Bialgebra.comulAlgHom k H) := by
    refine sup_le (fun y hy ↦ ?_) ?_
    · rw [Ideal.mem_comap, Bialgebra.comulAlgHom_apply]
      have h1 := (BialgHom.unipotentDefiningHopfIdeal l).comul_mem (HopfIdeal.mem_toIdeal.mp hy)
      exact tensorSup_mono (unip_le_filtrationIdeal l n) h1
    · rw [Ideal.span_le]
      intro w hw
      simp only [Set.mem_iUnion, SetLike.mem_coe] at hw
      obtain ⟨m, ⟨h0, hm⟩, hw⟩ := hw
      have hwJ : w ∈ filtrationIdeal l n := mem_filtrationIdeal_of_lt l h0 hm hw
      have h1 := comul_sub_mem_of_mem_lineGrading l hP h0 hw
      have h2 := tensorSup_mono (filtrationIdeal_mono l hm.le) h1
      rw [SetLike.mem_coe, Ideal.mem_comap, Bialgebra.comulAlgHom_apply]
      have : Coalgebra.comul (R := k) w = (Coalgebra.comul (R := k) w -
          (w ⊗ₜ[k] (1 : H) + (1 : H) ⊗ₜ[k] w)) + (w ⊗ₜ[k] (1 : H) + (1 : H) ⊗ₜ[k] w) := by abel
      rw [this]
      exact add_mem h2 (add_mem (tmul_one_mem_sup hwJ 1) (one_tmul_mem_sup 1 hwJ))
  have := hle hx
  rwa [Ideal.mem_comap, Bialgebra.comulAlgHom_apply] at this

/-- **(F3), Hopf part: antipode.** `S(J_n) ⊆ J_n`, by strong induction on `n`. -/
theorem antipode_mem_filtrationIdeal (hP : parabolicDefiningHopfIdeal l = ⊥) (n : ℕ) {x : H}
    (hx : x ∈ filtrationIdeal l n) : HopfAlgebra.antipode k x ∈ filtrationIdeal l n := by
  induction n using Nat.strong_induction_on generalizing x with
  | _ n ih =>
  let σ : H ⊗[k] H →ₐ[k] H := Algebra.TensorProduct.lift
    (HopfAlgebra.antipodeAlgHom k H) (AlgHom.id k H) (fun _ _ ↦ .all _ _)
  have hle : filtrationIdeal l n ≤ (filtrationIdeal l n).comap (HopfAlgebra.antipodeAlgHom k H) := by
    refine sup_le (fun y hy ↦ ?_) ?_
    · rw [Ideal.mem_comap]
      exact unip_le_filtrationIdeal l n (HopfIdeal.mem_toIdeal.mpr
        ((BialgHom.unipotentDefiningHopfIdeal l).antipode_mem (HopfIdeal.mem_toIdeal.mp hy)))
    · rw [Ideal.span_le]
      intro w hw
      simp only [Set.mem_iUnion, SetLike.mem_coe] at hw
      obtain ⟨m, ⟨h0, hm⟩, hw⟩ := hw
      rw [SetLike.mem_coe, Ideal.mem_comap]
      have hwJ : w ∈ filtrationIdeal l n := mem_filtrationIdeal_of_lt l h0 hm hw
      have h1 := comul_sub_mem_of_mem_lineGrading l hP h0 hw
      -- `σ` maps `J_m ⊗ H + H ⊗ J_m` into `J_m`
      have hσ : Ideal.map σ (Ideal.map (Algebra.TensorProduct.includeLeft (R := k) (S := k)
          (A := H) (B := H)) (filtrationIdeal l m) ⊔
          Ideal.map (Algebra.TensorProduct.includeRight (R := k) (A := H)) (filtrationIdeal l m)) ≤
          filtrationIdeal l m := by
        rw [Ideal.map_sup]
        refine sup_le ?_ ?_
        · rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
          intro y hy
          simp only [Ideal.mem_comap]
          simpa [σ] using ih m hm hy
        · rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
          intro y hy
          simp only [Ideal.mem_comap]
          simpa [σ] using hy
      have h2 : σ (Coalgebra.comul (R := k) w - (w ⊗ₜ[k] (1 : H) + (1 : H) ⊗ₜ[k] w)) ∈
          filtrationIdeal l n :=
        filtrationIdeal_mono l hm.le (hσ (Ideal.mem_map_of_mem σ h1))
      have hσΔ : σ (Coalgebra.comul (R := k) w) = algebraMap k H (Coalgebra.counit (R := k) w) := by
        have := HopfAlgebra.mul_antipode_rTensor_comul_apply (R := k) w
        rw [← this]
        induction (Coalgebra.comul (R := k) w) using TensorProduct.induction_on with
        | zero => simp
        | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
        | tmul a b => simp [σ]
      rw [map_sub, hσΔ, counit_eq_zero_of_mem_lineGrading l (by exact_mod_cast h0.ne') hw,
        map_zero, zero_sub, map_add] at h2
      have e : HopfAlgebra.antipodeAlgHom k H w =
          -(-(σ (w ⊗ₜ[k] (1 : H)) + σ ((1 : H) ⊗ₜ[k] w))) - w := by
        simp [σ]
      rw [e]
      exact sub_mem (neg_mem h2) hwJ
  have := hle hx
  rwa [Ideal.mem_comap] at this

/-- **(F3), Hopf part.** `J_n` is a Hopf ideal. -/
noncomputable def filtrationHopfIdeal (hP : parabolicDefiningHopfIdeal l = ⊥) (n : ℕ) :
    HopfIdeal k H :=
  HopfIdeal.ofIdeal (filtrationIdeal l n) (fun _ hx ↦ comul_mem_filtrationIdeal l hP n hx)
    (fun _ hx ↦ counit_eq_zero_of_mem_filtrationIdeal l hx)
    (fun _ hx ↦ antipode_mem_filtrationIdeal l hP n hx)

omit [DecidableEq H] [Algebra.FiniteType k H] [Algebra.Smooth k H] in
/-- The nonnegative coefficients of the extension over the origin are those of the conjugate. -/
lemma coeff_extend_ofConv {A : Type u} [CommRing A] [Algebra k A] (g : parabolic A l) (h : H)
    (m : ℕ) : ((extend A l g).ofConv h).coeff m = ((conjugate A l g.1).ofConv h).coeff m := by
  rw [← ofPolyPoint_extend g, ofPolyPoint_apply]
  simp only [ofConv_toConv, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    Polynomial.coe_toLaurentAlg, LaurentPolynomial.coeff_toLaurent]
  exact (Finsupp.mapDomain_apply_of_injective (Nat.castEmbedding (R := ℤ)).injective _ m).symm

/-- The coefficient condition cutting out `U_{≥n}` inside `P(λ)`. -/
def IsFiltPoint {A : Type u} [CommRing A] [Algebra k A] (n : ℕ) (g : WithConv (H →ₐ[k] A)) : Prop :=
  ∀ h : H, ∀ m : ℕ, m < max n 1 →
    g.ofConv ((conjugationAlgHom l h).coeff m) =
      if m = 0 then algebraMap k A (Coalgebra.counit (R := k) h) else 0

omit [DecidableEq H] [Algebra.FiniteType k H] [Algebra.Smooth k H] in
lemma isFiltPoint_of_le_ker {A : Type u} [CommRing A] [Algebra k A] {n : ℕ}
    {g : WithConv (H →ₐ[k] A)} (hg : filtrationIdeal l n ≤ RingHom.ker g.ofConv) :
    IsFiltPoint l n g := by
  intro h m hm
  split_ifs with h0
  · subst h0
    have := hg (unip_le_filtrationIdeal l n (coeff_zero_sub_mem_unip l h))
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at this
    exact_mod_cast this
  · exact hg (mem_filtrationIdeal_of_lt l (Nat.pos_of_ne_zero h0) (by omega)
      (coeff_mem_lineGrading h m))

omit [DecidableEq H] [Algebra.FiniteType k H] [Algebra.Smooth k H] in
lemma le_ker_of_isFiltPoint {A : Type u} [CommRing A] [Algebra k A] {n : ℕ}
    {g : WithConv (H →ₐ[k] A)} (hP : g ∈ parabolic A l) (hg : IsFiltPoint l n g) :
    filtrationIdeal l n ≤ RingHom.ker g.ofConv := by
  refine sup_le ?_ ?_
  · rw [unipotentDefiningHopfIdeal_eq_span, Ideal.span_le]
    rintro x (hx | ⟨h, rfl⟩)
    · simp only [Set.mem_iUnion, SetLike.mem_coe, mem_natMagnet, not_le] at hx
      obtain ⟨m, hm, hx⟩ := hx
      have h1 := (mem_parabolic_iff_forall_coeff_conjugate_eq_zero.mp hP) x m hm
      rw [coeff_conjugate, coeff_of_mem_lineGrading hx, if_pos rfl] at h1
      exact h1
    · have h1 := hg h 0 (by omega)
      rw [if_pos rfl] at h1
      simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, AlgHom.commutes]
      exact_mod_cast sub_eq_zero.mpr h1
  · rw [Ideal.span_le]
    intro w hw
    simp only [Set.mem_iUnion, SetLike.mem_coe] at hw
    obtain ⟨m, ⟨h0, hm⟩, hw⟩ := hw
    have h1 := hg w m (by omega)
    rw [if_neg (by omega)] at h1
    have e : (conjugationAlgHom l w).coeff (m : ℤ) = w := by
      rw [coeff_of_mem_lineGrading hw, if_pos rfl]
    rw [SetLike.mem_coe, RingHom.mem_ker, ← e]
    exact h1

omit [DecidableEq H] [Algebra.FiniteType k H] [Algebra.Smooth k H] in
/-- On `P(λ)(A)`, the coefficient condition is the kernel of truncation of the extension modulo
`X^{max n 1}`: a group homomorphism. -/
lemma truncPoint_eq_one_iff {A : Type u} [CommRing A] [Algebra k A] (n : ℕ) (g : parabolic A l) :
    (AlgHom.mapValue (Ideal.Quotient.mkₐ k (Ideal.span {(Polynomial.X : Polynomial A) ^ max n 1})))
        (extend A l g) = 1 ↔ IsFiltPoint l n g.1 := by
  set Tn := Ideal.span {(Polynomial.X : Polynomial A) ^ max n 1}
  constructor
  · intro h1 h m hm
    have := congrArg (fun p : WithConv (H →ₐ[k] Polynomial A ⧸ Tn) ↦ p.ofConv h) h1
    simp only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
      Ideal.Quotient.mkₐ_eq_mk, AlgHom.convOne_apply] at this
    change Ideal.Quotient.mk Tn _ = Ideal.Quotient.mk Tn
      (Polynomial.C (algebraMap k A (Coalgebra.counit (R := k) h))) at this
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff] at this
    have h2 := this m hm
    rw [Polynomial.coeff_sub, Polynomial.coeff_C, coeff_extend_ofConv, coeff_conjugate,
      sub_eq_zero] at h2
    rw [h2]
  · intro hg
    apply WithConv.ofConv_injective
    ext h
    simp only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
      Ideal.Quotient.mkₐ_eq_mk, AlgHom.convOne_apply]
    change Ideal.Quotient.mk Tn _ = Ideal.Quotient.mk Tn
      (Polynomial.C (algebraMap k A (Coalgebra.counit (R := k) h)))
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff]
    intro m hm
    rw [Polynomial.coeff_sub, Polynomial.coeff_C, coeff_extend_ofConv, coeff_conjugate,
      hg h m hm]
    split_ifs <;> simp

/-- **(F3), normality.** `U_{≥n}` is normal in `B = P(λ)`: it is the kernel of the group
homomorphism `P(λ)(A) → G(A[X]/X^{max n 1})`, truncated extension over the origin. -/
theorem filtrationHopfIdeal_isNormal (hP : parabolicDefiningHopfIdeal l = ⊥) (n : ℕ) :
    (filtrationHopfIdeal l hP n).IsNormal := by
  have hPall : ∀ (A : Type u) [CommRing A] [Algebra k A] (g : WithConv (H →ₐ[k] A)),
      g ∈ parabolic A l := fun A _ _ g ↦ by
    refine (negativeCoefficientIdeal_le_ker_iff l g).mp ?_
    have : negativeCoefficientIdeal l = (parabolicDefiningHopfIdeal l).toIdeal :=
      (parabolicDefiningHopfIdeal_toIdeal l).symm
    rw [this, hP]
    intro x hx
    have : x = 0 := by simpa using hx
    simp [this]
  rw [CommHopfAlgCat.isNormal_iff_quotientPointsSubgroup_normal (H := _root_.CommHopfAlgCat.of k H)]
  intro A
  refine ⟨fun g hg b ↦ ?_⟩
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hg ⊢
  have hg' : filtrationIdeal l n ≤ RingHom.ker g.ofConv := fun x hx ↦ hg x hx
  let φ := (AlgHom.mapValue (Ideal.Quotient.mkₐ k
    (Ideal.span {(Polynomial.X : Polynomial A) ^ max n 1}))).comp (extend A l)
  have hφg : φ ⟨g, hPall A g⟩ = 1 :=
    (truncPoint_eq_one_iff l n ⟨g, hPall A g⟩).mpr (isFiltPoint_of_le_ker l hg')
  have hconj : (⟨b * g * b⁻¹, hPall A _⟩ : parabolic A l) =
      ⟨b, hPall A b⟩ * ⟨g, hPall A g⟩ * (⟨b, hPall A b⟩)⁻¹ := rfl
  have hφ : φ ⟨b * g * b⁻¹, hPall A _⟩ = 1 := by
    rw [hconj, map_mul, map_mul, hφg, mul_one, map_inv, mul_inv_cancel]
  have hfp := (truncPoint_eq_one_iff l n _).mp hφ
  have hle := le_ker_of_isFiltPoint l (hPall A _) hfp
  exact fun x hx ↦ hle hx

/-- The magnet `{0} ∪ [n, ∞)` of `ℤ`: its attractor in `U(λ)` is `U_{≥n}`. -/
def gapMagnet (n : ℕ) : Magnet ℤ where
  carrier := {m | m = 0 ∨ (n : ℤ) ≤ m}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · left; simp
    · right; simpa using hb
    · right; simpa using ha
    · right; omega
  zero_mem' := Or.inl rfl

lemma mem_gapMagnet {n : ℕ} {m : ℤ} : m ∈ gapMagnet n ↔ m = 0 ∨ (n : ℤ) ≤ m := Iff.rfl

omit [DecidableEq H] [Algebra.FiniteType k H] [Algebra.Smooth k H] in
/-- `J_n` is the ideal of the attractor of `U(λ)` for the magnet `{0} ∪ [n, ∞)`. -/
lemma filtrationIdeal_eq_sup_magnetIdeal (n : ℕ) :
    filtrationIdeal l n = (BialgHom.unipotentDefiningHopfIdeal l).toIdeal ⊔
      magnetIdeal (lineGrading l) (gapMagnet n) := by
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    rw [Ideal.span_le]
    intro w hw
    simp only [Set.mem_iUnion, SetLike.mem_coe] at hw
    obtain ⟨m, ⟨h0, hm⟩, hw⟩ := hw
    refine (le_sup_right : _ ≤ (BialgHom.unipotentDefiningHopfIdeal l).toIdeal ⊔ _)
      (Ideal.subset_span ?_)
    simp only [Set.mem_iUnion, SetLike.mem_coe]
    exact ⟨m, by rw [mem_gapMagnet]; omega, hw⟩
  · refine sup_le le_sup_left ?_
    rw [magnetIdeal, Ideal.span_le]
    intro a ha
    simp only [Set.mem_iUnion, SetLike.mem_coe] at ha
    obtain ⟨m, hm, ha⟩ := ha
    rw [mem_gapMagnet] at hm
    rcases lt_or_gt_of_ne (fun h : m = 0 ↦ hm (Or.inl h)) with hneg | hpos
    · exact unip_le_filtrationIdeal l n (neg_mem_unip l hneg ha)
    · lift m to ℕ using hpos.le
      exact mem_filtrationIdeal_of_lt l (by omega) (by omega) ha

omit [Algebra.FiniteType k H] [Algebra.Smooth k H] in
lemma filtrationIdeal_isHomogeneous (n : ℕ) :
    (filtrationIdeal l n).IsHomogeneous (lineGrading l) := by
  rw [filtrationIdeal_eq_sup_magnetIdeal]
  refine (unipotent_lineGrading l).1.sup ?_
  have h := isHomogeneous_magnetIdeal (lineGrading l) (gapMagnet n)
  intro i r hr
  exact h r hr i

/-- **(F3), polynomial quotient.** `H ⧸ J_n` is a polynomial ring. Proof: `J_n = I_U + J_{N}` for
the magnet `N = {0} ∪ [n, ∞)`, so `H ⧸ J_n` is smooth (attractors of the smooth homogeneous `U`,
`smooth_quotient_sup_magnetIdeal`); it is `ℕ`-graded with degree zero `k`; apply (F2). -/
theorem filtrationIdeal_polynomial_graded (hP : parabolicDefiningHopfIdeal l = ⊥) (n : ℕ) :
    ∃ (r : ℕ) (x : Fin r → H) (d : Fin r → ℕ),
      (∀ i, n ≤ d i ∧ 0 < d i ∧ x i ∈ lineGrading l (d i : ℤ)) ∧
      Function.Bijective (MvPolynomial.aeval (R := k)
        (fun i ↦ Ideal.Quotient.mk (filtrationIdeal l n) (x i))) := by
  classical
  set I := (BialgHom.unipotentDefiningHopfIdeal l).toIdeal
  set J := filtrationIdeal l n
  have hIJ : I ≤ J := unip_le_filtrationIdeal l n
  have hJ : J.IsHomogeneous (lineGrading l) := filtrationIdeal_isHomogeneous l n
  -- smoothness
  haveI : Algebra.FormallySmooth k (H ⧸ I) := inferInstance
  haveI hsI : Algebra.Smooth k (H ⧸ I) :=
    ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  have hs : Algebra.Smooth k (H ⧸ (I ⊔ magnetIdeal (lineGrading l) (gapMagnet n))) :=
    smooth_quotient_sup_magnetIdeal (lineGrading l) (unipotent_lineGrading l).1 (gapMagnet n)
  have hJeq : J = I ⊔ magnetIdeal (lineGrading l) (gapMagnet n) :=
    filtrationIdeal_eq_sup_magnetIdeal l n
  haveI hsJ : Algebra.Smooth k (H ⧸ J) := by rw [hJeq]; exact hs
  -- the `ℕ`-grading
  letI := gradedAlgebraHomogQuot (lineGrading l) hJ
  set 𝒬 := homogQuotGrading (lineGrading l) J
  have hneg : ∀ m : ℤ, m < 0 → 𝒬 m = ⊥ := by
    intro m hm
    refine (Submodule.eq_bot_iff _).mpr fun y hy ↦ ?_
    obtain ⟨a, ha, rfl⟩ := (mem_homogQuotGrading _ _).mp hy
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hIJ (neg_mem_unip l hm ha))
  let 𝒬N : ℕ → Submodule k (H ⧸ J) := fun m ↦ 𝒬 (m : ℤ)
  haveI : SetLike.GradedMonoid 𝒬N :=
    { one_mem := SetLike.GradedOne.one_mem (A := 𝒬)
      mul_mem := fun i j _ _ ha hb ↦ by
        have := SetLike.GradedMul.mul_mem (A := 𝒬) (i := (i : ℤ)) (j := (j : ℤ)) ha hb
        simpa [𝒬N, Nat.cast_add] using this }
  have hint : DirectSum.IsInternal 𝒬N := by
    have h := isInternal_homogQuotGrading (lineGrading l) hJ
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at h ⊢
    refine ⟨h.1.comp Nat.cast_injective, ?_⟩
    rw [← h.2]
    apply le_antisymm
    · exact iSup_le fun m ↦ le_iSup 𝒬 (m : ℤ)
    · refine iSup_le fun m ↦ ?_
      rcases lt_or_ge m 0 with hm | hm
      · exact le_of_eq_of_le (hneg m hm) bot_le
      · refine le_iSup_of_le m.toNat ?_
        show 𝒬 m ≤ 𝒬 ((m.toNat : ℕ) : ℤ)
        rw [Int.toNat_of_nonneg hm]
  letI : GradedAlgebra 𝒬N :=
    { (inferInstance : SetLike.GradedMonoid 𝒬N) with
      toDecomposition := hint.chooseDecomposition }
  have h0 : 𝒬N 0 = LinearMap.range (Algebra.linearMap k (H ⧸ J)) := by
    apply le_antisymm
    · intro y hy
      obtain ⟨a, ha, rfl⟩ := (mem_homogQuotGrading _ _).mp hy
      refine ⟨Coalgebra.counit (R := k) a, ?_⟩
      change Ideal.Quotient.mk J (algebraMap k H _) = _
      exact (Ideal.Quotient.eq.mpr (hIJ (sub_counit_mem_unip l ha))).symm
    · rintro _ ⟨c, rfl⟩
      exact (mem_homogQuotGrading _ _).mpr ⟨algebraMap k H c, algebraMap_mem_lineGrading_zero c, rfl⟩
  haveI : Nontrivial (H ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr (by
    intro h
    have h1 : (1 : H) ∈ J := h ▸ Submodule.mem_top
    have := counit_eq_zero_of_mem_filtrationIdeal l h1
    rw [Bialgebra.counit_one] at this
    exact one_ne_zero this)
  obtain ⟨r, x, d, hd, hb⟩ := GradedNakayama.exists_mvPolynomial_equiv_of_graded_smooth' 𝒬N h0
  have hlift : ∀ i, ∃ a ∈ lineGrading l (d i : ℤ), Ideal.Quotient.mk J a = x i :=
    fun i ↦ (mem_homogQuotGrading _ _).mp (hd i).2
  choose a ha hax using hlift
  have hxa : (fun i ↦ Ideal.Quotient.mk J (a i)) = x := funext hax
  refine ⟨r, a, d, fun i ↦ ⟨?_, (hd i).1, ha i⟩, by rw [hxa]; exact hb⟩
  by_contra hlt
  push_neg at hlt
  have hz : x i = 0 := by
    rw [← hax i]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (mem_filtrationIdeal_of_lt l (hd i).1 hlt (ha i))
  have : MvPolynomial.aeval (R := k) x (MvPolynomial.X i) = MvPolynomial.aeval (R := k) x 0 := by
    rw [MvPolynomial.aeval_X, hz, map_zero]
  exact MvPolynomial.X_ne_zero i (hb.1 this)

/-- **(F3), polynomial quotient** (ungraded form, corollary of
`filtrationIdeal_polynomial_graded`). -/
theorem filtrationIdeal_polynomial (hP : parabolicDefiningHopfIdeal l = ⊥) (n : ℕ) :
    ∃ (r : ℕ) (x : Fin r → H ⧸ filtrationIdeal l n),
      Function.Bijective (MvPolynomial.aeval (R := k) x) := by
  obtain ⟨r, x, -, -, hb⟩ := filtrationIdeal_polynomial_graded l hP n
  exact ⟨r, _, hb⟩

/-- **(F3).** Under `P_B(λ) = B`, each `J_n` is a Hopf ideal whose subgroup `U_{≥n}` is normal in
`B`, smooth and connected (its quotient is a polynomial ring). The end of the filtration
(`U_{≥N} = 1`) is `filtrationIdeal_eventually`. -/
theorem filtrationIdeal_spec (hP : parabolicDefiningHopfIdeal l = ⊥) :
    ∀ n, ∃ J : HopfIdeal k H, J.toIdeal = filtrationIdeal l n ∧ J.IsNormal ∧
      ∃ (r : ℕ) (x : Fin r → H ⧸ filtrationIdeal l n),
        Function.Bijective (MvPolynomial.aeval (R := k) x) := fun n ↦
  ⟨filtrationHopfIdeal l hP n, rfl, filtrationHopfIdeal_isNormal l hP n,
    filtrationIdeal_polynomial l hP n⟩

/-- **(P1), homomorphism.** On `U_{≥n}(A)`, `n ≥ 1`, each `w` of `λ`-degree `n` is additive:
`(u u')(w) = u(w) + u'(w)`. So `u ↦ (w ↦ u(w))` is a group hom `U_{≥n}(A) → V_n(A)`. -/
theorem unipotentFiltrationPoints_map_mul (hP : parabolicDefiningHopfIdeal l = ⊥) {n : ℕ}
    (hn : 0 < n) {A : Type u} [CommRing A] [Algebra k A] {u u' : WithConv (H →ₐ[k] A)}
    (hu : filtrationIdeal l n ≤ RingHom.ker u.ofConv)
    (hu' : filtrationIdeal l n ≤ RingHom.ker u'.ofConv) {w : H} (hw : w ∈ lineGrading l (n : ℤ)) :
    (u * u').ofConv w = u.ofConv w + u'.ofConv w := by
  let L : H ⊗[k] H →ₐ[k] A := Algebra.TensorProduct.lift u.ofConv u'.ofConv (fun _ _ ↦ .all _ _)
  have hK : Ideal.map L (Ideal.map (Algebra.TensorProduct.includeLeft (R := k) (S := k)
      (A := H) (B := H)) (filtrationIdeal l n) ⊔
      Ideal.map (Algebra.TensorProduct.includeRight (R := k) (A := H)) (filtrationIdeal l n)) ≤ ⊥ := by
    rw [Ideal.map_sup]
    refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
      intro x hx
      simp only [Ideal.mem_comap, Ideal.mem_bot]
      simpa [L] using hu hx
    · rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
      intro x hx
      simp only [Ideal.mem_comap, Ideal.mem_bot]
      simpa [L] using hu' hx
  have h1 := hK (Ideal.mem_map_of_mem L (comul_sub_mem_of_mem_lineGrading l hP hn hw))
  rw [Ideal.mem_bot, map_sub, sub_eq_zero] at h1
  have e : (u * u').ofConv w = L (Coalgebra.comul (R := k) w) := AlgHom.convMul_apply u u' w
  rw [e, h1]
  simp [L]

omit [DecidableEq H] [Algebra.FiniteType k H] [Algebra.Smooth k H] in
/-- `J_{n+1} = J_n + (H_n)`. -/
lemma filtrationIdeal_succ (n : ℕ) (hn : 0 < n) :
    filtrationIdeal l (n + 1) = filtrationIdeal l n ⊔ Ideal.span (lineGrading l (n : ℤ) : Set H) := by
  apply le_antisymm
  · refine sup_le (le_sup_left.trans le_sup_left) ?_
    rw [Ideal.span_le]
    intro w hw
    simp only [Set.mem_iUnion, SetLike.mem_coe] at hw
    obtain ⟨m, ⟨h0, hm⟩, hw⟩ := hw
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | rfl
    · exact Ideal.mem_sup_left (mem_filtrationIdeal_of_lt l h0 hm hw)
    · exact Ideal.mem_sup_right (Ideal.subset_span hw)
  · refine sup_le (filtrationIdeal_mono l (Nat.le_succ n)) ?_
    rw [Ideal.span_le]
    intro w hw
    exact mem_filtrationIdeal_of_lt l hn (Nat.lt_succ_self n) hw

omit [DecidableEq H] [Algebra.FiniteType k H] [Algebra.Smooth k H] in
/-- **(P1), kernel.** A point of `U_{≥n}` lies in `U_{≥n+1}` iff it kills `H_n`. -/
theorem unipotentFiltrationPoints_ker {n : ℕ} (hn : 0 < n) {A : Type u} [CommRing A] [Algebra k A]
    {u : WithConv (H →ₐ[k] A)} (hu : filtrationIdeal l n ≤ RingHom.ker u.ofConv) :
    filtrationIdeal l (n + 1) ≤ RingHom.ker u.ofConv ↔
      ∀ w ∈ lineGrading l (n : ℤ), u.ofConv w = 0 := by
  rw [filtrationIdeal_succ l n hn]
  constructor
  · intro h w hw
    exact h (Ideal.mem_sup_right (Ideal.subset_span hw))
  · intro h
    refine sup_le hu ?_
    rw [Ideal.span_le]
    intro w hw
    exact h w hw

/-- A monomial of weighted degree `n`, all weights `≥ n ≥ 1`, is a single variable of weight `n`. -/
lemma eq_single_of_wdeg_eq {r n : ℕ} (hn : 0 < n) {d : Fin r → ℕ} (hd : ∀ i, n ≤ d i)
    {α : Fin r →₀ ℕ} (hα : ∑ j, α j * d j = n) : ∃ i, α = Finsupp.single i 1 ∧ d i = n := by
  classical
  have hne : ∃ i, α i ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h] at hα
    omega
  obtain ⟨i, hi⟩ := hne
  have hle : α i * d i ≤ n := hα ▸ Finset.single_le_sum (f := fun j ↦ α j * d j)
    (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
  have hdi := hd i
  have hαi : α i = 1 := by
    rcases Nat.lt_or_ge (α i) 2 with h | h
    · omega
    · have : 2 * n ≤ α i * d i := Nat.mul_le_mul h hdi
      omega
  have hdin : d i = n := by rw [hαi, one_mul] at hle; omega
  refine ⟨i, ?_, hdin⟩
  have hrest : ∀ j, j ≠ i → α j = 0 := by
    intro j hj
    have hsplit := Finset.add_sum_erase Finset.univ (fun j ↦ α j * d j) (Finset.mem_univ i)
    rw [hα, hαi, one_mul, hdin] at hsplit
    have h0 : ∑ x ∈ Finset.univ.erase i, α x * d x = 0 := by omega
    have := (Finset.sum_eq_zero_iff.mp h0) j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
    rcases Nat.mul_eq_zero.mp this with h | h
    · exact h
    · have := hd j; omega
  ext j
  by_cases hj : j = i
  · subst hj; simp [hαi]
  · simp [Finsupp.single_apply, Ne.symm hj, hrest j hj]

/-- **(P1), surjectivity.** Every linear form on `H_n` vanishing on `H_n ∩ J_n` is the restriction
of a `k`-point of `U_{≥n}`: the map `U_{≥n}(k) → V_n(k)` is onto. -/
theorem unipotentFiltrationPoints_surjective (hP : parabolicDefiningHopfIdeal l = ⊥) {n : ℕ}
    (hn : 0 < n) (φ : lineGrading l (n : ℤ) →ₗ[k] k)
    (hφ : ∀ w : lineGrading l (n : ℤ), (w : H) ∈ filtrationIdeal l n → φ w = 0) :
    ∃ u : WithConv (H →ₐ[k] k), filtrationIdeal l n ≤ RingHom.ker u.ofConv ∧
      ∀ w : lineGrading l (n : ℤ), u.ofConv w = φ w := by
  classical
  obtain ⟨r, x, d, hxd, hb⟩ := filtrationIdeal_polynomial_graded l hP n
  set J := filtrationIdeal l n
  let e := AlgEquiv.ofBijective (MvPolynomial.aeval (R := k) (fun i ↦ Ideal.Quotient.mk J (x i))) hb
  let D := {i : Fin r // d i = n}
  have hxD : ∀ i : D, x i.1 ∈ lineGrading l (n : ℤ) := fun i ↦ by
    have := (hxd i.1).2.2; rwa [i.2] at this
  let v : Fin r → k := fun i ↦ if h : d i = n then φ ⟨x i, by have := (hxd i).2.2; rwa [h] at this⟩
    else 0
  let u0 : (H ⧸ J) →ₐ[k] k := (MvPolynomial.aeval v).comp e.symm.toAlgHom
  let u : WithConv (H →ₐ[k] k) := toConv (u0.comp (Ideal.Quotient.mkₐ k J))
  have hux : ∀ i, u.ofConv (x i) = v i := by
    intro i
    have : e.symm (Ideal.Quotient.mk J (x i)) = MvPolynomial.X i := by
      rw [AlgEquiv.symm_apply_eq]
      simp [e]
    simp [u, u0, this]
  have hJ : J ≤ RingHom.ker u.ofConv := fun y hy ↦ by
    simp [u, u0, Ideal.Quotient.eq_zero_iff_mem.mpr hy]
  refine ⟨u, hJ, fun w ↦ ?_⟩
  -- `w ≡ ∑_{d i = n} c i • x i` modulo `J`
  obtain ⟨p, hp⟩ := hb.2 (Ideal.Quotient.mk J w)
  set q := MvPolynomial.aeval (R := k) x p
  have hq : Ideal.Quotient.mk J q = Ideal.Quotient.mk J w := by
    rw [← hp]
    exact MvPolynomial.comp_aeval_apply (R := k) (f := x) (Ideal.Quotient.mkₐ k J) p
  have hwq : (w : H) - q ∈ J := Ideal.Quotient.eq.mp hq.symm
  have hJh : J.IsHomogeneous (lineGrading l) := filtrationIdeal_isHomogeneous l n
  have hproj := hJh (n : ℤ) hwq
  rw [DirectSum.decompose_sub, DirectSum.sub_apply, Submodule.coe_sub,
    DirectSum.decompose_of_mem_same _ w.2] at hproj
  -- the degree-`n` part of `q` is in the span of the `x i`, `d i = n`
  have hspan : (DirectSum.decompose (lineGrading l) q (n : ℤ) : H) ∈
      Submodule.span k (Set.range fun i : D ↦ x i.1) := by
    simp only [q]
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', DirectSum.decompose_sum,
      DFinsupp.finset_sum_apply, Submodule.coe_sum]
    refine Submodule.sum_mem _ fun α _ ↦ ?_
    have hm : (algebraMap k H (p.coeff α)) * ∏ i, x i ^ α i ∈
        lineGrading l (∑ i, α i • ((d i : ℕ) : ℤ)) := by
      have := SetLike.prod_pow_mem_graded (lineGrading l) (F := Finset.univ) (fun i ↦ ((d i : ℕ) : ℤ))
        x α (fun i _ ↦ (hxd i).2.2)
      have h0 := algebraMap_mem_lineGrading_zero (l := l) (p.coeff α)
      simpa using SetLike.mul_mem_graded h0 this
    by_cases hdeg : (∑ i, α i • ((d i : ℕ) : ℤ)) = n
    · rw [hdeg] at hm
      rw [DirectSum.decompose_of_mem_same _ hm]
      have hα : ∑ j, α j * d j = n := by
        have : ((∑ j, α j * d j : ℕ) : ℤ) = n := by push_cast; simpa [nsmul_eq_mul] using hdeg
        exact_mod_cast this
      obtain ⟨i, rfl, hdi⟩ := eq_single_of_wdeg_eq hn (fun i ↦ (hxd i).1) hα
      have hprod : ∏ j, x j ^ (Finsupp.single i 1 : Fin r →₀ ℕ) j = x i := by
        rw [Finset.prod_eq_single i]
        · simp
        · intro j _ hj; simp [Finsupp.single_apply, Ne.symm hj]
        · simp
      rw [hprod, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hdi⟩, rfl⟩)
    · rw [DirectSum.decompose_of_mem_ne _ hm hdeg]
      exact zero_mem _
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hspan
  set y : H := ∑ i : D, c i • x i.1
  have hwy : (w : H) - y ∈ J := by rw [hc]; exact hproj
  have hyn : y ∈ lineGrading l (n : ℤ) := Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (hxD i)
  have hφw : φ w = φ ⟨y, hyn⟩ := by
    have := hφ (w - ⟨y, hyn⟩) (by simpa using hwy)
    rw [map_sub, sub_eq_zero] at this
    exact this
  have hφy : φ ⟨y, hyn⟩ = ∑ i : D, c i * v i.1 := by
    have : (⟨y, hyn⟩ : lineGrading l (n : ℤ)) = ∑ i : D, c i • ⟨x i.1, hxD i⟩ := by
      apply Subtype.ext
      simp [y]
    rw [this, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, smul_eq_mul]
    congr 1
    simp only [v, dif_pos i.2]
  have huw : u.ofConv w = u.ofConv y := by
    have := hJ hwy
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this
    exact this
  rw [huw, hφw, hφy]
  simp only [y, map_sum, map_smul, hux, smul_eq_mul]

omit [DecidableEq H] [Algebra.FiniteType k H] [Algebra.Smooth k H] in
lemma filtrationIdeal_one : filtrationIdeal l 1 = (BialgHom.unipotentDefiningHopfIdeal l).toIdeal := by
  refine le_antisymm (sup_le le_rfl ?_) le_sup_left
  rw [Ideal.span_le]
  intro x hx
  simp only [Set.mem_iUnion, SetLike.mem_coe] at hx
  obtain ⟨m, ⟨h0, h1⟩, -⟩ := hx
  omega

/-- **(T1a) Nullstellensatz step.** If every `k`-point of the reduced closed subgroup `V(S)` is a
product `t · u` with `t ∈ T(k)`, `u ∈ U(k)`, then `V(S) ⊆ T · U`. -/
theorem tuIdeal_one_le_of_points [IsAlgClosed k] (T S : HopfIdeal k H)
    [IsReduced (H ⧸ S.toIdeal)]
    (hpts : ∀ s : WithConv (H →ₐ[k] k), S.toIdeal ≤ RingHom.ker s.ofConv →
      ∃ t u : WithConv (H →ₐ[k] k), T.toIdeal ≤ RingHom.ker t.ofConv ∧ u ∈ unipotent k l ∧
        s = t * u) :
    tuIdeal l T 1 ≤ S.toIdeal := by
  intro x hx
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  refine TauCeti.eq_of_forall_algHom_apply_eq (k := k) (K := k) fun f ↦ ?_
  rw [map_zero]
  let s : WithConv (H →ₐ[k] k) := toConv (f.comp (Ideal.Quotient.mkₐ k S.toIdeal))
  have hs : S.toIdeal ≤ RingHom.ker s.ofConv := fun y hy ↦ by
    simp [s, Ideal.Quotient.eq_zero_iff_mem.mpr hy]
  obtain ⟨t, u, ht, hu, hst⟩ := hpts s hs
  have hu' : filtrationIdeal l 1 ≤ RingHom.ker u.ofConv := by
    rw [filtrationIdeal_one, BialgHom.unipotentDefiningHopfIdeal_toIdeal]
    exact (BialgHom.unipotentCoefficientIdeal_le_ker_iff l u).mpr hu
  let tb : (H ⧸ T.toIdeal) →ₐ[k] k := Ideal.Quotient.liftₐ T.toIdeal t.ofConv fun y hy ↦ ht hy
  let ub : (H ⧸ filtrationIdeal l 1) →ₐ[k] k :=
    Ideal.Quotient.liftₐ (filtrationIdeal l 1) u.ofConv fun y hy ↦ hu' hy
  have hlift : Algebra.TensorProduct.lift t.ofConv u.ofConv (fun _ _ ↦ .all _ _) =
      (Algebra.TensorProduct.lift tb ub (fun _ _ ↦ .all _ _)).comp
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k T.toIdeal)
          (Ideal.Quotient.mkₐ k (filtrationIdeal l 1))) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    rfl
  have hx0 : (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k T.toIdeal)
      (Ideal.Quotient.mkₐ k (filtrationIdeal l 1))) (Coalgebra.comul (R := k) x) = 0 := by
    have := hx
    simp only [tuIdeal, RingHom.mem_ker, AlgHom.coe_comp, Function.comp_apply,
      Bialgebra.comulAlgHom_apply] at this
    exact this
  have hsx : s.ofConv x = 0 := by
    rw [hst, AlgHom.convMul_apply, hlift, AlgHom.comp_apply, hx0, map_zero]
  simpa [s] using hsx

/-- A maximal torus over an algebraically closed field has reduced coordinate ring. -/
theorem isReduced_of_isMaximalTorus [IsAlgClosed k] (S : HopfIdeal k H)
    (hS : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) S) :
    IsReduced (H ⧸ S.toIdeal) := by
  have h1 := hS.1
  have h2 := h1.geometricallyReduced.isReduced
  exact h2

omit [DecidableEq H] [Algebra.FiniteType k H] [Algebra.Smooth k H] in
/-- **Levi decomposition of a point** (Tau Ceti): `s = lim(s) · (lim(s)⁻¹ s)` with the second
factor in `U(λ)`. -/
lemma limit_inv_mul_mem_unipotent {A : Type u} [CommRing A] [Algebra k A] (s : parabolic A l) :
    (limit A l s)⁻¹ * s.1 ∈ unipotent A l := by
  have hlev := limit_mem_levi s
  have hP' : (limit A l s)⁻¹ ∈ parabolic A l := (parabolic A l).inv_mem (levi_le_parabolic hlev)
  refine ⟨⟨(limit A l s)⁻¹ * s.1, (parabolic A l).mul_mem hP' s.2⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  have e : (⟨(limit A l s)⁻¹ * s.1, (parabolic A l).mul_mem hP' s.2⟩ : parabolic A l) =
      ⟨(limit A l s)⁻¹, hP'⟩ * s := rfl
  rw [e, map_mul]
  have hl : limit A l ⟨(limit A l s)⁻¹, hP'⟩ = (limit A l s)⁻¹ :=
    limit_of_mem_levi ((levi A l).inv_mem hlev)
  rw [hl, inv_mul_cancel]

/-- **End of the filtration** (from (F3), `U_{≥N} = 1`): `T · U_{≥N} = T`. -/
theorem tuIdeal_eventually {T : HopfIdeal k H} (h : DynHyp l T) :
    ∃ N, ∀ n, N ≤ n → tuIdeal l T n = T.toIdeal := by
  classical
  obtain ⟨N, hN⟩ := filtrationIdeal_eventually l
  refine ⟨N, fun n hn ↦ ?_⟩
  set E := filtrationIdeal l n with hEdef
  have hE : E = RingHom.ker (Bialgebra.counitAlgHom k H) := hN n hn
  -- in `H ⧸ ker ε` every class is a scalar
  have hmkE : ∀ b : H, Ideal.Quotient.mk E b =
      algebraMap k (H ⧸ E) (Coalgebra.counit (R := k) b) := by
    intro b
    change _ = Ideal.Quotient.mk E (algebraMap k H _)
    refine Ideal.Quotient.eq.mpr ?_
    rw [hE, RingHom.mem_ker, map_sub, Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply,
      Bialgebra.counit_algebraMap, sub_self]
  have hnt : Nontrivial (H ⧸ E) := Ideal.Quotient.nontrivial_iff.mpr (by
    intro h
    have : (1 : H) ∈ E := h ▸ Submodule.mem_top
    rw [hE, RingHom.mem_ker, map_one] at this
    exact one_ne_zero this)
  let ψ : H ⊗[k] H →ₐ[k] H := Algebra.TensorProduct.lift
    (AlgHom.id k H) ((Algebra.ofId k H).comp (Bialgebra.counitAlgHom k H)) (fun _ _ ↦ .all _ _)
  have hψΔ : ∀ x : H, ψ (Coalgebra.comul (R := k) x) = x := by
    intro x
    have h1 := Coalgebra.lTensor_counit_comul (R := k) x
    have : ∀ t : H ⊗[k] H, ψ t = TensorProduct.rid k H (LinearMap.lTensor H Coalgebra.counit t) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
      | tmul a b => simp [ψ, Algebra.algebraMap_eq_smul_one]
    rw [this, h1]; simp
  have hmap : ∀ t : H ⊗[k] H,
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k T.toIdeal) (Ideal.Quotient.mkₐ k E) t =
        Algebra.TensorProduct.includeLeft (R := k) (S := k) (B := H ⧸ E)
          (Ideal.Quotient.mk T.toIdeal (ψ t)) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, ha, hb, map_add, map_add, map_add]
    | tmul a b =>
      simp only [Algebra.TensorProduct.map_tmul, Ideal.Quotient.mkₐ_eq_mk, ψ,
        Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, AlgHom.comp_apply,
        Bialgebra.counitAlgHom_apply, Algebra.ofId_apply, Algebra.TensorProduct.includeLeft_apply,
        map_mul, hmkE b]
      simp only [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        mul_smul_comm, TensorProduct.smul_tmul]
      rw [show (Ideal.Quotient.mk T.toIdeal) (Coalgebra.counit (R := k) b • (1 : H)) =
          Coalgebra.counit (R := k) b • (1 : H ⧸ T.toIdeal) by
            rw [← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one]; rfl,
        mul_smul_comm, mul_one, TensorProduct.smul_tmul]
  have hinj : Function.Injective (Algebra.TensorProduct.includeLeft (R := k) (S := k)
      (A := H ⧸ T.toIdeal) (B := H ⧸ E)) :=
    Algebra.TensorProduct.includeLeft_injective (algebraMap k (H ⧸ E)).injective
  ext x
  simp only [tuIdeal, RingHom.mem_ker, AlgHom.coe_comp, Function.comp_apply,
    Bialgebra.comulAlgHom_apply]
  rw [hmap, hψΔ, ← map_zero (Algebra.TensorProduct.includeLeft (R := k) (S := k)
      (A := H ⧸ T.toIdeal) (B := H ⧸ E))]
  constructor
  · intro h0
    exact Ideal.Quotient.eq_zero_iff_mem.mp (hinj h0)
  · intro hx
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]

omit [DecidableEq H] [Algebra.Smooth k H] in
/-- **(P3)** `U_{≥N}(A) = 1` for `N` large, on points over every `k`-algebra `A`. -/
theorem unipotentFiltrationPoints_eventually :
    ∃ N, ∀ n, N ≤ n → ∀ (A : Type u) [CommRing A] [Algebra k A] (g : WithConv (H →ₐ[k] A)),
      filtrationIdeal l n ≤ RingHom.ker (ofConv g) → g = 1 := by
  obtain ⟨N, hN⟩ := filtrationIdeal_eventually l
  refine ⟨N, fun n hn A _ _ g hg ↦ ?_⟩
  rw [hN n hn] at hg
  apply WithConv.ofConv_injective
  ext x
  have hx : x - algebraMap k H (Coalgebra.counit (R := k) x) ∈
      RingHom.ker (Bialgebra.counitAlgHom k H) := by
    rw [RingHom.mem_ker, map_sub, Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply,
      Bialgebra.counit_algebraMap, sub_self]
  have h0 := hg hx
  rw [RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at h0
  rw [h0]
  rfl

end Dyn

end AlgMag.Reductive
