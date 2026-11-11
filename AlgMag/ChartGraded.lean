import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.GroupTheory.Finiteness
import Mathlib.Order.WellFoundedSet
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.Module.GradedModule
import Mathlib.RingTheory.Adjoin.FG

/-!
# Graded completion for the AHR chart of `D(M)`: §§2–3 of the chart-lemma proof

`ThickeningSystem`: the rings `O_n = Γ(X_n)` of §2. `ThickeningSystem.C`: `C = ⊕_d lim (O_n)_d`.
Results: `lemma_3_1`, `ThickeningSystem.lemma_3_2`, `lemma_3_3_krull`, `lemma_3_3_quot`,
`graded_nakayama`, `ModSystem.lemma_3_4`, `ModSystem.lemma_3_4_unique`,
`ModSystem.lemma_3_4_hom_of_family`, `ModSystem.lemma_3_4_family_of_hom`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace AlgMag.ChartGraded

open DirectSum

section Basics

variable {M : Type*} [AddCommGroup M] [DecidableEq M]

/-- Degree-`e` component of an element of a graded object. -/
noncomputable abbrev comp {N : Type*} [AddCommGroup N] (ℳ : M → AddSubgroup N)
    [Decomposition ℳ] (e : M) (y : N) : N :=
  (decompose ℳ y e : N)

lemma comp_add {N : Type*} [AddCommGroup N] (ℳ : M → AddSubgroup N) [Decomposition ℳ]
    (e : M) (x y : N) : comp ℳ e (x + y) = comp ℳ e x + comp ℳ e y := by
  simp [comp, decompose_add]

lemma comp_sub {N : Type*} [AddCommGroup N] (ℳ : M → AddSubgroup N) [Decomposition ℳ]
    (e : M) (x y : N) : comp ℳ e (x - y) = comp ℳ e x - comp ℳ e y := by
  simp [comp, decompose_sub]

lemma comp_zero {N : Type*} [AddCommGroup N] (ℳ : M → AddSubgroup N) [Decomposition ℳ]
    (e : M) : comp ℳ e (0 : N) = 0 := by
  simp [comp]

lemma comp_mem {N : Type*} [AddCommGroup N] (ℳ : M → AddSubgroup N) [Decomposition ℳ]
    (e : M) (y : N) : comp ℳ e y ∈ ℳ e :=
  (decompose ℳ y e).2

lemma comp_of_mem {N : Type*} [AddCommGroup N] (ℳ : M → AddSubgroup N) [Decomposition ℳ]
    {e : M} {y : N} (h : y ∈ ℳ e) : comp ℳ e y = y :=
  decompose_of_mem_same ℳ h

lemma comp_of_mem_ne {N : Type*} [AddCommGroup N] (ℳ : M → AddSubgroup N) [Decomposition ℳ]
    {e f : M} {y : N} (h : y ∈ ℳ f) (hne : f ≠ e) : comp ℳ e y = 0 :=
  decompose_of_mem_ne ℳ h hne

lemma comp_sum {N : Type*} [AddCommGroup N] (ℳ : M → AddSubgroup N) [Decomposition ℳ]
    (e : M) {τ : Type*} (s : Finset τ) (f : τ → N) :
    comp ℳ e (∑ t ∈ s, f t) = ∑ t ∈ s, comp ℳ e (f t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [comp_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, comp_add, ih]

/-- Every element is the finite sum of its homogeneous components. -/
lemma sum_comp {N : Type*} [AddCommGroup N] (ℳ : M → AddSubgroup N) [Decomposition ℳ]
    (y : N) : ∃ s : Finset M, y = ∑ e ∈ s, comp ℳ e y := by
  classical
  refine ⟨(decompose ℳ y).support, ?_⟩
  exact (DirectSum.sum_support_decompose ℳ y).symm

/-- A subgroup containing all homogeneous components of `y` contains `y`. -/
lemma mem_of_comp_mem {N : Type*} [AddCommGroup N] (ℳ : M → AddSubgroup N) [Decomposition ℳ]
    (P : AddSubgroup N) {y : N} (h : ∀ e, comp ℳ e y ∈ P) : y ∈ P := by
  obtain ⟨s, hs⟩ := sum_comp ℳ y
  rw [hs]
  exact P.sum_mem fun e _ => h e

/-- Graded action: multiplying by a homogeneous scalar shifts components. -/
lemma comp_smul_of_mem {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    (𝒜 : M → AddSubgroup R) (ℳ : M → AddSubgroup N) [Decomposition ℳ]
    [SetLike.GradedSMul 𝒜 ℳ] {i : M} {a : R} (ha : a ∈ 𝒜 i) (e : M) (y : N) :
    comp ℳ (i + e) (a • y) = a • comp ℳ e y := by
  classical
  induction y using Decomposition.inductionOn ℳ with
  | zero => simp [comp_zero]
  | homogeneous y =>
    rename_i f
    have h1 : a • (y : N) ∈ ℳ (i + f) := SetLike.GradedSMul.smul_mem ha y.2
    by_cases hfe : f = e
    · subst hfe
      rw [comp_of_mem ℳ h1, comp_of_mem ℳ y.2]
    · have h2 : i + f ≠ i + e := fun h => hfe (add_left_cancel h)
      rw [comp_of_mem_ne ℳ h1 h2, comp_of_mem_ne ℳ y.2 hfe, smul_zero]
  | add x y hx hy => rw [smul_add, comp_add, comp_add, hx, hy, smul_add]

/-- Ring version of `comp_smul_of_mem`, left factor of degree zero. -/
lemma comp_mul_of_mem_zero {R : Type*} [CommRing R] (𝒜 : M → AddSubgroup R) [GradedRing 𝒜]
    {a : R} (ha : a ∈ 𝒜 0) (e : M) (y : R) : comp 𝒜 e (a * y) = a * comp 𝒜 e y := by
  have := comp_smul_of_mem 𝒜 𝒜 ha e y
  simpa using this

/-- Monomial with exponent `α`. -/
noncomputable def mono {B ι : Type*} [CommRing B] [Fintype ι] (x : ι → B) (α : ι → ℕ) : B :=
  ∏ i, x i ^ α i

lemma mono_zero {B ι : Type*} [CommRing B] [Fintype ι] (x : ι → B) : mono x 0 = 1 := by
  simp [mono]

lemma mono_add {B ι : Type*} [CommRing B] [Fintype ι] (x : ι → B) (α β : ι → ℕ) :
    mono x (α + β) = mono x α * mono x β := by
  simp [mono, pow_add, Finset.prod_mul_distrib]

lemma mono_single {B ι : Type*} [CommRing B] [Fintype ι] [DecidableEq ι] (x : ι → B) (i : ι) :
    mono x (Pi.single i 1) = x i := by
  classical
  unfold mono
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_eq_of_ne hj]
  · simp

/-- Additive weight of an exponent vector. -/
def wt {ι W : Type*} [Fintype ι] [AddCommMonoid W] (δ : ι → W) : (ι → ℕ) →+ W where
  toFun α := ∑ i, α i • δ i
  map_zero' := by simp
  map_add' α β := by simp [add_smul, Finset.sum_add_distrib]

lemma wt_single {ι W : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid W] (δ : ι → W) (i : ι) :
    wt δ (Pi.single i 1) = δ i := by
  show ∑ j, (Pi.single i 1 : ι → ℕ) j • δ j = δ i
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_eq_of_ne hj]
  · simp

lemma mono_mem {B ι : Type*} [CommRing B] [Fintype ι] (𝒜 : M → AddSubgroup B) [GradedRing 𝒜]
    {x : ι → B} {δ : ι → M} (hx : ∀ i, x i ∈ 𝒜 (δ i)) (α : ι → ℕ) :
    mono x α ∈ 𝒜 (wt δ α) := by
  classical
  show ∏ i, x i ^ α i ∈ 𝒜 (∑ i, α i • δ i)
  have key : ∀ s : Finset ι, ∏ i ∈ s, x i ^ α i ∈ 𝒜 (∑ i ∈ s, α i • δ i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using SetLike.GradedOne.one_mem (A := 𝒜)
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact SetLike.GradedMul.mul_mem (SetLike.pow_mem_graded _ (hx a)) ih
  exact key _

/-- A subset of `ℕ^ι` has a finite subset below all its elements (Dickson). -/
lemma exists_finite_below {ι : Type*} [Fintype ι] (S : Set (ι → ℕ)) :
    ∃ T : Finset (ι → ℕ), (↑T ⊆ S) ∧ ∀ α ∈ S, ∃ β ∈ T, β ≤ α := by
  classical
  have hanti : IsAntichain (· ≤ ·) {α | Minimal (· ∈ S) α} := setOfPred_minimal_antichain _
  have hfin : {α : ι → ℕ | Minimal (· ∈ S) α}.Finite :=
    hanti.finite_of_partiallyWellOrderedOn (Set.isPWO_of_wellQuasiOrderedLE _)
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · intro α hα
    simp only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq] at hα
    exact hα.1
  · intro α hα
    obtain ⟨β, hβ, hm⟩ := (Set.isPWO_of_wellQuasiOrderedLE S).exists_le_minimal hα
    exact ⟨β, by simpa using hm, hβ⟩

/-- The degree-zero exponents form a finitely generated monoid (Gordan/Dickson). -/
lemma exists_kernel_gens {ι : Type*} [Fintype ι] (δ : ι → M) :
    ∃ A : Finset (ι → ℕ), (∀ a ∈ A, wt δ a = 0) ∧
      ∀ α, wt δ α = 0 → α ∈ AddSubmonoid.closure (A : Set (ι → ℕ)) := by
  classical
  obtain ⟨A, hA⟩ := AddSubmonoid.fg_eqLocusM (wt δ) (0 : (ι → ℕ) →+ M)
  refine ⟨A, ?_, ?_⟩
  · intro a ha
    have : a ∈ AddMonoidHom.eqLocusM (wt δ) (0 : (ι → ℕ) →+ M) := by
      rw [← hA]; exact AddSubmonoid.subset_closure ha
    simpa using this
  · intro α hα
    rw [hA]
    simpa using hα

end Basics

end AlgMag.ChartGraded

namespace AlgMag.ChartGraded

open DirectSum

section L31

variable {M : Type*} [AddCommGroup M] [DecidableEq M]

/-- Homogeneous elements whose additive closure contains a given finite set. -/
lemma exists_homogeneous_family {N : Type*} [AddCommGroup N] (ℳ : M → AddSubgroup N)
    [Decomposition ℳ] (s : Finset N) :
    ∃ (n : ℕ) (x : Fin n → N) (δ : Fin n → M), (∀ i, x i ∈ ℳ (δ i)) ∧
      (∀ a ∈ s, a ∈ AddSubgroup.closure (Set.range x)) ∧
      ∀ P : AddSubgroup N, (∀ a ∈ s, ∀ e, comp ℳ e a ∈ P) → ∀ i, x i ∈ P := by
  classical
  let T : Finset (N × M) :=
    s.biUnion fun a => (decompose ℳ a).support.image fun e => (comp ℳ e a, e)
  let eT := T.equivFin
  refine ⟨T.card, fun i => (eT.symm i).1.1, fun i => (eT.symm i).1.2, ?_, ?_, ?_⟩
  · intro i
    have := (eT.symm i).2
    simp only [T, Finset.mem_biUnion, Finset.mem_image] at this
    obtain ⟨a, _, e, _, he⟩ := this
    show (eT.symm i).1.1 ∈ ℳ (eT.symm i).1.2
    rw [← he]
    exact comp_mem ℳ e a
  · intro a ha
    rw [← DirectSum.sum_support_decompose ℳ a]
    refine AddSubgroup.sum_mem _ fun e he => AddSubgroup.subset_closure ?_
    have hm : (comp ℳ e a, e) ∈ T := by
      simp only [T, Finset.mem_biUnion, Finset.mem_image]
      exact ⟨a, ha, e, he, rfl⟩
    refine ⟨eT ⟨_, hm⟩, ?_⟩
    simp
  · intro P hP i
    have := (eT.symm i).2
    simp only [T, Finset.mem_biUnion, Finset.mem_image] at this
    obtain ⟨a, ha, e, _, he⟩ := this
    show (eT.symm i).1.1 ∈ P
    rw [← he]
    exact hP a ha e

variable {k B : Type*} [CommRing k] [CommRing B] [Algebra k B]

/-- The degree-zero part of a graded `k`-algebra, as a `k`-subalgebra. -/
def degZero (𝒜 : M → AddSubgroup B) [GradedRing 𝒜] (halg : ∀ r : k, algebraMap k B r ∈ 𝒜 0) :
    Subalgebra k B where
  carrier := 𝒜 0
  mul_mem' {a b} ha hb := by simpa using SetLike.GradedMul.mul_mem ha hb
  add_mem' ha hb := (𝒜 0).add_mem ha hb
  algebraMap_mem' := halg

lemma mem_span_mono {ι : Type*} [Fintype ι] {x : ι → B}
    (hx : Algebra.adjoin k (Set.range x) = ⊤) (y : B) :
    y ∈ Submodule.span k (Set.range (mono x)) := by
  have h1 : y ∈ Subalgebra.toSubmodule (Algebra.adjoin k (Set.range x)) := by rw [hx]; trivial
  rw [Algebra.adjoin_eq_span] at h1
  refine Submodule.span_mono ?_ h1
  intro a ha
  induction ha using Submonoid.closure_induction with
  | mem a h =>
    classical
    obtain ⟨i, rfl⟩ := h
    exact ⟨Pi.single i 1, mono_single x i⟩
  | one => exact ⟨0, mono_zero x⟩
  | mul a b _ _ ha hb =>
    obtain ⟨α, rfl⟩ := ha
    obtain ⟨β, rfl⟩ := hb
    exact ⟨α + β, mono_add x α β⟩

/-- Homogeneous elements of degree `d` are `k`-combinations of monomials of degree `d`. -/
lemma mem_span_mono_deg (𝒜 : M → AddSubgroup B) [GradedRing 𝒜]
    (halg : ∀ r : k, algebraMap k B r ∈ 𝒜 0)
    {ι : Type*} [Fintype ι] {x : ι → B} {δ : ι → M} (hxd : ∀ i, x i ∈ 𝒜 (δ i))
    (hx : Algebra.adjoin k (Set.range x) = ⊤) {d : M} {y : B} (hy : y ∈ 𝒜 d) :
    y ∈ Submodule.span k (mono x '' {α | wt δ α = d}) := by
  suffices h : ∀ z ∈ Submodule.span k (Set.range (mono x)),
      comp 𝒜 d z ∈ Submodule.span k (mono x '' {α | wt δ α = d}) by
    have := h y (mem_span_mono hx y)
    rwa [comp_of_mem 𝒜 hy] at this
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨α, rfl⟩ := hz
    by_cases h : wt δ α = d
    · rw [comp_of_mem 𝒜 (h ▸ mono_mem 𝒜 hxd α)]
      exact Submodule.subset_span ⟨α, h, rfl⟩
    · rw [comp_of_mem_ne 𝒜 (mono_mem 𝒜 hxd α) h]
      exact Submodule.zero_mem _
  | zero => rw [comp_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [comp_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha =>
    rw [Algebra.smul_def, comp_mul_of_mem_zero 𝒜 (halg r), ← Algebra.smul_def]
    exact Submodule.smul_mem _ r ha

/-- Homogeneous algebra generators of a finite type graded algebra. -/
lemma exists_homogeneous_gens (𝒜 : M → AddSubgroup B) [GradedRing 𝒜]
    [hft : Algebra.FiniteType k B] :
    ∃ (n : ℕ) (x : Fin n → B) (δ : Fin n → M), (∀ i, x i ∈ 𝒜 (δ i)) ∧
      Algebra.adjoin k (Set.range x) = ⊤ := by
  obtain ⟨s, hs⟩ := hft.out
  obtain ⟨n, x, δ, hx, hc, _⟩ := exists_homogeneous_family 𝒜 s
  refine ⟨n, x, δ, hx, ?_⟩
  rw [eq_top_iff, ← hs]
  refine Algebra.adjoin_le ?_
  have key : ∀ a ∈ AddSubgroup.closure (Set.range x), a ∈ Algebra.adjoin k (Set.range x) := by
    intro a ha
    induction ha using AddSubgroup.closure_induction with
    | mem a h => exact Algebra.subset_adjoin h
    | zero => exact Subalgebra.zero_mem _
    | add a b _ _ ha hb => exact Subalgebra.add_mem _ ha hb
    | neg a _ ha => exact Subalgebra.neg_mem _ ha
  exact fun a ha => key a (hc a ha)

/-- **Lemma 3.1 (Gordan/Dickson).** If `B` is an `M`-graded finite type `k`-algebra then `B_0` is a
finite type `k`-algebra and each `B_d` is finite over `B_0`. -/
theorem lemma_3_1 (𝒜 : M → AddSubgroup B) [GradedRing 𝒜]
    (halg : ∀ r : k, algebraMap k B r ∈ 𝒜 0) [Algebra.FiniteType k B] :
    (degZero 𝒜 halg).FG ∧ ∀ d : M, ∃ T : Finset B, (∀ t ∈ T, t ∈ 𝒜 d) ∧
      ∀ y ∈ 𝒜 d, y ∈ Submodule.span (degZero 𝒜 halg) (T : Set B) := by
  classical
  obtain ⟨n, x, δ, hxd, hx⟩ := exists_homogeneous_gens (k := k) 𝒜
  constructor
  · obtain ⟨A, hA0, hA⟩ := exists_kernel_gens δ
    refine ⟨A.image (mono x), le_antisymm ?_ ?_⟩
    · refine Algebra.adjoin_le ?_
      intro t ht
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at ht
      obtain ⟨a, ha, rfl⟩ := ht
      have := mono_mem 𝒜 hxd a
      rwa [hA0 a ha] at this
    · intro y hy
      have h0 := mem_span_mono_deg 𝒜 halg hxd hx (d := 0) hy
      have : Submodule.span k (mono x '' {α | wt δ α = 0}) ≤
          Subalgebra.toSubmodule (Algebra.adjoin k ((A.image (mono x) : Finset B) : Set B)) := by
        refine Submodule.span_le.2 ?_
        have key : ∀ α ∈ AddSubmonoid.closure (A : Set (Fin n → ℕ)),
            mono x α ∈ Algebra.adjoin k ((A.image (mono x) : Finset B) : Set B) := by
          intro α hc
          induction hc using AddSubmonoid.closure_induction with
          | mem a h =>
            exact Algebra.subset_adjoin (by simpa using ⟨a, h, rfl⟩)
          | zero => rw [mono_zero]; exact Subalgebra.one_mem _
          | add a b _ _ ha hb => rw [mono_add]; exact Subalgebra.mul_mem _ ha hb
        rintro _ ⟨α, hα, rfl⟩
        exact key α (hA α hα)
      exact this h0
  · intro d
    obtain ⟨T, hTS, hT⟩ := exists_finite_below {α | wt δ α = d}
    refine ⟨T.image (mono x), ?_, ?_⟩
    · intro t ht
      simp only [Finset.mem_image] at ht
      obtain ⟨β, hβ, rfl⟩ := ht
      have := mono_mem 𝒜 hxd β
      rwa [show wt δ β = d from hTS hβ] at this
    · intro y hy
      have h0 := mem_span_mono_deg 𝒜 halg hxd hx hy
      have hle : (Submodule.span k (mono x '' {α | wt δ α = d}) : Submodule k B) ≤
          (Submodule.span (degZero 𝒜 halg) ((T.image (mono x) : Finset B) : Set B)).restrictScalars k := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨α, hα, rfl⟩
        obtain ⟨β, hβ, hle⟩ := hT α hα
        have hsub : α = β + (α - β) := by
          funext i; have h9 : β i ≤ α i := hle i; simp only [Pi.add_apply, Pi.sub_apply]; omega
        have hw : wt δ (α - β) = 0 := by
          have h1 := congrArg (wt δ) hsub
          rw [map_add, show wt δ α = d from hα, show wt δ β = d from hTS hβ] at h1
          simpa using h1.symm
        have hm : mono x (α - β) ∈ degZero 𝒜 halg := by
          have := mono_mem 𝒜 hxd (α - β)
          rwa [hw] at this
        have : mono x α = (⟨mono x (α - β), hm⟩ : degZero 𝒜 halg) • mono x β := by
          conv_lhs => rw [hsub, mono_add]
          rw [Subalgebra.smul_def, smul_eq_mul, mul_comm]
        show mono x α ∈ Submodule.span _ _
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (by simpa using ⟨β, hβ, rfl⟩))
      exact hle h0

/-- Consequence of Lemma 3.1: `B_0` is noetherian over a noetherian base. -/
lemma isNoetherianRing_degZero [IsNoetherianRing k] (𝒜 : M → AddSubgroup B) [GradedRing 𝒜]
    (halg : ∀ r : k, algebraMap k B r ∈ 𝒜 0) [Algebra.FiniteType k B] :
    IsNoetherianRing (degZero 𝒜 halg) := by
  have := (Subalgebra.fg_iff_finiteType _).1 (lemma_3_1 𝒜 halg).1
  exact Algebra.FiniteType.isNoetherianRing k _

end L31

section Approx

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Successive approximation: the common convergence argument of §3 (Lemmas 3.2 and 3.4). If
elements of `Φ i ∩ S` are combinations of the `v w` modulo `Φ (i+1) ∩ S`, with coefficients in
`F (i - e w) ∩ Q w`, and the coefficients can be summed, then `Φ i₀ ∩ S` consists of combinations
with coefficients in `F (i₀ - e w) ∩ Q w`. -/
theorem approx {W : Type*} [Fintype W] (F : ℕ → Ideal R) (Φ : ℕ → AddSubgroup V)
    (S : AddSubgroup V) (Q : W → AddSubgroup R) (v : W → V) (e : W → ℕ)
    (hF0 : F 0 = ⊤) (hF : Antitone F) (hΦ : Antitone Φ) (hsep : ∀ y, (∀ i, y ∈ Φ i) → y = 0)
    (hv : ∀ w i a, a ∈ F i → a • v w ∈ Φ (i + e w))
    (hcompl : ∀ w (z : ℕ → R), (∀ j, z j ∈ F j ∧ z j ∈ Q w) →
      ∃ r ∈ Q w, ∀ N, r - ∑ j ∈ Finset.range N, z j ∈ F N)
    (hSv : ∀ w, ∀ a ∈ Q w, a • v w ∈ S)
    (hstep : ∀ i y, y ∈ Φ i → y ∈ S → ∃ r : W → R, (∀ w, r w ∈ F (i - e w) ∧ r w ∈ Q w) ∧
      y - ∑ w, r w • v w ∈ Φ (i + 1))
    (i₀ : ℕ) {y : V} (hy : y ∈ Φ i₀) (hyS : y ∈ S) :
    ∃ r : W → R, (∀ w, r w ∈ F (i₀ - e w) ∧ r w ∈ Q w) ∧ y = ∑ w, r w • v w := by
  classical
  choose! stp hstp1 hstp2 using hstep
  -- the recursive sequence of remainders
  let Y : (k : ℕ) → {t : V // t ∈ Φ (i₀ + k) ∧ t ∈ S} := fun k =>
    Nat.rec ⟨y, hy, hyS⟩
      (fun k t => ⟨t.1 - ∑ w, stp (i₀ + k) t.1 w • v w,
        hstp2 _ _ t.2.1 t.2.2,
        S.sub_mem t.2.2 (S.sum_mem fun w _ => hSv w _ (hstp1 _ _ t.2.1 t.2.2 w).2)⟩) k
  let c : ℕ → W → R := fun k w => stp (i₀ + k) (Y k).1 w
  have hc : ∀ k w, c k w ∈ F (i₀ + k - e w) ∧ c k w ∈ Q w := fun k w =>
    hstp1 _ _ (Y k).2.1 (Y k).2.2 w
  have hYs : ∀ k, (Y (k + 1)).1 = (Y k).1 - ∑ w, c k w • v w := fun k => rfl
  have hYN : ∀ N, y - ∑ w, (∑ k ∈ Finset.range N, c k w) • v w = (Y N).1 := by
    intro N
    induction N with
    | zero => simp [Y]
    | succ N ih =>
      rw [hYs, ← ih]
      simp only [Finset.sum_range_succ, add_smul, Finset.sum_add_distrib]
      abel
  -- summation of coefficients
  have hsum : ∀ w, ∃ r ∈ Q w, ∀ N, r - ∑ k ∈ Finset.range N, c k w ∈ F (i₀ + N - e w) := by
    intro w
    let zt : ℕ → R := fun j => if i₀ ≤ j then c (j - i₀) w else 0
    have hzt : ∀ j, zt j ∈ F (j - e w) ∧ zt j ∈ Q w := by
      intro j
      by_cases h : i₀ ≤ j
      · simp only [zt, if_pos h]
        refine ⟨?_, (hc _ _).2⟩
        have := (hc (j - i₀) w).1
        rwa [show i₀ + (j - i₀) - e w = j - e w by omega] at this
      · simp [zt, if_neg h]
    obtain ⟨r', hr'Q, hr'⟩ := hcompl w (fun j => zt (e w + j)) (fun j => by
      have := hzt (e w + j)
      rwa [show e w + j - e w = j by omega] at this)
    refine ⟨r' + ∑ j ∈ Finset.range (e w), zt j,
      (Q w).add_mem hr'Q ((Q w).sum_mem fun j _ => (hzt j).2), ?_⟩
    intro N
    have h1 : ∑ k ∈ Finset.range N, c k w = ∑ j ∈ Finset.range (i₀ + N), zt j := by
      rw [Finset.sum_range_add]
      have : ∑ j ∈ Finset.range i₀, zt j = 0 :=
        Finset.sum_eq_zero fun j hj => by
          simp [zt, if_neg (by simpa using Finset.mem_range.1 hj : ¬ i₀ ≤ j)]
      rw [this, zero_add]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [zt]
    rw [h1]
    by_cases hN : e w ≤ i₀ + N
    · have h2 : i₀ + N = e w + (i₀ + N - e w) := by omega
      have h3 := hr' (i₀ + N - e w)
      have h5 := Finset.sum_range_add zt (e w) (i₀ + N - e w)
      rw [← h2] at h5
      rw [h5]
      convert h3 using 1
      ring
    · rw [show i₀ + N - e w = 0 by omega, hF0]
      trivial
  choose r hrQ hr using hsum
  refine ⟨r, fun w => ⟨?_, hrQ w⟩, ?_⟩
  · simpa using hr w 0
  · rw [← sub_eq_zero]
    refine hsep _ fun i => ?_
    refine hΦ (Nat.le_add_left i i₀) ?_
    have h4 : y - ∑ w, r w • v w = (Y i).1 - ∑ w, (r w - ∑ k ∈ Finset.range i, c k w) • v w := by
      rw [← hYN i]
      simp only [sub_smul, Finset.sum_sub_distrib]
      abel
    rw [h4]
    refine (Φ _).sub_mem (Y i).2.1 ((Φ _).sum_mem fun w _ => ?_)
    refine hΦ ?_ (hv w _ _ (hr w i))
    omega

end Approx

section Filtered

open Polynomial

variable {R : Type*} [CommRing R]

/-- A separated complete multiplicative filtration by ideals. -/
structure IsCompleteFiltration (F : ℕ → Ideal R) : Prop where
  zero : F 0 = ⊤
  anti : Antitone F
  mul : ∀ i j, F i * F j ≤ F (i + j)
  sep : ∀ y, (∀ i, y ∈ F i) → y = 0
  compl : ∀ z : ℕ → R, (∀ j, z j ∈ F j) → ∃ w, ∀ N, w - ∑ j ∈ Finset.range N, z j ∈ F N

/-- Rees ring of a filtration, inside `R[X]`. -/
def rees (F : ℕ → Ideal R) (hF : IsCompleteFiltration F) : Subring R[X] where
  carrier := {p | ∀ i, p.coeff i ∈ F i}
  mul_mem' {p q} hp hq i := by
    rw [coeff_mul]
    refine Ideal.sum_mem _ fun x hx => ?_
    rw [← Finset.mem_antidiagonal.1 hx]
    exact hF.mul _ _ (Ideal.mul_mem_mul (hp _) (hq _))
  one_mem' i := by
    rw [hF.zero |> fun _ => coeff_one]
    split_ifs with h
    · subst h; rw [hF.zero]; trivial
    · exact Ideal.zero_mem _
  add_mem' {p q} hp hq i := by rw [coeff_add]; exact Ideal.add_mem _ (hp i) (hq i)
  zero_mem' i := by simp
  neg_mem' {p} hp i := by rw [coeff_neg]; exact Ideal.neg_mem_iff _ |>.2 (hp i)

/-- The kernel of `Rees → gr`. -/
def reesKer (F : ℕ → Ideal R) (hF : IsCompleteFiltration F) : Ideal (rees F hF) where
  carrier := {p | ∀ i, (p : R[X]).coeff i ∈ F (i + 1)}
  add_mem' {p q} hp hq i := by
    simp only [AddMemClass.coe_add, coeff_add]
    exact Ideal.add_mem _ (hp i) (hq i)
  zero_mem' i := by simp
  smul_mem' c {p} hp i := by
    simp only [smul_eq_mul, MulMemClass.coe_mul, coeff_mul]
    refine Ideal.sum_mem _ fun x hx => ?_
    have hx' := Finset.mem_antidiagonal.1 hx
    have := hF.mul _ _ (Ideal.mul_mem_mul (c.2 x.1) (hp x.2))
    rwa [show x.1 + (x.2 + 1) = i + 1 by omega] at this

/-- The associated graded ring of a filtration, as a quotient of the Rees ring. -/
abbrev grRing (F : ℕ → Ideal R) (hF : IsCompleteFiltration F) := rees F hF ⧸ reesKer F hF

/-- The element `y T^i` of the Rees ring. -/
noncomputable def reesT (F : ℕ → Ideal R) (hF : IsCompleteFiltration F) (i : ℕ) (y : R)
    (hy : y ∈ F i) : rees F hF :=
  ⟨monomial i y, fun j => by
    rw [coeff_monomial]
    split_ifs with h
    · exact h ▸ hy
    · exact Ideal.zero_mem _⟩

/-- Complete filtered ring with noetherian associated graded is noetherian
([God56, Thm 4], cited in AHR Lemma 4.9); used in Lemma 3.2. -/
theorem isNoetherianRing_of_gr (F : ℕ → Ideal R) (hF : IsCompleteFiltration F)
    [IsNoetherianRing (grRing F hF)] : IsNoetherianRing R := by
  classical
  rw [isNoetherianRing_iff_ideal_fg]
  intro J
  let gens : Set (grRing F hF) :=
    {g | ∃ (i : ℕ) (y : R) (hy : y ∈ F i), y ∈ J ∧ g = Ideal.Quotient.mk _ (reesT F hF i y hy)}
  have hfg : (Ideal.span gens).FG := IsNoetherian.noetherian _
  obtain ⟨s, hsg, hs⟩ := (Submodule.fg_span_iff_fg_span_finset_subset gens).1 hfg
  -- choose representatives
  have hrep : ∀ g : s, ∃ (i : ℕ) (y : R) (hy : y ∈ F i), y ∈ J ∧
      (g : grRing F hF) = Ideal.Quotient.mk _ (reesT F hF i y hy) := fun g => hsg g.2
  choose ei yi hyi hyJ hg using hrep
  have hstep : ∀ i y, y ∈ F i → y ∈ J → ∃ r : s → R,
      (∀ w, r w ∈ F (i - ei w) ∧ r w ∈ (⊤ : AddSubgroup R)) ∧
      y - ∑ w, r w • yi w ∈ F (i + 1) := by
    intro i y hy hyJ'
    have hmem : (Ideal.Quotient.mk (reesKer F hF) (reesT F hF i y hy)) ∈
        Ideal.span (s : Set (grRing F hF)) := by
      show _ ∈ Submodule.span _ _
      rw [← hs]
      exact Submodule.subset_span ⟨i, y, hy, hyJ', rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_finset').1 hmem
    have hlift : ∀ g : s, ∃ P : rees F hF, Ideal.Quotient.mk (reesKer F hF) P = c g :=
      fun g => Ideal.Quotient.mk_surjective _
    choose P hP using hlift
    have hker : (reesT F hF i y hy - ∑ g : s, P g * reesT F hF (ei g) (yi g) (hyi g)) ∈
        reesKer F hF := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hc, map_sum, sub_eq_zero]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [map_mul, hP, ← hg, smul_eq_mul]
    refine ⟨fun g => if ei g ≤ i then (P g : R[X]).coeff (i - ei g) else 0, ?_, ?_⟩
    · intro g
      refine ⟨?_, trivial⟩
      dsimp only
      split_ifs
      · exact (P g).2 _
      · exact Ideal.zero_mem _
    · have h := hker i
      have hcoe : ((reesT F hF i y hy - ∑ g : s, P g * reesT F hF (ei g) (yi g) (hyi g) :
          rees F hF) : R[X]).coeff i =
          y - ∑ g : s, (if ei g ≤ i then (P g : R[X]).coeff (i - ei g) else 0) • yi g := by
        have : ((reesT F hF i y hy - ∑ g : s, P g * reesT F hF (ei g) (yi g) (hyi g) :
            rees F hF) : R[X]) = monomial i y -
              ∑ g : s, (P g : R[X]) * monomial (ei g) (yi g) := by
          simp [reesT]
        rw [this, coeff_sub, coeff_monomial, if_pos rfl, finset_sum_coeff]
        congr 1
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [← C_mul_X_pow_eq_monomial, ← mul_assoc, coeff_mul_X_pow']
        split_ifs <;> simp [coeff_mul_C]
      rwa [hcoe] at h
  -- span
  refine ⟨(s.attach.image fun g => yi g), le_antisymm ?_ ?_⟩
  · refine Ideal.span_le.2 ?_
    intro t ht
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at ht
    obtain ⟨g, _, rfl⟩ := ht
    exact hyJ g
  · intro x hx
    let hsG : Fintype s := inferInstance
    obtain ⟨r, _, hr⟩ := approx (W := s) F (fun i => (F i).toAddSubgroup) J.toAddSubgroup (fun _ => ⊤) yi ei
      hF.zero hF.anti (fun i j hij => hF.anti hij) (fun y hy => hF.sep y hy)
      (fun w i a ha => hF.mul _ _ (Ideal.mul_mem_mul ha (hyi w)))
      (fun w z hz => by
        obtain ⟨u, hu⟩ := hF.compl z fun j => (hz j).1
        exact ⟨u, trivial, hu⟩)
      (fun w a _ => J.smul_mem a (hyJ w))
      (fun i y hy hyS => hstep i y hy hyS)
      0 (y := x) (by show x ∈ F 0; rw [hF.zero]; trivial) hx
    rw [hr]
    refine Ideal.sum_mem _ fun w _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ?_)
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨w, Finset.mem_attach _ _, rfl⟩)

end Filtered

end AlgMag.ChartGraded

namespace AlgMag.ChartGraded

open DirectSum

section GLim

variable {M : Type*} [AddCommGroup M] [DecidableEq M]
variable {V : ℕ → Type*} [∀ n, AddCommGroup (V n)] (ℳ : ∀ n, M → AddSubgroup (V n))
  [∀ n, Decomposition (ℳ n)] (p : ∀ n, V (n + 1) →+ V n)

/-- `lim (V_n)_d`, as a subgroup of the product. -/
def glim (d : M) : AddSubgroup (∀ n, V n) where
  carrier := {u | (∀ n, p n (u (n + 1)) = u n) ∧ ∀ n, u n ∈ ℳ n d}
  add_mem' {a b} ha hb := ⟨fun n => by simp [ha.1 n, hb.1 n],
    fun n => (ℳ n d).add_mem (ha.2 n) (hb.2 n)⟩
  zero_mem' := ⟨fun n => by simp, fun n => (ℳ n d).zero_mem⟩
  neg_mem' {a} ha := ⟨fun n => by simp [ha.1 n], fun n => (ℳ n d).neg_mem (ha.2 n)⟩

/-- `⊕_d lim (V_n)_d`, as a subgroup of the product. -/
def gL : AddSubgroup (∀ n, V n) := ⨆ d, glim ℳ p d

lemma glim_le_gL (d : M) : glim ℳ p d ≤ gL ℳ p := le_iSup (glim ℳ p) d

lemma gL_compat {u : ∀ n, V n} (hu : u ∈ gL ℳ p) (n : ℕ) : p n (u (n + 1)) = u n := by
  induction hu using AddSubgroup.iSup_induction' with
  | hp d x hx => exact hx.1 n
  | h1 => simp
  | hadd x y _ _ hx hy => simp [hx, hy]

variable {ℳ p}

lemma p_comp (hp : ∀ n d y, y ∈ ℳ (n + 1) d → p n y ∈ ℳ n d) (n : ℕ) (e : M) (y : V (n + 1)) :
    p n (comp (ℳ (n + 1)) e y) = comp (ℳ n) e (p n y) := by
  classical
  induction y using Decomposition.inductionOn (ℳ (n + 1)) with
  | zero => simp [comp_zero]
  | homogeneous y =>
    rename_i f
    by_cases hfe : f = e
    · subst hfe
      rw [comp_of_mem _ y.2, comp_of_mem _ (hp n f _ y.2)]
    · rw [comp_of_mem_ne _ y.2 hfe, comp_of_mem_ne _ (hp n f _ y.2) hfe, map_zero]
  | add x y hx hy => simp only [comp_add, map_add, hx, hy]

/-- Level-wise component of a compatible family. -/
lemma lcomp_mem (hp : ∀ n d y, y ∈ ℳ (n + 1) d → p n y ∈ ℳ n d) {u : ∀ n, V n}
    (hu : ∀ n, p n (u (n + 1)) = u n) (e : M) :
    (fun n => comp (ℳ n) e (u n)) ∈ glim ℳ p e :=
  ⟨fun n => by rw [p_comp hp, hu], fun n => comp_mem _ _ _⟩

/-- Push down from level `l` to level `m ≤ l`. -/
noncomputable def down (p : ∀ n, V (n + 1) →+ V n) : (l m : ℕ) → m ≤ l → V l → V m
  | 0, m, h, y => (Nat.le_zero.1 h).symm ▸ y
  | l + 1, m, h, y =>
    if h' : m ≤ l then down p l m h' (p l y)
    else (by omega : l + 1 = m) ▸ y

lemma down_self (p : ∀ n, V (n + 1) →+ V n) (l : ℕ) (y : V l) : down p l l le_rfl y = y := by
  cases l with
  | zero => rfl
  | succ l => simp [down]

lemma down_succ (p : ∀ n, V (n + 1) →+ V n) (l m : ℕ) (h : m ≤ l) (y : V (l + 1)) :
    down p (l + 1) m (by omega) y = down p l m h (p l y) := by
  simp [down, h]

lemma p_down (p : ∀ n, V (n + 1) →+ V n) (l m : ℕ) (h : m + 1 ≤ l) (y : V l) :
    p m (down p l (m + 1) h y) = down p l m (by omega) y := by
  induction l with
  | zero => omega
  | succ l ih =>
    by_cases hml : m + 1 ≤ l
    · rw [down_succ p l (m + 1) hml, down_succ p l m (by omega), ih hml]
    · obtain rfl : l = m := by omega
      rw [down_self, down_succ p l l le_rfl, down_self]

lemma down_mem (hp : ∀ n d y, y ∈ ℳ (n + 1) d → p n y ∈ ℳ n d) (l m : ℕ) (h : m ≤ l) {d : M}
    {y : V l} (hy : y ∈ ℳ l d) : down p l m h y ∈ ℳ m d := by
  induction l with
  | zero =>
    obtain rfl : m = 0 := by omega
    exact hy
  | succ l ih =>
    by_cases hml : m ≤ l
    · rw [down_succ p l m hml]; exact ih hml (hp _ _ _ hy)
    · obtain rfl : m = l + 1 := by omega
      rwa [down_self]

/-- Every homogeneous element of `V_n` lifts to the limit (surjective transition maps). -/
theorem exists_lift (hp : ∀ n d y, y ∈ ℳ (n + 1) d → p n y ∈ ℳ n d)
    (hs : ∀ n, Function.Surjective (p n)) (n : ℕ) {d : M} {x : V n} (hx : x ∈ ℳ n d) :
    ∃ u ∈ glim ℳ p d, u n = x := by
  classical
  have hs' : ∀ m (t : V m), t ∈ ℳ m d → ∃ y, y ∈ ℳ (m + 1) d ∧ p m y = t := by
    intro m t ht
    obtain ⟨y, rfl⟩ := hs m t
    refine ⟨comp _ d y, comp_mem _ _ _, ?_⟩
    rw [p_comp hp, comp_of_mem _ ht]
  choose! lf hlf1 hlf2 using hs'
  let Y : (k : ℕ) → {t : V (n + k) // t ∈ ℳ (n + k) d} := fun k =>
    Nat.rec ⟨x, hx⟩ (fun k t => ⟨lf (n + k) t.1, hlf1 _ _ t.2⟩) k
  have hY : ∀ k, p (n + k) (Y (k + 1)).1 = (Y k).1 := fun k => hlf2 _ _ (Y k).2
  refine ⟨fun m => down p (n + m) m (by omega) (Y m).1, ⟨fun m => ?_, fun m => ?_⟩, ?_⟩
  · show p m (down p (n + (m + 1)) (m + 1) (by omega) (Y (m + 1)).1) = _
    rw [p_down]
    show down p ((n + m) + 1) m (by omega) (Y (m + 1)).1 = _
    rw [down_succ p (n + m) m (by omega)]
    show down p (n + m) m _ (p (n + m) (Y (m + 1)).1) = _
    rw [hY]
  · exact down_mem hp _ _ _ (Y m).2
  · have key : ∀ k, down p (n + k) n (by omega) (Y k).1 = x := by
      intro k
      induction k with
      | zero => exact down_self p n x
      | succ k ih =>
        show down p ((n + k) + 1) n (by omega) (Y (k + 1)).1 = x
        rw [down_succ p (n + k) n (by omega), hY]
        exact ih
    exact key n

/-! ### Grading on an abstract copy of `⊕_d lim (V_n)_d` -/

variable {T : Type*} [AddCommGroup T] (ι : T →+ ∀ n, V n)

/-- The grading induced on `T` from the limits. -/
def tgrade (ℳ : ∀ n, M → AddSubgroup (V n)) [∀ n, Decomposition (ℳ n)]
    (p : ∀ n, V (n + 1) →+ V n) (ι : T →+ ∀ n, V n) (d : M) : AddSubgroup T :=
  (glim ℳ p d).comap ι

lemma coe_lvl_comp (x : ⨁ d, tgrade ℳ p ι d) (n : ℕ) (e : M) :
    comp (ℳ n) e (ι (DirectSum.coeAddMonoidHom (tgrade ℳ p ι) x) n) = ι (x e : T) n := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp [comp_zero]
  | of i y =>
    rw [DirectSum.coeAddMonoidHom_of]
    by_cases h : i = e
    · subst h
      rw [DirectSum.of_eq_same, comp_of_mem _ (y.2.2 n)]
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), comp_of_mem_ne _ (y.2.2 n) h]
      simp
  | add x y hx hy =>
    simp only [map_add, DirectSum.add_apply, AddMemClass.coe_add, Pi.add_apply, comp_add, hx, hy]

theorem tgrade_internal (hinj : Function.Injective ι) (hr : ∀ u, u ∈ gL ℳ p → ∃ t, ι t = u)
    (hr' : ∀ t, ι t ∈ gL ℳ p) : DirectSum.IsInternal (tgrade ℳ p ι) := by
  classical
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    refine DFinsupp.ext fun e => Subtype.ext (hinj (funext fun n => ?_))
    have := coe_lvl_comp (ℳ := ℳ) (p := p) ι x n e
    rw [hx] at this
    simpa [comp_zero] using this.symm
  · intro t
    have hle : gL ℳ p ≤
        (DirectSum.coeAddMonoidHom (tgrade ℳ p ι)).range.map ι := by
      refine iSup_le fun d u hu => ?_
      obtain ⟨t, rfl⟩ := hr u (glim_le_gL ℳ p d hu)
      exact ⟨t, ⟨DirectSum.of (fun d => tgrade ℳ p ι d) d ⟨t, hu⟩,
        by rw [DirectSum.coeAddMonoidHom_of]⟩, rfl⟩
    obtain ⟨t', ⟨x, hx⟩, ht'⟩ := hle (hr' t)
    exact ⟨x, by rw [hx]; exact hinj ht'⟩

lemma lvl_comp (hp : ∀ n d y, y ∈ ℳ (n + 1) d → p n y ∈ ℳ n d)
    [Decomposition (tgrade ℳ p ι)] (e : M) (t : T) (n : ℕ) :
    ι (comp (tgrade ℳ p ι) e t) n = comp (ℳ n) e (ι t n) := by
  classical
  induction t using Decomposition.inductionOn (tgrade ℳ p ι) with
  | zero => simp [comp_zero]
  | homogeneous y =>
    rename_i f
    by_cases hfe : f = e
    · subst hfe
      rw [comp_of_mem _ y.2, comp_of_mem _ (y.2.2 n)]
    · rw [comp_of_mem_ne _ y.2 hfe, comp_of_mem_ne _ (y.2.2 n) hfe]; simp
  | add x y hx hy => simp only [comp_add, map_add, Pi.add_apply, hx, hy]

end GLim

/-- The inverse system of `§2`: the graded rings `O_n = Γ(X_n)` of the thickenings of the orbit, with
ideals `I_n` (the image of the ideal `I` of `O` in `X`). -/
structure ThickeningSystem (M : Type*) [AddCommGroup M] [DecidableEq M] where
  /-- `O_n = Γ(X_n)`. -/
  O : ℕ → Type*
  [ring : ∀ n, CommRing (O n)]
  /-- the grading of `O_n` -/
  𝒜 : ∀ n, M → AddSubgroup (O n)
  [gr : ∀ n, GradedRing (𝒜 n)]
  /-- transition map -/
  π : ∀ n, O (n + 1) →+* O n
  π_mem : ∀ n d y, y ∈ 𝒜 (n + 1) d → π n y ∈ 𝒜 n d
  π_surj : ∀ n, Function.Surjective (π n)
  /-- ideal of `O` in `X_n` -/
  I : ∀ n, Ideal (O n)
  I_hom : ∀ n, (I n).IsHomogeneous (𝒜 n)
  I_zero : I 0 = ⊥
  I_nil : ∀ n, I n ^ (n + 1) = ⊥
  I_map : ∀ n, (I (n + 1)).map (π n) = I n
  ker_π : ∀ n, RingHom.ker (π n) = I (n + 1) ^ (n + 1)
  /-- `I/I²` is a finite module (coherent on the affine orbit). -/
  I_fg : (I 1).FG

attribute [instance] ThickeningSystem.ring ThickeningSystem.gr

namespace ThickeningSystem

variable {M : Type*} [AddCommGroup M] [DecidableEq M] (S : ThickeningSystem M)

/-- The transition maps, additively. -/
def πa (n : ℕ) : S.O (n + 1) →+ S.O n := (S.π n).toAddMonoidHom

lemma glim_mul {i j : M} {u v : ∀ n, S.O n} (hu : u ∈ glim S.𝒜 S.πa i)
    (hv : v ∈ glim S.𝒜 S.πa j) : u * v ∈ glim S.𝒜 S.πa (i + j) := by
  refine ⟨fun n => ?_, fun n => SetLike.GradedMul.mul_mem (hu.2 n) (hv.2 n)⟩
  have h1 := hu.1 n
  have h2 := hv.1 n
  simp only [πa, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe] at h1 h2 ⊢
  simp [h1, h2]

lemma glim_one : (1 : ∀ n, S.O n) ∈ glim S.𝒜 S.πa 0 :=
  ⟨fun n => by simp [πa], fun n => SetLike.GradedOne.one_mem⟩

/-- **§3**: the graded completion `C = ⊕_d lim (O_n)_d`. -/
def C : Subring (∀ n, S.O n) where
  carrier := gL S.𝒜 S.πa
  add_mem' := (gL S.𝒜 S.πa).add_mem
  zero_mem' := (gL S.𝒜 S.πa).zero_mem
  neg_mem' := (gL S.𝒜 S.πa).neg_mem
  one_mem' := glim_le_gL _ _ _ S.glim_one
  mul_mem' {a b} ha hb := by
    induction ha using AddSubgroup.iSup_induction' with
    | hp i x hx =>
      induction hb using AddSubgroup.iSup_induction' with
      | hp j y hy => exact glim_le_gL _ _ _ (S.glim_mul hx hy)
      | h1 => simpa using (gL S.𝒜 S.πa).zero_mem
      | hadd y z _ _ hy hz => rw [mul_add]; exact (gL S.𝒜 S.πa).add_mem hy hz
    | h1 => simpa using (gL S.𝒜 S.πa).zero_mem
    | hadd y z _ _ hy hz => rw [add_mul]; exact (gL S.𝒜 S.πa).add_mem hy hz

/-- Inclusion of `C` in the product. -/
def Cι : S.C →+ ∀ n, S.O n := S.C.subtype.toAddMonoidHom

/-- The grading `C_d = lim (O_n)_d`. -/
abbrev 𝒞 (d : M) : AddSubgroup S.C := tgrade S.𝒜 S.πa S.Cι d

lemma πa_mem (n : ℕ) (d : M) (y : S.O (n + 1)) (h : y ∈ S.𝒜 (n + 1) d) : S.πa n y ∈ S.𝒜 n d :=
  S.π_mem n d y h

noncomputable instance : Decomposition S.𝒞 :=
  (tgrade_internal (ℳ := S.𝒜) (p := S.πa) S.Cι Subtype.val_injective
    (fun u hu => ⟨⟨u, hu⟩, rfl⟩) (fun t => t.2)).chooseDecomposition

instance : SetLike.GradedMonoid S.𝒞 where
  one_mem := S.glim_one
  mul_mem _ _ _ _ hu hv := S.glim_mul hu hv

noncomputable instance : GradedRing S.𝒞 where

/-- Evaluation `C → O_n`. -/
def ev (n : ℕ) : S.C →+* S.O n := (Pi.evalRingHom S.O n).comp S.C.subtype

lemma π_ev (n : ℕ) (u : S.C) : S.π n (S.ev (n + 1) u) = S.ev n u :=
  gL_compat S.𝒜 S.πa u.2 n

lemma ev_mem {n : ℕ} {d : M} {u : S.C} (hu : u ∈ S.𝒞 d) : S.ev n u ∈ S.𝒜 n d := hu.2 n

lemma ev_comp (n : ℕ) (e : M) (u : S.C) :
    S.ev n (comp S.𝒞 e u) = comp (S.𝒜 n) e (S.ev n u) :=
  lvl_comp (ℳ := S.𝒜) (p := S.πa) S.Cι S.πa_mem e u n

lemma ext_ev {u v : S.C} (h : ∀ n, S.ev n u = S.ev n v) : u = v :=
  Subtype.ext (funext h)

/-- `C_d → (O_n)_d` is onto. -/
lemma exists_ev_mem (n : ℕ) {d : M} {x : S.O n} (hx : x ∈ S.𝒜 n d) :
    ∃ u ∈ S.𝒞 d, S.ev n u = x := by
  obtain ⟨u, hu, h⟩ := exists_lift (ℳ := S.𝒜) (p := S.πa) S.πa_mem S.π_surj n hx
  exact ⟨⟨u, glim_le_gL _ _ _ hu⟩, hu, h⟩

lemma ev_surj (n : ℕ) : Function.Surjective (S.ev n) := by
  intro x
  obtain ⟨s, hs⟩ := sum_comp (S.𝒜 n) x
  have : ∀ e, ∃ u ∈ S.𝒞 e, S.ev n u = comp (S.𝒜 n) e x :=
    fun e => S.exists_ev_mem n (comp_mem _ _ _)
  choose u _ hu using this
  exact ⟨∑ e ∈ s, u e, by rw [map_sum, Finset.sum_congr rfl fun e _ => hu e]; exact hs.symm⟩

/-- The ideal `m = ker(C → O_0)`. -/
def m : Ideal S.C := RingHom.ker (S.ev 0)

/-- The filtration `F^0 = C`, `F^{i+1} = ker (C → O_i)`. -/
def F : ℕ → Ideal S.C
  | 0 => ⊤
  | i + 1 => RingHom.ker (S.ev i)

lemma F_succ (i : ℕ) {u : S.C} : u ∈ S.F (i + 1) ↔ S.ev i u = 0 := RingHom.mem_ker

lemma F_anti : Antitone S.F := by
  refine antitone_nat_of_succ_le fun i => ?_
  cases i with
  | zero => exact le_top
  | succ i =>
    intro u hu
    rw [F_succ] at hu ⊢
    rw [← S.π_ev, hu, map_zero]

/-- Key comparison: `ev_m y = 0` iff `ev_n y ∈ I_n^{m+1}` for `m ≤ n`. -/
lemma ev_eq_zero_iff (m : ℕ) (k : ℕ) (y : S.C) :
    S.ev m y = 0 ↔ S.ev (m + k) y ∈ S.I (m + k) ^ (m + 1) := by
  induction k with
  | zero =>
    show _ ↔ S.ev m y ∈ _
    rw [S.I_nil]; simp
  | succ k ih =>
    rw [ih]
    show _ ↔ S.ev (m + k + 1) y ∈ S.I (m + k + 1) ^ (m + 1)
    constructor
    · intro h
      rw [← S.I_map, ← Ideal.map_pow] at h
      obtain ⟨w, hw, hwe⟩ := (Ideal.mem_map_iff_of_surjective _ (S.π_surj _)).1 h
      have hker : S.ev (m + k + 1) y - w ∈ RingHom.ker (S.π (m + k)) := by
        rw [RingHom.mem_ker, map_sub, hwe, S.π_ev, sub_self]
      rw [S.ker_π] at hker
      have hle : S.I (m + k + 1) ^ (m + k + 1) ≤ S.I (m + k + 1) ^ (m + 1) :=
        Ideal.pow_le_pow_right (by omega)
      have := Ideal.add_mem _ (hle hker) hw
      simpa using this
    · intro h
      rw [← S.π_ev, ← S.I_map, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ h

lemma mem_F_iff (i k : ℕ) (y : S.C) :
    y ∈ S.F (i + 1) ↔ S.ev (i + k) y ∈ S.I (i + k) ^ (i + 1) := by
  rw [F_succ]; exact S.ev_eq_zero_iff i k y

/-- `F` is multiplicative. -/
lemma F_mul (i j : ℕ) : S.F i * S.F j ≤ S.F (i + j) := by
  cases i with
  | zero => rw [zero_add]; exact Ideal.mul_le_right
  | succ i =>
    cases j with
    | zero => exact Ideal.mul_le_left
    | succ j =>
      rw [Ideal.mul_le]
      intro x hx y hy
      have hx' := (S.mem_F_iff i (j + 1) x).1 hx
      have hy' := (S.mem_F_iff j (i + 1) y).1 hy
      rw [show i + 1 + (j + 1) = (i + j + 1) + 1 by omega, F_succ, map_mul]
      have h1 : S.ev (i + j + 1) x ∈ S.I (i + j + 1) ^ (i + 1) := by
        have : i + (j + 1) = i + j + 1 := by omega
        rwa [this] at hx'
      have h2 : S.ev (i + j + 1) y ∈ S.I (i + j + 1) ^ (j + 1) := by
        have : j + (i + 1) = i + j + 1 := by omega
        rwa [this] at hy'
      have h3 := Ideal.mul_mem_mul h1 h2
      rw [← pow_add, show i + 1 + (j + 1) = (i + j + 1) + 1 by omega, S.I_nil] at h3
      simpa using h3

lemma F_sep (y : S.C) (h : ∀ i, y ∈ S.F i) : y = 0 :=
  S.ext_ev fun n => by rw [map_zero]; exact (S.F_succ n).1 (h (n + 1))

/-- `F` is complete on each `C_d`. -/
lemma F_compl (d : M) (z : ℕ → S.C) (hz : ∀ j, z j ∈ S.F j ∧ z j ∈ S.𝒞 d) :
    ∃ w ∈ S.𝒞 d, ∀ N, w - ∑ j ∈ Finset.range N, z j ∈ S.F N := by
  let u : ∀ n, S.O n := fun n => S.ev n (∑ j ∈ Finset.range (n + 1), z j)
  have hsum : ∀ N, ∑ j ∈ Finset.range N, z j ∈ S.𝒞 d :=
    fun N => (S.𝒞 d).sum_mem fun j _ => (hz j).2
  have hu : u ∈ glim S.𝒜 S.πa d := by
    refine ⟨fun n => ?_, fun n => S.ev_mem (hsum _)⟩
    show S.π n (S.ev (n + 1) _) = S.ev n _
    rw [S.π_ev, Finset.sum_range_succ, map_add, (S.F_succ n).1 (hz (n + 1)).1, add_zero]
  refine ⟨⟨u, glim_le_gL _ _ _ hu⟩, hu, fun N => ?_⟩
  cases N with
  | zero => trivial
  | succ N =>
    rw [F_succ, map_sub, sub_eq_zero]
    rfl

lemma F_comp {i : ℕ} {y : S.C} (hy : y ∈ S.F i) (e : M) : comp S.𝒞 e y ∈ S.F i := by
  cases i with
  | zero => trivial
  | succ i =>
    rw [F_succ] at hy ⊢
    rw [ev_comp, hy, comp_zero]

end ThickeningSystem

end AlgMag.ChartGraded

namespace AlgMag.ChartGraded

open DirectSum

namespace ThickeningSystem

variable {M : Type*} [AddCommGroup M] [DecidableEq M] (S : ThickeningSystem M)

/-- Admissible terms `a · x^α`, `a ∈ C_0`, of filtration level `i` and degree `d`. -/
def terms {ι : Type} [Fintype ι] (x : ι → S.C) (δ : ι → M) (lev : ι → ℕ) (i : ℕ) (d : M) :
    Set S.C :=
  {u | ∃ a ∈ S.𝒞 0, ∃ α, wt lev α = i ∧ wt δ α = d ∧ u = a * mono x α}

/-- Homogeneous lifts of generators of `gr_F C`: the first bullets of the proof of Lemma 3.2. -/
structure Gens where
  ι : Type
  [fin : Fintype ι]
  x : ι → S.C
  δ : ι → M
  lev : ι → ℕ
  hxd : ∀ i, x i ∈ S.𝒞 (δ i)
  hxm : ∀ i, x i ∈ S.m ^ lev i
  hgen : ∀ i d y, y ∈ S.F i → y ∈ S.𝒞 d →
    y ∈ AddSubgroup.closure (S.terms x δ lev i d) ⊔ (S.F (i + 1)).toAddSubgroup

attribute [instance] Gens.fin

lemma m_eq_F1 : S.m = S.F 1 := rfl

lemma m_pow_le_F (i : ℕ) : S.m ^ i ≤ S.F i := by
  induction i with
  | zero => simp [F]
  | succ i ih =>
    rw [pow_succ]
    exact (Ideal.mul_mono ih le_rfl).trans (S.F_mul i 1)

lemma mem_m_iff (n : ℕ) (y : S.C) : y ∈ S.m ↔ S.ev n y ∈ S.I n := by
  have h := S.ev_eq_zero_iff 0 n y
  have h2 : 0 + n = n := Nat.zero_add n
  rw [h2] at h
  simpa [m, RingHom.mem_ker] using h

lemma map_m (n : ℕ) : S.m.map (S.ev n) = S.I n := by
  ext z
  rw [Ideal.mem_map_iff_of_surjective _ (S.ev_surj n)]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (S.mem_m_iff n y).1 hy
  · intro hz
    obtain ⟨y, rfl⟩ := S.ev_surj n z
    exact ⟨y, (S.mem_m_iff n y).2 hz, rfl⟩

lemma F_le_m_pow_sup (i : ℕ) : S.F i ≤ S.m ^ i ⊔ S.F (i + 1) := by
  cases i with
  | zero => simp [F]
  | succ j =>
    intro y hy
    have h1 := (S.mem_F_iff j 1 y).1 hy
    rw [show j + 1 = j + 1 from rfl, ← S.map_m, ← Ideal.map_pow] at h1
    obtain ⟨z, hz, hze⟩ := (Ideal.mem_map_iff_of_surjective _ (S.ev_surj _)).1 h1
    refine Submodule.mem_sup.2 ⟨z, hz, y - z, ?_, by ring⟩
    rw [F_succ, map_sub, hze, sub_self]

lemma mono_mem_pow {ι : Type} [Fintype ι] (I : Ideal S.C) {x : ι → S.C} {lev : ι → ℕ}
    (hx : ∀ i, x i ∈ I ^ lev i) (α : ι → ℕ) : mono x α ∈ I ^ wt lev α := by
  classical
  show ∏ i, x i ^ α i ∈ I ^ ∑ i, α i • lev i
  have key : ∀ s : Finset ι, ∏ i ∈ s, x i ^ α i ∈ I ^ ∑ i ∈ s, α i • lev i := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, pow_add]
      refine Ideal.mul_mem_mul ?_ ih
      rw [smul_eq_mul, mul_comm, pow_mul]
      exact Ideal.pow_mem_pow (hx a) _
  exact key _

/-- Existence of generators (from `O_0` finite type over noetherian `k`, and `I_1` finite). -/
theorem exists_gens {k : Type*} [CommRing k] [Algebra k (S.O 0)]
    (halg : ∀ r : k, algebraMap k (S.O 0) r ∈ S.𝒜 0 0) [Algebra.FiniteType k (S.O 0)] :
    Nonempty S.Gens := by
  classical
  obtain ⟨n1, hb, δ1, hbd, hba⟩ := exists_homogeneous_gens (k := k) (S.𝒜 0)
  obtain ⟨s, hs⟩ := S.I_fg
  obtain ⟨n2, gb, δ2, hgd, hgc, hgP⟩ := exists_homogeneous_family (S.𝒜 1) s
  have hgI : ∀ j, gb j ∈ S.I 1 := by
    refine hgP (S.I 1).toAddSubgroup fun a ha e => ?_
    exact S.I_hom 1 e (by rw [← hs]; exact Ideal.subset_span ha)
  have hl1 : ∀ i, ∃ u ∈ S.𝒞 (δ1 i), S.ev 0 u = hb i := fun i => S.exists_ev_mem 0 (hbd i)
  have hl2 : ∀ j, ∃ u ∈ S.𝒞 (δ2 j), S.ev 1 u = gb j := fun j => S.exists_ev_mem 1 (hgd j)
  choose h hhd hhe using hl1
  choose g hgd' hge using hl2
  have hgm : ∀ j, g j ∈ S.m := fun j =>
    (S.mem_m_iff 1 (g j)).2 (by simpa [hge] using hgI j)
  let ι : Type := Fin n1 ⊕ Fin n2
  let x : ι → S.C := Sum.elim h g
  let δ : ι → M := Sum.elim δ1 δ2
  let lev : ι → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)
  have hxd : ∀ i, x i ∈ S.𝒞 (δ i) := by rintro (i | i); exacts [hhd i, hgd' i]
  have hxm : ∀ i, x i ∈ S.m ^ lev i := by
    rintro (i | i)
    · simp [lev]
    · simpa [lev, x] using hgm i
  have hxF : ∀ α, mono x α ∈ S.F (wt lev α) := fun α =>
    S.m_pow_le_F _ (S.mono_mem_pow S.m hxm α)
  refine ⟨⟨ι, x, δ, lev, hxd, hxm, ?_⟩⟩
  -- the additive approximation groups
  let U : ℕ → AddSubgroup S.C := fun i =>
    AddSubgroup.closure {u | ∃ a ∈ S.𝒞 0, ∃ α, wt lev α = i ∧ u = a * mono x α} ⊔
      (S.F (i + 1)).toAddSubgroup
  have hU0 : ∀ i (a u : S.C), a ∈ S.𝒞 0 → u ∈ U i → a * u ∈ U i := by
    intro i a u ha hu
    obtain ⟨p, hp, q, hq, rfl⟩ := AddSubgroup.mem_sup.1 hu
    clear hu
    rw [mul_add]
    refine (U i).add_mem ?_ (AddSubgroup.mem_sup_right ((S.F (i + 1)).mul_mem_left a hq))
    refine AddSubgroup.mem_sup_left ?_
    induction hp using AddSubgroup.closure_induction with
    | mem t ht =>
      obtain ⟨b, hb, α, hα, rfl⟩ := ht
      refine AddSubgroup.subset_closure ⟨a * b, ?_, α, hα, by ring⟩
      simpa using SetLike.GradedMul.mul_mem ha hb
    | zero => simp
    | add s t _ _ hs ht => rw [mul_add]; exact AddSubgroup.add_mem _ hs ht
    | neg s _ hs => rw [mul_neg]; exact AddSubgroup.neg_mem _ hs
  -- Claim 1
  have hmonoH : ∀ β : Fin n1 → ℕ, S.ev 0 (mono x (Sum.elim β 0)) = mono hb β := by
    intro β
    simp only [mono, map_prod, map_pow]
    erw [Fintype.prod_sum_type]
    simp [x, hhe]
  have hwt0 : ∀ β : Fin n1 → ℕ, wt lev (Sum.elim β 0) = 0 := by
    intro β
    show ∑ i, (Sum.elim β 0 : ι → ℕ) i • lev i = 0
    simp [Fintype.sum_sum_type, lev]
  have hw1 : ∀ i (c X : S.C), S.ev 0 c = 0 → X ∈ S.F i → c * X ∈ S.F (i + 1) := by
    intro i c X hc hX
    have := S.F_mul 1 i (Ideal.mul_mem_mul ((S.F_succ 0).2 hc) hX)
    rwa [add_comm] at this
  have claim1 : ∀ i α, wt lev α = i → ∀ t ∈ Submodule.span k (Set.range (mono hb)),
      ∀ c : S.C, S.ev 0 c = t → c * mono x α ∈ U i := by
    intro i α hα t ht
    have hXF : mono x α ∈ S.F i := hα ▸ hxF α
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨β, rfl⟩ := ht
      intro c hc
      have : c * mono x α = (c - mono x (Sum.elim β 0)) * mono x α +
          1 * mono x (Sum.elim β 0 + α) := by rw [mono_add]; ring
      rw [this]
      refine (U i).add_mem (AddSubgroup.mem_sup_right (hw1 i _ _ ?_ hXF))
        (AddSubgroup.mem_sup_left (AddSubgroup.subset_closure
          ⟨1, SetLike.GradedOne.one_mem, _, ?_, rfl⟩))
      · rw [map_sub, hc, hmonoH, sub_self]
      · rw [map_add, hwt0, zero_add, hα]
    | zero =>
      intro c hc
      exact AddSubgroup.mem_sup_right (hw1 i _ _ hc hXF)
    | add a b _ _ ha hb =>
      intro c hc
      obtain ⟨c1, hc1⟩ := S.ev_surj 0 a
      have : c = c1 + (c - c1) := by ring
      rw [this, add_mul]
      exact (U i).add_mem (ha c1 hc1) (hb _ (by rw [map_sub, hc, hc1]; ring))
    | smul r a _ ha =>
      intro c hc
      obtain ⟨ar, har, hare⟩ := S.exists_ev_mem 0 (halg r)
      obtain ⟨c1, hc1⟩ := S.ev_surj 0 a
      have : c * mono x α = ar * (c1 * mono x α) + (c - ar * c1) * mono x α := by ring
      rw [this]
      refine (U i).add_mem (hU0 _ _ _ har (ha c1 hc1)) (AddSubgroup.mem_sup_right ?_)
      refine hw1 i _ _ ?_ hXF
      rw [map_sub, map_mul, hc, hare, hc1, Algebra.smul_def, sub_self]
  have claim1' : ∀ i α, wt lev α = i → ∀ c : S.C, c * mono x α ∈ U i := fun i α hα c =>
    claim1 i α hα _ (mem_span_mono hba _) c rfl
  have hUC : ∀ i (c u : S.C), u ∈ U i → c * u ∈ U i := by
    intro i c u hu
    obtain ⟨p, hp, q, hq, rfl⟩ := AddSubgroup.mem_sup.1 hu
    clear hu
    rw [mul_add]
    refine (U i).add_mem ?_ (AddSubgroup.mem_sup_right ((S.F (i + 1)).mul_mem_left c hq))
    induction hp using AddSubgroup.closure_induction with
    | mem t ht =>
      obtain ⟨b, hb, α, hα, rfl⟩ := ht
      rw [← mul_assoc]
      exact claim1' i α hα _
    | zero => simp [(U i).zero_mem]
    | add s t _ _ hs ht => rw [mul_add]; exact (U i).add_mem hs ht
    | neg s _ hs => rw [mul_neg]; exact (U i).neg_mem hs
  -- the ideals J_i
  let J : ℕ → Ideal S.C := fun i => Ideal.span {u | ∃ α, wt lev α = i ∧ u = mono x α}
  have hJU : ∀ i, ∀ u ∈ J i, u ∈ U i := by
    intro i u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨α, hα, rfl⟩ := hu
      simpa using claim1' i α hα 1
    | zero => exact (U i).zero_mem
    | add a b _ _ ha hb => exact (U i).add_mem ha hb
    | smul c a _ ha => exact hUC i c a ha
  have hJF : ∀ i, J i ≤ S.F i := by
    intro i
    refine Ideal.span_le.2 ?_
    rintro _ ⟨α, hα, rfl⟩
    exact hα ▸ hxF α
  have hJmul : ∀ i j, J i * J j ≤ J (i + j) := by
    intro i j
    rw [Ideal.span_mul_span]
    refine Ideal.span_le.2 ?_
    rintro _ ⟨_, ⟨α, hα, rfl⟩, _, ⟨β, hβ, rfl⟩, rfl⟩
    exact Ideal.subset_span ⟨α + β, by rw [map_add, hα, hβ], (mono_add x α β).symm⟩
  have hm1 : S.m ≤ J 1 ⊔ S.F 2 := by
    intro y hy
    have h1 : S.ev 1 y ∈ S.I 1 := (S.mem_m_iff 1 y).1 hy
    have hspan : S.I 1 ≤ (J 1).map (S.ev 1) := by
      rw [← hs, Ideal.span_le]
      intro a ha
      have hcl := hgc a ha
      have key : ∀ a ∈ AddSubgroup.closure (Set.range gb), a ∈ (J 1).map (S.ev 1) := by
        intro a ha
        induction ha using AddSubgroup.closure_induction with
        | mem a ha =>
          obtain ⟨j, rfl⟩ := ha
          rw [← hge j]
          refine Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨Pi.single (Sum.inr j) 1, ?_, ?_⟩)
          · rw [wt_single]; rfl
          · rw [mono_single]; rfl
        | zero => exact Ideal.zero_mem _
        | add a b _ _ ha hb => exact Ideal.add_mem _ ha hb
        | neg a _ ha => exact (Ideal.neg_mem_iff _).2 ha
      exact key a hcl
    obtain ⟨z, hz, hze⟩ := (Ideal.mem_map_iff_of_surjective _ (S.ev_surj _)).1 (hspan h1)
    refine Submodule.mem_sup.2 ⟨z, hz, y - z, ?_, by ring⟩
    exact (S.F_succ 1).2 (by rw [map_sub, hze, sub_self])
  have hmpow : ∀ i, S.m ^ i ≤ J i ⊔ S.F (i + 1) := by
    intro i
    induction i with
    | zero =>
      have h0 : J 0 = ⊤ := (Ideal.eq_top_iff_one _).2
        (Ideal.subset_span ⟨0, map_zero _, (mono_zero x).symm⟩)
      rw [h0, pow_zero, Ideal.one_eq_top]
      exact le_sup_left
    | succ i ih =>
      rw [pow_succ]
      refine (Ideal.mul_mono ih hm1).trans ?_
      rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
      refine sup_le (sup_le (le_sup_of_le_left (hJmul i 1)) ?_) (sup_le ?_ ?_)
      · exact le_sup_of_le_right
          ((Ideal.mul_mono (hJF i) le_rfl).trans (S.F_mul i 2))
      · exact le_sup_of_le_right
          ((Ideal.mul_mono le_rfl (hJF 1)).trans (S.F_mul (i + 1) 1))
      · exact le_sup_of_le_right
          ((S.F_mul (i + 1) 2).trans (S.F_anti (by omega)))
  have hFU : ∀ i, ∀ y ∈ S.F i, y ∈ U i := by
    intro i y hy
    have h1 := S.F_le_m_pow_sup i hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 h1
    obtain ⟨c, hc, d, hd, rfl⟩ := Submodule.mem_sup.1 (hmpow i ha)
    exact (U i).add_mem ((U i).add_mem (hJU i c hc) (AddSubgroup.mem_sup_right hd))
      (AddSubgroup.mem_sup_right hb)
  -- homogeneous projection
  intro i d y hy hyd
  obtain ⟨p, hp, q, hq, hpq⟩ := AddSubgroup.mem_sup.1 (hFU i y hy)
  have hy' : y = comp S.𝒞 d p + comp S.𝒞 d q := by
    rw [← comp_add, hpq, comp_of_mem _ hyd]
  rw [hy']
  clear hy' hpq
  refine AddSubgroup.add_mem _ (AddSubgroup.mem_sup_left ?_)
    (AddSubgroup.mem_sup_right (S.F_comp hq d))
  induction hp using AddSubgroup.closure_induction with
  | mem t ht =>
    obtain ⟨a, ha, α, hα, rfl⟩ := ht
    rw [comp_mul_of_mem_zero S.𝒞 ha]
    by_cases hd : wt δ α = d
    · rw [comp_of_mem _ (hd ▸ mono_mem S.𝒞 hxd α)]
      exact AddSubgroup.subset_closure ⟨a, ha, α, hα, hd, rfl⟩
    · rw [comp_of_mem_ne _ (mono_mem S.𝒞 hxd α) hd, mul_zero]
      exact AddSubgroup.zero_mem _
  | zero => rw [comp_zero]; exact AddSubgroup.zero_mem _
  | add s t _ _ hs ht => rw [comp_add]; exact AddSubgroup.add_mem _ hs ht
  | neg s _ hs =>
    have : comp S.𝒞 d (-s) = - comp S.𝒞 d s := by
      have := comp_sub S.𝒞 d 0 s
      simpa [comp_zero] using this
    rw [this]; exact AddSubgroup.neg_mem _ hs

end ThickeningSystem

end AlgMag.ChartGraded

namespace AlgMag.ChartGraded

open DirectSum Polynomial

section Rees

variable {R : Type*} [CommRing R] (F : ℕ → Ideal R) (hF : IsCompleteFiltration F)

lemma reesT_congr {i j : ℕ} {y z : R} (hij : i = j) (hyz : y = z) (h1 : y ∈ F i) (h2 : z ∈ F j) :
    reesT F hF i y h1 = reesT F hF j z h2 := by
  subst hij; subst hyz; rfl

lemma reesT_mul {i j : ℕ} {y z : R} (h1 : y ∈ F i) (h2 : z ∈ F j) (h3 : y * z ∈ F (i + j)) :
    reesT F hF i y h1 * reesT F hF j z h2 = reesT F hF (i + j) (y * z) h3 :=
  Subtype.ext (by simp [reesT, monomial_mul_monomial])

lemma reesT_add {i : ℕ} {y z : R} (h1 : y ∈ F i) (h2 : z ∈ F i) (h3 : y + z ∈ F i) :
    reesT F hF i (y + z) h3 = reesT F hF i y h1 + reesT F hF i z h2 :=
  Subtype.ext (by simp [reesT])

lemma reesT_neg {i : ℕ} {y : R} (h1 : y ∈ F i) (h3 : -y ∈ F i) :
    reesT F hF i (-y) h3 = - reesT F hF i y h1 :=
  Subtype.ext (by simp [reesT])

lemma reesT_ker {i : ℕ} {y : R} (h1 : y ∈ F i) (h2 : y ∈ F (i + 1)) :
    reesT F hF i y h1 ∈ reesKer F hF := by
  intro j
  show (monomial i y).coeff j ∈ _
  rw [coeff_monomial]
  split_ifs with h
  · exact h ▸ h2
  · exact Ideal.zero_mem _

/-- The Rees ring is spanned by the `y T^i`. -/
lemma rees_sum (P : rees F hF) :
    ∃ s : Finset ℕ, P = ∑ i ∈ s, reesT F hF i ((P : R[X]).coeff i) (P.2 i) := by
  refine ⟨Finset.range ((P : R[X]).natDegree + 1), Subtype.ext ?_⟩
  rw [AddSubmonoidClass.coe_finset_sum]
  exact (P : R[X]).as_sum_range

end Rees

namespace ThickeningSystem

variable {M : Type*} [AddCommGroup M] [DecidableEq M] (S : ThickeningSystem M)

/-- `C_0` as a subring. -/
def C0 : Subring S.C where
  carrier := S.𝒞 0
  mul_mem' {a b} ha hb := by simpa using SetLike.GradedMul.mul_mem ha hb
  one_mem' := SetLike.GradedOne.one_mem
  add_mem' := (S.𝒞 0).add_mem
  zero_mem' := (S.𝒞 0).zero_mem
  neg_mem' := (S.𝒞 0).neg_mem

/-- The induced filtration on `C_0`. -/
def G (j : ℕ) : Ideal S.C0 := (S.F j).comap S.C0.subtype

lemma isCompleteFiltration_G : IsCompleteFiltration S.G where
  zero := by simp [G, F]
  anti i j hij y hy := S.F_anti hij hy
  mul i j := by
    rw [Ideal.mul_le]
    intro a ha b hb
    exact S.F_mul i j (Ideal.mul_mem_mul ha hb)
  sep y hy := Subtype.ext (S.F_sep y.1 hy)
  compl z hz := by
    obtain ⟨w, hw, h⟩ := S.F_compl 0 (fun j => (z j).1) (fun j => ⟨hz j, (z j).2⟩)
    refine ⟨⟨w, hw⟩, fun N => ?_⟩
    have := h N
    show ((⟨w, hw⟩ - ∑ j ∈ Finset.range N, z j : S.C0) : S.C) ∈ S.F N
    simpa using this

variable {S}

lemma mono_mem_F (g : S.Gens) (α : g.ι → ℕ) : mono g.x α ∈ S.F (wt g.lev α) :=
  S.m_pow_le_F _ (S.mono_mem_pow S.m g.hxm α)

/-- The monomial expansion behind Lemma 3.2: for each `i₀, d` there are finitely many monomials of
degree `d` and level `≥ i₀` generating `F^{i₀} ∩ C_d` over `C_0`. -/
theorem exists_mono_span (g : S.Gens) (i₀ : ℕ) (d : M) :
    ∃ T : Finset (g.ι → ℕ), (∀ β ∈ T, wt g.δ β = d ∧ i₀ ≤ wt g.lev β) ∧
      ∀ y, y ∈ S.F i₀ → y ∈ S.𝒞 d → ∃ r : T → S.C0, y = ∑ β, (r β : S.C) * mono g.x β := by
  classical
  obtain ⟨T, hTS, hT⟩ := exists_finite_below {α : g.ι → ℕ | wt g.δ α = d ∧ i₀ ≤ wt g.lev α}
  refine ⟨T, fun β hβ => hTS hβ, fun y hy hyd => ?_⟩
  have hsplit : ∀ (β α : g.ι → ℕ), β ≤ α → α = β + (α - β) := by
    intro β α h; funext i; have h9 : β i ≤ α i := h i
    simp only [Pi.add_apply, Pi.sub_apply]; omega
  obtain ⟨r, _, hr⟩ := approx (R := S.C0) (V := S.C) (W := T) S.G
    (fun j => (S.F (j + i₀)).toAddSubgroup) (S.𝒞 d) (fun _ => ⊤) (fun β => mono g.x β)
    (fun β => wt g.lev β - i₀) S.isCompleteFiltration_G.zero S.isCompleteFiltration_G.anti
    (fun i j hij u hu => S.F_anti (by omega : i + i₀ ≤ j + i₀) hu)
    (fun u hu => S.F_sep u fun i => S.F_anti (by omega : i ≤ i + i₀) (hu i))
    (fun β i a ha => by
      have h1 := S.F_mul _ _ (Ideal.mul_mem_mul ha (mono_mem_F g β.1))
      have h2 := (hTS β.2).2
      show (a : S.C) * mono g.x β ∈ S.F (i + (wt g.lev β - i₀) + i₀)
      rwa [show i + (wt g.lev β - i₀) + i₀ = i + wt g.lev β by omega])
    (fun β z hz => by
      obtain ⟨u, hu⟩ := S.isCompleteFiltration_G.compl z fun j => (hz j).1
      exact ⟨u, trivial, hu⟩)
    (fun β a _ => by
      have h1 := mono_mem S.𝒞 g.hxd β.1
      rw [(hTS β.2).1] at h1
      have := SetLike.GradedMul.mul_mem a.2 h1
      rw [zero_add] at this
      exact this)
    (fun i u hu hud => by
      obtain ⟨p, hp, q, hq, hpq⟩ := AddSubgroup.mem_sup.1 (g.hgen _ d u hu hud)
      have key : ∀ p ∈ AddSubgroup.closure (S.terms g.x g.δ g.lev (i + i₀) d), ∃ r : T → S.C0,
          (∀ β, r β ∈ S.G (i - (wt g.lev β.1 - i₀))) ∧
          p = ∑ β : T, r β • mono g.x β := by
        intro p hp
        induction hp using AddSubgroup.closure_induction with
        | mem t ht =>
          obtain ⟨a, ha, α, hα, hαd, rfl⟩ := ht
          obtain ⟨β, hβ, hle⟩ := hT α ⟨hαd, by omega⟩
          have hs := hsplit β α hle
          have hd0 : wt g.δ (α - β) = 0 := by
            have h1 := congrArg (wt g.δ) hs
            rw [map_add, hαd, (hTS hβ).1] at h1
            simpa using h1.symm
          have hl0 : wt g.lev β + wt g.lev (α - β) = i + i₀ := by
            rw [← map_add, ← hs, hα]
          have hmem : a * mono g.x (α - β) ∈ S.C0 := by
            have := SetLike.GradedMul.mul_mem ha (mono_mem S.𝒞 g.hxd (α - β))
            rwa [hd0, add_zero] at this
          refine ⟨fun w => if w.1 = β then ⟨_, hmem⟩ else 0, fun w => ?_, ?_⟩
          · dsimp only
            split_ifs with hw
            · rw [hw]
              show a * mono g.x (α - β) ∈ S.F _
              refine Ideal.mul_mem_left _ _ (S.F_anti ?_ (mono_mem_F g (α - β)))
              have := (hTS hβ).2
              omega
            · exact Ideal.zero_mem _
          · rw [Finset.sum_eq_single (⟨β, hβ⟩ : T)]
            · simp only [if_true]
              show _ = a * mono g.x (α - β) * mono g.x β
              conv_lhs => rw [hs, mono_add]
              ring
            · intro w _ hw
              dsimp only
              rw [if_neg (fun h => hw (Subtype.ext h)), zero_smul]
            · exact fun h => absurd (Finset.mem_univ _) h
        | zero =>
          exact ⟨0, fun β => Ideal.zero_mem _, by simp⟩
        | add s t _ _ hs ht =>
          obtain ⟨r1, hr1, rfl⟩ := hs
          obtain ⟨r2, hr2, rfl⟩ := ht
          exact ⟨r1 + r2, fun β => Ideal.add_mem _ (hr1 β) (hr2 β), by
            simp [add_smul, Finset.sum_add_distrib]⟩
        | neg s _ hs =>
          obtain ⟨r1, hr1, rfl⟩ := hs
          exact ⟨-r1, fun β => (Ideal.neg_mem_iff _).2 (hr1 β), by simp [neg_smul]⟩
      obtain ⟨r, hr, hre⟩ := key p hp
      refine ⟨r, fun β => ⟨hr β, trivial⟩, ?_⟩
      rw [← hre, ← hpq, add_sub_cancel_left]
      show q ∈ S.F (i + 1 + i₀)
      rwa [show i + 1 + i₀ = i + i₀ + 1 by omega])
    0 (y := y) (by simpa using hy) hyd
  exact ⟨r, hr⟩

/-- `F^i = m^i` (last bullet of the proof of Lemma 3.2). -/
theorem F_eq_m_pow (g : S.Gens) (i : ℕ) : S.F i = S.m ^ i := by
  refine le_antisymm (fun y hy => ?_) (S.m_pow_le_F i)
  refine mem_of_comp_mem S.𝒞 (S.m ^ i).toAddSubgroup fun e => ?_
  obtain ⟨T, hT, h⟩ := exists_mono_span g i e
  obtain ⟨r, hr⟩ := h _ (S.F_comp hy e) (comp_mem _ _ _)
  show comp S.𝒞 e y ∈ S.m ^ i
  rw [hr]
  refine Ideal.sum_mem _ fun β _ => Ideal.mul_mem_left _ _ ?_
  exact Ideal.pow_le_pow_right (hT β.1 β.2).2 (S.mono_mem_pow S.m g.hxm β.1)

set_option maxHeartbeats 3000000 in
/-- Generators of `gr C_0`, hence `C_0` noetherian. -/
theorem isNoetherianRing_C0 (g : S.Gens) [hA : IsNoetherianRing (S.C0 ⧸ S.G 1)] :
    IsNoetherianRing S.C0 := by
  classical
  let hF := S.isCompleteFiltration_G
  obtain ⟨A, hA0, hA'⟩ := exists_kernel_gens g.δ
  have hmA : ∀ a : A, mono g.x a.1 ∈ S.C0 := fun a => by
    have := mono_mem S.𝒞 g.hxd a.1
    rwa [hA0 a.1 a.2] at this
  let wA : A → S.C0 := fun a => ⟨_, hmA a⟩
  have hwA : ∀ a : A, wA a ∈ S.G (wt g.lev a.1) := fun a => mono_mem_F g a.1
  -- constants
  let cC : S.C0 →+* rees S.G hF :=
    (Polynomial.C (R := S.C0)).codRestrict (rees S.G hF) (fun c i => by
      rw [coeff_C]
      split_ifs with h
      · subst h; rw [hF.zero]; trivial
      · exact Ideal.zero_mem _)
  let ψ : S.C0 →+* grRing S.G hF := (Ideal.Quotient.mk _).comp cC
  have hψ : ∀ c ∈ S.G 1, ψ c = 0 := by
    intro c hc
    refine Ideal.Quotient.eq_zero_iff_mem.2 fun i => ?_
    show (Polynomial.C c).coeff i ∈ _
    rw [coeff_C]
    split_ifs with h
    · subst h; exact hc
    · exact Ideal.zero_mem _
  let ψb : (S.C0 ⧸ S.G 1) →+* grRing S.G hF := Ideal.Quotient.lift _ ψ hψ
  let φ : MvPolynomial A (S.C0 ⧸ S.G 1) →+* grRing S.G hF :=
    MvPolynomial.eval₂Hom ψb fun a => Ideal.Quotient.mk _ (reesT S.G hF _ _ (hwA a))
  have hψmem : ∀ c : S.C0, ψ c ∈ φ.range := fun c =>
    ⟨MvPolynomial.C (Ideal.Quotient.mk _ c), by simp [φ, ψb]⟩
  -- monomials of degree zero are in the range
  have key0 : ∀ α ∈ AddSubmonoid.closure (A : Set (g.ι → ℕ)), ∀ (h : mono g.x α ∈ S.C0)
      (h2 : (⟨_, h⟩ : S.C0) ∈ S.G (wt g.lev α)),
      Ideal.Quotient.mk (reesKer S.G hF) (reesT S.G hF _ ⟨_, h⟩ h2) ∈ φ.range := by
    intro α hα
    induction hα using AddSubmonoid.closure_induction with
    | mem a ha =>
      intro h h2
      exact ⟨MvPolynomial.X ⟨a, ha⟩, by simp [φ, wA]⟩
    | zero =>
      intro h h2
      have : reesT S.G hF (wt g.lev 0) ⟨mono g.x 0, h⟩ h2 = 1 :=
        Subtype.ext (by
          show monomial _ _ = 1
          rw [map_zero]
          have : (⟨mono g.x 0, h⟩ : S.C0) = 1 := Subtype.ext (mono_zero g.x)
          rw [this]; rfl)
      rw [this, map_one]
      exact one_mem _
    | add a b ha' hb' ha hb =>
      intro h h2
      have hd : ∀ c ∈ AddSubmonoid.closure (A : Set (g.ι → ℕ)), mono g.x c ∈ S.C0 := by
        intro c hc
        have h0 : wt g.δ c = 0 := by
          induction hc using AddSubmonoid.closure_induction with
          | mem c hc => exact hA0 c hc
          | zero => simp
          | add c d _ _ hc hd => rw [map_add, hc, hd, add_zero]
        have := mono_mem S.𝒞 g.hxd c
        rwa [h0] at this
      have h1 := ha (hd a ha') (mono_mem_F g a)
      have h3 := hb (hd b hb') (mono_mem_F g b)
      have h4 := mul_mem h1 h3
      have ga : (⟨_, hd a ha'⟩ : S.C0) ∈ S.G (wt g.lev a) := mono_mem_F g a
      have gb : (⟨_, hd b hb'⟩ : S.C0) ∈ S.G (wt g.lev b) := mono_mem_F g b
      rw [← map_mul, reesT_mul S.G hF ga gb (hF.mul _ _ (Ideal.mul_mem_mul ga gb))] at h4
      convert h4 using 2
      exact reesT_congr S.G hF (map_add _ _ _)
        (Subtype.ext (mono_add g.x a b)) _ _
  -- every `y T^i` is in the range
  have key1 : ∀ i (p : S.C), p ∈ AddSubgroup.closure (S.terms g.x g.δ g.lev i 0) →
      ∃ (h : p ∈ S.C0) (h2 : (⟨p, h⟩ : S.C0) ∈ S.G i),
        Ideal.Quotient.mk (reesKer S.G hF) (reesT S.G hF i ⟨p, h⟩ h2) ∈ φ.range := by
    intro i p hp
    induction hp using AddSubgroup.closure_induction with
    | mem t ht =>
      obtain ⟨a, ha, α, hα, hαd, rfl⟩ := ht
      have h0 := hA' α hαd
      have hm : mono g.x α ∈ S.C0 := by
        have := mono_mem S.𝒞 g.hxd α
        rwa [hαd] at this
      have hmF : (⟨_, hm⟩ : S.C0) ∈ S.G (wt g.lev α) := mono_mem_F g α
      have hP : a * mono g.x α ∈ S.C0 := S.C0.mul_mem ha hm
      have hPF : (⟨_, hP⟩ : S.C0) ∈ S.G i :=
        Ideal.mul_mem_left (S.F i) a (hα ▸ mono_mem_F g α)
      refine ⟨hP, hPF, ?_⟩
      have ha0 : a ∈ S.C0 := ha
      have h3 := mul_mem (hψmem ⟨a, ha0⟩) (key0 α h0 hm hmF)
      have e : reesT S.G hF i ⟨_, hP⟩ hPF =
          cC ⟨a, ha0⟩ * reesT S.G hF (wt g.lev α) ⟨_, hm⟩ hmF := by
        subst hα
        refine Subtype.ext ?_
        show monomial _ _ = Polynomial.C _ * monomial _ _
        rw [C_mul_monomial]
        rfl
      rw [e, map_mul]
      exact h3
    | zero =>
      have z1 : (⟨0, S.C0.zero_mem⟩ : S.C0) ∈ S.G i := Ideal.zero_mem (S.F i)
      have z2 : (⟨0, S.C0.zero_mem⟩ : S.C0) ∈ S.G (i + 1) := Ideal.zero_mem (S.F (i + 1))
      refine ⟨S.C0.zero_mem, z1, ?_⟩
      rw [Ideal.Quotient.eq_zero_iff_mem.2 (reesT_ker S.G hF z1 z2)]
      exact zero_mem _
    | add s t _ _ hs ht =>
      obtain ⟨h1, h2, h3⟩ := hs
      obtain ⟨h4, h5, h6⟩ := ht
      have h7 : (⟨s + t, S.C0.add_mem h1 h4⟩ : S.C0) ∈ S.G i := Ideal.add_mem (S.F i) h2 h5
      refine ⟨S.C0.add_mem h1 h4, h7, ?_⟩
      have e : reesT S.G hF i ⟨s + t, S.C0.add_mem h1 h4⟩ h7 =
          reesT S.G hF i ⟨s, h1⟩ h2 + reesT S.G hF i ⟨t, h4⟩ h5 := by
        refine Subtype.ext ?_
        show monomial _ _ = monomial _ _ + monomial _ _
        rw [← map_add]
        rfl
      rw [e, map_add]
      exact add_mem h3 h6
    | neg s _ hs =>
      obtain ⟨h1, h2, h3⟩ := hs
      have h7 : (⟨-s, S.C0.neg_mem h1⟩ : S.C0) ∈ S.G i := (Ideal.neg_mem_iff (S.F i)).2 h2
      refine ⟨S.C0.neg_mem h1, h7, ?_⟩
      have e : reesT S.G hF i ⟨-s, S.C0.neg_mem h1⟩ h7 = - reesT S.G hF i ⟨s, h1⟩ h2 := by
        refine Subtype.ext ?_
        show monomial _ _ = - monomial _ _
        rw [← map_neg]
        rfl
      rw [e, map_neg]
      exact neg_mem h3
  have key2 : ∀ i (y : S.C0) (hy : y ∈ S.G i),
      Ideal.Quotient.mk (reesKer S.G hF) (reesT S.G hF i y hy) ∈ φ.range := by
    intro i y hy
    obtain ⟨p, hp, q, hq, hpq⟩ := AddSubgroup.mem_sup.1 (g.hgen i 0 y.1 hy y.2)
    obtain ⟨h1, h2, h3⟩ := key1 i p hp
    have hq0 : q ∈ S.C0 := by
      have : q = y.1 - p := by rw [← hpq]; ring
      rw [this]; exact S.C0.sub_mem y.2 h1
    have hqF : (⟨q, hq0⟩ : S.C0) ∈ S.G i := S.F_anti (Nat.le_succ i) hq
    have hysum : y = ⟨p, h1⟩ + ⟨q, hq0⟩ := Subtype.ext hpq.symm
    have hk : reesT S.G hF i y hy = reesT S.G hF i ⟨p, h1⟩ h2 + reesT S.G hF i ⟨q, hq0⟩ hqF := by
      rw [← reesT_add S.G hF h2 hqF (Ideal.add_mem _ h2 hqF)]
      exact reesT_congr S.G hF rfl hysum _ _
    rw [hk, map_add, Ideal.Quotient.eq_zero_iff_mem.2 (reesT_ker S.G hF hqF hq), add_zero]
    exact h3
  have hsurj : Function.Surjective φ := by
    intro t
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective t
    obtain ⟨s, hs⟩ := rees_sum S.G hF P
    rw [hs, map_sum]
    exact (sum_mem fun i _ => key2 i _ _ : _ ∈ φ.range)
  haveI : IsNoetherianRing (grRing S.G hF) := isNoetherianRing_of_surjective _ _ φ hsurj
  exact isNoetherianRing_of_gr S.G hF

end ThickeningSystem

end AlgMag.ChartGraded

namespace AlgMag.ChartGraded

open DirectSum

/-- A **complete pair** (Conventions of the note): `C` noetherian `M`-graded, `m` homogeneous, and
`C_d → lim (C/m^n)_d` bijective for all `d`. Since `m` is homogeneous, `(C/m^n)_d = C_d/(m^n ∩ C_d)`,
so surjectivity is `exists_lim` and injectivity is `sep`. -/
structure IsCompletePair {M C : Type*} [AddCommGroup M] [DecidableEq M] [CommRing C]
    (𝒞 : M → AddSubgroup C) [GradedRing 𝒞] (m : Ideal C) : Prop where
  noeth : IsNoetherianRing C
  hom : m.IsHomogeneous 𝒞
  exists_lim : ∀ d (y : ℕ → C), (∀ n, y n ∈ 𝒞 d) → (∀ n, y (n + 1) - y n ∈ m ^ n) →
    ∃ c ∈ 𝒞 d, ∀ n, c - y n ∈ m ^ n
  sep : ∀ d, ∀ c ∈ 𝒞 d, (∀ n, c ∈ m ^ n) → c = 0

namespace ThickeningSystem

variable {M : Type*} [AddCommGroup M] [DecidableEq M] (S : ThickeningSystem M)

/-- **Lemma 3.2.** `C` is noetherian, `(C,m)` is a complete pair, `C/m^{n+1} = O_n` as graded rings,
and `C_0/m_0 = (O_0)_0` (which is `k` when `O_0 = k[Z_0]`). -/
theorem lemma_3_2 {k : Type*} [CommRing k] [IsNoetherianRing k] [Algebra k (S.O 0)]
    (halg : ∀ r : k, algebraMap k (S.O 0) r ∈ S.𝒜 0 0) [Algebra.FiniteType k (S.O 0)] :
    IsCompletePair S.𝒞 S.m ∧
    (∀ n, RingHom.ker (S.ev n) = S.m ^ (n + 1) ∧ Function.Surjective (S.ev n) ∧
      ∀ d, ∀ x ∈ S.𝒜 n d, ∃ u ∈ S.𝒞 d, S.ev n u = x) ∧
    (∀ x ∈ S.𝒜 0 0, ∃ u ∈ S.𝒞 0, S.ev 0 u = x) ∧
    (∀ u ∈ S.𝒞 0, S.ev 0 u ∈ S.𝒜 0 0 ∧ (S.ev 0 u = 0 ↔ u ∈ S.m)) := by
  classical
  obtain ⟨g⟩ := S.exists_gens halg
  have hFm := F_eq_m_pow (S := S) g
  -- `C_0 / G 1` noetherian
  have hdz := isNoetherianRing_degZero (k := k) (S.𝒜 0) halg
  let ρ : S.C0 →+* degZero (S.𝒜 0) halg :=
    ((S.ev 0).comp S.C0.subtype).codRestrict (degZero (S.𝒜 0) halg).toSubring
      (fun u => S.ev_mem u.2)
  have hρs : Function.Surjective ρ := by
    rintro ⟨x, hx⟩
    obtain ⟨u, hu, he⟩ := S.exists_ev_mem 0 (d := 0) hx
    exact ⟨⟨u, hu⟩, Subtype.ext he⟩
  have hρk : S.G 1 = RingHom.ker ρ := by
    ext u
    rw [RingHom.mem_ker]
    constructor
    · intro h; exact Subtype.ext h
    · intro h; exact congrArg Subtype.val h
  have hq : IsNoetherianRing (S.C0 ⧸ S.G 1) := by
    rw [hρk]
    exact isNoetherianRing_of_ringEquiv _ (RingHom.quotientKerEquivOfSurjective hρs).symm
  have h0 : IsNoetherianRing S.C0 := isNoetherianRing_C0 g
  -- `C` finite type over `C_0`
  have hft : Algebra.FiniteType S.C0 S.C := by
    refine ⟨⟨Finset.univ.image g.x, ?_⟩⟩
    rw [eq_top_iff]
    intro y _
    obtain ⟨s, hs⟩ := sum_comp S.𝒞 y
    rw [hs]
    refine Subalgebra.sum_mem _ fun e _ => ?_
    obtain ⟨T, _, h⟩ := exists_mono_span g 0 e
    obtain ⟨r, hr⟩ := h _ (by simp [F]) (comp_mem _ _ _)
    rw [hr]
    refine Subalgebra.sum_mem _ fun β _ => ?_
    have hm : mono g.x β.1 ∈ Algebra.adjoin S.C0 ((Finset.univ.image g.x : Finset S.C) : Set S.C) :=
      Subalgebra.prod_mem _ fun i _ => Subalgebra.pow_mem _
        (Algebra.subset_adjoin (by simp)) _
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ (r β)) hm
  have hC : IsNoetherianRing S.C := Algebra.FiniteType.isNoetherianRing S.C0 S.C
  refine ⟨⟨hC, fun e r hr => S.F_comp (i := 1) hr e, ?_, ?_⟩, fun n => ⟨?_, S.ev_surj n,
    fun d x hx => S.exists_ev_mem n hx⟩, fun x hx => S.exists_ev_mem 0 hx,
    fun u hu => ⟨S.ev_mem hu, by rw [m, RingHom.mem_ker]⟩⟩
  · intro d y hy hyd
    obtain ⟨w, hw, hN⟩ := S.F_compl d (fun j => y (j + 1) - y j)
      (fun j => ⟨by rw [hFm]; exact hyd j, (S.𝒞 d).sub_mem (hy _) (hy _)⟩)
    refine ⟨w + y 0, (S.𝒞 d).add_mem hw (hy 0), fun n => ?_⟩
    have := hN n
    rw [Finset.sum_range_sub, hFm] at this
    convert this using 1
    ring
  · intro d c _ h
    exact S.F_sep c fun i => by rw [hFm]; exact h i
  · rw [← hFm]
    ext u
    exact Iff.rfl

end ThickeningSystem

section L33

variable {M C N : Type*} [AddCommGroup M] [DecidableEq M] [CommRing C]
  {𝒞 : M → AddSubgroup C} [GradedRing 𝒞] {m : Ideal C}

/-- Elements of `1 + m_0` are units (geometric series). -/
lemma IsCompletePair.isUnit_one_sub (hP : IsCompletePair 𝒞 m) {a : C} (ha : a ∈ m) (ha0 : a ∈ 𝒞 0) :
    IsUnit (1 - a) := by
  have hpow : ∀ n, a ^ n ∈ 𝒞 0 := fun n => by
    simpa using SetLike.pow_mem_graded n ha0
  obtain ⟨c, hc, hl⟩ := hP.exists_lim 0 (fun n => ∑ j ∈ Finset.range n, a ^ j)
    (fun n => (𝒞 0).sum_mem fun j _ => hpow j)
    (fun n => by
      rw [Finset.sum_range_succ, add_sub_cancel_left]
      exact Ideal.pow_mem_pow ha n)
  have h1m : (1 - a) ∈ 𝒞 0 := (𝒞 0).sub_mem SetLike.GradedOne.one_mem ha0
  have hmul : (1 - a) * c - 1 = 0 := by
    refine hP.sep 0 _ ?_ fun n => ?_
    · refine (𝒞 0).sub_mem ?_ SetLike.GradedOne.one_mem
      simpa using SetLike.GradedMul.mul_mem h1m hc
    · have h2 := Ideal.mul_mem_left (m ^ n) (1 - a) (hl n)
      have hg := mul_neg_geom_sum a n
      have : (1 - a) * c - 1 = (1 - a) * (c - ∑ j ∈ Finset.range n, a ^ j) - a ^ n := by
        rw [mul_sub, hg]; ring
      rw [this]
      exact Ideal.sub_mem _ h2 (Ideal.pow_mem_pow ha n)
  exact IsUnit.of_mul_eq_one _ (sub_eq_zero.1 hmul)

variable [AddCommGroup N] [Module C N] (ℳ : M → AddSubgroup N) [Decomposition ℳ]
  [SetLike.GradedSMul 𝒞 ℳ]

/-- `comp` of `a • x` for `x` homogeneous. -/
lemma comp_smul_homog {e : M} {x : N} (hx : x ∈ ℳ e) (i : M) (a : C) :
    comp ℳ (i + e) (a • x) = comp 𝒞 i a • x := by
  classical
  induction a using Decomposition.inductionOn 𝒞 with
  | zero => simp [comp_zero]
  | homogeneous a =>
    rename_i f
    have h1 : (a : C) • x ∈ ℳ (f + e) := SetLike.GradedSMul.smul_mem a.2 hx
    by_cases hf : f = i
    · subst hf
      rw [comp_of_mem ℳ h1, comp_of_mem 𝒞 a.2]
    · rw [comp_of_mem_ne ℳ h1 (fun h => hf (add_right_cancel h)), comp_of_mem_ne 𝒞 a.2 hf, zero_smul]
  | add a b ha hb => rw [add_smul, comp_add, ha, hb, comp_add, add_smul]

lemma pow_homogeneous (hm : m.IsHomogeneous 𝒞) (n : ℕ) : (m ^ n).IsHomogeneous 𝒞 :=
  by
  induction n with
  | zero => simpa using Ideal.IsHomogeneous.top (𝒜 := 𝒞)
  | succ n ih => rw [pow_succ]; exact Ideal.IsHomogeneous.mul ih hm

/-- `m^n N` is a homogeneous submodule. -/
lemma comp_mem_pow_smul (hm : m.IsHomogeneous 𝒞) (n : ℕ) (e : M) {y : N}
    (hy : y ∈ (m ^ n) • (⊤ : Submodule C N)) : comp ℳ e y ∈ (m ^ n) • (⊤ : Submodule C N) := by
  classical
  induction hy using Submodule.smul_induction_on' with
  | smul a ha b _ =>
    obtain ⟨s, hs⟩ := sum_comp 𝒞 a
    rw [hs, Finset.sum_smul, comp_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hi := comp_smul_of_mem 𝒞 ℳ (comp_mem 𝒞 i a) (e - i) b
    rw [show i + (e - i) = e by abel] at hi
    rw [hi]
    exact Submodule.smul_mem_smul (pow_homogeneous hm n i ha) trivial
  | add x _ y _ hx hy => rw [comp_add]; exact Submodule.add_mem _ hx hy

include ℳ in
/-- **Lemma 3.3 (graded Krull).** For `N` finite graded over a complete pair, `∩ m^n N = 0`. -/
theorem lemma_3_3_krull (hP : IsCompletePair 𝒞 m) [Module.Finite C N] {y : N}
    (hy : ∀ n : ℕ, y ∈ (m ^ n) • (⊤ : Submodule C N)) : y = 0 := by
  classical
  haveI := hP.noeth
  have hhom : ∀ e x, x ∈ ℳ e → (∀ n : ℕ, x ∈ (m ^ n) • (⊤ : Submodule C N)) → x = 0 := by
    intro e x hx hxn
    have hinf : x ∈ (⨅ i : ℕ, m ^ i • ⊤ : Submodule C N) := by
      simpa [Submodule.mem_iInf] using hxn
    obtain ⟨r, hr⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff m x).1 hinf
    have h1 := comp_smul_homog (𝒞 := 𝒞) ℳ hx 0 (r : C)
    rw [zero_add, hr, comp_of_mem ℳ hx] at h1
    have hr0 : comp 𝒞 0 (r : C) ∈ m := hP.hom 0 r.2
    have hu := hP.isUnit_one_sub hr0 (comp_mem 𝒞 0 _)
    have h2 : (1 - comp 𝒞 0 (r : C)) • x = 0 := by
      rw [sub_smul, one_smul, ← h1, sub_self]
    exact (hu.smul_eq_zero).1 h2
  obtain ⟨s, hs⟩ := sum_comp ℳ y
  rw [hs]
  refine Finset.sum_eq_zero fun e _ => ?_
  exact hhom e _ (comp_mem ℳ e y) fun n => comp_mem_pow_smul ℳ hP.hom n e (hy n)

include ℳ in
/-- Graded Nakayama for complete pairs. -/
theorem graded_nakayama (hP : IsCompletePair 𝒞 m) [Module.Finite C N]
    (h : m • (⊤ : Submodule C N) = ⊤) : Subsingleton N := by
  have hp : ∀ n : ℕ, (m ^ n) • (⊤ : Submodule C N) = ⊤ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_smul, h, ih]
  refine ⟨fun a b => ?_⟩
  rw [← sub_eq_zero]
  exact lemma_3_3_krull ℳ hP fun n => by rw [hp]; trivial

end L33

end AlgMag.ChartGraded

namespace AlgMag.ChartGraded

open DirectSum

section Quot

variable {M C : Type*} [AddCommGroup M] [DecidableEq M] [CommRing C]
  (𝒞 : M → AddSubgroup C) [GradedRing 𝒞] (b : Ideal C)

/-- The grading of `C/b`. -/
def quotGrade (d : M) : AddSubgroup (C ⧸ b) :=
  (𝒞 d).map (Ideal.Quotient.mk b).toAddMonoidHom

variable {𝒞 b}

lemma mk_mem_quotGrade {d : M} {c : C} (hc : c ∈ 𝒞 d) :
    Ideal.Quotient.mk b c ∈ quotGrade 𝒞 b d := ⟨c, hc, rfl⟩

theorem quotGrade_internal (hb : b.IsHomogeneous 𝒞) : DirectSum.IsInternal (quotGrade 𝒞 b) := by
  classical
  have hlift : ∀ x : ⨁ d, quotGrade 𝒞 b d, ∃ y : ⨁ d, 𝒞 d,
      (∀ d, Ideal.Quotient.mk b (y d : C) = (x d : C ⧸ b)) ∧
      DirectSum.coeAddMonoidHom (quotGrade 𝒞 b) x =
        Ideal.Quotient.mk b (DirectSum.coeAddMonoidHom 𝒞 y) := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => exact ⟨0, by simp, by simp⟩
    | of i t =>
      obtain ⟨c, hc, hct⟩ := t.2
      refine ⟨DirectSum.of (fun d => 𝒞 d) i ⟨c, hc⟩, fun d => ?_, ?_⟩
      · by_cases h : i = d
        · subst h
          rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
          exact hct
        · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
          simp
      · rw [DirectSum.coeAddMonoidHom_of, DirectSum.coeAddMonoidHom_of]
        exact hct.symm
    | add x y hx hy =>
      obtain ⟨u, hu1, hu2⟩ := hx
      obtain ⟨v, hv1, hv2⟩ := hy
      refine ⟨u + v, fun d => ?_, ?_⟩
      · simp [DirectSum.add_apply, hu1, hv1]
      · simp [hu2, hv2]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, hy1, hy2⟩ := hlift x
    rw [hx] at hy2
    have hmem : DirectSum.coeAddMonoidHom 𝒞 y ∈ b := Ideal.Quotient.eq_zero_iff_mem.1 hy2.symm
    refine DFinsupp.ext fun d => Subtype.ext ?_
    have hd := hb d hmem
    have hc : decompose 𝒞 (DirectSum.coeAddMonoidHom 𝒞 y) d = y d := by
      have h2 : decompose 𝒞 (DirectSum.coeAddMonoidHom 𝒞 y) = y :=
        (decomposeAddEquiv 𝒞).apply_symm_apply y
      rw [h2]
    rw [hc] at hd
    show (x d : C ⧸ b) = 0
    rw [← hy1]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hd
  · intro t
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective t
    obtain ⟨s, hs⟩ := sum_comp 𝒞 c
    refine ⟨∑ e ∈ s, DirectSum.of (fun d => quotGrade 𝒞 b d) e
      ⟨Ideal.Quotient.mk b (comp 𝒞 e c), mk_mem_quotGrade (comp_mem 𝒞 e c)⟩, ?_⟩
    rw [map_sum]
    conv_rhs => rw [hs, map_sum]
    exact Finset.sum_congr rfl fun e _ => by rw [DirectSum.coeAddMonoidHom_of]

/-- The graded ring structure of `C/b`, for `b` homogeneous. -/
noncomputable def quotGradedRing (hb : b.IsHomogeneous 𝒞) : GradedRing (quotGrade 𝒞 b) :=
  letI : Decomposition (quotGrade 𝒞 b) := (quotGrade_internal hb).chooseDecomposition
  letI : SetLike.GradedMonoid (quotGrade 𝒞 b) :=
    { one_mem := mk_mem_quotGrade SetLike.GradedOne.one_mem
      mul_mem := by
        rintro i j _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x * y, SetLike.GradedMul.mul_mem hx hy, rfl⟩ }
  { }

/-- The grading on `C/b` as a graded `C`-module. -/
lemma quot_gradedSMul : SetLike.GradedSMul 𝒞 (quotGrade 𝒞 b) where
  smul_mem := by
    rintro i j a _ ha ⟨y, hy, rfl⟩
    exact ⟨a * y, SetLike.GradedMul.mul_mem ha hy, rfl⟩

lemma comp_quot (hb : b.IsHomogeneous 𝒞) [Decomposition (quotGrade 𝒞 b)] (e : M) (c : C) :
    comp (quotGrade 𝒞 b) e (Ideal.Quotient.mk b c) = Ideal.Quotient.mk b (comp 𝒞 e c) := by
  classical
  induction c using Decomposition.inductionOn 𝒞 with
  | zero => simp [comp_zero]
  | homogeneous y =>
    rename_i f
    by_cases hf : f = e
    · subst hf
      rw [comp_of_mem _ (mk_mem_quotGrade y.2), comp_of_mem _ y.2]
    · rw [comp_of_mem_ne _ (mk_mem_quotGrade y.2) hf, comp_of_mem_ne _ y.2 hf, map_zero]
  | add x y hx hy => rw [map_add, comp_add, hx, hy, comp_add, map_add]

/-- **Lemma 3.3, second half.** `C/b` is a complete pair for each homogeneous ideal `b`. -/
theorem lemma_3_3_quot {m : Ideal C} (hP : IsCompletePair 𝒞 m) (hb : b.IsHomogeneous 𝒞) :
    letI := quotGradedRing hb
    IsCompletePair (quotGrade 𝒞 b) (m.map (Ideal.Quotient.mk b)) := by
  classical
  letI := quotGradedRing hb
  haveI := hP.noeth
  have hmk : Function.Surjective (Ideal.Quotient.mk b) := Ideal.Quotient.mk_surjective
  have hpow : ∀ n : ℕ, ∀ t, t ∈ (m.map (Ideal.Quotient.mk b)) ^ n ↔
      ∃ u ∈ m ^ n, Ideal.Quotient.mk b u = t := by
    intro n t
    rw [← Ideal.map_pow, Ideal.mem_map_iff_of_surjective _ hmk]
  -- homogeneous representative in `m^n`
  have hrep : ∀ (n : ℕ) (d : M) (c : C), c ∈ 𝒞 d →
      Ideal.Quotient.mk b c ∈ (m.map (Ideal.Quotient.mk b)) ^ n →
      ∃ t ∈ m ^ n, t ∈ 𝒞 d ∧ Ideal.Quotient.mk b t = Ideal.Quotient.mk b c := by
    intro n d c hc h
    obtain ⟨u, hu, hue⟩ := (hpow n _).1 h
    refine ⟨comp 𝒞 d u, pow_homogeneous hP.hom n d hu, comp_mem _ _ _, ?_⟩
    rw [← comp_quot hb, hue, comp_quot hb, comp_of_mem 𝒞 hc]
  refine ⟨isNoetherianRing_of_surjective C _ (Ideal.Quotient.mk b) hmk, ?_, ?_, ?_⟩
  · intro e t ht
    obtain ⟨u, hu, rfl⟩ := Ideal.mem_map_iff_of_surjective _ hmk |>.1 ht
    show comp (quotGrade 𝒞 b) e _ ∈ _
    rw [comp_quot hb]
    exact Ideal.mem_map_of_mem _ (hP.hom e hu)
  · intro d y hy hyd
    have hch : ∀ n, ∃ c ∈ 𝒞 d, Ideal.Quotient.mk b c = y n := fun n => by
      obtain ⟨c, hc, h⟩ := hy n
      exact ⟨c, hc, h⟩
    choose c hc hce using hch
    have hst : ∀ n, ∃ t ∈ m ^ n, t ∈ 𝒞 d ∧
        Ideal.Quotient.mk b t = Ideal.Quotient.mk b (c (n + 1) - c n) := fun n =>
      hrep n d _ ((𝒞 d).sub_mem (hc _) (hc _)) (by
        rw [map_sub, hce, hce]; exact hyd n)
    choose t ht1 ht2 ht3 using hst
    let Y : ℕ → C := fun n => c 0 + ∑ j ∈ Finset.range n, t j
    have hYd : ∀ n, Y n ∈ 𝒞 d := fun n =>
      (𝒞 d).add_mem (hc 0) ((𝒞 d).sum_mem fun j _ => ht2 j)
    have hYm : ∀ n, Ideal.Quotient.mk b (Y n) = y n := by
      intro n
      induction n with
      | zero => simp [Y, hce]
      | succ n ih =>
        have : Y (n + 1) = Y n + t n := by simp [Y, Finset.sum_range_succ]; ring
        rw [this, map_add, ih, ht3, map_sub, hce, hce]; ring
    obtain ⟨w, hw, hl⟩ := hP.exists_lim d Y hYd (fun n => by
      have : Y (n + 1) - Y n = t n := by simp [Y, Finset.sum_range_succ]
      rw [this]; exact ht1 n)
    refine ⟨Ideal.Quotient.mk b w, mk_mem_quotGrade hw, fun n => ?_⟩
    rw [← hYm n, ← map_sub, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ (hl n)
  · intro d t ht hn
    haveI : SetLike.GradedSMul 𝒞 (quotGrade 𝒞 b) := quot_gradedSMul
    haveI : Module.Finite C (C ⧸ b) := Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ C b).toLinearMap hmk
    refine lemma_3_3_krull (𝒞 := 𝒞) (quotGrade 𝒞 b) hP fun n => ?_
    obtain ⟨u, hu, rfl⟩ := (hpow n t).1 (hn n)
    have : Ideal.Quotient.mk b u = u • (1 : C ⧸ b) := by
      rw [Algebra.smul_def]; simp
    rw [this]
    exact Submodule.smul_mem_smul hu trivial

end Quot

/-! ### Lemma 3.4 -/

/-- A compatible system of graded `C`-modules `N_n` killed by `m^{n+1}`, with `N_{n+1}/m^{n+1} = N_n`
(Lemma 3.4; the note's `N_{n+1}` is `N n` here). -/
structure ModSystem {M C : Type*} [AddCommGroup M] [DecidableEq M] [CommRing C]
    (𝒞 : M → AddSubgroup C) [GradedRing 𝒞] (m : Ideal C) where
  /-- the modules -/
  N : ℕ → Type*
  [grp : ∀ n, AddCommGroup (N n)]
  [mod : ∀ n, Module C (N n)]
  /-- the gradings -/
  ℳ : ∀ n, M → AddSubgroup (N n)
  [dec : ∀ n, Decomposition (ℳ n)]
  [gsm : ∀ n, SetLike.GradedSMul 𝒞 (ℳ n)]
  /-- transitions -/
  p : ∀ n, N (n + 1) →ₗ[C] N n
  p_mem : ∀ n d y, y ∈ ℳ (n + 1) d → p n y ∈ ℳ n d
  p_surj : ∀ n, Function.Surjective (p n)
  ker_p : ∀ n, LinearMap.ker (p n) = (m ^ (n + 1)) • (⊤ : Submodule C (N (n + 1)))
  tors : ∀ n, (m ^ (n + 1)) • (⊤ : Submodule C (N n)) = ⊥
  fin0 : Module.Finite C (N 0)

attribute [instance] ModSystem.grp ModSystem.mod ModSystem.dec ModSystem.gsm

namespace ModSystem

variable {M C : Type*} [AddCommGroup M] [DecidableEq M] [CommRing C]
  {𝒞 : M → AddSubgroup C} [GradedRing 𝒞] {m : Ideal C} (Y : ModSystem 𝒞 m)

/-- Additive transitions. -/
def pa (n : ℕ) : Y.N (n + 1) →+ Y.N n := (Y.p n).toAddMonoidHom

lemma glim_smul {i j : M} {a : C} (ha : a ∈ 𝒞 i) {u : ∀ n, Y.N n} (hu : u ∈ glim Y.ℳ Y.pa j) :
    a • u ∈ glim Y.ℳ Y.pa (i + j) := by
  refine ⟨fun n => ?_, fun n => SetLike.GradedSMul.smul_mem ha (hu.2 n)⟩
  have h := hu.1 n
  show Y.p n (a • u (n + 1)) = a • u n
  rw [map_smul]
  exact congrArg _ h

/-- `N = ⊕_d lim (N_n)_d`. -/
def Lim : Submodule C (∀ n, Y.N n) where
  carrier := gL Y.ℳ Y.pa
  add_mem' := (gL Y.ℳ Y.pa).add_mem
  zero_mem' := (gL Y.ℳ Y.pa).zero_mem
  smul_mem' a u hu := by
    obtain ⟨s, hs⟩ := sum_comp 𝒞 a
    rw [hs, Finset.sum_smul]
    refine (gL Y.ℳ Y.pa).sum_mem fun i _ => ?_
    induction hu using AddSubgroup.iSup_induction' with
    | hp j x hx => exact glim_le_gL _ _ _ (Y.glim_smul (comp_mem 𝒞 i a) hx)
    | h1 => simpa using (gL Y.ℳ Y.pa).zero_mem
    | hadd x z _ _ hx hz => rw [smul_add]; exact (gL Y.ℳ Y.pa).add_mem hx hz

/-- Inclusion of the limit in the product. -/
def Lι : Y.Lim →+ ∀ n, Y.N n := Y.Lim.subtype.toAddMonoidHom

/-- The grading on the limit. -/
abbrev ℒ (d : M) : AddSubgroup Y.Lim := tgrade Y.ℳ Y.pa Y.Lι d

noncomputable instance : Decomposition Y.ℒ :=
  (tgrade_internal (ℳ := Y.ℳ) (p := Y.pa) Y.Lι Subtype.val_injective
    (fun u hu => ⟨⟨u, hu⟩, rfl⟩) (fun t => t.2)).chooseDecomposition

instance : SetLike.GradedSMul 𝒞 Y.ℒ where
  smul_mem := fun {i j a u} ha hu => Y.glim_smul ha hu

/-- Evaluation `N → N_n`. -/
def ev (n : ℕ) : Y.Lim →ₗ[C] Y.N n := (LinearMap.proj n).comp Y.Lim.subtype

lemma p_ev (n : ℕ) (u : Y.Lim) : Y.p n (Y.ev (n + 1) u) = Y.ev n u :=
  gL_compat Y.ℳ Y.pa u.2 n

lemma ev_mem {n : ℕ} {d : M} {u : Y.Lim} (hu : u ∈ Y.ℒ d) : Y.ev n u ∈ Y.ℳ n d := hu.2 n

lemma ext_ev {u v : Y.Lim} (h : ∀ n, Y.ev n u = Y.ev n v) : u = v :=
  Subtype.ext (funext h)

lemma pa_mem (n : ℕ) (d : M) (y : Y.N (n + 1)) (h : y ∈ Y.ℳ (n + 1) d) : Y.pa n y ∈ Y.ℳ n d :=
  Y.p_mem n d y h

lemma ev_comp (n : ℕ) (e : M) (u : Y.Lim) :
    Y.ev n (comp Y.ℒ e u) = comp (Y.ℳ n) e (Y.ev n u) :=
  lvl_comp (ℳ := Y.ℳ) (p := Y.pa) Y.Lι Y.pa_mem e u n

lemma exists_ev_mem (n : ℕ) {d : M} {x : Y.N n} (hx : x ∈ Y.ℳ n d) :
    ∃ u ∈ Y.ℒ d, Y.ev n u = x := by
  obtain ⟨u, hu, h⟩ := exists_lift (ℳ := Y.ℳ) (p := Y.pa) Y.pa_mem Y.p_surj n hx
  exact ⟨⟨u, glim_le_gL _ _ _ hu⟩, hu, h⟩

lemma ev_surj (n : ℕ) : Function.Surjective (Y.ev n) := by
  intro x
  obtain ⟨s, hs⟩ := sum_comp (Y.ℳ n) x
  have : ∀ e, ∃ u ∈ Y.ℒ e, Y.ev n u = comp (Y.ℳ n) e x :=
    fun e => Y.exists_ev_mem n (comp_mem _ _ _)
  choose u _ hu using this
  exact ⟨∑ e ∈ s, u e, by rw [map_sum, Finset.sum_congr rfl fun e _ => hu e]; exact hs.symm⟩

/-- The filtration of the limit. -/
def Φ : ℕ → AddSubgroup Y.Lim
  | 0 => ⊤
  | i + 1 => (LinearMap.ker (Y.ev i)).toAddSubgroup

lemma Φ_succ {i : ℕ} {u : Y.Lim} : u ∈ Y.Φ (i + 1) ↔ Y.ev i u = 0 := LinearMap.mem_ker

lemma Φ_anti : Antitone Y.Φ := by
  refine antitone_nat_of_succ_le fun i => ?_
  cases i with
  | zero => exact le_top
  | succ i =>
    intro u hu
    rw [Φ_succ] at hu ⊢
    rw [← Y.p_ev, hu, map_zero]

/-- Each step of the kernel: `u ∈ Φ i` gives `ev_i u ∈ m^i N_i`. -/
lemma ev_mem_pow {i : ℕ} {u : Y.Lim} (hu : u ∈ Y.Φ i) :
    Y.ev i u ∈ (m ^ i) • (⊤ : Submodule C (Y.N i)) := by
  cases i with
  | zero => simp
  | succ i =>
    rw [← Y.ker_p, LinearMap.mem_ker, Y.p_ev]
    exact Y.Φ_succ.1 hu

lemma smul_mem_Φ {i : ℕ} {a : C} (ha : a ∈ m ^ i) (u : Y.Lim) : a • u ∈ Y.Φ i := by
  cases i with
  | zero => trivial
  | succ i =>
    rw [Φ_succ, map_smul]
    have := Submodule.smul_mem_smul ha (Submodule.mem_top (x := Y.ev i u))
    rw [Y.tors] at this
    simpa using this

/-- One approximation step for `mem_span_of_gen`. -/
lemma gen_step (hm : m.IsHomogeneous 𝒞) {r : ℕ} (e : Fin r → Y.Lim) (δ : Fin r → M)
    (he : ∀ w, e w ∈ Y.ℒ (δ w))
    (hgen : ∀ i, Submodule.span C (Set.range fun w => Y.ev i (e w)) = ⊤) (d : M) (i : ℕ)
    (u : Y.Lim) (hu : u ∈ Y.Φ i) (hud : u ∈ Y.ℒ d) :
    ∃ a : Fin r → C, (∀ w, a w ∈ m ^ (i - 0) ∧ a w ∈ 𝒞 (d - δ w)) ∧
      u - ∑ w, a w • e w ∈ Y.Φ (i + 1) := by
  classical
  have h1 := Y.ev_mem_pow hu
  rw [← hgen i, Submodule.mem_ideal_smul_span_iff_exists_sum] at h1
  obtain ⟨a, ha, hae⟩ := h1
  refine ⟨fun w => comp 𝒞 (d - δ w) (a w),
    fun w => ⟨pow_homogeneous hm i _ (ha w), comp_mem _ _ _⟩, ?_⟩
  rw [Φ_succ, map_sub, map_sum, sub_eq_zero]
  rw [← comp_of_mem (Y.ℳ i) (Y.ev_mem hud), ← hae, Finsupp.sum_fintype _ _ (by simp), comp_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have := comp_smul_homog (𝒞 := 𝒞) (Y.ℳ i) (Y.ev_mem (he w)) (d - δ w) (a w)
  rw [show d - δ w + δ w = d by abel] at this
  rw [this, map_smul]

/-- Common core of existence and uniqueness in Lemma 3.4: if a finite homogeneous family of the limit
generates every `N_i`, then `Φ^{i₀} ∩ N_d` is `Σ (m^{i₀} ∩ C_{d - d_w}) e_w`. -/
theorem mem_span_of_gen (hP : IsCompletePair 𝒞 m) {r : ℕ} (e : Fin r → Y.Lim) (δ : Fin r → M)
    (he : ∀ w, e w ∈ Y.ℒ (δ w))
    (hgen : ∀ i, Submodule.span C (Set.range fun w => Y.ev i (e w)) = ⊤)
    (i₀ : ℕ) (d : M) {y : Y.Lim} (hy : y ∈ Y.Φ i₀) (hyd : y ∈ Y.ℒ d) :
    ∃ a : Fin r → C, (∀ w, a w ∈ m ^ i₀ ∧ a w ∈ 𝒞 (d - δ w)) ∧ y = ∑ w, a w • e w := by
  classical
  have hzero : (m ^ 0 : Ideal C) = ⊤ := by simp
  have hanti : Antitone fun j => m ^ j := fun i j hij => Ideal.pow_le_pow_right hij
  have hsep : ∀ u : Y.Lim, (∀ i, u ∈ Y.Φ i) → u = 0 := fun u hu => Y.ext_ev fun n => by
    rw [map_zero]; exact Y.Φ_succ.1 (hu (n + 1))
  have hv : ∀ (w : Fin r) (i : ℕ) (a : C), a ∈ m ^ i → a • e w ∈ Y.Φ (i + 0) :=
    fun w i a ha => Y.smul_mem_Φ ha _
  have hcompl : ∀ (w : Fin r) (z : ℕ → C), (∀ j, z j ∈ m ^ j ∧ z j ∈ 𝒞 (d - δ w)) →
      ∃ c ∈ 𝒞 (d - δ w), ∀ N, c - ∑ j ∈ Finset.range N, z j ∈ m ^ N := by
    intro w z hz
    exact hP.exists_lim (d - δ w) (fun n => ∑ j ∈ Finset.range n, z j)
      (fun n => AddSubgroup.sum_mem _ fun j _ => (hz j).2)
      (fun n => by rw [Finset.sum_range_succ, add_sub_cancel_left]; exact (hz n).1)
  have hSv : ∀ (w : Fin r) (a : C), a ∈ 𝒞 (d - δ w) → a • e w ∈ Y.ℒ d := by
    intro w a ha
    have := SetLike.GradedSMul.smul_mem (A := 𝒞) (B := Y.ℒ) ha (he w)
    rw [show (d - δ w) +ᵥ δ w = d by simp] at this
    exact this
  obtain ⟨a, ha, hae⟩ := approx (R := C) (V := Y.Lim) (W := Fin r) (fun j => m ^ j) Y.Φ (Y.ℒ d)
    (fun w => 𝒞 (d - δ w)) e (fun _ => 0) hzero hanti Y.Φ_anti hsep hv hcompl hSv
    (fun i u hu hud => Y.gen_step hP.hom e δ he hgen d i u hu hud) i₀ hy hyd
  exact ⟨a, by simpa using ha, hae⟩

/-- `ev_i u = 0` iff `ev_{i+k} u ∈ m^{i+1} N_{i+k}`. -/
lemma ev_eq_zero_iff (i k : ℕ) (u : Y.Lim) :
    Y.ev i u = 0 ↔ Y.ev (i + k) u ∈ (m ^ (i + 1)) • (⊤ : Submodule C (Y.N (i + k))) := by
  induction k with
  | zero => show _ ↔ Y.ev i u ∈ _; rw [Y.tors]; simp
  | succ k ih =>
    rw [ih]
    show _ ↔ Y.ev (i + k + 1) u ∈ (m ^ (i + 1)) • (⊤ : Submodule C (Y.N (i + k + 1)))
    constructor
    · intro h
      have hmap : (m ^ (i + 1)) • (⊤ : Submodule C (Y.N (i + k))) =
          ((m ^ (i + 1)) • (⊤ : Submodule C (Y.N (i + k + 1)))).map (Y.p (i + k)) := by
        rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 (Y.p_surj _)]
      rw [hmap] at h
      obtain ⟨w, hw, hwe⟩ := h
      have hker : Y.ev (i + k + 1) u - w ∈ LinearMap.ker (Y.p (i + k)) := by
        rw [LinearMap.mem_ker, map_sub, hwe, Y.p_ev, sub_self]
      rw [Y.ker_p] at hker
      have hle : (m ^ (i + k + 1)) • (⊤ : Submodule C (Y.N (i + k + 1))) ≤
          (m ^ (i + 1)) • ⊤ :=
        Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
      simpa using Submodule.add_mem _ (hle hker) hw
    · intro h
      rw [← Y.p_ev]
      have := Submodule.mem_map_of_mem (f := Y.p (i + k)) h
      rwa [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 (Y.p_surj _)] at this

/-- Nilpotent Nakayama: generators of `N_0` from the limit generate each `N_i`. -/
lemma gen_of_gen0 {r : ℕ} (e : Fin r → Y.Lim)
    (h0 : Submodule.span C (Set.range fun w => Y.ev 0 (e w)) = ⊤) (i : ℕ) :
    Submodule.span C (Set.range fun w => Y.ev i (e w)) = ⊤ := by
  classical
  set P := Submodule.span C (Set.range fun w => Y.ev i (e w)) with hPdef
  have hmapi : ∀ n, Submodule.span C (Set.range fun w => Y.ev n (e w)) =
      (Submodule.span C (Set.range e)).map (Y.ev n) := by
    intro n
    rw [Submodule.map_span, ← Set.range_comp]; rfl
  have h1 : (⊤ : Submodule C (Y.N i)) ≤ P ⊔ m • ⊤ := by
    intro t _
    obtain ⟨u, rfl⟩ := Y.ev_surj i t
    have hu0 : Y.ev 0 u ∈ (Submodule.span C (Set.range e)).map (Y.ev 0) := by
      rw [← hmapi, h0]; trivial
    obtain ⟨v, hv, hve⟩ := hu0
    have hz : Y.ev 0 (u - v) = 0 := by rw [map_sub, hve, sub_self]
    have h2 := (Y.ev_eq_zero_iff 0 i (u - v)).1 hz
    have h3 : (0 + i) = i := Nat.zero_add i
    rw [h3] at h2
    have h4 : Y.ev i v ∈ P := by
      rw [hPdef, hmapi]; exact Submodule.mem_map_of_mem hv
    refine Submodule.mem_sup.2 ⟨Y.ev i v, h4, Y.ev i (u - v), by simpa using h2, ?_⟩
    rw [map_sub]; abel
  have h2 : ∀ k : ℕ, (⊤ : Submodule C (Y.N i)) ≤ P ⊔ (m ^ k) • ⊤ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      refine ih.trans (sup_le le_sup_left ?_)
      calc (m ^ k) • (⊤ : Submodule C (Y.N i)) ≤ (m ^ k) • (P ⊔ m • ⊤) :=
            smul_mono_right _ h1
        _ = (m ^ k) • P ⊔ (m ^ (k + 1)) • ⊤ := by
            rw [Submodule.smul_sup, pow_succ, mul_smul]
        _ ≤ P ⊔ (m ^ (k + 1)) • ⊤ :=
            sup_le_sup_right (Submodule.smul_le_right) _
  have h3 := h2 (i + 1)
  rw [Y.tors, sup_bot_eq] at h3
  exact top_le_iff.1 h3

/-- **Lemma 3.4 (Grothendieck existence for graded rings).** Over a complete pair, `N = ⊕_d lim (N_n)_d`
is finite graded, with `N/m^{n+1}N = N_n`. -/
theorem lemma_3_4 (hP : IsCompletePair 𝒞 m) :
    Module.Finite C Y.Lim ∧
    ∀ n, LinearMap.ker (Y.ev n) = (m ^ (n + 1)) • (⊤ : Submodule C Y.Lim) ∧
      Function.Surjective (Y.ev n) ∧ ∀ d, ∀ x ∈ Y.ℳ n d, ∃ u ∈ Y.ℒ d, Y.ev n u = x := by
  classical
  haveI := Y.fin0
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule C (Y.N 0)).FG)
  obtain ⟨r, x, δ, hxd, hxc, _⟩ := exists_homogeneous_family (Y.ℳ 0) s
  have hl : ∀ w, ∃ u ∈ Y.ℒ (δ w), Y.ev 0 u = x w := fun w => Y.exists_ev_mem 0 (hxd w)
  choose e he hee using hl
  have h0 : Submodule.span C (Set.range fun w => Y.ev 0 (e w)) = ⊤ := by
    have hxx : (fun w => Y.ev 0 (e w)) = x := funext hee
    rw [hxx, eq_top_iff, ← hs, Submodule.span_le]
    intro a ha
    have key : ∀ a ∈ AddSubgroup.closure (Set.range x), a ∈ Submodule.span C (Set.range x) := by
      intro a ha
      induction ha using AddSubgroup.closure_induction with
      | mem a h => exact Submodule.subset_span h
      | zero => exact Submodule.zero_mem _
      | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
      | neg a _ ha => exact Submodule.neg_mem _ ha
    exact key a (hxc a ha)
  have hg := Y.gen_of_gen0 e h0
  have hspan : ∀ (i₀ : ℕ) (u : Y.Lim), u ∈ Y.Φ i₀ →
      u ∈ (m ^ i₀) • Submodule.span C (Set.range e) := by
    intro i₀ u hu
    obtain ⟨t, ht⟩ := sum_comp Y.ℒ u
    rw [ht]
    refine Submodule.sum_mem _ fun d _ => ?_
    have hcΦ : comp Y.ℒ d u ∈ Y.Φ i₀ := by
      cases i₀ with
      | zero => trivial
      | succ i =>
        rw [Φ_succ, ev_comp, Y.Φ_succ.1 hu, comp_zero]
    obtain ⟨a, ha, hae⟩ := Y.mem_span_of_gen hP e δ he hg i₀ d hcΦ (comp_mem _ _ _)
    rw [hae]
    exact Submodule.sum_mem _ fun w _ =>
      Submodule.smul_mem_smul (ha w).1 (Submodule.subset_span ⟨w, rfl⟩)
  refine ⟨⟨⟨Finset.univ.image e, ?_⟩⟩, fun n => ⟨?_, Y.ev_surj n,
    fun d x hx => Y.exists_ev_mem n hx⟩⟩
  · rw [eq_top_iff]
    intro u _
    have := hspan 0 u trivial
    simpa using this
  · refine le_antisymm (fun u hu => ?_) ?_
    · exact (smul_mono_right (m ^ (n + 1)) (le_top : Submodule.span C (Set.range e) ≤ ⊤)) (hspan (n + 1) u (Y.Φ_succ.2 hu))
    · rw [Submodule.smul_le]
      intro a ha u _
      exact Y.Φ_succ.1 (Y.smul_mem_Φ ha u)

end ModSystem

end AlgMag.ChartGraded

namespace AlgMag.ChartGraded

open DirectSum

/-- Graded additive maps commute with components. -/
lemma comp_map {M N N' : Type*} [AddCommGroup M] [DecidableEq M] [AddCommGroup N] [AddCommGroup N']
    (ℳ : M → AddSubgroup N) [Decomposition ℳ] (ℳ' : M → AddSubgroup N') [Decomposition ℳ']
    (f : N →+ N') (hf : ∀ d y, y ∈ ℳ d → f y ∈ ℳ' d) (e : M) (y : N) :
    f (comp ℳ e y) = comp ℳ' e (f y) := by
  classical
  induction y using Decomposition.inductionOn ℳ with
  | zero => simp [comp_zero]
  | homogeneous y =>
    rename_i g
    by_cases h : g = e
    · subst h
      rw [comp_of_mem _ y.2, comp_of_mem _ (hf _ _ y.2)]
    · rw [comp_of_mem_ne _ y.2 h, comp_of_mem_ne _ (hf _ _ y.2) h, map_zero]
  | add a b ha hb => simp only [comp_add, map_add, ha, hb]

namespace ModSystem

variable {M C : Type*} [AddCommGroup M] [DecidableEq M] [CommRing C]
  {𝒞 : M → AddSubgroup C} [GradedRing 𝒞] {m : Ideal C} (Y : ModSystem 𝒞 m)

/-- **Lemma 3.4, uniqueness (graded Nakayama + Krull).** A finite graded module `P` with graded
surjections `q_n : P → N_n` of kernel `m^{n+1}P`, compatible with the system, is canonically
isomorphic to `N = ⊕_d lim (N_n)_d`, as graded modules and compatibly with the `q_n`. -/
theorem lemma_3_4_unique (hP : IsCompletePair 𝒞 m) {P : Type*} [AddCommGroup P] [Module C P]
    (Pg : M → AddSubgroup P) [Decomposition Pg] [SetLike.GradedSMul 𝒞 Pg] [Module.Finite C P]
    (q : ∀ n, P →ₗ[C] Y.N n) (q_mem : ∀ n d x, x ∈ Pg d → q n x ∈ Y.ℳ n d)
    (q_comm : ∀ n x, Y.p n (q (n + 1) x) = q n x) (q_surj : ∀ n, Function.Surjective (q n))
    (q_ker : ∀ n, LinearMap.ker (q n) = (m ^ (n + 1)) • (⊤ : Submodule C P)) :
    ∃ θ : P ≃ₗ[C] Y.Lim, (∀ n x, Y.ev n (θ x) = q n x) ∧ ∀ d x, x ∈ Pg d ↔ θ x ∈ Y.ℒ d := by
  classical
  have hglim : ∀ d x, x ∈ Pg d → (fun n => q n x) ∈ glim Y.ℳ Y.pa d := fun d x hx =>
    ⟨fun n => q_comm n x, fun n => q_mem n d x hx⟩
  have hL : ∀ x, (fun n => q n x) ∈ gL Y.ℳ Y.pa := by
    intro x
    obtain ⟨s, hs⟩ := sum_comp Pg x
    have : (fun n => q n x) = ∑ e ∈ s, fun n => q n (comp Pg e x) := by
      funext n
      rw [Finset.sum_apply, ← map_sum, ← hs]
    rw [this]
    exact AddSubgroup.sum_mem _ fun e _ => glim_le_gL _ _ _ (hglim e _ (comp_mem _ _ _))
  let θ₀ : P →ₗ[C] Y.Lim :=
    { toFun := fun x => ⟨fun n => q n x, hL x⟩
      map_add' := fun x y => Subtype.ext (funext fun n => map_add _ _ _)
      map_smul' := fun a x => Subtype.ext (funext fun n => map_smul _ _ _) }
  have hev : ∀ n x, Y.ev n (θ₀ x) = q n x := fun n x => rfl
  have hinj : Function.Injective θ₀ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    refine lemma_3_3_krull (𝒞 := 𝒞) Pg hP fun n => ?_
    have h : x ∈ (m ^ (n + 1)) • (⊤ : Submodule C P) := by
      rw [← q_ker, LinearMap.mem_ker, ← hev, hx, map_zero]
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n)) h
  have hsurj : Function.Surjective θ₀ := by
    intro y
    obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule C P).FG)
    obtain ⟨r, x, δ, hxd, hxc, _⟩ := exists_homogeneous_family Pg s
    have hspan : Submodule.span C (Set.range x) = ⊤ := by
      rw [eq_top_iff, ← hs, Submodule.span_le]
      intro a ha
      have key : ∀ a ∈ AddSubgroup.closure (Set.range x), a ∈ Submodule.span C (Set.range x) := by
        intro a ha
        induction ha using AddSubgroup.closure_induction with
        | mem a h => exact Submodule.subset_span h
        | zero => exact Submodule.zero_mem _
        | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
        | neg a _ ha => exact Submodule.neg_mem _ ha
      exact key a (hxc a ha)
    have hgen : ∀ i, Submodule.span C (Set.range fun w => Y.ev i (θ₀ (x w))) = ⊤ := by
      intro i
      have : (Set.range fun w => Y.ev i (θ₀ (x w))) = (q i) '' Set.range x := by
        rw [← Set.range_comp]; rfl
      rw [this, ← Submodule.map_span, hspan, Submodule.map_top,
        LinearMap.range_eq_top.2 (q_surj i)]
    obtain ⟨t, ht⟩ := sum_comp Y.ℒ y
    have hcomp : ∀ e, ∃ z, θ₀ z = comp Y.ℒ e y := by
      intro e
      obtain ⟨a, _, hae⟩ := Y.mem_span_of_gen hP (fun w => θ₀ (x w)) δ
        (fun w => hglim _ _ (hxd w)) hgen 0 e (y := comp Y.ℒ e y) trivial (comp_mem _ _ _)
      exact ⟨∑ w, a w • x w, by rw [hae, map_sum]; simp⟩
    choose z hz using hcomp
    exact ⟨∑ e ∈ t, z e, by
      rw [map_sum, Finset.sum_congr rfl fun e _ => hz e]; exact ht.symm⟩
  refine ⟨LinearEquiv.ofBijective θ₀ ⟨hinj, hsurj⟩, fun n x => rfl, fun d x => ⟨hglim d x, ?_⟩⟩
  intro hx
  have hx' : θ₀ x ∈ Y.ℒ d := hx
  have hc : ∀ e, e ≠ d → comp Pg e x = 0 := by
    intro e he
    apply hinj
    rw [map_zero]
    refine Y.ext_ev fun n => ?_
    rw [hev, map_zero]
    have h1 := comp_map Pg (Y.ℳ n) (q n).toAddMonoidHom (fun d y hy => q_mem n d y hy) e x
    have h2 : q n x ∈ Y.ℳ n d := hx'.2 n
    simp only [LinearMap.toAddMonoidHom_coe] at h1
    rw [h1]
    exact comp_of_mem_ne _ h2 (Ne.symm he)
  obtain ⟨s, hs⟩ := sum_comp Pg x
  have : x = comp Pg d x := by
    conv_lhs => rw [hs]
    by_cases hd : d ∈ s
    · rw [Finset.sum_eq_single_of_mem d hd fun e _ he => hc e he]
    · rw [Finset.sum_eq_zero fun e he => hc e (fun h => hd (h ▸ he))]
      have hxz : x = 0 := by
        rw [hs]; exact Finset.sum_eq_zero fun e he => hc e (fun h => hd (h ▸ he))
      rw [hxz, comp_zero]
  rw [this]
  exact comp_mem _ _ _

variable (Y' : ModSystem 𝒞 m)

/-- **Lemma 3.4, Homs (one direction).** A compatible family of graded maps `N_n → N'_n` comes from a
unique graded map of limits. -/
theorem lemma_3_4_hom_of_family (φ : ∀ n, Y.N n →ₗ[C] Y'.N n)
    (φ_mem : ∀ n d x, x ∈ Y.ℳ n d → φ n x ∈ Y'.ℳ n d)
    (φ_comm : ∀ n x, Y'.p n (φ (n + 1) x) = φ n (Y.p n x)) :
    ∃! Θ : Y.Lim →ₗ[C] Y'.Lim, (∀ n u, Y'.ev n (Θ u) = φ n (Y.ev n u)) ∧
      ∀ d u, u ∈ Y.ℒ d → Θ u ∈ Y'.ℒ d := by
  classical
  have hg : ∀ d (u : ∀ n, Y.N n), u ∈ glim Y.ℳ Y.pa d →
      (fun n => φ n (u n)) ∈ glim Y'.ℳ Y'.pa d := fun d u hu =>
    ⟨fun n => by
      show Y'.p n (φ (n + 1) (u (n + 1))) = _
      rw [φ_comm]
      exact congrArg _ (hu.1 n), fun n => φ_mem n d _ (hu.2 n)⟩
  have hL : ∀ u, u ∈ gL Y.ℳ Y.pa → (fun n => φ n (u n)) ∈ gL Y'.ℳ Y'.pa := by
    intro u hu
    induction hu using AddSubgroup.iSup_induction' with
    | hp d x hx => exact glim_le_gL _ _ _ (hg d x hx)
    | h1 => convert (gL Y'.ℳ Y'.pa).zero_mem using 1; funext n; simp
    | hadd x z _ _ hx hz =>
      have : (fun n => φ n ((x + z) n)) = (fun n => φ n (x n)) + fun n => φ n (z n) := by
        funext n; simp
      rw [this]
      exact (gL Y'.ℳ Y'.pa).add_mem hx hz
  refine ⟨{ toFun := fun u => ⟨fun n => φ n (u.1 n), hL _ u.2⟩
            map_add' := fun x y => Subtype.ext (funext fun n => map_add _ _ _)
            map_smul' := fun a x => Subtype.ext (funext fun n => map_smul _ _ _) },
    ⟨fun n u => rfl, fun d u hu => hg d _ hu⟩, ?_⟩
  rintro Θ ⟨h1, _⟩
  ext u n
  exact h1 n u

/-- **Lemma 3.4, Homs (other direction).** A graded map of limits induces a unique compatible family
of graded maps `N_n → N'_n`. -/
theorem lemma_3_4_family_of_hom (hP : IsCompletePair 𝒞 m) (Θ : Y.Lim →ₗ[C] Y'.Lim)
    (hΘ : ∀ d u, u ∈ Y.ℒ d → Θ u ∈ Y'.ℒ d) :
    ∃! φ : ∀ n, Y.N n →ₗ[C] Y'.N n, (∀ n u, Y'.ev n (Θ u) = φ n (Y.ev n u)) ∧
      (∀ n d x, x ∈ Y.ℳ n d → φ n x ∈ Y'.ℳ n d) ∧
      ∀ n x, Y'.p n (φ (n + 1) x) = φ n (Y.p n x) := by
  classical
  have hker : ∀ n, LinearMap.ker (Y.ev n) ≤ LinearMap.ker ((Y'.ev n).comp Θ) := by
    intro n u hu
    rw [(Y.lemma_3_4 hP).2 n |>.1] at hu
    rw [LinearMap.mem_ker, LinearMap.comp_apply]
    have hle : (m ^ (n + 1)) • (⊤ : Submodule C Y.Lim) ≤
        LinearMap.ker ((Y'.ev n).comp Θ) := by
      rw [Submodule.smul_le]
      intro a ha t _
      rw [LinearMap.mem_ker, LinearMap.comp_apply, map_smul]
      exact Y'.Φ_succ.1 (Y'.smul_mem_Φ ha (Θ t))
    exact hle hu
  have hex : ∀ n, ∃ φ : Y.N n →ₗ[C] Y'.N n, ∀ u, Y'.ev n (Θ u) = φ (Y.ev n u) := by
    intro n
    let E := (Y.ev n).quotKerEquivOfSurjective (Y.ev_surj n)
    refine ⟨((LinearMap.ker (Y.ev n)).liftQ _ (hker n)).comp E.symm.toLinearMap, fun u => ?_⟩
    have h : E.symm (Y.ev n u) = Submodule.Quotient.mk u := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp [h]
  choose φ hφ using hex
  refine ⟨φ, ⟨hφ, ?_, ?_⟩, ?_⟩
  · intro n d x hx
    obtain ⟨u, hu, rfl⟩ := Y.exists_ev_mem n hx
    rw [← hφ]
    exact Y'.ev_mem (hΘ d u hu)
  · intro n x
    obtain ⟨u, rfl⟩ := Y.ev_surj (n + 1) x
    rw [← hφ, Y'.p_ev, Y.p_ev, ← hφ]
  · rintro ψ ⟨hψ, _, _⟩
    funext n
    ext x
    obtain ⟨u, rfl⟩ := Y.ev_surj n x
    rw [← hψ, hφ]

end ModSystem

end AlgMag.ChartGraded
