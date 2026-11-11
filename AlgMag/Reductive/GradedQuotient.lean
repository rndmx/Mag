/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.AttractorSmooth
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Attractors of a homogeneous closed subscheme

Let `A` be an `M`-graded `R₀`-algebra and `I` a homogeneous ideal. Then `A ⧸ I` is graded by the
images of the `𝒜 m` (`homogQuotGrading`), its magnet ideals are the images of those of `A`
(`magnetIdeal_homogQuotGrading`), and if `A ⧸ I` is smooth over a Noetherian `R₀`, so is
`A ⧸ (I ⊔ J_N)` for every magnet `N` (`smooth_quotient_sup_magnetIdeal`).

For a smooth closed subgroup `U = V(I)` normalized by a torus (a normal subgroup, by
`AlgMag.Reductive.mem_of_normal_of_coeff`), this says that `U ∩ G^N = U^N` is smooth.
-/

suppress_compilation

open Magnetism

namespace AlgMag

universe u v

variable {M : Type*} [AddCancelCommMonoid M] [DecidableEq M]
variable {R₀ : Type u} {A : Type v} [CommRing R₀] [CommRing A] [Algebra R₀ A]
variable (𝒜 : M → Submodule R₀ A) [GradedAlgebra 𝒜] (I : Ideal A)

/-- The image grading on `A ⧸ I`. -/
def homogQuotGrading (m : M) : Submodule R₀ (A ⧸ I) :=
  (𝒜 m).map (Ideal.Quotient.mkₐ R₀ I).toLinearMap

omit [AddCancelCommMonoid M] [DecidableEq M] [GradedAlgebra 𝒜] in
lemma mem_homogQuotGrading {m : M} {y : A ⧸ I} :
    y ∈ homogQuotGrading 𝒜 I m ↔ ∃ a ∈ 𝒜 m, Ideal.Quotient.mk I a = y := by
  simp [homogQuotGrading]

/-- An element of `⨆_{j ≠ i} 𝒜 j` has zero `i`-component. -/
lemma decompose_eq_zero_of_mem_iSup_ne {i : M} {b : A} (hb : b ∈ ⨆ (j) (_ : j ≠ i), 𝒜 j) :
    (DirectSum.decompose 𝒜 b i : A) = 0 := by
  refine Submodule.iSup_induction (fun j => ⨆ (_ : j ≠ i), 𝒜 j)
    (motive := fun b => (DirectSum.decompose 𝒜 b i : A) = 0) hb ?_ ?_ ?_
  · intro j x hx
    by_cases hj : j = i
    · subst hj
      simp only [ne_eq, not_true_eq_false, iSup_false, Submodule.mem_bot] at hx
      rw [hx, DirectSum.decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero]
    · rw [iSup_pos hj] at hx
      rw [DirectSum.decompose_of_mem_ne 𝒜 hx hj]
  · rw [DirectSum.decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero]
  · intro x y hx hy
    rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add, hx, hy, add_zero]

variable {I}

theorem isInternal_homogQuotGrading (hI : I.IsHomogeneous 𝒜) :
    DirectSum.IsInternal (homogQuotGrading 𝒜 I) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · rw [iSupIndep_def]
    intro i
    rw [Submodule.disjoint_def]
    intro y hy hy'
    obtain ⟨a, ha, rfl⟩ := (mem_homogQuotGrading 𝒜 I).1 hy
    have hmap : (⨆ (j) (_ : j ≠ i), homogQuotGrading 𝒜 I j) =
        (⨆ (j) (_ : j ≠ i), 𝒜 j).map (Ideal.Quotient.mkₐ R₀ I).toLinearMap := by
      simp only [homogQuotGrading, Submodule.map_iSup]
    rw [hmap] at hy'
    obtain ⟨b, hb, hab⟩ := hy'
    have hab' : a - b ∈ I := by
      rw [← Ideal.Quotient.eq]
      exact hab.symm
    have hcomp := hI i hab'
    rw [DirectSum.decompose_sub, DirectSum.sub_apply, Submodule.coe_sub,
      DirectSum.decompose_of_mem_same 𝒜 ha, decompose_eq_zero_of_mem_iSup_ne 𝒜 hb,
      sub_zero] at hcomp
    exact Ideal.Quotient.eq_zero_iff_mem.2 hcomp
  · rw [eq_top_iff]
    intro y _
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    have ha : a ∈ ⨆ m, 𝒜 m := by
      rw [(DirectSum.Decomposition.isInternal 𝒜).submodule_iSup_eq_top]; trivial
    have : (⨆ m, homogQuotGrading 𝒜 I m) = (⨆ m, 𝒜 m).map (Ideal.Quotient.mkₐ R₀ I).toLinearMap := by
      simp only [homogQuotGrading, Submodule.map_iSup]
    rw [this]
    exact ⟨a, ha, rfl⟩

/-- The quotient of a graded algebra by a homogeneous ideal is graded. -/
abbrev gradedAlgebraHomogQuot (hI : I.IsHomogeneous 𝒜) : GradedAlgebra (homogQuotGrading 𝒜 I) where
  one_mem := (mem_homogQuotGrading 𝒜 I).2 ⟨1, SetLike.one_mem_graded 𝒜, map_one _⟩
  mul_mem i j x y hx hy := by
    obtain ⟨a, ha, rfl⟩ := (mem_homogQuotGrading 𝒜 I).1 hx
    obtain ⟨b, hb, rfl⟩ := (mem_homogQuotGrading 𝒜 I).1 hy
    exact (mem_homogQuotGrading 𝒜 I).2 ⟨a * b, SetLike.mul_mem_graded ha hb, map_mul _ _ _⟩
  toDecomposition := (isInternal_homogQuotGrading 𝒜 hI).chooseDecomposition

omit [DecidableEq M] [GradedAlgebra 𝒜] in
/-- The magnet ideals of `A ⧸ I` are the images of those of `A`. -/
theorem magnetIdeal_homogQuotGrading (N : Magnet M) :
    magnetIdeal (homogQuotGrading 𝒜 I) N = (magnetIdeal 𝒜 N).map (Ideal.Quotient.mk I) := by
  rw [magnetIdeal, magnetIdeal, Ideal.map_span]
  congr 1
  ext y
  simp only [Set.mem_iUnion, SetLike.mem_coe, Set.mem_image, mem_homogQuotGrading, exists_prop]
  constructor
  · rintro ⟨m, hm, a, ha, rfl⟩
    exact ⟨a, ⟨m, hm, ha⟩, rfl⟩
  · rintro ⟨a, ⟨m, hm, ha⟩, rfl⟩
    exact ⟨m, hm, a, ha, rfl⟩

/-- **Attractors of a smooth homogeneous closed subscheme are smooth.** -/
theorem smooth_quotient_sup_magnetIdeal [IsNoetherianRing R₀] (hI : I.IsHomogeneous 𝒜)
    [Algebra.Smooth R₀ (A ⧸ I)] (N : Magnet M) :
    Algebra.Smooth R₀ (A ⧸ (I ⊔ magnetIdeal 𝒜 N)) := by
  let := gradedAlgebraHomogQuot 𝒜 hI
  have h := smooth_quotient_magnetIdeal (homogQuotGrading 𝒜 I) N
  have hmap : Ideal.map (Ideal.Quotient.mkₐ R₀ I) (magnetIdeal 𝒜 N) =
      Ideal.map (Ideal.Quotient.mk I) (magnetIdeal 𝒜 N) := by
    simp only [Ideal.map, Ideal.Quotient.mkₐ_eq_mk]
  rw [magnetIdeal_homogQuotGrading, ← hmap] at h
  have e := DoubleQuot.quotQuotEquivQuotSupₐ R₀ I (magnetIdeal 𝒜 N)
  exact Algebra.Smooth.of_equiv e

end AlgMag
