/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
-/
import AlgMag.Sec12PrintedRing
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis

/-!
# (F2) graded Nakayama for smooth connected graded algebras

`exists_mvPolynomial_equiv_of_graded_smooth'` is the statement of
`AlgMag.Reductive.exists_mvPolynomial_equiv_of_graded_smooth` (in `TorusConjDyn.lean`) with the
extra hypothesis `[Nontrivial A]`. Without it the statement is false: `A = 0` satisfies all the
hypotheses (`𝒜 n = 0`, and `𝒜 0 = 0 = range`), but no `aeval x : k[X] → 0` is bijective; see
`not_bijective_of_subsingleton`.

Proof: derived from Theorem 12.4 (`AlgMag.Sec12Printed`, ring form) with `A₀ = k`, `B = A`,
`π` the projection to degree `0`: `Sym_k(I/I²) ≅ A` via a graded section `s : I/I² → A`; choose
a basis of `I/I²` made of classes of homogeneous elements of positive degree.
-/

universe u

open AlgMag.Sec12Printed

namespace AlgMag.Reductive.GradedNakayama

variable {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]
  (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]

lemma exists_proj0 (h0 : 𝒜 0 = LinearMap.range (Algebra.linearMap k A)) (a : A) :
    ∃ c : k, algebraMap k A c = GradedRing.projZeroRingHom 𝒜 a := by
  have : (GradedRing.projZeroRingHom 𝒜 a) ∈ 𝒜 0 := SetLike.coe_mem _
  rw [h0] at this
  obtain ⟨c, hc⟩ := this
  exact ⟨c, hc⟩

/-- The augmentation `A → k`, projection to degree `0`. -/
noncomputable def aug [Nontrivial A] (h0 : 𝒜 0 = LinearMap.range (Algebra.linearMap k A)) :
    A →ₐ[k] k :=
  have inj : Function.Injective (algebraMap k A) := (algebraMap k A).injective
  have key : ∀ a, algebraMap k A (Classical.choose (exists_proj0 𝒜 h0 a)) =
      GradedRing.projZeroRingHom 𝒜 a := fun a => Classical.choose_spec (exists_proj0 𝒜 h0 a)
  { toFun := fun a => Classical.choose (exists_proj0 𝒜 h0 a)
    map_one' := inj (by rw [key, map_one, map_one])
    map_mul' := fun a b => inj (by rw [key, map_mul, map_mul, key, key])
    map_zero' := inj (by rw [key, map_zero, map_zero])
    map_add' := fun a b => inj (by rw [key, map_add, map_add, key, key])
    commutes' := fun c => inj (by
      rw [key]
      change (DirectSum.decompose 𝒜 (algebraMap k A c) 0 : A) = _
      rw [DirectSum.decompose_of_mem_same 𝒜 (SetLike.algebraMap_mem_graded 𝒜 c)]; rfl) }

lemma algebraMap_aug [Nontrivial A] (h0 : 𝒜 0 = LinearMap.range (Algebra.linearMap k A)) (a : A) :
    algebraMap k A (aug 𝒜 h0 a) = (DirectSum.decompose 𝒜 a 0 : A) :=
  Classical.choose_spec (exists_proj0 𝒜 h0 a)

/-- The grading reindexed by `ULift ℕ : Type u` (Theorem 12.4 needs the index in `Type u`). -/
def up (i : ULift.{u} ℕ) : Submodule k A := 𝒜 i.down

instance : SetLike.GradedMonoid (up 𝒜) where
  one_mem := SetLike.GradedOne.one_mem (A := 𝒜)
  mul_mem i j _ _ ha hb := SetLike.GradedMul.mul_mem (A := 𝒜) (i := i.down) (j := j.down) ha hb

lemma up_isInternal : DirectSum.IsInternal (up 𝒜) := by
  have h := DirectSum.Decomposition.isInternal 𝒜
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at h ⊢
  refine ⟨h.1.comp ULift.down_injective, ?_⟩
  rw [← h.2]
  exact Equiv.ulift.iSup_comp (g := 𝒜)

noncomputable instance : GradedAlgebra (up 𝒜) :=
  { (inferInstance : SetLike.GradedMonoid (up 𝒜)) with
    toDecomposition := (up_isInternal 𝒜).chooseDecomposition }

lemma isAug [Nontrivial A] (h0 : 𝒜 0 = LinearMap.range (Algebra.linearMap k A)) :
    IsAug (up 𝒜) (aug 𝒜 h0) (fun y : ULift.{u} ℕ => y.down) where
  hw y _ _ _ h := ULift.ext _ _ h
  hadd _ _ _ _ _ _ _ _ := rfl
  hπ y hy b hb := (algebraMap k A).injective (by
    have hy' : y.down ≠ 0 := fun h => hy (ULift.ext _ _ h)
    rw [algebraMap_aug, DirectSum.decompose_of_mem_ne 𝒜 hb hy', map_zero])
  h0 b hb := by rw [algebraMap_aug, DirectSum.decompose_of_mem_same 𝒜 (show b ∈ 𝒜 0 from hb)]

/-- **(F2)**, statement of `AlgMag.Reductive.exists_mvPolynomial_equiv_of_graded_smooth` plus
`[Nontrivial A]` (necessary). -/
theorem exists_mvPolynomial_equiv_of_graded_smooth' {k : Type u} [Field k] {A : Type u}
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [Algebra.Smooth k A] [Nontrivial A]
    (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]
    (h0 : 𝒜 0 = LinearMap.range (Algebra.linearMap k A)) :
    ∃ (n : ℕ) (x : Fin n → A) (d : Fin n → ℕ), (∀ i, 0 < d i ∧ x i ∈ 𝒜 (d i)) ∧
      Function.Bijective (MvPolynomial.aeval (R := k) x) := by
  classical
  set π := aug 𝒜 h0
  have H := isAug 𝒜 h0
  have := projective_cotangent π
  have hfin := finite_cotangent π
  obtain ⟨s, hts, hπs, hg⟩ := exists_section H
  have hinj := phi_injective π hπs hts
  have hsurj := phi_surjective H hts hπs hg
  -- spanning set of classes of homogeneous elements of positive degree
  let S : Set (Conormal π) := {p | ∃ y : ULift.{u} ℕ, y ≠ 0 ∧ ∃ b ∈ up 𝒜 y, tMap π b = p}
  have hspan : Submodule.span k S = ⊤ := by
    refine eq_top_iff.2 fun p _ => ?_
    obtain ⟨a, rfl⟩ := tMap_surjective π p
    rw [← DirectSum.sum_support_decompose (up 𝒜) a, map_sum]
    refine Submodule.sum_mem _ fun y _ => ?_
    by_cases hy : y = 0
    · subst hy
      rw [tMap_of_zero H (SetLike.coe_mem _)]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨y, hy, _, SetLike.coe_mem _, rfl⟩
  obtain ⟨T, hTS, hTspan, hTli⟩ := exists_linearIndependent k S
  let bT : Module.Basis T k (Conormal π) :=
    Module.Basis.mk hTli (by rw [Subtype.range_coe, hTspan, hspan])
  have : Finite T := Module.Finite.finite_basis bT
  let _ : Fintype T := Fintype.ofFinite T
  let bas := bT.reindex (Fintype.equivFin T)
  have hbS : ∀ i, bas i ∈ S := fun i => by
    simp only [bas, Module.Basis.reindex_apply, bT, Module.Basis.mk_apply]
    exact hTS (Subtype.prop _)
  choose y hy b hb htb using hbS
  refine ⟨Fintype.card T, fun i => s (bas i), fun i => (y i).down,
    fun i => ⟨Nat.pos_of_ne_zero fun h => hy i (ULift.ext _ _ h), ?_⟩, ?_⟩
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

/-- The `[Nontrivial A]` hypothesis is necessary. -/
theorem not_bijective_of_subsingleton {k : Type u} [Field k] {A : Type u} [CommRing A]
    [Algebra k A] [Subsingleton A] {n : ℕ} (x : Fin n → A) :
    ¬ Function.Bijective (MvPolynomial.aeval (R := k) x) := fun h =>
  zero_ne_one (h.1 (Subsingleton.elim (MvPolynomial.aeval (R := k) x 0)
    (MvPolynomial.aeval (R := k) x 1)))

#print axioms exists_mvPolynomial_equiv_of_graded_smooth'

end AlgMag.Reductive.GradedNakayama
