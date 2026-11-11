/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.StepDBasePair
import AlgMag.Reductive.TorusMeetsNormal

/-!
# `UnipInTorus` (proved)

A smooth closed subgroup `V(N) ⊆ T = D(X)` with unipotent geometric points is trivial, over
`k = k̄`. Same argument as `sup_magnetHopfIdeal_bot_eq_augmentation` (TorusMeetsNormal), with
`W = N` (no normality needed, since `ker π ≤ N`):
* `H/N` is a quotient of `k[X]`, so the images of characters are group-like;
* a unipotent geometric point kills them (`eq_one_of_groupLike`), so it is the counit;
* `H/N` reduced with a unique rational point ⇒ trivial (`ker_counit_eq_bot_of_unique_point`).
-/

suppress_compilation

open Magnetism TauCeti TensorProduct

namespace AlgMag.Reductive.UnipInTorusProof

open AlgMag.Reductive

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {A : Type u} [CommRing A] [HopfAlgebra K A]
  [Algebra.FiniteType K A] {X : Type u} [CommGroup X] [DecidableEq X]

/-- Core: `ker ρ ≤ I`, `H/I` smooth with unipotent geometric points ⇒ `I = augmentation`. -/
theorem eq_augmentation_of_ker_le (ρ : A →ₐc[K] MonoidAlgebra K X)
    (hρ : Function.Surjective ρ) {W : HopfIdeal K A} (hkerW : RingHom.ker ρ.toAlgHom ≤ W.toIdeal)
    [Algebra.Smooth K (A ⧸ W.toIdeal)]
    (hu : ∀ g : WithConv ((A ⧸ W.toIdeal) →ₐ[K] AlgebraicClosure K),
      HopfAlgebra.IsUnipotentPoint g) :
    W = HopfIdeal.augmentation K A := by
  have hred : IsReduced (A ⧸ W.toIdeal) := isReduced_of_smooth K _
  let e := Ideal.quotientKerAlgEquivOfSurjective (R₁ := K) (f := ρ.toAlgHom) hρ
  let f : MonoidAlgebra K X →ₐ[K] A ⧸ W.toIdeal :=
    (Ideal.Quotient.factorₐ K hkerW).comp (e.symm : MonoidAlgebra K X →ₐ[K] _)
  have hf : ∀ x : A, f (ρ x) = Ideal.Quotient.mk W.toIdeal x := by
    intro x
    have : e.symm (ρ x) = Ideal.Quotient.mk (RingHom.ker ρ.toAlgHom) x := by
      apply e.injective
      rw [AlgEquiv.apply_symm_apply]
      rfl
    simp only [f, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, this]
    rfl
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨ρ x, hf x⟩
  have hgl : ∀ χ : X, Coalgebra.comul (R := K) (f (MonoidAlgebra.single χ 1)) =
      f (MonoidAlgebra.single χ 1) ⊗ₜ f (MonoidAlgebra.single χ 1) ∧
      Coalgebra.counit (R := K) (f (MonoidAlgebra.single χ 1)) = 1 := by
    intro χ
    obtain ⟨a, ha⟩ := hρ (MonoidAlgebra.single χ 1)
    have hmk : f (MonoidAlgebra.single χ 1) = Ideal.Quotient.mk W.toIdeal a := by rw [← ha, hf]
    rw [hmk]
    constructor
    · rw [Bialgebra.Quotient.comul_mk]
      have h1 : TensorProduct.map (Ideal.Quotient.mkₐ K W.toIdeal).toLinearMap
          (Ideal.Quotient.mkₐ K W.toIdeal).toLinearMap =
          TensorProduct.map f.toLinearMap f.toLinearMap ∘ₗ
            TensorProduct.map (ρ : A →ₐ[K] MonoidAlgebra K X).toLinearMap
              (ρ : A →ₐ[K] MonoidAlgebra K X).toLinearMap := by
        rw [← TensorProduct.map_comp]
        congr 1 <;> ext x <;> simp [hf]
      have h2 := CoalgHomClass.map_comp_comul_apply ρ a
      rw [h1, LinearMap.comp_apply]
      erw [h2]
      rw [ha, comul_single_one, TensorProduct.map_tmul]
      simp only [AlgHom.toLinearMap_apply]
      rw [hmk]
    · rw [Bialgebra.Quotient.counit_mk, ← CoalgHomClass.counit_comp_apply ρ a, ha,
        MonoidAlgebra.counit_single]
      rfl
  let q := (CommHopfAlgCat.quotientMapOfLe (CommHopfAlgCat.of K A) (le_refl W)).hom
  have hqs : Function.Surjective q :=
    CommHopfAlgCat.quotientMapOfLe_surjective (CommHopfAlgCat.of K A) (le_refl W)
  have hpt : ∀ g : (A ⧸ W.toIdeal) →ₐ[K] AlgebraicClosure K,
      g = (Algebra.ofId K (AlgebraicClosure K)).comp (Bialgebra.counitAlgHom K _) := by
    intro g
    have h1 : ∀ χ : X, g (f (MonoidAlgebra.single χ 1)) = 1 := fun χ =>
      eq_one_of_groupLike q hqs (hgl χ).1 (hgl χ).2 g (hu _)
    have hcomp : g.comp f =
        ((Algebra.ofId K (AlgebraicClosure K)).comp (Bialgebra.counitAlgHom K _)).comp f := by
      refine MonoidAlgebra.algHom_ext (fun χ => ?_) (Subsingleton.elim _ _)
      simp only [AlgHom.comp_apply, h1, Bialgebra.counitAlgHom_apply, (hgl χ).2, map_one]
    ext y
    obtain ⟨x, rfl⟩ := hfs y
    exact AlgHom.congr_fun hcomp x
  have huniq : ∀ φ : (A ⧸ W.toIdeal) →ₐ[K] K, φ = Bialgebra.counitAlgHom K _ := by
    intro φ
    have h := hpt ((Algebra.ofId K (AlgebraicClosure K)).comp φ)
    ext y
    have hy := AlgHom.congr_fun h y
    simp only [AlgHom.comp_apply, Algebra.ofId_apply] at hy
    exact (algebraMap K (AlgebraicClosure K)).injective hy
  have hker := ker_counit_eq_bot_of_unique_point huniq
  ext x
  constructor
  · intro hx
    exact HopfIdeal.le_augmentation K A W hx
  · intro hx
    have hx0 := (HopfIdeal.mem_augmentation K A).1 hx
    have hmem : Ideal.Quotient.mk W.toIdeal x ∈
        RingHom.ker (Bialgebra.counitAlgHom K (A ⧸ W.toIdeal)) := by
      rw [RingHom.mem_ker, Bialgebra.counitAlgHom_apply, Bialgebra.Quotient.counit_mk]
      exact hx0
    rw [hker, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hmem
    exact hmem

/-- **`UnipInTorus` for `T = ker π`** (proved), over `k = k̄`. -/
theorem unipInTorus (π : A →ₐc[K] MonoidAlgebra K X) (hπ : Function.Surjective π) :
    StepDBasePair.UnipInTorus (HopfIdeal.kerOfSurjective π hπ) := by
  intro N hTN _ hu
  obtain ⟨hsm, hup⟩ := (smoothUnipotentCommHopfAlgProperty_iff K _).1 hu
  have : Algebra.Smooth K (A ⧸ N.toIdeal) := hsm
  have hk : RingHom.ker π.toAlgHom ≤ N.toIdeal := hTN
  exact (eq_augmentation_of_ker_le π hπ hk hup).ge

end AlgMag.Reductive.UnipInTorusProof

#print axioms AlgMag.Reductive.UnipInTorusProof.unipInTorus
