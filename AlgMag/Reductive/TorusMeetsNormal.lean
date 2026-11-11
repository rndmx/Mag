/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.NormalAttractor
import AlgMag.Reductive.UnipotentGroupLike
import AlgMag.Reductive.UniquePointTrivial
import TauCeti.RingTheory.Smooth.GeometricallyReduced
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic

/-!
# A smooth normal subgroup with unipotent points meets `Z_G(T) = T` trivially

Let `K` be algebraically closed, `T = D(X) ⊆ G` with `Z_G(T) = T` (condition (i):
`J_⊥ = ker ρ`), and `U = V(I)` a smooth normal closed subgroup whose geometric points are
unipotent. Then `U ∩ T = U^T = V(I ⊔ J_⊥)` is trivial: `I ⊔ J_⊥` is the augmentation ideal.

* `U^T` is smooth (`smooth_quotient_sup_magnetIdeal_of_isNormal`), hence reduced;
* it is a quotient of `K[X]`, so the images `b_χ` of the characters are group-like;
* every geometric point `g` of `U^T` has `g ∘ q` unipotent on `U`, so `g b_χ = 1`
  (`eq_one_of_groupLike`), so `g` is the counit;
* a reduced finite-type bialgebra with a single rational point is trivial
  (`ker_counit_eq_bot_of_unique_point`).
-/

suppress_compilation

open Magnetism TauCeti TensorProduct

namespace AlgMag.Reductive

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {A : Type u} [CommRing A] [HopfAlgebra K A]
  [Algebra.FiniteType K A] {X : Type u} [CommGroup X] [DecidableEq X]

omit [IsAlgClosed K] [Algebra.FiniteType K A] [CommGroup X] [DecidableEq X] in
lemma comul_single_one (χ : X) :
    Coalgebra.comul (R := K) (MonoidAlgebra.single χ (1 : K)) =
      MonoidAlgebra.single χ 1 ⊗ₜ MonoidAlgebra.single χ 1 := by
  simp

/-- **`U ∩ T = e`** for a smooth normal subgroup `U = V(I)` with unipotent geometric points, when
`Z_G(T) = T`. -/
theorem sup_magnetHopfIdeal_bot_eq_augmentation (ρ : A →ₐc[K] MonoidAlgebra K X)
    (hρ : Function.Surjective ρ)
    (hI1 : magnetIdeal (torusGrading ρ) ⊥ = RingHom.ker ρ.toAlgHom)
    {I : HopfIdeal K A} (hI : I.IsNormal) [Algebra.Smooth K (A ⧸ I.toIdeal)]
    (hu : ∀ g : WithConv ((A ⧸ I.toIdeal) →ₐ[K] AlgebraicClosure K),
      HopfAlgebra.IsUnipotentPoint g) :
    I ⊔ magnetHopfIdeal ρ ⊥ = HopfIdeal.augmentation K A := by
  set W := I ⊔ magnetHopfIdeal ρ ⊥ with hW
  have hWI : W.toIdeal = I.toIdeal ⊔ magnetIdeal (torusGrading ρ) ⊥ := by
    rw [hW, HopfIdeal.sup_toIdeal, magnetHopfIdeal_toIdeal]
  have hsm : Algebra.Smooth K (A ⧸ W.toIdeal) := by
    rw [hWI]; exact smooth_quotient_sup_magnetIdeal_of_isNormal ρ hI ⊥
  have hred : IsReduced (A ⧸ W.toIdeal) := isReduced_of_smooth K _
  have hkerW : RingHom.ker ρ.toAlgHom ≤ W.toIdeal := by
    rw [hWI, ← hI1]; exact le_sup_right
  -- the factorization `f : K[X] → A ⧸ W` with `f ∘ ρ = mk`
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
  -- group-like images of the characters
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
  -- every geometric point of `A ⧸ W` is the counit
  let q := (CommHopfAlgCat.quotientMapOfLe (CommHopfAlgCat.of K A) (le_sup_left : I ≤ W)).hom
  have hqs : Function.Surjective q :=
    CommHopfAlgCat.quotientMapOfLe_surjective (CommHopfAlgCat.of K A) (le_sup_left : I ≤ W)
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

omit [IsAlgClosed K] [Algebra.FiniteType K A] in
/-- `U ∩ T = e` in the point form used by `eq_one_of_isNormalizingWith_of_mem`: a point killing
`I` and `ker ρ` is the unit. -/
theorem eq_one_of_kills_of_sup_eq (ρ : A →ₐc[K] MonoidAlgebra K X)
    (hI1 : magnetIdeal (torusGrading ρ) ⊥ = RingHom.ker ρ.toAlgHom) {I : HopfIdeal K A}
    (h : I ⊔ magnetHopfIdeal ρ ⊥ = HopfIdeal.augmentation K A)
    {B : Type u} [CommRing B] [Algebra K B] (g : WithConv (A →ₐ[K] B))
    (hgI : ∀ x ∈ I, g.ofConv x = 0) (hgT : ∀ x ∈ RingHom.ker ρ.toAlgHom, g.ofConv x = 0) :
    g = 1 := by
  have hkill : ∀ x ∈ (HopfIdeal.augmentation K A).toIdeal, g.ofConv x = 0 := by
    rw [← h, HopfIdeal.sup_toIdeal, magnetHopfIdeal_toIdeal, hI1]
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add, hgI a ha, hgT b hb, add_zero]
  apply WithConv.ext
  ext x
  have hx : x - algebraMap K A (Coalgebra.counit (R := K) x) ∈
      (HopfIdeal.augmentation K A).toIdeal := by
    rw [HopfIdeal.mem_toIdeal, HopfIdeal.mem_augmentation, map_sub, Algebra.algebraMap_eq_smul_one,
      map_smul, Bialgebra.counit_one, smul_eq_mul, mul_one, sub_self]
  have := hkill _ hx
  rw [map_sub, AlgHom.commutes, sub_eq_zero] at this
  rw [this]
  rfl

end AlgMag.Reductive
