/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec11Formal
import AlgMag.Affine.Naturality
import AlgMag.Reductive.AttractorSubgroup

/-!
# Smoothness of affine attractors (Corollary 11.10 of Algebraic Magnetism, ring form)

If `A` is an `M`-graded `R₀`-algebra which is formally smooth over `R₀`, then for every magnet `N`
the coordinate ring `A ⧸ J_N` of the attractor `X^N` is formally smooth over `R₀`. The proof is
Proposition 11.1 for `X → S` (`S = Spec R₀` with the trivial action): a point of `X^N` over a
first order thickening lifts by the equivariant lifting `AlgMag.exists_graded_lift`, and
Theorem 3.20 (`Magnetism.attractorEquiv`) translates points of `X^N` into maps out of `A ⧸ J_N`.

Over a Noetherian base, smoothness of `A` gives smoothness of `A ⧸ J_N`; in particular the
attractor `G^N` of a smooth affine group under a torus action is smooth.
-/

suppress_compilation

open Magnetism AlgMag.Deformations

namespace AlgMag

universe u v

section General

variable {M : Type*} [AddCancelCommMonoid M] [DecidableEq M]
variable {R₀ : Type u} {A : Type v} [CommRing R₀] [CommRing A] [Algebra R₀ A]
variable (𝒜 : M → Submodule R₀ A) [GradedAlgebra 𝒜] (N : Magnet M)

/-- **Corollary 11.10 of Algebraic Magnetism (affine, formal form).** If `X = Spec A` is formally
smooth over `S = Spec R₀`, so is its attractor `X^N = Spec (A ⧸ J_N)`. -/
theorem formallySmooth_quotient_magnetIdeal [Algebra.FormallySmooth R₀ A] :
    Algebra.FormallySmooth R₀ (A ⧸ magnetIdeal 𝒜 N) := by
  refine Algebra.FormallySmooth.of_comp_surjective fun B _ _ I hI f => ?_
  let φ : B →ₐ[R₀] B ⧸ I := Ideal.Quotient.mkₐ R₀ I
  have hφ : Function.Surjective φ := Ideal.Quotient.mk_surjective
  have hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0 := by
    intro x y hx hy
    have hx' : x ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hx
    have hy' : y ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hy
    have : x * y ∈ I ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hx' hy'
    rw [hI] at this
    exact (Ideal.mem_bot).mp this
  let α : Attractor 𝒜 N (B ⧸ I) := attractorEquiv 𝒜 N (B ⧸ I) f
  let ρ := AddMonoidAlgebra.mapRingHom N (φ : B →+* B ⧸ I)
  have hgr : ∀ m x, x ∈ magnetGrading N B m → ρ x ∈ magnetGrading N (B ⧸ I) m :=
    fun m x hx => map_mem_magnetGrading _ hx
  obtain ⟨γ, h₁, h₂, h₃⟩ := exists_graded_lift (𝒜 := 𝒜) (ℰ := magnetGrading N B) (B := R₀) ρ
    (mapRingHom_surjective _ hφ)
    (magnetAlgebra_mul_eq_zero _ hq)
    (fun k x hx => by
      rw [map_proj_of_graded (magnetGrading N B) (magnetGrading N (B ⧸ I)) ρ hgr, hx, map_zero])
    (α.toAlgHom : A →+* _) (algebraMap R₀ (AddMonoidAlgebra B N))
    (fun r => by
      change ρ (algebraMap R₀ _ r) = α (algebraMap R₀ A r)
      rw [show α (algebraMap R₀ A r) = algebraMap R₀ _ r from α.toAlgHom.commutes r]
      exact map_algebraMap_reduce (N := N) φ r)
    (fun m a ha => exists_homogeneous_lift _ hφ (α.map_mem ha))
    (fun b => AddSubmonoid.subset_closure
      ⟨0, SetLike.algebraMap_mem_graded 𝒜 b, algebraMap_mem_magnetGrading b⟩)
  let γ' : Attractor 𝒜 N B :=
    { toAlgHom := { γ with commutes' := h₂ }, map_mem' := fun {m a} ha => h₃ m a ha }
  refine ⟨(attractorEquiv 𝒜 N B).symm γ', ?_⟩
  apply (attractorEquiv 𝒜 N (B ⧸ I)).injective
  rw [attractorEquiv_naturality, Equiv.apply_symm_apply]
  refine GradedAlgHom.ext fun a => ?_
  rw [Attractor.map_apply]
  exact h₁ a

/-- **Corollary 11.10 of Algebraic Magnetism (affine).** Over a Noetherian ring, if `X = Spec A`
is smooth then so is its attractor `X^N = Spec (A ⧸ J_N)`. -/
theorem smooth_quotient_magnetIdeal [IsNoetherianRing R₀] [Algebra.Smooth R₀ A] :
    Algebra.Smooth R₀ (A ⧸ magnetIdeal 𝒜 N) := by
  have := formallySmooth_quotient_magnetIdeal 𝒜 N
  exact ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

end General

namespace Reductive

variable {R : Type u} {H : Type v} {X : Type*}
variable [CommRing R] [CommRing H] [HopfAlgebra R H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[R] MonoidAlgebra R X)

/-- **The attractor `G^N` of a smooth affine group is smooth** (Corollary 11.10 of Algebraic
Magnetism, for the action of `D(X)` on `G = Spec H`), over a Noetherian ring. -/
theorem smooth_quotient_magnetHopfIdeal [IsNoetherianRing R] [Algebra.Smooth R H]
    (N : Magnet (Additive X)) : Algebra.Smooth R (H ⧸ (magnetHopfIdeal π N).toIdeal) := by
  rw [magnetHopfIdeal_toIdeal]
  exact smooth_quotient_magnetIdeal (torusGrading π) N

end Reductive

end AlgMag
