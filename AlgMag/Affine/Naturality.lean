/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Affine.Representability

/-!
# Naturality of the identification `X^N ≃ Spec (A / J_N)`

Theorem 3.20 asserts that `X^N` is *represented* by `Spec (A / J_N)`, so the bijection
of `Magnetism.attractorEquiv` must be natural in the test algebra `C`. This file
supplies the missing functoriality and proves the naturality square.

Mathlib has no "change of coefficients" map for `AddMonoidAlgebra`, so `magnetMap`
is built here out of `AddMonoidAlgebra.liftNCAlgHom`.
-/

suppress_compilation

namespace Magnetism

open DirectSum

open scoped Classical

variable {M : Type*} [AddCommMonoid M] [DecidableEq M]
variable {R₀ A : Type*} [CommRing R₀] [CommRing A] [Algebra R₀ A]
variable (𝒜 : M → Submodule R₀ A) [GradedAlgebra 𝒜] (N : Magnet M)
variable {C C' : Type*} [CommRing C] [Algebra R₀ C] [CommRing C'] [Algebra R₀ C']

variable {𝒜}

/-- Change of coefficients `C[N] → C'[N]` along a `R₀`-algebra map `g : C → C'`. -/
def magnetMap (g : C →ₐ[R₀] C') :
    AddMonoidAlgebra C N →ₐ[R₀] AddMonoidAlgebra C' N :=
  AddMonoidAlgebra.mapAlgHom N g

@[simp] lemma magnetMap_single (g : C →ₐ[R₀] C') (n : N) (c : C) :
    magnetMap N g (AddMonoidAlgebra.single n c) = AddMonoidAlgebra.single n (g c) := by
  simp [magnetMap]

/-- Push a point of the attractor forward along `g : C → C'`. -/
def Attractor.map (g : C →ₐ[R₀] C') (f : Attractor 𝒜 N C) : Attractor 𝒜 N C' where
  __ := (magnetMap N g).comp f.toAlgHom
  map_mem' {m a} ha := by
    show magnetMap N g (f a) ∈ magnetGrading N C' m
    by_cases h : m ∈ N
    · obtain ⟨c, hc⟩ := exists_single_of_mem_magnetGrading h (f.map_mem ha)
      rw [hc, magnetMap_single]
      exact single_mem_magnetGrading _ _
    · rw [attractor_apply_eq_zero_of_notMem f h ha, map_zero]
      exact zero_mem _

@[simp] lemma Attractor.map_apply (g : C →ₐ[R₀] C') (f : Attractor 𝒜 N C) (a : A) :
    Attractor.map N g f a = magnetMap N g (f a) := rfl

variable (𝒜)

/-- **Naturality of Theorem 3.20.** The bijection
`Hom_{R₀}(A / J_N, C) ≃ X^N(C)` is natural in the `R₀`-algebra `C`. -/
lemma attractorEquiv_naturality (g : C →ₐ[R₀] C')
    (F : (A ⧸ magnetIdeal 𝒜 N) →ₐ[R₀] C) :
    attractorEquiv 𝒜 N C' (g.comp F) = Attractor.map N g (attractorEquiv 𝒜 N C F) := by
  refine GradedAlgHom.ext fun a => ?_
  show thetaAlgHom 𝒜 N C' (g.comp F) a = magnetMap N g (thetaAlgHom 𝒜 N C F a)
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous m x =>
      rw [thetaAlgHom_apply_of_mem 𝒜 N C' (g.comp F) x.2,
        thetaAlgHom_apply_of_mem 𝒜 N C F x.2]
      by_cases h : m ∈ N
      · rw [thetaComponent_apply_of_mem (g.comp F) h, thetaComponent_apply_of_mem F h,
          magnetMap_single]
        rfl
      · rw [thetaComponent_apply_of_notMem (g.comp F) h,
          thetaComponent_apply_of_notMem F h, map_zero]
  | add a a' ha ha' => simp only [map_add] at ha ha' ⊢; rw [ha, ha']

end Magnetism
