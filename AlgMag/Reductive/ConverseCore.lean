/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.TorusMeetsNormal
import AlgMag.Reductive.NormalInTorus
import AlgMag.Reductive.LieTrivialSubgroup
import AlgMag.Reductive.RootSpaceDim
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Basic

/-!
# Core of the converse: reduction to one root

For the converse of the reductivity criterion (equivalence.tex Theorem 5.1). Let `K` be
algebraically closed, `ρ : A → K[X]` onto with `Z_G(T) = T` (condition (i)), and `U = V(I)` a
normal, smooth, connected closed subgroup with unipotent geometric points. Then
* `U ∩ T = e` (`sup_magnetHopfIdeal_bot_eq_augmentation`);
* if `Lie U ⊆ 𝔤_0`, then `U ⊆ Z_G(T) = T`, so `U = U ∩ T = e`;
* otherwise `Lie U` contains a nonzero vector of a root space `𝔤_α`.

So `I` is the augmentation ideal as soon as the root case is excluded (`hroot`), which is the
rank-one endgame (`U_α ⊆ U`, `U_{-α} ⊆ U`, the Weyl element lies in `U · T`, contradiction).
-/

suppress_compilation

open Magnetism TauCeti

namespace AlgMag.Reductive

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {A : Type u} [CommRing A] [HopfAlgebra K A]
  [Algebra.FiniteType K A] {X : Type u} [CommGroup X] [DecidableEq X]

omit [IsAlgClosed K] [Algebra.FiniteType K A] in
/-- A nonzero root-space vector has a root as weight. -/
theorem mem_roots_of_mem_rootSpace [Module.Finite K (Bialgebra.CotangentSpace K A)]
    (ρ : A →ₐc[K] MonoidAlgebra K X) {α : Additive X} (hα : α ≠ 0)
    {e : Derivation K A (Bialgebra.CounitAlgebra K A K)} (he : e ∈ rootSpace ρ α) (he0 : e ≠ 0) :
    α ∈ roots ρ := by
  refine ⟨fun h => hα (Additive.toMul.injective (by rw [h]; rfl)), fun hbot => he0 ?_⟩
  obtain ⟨x, rfl⟩ := (Derivation.cotangentLinearEquiv (R := K) (A := A) (B := K)).surjective e
  have hx := (mem_adjointWeightSpace_iff_mem_rootSpace (π := ρ) x).2 he
  rw [hbot, Submodule.mem_bot] at hx
  rw [hx, map_zero]

/-- **Core of the converse, modulo the root case.** -/
theorem eq_augmentation_of_condI_of_root (ρ : A →ₐc[K] MonoidAlgebra K X)
    (hρ : Function.Surjective ρ)
    (hI1 : magnetIdeal (torusGrading ρ) ⊥ = RingHom.ker ρ.toAlgHom)
    {I : HopfIdeal K A} (hI : I.IsNormal) [Algebra.Smooth K (A ⧸ I.toIdeal)]
    [ConnectedSpace (PrimeSpectrum (A ⧸ I.toIdeal))]
    (hu : ∀ g : WithConv ((A ⧸ I.toIdeal) →ₐ[K] AlgebraicClosure K),
      HopfAlgebra.IsUnipotentPoint g)
    (hroot : I ⊔ magnetHopfIdeal ρ ⊥ = HopfIdeal.augmentation K A →
      ∀ α ∈ roots ρ, ∀ e ∈ I.lieSubalgebra (B := K), e ∈ rootSpace ρ α → e ≠ 0 → False) :
    I = HopfIdeal.augmentation K A := by
  have hUT := sup_magnetHopfIdeal_bot_eq_augmentation ρ hρ hI1 hI hu
  by_cases hall : ∀ d ∈ I.lieSubalgebra (B := K), d ∈ rootSpace ρ 0
  · have hle := magnetHopfIdeal_bot_le_of_lie_le ρ hI hall
    rw [← hUT, sup_eq_left.2 hle]
  · push Not at hall
    obtain ⟨d, hd, hd0⟩ := hall
    obtain ⟨α, hα, e, he, heα, he0⟩ := exists_rootSpace_lie_of_isNormal_of_notMem ρ hI hd hd0
    exact (hroot hUT α (mem_roots_of_mem_rootSpace ρ hα heα he0) e he heα he0).elim

/-- **Core of the converse, with the hypotheses in the form of Tau Ceti's reductivity
definition** (`I` a Hopf ideal of the bundled `A`, its quotient object geometrically connected
and smooth unipotent), modulo the root case. -/
theorem eq_augmentation_of_quotient_props_of_root (ρ : A →ₐc[K] MonoidAlgebra K X)
    (hρ : Function.Surjective ρ)
    (hI1 : magnetIdeal (torusGrading ρ) ⊥ = RingHom.ker ρ.toAlgHom)
    (I : HopfIdeal K (FiniteTypeCommHopfAlgCat.of K A)) (hI : I.IsNormal)
    (hc : geometricallyConnectedCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of K A) I).obj)
    (hu : smoothUnipotentCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of K A) I))
    (hroot : I ⊔ magnetHopfIdeal ρ ⊥ = HopfIdeal.augmentation K A →
      ∀ α ∈ roots ρ, ∀ e ∈ I.lieSubalgebra (B := K), e ∈ rootSpace ρ α → e ≠ 0 → False) :
    I = HopfIdeal.augmentation K (FiniteTypeCommHopfAlgCat.of K A) := by
  obtain ⟨hsm, hup⟩ := (smoothUnipotentCommHopfAlgProperty_iff K _).1 hu
  have : Algebra.Smooth K (A ⧸ I.toIdeal) := hsm
  have : ConnectedSpace (PrimeSpectrum (A ⧸ I.toIdeal)) :=
    connectedSpace_of_geometricallyConnected K (A ⧸ I.toIdeal) hc
  exact eq_augmentation_of_condI_of_root ρ hρ hI1 (I := I) hI hup hroot

end AlgMag.Reductive
