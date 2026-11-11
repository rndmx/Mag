/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartSection5

/-!
# Equivariant Artin approximation: the approximation step

Part of the proof of **Theorem 6.8 (ii)** (= Theorem A.2 (ii)) of Algebraic Magnetism (Mayeux,
Semigroup Forum 113 (2026)), through the specialization to `D(M)` of Alper–Hall–Rydh, Corollary 10.2.


`exists_artin_level`: `ArtinApproxFP` at `B₀ = R_t ⊆ P̂₀`, and `Spec Q_{A'}/(f̃)` lies in the site.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

namespace AlgMag.ChartS5

open ChartAlg

variable {C M : Type u} [CommRing C] [AddCommGroup M] [DecidableEq M] {ι : Type u} [Finite ι]
  {m : Ideal C} {w : ι → M} {x : ι → C}

/-- **Artin approximation step.** -/
theorem exists_artin_level (hArt : ChartConclude.ArtinApproxFP.{u}) [(p0 w x m).IsMaximal]
    (t : Finset (P0hat w x m)) (N : ℕ) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra (P0 w ℤ) A') (_ : Algebra.Etale (P0 w ℤ) A')
      (σ : A' →ₐ[P0 w ℤ] P0 w ℤ ⧸ p0 w x m ^ N) (θ : Rs w t →ₐ[P0 w ℤ] A'),
      ∀ b, σ (θ b) = AdicCompletion.evalₐ (p0 w x m) N (RsI w t b) := by
  haveI hZ : @Algebra.FiniteType ℤ (P0 w ℤ) _ _ (Ring.toIntAlgebra _) := by
    convert P0_finiteType w ℤ <;> first | rfl | exact Subsingleton.elim _ _ | exact (Subsingleton.elim _ _ : _ = _).heq
  haveI : Algebra.FiniteType (P0 w ℤ) (Rs w t) :=
    (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_adjoin_finset _)
  haveI : Algebra.FinitePresentation (P0 w ℤ) (Rs w t) :=
    Algebra.FinitePresentation.of_finiteType.1 inferInstance
  exact hArt (P0 w ℤ) (p0 w x m) (Rs w t) (RsI w t) N

/-- `Spec Q_{A'}/(f̃)` lies in the site. -/
theorem contains_Dq {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} [IsAffine S]
    {A' : Type u} [CommRing A'] [Algebra (P0 w ℤ) A'] [Algebra.FiniteType (P0 w ℤ) A'] {s₁ : ℕ}
    (F : Fin s₁ → QR w A') (ρ : RT (siteTop (B := B) (S := S) (hS := hS)) →+* Dq F) :
    B.Contains (Spec (.of (Dq F))) := by
  letI := ρ.toAlgebra
  haveI : Algebra.FiniteType ℤ (QR w A') := finiteType_QR_int w _
  haveI : Algebra.FiniteType ℤ (Dq F) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ (Ideal.span (Set.range F)))
      Ideal.Quotient.mk_surjective
  haveI : Algebra.FiniteType (RT (siteTop (B := B) (S := S) (hS := hS))) (Dq F) :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ _ _
  exact contains_ft (RT (siteTop (B := B) (S := S) (hS := hS))) (Dq F) (contains_RT _)

/-- **Coordinates**, indexed in the universe of `C` (so that `P̂₀` is in the universe of the site). -/
theorem exists_coordinates {𝒞 : M → AddSubgroup C} [GradedRing 𝒞] [IsNoetherianRing C]
    (hm : m.IsHomogeneous 𝒞) (T : Finset C) (hT : ∀ t ∈ T, ∃ d, t ∈ 𝒞 d)
    (hgen : ∀ c : C, ∃ p ∈ Algebra.adjoin ℤ (T : Set C), c - p ∈ m) :
    ∃ (n : ℕ) (x : ULift.{u} (Fin n) → C) (w : ULift.{u} (Fin n) → M), (∀ i, x i ∈ 𝒞 (w i)) ∧
      ∀ (c : C) (k : ℕ), ∃ p : MvPolynomial (ULift.{u} (Fin n)) ℤ,
        c - MvPolynomial.aeval x p ∈ m ^ k := by
  obtain ⟨n, x, w, hx, happ⟩ := graded_coordinates hm T hT hgen
  refine ⟨n, fun i => x i.down, fun i => w i.down, fun i => hx _, fun c k => ?_⟩
  obtain ⟨p, hp⟩ := happ c k
  refine ⟨MvPolynomial.rename ULift.up p, ?_⟩
  rwa [MvPolynomial.aeval_rename]

end AlgMag.ChartS5

#print axioms AlgMag.ChartS5.exists_artin_level
#print axioms AlgMag.ChartS5.contains_Dq
#print axioms AlgMag.ChartS5.exists_coordinates
