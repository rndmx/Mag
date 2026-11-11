/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartS5Graded
import AlgMag.ChartConclude

/-!
# Equivariant Artin approximation: "`f̃ ≡ f`, `r̃ ≡ r`"

Part of the proof of **Theorem 6.8 (ii)** (= Theorem A.2 (ii)) of Algebraic Magnetism (Mayeux,
Semigroup Forum 113 (2026)), through the specialization to `D(M)` of Alper–Hall–Rydh, Corollary 10.2.


`QRmap_congr`: maps `B₀ → R` congruent modulo `I` induce maps `Q_{B₀} → Q_R` congruent modulo `I Q_R`.
-/

open TensorProduct

universe u

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

namespace AlgMag.ChartS5

open ChartAlg

variable {M : Type*} [AddCommGroup M] [DecidableEq M] {ι : Type*} [Finite ι] (w : ι → M)
  {B₀ R : Type*} [CommRing B₀] [CommRing R] [Algebra (P0 w ℤ) B₀] [Algebra (P0 w ℤ) R]

/-- The congruence of the approximation step. -/
theorem QRmap_congr (g g' : B₀ →ₐ[P0 w ℤ] R) (I : Ideal R) (h : ∀ b, g b - g' b ∈ I) (q : QR w B₀) :
    QRmap w g q - QRmap w g' q ∈
      I.map (Algebra.TensorProduct.includeRight : R →ₐ[P0 w ℤ] QR w R) := by
  induction q using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    rw [map_add, map_add, add_sub_add_comm]
    exact add_mem ha hb
  | tmul p b =>
    rw [QRmap_tmul, QRmap_tmul]
    have e : p ⊗ₜ[P0 w ℤ] g b - p ⊗ₜ[P0 w ℤ] g' b =
        (p ⊗ₜ[P0 w ℤ] (1 : R)) * (Algebra.TensorProduct.includeRight : R →ₐ[P0 w ℤ] QR w R) (g b - g' b) := by
      rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
        TensorProduct.tmul_sub]
    rw [e]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (h b))

section Pres

variable {C : Type u} {M : Type u} [CommRing C] [AddCommGroup M] [DecidableEq M] {ι : Type u} [Finite ι]
  {𝒞 : M → AddSubgroup C} [GradedRing 𝒞] {m : Ideal C} {w : ι → M} {x : ι → C}

/-- **Coordinates**: `C = Q/(f)`, `f` homogeneous, `r` generators of the syzygies of `f`. -/
theorem exists_presentation (hx : ∀ i, x i ∈ 𝒞 (w i)) (hC : CompletePair 𝒞 m) :
    ∃ (s₁ t₁ : ℕ) (F : Fin s₁ → Qring w x m) (deg : Fin s₁ → M) (r : Fin t₁ → Fin s₁ → Qring w x m),
      Ideal.span (Set.range F) = RingHom.ker (Qmap hx hC) ∧ (∀ ℓ, qProj (deg ℓ) (F ℓ) = F ℓ) ∧
      Submodule.span (Qring w x m) (Set.range r) =
        LinearMap.ker (Fintype.linearCombination (Qring w x m) F) := by
  haveI : IsNoetherianRing (Qring w x m) := isNoetherianRing_Qring w x m
  haveI : IsNoetherianRing (P0hat w x m) := isNoetherianRing_P0hat w x m
  obtain ⟨s₁, F, deg, hd, hF⟩ := Qmap_ker_homogeneous hx hC
  obtain ⟨t₁, r, -, -, hr⟩ := ChartConclude.syzygies_homogeneous F deg hd
  exact ⟨s₁, t₁, F, deg, r, hF, hd, hr⟩

end Pres

end AlgMag.ChartS5

#print axioms AlgMag.ChartS5.QRmap_congr
#print axioms AlgMag.ChartS5.exists_presentation
