/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartS5Level

/-!
# Chart lemma, Artin approximation step: the orbit in `W`

Part of the proof of the equivariant étale chart lemma for `D(M)`-actions at a closed point (local
structure in the sense of Alper–Hall–Rydh), used for **Theorem 6.8** of Algebraic Magnetism.

For `A'` a `P₀`-algebra with `σ : A' → P₀/𝔭₀^N`, `N ≥ 1`, the graded ring map
`Λ : Q_{A'} → C/m` (`W/(p') = C/p̂₀C` "has quotient `k[Z₀]`").
-/

open DirectSum TensorProduct

universe u

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

namespace AlgMag.ChartS5

open ChartAlg

variable {C M : Type u} [CommRing C] [AddCommGroup M] [DecidableEq M] {ι : Type u} [Finite ι]
  {𝒞 : M → AddSubgroup C} [GradedRing 𝒞] {m : Ideal C} {w : ι → M} {x : ι → C}
  (hx : ∀ i, x i ∈ 𝒞 (w i)) (hC : CompletePair 𝒞 m)

/-- `P₀/𝔭₀^N → C/m`, for `N ≥ 1`. -/
noncomputable def p0ToCm {N : ℕ} (hN : 1 ≤ N) : P0 w ℤ ⧸ p0 w x m ^ N →+* C ⧸ m :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk m).comp (phi0 w x)) (fun a ha => by
    have h1 : phi0 w x a ∈ m ^ N := phi0_pow_mem ha
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_le_self (by omega) h1))

/-- `mk ∘ φ̂ = (P₀/𝔭₀^N → C/m) ∘ eval_N`. -/
lemma mk_phiHat {N : ℕ} (hN : 1 ≤ N) (y : P0hat w x m) :
    Ideal.Quotient.mk m (phiHat hx hC y) = p0ToCm hN (AdicCompletion.evalₐ (p0 w x m) N y) := by
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (p0 w x m) N y)
  rw [← hb]
  have h1 := (phiHat_isLim hx hC y).2 N b hb.symm
  exact Ideal.Quotient.eq.2 (Ideal.pow_le_self (by omega) h1)

variable {N : ℕ} (hN : 1 ≤ N) {A' : Type u} [CommRing A'] [Algebra (P0 w ℤ) A']
  (σ : A' →ₐ[P0 w ℤ] P0 w ℤ ⧸ p0 w x m ^ N)

/-- `Λ : Q_{A'} → C/m`. -/
noncomputable def Lam : QR w A' →+* C ⧸ m :=
  letI alg : Algebra (P0 w ℤ) (C ⧸ m) := ((Ideal.Quotient.mk m).comp (phi0 w x)).toAlgebra
  let g₁ : MvPolynomial ι ℤ →ₐ[P0 w ℤ] C ⧸ m :=
    { (Ideal.Quotient.mk m).comp (MvPolynomial.aeval x : MvPolynomial ι ℤ →ₐ[ℤ] C).toRingHom with
      commutes' := fun _ => rfl }
  let g₂ : A' →ₐ[P0 w ℤ] C ⧸ m :=
    { (p0ToCm hN).comp σ.toRingHom with
      commutes' := fun a => by
        have := σ.commutes a
        change p0ToCm hN (σ (algebraMap _ _ a)) = _
        rw [this]
        rfl }
  (Algebra.TensorProduct.productMap g₁ g₂).toRingHom

@[simp] lemma Lam_tmul (p : MvPolynomial ι ℤ) (a : A') :
    Lam hN σ (p ⊗ₜ a) =
      Ideal.Quotient.mk m (MvPolynomial.aeval x p) * p0ToCm hN (σ a) := by
  letI alg : Algebra (P0 w ℤ) (C ⧸ m) := ((Ideal.Quotient.mk m).comp (phi0 w x)).toAlgebra
  simp [Lam, Algebra.TensorProduct.productMap_apply_tmul]

/-- `Λ` on `Q_{R_t}`-classes is `Q → C → C/m`, when `σ θ = eval_N`. -/
lemma Lam_QRmap {B₀ : Type u} [CommRing B₀] [Algebra (P0 w ℤ) B₀] (θ : B₀ →ₐ[P0 w ℤ] A')
    (h : B₀ →ₐ[P0 w ℤ] P0hat w x m) (hθ : ∀ b, σ (θ b) = AdicCompletion.evalₐ (p0 w x m) N (h b))
    (q : QR w B₀) :
    Lam hN σ (QRmap w θ q) = Ideal.Quotient.mk m (Qmap hx hC (QRmap w h q)) := by
  induction q using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul p b =>
    rw [QRmap_tmul, QRmap_tmul, Lam_tmul, Qmap_tmul, map_mul, hθ, mk_phiHat hx hC hN]

include hx in
/-- `Λ` is graded. -/
lemma Lam_mem {d : M} {q : QR w A'} (hq : q ∈ qGrade w A' d) :
    Lam hN σ q ∈ ChartGraded.quotGrade 𝒞 m d := by
  have key : ∀ q : QR w A', Lam hN σ (qProjR w A' d q) ∈ ChartGraded.quotGrade 𝒞 m d := by
    intro q
    induction q using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add]; exact add_mem ha hb
    | tmul p a =>
      rw [qProjR_tmul, Lam_tmul]
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (σ a)
      rw [← hb]
      refine ⟨MvPolynomial.aeval x (piP w d p) * phi0 w x b, ?_, rfl⟩
      have h1 : MvPolynomial.aeval x (piP w d p) ∈ 𝒞 d :=
        aeval_mem_of_homog hx (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous d p)
      have := SetLike.GradedMul.mul_mem h1 (phi0_mem hx b)
      rwa [add_zero] at this
  have := key q
  rwa [show qProjR w A' d q = q from hq] at this

lemma Lam_surjective (happ : ∀ (c : C) (k : ℕ), ∃ p : MvPolynomial ι ℤ, c - MvPolynomial.aeval x p ∈ m ^ k) :
    Function.Surjective (Lam hN σ) := by
  intro c
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  obtain ⟨p, hp⟩ := happ c 1
  refine ⟨p ⊗ₜ 1, ?_⟩
  rw [Lam_tmul, map_one, map_one, mul_one]
  exact (Ideal.Quotient.eq.2 (by simpa using hp)).symm

end AlgMag.ChartS5
