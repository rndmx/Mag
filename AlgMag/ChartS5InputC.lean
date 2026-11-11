/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartS5InputB
import AlgMag.ChartS5Congr
import AlgMag.ChartS5HA

/-!
# Chart lemma, Artin approximation step: comparison of `Q_{A'}`, `Q` and `C`

Part of the proof of the equivariant étale chart lemma for `D(M)`-actions at a closed point (local
structure in the sense of Alper–Hall–Rydh), used for **Theorem 6.8** of Algebraic Magnetism.

`θh : A' → P̂₀` lifts `σ`. `nI = ker(Q → C → Γ(P))`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

namespace AlgMag.ChartS5

open ChartAlg

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} [hSa : IsAffine S]
  {M : Type u} [AddCommGroup M] [AddMonoid.FG M] [DecidableEq M]

variable {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  (actT : AAction (fppfO B S hS) M (yoneda.obj T)) [GradedRing (ChartMain.homog actT)]
  {m : Ideal (RT T)} {ι : Type u} [Finite ι] {w : ι → M} {x : ι → RT T}
  (hx : ∀ i, x i ∈ ChartMain.homog actT (w i)) (hC : CompletePair (ChartMain.homog actT) m)
  {P : BigFppfOver B S hS} (u : P ⟶ T)
  (hum : ∀ c ∈ m, ((BigFppfOver.toScheme B S hS).map u).appTop.hom c = 0)

/-- `𝔫 = ker(Q → C → Γ(P))`. -/
noncomputable abbrev nI : Ideal (Qring w x m) :=
  RingHom.ker (((BigFppfOver.toScheme B S hS).map u).appTop.hom.comp (Qmap hx hC))

lemma mem_nI (q : Qring w x m) : q ∈ nI actT hx hC u ↔ Qmap hx hC q ∈ kerI u := Iff.rfl

include hum in
/-- `p̂ Q ⊆ 𝔫`. -/
lemma ph_map_le : (RingHom.ker (AdicCompletion.evalₐ (p0 w x m) 1)).map
    (Algebra.TensorProduct.includeRight : P0hat w x m →ₐ[P0 w ℤ] Qring w x m) ≤ nI actT hx hC u := by
  refine Ideal.map_le_iff_le_comap.2 fun y hy => ?_
  have h1 : phiHat hx hC y ∈ m := by
    have h2 := (phiHat_isLim hx hC y).2 1 0 (by
      rw [map_zero]; exact hy)
    simpa using h2
  change ((BigFppfOver.toScheme B S hS).map u).appTop.hom (Qmap hx hC (1 ⊗ₜ y)) = 0
  rw [Qmap_tmul, map_mul, hum _ h1, mul_zero]

include hum in
/-- Congruence of the Artin approximation step: `g, g'` congruent at level `N` are congruent modulo `𝔫^N`. -/
lemma QRmap_congr_n {B₀ : Type*} [CommRing B₀] [Algebra (P0 w ℤ) B₀] [IsNoetherianRing (P0 w ℤ)]
    (g g' : B₀ →ₐ[P0 w ℤ] P0hat w x m) (N : ℕ)
    (h : ∀ b, AdicCompletion.evalₐ (p0 w x m) N (g b) = AdicCompletion.evalₐ (p0 w x m) N (g' b))
    (q : QR w B₀) : QRmap w g q - QRmap w g' q ∈ nI actT hx hC u ^ N := by
  have h1 := QRmap_congr w g g' (RingHom.ker (AdicCompletion.evalₐ (p0 w x m) 1) ^ N) (fun b => by
    rw [← ker_evalₐ_eq_pow, RingHom.mem_ker, map_sub, h, sub_self]) q
  rw [Ideal.map_pow] at h1
  exact Ideal.pow_right_mono (ph_map_le actT hx hC u hum) N h1

variable {N : ℕ} (hN : 1 ≤ N) {A' : Type u} [CommRing A'] [Algebra (P0 w ℤ) A']
  (σ : A' →ₐ[P0 w ℤ] P0 w ℤ ⧸ p0 w x m ^ N) (θh : A' →ₐ[P0 w ℤ] P0hat w x m)
  (hθh : ∀ a, AdicCompletion.evalₐ (p0 w x m) N (θh a) = σ a)

include hθh in
/-- `Λ y = mk(Qmap(θ̂ y))`. -/
lemma Lam_eq (y : QR w A') :
    Lam hN σ y = Ideal.Quotient.mk m (Qmap hx hC (QRmap w θh y)) := by
  have h := Lam_QRmap hx hC hN σ (AlgHom.id _ A') θh (fun b => (hθh b).symm) y
  rwa [QRmap_id] at h

end AlgMag.ChartS5

#print axioms AlgMag.ChartS5.Lam_eq
#print axioms AlgMag.ChartS5.QRmap_congr_n
