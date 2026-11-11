/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartS5InputC

/-!
# Chart lemma, Artin approximation step (étaleness): `gTwo` on `W`

Part of the proof of the equivariant étale chart lemma for `D(M)`-actions at a closed point (local
structure in the sense of Alper–Hall–Rydh), used for **Theorem 6.8** of Algebraic Magnetism.

The hypotheses `hS2`, `hW`, `hlamR` of `hc_of_a1` for `W = Spec Q_{A'}/(f̃)`.
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
  {t : Finset (P0hat w x m)} {s₁ : ℕ} (F₁ : Fin s₁ → QR w (Rs w t))
  (hv : ∀ ℓ, varpi hx hC t (F₁ ℓ) = 0)
  {N : ℕ} (hN : 1 ≤ N) {A' : Type u} [CommRing A'] [Algebra (P0 w ℤ) A']
  (σ : A' →ₐ[P0 w ℤ] P0 w ℤ ⧸ p0 w x m ^ N) (θ : Rs w t →ₐ[P0 w ℤ] A')
  (hθ : ∀ b, σ (θ b) = AdicCompletion.evalₐ (p0 w x m) N (RsI w t b))
  (θh : A' →ₐ[P0 w ℤ] P0hat w x m)
  (hθh : ∀ a, AdicCompletion.evalₐ (p0 w x m) N (θh a) = σ a)
  (ρ : RT (siteTop (B := B) (S := S) (hS := hS)) →+* Dq F₁)
  (hCt : B.Contains (Spec (.of (Dq F₁))))
  (hC₂ : B.Contains (Spec (.of (Dq (F2 F₁ θ)))))
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : ChartPoint X) (u : p.P ⟶ T)
  (hum : ∀ c ∈ m, ((BigFppfOver.toScheme B S hS).map u).appTop.hom c = 0)
  (hψ : (psiD actT hx hC F₁ hv).comp ρ = ((BigFppfOver.toScheme B S hS).map (toTop' T)).appTop.hom)

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- `w : P → W`. -/
noncomputable abbrev u0 : p.P ⟶ rObj (rho2 F₁ θ ρ) hC₂ :=
  wPt actT hx hC F₁ hv hN σ θ hθ ρ hC₂ p u hum hψ

include hθh in
lemma u0_QR (y : QR w A') :
    ((SCH).map (u0 actT hx hC F₁ hv hN σ θ hθ ρ hC₂ p u hum hψ)).appTop.hom
      (rSec (rho2 F₁ θ ρ) hC₂ (Ideal.Quotient.mk _ y)) =
    ((SCH).map u).appTop.hom (Qmap hx hC (QRmap w θh y)) := by
  refine (wPt_sec actT hx hC F₁ hv hN σ θ hθ ρ hC₂ p u hum hψ _).trans ?_
  change uC p u hum (Lam hN σ y) = _
  rw [Lam_eq actT hx hC hN σ θh hθh]
  rfl

lemma u0_surj (hus : Function.Surjective ((SCH).map u).appTop.hom)
    (happ : ∀ (c : RT T) (k : ℕ), ∃ p : MvPolynomial ι ℤ, c - MvPolynomial.aeval x p ∈ m ^ k) :
    Function.Surjective ((SCH).map (u0 actT hx hC F₁ hv hN σ θ hθ ρ hC₂ p u hum hψ)).appTop.hom := by
  intro z
  obtain ⟨c, rfl⟩ := hus z
  obtain ⟨y, hy⟩ := LamD_surjective actT hx hC F₁ hv hN σ θ hθ happ (Ideal.Quotient.mk m c)
  refine ⟨rSec (rho2 F₁ θ ρ) hC₂ y, ?_⟩
  refine (wPt_sec actT hx hC F₁ hv hN σ θ hθ ρ hC₂ p u hum hψ y).trans ?_
  rw [hy]
  rfl

/-- `w` lies over `x`. -/
lemma u0_over (xt : yoneda.obj (rObj ρ hCt) ⟶ X) (φ : yoneda.obj T ⟶ X)
    (hxφ : yoneda.map (spLift _ ρ hCt (toTop' T) (psiD actT hx hC F₁ hv) hψ) ≫ xt = φ) :
    yoneda.map (u0 actT hx hC F₁ hv hN σ θ hθ ρ hC₂ p u hum hψ) ≫ fW F₁ θ ρ hCt hC₂ xt =
      yoneda.map u ≫ φ := by
  have e1 : u0 actT hx hC F₁ hv hN σ θ hθ ρ hC₂ p u hum hψ ≫ toD F₁ θ ρ hCt hC₂ =
      u ≫ spLift _ ρ hCt (toTop' T) (psiD actT hx hC F₁ hv) hψ :=
    toD_eq actT hx hC F₁ hv θ ρ hCt hC₂ hψ _ u fun y => by
      refine (wPt_sec actT hx hC F₁ hv hN σ θ hθ ρ hC₂ p u hum hψ (Dmap F₁ θ y)).trans ?_
      rw [LamD_Dmap]
      rfl
  calc _ = yoneda.map (u0 actT hx hC F₁ hv hN σ θ hθ ρ hC₂ p u hum hψ ≫ toD F₁ θ ρ hCt hC₂) ≫ xt := by
        simp [fW]
    _ = _ := by rw [e1, ← hxφ]; simp

section GTwo

variable {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  {e : yoneda.obj V ⟶ X} {he : EtP e} (xt : yoneda.obj (rObj ρ hCt) ⟶ X) {v : p.P ⟶ V}
  {hw : yoneda.map (u0 actT hx hC F₁ hv hN σ θ hθ ρ hC₂ p u hum hψ) ≫ fW F₁ θ ρ hCt hC₂ xt =
    yoneda.map v ≫ e}
  (c : ChartPiece he (fW F₁ θ ρ hCt hC₂ xt) (u0 actT hx hC F₁ hv hN σ θ hθ ρ hC₂ p u hum hψ) v hw)
  {Ξ : Type u} [CommRing Ξ] {J J' : Ideal Ξ} (hJ : J' = J)
  (eC2 : (RT T ⧸ kerI u ^ 2) ≃+* Ξ ⧸ J)
  (eB2 : (Γ((BigFppfOver.toScheme B S hS).obj c.Sobj, ⊤) ⧸ (RingHom.ker c.ringP) ^ 2) ≃+* Ξ ⧸ J')
  (toΞ' : Qring w x m →+* Ξ)
  (hB : ∀ y : QR w A', eB2 (Ideal.Quotient.mk _ (c.ringW (rSec (rho2 F₁ θ ρ) hC₂ (Ideal.Quotient.mk _ y)))) =
    Ideal.Quotient.mk _ (toΞ' (QRmap w θh y)))
  (hE : ∀ q, eC2 (Ideal.Quotient.mk _ (Qmap hx hC q)) = Ideal.Quotient.mk _ (toΞ' q))

include hB hE in
lemma gTwo_QR (y : QR w A') :
    gTwo c u hJ eC2 eB2 (c.ringW (rSec (rho2 F₁ θ ρ) hC₂ (Ideal.Quotient.mk _ y))) =
      rZ T (kerI u ^ 2) (Qmap hx hC (QRmap w θh y)) := by
  have e1 : (Ideal.quotEquivOfEq hJ) (eB2 (Ideal.Quotient.mk _
      (c.ringW (rSec (rho2 F₁ θ ρ) hC₂ (Ideal.Quotient.mk _ y))))) =
      eC2 (Ideal.Quotient.mk _ (Qmap hx hC (QRmap w θh y))) := by
    rw [hB, hE]; rfl
  change zE T (kerI u ^ 2) (eC2.symm ((Ideal.quotEquivOfEq hJ) (eB2 (Ideal.Quotient.mk _ _)))) = _
  rw [e1, RingEquiv.symm_apply_apply]
  rfl

include hB hE hθh hθ in
/-- The two maps `D_t → C/𝔲²` agree (`N ≥ 2`). -/
lemma gTwo_D (hN2 : 2 ≤ N) (y : Dq F₁) :
    gTwo c u hJ eC2 eB2 (c.ringW (rSec (rho2 F₁ θ ρ) hC₂ (Dmap F₁ θ y))) =
      rZ T (kerI u ^ 2) (psiD actT hx hC F₁ hv y) := by
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [Dmap_mk]
  refine (gTwo_QR actT hx hC F₁ hv hN σ θ hθ θh ρ hCt hC₂ p u hum hψ xt c hJ eC2 eB2 toΞ' hB hE _).trans ?_
  change _ = rZ T (kerI u ^ 2) (Qmap hx hC (QRmap w (RsI w t) q))
  have h1 := QRmap_congr_n actT hx hC u hum (θh.comp θ) (RsI w t) N (fun b => by
    change AdicCompletion.evalₐ (p0 w x m) N (θh (θ b)) = _
    rw [hθh, hθ]) q
  rw [← QRmap_comp] at h1
  have h2 : Qmap hx hC (QRmap w θh (QRmap w θ q) - QRmap w (RsI w t) q) ∈ kerI u ^ 2 := by
    have h3 : (nI actT hx hC u (w := w) (x := x) (m := m) ^ N).map (Qmap hx hC) ≤ kerI u ^ 2 := by
      rw [Ideal.map_pow]
      refine (Ideal.pow_right_mono ?_ N).trans (Ideal.pow_le_pow_right hN2)
      exact Ideal.map_le_iff_le_comap.2 fun q hq => hq
    exact h3 (Ideal.mem_map_of_mem _ h1)
  have h4 := (rZ_eq_zero_iff T _ _).2 h2
  rw [map_sub, map_sub] at h4
  exact sub_eq_zero.1 h4

include hB hE hθh hθ hψ in
lemma gTwo_hS2 (hN2 : 2 ≤ N) (s) : gTwo c u hJ eC2 eB2 (((SCH).map (toTop' c.Sobj)).appTop.hom s) =
      ((SCH).map (toTop' (Zc T (kerI u ^ 2)))).appTop.hom s := by
  have e1 : ((SCH).map (toTop' c.Sobj)).appTop.hom s =
      c.ringW (rSec (rho2 F₁ θ ρ) hC₂ (Dmap F₁ θ (ρ s))) := by
    rw [← top_comp c.toW s]
    refine congrArg _ ?_
    have e3 : toTop' (rObj (rho2 F₁ θ ρ) hC₂) =
        spToT (siteTop (B := B) (S := S) (hS := hS)) (rho2 F₁ θ ρ) hC₂ := Over.mkIdTerminal.hom_ext _ _
    rw [e3]
    exact spToT_appTop (siteTop (B := B) (S := S) (hS := hS)) (rho2 F₁ θ ρ) hC₂ s
  rw [e1, gTwo_D actT hx hC F₁ hv hN σ θ hθ θh hθh ρ hCt hC₂ p u hum hψ xt c hJ eC2 eB2 toΞ' hB hE hN2,
    ← top_comp (Zi T (kerI u ^ 2)) s, ← hψ]
  rfl

include hB hE hθh hθ in
/-- `V(𝔲²) → Spec S → W → X` is `V(𝔲²) → T → X`. -/
lemma gTwo_hW (hN2 : 2 ≤ N) (φ : yoneda.obj T ⟶ X)
    (hxφ : yoneda.map (spLift _ ρ hCt (toTop' T) (psiD actT hx hC F₁ hv) hψ) ≫ xt = φ)
    (b₂ : Zc T (kerI u ^ 2) ⟶ c.Sobj) (hb : ((SCH).map b₂).appTop.hom = gTwo c u hJ eC2 eB2) :
    yoneda.map (b₂ ≫ c.toW) ≫ fW F₁ θ ρ hCt hC₂ xt = yoneda.map (Zi T (kerI u ^ 2)) ≫ φ := by
  have e1 : (b₂ ≫ c.toW) ≫ toD F₁ θ ρ hCt hC₂ =
      Zi T (kerI u ^ 2) ≫ spLift _ ρ hCt (toTop' T) (psiD actT hx hC F₁ hv) hψ :=
    toD_eq actT hx hC F₁ hv θ ρ hCt hC₂ hψ _ _ fun y => by
      rw [Functor.map_comp, Scheme.Hom.comp_appTop]
      change ((SCH).map b₂).appTop.hom (c.ringW _) = _
      rw [hb]
      exact gTwo_D actT hx hC F₁ hv hN σ θ hθ θh hθh ρ hCt hC₂ p u hum hψ xt c hJ eC2 eB2 toΞ' hB hE hN2 y
  change yoneda.map (b₂ ≫ c.toW) ≫ yoneda.map (toD F₁ θ ρ hCt hC₂) ≫ xt = _
  rw [← hxφ, ← Category.assoc, ← Functor.map_comp, e1]
  simp

include hB hE hθh in
/-- Residue of `gTwo`. -/
lemma gTwo_hlam (happ : ∀ (c : RT T) (k : ℕ), ∃ p : MvPolynomial ι ℤ, c - MvPolynomial.aeval x p ∈ m ^ k)
    (hus : Function.Surjective ((SCH).map u).appTop.hom) (a) :
    ((SCH).map (zLift (kerI u ^ 2) u (kill_pow u 2 (by omega)))).appTop.hom (gTwo c u hJ eC2 eB2 a) =
      c.ringP a := by
  letI := p.field
  letI := (isField_of_iso p.iso).toField
  let lam := ((SCH).map (zLift (kerI u ^ 2) u (kill_pow u 2 (by omega)))).appTop.hom
  obtain ⟨g, hg⟩ := u0_surj actT hx hC F₁ hv hN σ θ hθ ρ hC₂ p u hum hψ hus happ (c.ringP a)
  obtain ⟨y₀, rfl⟩ := (rSec (rho2 F₁ θ ρ) hC₂).surjective g
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y₀
  let x' := c.ringW (rSec (rho2 F₁ θ ρ) hC₂ (Ideal.Quotient.mk _ y))
  have hz : c.ringP (a - x') = 0 := by
    rw [map_sub, c.ringP_ringW, hg, sub_self]
  have hz2 : gTwo c u hJ eC2 eB2 ((a - x') ^ 2) = 0 := by
    have : Ideal.Quotient.mk (RingHom.ker c.ringP ^ 2) ((a - x') ^ 2) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hz 2)
    change zE T (kerI u ^ 2) (eC2.symm ((Ideal.quotEquivOfEq hJ) (eB2 (Ideal.Quotient.mk _ _)))) = 0
    rw [this, map_zero, map_zero, map_zero, map_zero]
  have hz3 : lam (gTwo c u hJ eC2 eB2 (a - x')) = 0 := by
    have : lam (gTwo c u hJ eC2 eB2 (a - x')) ^ 2 = 0 := by
      rw [← map_pow, ← map_pow, hz2, map_zero]
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this
  rw [map_sub, map_sub, sub_eq_zero] at hz3
  refine hz3.trans ?_
  rw [gTwo_QR actT hx hC F₁ hv hN σ θ hθ θh ρ hCt hC₂ p u hum hψ xt c hJ eC2 eB2 toΞ' hB hE y]
  refine (zLift_appTop _ _ _ _).trans ?_
  rw [← u0_QR actT hx hC F₁ hv hN σ θ hθ θh hθh ρ hC₂ p u hum hψ y]
  exact hg

end GTwo

end AlgMag.ChartS5

#print axioms AlgMag.ChartS5.gTwo_hS2
#print axioms AlgMag.ChartS5.gTwo_hW
#print axioms AlgMag.ChartS5.gTwo_hlam
