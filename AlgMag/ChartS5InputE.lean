/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartS5InputD
import AlgMag.ChartS5Step6
import AlgMag.ChartS5Final
import AlgMag.ChartS5Art
import AlgMag.ChartS5Lfp

/-!
# Chart lemma, Artin approximation step: `g₀` at a level

Part of the proof of the equivariant étale chart lemma for `D(M)`-actions at a closed point (local
structure in the sense of Alper–Hall–Rydh), used for **Theorem 6.8** of Algebraic Magnetism.
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

include hv hN hθ ρ hC₂ hum hψ hθh in
lemma F2_mem (ℓ : Fin s₁) : QRmap w θh (F2 F₁ θ ℓ) ∈ nI actT hx hC u := by
  have h := u0_QR actT hx hC F₁ hv hN σ θ hθ θh hθh ρ hC₂ p u hum hψ (F2 F₁ θ ℓ)
  have e : Ideal.Quotient.mk (Ideal.span (Set.range (F2 F₁ θ))) (F2 F₁ θ ℓ) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨ℓ, rfl⟩)
  rw [e, map_zero, map_zero] at h
  exact h.symm

include hθ hθh in
/-- **Artin approximation step, étaleness.** `g₀` on `W`. -/
theorem exists_g0 [IsNoetherianRing (RT T)] [(p0 w x m).IsMaximal] [Algebra.Etale (P0 w ℤ) A']
    [(nI actT hx hC u : Ideal (Qring w x m)).IsMaximal]
    (hsurj : Function.Surjective (Qmap hx hC)) (F : Fin s₁ → Qring w x m)
    (hF : Ideal.span (Set.range F) = RingHom.ker (Qmap hx hC)) (hN2 : 2 ≤ N)
    (happ : ∀ (c : RT T) (k : ℕ), ∃ p : MvPolynomial ι ℤ, c - MvPolynomial.aeval x p ∈ m ^ k)
    (hus : Function.Surjective ((SCH).map u).appTop.hom)
    (φ : yoneda.obj T ⟶ X) (xt : yoneda.obj (rObj ρ hCt) ⟶ X)
    (hxφ : yoneda.map (spLift _ ρ hCt (toTop' T) (psiD actT hx hC F₁ hv) hψ) ≫ xt = φ)
    (hfp : LFPP (fW F₁ θ ρ hCt hC₂ xt))
    {V : BigFppfOver B S hS} [IsAffine ((SCH).obj V)] [IsNoetherianRing Γ((SCH).obj V, ⊤)]
    {e : yoneda.obj V ⟶ X} (he : EtP e) (v : p.P ⟶ V) (hwv : yoneda.map u ≫ φ = yoneda.map v ≫ e)
    (hvs : Function.Surjective ((SCH).map v).appTop.hom)
    (hth : ∀ j, 1 ≤ j → ∃ ho : ChartMain.ClosedP (yoneda.map (Zi T (m ^ j)) ≫ φ),
      (ChartMain.idealOf ho e).ideal ⟨⊤, isAffineOpen_top _⟩ ≤ kerI v ^ j)
    {Ξ : Type u} [CommRing Ξ] [IsNoetherianRing Ξ] (𝔪 : Ideal Ξ) [𝔪.IsMaximal] (toQ : Qring w x m →+* Ξ)
    (eCf : ∀ j, (RT T ⧸ kerI u ^ j) ≃+* Ξ ⧸ (Ideal.span (Set.range fun ℓ => toQ (F ℓ)) ⊔ 𝔪 ^ j))
    (hE2 : ∀ q, eCf 2 (Ideal.Quotient.mk _ (Qmap hx hC q)) = Ideal.Quotient.mk _ (toQ q))
    (hEB : ∀ (S' : Type u) [CommRing S'] (ι' : Dq (F2 F₁ θ) →+* S') (_ : ι'.Etale) (q' : Ideal S')
      [q'.IsMaximal] (_ : q'.comap ι' = wIdeal θh (nI actT hx hC u) (F2 F₁ θ))
      (_ : Function.Surjective ((Ideal.Quotient.mk q').comp ι')),
      ∃ eB : ∀ j, (S' ⧸ q' ^ j) ≃+* Ξ ⧸
          (Ideal.span (Set.range fun ℓ => toQ (QRmap w θh (F2 F₁ θ ℓ))) ⊔ 𝔪 ^ j),
        ∀ j y, eB j (Ideal.Quotient.mk _ (ι' (Ideal.Quotient.mk _ y))) =
          Ideal.Quotient.mk _ (toQ (QRmap w θh y)))
    (hff : ∀ ℓ, toQ (QRmap w θh (F2 F₁ θ ℓ)) - toQ (F ℓ) ∈ 𝔪 ^ 2)
    (hNN : ∀ {R S' : Type u} [CommRing R] [CommRing S'] [Algebra R S'] [Algebra.FinitePresentation R S']
        [IsNoetherianRing R] [IsNoetherianRing S'] (𝔭 : Ideal R) [𝔭.IsMaximal] (q : Ideal S')
        [q.IsMaximal] (_hq : q.comap (algebraMap R S') = 𝔭)
        (eA : ∀ j, (R ⧸ 𝔭 ^ j) ≃+* Ξ ⧸ (Ideal.span (Set.range fun ℓ => toQ (F ℓ)) ⊔ 𝔪 ^ j))
        (eB : ∀ j, (S' ⧸ q ^ j) ≃+* Ξ ⧸
          (Ideal.span (Set.range fun ℓ => toQ (QRmap w θh (F2 F₁ θ ℓ))) ⊔ 𝔪 ^ j)),
        (∀ (a : R) (ξ : Ξ), eA 2 (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ ξ →
          eB 2 (Ideal.Quotient.mk _ (algebraMap R S' a)) = Ideal.Quotient.mk _ ξ) →
        Algebra.IsEtaleAt R q) :
    ∃ g₀ : Γ((SCH).obj (rObj (rho2 F₁ θ ρ) hC₂), ⊤), ChartConclude.IsEtaleOn (fW F₁ θ ρ hCt hC₂ xt) g₀ ∧
      ((SCH).map (wPt actT hx hC F₁ hv hN σ θ hθ ρ hC₂ p u hum hψ)).appTop.hom g₀ ≠ 0 := by
  classical
  letI := p.field
  let u₀ := u0 actT hx hC F₁ hv hN σ θ hθ ρ hC₂ p u hum hψ
  have hw : yoneda.map u₀ ≫ fW F₁ θ ρ hCt hC₂ xt = yoneda.map v ≫ e :=
    (u0_over actT hx hC F₁ hv hN σ θ hθ ρ hCt hC₂ p u hum hψ xt φ hxφ).trans hwv
  obtain ⟨c⟩ := exists_chartPiece he (fW F₁ θ ρ hCt hC₂ xt) p.iso u₀ v hw
  let f : Fin s₁ → Ξ := fun ℓ => toQ (F ℓ)
  let J : ℕ → Ideal Ξ := fun j => Ideal.span (Set.range f) ⊔ 𝔪 ^ j
  let eC' : ∀ j, (RT T ⧸ kerI u ^ j) ≃+* Ξ ⧸ J j := eCf
  obtain ⟨eA, a₁, hsq, hform, hres⟩ := exists_eA_pkg he φ p.iso u v hwv hus hvs m hum hth J eC'
  let ι' : Dq (F2 F₁ θ) →+* Γ((SCH).obj c.Sobj, ⊤) :=
    c.ringW.comp (rSec (rho2 F₁ θ ρ) hC₂ : Dq (F2 F₁ θ) →+* _)
  have hιe : ι'.Etale := RingHom.Etale.respectsIso.2 c.ringW (rSec (rho2 F₁ θ ρ) hC₂) c.ringW_etale
  haveI hmq : (RingHom.ker c.ringP).IsMaximal := c.ker_isMaximal p.iso
    (u0_surj actT hx hC F₁ hv hN σ θ hθ ρ hC₂ p u hum hψ hus happ)
  have hq : (RingHom.ker c.ringP).comap ι' = wIdeal θh (nI actT hx hC u) (F2 F₁ θ) := by
    ext g
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective g
    have h1 : c.ringP (ι' (Ideal.Quotient.mk _ y)) = _ :=
      (c.ringP_ringW _).trans (u0_QR actT hx hC F₁ hv hN σ θ hθ θh hθh ρ hC₂ p u hum hψ y)
    rw [Ideal.mem_comap, RingHom.mem_ker, h1]
    constructor
    · intro h
      exact Ideal.mem_map_of_mem _ (show gQ θh y ∈ nI actT hx hC u from h)
    · intro h
      obtain ⟨y', hy', hyy⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 h
      have hd := Ideal.Quotient.eq.1 hyy
      have hle : Ideal.span (Set.range (F2 F₁ θ)) ≤ (nI actT hx hC u).comap (gQ θh) := by
        rw [Ideal.span_le]
        rintro _ ⟨ℓ, rfl⟩
        exact F2_mem actT hx hC F₁ hv hN σ θ hθ θh hθh ρ hC₂ p u hum hψ ℓ
      have h2 : y ∈ (nI actT hx hC u).comap (gQ θh) := by
        have h3 := Ideal.sub_mem _ hy' (hle hd)
        simpa using h3
      exact h2
  have hres' : Function.Surjective ((Ideal.Quotient.mk (RingHom.ker c.ringP)).comp ι') := by
    intro y
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨g, hg⟩ := u0_surj actT hx hC F₁ hv hN σ θ hθ ρ hC₂ p u hum hψ hus happ (c.ringP s)
    obtain ⟨g₁, rfl⟩ := (rSec (rho2 F₁ θ ρ) hC₂).surjective g
    refine ⟨g₁, Ideal.Quotient.eq.2 ?_⟩
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    exact (c.ringP_ringW _).trans hg
  obtain ⟨eB, heB⟩ := hEB _ ι' hιe (RingHom.ker c.ringP) hq hres'
  let f' : Fin s₁ → Ξ := fun ℓ => toQ (QRmap w θh (F2 F₁ θ ℓ))
  have hJ : Ideal.span (Set.range f') ⊔ 𝔪 ^ 2 = J 2 := by
    have hd : ∀ ℓ, f' ℓ - f ℓ ∈ 𝔪 ^ 2 := hff
    refine le_antisymm (sup_le ?_ le_sup_right) (sup_le ?_ le_sup_right)
    · rw [Ideal.span_le]
      rintro _ ⟨ℓ, rfl⟩
      have : f' ℓ = f ℓ + (f' ℓ - f ℓ) := by ring
      rw [this]
      exact add_mem (Ideal.mem_sup_left (Ideal.subset_span ⟨ℓ, rfl⟩)) (Ideal.mem_sup_right (hd ℓ))
    · rw [Ideal.span_le]
      rintro _ ⟨ℓ, rfl⟩
      have : f ℓ = f' ℓ - (f' ℓ - f ℓ) := by ring
      rw [this]
      exact sub_mem (Ideal.mem_sup_left (Ideal.subset_span ⟨ℓ, rfl⟩)) (Ideal.mem_sup_right (hd ℓ))
  haveI hnm : (RingHom.ker ((SCH).map v).appTop.hom).IsMaximal := by
    letI := (isField_of_iso p.iso).toField
    exact RingHom.ker_isMaximal_of_surjective _ hvs
  haveI : Algebra.FiniteType (P0 w ℤ) A' := inferInstance
  haveI : IsNoetherianRing A' := Algebra.FiniteType.isNoetherianRing (P0 w ℤ) A'
  haveI : IsNoetherianRing (QR w A') := isNoetherianRing_QR w A'
  haveI hNW : IsNoetherianRing Γ((SCH).obj (rObj (rho2 F₁ θ ρ) hC₂), ⊤) :=
    isNoetherianRing_of_ringEquiv (Dq (F2 F₁ θ)) (rSec (rho2 F₁ θ ρ) hC₂)
  haveI hNS : IsNoetherianRing Γ((SCH).obj c.Sobj, ⊤) := by
    letI := c.ringW.toAlgebra
    haveI : Algebra.Etale Γ((SCH).obj (rObj (rho2 F₁ θ ρ) hC₂), ⊤) Γ((SCH).obj c.Sobj, ⊤) := c.ringW_etale
    exact Algebra.FiniteType.isNoetherianRing Γ((SCH).obj (rObj (rho2 F₁ θ ρ) hC₂), ⊤) _
  refine exists_etaleOn_of_truncations (t := 0) c p.iso hfp
    (u0_surj actT hx hC F₁ hv hN σ θ hθ ρ hC₂ p u hum hψ hus happ)
    𝔪 f f' hNN eA eB ?_
  intro a ξ h
  have hhB : ∀ y : QR w A', eB 2 (Ideal.Quotient.mk _ (c.ringW (rSec (rho2 F₁ θ ρ) hC₂ (Ideal.Quotient.mk _ y)))) =
      Ideal.Quotient.mk _ (toQ (QRmap w θh y)) := fun y => heB 2 y
  have hhE := hE2
  have hS2 := gTwo_hS2 actT hx hC F₁ hv hN σ θ hθ θh hθh ρ hCt hC₂ p u hum hψ xt c hJ (eC' 2) (eB 2)
    toQ hhB hhE hN2
  refine hc_of_a1 c u hJ (eC' 2) (eB 2) φ p.iso hus (eA 2) a₁ hsq hform hres hS2
    (gTwo_hW actT hx hC F₁ hv hN σ θ hθ θh hθh ρ hCt hC₂ p u hum hψ xt c hJ (eC' 2) (eB 2)
      toQ hhB hhE hN2 φ hxφ _ (siteOfRing_appTop _ hS2))
    (gTwo_hlam actT hx hC F₁ hv hN σ θ hθ θh hθh ρ hCt hC₂ p u hum hψ xt c hJ (eC' 2) (eB 2)
      toQ hhB hhE happ hus) a ξ h

end AlgMag.ChartS5

#print axioms AlgMag.ChartS5.exists_g0
