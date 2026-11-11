/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartSection5

/-!
# Chart lemma, Artin approximation step: `Section5Output`, given étaleness at `w`

Part of the proof of the equivariant étale chart lemma for `D(M)`-actions at a closed point (local
structure in the sense of Alper–Hall–Rydh), used for **Theorem 6.8** of Algebraic Magnetism.

`section5Output_of_etale`: the fields of `AlgMag.ChartConclude.Section5Output` for
`W = Spec Q_{A'}/(f̃)`, from `IsEtaleOn φ̃ g₀` with `g₀` not vanishing at `w`, and
`φ̃` locally of finite presentation.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry DirectSum

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
  {deg : Fin s₁ → M} (hm : ∀ ℓ, F₁ ℓ ∈ qGrade w (Rs w t) (deg ℓ))
  (ρ : RT (siteTop (B := B) (S := S) (hS := hS)) →+* Dq F₁)
  (hCt : B.Contains (Spec (.of (Dq F₁))))
  (hC₂ : B.Contains (Spec (.of (Dq (F2 F₁ θ)))))
  (h0 : ∀ a, ρ a ∈ gq F₁ 0)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (actX : AAction (fppfO B S hS) M X)
  (p : ChartPoint X) (u : p.P ⟶ T)
  (hum : ∀ c ∈ m, ((BigFppfOver.toScheme B S hS).map u).appTop.hom c = 0)
  (hψ : (psiD actT hx hC F₁ hv).comp ρ = ((BigFppfOver.toScheme B S hS).map (toTop' T)).appTop.hom)

/-- **Artin approximation and shrinking.** `Section5Output` for `W = Spec Q_{A'}/(f̃)`. -/
theorem section5Output_of_etale (hX : IsAlgebraicSpace B S hS X)
    (happ : ∀ (c : RT T) (k : ℕ), ∃ p : MvPolynomial ι ℤ, c - MvPolynomial.aeval x p ∈ m ^ k)
    (hOfC : ∀ d, ∀ c ∈ ChartMain.homog actT d, c ∉ m → ∃ c', c * c' - 1 ∈ m)
    (xt : yoneda.obj (rObj ρ hCt) ⟶ X)
    (hxt : letI := gqRing hm; IsEquivariant (rAct ρ hCt (gq F₁) h0) actX xt)
    (φ : yoneda.obj T ⟶ X)
    (hxφ : yoneda.map (spLift _ ρ hCt (toTop' T) (psiD actT hx hC F₁ hv) hψ) ≫ xt = φ)
    (hu : yoneda.map u ≫ φ = p.x)
    (hMono : ∀ {T' : BigFppfOver B S hS} (a b : T' ⟶ T),
      (∀ c ∈ m, ((BigFppfOver.toScheme B S hS).map a).appTop.hom c = 0) →
      (∀ c ∈ m, ((BigFppfOver.toScheme B S hS).map b).appTop.hom c = 0) →
      φ.app (op T') a = φ.app (op T') b → a = b)
    (hfp : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)))
      (fW F₁ θ ρ hCt hC₂ xt))
    (g₀ : Γ((BigFppfOver.toScheme B S hS).obj (rObj (rho2 F₁ θ ρ) hC₂), ⊤))
    (hg₀ : ChartConclude.IsEtaleOn (fW F₁ θ ρ hCt hC₂ xt) g₀)
    (hg₀u : ((BigFppfOver.toScheme B S hS).map
      (wPt actT hx hC F₁ hv hN σ θ hθ ρ hC₂ p u hum hψ)).appTop.hom g₀ ≠ 0) :
    ChartConclude.Section5Output actX p := by
  classical
  letI grW := gqRing (hm2 F₁ θ hm)
  let Λ := LamD actT hx hC F₁ hv hN σ θ hθ
  have hΛ : Function.Surjective Λ := LamD_surjective actT hx hC F₁ hv hN σ θ hθ happ
  let W := rObj (rho2 F₁ θ ρ) hC₂
  let e := rSec (rho2 F₁ θ ρ) hC₂
  let h02 := rho2_mem F₁ θ ρ h0
  let actW := rAct (rho2 F₁ θ ρ) hC₂ (gq (F2 F₁ θ)) h02
  let f := fW F₁ θ ρ hCt hC₂ xt
  let u₀ := wPt actT hx hC F₁ hv hN σ θ hθ ρ hC₂ p u hum hψ
  have hf : IsEquivariant actW actX f := fW_equivariant F₁ θ hm ρ hCt hC₂ h0 actX xt hxt
  let IO : Ideal Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) :=
    (RingHom.ker Λ).comap (e.symm : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) →+* Dq (F2 F₁ θ))
  have memIO : ∀ a, e a ∈ IO ↔ Λ a = 0 := fun a => by
    change Λ (e.symm (e a)) = 0 ↔ _
    rw [e.symm_apply_apply]
  have hker := LamD_ker_homog actT hx hC F₁ hv hN σ θ hθ hm
  have hmem : ∀ d a, a ∈ gq (F2 F₁ θ) d → e a ∈ ChartMain.homog actW d := fun d a ha =>
    (mem_homog_rAct (rho2 F₁ θ ρ) hC₂ (gq (F2 F₁ θ)) h02).2 ha
  -- `w` lies over `x`
  have hover : yoneda.map u₀ ≫ f = p.x := by
    have e1 : u₀ ≫ toD F₁ θ ρ hCt hC₂ = u ≫ spLift _ ρ hCt (toTop' T) (psiD actT hx hC F₁ hv) hψ :=
      toD_eq actT hx hC F₁ hv θ ρ hCt hC₂ hψ u₀ u fun y => by
        refine (wPt_sec actT hx hC F₁ hv hN σ θ hθ ρ hC₂ p u hum hψ (Dmap F₁ θ y)).trans ?_
        rw [LamD_Dmap]
        rfl
    calc yoneda.map u₀ ≫ f = yoneda.map (u₀ ≫ toD F₁ θ ρ hCt hC₂) ≫ xt := by
          simp [f, fW]
      _ = yoneda.map u ≫ yoneda.map (spLift _ ρ hCt (toTop' T) (psiD actT hx hC F₁ hv) hψ) ≫ xt := by
          rw [e1]; simp
      _ = p.x := by rw [hxφ, hu]
  have hkill : ∀ a, Λ a = 0 → ((BigFppfOver.toScheme B S hS).map u₀).appTop.hom (e a) = 0 := fun a ha => by
    refine (wPt_sec actT hx hC F₁ hv hN σ θ hθ ρ hC₂ p u hum hψ a).trans ?_
    change uC p u hum (Λ a) = 0
    rw [ha, map_zero]
  refine ⟨W, inferInstance, actW, f, IO, u₀, g₀, hf, ?_, ?_, ?_, hover, ?_, hg₀, hg₀u, ?_⟩
  · -- `I_O` is homogeneous
    exact comap_homog (rho2 F₁ θ ρ) hC₂ (gq (F2 F₁ θ)) h02 _ hker
  · -- homogeneous elements off `I_O` are units modulo `I_O`
    intro d c hc hcO
    obtain ⟨c₀, rfl⟩ := e.surjective c
    have hc₀ : c₀ ∈ gq (F2 F₁ θ) d := (mem_homog_rAct (rho2 F₁ θ ρ) hC₂ (gq (F2 F₁ θ)) h02).1 hc
    obtain ⟨c', hc', hk⟩ := LamD_mem actT hx hC F₁ hv hN σ θ hθ hc₀
    have hc'm : c' ∉ m := fun h => hcO ((memIO c₀).2 (by
      have e1 : Λ c₀ = Ideal.Quotient.mk m c' := hk.symm
      rw [e1]
      exact Ideal.Quotient.eq_zero_iff_mem.2 h))
    obtain ⟨c'', hc''⟩ := hOfC d c' hc' hc'm
    obtain ⟨y, hy⟩ := hΛ (Ideal.Quotient.mk m c'')
    refine ⟨e y, ?_⟩
    have e3 : e c₀ * e y - 1 = e (c₀ * y - 1) := by simp only [map_sub, map_mul, map_one]
    rw [e3]
    refine (memIO _).2 ?_
    rw [map_sub, map_mul, map_one, hy]
    have e1 : Λ c₀ = Ideal.Quotient.mk m c' := hk.symm
    rw [e1, ← map_mul, ← map_one (Ideal.Quotient.mk m), ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hc''
  · exact ChartEtale.etaleLocusStable actW hX hf hfp
  · intro a ha
    obtain ⟨a₀, rfl⟩ := e.surjective a
    exact hkill a₀ ((memIO a₀).1 ha)
  · intro T' s g hg
    have hk' : ∀ a, Λ a = 0 →
        ((BigFppfOver.toScheme B S hS).map (s ≫ u₀)).appTop.hom (e a) = 0 := fun a ha => by
      rw [Functor.map_comp, Scheme.Hom.comp_appTop]
      change ((BigFppfOver.toScheme B S hS).map s).appTop.hom
        (((BigFppfOver.toScheme B S hS).map u₀).appTop.hom (e a)) = 0
      rw [hkill a ha, map_zero]
    refine stab_of_mono (rho2 F₁ θ ρ) hC₂ Λ hΛ (LamD_rho2 actT hx hC F₁ hv hN σ θ hθ ρ hψ)
      (gq (F2 F₁ θ)) h02 actX hker f hf φ ?_ hMono (s ≫ u₀) hk' g hg
    intro T'' τ a hs
    have e1 : τ ≫ toD F₁ θ ρ hCt hC₂ = a ≫ spLift _ ρ hCt (toTop' T) (psiD actT hx hC F₁ hv) hψ :=
      toD_eq actT hx hC F₁ hv θ ρ hCt hC₂ hψ τ a fun y =>
        (hs (Dmap F₁ θ y) (psiD actT hx hC F₁ hv y)
          (LamD_Dmap actT hx hC F₁ hv hN σ θ hθ y)).symm
    change xt.app _ (τ ≫ toD F₁ θ ρ hCt hC₂) = φ.app _ a
    rw [e1, ← hxφ]
    rfl

end AlgMag.ChartS5

#print axioms AlgMag.ChartS5.section5Output_of_etale
