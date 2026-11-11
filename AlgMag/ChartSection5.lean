/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartS5W
import AlgMag.ChartEtaleLocus

/-!
# Chart lemma, Artin approximation step: `Section5Output`

Part of the proof of the equivariant étale chart lemma for `D(M)`-actions at a closed point (local
structure in the sense of Alper–Hall–Rydh), used for **Theorem 6.8** of Algebraic Magnetism.

For `θ : R_t → A'`, `σ : A' → P₀/𝔭₀^N` with `σθ = eval_N` (the output of Artin approximation),
`W = Spec Q_{A'}/(f̃)`, `φ̃ : W → X`, the orbit ideal `I_O = ker(Q_{A'}/(f̃) → C/m)`, `w`.

* `section5Output_of_etale`: `Section5Output` from a point `g₀` of the étale locus at `w`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry DirectSum

universe u

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

namespace AlgMag.ChartS5

open ChartAlg

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} [hSa : IsAffine S]
  {M : Type u} [AddCommGroup M] [AddMonoid.FG M] [DecidableEq M]

local notation "SCH" => BigFppfOver.toScheme B S hS

variable {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  (actT : AAction (fppfO B S hS) M (yoneda.obj T)) [GradedRing (ChartMain.homog actT)]
  {m : Ideal (RT T)} {ι : Type u} [Finite ι] {w : ι → M} {x : ι → RT T}
  (hx : ∀ i, x i ∈ ChartMain.homog actT (w i)) (hC : CompletePair (ChartMain.homog actT) m)
  {t : Finset (P0hat w x m)} {s₁ : ℕ} (F₁ : Fin s₁ → QR w (Rs w t))
  (hv : ∀ ℓ, varpi hx hC t (F₁ ℓ) = 0)
  {N : ℕ} (hN : 1 ≤ N) {A' : Type u} [CommRing A'] [Algebra (P0 w ℤ) A']
  (σ : A' →ₐ[P0 w ℤ] P0 w ℤ ⧸ p0 w x m ^ N) (θ : Rs w t →ₐ[P0 w ℤ] A')
  (hθ : ∀ b, σ (θ b) = AdicCompletion.evalₐ (p0 w x m) N (RsI w t b))

/-- `f̃`, over `A'`. -/
noncomputable abbrev F2 : Fin s₁ → QR w A' := fun ℓ => QRmap w θ (F₁ ℓ)

include hx hC hv hθ in
lemma Lam_F2 (ℓ : Fin s₁) : Lam hN σ (F2 F₁ θ ℓ) = 0 := by
  have h1 := Lam_QRmap hx hC hN σ θ (RsI w t) hθ (F₁ ℓ)
  refine h1.trans ?_
  have h2 : Qmap hx hC (QRmap w (RsI w t) (F₁ ℓ)) = 0 := hv ℓ
  rw [h2, map_zero]

/-- `Q_{A'}/(f̃) → C/m`. -/
noncomputable def LamD : Dq (F2 F₁ θ) →+* RT T ⧸ m :=
  Ideal.Quotient.lift _ (Lam hN σ) (fun a ha => by
    have : Ideal.span (Set.range (F2 F₁ θ)) ≤ RingHom.ker (Lam hN σ) := by
      rw [Ideal.span_le]
      rintro _ ⟨ℓ, rfl⟩
      exact Lam_F2 actT hx hC F₁ hv hN σ θ hθ ℓ
    exact this ha)

/-- `Λ ∘ (Q_{R_t}/(F₁) → Q_{A'}/(f̃)) = mk ∘ ψ`. -/
lemma LamD_Dmap (y : Dq F₁) : LamD actT hx hC F₁ hv hN σ θ hθ (Dmap F₁ θ y) =
    Ideal.Quotient.mk m (psiD actT hx hC F₁ hv y) := by
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact Lam_QRmap hx hC hN σ θ (RsI w t) hθ q

lemma LamD_mem {d : M} {a : Dq (F2 F₁ θ)} (ha : a ∈ gq (F2 F₁ θ) d) :
    LamD actT hx hC F₁ hv hN σ θ hθ a ∈ ChartGraded.quotGrade (ChartMain.homog actT) m d := by
  obtain ⟨q, hq, rfl⟩ := ha
  exact Lam_mem hx hN σ hq

lemma LamD_surjective (happ : ∀ (c : RT T) (k : ℕ), ∃ p : MvPolynomial ι ℤ, c - MvPolynomial.aeval x p ∈ m ^ k) :
    Function.Surjective (LamD actT hx hC F₁ hv hN σ θ hθ) := fun c => by
  obtain ⟨y, hy⟩ := Lam_surjective hN σ happ c
  exact ⟨Ideal.Quotient.mk _ y, hy⟩

variable {deg : Fin s₁ → M} (hm : ∀ ℓ, F₁ ℓ ∈ qGrade w (Rs w t) (deg ℓ))

include hm in
lemma hm2 (ℓ : Fin s₁) : F2 F₁ θ ℓ ∈ qGrade w A' (deg ℓ) := QRmap_mem w θ (hm ℓ)

lemma LamD_ker_homog :
    letI := gqRing (hm2 F₁ θ hm)
    (RingHom.ker (LamD actT hx hC F₁ hv hN σ θ hθ)).IsHomogeneous (gq (F2 F₁ θ)) := by
  letI := gqRing (hm2 F₁ θ hm)
  letI := ChartGraded.quotGradedRing hC.hom
  exact ChartMain.ker_isHomogeneous _ (ChartGraded.quotGrade (ChartMain.homog actT) m) _
    (fun d a ha => LamD_mem actT hx hC F₁ hv hN σ θ hθ ha)

variable (ρ : RT (siteTop (B := B) (S := S) (hS := hS)) →+* Dq F₁)
  (hCt : B.Contains (Spec (.of (Dq F₁))))
  (hC₂ : B.Contains (Spec (.of (Dq (F2 F₁ θ)))))

/-- `Γ(S) → Q_{A'}/(f̃)`. -/
noncomputable abbrev rho2 : RT (siteTop (B := B) (S := S) (hS := hS)) →+* Dq (F2 F₁ θ) :=
  (Dmap F₁ θ).comp ρ

/-- `W → Spec Q_{R_t}/(F₁)`. -/
noncomputable def toD : rObj (rho2 F₁ θ ρ) hC₂ ⟶ rObj ρ hCt :=
  spMap _ (hC := hCt) (hC' := hC₂) (Dmap F₁ θ) rfl

/-- `φ̃ : W → X`. -/
noncomputable def fW {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (xt : yoneda.obj (rObj ρ hCt) ⟶ X) :
    yoneda.obj (rObj (rho2 F₁ θ ρ) hC₂) ⟶ X :=
  yoneda.map (toD F₁ θ ρ hCt hC₂) ≫ xt

variable (h0 : ∀ a, ρ a ∈ gq F₁ 0)

include h0 in
lemma rho2_mem (a) : rho2 F₁ θ ρ a ∈ gq (F2 F₁ θ) 0 := Dmap_mem F₁ θ (h0 a)

/-- `W`'s action, and `φ̃` is equivariant. -/
theorem fW_equivariant {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (actX : AAction (fppfO B S hS) M X)
    (xt : yoneda.obj (rObj ρ hCt) ⟶ X)
    (hxt : letI := gqRing hm; IsEquivariant (rAct ρ hCt (gq F₁) h0) actX xt) :
    letI := gqRing (hm2 F₁ θ hm)
    IsEquivariant (rAct (rho2 F₁ θ ρ) hC₂ (gq (F2 F₁ θ)) (rho2_mem F₁ θ ρ h0)) actX
      (fW F₁ θ ρ hCt hC₂ xt) := by
  letI := gqRing hm
  letI := gqRing (hm2 F₁ θ hm)
  intro T' g z
  have h1 := equivariant_rMap ρ hCt (gq F₁) h0 (gq (F2 F₁ θ)) (rho2_mem F₁ θ ρ h0) (Dmap F₁ θ) rfl
    (fun d a ha => Dmap_mem F₁ θ ha) (T := T') g z
  have h2 := hxt (T := T') g (z ≫ toD F₁ θ ρ hCt hC₂)
  exact (congrArg (xt.app T') h1).trans h2

/-- `τ ≫ (W → D_t)` and `a ≫ (T → D_t)` agree as soon as they do on elements. -/
lemma toD_eq (hψ : (psiD actT hx hC F₁ hv).comp ρ = ((BigFppfOver.toScheme B S hS).map (toTop' T)).appTop.hom)
    {T' : BigFppfOver B S hS} (τ : T' ⟶ rObj (rho2 F₁ θ ρ) hC₂) (a : T' ⟶ T)
    (h : ∀ y, ((BigFppfOver.toScheme B S hS).map τ).appTop.hom (rSec (rho2 F₁ θ ρ) hC₂ (Dmap F₁ θ y)) =
      ((BigFppfOver.toScheme B S hS).map a).appTop.hom (psiD actT hx hC F₁ hv y)) :
    τ ≫ toD F₁ θ ρ hCt hC₂ = a ≫ spLift _ ρ hCt (toTop' T) (psiD actT hx hC F₁ hv) hψ :=
  hom_ext_rObj ρ hCt fun y =>
    (comp_spMap_sec ρ hCt (Dmap F₁ θ) rfl τ y).trans ((h y).trans
      (comp_spLift_sec ρ hCt _ hψ a y).symm)

section Point

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : ChartPoint X) (u : p.P ⟶ T)
  (hum : ∀ c ∈ m, ((BigFppfOver.toScheme B S hS).map u).appTop.hom c = 0)

/-- `C/m → Γ(P)`. -/
noncomputable def uC : RT T ⧸ m →+* Γ((BigFppfOver.toScheme B S hS).obj p.P, ⊤) :=
  Ideal.Quotient.lift m ((BigFppfOver.toScheme B S hS).map u).appTop.hom hum

variable (hψ : (psiD actT hx hC F₁ hv).comp ρ = ((BigFppfOver.toScheme B S hS).map (toTop' T)).appTop.hom)

include hψ in
lemma LamD_rho2 (a) : LamD actT hx hC F₁ hv hN σ θ hθ (rho2 F₁ θ ρ a) =
    Ideal.Quotient.mk m (((BigFppfOver.toScheme B S hS).map (toTop' T)).appTop.hom a) := by
  rw [← hψ]
  exact LamD_Dmap actT hx hC F₁ hv hN σ θ hθ (ρ a)

include hψ in
lemma wPt_aux : ((uC p u hum).comp (LamD actT hx hC F₁ hv hN σ θ hθ)).comp (rho2 F₁ θ ρ) =
    ((BigFppfOver.toScheme B S hS).map (toTop' p.P)).appTop.hom := by
  refine RingHom.ext fun a => ?_
  simp only [RingHom.comp_apply]
  rw [show LamD actT hx hC F₁ hv hN σ θ hθ ((Dmap F₁ θ) (ρ a)) = _ from
    LamD_rho2 actT hx hC F₁ hv hN σ θ hθ ρ hψ a]
  change ((BigFppfOver.toScheme B S hS).map u).appTop.hom _ = _
  have e3 : u ≫ toTop' T = toTop' p.P := Over.mkIdTerminal.hom_ext _ _
  have e4 := congrArg (fun z : p.P ⟶ siteTop (B := B) (S := S) (hS := hS) =>
    ((BigFppfOver.toScheme B S hS).map z).appTop.hom a) e3
  simp only [Functor.map_comp, Scheme.Hom.comp_appTop] at e4
  exact e4

/-- `w : P → W`. -/
noncomputable def wPt : p.P ⟶ rObj (rho2 F₁ θ ρ) hC₂ :=
  spLift _ (rho2 F₁ θ ρ) hC₂ (toTop' p.P) ((uC p u hum).comp (LamD actT hx hC F₁ hv hN σ θ hθ))
    (wPt_aux actT hx hC F₁ hv hN σ θ hθ ρ p u hum hψ)

lemma wPt_sec (y : Dq (F2 F₁ θ)) :
    ((BigFppfOver.toScheme B S hS).map (wPt actT hx hC F₁ hv hN σ θ hθ ρ hC₂ p u hum hψ)).appTop.hom
      (rSec (rho2 F₁ θ ρ) hC₂ y) = uC p u hum (LamD actT hx hC F₁ hv hN σ θ hθ y) :=
  spLift_appTop _ _ _ _ _ _ y

end Point

end AlgMag.ChartS5
