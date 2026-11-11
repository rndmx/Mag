/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartS5Chart
import AlgMag.ChartS5Trunc

/-!
# Chart lemma, Artin approximation step (étaleness): from truncations to `IsEtaleOn`

Part of the proof of the equivariant étale chart lemma for `D(M)`-actions at a closed point (local
structure in the sense of Alper–Hall–Rydh), used for **Theorem 6.8** of Algebraic Magnetism.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace AlgMag.ChartS5

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V W P : BigFppfOver B S hS}
  {e : yoneda.obj V ⟶ X} {f : yoneda.obj W ⟶ X} {he : EtP e} {u₀ : P ⟶ W} {v : P ⟶ V}
  {hw : yoneda.map u₀ ≫ f = yoneda.map v ≫ e}

/-- **Artin approximation step, étaleness**: the truncations `eA`, `eB`, compatible modulo `𝔫²`, give `g₀`. -/
theorem exists_etaleOn_of_truncations [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (c : ChartPiece he f u₀ v hw) {k : Type u} [Field k]
    (iso : (BigFppfOver.toScheme B S hS).obj P ≅ Spec (.of k)) (hfp : LFPP f)
    (hs : Function.Surjective ((BigFppfOver.toScheme B S hS).map u₀).appTop.hom)
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj c.Sobj, ⊤)]
    [hv : (RingHom.ker ((BigFppfOver.toScheme B S hS).map v).appTop.hom).IsMaximal]
    {Ξ : Type v} [CommRing Ξ] [IsNoetherianRing Ξ] (𝔫 : Ideal Ξ) [𝔫.IsMaximal] {s t : ℕ}
    (F F' : Fin s → Ξ)
    (hN : ∀ {R S' : Type u} [CommRing R] [CommRing S'] [Algebra R S'] [Algebra.FinitePresentation R S']
        [IsNoetherianRing R] [IsNoetherianRing S'] (p : Ideal R) [p.IsMaximal] (q : Ideal S')
        [q.IsMaximal] (_hq : q.comap (algebraMap R S') = p)
        (eA : ∀ j, (R ⧸ p ^ j) ≃+* Ξ ⧸ (Ideal.span (Set.range F) ⊔ 𝔫 ^ j))
        (eB : ∀ j, (S' ⧸ q ^ j) ≃+* Ξ ⧸ (Ideal.span (Set.range F') ⊔ 𝔫 ^ j)),
        (∀ (a : R) (ξ : Ξ), eA 2 (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ ξ →
          eB 2 (Ideal.Quotient.mk _ (algebraMap R S' a)) = Ideal.Quotient.mk _ ξ) →
        Algebra.IsEtaleAt R q)
    (eA : ∀ j, (Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ⧸
        (RingHom.ker ((BigFppfOver.toScheme B S hS).map v).appTop.hom) ^ j) ≃+*
        Ξ ⧸ (Ideal.span (Set.range F) ⊔ 𝔫 ^ j))
    (eB : ∀ j, (Γ((BigFppfOver.toScheme B S hS).obj c.Sobj, ⊤) ⧸ (RingHom.ker c.ringP) ^ j) ≃+*
        Ξ ⧸ (Ideal.span (Set.range F') ⊔ 𝔫 ^ j))
    (hc : ∀ (a : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) (ξ : Ξ),
      eA 2 (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ ξ →
      eB 2 (Ideal.Quotient.mk _ (c.ringV a)) = Ideal.Quotient.mk _ ξ) :
    ∃ g₀ : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤), ChartConclude.IsEtaleOn f g₀ ∧
      ((BigFppfOver.toScheme B S hS).map u₀).appTop.hom g₀ ≠ 0 := by
  letI := c.ringV.toAlgebra
  haveI : Algebra.FinitePresentation Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj c.Sobj, ⊤) :=
    (RingHom.finitePresentation_algebraMap).1 (c.ringV_finitePresentation hfp)
  haveI hq := c.ker_isMaximal iso hs
  have h := hN (RingHom.ker ((BigFppfOver.toScheme B S hS).map v).appTop.hom) (RingHom.ker c.ringP)
    c.comap_ringV eA eB hc
  exact exists_etaleOn_of_isEtaleAt c iso hfp h

end AlgMag.ChartS5

#print axioms AlgMag.ChartS5.exists_etaleOn_of_truncations
