/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartS5InputAlg

/-!
# Chart lemma, Artin approximation step: the ring `Ξ = Q_𝔫`, packaged

Part of the proof of the equivariant étale chart lemma for `D(M)`-actions at a closed point (local
structure in the sense of Alper–Hall–Rydh), used for **Theorem 6.8** of Algebraic Magnetism.

`exists_Xi` packages the properties of `Ξ` used in `section5Output_of_input`, so that its statement
and proof do not mention `Localization.AtPrime` of the concrete tensor product.
-/

open TensorProduct

universe u

namespace AlgMag.ChartS5

variable {P₀ P Rh C : Type u} [CommRing P₀] [CommRing P] [CommRing Rh] [CommRing C] [Algebra P₀ P]
  [Algebra P₀ Rh] [IsNoetherianRing (P ⊗[P₀] Rh)]

/-- **Artin approximation step, Coordinates**: `Ξ = Q_𝔫`, and `N₀` chosen before the approximation. -/
theorem exists_Xi (π : P ⊗[P₀] Rh →+* C) (hπ : Function.Surjective π) {s t : ℕ}
    (F : Fin s → P ⊗[P₀] Rh) (hF : Ideal.span (Set.range F) = RingHom.ker π)
    (r : Fin t → Fin s → P ⊗[P₀] Rh)
    (hr : Submodule.span (P ⊗[P₀] Rh) (Set.range r) =
      LinearMap.ker (Fintype.linearCombination (P ⊗[P₀] Rh) F))
    (𝔲 : Ideal C) (𝔫 : Ideal (P ⊗[P₀] Rh)) [𝔫.IsMaximal] (hn : 𝔲.comap π = 𝔫) :
    ∃ (Ξ : Type u) (_ : CommRing Ξ) (_ : IsNoetherianRing Ξ) (𝔪 : Ideal Ξ) (_ : 𝔪.IsMaximal)
      (toQ : P ⊗[P₀] Rh →+* Ξ)
      (eCf : ∀ j, (C ⧸ 𝔲 ^ j) ≃+* Ξ ⧸ (Ideal.span (Set.range fun ℓ => toQ (F ℓ)) ⊔ 𝔪 ^ j)),
      (∀ j q, eCf j (Ideal.Quotient.mk _ (π q)) = Ideal.Quotient.mk _ (toQ q)) ∧
      (∀ j q, q ∈ 𝔫 ^ j → toQ q ∈ 𝔪 ^ j) ∧
      (∀ {A : Type u} [CommRing A] [Algebra P₀ A] (θ : A →ₐ[P₀] Rh) (F₂ : Fin s → P ⊗[P₀] A)
        (S' : Type u) [CommRing S'] (ι' : (P ⊗[P₀] A ⧸ Ideal.span (Set.range F₂)) →+* S')
        (_ : ι'.Etale) (q' : Ideal S') [q'.IsMaximal] [(wIdeal θ 𝔫 F₂).IsMaximal]
        (_ : q'.comap ι' = wIdeal θ 𝔫 F₂)
        (_ : Function.Surjective ((Ideal.Quotient.mk q').comp ι'))
        (_ : ∀ j, (𝔫 ^ j).comap (gQ (P := P) θ) = (𝔫.comap (gQ (P := P) θ)) ^ j ∧
          Function.Surjective ((Ideal.Quotient.mk (𝔫 ^ j)).comp (gQ (P := P) θ))),
        ∃ eB : ∀ j, (S' ⧸ q' ^ j) ≃+* Ξ ⧸
            (Ideal.span (Set.range fun ℓ => toQ (gQ θ (F₂ ℓ))) ⊔ 𝔪 ^ j),
          ∀ j y, eB j (Ideal.Quotient.mk _ (ι' (Ideal.Quotient.mk _ y))) =
            Ideal.Quotient.mk _ (toQ (gQ θ y))) ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (f' : Fin s → Ξ) (r' : Fin t → Fin s → Ξ),
        (∀ ℓ, f' ℓ - toQ (F ℓ) ∈ 𝔪 ^ (N + 1)) → (∀ j ℓ, r' j ℓ - toQ (r j ℓ) ∈ 𝔪 ^ (N + 1)) →
        (∀ j, ∑ ℓ, r' j ℓ * f' ℓ = 0) →
        ∀ {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
          [IsNoetherianRing R] [IsNoetherianRing S] (p : Ideal R) [p.IsMaximal] (q : Ideal S)
          [q.IsMaximal] (_hq : q.comap (algebraMap R S) = p)
          (eA : ∀ j, (R ⧸ p ^ j) ≃+* Ξ ⧸ (Ideal.span (Set.range fun ℓ => toQ (F ℓ)) ⊔ 𝔪 ^ j))
          (eB : ∀ j, (S ⧸ q ^ j) ≃+* Ξ ⧸ (Ideal.span (Set.range f') ⊔ 𝔪 ^ j)),
          (∀ (a : R) (ξ : Ξ), eA 2 (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ ξ →
            eB 2 (Ideal.Quotient.mk _ (algebraMap R S a)) = Ideal.Quotient.mk _ ξ) →
          Algebra.IsEtaleAt R q := by
  haveI : IsNoetherianRing (Localization.AtPrime 𝔫) :=
    IsLocalization.isNoetherianRing 𝔫.primeCompl _ inferInstance
  have hrΞ := span_syzygies_localization 𝔫 F r hr
  obtain ⟨N₀, hN₀⟩ := exists_N₀_isEtaleAt (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔫)) _ _ hrΞ
  refine ⟨Localization.AtPrime 𝔫, inferInstance, inferInstance, IsLocalRing.maximalIdeal _, inferInstance,
    algebraMap _ _, fun j => eC π hπ F hF 𝔲 𝔫 hn j, fun j q => eC_mk π hπ F hF 𝔲 𝔫 hn j q,
    fun j q hq => (comap_localization_pow 𝔫 j).ge hq, ?_, N₀, hN₀⟩
  intro A _ _ θ F₂ S' _ ι' hι q' _ _ hq hres hT
  exact exists_eB θ 𝔫 F₂ ι' hι q' hq hres hT

end AlgMag.ChartS5

#print axioms AlgMag.ChartS5.exists_Xi
