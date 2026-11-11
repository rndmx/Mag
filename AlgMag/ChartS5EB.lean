/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartS5Trunc

/-!
# Chart lemma, Artin approximation step (étaleness): the truncations `eB`

Part of the proof of the equivariant étale chart lemma for `D(M)`-actions at a closed point (local
structure in the sense of Alper–Hall–Rydh), used for **Theorem 6.8** of Algebraic Magnetism.

`eB_equiv`: for `G = Q_A/(F)`, `S` étale over `G` with a maximal ideal `q` over `𝔴` with trivial
residue extension, `S/q^j ≃ Ξ/(F', 𝔫^j)`.
-/

open TensorProduct

universe u

namespace AlgMag.ChartS5

variable {P₀ P A Rh : Type*} [CommRing P₀] [CommRing P] [CommRing A] [CommRing Rh] [Algebra P₀ P]
  [Algebra P₀ A] [Algebra P₀ Rh] {s : ℕ} (θ : A →ₐ[P₀] Rh) (𝔫 : Ideal (P ⊗[P₀] Rh)) [𝔫.IsMaximal]
  (F : Fin s → P ⊗[P₀] A)
  {S : Type*} [CommRing S] [Algebra (P ⊗[P₀] A ⧸ Ideal.span (Set.range F)) S]
  [Algebra.Etale (P ⊗[P₀] A ⧸ Ideal.span (Set.range F)) S] (q : Ideal S) [q.IsMaximal]

/-- `𝔴 ⊂ G`. -/
noncomputable abbrev wIdeal : Ideal (P ⊗[P₀] A ⧸ Ideal.span (Set.range F)) :=
  (𝔫.comap (gQ (P := P) θ)).map (Ideal.Quotient.mk (Ideal.span (Set.range F)))

/-- **eB**. -/
noncomputable def eB_equiv [(wIdeal θ 𝔫 F).IsMaximal]
    (hq : q.comap (algebraMap _ S) = wIdeal θ 𝔫 F)
    (hres : Function.Surjective ((Ideal.Quotient.mk q).comp
      (algebraMap (P ⊗[P₀] A ⧸ Ideal.span (Set.range F)) S))) (j : ℕ)
    (h : (𝔫 ^ j).comap (gQ (P := P) θ) = (𝔫.comap (gQ (P := P) θ)) ^ j)
    (hs : Function.Surjective ((Ideal.Quotient.mk (𝔫 ^ j)).comp (gQ (P := P) θ))) :
    (S ⧸ q ^ j) ≃+* Localization.AtPrime 𝔫 ⧸
        (Ideal.span (Set.range fun ℓ => algebraMap (P ⊗[P₀] Rh) (Localization.AtPrime 𝔫)
            (gQ θ (F ℓ))) ⊔ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔫) ^ j) :=
  have hb := quot_pow_bijective_of_etale (wIdeal θ 𝔫 F) q hq hres j
  (truncEquiv (algebraMap _ S) (wIdeal θ 𝔫 F) q j hb.1 hb.2).symm.trans
    (quotient_trunc_equiv θ 𝔫 F j h hs)

lemma eB_equiv_algebraMap [(wIdeal θ 𝔫 F).IsMaximal]
    (hq : q.comap (algebraMap _ S) = wIdeal θ 𝔫 F)
    (hres : Function.Surjective ((Ideal.Quotient.mk q).comp
      (algebraMap (P ⊗[P₀] A ⧸ Ideal.span (Set.range F)) S))) (j : ℕ)
    (h : (𝔫 ^ j).comap (gQ (P := P) θ) = (𝔫.comap (gQ (P := P) θ)) ^ j)
    (hs : Function.Surjective ((Ideal.Quotient.mk (𝔫 ^ j)).comp (gQ (P := P) θ)))
    (y : P ⊗[P₀] A) :
    eB_equiv θ 𝔫 F q hq hres j h hs
        (Ideal.Quotient.mk (q ^ j) (algebraMap (P ⊗[P₀] A ⧸ Ideal.span (Set.range F)) S (Ideal.Quotient.mk (Ideal.span (Set.range F)) y))) =
      Ideal.Quotient.mk _ (algebraMap (P ⊗[P₀] Rh) (Localization.AtPrime 𝔫) (gQ θ y)) := by
  have hb := quot_pow_bijective_of_etale (wIdeal θ 𝔫 F) q hq hres j
  have e : (truncEquiv (algebraMap _ S) (wIdeal θ 𝔫 F) q j hb.1 hb.2).symm
      (Ideal.Quotient.mk (q ^ j) (algebraMap (P ⊗[P₀] A ⧸ Ideal.span (Set.range F)) S (Ideal.Quotient.mk (Ideal.span (Set.range F)) y))) =
      Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.span (Set.range F)) y) :=
    (RingEquiv.symm_apply_eq _).2 rfl
  change quotient_trunc_equiv θ 𝔫 F j h hs
    ((truncEquiv (algebraMap _ S) (wIdeal θ 𝔫 F) q j hb.1 hb.2).symm _) = _
  rw [e]
  rfl

/-- `eB` for a ring map `ι : G → S`, étale, not an instance. -/
theorem exists_eB {S' : Type*} [CommRing S'] (ι : (P ⊗[P₀] A ⧸ Ideal.span (Set.range F)) →+* S')
    (hι : ι.Etale) (q' : Ideal S') [q'.IsMaximal] [(wIdeal θ 𝔫 F).IsMaximal]
    (hq : q'.comap ι = wIdeal θ 𝔫 F) (hres : Function.Surjective ((Ideal.Quotient.mk q').comp ι))
    (hT : ∀ j, (𝔫 ^ j).comap (gQ (P := P) θ) = (𝔫.comap (gQ (P := P) θ)) ^ j ∧
      Function.Surjective ((Ideal.Quotient.mk (𝔫 ^ j)).comp (gQ (P := P) θ))) :
    ∃ eB : ∀ j, (S' ⧸ q' ^ j) ≃+* Localization.AtPrime 𝔫 ⧸
        (Ideal.span (Set.range fun ℓ => algebraMap (P ⊗[P₀] Rh) (Localization.AtPrime 𝔫)
            (gQ θ (F ℓ))) ⊔ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔫) ^ j),
      ∀ j y, eB j (Ideal.Quotient.mk _ (ι (Ideal.Quotient.mk _ y))) =
        Ideal.Quotient.mk _ (algebraMap (P ⊗[P₀] Rh) (Localization.AtPrime 𝔫) (gQ θ y)) := by
  letI := ι.toAlgebra
  haveI : Algebra.Etale (P ⊗[P₀] A ⧸ Ideal.span (Set.range F)) S' := hι
  exact ⟨fun j => eB_equiv θ 𝔫 F q' hq hres j (hT j).1 (hT j).2, fun j y =>
    eB_equiv_algebraMap θ 𝔫 F q' hq hres j (hT j).1 (hT j).2 y⟩

section EA

variable {R Cj B' : Type*} [CommRing R] [CommRing Cj] [CommRing B'] [Algebra Cj B'] [Algebra.Etale Cj B']
  (r : R →+* B') (hr : Function.Surjective r) (p : Ideal R) (𝔞 : Ideal Cj) [𝔞.IsMaximal]
  (𝔟 : Ideal B') [𝔟.IsMaximal] (hp : 𝔟.comap r = p) (h𝔞 : 𝔟.comap (algebraMap Cj B') = 𝔞)
  (hres' : Function.Surjective ((Ideal.Quotient.mk 𝔟).comp (algebraMap Cj B'))) (j : ℕ)
  (hker : RingHom.ker r ≤ p ^ j)

include hr hp hker in
lemma comap_pow_of_surjective : (𝔟 ^ j).comap r = p ^ j := by
  have h1 : 𝔟 = p.map r := by
    rw [← hp]; exact (Ideal.map_comap_of_surjective r hr 𝔟).symm
  rw [h1, ← Ideal.map_pow, Ideal.comap_map_of_surjective' r hr]
  exact sup_eq_left.2 hker

/-- **eA**, the étale step: `Γ(V)/p^j ≃ Γ(Z_j)/𝔞^j`, where `V ×_X Z_j` has ring `B'`, closed in `V`
with ideal in `p^j` and étale over `Z_j`. -/
noncomputable def eA_core : (R ⧸ p ^ j) ≃+* Cj ⧸ 𝔞 ^ j :=
  have hb := quot_pow_bijective_of_etale 𝔞 𝔟 h𝔞 hres' j
  (truncEquiv r p 𝔟 j (comap_pow_of_surjective r hr p 𝔟 hp j hker)
    (Ideal.Quotient.mk_surjective.comp hr)).trans
    (truncEquiv (algebraMap Cj B') 𝔞 𝔟 j hb.1 hb.2).symm

end EA

end AlgMag.ChartS5

#print axioms AlgMag.ChartS5.eB_equiv
#print axioms AlgMag.ChartS5.eA_core
#print axioms AlgMag.ChartS5.exists_eB
