/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartS5EB

/-!
# Chart lemma, Artin approximation step: rings for the truncations `eA`, `eC`

Part of the proof of the equivariant étale chart lemma for `D(M)`-actions at a closed point (local
structure in the sense of Alper–Hall–Rydh), used for **Theorem 6.8** of Algebraic Magnetism.
-/

universe u

namespace AlgMag.ChartS5

/-- A ring with a maximal nil ideal is local. -/
lemma isLocalRing_of_maximal_nil {R : Type*} [CommRing R] (I : Ideal R) [hI : I.IsMaximal]
    (h : ∀ x ∈ I, IsNilpotent x) : IsLocalRing R := by
  refine IsLocalRing.of_unique_max_ideal ⟨I, hI, fun J hJ => ?_⟩
  have hle : I ≤ J := fun x hx => by
    obtain ⟨n, hn⟩ := h x hx
    exact hJ.isPrime.mem_of_pow_mem n (hn ▸ J.zero_mem)
  exact (hI.eq_of_le hJ.ne_top hle).symm

section EC

variable {Q C : Type*} [CommRing Q] [CommRing C] (π : Q →+* C) (hπ : Function.Surjective π)
  {s : ℕ} (F : Fin s → Q) (hF : Ideal.span (Set.range F) = RingHom.ker π) (𝔲 : Ideal C)
  (𝔫 : Ideal Q) [h𝔫 : 𝔫.IsMaximal] (hn : 𝔲.comap π = 𝔫)

/-- `Q → Ξ/((F) + 𝔪^j)`. -/
noncomputable abbrev gΞ (j : ℕ) : Q →+* Localization.AtPrime 𝔫 ⧸
    (Ideal.span (Set.range fun ℓ => algebraMap Q (Localization.AtPrime 𝔫) (F ℓ)) ⊔
      IsLocalRing.maximalIdeal (Localization.AtPrime 𝔫) ^ j) :=
  (Ideal.Quotient.mk _).comp (algebraMap Q (Localization.AtPrime 𝔫))

include hF in
lemma gΞ_ker (j : ℕ) : ∀ q ∈ RingHom.ker π, q ∈ RingHom.ker (gΞ F 𝔫 j) := by
  rw [← hF]
  intro q hq
  have : Ideal.span (Set.range F) ≤ RingHom.ker (gΞ F 𝔫 j) := by
    rw [Ideal.span_le]
    rintro _ ⟨ℓ, rfl⟩
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left (Ideal.subset_span ⟨ℓ, rfl⟩))
  exact this hq

/-- `C → Ξ/((F) + 𝔪^j)`. -/
noncomputable def psiΞ (j : ℕ) : C →+* Localization.AtPrime 𝔫 ⧸
    (Ideal.span (Set.range fun ℓ => algebraMap Q (Localization.AtPrime 𝔫) (F ℓ)) ⊔
      IsLocalRing.maximalIdeal (Localization.AtPrime 𝔫) ^ j) :=
  RingHom.liftOfRightInverse π (Function.surjInv hπ) (Function.rightInverse_surjInv hπ)
    ⟨gΞ F 𝔫 j, fun q hq => gΞ_ker π F hF 𝔫 j q hq⟩

lemma psiΞ_π (j : ℕ) (q : Q) : psiΞ π hπ F hF 𝔫 j (π q) = gΞ F 𝔫 j q :=
  RingHom.liftOfRightInverse_comp_apply π (Function.surjInv hπ) (Function.rightInverse_surjInv hπ) _ q

include hπ hn in
lemma pow_eq_map (j : ℕ) : 𝔲 ^ j = (𝔫 ^ j).map π := by
  rw [Ideal.map_pow, ← hn, Ideal.map_comap_of_surjective π hπ]

/-- **`eC`**: `C/𝔲^j ≃ Ξ/((F) + 𝔪^j)`, for `C = Q/(F)`, `Ξ = Q_𝔫`. -/
noncomputable def eC (j : ℕ) : (C ⧸ 𝔲 ^ j) ≃+* Localization.AtPrime 𝔫 ⧸
    (Ideal.span (Set.range fun ℓ => algebraMap Q (Localization.AtPrime 𝔫) (F ℓ)) ⊔
      IsLocalRing.maximalIdeal (Localization.AtPrime 𝔫) ^ j) :=
  RingEquiv.ofBijective
    (Ideal.Quotient.lift (𝔲 ^ j) (psiΞ π hπ F hF 𝔫 j) (fun c hc => by
      rw [pow_eq_map π hπ 𝔲 𝔫 hn j] at hc
      obtain ⟨q, hq, rfl⟩ := (Ideal.mem_map_iff_of_surjective π hπ).1 hc
      rw [psiΞ_π]
      refine Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right ?_)
      exact (comap_localization_pow 𝔫 j).ge hq))
    (by
      constructor
      · refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
        obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
        obtain ⟨q, rfl⟩ := hπ c
        have h1 : gΞ F 𝔫 j q = 0 := (psiΞ_π π hπ F hF 𝔫 j q).symm.trans hy
        have h2 := mem_sup_of_map_mem (algebraMap Q (Localization.AtPrime 𝔫)) 𝔫 _ F j
          (comap_localization_pow 𝔫 j) (surjective_localization_pow 𝔫 j)
          (Ideal.Quotient.eq_zero_iff_mem.1 h1)
        obtain ⟨i, hi, a, ha, rfl⟩ := Submodule.mem_sup.1 h2
        refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
        rw [map_add]
        have h3 : π i = 0 := by
          have : i ∈ RingHom.ker π := hF ▸ hi
          exact this
        rw [h3, zero_add, pow_eq_map π hπ 𝔲 𝔫 hn j]
        exact Ideal.mem_map_of_mem _ ha
      · intro y
        obtain ⟨ξ, rfl⟩ := Ideal.Quotient.mk_surjective y
        obtain ⟨q, hq⟩ := surjective_localization_pow 𝔫 j (Ideal.Quotient.mk _ ξ)
        refine ⟨Ideal.Quotient.mk _ (π q), ?_⟩
        change psiΞ π hπ F hF 𝔫 j (π q) = _
        rw [psiΞ_π]
        exact Ideal.Quotient.eq.2 (Ideal.mem_sup_right (Ideal.Quotient.eq.1 hq)))

lemma eC_mk (j : ℕ) (q : Q) : eC π hπ F hF 𝔲 𝔫 hn j (Ideal.Quotient.mk _ (π q)) =
    Ideal.Quotient.mk _ (algebraMap Q (Localization.AtPrime 𝔫) q) :=
  psiΞ_π π hπ F hF 𝔫 j q

end EC

section Pkg

variable {R B' Cj C : Type*} [CommRing R] [CommRing B'] [CommRing Cj] [CommRing C]
  (r : R →+* B') (hr : Function.Surjective r) (c₀ : Cj →+* B') (hc₀ : c₀.Etale)
  (𝔟 : Ideal B') [h𝔟 : 𝔟.IsMaximal] (hres : Function.Surjective ((Ideal.Quotient.mk 𝔟).comp c₀))

include hc₀ h𝔟 hres in
/-- `Γ(Z_j) → B'/𝔟^j` is bijective on truncations. -/
lemma c0_trunc (j : ℕ) : (𝔟 ^ j).comap c₀ = (𝔟.comap c₀) ^ j ∧
    Function.Surjective ((Ideal.Quotient.mk (𝔟 ^ j)).comp c₀) := by
  letI := c₀.toAlgebra
  haveI : Algebra.Etale Cj B' := hc₀
  haveI : (𝔟.comap (algebraMap Cj B')).IsMaximal := comap_isMaximal_of_surj (algebraMap Cj B') 𝔟 hres
  exact quot_pow_bijective_of_etale (𝔟.comap (algebraMap Cj B')) 𝔟 rfl hres j

include hc₀ hres in
/-- A map killing `𝔞^j` extends to `B'`, killing `𝔟^j`. -/
theorem exists_trunc_lift {D : Type*} [CommRing D] (j : ℕ) (g₀ : Cj →+* D)
    (hg : ∀ z ∈ (𝔟.comap c₀) ^ j, g₀ z = 0) :
    ∃ g' : B' →+* D, (∀ z, g' (c₀ z) = g₀ z) ∧ ∀ b ∈ 𝔟 ^ j, g' b = 0 := by
  obtain ⟨h1, h2⟩ := c0_trunc c₀ hc₀ 𝔟 hres j
  let E := truncEquiv c₀ (𝔟.comap c₀) 𝔟 j h1 h2
  let g₁ : (Cj ⧸ (𝔟.comap c₀) ^ j) →+* D := Ideal.Quotient.lift _ g₀ hg
  refine ⟨(g₁.comp E.symm.toRingHom).comp (Ideal.Quotient.mk _), fun z => ?_, fun b hb => ?_⟩
  · have e : E.symm (Ideal.Quotient.mk _ (c₀ z)) = Ideal.Quotient.mk _ z := by
      rw [RingEquiv.symm_apply_eq]; rfl
    change g₁ (E.symm (Ideal.Quotient.mk _ (c₀ z))) = _
    rw [e]; rfl
  · change g₁ (E.symm (Ideal.Quotient.mk _ b)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hb, map_zero, map_zero]

variable (rj : C →+* Cj) (hrj : Function.Surjective rj) (𝔲 : Ideal C)
  (hu : (𝔟.comap c₀).comap rj = 𝔲) (p : Ideal R) (hp : 𝔟.comap r = p)

include hr hc₀ hres hrj hu hp in
/-- **Artin approximation step, formal étaleness**, on rings: `R/p^j ≃ C/𝔲^j`, where `V ×_X Z_j` has ring `B'`. -/
theorem ea_pkg (j : ℕ) (hker : RingHom.ker r ≤ p ^ j) (hkj : RingHom.ker rj ≤ 𝔲 ^ j) :
    ∃ E : (R ⧸ p ^ j) ≃+* (C ⧸ 𝔲 ^ j), ∀ a c, r a - c₀ (rj c) ∈ 𝔟 ^ j →
      E (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ c := by
  obtain ⟨h1, h2⟩ := c0_trunc c₀ hc₀ 𝔟 hres j
  haveI : (𝔟.comap c₀).IsMaximal := comap_isMaximal_of_surj c₀ 𝔟 hres
  have h3 := comap_pow_of_surjective r hr p 𝔟 hp j hker
  have h4 : ((𝔟.comap c₀) ^ j).comap rj = 𝔲 ^ j :=
    comap_pow_of_surjective rj hrj 𝔲 (𝔟.comap c₀) hu j hkj
  let E₁ := truncEquiv r p 𝔟 j h3 (Ideal.Quotient.mk_surjective.comp hr)
  let E₂ := truncEquiv c₀ (𝔟.comap c₀) 𝔟 j h1 h2
  let E₃ := truncEquiv rj 𝔲 ((𝔟.comap c₀)) j h4 (Ideal.Quotient.mk_surjective.comp hrj)
  refine ⟨(E₁.trans E₂.symm).trans E₃.symm, fun a c h => ?_⟩
  change E₃.symm (E₂.symm (E₁ (Ideal.Quotient.mk _ a))) = _
  rw [RingEquiv.symm_apply_eq, RingEquiv.symm_apply_eq]
  exact Ideal.Quotient.eq.2 h

end Pkg

end AlgMag.ChartS5

#print axioms AlgMag.ChartS5.eC
#print axioms AlgMag.ChartS5.ea_pkg
