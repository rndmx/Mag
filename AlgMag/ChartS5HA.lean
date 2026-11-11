/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartS5Trunc

/-!
# Chart lemma, Artin approximation step: `hA` of `QA_trunc` for `A'` étale over `P₀`

Part of the proof of the equivariant étale chart lemma for `D(M)`-actions at a closed point (local
structure in the sense of Alper–Hall–Rydh), used for **Theorem 6.8** of Algebraic Magnetism.
-/

universe u

namespace AlgMag.ChartS5

section HA

variable {P₀ A' : Type u} [CommRing P₀] [IsNoetherianRing P₀] [CommRing A'] [Algebra P₀ A']
  [Algebra.Etale P₀ A'] (𝔭 : Ideal P₀) [𝔭.IsMaximal] (θ : A' →ₐ[P₀] AdicCompletion 𝔭 P₀)

/-- The kernel of `eval_1`, the maximal ideal `p̂` of `P̂₀`. -/
local notation "ph" => RingHom.ker (AdicCompletion.evalₐ 𝔭 1)

lemma eval_algebraMap (j : ℕ) (b : P₀) :
    AdicCompletion.evalₐ 𝔭 j (algebraMap P₀ (AdicCompletion 𝔭 P₀) b) = Ideal.Quotient.mk _ b :=
  (AdicCompletion.evalₐ 𝔭 j).commutes b

/-- **The input `hA` of `QA_trunc`**: `A' → P̂₀/p̂^j` is onto with kernel `𝔮^j`, for `A'` étale over
`P₀` and `𝔮 = θ⁻¹(p̂)`. -/
theorem hA_of_etale (j : ℕ) :
    ((ph) ^ j).comap θ = ((ph).comap θ) ^ j ∧
      Function.Surjective ((Ideal.Quotient.mk ((ph) ^ j)).comp (θ : A' →+* AdicCompletion 𝔭 P₀)) := by
  have hθb : ∀ b : P₀, θ (algebraMap P₀ A' b) = algebraMap P₀ (AdicCompletion 𝔭 P₀) b :=
    fun b => θ.commutes b
  have hker : ∀ (j : ℕ) (b : P₀), algebraMap P₀ (AdicCompletion 𝔭 P₀) b ∈ (ph) ^ j ↔ b ∈ 𝔭 ^ j := by
    intro j b
    rw [← ker_evalₐ_eq_pow, RingHom.mem_ker]
    change AdicCompletion.evalₐ 𝔭 j (algebraMap P₀ _ b) = 0 ↔ _
    rw [eval_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
  have happ : ∀ (j : ℕ) (y : AdicCompletion 𝔭 P₀), ∃ b : P₀, y - algebraMap P₀ _ b ∈ (ph) ^ j := by
    intro j y
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ 𝔭 j y)
    refine ⟨b, ?_⟩
    rw [← ker_evalₐ_eq_pow, RingHom.mem_ker]
    change AdicCompletion.evalₐ 𝔭 j (y - algebraMap P₀ _ b) = 0
    rw [map_sub, eval_algebraMap, hb, sub_self]
  let 𝔮 : Ideal A' := (ph).comap θ
  have hq1 : ∀ a : A', ∃ b : P₀, a - algebraMap P₀ A' b ∈ 𝔮 := fun a => by
    obtain ⟨b, hb⟩ := happ 1 (θ a)
    refine ⟨b, ?_⟩
    change θ (a - algebraMap P₀ A' b) ∈ ph
    rw [map_sub, hθb]
    simpa using hb
  have hcq : 𝔮.comap (algebraMap P₀ A') = 𝔭 := by
    ext b
    change θ (algebraMap P₀ A' b) ∈ ph ↔ _
    rw [hθb]
    simpa using hker 1 b
  have hsurjq : Function.Surjective ((Ideal.Quotient.mk 𝔮).comp (algebraMap P₀ A')) := fun c => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨b, hb⟩ := hq1 a
    exact ⟨b, (Ideal.Quotient.eq.2 hb).symm⟩
  haveI h𝔮 : 𝔮.IsMaximal := by
    have hk : RingHom.ker ((Ideal.Quotient.mk 𝔮).comp (algebraMap P₀ A')) = 𝔭 := by
      rw [← hcq]; ext b
      change Ideal.Quotient.mk 𝔮 (algebraMap P₀ A' b) = 0 ↔ _
      rw [Ideal.Quotient.eq_zero_iff_mem]; rfl
    have hf : IsField (A' ⧸ 𝔮) := by
      have e := RingHom.quotientKerEquivOfSurjective hsurjq
      have : IsField (P₀ ⧸ RingHom.ker ((Ideal.Quotient.mk 𝔮).comp (algebraMap P₀ A'))) := by
        rw [hk]; exact Ideal.Quotient.maximal_ideal_iff_isField_quotient 𝔭 |>.1 inferInstance
      exact MulEquiv.isField this e.symm.toMulEquiv
    exact Ideal.Quotient.maximal_ideal_iff_isField_quotient 𝔮 |>.2 hf
  obtain ⟨h1, h2⟩ := quot_pow_bijective_of_etale (A := P₀) (B := A') 𝔭 𝔮 hcq hsurjq j
  have hle : 𝔮 ^ j ≤ ((ph) ^ j).comap θ := by
    have : (𝔮 ^ j).map (θ : A' →+* AdicCompletion 𝔭 P₀) ≤ (ph) ^ j := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono Ideal.map_comap_le j
    exact Ideal.map_le_iff_le_comap.1 this
  refine ⟨le_antisymm ?_ hle, fun c => ?_⟩
  · intro a ha
    obtain ⟨b, hb⟩ := h2 (Ideal.Quotient.mk _ a)
    have hab : a - algebraMap P₀ A' b ∈ 𝔮 ^ j := Ideal.Quotient.eq.1 hb.symm
    have h3 : θ (a - algebraMap P₀ A' b) ∈ (ph) ^ j := hle hab
    have h4 : θ (algebraMap P₀ A' b) ∈ (ph) ^ j := by
      have h5 : θ (algebraMap P₀ A' b) = θ a - θ (a - algebraMap P₀ A' b) := by
        rw [map_sub]; ring
      rw [h5]
      exact sub_mem ha h3
    rw [hθb, hker] at h4
    have h6 : algebraMap P₀ A' b ∈ 𝔮 ^ j := by
      rw [← h1] at h4
      exact h4
    have : a = (a - algebraMap P₀ A' b) + algebraMap P₀ A' b := by ring
    rw [this]
    exact add_mem hab h6
  · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨b, hb⟩ := happ j y
    refine ⟨algebraMap P₀ A' b, ?_⟩
    change Ideal.Quotient.mk _ (θ (algebraMap P₀ A' b)) = _
    rw [hθb]
    exact (Ideal.Quotient.eq.2 hb).symm

end HA

end AlgMag.ChartS5

#print axioms AlgMag.ChartS5.hA_of_etale
