/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.FromR1R2
import AlgMag.Reductive.PushCocharacter
import AlgMag.Reductive.OpenCellPoints
import AlgMag.Reductive.RegularSlice

/-!
# Transport of attractors and dynamic subgroups by a normalizing point

Let `n ∈ G(k)` normalize `T` with automorphism `σ` of `X`.
* `conj_mem_attractorSubgroup_comap`: `n G^N(k) n⁻¹ ⊆ G^{σ⁻¹N}(k)`, i.e. `x ∈ G^N(k)` gives
  `n x n⁻¹ ∈ G^{N.comap σ}(k)` (conjugation by `n` moves the weight `χ` to `σχ`).
* `conj_mem_parabolic_inv`: if `σ` turns `λ = λ_ψ` into `-λ` (`⟨σχ, ψ⟩ = -⟨χ, ψ⟩`), then
  `n P(λ)(k) n⁻¹ ⊆ P(-λ)(k)`.
* `not_mem_openCell`: in that situation, if `U(λ)(k) ≠ 1` then `n ∉ U(-λ)(k)·P(λ)(k)`, the
  (⇒) direction of the rank-one Bruhat statement (`n·1 ∉ Ω`).
-/

suppress_compilation

open Magnetism TauCeti TauCeti.Cocharacter WithConv AlgMag.Weyl

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)

/-- `σ` as an additive endomorphism of `Additive X`. -/
abbrev addAut (σ : X ≃* X) : Additive X →+ Additive X := σ.toMonoidHom.toAdditive

lemma mapValue_ofId_self' (g : WithConv (H →ₐ[k] k)) :
    AlgHom.mapValue (H := H) (Algebra.ofId k k) g = g := by
  apply WithConv.ofConv_injective
  ext x
  rw [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply]
  rfl

/-- `λ_{ψ⁻¹} = λ_ψ⁻¹` (port of OpenCellGen `cocharacter_inv`, which does not build now). -/
theorem cocharacter_inv' (ψ : X →* Multiplicative ℤ) :
    π.cocharacter ψ⁻¹ = (π.cocharacter ψ).oppositeCocharacter := by
  have key : ∀ c : MonoidAlgebra k X,
      (BialgHom.id k (MonoidAlgebra k X)).cocharacter ψ⁻¹ c =
        LaurentPolynomial.invert ((BialgHom.id k (MonoidAlgebra k X)).cocharacter ψ c) := by
    intro c
    induction c using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
    | single χ r =>
      rw [BialgHom.cocharacter_id_single, BialgHom.cocharacter_id_single]
      rw [LaurentPolynomial.single_eq_C_mul_T, LaurentPolynomial.single_eq_C_mul_T, map_mul,
        LaurentPolynomial.invert_C, LaurentPolynomial.invert_T]
      simp
  apply DFunLike.ext
  intro h
  rw [BialgHom.oppositeCocharacter_apply, ← BialgHom.cocharacter_id_comp π ψ⁻¹,
    ← BialgHom.cocharacter_id_comp π ψ, BialgHom.comp_apply, BialgHom.comp_apply, key]

/-- **Transport of attractors**: `x ∈ G^N(k) ⇒ n x n⁻¹ ∈ G^{N.comap σ}(k)`. -/
theorem conj_mem_attractorSubgroup_comap {n : WithConv (H →ₐ[k] k)} {σ : X ≃* X}
    (hn : IsNormalizingWith π k n σ) (N : Magnet (Additive X)) {x : WithConv (H →ₐ[k] k)}
    (hx : x ∈ attractorSubgroup π N k) :
    n * x * n⁻¹ ∈ attractorSubgroup π (N.comap (addAut σ)) k := by
  rw [mem_attractorSubgroup] at hx ⊢
  have hconj : n * x * n⁻¹ = toConv (x.ofConv.comp (HopfAlgebra.pointConjugationAlgHom n)) := by
    rw [HopfAlgebra.comp_pointConjugationAlgHom, mapValue_ofId_self']
  rw [hconj, ofConv_toConv, magnetIdeal, Ideal.span_le]
  simp only [Set.iUnion_subset_iff]
  intro χ hχ a ha
  have hmem := pointConjugation_mem_torusGrading π hn ha
  have hnot : Additive.ofMul (σ (Additive.toMul χ)) ∉ N := hχ
  have := hx (mem_magnetIdeal_of_notMem hnot hmem)
  simpa [RingHom.mem_ker] using this

/-- **Transport of the parabolic**: if `⟨σχ, ψ⟩ = -⟨χ, ψ⟩`, then `n P(λ_ψ)(k) n⁻¹ ⊆ P(λ_ψ⁻¹)(k)`. -/
theorem conj_mem_parabolic_inv {n : WithConv (H →ₐ[k] k)} {σ : X ≃* X}
    (hn : IsNormalizingWith π k n σ) {ψ : X →* Multiplicative ℤ}
    (hσψ : ∀ χ : Additive X, pairingHom ψ (addAut σ χ) = - pairingHom ψ χ)
    {x : WithConv (H →ₐ[k] k)} (hx : x ∈ parabolic k (π.cocharacter ψ)) :
    n * x * n⁻¹ ∈ parabolic k (π.cocharacter ψ⁻¹) := by
  rw [← magnetIdeal_torusGrading_comap_nat_le_ker_iff] at hx ⊢
  have h := conj_mem_attractorSubgroup_comap π hn _ ((mem_attractorSubgroup π).2 hx)
  rw [mem_attractorSubgroup] at h
  have heq : (natMagnet.comap (pairingHom ψ)).comap (addAut σ) =
      natMagnet.comap (pairingHom ψ⁻¹) := by
    ext χ
    simp only [AddSubmonoid.mem_comap, pairingHom_inv]
    rw [hσψ]
  rwa [heq] at h

/-- **(⇒) of the rank-one Bruhat statement**: if `σ` turns `λ` into `-λ` and `U(λ)(k) ≠ 1`, then
`n` is not in `U(-λ)(k) · P(λ)(k)` (the `k`-points of the open cell `Ω`). -/
theorem not_mem_openCell {n : WithConv (H →ₐ[k] k)} {σ : X ≃* X}
    (hn : IsNormalizingWith π k n σ) {ψ : X →* Multiplicative ℤ}
    (hσψ : ∀ χ : Additive X, pairingHom ψ (addAut σ χ) = - pairingHom ψ χ)
    (hU : ∃ u ∈ unipotent k (π.cocharacter ψ), u ≠ 1)
    {v b : WithConv (H →ₐ[k] k)} (hv : v ∈ unipotent k (π.cocharacter ψ⁻¹))
    (hb : b ∈ parabolic k (π.cocharacter ψ)) : n ≠ v * b := by
  rintro rfl
  obtain ⟨u, hu, hu1⟩ := hU
  have h1 := conj_mem_parabolic_inv π hn hσψ (unipotent_le_parabolic hu)
  have h2 : b * u * b⁻¹ ∈ unipotent k (π.cocharacter ψ) := conj_mem_unipotent hb hu
  have h3 : b * u * b⁻¹ ∈ parabolic k (π.cocharacter ψ⁻¹) := by
    have hv' := unipotent_le_parabolic hv
    have : b * u * b⁻¹ = v⁻¹ * (v * b * u * (v * b)⁻¹) * v := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hv') h1) hv'
  have hopp : π.cocharacter ψ = (π.cocharacter ψ⁻¹).oppositeCocharacter := by
    rw [← cocharacter_inv', inv_inv]
  have hbot := unipotent_opposite_inf_parabolic (A := k) (π.cocharacter ψ⁻¹)
  rw [← hopp] at hbot
  have : b * u * b⁻¹ ∈ (⊥ : Subgroup _) := hbot ▸ ⟨h2, h3⟩
  rw [Subgroup.mem_bot] at this
  apply hu1
  have : u = b⁻¹ * (b * u * b⁻¹) * b := by group
  rw [this, ‹b * u * b⁻¹ = 1›]; group

end AlgMag.Reductive
