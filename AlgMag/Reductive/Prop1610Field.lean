/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.TorusBaseChange

/-!
# Proposition 16.10 (ii) of Algebraic Magnetism over a field

Let `G = Spec H` be a smooth affine group over a field `k` with an action of the split torus
`D(X)`, and `f` a magnet map. If `N ⊆ f⁻¹(ℕ)` contains the same tangent weights as `f⁻¹(ℕ)` and
`P(λ_f)` is geometrically connected, then `G^N = P(λ_f)`.

The proof base changes to an algebraic closure `k̄`: attractor ideals and tangent weights base
change (`AlgMag.Reductive.magnetIdeal_baseChange`, `tangentWeights_baseChange_subset`), the
statement over `k̄` is `magnetIdeal_eq_parabolic_of_isAlgClosed`, and equality of ideals
descends along the faithfully flat `k → k̄`.
-/

suppress_compilation

open Magnetism TauCeti TauCeti.Cocharacter
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type*}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X) (ψ : X →* Multiplicative ℤ)

/-- An ideal `I` of `H` is recovered from its extension to `K ⊗[k] H`. -/
lemma mem_of_one_tmul_mem_map {K : Type*} [Field K] [Algebra k K] {I : Ideal H} {x : H}
    (hx : (1 : K) ⊗ₜ[k] x ∈ I.map (Algebra.TensorProduct.includeRight : H →ₐ[k] K ⊗[k] H)) :
    x ∈ I := by
  let e := Algebra.TensorProduct.tensorQuotientEquiv (R := k) K H K I
  have h0 : e.symm (Ideal.Quotient.mk _ ((1 : K) ⊗ₜ[k] x)) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  rw [show Ideal.Quotient.mk _ ((1 : K) ⊗ₜ[k] x) = ((1 : K) ⊗ₜ[k] x : K ⊗[k] H) from rfl,
    Algebra.TensorProduct.tensorQuotientEquiv_symm_apply_tmul] at h0
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight : H ⧸ I →ₐ[k] K ⊗[k] (H ⧸ I)) :=
    Algebra.TensorProduct.includeRight_injective (FaithfulSMul.algebraMap_injective k K)
  have : Ideal.Quotient.mk I x = 0 := hinj (by
    rw [Algebra.TensorProduct.includeRight_apply, map_zero]; exact h0)
  exact Ideal.Quotient.eq_zero_iff_mem.mp this

/-- **Proposition 16.10 (ii) of Algebraic Magnetism, over a field.** Let `G` be smooth, let
`N ⊆ f⁻¹(ℕ)` be a magnet containing the same tangent weights as `f⁻¹(ℕ)`, and suppose `P(λ_f)`
geometrically connected. Then `G^N = P(λ_f)`. -/
theorem magnetIdeal_eq_parabolic_of_field [Algebra.Smooth k H]
    {N : Magnet (Additive X)} (hN : N ≤ natMagnet.comap (pairingHom ψ))
    (hW : ∀ χ ∈ tangentWeights π k, χ ∈ N ↔ 0 ≤ pairingHom ψ χ)
    (hP : ConnectedSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k]
      (H ⧸ (parabolicDefiningHopfIdeal (π.cocharacter ψ)).toIdeal)))) :
    magnetIdeal (torusGrading π) N =
      (parabolicDefiningHopfIdeal (π.cocharacter ψ)).toIdeal := by
  let K := AlgebraicClosure k
  let πK := torusBaseChange K π
  have hPmap : ∀ πₒ : H →ₐc[k] MonoidAlgebra k X,
      (parabolicDefiningHopfIdeal (πₒ.cocharacter ψ)).toIdeal =
        magnetIdeal (torusGrading πₒ) (natMagnet.comap (pairingHom ψ)) :=
    fun πₒ => (magnetIdeal_torusGrading_comap_nat (π := πₒ) (ψ := ψ)).symm
  have hPK : (parabolicDefiningHopfIdeal (πK.cocharacter ψ)).toIdeal =
      (parabolicDefiningHopfIdeal (π.cocharacter ψ)).toIdeal.map
        (Algebra.TensorProduct.includeRight : H →ₐ[k] K ⊗[k] H) := by
    rw [← magnetIdeal_torusGrading_comap_nat, magnetIdeal_baseChange, hPmap]
  have hWK : ∀ χ ∈ tangentWeights πK K, χ ∈ N ↔ 0 ≤ pairingHom ψ χ :=
    fun χ hχ => hW χ (tangentWeights_baseChange_subset K π hχ)
  have hconn : ConnectedSpace
      (PrimeSpectrum ((K ⊗[k] H) ⧸ (parabolicDefiningHopfIdeal (πK.cocharacter ψ)).toIdeal)) := by
    rw [hPK]
    exact (PrimeSpectrum.homeomorphOfRingEquiv
      (Algebra.TensorProduct.tensorQuotientEquiv (R := k) K H K _).toRingEquiv).connectedSpace_iff.mp
      hP
  have key := magnetIdeal_eq_parabolic_of_isAlgClosed πK ψ hN hWK hconn
  rw [magnetIdeal_baseChange, hPK] at key
  apply le_antisymm
  · intro x hx
    apply mem_of_one_tmul_mem_map (k := k) (H := H) (K := K)
    rw [← key]
    exact Ideal.mem_map_of_mem _ hx
  · rw [hPmap]
    exact magnetIdeal_anti _ hN

/-- `P(λ_f)` is geometrically connected when the Levi subgroup `Z(λ_f)` is, for `G` smooth. -/
theorem connectedSpace_parabolic_baseChange_of_levi [Algebra.Smooth k H]
    (hZ : ConnectedSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k]
      (H ⧸ (leviDefiningHopfIdeal (π.cocharacter ψ)).toIdeal)))) :
    ConnectedSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k]
      (H ⧸ (parabolicDefiningHopfIdeal (π.cocharacter ψ)).toIdeal))) := by
  let K := AlgebraicClosure k
  let πK := torusBaseChange K π
  have hmap : ∀ M : Magnet ℤ,
      magnetIdeal (torusGrading πK) (M.comap (pairingHom ψ)) =
        (magnetIdeal (torusGrading π) (M.comap (pairingHom ψ))).map
          (Algebra.TensorProduct.includeRight : H →ₐ[k] K ⊗[k] H) :=
    fun M => magnetIdeal_baseChange K π _
  have hZK : ConnectedSpace (PrimeSpectrum
      ((K ⊗[k] H) ⧸ (leviDefiningHopfIdeal (πK.cocharacter ψ)).toIdeal)) := by
    rw [← magnetIdeal_torusGrading_comap_bot, hmap, magnetIdeal_torusGrading_comap_bot]
    exact (PrimeSpectrum.homeomorphOfRingEquiv
      (Algebra.TensorProduct.tensorQuotientEquiv (R := k) K H K _).toRingEquiv).connectedSpace_iff.mp
      hZ
  have hPK := connectedSpace_parabolic_of_levi (πK.cocharacter ψ) hZK
  rw [← magnetIdeal_torusGrading_comap_nat, hmap, magnetIdeal_torusGrading_comap_nat] at hPK
  exact (PrimeSpectrum.homeomorphOfRingEquiv
    (Algebra.TensorProduct.tensorQuotientEquiv (R := k) K H K _).toRingEquiv).connectedSpace_iff.mpr
    hPK

/-- **Proposition 16.10 (ii) of Algebraic Magnetism, over a field, from the Levi subgroup.** Let
`G` be smooth, `N ⊆ f⁻¹(ℕ)` a magnet containing the same tangent weights as `f⁻¹(ℕ)`, and
suppose `Z(λ_f)` geometrically connected. Then `G^N = P(λ_f)`. -/
theorem magnetIdeal_eq_parabolic_of_field_of_levi [Algebra.Smooth k H]
    {N : Magnet (Additive X)} (hN : N ≤ natMagnet.comap (pairingHom ψ))
    (hW : ∀ χ ∈ tangentWeights π k, χ ∈ N ↔ 0 ≤ pairingHom ψ χ)
    (hZ : ConnectedSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k]
      (H ⧸ (leviDefiningHopfIdeal (π.cocharacter ψ)).toIdeal)))) :
    magnetIdeal (torusGrading π) N =
      (parabolicDefiningHopfIdeal (π.cocharacter ψ)).toIdeal :=
  magnetIdeal_eq_parabolic_of_field π ψ hN hW
    (connectedSpace_parabolic_baseChange_of_levi π ψ hZ)

end AlgMag.Reductive
