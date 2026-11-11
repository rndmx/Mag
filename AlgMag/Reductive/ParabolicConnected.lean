/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.ParabolicAttractor
import TauCeti.Algebra.AlgebraicGroup.Dynamic.Unipotent.Connected
import TauCeti.RingTheory.Idempotents.Connected.ScalarExtension
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Connectedness of `P(λ)` from connectedness of the Levi subgroup

Over an algebraically closed field `k`, the spectrum of `B ⊗[k] A` is connected when those of `A`
and `B` are, `B` being reduced of finite type (`connectedSpace_tensorProduct_of_isAlgClosed`).
With the Levi decomposition `O(P(λ)) ≅ O(U(λ)) ⊗ O(Z(λ))` (Tau Ceti
`parabolicCoordinateAlgEquiv`) and the connectedness of `U(λ)` (Tau Ceti), connectedness of
`P(λ)` reduces to connectedness of the Levi subgroup `Z(λ) = Z_G(λ)`.
-/

suppress_compilation

open TauCeti TauCeti.Cocharacter
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

/-- Over an algebraically closed field, a tensor product of two algebras with connected spectra
has connected spectrum, provided one factor is reduced of finite type. -/
theorem connectedSpace_tensorProduct_of_isAlgClosed
    {k A B : Type*} [Field k] [IsAlgClosed k]
    [CommRing A] [Algebra k A] [ConnectedSpace (PrimeSpectrum A)]
    [CommRing B] [Algebra k B] [Algebra.FiniteType k B] [IsReduced B]
    [ConnectedSpace (PrimeSpectrum B)] :
    ConnectedSpace (PrimeSpectrum (B ⊗[k] A)) := by
  have : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  have : Nontrivial B := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  have : Nontrivial (B ⊗[k] A) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left k B A
      (FaithfulSMul.algebraMap_injective k A)
  apply connectedSpace_primeSpectrum_iff_idempotent_eq_zero_or_one.mpr
  intro e he
  obtain ⟨c, hc⟩ := exists_eq_tmul_one_of_isIdempotentElem (k := k) (A := A) (B := B) he
  have hinj : Function.Injective (Algebra.TensorProduct.includeLeft : B →ₐ[k] B ⊗[k] A) :=
    Algebra.TensorProduct.includeLeft_injective (S := k) (FaithfulSMul.algebraMap_injective k A)
  have hcid : IsIdempotentElem c := by
    apply hinj
    simpa only [map_mul, Algebra.TensorProduct.includeLeft_apply, ← hc] using he.eq
  rcases hcid.eq_zero_or_eq_one_of_preconnectedSpace with h | h <;>
    simp [hc, h, Algebra.TensorProduct.one_def]

variable {k : Type u} {H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]

/-- **`P(λ)` is connected when `Z(λ)` is**, for a smooth affine group over an algebraically closed
field: `P(λ) ≅ U(λ) × Z(λ)` as schemes, and `U(λ)` is connected. -/
theorem connectedSpace_parabolic_of_levi [IsAlgClosed k] [Algebra.Smooth k H]
    (l : H →ₐc[k] LaurentPolynomial k)
    (hZ : ConnectedSpace (PrimeSpectrum (H ⧸ (leviDefiningHopfIdeal l).toIdeal))) :
    ConnectedSpace (PrimeSpectrum (H ⧸ (parabolicDefiningHopfIdeal l).toIdeal)) := by
  have : Algebra.FiniteType k H := inferInstance
  let Hc : FiniteTypeCommHopfAlgCat.{u, u} k := FiniteTypeCommHopfAlgCat.of (R := k) H
  have hHc : Algebra.Smooth k Hc := ‹Algebra.Smooth k H›
  have hUs : Algebra.Smooth k (H ⧸ l.unipotentDefiningHopfIdeal.toIdeal) :=
    BialgHom.smoothCommHopfAlgProperty_quotient_unipotentDefiningHopfIdeal (H := Hc) l
  have : IsReduced (H ⧸ l.unipotentDefiningHopfIdeal.toIdeal) :=
    isReduced_of_smooth k _
  have hUc : ConnectedSpace (PrimeSpectrum (H ⧸ l.unipotentDefiningHopfIdeal.toIdeal)) :=
    geometricallyConnectedCommHopfAlgProperty.connectedSpace k _
      (Cocharacter.geometricallyConnectedCommHopfAlgProperty_quotient_unipotentDefiningHopfIdeal l)
  have := connectedSpace_tensorProduct_of_isAlgClosed (k := k)
    (A := H ⧸ (leviDefiningHopfIdeal l).toIdeal) (B := H ⧸ l.unipotentDefiningHopfIdeal.toIdeal)
  exact (PrimeSpectrum.homeomorphOfRingEquiv
    (BialgHom.parabolicCoordinateAlgEquiv l).toRingEquiv).connectedSpace_iff.mpr this

open Magnetism in
/-- **Proposition 16.10 (ii) of Algebraic Magnetism, `k` algebraically closed, from a connected
Levi subgroup.** If `G` is smooth, `N ⊆ f⁻¹(ℕ)` contains the same tangent weights as `f⁻¹(ℕ)`,
and `Z(λ_f)` is connected, then `G^N = P(λ_f)`. -/
theorem magnetIdeal_eq_parabolic_of_connected_levi {X : Type*} [CommGroup X] [DecidableEq X]
    (π : H →ₐc[k] MonoidAlgebra k X) (ψ : X →* Multiplicative ℤ) [IsAlgClosed k]
    [Algebra.Smooth k H] {N : Magnet (Additive X)} (hN : N ≤ natMagnet.comap (pairingHom ψ))
    (hW : ∀ χ ∈ tangentWeights π k, χ ∈ N ↔ 0 ≤ pairingHom ψ χ)
    (hZ : ConnectedSpace
      (PrimeSpectrum (H ⧸ (leviDefiningHopfIdeal (π.cocharacter ψ)).toIdeal))) :
    magnetIdeal (torusGrading π) N =
      (parabolicDefiningHopfIdeal (π.cocharacter ψ)).toIdeal :=
  magnetIdeal_eq_parabolic_of_isAlgClosed π ψ hN hW
    (connectedSpace_parabolic_of_levi (π.cocharacter ψ) hZ)

end AlgMag.Reductive
