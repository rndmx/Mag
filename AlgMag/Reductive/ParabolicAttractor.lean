/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.LieAttractor
import AlgMag.Reductive.AttractorSmooth
import AlgMag.Reductive.Prop1610
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Smooth.LieAlgebra
import TauCeti.Algebra.AlgebraicGroup.Dynamic.Smooth

/-!
# Proposition 16.10 (ii) of Algebraic Magnetism over an algebraically closed field

Let `G = Spec H` be a smooth affine group over an algebraically closed field `k`, with an action
of the split torus `D(X)` given by `π`, and let `f` be the magnet map given by `ψ`. If the magnet
`N ⊆ f⁻¹(ℕ)` contains exactly the tangent weights of `f⁻¹(ℕ)` and `P(λ_f)` is connected, then
`G^N = P(λ_f)`.

The proof is the printed one, without root groups: inside `P = P(λ_f)` the attractor `G^N` is a
closed subgroup (`G^N ⊆ P` since `N ⊆ f⁻¹(ℕ)`), smooth (Corollary 11.10,
`smooth_quotient_magnetHopfIdeal`), with the full Lie algebra
(Proposition 16.4, `lieSubalgebra_magnetHopfIdeal_eq_parabolic`). A smooth closed subgroup of a
smooth connected group with the full Lie algebra is everything
(`TauCeti.HopfIdeal.eq_bot_of_lieSubalgebra_eq_top`).
-/

suppress_compilation

open Magnetism TauCeti TauCeti.Cocharacter

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type*}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X) (ψ : X →* Multiplicative ℤ)

/-- The attractor `G^N` is contained in `P(λ_f)` when `N ⊆ f⁻¹(ℕ)`: as Hopf ideals. -/
lemma parabolic_le_magnetHopfIdeal {N : Magnet (Additive X)}
    (hN : N ≤ natMagnet.comap (pairingHom ψ)) :
    (parabolicDefiningHopfIdeal (π.cocharacter ψ)).toIdeal ≤ (magnetHopfIdeal π N).toIdeal := by
  rw [magnetHopfIdeal_toIdeal, ← magnetIdeal_torusGrading_comap_nat]
  exact magnetIdeal_anti _ hN

/-- **Proposition 16.10 (ii) of Algebraic Magnetism, `k` algebraically closed.** Let `G` be
smooth, `N ⊆ f⁻¹(ℕ)` a magnet containing the same tangent weights as `f⁻¹(ℕ)`, and suppose
`P(λ_f)` connected. Then `G^N = P(λ_f)`. -/
theorem magnetIdeal_eq_parabolic_of_isAlgClosed [IsAlgClosed k] [Algebra.Smooth k H]
    {N : Magnet (Additive X)} (hN : N ≤ natMagnet.comap (pairingHom ψ))
    (hW : ∀ χ ∈ tangentWeights π k, χ ∈ N ↔ 0 ≤ pairingHom ψ χ)
    (hP : ConnectedSpace
      (PrimeSpectrum (H ⧸ (parabolicDefiningHopfIdeal (π.cocharacter ψ)).toIdeal))) :
    magnetIdeal (torusGrading π) N =
      (parabolicDefiningHopfIdeal (π.cocharacter ψ)).toIdeal := by
  set Ip := parabolicDefiningHopfIdeal (π.cocharacter ψ) with hIp
  set J := magnetHopfIdeal π N with hJ
  have hle : Ip.toIdeal ≤ J.toIdeal := parabolic_le_magnetHopfIdeal π ψ hN
  apply le_antisymm _ (by rw [← magnetHopfIdeal_toIdeal]; exact hle)
  let mk := Bialgebra.Quotient.mkBialgHom (R := k) (A := H) Ip.toIdeal
  let J' : HopfIdeal k (H ⧸ Ip.toIdeal) := J.map mk
  have hJ'id : J'.toIdeal = J.toIdeal.map (Ideal.Quotient.mk Ip.toIdeal) := by
    rw [HopfIdeal.map_toIdeal]; rfl
  have : Algebra.FiniteType k H := inferInstance
  let Q : FiniteTypeCommHopfAlgCat.{u, u} k := FiniteTypeCommHopfAlgCat.of (R := k) (H ⧸ Ip.toIdeal)
  have hQs : Algebra.Smooth k (H ⧸ Ip.toIdeal) :=
    ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  have hQs' : Algebra.Smooth k Q := hQs
  have hQc : ConnectedSpace (PrimeSpectrum Q) := hP
  have hJs : Algebra.Smooth k (H ⧸ J.toIdeal) := smooth_quotient_magnetHopfIdeal π N
  have hJ's : Algebra.Smooth k ((H ⧸ Ip.toIdeal) ⧸ J'.toIdeal) := by
    rw [hJ'id]
    exact Algebra.Smooth.of_equiv (DoubleQuot.quotQuotEquivQuotOfLEₐ k hle).symm
  have hlie : J'.lieSubalgebra (B := k) = ⊤ := by
    rw [eq_top_iff]
    intro d _
    change d ∈ (J.map mk).lieSubalgebra (B := k)
    rw [HopfIdeal.lieSubalgebra_map, LieSubalgebra.mem_comap]
    rw [hJ, lieSubalgebra_magnetHopfIdeal_eq_parabolic ψ hW, HopfIdeal.mem_lieSubalgebra_iff]
    intro x hx
    rw [derivationCompLieHom_apply, derivationComp_apply]
    have h0 : Ideal.Quotient.mk Ip.toIdeal x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
    show d (Ideal.Quotient.mk Ip.toIdeal x) = 0
    rw [h0, map_zero]
  have hbot : J' = ⊥ := HopfIdeal.eq_bot_of_lieSubalgebra_eq_top (H := Q) J' hlie
  intro x hx
  rw [← magnetHopfIdeal_toIdeal] at hx
  have hmx : Ideal.Quotient.mk Ip.toIdeal x ∈ J'.toIdeal := by
    rw [hJ'id]; exact Ideal.mem_map_of_mem _ hx
  rw [hbot] at hmx
  exact Ideal.Quotient.eq_zero_iff_mem.mp hmx

end AlgMag.Reductive
