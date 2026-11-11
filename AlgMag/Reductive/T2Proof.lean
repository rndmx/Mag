/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.BorSideFinal
import TauCeti.Algebra.AlgebraicGroup.Borel.Existence
import TauCeti.Algebra.AlgebraicGroup.Solvable.Derived.Series
import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Characteristic

/-!
# T2 from `BorelZMax`: the rank-one Levi `Z = G^{ℤδ}` has non-solvable points

`BorelZMax π δ ψ` (BorSideFinal) says that `P_Z(λ_ψ)` and `P_Z(λ_ψ⁻¹)` are minimal among the
Borel-candidate Hopf ideals of `Z = G^{ℤδ}`. This file proves the implication
`BorelZMax ⇒ T2` (lean-fable.md §1, finish-plan.md §2), where

* **T2**: `Z(k)` is not solvable as soon as `ℤδ` carries a tangent weight `α` with
  `⟨ψ, α⟩ ≠ 0` (for `G` smooth connected, `δ` a line generator).

Proof: if `Z(k)` were solvable, the Hopf ideal `⊥` of `k[Z]` (the subgroup `Z` itself) would be a
Borel candidate of `Z` (`Z` is smooth, connected by `connectedSpace_lineAttractor`, and has
solvable points): Tau Ceti `isSolvableRadicalCandidate_bot_iff` + `.isBorelCandidate`. Since
`⊥ ≤ P_Z(λ^{±1})`, minimality gives `P_Z(λ) = ⊥ = P_Z(λ⁻¹)`, contradicting `parZ_ne_of_root`.

Non-circular: nothing about `Z_G(T)`, `C`, or condition (i). True for `SL₃`: `Z = GL₂`-type Levi,
`Z(k)` is not solvable. The converse (`T2 + T-transitivity ⇒ BorelZMax`) is the remaining content
of `BorelZMax`; see lean-fableT2.md.
-/

suppress_compilation

open Magnetism TauCeti TauCeti.Cocharacter AlgMag.Weyl
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)

open R1Build R1Dis

local instance zDecT2 (α : Additive X) : DecidableEq (ZAlg π α) := Classical.decEq _
local instance zSmoothT2 [Algebra.FiniteType k H] [Algebra.Smooth k H] (α : Additive X) :
    Algebra.Smooth k (ZAlg π α) := smooth_quotient_magnetHopfIdeal π _

/-- **`⊥` is a Borel candidate of `Z = G^{ℤδ}` when `Z(k)` is solvable** (`G` smooth connected,
`δ` a line generator). -/
theorem isBorelCandidate_bot_ZAlg_of_isSolvable [Algebra.FiniteType k H] [Algebra.Smooth k H]
    [ConnectedSpace (PrimeSpectrum H)] [Module.Free ℤ (Additive X)]
    (δ : Additive X) (hδ0 : δ ≠ 0)
    (hRay : ∀ β ∈ roots π, (∃ m n : ℤ, n ≠ 0 ∧ n • β = m • δ) → β ∈ lineMagnet δ)
    (hsolv : Group.IsSolvable (WithConv (ZAlg π δ →ₐ[k] k))) :
    HopfIdeal.IsBorelCandidate k (FiniteTypeCommHopfAlgCat.of k (ZAlg π δ)) ⊥ := by
  have hconn : ConnectedSpace (PrimeSpectrum (ZAlg π δ)) :=
    connectedSpace_lineAttractor π hδ0 hRay
  have hred : IsReduced (ZAlg π δ) := isReduced_of_smooth k (ZAlg π δ)
  have hgc : geometricallyConnectedCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.of k (ZAlg π δ)).obj :=
    (geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k _).2 hconn
  have hgeo : geometricallySolvablePointsCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.of k (ZAlg π δ)).obj :=
    (geometricallySolvablePointsCommHopfAlgProperty.iff_exists_derivedSeriesDefiningIdeal_eq_augmentation
      (FiniteTypeCommHopfAlgCat.of k (ZAlg π δ)).obj).mpr
      ((FiniteTypeCommHopfAlgCat.of k (ZAlg π δ)).obj.isSolvable_points_iff_exists_derivedSeriesDefiningIdeal_eq_augmentation.mp
        hsolv)
  exact ((HopfIdeal.isSolvableRadicalCandidate_bot_iff
      (FiniteTypeCommHopfAlgCat.of k (ZAlg π δ))).mpr
    ⟨hgc, inferInstance, hgeo⟩).isBorelCandidate

/-- **T2 from `BorelZMax`.** If `P_Z(λ_ψ^{±1})` are minimal Borel candidates of `Z = G^{ℤδ}` and
`ℤδ` carries a tangent weight `α` with `⟨ψ, α⟩ ≠ 0`, then `Z(k)` is not solvable. -/
theorem not_isSolvable_points_of_borelZMax [Algebra.FiniteType k H] [Algebra.Smooth k H]
    [ConnectedSpace (PrimeSpectrum H)] [Module.Free ℤ (Additive X)]
    (δ : Additive X) (hδ0 : δ ≠ 0)
    (hRay : ∀ β ∈ roots π, (∃ m n : ℤ, n ≠ 0 ∧ n • β = m • δ) → β ∈ lineMagnet δ)
    (ψ : X →* Multiplicative ℤ) {α : Additive X} (hα : α ∈ tangentWeights π k)
    (hαδ : α ∈ lineMagnet δ) (hψα : pairingHom ψ α ≠ 0)
    (hmax : BorelZMax π δ ψ) :
    ¬ Group.IsSolvable (WithConv (ZAlg π δ →ₐ[k] k)) := by
  intro hsolv
  have hbot := isBorelCandidate_bot_ZAlg_of_isSolvable π δ hδ0 hRay hsolv
  have h1 := hmax.1 ⊥ hbot bot_le
  have h2 := hmax.2 ⊥ hbot bot_le
  exact parZ_ne_of_root π δ ψ hα hαδ hψα ((le_bot_iff.1 h2).trans (le_bot_iff.1 h1).symm)

/-- The same with a root `α ∈ ℤδ` and `⟨ψ, δ⟩ ≠ 0` (the form of the final assembly). -/
theorem not_isSolvable_points_of_borelZMax_root [Algebra.FiniteType k H] [Algebra.Smooth k H]
    [ConnectedSpace (PrimeSpectrum H)] [Module.Free ℤ (Additive X)]
    (δ : Additive X) (hδ0 : δ ≠ 0)
    (hRay : ∀ β ∈ roots π, (∃ m n : ℤ, n ≠ 0 ∧ n • β = m • δ) → β ∈ lineMagnet δ)
    (ψ : X →* Multiplicative ℤ) (hψδ : pairingHom ψ δ ≠ 0)
    {α : Additive X} (hα : α ∈ roots π) (hαδ : α ∈ lineMagnet δ)
    (hmax : BorelZMax π δ ψ) :
    ¬ Group.IsSolvable (WithConv (ZAlg π δ →ₐ[k] k)) := by
  have hα0 : α ≠ 0 := ne_zero_of_mem_roots hα
  exact not_isSolvable_points_of_borelZMax π δ hδ0 hRay ψ
    ((mem_tangentWeights_iff_mem_roots hα0).2 hα) hαδ
    (pairingHom_ne_zero_of_mem_lineMagnet ψ hα0 hαδ hψδ) hmax

end AlgMag.Reductive

#print axioms AlgMag.Reductive.not_isSolvable_points_of_borelZMax
#print axioms AlgMag.Reductive.not_isSolvable_points_of_borelZMax_root
