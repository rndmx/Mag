/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.BorBasePair
import AlgMag.Reductive.OpenCellLevi
import AlgMag.Reductive.ParabolicConnected
import AlgMag.Reductive.OpenCell.OpenCellFlatness
import AlgMag.Reductive.OpenCell.IrreducibleOfConnected
import TauCeti.Algebra.AlgebraicGroup.Borel.Existence
import TauCeti.Algebra.AlgebraicGroup.Dynamic.LeviDecomposition.Basic
import TauCeti.Algebra.AlgebraicGroup.Dynamic.Unipotent.Basic
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Solvable
import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic

/-!
# `BaseCore` from the solvability of `C`

Setting: `k = k̄`, `G = Spec H` reductive (Tau Ceti `reductiveCommHopfAlgProperty`), `C` a Hopf
ideal and `ν₀` a regular cocharacter, `Z(ν₀) = C`.

* `isBorelCandidate_parabolic` (proved): for `G` smooth and connected, `P(ν)` is a Borel
  candidate as soon as `Z(ν)` is geometrically solvable.
  - smooth: Tau Ceti `smoothCommHopfAlgProperty_quotient_parabolicDefiningHopfIdeal`;
  - connected: `G` irreducible (`irreducibleSpace_of_connectedSpace`), the open cell is an open
    embedding (`isOpenEmbedding_openCell`), so `Z(ν)` is connected
    (`connectedSpace_levi_of_openCell`) and `P(ν) ≅ U(ν) × Z(ν)` is connected
    (`connectedSpace_parabolic_of_levi`);
  - solvable: on `k̄`-points `P(ν) = U(ν) ⋊ Z(ν)` (Tau Ceti `leviGroupExtension`), `U(ν)` has
    unipotent points (`isUnipotentPoint_quotient_of_le_unipotent`), hence solvable points
    (Kolchin, `geometricallyUnipotentPointsCommHopfAlgProperty.geometricallySolvable`), and
    solvability is closed under extensions.
* `isBorelCandidate_pm` (proved): part (b) of `BaseCore`, from a regular `ν₀` and the single named
  input `CSolvable C`; `Z(−ν₀) = Z(ν₀)`, so `−ν₀` is regular too.
* `baseCore_of_solvable`: `BaseCore C` from (b) and part (a) (a Borel `B ⊆ P(±ν₀)`), the latter
  passed as a hypothesis (not touched here; Tau Ceti has no "dynamic parabolic is parabolic").
* `CSolvable C` (named, NOT proved): `V(C)` has solvable geometric points. For `GL₂` with `T`
  diagonal, `C = T`, a commutative group: the statement holds literally.
-/

open CategoryTheory Magnetism TauCeti TauCeti.Cocharacter

namespace AlgMag.Reductive.BaseCoreB

open AlgMag.Reductive.BorelRoute AlgMag.Reductive.BorBasePair

universe u

variable {k : Type u} {H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]

local notation "Hf" => FiniteTypeCommHopfAlgCat.of k H
local notation "kb" => AlgebraicClosure k

/-! ### Solvability, on `k̄`-points -/

/-- Points of `H ⧸ I` are solvable iff the cut-out subgroup of points of `H` is. -/
theorem isSolvable_quotientPointsSubgroup_iff (I : HopfIdeal k H) :
    Group.IsSolvable (CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) I
      (CommAlgCat.of k kb)) ↔
    Group.IsSolvable (WithConv ((H ⧸ I.toIdeal) →ₐ[k] kb)) := by
  let e := (CommHopfAlgCat.quotientPointsSubgroupIso (_root_.CommHopfAlgCat.of k H) I
    (CommAlgCat.of k kb)).groupIsoToMulEquiv
  constructor
  · intro h
    exact @Group.isSolvable_of_surjective _ _ _ _ e.symm.toMonoidHom e.symm.surjective h
  · intro h
    exact @Group.isSolvable_of_surjective _ _ _ _ e.toMonoidHom e.surjective h

/-- The `k̄`-points of the dynamic unipotent subgroup form a solvable group (Kolchin). -/
theorem isSolvable_unipotent [Algebra.FiniteType k H] (l : H →ₐc[k] LaurentPolynomial k) :
    Group.IsSolvable (unipotent kb l) := by
  have hU : geometricallyUnipotentPointsCommHopfAlgProperty k
      (_root_.CommHopfAlgCat.of k (H ⧸ (U l).toIdeal)) := fun g =>
    isUnipotentPoint_quotient_of_le_unipotent (_root_.CommHopfAlgCat.of k H) (U l) l kb
      (l.quotientPointsSubgroup_unipotentDefiningHopfIdeal).le g
  have hs := geometricallyUnipotentPointsCommHopfAlgProperty.geometricallySolvable hU
  rw [geometricallySolvablePointsCommHopfAlgProperty_iff] at hs
  have h := (isSolvable_quotientPointsSubgroup_iff (U l)).2 hs
  rwa [l.quotientPointsSubgroup_unipotentDefiningHopfIdeal] at h

/-- **`P(λ)` is solvable iff `Z(λ)` is**, on `k̄`-points: `P(λ) = U(λ) ⋊ Z(λ)`. -/
theorem isSolvable_parabolic [Algebra.FiniteType k H] (l : H →ₐc[k] LaurentPolynomial k)
    (hZ : Group.IsSolvable (levi kb l)) : Group.IsSolvable (parabolic kb l) := by
  have := isSolvable_unipotent l
  exact Group.isSolvable_of_ker_le_range (unipotentToParabolic kb l) (limitToLevi kb l)
    (range_unipotentToParabolic_eq_ker_limitToLevi kb l).ge

/-- Geometric solvability of `P(λ)` from that of `Z(λ)`, as Hopf-ideal properties. -/
theorem geometricallySolvable_parabolic [Algebra.FiniteType k H]
    (l : H →ₐc[k] LaurentPolynomial k)
    (hZ : geometricallySolvablePointsCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient Hf (Z l)).obj) :
    geometricallySolvablePointsCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient Hf (P l)).obj := by
  rw [geometricallySolvablePointsCommHopfAlgProperty_iff] at hZ ⊢
  have hZ' := (isSolvable_quotientPointsSubgroup_iff (Z l)).2 hZ
  rw [quotientPointsSubgroup_leviDefiningHopfIdeal] at hZ'
  have hP := isSolvable_parabolic l hZ'
  rw [← quotientPointsSubgroup_parabolicDefiningHopfIdeal] at hP
  exact (isSolvable_quotientPointsSubgroup_iff (P l)).1 hP

/-! ### Smoothness and connectedness -/

/-- For `G` smooth and connected over `k = k̄`, `P(λ)` is geometrically connected. -/
theorem geometricallyConnected_parabolic [IsAlgClosed k] [Algebra.FiniteType k H]
    [Algebra.Smooth k H] [ConnectedSpace (PrimeSpectrum H)]
    (l : H →ₐc[k] LaurentPolynomial k) :
    geometricallyConnectedCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient Hf (P l)).obj := by
  have : IrreducibleSpace (PrimeSpectrum H) :=
    OpenCellNotes.irreducibleSpace_of_connectedSpace k
  have hZ := connectedSpace_levi_of_openCell l (isOpenEmbedding_openCell l)
  have hP := connectedSpace_parabolic_of_levi l hZ
  exact (geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k _).2 hP

/-- **`P(λ)` is a Borel candidate** when `G` is smooth and connected over `k = k̄` and `Z(λ)` is
geometrically solvable. -/
theorem isBorelCandidate_parabolic [IsAlgClosed k] [Algebra.FiniteType k H]
    [Algebra.Smooth k H] [ConnectedSpace (PrimeSpectrum H)]
    (l : H →ₐc[k] LaurentPolynomial k)
    (hZ : geometricallySolvablePointsCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient Hf (Z l)).obj) :
    HopfIdeal.IsBorelCandidate k Hf (P l) := by
  have hHf : Algebra.Smooth k Hf := ‹Algebra.Smooth k H›
  exact HopfIdeal.IsBorelCandidate.mk
    (BialgHom.smoothCommHopfAlgProperty_quotient_parabolicDefiningHopfIdeal (H := Hf) l)
    (geometricallyConnected_parabolic l) (geometricallySolvable_parabolic l hZ)

/-! ### `BaseCore` -/

/-- **The named input**: `V(C)` has solvable geometric points (`hsolv`). True for `GL₂`,
`C = T` diagonal (commutative). -/
def CSolvable (C : HopfIdeal k H) [Algebra.FiniteType k H] : Prop :=
  geometricallySolvablePointsCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient Hf C).obj

/-- **(b) of `BaseCore`**: for `G` reductive over `k = k̄` and `ν₀` regular, `P(ν₀)` and
`P(−ν₀)` are Borel candidates, given `CSolvable C`. -/
theorem isBorelCandidate_pm [IsAlgClosed k] [Algebra.FiniteType k H] {C : HopfIdeal k H}
    (hred : reductiveCommHopfAlgProperty k Hf) {ν : H →ₐc[k] LaurentPolynomial k}
    (hν : IsRegular C ν) (hC : CSolvable C) :
    HopfIdeal.IsBorelCandidate k Hf (P ν) ∧
      HopfIdeal.IsBorelCandidate k Hf (P ν.oppositeCocharacter) := by
  have : Algebra.Smooth k H := hred.smooth
  have : ConnectedSpace (PrimeSpectrum H) :=
    geometricallyConnectedCommHopfAlgProperty.connectedSpace k _ hred.geometricallyConnected
  have hZ : Z ν = C := hν
  have hZ' : Z ν.oppositeCocharacter = C := by
    rw [← hZ]; exact leviDefiningHopfIdeal_oppositeCocharacter ν
  refine ⟨isBorelCandidate_parabolic ν ?_, isBorelCandidate_parabolic _ ?_⟩
  · rw [hZ]; exact hC
  · rw [hZ']; exact hC

/-- **`BaseCore C`** for `G` reductive over `k = k̄`, from a regular `ν₀`, `CSolvable C` (part (b))
and part (a) of `BaseCore` (a Borel inside `P(±ν₀)`; ideal order `P ν ≤ B` is `V(B) ⊆ V(P ν)`),
kept as an explicit hypothesis. -/
theorem baseCore_of_solvable [IsAlgClosed k] [Algebra.FiniteType k H] {C : HopfIdeal k H}
    (hred : reductiveCommHopfAlgProperty k Hf) {ν : H →ₐc[k] LaurentPolynomial k}
    (hν : IsRegular C ν) (hC : CSolvable C)
    (ha : ∃ B, HopfIdeal.IsBorelOverAlgClosed k Hf B ∧ P ν ≤ B)
    (ha' : ∃ B', HopfIdeal.IsBorelOverAlgClosed k Hf B' ∧ P ν.oppositeCocharacter ≤ B') :
    BaseCore C :=
  ⟨ν, hν, ha, ha', isBorelCandidate_pm hred hν hC⟩

/-- **(Base±)** for `G` reductive over `k = k̄`, from the same inputs. -/
theorem basePair_of_solvable [IsAlgClosed k] [Algebra.FiniteType k H] {C : HopfIdeal k H}
    (hred : reductiveCommHopfAlgProperty k Hf) {ν : H →ₐc[k] LaurentPolynomial k}
    (hν : IsRegular C ν) (hC : CSolvable C)
    (ha : ∃ B, HopfIdeal.IsBorelOverAlgClosed k Hf B ∧ P ν ≤ B)
    (ha' : ∃ B', HopfIdeal.IsBorelOverAlgClosed k Hf B' ∧ P ν.oppositeCocharacter ≤ B') :
    BasePair C :=
  basePair_of_core (baseCore_of_solvable hred hν hC ha ha')

end AlgMag.Reductive.BaseCoreB
