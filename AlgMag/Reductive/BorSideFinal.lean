/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.BorWallStep
import AlgMag.Reductive.BaseCoreB
import AlgMag.Reductive.LeviMagnet

/-!
# The Borel side without `hT2` and `hBorStab`

`condI_condII_condIII_of_reductive_final` consumes its Borel-side input `hBorSide` only through
`hR1at`: for every line generator `δ ≠ 0` (roots on `ℚδ` lie in `ℤδ`), a point
`n ∈ G^{ℤδ}(k)` normalising `T` with `σ ≠ 1`. There it is produced by `r1Geom_of_opposite''`
(projective orbit, second fixed point), which needs `hT2` (`Z(k)` not solvable) and `hBorStab`.

This file supplies the same `hR1at` from the shorter W2–W3 route of Bor-plan §2, already in Lean
as `r1Geom_of_borelZ` (Borel conjugacy in `Z = G^{ℤδ}`, `exists_SQ`, `parZ_eq_of_conjugate_eq`):

* `parZ_ne_of_root` (proved): `P_Z(λ⁻¹) ≠ P_Z(λ)` at a line generator `δ` carrying a root
  `α ∈ ℤδ` (the generator need not be a root: `δ = ϖ` in `SL₂ × 𝔾_m`), by the Lie-algebra
  argument of `parZ_ne` with the adjoint weight vector of weight `α`.
* `BorelZSide π δ ψ` (named): `P_Z(λ_ψ)` and `P_Z(λ_ψ⁻¹)` are Borel subgroups of `Z`.
* `r1Geom_of_borelZSide`, `r1_of_borelZSide` (proved): `R1Geom`, then the Weyl element in the
  exact form of `hR1at`. Neither `hT2` nor `hBorStab` is used.
* `BorelZMax π δ ψ` (named, the only genuinely new input): `P_Z(λ^{±1})` are *minimal* Borel
  candidates of `Z` (no smooth connected solvable closed subgroup of `Z` strictly contains them).
  `borelZSide_of_max` (proved): `BorelZSide` from `BorelZMax` and solvability of `Z_Z(λ)`
  (`ZZSolvable`, which is `hsolvC` once `Z_Z(λ) = Z_G(T)` is identified), via
  `isBorelCandidate_parabolic` on `Z` (connected by `connectedSpace_lineAttractor`).

Non-circularity: no statement mentions `Z_G(T)`, `C`, or condition (i). For `SL₃` and a root `α`,
`Z = G^{ℤα}` is the `GL₂`-type Levi and `P_Z(±λ) = T·U_{±α}` are its Borels, so `BorelZSide` and
`BorelZMax` hold.
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

local instance zDecS (α : Additive X) : DecidableEq (ZAlg π α) := Classical.decEq _
local instance zSmoothS [Algebra.FiniteType k H] [Algebra.Smooth k H] (α : Additive X) :
    Algebra.Smooth k (ZAlg π α) := smooth_quotient_magnetHopfIdeal π _

omit [IsAlgClosed k] [DecidableEq X] in
/-- `⟨ψ, α⟩ ≠ 0` for `0 ≠ α ∈ ℤδ` when `⟨ψ, δ⟩ ≠ 0`. -/
theorem pairingHom_ne_zero_of_mem_lineMagnet (ψ : X →* Multiplicative ℤ) {δ α : Additive X}
    (hα0 : α ≠ 0) (hαδ : α ∈ lineMagnet δ) (hψδ : pairingHom ψ δ ≠ 0) :
    pairingHom ψ α ≠ 0 := by
  obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 (mem_lineMagnet.1 hαδ)
  rw [map_zsmul, smul_eq_mul]
  have hm : m ≠ 0 := by rintro rfl; simp at hα0
  exact mul_ne_zero hm hψδ

/-- **(b) at a line generator.** `P_Z(λ⁻¹) ≠ P_Z(λ)` for `Z = G^{ℤδ}` as soon as `ℤδ` contains a
tangent weight `α` with `⟨ψ, α⟩ ≠ 0`: both are attractors `G^{N±}`, `N± = ψ^{±1}⁻¹(ℕ) ∩ ℤδ`,
which differ on `α` (`magnetIdeal_ne_of_tangentWeight`). -/
theorem parZ_ne_of_root [Algebra.FiniteType k H] [Algebra.Smooth k H] (δ : Additive X)
    (ψ : X →* Multiplicative ℤ) {α : Additive X} (hα : α ∈ tangentWeights π k)
    (hαδ : α ∈ lineMagnet δ) (hψα : pairingHom ψ α ≠ 0) :
    parabolicDefiningHopfIdeal (zCochar π δ ψ).oppositeCocharacter ≠
      parabolicDefiningHopfIdeal (zCochar π δ ψ) := by
  intro heq
  have hs := R1Build.zMk_surjective π δ
  have e1 := parabolic_toIdeal_eq_map (zMk π δ) hs _ (zCochar π δ ψ) (R1Dis.zCochar_comp π δ ψ)
  have hop : (zCochar π δ ψ).oppositeCocharacter = zCochar π δ ψ⁻¹ := by
    unfold zCochar; rw [cocharacter_inv]
  have e2 := parabolic_toIdeal_eq_map (zMk π δ) hs _ (zCochar π δ ψ⁻¹)
    (R1Dis.zCochar_comp π δ ψ⁻¹)
  rw [← hop] at e2
  have h3 := congrArg (Ideal.comap (zMk π δ : H →ₐ[k] ZAlg π δ))
    (e2.symm.trans ((congrArg HopfIdeal.toIdeal heq).trans e1))
  have hK : Ideal.comap (zMk π δ : H →ₐ[k] ZAlg π δ) ⊥ =
      magnetIdeal (torusGrading π) (lineMagnet δ) := by
    ext x
    rw [Ideal.mem_comap, Ideal.mem_bot, ← magnetHopfIdeal_toIdeal]
    exact Ideal.Quotient.eq_zero_iff_mem
  rw [Ideal.comap_map_of_surjective (zMk π δ : H →ₐ[k] ZAlg π δ) hs,
    Ideal.comap_map_of_surjective (zMk π δ : H →ₐ[k] ZAlg π δ) hs, hK,
    ← magnetIdeal_torusGrading_comap_nat, ← magnetIdeal_torusGrading_comap_nat,
    ← magnetIdeal_inf, ← magnetIdeal_inf] at h3
  rcases lt_or_gt_of_ne hψα with hneg | hpos
  · refine magnetIdeal_ne_of_tangentWeight π hα (N := natMagnet.comap (pairingHom ψ⁻¹) ⊓
      lineMagnet δ) (N' := natMagnet.comap (pairingHom ψ) ⊓ lineMagnet δ) ⟨?_, hαδ⟩ ?_ h3
    · change pairingHom ψ⁻¹ α ∈ natMagnet
      rw [mem_natMagnet, borPairingHom_inv]; omega
    · rintro ⟨h, -⟩
      change pairingHom ψ α ∈ natMagnet at h
      rw [mem_natMagnet] at h; omega
  · refine magnetIdeal_ne_of_tangentWeight π hα (N := natMagnet.comap (pairingHom ψ) ⊓
      lineMagnet δ) (N' := natMagnet.comap (pairingHom ψ⁻¹) ⊓ lineMagnet δ) ⟨?_, hαδ⟩ ?_ h3.symm
    · change pairingHom ψ α ∈ natMagnet
      rw [mem_natMagnet]; omega
    · rintro ⟨h, -⟩
      change pairingHom ψ⁻¹ α ∈ natMagnet at h
      rw [mem_natMagnet, borPairingHom_inv] at h; omega

/-- **Borel side at `(δ, ψ)` (named).** `P_Z(λ_ψ)` and `P_Z(λ_ψ⁻¹)` are Borel subgroups of
`Z = G^{ℤδ}`. Replaces `hT2 ∧ hBorStab` (`BorelSide`) in the final assembly. -/
def BorelZSide [Algebra.FiniteType k H] [Algebra.Smooth k H] (δ : Additive X)
    (ψ : X →* Multiplicative ℤ) : Prop :=
  HopfIdeal.IsBorelOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k (ZAlg π δ))
      (parabolicDefiningHopfIdeal (zCochar π δ ψ)) ∧
    HopfIdeal.IsBorelOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k (ZAlg π δ))
      (parabolicDefiningHopfIdeal (zCochar π δ ψ).oppositeCocharacter)

/-- **`R1Geom` from `BorelZSide`** at a line generator `δ` carrying a root `α ∈ ℤδ`. -/
theorem r1Geom_of_borelZSide [Algebra.FiniteType k H] [Algebra.Smooth k H]
    (hπ : Function.Surjective π)
    (hT : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H)
      (HopfIdeal.kerOfSurjective π hπ))
    (δ : Additive X) (ψ : X →* Multiplicative ℤ) (hψδ : pairingHom ψ δ ≠ 0)
    {α : Additive X} (hα : α ∈ roots π) (hαδ : α ∈ lineMagnet δ)
    (hB : BorelZSide π δ ψ) : Nonempty (R1Geom π δ ψ hπ) := by
  have hα0 : α ≠ 0 := ne_zero_of_mem_roots hα
  have hΦ : α ∈ tangentWeights π k := (mem_tangentWeights_iff_mem_roots hα0).2 hα
  exact r1Geom_of_borelZ π δ ψ hπ hT hB.1 hB.2
    (parZ_ne_of_root π δ ψ hΦ hαδ (pairingHom_ne_zero_of_mem_lineMagnet ψ hα0 hαδ hψδ))

/-- **The Weyl element from `BorelZSide`**, in the form `hR1at` of
`condI_condII_condIII_of_reductive_final`: no `hT2`, no `hBorStab`. -/
theorem r1_of_borelZSide [Algebra.FiniteType k H] [Algebra.Smooth k H]
    (hπ : Function.Surjective π)
    (hT : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H)
      (HopfIdeal.kerOfSurjective π hπ))
    (δ : Additive X) (ψ : X →* Multiplicative ℤ) (hψδ : pairingHom ψ δ ≠ 0)
    {α : Additive X} (hα : α ∈ roots π) (hαδ : α ∈ lineMagnet δ)
    (hB : BorelZSide π δ ψ) :
    ∃ (n : WithConv (H →ₐ[k] k)) (σ : X ≃* X), IsNormalizingWith π k n σ ∧
      n ∈ attractorSubgroup π (lineMagnet δ) k ∧ σ ≠ 1 :=
  r1_of_r1Datum π hπ
    ((r1Geom_of_borelZSide π hπ hT δ ψ hψδ hα hαδ hB).some.toR1Datum π δ ψ hT hψδ)

/-! ### Splitting `BorelZSide`: candidate + maximality -/

/-- **Maximality (named, the only new input).** `P_Z(λ_ψ)` and `P_Z(λ_ψ⁻¹)` are minimal among
the Borel-candidate Hopf ideals of `Z = G^{ℤδ}`: no smooth, geometrically connected, geometrically
solvable closed subgroup of `Z` strictly contains them. -/
def BorelZMax [Algebra.FiniteType k H] [Algebra.Smooth k H] (δ : Additive X)
    (ψ : X →* Multiplicative ℤ) : Prop :=
  (∀ J, HopfIdeal.IsBorelCandidate k (FiniteTypeCommHopfAlgCat.of k (ZAlg π δ)) J →
      J ≤ parabolicDefiningHopfIdeal (zCochar π δ ψ) →
      parabolicDefiningHopfIdeal (zCochar π δ ψ) ≤ J) ∧
    (∀ J, HopfIdeal.IsBorelCandidate k (FiniteTypeCommHopfAlgCat.of k (ZAlg π δ)) J →
      J ≤ parabolicDefiningHopfIdeal (zCochar π δ ψ).oppositeCocharacter →
      parabolicDefiningHopfIdeal (zCochar π δ ψ).oppositeCocharacter ≤ J)

/-- **Solvability of `Z_Z(λ)` (named).** Its points over `k̄` are solvable. Since the magnet of
`Z_Z(λ_ψ)` in `Z = G^{ℤδ}` is `ker ψ ∩ ℤδ = 0` when `⟨ψ, δ⟩ ≠ 0`, this is `Z_G(T)` and the
statement is `hsolvC`. -/
def ZZSolvable [Algebra.FiniteType k H] [Algebra.Smooth k H] (δ : Additive X)
    (ψ : X →* Multiplicative ℤ) : Prop :=
  geometricallySolvablePointsCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient
    (FiniteTypeCommHopfAlgCat.of k (ZAlg π δ)) (leviDefiningHopfIdeal (zCochar π δ ψ))).obj

/-- `Z_Z(λ⁻¹) = Z_Z(λ)`, so `ZZSolvable` is symmetric. -/
theorem zzSolvable_opp [Algebra.FiniteType k H] [Algebra.Smooth k H] (δ : Additive X)
    (ψ : X →* Multiplicative ℤ) (h : ZZSolvable π δ ψ) :
    geometricallySolvablePointsCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient
      (FiniteTypeCommHopfAlgCat.of k (ZAlg π δ))
      (leviDefiningHopfIdeal (zCochar π δ ψ).oppositeCocharacter)).obj := by
  unfold ZZSolvable at h
  rwa [leviDefiningHopfIdeal_oppositeCocharacter]

/-- **`BorelZSide` from `BorelZMax` and `ZZSolvable`**, for `G` smooth and connected and `δ` a line
generator (`Z` connected by `connectedSpace_lineAttractor`); the candidate part is
`isBorelCandidate_parabolic` on `Z`. -/
theorem borelZSide_of_max [Algebra.FiniteType k H] [Algebra.Smooth k H]
    [ConnectedSpace (PrimeSpectrum H)] [Module.Free ℤ (Additive X)]
    (δ : Additive X) (hδ0 : δ ≠ 0)
    (hRay : ∀ β ∈ roots π, (∃ m n : ℤ, n ≠ 0 ∧ n • β = m • δ) → β ∈ lineMagnet δ)
    (ψ : X →* Multiplicative ℤ) (hZ : ZZSolvable π δ ψ) (hmax : BorelZMax π δ ψ) :
    BorelZSide π δ ψ := by
  have : ConnectedSpace (PrimeSpectrum (ZAlg π δ)) := connectedSpace_lineAttractor π hδ0 hRay
  have hc1 := BaseCoreB.isBorelCandidate_parabolic (H := ZAlg π δ) (zCochar π δ ψ) hZ
  have hc2 := BaseCoreB.isBorelCandidate_parabolic (H := ZAlg π δ)
    (zCochar π δ ψ).oppositeCocharacter (zzSolvable_opp π δ ψ hZ)
  exact ⟨⟨inferInstance, hc1, fun J hJ hle => hmax.1 J hJ hle⟩,
    ⟨inferInstance, hc2, fun J hJ hle => hmax.2 J hJ hle⟩⟩

/-- **The Weyl element from `BorelZMax` + `ZZSolvable`** (the `hR1at` form). -/
theorem r1_of_borelZMax [Algebra.FiniteType k H] [Algebra.Smooth k H]
    [ConnectedSpace (PrimeSpectrum H)] [Module.Free ℤ (Additive X)]
    (hπ : Function.Surjective π)
    (hT : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H)
      (HopfIdeal.kerOfSurjective π hπ))
    (δ : Additive X) (hδ0 : δ ≠ 0)
    (hRay : ∀ β ∈ roots π, (∃ m n : ℤ, n ≠ 0 ∧ n • β = m • δ) → β ∈ lineMagnet δ)
    (ψ : X →* Multiplicative ℤ) (hψδ : pairingHom ψ δ ≠ 0)
    {α : Additive X} (hα : α ∈ roots π) (hαδ : α ∈ lineMagnet δ)
    (hZ : ZZSolvable π δ ψ) (hmax : BorelZMax π δ ψ) :
    ∃ (n : WithConv (H →ₐ[k] k)) (σ : X ≃* X), IsNormalizingWith π k n σ ∧
      n ∈ attractorSubgroup π (lineMagnet δ) k ∧ σ ≠ 1 :=
  r1_of_borelZSide π hπ hT δ ψ hψδ hα hαδ (borelZSide_of_max π δ hδ0 hRay ψ hZ hmax)

end AlgMag.Reductive

#print axioms AlgMag.Reductive.r1_of_borelZSide
#print axioms AlgMag.Reductive.r1_of_borelZMax
