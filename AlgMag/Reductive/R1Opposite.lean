/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.R1GeomBuild
import AlgMag.Reductive.OpenCellGen

/-!
# `R1Geom` via the opposite Borel (no Białynicki-Birula)

Instantiates `R1Geometry.orbitInput_of_opposite` at `Z = G^{ℤα}`:
* `BmAlg = k[B⁻]`, `B⁻ = P_Z(λ⁻¹)`, with `fBm : k[Z] ↠ k[B⁻]`;
* `hTB_opp`: `T(k) ⊆ B⁻(k)` (`T ⊆ P(λ⁻¹)`, `parabolic_le_ker_torus'` with `cocharacter_inv`);
* `hgen_opp`: `B⁺(k) ∪ B⁻(k)` generates `Z(k)`, from `closure_openCell_eq_top` (OpenCellGen)
  applied to `Z` with the rank-one torus `λ : 𝔾_m → Z` itself (for which `C = Z(λ)`);
* `r1Geom_of_opposite`: `R1Geom` from `hT`, `hLevi`, `hZconn`, (Bor±), `hCB`, `hT2`, `hBorStab`.
-/

set_option linter.style.haveILetI false

open Magnetism TauCeti TauCeti.HopfIdeal TauCeti.Cocharacter TauCeti.Comodule WithConv

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable [IsAlgClosed k]
variable (π : H →ₐc[k] MonoidAlgebra k X) (α : Additive X) (ψ : X →* Multiplicative ℤ)
variable [Algebra.FiniteType k H] [Algebra.Smooth k H]

namespace R1Opp

noncomputable local instance zDecO : DecidableEq (ZAlg π α) := Classical.decEq _
local instance zSmoothO : Algebra.Smooth k (ZAlg π α) := smooth_quotient_magnetHopfIdeal π _

omit [IsAlgClosed k] in
/-- A point of `P(l)` comes from `k[P(l)]`. -/
lemma mem_range_of_mem_parabolic {Q : Type u} [CommRing Q] [HopfAlgebra k Q]
    (l : Q →ₐc[k] LaurentPolynomial k) {x : WithConv (Q →ₐ[k] k)} (hx : x ∈ parabolic k l) :
    x ∈ Set.range (BialgHom.mapDomain (A := k)
      (Bialgebra.Quotient.mkBialgHom (parabolicDefiningHopfIdeal l).toIdeal)) := by
  have hle : (parabolicDefiningHopfIdeal l).toIdeal ≤ RingHom.ker x.ofConv := by
    rw [parabolicDefiningHopfIdeal, HopfIdeal.ofIdealOfPointsSubgroup_toIdeal]
    exact (negativeCoefficientIdeal_le_ker_iff l x).2 hx
  refine ⟨toConv (Ideal.Quotient.liftₐ _ x.ofConv fun a ha => hle ha), ?_⟩
  apply WithConv.ofConv_injective
  ext a
  rw [BialgHom.mapDomain_apply, ofConv_toConv]
  rfl

/-- `k[B⁻]`, `B⁻ = P_Z(λ⁻¹)`. -/
abbrev BmAlg : Type u :=
  ZAlg π α ⧸ (parabolicDefiningHopfIdeal (zCochar π α ψ).oppositeCocharacter).toIdeal

/-- `k[Z] ↠ k[B⁻]`. -/
noncomputable abbrev fBm : ZAlg π α →ₐc[k] BmAlg π α ψ :=
  Bialgebra.Quotient.mkBialgHom
    (parabolicDefiningHopfIdeal (zCochar π α ψ).oppositeCocharacter).toIdeal

lemma piQ_fB (z : ZAlg π α) : piQ π α ψ (R1Build.fB π α ψ z) = piZ π α z := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact (piQ_apply π α ψ y).trans (piZ_apply π α y).symm

/-- **`T(k) ⊆ B⁻(k)`.** -/
lemma hTB_opp (hπ : Function.Surjective π) :
    ∀ t ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k (ZAlg π α))
      (R1Build.TZ π α ψ hπ) (CommAlgCat.of k k),
      t ∈ Set.range (BialgHom.mapDomain (A := k) (fBm π α ψ)) := by
  intro t ht
  apply mem_range_of_mem_parabolic
  have e : (parabolicDefiningHopfIdeal (zCochar π α ψ).oppositeCocharacter).toIdeal =
      negativeCoefficientIdeal (zCochar π α ψ).oppositeCocharacter := by
    rw [parabolicDefiningHopfIdeal, HopfIdeal.ofIdealOfPointsSubgroup_toIdeal]
  refine (negativeCoefficientIdeal_le_ker_iff _ t).1 ?_
  rw [← e]
  intro x hx
  have h1 : x ∈ (parabolicDefiningHopfIdeal ((piZ π α).cocharacter ψ⁻¹)).toIdeal := by
    rw [cocharacter_inv]; exact hx
  have h2 := parabolic_le_ker_torus' (piZ π α) ψ⁻¹ h1
  have hxT : x ∈ R1Build.TZ π α ψ hπ := by
    rw [R1Build.TZ, HopfIdeal.mem_comapOfSurjective, TQ, HopfIdeal.mem_kerOfSurjective, piQ_fB]
    simpa [RingHom.mem_ker] using h2
  exact (TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).1 ht x hxT

/-- The rank-one torus `λ : 𝔾_m → Z` as a diagonalizable-group map, with character group
`ULift ℤ` (to stay in universe `u`). -/
noncomputable abbrev piL : ZAlg π α →ₐc[k] MonoidAlgebra k (ULift.{u} (Multiplicative ℤ)) :=
  (MonoidAlgebra.mapDomainBialgHom k (MulEquiv.ulift.symm.toMonoidHom :
      Multiplicative ℤ →* ULift.{u} (Multiplicative ℤ))).comp
    ((AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp (zCochar π α ψ))

/-- The identity cocharacter of `ULift ℤ`. -/
abbrev psiL : ULift.{u} (Multiplicative ℤ) →* Multiplicative ℤ := MulEquiv.ulift.toMonoidHom

lemma mapDomain_ulift_roundtrip (c : MonoidAlgebra k (Multiplicative ℤ)) :
    MonoidAlgebra.mapDomainBialgHom k
        (MulEquiv.ulift.toMonoidHom : ULift.{u} (Multiplicative ℤ) →* Multiplicative ℤ)
      (MonoidAlgebra.mapDomainBialgHom k
        (MulEquiv.ulift.symm.toMonoidHom : Multiplicative ℤ →* ULift.{u} (Multiplicative ℤ)) c) =
      c := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | single χ r => simp [MonoidAlgebra.mapDomainBialgHom]

lemma piL_cocharacter : (piL π α ψ).cocharacter psiL = zCochar π α ψ := by
  ext x
  simp only [BialgHom.cocharacter, piL, psiL, BialgHom.comp_apply, mapDomain_ulift_roundtrip]
  simp

/-- **`B⁺(k) ∪ B⁻(k)` generates `Z(k)`** (`Z` connected). -/
lemma hgen_opp (hZconn : ConnectedSpace (PrimeSpectrum (ZAlg π α))) :
    Subgroup.closure (Set.range (BialgHom.mapDomain (A := CommAlgCat.of k k) (R1Build.fB π α ψ)) ∪
      Set.range (BialgHom.mapDomain (A := CommAlgCat.of k k) (fBm π α ψ))) = ⊤ := by
  have hbot : (⊥ : Magnet ℤ).comap (pairingHom psiL) = ⊥ := by
    ext χ
    simp [AddSubmonoid.mem_bot, pairingHom, psiL]
  have hreg : ∀ z ∈ levi k ((piL π α ψ).cocharacter psiL),
      z ∈ attractorSubgroup (piL π α ψ) ⊥ k := by
    intro z hz
    rw [mem_attractorSubgroup, ← hbot]
    exact (magnetIdeal_torusGrading_comap_bot_le_ker_iff (π := piL π α ψ) (ψ := psiL) z).2 hz
  have htop := closure_openCell_eq_top (piL π α ψ) psiL hreg
  rw [eq_top_iff, ← htop, Subgroup.closure_le]
  rintro x ((hx | hx) | hx)
  · apply Subgroup.subset_closure
    right
    have hx' : x ∈ unipotent k (zCochar π α ψ).oppositeCocharacter := by
      have := hx
      rwa [SetLike.mem_coe, cocharacter_inv, piL_cocharacter] at this
    exact mem_range_of_mem_parabolic _ (unipotent_le_parabolic hx')
  · apply Subgroup.subset_closure
    left
    have hx' : x ∈ parabolic k (zCochar π α ψ) := by
      rw [← piL_cocharacter, ← magnetIdeal_torusGrading_comap_nat_le_ker_iff]
      refine le_trans (magnetIdeal_anti_pure _ bot_le) ?_
      exact (mem_attractorSubgroup _).1 hx
    exact mem_range_of_mem_parabolic _ hx'
  · apply Subgroup.subset_closure
    left
    have hx' : x ∈ unipotent k (zCochar π α ψ) := by
      have := hx; rwa [SetLike.mem_coe, piL_cocharacter] at this
    exact mem_range_of_mem_parabolic _ (unipotent_le_parabolic hx')

end R1Opp

open R1Opp R1Build in
/-- **`R1Geom` without Białynicki-Birula.** Named inputs: `hLevi` (`Z_Z(λ)` connected),
`hZconn` (`Z` connected), (Bor⁺) and (Bor⁻) (instances: `B^±(k)` solvable), `hCB`
(`C(k) ⊆ B⁺(k)`), `hT2` (`Z(k)` not solvable) and `hBorStab` (`Stab(x₀)(k) ⊆ B⁺(k)` on the closed
orbit, for solvable stabilisers `S(k)`). -/
theorem r1Geom_of_opposite (hπ : Function.Surjective π)
    (hT : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H)
      (HopfIdeal.kerOfSurjective π hπ))
    (hLevi : ConnectedSpace (PrimeSpectrum
      (ZAlg π α ⧸ (leviDefiningHopfIdeal (zCochar π α ψ)).toIdeal)))
    (hZconn : ConnectedSpace (PrimeSpectrum (ZAlg π α)))
    [Group.IsSolvable (WithConv (BAlg π α ψ →ₐ[k] k))]
    [Group.IsSolvable (WithConv (BmAlg π α ψ →ₐ[k] k))]
    (hCB : ∀ a : WithConv (ZAlg π α →ₐ[k] k),
      BialgHom.mapDomain (zMk π α) a ∈ attractorSubgroup π ⊥ k →
        a ∈ Set.range (BialgHom.mapDomain (fB π α ψ)))
    (hT2 : ¬ Group.IsSolvable (WithConv (ZAlg π α →ₐ[k] k)))
    (hBorStab : ∀ (M : Type u) [AddCommGroup M] [Module k M] [Comodule k (ZAlg π α) M]
      [Module.Finite k M] (m : M) (hm : Module.IsUnimodular k m) (S : HopfIdeal k (ZAlg π α)),
      IsClosed (Set.range (projectiveOrbitMap (H := ZAlg π α) m hm)) →
      (∀ a : WithConv (ZAlg π α →ₐ[k] k),
        a ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k (ZAlg π α)) S
            (CommAlgCat.of k k) ↔
          projectiveOrbitMap (H := ZAlg π α) m hm (AlgHom.kernelPoint a.ofConv) =
            projectiveOrbitMap (H := ZAlg π α) m hm
              (AlgHom.kernelPoint (Bialgebra.counitAlgHom k (ZAlg π α)))) →
      (∀ b : WithConv (BAlg π α ψ →ₐ[k] k), BialgHom.mapDomain (fB π α ψ) b ∈
        CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k (ZAlg π α)) S
          (CommAlgCat.of k k)) →
      Group.IsSolvable (CommHopfAlgCat.quotientPointsSubgroup
        (_root_.CommHopfAlgCat.of k (ZAlg π α)) S (CommAlgCat.of k k)) →
      ∀ a : WithConv (ZAlg π α →ₐ[k] k),
        a ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k (ZAlg π α)) S
          (CommAlgCat.of k k) → a ∈ Set.range (BialgHom.mapDomain (fB π α ψ))) :
    Nonempty (R1Geom π α ψ hπ) := by
  classical
  haveI : Algebra.Smooth k (ZAlg π α) := smooth_quotient_magnetHopfIdeal π _
  haveI : Algebra.Smooth k (BAlg π α ψ) := smooth_parQuot (zCochar π α ψ)
  haveI : IsReduced (BAlg π α ψ) := isReduced_of_smooth k _
  haveI : ConnectedSpace (PrimeSpectrum (BAlg π α ψ)) :=
    connectedSpace_parabolic_of_levi (zCochar π α ψ) hLevi
  haveI : Algebra.Smooth k (BmAlg π α ψ) := smooth_parQuot (zCochar π α ψ).oppositeCocharacter
  haveI : IsReduced (BmAlg π α ψ) := isReduced_of_smooth k _
  haveI : ConnectedSpace (PrimeSpectrum (BmAlg π α ψ)) :=
    connectedSpace_parabolic_of_levi (zCochar π α ψ).oppositeCocharacter
      (by rw [leviDefiningHopfIdeal_oppositeCocharacter]; exact hLevi)
  exact r1Geom_of_inputs π α ψ hπ hT hLevi hCB
    (R1Geometry.orbitInput_of_opposite (fB π α ψ) (TZ π α ψ hπ) (fBm π α ψ)
      (hTB_opp π α ψ hπ) (hgen_opp π α ψ hZconn) hT2 hBorStab)

end AlgMag.Reductive
