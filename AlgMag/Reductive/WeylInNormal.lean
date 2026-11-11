/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.SliceTangentFinal
import AlgMag.Reductive.PointsDensity
import AlgMag.Reductive.RootGroupInNormal

/-!
# Step 5 of the converse: the Weyl point lies in `U(k) · T(k)`

* `exists_open_sliceConjugates`: the C2(d) open set of `K(k)` (`EtaleSliceAssembly.lean`,
  `exists_open_regularConjugates`) with the conjugating point kept as a product `u v` of points of
  the slice root groups `U⁻ = G^{[R ∩ λ<0⟩}_e`, `U⁺ = G^{[R ∩ λ>0⟩}_e` (same proof).
* `exists_open_sliceConjugates_lattice`: its hypothesis-free form for split reductive data on a
  lattice (`SliceSmooth.smooth_sliceSource`, `sliceTangentBijective_lattice`, `sliceSrc_lattice`).
-/

suppress_compilation

set_option linter.style.haveILetI false

open Magnetism TauCeti WithConv TensorProduct
open scoped AlgMag.Reductive.Zariski

namespace AlgMag.Reductive

universe u

section Slice

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X) [Module.Finite k (Bialgebra.CotangentSpace k H)]
  [IsAlgClosed k] [Algebra.FiniteType k H] [Algebra.Smooth k H]
variable (N : Magnet (Additive X)) (ψ : X →* Multiplicative ℤ)
  (hT : compIdeal π N ≤ RingHom.ker π.toAlgHom)

/-- **C2(d), keeping the conjugating point**: `K(k)` contains a nonempty open set of points
`(u v) t (u v)⁻¹` with `u ∈ U⁻(k)`, `v ∈ U⁺(k)`, `t` regular. -/
theorem exists_open_sliceConjugates
    (hψ : ∀ α ∈ roots π, α ∈ N → pairingHom ψ α ≠ 0)
    (hsmooth : Algebra.Smooth k (sliceSource π N ψ))
    (htan : ∀ τ : MonoidAlgebra k X →ₐ[k] k,
      (∀ α ∈ roots π, α ∈ N → τ (MonoidAlgebra.single (Additive.toMul α) 1) ≠ 1) →
        SliceTangentBijective π N ψ hT (sliceBasePt π N ψ τ)) :
    ∃ U : Set (compSubgroup π N), IsOpen U ∧ U.Nonempty ∧
      ∀ x ∈ U, ∃ u v t : WithConv (H →ₐ[k] k),
        (∀ h ∈ (sliceIdeal π N ψ⁻¹).toIdeal, u.ofConv h = 0) ∧
        (∀ h ∈ (sliceIdeal π N ψ).toIdeal, v.ofConv h = 0) ∧ t ∈ regularPoints π N ∧
        (x : WithConv (H →ₐ[k] k)) = (u * v) * t * (u * v)⁻¹ := by
  obtain ⟨t₀, τ, -, hτ⟩ := regularPoints_nonempty π N (finite_roots (π := π)) ψ hψ
  have hreg₀ : ∀ α ∈ roots π, α ∈ N → sliceBasePt π N ψ τ
      (sliceTorusHom π N ψ (MonoidAlgebra.single (Additive.toMul α) 1)) ≠ 1 := by
    intro α hα hN
    rw [sliceBasePt_torus]
    exact hτ α hα hN
  obtain ⟨s, hs0, hsreg, hflat, hfp⟩ :=
    exists_etale_slice π N ψ hT hsmooth (sliceBasePt π N ψ τ) hreg₀ (htan τ hτ)
  letI := sliceAlgebra π N ψ hT
  haveI : IsScalarTower k (compAlg π N) (sliceSource π N ψ) :=
    IsScalarTower.of_algebraMap_eq (fun c => ((sliceMap π N ψ hT).commutes c).symm)
  haveI : Module.Flat (compAlg π N) (Localization.Away s) := hflat
  haveI : Algebra.FinitePresentation (compAlg π N) (Localization.Away s) := hfp
  haveI := hsmooth
  letI : Algebra H (Localization.Away s) := ((algebraMap (compAlg π N) (Localization.Away s)).comp (algebraMap H (compAlg π N))).toAlgebra
  haveI : @IsScalarTower H (compAlg π N) (Localization.Away s) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : @IsScalarTower k H (Localization.Away s) Algebra.toSMul Algebra.toSMul Algebra.toSMul := by
    refine IsScalarTower.of_algebraMap_eq (fun c => ?_)
    rw [IsScalarTower.algebraMap_apply k (sliceSource π N ψ) (Localization.Away s) c]
    change _ = algebraMap (compAlg π N) (Localization.Away s) (algebraMap H (compAlg π N) (algebraMap k H c))
    rw [IsScalarTower.algebraMap_apply (compAlg π N) (sliceSource π N ψ) (Localization.Away s), ← IsScalarTower.algebraMap_apply k H (compAlg π N)]
    exact congrArg _ ((sliceMap π N ψ hT).commutes c).symm
  haveI : Algebra.FiniteType k (Localization.Away s) :=
    Algebra.FiniteType.trans (S := (sliceSource π N ψ)) inferInstance inferInstance
  have hp : Function.Surjective (algebraMap H (compAlg π N)) := compMk_surjective π N
  have hK : ∀ x, x ∈ (compSubgroup π N : Set (WithConv (H →ₐ[k] k))) ↔
      RingHom.ker (algebraMap H (compAlg π N)) ≤ RingHom.ker x.ofConv := fun x => mem_compSubgroup π N x
  -- every point of `(Localization.Away s)` lies over `K`
  have hmemK : ∀ y : (Localization.Away s) →ₐ[k] k,
      toConv (y.comp (IsScalarTower.toAlgHom k H (Localization.Away s))) ∈ compSubgroup π N := by
    intro y
    refine (hK _).2 fun h hh => ?_
    rw [RingHom.mem_ker] at hh ⊢
    change y (algebraMap (compAlg π N) (Localization.Away s) (algebraMap H (compAlg π N) h)) = 0
    rw [hh, map_zero, map_zero]
  refine ⟨Subtype.val ⁻¹' liftPoints (k := k) (H := H) (Localization.Away s),
    isOpen_liftPoints_subtype (A := compAlg π N) hp _ hK, ?_, ?_⟩
  · have hu : ∀ y : Submonoid.powers s, IsUnit (sliceBasePt π N ψ τ y) := by
      rintro ⟨_, n, rfl⟩
      change IsUnit (sliceBasePt π N ψ τ (s ^ n))
      rw [map_pow]
      exact (isUnit_iff_ne_zero.2 hs0).pow n
    let y' : (Localization.Away s) →ₐ[k] k := IsLocalization.liftAlgHom (M := Submonoid.powers s) hu
    exact ⟨⟨_, hmemK y'⟩, ⟨y', rfl⟩⟩
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    let z : (sliceSource π N ψ) →ₐ[k] k := y.comp (IsScalarTower.toAlgHom k (sliceSource π N ψ) (Localization.Away s))
    have hz : z s ≠ 0 := by
      intro h0
      have hu : IsUnit (y (algebraMap (sliceSource π N ψ) (Localization.Away s) s)) :=
        (IsLocalization.Away.algebraMap_isUnit s).map y
      exact hu.ne_zero h0
    have hx' : x = AlgHom.mapValue z (sliceConj π N ψ) := by
      apply WithConv.ofConv_injective
      ext h
      rw [← hy, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply, AlgHom.comp_apply,
        ← sliceMap_compMk π N ψ hT h]
      rfl
    refine ⟨AlgHom.mapValue z (slicePtMinus π N ψ), AlgHom.mapValue z (slicePtPlus π N ψ),
      AlgHom.mapValue z (slicePtTorus π N ψ), fun h hh => ?_, fun h hh => ?_,
      ⟨z.comp (sliceTorusHom π N ψ), rfl, fun α hα hN => hsreg z hz α hα hN⟩, ?_⟩
    · rw [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply]
      change z (Algebra.TensorProduct.includeLeft (S := k) (Algebra.TensorProduct.includeLeft
        (S := k) (Ideal.Quotient.mk (sliceIdeal π N ψ⁻¹).toIdeal h))) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hh, map_zero, map_zero]
      exact map_zero z
    · rw [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply]
      change z (Algebra.TensorProduct.includeLeft (S := k) (Algebra.TensorProduct.includeRight
        (Ideal.Quotient.mk (sliceIdeal π N ψ).toIdeal h))) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hh, map_zero, map_zero]
      exact map_zero z
    · change x = _
      rw [hx', sliceConj, conjFormula, map_mul, map_mul, map_inv, map_mul]

end Slice

section Lattice

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X) [Module.Finite k (Bialgebra.CotangentSpace k H)]
  [IsAlgClosed k] [Algebra.FiniteType k H] [Algebra.Smooth k H]
variable (D : SplitReductiveData π) [Monoid.FG X] [IsMulTorsionFree X]

include D in
/-- **C2(d) with slice root groups, for split reductive data on a lattice, hypothesis-free.** -/
theorem exists_open_sliceConjugates_lattice (N : Magnet (Additive X))
    (ψ : X →* Multiplicative ℤ) (hψ : ∀ α ∈ roots π, α ∈ N → pairingHom ψ α ≠ 0) :
    ∃ U : Set (compSubgroup π N), IsOpen U ∧ U.Nonempty ∧
      ∀ x ∈ U, ∃ u v t : WithConv (H →ₐ[k] k),
        (∀ h ∈ (sliceIdeal π N ψ⁻¹).toIdeal, u.ofConv h = 0) ∧
        (∀ h ∈ (sliceIdeal π N ψ).toIdeal, v.ofConv h = 0) ∧ t ∈ regularPoints π N ∧
        (x : WithConv (H →ₐ[k] k)) = (u * v) * t * (u * v)⁻¹ :=
  exists_open_sliceConjugates π N ψ (compIdeal_le_ker_torus π D N) hψ
    (SliceSmooth.smooth_sliceSource π N ψ)
    (fun τ hτ => sliceTangentBijective_lattice π D N ψ hψ τ hτ (sliceSrc_lattice π D N ψ τ))

end Lattice

section TorusPoints

open AlgMag.Weyl

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X]
variable (π : H →ₐc[k] MonoidAlgebra k X)

/-- Points of `D(X)` commute. -/
lemma torusAlgHom_comm {A : Type*} [CommRing A] [Algebra k A]
    (a b : MonoidAlgebra k X →ₐ[k] A) : toConv a * toConv b = toConv b * toConv a := by
  apply WithConv.ofConv_injective
  apply MonoidAlgebra.algHom_ext
  · intro x
    rw [AlgHom.convMul_apply, AlgHom.convMul_apply]
    simp [mul_comm]
  · exact Subsingleton.elim _ _

/-- Points of `T` (factoring through `π`) commute. -/
lemma torusPt_comm {A : Type*} [CommRing A] [Algebra k A] (a b : MonoidAlgebra k X →ₐ[k] A) :
    toConv (a.comp π.toAlgHom) * toConv (b.comp π.toAlgHom) =
      toConv (b.comp π.toAlgHom) * toConv (a.comp π.toAlgHom) := by
  have e : ∀ c d : MonoidAlgebra k X →ₐ[k] A,
      toConv (c.comp π.toAlgHom) * toConv (d.comp π.toAlgHom) =
        toConv (((toConv c * toConv d : WithConv _).ofConv).comp π.toAlgHom) := by
    intro c d
    apply WithConv.ofConv_injective
    rw [ofConv_toConv]
    exact (AlgHom.convMul_comp_bialgHom_distrib (toConv c) (toConv d) π).symm
  rw [e, e, torusAlgHom_comm]

/-- **A point of `T` normalizes `T` with the identity automorphism.** -/
lemma isNormalizingWith_torus {A : Type*} [CommRing A] [Algebra k A]
    (τ : MonoidAlgebra k X →ₐ[k] A) : IsNormalizingWith π A (toConv (τ.comp π.toAlgHom)) 1 := by
  have h1 : (1 : X ≃* X).toMonoidHom = MonoidHom.id X := rfl
  rw [IsNormalizingWith, h1, twistPoint_id, MulAut.conj_apply]
  have hL : AlgHom.mapValue (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := A)
      (B := MonoidAlgebra k X)) (toConv (τ.comp π.toAlgHom)) =
      toConv (((Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := A)
        (B := MonoidAlgebra k X)).comp τ).comp π.toAlgHom) := by
    rw [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_assoc]
  have hT : torusPoint π A = toConv ((Algebra.TensorProduct.includeRight (R := k) (A := A)
      (B := MonoidAlgebra k X)).comp π.toAlgHom) := rfl
  rw [hL, hT, torusPt_comm π]
  exact mul_inv_cancel_right (G := WithConv (H →ₐ[k] A ⊗[k] MonoidAlgebra k X)) _ _

end TorusPoints

section Levi

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X) [IsAlgClosed k] [Algebra.FiniteType k H]

/-- **A connected attractor is its own identity component**: `(G^N)° = G^N` when `Spec O(G^N)` is
connected. -/
theorem compIdeal_eq_magnetIdeal_of_connected (N : Magnet (Additive X))
    [ConnectedSpace (PrimeSpectrum (H ⧸ (magnetHopfIdeal π N).toIdeal))] :
    compIdeal π N = magnetIdeal (torusGrading π) N := by
  have : Algebra.FiniteType k (H ⧸ (magnetHopfIdeal π N).toIdeal) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k _) (Ideal.Quotient.mkₐ_surjective k _)
  have hbot : (attrComp π N).toIdeal = ⊥ := by
    rw [attrComp, HopfAlgebra.identityComponentHopfIdeal_toIdeal]
    simp only [PrimeSpectrum.connectedComponentIdeal]
    have : IsNoetherianRing (H ⧸ (magnetHopfIdeal π N).toIdeal) :=
      Algebra.FiniteType.isNoetherianRing k _
    erw [PrimeSpectrum.connectedComponentIdempotent_eq_one]
    rw [sub_self, Ideal.span_singleton_eq_bot]
  ext x
  rw [compIdeal, RingHom.mem_ker]
  change Ideal.Quotient.mk (attrComp π N).toIdeal (Ideal.Quotient.mk _ x) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, hbot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem,
    magnetHopfIdeal_toIdeal]

end Levi

section Perp

variable {X : Type u} [CommGroup X] [DecidableEq X]

omit [DecidableEq X] in
lemma pairingHom_mul_zpow (ψ₁ ψ₂ : X →* Multiplicative ℤ) (a b : ℤ) (χ : Additive X) :
    pairingHom (ψ₂ ^ a * ψ₁ ^ b) χ = a * pairingHom ψ₂ χ + b * pairingHom ψ₁ χ := by
  simp [pairingHom_apply, MonoidHom.mul_apply, toAdd_mul, toAdd_zpow]

/-- **A cocharacter orthogonal to `α` and nonzero on a finite set off `ℚα`**, together with one
nonzero on `α`. -/
theorem exists_perp_cocharacter [Module.Free ℤ (Additive X)] {α : Additive X} (hα0 : α ≠ 0)
    (R : Set (Additive X)) (hR : R.Finite)
    (hRα : ∀ β ∈ R, ∀ m n : ℤ, n ≠ 0 → n • β ≠ m • α) :
    ∃ ψ₁ μ : X →* Multiplicative ℤ, pairingHom ψ₁ α ≠ 0 ∧ pairingHom μ α = 0 ∧
      ∀ β ∈ R, pairingHom μ β ≠ 0 := by
  obtain ⟨ψ₁, hψ₁⟩ := exists_generic_cocharacter {α} (Set.finite_singleton α)
    (fun β hβ => by rw [Set.mem_singleton_iff.1 hβ]; exact hα0)
  have ha : pairingHom ψ₁ α ≠ 0 := hψ₁ α rfl
  set a := pairingHom ψ₁ α
  set R₂ := (fun β => a • β - pairingHom ψ₁ β • α) '' R
  obtain ⟨ψ₂, hψ₂⟩ := exists_generic_cocharacter R₂ (hR.image _) (by
    rintro _ ⟨β, hβ, rfl⟩ h0
    exact hRα β hβ (pairingHom ψ₁ β) a ha (sub_eq_zero.1 h0))
  refine ⟨ψ₁, ψ₂ ^ a * ψ₁ ^ (-pairingHom ψ₂ α), ha, ?_, fun β hβ => ?_⟩
  · rw [pairingHom_mul_zpow]; ring
  · have h := hψ₂ _ ⟨β, hβ, rfl⟩
    rw [pairingHom_mul_zpow]
    rw [map_sub, map_zsmul, map_zsmul, smul_eq_mul, smul_eq_mul] at h
    intro h0; apply h; linarith

end Perp

section Endgame

open AlgMag.Weyl

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X) [Module.Finite k (Bialgebra.CotangentSpace k H)]
  [IsAlgClosed k] [Algebra.FiniteType k H] [Algebra.Smooth k H]
variable [Monoid.FG X] [IsMulTorsionFree X]

/-- **Step 5 of the converse (endgame).** Let `U = V(I)` be a normal subgroup with `U ∩ T = e`
containing the root groups `U_{±α}` of a root `α` with `Φ ∩ ℚα = {±α}`. Then no point of the
rank-one attractor `G^{ℤα}` normalizes `T` acting by `σ` with `σ α = -α`.

Proof: the Levi `L = G^{μ^⊥}` (`μ ⊥ α` generic, `exists_perp_cocharacter`) is connected
(`connectedSpace_levi_of_openCell`), so `L(k)` is irreducible (`irreducibleSpace_points`) and
contains `n`; the slice open set (`exists_open_sliceConjugates_lattice`) lies in the subgroup
`U(k) T(k)` (its slice root groups are `U_{±α} ⊆ U`), hence so does `L(k)`
(`subset_of_isOpen_subset`); writing `n = v t`, `v ∈ U(k)` normalizes `T` with `σ`, so `σ = 1`
(`eq_one_of_isNormalizingWith_of_mem`), contradicting `σ α = -α`. -/
theorem false_of_weylPoint [Module.IsTorsionFree ℤ (Additive X)] (D : SplitReductiveData π)
    [IrreducibleSpace (PrimeSpectrum H)]
    {α : Additive X} (hα : α ∈ roots π)
    (hline : ∀ β ∈ roots π, (∃ m n : ℤ, n ≠ 0 ∧ n • β = m • α) → β = α ∨ β = -α)
    {I : HopfIdeal k H} (hI : I.IsNormal)
    (hUT : ∀ g : WithConv (H →ₐ[k] k ⊗[k] MonoidAlgebra k X), (∀ h ∈ I, g.ofConv h = 0) →
      (∀ h ∈ RingHom.ker π.toAlgHom, g.ofConv h = 0) → g = 1)
    (hUα : I.toIdeal ≤ prescribedUnitIdeal π (rayMagnet α))
    (hUα' : I.toIdeal ≤ prescribedUnitIdeal π (rayMagnet (-α)))
    {n : WithConv (H →ₐ[k] k)} {σ : X ≃* X} (hn : IsNormalizingWith π k n σ)
    (hnα : n ∈ attractorSubgroup π (lineMagnet α) k)
    (hσα : σ (Additive.toMul α) = (Additive.toMul α)⁻¹) : False := by
  have hπ : Function.Surjective π := D.surjective
  haveI : Module.Finite ℤ (Additive X) :=
    Module.Finite.iff_addGroup_fg.2 (AddGroup.fg_iff_addMonoid_fg.2
      (Monoid.fg_iff_add_fg.1 inferInstance))
  haveI : Module.Free ℤ (Additive X) := Module.free_of_finite_type_torsion_free'
  have hα0 : α ≠ 0 := ne_zero_of_mem_roots hα
  have hnegα : -α ∈ roots π := by
    have h := mem_roots_of_isNormalizingWith π hn hα
    rw [hσα] at h
    exact h
  have hσ : σ ≠ 1 := by
    rintro rfl
    have h1 : Additive.toMul α = (Additive.toMul α)⁻¹ := hσα
    have h2 : (2 : ℤ) • α = 0 := by
      rw [two_zsmul]
      apply Additive.toMul.injective
      rw [toMul_add, toMul_zero]
      nth_rewrite 1 [h1]
      exact inv_mul_cancel _
    exact hα0 ((smul_eq_zero_iff_right two_ne_zero).mp h2)
  -- the cocharacter `μ ⊥ α`, generic
  set R : Set (Additive X) := {β | β ∈ roots π ∧ β ≠ α ∧ β ≠ -α}
  have hRfin : R.Finite := (finite_roots (π := π)).subset fun β h => h.1
  have hRα : ∀ β ∈ R, ∀ m n : ℤ, n ≠ 0 → n • β ≠ m • α := by
    intro β hβ m n hn0 he
    rcases hline β hβ.1 ⟨m, n, hn0, he⟩ with h | h
    · exact hβ.2.1 h
    · exact hβ.2.2 h
  obtain ⟨ψ₁, μ, hψ₁, hμα, hμR⟩ := exists_perp_cocharacter hα0 R hRfin hRα
  set N' : Magnet (Additive X) := (⊥ : Magnet ℤ).comap (pairingHom μ) with hN'
  have hmemN' : ∀ χ, χ ∈ N' ↔ pairingHom μ χ = 0 := fun χ => by
    simp [N']
  have hrootsN' : ∀ β ∈ roots π, β ∈ N' → β = α ∨ β = -α := by
    intro β hβ hN
    by_contra h
    push Not at h
    exact hμR β ⟨hβ, h.1, h.2⟩ ((hmemN' β).1 hN)
  -- the Levi `G^{N'}` is connected, hence is its own identity component
  haveI : ConnectedSpace (PrimeSpectrum (H ⧸ (magnetHopfIdeal π N').toIdeal)) := by
    rw [magnetHopfIdeal_toIdeal, hN', magnetIdeal_torusGrading_comap_bot]
    exact connectedSpace_levi_of_openCell (π.cocharacter μ)
      (isOpenEmbedding_openCell (π.cocharacter μ))
  have hcomp := compIdeal_eq_magnetIdeal_of_connected π N'
  set K : Set (WithConv (H →ₐ[k] k)) := (compSubgroup π N' : Set (WithConv (H →ₐ[k] k)))
  have hK : ∀ x, x ∈ K ↔ compIdeal π N' ≤ RingHom.ker x.ofConv := mem_compSubgroup π N'
  haveI : IrreducibleSpace K := irreducibleSpace_points π N' K hK
  have hnK : n ∈ K := by
    rw [hK, hcomp]
    refine le_trans ?_ ((mem_attractorSubgroup π).1 hnα)
    rw [magnetIdeal, magnetIdeal]
    apply Ideal.span_mono
    intro x hx
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨χ, hχ, hx⟩ := hx
    refine ⟨χ, fun h => hχ ?_, hx⟩
    obtain ⟨z, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 h
    rw [hmemN', map_zsmul, hμα, smul_zero]
  -- the slice root groups are `U_{±α}`
  have hslice : ∀ ψ : X →* Multiplicative ℤ, pairingHom ψ α ≠ 0 →
      I.toIdeal ≤ (sliceIdeal π N' ψ).toIdeal := by
    intro ψ hψα
    rw [sliceIdeal_toIdeal]
    rcases lt_or_gt_of_ne hψα with hneg | hpos
    · have hS : sliceRoots π N' ψ = {-α} := by
        ext β
        simp only [sliceRoots, Set.mem_ofPred_eq, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hβ, hN, hp⟩
          rcases hrootsN' β hβ hN with rfl | rfl
          · exact absurd hp (by omega)
          · rfl
        · intro hβ
          rw [hβ]
          refine ⟨hnegα, ?_, ?_⟩
          · rw [hmemN', map_neg, hμα, neg_zero]
          · rw [map_neg]; omega
      have : sliceMagnet π N' ψ = rayMagnet (-α) := by rw [sliceMagnet, hS]; rfl
      rw [this]; exact hUα'
    · have hS : sliceRoots π N' ψ = {α} := by
        ext β
        simp only [sliceRoots, Set.mem_ofPred_eq, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hβ, hN, hp⟩
          rcases hrootsN' β hβ hN with rfl | rfl
          · rfl
          · rw [map_neg] at hp; exact absurd hp (by omega)
        · intro hβ
          rw [hβ]
          exact ⟨hα, (hmemN' α).2 hμα, hpos⟩
      have : sliceMagnet π N' ψ = rayMagnet α := by rw [sliceMagnet, hS]; rfl
      rw [this]; exact hUα
  have hψ : ∀ β ∈ roots π, β ∈ N' → pairingHom ψ₁ β ≠ 0 := by
    intro β hβ hN
    rcases hrootsN' β hβ hN with rfl | rfl
    · exact hψ₁
    · rw [map_neg]; exact neg_ne_zero.2 hψ₁
  have hψinv : pairingHom ψ₁⁻¹ α ≠ 0 := by
    simpa [pairingHom_apply] using hψ₁
  obtain ⟨O, hO, hOn, hOx⟩ := exists_open_sliceConjugates_lattice π D N' ψ₁ hψ
  -- the subgroup `U(k) T(k)`
  set Ucap := CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of k H) I (CommAlgCat.of k k)
  have hmemU : ∀ g : WithConv (H →ₐ[k] k), g ∈ Ucap ↔ ∀ h ∈ I, g.ofConv h = 0 := fun g =>
    CommHopfAlgCat.mem_quotientPointsSubgroup_iff (CommHopfAlgCat.of k H) I (CommAlgCat.of k k) g
  haveI hUn : Ucap.Normal :=
    CommHopfAlgCat.quotientPointsSubgroup_normal (CommHopfAlgCat.of k H) I hI (CommAlgCat.of k k)
  set Tp := CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of k H)
    (HopfIdeal.kerOfSurjective π hπ) (CommAlgCat.of k k)
  have hmemT : ∀ g : WithConv (H →ₐ[k] k), g ∈ Tp ↔ ∀ h, π h = 0 → g.ofConv h = 0 := by
    intro g
    rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    exact forall_congr' fun h => by rw [HopfIdeal.mem_kerOfSurjective]
  set S := Ucap ⊔ Tp
  have hOS : ∀ x ∈ O, (x : WithConv (H →ₐ[k] k)) ∈ S := by
    intro x hx
    obtain ⟨u, v, t, hu, hv, ht, hxe⟩ := hOx x hx
    have huU : u ∈ Ucap := (hmemU u).2 fun h hh => hu h (hslice ψ₁⁻¹ hψinv hh)
    have hvU : v ∈ Ucap := (hmemU v).2 fun h hh => hv h (hslice ψ₁ hψ₁ hh)
    have htT : t ∈ Tp := by
      obtain ⟨τ, rfl, -⟩ := ht
      refine (hmemT _).2 fun h hh => ?_
      change τ (π h) = 0
      rw [hh, map_zero]
    rw [hxe, Subgroup.mem_sup_of_normal_left]
    have huv : u * v ∈ Ucap := Ucap.mul_mem huU hvU
    refine ⟨(u * v) * (t * (u * v)⁻¹ * t⁻¹), Ucap.mul_mem huv
      (hUn.conj_mem _ (Ucap.inv_mem huv) t), t, htT, by group⟩
  have hnS : n ∈ S := subset_of_isOpen_subset K
    (fun x hx y hy => (compSubgroup π N').mul_mem hx hy)
    (fun x hx => (compSubgroup π N').inv_mem hx) S O hO hOn hOS n hnK
  obtain ⟨v, hv, t, ht, hvt⟩ := Subgroup.mem_sup_of_normal_left.1 hnS
  -- `t = τ₀ ∘ π`
  have hker : RingHom.ker π.toAlgHom ≤ RingHom.ker t.ofConv := fun h hh =>
    (hmemT t).1 ht h hh
  have hπ' : Function.Surjective π.toAlgHom := hπ
  set τ₀ : MonoidAlgebra k X →ₐ[k] k := (Ideal.Quotient.liftₐ (RingHom.ker π.toAlgHom) t.ofConv
      (fun h hh => hker hh)).comp (Ideal.quotientKerAlgEquivOfSurjective hπ').symm.toAlgHom
  have htτ : t = toConv (τ₀.comp π.toAlgHom) := by
    apply WithConv.ofConv_injective
    ext h
    have he : (Ideal.quotientKerAlgEquivOfSurjective hπ').symm (π.toAlgHom h) =
        Ideal.Quotient.mk _ h :=
      Ideal.quotientKerAlgEquivOfSurjective_symm_apply hπ' h
    simp only [AlgHom.comp_apply, τ₀]
    erw [he]
    rfl
  have htN := isNormalizingWith_torus π (A := k) τ₀
  rw [← htτ] at htN
  have hvN : IsNormalizingWith π k v σ := by
    have h2 := (htN.inv π).mul π hn
    have hv' : v = n * t⁻¹ := by rw [← hvt]; group
    rw [hv']
    simpa using h2
  exact hσ (eq_one_of_isNormalizingWith_of_mem π hπ hI hUT ((hmemU v).1 hv) hvN)

end Endgame

end AlgMag.Reductive
