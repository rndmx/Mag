/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.RegularSlice
import AlgMag.Reductive.RegularSliceEtale
import AlgMag.Reductive.KaehlerLocalization
import AlgMag.Reductive.KaehlerFibreTangent
import AlgMag.Reductive.OpenImagePoints
import AlgMag.Reductive.GluePrereqs
import AlgMag.Reductive.RegularPointsNonempty
import AlgMag.Reductive.AttractorReflects
import AlgMag.Reductive.RegularSliceLattice
import AlgMag.Reductive.SliceSmooth
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Assembly of step C2(d): the étale slice and the open set of regular conjugates

* `exists_away_bijective_of_fibre_projective`: a linear map between finite projective modules
  which is bijective on the fibre at a point `B → L` is bijective over `B[1/t]` for all
  multiples `t` of some `r` not vanishing at the point.
* `exists_etale_slice`: `μ^* : O(K) → O(U⁻ × U⁺ × T)[1/s]` is flat of finite presentation,
  `s` invertible at the base point and `s ≠ 0` forcing regularity of the torus coordinate.
* `exists_open_regularConjugates`: `K(k)` (with `K = compSubgroup π N`) contains a nonempty open
  set of conjugates `g t g⁻¹`, `g ∈ K(k)`, `t` regular.

The hypotheses not yet available in the library are explicit: smoothness of `sliceSource`
(`hsmooth`, the statement of `SliceSmooth.smooth_sliceSource`) and the tangent identity at the
base point `(e, e, τ)` (`SliceTangentBijective`, i.e. `dμ` bijective; item 3 of part (a)).
-/

suppress_compilation

open Magnetism TauCeti WithConv TensorProduct
open scoped AlgMag.Reductive.Zariski

namespace AlgMag.Reductive

section Spread

variable {B M N : Type*} [CommRing B] [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]

/-- `IsLocalizedModule.map` along `M → A ⊗ M` is the base change. -/
lemma isLocalizedModule_map_mk_eq (S : Submonoid B) (A : Type*) [CommRing A] [Algebra B A]
    [IsLocalization S A] (f : M →ₗ[B] N) :
    IsLocalizedModule.map S (TensorProduct.mk B A M 1) (TensorProduct.mk B A N 1) f =
      (f.baseChange A).restrictScalars B := by
  apply IsLocalizedModule.linearMap_ext S (TensorProduct.mk B A M 1) (TensorProduct.mk B A N 1)
  rw [IsLocalizedModule.map_comp]
  ext m
  simp

/-- **Spreading out, projective version.** -/
theorem exists_away_bijective_of_fibre_projective
    [Module.Finite B M] [Module.Projective B M] [Module.Finite B N] [Module.Projective B N]
    {L : Type*} [Field L] [Algebra B L] (f : M →ₗ[B] N)
    (hL : Function.Bijective (f.baseChange L)) :
    ∃ r : B, algebraMap B L r ≠ 0 ∧ ∀ t : B, r ∣ t →
      Function.Bijective (f.baseChange (Localization.Away t)) := by
  classical
  set p : Ideal B := RingHom.ker (algebraMap B L)
  haveI : p.IsPrime := RingHom.ker_isPrime _
  let Bp := Localization.AtPrime p
  have hunit : ∀ y : p.primeCompl, IsUnit (algebraMap B L y) := fun y =>
    isUnit_iff_ne_zero.2 (fun h => y.2 (RingHom.mem_ker.2 h))
  letI : Algebra Bp L := (IsLocalization.lift (M := p.primeCompl) (S := Bp) hunit).toAlgebra
  haveI : IsScalarTower B Bp L := IsScalarTower.of_algebraMap_eq
    (fun x => (IsLocalization.lift_eq (M := p.primeCompl) (S := Bp) hunit x).symm)
  haveI : Module.Free Bp (Bp ⊗[B] M) := Module.free_of_flat_of_isLocalRing
  haveI : Module.Free Bp (Bp ⊗[B] N) := Module.free_of_flat_of_isLocalRing
  let fp := f.baseChange Bp
  let eM := AlgebraTensorModule.cancelBaseChange B Bp L L M
  let eN := AlgebraTensorModule.cancelBaseChange B Bp L L N
  have key : ∀ z, eN (fp.baseChange L z) = f.baseChange L (eM z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
    | tmul l w =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [tmul_add, map_add, map_add, hx, hy, map_add, map_add]
      | tmul a m =>
        simp [eN, eM, fp, AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.baseChange_tmul]
  have hLp : Function.Bijective (fp.baseChange L) := by
    have : ⇑(fp.baseChange L) = eN.symm ∘ f.baseChange L ∘ eM := by
      funext z; simp [← key]
    rw [this]
    exact eN.symm.bijective.comp (hL.comp eM.bijective)
  have hrank := finrank_eq_of_baseChange_bijective fp hLp
  let e : (Bp ⊗[B] N) ≃ₗ[Bp] (Bp ⊗[B] M) := LinearEquiv.ofFinrankEq _ _ hrank.symm
  let g := e.toLinearMap ∘ₗ fp
  have h1 : IsUnit (algebraMap Bp L (LinearMap.det g)) :=
    (baseChange_bijective_iff_isUnit_det L g).1 ((baseChange_comp_equiv_bijective_iff L fp e).2 hLp)
  have h2 : IsUnit (LinearMap.det g) := by
    by_contra hn
    have hm : LinearMap.det g ∈ IsLocalRing.maximalIdeal Bp := hn
    rw [← Localization.AtPrime.map_eq_maximalIdeal] at hm
    have hle : Ideal.map (algebraMap B Bp) p ≤ RingHom.ker (algebraMap Bp L) := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, RingHom.mem_ker, ← IsScalarTower.algebraMap_apply]
      exact hx
    have h0 := hle hm
    rw [RingHom.mem_ker] at h0
    rw [h0] at h1
    exact not_isUnit_zero h1
  have hg : Function.Bijective g :=
    (Module.End.isUnit_iff g).1 ((LinearMap.isUnit_iff_isUnit_det g).2 h2)
  have hfp : Function.Bijective fp := by
    have : ⇑fp = e.symm ∘ g := by funext x; simp [g]
    rw [this]; exact e.symm.bijective.comp hg
  have hloc : Function.Bijective (IsLocalizedModule.map p.primeCompl
      (TensorProduct.mk B Bp M 1) (TensorProduct.mk B Bp N 1) f) := by
    rw [isLocalizedModule_map_mk_eq]; exact hfp
  haveI : Module.FinitePresentation B N := Module.finitePresentation_of_projective B N
  obtain ⟨r, hr, hr'⟩ := exists_bijective_map_powers p.primeCompl _ _ f hloc
  refine ⟨r, fun h => hr (RingHom.mem_ker.2 h), fun t ht => ?_⟩
  have := hr' t ht
  rw [← IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective
    (TensorProduct.mk B (Localization.Away t) M 1) (TensorProduct.mk B (Localization.Away t) N 1),
    isLocalizedModule_map_mk_eq] at this
  exact this

end Spread

universe u

section Slice

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X) [Module.Finite k (Bialgebra.CotangentSpace k H)]
  [IsAlgClosed k] [Algebra.FiniteType k H] [Algebra.Smooth k H]
variable (N : Magnet (Additive X)) (ψ : X →* Multiplicative ℤ)
  (hT : compIdeal π N ≤ RingHom.ker π.toAlgHom)

/-- The `O(K)`-algebra structure on the slice ring given by `μ^*`. -/
abbrev sliceAlgebra : Algebra (compAlg π N) (sliceSource π N ψ) :=
  (sliceMap π N ψ hT).toRingHom.toAlgebra

/-- The torus coordinate `O(T) → O(U⁻) ⊗ O(U⁺) ⊗ O(T)`. -/
def sliceTorusHom : MonoidAlgebra k X →ₐ[k] sliceSource π N ψ :=
  (Algebra.TensorProduct.includeRight : MonoidAlgebra k X →ₐ[k]
    ((H ⧸ (sliceIdeal π N ψ⁻¹).toIdeal) ⊗[k] (H ⧸ (sliceIdeal π N ψ).toIdeal)) ⊗[k]
      MonoidAlgebra k X)

/-- The counit of `O(U^±)`. -/
def sliceCounit : H ⧸ (sliceIdeal π N ψ).toIdeal →ₐ[k] k :=
  Ideal.Quotient.liftₐ _ (Bialgebra.counitAlgHom k H)
    (fun x hx => (sliceIdeal π N ψ).counit_eq_zero (HopfIdeal.mem_toIdeal.1 hx))

/-- The base point `(e, e, τ)` of the slice. -/
def sliceBasePt (τ : MonoidAlgebra k X →ₐ[k] k) : sliceSource π N ψ →ₐ[k] k :=
  Algebra.TensorProduct.productMap
    (Algebra.TensorProduct.productMap (sliceCounit π N ψ⁻¹) (sliceCounit π N ψ)) τ

lemma sliceBasePt_torus (τ : MonoidAlgebra k X →ₐ[k] k) (m : MonoidAlgebra k X) :
    sliceBasePt π N ψ τ (sliceTorusHom π N ψ m) = τ m := by
  change Algebra.TensorProduct.productMap _ τ (1 ⊗ₜ m) = _
  rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul]

/-- **Tangent hypothesis** (item 3 of C2(d) part (a)): at the point `y₀`, the tangent map
`Der_k(O(U⁻ × U⁺ × T), k) → Der_k(O(K), k)` of `μ` is bijective. -/
def SliceTangentBijective (y₀ : sliceSource π N ψ →ₐ[k] k) : Prop :=
  letI := sliceAlgebra π N ψ hT
  letI : Algebra (sliceSource π N ψ) k := y₀.toRingHom.toAlgebra
  letI : Algebra (compAlg π N) k := (y₀.comp (sliceMap π N ψ hT)).toRingHom.toAlgebra
  haveI : IsScalarTower k (compAlg π N) (sliceSource π N ψ) :=
    IsScalarTower.of_algebraMap_eq (fun c => ((sliceMap π N ψ hT).commutes c).symm)
  haveI : IsScalarTower (compAlg π N) (sliceSource π N ψ) k :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower k (sliceSource π N ψ) k :=
    IsScalarTower.of_algebraMap_eq (fun c => (y₀.commutes c).symm)
  haveI : IsScalarTower k (compAlg π N) k :=
    IsScalarTower.of_algebraMap_eq (fun c => ((y₀.comp (sliceMap π N ψ hT)).commutes c).symm)
  Function.Bijective (tangentPullback k (compAlg π N) (sliceSource π N ψ) k)

/-- **The étale slice** (C2(d), flatness). -/
theorem exists_etale_slice (hsmooth : Algebra.Smooth k (sliceSource π N ψ))
    (y₀ : sliceSource π N ψ →ₐ[k] k)
    (hreg₀ : ∀ α ∈ roots π, α ∈ N →
      y₀ (sliceTorusHom π N ψ (MonoidAlgebra.single (Additive.toMul α) 1)) ≠ 1)
    (htan : SliceTangentBijective π N ψ hT y₀) :
    ∃ s : sliceSource π N ψ, y₀ s ≠ 0 ∧
      (∀ y : sliceSource π N ψ →ₐ[k] k, y s ≠ 0 → ∀ α ∈ roots π, α ∈ N →
        y (sliceTorusHom π N ψ (MonoidAlgebra.single (Additive.toMul α) 1)) ≠ 1) ∧
      letI := sliceAlgebra π N ψ hT
      Module.Flat (compAlg π N) (Localization.Away s) ∧
        Algebra.FinitePresentation (compAlg π N) (Localization.Away s) := by
  classical
  letI := sliceAlgebra π N ψ hT
  letI : Algebra (sliceSource π N ψ) k := y₀.toRingHom.toAlgebra
  letI : Algebra (compAlg π N) k := (y₀.comp (sliceMap π N ψ hT)).toRingHom.toAlgebra
  haveI : IsScalarTower k (compAlg π N) (sliceSource π N ψ) :=
    IsScalarTower.of_algebraMap_eq (fun c => ((sliceMap π N ψ hT).commutes c).symm)
  haveI : IsScalarTower (compAlg π N) (sliceSource π N ψ) k :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower k (sliceSource π N ψ) k :=
    IsScalarTower.of_algebraMap_eq (fun c => (y₀.commutes c).symm)
  haveI : IsScalarTower k (compAlg π N) k :=
    IsScalarTower.of_algebraMap_eq (fun c => ((y₀.comp (sliceMap π N ψ hT)).commutes c).symm)
  haveI : Algebra.Smooth k (compAlg π N) := smooth_compAlg π N
  haveI := hsmooth
  haveI : Algebra.FinitePresentation (compAlg π N) (sliceSource π N ψ) :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation k _ _
  have hL : Function.Bijective ((KaehlerDifferential.mapBaseChange k (compAlg π N)
      (sliceSource π N ψ)).baseChange k) :=
    (bijective_fibre_mapBaseChange_iff k (compAlg π N) (sliceSource π N ψ) k).2 htan
  obtain ⟨r, hr, hr'⟩ := exists_away_bijective_of_fibre_projective (L := k) _ hL
  set R := (finite_roots (π := π)).toFinset.filter (· ∈ N)
  set Δ : sliceSource π N ψ := sliceTorusHom π N ψ
    (∏ α ∈ R, (MonoidAlgebra.single (Additive.toMul α) 1 - 1))
  have hΔ : ∀ y : sliceSource π N ψ →ₐ[k] k, y Δ =
      ∏ α ∈ R, (y (sliceTorusHom π N ψ (MonoidAlgebra.single (Additive.toMul α) 1)) - 1) := by
    intro y; simp [Δ, map_prod, map_sub]
  refine ⟨r * Δ, ?_, ?_, ?_⟩
  · rw [map_mul, hΔ]
    refine mul_ne_zero hr (Finset.prod_ne_zero_iff.2 fun α hα => sub_ne_zero.2 ?_)
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hα
    exact hreg₀ α ((finite_roots (π := π)).mem_toFinset.1 h1) h2
  · intro y hy α hα hN h
    apply hy
    rw [map_mul, hΔ, Finset.prod_eq_zero (i := α)
      (Finset.mem_filter.2 ⟨(finite_roots (π := π)).mem_toFinset.2 hα, hN⟩) (by rw [h, sub_self]),
      mul_zero]
  · have hb := hr' (r * Δ) (dvd_mul_right r Δ)
    exact ⟨flat_away_of_baseChange_bijective (r * Δ) hb, finitePresentation_away (r * Δ)⟩

/-- **Step C2(d)**: `K(k)` contains a nonempty open set of conjugates of regular points
(`K = compSubgroup π N`). -/
theorem exists_open_regularConjugates
    (hψ : ∀ α ∈ roots π, α ∈ N → pairingHom ψ α ≠ 0)
    (hsmooth : Algebra.Smooth k (sliceSource π N ψ))
    (htan : ∀ τ : MonoidAlgebra k X →ₐ[k] k,
      (∀ α ∈ roots π, α ∈ N → τ (MonoidAlgebra.single (Additive.toMul α) 1) ≠ 1) →
        SliceTangentBijective π N ψ hT (sliceBasePt π N ψ τ)) :
    ∃ U : Set (compSubgroup π N), IsOpen U ∧ U.Nonempty ∧
      ∀ x ∈ U, ∃ g ∈ compSubgroup π N, ∃ t ∈ regularPoints π N,
        (x : WithConv (H →ₐ[k] k)) = g * t * g⁻¹ := by
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
    refine ⟨AlgHom.mapValue z (slicePtMinus π N ψ) * AlgHom.mapValue z (slicePtPlus π N ψ),
      Subgroup.mul_mem _ ?_ ?_, AlgHom.mapValue z (slicePtTorus π N ψ),
      ⟨z.comp (sliceTorusHom π N ψ), rfl, fun α hα hN => hsreg z hz α hα hN⟩, ?_⟩
    · refine (mem_compSubgroup π N _).2 fun h hh => ?_
      have := compIdeal_le_sliceIdeal π N ψ⁻¹ hh
      rw [RingHom.mem_ker, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply]
      change z (Algebra.TensorProduct.includeLeft (S := k) (Algebra.TensorProduct.includeLeft
        (S := k) (Ideal.Quotient.mk (sliceIdeal π N ψ⁻¹).toIdeal h))) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.2 this, map_zero, map_zero]
      exact map_zero z
    · refine (mem_compSubgroup π N _).2 fun h hh => ?_
      have := compIdeal_le_sliceIdeal π N ψ hh
      rw [RingHom.mem_ker, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply]
      change z (Algebra.TensorProduct.includeLeft (S := k) (Algebra.TensorProduct.includeRight
        (Ideal.Quotient.mk (sliceIdeal π N ψ).toIdeal h))) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.2 this, map_zero, map_zero]
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

/-- **Step C2(d)** for split reductive data on a lattice: the only remaining hypothesis is the
tangent identity `htan` at the base points `(e, e, τ)` (`μ` built with `sliceMap' π D N ψ`). -/
theorem exists_open_regularConjugates_lattice (N : Magnet (Additive X))
    (htan : ∀ ψ : X →* Multiplicative ℤ, (∀ α ∈ roots π, α ∈ N → pairingHom ψ α ≠ 0) →
      ∀ τ : MonoidAlgebra k X →ₐ[k] k,
        (∀ α ∈ roots π, α ∈ N → τ (MonoidAlgebra.single (Additive.toMul α) 1) ≠ 1) →
          SliceTangentBijective π N ψ (compIdeal_le_ker_torus π D N) (sliceBasePt π N ψ τ)) :
    ∃ U : Set (compSubgroup π N), IsOpen U ∧ U.Nonempty ∧
      ∀ x ∈ U, ∃ g ∈ compSubgroup π N, ∃ t ∈ regularPoints π N,
        (x : WithConv (H →ₐ[k] k)) = g * t * g⁻¹ := by
  haveI : Module.Finite ℤ (Additive X) :=
    Module.Finite.iff_addGroup_fg.2 (AddGroup.fg_iff_addMonoid_fg.2
      (Monoid.fg_iff_add_fg.1 inferInstance))
  haveI : Module.Free ℤ (Additive X) := Module.free_of_finite_type_torsion_free'
  obtain ⟨ψ, hψ⟩ := exists_generic_cocharacter {α | α ∈ roots π ∧ α ∈ N}
    ((finite_roots (π := π)).subset fun _ h => h.1)
    (fun α h e => h.1.1 (by rw [e]; rfl))
  exact exists_open_regularConjugates π N ψ (compIdeal_le_ker_torus π D N)
    (fun α hα hN => hψ α ⟨hα, hN⟩) (SliceSmooth.smooth_sliceSource π N ψ) (htan ψ fun α hα hN => hψ α ⟨hα, hN⟩)

/-- `RegularConjugatesOpen` (the C2(d) hypothesis of the glue), given the tangent identity. -/
theorem regularConjugatesOpen_lattice
    (htan : ∀ N : Magnet (Additive X), ∀ ψ : X →* Multiplicative ℤ,
      (∀ α ∈ roots π, α ∈ N → pairingHom ψ α ≠ 0) → ∀ τ : MonoidAlgebra k X →ₐ[k] k,
        (∀ α ∈ roots π, α ∈ N → τ (MonoidAlgebra.single (Additive.toMul α) 1) ≠ 1) →
          SliceTangentBijective π N ψ (compIdeal_le_ker_torus π D N) (sliceBasePt π N ψ τ)) :
    ∀ N : Magnet (Additive X), ∃ U : Set (compSubgroup π N), IsOpen U ∧ U.Nonempty ∧
      ∀ x ∈ U, ∃ g ∈ compSubgroup π N, ∃ t ∈ regularPoints π N,
        (x : WithConv (H →ₐ[k] k)) = g * t * g⁻¹ :=
  fun N => exists_open_regularConjugates_lattice π D N (htan N)

end Lattice

end AlgMag.Reductive
