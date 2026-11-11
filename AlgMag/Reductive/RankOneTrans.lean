/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.RankOneStructure
import AlgMag.Reductive.RayGa
import AlgMag.Reductive.RegularCentralizer
import AlgMag.Reductive.ParabolicGenRay
import AlgMag.Reductive.R1Discharge
import AlgMag.Reductive.BorBase
import AlgMag.Reductive.ParabolicGenStep
import AlgMag.Reductive.BorWallStep

/-!
# `T`-transitivity on `U_Z(λ⁻¹)(k) ∖ 1` from `rayDim ≤ 1`, hence `BorelZMax` from T2

`Z = G^{ℤδ}`, `λ = λ_ψ` with `⟨ψ, δ⟩ ≠ 0`.

* `mem_rayPoints_of_unipotent`: `U_G(λ_φ)(k) ∩ G^N(k) ⊆ U_(α)(k)` when `N ∩ {⟨φ,·⟩ ≥ 0} ⊆ ℕα`.
  Its inputs are the parabolic as a magnet attractor (`magnetIdeal_torusGrading_comap_nat`) and
  the limit on `H_0` (`limit_eq_one_iff_coeff_conjugationAlgHom`).
* So `v ↦ v ∘ zMk` maps `U_Z(λ⁻¹)(k)` injectively into `U_(α₀)(k)`, where `α₀ = ±δ` is the
  generator of the `ψ⁻¹`-positive half of `ℤδ` (`BialgHom.mapDomain_mem_unipotent`).
* `rayDim ≤ 1` (the output of `hBruhat` in the final assembly) and RayGa `hGa_of_rayDim` give:
  either `U_(α₀)(k) = 1`, or `k[U_(α₀)] = k[ȳ]` with `y ∈ H_γ`, `⟨ψ⁻¹, γ⟩ ≠ 0`.
  - `e(v) = v(zMk y)` is then an injective coordinate (`eq_of_coord_eq`).
  - The point `λ_ψ(c)` acts on it by `c^{⟨ψ,γ⟩}` (`conj_torusPt_apply`), which runs over `kˣ`.
  - This gives `UTrans` (`uTrans_zCochar_of_rayDim`).
* `borelZMax_of_rayDim`: `BorelZMax π δ ψ` from T2 and `rayDim ≤ 1`.
-/

suppress_compilation

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Magnetism TauCeti TauCeti.Cocharacter WithConv AlgMag.Weyl
open scoped TensorProduct

universe u

namespace AlgMag.Reductive.RankOneStructure

open AlgMag.Reductive R1Build R1Dis

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)

/-- **`U_G(λ_φ)(k) ∩ G^N(k) ⊆ U_(α)(k)`** when every `χ ∈ N` with `⟨φ, χ⟩ ≥ 0` lies in `ℕα`. -/
theorem mem_rayPoints_of_unipotent (φ : X →* Multiplicative ℤ) (α : PosRay φ)
    (N : Magnet (Additive X)) (hN : ∀ χ ∈ N, 0 ≤ pairingHom φ χ → χ ∈ rayMagnet α.1)
    {g : WithConv (H →ₐ[k] k)} (hgN : magnetIdeal (torusGrading π) N ≤ RingHom.ker g.ofConv)
    (hgU : g ∈ unipotent k (π.cocharacter φ)) : g ∈ rayPoints π φ α := by
  obtain ⟨hgP, hlim⟩ := mem_unipotent_iff.mp hgU
  have hP := (magnetIdeal_torusGrading_comap_nat_le_ker_iff (π := π) (ψ := φ) g).2 hgP
  show (rootGroupIdeal π α.1 (PosRay.torsionFree φ α)).toIdeal ≤ RingHom.ker g.ofConv
  rw [rootGroupIdeal, prescribedUnitHopfIdeal_toIdeal, prescribedUnitIdeal, sup_le_iff]
  constructor
  · rw [magnetIdeal, Ideal.span_le]
    simp only [Set.iUnion_subset_iff]
    intro χ hχ a ha
    by_cases hχN : χ ∈ N
    · have hneg : ¬ 0 ≤ pairingHom φ χ := fun h => hχ (hN χ hχN h)
      apply hP
      rw [magnetIdeal]
      refine Ideal.subset_span (Set.mem_iUnion₂.2 ⟨χ, fun h => hneg ?_, ha⟩)
      change pairingHom φ χ ∈ natMagnet at h
      rwa [mem_natMagnet] at h
    · apply hgN
      rw [magnetIdeal]
      exact Ideal.subset_span (Set.mem_iUnion₂.2 ⟨χ, hχN, ha⟩)
  · rw [Ideal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have h1 : g.ofConv ((conjugationAlgHom (π.cocharacter φ) x).coeff 0 -
        algebraMap k H (Coalgebra.counit x)) = 0 := by
      first
      | exact (BialgHom.limit_eq_one_iff_coeff_conjugationAlgHom _ ⟨g, hgP⟩).1 hlim x
      | exact (limit_eq_one_iff_coeff_conjugationAlgHom _ ⟨g, hgP⟩).1 hlim x
    have hx' : x ∈ lineGrading (π.cocharacter φ) 0 := by
      have := torusGrading_le_lineGrading (π := π) (ψ := φ) 0 hx
      simpa using this
    rw [coeff_of_mem_lineGrading hx', if_pos rfl] at h1
    exact h1

omit [CommGroup X] [DecidableEq X] in
/-- **A point of `V(I)` is determined by its value on `y`** when `H ⧸ I = k[ȳ]`. -/
theorem eq_of_coord_eq {I : Ideal H} {y : H}
    (hbij : Function.Bijective (Polynomial.aeval (R := k) (Ideal.Quotient.mk I y)))
    {g g' : WithConv (H →ₐ[k] k)} (hg : I ≤ RingHom.ker g.ofConv)
    (hg' : I ≤ RingHom.ker g'.ofConv) (h : g.ofConv y = g'.ofConv y) : g = g' := by
  apply WithConv.ofConv_injective
  ext a
  obtain ⟨p, hp⟩ := hbij.2 (Ideal.Quotient.mk I a)
  have hd : a - Polynomial.aeval y p ∈ I := by
    rw [← Ideal.Quotient.eq, ← hp, ← Ideal.Quotient.mkₐ_eq_mk k]
    exact Polynomial.aeval_algHom_apply _ _ _
  have e : ∀ f : WithConv (H →ₐ[k] k), I ≤ RingHom.ker f.ofConv →
      f.ofConv a = Polynomial.aeval (f.ofConv y) p := by
    intro f hf
    have := hf hd
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this
    rw [this, Polynomial.aeval_algHom_apply]
  rw [e g hg, e g' hg', h]

omit [DecidableEq X] in
/-- `χ = mδ` with `⟨f, χ⟩ ≥ 0` lies in `ℕα₀` for `α₀ = ±δ` with `⟨f, α₀⟩ > 0`. -/
theorem mem_rayMagnet_of_pairing {f : Additive X →+ ℤ} {δ α₀ χ : Additive X}
    (hα₀ : α₀ = δ ∨ α₀ = -δ) (hpos : 0 < f α₀) (hχ : χ ∈ lineMagnet δ) (hnn : 0 ≤ f χ) :
    χ ∈ rayMagnet α₀ := by
  obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 (mem_lineMagnet.1 hχ)
  rw [rayMagnet, AddSubmonoid.mem_closure_singleton]
  rw [map_zsmul, smul_eq_mul] at hnn
  rcases hα₀ with rfl | rfl
  · have hm : 0 ≤ m := by
      by_contra hm
      push_neg at hm
      nlinarith
    exact ⟨m.toNat, by rw [← natCast_zsmul, Int.toNat_of_nonneg hm]⟩
  · rw [map_neg] at hpos
    have hm : m ≤ 0 := by
      by_contra hm
      push_neg at hm
      nlinarith
    refine ⟨(-m).toNat, ?_⟩
    rw [← natCast_zsmul, Int.toNat_of_nonneg (by omega), smul_neg, neg_smul, neg_neg]

omit [DecidableEq X] in
theorem mapDomain_ofConv {K : Type u} [CommRing K] [HopfAlgebra k K] (φ : H →ₐc[k] K)
    (g : WithConv (K →ₐ[k] k)) (x : H) :
    (BialgHom.mapDomain φ g).ofConv x = g.ofConv (φ x) := by
  first
  | rfl
  | simp [BialgHom.mapDomain_apply_apply]
  | simp [BialgHom.mapDomain_apply]

section AlgClosed

variable [IsAlgClosed k]

theorem zCochar_opp (δ : Additive X) (ψ : X →* Multiplicative ℤ) :
    (zCochar π δ ψ).oppositeCocharacter = zCochar π δ ψ⁻¹ := by
  unfold zCochar; rw [cocharacter_inv]

omit [CommGroup X] [DecidableEq X] in
/-- `a ↦ a^d` maps `kˣ` onto `kˣ` for `d ≠ 0`. -/
theorem exists_zpow_eq {d : ℤ} (hd : d ≠ 0) {c : k} (hc : c ≠ 0) :
    ∃ a : k, a ≠ 0 ∧ a ^ d = c := by
  rcases lt_or_gt_of_ne hd with h | h
  · obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq c⁻¹ (show 0 < d.natAbs by omega)
    have ha0 : a ≠ 0 := by
      rintro rfl; rw [zero_pow (by omega)] at ha; exact inv_ne_zero hc ha.symm
    refine ⟨a, ha0, ?_⟩
    have : d = -(d.natAbs : ℤ) := by omega
    rw [this, zpow_neg, zpow_natCast, ha, inv_inv]
  · obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq c (show 0 < d.natAbs by omega)
    have ha0 : a ≠ 0 := by
      rintro rfl; rw [zero_pow (by omega)] at ha; exact hc ha.symm
    refine ⟨a, ha0, ?_⟩
    have : d = (d.natAbs : ℤ) := by omega
    rw [this, zpow_natCast, ha]

omit [IsAlgClosed k] [DecidableEq X] in
/-- The point `λ_ψ(a)` of the torus: `χ ↦ a^{⟨ψ, χ⟩}`. -/
def cocharPt (ψ : X →* Multiplicative ℤ) {a : k} (ha : a ≠ 0) : MonoidAlgebra k X →ₐ[k] k :=
  MonoidAlgebra.lift k k X ((Units.coeHom k).comp ((zpowersHom kˣ (Units.mk0 a ha)).comp ψ))

omit [IsAlgClosed k] [DecidableEq X] in
theorem cocharPt_single (ψ : X →* Multiplicative ℤ) {a : k} (ha : a ≠ 0) (χ : Additive X) :
    cocharPt ψ ha (MonoidAlgebra.single (Additive.toMul χ) 1) = a ^ pairingHom ψ χ := by
  simp [cocharPt, MonoidAlgebra.lift_single, pairingHom_apply]

local instance zDecRT (α : Additive X) : DecidableEq (ZAlg π α) := Classical.decEq _

/-- **`T`-transitivity on `U_Z(λ_ψ⁻¹)(k) ∖ 1` from `rayDim ≤ 1`.** The conjugating element is the
torus point `λ_ψ(c)`. -/
theorem uTrans_zCochar_of_rayDim [Algebra.FiniteType k H] [Algebra.Smooth k H]
    (δ : Additive X) (ψ : X →* Multiplicative ℤ) (hψδ : pairingHom ψ δ ≠ 0)
    (hray : ∀ (φ : X →* Multiplicative ℤ) (α : Additive X), 0 < pairingHom φ α →
      rayDim π (pairingHom φ) α ≤ 1) :
    UTrans (zCochar π δ ψ) := by
  classical
  obtain ⟨α₀, hα₀δ, hα₀pos⟩ : ∃ α₀ : Additive X, (α₀ = δ ∨ α₀ = -δ) ∧
      0 < pairingHom ψ⁻¹ α₀ := by
    rcases lt_or_gt_of_ne hψδ with h | h
    · exact ⟨δ, Or.inl rfl, by rw [borPairingHom_inv]; omega⟩
    · exact ⟨-δ, Or.inr rfl, by rw [borPairingHom_inv, map_neg]; omega⟩
  let A : PosRay ψ⁻¹ := ⟨α₀, hα₀pos⟩
  have hs := zMk_surjective π δ
  have hPv : ∀ {φ' : X →* Multiplicative ℤ} {w : WithConv (ZAlg π δ →ₐ[k] k)},
      w ∈ parabolic k (zCochar π δ φ') →
      ∀ y ∈ magnetIdeal (torusGrading π) (natMagnet.comap (pairingHom φ')),
        w.ofConv (zMk π δ y) = 0 := by
    intro φ' w hw y hy
    rw [← quotientPointsSubgroup_parabolicDefiningHopfIdeal (A := k),
      CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hw
    apply hw
    rw [← HopfIdeal.mem_toIdeal, parabolic_toIdeal_eq_map (zMk π δ) hs _ _ (zCochar_comp π δ φ'),
      ← magnetIdeal_torusGrading_comap_nat]
    exact Ideal.mem_map_of_mem _ hy
  have hPmem : ∀ {φ' : X →* Multiplicative ℤ} {w : WithConv (ZAlg π δ →ₐ[k] k)},
      (∀ y ∈ magnetIdeal (torusGrading π) (natMagnet.comap (pairingHom φ')),
        w.ofConv (zMk π δ y) = 0) → w ∈ parabolic k (zCochar π δ φ') := by
    intro φ' w hw
    rw [← quotientPointsSubgroup_parabolicDefiningHopfIdeal (A := k),
      CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    intro h hh
    rw [← HopfIdeal.mem_toIdeal, parabolic_toIdeal_eq_map (zMk π δ) hs _ _ (zCochar_comp π δ φ'),
      ← magnetIdeal_torusGrading_comap_nat] at hh
    have hle : Ideal.map (zMk π δ : H →ₐ[k] ZAlg π δ)
        (magnetIdeal (torusGrading π) (natMagnet.comap (pairingHom φ'))) ≤
          RingHom.ker w.ofConv := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      exact Ideal.mem_comap.2 (RingHom.mem_ker.2 (hw y hy))
    exact hle hh
  have hinjZ : ∀ w w' : WithConv (ZAlg π δ →ₐ[k] k),
      BialgHom.mapDomain (zMk π δ) w = BialgHom.mapDomain (zMk π δ) w' → w = w' := by
    intro w w' h
    apply WithConv.ofConv_injective
    ext z
    obtain ⟨x, rfl⟩ := hs z
    have := congrArg (fun f : WithConv (H →ₐ[k] k) => f.ofConv x) h
    simpa only [mapDomain_ofConv] using this
  have hmapU : ∀ v ∈ unipotent k (zCochar π δ ψ).oppositeCocharacter,
      BialgHom.mapDomain (zMk π δ) v ∈ rayPoints π ψ⁻¹ A := by
    intro v hv
    rw [zCochar_opp] at hv
    obtain ⟨hvP, hlim⟩ := mem_unipotent_iff.mp hv
    show (rootGroupIdeal π α₀ (PosRay.torsionFree ψ⁻¹ A)).toIdeal ≤
      RingHom.ker (BialgHom.mapDomain (zMk π δ) v).ofConv
    rw [rootGroupIdeal, prescribedUnitHopfIdeal_toIdeal, prescribedUnitIdeal, sup_le_iff]
    constructor
    · rw [magnetIdeal, Ideal.span_le]
      simp only [Set.iUnion_subset_iff]
      intro χ hχ a ha
      rw [SetLike.mem_coe, RingHom.mem_ker, mapDomain_ofConv]
      by_cases hχN : χ ∈ lineMagnet δ
      · have hneg : ¬ 0 ≤ pairingHom ψ⁻¹ χ := fun h =>
          hχ (mem_rayMagnet_of_pairing hα₀δ hα₀pos hχN h)
        refine hPv hvP a ?_
        rw [magnetIdeal]
        refine Ideal.subset_span (Set.mem_iUnion₂.2 ⟨χ, fun h => hneg ?_, ha⟩)
        change pairingHom ψ⁻¹ χ ∈ natMagnet at h
        rwa [mem_natMagnet] at h
      · rw [zMk_eq_zero π δ (by
          rw [magnetIdeal]; exact Ideal.subset_span (Set.mem_iUnion₂.2 ⟨χ, hχN, ha⟩)), map_zero]
    · rw [Ideal.span_le]
      rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, mapDomain_ofConv]
      have h1 : v.ofConv ((conjugationAlgHom (zCochar π δ ψ⁻¹) (zMk π δ x)).coeff 0 -
          algebraMap k (ZAlg π δ) (Coalgebra.counit (zMk π δ x))) = 0 := by
        first
        | exact (BialgHom.limit_eq_one_iff_coeff_conjugationAlgHom _ ⟨v, hvP⟩).1 hlim _
        | exact (limit_eq_one_iff_coeff_conjugationAlgHom _ ⟨v, hvP⟩).1 hlim _
      have hx' : x ∈ lineGrading (π.cocharacter ψ⁻¹) 0 := by
        have := torusGrading_le_lineGrading (π := π) (ψ := ψ⁻¹) 0 hx
        simpa using this
      rw [conjugationAlgHom_natural (π.cocharacter ψ⁻¹) (zMk π δ) (zCochar π δ ψ⁻¹)
          (zCochar_comp π δ ψ⁻¹) x, AddMonoidAlgebra.coeff_mapAlgHom,
        coeff_of_mem_lineGrading hx', if_pos rfl, CoalgHomClass.counit_comp_apply] at h1
      have e2 : (zMk π δ) (x - algebraMap k H (Coalgebra.counit x)) =
          zMk π δ x - algebraMap k (ZAlg π δ) (Coalgebra.counit x) := by
        rw [map_sub, AlgHomClass.commutes]
      rw [e2]
      exact h1
  rcases hGa_of_rayDim π ψ⁻¹ A (hray ψ⁻¹ α₀ hα₀pos) with htriv | ⟨γ, hγ, y, hy, hbij⟩
  · intro u hu v hv hu1 hv1
    exact absurd (hinjZ _ _ ((htriv _ (hmapU u hu)).trans (map_one _).symm)) hu1
  · intro u hu v hv hu1 hv1
    have hγ0 : γ ≠ 0 := by rintro rfl; exact hγ (map_zero _)
    set e : WithConv (ZAlg π δ →ₐ[k] k) → k := fun w => w.ofConv (zMk π δ y) with he
    have hinj : ∀ w ∈ unipotent k (zCochar π δ ψ).oppositeCocharacter,
        ∀ w' ∈ unipotent k (zCochar π δ ψ).oppositeCocharacter, e w = e w' → w = w' := by
      intro w hw w' hw' h
      refine hinjZ _ _ (eq_of_coord_eq hbij (hmapU w hw) (hmapU w' hw') ?_)
      rw [mapDomain_ofConv, mapDomain_ofConv]
      exact h
    have he1 : e 1 = 0 := by
      have : e 1 = (BialgHom.mapDomain (zMk π δ) 1).ofConv y := (mapDomain_ofConv _ _ _).symm
      rw [this, map_one, AlgHom.convOne_apply]
      exact counit_eq_zero_of_mem (π := π) hγ0 hy
    have heu : e u ≠ 0 := fun h => hu1 (hinj u hu 1 (one_mem _) (h.trans he1.symm))
    have hev : e v ≠ 0 := fun h => hv1 (hinj v hv 1 (one_mem _) (h.trans he1.symm))
    have hd : pairingHom ψ γ ≠ 0 := by
      intro h; apply hγ; rw [borPairingHom_inv, h, neg_zero]
    obtain ⟨c, hc0, hcd⟩ := exists_zpow_eq hd (div_ne_zero hev heu)
    set τ := cocharPt ψ hc0 with hτ
    set t : WithConv (ZAlg π δ →ₐ[k] k) := toConv (τ.comp (piZ π δ).toAlgHom) with ht
    have htilde : BialgHom.mapDomain (zMk π δ) t = toConv (τ.comp π.toAlgHom) := by
      apply WithConv.ofConv_injective
      ext x
      rw [mapDomain_ofConv]
      show τ ((piZ π δ) (zMk π δ x)) = τ (π x)
      rw [piZ_apply]
    have htZ : ∀ φ' : X →* Multiplicative ℤ, t ∈ parabolic k (zCochar π δ φ') := fun φ' =>
      hPmem fun y hy => by
        have := magnetIdeal_le_ker_torus π _ hy
        rw [RingHom.mem_ker] at this
        show τ ((piZ π δ) (zMk π δ y)) = 0
        rw [piZ_apply]
        exact (congrArg τ this).trans (map_zero τ)
    have htP' : t ∈ parabolic k (zCochar π δ ψ).oppositeCocharacter := by
      rw [zCochar_opp]; exact htZ ψ⁻¹
    have htu : t * u * t⁻¹ ∈ unipotent k (zCochar π δ ψ).oppositeCocharacter :=
      conj_mem_unipotent htP' hu
    refine ⟨t, htZ ψ, (hinj _ htu v hv ?_).symm⟩
    have hconj : e (t * u * t⁻¹) = τ (MonoidAlgebra.single (Additive.toMul γ) 1) * e u := by
      simp only [he]
      rw [← mapDomain_ofConv, map_mul, map_mul, map_inv, htilde, conj_torusPt_apply π τ _ hy,
        mapDomain_ofConv]
    rw [hconj, hτ, cocharPt_single, hcd, div_mul_cancel₀ _ heu]

/-- The same on the other side: `T`-transitivity on `U_Z(λ_ψ)(k) ∖ 1`. -/
theorem uTrans_zCochar_opp_of_rayDim [Algebra.FiniteType k H] [Algebra.Smooth k H]
    (δ : Additive X) (ψ : X →* Multiplicative ℤ) (hψδ : pairingHom ψ δ ≠ 0)
    (hray : ∀ (φ : X →* Multiplicative ℤ) (α : Additive X), 0 < pairingHom φ α →
      rayDim π (pairingHom φ) α ≤ 1) :
    UTrans (zCochar π δ ψ).oppositeCocharacter := by
  rw [zCochar_opp]
  exact uTrans_zCochar_of_rayDim π δ ψ⁻¹
    (by rw [borPairingHom_inv]; exact neg_ne_zero.2 hψδ) hray

local instance zSmoothRT [Algebra.FiniteType k H] [Algebra.Smooth k H] (α : Additive X) :
    Algebra.Smooth k (ZAlg π α) := smooth_quotient_magnetHopfIdeal π _

/-- **`BorelZMax` from T2 and `rayDim ≤ 1`** (the output of `hBruhat`), for `G` smooth connected
and `δ` a line generator. -/
theorem borelZMax_of_rayDim [Algebra.FiniteType k H] [Algebra.Smooth k H]
    [ConnectedSpace (PrimeSpectrum H)] [Module.Free ℤ (Additive X)]
    (δ : Additive X) (hδ0 : δ ≠ 0)
    (hRay : ∀ β ∈ roots π, (∃ m n : ℤ, n ≠ 0 ∧ n • β = m • δ) → β ∈ lineMagnet δ)
    (ψ : X →* Multiplicative ℤ) (hψδ : pairingHom ψ δ ≠ 0)
    (hns : ¬ Group.IsSolvable (WithConv (ZAlg π δ →ₐ[k] k)))
    (hray : ∀ (φ : X →* Multiplicative ℤ) (α : Additive X), 0 < pairingHom φ α →
      rayDim π (pairingHom φ) α ≤ 1) :
    BorelZMax π δ ψ :=
  borelZMax_of_trans π δ hδ0 hRay ψ hns (uTrans_zCochar_of_rayDim π δ ψ hψδ hray)
    (uTrans_zCochar_opp_of_rayDim π δ ψ hψδ hray)

end AlgClosed

end AlgMag.Reductive.RankOneStructure

#print axioms AlgMag.Reductive.RankOneStructure.mem_rayPoints_of_unipotent
#print axioms AlgMag.Reductive.RankOneStructure.uTrans_zCochar_of_rayDim
#print axioms AlgMag.Reductive.RankOneStructure.borelZMax_of_rayDim
