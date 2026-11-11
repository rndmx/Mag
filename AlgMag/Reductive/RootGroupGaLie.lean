/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.RootGroupGa
import AlgMag.Sec12PrintedRing

/-!
# `U_α ≅ 𝔾_a`: the coordinate (discharge of the `𝔾_a` field of `IsRootGroup`)

`O = O(U_α) = H/J_U` is graded by the weights, supported on `ℕα`, with `O_0 = k`
(`isAug_rootGroup`). Its cotangent space at `e` is dual to `Lie(U_α) = 𝔤_α`; with `dim 𝔤_α = 1` it
is a line spanned by the class of some `y ∈ H_α` (`exists_generator`). The printed proof of
Theorem 12.4 (graded Nakayama, `Sec12Printed.phi_surjective`) gives `k[ȳ] ↠ O`; injectivity from
the grading and the reducedness of `O` (`isReduced_quotient_prescribedUnit`, BB for faces). The
grading of the comultiplication (`comul_mem_tensorGrading`) and the counit give
`Δȳ = ȳ ⊗ 1 + 1 ⊗ ȳ`.

Main result: `isRootGroup_rootGroupIdeal_of_finrank`, hypotheses `hα` (`α` of infinite order),
`hred` (`nα ∉ Φ`, `n ≥ 2`), `G` smooth, `dim 𝔤_α = 1`.
-/

suppress_compilation

open Magnetism TauCeti WithConv AlgMag.Sec12Printed
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable {π : H →ₐc[k] MonoidAlgebra k X} {α : Additive X}

variable (π α) in
/-- `J_U`, the ideal of `U_α = G^{[α⟩}_e`. -/
abbrev JU : Ideal H := prescribedUnitIdeal π (rayMagnet α)

lemma JU_le_ker_counit : JU π α ≤ RingHom.ker (Bialgebra.counitAlgHom k H) := by
  rw [JU, prescribedUnitIdeal, sup_le_iff, magnetIdeal, Ideal.span_le, Ideal.span_le]
  constructor
  · simp only [Set.iUnion_subset_iff]
    intro χ hχ y hy
    rw [SetLike.mem_coe, RingHom.mem_ker]
    exact counit_eq_zero_of_mem (by rintro rfl; exact hχ (rayMagnet α).zero_mem) hy
  · rintro _ ⟨x, -, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    change Coalgebra.counit (R := k) (x - algebraMap k H (Coalgebra.counit (R := k) x)) = 0
    rw [map_sub, Bialgebra.counit_algebraMap, sub_self]

variable (π α) in
/-- The counit of `O(U_α)`. -/
def counitO : (H ⧸ JU π α) →ₐ[k] k :=
  Ideal.Quotient.liftₐ _ (Bialgebra.counitAlgHom k H) fun _ hx => JU_le_ker_counit hx

lemma counitO_mk (h : H) : counitO π α (Ideal.Quotient.mk _ h) = Coalgebra.counit (R := k) h :=
  rfl

/-! ### The grading of `O(U_α)` -/

variable (π α) in
/-- The weight grading of `O(U_α)`. -/
abbrev gradO : Additive X → Submodule k (H ⧸ JU π α) := quotGrading (torusGrading π) (JU π α)

lemma isHomogeneousIdeal_JU (hα : ∀ n : ℕ, n • α = 0 → n = 0) :
    IsHomogeneousIdeal (torusGrading π) (JU π α) := by
  have h := isHomogeneous_rootGroupIdeal (π := π) α hα
  rw [rootGroupIdeal, prescribedUnitHopfIdeal_toIdeal] at h
  exact fun a ha m => h m ha

lemma mk_mem_gradO {χ : Additive X} {x : H} (hx : x ∈ torusGrading π χ) :
    Ideal.Quotient.mk (JU π α) x ∈ gradO π α χ := ⟨x, hx, rfl⟩

lemma eq_zero_of_mem_gradO {χ : Additive X} (hχ : χ ∉ rayMagnet α) {b : H ⧸ JU π α}
    (hb : b ∈ gradO π α χ) : b = 0 := by
  obtain ⟨x, hx, rfl⟩ := hb
  exact Ideal.Quotient.eq_zero_iff_mem.2 (le_sup_left (a := magnetIdeal (torusGrading π) _)
    (mem_magnetIdeal_of_notMem hχ hx))

lemma eq_algebraMap_of_mem_gradO_zero {b : H ⧸ JU π α} (hb : b ∈ gradO π α 0) :
    b = algebraMap k _ (counitO π α b) := by
  obtain ⟨x, hx, rfl⟩ := hb
  change Ideal.Quotient.mk _ x = algebraMap k _ (counitO π α (Ideal.Quotient.mk _ x))
  rw [counitO_mk, ← Ideal.Quotient.mkₐ_eq_mk k, ← AlgHom.commutes (Ideal.Quotient.mkₐ k (JU π α)),
    Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq]
  exact le_sup_right (a := magnetIdeal (torusGrading π) _) (Ideal.subset_span ⟨x, hx, rfl⟩)

lemma counitO_eq_zero_of_mem {χ : Additive X} (hχ : χ ≠ 0) {b : H ⧸ JU π α}
    (hb : b ∈ gradO π α χ) : counitO π α b = 0 := by
  obtain ⟨x, hx, rfl⟩ := hb
  change counitO π α (Ideal.Quotient.mk _ x) = 0
  rw [counitO_mk]
  exact counit_eq_zero_of_mem hχ hx

section Weight

variable (hα : ∀ n : ℕ, n • α = 0 → n = 0)
include hα

lemma nsmul_injective_of : Function.Injective (fun n : ℕ => n • α) := by
  intro m n h
  simp only at h
  rcases le_total m n with hmn | hmn
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    have h' : d • α = 0 := by simpa [add_smul] using h
    simp [hα d h']
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    have h' : d • α = 0 := by simpa [add_smul] using h
    simp [hα d h']

end Weight

open Classical in
variable (α) in
/-- The weight `w(nα) = n`. -/
noncomputable def wt (y : Additive X) : ℕ := if h : ∃ n : ℕ, n • α = y then Nat.find h else 0

lemma wt_nsmul (hα : ∀ n : ℕ, n • α = 0 → n = 0) (n : ℕ) : wt α (n • α) = n := by
  classical
  have h : ∃ m : ℕ, m • α = n • α := ⟨n, rfl⟩
  rw [wt, dif_pos h]
  exact nsmul_injective_of hα (Nat.find_spec h)

lemma isAug_rootGroup (hα : ∀ n : ℕ, n • α = 0 → n = 0) :
    letI := quotGradedAlgebra (isHomogeneousIdeal_JU (π := π) hα)
    IsAug (gradO π α) (counitO π α) (wt α) := by
  letI := quotGradedAlgebra (isHomogeneousIdeal_JU (π := π) hα)
  refine ⟨fun y b hb hb0 hw => ?_, fun u b hb hb0 v d hd hd0 => ?_, fun y hy b hb => ?_,
    fun b hb => ?_⟩
  · by_cases hy : y ∈ rayMagnet α
    · obtain ⟨n, rfl⟩ := AddSubmonoid.mem_closure_singleton.1 hy
      rw [wt_nsmul hα] at hw
      simp [hw]
    · exact absurd (eq_zero_of_mem_gradO hy hb) hb0
  · by_cases hu : u ∈ rayMagnet α
    · by_cases hv : v ∈ rayMagnet α
      · obtain ⟨m, rfl⟩ := AddSubmonoid.mem_closure_singleton.1 hu
        obtain ⟨n, rfl⟩ := AddSubmonoid.mem_closure_singleton.1 hv
        rw [← add_smul, wt_nsmul hα, wt_nsmul hα, wt_nsmul hα]
      · exact absurd (eq_zero_of_mem_gradO hv hd) hd0
    · exact absurd (eq_zero_of_mem_gradO hu hb) hb0
  · exact counitO_eq_zero_of_mem hy hb
  · exact (eq_algebraMap_of_mem_gradO_zero hb).symm

/-! ### The cotangent space of `U_α` -/

variable (π α) in
/-- `Lie(G)_α`: tangent vectors at `e` vanishing on every `H_χ`, `χ ≠ α`. -/
def rootSpace : Submodule k (Derivation k H (Bialgebra.CounitAlgebra k H k)) where
  carrier := {d | ∀ χ ≠ α, ∀ h ∈ torusGrading π χ, d h = 0}
  add_mem' {d d'} hd hd' χ hχ h hh := by
    rw [Derivation.add_apply, hd χ hχ h hh, hd' χ hχ h hh, add_zero]
  zero_mem' _ _ _ _ := rfl
  smul_mem' c d hd χ hχ h hh := by
    rw [Derivation.smul_apply, hd χ hχ h hh]
    exact smul_zero c

variable (π α) in
/-- The cotangent space `m/m²` of `U_α` at `e`. -/
abbrev CotU := Conormal (counitO π α)

variable (π α) in
/-- `Cot_e(G) → Cot_e(U_α)`. -/
def cotRestrict : Bialgebra.CotangentSpace k H →ₗ[k] CotU π α :=
  Ideal.mapCotangent (Bialgebra.AugmentationIdeal k H) (augI (counitO π α))
    (Ideal.Quotient.mkₐ k (JU π α)) (fun x hx => by
      rw [Ideal.mem_comap, RingHom.mem_ker]
      exact hx)

lemma cotRestrict_cotangentMap (h : H) :
    cotRestrict π α (Bialgebra.cotangentMap k H h) = tMap (counitO π α) (Ideal.Quotient.mk _ h) := by
  rw [Bialgebra.cotangentMap_apply, cotRestrict, Ideal.mapCotangent_toCotangent]
  refine congrArg (augI (counitO π α)).toCotangent (Subtype.ext ?_)
  simp only [Ideal.Quotient.mkₐ_eq_mk, map_sub, counitO_mk]
  rfl

lemma cotRestrict_surjective : Function.Surjective (cotRestrict π α) := by
  intro c
  obtain ⟨b, rfl⟩ := tMap_surjective (counitO π α) c
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact ⟨_, cotRestrict_cotangentMap h⟩

variable (π α) in
/-- `Cot_e(U_α)^* → Der_e(H)`, `f ↦ (h ↦ f(t(h̄)))`. -/
def dualToDer : Module.Dual k (CotU π α) →ₗ[k] Derivation k H (Bialgebra.CounitAlgebra k H k) :=
  (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k)).toLinearMap ∘ₗ
    (cotRestrict π α).dualMap

lemma dualToDer_apply (f : Module.Dual k (CotU π α)) (h : H) :
    Bialgebra.CounitAlgebra.algEquivSelf k H k (dualToDer π α f h) =
      f (tMap (counitO π α) (Ideal.Quotient.mk _ h)) := by
  rw [dualToDer, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Derivation.algEquivSelf_cotangentLinearEquiv_apply, LinearMap.dualMap_apply,
    cotRestrict_cotangentMap]

lemma dualToDer_injective : Function.Injective (dualToDer π α) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  ext c
  obtain ⟨b, rfl⟩ := tMap_surjective (counitO π α) c
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← dualToDer_apply, hf]
  rfl

lemma dualToDer_mem_lie (hα : ∀ n : ℕ, n • α = 0 → n = 0) (f : Module.Dual k (CotU π α)) :
    dualToDer π α f ∈ (rootGroupIdeal π α hα).lieSubalgebra (B := k) := by
  rw [HopfIdeal.mem_lieSubalgebra_iff]
  intro x hx
  rw [rootGroupIdeal, prescribedUnitHopfIdeal_toIdeal] at hx
  apply (Bialgebra.CounitAlgebra.algEquivSelf k H k).injective
  rw [dualToDer_apply, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero, map_zero, map_zero]

variable [Module.Finite k (Bialgebra.CotangentSpace k H)]

lemma dualToDer_mem_rootSpace (hα : ∀ n : ℕ, n • α = 0 → n = 0)
    (hred : ∀ n : ℕ, 2 ≤ n → n • α ∉ roots π) (f : Module.Dual k (CotU π α)) :
    dualToDer π α f ∈ rootSpace π α :=
  (mem_lieSubalgebra_rootGroupIdeal_iff α hα hred _).1 (dualToDer_mem_lie hα f)

/-- Cotangent vectors of `U_α` have weight `α`. -/
lemma tMap_mk_eq_zero (hα : ∀ n : ℕ, n • α = 0 → n = 0)
    (hred : ∀ n : ℕ, 2 ≤ n → n • α ∉ roots π) {χ : Additive X} (hχ : χ ≠ α) {x : H}
    (hx : x ∈ torusGrading π χ) : tMap (counitO π α) (Ideal.Quotient.mk _ x) = 0 := by
  refine (Module.forall_dual_apply_eq_zero_iff k _).1 fun f => ?_
  rw [← dualToDer_apply, dualToDer_mem_rootSpace hα hred f χ hχ x hx]
  rfl

instance : Module.Finite k (CotU π α) :=
  Module.Finite.of_surjective _ (cotRestrict_surjective (π := π) (α := α))

/-- `dim Cot_e(U_α) ≤ dim 𝔤_α`. -/
lemma finrank_cotU_le (hα : ∀ n : ℕ, n • α = 0 → n = 0)
    (hred : ∀ n : ℕ, 2 ≤ n → n • α ∉ roots π) (hdim : Module.finrank k (rootSpace π α) = 1) :
    Module.finrank k (CotU π α) ≤ 1 := by
  haveI : Module.Finite k (rootSpace π α) := Module.finite_of_finrank_eq_succ hdim
  rw [← Subspace.dual_finrank_eq, ← hdim]
  exact LinearMap.finrank_le_finrank_of_injective
    (f := (dualToDer π α).codRestrict _ (dualToDer_mem_rootSpace hα hred))
    (fun f g h => dualToDer_injective (congrArg Subtype.val h))

/-- A tangent vector of `G` killing `J_U` and vanishing on the cotangent space of `U_α`
vanishes. -/
lemma der_eq_zero_of_subsingleton [Subsingleton (CotU π α)]
    (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) (hd : ∀ x ∈ JU π α, d x = 0) : d = 0 := by
  set g := (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k)).symm d
  have hm : ∀ x : Bialgebra.AugmentationIdeal k H, d x = 0 := by
    intro x
    have hmk : (Ideal.Quotient.mk (JU π α) (x : H)) ∈ augI (counitO π α) := by
      rw [RingHom.mem_ker]; exact x.2
    have h0 : (augI (counitO π α)).toCotangent ⟨_, hmk⟩ = 0 := Subsingleton.elim _ _
    rw [Ideal.toCotangent_eq_zero] at h0
    have hle : augI (counitO π α) ≤ (Bialgebra.AugmentationIdeal k H).map (Ideal.Quotient.mk _) := by
      intro b hb
      obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective b
      exact Ideal.mem_map_of_mem _ hb
    have h1 := Ideal.pow_right_mono hle 2 h0
    rw [← Ideal.map_pow, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at h1
    obtain ⟨z, hz, hzx⟩ := h1
    have hxz : (x : H) - z ∈ JU π α := by
      rw [← Ideal.Quotient.eq]; exact hzx.symm
    have hdz : d z = 0 := by
      have hzm : z ∈ Bialgebra.AugmentationIdeal k H :=
        Ideal.pow_le_self (by norm_num) hz
      have := Derivation.cotangentLinearEquiv_symm_toCotangent (R := k) (A := H) (B := k) d ⟨z, hzm⟩
      rw [(Ideal.toCotangent_eq_zero _ _).2 hz, map_zero] at this
      exact (Bialgebra.CounitAlgebra.algEquivSelf k H k).injective (by rw [← this]; rfl)
    have := hd _ hxz
    rw [map_sub, hdz, sub_zero] at this
    exact this
  ext h
  have : h = (h - algebraMap k H (Coalgebra.counit (R := k) h)) +
      algebraMap k H (Coalgebra.counit (R := k) h) := by ring
  rw [this, map_add, d.map_algebraMap, add_zero]
  exact hm ⟨_, by simp [Bialgebra.AugmentationIdeal]⟩

/-- **`dim Cot_e(U_α) = 1`**, from `dim 𝔤_α = 1`. -/
theorem finrank_cotU (hα : ∀ n : ℕ, n • α = 0 → n = 0)
    (hred : ∀ n : ℕ, 2 ≤ n → n • α ∉ roots π) (hdim : Module.finrank k (rootSpace π α) = 1) :
    Module.finrank k (CotU π α) = 1 := by
  refine le_antisymm (finrank_cotU_le hα hred hdim) (Nat.one_le_iff_ne_zero.2 fun h0 => ?_)
  haveI : Subsingleton (CotU π α) := Module.finrank_zero_iff.1 h0
  haveI := Module.nontrivial_of_finrank_eq_succ hdim
  obtain ⟨⟨d, hdr⟩, hd0⟩ := exists_ne (0 : rootSpace π α)
  apply hd0
  have hl : d ∈ (rootGroupIdeal π α hα).lieSubalgebra (B := k) :=
    (mem_lieSubalgebra_rootGroupIdeal_iff α hα hred d).2 hdr
  rw [HopfIdeal.mem_lieSubalgebra_iff, rootGroupIdeal, prescribedUnitHopfIdeal_toIdeal] at hl
  exact Subtype.ext (der_eq_zero_of_subsingleton d hl)



lemma decompose_aeval (hα : ∀ n : ℕ, n • α = 0 → n = 0) {yb : H ⧸ JU π α}
    (hyb : yb ∈ gradO π α α) (P : Polynomial k) (m : ℕ) :
    letI := quotGradedAlgebra (isHomogeneousIdeal_JU (π := π) hα)
    (DirectSum.decompose (gradO π α) (Polynomial.aeval yb P) (m • α) : H ⧸ JU π α) =
      P.coeff m • yb ^ m := by
  letI := quotGradedAlgebra (isHomogeneousIdeal_JU (π := π) hα)
  rw [Polynomial.aeval_eq_sum_range, DirectSum.decompose_sum, DFinsupp.finset_sum_apply,
    AddSubmonoidClass.coe_finset_sum]
  have hmem : ∀ n, P.coeff n • yb ^ n ∈ gradO π α (n • α) := fun n =>
    Submodule.smul_mem _ _ (SetLike.pow_mem_graded n hyb)
  rw [Finset.sum_eq_single m]
  · exact DirectSum.decompose_of_mem_same _ (hmem m)
  · intro n _ hnm
    exact DirectSum.decompose_of_mem_ne _ (hmem n) (fun h => hnm (nsmul_injective_of hα h))
  · intro hm
    rw [Finset.mem_range, not_lt] at hm
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_smul]
    exact DirectSum.decompose_of_mem_same _ (Submodule.zero_mem _)

/-! ### The coordinate `ȳ` -/

section Coordinate

variable (hα : ∀ n : ℕ, n • α = 0 → n = 0) (hred : ∀ n : ℕ, 2 ≤ n → n • α ∉ roots π)
  (hdim : Module.finrank k (rootSpace π α) = 1)
include hα hred hdim

/-- A weight vector `y ∈ H_α` whose class spans the cotangent space of `U_α`. -/
theorem exists_generator : ∃ y ∈ torusGrading π α,
    tMap (counitO π α) (Ideal.Quotient.mk (JU π α) y) ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hall : ∀ h : H, tMap (counitO π α) (Ideal.Quotient.mk (JU π α) h) = 0 := by
    intro h
    induction h using induction_torusGrading (π := π) with
    | h0 => simp
    | hadd x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
    | hmem χ x hx =>
      by_cases hχ : χ = α
      · subst hχ; exact hcon x hx
      · exact tMap_mk_eq_zero hα hred hχ hx
  have h1 := finrank_cotU hα hred hdim
  haveI := Module.nontrivial_of_finrank_eq_succ h1
  obtain ⟨c, hc⟩ := exists_ne (0 : CotU π α)
  obtain ⟨b, rfl⟩ := tMap_surjective (counitO π α) c
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact hc (hall h)

variable [Algebra.Smooth k H]

/-- The data of the coordinate: `y ∈ H_α`, `k[ȳ] = O(U_α)`. -/
theorem bijective_aeval_generator {y : H} (hy : y ∈ torusGrading π α)
    (hy0 : tMap (counitO π α) (Ideal.Quotient.mk (JU π α) y) ≠ 0) :
    Function.Bijective (Polynomial.aeval (R := k) (Ideal.Quotient.mk (JU π α) y)) := by
  letI := quotGradedAlgebra (isHomogeneousIdeal_JU (π := π) hα)
  set yb := Ideal.Quotient.mk (JU π α) y
  set p := tMap (counitO π α) yb
  have hyb : yb ∈ gradO π α α := mk_mem_gradO hy
  have hα0 : α ≠ 0 := fun h => by simpa using hα 1 (by simp [h])
  -- the section `s : Cot → O`, `c p ↦ c ȳ`
  let bas := FiniteDimensional.basisSingleton Unit (finrank_cotU hα hred hdim) p hy0
  let s : CotU π α →ₗ[k] (H ⧸ JU π α) := LinearMap.smulRight (bas.coord ()) yb
  have hrepr : ∀ q : CotU π α, bas.coord () q • p = q := by
    intro q
    have := bas.sum_repr q
    rw [Fintype.sum_unique] at this
    simpa [bas, FiniteDimensional.basisSingleton_apply] using this
  have hts : ∀ q, tMap (counitO π α) (s q) = q := by
    intro q
    simp only [s, LinearMap.smulRight_apply, map_smul]
    exact hrepr q
  have hπs : ∀ q, counitO π α (s q) = 0 := by
    intro q
    simp only [s, LinearMap.smulRight_apply, map_smul, counitO_eq_zero_of_mem hα0 hyb, smul_zero]
  have hg : ∀ (χ : Additive X) (b : H ⧸ JU π α), b ∈ gradO π α χ →
      s (tMap (counitO π α) b) ∈ gradO π α χ := by
    intro χ b hb
    by_cases hχ : χ = α
    · subst hχ
      simp only [s, LinearMap.smulRight_apply]
      exact Submodule.smul_mem _ _ hyb
    · obtain ⟨x, hx, rfl⟩ := hb
      change s (tMap (counitO π α) (Ideal.Quotient.mk _ x)) ∈ _
      rw [tMap_mk_eq_zero hα hred hχ hx, map_zero]
      exact Submodule.zero_mem _
  have hsurj := phi_surjective (isAug_rootGroup (π := π) hα) hts hπs hg
  have hcomp := fun P m => decompose_aeval (π := π) hα hyb P m
  have hred' : IsReduced (H ⧸ JU π α) := isReduced_quotient_prescribedUnit hα
  refine ⟨(injective_iff_map_eq_zero _).2 fun P hP => ?_, fun z => ?_⟩
  · by_contra hP0
    obtain ⟨m, hm⟩ : ∃ m, P.coeff m ≠ 0 := by
      by_contra h; push_neg at h; exact hP0 (Polynomial.ext h)
    have := hcomp P m
    rw [hP, DirectSum.decompose_zero] at this
    have h0 : yb ^ m = 0 := by
      have h2 : P.coeff m • yb ^ m = 0 := by rw [← this]; rfl
      exact (smul_eq_zero.1 h2).resolve_left hm
    have hyb0 : yb = 0 := IsReduced.eq_zero yb ⟨m, h0⟩
    exact hy0 (by show tMap (counitO π α) yb = 0; rw [hyb0, map_zero])
  · obtain ⟨w, rfl⟩ := hsurj z
    have hle : (SymmetricAlgebra.lift s).range ≤ Algebra.adjoin k {yb} := by
      let A' := Algebra.adjoin k {yb}
      let s' : CotU π α →ₗ[k] A' := LinearMap.codRestrict (A'.toSubmodule) s fun q => by
        show bas.coord () q • yb ∈ A'
        exact Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) _
      have he : SymmetricAlgebra.lift s = A'.val.comp (SymmetricAlgebra.lift s') :=
        SymmetricAlgebra.algHom_ext (LinearMap.ext fun q => by
          change SymmetricAlgebra.lift s (SymmetricAlgebra.ι k _ q) =
            A'.val (SymmetricAlgebra.lift s' (SymmetricAlgebra.ι k _ q))
          rw [SymmetricAlgebra.lift_ι_apply, SymmetricAlgebra.lift_ι_apply]
          rfl)
      rw [he]
      exact (AlgHom.range_comp_le_range _ _).trans (by rw [Subalgebra.range_val])
    have := hle ⟨w, rfl⟩
    rw [Algebra.adjoin_singleton_eq_range_aeval] at this
    obtain ⟨P, hP⟩ := this
    exact ⟨P, hP⟩

end Coordinate

/-! ### Primitivity -/

section Primitive

variable (hα : ∀ n : ℕ, n • α = 0 → n = 0) (hred : ∀ n : ℕ, 2 ≤ n → n • α ∉ roots π)
  (hdim : Module.finrank k (rootSpace π α) = 1) [Algebra.Smooth k H]
include hα hred hdim

/-- `O(U_α)_α = k ȳ`. -/
lemma mem_gradO_alpha {y : H} (hy : y ∈ torusGrading π α)
    (hy0 : tMap (counitO π α) (Ideal.Quotient.mk (JU π α) y) ≠ 0) {b : H ⧸ JU π α}
    (hb : b ∈ gradO π α α) : ∃ c : k, b = c • Ideal.Quotient.mk (JU π α) y := by
  letI := quotGradedAlgebra (isHomogeneousIdeal_JU (π := π) hα)
  obtain ⟨P, rfl⟩ := (bijective_aeval_generator hα hred hdim hy hy0).2 b
  refine ⟨P.coeff 1, ?_⟩
  have hyb : Ideal.Quotient.mk (JU π α) y ∈ gradO π α α := mk_mem_gradO hy
  have h1 := decompose_aeval (π := π) hα hyb P 1
  rw [one_smul, pow_one, DirectSum.decompose_of_mem_same _ hb] at h1
  exact h1

/-- **`Δȳ = ȳ ⊗ 1 + 1 ⊗ ȳ`.** -/
theorem comul_generator {y : H} (hy : y ∈ torusGrading π α)
    (hy0 : tMap (counitO π α) (Ideal.Quotient.mk (JU π α) y) ≠ 0) :
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (JU π α)) (Ideal.Quotient.mkₐ k (JU π α))
        (Coalgebra.comul (R := k) y) =
      Ideal.Quotient.mk (JU π α) y ⊗ₜ[k] 1 + 1 ⊗ₜ[k] Ideal.Quotient.mk (JU π α) y := by
  set yb := Ideal.Quotient.mk (JU π α) y
  set T := Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (JU π α))
    (Ideal.Quotient.mkₐ k (JU π α)) (Coalgebra.comul (R := k) y)
  have hα0 : α ≠ 0 := fun h => by simpa using hα 1 (by simp [h])
  have hyb : yb ∈ gradO π α α := mk_mem_gradO hy
  have hybne : yb ≠ 0 := fun h => hy0 (by rw [h, map_zero])
  -- step 1: `T ∈ span {ȳ ⊗ 1, 1 ⊗ ȳ}`
  have hT : T ∈ Submodule.span k {yb ⊗ₜ[k] (1 : H ⧸ JU π α), (1 : H ⧸ JU π α) ⊗ₜ[k] yb} := by
    have hc := comul_mem_tensorGrading hy
    have key : ∀ t ∈ tensorGrading π α,
        Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (JU π α))
          (Ideal.Quotient.mkₐ k (JU π α)) t ∈
        Submodule.span k {yb ⊗ₜ[k] (1 : H ⧸ JU π α), (1 : H ⧸ JU π α) ⊗ₜ[k] yb} := by
      intro t ht
      induction ht using Submodule.span_induction with
      | zero => simp
      | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
      | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ r ha
      | mem t ht =>
        obtain ⟨a, b, hab, x, hx, z, hz, rfl⟩ := ht
        simp only [Algebra.TensorProduct.map_tmul, Ideal.Quotient.mkₐ_eq_mk]
        by_cases ha : a ∈ rayMagnet α
        · by_cases hb : b ∈ rayMagnet α
          · obtain ⟨m, rfl⟩ := AddSubmonoid.mem_closure_singleton.1 ha
            obtain ⟨n, rfl⟩ := AddSubmonoid.mem_closure_singleton.1 hb
            rw [← add_smul] at hab
            have hmn : m + n = 1 := nsmul_injective_of hα (by simpa using hab)
            rcases Nat.add_eq_one_iff.1 hmn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · rw [zero_smul] at hx
              rw [one_smul] at hz
              obtain ⟨c, hc⟩ := mem_gradO_alpha hα hred hdim hy hy0 (mk_mem_gradO hz)
              rw [eq_algebraMap_of_mem_gradO_zero (mk_mem_gradO hx), hc,
                Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, ← TensorProduct.smul_tmul']
              exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
                (Submodule.subset_span (Set.mem_insert_of_mem _ rfl)))
            · rw [one_smul] at hx
              rw [zero_smul] at hz
              obtain ⟨c, hc⟩ := mem_gradO_alpha hα hred hdim hy hy0 (mk_mem_gradO hx)
              rw [eq_algebraMap_of_mem_gradO_zero (mk_mem_gradO hz), hc,
                Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, ← TensorProduct.smul_tmul']
              exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
                (Submodule.subset_span (Set.mem_insert _ _)))
          · rw [eq_zero_of_mem_gradO hb (mk_mem_gradO hz), TensorProduct.tmul_zero]
            exact Submodule.zero_mem _
        · rw [eq_zero_of_mem_gradO ha (mk_mem_gradO hx), TensorProduct.zero_tmul]
          exact Submodule.zero_mem _
    exact key _ hc
  obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.1 hT
  -- step 2: the counit laws
  have hmapL : ∀ t : H ⊗[k] H, LinearMap.lTensor (H ⧸ JU π α) (counitO π α).toLinearMap
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (JU π α))
        (Ideal.Quotient.mkₐ k (JU π α)) t) =
      LinearMap.rTensor k (Ideal.Quotient.mkₐ k (JU π α)).toLinearMap
        (LinearMap.lTensor H (Coalgebra.counit (R := k) (A := H)) t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
    | tmul a b => simp [counitO_mk]
  have hmapR : ∀ t : H ⊗[k] H, LinearMap.rTensor (H ⧸ JU π α) (counitO π α).toLinearMap
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (JU π α))
        (Ideal.Quotient.mkₐ k (JU π α)) t) =
      LinearMap.lTensor k (Ideal.Quotient.mkₐ k (JU π α)).toLinearMap
        (LinearMap.rTensor H (Coalgebra.counit (R := k) (A := H)) t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
    | tmul a b => simp [counitO_mk]
  have hε : counitO π α yb = 0 := counitO_eq_zero_of_mem hα0 hyb
  have hL := hmapL (Coalgebra.comul (R := k) y)
  rw [Coalgebra.lTensor_counit_comul] at hL
  change LinearMap.lTensor _ _ T = _ at hL
  rw [← hcd] at hL
  simp only [map_add, map_smul, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul,
    AlgHom.toLinearMap_apply, map_one, hε, TensorProduct.tmul_zero, smul_zero, add_zero,
    Ideal.Quotient.mkₐ_eq_mk] at hL
  have hR := hmapR (Coalgebra.comul (R := k) y)
  rw [Coalgebra.rTensor_counit_comul] at hR
  change LinearMap.rTensor _ _ T = _ at hR
  rw [← hcd] at hR
  simp only [map_add, map_smul, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul,
    AlgHom.toLinearMap_apply, map_one, hε, TensorProduct.zero_tmul, smul_zero, zero_add,
    Ideal.Quotient.mkₐ_eq_mk] at hR
  have hc1 : c = 1 := by
    have := congrArg (TensorProduct.rid k (H ⧸ JU π α)) hL
    simp only [map_smul, TensorProduct.rid_tmul, one_smul] at this
    by_contra hne
    have h2 : (c - 1) • yb = 0 := by rw [sub_smul, this, one_smul, sub_self]
    exact hybne ((smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne))
  have hd1 : d = 1 := by
    have := congrArg (TensorProduct.lid k (H ⧸ JU π α)) hR
    simp only [map_smul, TensorProduct.lid_tmul, one_smul] at this
    by_contra hne
    have h2 : (d - 1) • yb = 0 := by rw [sub_smul, this, one_smul, sub_self]
    exact hybne ((smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne))
  rw [← hcd, hc1, hd1, one_smul, one_smul]

/-- **Proposition `prop:root-groups`: `U_α = G^{[α⟩}_e` is a root group for `α`**, for `G` smooth
and `dim 𝔤_α = 1`. -/
theorem isRootGroup_rootGroupIdeal_of_finrank : IsRootGroup π α (rootGroupIdeal π α hα) := by
  obtain ⟨y, hy, hy0⟩ := exists_generator hα hred hdim
  have hI : (rootGroupIdeal π α hα).toIdeal = JU π α := by
    rw [rootGroupIdeal, prescribedUnitHopfIdeal_toIdeal]
  refine isRootGroup_rootGroupIdeal α hα hred ⟨y, hy, ?_⟩
  have key : ∀ I : Ideal H, I = JU π α →
      Function.Bijective (Polynomial.aeval (R := k) (Ideal.Quotient.mk I y)) ∧
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I) (Ideal.Quotient.mkₐ k I)
          (Coalgebra.comul (R := k) y) =
        Ideal.Quotient.mk I y ⊗ₜ[k] 1 + 1 ⊗ₜ[k] Ideal.Quotient.mk I y := by
    rintro I rfl
    exact ⟨bijective_aeval_generator hα hred hdim hy hy0, comul_generator hα hred hdim hy hy0⟩
  exact key _ hI

end Primitive

end AlgMag.Reductive
