/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.SplitReductiveRootSpaces

/-!
# Uniqueness of root groups, by magnets

Let `U = Spec (H/I)` be a root group for `α` (`IsRootGroup π α I`): `T`-stable, `Lie U = 𝔤_α`,
and `H/I = k[ȳ]` with `y ∈ H_α`. Then `U = U_α = G^{[α⟩}_e` (`rootGroupIdeal`).

* `rootGroupIdeal_le_of_isRootGroup` (`U ⊆ G^{[α⟩}_e`): the grading of `H/I = k[ȳ]` is concentrated
  in `ℕα`, with degree `0` equal to `k`. So `I` contains `H_χ` for `χ ∉ [α⟩`, and `x - ε(x)` for
  `x ∈ H_0`: these generate the ideal of `G^{[α⟩}_e`.
* `eq_rootGroupIdeal_of_isRootGroup`: if moreover `U_α` is a root group, then `I = U_α`. The
  surjection `k[ȳ_α] = H/I_α → H/I = k[ȳ]` sends `ȳ_α` to a weight-`α` element `c • ȳ`, and `c ≠ 0`
  since `ȳ` is in its image; so it is injective.
* `SplitReductiveData.WithRootSpaces.eq_rootGroupIdeal`: for split reductive `G` with root spaces
  of dimension one, every root group for `α` is `U_α`.
-/

suppress_compilation

open Magnetism TauCeti WithConv Polynomial

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable {π : H →ₐc[k] MonoidAlgebra k X}

omit [DecidableEq X] in
/-- For `α` of infinite order, `n ↦ n • α` is injective. -/
lemma nsmul_inj_of_infiniteOrder {α : Additive X} (hα : ∀ n : ℕ, n • α = 0 → n = 0)
    {m n : ℕ} (h : m • α = n • α) : m = n := by
  rcases le_total m n with hmn | hmn
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    have : d • α = 0 := by rw [add_smul] at h; simpa using h
    have := hα d this
    omega
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    have : d • α = 0 := by rw [add_smul] at h; simpa using h
    have := hα d this
    omega

/-- The weight-`χ` component of `y ^ m`, for `y ∈ H_α`. -/
lemma proj_pow_of_mem {α : Additive X} {y : H} (hy : y ∈ torusGrading π α) (χ : Additive X)
    (m : ℕ) :
    GradedAlgebra.proj (torusGrading π) χ (y ^ m) = if m • α = χ then y ^ m else 0 := by
  have hm : y ^ m ∈ torusGrading π (m • α) := SetLike.pow_mem_graded m hy
  rw [GradedAlgebra.proj_apply]
  split_ifs with h
  · subst h; exact DirectSum.decompose_of_mem_same _ hm
  · exact DirectSum.decompose_of_mem_ne _ hm h

lemma mk_aeval (I : Ideal H) (y : H) (p : k[X]) :
    aeval (Ideal.Quotient.mk I y) p = Ideal.Quotient.mk I (aeval y p) := by
  have := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ k I) y p
  rwa [Ideal.Quotient.mkₐ_eq_mk] at this

/-- If `h ∈ H_χ` has class `p(ȳ)` in `H/I`, `I` homogeneous, then the weight-`χ` component of
`h - p(y)` lies in `I`. -/
lemma sub_proj_aeval_mem {I : Ideal H} (hI : I.IsHomogeneous (torusGrading π)) {α : Additive X}
    {y : H} (hy : y ∈ torusGrading π α) {χ : Additive X} {h : H} (hh : h ∈ torusGrading π χ)
    (p : k[X]) (hp : Ideal.Quotient.mk I h = aeval (Ideal.Quotient.mk I y) p) :
    h - ∑ m ∈ Finset.range (p.natDegree + 1), p.coeff m • (if m • α = χ then y ^ m else 0) ∈ I := by
  have h1 : h - aeval y p ∈ I := by
    rw [← Ideal.Quotient.eq, hp, mk_aeval]
  have h2 := (Ideal.IsHomogeneous.mem_iff _ hI).1 h1 χ
  rw [← GradedAlgebra.proj_apply, map_sub, aeval_eq_sum_range, map_sum] at h2
  simp only [map_smul, proj_pow_of_mem hy] at h2
  rwa [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same _ hh] at h2

/-- **Weight `χ ∉ [α⟩` dies in `k[ȳ]`.** -/
lemma mem_of_notMem_rayMagnet {I : Ideal H} (hI : I.IsHomogeneous (torusGrading π))
    {α : Additive X} {y : H} (hy : y ∈ torusGrading π α)
    (hs : Function.Surjective (aeval (R := k) (Ideal.Quotient.mk I y)))
    {χ : Additive X} (hχ : χ ∉ rayMagnet α) {h : H} (hh : h ∈ torusGrading π χ) : h ∈ I := by
  obtain ⟨p, hp⟩ := hs (Ideal.Quotient.mk I h)
  have := sub_proj_aeval_mem hI hy hh p hp.symm
  rwa [Finset.sum_eq_zero (fun m _ => by
    rw [ite_eq_right (fun e => hχ (AddSubmonoid.mem_closure_singleton.2 ⟨m, e⟩)), smul_zero]),
    sub_zero] at this

/-- **Weight `nα` in `k[ȳ]` is the line `k ȳ^n`.** -/
lemma exists_sub_smul_pow_mem {α : Additive X} (hα : ∀ n : ℕ, n • α = 0 → n = 0)
    {I : Ideal H} (hI : I.IsHomogeneous (torusGrading π)) {y : H} (hy : y ∈ torusGrading π α)
    (hs : Function.Surjective (aeval (R := k) (Ideal.Quotient.mk I y)))
    {n : ℕ} {h : H} (hh : h ∈ torusGrading π (n • α)) : ∃ c : k, h - c • y ^ n ∈ I := by
  obtain ⟨p, hp⟩ := hs (Ideal.Quotient.mk I h)
  refine ⟨p.coeff n, ?_⟩
  have := sub_proj_aeval_mem hI hy hh p hp.symm
  rwa [Finset.sum_eq_single n (fun m _ hmn => by
      rw [ite_eq_right (fun e => hmn (nsmul_inj_of_infiniteOrder hα e)), smul_zero])
    (fun hn => by
      rw [Finset.mem_range, not_lt] at hn
      rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_smul]), ite_eq_left rfl] at this

variable [Module.Finite k (Bialgebra.CotangentSpace k H)]

/-- **`U ⊆ G^{[α⟩}_e`** for every root group `U = Spec (H/I)` for `α`. -/
theorem rootGroupIdeal_le_of_isRootGroup {α : Additive X} (hα : ∀ n : ℕ, n • α = 0 → n = 0)
    {I : HopfIdeal k H} (hI : IsRootGroup π α I) :
    (rootGroupIdeal π α hα).toIdeal ≤ I.toIdeal := by
  obtain ⟨y, hy, hbij, -⟩ := hI.ga
  rw [rootGroupIdeal, prescribedUnitHopfIdeal_toIdeal, prescribedUnitIdeal, magnetIdeal,
    sup_le_iff, Ideal.span_le, Ideal.span_le]
  constructor
  · intro x hx
    obtain ⟨χ, hχ, hx⟩ := Set.mem_iUnion₂.1 hx
    exact mem_of_notMem_rayMagnet hI.stable hy hbij.2 hχ hx
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, hc⟩ := exists_sub_smul_pow_mem hα hI.stable hy hbij.2 (n := 0)
      (by rwa [zero_smul])
    rw [pow_zero] at hc
    have hε := I.counit_eq_zero (HopfIdeal.mem_toIdeal.1 hc)
    rw [map_sub, map_smul, Bialgebra.counit_one, smul_eq_mul, mul_one, sub_eq_zero] at hε
    rw [SetLike.mem_coe, hε, Algebra.algebraMap_eq_smul_one]
    exact hc

omit [Module.Finite k (Bialgebra.CotangentSpace k H)] in
/-- In `H/I = k[ȳ]`, `ȳ ≠ 0`. -/
lemma mk_ne_zero_of_injective {I : Ideal H} {y : H}
    (hi : Function.Injective (aeval (R := k) (Ideal.Quotient.mk I y))) :
    Ideal.Quotient.mk I y ≠ 0 := by
  intro h0
  have : aeval (R := k) (Ideal.Quotient.mk I y) (Polynomial.X : k[X]) =
      aeval (Ideal.Quotient.mk I y) (0 : k[X]) := by
    rw [aeval_X, map_zero, h0]
  exact X_ne_zero (hi this)

/-- **Uniqueness of root groups.** If `U = Spec (H/I)` and `U_α = G^{[α⟩}_e` are root groups for
`α`, then `U = U_α`. -/
theorem eq_rootGroupIdeal_of_isRootGroup {α : Additive X} (hα : ∀ n : ℕ, n • α = 0 → n = 0)
    {I : HopfIdeal k H} (hI : IsRootGroup π α I)
    (hJ : IsRootGroup π α (rootGroupIdeal π α hα)) : I = rootGroupIdeal π α hα := by
  set J := rootGroupIdeal π α hα with hJdef
  have hJI : J.toIdeal ≤ I.toIdeal := rootGroupIdeal_le_of_isRootGroup hα hI
  obtain ⟨y, hy, hbij, -⟩ := hI.ga
  obtain ⟨y', hy', hbij', -⟩ := hJ.ga
  have hy1 : y ∈ torusGrading π (1 • α) := by rwa [one_smul]
  have hy1' : y' ∈ torusGrading π (1 • α) := by rwa [one_smul]
  -- `ȳ_α = c • ȳ` in `H/I`, and `ȳ = d • ȳ_α` in `H/J`
  obtain ⟨c, hc⟩ := exists_sub_smul_pow_mem hα hI.stable hy hbij.2 hy1'
  obtain ⟨d, hd⟩ := exists_sub_smul_pow_mem hα hJ.stable hy' hbij'.2 hy1
  rw [pow_one] at hc hd
  have hc' : Ideal.Quotient.mk I.toIdeal y' = c • Ideal.Quotient.mk I.toIdeal y := by
    rw [Ideal.Quotient.eq.2 hc]; exact map_smul (Ideal.Quotient.mkₐ k I.toIdeal) c y
  have hd' : Ideal.Quotient.mk I.toIdeal y = d • Ideal.Quotient.mk I.toIdeal y' := by
    rw [Ideal.Quotient.eq.2 (hJI hd)]; exact map_smul (Ideal.Quotient.mkₐ k I.toIdeal) d y'
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc'
    rw [hc', smul_zero] at hd'
    exact mk_ne_zero_of_injective hbij.1 hd'
  refine (HopfIdeal.toIdeal_le_toIdeal.1 ?_).antisymm (HopfIdeal.toIdeal_le_toIdeal.1 hJI)
  intro z hz
  obtain ⟨p, hp⟩ := hbij'.2 (Ideal.Quotient.mk J.toIdeal z)
  rw [mk_aeval, Ideal.Quotient.eq] at hp
  have hpI : aeval y' p ∈ I.toIdeal := by
    have := I.toIdeal.add_mem (hJI hp) hz
    rwa [sub_add_cancel] at this
  have hcomp : aeval (Ideal.Quotient.mk I.toIdeal y) (p.comp (C c * Polynomial.X)) =
      aeval (Ideal.Quotient.mk I.toIdeal y) (0 : k[X]) := by
    rw [aeval_comp, map_mul, aeval_C, aeval_X, ← Algebra.smul_def, ← hc', mk_aeval, map_zero,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hpI
  have hp0 : p = 0 := by
    have h0 := hbij.1 hcomp
    have : (p.comp (C c * Polynomial.X)).comp (C c⁻¹ * Polynomial.X) = p := by
      rw [comp_assoc, mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hc0, C_1,
        one_mul, comp_X]
    rw [← this, h0, zero_comp]
  rw [hp0, map_zero, zero_sub] at hp
  exact J.toIdeal.neg_mem_iff.1 hp

/-- **Uniqueness of root groups for split reductive `G`** (root spaces of dimension one): every
root group for a root `α` is `U_α = G^{[α⟩}_e`. -/
theorem SplitReductiveData.WithRootSpaces.eq_rootGroupIdeal [Algebra.Smooth k H]
    (D : SplitReductiveData.WithRootSpaces π) {α : Additive X} (hα : α ∈ roots π)
    {I : HopfIdeal k H} (hI : IsRootGroup π α I) :
    I = rootGroupIdeal π α (D.nsmul_root_eq_zero hα) :=
  eq_rootGroupIdeal_of_isRootGroup _ hI (isRootGroup_of_withRootSpaces D hα)

end AlgMag.Reductive
