/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.SplitReductiveRootSpaces
import AlgMag.Reductive.RootDatumFromGPairing

/-!
# Dimension of root spaces and reducedness

For split reductive data with a root datum (`SplitReductiveData.WithRootDatum π`):

* **Reducedness as `nα ∉ Φ`** (`nsmul_root_not_mem`): `nα ∉ Φ` for every root `α` and `n ≥ 2`,
  and more precisely `zsmul_mem_roots_iff`: `zα ∈ Φ ↔ z = ±1`. This restates the field
  `P.IsReduced` of `WithRootDatum`. Roots have infinite order (`zsmul_root_eq_zero`,
  `nsmul_root_eq_zero`), by `⟨α, α^∨⟩ = 2`; no torsion-freeness of `X` is needed.
* **Conversely** (`WithReflections.isReduced_rootPairing`): the root datum `D.rootPairing` built
  from `G` is reduced as soon as `nα ∉ Φ` for `n ≥ 2` (generic lemma `isReduced_of_two_smul_ne`).
* **`dim 𝔤_α ≥ 1`** for every root (`rootSpace_ne_bot`, `one_le_finrank_rootSpace`).
* **`dim 𝔤_α ≤ 1` for any root group** (`finrank_rootSpace_le_one_of_isRootGroup`): a closed
  subgroup `U = Spec(H/I) ≅ 𝔾_a` with `Lie(U) = 𝔤_α` forces `𝔤_α` to be a line.
* **Reduction of `dim 𝔤_α = 1` to root groups** (`finrank_rootSpace_eq_one_iff`): for `G` smooth
  and `α ∈ Φ`, `dim 𝔤_α = 1` iff some root group for `α` exists, iff `U_α = G^{[α⟩}_e` is a root
  group. `WithRootDatum.toWithRootSpaces` builds `WithRootSpaces` from root groups.
* **Dimension count** (for any `π`): `𝔤_α` is the `α`-weight space of `D(X)` on `Lie(G)`
  (`rootSpace_eq_map_adjointWeightSpace`), `Φ` is finite (`roots_finite`),
  `dim Lie(G) = dim 𝔤₀ + Σ_{α ∈ Φ} dim 𝔤_α` (`finrank_lie_eq_sum_rootSpace`), hence
  `dim 𝔤_α = 1` for all `α ∈ Φ` iff `dim Lie(G) = dim 𝔤₀ + |Φ|`
  (`forall_finrank_rootSpace_eq_one_iff`).

**Remark (why `dim 𝔤_α = 1` is not derived from `WithRootDatum` alone).** The fields of
`SplitReductiveData.WithRootDatum` do not imply `dim 𝔤_α = 1`: in characteristic `2` let
`G = SL₂ ⋉ V`, `V = (k²)^{(2)}` the Frobenius twist of the standard representation, `T` the
diagonal torus of `SL₂`, `X = ℤ`. The weights of `T` on `Lie G = 𝔰𝔩₂ ⊕ V` are `0` (once, on
`Lie T`) and `±2` (each twice), `V^T = 0` so `N_G(T) = N_{SL₂}(T)`, `W = {±1}`, and the root
datum of `SL₂` satisfies all fields, while `dim 𝔤_{±2} = 2`. A reductivity input (e.g. the
classification of rank-one groups) is needed for `dim 𝔤_α = 1`.
-/

suppress_compilation

open Magnetism TauCeti WithConv

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable [Module.Finite k (Bialgebra.CotangentSpace k H)]
variable {π : H →ₐc[k] MonoidAlgebra k X}

/-! ### Reducedness from the root datum -/

namespace SplitReductiveData.WithRootDatum

variable (D : SplitReductiveData.WithRootDatum π)
include D

/-- Roots have infinite order: `zα = 0 → z = 0` (pair with `α^∨`). -/
lemma zsmul_root_eq_zero {α : Additive X} (hα : α ∈ roots π) (z : ℤ) (hz : z • α = 0) :
    z = 0 := by
  rw [← D.range_root] at hα
  obtain ⟨i, rfl⟩ := hα
  have h := congrArg (fun x => D.P.toLinearMap x (D.P.coroot i)) hz
  simp only [map_zsmul, LinearMap.smul_apply, D.P.root_coroot_two, map_zero,
    LinearMap.zero_apply, smul_eq_mul] at h
  omega

/-- Roots have infinite order: `nα = 0 → n = 0`. -/
lemma nsmul_root_eq_zero {α : Additive X} (hα : α ∈ roots π) (n : ℕ) (hn : n • α = 0) :
    n = 0 := by
  have := D.zsmul_root_eq_zero hα n (by rw [natCast_zsmul]; exact hn)
  exact_mod_cast this

/-- **`zα ∈ Φ ↔ z = ±1`** for a root `α`. -/
theorem zsmul_mem_roots_iff {α : Additive X} (hα : α ∈ roots π) (z : ℤ) :
    z • α ∈ roots π ↔ z = 1 ∨ z = -1 := by
  constructor
  · intro hzα
    have hα' := hα
    rw [← D.range_root] at hα' hzα
    obtain ⟨i, hi⟩ := hα'
    obtain ⟨j, hj⟩ := hzα
    have := D.reduced
    have hdep : ¬ LinearIndependent ℤ ![D.P.root j, D.P.root i] := by
      rw [LinearIndependent.pair_iff]
      intro h
      have := h 1 (-z) (by rw [hi, hj, one_smul, neg_smul, add_neg_cancel])
      exact one_ne_zero this.1
    rcases RootPairing.IsReduced.eq_or_eq_neg j i hdep with h | h
    · rw [hi, hj] at h
      have : (z - 1) • α = 0 := by rw [sub_smul, h, one_smul, sub_self]
      have := D.zsmul_root_eq_zero hα _ this
      left; omega
    · rw [hi, hj] at h
      have : (z + 1) • α = 0 := by rw [add_smul, h, one_smul, neg_add_cancel]
      have := D.zsmul_root_eq_zero hα _ this
      right; omega
  · rintro (rfl | rfl)
    · rwa [one_smul]
    · rw [neg_smul, one_smul, ← D.range_root]
      rw [← D.range_root] at hα
      obtain ⟨i, rfl⟩ := hα
      exact ⟨D.P.reflectionPerm i i, by rw [D.P.root_reflectionPerm, D.P.reflection_apply_self]⟩

/-- **Reducedness: `nα ∉ Φ` for `n ≥ 2`.** -/
theorem nsmul_root_not_mem {α : Additive X} (hα : α ∈ roots π) (n : ℕ) (hn : 2 ≤ n) :
    n • α ∉ roots π := by
  intro h
  rw [← natCast_zsmul, D.zsmul_mem_roots_iff hα] at h
  omega

/-- **`2α ∉ Φ`.** -/
theorem two_smul_root_not_mem {α : Additive X} (hα : α ∈ roots π) : (2 : ℕ) • α ∉ roots π :=
  D.nsmul_root_not_mem hα 2 le_rfl

/-- `U_α = G^{[α⟩}_e` is a root group when `dim 𝔤_α = 1` (no torsion-freeness of `X`). -/
theorem isRootGroup_of_finrank [Algebra.Smooth k H] {α : Additive X} (hα : α ∈ roots π)
    (hdim : Module.finrank k (rootSpace π α) = 1) :
    IsRootGroup π α (rootGroupIdeal π α (D.nsmul_root_eq_zero hα)) :=
  isRootGroup_rootGroupIdeal_of_finrank (D.nsmul_root_eq_zero hα) (D.nsmul_root_not_mem hα) hdim

end SplitReductiveData.WithRootDatum

/-! ### `dim 𝔤_α ≥ 1` -/

instance finite_derivation_counit :
    Module.Finite k (Derivation k H (Bialgebra.CounitAlgebra k H k)) :=
  Module.Finite.equiv (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k))

omit [DecidableEq X] in
attribute [local instance] Derivation.adjointComodule in
/-- **`𝔤_α ≠ 0` for every root `α`.** -/
theorem rootSpace_ne_bot {α : Additive X} (hα : α ∈ roots π) : rootSpace π α ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hα.2
  intro hbot
  have hmem : Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k) x ∈ rootSpace π α :=
    fun χ hχ h hh => cotangentLinearEquiv_eq_zero_of_mem_adjointWeightSpace hx
      (fun e => hχ (Additive.toMul.injective e)) hh
  rw [hbot, Submodule.mem_bot] at hmem
  exact hx0 ((Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k)).injective
    (hmem.trans (map_zero _).symm))

omit [DecidableEq X] in
/-- **`dim 𝔤_α ≥ 1`** for every root `α`. -/
theorem one_le_finrank_rootSpace {α : Additive X} (hα : α ∈ roots π) :
    1 ≤ Module.finrank k (rootSpace π α) :=
  Nat.one_le_iff_ne_zero.2 fun h =>
    rootSpace_ne_bot hα (Submodule.finrank_eq_zero.1 h)

/-! ### `dim 𝔤_α ≤ 1` from a root group -/

/-- Evaluation at `y`: `𝔤_α → k`, `d ↦ d(y)`. -/
def rootSpaceEval (α : Additive X) (y : H) : rootSpace π α →ₗ[k] k where
  toFun d := Bialgebra.CounitAlgebra.algEquivSelf k H k ((d : Derivation k H _) y)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Module.Finite k (Bialgebra.CotangentSpace k H)] in
/-- A tangent vector killing `I` and the `𝔾_a`-coordinate `y` of `H/I` vanishes. -/
lemma der_eq_zero_of_coord {I : HopfIdeal k H} {y : H}
    (hy : Function.Surjective (Polynomial.aeval (R := k) (Ideal.Quotient.mk I.toIdeal y)))
    (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) (hdI : ∀ x ∈ I.toIdeal, d x = 0)
    (hdy : d y = 0) : d = 0 := by
  ext h
  obtain ⟨P, hP⟩ := hy (Ideal.Quotient.mk I.toIdeal h)
  have hmk : Ideal.Quotient.mk I.toIdeal (h - Polynomial.aeval y P) = 0 := by
    rw [map_sub, ← hP, ← Ideal.Quotient.mkₐ_eq_mk k, ← Polynomial.aeval_algHom_apply, sub_self]
  have hmem := Ideal.Quotient.eq_zero_iff_mem.1 hmk
  have h1 := hdI _ hmem
  rw [map_sub, Derivation.map_aeval, hdy, smul_zero, sub_zero] at h1
  rw [h1]
  rfl

/-- **`dim 𝔤_α ≤ 1` for any root group `U` for `α`**: `Lie(U) = 𝔤_α` and `U ≅ 𝔾_a`. -/
theorem finrank_rootSpace_le_one_of_isRootGroup {α : Additive X} {I : HopfIdeal k H}
    (hI : IsRootGroup π α I) : Module.finrank k (rootSpace π α) ≤ 1 := by
  obtain ⟨y, -, hbij, -⟩ := hI.ga
  have hinj : Function.Injective (rootSpaceEval (π := π) α y) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨d, hd⟩ h0
    have hdI : ∀ x ∈ I.toIdeal, d x = 0 :=
      (HopfIdeal.mem_lieSubalgebra_iff I d).1 ((hI.lie d).2 hd)
    have hdy : d y = 0 := (Bialgebra.CounitAlgebra.algEquivSelf k H k).injective
      (h0.trans (map_zero _).symm)
    exact Subtype.ext (der_eq_zero_of_coord hbij.2 d hdI hdy)
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_self] at this

/-- **`dim 𝔤_α = 1`** for a root `α` admitting a root group. -/
theorem finrank_rootSpace_eq_one_of_isRootGroup {α : Additive X} (hα : α ∈ roots π)
    {I : HopfIdeal k H} (hI : IsRootGroup π α I) : Module.finrank k (rootSpace π α) = 1 :=
  le_antisymm (finrank_rootSpace_le_one_of_isRootGroup hI) (one_le_finrank_rootSpace hα)

/-! ### Reduction of `dim 𝔤_α = 1` to root groups -/

namespace SplitReductiveData.WithRootDatum

variable (D : SplitReductiveData.WithRootDatum π)
include D

/-- **`dim 𝔤_α = 1` iff `U_α = G^{[α⟩}_e` is a root group iff some root group for `α`
exists**, for `G` smooth and `α ∈ Φ`. -/
theorem finrank_rootSpace_eq_one_iff [Algebra.Smooth k H] {α : Additive X} (hα : α ∈ roots π) :
    List.TFAE [Module.finrank k (rootSpace π α) = 1,
      IsRootGroup π α (rootGroupIdeal π α (D.nsmul_root_eq_zero hα)),
      ∃ I : HopfIdeal k H, IsRootGroup π α I] := by
  tfae_have 1 → 2 := D.isRootGroup_of_finrank hα
  tfae_have 2 → 3 := fun h => ⟨_, h⟩
  tfae_have 3 → 1 := fun ⟨_, hI⟩ => finrank_rootSpace_eq_one_of_isRootGroup hα hI
  tfae_finish

/-- **`WithRootSpaces` from root groups**: a root datum, `X` torsion-free and a root group for
every root. -/
def toWithRootSpaces
    (htf : ∀ (x : Additive X) (n : ℕ), n • x = 0 → n = 0 ∨ x = 0)
    (hU : ∀ α ∈ roots π, ∃ I : HopfIdeal k H, IsRootGroup π α I) :
    SplitReductiveData.WithRootSpaces π where
  toWithRootDatum := D
  torsionFree := htf
  finrank_rootSpace α hα := by
    obtain ⟨I, hI⟩ := hU α hα
    exact finrank_rootSpace_eq_one_of_isRootGroup hα hI

end SplitReductiveData.WithRootDatum

/-! ### Dimension count: `dim Lie G = dim 𝔤₀ + Σ_{α ∈ Φ} dim 𝔤_α` -/

omit [Module.Finite k (Bialgebra.CotangentSpace k H)] in
/-- Finite-dimensional version of `dim ⊕ = Σ dim` for an independent family spanning `M`,
trivial outside a finite set `s`. -/
lemma finrank_eq_sum_of_iSupIndep {ι M : Type*} [AddCommGroup M] [Module k M]
    [FiniteDimensional k M] {W : ι → Submodule k M} (hind : iSupIndep W)
    (htop : ⨆ i, W i = ⊤) (s : Finset ι) (hs : ∀ i ∉ s, W i = ⊥) :
    Module.finrank k M = ∑ i ∈ s, Module.finrank k (W i) := by
  classical
  have key : ∀ t : Finset ι,
      Module.finrank k (⨆ i ∈ t, W i : Submodule k M) = ∑ i ∈ t, Module.finrank k (W i) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t hat ih =>
      rw [Finset.iSup_insert, Finset.sum_insert hat, ← ih]
      have hdis : Disjoint (W a) (⨆ i ∈ t, W i) := by
        have := hind.disjoint_biSup (y := (t : Set ι)) (x := a) hat
        simpa only [Finset.mem_coe] using this
      have h := Submodule.finrank_sup_add_finrank_inf_eq (W a) (⨆ i ∈ t, W i)
      rw [disjoint_iff.1 hdis, finrank_bot, add_zero] at h
      exact h
  have hs' : (⨆ i ∈ s, W i : Submodule k M) = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine iSup_le fun i => ?_
    by_cases hi : i ∈ s
    · exact le_biSup W hi
    · rw [hs i hi]; exact bot_le
  rw [← key, hs', finrank_top]

omit [Module.Finite k (Bialgebra.CotangentSpace k H)] in
/-- A tangent vector vanishing on every weight space `H_χ` vanishes. -/
lemma der_eq_zero_of_forall_grading (d : Derivation k H (Bialgebra.CounitAlgebra k H k))
    (hd : ∀ χ, ∀ h ∈ torusGrading π χ, d h = 0) : d = 0 := by
  refine Derivation.ext fun h => ?_
  rw [Derivation.zero_apply]
  have hh : h ∈ ⨆ β, torusGrading π β := by
    rw [(isInternal_torusGrading π).submodule_iSup_eq_top]; trivial
  induction hh using Submodule.iSup_induction' with
  | mem β y hy => exact hd β y hy
  | zero => exact map_zero d
  | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]

attribute [local instance] Derivation.adjointComodule

/-- **`𝔤_α` is the `α`-weight space of `D(X)` on `Lie(G)`**: an element `x` of
`Lie(G) = Cot_e(G)^*` lies in the adjoint weight space of `α` iff the corresponding tangent
vector vanishes on every `H_χ`, `χ ≠ α`. -/
theorem mem_adjointWeightSpace_iff_mem_rootSpace {α : Additive X}
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    x ∈ Derivation.adjointWeightSpace π (Additive.toMul α) ↔
      Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k) x ∈ rootSpace π α := by
  constructor
  · intro hx χ hχ h hh
    exact cotangentLinearEquiv_eq_zero_of_mem_adjointWeightSpace hx
      (fun e => hχ (Additive.toMul.injective e)) hh
  · intro hx
    have htop : x ∈ ⨆ β, Derivation.adjointWeightSpace π β := by
      rw [DirectSum.IsInternal.submodule_iSup_eq_top (dec_ι := Classical.decEq X)
        (Derivation.isInternal_adjointWeightSpace π)]; trivial
    rw [iSup_split_single _ (Additive.toMul α), Submodule.mem_sup] at htop
    obtain ⟨a, ha, b, hb, rfl⟩ := htop
    have ha' : ∀ χ ≠ α, ∀ h ∈ torusGrading π χ,
        Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k) a h = 0 :=
      fun χ hχ h hh => cotangentLinearEquiv_eq_zero_of_mem_adjointWeightSpace ha
        (fun e => hχ (Additive.toMul.injective e)) hh
    have hb0 : b = 0 := by
      apply (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k)).injective
      rw [map_zero]
      refine der_eq_zero_of_forall_grading (π := π) _ fun χ h hh => ?_
      by_cases hχ : χ = α
      · subst hχ
        clear hx
        induction hb using Submodule.iSup_induction' with
        | mem β y hy =>
          induction hy using Submodule.iSup_induction' with
          | mem hβ z hz =>
            exact cotangentLinearEquiv_eq_zero_of_mem_adjointWeightSpace hz (Ne.symm hβ) hh
          | zero => rw [map_zero]; rfl
          | add y z _ _ hy hz => rw [map_add, Derivation.add_apply, hy, hz, add_zero]
        | zero => rw [map_zero]; rfl
        | add y z _ _ hy hz => rw [map_add, Derivation.add_apply, hy, hz, add_zero]
      · have := hx χ hχ h hh
        rwa [map_add, Derivation.add_apply, ha' χ hχ h hh, zero_add] at this
    rw [hb0, add_zero]
    exact ha

/-- `𝔤_α` is the image of the adjoint weight space under `Cot_e(G)^* ≃ Der_e(H)`. -/
theorem rootSpace_eq_map_adjointWeightSpace (α : Additive X) :
    rootSpace π α = (Derivation.adjointWeightSpace π (Additive.toMul α)).map
      (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k)).toLinearMap := by
  ext d
  constructor
  · intro hd
    refine ⟨(Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k)).symm d,
      (mem_adjointWeightSpace_iff_mem_rootSpace _).2 (by rwa [LinearEquiv.apply_symm_apply]),
      LinearEquiv.apply_symm_apply _ _⟩
  · rintro ⟨x, hx, rfl⟩
    exact (mem_adjointWeightSpace_iff_mem_rootSpace x).1 hx

theorem finrank_rootSpace_eq_finrank_adjointWeightSpace (α : Additive X) :
    Module.finrank k (rootSpace π α) =
      Module.finrank k (Derivation.adjointWeightSpace π (Additive.toMul α)) := by
  rw [rootSpace_eq_map_adjointWeightSpace]
  exact LinearEquiv.finrank_map_eq _ _

variable (π) in
omit [DecidableEq X] in
/-- **`Φ` is finite.** -/
theorem roots_finite : (roots π).Finite := by
  have hind := (Derivation.isInternal_adjointWeightSpace π).submodule_iSupIndep
    (dec_ι := Classical.decEq X)
  let _ := hind.fintypeNeBotOfFiniteDimensional
  have hfin : {χ : X | Derivation.adjointWeightSpace π χ ≠ ⊥}.Finite :=
    Set.finite_coe_iff.1 (inferInstanceAs (Finite {χ : X // Derivation.adjointWeightSpace π χ ≠ ⊥}))
  exact (hfin.preimage Additive.toMul.injective.injOn).subset fun α hα => hα.2

variable (π) in
/-- **Dimension count**: `dim Lie(G) = dim 𝔤₀ + Σ_{α ∈ Φ} dim 𝔤_α`. -/
theorem finrank_lie_eq_sum_rootSpace :
    Module.finrank k (Derivation k H (Bialgebra.CounitAlgebra k H k)) =
      Module.finrank k (rootSpace π 0) +
        ∑ α ∈ (roots_finite π).toFinset, Module.finrank k (rootSpace π α) := by
  classical
  have hint := Derivation.isInternal_adjointWeightSpace π
  set s : Finset X := insert 1 ((roots_finite π).toFinset.map Additive.toMul.toEmbedding)
  have h1 : (1 : X) ∉ (roots_finite π).toFinset.map Additive.toMul.toEmbedding := by
    simp only [Finset.mem_map, Set.Finite.mem_toFinset, Equiv.coe_toEmbedding, not_exists,
      not_and]
    intro α hα h
    exact hα.1 h
  have hs : ∀ χ ∉ s, Derivation.adjointWeightSpace π χ = ⊥ := by
    intro χ hχ
    by_contra hne
    apply hχ
    by_cases h : χ = 1
    · rw [h]; exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finset.mem_map.2 ⟨Additive.ofMul χ, ?_, rfl⟩)
      rw [Set.Finite.mem_toFinset]
      exact ⟨h, hne⟩
  rw [← (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k)).finrank_eq,
    finrank_eq_sum_of_iSupIndep (hint.submodule_iSupIndep (dec_ι := Classical.decEq X))
      (DirectSum.IsInternal.submodule_iSup_eq_top (dec_ι := Classical.decEq X) hint) s hs,
    Finset.sum_insert h1, Finset.sum_map, finrank_rootSpace_eq_finrank_adjointWeightSpace]
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [finrank_rootSpace_eq_finrank_adjointWeightSpace]
  rfl

/-- **`dim 𝔤_α = 1` for all roots iff `dim Lie(G) = dim 𝔤₀ + |Φ|`.** -/
theorem forall_finrank_rootSpace_eq_one_iff :
    (∀ α ∈ roots π, Module.finrank k (rootSpace π α) = 1) ↔
      Module.finrank k (Derivation k H (Bialgebra.CounitAlgebra k H k)) =
        Module.finrank k (rootSpace π 0) + (roots_finite π).toFinset.card := by
  rw [finrank_lie_eq_sum_rootSpace π, add_right_inj, Finset.card_eq_sum_ones, eq_comm,
    Finset.sum_eq_sum_iff_of_le fun α hα =>
      one_le_finrank_rootSpace ((Set.Finite.mem_toFinset _).1 hα)]
  simp only [Set.Finite.mem_toFinset, eq_comm (a := 1)]


/-! ### Reducedness of the root datum built from `G` -/

omit [Module.Finite k (Bialgebra.CotangentSpace k H)] [DecidableEq X] in
/-- A finite root pairing over `ℤ` on a torsion-free lattice with `2α ∉ Φ` for every root `α`
is reduced (`⟨β, α^∨⟩ ∣ 4` and `⟨β, α^∨⟩ α = 2β` for dependent roots). -/
theorem isReduced_of_two_smul_ne {ι M N : Type*} [Finite ι] [AddCommGroup M] [AddCommGroup N]
    [Module.IsTorsionFree ℤ M] (P : RootPairing ι ℤ M N)
    (h2 : ∀ i j, P.root j ≠ (2 : ℤ) • P.root i) : P.IsReduced := by
  refine ⟨fun i j hl => ?_⟩
  have hc : P.pairing i j * P.pairing j i = 4 :=
    (P.coxeterWeight_eq_four_iff_not_linearIndependent (i := i) (j := j)).2 hl
  have hs := P.pairing_smul_root_eq_of_not_linearIndependent hl
  have hd : P.pairing j i ∣ 4 := ⟨P.pairing i j, by rw [← hc, mul_comm]⟩
  have hle := Int.le_of_dvd (by norm_num) hd
  have hge : -4 ≤ P.pairing j i := by
    have := Int.le_of_dvd (by norm_num) (Int.neg_dvd.2 hd); omega
  have inj2 : Function.Injective (fun x : M => (2 : ℤ) • x) := smul_right_injective M two_ne_zero
  generalize P.pairing j i = p at hs hd hle hge
  interval_cases p
  · exfalso
    apply h2 (P.reflectionPerm i i) j
    rw [P.root_reflectionPerm, P.reflection_apply_self]
    apply inj2
    simp only
    rw [← hs]
    module
  · norm_num at hd
  · right
    apply inj2
    simp only
    rw [smul_neg, ← hs]
    module
  · exfalso
    apply h2 (P.reflectionPerm j j) i
    rw [P.root_reflectionPerm, P.reflection_apply_self, smul_neg, ← hs]
    module
  · norm_num at hd
  · exfalso
    apply h2 j i
    rw [← hs, one_smul]
  · left
    exact inj2 hs
  · norm_num at hd
  · exfalso
    apply h2 i j
    apply inj2
    simp only
    rw [← hs]
    module

/-- **`D.rootPairing` is reduced** as soon as `nα ∉ Φ` for every root `α` and `n ≥ 2`
(fact (2), `R2`). `Φ = -Φ` holds automatically (`s_α α = -α`), and `Φ` is finite by
`roots_finite`. -/
theorem SplitReductiveData.WithReflections.isReduced_rootPairing
    [Module.Finite ℤ (Additive X)] [Module.IsTorsionFree ℤ (Additive X)]
    (D : SplitReductiveData.WithReflections π)
    (hred : ∀ α ∈ roots π, ∀ n : ℕ, 2 ≤ n → n • α ∉ roots π) : D.rootPairing.IsReduced := by
  have : Finite (roots π) := (roots_finite π).to_subtype
  refine isReduced_of_two_smul_ne _ fun i j h => ?_
  apply hred i i.2 2 le_rfl
  have hj : ((2 : ℕ) • (i : Additive X)) = j := by
    rw [← natCast_zsmul]
    exact h.symm
  rw [hj]
  exact j.2

end AlgMag.Reductive
