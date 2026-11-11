/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.RootDatumFromGPairing
import AlgMag.Reductive.RegularCentralizer

/-!
# Reflections at a root from the rank-one attractor `G^{ℤα}`

For a root `α`, let `ℤα` be the group magnet `lineMagnet α` and `G^{ℤα}` its attractor. By
Proposition 3.35 for group magnets, `G^{ℤα} = Z_G(D(X ⧸ ℤα))`, the centralizer of the
codimension-one diagonalizable subgroup `ker α` (`magnetHopfIdeal_lineMagnet_eq_centralizer`):
the rank-one Levi subgroup at `α`.

For a `k`-point `n` normalizing `T` with automorphism `σ`, the key lemma
(`mem_attractorSubgroup_iff_joinIrredWeylMagnets`) gives `n ∈ G^{ℤα}(k) ↔ (1 - σ)X ⊆ ℤα`
(`mem_lineAttractor_iff`). Hence:

* `isReflectionOn_of_mem_lineAttractor`: a point of `N_G(T)(k) ∩ G^{ℤα}(k)` with `σ ≠ 1` acts on
  `X` by a reflection at `α` (`σ α = -α` from `smul_self_eq_neg`, `W` finite and faithful);
* `not_mem_torus_of_ne_one`: such a point is not in `T(k)`;
* `exists_reflection_iff_lineAttractor`: a point of `N_G(T)(k)` acting by a reflection at `α`
  exists iff `N_{G^{ℤα}}(T)(k) ⊄ T(k)`, iff some `w ≠ 1` in `W` has `(1 - w)X ⊆ ℤα`;
* `exists_normalizing_reflection_of_lineAttractor`: `n ∈ N_G(T)(k)`, `n ∉ T(k)`, acting by a
  reflection at `α`, from a point of `N_{G^{ℤα}}(T)(k)` outside `T`;
* `SplitReductiveData.WithReflections.ofLineAttractor`: `WithReflections` from
  `N_{G^{ℤα}}(T)(k) ≠ T(k)` for every root `α`.

The remaining input, `N_{G^{ℤα}}(T)(k) ⊄ T(k)` (the Weyl group of the rank-one Levi is not
trivial), is where reductivity of `G` enters: `SplitReductiveData` alone does not imply it.
For the Borel subgroup of `SL₂` (roots `{α}`), or `𝔾_a² ⋊ 𝔾_m` with weights `α, -α`
(roots `{±α}`, smooth, connected, `Z_G(T) = T`), the normalizer of `T` is `T`, `W = 1`, and all
fields of `SplitReductiveData` hold.
-/

suppress_compilation

open TensorProduct Magnetism TauCeti WithConv

namespace AlgMag.Reductive

open AlgMag.Weyl LatticeReflection

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable {π : H →ₐc[k] MonoidAlgebra k X}

/-- The group magnet `ℤα`. -/
def lineMagnet (α : Additive X) : Magnet (Additive X) := (AddSubgroup.zmultiples α).toAddSubmonoid

omit [DecidableEq X] in
@[simp] lemma mem_lineMagnet {α χ : Additive X} :
    χ ∈ lineMagnet α ↔ χ ∈ AddSubgroup.zmultiples α := Iff.rfl

omit [DecidableEq X] in
/-- `ℤα` is the group magnet of the subgroup `⟨α⟩ ≤ X`. -/
lemma lineMagnet_eq_groupMagnet (α : Additive X) :
    lineMagnet α = groupMagnet (Subgroup.zpowers (Additive.toMul α)) := by
  ext χ
  rw [mem_lineMagnet, mem_groupMagnet, AddSubgroup.mem_zmultiples_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n, by simp⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [← ofMul_toMul χ, ← hn, ofMul_zpow, ofMul_toMul]

/-- **`G^{ℤα} = Z_G(D(X ⧸ ⟨α⟩))`**, the rank-one Levi subgroup at `α`. -/
theorem magnetHopfIdeal_lineMagnet_eq_centralizer (α : Additive X) :
    magnetHopfIdeal π (lineMagnet α) =
      BialgHom.centralizerHopfIdeal (quotientTorus π (Subgroup.zpowers (Additive.toMul α))) := by
  rw [lineMagnet_eq_groupMagnet, magnetHopfIdeal_groupMagnet_eq_centralizer]

omit [DecidableEq X] in
/-- `(1 - σ)X ⊆ ℤα` in terms of the Weyl magnets of `σ`. -/
lemma joinIrredWeylMagnets_subset_lineMagnet_iff {σ : X ≃* X} {α : Additive X} :
    joinIrredWeylMagnets σ ⊆ (lineMagnet α : Set (Additive X)) ↔
      ∀ x, x - actW σ x ∈ AddSubgroup.zmultiples α := by
  constructor
  · intro h x
    exact h ⟨x, rfl⟩
  · rintro h _ ⟨x, rfl⟩
    exact h x

/-- **Key lemma for `ℤα`.** A `k`-point `n` normalizing `T` with automorphism `σ` lies in
`G^{ℤα}(k)` iff `(1 - σ)X ⊆ ℤα`. -/
theorem mem_lineAttractor_iff (hπ : Function.Surjective π) {n : WithConv (H →ₐ[k] k)}
    {σ : X ≃* X} (hn : IsNormalizingWith π k n σ) (α : Additive X) :
    n ∈ attractorSubgroup π (lineMagnet α) k ↔ ∀ x, x - actW σ x ∈ AddSubgroup.zmultiples α := by
  rw [mem_attractorSubgroup_iff_joinIrredWeylMagnets π hπ hn, joinIrredWeylMagnets_subset_lineMagnet_iff]

/-- A `k`-point of `T` (`ker π ≤ ker n`) lies in `G^0(k)`. -/
lemma mem_attractorSubgroup_bot_of_ker_le {n : WithConv (H →ₐ[k] k)}
    (hn : RingHom.ker π.toAlgHom ≤ RingHom.ker n.ofConv) :
    n ∈ attractorSubgroup π ⊥ k := by
  rw [mem_attractorSubgroup]
  exact (magnetIdeal_le_ker_torus π ⊥).trans hn

/-- **`n ∉ T(k)`.** A `k`-point normalizing `T` with automorphism `σ ≠ 1` is not in `T(k)`. -/
theorem not_mem_torus_of_ne_one (hπ : Function.Surjective π) {n : WithConv (H →ₐ[k] k)}
    {σ : X ≃* X} (hn : IsNormalizingWith π k n σ) (hσ : σ ≠ 1) :
    ¬ RingHom.ker π.toAlgHom ≤ RingHom.ker n.ofConv := by
  intro hT
  have h := (mem_attractorSubgroup_iff_joinIrredWeylMagnets π hπ hn ⊥).1
    (mem_attractorSubgroup_bot_of_ker_le hT)
  refine hσ (MulEquiv.ext fun x => ?_)
  have hx := h ⟨Additive.ofMul x, rfl⟩
  simp only [SetLike.mem_coe, AddSubmonoid.mem_bot, sub_eq_zero] at hx
  exact (congrArg Additive.toMul hx).symm

variable [Module.Finite k (Bialgebra.CotangentSpace k H)]
variable [Module.IsTorsionFree ℤ (Additive X)]

omit [DecidableEq X] in
/-- A reflection at a root is not the identity (`α ≠ -α`, `X` torsion-free). -/
lemma ne_one_of_isReflectionOn {σ : X ≃* X} {α : Additive X} (hα : α ∈ roots π)
    (h : IsReflectionOn σ α) : σ ≠ 1 := by
  rintro rfl
  have h1 : actW (1 : X ≃* X) α = α := rfl
  have h2 : (2 : ℤ) • α = 0 := by
    rw [two_zsmul]
    nth_rewrite 1 [← h1]
    rw [h.1, neg_add_cancel]
  exact ne_zero_of_mem_roots hα ((smul_eq_zero_iff_right two_ne_zero).mp h2)

/-- **A reflection from the rank-one attractor.** A `k`-point of `N_G(T) ∩ G^{ℤα}` with
automorphism `σ ≠ 1` acts on `X` by a reflection at the root `α`: `σ α = -α` and
`(1 - σ)X ⊆ ℤα`. -/
theorem isReflectionOn_of_mem_lineAttractor (D : SplitReductiveData π) {α : Additive X}
    (hα : α ∈ roots π) {n : WithConv (H →ₐ[k] k)} {σ : X ≃* X}
    (hn : IsNormalizingWith π k n σ) (hnα : n ∈ attractorSubgroup π (lineMagnet α) k)
    (hσ : σ ≠ 1) : IsReflectionOn σ α := by
  have hrefl := (mem_lineAttractor_iff D.surjective hn α).1 hnα
  have hσW := mem_W_of_isNormalizingWith π D hn
  have : Finite D.W := D.finite
  have hne : (⟨σ, hσW⟩ : D.W) ≠ 1 := fun h1 => hσ (congrArg Subtype.val h1)
  exact ⟨smul_self_eq_neg (G := D.W) (w := ⟨σ, hσW⟩) (fun _ _ h => weyl_ext h)
    (ne_zero_of_mem_roots hα) hrefl hne, hrefl⟩

/-- **Rank-one criterion.** For a root `α`, the following are equivalent:
(1) some `n ∈ N_G(T)(k)` acts on `X` by a reflection at `α`;
(2) `N_{G^{ℤα}}(T)(k) ⊄ T(k)`: some `n ∈ G^{ℤα}(k)` normalizes `T` with automorphism `σ ≠ 1`;
(3) some `w ≠ 1` in `W` has `(1 - w)X ⊆ ℤα`. -/
theorem exists_reflection_iff_lineAttractor (D : SplitReductiveData π) {α : Additive X}
    (hα : α ∈ roots π) :
    List.TFAE
      [∃ (n : WithConv (H →ₐ[k] k)) (σ : X ≃* X), IsNormalizingWith π k n σ ∧ IsReflectionOn σ α,
       ∃ (n : WithConv (H →ₐ[k] k)) (σ : X ≃* X), IsNormalizingWith π k n σ ∧
          n ∈ attractorSubgroup π (lineMagnet α) k ∧ σ ≠ 1,
       ∃ w ∈ D.W, w ≠ 1 ∧ ∀ x, x - actW w x ∈ AddSubgroup.zmultiples α] := by
  tfae_have 1 → 2 := by
    rintro ⟨n, σ, hn, h⟩
    exact ⟨n, σ, hn, (mem_lineAttractor_iff D.surjective hn α).2 h.2,
      ne_one_of_isReflectionOn hα h⟩
  tfae_have 2 → 1 := by
    rintro ⟨n, σ, hn, hnα, hσ⟩
    exact ⟨n, σ, hn, isReflectionOn_of_mem_lineAttractor D hα hn hnα hσ⟩
  tfae_have 2 → 3 := by
    rintro ⟨n, σ, hn, hnα, hσ⟩
    exact ⟨σ, mem_W_of_isNormalizingWith π D hn, hσ,
      (mem_lineAttractor_iff D.surjective hn α).1 hnα⟩
  tfae_have 3 → 2 := by
    rintro ⟨w, hw, hw1, h⟩
    have hn := D.rep_normalizing ⟨w, hw⟩
    exact ⟨D.rep ⟨w, hw⟩, w, hn, (mem_lineAttractor_iff D.surjective hn α).2 h, hw1⟩
  tfae_finish

/-- **A reflection at `α` in `N_G(T)(k) ∖ T(k)`**, from a point of `N_{G^{ℤα}}(T)(k)` outside
`T`: there is `n ∈ N_G(T)(k)` with `n ∉ T(k)` whose automorphism `σ` of `X` is a reflection
at `α`. -/
theorem exists_normalizing_reflection_of_lineAttractor (D : SplitReductiveData π)
    {α : Additive X} (hα : α ∈ roots π) {n : WithConv (H →ₐ[k] k)} {σ : X ≃* X}
    (hn : IsNormalizingWith π k n σ) (hnα : n ∈ attractorSubgroup π (lineMagnet α) k)
    (hσ : σ ≠ 1) :
    ∃ (n : WithConv (H →ₐ[k] k)) (σ : X ≃* X), IsNormalizingWith π k n σ ∧
      ¬ RingHom.ker π.toAlgHom ≤ RingHom.ker n.ofConv ∧ IsReflectionOn σ α :=
  ⟨n, σ, hn, not_mem_torus_of_ne_one D.surjective hn hσ,
    isReflectionOn_of_mem_lineAttractor D hα hn hnα hσ⟩

/-- **`WithReflections` from the rank-one attractors**: it suffices that for each root `α`,
`N_{G^{ℤα}}(T)(k) ⊄ T(k)`. -/
def SplitReductiveData.WithReflections.ofLineAttractor (D : SplitReductiveData π)
    (h : ∀ α ∈ roots π, ∃ (n : WithConv (H →ₐ[k] k)) (σ : X ≃* X), IsNormalizingWith π k n σ ∧
      n ∈ attractorSubgroup π (lineMagnet α) k ∧ σ ≠ 1) :
    SplitReductiveData.WithReflections π where
  toSplitReductiveData := D
  exists_normalizing_refl α hα := by
    obtain ⟨n, σ, hn, hnα, hσ⟩ := h α hα
    exact ⟨toAlgClosure n, σ,
      IsNormalizingWith.mapValue π (Algebra.ofId k (AlgebraicClosure k)) hn,
      isReflectionOn_of_mem_lineAttractor D hα hn hnα hσ⟩

end AlgMag.Reductive
