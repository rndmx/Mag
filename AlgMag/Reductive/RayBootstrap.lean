/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.RankOneDim
import AlgMag.Weyl.Normalizer

/-!
# Bootstrap: T4 on a ray gives `hRay`

`hRay_of_T4`: if every ray carries root-space dimension `≤ 1` (`rayDim ≤ 1`, the T4 conclusion
`hT4`), `α` and `-α` are roots, and `f α > 0`, then every root proportional to `α` is `±α`, in
particular lies in `ℤα`. This is the `hRay` input of `connectedSpace_lineAttractor`.

Plan (lean-forward.md, round 14): R1 for the primitive generator `δ₀` of `ℚα ∩ X` (`hRay`
automatic) gives a Weyl point of `G^{ℤδ₀}`; that point feeds the T4/Bruhat route for the ray of
`δ₀`, giving `rayDim ≤ 1` there; `hRay_of_T4` then gives `hRay` for every root `α` on the ray.
-/

open Magnetism TauCeti WithConv AlgMag.Weyl

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X) [Module.Finite k (Bialgebra.CotangentSpace k H)]

open scoped Classical in
/-- Two `g`-positive roots on one ray are equal when the ray has dimension `≤ 1`. -/
lemma eq_of_rayDim_le_one {g : Additive X →+ ℤ} {β γ : Additive X}
    (hβ : β ∈ posRoots π g) (hγ : γ ∈ posRoots π g) (hr : SameRayRel β γ)
    (h1 : rayDim π g γ ≤ 1) : β = γ := by
  by_contra hne
  have hsub : ({β, γ} : Finset (Additive X)) ⊆
      (posRoots π g).filter (fun δ => SameRayRel δ γ) := by
    intro δ hδ
    rw [Finset.mem_insert, Finset.mem_singleton] at hδ
    rcases hδ with rfl | rfl
    · exact Finset.mem_filter.2 ⟨hβ, hr⟩
    · exact Finset.mem_filter.2 ⟨hγ, sameRayRel_equivalence.refl _⟩
  have hle := Finset.sum_le_sum_of_subset (f := fun δ =>
    Module.finrank k (Derivation.adjointWeightSpace π (Additive.toMul δ))) hsub
  rw [Finset.sum_pair hne] at hle
  have hβr : β ∈ roots π := by
    simp only [posRoots, Finset.mem_filter, Set.Finite.mem_toFinset] at hβ; exact hβ.1
  have hγr : γ ∈ roots π := by
    simp only [posRoots, Finset.mem_filter, Set.Finite.mem_toFinset] at hγ; exact hγ.1
  have := finrank_pos_of_mem_roots π hβr
  have := finrank_pos_of_mem_roots π hγr
  unfold rayDim at h1
  omega

lemma mem_posRoots {g : Additive X →+ ℤ} {β : Additive X} (hβ : β ∈ roots π) (h : 0 < g β) :
    β ∈ posRoots π g := by
  simp only [posRoots, Finset.mem_filter, Set.Finite.mem_toFinset]; exact ⟨hβ, h⟩

/-- **`hRay` from T4.** -/
theorem hRay_of_T4 [Module.IsTorsionFree ℤ (Additive X)] {α : Additive X} (f : Additive X →+ ℤ)
    (hα : α ∈ roots π) (hneg : -α ∈ roots π) (hfα : 0 < f α)
    (hT4 : ∀ (g : Additive X →+ ℤ), ∀ γ ∈ posRoots π g, rayDim π g γ ≤ 1) :
    ∀ β ∈ roots π, (∃ m n : ℤ, n ≠ 0 ∧ n • β = m • α) → β ∈ lineMagnet α := by
  rintro β hβ ⟨m, n, hn, h⟩
  have hβ0 := ne_zero_of_mem_roots hβ
  have hm : m ≠ 0 := by
    rintro rfl
    rw [zero_smul] at h
    exact hβ0 ((smul_eq_zero_iff_right hn).mp h)
  rcases lt_or_gt_of_ne (mul_ne_zero hn hm) with hmn | hmn
  · -- `β` on the ray of `-α`
    have h' : n • β = (-m) • (-α) := by rw [neg_smul, smul_neg, neg_neg, h]
    have hr := sameRay_of_zsmul h' (by nlinarith)
    have hα' : -α ∈ posRoots π (-f) := mem_posRoots π hneg (by simp [hfα])
    have hβ' : β ∈ posRoots π (-f) :=
      mem_posRoots π hβ (pos_of_sameRay (sameRayRel_equivalence.symm hr) (by simp [hfα]))
    rw [eq_of_rayDim_le_one π hβ' hα' hr (hT4 _ _ hα')]
    exact ⟨-1, by simp⟩
  · have hr := sameRay_of_zsmul h hmn
    have hα' : α ∈ posRoots π f := mem_posRoots π hα hfα
    have hβ' : β ∈ posRoots π f :=
      mem_posRoots π hβ (pos_of_sameRay (sameRayRel_equivalence.symm hr) hfα)
    rw [eq_of_rayDim_le_one π hβ' hα' hr (hT4 _ _ hα')]
    exact ⟨1, by simp⟩

/-! ### `σδ₀ = -δ₀` from `σ ≠ 1`, finite order and `(1 - σ)X ⊆ ℤδ₀` -/

section SigmaNeg

variable {X' : Type u} [CommGroup X']

lemma mulAut_pow_apply (σ : X' ≃* X') (n : ℕ) (x : X') : (σ ^ n) x = σ^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [pow_succ', MulAut.mul_apply, ih, Function.iterate_succ_apply']

/-- `σ` as an additive endomorphism. -/
abbrev sAdd (σ : X' ≃* X') : Additive X' →+ Additive X' := σ.toMonoidHom.toAdditive

lemma sAdd_iterate (σ : X' ≃* X') (n : ℕ) (χ : Additive X') :
    (sAdd σ)^[n] χ = Additive.ofMul ((σ ^ n) (Additive.toMul χ)) := by
  rw [mulAut_pow_apply]
  induction n generalizing χ with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']; rfl

/-- **`σδ = -δ`.** -/
theorem sAdd_eq_neg [Module.IsTorsionFree ℤ (Additive X')] (σ : X' ≃* X') {δ : Additive X'}
    (hδ : δ ≠ 0) (hσ : σ ≠ 1) (hfin : IsOfFinOrder σ)
    (hline : ∀ χ : Additive X', ∃ c : ℤ, χ - sAdd σ χ = c • δ) : sAdd σ δ = -δ := by
  obtain ⟨n, hn, hpow⟩ := (isOfFinOrder_iff_pow_eq_one).1 hfin
  have hfix : ∀ χ, (sAdd σ)^[n] χ = χ := fun χ => by rw [sAdd_iterate, hpow]; rfl
  obtain ⟨c, hc⟩ := hline δ
  set a : ℤ := 1 - c
  have hsδ : sAdd σ δ = a • δ := by
    have : sAdd σ δ = δ - c • δ := by rw [← hc]; abel
    rw [this, sub_smul, one_smul]
  have hit : ∀ m : ℕ, (sAdd σ)^[m] δ = a ^ m • δ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Function.iterate_succ_apply', ih, map_zsmul, hsδ, smul_smul, pow_succ]
  have han : a ^ n = 1 := by
    have h := hfix δ
    rw [hit] at h
    have h2 : (a ^ n - 1) • δ = 0 := by rw [sub_smul, one_smul, h, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero_iff_left hδ).1 h2)
  have ha : a = 1 ∨ a = -1 := by
    have h1 : a.natAbs = 1 := by
      have := congrArg Int.natAbs han
      rw [Int.natAbs_pow] at this
      rcases pow_eq_one_iff.1 this with h | h
      · exact h
      · omega
    simpa using Int.natAbs_eq_iff.1 h1
  rcases ha with ha | ha
  · exfalso
    apply hσ
    have hsδ' : sAdd σ δ = δ := by rw [hsδ, ha, one_smul]
    ext x
    obtain ⟨cx, hcx⟩ := hline (Additive.ofMul x)
    have hs : sAdd σ (Additive.ofMul x) = Additive.ofMul x - cx • δ := by rw [← hcx]; abel
    have hitx : ∀ m : ℕ, (sAdd σ)^[m] (Additive.ofMul x) =
        Additive.ofMul x - ((m : ℤ) * cx) • δ := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Function.iterate_succ_apply', ih, map_sub, hs, map_zsmul, hsδ']
        push_cast; rw [add_mul, one_mul, add_smul]; abel
    have h := hfix (Additive.ofMul x)
    rw [hitx] at h
    have h2 : ((n : ℤ) * cx) • δ = 0 := by
      have := congrArg (fun y => Additive.ofMul x - y) h
      simpa using this
    have hcx0 : cx = 0 := by
      have := (smul_eq_zero_iff_left hδ).1 h2
      rcases mul_eq_zero.1 this with h | h
      · omega
      · exact h
    have : sAdd σ (Additive.ofMul x) = Additive.ofMul x := by rw [hs, hcx0, zero_smul, sub_zero]
    exact congrArg Additive.toMul this
  · rw [hsδ, ha, neg_one_smul]

end SigmaNeg

/-- **`-α ∈ Φ` from a nontrivial Weyl point of `G^{ℤδ}`** (`α ∈ ℤδ` a root, `δ ≠ 0`). -/
theorem neg_mem_roots_of_r1 [Module.IsTorsionFree ℤ (Additive X)] (hπ : Function.Surjective π)
    {n : WithConv (H →ₐ[k] k)} {σ : X ≃* X} (hn : IsNormalizingWith π k n σ)
    {δ : Additive X} (hδ : δ ≠ 0) (hmem : n ∈ attractorSubgroup π (lineMagnet δ) k)
    (hσ : σ ≠ 1) (hfin : IsOfFinOrder σ) {α : Additive X} (hα : α ∈ roots π)
    (hαδ : α ∈ lineMagnet δ) : -α ∈ roots π := by
  have hle := (mem_attractorSubgroup_iff_weylMagnet_le π hπ hn _).1 hmem
  have hline : ∀ χ : Additive X, ∃ c : ℤ, χ - sAdd σ χ = c • δ := by
    intro χ
    obtain ⟨c, hc⟩ := hle (AddSubmonoid.subset_closure ⟨χ, rfl⟩)
    exact ⟨c, hc.symm⟩
  have hs := sAdd_eq_neg σ hδ hσ hfin hline
  obtain ⟨m, rfl⟩ := hαδ
  have h := mem_roots_of_isNormalizingWith π hn hα
  have : Additive.ofMul (σ (Additive.toMul (m • δ))) = -(m • δ) := by
    change sAdd σ (m • δ) = _
    rw [map_zsmul, hs, smul_neg]
  rwa [this] at h

/-- **The bootstrap, assembled.** A nontrivial Weyl point of `G^{ℤδ}` (R1 for the ray generator
`δ`; `σ` of finite order) and T4 (`hT4`) give `hRay` for every root `α ∈ ℤδ`. -/
theorem hRay_of_bootstrap [Module.IsTorsionFree ℤ (Additive X)] (hπ : Function.Surjective π)
    {n : WithConv (H →ₐ[k] k)} {σ : X ≃* X} (hn : IsNormalizingWith π k n σ)
    {δ : Additive X} (hδ : δ ≠ 0) (hmem : n ∈ attractorSubgroup π (lineMagnet δ) k)
    (hσ : σ ≠ 1) (hfin : IsOfFinOrder σ) {α : Additive X} (hα : α ∈ roots π)
    (hαδ : α ∈ lineMagnet δ) (f : Additive X →+ ℤ) (hfα : 0 < f α)
    (hT4 : ∀ (g : Additive X →+ ℤ), ∀ γ ∈ posRoots π g, rayDim π g γ ≤ 1) :
    ∀ β ∈ roots π, (∃ m n : ℤ, n ≠ 0 ∧ n • β = m • α) → β ∈ lineMagnet α :=
  hRay_of_T4 π f hα (neg_mem_roots_of_r1 π hπ hn hδ hmem hσ hfin hα hαδ) hfα hT4

end AlgMag.Reductive
