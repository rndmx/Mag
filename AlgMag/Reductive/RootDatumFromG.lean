/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.WeylPartReflections

/-!
# The root datum of `G` from its Weyl elements

`SplitReductiveData.WithRootDatum` takes a Mathlib root datum `P` as data. Here the root datum
is *constructed* from `G`: the only input beyond `SplitReductiveData` is, for each root `α`, a
`k̄`-point `n_α` of `N_G(T)` acting on `X` by a reflection at `α`
(`n_α t n_α⁻¹ = s_α(t)` with `s_α α = -α` and `(1 - s_α)X ⊆ ℤα`), and `X` finite free.

Lattice part (any finite group `G` acting on a torsion-free `M`):
* `coroot`: a reflection `w` at `α` (`(1 - w)M ⊆ ℤα`) has a unique `α^∨ : M →+ ℤ` with
  `w x = x - ⟨x, α^∨⟩ α`; `⟨α, α^∨⟩ = 2` when `w α = -α`.
* `coroot_unique`: in a *finite* group two reflections at `α` with `⟨α, ·⟩ = 2` have the same
  coroot (`w w'` is a transvection of finite order); `refl_unique`: hence they are equal when the
  action is faithful.
* `root_eq_of_coroot_eq`: a coroot determines its root.
* `smul_self_eq_neg`: in a finite group acting faithfully, a nontrivial reflection at `α` sends
  `α` to `-α` (so `s_α α = -α` need not be assumed).

Group part, for `D : SplitReductiveData.WithReflections π`:
* `mem_W_of_normalizing`: `s_α ∈ W` (from `normalizer_cover`);
* `rootPairing`: a root datum `RootPairing (roots π) ℤ X X^∨` with roots `Φ = roots π`
  (`range_root_rootPairing`) and coroots the `α^∨` above, built by `RootPairing.mk'`;
* `reflection_rootPairing`: the reflections of this root datum are the `s_α ∈ W`.
-/

open Set Function Module

namespace AlgMag.Reductive

/-! ### Reflections of a lattice -/

namespace LatticeReflection

variable {G M : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M]

/-- `w` acts on `M` as a reflection at `α`: `(1 - w)M ⊆ ℤα`. -/
def IsReflAt (w : G) (α : M) : Prop := ∀ x : M, x - w • x ∈ AddSubgroup.zmultiples α

lemma transvection_pow {u : G} {g : M →+ ℤ} {γ : M} (hu : ∀ x, u • x = x + g x • γ)
    (hg : g γ = 0) (n : ℕ) (x : M) : (u ^ n) • x = x + ((n : ℤ) * g x) • γ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_smul, ih, hu, map_add, map_zsmul, hg, smul_zero, add_zero]
    push_cast
    rw [add_mul, one_mul, add_smul]
    abel

variable [Module.IsTorsionFree ℤ M]

/-- A transvection `x ↦ x + g(x) γ` (`g γ = 0`) of finite order is trivial. -/
lemma transvection_trivial [Finite G] {u : G} {g : M →+ ℤ} {γ : M}
    (hu : ∀ x, u • x = x + g x • γ) (hg : g γ = 0) (x : M) : g x • γ = 0 := by
  obtain ⟨n, hn, hun⟩ := isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_finite u)
  have h := transvection_pow hu hg n x
  rw [hun, one_smul] at h
  have h0 : ((n : ℤ) * g x) • γ = 0 := (add_eq_left.mp h.symm)
  rw [mul_smul] at h0
  exact (smul_eq_zero_iff_right (by exact_mod_cast hn.ne')).mp h0

variable {w : G} {α : M}

/-- The integer `⟨x, α^∨⟩` with `x - w x = ⟨x, α^∨⟩ α`. -/
noncomputable def corootFun (h : IsReflAt w α) (x : M) : ℤ :=
  (AddSubgroup.mem_zmultiples_iff.mp (h x)).choose

omit [Module.IsTorsionFree ℤ M] in
lemma corootFun_spec (h : IsReflAt w α) (x : M) : corootFun h x • α = x - w • x :=
  (AddSubgroup.mem_zmultiples_iff.mp (h x)).choose_spec

/-- The coroot `α^∨ : M →+ ℤ` of a reflection `w` at `α ≠ 0`. -/
noncomputable def coroot (hα : α ≠ 0) (h : IsReflAt w α) : M →+ ℤ where
  toFun := corootFun h
  map_zero' := by
    have := corootFun_spec h 0
    rw [smul_zero, sub_zero] at this
    exact (smul_eq_zero_iff_left hα).mp this
  map_add' x y := by
    have : (corootFun h (x + y) - (corootFun h x + corootFun h y)) • α = 0 := by
      rw [sub_smul, add_smul, corootFun_spec, corootFun_spec, corootFun_spec, smul_add]
      abel
    exact sub_eq_zero.mp ((smul_eq_zero_iff_left hα).mp this)

/-- `w x = x - ⟨x, α^∨⟩ α`. -/
lemma smul_eq_sub_coroot (hα : α ≠ 0) (h : IsReflAt w α) (x : M) :
    w • x = x - coroot hα h x • α := by
  show w • x = x - corootFun h x • α
  rw [corootFun_spec]
  abel

/-- Uniqueness of the coroot of a given reflection. -/
lemma coroot_eq_of_smul_eq (hα : α ≠ 0) (h : IsReflAt w α) {f : M →+ ℤ}
    (hf : ∀ x, w • x = x - f x • α) : coroot hα h = f := by
  ext x
  have h1 := smul_eq_sub_coroot hα h x
  rw [hf x] at h1
  have : (f x - coroot hα h x) • α = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact sub_right_inj.mp h1
  exact (sub_eq_zero.mp ((smul_eq_zero_iff_left hα).mp this)).symm

/-- `⟨α, α^∨⟩ = 2` when `w α = -α`. -/
lemma coroot_self (hα : α ≠ 0) (h : IsReflAt w α) (hneg : w • α = -α) : coroot hα h α = 2 := by
  have h1 := corootFun_spec h α
  rw [hneg, sub_neg_eq_add] at h1
  have : (corootFun h α - 2) • α = 0 := by rw [sub_smul, h1, two_smul, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero_iff_left hα).mp this)

omit [Module.IsTorsionFree ℤ M] in
/-- The reflection form gives a reflection. -/
lemma isReflAt_of_smul_eq {f : M →+ ℤ} (hf : ∀ x, w • x = x - f x • α) : IsReflAt w α :=
  fun x => AddSubgroup.mem_zmultiples_iff.mpr ⟨f x, by rw [hf]; abel⟩

variable [Finite G]

/-- **`w α = -α` is automatic**: in a finite group acting faithfully, a nontrivial reflection
`w` at `α` (`(1 - w)M ⊆ ℤα`) sends `α` to `-α`. -/
theorem smul_self_eq_neg (hfaith : ∀ w w' : G, (∀ x : M, w • x = w' • x) → w = w') {w : G}
    {α : M} (hα : α ≠ 0) (h : IsReflAt w α) (hw : w ≠ 1) : w • α = -α := by
  have hs := smul_eq_sub_coroot hα h
  set f := coroot hα h
  have hwα : w • α = (1 - f α) • α := by rw [hs, sub_smul, one_smul]
  have hpow : ∀ n : ℕ, (w ^ n) • α = ((1 - f α) ^ n) • α := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_smul, ih]
      change DistribSMul.toAddMonoidHom M w (((1 - f α) ^ n) • α) = _
      rw [map_zsmul, DistribSMul.toAddMonoidHom_apply, hwα, smul_smul, pow_succ]
  obtain ⟨n, hn, hwn⟩ := isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_finite w)
  have h1 : (1 - f α) ^ n = 1 := by
    have h' := hpow n
    rw [hwn, one_smul] at h'
    have : ((1 - f α) ^ n - 1) • α = 0 := by rw [sub_smul, ← h', one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero_iff_left hα).mp this)
  have hab : (1 - f α).natAbs = 1 := by
    have := congrArg Int.natAbs h1
    rw [Int.natAbs_pow] at this
    exact (Nat.pow_eq_one.mp this).resolve_right hn.ne'
  rcases Int.natAbs_eq_iff.mp hab with h2 | h2
  · exfalso
    have hf0 : f α = 0 := by push_cast at h2; omega
    have hu : ∀ x, w • x = x + (-f) x • α := by
      intro x
      rw [hs, AddMonoidHom.neg_apply, neg_smul, sub_eq_add_neg]
    have hg : (-f) α = 0 := by simp [hf0]
    refine hw (hfaith w 1 fun x => ?_)
    rw [hu, transvection_trivial hu hg x, add_zero, one_smul]
  · rw [hwα, h2]
    simp

/-- **Uniqueness of coroots**: in a finite group, two reflections at `α` with
`⟨α, α^∨⟩ = 2` have the same coroot. -/
theorem coroot_unique {w w' : G} {f f' : M →+ ℤ} (hα : α ≠ 0)
    (hw : ∀ x, w • x = x - f x • α) (hw' : ∀ x, w' • x = x - f' x • α)
    (hf : f α = 2) (hf' : f' α = 2) : f = f' := by
  have hu : ∀ x, (w * w') • x = x + (f' - f) x • α := by
    intro x
    rw [mul_smul, hw', hw, map_sub, map_zsmul, hf, AddMonoidHom.sub_apply, smul_eq_mul]
    module
  have hg : (f' - f) α = 0 := by simp [hf, hf']
  ext x
  have := transvection_trivial hu hg x
  rw [smul_eq_zero_iff_left hα, AddMonoidHom.sub_apply, sub_eq_zero] at this
  exact this.symm

/-- In a finite group acting faithfully, the reflection at `α` is unique. -/
theorem refl_unique (hfaith : ∀ w w' : G, (∀ x : M, w • x = w' • x) → w = w') {w w' : G}
    {f f' : M →+ ℤ} (hα : α ≠ 0) (hw : ∀ x, w • x = x - f x • α)
    (hw' : ∀ x, w' • x = x - f' x • α) (hf : f α = 2) (hf' : f' α = 2) : w = w' := by
  have := coroot_unique hα hw hw' hf hf'
  subst this
  exact hfaith w w' fun x => by rw [hw, hw']

/-- A coroot determines its root. -/
theorem root_eq_of_coroot_eq {w w' : G} {α β : M} {f : M →+ ℤ}
    (hw : ∀ x, w • x = x - f x • α) (hw' : ∀ x, w' • x = x - f x • β)
    (hfα : f α = 2) (hfβ : f β = 2) : α = β := by
  have hu : ∀ x, (w * w') • x = x + f x • (α - β) := by
    intro x
    rw [mul_smul, hw', hw, map_sub, map_zsmul, hfβ, smul_eq_mul]
    module
  have hg : f (α - β) = 0 := by simp [hfα, hfβ]
  have := transvection_trivial hu hg α
  rw [hfα, smul_eq_zero_iff_right two_ne_zero, sub_eq_zero] at this
  exact this

end LatticeReflection

end AlgMag.Reductive
