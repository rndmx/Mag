/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Torsion.Hypotheses

/-!
# Non-vacuity of (R1), (R2): they hold for the rank-one root datum of type `A₁`

`M = ℤ`, `N = Dual ℤ ℤ`, roots `±1`, coroots `±2` (the root datum of `PGL₂`).
-/

namespace AlgMag.Torsion.A1

open Set RD

/-- Roots `±1`. -/
def rootE : Bool ↪ ℤ := ⟨fun b => if b then 1 else -1, by
  intro a b h; cases a <;> cases b <;> simp_all⟩

/-- Coroots `±2`. -/
def corootE : Bool ↪ Module.Dual ℤ ℤ := ⟨fun b => (if b then (2 : ℤ) else -2) • LinearMap.id, by
  intro a b h
  have := LinearMap.congr_fun h 1
  cases a <;> cases b <;> simp at this ⊢ <;> norm_num at this⟩

lemma corootE_apply (b : Bool) (m : ℤ) : corootE b m = (if b then 2 else -2) * m := by
  cases b <;> simp [corootE]

lemma rootE_apply (b : Bool) : rootE b = if b then 1 else -1 := rfl

/-- The root datum of type `A₁` (`PGL₂`). -/
noncomputable def P : RootPairing Bool ℤ ℤ (Module.Dual ℤ ℤ) :=
  RootPairing.mk' (Module.Dual.eval ℤ ℤ) rootE corootE
    (by intro i; cases i <;> simp [corootE_apply, rootE_apply])
    (by
      rintro i - ⟨j, rfl⟩
      refine ⟨!j, ?_⟩
      cases i <;> cases j <;> simp [Module.preReflection_apply, corootE_apply, rootE_apply] <;>
        norm_num)
    (by
      rintro i - ⟨j, rfl⟩
      refine ⟨!j, ?_⟩
      cases i <;> cases j <;> ext <;>
        simp [Module.preReflection_apply, corootE_apply, rootE_apply] <;> norm_num)

lemma P_root (b : Bool) : P.root b = if b then 1 else -1 := rfl

lemma P_coroot' (b : Bool) (m : ℤ) : P.coroot' b m = (if b then 2 else -2) * m := by
  change corootE b m = _
  exact corootE_apply b m

lemma P_reflection (b : Bool) : P.reflection b = LinearEquiv.neg ℤ := by
  ext m
  rw [RootPairing.reflection_apply, P_coroot', P_root]
  cases b <;> simp <;> ring

lemma root_val (b : Bool) : P.root b * P.root b = 1 := by cases b <;> simp [P_root]

/-- `W(Ψ) ⊆ {1, -1}`. -/
lemma mem_W {Ψ : Set ℤ} {w : ℤ ≃ₗ[ℤ] ℤ} (hw : w ∈ W P Ψ) : w = 1 ∨ w = LinearEquiv.neg ℤ := by
  induction hw using Subgroup.closure_induction with
  | mem x hx => obtain ⟨i, -, rfl⟩ := hx; exact Or.inr (P_reflection i)
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · simp
    · simp
    · simp
    · left; ext m; simp
  | inv x _ hx =>
    rcases hx with rfl | rfl
    · simp
    · right; ext m; simp [LinearEquiv.symm_apply_eq]

lemma neg_ne_one : (LinearEquiv.neg ℤ : ℤ ≃ₗ[ℤ] ℤ) ≠ 1 := by
  intro h; have := LinearEquiv.congr_fun h 1; simp at this

/-- If `-1 ∈ W(Ψ)` then some root lies in `Ψ`. -/
lemma exists_root {Ψ : Set ℤ} (hw : LinearEquiv.neg ℤ ∈ W P Ψ) : ∃ i, P.root i ∈ Ψ := by
  by_contra h
  push_neg at h
  have : refls P Ψ = ∅ := by
    ext v; simp only [refls, mem_setOf_eq, mem_empty_iff_false, iff_false]
    rintro ⟨i, hi, -⟩; exact h i hi
  rw [W, this, Subgroup.closure_empty, Subgroup.mem_bot] at hw
  exact neg_ne_one hw

lemma actPt_neg (x : ℤ →+ ℝ) (m : ℤ) : actPt (LinearEquiv.neg ℤ) x m = - x m := by
  simp [actPt]

lemma hom_apply (x : ℤ →+ ℝ) (m : ℤ) : x m = m * x 1 := by
  have := map_zsmul x m 1
  simpa [zsmul_eq_mul] using this

/-- (R1) holds for `A₁`. -/
theorem hypR1 : HypR1 P := by
  intro Ψ _ S w hw hS
  rcases mem_W hw with rfl | rfl
  · exact one_mem _
  · obtain ⟨i, hi⟩ := exists_root hw
    refine Subgroup.subset_closure ⟨i, hi, fun x hx => ?_, P_reflection i⟩
    have h := congrArg (fun f : ℤ →+ ℝ => f (P.root i)) (hS x hx)
    simp only [actPt_neg] at h
    linarith

/-- (R2) holds for `A₁`. -/
theorem hypR2 : HypR2 P := by
  intro Ψ _ x w hw t ht hfix
  rcases mem_W hw with rfl | rfl
  · refine ⟨[], by simp, ?_⟩
    have ht0 : t = 0 := by
      have : actPt 1 x = x := rfl
      rw [this] at hfix; simpa using hfix
    subst ht0
    funext y
    simp only [List.map_nil, List.foldr_nil, add_zero, id]
    rfl
  · obtain ⟨i, hi⟩ := exists_root hw
    -- values of `t` at `α_i` are even integers
    have heven' : ∀ s ∈ corootLattR P Ψ, ∃ n : ℤ, s (P.root i) = 2 * n := by
      intro s hs
      induction hs using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨j, -, rfl⟩ := hy
        refine ⟨if j then (if i then 1 else -1) else (if i then -1 else 1), ?_⟩
        simp only [corootR, AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
          P_coroot', P_root, Int.coe_castAddHom]
        cases i <;> cases j <;> norm_num
      | zero => exact ⟨0, by simp⟩
      | add a b _ _ ha hb =>
        obtain ⟨n, hn⟩ := ha; obtain ⟨n', hn'⟩ := hb
        exact ⟨n + n', by simp [hn, hn']; ring⟩
      | neg a _ ha =>
        obtain ⟨n, hn⟩ := ha; exact ⟨-n, by simp [hn]⟩
    obtain ⟨n, hn⟩ := heven' t ht
    have htx : ∀ m, t m = 2 * x m := by
      intro m
      have := congrArg (fun f : ℤ →+ ℝ => f m) hfix
      simp only [AddMonoidHom.add_apply, actPt_neg] at this
      linarith
    have hxn : x (P.root i) = n := by have := htx (P.root i); linarith
    refine ⟨[(i, n)], by simpa using ⟨hi, hxn⟩, ?_⟩
    funext y; apply AddMonoidHom.ext; intro m
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Function.comp_id,
      affRefl, AddMonoidHom.add_apply, AddMonoidHom.sub_apply, AddMonoidHom.smul_apply, actPt_neg,
      htx, corootR, AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
      Int.coe_castAddHom, P_coroot', smul_eq_mul]
    simp only [id_eq]
    rw [hom_apply x (P.root i)] at hxn
    rw [← hxn]
    rw [hom_apply x m, hom_apply y m, hom_apply y (P.root i), P_root]
    cases i <;> simp <;> ring

end AlgMag.Torsion.A1
