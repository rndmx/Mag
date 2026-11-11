/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Torsion.Hypotheses

/-!
# Lemma 3.2 of `notes/torsion-converse.md` (the homomorphism `θ_x`)

Points `x ∈ M^∨ ⊗ ℝ` are `M →+ ℝ`; `M^∨` is the subgroup `intPts` of integer-valued points;
`ℤΨ^∨ = corootLattR P Ψ`; `M_x = {m | ⟨m, x⟩ ∈ ℤ}`.

* `sub_actPt_mem` (Lemma 1.2(a), dual form): `μ - vμ ∈ ℤΨ^∨` for `v ∈ W(Ψ)`, `μ ∈ M^∨`.
* `mem_U_iff` (3.2(a)): `(1-v)M ⊆ M_x ↔ x - vx ∈ M^∨`.
* `theta_mul` (3.2(a)): `θ_x(uv) ≡ θ_x(u) + θ_x(v)` mod `ℤΨ^∨`.
* `theta_refl` (3.2(b)), `mem_W_of_theta` (3.2(c), uses **(R2)**), `nsmul_theta` (3.2(d)).
-/

namespace AlgMag.Torsion

open Set RD

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] (P : RootPairing ι ℤ M N)

namespace RD

/-- `M^∨ ⊆ M^∨ ⊗ ℝ`: integer-valued points. -/
def intPts : AddSubgroup (M →+ ℝ) where
  carrier := {y | ∀ m, ∃ k : ℤ, y m = k}
  zero_mem' := fun m => ⟨0, by simp⟩
  add_mem' := by
    intro a b ha hb m
    obtain ⟨k, hk⟩ := ha m; obtain ⟨k', hk'⟩ := hb m
    exact ⟨k + k', by simp [hk, hk']⟩
  neg_mem' := by
    intro a ha m
    obtain ⟨k, hk⟩ := ha m
    exact ⟨-k, by simp [hk]⟩

/-- `M_x = {m | ⟨m,x⟩ ∈ ℤ}`. -/
def Mx (x : M →+ ℝ) : Set M := {m | ∃ k : ℤ, x m = k}

variable {P}

lemma actPt_mul (u v : M ≃ₗ[ℤ] M) (y : M →+ ℝ) : actPt (u * v) y = actPt u (actPt v y) := rfl

lemma actPt_one (y : M →+ ℝ) : actPt (1 : M ≃ₗ[ℤ] M) y = y := rfl

lemma actPt_add (v : M ≃ₗ[ℤ] M) (y z : M →+ ℝ) : actPt v (y + z) = actPt v y + actPt v z := rfl

lemma actPt_sub (v : M ≃ₗ[ℤ] M) (y z : M →+ ℝ) : actPt v (y - z) = actPt v y - actPt v z := rfl

lemma actPt_zsmul (v : M ≃ₗ[ℤ] M) (n : ℤ) (y : M →+ ℝ) : actPt v (n • y) = n • actPt v y := rfl

lemma actPt_rsmul (v : M ≃ₗ[ℤ] M) (r : ℝ) (y : M →+ ℝ) : actPt v (r • y) = r • actPt v y := rfl

lemma actPt_inv (v : M ≃ₗ[ℤ] M) (y : M →+ ℝ) : actPt v (actPt v⁻¹ y) = y := by
  rw [← actPt_mul, mul_inv_cancel, actPt_one]

lemma reflection_symm (i : ι) : (P.reflection i).symm = P.reflection i := by
  first
  | exact P.reflection_symm i
  | (ext m; rw [LinearEquiv.symm_apply_eq]; simp)

lemma W_mono {Ψ Ψ' : Set M} (h : Ψ ⊆ Ψ') : W P Ψ ≤ W P Ψ' :=
  Subgroup.closure_mono fun _ hw => by
    obtain ⟨i, hi, e⟩ := hw
    exact ⟨i, h hi, e⟩

/-- `s_α y = y - ⟨α, y⟩ α^∨`. -/
lemma actPt_reflection (i : ι) (y : M →+ ℝ) :
    actPt (P.reflection i) y = y - y (P.root i) • corootR P i := by
  ext m
  simp only [actPt, reflection_symm, AddMonoidHom.coe_comp, Function.comp_apply,
    LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe, RootPairing.reflection_apply,
    AddMonoidHom.sub_apply, AddMonoidHom.smul_apply, corootR, Int.coe_castAddHom, smul_eq_mul,
    map_sub, map_zsmul, zsmul_eq_mul]
  ring

lemma corootR_mem {Ψ : Set M} {i : ι} (hi : P.root i ∈ Ψ) : corootR P i ∈ corootLattR P Ψ :=
  AddSubgroup.subset_closure ⟨i, hi, rfl⟩

lemma actPt_intPts (v : M ≃ₗ[ℤ] M) {μ : M →+ ℝ} (hμ : μ ∈ intPts) : actPt v μ ∈ intPts :=
  fun m => hμ _

/-- Lemma 1.2(a), dual form: `vμ - μ ∈ ℤΨ^∨` for `v ∈ W(Ψ)`, `μ ∈ M^∨`. -/
lemma actPt_sub_mem {Ψ : Set M} {v : M ≃ₗ[ℤ] M} (hv : v ∈ W P Ψ) :
    ∀ μ ∈ (intPts : AddSubgroup (M →+ ℝ)), actPt v μ - μ ∈ corootLattR P Ψ := by
  induction hv using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨i, hi, rfl⟩ := hw
    intro μ hμ
    obtain ⟨k, hk⟩ := hμ (P.root i)
    rw [actPt_reflection, hk, sub_sub_cancel_left, ← neg_smul]
    have : (-(k : ℝ)) • corootR P i = (-k) • corootR P i := by
      ext m; simp [zsmul_eq_mul]
    rw [this]
    exact zsmul_mem (corootR_mem hi) _
  | one => intro μ _; simp [actPt_one]
  | mul u w _ _ hu hw =>
    intro μ hμ
    have := add_mem (hu _ (actPt_intPts w hμ)) (hw μ hμ)
    show actPt u (actPt w μ) - μ ∈ _
    rwa [sub_add_sub_cancel] at this
  | inv w _ hw =>
    intro μ hμ
    have := neg_mem (hw _ (actPt_intPts w⁻¹ hμ))
    rwa [actPt_inv, neg_sub] at this

/-- `ℤΨ^∨ ⊆ M^∨`. -/
lemma corootLattR_le {Ψ : Set M} : corootLattR P Ψ ≤ intPts := by
  rw [corootLattR, AddSubgroup.closure_le]
  rintro _ ⟨i, -, rfl⟩ m
  exact ⟨P.coroot' i m, rfl⟩

/-- Lemma 3.2(a), first part: `(1-v)M ⊆ M_x ↔ x - vx ∈ M^∨`. -/
lemma mem_U_iff (x : M →+ ℝ) (v : M ≃ₗ[ℤ] M) :
    (∀ m, m - v m ∈ Mx x) ↔ x - actPt v x ∈ (intPts : AddSubgroup (M →+ ℝ)) := by
  constructor
  · intro h m
    obtain ⟨k, hk⟩ := h (v.symm m)
    refine ⟨-k, ?_⟩
    simp [actPt, Mx] at hk ⊢
    push_cast; linarith
  · intro h m
    obtain ⟨k, hk⟩ := h (v m)
    refine ⟨-k, ?_⟩
    simp [actPt, Mx] at hk ⊢
    push_cast; linarith

/-- Lemma 3.2(a), second part: `θ_x(uv) = θ_x(u) + θ_x(v)` modulo `ℤΨ^∨`. -/
lemma theta_mul {Ψ : Set M} (x : M →+ ℝ) {u v : M ≃ₗ[ℤ] M} (hu : u ∈ W P Ψ)
    (hv : x - actPt v x ∈ (intPts : AddSubgroup (M →+ ℝ))) :
    (x - actPt (u * v) x) - ((x - actPt u x) + (x - actPt v x)) ∈ corootLattR P Ψ := by
  have := actPt_sub_mem hu _ hv
  have e : (x - actPt (u * v) x) - ((x - actPt u x) + (x - actPt v x)) =
      actPt u (x - actPt v x) - (x - actPt v x) := by
    rw [actPt_sub, actPt_mul]; abel
  rwa [e]

/-- Lemma 3.2(b): `θ_x(s_α) = 0` for `α ∈ Ψ ∩ M_x`. -/
lemma theta_refl {Ψ : Set M} (x : M →+ ℝ) {i : ι} (hi : P.root i ∈ Ψ) (hx : P.root i ∈ Mx x) :
    x - actPt (P.reflection i) x ∈ corootLattR P Ψ := by
  obtain ⟨k, hk⟩ := hx
  rw [actPt_reflection, sub_sub_cancel, hk]
  have : (k : ℝ) • corootR P i = k • corootR P i := by ext m; simp [zsmul_eq_mul]
  rw [this]; exact zsmul_mem (corootR_mem hi) _

/-- Lemma 3.2(b), group form: `W(Ψ ∩ M_x) ⊆ ker θ_x`. -/
lemma theta_of_mem {Ψ : Set M} (x : M →+ ℝ) {v : M ≃ₗ[ℤ] M} (hv : v ∈ W P (Ψ ∩ Mx x)) :
    x - actPt v x ∈ corootLattR P Ψ := by
  induction hv using Subgroup.closure_induction with
  | mem w hw => obtain ⟨i, hi, rfl⟩ := hw; exact theta_refl x hi.1 hi.2
  | one => simp [actPt_one]
  | mul u w hu' _ hu hw =>
    have hu'' : u ∈ W P Ψ := W_mono inter_subset_left hu'
    have := add_mem (theta_mul x hu'' (corootLattR_le hw)) (add_mem hu hw)
    simpa using this
  | inv w hw' hw =>
    have hw'' : w ∈ W P Ψ := W_mono inter_subset_left hw'
    have h1 := actPt_sub_mem (inv_mem hw'') _ (corootLattR_le hw)
    have e : x - actPt w⁻¹ x = -(actPt w⁻¹ (x - actPt w x) - (x - actPt w x)) - (x - actPt w x) := by
      rw [actPt_sub, ← actPt_mul, inv_mul_cancel, actPt_one]; abel
    rw [e]
    exact sub_mem (neg_mem h1) hw

/-- Lemma 3.2(d): if `n x ∈ M^∨` then `n θ_x(v) = 0`. -/
lemma nsmul_theta {Ψ : Set M} (x : M →+ ℝ) {v : M ≃ₗ[ℤ] M} (hv : v ∈ W P Ψ) {n : ℤ}
    (hn : n • x ∈ (intPts : AddSubgroup (M →+ ℝ))) :
    n • (x - actPt v x) ∈ corootLattR P Ψ := by
  have := neg_mem (actPt_sub_mem hv _ hn)
  rw [smul_sub]
  rwa [neg_sub, actPt_zsmul] at this

/-- `s_{α,k} = s_α + k α^∨`. -/
lemma affRefl_eq (i : ι) (k : ℤ) (y : M →+ ℝ) :
    affRefl P i k y = actPt (P.reflection i) y + (k : ℝ) • corootR P i := by
  rw [actPt_reflection, affRefl, sub_smul]; abel

/-- A composite of affine reflections is affine with linear part the product of reflections. -/
lemma foldr_affRefl (l : List (ι × ℤ)) : ∃ c : M →+ ℝ, ∀ y,
    (l.map fun q => affRefl P q.1 q.2).foldr (· ∘ ·) id y =
      actPt (l.map fun q => P.reflection q.1).prod y + c := by
  induction l with
  | nil => exact ⟨0, fun y => by simp [actPt_one]⟩
  | cons q l ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨actPt (P.reflection q.1) c + (q.2 : ℝ) • corootR P q.1, fun y => ?_⟩
    simp only [List.map_cons, List.foldr_cons, Function.comp_apply, List.prod_cons, hc,
      affRefl_eq, actPt_add, actPt_mul]
    abel

end RD

open RD

/-- Lemma 3.2(c), from **(R2)**: `ker θ_x ⊆ W(Ψ ∩ M_x)`, provided the action of `W` on
`M^∨ ⊗ ℝ` is faithful (`hfaith`, automatic for `M` free of finite rank: `faithful_of_free`). -/
lemma mem_W_of_theta (hR2 : HypR2 P)
    (hfaith : ∀ u v : M ≃ₗ[ℤ] M, (∀ y, actPt u y = actPt v y) → u = v)
    {Ψ : Set M} (hΨ : IsSubsystem P Ψ) (x : M →+ ℝ) {v : M ≃ₗ[ℤ] M} (hv : v ∈ W P Ψ)
    (hker : x - actPt v x ∈ corootLattR P Ψ) : v ∈ W P (Ψ ∩ Mx x) := by
  obtain ⟨l, hl, hg⟩ := hR2 Ψ hΨ x v hv _ hker (by abel)
  obtain ⟨c, hc⟩ := foldr_affRefl (P := P) l
  have h0 := congrFun hg 0
  simp only [hc, show actPt v 0 = 0 from rfl, show ∀ w : M ≃ₗ[ℤ] M, actPt w 0 = 0 from fun _ => rfl,
    zero_add] at h0
  have hv' : v = (l.map fun q => P.reflection q.1).prod := by
    apply hfaith
    intro y
    have := congrFun hg y
    rw [hc, ← h0] at this
    exact add_right_cancel this
  rw [hv']
  refine (W P (Ψ ∩ Mx x)).list_prod_mem ?_
  intro w hw
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hw
  exact Subgroup.subset_closure ⟨q.1, ⟨(hl q hq).1, q.2, (hl q hq).2⟩, rfl⟩

/-- Faithfulness for `M` free of finite rank. -/
lemma faithful_of_free [Module.Free ℤ M] [Module.Finite ℤ M] :
    ∀ u v : M ≃ₗ[ℤ] M, (∀ y, actPt u y = actPt v y) → u = v := by
  intro u v h
  have key : ∀ m : M, (∀ y : M →+ ℝ, y m = 0) → m = 0 := by
    intro m hm
    rw [← Module.forall_dual_apply_eq_zero_iff ℤ m]
    intro φ
    have := hm ((Int.castAddHom ℝ).comp φ.toAddMonoidHom)
    simpa using this
  have hs : u.symm = v.symm := by
    ext m
    rw [← sub_eq_zero]
    apply key
    intro y
    have := congrArg (fun f : M →+ ℝ => f m) (h y)
    simp only [actPt, AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
      LinearEquiv.coe_coe] at this
    simp [this]
  simpa using congrArg LinearEquiv.symm hs

end AlgMag.Torsion
