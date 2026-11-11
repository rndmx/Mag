/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Torsion.Prop41Full
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Lemma 3.1 (saturated subgroups), from **(R1)**

For `Z ⊆ M` a subgroup with `M/Z` torsion-free (`hZ`), `M` free of finite rank, a subsystem `Ψ`,
and `v ∈ W(Ψ)`: `(1 - v)M ⊆ Z ↔ v ∈ W(Ψ ∩ Z)`. That is `W(Ψ) ∩ W_Z = W(Ψ ∩ Z)`, where
`W_Z = {v | (1 - v)M ⊆ Z}`. The easy inclusion `sub_mem_of_mem_W_inter` needs nothing.
-/

namespace AlgMag.Torsion

open Set RD

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] {P : RootPairing ι ℤ M N}

namespace RD

/-- Easy direction (no hypothesis): `W(Ψ ∩ Z)` consists of elements with `(1 - v)M ⊆ Z`. -/
lemma sub_mem_of_mem_W_inter {Ψ : Set M} (Z : AddSubgroup M) {v : M ≃ₗ[ℤ] M}
    (hv : v ∈ W P (Ψ ∩ (Z : Set M))) : ∀ m, m - v m ∈ Z := by
  induction hv using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨i, hi, rfl⟩ := hw
    intro m
    rw [RootPairing.reflection_apply, sub_sub_cancel]
    exact Z.zsmul_mem hi.2 _
  | one => intro m; simp
  | mul u w _ _ hu hw =>
    intro m
    have h1 := hu m
    have h2 := hw m
    have h3 : u (m - w m) ∈ Z := by
      have := Z.sub_mem h2 (hu (m - w m))
      simpa using this
    have := Z.add_mem h1 h3
    rw [LinearEquiv.mul_apply]
    convert this using 1
    rw [map_sub]; abel
  | inv w _ hw =>
    intro m
    have := Z.neg_mem (hw (w⁻¹ m))
    rw [neg_sub] at this
    convert this using 2
    show m = w (w.symm m)
    simp

/-- Separation by integer-valued points for a saturated subgroup of a free module. -/
lemma exists_pt_of_not_mem [Module.Free ℤ M] [Module.Finite ℤ M] (Z : AddSubgroup M)
    (hZ : ∀ (m : M) (n : ℤ), n ≠ 0 → n • m ∈ Z → m ∈ Z) {m : M} (hm : m ∉ Z) :
    ∃ y : M →+ ℝ, (∀ z ∈ Z, y z = 0) ∧ y m ≠ 0 := by
  haveI : NoZeroSMulDivisors ℤ (M ⧸ Z) := by
    refine ⟨fun {n q} h => ?_⟩
    induction q using QuotientAddGroup.induction_on with
    | H m =>
      by_cases hn : n = 0
      · exact Or.inl hn
      · right
        have : n • m ∈ Z := by
          rw [← QuotientAddGroup.eq_zero_iff]
          exact h
        exact (QuotientAddGroup.eq_zero_iff m).2 (hZ m n hn this)
  haveI : Module.Finite ℤ (M ⧸ Z) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' Z).toIntLinearMap
      QuotientAddGroup.mk_surjective
  haveI : Module.Free ℤ (M ⧸ Z) := Module.free_of_finite_type_torsion_free'
  have hne : (QuotientAddGroup.mk m : M ⧸ Z) ≠ 0 := fun h =>
    hm ((QuotientAddGroup.eq_zero_iff m).1 h)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℤ (M ⧸ Z), φ (QuotientAddGroup.mk m) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne ((Module.forall_dual_apply_eq_zero_iff ℤ _).1 hcon)
  refine ⟨(Int.castAddHom ℝ).comp (φ.toAddMonoidHom.comp (QuotientAddGroup.mk' Z)), ?_, ?_⟩
  · intro z hz
    have : (QuotientAddGroup.mk z : M ⧸ Z) = 0 := (QuotientAddGroup.eq_zero_iff z).2 hz
    simp [this]
  · simpa using hφ

/-- **Lemma 3.1.** -/
theorem lemma31 [Module.Free ℤ M] [Module.Finite ℤ M] (hR1 : HypR1 P) {Ψ : Set M}
    (hΨ : IsSubsystem P Ψ) (Z : AddSubgroup M)
    (hZ : ∀ (m : M) (n : ℤ), n ≠ 0 → n • m ∈ Z → m ∈ Z) {v : M ≃ₗ[ℤ] M} (hv : v ∈ W P Ψ) :
    (∀ m, m - v m ∈ Z) ↔ v ∈ W P (Ψ ∩ (Z : Set M)) := by
  refine ⟨fun h => ?_, sub_mem_of_mem_W_inter Z⟩
  let E : Set (M →+ ℝ) := {y | ∀ z ∈ Z, y z = 0}
  have hfix : ∀ y ∈ E, actPt v y = y := by
    intro y hy
    ext m
    have h1 := hy _ (h (v.symm m))
    rw [map_sub] at h1
    have : y (v.symm m) = y m := by
      have e : v (v.symm m) = m := v.apply_symm_apply m
      rw [e] at h1
      linarith
    exact this
  have := hR1 Ψ hΨ E v hv hfix
  refine (Subgroup.closure_mono ?_) this
  rintro w ⟨i, hi, hE, rfl⟩
  refine ⟨i, ⟨hi, ?_⟩, rfl⟩
  by_contra hnot
  obtain ⟨y, hy, hy2⟩ := exists_pt_of_not_mem Z hZ hnot
  exact hy2 (hE y hy)

end RD

end AlgMag.Torsion
