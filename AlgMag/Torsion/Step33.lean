/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Torsion.Lemma31

/-!
# The inductive step of Prop 3.3 (one character, prime `p`)

`WZ Z = W_Z = {v | (1-v)M ⊆ Z}` (Lemma 1.2(a): a subgroup). `step33`: for `Z ⊆ Y`, `x` with
`p x ∈ M^∨` and `Y ∩ M_x = Z`, and `u ∈ W(Φ ∩ Y) ∩ W_Z`: `u^p ∈ W(Φ ∩ Z)`, and `u ∈ W(Φ ∩ Z)` as
soon as `x - u x ∈ ℤ(Φ∩Y)^∨`. Uses (R2) (via Lemma 3.2(c)).
-/

namespace AlgMag.Torsion

open Set RD

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] {P : RootPairing ι ℤ M N}

namespace RD

/-- `W_Z = {v ∈ Aut M | (1 - v) M ⊆ Z}`. -/
def WZ (Z : AddSubgroup M) : Subgroup (M ≃ₗ[ℤ] M) where
  carrier := {v | ∀ m, m - v m ∈ Z}
  one_mem' := fun m => by simp
  mul_mem' := by
    intro u v hu hv m
    have h3 : u (m - v m) ∈ Z := by
      have := Z.sub_mem (hv m) (hu (m - v m))
      simpa using this
    have := Z.add_mem (hu m) h3
    rw [LinearEquiv.mul_apply]
    convert this using 1
    rw [map_sub]; abel
  inv_mem' := by
    intro v hv m
    have := Z.neg_mem (hv (v⁻¹ m))
    rw [neg_sub] at this
    convert this using 2
    show m = v (v⁻¹ m)
    simp

lemma mem_WZ {Z : AddSubgroup M} {v : M ≃ₗ[ℤ] M} : v ∈ WZ Z ↔ ∀ m, m - v m ∈ Z := Iff.rfl

lemma isSubsystem_inter (Z : AddSubgroup M) : IsSubsystem P (range P.root ∩ (Z : Set M)) := by
  refine ⟨inter_subset_left, ?_⟩
  rintro i j ⟨-, hi⟩ ⟨⟨k, hk⟩, hj⟩
  have hj' : P.root j ∈ (Z : Set M) := hj
  refine ⟨⟨P.reflectionPerm i k, ?_⟩, ?_⟩
  · rw [P.root_reflectionPerm i k, hk]
  · rw [RootPairing.reflection_apply]
    exact Z.sub_mem hj' (Z.zsmul_mem hi _)

lemma pow_theta {Ψ : Set M} (x : M →+ ℝ) {u : M ≃ₗ[ℤ] M} (hu : u ∈ W P Ψ)
    (hμ : x - actPt u x ∈ (intPts : AddSubgroup (M →+ ℝ))) (k : ℕ) :
    x - actPt (u ^ k) x ∈ (intPts : AddSubgroup (M →+ ℝ)) ∧
    (x - actPt (u ^ k) x) - (k : ℤ) • (x - actPt u x) ∈ corootLattR P Ψ := by
  induction k with
  | zero => simp [actPt_one]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    have h3 := theta_mul (P := P) x hu h1
    rw [← pow_succ'] at h3
    have h4 := corootLattR_le h3
    refine ⟨?_, ?_⟩
    · have : x - actPt (u ^ (k + 1)) x = ((x - actPt u x) + (x - actPt (u ^ k) x)) +
          ((x - actPt (u ^ (k + 1)) x) - ((x - actPt u x) + (x - actPt (u ^ k) x))) := by abel
      rw [this]; exact add_mem (add_mem hμ h1) h4
    · have : (x - actPt (u ^ (k + 1)) x) - ((k + 1 : ℕ) : ℤ) • (x - actPt u x) =
          ((x - actPt (u ^ (k + 1)) x) - ((x - actPt u x) + (x - actPt (u ^ k) x))) +
          ((x - actPt (u ^ k) x) - (k : ℤ) • (x - actPt u x)) := by
        rw [Nat.cast_succ, add_smul, one_smul]; abel
      rw [this]; exact add_mem h3 h2

variable [Module.Free ℤ M] [Module.Finite ℤ M]

/-- Inductive step: `Y ∩ M_x = Z`. -/
theorem step33 (hR2 : HypR2 P) {p : ℕ} (Y Z : AddSubgroup M) (hZY : Z ≤ Y) (x : M →+ ℝ)
    (hxp : (p : ℤ) • x ∈ (intPts : AddSubgroup (M →+ ℝ)))
    (hYx : ∀ m ∈ Y, m ∈ Z ↔ m ∈ Mx x) {u : M ≃ₗ[ℤ] M}
    (hu : u ∈ W P (range P.root ∩ (Y : Set M))) (huZ : u ∈ WZ Z) :
    x - actPt u x ∈ (intPts : AddSubgroup (M →+ ℝ)) ∧
    (p : ℤ) • (x - actPt u x) ∈ corootLattR P (range P.root ∩ (Y : Set M)) ∧
    u ^ p ∈ W P (range P.root ∩ (Z : Set M)) ∧
    (x - actPt u x ∈ corootLattR P (range P.root ∩ (Y : Set M)) →
      u ∈ W P (range P.root ∩ (Z : Set M))) := by
  have hset : (range P.root ∩ (Y : Set M)) ∩ Mx x = range P.root ∩ (Z : Set M) := by
    ext m
    simp only [mem_inter_iff, SetLike.mem_coe]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, (hYx m h2).2 h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, hZY h2⟩, (hYx m (hZY h2)).1 h2⟩
  have hsub := isSubsystem_inter (P := P) Y
  have h1 : x - actPt u x ∈ (intPts : AddSubgroup (M →+ ℝ)) :=
    (mem_U_iff x u).1 fun m => (hYx _ (hZY (huZ m))).1 (huZ m)
  have h2 := nsmul_theta (P := P) x hu hxp
  refine ⟨h1, h2, ?_, ?_⟩
  · have hp := pow_theta (P := P) x hu h1 p
    have hker : x - actPt (u ^ p) x ∈ corootLattR P (range P.root ∩ (Y : Set M)) := by
      have : x - actPt (u ^ p) x = ((x - actPt (u ^ p) x) - (p : ℤ) • (x - actPt u x)) +
          (p : ℤ) • (x - actPt u x) := by abel
      rw [this]; exact add_mem hp.2 h2
    rw [← hset]
    exact mem_W_of_theta P hR2 faithful_of_free hsub x (pow_mem hu p) hker
  · intro hker
    rw [← hset]
    exact mem_W_of_theta P hR2 faithful_of_free hsub x hu hker

end RD

end AlgMag.Torsion
