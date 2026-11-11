/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Torsion.Theta

/-!
# Prop 4.1 of `notes/torsion-converse.md`, from `x - cx = λ` onwards

`prop41_core`: given `c ∈ W(Ψ)` (`Ψ` integrally closed) and a point `x` with
`λ := x - cx ∈ M^∨`, `λ ∉ ℤΨ^∨`, `pλ ∈ ℤΨ^∨`, the element `w₀ = c^m` (`ord c = p^b m`, `p ∤ m`)
has order `p^b`, is `≠ 1`, and `w₀ ∉ W(R_{w₀})`, `R_w = Φ ∩ (1-w)M`.

The existence of `x` (notes Lemma 1.2(d), `1 - c` bijective on `ℚΨ^∨` for a product `c` of
reflections in a maximal linearly independent subset of `Ψ`) is NOT formalized here.
-/

namespace AlgMag.Torsion

open Set RD

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] {P : RootPairing ι ℤ M N}

/-- `Z_w = (1 - w)M`. -/
def Zset (w : M ≃ₗ[ℤ] M) : Set M := {z | ∃ y, y - w y = z}

/-- Lemma 1.2(a): `(1 - v)M ⊆ ℤΨ` for `v ∈ W(Ψ)`. -/
lemma sub_mem_span {Ψ : Set M} {v : M ≃ₗ[ℤ] M} (hv : v ∈ W P Ψ) :
    ∀ y, y - v y ∈ Submodule.span ℤ Ψ := by
  induction hv using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨i, hi, rfl⟩ := hw
    intro y
    rw [RootPairing.reflection_apply, sub_sub_cancel]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hi)
  | one => intro y; simp
  | mul u w _ _ hu hw =>
    intro y
    have := add_mem (hw y) (hu (w y))
    rwa [sub_add_sub_cancel] at this
  | inv w _ hw =>
    intro y
    have := neg_mem (hw (w⁻¹ y))
    rw [neg_sub] at this
    convert this using 2
    show y = w (w.symm y)
    simp

lemma theta_pow {Ψ : Set M} (x : M →+ ℝ) {c : M ≃ₗ[ℤ] M} (hc : c ∈ W P Ψ)
    (hl : x - actPt c x ∈ (intPts : AddSubgroup (M →+ ℝ))) (k : ℕ) :
    (x - actPt (c ^ k) x) - (k : ℤ) • (x - actPt c x) ∈ corootLattR P Ψ := by
  induction k with
  | zero => simp [actPt_one]
  | succ k ih =>
    have h1 := theta_mul (P := P) x (u := c) (v := c ^ k) hc ?_
    · have := add_mem h1 ih
      rw [pow_succ']
      convert this using 1
      push_cast
      rw [add_smul, one_smul]; abel
    · have e : x - actPt (c ^ k) x =
          ((x - actPt (c ^ k) x) - (k : ℤ) • (x - actPt c x)) + (k : ℤ) • (x - actPt c x) := by abel
      rw [e]; exact add_mem (corootLattR_le ih) (zsmul_mem hl _)

/-- **Prop 4.1, core.** -/
theorem prop41_core {Ψ : Set M} (hΨ : IsIntClosed P Ψ) {c : M ≃ₗ[ℤ] M} (hc : c ∈ W P Ψ)
    (x : M →+ ℝ) (hl : x - actPt c x ∈ (intPts : AddSubgroup (M →+ ℝ)))
    (hln : x - actPt c x ∉ corootLattR P Ψ) {p : ℕ} (hp : p.Prime)
    (hpl : (p : ℤ) • (x - actPt c x) ∈ corootLattR P Ψ) {b m : ℕ}
    (hord : orderOf c = p ^ b * m) (hpm : ¬ p ∣ m) :
    orderOf (c ^ m) = p ^ b ∧ c ^ m ≠ 1 ∧ c ^ m ∉ W P (range P.root ∩ Zset (c ^ m)) := by
  -- θ(c^m) ∉ ℤΨ^∨
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hpm
  have hθ := theta_pow (P := P) x hc hl m
  have hml : (m : ℤ) • (x - actPt c x) ∉ corootLattR P Ψ := by
    intro h
    apply hln
    obtain ⟨a, b', hab⟩ : ∃ a b' : ℤ, a * p + b' * m = 1 := by
      refine ⟨Nat.gcdA p m, Nat.gcdB p m, ?_⟩
      have := Nat.gcd_eq_gcd_ab p m
      rw [hcop] at this; push_cast at this; linarith
    have e : x - actPt c x = a • ((p : ℤ) • (x - actPt c x)) + b' • ((m : ℤ) • (x - actPt c x)) := by
      rw [smul_smul, smul_smul, ← add_smul, hab, one_smul]
    rw [e]; exact add_mem (zsmul_mem hpl _) (zsmul_mem h _)
  have hw0 : x - actPt (c ^ m) x ∉ corootLattR P Ψ := by
    intro h; apply hml
    have := sub_mem h hθ; simpa using this
  have hw0int : x - actPt (c ^ m) x ∈ (intPts : AddSubgroup (M →+ ℝ)) := by
    have e : x - actPt (c ^ m) x =
        ((x - actPt (c ^ m) x) - (m : ℤ) • (x - actPt c x)) + (m : ℤ) • (x - actPt c x) := by abel
    rw [e]; exact add_mem (corootLattR_le hθ) (zsmul_mem hl _)
  refine ⟨?_, ?_, ?_⟩
  · have hm0 : m ≠ 0 := by rintro rfl; exact hpm (dvd_zero p)
    rw [orderOf_pow' c hm0, hord, Nat.gcd_mul_left_left, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  · intro h1; apply hw0; rw [h1]; simp [actPt_one]
  · intro hmem
    apply hw0
    have hW : c ^ m ∈ W P Ψ := pow_mem hc m
    have hsub : range P.root ∩ Zset (c ^ m) ⊆ Ψ ∩ Mx x := by
      rintro α ⟨hα, y, rfl⟩
      refine ⟨?_, (mem_U_iff x (c ^ m)).2 hw0int y⟩
      rw [hΨ]; exact ⟨hα, sub_mem_span hW y⟩
    exact theta_of_mem x (W_mono hsub hmem)

end AlgMag.Torsion
