/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Torsion.Prop41Core
import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate

/-!
# Lemma 1.2(d), part A: independence of coroots (form argument)

`coroot_indep`: if `α_j` (`j ∈ T`) are `ℤ`-linearly independent in `M`, then the coroots `α_j^∨`
are `ℚ`-linearly independent (as points of `M^∨ ⊗ ℝ`; the relation is expressed by pairing with
the roots `α_k`, `k ∈ T`). Uses the invariant form and `[Fintype ι]` (finitely many roots, part of
the definition of a root datum).
-/

namespace AlgMag.Torsion

open Set RD

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] [Fintype ι]
  (P : RootPairing ι ℤ M N)

namespace RD

/-- `n_j = ∑_i ⟨α_j, α_i^∨⟩²`. -/
def nrm (j : ι) : ℤ := ∑ i, P.pairing j i * P.pairing j i

lemma corootR_root (j k : ι) : corootR P j (P.root k) = (P.pairing k j : ℝ) := rfl

lemma nrm_pos (j : ι) : 0 < nrm P j := by
  have h : P.pairing j j * P.pairing j j ≤ nrm P j :=
    Finset.single_le_sum (f := fun i => P.pairing j i * P.pairing j i)
      (fun i _ => mul_self_nonneg _) (Finset.mem_univ j)
  have h2 : P.pairing j j = 2 := P.pairing_same j
  rw [h2] at h
  omega

lemma nrm_ne (j : ι) : (nrm P j : ℝ) ≠ 0 := by
  have := nrm_pos P j
  positivity

/-- `n_j ⟨α_k, α_j^∨⟩ = 2 ∑_i ⟨α_j,α_i^∨⟩⟨α_k,α_i^∨⟩`. -/
lemma nrm_pairing (j k : ι) :
    (nrm P j : ℝ) * (P.pairing k j : ℝ) =
      2 * ∑ i, (P.pairing j i : ℝ) * (P.pairing k i : ℝ) := by
  have h := congrArg (fun n : N => P.toLinearMap (P.root k) n) (P.rootForm_self_smul_coroot j)
  simp only [map_nsmul, map_sum, RootPairing.Polarization_apply, map_smul, smul_eq_mul,
    nsmul_eq_mul, P.rootForm_root_self, RootPairing.root_coroot_eq_pairing,
    RootPairing.root_coroot'_eq_pairing] at h
  have h2 : (nrm P j) * P.pairing k j = 2 * ∑ i, P.pairing j i * P.pairing k i := by
    unfold nrm
    first | exact h | (rw [Finset.mul_sum] at h ⊢; linarith [h])
  exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h2

lemma claimA (T : Finset ι) (a : ι → ℝ)
    (hy : ∀ k ∈ T, ∑ j ∈ T, a j * (P.pairing k j : ℝ) = 0) :
    ∀ i, ∑ j ∈ T, a j * (2 / (nrm P j : ℝ)) * (P.pairing j i : ℝ) = 0 := by
  set c : ι → ℝ := fun i => ∑ j ∈ T, a j * (2 / (nrm P j : ℝ)) * (P.pairing j i : ℝ) with hc
  have hk : ∀ k, ∑ i, c i * (P.pairing k i : ℝ) = ∑ j ∈ T, a j * (P.pairing k j : ℝ) := by
    intro k
    simp only [hc, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := nrm_pairing P j k
    have hn := nrm_ne P j
    have e : ∑ i, a j * (2 / (nrm P j : ℝ)) * (P.pairing j i : ℝ) * (P.pairing k i : ℝ)
        = a j * (2 / (nrm P j : ℝ)) * ∑ i, (P.pairing j i : ℝ) * (P.pairing k i : ℝ) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    have : ∑ i, (P.pairing j i : ℝ) * (P.pairing k i : ℝ)
        = (nrm P j : ℝ) * (P.pairing k j : ℝ) / 2 := by linarith
    rw [this]; field_simp
  have hsq : ∑ i, c i * c i = 0 := by
    have : ∀ i, c i * c i = ∑ j ∈ T, a j * (2 / (nrm P j : ℝ)) * (c i * (P.pairing j i : ℝ)) := by
      intro i
      conv_lhs => rw [show c i * c i = c i * ∑ j ∈ T, a j * (2 / (nrm P j : ℝ)) * (P.pairing j i : ℝ)
        from rfl]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp_rw [this]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [← Finset.mul_sum, hk j, hy j hj, mul_zero]
  intro i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (c i))).1 hsq i
    (Finset.mem_univ i)
  exact mul_self_eq_zero.1 this

/-- Integral independence of the roots indexed by `T`. -/
def IndOn (T : Finset ι) : Prop :=
  ∀ z : ι → ℤ, ∑ j ∈ T, z j • P.root j = 0 → ∀ j ∈ T, z j = 0

lemma coroot_indep (T : Finset ι) (hT : IndOn P T) (a : ι → ℚ)
    (h : ∀ k ∈ T, ∑ j ∈ T, (a j : ℝ) * (P.pairing k j : ℝ) = 0) : ∀ j ∈ T, a j = 0 := by
  have hA := claimA P T (fun j => (a j : ℝ)) h
  set b : ι → ℚ := fun j => a j * (2 / (nrm P j : ℚ)) with hb
  have hbz : ∀ i, ∑ j ∈ T, b j * (P.pairing j i : ℚ) = 0 := by
    intro i
    have := hA i
    have h' : ((∑ j ∈ T, b j * (P.pairing j i : ℚ) : ℚ) : ℝ) = 0 := by
      push_cast [hb]; exact this
    exact_mod_cast h'
  set D : ℕ := ∏ j ∈ T, (b j).den with hD
  have hDpos : 0 < D := Finset.prod_pos fun j _ => (b j).pos
  set z : ι → ℤ := fun j => ((D / (b j).den : ℕ) : ℤ) * (b j).num with hz
  have hzb : ∀ j ∈ T, (z j : ℚ) = D * b j := by
    intro j hj
    have hdvd : (b j).den ∣ D := Finset.dvd_prod_of_mem _ hj
    obtain ⟨e, he⟩ := hdvd
    have hden : (0 : ℚ) < (b j).den := by exact_mod_cast (b j).pos
    have hD' : D / (b j).den = e := by
      rw [he]; exact Nat.mul_div_cancel_left e (b j).pos
    simp only [hz, hD', Int.cast_mul, Int.cast_natCast]
    rw [he]; push_cast
    rw [← Rat.mul_den_eq_num (b j)]; ring
  have hzs : ∀ i, ∑ j ∈ T, z j * P.pairing j i = 0 := by
    intro i
    have : ((∑ j ∈ T, z j * P.pairing j i : ℤ) : ℚ) = 0 := by
      push_cast
      rw [Finset.sum_congr rfl fun j hj => by rw [hzb j hj]]
      have := hbz i
      simp_rw [mul_assoc, ← Finset.mul_sum, this, mul_zero]
    exact_mod_cast this
  have hu : ∑ j ∈ T, z j • P.root j = 0 := by
    set u := ∑ j ∈ T, z j • P.root j with hu
    have h1 : u ∈ P.rootSpan ℤ :=
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨j, rfl⟩)
    have h2 : u ∈ LinearMap.ker P.RootForm := by
      rw [LinearMap.mem_ker]
      ext x
      have hc : ∀ i, P.coroot' i u = 0 := by
        intro i
        have : P.coroot' i u = ∑ j ∈ T, z j * P.pairing j i := by
          simp only [hu, map_sum, map_zsmul, zsmul_eq_mul, Int.cast_id,
            RootPairing.root_coroot'_eq_pairing]
        rw [this]; exact hzs i
      simp [RootPairing.rootForm_apply_apply, hc]
    have := (P.disjoint_rootSpan_ker_rootForm).le_bot ⟨h1, h2⟩
    simpa using this
  intro j hj
  have h0 := hT z hu j hj
  have hbj : b j = 0 := by
    have := hzb j hj
    rw [h0] at this
    simp at this
    rcases this with h | h
    · exact absurd h hDpos.ne'
    · exact h
  have hn : (nrm P j : ℚ) ≠ 0 := by
    have := nrm_pos P j; positivity
  simp only [hb] at hbj
  rcases mul_eq_zero.1 hbj with h | h
  · exact h
  · exfalso
    field_simp at h
    exact hn (by simpa using h)

end RD

end AlgMag.Torsion
