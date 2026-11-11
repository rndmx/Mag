/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec15PureMagnets
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# `D(ℤ/6ℤ)` acting on `𝔸(ℕ)³` with weights `1, 2, 3`

Example (vi) after Fact 15.11 of *Algebraic Magnetism*, with the action on `𝔸(ℕ)³` (the
corrected reading of the misprint `D(ℤ/6ℤ)³`): `𝔸³_R = Spec R[x₁, x₂, x₃]`, graded by `ℤ/6ℤ` with
`deg xᵢ = i`. The pure magnets are `0, 2ℤ/6ℤ, 3ℤ/6ℤ, ℤ/6ℤ`.

* `magnetIdeal_le_ker_eval`: the attractor `X^L` contains the point `e_L` with coordinates `1`
  where the weight lies in `L` and `0` elsewhere;
* `weight_mem_iff_of_magnetIdeal_eq`: magnets with the same attractor contain the same weights;
* `addSubmonoid_zmod_six`: the submonoids of `ℤ/6ℤ` are `0, 2ℤ/6ℤ, 3ℤ/6ℤ, ℤ/6ℤ`;
* `pureMagnets_zmod_six_weights`: `Π(a) = {0, 2ℤ/6ℤ, 3ℤ/6ℤ, ℤ/6ℤ}`.
-/

open MvPolynomial Magnetism

namespace AlgMag

section Weights

variable {σ M : Type*} [Fintype σ] [AddCommMonoid M]
variable (R : Type*) [CommRing R] (w : σ → M)

/-- The point `e_L` of `𝔸^σ`: coordinate `1` where the weight lies in `L`, `0` elsewhere. -/
noncomputable def weightPoint (L : AddSubmonoid M) : σ → R :=
  fun i => by classical exact if w i ∈ L then 1 else 0

/-- `e_L ∈ X^L`: evaluation at `e_L` kills `J_L`. -/
theorem magnetIdeal_le_ker_eval (L : AddSubmonoid M) :
    magnetIdeal (weightedHomogeneousSubmodule R w) L ≤
      RingHom.ker (eval (weightPoint R w L)) := by
  classical
  refine Ideal.span_le.2 fun φ hφ => ?_
  simp only [Set.mem_iUnion, SetLike.mem_coe, mem_weightedHomogeneousSubmodule] at hφ
  obtain ⟨m, hm, hφ⟩ := hφ
  rw [SetLike.mem_coe, RingHom.mem_ker, eval_eq']
  refine Finset.sum_eq_zero fun d hd => ?_
  have hw := hφ (mem_support_iff.1 hd)
  obtain ⟨i, hi, hiL⟩ : ∃ i ∈ d.support, w i ∉ L := by
    by_contra! h
    apply hm
    rw [← hw, Finsupp.weight_apply, Finsupp.sum]
    exact L.sum_mem fun i hi => L.nsmul_mem (h i hi) _
  have : weightPoint R w L i ^ d i = 0 := by
    simp only [weightPoint, hiL, ↓reduceIte]
    exact zero_pow (Finsupp.mem_support_iff.1 hi)
  rw [Finset.prod_eq_zero (Finset.mem_univ i) this, mul_zero]

variable [Nontrivial R]

/-- Magnets with the same attractor contain the same weights. -/
theorem weight_mem_iff_of_magnetIdeal_eq {N L : AddSubmonoid M}
    (h : magnetIdeal (weightedHomogeneousSubmodule R w) N =
      magnetIdeal (weightedHomogeneousSubmodule R w) L) (i : σ) : w i ∈ N ↔ w i ∈ L := by
  classical
  have key : ∀ {N L : AddSubmonoid M}, magnetIdeal (weightedHomogeneousSubmodule R w) N =
      magnetIdeal (weightedHomogeneousSubmodule R w) L → w i ∈ L → w i ∈ N := by
    intro N L h hL
    by_contra hN
    have hX : (X i : MvPolynomial σ R) ∈ magnetIdeal (weightedHomogeneousSubmodule R w) N :=
      mem_magnetIdeal_of_notMem hN ((mem_weightedHomogeneousSubmodule _ _ _ _).2
        (isWeightedHomogeneous_X R w i))
    have := magnetIdeal_le_ker_eval R w L (h ▸ hX)
    simp [RingHom.mem_ker, weightPoint, hL] at this
  exact ⟨key h.symm, key h⟩

end Weights

section ZModSix

/-- `2ℤ/6ℤ`. -/
def evensSix : AddSubmonoid (ZMod 6) where
  carrier := {x | x = 0 ∨ x = 2 ∨ x = 4}
  add_mem' := by
    rintro a b (rfl | rfl | rfl) (rfl | rfl | rfl) <;> decide
  zero_mem' := Or.inl rfl

/-- `3ℤ/6ℤ`. -/
def triplesSix : AddSubmonoid (ZMod 6) where
  carrier := {x | x = 0 ∨ x = 3}
  add_mem' := by
    rintro a b (rfl | rfl) (rfl | rfl) <;> decide
  zero_mem' := Or.inl rfl

lemma zmod_six_cases (x : ZMod 6) :
    x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by
  revert x; decide

lemma closure_two_eq : AddSubmonoid.closure ({2} : Set (ZMod 6)) = evensSix := by
  refine le_antisymm (AddSubmonoid.closure_le.2 fun x hx => ?_) fun x hx => ?_
  · rw [Set.mem_singleton_iff.1 hx]; exact Or.inr (Or.inl rfl)
  · have h2 : (2 : ZMod 6) ∈ AddSubmonoid.closure ({2} : Set (ZMod 6)) :=
      AddSubmonoid.subset_closure rfl
    rcases hx with rfl | rfl | rfl
    · exact zero_mem _
    · exact h2
    · exact (show (4 : ZMod 6) = 2 + 2 by decide) ▸ add_mem h2 h2

lemma closure_three_eq : AddSubmonoid.closure ({3} : Set (ZMod 6)) = triplesSix := by
  refine le_antisymm (AddSubmonoid.closure_le.2 fun x hx => ?_) fun x hx => ?_
  · rw [Set.mem_singleton_iff.1 hx]; exact Or.inr rfl
  · rcases hx with rfl | rfl
    · exact zero_mem _
    · exact AddSubmonoid.subset_closure rfl

/-- The submonoids of `ℤ/6ℤ` are `0, 2ℤ/6ℤ, 3ℤ/6ℤ, ℤ/6ℤ`. -/
theorem addSubmonoid_zmod_six (N : AddSubmonoid (ZMod 6)) :
    N = ⊥ ∨ N = AddSubmonoid.closure {2} ∨ N = AddSubmonoid.closure {3} ∨ N = ⊤ := by
  rw [closure_two_eq, closure_three_eq]
  by_cases h1 : (1 : ZMod 6) ∈ N
  · refine Or.inr (Or.inr (Or.inr (eq_top_iff.2 fun x _ => ?_)))
    have := N.nsmul_mem h1 x.val
    rwa [nsmul_one, ZMod.natCast_zmod_val] at this
  have h5 : (5 : ZMod 6) ∉ N := fun h =>
    h1 ((show (5 : ZMod 6) + 5 + 5 + 5 + 5 = 1 by decide) ▸
      add_mem (add_mem (add_mem (add_mem h h) h) h) h)
  by_cases h24 : (2 : ZMod 6) ∈ N ∨ (4 : ZMod 6) ∈ N
  · have h2 : (2 : ZMod 6) ∈ N := h24.elim id fun h =>
      (show (4 : ZMod 6) + 4 = 2 by decide) ▸ add_mem h h
    have h4 : (4 : ZMod 6) ∈ N := (show (2 : ZMod 6) + 2 = 4 by decide) ▸ add_mem h2 h2
    have h3 : (3 : ZMod 6) ∉ N := fun h => h5 ((show (2 : ZMod 6) + 3 = 5 by decide) ▸ add_mem h2 h)
    refine Or.inr (Or.inl (AddSubmonoid.ext fun x => ?_))
    change x ∈ N ↔ x = 0 ∨ x = 2 ∨ x = 4
    rcases zmod_six_cases x with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all <;> decide
  · simp only [not_or] at h24
    by_cases h3 : (3 : ZMod 6) ∈ N
    · refine Or.inr (Or.inr (Or.inl (AddSubmonoid.ext fun x => ?_)))
      change x ∈ N ↔ x = 0 ∨ x = 3
      rcases zmod_six_cases x with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp_all <;> decide
    · refine Or.inl (AddSubmonoid.ext fun x => ?_)
      rw [AddSubmonoid.mem_bot]
      rcases zmod_six_cases x with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp_all <;> decide

/-- The weights `1, 2, 3` of `x₁, x₂, x₃`. -/
def weightsSix : Fin 3 → ZMod 6 := ![1, 2, 3]

variable (R : Type*) [CommRing R] [Nontrivial R]

set_option linter.unnecessarySeqFocus false in
/-- **Example (vi) after Fact 15.11, corrected.** `D(ℤ/6ℤ)` acting on `𝔸(ℕ)³ = Spec R[x₁, x₂, x₃]`
with weights `1, 2, 3`: `Π(a) = {0, 2ℤ/6ℤ, 3ℤ/6ℤ, ℤ/6ℤ}`. -/
theorem pureMagnets_zmod_six_weights :
    pureMagnets (affineY (weightedHomogeneousSubmodule R weightsSix)) =
      {⊥, AddSubmonoid.closure {2}, AddSubmonoid.closure {3}, ⊤} := by
  -- the weights in each of the four submonoids
  have key : ∀ N L : AddSubmonoid (ZMod 6),
      (N = ⊥ ∨ N = AddSubmonoid.closure {2} ∨ N = AddSubmonoid.closure {3} ∨ N = ⊤) →
      (L = ⊥ ∨ L = AddSubmonoid.closure {2} ∨ L = AddSubmonoid.closure {3} ∨ L = ⊤) →
      (∀ i, weightsSix i ∈ N ↔ weightsSix i ∈ L) → N = L := by
    intro N L hN hL h
    rw [closure_two_eq, closure_three_eq] at hN hL
    have h1 := h 0
    have h2 := h 1
    have h3 := h 2
    simp only [weightsSix, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h1 h2 h3
    rcases hN with rfl | rfl | rfl | rfl <;> rcases hL with rfl | rfl | rfl | rfl <;>
      first
      | rfl
      | (exfalso; simp [evensSix, triplesSix, AddSubmonoid.mem_bot] at h1 h2 h3 <;> revert h1 h2 h3 <;> decide)
  ext N
  constructor
  · intro _
    have := addSubmonoid_zmod_six N
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  · intro hN L hL
    have hN' : N = ⊥ ∨ N = AddSubmonoid.closure {2} ∨ N = AddSubmonoid.closure {3} ∨ N = ⊤ := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hN
    have hJ : magnetIdeal (weightedHomogeneousSubmodule R weightsSix) N =
        magnetIdeal (weightedHomogeneousSubmodule R weightsSix) L := hL
    exact (key N L hN' (addSubmonoid_zmod_six L)
      (weight_mem_iff_of_magnetIdeal_eq R weightsSix hJ)).le

end ZModSix

end AlgMag
