/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Torsion.Lemma12dA

/-!
# Lemma 1.2(d), part B

For a finite set `T` of root indices (`Ψ = {α_j | j ∈ T}`), `E_T = ℚ`-span of `{α_j^∨ | j ∈ T}`
inside `M^∨ ⊗ ℝ = (M →+ ℝ)`, and `c` the product of the reflections in a maximal `ℤ`-independent
subfamily `A ⊆ T`: `1 - c` is injective on `E_T` (`fix_zero`, `rep_eq_zero`), hence bijective
(`exists_c_x`), which gives the point `x` of Prop 4.1.
-/

namespace AlgMag.Torsion

open Set RD Classical

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] [Fintype ι]
  (P : RootPairing ι ℤ M N)

namespace RD

/-- `∑_{j ∈ T} b_j α_j^∨`. -/
noncomputable def Rep (T : Finset ι) (b : ι → ℚ) : M →+ ℝ := ∑ j ∈ T, (b j : ℝ) • corootR P j

def HasRep (T : Finset ι) (y : M →+ ℝ) : Prop := ∃ b, y = Rep P T b

lemma Rep_apply (T : Finset ι) (b : ι → ℚ) (m : M) :
    Rep P T b m = ∑ j ∈ T, (b j : ℝ) * corootR P j m := by
  simp [Rep, AddMonoidHom.finset_sum_apply]

lemma Rep_root (T : Finset ι) (b : ι → ℚ) (k : ι) :
    Rep P T b (P.root k) = ∑ j ∈ T, (b j : ℝ) * (P.pairing k j : ℝ) := by
  rw [Rep_apply]; rfl

lemma Rep_sub (T : Finset ι) (b b' : ι → ℚ) :
    Rep P T (fun j => b j - b' j) = Rep P T b - Rep P T b' := by
  ext m
  simp only [Rep_apply, AddMonoidHom.sub_apply, Rat.cast_sub, sub_mul, Finset.sum_sub_distrib]

lemma Rep_single (A : Finset ι) {i : ι} (hi : i ∈ A) (q : ℚ) :
    Rep P A (fun j => if j = i then q else 0) = (q : ℝ) • corootR P i := by
  ext m
  simp only [Rep_apply, AddMonoidHom.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · intro h; exact absurd hi h

lemma rat_val {T : Finset ι} {y : M →+ ℝ} (hy : HasRep P T y) (k : ι) :
    ∃ q : ℚ, y (P.root k) = q := by
  obtain ⟨b, rfl⟩ := hy
  refine ⟨∑ j ∈ T, b j * (P.pairing k j : ℚ), ?_⟩
  rw [Rep_root]; push_cast; rfl

lemma hasRep_refl {T : Finset ι} {y : M →+ ℝ} (hy : HasRep P T y) {i : ι} (hi : i ∈ T) :
    HasRep P T (actPt (P.reflection i) y) := by
  obtain ⟨q, hq⟩ := rat_val P hy i
  obtain ⟨b, rfl⟩ := hy
  refine ⟨fun j => b j - if j = i then q else 0, ?_⟩
  rw [Rep_sub, Rep_single P T hi, actPt_reflection, hq]

lemma hasRep_prod {T : Finset ι} (l : List ι) (hl : ∀ i ∈ l, i ∈ T) {y : M →+ ℝ}
    (hy : HasRep P T y) : HasRep P T (actPt (l.map P.reflection).prod y) := by
  induction l with
  | nil => simpa [actPt_one] using hy
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, actPt_mul]
    exact hasRep_refl P (ih fun j hj => hl j (List.mem_cons_of_mem _ hj))
      (hl i List.mem_cons_self)

lemma diff_rep {T A : Finset ι} (hAT : A ⊆ T) (l : List ι) (hl : ∀ i ∈ l, i ∈ A)
    {y : M →+ ℝ} (hy : HasRep P T y) :
    ∃ b : ι → ℚ, (∀ j, j ∉ l → b j = 0) ∧
      actPt (l.map P.reflection).prod y - y = Rep P A b := by
  induction l with
  | nil => exact ⟨0, fun _ _ => rfl, by ext m; simp [Rep_apply, actPt_one]⟩
  | cons i l ih =>
    obtain ⟨b, hb, hd⟩ := ih fun j hj => hl j (List.mem_cons_of_mem _ hj)
    have hy' := hasRep_prod P l (fun j hj => hAT (hl j (List.mem_cons_of_mem _ hj))) hy
    obtain ⟨q, hq⟩ := rat_val P hy' i
    have hiA : i ∈ A := hl i List.mem_cons_self
    refine ⟨fun j => b j - if j = i then q else 0, ?_, ?_⟩
    · intro j hj
      have h1 : j ≠ i := fun h => hj (h ▸ List.mem_cons_self)
      have h2 : j ∉ l := fun h => hj (List.mem_cons_of_mem _ h)
      simp [hb j h2, h1]
    · rw [Rep_sub, Rep_single P A hiA, ← hd]
      simp only [List.map_cons, List.prod_cons, actPt_mul, actPt_reflection, hq]
      abel

lemma indep_apply {A : Finset ι} (hA : IndOn P A) (b : ι → ℚ) (h : Rep P A b = 0) :
    ∀ j ∈ A, b j = 0 := by
  apply coroot_indep P A hA b
  intro k _
  rw [← Rep_root, h]; rfl

/-- If `y ∈ E_T` is fixed by the product of the reflections of a list in `A`, then `⟨α_i, y⟩ = 0`
for all `i` in the list. -/
lemma fix_zero {T A : Finset ι} (hAT : A ⊆ T) (hA : IndOn P A) (l : List ι) (hnd : l.Nodup)
    (hl : ∀ i ∈ l, i ∈ A) {y : M →+ ℝ} (hy : HasRep P T y)
    (hfix : actPt (l.map P.reflection).prod y = y) : ∀ i ∈ l, y (P.root i) = 0 := by
  induction l generalizing y with
  | nil => simp
  | cons i l ih =>
    have hl' : ∀ j ∈ l, j ∈ A := fun j hj => hl j (List.mem_cons_of_mem _ hj)
    have hiA : i ∈ A := hl i List.mem_cons_self
    have hil : i ∉ l := (List.nodup_cons.1 hnd).1
    have hy' := hasRep_prod P l (fun j hj => hAT (hl' j hj)) hy
    obtain ⟨q, hq⟩ := rat_val P hy' i
    obtain ⟨b, hb, hd⟩ := diff_rep P hAT l hl' hy
    -- y' - y = q • α_i^∨
    have hcons : actPt (l.map P.reflection).prod y - (q : ℝ) • corootR P i = y := by
      have := hfix
      simp only [List.map_cons, List.prod_cons, actPt_mul, actPt_reflection, hq] at this
      exact this
    have hrep : Rep P A (fun j => b j - if j = i then q else 0) = 0 := by
      rw [Rep_sub, Rep_single P A hiA, ← hd, sub_right_comm, hcons, sub_self]
    have h0 := indep_apply P hA _ hrep i hiA
    have hbi : b i = 0 := hb i hil
    simp only [if_true, hbi] at h0
    have hq0 : q = 0 := by linarith
    have hsame : actPt (l.map P.reflection).prod y = y := by
      have h := hcons
      rw [hq0] at h
      simpa using h
    intro j hj
    rcases List.mem_cons.1 hj with h | hj'
    · have : y (P.root i) = (q : ℝ) := by rw [← hq, hsame]
      rw [h, this, hq0]; simp
    · exact ih (List.nodup_cons.1 hnd).2 hl' hy hsame j hj'

end RD

end AlgMag.Torsion
