/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Torsion.Lemma12dB

/-!
# Lemma 1.2(d), part C: existence of `c` and of the point `x` with `x - c x = λ`

`exists_c_x`: for a set `Ψ` of roots and `λ ∈ M^∨ ⊗ ℝ` with `pλ ∈ ℤΨ^∨` (`p > 0`), there are
`c ∈ W(Ψ)` (a product of reflections in a maximal `ℤ`-independent subset of `Ψ`) and a point `x`
with `x - c x = λ`. Hypotheses: `[Fintype ι]` only (finitely many roots, part of the definition of
a root datum).
-/

namespace AlgMag.Torsion

open Set RD Classical

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] [Fintype ι]
  (P : RootPairing ι ℤ M N)

namespace RD

lemma nrm_corootR (j : ι) (m : M) :
    (nrm P j : ℝ) * corootR P j m = 2 * ∑ i, (P.pairing j i : ℝ) * corootR P i m := by
  have h := congrArg (fun n : N => P.toLinearMap m n) (P.rootForm_self_smul_coroot j)
  simp only [map_nsmul, map_sum, RootPairing.Polarization_apply, map_smul, smul_eq_mul,
    nsmul_eq_mul, P.rootForm_root_self, RootPairing.root_coroot'_eq_pairing] at h
  have h2 : (nrm P j) * P.toLinearMap m (P.coroot j)
      = 2 * ∑ i, P.pairing j i * P.toLinearMap m (P.coroot i) := by
    unfold nrm
    first | exact h | (rw [Finset.mul_sum] at h ⊢; linarith [h])
  have e : ∀ i, corootR P i m = ((P.toLinearMap m (P.coroot i) : ℤ) : ℝ) := fun _ => rfl
  simp only [e]
  exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h2

lemma rep_eq_zero {T : Finset ι} {a : ι → ℚ} (hy : ∀ k ∈ T, Rep P T a (P.root k) = 0) :
    Rep P T a = 0 := by
  have h1 : ∀ k ∈ T, ∑ j ∈ T, (a j : ℝ) * (P.pairing k j : ℝ) = 0 := fun k hk => by
    rw [← Rep_root]; exact hy k hk
  have hA := claimA P T (fun j => (a j : ℝ)) h1
  ext m
  rw [Rep_apply]
  have this : ∀ j, corootR P j m = (2 / (nrm P j : ℝ)) * ∑ i, (P.pairing j i : ℝ) * corootR P i m := by
    intro j
    have h := nrm_corootR P j m
    have hn := nrm_ne P j
    field_simp
    linarith
  have e : ∑ j ∈ T, (a j : ℝ) * corootR P j m
      = ∑ i, (∑ j ∈ T, (a j : ℝ) * (2 / (nrm P j : ℝ)) * (P.pairing j i : ℝ)) * corootR P i m := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [this j, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e]
  simp [hA]

lemma exists_indep (T : Finset ι) :
    ∃ A ⊆ T, IndOn P A ∧ ∀ j ∈ T, ∃ n : ℤ, n ≠ 0 ∧ ∃ z : ι → ℤ,
      n • P.root j = ∑ i ∈ A, z i • P.root i := by
  obtain ⟨A, hA, hmax⟩ := Finset.exists_max_image (T.powerset.filter (fun A => IndOn P A))
    Finset.card ⟨∅, by
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.empty_subset _, fun z _ j hj => absurd hj (Finset.notMem_empty j)⟩⟩
  rw [Finset.mem_filter, Finset.mem_powerset] at hA
  refine ⟨A, hA.1, hA.2, fun j hj => ?_⟩
  by_cases hjA : j ∈ A
  · refine ⟨1, one_ne_zero, fun i => if i = j then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hi; simp [hi]
    · intro h; exact absurd hjA h
  · have hnot : ¬ IndOn P (insert j A) := by
      intro hind
      have := hmax (insert j A) (by
        rw [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.insert_subset hj hA.1, hind⟩)
      rw [Finset.card_insert_of_notMem hjA] at this
      omega
    unfold IndOn at hnot
    push_neg at hnot
    obtain ⟨z, hz, i0, hi0, hzi0⟩ := hnot
    rw [Finset.sum_insert hjA] at hz
    have hzj : z j ≠ 0 := by
      intro h0
      rw [h0, zero_smul, zero_add] at hz
      have := hA.2 z hz
      rcases Finset.mem_insert.1 hi0 with rfl | h
      · exact hzi0 h0
      · exact hzi0 (this i0 h)
    refine ⟨z j, hzj, fun i => - z i, ?_⟩
    have : z j • P.root j = -∑ i ∈ A, z i • P.root i := eq_neg_of_add_eq_zero_left hz
    rw [this, ← Finset.sum_neg_distrib]
    simp [neg_smul]

lemma surj_of_inj_restrict {V : Type*} [AddCommGroup V] [Module ℚ V] (E : Submodule ℚ V)
    [FiniteDimensional ℚ E] (g : V →ₗ[ℚ] V) (hg : ∀ y ∈ E, g y ∈ E)
    (hinj : ∀ y ∈ E, g y = 0 → y = 0) : ∀ z ∈ E, ∃ y ∈ E, g y = z := by
  have h : Function.Injective (g.restrict hg) := by
    refine (injective_iff_map_eq_zero (g.restrict hg)).2 fun y hy => ?_
    have := hinj y.1 y.2 (congrArg Subtype.val hy)
    exact Subtype.ext this
  intro z hz
  obtain ⟨y, hy⟩ := LinearMap.surjective_of_injective h ⟨z, hz⟩
  exact ⟨y.1, y.2, congrArg Subtype.val hy⟩

noncomputable def RepL(T : Finset ι) : (ι → ℚ) →ₗ[ℚ] (M →+ ℝ) where
  toFun := Rep P T
  map_add' b b' := by
    ext m; simp [Rep_apply, add_mul, Finset.sum_add_distrib]
  map_smul' q b := by
    ext m; simp [Rep_apply, Finset.mul_sum, mul_assoc, Rat.smul_def]

noncomputable def actL (w : M ≃ₗ[ℤ] M) : (M →+ ℝ) →ₗ[ℚ] (M →+ ℝ) where
  toFun := actPt w
  map_add' := actPt_add w
  map_smul' q y := by ext m; rfl

theorem exists_c_x (Ψ : Set M) (p : ℕ) (hp : 0 < p) (lam : M →+ ℝ)
    (hpl : (p : ℤ) • lam ∈ corootLattR P Ψ) :
    ∃ c ∈ W P Ψ, ∃ x : M →+ ℝ, x - actPt c x = lam := by
  set T : Finset ι := Finset.univ.filter (fun j => P.root j ∈ Ψ) with hT
  obtain ⟨A, hAT, hA, hspan⟩ := exists_indep P T
  have hlA : ∀ i ∈ A.toList, i ∈ A := fun i hi => Finset.mem_toList.1 hi
  refine ⟨(A.toList.map P.reflection).prod, ?_, ?_⟩
  · apply Subgroup.list_prod_mem
    intro w hw
    rw [List.mem_map] at hw
    obtain ⟨i, hi, rfl⟩ := hw
    exact Subgroup.subset_closure
      ⟨i, (Finset.mem_filter.1 (hAT (hlA i hi))).2, rfl⟩
  · set c := (A.toList.map P.reflection).prod with hc
    let E : Submodule ℚ (M →+ ℝ) := LinearMap.range (RepL P T)
    have hE : ∀ y, y ∈ E ↔ HasRep P T y := fun y =>
      ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩
    let g : (M →+ ℝ) →ₗ[ℚ] (M →+ ℝ) := LinearMap.id - actL c
    have hstab : ∀ y ∈ E, g y ∈ E := by
      intro y hy
      have hy' := (hE y).1 hy
      have h2 := hasRep_prod P A.toList (fun i hi => hAT (hlA i hi)) hy'
      show y - actPt c y ∈ E
      exact E.sub_mem hy ((hE _).2 h2)
    have hinj : ∀ y ∈ E, g y = 0 → y = 0 := by
      intro y hyE hy
      have hy0 : y - actPt c y = 0 := hy
      have hfix : actPt c y = y := by
        rw [sub_eq_zero] at hy0; exact hy0.symm
      have hrep := (hE _).1 hyE
      have hz := fix_zero P hAT hA A.toList (Finset.nodup_toList A) hlA hrep hfix
      have hz' : ∀ k ∈ T, y (P.root k) = 0 := by
        intro k hk
        obtain ⟨n, hn, z, hz2⟩ := hspan k hk
        have h3 : y (n • P.root k) = y (∑ i ∈ A, z i • P.root i) := by rw [hz2]
        rw [map_zsmul, map_sum] at h3
        simp only [map_zsmul] at h3
        have h4 : ∑ i ∈ A, z i • y (P.root i) = 0 :=
          Finset.sum_eq_zero fun i hi => by
            rw [hz i (Finset.mem_toList.2 hi)]; simp
        rw [h4] at h3
        have : (n : ℝ) * y (P.root k) = 0 := by simpa using h3
        rcases mul_eq_zero.1 this with h | h
        · exact absurd (by exact_mod_cast h) hn
        · exact h
      obtain ⟨b, hb⟩ := hrep
      rw [hb] at hz' ⊢
      exact rep_eq_zero P hz'
    haveI : FiniteDimensional ℚ E := Module.Finite.range (RepL P T)
    have hlamE : lam ∈ E := by
      have hsub : corootLattR P Ψ ≤ E.toAddSubgroup := by
        refine (AddSubgroup.closure_le _).2 ?_
        rintro y ⟨i, hi, rfl⟩
        have hiT : i ∈ T := Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩
        refine (hE _).2 ⟨fun j => if j = i then 1 else 0, ?_⟩
        rw [Rep_single P T hiT]; simp
      have h1 : (p : ℤ) • lam ∈ E := hsub hpl
      have h2 : ((1 : ℚ) / p) • ((p : ℤ) • lam) = lam := by
        rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul]
        have : ((1 : ℚ) / p) * ((p : ℤ) : ℚ) = 1 := by
          push_cast; field_simp
        rw [this, one_smul]
      rw [← h2]
      exact E.smul_mem _ h1
    obtain ⟨x, _, hx⟩ := surj_of_inj_restrict E g hstab hinj lam hlamE
    exact ⟨x, hx⟩

end RD

end AlgMag.Torsion
