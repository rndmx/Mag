/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Torsion.Lemma12dC

/-!
# Finiteness of `W` (needed for finite orders)

`W_finite`: `W(Φ)` is finite (`[Fintype ι]`). `w ∈ W` is determined by the roots `w(α_j)`
(`eq_one_of_fix`: uses the invariant form), and `w` permutes the finite set of roots.
-/

namespace AlgMag.Torsion

open Set RD Classical

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] [Fintype ι]
  (P : RootPairing ι ℤ M N)

namespace RD

lemma zero_of_coroot_zero {u : M} (hu : u ∈ P.rootSpan ℤ) (h : ∀ i, P.coroot' i u = 0) :
    u = 0 := by
  have h2 : u ∈ LinearMap.ker P.RootForm := by
    rw [LinearMap.mem_ker]
    ext x
    simp [RootPairing.rootForm_apply_apply, h]
  have := (P.disjoint_rootSpan_ker_rootForm).le_bot ⟨hu, h2⟩
  simpa using this

lemma reflection_inv (i : ι) : (P.reflection i)⁻¹ = P.reflection i := by
  show (P.reflection i).symm = P.reflection i
  exact reflection_symm (P := P) i

lemma W_mem_list {Ψ : Set M} {w : M ≃ₗ[ℤ] M} (hw : w ∈ W P Ψ) :
    ∃ l : List ι, (∀ i ∈ l, P.root i ∈ Ψ) ∧ w = (l.map P.reflection).prod := by
  let Q : Subgroup (M ≃ₗ[ℤ] M) :=
    { carrier := {w | ∃ l : List ι, (∀ i ∈ l, P.root i ∈ Ψ) ∧ w = (l.map P.reflection).prod}
      mul_mem' := by
        rintro a b ⟨l, hl, rfl⟩ ⟨l', hl', rfl⟩
        refine ⟨l ++ l', ?_, by simp⟩
        intro i hi
        rcases List.mem_append.1 hi with h | h
        · exact hl i h
        · exact hl' i h
      one_mem' := ⟨[], by simp, by simp⟩
      inv_mem' := by
        rintro a ⟨l, hl, rfl⟩
        refine ⟨l.reverse, fun i hi => hl i (List.mem_reverse.1 hi), ?_⟩
        rw [List.prod_inv_reverse, List.map_map]
        have : ((fun x : M ≃ₗ[ℤ] M => x⁻¹) ∘ P.reflection) = P.reflection :=
          funext (reflection_inv P)
        rw [this, ← List.map_reverse] }
  refine (Subgroup.closure_le Q).2 ?_ hw
  rintro w ⟨i, hi, e⟩
  exact ⟨[i], by simpa using hi, by simp [← e]⟩

lemma list_root (l : List ι) (j : ι) : ∃ k, (l.map P.reflection).prod (P.root j) = P.root k := by
  induction l with
  | nil => exact ⟨j, by simp⟩
  | cons i l ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨P.reflectionPerm i k, ?_⟩
    simp only [List.map_cons, List.prod_cons, LinearEquiv.mul_apply, hk]
    exact (P.root_reflectionPerm i k).symm

lemma eq_one_of_fix {g : M ≃ₗ[ℤ] M} (hg : g ∈ W P (range P.root))
    (hfix : ∀ j, g (P.root j) = P.root j) : g = 1 := by
  obtain ⟨l, -, hl⟩ := W_mem_list P (inv_mem hg)
  ext m
  have hu : m - g m ∈ Submodule.span ℤ (range P.root) := sub_mem_span hg m
  have key : ∀ β, corootR P β (g m) = corootR P β m := by
    intro β
    have hrep : HasRep P Finset.univ (corootR P β) :=
      ⟨fun j => if j = β then 1 else 0, by rw [Rep_single P _ (Finset.mem_univ β) 1]; simp⟩
    have h1 := hasRep_prod P l (fun _ _ => Finset.mem_univ _) hrep
    rw [← hl] at h1
    obtain ⟨b, hb⟩ := h1
    obtain ⟨b', hb'⟩ := hrep
    have h2 : actPt g⁻¹ (corootR P β) - corootR P β = 0 := by
      have : actPt g⁻¹ (corootR P β) - corootR P β = Rep P Finset.univ (fun j => b j - b' j) := by
        rw [Rep_sub, ← hb, ← hb']
      rw [this]
      apply rep_eq_zero
      intro k _
      rw [← this]
      show corootR P β ((g⁻¹).symm (P.root k)) - corootR P β (P.root k) = 0
      rw [show (g⁻¹).symm = g from rfl, hfix k, sub_self]
    have h3 := DFunLike.congr_fun h2 m
    simp only [AddMonoidHom.sub_apply, AddMonoidHom.zero_apply] at h3
    have h4 : actPt g⁻¹ (corootR P β) m = corootR P β (g m) := rfl
    rw [h4] at h3
    linarith
  have hc : ∀ i, P.coroot' i (m - g m) = 0 := by
    intro i
    have := key i
    have h5 : (P.coroot' i (g m) : ℝ) = P.coroot' i m := this
    have h6 : P.coroot' i (g m) = P.coroot' i m := by exact_mod_cast h5
    rw [map_sub, h6, sub_self]
  have := zero_of_coroot_zero P hu hc
  exact (sub_eq_zero.1 this).symm

theorem W_finite : Finite (W P (range P.root)) := by
  let S : Set (ι → M) := Set.pi univ fun _ => range P.root
  have hS : S.Finite := Set.Finite.pi fun _ => Set.finite_range _
  haveI : Finite S := hS.to_subtype
  let f : W P (range P.root) → S := fun w =>
    ⟨fun j => (w : M ≃ₗ[ℤ] M) (P.root j), fun j _ => by
      obtain ⟨l, -, hl⟩ := W_mem_list P w.2
      obtain ⟨k, hk⟩ := list_root P l j
      rw [hl]
      exact ⟨k, hk.symm⟩⟩
  refine Finite.of_injective f fun u v huv => ?_
  have h : ∀ j, (u : M ≃ₗ[ℤ] M) (P.root j) = (v : M ≃ₗ[ℤ] M) (P.root j) := fun j =>
    congrFun (congrArg Subtype.val huv) j
  have h1 : (u : M ≃ₗ[ℤ] M)⁻¹ * v = 1 := by
    apply eq_one_of_fix P (mul_mem (inv_mem u.2) v.2)
    intro j
    rw [LinearEquiv.mul_apply, ← h j]
    exact LinearEquiv.symm_apply_apply _ _
  exact Subtype.ext (inv_mul_eq_one.1 h1)

lemma orderOf_pos_of_mem {Ψ : Set M} (hΨ : Ψ ⊆ range P.root) {w : M ≃ₗ[ℤ] M} (hw : w ∈ W P Ψ) :
    0 < orderOf w := by
  haveI := W_finite P
  have hw' : w ∈ W P (range P.root) := W_mono hΨ hw
  rw [← Subgroup.orderOf_mk w hw']
  exact orderOf_pos _

end RD

end AlgMag.Torsion
