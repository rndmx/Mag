/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.LinearAlgebra.FreeModule.PID


/-!
# Fact 3.34 for infinite families: the unit group steps

Combinatorial and algebra steps for unit groups without a minimum.
The scheme arguments are not formalized.
-/

namespace AlgMag.Fact334Inf

variable {M : Type*} [AddCommGroup M]

/-- Unit step of **Fact 3.34**: if a positive multiple of each element of `H₁` lies in `Hᵢ ≤ N`,
then an element of `N ∩ H₁` is a unit of `N`. -/
theorem neg_mem_of_mem_units {N : AddSubmonoid M} {H₁ : AddSubgroup M} {H : AddSubgroup M}
    (hHN : (H : Set M) ⊆ N) (hmul : ∀ x ∈ H₁, ∃ d : ℕ, d ≠ 0 ∧ d • x ∈ H) {n : M} (hn : n ∈ N)
    (hn1 : n ∈ H₁) : -n ∈ N := by
  obtain ⟨d, hd, hk⟩ := hmul n hn1
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd
  have : -n = -((e + 1) • n) + e • n := by rw [succ_nsmul]; abel
  rw [this]
  exact N.add_mem (hHN (H.neg_mem hk)) (N.nsmul_mem hn e)

/-- Sharpness step of **Fact 3.34**: if `N i ∩ H₁ ⊆ H i` for all `i` and the `H i` meet in `0`, then
`⋂ N i` meets `H₁` in `0`. So nonzero elements of the support of `c` are nonunits of `N₁`. -/
theorem iInf_inter_eq_zero {ι : Sort*} (N : ι → AddSubmonoid M) (H : ι → AddSubgroup M)
    (H₁ : AddSubgroup M) (h : ∀ i, ∀ n ∈ N i, n ∈ H₁ → n ∈ H i) (h0 : ⨅ i, H i = ⊥) {n : M}
    (hn : ∀ i, n ∈ N i) (hn1 : n ∈ H₁) : n = 0 := by
  have : n ∈ ⨅ i, H i := AddSubgroup.mem_iInf.mpr fun i => h i n (hn i) hn1
  rwa [h0, AddSubgroup.mem_bot] at this

/-- Rank step of **Fact 3.34**: for `H ≤ H₁` in a finitely generated abelian group, of the same rank, each element of
`H₁` has a positive multiple in `H`. -/
theorem exists_nsmul_mem_of_finrank_eq [Module.Finite ℤ M] {H H₁ : Submodule ℤ M} (hle : H ≤ H₁)
    (hr : Module.finrank ℤ H = Module.finrank ℤ H₁) {x : M} (hx : x ∈ H₁) :
    ∃ d : ℕ, d ≠ 0 ∧ d • x ∈ H := by
  by_contra hno
  simp only [not_exists, not_and] at hno
  -- `x` is free over `H`, so `H + ℤ x` has larger rank
  have hind : ∀ c : ℤ, c • x ∈ H → c = 0 := by
    intro c hc
    by_contra hc0
    refine hno c.natAbs (Int.natAbs_ne_zero.mpr hc0) ?_
    rcases Int.natAbs_eq c with e | e
    · rw [e, natCast_zsmul] at hc; exact hc
    · rw [e, neg_smul, natCast_zsmul] at hc; simpa using H.neg_mem hc
  let Q := H₁ ⧸ H.submoduleOf H₁
  have hq : Module.finrank ℤ Q + Module.finrank ℤ (H.submoduleOf H₁) = Module.finrank ℤ H₁ :=
    Submodule.finrank_quotient_add_finrank _
  have he : Module.finrank ℤ (H.submoduleOf H₁) = Module.finrank ℤ H :=
    (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  have hQ0 : Module.finrank ℤ Q = 0 := by omega
  have htor := Module.finrank_eq_zero_iff_isTorsion.mp hQ0
  let qx : Q := Submodule.Quotient.mk ⟨x, hx⟩
  obtain ⟨⟨c, hc⟩, hcx⟩ := @htor qx
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  apply hc0
  apply hind
  have : (c • (⟨x, hx⟩ : H₁)) ∈ H.submoduleOf H₁ := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    exact hcx
  simpa [Submodule.submoduleOf] using this

/-- Group step of **Fact 3.34**: `R[A/H]` injects in the product of the `R[A/Hᵢ]`, for a directed family of subgroups of
intersection `H`. So the `D(A/Hᵢ)` are schematically dense in `D(A/H)`, and the vertex map, invariant under all of them, is invariant under `D(A/H)`. -/
theorem mapDomain_eq_zero_of_directed {A R ι : Type*} [AddCommGroup A] [Semiring R] [Nonempty ι]
    (H : ι → AddSubgroup A) (hd : Directed (· ≥ ·) H) (x : (A ⧸ (⨅ i, H i)) →₀ R)
    (hx : ∀ i, x.mapDomain (QuotientAddGroup.map _ (H i) (AddMonoidHom.id A)
      (by simpa using iInf_le H i)) = 0) : x = 0 := by
  classical
  let q := fun i => QuotientAddGroup.map (⨅ i, H i) (H i) (AddMonoidHom.id A)
    (by simpa using iInf_le H i)
  have pair : ∀ p : (A ⧸ (⨅ i, H i)) × (A ⧸ (⨅ i, H i)), ∃ i, p.1 ≠ p.2 → q i p.1 ≠ q i p.2 := by
    rintro ⟨a, b⟩
    induction a using QuotientAddGroup.induction_on with | _ a => ?_
    induction b using QuotientAddGroup.induction_on with | _ b => ?_
    by_cases hab : (a : A ⧸ (⨅ i, H i)) = b
    · exact ⟨Classical.arbitrary ι, fun h => absurd hab h⟩
    · have hn : -a + b ∉ ⨅ i, H i := fun h => hab (QuotientAddGroup.eq.mpr h)
      rw [AddSubgroup.mem_iInf] at hn
      obtain ⟨i, hi⟩ := not_forall.mp hn
      refine ⟨i, fun _ h => hi (QuotientAddGroup.eq.mp (by simpa [q] using h))⟩
  choose f hf using pair
  obtain ⟨z, hz⟩ := hd.finset_le ((x.support ×ˢ x.support).image f)
  have hinj : Set.InjOn (q z) (x.support : Set _) := by
    intro a ha b hb hab
    by_contra hne
    have hle := hz (f (a, b)) (Finset.mem_image_of_mem _ (Finset.mem_product.mpr ⟨ha, hb⟩))
    refine hf (a, b) hne ?_
    induction a using QuotientAddGroup.induction_on with | _ a => ?_
    induction b using QuotientAddGroup.induction_on with | _ b => ?_
    exact QuotientAddGroup.eq.mpr (hle (QuotientAddGroup.eq.mp (by simpa [q] using hab)))
  refine Finsupp.mapDomain_injOn _ hinj (by simp) (by simp) ?_
  simpa [q] using hx z

end AlgMag.Fact334Inf

#print axioms AlgMag.Fact334Inf.neg_mem_of_mem_units
#print axioms AlgMag.Fact334Inf.iInf_inter_eq_zero
#print axioms AlgMag.Fact334Inf.exists_nsmul_mem_of_finrank_eq
#print axioms AlgMag.Fact334Inf.mapDomain_eq_zero_of_directed
