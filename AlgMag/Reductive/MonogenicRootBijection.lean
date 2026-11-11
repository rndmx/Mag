/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.ComponentsMeetNormalizerProof

/-!
# Monogenic pure magnets of a split reductive group: the bijection `α ↦ ℕα`

Corollary `cor:red-monogenic`: the map `α ↦ ℕα` is a bijection from `Φ` onto the set of nonzero
monogenerated pure magnets.

* `AlgMag.Rooted.closure_singleton_inj`: for `M` torsion-free, `ℕx = ℕy` with `x, y ≠ 0` gives `x = y`.
* `AlgMag.Reductive.red_mono_injOn_lattice`: `α ↦ ℕα` is injective on `Φ`.
* `AlgMag.Reductive.red_mono_bijOn_lattice`: the bijection.
-/

namespace AlgMag.Rooted

variable {M : Type*} [AddCommGroup M] [IsAddTorsionFree M]

/-- In a torsion-free group, the generator of a nonzero monogenerated monoid is unique. -/
theorem closure_singleton_inj {x y : M} (hx : x ≠ 0)
    (h : AddSubmonoid.closure {x} = AddSubmonoid.closure {y}) : x = y := by
  have hx' : x ∈ AddSubmonoid.closure {y} := h ▸ AddSubmonoid.subset_closure rfl
  have hy' : y ∈ AddSubmonoid.closure {x} := h.symm ▸ AddSubmonoid.subset_closure rfl
  obtain ⟨n, rfl⟩ := AddSubmonoid.mem_closure_singleton.1 hx'
  obtain ⟨m, hm⟩ := AddSubmonoid.mem_closure_singleton.1 hy'
  have e : (m * n) • y = 1 • y := by rw [mul_nsmul', hm, one_smul]
  have hy0 : y ≠ 0 := by rintro rfl; exact hx (smul_zero n)
  have hnm : m * n = 1 := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have h0 : m * n = 0 := by omega
      rw [h0, zero_smul, one_smul] at e
      exact hy0 e.symm
    · have e' : (m * n - 1) • y = 0 := by
        rw [sub_nsmul y hgt.le, e]; exact add_neg_cancel (1 • y)
      exact hy0 (eq_zero_of_nsmul_eq_zero (by omega) e')
  rw [(mul_eq_one.1 hnm).2, one_smul]

end AlgMag.Rooted

suppress_compilation

open Magnetism TauCeti WithConv

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)
variable [IsAlgClosed k] [Algebra.FiniteType k H] [Algebra.Smooth k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)]
variable [Monoid.FG X] [IsMulTorsionFree X]

variable {π}

omit [IsAlgClosed k] [Algebra.FiniteType k H] [Algebra.Smooth k H] [Monoid.FG X] in
/-- `α ↦ ℕα` is injective on the roots (`X` torsion-free, `0 ∉ Φ`). -/
theorem red_mono_injOn_lattice (D : SplitReductiveData.WithRootDatum π) :
    Set.InjOn (fun a : Additive X => AddSubmonoid.closure {a}) (roots π) := by
  intro a ha b _ h
  have h0 : (0 : Additive X) ∉ roots π := by
    rw [← D.range_root]; exact D.P.zero_notMem_range_root
  exact Rooted.closure_singleton_inj (fun e => h0 (e ▸ ha)) h

/-- **Corollary `cor:red-monogenic`**: `α ↦ ℕα` is a bijection from `Φ` onto the set of nonzero
monogenerated pure magnets. -/
theorem red_mono_bijOn_lattice (D : SplitReductiveData.WithRootDatum π) :
    Set.BijOn (fun a : Additive X => AddSubmonoid.closure {a}) (roots π)
      {N | IsPure (affineY (torusGrading π)) N ∧ (∃ x, N = AddSubmonoid.closure {x}) ∧ N ≠ ⊥} := by
  refine ⟨fun a ha => ?_, red_mono_injOn_lattice D, fun N hN => ?_⟩
  · obtain ⟨hp, x, hx, e⟩ := (red_pure_mono_iff_lattice D _).2 ⟨a, ha, rfl⟩
    refine ⟨hp, ⟨a, rfl⟩, fun hb => hx ?_⟩
    change AddSubmonoid.closure {a} = ⊥ at hb
    have : x ∈ AddSubmonoid.closure {a} := e ▸ AddSubmonoid.subset_closure rfl
    rw [hb] at this
    exact (AddSubmonoid.mem_bot).1 this
  · obtain ⟨hp, ⟨x, rfl⟩, hne⟩ := hN
    have hx : x ≠ 0 := by
      rintro rfl
      exact hne (by rw [eq_bot_iff, AddSubmonoid.closure_le]; simp)
    obtain ⟨a, ha, e⟩ := (red_pure_mono_iff_lattice D _).1 ⟨hp, x, hx, rfl⟩
    exact ⟨a, ha, e.symm⟩

end AlgMag.Reductive

#print axioms AlgMag.Rooted.closure_singleton_inj
#print axioms AlgMag.Reductive.red_mono_bijOn_lattice
